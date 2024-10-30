/**CFile****************************************************************

  FileName    [powerexact.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [SAT-based bounded model checking.]

  Synopsis    [Exact synthesis with majority gates.]

  Author      [Michael Feldmeier]
  
  Affiliation [TUM Munich]

  Date        [Ver. 1.0. Started - October 1, 2017.]

  Revision    [$Id: bmcMaj.c,v 1.00 2017/10/01 00:00:00 alanmi Exp $]

***********************************************************************/

#include "bmc.h"
#include "misc/extra/extra.h"
#include "misc/util/utilTruth.h"
#include "sat/cnf/cnf.h"
#include "sat/bsat/satStore.h"
#include "math.h"

ABC_NAMESPACE_IMPL_START

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

#define MAJ_NOBJS  32 // Const0 + Const1 + nVars + nNodes







typedef struct Exa_Man_t_ Exa_Man_t;
struct Exa_Man_t_ 
{
    Bmc_EsPar_t *     pPars;     // parameters
    int               nVars;     // inputs
    int               nNodes;    // internal nodes
    int               nObjs;     // total objects (nVars inputs + nNodes internal nodes)
    int               nWords;    // the truth table size in 64-bit words
    int               iVar;      // the next available SAT variable
    int               i_p;       //start of p variables
    int               i_o;       //start of o variables
    int               o_l;       // amound of o variables
    word *            pTruth;    // truth table
    Vec_Wrd_t *       vInfo;     // nVars + nNodes + 1
    int               VarMarks[MAJ_NOBJS][2][MAJ_NOBJS]; // variable marks
    int               VarVals[MAJ_NOBJS]; // values of the first nVars variables
    Vec_Wec_t *       vOutLits;  // output vars
    sat_solver *      pSat;      // SAT solver
};

static inline word *  Exa_ManTruth( Exa_Man_t * p, int v ) { return Vec_WrdEntryP( p->vInfo, p->nWords * v ); }

typedef struct comb_ comb;
struct comb_{
    int act;
    int r;
    int *satfy;
    int *combi;
    comb* next;
};

typedef struct comb_list_ comb_list;
struct comb_list_
{
    comb* start;
    int len;
    int length;
    
};


void add_combi(int act,int r,int* combi,comb_list* list){    
    int len=list->len;
    comb* node=(comb*) malloc(sizeof(comb));
    node->act=act;
    node->r=r;    
    node->combi=(int*) malloc(len*sizeof(int));
    node->satfy=(int*) malloc(len*sizeof(int));
    for(int i=0;i<len;i++){
        *(node->satfy+i)=-1;
    }   

    
    for(int i=0;i<len;i++){
        *(node->combi+i)=*(combi+i);
    }   
    comb *ptr=list->start;
    if (list->length==0)
    {
        list->start=node;
    }
    else{
        if((ptr->act > act) || ((ptr->act== act)&&(r < ptr->r))){
            list->start=node;
            node->next=ptr;
        }
        else
        {
            for(int l=0;l<list->length-1;l++)
            {
                if(((ptr->act <= act)&&(ptr->next->act>act)) ||
                  
                  
                  ((ptr->act== act)&&(ptr->next->act== act)&&(r >= ptr->r)&&(r <= ptr->next->r)))
                 {
                    node->next=ptr->next;
                    break;
                }
                ptr=ptr->next;
            }
            ptr->next=node;
        }
    }
    list->length++;
}
comb* pop_comb(comb_list* list){
        list->length--;
        comb* node=list->start;
        list->start=list->start->next;
        return node;   
}

void remove_combis(comb_list *list, int r, int *combi)
{
    int l = 0;
    int iptr = 0;
    if (list->length > 0)
    {
        comb *ptr = list->start;
        comb *ptr_old = list->start;
        while (ptr->next != NULL)
        {
            // printf("Loop Start\n");
            if ((ptr->r) == r)
            {
                int match = 0;
                // printf("new ptr\n");
                for (int i = 0; i < list->len; i++)
                {
                    // printf("comparing %d with %d\n",*(ptr->combi+i),*(combi+i));
                    if ((*(combi + i) == -1) || (*(ptr->combi + i) == *(combi + i)))
                        match++;
                }
                if (match == list->len)
                {
                    // printf("element:%d\n",l);
                    // printf("removed\n");
                    if (ptr == list->start)
                    {
                        l++;
                        list->start = ptr->next;
                        ptr_old = list->start;
                        list->length--;
                        // free(ptr->combi);
                        // free(ptr);
                        // ptr=list->start;
                    }
                    else
                    {
                        printf("Removed ACT=%d r=%d p1=%d\n", ptr->act, ptr->r, *combi);
                        l++;
                        ptr_old->next = ptr->next;
                        ptr = ptr_old;
                        list->length--;
                        // free(ptr->combi);
                        // free(ptr);
                        // ptr=ptr_old;
                    }
                }
            }
            ptr_old = ptr;
            ptr = ptr->next;
            // printf("in list %d from %d\n",iptr,list->length);
            iptr++;
            if (iptr == list->length - 1)
                break;
        }

        printf("%d combis removed removing\n", l);
    }
}

void add_satfy_values(comb_list *list, int r, int *combi)
{
    if (list->length > 0)
    {
        comb *ptr = list->start;
        comb *ptr_old = list->start;
        int l = 0;
        int iptr = 0;
        while (ptr->next != NULL)
        {
            if ((ptr->r) == r)
            {
                int match = 0;
                for (int i = 0; i < list->len; i++)
                {
                    // printf("comparing %d with %d\n",*(ptr->combi+i),*(combi+i));
                    if ((*(combi + i) == -1) || (*(ptr->combi + i) == *(combi + i)))
                        match++;
                }
                if (match == list->len)
                {
                    printf("ACT=%d r=%d p1=%d:\n", ptr->act, ptr->r, *(ptr->combi));
                    for (int sa = 0; sa < list->len; sa++)
                    {
                        // printf("satfy_%d=%d\n",sa+1,*(combi+sa));
                        //*(ptr->satfy+sa)=*(combi+sa);
                        int val = *(combi + sa);
                        *(ptr->satfy + sa) = val;
                    }
                    l++;
                }
            }
            ptr_old = ptr;
            ptr = ptr->next;
            // printf("in list %d from %d\n",iptr,list->length);
            iptr++;
            if (iptr == list->length - 1)
                break;
        }
        printf("added satfy for r=%d %d combis \n", r, l);
    }
}

void free_comb_list(comb_list* list){
    while(list->length>0){
       comb* node=pop_comb(list); 
       free(node->satfy);
       free(node->combi);
       free(node);
    }
}



void print_combi_list(comb_list* list){
    printf("List length:%d len:%d\n",list->length,list->len);
    comb* ptr=list->start;
    if(list->length>0){
        while (ptr!=NULL)
        {
            printf("r=%d,act=%d combi:",ptr->r,ptr->act);
            for (int i = 0; i < list->len; i++)
            {
                printf("%d;",*(ptr->combi+i));
            }
            printf("\n");
            ptr=ptr->next;
        }
        
    }

}

/////////////////////////////////////////////////BDD Summed weights
typedef struct node_ node;
struct node_
{
    node* n0;
    node* n1;
    int end0;//-1 for 1-End -2 for 0-End
    int end1;//-1 for 1-End -2 for 0-End
    int i;
    int np;
    int act;  
    int id;  
    int o_var;
    int constr;
};
typedef struct bdd_ bdd;
struct bdd_
{
    node* start;    
    int act;    
};
int* new_node(int end0,int end1,int i,int np, int act,int id)
{
    node* n=(node*) malloc(sizeof(node));
    n->end0=end0;
    n->end1=end1;
    n->i=i;
    n->np=np;
    n->act=act;
    n->id=id;
    n->o_var=0;
    n->constr=0;

    return n;
}

print_bdd(node* n){    
    
    if(n!=NULL){ 
            int in=n->id;       
            printf("#######################\n");
            printf("Node %d act=%d i=%d np=%d",n->id,n->act,n->i,n->np);
            if(n->end1==-1)
                printf(" n1->0-End");
            else if(n->end1==-2)
                printf(" n1->1-End");  
            else 
                printf(" n1:Node%d",n->n1->id);
            if(n->end0==-1)
                printf(" n0->0-End");
            else if(n->end0==-2)
                printf(" n0->1-End");    
            else                 
                printf(" n0->Node%d",n->n0->id);   
            printf("\n");
            printf("#######################\n");
            if(n->end1==0)
                if(n->n1->id>in)
                    print_bdd(n->n1);

            if(n->end0==0)
                if(n->n0->id>in)
                    print_bdd(n->n0);
    }
}
int search_node(node* n,node* target,int i,int np, int act,int from){
    if(n!=NULL){
        int c=n->id;
        if(n->i==i&&n->np==np&&n->act==act){
            //printf("match node %d from node %d i=%d!!\n",n->id,target->id,from);
            if(from)
                target->n1=n;
            else
                target->n0=n;

            return 1;
        }    
        if(n->end0<0 &&n->end1<0){
            return 0;
        }
        else if(n->end0==0 && n->end1==0){         
            //if(n->n1->id>c)   
                if(search_node(n->n1,target,i,np,act,from))
                    return 1;
            //if(n->n0->id>c)
                if(search_node(n->n0,target,i,np,act,from))
                    return 1;
        }
        else if(n->end0==0){
            //if(n->n0->id>c)
                if(search_node(n->n0,target,i,np,act,from))
                    return 1;
        }
        else if(n->end1==0){
            //if(n->n1->id>c)
                if(search_node(n->n1,target,i,np,act,from))
                    return 1;
        }
    }
    return 0;
}

int get_len_bdd(node* n){
    int i=0;
    int c=n->id;    
    if(n->end0<0 &&n->end1<0){
        return 1;
    }
    else if(n->end0==0 && n->end1==0){
        if(n->n1->id>c)
            i=get_len_bdd(n->n1);
        if(n->n0->id>c)
            i=i+get_len_bdd(n->n0);
        return i+1;
    }
    else if(n->end0==0){
        if(n->n0->id>c)
            return 1+get_len_bdd(n->n0);
        
    }
    else if(n->end1==0){
         if(n->n1->id>c)
            return 1+get_len_bdd(n->n1);
    }
    return 1;
}

bdd* calculate_bdd(Exa_Man_t * p,int act,int r){
    int k=p->nVars;
    int r_n=r;
    int n_p=pow(2,k-1);
    int w_p[n_p];
    int w_arr[n_p*r_n];
    int i_arr[n_p*r_n];
    int n_p_arr[n_p*r_n];
   
    for (int i = 0; i < n_p; i++)
    {
        w_p[i]=2*(i+1)*(pow(2,k)-(i+1));
        //printf("%d\n",w_p[i]);
    }
    int index=0;
    //printf("Constructing BDD for r=%d from Summed Weightfunction\n",r_n);
   // printf("%d = ",act);   
    for (int np = n_p-1;np>=0;np--)
    {
        for (int i = 0; i < r_n; i++)
        {
            //printf("%d*p_%d_%d + ",w_p[np],i,np+1);
            int w=w_p[np];
            w_arr[index]=w;
            i_arr[index]=i;
            n_p_arr[index]=np;            
            index++;
        }        
    }    
    
    printf("\n");
    bdd* BDD=(bdd*) malloc(sizeof(bdd));
    BDD->act=act;
    int i_act=act;
    BDD->start=new_node(0,0,i_arr[0],n_p_arr[0],act,0);
    node* i_ptr=BDD->start;
    calculate_node_opt(i_ptr,w_arr,i_arr,n_p,index,0,act,1,n_p_arr,r,BDD);
    //print_bdd(BDD->start);
    
    return BDD;
}
int calculate_node(node* n,int* w_arr,int* i_arr,int n_p,int len,int ptr_start,int act,int id,int* n_p_arr,int r,bdd* BDD){
    
    int i_act=w_arr[ptr_start];
    int iid=id;
    //printf("###Calculate Node %d for act=%d i=%d i_act=%d\n",n->id,act,*(i_arr+ptr_start),i_act);
    ///////////1-node
    int bdd_calc1=bdd_calc_end(w_arr,len,ptr_start+1,act-i_act,r-1,n_p);
    //printf("##Node %d bdd_calc1=%d\n",n->id,bdd_calc1);
    if(bdd_calc1==1){
        //printf("#1-Node:\n");
        
        
        node* n1=new_node(0,0,*(i_arr+ptr_start+1),*(n_p_arr+ptr_start+1),act-i_act,iid);
        iid++;
        iid=calculate_node(n1,w_arr,i_arr,n_p,len,ptr_start+1,act-i_act,iid,n_p_arr,r-1,BDD);
        n->n1=n1;  
                    
        }
    else if(bdd_calc1==2)
        n->end1=-2;    
    else
        n->end1=-1;

    /////////////////0-node    
    int bdd_calc0=bdd_calc_end(w_arr,len,ptr_start+1,act,r,n_p);     
    //printf("##Node %d bdd_calc0=%d\n",n->id,bdd_calc0);
    if(bdd_calc0==1){
        //printf("#0-Node:\n");                    
        
        node* n0=new_node(0,0,*(i_arr+ptr_start+1),*(n_p_arr+ptr_start+1),act,iid);
        iid++;
        iid=calculate_node(n0,w_arr,i_arr,n_p,len,ptr_start+1,act,iid,n_p_arr,r,BDD);
        n->n0=n0;
              
        //iid=calculate_node(n0,w_arr,i_arr,*(n_p_arr+ptr_start+1),len,ptr_start+1,act,iid,n_p_arr,r,hst);  
          
    }
    else if(bdd_calc0==2)    
        n->end0=-2;
    else
        n->end0=-1;
       
    return iid;
}

int calculate_node_opt(node* n,int* w_arr,int* i_arr,int n_p,int len,int ptr_start,int act,int id,int* n_p_arr,int r,bdd* BDD){
    
    int i_act=w_arr[ptr_start];
    int iid=id;
    //printf("###Calculate Node %d for act=%d i=%d i_act=%d\n",n->id,act,*(i_arr+ptr_start),i_act);
    ///////////1-node
    int bdd_calc1=bdd_calc_end(w_arr,len,ptr_start+1,act-i_act,r-1,n_p);
    //printf("##Node %d bdd_calc1=%d\n",n->id,bdd_calc1);
    if(bdd_calc1==1){
        //printf("#1-Node:\n");
        if(!search_node(BDD->start,n,*(i_arr+ptr_start+1),*(n_p_arr+ptr_start+1),act-i_act,1)){
            node* n1=new_node(0,0,*(i_arr+ptr_start+1),*(n_p_arr+ptr_start+1),act-i_act,iid);
            iid++;
            iid=calculate_node_opt(n1,w_arr,i_arr,n_p,len,ptr_start+1,act-i_act,iid,n_p_arr,r-1,BDD);
            n->n1=n1;  
        }            
        }
    else if(bdd_calc1==2)
        n->end1=-2;    
    else
        n->end1=-1;

    /////////////////0-node    
    int bdd_calc0=bdd_calc_end(w_arr,len,ptr_start+1,act,r,n_p);     
    //printf("##Node %d bdd_calc0=%d\n",n->id,bdd_calc0);
    if(bdd_calc0==1){
        //printf("#0-Node:\n");                    
        if(!search_node(BDD->start,n,*(i_arr+ptr_start+1),*(n_p_arr+ptr_start+1),act,0)){
            node* n0=new_node(0,0,*(i_arr+ptr_start+1),*(n_p_arr+ptr_start+1),act,iid);
            iid++;
            iid=calculate_node_opt(n0,w_arr,i_arr,n_p,len,ptr_start+1,act,iid,n_p_arr,r,BDD);
            n->n0=n0;
        }      
        //iid=calculate_node(n0,w_arr,i_arr,*(n_p_arr+ptr_start+1),len,ptr_start+1,act,iid,n_p_arr,r,hst);  
          
    }
    else if(bdd_calc0==2)    
        n->end0=-2;
    else
        n->end0=-1;
       
    return iid;
}


int bdd_calc_end(int* w_arr,int len,int ptr_start,int act,int r,int n_p){
    //printf("len=%d,ptr_start=%d act=%d r=%d\n",len,ptr_start,act,r);      
    
    if(act==0 && r==0)
        return 2;  

    if(act<0)
        return 0;

    int w=0;
    int n_len=0;
    int w_p[n_p];
    int len_w_p[n_p];
    for (int i = ptr_start; i < len; i++)
    {
        if(w_arr[i]!=w){
           len_w_p[n_len]=1;
           w_p[n_len]=w_arr[i];
           w=w_arr[i];
           //printf("Weight:%d\n",w);
           n_len++;           
        }
        else
            len_w_p[n_len-1]+=1;         
    }
    /*for (int i = 0; i < n_len; i++)
    {
        printf("%d,",len_w_p[i]);
    }*/
    
    //printf("n_len:%d\n",n_len);
    for (int i = 0; i < pow(r+1,n_len); i++)
    {        
        int sum=0;
        int sum_b=0;
        int combi[n_len];        
        convert_base_int(r+1,i,n_len,combi);
        for (int j = 0; j < n_len; j++)
        {
            /*if(combi[j]>len_w_p[j]){
                j=n_len;
                sum=0;
            }*//////////////////
            sum_b=sum_b+combi[j];
            int mul=combi[j];
            sum=sum+(w_p[n_len-j-1]*mul);            
        }
        if(sum==act && sum_b==r){
            /*printf("Match Result:");
            for (int a = 0; a < n_len; a++)
                {
                    printf("%d,",combi[a]);
                }
                printf("\n");*/
            return 1;
        }
        
    }
    return 0;
}


delete_bdd(node* n){
    if(n!=NULL){        
        int in=n->id;
        if(n->end0< 0 && n->end1 < 0){
            free(n);
        }
        else if(n->end0<0){
            if(n->n1->id>in)
                delete_bdd(n->n1);
            free(n);
        }
        else if(n->end1<0){
            if(n->n0->id>in)
                delete_bdd(n->n0);
            free(n);
        }
        else{
            if(n->n1->id>in)
                delete_bdd(n->n1);
            if(n->n0->id>in)
                delete_bdd(n->n0);
            free(n);
        }
    }


}

void optimize_bdd(bdd* BDD){
    if(BDD->start!=NULL){
        if(BDD->start->end0==0&&BDD->start->end1==0){
            optimize_recursive(BDD->start->n1,BDD->start,1);
            optimize_recursive(BDD->start->n0,BDD->start,0);
        }
            
        if(BDD->start->end0==0)
            optimize_recursive(BDD->start->n0,BDD->start,0);
        if(BDD->start->end1==0)
            optimize_recursive(BDD->start->n1,BDD->start,1);
    }
}


        
void optimize_recursive(node* n,node* p,int i){
    //printf("optimizing node %d\n",n->id);
    if(n->end0==-2 &&n->end1==-2){
        //printf("optimizing node %d End\n",n->id);
        
    }
    else if(n->end0==-2 &&n->end1==-1){
      if(i==1){
            p->n1=NULL;
            p->end1=-1;
        }            
        else{
            p->n0=NULL;
            p->end0=-1;
        }
    }
    else if(n->end1==-1 && n->end0==-1){
        //printf("optimizing NOde:%d 2 times 0\n",n->id);
        if(i==1){
            p->n1=NULL;
            p->end1=-1;
        }            
        else{
            p->n0=NULL;
            p->end0=-1;
        }
    }
    /*else if(n->end0==-1 && n->end1==0){
        //printf("optimizing node %d Removed\n",n->id);
        if(i==1)
            p->n1=n->n1;
        else
            p->n0=n->n1;
        optimize_recursive(n->n1,p,i);
    }*/
    else if(n->end1==0 && n->end0==-1){
        //printf("optimizing node %d Removed\n",n->id);        
        optimize_recursive(n->n1,n,1);
    }
    else if(n->end1==-1 && n->end0==0){
        //printf("optimizing node %d Removed\n",n->id);
        if(i==1)
            p->n1=n->n0;
        else
            p->n0=n->n0;
        optimize_recursive(n->n0,p,i);
    }
    else if(n->end0==0 && n->end1==0){
        //printf("optimizing node %d 2 ways\n",n->id);
        optimize_recursive(n->n1,n,1); 
       // printf("optimizing node %d %dsecound ways\n",n->id,n->n0->id);
        optimize_recursive(n->n0,n,0);
    }
    else if(n->end0==0 && n->end1==-2){
       // printf("optimizing node %d n0 ways\n",n->id);
        optimize_recursive(n->n0,n,0);
    }
    else if(n->end1==0 && n->end0==-2){
        //printf("optimizing node %d n1 ways\n",n->id);
        optimize_recursive(n->n1,n,1);        
    }
}

void optimize_bdd2(bdd* BDD,int k){
    int n_p=pow(2,k-1);
    int hst[n_p];
    for (int i = 0; i < n_p; i++)
    {
        hst[i]=0;
    }
    
    if(BDD->start!=NULL){
        if(BDD->start->end0==0&&BDD->start->end1==0){
            hst[BDD->start->i]=1;
            optimize_recursive2(BDD->start->n1,BDD->start,1,hst);
            hst[BDD->start->i]=0;
            optimize_recursive2(BDD->start->n0,BDD->start,0,hst);
        }            
        if(BDD->start->end0==0)
            optimize_recursive2(BDD->start->n0,BDD->start,0,hst);
        if(BDD->start->end1==0){
            hst[BDD->start->i]=1;
            optimize_recursive2(BDD->start->n1,BDD->start,1,hst);
        }
            
    }
}

void optimize_recursive2(node* n,node* p,int i,int *hst){
    if(hst[n->i]==1){
        n->n1=NULL;
        n->end1=-1;
        if(n->end0==0){
            hst[n->i]=0;
            optimize_recursive2(n->n0,n,0,hst);            
        }
    }
    else{
    if(n->end0<0 && n->end1<0){
        
        
    }   
    else if(n->end0==0 && n->end1==0){        
        hst[n->i]=1;
        optimize_recursive2(n->n1,n,1,hst);
        hst[n->i]=0;
        optimize_recursive2(n->n0,n,0,hst);
    }
    else if(n->end0==0){
        hst[n->i]=0;
        optimize_recursive2(n->n0,n,0,hst); 
        
    }
    else if(n->end1==0){
        hst[n->i]=1;
        optimize_recursive2(n->n1,n,1,hst);        
    } 
    }    
    hst[n->i]=0;
}



/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static Vec_Wrd_t * Exa_ManTruthTables( Exa_Man_t * p )
{
    Vec_Wrd_t * vInfo = p->vInfo = Vec_WrdStart( p->nWords * (p->nObjs+1) ); int i;
    for ( i = 0; i < p->nVars; i++ )
        Abc_TtIthVar( Exa_ManTruth(p, i), i, p->nVars );
    //Dau_DsdPrintFromTruth( Exa_ManTruth(p, p->nObjs), p->nVars );
    return vInfo;
}
static int Exa_ManMarkup( Exa_Man_t * p )
{
    int i, k, j;
    assert( p->nObjs <= MAJ_NOBJS );
    // assign functionality
    p->iVar = 1 + p->nNodes * 3;
    // assign connectivity variables
    for ( i = p->nVars; i < p->nObjs; i++ )
    {
        for ( k = 0; k < 2; k++ )
        {
            if ( p->pPars->fFewerVars && i == p->nObjs - 1 && k == 0 )
            {
                j = p->nObjs - 2;
                Vec_WecPush( p->vOutLits, j, Abc_Var2Lit(p->iVar, 0) );
                p->VarMarks[i][k][j] = p->iVar++;
                continue;
            }
            for ( j = p->pPars->fFewerVars ? 1 - k : 0; j < i - k; j++ )
            {
                Vec_WecPush( p->vOutLits, j, Abc_Var2Lit(p->iVar, 0) );
                p->VarMarks[i][k][j] = p->iVar++;
            }
        }
    }
    //printf( "The number of parameter variables = %d.\n", p->iVar );
    return p->iVar;
    // printout
    for ( i = p->nVars; i < p->nObjs; i++ )
    {
        printf( "Node %d\n", i );
        for ( j = 0; j < p->nObjs; j++ )
        {
            for ( k = 0; k < 2; k++ )
                printf( "%3d ", p->VarMarks[i][k][j] );
            printf( "\n" );
        }
    }
    return p->iVar;
}
static Exa_Man_t * Exa_ManAlloc( Bmc_EsPar_t * pPars, word * pTruth )
{
    Exa_Man_t * p = ABC_CALLOC( Exa_Man_t, 1 );
    p->pPars      = pPars;
    p->nVars      = pPars->nVars;
    p->nNodes     = pPars->nNodes;
    p->nObjs      = pPars->nVars + pPars->nNodes;
    p->nWords     = Abc_TtWordNum(pPars->nVars);
    p->pTruth     = pTruth;
    p->i_p        =0;
    p->o_l        =0;
    p->i_o        =0;
    p->vOutLits   = Vec_WecStart( p->nObjs );
    p->iVar       = Exa_ManMarkup( p );
    p->vInfo      = Exa_ManTruthTables( p );
    p->pSat       = sat_solver_new();
    sat_solver_setnvars( p->pSat, p->iVar );
    return p;
}
static void Exa_ManFree( Exa_Man_t * p )
{
    sat_solver_delete( p->pSat );
    Vec_WrdFree( p->vInfo );
    Vec_WecFree( p->vOutLits );
    ABC_FREE( p );
}


/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline int Exa_ManFindFanin( Exa_Man_t * p, int i, int k )
{
    int j, Count = 0, iVar = -1;
    for ( j = 0; j < p->nObjs; j++ )
        if ( p->VarMarks[i][k][j] && sat_solver_var_value(p->pSat, p->VarMarks[i][k][j]) )
        {
            iVar = j;
            Count++;
        }
    assert( Count == 1 );
    return iVar;
}
static inline int Exa_ManEval( Exa_Man_t * p )
{
    static int Flag = 0;
    int i, k, iMint; word * pFanins[2];
    for ( i = p->nVars; i < p->nObjs; i++ )
    {
        int iVarStart = 1 + 3*(i - p->nVars);
        for ( k = 0; k < 2; k++ )
            pFanins[k] = Exa_ManTruth( p, Exa_ManFindFanin(p, i, k) );
        Abc_TtConst0( Exa_ManTruth(p, i), p->nWords );
        for ( k = 1; k < 4; k++ )
        {
            if ( !sat_solver_var_value(p->pSat, iVarStart+k-1) )
                continue;
            Abc_TtAndCompl( Exa_ManTruth(p, p->nObjs), pFanins[0], !(k&1), pFanins[1], !(k>>1), p->nWords );
            Abc_TtOr( Exa_ManTruth(p, i), Exa_ManTruth(p, i), Exa_ManTruth(p, p->nObjs), p->nWords );
        }
    }
    if ( Flag && p->nVars >= 6 )
        iMint = Abc_TtFindLastDiffBit( Exa_ManTruth(p, p->nObjs-1), p->pTruth, p->nVars );
    else
        iMint = Abc_TtFindFirstDiffBit( Exa_ManTruth(p, p->nObjs-1), p->pTruth, p->nVars );
    //Flag ^= 1;
    assert( iMint < (1 << p->nVars) );
    return iMint;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Exa_ManPrintSolution( Exa_Man_t * p, int fCompl )
{
    int i, k, iVar;
    printf( "Realization of given %d-input function using %d two-input gates complementary=%d:\n", p->nVars, p->nNodes,fCompl );
//    for ( i = p->nVars + 2; i < p->nObjs; i++ )
    for ( i = p->nObjs - 1; i >= p->nVars; i-- )
    {
        int iVarStart = 1 + 3*(i - p->nVars);
        int Val1 = sat_solver_var_value(p->pSat, iVarStart);
        int Val2 = sat_solver_var_value(p->pSat, iVarStart+1);
        int Val3 = sat_solver_var_value(p->pSat, iVarStart+2);
        if ( i == p->nObjs - 1 && fCompl )
            printf( "%02d = 4\'b%d%d%d1(", i, !Val3, !Val2, !Val1 );
        else
            printf( "%02d = 4\'b%d%d%d0(", i, Val3, Val2, Val1 );
        for ( k = 1; k >= 0; k-- )
        {
            iVar = Exa_ManFindFanin( p, i, k );
            if ( iVar >= 0 && iVar < p->nVars )
                printf( " %c", 'a'+iVar );
            else
                printf( " %02d", iVar );
        }
        printf( " )\n" );
    }
    printf("Printing P Variables...\n");;
    int n_p=pow(2,p->nVars-1);
    for (int i = 0; i < p->nNodes-1; i++)
    {
        for (int j = 0; j < n_p; j++)
        {
            printf("p_%d_%d has value %d\n",p->nVars+i,j+1,sat_solver_var_value(p->pSat,p->i_p+n_p*i+j));
        }
    }
    printf("Printing overall Truth Table...\n");
    int len=(p->nObjs)*(pow(2,p->nVars));
    int x_it[len];
    int xi_base= p->nNodes*(2*p->nVars+p->nNodes-1)-p->nNodes+3*p->nNodes;


    for (int i = 0; i < p->nVars; i++)
    {
        for (int t = 0; t < pow(2,p->nVars); t++)
        {
            int index=i*(pow(2,p->nVars))+t;
            x_it[index] = value_of_nthbit(t,i);
        }
    }
    
    for(int i=p->nVars;i<p->nVars+p->nNodes-1;i++)
    {
        int index=i*(pow(2,p->nVars));
        x_it[index]=0;
        for (int t = 1; t < pow(2,p->nVars); t++)
        {
            int index=i*(pow(2,p->nVars))+t;
            x_it[index] = sat_solver_var_value(p->pSat ,xi_base + 3*(i-p->nVars+1)+(t-1)*(3*p->nNodes));
           
        }
        
    }
    for (int i = 0; i < p->nObjs-1; i++)
    {
        printf("i=%d:",i);
        for (int t = 0; t < pow(2,p->nVars); t++)
        {
            int index=i*(pow(2,p->nVars))+t;
            printf("%d",x_it[index]);
        }
        printf("\n");        
    }     
    int iVarStart = 1 + 3*(p->nObjs - 1 - p->nVars);
    int f_out[4];
    f_out[0]=fCompl;
    f_out[1] =fCompl ? !sat_solver_var_value(p->pSat, iVarStart) :sat_solver_var_value(p->pSat, iVarStart);
    f_out[2] =fCompl ? !sat_solver_var_value(p->pSat, iVarStart+1):sat_solver_var_value(p->pSat, iVarStart+1);
    f_out[3] =fCompl ? !sat_solver_var_value(p->pSat, iVarStart+2):sat_solver_var_value(p->pSat, iVarStart+2);
    int i0 = Exa_ManFindFanin( p, p->nObjs-1, 0);
    int i1 = Exa_ManFindFanin( p, p->nObjs-1, 1);
    printf("i=%d:",p->nObjs-1);
    for (int t = 0; t <  pow(2,p->nVars); t++)
    {
        int index_0=i0*(pow(2,p->nVars))+t;
        int index_1=i1*(pow(2,p->nVars))+t;
        int index=(x_it[index_1]<<1)+(x_it[index_0]);
        printf("%d",f_out[index]);
    }    
    printf("\n");
    printf("\n");
    int sum_act=0;
    for (int i = p->nVars; i < p->nObjs-1; i++)
    {
        int sum_0=0;
        int sum_1=0;
        int min_sum=0;
        for (int t = 0; t <  pow(2,p->nVars); t++)
        {
            int index=i*(pow(2,p->nVars))+t;
            if(x_it[index]==1)
                sum_1++;
            else
                sum_0++;                
        }
        min_sum=sum_1<=sum_0? sum_1: sum_0;
        sum_act+= 2*min_sum*(pow(2,p->nVars)-min_sum);
    }
    printf("Switching Activity=%d\n",sum_act);
    printf("Number of Gates: r=%d\n",p->nNodes);
   
}

static void Exa_ManPrintSolution_bdd( Exa_Man_t * p, int fCompl )
{
    int i, k, iVar;
    printf( "Realization of given %d-input function using %d two-input gates complementary=%d:\n", p->nVars, p->nNodes,fCompl );
//    for ( i = p->nVars + 2; i < p->nObjs; i++ )
    for ( i = p->nObjs - 1; i >= p->nVars; i-- )
    {
        int iVarStart = 1 + 3*(i - p->nVars);
        int Val1 = sat_solver_var_value(p->pSat, iVarStart);
        int Val2 = sat_solver_var_value(p->pSat, iVarStart+1);
        int Val3 = sat_solver_var_value(p->pSat, iVarStart+2);
        if ( i == p->nObjs - 1 && fCompl )
            printf( "%02d = 4\'b%d%d%d1(", i, !Val3, !Val2, !Val1 );
        else
            printf( "%02d = 4\'b%d%d%d0(", i, Val3, Val2, Val1 );
        for ( k = 1; k >= 0; k-- )
        {
            iVar = Exa_ManFindFanin( p, i, k );
            if ( iVar >= 0 && iVar < p->nVars )
                printf( " %c", 'a'+iVar );
            else
                printf( " %02d", iVar );
        }
        printf( " )\n" );
    }
    /*printf("Printing M Variables...\n");
    int m_size=0;
    for (int i = 1; i <=pow(2,p->nVars)-1; i++)
    {
        m_size+=i;
    }
    int n_p=pow(2,p->nVars-1)+1;
    for (int i = 0; i < p->nNodes-1; i++)
    {
        for (int j = 0; j < m_size; j++)
        {
            printf("m_%d_%d has value %d\n",p->nVars+i,j+1,sat_solver_var_value(p->pSat,p->i_p+(n_p+m_size)*i+j));
        }
        for (int j = 0; j < n_p; j++)
        {
            printf("p_%d_%d has value %d\n",p->nVars+i,j,sat_solver_var_value(p->pSat,p->i_p+(n_p+m_size)*i+j+m_size));
        }
    }*/
    printf("Printing overall Truth Table...\n");
    int len=(p->nObjs)*(pow(2,p->nVars));
    int x_it[len];
    int xi_base= p->nNodes*(2*p->nVars+p->nNodes-1)-p->nNodes+3*p->nNodes;


    for (int i = 0; i < p->nVars; i++)
    {
        for (int t = 0; t < pow(2,p->nVars); t++)
        {
            int index=i*(pow(2,p->nVars))+t;
            x_it[index] = value_of_nthbit(t,i);
        }
    }
    
    for(int i=p->nVars;i<p->nVars+p->nNodes-1;i++)
    {
        int index=i*(pow(2,p->nVars));
        x_it[index]=0;
        for (int t = 1; t < pow(2,p->nVars); t++)
        {
            int index=i*(pow(2,p->nVars))+t;
            x_it[index] = sat_solver_var_value(p->pSat ,xi_base + 3*(i-p->nVars+1)+(t-1)*(3*p->nNodes));
           
        }
        
    }
    for (int i = 0; i < p->nObjs-1; i++)
    {
        printf("i=%d:",i);
        for (int t = 0; t < pow(2,p->nVars); t++)
        {
            int index=i*(pow(2,p->nVars))+t;
            printf("%d",x_it[index]);
        }
        printf("\n");        
    }     
    int iVarStart = 1 + 3*(p->nObjs - 1 - p->nVars);
    int f_out[4];
    f_out[0]=fCompl;
    f_out[1] =fCompl ? !sat_solver_var_value(p->pSat, iVarStart) :sat_solver_var_value(p->pSat, iVarStart);
    f_out[2] =fCompl ? !sat_solver_var_value(p->pSat, iVarStart+1):sat_solver_var_value(p->pSat, iVarStart+1);
    f_out[3] =fCompl ? !sat_solver_var_value(p->pSat, iVarStart+2):sat_solver_var_value(p->pSat, iVarStart+2);
    int i0 = Exa_ManFindFanin( p, p->nObjs-1, 0);
    int i1 = Exa_ManFindFanin( p, p->nObjs-1, 1);
    printf("i=%d:",p->nObjs-1);
    for (int t = 0; t <  pow(2,p->nVars); t++)
    {
        int index_0=i0*(pow(2,p->nVars))+t;
        int index_1=i1*(pow(2,p->nVars))+t;
        int index=(x_it[index_1]<<1)+(x_it[index_0]);
        printf("%d",f_out[index]);
    }    
    printf("\n");
    printf("\n");
    int sum_act=0;
    for (int i = p->nVars; i < p->nObjs-1; i++)
    {
        int sum_0=0;
        int sum_1=0;
        int min_sum=0;
        for (int t = 0; t <  pow(2,p->nVars); t++)
        {
            int index=i*(pow(2,p->nVars))+t;
            if(x_it[index]==1)
                sum_1++;
            else
                sum_0++;                
        }
        min_sum=sum_1<=sum_0? sum_1: sum_0;
        sum_act+= 2*min_sum*(pow(2,p->nVars)-min_sum);
    }
    printf("Switching Activity=%d\n",sum_act);
    printf("Number of Gates: r=%d\n",p->nNodes);
   
}


/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Exa_ManAddCnfStart( Exa_Man_t * p, int fOnlyAnd )
{
    int pLits[MAJ_NOBJS], pLits2[2], i, j, k, n, m;
    // input constraints
    for ( i = p->nVars; i < p->nObjs; i++ )
    {
        int iVarStart = 1 + 3*(i - p->nVars);
        for ( k = 0; k < 2; k++ )
        {
            int nLits = 0;
            for ( j = 0; j < p->nObjs; j++ )
                if ( p->VarMarks[i][k][j] )
                    pLits[nLits++] = Abc_Var2Lit( p->VarMarks[i][k][j], 0 );
            assert( nLits > 0 );
            // input uniqueness
            if ( !sat_solver_addclause( p->pSat, pLits, pLits+nLits ) )
                return 0;
            for ( n = 0;   n < nLits; n++ )
            for ( m = n+1; m < nLits; m++ )
            {
                pLits2[0] = Abc_LitNot(pLits[n]);
                pLits2[1] = Abc_LitNot(pLits[m]);
                if ( !sat_solver_addclause( p->pSat, pLits2, pLits2+2 ) )
                    return 0;
            }
            if ( k == 1 )
                break;
            // symmetry breaking
            
            for ( j = 0; j < p->nObjs; j++ ) if ( p->VarMarks[i][k][j] )
            for ( n = j; n < p->nObjs; n++ ) if ( p->VarMarks[i][k+1][n] )
            {
                pLits2[0] = Abc_Var2Lit( p->VarMarks[i][k][j], 1 );
                pLits2[1] = Abc_Var2Lit( p->VarMarks[i][k+1][n], 1 );
                if ( !sat_solver_addclause( p->pSat, pLits2, pLits2+2 ) )
                    return 0;
            }
        }
#ifdef USE_NODE_ORDER
        // node ordering
        for ( j = p->nVars; j < i; j++ )
        for ( n = 0;   n < p->nObjs; n++ ) if ( p->VarMarks[i][0][n] )
        for ( m = n+1; m < p->nObjs; m++ ) if ( p->VarMarks[j][0][m] )
        {
            pLits2[0] = Abc_Var2Lit( p->VarMarks[i][0][n], 1 );
            pLits2[1] = Abc_Var2Lit( p->VarMarks[j][0][m], 1 );
            if ( !sat_solver_addclause( p->pSat, pLits2, pLits2+2 ) )
                return 0;
        }
#endif
        // two input functions
        for ( k = 0; k < 3; k++ )
        {
            pLits[0] = Abc_Var2Lit( iVarStart,   k==1 );
            pLits[1] = Abc_Var2Lit( iVarStart+1, k==2 );
            pLits[2] = Abc_Var2Lit( iVarStart+2, k!=0 );
            if ( !sat_solver_addclause( p->pSat, pLits, pLits+3 ) )
                return 0;
        }
        if ( fOnlyAnd )
        {
            pLits[0] = Abc_Var2Lit( iVarStart,   1 );
            pLits[1] = Abc_Var2Lit( iVarStart+1, 1 );
            pLits[2] = Abc_Var2Lit( iVarStart+2, 0 );
            if ( !sat_solver_addclause( p->pSat, pLits, pLits+3 ) )
                return 0;
        }
    }
    // outputs should be used
    for ( i = 0; i < p->nObjs - 1; i++ )
    {
        Vec_Int_t * vArray = Vec_WecEntry(p->vOutLits, i);
               
        assert( Vec_IntSize(vArray) > 0 );
        if ( !sat_solver_addclause( p->pSat, Vec_IntArray(vArray), Vec_IntLimit(vArray) ) )
            return 0;
    }
    return 1;
}
static int Exa_ManAddCnf( Exa_Man_t * p, int iMint )
{
    // save minterm values
    int i, k, n, j, Value = Abc_TtGetBit(p->pTruth, iMint);
    for ( i = 0; i < p->nVars; i++ )
        p->VarVals[i] = (iMint >> i) & 1;
    sat_solver_setnvars( p->pSat, p->iVar + 3*p->nNodes );
    //printf( "Adding clauses for minterm %d with value %d.\n", iMint, Value );
    for ( i = p->nVars; i < p->nObjs; i++ )
    {
        // fanin connectivity
        int iVarStart = 1 + 3*(i - p->nVars);
        int iBaseSatVarI = p->iVar + 3*(i - p->nVars);
        for ( k = 0; k < 2; k++ )
        {
            for ( j = 0; j < p->nObjs; j++ ) if ( p->VarMarks[i][k][j] )
            {
                int iBaseSatVarJ = p->iVar + 3*(j - p->nVars);
                for ( n = 0; n < 2; n++ )
                {
                    int pLits[3], nLits = 0;
                    pLits[nLits++] = Abc_Var2Lit( p->VarMarks[i][k][j], 1 );
                    pLits[nLits++] = Abc_Var2Lit( iBaseSatVarI + k, n );
                    if ( j >= p->nVars )
                        pLits[nLits++] = Abc_Var2Lit( iBaseSatVarJ + 2, !n );
                    else if ( p->VarVals[j] == n )
                        continue;
                    if ( !sat_solver_addclause( p->pSat, pLits, pLits+nLits ) )
                        return 0;
                }
            }
        }
        // node functionality
        for ( n = 0; n < 2; n++ )
        {
            if ( i == p->nObjs - 1 && n == Value )
                continue;
            for ( k = 0; k < 4; k++ )
            {
                int pLits[4], nLits = 0;
                if ( k == 0 && n == 1 )
                    continue;
                pLits[nLits++] = Abc_Var2Lit( iBaseSatVarI + 0, (k&1)  );
                pLits[nLits++] = Abc_Var2Lit( iBaseSatVarI + 1, (k>>1) );
                if ( i != p->nObjs - 1 ) pLits[nLits++] = Abc_Var2Lit( iBaseSatVarI + 2, !n );
                if ( k > 0 )             pLits[nLits++] = Abc_Var2Lit( iVarStart +  k-1,  n );
                assert( nLits <= 4 );
                if (!sat_solver_addclause(p->pSat, pLits, pLits+nLits))
                    return 0;
            }
        }
           
    }
    
    p->iVar += 3*p->nNodes;
    return 1;
}

int Exa_ManEvalPVariables_bdd(Exa_Man_t * p, int* combi,int * arr_xp){
    int n_p=pow(2,p->nVars-1)+1;
    int combi_sol[n_p];
    for (int i = 0; i < n_p; i++)
    {
        combi_sol[i]=0;
    }
    

    int m_size=0;
    for (int i = 1; i <=pow(2,p->nVars)-1; i++)
    {
        m_size+=i;
    }    
    /*for (int i = 0; i < p->nNodes-1; i++)
    {
        for (int j = 0; j < m_size; j++)
        {
            printf("m_%d_%d has value %d\n",p->nVars+i,j+1,sat_solver_var_value(p->pSat,p->i_p+(n_p+m_size)*i+j));
        }
        for (int j = 0; j < n_p; j++)
        {
            printf("p_%d_%d has value %d\n",p->nVars+i,j,sat_solver_var_value(p->pSat,p->i_p+(n_p+m_size)*i+j+m_size));
        }
    }*/
    for (int i = 0; i < p->nNodes-1; i++)
    {
        for (int j = 0; j < n_p; j++)
        {
            combi_sol[j]+=sat_solver_var_value(p->pSat,p->i_p+(n_p+m_size)*i+j+m_size);
            //printf("p_%d_%d has value %d\n",p->nVars+i,j+1,sat_solver_var_value(p->pSat,p->i_p+n_p*i+j));
        }
    }
    for (int i = 0; i < n_p-1; i++)
    {
        //printf("comparing xp=%d %d with %d\n",i+1,combi_sol[i],*(combi+i));
        if(*(combi+i)!=combi_sol[i+1])
            return i;     
        //else
        //    *(arr_xp+i)=*(combi+i);   
    }
    return -1;   
}

int Exa_ManEvalPVariables(Exa_Man_t * p, int* combi){
    int n_p=pow(2,p->nVars-1);
    int combi_sol[n_p];
    for (int i = 0; i < n_p; i++)
    {
        combi_sol[i]=0;
    }
    
    for (int i = 0; i < p->nNodes-1; i++)
    {
        for (int j = 0; j < n_p; j++)
        {
            combi_sol[j]+=sat_solver_var_value(p->pSat,p->i_p+n_p*i+j);
            //printf("p_%d_%d has value %d\n",p->nVars+i,j+1,sat_solver_var_value(p->pSat,p->i_p+n_p*i+j));
        }
    }

    for (int i = 0; i < n_p; i++)
    {
        //printf("comparing xp=%d %d with %d\n",i+1,combi_sol[i],*(combi+i));
        if(*(combi+i)!=combi_sol[i])
            return i;        
    }
    return -1;   
}

int faku(int n){
    if(n>0)
        return n*faku(n-1);
    else 
        return 1;    
}

void Exa_ManAddPClauses_bdd(Exa_Man_t * p){
    //printf("adding P Clauses\n");
    int xi_base= p->nNodes*(2*p->nVars+p->nNodes-1)-p->nNodes+3*p->nNodes;   
    int n_p=pow(2,p->nVars-1)+1;
    int x_it=0;
    int m_size=pow(2,p->nVars)-1;
    int x_size=pow(2,p->nVars)-1;
    int fak=0;
   
    for (int f = 1; f <= m_size; f++)
    {       
        fak=fak+f;
    }
    m_size=fak;
    p->i_p=p->iVar;
    //printf("Creating %d new Variables for bdd EQ Encoding\n",m_size);    
    for(int i=p->nVars+1;i<p->nVars+p->nNodes;i++){
        int m_start=p->iVar;
        p->iVar+=m_size;
        sat_solver_setnvars( p->pSat, p->iVar);
        int p_start=p->iVar;
        p->iVar+=n_p;
        sat_solver_setnvars( p->pSat, p->iVar);
        int lit=Abc_Var2Lit(p_start,1);
        sat_solver_addclause(p->pSat,&lit,&lit+1);//restricting p0   
        lit=Abc_Var2Lit(m_start,0);
        sat_solver_addclause(p->pSat,&lit,&lit+1);//restricting m1 needs to be fullfilled       
        int p_vars[2*n_p-2];
        for (int p = 0; p < n_p; p++)
        {
            p_vars[p]=p_start+p;
        }
        for (int p = n_p; p < 2*n_p-2; p++)
        {
            p_vars[p]=p_start+2*n_p-2-p;
        }         
        //printf("Adding MUX Clasues for i=%d\n",i);
        int x_end =pow(2,p->nVars)-1;
        int x =0;
        int y =0;
        for (int m = 0; m < m_size; m++)
        {   
            //printf("Adding MUX for m=%d\n",m);
            int t=y+x+1;
            x_it = xi_base + 3*(i-p->nVars)+(t-1)*(3*p->nNodes);
            int m1;
            int m0;
            if(x==x_end-1){
                m1=p_vars[y+1];
                m0=p_vars[y];    
                //printf("Adding Mux m_%d=(x_%d?p_%d:p_%d)\n",m+1,t,y+1,y);           
            }
            else{
                m1=m_start+m+x_end;
                m0=m_start+m+1;
                //printf("Adding Mux m_%d=(x_%d?m_%d:m_%d)\n",m+1,t,m+x_end+1,m+1+1);
            }            
            add_mux_encoding(p,m_start+m,x_it,m1,m0);
            x++;
            if(x==x_end){
                x=0;
                x_end--;
                y++;
            }            
        }        
    
    
    
    ///////////////////////////////Sum(p)=1
        int pLits[n_p-1];
        for (int j = 0; j < pow(2,n_p-1); j++)
        {
           
           int lit_sum=0;
           int res[n_p-1];
            convert_base_int(2,j,n_p-1,res);
            int sum=0;
            for (int l = 0; l < n_p-1; l++)
            {
                sum+=*(res+l);
            }
            if(sum==2){
                lit_sum=0;
                for (int l = 0; l < n_p-1; l++){
                        if(*(res+l)==1){                            
                            pLits[lit_sum++]=Abc_Var2Lit(p->i_p+(i-p->nVars-1)*(n_p+m_size)+m_size+l+1,1);
                        }
                }           
            sat_solver_addclause(p->pSat,pLits,pLits+lit_sum);                
            }
        }
        for (int j = 0; j < pow(2,n_p-1); j++)
        {
          
           int lit_sum=0;
           int res[n_p-1];
            convert_base_int(2,j,n_p-1,res);
            int sum=0;
            for (int l = 0; l < n_p-1; l++)
            {
                sum+=*(res+l);
            }
            if(sum==n_p-1){
                lit_sum=0;
                for (int l = 0; l < n_p-1; l++){
                        if(*(res+l)==1){                            
                            pLits[lit_sum++]=Abc_Var2Lit(p->i_p+(i-p->nVars-1)*(n_p+m_size)+m_size+l+1,0);
                        }
                }           
            sat_solver_addclause(p->pSat,pLits,pLits+lit_sum);                
            }
        }
    }


    
        
}

void add_mux_encoding(Exa_Man_t * p,int o,int c, int i1,int i0){    
    int pLits[3];    
    pLits[0]=Abc_Var2Lit(c,1);
    pLits[1]=Abc_Var2Lit(o,1);
    pLits[2]=Abc_Var2Lit(i1,0);
    sat_solver_addclause( p->pSat, pLits, pLits+3);
    pLits[0]=Abc_Var2Lit(c,1);
    pLits[1]=Abc_Var2Lit(i1,1);
    pLits[2]=Abc_Var2Lit(o,0);
    sat_solver_addclause( p->pSat, pLits, pLits+3);
    pLits[0]=Abc_Var2Lit(c,0);
    pLits[1]=Abc_Var2Lit(o,1);
    pLits[2]=Abc_Var2Lit(i0,0);
    sat_solver_addclause( p->pSat, pLits, pLits+3);
    pLits[0]=Abc_Var2Lit(c,0);
    pLits[1]=Abc_Var2Lit(i0,1);
    pLits[2]=Abc_Var2Lit(o,0);
    sat_solver_addclause( p->pSat, pLits, pLits+3);
}


void Exa_ManAddPClauses(Exa_Man_t * p){
    //printf("adding P Clauses\n");
    int xi_base= p->nNodes*(2*p->nVars+p->nNodes-1)-p->nNodes+3*p->nNodes;  
    int litsize=pow(2,p->nVars); 
    int n_combs=pow(2,pow(2,p->nVars)-1);
    int n_p=pow(2,p->nVars-1);      
    int pLits[litsize]; 
    int pLits_p[litsize];
    int x_it=0; 
    p->i_p=p->iVar;
    for(int i=p->nVars+1;i<p->nVars+p->nNodes;i++){
        int p_startvar=p->iVar;
        p->iVar+=n_p;
        //printf("adding power CLauses for i:%d\n",i);
        sat_solver_setnvars( p->pSat, p->iVar); 
        for(int p=0;p<n_p;p++){
                pLits_p[p]=Abc_Var2Lit( p_startvar++ , 0);
        }  

        for(int m=1;m<n_combs;m++){ 
            for(int t=1;t<pow(2,p->nVars);t++){
                x_it = xi_base + 3*(i-p->nVars)+(t-1)*(3*p->nNodes);  
                pLits[t-1] = Abc_Var2Lit( x_it , value_of_nthbit(m, t-1));                
            }
            pLits[litsize-1]=pLits_p[amound_of_1s(m,litsize-1)-1];
            sat_solver_addclause( p->pSat, pLits, pLits+litsize );
        }
        ///////////////////////////////Sum(p)=1
        for (int j = 0; j < pow(2,n_p); j++)
        {
           int pLits_sum[2];
           int lit_sum=0;
           int res[n_p];
            convert_base_int(2,j,n_p,res);
            int sum=0;
            for (int l = 0; l < n_p; l++)
            {
                sum+=*(res+l);
            }
            if(sum==2){
                lit_sum=0;
                for (int l = 0; l < n_p; l++){
                        if(*(res+l)==1){                            
                            pLits[lit_sum++]=Abc_Var2Lit(p->i_p+(i-p->nVars-1)*n_p+l,1);
                        }
                }           
            sat_solver_addclause(p->pSat,pLits,pLits+lit_sum);                
            }
        }
        for (int j = 0; j < pow(2,n_p); j++)
        {
           int pLits_sum[2];
           int lit_sum=0;
           int res[n_p];
            convert_base_int(2,j,n_p,res);
            int sum=0;
            for (int l = 0; l < n_p; l++)
            {
                sum+=*(res+l);
            }
            if(sum==n_p){
                lit_sum=0;
                for (int l = 0; l < n_p; l++){
                        if(*(res+l)==1){                            
                            pLits[lit_sum++]=Abc_Var2Lit(p->i_p+(i-p->nVars-1)*n_p+l,0);
                        }
                }           
            sat_solver_addclause(p->pSat,pLits,pLits+lit_sum);                
            }
        }
        


    }
}

void Exa_ManAddCardinality_P_bdd(Exa_Man_t *p, int *combi, int xp)
{

    int n_i = p->nNodes - 1;
    int n_p = pow(2, p->nVars - 1) + 1;
    int m_len = 0;
    for (int i = 1; i <= pow(2, p->nVars) - 1; i++)
    {
        m_len += i;
    }
    int pi = xp;
    // printf("constrain for Sum:p_%d=%d\n",pi+1,*(combi+pi));
    int pLits[n_i];
    int lit = 0;
    int l = *(combi + pi);
    // less then l
    int j = l + 1;
    for (int i = 0; i < pow(2, n_i); i++)
    {
        int res[n_i];
        convert_base_int(2, i, n_i, res);
        int sum = 0;
        for (int l = 0; l < n_i; l++)
        {
            sum += *(res + l);
        }
        if (sum == j)
        {
            lit = 0;
            for (int l = 0; l < n_i; l++)
            {
                if (*(res + l) == 1)
                {
                    // printf("%d,",l+1);
                    pLits[lit++] = Abc_Var2Lit(p->i_p + m_len + l * (m_len + n_p) + pi + 1, 1);
                }
            }
            // printf("\n");
            sat_solver_addclause(p->pSat, pLits, pLits + lit);
        }
    }
    lit = 0;
    // more then l
    j = n_i - l + 1;
    for (int i = 0; i < pow(2, n_i); i++)
    {
        int res[n_i];
        convert_base_int(2, i, n_i, res);
        int sum = 0;
        for (int l = 0; l < n_i; l++)
        {
            sum += *(res + l);
        }
        if (sum == j)
        {
            lit = 0;
            for (int l = 0; l < n_i; l++)
            {
                if (*(res + l) == 1)
                {
                    pLits[lit++] = Abc_Var2Lit(p->i_p + m_len + l * (m_len + n_p) + pi + 1, 0);
                }
            }
            sat_solver_addclause(p->pSat, pLits, pLits + lit);
        }
        // }
    }
}

void Exa_ManAddCardinality_P_sw(Exa_Man_t *p, int *combi, bdd* BDD)
{
    
    
    int n_i = p->nNodes ;
    int n_p = pow(2, p->nVars - 1) + 1;
    int m_len = 0;
    for (int i = 1; i <= pow(2, p->nVars) - 1; i++)
    {
        m_len += i;
    }    
   int lit_const0_raw=p->iVar; 
   int lit_const0=Abc_Var2Lit(p->iVar,1);
   p->iVar+=1;
   sat_solver_setnvars( p->pSat, p->iVar);
   sat_solver_addclause(p->pSat,&lit_const0,&lit_const0+1);

   int lit_const1_raw=p->iVar;  
   int lit_const1=Abc_Var2Lit(p->iVar,0);
   p->iVar+=1;
   sat_solver_setnvars( p->pSat, p->iVar); 
   sat_solver_addclause(p->pSat,&lit_const1,&lit_const1+1);

   int lit=Exa_ManAddBDD_PCCs(p,BDD->start,lit_const0_raw,lit_const1_raw,m_len,n_p,p->i_p);
   lit=Abc_Var2Lit(lit,0);
   sat_solver_addclause(p->pSat,&lit,&lit+1);
}

int Exa_ManAddBDD_PCCs(Exa_Man_t *p,node* n,int lit0_const,int lit1_const,int m_len,int n_p,int i_p){    
    int lit_base=0;
    if(n!=NULL){  
            //printf("Node %d\n",n->id);                      
            lit_base=p->iVar;
            n->o_var=lit_base;
            n->constr=1;
            p->iVar+=1;
            sat_solver_setnvars(p->pSat, p->iVar);
            int r=n->i;
            int np=n->np; 
            int pi=p->i_p+m_len+r*(m_len+n_p)+np+1;
            if(n->end0==-1 && n->end1==-1){
                add_mux_encoding(p,lit_base,pi,lit0_const,lit0_const);
            }
            else if(n->end0==-2 && n->end1==-2){
                add_mux_encoding(p,lit_base,pi,lit1_const,lit1_const);
            }
            else if(n->end0==-2 && n->end1==-1){
                add_mux_encoding(p,lit_base,pi,lit0_const,lit1_const);
            }
            else if(n->end0==-1 && n->end1==-2){
                add_mux_encoding(p,lit_base,pi,lit1_const,lit0_const);
            }   
            else {
                if(n->end0==-1){
                    int lit1;
                              
                    //printf("n->n1->const:%d\n",(n->n1->constr==0));
                    if(n->n1->constr==0)            
                        lit1=Exa_ManAddBDD_PCCs(p,n->n1,lit0_const,lit1_const,m_len,n_p,p->i_p);
                    else
                        lit1=n->n1->o_var;
                   // printf("end0-1\n");
                    //printf("Node %d 0lit=%d\n",n->id,lit1);
                    add_mux_encoding(p,lit_base,pi,lit1,lit0_const);
                }
                else if(n->end0==-2){  
                    int lit1;
                    if(n->n1->constr==0)
                        lit1=Exa_ManAddBDD_PCCs(p,n->n1,lit0_const,lit1_const,m_len,n_p,p->i_p);
                    else
                       lit1=n->n1->o_var; 
                   // printf("end0-2\n");
                    //printf("1lit=%d\n",lit1);
                    add_mux_encoding(p,lit_base,pi,lit1,lit1_const);
                }
                else if(n->end1==-1){ 
                    int lit0;                   
                    if(n->n0->constr==0)
                        lit0=Exa_ManAddBDD_PCCs(p,n->n0,lit0_const,lit1_const,m_len,n_p,p->i_p);
                    else
                        lit0=n->n0->o_var;
                   // printf("end1-1\n");
                    //printf("2lit=%d\n",lit0);
                    add_mux_encoding(p,lit_base,pi,lit0_const,lit0);
                }
                else if(n->end1==-2){
                    int lit0;                    
                    if(n->n0->constr==0)
                        lit0=Exa_ManAddBDD_PCCs(p,n->n0,lit0_const,lit1_const,m_len,n_p,p->i_p);
                    else
                        lit0=n->n0->o_var;
                    //printf("end1-2 end1=%d\n",n->end1);
                    //printf("3lit=%d\n",lit0);
                    add_mux_encoding(p,lit_base,pi,lit1_const,lit0);
                }
                else{
                    int lit1;
                    if(n->n1->constr==0)
                        lit1=Exa_ManAddBDD_PCCs(p,n->n1,lit0_const,lit1_const,m_len,n_p,p->i_p);
                    else
                        lit1=n->n1->o_var;
                    int lit0;
                    if(n->n0->constr==0)
                        lit0=Exa_ManAddBDD_PCCs(p,n->n0,lit0_const,lit1_const,m_len,n_p,p->i_p);
                    else
                        lit0=n->n0->o_var;
                    //printf("4lit=%d\n",lit0);
                   // printf("5lit=%d\n",lit1);
                    add_mux_encoding(p,lit_base,pi,lit1,lit0);
                }
                
            }         
    }
    //printf("return\n");
    return lit_base;    
}

void Exa_ManAddCardinality_P(Exa_Man_t *p, int *combi, int xp, int grp)
{
    if (grp == 1)
    {
        if (p->o_l == 0)
            p->i_o = p->iVar;
        p->o_l++;
        int o_n = p->iVar;
        p->iVar += 1;
        sat_solver_setnvars(p->pSat, p->iVar);

        int n_i = p->nNodes - 1;
        int n_p = pow(2, p->nVars - 1);
        for (int pi = 0; pi < n_p; pi++)
        {
            // printf("constrain for Sum:p_%d=%d\n",pi+1,*(combi+pi));
            int pLits[n_i + 1];
            int lit = 0;
            int l = *(combi + pi);
            // less then l
            int j = l + 1;
            for (int i = 0; i < pow(2, n_i); i++)
            {
                int res[n_i];
                convert_base_int(2, i, n_i, res);
                int sum = 0;
                for (int l = 0; l < n_i; l++)
                {
                    sum += *(res + l);
                }
                if (sum == j)
                {
                    lit = 0;
                    pLits[0] = Abc_Var2Lit(o_n, 1);
                    for (int l = 0; l < n_i; l++)
                    {
                        if (*(res + l) == 1)
                        {
                            // printf("%d,",l+1);
                            pLits[lit + 1] = Abc_Var2Lit(p->i_p + l * n_p + pi, 1);
                            lit++;
                        }
                    }
                    // printf("\n");
                    sat_solver_addclause(p->pSat, pLits, pLits + lit + 1);
                }
            }
            lit = 0;
            // more then l
            j = n_i - l + 1;
            for (int i = 0; i < pow(2, n_i); i++)
            {
                int res[n_i];
                convert_base_int(2, i, n_i, res);
                int sum = 0;
                for (int l = 0; l < n_i; l++)
                {
                    sum += *(res + l);
                }
                if (sum == j)
                {
                    lit = 0;
                    pLits[0] = Abc_Var2Lit(o_n, 1);
                    for (int l = 0; l < n_i; l++)
                    {
                        if (*(res + l) == 1)
                        {
                            pLits[lit + 1] = Abc_Var2Lit(p->i_p + l * n_p + pi, 0);
                            lit++;
                        }
                    }
                    sat_solver_addclause(p->pSat, pLits, pLits + lit + 1);
                }
            }
        }
    }
    else
    {
        int n_i = p->nNodes - 1;
        int n_p = pow(2, p->nVars - 1);
        // for(int pi=0;pi<n_p;pi++){
        int pi = xp;
        // printf("constrain for Sum:p_%d=%d\n",pi+1,*(combi+pi));
        int pLits[n_i];
        int lit = 0;
        int l = *(combi + pi);
        // less then l
        int j = l + 1;
        for (int i = 0; i < pow(2, n_i); i++)
        {
            int res[n_i];
            convert_base_int(2, i, n_i, res);
            int sum = 0;
            for (int l = 0; l < n_i; l++)
            {
                sum += *(res + l);
            }
            if (sum == j)
            {
                lit = 0;
                for (int l = 0; l < n_i; l++)
                {
                    if (*(res + l) == 1)
                    {
                        // printf("%d,",l+1);
                        pLits[lit++] = Abc_Var2Lit(p->i_p + l * n_p + pi, 1);
                    }
                }
                // printf("\n");
                sat_solver_addclause(p->pSat, pLits, pLits + lit);
            }
        }
        lit = 0;
        // more then l
        j = n_i - l + 1;
        for (int i = 0; i < pow(2, n_i); i++)
        {
            int res[n_i];
            convert_base_int(2, i, n_i, res);
            int sum = 0;
            for (int l = 0; l < n_i; l++)
            {
                sum += *(res + l);
            }
            if (sum == j)
            {
                lit = 0;
                for (int l = 0; l < n_i; l++)
                {
                    if (*(res + l) == 1)
                    {
                        pLits[lit++] = Abc_Var2Lit(p->i_p + l * n_p + pi, 0);
                    }
                }
                sat_solver_addclause(p->pSat, pLits, pLits + lit);
            }
            // }
        }
    }
}








void Exa_ManAddOrClauses_equal1(Exa_Man_t * p){

    int o_l=p->o_l;
    int pLits[o_l];   
    //printf("i_o = %d\n",p->i_o); 
    ///////////////////////////////Sum(o)=1
        for (int j = 0; j < pow(2,o_l); j++)
        {
            int pLits_sum[2];
            int lit_sum=0;
            int res[o_l];
            convert_base_int(2,j,o_l,res);
            int sum=0;
            for (int l = 0; l < o_l; l++)
            {
                sum+=*(res+l);
            }
            if(sum==2){
                lit_sum=0;
                for (int l = 0; l < o_l; l++){
                        if(*(res+l)==1){                            
                            pLits[lit_sum++]=Abc_Var2Lit(p->i_o+l,1);
                        }
                }           
            sat_solver_addclause(p->pSat,pLits,pLits+lit_sum);                
            }
        }

        for (int j = 0; j < pow(2,o_l); j++)
        {
           int pLits_sum[2];
           int lit_sum=0;
           int res[o_l];
            convert_base_int(2,j,o_l,res);
            int sum=0;
            for (int l = 0; l < o_l; l++)
            {
                sum+=*(res+l);
            }
            if(sum==o_l){
                lit_sum=0;
                for (int l = 0; l < o_l; l++){
                        if(*(res+l)==1){                            
                            pLits[lit_sum++]=Abc_Var2Lit(p->i_o+l,0);
                        }
                }           
            sat_solver_addclause(p->pSat,pLits,pLits+lit_sum);                
            }
        }
}



void convert_base_int(int base,int value,int size,int* results){
    
    int r;
    for (int i = 0; i < size; i++)
    {
        r=value%base;
        results[i]=r;
        value=value/base;
        
    }
    
    return results;
}

void calculate_comb_array(int k,int r,comb_list* list){
    if(r==0)
        return 0;    
    int size=pow(r+1,pow(2,k-1));    
    int size_single=pow(2,k-1);
    int array_single[size_single];   
    for(int i=0;i<size_single;i++){
        array_single[i]= 2*(i+1)*(pow(2,k)-(i+1));
        //printf("for i=%d:%d\n",i,array_single[i]);
    }
    for(int i=0;i<size;i++){
      // printf("i:%d\n",i);
       int res[size_single];
       convert_base_int(r+1,i,size_single,res);
       int sum=0;
       int sum_act=0;
       for (int j = 0; j < size_single; j++)
       {
        sum+=*(res+j);
        sum_act+=array_single[j]*(*(res+j));
        if(sum>r)
            j=size_single;
        }
       
       if(sum == r){
            if(k==4){
                int p1=*(res);
                int p2=*(res+1);
                int p3=*(res+2);
                int p4=*(res+3);
                int p5=*(res+4);
                int p6=*(res+5);
                int p7=*(res+6);
                int p8=*(res+7);
                int exep1=(p4>=2)|(p8>01)|((p4>=1)&&(p8>=1))|(((p4>=1)|(p8>=1))&&((p2>=1)|(p6>=1)));
                int exep2=(*(res)<=r-2)&&(*(res+1)<=r-1)&&(*(res+2)<=r-1)&&(*(res+4)<=r-2)&&(*(res+5)<=r-1)&&(*(res+6)<=r-2);
                if(exep1==1 && exep2==1)
                  add_combi(sum_act,r,res,list);  
            }
            else
                add_combi(sum_act,r,res,list);
            /*
            for (int j = size_single-1; j >= 0; j--)
            {
                printf("%d;",*(res+j));
            }
            printf("->sum: %d\n",sum_act);
            printf("\n");*/
            
       }
       
       
    }
}

int calc_max_r(int act,int k){
    int ret=(int)((act/(pow(2,k+1)-2)));
    ret = ret==0 ? 1 : ret;
    return ret;
}
int calc_min_r(int act,int k){
    int ret=(int)((act/(pow(2,2*k)-pow(2,2*k-1)))+0.5);
    ret = ret==0 ? 1 : ret;
    return ret;
}

int calc_max_act(int r,int k){    
    int ret=(int)(((pow(2,k+1)-2))*r);
    return ret;
}
int calc_min_act(int r,int k){
    int ret=(int)(((pow(2,2*k)-pow(2,2*k-1)))*r);
    return ret;
}







/*
void Exa_ManExactPowerSynthesis2( Bmc_EsPar_t * pPars )
{
    int i, status, iMint = 1;
    abctime clkTotal = Abc_Clock();
    Exa_Man_t * p; int fCompl = 0;
    word pTruth[16]; Abc_TtReadHex( pTruth, pPars->pTtStr );
    assert( pPars->nVars <= 10 );
    p = Exa_ManAlloc( pPars, pTruth );
    if ( pTruth[0] & 1 ) { fCompl = 1; Abc_TtNot( pTruth, p->nWords ); }
    status = Exa_ManAddCnfStart( p, pPars->fOnlyAnd );
    assert( status );
    printf( "Running exact synthesis for %d-input function with %d two-input gates...\n", p->nVars, p->nNodes );
    for ( iMint = 1; iMint <pow(2,p->nVars); iMint++ )
    {
        abctime clk = Abc_Clock();
        if ( !Exa_ManAddCnf( p, iMint)){
            printf( "The problem has no solution.\n" );
            iMint=0;
            break;
        }
        //status = sat_solver_solve( p->pSat, NULL, NULL, 0, 0, 0, 0 );
        if ( pPar###Calculate Node for act=32 i=1 i_act=32
len=8,ptr_start=1
##bdd_calc1=2s->fVerbose )
        {
            printf( "Iter %3d : ", i );
            Extra_PrintBinary( stdout, (unsigned *)&iMint, p->nVars );
            printf( "  Var =%5d  ", p->iVar );
            printf( "Cla =%6d  ", sat_solver_nclauses(p->pSat) );
            printf( "Conf =%9d  ", sat_solver_nconflicts(p->pSat) );
            Abc_PrintTime( 1, "Time", Abc_Clock() - clk );
        }
        if ( status == l_False )
        {
            printf( "The problem has no solution.\n" );
            iMint=0;
            break;
        }
       
    }
    Exa_ManAddPClauses(p);
    int combi[8];
    combi[0]=1;
    combi[1]=1;   
    combi[2]=0;
    combi[3]=2;
    combi[4]=0;
    combi[5]=0;
    combi[6]=0;
    combi[7]=1;
    printf("Adding Sum Constraints\n"); 
    Exa_ManAddCardinality_P(p,&combi); 
    combi[0]=2;
    combi[1]=0;   
    combi[2]=0;
    combi[3]=0;
    combi[4]=2;
    combi[5]=0;
    combi[6]=1;
    combi[7]=0;
    printf("Adding Sum Constraints\n"); 
    Exa_ManAddCardinality_P(p,&combi); 
    combi[0]=0;
    combi[1]=2;   
    combi[2]=1;
    combi[3]=1;
    combi[4]=0;
    combi[5]=1;
    combi[6]=0;
    combi[7]=0;
    Exa_ManAddCardinality_P(p,&combi);
    combi[0]=1;
    combi[1]=0;   
    combi[2]=2;
    combi[3]=0;
    combi[4]=2;
    combi[5]=0;
    combi[6]=0;
    combi[7]=0;
    Exa_ManAddCardinality_P(p,&combi);

    printf("Adding Sum(0) equal 1 Constraints\n");
    Exa_ManAddOrClauses_equal1(p);
    
    status = sat_solver_solve( p->pSat, NULL, NULL, 0, 0, 0, 0 );
    printf("solution: %d \n",status);
    if ( status == 1 )    
        Exa_ManPrintSolution( p, fCompl );
    Exa_ManFree( p );
    Abc_PrintTime( 1, "Total runtime", Abc_Clock() - clkTotal );
}*/


void Exa_ManExactPowerSynthesis2( Bmc_EsPar_t * pPars ){           
        int i, status, iMint = 1;
        abctime clkTotal = Abc_Clock();
        Exa_Man_t * p; int fCompl = 0;
        word pTruth[16]; Abc_TtReadHex( pTruth, pPars->pTtStr );
        assert( pPars->nVars <= 10 );
        p = Exa_ManAlloc( pPars, pTruth );
        if ( pTruth[0] & 1 ) { fCompl = 1; Abc_TtNot( pTruth, p->nWords );}            
        comb_list* list=(comb_list*) malloc(sizeof(comb_list));
        list->len=pow(2,p->nVars-1);
        list->length=0;
        int r=0; 
        int act=0;
        while (1)
            {                
                if(act >= calc_max_act(r+1,p->nVars)){                    
                    r++;
                    //////////////////////////Check if there is a general solution for r
                    Exa_ManFree( p );
                    pPars->nNodes=r+1;
                    p = Exa_ManAlloc( pPars, pTruth );
                    status = Exa_ManAddCnfStart( p, pPars->fOnlyAnd);
                    assert( status );                   
                    for ( iMint = 1; iMint <pow(2,p->nVars); iMint++ )
                    {                        
                        if ( !Exa_ManAddCnf( p, iMint)){
                            printf( "The problem has no solution.\n" );
                            break;
                        }           
                    }
                    status = sat_solver_solve( p->pSat, NULL, NULL, 0, 0, 0, 0 );
                    //////////////////////////
                    if(status==1){
                        calculate_comb_array(p->nVars,r,list);
                        printf("######ACT:%d -> R= %d ADDED\n",act,r+1);                                                
                        }                        
                    else
                        printf("######ACT:%d No general Solution for r=%d\n",act,r+1);                        
                        
                }
                if(list->length >0){
                    if(list->start->act==act){
                            comb* node=pop_comb(list);
                            printf("###ACT:%d,r:%d CONSUMED COMBINATION:",(node->act),node->r+1);
                            for (int im = 0; im < list->len; im++)
                            {
                                printf("%d,",*(node->combi+im));
                            }
                            printf("\n");
                            ////////////////////////////////////////////////////programm sat solver
                            Exa_ManFree( p );
                            pPars->nNodes=node->r+1;
                            p = Exa_ManAlloc( pPars, pTruth );
                            status = Exa_ManAddCnfStart( p, pPars->fOnlyAnd);
                            assert( status );
                            printf("Adding Minterm Clauses\n");
                            for ( iMint = 1; iMint <pow(2,p->nVars); iMint++ )
                            {
                                abctime clk = Abc_Clock();
                                if ( !Exa_ManAddCnf( p, iMint)){
                                    printf( "The problem has no solution.\n" );
                                    break;
                                }           
                            }
                            Exa_ManAddPClauses(p);
                            printf("##Adding Sum Constraints\n"); 
                            int arr_xp[list->len];
                            for (int ax = 0; ax < list->len; ax++)
                            {
                               arr_xp[ax]=-1;
                            }
                            int xp=0;
                            
                            for (int i0 = 0; i0 < list->len; i0++)
                            {
                                printf("#CHECKING p_%d =%d\n",i0+1,*(node->satfy+i0));
                                if(*(node->satfy+i0)!=-1){
                                    Exa_ManAddCardinality_P(p,node->combi,i0,0);
                                    printf("Already tried p_%d -> skipped\n",i0+1);
                                    arr_xp[i0]=*(node->combi+i0);
                                    xp=i0+1;
                                }
                               
                            }
                            while( xp >= 0 )
                            {
                            printf("#CEGAR Constraining Sum(p_%d) == %d\n",xp+1,*(node->combi+xp));
                            Exa_ManAddCardinality_P(p,node->combi,xp,0);
                            arr_xp[xp]=*(node->combi+xp);   
                            
                            //Grouping
                            /*   
                            while(list->start->act==act && list->start->r+1==p->nNodes){
                                free(node->combi);
                                free(node);
                                node=pop_comb(list);
                                Exa_ManAddCardinality_P(p,node->combi);  
                                printf("#Grouping with ACT:%d,r:%d CONSUMED COMBINATION:",(node->act),node->r+1);
                                for (int im = 0; im < list->len; im++)
                                {
                                    printf("%d,",*(node->combi+im));
                                }
                                printf("\n");
                            }*/
                            //printf("Adding Sum(0) equal 1 Constraints\n");
                            //Exa_ManAddOrClauses_equal1(p);
                                                   
                                status = sat_solver_solve( p->pSat, NULL, NULL, 0, 0, 0, 0 );
                                printf("solution: %d \n",status);
                                if ( status == 1 ){
                                    add_satfy_values(list,node->r,arr_xp);
                                    xp=Exa_ManEvalPVariables(p,node->combi);
                                    if(xp==-1){
                                        free(node->combi);
                                        free(node); 
                                        Exa_ManPrintSolution( p, fCompl );
                                        Exa_ManFree( p );
                                        Abc_PrintTime( 1, "Total runtime", Abc_Clock() - clkTotal );
                                        break;
                                    }
                                    
                                }
                                else{
                                    xp=-2;
                                    printf("removing combis with no solution \n");
                                    remove_combis(list,node->r,arr_xp);
                                    //print_combi_list(list);
                                    }
                                    

                            }
                            //printf("Loop breakout\n");  
                            free(node->combi);
                            free(node); 
                            ////////////////////////////////////////////////////
                            continue;
                    }
                } 
                act++;
                if(act>2000)
                    break;
            }
            free_comb_list(list);
            //print_combi_list(list);       
}

int amound_of_1s(int value,int len){
    int ret_1=0;
    int ret_0=1;
    for(int i=0;i<len;i++){
        ret_1+=value&1;
        ret_0+=!(value&1);
        value>>=1;
    }
    return ret_0>=ret_1 ? ret_1 : ret_0;
}

int value_of_nthbit(int value, int n){
    int ret=(value>>n)&1;
    return ret;
}
////////////////////////////////////////////////////////////////////base
void Exa_ManExactPowerSynthesis_base(Bmc_EsPar_t *pPars)
{
    int i, status, iMint = 1;
    abctime clkTotal = Abc_Clock();
    Exa_Man_t *p;
    int fCompl = 0;
    word pTruth[16];
    Abc_TtReadHex(pTruth, pPars->pTtStr);
    assert(pPars->nVars <= 10);
    p = Exa_ManAlloc(pPars, pTruth);
    if (pTruth[0] & 1)
    {
        fCompl = 1;
        Abc_TtNot(pTruth, p->nWords);
    }
    comb_list *list = (comb_list *)malloc(sizeof(comb_list));
    list->len = pow(2, p->nVars - 1);
    list->length = 0;
    int r = 0;
    int act = 0;
    while (1)
    {
        //printf("ACT=%d\n",act);
        if (act >= calc_max_act(r + 1, p->nVars))
        {
           
            r++;
            pPars->nNodes = r + 1;
            calculate_comb_array(p->nVars, r, list);
            printf("######ACT:%d -> R= %d ADDED\n", act, r + 1);
            //print_combi_list(list);
        }
        if (list->length > 0)
        {            
            if (list->start->act == act)
            {
                comb *node = pop_comb(list);
                printf("###ACT:%d,r:%d CONSUMED COMBINATION:", (node->act), node->r + 1);
                for (int im = 0; im < list->len; im++)
                {
                    printf("%d,", *(node->combi + im));
                }
                printf("\n");
                ////////////////////////////////////////////////////programm sat solver
                Exa_ManFree(p);
                pPars->nNodes = node->r + 1;
                p = Exa_ManAlloc(pPars, pTruth);
                status = Exa_ManAddCnfStart(p, pPars->fOnlyAnd);
                printf("#Added Base Constraints -> %d Clauses\n",sat_solver_nclauses(p->pSat));
                assert(status);                
                for (iMint = 1; iMint < pow(2, p->nVars); iMint++)
                {
                    abctime clk = Abc_Clock();
                    if (!Exa_ManAddCnf(p, iMint))
                    {
                        printf("The problem has no solution.\n");
                        break;
                    }
                }
                printf("#Added Minterm Constraints -> %d Clauses\n",sat_solver_nclauses(p->pSat));
                Exa_ManAddPClauses_bdd(p);
                printf("#Added P Constraints -> %d Clauses\n",sat_solver_nclauses(p->pSat));
                for (int i0 = 0; i0 < list->len; i0++)
                {
                    Exa_ManAddCardinality_P_bdd(p, node->combi, i0);
                }
                printf("#Added P Card. Constraints -> %d Clauses\n",sat_solver_nclauses(p->pSat));
                status = sat_solver_solve(p->pSat, NULL, NULL, 0, 0, 0, 0);
                printf("###Solution: %d \n", status);
                if (status == 1)
                {
                    free(node->satfy);
                    free(node->combi);
                    free(node);
                    Exa_ManPrintSolution_bdd(p, fCompl);
                    Exa_ManFree(p);
                    Abc_PrintTime(1, "Total runtime", Abc_Clock() - clkTotal);
                    break;
                }
            free(node->satfy);
            free(node->combi);
            free(node);
            continue;
            }
            ////////////////////////////////////////////////////
        }        
        act++;

        if (act > 2000)
            break;
    }    
    free_comb_list(list);
}
////////////////////////////////////////////////////////////////////Grouping+skipping-nonsat-r's
void Exa_ManExactPowerSynthesis_gr_skip(Bmc_EsPar_t *pPars)
{
    int i, status, iMint = 1;
    abctime clkTotal = Abc_Clock();
    Exa_Man_t *p;
    int fCompl = 0;
    word pTruth[16];
    Abc_TtReadHex(pTruth, pPars->pTtStr);
    assert(pPars->nVars <= 10);
    p = Exa_ManAlloc(pPars, pTruth);
    if (pTruth[0] & 1)
    {
        fCompl = 1;
        Abc_TtNot(pTruth, p->nWords);
    }
    comb_list *list = (comb_list *)malloc(sizeof(comb_list));
    list->len = pow(2, p->nVars - 1);
    list->length = 0;
    int r = 0;
    int act = 0;
    while (1)
    {
        if (act >= calc_max_act(r + 1, p->nVars))
        {
            r++;
            //////////////////////////Check if there is a general solution for r
            Exa_ManFree(p);
            pPars->nNodes = r + 1;
            p = Exa_ManAlloc(pPars, pTruth);
            status = Exa_ManAddCnfStart(p, pPars->fOnlyAnd);
            assert(status);
            for (iMint = 1; iMint < pow(2, p->nVars); iMint++)
            {
                if (!Exa_ManAddCnf(p, iMint))
                {
                    printf("The problem has no solution.\n");
                    break;
                }
            }
            status = sat_solver_solve(p->pSat, NULL, NULL, 0, 0, 0, 0);
            //////////////////////////
            if (status == 1)
            {
                calculate_comb_array(p->nVars, r, list);
                printf("######ACT:%d -> R= %d ADDED\n", act, r + 1);
            }
            else
                printf("######ACT:%d No general Solution for r=%d\n", act, r + 1);
        }
        if (list->length > 0)
        {
            if (list->start->act == act)
            {
                comb *node = pop_comb(list);
                printf("###ACT:%d,r:%d CONSUMED COMBINATION:", (node->act), node->r + 1);
                for (int im = 0; im < list->len; im++)
                {
                    printf("%d,", *(node->combi + im));
                }
                printf("\n");
                ////////////////////////////////////////////////////programm sat solver
                Exa_ManFree(p);
                pPars->nNodes = node->r + 1;
                p = Exa_ManAlloc(pPars, pTruth);
                status = Exa_ManAddCnfStart(p, pPars->fOnlyAnd);
                assert(status);
                printf("Adding Minterm Clauses\n");
                for (iMint = 1; iMint < pow(2, p->nVars); iMint++)
                {
                    abctime clk = Abc_Clock();
                    if (!Exa_ManAddCnf(p, iMint))
                    {
                        printf("The problem has no solution.\n");
                        break;
                    }
                }
                Exa_ManAddPClauses(p);
                printf("##Adding Sum Constraints\n");               
                Exa_ManAddCardinality_P(p, node->combi, 0, 1);

                while (list->start->act == act && list->start->r + 1 == p->nNodes)
                {
                    free(node->satfy);
                    free(node->combi);
                    free(node);
                    node = pop_comb(list);                    
                    Exa_ManAddCardinality_P(p, node->combi, 0, 1);                                        
                    printf("#Grouping with ACT:%d,r:%d CONSUMED COMBINATION:", (node->act), node->r + 1);
                    for (int im = 0; im < list->len; im++)
                    {
                        printf("p_1%d,", *(node->combi + im));
                    }
                    printf("\n");
                }
                printf("Adding Sum(0) equal 1 Constraints\n");
                Exa_ManAddOrClauses_equal1(p);

                status = sat_solver_solve(p->pSat, NULL, NULL, 0, 0, 0, 0);
                printf("solution: %d \n", status);
                if (status == 1)
                {
                    free(node->satfy);
                    free(node->combi);
                    free(node);
                    Exa_ManPrintSolution(p, fCompl);
                    Exa_ManFree(p);
                    Abc_PrintTime(1, "Total runtime", Abc_Clock() - clkTotal);
                    break;
                }

                // printf("Loop breakout\n");
                free(node->satfy);
                free(node->combi);
                free(node);
                ////////////////////////////////////////////////////
                continue;
            }
        }
        act++;
        if (act > 2000)
            break;
    }
    free_comb_list(list);
    // print_combi_list(list);
}

////////////////////////////////////////////////////////////////////skipping-nonsat-r's+CEGAR for p variables
void Exa_ManExactPowerSynthesis_cegar(Bmc_EsPar_t *pPars)
{
    int i, status, iMint = 1;
    abctime clkTotal = Abc_Clock();
    Exa_Man_t *p;
    int fCompl = 0;
    word pTruth[16];
    Abc_TtReadHex(pTruth, pPars->pTtStr);
    assert(pPars->nVars <= 10);
    p = Exa_ManAlloc(pPars, pTruth);
    if (pTruth[0] & 1)
    {
        fCompl = 1;
        Abc_TtNot(pTruth, p->nWords);
    }
    comb_list *list = (comb_list *)malloc(sizeof(comb_list));
    list->len = pow(2, p->nVars - 1);
    list->length = 0;
    int r = 0;
    int act = 0;
    while (1)
    {
        if (act >= calc_max_act(r + 1, p->nVars))
        {
            r++;
            //////////////////////////Check if there is a general solution for r
            Exa_ManFree(p);
            pPars->nNodes = r + 1;
            p = Exa_ManAlloc(pPars, pTruth);
            status = Exa_ManAddCnfStart(p, pPars->fOnlyAnd);
            assert(status);
            for (iMint = 1; iMint < pow(2, p->nVars); iMint++)
            {
                if (!Exa_ManAddCnf(p, iMint))
                {
                    printf("The problem has no solution.\n");
                    break;
                }
            }
            status = sat_solver_solve(p->pSat, NULL, NULL, 0, 0, 0, 0);
            //////////////////////////
            if (status == 1)
            {
                calculate_comb_array(p->nVars, r, list);
                printf("######ACT:%d -> R= %d ADDED\n", act, r + 1);
            }
            else
                printf("######ACT:%d No general Solution for r=%d\n", act, r + 1);
        }
        if (list->length > 0)
        {
            if (list->start->act == act)
            {
                comb *node = pop_comb(list);
                printf("###ACT:%d,r:%d CONSUMED COMBINATION:", (node->act), node->r + 1);
                for (int im = 0; im < list->len; im++)
                {
                    printf("%d,", *(node->combi + im));
                }
                printf("\n");
                ////////////////////////////////////////////////////programm sat solver
                Exa_ManFree(p);
                pPars->nNodes = node->r + 1;
                p = Exa_ManAlloc(pPars, pTruth);
                status = Exa_ManAddCnfStart(p, pPars->fOnlyAnd);
                assert(status);
                printf("Adding Minterm Clauses\n");
                for (iMint = 1; iMint < pow(2, p->nVars); iMint++)
                {
                    abctime clk = Abc_Clock();
                    if (!Exa_ManAddCnf(p, iMint))
                    {
                        printf("The problem has no solution.\n");
                        break;
                    }
                }
                Exa_ManAddPClauses(p);
                printf("##Adding Sum Constraints\n");
                int arr_xp[list->len];
                for (int ax = 0; ax < list->len; ax++)
                {
                    arr_xp[ax] = -1;
                }
                int xp = 0;
                while (xp >= 0)
                {
                    printf("#CEGAR Constraining Sum(p_%d) == %d\n", xp + 1, *(node->combi + xp));
                    Exa_ManAddCardinality_P(p, node->combi, xp, 0);
                    arr_xp[xp] = *(node->combi + xp);
                    status = sat_solver_solve(p->pSat, NULL, NULL, 0, 0, 0, 0);
                    printf("solution: %d \n", status);
                    if (status == 1)
                    {
                        xp = Exa_ManEvalPVariables(p, node->combi);
                        if (xp == -1)
                        {
                            free(node->satfy);
                            free(node->combi);
                            free(node);
                            Exa_ManPrintSolution(p, fCompl);
                            Exa_ManFree(p);
                            Abc_PrintTime(1, "Total runtime", Abc_Clock() - clkTotal);
                            break;
                        }
                    }
                    else
                    {
                        xp = -1;
                    }
                }
                // printf("Loop breakout\n");
                free(node->satfy);
                free(node->combi);
                free(node);
                ////////////////////////////////////////////////////
                continue;
            }
        }
        act++;
        if (act > 2000)
            break;
    }
    free_comb_list(list);
}
////////////////////////////////////////////////////////////////////skipping-nonsat-r's+CEGAR for p variables+removing nonsat combis+storing redundant combis
void Exa_ManExactPowerSynthesis_cegar2(Bmc_EsPar_t *pPars)
{
    int i, status, iMint = 1;
    abctime clkTotal = Abc_Clock();
    Exa_Man_t *p;
    int fCompl = 0;
    word pTruth[16];
    Abc_TtReadHex(pTruth, pPars->pTtStr);
    assert(pPars->nVars <= 10);
    p = Exa_ManAlloc(pPars, pTruth);
    if (pTruth[0] & 1)
    {
        fCompl = 1;
        Abc_TtNot(pTruth, p->nWords);
    }
    comb_list *list = (comb_list *)malloc(sizeof(comb_list));
    list->len = pow(2, p->nVars - 1);
    list->length = 0;
    int r = 0;
    int act = 0;
    while (1)
    {
        if (act >= calc_max_act(r + 1, p->nVars))
        {
            r++;
            //////////////////////////Check if there is a general solution for r
            Exa_ManFree(p);
            pPars->nNodes = r + 1;
            p = Exa_ManAlloc(pPars, pTruth);
            status = Exa_ManAddCnfStart(p, pPars->fOnlyAnd);
            assert(status);
            for (iMint = 1; iMint < pow(2, p->nVars); iMint++)
            {
                if (!Exa_ManAddCnf(p, iMint))
                {
                    printf("The problem has no solution.\n");
                    break;
                }
            }
            status = sat_solver_solve(p->pSat, NULL, NULL, 0, 0, 0, 0);
            //////////////////////////
            if (status == 1)
            {
                calculate_comb_array(p->nVars, r, list);
                printf("######ACT:%d -> R= %d ADDED\n", act, r + 1);
            }
            else
                printf("######ACT:%d No general Solution for r=%d\n", act, r + 1);
        }
        if (list->length > 0)
        {
            if (list->start->act == act)
            {
                comb *node = pop_comb(list);
                printf("###ACT:%d,r:%d CONSUMED COMBINATION:", (node->act), node->r + 1);
                for (int im = 0; im < list->len; im++)
                {
                    printf("%d,", *(node->combi + im));
                }
                printf("\n");
                ////////////////////////////////////////////////////programm sat solver
                Exa_ManFree(p);
                pPars->nNodes = node->r + 1;
                p = Exa_ManAlloc(pPars, pTruth);
                status = Exa_ManAddCnfStart(p, pPars->fOnlyAnd);
                assert(status);
                printf("Adding Minterm Clauses\n");
                for (iMint = 1; iMint < pow(2, p->nVars); iMint++)
                {
                    abctime clk = Abc_Clock();
                    if (!Exa_ManAddCnf(p, iMint))
                    {
                        printf("The problem has no solution.\n");
                        break;
                    }
                }
                Exa_ManAddPClauses(p);
                printf("##Adding Sum Constraints\n");
                int arr_xp[list->len];
                for (int ax = 0; ax < list->len; ax++)
                {
                    arr_xp[ax] = -1;
                }
                int xp = 0;

                for (int i0 = 0; i0 < list->len; i0++)
                {
                    printf("#CHECKING p_%d =%d\n", i0 + 1, *(node->satfy + i0));
                    if (*(node->satfy + i0) != -1)
                    {
                        Exa_ManAddCardinality_P(p, node->combi, i0, 0);
                        printf("Already tried p_%d -> skipped\n", i0 + 1);
                        arr_xp[i0] = *(node->combi + i0);
                        xp = i0 + 1;
                    }
                }
                while (xp >= 0)
                {
                    printf("#CEGAR Constraining Sum(p_%d) == %d\n", xp + 1, *(node->combi + xp));
                    Exa_ManAddCardinality_P(p, node->combi, xp, 0);
                    arr_xp[xp] = *(node->combi + xp);
                    status = sat_solver_solve(p->pSat, NULL, NULL, 0, 0, 0, 0);
                    printf("solution: %d \n", status);
                    if (status == 1)
                    {
                        add_satfy_values(list, node->r, arr_xp);
                        xp = Exa_ManEvalPVariables(p, node->combi);
                        if (xp == -1)
                        {
                            free(node->satfy);
                            free(node->combi);
                            free(node);
                            Exa_ManPrintSolution(p, fCompl);
                            Exa_ManFree(p);
                            Abc_PrintTime(1, "Total runtime", Abc_Clock() - clkTotal);
                            break;
                        }
                    }
                    else
                    {
                        xp = -1;
                        printf("removing combis with no solution \n");
                        remove_combis(list, node->r, arr_xp);
                        // print_combi_list(list);
                    }
                }
                // printf("Loop breakout\n");
                free(node->satfy);
                free(node->combi);
                free(node);
                ////////////////////////////////////////////////////
                continue;
            }
        }
        act++;
        if (act > 2000)
            break;
    }
    free_comb_list(list);
    // print_combi_list(list);
}
/////////////////////////////////////////////////////////////base bdd 
void Exa_ManExactPowerSynthesis_base_bdd(Bmc_EsPar_t *pPars)
{
    int i, status, iMint = 1;
    abctime clkTotal = Abc_Clock();
    Exa_Man_t *p;
    int fCompl = 0;
    word pTruth[16];
    Abc_TtReadHex(pTruth, pPars->pTtStr);
    assert(pPars->nVars <= 10);
    p = Exa_ManAlloc(pPars, pTruth);
    if (pTruth[0] & 1)
    {
        fCompl = 1;
        Abc_TtNot(pTruth, p->nWords);
    }
    comb_list *list = (comb_list *)malloc(sizeof(comb_list));
    list->len = pow(2, p->nVars - 1);
    list->length = 0;
    int r = 0;
    int act = 0;
    while (1)
    {
        //printf("ACT=%d\n",act);
        if (act >= calc_max_act(r + 1, p->nVars))
        {
           
            r++;
            pPars->nNodes = r + 1;
            calculate_comb_array(p->nVars, r, list);
            printf("######ACT:%d -> R= %d ADDED\n", act, r + 1);
            //print_combi_list(list);
        }
        if (list->length > 0)
        {            
            if (list->start->act == act)
            {
                comb *node = pop_comb(list);
                printf("###ACT:%d,r:%d CONSUMED COMBINATION:", (node->act), node->r + 1);
                for (int im = 0; im < list->len; im++)
                {
                    printf("%d,", *(node->combi + im));
                }
                printf("\n");
                ////////////////////////////////////////////////////programm sat solver
                Exa_ManFree(p);
                pPars->nNodes = node->r + 1;
                p = Exa_ManAlloc(pPars, pTruth);
                status = Exa_ManAddCnfStart(p, pPars->fOnlyAnd);
                printf("#Added Base Constraints -> %d Clauses\n",sat_solver_nclauses(p->pSat));
                assert(status);                
                for (iMint = 1; iMint < pow(2, p->nVars); iMint++)
                {
                    abctime clk = Abc_Clock();
                    if (!Exa_ManAddCnf(p, iMint))
                    {
                        printf("The problem has no solution.\n");
                        break;
                    }
                }
                printf("#Added Minterm Constraints -> %d Clauses\n",sat_solver_nclauses(p->pSat));
                Exa_ManAddPClauses_bdd(p);
                printf("#Added P Constraints -> %d Clauses\n",sat_solver_nclauses(p->pSat));
                for (int i0 = 0; i0 < list->len; i0++)
                {
                    Exa_ManAddCardinality_P_bdd(p, node->combi, i0);
                }
                printf("#Added P Card. Constraints -> %d Clauses\n",sat_solver_nclauses(p->pSat));
                status = sat_solver_solve(p->pSat, NULL, NULL, 0, 0, 0, 0);
                printf("###Solution: %d \n", status);
                if (status == 1)
                {
                    free(node->satfy);
                    free(node->combi);
                    free(node);
                    Exa_ManPrintSolution_bdd(p, fCompl);
                    Exa_ManFree(p);
                    Abc_PrintTime(1, "Total runtime", Abc_Clock() - clkTotal);
                    break;
                }
            free(node->satfy);
            free(node->combi);
            free(node);
            continue;
            }
            
            ////////////////////////////////////////////////////
            
        }        
        act++;

        if (act > 2000)
            break;
    }    
    free_comb_list(list);
}
/////////////////////////////////////////////////cegar2 bdd
void Exa_ManExactPowerSynthesis_cegar2_bdd(Bmc_EsPar_t *pPars)
{
    int i, status, iMint = 1;
    abctime clkTotal = Abc_Clock();
    Exa_Man_t *p;
    int fCompl = 0;
    word pTruth[16];
    Abc_TtReadHex(pTruth, pPars->pTtStr);
    assert(pPars->nVars <= 10);
    p = Exa_ManAlloc(pPars, pTruth);
    if (pTruth[0] & 1)
    {
        fCompl = 1;
        Abc_TtNot(pTruth, p->nWords);
    }
    comb_list *list = (comb_list *)malloc(sizeof(comb_list));
    list->len = pow(2, p->nVars - 1);
    list->length = 0;
    int r = 0;
    int act = 0;
    while (1)
    {
        if (act >= calc_max_act(r + 1, p->nVars))
        {
            r++;
            //////////////////////////Check if there is a general solution for r
            Exa_ManFree(p);
            pPars->nNodes = r + 1;
            p = Exa_ManAlloc(pPars, pTruth);
            status = Exa_ManAddCnfStart(p, pPars->fOnlyAnd);
            assert(status);
            for (iMint = 1; iMint < pow(2, p->nVars); iMint++)
            {
                if (!Exa_ManAddCnf(p, iMint))
                {
                    printf("The problem has no solution.\n");
                    break;
                }
            }
            status = sat_solver_solve(p->pSat, NULL, NULL, 0, 0, 0, 0);
            //////////////////////////
            if (status == 1)
            {
                calculate_comb_array(p->nVars, r, list);
                printf("######ACT:%d -> R= %d ADDED\n", act, r + 1);
            }
            else
                printf("######ACT:%d No general Solution for r=%d\n", act, r + 1);
        }
        if (list->length > 0)
        {
            if (list->start->act == act)
            {
                comb *node = pop_comb(list);
                printf("###ACT:%d,r:%d CONSUMED COMBINATION:", (node->act), node->r + 1);
                for (int im = 0; im < list->len; im++)
                {
                    printf("%d,", *(node->combi + im));
                }
                printf("\n");
                ////////////////////////////////////////////////////programm sat solver
                Exa_ManFree(p);
                pPars->nNodes = node->r + 1;
                p = Exa_ManAlloc(pPars, pTruth);
                status = Exa_ManAddCnfStart(p, pPars->fOnlyAnd);
                assert(status);
                printf("Adding Minterm Clauses\n");
                for (iMint = 1; iMint < pow(2, p->nVars); iMint++)
                {
                    abctime clk = Abc_Clock();
                    if (!Exa_ManAddCnf(p, iMint))
                    {
                        printf("The problem has no solution.\n");
                        break;
                    }
                }
                Exa_ManAddPClauses_bdd(p);
                printf("##Adding Sum Constraints\n");
                int arr_xp[list->len];
                for (int ax = 0; ax < list->len; ax++)
                {
                    arr_xp[ax] = -1;
                }
                int xp = 0;

                for (int i0 = 0; i0 < list->len; i0++)
                {
                    printf("#CHECKING p_%d =%d\n", i0 + 1, *(node->satfy + i0));
                    if (*(node->satfy + i0) != -1)
                    {
                        Exa_ManAddCardinality_P_bdd(p, node->combi, i0);
                        printf("Already tried p_%d -> skipped\n", i0 + 1);
                        arr_xp[i0] = *(node->combi + i0);
                        xp = i0 + 1;
                    }                      
                }
                while (xp >= 0)
                {
                    printf("#CEGAR Constraining Sum(p_%d) == %d\n", xp + 1, *(node->combi + xp));
                    Exa_ManAddCardinality_P_bdd(p, node->combi, xp);
                    arr_xp[xp] = *(node->combi + xp);
                    status = sat_solver_solve(p->pSat, NULL, NULL, 0, 0, 0, 0);
                    printf("solution: %d \n", status);
                    if (status == 1)
                    {
                        add_satfy_values(list, node->r, arr_xp);
                        xp = Exa_ManEvalPVariables_bdd(p, node->combi,arr_xp);
                        if (xp == -1)
                        {
                            free(node->satfy);
                            free(node->combi);
                            free(node);
                            Exa_ManPrintSolution_bdd(p, fCompl);
                            Exa_ManFree(p);
                            Abc_PrintTime(1, "Total runtime", Abc_Clock() - clkTotal);
                            break;
                        }
                    }
                    else
                    {
                        xp = -1;
                        printf("removing combis with no solution\n");
                        remove_combis(list, node->r, arr_xp);
                        // print_combi_list(list);
                    }
                }                
                free(node->satfy);
                free(node->combi);
                free(node);
                ////////////////////////////////////////////////////
                continue;
            }
        }
        act++;
        if (act > 2000)
            break;
    }
    free_comb_list(list);
    // print_combi_list(list);
}
////////////////////////////////////////////////BBD For Encoding weighted Sum

void Exa_ManExactPowerSynthesis_sw(Bmc_EsPar_t *pPars)
{
    int i, status, iMint = 1;
    abctime clkTotal = Abc_Clock();
    Exa_Man_t *p;
    int fCompl = 0;
    word pTruth[16];
    Abc_TtReadHex(pTruth, pPars->pTtStr);
    assert(pPars->nVars <= 10);
    p = Exa_ManAlloc(pPars, pTruth);
    if (pTruth[0] & 1)
    {
        fCompl = 1;
        Abc_TtNot(pTruth, p->nWords);
    }
    comb_list *list = (comb_list *)malloc(sizeof(comb_list));
    list->len = pow(2, p->nVars - 1);
    list->length = 0;
    int r = 0;
    int act = 0;
    while (1)
    {
        //printf("ACT=%d\n",act);
        if (act >= calc_max_act(r + 1, p->nVars))
        {           
            r++;
            //////////////////////////Check if there is a general solution for r
            Exa_ManFree(p);
            pPars->nNodes = r + 1;
            p = Exa_ManAlloc(pPars, pTruth);
            status = Exa_ManAddCnfStart(p, pPars->fOnlyAnd);
            assert(status);
            for (iMint = 1; iMint < pow(2, p->nVars); iMint++)
            {
                if (!Exa_ManAddCnf(p, iMint))
                {
                    printf("The problem has no solution.\n");
                    break;
                }
            }
            status = sat_solver_solve(p->pSat, NULL, NULL, 0, 0, 0, 0);
            //////////////////////////
            if (status == 1)
            {
                calculate_comb_array(p->nVars, r, list);
                printf("######ACT:%d -> R= %d ADDED\n", act, r + 1);
            }
            else
                printf("######ACT:%d No general Solution for r=%d\n", act, r + 1);        
        }
        if (list->length > 0)
        {            
            if (list->start->act == act)
            {
                comb *node = pop_comb(list);                
                printf("###ACT:%d,r:%d CONSUMED COMBINATION:", (node->act), node->r + 1);
                for (int im = 0; im < list->len; im++)
                {
                    printf("%d,", *(node->combi + im));
                }
                printf("\n");                
                ////////////////////////////////////////////////////programm sat solver                
                Exa_ManFree(p);
                pPars->nNodes = node->r + 1;
                p = Exa_ManAlloc(pPars, pTruth);
                status = Exa_ManAddCnfStart(p, pPars->fOnlyAnd);
                printf("#Calculating BDD");
                bdd* BDD=calculate_bdd(p,act,node->r);                
                //print_bdd(BDD->start);
                printf("BDD nodes: %d\n",get_len_bdd(BDD->start));
                optimize_bdd(BDD);
                optimize_bdd2(BDD,p->nVars);               
                optimize_bdd(BDD);
                printf("BDD_optimized nodes: %d\n",get_len_bdd(BDD->start));
                //optimize_bdd(BDD);
                //print_bdd(BDD->start);
                //break;
                //print_bdd(BDD->start);

                while(list->start->act==act && list->start->r+1==p->nNodes){
                    comb* node1;
                    node1=pop_comb(list);   
                    free(node1->combi);
                    free(node1);                                     
                    printf("#Skipping ACT:%d,r:%d CONSUMED COMBINATION:",(node->act),node->r+1);
                    for (int im = 0; im < list->len; im++)
                    {
                        printf("%d,",*(node->combi+im));
                    }
                    printf("\n");
                }

                printf("#Added Base Constraints -> %d Clauses\n",sat_solver_nclauses(p->pSat));
                assert(status);                
                for (iMint = 1; iMint < pow(2, p->nVars); iMint++)
                {
                    abctime clk = Abc_Clock();
                    if (!Exa_ManAddCnf(p, iMint))
                    {
                        printf("The problem has no solution.\n");
                        break;
                    }
                }
                printf("#Added Minterm Constraints -> %d Clauses\n",sat_solver_nclauses(p->pSat));
                Exa_ManAddPClauses_bdd(p);
                printf("#Added P Constraints -> %d Clauses\n",sat_solver_nclauses(p->pSat));
                
                Exa_ManAddCardinality_P_sw(p,node->combi,BDD);
                
                printf("#Added P Card. Constraints -> %d Clauses\n",sat_solver_nclauses(p->pSat));
                status = sat_solver_solve(p->pSat, NULL, NULL, 0, 0, 0, 0);
                printf("###Solution: %d \n", status);
                if (status == 1)
                {           
                    print_bdd(BDD->start); 
                    delete_bdd(BDD->start);  
                    free(BDD);      
                    free(node->combi);
                    free(node);
                    Exa_ManPrintSolution_bdd(p, fCompl);
                    Exa_ManFree(p);
                    Abc_PrintTime(1, "Total runtime", Abc_Clock() - clkTotal);
                    break;
                }    
            delete_bdd(BDD->start);  
            free(BDD);      
            free(node->combi);
            free(node);
            continue;
            }
            ////////////////////////////////////////////////////
        }        
        act++;

        if (act > 2000)
            break;
    }    
    free_comb_list(list);
}



/*
void Exa_ManExactPowerSynthesis_sw(Bmc_EsPar_t *pPars)
{
    int i, status, iMint = 1;
    abctime clkTotal = Abc_Clock();
    Exa_Man_t *p;
    int fCompl = 0;
    word pTruth[16];
    Abc_TtReadHex(pTruth, pPars->pTtStr);
    assert(pPars->nVars <= 10);
    pPars->nNodes=6;
    p = Exa_ManAlloc(pPars, pTruth);    
    bdd* BDD=calculate_bdd(p,406,5);
}*/



