



/////////////////////////////////////////////////BDD Summed weights my implementation

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
typedef struct bdd2_ bdd2;
struct bdd2_
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

print_bdd2(node* n){    
    
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
                    print_bdd2(n->n1);

            if(n->end0==0)
                if(n->n0->id>in)
                    print_bdd2(n->n0);
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

int get_len_bdd2(node* n){
    int i=0;
    int c=n->id;    
    if(n->end0<0 &&n->end1<0){
        return 1;
    }
    else if(n->end0==0 && n->end1==0){
        if(n->n1->id>c)
            i=get_len_bdd2(n->n1);
        if(n->n0->id>c)
            i=i+get_len_bdd2(n->n0);
        return i+1;
    }
    else if(n->end0==0){
        if(n->n0->id>c)
            return 1+get_len_bdd2(n->n0);
        
    }
    else if(n->end1==0){
         if(n->n1->id>c)
            return 1+get_len_bdd2(n->n1);
    }
    return 1;
}

bdd2* calculate_bdd2(Exa_Man_t * p,int act,int r){
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
    bdd2* BDD=(bdd2*) malloc(sizeof(bdd2));
    BDD->act=act;
    int i_act=act;
    BDD->start=new_node(0,0,i_arr[0],n_p_arr[0],act,0);
    node* i_ptr=BDD->start;
    calculate_node_opt(i_ptr,w_arr,i_arr,n_p,index,0,act,1,n_p_arr,r,BDD);
    //print_bdd(BDD->start);
    
    return BDD;
}
int calculate_node(node* n,int* w_arr,int* i_arr,int n_p,int len,int ptr_start,int act,int id,int* n_p_arr,int r,bdd2* BDD){
    
    int i_act=w_arr[ptr_start];
    int iid=id;
    //printf("###Calculate Node %d for act=%d i=%d i_act=%d\n",n->id,act,*(i_arr+ptr_start),i_act);
    ///////////1-node
    int bdd2_calc1=bdd2_calc_end(w_arr,len,ptr_start+1,act-i_act,r-1,n_p);
    //printf("##Node %d bdd_calc1=%d\n",n->id,bdd_calc1);
    if(bdd2_calc1==1){
        //printf("#1-Node:\n");
        
        
        node* n1=new_node(0,0,*(i_arr+ptr_start+1),*(n_p_arr+ptr_start+1),act-i_act,iid);
        iid++;
        iid=calculate_node(n1,w_arr,i_arr,n_p,len,ptr_start+1,act-i_act,iid,n_p_arr,r-1,BDD);
        n->n1=n1;  
                    
        }
    else if(bdd2_calc1==2)
        n->end1=-2;    
    else
        n->end1=-1;

    /////////////////0-node    
    int bdd2_calc0=bdd2_calc_end(w_arr,len,ptr_start+1,act,r,n_p);     
    //printf("##Node %d bdd_calc0=%d\n",n->id,bdd_calc0);
    if(bdd2_calc0==1){
        //printf("#0-Node:\n");                    
        
        node* n0=new_node(0,0,*(i_arr+ptr_start+1),*(n_p_arr+ptr_start+1),act,iid);
        iid++;
        iid=calculate_node(n0,w_arr,i_arr,n_p,len,ptr_start+1,act,iid,n_p_arr,r,BDD);
        n->n0=n0;
              
        //iid=calculate_node(n0,w_arr,i_arr,*(n_p_arr+ptr_start+1),len,ptr_start+1,act,iid,n_p_arr,r,hst);  
          
    }
    else if(bdd2_calc0==2)    
        n->end0=-2;
    else
        n->end0=-1;
       
    return iid;
}

int calculate_node_opt(node* n,int* w_arr,int* i_arr,int n_p,int len,int ptr_start,int act,int id,int* n_p_arr,int r,bdd2* BDD){
    
    int i_act=w_arr[ptr_start];
    int iid=id;
    //printf("###Calculate Node %d for act=%d i=%d i_act=%d\n",n->id,act,*(i_arr+ptr_start),i_act);
    ///////////1-node
    int bdd2_calc1=bdd2_calc_end(w_arr,len,ptr_start+1,act-i_act,r-1,n_p);
    //printf("##Node %d bdd_calc1=%d\n",n->id,bdd_calc1);
    if(bdd2_calc1==1){
        //printf("#1-Node:\n");
        if(!search_node(BDD->start,n,*(i_arr+ptr_start+1),*(n_p_arr+ptr_start+1),act-i_act,1)){
            node* n1=new_node(0,0,*(i_arr+ptr_start+1),*(n_p_arr+ptr_start+1),act-i_act,iid);
            iid++;
            iid=calculate_node_opt(n1,w_arr,i_arr,n_p,len,ptr_start+1,act-i_act,iid,n_p_arr,r-1,BDD);
            n->n1=n1;  
        }            
        }
    else if(bdd2_calc1==2)
        n->end1=-2;    
    else
        n->end1=-1;

    /////////////////0-node    
    int bdd2_calc0=bdd2_calc_end(w_arr,len,ptr_start+1,act,r,n_p);     
    //printf("##Node %d bdd_calc0=%d\n",n->id,bdd_calc0);
    if(bdd2_calc0==1){
        //printf("#0-Node:\n");                    
        if(!search_node(BDD->start,n,*(i_arr+ptr_start+1),*(n_p_arr+ptr_start+1),act,0)){
            node* n0=new_node(0,0,*(i_arr+ptr_start+1),*(n_p_arr+ptr_start+1),act,iid);
            iid++;
            iid=calculate_node_opt(n0,w_arr,i_arr,n_p,len,ptr_start+1,act,iid,n_p_arr,r,BDD);
            n->n0=n0;
        }      
        //iid=calculate_node(n0,w_arr,i_arr,*(n_p_arr+ptr_start+1),len,ptr_start+1,act,iid,n_p_arr,r,hst);  
          
    }
    else if(bdd2_calc0==2)    
        n->end0=-2;
    else
        n->end0=-1;
       
    return iid;
}


int bdd2_calc_end(int* w_arr,int len,int ptr_start,int act,int r,int n_p){
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


delete_bdd2(node* n){
    if(n!=NULL){        
        int in=n->id;
        if(n->end0< 0 && n->end1 < 0){
            free(n);
        }
        else if(n->end0<0){
            if(n->n1->id>in)
                delete_bdd2(n->n1);
            free(n);
        }
        else if(n->end1<0){
            if(n->n0->id>in)
                delete_bdd2(n->n0);
            free(n);
        }
        else{
            if(n->n1->id>in)
                delete_bdd2(n->n1);
            if(n->n0->id>in)
                delete_bdd2(n->n0);
            free(n);
        }
    }


}

void optimize_bdd2(bdd2* BDD){
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

void optimize_bdd2_2(bdd2* BDD,int k){
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


void Exa_ManAddCardinality_P_sw(Exa_Man_t *p, int *combi, bdd2* BDD)
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