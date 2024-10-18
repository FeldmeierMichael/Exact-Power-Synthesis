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


void free_comb_list(comb_list* list){
    while(list->length>0){
       comb* node=pop_comb(list); 
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
            printf("p_%d_%d has value %d\n",p->nVars+i,j+1,sat_solver_var_value(p->pSat,p->i_p+n_p*i+j));
        }
    }

    for (int i = 0; i < n_p; i++)
    {
        printf("comparing xp=%d %d with %d\n",i+1,combi_sol[i],*(combi+i));
        if(*(combi+i)!=combi_sol[i])
            return i;        
    }
    return -1;   
}




void Exa_ManAddPClauses(Exa_Man_t * p){
    printf("adding P Clauses\n");
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


void Exa_ManAddCardinality_P(Exa_Man_t * p,int * combi,int xp,int grp){
    if(grp==1){
        if(p->o_l==0)
            p->i_o=p->iVar;
        p->o_l++;
        int o_n=p->iVar;
        p->iVar+=1;        
        sat_solver_setnvars(p->pSat, p->iVar); 

        int n_i=p->nNodes-1;
        int n_p = pow(2,p->nVars-1);
        //for(int pi=xp;pi<xp+1;pi++){
            int pi=xp;
            //printf("constrain for Sum:p_%d=%d\n",pi+1,*(combi+pi));
            int pLits[n_i+1];
            int lit=0;
            int l=*(combi+pi);        
            //less then l    
            int j=l+1;
            for (int i = 0; i < pow(2,n_i); i++)
            {
                int res[n_i];
                convert_base_int(2,i,n_i,res);
                int sum=0;
                for (int l = 0; l < n_i; l++)
                {
                    sum+=*(res+l);
                }
                if(sum==j){
                    lit=0;
                    pLits[0]=Abc_Var2Lit(o_n,1);
                    for (int l = 0; l < n_i; l++){
                            if(*(res+l)==1){
                                //printf("%d,",l+1);
                                pLits[lit+1]=Abc_Var2Lit(p->i_p+l*n_p+pi,1);
                                lit++;
                            }
                    }
                //printf("\n");
                sat_solver_addclause(p->pSat,pLits,pLits+lit+1);                
                }       
            }            
            lit=0;
            //more then l    
            j=n_i-l+1;
            for (int i = 0; i < pow(2,n_i); i++)
            {
                int res[n_i];
                convert_base_int(2,i,n_i,res);
                int sum=0;
                for (int l = 0; l < n_i; l++)
                {
                    sum+=*(res+l);
                }
                if(sum==j){
                    lit=0;
                    pLits[0]=Abc_Var2Lit(o_n,1);
                    for (int l = 0; l < n_i; l++){
                            if(*(res+l)==1){
                                pLits[lit+1]=Abc_Var2Lit(p->i_p+l*n_p+pi,0);
                                lit++;
                            }
                    }            
                sat_solver_addclause(p->pSat,pLits,pLits+lit+1);                    
                }       
        //}
    }
    }
    else{
        int n_i=p->nNodes-1;
        int n_p = pow(2,p->nVars-1);
        for(int pi=0;pi<n_p;pi++){
            //printf("constrain for Sum:p_%d=%d\n",pi+1,*(combi+pi));
            int pLits[n_i];
            int lit=0;
            int l=*(combi+pi);        
            //less then l    
            int j=l+1;
            for (int i = 0; i < pow(2,n_i); i++)
            {
                int res[n_i];
                convert_base_int(2,i,n_i,res);
                int sum=0;
                for (int l = 0; l < n_i; l++)
                {
                    sum+=*(res+l);
                }
                if(sum==j){
                    lit=0;
                    for (int l = 0; l < n_i; l++){
                            if(*(res+l)==1){
                                //printf("%d,",l+1);
                                pLits[lit++]=Abc_Var2Lit(p->i_p+l*n_p+pi,1);
                            }
                    }
                //printf("\n");
                sat_solver_addclause(p->pSat,pLits,pLits+lit);                
                }       
            }            
            lit=0;
            //more then l    
            j=n_i-l+1;
            for (int i = 0; i < pow(2,n_i); i++)
            {
                int res[n_i];
                convert_base_int(2,i,n_i,res);
                int sum=0;
                for (int l = 0; l < n_i; l++)
                {
                    sum+=*(res+l);
                }
                if(sum==j){
                    lit=0;
                    for (int l = 0; l < n_i; l++){
                            if(*(res+l)==1){
                                pLits[lit++]=Abc_Var2Lit(p->i_p+l*n_p+pi,0);
                            }
                    }            
                sat_solver_addclause(p->pSat,pLits,pLits+lit);                    
                }       
        }
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
        if ( pPars->fVerbose )
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
                            for (int xp = 0; xp >=0 ; xp++)
                            {
                                printf("#CEGAR Constraining Sum(p_%d) == %d\n",xp+1,*(node->combi+xp));
                                Exa_ManAddCardinality_P(p,node->combi,xp,0);
                            
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
                                else
                                    xp=-2;

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


 


