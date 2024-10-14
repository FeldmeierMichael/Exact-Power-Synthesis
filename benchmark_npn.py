import itertools
from collections import Counter
from progress.bar import Bar

def input_inversions(f_arr,f_lookup,k):
    bar1=Bar('i_INV_Loop',max='16')
    bar2=Bar('i_INV_Loop_inner_f',max=2**(2**k))
    
    ######################
    inv_l=[]
    for f in range((2**k)):
        str_app="{:0"+str(k)+"b}"
        inv_l.append(str_app.format(f))  
    ######################
    for inv in inv_l:
        #print("I_INV:"+str(inv))
        f_in_arr=[]
        for fin,f in enumerate(f_arr):        
            #if(fin != f_lookup[fin]):
            #    continue
            f_in=list(f)  
            for i,l in enumerate(f):
                bin=str_app.format(i)
                new_bin=list(bin)
                for ki,b in enumerate(bin):
                    if(inv[ki]=='1'):
                        if(b=='0'):
                            new_bin[ki]='1'
                        else:
                            new_bin[ki]='0'                        
                    else:
                        new_bin[ki]=b
                new_bin=''.join(new_bin)
                new_index=int(new_bin,2)
                f_in[new_index]=l
            f_in=''.join(f_in)
            #print("I_INV:"+str(f_in))
            f_in_arr.append(f_in)
            for infl,fl in enumerate(f_arr):
                if(fl==f_in):
                    for luin,lu in enumerate(f_lookup):
                        if(lu==infl):
                            f_lookup[luin]=f_lookup[fin]
                    #f_lookup[infl]=f_lookup[fin]
            bar2.next()
        permutations(f_in_arr,f_lookup,k)
        bar1.next()

################################
def output_inversion(f_arr,f_lookup):
    for fin,f in enumerate(f_arr): 
        #if(fin != f_lookup[fin]):
        #    continue   
        
        f_n=''.join(['1' if l=='0' else '0'  for l in f])
        #print("O_INV:"+str(f_n))
        for infl,fl in enumerate(f_arr):
            if(fl==f_n):
                #print("match")
                for luin,lu in enumerate(f_lookup):
                        if(lu==infl):
                            f_lookup[luin]=f_lookup[fin]   
        




def permutations(f_arr,f_lookup,k):
    
    
    perm=[]
    for i in range(k):
        perm.append(i+1)    
    perm_l=(list(itertools.permutations(perm)))

    bar3=Bar('Perm_Loop',max=len(perm_l))
    bar4=Bar('Perm_Loop_inner_f',max=2**(2**k))
   
    #filtering permutations  
      
    for p in perm_l:
        #print("PERM:"+str(p))
        f_p_arr=[]
        for fin,f in enumerate(f_arr):   
            #if(fin != f_lookup[fin]):
            #    continue           
            f_p=list(f)  
            for i,l in enumerate(f):
                str_app="{:0"+str(k)+"b}"
                bin=str_app.format(i)
                new_bin=list(bin)
                for ki,b in zip(p,bin):
                    new_bin[ki-1]=b
                new_bin=''.join(new_bin)
                new_index=int(new_bin,2)
                f_p[new_index]=l
            f_p=''.join(f_p)
            #print("PERM:"+str(f_p))
            f_p_arr.append(f_p)            
            for infl,fl in enumerate(f_arr):
                if(fl==f_p):
                    #print("match")
                     for luin,lu in enumerate(f_lookup):
                        if(lu==infl):
                            f_lookup[luin]=f_lookup[fin]
                        
                    #f_lookup[infl]=f_lookup[fin] 
                bar4.next()
        output_inversion(f_p_arr,f_lookup)
        bar3.next()
            

k=4
f_arr=[]
npn=[]
f_loup=[]

for f in range(2**(2**k)):
    str_app="{:0"+str(2**k)+"b}"
    f_arr.append(str_app.format(f))
    f_loup.append(f)
#print(f_loup)
input_inversions(f_arr,f_loup,k)
print(f_loup)
n=Counter(f_loup).keys()
#print("NPN-Klassen:"+str(len(n)))
file =open("npn.txt",'w')
for a in f_loup:
    file.write(a+'\n')
file.close()



