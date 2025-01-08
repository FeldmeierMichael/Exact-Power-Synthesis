import os
import re
import time
import subprocess, datetime, signal


file_name='benchmark_opt_500_10.md'




def print_mermaid(x,p_val,val,p_r,r):
    p_avg=sum(p_val)/len(p_val)
    avg=sum(val)/len(val)
    p_avg_arr=[p_avg for i in x]
    avg_arr=[avg for i in x]
    os.system('echo "\`\`\`mermaid\" >> '+file_name)
    os.system('echo "xychart-beta" >> '+file_name)    
    #print('echo "    title '+'\"Comparison powertwoexact twoexact\"'+'">> '+file_name)
    os.system('echo "    title '+'\\"Comparison powertwoexact twoexact\\"'+'">> '+file_name)
    os.system('echo "    x-axis '+''.join(str(x))+'" >> '+file_name)
    os.system('echo "    y-axis '+'\\"Switching Activity\\"'+' 0-->'+str(max(max(p_val),max(val)))+'">> '+file_name)
    os.system('echo "    line '+''.join(str(p_val))+'" >> '+file_name)
    os.system('echo "    line '+''.join(str(val))+'" >> '+file_name)
    os.system('echo "    line '+''.join(str(p_avg_arr))+'" >> '+file_name)
    os.system('echo "    line '+''.join(str(avg_arr))+'" >> '+file_name)
    os.system('echo "    bar '+''.join(str([r*20 for r in p_r]))+'" >> '+file_name)
    os.system('echo "    bar '+''.join(str([i*20 for i in r]))+'" >> '+file_name)
    os.system('echo "\`\`\`\n" >> '+file_name)
    

p_command_base="timeout 86400 ./abc -c 'powertwoexact -N 3 -I 4 -F 7 "
command_base="./abc -c 'twoexact -N 3 -I 4 "

res=[]
p_res=[]

#os.system('echo "[INFO] Running Benchmark for k=4\n" > '+file_name)


file=open("npn.txt",'r')
npn_l=file.read().splitlines()

k=4
f_arr=[]
for f in range(2**(2**k)):
    str_app="{:0"+str(2**k)+"b}"
    f_arr.append(str_app.format(f))

f_npn_i=[]
for i in npn_l:
    if(int(i) not in f_npn_i):
        f_npn_i.append(int(i))

f_npn=[]
for i in f_npn_i:
    f_npn.append(f_arr[i])


#print(f_npn)
#n_classes=len(f_npn)
ts=time.time()
#os.system('echo "[INFO] Number of NPN Classes:'+str(len(f_npn))+'\n\n" >> '+file_name)
#os.system('echo "test\n" >> '+file_name)
#os.system('echo "test\n" >> '+file_name)
#os.system('echo "test\n" >> '+file_name)
#os.system('echo "test\n" >> '+file_name)
#os.system('echo "test\n" >> '+file_name)
#os.system('echo "test\n" >> '+file_name)
#os.system('\n" >> '+file_name)

p_r_arr=[]
p_s_arr=[]
r_arr=[]
s_arr=[]
x=[]
upd=0

for c_i,f in enumerate(f_npn[189:]):
    f_int=int(f,2)
   
    number="0x%0.4X" %f_int
    print("Synthesising:"+number)
    p_command=p_command_base+number[2:]+"'"
    print(p_command)
    command=command_base+number[2:]+"'"
    
    result=os.popen(command).read()

    #os.system("sed -i '' -e '$ d' "+ file_name)
    
    #os.system("sed -i '' -e '$ d' "+ file_name)
    #os.system("sed -i '' -e '$ d' "+ file_name)
    #os.system("sed -i '' -e '$ d' "+ file_name)
    #os.system("sed -i '' -e '$ d' "+ file_name)
    #
    #os.system("sed -i '' -e '$ d' "+ file_name)
    #os.system("sed -i '' -e '$ d' "+ file_name)
    #os.system("sed -i '' -e '$ d' "+ file_name)
    #os.system("sed -i '' -e '$ d' "+ file_name)
    #os.system("sed -i '' -e '$ d' "+ file_name)
    #os.system("sed -i '' -e '$ d' "+ file_name)
    #os.system("sed -i '' -e '$ d' "+ file_name)
    #os.system("sed -i '' -e '$ d' "+ file_name)

    
    #os.system("mv temp.txt benchmark.md")
    #os.system("head -n -1 benchmark.md > temp.txt")
    #os.system("mv temp.txt benchmark.md")
    
    res=re.search('Switching Activity=([0-9]+)',result) 
    res_g=re.search('Number of Gates: r=([0-9]+)',result) 

    if(int(res[1])>=500): 

        p_result=os.popen(p_command).read()
      
        p_res=re.search('Switching Activity=([0-9]+)',p_result)

        skip=0
        if(p_res is None):
            print("Skipped time exceded 24h")
            skip=1
            os.system('echo \"'+'[INFO] (Skipped > 24h) Synthesising NPN Class='+str(c_i)+' TruthTable:'+number+' exact:'+str(res[1])+' r='+str(res_g[1])+'\n" >> '+file_name)
           

        if(skip==0):
            p_res_g=re.search('Number of Gates: r=([0-9]+)',p_result)
            
            timest=round((time.time()-ts)/60,2)

            print('Synthesising NPN Class='+str(c_i)+' TruthTable:' +number+' pexact:'+str(p_res[1])+' exact:'+str(res[1]))
            os.system('echo \"'+'[INFO] Synthesising NPN Class='+str(c_i)+' TruthTable:'+number+' pexact:'+str(p_res[1])+' r='+str(p_res_g[1])+' exact:'+str(res[1])+' r='+str(res_g[1])+' time='+str(timest)+'min \n" >> '+file_name)
            
            p_r_arr.append(int(p_res_g[1]))
            p_s_arr.append(int(p_res[1]))
            r_arr.append(int(res_g[1]))
            s_arr.append(int(res[1]))
            x.append(f_int)
            avg_ps=sum(p_s_arr)/len(p_s_arr)
            avg_pr=sum(p_r_arr)/len(p_r_arr)
            avg_s=sum(s_arr)/len(s_arr)
            avg_r=sum(r_arr)/len(r_arr)


        #print_mermaid(x,p_s_arr,s_arr,p_r_arr,r_arr)
        #os.system('echo " avg_p_s='+str(round(avg_ps,2))+' avg_s='+str(round(avg_s,2))+' avg_pr='+str(round(avg_pr,2))+' avg_r='+str(round(avg_r,2))+'\n" >> '+file_name)
        
        


        os.system('git add '+file_name)    
        os.system('git commit -m \"'+number+"\"")
        os.system('git push')
        
    """else:
        #p_result=os.popen(p_command).read()
        p_res=res
    

        p_res_g=res_g
        
        timest=round((time.time()-ts)/60,2)

        print('Synthesising NPN Class='+str(c_i)+' TruthTable:' +number+' pexact:'+str(p_res[1])+' exact:'+str(res[1]))
        os.system('echo \"'+'[INFO] (Skipped>500)  Synthesising NPN Class='+str(c_i)+' TruthTable:'+number+' pexact:'+str(p_res[1])+' r='+str(p_res_g[1])+' exact:'+str(res[1])+' r='+str(res_g[1])+' time='+str(timest)+'min \n" >> '+file_name)
        
        p_r_arr.append(int(p_res_g[1]))
        p_s_arr.append(int(p_res[1]))
        r_arr.append(int(res_g[1]))
        s_arr.append(int(res[1]))
        x.append(f_int)
    
    
        avg_ps=sum(p_s_arr)/len(p_s_arr)
        avg_pr=sum(p_r_arr)/len(p_r_arr)
        avg_s=sum(s_arr)/len(s_arr)
        avg_r=sum(r_arr)/len(r_arr)


        print_mermaid(x,p_s_arr,s_arr,p_r_arr,r_arr)
        #os.system('echo " avg_p_s='+str(round(avg_ps,2))+' avg_s='+str(round(avg_s,2))+' avg_pr='+str(round(avg_pr,2))+' avg_r='+str(round(avg_r,2))+'\n" >> '+file_name)
    """    
        


        

   
    


