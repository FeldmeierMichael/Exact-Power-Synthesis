import os
import re
import time
import subprocess, datetime, signal

import matplotlib.pyplot as plt
import numpy 


p_command_base="timeout 86400 ./abc -c 'powertwoexact -N 3 -I 4 -F 14 01AC"
command_base="./abc -c 'twoexact -N 3 -I 4 "

res=[]
p_res=[]

#result=os.popen(command).read()
results= [line.strip() for line in open("ben_0016.txt", 'r')]
ben1_t=[]
ben_1_act=[]
ben2_t=[]
ben_2_act=[]
ben3_t=[]
ben_3_act=[]
ben4_t=[]
ben_4_act=[]
l=0
for line in results:
    if("#2" in line):
        break
    res=re.search('ACT=([0-9]+)',line)
    if(res!= None):
        #print(res[1])
        value=int(res[0][4:])
        ben_1_act.append(value) 
        res=re.search('([+-]?([0-9]*[.])?[0-9]+) sec',line)
        if(res!= None):
            value=float(res[0][:-4])
            ben1_t.append(value)
    l=l+1

for line in results[l:]:
    if("#3" in line):
        break
    res=re.search('ACT=([0-9]+)',line)
    if(res!= None):
        #print(res[1])
        value=int(res[0][4:])
        ben_2_act.append(value) 
        res=re.search('([+-]?([0-9]*[.])?[0-9]+) sec',line)
        if(res!= None):
            value=float(res[0][:-4])
            ben2_t.append(value)
    l=l+1

for line in results[l:]:
    if("#4" in line):
        break
    res=re.search('ACT=([0-9]+)',line)
    if(res!= None):
        #print(res[1])
        value=int(res[0][4:])
        ben_3_act.append(value) 
        res=re.search('([+-]?([0-9]*[.])?[0-9]+) sec',line)
        if(res!= None):
            value=float(res[0][:-4])
            ben3_t.append(value)
    l=l+1


for line in results[l:]:
   
    res=re.search('ACT=([0-9]+)',line)
    if(res!= None):
        #print(res[1])
        value=int(res[0][4:])
        ben_4_act.append(value) 
        res=re.search('([+-]?([0-9]*[.])?[0-9]+) sec',line)
        if(res!= None):
            value=float(res[0][:-4])
            ben4_t.append(value)
    l=l+1




plt.title("title")
plt.xlabel("secounds")
plt.ylabel("ACT")
fig = plt.figure()
ax = fig.gca()
ax.set_xticks(numpy.arange(0, max(ben2_t), 25))
ax.set_yticks(numpy.arange(0, 500, 50))
plt.plot(ben1_t, ben_1_act, linestyle="-", marker="o", markersize=4,color='yellow')
plt.plot(ben2_t, ben_2_act,linestyle="-", marker="o",markersize=4,color='blue')
plt.plot(ben3_t, ben_3_act,linestyle="-", marker="o",markersize=4,color='black')
plt.plot(ben4_t, ben_4_act,linestyle="-", marker="o",markersize=4,color='green')
plt.grid()
plt.savefig('comare.png')



#os.system('echo "[INFO] Running Benchmark for k=4\n" > '+file_name)

"""
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
        
        
"""

       
   
        


        

   
    


