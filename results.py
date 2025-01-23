import os
import re
import time
import subprocess, datetime, signal

import matplotlib.pyplot as plt
import numpy 

output_files='comp_alg_3_'
list=['0016','0116','0168','018A','019E','01BE','033F','036C','037D','03D4','03DD','066F','0697','0776','077A']

p_command_base="./abc -c 'powertwoexact -N 3 -I 4 -F 14 "
command_base="./abc -c 'twoexact -N 3 -I 4 "



for i,a in enumerate(list):
    command=p_command_base+a+'\'>'+output_files+a+'.txt'
    print(command)
    os.system(command)

"""
res_all=[]
for i,a in enumerate(list):
    file=output_files+a
    entry=[]
    results= [line.strip() for line in open("ben_012F.txt", 'r')]
    ben1_t=[]
    ben_1_act=[]
    ben2_t=[]
    ben_2_act=[]
    ben3_t=[]
    ben_3_act=[]
    ben4_t=[]
    ben_4_act=[]
    ben5_t=[]
    ben_5_act=[]
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

    entry=[(ben1_t,ben_1_act),(ben2_t,ben_2_act),(ben3_t,ben_3_act),(ben4_t,ben4_t),(ben5_t,ben_5_act)]
    res_all.append(entry)
    



break
#result=os.popen(command).read()



for line in results[l:]:
    if("#5" in line):
        break
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


for line in results[l:]:   
    res=re.search('ACT=([0-9]+)',line)
    if(res!= None):
        #print(res[1])
        value=int(res[0][4:])
        ben_5_act.append(value) 
        res=re.search('([+-]?([0-9]*[.])?[0-9]+) sec',line)
        if(res!= None):
            value=float(res[0][:-4])
            ben5_t.append(value)
    l=l+1

max_act=max(ben_1_act)
max_time=max(max(ben1_t),max(ben2_t),max(ben3_t))
ben_1_act=[act/max_act for act in ben_1_act]
ben_2_act=[act/max_act for act in ben_2_act]
ben_3_act=[act/max_act for act in ben_3_act]

ben1_t=[act/max_time for act in ben1_t]
ben2_t=[act/max_time for act in ben2_t]
ben3_t=[act/max_time for act in ben3_t]

cutoff_act=0.5

ben_1_act=[act for act in ben_1_act]
ben_2_act=[act for act in ben_2_act]
ben_3_act=[act for act in ben_3_act]

plt.title("title")
plt.xlabel("secounds")
plt.ylabel("ACT")
fig = plt.figure()
ax = fig.gca()

ax.set_xticks(numpy.arange(0, 1.1, 0.1))
ax.set_yticks(numpy.arange(0, 1.1, 0.1))
plt.ylim(0.7,1.1)
plt.plot(ben1_t, ben_1_act, linestyle="-", marker="o", markersize=2,color='red')
plt.plot(ben2_t, ben_2_act,linestyle="-", marker="o",markersize=2,color='blue')
plt.plot(ben3_t, ben_3_act,linestyle="-", marker="o",markersize=2,color='green')
#plt.plot(ben4_t, ben_4_act,linestyle="-", marker="o",markersize=4,color='green')
#plt.plot(ben5_t, ben_5_act,linestyle="-", marker="o",markersize=4,color='red')
plt.grid()
plt.savefig('comare.png')



"""