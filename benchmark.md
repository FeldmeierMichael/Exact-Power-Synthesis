[INFO] Running Benchmark for k=4


[INFO] Number of NPN Classes:222
[INFO] Synthesising NPN Class=0 TruthTable:0x0000 pexact:96 r=4 exact:192 r=4time=0.030665067831675212min 

[INFO] Synthesising NPN Class=1 TruthTable:0x0001 pexact:152 r=3 exact:152 r=3time=0.08003389835357666min 

[INFO] Synthesising NPN Class=2 TruthTable:0x0003 pexact:182 r=4 exact:312 r=4time=0.16355549891789753min 

```mermaid
xychart-beta
    title "Comparison powertwoexact twoexact"
    x-axis ['0000000000000000', '0000000000000001', '0000000000000011']
    y-axis "Switching Activity" 0-->312
    line [96, 152, 182]
    line [192, 152, 312]
    line [143.33333333333334, 143.33333333333334, 143.33333333333334]
    line [218.66666666666666, 218.66666666666666, 218.66666666666666]
    bar [80, 60, 80]
    bar [80, 60, 80]
```

