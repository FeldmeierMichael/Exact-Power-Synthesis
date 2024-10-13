[INFO] Running Benchmark for k=4


[INFO] Number of NPN Classes:222
[INFO] Synthesising NPN Class=0 TruthTable:0x0000 pexact:96 r=4 exact:192 r=4time=0.030665067831675212min 

[INFO] Synthesising NPN Class=1 TruthTable:0x0001 pexact:152 r=3 exact:152 r=3time=0.08003389835357666min 

[INFO] Synthesising NPN Class=2 TruthTable:0x0003 pexact:182 r=4 exact:312 r=4time=0.16355549891789753min 

[INFO] Synthesising NPN Class=3 TruthTable:0x0006 pexact:208 r=4 exact:224 r=3time=0.2905206720034281min 

[INFO] Synthesising NPN Class=4 TruthTable:0x0007 pexact:182 r=4 exact:192 r=3time=0.3716464638710022min 

[INFO] Synthesising NPN Class=5 TruthTable:0x000F pexact:182 r=4 exact:352 r=4time=0.4697942058245341min 

```mermaid
xychart-beta
    title "Comparison powertwoexact twoexact"
    x-axis ['0000000000000000', '0000000000000001', '0000000000000011', '0000000000000110', '0000000000000111', '0000000000001111']
    y-axis "Switching Activity" 0-->352
    line [96, 152, 182, 208, 182, 182]
    line [192, 152, 312, 224, 192, 352]
    line [167.0, 167.0, 167.0, 167.0, 167.0, 167.0]
    line [237.33333333333334, 237.33333333333334, 237.33333333333334, 237.33333333333334, 237.33333333333334, 237.33333333333334]
    bar [80, 60, 80, 80, 80, 80]
    bar [80, 60, 80, 60, 60, 80]
```

