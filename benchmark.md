[INFO] Running Benchmark for k=4

[INFO] Number of NPN Classes:222

[INFO] Synthesising NPN Class=0 TruthTable:0x0000 pexact:96 r=4 exact:192 r=4time=0.031318271160125734min 

[INFO] Synthesising NPN Class=1 TruthTable:0x0001 pexact:152 r=3 exact:152 r=3time=0.07989815870920818min 

[INFO] Synthesising NPN Class=2 TruthTable:0x0003 pexact:182 r=4 exact:312 r=4time=0.1615140676498413min 

[INFO] Synthesising NPN Class=3 TruthTable:0x0006 pexact:208 r=4 exact:224 r=3time=0.2912542502085368min 

```mermaid
xychart-beta
    title "Comparison powertwoexact twoexact"
    x-axis ['0000000000000000', '0000000000000001', '0000000000000011', '0000000000000110']
    y-axis "Switching Activity" 0-->312
    line [96, 152, 182, 208]
    line [192, 152, 312, 224]
    line [159.5, 159.5, 159.5, 159.5]
    line [220.0, 220.0, 220.0, 220.0]
    bar [80, 60, 80, 80]
    bar [80, 60, 80, 60]
```

