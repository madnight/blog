---
title: Disk Latency
date: 2021-03-08
tags: ["storage", "performance", "benchmark"]
subtitle: Measuring Disk Latency with ioping
---

There are different kind of performance indicators for disks. The most commonly known performance indicator for storage is probably throughput. If you have ever used a USB stick you will immediately notice if it's USB 2.0 or 3.x in case of a gigabyte sized data transfer. Another common performance indicator for storage is IOPS. IOPS are the number of IO operations that the disk can handle per second. For example a typical 7200U SATA HDD has about 75 IOPS, while a Samsung SSD 850 PRO has about 100k IOPS[^1]. Therefore you have probably noticed the performance boost when replacing your HDD with and SSD for your OS.


IOPS as the number of transactions that an array can pass through an aggregate of all its ports in a given second. While latency is the amount of time it takes to process the transaction within the system.


ioping is very much like pinging a IP. And if you were to mount a remote host over ssh with sshfs and pig the mount, then you will see that the ioping to disk will be the same as the ping to remote host ip, except for some additional microseconds of 



```
ping IP 
sshf ping
ping
```

Pinging HDSS is much slower than SSDs, In fact a HDD ping might be as aslow as a netowrk ping to a remote host. A lost IO lantecy is importatnt for many devices because often times IO operations happens to be sequetnital. This is similar to the multi core CPU architectö. A program that runs single threaded can only utilize one core at a time and ahavin many corew won't speed up the application.



## References
[^1]: [Samsung SSD 850 PRO Specifications](https://www.samsung.com/semiconductor/minisite/ssd/product/consumer/850pro/)

