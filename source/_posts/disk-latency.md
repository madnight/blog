---
title: Disk Latency
date: 2021-03-08
tags: ["storage", "performance", "benchmark"]
subtitle: Measuring Disk Latency with ioping
---

There are different kind of performance indicators for disks. The most commonly known is probably throughput. When you use a USB stick you will immediately notice if it's USB 2.0 or 3.x in case of a GiB sized data transfer. Another important performance indicator for storage is IOPS. IOPS is the number of I/O operations that the disk can handle per second. For example, a typical 7200U SATA HDD has about 75 IOPS, while a Samsung SSD 850 PRO has about 100k IOPS[^1]. You've probably noticed a significant performance boost after replacing your HDD with a SSD for your operating system.

To reach the maximum IOPS and throughput limits, the applications have to issue I/O requests with enough parallelism. If they don't, well then disk latency becomes the bottleneck. Disk latency is the amount of time it takes to process a I/O transaction. It can be measured with a tool called ioping, which works very much like the ping tool for hosts.

# Install

ioping is available for common Linux distributions and BSD.
```bash
# Ubuntu/Debian
apt-get install ioping

# Arch
pacman -S ioping

# Fedora
dnf install ioping

# MacOS
brew install ioping

# FreeBSD
pkg install ioping
```

If you are running on Windows you can download [ioping-1.2-win32.zip](https://github.com/koct9i/ioping/releases/download/v1.2/ioping-1.2-win32.zip) then unzip and run the ioping executable. In case your OS is not listed you can try to build ioping from source see: https://github.com/koct9i/ioping

# Usage

If you know how ping works, then you already know how to use ioping, just write the command and give it a directory path as argument. Here you can see an example run for the current directory:

```perl
ioping .
4 KiB <<< . (ext4 /dev/dm-0 107.8 GiB): request=1 time=282.6 us (warmup)
4 KiB <<< . (ext4 /dev/dm-0 107.8 GiB): request=2 time=855.6 us
4 KiB <<< . (ext4 /dev/dm-0 107.8 GiB): request=3 time=871.1 us
4 KiB <<< . (ext4 /dev/dm-0 107.8 GiB): request=4 time=748.5 us
4 KiB <<< . (ext4 /dev/dm-0 107.8 GiB): request=5 time=755.4 us
4 KiB <<< . (ext4 /dev/dm-0 107.8 GiB): request=6 time=747.8 us
^C
--- . (ext4 /dev/dm-0 107.8 GiB) ioping statistics ---
5 requests completed in 3.98 ms, 20 KiB read, 1.26 k iops, 4.91 MiB/s
generated 6 requests in 5.20 s, 24 KiB, 1 iops, 4.62 KiB/s
min/avg/max/mdev = 747.8 us / 795.7 us / 871.1 us / 55.5 us
```

As we can see the average response time for my SSD is about 800 us (0.8 ms), which results in 1260 sequential IOPS. Even though the SSD could achieve something like 100k IOPS in parallel, it can do only a little more than 1k IOPS on sequential request.

# Results

It's also possible to ping RAM in case it's mounted on `/tmp`, which is the default case under many linux distributions. If you want to ping the memory 10 times run `ioping -c 10 /tmp`. I did that for RAM and some other devices and collected the results in the following table:


{% raw %}<div style="overflow-x:auto;"><center>{% endraw %}
| Device        | Latency | IOPS          | Note  |
| ------------- |:-------------:|:---:| :-----:|
| RAM   | 22 us | 48000 | DDR3 1600MHz (PC3L 12800S) |
| SSD   | 796 us | 1240 | TOSHIBA THNSNJ12 |
| iSCSI | 1.5 ms | 649 | Hetzner Cloud Storage (Ceph block device) |
| HDD   | 14 ms | 73 | HGST HTS725050A7 |
| SSHFS     | 26 ms | 40 | Hetzner VPS (20 ms network ping) |
{% raw %}</div>{% endraw %}

As we can see a fast SSD over network mount can easily beat a local HDD. The I/O latency for Hetzner Cloud Storage is about 1.5 ms. This tells us that their SSD based Ceph cluster must be in the same data center as the VPS, that makes sense. A mount over ssh with sshfs reveals that sshfs itself adds about 6 ms of latency on top of the network latency. Although the drive itself is a SSD, the network latency turns it into a very slow filesystem mount with about half the performance of a local HDD. It is possible to calculate sequential IOPS, since it follows from the latency with IOPS = 1/$t$, whereas $t$ is latency in seconds.

We can conclude that I/O latency plays an important role for many applications, because I/O operations often happen to be sequential. This is similar to the importance of single-thread performance in a multi-core CPU architecture. While it is good to have many cores available, the single-thread performance of each core is still very relevant for the overall CPU speed in practice. The reason for that is that many applications runs single-threaded, like all coreutils except for sort[^2], and can only utilize one core at a time.

## References
[^1]: [Samsung SSD 850 PRO Specifications](https://www.samsung.com/semiconductor/minisite/ssd/product/consumer/850pro/)
[^2]: [Decoded: GNU coreutils](http://maizure.org/projects/decoded-gnu-coreutils/)

