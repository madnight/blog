---
title: Arch Linux Versioned
date: 2021-06-21
tags: ["arch", "linux", "updates"]
subtitle: Arch Linux Date Based Versioned Updates
---

Have you ever been in the situation that you just wanted to install a single new package, but pacman couldn't find it, because your local package database is outdated? If so then you usually have two options. Perform a full system upgrade with `pacman -Syu` and a potential reboot in case of a new kernel or do a partial upgrade. Upgrade your local package database and only install the package plus all it's dependencies in the newest version. Problem is that partial upgrades are unsupported[^1]. Therefore, sooner than later, you might end up with a broken installation (missing .so files, wrong glibc version, kernel does not boot...). This might not be a big deal for a seasoned Archer. All you have to do is to arch-chroot from a live USB (some might have a Arch Linux Live USB stick always plugged in just in case) and fix the system. But this is at least time consuming and maybe a bit annoying. However, there's a third, lesser known option.

# Arch Linux Archive

The Arch Linux Archive (ALA), stores official repositories snapshots, iso images and bootstrap tarballs across time. It keeps packages for a few years on a daily bases. The most common use case for ALA is a full system downgrade in case something went wrong.


 Use Arch Linux Archive as your mirror.

With the Arch Linux Archive (ALA) you are able to pin down all your packages to specific point in time. This allows you to install any package from core, extra or community even if you are let's say 2 month behind the current Arch Linux upstream.

# Setup

This allows you to do versioned up and downgrades like you could do with a docker image by changing the tag, by replacing your `/etc/pacman.d/mirrorlist` with the following content:[^2]

```bash
##
## Arch Linux repository mirrorlist
## Generated on 2042-01-01
##
Server=https://archive.archlinux.org/repos/2021/03/30/$repo/os/$arch
```


## References
[^1]: [Arch Linux System Maintenance](https://wiki.archlinux.org/title/System_maintenance#Upgrading_the_system)
[^2]: [Arch Linux Archive](https://wiki.archlinux.org/title/Arch_Linux_Archive#How_to_restore_all_packages_to_a_specific_date)

