---
title: Arch Linux Versioned
date: 2021-06-21
tags: ["arch", "linux", "upgrades"]
subtitle: Arch Linux Date-Based Versioned Upgrades
---

Have you ever been in the situation that you just wanted to install a single new package, but pacman couldn't find it, because your local package database is outdated? If so then you usually have two options. Perform a full system upgrade with `pacman -Syu`[^1] and a potential reboot in case of a new kernel or do a partial upgrade. Upgrade your local package database and only install the package plus all it's dependencies in the newest version. The problem is that partial upgrades are unsupported[^2]. Therefore, sooner than later, you might end up with a broken installation (missing .so files, wrong glibc version, kernel does not boot...). This might not be a big deal for a seasoned Archer. All you have to do is to arch-chroot from a live USB stick (some might have a Arch Linux Live USB stick always plugged in just in case) and fix the system. But this is at least time consuming and maybe a bit annoying. However, there's a third, lesser known option.

# Arch Linux Archive

The Arch Linux Archive (ALA), stores official repositories snapshots, iso images and bootstrap tarballs across time. It keeps packages for a few years on a daily bases. The most common use case for ALA is a full system downgrade in case something went wrong. With the Arch Linux Archive you are **able to pin down all your packages to a specific point in time** by defining the ALA as your only mirror in the pacman mirrorlist. This allows you to install any package from core, extra or community even if you are let's say 2 month behind the current Arch Linux upstream.

# Setup

Replace your `/etc/pacman.d/mirrorlist` with the following content:[^3]

```bash
##
## Arch Linux repository mirrorlist
## Generated on 2042-01-01
##
Server=https://archive.archlinux.org/repos/2042/01/01/$repo/os/$arch
```

And replace the date `2042/01/01` with the current date or any date you wish (>=2014). Now you are always able to install any package without upgrading. But, upgrading you should. Since `pacman -Syu` will not offer any new updates you have to update your mirror first. You could either manually edit the mirrorlist bump the date and `pacman -Syu` again or you can put the following bash function in you `.bashrc` or `.zshrc` which will do that for you automatically:

```sh
upgrade() {
    YESTERDAY=$(date -d "yesterday" +'%Y/%m/%d')
    MIRROR="https://archive.archlinux.org/repos"

    echo "Server = $MIRROR/$YESTERDAY/\$repo/os/\$arch" \
       | sudo tee /etc/pacman.d/mirrorlist
    sudo pacman -Syu
}
```


## References
[^1]: [Pacman Upgrading Packages](https://wiki.archlinux.org/title/Pacman#Upgrading_packages)
[^2]: [Arch Linux System Maintenance](https://wiki.archlinux.org/title/System_maintenance#Upgrading_the_system)
[^3]: [Arch Linux Archive](https://wiki.archlinux.org/title/Arch_Linux_Archive#How_to_restore_all_packages_to_a_specific_date)
