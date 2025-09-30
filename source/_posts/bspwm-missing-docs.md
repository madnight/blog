---
title: The Missing Docs of Bspwm
date: 2017-06-23
tags: ["bspwm", "wm", "linux", "ricing"]
subtitle: Bspwm as undocumented i3-gaps alternative
categories:
  - Computer Science
---

# Introduction
Although this post is about bspwm <ins>(b</ins>inary <ins>s</ins>pace <ins>p</ins>artitioning <ins>w</ins>indow <ins>m</ins>anager), lets start with [i3](https://i3wm.org/) and why I don't use it, beside its excellent documentation. i3 is a tiling window window manager, started at as fork of [wmii](https://wiki.archlinux.org/index.php/wmii), written by [Micheal Stapelberg](https://github.com/stapelberg). One popular feature of most tiling window managers, are visual gaps between application windows. The main problem of users who like gaps, is that i3 is lacking the gaps feature. Is this really a thing? Well just compare the [i3 repository](https://github.com/stapelberg/i3) with the [i3-gaps](https://github.com/Airblader/i3) fork. This fork only contains the missing gaps feature. Its hard to find a comparable fork on GitHub, that have such a major impact on the community, just by adding a tiny feature. Another indicator is the subreddit [/r/unixporn](https://www.reddit.com/r/unixporn/) with 64k subscribers. Many so called *nixers* and *ricers*, that are people who customize their Linux distribution, prefer the i3-gaps variant over stock i3. This leads to the simple question, why is the gaps feature not part of stock i3?

<img src="/images/gaps.jpg" onclick="window.open(this.src)">

The answer to that question is quiet simple. The creator and maintainer of i3 thinks that gaps are don't serve any purpose{% raw %}<sup>[citation needed]</sup>{% endraw %}. The reason why many people think otherwise vary, some people like the visual separation of their applications, others simply like the fancy look and some have a specific use case in mind. However, it seems that it is not possible to convince Michael to merge the i3-gaps fork maintained by [Airblader](https://github.com/Airblader/).

Now the final conclusion could be, use i3-gaps and be happy with a fork of the most popular and well documented tiling window manager. But i3-gaps has its own problems. First of all it is not official supported, there might be bugs, there might be a problem with the gaps, there might be a missing gaps feature. Bspwm allows for a very fine granulated control over the gaps. They can be set dynamically and each gap (north, east, south, west) can be controlled individually. This can be useful, for instance if you want to have a permanent visual conky on one side of your screen. Not so with i3-gaps, its not supported and Airblader currently has no time to implement it, fair enough. - Lets switch to the second most popular tiling window manager bspwm with native gaps support.

# The Missing Docs
[Bspwm](https://github.com/baskerville/bspwm) is a great alternative to i3-gaps, but unfortunately it lacks documentation. Not only that, the commands change over time, so that every guide and documentation will become outdated sooner or later. This leads to confusion about outdated bspwm configuration syntax, floating around all over the Internet and forcing to constantly update the own set of config, to handle breaking changes. There is a relatively small bspwm Arch Linux Wiki page, that describes some basic features, the `README.md` on GitHub and a manpage. Having a manpage is a big plus, but is insufficient without further documentation. The man page is there to describe the command line parameters, but there's no introduction, no guide, no tutorial and no workflow. Airblader provides some basic config examples, but without description or context.


<img src="/images/slant-bspwm-i3.jpg" onclick="window.open(this.src)">
<img src="/images/slant-bspwm-bad-docs.jpg" onclick="window.open(this.src)">

Bspwm could be much more popular (see Slant screenshot above), if it would provide a good documentation, be it a set of markdown files, a PDF or a website. Therefore I decided to start a simple [documentation website for bswpm](https://madnight.github.io/bspwm/), that is auto generated from the few available official resources. The advantage of this approach is, that in case of changes, the documentation page can be simply regenerated and therefore always stays up to date. Furthermore I added a [corresponding GitHub Issue](https://github.com/baskerville/bspwm/issues/645) that addresses this issue.
