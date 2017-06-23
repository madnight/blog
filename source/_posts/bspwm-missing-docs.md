---
title: The missing docs of bspwm
date: 2017-06-23
tags: ["bspwm", "WM", "Linux", "ricing"]
subtitle: bspwm as undocumented i3-gaps alternative
---

# This post is WIP

# Introduction
Although this post is about bspwm, lets start with i3 and why im not using it, beside its excelent documentation. i3 is a tiling window window manager, started at as fork of wmii, written by Micheal Stapelberg.[^1] One popular feature of most tiling window managers, are visial aps between application windows. The main problem of users who like gaps, is that i3 is lacking the gaps feature. Is this really a thing? Well just compare the i3 repo[^2] (2.1 k stars) with the fork i3-gaps[^3] (1.3 k stars). This fork only contains the missing gaps feature. Its hard to find a comparable fork on Github, that have such a major impact on the community, just by adding a tiny feature. The subreddit /r/unixporn with 64k subscriber also shows that many users are prefering the i3 gaps varians instead of i3.

The creator and maintainer of i3 thinks that gaps are useless{% raw %} <sup>[citation needed]</sup> {% endraw %}. The reason why many poeple think otherwise vary, some people like the visual separation of their applications, others simply like the fancy look and some have a specific use case in mind. However it seems that it is not possible to convince Michael to merge the i3-gaps fork maintained by Airblader.[^2]

Now the story could end here, use i3-gaps and be happy with a fork of the most popular and well documented tiling wm. But i3-gaps also have it's problems. First of all it is not official supported, so there might be bugs, there might be a problem with the gaps, there might be a missing gaps feature. Lets talk about the latter. The bspwm allows a very fine granulated control over the gaps, you can set them dynamically and you can set each gap (north, east, south, west) individually. This comes handy, for instance if you want to have a permanent visual conky on one side of your screen. Not so with i3-gaps, its simply not supported and Airblader has currently no time to implement it, fair enough ... lets switch to the second most popular tiling wm bspwm with native gaps support.

# The missing docs
bspwm is a great alternative to i3-gaps, but unforounatley (typo fix it) it lacks documentation. Not only that the commands change over time, so that every guide and documentation gets outdated over time and people gets confused from their own bspwm config. There is not even an simple introduction guide. There is a relativley small bspwm arch linux wiki page, that describes some basic features, the projects readme.md and a manpage. Having a manpage is a big plus, but that cannot be considerd enough, since it only describes the command line parameters, no introduction, no guide, no tutorial and no workflow. Airblader provides some basic config examples, but without description or context.

I think that the bspwm could be much more popular if it would provide a good documentation, be it a set of markdown files, a pdf or a website. So I started a simple documentation website for bswpm, that is auto generated from the few available offical ressources. The advantage of this approach is, that in case of breaking changes, the documentation page can simply be regenerated and therefore stays up to date. Here you go https://madnight.github.io/bspwm/. 

## References
[^1]: [Michael Stapelberg Github](https://github.com/stapelberg)
[^2]: [i3](https://github.com/stapelberg/i3)
[^3]: [i3-gaps](https://github.com/Airblader/i3)
