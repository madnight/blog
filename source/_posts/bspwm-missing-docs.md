---
title: The missing docs of bspwm
date: 2017-06-23
tags: ["bspwm", "WM", "Linux", "ricing"]
subtitle: bspwm as undocumented i3-gaps alternative
---

# This is a post is WIP

# Introduction
bspwm is a great alternative to i3-gaps. i3 is a nice window manager, started at as fork of wmii, written by Micheal Stapelberg.[^1] The main problem of i3 is it's lacking gaps feature. Why is this is a thing, well just compare the i3 repo[^2] (2.1 k stars) and then look at the fork i3-gaps[^3] (1.3 k) stars. This fork only contains the missing gaps, nothing more than a small and simple feature. Its hard to find a comparable fork on Github, that have such a major impact on the community, just by adding a tiny feature.

The creator and maintainer of i3 thinks that gaps are useless{% raw %} <sup>[citation needed]</sup> {% endraw %}, however many people (including me) want that fancy gaps. There are many different reasons for why that is the case, some people like the visual separation of their applications, others simply like the fancy look. However it seems that it is not possible to convince Michael to merge the i3-gaps fork maintained by Airblader.[^2]

Now the story could end here, use i3-gaps and be happy with a fork of the most popular and well documented tiling wm. But i3-gaps also have it's problems, first of all it is not official supported, so there might be bugs and there might be a problem with the gaps that or a missing gaps feature. Lets talk about the latter. The bspwm allows a very fine granulated control over the gaps, you can set them dynamically and you can set each gap (north, east, south, west) individually. This comes handy, for instance if you want to have a permanent visual conky on one side of your screen. Not so with i3-gaps, its simply not supported and Airblader has currently no time to implement it, fair enough.

# The missing docs

The bspwm could be the better i3. But it lacks documentation. Not only that the commands change over time, so that every guide and documentation gets outdated over time and people gets confused with their configuration files. 

It's easy to sit in front of the computer and criticize the weaknesses of others work, without providing solutions. So I started a simple documentation website for bswpm, that is auto generated from the few available offical ressources. The advantage of this approach is, that in case some breaking changes happens, the documentation page can simply be regenerated and therefore stays up to date. Here you go https://madnight.github.io/bspwm/



## References
[^1]: [Michael Stapelberg Github](https://github.com/stapelberg)
[^2]: [i3](https://github.com/stapelberg/i3)
[^3]: [i3-gaps](https://github.com/Airblader/i3)
