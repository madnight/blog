---
title: Docker alpine wkthmltopdf
date: 2017-06-22
tags: ["Docker", "Patch", "PDF", "musl"]
subtitle: Generate PDF's from HTML with minimal Docker container, without X11
---

# Introduction

Rendering PDF's from HTML can be done by an major browser, however it might be necessary to render HTML to PDF's on the server side or on the command line. Creating command line utilities with a small footprint, without much dependencies and simple, easy usage is not a trivial task, especially if you have to leave the well supported linux distros such as Debian.

# Alpine Linux

As you may know the alpine linux distribution is a very common choice as docker linux base distro, cause of its small size. After a small search one will find the package in the official repositories[^1]. Interestingly though, the given binary size is about 202 kB. Well that would be fine, if there wouldn't be a problem with the dependencies list. It contains 7 items. One of them is qt5-qtwebkit. Unfortunately this one requires 28 MB (installed size) and Xorg. Not only that, the Xorg server needs to be started to use the tool. At this point i realized that i have to search for another solution.


## References
[^1]: [Alpine Linux wkthmltopdf](https://pkgs.alpinelinux.org/package/edge/testing/x86/wkhtmltopdf)
