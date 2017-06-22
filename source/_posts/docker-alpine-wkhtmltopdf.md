---
title: Docker alpine wkthmltopdf
date: 2017-06-22
tags: ["Docker", "Patch", "PDF", "musl"]
subtitle: Generate PDF's from HTML with minimal Docker container, without X11
---

# This is a post is WIP

# Introduction

Rendering PDF's from HTML can be done by an major browser, however it might be necessary to render HTML to PDF's on the server side or on the command line. Creating command line utilities with a small footprint, without much dependencies and simple, easy usage is not a trivial task, especially if you have to leave the well supported linux distros such as Debian.

# Alpine Linux

As you may know the alpine linux distribution is a very common choice as docker linux base distro, cause of its small size. After a small google search one will find the package in the official repositories[^1]. Interestingly though, the given binary size is about 202 kB. Well that would be fine, if there wouldn't be a problem with the dependencies list. It contains 7 items. One of them is qt5-qtwebkit. Unfortunately this one requires 28 MB (installed size) and Xorg. Not only that, the Xorg server needs to be started to use the tool. At this point i realized that i have to search for another solution.

# Qt patches

Since wkhtmltopdf uses the webkit engine to render its PDFs, there will be no way around the qt5-qtwebkit. However it is possible to get around a started instance of Xorg. I found this [^2] repository that provided a solution for that problem. The problem with it was, that compiling the whole qt library including the necessary patches takes about 4 hours (on EC2 m1.large in 2016). It would be acceptable to do so once, but docker requires to do so every time you want to build the container, in case that you dont have the docker layer. At first, I thought that I could work around that problem by pushing the build to docker hub. Docker hub compiles Dockerfiles and provides a compiled variant that can be publicly pulled. But there is a problem, docker hub has a build timeout after 2 hours, so it wasn't able to finish the build. Therefore I compiled it locally, pushed the binary into the Github repository, copied it into the docker file and pushed everything to docker hub. https://github.com/madnight/docker-alpine-wkhtmltopdf

## References
[^1]: [Alpine Linux wkthmltopdf](https://pkgs.alpinelinux.org/package/edge/testing/x86/wkhtmltopdf)
[^2]: [Docker Alpine Qt Patches](https://github.com/alloylab/Docker-Alpine-wkhtmltopdf)
