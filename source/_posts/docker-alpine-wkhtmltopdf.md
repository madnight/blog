---
title: Minimal wkthmltopdf alpine Docker container without X
date: 2017-06-22
tags: ["Docker", "Patch", "PDF", "musl"]
subtitle: Generate PDF's from HTML with minimal Docker container, without X11 using qt patches
---

# Introduction

Render HTML to PDF on the clientside can be done by any major browser, often through the print or save as function, but there is no standard way of doing so on the serverside or on the command line. Lets build a docker container command line tool by composing existing technology, with a small footprint, with minimal dependencies, with many different command line options for full control of the pdf generation process and a simple usage on Linux, Mac and even Windows. To achieve that goal I decided to use the well documented and maintained commandline utility wkhtmltopdf and a alpine based docker to make it available on all systems that run docker.

# Alpine Linux

Building Docker images based on debian or ubuntu often results in image sizes of a few hundred megabytes and more. This is a known problem and therefore many docker image distributors also offers a alpine linux based image. The alpine linux distribution is a very common docker linux base distro, because of its small size. After a small google search one will find the wkhtmltopdf package in the official repositories[^1]. Interestingly though, the given binary size is about 202 kB. That would be fine, if there wouldn't be a problem with the dependencies list. It contains 7 items. One of them is qt5-qtwebkit. Unfortunately this one requires 28 MB (installed size) and Xorg. Not only that, the Xorg server needs to be started to use the tool.

# Qt patches

Since wkhtmltopdf uses the webkit engine to render its PDFs, there will be no way around the qt5-qtwebkit. However it is possible to get around a started instance of Xorg. I found a repository[^2] that provided a solution for that problem, by compiling a qt-webkit version without the need for Xorg.
{% raw %}
<script src="https://gist-it.appspot.com/github/madnight/docker-alpine-wkhtmltopdf/blob/master/Dockerfile"></script>
{% endraw %}
The problem with it was, that compiling the whole qt library including the necessary patches takes about 4 hours (on EC2 m1.large in 2016). It would be ok to do so once, but docker requires to do so every time you want to build the container, in case that you don't already have the docker layer. At first, I thought that I could work around that problem by pushing the build to docker hub. Docker hub compiles Dockerfiles and provides a compiled variant that can be pulled from their servers. But docker hub has a build timeout after 2 hours[^3], so it wasn't able to finish the build.

![](/images/docker-wkhtmltopdf-alpine.png)

Therefore I compiled the image locally, pushed the binary into the Github repository, copied it into the docker file and pushed everything to docker hub.
https://github.com/madnight/docker-alpine-wkhtmltopdf


## References
[^1]: [Alpine Linux wkthmltopdf](https://pkgs.alpinelinux.org/package/edge/testing/x86/wkhtmltopdf)
[^2]: [Docker Alpine Qt Patches](https://github.com/alloylab/Docker-Alpine-wkhtmltopdf)
[^3]: [Docker hub build timeout stackoverflow](https://stackoverflow.com/questions/34440753/docker-hub-timeout-in-automated-build)
