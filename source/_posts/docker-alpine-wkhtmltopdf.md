---
title: Minimal Wkthmltopdf Docker Container
date: 2017-06-22
tags: ["docker", "patch", "pdf", "musl"]
subtitle: HTML to PDF minimal Docker container, without X11
---

# Introduction

All major browsers, such as Chrome, Firefox and Safari are capable of exporting the currently visited website from HTML to PDF. This can be done via the _print_ or _save as_ function. However, there is no standard way of doing so on the command-line. Lets build a command-line with the following goals in mind: a small footprint, minimal dependencies, composing existing technology, many options for full control of the PDF generation process and a simple usage on Linux, Mac and Windows. To achieve this, I decided to use the well documented and maintained command-line utility *wkhtmltopdf* and a Alpine Linux based Docker image, to make it available on all platforms with Docker support.

# Alpine Linux

Building Docker images based on Debian or Ubuntu often results in image sizes of a few hundred megabytes or more. This is a well known problem and therefore many Docker image distributors are also offering an Alpine Linux based Docker image. The Alpine Linux distribution is a very common Docker base distribution, because of its very small size of about 5 MB. After a fast Google search, the *wkhtmltopdf* package of the [official Alpine repositories](https://pkgs.alpinelinux.org/package/edge/testing/x86/wkhtmltopdf) shows up in the search results. Interestingly though, the given binary size is just about 202 KB. Which would be perfectly fine, if it wasn't for the dependency list. It contains 7 items, including *qt5-qtwebkit*. Unfortunately, this alone requires 28 MB (installed size) and Xorg. Not only that, the Xorg server needs to be started in order to use the binary.

# Qt Patches

Since *wkhtmltopdf* uses the webkit engine to render PDFs, there is no way around the *qt5-qtwebkit* dependency. However, it is possible to avoid Xorg. I was able to find a [GitHub repository](https://github.com/alloylab/Docker-Alpine-wkhtmltopdf) that provides a solution, by compiling a *qt-webkit* version without the need for Xorg.

{% vimhl Dockerfile %}
FROM alpine:3.5
MAINTAINER Fabian Beuke <mail@beuke.org>

RUN apk add --update --no-cache \
    libgcc libstdc++ libx11 glib libxrender libxext libintl \
    libcrypto1.0 libssl1.0 \
    ttf-dejavu ttf-droid ttf-freefont ttf-liberation ttf-ubuntu-font-family

# on alpine static compiled patched qt headless wkhtmltopdf (47.2 MB)
# compilation takes 4 hours on EC2 m1.large in 2016 thats why binary
COPY wkhtmltopdf /bin

ENTRYPOINT ["wkhtmltopdf"]
{% endvimhl %}

Unfortunately, this led to a new problem. The compilation of the whole Qt library including the necessary patches takes about 4 hours on *EC2 m1.large* in 2016. It would be ok to do so once, but Docker requires you to do so every time you want to build the container, in case that you don't already have that Docker layer. At first, I thought that I could address that issue by pushing the build to Docker Hub. Docker Hub compiles Dockerfiles and provides a compiled Docker image that can be pulled from their servers. But Docker Hub has a [build timeout](https://stackoverflow.com/questions/34440753/docker-hub-timeout-in-automated-build) after 2 hours, so it wasn't able to finish the build.

<img src="/images/docker-wkhtmltopdf-alpine.png" onclick="window.open(this.src)">

Therefore I compiled the Dockerfile on my computer, pushed the binary to the GitHub repository, copied it into the Dockerfile and pushed everything to [Docker Hub](https://hub.docker.com/r/madnight/docker-alpine-wkhtmltopdf/).

### Update September 2019

I found that it is now possible to build the patched wkhtmltopdf Alpine binary in Travis CI, although documentation says otherwise:

> It is very common for test suites or build scripts to hang. Travis CI has specific time limits for each job, and will stop the build and add an error message to the build log in the following situations:
> * When a job produces no log output for 10 minutes.
> * When a job on a public repository takes longer than 50 minutes.
> * When a job on a private repository takes longer than 120 minutes.

Source: https://docs.travis-ci.com/user/customizing-the-build/#build-timeouts

As you can see in [Travis CI](https://travis-ci.org/madnight/docker-alpine-wkhtmltopdf/builds/585241704) the build takes more than one hour, despite being a job on a public repository. Now, being able to build in CI, I removed the binary from the git repository and copied it from the builder image into the Docker image.

{% vimhl Dockerfile %}
COPY --from=madnight/alpine-wkhtmltopdf-builder:0.12.5-alpine3.10 \
    /bin/wkhtmltopdf /bin/wkhtmltopdf
{% endvimhl %}
