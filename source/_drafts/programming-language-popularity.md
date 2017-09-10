---
title: Programming language popularity
date: 2017-09-10
tags: ["Github", "JavaScript", "Programming"]
subtitle: Github programming language popularity based on BigQuery datasets
cover: https://i.imgur.com/jhIkc55.jpg
---

There are many programming language popularity rankings out there in the Internet.
Three of the more popluar ones, that show up on the first google search pages are:

* [TIOBE Programming Community Index](//tiobe.com/tiobe-index/)
* [The RedMonk Programming Language Rankings](//redmonk.com/sogrady/2016/07/20/language-rankings-6-16/)
* [The PYPL PopularitY of Programming Language Index](//pypl.github.io/PYPL.html)

Its not easy to choose an objective indicator for programming popularity ranking.

| Features           | TOIBE           | RedMonk                  | PYPL              |
| -------------      | :-------------: | :-------------:          | :-----:           |
| Data source        | search engines  | GitHub                   | Google Trends     |
| Available data set | 5,000$          | GitHub Archive           | Google Trends     |
| Metric             | intransparent   | Pull Request             | tutorial searches |
| Years covered      | since 2001 | since 2004               | since 2004        |
| Top 3 (2017)       | Java, C , C++   | JavaScript, Java, Python | Java, Python, PHP |


The PYPL PopularitY of Programming Language Index is created by analyzing how often language tutorials are searched on Google. The more a language tutorial is searched, the more popular the language is assumed to be. It is a leading indicator. The raw data comes from Google Trends.

TOIBE data set
> Q: I would like to have the complete data set of the TIOBE index. Is this possible?
> A: We spent a lot of effort to obtain all the data and keep the TIOBE index up to date. In order to compensate a bit for this, we ask a fee of 5,000 US$ for the complete data set. The data set runs from June 2001 till today.


, but mixing things together with different percentage weights it seems arbitrary metric

Lets examine the pros and cons of each of theses rankings.

One of the popular ones is the TOIBE index, that is based TODO describe on what its based


For this very reason i decided to create a page that is not based on multiple indactors and weights, instead it is based on raw data from one source, with one metric.

It's impossible to find a data source that a approximates the entire programming community, because many projects are closed source.

Another consideration that comes to mind is that it is not said that the developers are happy with that language, for instance the Microsoft Kernel is written in C++. So
should a popularity index somehow respect that the developers are freee to choose the language and are not forced to do so? On the other hand there are developer surveys where prpgramming language that are not largley used such as haskell, seems to have many developer fans and thats whats they write in on their weekends, according to this [stackoverflow blog post](https://stackoverflow.blog/2017/02/07/what-programming-languages-weekends/).

Some other questions that should be considered is :
So you have to chose publicty  avaikable
so that anyone is able to check the results

The idea to create a analysis of popularity from programming languages that are used on github is not new. The github projecr githut provided ... such a thing
unfortunaltey the dataset havve not been updated since 2015. Issues have been raised, in where the project creator have been asked what has happend to the poject. His answer was, that Github changed their BigQuery dataset, making it impossible to fetch the required information to proceed the project.

The ranking is intented to not make the impression that any of the listed language is better than any other language as a result of an complicated calculation, it is better to be understood as a sorted list based on a critera. The criteras are given by the dataset itself, they are simply the type of events that got tracked.

it simply provides a metric on how many issues


## References
[^1]: The PYPL PopularitY of Programming Language is an indicator based on Google Trends, reflecting the developers searches for programming language tutorial, instead of what pages are available.
[^2]: [TOIBE Frequently Asked Questions (FAQ)](https://www.tiobe.com/tiobe-index/)
*Q: I would like to have the complete data set of the TIOBE index. Is this possible?*
*A: We spent a lot of effort to obtain all the data and keep the TIOBE index up to date. In order to compensate a bit for this, we ask a fee of 5,000 US$ for the complete data set. The data set runs from June 2001 till today*




