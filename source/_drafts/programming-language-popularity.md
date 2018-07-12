---
title: Programming Language Popularity
date: 2017-09-10
tags: ["github", "javascript", "programming"]
subtitle: GitHub Programming Language Popularity based on BigQuery data
---

The topic of this post is a comparison of different programming language popularity rankings and why I decided to add yet another programming language popularity index.

Many different programming language popularity rankings can be found in the Internet. Three popular ones that show up on the first google search page are:

* [TIOBE Programming Community Index](//tiobe.com/tiobe-index/)
* [The RedMonk Programming Language Rankings](//redmonk.com/sogrady/2016/07/20/language-rankings-6-16/)
* [The PYPL PopularitY of Programming Language Index](//pypl.github.io/PYPL.html)

It's not easy to choose an objective indicator for a programming popularity ranking.

#### <center>Comparison of programming popularity rankings</center>

| Features           | TOIBE           | RedMonk                  | PYPL              |
| -------------      | :-------------: | :-------------:          | :-----:           |
| Data source        | Search engines  | GitHub                   | Google Trends     |
| Available data set | 5,000$[^toibe]  | GitHub Archive           | Google Trends     |
| Metric             | Intransparent   | Pull Request             | Tutorial searches |
| Years covered      | Since 2001      | Since 2004               | Since 2004        |
| TOP 3 in 2017      | Java, C , C++   | JavaScript, Java, Python | Java, Python, PHP |

The major critism of the TOIBE index is that it is actually way behind of what's actually going on in the programming community. For example, the authors of the PYPL Index describe the TOIBE index as a lagging indicator.[^pypldiff] Another problem is the availability of the TOIBE dataset. Its fairly safe to say that almost no one is willing to pay 5.000$ to be able to see how the ranking is actually build. This makes the index intransparent and hard to reproduce. Even if one were to buy the dataset it's still a open mystey why and how TOIBE choose differen percentage weights for different data sources resulting in a arbitrary metric, where the ranking can be adjusted just by playing around with the choosen parameters. Because of this we can conclude that the TOIBE Index as a lagging and subjective indicator, which is in many cases the opposite of what you want, namely an up to date and neutral index. Lets see if PYPL is any better.

The PYPL PopularitY of Programming Language[^pypl] Index is created by analyzing how often language tutorials are searched on Google. The more a language tutorial for a certain programming language is searched on Google, the more popular the language is assumed to be. Its raw data comes from Google Trends, that makes it quite transparent.

The RedMonk Programming Language Ranking is published in irregualar intervals. The lates release was in June 2017. According to RedMonk they use the following criterias to build their ranking:

* Query languages by pull request
* Language is based on the base repository language
* Exclude forked repos
* Aggregated history to determine ranking

The RedMonk ranking makes some sensible decision on how to improve the quality of the raw dataset by applying some filters (e.g. no forks) while trying to stay as neutral as possible. However they are missing the feature of historical data, draw a graph.

Add screenshot of RedMonk here ...

There are also other rankings that are worth noting. The https://octoverse.github.com/ which is a offical GitHub source and shows some additonal intresting statistics about GitHub. However, their ranking only shows the top 15 programming languages and it does not offer a history, nor does it reveal any informations on how the underlying data has been aggreagated. Another one is the Programming Language Popularity chart on https://langpop.corger.nl, which shows a bubble chart with StackOverflow (tags) / GithHub (lines changes) ratio for every language on GitHub in Februrary 2013. Its seems as though the chart didn't received any update since then and can therefore be considered outdated.

Since non of the presented approaches matches my criteria for a sensible, neutral, reproducible, forkable, up to date solution, I decided to create a page that is not based on multiple indicators and weights, instead it is based on raw data from one source, with one metric. One have to say that it's impossible to find a data source that a approximates the entire programming community, because many projects are closed source.

Another consideration that comes to mind is that it is not said that the developers are happy with that language, for instance the Microsoft Kernel is written in C++. So should a popularity index somehow respect that the developers are free to choose the language and are not forced to do so? On the other hand there are developer surveys where programming language that are not largely used such as haskell, seems to have many developer fans and thats whats they write in on their weekends, according to this [stackoverflow blog post](https://stackoverflow.blog/2017/02/07/what-programming-languages-weekends/).

The idea to create a analysis of popularity from programming languages that are used on github is not new. The github project githut provided ... 
Unfortunately the dataset have not been updated since 2015. Issues have been raised, in where the project creator have been asked what has happened to the project. His answer was, that Github changed their BigQuery dataset, making it impossible to fetch the required information to proceed the project.

The ranking is intented to not make the impression that any of the listed language is better than any other language as a result of an complicated calculation, it is better to be understood as a sorted list based on a criteria. The criterias are given by the dataset itself, they are simply the type of events that got tracked.

it simply provides a metric on how many issues


## References
[^pypl]: The PYPL PopularitY of Programming Language is an indicator based on Google Trends, reflecting the developers searches for programming language tutorial, instead of what pages are available.
[^toibe]: [TOIBE Frequently Asked Questions (FAQ)](https://www.tiobe.com/tiobe-index/)
*Q: I would like to have the complete data set of the TIOBE index. Is this possible?*
*A: We spent a lot of effort to obtain all the data and keep the TIOBE index up to date. In order to compensate a bit for this, we ask a fee of 5,000 US$ for the complete data set. The data set runs from June 2001 till today*
[^pypldiff]: [PYPL FAQ](http://pypl.github.io/PYPL.html)
*The TIOBE Index is a lagging indicator. It counts the number of web pages with the language name. Objective-c programming has over 20 million pages on the web, [s] while C programming has only 11 million. [s] This explains why Objective-C has a high TIOBE ranking. But who is reading those Objective-C web pages ? Hardly anyone, according to Google Trends data. Objective C programming is searched 30 times less than C programming. [s] In fact, the use of programming by the TIOBE index is misleading (see next question).*


