---
title: Programming Language Popularity
date: 2018-07-14
tags: ["ranking", "programming languages"]
subtitle: GitHub Programming Language Popularity based on BigQuery
---

### Introduction

The topic of this post is a comparison of different programming language popularity rankings and why I decided to add yet another programming language popularity index. Many different programming language popularity rankings can be found in the Internet. Three popular ones that show up on the first Google search page are:

* [TIOBE Programming Community Index](//tiobe.com/tiobe-index/)
* [The RedMonk Programming Language Rankings](//redmonk.com/sogrady/2016/07/20/language-rankings-6-16/)
* [The PYPL PopularitY of Programming Language Index](//pypl.github.io/PYPL.html)

It's not easy to choose an objective indicator for a programming popularity ranking. The following table provides a small overview of existing solutions.


{% raw %}<div style="overflow-x:auto;"><center>{% endraw %}
#### Comparison of programming popularity rankings

| Features           | TOIBE           | RedMonk                  | PYPL              |
| -------------      | :-------------: | :-------------:          | :-----:           |
| Data source        | Search engines  | GitHub                   | Google Trends     |
| Available dataset | 5,000$[^toibe]  | GitHub Archive           | Google Trends     |
| Metric             | Intransparent   | Pull Request             | Tutorial searches |
| Years covered      | Since 2001      | Since 2004               | Since 2004        |
| TOP 3 in 2018      | Java, C , C++   | JavaScript, Java, Python | Java, Python, PHP |
<br>
{% raw %}</div>{% endraw %}

### TOIBE
The major criticism of the TOIBE index is that it is actually way behind of what's actually going on in the programming community. For example, the authors of PYPL describe the TOIBE index as lagging indicator.[^pypldiff] Another problem is the availability of the TOIBE dataset. It's fairly safe to assume that almost no one is willing to pay 5.000$ to be able to see how the ranking is actually build. This makes the index intransparent and hard to reproduce. Even if one were to buy the dataset it's still a mystery why and how TOIBE choose different percentage weights for different data sources resulting in a arbitrary metric, where the ranking can be adjusted just by playing around with the parameters. Because of this we can conclude that the TOIBE Index is a slow and subjective indicator, which is in many cases the opposite of what you want. Let's see if RedMonk can do any better.

<img src="/images/toibe.png" onclick="window.open(this.src)">

### RedMonk
The RedMonk Programming Language Ranking is published in irregular intervals. The latest release was in January 2018. According to RedMonk they use the following criteria to build their ranking:

* Query languages by pull request
* Language is based on the base repository language
* Exclude forked repos
* Aggregated history to determine ranking

The RedMonk ranking makes some sensible decision on how to improve the quality of the raw dataset by applying some filters (e.g. no forks) while trying to stay as neutral as possible. However they are missing features, such as historical data and a historical chart.

<img src="/images/redmonk.png" onclick="window.open(this.src)">

### PYPL
The PYPL PopularitY of Programming Language Index[^pypl] is created by analyzing how often language tutorials are searched on Google. The more a language tutorial for a certain programming language is searched on Google, the more popular the language is assumed to be. Its dataset is based on Google Trends, which makes it quite transparent. The main drawback of PYPL is that it only compares the TOP 22 languages (as of July 2018) and there are no historical rankings. They only provide a historical chart.

<img src="/images/pypl.png" onclick="window.open(this.src)">

### Other

There are other rankings worth noting. The [octoverse](https://octoverse.github.com/) which is a official GitHub source and shows some additional interesting statistics about GitHub. However, their ranking only shows the top 15 programming languages and it does not offer a history, nor does it reveal any informations on how the underlying data has been aggregated. Another one is the Programming Language Popularity chart on https://archive.is/f1ZBZ, which shows a bubble chart with StackOverflow (tags) / GithHub (lines changes) ratio for every language on GitHub in February 2013. It seems as though the chart didn't received any update since then and can therefore be considered outdated.

### Conclusion

Since non of the presented approaches matches my criteria for a sensible, neutral, reproducible, forkable, up to date solution, I decided to create a page that is not based on multiple indicators and weights, but on raw data from one source with a flexibel unbiased metric. The idea to create a neutral and open source analysis of programming language popularity that are used on GitHub is nothing new. The GitHub project http://githut.info provides a good solution. Unfortunately, it received its last update in 2014 and there are many unresolved issues on GitHub, hence we can consider this project as outdated and unmaintained. So I came up with a new approach [GitHut 2.0](https://madnight.github.io/githut) a successor of GitHut. It shows a ranking with the top 50 languages based on the last quarter. A language trend is calculated as difference from the same quarter of the year before. The percentages shown are the actual fractions of Pull Requests, Pushes, Stars and Issues, which represents the underlying metric of the ranking.

I have to admit that it's impossible to find a data source that approximates the entire programming community, because many projects are closed source. Another consideration that comes to mind: It is not said that the developers are happy with their bread and butter language at work, for instance the Microsoft Kernel is written in C++. Should a popularity index somehow respect that the developers are free to choose the language and are not forced to do so? On the other hand there are [developer surveys](https://stackoverfilow.blog/2017/02/07/what-programming-languages-weekends/) where programming language that are not largely used in industry, such as Haskell, have many fans and that's what they write their hobby projects on weekends. However, I think that my approach offers a good approximation on what is considered to be a current popular programming language choice in the developer community.


## References

[^pypl]: [PYPL Description](http://pypl.github.io/PYPL.html)
*The PYPL PopularitY of Programming Language is an indicator based on Google Trends, reflecting the developers searches for programming language tutorial, instead of what pages are available.*
[^toibe]: [TOIBE Frequently Asked Questions (FAQ)](https://www.tiobe.com/tiobe-index/)
*Q: I would like to have the complete data set of the TIOBE index. Is this possible?*
*A: We spent a lot of effort to obtain all the data and keep the TIOBE index up to date. In order to compensate a bit for this, we ask a fee of 5,000 US$ for the complete data set. The data set runs from June 2001 till today*
[^pypldiff]: [PYPL FAQ](http://pypl.github.io/PYPL.html)
*The TIOBE Index is a lagging indicator. It counts the number of web pages with the language name. Objective-c programming has over 20 million pages on the web, [s] while C programming has only 11 million. [s] This explains why Objective-C has a high TIOBE ranking. But who is reading those Objective-C web pages ? Hardly anyone, according to Google Trends data. Objective C programming is searched 30 times less than C programming. [s] In fact, the use of programming by the TIOBE index is misleading (see next question).*
