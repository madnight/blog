---
title: Quantifying AI Coverage on Hacker News
subtitle: The Growth of AI Mentions on Hacker News since 2008
date: 2025-10-09
tags: ["hacker news", "artificial intelligence", "statistical analysis"]
categories:
  - Computer Science
---

The chart in this article captures how often Hacker News front-page stories mention AI-related keywords each month, from early 2008 through July 2025. The underlying dataset comes from the ClickHouse public dataset[^8] and filters for submissions where the titles contain terms such as "artificial intelligence", "ChatGPT", "LLM", "transformer", "machine learning", and dozens more. For every month we compute percentage of those stories whose titles match at least one AI keyword.

<figure>
  <img src="/images/ai_percentage_over_time.png" alt="Share of Hacker News front-page stories mentioning AI, 2008–2025" />
  <figcaption>Monthly percentage of Hacker News front-page stories that mention AI-related terms. The dashed line marks the public launch of ChatGPT (Nov 30, 2022).</figcaption>
</figure>

The graph renders these values as a monthly bar chart. Each bar shows the share of stories in that month that referenced AI. A dashed vertical line marks the public launch of ChatGPT on November 30, 2022, with a callout label slightly above the plot for quick reference. In the following you can find the query to obtain the data.

<details>
  <summary>SQL Query</summary>
  <div class="coq">
{% vimhl sql %}
SELECT
    month,
    countIf(type = 'story') AS total_stories,
    round(
        100 * countIf(
            match(
                lower(title),
                '\\b(' ||
                'artificial intelligence|' ||
                'artificial general intelligence|' ||
                'ai safety|alignment|' ||
                'gpt|chatgpt|gpt-[0-9]|llm|large language model|' ||
                'openai|anthropic|claude|sonnet|grok|' ||
                'gemini|bard|sora|copilot|midjourney|' ||
                'dall[- ]?e|stable diffusion|runway|deepmind|' ||
                'huggingface|mistral|falcon|perplexity|' ||
                'reka|blackbox|palm|gemma|' ||
                'prompt engineering|auto[- ]?gpt|' ||
                'agentgpt|langchain|llama|llama2|llama3|' ||
                'transformer|neural network|machine learning|deep learning|' ||
                'embedding model|vector database|semantic search|' ||
                'qwen|deepseek|kimi|o3|o4' ||
                ')\\b'
            )
        ) / nullIf(countIf(type = 'story'), 0),
        3
    ) AS ai_percentage
FROM
(
    SELECT
        toStartOfMonth(time) AS month,
        title,
        type
    FROM hackernews_history
    WHERE type = 'story'
      AND title != ''
      AND time IS NOT NULL
)
GROUP BY month
HAVING month >= toDate('2006-01-01')
ORDER BY month;
{% endvimhl %}
  </div>
</details>



## Early Years (2007–2015)

In Hacker News’s first several years, AI was a niche topic. The share of submissions about AI was very low – on the order of a few tenths of a percent of total submissions per month in the late 2000s and early 2010s. During this period, Hacker News discussions were dominated by general startup and programming topics, and AI had not yet entered the tech mainstream. There were occasional spikes of interest (for instance, academic milestones or notable AI research news), but these were modest. Even by 2014–2015, AI-related stories made up only around **0.5–1%** of the monthly submissions on HN. The gradual uptick through the mid-2010s reflects how machine learning and deep learning began moving from academic circles into industry and popular awareness. For example, 2015 saw increasing buzz in the tech community around neural‑net powered image recognition and personal assistants, and by late 2015 the proportion of AI‑themed stories crept above **1%**. Still, in absolute terms, AI was a minor slice of Hacker News content prior to 2016.

## Growth of AI Discussion (2016–2021)

The volume of AI discussions started to noticeably grow around 2016. Several events around that time likely contributed. In March 2016, DeepMind’s AlphaGo achieved a landmark victory against a world champion Go player[^1], sparking global interest in AI capabilities. That year also saw the founding of OpenAI (late 2015) and a surge of investment and research in deep learning. On Hacker News, one can observe the share of submissions about AI roughly doubling from around **1%** in 2015 to over **2%** by the end of 2016, based on keyword analysis of post titles. From 2016 onward, the trend is a steady climb: each year AI becomes a larger part of the discourse. By 2017–2018, roughly **2.5–3%** of monthly HN submissions were related to AI, and this proportion held in the few‑percent range through 2021. Notable inflection points in this period correspond to high‑profile announcements – for instance, AlphaGo Zero in late 2017 (showing AI self‑learning superhuman Go play)[^2] and the release of GPT‑2 in 2019[^3]. GPT‑2, unveiled by OpenAI in February 2019, was a text‑generating model that gained attention in part due to OpenAI’s decision to initially withhold the full model for fear of misuse. This and other advances kept AI in the tech news, but the overall share on HN still remained in the low single digits.

## 2022–2025

In late November 2022, OpenAI released ChatGPT (an easy‑to‑use conversational AI based on GPT‑3.5)[^5]. Almost overnight, AI became a dominant topic not just among specialists but across the tech world and beyond. Hacker News, with its tech‑savvy audience, reflected this interest: by December 2022, roughly **8%** of all stories posted that month were about AI, more than double the share in the month before (around **3.5%** in November 2022). This was an unprecedented jump in the data.

By March–April 2023, AI‑related submissions composed roughly **13–14%** of all Hacker News stories – a tenfold increase in share compared to a few years prior. In 2025 we are facing about **18%**. This peak represents the height of the “AI boom” on HN so far, corresponding with the intense public interest in generative AI during that period.

## Highlights from the data

- **Steady climb (2017–2021)**: Starting around 2017 the monthly share oscillates between **2–4%**, driven by deep learning breakthroughs, transformer papers[^4], and new tooling. The trend is upward but still relatively muted.
- **ChatGPT inflection (late 2022)**: The ChatGPT launch coincides with the most dramatic jump in the series. The chart shows the share doubling within a single month—from roughly **3.6%** in November 2022 to **8.2%** in December 2022.
- **Generative AI era (2023–2025)**: After the initial spike the monthly share settles into a higher band between **9%** and **18%**. Peaks align with the release of new foundation models and product announcements (GPT‑4[^6], Llama 2[^7], etc.)

## Takeaways

- AI has shifted from a niche research topic to a dominant theme on Hacker News. The chart’s sustained high interest after late 2022 suggests that generative AI remains the community’s most persistent discussion driver.
- Spikes in the percentage often coincide with headline-grabbing launches or policy debates, underlining how product releases and societal implications feed directly into the news cycle.
- Even as total story volume fluctuates, the relative share focusing on AI keeps climbing, indicating continued audience appetite for coverage of large language models, agents, and related tooling.

## References

[^1]: Silver, D., Huang, A., Maddison, C. J., et al. (2016). Mastering the game of Go with deep neural networks and tree search. Nature, 529, 484–489. DOI: 10.1038/nature16961. https://www.nature.com/articles/nature16961

[^2]: Silver, D., Schrittwieser, J., Simonyan, K., et al. (2017). Mastering the game of Go without human knowledge. Nature, 550, 354–359. DOI: 10.1038/nature24270. https://www.nature.com/articles/nature24270

[^3]: OpenAI (2019). Better Language Models and Their Implications. OpenAI Blog. https://openai.com/blog/better-language-models

[^4]: Vaswani, A., Shazeer, N., Parmar, N., et al. (2017). Attention Is All You Need. arXiv:1706.03762. https://arxiv.org/abs/1706.03762

[^5]: OpenAI (2022). Introducing ChatGPT. OpenAI Blog. https://openai.com/blog/chatgpt

[^6]: OpenAI (2023). GPT‑4 Technical Report. arXiv:2303.08774. https://arxiv.org/abs/2303.08774

[^7]: Touvron, H., Martin, L., Stone, K., et al. (2023). Llama 2: Open Foundation and Fine‑Tuned Chat Models. arXiv:2307.09288. https://arxiv.org/abs/2307.09288

[^8]: ClickHouse HN Dataset — Hacker News dataset accessed via play.clickhouse.com. https://play.clickhouse.com/
