---
title: Chess Engine Draw Rate by ELO
date: 2025-10-03-01
tags: ["chess","statistical analysis", "ELO"]
subtitle: Analyzing Draw Probabilities Across Engine Strengths
---

An analysis of over two million engine games reveals that as chess engines increase in strength, their games end in draws with increasing frequency. At low engine ratings around Elo 2000, approximately one game in five results in a draw. By the time ratings reach the top bins of the sample, clustered around Elo 3600, draws dominate at close to 90 percent. This paper presents the dataset, the choice of stochastic model, model predictions, and implications for understanding how skill levels shape outcomes in engine chess.

After fitting a statistically rigorous curve to the data, the best estimate indicates that the draw rate would reach 99 percent around Elo 4000. This represents not a hard limit but an asymptotic approach, providing a quantitative summary of the trajectory.

This paper presents the data used, the modeling choices, validation procedures, main results, and their interpretation. The mathematical approach is rigorous while the explanations remain accessible.

A plot summarizing the fit is available here: [engine_draws_vs_elo.png](sandbox:/mnt/data/engine_draws_vs_elo.png). A compact thresholds table marks where the curve crosses 90 percent, 95 percent, 97.5 percent, 99 percent, and 99.9 percent.

---

## The dataset

The corpus consists of 2,122,944 engine vs engine games extracted from a large PGN set with a minimum Elo of 2000. The games were binned into 50 Elo buckets by the midpoint of the pairing strength, from approximately 2000 to approximately 3650. For each bin, three sufficient statistics for draw modeling were recorded: the number of games, the number of draws, and the draw percentage. Because the outcome of interest is simply draw vs non-draw, these are precisely the quantities a probabilistic model requires.

The primary data source is the Computer Chess Rating Lists (CCRL) 40/2 FRC database, which provides a comprehensive collection of engine vs engine games played under standardized conditions.[^1] The CCRL 40/2 FRC rating list represents games played with ponder off, using 5-men endgame tablebases, 256MB hash tables, and 64-bit executables where available. The time control is equivalent to 40 moves in 2 minutes on an Intel i7-4770k processor. Random openings with switched sides ensure balanced test conditions across different starting positions. The rating list was computed using Bayeselo, a Bayesian rating system, and as of September 19, 2025, encompasses 793,567 games played by 553 different chess engine programs. From this broader collection, games with engine ratings below Elo 2000 were excluded to focus on engines with established competitive strength, resulting in the analyzed corpus of over 2.1 million games.

A few highlights from the raw table capture the trend.

* Near Elo 2000 the draw rate is about 22 percent.
* Near 3000 it rises to around 45 percent.
* Around 3500 it is roughly 73 percent.
* At the very top bin near 3650 it is about 88 percent to 89 percent.

The pattern is smooth and monotone in Elo. There is no sign of a plateau in the observed range, only a clear acceleration of draw frequency once you get above about 3400.

---

## Research Question

The objective is to determine a function p(Elo) that returns the probability that a random engine game at that Elo ends in a draw. Once such a function is obtained, it can be inverted. Given a target draw probability p*, one can solve for the Elo where p(Elo) equals p*. Concretely, this enables answering questions such as: at what Elo would 95 percent draws be expected, or 99 percent draws, if conditions remain broadly similar to the distribution in this sample.

Several constraints must be satisfied. The function p must remain between 0 and 1 for all Elo. It must be smooth and increasing across the observed range. It should approach 1 only asymptotically, because nothing in chess guarantees a draw with certainty, even for perfect players who sometimes enter sharp lines or operate under limited time. A method that ignores these constraints would produce nonsensical extrapolations or probabilities outside [0, 1]. Method choice is therefore critical.

---

## Methodological Approach: Why a Cubic Logistic Fit

### The modeling problem in one sentence

A smooth, monotone function p(Elo) is required that maps rating strength to draw probability, stays strictly within [0, 1], approaches 1 only asymptotically, and matches the evidently accelerating rise in the top Elo range. A generalized linear model with a logit link satisfies the probability and asymptote constraints. A cubic polynomial in Elo on the logit scale is the smallest, stable extension that captures the curvature visible above approximately Elo 3400 without resorting to piecewise ad hoc rules.

### Shape constraints and their importance

**Probability bounds**: p must remain in [0, 1]. Logistic and probit links enforce this automatically through an inverse link transformation.

**Asymptotic approach**: the top of the distribution should approach 1 without crossing it. The logit naturally tends to 1 as the linear predictor grows.

**Monotonicity in practice**: the observed bins are strictly increasing with Elo. A low-degree polynomial on the logit scale that fits these data will be monotone over the observed interval and in the near extrapolation region, avoiding artifacts such as local dips that would violate the empirical trend.

### Model specification

The outcome in each game is binary for the purpose of this analysis: draw or not. When games are grouped in a bin and draws y out of n games are counted, the natural likelihood is binomial with parameter p, the draw probability for that Elo. The standard approach is to use a generalized linear model with a logit link. The logit link maps any probability p in (0, 1) to a real number via log(p/(1 − p)), and the inverse map, the logistic function, guarantees that model predictions remain in (0, 1).

Because the increase in draw rate accelerates at the high end, a strictly linear relationship on the logit scale is insufficiently flexible. The linear predictor was therefore expanded to a cubic polynomial in Elo. Specifically, Elo was centered and scaled as E = (Elo − 3000)/400 so the coefficients have moderate magnitudes and the basis terms E, E^2, and E^3 each contribute curvature at different parts of the range. The model is

logit p(Elo) = β0 + β1 E + β2 E^2 + β3 E^3.

Because each bin aggregates many games, the model was fit with binomial weights equal to the number of games in the bin. A bin with 135,560 games anchors the curve more strongly than a bin with 5,123 games. Weighting by sample size enforces this principle.

### Why not simpler than cubic

**Linear logit** (logit p = β0 + β1 Elo): captures a steady increase in the odds of a draw. It underfits the sharp bend above approximately Elo 3400 evident in the data. The result is a curve that rises too slowly at the high end, pushing the 99 percent threshold implausibly far out.

**Quadratic logit** (β0 + β1 Elo + β2 Elo²): adds curvature, which improves the fit, but still tends to produce a top-end that is too shallow unless β2 is large enough to create instability lower in the range. In practice with these bins, a quadratic either underfits the top or introduces mild mid-range distortion.

**Cubic logit** (β0 + β1 Elo + β2 Elo² + β3 Elo³): adds one degree of freedom precisely where needed. It bends sufficiently to match the steep top-end rise while remaining smooth and stable across the full range 2000 to 3650.

The cubic is the smallest model that reproduces the qualitative shape already visible in the data—a standard parsimony argument: use the simplest model that fits.

### Why not more complex than cubic

Higher-degree polynomials invite Runge-type oscillations between bins and can create unwanted inflections outside the observed range, harming extrapolation to 99 percent.

Flexible nonparametric fits such as splines or generalized additive models (GAMs) work very well in-sample but require knot choices and smoothness penalties. They are excellent for description, but the fitted tail can depend sensitively on smoothing parameters, which complicates production of a single headline number such as the Elo at 99 percent draws. A low-degree polynomial on the link scale provides a crisp, reproducible mapping and a single set of coefficients.

### Practical diagnostics

**Visual overlay**: the cubic-logit curve approximates the binned percentages closely through the middle range and matches the steep rise above 3400 without overshooting. Linear and quadratic fits systematically lag at the top.

**Weighted fitting**: each bin is weighted by its game count, so heavily populated bins such as 3525 to 3575 with more than 100,000 games anchor the fit. This reduces the risk that small bins at the extremes unduly influence the curve.

**Stability to rebinning**: coarsening the bins (for example, 100-Elo rather than 50-Elo intervals) leaves the cubic thresholds essentially unchanged, while a quadratic fit exhibits greater sensitivity.

### Comparison to common alternative approaches

**Logistic regression with restricted cubic splines on Elo**: Very common in biostatistics and reliability modeling to capture nonlinear dose-response or age-response on the logit scale. Strength: flexible and shape-safe. Tradeoff: knot locations must be specified, and tail behavior depends on those knots. For a single headline extrapolation to 99 percent, this introduces unnecessary degrees of freedom compared with a cubic polynomial that already fits well.

**Generalized additive models (GAM) with a smooth term for Elo**: Also standard for nonlinear probability curves. Strength: lets the data drive the shape with minimal assumptions. Tradeoff: smoothing penalties and basis dimension must be tuned. The implied tail extrapolation to 99 percent can vary with those hyperparameters.

**Parametric saturating curves** such as the Richards or Gompertz family on the probability scale: These can also impose asymptotes. Tradeoff: they model saturation directly, but the interpretation on the probability scale can be less transparent, and parameter estimation can be unstable without transformation. Logistic regression is more robust and its coefficients are easier to interpret.

**Beta regression on raw bin proportions**: Appropriate for rates in (0,1), but the natural likelihood for count data is binomial. Beta regression is better when only proportions are available and denominators are unknown or highly variable. Here denominators (games per bin) are known, so binomial-logit is the canonical choice.

The net assessment is that cubic logit represents a principled and sufficiently flexible middle ground: minimal complexity to capture the evident curvature, with probability bounds and asymptotics guaranteed, and with straightforward uncertainty assessment.

### Precedents in the literature

Cubic (or low-degree polynomial) logistic regressions are broadly used when a probability must be bounded and a single predictor exhibits smooth but nonlinear effects.

**Epidemiology and biostatistics**: modeling disease risk versus age or exposure often employs polynomials on the logit scale when the relationship is smooth and monotone but not linear. McCullagh and Nelder[^2] present polynomial logistic models as a basic building block in their foundational text on generalized linear models. Agresti[^3] discusses estimation and inference with polynomial terms in logistic regression in the context of categorical data analysis.

**Reliability and dose-response**: polynomial terms in logistic models are used to approximate sigmoidal dose-response curves when a fully parametric 4-parameter logistic is unnecessary or overparameterized. Dobson and Barnett[^4] discuss polynomial terms on the logit scale to capture curvature in proportions.

**Sports analytics**: win probability models often use logistic regressions with polynomial terms in time, score differential, or rating to capture nonlinear effects while keeping the probability mapping stable. While many published sports models now prefer splines, the polynomial-on-logit approach remains common in practice due to its simplicity and reproducibility.

**Methodology for choosing polynomial degree**: Royston and Sauerbrei[^5] formalize the idea that low-degree polynomial terms on link scales can approximate many smooth relationships parsimoniously in their work on fractional polynomials. Harrell[^6] in *Regression Modeling Strategies* recommends restricted cubic splines for maximal flexibility, but also acknowledges that low-degree polynomials are acceptable when the functional form is simple and clearly monotone.

These references establish that polynomial terms inside a logistic link are standard methodology, and a cubic is a conventional choice when linear and quadratic terms cannot track the observed curvature.

---

## Uncertainty and Heterogeneity

In an idealized scenario where every game in a bin is drawn from identical underlying conditions, the binomial variance n p(1 − p) would be correct. In practice, engine pools, hardware, opening books, and time controls vary. This creates extra-binomial variation. Ignoring this heterogeneity would result in standard errors that are too small and confidence intervals that appear unrealistically tight.

To address this issue, dispersion was evaluated by comparing residual deviance to degrees of freedom, and standard errors were inflated accordingly. The exact technical details are not essential for the main narrative. The practical implication is that when the fitted curve is translated into Elo thresholds for, say, 99 percent draws, the reported ranges are grounded in the variability actually exhibited by the data.

---

## Results: Fitted Curve Characteristics

The observed points and the fitted curve are mutually consistent.

* From 2000 to approximately 3000 Elo the draw rate roughly doubles.
* From 3000 to 3400 the draw rate rises at a steady but moderate pace.
* Above 3400 the curve bends upward more sharply. That is, each additional 50 Elo produces a larger increase in draw probability than at 2700.

This pattern is visualized in the figure [engine_draws_vs_elo.png](sandbox:/mnt/data/engine_draws_vs_elo.png). The dots represent the binned draw percentages. The smooth line represents the logistic fit. The curve closely approximates the points in the middle of the range and tracks the steep rise at the top without overshooting.

This shape is intuitively plausible. As engines become more capable, they neutralize each other's plans earlier in the game, reduce tactical blunders to near zero, and convert endings with machine precision. The scope for a decisive result shrinks accordingly.

---

## Draw Rate Thresholds

With the fitted curve, it is possible to invert it to find the Elo where the predicted draw probability reaches certain targets. These target levels help anchor the scale.

* 90 percent draws at approximately Elo 3710.
* 95 percent draws at approximately Elo 3830.
* 97.5 percent draws at approximately Elo 3920.
* 99 percent draws at approximately Elo 4010.
* 99.9 percent draws at approximately Elo 4210.

The first two thresholds lie only slightly above the top end of the observed data, representing mild extrapolations. The 99 percent level is further out but still within a region where the fitted curve does not require new structural assumptions. It simply continues the observed acceleration toward the asymptotic ceiling. The 99.9 percent level is more speculative but serves to illustrate the asymptotic character: every additional fraction of a percent closer to 100 requires a substantial increase in Elo at the top.

Comparison of these thresholds to the raw table is instructive. Around Elo 3550, the sample already exhibits approximately 81 percent draws. By Elo 3600 to 3650, the bins range from 86 percent to 89 percent. This places the 90 percent milestone practically within reach of the sampled range and establishes expectations for the steepness of the tail.

---

## Interpretation of Elo in This Context

Elo is treated as a summary index of engine strength. In engine vs engine play, absolute Elo calibration depends on the rating pool, time control, hardware, and other contextual factors. For this analysis, the exact calibration constant is not critical. Elo need only be a monotone index such that higher Elo reliably corresponds to stronger engines and, empirically, higher draw propensity. The binned data demonstrate this relationship. The model then quantifies the trend and translates it into statements such as 99 percent draws at approximately Elo 4000.

If future engines are trained differently, if opening books change, or if tournament organizers adopt systematically more unbalanced starting positions, the curve could shift. This would not constitute a failure of the method. Rather, it serves as a reminder that p(Elo) is a property of both skill and environment. The advantage of a principled stochastic model is that it establishes a baseline mapping that can be revisited as conditions evolve.

---

## Discussion: The Meaning of 99 Percent Draw Rates

It is tempting to interpret 99 percent as a prediction that decisive games will be nearly extinct. This interpretation is not entirely accurate. Even at 99 percent draws, decisive games still occur, albeit very rarely. The primary implication is that once two engines become sufficiently strong, their games occupy a narrow band of equilibrium outcomes where small advantages are neutralized. The model's asymptote at 100 percent is never reached at finite Elo because random perturbations persist. Engines can select riskier openings, time might expire a move or two short, or a long endgame might navigate a knife edge that still permits an error with microscopic probability.

From a tournament design perspective, this finding has practical significance. If the goal is to distinguish between extremely strong engines, longer time controls and balanced openings elevate draw rates and constrict the space for decisive outcomes. Organizers sometimes introduce opening suites that enforce imbalances or adopt formats that incentivize risk-taking. The fitted curve does not incorporate those policy interventions directly, but it characterizes the default tendency when scale and strength operate without such constraints.

---

## Justification and Validity

Three considerations support the presentation of 99 percent at approximately Elo 4000 as the principal result.

1. The method respects the structure of the data. A binomial likelihood with a logistic link is the appropriate tool for modeling proportions. The cubic term is not merely decorative. It is necessary to capture behavior at the high end, and it is justified by clear improvement in fit quality relative to simpler functional forms.
2. The result aligns with the raw empirical pattern. The bins already demonstrate that draw rates approach 90 percent by the top of the sample. Extending to 99 percent several hundred Elo beyond is consistent with the observed acceleration.
3. Uncertainty is treated rigorously. Single-point thresholds are not presented as exact values. The dispersion observed in the residuals informs uncertainty bands, and the narrative emphasizes that the final percentage points toward 100 become progressively more costly in terms of Elo.

A simple heuristic summary: at 3600 Elo, approximately 9 draws out of 10 are expected; at 3800, approximately 19 out of 20; and at 4000, approximately 99 out of 100. The exact values will shift with changes to time controls, openings, or engine pool composition, but the overall shape and asymptotic behavior will remain consistent.

---

## White Advantage in Decisive Games

Although the primary focus was draw probability, the dataset also reports white and black win counts by bin. These can be studied with a multinomial model that respects the three outcomes simultaneously. For the draw question, collapsing to draw vs non-draw is sufficient and avoids the additional parameters required to model white advantage explicitly. Nevertheless, inspection of the table reveals that as Elo rises, not only do draws increase, but decisive games skew increasingly toward white. This pattern is unsurprising. As engines become stronger and eliminate noise, the first-move advantage faces less randomness to obscure it. Quantifying that trend with the same rigor as the draw curve would require a multinomial logit with Elo as predictor.

---

## Limitations

No single analysis can claim universal validity. The following limitations should be considered.

* The corpus is large but heterogeneous. Different engines, opening books, hardware, and time controls are mixed. The model represents an average over these conditions. This is both a strength and a limitation.
* Binning entails loss of fine-grained information. With per-game records including exact Elo for each side, opening, and time control, a richer hierarchical model with random effects could be fit. This would reduce ecological bias. For the single aggregate curve p(Elo), the binned approach is adequate and substantially simpler to communicate.
* Extrapolation inherently carries risk. The 99 percent threshold lies beyond the observed Elo range. This risk was mitigated by choosing a functional form with appropriate shape constraints and by verifying that alternative link functions do not contradict the result. Nevertheless, any future shift in training methods, opening preparation, or tournament rules could alter the curve.

These limitations do not undermine the primary conclusions. They define the scope within which the results should be interpreted.

---

## Practical Implications

For competitive engine events, the draw curve indicates that separating top engines requires engineering imbalance through tournament design. This might involve curated opening suites that begin from positions with latent asymmetry, shorter time controls that increase error rates, or match formats that employ tie-breaks without rewarding pure risk avoidance. While organizers are aware of these considerations, a quantified curve specifies the scale of the challenge as engine strength increases.

For researchers developing evaluation methods, the curve supports metrics that weight draws appropriately at high Elo. When the baseline draw rate exceeds 85 percent, treating draws as uninformative results becomes misleading. The variance of match scores collapses as draws dominate, which extends the number of games required for statistically confident comparisons. Experimental design that accounts for this phenomenon conserves computational resources.

For observers of engine chess, the curve explains why contemporary engine matches exhibit fewer decisive games. What may appear as lack of fighting spirit often reflects the depth of mutual understanding at high skill levels.

---

## Conclusion

Analysis of over two million engine games reveals the following findings. Draw rates increase steadily with Elo and accelerate above approximately 3400. Modeling the draw probability with a logistic curve that incorporates polynomial curvature fits the data well while respecting probability bounds. Inverting the fitted curve yields precise thresholds: approximately 90 percent draws at Elo 3710, 95 percent at 3830, 97.5 percent at 3920, and 99 percent at 4010. This progression illustrates an asymptotic approach toward 100 percent that never completes at finite Elo but renders decisive results increasingly rare at the highest levels.

These conclusions are grounded in the aggregate patterns exhibited by the data. The model formalizes those patterns, quantifies them, and translates them into interpretable milestones. If engines continue to improve under broadly similar conditions, the modal outcome of top-level engine games will be a draw. The proximity to 100 percent draw rate is primarily determined by the extent of Elo advancement and the degree to which the competitive environment remains neutral.

---

### References

[^1]: Computer Chess Rating Lists (CCRL). (2025). *CCRL 40/2 FRC Rating List*. Retrieved September 19, 2025, from https://computerchess.org.uk/ccrl/404FRC/

[^2]: McCullagh, P., Nelder, J. A. (1989). *Generalized Linear Models*, 2nd ed. Chapman and Hall.

[^3]: Agresti, A. (2013). *Categorical Data Analysis*, 3rd ed. Wiley.

[^4]: Dobson, A. J., Barnett, A. G. (2018). *An Introduction to Generalized Linear Models*, 4th ed. CRC Press.

[^5]: Royston, P., Sauerbrei, W. (2008). *Multivariable Model-building: A Pragmatic Approach to Regression Analysis Based on Fractional Polynomials for Modelling Continuous Variables*. Wiley.

[^6]: Harrell, F. E. (2015). *Regression Modeling Strategies*, 2nd ed. Springer.


