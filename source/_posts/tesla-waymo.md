---
title: Tesla vs. Waymo
date: 2025-10-01
tags: ["artificial intelligence", "tesla", "waymo", "autonomous driving"]
subtitle: Two different approaches to full self-driving
categories:
  - Computer Science
---

# Introduction

Waymo and Tesla represent distinct approaches to autonomous driving technology. Waymo operates driverless robotaxi fleets in select metros using sensor fusion with HD maps and city-specific safety cases, providing commercial service without human drivers in Phoenix, San Francisco, and Los Angeles. Tesla sells Full Self‑Driving (Supervised), a driver assistance system that operates nationwide with a vision‑only, end‑to‑end stack but requires constant human oversight. Waymo's deployment model emphasizes geographically limited areas with full autonomy, while Tesla distributes supervised capabilities across hundreds of thousands of customer vehicles. The companies differ in their use of sensors, maps, validation methods, and strategies for scaling autonomous transportation.

## Vehicles, Hardware, and Software

Waymo's current commercial fleet is built primarily on the Jaguar I‑PACE EV and uses its 5th- and 6th-gen "Waymo Driver" hardware. The stack fuses 360‑degree lidar, radar, and multiple cameras with onboard compute and HD maps. The 6th-gen refresh, announced in 2024 and paired with a purpose‑built Zeekr robotaxi platform, emphasizes lower sensor cost and efficiency for reduced per‑mile cost.[^1]

<figure>
  <img src="/images/waymo.jpg" alt="Waymo autonomous vehicle">
  <figcaption>Waymo's robotaxi with integrated lidar, radar, and camera sensor suite</figcaption>
</figure>

Tesla's production vehicles run a "Tesla Vision" stack that eliminates radar and ultrasonics on most models for a pure camera suite feeding an onboard FSD computer. FSD v12 uses end‑to‑end neural networks that map video directly to driving controls, replacing most handcrafted planning code. Think apprentice driver that learns by watching millions of examples rather than following an explicit rulebook. The system uses standard navigation maps for routing but avoids city‑specific HD maps.[^3]

<figure>
  <img src="/images/tesla.jpg" alt="Tesla vehicle">
  <figcaption>Tesla vehicle with camera-only perception for Full Self-Driving (Supervised)</figcaption>
</figure>

## Fundamental Approaches

Waymo depends on HD maps as a strong prior before localizing and reasoning about dynamic actors. Tesla avoids HD maps, aiming for generalization from perception alone.[^4] Waymo's lidar, radar, and camera fusion provides redundancy across weather and lighting conditions and precise range estimation. Tesla relies on multi‑camera vision and learned depth and occupancy estimation, arguing that vision captures the full richness of roadway cues and that additional sensors add cost and complexity without sufficient benefit.[^1]

Both companies train large neural models. Waymo supplements real‑world miles with extensive simulation to rehearse edge cases and validate updates. Tesla relies on fleet data under supervision and broad over‑the‑air updates. Validation differs: Waymo certifies city by city with safety cases; Tesla iterates at continental scale.[^2]

## Chronology of Key Milestones

### Waymo

* **2009 to 2016**: Google self‑driving project initiates; Waymo spun out of Google in 2016. Early demonstrations include a 2015 public road ride with no human driver for a legally blind rider, signaling driverless readiness in controlled contexts.[^5]
* **2018**: Launch of Waymo One in metro Phoenix as a commercial robotaxi service with trained safety operators and limited rider base.[^6]
* **2020**: Opening of fully driverless rides to the public in parts of Phoenix, beginning driverless commercial service.[^7]
* **2023 to 2024**: California CPUC grants Waymo authority for 24/7 paid driverless service in San Francisco, later approving expansion into parts of Los Angeles and San Mateo County. Waymo begins opening San Francisco access broadly to the public.[^8]
* **2024 to 2025**: Hardware refresh announced; the company retires Chrysler Pacifica vans in favor of all‑electric Jaguars. Waymo expands service areas in Phoenix and Los Angeles and initiates access via Uber in Austin and Atlanta.[^9]

### Tesla

* **2016 to 2017**: Elon Musk announces Tesla will demonstrate coast‑to‑coast autonomous drive by late 2017.[^10]
* **2019**: At "Autonomy Day," Musk predicts over 1 million Tesla robotaxis on roads by 2020.[^11]
* **2020**: Limited release of FSD "Beta" for supervised use on city streets begins.[^12]
* **2022**: Wide availability of FSD Beta across North America, with Tesla citing roughly 400,000 participating vehicles.[^13]
* **2023**: NHTSA directs a safety recall of FSD Beta behaviors, prompting over‑the‑air remedial changes.
* **2024**: Tesla rolled out an end‑to‑end neural architecture in FSD v12 and rebranded to "FSD (Supervised)." A 30‑day trial was offered to U.S. owners to boost exposure.[^14]

## Public Claims vs Delivered Functionality

Musk's major public timelines have repeatedly been more aggressive than realized deployments. The 2016 promise of a coast‑to‑coast autonomous trip by 2017 and the 2019 forecast of over 1 million robotaxis by 2020 remain unmet. Tesla, however, has delivered a supervised driver assistance product with iterative capability increases and a national footprint. These features remain Level 2, subject to recalls and regulatory review when safety risks were identified. Tesla dropped the "Beta" label in 2024 in favor of "Supervised" to better reflect required driver oversight.[^10]

The gap between claims and delivery has major consequences for consumer expectations and policy debates. California DMV's false‑advertising complaint against Tesla regarding Autopilot and FSD marketing survived an early dismissal attempt in 2024, indicating regulators' interest in how automation capabilities are described to the public.[^15]

## Where They Operate Today

Waymo operates paid, driverless rides in defined parts of Phoenix metro, San Francisco, and Los Angeles, with service sizes published in updates. In Phoenix, Waymo reported approximately 315 square miles of service area by mid‑2024. In 2024 to 2025, San Francisco service opened broadly and Los Angeles coverage expanded. Waymo also began offering rides via Uber in limited zones of Austin and Atlanta as it seeds future markets. Reuters reported that Waymo is completing more than 1 million paid rides per month across its network.[^16]

Tesla's supervised system provides city‑street driving features to customer cars broadly across the United States and Canada. In March 2024 Tesla offered a 30‑day trial in the U.S., and independent reporting and Tesla communications have consistently put the North American user base around 400,000 vehicles since early 2023.[^17]

## Regulatory, Technological, and Practical Limits

Waymo's model emphasizes geofenced deployments with progressive regulatory approvals, including CPUC decisions for fare collection and service expansion. The company has issued voluntary software recalls after low‑severity incidents, including collisions with stationary barriers and a bicyclist strike in San Francisco that produced minor injuries.[^8]

California disengagement reporting provides one public window into developmental performance. DMV's program requires companies testing in the state to report miles and disengagements annually, although the relevance of these metrics to driverless service remains debated. DMV reports show Waymo logged millions of California miles while steadily reducing disengagements as it moved toward rider‑only operations. The DMV maintains the official reports and mileage datasets for each year.[^18]

Tesla's system is treated as Level 2 driver assistance in the U.S., which means it must keep an engaged human supervisor at all times. NHTSA's 2023 recall aimed to mitigate specific risky behaviors in FSD Beta, and NHTSA continues oversight of Autopilot and FSD through defect investigations and standing crash reporting orders. In 2024 Tesla renamed the product to FSD (Supervised) and began a national trial to increase adoption.[^19]

Waymo's sensor‑fusion and HD maps reduce ambiguity but impose higher per‑vehicle cost and the operational overhead of mapping and certifying each expansion. Tesla's vision‑only generalization reduces dependency on prior mapping and custom sensors, facilitating wide distribution across customer cars, but places greater burden on perception to handle edge cases in adverse conditions. A Reuters analysis characterized Tesla's move to end‑to‑end "black box" models as high potential reward with notable verification and transparency challenges for safety assurance and regulators.[^20]

## Key Concepts

* **End‑to‑end neural network**: Instead of a pipeline of separate modules with explicit rules, the system learns to go from video to steering and pedals in one learned model, *similar to how a human learns to drive by feel from experience rather than consulting a stepwise checklist*. This is Tesla's stated approach in FSD v12.[^14]

* **HD map**: A machine‑readable atlas containing detailed lane geometry, curb positions, and traffic signal locations, which lets the autonomy system know the expected layout before it sees it, *much like a pilot's approach plate*. Waymo localizes to this map for context and consistency.[^4]

* **Simulation**: A synthetic driving world that can replay real incidents and generate variations to probe rare hazards, *comparable to a flight simulator's stress drills*. Waymo uses Simulation City and Carcraft to test software changes comprehensively before release.[^2]

* **Disengagement**: A handover from the automated system to a human or a remote operator during testing. Disengagement rates provide one lens on developmental maturity, though they are sensitive to test policies and not directly comparable across companies or to driverless service performance. California's DMV publishes these reports annually.[^18]

## Outlook

Waymo today operates true driverless robotaxi fleets at commercial scale in selected U.S. cities, reporting over 1 million monthly rides across Phoenix, San Francisco, and Los Angeles.[^21] The company's conservative, sensor‑heavy approach yields fully driverless service once established, though expansion remains slower due to the capital intensity of HD mapping, obtaining local permits, and building safety cases for each new metro. Near-term plans focus on densifying service in existing cities and expanding through partnerships such as Uber integration in Austin and Atlanta.

Tesla offers FSD (Supervised) to hundreds of thousands of private owners.[^17] The company aims to transition to unsupervised operation through larger end‑to‑end models trained on fleet video, likely starting with narrow geofenced domains. The key hurdles are regulatory acceptance of vision‑only, "black box" models without sensor redundancy, plus demonstrating robust performance in adverse conditions. While Tesla's approach scales quickly in coverage, it remains supervised with required human oversight.

## References

[^1]: Google Help. (2024). How our cars drive - Waymo Help. https://support.google.com/waymo/answer/9190838?hl=en
[^2]: Waymo. (2021). Simulation City: Introducing Waymo's most advanced simulation system. https://waymo.com/blog/2021/07/simulation-city/
[^3]: Tesla. (2024). Tesla Vision Update: Replacing Ultrasonic Sensors with Tesla Vision. https://www.tesla.com/support/transitioning-tesla-vision
[^4]: Waymo. (2020). The Waymo Driver Handbook: How our highly-detailed maps help unlock new capabilities. https://waymo.com/blog/2020/09/the-waymo-driver-handbook-mapping/
[^5]: Waymo. (2016). On the road with self-driving car user number one. https://waymo.com/blog/2016/12/on-road-with-self-driving-car-user/
[^6]: Waymo. (2018). Waymo One: The next step on our self-driving journey. https://waymo.com/blog/2018/12/waymo-one-next-step-on-our-self-driving/
[^7]: Waymo. (2020). Waymo is opening its fully driverless service to the general public in Phoenix. https://waymo.com/blog/2020/10/waymo-is-opening-its-fully-driverless-service-in-phoenix/
[^8]: California Public Utilities Commission. (2023). CPUC Approves Permits for Cruise and Waymo To Charge Fares for Passenger Service in SF. https://www.cpuc.ca.gov/news-and-updates/all-news/cpuc-approves-permits-for-cruise-and-waymo-to-charge-fares-for-passenger-service-in-sf-2023
[^9]: Waymo. (2024). Meet the 6th-generation Waymo Driver: Optimized for costs, designed to scale. https://waymo.com/blog/2024/08/meet-the-6th-generation-waymo-driver/
[^10]: TechCrunch. (2016). Musk targeting coast-to-coast test drive of fully self-driving Tesla by late 2017. https://techcrunch.com/2016/10/19/musk-targeting-coast-to-coast-test-drive-of-fully-self-driving-tesla-by-late-2017/
[^11]: Business Insider. (2019). Elon Musk Said Tesla Will Have 1 Million Robo-Taxis Next Year. https://www.businessinsider.com/tesla-robo-taxis-elon-musk-pt-barnum-circus-2019-4
[^12]: TechCrunch. (2020). After release of Tesla's 'Full Self-Driving' beta, Elon Musk promises roughly $2,000 price hike. https://techcrunch.com/2020/10/22/after-release-of-teslas-full-self-driving-beta-elon-musk-promises-roughly-2000-price-hike/
[^13]: InsideEVs. (2022). Tesla's FSD Beta Now Active In 400,000 Cars In US And Canada. https://insideevs.com/news/633328/tesla-fsd-beta-now-active-to-400000-cars-us-canada/
[^14]: The Verge. (2024). Tesla finally releases (sort of) its neural network Full Self-Driving feature. https://www.theverge.com/2024/1/22/24046879/tesla-finally-releases-sort-of-its-neural-network-full-self-driving-feature
[^15]: Reuters. (2024). Tesla must face California's false-marketing claims concerning Autopilot. https://www.reuters.com/legal/tesla-must-face-californias-false-marketing-claims-concerning-autopilot-2024-06-10/
[^16]: Waymo. (2024). Largest Autonomous Ride-Hail Territory in US Now Even Larger. https://waymo.com/blog/2024/06/largest-autonomous-ride-hail-territory-in-us-now-even-larger/
[^17]: Reuters. (2024). Tesla offers U.S. customers a month's trial of its driver-assist technology. https://www.reuters.com/business/autos-transportation/tesla-give-one-month-driver-assist-technology-trial-customers-2024-03-26/
[^18]: California DMV. (2024). Disengagement Reports. https://www.dmv.ca.gov/portal/vehicle-industry-services/autonomous-vehicles/disengagement-reports/
[^19]: NHTSA. (2022). Additional Information Regarding EA22002 Investigation. https://static.nhtsa.gov/odi/inv/2022/INCR-EA22002-14496.pdf
[^20]: Reuters. (2024). Tesla gambles on 'black box' AI tech for robotaxis. https://www.reuters.com/technology/tesla-gambles-black-box-ai-tech-robotaxis-2024-10-10/
[^21]: Reuters. (2025). Waymo launches corporate robotaxi accounts to court business travel. https://www.reuters.com/business/autos-transportation/waymo-launches-corporate-robotaxi-accounts-court-business-travel-2025-09-24/
[^22]: Waymo. (2024). Voluntary recall of our previous software. https://waymo.com/blog/2024/02/voluntary-recall-of-our-previous-software/
