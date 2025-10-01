---
title: Tesla vs. Waymo
date: 2025-10-01
tags: ["artificial intelligence", "tesla", "waymo", "autonomous driving"]
subtitle: Two different approaches to full self-driving
---

# Introduction

Tesla and Waymo pursue automated driving with markedly different philosophies, technology stacks, deployment models, and regulatory postures. Waymo fields geofenced, driverless robotaxi fleets in select U.S. metros using a multi‑sensor suite fused with high definition maps and safety cases tailored to each service area. Tesla sells an advanced driver assistance system, marketed as Full Self‑Driving (Supervised), that operates nationwide under driver supervision and relies on a camera‑only perception stack trained end‑to‑end on fleet video. Both companies continue to expand capability and scale, but their risk profiles, validation methods, and regulatory trajectories diverge.

## Vehicles, Hardware, and Software

Waymo's current commercial fleet is built primarily on the Jaguar I‑PACE EV and integrates its fifth and sixth generation "Waymo Driver" hardware. The stack fuses 360‑degree lidar, near and long range radar, and multiple cameras, coupled to on‑vehicle compute and highly detailed prior maps. The sixth generation refresh, announced in 2024 and paired with a purpose‑built Zeekr robotaxi platform, emphasizes lower sensor cost, higher range and resolution, and more efficient compute, aiming to reduce per‑mile operating cost for ride‑hail service. Think of Waymo's hardware as a synergistic team: cameras provide rich texture and color, radar offers motion and range robustness in rain or glare, and lidar supplies precise 3D geometry, all anchored to a prebuilt map of lane‑level road semantics.[^1]

<figure>
  <img src="/images/waymo.jpg" alt="Waymo autonomous vehicle">
  <figcaption>Waymo's robotaxi with integrated lidar, radar, and camera sensor suite</figcaption>
</figure>

Beyond the car, Waymo runs large‑scale simulation environments such as Carcraft and Simulation City to rehearse rare edge cases and validate software updates before on‑road release. An intuitive analogue is a flight simulator for pilots that can recreate unusual wind shear or equipment failures; Waymo's simulators replay unusual traffic scenarios at scale and stress‑test proposed behaviors without endangering riders. Waymo reports extensive use of simulation to amplify learning and vet software changes.[^2]

Tesla's production vehicles run a "Tesla Vision" stack that, by design, eliminates both radar and ultrasonic sensors on most models in favor of a pure camera suite feeding an on‑board FSD computer. Recent generations of the system, branded FSD v12, use end‑to‑end neural networks that map video directly to driving controls, replacing large amounts of handcrafted planning code. A useful mental model is an apprentice driver that learns by watching millions of examples rather than following an explicit rulebook. Tesla emphasizes that this vision‑only approach scales globally without the burden of maintaining city‑specific HD maps, though it still uses standard navigation maps for routing.[^3]

<figure>
  <img src="/images/tesla.jpg" alt="Tesla vehicle">
  <figcaption>Tesla vehicle with camera-only perception for Full Self-Driving (Supervised)</figcaption>
</figure>

## Fundamental Approaches

Waymo depends on HD maps that encode lane geometry, speed limits, and traffic control semantics. These maps act as a strong prior, similar to a pilot's instrument chart that structures navigation before sensor readings fill in live details. The on‑board stack localizes to this map and then reasons about dynamic actors. Tesla avoids HD maps, aiming for generalization from perception alone. The analogy is a human driver visiting a new city: road rules are learned from visual cues rather than memorized local blueprints.[^4]

Waymo's lidar‑radar‑camera fusion provides redundancy across weather and lighting conditions and precise range estimation. Tesla relies on multi‑camera vision and learned depth and occupancy estimation, arguing that vision captures the full richness of roadway cues and that additional sensors add cost and complexity without sufficient benefit. The debate resembles using multiple instruments vs honing one instrument to mastery.[^1]

Both companies train large neural models. Waymo supplements real‑world fully driverless miles with extensive simulation to tune and verify behaviors before public rollout. Tesla leans on at‑scale fleet data collection under human supervision, plus on‑road software updates pushed broadly across North America. Validation philosophies differ accordingly: Waymo certifies city by city with safety cases; Tesla iterates at continental scale with driver oversight.[^2]

## Chronology of Key Milestones

### Waymo

* **2009 to 2016**: Google self‑driving project initiates; Waymo spun out of Google in 2016. Early demonstrations include a 2015 public road ride with no human driver for a legally blind rider, signaling driverless readiness in controlled contexts.[^5]
* **2018**: Launch of Waymo One in metro Phoenix as a commercial robotaxi service with trained safety operators and limited rider base.[^6]
* **2020**: Opening of fully driverless rides to the public in parts of Phoenix, beginning a true no‑driver commercial service.[^7]
* **2023 to 2024**: California CPUC grants Waymo authority for 24/7 paid driverless service in San Francisco, later approving expansion into parts of Los Angeles and San Mateo County. Waymo begins opening San Francisco access broadly to the public.[^8]
* **2024 to 2025**: Sixth generation hardware announced; the company retires Chrysler Pacifica vans in favor of all‑electric Jaguars. Waymo expands service areas in Phoenix and Los Angeles and initiates access via Uber in Austin and Atlanta.[^9]

### Tesla

* **2016 to 2017**: Elon Musk says Tesla will demonstrate a coast‑to‑coast autonomous drive by late 2017, which does not occur.[^10]
* **2019**: At "Autonomy Day," Musk predicts over 1 million Tesla robotaxis on roads "next year." That deployment does not materialize.[^11]
* **2020**: Limited release of FSD "Beta" for supervised use on city streets begins.[^12]
* **2022**: Wide availability of FSD Beta across North America, with Tesla citing roughly 400,000 participating vehicles.[^13]
* **2023**: NHTSA directs a safety recall of FSD Beta behaviors, prompting over‑the‑air remedial changes.
* **2024**: Tesla rolls out an end‑to‑end neural architecture in FSD v12 and rebrands to "FSD (Supervised)." A 30‑day trial is offered to U.S. owners to boost exposure.[^14]

## Public Claims vs Delivered Functionality

Musk's major public timelines have repeatedly been more aggressive than realized deployments. The 2016 promise of a coast‑to‑coast autonomous trip by 2017 and the 2019 forecast of over 1 million robotaxis by 2020 remain unmet. Tesla, however, has delivered a broad, supervised driver assistance product with iterative capability increases and a national footprint. These features remain Level 2, requiring an attentive human supervisor, and have been subject to regulatory recall and review when safety risks were identified. In parallel, Tesla dropped the "Beta" label in 2024 in favor of "Supervised" to better reflect required driver oversight.[^10]

The delta between claims and delivery is consequential for consumer expectations and policy debates. California's DMV false‑advertising complaint against Tesla regarding Autopilot and FSD marketing survived an early dismissal attempt in 2024, indicating regulators' interest in how automation capabilities are described to the public.[^15]

## Where They Operate Today

Waymo operates paid, no‑driver rides in defined parts of Phoenix metro, San Francisco, and Los Angeles, with service sizes published in updates. In Phoenix, Waymo reported about 315 square miles of service area by mid‑2024. In 2024 to 2025, San Francisco service opened broadly and Los Angeles coverage expanded. Waymo also began offering rides via Uber in limited zones of Austin and Atlanta as it seeds future markets. Reuters recently reported that Waymo is completing more than 1 million paid rides per month across its network.[^16]

Tesla provides supervised city‑street driving features to customer cars broadly across the United States and Canada. In March 2024 Tesla offered a 30‑day trial in the U.S., and independent reporting and Tesla communications have consistently put the North American user base for FSD Beta or Supervised around 400,000 vehicles since early 2023. Unlike Waymo, Tesla's system is not a ride‑hail service and does not operate without a human driver.[^17]

## Regulatory, Technological, and Practical Limits

Waymo's model emphasizes geofenced deployments with progressive regulatory approvals, including CPUC decisions for fare collection and service expansion. The company has issued voluntary software recalls after low‑severity incidents, including collisions with stationary barriers and a bicyclist strike in San Francisco that produced minor injuries, illustrating how safety monitoring and corrective updates are handled in a driverless context. The practical limitation is scalability of HD mapping and operations to new cities, along with community acceptance and policing interfaces in mixed traffic. Waymo's reliance on curated service areas enables high reliability within the operational design domain, but expansion requires time to map, validate, and build local safety cases.[^8]

California disengagement reporting provides one public window into developmental performance. DMV's program requires companies testing in the state to report miles and disengagements annually, although the relevance of these metrics to driverless service remains debated. Public CSVs and independent tallies show that Waymo logged millions of autonomous miles in California while steadily reducing disengagements over time as it approached rider‑only operations. The DMV maintains the official reports and mileage datasets for each year.[^18]

Tesla's system is treated as Level 2 driver assistance in the U.S., which means it must keep an engaged human supervisor at all times. NHTSA's 2023 recall aimed to mitigate specific risky behaviors in FSD Beta, and NHTSA continues oversight of Autopilot and FSD through defect investigations and standing crash reporting orders. In 2024 Tesla renamed the product to FSD (Supervised) and began a national trial to increase adoption. The practical limits of Tesla's approach include performance under poor visibility, the absence of HD maps or non‑visual sensors to provide alternative ranging modalities, and the challenge of winning regulatory approval for unsupervised operation.[^19]

Waymo's sensor‑fusion and HD maps reduce ambiguity and provide redundancy, but impose higher per‑vehicle cost and the operational overhead of mapping and validating each expansion. Tesla's vision‑only generalization reduces dependency on prior mapping and custom sensors, facilitating wide distribution across customer cars, but places greater burden on perception to handle edge cases in adverse conditions. A Reuters analysis characterized Tesla's move to end‑to‑end "black box" models as high potential reward with notable verification and transparency challenges for safety assurance and regulators.[^20]

## Outlook

Waymo's near term roadmap appears focused on deepening density in existing cities, airport connectivity, and broadening access across greater metro regions, often through partnerships such as Uber integration for incremental demand. The company has communicated plans to expand fleet size and service areas, referencing ongoing growth in Los Angeles and Phoenix and the opening of San Francisco access to the general public. Reuters recently reported monthly ride volumes above 1 million, which suggests scale effects may begin to improve unit economics, although high fixed costs and the pace of permitting remain key variables. Continued, periodic software recalls to address discovered edge cases should be expected as part of safety management for a driverless service.[^21]

Tesla's stated trajectory is to increase FSD capability through larger end‑to‑end models trained on more fleet video, deploy improvements through over‑the‑air updates, and eventually transition from supervised to unsupervised operation, likely starting with narrow geofenced domains such as shuttle or robotaxi pilots. The company has worked to grow adoption through pricing changes and free trials and has maintained that camera‑only autonomy can scale globally. The key hurdles are regulatory permission for driverless operation, building externally verifiable safety cases for "black box" models, and demonstrating robust performance in low‑visibility and rare hazards without auxiliary sensing or HD maps. U.S. oversight will continue through NHTSA investigations and any state actions concerning marketing and safety claims, such as California's DMV case.[^17]

Comparative synthesis by topic

* Sensor stack. Waymo uses lidar, radar, and cameras for complementary coverage and redundancy. Tesla uses cameras only, having removed radar and ultrasonic sensors in the transition to Tesla Vision. Waymo's approach is akin to triangulating a position using several instruments; Tesla's is akin to mastering a single instrument with powerful pattern recognition.[^1]

* Mapping. Waymo's HD maps serve as a high fidelity prior that constrains and simplifies online perception and planning within defined geofences. Tesla positions itself as map‑light, aiming to infer environment and rules directly from live video, which theoretically scales faster across regions but shifts more burden to perception and policy learning.[^4]

* Software architecture. Waymo uses a modular pipeline with perception, prediction, and planning components validated against maps and extensive simulation. Tesla has migrated to end‑to‑end neural networks that directly learn control from fleet video, reducing hand‑coded logic. The verification challenge differs: Waymo validates modules and their integration against a known map and simulation suite; Tesla validates emergent behaviors learned from data at scale.[^2]

* Operational model. Waymo operates driverless ride‑hail with permits, safety cases, and staged expansion. Tesla sells a supervised feature to individual owners, allowing continent‑wide exposure but keeping the human as fallback. This leads to different real‑world data: Waymo can measure driverless service reliability and ride outcomes; Tesla measures supervised intervention rates and disengagements by customers that remain legally responsible for driving.[^8]

* Scale and footprint. Waymo is live, driverless, in parts of Phoenix, San Francisco, and Los Angeles, and is piloting through Uber in Austin and Atlanta, reporting over 1 million monthly rides. Tesla's FSD (Supervised) is widely available across North America, with an estimated hundreds of thousands of cars having access, supported by a U.S. 30‑day trial to increase usage.[^21]

* Safety and regulation. Waymo has filed voluntary software recalls to correct specific failure modes and interacts with CPUC and local agencies as it expands service areas. Tesla's FSD and Autopilot are subjects of NHTSA reviews and recalls, including a large 2023 FSD Beta remedy and ongoing investigative work related to driver monitoring and crash reporting. California's DMV marketing case underscores the scrutiny around claims and naming. Both companies operate under evolving federal and state frameworks that are tightening around autonomous and semi‑autonomous claims.[^22]

Key concepts explained with intuitive examples

* End‑to‑end neural network. Instead of a pipeline of separate modules with explicit rules, the system learns to go from video to steering and pedals in one learned model, similar to how a human learns to drive by feel from experience rather than consulting a stepwise checklist. This is Tesla's stated approach in FSD v12.[^14]

* HD map. A machine‑readable atlas containing detailed lane geometry, curb positions, and traffic signal locations, which lets the autonomy system know the expected layout before it sees it, much like a pilot's approach plate. Waymo localizes to this map for context and consistency.[^4]

* Simulation. A synthetic driving world that can replay real incidents and generate variations to probe rare hazards, comparable to a flight simulator's stress drills. Waymo uses Simulation City and Carcraft to test software changes comprehensively before release.[^2]

* Disengagement. A handover from the automated system to a human or a remote operator during testing. Disengagement rates provide one lens on developmental maturity, though they are sensitive to test policies and not directly comparable across companies or to driverless service performance. California's DMV publishes these reports annually.[^18]

Risks to scaling

Waymo's primary risks are the capital and operational intensity of expanding HD maps and depots to new metros, the necessity to obtain local operating permissions, and the need to maintain public trust during incidents and recalls. Each new city requires mapping, simulation‑based validation, and staged pilot programs. However, once established, Waymo can offer a driverless product with full fare collection and growing monthly volume, which supports a service business model.[^8]

Tesla's primary risks are regulatory acceptance of unsupervised operation with a vision‑only, end‑to‑end model, explainability and auditability of black‑box behaviors, and robustness under adverse weather and rare hazards without sensor redundancy. In the near term, Tesla's offering remains a supervised convenience feature, subject to safety recalls and investigations. Transitioning to driverless operation would require city‑by‑city permissions or a new federal framework and credible third‑party safety evidence.[^20]

Bottom line

* Waymo today operates true driverless robotaxi fleets at commercial scale in selected U.S. cities, enabled by a conservative, sensor‑heavy, map‑anchored approach and a city‑specific regulatory strategy. The model is slower to expand but yields fully driverless service once established. Recent reports put total monthly rides above 1 million across markets.[^21]

* Tesla today offers a widely distributed, supervised system for private owners in North America using camera‑only perception and end‑to‑end learning. The model scales quickly in coverage and data but remains Level 2, guided by driver oversight and ongoing regulatory scrutiny. The company's public timelines for unsupervised robotaxi service have historically been optimistic relative to delivered functionality, and future progress will hinge on safety validation evidence acceptable to regulators.[^17]

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
