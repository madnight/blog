---
title: Efficiently Updatable Neural Network (NNUE)
date: 2025-10-07
tags: ["artificial intelligence", "chess", "neural networks"]
subtitle: Development of Neural Network Chess Engines
categories:
  - Computer Science
---

<audio controls>
  <source src="/audio/twistor.mp3" type="audio/mpeg">
  Your browser does not support the audio element.
</audio>

## Origins and Development of NNUE in Chess Engines

The Efficiently Updatable Neural Network (NNUE) originated in the Japanese computer shogi community. It was invented in 2018 by Yu Nasu, who introduced this neural-network-based evaluation approach to shogi as a replacement for traditional handcrafted evaluation functions[^1]. The name "NNUE" is a Japanese wordplay on Nue (a mythical chimera), and it is sometimes stylized as "ƎUИИ". In shogi engines (notably in adaptations of the open-source engine YaneuraOu), NNUE proved remarkably strong – reportedly reaching play on par with DeepMind's AlphaZero in that domain[^2]. The NNUE concept built on earlier ideas like piece-square tables indexed by king location (an idea used in Kunihito Hoki's shogi engine Bonanza), extending them with a neural network that could learn complex piece interactions[^3]. In essence, NNUE provided a way to combine the efficiency of classical evaluation tables with the flexibility of machine-learned patterns.

After its success in shogi, NNUE was soon applied to chess. A Japanese programmer Hisayori "Nodchip" Noda ported NNUE into a development version of the chess engine Stockfish in early 2020 as a proof of concept[^4]. This prototype, dubbed Stockfish NNUE, quickly demonstrated dramatically improved playing strength despite some reduction in raw search speed[^5]. The chess community took note in the summer of 2020, as Stockfish with NNUE began to significantly outperform the conventional Stockfish that used a purely hand-crafted evaluation. On August 6, 2020, the Stockfish team officially merged NNUE into the engine; the resulting release (Stockfish 12) showed a major increase in playing strength over previous versions[^6]. This marked the first time a top chess engine successfully integrated a neural network evaluation running efficiently on CPU. The elo gain was on the order of 80–100 points in engine testing – a huge leap in a field where progress is often incremental[^7][^8].

The adoption of NNUE in Stockfish sparked a broader revolution in computer chess. Many other engine developers quickly experimented with NNUE in their own programs, attracted by the method's strength and the relatively small implementation effort required[^9]. Engines such as Komodo (Dragon), Ethereal, Igel, Scorpio, and various Stockfish derivatives all added NNUE-based evaluations in late 2020 and 2021[^10][^11]. Even commercial products like Fat Fritz 2 (by ChessBase) leveraged Stockfish's NNUE code with customized networks. In a matter of months, efficiently updatable neural nets became the new standard for top engines, largely replacing the decades-long era of handcrafted evaluation functions in classical alpha-beta search engines.

It is worth noting the key contributors in this development. Yu Nasu's original NNUE research laid the groundwork[^12]. The Stockfish integration was enabled by Noda (nodchip) and other collaborators in the open-source community, with support from shogi-engine authors (the Stockfish blog credits "nodchip, ynasu87, yaneurao (initial port and NNUE authors)" among others)[^13]. Early trained networks for chess were produced by community members like gekkehenker and sergiovieri, whose nets were used as defaults in Stockfish 12[^14][^15]. This collaborative, cross-community effort was a prime example of knowledge transfer from computer shogi to chess. By 2021, Stockfish NNUE decisively won the Top Chess Engine Championship (TCEC), and the hybrid of classical search with NNUE evaluation firmly established itself as the strongest engine paradigm.

## Technical Design

At its core, an NNUE is a neural network-based evaluation function used inside a chess engine's search. Unlike the deep convolutional networks used by systems like AlphaZero or Leela Chess Zero, an NNUE is typically a fully-connected network with a relatively small number of layers. A common architecture (as used in early NNUE for chess) consisted of an input layer feeding into one or two hidden layers, and an output neuron that produces the evaluation score of a position[^16]. For example, one basic NNUE design has an input vector of length 768 (representing board features), a hidden layer of an arbitrary size (often on the order of a few thousand neurons), and then an output layer that yields a single scalar score[^17]. The network uses standard nonlinear activation functions (the original NNUE used ReLU or its clipped variants) to introduce non-linearity[^18]. Notably, the inputs to NNUE are hand-engineered feature indices rather than raw pixels or raw board matrices. In chess, these inputs are derived from piece-square tables – essentially indicators for specific piece types on specific squares, possibly differentiated by the king's location or side to move[^19]. This structured input leverages domain knowledge (like classical evaluation terms) in a way that is amenable to neural processing.

The defining feature of NNUE's design is captured in the name "efficiently updatable." The network is structured to exploit the fact that consecutive chess positions (during a search) differ only by a small number of piece moves. Therefore, instead of recomputing the entire network from scratch for each position, NNUE maintains an accumulator for the first hidden layer that can be incrementally updated when a move is made or unmade[^20]. In practice, this means when a piece moves, only a few input neurons change (for a typical quiet move, two input neurons change state; for a capture or castling, maybe three or four inputs change)[^21]. The contribution of those changed inputs to the hidden layer is added or subtracted from the accumulator, while unaffected neurons retain their previous values[^22]. This technique avoids a full recomputation of the hidden layer on every node of the search tree. After updating the first layer incrementally, the subsequent layers (from the hidden layer to output) are small enough to compute from scratch very quickly. This incremental computation is what allows NNUE to be used within a high-speed alpha-beta search without crippling the engine's nodes-per-second – a critical requirement that earlier large neural networks could not meet.

To achieve maximum efficiency on standard CPUs, NNUE implementations use low-precision arithmetic and vectorized instructions. The networks are typically quantized to use integers (e.g. 8-bit or 16-bit weights) instead of 32-bit floats[^23]. Stockfish's NNUE, for instance, stores the first-layer weights as 16-bit and later layers as 8-bit values[^24]. The arithmetic is then optimized with SIMD (Single Instruction, Multiple Data) operations, taking advantage of CPU instruction sets to compute many neuron contributions in parallel[^25]. These optimizations, combined with the accumulator design, allow NNUE to evaluate millions of positions per second on a CPU, only modestly slower than classical evaluation code. By contrast, a typical deep neural net like Leela Chess Zero's requires a GPU for fast inference due to its size and complexity[^26]. In summary, the NNUE design marries a simple fully-connected neural network with clever engineering (feature-based inputs, incremental updates, and quantized SIMD computation) to create a fast and strong evaluation function suitable for classical search engines.

## Principles and Comparison with Traditional Neural Networks

The fundamental principle behind NNUE is leveraging small state changes for efficient evaluation updates. Traditional neural networks used in chess (such as the deep residual networks in Leela Chess Zero (LC0) or Google DeepMind's AlphaZero) treat each position independently – they input the entire board state (often as a multi-plane matrix encoding piece locations or probabilities) into a large network and compute an evaluation (and in LC0's case, also move probabilities) from scratch. NNUE differs in several key ways:

**Handcrafted Input Features vs Raw Inputs**: NNUE uses a structured input encoding (piece-square indices, often split by side-to-move or king proximity) which is sparse and based on domain-specific features[^27]. Each input neuron might correspond to something like "white knight on F3" or "black queen on D8 with white king on G1" in some formulations. Only those neurons corresponding to pieces actually present on the board are active. In contrast, LC0's network takes a complete board representation (e.g. 8×8×N binary planes or other similar encodings) without such explicit feature indexing. NNUE's input design thus embeds chess knowledge into the network's structure, whereas LC0's deep net learns from more generic representations.

**Shallower Network, Fewer Parameters**: NNUE networks are relatively shallow (commonly 3 or 4 layers in total as noted above) and have on the order of a few million weights[^28]. LC0's neural net by comparison is a deep residual network with dozens of layers and tens of millions of weights, requiring far more computation. The NNUE's simplicity is a trade-off made to ensure it can run quickly on CPU. The "efficiently updatable" property only strictly applies to the first layer (since once a non-linear activation is applied, reusing intermediate values further in the network is not straightforward)[^29]. In practice, Stockfish's search updates the first hidden layer via the accumulator and then computes the remaining layers fresh[^30][^31]. Deep networks like LC0 do not have any concept of incremental update; every evaluation is a full forward-pass through the entire network. This makes them far slower per position – LC0 compensates by evaluating fewer positions using intelligent Monte Carlo Tree Search, guided by the network's policy outputs.

**Training Methodology**: The way NNUE networks are trained also differs from reinforcement learning approaches used by AlphaZero/Leela. NNUE networks for chess have typically been trained in a supervised manner using annotated position data. In fact, the initial Stockfish NNUE was trained on "the evaluations of millions of positions at moderate search depth"[^32]. In other words, millions of chess positions were evaluated with classical Stockfish (or an engine) at some depth, and those evaluation scores became training targets for the neural net. This process is akin to knowledge distillation – the network learns to predict the engine's own evaluation. This provided a huge training set without needing self-play from scratch. Subsequent networks have also incorporated reinforcement learning elements or self-play data to further improve: for example, developers experimented with letting engines using NNUE play games against each other or against classical engines to generate new training data, thus blending supervised and reinforcement learning[^33]. By contrast, Leela Chess Zero's nets are trained via pure reinforcement learning from self-play games (starting from random play and gradually improving), guided by game outcomes and the AlphaZero-style algorithms. In summary, NNUE training tends to use existing chess knowledge or engine analysis as a teacher, whereas LC0 learns by playing millions of games to tune its weights.

**Integration with Search**: Both NNUE-based engines and Leela/AlphaZero ultimately combine neural evaluations with search, but the search paradigms differ. Stockfish with NNUE continues to use alpha-beta pruning and related deterministic search techniques, examining huge game trees with the NNUE providing static scores at leaf nodes (and sometimes mid-search for pruning heuristics)[^34]. Leela's approach uses Monte Carlo Tree Search (MCTS) guided by neural net outputs (both value and policy), which means it investigates fewer positions but in a probabilistic, policy-driven way[^35]. For a user, one practical difference is that Stockfish NNUE still provides deterministic principal variation lines and numeric scores in centipawns, while Leela's evaluations come as win probabilities and its move choice may appear more "strategic" due to the policy guidance. In terms of output, NNUE yields only a single evaluation number (how favorable the position is for a side)[^36], whereas Leela's network produces both an evaluation and a probability distribution over moves (this distribution is used to bias the search towards promising moves). Despite these differences, at a high level NNUE and Leela's net share the role of replacing manual evaluation heuristics with learned knowledge. Modern Stockfish (as of 2023–2025) even incorporated some ideas from deep learning world by using multiple embedded nets or larger nets (up to two hidden layers, etc.) as long as they remain efficient[^37][^38].

In summary, NNUE can be seen as a hybrid approach: it injects a neural network into a classical engine, preserving the efficient search algorithm. Leela Chess Zero represents the end-to-end neural approach, using a big neural net to evaluate positions (and suggest moves) with a different style of search. Both approaches have yielded top-tier performance, but they differ in resource needs and style. Notably, NNUE's big advantage is that it runs on CPU and slots into existing chess engines, whereas LC0 typically needs GPU acceleration to reach its full potential[^39]. This difference in hardware reliance is a direct outcome of the design philosophy behind NNUE – to be lightweight enough for CPU inference.

### NNUE vs. Leela Chess Zero

**Pros of NNUE approach**: It can leverage extremely fast alpha-beta search; Stockfish NNUE examines far more nodes per second than Leela can, which means it won't miss brute-force wins (e.g. long tactical sequences) as easily. It also runs on commodity CPUs without needing a high-end GPU – very practical for most users or for running on servers. Additionally, the hybrid approach benefited from decades of search optimizations (pruning, move ordering, endgame tablebases, etc.), which were all retained. In engine-vs-engine play, Stockfish NNUE has maintained an edge in strength over LC0 in most settings, especially when each is on its "ideal" hardware (Stockfish on CPU cluster vs Leela on GPU cluster)[^45][^46]. This suggests the combination of deep search and a decent neural eval is a potent mix.

**Cons or differences of NNUE vs Leela**: Leela's approach has an intrinsic elegance – the neural network learns everything (evaluation and move preferences) from scratch, potentially noticing long-term strategic plans more naturally. LC0's evaluations are on a scale of win probabilities, which sometimes align better with practical game outcomes (whereas NNUE's centipawn scores are not directly probabilities). In some types of positions, especially those requiring nuanced judgment without deep calculation (say fortress scenarios or long-term sacrifices), Leela's policy-driven search can sometimes find moves that the brute-force approach might overlook until very deep. Another aspect is that Leela's network, being larger, might encode patterns (like complex positional themes) that a smaller NNUE might not capture unless explicitly present in training data. From a development perspective, the LC0 style also opens research into new network architectures (e.g. transformers, as some works suggest[^47]), whereas NNUE is relatively constrained by needing to remain small and updatable. Finally, LC0's use of GPU hardware means it can scale with improved hardware (bigger and faster GPUs can directly accelerate it), whereas scaling Stockfish beyond a point yields diminishing returns due to memory and parallel search limits. In summary, NNUE's approach is more pragmatic and engineered for immediate strength, while Leela's is more holistic, potentially offering insights into chess that a brute-force engine might not find as intuitively.

## Grandmasters' Perspectives on Neural-Network Engines

The rise of NNUE and neural-network engines has not only impacted computer chess competitions but also influenced top human players and their preparation. Elite grandmasters have closely followed these developments and often commented on them:

Magnus Carlsen has expressed great interest in neural net engines. In fact, he was quick to incorporate Leela Chess Zero into his analytical toolkit. In a 2021 Norwegian interview, Carlsen noted that he started using Leela "very quickly, before all of his competitors did," and he partially credited this early adoption for one of the best performance periods of his career[^48]. This indicates that Carlsen gained practical insights or novelties from Leela's style of analysis that others hadn't yet accessed. He has also been inspired by AlphaZero's games – Carlsen remarked that AlphaZero's willingness to sacrifice material for long-term advantages was fascinating, and it offered a "different perspective" on the game that influenced his own play[^49][^50]. In interviews, Carlsen described being "hugely inspired" by the creative, sometimes "alien" strategies shown by neural network engines, suggesting that studying these engines helped him evolve his style. It's telling that the World Champion's team in recent years uses a mix of traditional engines and neural nets for preparation. For example, during the 2018 World Championship match, both Carlsen's and challenger Fabiano Caruana's teams made use of Leela Chess Zero for opening preparation, even though Leela at the time was still relatively weak in some technical positions[^51]. Caruana noted that in 2018 "nobody was really using Leela then" but they decided to try it, and while it had endgame weaknesses and occasional tactical blind spots, "it was also helpful in preparation"[^52]. This early use by top players underscores the value of Leela's unique "human-like" ideas, which could complement the brute-force analysis of engines like Stockfish.

Hikaru Nakamura has also engaged with neural-net engines, both in analysis and even in exhibition matches. He played a public match against Leela Chess Zero (receiving knight odds) in 2020, which showcased the engine's strength even with a material handicap. Nakamura, known for his pragmatic and sometimes skeptical view on hype, essentially recognized that neural net engines brought something new to the table. In a later interview, he mentioned that engines like Leela and AlphaZero introduced ideas that "completely changed the way top players analyze certain positions," especially in terms of dynamic sacrifices and pawn structure strategies. Like many of his peers, Nakamura uses engines extensively in his game preparation and has adapted to the "new wisdom" they provide – for instance, being more willing to consider long-term piece sacrifices that classical engines used to undervalue.

Garry Kasparov, who famously was the first world champion defeated by a computer (Deep Blue in 1997), has spoken very positively about the new generation of AI engines. He called AlphaZero's style "a pleasure to watch," noting that unlike the old brute-force machines, AlphaZero played "very aggressive, creative" chess[^55]. Kasparov was struck by how the machine's play "sounds rather human" in its qualities – a testament to how neural nets brought a form of intuition to computer chess[^56]. He labeled AlphaZero's emergence a "real breakthrough" and has since advocated that humans should learn from these AI. Kasparov's endorsement is significant: after initially feeling bitter about computers, he now embraces the neural net engines as tools that push chess understanding forward and even as analogies for broader AI potential.

Players like Vishwanathan Anand and Fabiano Caruana have also discussed how the engine landscape changed around 2018–2020. Caruana mentioned that the "rate of improvement [in engines] is amazing" and that by 2021 the level of preparation with engines had become astronomically high[^58]. He noted that mistakes in analysis that might have occurred a few years ago "would never happen, three years later" because the neural-net-enhanced engines "spot it instantly"[^59][^60]. This underscores that modern engines (Stockfish NNUE, Leela, etc.) have improved so much that top humans rely on them to double-check every line. Ding Liren and Ian Nepomniachtchi, who contested the 2023 World Championship, both prepared with a combination of Stockfish (with NNUE) and Leela, often cross-verifying critical positions with both types of engines to gather diverse insights.

In practical terms, neural network engines have influenced top GMs in areas like opening preparation and positional understanding. AI chess engines introduced a wealth of unorthodox opening ideas, some lines once considered dubious were found to be playable thanks to deep neural eval, and vice versa. For instance, neural nets often favor dynamic piece activity over material, leading to a re-examination of gambit lines or long-term sacrifices. Grandmasters have incorporated many of these engine-approved ideas into their repertoires. Additionally, studying the games played between Stockfish and Leela (in events like TCEC) has become a way for GMs to enrich their intuition. As one article noted, "every serious chess player — amateur or professional — studies the games of these engines to expand their understanding."[^61] This sentiment is widely shared: the engine "sparring partners" are simply too strong and insightful to ignore.

## Conclusion

The Efficiently Updatable Neural Network (NNUE) represents a revolutionary advancement in computer chess that successfully bridged the gap between classical search algorithms and modern neural network technology. By combining the efficiency of traditional alpha-beta search with the pattern recognition capabilities of neural networks, NNUE created a new paradigm that has fundamentally transformed the landscape of chess engines.

The success of NNUE demonstrates the power of hybrid approaches in artificial intelligence. Rather than replacing classical methods entirely, NNUE enhanced them by providing more sophisticated evaluation functions that could learn from vast amounts of data while maintaining the computational efficiency required for deep search. This approach proved so effective that it quickly became the standard for top chess engines, marking the end of the era of purely handcrafted evaluation functions.

The impact of NNUE extends beyond mere technical achievement. It has influenced how top human players approach chess preparation and analysis, creating a symbiotic relationship between human creativity and machine intelligence. Grandmasters like Magnus Carlsen have embraced these tools, finding inspiration in the novel strategies and insights that neural networks can provide.

Looking forward, NNUE represents just the beginning of what's possible when combining classical algorithms with modern machine learning techniques. The principles developed for NNUE—efficient incremental updates, quantized networks, and hybrid architectures—have applications far beyond chess, potentially influencing other domains where real-time decision making requires both speed and sophistication.

The story of NNUE is ultimately one of collaboration and innovation, showing how ideas from different communities (Japanese shogi programmers, open-source chess developers, and machine learning researchers) can come together to create something greater than the sum of its parts. As we continue to explore the intersection of classical algorithms and neural networks, NNUE stands as a testament to the power of thoughtful engineering and the potential for AI to enhance rather than replace human capabilities.

## References

[^1]: Wikipedia contributors. "Efficiently updatable neural network." Wikipedia, The Free Encyclopedia. https://en.wikipedia.org/wiki/Efficiently_updatable_neural_network

[^2]: ChessProgramming Wiki. "NNUE." https://www.chessprogramming.org/NNUE

[^3]: ChessProgramming Wiki. "NNUE." https://www.chessprogramming.org/NNUE

[^4]: ChessProgramming Wiki. "NNUE." https://www.chessprogramming.org/NNUE

[^5]: ChessProgramming Wiki. "NNUE." https://www.chessprogramming.org/NNUE

[^6]: Wikipedia contributors. "Efficiently updatable neural network." Wikipedia, The Free Encyclopedia. https://en.wikipedia.org/wiki/Efficiently_updatable_neural_network

[^7]: Stockfish Chess. "Stockfish 12." https://stockfishchess.org/

[^8]: Stockfish Chess. "Stockfish 12." https://stockfishchess.org/

[^9]: ChessProgramming Wiki. "NNUE." https://www.chessprogramming.org/NNUE

[^10]: ChessProgramming Wiki. "NNUE." https://www.chessprogramming.org/NNUE

[^11]: ChessProgramming Wiki. "NNUE." https://www.chessprogramming.org/NNUE

[^12]: Wikipedia contributors. "Efficiently updatable neural network." Wikipedia, The Free Encyclopedia. https://en.wikipedia.org/wiki/Efficiently_updatable_neural_network

[^13]: Stockfish Chess. "Stockfish 12." https://stockfishchess.org/

[^14]: Stockfish Chess. "Stockfish 12." https://stockfishchess.org/

[^15]: Stockfish Chess. "Stockfish 12." https://stockfishchess.org/

[^16]: ChessProgramming Wiki. "NNUE." https://www.chessprogramming.org/NNUE

[^17]: ChessProgramming Wiki. "NNUE." https://www.chessprogramming.org/NNUE

[^18]: Wikipedia contributors. "Efficiently updatable neural network." Wikipedia, The Free Encyclopedia. https://en.wikipedia.org/wiki/Efficiently_updatable_neural_network

[^19]: Wikipedia contributors. "Efficiently updatable neural network." Wikipedia, The Free Encyclopedia. https://en.wikipedia.org/wiki/Efficiently_updatable_neural_network

[^20]: ChessProgramming Wiki. "NNUE." https://www.chessprogramming.org/NNUE

[^21]: ChessProgramming Wiki. "NNUE." https://www.chessprogramming.org/NNUE

[^22]: ChessProgramming Wiki. "NNUE." https://www.chessprogramming.org/NNUE

[^23]: Wikipedia contributors. "Efficiently updatable neural network." Wikipedia, The Free Encyclopedia. https://en.wikipedia.org/wiki/Efficiently_updatable_neural_network

[^24]: Wikipedia contributors. "Efficiently updatable neural network." Wikipedia, The Free Encyclopedia. https://en.wikipedia.org/wiki/Efficiently_updatable_neural_network

[^25]: Wikipedia contributors. "Efficiently updatable neural network." Wikipedia, The Free Encyclopedia. https://en.wikipedia.org/wiki/Efficiently_updatable_neural_network

[^26]: Wikipedia contributors. "Efficiently updatable neural network." Wikipedia, The Free Encyclopedia. https://en.wikipedia.org/wiki/Efficiently_updatable_neural_network

[^27]: Wikipedia contributors. "Efficiently updatable neural network." Wikipedia, The Free Encyclopedia. https://en.wikipedia.org/wiki/Efficiently_updatable_neural_network

[^28]: Wikipedia contributors. "Efficiently updatable neural network." Wikipedia, The Free Encyclopedia. https://en.wikipedia.org/wiki/Efficiently_updatable_neural_network

[^29]: ChessProgramming Wiki. "NNUE." https://www.chessprogramming.org/NNUE

[^30]: ChessProgramming Wiki. "NNUE." https://www.chessprogramming.org/NNUE

[^31]: ChessProgramming Wiki. "NNUE." https://www.chessprogramming.org/NNUE

[^32]: Stockfish Chess. "Stockfish 12." https://stockfishchess.org/

[^33]: ChessProgramming Wiki. "NNUE." https://www.chessprogramming.org/NNUE

[^34]: Stockfish Chess. "Stockfish 12." https://stockfishchess.org/

[^35]: ChessWorld.net. "Leela Chess Zero." https://chessworld.net/

[^36]: ChessProgramming Wiki. "NNUE." https://www.chessprogramming.org/NNUE

[^37]: ChessProgramming Wiki. "NNUE." https://www.chessprogramming.org/NNUE

[^38]: ChessProgramming Wiki. "NNUE." https://www.chessprogramming.org/NNUE

[^39]: Wikipedia contributors. "Efficiently updatable neural network." Wikipedia, The Free Encyclopedia. https://en.wikipedia.org/wiki/Efficiently_updatable_neural_network

[^40]: Stockfish Chess. "Stockfish 12." https://stockfishchess.org/

[^41]: Stockfish Chess. "Stockfish 12." https://stockfishchess.org/

[^42]: Wikipedia contributors. "Efficiently updatable neural network." Wikipedia, The Free Encyclopedia. https://en.wikipedia.org/wiki/Efficiently_updatable_neural_network

[^43]: ChessProgramming Wiki. "NNUE." https://www.chessprogramming.org/NNUE

[^44]: ChessProgramming Wiki. "NNUE." https://www.chessprogramming.org/NNUE

[^45]: ChessWorld.net. "Leela Chess Zero." https://chessworld.net/

[^46]: ChessWorld.net. "Leela Chess Zero." https://chessworld.net/

[^47]: Wikipedia contributors. "Efficiently updatable neural network." Wikipedia, The Free Encyclopedia. https://en.wikipedia.org/wiki/Efficiently_updatable_neural_network

[^48]: Reddit. "Magnus Carlsen on Leela Chess Zero." https://reddit.com/

[^49]: Glasp. "Carlsen on AlphaZero." https://glasp.co/

[^50]: Glasp. "Carlsen on AlphaZero." https://glasp.co/

[^51]: Chess.com. "World Championship Preparation." https://chess.com/

[^52]: Chess.com. "World Championship Preparation." https://chess.com/

[^53]: ChessWorld.net. "Nakamura on AlphaZero." https://chessworld.net/

[^54]: ChessWorld.net. "Nakamura on AlphaZero." https://chessworld.net/

[^55]: The Guardian. "Kasparov on AlphaZero." https://theguardian.com/

[^56]: The Guardian. "Kasparov on AlphaZero." https://theguardian.com/

[^57]: ChessWorld.net. "Peter Heine Nielsen on AlphaZero." https://chessworld.net/

[^58]: Chess.com. "Caruana on Engine Development." https://chess.com/

[^59]: Chess.com. "Caruana on Engine Development." https://chess.com/

[^60]: Chess.com. "Caruana on Engine Development." https://chess.com/

[^61]: ChessWorld.net. "Engine Analysis in Chess." https://chessworld.net/

[^62]: The Guardian. "Kasparov on Machine Creativity." https://theguardian.com/
