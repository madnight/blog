---
title: Monad
date: 2023-07-25
tags: ["category theory"]
subtitle: A Monoid in the Category of Endofunctors
mathjax: true
---


{% raw %}
<script>
  MathJax = {
    loader: {
      load: ['[custom]/xypic.js'],
      paths: {custom: 'https://cdn.jsdelivr.net/gh/sonoisa/XyJax-v3@3.0.1/build/'}
    },
    tex: {
      packages: {'[+]': ['xypic']}
    }
  };
</script>

<script id="MathJax-script" async src="https://cdn.jsdelivr.net/npm/mathjax@3.1.4/es5/tex-chtml-full.js"></script>
<!-- <script id="MathJax-script" async src="https://cdn.jsdelivr.net/npm/mathjax@3.1.4/es5/tex-svg-full.js"></script> -->

<script>
window.addEventListener('load', function() {
   document.querySelectorAll("mjx-xypic-object").forEach( (x) => (x.style.color = "var(--darkreader-text--text"));
   document.querySelectorAll("mjx-math > mjx-xypic > svg > g").forEach(x => x.setAttribute("stroke", "var(--darkreader-text--text"))
})
</script>

</style>
{% endraw %}

<br>
<img src="/images/typeclasses.svg" onclick="window.open(this.src)">
<!-- The source as dot is next to image. Compile with: dot -Tsvg typeclasses.dot -o typeclasses.svg -->
<br>

A Monad is a triple $(T, \eta, \mu)$ where:

* $T: \mathcal{C} \rightarrow \mathcal{C}$ is an endofunctor
* $\eta: 1_\mathcal{C} \rightarrow T$ is a natural transformation (the unit)
* $\mu: TT \rightarrow T$ is another natural transformation (the multiplication)

These must satisfy the following coherence conditions, known as the Monad laws:

* $\mu \circ T\mu = \mu \circ \mu T$ (associativity)
* $\mu \circ T\eta = \mu \circ \eta T = 1_T$ (left and right identity)

This means that for any object $X$ in $\mathcal{C}$, we have:

* $\mu_X \circ T(\mu_X) = \mu_X \circ \mu_{T(X)}$ (associativity)
* $\mu_X \circ T(\eta_X) = \mu_X \circ \eta_{T(X)} = id_{T(X)}$ (left and right unit laws)


We can rephrase these conditions using the subsequent commutative diagrams:

{% raw %}
<div class="splitscreen">
  <div class="left">
\begin{xy}
\xymatrix{
  TTT \ar[d]_{\mu T} \ar[r]^{T\mu} & TT \ar[d]^{\mu} \\
  TT \ar[r]_{\mu} & T
}
\end{xy}
  </div>

  <div class="right">
\begin{xy}
\xymatrix{
  T \ar[d]_{\eta T} \ar[r]^{T\eta} \ar@{=}[dr] & TT \ar[d]^{\mu} \\
  TT \ar[r]_{\mu} & T
}
\end{xy}
  </div>
</div>

{% endraw %}

An application of this concept is that monads provide a way to express computations (in terms of morphisms) that include additional structure or side-effects (captured by the endofunctor $T$) in such a way that these computations can be chained together (via the $\mu$ natural transformation) and lifted over the monadic structure (via the $\eta$ natural transformation), and they do so in a way that is consistent (respecting the associativity and unit laws).

# Example

The Monad, by definition, requires us to implement two functions: the unit, which is called return in Haskell, where we just have to lift a value into the Monad (e.g., put a value into a list), and the multiplication `>>` (sequence) or `>>=` (bind). The sequence can be used if you are only interested in collapsing the structure (TT -> T). The bind function can be used if you need to operate on the lifted value before collapsing. This will become clearer in the following examples.

{% vimhl hs %}
-- Haskell Definition of Monad (Interface)
class Monad m where
  -- η : 1c -> T (unit)
  return :: a -> m a

  -- μ : TT -> T (multiplication)
  (>>) :: m a -> m b -> m b
  (>>=) :: m a -> (a -> m b) -> m b

-- An Instance of Monad, the List Monad
instance Monad [] where
  return :: a -> [a]
  return x = [x]

  (>>) :: [a] -> [b] -> [b]
  m >> n = m >>= \_ -> n

  (>>=) :: [a] -> (a -> [b]) -> [b]
  xs >>= f = concat (map f xs)

-- Another Instance, the Maybe Monad
instance Monad Maybe where
  return :: a -> Maybe a
  return x  = Just x

  (>>=) :: Maybe a -> (a -> Maybe b) -> Maybe b
  (>>=) m g = case m of
                 Nothing -> Nothing
                 Just x  -> g x
{% endvimhl %}
All of the above is already implemented in the standard Haskell library, so you can also simply open an interactive Haskell interpreter (ghci) and test the following example use cases.
{% vimhl hs %}
-- Example Usage
ghci> [1,2,3] >>= \x -> [x, x*2]
[1,2,2,4,3,6]

ghci> Just 3 >>= \x -> Just (x*2)
Just 6

-- And here's how to use IO
ghci> putStr "Hello, " >> putStrLn "world!"
Hello, world!

ghci> getLine >>= \line -> putStrLn ("You said: " ++ line ++ "!")
Hi
You said: Hi!
{% endvimhl %}


[^1]: [Monad in ncatlab](https://ncatlab.org/nlab/show/monad#definition)
[^2]: [Typeclassopedia](https://wiki.haskell.org/Typeclassopedia)
