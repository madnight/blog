---
title: Monad
date: 2023-07-25
tags: ["category theory", "abstract algebra", "monads"]
subtitle: A Monoid in the Category of Endofunctors
mathjax: true
---

{% raw %}
<script>
  MathJax = {
    loader: {
      load: ['[custom]/xypic.js'],
      paths: {custom: 'https://beuke.org/js'}
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

This means that for any object $A$ in $\mathcal{C}$, we have:

* $\mu_A \circ T(\mu_A) = \mu_A \circ \mu_{T(A)}$ (associativity)
* $\mu_A \circ T(\eta_A) = \mu_A \circ \eta_{T(A)} = id_{T(A)}$ (left and right unit laws)


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

We can also write down the natural transformations in terms of their components. For each object $A$ of $\mathcal{C}$, the unit is a morphism $\eta_{A} : A \rightarrow T A$, and the multiplication is a morphism $\mu_{A} : T(T A) \rightarrow T A$, such that the following diagrams commute:

{% raw %}
<div class="splitscreen">
  <div class="left">
\begin{xy}
\xymatrix{
  T(T(TA)) \ar[d]_{\mu TA} \ar[r]^{T\mu{(A)}} & T(TA) \ar[d]^{\mu{A}} \\
  T(TA) \ar[r]_{\mu{A}} & TA
}
\end{xy}
  </div>

  <div class="right">
\begin{xy}
\xymatrix{
  TA \ar[d]_{\eta TA} \ar[r]^{T\eta{(A)}} \ar@{=}[dr] & T(TA) \ar[d]^{\mu{A}} \\
  T(TA) \ar[r]_{\mu{A}} & TA
}
\end{xy}
  </div>
</div>
{% endraw %}


An application of this concept is that monads provide a way to express computations (in terms of morphisms) that include additional structure or side-effects (captured by the endofunctor $T$) in such a way that these computations can be chained together (via the $\mu$ natural transformation) and lifted over the monadic structure (via the $\eta$ natural transformation), and they do so in a way that is consistent (respecting the associativity and unit laws).

# Example

The Monad, by definition, requires us to implement two functions: the unit, which is called return in Haskell, where we just have to lift a value into the Monad (e.g., put a value into a list), and the multiplication `join`.

Haskell Definition of Monad (Interface)
{% vimhl hs %}
class Monad m where
  --   ηx : A -> T A (unit)
  return :: a -> m a

  --   μx : T (T A) -> T A (multiplication)
  join   :: m (m a) -> m a
{% endvimhl %}

These have to obey the Monad laws:
<!-- * $\text{join . join }$== $\text{join . fmap join}$  (associativity) -->
<!-- * $\text{join . return }$= $\text{id}$ = $\text{join . fmap return}$  (left and right idenity) -->
<!-- * `join . return  = id = join . fmap return` (left and right identiy) -->
<!-- * `join . join == join . fmap join`  (associativity) -->
{% vimhl hs %}
join . join == join . fmap join           -- associativity
join . return == id == join . fmap return -- left and right identiy
{% endvimhl %}

We can now draw the commutative diagram for the Haskell definition of Monad:

{% raw %}
<div class="splitscreen">
  <div class="left">
\begin{xy}
\xymatrix{
  \text{m(m(m a))} \ar[d]_{\text{fmap join}} \ar[r]^{\text{join}} & \text{m(m a)} \ar[d]^{\text{join}} \\
  \text{m(m a)} \ar[r]_{\text{join}} & \text{m a}
}
\end{xy}
  </div>

  <div class="right">
\begin{xy}
\xymatrix{
  \text{m a} \ar[d]_{\text{fmap return}} \ar[r]^{\text{return}} \ar@{=}[dr] & \text{m(m a)} \ar[d]^{\text{join}} \\
  \text{m(m a)} \ar[r]_{\text{join}} & \text{m a}
}
\end{xy}
  </div>
</div>
{% endraw %}

The definition of a monad given here is equivalent to the one we typically use in Haskell.

{% vimhl hs %}
class Monad m where
  return :: a -> m a
   (>>=) :: m a -> (a -> m b) -> m b
{% endvimhl %}

We can easily define `>>=` with `join` and `fmap`.

{% vimhl hs %}
a >>= f = join (fmap f a)
{% endvimhl %}

This operation is called bind (or is sometimes refered to as flatMap). The bind function can be used if you need to operate on the lifted value before collapsing. We can also translate the other way around and define `join` in terms of `>>=` and `id`:

{% vimhl hs %}
join a = a >>= id
{% endvimhl %}

Hence `join` is bind applied to the identity function. These two constructions are reverse to each other and they translate the monad laws correctly. Now we lets have a look at some concrete examples (instances of Monad).

An Instance of Monad, the List Monad
{% vimhl hs %}
instance Monad [] where
  return :: a -> [a]
  return x = [x]

  (>>=) :: [a] -> (a -> [b]) -> [b]
  xs >>= f = concat (map f xs)
{% endvimhl %}

<!-- {% raw %} -->
<!-- <div class="splitscreen"> -->
<!--   <div class="left"> -->
<!-- \begin{xy} -->
<!-- \xymatrix{ -->
<!--   \texttt{m a} \ar[d]_{\texttt{fmap return}} \ar[r]^{\texttt{return}} \ar@{=}[dr] & \texttt{m (m a)} \ar[d]^{\texttt{join}} \\ -->
<!--   \texttt{m (m a)} \ar[r]_{\texttt{join}} & \texttt{m a} -->
<!-- } -->
<!-- \end{xy} -->

<!-- {% endraw %} -->
<!--   </div> -->
<!--   <div class="right"> -->
<!-- {% raw %} -->
<!-- \begin{xy} -->
<!-- \xymatrix{ -->
<!--   \texttt{[]} \ar[d]_{\texttt{return}} \ar[r]^{\texttt{return}} \ar@{=}[dr] & \texttt{[[]]} \ar[d]^{\texttt{concat}} \\ -->
<!--   \texttt{[[]]} \ar[r]_{\texttt{concat}} & \texttt{[]} -->
<!-- } -->
<!-- \end{xy} -->
<!--   </div> -->
<!-- </div> -->
<!-- {% endraw %} -->

<!-- You may encounter various names for *concat*, such as *flatten* or *flatMap* and *bind* in case we combine concat with map as in the list implementation of >>=. We can lift values into the structure or increase the nested level of the structure by one with *return* and we can reduce one level of the structure with *concat*. -->

Another Instance, the Maybe Monad
{% vimhl hs %}
instance Monad Maybe where
  return :: a -> Maybe a
  return x  = Just x

  (>>=) :: Maybe a -> (a -> Maybe b) -> Maybe b
  (>>=) m g = case m of
                 Nothing -> Nothing
                 Just x  -> g x
{% endvimhl %}

All of the above is already implemented in the standard Haskell library, so you can simply open an interactive Haskell interpreter (ghci) and test the following examples.
{% vimhl hs %}
ghci> [1,2,3] >>= \x -> [x, x*2]
[1,2,2,4,3,6]

ghci> Just 3 >>= \x -> Just (x*2)
Just 6

-- And here's how to use IO
ghci> getLine >>= \line -> putStrLn ("You said: " ++ line ++ "!")
Hi
You said: Hi!
{% endvimhl %}


### References

[^0]: The diagram displayed at the top of this post is a modified version of Brent Yorgey's [Typeclassopedia diagram](https://wiki.haskell.org/File:Typeclassopedia-diagram.png)
[^1]: [Monad in ncatlab](https://ncatlab.org/nlab/show/monad#definition)
[^2]: [Notes on Category Theory by Paolo Perrone](https://arxiv.org/pdf/1912.10642.pdf)
[^3]: [Category theory/Monads](https://wiki.haskell.org/Category_theory/Monads)
