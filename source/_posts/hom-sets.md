---
title: Hom-Sets
date: 2020-01-13
tags: ["category theory"]
subtitle: Sets of Morphisms
---

In [category theory](https://en.wikipedia.org/wiki/Category_theory), hom-sets, are sets of [morphisms](https://en.wikipedia.org/wiki/Morphism) between objects. Given objects $A$ and $B$ in a [locally small category](https://en.wikipedia.org/wiki/Category_(mathematics)#Small_and_large_categories), the hom-set $\text{Hom}(A,B)$ is the [set](https://en.wikipedia.org/wiki/Set_(mathematics)) of all morphisms $\{\rightarrow_0,$$\rightarrow_1,$$\rightarrow_2,$$\dots,$$\rightarrow_n\}$ from A to B.
{% raw %}
\begin{xy}
\xymatrix{
A \ar@/^/[r]
  \ar@/^1pc/[r]
  \ar[r]
  \ar@/_/[r]
  \ar@/_1pc/[r]
  &
B
}
\end{xy}
{% endraw %}
Hom-sets itself give rise to another category where hom-sets are objects and arrows between hom-sets are hom-set morphisms. A hom-set morphism is defined as:
$\text{Hom}(A,f) : \text{Hom}(A,B) \rightarrow \text{Hom}(A,D)$, $ f' \rightarrow $ $f \circ {f'}$ for $f : B \rightarrow D$ and
$\text{Hom}(h,B) : \text{Hom}(A,B) \rightarrow \text{Hom}(C,B)$, $ h' \rightarrow $ $h' \circ {h}$ for $h : C \rightarrow A$
such that the following [diagram commutes](https://en.wikipedia.org/wiki/Commutative_diagram):

{% raw %}
\begin{xy}
\xymatrix@!C=4.0cm@!R=1.0cm{
\text{Hom}(A,B) \ar[dr]|-{\text{Hom}(h,f)} \ar[d]_{\text{Hom}(A,f)} \ar[r]^{\text{Hom}(h,B)} &
\text{Hom}(C,B) \ar[d]^{Hom(C,f)} \\
\text{Hom}(A,D) \ar[r]_{\text{Hom}(h,D)} & \text{Hom}(C,D)
}
\end{xy}
{% endraw %}

This can be translated to [Hask](https://wiki.haskell.org/Hask), the category with Haskell types as objects and functions as morphisms, in a straight forward manner. The previous morphisms $f,h$ are now functions `f :: b -> d`, `h :: c -> a` and $\text{Hom}(A,B) = a \rightarrow$ b, such that:

{% raw %}
\begin{xy}
\xymatrix@!C=4.0cm@!R=1.0cm{
a \rightarrow b \ar[dr]|-{c\ \rightarrow\ a\ \rightarrow\ b\ \rightarrow\ d} \ar[d]_{a\ \rightarrow\ b\ \rightarrow\ d} \ar[r]^{c\ \rightarrow\ a\ \rightarrow\ b} &
c \rightarrow b \ar[d]^{c\ \rightarrow\ b\ \rightarrow\ d} \\
a \rightarrow d \ar[r]_{c\ \rightarrow\ a\ \rightarrow\ d} & c \rightarrow d
}
\end{xy}
{% endraw %}

Let's have a closer look at the morphism from $a \rightarrow b$ and $c \rightarrow b$. So we have a $a \rightarrow b$ and a morphisms that tells us we can go from $c \rightarrow a \rightarrow b$ resulting in $c \rightarrow b$. Now, this makes sense if we remember how function composition works:

{% raw %}
\begin{xy}
\xymatrix {
  c \ar[r]^{f'} \ar[dr]_{g' \circ {f'}} &
  a \ar[d]^{g'} & \\ & b &&&&&
}
\end{xy}
{% endraw %}

We can see that $c \rightarrow b$ is the function composition $g' \circ {f'}$. Thus, a hom-set morphism $\text{Hom}(f,-)$ is simply morphism pre-composition $f \circ -$ and $\text{Hom}(-,f)$ is just morphism post-composition $- \circ f$. Furthermore, $\text{Hom}(A,-)$, which you can think of as $A \rightarrow$, is called a [covariant hom-functor](https://en.wikipedia.org/wiki/Functor#Covariance_and_contravariance) or [representable functor](https://en.wikipedia.org/wiki/Representable_functor)  from the category $C$ to the category $Set$, $x \rightarrow \text{Hom}_C(A,x)$ with $x \in C$ and $\text{Hom}_C(A,x) \in Set$. When the second position is fixed $\text{Hom}(-,B): C^{op} \rightarrow Set$ (or $\rightarrow B$) then it's called a contravariant functor. Consequently, if non of the arguments of the hom-functor is fixed $\text{Hom}(−,−): C^{op} \times C \rightarrow Set$ then we have a hom [bifunctor](https://en.wikipedia.org/wiki/Functor#Bifunctors_and_multifunctors) also called [profunctor](https://en.wikipedia.org/wiki/Profunctor), see for instance the diagonal arrow $\text{Hom}(h,f)$ with pre- **and** post-composition.
