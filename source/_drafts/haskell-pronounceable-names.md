---
title: Pronounceable Haskell Operators
date: 2018-08-14
tags: ["haskell", "functional programming", "operators"]
subtitle: Pronounceable Names for Common Haskell Operators
---

This article offers a small collection of haskell operators with some funny names for them. Haskell tutorials and tech speak can sometimes be very dry. True to the motto "Put the fun back into computing" (distrowatch).

<br>

## TIE fighter <*>

<!-- | Package        | Module           | Short Desc  | -->
<!-- | :-------------: |:-------------:| :-----:| -->
<!-- | [base](https://hackage.haskell.org/package/base-4.11.1.0) | [Control.Applicative](https://hackage.haskell.org/package/base-4.11.1.0/docs/Control-Applicative.html#v:-60--42--62-) | Sequential application. | -->
<br>

<img style="float: right;" src="https://upload.wikimedia.org/wikipedia/en/d/d9/TIEfighter.jpg">
<table width="10px">
  <tr>
    <th>Package</th>
    <th>Module</th>
    <th>Describtion</th>
  </tr>
  <tr>
    <td><a href="https://hackage.haskell.org/package/base-4.11.1.0">base</a></td>
    <td><a href="https://hackage.haskell.org/package/base-4.11.1.0/docs/Control-Applicative.html#v:-60--42--62-">Control.Applicative</a></td>
    <td>Sequential application.</td>
  </tr>
</table>


{% raw %}</div>{% endraw %}

**Default implementation:**
`(<*>) :: f (a -> b) -> f a -> f b`
`(<*>) = liftA2 id`

**Example Usage:**

{% raw %}<div style="width: 400px;">{% endraw %}

```haskell
> [(*2)] <*> [1,2,3]
[2,4,6]
```
**Other names: ap, apply**

{% raw %}</div>{% endraw %}

<br><br>

## Wedge-shaped Imperial Star Destroyer <|>
<br>
<img style="width: 300px; float: right;" src="/images/imperial.jpg">

<table width="430px">
  <tr>
    <th>Package</th>
    <th>Module</th>
    <th>Describtion</th>
  </tr>
  <tr>
    <td><a href="https://hackage.haskell.org/package/base-4.11.1.0">base</a></td>
    <td><a href="https://hackage.haskell.org/package/base-4.11.1.0/docs/Control-Applicative.html#v:-60--42--62-">Control.Applicative</a></td>
    <td>An associative binary operation.</td>
  </tr>
</table>

**Default implementation:**
`(<|>) :: f a -> f a -> f a`
`(<|>) = (++)`

**Example Usage:**
```haskell
> [1,2,3] <|> [4,5]
[1,2,3,4,5]
```

**Other names: or, alternative**

<br> <br>

## TIE bomber <**>

<br>

<img style="width: 300px; float: right;" src="/images/tie-bomber.jpg">
<table width="430px">
  <tr>
    <th>Package</th>
    <th>Module</th>
    <th>Desc</th>
  </tr>
  <tr>
    <td><a href="https://hackage.haskell.org/package/base-4.11.1.0">base</a></td>
    <td><a href="https://hackage.haskell.org/package/base-4.11.1.0/docs/Control-Applicative.html#v:-60--42--62-">Control.Applicative</a></td>
    <td>A variant of <*> with the arguments reversed.</td>
  </tr>
</table>

**Default Implementation:**
`(<**>) :: f a -> f (a -> b) -> f b`
`(<**>) = liftA2 (\a f -> f a)`

**Example:**
```haskell
> [1,2,3] <**> [(*2)]
[2,4,6]
```

<br> <br>

## Right fish >=>
<img style="width: 300px; float: right;" src="/images/right-fish.gif">

<table width="10px">
  <tr>
    <th>Package</th>
    <th>Module</th>
    <th>Describtion</th>
  </tr>
  <tr>
    <td><a href="https://hackage.haskell.org/package/base-4.11.1.0">base</a></td>
    <td><a href="http://hackage.haskell.org/package/base-4.11.1.0/docs/Control-Monad.html#v:-62--61--62-">Control.Monad</a></td>
    <td>Left-to-right Kleisli composition of monads.
    </td>
  </tr>
</table>

**Default Implementation:**
`(>=>)       :: Monad m => (a -> m b) -> (b -> m c) -> (a -> m c)`
`f >=> g     = \x -> f x >>= g`

**Example Usage:**
```haskell
> (pure . (2 +)) >=> (pure . (3 *)) $ 2
12
```


<br> <br>

## Left fish <=<

<img style="width: 300px; float: right;" src="/images/left-fish.gif">

<table width="10px">
  <tr>
    <th>Package</th>
    <th>Module</th>
    <th>Describtion</th>
  </tr>
  <tr>
    <td><a href="https://hackage.haskell.org/package/base-4.11.1.0">base</a></td>
    <td><a href="http://hackage.haskell.org/package/base-4.11.1.0/docs/Control-Monad.html#v:-60--61--60-">Control.Monad</a></td>
    <td>(>=>), with the arguments flipped.</td>
  </tr>
</table>

`(<=<)       :: Monad m => (b -> m c) -> (a -> m b) -> (a -> m c)`
`(<=<)       = flip (>=>)`

**Example Usage:**
```haskell
> (pure . (2 +)) >=> (pure . (3 *)) $ 2
12
`


<br> <br> <br> <br> <br> <br> <br> <br>




`(>=>) :: (a -> m b) -> (b -> m c) -> (a -> m c)`
`f >=> g = \x -> f x >>= g`



<br> <br> <br> <br> <br> <br> <br> <br>
# Others

```haskell
>>=     bind
>>      then
*>      then
->      to                a -> b: a to b
<-      bind              (as it desugars to >>=)
<$>     (f)map
<$      map-replace by    0 <$ f: "f map-replace by 0"
<*>     ap(ply)           (as it is the same as Control.Monad.ap)
$                         (none, just as " " [whitespace])
.       pipe to           a . b: "b pipe-to a"
!!      index
!       index / strict    a ! b: "a index b", foo !x: foo strict x
<|>     or / alternative  expr <|> term: "expr or term"
++      concat / plus / append
[]      empty list
:       cons
::      of type / as      f x :: Int: f x of type Int
\       lambda
@       as                go ll@(l:ls): go ll as l cons ls
~       lazy              go ~(a,b): go lazy pair a, b
```


<table width="10px">
  <tr>
    <th>Operator</th>
    <th>Module</th>
    <th>Describtion</th>
  </tr>
  <tr>
    <td><a href="https://hackage.haskell.org/package/base-4.11.1.0">base</a></td>
    <td><a href="https://hackage.haskell.org/package/base-4.11.1.0/docs/Control-Applicative.html#v:-60--42--62-">Control.Applicative</a></td>
    <td>Sequential application.</td>
  </tr>
</table>




<br> <br> <br> <br> <br> <br> <br> <br>
<br> <br> <br> <br> <br> <br> <br> <br>
