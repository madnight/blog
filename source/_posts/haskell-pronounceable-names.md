---
title: Pronounceable Haskell Operators
date: 2018-08-14
tags: ["haskell", "functional programming", "operators"]
subtitle: Pronounceable Names for Common Haskell Operators
---

(Just a) small collection of Haskell operators with some funny names for them. Haskell tutorials and discussions can sometimes be very dry, so lets "Put the fun back into computing" (distrowatch).

<br>

## TIE fighter <*>

<br>

<img style="width: 300px; float: right;" src="https://upload.wikimedia.org/wikipedia/en/d/d9/TIEfighter.jpg">
<table width="400px">
  <tr>
    <th>Package</th>
    <th>Module</th>
    <th>Description</th>
  </tr>
  <tr>
    <td><a href="https://hackage.haskell.org/package/base-4.11.1.0">base</a></td>
    <td><a href="https://hackage.haskell.org/package/base-4.11.1.0/docs/Control-Applicative.html#v:-60--42--62-">Control.Applicative</a></td>
    <td>Sequential application.</td>
  </tr>
</table>


**Definition:**
`(<*>) :: f (a -> b) -> f a -> f b`
`(<*>) = liftA2 id`

**Example:**

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

<table width="400px">
  <tr>
    <th>Package</th>
    <th>Module</th>
    <th>Description</th>
  </tr>
  <tr>
    <td><a href="https://hackage.haskell.org/package/base-4.11.1.0">base</a></td>
    <td><a href="https://hackage.haskell.org/package/base-4.11.1.0/docs/Control-Applicative.html#v:-60--42--62-">Control.Applicative</a></td>
    <td>Associative binary operation.</td>
  </tr>
</table>

**Definition:**
`(<|>) :: f a -> f a -> f a`
`(<|>) = (++)`

**Example:**

{% raw %}<div style="width: 100%;">{% endraw %}
```haskell
> [1,2,3] <|> [4,5]
[1,2,3,4,5]
```
{% raw %}</div>{% endraw %}

**Other names: or, alternative**

<br> <br>

## TIE bomber <**>

<br>

<img style="width: 300px; float: right;" src="/images/tie-bomber.jpg">
<table width="400px">
  <tr>
    <th>Package</th>
    <th>Module</th>
    <th>Description</th>
  </tr>
  <tr>
    <td><a href="https://hackage.haskell.org/package/base-4.11.1.0">base</a></td>
    <td><a href="https://hackage.haskell.org/package/base-4.11.1.0/docs/Control-Applicative.html#v:-60--42--62-">Control.Applicative</a></td>
    <td>A variant of <*> with arguments reversed.</td>
  </tr>
</table>

**Definition:**
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

<table width="400px">
  <tr>
    <th>Package</th>
    <th>Module</th>
    <th>Description</th>
  </tr>
  <tr>
    <td><a href="https://hackage.haskell.org/package/base-4.11.1.0">base</a></td>
    <td><a href="http://hackage.haskell.org/package/base-4.11.1.0/docs/Control-Monad.html#v:-62--61--62-">Control.Monad</a></td>
    <td>Left-to-right Kleisli composition of monads.
    </td>
  </tr>
</table>

**Definition:**
`(>=>)       :: Monad m => (a -> m b) -> (b -> m c) -> (a -> m c)`
`f >=> g     = \x -> f x >>= g`

**Example:**
```haskell
> (pure . (2 +)) >=> (pure . (3 *)) $ 2
12
```

<br> <br>

## Left fish

<img style="width: 300px; float: right;" src="/images/left-fish.gif">

<table width="400px">
  <tr>
    <th>Package</th>
    <th>Module</th>
    <th>Description</th>
  </tr>
  <tr>
    <td><a href="https://hackage.haskell.org/package/base-4.11.1.0">base</a></td>
    <td><a href="http://hackage.haskell.org/package/base-4.11.1.0/docs/Control-Monad.html#v:-60--61--60-">Control.Monad</a></td>
    <td>(>=>), with arguments flipped.</td>
  </tr>
</table>

`(<=<)       :: Monad m => (b -> m c) -> (a -> m b) -> (a -> m c)`
`(<=<)       = flip (>=>)`

**Example:**
```haskell
> (pure . (2 +)) <=< (pure . (3 *)) $ 2
8
```


<br> <br>

## Right pipe >>>

<img style="width: 300px; float: right;" src="/images/r-pipe.jpg">

<table width="400px">
  <tr>
    <th>Package</th>
    <th>Module</th>
    <th>Description</th>
  </tr>
  <tr>
    <td><a href="https://hackage.haskell.org/package/base-4.11.1.0">base</a></td>
    <td><a href="http://hackage.haskell.org/package/base-4.11.1.0/docs/Control-Category.html#v:-62--62--62-">Control.Category</a></td>
    <td>Left-to-right composition.</td>
  </tr>
</table>


`(>>>) :: cat a b -> cat b c -> cat a c`
`f >>> g = g . f`

**Example:**
```haskell
> ((*2) >>> (+3)) $ 2
7
```

<br> <br>

## Left pipe .

<img style="width: 300px; float: right;" src="/images/l-pipe.jpg">

<table width="400px">
  <tr>
    <th>Package</th>
    <th>Module</th>
    <th>Description</th>
  </tr>
  <tr>
    <td><a href="https://hackage.haskell.org/package/base-4.11.1.0">base</a></td>
    <td><a href="http://hackage.haskell.org/package/base-4.11.1.0/docs/Prelude.html#v:-46-">Prelude</a></td>
    <td>Right-to-left composition.</td>
  </tr>
</table>



**Definition:**
`(.) :: (b -> c) -> (a -> b) -> a -> c`
`(.) f g = \x -> f (g x)`

**Example:**
```haskell
> ((*2) . (+3)) $ 2
10
```

<br> <br>

# Operators and shenanigans without funny names, yet
|Notation|Signature|Description|
|--- |--- |--- |
|>>=|(>>=) :: Monad m => m a -> (a -> m b) -> m b|bind|
|>>|(>>) :: Monad m => m a -> m b -> m b|then|
|->||to|
|<-||bind|
|<$>|(<$>) :: Functor f => (a -> b) -> f a -> f b|fmap|
|<$|(<$) :: Functor f => a -> f b -> f a|map-replace by|
|!!|(!!) :: [a] -> Int -> a|index|
|!||strict|
|++|(++) :: [a] -> [a] -> [a]|concat|
|[]|([]) :: [a]|empty list|
|:|(:) :: a -> [a] -> [a]|cons|
|::||of type|
|\\||lambda|
|@||as|
|~||lazy|

