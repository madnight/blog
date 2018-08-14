---
title: Pronounceable Haskell Operators
date: 2018-08-14
tags: ["haskell", "functional programming", "operators"]
subtitle: Pronounceable Names for Common Haskell Operators
---

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
    <th>Desc</th>
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

<img style="width: 400px; float: right;" src="/images/imperial.jpg">

<br> <br> <br> <br> <br> <br> <br> <br>
<br> <br> <br> <br> <br> <br> <br> <br>


## The TIE bomber <**>

<img style="width: 350px; float: right;" src="/images/tie-bomber.jpg">
<table width="10px">
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

<br> <br> <br> <br> <br> <br> <br> <br>
<br> <br> <br> <br> <br> <br> <br> <br>



## The left fish <=<


<table width="10px">
  <tr>
    <th>Package</th>
    <th>Module</th>
    <th>Desc</th>
  </tr>
  <tr>
    <td><a href="https://hackage.haskell.org/package/base-4.11.1.0">base</a></td>
    <td><a href="https://hackage.haskell.org/package/base-4.11.1.0/docs/Control-Applicative.html#v:-60--42--62-">Control.Applicative</a></td>
    <td>Sequential application.</td>
  </tr>
</table>




<img style="width: 400px; float: right;" src="http://dnr.maryland.gov/fisheries/fishfacts/american_shad.gif">

<br> <br> <br> <br> <br> <br> <br> <br>

## The right fish >=>
<img style="width: 400px; float: right;" src="http://dnr.maryland.gov/fisheries/fishfacts/american_shad.gif">


<br> <br> <br> <br> <br> <br> <br> <br>
<br> <br> <br> <br> <br> <br> <br> <br>
