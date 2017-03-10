---
title     : "Maps: Total and Partial Maps"
layout    : page
permalink : /Maps
---

# Maps: Total and Partial Maps

Maps (or dictionaries) are ubiquitous data structures, both in
software construction generally and in the theory of programming
languages in particular; we're going to need them in many places in
the coming chapters.  They also make a nice case study using ideas
we've seen in previous chapters, including building data structures
out of higher-order functions (from [Basics](sf/Basics.html)
and [Poly](sf/Poly.html) and the use of reflection to streamline
proofs (from [IndProp](sf/IndProp.html).

We'll define two flavors of maps: _total_ maps, which include a
"default" element to be returned when a key being looked up
doesn't exist, and _partial_ maps, which return an `Maybe` to
indicate success or failure.  The latter is defined in terms of
the former, using `nothing` as the default element.

## The Agda Standard Library

One small digression before we start.

Unlike the chapters we have seen so far, this one does not
import the chapter before it (and, transitively, all the
earlier chapters).  Instead, in this chapter and from now, on
we're going to import the definitions and theorems we need
directly from Agda's standard library stuff.  You should not notice
much difference, though, because we've been careful to name our
own definitions and theorems the same as their counterparts in the
standard library, wherever they overlap.

<pre class="Agda">{% raw %}
<a name="1482" class="Keyword"
      >open</a
      ><a name="1486"
      > </a
      ><a name="1487" class="Keyword"
      >import</a
      ><a name="1493"
      > </a
      ><a name="1494" href="https://agda.github.io/agda-stdlib/Function.html#1" class="Module"
      >Function</a
      ><a name="1502"
      >         </a
      ><a name="1511" class="Keyword"
      >using</a
      ><a name="1516"
      > </a
      ><a name="1517" class="Symbol"
      >(</a
      ><a name="1518" href="https://agda.github.io/agda-stdlib/Function.html#713" class="Function Operator"
      >_&#8728;_</a
      ><a name="1521" class="Symbol"
      >)</a
      ><a name="1522"
      >
</a
      ><a name="1523" class="Keyword"
      >open</a
      ><a name="1527"
      > </a
      ><a name="1528" class="Keyword"
      >import</a
      ><a name="1534"
      > </a
      ><a name="1535" href="https://agda.github.io/agda-stdlib/Data.Bool.html#1" class="Module"
      >Data.Bool</a
      ><a name="1544"
      >        </a
      ><a name="1552" class="Keyword"
      >using</a
      ><a name="1557"
      > </a
      ><a name="1558" class="Symbol"
      >(</a
      ><a name="1559" href="Agda.Builtin.Bool.html#67" class="Datatype"
      >Bool</a
      ><a name="1563" class="Symbol"
      >;</a
      ><a name="1564"
      > </a
      ><a name="1565" href="Agda.Builtin.Bool.html#92" class="InductiveConstructor"
      >true</a
      ><a name="1569" class="Symbol"
      >;</a
      ><a name="1570"
      > </a
      ><a name="1571" href="Agda.Builtin.Bool.html#86" class="InductiveConstructor"
      >false</a
      ><a name="1576" class="Symbol"
      >)</a
      ><a name="1577"
      >
</a
      ><a name="1578" class="Keyword"
      >open</a
      ><a name="1582"
      > </a
      ><a name="1583" class="Keyword"
      >import</a
      ><a name="1589"
      > </a
      ><a name="1590" href="https://agda.github.io/agda-stdlib/Data.Empty.html#1" class="Module"
      >Data.Empty</a
      ><a name="1600"
      >       </a
      ><a name="1607" class="Keyword"
      >using</a
      ><a name="1612"
      > </a
      ><a name="1613" class="Symbol"
      >(</a
      ><a name="1614" href="https://agda.github.io/agda-stdlib/Data.Empty.html#243" class="Datatype"
      >&#8869;</a
      ><a name="1615" class="Symbol"
      >;</a
      ><a name="1616"
      > </a
      ><a name="1617" href="https://agda.github.io/agda-stdlib/Data.Empty.html#348" class="Function"
      >&#8869;-elim</a
      ><a name="1623" class="Symbol"
      >)</a
      ><a name="1624"
      >
</a
      ><a name="1625" class="Keyword"
      >open</a
      ><a name="1629"
      > </a
      ><a name="1630" class="Keyword"
      >import</a
      ><a name="1636"
      > </a
      ><a name="1637" href="https://agda.github.io/agda-stdlib/Data.Maybe.html#1" class="Module"
      >Data.Maybe</a
      ><a name="1647"
      >       </a
      ><a name="1654" class="Keyword"
      >using</a
      ><a name="1659"
      > </a
      ><a name="1660" class="Symbol"
      >(</a
      ><a name="1661" href="https://agda.github.io/agda-stdlib/Data.Maybe.Base.html#335" class="Datatype"
      >Maybe</a
      ><a name="1666" class="Symbol"
      >;</a
      ><a name="1667"
      > </a
      ><a name="1668" href="https://agda.github.io/agda-stdlib/Data.Maybe.html#1527" class="InductiveConstructor"
      >just</a
      ><a name="1672" class="Symbol"
      >;</a
      ><a name="1673"
      > </a
      ><a name="1674" href="https://agda.github.io/agda-stdlib/Data.Maybe.html#1588" class="InductiveConstructor"
      >nothing</a
      ><a name="1681" class="Symbol"
      >)</a
      ><a name="1682"
      >
</a
      ><a name="1683" class="Keyword"
      >open</a
      ><a name="1687"
      > </a
      ><a name="1688" class="Keyword"
      >import</a
      ><a name="1694"
      > </a
      ><a name="1695" href="https://agda.github.io/agda-stdlib/Data.Nat.html#1" class="Module"
      >Data.Nat</a
      ><a name="1703"
      >         </a
      ><a name="1712" class="Keyword"
      >using</a
      ><a name="1717"
      > </a
      ><a name="1718" class="Symbol"
      >(</a
      ><a name="1719" href="Agda.Builtin.Nat.html#97" class="Datatype"
      >&#8469;</a
      ><a name="1720" class="Symbol"
      >)</a
      ><a name="1721"
      >
</a
      ><a name="1722" class="Keyword"
      >open</a
      ><a name="1726"
      > </a
      ><a name="1727" class="Keyword"
      >import</a
      ><a name="1733"
      > </a
      ><a name="1734" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#1" class="Module"
      >Relation.Nullary</a
      ><a name="1750"
      > </a
      ><a name="1751" class="Keyword"
      >using</a
      ><a name="1756"
      > </a
      ><a name="1757" class="Symbol"
      >(</a
      ><a name="1758" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#484" class="Datatype"
      >Dec</a
      ><a name="1761" class="Symbol"
      >;</a
      ><a name="1762"
      > </a
      ><a name="1763" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#520" class="InductiveConstructor"
      >yes</a
      ><a name="1766" class="Symbol"
      >;</a
      ><a name="1767"
      > </a
      ><a name="1768" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#547" class="InductiveConstructor"
      >no</a
      ><a name="1770" class="Symbol"
      >)</a
      ><a name="1771"
      >
</a
      ><a name="1772" class="Keyword"
      >open</a
      ><a name="1776"
      > </a
      ><a name="1777" class="Keyword"
      >import</a
      ><a name="1783"
      > </a
      ><a name="1784" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#1" class="Module"
      >Relation.Binary.PropositionalEquality</a
      >
{% endraw %}</pre>

Documentation for the standard library can be found at
<https://agda.github.io/agda-stdlib/>.

## Identifiers

First, we need a type for the keys that we use to index into our
maps.  For this purpose, we again use the type Id` from the
[Lists](sf/Lists.html) chapter.  To make this chapter self contained,
we repeat its definition here, together with the equality comparison
function for ids and its fundamental property.

<pre class="Agda">{% raw %}
<a name="2270" class="Keyword"
      >data</a
      ><a name="2274"
      > </a
      ><a name="2275" href="Maps.html#2275" class="Datatype"
      >Id</a
      ><a name="2277"
      > </a
      ><a name="2278" class="Symbol"
      >:</a
      ><a name="2279"
      > </a
      ><a name="2280" class="PrimitiveType"
      >Set</a
      ><a name="2283"
      > </a
      ><a name="2284" class="Keyword"
      >where</a
      ><a name="2289"
      >
  </a
      ><a name="2292" href="Maps.html#2292" class="InductiveConstructor"
      >id</a
      ><a name="2294"
      > </a
      ><a name="2295" class="Symbol"
      >:</a
      ><a name="2296"
      > </a
      ><a name="2297" href="Agda.Builtin.Nat.html#97" class="Datatype"
      >&#8469;</a
      ><a name="2298"
      > </a
      ><a name="2299" class="Symbol"
      >&#8594;</a
      ><a name="2300"
      > </a
      ><a name="2301" href="Maps.html#2275" class="Datatype"
      >Id</a
      >
{% endraw %}</pre>

<pre class="Agda">{% raw %}
<a name="2329" href="Maps.html#2329" class="Function Operator"
      >_&#8799;_</a
      ><a name="2332"
      > </a
      ><a name="2333" class="Symbol"
      >:</a
      ><a name="2334"
      > </a
      ><a name="2335" class="Symbol"
      >(</a
      ><a name="2336" href="Maps.html#2336" class="Bound"
      >x</a
      ><a name="2337"
      > </a
      ><a name="2338" href="Maps.html#2338" class="Bound"
      >y</a
      ><a name="2339"
      > </a
      ><a name="2340" class="Symbol"
      >:</a
      ><a name="2341"
      > </a
      ><a name="2342" href="Maps.html#2275" class="Datatype"
      >Id</a
      ><a name="2344" class="Symbol"
      >)</a
      ><a name="2345"
      > </a
      ><a name="2346" class="Symbol"
      >&#8594;</a
      ><a name="2347"
      > </a
      ><a name="2348" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#484" class="Datatype"
      >Dec</a
      ><a name="2351"
      > </a
      ><a name="2352" class="Symbol"
      >(</a
      ><a name="2353" href="Maps.html#2336" class="Bound"
      >x</a
      ><a name="2354"
      > </a
      ><a name="2355" href="Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="2356"
      > </a
      ><a name="2357" href="Maps.html#2338" class="Bound"
      >y</a
      ><a name="2358" class="Symbol"
      >)</a
      ><a name="2359"
      >
</a
      ><a name="2360" href="Maps.html#2292" class="InductiveConstructor"
      >id</a
      ><a name="2362"
      > </a
      ><a name="2363" href="Maps.html#2363" class="Bound"
      >x</a
      ><a name="2364"
      > </a
      ><a name="2365" href="Maps.html#2329" class="Function Operator"
      >&#8799;</a
      ><a name="2366"
      > </a
      ><a name="2367" href="Maps.html#2292" class="InductiveConstructor"
      >id</a
      ><a name="2369"
      > </a
      ><a name="2370" href="Maps.html#2370" class="Bound"
      >y</a
      ><a name="2371"
      > </a
      ><a name="2372" class="Keyword"
      >with</a
      ><a name="2376"
      > </a
      ><a name="2377" href="Maps.html#2363" class="Bound"
      >x</a
      ><a name="2378"
      > </a
      ><a name="2379" href="https://agda.github.io/agda-stdlib/Data.Nat.Base.html#3212" class="Function Operator"
      >Data.Nat.&#8799;</a
      ><a name="2389"
      > </a
      ><a name="2390" href="Maps.html#2370" class="Bound"
      >y</a
      ><a name="2391"
      >
</a
      ><a name="2392" href="Maps.html#2292" class="InductiveConstructor"
      >id</a
      ><a name="2394"
      > </a
      ><a name="2395" href="Maps.html#2395" class="Bound"
      >x</a
      ><a name="2396"
      > </a
      ><a name="2397" href="Maps.html#2329" class="Function Operator"
      >&#8799;</a
      ><a name="2398"
      > </a
      ><a name="2399" href="Maps.html#2292" class="InductiveConstructor"
      >id</a
      ><a name="2401"
      > </a
      ><a name="2402" href="Maps.html#2402" class="Bound"
      >y</a
      ><a name="2403"
      > </a
      ><a name="2404" class="Symbol"
      >|</a
      ><a name="2405"
      > </a
      ><a name="2406" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#520" class="InductiveConstructor"
      >yes</a
      ><a name="2409"
      > </a
      ><a name="2410" href="Maps.html#2410" class="Bound"
      >x=y</a
      ><a name="2413"
      > </a
      ><a name="2414" class="Keyword"
      >rewrite</a
      ><a name="2421"
      > </a
      ><a name="2422" href="Maps.html#2410" class="Bound"
      >x=y</a
      ><a name="2425"
      > </a
      ><a name="2426" class="Symbol"
      >=</a
      ><a name="2427"
      > </a
      ><a name="2428" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#520" class="InductiveConstructor"
      >yes</a
      ><a name="2431"
      > </a
      ><a name="2432" href="Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="2436"
      >
</a
      ><a name="2437" href="Maps.html#2292" class="InductiveConstructor"
      >id</a
      ><a name="2439"
      > </a
      ><a name="2440" href="Maps.html#2440" class="Bound"
      >x</a
      ><a name="2441"
      > </a
      ><a name="2442" href="Maps.html#2329" class="Function Operator"
      >&#8799;</a
      ><a name="2443"
      > </a
      ><a name="2444" href="Maps.html#2292" class="InductiveConstructor"
      >id</a
      ><a name="2446"
      > </a
      ><a name="2447" href="Maps.html#2447" class="Bound"
      >y</a
      ><a name="2448"
      > </a
      ><a name="2449" class="Symbol"
      >|</a
      ><a name="2450"
      > </a
      ><a name="2451" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#547" class="InductiveConstructor"
      >no</a
      ><a name="2453"
      >  </a
      ><a name="2455" href="Maps.html#2455" class="Bound"
      >x&#8800;y</a
      ><a name="2458"
      > </a
      ><a name="2459" class="Symbol"
      >=</a
      ><a name="2460"
      > </a
      ><a name="2461" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#547" class="InductiveConstructor"
      >no</a
      ><a name="2463"
      > </a
      ><a name="2464" class="Symbol"
      >(</a
      ><a name="2465" href="Maps.html#2455" class="Bound"
      >x&#8800;y</a
      ><a name="2468"
      > </a
      ><a name="2469" href="https://agda.github.io/agda-stdlib/Function.html#713" class="Function Operator"
      >&#8728;</a
      ><a name="2470"
      > </a
      ><a name="2471" href="Maps.html#2491" class="Function"
      >id-inj</a
      ><a name="2477" class="Symbol"
      >)</a
      ><a name="2478"
      >
  </a
      ><a name="2481" class="Keyword"
      >where</a
      ><a name="2486"
      >
    </a
      ><a name="2491" href="Maps.html#2491" class="Function"
      >id-inj</a
      ><a name="2497"
      > </a
      ><a name="2498" class="Symbol"
      >:</a
      ><a name="2499"
      > </a
      ><a name="2500" class="Symbol"
      >&#8704;</a
      ><a name="2501"
      > </a
      ><a name="2508" class="Symbol"
      >&#8594;</a
      ><a name="2509"
      > </a
      ><a name="2510" href="Maps.html#2292" class="InductiveConstructor"
      >id</a
      ><a name="2512"
      > </a
      ><a name="2513" href="Maps.html#2503" class="Bound"
      >x</a
      ><a name="2514"
      > </a
      ><a name="2515" href="Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="2516"
      > </a
      ><a name="2517" href="Maps.html#2292" class="InductiveConstructor"
      >id</a
      ><a name="2519"
      > </a
      ><a name="2520" href="Maps.html#2505" class="Bound"
      >y</a
      ><a name="2521"
      > </a
      ><a name="2522" class="Symbol"
      >&#8594;</a
      ><a name="2523"
      > </a
      ><a name="2524" href="Maps.html#2503" class="Bound"
      >x</a
      ><a name="2525"
      > </a
      ><a name="2526" href="Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="2527"
      > </a
      ><a name="2528" href="Maps.html#2505" class="Bound"
      >y</a
      ><a name="2529"
      >
    </a
      ><a name="2534" href="Maps.html#2491" class="Function"
      >id-inj</a
      ><a name="2540"
      > </a
      ><a name="2541" href="Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="2545"
      > </a
      ><a name="2546" class="Symbol"
      >=</a
      ><a name="2547"
      > </a
      ><a name="2548" href="Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      >
{% endraw %}</pre>

## Total Maps

Our main job in this chapter will be to build a definition of
partial maps that is similar in behavior to the one we saw in the
[Lists](sf/Lists.html) chapter, plus accompanying lemmas about their
behavior.

This time around, though, we're going to use _functions_, rather
than lists of key-value pairs, to build maps.  The advantage of
this representation is that it offers a more _extensional_ view of
maps, where two maps that respond to queries in the same way will
be represented as literally the same thing (the same function),
rather than just "equivalent" data structures.  This, in turn,
simplifies proofs that use maps.

We build partial maps in two steps.  First, we define a type of
_total maps_ that return a default value when we look up a key
that is not present in the map.

<pre class="Agda">{% raw %}
<a name="3384" href="Maps.html#3384" class="Function"
      >TotalMap</a
      ><a name="3392"
      > </a
      ><a name="3393" class="Symbol"
      >:</a
      ><a name="3394"
      > </a
      ><a name="3395" class="PrimitiveType"
      >Set</a
      ><a name="3398"
      > </a
      ><a name="3399" class="Symbol"
      >&#8594;</a
      ><a name="3400"
      > </a
      ><a name="3401" class="PrimitiveType"
      >Set</a
      ><a name="3404"
      >
</a
      ><a name="3405" href="Maps.html#3384" class="Function"
      >TotalMap</a
      ><a name="3413"
      > </a
      ><a name="3414" href="Maps.html#3414" class="Bound"
      >A</a
      ><a name="3415"
      > </a
      ><a name="3416" class="Symbol"
      >=</a
      ><a name="3417"
      > </a
      ><a name="3418" href="Maps.html#2275" class="Datatype"
      >Id</a
      ><a name="3420"
      > </a
      ><a name="3421" class="Symbol"
      >&#8594;</a
      ><a name="3422"
      > </a
      ><a name="3423" href="Maps.html#3414" class="Bound"
      >A</a
      >
{% endraw %}</pre>

Intuitively, a total map over anﬁ element type $$A$$ _is_ just a
function that can be used to look up ids, yielding $$A$$s.

<pre class="Agda">{% raw %}
<a name="3575" class="Keyword"
      >module</a
      ><a name="3581"
      > </a
      ><a name="3582" href="Maps.html#3582" class="Module"
      >TotalMap</a
      ><a name="3590"
      > </a
      ><a name="3591" class="Keyword"
      >where</a
      >
{% endraw %}</pre>

The function `empty` yields an empty total map, given a
default element; this map always returns the default element when
applied to any id.

<pre class="Agda">{% raw %}
  <a name="3766" href="Maps.html#3766" class="Function"
      >empty</a
      ><a name="3771"
      > </a
      ><a name="3772" class="Symbol"
      >:</a
      ><a name="3773"
      > </a
      ><a name="3774" class="Symbol"
      >&#8704;</a
      ><a name="3775"
      > </a
      ><a name="3780" class="Symbol"
      >&#8594;</a
      ><a name="3781"
      > </a
      ><a name="3782" href="Maps.html#3777" class="Bound"
      >A</a
      ><a name="3783"
      > </a
      ><a name="3784" class="Symbol"
      >&#8594;</a
      ><a name="3785"
      > </a
      ><a name="3786" href="Maps.html#3384" class="Function"
      >TotalMap</a
      ><a name="3794"
      > </a
      ><a name="3795" href="Maps.html#3777" class="Bound"
      >A</a
      ><a name="3796"
      >
  </a
      ><a name="3799" href="Maps.html#3766" class="Function"
      >empty</a
      ><a name="3804"
      > </a
      ><a name="3805" href="Maps.html#3805" class="Bound"
      >x</a
      ><a name="3806"
      > </a
      ><a name="3807" class="Symbol"
      >=</a
      ><a name="3808"
      > </a
      ><a name="3809" class="Symbol"
      >&#955;</a
      ><a name="3810"
      > </a
      ><a name="3811" href="Maps.html#3811" class="Bound"
      >_</a
      ><a name="3812"
      > </a
      ><a name="3813" class="Symbol"
      >&#8594;</a
      ><a name="3814"
      > </a
      ><a name="3815" href="Maps.html#3805" class="Bound"
      >x</a
      >
{% endraw %}</pre>

More interesting is the `update` function, which (as before) takes
a map $$m$$, a key $$x$$, and a value $$v$$ and returns a new map that
takes $$x$$ to $$v$$ and takes every other key to whatever $$m$$ does.

<pre class="Agda">{% raw %}
  <a name="4054" href="Maps.html#4054" class="Function"
      >update</a
      ><a name="4060"
      > </a
      ><a name="4061" class="Symbol"
      >:</a
      ><a name="4062"
      > </a
      ><a name="4063" class="Symbol"
      >&#8704;</a
      ><a name="4064"
      > </a
      ><a name="4069" class="Symbol"
      >&#8594;</a
      ><a name="4070"
      > </a
      ><a name="4071" href="Maps.html#3384" class="Function"
      >TotalMap</a
      ><a name="4079"
      > </a
      ><a name="4080" href="Maps.html#4066" class="Bound"
      >A</a
      ><a name="4081"
      > </a
      ><a name="4082" class="Symbol"
      >-&gt;</a
      ><a name="4084"
      > </a
      ><a name="4085" href="Maps.html#2275" class="Datatype"
      >Id</a
      ><a name="4087"
      > </a
      ><a name="4088" class="Symbol"
      >-&gt;</a
      ><a name="4090"
      > </a
      ><a name="4091" href="Maps.html#4066" class="Bound"
      >A</a
      ><a name="4092"
      > </a
      ><a name="4093" class="Symbol"
      >-&gt;</a
      ><a name="4095"
      > </a
      ><a name="4096" href="Maps.html#3384" class="Function"
      >TotalMap</a
      ><a name="4104"
      > </a
      ><a name="4105" href="Maps.html#4066" class="Bound"
      >A</a
      ><a name="4106"
      >
  </a
      ><a name="4109" href="Maps.html#4054" class="Function"
      >update</a
      ><a name="4115"
      > </a
      ><a name="4116" href="Maps.html#4116" class="Bound"
      >m</a
      ><a name="4117"
      > </a
      ><a name="4118" href="Maps.html#4118" class="Bound"
      >x</a
      ><a name="4119"
      > </a
      ><a name="4120" href="Maps.html#4120" class="Bound"
      >v</a
      ><a name="4121"
      > </a
      ><a name="4122" href="Maps.html#4122" class="Bound"
      >y</a
      ><a name="4123"
      > </a
      ><a name="4124" class="Keyword"
      >with</a
      ><a name="4128"
      > </a
      ><a name="4129" href="Maps.html#4118" class="Bound"
      >x</a
      ><a name="4130"
      > </a
      ><a name="4131" href="Maps.html#2329" class="Function Operator"
      >&#8799;</a
      ><a name="4132"
      > </a
      ><a name="4133" href="Maps.html#4122" class="Bound"
      >y</a
      ><a name="4134"
      >
  </a
      ><a name="4137" class="Symbol"
      >...</a
      ><a name="4140"
      > </a
      ><a name="4141" class="Symbol"
      >|</a
      ><a name="4142"
      > </a
      ><a name="4143" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#520" class="InductiveConstructor"
      >yes</a
      ><a name="4146"
      > </a
      ><a name="4147" href="Maps.html#4147" class="Bound"
      >x=y</a
      ><a name="4150"
      > </a
      ><a name="4151" class="Symbol"
      >=</a
      ><a name="4152"
      > </a
      ><a name="4153" href="Maps.html#4120" class="Bound"
      >v</a
      ><a name="4154"
      >
  </a
      ><a name="4157" class="Symbol"
      >...</a
      ><a name="4160"
      > </a
      ><a name="4161" class="Symbol"
      >|</a
      ><a name="4162"
      > </a
      ><a name="4163" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#547" class="InductiveConstructor"
      >no</a
      ><a name="4165"
      >  </a
      ><a name="4167" href="Maps.html#4167" class="Bound"
      >x&#8800;y</a
      ><a name="4170"
      > </a
      ><a name="4171" class="Symbol"
      >=</a
      ><a name="4172"
      > </a
      ><a name="4173" href="Maps.html#4116" class="Bound"
      >m</a
      ><a name="4174"
      > </a
      ><a name="4175" href="Maps.html#4122" class="Bound"
      >y</a
      >
{% endraw %}</pre>

This definition is a nice example of higher-order programming.
The `update` function takes a _function_ $$m$$ and yields a new
function $$\lambda x'.\vdots$$ that behaves like the desired map.

For example, we can build a map taking ids to bools, where `id
3` is mapped to `true` and every other key is mapped to `false`,
like this:

<pre class="Agda">{% raw %}
  <a name="4538" href="Maps.html#4538" class="Function"
      >examplemap</a
      ><a name="4548"
      > </a
      ><a name="4549" class="Symbol"
      >:</a
      ><a name="4550"
      > </a
      ><a name="4551" href="Maps.html#3384" class="Function"
      >TotalMap</a
      ><a name="4559"
      > </a
      ><a name="4560" href="Agda.Builtin.Bool.html#67" class="Datatype"
      >Bool</a
      ><a name="4564"
      >
  </a
      ><a name="4567" href="Maps.html#4538" class="Function"
      >examplemap</a
      ><a name="4577"
      > </a
      ><a name="4578" class="Symbol"
      >=</a
      ><a name="4579"
      > </a
      ><a name="4580" href="Maps.html#4054" class="Function"
      >update</a
      ><a name="4586"
      > </a
      ><a name="4587" class="Symbol"
      >(</a
      ><a name="4588" href="Maps.html#4054" class="Function"
      >update</a
      ><a name="4594"
      > </a
      ><a name="4595" class="Symbol"
      >(</a
      ><a name="4596" href="Maps.html#3766" class="Function"
      >empty</a
      ><a name="4601"
      > </a
      ><a name="4602" href="Agda.Builtin.Bool.html#86" class="InductiveConstructor"
      >false</a
      ><a name="4607" class="Symbol"
      >)</a
      ><a name="4608"
      > </a
      ><a name="4609" class="Symbol"
      >(</a
      ><a name="4610" href="Maps.html#2292" class="InductiveConstructor"
      >id</a
      ><a name="4612"
      > </a
      ><a name="4613" class="Number"
      >1</a
      ><a name="4614" class="Symbol"
      >)</a
      ><a name="4615"
      > </a
      ><a name="4616" href="Agda.Builtin.Bool.html#86" class="InductiveConstructor"
      >false</a
      ><a name="4621" class="Symbol"
      >)</a
      ><a name="4622"
      > </a
      ><a name="4623" class="Symbol"
      >(</a
      ><a name="4624" href="Maps.html#2292" class="InductiveConstructor"
      >id</a
      ><a name="4626"
      > </a
      ><a name="4627" class="Number"
      >3</a
      ><a name="4628" class="Symbol"
      >)</a
      ><a name="4629"
      > </a
      ><a name="4630" href="Agda.Builtin.Bool.html#92" class="InductiveConstructor"
      >true</a
      >
{% endraw %}</pre>

This completes the definition of total maps.  Note that we don't
need to define a `find` operation because it is just function
application!

<pre class="Agda">{% raw %}
  <a name="4803" href="Maps.html#4803" class="Function Operator"
      >test_examplemap0</a
      ><a name="4819"
      > </a
      ><a name="4820" class="Symbol"
      >:</a
      ><a name="4821"
      > </a
      ><a name="4822" href="Maps.html#4538" class="Function"
      >examplemap</a
      ><a name="4832"
      > </a
      ><a name="4833" class="Symbol"
      >(</a
      ><a name="4834" href="Maps.html#2292" class="InductiveConstructor"
      >id</a
      ><a name="4836"
      > </a
      ><a name="4837" class="Number"
      >0</a
      ><a name="4838" class="Symbol"
      >)</a
      ><a name="4839"
      > </a
      ><a name="4840" href="Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="4841"
      > </a
      ><a name="4842" href="Agda.Builtin.Bool.html#86" class="InductiveConstructor"
      >false</a
      ><a name="4847"
      >
  </a
      ><a name="4850" href="Maps.html#4803" class="Function Operator"
      >test_examplemap0</a
      ><a name="4866"
      > </a
      ><a name="4867" class="Symbol"
      >=</a
      ><a name="4868"
      > </a
      ><a name="4869" href="Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="4873"
      >

  </a
      ><a name="4877" href="Maps.html#4877" class="Function Operator"
      >test_examplemap1</a
      ><a name="4893"
      > </a
      ><a name="4894" class="Symbol"
      >:</a
      ><a name="4895"
      > </a
      ><a name="4896" href="Maps.html#4538" class="Function"
      >examplemap</a
      ><a name="4906"
      > </a
      ><a name="4907" class="Symbol"
      >(</a
      ><a name="4908" href="Maps.html#2292" class="InductiveConstructor"
      >id</a
      ><a name="4910"
      > </a
      ><a name="4911" class="Number"
      >1</a
      ><a name="4912" class="Symbol"
      >)</a
      ><a name="4913"
      > </a
      ><a name="4914" href="Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="4915"
      > </a
      ><a name="4916" href="Agda.Builtin.Bool.html#86" class="InductiveConstructor"
      >false</a
      ><a name="4921"
      >
  </a
      ><a name="4924" href="Maps.html#4877" class="Function Operator"
      >test_examplemap1</a
      ><a name="4940"
      > </a
      ><a name="4941" class="Symbol"
      >=</a
      ><a name="4942"
      > </a
      ><a name="4943" href="Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="4947"
      >

  </a
      ><a name="4951" href="Maps.html#4951" class="Function Operator"
      >test_examplemap2</a
      ><a name="4967"
      > </a
      ><a name="4968" class="Symbol"
      >:</a
      ><a name="4969"
      > </a
      ><a name="4970" href="Maps.html#4538" class="Function"
      >examplemap</a
      ><a name="4980"
      > </a
      ><a name="4981" class="Symbol"
      >(</a
      ><a name="4982" href="Maps.html#2292" class="InductiveConstructor"
      >id</a
      ><a name="4984"
      > </a
      ><a name="4985" class="Number"
      >2</a
      ><a name="4986" class="Symbol"
      >)</a
      ><a name="4987"
      > </a
      ><a name="4988" href="Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="4989"
      > </a
      ><a name="4990" href="Agda.Builtin.Bool.html#86" class="InductiveConstructor"
      >false</a
      ><a name="4995"
      >
  </a
      ><a name="4998" href="Maps.html#4951" class="Function Operator"
      >test_examplemap2</a
      ><a name="5014"
      > </a
      ><a name="5015" class="Symbol"
      >=</a
      ><a name="5016"
      > </a
      ><a name="5017" href="Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="5021"
      >

  </a
      ><a name="5025" href="Maps.html#5025" class="Function Operator"
      >test_examplemap3</a
      ><a name="5041"
      > </a
      ><a name="5042" class="Symbol"
      >:</a
      ><a name="5043"
      > </a
      ><a name="5044" href="Maps.html#4538" class="Function"
      >examplemap</a
      ><a name="5054"
      > </a
      ><a name="5055" class="Symbol"
      >(</a
      ><a name="5056" href="Maps.html#2292" class="InductiveConstructor"
      >id</a
      ><a name="5058"
      > </a
      ><a name="5059" class="Number"
      >3</a
      ><a name="5060" class="Symbol"
      >)</a
      ><a name="5061"
      > </a
      ><a name="5062" href="Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="5063"
      > </a
      ><a name="5064" href="Agda.Builtin.Bool.html#92" class="InductiveConstructor"
      >true</a
      ><a name="5068"
      >
  </a
      ><a name="5071" href="Maps.html#5025" class="Function Operator"
      >test_examplemap3</a
      ><a name="5087"
      > </a
      ><a name="5088" class="Symbol"
      >=</a
      ><a name="5089"
      > </a
      ><a name="5090" href="Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      >
{% endraw %}</pre>

To use maps in later chapters, we'll need several fundamental
facts about how they behave.  Even if you don't work the following
exercises, make sure you thoroughly understand the statements of
the lemmas!  (Some of the proofs require the functional
extensionality axiom, which is discussed in the [Logic]
chapter and included in the Agda standard library.)

#### Exercise: 1 star, optional (apply-empty)
First, the empty map returns its default element for all keys:

<pre class="Agda">{% raw %}
  <a name="5591" class="Keyword"
      >postulate</a
      ><a name="5600"
      >
    </a
      ><a name="5605" href="Maps.html#5605" class="Postulate"
      >apply-empty</a
      ><a name="5616"
      > </a
      ><a name="5617" class="Symbol"
      >:</a
      ><a name="5618"
      > </a
      ><a name="5619" class="Symbol"
      >&#8704;</a
      ><a name="5620"
      > </a
      ><a name="5629" class="Symbol"
      >&#8594;</a
      ><a name="5630"
      > </a
      ><a name="5631" href="Maps.html#3766" class="Function"
      >empty</a
      ><a name="5636"
      > </a
      ><a name="5641" href="Maps.html#5626" class="Bound"
      >v</a
      ><a name="5642"
      > </a
      ><a name="5643" href="Maps.html#5624" class="Bound"
      >x</a
      ><a name="5644"
      > </a
      ><a name="5645" href="Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="5646"
      > </a
      ><a name="5647" href="Maps.html#5626" class="Bound"
      >v</a
      >
{% endraw %}</pre>

<div class="hidden">
<pre class="Agda">{% raw %}
  <a name="5697" href="Maps.html#5697" class="Function"
      >apply-empty&#8242;</a
      ><a name="5709"
      > </a
      ><a name="5710" class="Symbol"
      >:</a
      ><a name="5711"
      > </a
      ><a name="5712" class="Symbol"
      >&#8704;</a
      ><a name="5713"
      > </a
      ><a name="5722" class="Symbol"
      >&#8594;</a
      ><a name="5723"
      > </a
      ><a name="5724" href="Maps.html#3766" class="Function"
      >empty</a
      ><a name="5729"
      > </a
      ><a name="5734" href="Maps.html#5719" class="Bound"
      >v</a
      ><a name="5735"
      > </a
      ><a name="5736" href="Maps.html#5717" class="Bound"
      >x</a
      ><a name="5737"
      > </a
      ><a name="5738" href="Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="5739"
      > </a
      ><a name="5740" href="Maps.html#5719" class="Bound"
      >v</a
      ><a name="5741"
      >
  </a
      ><a name="5744" href="Maps.html#5697" class="Function"
      >apply-empty&#8242;</a
      ><a name="5756"
      > </a
      ><a name="5757" class="Symbol"
      >=</a
      ><a name="5758"
      > </a
      ><a name="5759" href="Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      >
{% endraw %}</pre>
</div>

#### Exercise: 2 stars, optional (update-eq)
Next, if we update a map $$m$$ at a key $$x$$ with a new value $$v$$
and then look up $$x$$ in the map resulting from the `update`, we get
back $$v$$:

<pre class="Agda">{% raw %}
  <a name="5995" class="Keyword"
      >postulate</a
      ><a name="6004"
      >
    </a
      ><a name="6009" href="Maps.html#6009" class="Postulate"
      >update-eq</a
      ><a name="6018"
      > </a
      ><a name="6019" class="Symbol"
      >:</a
      ><a name="6020"
      > </a
      ><a name="6021" class="Symbol"
      >&#8704;</a
      ><a name="6022"
      > </a
      ><a name="6029" class="Symbol"
      >(</a
      ><a name="6030" href="Maps.html#6030" class="Bound"
      >m</a
      ><a name="6031"
      > </a
      ><a name="6032" class="Symbol"
      >:</a
      ><a name="6033"
      > </a
      ><a name="6034" href="Maps.html#3384" class="Function"
      >TotalMap</a
      ><a name="6042"
      > </a
      ><a name="6043" href="Maps.html#6024" class="Bound"
      >A</a
      ><a name="6044" class="Symbol"
      >)</a
      ><a name="6045"
      > </a
      ><a name="6046" class="Symbol"
      >(</a
      ><a name="6047" href="Maps.html#6047" class="Bound"
      >x</a
      ><a name="6048"
      > </a
      ><a name="6049" class="Symbol"
      >:</a
      ><a name="6050"
      > </a
      ><a name="6051" href="Maps.html#2275" class="Datatype"
      >Id</a
      ><a name="6053" class="Symbol"
      >)</a
      ><a name="6054"
      >
              </a
      ><a name="6069" class="Symbol"
      >&#8594;</a
      ><a name="6070"
      > </a
      ><a name="6071" class="Symbol"
      >(</a
      ><a name="6072" href="Maps.html#4054" class="Function"
      >update</a
      ><a name="6078"
      > </a
      ><a name="6079" href="Maps.html#6030" class="Bound"
      >m</a
      ><a name="6080"
      > </a
      ><a name="6081" href="Maps.html#6047" class="Bound"
      >x</a
      ><a name="6082"
      > </a
      ><a name="6083" href="Maps.html#6026" class="Bound"
      >v</a
      ><a name="6084" class="Symbol"
      >)</a
      ><a name="6085"
      > </a
      ><a name="6086" href="Maps.html#6047" class="Bound"
      >x</a
      ><a name="6087"
      > </a
      ><a name="6088" href="Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="6089"
      > </a
      ><a name="6090" href="Maps.html#6026" class="Bound"
      >v</a
      >
{% endraw %}</pre>

<div class="hidden">
<pre class="Agda">{% raw %}
  <a name="6140" href="Maps.html#6140" class="Function"
      >update-eq&#8242;</a
      ><a name="6150"
      > </a
      ><a name="6151" class="Symbol"
      >:</a
      ><a name="6152"
      > </a
      ><a name="6153" class="Symbol"
      >&#8704;</a
      ><a name="6154"
      > </a
      ><a name="6161" class="Symbol"
      >(</a
      ><a name="6162" href="Maps.html#6162" class="Bound"
      >m</a
      ><a name="6163"
      > </a
      ><a name="6164" class="Symbol"
      >:</a
      ><a name="6165"
      > </a
      ><a name="6166" href="Maps.html#3384" class="Function"
      >TotalMap</a
      ><a name="6174"
      > </a
      ><a name="6175" href="Maps.html#6156" class="Bound"
      >A</a
      ><a name="6176" class="Symbol"
      >)</a
      ><a name="6177"
      > </a
      ><a name="6178" class="Symbol"
      >(</a
      ><a name="6179" href="Maps.html#6179" class="Bound"
      >x</a
      ><a name="6180"
      > </a
      ><a name="6181" class="Symbol"
      >:</a
      ><a name="6182"
      > </a
      ><a name="6183" href="Maps.html#2275" class="Datatype"
      >Id</a
      ><a name="6185" class="Symbol"
      >)</a
      ><a name="6186"
      >
             </a
      ><a name="6200" class="Symbol"
      >&#8594;</a
      ><a name="6201"
      > </a
      ><a name="6202" class="Symbol"
      >(</a
      ><a name="6203" href="Maps.html#4054" class="Function"
      >update</a
      ><a name="6209"
      > </a
      ><a name="6210" href="Maps.html#6162" class="Bound"
      >m</a
      ><a name="6211"
      > </a
      ><a name="6212" href="Maps.html#6179" class="Bound"
      >x</a
      ><a name="6213"
      > </a
      ><a name="6214" href="Maps.html#6158" class="Bound"
      >v</a
      ><a name="6215" class="Symbol"
      >)</a
      ><a name="6216"
      > </a
      ><a name="6217" href="Maps.html#6179" class="Bound"
      >x</a
      ><a name="6218"
      > </a
      ><a name="6219" href="Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="6220"
      > </a
      ><a name="6221" href="Maps.html#6158" class="Bound"
      >v</a
      ><a name="6222"
      >
  </a
      ><a name="6225" href="Maps.html#6140" class="Function"
      >update-eq&#8242;</a
      ><a name="6235"
      > </a
      ><a name="6236" href="Maps.html#6236" class="Bound"
      >m</a
      ><a name="6237"
      > </a
      ><a name="6238" href="Maps.html#6238" class="Bound"
      >x</a
      ><a name="6239"
      > </a
      ><a name="6240" class="Keyword"
      >with</a
      ><a name="6244"
      > </a
      ><a name="6245" href="Maps.html#6238" class="Bound"
      >x</a
      ><a name="6246"
      > </a
      ><a name="6247" href="Maps.html#2329" class="Function Operator"
      >&#8799;</a
      ><a name="6248"
      > </a
      ><a name="6249" href="Maps.html#6238" class="Bound"
      >x</a
      ><a name="6250"
      >
  </a
      ><a name="6253" class="Symbol"
      >...</a
      ><a name="6256"
      > </a
      ><a name="6257" class="Symbol"
      >|</a
      ><a name="6258"
      > </a
      ><a name="6259" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#520" class="InductiveConstructor"
      >yes</a
      ><a name="6262"
      > </a
      ><a name="6263" href="Maps.html#6263" class="Bound"
      >x=x</a
      ><a name="6266"
      > </a
      ><a name="6267" class="Symbol"
      >=</a
      ><a name="6268"
      > </a
      ><a name="6269" href="Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="6273"
      >
  </a
      ><a name="6276" class="Symbol"
      >...</a
      ><a name="6279"
      > </a
      ><a name="6280" class="Symbol"
      >|</a
      ><a name="6281"
      > </a
      ><a name="6282" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#547" class="InductiveConstructor"
      >no</a
      ><a name="6284"
      >  </a
      ><a name="6286" href="Maps.html#6286" class="Bound"
      >x&#8800;x</a
      ><a name="6289"
      > </a
      ><a name="6290" class="Symbol"
      >=</a
      ><a name="6291"
      > </a
      ><a name="6292" href="https://agda.github.io/agda-stdlib/Data.Empty.html#348" class="Function"
      >&#8869;-elim</a
      ><a name="6298"
      > </a
      ><a name="6299" class="Symbol"
      >(</a
      ><a name="6300" href="Maps.html#6286" class="Bound"
      >x&#8800;x</a
      ><a name="6303"
      > </a
      ><a name="6304" href="Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="6308" class="Symbol"
      >)</a
      >
{% endraw %}</pre>
</div>

#### Exercise: 2 stars, optional (update-neq)
On the other hand, if we update a map $$m$$ at a key $$x$$ and
then look up a _different_ key $$y$$ in the resulting map, we get
the same result that $$m$$ would have given:

<pre class="Agda">{% raw %}
  <a name="6565" href="Maps.html#6565" class="Function"
      >update-neq</a
      ><a name="6575"
      > </a
      ><a name="6576" class="Symbol"
      >:</a
      ><a name="6577"
      > </a
      ><a name="6578" class="Symbol"
      >&#8704;</a
      ><a name="6579"
      > </a
      ><a name="6586" class="Symbol"
      >(</a
      ><a name="6587" href="Maps.html#6587" class="Bound"
      >m</a
      ><a name="6588"
      > </a
      ><a name="6589" class="Symbol"
      >:</a
      ><a name="6590"
      > </a
      ><a name="6591" href="Maps.html#3384" class="Function"
      >TotalMap</a
      ><a name="6599"
      > </a
      ><a name="6600" href="Maps.html#6581" class="Bound"
      >A</a
      ><a name="6601" class="Symbol"
      >)</a
      ><a name="6602"
      > </a
      ><a name="6603" class="Symbol"
      >(</a
      ><a name="6604" href="Maps.html#6604" class="Bound"
      >x</a
      ><a name="6605"
      > </a
      ><a name="6606" href="Maps.html#6606" class="Bound"
      >y</a
      ><a name="6607"
      > </a
      ><a name="6608" class="Symbol"
      >:</a
      ><a name="6609"
      > </a
      ><a name="6610" href="Maps.html#2275" class="Datatype"
      >Id</a
      ><a name="6612" class="Symbol"
      >)</a
      ><a name="6613"
      >
             </a
      ><a name="6627" class="Symbol"
      >&#8594;</a
      ><a name="6628"
      > </a
      ><a name="6629" href="Maps.html#6604" class="Bound"
      >x</a
      ><a name="6630"
      > </a
      ><a name="6631" href="https://agda.github.io/agda-stdlib/Relation.Binary.Core.html#4493" class="Function Operator"
      >&#8802;</a
      ><a name="6632"
      > </a
      ><a name="6633" href="Maps.html#6606" class="Bound"
      >y</a
      ><a name="6634"
      > </a
      ><a name="6635" class="Symbol"
      >&#8594;</a
      ><a name="6636"
      > </a
      ><a name="6637" class="Symbol"
      >(</a
      ><a name="6638" href="Maps.html#4054" class="Function"
      >update</a
      ><a name="6644"
      > </a
      ><a name="6645" href="Maps.html#6587" class="Bound"
      >m</a
      ><a name="6646"
      > </a
      ><a name="6647" href="Maps.html#6604" class="Bound"
      >x</a
      ><a name="6648"
      > </a
      ><a name="6649" href="Maps.html#6583" class="Bound"
      >v</a
      ><a name="6650" class="Symbol"
      >)</a
      ><a name="6651"
      > </a
      ><a name="6652" href="Maps.html#6606" class="Bound"
      >y</a
      ><a name="6653"
      > </a
      ><a name="6654" href="Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="6655"
      > </a
      ><a name="6656" href="Maps.html#6587" class="Bound"
      >m</a
      ><a name="6657"
      > </a
      ><a name="6658" href="Maps.html#6606" class="Bound"
      >y</a
      ><a name="6659"
      >
  </a
      ><a name="6662" href="Maps.html#6565" class="Function"
      >update-neq</a
      ><a name="6672"
      > </a
      ><a name="6673" href="Maps.html#6673" class="Bound"
      >m</a
      ><a name="6674"
      > </a
      ><a name="6675" href="Maps.html#6675" class="Bound"
      >x</a
      ><a name="6676"
      > </a
      ><a name="6677" href="Maps.html#6677" class="Bound"
      >y</a
      ><a name="6678"
      > </a
      ><a name="6679" href="Maps.html#6679" class="Bound"
      >x&#8800;y</a
      ><a name="6682"
      > </a
      ><a name="6683" class="Keyword"
      >with</a
      ><a name="6687"
      > </a
      ><a name="6688" href="Maps.html#6675" class="Bound"
      >x</a
      ><a name="6689"
      > </a
      ><a name="6690" href="Maps.html#2329" class="Function Operator"
      >&#8799;</a
      ><a name="6691"
      > </a
      ><a name="6692" href="Maps.html#6677" class="Bound"
      >y</a
      ><a name="6693"
      >
  </a
      ><a name="6696" class="Symbol"
      >...</a
      ><a name="6699"
      > </a
      ><a name="6700" class="Symbol"
      >|</a
      ><a name="6701"
      > </a
      ><a name="6702" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#520" class="InductiveConstructor"
      >yes</a
      ><a name="6705"
      > </a
      ><a name="6706" href="Maps.html#6706" class="Bound"
      >x=y</a
      ><a name="6709"
      > </a
      ><a name="6710" class="Symbol"
      >=</a
      ><a name="6711"
      > </a
      ><a name="6712" href="https://agda.github.io/agda-stdlib/Data.Empty.html#348" class="Function"
      >&#8869;-elim</a
      ><a name="6718"
      > </a
      ><a name="6719" class="Symbol"
      >(</a
      ><a name="6720" href="Maps.html#6679" class="Bound"
      >x&#8800;y</a
      ><a name="6723"
      > </a
      ><a name="6724" href="Maps.html#6706" class="Bound"
      >x=y</a
      ><a name="6727" class="Symbol"
      >)</a
      ><a name="6728"
      >
  </a
      ><a name="6731" class="Symbol"
      >...</a
      ><a name="6734"
      > </a
      ><a name="6735" class="Symbol"
      >|</a
      ><a name="6736"
      > </a
      ><a name="6737" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#547" class="InductiveConstructor"
      >no</a
      ><a name="6739"
      >  </a
      ><a name="6741" class="Symbol"
      >_</a
      ><a name="6742"
      >   </a
      ><a name="6745" class="Symbol"
      >=</a
      ><a name="6746"
      > </a
      ><a name="6747" href="Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      >
{% endraw %}</pre>

#### Exercise: 2 stars, optional (update-shadow)
If we update a map $$m$$ at a key $$x$$ with a value $$v_1$$ and then
update again with the same key $$x$$ and another value $$v_2$$, the
resulting map behaves the same (gives the same result when applied
to any key) as the simpler map obtained by performing just
the second `update` on $$m$$:

<pre class="Agda">{% raw %}
  <a name="7123" class="Keyword"
      >postulate</a
      ><a name="7132"
      >
    </a
      ><a name="7137" href="Maps.html#7137" class="Postulate"
      >update-shadow</a
      ><a name="7150"
      > </a
      ><a name="7151" class="Symbol"
      >:</a
      ><a name="7152"
      > </a
      ><a name="7153" class="Symbol"
      >&#8704;</a
      ><a name="7154"
      > </a
      ><a name="7165" class="Symbol"
      >(</a
      ><a name="7166" href="Maps.html#7166" class="Bound"
      >m</a
      ><a name="7167"
      > </a
      ><a name="7168" class="Symbol"
      >:</a
      ><a name="7169"
      > </a
      ><a name="7170" href="Maps.html#3384" class="Function"
      >TotalMap</a
      ><a name="7178"
      > </a
      ><a name="7179" href="Maps.html#7156" class="Bound"
      >A</a
      ><a name="7180" class="Symbol"
      >)</a
      ><a name="7181"
      > </a
      ><a name="7182" class="Symbol"
      >(</a
      ><a name="7183" href="Maps.html#7183" class="Bound"
      >x</a
      ><a name="7184"
      > </a
      ><a name="7185" href="Maps.html#7185" class="Bound"
      >y</a
      ><a name="7186"
      > </a
      ><a name="7187" class="Symbol"
      >:</a
      ><a name="7188"
      > </a
      ><a name="7189" href="Maps.html#2275" class="Datatype"
      >Id</a
      ><a name="7191" class="Symbol"
      >)</a
      ><a name="7192"
      >
                  </a
      ><a name="7211" class="Symbol"
      >&#8594;</a
      ><a name="7212"
      > </a
      ><a name="7213" class="Symbol"
      >(</a
      ><a name="7214" href="Maps.html#4054" class="Function"
      >update</a
      ><a name="7220"
      > </a
      ><a name="7221" class="Symbol"
      >(</a
      ><a name="7222" href="Maps.html#4054" class="Function"
      >update</a
      ><a name="7228"
      > </a
      ><a name="7229" href="Maps.html#7166" class="Bound"
      >m</a
      ><a name="7230"
      > </a
      ><a name="7231" href="Maps.html#7183" class="Bound"
      >x</a
      ><a name="7232"
      > </a
      ><a name="7233" href="Maps.html#7158" class="Bound"
      >v1</a
      ><a name="7235" class="Symbol"
      >)</a
      ><a name="7236"
      > </a
      ><a name="7237" href="Maps.html#7183" class="Bound"
      >x</a
      ><a name="7238"
      > </a
      ><a name="7239" href="Maps.html#7161" class="Bound"
      >v2</a
      ><a name="7241" class="Symbol"
      >)</a
      ><a name="7242"
      > </a
      ><a name="7243" href="Maps.html#7185" class="Bound"
      >y</a
      ><a name="7244"
      > </a
      ><a name="7245" href="Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="7246"
      > </a
      ><a name="7247" class="Symbol"
      >(</a
      ><a name="7248" href="Maps.html#4054" class="Function"
      >update</a
      ><a name="7254"
      > </a
      ><a name="7255" href="Maps.html#7166" class="Bound"
      >m</a
      ><a name="7256"
      > </a
      ><a name="7257" href="Maps.html#7183" class="Bound"
      >x</a
      ><a name="7258"
      > </a
      ><a name="7259" href="Maps.html#7161" class="Bound"
      >v2</a
      ><a name="7261" class="Symbol"
      >)</a
      ><a name="7262"
      > </a
      ><a name="7263" href="Maps.html#7185" class="Bound"
      >y</a
      >
{% endraw %}</pre>

<div class="hidden">
<pre class="Agda">{% raw %}
  <a name="7313" href="Maps.html#7313" class="Function"
      >update-shadow&#8242;</a
      ><a name="7327"
      > </a
      ><a name="7328" class="Symbol"
      >:</a
      ><a name="7329"
      > </a
      ><a name="7330" class="Symbol"
      >&#8704;</a
      ><a name="7331"
      > </a
      ><a name="7342" class="Symbol"
      >(</a
      ><a name="7343" href="Maps.html#7343" class="Bound"
      >m</a
      ><a name="7344"
      > </a
      ><a name="7345" class="Symbol"
      >:</a
      ><a name="7346"
      > </a
      ><a name="7347" href="Maps.html#3384" class="Function"
      >TotalMap</a
      ><a name="7355"
      > </a
      ><a name="7356" href="Maps.html#7333" class="Bound"
      >A</a
      ><a name="7357" class="Symbol"
      >)</a
      ><a name="7358"
      > </a
      ><a name="7359" class="Symbol"
      >(</a
      ><a name="7360" href="Maps.html#7360" class="Bound"
      >x</a
      ><a name="7361"
      > </a
      ><a name="7362" href="Maps.html#7362" class="Bound"
      >y</a
      ><a name="7363"
      > </a
      ><a name="7364" class="Symbol"
      >:</a
      ><a name="7365"
      > </a
      ><a name="7366" href="Maps.html#2275" class="Datatype"
      >Id</a
      ><a name="7368" class="Symbol"
      >)</a
      ><a name="7369"
      >
                 </a
      ><a name="7387" class="Symbol"
      >&#8594;</a
      ><a name="7388"
      > </a
      ><a name="7389" class="Symbol"
      >(</a
      ><a name="7390" href="Maps.html#4054" class="Function"
      >update</a
      ><a name="7396"
      > </a
      ><a name="7397" class="Symbol"
      >(</a
      ><a name="7398" href="Maps.html#4054" class="Function"
      >update</a
      ><a name="7404"
      > </a
      ><a name="7405" href="Maps.html#7343" class="Bound"
      >m</a
      ><a name="7406"
      > </a
      ><a name="7407" href="Maps.html#7360" class="Bound"
      >x</a
      ><a name="7408"
      > </a
      ><a name="7409" href="Maps.html#7335" class="Bound"
      >v1</a
      ><a name="7411" class="Symbol"
      >)</a
      ><a name="7412"
      > </a
      ><a name="7413" href="Maps.html#7360" class="Bound"
      >x</a
      ><a name="7414"
      > </a
      ><a name="7415" href="Maps.html#7338" class="Bound"
      >v2</a
      ><a name="7417" class="Symbol"
      >)</a
      ><a name="7418"
      > </a
      ><a name="7419" href="Maps.html#7362" class="Bound"
      >y</a
      ><a name="7420"
      > </a
      ><a name="7421" href="Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="7422"
      > </a
      ><a name="7423" class="Symbol"
      >(</a
      ><a name="7424" href="Maps.html#4054" class="Function"
      >update</a
      ><a name="7430"
      > </a
      ><a name="7431" href="Maps.html#7343" class="Bound"
      >m</a
      ><a name="7432"
      > </a
      ><a name="7433" href="Maps.html#7360" class="Bound"
      >x</a
      ><a name="7434"
      > </a
      ><a name="7435" href="Maps.html#7338" class="Bound"
      >v2</a
      ><a name="7437" class="Symbol"
      >)</a
      ><a name="7438"
      > </a
      ><a name="7439" href="Maps.html#7362" class="Bound"
      >y</a
      ><a name="7440"
      >
  </a
      ><a name="7443" href="Maps.html#7313" class="Function"
      >update-shadow&#8242;</a
      ><a name="7457"
      > </a
      ><a name="7458" href="Maps.html#7458" class="Bound"
      >m</a
      ><a name="7459"
      > </a
      ><a name="7460" href="Maps.html#7460" class="Bound"
      >x</a
      ><a name="7461"
      > </a
      ><a name="7462" href="Maps.html#7462" class="Bound"
      >y</a
      ><a name="7463"
      >
      </a
      ><a name="7470" class="Keyword"
      >with</a
      ><a name="7474"
      > </a
      ><a name="7475" href="Maps.html#7460" class="Bound"
      >x</a
      ><a name="7476"
      > </a
      ><a name="7477" href="Maps.html#2329" class="Function Operator"
      >&#8799;</a
      ><a name="7478"
      > </a
      ><a name="7479" href="Maps.html#7462" class="Bound"
      >y</a
      ><a name="7480"
      >
  </a
      ><a name="7483" class="Symbol"
      >...</a
      ><a name="7486"
      > </a
      ><a name="7487" class="Symbol"
      >|</a
      ><a name="7488"
      > </a
      ><a name="7489" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#520" class="InductiveConstructor"
      >yes</a
      ><a name="7492"
      > </a
      ><a name="7493" href="Maps.html#7493" class="Bound"
      >x=y</a
      ><a name="7496"
      > </a
      ><a name="7497" class="Symbol"
      >=</a
      ><a name="7498"
      > </a
      ><a name="7499" href="Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="7503"
      >
  </a
      ><a name="7506" class="Symbol"
      >...</a
      ><a name="7509"
      > </a
      ><a name="7510" class="Symbol"
      >|</a
      ><a name="7511"
      > </a
      ><a name="7512" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#547" class="InductiveConstructor"
      >no</a
      ><a name="7514"
      >  </a
      ><a name="7516" href="Maps.html#7516" class="Bound"
      >x&#8800;y</a
      ><a name="7519"
      > </a
      ><a name="7520" class="Symbol"
      >=</a
      ><a name="7521"
      > </a
      ><a name="7522" href="Maps.html#6565" class="Function"
      >update-neq</a
      ><a name="7532"
      > </a
      ><a name="7533" href="Maps.html#7458" class="Bound"
      >m</a
      ><a name="7534"
      > </a
      ><a name="7535" href="Maps.html#7460" class="Bound"
      >x</a
      ><a name="7536"
      > </a
      ><a name="7537" href="Maps.html#7462" class="Bound"
      >y</a
      ><a name="7538"
      > </a
      ><a name="7539" href="Maps.html#7516" class="Bound"
      >x&#8800;y</a
      >
{% endraw %}</pre>
</div>

#### Exercise: 2 stars (update-same)
Prove the following theorem, which states that if we update a map to
assign key $$x$$ the same value as it already has in $$m$$, then the
result is equal to $$m$$:

<pre class="Agda">{% raw %}
  <a name="7779" class="Keyword"
      >postulate</a
      ><a name="7788"
      >
    </a
      ><a name="7793" href="Maps.html#7793" class="Postulate"
      >update-same</a
      ><a name="7804"
      > </a
      ><a name="7805" class="Symbol"
      >:</a
      ><a name="7806"
      > </a
      ><a name="7807" class="Symbol"
      >&#8704;</a
      ><a name="7808"
      > </a
      ><a name="7813" class="Symbol"
      >(</a
      ><a name="7814" href="Maps.html#7814" class="Bound"
      >m</a
      ><a name="7815"
      > </a
      ><a name="7816" class="Symbol"
      >:</a
      ><a name="7817"
      > </a
      ><a name="7818" href="Maps.html#3384" class="Function"
      >TotalMap</a
      ><a name="7826"
      > </a
      ><a name="7827" href="Maps.html#7810" class="Bound"
      >A</a
      ><a name="7828" class="Symbol"
      >)</a
      ><a name="7829"
      > </a
      ><a name="7830" class="Symbol"
      >(</a
      ><a name="7831" href="Maps.html#7831" class="Bound"
      >x</a
      ><a name="7832"
      > </a
      ><a name="7833" href="Maps.html#7833" class="Bound"
      >y</a
      ><a name="7834"
      > </a
      ><a name="7835" class="Symbol"
      >:</a
      ><a name="7836"
      > </a
      ><a name="7837" href="Maps.html#2275" class="Datatype"
      >Id</a
      ><a name="7839" class="Symbol"
      >)</a
      ><a name="7840"
      >
                </a
      ><a name="7857" class="Symbol"
      >&#8594;</a
      ><a name="7858"
      > </a
      ><a name="7859" class="Symbol"
      >(</a
      ><a name="7860" href="Maps.html#4054" class="Function"
      >update</a
      ><a name="7866"
      > </a
      ><a name="7867" href="Maps.html#7814" class="Bound"
      >m</a
      ><a name="7868"
      > </a
      ><a name="7869" href="Maps.html#7831" class="Bound"
      >x</a
      ><a name="7870"
      > </a
      ><a name="7871" class="Symbol"
      >(</a
      ><a name="7872" href="Maps.html#7814" class="Bound"
      >m</a
      ><a name="7873"
      > </a
      ><a name="7874" href="Maps.html#7831" class="Bound"
      >x</a
      ><a name="7875" class="Symbol"
      >))</a
      ><a name="7877"
      > </a
      ><a name="7878" href="Maps.html#7833" class="Bound"
      >y</a
      ><a name="7879"
      > </a
      ><a name="7880" href="Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="7881"
      > </a
      ><a name="7882" href="Maps.html#7814" class="Bound"
      >m</a
      ><a name="7883"
      > </a
      ><a name="7884" href="Maps.html#7833" class="Bound"
      >y</a
      >
{% endraw %}</pre>

<div class="hidden">
<pre class="Agda">{% raw %}
  <a name="7934" href="Maps.html#7934" class="Function"
      >update-same&#8242;</a
      ><a name="7946"
      > </a
      ><a name="7947" class="Symbol"
      >:</a
      ><a name="7948"
      > </a
      ><a name="7949" class="Symbol"
      >&#8704;</a
      ><a name="7950"
      > </a
      ><a name="7955" class="Symbol"
      >(</a
      ><a name="7956" href="Maps.html#7956" class="Bound"
      >m</a
      ><a name="7957"
      > </a
      ><a name="7958" class="Symbol"
      >:</a
      ><a name="7959"
      > </a
      ><a name="7960" href="Maps.html#3384" class="Function"
      >TotalMap</a
      ><a name="7968"
      > </a
      ><a name="7969" href="Maps.html#7952" class="Bound"
      >A</a
      ><a name="7970" class="Symbol"
      >)</a
      ><a name="7971"
      > </a
      ><a name="7972" class="Symbol"
      >(</a
      ><a name="7973" href="Maps.html#7973" class="Bound"
      >x</a
      ><a name="7974"
      > </a
      ><a name="7975" href="Maps.html#7975" class="Bound"
      >y</a
      ><a name="7976"
      > </a
      ><a name="7977" class="Symbol"
      >:</a
      ><a name="7978"
      > </a
      ><a name="7979" href="Maps.html#2275" class="Datatype"
      >Id</a
      ><a name="7981" class="Symbol"
      >)</a
      ><a name="7982"
      >
               </a
      ><a name="7998" class="Symbol"
      >&#8594;</a
      ><a name="7999"
      > </a
      ><a name="8000" class="Symbol"
      >(</a
      ><a name="8001" href="Maps.html#4054" class="Function"
      >update</a
      ><a name="8007"
      > </a
      ><a name="8008" href="Maps.html#7956" class="Bound"
      >m</a
      ><a name="8009"
      > </a
      ><a name="8010" href="Maps.html#7973" class="Bound"
      >x</a
      ><a name="8011"
      > </a
      ><a name="8012" class="Symbol"
      >(</a
      ><a name="8013" href="Maps.html#7956" class="Bound"
      >m</a
      ><a name="8014"
      > </a
      ><a name="8015" href="Maps.html#7973" class="Bound"
      >x</a
      ><a name="8016" class="Symbol"
      >))</a
      ><a name="8018"
      > </a
      ><a name="8019" href="Maps.html#7975" class="Bound"
      >y</a
      ><a name="8020"
      > </a
      ><a name="8021" href="Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="8022"
      > </a
      ><a name="8023" href="Maps.html#7956" class="Bound"
      >m</a
      ><a name="8024"
      > </a
      ><a name="8025" href="Maps.html#7975" class="Bound"
      >y</a
      ><a name="8026"
      >
  </a
      ><a name="8029" href="Maps.html#7934" class="Function"
      >update-same&#8242;</a
      ><a name="8041"
      > </a
      ><a name="8042" href="Maps.html#8042" class="Bound"
      >m</a
      ><a name="8043"
      > </a
      ><a name="8044" href="Maps.html#8044" class="Bound"
      >x</a
      ><a name="8045"
      > </a
      ><a name="8046" href="Maps.html#8046" class="Bound"
      >y</a
      ><a name="8047"
      >
    </a
      ><a name="8052" class="Keyword"
      >with</a
      ><a name="8056"
      > </a
      ><a name="8057" href="Maps.html#8044" class="Bound"
      >x</a
      ><a name="8058"
      > </a
      ><a name="8059" href="Maps.html#2329" class="Function Operator"
      >&#8799;</a
      ><a name="8060"
      > </a
      ><a name="8061" href="Maps.html#8046" class="Bound"
      >y</a
      ><a name="8062"
      >
  </a
      ><a name="8065" class="Symbol"
      >...</a
      ><a name="8068"
      > </a
      ><a name="8069" class="Symbol"
      >|</a
      ><a name="8070"
      > </a
      ><a name="8071" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#520" class="InductiveConstructor"
      >yes</a
      ><a name="8074"
      > </a
      ><a name="8075" href="Maps.html#8075" class="Bound"
      >x=y</a
      ><a name="8078"
      > </a
      ><a name="8079" class="Keyword"
      >rewrite</a
      ><a name="8086"
      > </a
      ><a name="8087" href="Maps.html#8075" class="Bound"
      >x=y</a
      ><a name="8090"
      > </a
      ><a name="8091" class="Symbol"
      >=</a
      ><a name="8092"
      > </a
      ><a name="8093" href="Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="8097"
      >
  </a
      ><a name="8100" class="Symbol"
      >...</a
      ><a name="8103"
      > </a
      ><a name="8104" class="Symbol"
      >|</a
      ><a name="8105"
      > </a
      ><a name="8106" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#547" class="InductiveConstructor"
      >no</a
      ><a name="8108"
      >  </a
      ><a name="8110" href="Maps.html#8110" class="Bound"
      >x&#8800;y</a
      ><a name="8113"
      > </a
      ><a name="8114" class="Symbol"
      >=</a
      ><a name="8115"
      > </a
      ><a name="8116" href="Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      >
{% endraw %}</pre>
</div>

#### Exercise: 3 stars, recommended (update-permute)
Prove one final property of the `update` function: If we update a map
$$m$$ at two distinct keys, it doesn't matter in which order we do the
updates.

<pre class="Agda">{% raw %}
  <a name="8359" class="Keyword"
      >postulate</a
      ><a name="8368"
      >
    </a
      ><a name="8373" href="Maps.html#8373" class="Postulate"
      >update-permute</a
      ><a name="8387"
      > </a
      ><a name="8388" class="Symbol"
      >:</a
      ><a name="8389"
      > </a
      ><a name="8390" class="Symbol"
      >&#8704;</a
      ><a name="8391"
      > </a
      ><a name="8402" class="Symbol"
      >(</a
      ><a name="8403" href="Maps.html#8403" class="Bound"
      >m</a
      ><a name="8404"
      > </a
      ><a name="8405" class="Symbol"
      >:</a
      ><a name="8406"
      > </a
      ><a name="8407" href="Maps.html#3384" class="Function"
      >TotalMap</a
      ><a name="8415"
      > </a
      ><a name="8416" href="Maps.html#8393" class="Bound"
      >A</a
      ><a name="8417" class="Symbol"
      >)</a
      ><a name="8418"
      > </a
      ><a name="8419" class="Symbol"
      >(</a
      ><a name="8420" href="Maps.html#8420" class="Bound"
      >x1</a
      ><a name="8422"
      > </a
      ><a name="8423" href="Maps.html#8423" class="Bound"
      >x2</a
      ><a name="8425"
      > </a
      ><a name="8426" href="Maps.html#8426" class="Bound"
      >y</a
      ><a name="8427"
      > </a
      ><a name="8428" class="Symbol"
      >:</a
      ><a name="8429"
      > </a
      ><a name="8430" href="Maps.html#2275" class="Datatype"
      >Id</a
      ><a name="8432" class="Symbol"
      >)</a
      ><a name="8433"
      >
                   </a
      ><a name="8453" class="Symbol"
      >&#8594;</a
      ><a name="8454"
      > </a
      ><a name="8455" href="Maps.html#8420" class="Bound"
      >x1</a
      ><a name="8457"
      > </a
      ><a name="8458" href="https://agda.github.io/agda-stdlib/Relation.Binary.Core.html#4493" class="Function Operator"
      >&#8802;</a
      ><a name="8459"
      > </a
      ><a name="8460" href="Maps.html#8423" class="Bound"
      >x2</a
      ><a name="8462"
      > </a
      ><a name="8463" class="Symbol"
      >&#8594;</a
      ><a name="8464"
      > </a
      ><a name="8465" class="Symbol"
      >(</a
      ><a name="8466" href="Maps.html#4054" class="Function"
      >update</a
      ><a name="8472"
      > </a
      ><a name="8473" class="Symbol"
      >(</a
      ><a name="8474" href="Maps.html#4054" class="Function"
      >update</a
      ><a name="8480"
      > </a
      ><a name="8481" href="Maps.html#8403" class="Bound"
      >m</a
      ><a name="8482"
      > </a
      ><a name="8483" href="Maps.html#8423" class="Bound"
      >x2</a
      ><a name="8485"
      > </a
      ><a name="8486" href="Maps.html#8398" class="Bound"
      >v2</a
      ><a name="8488" class="Symbol"
      >)</a
      ><a name="8489"
      > </a
      ><a name="8490" href="Maps.html#8420" class="Bound"
      >x1</a
      ><a name="8492"
      > </a
      ><a name="8493" href="Maps.html#8395" class="Bound"
      >v1</a
      ><a name="8495" class="Symbol"
      >)</a
      ><a name="8496"
      > </a
      ><a name="8497" href="Maps.html#8426" class="Bound"
      >y</a
      ><a name="8498"
      >
                             </a
      ><a name="8528" href="Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="8529"
      > </a
      ><a name="8530" class="Symbol"
      >(</a
      ><a name="8531" href="Maps.html#4054" class="Function"
      >update</a
      ><a name="8537"
      > </a
      ><a name="8538" class="Symbol"
      >(</a
      ><a name="8539" href="Maps.html#4054" class="Function"
      >update</a
      ><a name="8545"
      > </a
      ><a name="8546" href="Maps.html#8403" class="Bound"
      >m</a
      ><a name="8547"
      > </a
      ><a name="8548" href="Maps.html#8420" class="Bound"
      >x1</a
      ><a name="8550"
      > </a
      ><a name="8551" href="Maps.html#8395" class="Bound"
      >v1</a
      ><a name="8553" class="Symbol"
      >)</a
      ><a name="8554"
      > </a
      ><a name="8555" href="Maps.html#8423" class="Bound"
      >x2</a
      ><a name="8557"
      > </a
      ><a name="8558" href="Maps.html#8398" class="Bound"
      >v2</a
      ><a name="8560" class="Symbol"
      >)</a
      ><a name="8561"
      > </a
      ><a name="8562" href="Maps.html#8426" class="Bound"
      >y</a
      >
{% endraw %}</pre>

<div class="hidden">
<pre class="Agda">{% raw %}
  <a name="8612" href="Maps.html#8612" class="Function"
      >update-permute&#8242;</a
      ><a name="8627"
      > </a
      ><a name="8628" class="Symbol"
      >:</a
      ><a name="8629"
      > </a
      ><a name="8630" class="Symbol"
      >&#8704;</a
      ><a name="8631"
      > </a
      ><a name="8642" class="Symbol"
      >(</a
      ><a name="8643" href="Maps.html#8643" class="Bound"
      >m</a
      ><a name="8644"
      > </a
      ><a name="8645" class="Symbol"
      >:</a
      ><a name="8646"
      > </a
      ><a name="8647" href="Maps.html#3384" class="Function"
      >TotalMap</a
      ><a name="8655"
      > </a
      ><a name="8656" href="Maps.html#8633" class="Bound"
      >A</a
      ><a name="8657" class="Symbol"
      >)</a
      ><a name="8658"
      > </a
      ><a name="8659" class="Symbol"
      >(</a
      ><a name="8660" href="Maps.html#8660" class="Bound"
      >x1</a
      ><a name="8662"
      > </a
      ><a name="8663" href="Maps.html#8663" class="Bound"
      >x2</a
      ><a name="8665"
      > </a
      ><a name="8666" href="Maps.html#8666" class="Bound"
      >y</a
      ><a name="8667"
      > </a
      ><a name="8668" class="Symbol"
      >:</a
      ><a name="8669"
      > </a
      ><a name="8670" href="Maps.html#2275" class="Datatype"
      >Id</a
      ><a name="8672" class="Symbol"
      >)</a
      ><a name="8673"
      >
                  </a
      ><a name="8692" class="Symbol"
      >&#8594;</a
      ><a name="8693"
      > </a
      ><a name="8694" href="Maps.html#8660" class="Bound"
      >x1</a
      ><a name="8696"
      > </a
      ><a name="8697" href="https://agda.github.io/agda-stdlib/Relation.Binary.Core.html#4493" class="Function Operator"
      >&#8802;</a
      ><a name="8698"
      > </a
      ><a name="8699" href="Maps.html#8663" class="Bound"
      >x2</a
      ><a name="8701"
      > </a
      ><a name="8702" class="Symbol"
      >&#8594;</a
      ><a name="8703"
      > </a
      ><a name="8704" class="Symbol"
      >(</a
      ><a name="8705" href="Maps.html#4054" class="Function"
      >update</a
      ><a name="8711"
      > </a
      ><a name="8712" class="Symbol"
      >(</a
      ><a name="8713" href="Maps.html#4054" class="Function"
      >update</a
      ><a name="8719"
      > </a
      ><a name="8720" href="Maps.html#8643" class="Bound"
      >m</a
      ><a name="8721"
      > </a
      ><a name="8722" href="Maps.html#8663" class="Bound"
      >x2</a
      ><a name="8724"
      > </a
      ><a name="8725" href="Maps.html#8638" class="Bound"
      >v2</a
      ><a name="8727" class="Symbol"
      >)</a
      ><a name="8728"
      > </a
      ><a name="8729" href="Maps.html#8660" class="Bound"
      >x1</a
      ><a name="8731"
      > </a
      ><a name="8732" href="Maps.html#8635" class="Bound"
      >v1</a
      ><a name="8734" class="Symbol"
      >)</a
      ><a name="8735"
      > </a
      ><a name="8736" href="Maps.html#8666" class="Bound"
      >y</a
      ><a name="8737"
      >
                            </a
      ><a name="8766" href="Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="8767"
      > </a
      ><a name="8768" class="Symbol"
      >(</a
      ><a name="8769" href="Maps.html#4054" class="Function"
      >update</a
      ><a name="8775"
      > </a
      ><a name="8776" class="Symbol"
      >(</a
      ><a name="8777" href="Maps.html#4054" class="Function"
      >update</a
      ><a name="8783"
      > </a
      ><a name="8784" href="Maps.html#8643" class="Bound"
      >m</a
      ><a name="8785"
      > </a
      ><a name="8786" href="Maps.html#8660" class="Bound"
      >x1</a
      ><a name="8788"
      > </a
      ><a name="8789" href="Maps.html#8635" class="Bound"
      >v1</a
      ><a name="8791" class="Symbol"
      >)</a
      ><a name="8792"
      > </a
      ><a name="8793" href="Maps.html#8663" class="Bound"
      >x2</a
      ><a name="8795"
      > </a
      ><a name="8796" href="Maps.html#8638" class="Bound"
      >v2</a
      ><a name="8798" class="Symbol"
      >)</a
      ><a name="8799"
      > </a
      ><a name="8800" href="Maps.html#8666" class="Bound"
      >y</a
      ><a name="8801"
      >
  </a
      ><a name="8804" href="Maps.html#8612" class="Function"
      >update-permute&#8242;</a
      ><a name="8819"
      > </a
      ><a name="8834" href="Maps.html#8834" class="Bound"
      >m</a
      ><a name="8835"
      > </a
      ><a name="8836" href="Maps.html#8836" class="Bound"
      >x1</a
      ><a name="8838"
      > </a
      ><a name="8839" href="Maps.html#8839" class="Bound"
      >x2</a
      ><a name="8841"
      > </a
      ><a name="8842" href="Maps.html#8842" class="Bound"
      >y</a
      ><a name="8843"
      > </a
      ><a name="8844" href="Maps.html#8844" class="Bound"
      >x1&#8800;x2</a
      ><a name="8849"
      >
    </a
      ><a name="8854" class="Keyword"
      >with</a
      ><a name="8858"
      > </a
      ><a name="8859" href="Maps.html#8836" class="Bound"
      >x1</a
      ><a name="8861"
      > </a
      ><a name="8862" href="Maps.html#2329" class="Function Operator"
      >&#8799;</a
      ><a name="8863"
      > </a
      ><a name="8864" href="Maps.html#8842" class="Bound"
      >y</a
      ><a name="8865"
      > </a
      ><a name="8866" class="Symbol"
      >|</a
      ><a name="8867"
      > </a
      ><a name="8868" href="Maps.html#8839" class="Bound"
      >x2</a
      ><a name="8870"
      > </a
      ><a name="8871" href="Maps.html#2329" class="Function Operator"
      >&#8799;</a
      ><a name="8872"
      > </a
      ><a name="8873" href="Maps.html#8842" class="Bound"
      >y</a
      ><a name="8874"
      >
  </a
      ><a name="8877" class="Symbol"
      >...</a
      ><a name="8880"
      > </a
      ><a name="8881" class="Symbol"
      >|</a
      ><a name="8882"
      > </a
      ><a name="8883" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#520" class="InductiveConstructor"
      >yes</a
      ><a name="8886"
      > </a
      ><a name="8887" href="Maps.html#8887" class="Bound"
      >x1=y</a
      ><a name="8891"
      > </a
      ><a name="8892" class="Symbol"
      >|</a
      ><a name="8893"
      > </a
      ><a name="8894" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#520" class="InductiveConstructor"
      >yes</a
      ><a name="8897"
      > </a
      ><a name="8898" href="Maps.html#8898" class="Bound"
      >x2=y</a
      ><a name="8902"
      > </a
      ><a name="8903" class="Symbol"
      >=</a
      ><a name="8904"
      > </a
      ><a name="8905" href="https://agda.github.io/agda-stdlib/Data.Empty.html#348" class="Function"
      >&#8869;-elim</a
      ><a name="8911"
      > </a
      ><a name="8912" class="Symbol"
      >(</a
      ><a name="8913" href="Maps.html#8844" class="Bound"
      >x1&#8800;x2</a
      ><a name="8918"
      > </a
      ><a name="8919" class="Symbol"
      >(</a
      ><a name="8920" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.Core.html#632" class="Function"
      >trans</a
      ><a name="8925"
      > </a
      ><a name="8926" href="Maps.html#8887" class="Bound"
      >x1=y</a
      ><a name="8930"
      > </a
      ><a name="8931" class="Symbol"
      >(</a
      ><a name="8932" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.Core.html#565" class="Function"
      >sym</a
      ><a name="8935"
      > </a
      ><a name="8936" href="Maps.html#8898" class="Bound"
      >x2=y</a
      ><a name="8940" class="Symbol"
      >)))</a
      ><a name="8943"
      >
  </a
      ><a name="8946" class="Symbol"
      >...</a
      ><a name="8949"
      > </a
      ><a name="8950" class="Symbol"
      >|</a
      ><a name="8951"
      > </a
      ><a name="8952" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#547" class="InductiveConstructor"
      >no</a
      ><a name="8954"
      >  </a
      ><a name="8956" href="Maps.html#8956" class="Bound"
      >x1&#8800;y</a
      ><a name="8960"
      > </a
      ><a name="8961" class="Symbol"
      >|</a
      ><a name="8962"
      > </a
      ><a name="8963" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#520" class="InductiveConstructor"
      >yes</a
      ><a name="8966"
      > </a
      ><a name="8967" href="Maps.html#8967" class="Bound"
      >x2=y</a
      ><a name="8971"
      > </a
      ><a name="8972" class="Keyword"
      >rewrite</a
      ><a name="8979"
      > </a
      ><a name="8980" href="Maps.html#8967" class="Bound"
      >x2=y</a
      ><a name="8984"
      > </a
      ><a name="8985" class="Symbol"
      >=</a
      ><a name="8986"
      > </a
      ><a name="8987" href="Maps.html#6140" class="Function"
      >update-eq&#8242;</a
      ><a name="8997"
      > </a
      ><a name="8998" href="Maps.html#8834" class="Bound"
      >m</a
      ><a name="8999"
      > </a
      ><a name="9000" href="Maps.html#8842" class="Bound"
      >y</a
      ><a name="9001"
      >
  </a
      ><a name="9004" class="Symbol"
      >...</a
      ><a name="9007"
      > </a
      ><a name="9008" class="Symbol"
      >|</a
      ><a name="9009"
      > </a
      ><a name="9010" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#520" class="InductiveConstructor"
      >yes</a
      ><a name="9013"
      > </a
      ><a name="9014" href="Maps.html#9014" class="Bound"
      >x1=y</a
      ><a name="9018"
      > </a
      ><a name="9019" class="Symbol"
      >|</a
      ><a name="9020"
      > </a
      ><a name="9021" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#547" class="InductiveConstructor"
      >no</a
      ><a name="9023"
      >  </a
      ><a name="9025" href="Maps.html#9025" class="Bound"
      >x2&#8800;y</a
      ><a name="9029"
      > </a
      ><a name="9030" class="Keyword"
      >rewrite</a
      ><a name="9037"
      > </a
      ><a name="9038" href="Maps.html#9014" class="Bound"
      >x1=y</a
      ><a name="9042"
      > </a
      ><a name="9043" class="Symbol"
      >=</a
      ><a name="9044"
      > </a
      ><a name="9045" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.Core.html#565" class="Function"
      >sym</a
      ><a name="9048"
      > </a
      ><a name="9049" class="Symbol"
      >(</a
      ><a name="9050" href="Maps.html#6140" class="Function"
      >update-eq&#8242;</a
      ><a name="9060"
      > </a
      ><a name="9061" href="Maps.html#8834" class="Bound"
      >m</a
      ><a name="9062"
      > </a
      ><a name="9063" href="Maps.html#8842" class="Bound"
      >y</a
      ><a name="9064" class="Symbol"
      >)</a
      ><a name="9065"
      >
  </a
      ><a name="9068" class="Symbol"
      >...</a
      ><a name="9071"
      > </a
      ><a name="9072" class="Symbol"
      >|</a
      ><a name="9073"
      > </a
      ><a name="9074" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#547" class="InductiveConstructor"
      >no</a
      ><a name="9076"
      >  </a
      ><a name="9078" href="Maps.html#9078" class="Bound"
      >x1&#8800;y</a
      ><a name="9082"
      > </a
      ><a name="9083" class="Symbol"
      >|</a
      ><a name="9084"
      > </a
      ><a name="9085" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#547" class="InductiveConstructor"
      >no</a
      ><a name="9087"
      >  </a
      ><a name="9089" href="Maps.html#9089" class="Bound"
      >x2&#8800;y</a
      ><a name="9093"
      > </a
      ><a name="9094" class="Symbol"
      >=</a
      ><a name="9095"
      >
    </a
      ><a name="9100" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.Core.html#632" class="Function"
      >trans</a
      ><a name="9105"
      > </a
      ><a name="9106" class="Symbol"
      >(</a
      ><a name="9107" href="Maps.html#6565" class="Function"
      >update-neq</a
      ><a name="9117"
      > </a
      ><a name="9118" href="Maps.html#8834" class="Bound"
      >m</a
      ><a name="9119"
      > </a
      ><a name="9120" href="Maps.html#8839" class="Bound"
      >x2</a
      ><a name="9122"
      > </a
      ><a name="9123" href="Maps.html#8842" class="Bound"
      >y</a
      ><a name="9124"
      > </a
      ><a name="9125" href="Maps.html#9089" class="Bound"
      >x2&#8800;y</a
      ><a name="9129" class="Symbol"
      >)</a
      ><a name="9130"
      > </a
      ><a name="9131" class="Symbol"
      >(</a
      ><a name="9132" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.Core.html#565" class="Function"
      >sym</a
      ><a name="9135"
      > </a
      ><a name="9136" class="Symbol"
      >(</a
      ><a name="9137" href="Maps.html#6565" class="Function"
      >update-neq</a
      ><a name="9147"
      > </a
      ><a name="9148" href="Maps.html#8834" class="Bound"
      >m</a
      ><a name="9149"
      > </a
      ><a name="9150" href="Maps.html#8836" class="Bound"
      >x1</a
      ><a name="9152"
      > </a
      ><a name="9153" href="Maps.html#8842" class="Bound"
      >y</a
      ><a name="9154"
      > </a
      ><a name="9155" href="Maps.html#9078" class="Bound"
      >x1&#8800;y</a
      ><a name="9159" class="Symbol"
      >))</a
      >
{% endraw %}</pre>
</div>

## Partial maps

Finally, we define _partial maps_ on top of total maps.  A partial
map with elements of type `A` is simply a total map with elements
of type `Maybe A` and default element `nothing`.

<pre class="Agda">{% raw %}
<a name="9394" href="Maps.html#9394" class="Function"
      >PartialMap</a
      ><a name="9404"
      > </a
      ><a name="9405" class="Symbol"
      >:</a
      ><a name="9406"
      > </a
      ><a name="9407" class="PrimitiveType"
      >Set</a
      ><a name="9410"
      > </a
      ><a name="9411" class="Symbol"
      >&#8594;</a
      ><a name="9412"
      > </a
      ><a name="9413" class="PrimitiveType"
      >Set</a
      ><a name="9416"
      >
</a
      ><a name="9417" href="Maps.html#9394" class="Function"
      >PartialMap</a
      ><a name="9427"
      > </a
      ><a name="9428" href="Maps.html#9428" class="Bound"
      >A</a
      ><a name="9429"
      > </a
      ><a name="9430" class="Symbol"
      >=</a
      ><a name="9431"
      > </a
      ><a name="9432" href="Maps.html#3384" class="Function"
      >TotalMap</a
      ><a name="9440"
      > </a
      ><a name="9441" class="Symbol"
      >(</a
      ><a name="9442" href="https://agda.github.io/agda-stdlib/Data.Maybe.Base.html#335" class="Datatype"
      >Maybe</a
      ><a name="9447"
      > </a
      ><a name="9448" href="Maps.html#9428" class="Bound"
      >A</a
      ><a name="9449" class="Symbol"
      >)</a
      >
{% endraw %}</pre>

<pre class="Agda">{% raw %}
<a name="9476" class="Keyword"
      >module</a
      ><a name="9482"
      > </a
      ><a name="9483" href="Maps.html#9483" class="Module"
      >PartialMap</a
      ><a name="9493"
      > </a
      ><a name="9494" class="Keyword"
      >where</a
      >
{% endraw %}</pre>

<pre class="Agda">{% raw %}
  <a name="9527" href="Maps.html#9527" class="Function"
      >empty</a
      ><a name="9532"
      > </a
      ><a name="9533" class="Symbol"
      >:</a
      ><a name="9534"
      > </a
      ><a name="9535" class="Symbol"
      >&#8704;</a
      ><a name="9536"
      > </a
      ><a name="9541" class="Symbol"
      >&#8594;</a
      ><a name="9542"
      > </a
      ><a name="9543" href="Maps.html#9394" class="Function"
      >PartialMap</a
      ><a name="9553"
      > </a
      ><a name="9554" href="Maps.html#9538" class="Bound"
      >A</a
      ><a name="9555"
      >
  </a
      ><a name="9558" href="Maps.html#9527" class="Function"
      >empty</a
      ><a name="9563"
      > </a
      ><a name="9564" class="Symbol"
      >=</a
      ><a name="9565"
      > </a
      ><a name="9566" href="Maps.html#3766" class="Function"
      >TotalMap.empty</a
      ><a name="9580"
      > </a
      ><a name="9581" href="https://agda.github.io/agda-stdlib/Data.Maybe.Base.html#403" class="InductiveConstructor"
      >nothing</a
      >
{% endraw %}</pre>

<pre class="Agda">{% raw %}
  <a name="9616" href="Maps.html#9616" class="Function"
      >update</a
      ><a name="9622"
      > </a
      ><a name="9623" class="Symbol"
      >:</a
      ><a name="9624"
      > </a
      ><a name="9625" class="Symbol"
      >&#8704;</a
      ><a name="9626"
      > </a
      ><a name="9631" class="Symbol"
      >(</a
      ><a name="9632" href="Maps.html#9632" class="Bound"
      >m</a
      ><a name="9633"
      > </a
      ><a name="9634" class="Symbol"
      >:</a
      ><a name="9635"
      > </a
      ><a name="9636" href="Maps.html#9394" class="Function"
      >PartialMap</a
      ><a name="9646"
      > </a
      ><a name="9647" href="Maps.html#9628" class="Bound"
      >A</a
      ><a name="9648" class="Symbol"
      >)</a
      ><a name="9649"
      > </a
      ><a name="9650" class="Symbol"
      >(</a
      ><a name="9651" href="Maps.html#9651" class="Bound"
      >x</a
      ><a name="9652"
      > </a
      ><a name="9653" class="Symbol"
      >:</a
      ><a name="9654"
      > </a
      ><a name="9655" href="Maps.html#2275" class="Datatype"
      >Id</a
      ><a name="9657" class="Symbol"
      >)</a
      ><a name="9658"
      > </a
      ><a name="9659" class="Symbol"
      >(</a
      ><a name="9660" href="Maps.html#9660" class="Bound"
      >v</a
      ><a name="9661"
      > </a
      ><a name="9662" class="Symbol"
      >:</a
      ><a name="9663"
      > </a
      ><a name="9664" href="Maps.html#9628" class="Bound"
      >A</a
      ><a name="9665" class="Symbol"
      >)</a
      ><a name="9666"
      > </a
      ><a name="9667" class="Symbol"
      >&#8594;</a
      ><a name="9668"
      > </a
      ><a name="9669" href="Maps.html#9394" class="Function"
      >PartialMap</a
      ><a name="9679"
      > </a
      ><a name="9680" href="Maps.html#9628" class="Bound"
      >A</a
      ><a name="9681"
      >
  </a
      ><a name="9684" href="Maps.html#9616" class="Function"
      >update</a
      ><a name="9690"
      > </a
      ><a name="9691" href="Maps.html#9691" class="Bound"
      >m</a
      ><a name="9692"
      > </a
      ><a name="9693" href="Maps.html#9693" class="Bound"
      >x</a
      ><a name="9694"
      > </a
      ><a name="9695" href="Maps.html#9695" class="Bound"
      >v</a
      ><a name="9696"
      > </a
      ><a name="9697" class="Symbol"
      >=</a
      ><a name="9698"
      > </a
      ><a name="9699" href="Maps.html#4054" class="Function"
      >TotalMap.update</a
      ><a name="9714"
      > </a
      ><a name="9715" href="Maps.html#9691" class="Bound"
      >m</a
      ><a name="9716"
      > </a
      ><a name="9717" href="Maps.html#9693" class="Bound"
      >x</a
      ><a name="9718"
      > </a
      ><a name="9719" class="Symbol"
      >(</a
      ><a name="9720" href="https://agda.github.io/agda-stdlib/Data.Maybe.Base.html#373" class="InductiveConstructor"
      >just</a
      ><a name="9724"
      > </a
      ><a name="9725" href="Maps.html#9695" class="Bound"
      >v</a
      ><a name="9726" class="Symbol"
      >)</a
      >
{% endraw %}</pre>

We can now lift all of the basic lemmas about total maps to
partial maps.

<pre class="Agda">{% raw %}
  <a name="9830" href="Maps.html#9830" class="Function"
      >update-eq</a
      ><a name="9839"
      > </a
      ><a name="9840" class="Symbol"
      >:</a
      ><a name="9841"
      > </a
      ><a name="9842" class="Symbol"
      >&#8704;</a
      ><a name="9843"
      > </a
      ><a name="9850" class="Symbol"
      >(</a
      ><a name="9851" href="Maps.html#9851" class="Bound"
      >m</a
      ><a name="9852"
      > </a
      ><a name="9853" class="Symbol"
      >:</a
      ><a name="9854"
      > </a
      ><a name="9855" href="Maps.html#9394" class="Function"
      >PartialMap</a
      ><a name="9865"
      > </a
      ><a name="9866" href="Maps.html#9845" class="Bound"
      >A</a
      ><a name="9867" class="Symbol"
      >)</a
      ><a name="9868"
      > </a
      ><a name="9869" class="Symbol"
      >(</a
      ><a name="9870" href="Maps.html#9870" class="Bound"
      >x</a
      ><a name="9871"
      > </a
      ><a name="9872" class="Symbol"
      >:</a
      ><a name="9873"
      > </a
      ><a name="9874" href="Maps.html#2275" class="Datatype"
      >Id</a
      ><a name="9876" class="Symbol"
      >)</a
      ><a name="9877"
      >
            </a
      ><a name="9890" class="Symbol"
      >&#8594;</a
      ><a name="9891"
      > </a
      ><a name="9892" class="Symbol"
      >(</a
      ><a name="9893" href="Maps.html#9616" class="Function"
      >update</a
      ><a name="9899"
      > </a
      ><a name="9900" href="Maps.html#9851" class="Bound"
      >m</a
      ><a name="9901"
      > </a
      ><a name="9902" href="Maps.html#9870" class="Bound"
      >x</a
      ><a name="9903"
      > </a
      ><a name="9904" href="Maps.html#9847" class="Bound"
      >v</a
      ><a name="9905" class="Symbol"
      >)</a
      ><a name="9906"
      > </a
      ><a name="9907" href="Maps.html#9870" class="Bound"
      >x</a
      ><a name="9908"
      > </a
      ><a name="9909" href="Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="9910"
      > </a
      ><a name="9911" href="https://agda.github.io/agda-stdlib/Data.Maybe.Base.html#373" class="InductiveConstructor"
      >just</a
      ><a name="9915"
      > </a
      ><a name="9916" href="Maps.html#9847" class="Bound"
      >v</a
      ><a name="9917"
      >
  </a
      ><a name="9920" href="Maps.html#9830" class="Function"
      >update-eq</a
      ><a name="9929"
      > </a
      ><a name="9930" href="Maps.html#9930" class="Bound"
      >m</a
      ><a name="9931"
      > </a
      ><a name="9932" href="Maps.html#9932" class="Bound"
      >x</a
      ><a name="9933"
      > </a
      ><a name="9934" class="Symbol"
      >=</a
      ><a name="9935"
      > </a
      ><a name="9936" href="Maps.html#6009" class="Postulate"
      >TotalMap.update-eq</a
      ><a name="9954"
      > </a
      ><a name="9955" href="Maps.html#9930" class="Bound"
      >m</a
      ><a name="9956"
      > </a
      ><a name="9957" href="Maps.html#9932" class="Bound"
      >x</a
      >
{% endraw %}</pre>

<pre class="Agda">{% raw %}
  <a name="9986" href="Maps.html#9986" class="Function"
      >update-neq</a
      ><a name="9996"
      > </a
      ><a name="9997" class="Symbol"
      >:</a
      ><a name="9998"
      > </a
      ><a name="9999" class="Symbol"
      >&#8704;</a
      ><a name="10000"
      > </a
      ><a name="10007" class="Symbol"
      >(</a
      ><a name="10008" href="Maps.html#10008" class="Bound"
      >m</a
      ><a name="10009"
      > </a
      ><a name="10010" class="Symbol"
      >:</a
      ><a name="10011"
      > </a
      ><a name="10012" href="Maps.html#9394" class="Function"
      >PartialMap</a
      ><a name="10022"
      > </a
      ><a name="10023" href="Maps.html#10002" class="Bound"
      >A</a
      ><a name="10024" class="Symbol"
      >)</a
      ><a name="10025"
      > </a
      ><a name="10026" class="Symbol"
      >(</a
      ><a name="10027" href="Maps.html#10027" class="Bound"
      >x</a
      ><a name="10028"
      > </a
      ><a name="10029" href="Maps.html#10029" class="Bound"
      >y</a
      ><a name="10030"
      > </a
      ><a name="10031" class="Symbol"
      >:</a
      ><a name="10032"
      > </a
      ><a name="10033" href="Maps.html#2275" class="Datatype"
      >Id</a
      ><a name="10035" class="Symbol"
      >)</a
      ><a name="10036"
      >
             </a
      ><a name="10050" class="Symbol"
      >&#8594;</a
      ><a name="10051"
      > </a
      ><a name="10052" href="Maps.html#10027" class="Bound"
      >x</a
      ><a name="10053"
      > </a
      ><a name="10054" href="https://agda.github.io/agda-stdlib/Relation.Binary.Core.html#4493" class="Function Operator"
      >&#8802;</a
      ><a name="10055"
      > </a
      ><a name="10056" href="Maps.html#10029" class="Bound"
      >y</a
      ><a name="10057"
      > </a
      ><a name="10058" class="Symbol"
      >&#8594;</a
      ><a name="10059"
      > </a
      ><a name="10060" class="Symbol"
      >(</a
      ><a name="10061" href="Maps.html#9616" class="Function"
      >update</a
      ><a name="10067"
      > </a
      ><a name="10068" href="Maps.html#10008" class="Bound"
      >m</a
      ><a name="10069"
      > </a
      ><a name="10070" href="Maps.html#10027" class="Bound"
      >x</a
      ><a name="10071"
      > </a
      ><a name="10072" href="Maps.html#10004" class="Bound"
      >v</a
      ><a name="10073" class="Symbol"
      >)</a
      ><a name="10074"
      > </a
      ><a name="10075" href="Maps.html#10029" class="Bound"
      >y</a
      ><a name="10076"
      > </a
      ><a name="10077" href="Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="10078"
      > </a
      ><a name="10079" href="Maps.html#10008" class="Bound"
      >m</a
      ><a name="10080"
      > </a
      ><a name="10081" href="Maps.html#10029" class="Bound"
      >y</a
      ><a name="10082"
      >
  </a
      ><a name="10085" href="Maps.html#9986" class="Function"
      >update-neq</a
      ><a name="10095"
      > </a
      ><a name="10096" href="Maps.html#10096" class="Bound"
      >m</a
      ><a name="10097"
      > </a
      ><a name="10098" href="Maps.html#10098" class="Bound"
      >x</a
      ><a name="10099"
      > </a
      ><a name="10100" href="Maps.html#10100" class="Bound"
      >y</a
      ><a name="10101"
      > </a
      ><a name="10102" href="Maps.html#10102" class="Bound"
      >x&#8800;y</a
      ><a name="10105"
      > </a
      ><a name="10106" class="Symbol"
      >=</a
      ><a name="10107"
      > </a
      ><a name="10108" href="Maps.html#6565" class="Function"
      >TotalMap.update-neq</a
      ><a name="10127"
      > </a
      ><a name="10128" href="Maps.html#10096" class="Bound"
      >m</a
      ><a name="10129"
      > </a
      ><a name="10130" href="Maps.html#10098" class="Bound"
      >x</a
      ><a name="10131"
      > </a
      ><a name="10132" href="Maps.html#10100" class="Bound"
      >y</a
      ><a name="10133"
      > </a
      ><a name="10134" href="Maps.html#10102" class="Bound"
      >x&#8800;y</a
      >
{% endraw %}</pre>

<pre class="Agda">{% raw %}
  <a name="10165" href="Maps.html#10165" class="Function"
      >update-shadow</a
      ><a name="10178"
      > </a
      ><a name="10179" class="Symbol"
      >:</a
      ><a name="10180"
      > </a
      ><a name="10181" class="Symbol"
      >&#8704;</a
      ><a name="10182"
      > </a
      ><a name="10193" class="Symbol"
      >(</a
      ><a name="10194" href="Maps.html#10194" class="Bound"
      >m</a
      ><a name="10195"
      > </a
      ><a name="10196" class="Symbol"
      >:</a
      ><a name="10197"
      > </a
      ><a name="10198" href="Maps.html#9394" class="Function"
      >PartialMap</a
      ><a name="10208"
      > </a
      ><a name="10209" href="Maps.html#10184" class="Bound"
      >A</a
      ><a name="10210" class="Symbol"
      >)</a
      ><a name="10211"
      > </a
      ><a name="10212" class="Symbol"
      >(</a
      ><a name="10213" href="Maps.html#10213" class="Bound"
      >x</a
      ><a name="10214"
      > </a
      ><a name="10215" href="Maps.html#10215" class="Bound"
      >y</a
      ><a name="10216"
      > </a
      ><a name="10217" class="Symbol"
      >:</a
      ><a name="10218"
      > </a
      ><a name="10219" href="Maps.html#2275" class="Datatype"
      >Id</a
      ><a name="10221" class="Symbol"
      >)</a
      ><a name="10222"
      >
                </a
      ><a name="10239" class="Symbol"
      >&#8594;</a
      ><a name="10240"
      > </a
      ><a name="10241" class="Symbol"
      >(</a
      ><a name="10242" href="Maps.html#9616" class="Function"
      >update</a
      ><a name="10248"
      > </a
      ><a name="10249" class="Symbol"
      >(</a
      ><a name="10250" href="Maps.html#9616" class="Function"
      >update</a
      ><a name="10256"
      > </a
      ><a name="10257" href="Maps.html#10194" class="Bound"
      >m</a
      ><a name="10258"
      > </a
      ><a name="10259" href="Maps.html#10213" class="Bound"
      >x</a
      ><a name="10260"
      > </a
      ><a name="10261" href="Maps.html#10186" class="Bound"
      >v1</a
      ><a name="10263" class="Symbol"
      >)</a
      ><a name="10264"
      > </a
      ><a name="10265" href="Maps.html#10213" class="Bound"
      >x</a
      ><a name="10266"
      > </a
      ><a name="10267" href="Maps.html#10189" class="Bound"
      >v2</a
      ><a name="10269" class="Symbol"
      >)</a
      ><a name="10270"
      > </a
      ><a name="10271" href="Maps.html#10215" class="Bound"
      >y</a
      ><a name="10272"
      > </a
      ><a name="10273" href="Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="10274"
      > </a
      ><a name="10275" class="Symbol"
      >(</a
      ><a name="10276" href="Maps.html#9616" class="Function"
      >update</a
      ><a name="10282"
      > </a
      ><a name="10283" href="Maps.html#10194" class="Bound"
      >m</a
      ><a name="10284"
      > </a
      ><a name="10285" href="Maps.html#10213" class="Bound"
      >x</a
      ><a name="10286"
      > </a
      ><a name="10287" href="Maps.html#10189" class="Bound"
      >v2</a
      ><a name="10289" class="Symbol"
      >)</a
      ><a name="10290"
      > </a
      ><a name="10291" href="Maps.html#10215" class="Bound"
      >y</a
      ><a name="10292"
      >
  </a
      ><a name="10295" href="Maps.html#10165" class="Function"
      >update-shadow</a
      ><a name="10308"
      > </a
      ><a name="10309" href="Maps.html#10309" class="Bound"
      >m</a
      ><a name="10310"
      > </a
      ><a name="10311" href="Maps.html#10311" class="Bound"
      >x</a
      ><a name="10312"
      > </a
      ><a name="10313" href="Maps.html#10313" class="Bound"
      >y</a
      ><a name="10314"
      > </a
      ><a name="10315" class="Symbol"
      >=</a
      ><a name="10316"
      > </a
      ><a name="10317" href="Maps.html#7137" class="Postulate"
      >TotalMap.update-shadow</a
      ><a name="10339"
      > </a
      ><a name="10340" href="Maps.html#10309" class="Bound"
      >m</a
      ><a name="10341"
      > </a
      ><a name="10342" href="Maps.html#10311" class="Bound"
      >x</a
      ><a name="10343"
      > </a
      ><a name="10344" href="Maps.html#10313" class="Bound"
      >y</a
      >
{% endraw %}</pre>

<pre class="Agda">{% raw %}
  <a name="10373" href="Maps.html#10373" class="Function"
      >update-same</a
      ><a name="10384"
      > </a
      ><a name="10385" class="Symbol"
      >:</a
      ><a name="10386"
      > </a
      ><a name="10387" class="Symbol"
      >&#8704;</a
      ><a name="10388"
      > </a
      ><a name="10395" class="Symbol"
      >(</a
      ><a name="10396" href="Maps.html#10396" class="Bound"
      >m</a
      ><a name="10397"
      > </a
      ><a name="10398" class="Symbol"
      >:</a
      ><a name="10399"
      > </a
      ><a name="10400" href="Maps.html#9394" class="Function"
      >PartialMap</a
      ><a name="10410"
      > </a
      ><a name="10411" href="Maps.html#10390" class="Bound"
      >A</a
      ><a name="10412" class="Symbol"
      >)</a
      ><a name="10413"
      > </a
      ><a name="10414" class="Symbol"
      >(</a
      ><a name="10415" href="Maps.html#10415" class="Bound"
      >x</a
      ><a name="10416"
      > </a
      ><a name="10417" href="Maps.html#10417" class="Bound"
      >y</a
      ><a name="10418"
      > </a
      ><a name="10419" class="Symbol"
      >:</a
      ><a name="10420"
      > </a
      ><a name="10421" href="Maps.html#2275" class="Datatype"
      >Id</a
      ><a name="10423" class="Symbol"
      >)</a
      ><a name="10424"
      >
              </a
      ><a name="10439" class="Symbol"
      >&#8594;</a
      ><a name="10440"
      > </a
      ><a name="10441" href="Maps.html#10396" class="Bound"
      >m</a
      ><a name="10442"
      > </a
      ><a name="10443" href="Maps.html#10415" class="Bound"
      >x</a
      ><a name="10444"
      > </a
      ><a name="10445" href="Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="10446"
      > </a
      ><a name="10447" href="https://agda.github.io/agda-stdlib/Data.Maybe.Base.html#373" class="InductiveConstructor"
      >just</a
      ><a name="10451"
      > </a
      ><a name="10452" href="Maps.html#10392" class="Bound"
      >v</a
      ><a name="10453"
      >
              </a
      ><a name="10468" class="Symbol"
      >&#8594;</a
      ><a name="10469"
      > </a
      ><a name="10470" class="Symbol"
      >(</a
      ><a name="10471" href="Maps.html#9616" class="Function"
      >update</a
      ><a name="10477"
      > </a
      ><a name="10478" href="Maps.html#10396" class="Bound"
      >m</a
      ><a name="10479"
      > </a
      ><a name="10480" href="Maps.html#10415" class="Bound"
      >x</a
      ><a name="10481"
      > </a
      ><a name="10482" href="Maps.html#10392" class="Bound"
      >v</a
      ><a name="10483" class="Symbol"
      >)</a
      ><a name="10484"
      > </a
      ><a name="10485" href="Maps.html#10417" class="Bound"
      >y</a
      ><a name="10486"
      > </a
      ><a name="10487" href="Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="10488"
      > </a
      ><a name="10489" href="Maps.html#10396" class="Bound"
      >m</a
      ><a name="10490"
      > </a
      ><a name="10491" href="Maps.html#10417" class="Bound"
      >y</a
      ><a name="10492"
      >
  </a
      ><a name="10495" href="Maps.html#10373" class="Function"
      >update-same</a
      ><a name="10506"
      > </a
      ><a name="10507" href="Maps.html#10507" class="Bound"
      >m</a
      ><a name="10508"
      > </a
      ><a name="10509" href="Maps.html#10509" class="Bound"
      >x</a
      ><a name="10510"
      > </a
      ><a name="10511" href="Maps.html#10511" class="Bound"
      >y</a
      ><a name="10512"
      > </a
      ><a name="10513" href="Maps.html#10513" class="Bound"
      >mx=v</a
      ><a name="10517"
      > </a
      ><a name="10518" class="Keyword"
      >rewrite</a
      ><a name="10525"
      > </a
      ><a name="10526" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.Core.html#565" class="Function"
      >sym</a
      ><a name="10529"
      > </a
      ><a name="10530" href="Maps.html#10513" class="Bound"
      >mx=v</a
      ><a name="10534"
      > </a
      ><a name="10535" class="Symbol"
      >=</a
      ><a name="10536"
      > </a
      ><a name="10537" href="Maps.html#7793" class="Postulate"
      >TotalMap.update-same</a
      ><a name="10557"
      > </a
      ><a name="10558" href="Maps.html#10507" class="Bound"
      >m</a
      ><a name="10559"
      > </a
      ><a name="10560" href="Maps.html#10509" class="Bound"
      >x</a
      ><a name="10561"
      > </a
      ><a name="10562" href="Maps.html#10511" class="Bound"
      >y</a
      >
{% endraw %}</pre>

<pre class="Agda">{% raw %}
  <a name="10591" href="Maps.html#10591" class="Function"
      >update-permute</a
      ><a name="10605"
      > </a
      ><a name="10606" class="Symbol"
      >:</a
      ><a name="10607"
      > </a
      ><a name="10608" class="Symbol"
      >&#8704;</a
      ><a name="10609"
      > </a
      ><a name="10620" class="Symbol"
      >(</a
      ><a name="10621" href="Maps.html#10621" class="Bound"
      >m</a
      ><a name="10622"
      > </a
      ><a name="10623" class="Symbol"
      >:</a
      ><a name="10624"
      > </a
      ><a name="10625" href="Maps.html#9394" class="Function"
      >PartialMap</a
      ><a name="10635"
      > </a
      ><a name="10636" href="Maps.html#10611" class="Bound"
      >A</a
      ><a name="10637" class="Symbol"
      >)</a
      ><a name="10638"
      > </a
      ><a name="10639" class="Symbol"
      >(</a
      ><a name="10640" href="Maps.html#10640" class="Bound"
      >x1</a
      ><a name="10642"
      > </a
      ><a name="10643" href="Maps.html#10643" class="Bound"
      >x2</a
      ><a name="10645"
      > </a
      ><a name="10646" href="Maps.html#10646" class="Bound"
      >y</a
      ><a name="10647"
      > </a
      ><a name="10648" class="Symbol"
      >:</a
      ><a name="10649"
      > </a
      ><a name="10650" href="Maps.html#2275" class="Datatype"
      >Id</a
      ><a name="10652" class="Symbol"
      >)</a
      ><a name="10653"
      >
                 </a
      ><a name="10671" class="Symbol"
      >&#8594;</a
      ><a name="10672"
      > </a
      ><a name="10673" href="Maps.html#10640" class="Bound"
      >x1</a
      ><a name="10675"
      > </a
      ><a name="10676" href="https://agda.github.io/agda-stdlib/Relation.Binary.Core.html#4493" class="Function Operator"
      >&#8802;</a
      ><a name="10677"
      > </a
      ><a name="10678" href="Maps.html#10643" class="Bound"
      >x2</a
      ><a name="10680"
      > </a
      ><a name="10681" class="Symbol"
      >&#8594;</a
      ><a name="10682"
      > </a
      ><a name="10683" class="Symbol"
      >(</a
      ><a name="10684" href="Maps.html#9616" class="Function"
      >update</a
      ><a name="10690"
      > </a
      ><a name="10691" class="Symbol"
      >(</a
      ><a name="10692" href="Maps.html#9616" class="Function"
      >update</a
      ><a name="10698"
      > </a
      ><a name="10699" href="Maps.html#10621" class="Bound"
      >m</a
      ><a name="10700"
      > </a
      ><a name="10701" href="Maps.html#10643" class="Bound"
      >x2</a
      ><a name="10703"
      > </a
      ><a name="10704" href="Maps.html#10616" class="Bound"
      >v2</a
      ><a name="10706" class="Symbol"
      >)</a
      ><a name="10707"
      > </a
      ><a name="10708" href="Maps.html#10640" class="Bound"
      >x1</a
      ><a name="10710"
      > </a
      ><a name="10711" href="Maps.html#10613" class="Bound"
      >v1</a
      ><a name="10713" class="Symbol"
      >)</a
      ><a name="10714"
      > </a
      ><a name="10715" href="Maps.html#10646" class="Bound"
      >y</a
      ><a name="10716"
      >
                           </a
      ><a name="10744" href="Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="10745"
      > </a
      ><a name="10746" class="Symbol"
      >(</a
      ><a name="10747" href="Maps.html#9616" class="Function"
      >update</a
      ><a name="10753"
      > </a
      ><a name="10754" class="Symbol"
      >(</a
      ><a name="10755" href="Maps.html#9616" class="Function"
      >update</a
      ><a name="10761"
      > </a
      ><a name="10762" href="Maps.html#10621" class="Bound"
      >m</a
      ><a name="10763"
      > </a
      ><a name="10764" href="Maps.html#10640" class="Bound"
      >x1</a
      ><a name="10766"
      > </a
      ><a name="10767" href="Maps.html#10613" class="Bound"
      >v1</a
      ><a name="10769" class="Symbol"
      >)</a
      ><a name="10770"
      > </a
      ><a name="10771" href="Maps.html#10643" class="Bound"
      >x2</a
      ><a name="10773"
      > </a
      ><a name="10774" href="Maps.html#10616" class="Bound"
      >v2</a
      ><a name="10776" class="Symbol"
      >)</a
      ><a name="10777"
      > </a
      ><a name="10778" href="Maps.html#10646" class="Bound"
      >y</a
      ><a name="10779"
      >
  </a
      ><a name="10782" href="Maps.html#10591" class="Function"
      >update-permute</a
      ><a name="10796"
      > </a
      ><a name="10797" href="Maps.html#10797" class="Bound"
      >m</a
      ><a name="10798"
      > </a
      ><a name="10799" href="Maps.html#10799" class="Bound"
      >x1</a
      ><a name="10801"
      > </a
      ><a name="10802" href="Maps.html#10802" class="Bound"
      >x2</a
      ><a name="10804"
      > </a
      ><a name="10805" href="Maps.html#10805" class="Bound"
      >y</a
      ><a name="10806"
      > </a
      ><a name="10807" href="Maps.html#10807" class="Bound"
      >x1&#8800;x2</a
      ><a name="10812"
      > </a
      ><a name="10813" class="Symbol"
      >=</a
      ><a name="10814"
      > </a
      ><a name="10815" href="Maps.html#8373" class="Postulate"
      >TotalMap.update-permute</a
      ><a name="10838"
      > </a
      ><a name="10839" href="Maps.html#10797" class="Bound"
      >m</a
      ><a name="10840"
      > </a
      ><a name="10841" href="Maps.html#10799" class="Bound"
      >x1</a
      ><a name="10843"
      > </a
      ><a name="10844" href="Maps.html#10802" class="Bound"
      >x2</a
      ><a name="10846"
      > </a
      ><a name="10847" href="Maps.html#10805" class="Bound"
      >y</a
      ><a name="10848"
      > </a
      ><a name="10849" href="Maps.html#10807" class="Bound"
      >x1&#8800;x2</a
      >
{% endraw %}</pre>
