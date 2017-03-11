---
title     : "Maps: Total and Partial Maps"
layout    : page
permalink : /Maps
---

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
<a name="1450" class="Keyword"
      >open</a
      ><a name="1454"
      > </a
      ><a name="1455" class="Keyword"
      >import</a
      ><a name="1461"
      > </a
      ><a name="1462" href="https://agda.github.io/agda-stdlib/Function.html#1" class="Module"
      >Function</a
      ><a name="1470"
      >         </a
      ><a name="1479" class="Keyword"
      >using</a
      ><a name="1484"
      > </a
      ><a name="1485" class="Symbol"
      >(</a
      ><a name="1486" href="https://agda.github.io/agda-stdlib/Function.html#713" class="Function Operator"
      >_&#8728;_</a
      ><a name="1489" class="Symbol"
      >)</a
      ><a name="1490"
      >
</a
      ><a name="1491" class="Keyword"
      >open</a
      ><a name="1495"
      > </a
      ><a name="1496" class="Keyword"
      >import</a
      ><a name="1502"
      > </a
      ><a name="1503" href="https://agda.github.io/agda-stdlib/Data.Bool.html#1" class="Module"
      >Data.Bool</a
      ><a name="1512"
      >        </a
      ><a name="1520" class="Keyword"
      >using</a
      ><a name="1525"
      > </a
      ><a name="1526" class="Symbol"
      >(</a
      ><a name="1527" href="Agda.Builtin.Bool.html#67" class="Datatype"
      >Bool</a
      ><a name="1531" class="Symbol"
      >;</a
      ><a name="1532"
      > </a
      ><a name="1533" href="Agda.Builtin.Bool.html#92" class="InductiveConstructor"
      >true</a
      ><a name="1537" class="Symbol"
      >;</a
      ><a name="1538"
      > </a
      ><a name="1539" href="Agda.Builtin.Bool.html#86" class="InductiveConstructor"
      >false</a
      ><a name="1544" class="Symbol"
      >)</a
      ><a name="1545"
      >
</a
      ><a name="1546" class="Keyword"
      >open</a
      ><a name="1550"
      > </a
      ><a name="1551" class="Keyword"
      >import</a
      ><a name="1557"
      > </a
      ><a name="1558" href="https://agda.github.io/agda-stdlib/Data.Empty.html#1" class="Module"
      >Data.Empty</a
      ><a name="1568"
      >       </a
      ><a name="1575" class="Keyword"
      >using</a
      ><a name="1580"
      > </a
      ><a name="1581" class="Symbol"
      >(</a
      ><a name="1582" href="https://agda.github.io/agda-stdlib/Data.Empty.html#243" class="Datatype"
      >&#8869;</a
      ><a name="1583" class="Symbol"
      >;</a
      ><a name="1584"
      > </a
      ><a name="1585" href="https://agda.github.io/agda-stdlib/Data.Empty.html#348" class="Function"
      >&#8869;-elim</a
      ><a name="1591" class="Symbol"
      >)</a
      ><a name="1592"
      >
</a
      ><a name="1593" class="Keyword"
      >open</a
      ><a name="1597"
      > </a
      ><a name="1598" class="Keyword"
      >import</a
      ><a name="1604"
      > </a
      ><a name="1605" href="https://agda.github.io/agda-stdlib/Data.Maybe.html#1" class="Module"
      >Data.Maybe</a
      ><a name="1615"
      >       </a
      ><a name="1622" class="Keyword"
      >using</a
      ><a name="1627"
      > </a
      ><a name="1628" class="Symbol"
      >(</a
      ><a name="1629" href="https://agda.github.io/agda-stdlib/Data.Maybe.Base.html#335" class="Datatype"
      >Maybe</a
      ><a name="1634" class="Symbol"
      >;</a
      ><a name="1635"
      > </a
      ><a name="1636" href="https://agda.github.io/agda-stdlib/Data.Maybe.html#1527" class="InductiveConstructor"
      >just</a
      ><a name="1640" class="Symbol"
      >;</a
      ><a name="1641"
      > </a
      ><a name="1642" href="https://agda.github.io/agda-stdlib/Data.Maybe.html#1588" class="InductiveConstructor"
      >nothing</a
      ><a name="1649" class="Symbol"
      >)</a
      ><a name="1650"
      >
</a
      ><a name="1651" class="Keyword"
      >open</a
      ><a name="1655"
      > </a
      ><a name="1656" class="Keyword"
      >import</a
      ><a name="1662"
      > </a
      ><a name="1663" href="https://agda.github.io/agda-stdlib/Data.Nat.html#1" class="Module"
      >Data.Nat</a
      ><a name="1671"
      >         </a
      ><a name="1680" class="Keyword"
      >using</a
      ><a name="1685"
      > </a
      ><a name="1686" class="Symbol"
      >(</a
      ><a name="1687" href="Agda.Builtin.Nat.html#97" class="Datatype"
      >&#8469;</a
      ><a name="1688" class="Symbol"
      >)</a
      ><a name="1689"
      >
</a
      ><a name="1690" class="Keyword"
      >open</a
      ><a name="1694"
      > </a
      ><a name="1695" class="Keyword"
      >import</a
      ><a name="1701"
      > </a
      ><a name="1702" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#1" class="Module"
      >Relation.Nullary</a
      ><a name="1718"
      > </a
      ><a name="1719" class="Keyword"
      >using</a
      ><a name="1724"
      > </a
      ><a name="1725" class="Symbol"
      >(</a
      ><a name="1726" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#484" class="Datatype"
      >Dec</a
      ><a name="1729" class="Symbol"
      >;</a
      ><a name="1730"
      > </a
      ><a name="1731" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#520" class="InductiveConstructor"
      >yes</a
      ><a name="1734" class="Symbol"
      >;</a
      ><a name="1735"
      > </a
      ><a name="1736" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#547" class="InductiveConstructor"
      >no</a
      ><a name="1738" class="Symbol"
      >)</a
      ><a name="1739"
      >
</a
      ><a name="1740" class="Keyword"
      >open</a
      ><a name="1744"
      > </a
      ><a name="1745" class="Keyword"
      >import</a
      ><a name="1751"
      > </a
      ><a name="1752" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#1" class="Module"
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
<a name="2238" class="Keyword"
      >data</a
      ><a name="2242"
      > </a
      ><a name="2243" href="Maps.html#2243" class="Datatype"
      >Id</a
      ><a name="2245"
      > </a
      ><a name="2246" class="Symbol"
      >:</a
      ><a name="2247"
      > </a
      ><a name="2248" class="PrimitiveType"
      >Set</a
      ><a name="2251"
      > </a
      ><a name="2252" class="Keyword"
      >where</a
      ><a name="2257"
      >
  </a
      ><a name="2260" href="Maps.html#2260" class="InductiveConstructor"
      >id</a
      ><a name="2262"
      > </a
      ><a name="2263" class="Symbol"
      >:</a
      ><a name="2264"
      > </a
      ><a name="2265" href="Agda.Builtin.Nat.html#97" class="Datatype"
      >&#8469;</a
      ><a name="2266"
      > </a
      ><a name="2267" class="Symbol"
      >&#8594;</a
      ><a name="2268"
      > </a
      ><a name="2269" href="Maps.html#2243" class="Datatype"
      >Id</a
      >
{% endraw %}</pre>

<pre class="Agda">{% raw %}
<a name="2297" href="Maps.html#2297" class="Function Operator"
      >_&#8799;_</a
      ><a name="2300"
      > </a
      ><a name="2301" class="Symbol"
      >:</a
      ><a name="2302"
      > </a
      ><a name="2303" class="Symbol"
      >(</a
      ><a name="2304" href="Maps.html#2304" class="Bound"
      >x</a
      ><a name="2305"
      > </a
      ><a name="2306" href="Maps.html#2306" class="Bound"
      >y</a
      ><a name="2307"
      > </a
      ><a name="2308" class="Symbol"
      >:</a
      ><a name="2309"
      > </a
      ><a name="2310" href="Maps.html#2243" class="Datatype"
      >Id</a
      ><a name="2312" class="Symbol"
      >)</a
      ><a name="2313"
      > </a
      ><a name="2314" class="Symbol"
      >&#8594;</a
      ><a name="2315"
      > </a
      ><a name="2316" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#484" class="Datatype"
      >Dec</a
      ><a name="2319"
      > </a
      ><a name="2320" class="Symbol"
      >(</a
      ><a name="2321" href="Maps.html#2304" class="Bound"
      >x</a
      ><a name="2322"
      > </a
      ><a name="2323" href="Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="2324"
      > </a
      ><a name="2325" href="Maps.html#2306" class="Bound"
      >y</a
      ><a name="2326" class="Symbol"
      >)</a
      ><a name="2327"
      >
</a
      ><a name="2328" href="Maps.html#2260" class="InductiveConstructor"
      >id</a
      ><a name="2330"
      > </a
      ><a name="2331" href="Maps.html#2331" class="Bound"
      >x</a
      ><a name="2332"
      > </a
      ><a name="2333" href="Maps.html#2297" class="Function Operator"
      >&#8799;</a
      ><a name="2334"
      > </a
      ><a name="2335" href="Maps.html#2260" class="InductiveConstructor"
      >id</a
      ><a name="2337"
      > </a
      ><a name="2338" href="Maps.html#2338" class="Bound"
      >y</a
      ><a name="2339"
      > </a
      ><a name="2340" class="Keyword"
      >with</a
      ><a name="2344"
      > </a
      ><a name="2345" href="Maps.html#2331" class="Bound"
      >x</a
      ><a name="2346"
      > </a
      ><a name="2347" href="https://agda.github.io/agda-stdlib/Data.Nat.Base.html#3212" class="Function Operator"
      >Data.Nat.&#8799;</a
      ><a name="2357"
      > </a
      ><a name="2358" href="Maps.html#2338" class="Bound"
      >y</a
      ><a name="2359"
      >
</a
      ><a name="2360" href="Maps.html#2260" class="InductiveConstructor"
      >id</a
      ><a name="2362"
      > </a
      ><a name="2363" href="Maps.html#2363" class="Bound"
      >x</a
      ><a name="2364"
      > </a
      ><a name="2365" href="Maps.html#2297" class="Function Operator"
      >&#8799;</a
      ><a name="2366"
      > </a
      ><a name="2367" href="Maps.html#2260" class="InductiveConstructor"
      >id</a
      ><a name="2369"
      > </a
      ><a name="2370" href="Maps.html#2370" class="Bound"
      >y</a
      ><a name="2371"
      > </a
      ><a name="2372" class="Symbol"
      >|</a
      ><a name="2373"
      > </a
      ><a name="2374" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#520" class="InductiveConstructor"
      >yes</a
      ><a name="2377"
      > </a
      ><a name="2378" href="Maps.html#2378" class="Bound"
      >x=y</a
      ><a name="2381"
      > </a
      ><a name="2382" class="Keyword"
      >rewrite</a
      ><a name="2389"
      > </a
      ><a name="2390" href="Maps.html#2378" class="Bound"
      >x=y</a
      ><a name="2393"
      > </a
      ><a name="2394" class="Symbol"
      >=</a
      ><a name="2395"
      > </a
      ><a name="2396" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#520" class="InductiveConstructor"
      >yes</a
      ><a name="2399"
      > </a
      ><a name="2400" href="Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="2404"
      >
</a
      ><a name="2405" href="Maps.html#2260" class="InductiveConstructor"
      >id</a
      ><a name="2407"
      > </a
      ><a name="2408" href="Maps.html#2408" class="Bound"
      >x</a
      ><a name="2409"
      > </a
      ><a name="2410" href="Maps.html#2297" class="Function Operator"
      >&#8799;</a
      ><a name="2411"
      > </a
      ><a name="2412" href="Maps.html#2260" class="InductiveConstructor"
      >id</a
      ><a name="2414"
      > </a
      ><a name="2415" href="Maps.html#2415" class="Bound"
      >y</a
      ><a name="2416"
      > </a
      ><a name="2417" class="Symbol"
      >|</a
      ><a name="2418"
      > </a
      ><a name="2419" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#547" class="InductiveConstructor"
      >no</a
      ><a name="2421"
      >  </a
      ><a name="2423" href="Maps.html#2423" class="Bound"
      >x&#8800;y</a
      ><a name="2426"
      > </a
      ><a name="2427" class="Symbol"
      >=</a
      ><a name="2428"
      > </a
      ><a name="2429" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#547" class="InductiveConstructor"
      >no</a
      ><a name="2431"
      > </a
      ><a name="2432" class="Symbol"
      >(</a
      ><a name="2433" href="Maps.html#2423" class="Bound"
      >x&#8800;y</a
      ><a name="2436"
      > </a
      ><a name="2437" href="https://agda.github.io/agda-stdlib/Function.html#713" class="Function Operator"
      >&#8728;</a
      ><a name="2438"
      > </a
      ><a name="2439" href="Maps.html#2459" class="Function"
      >id-inj</a
      ><a name="2445" class="Symbol"
      >)</a
      ><a name="2446"
      >
  </a
      ><a name="2449" class="Keyword"
      >where</a
      ><a name="2454"
      >
    </a
      ><a name="2459" href="Maps.html#2459" class="Function"
      >id-inj</a
      ><a name="2465"
      > </a
      ><a name="2466" class="Symbol"
      >:</a
      ><a name="2467"
      > </a
      ><a name="2468" class="Symbol"
      >&#8704;</a
      ><a name="2469"
      > </a
      ><a name="2476" class="Symbol"
      >&#8594;</a
      ><a name="2477"
      > </a
      ><a name="2478" href="Maps.html#2260" class="InductiveConstructor"
      >id</a
      ><a name="2480"
      > </a
      ><a name="2481" href="Maps.html#2471" class="Bound"
      >x</a
      ><a name="2482"
      > </a
      ><a name="2483" href="Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="2484"
      > </a
      ><a name="2485" href="Maps.html#2260" class="InductiveConstructor"
      >id</a
      ><a name="2487"
      > </a
      ><a name="2488" href="Maps.html#2473" class="Bound"
      >y</a
      ><a name="2489"
      > </a
      ><a name="2490" class="Symbol"
      >&#8594;</a
      ><a name="2491"
      > </a
      ><a name="2492" href="Maps.html#2471" class="Bound"
      >x</a
      ><a name="2493"
      > </a
      ><a name="2494" href="Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="2495"
      > </a
      ><a name="2496" href="Maps.html#2473" class="Bound"
      >y</a
      ><a name="2497"
      >
    </a
      ><a name="2502" href="Maps.html#2459" class="Function"
      >id-inj</a
      ><a name="2508"
      > </a
      ><a name="2509" href="Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="2513"
      > </a
      ><a name="2514" class="Symbol"
      >=</a
      ><a name="2515"
      > </a
      ><a name="2516" href="Agda.Builtin.Equality.html#140" class="InductiveConstructor"
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
<a name="3352" href="Maps.html#3352" class="Function"
      >TotalMap</a
      ><a name="3360"
      > </a
      ><a name="3361" class="Symbol"
      >:</a
      ><a name="3362"
      > </a
      ><a name="3363" class="PrimitiveType"
      >Set</a
      ><a name="3366"
      > </a
      ><a name="3367" class="Symbol"
      >&#8594;</a
      ><a name="3368"
      > </a
      ><a name="3369" class="PrimitiveType"
      >Set</a
      ><a name="3372"
      >
</a
      ><a name="3373" href="Maps.html#3352" class="Function"
      >TotalMap</a
      ><a name="3381"
      > </a
      ><a name="3382" href="Maps.html#3382" class="Bound"
      >A</a
      ><a name="3383"
      > </a
      ><a name="3384" class="Symbol"
      >=</a
      ><a name="3385"
      > </a
      ><a name="3386" href="Maps.html#2243" class="Datatype"
      >Id</a
      ><a name="3388"
      > </a
      ><a name="3389" class="Symbol"
      >&#8594;</a
      ><a name="3390"
      > </a
      ><a name="3391" href="Maps.html#3382" class="Bound"
      >A</a
      >
{% endraw %}</pre>

Intuitively, a total map over anﬁ element type $$A$$ _is_ just a
function that can be used to look up ids, yielding $$A$$s.

<pre class="Agda">{% raw %}
<a name="3543" class="Keyword"
      >module</a
      ><a name="3549"
      > </a
      ><a name="3550" href="Maps.html#3550" class="Module"
      >TotalMap</a
      ><a name="3558"
      > </a
      ><a name="3559" class="Keyword"
      >where</a
      >
{% endraw %}</pre>

The function `empty` yields an empty total map, given a
default element; this map always returns the default element when
applied to any id.

<pre class="Agda">{% raw %}
  <a name="3734" href="Maps.html#3734" class="Function"
      >empty</a
      ><a name="3739"
      > </a
      ><a name="3740" class="Symbol"
      >:</a
      ><a name="3741"
      > </a
      ><a name="3742" class="Symbol"
      >&#8704;</a
      ><a name="3743"
      > </a
      ><a name="3748" class="Symbol"
      >&#8594;</a
      ><a name="3749"
      > </a
      ><a name="3750" href="Maps.html#3745" class="Bound"
      >A</a
      ><a name="3751"
      > </a
      ><a name="3752" class="Symbol"
      >&#8594;</a
      ><a name="3753"
      > </a
      ><a name="3754" href="Maps.html#3352" class="Function"
      >TotalMap</a
      ><a name="3762"
      > </a
      ><a name="3763" href="Maps.html#3745" class="Bound"
      >A</a
      ><a name="3764"
      >
  </a
      ><a name="3767" href="Maps.html#3734" class="Function"
      >empty</a
      ><a name="3772"
      > </a
      ><a name="3773" href="Maps.html#3773" class="Bound"
      >x</a
      ><a name="3774"
      > </a
      ><a name="3775" class="Symbol"
      >=</a
      ><a name="3776"
      > </a
      ><a name="3777" class="Symbol"
      >&#955;</a
      ><a name="3778"
      > </a
      ><a name="3779" href="Maps.html#3779" class="Bound"
      >_</a
      ><a name="3780"
      > </a
      ><a name="3781" class="Symbol"
      >&#8594;</a
      ><a name="3782"
      > </a
      ><a name="3783" href="Maps.html#3773" class="Bound"
      >x</a
      >
{% endraw %}</pre>

More interesting is the `update` function, which (as before) takes
a map $$m$$, a key $$x$$, and a value $$v$$ and returns a new map that
takes $$x$$ to $$v$$ and takes every other key to whatever $$m$$ does.

<pre class="Agda">{% raw %}
  <a name="4022" href="Maps.html#4022" class="Function"
      >update</a
      ><a name="4028"
      > </a
      ><a name="4029" class="Symbol"
      >:</a
      ><a name="4030"
      > </a
      ><a name="4031" class="Symbol"
      >&#8704;</a
      ><a name="4032"
      > </a
      ><a name="4037" class="Symbol"
      >&#8594;</a
      ><a name="4038"
      > </a
      ><a name="4039" href="Maps.html#3352" class="Function"
      >TotalMap</a
      ><a name="4047"
      > </a
      ><a name="4048" href="Maps.html#4034" class="Bound"
      >A</a
      ><a name="4049"
      > </a
      ><a name="4050" class="Symbol"
      >-&gt;</a
      ><a name="4052"
      > </a
      ><a name="4053" href="Maps.html#2243" class="Datatype"
      >Id</a
      ><a name="4055"
      > </a
      ><a name="4056" class="Symbol"
      >-&gt;</a
      ><a name="4058"
      > </a
      ><a name="4059" href="Maps.html#4034" class="Bound"
      >A</a
      ><a name="4060"
      > </a
      ><a name="4061" class="Symbol"
      >-&gt;</a
      ><a name="4063"
      > </a
      ><a name="4064" href="Maps.html#3352" class="Function"
      >TotalMap</a
      ><a name="4072"
      > </a
      ><a name="4073" href="Maps.html#4034" class="Bound"
      >A</a
      ><a name="4074"
      >
  </a
      ><a name="4077" href="Maps.html#4022" class="Function"
      >update</a
      ><a name="4083"
      > </a
      ><a name="4084" href="Maps.html#4084" class="Bound"
      >m</a
      ><a name="4085"
      > </a
      ><a name="4086" href="Maps.html#4086" class="Bound"
      >x</a
      ><a name="4087"
      > </a
      ><a name="4088" href="Maps.html#4088" class="Bound"
      >v</a
      ><a name="4089"
      > </a
      ><a name="4090" href="Maps.html#4090" class="Bound"
      >y</a
      ><a name="4091"
      > </a
      ><a name="4092" class="Keyword"
      >with</a
      ><a name="4096"
      > </a
      ><a name="4097" href="Maps.html#4086" class="Bound"
      >x</a
      ><a name="4098"
      > </a
      ><a name="4099" href="Maps.html#2297" class="Function Operator"
      >&#8799;</a
      ><a name="4100"
      > </a
      ><a name="4101" href="Maps.html#4090" class="Bound"
      >y</a
      ><a name="4102"
      >
  </a
      ><a name="4105" class="Symbol"
      >...</a
      ><a name="4108"
      > </a
      ><a name="4109" class="Symbol"
      >|</a
      ><a name="4110"
      > </a
      ><a name="4111" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#520" class="InductiveConstructor"
      >yes</a
      ><a name="4114"
      > </a
      ><a name="4115" href="Maps.html#4115" class="Bound"
      >x=y</a
      ><a name="4118"
      > </a
      ><a name="4119" class="Symbol"
      >=</a
      ><a name="4120"
      > </a
      ><a name="4121" href="Maps.html#4088" class="Bound"
      >v</a
      ><a name="4122"
      >
  </a
      ><a name="4125" class="Symbol"
      >...</a
      ><a name="4128"
      > </a
      ><a name="4129" class="Symbol"
      >|</a
      ><a name="4130"
      > </a
      ><a name="4131" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#547" class="InductiveConstructor"
      >no</a
      ><a name="4133"
      >  </a
      ><a name="4135" href="Maps.html#4135" class="Bound"
      >x&#8800;y</a
      ><a name="4138"
      > </a
      ><a name="4139" class="Symbol"
      >=</a
      ><a name="4140"
      > </a
      ><a name="4141" href="Maps.html#4084" class="Bound"
      >m</a
      ><a name="4142"
      > </a
      ><a name="4143" href="Maps.html#4090" class="Bound"
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
  <a name="4506" href="Maps.html#4506" class="Function"
      >examplemap</a
      ><a name="4516"
      > </a
      ><a name="4517" class="Symbol"
      >:</a
      ><a name="4518"
      > </a
      ><a name="4519" href="Maps.html#3352" class="Function"
      >TotalMap</a
      ><a name="4527"
      > </a
      ><a name="4528" href="Agda.Builtin.Bool.html#67" class="Datatype"
      >Bool</a
      ><a name="4532"
      >
  </a
      ><a name="4535" href="Maps.html#4506" class="Function"
      >examplemap</a
      ><a name="4545"
      > </a
      ><a name="4546" class="Symbol"
      >=</a
      ><a name="4547"
      > </a
      ><a name="4548" href="Maps.html#4022" class="Function"
      >update</a
      ><a name="4554"
      > </a
      ><a name="4555" class="Symbol"
      >(</a
      ><a name="4556" href="Maps.html#4022" class="Function"
      >update</a
      ><a name="4562"
      > </a
      ><a name="4563" class="Symbol"
      >(</a
      ><a name="4564" href="Maps.html#3734" class="Function"
      >empty</a
      ><a name="4569"
      > </a
      ><a name="4570" href="Agda.Builtin.Bool.html#86" class="InductiveConstructor"
      >false</a
      ><a name="4575" class="Symbol"
      >)</a
      ><a name="4576"
      > </a
      ><a name="4577" class="Symbol"
      >(</a
      ><a name="4578" href="Maps.html#2260" class="InductiveConstructor"
      >id</a
      ><a name="4580"
      > </a
      ><a name="4581" class="Number"
      >1</a
      ><a name="4582" class="Symbol"
      >)</a
      ><a name="4583"
      > </a
      ><a name="4584" href="Agda.Builtin.Bool.html#86" class="InductiveConstructor"
      >false</a
      ><a name="4589" class="Symbol"
      >)</a
      ><a name="4590"
      > </a
      ><a name="4591" class="Symbol"
      >(</a
      ><a name="4592" href="Maps.html#2260" class="InductiveConstructor"
      >id</a
      ><a name="4594"
      > </a
      ><a name="4595" class="Number"
      >3</a
      ><a name="4596" class="Symbol"
      >)</a
      ><a name="4597"
      > </a
      ><a name="4598" href="Agda.Builtin.Bool.html#92" class="InductiveConstructor"
      >true</a
      >
{% endraw %}</pre>

This completes the definition of total maps.  Note that we don't
need to define a `find` operation because it is just function
application!

<pre class="Agda">{% raw %}
  <a name="4771" href="Maps.html#4771" class="Function Operator"
      >test_examplemap0</a
      ><a name="4787"
      > </a
      ><a name="4788" class="Symbol"
      >:</a
      ><a name="4789"
      > </a
      ><a name="4790" href="Maps.html#4506" class="Function"
      >examplemap</a
      ><a name="4800"
      > </a
      ><a name="4801" class="Symbol"
      >(</a
      ><a name="4802" href="Maps.html#2260" class="InductiveConstructor"
      >id</a
      ><a name="4804"
      > </a
      ><a name="4805" class="Number"
      >0</a
      ><a name="4806" class="Symbol"
      >)</a
      ><a name="4807"
      > </a
      ><a name="4808" href="Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="4809"
      > </a
      ><a name="4810" href="Agda.Builtin.Bool.html#86" class="InductiveConstructor"
      >false</a
      ><a name="4815"
      >
  </a
      ><a name="4818" href="Maps.html#4771" class="Function Operator"
      >test_examplemap0</a
      ><a name="4834"
      > </a
      ><a name="4835" class="Symbol"
      >=</a
      ><a name="4836"
      > </a
      ><a name="4837" href="Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="4841"
      >

  </a
      ><a name="4845" href="Maps.html#4845" class="Function Operator"
      >test_examplemap1</a
      ><a name="4861"
      > </a
      ><a name="4862" class="Symbol"
      >:</a
      ><a name="4863"
      > </a
      ><a name="4864" href="Maps.html#4506" class="Function"
      >examplemap</a
      ><a name="4874"
      > </a
      ><a name="4875" class="Symbol"
      >(</a
      ><a name="4876" href="Maps.html#2260" class="InductiveConstructor"
      >id</a
      ><a name="4878"
      > </a
      ><a name="4879" class="Number"
      >1</a
      ><a name="4880" class="Symbol"
      >)</a
      ><a name="4881"
      > </a
      ><a name="4882" href="Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="4883"
      > </a
      ><a name="4884" href="Agda.Builtin.Bool.html#86" class="InductiveConstructor"
      >false</a
      ><a name="4889"
      >
  </a
      ><a name="4892" href="Maps.html#4845" class="Function Operator"
      >test_examplemap1</a
      ><a name="4908"
      > </a
      ><a name="4909" class="Symbol"
      >=</a
      ><a name="4910"
      > </a
      ><a name="4911" href="Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="4915"
      >

  </a
      ><a name="4919" href="Maps.html#4919" class="Function Operator"
      >test_examplemap2</a
      ><a name="4935"
      > </a
      ><a name="4936" class="Symbol"
      >:</a
      ><a name="4937"
      > </a
      ><a name="4938" href="Maps.html#4506" class="Function"
      >examplemap</a
      ><a name="4948"
      > </a
      ><a name="4949" class="Symbol"
      >(</a
      ><a name="4950" href="Maps.html#2260" class="InductiveConstructor"
      >id</a
      ><a name="4952"
      > </a
      ><a name="4953" class="Number"
      >2</a
      ><a name="4954" class="Symbol"
      >)</a
      ><a name="4955"
      > </a
      ><a name="4956" href="Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="4957"
      > </a
      ><a name="4958" href="Agda.Builtin.Bool.html#86" class="InductiveConstructor"
      >false</a
      ><a name="4963"
      >
  </a
      ><a name="4966" href="Maps.html#4919" class="Function Operator"
      >test_examplemap2</a
      ><a name="4982"
      > </a
      ><a name="4983" class="Symbol"
      >=</a
      ><a name="4984"
      > </a
      ><a name="4985" href="Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="4989"
      >

  </a
      ><a name="4993" href="Maps.html#4993" class="Function Operator"
      >test_examplemap3</a
      ><a name="5009"
      > </a
      ><a name="5010" class="Symbol"
      >:</a
      ><a name="5011"
      > </a
      ><a name="5012" href="Maps.html#4506" class="Function"
      >examplemap</a
      ><a name="5022"
      > </a
      ><a name="5023" class="Symbol"
      >(</a
      ><a name="5024" href="Maps.html#2260" class="InductiveConstructor"
      >id</a
      ><a name="5026"
      > </a
      ><a name="5027" class="Number"
      >3</a
      ><a name="5028" class="Symbol"
      >)</a
      ><a name="5029"
      > </a
      ><a name="5030" href="Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="5031"
      > </a
      ><a name="5032" href="Agda.Builtin.Bool.html#92" class="InductiveConstructor"
      >true</a
      ><a name="5036"
      >
  </a
      ><a name="5039" href="Maps.html#4993" class="Function Operator"
      >test_examplemap3</a
      ><a name="5055"
      > </a
      ><a name="5056" class="Symbol"
      >=</a
      ><a name="5057"
      > </a
      ><a name="5058" href="Agda.Builtin.Equality.html#140" class="InductiveConstructor"
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
  <a name="5559" class="Keyword"
      >postulate</a
      ><a name="5568"
      >
    </a
      ><a name="5573" href="Maps.html#5573" class="Postulate"
      >apply-empty</a
      ><a name="5584"
      > </a
      ><a name="5585" class="Symbol"
      >:</a
      ><a name="5586"
      > </a
      ><a name="5587" class="Symbol"
      >&#8704;</a
      ><a name="5588"
      > </a
      ><a name="5597" class="Symbol"
      >&#8594;</a
      ><a name="5598"
      > </a
      ><a name="5599" href="Maps.html#3734" class="Function"
      >empty</a
      ><a name="5604"
      > </a
      ><a name="5609" href="Maps.html#5594" class="Bound"
      >v</a
      ><a name="5610"
      > </a
      ><a name="5611" href="Maps.html#5592" class="Bound"
      >x</a
      ><a name="5612"
      > </a
      ><a name="5613" href="Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="5614"
      > </a
      ><a name="5615" href="Maps.html#5594" class="Bound"
      >v</a
      >
{% endraw %}</pre>

<div class="hidden">
<pre class="Agda">{% raw %}
  <a name="5665" href="Maps.html#5665" class="Function"
      >apply-empty&#8242;</a
      ><a name="5677"
      > </a
      ><a name="5678" class="Symbol"
      >:</a
      ><a name="5679"
      > </a
      ><a name="5680" class="Symbol"
      >&#8704;</a
      ><a name="5681"
      > </a
      ><a name="5690" class="Symbol"
      >&#8594;</a
      ><a name="5691"
      > </a
      ><a name="5692" href="Maps.html#3734" class="Function"
      >empty</a
      ><a name="5697"
      > </a
      ><a name="5702" href="Maps.html#5687" class="Bound"
      >v</a
      ><a name="5703"
      > </a
      ><a name="5704" href="Maps.html#5685" class="Bound"
      >x</a
      ><a name="5705"
      > </a
      ><a name="5706" href="Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="5707"
      > </a
      ><a name="5708" href="Maps.html#5687" class="Bound"
      >v</a
      ><a name="5709"
      >
  </a
      ><a name="5712" href="Maps.html#5665" class="Function"
      >apply-empty&#8242;</a
      ><a name="5724"
      > </a
      ><a name="5725" class="Symbol"
      >=</a
      ><a name="5726"
      > </a
      ><a name="5727" href="Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      >
{% endraw %}</pre>
</div>

#### Exercise: 2 stars, optional (update-eq)
Next, if we update a map $$m$$ at a key $$x$$ with a new value $$v$$
and then look up $$x$$ in the map resulting from the `update`, we get
back $$v$$:

<pre class="Agda">{% raw %}
  <a name="5963" class="Keyword"
      >postulate</a
      ><a name="5972"
      >
    </a
      ><a name="5977" href="Maps.html#5977" class="Postulate"
      >update-eq</a
      ><a name="5986"
      > </a
      ><a name="5987" class="Symbol"
      >:</a
      ><a name="5988"
      > </a
      ><a name="5989" class="Symbol"
      >&#8704;</a
      ><a name="5990"
      > </a
      ><a name="5997" class="Symbol"
      >(</a
      ><a name="5998" href="Maps.html#5998" class="Bound"
      >m</a
      ><a name="5999"
      > </a
      ><a name="6000" class="Symbol"
      >:</a
      ><a name="6001"
      > </a
      ><a name="6002" href="Maps.html#3352" class="Function"
      >TotalMap</a
      ><a name="6010"
      > </a
      ><a name="6011" href="Maps.html#5992" class="Bound"
      >A</a
      ><a name="6012" class="Symbol"
      >)</a
      ><a name="6013"
      > </a
      ><a name="6014" class="Symbol"
      >(</a
      ><a name="6015" href="Maps.html#6015" class="Bound"
      >x</a
      ><a name="6016"
      > </a
      ><a name="6017" class="Symbol"
      >:</a
      ><a name="6018"
      > </a
      ><a name="6019" href="Maps.html#2243" class="Datatype"
      >Id</a
      ><a name="6021" class="Symbol"
      >)</a
      ><a name="6022"
      >
              </a
      ><a name="6037" class="Symbol"
      >&#8594;</a
      ><a name="6038"
      > </a
      ><a name="6039" class="Symbol"
      >(</a
      ><a name="6040" href="Maps.html#4022" class="Function"
      >update</a
      ><a name="6046"
      > </a
      ><a name="6047" href="Maps.html#5998" class="Bound"
      >m</a
      ><a name="6048"
      > </a
      ><a name="6049" href="Maps.html#6015" class="Bound"
      >x</a
      ><a name="6050"
      > </a
      ><a name="6051" href="Maps.html#5994" class="Bound"
      >v</a
      ><a name="6052" class="Symbol"
      >)</a
      ><a name="6053"
      > </a
      ><a name="6054" href="Maps.html#6015" class="Bound"
      >x</a
      ><a name="6055"
      > </a
      ><a name="6056" href="Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="6057"
      > </a
      ><a name="6058" href="Maps.html#5994" class="Bound"
      >v</a
      >
{% endraw %}</pre>

<div class="hidden">
<pre class="Agda">{% raw %}
  <a name="6108" href="Maps.html#6108" class="Function"
      >update-eq&#8242;</a
      ><a name="6118"
      > </a
      ><a name="6119" class="Symbol"
      >:</a
      ><a name="6120"
      > </a
      ><a name="6121" class="Symbol"
      >&#8704;</a
      ><a name="6122"
      > </a
      ><a name="6129" class="Symbol"
      >(</a
      ><a name="6130" href="Maps.html#6130" class="Bound"
      >m</a
      ><a name="6131"
      > </a
      ><a name="6132" class="Symbol"
      >:</a
      ><a name="6133"
      > </a
      ><a name="6134" href="Maps.html#3352" class="Function"
      >TotalMap</a
      ><a name="6142"
      > </a
      ><a name="6143" href="Maps.html#6124" class="Bound"
      >A</a
      ><a name="6144" class="Symbol"
      >)</a
      ><a name="6145"
      > </a
      ><a name="6146" class="Symbol"
      >(</a
      ><a name="6147" href="Maps.html#6147" class="Bound"
      >x</a
      ><a name="6148"
      > </a
      ><a name="6149" class="Symbol"
      >:</a
      ><a name="6150"
      > </a
      ><a name="6151" href="Maps.html#2243" class="Datatype"
      >Id</a
      ><a name="6153" class="Symbol"
      >)</a
      ><a name="6154"
      >
             </a
      ><a name="6168" class="Symbol"
      >&#8594;</a
      ><a name="6169"
      > </a
      ><a name="6170" class="Symbol"
      >(</a
      ><a name="6171" href="Maps.html#4022" class="Function"
      >update</a
      ><a name="6177"
      > </a
      ><a name="6178" href="Maps.html#6130" class="Bound"
      >m</a
      ><a name="6179"
      > </a
      ><a name="6180" href="Maps.html#6147" class="Bound"
      >x</a
      ><a name="6181"
      > </a
      ><a name="6182" href="Maps.html#6126" class="Bound"
      >v</a
      ><a name="6183" class="Symbol"
      >)</a
      ><a name="6184"
      > </a
      ><a name="6185" href="Maps.html#6147" class="Bound"
      >x</a
      ><a name="6186"
      > </a
      ><a name="6187" href="Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="6188"
      > </a
      ><a name="6189" href="Maps.html#6126" class="Bound"
      >v</a
      ><a name="6190"
      >
  </a
      ><a name="6193" href="Maps.html#6108" class="Function"
      >update-eq&#8242;</a
      ><a name="6203"
      > </a
      ><a name="6204" href="Maps.html#6204" class="Bound"
      >m</a
      ><a name="6205"
      > </a
      ><a name="6206" href="Maps.html#6206" class="Bound"
      >x</a
      ><a name="6207"
      > </a
      ><a name="6208" class="Keyword"
      >with</a
      ><a name="6212"
      > </a
      ><a name="6213" href="Maps.html#6206" class="Bound"
      >x</a
      ><a name="6214"
      > </a
      ><a name="6215" href="Maps.html#2297" class="Function Operator"
      >&#8799;</a
      ><a name="6216"
      > </a
      ><a name="6217" href="Maps.html#6206" class="Bound"
      >x</a
      ><a name="6218"
      >
  </a
      ><a name="6221" class="Symbol"
      >...</a
      ><a name="6224"
      > </a
      ><a name="6225" class="Symbol"
      >|</a
      ><a name="6226"
      > </a
      ><a name="6227" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#520" class="InductiveConstructor"
      >yes</a
      ><a name="6230"
      > </a
      ><a name="6231" href="Maps.html#6231" class="Bound"
      >x=x</a
      ><a name="6234"
      > </a
      ><a name="6235" class="Symbol"
      >=</a
      ><a name="6236"
      > </a
      ><a name="6237" href="Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="6241"
      >
  </a
      ><a name="6244" class="Symbol"
      >...</a
      ><a name="6247"
      > </a
      ><a name="6248" class="Symbol"
      >|</a
      ><a name="6249"
      > </a
      ><a name="6250" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#547" class="InductiveConstructor"
      >no</a
      ><a name="6252"
      >  </a
      ><a name="6254" href="Maps.html#6254" class="Bound"
      >x&#8800;x</a
      ><a name="6257"
      > </a
      ><a name="6258" class="Symbol"
      >=</a
      ><a name="6259"
      > </a
      ><a name="6260" href="https://agda.github.io/agda-stdlib/Data.Empty.html#348" class="Function"
      >&#8869;-elim</a
      ><a name="6266"
      > </a
      ><a name="6267" class="Symbol"
      >(</a
      ><a name="6268" href="Maps.html#6254" class="Bound"
      >x&#8800;x</a
      ><a name="6271"
      > </a
      ><a name="6272" href="Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="6276" class="Symbol"
      >)</a
      >
{% endraw %}</pre>
</div>

#### Exercise: 2 stars, optional (update-neq)
On the other hand, if we update a map $$m$$ at a key $$x$$ and
then look up a _different_ key $$y$$ in the resulting map, we get
the same result that $$m$$ would have given:

<pre class="Agda">{% raw %}
  <a name="6533" href="Maps.html#6533" class="Function"
      >update-neq</a
      ><a name="6543"
      > </a
      ><a name="6544" class="Symbol"
      >:</a
      ><a name="6545"
      > </a
      ><a name="6546" class="Symbol"
      >&#8704;</a
      ><a name="6547"
      > </a
      ><a name="6554" class="Symbol"
      >(</a
      ><a name="6555" href="Maps.html#6555" class="Bound"
      >m</a
      ><a name="6556"
      > </a
      ><a name="6557" class="Symbol"
      >:</a
      ><a name="6558"
      > </a
      ><a name="6559" href="Maps.html#3352" class="Function"
      >TotalMap</a
      ><a name="6567"
      > </a
      ><a name="6568" href="Maps.html#6549" class="Bound"
      >A</a
      ><a name="6569" class="Symbol"
      >)</a
      ><a name="6570"
      > </a
      ><a name="6571" class="Symbol"
      >(</a
      ><a name="6572" href="Maps.html#6572" class="Bound"
      >x</a
      ><a name="6573"
      > </a
      ><a name="6574" href="Maps.html#6574" class="Bound"
      >y</a
      ><a name="6575"
      > </a
      ><a name="6576" class="Symbol"
      >:</a
      ><a name="6577"
      > </a
      ><a name="6578" href="Maps.html#2243" class="Datatype"
      >Id</a
      ><a name="6580" class="Symbol"
      >)</a
      ><a name="6581"
      >
             </a
      ><a name="6595" class="Symbol"
      >&#8594;</a
      ><a name="6596"
      > </a
      ><a name="6597" href="Maps.html#6572" class="Bound"
      >x</a
      ><a name="6598"
      > </a
      ><a name="6599" href="https://agda.github.io/agda-stdlib/Relation.Binary.Core.html#4493" class="Function Operator"
      >&#8802;</a
      ><a name="6600"
      > </a
      ><a name="6601" href="Maps.html#6574" class="Bound"
      >y</a
      ><a name="6602"
      > </a
      ><a name="6603" class="Symbol"
      >&#8594;</a
      ><a name="6604"
      > </a
      ><a name="6605" class="Symbol"
      >(</a
      ><a name="6606" href="Maps.html#4022" class="Function"
      >update</a
      ><a name="6612"
      > </a
      ><a name="6613" href="Maps.html#6555" class="Bound"
      >m</a
      ><a name="6614"
      > </a
      ><a name="6615" href="Maps.html#6572" class="Bound"
      >x</a
      ><a name="6616"
      > </a
      ><a name="6617" href="Maps.html#6551" class="Bound"
      >v</a
      ><a name="6618" class="Symbol"
      >)</a
      ><a name="6619"
      > </a
      ><a name="6620" href="Maps.html#6574" class="Bound"
      >y</a
      ><a name="6621"
      > </a
      ><a name="6622" href="Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="6623"
      > </a
      ><a name="6624" href="Maps.html#6555" class="Bound"
      >m</a
      ><a name="6625"
      > </a
      ><a name="6626" href="Maps.html#6574" class="Bound"
      >y</a
      ><a name="6627"
      >
  </a
      ><a name="6630" href="Maps.html#6533" class="Function"
      >update-neq</a
      ><a name="6640"
      > </a
      ><a name="6641" href="Maps.html#6641" class="Bound"
      >m</a
      ><a name="6642"
      > </a
      ><a name="6643" href="Maps.html#6643" class="Bound"
      >x</a
      ><a name="6644"
      > </a
      ><a name="6645" href="Maps.html#6645" class="Bound"
      >y</a
      ><a name="6646"
      > </a
      ><a name="6647" href="Maps.html#6647" class="Bound"
      >x&#8800;y</a
      ><a name="6650"
      > </a
      ><a name="6651" class="Keyword"
      >with</a
      ><a name="6655"
      > </a
      ><a name="6656" href="Maps.html#6643" class="Bound"
      >x</a
      ><a name="6657"
      > </a
      ><a name="6658" href="Maps.html#2297" class="Function Operator"
      >&#8799;</a
      ><a name="6659"
      > </a
      ><a name="6660" href="Maps.html#6645" class="Bound"
      >y</a
      ><a name="6661"
      >
  </a
      ><a name="6664" class="Symbol"
      >...</a
      ><a name="6667"
      > </a
      ><a name="6668" class="Symbol"
      >|</a
      ><a name="6669"
      > </a
      ><a name="6670" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#520" class="InductiveConstructor"
      >yes</a
      ><a name="6673"
      > </a
      ><a name="6674" href="Maps.html#6674" class="Bound"
      >x=y</a
      ><a name="6677"
      > </a
      ><a name="6678" class="Symbol"
      >=</a
      ><a name="6679"
      > </a
      ><a name="6680" href="https://agda.github.io/agda-stdlib/Data.Empty.html#348" class="Function"
      >&#8869;-elim</a
      ><a name="6686"
      > </a
      ><a name="6687" class="Symbol"
      >(</a
      ><a name="6688" href="Maps.html#6647" class="Bound"
      >x&#8800;y</a
      ><a name="6691"
      > </a
      ><a name="6692" href="Maps.html#6674" class="Bound"
      >x=y</a
      ><a name="6695" class="Symbol"
      >)</a
      ><a name="6696"
      >
  </a
      ><a name="6699" class="Symbol"
      >...</a
      ><a name="6702"
      > </a
      ><a name="6703" class="Symbol"
      >|</a
      ><a name="6704"
      > </a
      ><a name="6705" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#547" class="InductiveConstructor"
      >no</a
      ><a name="6707"
      >  </a
      ><a name="6709" class="Symbol"
      >_</a
      ><a name="6710"
      >   </a
      ><a name="6713" class="Symbol"
      >=</a
      ><a name="6714"
      > </a
      ><a name="6715" href="Agda.Builtin.Equality.html#140" class="InductiveConstructor"
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
  <a name="7091" class="Keyword"
      >postulate</a
      ><a name="7100"
      >
    </a
      ><a name="7105" href="Maps.html#7105" class="Postulate"
      >update-shadow</a
      ><a name="7118"
      > </a
      ><a name="7119" class="Symbol"
      >:</a
      ><a name="7120"
      > </a
      ><a name="7121" class="Symbol"
      >&#8704;</a
      ><a name="7122"
      > </a
      ><a name="7133" class="Symbol"
      >(</a
      ><a name="7134" href="Maps.html#7134" class="Bound"
      >m</a
      ><a name="7135"
      > </a
      ><a name="7136" class="Symbol"
      >:</a
      ><a name="7137"
      > </a
      ><a name="7138" href="Maps.html#3352" class="Function"
      >TotalMap</a
      ><a name="7146"
      > </a
      ><a name="7147" href="Maps.html#7124" class="Bound"
      >A</a
      ><a name="7148" class="Symbol"
      >)</a
      ><a name="7149"
      > </a
      ><a name="7150" class="Symbol"
      >(</a
      ><a name="7151" href="Maps.html#7151" class="Bound"
      >x</a
      ><a name="7152"
      > </a
      ><a name="7153" href="Maps.html#7153" class="Bound"
      >y</a
      ><a name="7154"
      > </a
      ><a name="7155" class="Symbol"
      >:</a
      ><a name="7156"
      > </a
      ><a name="7157" href="Maps.html#2243" class="Datatype"
      >Id</a
      ><a name="7159" class="Symbol"
      >)</a
      ><a name="7160"
      >
                  </a
      ><a name="7179" class="Symbol"
      >&#8594;</a
      ><a name="7180"
      > </a
      ><a name="7181" class="Symbol"
      >(</a
      ><a name="7182" href="Maps.html#4022" class="Function"
      >update</a
      ><a name="7188"
      > </a
      ><a name="7189" class="Symbol"
      >(</a
      ><a name="7190" href="Maps.html#4022" class="Function"
      >update</a
      ><a name="7196"
      > </a
      ><a name="7197" href="Maps.html#7134" class="Bound"
      >m</a
      ><a name="7198"
      > </a
      ><a name="7199" href="Maps.html#7151" class="Bound"
      >x</a
      ><a name="7200"
      > </a
      ><a name="7201" href="Maps.html#7126" class="Bound"
      >v1</a
      ><a name="7203" class="Symbol"
      >)</a
      ><a name="7204"
      > </a
      ><a name="7205" href="Maps.html#7151" class="Bound"
      >x</a
      ><a name="7206"
      > </a
      ><a name="7207" href="Maps.html#7129" class="Bound"
      >v2</a
      ><a name="7209" class="Symbol"
      >)</a
      ><a name="7210"
      > </a
      ><a name="7211" href="Maps.html#7153" class="Bound"
      >y</a
      ><a name="7212"
      > </a
      ><a name="7213" href="Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="7214"
      > </a
      ><a name="7215" class="Symbol"
      >(</a
      ><a name="7216" href="Maps.html#4022" class="Function"
      >update</a
      ><a name="7222"
      > </a
      ><a name="7223" href="Maps.html#7134" class="Bound"
      >m</a
      ><a name="7224"
      > </a
      ><a name="7225" href="Maps.html#7151" class="Bound"
      >x</a
      ><a name="7226"
      > </a
      ><a name="7227" href="Maps.html#7129" class="Bound"
      >v2</a
      ><a name="7229" class="Symbol"
      >)</a
      ><a name="7230"
      > </a
      ><a name="7231" href="Maps.html#7153" class="Bound"
      >y</a
      >
{% endraw %}</pre>

<div class="hidden">
<pre class="Agda">{% raw %}
  <a name="7281" href="Maps.html#7281" class="Function"
      >update-shadow&#8242;</a
      ><a name="7295"
      > </a
      ><a name="7296" class="Symbol"
      >:</a
      ><a name="7297"
      > </a
      ><a name="7298" class="Symbol"
      >&#8704;</a
      ><a name="7299"
      > </a
      ><a name="7310" class="Symbol"
      >(</a
      ><a name="7311" href="Maps.html#7311" class="Bound"
      >m</a
      ><a name="7312"
      > </a
      ><a name="7313" class="Symbol"
      >:</a
      ><a name="7314"
      > </a
      ><a name="7315" href="Maps.html#3352" class="Function"
      >TotalMap</a
      ><a name="7323"
      > </a
      ><a name="7324" href="Maps.html#7301" class="Bound"
      >A</a
      ><a name="7325" class="Symbol"
      >)</a
      ><a name="7326"
      > </a
      ><a name="7327" class="Symbol"
      >(</a
      ><a name="7328" href="Maps.html#7328" class="Bound"
      >x</a
      ><a name="7329"
      > </a
      ><a name="7330" href="Maps.html#7330" class="Bound"
      >y</a
      ><a name="7331"
      > </a
      ><a name="7332" class="Symbol"
      >:</a
      ><a name="7333"
      > </a
      ><a name="7334" href="Maps.html#2243" class="Datatype"
      >Id</a
      ><a name="7336" class="Symbol"
      >)</a
      ><a name="7337"
      >
                 </a
      ><a name="7355" class="Symbol"
      >&#8594;</a
      ><a name="7356"
      > </a
      ><a name="7357" class="Symbol"
      >(</a
      ><a name="7358" href="Maps.html#4022" class="Function"
      >update</a
      ><a name="7364"
      > </a
      ><a name="7365" class="Symbol"
      >(</a
      ><a name="7366" href="Maps.html#4022" class="Function"
      >update</a
      ><a name="7372"
      > </a
      ><a name="7373" href="Maps.html#7311" class="Bound"
      >m</a
      ><a name="7374"
      > </a
      ><a name="7375" href="Maps.html#7328" class="Bound"
      >x</a
      ><a name="7376"
      > </a
      ><a name="7377" href="Maps.html#7303" class="Bound"
      >v1</a
      ><a name="7379" class="Symbol"
      >)</a
      ><a name="7380"
      > </a
      ><a name="7381" href="Maps.html#7328" class="Bound"
      >x</a
      ><a name="7382"
      > </a
      ><a name="7383" href="Maps.html#7306" class="Bound"
      >v2</a
      ><a name="7385" class="Symbol"
      >)</a
      ><a name="7386"
      > </a
      ><a name="7387" href="Maps.html#7330" class="Bound"
      >y</a
      ><a name="7388"
      > </a
      ><a name="7389" href="Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="7390"
      > </a
      ><a name="7391" class="Symbol"
      >(</a
      ><a name="7392" href="Maps.html#4022" class="Function"
      >update</a
      ><a name="7398"
      > </a
      ><a name="7399" href="Maps.html#7311" class="Bound"
      >m</a
      ><a name="7400"
      > </a
      ><a name="7401" href="Maps.html#7328" class="Bound"
      >x</a
      ><a name="7402"
      > </a
      ><a name="7403" href="Maps.html#7306" class="Bound"
      >v2</a
      ><a name="7405" class="Symbol"
      >)</a
      ><a name="7406"
      > </a
      ><a name="7407" href="Maps.html#7330" class="Bound"
      >y</a
      ><a name="7408"
      >
  </a
      ><a name="7411" href="Maps.html#7281" class="Function"
      >update-shadow&#8242;</a
      ><a name="7425"
      > </a
      ><a name="7426" href="Maps.html#7426" class="Bound"
      >m</a
      ><a name="7427"
      > </a
      ><a name="7428" href="Maps.html#7428" class="Bound"
      >x</a
      ><a name="7429"
      > </a
      ><a name="7430" href="Maps.html#7430" class="Bound"
      >y</a
      ><a name="7431"
      >
      </a
      ><a name="7438" class="Keyword"
      >with</a
      ><a name="7442"
      > </a
      ><a name="7443" href="Maps.html#7428" class="Bound"
      >x</a
      ><a name="7444"
      > </a
      ><a name="7445" href="Maps.html#2297" class="Function Operator"
      >&#8799;</a
      ><a name="7446"
      > </a
      ><a name="7447" href="Maps.html#7430" class="Bound"
      >y</a
      ><a name="7448"
      >
  </a
      ><a name="7451" class="Symbol"
      >...</a
      ><a name="7454"
      > </a
      ><a name="7455" class="Symbol"
      >|</a
      ><a name="7456"
      > </a
      ><a name="7457" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#520" class="InductiveConstructor"
      >yes</a
      ><a name="7460"
      > </a
      ><a name="7461" href="Maps.html#7461" class="Bound"
      >x=y</a
      ><a name="7464"
      > </a
      ><a name="7465" class="Symbol"
      >=</a
      ><a name="7466"
      > </a
      ><a name="7467" href="Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="7471"
      >
  </a
      ><a name="7474" class="Symbol"
      >...</a
      ><a name="7477"
      > </a
      ><a name="7478" class="Symbol"
      >|</a
      ><a name="7479"
      > </a
      ><a name="7480" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#547" class="InductiveConstructor"
      >no</a
      ><a name="7482"
      >  </a
      ><a name="7484" href="Maps.html#7484" class="Bound"
      >x&#8800;y</a
      ><a name="7487"
      > </a
      ><a name="7488" class="Symbol"
      >=</a
      ><a name="7489"
      > </a
      ><a name="7490" href="Maps.html#6533" class="Function"
      >update-neq</a
      ><a name="7500"
      > </a
      ><a name="7501" href="Maps.html#7426" class="Bound"
      >m</a
      ><a name="7502"
      > </a
      ><a name="7503" href="Maps.html#7428" class="Bound"
      >x</a
      ><a name="7504"
      > </a
      ><a name="7505" href="Maps.html#7430" class="Bound"
      >y</a
      ><a name="7506"
      > </a
      ><a name="7507" href="Maps.html#7484" class="Bound"
      >x&#8800;y</a
      >
{% endraw %}</pre>
</div>

#### Exercise: 2 stars (update-same)
Prove the following theorem, which states that if we update a map to
assign key $$x$$ the same value as it already has in $$m$$, then the
result is equal to $$m$$:

<pre class="Agda">{% raw %}
  <a name="7747" class="Keyword"
      >postulate</a
      ><a name="7756"
      >
    </a
      ><a name="7761" href="Maps.html#7761" class="Postulate"
      >update-same</a
      ><a name="7772"
      > </a
      ><a name="7773" class="Symbol"
      >:</a
      ><a name="7774"
      > </a
      ><a name="7775" class="Symbol"
      >&#8704;</a
      ><a name="7776"
      > </a
      ><a name="7781" class="Symbol"
      >(</a
      ><a name="7782" href="Maps.html#7782" class="Bound"
      >m</a
      ><a name="7783"
      > </a
      ><a name="7784" class="Symbol"
      >:</a
      ><a name="7785"
      > </a
      ><a name="7786" href="Maps.html#3352" class="Function"
      >TotalMap</a
      ><a name="7794"
      > </a
      ><a name="7795" href="Maps.html#7778" class="Bound"
      >A</a
      ><a name="7796" class="Symbol"
      >)</a
      ><a name="7797"
      > </a
      ><a name="7798" class="Symbol"
      >(</a
      ><a name="7799" href="Maps.html#7799" class="Bound"
      >x</a
      ><a name="7800"
      > </a
      ><a name="7801" href="Maps.html#7801" class="Bound"
      >y</a
      ><a name="7802"
      > </a
      ><a name="7803" class="Symbol"
      >:</a
      ><a name="7804"
      > </a
      ><a name="7805" href="Maps.html#2243" class="Datatype"
      >Id</a
      ><a name="7807" class="Symbol"
      >)</a
      ><a name="7808"
      >
                </a
      ><a name="7825" class="Symbol"
      >&#8594;</a
      ><a name="7826"
      > </a
      ><a name="7827" class="Symbol"
      >(</a
      ><a name="7828" href="Maps.html#4022" class="Function"
      >update</a
      ><a name="7834"
      > </a
      ><a name="7835" href="Maps.html#7782" class="Bound"
      >m</a
      ><a name="7836"
      > </a
      ><a name="7837" href="Maps.html#7799" class="Bound"
      >x</a
      ><a name="7838"
      > </a
      ><a name="7839" class="Symbol"
      >(</a
      ><a name="7840" href="Maps.html#7782" class="Bound"
      >m</a
      ><a name="7841"
      > </a
      ><a name="7842" href="Maps.html#7799" class="Bound"
      >x</a
      ><a name="7843" class="Symbol"
      >))</a
      ><a name="7845"
      > </a
      ><a name="7846" href="Maps.html#7801" class="Bound"
      >y</a
      ><a name="7847"
      > </a
      ><a name="7848" href="Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="7849"
      > </a
      ><a name="7850" href="Maps.html#7782" class="Bound"
      >m</a
      ><a name="7851"
      > </a
      ><a name="7852" href="Maps.html#7801" class="Bound"
      >y</a
      >
{% endraw %}</pre>

<div class="hidden">
<pre class="Agda">{% raw %}
  <a name="7902" href="Maps.html#7902" class="Function"
      >update-same&#8242;</a
      ><a name="7914"
      > </a
      ><a name="7915" class="Symbol"
      >:</a
      ><a name="7916"
      > </a
      ><a name="7917" class="Symbol"
      >&#8704;</a
      ><a name="7918"
      > </a
      ><a name="7923" class="Symbol"
      >(</a
      ><a name="7924" href="Maps.html#7924" class="Bound"
      >m</a
      ><a name="7925"
      > </a
      ><a name="7926" class="Symbol"
      >:</a
      ><a name="7927"
      > </a
      ><a name="7928" href="Maps.html#3352" class="Function"
      >TotalMap</a
      ><a name="7936"
      > </a
      ><a name="7937" href="Maps.html#7920" class="Bound"
      >A</a
      ><a name="7938" class="Symbol"
      >)</a
      ><a name="7939"
      > </a
      ><a name="7940" class="Symbol"
      >(</a
      ><a name="7941" href="Maps.html#7941" class="Bound"
      >x</a
      ><a name="7942"
      > </a
      ><a name="7943" href="Maps.html#7943" class="Bound"
      >y</a
      ><a name="7944"
      > </a
      ><a name="7945" class="Symbol"
      >:</a
      ><a name="7946"
      > </a
      ><a name="7947" href="Maps.html#2243" class="Datatype"
      >Id</a
      ><a name="7949" class="Symbol"
      >)</a
      ><a name="7950"
      >
               </a
      ><a name="7966" class="Symbol"
      >&#8594;</a
      ><a name="7967"
      > </a
      ><a name="7968" class="Symbol"
      >(</a
      ><a name="7969" href="Maps.html#4022" class="Function"
      >update</a
      ><a name="7975"
      > </a
      ><a name="7976" href="Maps.html#7924" class="Bound"
      >m</a
      ><a name="7977"
      > </a
      ><a name="7978" href="Maps.html#7941" class="Bound"
      >x</a
      ><a name="7979"
      > </a
      ><a name="7980" class="Symbol"
      >(</a
      ><a name="7981" href="Maps.html#7924" class="Bound"
      >m</a
      ><a name="7982"
      > </a
      ><a name="7983" href="Maps.html#7941" class="Bound"
      >x</a
      ><a name="7984" class="Symbol"
      >))</a
      ><a name="7986"
      > </a
      ><a name="7987" href="Maps.html#7943" class="Bound"
      >y</a
      ><a name="7988"
      > </a
      ><a name="7989" href="Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="7990"
      > </a
      ><a name="7991" href="Maps.html#7924" class="Bound"
      >m</a
      ><a name="7992"
      > </a
      ><a name="7993" href="Maps.html#7943" class="Bound"
      >y</a
      ><a name="7994"
      >
  </a
      ><a name="7997" href="Maps.html#7902" class="Function"
      >update-same&#8242;</a
      ><a name="8009"
      > </a
      ><a name="8010" href="Maps.html#8010" class="Bound"
      >m</a
      ><a name="8011"
      > </a
      ><a name="8012" href="Maps.html#8012" class="Bound"
      >x</a
      ><a name="8013"
      > </a
      ><a name="8014" href="Maps.html#8014" class="Bound"
      >y</a
      ><a name="8015"
      >
    </a
      ><a name="8020" class="Keyword"
      >with</a
      ><a name="8024"
      > </a
      ><a name="8025" href="Maps.html#8012" class="Bound"
      >x</a
      ><a name="8026"
      > </a
      ><a name="8027" href="Maps.html#2297" class="Function Operator"
      >&#8799;</a
      ><a name="8028"
      > </a
      ><a name="8029" href="Maps.html#8014" class="Bound"
      >y</a
      ><a name="8030"
      >
  </a
      ><a name="8033" class="Symbol"
      >...</a
      ><a name="8036"
      > </a
      ><a name="8037" class="Symbol"
      >|</a
      ><a name="8038"
      > </a
      ><a name="8039" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#520" class="InductiveConstructor"
      >yes</a
      ><a name="8042"
      > </a
      ><a name="8043" href="Maps.html#8043" class="Bound"
      >x=y</a
      ><a name="8046"
      > </a
      ><a name="8047" class="Keyword"
      >rewrite</a
      ><a name="8054"
      > </a
      ><a name="8055" href="Maps.html#8043" class="Bound"
      >x=y</a
      ><a name="8058"
      > </a
      ><a name="8059" class="Symbol"
      >=</a
      ><a name="8060"
      > </a
      ><a name="8061" href="Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="8065"
      >
  </a
      ><a name="8068" class="Symbol"
      >...</a
      ><a name="8071"
      > </a
      ><a name="8072" class="Symbol"
      >|</a
      ><a name="8073"
      > </a
      ><a name="8074" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#547" class="InductiveConstructor"
      >no</a
      ><a name="8076"
      >  </a
      ><a name="8078" href="Maps.html#8078" class="Bound"
      >x&#8800;y</a
      ><a name="8081"
      > </a
      ><a name="8082" class="Symbol"
      >=</a
      ><a name="8083"
      > </a
      ><a name="8084" href="Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      >
{% endraw %}</pre>
</div>

#### Exercise: 3 stars, recommended (update-permute)
Prove one final property of the `update` function: If we update a map
$$m$$ at two distinct keys, it doesn't matter in which order we do the
updates.

<pre class="Agda">{% raw %}
  <a name="8327" class="Keyword"
      >postulate</a
      ><a name="8336"
      >
    </a
      ><a name="8341" href="Maps.html#8341" class="Postulate"
      >update-permute</a
      ><a name="8355"
      > </a
      ><a name="8356" class="Symbol"
      >:</a
      ><a name="8357"
      > </a
      ><a name="8358" class="Symbol"
      >&#8704;</a
      ><a name="8359"
      > </a
      ><a name="8370" class="Symbol"
      >(</a
      ><a name="8371" href="Maps.html#8371" class="Bound"
      >m</a
      ><a name="8372"
      > </a
      ><a name="8373" class="Symbol"
      >:</a
      ><a name="8374"
      > </a
      ><a name="8375" href="Maps.html#3352" class="Function"
      >TotalMap</a
      ><a name="8383"
      > </a
      ><a name="8384" href="Maps.html#8361" class="Bound"
      >A</a
      ><a name="8385" class="Symbol"
      >)</a
      ><a name="8386"
      > </a
      ><a name="8387" class="Symbol"
      >(</a
      ><a name="8388" href="Maps.html#8388" class="Bound"
      >x1</a
      ><a name="8390"
      > </a
      ><a name="8391" href="Maps.html#8391" class="Bound"
      >x2</a
      ><a name="8393"
      > </a
      ><a name="8394" href="Maps.html#8394" class="Bound"
      >y</a
      ><a name="8395"
      > </a
      ><a name="8396" class="Symbol"
      >:</a
      ><a name="8397"
      > </a
      ><a name="8398" href="Maps.html#2243" class="Datatype"
      >Id</a
      ><a name="8400" class="Symbol"
      >)</a
      ><a name="8401"
      >
                   </a
      ><a name="8421" class="Symbol"
      >&#8594;</a
      ><a name="8422"
      > </a
      ><a name="8423" href="Maps.html#8388" class="Bound"
      >x1</a
      ><a name="8425"
      > </a
      ><a name="8426" href="https://agda.github.io/agda-stdlib/Relation.Binary.Core.html#4493" class="Function Operator"
      >&#8802;</a
      ><a name="8427"
      > </a
      ><a name="8428" href="Maps.html#8391" class="Bound"
      >x2</a
      ><a name="8430"
      > </a
      ><a name="8431" class="Symbol"
      >&#8594;</a
      ><a name="8432"
      > </a
      ><a name="8433" class="Symbol"
      >(</a
      ><a name="8434" href="Maps.html#4022" class="Function"
      >update</a
      ><a name="8440"
      > </a
      ><a name="8441" class="Symbol"
      >(</a
      ><a name="8442" href="Maps.html#4022" class="Function"
      >update</a
      ><a name="8448"
      > </a
      ><a name="8449" href="Maps.html#8371" class="Bound"
      >m</a
      ><a name="8450"
      > </a
      ><a name="8451" href="Maps.html#8391" class="Bound"
      >x2</a
      ><a name="8453"
      > </a
      ><a name="8454" href="Maps.html#8366" class="Bound"
      >v2</a
      ><a name="8456" class="Symbol"
      >)</a
      ><a name="8457"
      > </a
      ><a name="8458" href="Maps.html#8388" class="Bound"
      >x1</a
      ><a name="8460"
      > </a
      ><a name="8461" href="Maps.html#8363" class="Bound"
      >v1</a
      ><a name="8463" class="Symbol"
      >)</a
      ><a name="8464"
      > </a
      ><a name="8465" href="Maps.html#8394" class="Bound"
      >y</a
      ><a name="8466"
      >
                             </a
      ><a name="8496" href="Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="8497"
      > </a
      ><a name="8498" class="Symbol"
      >(</a
      ><a name="8499" href="Maps.html#4022" class="Function"
      >update</a
      ><a name="8505"
      > </a
      ><a name="8506" class="Symbol"
      >(</a
      ><a name="8507" href="Maps.html#4022" class="Function"
      >update</a
      ><a name="8513"
      > </a
      ><a name="8514" href="Maps.html#8371" class="Bound"
      >m</a
      ><a name="8515"
      > </a
      ><a name="8516" href="Maps.html#8388" class="Bound"
      >x1</a
      ><a name="8518"
      > </a
      ><a name="8519" href="Maps.html#8363" class="Bound"
      >v1</a
      ><a name="8521" class="Symbol"
      >)</a
      ><a name="8522"
      > </a
      ><a name="8523" href="Maps.html#8391" class="Bound"
      >x2</a
      ><a name="8525"
      > </a
      ><a name="8526" href="Maps.html#8366" class="Bound"
      >v2</a
      ><a name="8528" class="Symbol"
      >)</a
      ><a name="8529"
      > </a
      ><a name="8530" href="Maps.html#8394" class="Bound"
      >y</a
      >
{% endraw %}</pre>

<div class="hidden">
<pre class="Agda">{% raw %}
  <a name="8580" href="Maps.html#8580" class="Function"
      >update-permute&#8242;</a
      ><a name="8595"
      > </a
      ><a name="8596" class="Symbol"
      >:</a
      ><a name="8597"
      > </a
      ><a name="8598" class="Symbol"
      >&#8704;</a
      ><a name="8599"
      > </a
      ><a name="8610" class="Symbol"
      >(</a
      ><a name="8611" href="Maps.html#8611" class="Bound"
      >m</a
      ><a name="8612"
      > </a
      ><a name="8613" class="Symbol"
      >:</a
      ><a name="8614"
      > </a
      ><a name="8615" href="Maps.html#3352" class="Function"
      >TotalMap</a
      ><a name="8623"
      > </a
      ><a name="8624" href="Maps.html#8601" class="Bound"
      >A</a
      ><a name="8625" class="Symbol"
      >)</a
      ><a name="8626"
      > </a
      ><a name="8627" class="Symbol"
      >(</a
      ><a name="8628" href="Maps.html#8628" class="Bound"
      >x1</a
      ><a name="8630"
      > </a
      ><a name="8631" href="Maps.html#8631" class="Bound"
      >x2</a
      ><a name="8633"
      > </a
      ><a name="8634" href="Maps.html#8634" class="Bound"
      >y</a
      ><a name="8635"
      > </a
      ><a name="8636" class="Symbol"
      >:</a
      ><a name="8637"
      > </a
      ><a name="8638" href="Maps.html#2243" class="Datatype"
      >Id</a
      ><a name="8640" class="Symbol"
      >)</a
      ><a name="8641"
      >
                  </a
      ><a name="8660" class="Symbol"
      >&#8594;</a
      ><a name="8661"
      > </a
      ><a name="8662" href="Maps.html#8628" class="Bound"
      >x1</a
      ><a name="8664"
      > </a
      ><a name="8665" href="https://agda.github.io/agda-stdlib/Relation.Binary.Core.html#4493" class="Function Operator"
      >&#8802;</a
      ><a name="8666"
      > </a
      ><a name="8667" href="Maps.html#8631" class="Bound"
      >x2</a
      ><a name="8669"
      > </a
      ><a name="8670" class="Symbol"
      >&#8594;</a
      ><a name="8671"
      > </a
      ><a name="8672" class="Symbol"
      >(</a
      ><a name="8673" href="Maps.html#4022" class="Function"
      >update</a
      ><a name="8679"
      > </a
      ><a name="8680" class="Symbol"
      >(</a
      ><a name="8681" href="Maps.html#4022" class="Function"
      >update</a
      ><a name="8687"
      > </a
      ><a name="8688" href="Maps.html#8611" class="Bound"
      >m</a
      ><a name="8689"
      > </a
      ><a name="8690" href="Maps.html#8631" class="Bound"
      >x2</a
      ><a name="8692"
      > </a
      ><a name="8693" href="Maps.html#8606" class="Bound"
      >v2</a
      ><a name="8695" class="Symbol"
      >)</a
      ><a name="8696"
      > </a
      ><a name="8697" href="Maps.html#8628" class="Bound"
      >x1</a
      ><a name="8699"
      > </a
      ><a name="8700" href="Maps.html#8603" class="Bound"
      >v1</a
      ><a name="8702" class="Symbol"
      >)</a
      ><a name="8703"
      > </a
      ><a name="8704" href="Maps.html#8634" class="Bound"
      >y</a
      ><a name="8705"
      >
                            </a
      ><a name="8734" href="Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="8735"
      > </a
      ><a name="8736" class="Symbol"
      >(</a
      ><a name="8737" href="Maps.html#4022" class="Function"
      >update</a
      ><a name="8743"
      > </a
      ><a name="8744" class="Symbol"
      >(</a
      ><a name="8745" href="Maps.html#4022" class="Function"
      >update</a
      ><a name="8751"
      > </a
      ><a name="8752" href="Maps.html#8611" class="Bound"
      >m</a
      ><a name="8753"
      > </a
      ><a name="8754" href="Maps.html#8628" class="Bound"
      >x1</a
      ><a name="8756"
      > </a
      ><a name="8757" href="Maps.html#8603" class="Bound"
      >v1</a
      ><a name="8759" class="Symbol"
      >)</a
      ><a name="8760"
      > </a
      ><a name="8761" href="Maps.html#8631" class="Bound"
      >x2</a
      ><a name="8763"
      > </a
      ><a name="8764" href="Maps.html#8606" class="Bound"
      >v2</a
      ><a name="8766" class="Symbol"
      >)</a
      ><a name="8767"
      > </a
      ><a name="8768" href="Maps.html#8634" class="Bound"
      >y</a
      ><a name="8769"
      >
  </a
      ><a name="8772" href="Maps.html#8580" class="Function"
      >update-permute&#8242;</a
      ><a name="8787"
      > </a
      ><a name="8802" href="Maps.html#8802" class="Bound"
      >m</a
      ><a name="8803"
      > </a
      ><a name="8804" href="Maps.html#8804" class="Bound"
      >x1</a
      ><a name="8806"
      > </a
      ><a name="8807" href="Maps.html#8807" class="Bound"
      >x2</a
      ><a name="8809"
      > </a
      ><a name="8810" href="Maps.html#8810" class="Bound"
      >y</a
      ><a name="8811"
      > </a
      ><a name="8812" href="Maps.html#8812" class="Bound"
      >x1&#8800;x2</a
      ><a name="8817"
      >
    </a
      ><a name="8822" class="Keyword"
      >with</a
      ><a name="8826"
      > </a
      ><a name="8827" href="Maps.html#8804" class="Bound"
      >x1</a
      ><a name="8829"
      > </a
      ><a name="8830" href="Maps.html#2297" class="Function Operator"
      >&#8799;</a
      ><a name="8831"
      > </a
      ><a name="8832" href="Maps.html#8810" class="Bound"
      >y</a
      ><a name="8833"
      > </a
      ><a name="8834" class="Symbol"
      >|</a
      ><a name="8835"
      > </a
      ><a name="8836" href="Maps.html#8807" class="Bound"
      >x2</a
      ><a name="8838"
      > </a
      ><a name="8839" href="Maps.html#2297" class="Function Operator"
      >&#8799;</a
      ><a name="8840"
      > </a
      ><a name="8841" href="Maps.html#8810" class="Bound"
      >y</a
      ><a name="8842"
      >
  </a
      ><a name="8845" class="Symbol"
      >...</a
      ><a name="8848"
      > </a
      ><a name="8849" class="Symbol"
      >|</a
      ><a name="8850"
      > </a
      ><a name="8851" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#520" class="InductiveConstructor"
      >yes</a
      ><a name="8854"
      > </a
      ><a name="8855" href="Maps.html#8855" class="Bound"
      >x1=y</a
      ><a name="8859"
      > </a
      ><a name="8860" class="Symbol"
      >|</a
      ><a name="8861"
      > </a
      ><a name="8862" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#520" class="InductiveConstructor"
      >yes</a
      ><a name="8865"
      > </a
      ><a name="8866" href="Maps.html#8866" class="Bound"
      >x2=y</a
      ><a name="8870"
      > </a
      ><a name="8871" class="Symbol"
      >=</a
      ><a name="8872"
      > </a
      ><a name="8873" href="https://agda.github.io/agda-stdlib/Data.Empty.html#348" class="Function"
      >&#8869;-elim</a
      ><a name="8879"
      > </a
      ><a name="8880" class="Symbol"
      >(</a
      ><a name="8881" href="Maps.html#8812" class="Bound"
      >x1&#8800;x2</a
      ><a name="8886"
      > </a
      ><a name="8887" class="Symbol"
      >(</a
      ><a name="8888" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.Core.html#632" class="Function"
      >trans</a
      ><a name="8893"
      > </a
      ><a name="8894" href="Maps.html#8855" class="Bound"
      >x1=y</a
      ><a name="8898"
      > </a
      ><a name="8899" class="Symbol"
      >(</a
      ><a name="8900" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.Core.html#565" class="Function"
      >sym</a
      ><a name="8903"
      > </a
      ><a name="8904" href="Maps.html#8866" class="Bound"
      >x2=y</a
      ><a name="8908" class="Symbol"
      >)))</a
      ><a name="8911"
      >
  </a
      ><a name="8914" class="Symbol"
      >...</a
      ><a name="8917"
      > </a
      ><a name="8918" class="Symbol"
      >|</a
      ><a name="8919"
      > </a
      ><a name="8920" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#547" class="InductiveConstructor"
      >no</a
      ><a name="8922"
      >  </a
      ><a name="8924" href="Maps.html#8924" class="Bound"
      >x1&#8800;y</a
      ><a name="8928"
      > </a
      ><a name="8929" class="Symbol"
      >|</a
      ><a name="8930"
      > </a
      ><a name="8931" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#520" class="InductiveConstructor"
      >yes</a
      ><a name="8934"
      > </a
      ><a name="8935" href="Maps.html#8935" class="Bound"
      >x2=y</a
      ><a name="8939"
      > </a
      ><a name="8940" class="Keyword"
      >rewrite</a
      ><a name="8947"
      > </a
      ><a name="8948" href="Maps.html#8935" class="Bound"
      >x2=y</a
      ><a name="8952"
      > </a
      ><a name="8953" class="Symbol"
      >=</a
      ><a name="8954"
      > </a
      ><a name="8955" href="Maps.html#6108" class="Function"
      >update-eq&#8242;</a
      ><a name="8965"
      > </a
      ><a name="8966" href="Maps.html#8802" class="Bound"
      >m</a
      ><a name="8967"
      > </a
      ><a name="8968" href="Maps.html#8810" class="Bound"
      >y</a
      ><a name="8969"
      >
  </a
      ><a name="8972" class="Symbol"
      >...</a
      ><a name="8975"
      > </a
      ><a name="8976" class="Symbol"
      >|</a
      ><a name="8977"
      > </a
      ><a name="8978" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#520" class="InductiveConstructor"
      >yes</a
      ><a name="8981"
      > </a
      ><a name="8982" href="Maps.html#8982" class="Bound"
      >x1=y</a
      ><a name="8986"
      > </a
      ><a name="8987" class="Symbol"
      >|</a
      ><a name="8988"
      > </a
      ><a name="8989" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#547" class="InductiveConstructor"
      >no</a
      ><a name="8991"
      >  </a
      ><a name="8993" href="Maps.html#8993" class="Bound"
      >x2&#8800;y</a
      ><a name="8997"
      > </a
      ><a name="8998" class="Keyword"
      >rewrite</a
      ><a name="9005"
      > </a
      ><a name="9006" href="Maps.html#8982" class="Bound"
      >x1=y</a
      ><a name="9010"
      > </a
      ><a name="9011" class="Symbol"
      >=</a
      ><a name="9012"
      > </a
      ><a name="9013" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.Core.html#565" class="Function"
      >sym</a
      ><a name="9016"
      > </a
      ><a name="9017" class="Symbol"
      >(</a
      ><a name="9018" href="Maps.html#6108" class="Function"
      >update-eq&#8242;</a
      ><a name="9028"
      > </a
      ><a name="9029" href="Maps.html#8802" class="Bound"
      >m</a
      ><a name="9030"
      > </a
      ><a name="9031" href="Maps.html#8810" class="Bound"
      >y</a
      ><a name="9032" class="Symbol"
      >)</a
      ><a name="9033"
      >
  </a
      ><a name="9036" class="Symbol"
      >...</a
      ><a name="9039"
      > </a
      ><a name="9040" class="Symbol"
      >|</a
      ><a name="9041"
      > </a
      ><a name="9042" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#547" class="InductiveConstructor"
      >no</a
      ><a name="9044"
      >  </a
      ><a name="9046" href="Maps.html#9046" class="Bound"
      >x1&#8800;y</a
      ><a name="9050"
      > </a
      ><a name="9051" class="Symbol"
      >|</a
      ><a name="9052"
      > </a
      ><a name="9053" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#547" class="InductiveConstructor"
      >no</a
      ><a name="9055"
      >  </a
      ><a name="9057" href="Maps.html#9057" class="Bound"
      >x2&#8800;y</a
      ><a name="9061"
      > </a
      ><a name="9062" class="Symbol"
      >=</a
      ><a name="9063"
      >
    </a
      ><a name="9068" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.Core.html#632" class="Function"
      >trans</a
      ><a name="9073"
      > </a
      ><a name="9074" class="Symbol"
      >(</a
      ><a name="9075" href="Maps.html#6533" class="Function"
      >update-neq</a
      ><a name="9085"
      > </a
      ><a name="9086" href="Maps.html#8802" class="Bound"
      >m</a
      ><a name="9087"
      > </a
      ><a name="9088" href="Maps.html#8807" class="Bound"
      >x2</a
      ><a name="9090"
      > </a
      ><a name="9091" href="Maps.html#8810" class="Bound"
      >y</a
      ><a name="9092"
      > </a
      ><a name="9093" href="Maps.html#9057" class="Bound"
      >x2&#8800;y</a
      ><a name="9097" class="Symbol"
      >)</a
      ><a name="9098"
      > </a
      ><a name="9099" class="Symbol"
      >(</a
      ><a name="9100" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.Core.html#565" class="Function"
      >sym</a
      ><a name="9103"
      > </a
      ><a name="9104" class="Symbol"
      >(</a
      ><a name="9105" href="Maps.html#6533" class="Function"
      >update-neq</a
      ><a name="9115"
      > </a
      ><a name="9116" href="Maps.html#8802" class="Bound"
      >m</a
      ><a name="9117"
      > </a
      ><a name="9118" href="Maps.html#8804" class="Bound"
      >x1</a
      ><a name="9120"
      > </a
      ><a name="9121" href="Maps.html#8810" class="Bound"
      >y</a
      ><a name="9122"
      > </a
      ><a name="9123" href="Maps.html#9046" class="Bound"
      >x1&#8800;y</a
      ><a name="9127" class="Symbol"
      >))</a
      >
{% endraw %}</pre>
</div>

## Partial maps

Finally, we define _partial maps_ on top of total maps.  A partial
map with elements of type `A` is simply a total map with elements
of type `Maybe A` and default element `nothing`.

<pre class="Agda">{% raw %}
<a name="9362" href="Maps.html#9362" class="Function"
      >PartialMap</a
      ><a name="9372"
      > </a
      ><a name="9373" class="Symbol"
      >:</a
      ><a name="9374"
      > </a
      ><a name="9375" class="PrimitiveType"
      >Set</a
      ><a name="9378"
      > </a
      ><a name="9379" class="Symbol"
      >&#8594;</a
      ><a name="9380"
      > </a
      ><a name="9381" class="PrimitiveType"
      >Set</a
      ><a name="9384"
      >
</a
      ><a name="9385" href="Maps.html#9362" class="Function"
      >PartialMap</a
      ><a name="9395"
      > </a
      ><a name="9396" href="Maps.html#9396" class="Bound"
      >A</a
      ><a name="9397"
      > </a
      ><a name="9398" class="Symbol"
      >=</a
      ><a name="9399"
      > </a
      ><a name="9400" href="Maps.html#3352" class="Function"
      >TotalMap</a
      ><a name="9408"
      > </a
      ><a name="9409" class="Symbol"
      >(</a
      ><a name="9410" href="https://agda.github.io/agda-stdlib/Data.Maybe.Base.html#335" class="Datatype"
      >Maybe</a
      ><a name="9415"
      > </a
      ><a name="9416" href="Maps.html#9396" class="Bound"
      >A</a
      ><a name="9417" class="Symbol"
      >)</a
      >
{% endraw %}</pre>

<pre class="Agda">{% raw %}
<a name="9444" class="Keyword"
      >module</a
      ><a name="9450"
      > </a
      ><a name="9451" href="Maps.html#9451" class="Module"
      >PartialMap</a
      ><a name="9461"
      > </a
      ><a name="9462" class="Keyword"
      >where</a
      >
{% endraw %}</pre>

<pre class="Agda">{% raw %}
  <a name="9495" href="Maps.html#9495" class="Function"
      >empty</a
      ><a name="9500"
      > </a
      ><a name="9501" class="Symbol"
      >:</a
      ><a name="9502"
      > </a
      ><a name="9503" class="Symbol"
      >&#8704;</a
      ><a name="9504"
      > </a
      ><a name="9509" class="Symbol"
      >&#8594;</a
      ><a name="9510"
      > </a
      ><a name="9511" href="Maps.html#9362" class="Function"
      >PartialMap</a
      ><a name="9521"
      > </a
      ><a name="9522" href="Maps.html#9506" class="Bound"
      >A</a
      ><a name="9523"
      >
  </a
      ><a name="9526" href="Maps.html#9495" class="Function"
      >empty</a
      ><a name="9531"
      > </a
      ><a name="9532" class="Symbol"
      >=</a
      ><a name="9533"
      > </a
      ><a name="9534" href="Maps.html#3734" class="Function"
      >TotalMap.empty</a
      ><a name="9548"
      > </a
      ><a name="9549" href="https://agda.github.io/agda-stdlib/Data.Maybe.Base.html#403" class="InductiveConstructor"
      >nothing</a
      >
{% endraw %}</pre>

<pre class="Agda">{% raw %}
  <a name="9584" href="Maps.html#9584" class="Function"
      >update</a
      ><a name="9590"
      > </a
      ><a name="9591" class="Symbol"
      >:</a
      ><a name="9592"
      > </a
      ><a name="9593" class="Symbol"
      >&#8704;</a
      ><a name="9594"
      > </a
      ><a name="9599" class="Symbol"
      >(</a
      ><a name="9600" href="Maps.html#9600" class="Bound"
      >m</a
      ><a name="9601"
      > </a
      ><a name="9602" class="Symbol"
      >:</a
      ><a name="9603"
      > </a
      ><a name="9604" href="Maps.html#9362" class="Function"
      >PartialMap</a
      ><a name="9614"
      > </a
      ><a name="9615" href="Maps.html#9596" class="Bound"
      >A</a
      ><a name="9616" class="Symbol"
      >)</a
      ><a name="9617"
      > </a
      ><a name="9618" class="Symbol"
      >(</a
      ><a name="9619" href="Maps.html#9619" class="Bound"
      >x</a
      ><a name="9620"
      > </a
      ><a name="9621" class="Symbol"
      >:</a
      ><a name="9622"
      > </a
      ><a name="9623" href="Maps.html#2243" class="Datatype"
      >Id</a
      ><a name="9625" class="Symbol"
      >)</a
      ><a name="9626"
      > </a
      ><a name="9627" class="Symbol"
      >(</a
      ><a name="9628" href="Maps.html#9628" class="Bound"
      >v</a
      ><a name="9629"
      > </a
      ><a name="9630" class="Symbol"
      >:</a
      ><a name="9631"
      > </a
      ><a name="9632" href="Maps.html#9596" class="Bound"
      >A</a
      ><a name="9633" class="Symbol"
      >)</a
      ><a name="9634"
      > </a
      ><a name="9635" class="Symbol"
      >&#8594;</a
      ><a name="9636"
      > </a
      ><a name="9637" href="Maps.html#9362" class="Function"
      >PartialMap</a
      ><a name="9647"
      > </a
      ><a name="9648" href="Maps.html#9596" class="Bound"
      >A</a
      ><a name="9649"
      >
  </a
      ><a name="9652" href="Maps.html#9584" class="Function"
      >update</a
      ><a name="9658"
      > </a
      ><a name="9659" href="Maps.html#9659" class="Bound"
      >m</a
      ><a name="9660"
      > </a
      ><a name="9661" href="Maps.html#9661" class="Bound"
      >x</a
      ><a name="9662"
      > </a
      ><a name="9663" href="Maps.html#9663" class="Bound"
      >v</a
      ><a name="9664"
      > </a
      ><a name="9665" class="Symbol"
      >=</a
      ><a name="9666"
      > </a
      ><a name="9667" href="Maps.html#4022" class="Function"
      >TotalMap.update</a
      ><a name="9682"
      > </a
      ><a name="9683" href="Maps.html#9659" class="Bound"
      >m</a
      ><a name="9684"
      > </a
      ><a name="9685" href="Maps.html#9661" class="Bound"
      >x</a
      ><a name="9686"
      > </a
      ><a name="9687" class="Symbol"
      >(</a
      ><a name="9688" href="https://agda.github.io/agda-stdlib/Data.Maybe.Base.html#373" class="InductiveConstructor"
      >just</a
      ><a name="9692"
      > </a
      ><a name="9693" href="Maps.html#9663" class="Bound"
      >v</a
      ><a name="9694" class="Symbol"
      >)</a
      >
{% endraw %}</pre>

We can now lift all of the basic lemmas about total maps to
partial maps.

<pre class="Agda">{% raw %}
  <a name="9798" href="Maps.html#9798" class="Function"
      >update-eq</a
      ><a name="9807"
      > </a
      ><a name="9808" class="Symbol"
      >:</a
      ><a name="9809"
      > </a
      ><a name="9810" class="Symbol"
      >&#8704;</a
      ><a name="9811"
      > </a
      ><a name="9818" class="Symbol"
      >(</a
      ><a name="9819" href="Maps.html#9819" class="Bound"
      >m</a
      ><a name="9820"
      > </a
      ><a name="9821" class="Symbol"
      >:</a
      ><a name="9822"
      > </a
      ><a name="9823" href="Maps.html#9362" class="Function"
      >PartialMap</a
      ><a name="9833"
      > </a
      ><a name="9834" href="Maps.html#9813" class="Bound"
      >A</a
      ><a name="9835" class="Symbol"
      >)</a
      ><a name="9836"
      > </a
      ><a name="9837" class="Symbol"
      >(</a
      ><a name="9838" href="Maps.html#9838" class="Bound"
      >x</a
      ><a name="9839"
      > </a
      ><a name="9840" class="Symbol"
      >:</a
      ><a name="9841"
      > </a
      ><a name="9842" href="Maps.html#2243" class="Datatype"
      >Id</a
      ><a name="9844" class="Symbol"
      >)</a
      ><a name="9845"
      >
            </a
      ><a name="9858" class="Symbol"
      >&#8594;</a
      ><a name="9859"
      > </a
      ><a name="9860" class="Symbol"
      >(</a
      ><a name="9861" href="Maps.html#9584" class="Function"
      >update</a
      ><a name="9867"
      > </a
      ><a name="9868" href="Maps.html#9819" class="Bound"
      >m</a
      ><a name="9869"
      > </a
      ><a name="9870" href="Maps.html#9838" class="Bound"
      >x</a
      ><a name="9871"
      > </a
      ><a name="9872" href="Maps.html#9815" class="Bound"
      >v</a
      ><a name="9873" class="Symbol"
      >)</a
      ><a name="9874"
      > </a
      ><a name="9875" href="Maps.html#9838" class="Bound"
      >x</a
      ><a name="9876"
      > </a
      ><a name="9877" href="Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="9878"
      > </a
      ><a name="9879" href="https://agda.github.io/agda-stdlib/Data.Maybe.Base.html#373" class="InductiveConstructor"
      >just</a
      ><a name="9883"
      > </a
      ><a name="9884" href="Maps.html#9815" class="Bound"
      >v</a
      ><a name="9885"
      >
  </a
      ><a name="9888" href="Maps.html#9798" class="Function"
      >update-eq</a
      ><a name="9897"
      > </a
      ><a name="9898" href="Maps.html#9898" class="Bound"
      >m</a
      ><a name="9899"
      > </a
      ><a name="9900" href="Maps.html#9900" class="Bound"
      >x</a
      ><a name="9901"
      > </a
      ><a name="9902" class="Symbol"
      >=</a
      ><a name="9903"
      > </a
      ><a name="9904" href="Maps.html#5977" class="Postulate"
      >TotalMap.update-eq</a
      ><a name="9922"
      > </a
      ><a name="9923" href="Maps.html#9898" class="Bound"
      >m</a
      ><a name="9924"
      > </a
      ><a name="9925" href="Maps.html#9900" class="Bound"
      >x</a
      >
{% endraw %}</pre>

<pre class="Agda">{% raw %}
  <a name="9954" href="Maps.html#9954" class="Function"
      >update-neq</a
      ><a name="9964"
      > </a
      ><a name="9965" class="Symbol"
      >:</a
      ><a name="9966"
      > </a
      ><a name="9967" class="Symbol"
      >&#8704;</a
      ><a name="9968"
      > </a
      ><a name="9975" class="Symbol"
      >(</a
      ><a name="9976" href="Maps.html#9976" class="Bound"
      >m</a
      ><a name="9977"
      > </a
      ><a name="9978" class="Symbol"
      >:</a
      ><a name="9979"
      > </a
      ><a name="9980" href="Maps.html#9362" class="Function"
      >PartialMap</a
      ><a name="9990"
      > </a
      ><a name="9991" href="Maps.html#9970" class="Bound"
      >A</a
      ><a name="9992" class="Symbol"
      >)</a
      ><a name="9993"
      > </a
      ><a name="9994" class="Symbol"
      >(</a
      ><a name="9995" href="Maps.html#9995" class="Bound"
      >x</a
      ><a name="9996"
      > </a
      ><a name="9997" href="Maps.html#9997" class="Bound"
      >y</a
      ><a name="9998"
      > </a
      ><a name="9999" class="Symbol"
      >:</a
      ><a name="10000"
      > </a
      ><a name="10001" href="Maps.html#2243" class="Datatype"
      >Id</a
      ><a name="10003" class="Symbol"
      >)</a
      ><a name="10004"
      >
             </a
      ><a name="10018" class="Symbol"
      >&#8594;</a
      ><a name="10019"
      > </a
      ><a name="10020" href="Maps.html#9995" class="Bound"
      >x</a
      ><a name="10021"
      > </a
      ><a name="10022" href="https://agda.github.io/agda-stdlib/Relation.Binary.Core.html#4493" class="Function Operator"
      >&#8802;</a
      ><a name="10023"
      > </a
      ><a name="10024" href="Maps.html#9997" class="Bound"
      >y</a
      ><a name="10025"
      > </a
      ><a name="10026" class="Symbol"
      >&#8594;</a
      ><a name="10027"
      > </a
      ><a name="10028" class="Symbol"
      >(</a
      ><a name="10029" href="Maps.html#9584" class="Function"
      >update</a
      ><a name="10035"
      > </a
      ><a name="10036" href="Maps.html#9976" class="Bound"
      >m</a
      ><a name="10037"
      > </a
      ><a name="10038" href="Maps.html#9995" class="Bound"
      >x</a
      ><a name="10039"
      > </a
      ><a name="10040" href="Maps.html#9972" class="Bound"
      >v</a
      ><a name="10041" class="Symbol"
      >)</a
      ><a name="10042"
      > </a
      ><a name="10043" href="Maps.html#9997" class="Bound"
      >y</a
      ><a name="10044"
      > </a
      ><a name="10045" href="Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="10046"
      > </a
      ><a name="10047" href="Maps.html#9976" class="Bound"
      >m</a
      ><a name="10048"
      > </a
      ><a name="10049" href="Maps.html#9997" class="Bound"
      >y</a
      ><a name="10050"
      >
  </a
      ><a name="10053" href="Maps.html#9954" class="Function"
      >update-neq</a
      ><a name="10063"
      > </a
      ><a name="10064" href="Maps.html#10064" class="Bound"
      >m</a
      ><a name="10065"
      > </a
      ><a name="10066" href="Maps.html#10066" class="Bound"
      >x</a
      ><a name="10067"
      > </a
      ><a name="10068" href="Maps.html#10068" class="Bound"
      >y</a
      ><a name="10069"
      > </a
      ><a name="10070" href="Maps.html#10070" class="Bound"
      >x&#8800;y</a
      ><a name="10073"
      > </a
      ><a name="10074" class="Symbol"
      >=</a
      ><a name="10075"
      > </a
      ><a name="10076" href="Maps.html#6533" class="Function"
      >TotalMap.update-neq</a
      ><a name="10095"
      > </a
      ><a name="10096" href="Maps.html#10064" class="Bound"
      >m</a
      ><a name="10097"
      > </a
      ><a name="10098" href="Maps.html#10066" class="Bound"
      >x</a
      ><a name="10099"
      > </a
      ><a name="10100" href="Maps.html#10068" class="Bound"
      >y</a
      ><a name="10101"
      > </a
      ><a name="10102" href="Maps.html#10070" class="Bound"
      >x&#8800;y</a
      >
{% endraw %}</pre>

<pre class="Agda">{% raw %}
  <a name="10133" href="Maps.html#10133" class="Function"
      >update-shadow</a
      ><a name="10146"
      > </a
      ><a name="10147" class="Symbol"
      >:</a
      ><a name="10148"
      > </a
      ><a name="10149" class="Symbol"
      >&#8704;</a
      ><a name="10150"
      > </a
      ><a name="10161" class="Symbol"
      >(</a
      ><a name="10162" href="Maps.html#10162" class="Bound"
      >m</a
      ><a name="10163"
      > </a
      ><a name="10164" class="Symbol"
      >:</a
      ><a name="10165"
      > </a
      ><a name="10166" href="Maps.html#9362" class="Function"
      >PartialMap</a
      ><a name="10176"
      > </a
      ><a name="10177" href="Maps.html#10152" class="Bound"
      >A</a
      ><a name="10178" class="Symbol"
      >)</a
      ><a name="10179"
      > </a
      ><a name="10180" class="Symbol"
      >(</a
      ><a name="10181" href="Maps.html#10181" class="Bound"
      >x</a
      ><a name="10182"
      > </a
      ><a name="10183" href="Maps.html#10183" class="Bound"
      >y</a
      ><a name="10184"
      > </a
      ><a name="10185" class="Symbol"
      >:</a
      ><a name="10186"
      > </a
      ><a name="10187" href="Maps.html#2243" class="Datatype"
      >Id</a
      ><a name="10189" class="Symbol"
      >)</a
      ><a name="10190"
      >
                </a
      ><a name="10207" class="Symbol"
      >&#8594;</a
      ><a name="10208"
      > </a
      ><a name="10209" class="Symbol"
      >(</a
      ><a name="10210" href="Maps.html#9584" class="Function"
      >update</a
      ><a name="10216"
      > </a
      ><a name="10217" class="Symbol"
      >(</a
      ><a name="10218" href="Maps.html#9584" class="Function"
      >update</a
      ><a name="10224"
      > </a
      ><a name="10225" href="Maps.html#10162" class="Bound"
      >m</a
      ><a name="10226"
      > </a
      ><a name="10227" href="Maps.html#10181" class="Bound"
      >x</a
      ><a name="10228"
      > </a
      ><a name="10229" href="Maps.html#10154" class="Bound"
      >v1</a
      ><a name="10231" class="Symbol"
      >)</a
      ><a name="10232"
      > </a
      ><a name="10233" href="Maps.html#10181" class="Bound"
      >x</a
      ><a name="10234"
      > </a
      ><a name="10235" href="Maps.html#10157" class="Bound"
      >v2</a
      ><a name="10237" class="Symbol"
      >)</a
      ><a name="10238"
      > </a
      ><a name="10239" href="Maps.html#10183" class="Bound"
      >y</a
      ><a name="10240"
      > </a
      ><a name="10241" href="Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="10242"
      > </a
      ><a name="10243" class="Symbol"
      >(</a
      ><a name="10244" href="Maps.html#9584" class="Function"
      >update</a
      ><a name="10250"
      > </a
      ><a name="10251" href="Maps.html#10162" class="Bound"
      >m</a
      ><a name="10252"
      > </a
      ><a name="10253" href="Maps.html#10181" class="Bound"
      >x</a
      ><a name="10254"
      > </a
      ><a name="10255" href="Maps.html#10157" class="Bound"
      >v2</a
      ><a name="10257" class="Symbol"
      >)</a
      ><a name="10258"
      > </a
      ><a name="10259" href="Maps.html#10183" class="Bound"
      >y</a
      ><a name="10260"
      >
  </a
      ><a name="10263" href="Maps.html#10133" class="Function"
      >update-shadow</a
      ><a name="10276"
      > </a
      ><a name="10277" href="Maps.html#10277" class="Bound"
      >m</a
      ><a name="10278"
      > </a
      ><a name="10279" href="Maps.html#10279" class="Bound"
      >x</a
      ><a name="10280"
      > </a
      ><a name="10281" href="Maps.html#10281" class="Bound"
      >y</a
      ><a name="10282"
      > </a
      ><a name="10283" class="Symbol"
      >=</a
      ><a name="10284"
      > </a
      ><a name="10285" href="Maps.html#7105" class="Postulate"
      >TotalMap.update-shadow</a
      ><a name="10307"
      > </a
      ><a name="10308" href="Maps.html#10277" class="Bound"
      >m</a
      ><a name="10309"
      > </a
      ><a name="10310" href="Maps.html#10279" class="Bound"
      >x</a
      ><a name="10311"
      > </a
      ><a name="10312" href="Maps.html#10281" class="Bound"
      >y</a
      >
{% endraw %}</pre>

<pre class="Agda">{% raw %}
  <a name="10341" href="Maps.html#10341" class="Function"
      >update-same</a
      ><a name="10352"
      > </a
      ><a name="10353" class="Symbol"
      >:</a
      ><a name="10354"
      > </a
      ><a name="10355" class="Symbol"
      >&#8704;</a
      ><a name="10356"
      > </a
      ><a name="10363" class="Symbol"
      >(</a
      ><a name="10364" href="Maps.html#10364" class="Bound"
      >m</a
      ><a name="10365"
      > </a
      ><a name="10366" class="Symbol"
      >:</a
      ><a name="10367"
      > </a
      ><a name="10368" href="Maps.html#9362" class="Function"
      >PartialMap</a
      ><a name="10378"
      > </a
      ><a name="10379" href="Maps.html#10358" class="Bound"
      >A</a
      ><a name="10380" class="Symbol"
      >)</a
      ><a name="10381"
      > </a
      ><a name="10382" class="Symbol"
      >(</a
      ><a name="10383" href="Maps.html#10383" class="Bound"
      >x</a
      ><a name="10384"
      > </a
      ><a name="10385" href="Maps.html#10385" class="Bound"
      >y</a
      ><a name="10386"
      > </a
      ><a name="10387" class="Symbol"
      >:</a
      ><a name="10388"
      > </a
      ><a name="10389" href="Maps.html#2243" class="Datatype"
      >Id</a
      ><a name="10391" class="Symbol"
      >)</a
      ><a name="10392"
      >
              </a
      ><a name="10407" class="Symbol"
      >&#8594;</a
      ><a name="10408"
      > </a
      ><a name="10409" href="Maps.html#10364" class="Bound"
      >m</a
      ><a name="10410"
      > </a
      ><a name="10411" href="Maps.html#10383" class="Bound"
      >x</a
      ><a name="10412"
      > </a
      ><a name="10413" href="Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="10414"
      > </a
      ><a name="10415" href="https://agda.github.io/agda-stdlib/Data.Maybe.Base.html#373" class="InductiveConstructor"
      >just</a
      ><a name="10419"
      > </a
      ><a name="10420" href="Maps.html#10360" class="Bound"
      >v</a
      ><a name="10421"
      >
              </a
      ><a name="10436" class="Symbol"
      >&#8594;</a
      ><a name="10437"
      > </a
      ><a name="10438" class="Symbol"
      >(</a
      ><a name="10439" href="Maps.html#9584" class="Function"
      >update</a
      ><a name="10445"
      > </a
      ><a name="10446" href="Maps.html#10364" class="Bound"
      >m</a
      ><a name="10447"
      > </a
      ><a name="10448" href="Maps.html#10383" class="Bound"
      >x</a
      ><a name="10449"
      > </a
      ><a name="10450" href="Maps.html#10360" class="Bound"
      >v</a
      ><a name="10451" class="Symbol"
      >)</a
      ><a name="10452"
      > </a
      ><a name="10453" href="Maps.html#10385" class="Bound"
      >y</a
      ><a name="10454"
      > </a
      ><a name="10455" href="Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="10456"
      > </a
      ><a name="10457" href="Maps.html#10364" class="Bound"
      >m</a
      ><a name="10458"
      > </a
      ><a name="10459" href="Maps.html#10385" class="Bound"
      >y</a
      ><a name="10460"
      >
  </a
      ><a name="10463" href="Maps.html#10341" class="Function"
      >update-same</a
      ><a name="10474"
      > </a
      ><a name="10475" href="Maps.html#10475" class="Bound"
      >m</a
      ><a name="10476"
      > </a
      ><a name="10477" href="Maps.html#10477" class="Bound"
      >x</a
      ><a name="10478"
      > </a
      ><a name="10479" href="Maps.html#10479" class="Bound"
      >y</a
      ><a name="10480"
      > </a
      ><a name="10481" href="Maps.html#10481" class="Bound"
      >mx=v</a
      ><a name="10485"
      > </a
      ><a name="10486" class="Keyword"
      >rewrite</a
      ><a name="10493"
      > </a
      ><a name="10494" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.Core.html#565" class="Function"
      >sym</a
      ><a name="10497"
      > </a
      ><a name="10498" href="Maps.html#10481" class="Bound"
      >mx=v</a
      ><a name="10502"
      > </a
      ><a name="10503" class="Symbol"
      >=</a
      ><a name="10504"
      > </a
      ><a name="10505" href="Maps.html#7761" class="Postulate"
      >TotalMap.update-same</a
      ><a name="10525"
      > </a
      ><a name="10526" href="Maps.html#10475" class="Bound"
      >m</a
      ><a name="10527"
      > </a
      ><a name="10528" href="Maps.html#10477" class="Bound"
      >x</a
      ><a name="10529"
      > </a
      ><a name="10530" href="Maps.html#10479" class="Bound"
      >y</a
      >
{% endraw %}</pre>

<pre class="Agda">{% raw %}
  <a name="10559" href="Maps.html#10559" class="Function"
      >update-permute</a
      ><a name="10573"
      > </a
      ><a name="10574" class="Symbol"
      >:</a
      ><a name="10575"
      > </a
      ><a name="10576" class="Symbol"
      >&#8704;</a
      ><a name="10577"
      > </a
      ><a name="10588" class="Symbol"
      >(</a
      ><a name="10589" href="Maps.html#10589" class="Bound"
      >m</a
      ><a name="10590"
      > </a
      ><a name="10591" class="Symbol"
      >:</a
      ><a name="10592"
      > </a
      ><a name="10593" href="Maps.html#9362" class="Function"
      >PartialMap</a
      ><a name="10603"
      > </a
      ><a name="10604" href="Maps.html#10579" class="Bound"
      >A</a
      ><a name="10605" class="Symbol"
      >)</a
      ><a name="10606"
      > </a
      ><a name="10607" class="Symbol"
      >(</a
      ><a name="10608" href="Maps.html#10608" class="Bound"
      >x1</a
      ><a name="10610"
      > </a
      ><a name="10611" href="Maps.html#10611" class="Bound"
      >x2</a
      ><a name="10613"
      > </a
      ><a name="10614" href="Maps.html#10614" class="Bound"
      >y</a
      ><a name="10615"
      > </a
      ><a name="10616" class="Symbol"
      >:</a
      ><a name="10617"
      > </a
      ><a name="10618" href="Maps.html#2243" class="Datatype"
      >Id</a
      ><a name="10620" class="Symbol"
      >)</a
      ><a name="10621"
      >
                 </a
      ><a name="10639" class="Symbol"
      >&#8594;</a
      ><a name="10640"
      > </a
      ><a name="10641" href="Maps.html#10608" class="Bound"
      >x1</a
      ><a name="10643"
      > </a
      ><a name="10644" href="https://agda.github.io/agda-stdlib/Relation.Binary.Core.html#4493" class="Function Operator"
      >&#8802;</a
      ><a name="10645"
      > </a
      ><a name="10646" href="Maps.html#10611" class="Bound"
      >x2</a
      ><a name="10648"
      > </a
      ><a name="10649" class="Symbol"
      >&#8594;</a
      ><a name="10650"
      > </a
      ><a name="10651" class="Symbol"
      >(</a
      ><a name="10652" href="Maps.html#9584" class="Function"
      >update</a
      ><a name="10658"
      > </a
      ><a name="10659" class="Symbol"
      >(</a
      ><a name="10660" href="Maps.html#9584" class="Function"
      >update</a
      ><a name="10666"
      > </a
      ><a name="10667" href="Maps.html#10589" class="Bound"
      >m</a
      ><a name="10668"
      > </a
      ><a name="10669" href="Maps.html#10611" class="Bound"
      >x2</a
      ><a name="10671"
      > </a
      ><a name="10672" href="Maps.html#10584" class="Bound"
      >v2</a
      ><a name="10674" class="Symbol"
      >)</a
      ><a name="10675"
      > </a
      ><a name="10676" href="Maps.html#10608" class="Bound"
      >x1</a
      ><a name="10678"
      > </a
      ><a name="10679" href="Maps.html#10581" class="Bound"
      >v1</a
      ><a name="10681" class="Symbol"
      >)</a
      ><a name="10682"
      > </a
      ><a name="10683" href="Maps.html#10614" class="Bound"
      >y</a
      ><a name="10684"
      >
                           </a
      ><a name="10712" href="Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="10713"
      > </a
      ><a name="10714" class="Symbol"
      >(</a
      ><a name="10715" href="Maps.html#9584" class="Function"
      >update</a
      ><a name="10721"
      > </a
      ><a name="10722" class="Symbol"
      >(</a
      ><a name="10723" href="Maps.html#9584" class="Function"
      >update</a
      ><a name="10729"
      > </a
      ><a name="10730" href="Maps.html#10589" class="Bound"
      >m</a
      ><a name="10731"
      > </a
      ><a name="10732" href="Maps.html#10608" class="Bound"
      >x1</a
      ><a name="10734"
      > </a
      ><a name="10735" href="Maps.html#10581" class="Bound"
      >v1</a
      ><a name="10737" class="Symbol"
      >)</a
      ><a name="10738"
      > </a
      ><a name="10739" href="Maps.html#10611" class="Bound"
      >x2</a
      ><a name="10741"
      > </a
      ><a name="10742" href="Maps.html#10584" class="Bound"
      >v2</a
      ><a name="10744" class="Symbol"
      >)</a
      ><a name="10745"
      > </a
      ><a name="10746" href="Maps.html#10614" class="Bound"
      >y</a
      ><a name="10747"
      >
  </a
      ><a name="10750" href="Maps.html#10559" class="Function"
      >update-permute</a
      ><a name="10764"
      > </a
      ><a name="10765" href="Maps.html#10765" class="Bound"
      >m</a
      ><a name="10766"
      > </a
      ><a name="10767" href="Maps.html#10767" class="Bound"
      >x1</a
      ><a name="10769"
      > </a
      ><a name="10770" href="Maps.html#10770" class="Bound"
      >x2</a
      ><a name="10772"
      > </a
      ><a name="10773" href="Maps.html#10773" class="Bound"
      >y</a
      ><a name="10774"
      > </a
      ><a name="10775" href="Maps.html#10775" class="Bound"
      >x1&#8800;x2</a
      ><a name="10780"
      > </a
      ><a name="10781" class="Symbol"
      >=</a
      ><a name="10782"
      > </a
      ><a name="10783" href="Maps.html#8341" class="Postulate"
      >TotalMap.update-permute</a
      ><a name="10806"
      > </a
      ><a name="10807" href="Maps.html#10765" class="Bound"
      >m</a
      ><a name="10808"
      > </a
      ><a name="10809" href="Maps.html#10767" class="Bound"
      >x1</a
      ><a name="10811"
      > </a
      ><a name="10812" href="Maps.html#10770" class="Bound"
      >x2</a
      ><a name="10814"
      > </a
      ><a name="10815" href="Maps.html#10773" class="Bound"
      >y</a
      ><a name="10816"
      > </a
      ><a name="10817" href="Maps.html#10775" class="Bound"
      >x1&#8800;x2</a
      >
{% endraw %}</pre>
