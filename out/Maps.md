---
title     : "Maps: Total and Partial Maps"
layout    : page
permalink : /Maps
---

Maps (or dictionaries) are ubiquitous data structures, both in software
construction generally and in the theory of programming languages in particular;
we're going to need them in many places in the coming chapters.  They also make
a nice case study using ideas we've seen in previous chapters, including
building data structures out of higher-order functions (from [Basics]({{
"Basics" | relative_url }}) and [Poly]({{ "Poly" | relative_url }}) and the use
of reflection to streamline proofs (from [IndProp]({{ "IndProp" | relative_url
}})). 

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
<a name="1497" class="Keyword"
      >open</a
      ><a name="1501"
      > </a
      ><a name="1502" class="Keyword"
      >import</a
      ><a name="1508"
      > </a
      ><a name="1509" href="https://agda.github.io/agda-stdlib/Function.html#1" class="Module"
      >Function</a
      ><a name="1517"
      >         </a
      ><a name="1526" class="Keyword"
      >using</a
      ><a name="1531"
      > </a
      ><a name="1532" class="Symbol"
      >(</a
      ><a name="1533" href="https://agda.github.io/agda-stdlib/Function.html#713" class="Function Operator"
      >_&#8728;_</a
      ><a name="1536" class="Symbol"
      >)</a
      ><a name="1537"
      >
</a
      ><a name="1538" class="Keyword"
      >open</a
      ><a name="1542"
      > </a
      ><a name="1543" class="Keyword"
      >import</a
      ><a name="1549"
      > </a
      ><a name="1550" href="https://agda.github.io/agda-stdlib/Data.Bool.html#1" class="Module"
      >Data.Bool</a
      ><a name="1559"
      >        </a
      ><a name="1567" class="Keyword"
      >using</a
      ><a name="1572"
      > </a
      ><a name="1573" class="Symbol"
      >(</a
      ><a name="1574" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Bool.html#67" class="Datatype"
      >Bool</a
      ><a name="1578" class="Symbol"
      >;</a
      ><a name="1579"
      > </a
      ><a name="1580" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Bool.html#92" class="InductiveConstructor"
      >true</a
      ><a name="1584" class="Symbol"
      >;</a
      ><a name="1585"
      > </a
      ><a name="1586" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Bool.html#86" class="InductiveConstructor"
      >false</a
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
      ><a name="1605" href="https://agda.github.io/agda-stdlib/Data.Empty.html#1" class="Module"
      >Data.Empty</a
      ><a name="1615"
      >       </a
      ><a name="1622" class="Keyword"
      >using</a
      ><a name="1627"
      > </a
      ><a name="1628" class="Symbol"
      >(</a
      ><a name="1629" href="https://agda.github.io/agda-stdlib/Data.Empty.html#243" class="Datatype"
      >&#8869;</a
      ><a name="1630" class="Symbol"
      >;</a
      ><a name="1631"
      > </a
      ><a name="1632" href="https://agda.github.io/agda-stdlib/Data.Empty.html#360" class="Function"
      >&#8869;-elim</a
      ><a name="1638" class="Symbol"
      >)</a
      ><a name="1639"
      >
</a
      ><a name="1640" class="Keyword"
      >open</a
      ><a name="1644"
      > </a
      ><a name="1645" class="Keyword"
      >import</a
      ><a name="1651"
      > </a
      ><a name="1652" href="https://agda.github.io/agda-stdlib/Data.Maybe.html#1" class="Module"
      >Data.Maybe</a
      ><a name="1662"
      >       </a
      ><a name="1669" class="Keyword"
      >using</a
      ><a name="1674"
      > </a
      ><a name="1675" class="Symbol"
      >(</a
      ><a name="1676" href="https://agda.github.io/agda-stdlib/Data.Maybe.Base.html#335" class="Datatype"
      >Maybe</a
      ><a name="1681" class="Symbol"
      >;</a
      ><a name="1682"
      > </a
      ><a name="1683" href="https://agda.github.io/agda-stdlib/Data.Maybe.html#1527" class="InductiveConstructor"
      >just</a
      ><a name="1687" class="Symbol"
      >;</a
      ><a name="1688"
      > </a
      ><a name="1689" href="https://agda.github.io/agda-stdlib/Data.Maybe.html#1588" class="InductiveConstructor"
      >nothing</a
      ><a name="1696" class="Symbol"
      >)</a
      ><a name="1697"
      >
</a
      ><a name="1698" class="Keyword"
      >open</a
      ><a name="1702"
      > </a
      ><a name="1703" class="Keyword"
      >import</a
      ><a name="1709"
      > </a
      ><a name="1710" href="https://agda.github.io/agda-stdlib/Data.Nat.html#1" class="Module"
      >Data.Nat</a
      ><a name="1718"
      >         </a
      ><a name="1727" class="Keyword"
      >using</a
      ><a name="1732"
      > </a
      ><a name="1733" class="Symbol"
      >(</a
      ><a name="1734" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#97" class="Datatype"
      >&#8469;</a
      ><a name="1735" class="Symbol"
      >)</a
      ><a name="1736"
      >
</a
      ><a name="1737" class="Keyword"
      >open</a
      ><a name="1741"
      > </a
      ><a name="1742" class="Keyword"
      >import</a
      ><a name="1748"
      > </a
      ><a name="1749" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#1" class="Module"
      >Relation.Nullary</a
      ><a name="1765"
      > </a
      ><a name="1766" class="Keyword"
      >using</a
      ><a name="1771"
      > </a
      ><a name="1772" class="Symbol"
      >(</a
      ><a name="1773" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#484" class="Datatype"
      >Dec</a
      ><a name="1776" class="Symbol"
      >;</a
      ><a name="1777"
      > </a
      ><a name="1778" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#520" class="InductiveConstructor"
      >yes</a
      ><a name="1781" class="Symbol"
      >;</a
      ><a name="1782"
      > </a
      ><a name="1783" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#547" class="InductiveConstructor"
      >no</a
      ><a name="1785" class="Symbol"
      >)</a
      ><a name="1786"
      >
</a
      ><a name="1787" class="Keyword"
      >open</a
      ><a name="1791"
      > </a
      ><a name="1792" class="Keyword"
      >import</a
      ><a name="1798"
      > </a
      ><a name="1799" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#1" class="Module"
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
<a name="2285" class="Keyword"
      >data</a
      ><a name="2289"
      > </a
      ><a name="2290" href="Maps.html#2290" class="Datatype"
      >Id</a
      ><a name="2292"
      > </a
      ><a name="2293" class="Symbol"
      >:</a
      ><a name="2294"
      > </a
      ><a name="2295" class="PrimitiveType"
      >Set</a
      ><a name="2298"
      > </a
      ><a name="2299" class="Keyword"
      >where</a
      ><a name="2304"
      >
  </a
      ><a name="2307" href="Maps.html#2307" class="InductiveConstructor"
      >id</a
      ><a name="2309"
      > </a
      ><a name="2310" class="Symbol"
      >:</a
      ><a name="2311"
      > </a
      ><a name="2312" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#97" class="Datatype"
      >&#8469;</a
      ><a name="2313"
      > </a
      ><a name="2314" class="Symbol"
      >&#8594;</a
      ><a name="2315"
      > </a
      ><a name="2316" href="Maps.html#2290" class="Datatype"
      >Id</a
      >
{% endraw %}</pre>

<pre class="Agda">{% raw %}
<a name="2344" href="Maps.html#2344" class="Function Operator"
      >_&#8799;_</a
      ><a name="2347"
      > </a
      ><a name="2348" class="Symbol"
      >:</a
      ><a name="2349"
      > </a
      ><a name="2350" class="Symbol"
      >(</a
      ><a name="2351" href="Maps.html#2351" class="Bound"
      >x</a
      ><a name="2352"
      > </a
      ><a name="2353" href="Maps.html#2353" class="Bound"
      >y</a
      ><a name="2354"
      > </a
      ><a name="2355" class="Symbol"
      >:</a
      ><a name="2356"
      > </a
      ><a name="2357" href="Maps.html#2290" class="Datatype"
      >Id</a
      ><a name="2359" class="Symbol"
      >)</a
      ><a name="2360"
      > </a
      ><a name="2361" class="Symbol"
      >&#8594;</a
      ><a name="2362"
      > </a
      ><a name="2363" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#484" class="Datatype"
      >Dec</a
      ><a name="2366"
      > </a
      ><a name="2367" class="Symbol"
      >(</a
      ><a name="2368" href="Maps.html#2351" class="Bound"
      >x</a
      ><a name="2369"
      > </a
      ><a name="2370" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="2371"
      > </a
      ><a name="2372" href="Maps.html#2353" class="Bound"
      >y</a
      ><a name="2373" class="Symbol"
      >)</a
      ><a name="2374"
      >
</a
      ><a name="2375" href="Maps.html#2307" class="InductiveConstructor"
      >id</a
      ><a name="2377"
      > </a
      ><a name="2378" href="Maps.html#2378" class="Bound"
      >x</a
      ><a name="2379"
      > </a
      ><a name="2380" href="Maps.html#2344" class="Function Operator"
      >&#8799;</a
      ><a name="2381"
      > </a
      ><a name="2382" href="Maps.html#2307" class="InductiveConstructor"
      >id</a
      ><a name="2384"
      > </a
      ><a name="2385" href="Maps.html#2385" class="Bound"
      >y</a
      ><a name="2386"
      > </a
      ><a name="2387" class="Keyword"
      >with</a
      ><a name="2391"
      > </a
      ><a name="2392" href="Maps.html#2378" class="Bound"
      >x</a
      ><a name="2393"
      > </a
      ><a name="2394" href="https://agda.github.io/agda-stdlib/Data.Nat.Base.html#3212" class="Function Operator"
      >Data.Nat.&#8799;</a
      ><a name="2404"
      > </a
      ><a name="2405" href="Maps.html#2385" class="Bound"
      >y</a
      ><a name="2406"
      >
</a
      ><a name="2407" href="Maps.html#2307" class="InductiveConstructor"
      >id</a
      ><a name="2409"
      > </a
      ><a name="2410" href="Maps.html#2410" class="Bound"
      >x</a
      ><a name="2411"
      > </a
      ><a name="2412" href="Maps.html#2344" class="Function Operator"
      >&#8799;</a
      ><a name="2413"
      > </a
      ><a name="2414" href="Maps.html#2307" class="InductiveConstructor"
      >id</a
      ><a name="2416"
      > </a
      ><a name="2417" href="Maps.html#2417" class="Bound"
      >y</a
      ><a name="2418"
      > </a
      ><a name="2419" class="Symbol"
      >|</a
      ><a name="2420"
      > </a
      ><a name="2421" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#520" class="InductiveConstructor"
      >yes</a
      ><a name="2424"
      > </a
      ><a name="2425" href="Maps.html#2425" class="Bound"
      >x=y</a
      ><a name="2428"
      > </a
      ><a name="2429" class="Keyword"
      >rewrite</a
      ><a name="2436"
      > </a
      ><a name="2437" href="Maps.html#2425" class="Bound"
      >x=y</a
      ><a name="2440"
      > </a
      ><a name="2441" class="Symbol"
      >=</a
      ><a name="2442"
      > </a
      ><a name="2443" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#520" class="InductiveConstructor"
      >yes</a
      ><a name="2446"
      > </a
      ><a name="2447" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="2451"
      >
</a
      ><a name="2452" href="Maps.html#2307" class="InductiveConstructor"
      >id</a
      ><a name="2454"
      > </a
      ><a name="2455" href="Maps.html#2455" class="Bound"
      >x</a
      ><a name="2456"
      > </a
      ><a name="2457" href="Maps.html#2344" class="Function Operator"
      >&#8799;</a
      ><a name="2458"
      > </a
      ><a name="2459" href="Maps.html#2307" class="InductiveConstructor"
      >id</a
      ><a name="2461"
      > </a
      ><a name="2462" href="Maps.html#2462" class="Bound"
      >y</a
      ><a name="2463"
      > </a
      ><a name="2464" class="Symbol"
      >|</a
      ><a name="2465"
      > </a
      ><a name="2466" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#547" class="InductiveConstructor"
      >no</a
      ><a name="2468"
      >  </a
      ><a name="2470" href="Maps.html#2470" class="Bound"
      >x&#8800;y</a
      ><a name="2473"
      > </a
      ><a name="2474" class="Symbol"
      >=</a
      ><a name="2475"
      > </a
      ><a name="2476" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#547" class="InductiveConstructor"
      >no</a
      ><a name="2478"
      > </a
      ><a name="2479" class="Symbol"
      >(</a
      ><a name="2480" href="Maps.html#2470" class="Bound"
      >x&#8800;y</a
      ><a name="2483"
      > </a
      ><a name="2484" href="https://agda.github.io/agda-stdlib/Function.html#713" class="Function Operator"
      >&#8728;</a
      ><a name="2485"
      > </a
      ><a name="2486" href="Maps.html#2506" class="Function"
      >id-inj</a
      ><a name="2492" class="Symbol"
      >)</a
      ><a name="2493"
      >
  </a
      ><a name="2496" class="Keyword"
      >where</a
      ><a name="2501"
      >
    </a
      ><a name="2506" href="Maps.html#2506" class="Function"
      >id-inj</a
      ><a name="2512"
      > </a
      ><a name="2513" class="Symbol"
      >:</a
      ><a name="2514"
      > </a
      ><a name="2515" class="Symbol"
      >&#8704;</a
      ><a name="2516"
      > </a
      ><a name="2517" class="Symbol"
      >{</a
      ><a name="2518" href="Maps.html#2518" class="Bound"
      >x</a
      ><a name="2519"
      > </a
      ><a name="2520" href="Maps.html#2520" class="Bound"
      >y</a
      ><a name="2521" class="Symbol"
      >}</a
      ><a name="2522"
      > </a
      ><a name="2523" class="Symbol"
      >&#8594;</a
      ><a name="2524"
      > </a
      ><a name="2525" href="Maps.html#2307" class="InductiveConstructor"
      >id</a
      ><a name="2527"
      > </a
      ><a name="2528" href="Maps.html#2518" class="Bound"
      >x</a
      ><a name="2529"
      > </a
      ><a name="2530" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="2531"
      > </a
      ><a name="2532" href="Maps.html#2307" class="InductiveConstructor"
      >id</a
      ><a name="2534"
      > </a
      ><a name="2535" href="Maps.html#2520" class="Bound"
      >y</a
      ><a name="2536"
      > </a
      ><a name="2537" class="Symbol"
      >&#8594;</a
      ><a name="2538"
      > </a
      ><a name="2539" href="Maps.html#2518" class="Bound"
      >x</a
      ><a name="2540"
      > </a
      ><a name="2541" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="2542"
      > </a
      ><a name="2543" href="Maps.html#2520" class="Bound"
      >y</a
      ><a name="2544"
      >
    </a
      ><a name="2549" href="Maps.html#2506" class="Function"
      >id-inj</a
      ><a name="2555"
      > </a
      ><a name="2556" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="2560"
      > </a
      ><a name="2561" class="Symbol"
      >=</a
      ><a name="2562"
      > </a
      ><a name="2563" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
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
<a name="3399" href="Maps.html#3399" class="Function"
      >TotalMap</a
      ><a name="3407"
      > </a
      ><a name="3408" class="Symbol"
      >:</a
      ><a name="3409"
      > </a
      ><a name="3410" class="PrimitiveType"
      >Set</a
      ><a name="3413"
      > </a
      ><a name="3414" class="Symbol"
      >&#8594;</a
      ><a name="3415"
      > </a
      ><a name="3416" class="PrimitiveType"
      >Set</a
      ><a name="3419"
      >
</a
      ><a name="3420" href="Maps.html#3399" class="Function"
      >TotalMap</a
      ><a name="3428"
      > </a
      ><a name="3429" href="Maps.html#3429" class="Bound"
      >A</a
      ><a name="3430"
      > </a
      ><a name="3431" class="Symbol"
      >=</a
      ><a name="3432"
      > </a
      ><a name="3433" href="Maps.html#2290" class="Datatype"
      >Id</a
      ><a name="3435"
      > </a
      ><a name="3436" class="Symbol"
      >&#8594;</a
      ><a name="3437"
      > </a
      ><a name="3438" href="Maps.html#3429" class="Bound"
      >A</a
      >
{% endraw %}</pre>

Intuitively, a total map over anﬁ element type $$A$$ _is_ just a
function that can be used to look up ids, yielding $$A$$s.

<pre class="Agda">{% raw %}
<a name="3590" class="Keyword"
      >module</a
      ><a name="3596"
      > </a
      ><a name="3597" href="Maps.html#3597" class="Module"
      >TotalMap</a
      ><a name="3605"
      > </a
      ><a name="3606" class="Keyword"
      >where</a
      >
{% endraw %}</pre>

The function `empty` yields an empty total map, given a
default element; this map always returns the default element when
applied to any id.

<pre class="Agda">{% raw %}
  <a name="3781" href="Maps.html#3781" class="Function"
      >empty</a
      ><a name="3786"
      > </a
      ><a name="3787" class="Symbol"
      >:</a
      ><a name="3788"
      > </a
      ><a name="3789" class="Symbol"
      >&#8704;</a
      ><a name="3790"
      > </a
      ><a name="3791" class="Symbol"
      >{</a
      ><a name="3792" href="Maps.html#3792" class="Bound"
      >A</a
      ><a name="3793" class="Symbol"
      >}</a
      ><a name="3794"
      > </a
      ><a name="3795" class="Symbol"
      >&#8594;</a
      ><a name="3796"
      > </a
      ><a name="3797" href="Maps.html#3792" class="Bound"
      >A</a
      ><a name="3798"
      > </a
      ><a name="3799" class="Symbol"
      >&#8594;</a
      ><a name="3800"
      > </a
      ><a name="3801" href="Maps.html#3399" class="Function"
      >TotalMap</a
      ><a name="3809"
      > </a
      ><a name="3810" href="Maps.html#3792" class="Bound"
      >A</a
      ><a name="3811"
      >
  </a
      ><a name="3814" href="Maps.html#3781" class="Function"
      >empty</a
      ><a name="3819"
      > </a
      ><a name="3820" href="Maps.html#3820" class="Bound"
      >x</a
      ><a name="3821"
      > </a
      ><a name="3822" class="Symbol"
      >=</a
      ><a name="3823"
      > </a
      ><a name="3824" class="Symbol"
      >&#955;</a
      ><a name="3825"
      > </a
      ><a name="3826" href="Maps.html#3826" class="Bound"
      >_</a
      ><a name="3827"
      > </a
      ><a name="3828" class="Symbol"
      >&#8594;</a
      ><a name="3829"
      > </a
      ><a name="3830" href="Maps.html#3820" class="Bound"
      >x</a
      >
{% endraw %}</pre>

More interesting is the `update` function, which (as before) takes
a map $$m$$, a key $$x$$, and a value $$v$$ and returns a new map that
takes $$x$$ to $$v$$ and takes every other key to whatever $$m$$ does.

<pre class="Agda">{% raw %}
  <a name="4069" href="Maps.html#4069" class="Function"
      >update</a
      ><a name="4075"
      > </a
      ><a name="4076" class="Symbol"
      >:</a
      ><a name="4077"
      > </a
      ><a name="4078" class="Symbol"
      >&#8704;</a
      ><a name="4079"
      > </a
      ><a name="4080" class="Symbol"
      >{</a
      ><a name="4081" href="Maps.html#4081" class="Bound"
      >A</a
      ><a name="4082" class="Symbol"
      >}</a
      ><a name="4083"
      > </a
      ><a name="4084" class="Symbol"
      >&#8594;</a
      ><a name="4085"
      > </a
      ><a name="4086" href="Maps.html#3399" class="Function"
      >TotalMap</a
      ><a name="4094"
      > </a
      ><a name="4095" href="Maps.html#4081" class="Bound"
      >A</a
      ><a name="4096"
      > </a
      ><a name="4097" class="Symbol"
      >-&gt;</a
      ><a name="4099"
      > </a
      ><a name="4100" href="Maps.html#2290" class="Datatype"
      >Id</a
      ><a name="4102"
      > </a
      ><a name="4103" class="Symbol"
      >-&gt;</a
      ><a name="4105"
      > </a
      ><a name="4106" href="Maps.html#4081" class="Bound"
      >A</a
      ><a name="4107"
      > </a
      ><a name="4108" class="Symbol"
      >-&gt;</a
      ><a name="4110"
      > </a
      ><a name="4111" href="Maps.html#3399" class="Function"
      >TotalMap</a
      ><a name="4119"
      > </a
      ><a name="4120" href="Maps.html#4081" class="Bound"
      >A</a
      ><a name="4121"
      >
  </a
      ><a name="4124" href="Maps.html#4069" class="Function"
      >update</a
      ><a name="4130"
      > </a
      ><a name="4131" href="Maps.html#4131" class="Bound"
      >m</a
      ><a name="4132"
      > </a
      ><a name="4133" href="Maps.html#4133" class="Bound"
      >x</a
      ><a name="4134"
      > </a
      ><a name="4135" href="Maps.html#4135" class="Bound"
      >v</a
      ><a name="4136"
      > </a
      ><a name="4137" href="Maps.html#4137" class="Bound"
      >y</a
      ><a name="4138"
      > </a
      ><a name="4139" class="Keyword"
      >with</a
      ><a name="4143"
      > </a
      ><a name="4144" href="Maps.html#4133" class="Bound"
      >x</a
      ><a name="4145"
      > </a
      ><a name="4146" href="Maps.html#2344" class="Function Operator"
      >&#8799;</a
      ><a name="4147"
      > </a
      ><a name="4148" href="Maps.html#4137" class="Bound"
      >y</a
      ><a name="4149"
      >
  </a
      ><a name="4152" class="Symbol"
      >...</a
      ><a name="4155"
      > </a
      ><a name="4156" class="Symbol"
      >|</a
      ><a name="4157"
      > </a
      ><a name="4158" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#520" class="InductiveConstructor"
      >yes</a
      ><a name="4161"
      > </a
      ><a name="4162" href="Maps.html#4162" class="Bound"
      >x=y</a
      ><a name="4165"
      > </a
      ><a name="4166" class="Symbol"
      >=</a
      ><a name="4167"
      > </a
      ><a name="4168" href="Maps.html#4135" class="Bound"
      >v</a
      ><a name="4169"
      >
  </a
      ><a name="4172" class="Symbol"
      >...</a
      ><a name="4175"
      > </a
      ><a name="4176" class="Symbol"
      >|</a
      ><a name="4177"
      > </a
      ><a name="4178" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#547" class="InductiveConstructor"
      >no</a
      ><a name="4180"
      >  </a
      ><a name="4182" href="Maps.html#4182" class="Bound"
      >x&#8800;y</a
      ><a name="4185"
      > </a
      ><a name="4186" class="Symbol"
      >=</a
      ><a name="4187"
      > </a
      ><a name="4188" href="Maps.html#4131" class="Bound"
      >m</a
      ><a name="4189"
      > </a
      ><a name="4190" href="Maps.html#4137" class="Bound"
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
  <a name="4553" href="Maps.html#4553" class="Function"
      >examplemap</a
      ><a name="4563"
      > </a
      ><a name="4564" class="Symbol"
      >:</a
      ><a name="4565"
      > </a
      ><a name="4566" href="Maps.html#3399" class="Function"
      >TotalMap</a
      ><a name="4574"
      > </a
      ><a name="4575" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Bool.html#67" class="Datatype"
      >Bool</a
      ><a name="4579"
      >
  </a
      ><a name="4582" href="Maps.html#4553" class="Function"
      >examplemap</a
      ><a name="4592"
      > </a
      ><a name="4593" class="Symbol"
      >=</a
      ><a name="4594"
      > </a
      ><a name="4595" href="Maps.html#4069" class="Function"
      >update</a
      ><a name="4601"
      > </a
      ><a name="4602" class="Symbol"
      >(</a
      ><a name="4603" href="Maps.html#4069" class="Function"
      >update</a
      ><a name="4609"
      > </a
      ><a name="4610" class="Symbol"
      >(</a
      ><a name="4611" href="Maps.html#3781" class="Function"
      >empty</a
      ><a name="4616"
      > </a
      ><a name="4617" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Bool.html#86" class="InductiveConstructor"
      >false</a
      ><a name="4622" class="Symbol"
      >)</a
      ><a name="4623"
      > </a
      ><a name="4624" class="Symbol"
      >(</a
      ><a name="4625" href="Maps.html#2307" class="InductiveConstructor"
      >id</a
      ><a name="4627"
      > </a
      ><a name="4628" class="Number"
      >1</a
      ><a name="4629" class="Symbol"
      >)</a
      ><a name="4630"
      > </a
      ><a name="4631" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Bool.html#86" class="InductiveConstructor"
      >false</a
      ><a name="4636" class="Symbol"
      >)</a
      ><a name="4637"
      > </a
      ><a name="4638" class="Symbol"
      >(</a
      ><a name="4639" href="Maps.html#2307" class="InductiveConstructor"
      >id</a
      ><a name="4641"
      > </a
      ><a name="4642" class="Number"
      >3</a
      ><a name="4643" class="Symbol"
      >)</a
      ><a name="4644"
      > </a
      ><a name="4645" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Bool.html#92" class="InductiveConstructor"
      >true</a
      >
{% endraw %}</pre>

This completes the definition of total maps.  Note that we don't
need to define a `find` operation because it is just function
application!

<pre class="Agda">{% raw %}
  <a name="4818" href="Maps.html#4818" class="Function Operator"
      >test_examplemap0</a
      ><a name="4834"
      > </a
      ><a name="4835" class="Symbol"
      >:</a
      ><a name="4836"
      > </a
      ><a name="4837" href="Maps.html#4553" class="Function"
      >examplemap</a
      ><a name="4847"
      > </a
      ><a name="4848" class="Symbol"
      >(</a
      ><a name="4849" href="Maps.html#2307" class="InductiveConstructor"
      >id</a
      ><a name="4851"
      > </a
      ><a name="4852" class="Number"
      >0</a
      ><a name="4853" class="Symbol"
      >)</a
      ><a name="4854"
      > </a
      ><a name="4855" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="4856"
      > </a
      ><a name="4857" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Bool.html#86" class="InductiveConstructor"
      >false</a
      ><a name="4862"
      >
  </a
      ><a name="4865" href="Maps.html#4818" class="Function Operator"
      >test_examplemap0</a
      ><a name="4881"
      > </a
      ><a name="4882" class="Symbol"
      >=</a
      ><a name="4883"
      > </a
      ><a name="4884" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="4888"
      >

  </a
      ><a name="4892" href="Maps.html#4892" class="Function Operator"
      >test_examplemap1</a
      ><a name="4908"
      > </a
      ><a name="4909" class="Symbol"
      >:</a
      ><a name="4910"
      > </a
      ><a name="4911" href="Maps.html#4553" class="Function"
      >examplemap</a
      ><a name="4921"
      > </a
      ><a name="4922" class="Symbol"
      >(</a
      ><a name="4923" href="Maps.html#2307" class="InductiveConstructor"
      >id</a
      ><a name="4925"
      > </a
      ><a name="4926" class="Number"
      >1</a
      ><a name="4927" class="Symbol"
      >)</a
      ><a name="4928"
      > </a
      ><a name="4929" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="4930"
      > </a
      ><a name="4931" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Bool.html#86" class="InductiveConstructor"
      >false</a
      ><a name="4936"
      >
  </a
      ><a name="4939" href="Maps.html#4892" class="Function Operator"
      >test_examplemap1</a
      ><a name="4955"
      > </a
      ><a name="4956" class="Symbol"
      >=</a
      ><a name="4957"
      > </a
      ><a name="4958" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="4962"
      >

  </a
      ><a name="4966" href="Maps.html#4966" class="Function Operator"
      >test_examplemap2</a
      ><a name="4982"
      > </a
      ><a name="4983" class="Symbol"
      >:</a
      ><a name="4984"
      > </a
      ><a name="4985" href="Maps.html#4553" class="Function"
      >examplemap</a
      ><a name="4995"
      > </a
      ><a name="4996" class="Symbol"
      >(</a
      ><a name="4997" href="Maps.html#2307" class="InductiveConstructor"
      >id</a
      ><a name="4999"
      > </a
      ><a name="5000" class="Number"
      >2</a
      ><a name="5001" class="Symbol"
      >)</a
      ><a name="5002"
      > </a
      ><a name="5003" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="5004"
      > </a
      ><a name="5005" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Bool.html#86" class="InductiveConstructor"
      >false</a
      ><a name="5010"
      >
  </a
      ><a name="5013" href="Maps.html#4966" class="Function Operator"
      >test_examplemap2</a
      ><a name="5029"
      > </a
      ><a name="5030" class="Symbol"
      >=</a
      ><a name="5031"
      > </a
      ><a name="5032" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="5036"
      >

  </a
      ><a name="5040" href="Maps.html#5040" class="Function Operator"
      >test_examplemap3</a
      ><a name="5056"
      > </a
      ><a name="5057" class="Symbol"
      >:</a
      ><a name="5058"
      > </a
      ><a name="5059" href="Maps.html#4553" class="Function"
      >examplemap</a
      ><a name="5069"
      > </a
      ><a name="5070" class="Symbol"
      >(</a
      ><a name="5071" href="Maps.html#2307" class="InductiveConstructor"
      >id</a
      ><a name="5073"
      > </a
      ><a name="5074" class="Number"
      >3</a
      ><a name="5075" class="Symbol"
      >)</a
      ><a name="5076"
      > </a
      ><a name="5077" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="5078"
      > </a
      ><a name="5079" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Bool.html#92" class="InductiveConstructor"
      >true</a
      ><a name="5083"
      >
  </a
      ><a name="5086" href="Maps.html#5040" class="Function Operator"
      >test_examplemap3</a
      ><a name="5102"
      > </a
      ><a name="5103" class="Symbol"
      >=</a
      ><a name="5104"
      > </a
      ><a name="5105" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
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
  <a name="5606" class="Keyword"
      >postulate</a
      ><a name="5615"
      >
    </a
      ><a name="5620" href="Maps.html#5620" class="Postulate"
      >apply-empty</a
      ><a name="5631"
      > </a
      ><a name="5632" class="Symbol"
      >:</a
      ><a name="5633"
      > </a
      ><a name="5634" class="Symbol"
      >&#8704;</a
      ><a name="5635"
      > </a
      ><a name="5636" class="Symbol"
      >{</a
      ><a name="5637" href="Maps.html#5637" class="Bound"
      >A</a
      ><a name="5638"
      > </a
      ><a name="5639" href="Maps.html#5639" class="Bound"
      >x</a
      ><a name="5640"
      > </a
      ><a name="5641" href="Maps.html#5641" class="Bound"
      >v</a
      ><a name="5642" class="Symbol"
      >}</a
      ><a name="5643"
      > </a
      ><a name="5644" class="Symbol"
      >&#8594;</a
      ><a name="5645"
      > </a
      ><a name="5646" href="Maps.html#3781" class="Function"
      >empty</a
      ><a name="5651"
      > </a
      ><a name="5652" class="Symbol"
      >{</a
      ><a name="5653" href="Maps.html#5637" class="Bound"
      >A</a
      ><a name="5654" class="Symbol"
      >}</a
      ><a name="5655"
      > </a
      ><a name="5656" href="Maps.html#5641" class="Bound"
      >v</a
      ><a name="5657"
      > </a
      ><a name="5658" href="Maps.html#5639" class="Bound"
      >x</a
      ><a name="5659"
      > </a
      ><a name="5660" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="5661"
      > </a
      ><a name="5662" href="Maps.html#5641" class="Bound"
      >v</a
      >
{% endraw %}</pre>

<div class="hidden">
<pre class="Agda">{% raw %}
  <a name="5712" href="Maps.html#5712" class="Function"
      >apply-empty&#8242;</a
      ><a name="5724"
      > </a
      ><a name="5725" class="Symbol"
      >:</a
      ><a name="5726"
      > </a
      ><a name="5727" class="Symbol"
      >&#8704;</a
      ><a name="5728"
      > </a
      ><a name="5729" class="Symbol"
      >{</a
      ><a name="5730" href="Maps.html#5730" class="Bound"
      >A</a
      ><a name="5731"
      > </a
      ><a name="5732" href="Maps.html#5732" class="Bound"
      >x</a
      ><a name="5733"
      > </a
      ><a name="5734" href="Maps.html#5734" class="Bound"
      >v</a
      ><a name="5735" class="Symbol"
      >}</a
      ><a name="5736"
      > </a
      ><a name="5737" class="Symbol"
      >&#8594;</a
      ><a name="5738"
      > </a
      ><a name="5739" href="Maps.html#3781" class="Function"
      >empty</a
      ><a name="5744"
      > </a
      ><a name="5745" class="Symbol"
      >{</a
      ><a name="5746" href="Maps.html#5730" class="Bound"
      >A</a
      ><a name="5747" class="Symbol"
      >}</a
      ><a name="5748"
      > </a
      ><a name="5749" href="Maps.html#5734" class="Bound"
      >v</a
      ><a name="5750"
      > </a
      ><a name="5751" href="Maps.html#5732" class="Bound"
      >x</a
      ><a name="5752"
      > </a
      ><a name="5753" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="5754"
      > </a
      ><a name="5755" href="Maps.html#5734" class="Bound"
      >v</a
      ><a name="5756"
      >
  </a
      ><a name="5759" href="Maps.html#5712" class="Function"
      >apply-empty&#8242;</a
      ><a name="5771"
      > </a
      ><a name="5772" class="Symbol"
      >=</a
      ><a name="5773"
      > </a
      ><a name="5774" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      >
{% endraw %}</pre>
</div>

#### Exercise: 2 stars, optional (update-eq)
Next, if we update a map $$m$$ at a key $$x$$ with a new value $$v$$
and then look up $$x$$ in the map resulting from the `update`, we get
back $$v$$:

<pre class="Agda">{% raw %}
  <a name="6010" class="Keyword"
      >postulate</a
      ><a name="6019"
      >
    </a
      ><a name="6024" href="Maps.html#6024" class="Postulate"
      >update-eq</a
      ><a name="6033"
      > </a
      ><a name="6034" class="Symbol"
      >:</a
      ><a name="6035"
      > </a
      ><a name="6036" class="Symbol"
      >&#8704;</a
      ><a name="6037"
      > </a
      ><a name="6038" class="Symbol"
      >{</a
      ><a name="6039" href="Maps.html#6039" class="Bound"
      >A</a
      ><a name="6040"
      > </a
      ><a name="6041" href="Maps.html#6041" class="Bound"
      >v</a
      ><a name="6042" class="Symbol"
      >}</a
      ><a name="6043"
      > </a
      ><a name="6044" class="Symbol"
      >(</a
      ><a name="6045" href="Maps.html#6045" class="Bound"
      >m</a
      ><a name="6046"
      > </a
      ><a name="6047" class="Symbol"
      >:</a
      ><a name="6048"
      > </a
      ><a name="6049" href="Maps.html#3399" class="Function"
      >TotalMap</a
      ><a name="6057"
      > </a
      ><a name="6058" href="Maps.html#6039" class="Bound"
      >A</a
      ><a name="6059" class="Symbol"
      >)</a
      ><a name="6060"
      > </a
      ><a name="6061" class="Symbol"
      >(</a
      ><a name="6062" href="Maps.html#6062" class="Bound"
      >x</a
      ><a name="6063"
      > </a
      ><a name="6064" class="Symbol"
      >:</a
      ><a name="6065"
      > </a
      ><a name="6066" href="Maps.html#2290" class="Datatype"
      >Id</a
      ><a name="6068" class="Symbol"
      >)</a
      ><a name="6069"
      >
              </a
      ><a name="6084" class="Symbol"
      >&#8594;</a
      ><a name="6085"
      > </a
      ><a name="6086" class="Symbol"
      >(</a
      ><a name="6087" href="Maps.html#4069" class="Function"
      >update</a
      ><a name="6093"
      > </a
      ><a name="6094" href="Maps.html#6045" class="Bound"
      >m</a
      ><a name="6095"
      > </a
      ><a name="6096" href="Maps.html#6062" class="Bound"
      >x</a
      ><a name="6097"
      > </a
      ><a name="6098" href="Maps.html#6041" class="Bound"
      >v</a
      ><a name="6099" class="Symbol"
      >)</a
      ><a name="6100"
      > </a
      ><a name="6101" href="Maps.html#6062" class="Bound"
      >x</a
      ><a name="6102"
      > </a
      ><a name="6103" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="6104"
      > </a
      ><a name="6105" href="Maps.html#6041" class="Bound"
      >v</a
      >
{% endraw %}</pre>

<div class="hidden">
<pre class="Agda">{% raw %}
  <a name="6155" href="Maps.html#6155" class="Function"
      >update-eq&#8242;</a
      ><a name="6165"
      > </a
      ><a name="6166" class="Symbol"
      >:</a
      ><a name="6167"
      > </a
      ><a name="6168" class="Symbol"
      >&#8704;</a
      ><a name="6169"
      > </a
      ><a name="6170" class="Symbol"
      >{</a
      ><a name="6171" href="Maps.html#6171" class="Bound"
      >A</a
      ><a name="6172"
      > </a
      ><a name="6173" href="Maps.html#6173" class="Bound"
      >v</a
      ><a name="6174" class="Symbol"
      >}</a
      ><a name="6175"
      > </a
      ><a name="6176" class="Symbol"
      >(</a
      ><a name="6177" href="Maps.html#6177" class="Bound"
      >m</a
      ><a name="6178"
      > </a
      ><a name="6179" class="Symbol"
      >:</a
      ><a name="6180"
      > </a
      ><a name="6181" href="Maps.html#3399" class="Function"
      >TotalMap</a
      ><a name="6189"
      > </a
      ><a name="6190" href="Maps.html#6171" class="Bound"
      >A</a
      ><a name="6191" class="Symbol"
      >)</a
      ><a name="6192"
      > </a
      ><a name="6193" class="Symbol"
      >(</a
      ><a name="6194" href="Maps.html#6194" class="Bound"
      >x</a
      ><a name="6195"
      > </a
      ><a name="6196" class="Symbol"
      >:</a
      ><a name="6197"
      > </a
      ><a name="6198" href="Maps.html#2290" class="Datatype"
      >Id</a
      ><a name="6200" class="Symbol"
      >)</a
      ><a name="6201"
      >
             </a
      ><a name="6215" class="Symbol"
      >&#8594;</a
      ><a name="6216"
      > </a
      ><a name="6217" class="Symbol"
      >(</a
      ><a name="6218" href="Maps.html#4069" class="Function"
      >update</a
      ><a name="6224"
      > </a
      ><a name="6225" href="Maps.html#6177" class="Bound"
      >m</a
      ><a name="6226"
      > </a
      ><a name="6227" href="Maps.html#6194" class="Bound"
      >x</a
      ><a name="6228"
      > </a
      ><a name="6229" href="Maps.html#6173" class="Bound"
      >v</a
      ><a name="6230" class="Symbol"
      >)</a
      ><a name="6231"
      > </a
      ><a name="6232" href="Maps.html#6194" class="Bound"
      >x</a
      ><a name="6233"
      > </a
      ><a name="6234" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="6235"
      > </a
      ><a name="6236" href="Maps.html#6173" class="Bound"
      >v</a
      ><a name="6237"
      >
  </a
      ><a name="6240" href="Maps.html#6155" class="Function"
      >update-eq&#8242;</a
      ><a name="6250"
      > </a
      ><a name="6251" href="Maps.html#6251" class="Bound"
      >m</a
      ><a name="6252"
      > </a
      ><a name="6253" href="Maps.html#6253" class="Bound"
      >x</a
      ><a name="6254"
      > </a
      ><a name="6255" class="Keyword"
      >with</a
      ><a name="6259"
      > </a
      ><a name="6260" href="Maps.html#6253" class="Bound"
      >x</a
      ><a name="6261"
      > </a
      ><a name="6262" href="Maps.html#2344" class="Function Operator"
      >&#8799;</a
      ><a name="6263"
      > </a
      ><a name="6264" href="Maps.html#6253" class="Bound"
      >x</a
      ><a name="6265"
      >
  </a
      ><a name="6268" class="Symbol"
      >...</a
      ><a name="6271"
      > </a
      ><a name="6272" class="Symbol"
      >|</a
      ><a name="6273"
      > </a
      ><a name="6274" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#520" class="InductiveConstructor"
      >yes</a
      ><a name="6277"
      > </a
      ><a name="6278" href="Maps.html#6278" class="Bound"
      >x=x</a
      ><a name="6281"
      > </a
      ><a name="6282" class="Symbol"
      >=</a
      ><a name="6283"
      > </a
      ><a name="6284" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="6288"
      >
  </a
      ><a name="6291" class="Symbol"
      >...</a
      ><a name="6294"
      > </a
      ><a name="6295" class="Symbol"
      >|</a
      ><a name="6296"
      > </a
      ><a name="6297" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#547" class="InductiveConstructor"
      >no</a
      ><a name="6299"
      >  </a
      ><a name="6301" href="Maps.html#6301" class="Bound"
      >x&#8800;x</a
      ><a name="6304"
      > </a
      ><a name="6305" class="Symbol"
      >=</a
      ><a name="6306"
      > </a
      ><a name="6307" href="https://agda.github.io/agda-stdlib/Data.Empty.html#360" class="Function"
      >&#8869;-elim</a
      ><a name="6313"
      > </a
      ><a name="6314" class="Symbol"
      >(</a
      ><a name="6315" href="Maps.html#6301" class="Bound"
      >x&#8800;x</a
      ><a name="6318"
      > </a
      ><a name="6319" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="6323" class="Symbol"
      >)</a
      >
{% endraw %}</pre>
</div>

#### Exercise: 2 stars, optional (update-neq)
On the other hand, if we update a map $$m$$ at a key $$x$$ and
then look up a _different_ key $$y$$ in the resulting map, we get
the same result that $$m$$ would have given:

<pre class="Agda">{% raw %}
  <a name="6580" href="Maps.html#6580" class="Function"
      >update-neq</a
      ><a name="6590"
      > </a
      ><a name="6591" class="Symbol"
      >:</a
      ><a name="6592"
      > </a
      ><a name="6593" class="Symbol"
      >&#8704;</a
      ><a name="6594"
      > </a
      ><a name="6595" class="Symbol"
      >{</a
      ><a name="6596" href="Maps.html#6596" class="Bound"
      >A</a
      ><a name="6597"
      > </a
      ><a name="6598" href="Maps.html#6598" class="Bound"
      >v</a
      ><a name="6599" class="Symbol"
      >}</a
      ><a name="6600"
      > </a
      ><a name="6601" class="Symbol"
      >(</a
      ><a name="6602" href="Maps.html#6602" class="Bound"
      >m</a
      ><a name="6603"
      > </a
      ><a name="6604" class="Symbol"
      >:</a
      ><a name="6605"
      > </a
      ><a name="6606" href="Maps.html#3399" class="Function"
      >TotalMap</a
      ><a name="6614"
      > </a
      ><a name="6615" href="Maps.html#6596" class="Bound"
      >A</a
      ><a name="6616" class="Symbol"
      >)</a
      ><a name="6617"
      > </a
      ><a name="6618" class="Symbol"
      >(</a
      ><a name="6619" href="Maps.html#6619" class="Bound"
      >x</a
      ><a name="6620"
      > </a
      ><a name="6621" href="Maps.html#6621" class="Bound"
      >y</a
      ><a name="6622"
      > </a
      ><a name="6623" class="Symbol"
      >:</a
      ><a name="6624"
      > </a
      ><a name="6625" href="Maps.html#2290" class="Datatype"
      >Id</a
      ><a name="6627" class="Symbol"
      >)</a
      ><a name="6628"
      >
             </a
      ><a name="6642" class="Symbol"
      >&#8594;</a
      ><a name="6643"
      > </a
      ><a name="6644" href="Maps.html#6619" class="Bound"
      >x</a
      ><a name="6645"
      > </a
      ><a name="6646" href="https://agda.github.io/agda-stdlib/Relation.Binary.Core.html#4493" class="Function Operator"
      >&#8802;</a
      ><a name="6647"
      > </a
      ><a name="6648" href="Maps.html#6621" class="Bound"
      >y</a
      ><a name="6649"
      > </a
      ><a name="6650" class="Symbol"
      >&#8594;</a
      ><a name="6651"
      > </a
      ><a name="6652" class="Symbol"
      >(</a
      ><a name="6653" href="Maps.html#4069" class="Function"
      >update</a
      ><a name="6659"
      > </a
      ><a name="6660" href="Maps.html#6602" class="Bound"
      >m</a
      ><a name="6661"
      > </a
      ><a name="6662" href="Maps.html#6619" class="Bound"
      >x</a
      ><a name="6663"
      > </a
      ><a name="6664" href="Maps.html#6598" class="Bound"
      >v</a
      ><a name="6665" class="Symbol"
      >)</a
      ><a name="6666"
      > </a
      ><a name="6667" href="Maps.html#6621" class="Bound"
      >y</a
      ><a name="6668"
      > </a
      ><a name="6669" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="6670"
      > </a
      ><a name="6671" href="Maps.html#6602" class="Bound"
      >m</a
      ><a name="6672"
      > </a
      ><a name="6673" href="Maps.html#6621" class="Bound"
      >y</a
      ><a name="6674"
      >
  </a
      ><a name="6677" href="Maps.html#6580" class="Function"
      >update-neq</a
      ><a name="6687"
      > </a
      ><a name="6688" href="Maps.html#6688" class="Bound"
      >m</a
      ><a name="6689"
      > </a
      ><a name="6690" href="Maps.html#6690" class="Bound"
      >x</a
      ><a name="6691"
      > </a
      ><a name="6692" href="Maps.html#6692" class="Bound"
      >y</a
      ><a name="6693"
      > </a
      ><a name="6694" href="Maps.html#6694" class="Bound"
      >x&#8800;y</a
      ><a name="6697"
      > </a
      ><a name="6698" class="Keyword"
      >with</a
      ><a name="6702"
      > </a
      ><a name="6703" href="Maps.html#6690" class="Bound"
      >x</a
      ><a name="6704"
      > </a
      ><a name="6705" href="Maps.html#2344" class="Function Operator"
      >&#8799;</a
      ><a name="6706"
      > </a
      ><a name="6707" href="Maps.html#6692" class="Bound"
      >y</a
      ><a name="6708"
      >
  </a
      ><a name="6711" class="Symbol"
      >...</a
      ><a name="6714"
      > </a
      ><a name="6715" class="Symbol"
      >|</a
      ><a name="6716"
      > </a
      ><a name="6717" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#520" class="InductiveConstructor"
      >yes</a
      ><a name="6720"
      > </a
      ><a name="6721" href="Maps.html#6721" class="Bound"
      >x=y</a
      ><a name="6724"
      > </a
      ><a name="6725" class="Symbol"
      >=</a
      ><a name="6726"
      > </a
      ><a name="6727" href="https://agda.github.io/agda-stdlib/Data.Empty.html#360" class="Function"
      >&#8869;-elim</a
      ><a name="6733"
      > </a
      ><a name="6734" class="Symbol"
      >(</a
      ><a name="6735" href="Maps.html#6694" class="Bound"
      >x&#8800;y</a
      ><a name="6738"
      > </a
      ><a name="6739" href="Maps.html#6721" class="Bound"
      >x=y</a
      ><a name="6742" class="Symbol"
      >)</a
      ><a name="6743"
      >
  </a
      ><a name="6746" class="Symbol"
      >...</a
      ><a name="6749"
      > </a
      ><a name="6750" class="Symbol"
      >|</a
      ><a name="6751"
      > </a
      ><a name="6752" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#547" class="InductiveConstructor"
      >no</a
      ><a name="6754"
      >  </a
      ><a name="6756" class="Symbol"
      >_</a
      ><a name="6757"
      >   </a
      ><a name="6760" class="Symbol"
      >=</a
      ><a name="6761"
      > </a
      ><a name="6762" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
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
  <a name="7138" class="Keyword"
      >postulate</a
      ><a name="7147"
      >
    </a
      ><a name="7152" href="Maps.html#7152" class="Postulate"
      >update-shadow</a
      ><a name="7165"
      > </a
      ><a name="7166" class="Symbol"
      >:</a
      ><a name="7167"
      > </a
      ><a name="7168" class="Symbol"
      >&#8704;</a
      ><a name="7169"
      > </a
      ><a name="7170" class="Symbol"
      >{</a
      ><a name="7171" href="Maps.html#7171" class="Bound"
      >A</a
      ><a name="7172"
      > </a
      ><a name="7173" href="Maps.html#7173" class="Bound"
      >v1</a
      ><a name="7175"
      > </a
      ><a name="7176" href="Maps.html#7176" class="Bound"
      >v2</a
      ><a name="7178" class="Symbol"
      >}</a
      ><a name="7179"
      > </a
      ><a name="7180" class="Symbol"
      >(</a
      ><a name="7181" href="Maps.html#7181" class="Bound"
      >m</a
      ><a name="7182"
      > </a
      ><a name="7183" class="Symbol"
      >:</a
      ><a name="7184"
      > </a
      ><a name="7185" href="Maps.html#3399" class="Function"
      >TotalMap</a
      ><a name="7193"
      > </a
      ><a name="7194" href="Maps.html#7171" class="Bound"
      >A</a
      ><a name="7195" class="Symbol"
      >)</a
      ><a name="7196"
      > </a
      ><a name="7197" class="Symbol"
      >(</a
      ><a name="7198" href="Maps.html#7198" class="Bound"
      >x</a
      ><a name="7199"
      > </a
      ><a name="7200" href="Maps.html#7200" class="Bound"
      >y</a
      ><a name="7201"
      > </a
      ><a name="7202" class="Symbol"
      >:</a
      ><a name="7203"
      > </a
      ><a name="7204" href="Maps.html#2290" class="Datatype"
      >Id</a
      ><a name="7206" class="Symbol"
      >)</a
      ><a name="7207"
      >
                  </a
      ><a name="7226" class="Symbol"
      >&#8594;</a
      ><a name="7227"
      > </a
      ><a name="7228" class="Symbol"
      >(</a
      ><a name="7229" href="Maps.html#4069" class="Function"
      >update</a
      ><a name="7235"
      > </a
      ><a name="7236" class="Symbol"
      >(</a
      ><a name="7237" href="Maps.html#4069" class="Function"
      >update</a
      ><a name="7243"
      > </a
      ><a name="7244" href="Maps.html#7181" class="Bound"
      >m</a
      ><a name="7245"
      > </a
      ><a name="7246" href="Maps.html#7198" class="Bound"
      >x</a
      ><a name="7247"
      > </a
      ><a name="7248" href="Maps.html#7173" class="Bound"
      >v1</a
      ><a name="7250" class="Symbol"
      >)</a
      ><a name="7251"
      > </a
      ><a name="7252" href="Maps.html#7198" class="Bound"
      >x</a
      ><a name="7253"
      > </a
      ><a name="7254" href="Maps.html#7176" class="Bound"
      >v2</a
      ><a name="7256" class="Symbol"
      >)</a
      ><a name="7257"
      > </a
      ><a name="7258" href="Maps.html#7200" class="Bound"
      >y</a
      ><a name="7259"
      > </a
      ><a name="7260" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="7261"
      > </a
      ><a name="7262" class="Symbol"
      >(</a
      ><a name="7263" href="Maps.html#4069" class="Function"
      >update</a
      ><a name="7269"
      > </a
      ><a name="7270" href="Maps.html#7181" class="Bound"
      >m</a
      ><a name="7271"
      > </a
      ><a name="7272" href="Maps.html#7198" class="Bound"
      >x</a
      ><a name="7273"
      > </a
      ><a name="7274" href="Maps.html#7176" class="Bound"
      >v2</a
      ><a name="7276" class="Symbol"
      >)</a
      ><a name="7277"
      > </a
      ><a name="7278" href="Maps.html#7200" class="Bound"
      >y</a
      >
{% endraw %}</pre>

<div class="hidden">
<pre class="Agda">{% raw %}
  <a name="7328" href="Maps.html#7328" class="Function"
      >update-shadow&#8242;</a
      ><a name="7342"
      > </a
      ><a name="7343" class="Symbol"
      >:</a
      ><a name="7344"
      > </a
      ><a name="7345" class="Symbol"
      >&#8704;</a
      ><a name="7346"
      > </a
      ><a name="7347" class="Symbol"
      >{</a
      ><a name="7348" href="Maps.html#7348" class="Bound"
      >A</a
      ><a name="7349"
      > </a
      ><a name="7350" href="Maps.html#7350" class="Bound"
      >v1</a
      ><a name="7352"
      > </a
      ><a name="7353" href="Maps.html#7353" class="Bound"
      >v2</a
      ><a name="7355" class="Symbol"
      >}</a
      ><a name="7356"
      > </a
      ><a name="7357" class="Symbol"
      >(</a
      ><a name="7358" href="Maps.html#7358" class="Bound"
      >m</a
      ><a name="7359"
      > </a
      ><a name="7360" class="Symbol"
      >:</a
      ><a name="7361"
      > </a
      ><a name="7362" href="Maps.html#3399" class="Function"
      >TotalMap</a
      ><a name="7370"
      > </a
      ><a name="7371" href="Maps.html#7348" class="Bound"
      >A</a
      ><a name="7372" class="Symbol"
      >)</a
      ><a name="7373"
      > </a
      ><a name="7374" class="Symbol"
      >(</a
      ><a name="7375" href="Maps.html#7375" class="Bound"
      >x</a
      ><a name="7376"
      > </a
      ><a name="7377" href="Maps.html#7377" class="Bound"
      >y</a
      ><a name="7378"
      > </a
      ><a name="7379" class="Symbol"
      >:</a
      ><a name="7380"
      > </a
      ><a name="7381" href="Maps.html#2290" class="Datatype"
      >Id</a
      ><a name="7383" class="Symbol"
      >)</a
      ><a name="7384"
      >
                 </a
      ><a name="7402" class="Symbol"
      >&#8594;</a
      ><a name="7403"
      > </a
      ><a name="7404" class="Symbol"
      >(</a
      ><a name="7405" href="Maps.html#4069" class="Function"
      >update</a
      ><a name="7411"
      > </a
      ><a name="7412" class="Symbol"
      >(</a
      ><a name="7413" href="Maps.html#4069" class="Function"
      >update</a
      ><a name="7419"
      > </a
      ><a name="7420" href="Maps.html#7358" class="Bound"
      >m</a
      ><a name="7421"
      > </a
      ><a name="7422" href="Maps.html#7375" class="Bound"
      >x</a
      ><a name="7423"
      > </a
      ><a name="7424" href="Maps.html#7350" class="Bound"
      >v1</a
      ><a name="7426" class="Symbol"
      >)</a
      ><a name="7427"
      > </a
      ><a name="7428" href="Maps.html#7375" class="Bound"
      >x</a
      ><a name="7429"
      > </a
      ><a name="7430" href="Maps.html#7353" class="Bound"
      >v2</a
      ><a name="7432" class="Symbol"
      >)</a
      ><a name="7433"
      > </a
      ><a name="7434" href="Maps.html#7377" class="Bound"
      >y</a
      ><a name="7435"
      > </a
      ><a name="7436" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="7437"
      > </a
      ><a name="7438" class="Symbol"
      >(</a
      ><a name="7439" href="Maps.html#4069" class="Function"
      >update</a
      ><a name="7445"
      > </a
      ><a name="7446" href="Maps.html#7358" class="Bound"
      >m</a
      ><a name="7447"
      > </a
      ><a name="7448" href="Maps.html#7375" class="Bound"
      >x</a
      ><a name="7449"
      > </a
      ><a name="7450" href="Maps.html#7353" class="Bound"
      >v2</a
      ><a name="7452" class="Symbol"
      >)</a
      ><a name="7453"
      > </a
      ><a name="7454" href="Maps.html#7377" class="Bound"
      >y</a
      ><a name="7455"
      >
  </a
      ><a name="7458" href="Maps.html#7328" class="Function"
      >update-shadow&#8242;</a
      ><a name="7472"
      > </a
      ><a name="7473" href="Maps.html#7473" class="Bound"
      >m</a
      ><a name="7474"
      > </a
      ><a name="7475" href="Maps.html#7475" class="Bound"
      >x</a
      ><a name="7476"
      > </a
      ><a name="7477" href="Maps.html#7477" class="Bound"
      >y</a
      ><a name="7478"
      >
      </a
      ><a name="7485" class="Keyword"
      >with</a
      ><a name="7489"
      > </a
      ><a name="7490" href="Maps.html#7475" class="Bound"
      >x</a
      ><a name="7491"
      > </a
      ><a name="7492" href="Maps.html#2344" class="Function Operator"
      >&#8799;</a
      ><a name="7493"
      > </a
      ><a name="7494" href="Maps.html#7477" class="Bound"
      >y</a
      ><a name="7495"
      >
  </a
      ><a name="7498" class="Symbol"
      >...</a
      ><a name="7501"
      > </a
      ><a name="7502" class="Symbol"
      >|</a
      ><a name="7503"
      > </a
      ><a name="7504" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#520" class="InductiveConstructor"
      >yes</a
      ><a name="7507"
      > </a
      ><a name="7508" href="Maps.html#7508" class="Bound"
      >x=y</a
      ><a name="7511"
      > </a
      ><a name="7512" class="Symbol"
      >=</a
      ><a name="7513"
      > </a
      ><a name="7514" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="7518"
      >
  </a
      ><a name="7521" class="Symbol"
      >...</a
      ><a name="7524"
      > </a
      ><a name="7525" class="Symbol"
      >|</a
      ><a name="7526"
      > </a
      ><a name="7527" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#547" class="InductiveConstructor"
      >no</a
      ><a name="7529"
      >  </a
      ><a name="7531" href="Maps.html#7531" class="Bound"
      >x&#8800;y</a
      ><a name="7534"
      > </a
      ><a name="7535" class="Symbol"
      >=</a
      ><a name="7536"
      > </a
      ><a name="7537" href="Maps.html#6580" class="Function"
      >update-neq</a
      ><a name="7547"
      > </a
      ><a name="7548" href="Maps.html#7473" class="Bound"
      >m</a
      ><a name="7549"
      > </a
      ><a name="7550" href="Maps.html#7475" class="Bound"
      >x</a
      ><a name="7551"
      > </a
      ><a name="7552" href="Maps.html#7477" class="Bound"
      >y</a
      ><a name="7553"
      > </a
      ><a name="7554" href="Maps.html#7531" class="Bound"
      >x&#8800;y</a
      >
{% endraw %}</pre>
</div>

#### Exercise: 2 stars (update-same)
Prove the following theorem, which states that if we update a map to
assign key $$x$$ the same value as it already has in $$m$$, then the
result is equal to $$m$$:

<pre class="Agda">{% raw %}
  <a name="7794" class="Keyword"
      >postulate</a
      ><a name="7803"
      >
    </a
      ><a name="7808" href="Maps.html#7808" class="Postulate"
      >update-same</a
      ><a name="7819"
      > </a
      ><a name="7820" class="Symbol"
      >:</a
      ><a name="7821"
      > </a
      ><a name="7822" class="Symbol"
      >&#8704;</a
      ><a name="7823"
      > </a
      ><a name="7824" class="Symbol"
      >{</a
      ><a name="7825" href="Maps.html#7825" class="Bound"
      >A</a
      ><a name="7826" class="Symbol"
      >}</a
      ><a name="7827"
      > </a
      ><a name="7828" class="Symbol"
      >(</a
      ><a name="7829" href="Maps.html#7829" class="Bound"
      >m</a
      ><a name="7830"
      > </a
      ><a name="7831" class="Symbol"
      >:</a
      ><a name="7832"
      > </a
      ><a name="7833" href="Maps.html#3399" class="Function"
      >TotalMap</a
      ><a name="7841"
      > </a
      ><a name="7842" href="Maps.html#7825" class="Bound"
      >A</a
      ><a name="7843" class="Symbol"
      >)</a
      ><a name="7844"
      > </a
      ><a name="7845" class="Symbol"
      >(</a
      ><a name="7846" href="Maps.html#7846" class="Bound"
      >x</a
      ><a name="7847"
      > </a
      ><a name="7848" href="Maps.html#7848" class="Bound"
      >y</a
      ><a name="7849"
      > </a
      ><a name="7850" class="Symbol"
      >:</a
      ><a name="7851"
      > </a
      ><a name="7852" href="Maps.html#2290" class="Datatype"
      >Id</a
      ><a name="7854" class="Symbol"
      >)</a
      ><a name="7855"
      >
                </a
      ><a name="7872" class="Symbol"
      >&#8594;</a
      ><a name="7873"
      > </a
      ><a name="7874" class="Symbol"
      >(</a
      ><a name="7875" href="Maps.html#4069" class="Function"
      >update</a
      ><a name="7881"
      > </a
      ><a name="7882" href="Maps.html#7829" class="Bound"
      >m</a
      ><a name="7883"
      > </a
      ><a name="7884" href="Maps.html#7846" class="Bound"
      >x</a
      ><a name="7885"
      > </a
      ><a name="7886" class="Symbol"
      >(</a
      ><a name="7887" href="Maps.html#7829" class="Bound"
      >m</a
      ><a name="7888"
      > </a
      ><a name="7889" href="Maps.html#7846" class="Bound"
      >x</a
      ><a name="7890" class="Symbol"
      >))</a
      ><a name="7892"
      > </a
      ><a name="7893" href="Maps.html#7848" class="Bound"
      >y</a
      ><a name="7894"
      > </a
      ><a name="7895" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="7896"
      > </a
      ><a name="7897" href="Maps.html#7829" class="Bound"
      >m</a
      ><a name="7898"
      > </a
      ><a name="7899" href="Maps.html#7848" class="Bound"
      >y</a
      >
{% endraw %}</pre>

<div class="hidden">
<pre class="Agda">{% raw %}
  <a name="7949" href="Maps.html#7949" class="Function"
      >update-same&#8242;</a
      ><a name="7961"
      > </a
      ><a name="7962" class="Symbol"
      >:</a
      ><a name="7963"
      > </a
      ><a name="7964" class="Symbol"
      >&#8704;</a
      ><a name="7965"
      > </a
      ><a name="7966" class="Symbol"
      >{</a
      ><a name="7967" href="Maps.html#7967" class="Bound"
      >A</a
      ><a name="7968" class="Symbol"
      >}</a
      ><a name="7969"
      > </a
      ><a name="7970" class="Symbol"
      >(</a
      ><a name="7971" href="Maps.html#7971" class="Bound"
      >m</a
      ><a name="7972"
      > </a
      ><a name="7973" class="Symbol"
      >:</a
      ><a name="7974"
      > </a
      ><a name="7975" href="Maps.html#3399" class="Function"
      >TotalMap</a
      ><a name="7983"
      > </a
      ><a name="7984" href="Maps.html#7967" class="Bound"
      >A</a
      ><a name="7985" class="Symbol"
      >)</a
      ><a name="7986"
      > </a
      ><a name="7987" class="Symbol"
      >(</a
      ><a name="7988" href="Maps.html#7988" class="Bound"
      >x</a
      ><a name="7989"
      > </a
      ><a name="7990" href="Maps.html#7990" class="Bound"
      >y</a
      ><a name="7991"
      > </a
      ><a name="7992" class="Symbol"
      >:</a
      ><a name="7993"
      > </a
      ><a name="7994" href="Maps.html#2290" class="Datatype"
      >Id</a
      ><a name="7996" class="Symbol"
      >)</a
      ><a name="7997"
      >
               </a
      ><a name="8013" class="Symbol"
      >&#8594;</a
      ><a name="8014"
      > </a
      ><a name="8015" class="Symbol"
      >(</a
      ><a name="8016" href="Maps.html#4069" class="Function"
      >update</a
      ><a name="8022"
      > </a
      ><a name="8023" href="Maps.html#7971" class="Bound"
      >m</a
      ><a name="8024"
      > </a
      ><a name="8025" href="Maps.html#7988" class="Bound"
      >x</a
      ><a name="8026"
      > </a
      ><a name="8027" class="Symbol"
      >(</a
      ><a name="8028" href="Maps.html#7971" class="Bound"
      >m</a
      ><a name="8029"
      > </a
      ><a name="8030" href="Maps.html#7988" class="Bound"
      >x</a
      ><a name="8031" class="Symbol"
      >))</a
      ><a name="8033"
      > </a
      ><a name="8034" href="Maps.html#7990" class="Bound"
      >y</a
      ><a name="8035"
      > </a
      ><a name="8036" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="8037"
      > </a
      ><a name="8038" href="Maps.html#7971" class="Bound"
      >m</a
      ><a name="8039"
      > </a
      ><a name="8040" href="Maps.html#7990" class="Bound"
      >y</a
      ><a name="8041"
      >
  </a
      ><a name="8044" href="Maps.html#7949" class="Function"
      >update-same&#8242;</a
      ><a name="8056"
      > </a
      ><a name="8057" href="Maps.html#8057" class="Bound"
      >m</a
      ><a name="8058"
      > </a
      ><a name="8059" href="Maps.html#8059" class="Bound"
      >x</a
      ><a name="8060"
      > </a
      ><a name="8061" href="Maps.html#8061" class="Bound"
      >y</a
      ><a name="8062"
      >
    </a
      ><a name="8067" class="Keyword"
      >with</a
      ><a name="8071"
      > </a
      ><a name="8072" href="Maps.html#8059" class="Bound"
      >x</a
      ><a name="8073"
      > </a
      ><a name="8074" href="Maps.html#2344" class="Function Operator"
      >&#8799;</a
      ><a name="8075"
      > </a
      ><a name="8076" href="Maps.html#8061" class="Bound"
      >y</a
      ><a name="8077"
      >
  </a
      ><a name="8080" class="Symbol"
      >...</a
      ><a name="8083"
      > </a
      ><a name="8084" class="Symbol"
      >|</a
      ><a name="8085"
      > </a
      ><a name="8086" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#520" class="InductiveConstructor"
      >yes</a
      ><a name="8089"
      > </a
      ><a name="8090" href="Maps.html#8090" class="Bound"
      >x=y</a
      ><a name="8093"
      > </a
      ><a name="8094" class="Keyword"
      >rewrite</a
      ><a name="8101"
      > </a
      ><a name="8102" href="Maps.html#8090" class="Bound"
      >x=y</a
      ><a name="8105"
      > </a
      ><a name="8106" class="Symbol"
      >=</a
      ><a name="8107"
      > </a
      ><a name="8108" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="8112"
      >
  </a
      ><a name="8115" class="Symbol"
      >...</a
      ><a name="8118"
      > </a
      ><a name="8119" class="Symbol"
      >|</a
      ><a name="8120"
      > </a
      ><a name="8121" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#547" class="InductiveConstructor"
      >no</a
      ><a name="8123"
      >  </a
      ><a name="8125" href="Maps.html#8125" class="Bound"
      >x&#8800;y</a
      ><a name="8128"
      > </a
      ><a name="8129" class="Symbol"
      >=</a
      ><a name="8130"
      > </a
      ><a name="8131" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      >
{% endraw %}</pre>
</div>

#### Exercise: 3 stars, recommended (update-permute)
Prove one final property of the `update` function: If we update a map
$$m$$ at two distinct keys, it doesn't matter in which order we do the
updates.

<pre class="Agda">{% raw %}
  <a name="8374" class="Keyword"
      >postulate</a
      ><a name="8383"
      >
    </a
      ><a name="8388" href="Maps.html#8388" class="Postulate"
      >update-permute</a
      ><a name="8402"
      > </a
      ><a name="8403" class="Symbol"
      >:</a
      ><a name="8404"
      > </a
      ><a name="8405" class="Symbol"
      >&#8704;</a
      ><a name="8406"
      > </a
      ><a name="8407" class="Symbol"
      >{</a
      ><a name="8408" href="Maps.html#8408" class="Bound"
      >A</a
      ><a name="8409"
      > </a
      ><a name="8410" href="Maps.html#8410" class="Bound"
      >v1</a
      ><a name="8412"
      > </a
      ><a name="8413" href="Maps.html#8413" class="Bound"
      >v2</a
      ><a name="8415" class="Symbol"
      >}</a
      ><a name="8416"
      > </a
      ><a name="8417" class="Symbol"
      >(</a
      ><a name="8418" href="Maps.html#8418" class="Bound"
      >m</a
      ><a name="8419"
      > </a
      ><a name="8420" class="Symbol"
      >:</a
      ><a name="8421"
      > </a
      ><a name="8422" href="Maps.html#3399" class="Function"
      >TotalMap</a
      ><a name="8430"
      > </a
      ><a name="8431" href="Maps.html#8408" class="Bound"
      >A</a
      ><a name="8432" class="Symbol"
      >)</a
      ><a name="8433"
      > </a
      ><a name="8434" class="Symbol"
      >(</a
      ><a name="8435" href="Maps.html#8435" class="Bound"
      >x1</a
      ><a name="8437"
      > </a
      ><a name="8438" href="Maps.html#8438" class="Bound"
      >x2</a
      ><a name="8440"
      > </a
      ><a name="8441" href="Maps.html#8441" class="Bound"
      >y</a
      ><a name="8442"
      > </a
      ><a name="8443" class="Symbol"
      >:</a
      ><a name="8444"
      > </a
      ><a name="8445" href="Maps.html#2290" class="Datatype"
      >Id</a
      ><a name="8447" class="Symbol"
      >)</a
      ><a name="8448"
      >
                   </a
      ><a name="8468" class="Symbol"
      >&#8594;</a
      ><a name="8469"
      > </a
      ><a name="8470" href="Maps.html#8435" class="Bound"
      >x1</a
      ><a name="8472"
      > </a
      ><a name="8473" href="https://agda.github.io/agda-stdlib/Relation.Binary.Core.html#4493" class="Function Operator"
      >&#8802;</a
      ><a name="8474"
      > </a
      ><a name="8475" href="Maps.html#8438" class="Bound"
      >x2</a
      ><a name="8477"
      > </a
      ><a name="8478" class="Symbol"
      >&#8594;</a
      ><a name="8479"
      > </a
      ><a name="8480" class="Symbol"
      >(</a
      ><a name="8481" href="Maps.html#4069" class="Function"
      >update</a
      ><a name="8487"
      > </a
      ><a name="8488" class="Symbol"
      >(</a
      ><a name="8489" href="Maps.html#4069" class="Function"
      >update</a
      ><a name="8495"
      > </a
      ><a name="8496" href="Maps.html#8418" class="Bound"
      >m</a
      ><a name="8497"
      > </a
      ><a name="8498" href="Maps.html#8438" class="Bound"
      >x2</a
      ><a name="8500"
      > </a
      ><a name="8501" href="Maps.html#8413" class="Bound"
      >v2</a
      ><a name="8503" class="Symbol"
      >)</a
      ><a name="8504"
      > </a
      ><a name="8505" href="Maps.html#8435" class="Bound"
      >x1</a
      ><a name="8507"
      > </a
      ><a name="8508" href="Maps.html#8410" class="Bound"
      >v1</a
      ><a name="8510" class="Symbol"
      >)</a
      ><a name="8511"
      > </a
      ><a name="8512" href="Maps.html#8441" class="Bound"
      >y</a
      ><a name="8513"
      >
                             </a
      ><a name="8543" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="8544"
      > </a
      ><a name="8545" class="Symbol"
      >(</a
      ><a name="8546" href="Maps.html#4069" class="Function"
      >update</a
      ><a name="8552"
      > </a
      ><a name="8553" class="Symbol"
      >(</a
      ><a name="8554" href="Maps.html#4069" class="Function"
      >update</a
      ><a name="8560"
      > </a
      ><a name="8561" href="Maps.html#8418" class="Bound"
      >m</a
      ><a name="8562"
      > </a
      ><a name="8563" href="Maps.html#8435" class="Bound"
      >x1</a
      ><a name="8565"
      > </a
      ><a name="8566" href="Maps.html#8410" class="Bound"
      >v1</a
      ><a name="8568" class="Symbol"
      >)</a
      ><a name="8569"
      > </a
      ><a name="8570" href="Maps.html#8438" class="Bound"
      >x2</a
      ><a name="8572"
      > </a
      ><a name="8573" href="Maps.html#8413" class="Bound"
      >v2</a
      ><a name="8575" class="Symbol"
      >)</a
      ><a name="8576"
      > </a
      ><a name="8577" href="Maps.html#8441" class="Bound"
      >y</a
      >
{% endraw %}</pre>

<div class="hidden">
<pre class="Agda">{% raw %}
  <a name="8627" href="Maps.html#8627" class="Function"
      >update-permute&#8242;</a
      ><a name="8642"
      > </a
      ><a name="8643" class="Symbol"
      >:</a
      ><a name="8644"
      > </a
      ><a name="8645" class="Symbol"
      >&#8704;</a
      ><a name="8646"
      > </a
      ><a name="8647" class="Symbol"
      >{</a
      ><a name="8648" href="Maps.html#8648" class="Bound"
      >A</a
      ><a name="8649"
      > </a
      ><a name="8650" href="Maps.html#8650" class="Bound"
      >v1</a
      ><a name="8652"
      > </a
      ><a name="8653" href="Maps.html#8653" class="Bound"
      >v2</a
      ><a name="8655" class="Symbol"
      >}</a
      ><a name="8656"
      > </a
      ><a name="8657" class="Symbol"
      >(</a
      ><a name="8658" href="Maps.html#8658" class="Bound"
      >m</a
      ><a name="8659"
      > </a
      ><a name="8660" class="Symbol"
      >:</a
      ><a name="8661"
      > </a
      ><a name="8662" href="Maps.html#3399" class="Function"
      >TotalMap</a
      ><a name="8670"
      > </a
      ><a name="8671" href="Maps.html#8648" class="Bound"
      >A</a
      ><a name="8672" class="Symbol"
      >)</a
      ><a name="8673"
      > </a
      ><a name="8674" class="Symbol"
      >(</a
      ><a name="8675" href="Maps.html#8675" class="Bound"
      >x1</a
      ><a name="8677"
      > </a
      ><a name="8678" href="Maps.html#8678" class="Bound"
      >x2</a
      ><a name="8680"
      > </a
      ><a name="8681" href="Maps.html#8681" class="Bound"
      >y</a
      ><a name="8682"
      > </a
      ><a name="8683" class="Symbol"
      >:</a
      ><a name="8684"
      > </a
      ><a name="8685" href="Maps.html#2290" class="Datatype"
      >Id</a
      ><a name="8687" class="Symbol"
      >)</a
      ><a name="8688"
      >
                  </a
      ><a name="8707" class="Symbol"
      >&#8594;</a
      ><a name="8708"
      > </a
      ><a name="8709" href="Maps.html#8675" class="Bound"
      >x1</a
      ><a name="8711"
      > </a
      ><a name="8712" href="https://agda.github.io/agda-stdlib/Relation.Binary.Core.html#4493" class="Function Operator"
      >&#8802;</a
      ><a name="8713"
      > </a
      ><a name="8714" href="Maps.html#8678" class="Bound"
      >x2</a
      ><a name="8716"
      > </a
      ><a name="8717" class="Symbol"
      >&#8594;</a
      ><a name="8718"
      > </a
      ><a name="8719" class="Symbol"
      >(</a
      ><a name="8720" href="Maps.html#4069" class="Function"
      >update</a
      ><a name="8726"
      > </a
      ><a name="8727" class="Symbol"
      >(</a
      ><a name="8728" href="Maps.html#4069" class="Function"
      >update</a
      ><a name="8734"
      > </a
      ><a name="8735" href="Maps.html#8658" class="Bound"
      >m</a
      ><a name="8736"
      > </a
      ><a name="8737" href="Maps.html#8678" class="Bound"
      >x2</a
      ><a name="8739"
      > </a
      ><a name="8740" href="Maps.html#8653" class="Bound"
      >v2</a
      ><a name="8742" class="Symbol"
      >)</a
      ><a name="8743"
      > </a
      ><a name="8744" href="Maps.html#8675" class="Bound"
      >x1</a
      ><a name="8746"
      > </a
      ><a name="8747" href="Maps.html#8650" class="Bound"
      >v1</a
      ><a name="8749" class="Symbol"
      >)</a
      ><a name="8750"
      > </a
      ><a name="8751" href="Maps.html#8681" class="Bound"
      >y</a
      ><a name="8752"
      >
                            </a
      ><a name="8781" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="8782"
      > </a
      ><a name="8783" class="Symbol"
      >(</a
      ><a name="8784" href="Maps.html#4069" class="Function"
      >update</a
      ><a name="8790"
      > </a
      ><a name="8791" class="Symbol"
      >(</a
      ><a name="8792" href="Maps.html#4069" class="Function"
      >update</a
      ><a name="8798"
      > </a
      ><a name="8799" href="Maps.html#8658" class="Bound"
      >m</a
      ><a name="8800"
      > </a
      ><a name="8801" href="Maps.html#8675" class="Bound"
      >x1</a
      ><a name="8803"
      > </a
      ><a name="8804" href="Maps.html#8650" class="Bound"
      >v1</a
      ><a name="8806" class="Symbol"
      >)</a
      ><a name="8807"
      > </a
      ><a name="8808" href="Maps.html#8678" class="Bound"
      >x2</a
      ><a name="8810"
      > </a
      ><a name="8811" href="Maps.html#8653" class="Bound"
      >v2</a
      ><a name="8813" class="Symbol"
      >)</a
      ><a name="8814"
      > </a
      ><a name="8815" href="Maps.html#8681" class="Bound"
      >y</a
      ><a name="8816"
      >
  </a
      ><a name="8819" href="Maps.html#8627" class="Function"
      >update-permute&#8242;</a
      ><a name="8834"
      > </a
      ><a name="8835" class="Symbol"
      >{</a
      ><a name="8836" href="Maps.html#8836" class="Bound"
      >A</a
      ><a name="8837" class="Symbol"
      >}</a
      ><a name="8838"
      > </a
      ><a name="8839" class="Symbol"
      >{</a
      ><a name="8840" href="Maps.html#8840" class="Bound"
      >v1</a
      ><a name="8842" class="Symbol"
      >}</a
      ><a name="8843"
      > </a
      ><a name="8844" class="Symbol"
      >{</a
      ><a name="8845" href="Maps.html#8845" class="Bound"
      >v2</a
      ><a name="8847" class="Symbol"
      >}</a
      ><a name="8848"
      > </a
      ><a name="8849" href="Maps.html#8849" class="Bound"
      >m</a
      ><a name="8850"
      > </a
      ><a name="8851" href="Maps.html#8851" class="Bound"
      >x1</a
      ><a name="8853"
      > </a
      ><a name="8854" href="Maps.html#8854" class="Bound"
      >x2</a
      ><a name="8856"
      > </a
      ><a name="8857" href="Maps.html#8857" class="Bound"
      >y</a
      ><a name="8858"
      > </a
      ><a name="8859" href="Maps.html#8859" class="Bound"
      >x1&#8800;x2</a
      ><a name="8864"
      >
    </a
      ><a name="8869" class="Keyword"
      >with</a
      ><a name="8873"
      > </a
      ><a name="8874" href="Maps.html#8851" class="Bound"
      >x1</a
      ><a name="8876"
      > </a
      ><a name="8877" href="Maps.html#2344" class="Function Operator"
      >&#8799;</a
      ><a name="8878"
      > </a
      ><a name="8879" href="Maps.html#8857" class="Bound"
      >y</a
      ><a name="8880"
      > </a
      ><a name="8881" class="Symbol"
      >|</a
      ><a name="8882"
      > </a
      ><a name="8883" href="Maps.html#8854" class="Bound"
      >x2</a
      ><a name="8885"
      > </a
      ><a name="8886" href="Maps.html#2344" class="Function Operator"
      >&#8799;</a
      ><a name="8887"
      > </a
      ><a name="8888" href="Maps.html#8857" class="Bound"
      >y</a
      ><a name="8889"
      >
  </a
      ><a name="8892" class="Symbol"
      >...</a
      ><a name="8895"
      > </a
      ><a name="8896" class="Symbol"
      >|</a
      ><a name="8897"
      > </a
      ><a name="8898" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#520" class="InductiveConstructor"
      >yes</a
      ><a name="8901"
      > </a
      ><a name="8902" href="Maps.html#8902" class="Bound"
      >x1=y</a
      ><a name="8906"
      > </a
      ><a name="8907" class="Symbol"
      >|</a
      ><a name="8908"
      > </a
      ><a name="8909" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#520" class="InductiveConstructor"
      >yes</a
      ><a name="8912"
      > </a
      ><a name="8913" href="Maps.html#8913" class="Bound"
      >x2=y</a
      ><a name="8917"
      > </a
      ><a name="8918" class="Symbol"
      >=</a
      ><a name="8919"
      > </a
      ><a name="8920" href="https://agda.github.io/agda-stdlib/Data.Empty.html#360" class="Function"
      >&#8869;-elim</a
      ><a name="8926"
      > </a
      ><a name="8927" class="Symbol"
      >(</a
      ><a name="8928" href="Maps.html#8859" class="Bound"
      >x1&#8800;x2</a
      ><a name="8933"
      > </a
      ><a name="8934" class="Symbol"
      >(</a
      ><a name="8935" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.Core.html#632" class="Function"
      >trans</a
      ><a name="8940"
      > </a
      ><a name="8941" href="Maps.html#8902" class="Bound"
      >x1=y</a
      ><a name="8945"
      > </a
      ><a name="8946" class="Symbol"
      >(</a
      ><a name="8947" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.Core.html#565" class="Function"
      >sym</a
      ><a name="8950"
      > </a
      ><a name="8951" href="Maps.html#8913" class="Bound"
      >x2=y</a
      ><a name="8955" class="Symbol"
      >)))</a
      ><a name="8958"
      >
  </a
      ><a name="8961" class="Symbol"
      >...</a
      ><a name="8964"
      > </a
      ><a name="8965" class="Symbol"
      >|</a
      ><a name="8966"
      > </a
      ><a name="8967" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#547" class="InductiveConstructor"
      >no</a
      ><a name="8969"
      >  </a
      ><a name="8971" href="Maps.html#8971" class="Bound"
      >x1&#8800;y</a
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
      >x2=y</a
      ><a name="8986"
      > </a
      ><a name="8987" class="Keyword"
      >rewrite</a
      ><a name="8994"
      > </a
      ><a name="8995" href="Maps.html#8982" class="Bound"
      >x2=y</a
      ><a name="8999"
      > </a
      ><a name="9000" class="Symbol"
      >=</a
      ><a name="9001"
      > </a
      ><a name="9002" href="Maps.html#6155" class="Function"
      >update-eq&#8242;</a
      ><a name="9012"
      > </a
      ><a name="9013" href="Maps.html#8849" class="Bound"
      >m</a
      ><a name="9014"
      > </a
      ><a name="9015" href="Maps.html#8857" class="Bound"
      >y</a
      ><a name="9016"
      >
  </a
      ><a name="9019" class="Symbol"
      >...</a
      ><a name="9022"
      > </a
      ><a name="9023" class="Symbol"
      >|</a
      ><a name="9024"
      > </a
      ><a name="9025" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#520" class="InductiveConstructor"
      >yes</a
      ><a name="9028"
      > </a
      ><a name="9029" href="Maps.html#9029" class="Bound"
      >x1=y</a
      ><a name="9033"
      > </a
      ><a name="9034" class="Symbol"
      >|</a
      ><a name="9035"
      > </a
      ><a name="9036" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#547" class="InductiveConstructor"
      >no</a
      ><a name="9038"
      >  </a
      ><a name="9040" href="Maps.html#9040" class="Bound"
      >x2&#8800;y</a
      ><a name="9044"
      > </a
      ><a name="9045" class="Keyword"
      >rewrite</a
      ><a name="9052"
      > </a
      ><a name="9053" href="Maps.html#9029" class="Bound"
      >x1=y</a
      ><a name="9057"
      > </a
      ><a name="9058" class="Symbol"
      >=</a
      ><a name="9059"
      > </a
      ><a name="9060" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.Core.html#565" class="Function"
      >sym</a
      ><a name="9063"
      > </a
      ><a name="9064" class="Symbol"
      >(</a
      ><a name="9065" href="Maps.html#6155" class="Function"
      >update-eq&#8242;</a
      ><a name="9075"
      > </a
      ><a name="9076" href="Maps.html#8849" class="Bound"
      >m</a
      ><a name="9077"
      > </a
      ><a name="9078" href="Maps.html#8857" class="Bound"
      >y</a
      ><a name="9079" class="Symbol"
      >)</a
      ><a name="9080"
      >
  </a
      ><a name="9083" class="Symbol"
      >...</a
      ><a name="9086"
      > </a
      ><a name="9087" class="Symbol"
      >|</a
      ><a name="9088"
      > </a
      ><a name="9089" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#547" class="InductiveConstructor"
      >no</a
      ><a name="9091"
      >  </a
      ><a name="9093" href="Maps.html#9093" class="Bound"
      >x1&#8800;y</a
      ><a name="9097"
      > </a
      ><a name="9098" class="Symbol"
      >|</a
      ><a name="9099"
      > </a
      ><a name="9100" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#547" class="InductiveConstructor"
      >no</a
      ><a name="9102"
      >  </a
      ><a name="9104" href="Maps.html#9104" class="Bound"
      >x2&#8800;y</a
      ><a name="9108"
      > </a
      ><a name="9109" class="Symbol"
      >=</a
      ><a name="9110"
      >
    </a
      ><a name="9115" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.Core.html#632" class="Function"
      >trans</a
      ><a name="9120"
      > </a
      ><a name="9121" class="Symbol"
      >(</a
      ><a name="9122" href="Maps.html#6580" class="Function"
      >update-neq</a
      ><a name="9132"
      > </a
      ><a name="9133" href="Maps.html#8849" class="Bound"
      >m</a
      ><a name="9134"
      > </a
      ><a name="9135" href="Maps.html#8854" class="Bound"
      >x2</a
      ><a name="9137"
      > </a
      ><a name="9138" href="Maps.html#8857" class="Bound"
      >y</a
      ><a name="9139"
      > </a
      ><a name="9140" href="Maps.html#9104" class="Bound"
      >x2&#8800;y</a
      ><a name="9144" class="Symbol"
      >)</a
      ><a name="9145"
      > </a
      ><a name="9146" class="Symbol"
      >(</a
      ><a name="9147" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.Core.html#565" class="Function"
      >sym</a
      ><a name="9150"
      > </a
      ><a name="9151" class="Symbol"
      >(</a
      ><a name="9152" href="Maps.html#6580" class="Function"
      >update-neq</a
      ><a name="9162"
      > </a
      ><a name="9163" href="Maps.html#8849" class="Bound"
      >m</a
      ><a name="9164"
      > </a
      ><a name="9165" href="Maps.html#8851" class="Bound"
      >x1</a
      ><a name="9167"
      > </a
      ><a name="9168" href="Maps.html#8857" class="Bound"
      >y</a
      ><a name="9169"
      > </a
      ><a name="9170" href="Maps.html#9093" class="Bound"
      >x1&#8800;y</a
      ><a name="9174" class="Symbol"
      >))</a
      >
{% endraw %}</pre>
</div>

## Partial maps

Finally, we define _partial maps_ on top of total maps.  A partial
map with elements of type `A` is simply a total map with elements
of type `Maybe A` and default element `nothing`.

<pre class="Agda">{% raw %}
<a name="9409" href="Maps.html#9409" class="Function"
      >PartialMap</a
      ><a name="9419"
      > </a
      ><a name="9420" class="Symbol"
      >:</a
      ><a name="9421"
      > </a
      ><a name="9422" class="PrimitiveType"
      >Set</a
      ><a name="9425"
      > </a
      ><a name="9426" class="Symbol"
      >&#8594;</a
      ><a name="9427"
      > </a
      ><a name="9428" class="PrimitiveType"
      >Set</a
      ><a name="9431"
      >
</a
      ><a name="9432" href="Maps.html#9409" class="Function"
      >PartialMap</a
      ><a name="9442"
      > </a
      ><a name="9443" href="Maps.html#9443" class="Bound"
      >A</a
      ><a name="9444"
      > </a
      ><a name="9445" class="Symbol"
      >=</a
      ><a name="9446"
      > </a
      ><a name="9447" href="Maps.html#3399" class="Function"
      >TotalMap</a
      ><a name="9455"
      > </a
      ><a name="9456" class="Symbol"
      >(</a
      ><a name="9457" href="https://agda.github.io/agda-stdlib/Data.Maybe.Base.html#335" class="Datatype"
      >Maybe</a
      ><a name="9462"
      > </a
      ><a name="9463" href="Maps.html#9443" class="Bound"
      >A</a
      ><a name="9464" class="Symbol"
      >)</a
      >
{% endraw %}</pre>

<pre class="Agda">{% raw %}
<a name="9491" class="Keyword"
      >module</a
      ><a name="9497"
      > </a
      ><a name="9498" href="Maps.html#9498" class="Module"
      >PartialMap</a
      ><a name="9508"
      > </a
      ><a name="9509" class="Keyword"
      >where</a
      >
{% endraw %}</pre>

<pre class="Agda">{% raw %}
  <a name="9542" href="Maps.html#9542" class="Function"
      >empty</a
      ><a name="9547"
      > </a
      ><a name="9548" class="Symbol"
      >:</a
      ><a name="9549"
      > </a
      ><a name="9550" class="Symbol"
      >&#8704;</a
      ><a name="9551"
      > </a
      ><a name="9552" class="Symbol"
      >{</a
      ><a name="9553" href="Maps.html#9553" class="Bound"
      >A</a
      ><a name="9554" class="Symbol"
      >}</a
      ><a name="9555"
      > </a
      ><a name="9556" class="Symbol"
      >&#8594;</a
      ><a name="9557"
      > </a
      ><a name="9558" href="Maps.html#9409" class="Function"
      >PartialMap</a
      ><a name="9568"
      > </a
      ><a name="9569" href="Maps.html#9553" class="Bound"
      >A</a
      ><a name="9570"
      >
  </a
      ><a name="9573" href="Maps.html#9542" class="Function"
      >empty</a
      ><a name="9578"
      > </a
      ><a name="9579" class="Symbol"
      >=</a
      ><a name="9580"
      > </a
      ><a name="9581" href="Maps.html#3781" class="Function"
      >TotalMap.empty</a
      ><a name="9595"
      > </a
      ><a name="9596" href="https://agda.github.io/agda-stdlib/Data.Maybe.Base.html#403" class="InductiveConstructor"
      >nothing</a
      >
{% endraw %}</pre>

<pre class="Agda">{% raw %}
  <a name="9631" href="Maps.html#9631" class="Function"
      >update</a
      ><a name="9637"
      > </a
      ><a name="9638" class="Symbol"
      >:</a
      ><a name="9639"
      > </a
      ><a name="9640" class="Symbol"
      >&#8704;</a
      ><a name="9641"
      > </a
      ><a name="9642" class="Symbol"
      >{</a
      ><a name="9643" href="Maps.html#9643" class="Bound"
      >A</a
      ><a name="9644" class="Symbol"
      >}</a
      ><a name="9645"
      > </a
      ><a name="9646" class="Symbol"
      >(</a
      ><a name="9647" href="Maps.html#9647" class="Bound"
      >m</a
      ><a name="9648"
      > </a
      ><a name="9649" class="Symbol"
      >:</a
      ><a name="9650"
      > </a
      ><a name="9651" href="Maps.html#9409" class="Function"
      >PartialMap</a
      ><a name="9661"
      > </a
      ><a name="9662" href="Maps.html#9643" class="Bound"
      >A</a
      ><a name="9663" class="Symbol"
      >)</a
      ><a name="9664"
      > </a
      ><a name="9665" class="Symbol"
      >(</a
      ><a name="9666" href="Maps.html#9666" class="Bound"
      >x</a
      ><a name="9667"
      > </a
      ><a name="9668" class="Symbol"
      >:</a
      ><a name="9669"
      > </a
      ><a name="9670" href="Maps.html#2290" class="Datatype"
      >Id</a
      ><a name="9672" class="Symbol"
      >)</a
      ><a name="9673"
      > </a
      ><a name="9674" class="Symbol"
      >(</a
      ><a name="9675" href="Maps.html#9675" class="Bound"
      >v</a
      ><a name="9676"
      > </a
      ><a name="9677" class="Symbol"
      >:</a
      ><a name="9678"
      > </a
      ><a name="9679" href="Maps.html#9643" class="Bound"
      >A</a
      ><a name="9680" class="Symbol"
      >)</a
      ><a name="9681"
      > </a
      ><a name="9682" class="Symbol"
      >&#8594;</a
      ><a name="9683"
      > </a
      ><a name="9684" href="Maps.html#9409" class="Function"
      >PartialMap</a
      ><a name="9694"
      > </a
      ><a name="9695" href="Maps.html#9643" class="Bound"
      >A</a
      ><a name="9696"
      >
  </a
      ><a name="9699" href="Maps.html#9631" class="Function"
      >update</a
      ><a name="9705"
      > </a
      ><a name="9706" href="Maps.html#9706" class="Bound"
      >m</a
      ><a name="9707"
      > </a
      ><a name="9708" href="Maps.html#9708" class="Bound"
      >x</a
      ><a name="9709"
      > </a
      ><a name="9710" href="Maps.html#9710" class="Bound"
      >v</a
      ><a name="9711"
      > </a
      ><a name="9712" class="Symbol"
      >=</a
      ><a name="9713"
      > </a
      ><a name="9714" href="Maps.html#4069" class="Function"
      >TotalMap.update</a
      ><a name="9729"
      > </a
      ><a name="9730" href="Maps.html#9706" class="Bound"
      >m</a
      ><a name="9731"
      > </a
      ><a name="9732" href="Maps.html#9708" class="Bound"
      >x</a
      ><a name="9733"
      > </a
      ><a name="9734" class="Symbol"
      >(</a
      ><a name="9735" href="https://agda.github.io/agda-stdlib/Data.Maybe.Base.html#373" class="InductiveConstructor"
      >just</a
      ><a name="9739"
      > </a
      ><a name="9740" href="Maps.html#9710" class="Bound"
      >v</a
      ><a name="9741" class="Symbol"
      >)</a
      >
{% endraw %}</pre>

We can now lift all of the basic lemmas about total maps to
partial maps.

<pre class="Agda">{% raw %}
  <a name="9845" href="Maps.html#9845" class="Function"
      >update-eq</a
      ><a name="9854"
      > </a
      ><a name="9855" class="Symbol"
      >:</a
      ><a name="9856"
      > </a
      ><a name="9857" class="Symbol"
      >&#8704;</a
      ><a name="9858"
      > </a
      ><a name="9859" class="Symbol"
      >{</a
      ><a name="9860" href="Maps.html#9860" class="Bound"
      >A</a
      ><a name="9861"
      > </a
      ><a name="9862" href="Maps.html#9862" class="Bound"
      >v</a
      ><a name="9863" class="Symbol"
      >}</a
      ><a name="9864"
      > </a
      ><a name="9865" class="Symbol"
      >(</a
      ><a name="9866" href="Maps.html#9866" class="Bound"
      >m</a
      ><a name="9867"
      > </a
      ><a name="9868" class="Symbol"
      >:</a
      ><a name="9869"
      > </a
      ><a name="9870" href="Maps.html#9409" class="Function"
      >PartialMap</a
      ><a name="9880"
      > </a
      ><a name="9881" href="Maps.html#9860" class="Bound"
      >A</a
      ><a name="9882" class="Symbol"
      >)</a
      ><a name="9883"
      > </a
      ><a name="9884" class="Symbol"
      >(</a
      ><a name="9885" href="Maps.html#9885" class="Bound"
      >x</a
      ><a name="9886"
      > </a
      ><a name="9887" class="Symbol"
      >:</a
      ><a name="9888"
      > </a
      ><a name="9889" href="Maps.html#2290" class="Datatype"
      >Id</a
      ><a name="9891" class="Symbol"
      >)</a
      ><a name="9892"
      >
            </a
      ><a name="9905" class="Symbol"
      >&#8594;</a
      ><a name="9906"
      > </a
      ><a name="9907" class="Symbol"
      >(</a
      ><a name="9908" href="Maps.html#9631" class="Function"
      >update</a
      ><a name="9914"
      > </a
      ><a name="9915" href="Maps.html#9866" class="Bound"
      >m</a
      ><a name="9916"
      > </a
      ><a name="9917" href="Maps.html#9885" class="Bound"
      >x</a
      ><a name="9918"
      > </a
      ><a name="9919" href="Maps.html#9862" class="Bound"
      >v</a
      ><a name="9920" class="Symbol"
      >)</a
      ><a name="9921"
      > </a
      ><a name="9922" href="Maps.html#9885" class="Bound"
      >x</a
      ><a name="9923"
      > </a
      ><a name="9924" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="9925"
      > </a
      ><a name="9926" href="https://agda.github.io/agda-stdlib/Data.Maybe.Base.html#373" class="InductiveConstructor"
      >just</a
      ><a name="9930"
      > </a
      ><a name="9931" href="Maps.html#9862" class="Bound"
      >v</a
      ><a name="9932"
      >
  </a
      ><a name="9935" href="Maps.html#9845" class="Function"
      >update-eq</a
      ><a name="9944"
      > </a
      ><a name="9945" href="Maps.html#9945" class="Bound"
      >m</a
      ><a name="9946"
      > </a
      ><a name="9947" href="Maps.html#9947" class="Bound"
      >x</a
      ><a name="9948"
      > </a
      ><a name="9949" class="Symbol"
      >=</a
      ><a name="9950"
      > </a
      ><a name="9951" href="Maps.html#6024" class="Postulate"
      >TotalMap.update-eq</a
      ><a name="9969"
      > </a
      ><a name="9970" href="Maps.html#9945" class="Bound"
      >m</a
      ><a name="9971"
      > </a
      ><a name="9972" href="Maps.html#9947" class="Bound"
      >x</a
      >
{% endraw %}</pre>

<pre class="Agda">{% raw %}
  <a name="10001" href="Maps.html#10001" class="Function"
      >update-neq</a
      ><a name="10011"
      > </a
      ><a name="10012" class="Symbol"
      >:</a
      ><a name="10013"
      > </a
      ><a name="10014" class="Symbol"
      >&#8704;</a
      ><a name="10015"
      > </a
      ><a name="10016" class="Symbol"
      >{</a
      ><a name="10017" href="Maps.html#10017" class="Bound"
      >A</a
      ><a name="10018"
      > </a
      ><a name="10019" href="Maps.html#10019" class="Bound"
      >v</a
      ><a name="10020" class="Symbol"
      >}</a
      ><a name="10021"
      > </a
      ><a name="10022" class="Symbol"
      >(</a
      ><a name="10023" href="Maps.html#10023" class="Bound"
      >m</a
      ><a name="10024"
      > </a
      ><a name="10025" class="Symbol"
      >:</a
      ><a name="10026"
      > </a
      ><a name="10027" href="Maps.html#9409" class="Function"
      >PartialMap</a
      ><a name="10037"
      > </a
      ><a name="10038" href="Maps.html#10017" class="Bound"
      >A</a
      ><a name="10039" class="Symbol"
      >)</a
      ><a name="10040"
      > </a
      ><a name="10041" class="Symbol"
      >(</a
      ><a name="10042" href="Maps.html#10042" class="Bound"
      >x</a
      ><a name="10043"
      > </a
      ><a name="10044" href="Maps.html#10044" class="Bound"
      >y</a
      ><a name="10045"
      > </a
      ><a name="10046" class="Symbol"
      >:</a
      ><a name="10047"
      > </a
      ><a name="10048" href="Maps.html#2290" class="Datatype"
      >Id</a
      ><a name="10050" class="Symbol"
      >)</a
      ><a name="10051"
      >
             </a
      ><a name="10065" class="Symbol"
      >&#8594;</a
      ><a name="10066"
      > </a
      ><a name="10067" href="Maps.html#10042" class="Bound"
      >x</a
      ><a name="10068"
      > </a
      ><a name="10069" href="https://agda.github.io/agda-stdlib/Relation.Binary.Core.html#4493" class="Function Operator"
      >&#8802;</a
      ><a name="10070"
      > </a
      ><a name="10071" href="Maps.html#10044" class="Bound"
      >y</a
      ><a name="10072"
      > </a
      ><a name="10073" class="Symbol"
      >&#8594;</a
      ><a name="10074"
      > </a
      ><a name="10075" class="Symbol"
      >(</a
      ><a name="10076" href="Maps.html#9631" class="Function"
      >update</a
      ><a name="10082"
      > </a
      ><a name="10083" href="Maps.html#10023" class="Bound"
      >m</a
      ><a name="10084"
      > </a
      ><a name="10085" href="Maps.html#10042" class="Bound"
      >x</a
      ><a name="10086"
      > </a
      ><a name="10087" href="Maps.html#10019" class="Bound"
      >v</a
      ><a name="10088" class="Symbol"
      >)</a
      ><a name="10089"
      > </a
      ><a name="10090" href="Maps.html#10044" class="Bound"
      >y</a
      ><a name="10091"
      > </a
      ><a name="10092" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="10093"
      > </a
      ><a name="10094" href="Maps.html#10023" class="Bound"
      >m</a
      ><a name="10095"
      > </a
      ><a name="10096" href="Maps.html#10044" class="Bound"
      >y</a
      ><a name="10097"
      >
  </a
      ><a name="10100" href="Maps.html#10001" class="Function"
      >update-neq</a
      ><a name="10110"
      > </a
      ><a name="10111" href="Maps.html#10111" class="Bound"
      >m</a
      ><a name="10112"
      > </a
      ><a name="10113" href="Maps.html#10113" class="Bound"
      >x</a
      ><a name="10114"
      > </a
      ><a name="10115" href="Maps.html#10115" class="Bound"
      >y</a
      ><a name="10116"
      > </a
      ><a name="10117" href="Maps.html#10117" class="Bound"
      >x&#8800;y</a
      ><a name="10120"
      > </a
      ><a name="10121" class="Symbol"
      >=</a
      ><a name="10122"
      > </a
      ><a name="10123" href="Maps.html#6580" class="Function"
      >TotalMap.update-neq</a
      ><a name="10142"
      > </a
      ><a name="10143" href="Maps.html#10111" class="Bound"
      >m</a
      ><a name="10144"
      > </a
      ><a name="10145" href="Maps.html#10113" class="Bound"
      >x</a
      ><a name="10146"
      > </a
      ><a name="10147" href="Maps.html#10115" class="Bound"
      >y</a
      ><a name="10148"
      > </a
      ><a name="10149" href="Maps.html#10117" class="Bound"
      >x&#8800;y</a
      >
{% endraw %}</pre>

<pre class="Agda">{% raw %}
  <a name="10180" href="Maps.html#10180" class="Function"
      >update-shadow</a
      ><a name="10193"
      > </a
      ><a name="10194" class="Symbol"
      >:</a
      ><a name="10195"
      > </a
      ><a name="10196" class="Symbol"
      >&#8704;</a
      ><a name="10197"
      > </a
      ><a name="10198" class="Symbol"
      >{</a
      ><a name="10199" href="Maps.html#10199" class="Bound"
      >A</a
      ><a name="10200"
      > </a
      ><a name="10201" href="Maps.html#10201" class="Bound"
      >v1</a
      ><a name="10203"
      > </a
      ><a name="10204" href="Maps.html#10204" class="Bound"
      >v2</a
      ><a name="10206" class="Symbol"
      >}</a
      ><a name="10207"
      > </a
      ><a name="10208" class="Symbol"
      >(</a
      ><a name="10209" href="Maps.html#10209" class="Bound"
      >m</a
      ><a name="10210"
      > </a
      ><a name="10211" class="Symbol"
      >:</a
      ><a name="10212"
      > </a
      ><a name="10213" href="Maps.html#9409" class="Function"
      >PartialMap</a
      ><a name="10223"
      > </a
      ><a name="10224" href="Maps.html#10199" class="Bound"
      >A</a
      ><a name="10225" class="Symbol"
      >)</a
      ><a name="10226"
      > </a
      ><a name="10227" class="Symbol"
      >(</a
      ><a name="10228" href="Maps.html#10228" class="Bound"
      >x</a
      ><a name="10229"
      > </a
      ><a name="10230" href="Maps.html#10230" class="Bound"
      >y</a
      ><a name="10231"
      > </a
      ><a name="10232" class="Symbol"
      >:</a
      ><a name="10233"
      > </a
      ><a name="10234" href="Maps.html#2290" class="Datatype"
      >Id</a
      ><a name="10236" class="Symbol"
      >)</a
      ><a name="10237"
      >
                </a
      ><a name="10254" class="Symbol"
      >&#8594;</a
      ><a name="10255"
      > </a
      ><a name="10256" class="Symbol"
      >(</a
      ><a name="10257" href="Maps.html#9631" class="Function"
      >update</a
      ><a name="10263"
      > </a
      ><a name="10264" class="Symbol"
      >(</a
      ><a name="10265" href="Maps.html#9631" class="Function"
      >update</a
      ><a name="10271"
      > </a
      ><a name="10272" href="Maps.html#10209" class="Bound"
      >m</a
      ><a name="10273"
      > </a
      ><a name="10274" href="Maps.html#10228" class="Bound"
      >x</a
      ><a name="10275"
      > </a
      ><a name="10276" href="Maps.html#10201" class="Bound"
      >v1</a
      ><a name="10278" class="Symbol"
      >)</a
      ><a name="10279"
      > </a
      ><a name="10280" href="Maps.html#10228" class="Bound"
      >x</a
      ><a name="10281"
      > </a
      ><a name="10282" href="Maps.html#10204" class="Bound"
      >v2</a
      ><a name="10284" class="Symbol"
      >)</a
      ><a name="10285"
      > </a
      ><a name="10286" href="Maps.html#10230" class="Bound"
      >y</a
      ><a name="10287"
      > </a
      ><a name="10288" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="10289"
      > </a
      ><a name="10290" class="Symbol"
      >(</a
      ><a name="10291" href="Maps.html#9631" class="Function"
      >update</a
      ><a name="10297"
      > </a
      ><a name="10298" href="Maps.html#10209" class="Bound"
      >m</a
      ><a name="10299"
      > </a
      ><a name="10300" href="Maps.html#10228" class="Bound"
      >x</a
      ><a name="10301"
      > </a
      ><a name="10302" href="Maps.html#10204" class="Bound"
      >v2</a
      ><a name="10304" class="Symbol"
      >)</a
      ><a name="10305"
      > </a
      ><a name="10306" href="Maps.html#10230" class="Bound"
      >y</a
      ><a name="10307"
      >
  </a
      ><a name="10310" href="Maps.html#10180" class="Function"
      >update-shadow</a
      ><a name="10323"
      > </a
      ><a name="10324" href="Maps.html#10324" class="Bound"
      >m</a
      ><a name="10325"
      > </a
      ><a name="10326" href="Maps.html#10326" class="Bound"
      >x</a
      ><a name="10327"
      > </a
      ><a name="10328" href="Maps.html#10328" class="Bound"
      >y</a
      ><a name="10329"
      > </a
      ><a name="10330" class="Symbol"
      >=</a
      ><a name="10331"
      > </a
      ><a name="10332" href="Maps.html#7152" class="Postulate"
      >TotalMap.update-shadow</a
      ><a name="10354"
      > </a
      ><a name="10355" href="Maps.html#10324" class="Bound"
      >m</a
      ><a name="10356"
      > </a
      ><a name="10357" href="Maps.html#10326" class="Bound"
      >x</a
      ><a name="10358"
      > </a
      ><a name="10359" href="Maps.html#10328" class="Bound"
      >y</a
      >
{% endraw %}</pre>

<pre class="Agda">{% raw %}
  <a name="10388" href="Maps.html#10388" class="Function"
      >update-same</a
      ><a name="10399"
      > </a
      ><a name="10400" class="Symbol"
      >:</a
      ><a name="10401"
      > </a
      ><a name="10402" class="Symbol"
      >&#8704;</a
      ><a name="10403"
      > </a
      ><a name="10404" class="Symbol"
      >{</a
      ><a name="10405" href="Maps.html#10405" class="Bound"
      >A</a
      ><a name="10406"
      > </a
      ><a name="10407" href="Maps.html#10407" class="Bound"
      >v</a
      ><a name="10408" class="Symbol"
      >}</a
      ><a name="10409"
      > </a
      ><a name="10410" class="Symbol"
      >(</a
      ><a name="10411" href="Maps.html#10411" class="Bound"
      >m</a
      ><a name="10412"
      > </a
      ><a name="10413" class="Symbol"
      >:</a
      ><a name="10414"
      > </a
      ><a name="10415" href="Maps.html#9409" class="Function"
      >PartialMap</a
      ><a name="10425"
      > </a
      ><a name="10426" href="Maps.html#10405" class="Bound"
      >A</a
      ><a name="10427" class="Symbol"
      >)</a
      ><a name="10428"
      > </a
      ><a name="10429" class="Symbol"
      >(</a
      ><a name="10430" href="Maps.html#10430" class="Bound"
      >x</a
      ><a name="10431"
      > </a
      ><a name="10432" href="Maps.html#10432" class="Bound"
      >y</a
      ><a name="10433"
      > </a
      ><a name="10434" class="Symbol"
      >:</a
      ><a name="10435"
      > </a
      ><a name="10436" href="Maps.html#2290" class="Datatype"
      >Id</a
      ><a name="10438" class="Symbol"
      >)</a
      ><a name="10439"
      >
              </a
      ><a name="10454" class="Symbol"
      >&#8594;</a
      ><a name="10455"
      > </a
      ><a name="10456" href="Maps.html#10411" class="Bound"
      >m</a
      ><a name="10457"
      > </a
      ><a name="10458" href="Maps.html#10430" class="Bound"
      >x</a
      ><a name="10459"
      > </a
      ><a name="10460" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="10461"
      > </a
      ><a name="10462" href="https://agda.github.io/agda-stdlib/Data.Maybe.Base.html#373" class="InductiveConstructor"
      >just</a
      ><a name="10466"
      > </a
      ><a name="10467" href="Maps.html#10407" class="Bound"
      >v</a
      ><a name="10468"
      >
              </a
      ><a name="10483" class="Symbol"
      >&#8594;</a
      ><a name="10484"
      > </a
      ><a name="10485" class="Symbol"
      >(</a
      ><a name="10486" href="Maps.html#9631" class="Function"
      >update</a
      ><a name="10492"
      > </a
      ><a name="10493" href="Maps.html#10411" class="Bound"
      >m</a
      ><a name="10494"
      > </a
      ><a name="10495" href="Maps.html#10430" class="Bound"
      >x</a
      ><a name="10496"
      > </a
      ><a name="10497" href="Maps.html#10407" class="Bound"
      >v</a
      ><a name="10498" class="Symbol"
      >)</a
      ><a name="10499"
      > </a
      ><a name="10500" href="Maps.html#10432" class="Bound"
      >y</a
      ><a name="10501"
      > </a
      ><a name="10502" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="10503"
      > </a
      ><a name="10504" href="Maps.html#10411" class="Bound"
      >m</a
      ><a name="10505"
      > </a
      ><a name="10506" href="Maps.html#10432" class="Bound"
      >y</a
      ><a name="10507"
      >
  </a
      ><a name="10510" href="Maps.html#10388" class="Function"
      >update-same</a
      ><a name="10521"
      > </a
      ><a name="10522" href="Maps.html#10522" class="Bound"
      >m</a
      ><a name="10523"
      > </a
      ><a name="10524" href="Maps.html#10524" class="Bound"
      >x</a
      ><a name="10525"
      > </a
      ><a name="10526" href="Maps.html#10526" class="Bound"
      >y</a
      ><a name="10527"
      > </a
      ><a name="10528" href="Maps.html#10528" class="Bound"
      >mx=v</a
      ><a name="10532"
      > </a
      ><a name="10533" class="Keyword"
      >rewrite</a
      ><a name="10540"
      > </a
      ><a name="10541" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.Core.html#565" class="Function"
      >sym</a
      ><a name="10544"
      > </a
      ><a name="10545" href="Maps.html#10528" class="Bound"
      >mx=v</a
      ><a name="10549"
      > </a
      ><a name="10550" class="Symbol"
      >=</a
      ><a name="10551"
      > </a
      ><a name="10552" href="Maps.html#7808" class="Postulate"
      >TotalMap.update-same</a
      ><a name="10572"
      > </a
      ><a name="10573" href="Maps.html#10522" class="Bound"
      >m</a
      ><a name="10574"
      > </a
      ><a name="10575" href="Maps.html#10524" class="Bound"
      >x</a
      ><a name="10576"
      > </a
      ><a name="10577" href="Maps.html#10526" class="Bound"
      >y</a
      >
{% endraw %}</pre>

<pre class="Agda">{% raw %}
  <a name="10606" href="Maps.html#10606" class="Function"
      >update-permute</a
      ><a name="10620"
      > </a
      ><a name="10621" class="Symbol"
      >:</a
      ><a name="10622"
      > </a
      ><a name="10623" class="Symbol"
      >&#8704;</a
      ><a name="10624"
      > </a
      ><a name="10625" class="Symbol"
      >{</a
      ><a name="10626" href="Maps.html#10626" class="Bound"
      >A</a
      ><a name="10627"
      > </a
      ><a name="10628" href="Maps.html#10628" class="Bound"
      >v1</a
      ><a name="10630"
      > </a
      ><a name="10631" href="Maps.html#10631" class="Bound"
      >v2</a
      ><a name="10633" class="Symbol"
      >}</a
      ><a name="10634"
      > </a
      ><a name="10635" class="Symbol"
      >(</a
      ><a name="10636" href="Maps.html#10636" class="Bound"
      >m</a
      ><a name="10637"
      > </a
      ><a name="10638" class="Symbol"
      >:</a
      ><a name="10639"
      > </a
      ><a name="10640" href="Maps.html#9409" class="Function"
      >PartialMap</a
      ><a name="10650"
      > </a
      ><a name="10651" href="Maps.html#10626" class="Bound"
      >A</a
      ><a name="10652" class="Symbol"
      >)</a
      ><a name="10653"
      > </a
      ><a name="10654" class="Symbol"
      >(</a
      ><a name="10655" href="Maps.html#10655" class="Bound"
      >x1</a
      ><a name="10657"
      > </a
      ><a name="10658" href="Maps.html#10658" class="Bound"
      >x2</a
      ><a name="10660"
      > </a
      ><a name="10661" href="Maps.html#10661" class="Bound"
      >y</a
      ><a name="10662"
      > </a
      ><a name="10663" class="Symbol"
      >:</a
      ><a name="10664"
      > </a
      ><a name="10665" href="Maps.html#2290" class="Datatype"
      >Id</a
      ><a name="10667" class="Symbol"
      >)</a
      ><a name="10668"
      >
                 </a
      ><a name="10686" class="Symbol"
      >&#8594;</a
      ><a name="10687"
      > </a
      ><a name="10688" href="Maps.html#10655" class="Bound"
      >x1</a
      ><a name="10690"
      > </a
      ><a name="10691" href="https://agda.github.io/agda-stdlib/Relation.Binary.Core.html#4493" class="Function Operator"
      >&#8802;</a
      ><a name="10692"
      > </a
      ><a name="10693" href="Maps.html#10658" class="Bound"
      >x2</a
      ><a name="10695"
      > </a
      ><a name="10696" class="Symbol"
      >&#8594;</a
      ><a name="10697"
      > </a
      ><a name="10698" class="Symbol"
      >(</a
      ><a name="10699" href="Maps.html#9631" class="Function"
      >update</a
      ><a name="10705"
      > </a
      ><a name="10706" class="Symbol"
      >(</a
      ><a name="10707" href="Maps.html#9631" class="Function"
      >update</a
      ><a name="10713"
      > </a
      ><a name="10714" href="Maps.html#10636" class="Bound"
      >m</a
      ><a name="10715"
      > </a
      ><a name="10716" href="Maps.html#10658" class="Bound"
      >x2</a
      ><a name="10718"
      > </a
      ><a name="10719" href="Maps.html#10631" class="Bound"
      >v2</a
      ><a name="10721" class="Symbol"
      >)</a
      ><a name="10722"
      > </a
      ><a name="10723" href="Maps.html#10655" class="Bound"
      >x1</a
      ><a name="10725"
      > </a
      ><a name="10726" href="Maps.html#10628" class="Bound"
      >v1</a
      ><a name="10728" class="Symbol"
      >)</a
      ><a name="10729"
      > </a
      ><a name="10730" href="Maps.html#10661" class="Bound"
      >y</a
      ><a name="10731"
      >
                           </a
      ><a name="10759" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="10760"
      > </a
      ><a name="10761" class="Symbol"
      >(</a
      ><a name="10762" href="Maps.html#9631" class="Function"
      >update</a
      ><a name="10768"
      > </a
      ><a name="10769" class="Symbol"
      >(</a
      ><a name="10770" href="Maps.html#9631" class="Function"
      >update</a
      ><a name="10776"
      > </a
      ><a name="10777" href="Maps.html#10636" class="Bound"
      >m</a
      ><a name="10778"
      > </a
      ><a name="10779" href="Maps.html#10655" class="Bound"
      >x1</a
      ><a name="10781"
      > </a
      ><a name="10782" href="Maps.html#10628" class="Bound"
      >v1</a
      ><a name="10784" class="Symbol"
      >)</a
      ><a name="10785"
      > </a
      ><a name="10786" href="Maps.html#10658" class="Bound"
      >x2</a
      ><a name="10788"
      > </a
      ><a name="10789" href="Maps.html#10631" class="Bound"
      >v2</a
      ><a name="10791" class="Symbol"
      >)</a
      ><a name="10792"
      > </a
      ><a name="10793" href="Maps.html#10661" class="Bound"
      >y</a
      ><a name="10794"
      >
  </a
      ><a name="10797" href="Maps.html#10606" class="Function"
      >update-permute</a
      ><a name="10811"
      > </a
      ><a name="10812" href="Maps.html#10812" class="Bound"
      >m</a
      ><a name="10813"
      > </a
      ><a name="10814" href="Maps.html#10814" class="Bound"
      >x1</a
      ><a name="10816"
      > </a
      ><a name="10817" href="Maps.html#10817" class="Bound"
      >x2</a
      ><a name="10819"
      > </a
      ><a name="10820" href="Maps.html#10820" class="Bound"
      >y</a
      ><a name="10821"
      > </a
      ><a name="10822" href="Maps.html#10822" class="Bound"
      >x1&#8800;x2</a
      ><a name="10827"
      > </a
      ><a name="10828" class="Symbol"
      >=</a
      ><a name="10829"
      > </a
      ><a name="10830" href="Maps.html#8388" class="Postulate"
      >TotalMap.update-permute</a
      ><a name="10853"
      > </a
      ><a name="10854" href="Maps.html#10812" class="Bound"
      >m</a
      ><a name="10855"
      > </a
      ><a name="10856" href="Maps.html#10814" class="Bound"
      >x1</a
      ><a name="10858"
      > </a
      ><a name="10859" href="Maps.html#10817" class="Bound"
      >x2</a
      ><a name="10861"
      > </a
      ><a name="10862" href="Maps.html#10820" class="Bound"
      >y</a
      ><a name="10863"
      > </a
      ><a name="10864" href="Maps.html#10822" class="Bound"
      >x1&#8800;x2</a
      >
{% endraw %}</pre>
