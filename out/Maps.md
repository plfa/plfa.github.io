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
directly from Agda's standard library.  You should not notice
much difference, though, because we've been careful to name our
own definitions and theorems the same as their counterparts in the
standard library, wherever they overlap.

<pre class="Agda">{% raw %}
<a name="1490" class="Keyword"
      >open</a
      ><a name="1494"
      > </a
      ><a name="1495" class="Keyword"
      >import</a
      ><a name="1501"
      > </a
      ><a name="1502" href="https://agda.github.io/agda-stdlib/Data.Nat.html#1" class="Module"
      >Data.Nat</a
      ><a name="1510"
      >         </a
      ><a name="1519" class="Keyword"
      >using</a
      ><a name="1524"
      > </a
      ><a name="1525" class="Symbol"
      >(</a
      ><a name="1526" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#97" class="Datatype"
      >&#8469;</a
      ><a name="1527" class="Symbol"
      >)</a
      ><a name="1528"
      >
</a
      ><a name="1529" class="Keyword"
      >open</a
      ><a name="1533"
      > </a
      ><a name="1534" class="Keyword"
      >import</a
      ><a name="1540"
      > </a
      ><a name="1541" href="https://agda.github.io/agda-stdlib/Data.Empty.html#1" class="Module"
      >Data.Empty</a
      ><a name="1551"
      >       </a
      ><a name="1558" class="Keyword"
      >using</a
      ><a name="1563"
      > </a
      ><a name="1564" class="Symbol"
      >(</a
      ><a name="1565" href="https://agda.github.io/agda-stdlib/Data.Empty.html#243" class="Datatype"
      >&#8869;</a
      ><a name="1566" class="Symbol"
      >;</a
      ><a name="1567"
      > </a
      ><a name="1568" href="https://agda.github.io/agda-stdlib/Data.Empty.html#348" class="Function"
      >&#8869;-elim</a
      ><a name="1574" class="Symbol"
      >)</a
      ><a name="1575"
      >
</a
      ><a name="1576" class="Keyword"
      >open</a
      ><a name="1580"
      > </a
      ><a name="1581" class="Keyword"
      >import</a
      ><a name="1587"
      > </a
      ><a name="1588" href="https://agda.github.io/agda-stdlib/Data.Maybe.html#1" class="Module"
      >Data.Maybe</a
      ><a name="1598"
      >       </a
      ><a name="1605" class="Keyword"
      >using</a
      ><a name="1610"
      > </a
      ><a name="1611" class="Symbol"
      >(</a
      ><a name="1612" href="https://agda.github.io/agda-stdlib/Data.Maybe.Base.html#335" class="Datatype"
      >Maybe</a
      ><a name="1617" class="Symbol"
      >;</a
      ><a name="1618"
      > </a
      ><a name="1619" href="https://agda.github.io/agda-stdlib/Data.Maybe.html#1527" class="InductiveConstructor"
      >just</a
      ><a name="1623" class="Symbol"
      >;</a
      ><a name="1624"
      > </a
      ><a name="1625" href="https://agda.github.io/agda-stdlib/Data.Maybe.html#1588" class="InductiveConstructor"
      >nothing</a
      ><a name="1632" class="Symbol"
      >)</a
      ><a name="1633"
      >
</a
      ><a name="1634" class="Keyword"
      >open</a
      ><a name="1638"
      > </a
      ><a name="1639" class="Keyword"
      >import</a
      ><a name="1645"
      > </a
      ><a name="1646" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#1" class="Module"
      >Relation.Nullary</a
      ><a name="1662"
      > </a
      ><a name="1663" class="Keyword"
      >using</a
      ><a name="1668"
      > </a
      ><a name="1669" class="Symbol"
      >(</a
      ><a name="1670" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#414" class="Function Operator"
      >&#172;_</a
      ><a name="1672" class="Symbol"
      >;</a
      ><a name="1673"
      > </a
      ><a name="1674" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#484" class="Datatype"
      >Dec</a
      ><a name="1677" class="Symbol"
      >;</a
      ><a name="1678"
      > </a
      ><a name="1679" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#520" class="InductiveConstructor"
      >yes</a
      ><a name="1682" class="Symbol"
      >;</a
      ><a name="1683"
      > </a
      ><a name="1684" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#547" class="InductiveConstructor"
      >no</a
      ><a name="1686" class="Symbol"
      >)</a
      ><a name="1687"
      >
</a
      ><a name="1688" class="Keyword"
      >open</a
      ><a name="1692"
      > </a
      ><a name="1693" class="Keyword"
      >import</a
      ><a name="1699"
      > </a
      ><a name="1700" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#1" class="Module"
      >Relation.Binary.PropositionalEquality</a
      ><a name="1737"
      >
                             </a
      ><a name="1767" class="Keyword"
      >using</a
      ><a name="1772"
      > </a
      ><a name="1773" class="Symbol"
      >(</a
      ><a name="1774" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >_&#8801;_</a
      ><a name="1777" class="Symbol"
      >;</a
      ><a name="1778"
      > </a
      ><a name="1779" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="1783" class="Symbol"
      >;</a
      ><a name="1784"
      > </a
      ><a name="1785" href="https://agda.github.io/agda-stdlib/Relation.Binary.Core.html#4493" class="Function Operator"
      >_&#8802;_</a
      ><a name="1788" class="Symbol"
      >;</a
      ><a name="1789"
      > </a
      ><a name="1790" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.Core.html#632" class="Function"
      >trans</a
      ><a name="1795" class="Symbol"
      >;</a
      ><a name="1796"
      > </a
      ><a name="1797" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.Core.html#565" class="Function"
      >sym</a
      ><a name="1800" class="Symbol"
      >)</a
      >
{% endraw %}</pre>

Documentation for the standard library can be found at
<https://agda.github.io/agda-stdlib/>.

## Identifiers

First, we need a type for the keys that we use to index into our
maps.  For this purpose, we again use the type `Id` from the
[Lists](sf/Lists.html) chapter.  To make this chapter self contained,
we repeat its definition here.

<pre class="Agda">{% raw %}
<a name="2166" class="Keyword"
      >data</a
      ><a name="2170"
      > </a
      ><a name="2171" href="Maps.html#2171" class="Datatype"
      >Id</a
      ><a name="2173"
      > </a
      ><a name="2174" class="Symbol"
      >:</a
      ><a name="2175"
      > </a
      ><a name="2176" class="PrimitiveType"
      >Set</a
      ><a name="2179"
      > </a
      ><a name="2180" class="Keyword"
      >where</a
      ><a name="2185"
      >
  </a
      ><a name="2188" href="Maps.html#2188" class="InductiveConstructor"
      >id</a
      ><a name="2190"
      > </a
      ><a name="2191" class="Symbol"
      >:</a
      ><a name="2192"
      > </a
      ><a name="2193" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#97" class="Datatype"
      >&#8469;</a
      ><a name="2194"
      > </a
      ><a name="2195" class="Symbol"
      >&#8594;</a
      ><a name="2196"
      > </a
      ><a name="2197" href="Maps.html#2171" class="Datatype"
      >Id</a
      >
{% endraw %}</pre>

We recall a standard fact of logic.

<pre class="Agda">{% raw %}
<a name="2262" href="Maps.html#2262" class="Function"
      >contrapositive</a
      ><a name="2276"
      > </a
      ><a name="2277" class="Symbol"
      >:</a
      ><a name="2278"
      > </a
      ><a name="2279" class="Symbol"
      >&#8704;</a
      ><a name="2280"
      > </a
      ><a name="2281" class="Symbol"
      >{</a
      ><a name="2282" href="Maps.html#2282" class="Bound"
      >&#8467;&#8321;</a
      ><a name="2284"
      > </a
      ><a name="2285" href="Maps.html#2285" class="Bound"
      >&#8467;&#8322;</a
      ><a name="2287" class="Symbol"
      >}</a
      ><a name="2288"
      > </a
      ><a name="2289" class="Symbol"
      >{</a
      ><a name="2290" href="Maps.html#2290" class="Bound"
      >P</a
      ><a name="2291"
      > </a
      ><a name="2292" class="Symbol"
      >:</a
      ><a name="2293"
      > </a
      ><a name="2294" class="PrimitiveType"
      >Set</a
      ><a name="2297"
      > </a
      ><a name="2298" href="Maps.html#2282" class="Bound"
      >&#8467;&#8321;</a
      ><a name="2300" class="Symbol"
      >}</a
      ><a name="2301"
      > </a
      ><a name="2302" class="Symbol"
      >{</a
      ><a name="2303" href="Maps.html#2303" class="Bound"
      >Q</a
      ><a name="2304"
      > </a
      ><a name="2305" class="Symbol"
      >:</a
      ><a name="2306"
      > </a
      ><a name="2307" class="PrimitiveType"
      >Set</a
      ><a name="2310"
      > </a
      ><a name="2311" href="Maps.html#2285" class="Bound"
      >&#8467;&#8322;</a
      ><a name="2313" class="Symbol"
      >}</a
      ><a name="2314"
      > </a
      ><a name="2315" class="Symbol"
      >&#8594;</a
      ><a name="2316"
      > </a
      ><a name="2317" class="Symbol"
      >(</a
      ><a name="2318" href="Maps.html#2290" class="Bound"
      >P</a
      ><a name="2319"
      > </a
      ><a name="2320" class="Symbol"
      >&#8594;</a
      ><a name="2321"
      > </a
      ><a name="2322" href="Maps.html#2303" class="Bound"
      >Q</a
      ><a name="2323" class="Symbol"
      >)</a
      ><a name="2324"
      > </a
      ><a name="2325" class="Symbol"
      >&#8594;</a
      ><a name="2326"
      > </a
      ><a name="2327" class="Symbol"
      >(</a
      ><a name="2328" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#414" class="Function Operator"
      >&#172;</a
      ><a name="2329"
      > </a
      ><a name="2330" href="Maps.html#2303" class="Bound"
      >Q</a
      ><a name="2331"
      > </a
      ><a name="2332" class="Symbol"
      >&#8594;</a
      ><a name="2333"
      > </a
      ><a name="2334" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#414" class="Function Operator"
      >&#172;</a
      ><a name="2335"
      > </a
      ><a name="2336" href="Maps.html#2290" class="Bound"
      >P</a
      ><a name="2337" class="Symbol"
      >)</a
      ><a name="2338"
      >
</a
      ><a name="2339" href="Maps.html#2262" class="Function"
      >contrapositive</a
      ><a name="2353"
      > </a
      ><a name="2354" href="Maps.html#2354" class="Bound"
      >p&#8594;q</a
      ><a name="2357"
      > </a
      ><a name="2358" href="Maps.html#2358" class="Bound"
      >&#172;q</a
      ><a name="2360"
      > </a
      ><a name="2361" href="Maps.html#2361" class="Bound"
      >p</a
      ><a name="2362"
      > </a
      ><a name="2363" class="Symbol"
      >=</a
      ><a name="2364"
      > </a
      ><a name="2365" href="Maps.html#2358" class="Bound"
      >&#172;q</a
      ><a name="2367"
      > </a
      ><a name="2368" class="Symbol"
      >(</a
      ><a name="2369" href="Maps.html#2354" class="Bound"
      >p&#8594;q</a
      ><a name="2372"
      > </a
      ><a name="2373" href="Maps.html#2361" class="Bound"
      >p</a
      ><a name="2374" class="Symbol"
      >)</a
      >
{% endraw %}</pre>

Using the above, we can decide equality of two identifiers
by deciding equality on the underlying strings.

<pre class="Agda">{% raw %}
<a name="2509" href="Maps.html#2509" class="Function Operator"
      >_&#8799;_</a
      ><a name="2512"
      > </a
      ><a name="2513" class="Symbol"
      >:</a
      ><a name="2514"
      > </a
      ><a name="2515" class="Symbol"
      >(</a
      ><a name="2516" href="Maps.html#2516" class="Bound"
      >x</a
      ><a name="2517"
      > </a
      ><a name="2518" href="Maps.html#2518" class="Bound"
      >y</a
      ><a name="2519"
      > </a
      ><a name="2520" class="Symbol"
      >:</a
      ><a name="2521"
      > </a
      ><a name="2522" href="Maps.html#2171" class="Datatype"
      >Id</a
      ><a name="2524" class="Symbol"
      >)</a
      ><a name="2525"
      > </a
      ><a name="2526" class="Symbol"
      >&#8594;</a
      ><a name="2527"
      > </a
      ><a name="2528" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#484" class="Datatype"
      >Dec</a
      ><a name="2531"
      > </a
      ><a name="2532" class="Symbol"
      >(</a
      ><a name="2533" href="Maps.html#2516" class="Bound"
      >x</a
      ><a name="2534"
      > </a
      ><a name="2535" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="2536"
      > </a
      ><a name="2537" href="Maps.html#2518" class="Bound"
      >y</a
      ><a name="2538" class="Symbol"
      >)</a
      ><a name="2539"
      >
</a
      ><a name="2540" href="Maps.html#2188" class="InductiveConstructor"
      >id</a
      ><a name="2542"
      > </a
      ><a name="2543" href="Maps.html#2543" class="Bound"
      >x</a
      ><a name="2544"
      > </a
      ><a name="2545" href="Maps.html#2509" class="Function Operator"
      >&#8799;</a
      ><a name="2546"
      > </a
      ><a name="2547" href="Maps.html#2188" class="InductiveConstructor"
      >id</a
      ><a name="2549"
      > </a
      ><a name="2550" href="Maps.html#2550" class="Bound"
      >y</a
      ><a name="2551"
      > </a
      ><a name="2552" class="Keyword"
      >with</a
      ><a name="2556"
      > </a
      ><a name="2557" href="Maps.html#2543" class="Bound"
      >x</a
      ><a name="2558"
      > </a
      ><a name="2559" href="https://agda.github.io/agda-stdlib/Data.Nat.Base.html#3212" class="Function Operator"
      >Data.Nat.&#8799;</a
      ><a name="2569"
      > </a
      ><a name="2570" href="Maps.html#2550" class="Bound"
      >y</a
      ><a name="2571"
      >
</a
      ><a name="2572" href="Maps.html#2188" class="InductiveConstructor"
      >id</a
      ><a name="2574"
      > </a
      ><a name="2575" href="Maps.html#2575" class="Bound"
      >x</a
      ><a name="2576"
      > </a
      ><a name="2577" href="Maps.html#2509" class="Function Operator"
      >&#8799;</a
      ><a name="2578"
      > </a
      ><a name="2579" href="Maps.html#2188" class="InductiveConstructor"
      >id</a
      ><a name="2581"
      > </a
      ><a name="2582" href="Maps.html#2582" class="Bound"
      >y</a
      ><a name="2583"
      > </a
      ><a name="2584" class="Symbol"
      >|</a
      ><a name="2585"
      > </a
      ><a name="2586" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#520" class="InductiveConstructor"
      >yes</a
      ><a name="2589"
      > </a
      ><a name="2590" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="2594"
      >  </a
      ><a name="2596" class="Symbol"
      >=</a
      ><a name="2597"
      >  </a
      ><a name="2599" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#520" class="InductiveConstructor"
      >yes</a
      ><a name="2602"
      > </a
      ><a name="2603" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="2607"
      >
</a
      ><a name="2608" href="Maps.html#2188" class="InductiveConstructor"
      >id</a
      ><a name="2610"
      > </a
      ><a name="2611" href="Maps.html#2611" class="Bound"
      >x</a
      ><a name="2612"
      > </a
      ><a name="2613" href="Maps.html#2509" class="Function Operator"
      >&#8799;</a
      ><a name="2614"
      > </a
      ><a name="2615" href="Maps.html#2188" class="InductiveConstructor"
      >id</a
      ><a name="2617"
      > </a
      ><a name="2618" href="Maps.html#2618" class="Bound"
      >y</a
      ><a name="2619"
      > </a
      ><a name="2620" class="Symbol"
      >|</a
      ><a name="2621"
      > </a
      ><a name="2622" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#547" class="InductiveConstructor"
      >no</a
      ><a name="2624"
      >  </a
      ><a name="2626" href="Maps.html#2626" class="Bound"
      >x&#8802;y</a
      ><a name="2629"
      >   </a
      ><a name="2632" class="Symbol"
      >=</a
      ><a name="2633"
      >  </a
      ><a name="2635" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#547" class="InductiveConstructor"
      >no</a
      ><a name="2637"
      > </a
      ><a name="2638" class="Symbol"
      >(</a
      ><a name="2639" href="Maps.html#2262" class="Function"
      >contrapositive</a
      ><a name="2653"
      > </a
      ><a name="2654" href="Maps.html#2678" class="Function"
      >id-inj</a
      ><a name="2660"
      > </a
      ><a name="2661" href="Maps.html#2626" class="Bound"
      >x&#8802;y</a
      ><a name="2664" class="Symbol"
      >)</a
      ><a name="2665"
      >
  </a
      ><a name="2668" class="Keyword"
      >where</a
      ><a name="2673"
      >
    </a
      ><a name="2678" href="Maps.html#2678" class="Function"
      >id-inj</a
      ><a name="2684"
      > </a
      ><a name="2685" class="Symbol"
      >:</a
      ><a name="2686"
      > </a
      ><a name="2687" class="Symbol"
      >&#8704;</a
      ><a name="2688"
      > </a
      ><a name="2689" class="Symbol"
      >{</a
      ><a name="2690" href="Maps.html#2690" class="Bound"
      >x</a
      ><a name="2691"
      > </a
      ><a name="2692" href="Maps.html#2692" class="Bound"
      >y</a
      ><a name="2693" class="Symbol"
      >}</a
      ><a name="2694"
      > </a
      ><a name="2695" class="Symbol"
      >&#8594;</a
      ><a name="2696"
      > </a
      ><a name="2697" href="Maps.html#2188" class="InductiveConstructor"
      >id</a
      ><a name="2699"
      > </a
      ><a name="2700" href="Maps.html#2690" class="Bound"
      >x</a
      ><a name="2701"
      > </a
      ><a name="2702" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="2703"
      > </a
      ><a name="2704" href="Maps.html#2188" class="InductiveConstructor"
      >id</a
      ><a name="2706"
      > </a
      ><a name="2707" href="Maps.html#2692" class="Bound"
      >y</a
      ><a name="2708"
      > </a
      ><a name="2709" class="Symbol"
      >&#8594;</a
      ><a name="2710"
      > </a
      ><a name="2711" href="Maps.html#2690" class="Bound"
      >x</a
      ><a name="2712"
      > </a
      ><a name="2713" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="2714"
      > </a
      ><a name="2715" href="Maps.html#2692" class="Bound"
      >y</a
      ><a name="2716"
      >
    </a
      ><a name="2721" href="Maps.html#2678" class="Function"
      >id-inj</a
      ><a name="2727"
      > </a
      ><a name="2728" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="2732"
      >  </a
      ><a name="2734" class="Symbol"
      >=</a
      ><a name="2735"
      >  </a
      ><a name="2737" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
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
<a name="3573" href="Maps.html#3573" class="Function"
      >TotalMap</a
      ><a name="3581"
      > </a
      ><a name="3582" class="Symbol"
      >:</a
      ><a name="3583"
      > </a
      ><a name="3584" class="PrimitiveType"
      >Set</a
      ><a name="3587"
      > </a
      ><a name="3588" class="Symbol"
      >&#8594;</a
      ><a name="3589"
      > </a
      ><a name="3590" class="PrimitiveType"
      >Set</a
      ><a name="3593"
      >
</a
      ><a name="3594" href="Maps.html#3573" class="Function"
      >TotalMap</a
      ><a name="3602"
      > </a
      ><a name="3603" href="Maps.html#3603" class="Bound"
      >A</a
      ><a name="3604"
      > </a
      ><a name="3605" class="Symbol"
      >=</a
      ><a name="3606"
      > </a
      ><a name="3607" href="Maps.html#2171" class="Datatype"
      >Id</a
      ><a name="3609"
      > </a
      ><a name="3610" class="Symbol"
      >&#8594;</a
      ><a name="3611"
      > </a
      ><a name="3612" href="Maps.html#3603" class="Bound"
      >A</a
      >
{% endraw %}</pre>

Intuitively, a total map over anﬁ element type `A` _is_ just a
function that can be used to look up ids, yielding `A`s.

<pre class="Agda">{% raw %}
<a name="3760" class="Keyword"
      >module</a
      ><a name="3766"
      > </a
      ><a name="3767" href="Maps.html#3767" class="Module"
      >TotalMap</a
      ><a name="3775"
      > </a
      ><a name="3776" class="Keyword"
      >where</a
      >
{% endraw %}</pre>

The function `always` yields a total map given a
default element; this map always returns the default element when
applied to any id.

<pre class="Agda">{% raw %}
  <a name="3944" href="Maps.html#3944" class="Function"
      >always</a
      ><a name="3950"
      > </a
      ><a name="3951" class="Symbol"
      >:</a
      ><a name="3952"
      > </a
      ><a name="3953" class="Symbol"
      >&#8704;</a
      ><a name="3954"
      > </a
      ><a name="3955" class="Symbol"
      >{</a
      ><a name="3956" href="Maps.html#3956" class="Bound"
      >A</a
      ><a name="3957" class="Symbol"
      >}</a
      ><a name="3958"
      > </a
      ><a name="3959" class="Symbol"
      >&#8594;</a
      ><a name="3960"
      > </a
      ><a name="3961" href="Maps.html#3956" class="Bound"
      >A</a
      ><a name="3962"
      > </a
      ><a name="3963" class="Symbol"
      >&#8594;</a
      ><a name="3964"
      > </a
      ><a name="3965" href="Maps.html#3573" class="Function"
      >TotalMap</a
      ><a name="3973"
      > </a
      ><a name="3974" href="Maps.html#3956" class="Bound"
      >A</a
      ><a name="3975"
      >
  </a
      ><a name="3978" href="Maps.html#3944" class="Function"
      >always</a
      ><a name="3984"
      > </a
      ><a name="3985" href="Maps.html#3985" class="Bound"
      >v</a
      ><a name="3986"
      > </a
      ><a name="3987" href="Maps.html#3987" class="Bound"
      >x</a
      ><a name="3988"
      > </a
      ><a name="3989" class="Symbol"
      >=</a
      ><a name="3990"
      > </a
      ><a name="3991" href="Maps.html#3985" class="Bound"
      >v</a
      >
{% endraw %}</pre>

More interesting is the update function, which (as before) takes
a map `ρ`, a key `x`, and a value `v` and returns a new map that
takes `x` to `v` and takes every other key to whatever `ρ` does.

<pre class="Agda">{% raw %}
  <a name="4216" class="Keyword"
      >infixl</a
      ><a name="4222"
      > </a
      ><a name="4223" class="Number"
      >15</a
      ><a name="4225"
      > </a
      ><a name="4226" href="Maps.html#4237" class="Function Operator"
      >_,_&#8614;_</a
      ><a name="4231"
      >  

  </a
      ><a name="4237" href="Maps.html#4237" class="Function Operator"
      >_,_&#8614;_</a
      ><a name="4242"
      > </a
      ><a name="4243" class="Symbol"
      >:</a
      ><a name="4244"
      > </a
      ><a name="4245" class="Symbol"
      >&#8704;</a
      ><a name="4246"
      > </a
      ><a name="4247" class="Symbol"
      >{</a
      ><a name="4248" href="Maps.html#4248" class="Bound"
      >A</a
      ><a name="4249" class="Symbol"
      >}</a
      ><a name="4250"
      > </a
      ><a name="4251" class="Symbol"
      >&#8594;</a
      ><a name="4252"
      > </a
      ><a name="4253" href="Maps.html#3573" class="Function"
      >TotalMap</a
      ><a name="4261"
      > </a
      ><a name="4262" href="Maps.html#4248" class="Bound"
      >A</a
      ><a name="4263"
      > </a
      ><a name="4264" class="Symbol"
      >&#8594;</a
      ><a name="4265"
      > </a
      ><a name="4266" href="Maps.html#2171" class="Datatype"
      >Id</a
      ><a name="4268"
      > </a
      ><a name="4269" class="Symbol"
      >&#8594;</a
      ><a name="4270"
      > </a
      ><a name="4271" href="Maps.html#4248" class="Bound"
      >A</a
      ><a name="4272"
      > </a
      ><a name="4273" class="Symbol"
      >&#8594;</a
      ><a name="4274"
      > </a
      ><a name="4275" href="Maps.html#3573" class="Function"
      >TotalMap</a
      ><a name="4283"
      > </a
      ><a name="4284" href="Maps.html#4248" class="Bound"
      >A</a
      ><a name="4285"
      >
  </a
      ><a name="4288" class="Symbol"
      >(</a
      ><a name="4289" href="Maps.html#4289" class="Bound"
      >&#961;</a
      ><a name="4290"
      > </a
      ><a name="4291" href="Maps.html#4237" class="Function Operator"
      >,</a
      ><a name="4292"
      > </a
      ><a name="4293" href="Maps.html#4293" class="Bound"
      >x</a
      ><a name="4294"
      > </a
      ><a name="4295" href="Maps.html#4237" class="Function Operator"
      >&#8614;</a
      ><a name="4296"
      > </a
      ><a name="4297" href="Maps.html#4297" class="Bound"
      >v</a
      ><a name="4298" class="Symbol"
      >)</a
      ><a name="4299"
      > </a
      ><a name="4300" href="Maps.html#4300" class="Bound"
      >y</a
      ><a name="4301"
      > </a
      ><a name="4302" class="Keyword"
      >with</a
      ><a name="4306"
      > </a
      ><a name="4307" href="Maps.html#4293" class="Bound"
      >x</a
      ><a name="4308"
      > </a
      ><a name="4309" href="Maps.html#2509" class="Function Operator"
      >&#8799;</a
      ><a name="4310"
      > </a
      ><a name="4311" href="Maps.html#4300" class="Bound"
      >y</a
      ><a name="4312"
      >
  </a
      ><a name="4315" class="Symbol"
      >...</a
      ><a name="4318"
      > </a
      ><a name="4319" class="Symbol"
      >|</a
      ><a name="4320"
      > </a
      ><a name="4321" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#520" class="InductiveConstructor"
      >yes</a
      ><a name="4324"
      > </a
      ><a name="4325" href="Maps.html#4325" class="Bound"
      >x&#8801;y</a
      ><a name="4328"
      > </a
      ><a name="4329" class="Symbol"
      >=</a
      ><a name="4330"
      > </a
      ><a name="4331" href="Maps.html#4297" class="Bound"
      >v</a
      ><a name="4332"
      >
  </a
      ><a name="4335" class="Symbol"
      >...</a
      ><a name="4338"
      > </a
      ><a name="4339" class="Symbol"
      >|</a
      ><a name="4340"
      > </a
      ><a name="4341" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#547" class="InductiveConstructor"
      >no</a
      ><a name="4343"
      >  </a
      ><a name="4345" href="Maps.html#4345" class="Bound"
      >x&#8802;y</a
      ><a name="4348"
      > </a
      ><a name="4349" class="Symbol"
      >=</a
      ><a name="4350"
      > </a
      ><a name="4351" href="Maps.html#4289" class="Bound"
      >&#961;</a
      ><a name="4352"
      > </a
      ><a name="4353" href="Maps.html#4300" class="Bound"
      >y</a
      >
{% endraw %}</pre>

This definition is a nice example of higher-order programming.
The update function takes a _function_ `ρ` and yields a new
function that behaves like the desired map.

For example, we can build a map taking ids to naturals, where `x`
maps to 42, `y` maps to 69, and every other key maps to 0, as follows:

<pre class="Agda">{% raw %}
  <a name="4688" class="Keyword"
      >module</a
      ><a name="4694"
      > </a
      ><a name="4695" href="Maps.html#4695" class="Module"
      >example</a
      ><a name="4702"
      > </a
      ><a name="4703" class="Keyword"
      >where</a
      ><a name="4708"
      >

    </a
      ><a name="4714" href="Maps.html#4714" class="Function"
      >x</a
      ><a name="4715"
      > </a
      ><a name="4716" href="Maps.html#4716" class="Function"
      >y</a
      ><a name="4717"
      > </a
      ><a name="4718" href="Maps.html#4718" class="Function"
      >z</a
      ><a name="4719"
      > </a
      ><a name="4720" class="Symbol"
      >:</a
      ><a name="4721"
      > </a
      ><a name="4722" href="Maps.html#2171" class="Datatype"
      >Id</a
      ><a name="4724"
      >
    </a
      ><a name="4729" href="Maps.html#4714" class="Function"
      >x</a
      ><a name="4730"
      > </a
      ><a name="4731" class="Symbol"
      >=</a
      ><a name="4732"
      > </a
      ><a name="4733" href="Maps.html#2188" class="InductiveConstructor"
      >id</a
      ><a name="4735"
      > </a
      ><a name="4736" class="Number"
      >0</a
      ><a name="4737"
      >
    </a
      ><a name="4742" href="Maps.html#4716" class="Function"
      >y</a
      ><a name="4743"
      > </a
      ><a name="4744" class="Symbol"
      >=</a
      ><a name="4745"
      > </a
      ><a name="4746" href="Maps.html#2188" class="InductiveConstructor"
      >id</a
      ><a name="4748"
      > </a
      ><a name="4749" class="Number"
      >1</a
      ><a name="4750"
      >
    </a
      ><a name="4755" href="Maps.html#4718" class="Function"
      >z</a
      ><a name="4756"
      > </a
      ><a name="4757" class="Symbol"
      >=</a
      ><a name="4758"
      > </a
      ><a name="4759" href="Maps.html#2188" class="InductiveConstructor"
      >id</a
      ><a name="4761"
      > </a
      ><a name="4762" class="Number"
      >2</a
      ><a name="4763"
      >

    </a
      ><a name="4769" href="Maps.html#4769" class="Function"
      >&#961;&#8320;</a
      ><a name="4771"
      > </a
      ><a name="4772" class="Symbol"
      >:</a
      ><a name="4773"
      > </a
      ><a name="4774" href="Maps.html#3573" class="Function"
      >TotalMap</a
      ><a name="4782"
      > </a
      ><a name="4783" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#97" class="Datatype"
      >&#8469;</a
      ><a name="4784"
      >
    </a
      ><a name="4789" href="Maps.html#4769" class="Function"
      >&#961;&#8320;</a
      ><a name="4791"
      > </a
      ><a name="4792" class="Symbol"
      >=</a
      ><a name="4793"
      > </a
      ><a name="4794" href="Maps.html#3944" class="Function"
      >always</a
      ><a name="4800"
      > </a
      ><a name="4801" class="Number"
      >0</a
      ><a name="4802"
      > </a
      ><a name="4803" href="Maps.html#4237" class="Function Operator"
      >,</a
      ><a name="4804"
      > </a
      ><a name="4805" href="Maps.html#4714" class="Function"
      >x</a
      ><a name="4806"
      > </a
      ><a name="4807" href="Maps.html#4237" class="Function Operator"
      >&#8614;</a
      ><a name="4808"
      > </a
      ><a name="4809" class="Number"
      >42</a
      ><a name="4811"
      > </a
      ><a name="4812" href="Maps.html#4237" class="Function Operator"
      >,</a
      ><a name="4813"
      > </a
      ><a name="4814" href="Maps.html#4716" class="Function"
      >y</a
      ><a name="4815"
      > </a
      ><a name="4816" href="Maps.html#4237" class="Function Operator"
      >&#8614;</a
      ><a name="4817"
      > </a
      ><a name="4818" class="Number"
      >69</a
      ><a name="4820"
      >

    </a
      ><a name="4826" href="Maps.html#4826" class="Function"
      >test&#8321;</a
      ><a name="4831"
      > </a
      ><a name="4832" class="Symbol"
      >:</a
      ><a name="4833"
      > </a
      ><a name="4834" href="Maps.html#4769" class="Function"
      >&#961;&#8320;</a
      ><a name="4836"
      > </a
      ><a name="4837" href="Maps.html#4714" class="Function"
      >x</a
      ><a name="4838"
      > </a
      ><a name="4839" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="4840"
      > </a
      ><a name="4841" class="Number"
      >42</a
      ><a name="4843"
      >
    </a
      ><a name="4848" href="Maps.html#4826" class="Function"
      >test&#8321;</a
      ><a name="4853"
      > </a
      ><a name="4854" class="Symbol"
      >=</a
      ><a name="4855"
      > </a
      ><a name="4856" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="4860"
      >

    </a
      ><a name="4866" href="Maps.html#4866" class="Function"
      >test&#8322;</a
      ><a name="4871"
      > </a
      ><a name="4872" class="Symbol"
      >:</a
      ><a name="4873"
      > </a
      ><a name="4874" href="Maps.html#4769" class="Function"
      >&#961;&#8320;</a
      ><a name="4876"
      > </a
      ><a name="4877" href="Maps.html#4716" class="Function"
      >y</a
      ><a name="4878"
      > </a
      ><a name="4879" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="4880"
      > </a
      ><a name="4881" class="Number"
      >69</a
      ><a name="4883"
      >
    </a
      ><a name="4888" href="Maps.html#4866" class="Function"
      >test&#8322;</a
      ><a name="4893"
      > </a
      ><a name="4894" class="Symbol"
      >=</a
      ><a name="4895"
      > </a
      ><a name="4896" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="4900"
      >

    </a
      ><a name="4906" href="Maps.html#4906" class="Function"
      >test&#8323;</a
      ><a name="4911"
      > </a
      ><a name="4912" class="Symbol"
      >:</a
      ><a name="4913"
      > </a
      ><a name="4914" href="Maps.html#4769" class="Function"
      >&#961;&#8320;</a
      ><a name="4916"
      > </a
      ><a name="4917" href="Maps.html#4718" class="Function"
      >z</a
      ><a name="4918"
      > </a
      ><a name="4919" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="4920"
      > </a
      ><a name="4921" class="Number"
      >0</a
      ><a name="4922"
      >
    </a
      ><a name="4927" href="Maps.html#4906" class="Function"
      >test&#8323;</a
      ><a name="4932"
      > </a
      ><a name="4933" class="Symbol"
      >=</a
      ><a name="4934"
      > </a
      ><a name="4935" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      >
{% endraw %}</pre>

This completes the definition of total maps.  Note that we don't
need to define a `find` operation because it is just function
application!

To use maps in later chapters, we'll need several fundamental
facts about how they behave.  Even if you don't work the following
exercises, make sure you understand the statements of
the lemmas!

#### Exercise: 1 star, optional (apply-always)
The `always` map returns its default element for all keys:

<pre class="Agda">{% raw %}
  <a name="5411" class="Keyword"
      >postulate</a
      ><a name="5420"
      >
    </a
      ><a name="5425" href="Maps.html#5425" class="Postulate"
      >apply-always</a
      ><a name="5437"
      > </a
      ><a name="5438" class="Symbol"
      >:</a
      ><a name="5439"
      > </a
      ><a name="5440" class="Symbol"
      >&#8704;</a
      ><a name="5441"
      > </a
      ><a name="5442" class="Symbol"
      >{</a
      ><a name="5443" href="Maps.html#5443" class="Bound"
      >A</a
      ><a name="5444" class="Symbol"
      >}</a
      ><a name="5445"
      > </a
      ><a name="5446" class="Symbol"
      >(</a
      ><a name="5447" href="Maps.html#5447" class="Bound"
      >v</a
      ><a name="5448"
      > </a
      ><a name="5449" class="Symbol"
      >:</a
      ><a name="5450"
      > </a
      ><a name="5451" href="Maps.html#5443" class="Bound"
      >A</a
      ><a name="5452" class="Symbol"
      >)</a
      ><a name="5453"
      > </a
      ><a name="5454" class="Symbol"
      >(</a
      ><a name="5455" href="Maps.html#5455" class="Bound"
      >x</a
      ><a name="5456"
      > </a
      ><a name="5457" class="Symbol"
      >:</a
      ><a name="5458"
      > </a
      ><a name="5459" href="Maps.html#2171" class="Datatype"
      >Id</a
      ><a name="5461" class="Symbol"
      >)</a
      ><a name="5462"
      > </a
      ><a name="5463" class="Symbol"
      >&#8594;</a
      ><a name="5464"
      > </a
      ><a name="5465" href="Maps.html#3944" class="Function"
      >always</a
      ><a name="5471"
      > </a
      ><a name="5472" href="Maps.html#5447" class="Bound"
      >v</a
      ><a name="5473"
      > </a
      ><a name="5474" href="Maps.html#5455" class="Bound"
      >x</a
      ><a name="5475"
      > </a
      ><a name="5476" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="5477"
      > </a
      ><a name="5478" href="Maps.html#5447" class="Bound"
      >v</a
      >
{% endraw %}</pre>

<div class="hidden">
<pre class="Agda">{% raw %}
  <a name="5528" href="Maps.html#5528" class="Function"
      >apply-always&#8242;</a
      ><a name="5541"
      > </a
      ><a name="5542" class="Symbol"
      >:</a
      ><a name="5543"
      > </a
      ><a name="5544" class="Symbol"
      >&#8704;</a
      ><a name="5545"
      > </a
      ><a name="5546" class="Symbol"
      >{</a
      ><a name="5547" href="Maps.html#5547" class="Bound"
      >A</a
      ><a name="5548" class="Symbol"
      >}</a
      ><a name="5549"
      > </a
      ><a name="5550" class="Symbol"
      >(</a
      ><a name="5551" href="Maps.html#5551" class="Bound"
      >v</a
      ><a name="5552"
      > </a
      ><a name="5553" class="Symbol"
      >:</a
      ><a name="5554"
      > </a
      ><a name="5555" href="Maps.html#5547" class="Bound"
      >A</a
      ><a name="5556" class="Symbol"
      >)</a
      ><a name="5557"
      > </a
      ><a name="5558" class="Symbol"
      >(</a
      ><a name="5559" href="Maps.html#5559" class="Bound"
      >x</a
      ><a name="5560"
      > </a
      ><a name="5561" class="Symbol"
      >:</a
      ><a name="5562"
      > </a
      ><a name="5563" href="Maps.html#2171" class="Datatype"
      >Id</a
      ><a name="5565" class="Symbol"
      >)</a
      ><a name="5566"
      > </a
      ><a name="5567" class="Symbol"
      >&#8594;</a
      ><a name="5568"
      > </a
      ><a name="5569" href="Maps.html#3944" class="Function"
      >always</a
      ><a name="5575"
      > </a
      ><a name="5576" href="Maps.html#5551" class="Bound"
      >v</a
      ><a name="5577"
      > </a
      ><a name="5578" href="Maps.html#5559" class="Bound"
      >x</a
      ><a name="5579"
      > </a
      ><a name="5580" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="5581"
      > </a
      ><a name="5582" href="Maps.html#5551" class="Bound"
      >v</a
      ><a name="5583"
      >
  </a
      ><a name="5586" href="Maps.html#5528" class="Function"
      >apply-always&#8242;</a
      ><a name="5599"
      > </a
      ><a name="5600" href="Maps.html#5600" class="Bound"
      >v</a
      ><a name="5601"
      > </a
      ><a name="5602" href="Maps.html#5602" class="Bound"
      >x</a
      ><a name="5603"
      > </a
      ><a name="5604" class="Symbol"
      >=</a
      ><a name="5605"
      > </a
      ><a name="5606" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      >
{% endraw %}</pre>
</div>

#### Exercise: 2 stars, optional (update-eq)
Next, if we update a map `ρ` at a key `x` with a new value `v`
and then look up `x` in the map resulting from the update, we get
back `v`:

<pre class="Agda">{% raw %}
  <a name="5830" class="Keyword"
      >postulate</a
      ><a name="5839"
      >
    </a
      ><a name="5844" href="Maps.html#5844" class="Postulate"
      >update-eq</a
      ><a name="5853"
      > </a
      ><a name="5854" class="Symbol"
      >:</a
      ><a name="5855"
      > </a
      ><a name="5856" class="Symbol"
      >&#8704;</a
      ><a name="5857"
      > </a
      ><a name="5858" class="Symbol"
      >{</a
      ><a name="5859" href="Maps.html#5859" class="Bound"
      >A</a
      ><a name="5860" class="Symbol"
      >}</a
      ><a name="5861"
      > </a
      ><a name="5862" class="Symbol"
      >(</a
      ><a name="5863" href="Maps.html#5863" class="Bound"
      >&#961;</a
      ><a name="5864"
      > </a
      ><a name="5865" class="Symbol"
      >:</a
      ><a name="5866"
      > </a
      ><a name="5867" href="Maps.html#3573" class="Function"
      >TotalMap</a
      ><a name="5875"
      > </a
      ><a name="5876" href="Maps.html#5859" class="Bound"
      >A</a
      ><a name="5877" class="Symbol"
      >)</a
      ><a name="5878"
      > </a
      ><a name="5879" class="Symbol"
      >(</a
      ><a name="5880" href="Maps.html#5880" class="Bound"
      >x</a
      ><a name="5881"
      > </a
      ><a name="5882" class="Symbol"
      >:</a
      ><a name="5883"
      > </a
      ><a name="5884" href="Maps.html#2171" class="Datatype"
      >Id</a
      ><a name="5886" class="Symbol"
      >)</a
      ><a name="5887"
      > </a
      ><a name="5888" class="Symbol"
      >(</a
      ><a name="5889" href="Maps.html#5889" class="Bound"
      >v</a
      ><a name="5890"
      > </a
      ><a name="5891" class="Symbol"
      >:</a
      ><a name="5892"
      > </a
      ><a name="5893" href="Maps.html#5859" class="Bound"
      >A</a
      ><a name="5894" class="Symbol"
      >)</a
      ><a name="5895"
      >
              </a
      ><a name="5910" class="Symbol"
      >&#8594;</a
      ><a name="5911"
      > </a
      ><a name="5912" class="Symbol"
      >(</a
      ><a name="5913" href="Maps.html#5863" class="Bound"
      >&#961;</a
      ><a name="5914"
      > </a
      ><a name="5915" href="Maps.html#4237" class="Function Operator"
      >,</a
      ><a name="5916"
      > </a
      ><a name="5917" href="Maps.html#5880" class="Bound"
      >x</a
      ><a name="5918"
      > </a
      ><a name="5919" href="Maps.html#4237" class="Function Operator"
      >&#8614;</a
      ><a name="5920"
      > </a
      ><a name="5921" href="Maps.html#5889" class="Bound"
      >v</a
      ><a name="5922" class="Symbol"
      >)</a
      ><a name="5923"
      > </a
      ><a name="5924" href="Maps.html#5880" class="Bound"
      >x</a
      ><a name="5925"
      > </a
      ><a name="5926" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="5927"
      > </a
      ><a name="5928" href="Maps.html#5889" class="Bound"
      >v</a
      >
{% endraw %}</pre>

<div class="hidden">
<pre class="Agda">{% raw %}
  <a name="5978" href="Maps.html#5978" class="Function"
      >update-eq&#8242;</a
      ><a name="5988"
      > </a
      ><a name="5989" class="Symbol"
      >:</a
      ><a name="5990"
      > </a
      ><a name="5991" class="Symbol"
      >&#8704;</a
      ><a name="5992"
      > </a
      ><a name="5993" class="Symbol"
      >{</a
      ><a name="5994" href="Maps.html#5994" class="Bound"
      >A</a
      ><a name="5995" class="Symbol"
      >}</a
      ><a name="5996"
      > </a
      ><a name="5997" class="Symbol"
      >(</a
      ><a name="5998" href="Maps.html#5998" class="Bound"
      >&#961;</a
      ><a name="5999"
      > </a
      ><a name="6000" class="Symbol"
      >:</a
      ><a name="6001"
      > </a
      ><a name="6002" href="Maps.html#3573" class="Function"
      >TotalMap</a
      ><a name="6010"
      > </a
      ><a name="6011" href="Maps.html#5994" class="Bound"
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
      ><a name="6019" href="Maps.html#2171" class="Datatype"
      >Id</a
      ><a name="6021" class="Symbol"
      >)</a
      ><a name="6022"
      > </a
      ><a name="6023" class="Symbol"
      >(</a
      ><a name="6024" href="Maps.html#6024" class="Bound"
      >v</a
      ><a name="6025"
      > </a
      ><a name="6026" class="Symbol"
      >:</a
      ><a name="6027"
      > </a
      ><a name="6028" href="Maps.html#5994" class="Bound"
      >A</a
      ><a name="6029" class="Symbol"
      >)</a
      ><a name="6030"
      >
             </a
      ><a name="6044" class="Symbol"
      >&#8594;</a
      ><a name="6045"
      > </a
      ><a name="6046" class="Symbol"
      >(</a
      ><a name="6047" href="Maps.html#5998" class="Bound"
      >&#961;</a
      ><a name="6048"
      > </a
      ><a name="6049" href="Maps.html#4237" class="Function Operator"
      >,</a
      ><a name="6050"
      > </a
      ><a name="6051" href="Maps.html#6015" class="Bound"
      >x</a
      ><a name="6052"
      > </a
      ><a name="6053" href="Maps.html#4237" class="Function Operator"
      >&#8614;</a
      ><a name="6054"
      > </a
      ><a name="6055" href="Maps.html#6024" class="Bound"
      >v</a
      ><a name="6056" class="Symbol"
      >)</a
      ><a name="6057"
      > </a
      ><a name="6058" href="Maps.html#6015" class="Bound"
      >x</a
      ><a name="6059"
      > </a
      ><a name="6060" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="6061"
      > </a
      ><a name="6062" href="Maps.html#6024" class="Bound"
      >v</a
      ><a name="6063"
      >
  </a
      ><a name="6066" href="Maps.html#5978" class="Function"
      >update-eq&#8242;</a
      ><a name="6076"
      > </a
      ><a name="6077" href="Maps.html#6077" class="Bound"
      >&#961;</a
      ><a name="6078"
      > </a
      ><a name="6079" href="Maps.html#6079" class="Bound"
      >x</a
      ><a name="6080"
      > </a
      ><a name="6081" href="Maps.html#6081" class="Bound"
      >v</a
      ><a name="6082"
      > </a
      ><a name="6083" class="Keyword"
      >with</a
      ><a name="6087"
      > </a
      ><a name="6088" href="Maps.html#6079" class="Bound"
      >x</a
      ><a name="6089"
      > </a
      ><a name="6090" href="Maps.html#2509" class="Function Operator"
      >&#8799;</a
      ><a name="6091"
      > </a
      ><a name="6092" href="Maps.html#6079" class="Bound"
      >x</a
      ><a name="6093"
      >
  </a
      ><a name="6096" class="Symbol"
      >...</a
      ><a name="6099"
      > </a
      ><a name="6100" class="Symbol"
      >|</a
      ><a name="6101"
      > </a
      ><a name="6102" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#520" class="InductiveConstructor"
      >yes</a
      ><a name="6105"
      > </a
      ><a name="6106" href="Maps.html#6106" class="Bound"
      >x&#8801;x</a
      ><a name="6109"
      > </a
      ><a name="6110" class="Symbol"
      >=</a
      ><a name="6111"
      > </a
      ><a name="6112" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="6116"
      >
  </a
      ><a name="6119" class="Symbol"
      >...</a
      ><a name="6122"
      > </a
      ><a name="6123" class="Symbol"
      >|</a
      ><a name="6124"
      > </a
      ><a name="6125" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#547" class="InductiveConstructor"
      >no</a
      ><a name="6127"
      >  </a
      ><a name="6129" href="Maps.html#6129" class="Bound"
      >x&#8802;x</a
      ><a name="6132"
      > </a
      ><a name="6133" class="Symbol"
      >=</a
      ><a name="6134"
      > </a
      ><a name="6135" href="https://agda.github.io/agda-stdlib/Data.Empty.html#348" class="Function"
      >&#8869;-elim</a
      ><a name="6141"
      > </a
      ><a name="6142" class="Symbol"
      >(</a
      ><a name="6143" href="Maps.html#6129" class="Bound"
      >x&#8802;x</a
      ><a name="6146"
      > </a
      ><a name="6147" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="6151" class="Symbol"
      >)</a
      >
{% endraw %}</pre>
</div>

#### Exercise: 2 stars, optional (update-neq)
On the other hand, if we update a map `m` at a key `x` and
then look up a _different_ key `y` in the resulting map, we get
the same result that `m` would have given:

<pre class="Agda">{% raw %}
  <a name="6400" href="Maps.html#6400" class="Function"
      >update-neq</a
      ><a name="6410"
      > </a
      ><a name="6411" class="Symbol"
      >:</a
      ><a name="6412"
      > </a
      ><a name="6413" class="Symbol"
      >&#8704;</a
      ><a name="6414"
      > </a
      ><a name="6415" class="Symbol"
      >{</a
      ><a name="6416" href="Maps.html#6416" class="Bound"
      >A</a
      ><a name="6417" class="Symbol"
      >}</a
      ><a name="6418"
      > </a
      ><a name="6419" class="Symbol"
      >(</a
      ><a name="6420" href="Maps.html#6420" class="Bound"
      >&#961;</a
      ><a name="6421"
      > </a
      ><a name="6422" class="Symbol"
      >:</a
      ><a name="6423"
      > </a
      ><a name="6424" href="Maps.html#3573" class="Function"
      >TotalMap</a
      ><a name="6432"
      > </a
      ><a name="6433" href="Maps.html#6416" class="Bound"
      >A</a
      ><a name="6434" class="Symbol"
      >)</a
      ><a name="6435"
      > </a
      ><a name="6436" class="Symbol"
      >(</a
      ><a name="6437" href="Maps.html#6437" class="Bound"
      >x</a
      ><a name="6438"
      > </a
      ><a name="6439" class="Symbol"
      >:</a
      ><a name="6440"
      > </a
      ><a name="6441" href="Maps.html#2171" class="Datatype"
      >Id</a
      ><a name="6443" class="Symbol"
      >)</a
      ><a name="6444"
      > </a
      ><a name="6445" class="Symbol"
      >(</a
      ><a name="6446" href="Maps.html#6446" class="Bound"
      >v</a
      ><a name="6447"
      > </a
      ><a name="6448" class="Symbol"
      >:</a
      ><a name="6449"
      > </a
      ><a name="6450" href="Maps.html#6416" class="Bound"
      >A</a
      ><a name="6451" class="Symbol"
      >)</a
      ><a name="6452"
      > </a
      ><a name="6453" class="Symbol"
      >(</a
      ><a name="6454" href="Maps.html#6454" class="Bound"
      >y</a
      ><a name="6455"
      > </a
      ><a name="6456" class="Symbol"
      >:</a
      ><a name="6457"
      > </a
      ><a name="6458" href="Maps.html#2171" class="Datatype"
      >Id</a
      ><a name="6460" class="Symbol"
      >)</a
      ><a name="6461"
      >
             </a
      ><a name="6475" class="Symbol"
      >&#8594;</a
      ><a name="6476"
      > </a
      ><a name="6477" href="Maps.html#6437" class="Bound"
      >x</a
      ><a name="6478"
      > </a
      ><a name="6479" href="https://agda.github.io/agda-stdlib/Relation.Binary.Core.html#4493" class="Function Operator"
      >&#8802;</a
      ><a name="6480"
      > </a
      ><a name="6481" href="Maps.html#6454" class="Bound"
      >y</a
      ><a name="6482"
      > </a
      ><a name="6483" class="Symbol"
      >&#8594;</a
      ><a name="6484"
      > </a
      ><a name="6485" class="Symbol"
      >(</a
      ><a name="6486" href="Maps.html#6420" class="Bound"
      >&#961;</a
      ><a name="6487"
      > </a
      ><a name="6488" href="Maps.html#4237" class="Function Operator"
      >,</a
      ><a name="6489"
      > </a
      ><a name="6490" href="Maps.html#6437" class="Bound"
      >x</a
      ><a name="6491"
      > </a
      ><a name="6492" href="Maps.html#4237" class="Function Operator"
      >&#8614;</a
      ><a name="6493"
      > </a
      ><a name="6494" href="Maps.html#6446" class="Bound"
      >v</a
      ><a name="6495" class="Symbol"
      >)</a
      ><a name="6496"
      > </a
      ><a name="6497" href="Maps.html#6454" class="Bound"
      >y</a
      ><a name="6498"
      > </a
      ><a name="6499" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="6500"
      > </a
      ><a name="6501" href="Maps.html#6420" class="Bound"
      >&#961;</a
      ><a name="6502"
      > </a
      ><a name="6503" href="Maps.html#6454" class="Bound"
      >y</a
      ><a name="6504"
      >
  </a
      ><a name="6507" href="Maps.html#6400" class="Function"
      >update-neq</a
      ><a name="6517"
      > </a
      ><a name="6518" href="Maps.html#6518" class="Bound"
      >&#961;</a
      ><a name="6519"
      > </a
      ><a name="6520" href="Maps.html#6520" class="Bound"
      >x</a
      ><a name="6521"
      > </a
      ><a name="6522" href="Maps.html#6522" class="Bound"
      >v</a
      ><a name="6523"
      > </a
      ><a name="6524" href="Maps.html#6524" class="Bound"
      >y</a
      ><a name="6525"
      > </a
      ><a name="6526" href="Maps.html#6526" class="Bound"
      >x&#8802;y</a
      ><a name="6529"
      > </a
      ><a name="6530" class="Keyword"
      >with</a
      ><a name="6534"
      > </a
      ><a name="6535" href="Maps.html#6520" class="Bound"
      >x</a
      ><a name="6536"
      > </a
      ><a name="6537" href="Maps.html#2509" class="Function Operator"
      >&#8799;</a
      ><a name="6538"
      > </a
      ><a name="6539" href="Maps.html#6524" class="Bound"
      >y</a
      ><a name="6540"
      >
  </a
      ><a name="6543" class="Symbol"
      >...</a
      ><a name="6546"
      > </a
      ><a name="6547" class="Symbol"
      >|</a
      ><a name="6548"
      > </a
      ><a name="6549" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#520" class="InductiveConstructor"
      >yes</a
      ><a name="6552"
      > </a
      ><a name="6553" href="Maps.html#6553" class="Bound"
      >x&#8801;y</a
      ><a name="6556"
      > </a
      ><a name="6557" class="Symbol"
      >=</a
      ><a name="6558"
      > </a
      ><a name="6559" href="https://agda.github.io/agda-stdlib/Data.Empty.html#348" class="Function"
      >&#8869;-elim</a
      ><a name="6565"
      > </a
      ><a name="6566" class="Symbol"
      >(</a
      ><a name="6567" href="Maps.html#6526" class="Bound"
      >x&#8802;y</a
      ><a name="6570"
      > </a
      ><a name="6571" href="Maps.html#6553" class="Bound"
      >x&#8801;y</a
      ><a name="6574" class="Symbol"
      >)</a
      ><a name="6575"
      >
  </a
      ><a name="6578" class="Symbol"
      >...</a
      ><a name="6581"
      > </a
      ><a name="6582" class="Symbol"
      >|</a
      ><a name="6583"
      > </a
      ><a name="6584" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#547" class="InductiveConstructor"
      >no</a
      ><a name="6586"
      >  </a
      ><a name="6588" class="Symbol"
      >_</a
      ><a name="6589"
      >   </a
      ><a name="6592" class="Symbol"
      >=</a
      ><a name="6593"
      > </a
      ><a name="6594" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      >
{% endraw %}</pre>

For the following lemmas, since maps are represented by functions, to
show two maps equal we will need to postulate extensionality.

<pre class="Agda">{% raw %}
  <a name="6759" class="Keyword"
      >postulate</a
      ><a name="6768"
      >
    </a
      ><a name="6773" href="Maps.html#6773" class="Postulate"
      >extensionality</a
      ><a name="6787"
      > </a
      ><a name="6788" class="Symbol"
      >:</a
      ><a name="6789"
      > </a
      ><a name="6790" class="Symbol"
      >&#8704;</a
      ><a name="6791"
      > </a
      ><a name="6792" class="Symbol"
      >{</a
      ><a name="6793" href="Maps.html#6793" class="Bound"
      >A</a
      ><a name="6794"
      > </a
      ><a name="6795" class="Symbol"
      >:</a
      ><a name="6796"
      > </a
      ><a name="6797" class="PrimitiveType"
      >Set</a
      ><a name="6800" class="Symbol"
      >}</a
      ><a name="6801"
      > </a
      ><a name="6802" class="Symbol"
      >{</a
      ><a name="6803" href="Maps.html#6803" class="Bound"
      >&#961;</a
      ><a name="6804"
      > </a
      ><a name="6805" href="Maps.html#6805" class="Bound"
      >&#961;&#8242;</a
      ><a name="6807"
      > </a
      ><a name="6808" class="Symbol"
      >:</a
      ><a name="6809"
      > </a
      ><a name="6810" href="Maps.html#3573" class="Function"
      >TotalMap</a
      ><a name="6818"
      > </a
      ><a name="6819" href="Maps.html#6793" class="Bound"
      >A</a
      ><a name="6820" class="Symbol"
      >}</a
      ><a name="6821"
      > </a
      ><a name="6822" class="Symbol"
      >&#8594;</a
      ><a name="6823"
      > </a
      ><a name="6824" class="Symbol"
      >(&#8704;</a
      ><a name="6826"
      > </a
      ><a name="6827" href="Maps.html#6827" class="Bound"
      >x</a
      ><a name="6828"
      > </a
      ><a name="6829" class="Symbol"
      >&#8594;</a
      ><a name="6830"
      > </a
      ><a name="6831" href="Maps.html#6803" class="Bound"
      >&#961;</a
      ><a name="6832"
      > </a
      ><a name="6833" href="Maps.html#6827" class="Bound"
      >x</a
      ><a name="6834"
      > </a
      ><a name="6835" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="6836"
      > </a
      ><a name="6837" href="Maps.html#6805" class="Bound"
      >&#961;&#8242;</a
      ><a name="6839"
      > </a
      ><a name="6840" href="Maps.html#6827" class="Bound"
      >x</a
      ><a name="6841" class="Symbol"
      >)</a
      ><a name="6842"
      > </a
      ><a name="6843" class="Symbol"
      >&#8594;</a
      ><a name="6844"
      > </a
      ><a name="6845" href="Maps.html#6803" class="Bound"
      >&#961;</a
      ><a name="6846"
      > </a
      ><a name="6847" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="6848"
      > </a
      ><a name="6849" href="Maps.html#6805" class="Bound"
      >&#961;&#8242;</a
      >
{% endraw %}</pre>

#### Exercise: 2 stars, optional (update-shadow)
If we update a map `ρ` at a key `x` with a value `v` and then
update again with the same key `x` and another value `w`, the
resulting map behaves the same (gives the same result when applied
to any key) as the simpler map obtained by performing just
the second update on `ρ`:

<pre class="Agda">{% raw %}
  <a name="7205" class="Keyword"
      >postulate</a
      ><a name="7214"
      >
    </a
      ><a name="7219" href="Maps.html#7219" class="Postulate"
      >update-shadow</a
      ><a name="7232"
      > </a
      ><a name="7233" class="Symbol"
      >:</a
      ><a name="7234"
      > </a
      ><a name="7235" class="Symbol"
      >&#8704;</a
      ><a name="7236"
      > </a
      ><a name="7237" class="Symbol"
      >{</a
      ><a name="7238" href="Maps.html#7238" class="Bound"
      >A</a
      ><a name="7239" class="Symbol"
      >}</a
      ><a name="7240"
      > </a
      ><a name="7241" class="Symbol"
      >(</a
      ><a name="7242" href="Maps.html#7242" class="Bound"
      >&#961;</a
      ><a name="7243"
      > </a
      ><a name="7244" class="Symbol"
      >:</a
      ><a name="7245"
      > </a
      ><a name="7246" href="Maps.html#3573" class="Function"
      >TotalMap</a
      ><a name="7254"
      > </a
      ><a name="7255" href="Maps.html#7238" class="Bound"
      >A</a
      ><a name="7256" class="Symbol"
      >)</a
      ><a name="7257"
      > </a
      ><a name="7258" class="Symbol"
      >(</a
      ><a name="7259" href="Maps.html#7259" class="Bound"
      >x</a
      ><a name="7260"
      > </a
      ><a name="7261" class="Symbol"
      >:</a
      ><a name="7262"
      > </a
      ><a name="7263" href="Maps.html#2171" class="Datatype"
      >Id</a
      ><a name="7265" class="Symbol"
      >)</a
      ><a name="7266"
      > </a
      ><a name="7267" class="Symbol"
      >(</a
      ><a name="7268" href="Maps.html#7268" class="Bound"
      >v</a
      ><a name="7269"
      > </a
      ><a name="7270" href="Maps.html#7270" class="Bound"
      >w</a
      ><a name="7271"
      > </a
      ><a name="7272" class="Symbol"
      >:</a
      ><a name="7273"
      > </a
      ><a name="7274" href="Maps.html#7238" class="Bound"
      >A</a
      ><a name="7275" class="Symbol"
      >)</a
      ><a name="7276"
      > 
                  </a
      ><a name="7296" class="Symbol"
      >&#8594;</a
      ><a name="7297"
      > </a
      ><a name="7298" class="Symbol"
      >(</a
      ><a name="7299" href="Maps.html#7242" class="Bound"
      >&#961;</a
      ><a name="7300"
      > </a
      ><a name="7301" href="Maps.html#4237" class="Function Operator"
      >,</a
      ><a name="7302"
      > </a
      ><a name="7303" href="Maps.html#7259" class="Bound"
      >x</a
      ><a name="7304"
      > </a
      ><a name="7305" href="Maps.html#4237" class="Function Operator"
      >&#8614;</a
      ><a name="7306"
      > </a
      ><a name="7307" href="Maps.html#7268" class="Bound"
      >v</a
      ><a name="7308"
      > </a
      ><a name="7309" href="Maps.html#4237" class="Function Operator"
      >,</a
      ><a name="7310"
      > </a
      ><a name="7311" href="Maps.html#7259" class="Bound"
      >x</a
      ><a name="7312"
      > </a
      ><a name="7313" href="Maps.html#4237" class="Function Operator"
      >&#8614;</a
      ><a name="7314"
      > </a
      ><a name="7315" href="Maps.html#7270" class="Bound"
      >w</a
      ><a name="7316" class="Symbol"
      >)</a
      ><a name="7317"
      > </a
      ><a name="7318" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="7319"
      > </a
      ><a name="7320" class="Symbol"
      >(</a
      ><a name="7321" href="Maps.html#7242" class="Bound"
      >&#961;</a
      ><a name="7322"
      > </a
      ><a name="7323" href="Maps.html#4237" class="Function Operator"
      >,</a
      ><a name="7324"
      > </a
      ><a name="7325" href="Maps.html#7259" class="Bound"
      >x</a
      ><a name="7326"
      > </a
      ><a name="7327" href="Maps.html#4237" class="Function Operator"
      >&#8614;</a
      ><a name="7328"
      > </a
      ><a name="7329" href="Maps.html#7270" class="Bound"
      >w</a
      ><a name="7330" class="Symbol"
      >)</a
      >
{% endraw %}</pre>

<div class="hidden">
<pre class="Agda">{% raw %}
  <a name="7380" href="Maps.html#7380" class="Function"
      >update-shadow&#8242;</a
      ><a name="7394"
      > </a
      ><a name="7395" class="Symbol"
      >:</a
      ><a name="7396"
      >  </a
      ><a name="7398" class="Symbol"
      >&#8704;</a
      ><a name="7399"
      > </a
      ><a name="7400" class="Symbol"
      >{</a
      ><a name="7401" href="Maps.html#7401" class="Bound"
      >A</a
      ><a name="7402" class="Symbol"
      >}</a
      ><a name="7403"
      > </a
      ><a name="7404" class="Symbol"
      >(</a
      ><a name="7405" href="Maps.html#7405" class="Bound"
      >&#961;</a
      ><a name="7406"
      > </a
      ><a name="7407" class="Symbol"
      >:</a
      ><a name="7408"
      > </a
      ><a name="7409" href="Maps.html#3573" class="Function"
      >TotalMap</a
      ><a name="7417"
      > </a
      ><a name="7418" href="Maps.html#7401" class="Bound"
      >A</a
      ><a name="7419" class="Symbol"
      >)</a
      ><a name="7420"
      > </a
      ><a name="7421" class="Symbol"
      >(</a
      ><a name="7422" href="Maps.html#7422" class="Bound"
      >x</a
      ><a name="7423"
      > </a
      ><a name="7424" class="Symbol"
      >:</a
      ><a name="7425"
      > </a
      ><a name="7426" href="Maps.html#2171" class="Datatype"
      >Id</a
      ><a name="7428" class="Symbol"
      >)</a
      ><a name="7429"
      > </a
      ><a name="7430" class="Symbol"
      >(</a
      ><a name="7431" href="Maps.html#7431" class="Bound"
      >v</a
      ><a name="7432"
      > </a
      ><a name="7433" href="Maps.html#7433" class="Bound"
      >w</a
      ><a name="7434"
      > </a
      ><a name="7435" class="Symbol"
      >:</a
      ><a name="7436"
      > </a
      ><a name="7437" href="Maps.html#7401" class="Bound"
      >A</a
      ><a name="7438" class="Symbol"
      >)</a
      ><a name="7439"
      > 
                  </a
      ><a name="7459" class="Symbol"
      >&#8594;</a
      ><a name="7460"
      > </a
      ><a name="7461" class="Symbol"
      >((</a
      ><a name="7463" href="Maps.html#7405" class="Bound"
      >&#961;</a
      ><a name="7464"
      > </a
      ><a name="7465" href="Maps.html#4237" class="Function Operator"
      >,</a
      ><a name="7466"
      > </a
      ><a name="7467" href="Maps.html#7422" class="Bound"
      >x</a
      ><a name="7468"
      > </a
      ><a name="7469" href="Maps.html#4237" class="Function Operator"
      >&#8614;</a
      ><a name="7470"
      > </a
      ><a name="7471" href="Maps.html#7431" class="Bound"
      >v</a
      ><a name="7472" class="Symbol"
      >)</a
      ><a name="7473"
      > </a
      ><a name="7474" href="Maps.html#4237" class="Function Operator"
      >,</a
      ><a name="7475"
      > </a
      ><a name="7476" href="Maps.html#7422" class="Bound"
      >x</a
      ><a name="7477"
      > </a
      ><a name="7478" href="Maps.html#4237" class="Function Operator"
      >&#8614;</a
      ><a name="7479"
      > </a
      ><a name="7480" href="Maps.html#7433" class="Bound"
      >w</a
      ><a name="7481" class="Symbol"
      >)</a
      ><a name="7482"
      > </a
      ><a name="7483" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="7484"
      > </a
      ><a name="7485" class="Symbol"
      >(</a
      ><a name="7486" href="Maps.html#7405" class="Bound"
      >&#961;</a
      ><a name="7487"
      > </a
      ><a name="7488" href="Maps.html#4237" class="Function Operator"
      >,</a
      ><a name="7489"
      > </a
      ><a name="7490" href="Maps.html#7422" class="Bound"
      >x</a
      ><a name="7491"
      > </a
      ><a name="7492" href="Maps.html#4237" class="Function Operator"
      >&#8614;</a
      ><a name="7493"
      > </a
      ><a name="7494" href="Maps.html#7433" class="Bound"
      >w</a
      ><a name="7495" class="Symbol"
      >)</a
      ><a name="7496"
      >
  </a
      ><a name="7499" href="Maps.html#7380" class="Function"
      >update-shadow&#8242;</a
      ><a name="7513"
      > </a
      ><a name="7514" href="Maps.html#7514" class="Bound"
      >&#961;</a
      ><a name="7515"
      > </a
      ><a name="7516" href="Maps.html#7516" class="Bound"
      >x</a
      ><a name="7517"
      > </a
      ><a name="7518" href="Maps.html#7518" class="Bound"
      >v</a
      ><a name="7519"
      > </a
      ><a name="7520" href="Maps.html#7520" class="Bound"
      >w</a
      ><a name="7521"
      > </a
      ><a name="7522" class="Symbol"
      >=</a
      ><a name="7523"
      > </a
      ><a name="7524" href="Maps.html#6773" class="Postulate"
      >extensionality</a
      ><a name="7538"
      > </a
      ><a name="7539" href="Maps.html#7559" class="Function"
      >lemma</a
      ><a name="7544"
      >
    </a
      ><a name="7549" class="Keyword"
      >where</a
      ><a name="7554"
      >
    </a
      ><a name="7559" href="Maps.html#7559" class="Function"
      >lemma</a
      ><a name="7564"
      > </a
      ><a name="7565" class="Symbol"
      >:</a
      ><a name="7566"
      > </a
      ><a name="7567" class="Symbol"
      >&#8704;</a
      ><a name="7568"
      > </a
      ><a name="7569" href="Maps.html#7569" class="Bound"
      >y</a
      ><a name="7570"
      > </a
      ><a name="7571" class="Symbol"
      >&#8594;</a
      ><a name="7572"
      > </a
      ><a name="7573" class="Symbol"
      >((</a
      ><a name="7575" href="Maps.html#7514" class="Bound"
      >&#961;</a
      ><a name="7576"
      > </a
      ><a name="7577" href="Maps.html#4237" class="Function Operator"
      >,</a
      ><a name="7578"
      > </a
      ><a name="7579" href="Maps.html#7516" class="Bound"
      >x</a
      ><a name="7580"
      > </a
      ><a name="7581" href="Maps.html#4237" class="Function Operator"
      >&#8614;</a
      ><a name="7582"
      > </a
      ><a name="7583" href="Maps.html#7518" class="Bound"
      >v</a
      ><a name="7584" class="Symbol"
      >)</a
      ><a name="7585"
      > </a
      ><a name="7586" href="Maps.html#4237" class="Function Operator"
      >,</a
      ><a name="7587"
      > </a
      ><a name="7588" href="Maps.html#7516" class="Bound"
      >x</a
      ><a name="7589"
      > </a
      ><a name="7590" href="Maps.html#4237" class="Function Operator"
      >&#8614;</a
      ><a name="7591"
      > </a
      ><a name="7592" href="Maps.html#7520" class="Bound"
      >w</a
      ><a name="7593" class="Symbol"
      >)</a
      ><a name="7594"
      > </a
      ><a name="7595" href="Maps.html#7569" class="Bound"
      >y</a
      ><a name="7596"
      > </a
      ><a name="7597" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="7598"
      > </a
      ><a name="7599" class="Symbol"
      >(</a
      ><a name="7600" href="Maps.html#7514" class="Bound"
      >&#961;</a
      ><a name="7601"
      > </a
      ><a name="7602" href="Maps.html#4237" class="Function Operator"
      >,</a
      ><a name="7603"
      > </a
      ><a name="7604" href="Maps.html#7516" class="Bound"
      >x</a
      ><a name="7605"
      > </a
      ><a name="7606" href="Maps.html#4237" class="Function Operator"
      >&#8614;</a
      ><a name="7607"
      > </a
      ><a name="7608" href="Maps.html#7520" class="Bound"
      >w</a
      ><a name="7609" class="Symbol"
      >)</a
      ><a name="7610"
      > </a
      ><a name="7611" href="Maps.html#7569" class="Bound"
      >y</a
      ><a name="7612"
      >
    </a
      ><a name="7617" href="Maps.html#7559" class="Function"
      >lemma</a
      ><a name="7622"
      > </a
      ><a name="7623" href="Maps.html#7623" class="Bound"
      >y</a
      ><a name="7624"
      > </a
      ><a name="7625" class="Keyword"
      >with</a
      ><a name="7629"
      > </a
      ><a name="7630" href="Maps.html#7516" class="Bound"
      >x</a
      ><a name="7631"
      > </a
      ><a name="7632" href="Maps.html#2509" class="Function Operator"
      >&#8799;</a
      ><a name="7633"
      > </a
      ><a name="7634" href="Maps.html#7623" class="Bound"
      >y</a
      ><a name="7635"
      >
    </a
      ><a name="7640" class="Symbol"
      >...</a
      ><a name="7643"
      > </a
      ><a name="7644" class="Symbol"
      >|</a
      ><a name="7645"
      > </a
      ><a name="7646" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#520" class="InductiveConstructor"
      >yes</a
      ><a name="7649"
      > </a
      ><a name="7650" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="7654"
      > </a
      ><a name="7655" class="Symbol"
      >=</a
      ><a name="7656"
      > </a
      ><a name="7657" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="7661"
      >
    </a
      ><a name="7666" class="Symbol"
      >...</a
      ><a name="7669"
      > </a
      ><a name="7670" class="Symbol"
      >|</a
      ><a name="7671"
      > </a
      ><a name="7672" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#547" class="InductiveConstructor"
      >no</a
      ><a name="7674"
      >  </a
      ><a name="7676" href="Maps.html#7676" class="Bound"
      >x&#8802;y</a
      ><a name="7679"
      >  </a
      ><a name="7681" class="Symbol"
      >=</a
      ><a name="7682"
      > </a
      ><a name="7683" href="Maps.html#6400" class="Function"
      >update-neq</a
      ><a name="7693"
      > </a
      ><a name="7694" href="Maps.html#7514" class="Bound"
      >&#961;</a
      ><a name="7695"
      > </a
      ><a name="7696" href="Maps.html#7516" class="Bound"
      >x</a
      ><a name="7697"
      > </a
      ><a name="7698" href="Maps.html#7518" class="Bound"
      >v</a
      ><a name="7699"
      > </a
      ><a name="7700" href="Maps.html#7623" class="Bound"
      >y</a
      ><a name="7701"
      > </a
      ><a name="7702" href="Maps.html#7676" class="Bound"
      >x&#8802;y</a
      >
{% endraw %}</pre>
</div>

#### Exercise: 2 stars (update-same)
Prove the following theorem, which states that if we update a map `ρ` to
assign key `x` the same value as it already has in `ρ`, then the
result is equal to `ρ`:

<pre class="Agda">{% raw %}
  <a name="7940" class="Keyword"
      >postulate</a
      ><a name="7949"
      >
    </a
      ><a name="7954" href="Maps.html#7954" class="Postulate"
      >update-same</a
      ><a name="7965"
      > </a
      ><a name="7966" class="Symbol"
      >:</a
      ><a name="7967"
      > </a
      ><a name="7968" class="Symbol"
      >&#8704;</a
      ><a name="7969"
      > </a
      ><a name="7970" class="Symbol"
      >{</a
      ><a name="7971" href="Maps.html#7971" class="Bound"
      >A</a
      ><a name="7972" class="Symbol"
      >}</a
      ><a name="7973"
      > </a
      ><a name="7974" class="Symbol"
      >(</a
      ><a name="7975" href="Maps.html#7975" class="Bound"
      >&#961;</a
      ><a name="7976"
      > </a
      ><a name="7977" class="Symbol"
      >:</a
      ><a name="7978"
      > </a
      ><a name="7979" href="Maps.html#3573" class="Function"
      >TotalMap</a
      ><a name="7987"
      > </a
      ><a name="7988" href="Maps.html#7971" class="Bound"
      >A</a
      ><a name="7989" class="Symbol"
      >)</a
      ><a name="7990"
      > </a
      ><a name="7991" class="Symbol"
      >(</a
      ><a name="7992" href="Maps.html#7992" class="Bound"
      >x</a
      ><a name="7993"
      > </a
      ><a name="7994" class="Symbol"
      >:</a
      ><a name="7995"
      > </a
      ><a name="7996" href="Maps.html#2171" class="Datatype"
      >Id</a
      ><a name="7998" class="Symbol"
      >)</a
      ><a name="7999"
      > </a
      ><a name="8000" class="Symbol"
      >&#8594;</a
      ><a name="8001"
      > </a
      ><a name="8002" class="Symbol"
      >(</a
      ><a name="8003" href="Maps.html#7975" class="Bound"
      >&#961;</a
      ><a name="8004"
      > </a
      ><a name="8005" href="Maps.html#4237" class="Function Operator"
      >,</a
      ><a name="8006"
      > </a
      ><a name="8007" href="Maps.html#7992" class="Bound"
      >x</a
      ><a name="8008"
      > </a
      ><a name="8009" href="Maps.html#4237" class="Function Operator"
      >&#8614;</a
      ><a name="8010"
      > </a
      ><a name="8011" href="Maps.html#7975" class="Bound"
      >&#961;</a
      ><a name="8012"
      > </a
      ><a name="8013" href="Maps.html#7992" class="Bound"
      >x</a
      ><a name="8014" class="Symbol"
      >)</a
      ><a name="8015"
      > </a
      ><a name="8016" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="8017"
      > </a
      ><a name="8018" href="Maps.html#7975" class="Bound"
      >&#961;</a
      >
{% endraw %}</pre>

<div class="hidden">
<pre class="Agda">{% raw %}
  <a name="8068" href="Maps.html#8068" class="Function"
      >update-same&#8242;</a
      ><a name="8080"
      > </a
      ><a name="8081" class="Symbol"
      >:</a
      ><a name="8082"
      > </a
      ><a name="8083" class="Symbol"
      >&#8704;</a
      ><a name="8084"
      > </a
      ><a name="8085" class="Symbol"
      >{</a
      ><a name="8086" href="Maps.html#8086" class="Bound"
      >A</a
      ><a name="8087" class="Symbol"
      >}</a
      ><a name="8088"
      > </a
      ><a name="8089" class="Symbol"
      >(</a
      ><a name="8090" href="Maps.html#8090" class="Bound"
      >&#961;</a
      ><a name="8091"
      > </a
      ><a name="8092" class="Symbol"
      >:</a
      ><a name="8093"
      > </a
      ><a name="8094" href="Maps.html#3573" class="Function"
      >TotalMap</a
      ><a name="8102"
      > </a
      ><a name="8103" href="Maps.html#8086" class="Bound"
      >A</a
      ><a name="8104" class="Symbol"
      >)</a
      ><a name="8105"
      > </a
      ><a name="8106" class="Symbol"
      >(</a
      ><a name="8107" href="Maps.html#8107" class="Bound"
      >x</a
      ><a name="8108"
      > </a
      ><a name="8109" class="Symbol"
      >:</a
      ><a name="8110"
      > </a
      ><a name="8111" href="Maps.html#2171" class="Datatype"
      >Id</a
      ><a name="8113" class="Symbol"
      >)</a
      ><a name="8114"
      > </a
      ><a name="8115" class="Symbol"
      >&#8594;</a
      ><a name="8116"
      > </a
      ><a name="8117" class="Symbol"
      >(</a
      ><a name="8118" href="Maps.html#8090" class="Bound"
      >&#961;</a
      ><a name="8119"
      > </a
      ><a name="8120" href="Maps.html#4237" class="Function Operator"
      >,</a
      ><a name="8121"
      > </a
      ><a name="8122" href="Maps.html#8107" class="Bound"
      >x</a
      ><a name="8123"
      > </a
      ><a name="8124" href="Maps.html#4237" class="Function Operator"
      >&#8614;</a
      ><a name="8125"
      > </a
      ><a name="8126" href="Maps.html#8090" class="Bound"
      >&#961;</a
      ><a name="8127"
      > </a
      ><a name="8128" href="Maps.html#8107" class="Bound"
      >x</a
      ><a name="8129" class="Symbol"
      >)</a
      ><a name="8130"
      > </a
      ><a name="8131" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="8132"
      > </a
      ><a name="8133" href="Maps.html#8090" class="Bound"
      >&#961;</a
      ><a name="8134"
      >
  </a
      ><a name="8137" href="Maps.html#8068" class="Function"
      >update-same&#8242;</a
      ><a name="8149"
      > </a
      ><a name="8150" href="Maps.html#8150" class="Bound"
      >&#961;</a
      ><a name="8151"
      > </a
      ><a name="8152" href="Maps.html#8152" class="Bound"
      >x</a
      ><a name="8153"
      >  </a
      ><a name="8155" class="Symbol"
      >=</a
      ><a name="8156"
      >  </a
      ><a name="8158" href="Maps.html#6773" class="Postulate"
      >extensionality</a
      ><a name="8172"
      > </a
      ><a name="8173" href="Maps.html#8193" class="Function"
      >lemma</a
      ><a name="8178"
      >
    </a
      ><a name="8183" class="Keyword"
      >where</a
      ><a name="8188"
      >
    </a
      ><a name="8193" href="Maps.html#8193" class="Function"
      >lemma</a
      ><a name="8198"
      > </a
      ><a name="8199" class="Symbol"
      >:</a
      ><a name="8200"
      > </a
      ><a name="8201" class="Symbol"
      >&#8704;</a
      ><a name="8202"
      > </a
      ><a name="8203" href="Maps.html#8203" class="Bound"
      >y</a
      ><a name="8204"
      > </a
      ><a name="8205" class="Symbol"
      >&#8594;</a
      ><a name="8206"
      > </a
      ><a name="8207" class="Symbol"
      >(</a
      ><a name="8208" href="Maps.html#8150" class="Bound"
      >&#961;</a
      ><a name="8209"
      > </a
      ><a name="8210" href="Maps.html#4237" class="Function Operator"
      >,</a
      ><a name="8211"
      > </a
      ><a name="8212" href="Maps.html#8152" class="Bound"
      >x</a
      ><a name="8213"
      > </a
      ><a name="8214" href="Maps.html#4237" class="Function Operator"
      >&#8614;</a
      ><a name="8215"
      > </a
      ><a name="8216" href="Maps.html#8150" class="Bound"
      >&#961;</a
      ><a name="8217"
      > </a
      ><a name="8218" href="Maps.html#8152" class="Bound"
      >x</a
      ><a name="8219" class="Symbol"
      >)</a
      ><a name="8220"
      > </a
      ><a name="8221" href="Maps.html#8203" class="Bound"
      >y</a
      ><a name="8222"
      > </a
      ><a name="8223" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="8224"
      > </a
      ><a name="8225" href="Maps.html#8150" class="Bound"
      >&#961;</a
      ><a name="8226"
      > </a
      ><a name="8227" href="Maps.html#8203" class="Bound"
      >y</a
      ><a name="8228"
      >
    </a
      ><a name="8233" href="Maps.html#8193" class="Function"
      >lemma</a
      ><a name="8238"
      > </a
      ><a name="8239" href="Maps.html#8239" class="Bound"
      >y</a
      ><a name="8240"
      > </a
      ><a name="8241" class="Keyword"
      >with</a
      ><a name="8245"
      > </a
      ><a name="8246" href="Maps.html#8152" class="Bound"
      >x</a
      ><a name="8247"
      > </a
      ><a name="8248" href="Maps.html#2509" class="Function Operator"
      >&#8799;</a
      ><a name="8249"
      > </a
      ><a name="8250" href="Maps.html#8239" class="Bound"
      >y</a
      ><a name="8251"
      >
    </a
      ><a name="8256" class="Symbol"
      >...</a
      ><a name="8259"
      > </a
      ><a name="8260" class="Symbol"
      >|</a
      ><a name="8261"
      > </a
      ><a name="8262" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#520" class="InductiveConstructor"
      >yes</a
      ><a name="8265"
      > </a
      ><a name="8266" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="8270"
      > </a
      ><a name="8271" class="Symbol"
      >=</a
      ><a name="8272"
      > </a
      ><a name="8273" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="8277"
      >
    </a
      ><a name="8282" class="Symbol"
      >...</a
      ><a name="8285"
      > </a
      ><a name="8286" class="Symbol"
      >|</a
      ><a name="8287"
      > </a
      ><a name="8288" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#547" class="InductiveConstructor"
      >no</a
      ><a name="8290"
      >  </a
      ><a name="8292" href="Maps.html#8292" class="Bound"
      >x&#8802;y</a
      ><a name="8295"
      >  </a
      ><a name="8297" class="Symbol"
      >=</a
      ><a name="8298"
      > </a
      ><a name="8299" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      >
{% endraw %}</pre>
</div>

#### Exercise: 3 stars, recommended (update-permute)
Prove one final property of the `update` function: If we update a map
`m` at two distinct keys, it doesn't matter in which order we do the
updates.

<pre class="Agda">{% raw %}
  <a name="8540" class="Keyword"
      >postulate</a
      ><a name="8549"
      >
    </a
      ><a name="8554" href="Maps.html#8554" class="Postulate"
      >update-permute</a
      ><a name="8568"
      > </a
      ><a name="8569" class="Symbol"
      >:</a
      ><a name="8570"
      > </a
      ><a name="8571" class="Symbol"
      >&#8704;</a
      ><a name="8572"
      > </a
      ><a name="8573" class="Symbol"
      >{</a
      ><a name="8574" href="Maps.html#8574" class="Bound"
      >A</a
      ><a name="8575" class="Symbol"
      >}</a
      ><a name="8576"
      > </a
      ><a name="8577" class="Symbol"
      >(</a
      ><a name="8578" href="Maps.html#8578" class="Bound"
      >&#961;</a
      ><a name="8579"
      > </a
      ><a name="8580" class="Symbol"
      >:</a
      ><a name="8581"
      > </a
      ><a name="8582" href="Maps.html#3573" class="Function"
      >TotalMap</a
      ><a name="8590"
      > </a
      ><a name="8591" href="Maps.html#8574" class="Bound"
      >A</a
      ><a name="8592" class="Symbol"
      >)</a
      ><a name="8593"
      > </a
      ><a name="8594" class="Symbol"
      >(</a
      ><a name="8595" href="Maps.html#8595" class="Bound"
      >x</a
      ><a name="8596"
      > </a
      ><a name="8597" class="Symbol"
      >:</a
      ><a name="8598"
      > </a
      ><a name="8599" href="Maps.html#2171" class="Datatype"
      >Id</a
      ><a name="8601" class="Symbol"
      >)</a
      ><a name="8602"
      > </a
      ><a name="8603" class="Symbol"
      >(</a
      ><a name="8604" href="Maps.html#8604" class="Bound"
      >v</a
      ><a name="8605"
      > </a
      ><a name="8606" class="Symbol"
      >:</a
      ><a name="8607"
      > </a
      ><a name="8608" href="Maps.html#8574" class="Bound"
      >A</a
      ><a name="8609" class="Symbol"
      >)</a
      ><a name="8610"
      > </a
      ><a name="8611" class="Symbol"
      >(</a
      ><a name="8612" href="Maps.html#8612" class="Bound"
      >y</a
      ><a name="8613"
      > </a
      ><a name="8614" class="Symbol"
      >:</a
      ><a name="8615"
      > </a
      ><a name="8616" href="Maps.html#2171" class="Datatype"
      >Id</a
      ><a name="8618" class="Symbol"
      >)</a
      ><a name="8619"
      > </a
      ><a name="8620" class="Symbol"
      >(</a
      ><a name="8621" href="Maps.html#8621" class="Bound"
      >w</a
      ><a name="8622"
      > </a
      ><a name="8623" class="Symbol"
      >:</a
      ><a name="8624"
      > </a
      ><a name="8625" href="Maps.html#8574" class="Bound"
      >A</a
      ><a name="8626" class="Symbol"
      >)</a
      ><a name="8627"
      >
                   </a
      ><a name="8647" class="Symbol"
      >&#8594;</a
      ><a name="8648"
      > </a
      ><a name="8649" href="Maps.html#8595" class="Bound"
      >x</a
      ><a name="8650"
      > </a
      ><a name="8651" href="https://agda.github.io/agda-stdlib/Relation.Binary.Core.html#4493" class="Function Operator"
      >&#8802;</a
      ><a name="8652"
      > </a
      ><a name="8653" href="Maps.html#8612" class="Bound"
      >y</a
      ><a name="8654"
      > </a
      ><a name="8655" class="Symbol"
      >&#8594;</a
      ><a name="8656"
      > </a
      ><a name="8657" class="Symbol"
      >(</a
      ><a name="8658" href="Maps.html#8578" class="Bound"
      >&#961;</a
      ><a name="8659"
      > </a
      ><a name="8660" href="Maps.html#4237" class="Function Operator"
      >,</a
      ><a name="8661"
      > </a
      ><a name="8662" href="Maps.html#8595" class="Bound"
      >x</a
      ><a name="8663"
      > </a
      ><a name="8664" href="Maps.html#4237" class="Function Operator"
      >&#8614;</a
      ><a name="8665"
      > </a
      ><a name="8666" href="Maps.html#8604" class="Bound"
      >v</a
      ><a name="8667"
      > </a
      ><a name="8668" href="Maps.html#4237" class="Function Operator"
      >,</a
      ><a name="8669"
      > </a
      ><a name="8670" href="Maps.html#8612" class="Bound"
      >y</a
      ><a name="8671"
      > </a
      ><a name="8672" href="Maps.html#4237" class="Function Operator"
      >&#8614;</a
      ><a name="8673"
      > </a
      ><a name="8674" href="Maps.html#8621" class="Bound"
      >w</a
      ><a name="8675" class="Symbol"
      >)</a
      ><a name="8676"
      > </a
      ><a name="8677" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="8678"
      > </a
      ><a name="8679" class="Symbol"
      >(</a
      ><a name="8680" href="Maps.html#8578" class="Bound"
      >&#961;</a
      ><a name="8681"
      > </a
      ><a name="8682" href="Maps.html#4237" class="Function Operator"
      >,</a
      ><a name="8683"
      > </a
      ><a name="8684" href="Maps.html#8612" class="Bound"
      >y</a
      ><a name="8685"
      > </a
      ><a name="8686" href="Maps.html#4237" class="Function Operator"
      >&#8614;</a
      ><a name="8687"
      > </a
      ><a name="8688" href="Maps.html#8621" class="Bound"
      >w</a
      ><a name="8689"
      > </a
      ><a name="8690" href="Maps.html#4237" class="Function Operator"
      >,</a
      ><a name="8691"
      > </a
      ><a name="8692" href="Maps.html#8595" class="Bound"
      >x</a
      ><a name="8693"
      > </a
      ><a name="8694" href="Maps.html#4237" class="Function Operator"
      >&#8614;</a
      ><a name="8695"
      > </a
      ><a name="8696" href="Maps.html#8604" class="Bound"
      >v</a
      ><a name="8697" class="Symbol"
      >)</a
      >
{% endraw %}</pre>

<div class="hidden">
<pre class="Agda">{% raw %}
  <a name="8747" href="Maps.html#8747" class="Function"
      >update-permute&#8242;</a
      ><a name="8762"
      > </a
      ><a name="8763" class="Symbol"
      >:</a
      ><a name="8764"
      > </a
      ><a name="8765" class="Symbol"
      >&#8704;</a
      ><a name="8766"
      > </a
      ><a name="8767" class="Symbol"
      >{</a
      ><a name="8768" href="Maps.html#8768" class="Bound"
      >A</a
      ><a name="8769" class="Symbol"
      >}</a
      ><a name="8770"
      > </a
      ><a name="8771" class="Symbol"
      >(</a
      ><a name="8772" href="Maps.html#8772" class="Bound"
      >&#961;</a
      ><a name="8773"
      > </a
      ><a name="8774" class="Symbol"
      >:</a
      ><a name="8775"
      > </a
      ><a name="8776" href="Maps.html#3573" class="Function"
      >TotalMap</a
      ><a name="8784"
      > </a
      ><a name="8785" href="Maps.html#8768" class="Bound"
      >A</a
      ><a name="8786" class="Symbol"
      >)</a
      ><a name="8787"
      > </a
      ><a name="8788" class="Symbol"
      >(</a
      ><a name="8789" href="Maps.html#8789" class="Bound"
      >x</a
      ><a name="8790"
      > </a
      ><a name="8791" class="Symbol"
      >:</a
      ><a name="8792"
      > </a
      ><a name="8793" href="Maps.html#2171" class="Datatype"
      >Id</a
      ><a name="8795" class="Symbol"
      >)</a
      ><a name="8796"
      > </a
      ><a name="8797" class="Symbol"
      >(</a
      ><a name="8798" href="Maps.html#8798" class="Bound"
      >v</a
      ><a name="8799"
      > </a
      ><a name="8800" class="Symbol"
      >:</a
      ><a name="8801"
      > </a
      ><a name="8802" href="Maps.html#8768" class="Bound"
      >A</a
      ><a name="8803" class="Symbol"
      >)</a
      ><a name="8804"
      > </a
      ><a name="8805" class="Symbol"
      >(</a
      ><a name="8806" href="Maps.html#8806" class="Bound"
      >y</a
      ><a name="8807"
      > </a
      ><a name="8808" class="Symbol"
      >:</a
      ><a name="8809"
      > </a
      ><a name="8810" href="Maps.html#2171" class="Datatype"
      >Id</a
      ><a name="8812" class="Symbol"
      >)</a
      ><a name="8813"
      > </a
      ><a name="8814" class="Symbol"
      >(</a
      ><a name="8815" href="Maps.html#8815" class="Bound"
      >w</a
      ><a name="8816"
      > </a
      ><a name="8817" class="Symbol"
      >:</a
      ><a name="8818"
      > </a
      ><a name="8819" href="Maps.html#8768" class="Bound"
      >A</a
      ><a name="8820" class="Symbol"
      >)</a
      ><a name="8821"
      >
                   </a
      ><a name="8841" class="Symbol"
      >&#8594;</a
      ><a name="8842"
      > </a
      ><a name="8843" href="Maps.html#8789" class="Bound"
      >x</a
      ><a name="8844"
      > </a
      ><a name="8845" href="https://agda.github.io/agda-stdlib/Relation.Binary.Core.html#4493" class="Function Operator"
      >&#8802;</a
      ><a name="8846"
      > </a
      ><a name="8847" href="Maps.html#8806" class="Bound"
      >y</a
      ><a name="8848"
      > </a
      ><a name="8849" class="Symbol"
      >&#8594;</a
      ><a name="8850"
      > </a
      ><a name="8851" class="Symbol"
      >(</a
      ><a name="8852" href="Maps.html#8772" class="Bound"
      >&#961;</a
      ><a name="8853"
      > </a
      ><a name="8854" href="Maps.html#4237" class="Function Operator"
      >,</a
      ><a name="8855"
      > </a
      ><a name="8856" href="Maps.html#8789" class="Bound"
      >x</a
      ><a name="8857"
      > </a
      ><a name="8858" href="Maps.html#4237" class="Function Operator"
      >&#8614;</a
      ><a name="8859"
      > </a
      ><a name="8860" href="Maps.html#8798" class="Bound"
      >v</a
      ><a name="8861"
      > </a
      ><a name="8862" href="Maps.html#4237" class="Function Operator"
      >,</a
      ><a name="8863"
      > </a
      ><a name="8864" href="Maps.html#8806" class="Bound"
      >y</a
      ><a name="8865"
      > </a
      ><a name="8866" href="Maps.html#4237" class="Function Operator"
      >&#8614;</a
      ><a name="8867"
      > </a
      ><a name="8868" href="Maps.html#8815" class="Bound"
      >w</a
      ><a name="8869" class="Symbol"
      >)</a
      ><a name="8870"
      > </a
      ><a name="8871" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="8872"
      > </a
      ><a name="8873" class="Symbol"
      >(</a
      ><a name="8874" href="Maps.html#8772" class="Bound"
      >&#961;</a
      ><a name="8875"
      > </a
      ><a name="8876" href="Maps.html#4237" class="Function Operator"
      >,</a
      ><a name="8877"
      > </a
      ><a name="8878" href="Maps.html#8806" class="Bound"
      >y</a
      ><a name="8879"
      > </a
      ><a name="8880" href="Maps.html#4237" class="Function Operator"
      >&#8614;</a
      ><a name="8881"
      > </a
      ><a name="8882" href="Maps.html#8815" class="Bound"
      >w</a
      ><a name="8883"
      > </a
      ><a name="8884" href="Maps.html#4237" class="Function Operator"
      >,</a
      ><a name="8885"
      > </a
      ><a name="8886" href="Maps.html#8789" class="Bound"
      >x</a
      ><a name="8887"
      > </a
      ><a name="8888" href="Maps.html#4237" class="Function Operator"
      >&#8614;</a
      ><a name="8889"
      > </a
      ><a name="8890" href="Maps.html#8798" class="Bound"
      >v</a
      ><a name="8891" class="Symbol"
      >)</a
      ><a name="8892"
      >
  </a
      ><a name="8895" href="Maps.html#8747" class="Function"
      >update-permute&#8242;</a
      ><a name="8910"
      > </a
      ><a name="8911" class="Symbol"
      >{</a
      ><a name="8912" href="Maps.html#8912" class="Bound"
      >A</a
      ><a name="8913" class="Symbol"
      >}</a
      ><a name="8914"
      > </a
      ><a name="8915" href="Maps.html#8915" class="Bound"
      >&#961;</a
      ><a name="8916"
      > </a
      ><a name="8917" href="Maps.html#8917" class="Bound"
      >x</a
      ><a name="8918"
      > </a
      ><a name="8919" href="Maps.html#8919" class="Bound"
      >v</a
      ><a name="8920"
      > </a
      ><a name="8921" href="Maps.html#8921" class="Bound"
      >y</a
      ><a name="8922"
      > </a
      ><a name="8923" href="Maps.html#8923" class="Bound"
      >w</a
      ><a name="8924"
      > </a
      ><a name="8925" href="Maps.html#8925" class="Bound"
      >x&#8802;y</a
      ><a name="8928"
      >  </a
      ><a name="8930" class="Symbol"
      >=</a
      ><a name="8931"
      >  </a
      ><a name="8933" href="Maps.html#6773" class="Postulate"
      >extensionality</a
      ><a name="8947"
      > </a
      ><a name="8948" href="Maps.html#8968" class="Function"
      >lemma</a
      ><a name="8953"
      >
    </a
      ><a name="8958" class="Keyword"
      >where</a
      ><a name="8963"
      >
    </a
      ><a name="8968" href="Maps.html#8968" class="Function"
      >lemma</a
      ><a name="8973"
      > </a
      ><a name="8974" class="Symbol"
      >:</a
      ><a name="8975"
      > </a
      ><a name="8976" class="Symbol"
      >&#8704;</a
      ><a name="8977"
      > </a
      ><a name="8978" href="Maps.html#8978" class="Bound"
      >z</a
      ><a name="8979"
      > </a
      ><a name="8980" class="Symbol"
      >&#8594;</a
      ><a name="8981"
      > </a
      ><a name="8982" class="Symbol"
      >(</a
      ><a name="8983" href="Maps.html#8915" class="Bound"
      >&#961;</a
      ><a name="8984"
      > </a
      ><a name="8985" href="Maps.html#4237" class="Function Operator"
      >,</a
      ><a name="8986"
      > </a
      ><a name="8987" href="Maps.html#8917" class="Bound"
      >x</a
      ><a name="8988"
      > </a
      ><a name="8989" href="Maps.html#4237" class="Function Operator"
      >&#8614;</a
      ><a name="8990"
      > </a
      ><a name="8991" href="Maps.html#8919" class="Bound"
      >v</a
      ><a name="8992"
      > </a
      ><a name="8993" href="Maps.html#4237" class="Function Operator"
      >,</a
      ><a name="8994"
      > </a
      ><a name="8995" href="Maps.html#8921" class="Bound"
      >y</a
      ><a name="8996"
      > </a
      ><a name="8997" href="Maps.html#4237" class="Function Operator"
      >&#8614;</a
      ><a name="8998"
      > </a
      ><a name="8999" href="Maps.html#8923" class="Bound"
      >w</a
      ><a name="9000" class="Symbol"
      >)</a
      ><a name="9001"
      > </a
      ><a name="9002" href="Maps.html#8978" class="Bound"
      >z</a
      ><a name="9003"
      > </a
      ><a name="9004" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="9005"
      > </a
      ><a name="9006" class="Symbol"
      >(</a
      ><a name="9007" href="Maps.html#8915" class="Bound"
      >&#961;</a
      ><a name="9008"
      > </a
      ><a name="9009" href="Maps.html#4237" class="Function Operator"
      >,</a
      ><a name="9010"
      > </a
      ><a name="9011" href="Maps.html#8921" class="Bound"
      >y</a
      ><a name="9012"
      > </a
      ><a name="9013" href="Maps.html#4237" class="Function Operator"
      >&#8614;</a
      ><a name="9014"
      > </a
      ><a name="9015" href="Maps.html#8923" class="Bound"
      >w</a
      ><a name="9016"
      > </a
      ><a name="9017" href="Maps.html#4237" class="Function Operator"
      >,</a
      ><a name="9018"
      > </a
      ><a name="9019" href="Maps.html#8917" class="Bound"
      >x</a
      ><a name="9020"
      > </a
      ><a name="9021" href="Maps.html#4237" class="Function Operator"
      >&#8614;</a
      ><a name="9022"
      > </a
      ><a name="9023" href="Maps.html#8919" class="Bound"
      >v</a
      ><a name="9024" class="Symbol"
      >)</a
      ><a name="9025"
      > </a
      ><a name="9026" href="Maps.html#8978" class="Bound"
      >z</a
      ><a name="9027"
      >
    </a
      ><a name="9032" href="Maps.html#8968" class="Function"
      >lemma</a
      ><a name="9037"
      > </a
      ><a name="9038" href="Maps.html#9038" class="Bound"
      >z</a
      ><a name="9039"
      > </a
      ><a name="9040" class="Keyword"
      >with</a
      ><a name="9044"
      > </a
      ><a name="9045" href="Maps.html#8917" class="Bound"
      >x</a
      ><a name="9046"
      > </a
      ><a name="9047" href="Maps.html#2509" class="Function Operator"
      >&#8799;</a
      ><a name="9048"
      > </a
      ><a name="9049" href="Maps.html#9038" class="Bound"
      >z</a
      ><a name="9050"
      > </a
      ><a name="9051" class="Symbol"
      >|</a
      ><a name="9052"
      > </a
      ><a name="9053" href="Maps.html#8921" class="Bound"
      >y</a
      ><a name="9054"
      > </a
      ><a name="9055" href="Maps.html#2509" class="Function Operator"
      >&#8799;</a
      ><a name="9056"
      > </a
      ><a name="9057" href="Maps.html#9038" class="Bound"
      >z</a
      ><a name="9058"
      >
    </a
      ><a name="9063" class="Symbol"
      >...</a
      ><a name="9066"
      > </a
      ><a name="9067" class="Symbol"
      >|</a
      ><a name="9068"
      > </a
      ><a name="9069" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#520" class="InductiveConstructor"
      >yes</a
      ><a name="9072"
      > </a
      ><a name="9073" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="9077"
      > </a
      ><a name="9078" class="Symbol"
      >|</a
      ><a name="9079"
      > </a
      ><a name="9080" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#520" class="InductiveConstructor"
      >yes</a
      ><a name="9083"
      > </a
      ><a name="9084" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="9088"
      >  </a
      ><a name="9090" class="Symbol"
      >=</a
      ><a name="9091"
      >  </a
      ><a name="9093" href="https://agda.github.io/agda-stdlib/Data.Empty.html#348" class="Function"
      >&#8869;-elim</a
      ><a name="9099"
      > </a
      ><a name="9100" class="Symbol"
      >(</a
      ><a name="9101" href="Maps.html#8925" class="Bound"
      >x&#8802;y</a
      ><a name="9104"
      > </a
      ><a name="9105" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="9109" class="Symbol"
      >)</a
      ><a name="9110"
      >
    </a
      ><a name="9115" class="Symbol"
      >...</a
      ><a name="9118"
      > </a
      ><a name="9119" class="Symbol"
      >|</a
      ><a name="9120"
      > </a
      ><a name="9121" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#547" class="InductiveConstructor"
      >no</a
      ><a name="9123"
      >  </a
      ><a name="9125" href="Maps.html#9125" class="Bound"
      >x&#8802;z</a
      ><a name="9128"
      >  </a
      ><a name="9130" class="Symbol"
      >|</a
      ><a name="9131"
      > </a
      ><a name="9132" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#520" class="InductiveConstructor"
      >yes</a
      ><a name="9135"
      > </a
      ><a name="9136" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="9140"
      >  </a
      ><a name="9142" class="Symbol"
      >=</a
      ><a name="9143"
      >  </a
      ><a name="9145" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.Core.html#565" class="Function"
      >sym</a
      ><a name="9148"
      > </a
      ><a name="9149" class="Symbol"
      >(</a
      ><a name="9150" href="Maps.html#5978" class="Function"
      >update-eq&#8242;</a
      ><a name="9160"
      > </a
      ><a name="9161" href="Maps.html#8915" class="Bound"
      >&#961;</a
      ><a name="9162"
      > </a
      ><a name="9163" href="Maps.html#9038" class="Bound"
      >z</a
      ><a name="9164"
      > </a
      ><a name="9165" href="Maps.html#8923" class="Bound"
      >w</a
      ><a name="9166" class="Symbol"
      >)</a
      ><a name="9167"
      >
    </a
      ><a name="9172" class="Symbol"
      >...</a
      ><a name="9175"
      > </a
      ><a name="9176" class="Symbol"
      >|</a
      ><a name="9177"
      > </a
      ><a name="9178" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#520" class="InductiveConstructor"
      >yes</a
      ><a name="9181"
      > </a
      ><a name="9182" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="9186"
      > </a
      ><a name="9187" class="Symbol"
      >|</a
      ><a name="9188"
      > </a
      ><a name="9189" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#547" class="InductiveConstructor"
      >no</a
      ><a name="9191"
      >  </a
      ><a name="9193" href="Maps.html#9193" class="Bound"
      >y&#8802;z</a
      ><a name="9196"
      >   </a
      ><a name="9199" class="Symbol"
      >=</a
      ><a name="9200"
      >  </a
      ><a name="9202" href="Maps.html#5978" class="Function"
      >update-eq&#8242;</a
      ><a name="9212"
      > </a
      ><a name="9213" href="Maps.html#8915" class="Bound"
      >&#961;</a
      ><a name="9214"
      > </a
      ><a name="9215" href="Maps.html#9038" class="Bound"
      >z</a
      ><a name="9216"
      > </a
      ><a name="9217" href="Maps.html#8919" class="Bound"
      >v</a
      ><a name="9218"
      >
    </a
      ><a name="9223" class="Symbol"
      >...</a
      ><a name="9226"
      > </a
      ><a name="9227" class="Symbol"
      >|</a
      ><a name="9228"
      > </a
      ><a name="9229" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#547" class="InductiveConstructor"
      >no</a
      ><a name="9231"
      >  </a
      ><a name="9233" href="Maps.html#9233" class="Bound"
      >x&#8802;z</a
      ><a name="9236"
      >  </a
      ><a name="9238" class="Symbol"
      >|</a
      ><a name="9239"
      > </a
      ><a name="9240" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#547" class="InductiveConstructor"
      >no</a
      ><a name="9242"
      >  </a
      ><a name="9244" href="Maps.html#9244" class="Bound"
      >y&#8802;z</a
      ><a name="9247"
      >   </a
      ><a name="9250" class="Symbol"
      >=</a
      ><a name="9251"
      >  </a
      ><a name="9253" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.Core.html#632" class="Function"
      >trans</a
      ><a name="9258"
      > </a
      ><a name="9259" class="Symbol"
      >(</a
      ><a name="9260" href="Maps.html#6400" class="Function"
      >update-neq</a
      ><a name="9270"
      > </a
      ><a name="9271" href="Maps.html#8915" class="Bound"
      >&#961;</a
      ><a name="9272"
      > </a
      ><a name="9273" href="Maps.html#8917" class="Bound"
      >x</a
      ><a name="9274"
      > </a
      ><a name="9275" href="Maps.html#8919" class="Bound"
      >v</a
      ><a name="9276"
      > </a
      ><a name="9277" href="Maps.html#9038" class="Bound"
      >z</a
      ><a name="9278"
      > </a
      ><a name="9279" href="Maps.html#9233" class="Bound"
      >x&#8802;z</a
      ><a name="9282" class="Symbol"
      >)</a
      ><a name="9283"
      > </a
      ><a name="9284" class="Symbol"
      >(</a
      ><a name="9285" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.Core.html#565" class="Function"
      >sym</a
      ><a name="9288"
      > </a
      ><a name="9289" class="Symbol"
      >(</a
      ><a name="9290" href="Maps.html#6400" class="Function"
      >update-neq</a
      ><a name="9300"
      > </a
      ><a name="9301" href="Maps.html#8915" class="Bound"
      >&#961;</a
      ><a name="9302"
      > </a
      ><a name="9303" href="Maps.html#8921" class="Bound"
      >y</a
      ><a name="9304"
      > </a
      ><a name="9305" href="Maps.html#8923" class="Bound"
      >w</a
      ><a name="9306"
      > </a
      ><a name="9307" href="Maps.html#9038" class="Bound"
      >z</a
      ><a name="9308"
      > </a
      ><a name="9309" href="Maps.html#9244" class="Bound"
      >y&#8802;z</a
      ><a name="9312" class="Symbol"
      >))</a
      >
{% endraw %}</pre>

And a slightly different version of the same proof.

<pre class="Agda">{% raw %}
  <a name="9399" href="Maps.html#9399" class="Function"
      >update-permute&#8242;&#8242;</a
      ><a name="9415"
      > </a
      ><a name="9416" class="Symbol"
      >:</a
      ><a name="9417"
      > </a
      ><a name="9418" class="Symbol"
      >&#8704;</a
      ><a name="9419"
      > </a
      ><a name="9420" class="Symbol"
      >{</a
      ><a name="9421" href="Maps.html#9421" class="Bound"
      >A</a
      ><a name="9422" class="Symbol"
      >}</a
      ><a name="9423"
      > </a
      ><a name="9424" class="Symbol"
      >(</a
      ><a name="9425" href="Maps.html#9425" class="Bound"
      >&#961;</a
      ><a name="9426"
      > </a
      ><a name="9427" class="Symbol"
      >:</a
      ><a name="9428"
      > </a
      ><a name="9429" href="Maps.html#3573" class="Function"
      >TotalMap</a
      ><a name="9437"
      > </a
      ><a name="9438" href="Maps.html#9421" class="Bound"
      >A</a
      ><a name="9439" class="Symbol"
      >)</a
      ><a name="9440"
      > </a
      ><a name="9441" class="Symbol"
      >(</a
      ><a name="9442" href="Maps.html#9442" class="Bound"
      >x</a
      ><a name="9443"
      > </a
      ><a name="9444" class="Symbol"
      >:</a
      ><a name="9445"
      > </a
      ><a name="9446" href="Maps.html#2171" class="Datatype"
      >Id</a
      ><a name="9448" class="Symbol"
      >)</a
      ><a name="9449"
      > </a
      ><a name="9450" class="Symbol"
      >(</a
      ><a name="9451" href="Maps.html#9451" class="Bound"
      >v</a
      ><a name="9452"
      > </a
      ><a name="9453" class="Symbol"
      >:</a
      ><a name="9454"
      > </a
      ><a name="9455" href="Maps.html#9421" class="Bound"
      >A</a
      ><a name="9456" class="Symbol"
      >)</a
      ><a name="9457"
      > </a
      ><a name="9458" class="Symbol"
      >(</a
      ><a name="9459" href="Maps.html#9459" class="Bound"
      >y</a
      ><a name="9460"
      > </a
      ><a name="9461" class="Symbol"
      >:</a
      ><a name="9462"
      > </a
      ><a name="9463" href="Maps.html#2171" class="Datatype"
      >Id</a
      ><a name="9465" class="Symbol"
      >)</a
      ><a name="9466"
      > </a
      ><a name="9467" class="Symbol"
      >(</a
      ><a name="9468" href="Maps.html#9468" class="Bound"
      >w</a
      ><a name="9469"
      > </a
      ><a name="9470" class="Symbol"
      >:</a
      ><a name="9471"
      > </a
      ><a name="9472" href="Maps.html#9421" class="Bound"
      >A</a
      ><a name="9473" class="Symbol"
      >)</a
      ><a name="9474"
      > </a
      ><a name="9475" class="Symbol"
      >(</a
      ><a name="9476" href="Maps.html#9476" class="Bound"
      >z</a
      ><a name="9477"
      > </a
      ><a name="9478" class="Symbol"
      >:</a
      ><a name="9479"
      > </a
      ><a name="9480" href="Maps.html#2171" class="Datatype"
      >Id</a
      ><a name="9482" class="Symbol"
      >)</a
      ><a name="9483"
      >
                   </a
      ><a name="9503" class="Symbol"
      >&#8594;</a
      ><a name="9504"
      > </a
      ><a name="9505" href="Maps.html#9442" class="Bound"
      >x</a
      ><a name="9506"
      > </a
      ><a name="9507" href="https://agda.github.io/agda-stdlib/Relation.Binary.Core.html#4493" class="Function Operator"
      >&#8802;</a
      ><a name="9508"
      > </a
      ><a name="9509" href="Maps.html#9459" class="Bound"
      >y</a
      ><a name="9510"
      > </a
      ><a name="9511" class="Symbol"
      >&#8594;</a
      ><a name="9512"
      > </a
      ><a name="9513" class="Symbol"
      >(</a
      ><a name="9514" href="Maps.html#9425" class="Bound"
      >&#961;</a
      ><a name="9515"
      > </a
      ><a name="9516" href="Maps.html#4237" class="Function Operator"
      >,</a
      ><a name="9517"
      > </a
      ><a name="9518" href="Maps.html#9442" class="Bound"
      >x</a
      ><a name="9519"
      > </a
      ><a name="9520" href="Maps.html#4237" class="Function Operator"
      >&#8614;</a
      ><a name="9521"
      > </a
      ><a name="9522" href="Maps.html#9451" class="Bound"
      >v</a
      ><a name="9523"
      > </a
      ><a name="9524" href="Maps.html#4237" class="Function Operator"
      >,</a
      ><a name="9525"
      > </a
      ><a name="9526" href="Maps.html#9459" class="Bound"
      >y</a
      ><a name="9527"
      > </a
      ><a name="9528" href="Maps.html#4237" class="Function Operator"
      >&#8614;</a
      ><a name="9529"
      > </a
      ><a name="9530" href="Maps.html#9468" class="Bound"
      >w</a
      ><a name="9531" class="Symbol"
      >)</a
      ><a name="9532"
      > </a
      ><a name="9533" href="Maps.html#9476" class="Bound"
      >z</a
      ><a name="9534"
      > </a
      ><a name="9535" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="9536"
      > </a
      ><a name="9537" class="Symbol"
      >(</a
      ><a name="9538" href="Maps.html#9425" class="Bound"
      >&#961;</a
      ><a name="9539"
      > </a
      ><a name="9540" href="Maps.html#4237" class="Function Operator"
      >,</a
      ><a name="9541"
      > </a
      ><a name="9542" href="Maps.html#9459" class="Bound"
      >y</a
      ><a name="9543"
      > </a
      ><a name="9544" href="Maps.html#4237" class="Function Operator"
      >&#8614;</a
      ><a name="9545"
      > </a
      ><a name="9546" href="Maps.html#9468" class="Bound"
      >w</a
      ><a name="9547"
      > </a
      ><a name="9548" href="Maps.html#4237" class="Function Operator"
      >,</a
      ><a name="9549"
      > </a
      ><a name="9550" href="Maps.html#9442" class="Bound"
      >x</a
      ><a name="9551"
      > </a
      ><a name="9552" href="Maps.html#4237" class="Function Operator"
      >&#8614;</a
      ><a name="9553"
      > </a
      ><a name="9554" href="Maps.html#9451" class="Bound"
      >v</a
      ><a name="9555" class="Symbol"
      >)</a
      ><a name="9556"
      > </a
      ><a name="9557" href="Maps.html#9476" class="Bound"
      >z</a
      ><a name="9558"
      >
  </a
      ><a name="9561" href="Maps.html#9399" class="Function"
      >update-permute&#8242;&#8242;</a
      ><a name="9577"
      > </a
      ><a name="9578" class="Symbol"
      >{</a
      ><a name="9579" href="Maps.html#9579" class="Bound"
      >A</a
      ><a name="9580" class="Symbol"
      >}</a
      ><a name="9581"
      > </a
      ><a name="9582" href="Maps.html#9582" class="Bound"
      >&#961;</a
      ><a name="9583"
      > </a
      ><a name="9584" href="Maps.html#9584" class="Bound"
      >x</a
      ><a name="9585"
      > </a
      ><a name="9586" href="Maps.html#9586" class="Bound"
      >v</a
      ><a name="9587"
      > </a
      ><a name="9588" href="Maps.html#9588" class="Bound"
      >y</a
      ><a name="9589"
      > </a
      ><a name="9590" href="Maps.html#9590" class="Bound"
      >w</a
      ><a name="9591"
      > </a
      ><a name="9592" href="Maps.html#9592" class="Bound"
      >z</a
      ><a name="9593"
      > </a
      ><a name="9594" href="Maps.html#9594" class="Bound"
      >x&#8802;y</a
      ><a name="9597"
      > </a
      ><a name="9598" class="Keyword"
      >with</a
      ><a name="9602"
      > </a
      ><a name="9603" href="Maps.html#9584" class="Bound"
      >x</a
      ><a name="9604"
      > </a
      ><a name="9605" href="Maps.html#2509" class="Function Operator"
      >&#8799;</a
      ><a name="9606"
      > </a
      ><a name="9607" href="Maps.html#9592" class="Bound"
      >z</a
      ><a name="9608"
      > </a
      ><a name="9609" class="Symbol"
      >|</a
      ><a name="9610"
      > </a
      ><a name="9611" href="Maps.html#9588" class="Bound"
      >y</a
      ><a name="9612"
      > </a
      ><a name="9613" href="Maps.html#2509" class="Function Operator"
      >&#8799;</a
      ><a name="9614"
      > </a
      ><a name="9615" href="Maps.html#9592" class="Bound"
      >z</a
      ><a name="9616"
      >
  </a
      ><a name="9619" class="Symbol"
      >...</a
      ><a name="9622"
      > </a
      ><a name="9623" class="Symbol"
      >|</a
      ><a name="9624"
      > </a
      ><a name="9625" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#520" class="InductiveConstructor"
      >yes</a
      ><a name="9628"
      > </a
      ><a name="9629" href="Maps.html#9629" class="Bound"
      >x&#8801;z</a
      ><a name="9632"
      > </a
      ><a name="9633" class="Symbol"
      >|</a
      ><a name="9634"
      > </a
      ><a name="9635" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#520" class="InductiveConstructor"
      >yes</a
      ><a name="9638"
      > </a
      ><a name="9639" href="Maps.html#9639" class="Bound"
      >y&#8801;z</a
      ><a name="9642"
      > </a
      ><a name="9643" class="Symbol"
      >=</a
      ><a name="9644"
      > </a
      ><a name="9645" href="https://agda.github.io/agda-stdlib/Data.Empty.html#348" class="Function"
      >&#8869;-elim</a
      ><a name="9651"
      > </a
      ><a name="9652" class="Symbol"
      >(</a
      ><a name="9653" href="Maps.html#9594" class="Bound"
      >x&#8802;y</a
      ><a name="9656"
      > </a
      ><a name="9657" class="Symbol"
      >(</a
      ><a name="9658" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.Core.html#632" class="Function"
      >trans</a
      ><a name="9663"
      > </a
      ><a name="9664" href="Maps.html#9629" class="Bound"
      >x&#8801;z</a
      ><a name="9667"
      > </a
      ><a name="9668" class="Symbol"
      >(</a
      ><a name="9669" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.Core.html#565" class="Function"
      >sym</a
      ><a name="9672"
      > </a
      ><a name="9673" href="Maps.html#9639" class="Bound"
      >y&#8801;z</a
      ><a name="9676" class="Symbol"
      >)))</a
      ><a name="9679"
      >
  </a
      ><a name="9682" class="Symbol"
      >...</a
      ><a name="9685"
      > </a
      ><a name="9686" class="Symbol"
      >|</a
      ><a name="9687"
      > </a
      ><a name="9688" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#547" class="InductiveConstructor"
      >no</a
      ><a name="9690"
      >  </a
      ><a name="9692" href="Maps.html#9692" class="Bound"
      >x&#8802;z</a
      ><a name="9695"
      > </a
      ><a name="9696" class="Symbol"
      >|</a
      ><a name="9697"
      > </a
      ><a name="9698" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#520" class="InductiveConstructor"
      >yes</a
      ><a name="9701"
      > </a
      ><a name="9702" href="Maps.html#9702" class="Bound"
      >y&#8801;z</a
      ><a name="9705"
      > </a
      ><a name="9706" class="Keyword"
      >rewrite</a
      ><a name="9713"
      > </a
      ><a name="9714" href="Maps.html#9702" class="Bound"
      >y&#8801;z</a
      ><a name="9717"
      >  </a
      ><a name="9719" class="Symbol"
      >=</a
      ><a name="9720"
      >  </a
      ><a name="9722" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.Core.html#565" class="Function"
      >sym</a
      ><a name="9725"
      > </a
      ><a name="9726" class="Symbol"
      >(</a
      ><a name="9727" href="Maps.html#5978" class="Function"
      >update-eq&#8242;</a
      ><a name="9737"
      > </a
      ><a name="9738" href="Maps.html#9582" class="Bound"
      >&#961;</a
      ><a name="9739"
      > </a
      ><a name="9740" href="Maps.html#9592" class="Bound"
      >z</a
      ><a name="9741"
      > </a
      ><a name="9742" href="Maps.html#9590" class="Bound"
      >w</a
      ><a name="9743" class="Symbol"
      >)</a
      ><a name="9744"
      >  
  </a
      ><a name="9749" class="Symbol"
      >...</a
      ><a name="9752"
      > </a
      ><a name="9753" class="Symbol"
      >|</a
      ><a name="9754"
      > </a
      ><a name="9755" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#520" class="InductiveConstructor"
      >yes</a
      ><a name="9758"
      > </a
      ><a name="9759" href="Maps.html#9759" class="Bound"
      >x&#8801;z</a
      ><a name="9762"
      > </a
      ><a name="9763" class="Symbol"
      >|</a
      ><a name="9764"
      > </a
      ><a name="9765" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#547" class="InductiveConstructor"
      >no</a
      ><a name="9767"
      >  </a
      ><a name="9769" href="Maps.html#9769" class="Bound"
      >y&#8802;z</a
      ><a name="9772"
      > </a
      ><a name="9773" class="Keyword"
      >rewrite</a
      ><a name="9780"
      > </a
      ><a name="9781" href="Maps.html#9759" class="Bound"
      >x&#8801;z</a
      ><a name="9784"
      >  </a
      ><a name="9786" class="Symbol"
      >=</a
      ><a name="9787"
      >  </a
      ><a name="9789" href="Maps.html#5978" class="Function"
      >update-eq&#8242;</a
      ><a name="9799"
      > </a
      ><a name="9800" href="Maps.html#9582" class="Bound"
      >&#961;</a
      ><a name="9801"
      > </a
      ><a name="9802" href="Maps.html#9592" class="Bound"
      >z</a
      ><a name="9803"
      > </a
      ><a name="9804" href="Maps.html#9586" class="Bound"
      >v</a
      ><a name="9805"
      >
  </a
      ><a name="9808" class="Symbol"
      >...</a
      ><a name="9811"
      > </a
      ><a name="9812" class="Symbol"
      >|</a
      ><a name="9813"
      > </a
      ><a name="9814" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#547" class="InductiveConstructor"
      >no</a
      ><a name="9816"
      >  </a
      ><a name="9818" href="Maps.html#9818" class="Bound"
      >x&#8802;z</a
      ><a name="9821"
      > </a
      ><a name="9822" class="Symbol"
      >|</a
      ><a name="9823"
      > </a
      ><a name="9824" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#547" class="InductiveConstructor"
      >no</a
      ><a name="9826"
      >  </a
      ><a name="9828" href="Maps.html#9828" class="Bound"
      >y&#8802;z</a
      ><a name="9831"
      >  </a
      ><a name="9833" class="Symbol"
      >=</a
      ><a name="9834"
      >  </a
      ><a name="9836" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.Core.html#632" class="Function"
      >trans</a
      ><a name="9841"
      > </a
      ><a name="9842" class="Symbol"
      >(</a
      ><a name="9843" href="Maps.html#6400" class="Function"
      >update-neq</a
      ><a name="9853"
      > </a
      ><a name="9854" href="Maps.html#9582" class="Bound"
      >&#961;</a
      ><a name="9855"
      > </a
      ><a name="9856" href="Maps.html#9584" class="Bound"
      >x</a
      ><a name="9857"
      > </a
      ><a name="9858" href="Maps.html#9586" class="Bound"
      >v</a
      ><a name="9859"
      > </a
      ><a name="9860" href="Maps.html#9592" class="Bound"
      >z</a
      ><a name="9861"
      > </a
      ><a name="9862" href="Maps.html#9818" class="Bound"
      >x&#8802;z</a
      ><a name="9865" class="Symbol"
      >)</a
      ><a name="9866"
      > </a
      ><a name="9867" class="Symbol"
      >(</a
      ><a name="9868" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.Core.html#565" class="Function"
      >sym</a
      ><a name="9871"
      > </a
      ><a name="9872" class="Symbol"
      >(</a
      ><a name="9873" href="Maps.html#6400" class="Function"
      >update-neq</a
      ><a name="9883"
      > </a
      ><a name="9884" href="Maps.html#9582" class="Bound"
      >&#961;</a
      ><a name="9885"
      > </a
      ><a name="9886" href="Maps.html#9588" class="Bound"
      >y</a
      ><a name="9887"
      > </a
      ><a name="9888" href="Maps.html#9590" class="Bound"
      >w</a
      ><a name="9889"
      > </a
      ><a name="9890" href="Maps.html#9592" class="Bound"
      >z</a
      ><a name="9891"
      > </a
      ><a name="9892" href="Maps.html#9828" class="Bound"
      >y&#8802;z</a
      ><a name="9895" class="Symbol"
      >))</a
      >
{% endraw %}</pre>
</div>

## Partial maps

Finally, we define _partial maps_ on top of total maps.  A partial
map with elements of type `A` is simply a total map with elements
of type `Maybe A` and default element `nothing`.

<pre class="Agda">{% raw %}
<a name="10132" href="Maps.html#10132" class="Function"
      >PartialMap</a
      ><a name="10142"
      > </a
      ><a name="10143" class="Symbol"
      >:</a
      ><a name="10144"
      > </a
      ><a name="10145" class="PrimitiveType"
      >Set</a
      ><a name="10148"
      > </a
      ><a name="10149" class="Symbol"
      >&#8594;</a
      ><a name="10150"
      > </a
      ><a name="10151" class="PrimitiveType"
      >Set</a
      ><a name="10154"
      >
</a
      ><a name="10155" href="Maps.html#10132" class="Function"
      >PartialMap</a
      ><a name="10165"
      > </a
      ><a name="10166" href="Maps.html#10166" class="Bound"
      >A</a
      ><a name="10167"
      > </a
      ><a name="10168" class="Symbol"
      >=</a
      ><a name="10169"
      > </a
      ><a name="10170" href="Maps.html#3573" class="Function"
      >TotalMap</a
      ><a name="10178"
      > </a
      ><a name="10179" class="Symbol"
      >(</a
      ><a name="10180" href="https://agda.github.io/agda-stdlib/Data.Maybe.Base.html#335" class="Datatype"
      >Maybe</a
      ><a name="10185"
      > </a
      ><a name="10186" href="Maps.html#10166" class="Bound"
      >A</a
      ><a name="10187" class="Symbol"
      >)</a
      >
{% endraw %}</pre>

<pre class="Agda">{% raw %}
<a name="10214" class="Keyword"
      >module</a
      ><a name="10220"
      > </a
      ><a name="10221" href="Maps.html#10221" class="Module"
      >PartialMap</a
      ><a name="10231"
      > </a
      ><a name="10232" class="Keyword"
      >where</a
      >
{% endraw %}</pre>

<pre class="Agda">{% raw %}
  <a name="10265" href="Maps.html#10265" class="Function"
      >&#8709;</a
      ><a name="10266"
      > </a
      ><a name="10267" class="Symbol"
      >:</a
      ><a name="10268"
      > </a
      ><a name="10269" class="Symbol"
      >&#8704;</a
      ><a name="10270"
      > </a
      ><a name="10271" class="Symbol"
      >{</a
      ><a name="10272" href="Maps.html#10272" class="Bound"
      >A</a
      ><a name="10273" class="Symbol"
      >}</a
      ><a name="10274"
      > </a
      ><a name="10275" class="Symbol"
      >&#8594;</a
      ><a name="10276"
      > </a
      ><a name="10277" href="Maps.html#10132" class="Function"
      >PartialMap</a
      ><a name="10287"
      > </a
      ><a name="10288" href="Maps.html#10272" class="Bound"
      >A</a
      ><a name="10289"
      >
  </a
      ><a name="10292" href="Maps.html#10265" class="Function"
      >&#8709;</a
      ><a name="10293"
      > </a
      ><a name="10294" class="Symbol"
      >=</a
      ><a name="10295"
      > </a
      ><a name="10296" href="Maps.html#3944" class="Function"
      >TotalMap.always</a
      ><a name="10311"
      > </a
      ><a name="10312" href="https://agda.github.io/agda-stdlib/Data.Maybe.Base.html#403" class="InductiveConstructor"
      >nothing</a
      >
{% endraw %}</pre>

<pre class="Agda">{% raw %}
  <a name="10347" class="Keyword"
      >infixl</a
      ><a name="10353"
      > </a
      ><a name="10354" class="Number"
      >15</a
      ><a name="10356"
      > </a
      ><a name="10357" href="Maps.html#10368" class="Function Operator"
      >_,_&#8614;_</a
      ><a name="10362"
      >  

  </a
      ><a name="10368" href="Maps.html#10368" class="Function Operator"
      >_,_&#8614;_</a
      ><a name="10373"
      > </a
      ><a name="10374" class="Symbol"
      >:</a
      ><a name="10375"
      > </a
      ><a name="10376" class="Symbol"
      >&#8704;</a
      ><a name="10377"
      > </a
      ><a name="10378" class="Symbol"
      >{</a
      ><a name="10379" href="Maps.html#10379" class="Bound"
      >A</a
      ><a name="10380" class="Symbol"
      >}</a
      ><a name="10381"
      > </a
      ><a name="10382" class="Symbol"
      >(</a
      ><a name="10383" href="Maps.html#10383" class="Bound"
      >&#961;</a
      ><a name="10384"
      > </a
      ><a name="10385" class="Symbol"
      >:</a
      ><a name="10386"
      > </a
      ><a name="10387" href="Maps.html#10132" class="Function"
      >PartialMap</a
      ><a name="10397"
      > </a
      ><a name="10398" href="Maps.html#10379" class="Bound"
      >A</a
      ><a name="10399" class="Symbol"
      >)</a
      ><a name="10400"
      > </a
      ><a name="10401" class="Symbol"
      >(</a
      ><a name="10402" href="Maps.html#10402" class="Bound"
      >x</a
      ><a name="10403"
      > </a
      ><a name="10404" class="Symbol"
      >:</a
      ><a name="10405"
      > </a
      ><a name="10406" href="Maps.html#2171" class="Datatype"
      >Id</a
      ><a name="10408" class="Symbol"
      >)</a
      ><a name="10409"
      > </a
      ><a name="10410" class="Symbol"
      >(</a
      ><a name="10411" href="Maps.html#10411" class="Bound"
      >v</a
      ><a name="10412"
      > </a
      ><a name="10413" class="Symbol"
      >:</a
      ><a name="10414"
      > </a
      ><a name="10415" href="Maps.html#10379" class="Bound"
      >A</a
      ><a name="10416" class="Symbol"
      >)</a
      ><a name="10417"
      > </a
      ><a name="10418" class="Symbol"
      >&#8594;</a
      ><a name="10419"
      > </a
      ><a name="10420" href="Maps.html#10132" class="Function"
      >PartialMap</a
      ><a name="10430"
      > </a
      ><a name="10431" href="Maps.html#10379" class="Bound"
      >A</a
      ><a name="10432"
      >
  </a
      ><a name="10435" href="Maps.html#10435" class="Bound"
      >&#961;</a
      ><a name="10436"
      > </a
      ><a name="10437" href="Maps.html#10368" class="Function Operator"
      >,</a
      ><a name="10438"
      > </a
      ><a name="10439" href="Maps.html#10439" class="Bound"
      >x</a
      ><a name="10440"
      > </a
      ><a name="10441" href="Maps.html#10368" class="Function Operator"
      >&#8614;</a
      ><a name="10442"
      > </a
      ><a name="10443" href="Maps.html#10443" class="Bound"
      >v</a
      ><a name="10444"
      > </a
      ><a name="10445" class="Symbol"
      >=</a
      ><a name="10446"
      > </a
      ><a name="10447" href="Maps.html#4237" class="Function Operator"
      >TotalMap._,_&#8614;_</a
      ><a name="10461"
      > </a
      ><a name="10462" href="Maps.html#10435" class="Bound"
      >&#961;</a
      ><a name="10463"
      > </a
      ><a name="10464" href="Maps.html#10439" class="Bound"
      >x</a
      ><a name="10465"
      > </a
      ><a name="10466" class="Symbol"
      >(</a
      ><a name="10467" href="https://agda.github.io/agda-stdlib/Data.Maybe.Base.html#373" class="InductiveConstructor"
      >just</a
      ><a name="10471"
      > </a
      ><a name="10472" href="Maps.html#10443" class="Bound"
      >v</a
      ><a name="10473" class="Symbol"
      >)</a
      >
{% endraw %}</pre>

We now lift all of the basic lemmas about total maps to partial maps.

<pre class="Agda">{% raw %}
  <a name="10573" href="Maps.html#10573" class="Function"
      >apply-&#8709;</a
      ><a name="10580"
      > </a
      ><a name="10581" class="Symbol"
      >:</a
      ><a name="10582"
      > </a
      ><a name="10583" class="Symbol"
      >&#8704;</a
      ><a name="10584"
      > </a
      ><a name="10585" class="Symbol"
      >{</a
      ><a name="10586" href="Maps.html#10586" class="Bound"
      >A</a
      ><a name="10587" class="Symbol"
      >}</a
      ><a name="10588"
      > </a
      ><a name="10589" class="Symbol"
      >&#8594;</a
      ><a name="10590"
      > </a
      ><a name="10591" class="Symbol"
      >(</a
      ><a name="10592" href="Maps.html#10592" class="Bound"
      >x</a
      ><a name="10593"
      > </a
      ><a name="10594" class="Symbol"
      >:</a
      ><a name="10595"
      > </a
      ><a name="10596" href="Maps.html#2171" class="Datatype"
      >Id</a
      ><a name="10598" class="Symbol"
      >)</a
      ><a name="10599"
      > </a
      ><a name="10600" class="Symbol"
      >&#8594;</a
      ><a name="10601"
      > </a
      ><a name="10602" class="Symbol"
      >(</a
      ><a name="10603" href="Maps.html#10265" class="Function"
      >&#8709;</a
      ><a name="10604"
      > </a
      ><a name="10605" class="Symbol"
      >{</a
      ><a name="10606" href="Maps.html#10586" class="Bound"
      >A</a
      ><a name="10607" class="Symbol"
      >}</a
      ><a name="10608"
      > </a
      ><a name="10609" href="Maps.html#10592" class="Bound"
      >x</a
      ><a name="10610" class="Symbol"
      >)</a
      ><a name="10611"
      > </a
      ><a name="10612" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="10613"
      > </a
      ><a name="10614" href="https://agda.github.io/agda-stdlib/Data.Maybe.Base.html#403" class="InductiveConstructor"
      >nothing</a
      ><a name="10621"
      >
  </a
      ><a name="10624" href="Maps.html#10573" class="Function"
      >apply-&#8709;</a
      ><a name="10631"
      > </a
      ><a name="10632" href="Maps.html#10632" class="Bound"
      >x</a
      ><a name="10633"
      >  </a
      ><a name="10635" class="Symbol"
      >=</a
      ><a name="10636"
      > </a
      ><a name="10637" href="Maps.html#5425" class="Postulate"
      >TotalMap.apply-always</a
      ><a name="10658"
      > </a
      ><a name="10659" href="https://agda.github.io/agda-stdlib/Data.Maybe.Base.html#403" class="InductiveConstructor"
      >nothing</a
      ><a name="10666"
      > </a
      ><a name="10667" href="Maps.html#10632" class="Bound"
      >x</a
      >
{% endraw %}</pre>

<pre class="Agda">{% raw %}
  <a name="10696" href="Maps.html#10696" class="Function"
      >update-eq</a
      ><a name="10705"
      > </a
      ><a name="10706" class="Symbol"
      >:</a
      ><a name="10707"
      > </a
      ><a name="10708" class="Symbol"
      >&#8704;</a
      ><a name="10709"
      > </a
      ><a name="10710" class="Symbol"
      >{</a
      ><a name="10711" href="Maps.html#10711" class="Bound"
      >A</a
      ><a name="10712" class="Symbol"
      >}</a
      ><a name="10713"
      > </a
      ><a name="10714" class="Symbol"
      >(</a
      ><a name="10715" href="Maps.html#10715" class="Bound"
      >&#961;</a
      ><a name="10716"
      > </a
      ><a name="10717" class="Symbol"
      >:</a
      ><a name="10718"
      > </a
      ><a name="10719" href="Maps.html#10132" class="Function"
      >PartialMap</a
      ><a name="10729"
      > </a
      ><a name="10730" href="Maps.html#10711" class="Bound"
      >A</a
      ><a name="10731" class="Symbol"
      >)</a
      ><a name="10732"
      > </a
      ><a name="10733" class="Symbol"
      >(</a
      ><a name="10734" href="Maps.html#10734" class="Bound"
      >x</a
      ><a name="10735"
      > </a
      ><a name="10736" class="Symbol"
      >:</a
      ><a name="10737"
      > </a
      ><a name="10738" href="Maps.html#2171" class="Datatype"
      >Id</a
      ><a name="10740" class="Symbol"
      >)</a
      ><a name="10741"
      > </a
      ><a name="10742" class="Symbol"
      >(</a
      ><a name="10743" href="Maps.html#10743" class="Bound"
      >v</a
      ><a name="10744"
      > </a
      ><a name="10745" class="Symbol"
      >:</a
      ><a name="10746"
      > </a
      ><a name="10747" href="Maps.html#10711" class="Bound"
      >A</a
      ><a name="10748" class="Symbol"
      >)</a
      ><a name="10749"
      >
            </a
      ><a name="10762" class="Symbol"
      >&#8594;</a
      ><a name="10763"
      > </a
      ><a name="10764" class="Symbol"
      >(</a
      ><a name="10765" href="Maps.html#10715" class="Bound"
      >&#961;</a
      ><a name="10766"
      > </a
      ><a name="10767" href="Maps.html#10368" class="Function Operator"
      >,</a
      ><a name="10768"
      > </a
      ><a name="10769" href="Maps.html#10734" class="Bound"
      >x</a
      ><a name="10770"
      > </a
      ><a name="10771" href="Maps.html#10368" class="Function Operator"
      >&#8614;</a
      ><a name="10772"
      > </a
      ><a name="10773" href="Maps.html#10743" class="Bound"
      >v</a
      ><a name="10774" class="Symbol"
      >)</a
      ><a name="10775"
      > </a
      ><a name="10776" href="Maps.html#10734" class="Bound"
      >x</a
      ><a name="10777"
      > </a
      ><a name="10778" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="10779"
      > </a
      ><a name="10780" href="https://agda.github.io/agda-stdlib/Data.Maybe.Base.html#373" class="InductiveConstructor"
      >just</a
      ><a name="10784"
      > </a
      ><a name="10785" href="Maps.html#10743" class="Bound"
      >v</a
      ><a name="10786"
      >
  </a
      ><a name="10789" href="Maps.html#10696" class="Function"
      >update-eq</a
      ><a name="10798"
      > </a
      ><a name="10799" href="Maps.html#10799" class="Bound"
      >&#961;</a
      ><a name="10800"
      > </a
      ><a name="10801" href="Maps.html#10801" class="Bound"
      >x</a
      ><a name="10802"
      > </a
      ><a name="10803" href="Maps.html#10803" class="Bound"
      >v</a
      ><a name="10804"
      > </a
      ><a name="10805" class="Symbol"
      >=</a
      ><a name="10806"
      > </a
      ><a name="10807" href="Maps.html#5844" class="Postulate"
      >TotalMap.update-eq</a
      ><a name="10825"
      > </a
      ><a name="10826" href="Maps.html#10799" class="Bound"
      >&#961;</a
      ><a name="10827"
      > </a
      ><a name="10828" href="Maps.html#10801" class="Bound"
      >x</a
      ><a name="10829"
      > </a
      ><a name="10830" class="Symbol"
      >(</a
      ><a name="10831" href="https://agda.github.io/agda-stdlib/Data.Maybe.Base.html#373" class="InductiveConstructor"
      >just</a
      ><a name="10835"
      > </a
      ><a name="10836" href="Maps.html#10803" class="Bound"
      >v</a
      ><a name="10837" class="Symbol"
      >)</a
      >
{% endraw %}</pre>

<pre class="Agda">{% raw %}
  <a name="10866" href="Maps.html#10866" class="Function"
      >update-neq</a
      ><a name="10876"
      > </a
      ><a name="10877" class="Symbol"
      >:</a
      ><a name="10878"
      > </a
      ><a name="10879" class="Symbol"
      >&#8704;</a
      ><a name="10880"
      > </a
      ><a name="10881" class="Symbol"
      >{</a
      ><a name="10882" href="Maps.html#10882" class="Bound"
      >A</a
      ><a name="10883" class="Symbol"
      >}</a
      ><a name="10884"
      > </a
      ><a name="10885" class="Symbol"
      >(</a
      ><a name="10886" href="Maps.html#10886" class="Bound"
      >&#961;</a
      ><a name="10887"
      > </a
      ><a name="10888" class="Symbol"
      >:</a
      ><a name="10889"
      > </a
      ><a name="10890" href="Maps.html#10132" class="Function"
      >PartialMap</a
      ><a name="10900"
      > </a
      ><a name="10901" href="Maps.html#10882" class="Bound"
      >A</a
      ><a name="10902" class="Symbol"
      >)</a
      ><a name="10903"
      > </a
      ><a name="10904" class="Symbol"
      >(</a
      ><a name="10905" href="Maps.html#10905" class="Bound"
      >x</a
      ><a name="10906"
      > </a
      ><a name="10907" class="Symbol"
      >:</a
      ><a name="10908"
      > </a
      ><a name="10909" href="Maps.html#2171" class="Datatype"
      >Id</a
      ><a name="10911" class="Symbol"
      >)</a
      ><a name="10912"
      > </a
      ><a name="10913" class="Symbol"
      >(</a
      ><a name="10914" href="Maps.html#10914" class="Bound"
      >v</a
      ><a name="10915"
      > </a
      ><a name="10916" class="Symbol"
      >:</a
      ><a name="10917"
      > </a
      ><a name="10918" href="Maps.html#10882" class="Bound"
      >A</a
      ><a name="10919" class="Symbol"
      >)</a
      ><a name="10920"
      > </a
      ><a name="10921" class="Symbol"
      >(</a
      ><a name="10922" href="Maps.html#10922" class="Bound"
      >y</a
      ><a name="10923"
      > </a
      ><a name="10924" class="Symbol"
      >:</a
      ><a name="10925"
      > </a
      ><a name="10926" href="Maps.html#2171" class="Datatype"
      >Id</a
      ><a name="10928" class="Symbol"
      >)</a
      ><a name="10929"
      >
             </a
      ><a name="10943" class="Symbol"
      >&#8594;</a
      ><a name="10944"
      > </a
      ><a name="10945" href="Maps.html#10905" class="Bound"
      >x</a
      ><a name="10946"
      > </a
      ><a name="10947" href="https://agda.github.io/agda-stdlib/Relation.Binary.Core.html#4493" class="Function Operator"
      >&#8802;</a
      ><a name="10948"
      > </a
      ><a name="10949" href="Maps.html#10922" class="Bound"
      >y</a
      ><a name="10950"
      > </a
      ><a name="10951" class="Symbol"
      >&#8594;</a
      ><a name="10952"
      > </a
      ><a name="10953" class="Symbol"
      >(</a
      ><a name="10954" href="Maps.html#10886" class="Bound"
      >&#961;</a
      ><a name="10955"
      > </a
      ><a name="10956" href="Maps.html#10368" class="Function Operator"
      >,</a
      ><a name="10957"
      > </a
      ><a name="10958" href="Maps.html#10905" class="Bound"
      >x</a
      ><a name="10959"
      > </a
      ><a name="10960" href="Maps.html#10368" class="Function Operator"
      >&#8614;</a
      ><a name="10961"
      > </a
      ><a name="10962" href="Maps.html#10914" class="Bound"
      >v</a
      ><a name="10963" class="Symbol"
      >)</a
      ><a name="10964"
      > </a
      ><a name="10965" href="Maps.html#10922" class="Bound"
      >y</a
      ><a name="10966"
      > </a
      ><a name="10967" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="10968"
      > </a
      ><a name="10969" href="Maps.html#10886" class="Bound"
      >&#961;</a
      ><a name="10970"
      > </a
      ><a name="10971" href="Maps.html#10922" class="Bound"
      >y</a
      ><a name="10972"
      >
  </a
      ><a name="10975" href="Maps.html#10866" class="Function"
      >update-neq</a
      ><a name="10985"
      > </a
      ><a name="10986" href="Maps.html#10986" class="Bound"
      >&#961;</a
      ><a name="10987"
      > </a
      ><a name="10988" href="Maps.html#10988" class="Bound"
      >x</a
      ><a name="10989"
      > </a
      ><a name="10990" href="Maps.html#10990" class="Bound"
      >v</a
      ><a name="10991"
      > </a
      ><a name="10992" href="Maps.html#10992" class="Bound"
      >y</a
      ><a name="10993"
      > </a
      ><a name="10994" href="Maps.html#10994" class="Bound"
      >x&#8802;y</a
      ><a name="10997"
      > </a
      ><a name="10998" class="Symbol"
      >=</a
      ><a name="10999"
      > </a
      ><a name="11000" href="Maps.html#6400" class="Function"
      >TotalMap.update-neq</a
      ><a name="11019"
      > </a
      ><a name="11020" href="Maps.html#10986" class="Bound"
      >&#961;</a
      ><a name="11021"
      > </a
      ><a name="11022" href="Maps.html#10988" class="Bound"
      >x</a
      ><a name="11023"
      > </a
      ><a name="11024" class="Symbol"
      >(</a
      ><a name="11025" href="https://agda.github.io/agda-stdlib/Data.Maybe.Base.html#373" class="InductiveConstructor"
      >just</a
      ><a name="11029"
      > </a
      ><a name="11030" href="Maps.html#10990" class="Bound"
      >v</a
      ><a name="11031" class="Symbol"
      >)</a
      ><a name="11032"
      > </a
      ><a name="11033" href="Maps.html#10992" class="Bound"
      >y</a
      ><a name="11034"
      > </a
      ><a name="11035" href="Maps.html#10994" class="Bound"
      >x&#8802;y</a
      >
{% endraw %}</pre>

<pre class="Agda">{% raw %}
  <a name="11066" href="Maps.html#11066" class="Function"
      >update-shadow</a
      ><a name="11079"
      > </a
      ><a name="11080" class="Symbol"
      >:</a
      ><a name="11081"
      > </a
      ><a name="11082" class="Symbol"
      >&#8704;</a
      ><a name="11083"
      > </a
      ><a name="11084" class="Symbol"
      >{</a
      ><a name="11085" href="Maps.html#11085" class="Bound"
      >A</a
      ><a name="11086" class="Symbol"
      >}</a
      ><a name="11087"
      > </a
      ><a name="11088" class="Symbol"
      >(</a
      ><a name="11089" href="Maps.html#11089" class="Bound"
      >&#961;</a
      ><a name="11090"
      > </a
      ><a name="11091" class="Symbol"
      >:</a
      ><a name="11092"
      > </a
      ><a name="11093" href="Maps.html#10132" class="Function"
      >PartialMap</a
      ><a name="11103"
      > </a
      ><a name="11104" href="Maps.html#11085" class="Bound"
      >A</a
      ><a name="11105" class="Symbol"
      >)</a
      ><a name="11106"
      > </a
      ><a name="11107" class="Symbol"
      >(</a
      ><a name="11108" href="Maps.html#11108" class="Bound"
      >x</a
      ><a name="11109"
      > </a
      ><a name="11110" class="Symbol"
      >:</a
      ><a name="11111"
      > </a
      ><a name="11112" href="Maps.html#2171" class="Datatype"
      >Id</a
      ><a name="11114" class="Symbol"
      >)</a
      ><a name="11115"
      > </a
      ><a name="11116" class="Symbol"
      >(</a
      ><a name="11117" href="Maps.html#11117" class="Bound"
      >v</a
      ><a name="11118"
      > </a
      ><a name="11119" href="Maps.html#11119" class="Bound"
      >w</a
      ><a name="11120"
      > </a
      ><a name="11121" class="Symbol"
      >:</a
      ><a name="11122"
      > </a
      ><a name="11123" href="Maps.html#11085" class="Bound"
      >A</a
      ><a name="11124" class="Symbol"
      >)</a
      ><a name="11125"
      > 
                </a
      ><a name="11143" class="Symbol"
      >&#8594;</a
      ><a name="11144"
      > </a
      ><a name="11145" class="Symbol"
      >(</a
      ><a name="11146" href="Maps.html#11089" class="Bound"
      >&#961;</a
      ><a name="11147"
      > </a
      ><a name="11148" href="Maps.html#10368" class="Function Operator"
      >,</a
      ><a name="11149"
      > </a
      ><a name="11150" href="Maps.html#11108" class="Bound"
      >x</a
      ><a name="11151"
      > </a
      ><a name="11152" href="Maps.html#10368" class="Function Operator"
      >&#8614;</a
      ><a name="11153"
      > </a
      ><a name="11154" href="Maps.html#11117" class="Bound"
      >v</a
      ><a name="11155"
      > </a
      ><a name="11156" href="Maps.html#10368" class="Function Operator"
      >,</a
      ><a name="11157"
      > </a
      ><a name="11158" href="Maps.html#11108" class="Bound"
      >x</a
      ><a name="11159"
      > </a
      ><a name="11160" href="Maps.html#10368" class="Function Operator"
      >&#8614;</a
      ><a name="11161"
      > </a
      ><a name="11162" href="Maps.html#11119" class="Bound"
      >w</a
      ><a name="11163" class="Symbol"
      >)</a
      ><a name="11164"
      > </a
      ><a name="11165" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="11166"
      > </a
      ><a name="11167" class="Symbol"
      >(</a
      ><a name="11168" href="Maps.html#11089" class="Bound"
      >&#961;</a
      ><a name="11169"
      > </a
      ><a name="11170" href="Maps.html#10368" class="Function Operator"
      >,</a
      ><a name="11171"
      > </a
      ><a name="11172" href="Maps.html#11108" class="Bound"
      >x</a
      ><a name="11173"
      > </a
      ><a name="11174" href="Maps.html#10368" class="Function Operator"
      >&#8614;</a
      ><a name="11175"
      > </a
      ><a name="11176" href="Maps.html#11119" class="Bound"
      >w</a
      ><a name="11177" class="Symbol"
      >)</a
      ><a name="11178"
      >
  </a
      ><a name="11181" href="Maps.html#11066" class="Function"
      >update-shadow</a
      ><a name="11194"
      > </a
      ><a name="11195" href="Maps.html#11195" class="Bound"
      >&#961;</a
      ><a name="11196"
      > </a
      ><a name="11197" href="Maps.html#11197" class="Bound"
      >x</a
      ><a name="11198"
      > </a
      ><a name="11199" href="Maps.html#11199" class="Bound"
      >v</a
      ><a name="11200"
      > </a
      ><a name="11201" href="Maps.html#11201" class="Bound"
      >w</a
      ><a name="11202"
      > </a
      ><a name="11203" class="Symbol"
      >=</a
      ><a name="11204"
      > </a
      ><a name="11205" href="Maps.html#7219" class="Postulate"
      >TotalMap.update-shadow</a
      ><a name="11227"
      > </a
      ><a name="11228" href="Maps.html#11195" class="Bound"
      >&#961;</a
      ><a name="11229"
      > </a
      ><a name="11230" href="Maps.html#11197" class="Bound"
      >x</a
      ><a name="11231"
      > </a
      ><a name="11232" class="Symbol"
      >(</a
      ><a name="11233" href="https://agda.github.io/agda-stdlib/Data.Maybe.Base.html#373" class="InductiveConstructor"
      >just</a
      ><a name="11237"
      > </a
      ><a name="11238" href="Maps.html#11199" class="Bound"
      >v</a
      ><a name="11239" class="Symbol"
      >)</a
      ><a name="11240"
      > </a
      ><a name="11241" class="Symbol"
      >(</a
      ><a name="11242" href="https://agda.github.io/agda-stdlib/Data.Maybe.Base.html#373" class="InductiveConstructor"
      >just</a
      ><a name="11246"
      > </a
      ><a name="11247" href="Maps.html#11201" class="Bound"
      >w</a
      ><a name="11248" class="Symbol"
      >)</a
      >
{% endraw %}</pre>

<pre class="Agda">{% raw %}
  <a name="11277" href="Maps.html#11277" class="Function"
      >update-same</a
      ><a name="11288"
      > </a
      ><a name="11289" class="Symbol"
      >:</a
      ><a name="11290"
      > </a
      ><a name="11291" class="Symbol"
      >&#8704;</a
      ><a name="11292"
      > </a
      ><a name="11293" class="Symbol"
      >{</a
      ><a name="11294" href="Maps.html#11294" class="Bound"
      >A</a
      ><a name="11295" class="Symbol"
      >}</a
      ><a name="11296"
      > </a
      ><a name="11297" class="Symbol"
      >(</a
      ><a name="11298" href="Maps.html#11298" class="Bound"
      >&#961;</a
      ><a name="11299"
      > </a
      ><a name="11300" class="Symbol"
      >:</a
      ><a name="11301"
      > </a
      ><a name="11302" href="Maps.html#10132" class="Function"
      >PartialMap</a
      ><a name="11312"
      > </a
      ><a name="11313" href="Maps.html#11294" class="Bound"
      >A</a
      ><a name="11314" class="Symbol"
      >)</a
      ><a name="11315"
      > </a
      ><a name="11316" class="Symbol"
      >(</a
      ><a name="11317" href="Maps.html#11317" class="Bound"
      >x</a
      ><a name="11318"
      > </a
      ><a name="11319" class="Symbol"
      >:</a
      ><a name="11320"
      > </a
      ><a name="11321" href="Maps.html#2171" class="Datatype"
      >Id</a
      ><a name="11323" class="Symbol"
      >)</a
      ><a name="11324"
      > </a
      ><a name="11325" class="Symbol"
      >(</a
      ><a name="11326" href="Maps.html#11326" class="Bound"
      >v</a
      ><a name="11327"
      > </a
      ><a name="11328" class="Symbol"
      >:</a
      ><a name="11329"
      > </a
      ><a name="11330" href="Maps.html#11294" class="Bound"
      >A</a
      ><a name="11331" class="Symbol"
      >)</a
      ><a name="11332"
      > 
              </a
      ><a name="11348" class="Symbol"
      >&#8594;</a
      ><a name="11349"
      > </a
      ><a name="11350" href="Maps.html#11298" class="Bound"
      >&#961;</a
      ><a name="11351"
      > </a
      ><a name="11352" href="Maps.html#11317" class="Bound"
      >x</a
      ><a name="11353"
      > </a
      ><a name="11354" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="11355"
      > </a
      ><a name="11356" href="https://agda.github.io/agda-stdlib/Data.Maybe.Base.html#373" class="InductiveConstructor"
      >just</a
      ><a name="11360"
      > </a
      ><a name="11361" href="Maps.html#11326" class="Bound"
      >v</a
      ><a name="11362"
      >
              </a
      ><a name="11377" class="Symbol"
      >&#8594;</a
      ><a name="11378"
      > </a
      ><a name="11379" class="Symbol"
      >(</a
      ><a name="11380" href="Maps.html#11298" class="Bound"
      >&#961;</a
      ><a name="11381"
      > </a
      ><a name="11382" href="Maps.html#10368" class="Function Operator"
      >,</a
      ><a name="11383"
      > </a
      ><a name="11384" href="Maps.html#11317" class="Bound"
      >x</a
      ><a name="11385"
      > </a
      ><a name="11386" href="Maps.html#10368" class="Function Operator"
      >&#8614;</a
      ><a name="11387"
      > </a
      ><a name="11388" href="Maps.html#11326" class="Bound"
      >v</a
      ><a name="11389" class="Symbol"
      >)</a
      ><a name="11390"
      > </a
      ><a name="11391" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="11392"
      > </a
      ><a name="11393" href="Maps.html#11298" class="Bound"
      >&#961;</a
      ><a name="11394"
      >
  </a
      ><a name="11397" href="Maps.html#11277" class="Function"
      >update-same</a
      ><a name="11408"
      > </a
      ><a name="11409" href="Maps.html#11409" class="Bound"
      >&#961;</a
      ><a name="11410"
      > </a
      ><a name="11411" href="Maps.html#11411" class="Bound"
      >x</a
      ><a name="11412"
      > </a
      ><a name="11413" href="Maps.html#11413" class="Bound"
      >v</a
      ><a name="11414"
      > </a
      ><a name="11415" href="Maps.html#11415" class="Bound"
      >&#961;x&#8801;v</a
      ><a name="11419"
      > </a
      ><a name="11420" class="Keyword"
      >rewrite</a
      ><a name="11427"
      > </a
      ><a name="11428" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.Core.html#565" class="Function"
      >sym</a
      ><a name="11431"
      > </a
      ><a name="11432" href="Maps.html#11415" class="Bound"
      >&#961;x&#8801;v</a
      ><a name="11436"
      > </a
      ><a name="11437" class="Symbol"
      >=</a
      ><a name="11438"
      > </a
      ><a name="11439" href="Maps.html#7954" class="Postulate"
      >TotalMap.update-same</a
      ><a name="11459"
      > </a
      ><a name="11460" href="Maps.html#11409" class="Bound"
      >&#961;</a
      ><a name="11461"
      > </a
      ><a name="11462" href="Maps.html#11411" class="Bound"
      >x</a
      >
{% endraw %}</pre>

<pre class="Agda">{% raw %}
  <a name="11491" href="Maps.html#11491" class="Function"
      >update-permute</a
      ><a name="11505"
      > </a
      ><a name="11506" class="Symbol"
      >:</a
      ><a name="11507"
      > </a
      ><a name="11508" class="Symbol"
      >&#8704;</a
      ><a name="11509"
      > </a
      ><a name="11510" class="Symbol"
      >{</a
      ><a name="11511" href="Maps.html#11511" class="Bound"
      >A</a
      ><a name="11512" class="Symbol"
      >}</a
      ><a name="11513"
      > </a
      ><a name="11514" class="Symbol"
      >(</a
      ><a name="11515" href="Maps.html#11515" class="Bound"
      >&#961;</a
      ><a name="11516"
      > </a
      ><a name="11517" class="Symbol"
      >:</a
      ><a name="11518"
      > </a
      ><a name="11519" href="Maps.html#10132" class="Function"
      >PartialMap</a
      ><a name="11529"
      > </a
      ><a name="11530" href="Maps.html#11511" class="Bound"
      >A</a
      ><a name="11531" class="Symbol"
      >)</a
      ><a name="11532"
      > </a
      ><a name="11533" class="Symbol"
      >(</a
      ><a name="11534" href="Maps.html#11534" class="Bound"
      >x</a
      ><a name="11535"
      > </a
      ><a name="11536" class="Symbol"
      >:</a
      ><a name="11537"
      > </a
      ><a name="11538" href="Maps.html#2171" class="Datatype"
      >Id</a
      ><a name="11540" class="Symbol"
      >)</a
      ><a name="11541"
      > </a
      ><a name="11542" class="Symbol"
      >(</a
      ><a name="11543" href="Maps.html#11543" class="Bound"
      >v</a
      ><a name="11544"
      > </a
      ><a name="11545" class="Symbol"
      >:</a
      ><a name="11546"
      > </a
      ><a name="11547" href="Maps.html#11511" class="Bound"
      >A</a
      ><a name="11548" class="Symbol"
      >)</a
      ><a name="11549"
      > </a
      ><a name="11550" class="Symbol"
      >(</a
      ><a name="11551" href="Maps.html#11551" class="Bound"
      >y</a
      ><a name="11552"
      > </a
      ><a name="11553" class="Symbol"
      >:</a
      ><a name="11554"
      > </a
      ><a name="11555" href="Maps.html#2171" class="Datatype"
      >Id</a
      ><a name="11557" class="Symbol"
      >)</a
      ><a name="11558"
      > </a
      ><a name="11559" class="Symbol"
      >(</a
      ><a name="11560" href="Maps.html#11560" class="Bound"
      >w</a
      ><a name="11561"
      > </a
      ><a name="11562" class="Symbol"
      >:</a
      ><a name="11563"
      > </a
      ><a name="11564" href="Maps.html#11511" class="Bound"
      >A</a
      ><a name="11565" class="Symbol"
      >)</a
      ><a name="11566"
      > 
                 </a
      ><a name="11585" class="Symbol"
      >&#8594;</a
      ><a name="11586"
      > </a
      ><a name="11587" href="Maps.html#11534" class="Bound"
      >x</a
      ><a name="11588"
      > </a
      ><a name="11589" href="https://agda.github.io/agda-stdlib/Relation.Binary.Core.html#4493" class="Function Operator"
      >&#8802;</a
      ><a name="11590"
      > </a
      ><a name="11591" href="Maps.html#11551" class="Bound"
      >y</a
      ><a name="11592"
      > </a
      ><a name="11593" class="Symbol"
      >&#8594;</a
      ><a name="11594"
      > </a
      ><a name="11595" class="Symbol"
      >(</a
      ><a name="11596" href="Maps.html#11515" class="Bound"
      >&#961;</a
      ><a name="11597"
      > </a
      ><a name="11598" href="Maps.html#10368" class="Function Operator"
      >,</a
      ><a name="11599"
      > </a
      ><a name="11600" href="Maps.html#11534" class="Bound"
      >x</a
      ><a name="11601"
      > </a
      ><a name="11602" href="Maps.html#10368" class="Function Operator"
      >&#8614;</a
      ><a name="11603"
      > </a
      ><a name="11604" href="Maps.html#11543" class="Bound"
      >v</a
      ><a name="11605"
      > </a
      ><a name="11606" href="Maps.html#10368" class="Function Operator"
      >,</a
      ><a name="11607"
      > </a
      ><a name="11608" href="Maps.html#11551" class="Bound"
      >y</a
      ><a name="11609"
      > </a
      ><a name="11610" href="Maps.html#10368" class="Function Operator"
      >&#8614;</a
      ><a name="11611"
      > </a
      ><a name="11612" href="Maps.html#11560" class="Bound"
      >w</a
      ><a name="11613" class="Symbol"
      >)</a
      ><a name="11614"
      > </a
      ><a name="11615" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="11616"
      > </a
      ><a name="11617" class="Symbol"
      >(</a
      ><a name="11618" href="Maps.html#11515" class="Bound"
      >&#961;</a
      ><a name="11619"
      > </a
      ><a name="11620" href="Maps.html#10368" class="Function Operator"
      >,</a
      ><a name="11621"
      > </a
      ><a name="11622" href="Maps.html#11551" class="Bound"
      >y</a
      ><a name="11623"
      > </a
      ><a name="11624" href="Maps.html#10368" class="Function Operator"
      >&#8614;</a
      ><a name="11625"
      > </a
      ><a name="11626" href="Maps.html#11560" class="Bound"
      >w</a
      ><a name="11627"
      > </a
      ><a name="11628" href="Maps.html#10368" class="Function Operator"
      >,</a
      ><a name="11629"
      > </a
      ><a name="11630" href="Maps.html#11534" class="Bound"
      >x</a
      ><a name="11631"
      > </a
      ><a name="11632" href="Maps.html#10368" class="Function Operator"
      >&#8614;</a
      ><a name="11633"
      > </a
      ><a name="11634" href="Maps.html#11543" class="Bound"
      >v</a
      ><a name="11635" class="Symbol"
      >)</a
      ><a name="11636"
      >
  </a
      ><a name="11639" href="Maps.html#11491" class="Function"
      >update-permute</a
      ><a name="11653"
      > </a
      ><a name="11654" href="Maps.html#11654" class="Bound"
      >&#961;</a
      ><a name="11655"
      > </a
      ><a name="11656" href="Maps.html#11656" class="Bound"
      >x</a
      ><a name="11657"
      > </a
      ><a name="11658" href="Maps.html#11658" class="Bound"
      >v</a
      ><a name="11659"
      > </a
      ><a name="11660" href="Maps.html#11660" class="Bound"
      >y</a
      ><a name="11661"
      > </a
      ><a name="11662" href="Maps.html#11662" class="Bound"
      >w</a
      ><a name="11663"
      > </a
      ><a name="11664" href="Maps.html#11664" class="Bound"
      >x&#8802;y</a
      ><a name="11667"
      > </a
      ><a name="11668" class="Symbol"
      >=</a
      ><a name="11669"
      > </a
      ><a name="11670" href="Maps.html#8554" class="Postulate"
      >TotalMap.update-permute</a
      ><a name="11693"
      > </a
      ><a name="11694" href="Maps.html#11654" class="Bound"
      >&#961;</a
      ><a name="11695"
      > </a
      ><a name="11696" href="Maps.html#11656" class="Bound"
      >x</a
      ><a name="11697"
      > </a
      ><a name="11698" class="Symbol"
      >(</a
      ><a name="11699" href="https://agda.github.io/agda-stdlib/Data.Maybe.Base.html#373" class="InductiveConstructor"
      >just</a
      ><a name="11703"
      > </a
      ><a name="11704" href="Maps.html#11658" class="Bound"
      >v</a
      ><a name="11705" class="Symbol"
      >)</a
      ><a name="11706"
      > </a
      ><a name="11707" href="Maps.html#11660" class="Bound"
      >y</a
      ><a name="11708"
      > </a
      ><a name="11709" class="Symbol"
      >(</a
      ><a name="11710" href="https://agda.github.io/agda-stdlib/Data.Maybe.Base.html#373" class="InductiveConstructor"
      >just</a
      ><a name="11714"
      > </a
      ><a name="11715" href="Maps.html#11662" class="Bound"
      >w</a
      ><a name="11716" class="Symbol"
      >)</a
      ><a name="11717"
      > </a
      ><a name="11718" href="Maps.html#11664" class="Bound"
      >x&#8802;y</a
      >
{% endraw %}</pre>

We will also need the following basic facts about the `Maybe` type.

<pre class="Agda">{% raw %}
  <a name="11818" href="Maps.html#11818" class="Function"
      >just&#8802;nothing</a
      ><a name="11830"
      > </a
      ><a name="11831" class="Symbol"
      >:</a
      ><a name="11832"
      > </a
      ><a name="11833" class="Symbol"
      >&#8704;</a
      ><a name="11834"
      > </a
      ><a name="11835" class="Symbol"
      >{</a
      ><a name="11836" href="Maps.html#11836" class="Bound"
      >X</a
      ><a name="11837"
      > </a
      ><a name="11838" class="Symbol"
      >:</a
      ><a name="11839"
      > </a
      ><a name="11840" class="PrimitiveType"
      >Set</a
      ><a name="11843" class="Symbol"
      >}</a
      ><a name="11844"
      > </a
      ><a name="11845" class="Symbol"
      >&#8594;</a
      ><a name="11846"
      > </a
      ><a name="11847" class="Symbol"
      >&#8704;</a
      ><a name="11848"
      > </a
      ><a name="11849" class="Symbol"
      >{</a
      ><a name="11850" href="Maps.html#11850" class="Bound"
      >x</a
      ><a name="11851"
      > </a
      ><a name="11852" class="Symbol"
      >:</a
      ><a name="11853"
      > </a
      ><a name="11854" href="Maps.html#11836" class="Bound"
      >X</a
      ><a name="11855" class="Symbol"
      >}</a
      ><a name="11856"
      > </a
      ><a name="11857" class="Symbol"
      >&#8594;</a
      ><a name="11858"
      > </a
      ><a name="11859" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#414" class="Function Operator"
      >&#172;</a
      ><a name="11860"
      > </a
      ><a name="11861" class="Symbol"
      >(</a
      ><a name="11862" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >_&#8801;_</a
      ><a name="11865"
      > </a
      ><a name="11866" class="Symbol"
      >{</a
      ><a name="11867" class="Argument"
      >A</a
      ><a name="11868"
      > </a
      ><a name="11869" class="Symbol"
      >=</a
      ><a name="11870"
      > </a
      ><a name="11871" href="https://agda.github.io/agda-stdlib/Data.Maybe.Base.html#335" class="Datatype"
      >Maybe</a
      ><a name="11876"
      > </a
      ><a name="11877" href="Maps.html#11836" class="Bound"
      >X</a
      ><a name="11878" class="Symbol"
      >}</a
      ><a name="11879"
      > </a
      ><a name="11880" class="Symbol"
      >(</a
      ><a name="11881" href="https://agda.github.io/agda-stdlib/Data.Maybe.Base.html#373" class="InductiveConstructor"
      >just</a
      ><a name="11885"
      > </a
      ><a name="11886" href="Maps.html#11850" class="Bound"
      >x</a
      ><a name="11887" class="Symbol"
      >)</a
      ><a name="11888"
      > </a
      ><a name="11889" href="https://agda.github.io/agda-stdlib/Data.Maybe.Base.html#403" class="InductiveConstructor"
      >nothing</a
      ><a name="11896" class="Symbol"
      >)</a
      ><a name="11897"
      >
  </a
      ><a name="11900" href="Maps.html#11818" class="Function"
      >just&#8802;nothing</a
      ><a name="11912"
      > </a
      ><a name="11913" class="Symbol"
      >()</a
      ><a name="11915"
      >

  </a
      ><a name="11919" href="Maps.html#11919" class="Function"
      >just-injective</a
      ><a name="11933"
      > </a
      ><a name="11934" class="Symbol"
      >:</a
      ><a name="11935"
      > </a
      ><a name="11936" class="Symbol"
      >&#8704;</a
      ><a name="11937"
      > </a
      ><a name="11938" class="Symbol"
      >{</a
      ><a name="11939" href="Maps.html#11939" class="Bound"
      >X</a
      ><a name="11940"
      > </a
      ><a name="11941" class="Symbol"
      >:</a
      ><a name="11942"
      > </a
      ><a name="11943" class="PrimitiveType"
      >Set</a
      ><a name="11946" class="Symbol"
      >}</a
      ><a name="11947"
      > </a
      ><a name="11948" class="Symbol"
      >{</a
      ><a name="11949" href="Maps.html#11949" class="Bound"
      >x</a
      ><a name="11950"
      > </a
      ><a name="11951" href="Maps.html#11951" class="Bound"
      >y</a
      ><a name="11952"
      > </a
      ><a name="11953" class="Symbol"
      >:</a
      ><a name="11954"
      > </a
      ><a name="11955" href="Maps.html#11939" class="Bound"
      >X</a
      ><a name="11956" class="Symbol"
      >}</a
      ><a name="11957"
      > </a
      ><a name="11958" class="Symbol"
      >&#8594;</a
      ><a name="11959"
      > </a
      ><a name="11960" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >_&#8801;_</a
      ><a name="11963"
      > </a
      ><a name="11964" class="Symbol"
      >{</a
      ><a name="11965" class="Argument"
      >A</a
      ><a name="11966"
      > </a
      ><a name="11967" class="Symbol"
      >=</a
      ><a name="11968"
      > </a
      ><a name="11969" href="https://agda.github.io/agda-stdlib/Data.Maybe.Base.html#335" class="Datatype"
      >Maybe</a
      ><a name="11974"
      > </a
      ><a name="11975" href="Maps.html#11939" class="Bound"
      >X</a
      ><a name="11976" class="Symbol"
      >}</a
      ><a name="11977"
      > </a
      ><a name="11978" class="Symbol"
      >(</a
      ><a name="11979" href="https://agda.github.io/agda-stdlib/Data.Maybe.Base.html#373" class="InductiveConstructor"
      >just</a
      ><a name="11983"
      > </a
      ><a name="11984" href="Maps.html#11949" class="Bound"
      >x</a
      ><a name="11985" class="Symbol"
      >)</a
      ><a name="11986"
      > </a
      ><a name="11987" class="Symbol"
      >(</a
      ><a name="11988" href="https://agda.github.io/agda-stdlib/Data.Maybe.Base.html#373" class="InductiveConstructor"
      >just</a
      ><a name="11992"
      > </a
      ><a name="11993" href="Maps.html#11951" class="Bound"
      >y</a
      ><a name="11994" class="Symbol"
      >)</a
      ><a name="11995"
      > </a
      ><a name="11996" class="Symbol"
      >&#8594;</a
      ><a name="11997"
      > </a
      ><a name="11998" href="Maps.html#11949" class="Bound"
      >x</a
      ><a name="11999"
      > </a
      ><a name="12000" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="12001"
      > </a
      ><a name="12002" href="Maps.html#11951" class="Bound"
      >y</a
      ><a name="12003"
      >
  </a
      ><a name="12006" href="Maps.html#11919" class="Function"
      >just-injective</a
      ><a name="12020"
      > </a
      ><a name="12021" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="12025"
      > </a
      ><a name="12026" class="Symbol"
      >=</a
      ><a name="12027"
      > </a
      ><a name="12028" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      >
{% endraw %}</pre>
