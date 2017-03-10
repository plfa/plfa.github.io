---
title         : "Maps: Total and Partial Maps"
layout        : default
hide-implicit : false
extra-script : [agda-extra-script.html]
extra-style  : [agda-extra-style.html]
permalink     : "sf/Maps.html"
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

<!--{% raw %}--><pre class="Agda">
<a name="1607" class="Keyword"
      >open</a
      ><a name="1611"
      > </a
      ><a name="1612" class="Keyword"
      >import</a
      ><a name="1618"
      > </a
      ><a name="1619" href="https://agda.github.io/agda-stdlib/Function.html#1" class="Module"
      >Function</a
      ><a name="1627"
      >         </a
      ><a name="1636" class="Keyword"
      >using</a
      ><a name="1641"
      > </a
      ><a name="1642" class="Symbol"
      >(</a
      ><a name="1643" href="https://agda.github.io/agda-stdlib/Function.html#713" class="Function Operator"
      >_&#8728;_</a
      ><a name="1646" class="Symbol"
      >)</a
      ><a name="1647"
      >
</a
      ><a name="1648" class="Keyword"
      >open</a
      ><a name="1652"
      > </a
      ><a name="1653" class="Keyword"
      >import</a
      ><a name="1659"
      > </a
      ><a name="1660" href="https://agda.github.io/agda-stdlib/Data.Bool.html#1" class="Module"
      >Data.Bool</a
      ><a name="1669"
      >        </a
      ><a name="1677" class="Keyword"
      >using</a
      ><a name="1682"
      > </a
      ><a name="1683" class="Symbol"
      >(</a
      ><a name="1684" href="Agda.Builtin.Bool.html#39" class="Datatype"
      >Bool</a
      ><a name="1688" class="Symbol"
      >;</a
      ><a name="1689"
      > </a
      ><a name="1690" href="Agda.Builtin.Bool.html#64" class="InductiveConstructor"
      >true</a
      ><a name="1694" class="Symbol"
      >;</a
      ><a name="1695"
      > </a
      ><a name="1696" href="Agda.Builtin.Bool.html#58" class="InductiveConstructor"
      >false</a
      ><a name="1701" class="Symbol"
      >)</a
      ><a name="1702"
      >
</a
      ><a name="1703" class="Keyword"
      >open</a
      ><a name="1707"
      > </a
      ><a name="1708" class="Keyword"
      >import</a
      ><a name="1714"
      > </a
      ><a name="1715" href="https://agda.github.io/agda-stdlib/Data.Empty.html#1" class="Module"
      >Data.Empty</a
      ><a name="1725"
      >       </a
      ><a name="1732" class="Keyword"
      >using</a
      ><a name="1737"
      > </a
      ><a name="1738" class="Symbol"
      >(</a
      ><a name="1739" href="https://agda.github.io/agda-stdlib/Data.Empty.html#243" class="Datatype"
      >&#8869;</a
      ><a name="1740" class="Symbol"
      >;</a
      ><a name="1741"
      > </a
      ><a name="1742" href="https://agda.github.io/agda-stdlib/Data.Empty.html#348" class="Function"
      >&#8869;-elim</a
      ><a name="1748" class="Symbol"
      >)</a
      ><a name="1749"
      >
</a
      ><a name="1750" class="Keyword"
      >open</a
      ><a name="1754"
      > </a
      ><a name="1755" class="Keyword"
      >import</a
      ><a name="1761"
      > </a
      ><a name="1762" href="https://agda.github.io/agda-stdlib/Data.Maybe.html#1" class="Module"
      >Data.Maybe</a
      ><a name="1772"
      >       </a
      ><a name="1779" class="Keyword"
      >using</a
      ><a name="1784"
      > </a
      ><a name="1785" class="Symbol"
      >(</a
      ><a name="1786" href="https://agda.github.io/agda-stdlib/Data.Maybe.Base.html#335" class="Datatype"
      >Maybe</a
      ><a name="1791" class="Symbol"
      >;</a
      ><a name="1792"
      > </a
      ><a name="1793" href="https://agda.github.io/agda-stdlib/Data.Maybe.html#1527" class="InductiveConstructor"
      >just</a
      ><a name="1797" class="Symbol"
      >;</a
      ><a name="1798"
      > </a
      ><a name="1799" href="https://agda.github.io/agda-stdlib/Data.Maybe.html#1588" class="InductiveConstructor"
      >nothing</a
      ><a name="1806" class="Symbol"
      >)</a
      ><a name="1807"
      >
</a
      ><a name="1808" class="Keyword"
      >open</a
      ><a name="1812"
      > </a
      ><a name="1813" class="Keyword"
      >import</a
      ><a name="1819"
      > </a
      ><a name="1820" href="https://agda.github.io/agda-stdlib/Data.Nat.html#1" class="Module"
      >Data.Nat</a
      ><a name="1828"
      >         </a
      ><a name="1837" class="Keyword"
      >using</a
      ><a name="1842"
      > </a
      ><a name="1843" class="Symbol"
      >(</a
      ><a name="1844" href="Agda.Builtin.Nat.html#69" class="Datatype"
      >&#8469;</a
      ><a name="1845" class="Symbol"
      >)</a
      ><a name="1846"
      >
</a
      ><a name="1847" class="Keyword"
      >open</a
      ><a name="1851"
      > </a
      ><a name="1852" class="Keyword"
      >import</a
      ><a name="1858"
      > </a
      ><a name="1859" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#1" class="Module"
      >Relation.Nullary</a
      ><a name="1875"
      > </a
      ><a name="1876" class="Keyword"
      >using</a
      ><a name="1881"
      > </a
      ><a name="1882" class="Symbol"
      >(</a
      ><a name="1883" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#484" class="Datatype"
      >Dec</a
      ><a name="1886" class="Symbol"
      >;</a
      ><a name="1887"
      > </a
      ><a name="1888" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#520" class="InductiveConstructor"
      >yes</a
      ><a name="1891" class="Symbol"
      >;</a
      ><a name="1892"
      > </a
      ><a name="1893" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#547" class="InductiveConstructor"
      >no</a
      ><a name="1895" class="Symbol"
      >)</a
      ><a name="1896"
      >
</a
      ><a name="1897" class="Keyword"
      >open</a
      ><a name="1901"
      > </a
      ><a name="1902" class="Keyword"
      >import</a
      ><a name="1908"
      > </a
      ><a name="1909" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#1" class="Module"
      >Relation.Binary.PropositionalEquality</a
      >
</pre><!--{% endraw %}-->

Documentation for the standard library can be found at
<https://agda.github.io/agda-stdlib/>.

## Identifiers

First, we need a type for the keys that we use to index into our
maps.  For this purpose, we again use the type Id` from the
[Lists](sf/Lists.html) chapter.  To make this chapter self contained,
we repeat its definition here, together with the equality comparison
function for ids and its fundamental property.

<!--{% raw %}--><pre class="Agda">
<a name="2395" class="Keyword"
      >data</a
      ><a name="2399"
      > </a
      ><a name="2400" href="Maps.html#2400" class="Datatype"
      >Id</a
      ><a name="2402"
      > </a
      ><a name="2403" class="Symbol"
      >:</a
      ><a name="2404"
      > </a
      ><a name="2405" class="PrimitiveType"
      >Set</a
      ><a name="2408"
      > </a
      ><a name="2409" class="Keyword"
      >where</a
      ><a name="2414"
      >
  </a
      ><a name="2417" href="Maps.html#2417" class="InductiveConstructor"
      >id</a
      ><a name="2419"
      > </a
      ><a name="2420" class="Symbol"
      >:</a
      ><a name="2421"
      > </a
      ><a name="2422" href="Agda.Builtin.Nat.html#69" class="Datatype"
      >&#8469;</a
      ><a name="2423"
      > </a
      ><a name="2424" class="Symbol"
      >&#8594;</a
      ><a name="2425"
      > </a
      ><a name="2426" href="Maps.html#2400" class="Datatype"
      >Id</a
      >
</pre><!--{% endraw %}-->

<!--{% raw %}--><pre class="Agda">
<a name="2454" href="Maps.html#2454" class="Function Operator"
      >_&#8799;_</a
      ><a name="2457"
      > </a
      ><a name="2458" class="Symbol"
      >:</a
      ><a name="2459"
      > </a
      ><a name="2460" class="Symbol"
      >(</a
      ><a name="2461" href="Maps.html#2461" class="Bound"
      >x</a
      ><a name="2462"
      > </a
      ><a name="2463" href="Maps.html#2463" class="Bound"
      >y</a
      ><a name="2464"
      > </a
      ><a name="2465" class="Symbol"
      >:</a
      ><a name="2466"
      > </a
      ><a name="2467" href="Maps.html#2400" class="Datatype"
      >Id</a
      ><a name="2469" class="Symbol"
      >)</a
      ><a name="2470"
      > </a
      ><a name="2471" class="Symbol"
      >&#8594;</a
      ><a name="2472"
      > </a
      ><a name="2473" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#484" class="Datatype"
      >Dec</a
      ><a name="2476"
      > </a
      ><a name="2477" class="Symbol"
      >(</a
      ><a name="2478" href="Maps.html#2461" class="Bound"
      >x</a
      ><a name="2479"
      > </a
      ><a name="2480" href="Agda.Builtin.Equality.html#55" class="Datatype Operator"
      >&#8801;</a
      ><a name="2481"
      > </a
      ><a name="2482" href="Maps.html#2463" class="Bound"
      >y</a
      ><a name="2483" class="Symbol"
      >)</a
      ><a name="2484"
      >
</a
      ><a name="2485" href="Maps.html#2417" class="InductiveConstructor"
      >id</a
      ><a name="2487"
      > </a
      ><a name="2488" href="Maps.html#2488" class="Bound"
      >x</a
      ><a name="2489"
      > </a
      ><a name="2490" href="Maps.html#2454" class="Function Operator"
      >&#8799;</a
      ><a name="2491"
      > </a
      ><a name="2492" href="Maps.html#2417" class="InductiveConstructor"
      >id</a
      ><a name="2494"
      > </a
      ><a name="2495" href="Maps.html#2495" class="Bound"
      >y</a
      ><a name="2496"
      > </a
      ><a name="2497" class="Keyword"
      >with</a
      ><a name="2501"
      > </a
      ><a name="2502" href="Maps.html#2488" class="Bound"
      >x</a
      ><a name="2503"
      > </a
      ><a name="2504" href="https://agda.github.io/agda-stdlib/Data.Nat.Base.html#3199" class="Function Operator"
      >Data.Nat.&#8799;</a
      ><a name="2514"
      > </a
      ><a name="2515" href="Maps.html#2495" class="Bound"
      >y</a
      ><a name="2516"
      >
</a
      ><a name="2517" href="Maps.html#2417" class="InductiveConstructor"
      >id</a
      ><a name="2519"
      > </a
      ><a name="2520" href="Maps.html#2520" class="Bound"
      >x</a
      ><a name="2521"
      > </a
      ><a name="2522" href="Maps.html#2454" class="Function Operator"
      >&#8799;</a
      ><a name="2523"
      > </a
      ><a name="2524" href="Maps.html#2417" class="InductiveConstructor"
      >id</a
      ><a name="2526"
      > </a
      ><a name="2527" href="Maps.html#2527" class="Bound"
      >y</a
      ><a name="2528"
      > </a
      ><a name="2529" class="Symbol"
      >|</a
      ><a name="2530"
      > </a
      ><a name="2531" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#520" class="InductiveConstructor"
      >yes</a
      ><a name="2534"
      > </a
      ><a name="2535" href="Maps.html#2535" class="Bound"
      >x=y</a
      ><a name="2538"
      > </a
      ><a name="2539" class="Keyword"
      >rewrite</a
      ><a name="2546"
      > </a
      ><a name="2547" href="Maps.html#2535" class="Bound"
      >x=y</a
      ><a name="2550"
      > </a
      ><a name="2551" class="Symbol"
      >=</a
      ><a name="2552"
      > </a
      ><a name="2553" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#520" class="InductiveConstructor"
      >yes</a
      ><a name="2556"
      > </a
      ><a name="2557" href="Agda.Builtin.Equality.html#112" class="InductiveConstructor"
      >refl</a
      ><a name="2561"
      >
</a
      ><a name="2562" href="Maps.html#2417" class="InductiveConstructor"
      >id</a
      ><a name="2564"
      > </a
      ><a name="2565" href="Maps.html#2565" class="Bound"
      >x</a
      ><a name="2566"
      > </a
      ><a name="2567" href="Maps.html#2454" class="Function Operator"
      >&#8799;</a
      ><a name="2568"
      > </a
      ><a name="2569" href="Maps.html#2417" class="InductiveConstructor"
      >id</a
      ><a name="2571"
      > </a
      ><a name="2572" href="Maps.html#2572" class="Bound"
      >y</a
      ><a name="2573"
      > </a
      ><a name="2574" class="Symbol"
      >|</a
      ><a name="2575"
      > </a
      ><a name="2576" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#547" class="InductiveConstructor"
      >no</a
      ><a name="2578"
      >  </a
      ><a name="2580" href="Maps.html#2580" class="Bound"
      >x&#8800;y</a
      ><a name="2583"
      > </a
      ><a name="2584" class="Symbol"
      >=</a
      ><a name="2585"
      > </a
      ><a name="2586" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#547" class="InductiveConstructor"
      >no</a
      ><a name="2588"
      > </a
      ><a name="2589" class="Symbol"
      >(</a
      ><a name="2590" href="Maps.html#2580" class="Bound"
      >x&#8800;y</a
      ><a name="2593"
      > </a
      ><a name="2594" href="https://agda.github.io/agda-stdlib/Function.html#713" class="Function Operator"
      >&#8728;</a
      ><a name="2595"
      > </a
      ><a name="2596" href="Maps.html#2616" class="Function"
      >id-inj</a
      ><a name="2602" class="Symbol"
      >)</a
      ><a name="2603"
      >
  </a
      ><a name="2606" class="Keyword"
      >where</a
      ><a name="2611"
      >
    </a
      ><a name="2616" href="Maps.html#2616" class="Function"
      >id-inj</a
      ><a name="2622"
      > </a
      ><a name="2623" class="Symbol"
      >:</a
      ><a name="2624"
      > </a
      ><a name="2625" class="Symbol"
      >&#8704;</a
      ><a name="2626"
      > </a
      ><a name="2627" class="Symbol"
      >{</a
      ><a name="2628" href="Maps.html#2628" class="Bound"
      >x</a
      ><a name="2629"
      > </a
      ><a name="2630" href="Maps.html#2630" class="Bound"
      >y</a
      ><a name="2631" class="Symbol"
      >}</a
      ><a name="2632"
      > </a
      ><a name="2633" class="Symbol"
      >&#8594;</a
      ><a name="2634"
      > </a
      ><a name="2635" href="Maps.html#2417" class="InductiveConstructor"
      >id</a
      ><a name="2637"
      > </a
      ><a name="2638" href="Maps.html#2628" class="Bound"
      >x</a
      ><a name="2639"
      > </a
      ><a name="2640" href="Agda.Builtin.Equality.html#55" class="Datatype Operator"
      >&#8801;</a
      ><a name="2641"
      > </a
      ><a name="2642" href="Maps.html#2417" class="InductiveConstructor"
      >id</a
      ><a name="2644"
      > </a
      ><a name="2645" href="Maps.html#2630" class="Bound"
      >y</a
      ><a name="2646"
      > </a
      ><a name="2647" class="Symbol"
      >&#8594;</a
      ><a name="2648"
      > </a
      ><a name="2649" href="Maps.html#2628" class="Bound"
      >x</a
      ><a name="2650"
      > </a
      ><a name="2651" href="Agda.Builtin.Equality.html#55" class="Datatype Operator"
      >&#8801;</a
      ><a name="2652"
      > </a
      ><a name="2653" href="Maps.html#2630" class="Bound"
      >y</a
      ><a name="2654"
      >
    </a
      ><a name="2659" href="Maps.html#2616" class="Function"
      >id-inj</a
      ><a name="2665"
      > </a
      ><a name="2666" href="Agda.Builtin.Equality.html#112" class="InductiveConstructor"
      >refl</a
      ><a name="2670"
      > </a
      ><a name="2671" class="Symbol"
      >=</a
      ><a name="2672"
      > </a
      ><a name="2673" href="Agda.Builtin.Equality.html#112" class="InductiveConstructor"
      >refl</a
      >
</pre><!--{% endraw %}-->

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

<!--{% raw %}--><pre class="Agda">
<a name="3509" href="Maps.html#3509" class="Function"
      >TotalMap</a
      ><a name="3517"
      > </a
      ><a name="3518" class="Symbol"
      >:</a
      ><a name="3519"
      > </a
      ><a name="3520" class="PrimitiveType"
      >Set</a
      ><a name="3523"
      > </a
      ><a name="3524" class="Symbol"
      >&#8594;</a
      ><a name="3525"
      > </a
      ><a name="3526" class="PrimitiveType"
      >Set</a
      ><a name="3529"
      >
</a
      ><a name="3530" href="Maps.html#3509" class="Function"
      >TotalMap</a
      ><a name="3538"
      > </a
      ><a name="3539" href="Maps.html#3539" class="Bound"
      >A</a
      ><a name="3540"
      > </a
      ><a name="3541" class="Symbol"
      >=</a
      ><a name="3542"
      > </a
      ><a name="3543" href="Maps.html#2400" class="Datatype"
      >Id</a
      ><a name="3545"
      > </a
      ><a name="3546" class="Symbol"
      >&#8594;</a
      ><a name="3547"
      > </a
      ><a name="3548" href="Maps.html#3539" class="Bound"
      >A</a
      >
</pre><!--{% endraw %}-->

Intuitively, a total map over anﬁ element type $$A$$ _is_ just a
function that can be used to look up ids, yielding $$A$$s.

<!--{% raw %}--><pre class="Agda">
<a name="3700" class="Keyword"
      >module</a
      ><a name="3706"
      > </a
      ><a name="3707" href="Maps.html#3707" class="Module"
      >TotalMap</a
      ><a name="3715"
      > </a
      ><a name="3716" class="Keyword"
      >where</a
      >
</pre><!--{% endraw %}-->

The function `empty` yields an empty total map, given a
default element; this map always returns the default element when
applied to any id.

<!--{% raw %}--><pre class="Agda">
  <a name="3891" href="Maps.html#3891" class="Function"
      >empty</a
      ><a name="3896"
      > </a
      ><a name="3897" class="Symbol"
      >:</a
      ><a name="3898"
      > </a
      ><a name="3899" class="Symbol"
      >&#8704;</a
      ><a name="3900"
      > </a
      ><a name="3901" class="Symbol"
      >{</a
      ><a name="3902" href="Maps.html#3902" class="Bound"
      >A</a
      ><a name="3903" class="Symbol"
      >}</a
      ><a name="3904"
      > </a
      ><a name="3905" class="Symbol"
      >&#8594;</a
      ><a name="3906"
      > </a
      ><a name="3907" href="Maps.html#3902" class="Bound"
      >A</a
      ><a name="3908"
      > </a
      ><a name="3909" class="Symbol"
      >&#8594;</a
      ><a name="3910"
      > </a
      ><a name="3911" href="Maps.html#3509" class="Function"
      >TotalMap</a
      ><a name="3919"
      > </a
      ><a name="3920" href="Maps.html#3902" class="Bound"
      >A</a
      ><a name="3921"
      >
  </a
      ><a name="3924" href="Maps.html#3891" class="Function"
      >empty</a
      ><a name="3929"
      > </a
      ><a name="3930" href="Maps.html#3930" class="Bound"
      >x</a
      ><a name="3931"
      > </a
      ><a name="3932" class="Symbol"
      >=</a
      ><a name="3933"
      > </a
      ><a name="3934" class="Symbol"
      >&#955;</a
      ><a name="3935"
      > </a
      ><a name="3936" href="Maps.html#3936" class="Bound"
      >_</a
      ><a name="3937"
      > </a
      ><a name="3938" class="Symbol"
      >&#8594;</a
      ><a name="3939"
      > </a
      ><a name="3940" href="Maps.html#3930" class="Bound"
      >x</a
      >
</pre><!--{% endraw %}-->

More interesting is the `update` function, which (as before) takes
a map $$m$$, a key $$x$$, and a value $$v$$ and returns a new map that
takes $$x$$ to $$v$$ and takes every other key to whatever $$m$$ does.

<!--{% raw %}--><pre class="Agda">
  <a name="4179" href="Maps.html#4179" class="Function"
      >update</a
      ><a name="4185"
      > </a
      ><a name="4186" class="Symbol"
      >:</a
      ><a name="4187"
      > </a
      ><a name="4188" class="Symbol"
      >&#8704;</a
      ><a name="4189"
      > </a
      ><a name="4190" class="Symbol"
      >{</a
      ><a name="4191" href="Maps.html#4191" class="Bound"
      >A</a
      ><a name="4192" class="Symbol"
      >}</a
      ><a name="4193"
      > </a
      ><a name="4194" class="Symbol"
      >&#8594;</a
      ><a name="4195"
      > </a
      ><a name="4196" href="Maps.html#3509" class="Function"
      >TotalMap</a
      ><a name="4204"
      > </a
      ><a name="4205" href="Maps.html#4191" class="Bound"
      >A</a
      ><a name="4206"
      > </a
      ><a name="4207" class="Symbol"
      >-&gt;</a
      ><a name="4209"
      > </a
      ><a name="4210" href="Maps.html#2400" class="Datatype"
      >Id</a
      ><a name="4212"
      > </a
      ><a name="4213" class="Symbol"
      >-&gt;</a
      ><a name="4215"
      > </a
      ><a name="4216" href="Maps.html#4191" class="Bound"
      >A</a
      ><a name="4217"
      > </a
      ><a name="4218" class="Symbol"
      >-&gt;</a
      ><a name="4220"
      > </a
      ><a name="4221" href="Maps.html#3509" class="Function"
      >TotalMap</a
      ><a name="4229"
      > </a
      ><a name="4230" href="Maps.html#4191" class="Bound"
      >A</a
      ><a name="4231"
      >
  </a
      ><a name="4234" href="Maps.html#4179" class="Function"
      >update</a
      ><a name="4240"
      > </a
      ><a name="4241" href="Maps.html#4241" class="Bound"
      >m</a
      ><a name="4242"
      > </a
      ><a name="4243" href="Maps.html#4243" class="Bound"
      >x</a
      ><a name="4244"
      > </a
      ><a name="4245" href="Maps.html#4245" class="Bound"
      >v</a
      ><a name="4246"
      > </a
      ><a name="4247" href="Maps.html#4247" class="Bound"
      >y</a
      ><a name="4248"
      > </a
      ><a name="4249" class="Keyword"
      >with</a
      ><a name="4253"
      > </a
      ><a name="4254" href="Maps.html#4243" class="Bound"
      >x</a
      ><a name="4255"
      > </a
      ><a name="4256" href="Maps.html#2454" class="Function Operator"
      >&#8799;</a
      ><a name="4257"
      > </a
      ><a name="4258" href="Maps.html#4247" class="Bound"
      >y</a
      ><a name="4259"
      >
  </a
      ><a name="4262" class="Symbol"
      >...</a
      ><a name="4265"
      > </a
      ><a name="4266" class="Symbol"
      >|</a
      ><a name="4267"
      > </a
      ><a name="4268" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#520" class="InductiveConstructor"
      >yes</a
      ><a name="4271"
      > </a
      ><a name="4272" href="Maps.html#4272" class="Bound"
      >x=y</a
      ><a name="4275"
      > </a
      ><a name="4276" class="Symbol"
      >=</a
      ><a name="4277"
      > </a
      ><a name="4278" href="Maps.html#4245" class="Bound"
      >v</a
      ><a name="4279"
      >
  </a
      ><a name="4282" class="Symbol"
      >...</a
      ><a name="4285"
      > </a
      ><a name="4286" class="Symbol"
      >|</a
      ><a name="4287"
      > </a
      ><a name="4288" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#547" class="InductiveConstructor"
      >no</a
      ><a name="4290"
      >  </a
      ><a name="4292" href="Maps.html#4292" class="Bound"
      >x&#8800;y</a
      ><a name="4295"
      > </a
      ><a name="4296" class="Symbol"
      >=</a
      ><a name="4297"
      > </a
      ><a name="4298" href="Maps.html#4241" class="Bound"
      >m</a
      ><a name="4299"
      > </a
      ><a name="4300" href="Maps.html#4247" class="Bound"
      >y</a
      >
</pre><!--{% endraw %}-->

This definition is a nice example of higher-order programming.
The `update` function takes a _function_ $$m$$ and yields a new
function $$\lambda x'.\vdots$$ that behaves like the desired map.

For example, we can build a map taking ids to bools, where `id
3` is mapped to `true` and every other key is mapped to `false`,
like this:

<!--{% raw %}--><pre class="Agda">
  <a name="4663" href="Maps.html#4663" class="Function"
      >examplemap</a
      ><a name="4673"
      > </a
      ><a name="4674" class="Symbol"
      >:</a
      ><a name="4675"
      > </a
      ><a name="4676" href="Maps.html#3509" class="Function"
      >TotalMap</a
      ><a name="4684"
      > </a
      ><a name="4685" href="Agda.Builtin.Bool.html#39" class="Datatype"
      >Bool</a
      ><a name="4689"
      >
  </a
      ><a name="4692" href="Maps.html#4663" class="Function"
      >examplemap</a
      ><a name="4702"
      > </a
      ><a name="4703" class="Symbol"
      >=</a
      ><a name="4704"
      > </a
      ><a name="4705" href="Maps.html#4179" class="Function"
      >update</a
      ><a name="4711"
      > </a
      ><a name="4712" class="Symbol"
      >(</a
      ><a name="4713" href="Maps.html#4179" class="Function"
      >update</a
      ><a name="4719"
      > </a
      ><a name="4720" class="Symbol"
      >(</a
      ><a name="4721" href="Maps.html#3891" class="Function"
      >empty</a
      ><a name="4726"
      > </a
      ><a name="4727" href="Agda.Builtin.Bool.html#58" class="InductiveConstructor"
      >false</a
      ><a name="4732" class="Symbol"
      >)</a
      ><a name="4733"
      > </a
      ><a name="4734" class="Symbol"
      >(</a
      ><a name="4735" href="Maps.html#2417" class="InductiveConstructor"
      >id</a
      ><a name="4737"
      > </a
      ><a name="4738" class="Number"
      >1</a
      ><a name="4739" class="Symbol"
      >)</a
      ><a name="4740"
      > </a
      ><a name="4741" href="Agda.Builtin.Bool.html#58" class="InductiveConstructor"
      >false</a
      ><a name="4746" class="Symbol"
      >)</a
      ><a name="4747"
      > </a
      ><a name="4748" class="Symbol"
      >(</a
      ><a name="4749" href="Maps.html#2417" class="InductiveConstructor"
      >id</a
      ><a name="4751"
      > </a
      ><a name="4752" class="Number"
      >3</a
      ><a name="4753" class="Symbol"
      >)</a
      ><a name="4754"
      > </a
      ><a name="4755" href="Agda.Builtin.Bool.html#64" class="InductiveConstructor"
      >true</a
      >
</pre><!--{% endraw %}-->

This completes the definition of total maps.  Note that we don't
need to define a `find` operation because it is just function
application!

<!--{% raw %}--><pre class="Agda">
  <a name="4928" href="Maps.html#4928" class="Function Operator"
      >test_examplemap0</a
      ><a name="4944"
      > </a
      ><a name="4945" class="Symbol"
      >:</a
      ><a name="4946"
      > </a
      ><a name="4947" href="Maps.html#4663" class="Function"
      >examplemap</a
      ><a name="4957"
      > </a
      ><a name="4958" class="Symbol"
      >(</a
      ><a name="4959" href="Maps.html#2417" class="InductiveConstructor"
      >id</a
      ><a name="4961"
      > </a
      ><a name="4962" class="Number"
      >0</a
      ><a name="4963" class="Symbol"
      >)</a
      ><a name="4964"
      > </a
      ><a name="4965" href="Agda.Builtin.Equality.html#55" class="Datatype Operator"
      >&#8801;</a
      ><a name="4966"
      > </a
      ><a name="4967" href="Agda.Builtin.Bool.html#58" class="InductiveConstructor"
      >false</a
      ><a name="4972"
      >
  </a
      ><a name="4975" href="Maps.html#4928" class="Function Operator"
      >test_examplemap0</a
      ><a name="4991"
      > </a
      ><a name="4992" class="Symbol"
      >=</a
      ><a name="4993"
      > </a
      ><a name="4994" href="Agda.Builtin.Equality.html#112" class="InductiveConstructor"
      >refl</a
      ><a name="4998"
      >

  </a
      ><a name="5002" href="Maps.html#5002" class="Function Operator"
      >test_examplemap1</a
      ><a name="5018"
      > </a
      ><a name="5019" class="Symbol"
      >:</a
      ><a name="5020"
      > </a
      ><a name="5021" href="Maps.html#4663" class="Function"
      >examplemap</a
      ><a name="5031"
      > </a
      ><a name="5032" class="Symbol"
      >(</a
      ><a name="5033" href="Maps.html#2417" class="InductiveConstructor"
      >id</a
      ><a name="5035"
      > </a
      ><a name="5036" class="Number"
      >1</a
      ><a name="5037" class="Symbol"
      >)</a
      ><a name="5038"
      > </a
      ><a name="5039" href="Agda.Builtin.Equality.html#55" class="Datatype Operator"
      >&#8801;</a
      ><a name="5040"
      > </a
      ><a name="5041" href="Agda.Builtin.Bool.html#58" class="InductiveConstructor"
      >false</a
      ><a name="5046"
      >
  </a
      ><a name="5049" href="Maps.html#5002" class="Function Operator"
      >test_examplemap1</a
      ><a name="5065"
      > </a
      ><a name="5066" class="Symbol"
      >=</a
      ><a name="5067"
      > </a
      ><a name="5068" href="Agda.Builtin.Equality.html#112" class="InductiveConstructor"
      >refl</a
      ><a name="5072"
      >

  </a
      ><a name="5076" href="Maps.html#5076" class="Function Operator"
      >test_examplemap2</a
      ><a name="5092"
      > </a
      ><a name="5093" class="Symbol"
      >:</a
      ><a name="5094"
      > </a
      ><a name="5095" href="Maps.html#4663" class="Function"
      >examplemap</a
      ><a name="5105"
      > </a
      ><a name="5106" class="Symbol"
      >(</a
      ><a name="5107" href="Maps.html#2417" class="InductiveConstructor"
      >id</a
      ><a name="5109"
      > </a
      ><a name="5110" class="Number"
      >2</a
      ><a name="5111" class="Symbol"
      >)</a
      ><a name="5112"
      > </a
      ><a name="5113" href="Agda.Builtin.Equality.html#55" class="Datatype Operator"
      >&#8801;</a
      ><a name="5114"
      > </a
      ><a name="5115" href="Agda.Builtin.Bool.html#58" class="InductiveConstructor"
      >false</a
      ><a name="5120"
      >
  </a
      ><a name="5123" href="Maps.html#5076" class="Function Operator"
      >test_examplemap2</a
      ><a name="5139"
      > </a
      ><a name="5140" class="Symbol"
      >=</a
      ><a name="5141"
      > </a
      ><a name="5142" href="Agda.Builtin.Equality.html#112" class="InductiveConstructor"
      >refl</a
      ><a name="5146"
      >

  </a
      ><a name="5150" href="Maps.html#5150" class="Function Operator"
      >test_examplemap3</a
      ><a name="5166"
      > </a
      ><a name="5167" class="Symbol"
      >:</a
      ><a name="5168"
      > </a
      ><a name="5169" href="Maps.html#4663" class="Function"
      >examplemap</a
      ><a name="5179"
      > </a
      ><a name="5180" class="Symbol"
      >(</a
      ><a name="5181" href="Maps.html#2417" class="InductiveConstructor"
      >id</a
      ><a name="5183"
      > </a
      ><a name="5184" class="Number"
      >3</a
      ><a name="5185" class="Symbol"
      >)</a
      ><a name="5186"
      > </a
      ><a name="5187" href="Agda.Builtin.Equality.html#55" class="Datatype Operator"
      >&#8801;</a
      ><a name="5188"
      > </a
      ><a name="5189" href="Agda.Builtin.Bool.html#64" class="InductiveConstructor"
      >true</a
      ><a name="5193"
      >
  </a
      ><a name="5196" href="Maps.html#5150" class="Function Operator"
      >test_examplemap3</a
      ><a name="5212"
      > </a
      ><a name="5213" class="Symbol"
      >=</a
      ><a name="5214"
      > </a
      ><a name="5215" href="Agda.Builtin.Equality.html#112" class="InductiveConstructor"
      >refl</a
      >
</pre><!--{% endraw %}-->

To use maps in later chapters, we'll need several fundamental
facts about how they behave.  Even if you don't work the following
exercises, make sure you thoroughly understand the statements of
the lemmas!  (Some of the proofs require the functional
extensionality axiom, which is discussed in the [Logic]
chapter and included in the Agda standard library.)

#### Exercise: 1 star, optional (apply-empty)
First, the empty map returns its default element for all keys:

<!--{% raw %}--><pre class="Agda">
  <a name="5716" class="Keyword"
      >postulate</a
      ><a name="5725"
      >
    </a
      ><a name="5730" href="Maps.html#5730" class="Postulate"
      >apply-empty</a
      ><a name="5741"
      > </a
      ><a name="5742" class="Symbol"
      >:</a
      ><a name="5743"
      > </a
      ><a name="5744" class="Symbol"
      >&#8704;</a
      ><a name="5745"
      > </a
      ><a name="5746" class="Symbol"
      >{</a
      ><a name="5747" href="Maps.html#5747" class="Bound"
      >A</a
      ><a name="5748"
      > </a
      ><a name="5749" href="Maps.html#5749" class="Bound"
      >x</a
      ><a name="5750"
      > </a
      ><a name="5751" href="Maps.html#5751" class="Bound"
      >v</a
      ><a name="5752" class="Symbol"
      >}</a
      ><a name="5753"
      > </a
      ><a name="5754" class="Symbol"
      >&#8594;</a
      ><a name="5755"
      > </a
      ><a name="5756" href="Maps.html#3891" class="Function"
      >empty</a
      ><a name="5761"
      > </a
      ><a name="5762" class="Symbol"
      >{</a
      ><a name="5763" href="Maps.html#5747" class="Bound"
      >A</a
      ><a name="5764" class="Symbol"
      >}</a
      ><a name="5765"
      > </a
      ><a name="5766" href="Maps.html#5751" class="Bound"
      >v</a
      ><a name="5767"
      > </a
      ><a name="5768" href="Maps.html#5749" class="Bound"
      >x</a
      ><a name="5769"
      > </a
      ><a name="5770" href="Agda.Builtin.Equality.html#55" class="Datatype Operator"
      >&#8801;</a
      ><a name="5771"
      > </a
      ><a name="5772" href="Maps.html#5751" class="Bound"
      >v</a
      >
</pre><!--{% endraw %}-->

<div class="hidden">
<!--{% raw %}--><pre class="Agda">
  <a name="5822" href="Maps.html#5822" class="Function"
      >apply-empty&#8242;</a
      ><a name="5834"
      > </a
      ><a name="5835" class="Symbol"
      >:</a
      ><a name="5836"
      > </a
      ><a name="5837" class="Symbol"
      >&#8704;</a
      ><a name="5838"
      > </a
      ><a name="5839" class="Symbol"
      >{</a
      ><a name="5840" href="Maps.html#5840" class="Bound"
      >A</a
      ><a name="5841"
      > </a
      ><a name="5842" href="Maps.html#5842" class="Bound"
      >x</a
      ><a name="5843"
      > </a
      ><a name="5844" href="Maps.html#5844" class="Bound"
      >v</a
      ><a name="5845" class="Symbol"
      >}</a
      ><a name="5846"
      > </a
      ><a name="5847" class="Symbol"
      >&#8594;</a
      ><a name="5848"
      > </a
      ><a name="5849" href="Maps.html#3891" class="Function"
      >empty</a
      ><a name="5854"
      > </a
      ><a name="5855" class="Symbol"
      >{</a
      ><a name="5856" href="Maps.html#5840" class="Bound"
      >A</a
      ><a name="5857" class="Symbol"
      >}</a
      ><a name="5858"
      > </a
      ><a name="5859" href="Maps.html#5844" class="Bound"
      >v</a
      ><a name="5860"
      > </a
      ><a name="5861" href="Maps.html#5842" class="Bound"
      >x</a
      ><a name="5862"
      > </a
      ><a name="5863" href="Agda.Builtin.Equality.html#55" class="Datatype Operator"
      >&#8801;</a
      ><a name="5864"
      > </a
      ><a name="5865" href="Maps.html#5844" class="Bound"
      >v</a
      ><a name="5866"
      >
  </a
      ><a name="5869" href="Maps.html#5822" class="Function"
      >apply-empty&#8242;</a
      ><a name="5881"
      > </a
      ><a name="5882" class="Symbol"
      >=</a
      ><a name="5883"
      > </a
      ><a name="5884" href="Agda.Builtin.Equality.html#112" class="InductiveConstructor"
      >refl</a
      >
</pre><!--{% endraw %}-->
</div>

#### Exercise: 2 stars, optional (update-eq)
Next, if we update a map $$m$$ at a key $$x$$ with a new value $$v$$
and then look up $$x$$ in the map resulting from the `update`, we get
back $$v$$:

<!--{% raw %}--><pre class="Agda">
  <a name="6120" class="Keyword"
      >postulate</a
      ><a name="6129"
      >
    </a
      ><a name="6134" href="Maps.html#6134" class="Postulate"
      >update-eq</a
      ><a name="6143"
      > </a
      ><a name="6144" class="Symbol"
      >:</a
      ><a name="6145"
      > </a
      ><a name="6146" class="Symbol"
      >&#8704;</a
      ><a name="6147"
      > </a
      ><a name="6148" class="Symbol"
      >{</a
      ><a name="6149" href="Maps.html#6149" class="Bound"
      >A</a
      ><a name="6150"
      > </a
      ><a name="6151" href="Maps.html#6151" class="Bound"
      >v</a
      ><a name="6152" class="Symbol"
      >}</a
      ><a name="6153"
      > </a
      ><a name="6154" class="Symbol"
      >(</a
      ><a name="6155" href="Maps.html#6155" class="Bound"
      >m</a
      ><a name="6156"
      > </a
      ><a name="6157" class="Symbol"
      >:</a
      ><a name="6158"
      > </a
      ><a name="6159" href="Maps.html#3509" class="Function"
      >TotalMap</a
      ><a name="6167"
      > </a
      ><a name="6168" href="Maps.html#6149" class="Bound"
      >A</a
      ><a name="6169" class="Symbol"
      >)</a
      ><a name="6170"
      > </a
      ><a name="6171" class="Symbol"
      >(</a
      ><a name="6172" href="Maps.html#6172" class="Bound"
      >x</a
      ><a name="6173"
      > </a
      ><a name="6174" class="Symbol"
      >:</a
      ><a name="6175"
      > </a
      ><a name="6176" href="Maps.html#2400" class="Datatype"
      >Id</a
      ><a name="6178" class="Symbol"
      >)</a
      ><a name="6179"
      >
              </a
      ><a name="6194" class="Symbol"
      >&#8594;</a
      ><a name="6195"
      > </a
      ><a name="6196" class="Symbol"
      >(</a
      ><a name="6197" href="Maps.html#4179" class="Function"
      >update</a
      ><a name="6203"
      > </a
      ><a name="6204" href="Maps.html#6155" class="Bound"
      >m</a
      ><a name="6205"
      > </a
      ><a name="6206" href="Maps.html#6172" class="Bound"
      >x</a
      ><a name="6207"
      > </a
      ><a name="6208" href="Maps.html#6151" class="Bound"
      >v</a
      ><a name="6209" class="Symbol"
      >)</a
      ><a name="6210"
      > </a
      ><a name="6211" href="Maps.html#6172" class="Bound"
      >x</a
      ><a name="6212"
      > </a
      ><a name="6213" href="Agda.Builtin.Equality.html#55" class="Datatype Operator"
      >&#8801;</a
      ><a name="6214"
      > </a
      ><a name="6215" href="Maps.html#6151" class="Bound"
      >v</a
      >
</pre><!--{% endraw %}-->

<div class="hidden">
<!--{% raw %}--><pre class="Agda">
  <a name="6265" href="Maps.html#6265" class="Function"
      >update-eq&#8242;</a
      ><a name="6275"
      > </a
      ><a name="6276" class="Symbol"
      >:</a
      ><a name="6277"
      > </a
      ><a name="6278" class="Symbol"
      >&#8704;</a
      ><a name="6279"
      > </a
      ><a name="6280" class="Symbol"
      >{</a
      ><a name="6281" href="Maps.html#6281" class="Bound"
      >A</a
      ><a name="6282"
      > </a
      ><a name="6283" href="Maps.html#6283" class="Bound"
      >v</a
      ><a name="6284" class="Symbol"
      >}</a
      ><a name="6285"
      > </a
      ><a name="6286" class="Symbol"
      >(</a
      ><a name="6287" href="Maps.html#6287" class="Bound"
      >m</a
      ><a name="6288"
      > </a
      ><a name="6289" class="Symbol"
      >:</a
      ><a name="6290"
      > </a
      ><a name="6291" href="Maps.html#3509" class="Function"
      >TotalMap</a
      ><a name="6299"
      > </a
      ><a name="6300" href="Maps.html#6281" class="Bound"
      >A</a
      ><a name="6301" class="Symbol"
      >)</a
      ><a name="6302"
      > </a
      ><a name="6303" class="Symbol"
      >(</a
      ><a name="6304" href="Maps.html#6304" class="Bound"
      >x</a
      ><a name="6305"
      > </a
      ><a name="6306" class="Symbol"
      >:</a
      ><a name="6307"
      > </a
      ><a name="6308" href="Maps.html#2400" class="Datatype"
      >Id</a
      ><a name="6310" class="Symbol"
      >)</a
      ><a name="6311"
      >
             </a
      ><a name="6325" class="Symbol"
      >&#8594;</a
      ><a name="6326"
      > </a
      ><a name="6327" class="Symbol"
      >(</a
      ><a name="6328" href="Maps.html#4179" class="Function"
      >update</a
      ><a name="6334"
      > </a
      ><a name="6335" href="Maps.html#6287" class="Bound"
      >m</a
      ><a name="6336"
      > </a
      ><a name="6337" href="Maps.html#6304" class="Bound"
      >x</a
      ><a name="6338"
      > </a
      ><a name="6339" href="Maps.html#6283" class="Bound"
      >v</a
      ><a name="6340" class="Symbol"
      >)</a
      ><a name="6341"
      > </a
      ><a name="6342" href="Maps.html#6304" class="Bound"
      >x</a
      ><a name="6343"
      > </a
      ><a name="6344" href="Agda.Builtin.Equality.html#55" class="Datatype Operator"
      >&#8801;</a
      ><a name="6345"
      > </a
      ><a name="6346" href="Maps.html#6283" class="Bound"
      >v</a
      ><a name="6347"
      >
  </a
      ><a name="6350" href="Maps.html#6265" class="Function"
      >update-eq&#8242;</a
      ><a name="6360"
      > </a
      ><a name="6361" href="Maps.html#6361" class="Bound"
      >m</a
      ><a name="6362"
      > </a
      ><a name="6363" href="Maps.html#6363" class="Bound"
      >x</a
      ><a name="6364"
      > </a
      ><a name="6365" class="Keyword"
      >with</a
      ><a name="6369"
      > </a
      ><a name="6370" href="Maps.html#6363" class="Bound"
      >x</a
      ><a name="6371"
      > </a
      ><a name="6372" href="Maps.html#2454" class="Function Operator"
      >&#8799;</a
      ><a name="6373"
      > </a
      ><a name="6374" href="Maps.html#6363" class="Bound"
      >x</a
      ><a name="6375"
      >
  </a
      ><a name="6378" class="Symbol"
      >...</a
      ><a name="6381"
      > </a
      ><a name="6382" class="Symbol"
      >|</a
      ><a name="6383"
      > </a
      ><a name="6384" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#520" class="InductiveConstructor"
      >yes</a
      ><a name="6387"
      > </a
      ><a name="6388" href="Maps.html#6388" class="Bound"
      >x=x</a
      ><a name="6391"
      > </a
      ><a name="6392" class="Symbol"
      >=</a
      ><a name="6393"
      > </a
      ><a name="6394" href="Agda.Builtin.Equality.html#112" class="InductiveConstructor"
      >refl</a
      ><a name="6398"
      >
  </a
      ><a name="6401" class="Symbol"
      >...</a
      ><a name="6404"
      > </a
      ><a name="6405" class="Symbol"
      >|</a
      ><a name="6406"
      > </a
      ><a name="6407" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#547" class="InductiveConstructor"
      >no</a
      ><a name="6409"
      >  </a
      ><a name="6411" href="Maps.html#6411" class="Bound"
      >x&#8800;x</a
      ><a name="6414"
      > </a
      ><a name="6415" class="Symbol"
      >=</a
      ><a name="6416"
      > </a
      ><a name="6417" href="https://agda.github.io/agda-stdlib/Data.Empty.html#348" class="Function"
      >&#8869;-elim</a
      ><a name="6423"
      > </a
      ><a name="6424" class="Symbol"
      >(</a
      ><a name="6425" href="Maps.html#6411" class="Bound"
      >x&#8800;x</a
      ><a name="6428"
      > </a
      ><a name="6429" href="Agda.Builtin.Equality.html#112" class="InductiveConstructor"
      >refl</a
      ><a name="6433" class="Symbol"
      >)</a
      >
</pre><!--{% endraw %}-->
</div>

#### Exercise: 2 stars, optional (update-neq)
On the other hand, if we update a map $$m$$ at a key $$x$$ and
then look up a _different_ key $$y$$ in the resulting map, we get
the same result that $$m$$ would have given:

<!--{% raw %}--><pre class="Agda">
  <a name="6690" href="Maps.html#6690" class="Function"
      >update-neq</a
      ><a name="6700"
      > </a
      ><a name="6701" class="Symbol"
      >:</a
      ><a name="6702"
      > </a
      ><a name="6703" class="Symbol"
      >&#8704;</a
      ><a name="6704"
      > </a
      ><a name="6705" class="Symbol"
      >{</a
      ><a name="6706" href="Maps.html#6706" class="Bound"
      >A</a
      ><a name="6707"
      > </a
      ><a name="6708" href="Maps.html#6708" class="Bound"
      >v</a
      ><a name="6709" class="Symbol"
      >}</a
      ><a name="6710"
      > </a
      ><a name="6711" class="Symbol"
      >(</a
      ><a name="6712" href="Maps.html#6712" class="Bound"
      >m</a
      ><a name="6713"
      > </a
      ><a name="6714" class="Symbol"
      >:</a
      ><a name="6715"
      > </a
      ><a name="6716" href="Maps.html#3509" class="Function"
      >TotalMap</a
      ><a name="6724"
      > </a
      ><a name="6725" href="Maps.html#6706" class="Bound"
      >A</a
      ><a name="6726" class="Symbol"
      >)</a
      ><a name="6727"
      > </a
      ><a name="6728" class="Symbol"
      >(</a
      ><a name="6729" href="Maps.html#6729" class="Bound"
      >x</a
      ><a name="6730"
      > </a
      ><a name="6731" href="Maps.html#6731" class="Bound"
      >y</a
      ><a name="6732"
      > </a
      ><a name="6733" class="Symbol"
      >:</a
      ><a name="6734"
      > </a
      ><a name="6735" href="Maps.html#2400" class="Datatype"
      >Id</a
      ><a name="6737" class="Symbol"
      >)</a
      ><a name="6738"
      >
             </a
      ><a name="6752" class="Symbol"
      >&#8594;</a
      ><a name="6753"
      > </a
      ><a name="6754" href="Maps.html#6729" class="Bound"
      >x</a
      ><a name="6755"
      > </a
      ><a name="6756" href="https://agda.github.io/agda-stdlib/Relation.Binary.Core.html#4493" class="Function Operator"
      >&#8802;</a
      ><a name="6757"
      > </a
      ><a name="6758" href="Maps.html#6731" class="Bound"
      >y</a
      ><a name="6759"
      > </a
      ><a name="6760" class="Symbol"
      >&#8594;</a
      ><a name="6761"
      > </a
      ><a name="6762" class="Symbol"
      >(</a
      ><a name="6763" href="Maps.html#4179" class="Function"
      >update</a
      ><a name="6769"
      > </a
      ><a name="6770" href="Maps.html#6712" class="Bound"
      >m</a
      ><a name="6771"
      > </a
      ><a name="6772" href="Maps.html#6729" class="Bound"
      >x</a
      ><a name="6773"
      > </a
      ><a name="6774" href="Maps.html#6708" class="Bound"
      >v</a
      ><a name="6775" class="Symbol"
      >)</a
      ><a name="6776"
      > </a
      ><a name="6777" href="Maps.html#6731" class="Bound"
      >y</a
      ><a name="6778"
      > </a
      ><a name="6779" href="Agda.Builtin.Equality.html#55" class="Datatype Operator"
      >&#8801;</a
      ><a name="6780"
      > </a
      ><a name="6781" href="Maps.html#6712" class="Bound"
      >m</a
      ><a name="6782"
      > </a
      ><a name="6783" href="Maps.html#6731" class="Bound"
      >y</a
      ><a name="6784"
      >
  </a
      ><a name="6787" href="Maps.html#6690" class="Function"
      >update-neq</a
      ><a name="6797"
      > </a
      ><a name="6798" href="Maps.html#6798" class="Bound"
      >m</a
      ><a name="6799"
      > </a
      ><a name="6800" href="Maps.html#6800" class="Bound"
      >x</a
      ><a name="6801"
      > </a
      ><a name="6802" href="Maps.html#6802" class="Bound"
      >y</a
      ><a name="6803"
      > </a
      ><a name="6804" href="Maps.html#6804" class="Bound"
      >x&#8800;y</a
      ><a name="6807"
      > </a
      ><a name="6808" class="Keyword"
      >with</a
      ><a name="6812"
      > </a
      ><a name="6813" href="Maps.html#6800" class="Bound"
      >x</a
      ><a name="6814"
      > </a
      ><a name="6815" href="Maps.html#2454" class="Function Operator"
      >&#8799;</a
      ><a name="6816"
      > </a
      ><a name="6817" href="Maps.html#6802" class="Bound"
      >y</a
      ><a name="6818"
      >
  </a
      ><a name="6821" class="Symbol"
      >...</a
      ><a name="6824"
      > </a
      ><a name="6825" class="Symbol"
      >|</a
      ><a name="6826"
      > </a
      ><a name="6827" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#520" class="InductiveConstructor"
      >yes</a
      ><a name="6830"
      > </a
      ><a name="6831" href="Maps.html#6831" class="Bound"
      >x=y</a
      ><a name="6834"
      > </a
      ><a name="6835" class="Symbol"
      >=</a
      ><a name="6836"
      > </a
      ><a name="6837" href="https://agda.github.io/agda-stdlib/Data.Empty.html#348" class="Function"
      >&#8869;-elim</a
      ><a name="6843"
      > </a
      ><a name="6844" class="Symbol"
      >(</a
      ><a name="6845" href="Maps.html#6804" class="Bound"
      >x&#8800;y</a
      ><a name="6848"
      > </a
      ><a name="6849" href="Maps.html#6831" class="Bound"
      >x=y</a
      ><a name="6852" class="Symbol"
      >)</a
      ><a name="6853"
      >
  </a
      ><a name="6856" class="Symbol"
      >...</a
      ><a name="6859"
      > </a
      ><a name="6860" class="Symbol"
      >|</a
      ><a name="6861"
      > </a
      ><a name="6862" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#547" class="InductiveConstructor"
      >no</a
      ><a name="6864"
      >  </a
      ><a name="6866" class="Symbol"
      >_</a
      ><a name="6867"
      >   </a
      ><a name="6870" class="Symbol"
      >=</a
      ><a name="6871"
      > </a
      ><a name="6872" href="Agda.Builtin.Equality.html#112" class="InductiveConstructor"
      >refl</a
      >
</pre><!--{% endraw %}-->

#### Exercise: 2 stars, optional (update-shadow)
If we update a map $$m$$ at a key $$x$$ with a value $$v_1$$ and then
update again with the same key $$x$$ and another value $$v_2$$, the
resulting map behaves the same (gives the same result when applied
to any key) as the simpler map obtained by performing just
the second `update` on $$m$$:

<!--{% raw %}--><pre class="Agda">
  <a name="7248" class="Keyword"
      >postulate</a
      ><a name="7257"
      >
    </a
      ><a name="7262" href="Maps.html#7262" class="Postulate"
      >update-shadow</a
      ><a name="7275"
      > </a
      ><a name="7276" class="Symbol"
      >:</a
      ><a name="7277"
      > </a
      ><a name="7278" class="Symbol"
      >&#8704;</a
      ><a name="7279"
      > </a
      ><a name="7280" class="Symbol"
      >{</a
      ><a name="7281" href="Maps.html#7281" class="Bound"
      >A</a
      ><a name="7282"
      > </a
      ><a name="7283" href="Maps.html#7283" class="Bound"
      >v1</a
      ><a name="7285"
      > </a
      ><a name="7286" href="Maps.html#7286" class="Bound"
      >v2</a
      ><a name="7288" class="Symbol"
      >}</a
      ><a name="7289"
      > </a
      ><a name="7290" class="Symbol"
      >(</a
      ><a name="7291" href="Maps.html#7291" class="Bound"
      >m</a
      ><a name="7292"
      > </a
      ><a name="7293" class="Symbol"
      >:</a
      ><a name="7294"
      > </a
      ><a name="7295" href="Maps.html#3509" class="Function"
      >TotalMap</a
      ><a name="7303"
      > </a
      ><a name="7304" href="Maps.html#7281" class="Bound"
      >A</a
      ><a name="7305" class="Symbol"
      >)</a
      ><a name="7306"
      > </a
      ><a name="7307" class="Symbol"
      >(</a
      ><a name="7308" href="Maps.html#7308" class="Bound"
      >x</a
      ><a name="7309"
      > </a
      ><a name="7310" href="Maps.html#7310" class="Bound"
      >y</a
      ><a name="7311"
      > </a
      ><a name="7312" class="Symbol"
      >:</a
      ><a name="7313"
      > </a
      ><a name="7314" href="Maps.html#2400" class="Datatype"
      >Id</a
      ><a name="7316" class="Symbol"
      >)</a
      ><a name="7317"
      >
                  </a
      ><a name="7336" class="Symbol"
      >&#8594;</a
      ><a name="7337"
      > </a
      ><a name="7338" class="Symbol"
      >(</a
      ><a name="7339" href="Maps.html#4179" class="Function"
      >update</a
      ><a name="7345"
      > </a
      ><a name="7346" class="Symbol"
      >(</a
      ><a name="7347" href="Maps.html#4179" class="Function"
      >update</a
      ><a name="7353"
      > </a
      ><a name="7354" href="Maps.html#7291" class="Bound"
      >m</a
      ><a name="7355"
      > </a
      ><a name="7356" href="Maps.html#7308" class="Bound"
      >x</a
      ><a name="7357"
      > </a
      ><a name="7358" href="Maps.html#7283" class="Bound"
      >v1</a
      ><a name="7360" class="Symbol"
      >)</a
      ><a name="7361"
      > </a
      ><a name="7362" href="Maps.html#7308" class="Bound"
      >x</a
      ><a name="7363"
      > </a
      ><a name="7364" href="Maps.html#7286" class="Bound"
      >v2</a
      ><a name="7366" class="Symbol"
      >)</a
      ><a name="7367"
      > </a
      ><a name="7368" href="Maps.html#7310" class="Bound"
      >y</a
      ><a name="7369"
      > </a
      ><a name="7370" href="Agda.Builtin.Equality.html#55" class="Datatype Operator"
      >&#8801;</a
      ><a name="7371"
      > </a
      ><a name="7372" class="Symbol"
      >(</a
      ><a name="7373" href="Maps.html#4179" class="Function"
      >update</a
      ><a name="7379"
      > </a
      ><a name="7380" href="Maps.html#7291" class="Bound"
      >m</a
      ><a name="7381"
      > </a
      ><a name="7382" href="Maps.html#7308" class="Bound"
      >x</a
      ><a name="7383"
      > </a
      ><a name="7384" href="Maps.html#7286" class="Bound"
      >v2</a
      ><a name="7386" class="Symbol"
      >)</a
      ><a name="7387"
      > </a
      ><a name="7388" href="Maps.html#7310" class="Bound"
      >y</a
      >
</pre><!--{% endraw %}-->

<div class="hidden">
<!--{% raw %}--><pre class="Agda">
  <a name="7438" href="Maps.html#7438" class="Function"
      >update-shadow&#8242;</a
      ><a name="7452"
      > </a
      ><a name="7453" class="Symbol"
      >:</a
      ><a name="7454"
      > </a
      ><a name="7455" class="Symbol"
      >&#8704;</a
      ><a name="7456"
      > </a
      ><a name="7457" class="Symbol"
      >{</a
      ><a name="7458" href="Maps.html#7458" class="Bound"
      >A</a
      ><a name="7459"
      > </a
      ><a name="7460" href="Maps.html#7460" class="Bound"
      >v1</a
      ><a name="7462"
      > </a
      ><a name="7463" href="Maps.html#7463" class="Bound"
      >v2</a
      ><a name="7465" class="Symbol"
      >}</a
      ><a name="7466"
      > </a
      ><a name="7467" class="Symbol"
      >(</a
      ><a name="7468" href="Maps.html#7468" class="Bound"
      >m</a
      ><a name="7469"
      > </a
      ><a name="7470" class="Symbol"
      >:</a
      ><a name="7471"
      > </a
      ><a name="7472" href="Maps.html#3509" class="Function"
      >TotalMap</a
      ><a name="7480"
      > </a
      ><a name="7481" href="Maps.html#7458" class="Bound"
      >A</a
      ><a name="7482" class="Symbol"
      >)</a
      ><a name="7483"
      > </a
      ><a name="7484" class="Symbol"
      >(</a
      ><a name="7485" href="Maps.html#7485" class="Bound"
      >x</a
      ><a name="7486"
      > </a
      ><a name="7487" href="Maps.html#7487" class="Bound"
      >y</a
      ><a name="7488"
      > </a
      ><a name="7489" class="Symbol"
      >:</a
      ><a name="7490"
      > </a
      ><a name="7491" href="Maps.html#2400" class="Datatype"
      >Id</a
      ><a name="7493" class="Symbol"
      >)</a
      ><a name="7494"
      >
                 </a
      ><a name="7512" class="Symbol"
      >&#8594;</a
      ><a name="7513"
      > </a
      ><a name="7514" class="Symbol"
      >(</a
      ><a name="7515" href="Maps.html#4179" class="Function"
      >update</a
      ><a name="7521"
      > </a
      ><a name="7522" class="Symbol"
      >(</a
      ><a name="7523" href="Maps.html#4179" class="Function"
      >update</a
      ><a name="7529"
      > </a
      ><a name="7530" href="Maps.html#7468" class="Bound"
      >m</a
      ><a name="7531"
      > </a
      ><a name="7532" href="Maps.html#7485" class="Bound"
      >x</a
      ><a name="7533"
      > </a
      ><a name="7534" href="Maps.html#7460" class="Bound"
      >v1</a
      ><a name="7536" class="Symbol"
      >)</a
      ><a name="7537"
      > </a
      ><a name="7538" href="Maps.html#7485" class="Bound"
      >x</a
      ><a name="7539"
      > </a
      ><a name="7540" href="Maps.html#7463" class="Bound"
      >v2</a
      ><a name="7542" class="Symbol"
      >)</a
      ><a name="7543"
      > </a
      ><a name="7544" href="Maps.html#7487" class="Bound"
      >y</a
      ><a name="7545"
      > </a
      ><a name="7546" href="Agda.Builtin.Equality.html#55" class="Datatype Operator"
      >&#8801;</a
      ><a name="7547"
      > </a
      ><a name="7548" class="Symbol"
      >(</a
      ><a name="7549" href="Maps.html#4179" class="Function"
      >update</a
      ><a name="7555"
      > </a
      ><a name="7556" href="Maps.html#7468" class="Bound"
      >m</a
      ><a name="7557"
      > </a
      ><a name="7558" href="Maps.html#7485" class="Bound"
      >x</a
      ><a name="7559"
      > </a
      ><a name="7560" href="Maps.html#7463" class="Bound"
      >v2</a
      ><a name="7562" class="Symbol"
      >)</a
      ><a name="7563"
      > </a
      ><a name="7564" href="Maps.html#7487" class="Bound"
      >y</a
      ><a name="7565"
      >
  </a
      ><a name="7568" href="Maps.html#7438" class="Function"
      >update-shadow&#8242;</a
      ><a name="7582"
      > </a
      ><a name="7583" href="Maps.html#7583" class="Bound"
      >m</a
      ><a name="7584"
      > </a
      ><a name="7585" href="Maps.html#7585" class="Bound"
      >x</a
      ><a name="7586"
      > </a
      ><a name="7587" href="Maps.html#7587" class="Bound"
      >y</a
      ><a name="7588"
      >
      </a
      ><a name="7595" class="Keyword"
      >with</a
      ><a name="7599"
      > </a
      ><a name="7600" href="Maps.html#7585" class="Bound"
      >x</a
      ><a name="7601"
      > </a
      ><a name="7602" href="Maps.html#2454" class="Function Operator"
      >&#8799;</a
      ><a name="7603"
      > </a
      ><a name="7604" href="Maps.html#7587" class="Bound"
      >y</a
      ><a name="7605"
      >
  </a
      ><a name="7608" class="Symbol"
      >...</a
      ><a name="7611"
      > </a
      ><a name="7612" class="Symbol"
      >|</a
      ><a name="7613"
      > </a
      ><a name="7614" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#520" class="InductiveConstructor"
      >yes</a
      ><a name="7617"
      > </a
      ><a name="7618" href="Maps.html#7618" class="Bound"
      >x=y</a
      ><a name="7621"
      > </a
      ><a name="7622" class="Symbol"
      >=</a
      ><a name="7623"
      > </a
      ><a name="7624" href="Agda.Builtin.Equality.html#112" class="InductiveConstructor"
      >refl</a
      ><a name="7628"
      >
  </a
      ><a name="7631" class="Symbol"
      >...</a
      ><a name="7634"
      > </a
      ><a name="7635" class="Symbol"
      >|</a
      ><a name="7636"
      > </a
      ><a name="7637" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#547" class="InductiveConstructor"
      >no</a
      ><a name="7639"
      >  </a
      ><a name="7641" href="Maps.html#7641" class="Bound"
      >x&#8800;y</a
      ><a name="7644"
      > </a
      ><a name="7645" class="Symbol"
      >=</a
      ><a name="7646"
      > </a
      ><a name="7647" href="Maps.html#6690" class="Function"
      >update-neq</a
      ><a name="7657"
      > </a
      ><a name="7658" href="Maps.html#7583" class="Bound"
      >m</a
      ><a name="7659"
      > </a
      ><a name="7660" href="Maps.html#7585" class="Bound"
      >x</a
      ><a name="7661"
      > </a
      ><a name="7662" href="Maps.html#7587" class="Bound"
      >y</a
      ><a name="7663"
      > </a
      ><a name="7664" href="Maps.html#7641" class="Bound"
      >x&#8800;y</a
      >
</pre><!--{% endraw %}-->
</div>

#### Exercise: 2 stars (update-same)
Prove the following theorem, which states that if we update a map to
assign key $$x$$ the same value as it already has in $$m$$, then the
result is equal to $$m$$:

<!--{% raw %}--><pre class="Agda">
  <a name="7904" class="Keyword"
      >postulate</a
      ><a name="7913"
      >
    </a
      ><a name="7918" href="Maps.html#7918" class="Postulate"
      >update-same</a
      ><a name="7929"
      > </a
      ><a name="7930" class="Symbol"
      >:</a
      ><a name="7931"
      > </a
      ><a name="7932" class="Symbol"
      >&#8704;</a
      ><a name="7933"
      > </a
      ><a name="7934" class="Symbol"
      >{</a
      ><a name="7935" href="Maps.html#7935" class="Bound"
      >A</a
      ><a name="7936" class="Symbol"
      >}</a
      ><a name="7937"
      > </a
      ><a name="7938" class="Symbol"
      >(</a
      ><a name="7939" href="Maps.html#7939" class="Bound"
      >m</a
      ><a name="7940"
      > </a
      ><a name="7941" class="Symbol"
      >:</a
      ><a name="7942"
      > </a
      ><a name="7943" href="Maps.html#3509" class="Function"
      >TotalMap</a
      ><a name="7951"
      > </a
      ><a name="7952" href="Maps.html#7935" class="Bound"
      >A</a
      ><a name="7953" class="Symbol"
      >)</a
      ><a name="7954"
      > </a
      ><a name="7955" class="Symbol"
      >(</a
      ><a name="7956" href="Maps.html#7956" class="Bound"
      >x</a
      ><a name="7957"
      > </a
      ><a name="7958" href="Maps.html#7958" class="Bound"
      >y</a
      ><a name="7959"
      > </a
      ><a name="7960" class="Symbol"
      >:</a
      ><a name="7961"
      > </a
      ><a name="7962" href="Maps.html#2400" class="Datatype"
      >Id</a
      ><a name="7964" class="Symbol"
      >)</a
      ><a name="7965"
      >
                </a
      ><a name="7982" class="Symbol"
      >&#8594;</a
      ><a name="7983"
      > </a
      ><a name="7984" class="Symbol"
      >(</a
      ><a name="7985" href="Maps.html#4179" class="Function"
      >update</a
      ><a name="7991"
      > </a
      ><a name="7992" href="Maps.html#7939" class="Bound"
      >m</a
      ><a name="7993"
      > </a
      ><a name="7994" href="Maps.html#7956" class="Bound"
      >x</a
      ><a name="7995"
      > </a
      ><a name="7996" class="Symbol"
      >(</a
      ><a name="7997" href="Maps.html#7939" class="Bound"
      >m</a
      ><a name="7998"
      > </a
      ><a name="7999" href="Maps.html#7956" class="Bound"
      >x</a
      ><a name="8000" class="Symbol"
      >))</a
      ><a name="8002"
      > </a
      ><a name="8003" href="Maps.html#7958" class="Bound"
      >y</a
      ><a name="8004"
      > </a
      ><a name="8005" href="Agda.Builtin.Equality.html#55" class="Datatype Operator"
      >&#8801;</a
      ><a name="8006"
      > </a
      ><a name="8007" href="Maps.html#7939" class="Bound"
      >m</a
      ><a name="8008"
      > </a
      ><a name="8009" href="Maps.html#7958" class="Bound"
      >y</a
      >
</pre><!--{% endraw %}-->

<div class="hidden">
<!--{% raw %}--><pre class="Agda">
  <a name="8059" href="Maps.html#8059" class="Function"
      >update-same&#8242;</a
      ><a name="8071"
      > </a
      ><a name="8072" class="Symbol"
      >:</a
      ><a name="8073"
      > </a
      ><a name="8074" class="Symbol"
      >&#8704;</a
      ><a name="8075"
      > </a
      ><a name="8076" class="Symbol"
      >{</a
      ><a name="8077" href="Maps.html#8077" class="Bound"
      >A</a
      ><a name="8078" class="Symbol"
      >}</a
      ><a name="8079"
      > </a
      ><a name="8080" class="Symbol"
      >(</a
      ><a name="8081" href="Maps.html#8081" class="Bound"
      >m</a
      ><a name="8082"
      > </a
      ><a name="8083" class="Symbol"
      >:</a
      ><a name="8084"
      > </a
      ><a name="8085" href="Maps.html#3509" class="Function"
      >TotalMap</a
      ><a name="8093"
      > </a
      ><a name="8094" href="Maps.html#8077" class="Bound"
      >A</a
      ><a name="8095" class="Symbol"
      >)</a
      ><a name="8096"
      > </a
      ><a name="8097" class="Symbol"
      >(</a
      ><a name="8098" href="Maps.html#8098" class="Bound"
      >x</a
      ><a name="8099"
      > </a
      ><a name="8100" href="Maps.html#8100" class="Bound"
      >y</a
      ><a name="8101"
      > </a
      ><a name="8102" class="Symbol"
      >:</a
      ><a name="8103"
      > </a
      ><a name="8104" href="Maps.html#2400" class="Datatype"
      >Id</a
      ><a name="8106" class="Symbol"
      >)</a
      ><a name="8107"
      >
               </a
      ><a name="8123" class="Symbol"
      >&#8594;</a
      ><a name="8124"
      > </a
      ><a name="8125" class="Symbol"
      >(</a
      ><a name="8126" href="Maps.html#4179" class="Function"
      >update</a
      ><a name="8132"
      > </a
      ><a name="8133" href="Maps.html#8081" class="Bound"
      >m</a
      ><a name="8134"
      > </a
      ><a name="8135" href="Maps.html#8098" class="Bound"
      >x</a
      ><a name="8136"
      > </a
      ><a name="8137" class="Symbol"
      >(</a
      ><a name="8138" href="Maps.html#8081" class="Bound"
      >m</a
      ><a name="8139"
      > </a
      ><a name="8140" href="Maps.html#8098" class="Bound"
      >x</a
      ><a name="8141" class="Symbol"
      >))</a
      ><a name="8143"
      > </a
      ><a name="8144" href="Maps.html#8100" class="Bound"
      >y</a
      ><a name="8145"
      > </a
      ><a name="8146" href="Agda.Builtin.Equality.html#55" class="Datatype Operator"
      >&#8801;</a
      ><a name="8147"
      > </a
      ><a name="8148" href="Maps.html#8081" class="Bound"
      >m</a
      ><a name="8149"
      > </a
      ><a name="8150" href="Maps.html#8100" class="Bound"
      >y</a
      ><a name="8151"
      >
  </a
      ><a name="8154" href="Maps.html#8059" class="Function"
      >update-same&#8242;</a
      ><a name="8166"
      > </a
      ><a name="8167" href="Maps.html#8167" class="Bound"
      >m</a
      ><a name="8168"
      > </a
      ><a name="8169" href="Maps.html#8169" class="Bound"
      >x</a
      ><a name="8170"
      > </a
      ><a name="8171" href="Maps.html#8171" class="Bound"
      >y</a
      ><a name="8172"
      >
    </a
      ><a name="8177" class="Keyword"
      >with</a
      ><a name="8181"
      > </a
      ><a name="8182" href="Maps.html#8169" class="Bound"
      >x</a
      ><a name="8183"
      > </a
      ><a name="8184" href="Maps.html#2454" class="Function Operator"
      >&#8799;</a
      ><a name="8185"
      > </a
      ><a name="8186" href="Maps.html#8171" class="Bound"
      >y</a
      ><a name="8187"
      >
  </a
      ><a name="8190" class="Symbol"
      >...</a
      ><a name="8193"
      > </a
      ><a name="8194" class="Symbol"
      >|</a
      ><a name="8195"
      > </a
      ><a name="8196" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#520" class="InductiveConstructor"
      >yes</a
      ><a name="8199"
      > </a
      ><a name="8200" href="Maps.html#8200" class="Bound"
      >x=y</a
      ><a name="8203"
      > </a
      ><a name="8204" class="Keyword"
      >rewrite</a
      ><a name="8211"
      > </a
      ><a name="8212" href="Maps.html#8200" class="Bound"
      >x=y</a
      ><a name="8215"
      > </a
      ><a name="8216" class="Symbol"
      >=</a
      ><a name="8217"
      > </a
      ><a name="8218" href="Agda.Builtin.Equality.html#112" class="InductiveConstructor"
      >refl</a
      ><a name="8222"
      >
  </a
      ><a name="8225" class="Symbol"
      >...</a
      ><a name="8228"
      > </a
      ><a name="8229" class="Symbol"
      >|</a
      ><a name="8230"
      > </a
      ><a name="8231" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#547" class="InductiveConstructor"
      >no</a
      ><a name="8233"
      >  </a
      ><a name="8235" href="Maps.html#8235" class="Bound"
      >x&#8800;y</a
      ><a name="8238"
      > </a
      ><a name="8239" class="Symbol"
      >=</a
      ><a name="8240"
      > </a
      ><a name="8241" href="Agda.Builtin.Equality.html#112" class="InductiveConstructor"
      >refl</a
      >
</pre><!--{% endraw %}-->
</div>

#### Exercise: 3 stars, recommended (update-permute)
Prove one final property of the `update` function: If we update a map
$$m$$ at two distinct keys, it doesn't matter in which order we do the
updates.

<!--{% raw %}--><pre class="Agda">
  <a name="8484" class="Keyword"
      >postulate</a
      ><a name="8493"
      >
    </a
      ><a name="8498" href="Maps.html#8498" class="Postulate"
      >update-permute</a
      ><a name="8512"
      > </a
      ><a name="8513" class="Symbol"
      >:</a
      ><a name="8514"
      > </a
      ><a name="8515" class="Symbol"
      >&#8704;</a
      ><a name="8516"
      > </a
      ><a name="8517" class="Symbol"
      >{</a
      ><a name="8518" href="Maps.html#8518" class="Bound"
      >A</a
      ><a name="8519"
      > </a
      ><a name="8520" href="Maps.html#8520" class="Bound"
      >v1</a
      ><a name="8522"
      > </a
      ><a name="8523" href="Maps.html#8523" class="Bound"
      >v2</a
      ><a name="8525" class="Symbol"
      >}</a
      ><a name="8526"
      > </a
      ><a name="8527" class="Symbol"
      >(</a
      ><a name="8528" href="Maps.html#8528" class="Bound"
      >m</a
      ><a name="8529"
      > </a
      ><a name="8530" class="Symbol"
      >:</a
      ><a name="8531"
      > </a
      ><a name="8532" href="Maps.html#3509" class="Function"
      >TotalMap</a
      ><a name="8540"
      > </a
      ><a name="8541" href="Maps.html#8518" class="Bound"
      >A</a
      ><a name="8542" class="Symbol"
      >)</a
      ><a name="8543"
      > </a
      ><a name="8544" class="Symbol"
      >(</a
      ><a name="8545" href="Maps.html#8545" class="Bound"
      >x1</a
      ><a name="8547"
      > </a
      ><a name="8548" href="Maps.html#8548" class="Bound"
      >x2</a
      ><a name="8550"
      > </a
      ><a name="8551" href="Maps.html#8551" class="Bound"
      >y</a
      ><a name="8552"
      > </a
      ><a name="8553" class="Symbol"
      >:</a
      ><a name="8554"
      > </a
      ><a name="8555" href="Maps.html#2400" class="Datatype"
      >Id</a
      ><a name="8557" class="Symbol"
      >)</a
      ><a name="8558"
      >
                   </a
      ><a name="8578" class="Symbol"
      >&#8594;</a
      ><a name="8579"
      > </a
      ><a name="8580" href="Maps.html#8545" class="Bound"
      >x1</a
      ><a name="8582"
      > </a
      ><a name="8583" href="https://agda.github.io/agda-stdlib/Relation.Binary.Core.html#4493" class="Function Operator"
      >&#8802;</a
      ><a name="8584"
      > </a
      ><a name="8585" href="Maps.html#8548" class="Bound"
      >x2</a
      ><a name="8587"
      > </a
      ><a name="8588" class="Symbol"
      >&#8594;</a
      ><a name="8589"
      > </a
      ><a name="8590" class="Symbol"
      >(</a
      ><a name="8591" href="Maps.html#4179" class="Function"
      >update</a
      ><a name="8597"
      > </a
      ><a name="8598" class="Symbol"
      >(</a
      ><a name="8599" href="Maps.html#4179" class="Function"
      >update</a
      ><a name="8605"
      > </a
      ><a name="8606" href="Maps.html#8528" class="Bound"
      >m</a
      ><a name="8607"
      > </a
      ><a name="8608" href="Maps.html#8548" class="Bound"
      >x2</a
      ><a name="8610"
      > </a
      ><a name="8611" href="Maps.html#8523" class="Bound"
      >v2</a
      ><a name="8613" class="Symbol"
      >)</a
      ><a name="8614"
      > </a
      ><a name="8615" href="Maps.html#8545" class="Bound"
      >x1</a
      ><a name="8617"
      > </a
      ><a name="8618" href="Maps.html#8520" class="Bound"
      >v1</a
      ><a name="8620" class="Symbol"
      >)</a
      ><a name="8621"
      > </a
      ><a name="8622" href="Maps.html#8551" class="Bound"
      >y</a
      ><a name="8623"
      >
                             </a
      ><a name="8653" href="Agda.Builtin.Equality.html#55" class="Datatype Operator"
      >&#8801;</a
      ><a name="8654"
      > </a
      ><a name="8655" class="Symbol"
      >(</a
      ><a name="8656" href="Maps.html#4179" class="Function"
      >update</a
      ><a name="8662"
      > </a
      ><a name="8663" class="Symbol"
      >(</a
      ><a name="8664" href="Maps.html#4179" class="Function"
      >update</a
      ><a name="8670"
      > </a
      ><a name="8671" href="Maps.html#8528" class="Bound"
      >m</a
      ><a name="8672"
      > </a
      ><a name="8673" href="Maps.html#8545" class="Bound"
      >x1</a
      ><a name="8675"
      > </a
      ><a name="8676" href="Maps.html#8520" class="Bound"
      >v1</a
      ><a name="8678" class="Symbol"
      >)</a
      ><a name="8679"
      > </a
      ><a name="8680" href="Maps.html#8548" class="Bound"
      >x2</a
      ><a name="8682"
      > </a
      ><a name="8683" href="Maps.html#8523" class="Bound"
      >v2</a
      ><a name="8685" class="Symbol"
      >)</a
      ><a name="8686"
      > </a
      ><a name="8687" href="Maps.html#8551" class="Bound"
      >y</a
      >
</pre><!--{% endraw %}-->

<div class="hidden">
<!--{% raw %}--><pre class="Agda">
  <a name="8737" href="Maps.html#8737" class="Function"
      >update-permute&#8242;</a
      ><a name="8752"
      > </a
      ><a name="8753" class="Symbol"
      >:</a
      ><a name="8754"
      > </a
      ><a name="8755" class="Symbol"
      >&#8704;</a
      ><a name="8756"
      > </a
      ><a name="8757" class="Symbol"
      >{</a
      ><a name="8758" href="Maps.html#8758" class="Bound"
      >A</a
      ><a name="8759"
      > </a
      ><a name="8760" href="Maps.html#8760" class="Bound"
      >v1</a
      ><a name="8762"
      > </a
      ><a name="8763" href="Maps.html#8763" class="Bound"
      >v2</a
      ><a name="8765" class="Symbol"
      >}</a
      ><a name="8766"
      > </a
      ><a name="8767" class="Symbol"
      >(</a
      ><a name="8768" href="Maps.html#8768" class="Bound"
      >m</a
      ><a name="8769"
      > </a
      ><a name="8770" class="Symbol"
      >:</a
      ><a name="8771"
      > </a
      ><a name="8772" href="Maps.html#3509" class="Function"
      >TotalMap</a
      ><a name="8780"
      > </a
      ><a name="8781" href="Maps.html#8758" class="Bound"
      >A</a
      ><a name="8782" class="Symbol"
      >)</a
      ><a name="8783"
      > </a
      ><a name="8784" class="Symbol"
      >(</a
      ><a name="8785" href="Maps.html#8785" class="Bound"
      >x1</a
      ><a name="8787"
      > </a
      ><a name="8788" href="Maps.html#8788" class="Bound"
      >x2</a
      ><a name="8790"
      > </a
      ><a name="8791" href="Maps.html#8791" class="Bound"
      >y</a
      ><a name="8792"
      > </a
      ><a name="8793" class="Symbol"
      >:</a
      ><a name="8794"
      > </a
      ><a name="8795" href="Maps.html#2400" class="Datatype"
      >Id</a
      ><a name="8797" class="Symbol"
      >)</a
      ><a name="8798"
      >
                  </a
      ><a name="8817" class="Symbol"
      >&#8594;</a
      ><a name="8818"
      > </a
      ><a name="8819" href="Maps.html#8785" class="Bound"
      >x1</a
      ><a name="8821"
      > </a
      ><a name="8822" href="https://agda.github.io/agda-stdlib/Relation.Binary.Core.html#4493" class="Function Operator"
      >&#8802;</a
      ><a name="8823"
      > </a
      ><a name="8824" href="Maps.html#8788" class="Bound"
      >x2</a
      ><a name="8826"
      > </a
      ><a name="8827" class="Symbol"
      >&#8594;</a
      ><a name="8828"
      > </a
      ><a name="8829" class="Symbol"
      >(</a
      ><a name="8830" href="Maps.html#4179" class="Function"
      >update</a
      ><a name="8836"
      > </a
      ><a name="8837" class="Symbol"
      >(</a
      ><a name="8838" href="Maps.html#4179" class="Function"
      >update</a
      ><a name="8844"
      > </a
      ><a name="8845" href="Maps.html#8768" class="Bound"
      >m</a
      ><a name="8846"
      > </a
      ><a name="8847" href="Maps.html#8788" class="Bound"
      >x2</a
      ><a name="8849"
      > </a
      ><a name="8850" href="Maps.html#8763" class="Bound"
      >v2</a
      ><a name="8852" class="Symbol"
      >)</a
      ><a name="8853"
      > </a
      ><a name="8854" href="Maps.html#8785" class="Bound"
      >x1</a
      ><a name="8856"
      > </a
      ><a name="8857" href="Maps.html#8760" class="Bound"
      >v1</a
      ><a name="8859" class="Symbol"
      >)</a
      ><a name="8860"
      > </a
      ><a name="8861" href="Maps.html#8791" class="Bound"
      >y</a
      ><a name="8862"
      >
                            </a
      ><a name="8891" href="Agda.Builtin.Equality.html#55" class="Datatype Operator"
      >&#8801;</a
      ><a name="8892"
      > </a
      ><a name="8893" class="Symbol"
      >(</a
      ><a name="8894" href="Maps.html#4179" class="Function"
      >update</a
      ><a name="8900"
      > </a
      ><a name="8901" class="Symbol"
      >(</a
      ><a name="8902" href="Maps.html#4179" class="Function"
      >update</a
      ><a name="8908"
      > </a
      ><a name="8909" href="Maps.html#8768" class="Bound"
      >m</a
      ><a name="8910"
      > </a
      ><a name="8911" href="Maps.html#8785" class="Bound"
      >x1</a
      ><a name="8913"
      > </a
      ><a name="8914" href="Maps.html#8760" class="Bound"
      >v1</a
      ><a name="8916" class="Symbol"
      >)</a
      ><a name="8917"
      > </a
      ><a name="8918" href="Maps.html#8788" class="Bound"
      >x2</a
      ><a name="8920"
      > </a
      ><a name="8921" href="Maps.html#8763" class="Bound"
      >v2</a
      ><a name="8923" class="Symbol"
      >)</a
      ><a name="8924"
      > </a
      ><a name="8925" href="Maps.html#8791" class="Bound"
      >y</a
      ><a name="8926"
      >
  </a
      ><a name="8929" href="Maps.html#8737" class="Function"
      >update-permute&#8242;</a
      ><a name="8944"
      > </a
      ><a name="8945" class="Symbol"
      >{</a
      ><a name="8946" href="Maps.html#8946" class="Bound"
      >A</a
      ><a name="8947" class="Symbol"
      >}</a
      ><a name="8948"
      > </a
      ><a name="8949" class="Symbol"
      >{</a
      ><a name="8950" href="Maps.html#8950" class="Bound"
      >v1</a
      ><a name="8952" class="Symbol"
      >}</a
      ><a name="8953"
      > </a
      ><a name="8954" class="Symbol"
      >{</a
      ><a name="8955" href="Maps.html#8955" class="Bound"
      >v2</a
      ><a name="8957" class="Symbol"
      >}</a
      ><a name="8958"
      > </a
      ><a name="8959" href="Maps.html#8959" class="Bound"
      >m</a
      ><a name="8960"
      > </a
      ><a name="8961" href="Maps.html#8961" class="Bound"
      >x1</a
      ><a name="8963"
      > </a
      ><a name="8964" href="Maps.html#8964" class="Bound"
      >x2</a
      ><a name="8966"
      > </a
      ><a name="8967" href="Maps.html#8967" class="Bound"
      >y</a
      ><a name="8968"
      > </a
      ><a name="8969" href="Maps.html#8969" class="Bound"
      >x1&#8800;x2</a
      ><a name="8974"
      >
    </a
      ><a name="8979" class="Keyword"
      >with</a
      ><a name="8983"
      > </a
      ><a name="8984" href="Maps.html#8961" class="Bound"
      >x1</a
      ><a name="8986"
      > </a
      ><a name="8987" href="Maps.html#2454" class="Function Operator"
      >&#8799;</a
      ><a name="8988"
      > </a
      ><a name="8989" href="Maps.html#8967" class="Bound"
      >y</a
      ><a name="8990"
      > </a
      ><a name="8991" class="Symbol"
      >|</a
      ><a name="8992"
      > </a
      ><a name="8993" href="Maps.html#8964" class="Bound"
      >x2</a
      ><a name="8995"
      > </a
      ><a name="8996" href="Maps.html#2454" class="Function Operator"
      >&#8799;</a
      ><a name="8997"
      > </a
      ><a name="8998" href="Maps.html#8967" class="Bound"
      >y</a
      ><a name="8999"
      >
  </a
      ><a name="9002" class="Symbol"
      >...</a
      ><a name="9005"
      > </a
      ><a name="9006" class="Symbol"
      >|</a
      ><a name="9007"
      > </a
      ><a name="9008" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#520" class="InductiveConstructor"
      >yes</a
      ><a name="9011"
      > </a
      ><a name="9012" href="Maps.html#9012" class="Bound"
      >x1=y</a
      ><a name="9016"
      > </a
      ><a name="9017" class="Symbol"
      >|</a
      ><a name="9018"
      > </a
      ><a name="9019" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#520" class="InductiveConstructor"
      >yes</a
      ><a name="9022"
      > </a
      ><a name="9023" href="Maps.html#9023" class="Bound"
      >x2=y</a
      ><a name="9027"
      > </a
      ><a name="9028" class="Symbol"
      >=</a
      ><a name="9029"
      > </a
      ><a name="9030" href="https://agda.github.io/agda-stdlib/Data.Empty.html#348" class="Function"
      >&#8869;-elim</a
      ><a name="9036"
      > </a
      ><a name="9037" class="Symbol"
      >(</a
      ><a name="9038" href="Maps.html#8969" class="Bound"
      >x1&#8800;x2</a
      ><a name="9043"
      > </a
      ><a name="9044" class="Symbol"
      >(</a
      ><a name="9045" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.Core.html#632" class="Function"
      >trans</a
      ><a name="9050"
      > </a
      ><a name="9051" href="Maps.html#9012" class="Bound"
      >x1=y</a
      ><a name="9055"
      > </a
      ><a name="9056" class="Symbol"
      >(</a
      ><a name="9057" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.Core.html#565" class="Function"
      >sym</a
      ><a name="9060"
      > </a
      ><a name="9061" href="Maps.html#9023" class="Bound"
      >x2=y</a
      ><a name="9065" class="Symbol"
      >)))</a
      ><a name="9068"
      >
  </a
      ><a name="9071" class="Symbol"
      >...</a
      ><a name="9074"
      > </a
      ><a name="9075" class="Symbol"
      >|</a
      ><a name="9076"
      > </a
      ><a name="9077" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#547" class="InductiveConstructor"
      >no</a
      ><a name="9079"
      >  </a
      ><a name="9081" href="Maps.html#9081" class="Bound"
      >x1&#8800;y</a
      ><a name="9085"
      > </a
      ><a name="9086" class="Symbol"
      >|</a
      ><a name="9087"
      > </a
      ><a name="9088" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#520" class="InductiveConstructor"
      >yes</a
      ><a name="9091"
      > </a
      ><a name="9092" href="Maps.html#9092" class="Bound"
      >x2=y</a
      ><a name="9096"
      > </a
      ><a name="9097" class="Keyword"
      >rewrite</a
      ><a name="9104"
      > </a
      ><a name="9105" href="Maps.html#9092" class="Bound"
      >x2=y</a
      ><a name="9109"
      > </a
      ><a name="9110" class="Symbol"
      >=</a
      ><a name="9111"
      > </a
      ><a name="9112" href="Maps.html#6265" class="Function"
      >update-eq&#8242;</a
      ><a name="9122"
      > </a
      ><a name="9123" href="Maps.html#8959" class="Bound"
      >m</a
      ><a name="9124"
      > </a
      ><a name="9125" href="Maps.html#8967" class="Bound"
      >y</a
      ><a name="9126"
      >
  </a
      ><a name="9129" class="Symbol"
      >...</a
      ><a name="9132"
      > </a
      ><a name="9133" class="Symbol"
      >|</a
      ><a name="9134"
      > </a
      ><a name="9135" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#520" class="InductiveConstructor"
      >yes</a
      ><a name="9138"
      > </a
      ><a name="9139" href="Maps.html#9139" class="Bound"
      >x1=y</a
      ><a name="9143"
      > </a
      ><a name="9144" class="Symbol"
      >|</a
      ><a name="9145"
      > </a
      ><a name="9146" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#547" class="InductiveConstructor"
      >no</a
      ><a name="9148"
      >  </a
      ><a name="9150" href="Maps.html#9150" class="Bound"
      >x2&#8800;y</a
      ><a name="9154"
      > </a
      ><a name="9155" class="Keyword"
      >rewrite</a
      ><a name="9162"
      > </a
      ><a name="9163" href="Maps.html#9139" class="Bound"
      >x1=y</a
      ><a name="9167"
      > </a
      ><a name="9168" class="Symbol"
      >=</a
      ><a name="9169"
      > </a
      ><a name="9170" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.Core.html#565" class="Function"
      >sym</a
      ><a name="9173"
      > </a
      ><a name="9174" class="Symbol"
      >(</a
      ><a name="9175" href="Maps.html#6265" class="Function"
      >update-eq&#8242;</a
      ><a name="9185"
      > </a
      ><a name="9186" href="Maps.html#8959" class="Bound"
      >m</a
      ><a name="9187"
      > </a
      ><a name="9188" href="Maps.html#8967" class="Bound"
      >y</a
      ><a name="9189" class="Symbol"
      >)</a
      ><a name="9190"
      >
  </a
      ><a name="9193" class="Symbol"
      >...</a
      ><a name="9196"
      > </a
      ><a name="9197" class="Symbol"
      >|</a
      ><a name="9198"
      > </a
      ><a name="9199" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#547" class="InductiveConstructor"
      >no</a
      ><a name="9201"
      >  </a
      ><a name="9203" href="Maps.html#9203" class="Bound"
      >x1&#8800;y</a
      ><a name="9207"
      > </a
      ><a name="9208" class="Symbol"
      >|</a
      ><a name="9209"
      > </a
      ><a name="9210" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#547" class="InductiveConstructor"
      >no</a
      ><a name="9212"
      >  </a
      ><a name="9214" href="Maps.html#9214" class="Bound"
      >x2&#8800;y</a
      ><a name="9218"
      > </a
      ><a name="9219" class="Symbol"
      >=</a
      ><a name="9220"
      >
    </a
      ><a name="9225" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.Core.html#632" class="Function"
      >trans</a
      ><a name="9230"
      > </a
      ><a name="9231" class="Symbol"
      >(</a
      ><a name="9232" href="Maps.html#6690" class="Function"
      >update-neq</a
      ><a name="9242"
      > </a
      ><a name="9243" href="Maps.html#8959" class="Bound"
      >m</a
      ><a name="9244"
      > </a
      ><a name="9245" href="Maps.html#8964" class="Bound"
      >x2</a
      ><a name="9247"
      > </a
      ><a name="9248" href="Maps.html#8967" class="Bound"
      >y</a
      ><a name="9249"
      > </a
      ><a name="9250" href="Maps.html#9214" class="Bound"
      >x2&#8800;y</a
      ><a name="9254" class="Symbol"
      >)</a
      ><a name="9255"
      > </a
      ><a name="9256" class="Symbol"
      >(</a
      ><a name="9257" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.Core.html#565" class="Function"
      >sym</a
      ><a name="9260"
      > </a
      ><a name="9261" class="Symbol"
      >(</a
      ><a name="9262" href="Maps.html#6690" class="Function"
      >update-neq</a
      ><a name="9272"
      > </a
      ><a name="9273" href="Maps.html#8959" class="Bound"
      >m</a
      ><a name="9274"
      > </a
      ><a name="9275" href="Maps.html#8961" class="Bound"
      >x1</a
      ><a name="9277"
      > </a
      ><a name="9278" href="Maps.html#8967" class="Bound"
      >y</a
      ><a name="9279"
      > </a
      ><a name="9280" href="Maps.html#9203" class="Bound"
      >x1&#8800;y</a
      ><a name="9284" class="Symbol"
      >))</a
      >
</pre><!--{% endraw %}-->
</div>

## Partial maps

Finally, we define _partial maps_ on top of total maps.  A partial
map with elements of type `A` is simply a total map with elements
of type `Maybe A` and default element `nothing`.

<!--{% raw %}--><pre class="Agda">
<a name="9519" href="Maps.html#9519" class="Function"
      >PartialMap</a
      ><a name="9529"
      > </a
      ><a name="9530" class="Symbol"
      >:</a
      ><a name="9531"
      > </a
      ><a name="9532" class="PrimitiveType"
      >Set</a
      ><a name="9535"
      > </a
      ><a name="9536" class="Symbol"
      >&#8594;</a
      ><a name="9537"
      > </a
      ><a name="9538" class="PrimitiveType"
      >Set</a
      ><a name="9541"
      >
</a
      ><a name="9542" href="Maps.html#9519" class="Function"
      >PartialMap</a
      ><a name="9552"
      > </a
      ><a name="9553" href="Maps.html#9553" class="Bound"
      >A</a
      ><a name="9554"
      > </a
      ><a name="9555" class="Symbol"
      >=</a
      ><a name="9556"
      > </a
      ><a name="9557" href="Maps.html#3509" class="Function"
      >TotalMap</a
      ><a name="9565"
      > </a
      ><a name="9566" class="Symbol"
      >(</a
      ><a name="9567" href="https://agda.github.io/agda-stdlib/Data.Maybe.Base.html#335" class="Datatype"
      >Maybe</a
      ><a name="9572"
      > </a
      ><a name="9573" href="Maps.html#9553" class="Bound"
      >A</a
      ><a name="9574" class="Symbol"
      >)</a
      >
</pre><!--{% endraw %}-->

<!--{% raw %}--><pre class="Agda">
<a name="9601" class="Keyword"
      >module</a
      ><a name="9607"
      > </a
      ><a name="9608" href="Maps.html#9608" class="Module"
      >PartialMap</a
      ><a name="9618"
      > </a
      ><a name="9619" class="Keyword"
      >where</a
      >
</pre><!--{% endraw %}-->

<!--{% raw %}--><pre class="Agda">
  <a name="9652" href="Maps.html#9652" class="Function"
      >empty</a
      ><a name="9657"
      > </a
      ><a name="9658" class="Symbol"
      >:</a
      ><a name="9659"
      > </a
      ><a name="9660" class="Symbol"
      >&#8704;</a
      ><a name="9661"
      > </a
      ><a name="9662" class="Symbol"
      >{</a
      ><a name="9663" href="Maps.html#9663" class="Bound"
      >A</a
      ><a name="9664" class="Symbol"
      >}</a
      ><a name="9665"
      > </a
      ><a name="9666" class="Symbol"
      >&#8594;</a
      ><a name="9667"
      > </a
      ><a name="9668" href="Maps.html#9519" class="Function"
      >PartialMap</a
      ><a name="9678"
      > </a
      ><a name="9679" href="Maps.html#9663" class="Bound"
      >A</a
      ><a name="9680"
      >
  </a
      ><a name="9683" href="Maps.html#9652" class="Function"
      >empty</a
      ><a name="9688"
      > </a
      ><a name="9689" class="Symbol"
      >=</a
      ><a name="9690"
      > </a
      ><a name="9691" href="Maps.html#3891" class="Function"
      >TotalMap.empty</a
      ><a name="9705"
      > </a
      ><a name="9706" href="https://agda.github.io/agda-stdlib/Data.Maybe.Base.html#403" class="InductiveConstructor"
      >nothing</a
      >
</pre><!--{% endraw %}-->

<!--{% raw %}--><pre class="Agda">
  <a name="9741" href="Maps.html#9741" class="Function"
      >update</a
      ><a name="9747"
      > </a
      ><a name="9748" class="Symbol"
      >:</a
      ><a name="9749"
      > </a
      ><a name="9750" class="Symbol"
      >&#8704;</a
      ><a name="9751"
      > </a
      ><a name="9752" class="Symbol"
      >{</a
      ><a name="9753" href="Maps.html#9753" class="Bound"
      >A</a
      ><a name="9754" class="Symbol"
      >}</a
      ><a name="9755"
      > </a
      ><a name="9756" class="Symbol"
      >(</a
      ><a name="9757" href="Maps.html#9757" class="Bound"
      >m</a
      ><a name="9758"
      > </a
      ><a name="9759" class="Symbol"
      >:</a
      ><a name="9760"
      > </a
      ><a name="9761" href="Maps.html#9519" class="Function"
      >PartialMap</a
      ><a name="9771"
      > </a
      ><a name="9772" href="Maps.html#9753" class="Bound"
      >A</a
      ><a name="9773" class="Symbol"
      >)</a
      ><a name="9774"
      > </a
      ><a name="9775" class="Symbol"
      >(</a
      ><a name="9776" href="Maps.html#9776" class="Bound"
      >x</a
      ><a name="9777"
      > </a
      ><a name="9778" class="Symbol"
      >:</a
      ><a name="9779"
      > </a
      ><a name="9780" href="Maps.html#2400" class="Datatype"
      >Id</a
      ><a name="9782" class="Symbol"
      >)</a
      ><a name="9783"
      > </a
      ><a name="9784" class="Symbol"
      >(</a
      ><a name="9785" href="Maps.html#9785" class="Bound"
      >v</a
      ><a name="9786"
      > </a
      ><a name="9787" class="Symbol"
      >:</a
      ><a name="9788"
      > </a
      ><a name="9789" href="Maps.html#9753" class="Bound"
      >A</a
      ><a name="9790" class="Symbol"
      >)</a
      ><a name="9791"
      > </a
      ><a name="9792" class="Symbol"
      >&#8594;</a
      ><a name="9793"
      > </a
      ><a name="9794" href="Maps.html#9519" class="Function"
      >PartialMap</a
      ><a name="9804"
      > </a
      ><a name="9805" href="Maps.html#9753" class="Bound"
      >A</a
      ><a name="9806"
      >
  </a
      ><a name="9809" href="Maps.html#9741" class="Function"
      >update</a
      ><a name="9815"
      > </a
      ><a name="9816" href="Maps.html#9816" class="Bound"
      >m</a
      ><a name="9817"
      > </a
      ><a name="9818" href="Maps.html#9818" class="Bound"
      >x</a
      ><a name="9819"
      > </a
      ><a name="9820" href="Maps.html#9820" class="Bound"
      >v</a
      ><a name="9821"
      > </a
      ><a name="9822" class="Symbol"
      >=</a
      ><a name="9823"
      > </a
      ><a name="9824" href="Maps.html#4179" class="Function"
      >TotalMap.update</a
      ><a name="9839"
      > </a
      ><a name="9840" href="Maps.html#9816" class="Bound"
      >m</a
      ><a name="9841"
      > </a
      ><a name="9842" href="Maps.html#9818" class="Bound"
      >x</a
      ><a name="9843"
      > </a
      ><a name="9844" class="Symbol"
      >(</a
      ><a name="9845" href="https://agda.github.io/agda-stdlib/Data.Maybe.Base.html#373" class="InductiveConstructor"
      >just</a
      ><a name="9849"
      > </a
      ><a name="9850" href="Maps.html#9820" class="Bound"
      >v</a
      ><a name="9851" class="Symbol"
      >)</a
      >
</pre><!--{% endraw %}-->

We can now lift all of the basic lemmas about total maps to
partial maps.

<!--{% raw %}--><pre class="Agda">
  <a name="9955" href="Maps.html#9955" class="Function"
      >update-eq</a
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
      ><a name="9969" class="Symbol"
      >{</a
      ><a name="9970" href="Maps.html#9970" class="Bound"
      >A</a
      ><a name="9971"
      > </a
      ><a name="9972" href="Maps.html#9972" class="Bound"
      >v</a
      ><a name="9973" class="Symbol"
      >}</a
      ><a name="9974"
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
      ><a name="9980" href="Maps.html#9519" class="Function"
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
      ><a name="9997" class="Symbol"
      >:</a
      ><a name="9998"
      > </a
      ><a name="9999" href="Maps.html#2400" class="Datatype"
      >Id</a
      ><a name="10001" class="Symbol"
      >)</a
      ><a name="10002"
      >
            </a
      ><a name="10015" class="Symbol"
      >&#8594;</a
      ><a name="10016"
      > </a
      ><a name="10017" class="Symbol"
      >(</a
      ><a name="10018" href="Maps.html#9741" class="Function"
      >update</a
      ><a name="10024"
      > </a
      ><a name="10025" href="Maps.html#9976" class="Bound"
      >m</a
      ><a name="10026"
      > </a
      ><a name="10027" href="Maps.html#9995" class="Bound"
      >x</a
      ><a name="10028"
      > </a
      ><a name="10029" href="Maps.html#9972" class="Bound"
      >v</a
      ><a name="10030" class="Symbol"
      >)</a
      ><a name="10031"
      > </a
      ><a name="10032" href="Maps.html#9995" class="Bound"
      >x</a
      ><a name="10033"
      > </a
      ><a name="10034" href="Agda.Builtin.Equality.html#55" class="Datatype Operator"
      >&#8801;</a
      ><a name="10035"
      > </a
      ><a name="10036" href="https://agda.github.io/agda-stdlib/Data.Maybe.Base.html#373" class="InductiveConstructor"
      >just</a
      ><a name="10040"
      > </a
      ><a name="10041" href="Maps.html#9972" class="Bound"
      >v</a
      ><a name="10042"
      >
  </a
      ><a name="10045" href="Maps.html#9955" class="Function"
      >update-eq</a
      ><a name="10054"
      > </a
      ><a name="10055" href="Maps.html#10055" class="Bound"
      >m</a
      ><a name="10056"
      > </a
      ><a name="10057" href="Maps.html#10057" class="Bound"
      >x</a
      ><a name="10058"
      > </a
      ><a name="10059" class="Symbol"
      >=</a
      ><a name="10060"
      > </a
      ><a name="10061" href="Maps.html#6134" class="Postulate"
      >TotalMap.update-eq</a
      ><a name="10079"
      > </a
      ><a name="10080" href="Maps.html#10055" class="Bound"
      >m</a
      ><a name="10081"
      > </a
      ><a name="10082" href="Maps.html#10057" class="Bound"
      >x</a
      >
</pre><!--{% endraw %}-->

<!--{% raw %}--><pre class="Agda">
  <a name="10111" href="Maps.html#10111" class="Function"
      >update-neq</a
      ><a name="10121"
      > </a
      ><a name="10122" class="Symbol"
      >:</a
      ><a name="10123"
      > </a
      ><a name="10124" class="Symbol"
      >&#8704;</a
      ><a name="10125"
      > </a
      ><a name="10126" class="Symbol"
      >{</a
      ><a name="10127" href="Maps.html#10127" class="Bound"
      >A</a
      ><a name="10128"
      > </a
      ><a name="10129" href="Maps.html#10129" class="Bound"
      >v</a
      ><a name="10130" class="Symbol"
      >}</a
      ><a name="10131"
      > </a
      ><a name="10132" class="Symbol"
      >(</a
      ><a name="10133" href="Maps.html#10133" class="Bound"
      >m</a
      ><a name="10134"
      > </a
      ><a name="10135" class="Symbol"
      >:</a
      ><a name="10136"
      > </a
      ><a name="10137" href="Maps.html#9519" class="Function"
      >PartialMap</a
      ><a name="10147"
      > </a
      ><a name="10148" href="Maps.html#10127" class="Bound"
      >A</a
      ><a name="10149" class="Symbol"
      >)</a
      ><a name="10150"
      > </a
      ><a name="10151" class="Symbol"
      >(</a
      ><a name="10152" href="Maps.html#10152" class="Bound"
      >x</a
      ><a name="10153"
      > </a
      ><a name="10154" href="Maps.html#10154" class="Bound"
      >y</a
      ><a name="10155"
      > </a
      ><a name="10156" class="Symbol"
      >:</a
      ><a name="10157"
      > </a
      ><a name="10158" href="Maps.html#2400" class="Datatype"
      >Id</a
      ><a name="10160" class="Symbol"
      >)</a
      ><a name="10161"
      >
             </a
      ><a name="10175" class="Symbol"
      >&#8594;</a
      ><a name="10176"
      > </a
      ><a name="10177" href="Maps.html#10152" class="Bound"
      >x</a
      ><a name="10178"
      > </a
      ><a name="10179" href="https://agda.github.io/agda-stdlib/Relation.Binary.Core.html#4493" class="Function Operator"
      >&#8802;</a
      ><a name="10180"
      > </a
      ><a name="10181" href="Maps.html#10154" class="Bound"
      >y</a
      ><a name="10182"
      > </a
      ><a name="10183" class="Symbol"
      >&#8594;</a
      ><a name="10184"
      > </a
      ><a name="10185" class="Symbol"
      >(</a
      ><a name="10186" href="Maps.html#9741" class="Function"
      >update</a
      ><a name="10192"
      > </a
      ><a name="10193" href="Maps.html#10133" class="Bound"
      >m</a
      ><a name="10194"
      > </a
      ><a name="10195" href="Maps.html#10152" class="Bound"
      >x</a
      ><a name="10196"
      > </a
      ><a name="10197" href="Maps.html#10129" class="Bound"
      >v</a
      ><a name="10198" class="Symbol"
      >)</a
      ><a name="10199"
      > </a
      ><a name="10200" href="Maps.html#10154" class="Bound"
      >y</a
      ><a name="10201"
      > </a
      ><a name="10202" href="Agda.Builtin.Equality.html#55" class="Datatype Operator"
      >&#8801;</a
      ><a name="10203"
      > </a
      ><a name="10204" href="Maps.html#10133" class="Bound"
      >m</a
      ><a name="10205"
      > </a
      ><a name="10206" href="Maps.html#10154" class="Bound"
      >y</a
      ><a name="10207"
      >
  </a
      ><a name="10210" href="Maps.html#10111" class="Function"
      >update-neq</a
      ><a name="10220"
      > </a
      ><a name="10221" href="Maps.html#10221" class="Bound"
      >m</a
      ><a name="10222"
      > </a
      ><a name="10223" href="Maps.html#10223" class="Bound"
      >x</a
      ><a name="10224"
      > </a
      ><a name="10225" href="Maps.html#10225" class="Bound"
      >y</a
      ><a name="10226"
      > </a
      ><a name="10227" href="Maps.html#10227" class="Bound"
      >x&#8800;y</a
      ><a name="10230"
      > </a
      ><a name="10231" class="Symbol"
      >=</a
      ><a name="10232"
      > </a
      ><a name="10233" href="Maps.html#6690" class="Function"
      >TotalMap.update-neq</a
      ><a name="10252"
      > </a
      ><a name="10253" href="Maps.html#10221" class="Bound"
      >m</a
      ><a name="10254"
      > </a
      ><a name="10255" href="Maps.html#10223" class="Bound"
      >x</a
      ><a name="10256"
      > </a
      ><a name="10257" href="Maps.html#10225" class="Bound"
      >y</a
      ><a name="10258"
      > </a
      ><a name="10259" href="Maps.html#10227" class="Bound"
      >x&#8800;y</a
      >
</pre><!--{% endraw %}-->

<!--{% raw %}--><pre class="Agda">
  <a name="10290" href="Maps.html#10290" class="Function"
      >update-shadow</a
      ><a name="10303"
      > </a
      ><a name="10304" class="Symbol"
      >:</a
      ><a name="10305"
      > </a
      ><a name="10306" class="Symbol"
      >&#8704;</a
      ><a name="10307"
      > </a
      ><a name="10308" class="Symbol"
      >{</a
      ><a name="10309" href="Maps.html#10309" class="Bound"
      >A</a
      ><a name="10310"
      > </a
      ><a name="10311" href="Maps.html#10311" class="Bound"
      >v1</a
      ><a name="10313"
      > </a
      ><a name="10314" href="Maps.html#10314" class="Bound"
      >v2</a
      ><a name="10316" class="Symbol"
      >}</a
      ><a name="10317"
      > </a
      ><a name="10318" class="Symbol"
      >(</a
      ><a name="10319" href="Maps.html#10319" class="Bound"
      >m</a
      ><a name="10320"
      > </a
      ><a name="10321" class="Symbol"
      >:</a
      ><a name="10322"
      > </a
      ><a name="10323" href="Maps.html#9519" class="Function"
      >PartialMap</a
      ><a name="10333"
      > </a
      ><a name="10334" href="Maps.html#10309" class="Bound"
      >A</a
      ><a name="10335" class="Symbol"
      >)</a
      ><a name="10336"
      > </a
      ><a name="10337" class="Symbol"
      >(</a
      ><a name="10338" href="Maps.html#10338" class="Bound"
      >x</a
      ><a name="10339"
      > </a
      ><a name="10340" href="Maps.html#10340" class="Bound"
      >y</a
      ><a name="10341"
      > </a
      ><a name="10342" class="Symbol"
      >:</a
      ><a name="10343"
      > </a
      ><a name="10344" href="Maps.html#2400" class="Datatype"
      >Id</a
      ><a name="10346" class="Symbol"
      >)</a
      ><a name="10347"
      >
                </a
      ><a name="10364" class="Symbol"
      >&#8594;</a
      ><a name="10365"
      > </a
      ><a name="10366" class="Symbol"
      >(</a
      ><a name="10367" href="Maps.html#9741" class="Function"
      >update</a
      ><a name="10373"
      > </a
      ><a name="10374" class="Symbol"
      >(</a
      ><a name="10375" href="Maps.html#9741" class="Function"
      >update</a
      ><a name="10381"
      > </a
      ><a name="10382" href="Maps.html#10319" class="Bound"
      >m</a
      ><a name="10383"
      > </a
      ><a name="10384" href="Maps.html#10338" class="Bound"
      >x</a
      ><a name="10385"
      > </a
      ><a name="10386" href="Maps.html#10311" class="Bound"
      >v1</a
      ><a name="10388" class="Symbol"
      >)</a
      ><a name="10389"
      > </a
      ><a name="10390" href="Maps.html#10338" class="Bound"
      >x</a
      ><a name="10391"
      > </a
      ><a name="10392" href="Maps.html#10314" class="Bound"
      >v2</a
      ><a name="10394" class="Symbol"
      >)</a
      ><a name="10395"
      > </a
      ><a name="10396" href="Maps.html#10340" class="Bound"
      >y</a
      ><a name="10397"
      > </a
      ><a name="10398" href="Agda.Builtin.Equality.html#55" class="Datatype Operator"
      >&#8801;</a
      ><a name="10399"
      > </a
      ><a name="10400" class="Symbol"
      >(</a
      ><a name="10401" href="Maps.html#9741" class="Function"
      >update</a
      ><a name="10407"
      > </a
      ><a name="10408" href="Maps.html#10319" class="Bound"
      >m</a
      ><a name="10409"
      > </a
      ><a name="10410" href="Maps.html#10338" class="Bound"
      >x</a
      ><a name="10411"
      > </a
      ><a name="10412" href="Maps.html#10314" class="Bound"
      >v2</a
      ><a name="10414" class="Symbol"
      >)</a
      ><a name="10415"
      > </a
      ><a name="10416" href="Maps.html#10340" class="Bound"
      >y</a
      ><a name="10417"
      >
  </a
      ><a name="10420" href="Maps.html#10290" class="Function"
      >update-shadow</a
      ><a name="10433"
      > </a
      ><a name="10434" href="Maps.html#10434" class="Bound"
      >m</a
      ><a name="10435"
      > </a
      ><a name="10436" href="Maps.html#10436" class="Bound"
      >x</a
      ><a name="10437"
      > </a
      ><a name="10438" href="Maps.html#10438" class="Bound"
      >y</a
      ><a name="10439"
      > </a
      ><a name="10440" class="Symbol"
      >=</a
      ><a name="10441"
      > </a
      ><a name="10442" href="Maps.html#7262" class="Postulate"
      >TotalMap.update-shadow</a
      ><a name="10464"
      > </a
      ><a name="10465" href="Maps.html#10434" class="Bound"
      >m</a
      ><a name="10466"
      > </a
      ><a name="10467" href="Maps.html#10436" class="Bound"
      >x</a
      ><a name="10468"
      > </a
      ><a name="10469" href="Maps.html#10438" class="Bound"
      >y</a
      >
</pre><!--{% endraw %}-->

<!--{% raw %}--><pre class="Agda">
  <a name="10498" href="Maps.html#10498" class="Function"
      >update-same</a
      ><a name="10509"
      > </a
      ><a name="10510" class="Symbol"
      >:</a
      ><a name="10511"
      > </a
      ><a name="10512" class="Symbol"
      >&#8704;</a
      ><a name="10513"
      > </a
      ><a name="10514" class="Symbol"
      >{</a
      ><a name="10515" href="Maps.html#10515" class="Bound"
      >A</a
      ><a name="10516"
      > </a
      ><a name="10517" href="Maps.html#10517" class="Bound"
      >v</a
      ><a name="10518" class="Symbol"
      >}</a
      ><a name="10519"
      > </a
      ><a name="10520" class="Symbol"
      >(</a
      ><a name="10521" href="Maps.html#10521" class="Bound"
      >m</a
      ><a name="10522"
      > </a
      ><a name="10523" class="Symbol"
      >:</a
      ><a name="10524"
      > </a
      ><a name="10525" href="Maps.html#9519" class="Function"
      >PartialMap</a
      ><a name="10535"
      > </a
      ><a name="10536" href="Maps.html#10515" class="Bound"
      >A</a
      ><a name="10537" class="Symbol"
      >)</a
      ><a name="10538"
      > </a
      ><a name="10539" class="Symbol"
      >(</a
      ><a name="10540" href="Maps.html#10540" class="Bound"
      >x</a
      ><a name="10541"
      > </a
      ><a name="10542" href="Maps.html#10542" class="Bound"
      >y</a
      ><a name="10543"
      > </a
      ><a name="10544" class="Symbol"
      >:</a
      ><a name="10545"
      > </a
      ><a name="10546" href="Maps.html#2400" class="Datatype"
      >Id</a
      ><a name="10548" class="Symbol"
      >)</a
      ><a name="10549"
      >
              </a
      ><a name="10564" class="Symbol"
      >&#8594;</a
      ><a name="10565"
      > </a
      ><a name="10566" href="Maps.html#10521" class="Bound"
      >m</a
      ><a name="10567"
      > </a
      ><a name="10568" href="Maps.html#10540" class="Bound"
      >x</a
      ><a name="10569"
      > </a
      ><a name="10570" href="Agda.Builtin.Equality.html#55" class="Datatype Operator"
      >&#8801;</a
      ><a name="10571"
      > </a
      ><a name="10572" href="https://agda.github.io/agda-stdlib/Data.Maybe.Base.html#373" class="InductiveConstructor"
      >just</a
      ><a name="10576"
      > </a
      ><a name="10577" href="Maps.html#10517" class="Bound"
      >v</a
      ><a name="10578"
      >
              </a
      ><a name="10593" class="Symbol"
      >&#8594;</a
      ><a name="10594"
      > </a
      ><a name="10595" class="Symbol"
      >(</a
      ><a name="10596" href="Maps.html#9741" class="Function"
      >update</a
      ><a name="10602"
      > </a
      ><a name="10603" href="Maps.html#10521" class="Bound"
      >m</a
      ><a name="10604"
      > </a
      ><a name="10605" href="Maps.html#10540" class="Bound"
      >x</a
      ><a name="10606"
      > </a
      ><a name="10607" href="Maps.html#10517" class="Bound"
      >v</a
      ><a name="10608" class="Symbol"
      >)</a
      ><a name="10609"
      > </a
      ><a name="10610" href="Maps.html#10542" class="Bound"
      >y</a
      ><a name="10611"
      > </a
      ><a name="10612" href="Agda.Builtin.Equality.html#55" class="Datatype Operator"
      >&#8801;</a
      ><a name="10613"
      > </a
      ><a name="10614" href="Maps.html#10521" class="Bound"
      >m</a
      ><a name="10615"
      > </a
      ><a name="10616" href="Maps.html#10542" class="Bound"
      >y</a
      ><a name="10617"
      >
  </a
      ><a name="10620" href="Maps.html#10498" class="Function"
      >update-same</a
      ><a name="10631"
      > </a
      ><a name="10632" href="Maps.html#10632" class="Bound"
      >m</a
      ><a name="10633"
      > </a
      ><a name="10634" href="Maps.html#10634" class="Bound"
      >x</a
      ><a name="10635"
      > </a
      ><a name="10636" href="Maps.html#10636" class="Bound"
      >y</a
      ><a name="10637"
      > </a
      ><a name="10638" href="Maps.html#10638" class="Bound"
      >mx=v</a
      ><a name="10642"
      > </a
      ><a name="10643" class="Keyword"
      >rewrite</a
      ><a name="10650"
      > </a
      ><a name="10651" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.Core.html#565" class="Function"
      >sym</a
      ><a name="10654"
      > </a
      ><a name="10655" href="Maps.html#10638" class="Bound"
      >mx=v</a
      ><a name="10659"
      > </a
      ><a name="10660" class="Symbol"
      >=</a
      ><a name="10661"
      > </a
      ><a name="10662" href="Maps.html#7918" class="Postulate"
      >TotalMap.update-same</a
      ><a name="10682"
      > </a
      ><a name="10683" href="Maps.html#10632" class="Bound"
      >m</a
      ><a name="10684"
      > </a
      ><a name="10685" href="Maps.html#10634" class="Bound"
      >x</a
      ><a name="10686"
      > </a
      ><a name="10687" href="Maps.html#10636" class="Bound"
      >y</a
      >
</pre><!--{% endraw %}-->

<!--{% raw %}--><pre class="Agda">
  <a name="10716" href="Maps.html#10716" class="Function"
      >update-permute</a
      ><a name="10730"
      > </a
      ><a name="10731" class="Symbol"
      >:</a
      ><a name="10732"
      > </a
      ><a name="10733" class="Symbol"
      >&#8704;</a
      ><a name="10734"
      > </a
      ><a name="10735" class="Symbol"
      >{</a
      ><a name="10736" href="Maps.html#10736" class="Bound"
      >A</a
      ><a name="10737"
      > </a
      ><a name="10738" href="Maps.html#10738" class="Bound"
      >v1</a
      ><a name="10740"
      > </a
      ><a name="10741" href="Maps.html#10741" class="Bound"
      >v2</a
      ><a name="10743" class="Symbol"
      >}</a
      ><a name="10744"
      > </a
      ><a name="10745" class="Symbol"
      >(</a
      ><a name="10746" href="Maps.html#10746" class="Bound"
      >m</a
      ><a name="10747"
      > </a
      ><a name="10748" class="Symbol"
      >:</a
      ><a name="10749"
      > </a
      ><a name="10750" href="Maps.html#9519" class="Function"
      >PartialMap</a
      ><a name="10760"
      > </a
      ><a name="10761" href="Maps.html#10736" class="Bound"
      >A</a
      ><a name="10762" class="Symbol"
      >)</a
      ><a name="10763"
      > </a
      ><a name="10764" class="Symbol"
      >(</a
      ><a name="10765" href="Maps.html#10765" class="Bound"
      >x1</a
      ><a name="10767"
      > </a
      ><a name="10768" href="Maps.html#10768" class="Bound"
      >x2</a
      ><a name="10770"
      > </a
      ><a name="10771" href="Maps.html#10771" class="Bound"
      >y</a
      ><a name="10772"
      > </a
      ><a name="10773" class="Symbol"
      >:</a
      ><a name="10774"
      > </a
      ><a name="10775" href="Maps.html#2400" class="Datatype"
      >Id</a
      ><a name="10777" class="Symbol"
      >)</a
      ><a name="10778"
      >
                 </a
      ><a name="10796" class="Symbol"
      >&#8594;</a
      ><a name="10797"
      > </a
      ><a name="10798" href="Maps.html#10765" class="Bound"
      >x1</a
      ><a name="10800"
      > </a
      ><a name="10801" href="https://agda.github.io/agda-stdlib/Relation.Binary.Core.html#4493" class="Function Operator"
      >&#8802;</a
      ><a name="10802"
      > </a
      ><a name="10803" href="Maps.html#10768" class="Bound"
      >x2</a
      ><a name="10805"
      > </a
      ><a name="10806" class="Symbol"
      >&#8594;</a
      ><a name="10807"
      > </a
      ><a name="10808" class="Symbol"
      >(</a
      ><a name="10809" href="Maps.html#9741" class="Function"
      >update</a
      ><a name="10815"
      > </a
      ><a name="10816" class="Symbol"
      >(</a
      ><a name="10817" href="Maps.html#9741" class="Function"
      >update</a
      ><a name="10823"
      > </a
      ><a name="10824" href="Maps.html#10746" class="Bound"
      >m</a
      ><a name="10825"
      > </a
      ><a name="10826" href="Maps.html#10768" class="Bound"
      >x2</a
      ><a name="10828"
      > </a
      ><a name="10829" href="Maps.html#10741" class="Bound"
      >v2</a
      ><a name="10831" class="Symbol"
      >)</a
      ><a name="10832"
      > </a
      ><a name="10833" href="Maps.html#10765" class="Bound"
      >x1</a
      ><a name="10835"
      > </a
      ><a name="10836" href="Maps.html#10738" class="Bound"
      >v1</a
      ><a name="10838" class="Symbol"
      >)</a
      ><a name="10839"
      > </a
      ><a name="10840" href="Maps.html#10771" class="Bound"
      >y</a
      ><a name="10841"
      >
                           </a
      ><a name="10869" href="Agda.Builtin.Equality.html#55" class="Datatype Operator"
      >&#8801;</a
      ><a name="10870"
      > </a
      ><a name="10871" class="Symbol"
      >(</a
      ><a name="10872" href="Maps.html#9741" class="Function"
      >update</a
      ><a name="10878"
      > </a
      ><a name="10879" class="Symbol"
      >(</a
      ><a name="10880" href="Maps.html#9741" class="Function"
      >update</a
      ><a name="10886"
      > </a
      ><a name="10887" href="Maps.html#10746" class="Bound"
      >m</a
      ><a name="10888"
      > </a
      ><a name="10889" href="Maps.html#10765" class="Bound"
      >x1</a
      ><a name="10891"
      > </a
      ><a name="10892" href="Maps.html#10738" class="Bound"
      >v1</a
      ><a name="10894" class="Symbol"
      >)</a
      ><a name="10895"
      > </a
      ><a name="10896" href="Maps.html#10768" class="Bound"
      >x2</a
      ><a name="10898"
      > </a
      ><a name="10899" href="Maps.html#10741" class="Bound"
      >v2</a
      ><a name="10901" class="Symbol"
      >)</a
      ><a name="10902"
      > </a
      ><a name="10903" href="Maps.html#10771" class="Bound"
      >y</a
      ><a name="10904"
      >
  </a
      ><a name="10907" href="Maps.html#10716" class="Function"
      >update-permute</a
      ><a name="10921"
      > </a
      ><a name="10922" href="Maps.html#10922" class="Bound"
      >m</a
      ><a name="10923"
      > </a
      ><a name="10924" href="Maps.html#10924" class="Bound"
      >x1</a
      ><a name="10926"
      > </a
      ><a name="10927" href="Maps.html#10927" class="Bound"
      >x2</a
      ><a name="10929"
      > </a
      ><a name="10930" href="Maps.html#10930" class="Bound"
      >y</a
      ><a name="10931"
      > </a
      ><a name="10932" href="Maps.html#10932" class="Bound"
      >x1&#8800;x2</a
      ><a name="10937"
      > </a
      ><a name="10938" class="Symbol"
      >=</a
      ><a name="10939"
      > </a
      ><a name="10940" href="Maps.html#8498" class="Postulate"
      >TotalMap.update-permute</a
      ><a name="10963"
      > </a
      ><a name="10964" href="Maps.html#10922" class="Bound"
      >m</a
      ><a name="10965"
      > </a
      ><a name="10966" href="Maps.html#10924" class="Bound"
      >x1</a
      ><a name="10968"
      > </a
      ><a name="10969" href="Maps.html#10927" class="Bound"
      >x2</a
      ><a name="10971"
      > </a
      ><a name="10972" href="Maps.html#10930" class="Bound"
      >y</a
      ><a name="10973"
      > </a
      ><a name="10974" href="Maps.html#10932" class="Bound"
      >x1&#8800;x2</a
      >
</pre><!--{% endraw %}-->
