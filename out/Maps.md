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

<pre class="Agda">

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
      ><a name="1568" href="https://agda.github.io/agda-stdlib/Data.Empty.html#360" class="Function"
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
      ><a name="1646" href="https://agda.github.io/agda-stdlib/Data.String.html#1" class="Module"
      >Data.String</a
      ><a name="1657"
      >      </a
      ><a name="1663" class="Keyword"
      >using</a
      ><a name="1668"
      > </a
      ><a name="1669" class="Symbol"
      >(</a
      ><a name="1670" href="https://agda.github.io/agda-stdlib/Agda.Builtin.String.html#165" class="Postulate"
      >String</a
      ><a name="1676" class="Symbol"
      >)</a
      ><a name="1677"
      >
</a
      ><a name="1678" class="Keyword"
      >open</a
      ><a name="1682"
      > </a
      ><a name="1683" class="Keyword"
      >import</a
      ><a name="1689"
      > </a
      ><a name="1690" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#1" class="Module"
      >Relation.Nullary</a
      ><a name="1706"
      > </a
      ><a name="1707" class="Keyword"
      >using</a
      ><a name="1712"
      > </a
      ><a name="1713" class="Symbol"
      >(</a
      ><a name="1714" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#414" class="Function Operator"
      >&#172;_</a
      ><a name="1716" class="Symbol"
      >;</a
      ><a name="1717"
      > </a
      ><a name="1718" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#484" class="Datatype"
      >Dec</a
      ><a name="1721" class="Symbol"
      >;</a
      ><a name="1722"
      > </a
      ><a name="1723" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#520" class="InductiveConstructor"
      >yes</a
      ><a name="1726" class="Symbol"
      >;</a
      ><a name="1727"
      > </a
      ><a name="1728" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#547" class="InductiveConstructor"
      >no</a
      ><a name="1730" class="Symbol"
      >)</a
      ><a name="1731"
      >
</a
      ><a name="1732" class="Keyword"
      >open</a
      ><a name="1736"
      > </a
      ><a name="1737" class="Keyword"
      >import</a
      ><a name="1743"
      > </a
      ><a name="1744" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#1" class="Module"
      >Relation.Binary.PropositionalEquality</a
      ><a name="1781"
      >
                             </a
      ><a name="1811" class="Keyword"
      >using</a
      ><a name="1816"
      > </a
      ><a name="1817" class="Symbol"
      >(</a
      ><a name="1818" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >_&#8801;_</a
      ><a name="1821" class="Symbol"
      >;</a
      ><a name="1822"
      > </a
      ><a name="1823" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="1827" class="Symbol"
      >;</a
      ><a name="1828"
      > </a
      ><a name="1829" href="https://agda.github.io/agda-stdlib/Relation.Binary.Core.html#4493" class="Function Operator"
      >_&#8802;_</a
      ><a name="1832" class="Symbol"
      >;</a
      ><a name="1833"
      > </a
      ><a name="1834" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.Core.html#632" class="Function"
      >trans</a
      ><a name="1839" class="Symbol"
      >;</a
      ><a name="1840"
      > </a
      ><a name="1841" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.Core.html#565" class="Function"
      >sym</a
      ><a name="1844" class="Symbol"
      >)</a
      >

</pre>

Documentation for the standard library can be found at
<https://agda.github.io/agda-stdlib/>.

## Identifiers

First, we need a type for the keys that we use to index into our
maps.  For this purpose, we again use the type `Id` from the
[Lists](sf/Lists.html) chapter.  To make this chapter self contained,
we repeat its definition here.

<pre class="Agda">

<a name="2210" class="Keyword"
      >data</a
      ><a name="2214"
      > </a
      ><a name="2215" href="Maps.html#2215" class="Datatype"
      >Id</a
      ><a name="2217"
      > </a
      ><a name="2218" class="Symbol"
      >:</a
      ><a name="2219"
      > </a
      ><a name="2220" class="PrimitiveType"
      >Set</a
      ><a name="2223"
      > </a
      ><a name="2224" class="Keyword"
      >where</a
      ><a name="2229"
      >
  </a
      ><a name="2232" href="Maps.html#2232" class="InductiveConstructor"
      >id</a
      ><a name="2234"
      > </a
      ><a name="2235" class="Symbol"
      >:</a
      ><a name="2236"
      > </a
      ><a name="2237" href="https://agda.github.io/agda-stdlib/Agda.Builtin.String.html#165" class="Postulate"
      >String</a
      ><a name="2243"
      > </a
      ><a name="2244" class="Symbol"
      >&#8594;</a
      ><a name="2245"
      > </a
      ><a name="2246" href="Maps.html#2215" class="Datatype"
      >Id</a
      >

</pre>

We recall a standard fact of logic.

<pre class="Agda">

<a name="2311" href="Maps.html#2311" class="Function"
      >contrapositive</a
      ><a name="2325"
      > </a
      ><a name="2326" class="Symbol"
      >:</a
      ><a name="2327"
      > </a
      ><a name="2328" class="Symbol"
      >&#8704;</a
      ><a name="2329"
      > </a
      ><a name="2330" class="Symbol"
      >{</a
      ><a name="2331" href="Maps.html#2331" class="Bound"
      >&#8467;&#8321;</a
      ><a name="2333"
      > </a
      ><a name="2334" href="Maps.html#2334" class="Bound"
      >&#8467;&#8322;</a
      ><a name="2336" class="Symbol"
      >}</a
      ><a name="2337"
      > </a
      ><a name="2338" class="Symbol"
      >{</a
      ><a name="2339" href="Maps.html#2339" class="Bound"
      >P</a
      ><a name="2340"
      > </a
      ><a name="2341" class="Symbol"
      >:</a
      ><a name="2342"
      > </a
      ><a name="2343" class="PrimitiveType"
      >Set</a
      ><a name="2346"
      > </a
      ><a name="2347" href="Maps.html#2331" class="Bound"
      >&#8467;&#8321;</a
      ><a name="2349" class="Symbol"
      >}</a
      ><a name="2350"
      > </a
      ><a name="2351" class="Symbol"
      >{</a
      ><a name="2352" href="Maps.html#2352" class="Bound"
      >Q</a
      ><a name="2353"
      > </a
      ><a name="2354" class="Symbol"
      >:</a
      ><a name="2355"
      > </a
      ><a name="2356" class="PrimitiveType"
      >Set</a
      ><a name="2359"
      > </a
      ><a name="2360" href="Maps.html#2334" class="Bound"
      >&#8467;&#8322;</a
      ><a name="2362" class="Symbol"
      >}</a
      ><a name="2363"
      > </a
      ><a name="2364" class="Symbol"
      >&#8594;</a
      ><a name="2365"
      > </a
      ><a name="2366" class="Symbol"
      >(</a
      ><a name="2367" href="Maps.html#2339" class="Bound"
      >P</a
      ><a name="2368"
      > </a
      ><a name="2369" class="Symbol"
      >&#8594;</a
      ><a name="2370"
      > </a
      ><a name="2371" href="Maps.html#2352" class="Bound"
      >Q</a
      ><a name="2372" class="Symbol"
      >)</a
      ><a name="2373"
      > </a
      ><a name="2374" class="Symbol"
      >&#8594;</a
      ><a name="2375"
      > </a
      ><a name="2376" class="Symbol"
      >(</a
      ><a name="2377" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#414" class="Function Operator"
      >&#172;</a
      ><a name="2378"
      > </a
      ><a name="2379" href="Maps.html#2352" class="Bound"
      >Q</a
      ><a name="2380"
      > </a
      ><a name="2381" class="Symbol"
      >&#8594;</a
      ><a name="2382"
      > </a
      ><a name="2383" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#414" class="Function Operator"
      >&#172;</a
      ><a name="2384"
      > </a
      ><a name="2385" href="Maps.html#2339" class="Bound"
      >P</a
      ><a name="2386" class="Symbol"
      >)</a
      ><a name="2387"
      >
</a
      ><a name="2388" href="Maps.html#2311" class="Function"
      >contrapositive</a
      ><a name="2402"
      > </a
      ><a name="2403" href="Maps.html#2403" class="Bound"
      >p&#8594;q</a
      ><a name="2406"
      > </a
      ><a name="2407" href="Maps.html#2407" class="Bound"
      >&#172;q</a
      ><a name="2409"
      > </a
      ><a name="2410" href="Maps.html#2410" class="Bound"
      >p</a
      ><a name="2411"
      > </a
      ><a name="2412" class="Symbol"
      >=</a
      ><a name="2413"
      > </a
      ><a name="2414" href="Maps.html#2407" class="Bound"
      >&#172;q</a
      ><a name="2416"
      > </a
      ><a name="2417" class="Symbol"
      >(</a
      ><a name="2418" href="Maps.html#2403" class="Bound"
      >p&#8594;q</a
      ><a name="2421"
      > </a
      ><a name="2422" href="Maps.html#2410" class="Bound"
      >p</a
      ><a name="2423" class="Symbol"
      >)</a
      >

</pre>

Using the above, we can decide equality of two identifiers
by deciding equality on the underlying strings.

<pre class="Agda">

<a name="2558" href="Maps.html#2558" class="Function Operator"
      >_&#8799;_</a
      ><a name="2561"
      > </a
      ><a name="2562" class="Symbol"
      >:</a
      ><a name="2563"
      > </a
      ><a name="2564" class="Symbol"
      >(</a
      ><a name="2565" href="Maps.html#2565" class="Bound"
      >x</a
      ><a name="2566"
      > </a
      ><a name="2567" href="Maps.html#2567" class="Bound"
      >y</a
      ><a name="2568"
      > </a
      ><a name="2569" class="Symbol"
      >:</a
      ><a name="2570"
      > </a
      ><a name="2571" href="Maps.html#2215" class="Datatype"
      >Id</a
      ><a name="2573" class="Symbol"
      >)</a
      ><a name="2574"
      > </a
      ><a name="2575" class="Symbol"
      >&#8594;</a
      ><a name="2576"
      > </a
      ><a name="2577" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#484" class="Datatype"
      >Dec</a
      ><a name="2580"
      > </a
      ><a name="2581" class="Symbol"
      >(</a
      ><a name="2582" href="Maps.html#2565" class="Bound"
      >x</a
      ><a name="2583"
      > </a
      ><a name="2584" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="2585"
      > </a
      ><a name="2586" href="Maps.html#2567" class="Bound"
      >y</a
      ><a name="2587" class="Symbol"
      >)</a
      ><a name="2588"
      >
</a
      ><a name="2589" href="Maps.html#2232" class="InductiveConstructor"
      >id</a
      ><a name="2591"
      > </a
      ><a name="2592" href="Maps.html#2592" class="Bound"
      >x</a
      ><a name="2593"
      > </a
      ><a name="2594" href="Maps.html#2558" class="Function Operator"
      >&#8799;</a
      ><a name="2595"
      > </a
      ><a name="2596" href="Maps.html#2232" class="InductiveConstructor"
      >id</a
      ><a name="2598"
      > </a
      ><a name="2599" href="Maps.html#2599" class="Bound"
      >y</a
      ><a name="2600"
      > </a
      ><a name="2601" class="Keyword"
      >with</a
      ><a name="2605"
      > </a
      ><a name="2606" href="Maps.html#2592" class="Bound"
      >x</a
      ><a name="2607"
      > </a
      ><a name="2608" href="https://agda.github.io/agda-stdlib/Data.String.html#1196" class="Function Operator"
      >Data.String.&#8799;</a
      ><a name="2621"
      > </a
      ><a name="2622" href="Maps.html#2599" class="Bound"
      >y</a
      ><a name="2623"
      >
</a
      ><a name="2624" href="Maps.html#2232" class="InductiveConstructor"
      >id</a
      ><a name="2626"
      > </a
      ><a name="2627" href="Maps.html#2627" class="Bound"
      >x</a
      ><a name="2628"
      > </a
      ><a name="2629" href="Maps.html#2558" class="Function Operator"
      >&#8799;</a
      ><a name="2630"
      > </a
      ><a name="2631" href="Maps.html#2232" class="InductiveConstructor"
      >id</a
      ><a name="2633"
      > </a
      ><a name="2634" href="Maps.html#2634" class="Bound"
      >y</a
      ><a name="2635"
      > </a
      ><a name="2636" class="Symbol"
      >|</a
      ><a name="2637"
      > </a
      ><a name="2638" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#520" class="InductiveConstructor"
      >yes</a
      ><a name="2641"
      > </a
      ><a name="2642" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="2646"
      >  </a
      ><a name="2648" class="Symbol"
      >=</a
      ><a name="2649"
      >  </a
      ><a name="2651" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#520" class="InductiveConstructor"
      >yes</a
      ><a name="2654"
      > </a
      ><a name="2655" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="2659"
      >
</a
      ><a name="2660" href="Maps.html#2232" class="InductiveConstructor"
      >id</a
      ><a name="2662"
      > </a
      ><a name="2663" href="Maps.html#2663" class="Bound"
      >x</a
      ><a name="2664"
      > </a
      ><a name="2665" href="Maps.html#2558" class="Function Operator"
      >&#8799;</a
      ><a name="2666"
      > </a
      ><a name="2667" href="Maps.html#2232" class="InductiveConstructor"
      >id</a
      ><a name="2669"
      > </a
      ><a name="2670" href="Maps.html#2670" class="Bound"
      >y</a
      ><a name="2671"
      > </a
      ><a name="2672" class="Symbol"
      >|</a
      ><a name="2673"
      > </a
      ><a name="2674" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#547" class="InductiveConstructor"
      >no</a
      ><a name="2676"
      >  </a
      ><a name="2678" href="Maps.html#2678" class="Bound"
      >x&#8802;y</a
      ><a name="2681"
      >   </a
      ><a name="2684" class="Symbol"
      >=</a
      ><a name="2685"
      >  </a
      ><a name="2687" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#547" class="InductiveConstructor"
      >no</a
      ><a name="2689"
      > </a
      ><a name="2690" class="Symbol"
      >(</a
      ><a name="2691" href="Maps.html#2311" class="Function"
      >contrapositive</a
      ><a name="2705"
      > </a
      ><a name="2706" href="Maps.html#2730" class="Function"
      >id-inj</a
      ><a name="2712"
      > </a
      ><a name="2713" href="Maps.html#2678" class="Bound"
      >x&#8802;y</a
      ><a name="2716" class="Symbol"
      >)</a
      ><a name="2717"
      >
  </a
      ><a name="2720" class="Keyword"
      >where</a
      ><a name="2725"
      >
    </a
      ><a name="2730" href="Maps.html#2730" class="Function"
      >id-inj</a
      ><a name="2736"
      > </a
      ><a name="2737" class="Symbol"
      >:</a
      ><a name="2738"
      > </a
      ><a name="2739" class="Symbol"
      >&#8704;</a
      ><a name="2740"
      > </a
      ><a name="2741" class="Symbol"
      >{</a
      ><a name="2742" href="Maps.html#2742" class="Bound"
      >x</a
      ><a name="2743"
      > </a
      ><a name="2744" href="Maps.html#2744" class="Bound"
      >y</a
      ><a name="2745" class="Symbol"
      >}</a
      ><a name="2746"
      > </a
      ><a name="2747" class="Symbol"
      >&#8594;</a
      ><a name="2748"
      > </a
      ><a name="2749" href="Maps.html#2232" class="InductiveConstructor"
      >id</a
      ><a name="2751"
      > </a
      ><a name="2752" href="Maps.html#2742" class="Bound"
      >x</a
      ><a name="2753"
      > </a
      ><a name="2754" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="2755"
      > </a
      ><a name="2756" href="Maps.html#2232" class="InductiveConstructor"
      >id</a
      ><a name="2758"
      > </a
      ><a name="2759" href="Maps.html#2744" class="Bound"
      >y</a
      ><a name="2760"
      > </a
      ><a name="2761" class="Symbol"
      >&#8594;</a
      ><a name="2762"
      > </a
      ><a name="2763" href="Maps.html#2742" class="Bound"
      >x</a
      ><a name="2764"
      > </a
      ><a name="2765" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="2766"
      > </a
      ><a name="2767" href="Maps.html#2744" class="Bound"
      >y</a
      ><a name="2768"
      >
    </a
      ><a name="2773" href="Maps.html#2730" class="Function"
      >id-inj</a
      ><a name="2779"
      > </a
      ><a name="2780" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="2784"
      >  </a
      ><a name="2786" class="Symbol"
      >=</a
      ><a name="2787"
      >  </a
      ><a name="2789" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      >

</pre>

We define some identifiers for future use.

<pre class="Agda">

<a name="2863" href="Maps.html#2863" class="Function"
      >x</a
      ><a name="2864"
      > </a
      ><a name="2865" href="Maps.html#2865" class="Function"
      >y</a
      ><a name="2866"
      > </a
      ><a name="2867" href="Maps.html#2867" class="Function"
      >z</a
      ><a name="2868"
      > </a
      ><a name="2869" class="Symbol"
      >:</a
      ><a name="2870"
      > </a
      ><a name="2871" href="Maps.html#2215" class="Datatype"
      >Id</a
      ><a name="2873"
      >
</a
      ><a name="2874" href="Maps.html#2863" class="Function"
      >x</a
      ><a name="2875"
      > </a
      ><a name="2876" class="Symbol"
      >=</a
      ><a name="2877"
      > </a
      ><a name="2878" href="Maps.html#2232" class="InductiveConstructor"
      >id</a
      ><a name="2880"
      > </a
      ><a name="2881" class="String"
      >&quot;x&quot;</a
      ><a name="2884"
      >
</a
      ><a name="2885" href="Maps.html#2865" class="Function"
      >y</a
      ><a name="2886"
      > </a
      ><a name="2887" class="Symbol"
      >=</a
      ><a name="2888"
      > </a
      ><a name="2889" href="Maps.html#2232" class="InductiveConstructor"
      >id</a
      ><a name="2891"
      > </a
      ><a name="2892" class="String"
      >&quot;y&quot;</a
      ><a name="2895"
      >
</a
      ><a name="2896" href="Maps.html#2867" class="Function"
      >z</a
      ><a name="2897"
      > </a
      ><a name="2898" class="Symbol"
      >=</a
      ><a name="2899"
      > </a
      ><a name="2900" href="Maps.html#2232" class="InductiveConstructor"
      >id</a
      ><a name="2902"
      > </a
      ><a name="2903" class="String"
      >&quot;z&quot;</a
      >

</pre>

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

<pre class="Agda">

<a name="3738" href="Maps.html#3738" class="Function"
      >TotalMap</a
      ><a name="3746"
      > </a
      ><a name="3747" class="Symbol"
      >:</a
      ><a name="3748"
      > </a
      ><a name="3749" class="PrimitiveType"
      >Set</a
      ><a name="3752"
      > </a
      ><a name="3753" class="Symbol"
      >&#8594;</a
      ><a name="3754"
      > </a
      ><a name="3755" class="PrimitiveType"
      >Set</a
      ><a name="3758"
      >
</a
      ><a name="3759" href="Maps.html#3738" class="Function"
      >TotalMap</a
      ><a name="3767"
      > </a
      ><a name="3768" href="Maps.html#3768" class="Bound"
      >A</a
      ><a name="3769"
      > </a
      ><a name="3770" class="Symbol"
      >=</a
      ><a name="3771"
      > </a
      ><a name="3772" href="Maps.html#2215" class="Datatype"
      >Id</a
      ><a name="3774"
      > </a
      ><a name="3775" class="Symbol"
      >&#8594;</a
      ><a name="3776"
      > </a
      ><a name="3777" href="Maps.html#3768" class="Bound"
      >A</a
      >

</pre>

Intuitively, a total map over anﬁ element type `A` _is_ just a
function that can be used to look up ids, yielding `A`s.

<pre class="Agda">

<a name="3925" class="Keyword"
      >module</a
      ><a name="3931"
      > </a
      ><a name="3932" href="Maps.html#3932" class="Module"
      >TotalMap</a
      ><a name="3940"
      > </a
      ><a name="3941" class="Keyword"
      >where</a
      >

</pre>

The function `always` yields a total map given a
default element; this map always returns the default element when
applied to any id.

<pre class="Agda">

  <a name="4109" href="Maps.html#4109" class="Function"
      >always</a
      ><a name="4115"
      > </a
      ><a name="4116" class="Symbol"
      >:</a
      ><a name="4117"
      > </a
      ><a name="4118" class="Symbol"
      >&#8704;</a
      ><a name="4119"
      > </a
      ><a name="4120" class="Symbol"
      >{</a
      ><a name="4121" href="Maps.html#4121" class="Bound"
      >A</a
      ><a name="4122" class="Symbol"
      >}</a
      ><a name="4123"
      > </a
      ><a name="4124" class="Symbol"
      >&#8594;</a
      ><a name="4125"
      > </a
      ><a name="4126" href="Maps.html#4121" class="Bound"
      >A</a
      ><a name="4127"
      > </a
      ><a name="4128" class="Symbol"
      >&#8594;</a
      ><a name="4129"
      > </a
      ><a name="4130" href="Maps.html#3738" class="Function"
      >TotalMap</a
      ><a name="4138"
      > </a
      ><a name="4139" href="Maps.html#4121" class="Bound"
      >A</a
      ><a name="4140"
      >
  </a
      ><a name="4143" href="Maps.html#4109" class="Function"
      >always</a
      ><a name="4149"
      > </a
      ><a name="4150" href="Maps.html#4150" class="Bound"
      >v</a
      ><a name="4151"
      > </a
      ><a name="4152" href="Maps.html#4152" class="Bound"
      >x</a
      ><a name="4153"
      > </a
      ><a name="4154" class="Symbol"
      >=</a
      ><a name="4155"
      > </a
      ><a name="4156" href="Maps.html#4150" class="Bound"
      >v</a
      >

</pre>

More interesting is the update function, which (as before) takes
a map `ρ`, a key `x`, and a value `v` and returns a new map that
takes `x` to `v` and takes every other key to whatever `ρ` does.

<pre class="Agda">

  <a name="4381" class="Keyword"
      >infixl</a
      ><a name="4387"
      > </a
      ><a name="4388" class="Number"
      >100</a
      ><a name="4391"
      > </a
      ><a name="4392" href="Maps.html#4403" class="Function Operator"
      >_,_&#8614;_</a
      ><a name="4397"
      >  

  </a
      ><a name="4403" href="Maps.html#4403" class="Function Operator"
      >_,_&#8614;_</a
      ><a name="4408"
      > </a
      ><a name="4409" class="Symbol"
      >:</a
      ><a name="4410"
      > </a
      ><a name="4411" class="Symbol"
      >&#8704;</a
      ><a name="4412"
      > </a
      ><a name="4413" class="Symbol"
      >{</a
      ><a name="4414" href="Maps.html#4414" class="Bound"
      >A</a
      ><a name="4415" class="Symbol"
      >}</a
      ><a name="4416"
      > </a
      ><a name="4417" class="Symbol"
      >&#8594;</a
      ><a name="4418"
      > </a
      ><a name="4419" href="Maps.html#3738" class="Function"
      >TotalMap</a
      ><a name="4427"
      > </a
      ><a name="4428" href="Maps.html#4414" class="Bound"
      >A</a
      ><a name="4429"
      > </a
      ><a name="4430" class="Symbol"
      >&#8594;</a
      ><a name="4431"
      > </a
      ><a name="4432" href="Maps.html#2215" class="Datatype"
      >Id</a
      ><a name="4434"
      > </a
      ><a name="4435" class="Symbol"
      >&#8594;</a
      ><a name="4436"
      > </a
      ><a name="4437" href="Maps.html#4414" class="Bound"
      >A</a
      ><a name="4438"
      > </a
      ><a name="4439" class="Symbol"
      >&#8594;</a
      ><a name="4440"
      > </a
      ><a name="4441" href="Maps.html#3738" class="Function"
      >TotalMap</a
      ><a name="4449"
      > </a
      ><a name="4450" href="Maps.html#4414" class="Bound"
      >A</a
      ><a name="4451"
      >
  </a
      ><a name="4454" class="Symbol"
      >(</a
      ><a name="4455" href="Maps.html#4455" class="Bound"
      >&#961;</a
      ><a name="4456"
      > </a
      ><a name="4457" href="Maps.html#4403" class="Function Operator"
      >,</a
      ><a name="4458"
      > </a
      ><a name="4459" href="Maps.html#4459" class="Bound"
      >x</a
      ><a name="4460"
      > </a
      ><a name="4461" href="Maps.html#4403" class="Function Operator"
      >&#8614;</a
      ><a name="4462"
      > </a
      ><a name="4463" href="Maps.html#4463" class="Bound"
      >v</a
      ><a name="4464" class="Symbol"
      >)</a
      ><a name="4465"
      > </a
      ><a name="4466" href="Maps.html#4466" class="Bound"
      >y</a
      ><a name="4467"
      > </a
      ><a name="4468" class="Keyword"
      >with</a
      ><a name="4472"
      > </a
      ><a name="4473" href="Maps.html#4459" class="Bound"
      >x</a
      ><a name="4474"
      > </a
      ><a name="4475" href="Maps.html#2558" class="Function Operator"
      >&#8799;</a
      ><a name="4476"
      > </a
      ><a name="4477" href="Maps.html#4466" class="Bound"
      >y</a
      ><a name="4478"
      >
  </a
      ><a name="4481" class="Symbol"
      >...</a
      ><a name="4484"
      > </a
      ><a name="4485" class="Symbol"
      >|</a
      ><a name="4486"
      > </a
      ><a name="4487" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#520" class="InductiveConstructor"
      >yes</a
      ><a name="4490"
      > </a
      ><a name="4491" href="Maps.html#4491" class="Bound"
      >x=y</a
      ><a name="4494"
      > </a
      ><a name="4495" class="Symbol"
      >=</a
      ><a name="4496"
      > </a
      ><a name="4497" href="Maps.html#4463" class="Bound"
      >v</a
      ><a name="4498"
      >
  </a
      ><a name="4501" class="Symbol"
      >...</a
      ><a name="4504"
      > </a
      ><a name="4505" class="Symbol"
      >|</a
      ><a name="4506"
      > </a
      ><a name="4507" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#547" class="InductiveConstructor"
      >no</a
      ><a name="4509"
      >  </a
      ><a name="4511" href="Maps.html#4511" class="Bound"
      >x&#8800;y</a
      ><a name="4514"
      > </a
      ><a name="4515" class="Symbol"
      >=</a
      ><a name="4516"
      > </a
      ><a name="4517" href="Maps.html#4455" class="Bound"
      >&#961;</a
      ><a name="4518"
      > </a
      ><a name="4519" href="Maps.html#4466" class="Bound"
      >y</a
      >

</pre>

This definition is a nice example of higher-order programming.
The update function takes a _function_ `ρ` and yields a new
function that behaves like the desired map.

For example, we can build a map taking ids to naturals, where `x`
maps to 42, `y` maps to 69, and every other key maps to 0, as follows:

<pre class="Agda">

  <a name="4854" href="Maps.html#4854" class="Function"
      >&#961;&#8320;</a
      ><a name="4856"
      > </a
      ><a name="4857" class="Symbol"
      >:</a
      ><a name="4858"
      > </a
      ><a name="4859" href="Maps.html#3738" class="Function"
      >TotalMap</a
      ><a name="4867"
      > </a
      ><a name="4868" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#97" class="Datatype"
      >&#8469;</a
      ><a name="4869"
      >
  </a
      ><a name="4872" href="Maps.html#4854" class="Function"
      >&#961;&#8320;</a
      ><a name="4874"
      > </a
      ><a name="4875" class="Symbol"
      >=</a
      ><a name="4876"
      > </a
      ><a name="4877" href="Maps.html#4109" class="Function"
      >always</a
      ><a name="4883"
      > </a
      ><a name="4884" class="Number"
      >0</a
      ><a name="4885"
      > </a
      ><a name="4886" href="Maps.html#4403" class="Function Operator"
      >,</a
      ><a name="4887"
      > </a
      ><a name="4888" href="Maps.html#2863" class="Function"
      >x</a
      ><a name="4889"
      > </a
      ><a name="4890" href="Maps.html#4403" class="Function Operator"
      >&#8614;</a
      ><a name="4891"
      > </a
      ><a name="4892" class="Number"
      >42</a
      ><a name="4894"
      > </a
      ><a name="4895" href="Maps.html#4403" class="Function Operator"
      >,</a
      ><a name="4896"
      > </a
      ><a name="4897" href="Maps.html#2865" class="Function"
      >y</a
      ><a name="4898"
      > </a
      ><a name="4899" href="Maps.html#4403" class="Function Operator"
      >&#8614;</a
      ><a name="4900"
      > </a
      ><a name="4901" class="Number"
      >69</a
      >

</pre>

This completes the definition of total maps.  Note that we don't
need to define a `find` operation because it is just function
application!

<pre class="Agda">

  <a name="5072" href="Maps.html#5072" class="Function"
      >test&#8321;</a
      ><a name="5077"
      > </a
      ><a name="5078" class="Symbol"
      >:</a
      ><a name="5079"
      > </a
      ><a name="5080" href="Maps.html#4854" class="Function"
      >&#961;&#8320;</a
      ><a name="5082"
      > </a
      ><a name="5083" href="Maps.html#2863" class="Function"
      >x</a
      ><a name="5084"
      > </a
      ><a name="5085" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="5086"
      > </a
      ><a name="5087" class="Number"
      >42</a
      ><a name="5089"
      >
  </a
      ><a name="5092" href="Maps.html#5072" class="Function"
      >test&#8321;</a
      ><a name="5097"
      > </a
      ><a name="5098" class="Symbol"
      >=</a
      ><a name="5099"
      > </a
      ><a name="5100" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="5104"
      >

  </a
      ><a name="5108" href="Maps.html#5108" class="Function"
      >test&#8322;</a
      ><a name="5113"
      > </a
      ><a name="5114" class="Symbol"
      >:</a
      ><a name="5115"
      > </a
      ><a name="5116" href="Maps.html#4854" class="Function"
      >&#961;&#8320;</a
      ><a name="5118"
      > </a
      ><a name="5119" href="Maps.html#2865" class="Function"
      >y</a
      ><a name="5120"
      > </a
      ><a name="5121" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="5122"
      > </a
      ><a name="5123" class="Number"
      >69</a
      ><a name="5125"
      >
  </a
      ><a name="5128" href="Maps.html#5108" class="Function"
      >test&#8322;</a
      ><a name="5133"
      > </a
      ><a name="5134" class="Symbol"
      >=</a
      ><a name="5135"
      > </a
      ><a name="5136" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="5140"
      >

  </a
      ><a name="5144" href="Maps.html#5144" class="Function"
      >test&#8323;</a
      ><a name="5149"
      > </a
      ><a name="5150" class="Symbol"
      >:</a
      ><a name="5151"
      > </a
      ><a name="5152" href="Maps.html#4854" class="Function"
      >&#961;&#8320;</a
      ><a name="5154"
      > </a
      ><a name="5155" href="Maps.html#2867" class="Function"
      >z</a
      ><a name="5156"
      > </a
      ><a name="5157" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="5158"
      > </a
      ><a name="5159" class="Number"
      >0</a
      ><a name="5160"
      >
  </a
      ><a name="5163" href="Maps.html#5144" class="Function"
      >test&#8323;</a
      ><a name="5168"
      > </a
      ><a name="5169" class="Symbol"
      >=</a
      ><a name="5170"
      > </a
      ><a name="5171" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      >

</pre>

To use maps in later chapters, we'll need several fundamental
facts about how they behave.  Even if you don't work the following
exercises, make sure you understand the statements of
the lemmas!

#### Exercise: 1 star, optional (apply-always)
The `always` map returns its default element for all keys:

<pre class="Agda">

  <a name="5506" class="Keyword"
      >postulate</a
      ><a name="5515"
      >
    </a
      ><a name="5520" href="Maps.html#5520" class="Postulate"
      >apply-always</a
      ><a name="5532"
      > </a
      ><a name="5533" class="Symbol"
      >:</a
      ><a name="5534"
      > </a
      ><a name="5535" class="Symbol"
      >&#8704;</a
      ><a name="5536"
      > </a
      ><a name="5537" class="Symbol"
      >{</a
      ><a name="5538" href="Maps.html#5538" class="Bound"
      >A</a
      ><a name="5539" class="Symbol"
      >}</a
      ><a name="5540"
      > </a
      ><a name="5541" class="Symbol"
      >(</a
      ><a name="5542" href="Maps.html#5542" class="Bound"
      >v</a
      ><a name="5543"
      > </a
      ><a name="5544" class="Symbol"
      >:</a
      ><a name="5545"
      > </a
      ><a name="5546" href="Maps.html#5538" class="Bound"
      >A</a
      ><a name="5547" class="Symbol"
      >)</a
      ><a name="5548"
      > </a
      ><a name="5549" class="Symbol"
      >(</a
      ><a name="5550" href="Maps.html#5550" class="Bound"
      >x</a
      ><a name="5551"
      > </a
      ><a name="5552" class="Symbol"
      >:</a
      ><a name="5553"
      > </a
      ><a name="5554" href="Maps.html#2215" class="Datatype"
      >Id</a
      ><a name="5556" class="Symbol"
      >)</a
      ><a name="5557"
      > </a
      ><a name="5558" class="Symbol"
      >&#8594;</a
      ><a name="5559"
      > </a
      ><a name="5560" href="Maps.html#4109" class="Function"
      >always</a
      ><a name="5566"
      > </a
      ><a name="5567" href="Maps.html#5542" class="Bound"
      >v</a
      ><a name="5568"
      > </a
      ><a name="5569" href="Maps.html#5550" class="Bound"
      >x</a
      ><a name="5570"
      > </a
      ><a name="5571" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="5572"
      > </a
      ><a name="5573" href="Maps.html#5542" class="Bound"
      >v</a
      >

</pre>

<div class="hidden">
<pre class="Agda">

  <a name="5623" href="Maps.html#5623" class="Function"
      >apply-always&#8242;</a
      ><a name="5636"
      > </a
      ><a name="5637" class="Symbol"
      >:</a
      ><a name="5638"
      > </a
      ><a name="5639" class="Symbol"
      >&#8704;</a
      ><a name="5640"
      > </a
      ><a name="5641" class="Symbol"
      >{</a
      ><a name="5642" href="Maps.html#5642" class="Bound"
      >A</a
      ><a name="5643" class="Symbol"
      >}</a
      ><a name="5644"
      > </a
      ><a name="5645" class="Symbol"
      >(</a
      ><a name="5646" href="Maps.html#5646" class="Bound"
      >v</a
      ><a name="5647"
      > </a
      ><a name="5648" class="Symbol"
      >:</a
      ><a name="5649"
      > </a
      ><a name="5650" href="Maps.html#5642" class="Bound"
      >A</a
      ><a name="5651" class="Symbol"
      >)</a
      ><a name="5652"
      > </a
      ><a name="5653" class="Symbol"
      >(</a
      ><a name="5654" href="Maps.html#5654" class="Bound"
      >x</a
      ><a name="5655"
      > </a
      ><a name="5656" class="Symbol"
      >:</a
      ><a name="5657"
      > </a
      ><a name="5658" href="Maps.html#2215" class="Datatype"
      >Id</a
      ><a name="5660" class="Symbol"
      >)</a
      ><a name="5661"
      > </a
      ><a name="5662" class="Symbol"
      >&#8594;</a
      ><a name="5663"
      > </a
      ><a name="5664" href="Maps.html#4109" class="Function"
      >always</a
      ><a name="5670"
      > </a
      ><a name="5671" href="Maps.html#5646" class="Bound"
      >v</a
      ><a name="5672"
      > </a
      ><a name="5673" href="Maps.html#5654" class="Bound"
      >x</a
      ><a name="5674"
      > </a
      ><a name="5675" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="5676"
      > </a
      ><a name="5677" href="Maps.html#5646" class="Bound"
      >v</a
      ><a name="5678"
      >
  </a
      ><a name="5681" href="Maps.html#5623" class="Function"
      >apply-always&#8242;</a
      ><a name="5694"
      > </a
      ><a name="5695" href="Maps.html#5695" class="Bound"
      >v</a
      ><a name="5696"
      > </a
      ><a name="5697" href="Maps.html#5697" class="Bound"
      >x</a
      ><a name="5698"
      > </a
      ><a name="5699" class="Symbol"
      >=</a
      ><a name="5700"
      > </a
      ><a name="5701" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      >

</pre>
</div>

#### Exercise: 2 stars, optional (update-eq)
Next, if we update a map `ρ` at a key `x` with a new value `v`
and then look up `x` in the map resulting from the update, we get
back `v`:

<pre class="Agda">

  <a name="5925" class="Keyword"
      >postulate</a
      ><a name="5934"
      >
    </a
      ><a name="5939" href="Maps.html#5939" class="Postulate"
      >update-eq</a
      ><a name="5948"
      > </a
      ><a name="5949" class="Symbol"
      >:</a
      ><a name="5950"
      > </a
      ><a name="5951" class="Symbol"
      >&#8704;</a
      ><a name="5952"
      > </a
      ><a name="5953" class="Symbol"
      >{</a
      ><a name="5954" href="Maps.html#5954" class="Bound"
      >A</a
      ><a name="5955" class="Symbol"
      >}</a
      ><a name="5956"
      > </a
      ><a name="5957" class="Symbol"
      >(</a
      ><a name="5958" href="Maps.html#5958" class="Bound"
      >&#961;</a
      ><a name="5959"
      > </a
      ><a name="5960" class="Symbol"
      >:</a
      ><a name="5961"
      > </a
      ><a name="5962" href="Maps.html#3738" class="Function"
      >TotalMap</a
      ><a name="5970"
      > </a
      ><a name="5971" href="Maps.html#5954" class="Bound"
      >A</a
      ><a name="5972" class="Symbol"
      >)</a
      ><a name="5973"
      > </a
      ><a name="5974" class="Symbol"
      >(</a
      ><a name="5975" href="Maps.html#5975" class="Bound"
      >x</a
      ><a name="5976"
      > </a
      ><a name="5977" class="Symbol"
      >:</a
      ><a name="5978"
      > </a
      ><a name="5979" href="Maps.html#2215" class="Datatype"
      >Id</a
      ><a name="5981" class="Symbol"
      >)</a
      ><a name="5982"
      > </a
      ><a name="5983" class="Symbol"
      >(</a
      ><a name="5984" href="Maps.html#5984" class="Bound"
      >v</a
      ><a name="5985"
      > </a
      ><a name="5986" class="Symbol"
      >:</a
      ><a name="5987"
      > </a
      ><a name="5988" href="Maps.html#5954" class="Bound"
      >A</a
      ><a name="5989" class="Symbol"
      >)</a
      ><a name="5990"
      >
              </a
      ><a name="6005" class="Symbol"
      >&#8594;</a
      ><a name="6006"
      > </a
      ><a name="6007" class="Symbol"
      >(</a
      ><a name="6008" href="Maps.html#5958" class="Bound"
      >&#961;</a
      ><a name="6009"
      > </a
      ><a name="6010" href="Maps.html#4403" class="Function Operator"
      >,</a
      ><a name="6011"
      > </a
      ><a name="6012" href="Maps.html#5975" class="Bound"
      >x</a
      ><a name="6013"
      > </a
      ><a name="6014" href="Maps.html#4403" class="Function Operator"
      >&#8614;</a
      ><a name="6015"
      > </a
      ><a name="6016" href="Maps.html#5984" class="Bound"
      >v</a
      ><a name="6017" class="Symbol"
      >)</a
      ><a name="6018"
      > </a
      ><a name="6019" href="Maps.html#5975" class="Bound"
      >x</a
      ><a name="6020"
      > </a
      ><a name="6021" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="6022"
      > </a
      ><a name="6023" href="Maps.html#5984" class="Bound"
      >v</a
      >

</pre>

<div class="hidden">
<pre class="Agda">

  <a name="6073" href="Maps.html#6073" class="Function"
      >update-eq&#8242;</a
      ><a name="6083"
      > </a
      ><a name="6084" class="Symbol"
      >:</a
      ><a name="6085"
      > </a
      ><a name="6086" class="Symbol"
      >&#8704;</a
      ><a name="6087"
      > </a
      ><a name="6088" class="Symbol"
      >{</a
      ><a name="6089" href="Maps.html#6089" class="Bound"
      >A</a
      ><a name="6090" class="Symbol"
      >}</a
      ><a name="6091"
      > </a
      ><a name="6092" class="Symbol"
      >(</a
      ><a name="6093" href="Maps.html#6093" class="Bound"
      >&#961;</a
      ><a name="6094"
      > </a
      ><a name="6095" class="Symbol"
      >:</a
      ><a name="6096"
      > </a
      ><a name="6097" href="Maps.html#3738" class="Function"
      >TotalMap</a
      ><a name="6105"
      > </a
      ><a name="6106" href="Maps.html#6089" class="Bound"
      >A</a
      ><a name="6107" class="Symbol"
      >)</a
      ><a name="6108"
      > </a
      ><a name="6109" class="Symbol"
      >(</a
      ><a name="6110" href="Maps.html#6110" class="Bound"
      >x</a
      ><a name="6111"
      > </a
      ><a name="6112" class="Symbol"
      >:</a
      ><a name="6113"
      > </a
      ><a name="6114" href="Maps.html#2215" class="Datatype"
      >Id</a
      ><a name="6116" class="Symbol"
      >)</a
      ><a name="6117"
      > </a
      ><a name="6118" class="Symbol"
      >(</a
      ><a name="6119" href="Maps.html#6119" class="Bound"
      >v</a
      ><a name="6120"
      > </a
      ><a name="6121" class="Symbol"
      >:</a
      ><a name="6122"
      > </a
      ><a name="6123" href="Maps.html#6089" class="Bound"
      >A</a
      ><a name="6124" class="Symbol"
      >)</a
      ><a name="6125"
      >
             </a
      ><a name="6139" class="Symbol"
      >&#8594;</a
      ><a name="6140"
      > </a
      ><a name="6141" class="Symbol"
      >(</a
      ><a name="6142" href="Maps.html#6093" class="Bound"
      >&#961;</a
      ><a name="6143"
      > </a
      ><a name="6144" href="Maps.html#4403" class="Function Operator"
      >,</a
      ><a name="6145"
      > </a
      ><a name="6146" href="Maps.html#6110" class="Bound"
      >x</a
      ><a name="6147"
      > </a
      ><a name="6148" href="Maps.html#4403" class="Function Operator"
      >&#8614;</a
      ><a name="6149"
      > </a
      ><a name="6150" href="Maps.html#6119" class="Bound"
      >v</a
      ><a name="6151" class="Symbol"
      >)</a
      ><a name="6152"
      > </a
      ><a name="6153" href="Maps.html#6110" class="Bound"
      >x</a
      ><a name="6154"
      > </a
      ><a name="6155" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="6156"
      > </a
      ><a name="6157" href="Maps.html#6119" class="Bound"
      >v</a
      ><a name="6158"
      >
  </a
      ><a name="6161" href="Maps.html#6073" class="Function"
      >update-eq&#8242;</a
      ><a name="6171"
      > </a
      ><a name="6172" href="Maps.html#6172" class="Bound"
      >&#961;</a
      ><a name="6173"
      > </a
      ><a name="6174" href="Maps.html#6174" class="Bound"
      >x</a
      ><a name="6175"
      > </a
      ><a name="6176" href="Maps.html#6176" class="Bound"
      >v</a
      ><a name="6177"
      > </a
      ><a name="6178" class="Keyword"
      >with</a
      ><a name="6182"
      > </a
      ><a name="6183" href="Maps.html#6174" class="Bound"
      >x</a
      ><a name="6184"
      > </a
      ><a name="6185" href="Maps.html#2558" class="Function Operator"
      >&#8799;</a
      ><a name="6186"
      > </a
      ><a name="6187" href="Maps.html#6174" class="Bound"
      >x</a
      ><a name="6188"
      >
  </a
      ><a name="6191" class="Symbol"
      >...</a
      ><a name="6194"
      > </a
      ><a name="6195" class="Symbol"
      >|</a
      ><a name="6196"
      > </a
      ><a name="6197" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#520" class="InductiveConstructor"
      >yes</a
      ><a name="6200"
      > </a
      ><a name="6201" href="Maps.html#6201" class="Bound"
      >x&#8801;x</a
      ><a name="6204"
      > </a
      ><a name="6205" class="Symbol"
      >=</a
      ><a name="6206"
      > </a
      ><a name="6207" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="6211"
      >
  </a
      ><a name="6214" class="Symbol"
      >...</a
      ><a name="6217"
      > </a
      ><a name="6218" class="Symbol"
      >|</a
      ><a name="6219"
      > </a
      ><a name="6220" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#547" class="InductiveConstructor"
      >no</a
      ><a name="6222"
      >  </a
      ><a name="6224" href="Maps.html#6224" class="Bound"
      >x&#8802;x</a
      ><a name="6227"
      > </a
      ><a name="6228" class="Symbol"
      >=</a
      ><a name="6229"
      > </a
      ><a name="6230" href="https://agda.github.io/agda-stdlib/Data.Empty.html#360" class="Function"
      >&#8869;-elim</a
      ><a name="6236"
      > </a
      ><a name="6237" class="Symbol"
      >(</a
      ><a name="6238" href="Maps.html#6224" class="Bound"
      >x&#8802;x</a
      ><a name="6241"
      > </a
      ><a name="6242" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="6246" class="Symbol"
      >)</a
      >

</pre>
</div>

#### Exercise: 2 stars, optional (update-neq)
On the other hand, if we update a map `m` at a key `x` and
then look up a _different_ key `y` in the resulting map, we get
the same result that `m` would have given:

<pre class="Agda">

  <a name="6495" href="Maps.html#6495" class="Function"
      >update-neq</a
      ><a name="6505"
      > </a
      ><a name="6506" class="Symbol"
      >:</a
      ><a name="6507"
      > </a
      ><a name="6508" class="Symbol"
      >&#8704;</a
      ><a name="6509"
      > </a
      ><a name="6510" class="Symbol"
      >{</a
      ><a name="6511" href="Maps.html#6511" class="Bound"
      >A</a
      ><a name="6512" class="Symbol"
      >}</a
      ><a name="6513"
      > </a
      ><a name="6514" class="Symbol"
      >(</a
      ><a name="6515" href="Maps.html#6515" class="Bound"
      >&#961;</a
      ><a name="6516"
      > </a
      ><a name="6517" class="Symbol"
      >:</a
      ><a name="6518"
      > </a
      ><a name="6519" href="Maps.html#3738" class="Function"
      >TotalMap</a
      ><a name="6527"
      > </a
      ><a name="6528" href="Maps.html#6511" class="Bound"
      >A</a
      ><a name="6529" class="Symbol"
      >)</a
      ><a name="6530"
      > </a
      ><a name="6531" class="Symbol"
      >(</a
      ><a name="6532" href="Maps.html#6532" class="Bound"
      >x</a
      ><a name="6533"
      > </a
      ><a name="6534" class="Symbol"
      >:</a
      ><a name="6535"
      > </a
      ><a name="6536" href="Maps.html#2215" class="Datatype"
      >Id</a
      ><a name="6538" class="Symbol"
      >)</a
      ><a name="6539"
      > </a
      ><a name="6540" class="Symbol"
      >(</a
      ><a name="6541" href="Maps.html#6541" class="Bound"
      >v</a
      ><a name="6542"
      > </a
      ><a name="6543" class="Symbol"
      >:</a
      ><a name="6544"
      > </a
      ><a name="6545" href="Maps.html#6511" class="Bound"
      >A</a
      ><a name="6546" class="Symbol"
      >)</a
      ><a name="6547"
      > </a
      ><a name="6548" class="Symbol"
      >(</a
      ><a name="6549" href="Maps.html#6549" class="Bound"
      >y</a
      ><a name="6550"
      > </a
      ><a name="6551" class="Symbol"
      >:</a
      ><a name="6552"
      > </a
      ><a name="6553" href="Maps.html#2215" class="Datatype"
      >Id</a
      ><a name="6555" class="Symbol"
      >)</a
      ><a name="6556"
      >
             </a
      ><a name="6570" class="Symbol"
      >&#8594;</a
      ><a name="6571"
      > </a
      ><a name="6572" href="Maps.html#6532" class="Bound"
      >x</a
      ><a name="6573"
      > </a
      ><a name="6574" href="https://agda.github.io/agda-stdlib/Relation.Binary.Core.html#4493" class="Function Operator"
      >&#8802;</a
      ><a name="6575"
      > </a
      ><a name="6576" href="Maps.html#6549" class="Bound"
      >y</a
      ><a name="6577"
      > </a
      ><a name="6578" class="Symbol"
      >&#8594;</a
      ><a name="6579"
      > </a
      ><a name="6580" class="Symbol"
      >(</a
      ><a name="6581" href="Maps.html#6515" class="Bound"
      >&#961;</a
      ><a name="6582"
      > </a
      ><a name="6583" href="Maps.html#4403" class="Function Operator"
      >,</a
      ><a name="6584"
      > </a
      ><a name="6585" href="Maps.html#6532" class="Bound"
      >x</a
      ><a name="6586"
      > </a
      ><a name="6587" href="Maps.html#4403" class="Function Operator"
      >&#8614;</a
      ><a name="6588"
      > </a
      ><a name="6589" href="Maps.html#6541" class="Bound"
      >v</a
      ><a name="6590" class="Symbol"
      >)</a
      ><a name="6591"
      > </a
      ><a name="6592" href="Maps.html#6549" class="Bound"
      >y</a
      ><a name="6593"
      > </a
      ><a name="6594" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="6595"
      > </a
      ><a name="6596" href="Maps.html#6515" class="Bound"
      >&#961;</a
      ><a name="6597"
      > </a
      ><a name="6598" href="Maps.html#6549" class="Bound"
      >y</a
      ><a name="6599"
      >
  </a
      ><a name="6602" href="Maps.html#6495" class="Function"
      >update-neq</a
      ><a name="6612"
      > </a
      ><a name="6613" href="Maps.html#6613" class="Bound"
      >&#961;</a
      ><a name="6614"
      > </a
      ><a name="6615" href="Maps.html#6615" class="Bound"
      >x</a
      ><a name="6616"
      > </a
      ><a name="6617" href="Maps.html#6617" class="Bound"
      >v</a
      ><a name="6618"
      > </a
      ><a name="6619" href="Maps.html#6619" class="Bound"
      >y</a
      ><a name="6620"
      > </a
      ><a name="6621" href="Maps.html#6621" class="Bound"
      >x&#8802;y</a
      ><a name="6624"
      > </a
      ><a name="6625" class="Keyword"
      >with</a
      ><a name="6629"
      > </a
      ><a name="6630" href="Maps.html#6615" class="Bound"
      >x</a
      ><a name="6631"
      > </a
      ><a name="6632" href="Maps.html#2558" class="Function Operator"
      >&#8799;</a
      ><a name="6633"
      > </a
      ><a name="6634" href="Maps.html#6619" class="Bound"
      >y</a
      ><a name="6635"
      >
  </a
      ><a name="6638" class="Symbol"
      >...</a
      ><a name="6641"
      > </a
      ><a name="6642" class="Symbol"
      >|</a
      ><a name="6643"
      > </a
      ><a name="6644" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#520" class="InductiveConstructor"
      >yes</a
      ><a name="6647"
      > </a
      ><a name="6648" href="Maps.html#6648" class="Bound"
      >x&#8801;y</a
      ><a name="6651"
      > </a
      ><a name="6652" class="Symbol"
      >=</a
      ><a name="6653"
      > </a
      ><a name="6654" href="https://agda.github.io/agda-stdlib/Data.Empty.html#360" class="Function"
      >&#8869;-elim</a
      ><a name="6660"
      > </a
      ><a name="6661" class="Symbol"
      >(</a
      ><a name="6662" href="Maps.html#6621" class="Bound"
      >x&#8802;y</a
      ><a name="6665"
      > </a
      ><a name="6666" href="Maps.html#6648" class="Bound"
      >x&#8801;y</a
      ><a name="6669" class="Symbol"
      >)</a
      ><a name="6670"
      >
  </a
      ><a name="6673" class="Symbol"
      >...</a
      ><a name="6676"
      > </a
      ><a name="6677" class="Symbol"
      >|</a
      ><a name="6678"
      > </a
      ><a name="6679" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#547" class="InductiveConstructor"
      >no</a
      ><a name="6681"
      >  </a
      ><a name="6683" class="Symbol"
      >_</a
      ><a name="6684"
      >   </a
      ><a name="6687" class="Symbol"
      >=</a
      ><a name="6688"
      > </a
      ><a name="6689" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      >

</pre>

For the following lemmas, since maps are represented by functions, to
show two maps equal we will need to postulate extensionality.

<pre class="Agda">

  <a name="6854" class="Keyword"
      >postulate</a
      ><a name="6863"
      >
    </a
      ><a name="6868" href="Maps.html#6868" class="Postulate"
      >extensionality</a
      ><a name="6882"
      > </a
      ><a name="6883" class="Symbol"
      >:</a
      ><a name="6884"
      > </a
      ><a name="6885" class="Symbol"
      >&#8704;</a
      ><a name="6886"
      > </a
      ><a name="6887" class="Symbol"
      >{</a
      ><a name="6888" href="Maps.html#6888" class="Bound"
      >A</a
      ><a name="6889"
      > </a
      ><a name="6890" class="Symbol"
      >:</a
      ><a name="6891"
      > </a
      ><a name="6892" class="PrimitiveType"
      >Set</a
      ><a name="6895" class="Symbol"
      >}</a
      ><a name="6896"
      > </a
      ><a name="6897" class="Symbol"
      >{</a
      ><a name="6898" href="Maps.html#6898" class="Bound"
      >&#961;</a
      ><a name="6899"
      > </a
      ><a name="6900" href="Maps.html#6900" class="Bound"
      >&#961;&#8242;</a
      ><a name="6902"
      > </a
      ><a name="6903" class="Symbol"
      >:</a
      ><a name="6904"
      > </a
      ><a name="6905" href="Maps.html#3738" class="Function"
      >TotalMap</a
      ><a name="6913"
      > </a
      ><a name="6914" href="Maps.html#6888" class="Bound"
      >A</a
      ><a name="6915" class="Symbol"
      >}</a
      ><a name="6916"
      > </a
      ><a name="6917" class="Symbol"
      >&#8594;</a
      ><a name="6918"
      > </a
      ><a name="6919" class="Symbol"
      >(&#8704;</a
      ><a name="6921"
      > </a
      ><a name="6922" href="Maps.html#6922" class="Bound"
      >x</a
      ><a name="6923"
      > </a
      ><a name="6924" class="Symbol"
      >&#8594;</a
      ><a name="6925"
      > </a
      ><a name="6926" href="Maps.html#6898" class="Bound"
      >&#961;</a
      ><a name="6927"
      > </a
      ><a name="6928" href="Maps.html#6922" class="Bound"
      >x</a
      ><a name="6929"
      > </a
      ><a name="6930" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="6931"
      > </a
      ><a name="6932" href="Maps.html#6900" class="Bound"
      >&#961;&#8242;</a
      ><a name="6934"
      > </a
      ><a name="6935" href="Maps.html#6922" class="Bound"
      >x</a
      ><a name="6936" class="Symbol"
      >)</a
      ><a name="6937"
      > </a
      ><a name="6938" class="Symbol"
      >&#8594;</a
      ><a name="6939"
      > </a
      ><a name="6940" href="Maps.html#6898" class="Bound"
      >&#961;</a
      ><a name="6941"
      > </a
      ><a name="6942" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="6943"
      > </a
      ><a name="6944" href="Maps.html#6900" class="Bound"
      >&#961;&#8242;</a
      >

</pre>

#### Exercise: 2 stars, optional (update-shadow)
If we update a map `ρ` at a key `x` with a value `v` and then
update again with the same key `x` and another value `w`, the
resulting map behaves the same (gives the same result when applied
to any key) as the simpler map obtained by performing just
the second update on `ρ`:

<pre class="Agda">

  <a name="7300" class="Keyword"
      >postulate</a
      ><a name="7309"
      >
    </a
      ><a name="7314" href="Maps.html#7314" class="Postulate"
      >update-shadow</a
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
      ><a name="7332" class="Symbol"
      >{</a
      ><a name="7333" href="Maps.html#7333" class="Bound"
      >A</a
      ><a name="7334" class="Symbol"
      >}</a
      ><a name="7335"
      > </a
      ><a name="7336" class="Symbol"
      >(</a
      ><a name="7337" href="Maps.html#7337" class="Bound"
      >&#961;</a
      ><a name="7338"
      > </a
      ><a name="7339" class="Symbol"
      >:</a
      ><a name="7340"
      > </a
      ><a name="7341" href="Maps.html#3738" class="Function"
      >TotalMap</a
      ><a name="7349"
      > </a
      ><a name="7350" href="Maps.html#7333" class="Bound"
      >A</a
      ><a name="7351" class="Symbol"
      >)</a
      ><a name="7352"
      > </a
      ><a name="7353" class="Symbol"
      >(</a
      ><a name="7354" href="Maps.html#7354" class="Bound"
      >x</a
      ><a name="7355"
      > </a
      ><a name="7356" class="Symbol"
      >:</a
      ><a name="7357"
      > </a
      ><a name="7358" href="Maps.html#2215" class="Datatype"
      >Id</a
      ><a name="7360" class="Symbol"
      >)</a
      ><a name="7361"
      > </a
      ><a name="7362" class="Symbol"
      >(</a
      ><a name="7363" href="Maps.html#7363" class="Bound"
      >v</a
      ><a name="7364"
      > </a
      ><a name="7365" href="Maps.html#7365" class="Bound"
      >w</a
      ><a name="7366"
      > </a
      ><a name="7367" class="Symbol"
      >:</a
      ><a name="7368"
      > </a
      ><a name="7369" href="Maps.html#7333" class="Bound"
      >A</a
      ><a name="7370" class="Symbol"
      >)</a
      ><a name="7371"
      > 
                  </a
      ><a name="7391" class="Symbol"
      >&#8594;</a
      ><a name="7392"
      > </a
      ><a name="7393" class="Symbol"
      >(</a
      ><a name="7394" href="Maps.html#7337" class="Bound"
      >&#961;</a
      ><a name="7395"
      > </a
      ><a name="7396" href="Maps.html#4403" class="Function Operator"
      >,</a
      ><a name="7397"
      > </a
      ><a name="7398" href="Maps.html#7354" class="Bound"
      >x</a
      ><a name="7399"
      > </a
      ><a name="7400" href="Maps.html#4403" class="Function Operator"
      >&#8614;</a
      ><a name="7401"
      > </a
      ><a name="7402" href="Maps.html#7363" class="Bound"
      >v</a
      ><a name="7403"
      > </a
      ><a name="7404" href="Maps.html#4403" class="Function Operator"
      >,</a
      ><a name="7405"
      > </a
      ><a name="7406" href="Maps.html#7354" class="Bound"
      >x</a
      ><a name="7407"
      > </a
      ><a name="7408" href="Maps.html#4403" class="Function Operator"
      >&#8614;</a
      ><a name="7409"
      > </a
      ><a name="7410" href="Maps.html#7365" class="Bound"
      >w</a
      ><a name="7411" class="Symbol"
      >)</a
      ><a name="7412"
      > </a
      ><a name="7413" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="7414"
      > </a
      ><a name="7415" class="Symbol"
      >(</a
      ><a name="7416" href="Maps.html#7337" class="Bound"
      >&#961;</a
      ><a name="7417"
      > </a
      ><a name="7418" href="Maps.html#4403" class="Function Operator"
      >,</a
      ><a name="7419"
      > </a
      ><a name="7420" href="Maps.html#7354" class="Bound"
      >x</a
      ><a name="7421"
      > </a
      ><a name="7422" href="Maps.html#4403" class="Function Operator"
      >&#8614;</a
      ><a name="7423"
      > </a
      ><a name="7424" href="Maps.html#7365" class="Bound"
      >w</a
      ><a name="7425" class="Symbol"
      >)</a
      >

</pre>

<div class="hidden">
<pre class="Agda">

  <a name="7475" href="Maps.html#7475" class="Function"
      >update-shadow&#8242;</a
      ><a name="7489"
      > </a
      ><a name="7490" class="Symbol"
      >:</a
      ><a name="7491"
      >  </a
      ><a name="7493" class="Symbol"
      >&#8704;</a
      ><a name="7494"
      > </a
      ><a name="7495" class="Symbol"
      >{</a
      ><a name="7496" href="Maps.html#7496" class="Bound"
      >A</a
      ><a name="7497" class="Symbol"
      >}</a
      ><a name="7498"
      > </a
      ><a name="7499" class="Symbol"
      >(</a
      ><a name="7500" href="Maps.html#7500" class="Bound"
      >&#961;</a
      ><a name="7501"
      > </a
      ><a name="7502" class="Symbol"
      >:</a
      ><a name="7503"
      > </a
      ><a name="7504" href="Maps.html#3738" class="Function"
      >TotalMap</a
      ><a name="7512"
      > </a
      ><a name="7513" href="Maps.html#7496" class="Bound"
      >A</a
      ><a name="7514" class="Symbol"
      >)</a
      ><a name="7515"
      > </a
      ><a name="7516" class="Symbol"
      >(</a
      ><a name="7517" href="Maps.html#7517" class="Bound"
      >x</a
      ><a name="7518"
      > </a
      ><a name="7519" class="Symbol"
      >:</a
      ><a name="7520"
      > </a
      ><a name="7521" href="Maps.html#2215" class="Datatype"
      >Id</a
      ><a name="7523" class="Symbol"
      >)</a
      ><a name="7524"
      > </a
      ><a name="7525" class="Symbol"
      >(</a
      ><a name="7526" href="Maps.html#7526" class="Bound"
      >v</a
      ><a name="7527"
      > </a
      ><a name="7528" href="Maps.html#7528" class="Bound"
      >w</a
      ><a name="7529"
      > </a
      ><a name="7530" class="Symbol"
      >:</a
      ><a name="7531"
      > </a
      ><a name="7532" href="Maps.html#7496" class="Bound"
      >A</a
      ><a name="7533" class="Symbol"
      >)</a
      ><a name="7534"
      > 
                  </a
      ><a name="7554" class="Symbol"
      >&#8594;</a
      ><a name="7555"
      > </a
      ><a name="7556" class="Symbol"
      >((</a
      ><a name="7558" href="Maps.html#7500" class="Bound"
      >&#961;</a
      ><a name="7559"
      > </a
      ><a name="7560" href="Maps.html#4403" class="Function Operator"
      >,</a
      ><a name="7561"
      > </a
      ><a name="7562" href="Maps.html#7517" class="Bound"
      >x</a
      ><a name="7563"
      > </a
      ><a name="7564" href="Maps.html#4403" class="Function Operator"
      >&#8614;</a
      ><a name="7565"
      > </a
      ><a name="7566" href="Maps.html#7526" class="Bound"
      >v</a
      ><a name="7567" class="Symbol"
      >)</a
      ><a name="7568"
      > </a
      ><a name="7569" href="Maps.html#4403" class="Function Operator"
      >,</a
      ><a name="7570"
      > </a
      ><a name="7571" href="Maps.html#7517" class="Bound"
      >x</a
      ><a name="7572"
      > </a
      ><a name="7573" href="Maps.html#4403" class="Function Operator"
      >&#8614;</a
      ><a name="7574"
      > </a
      ><a name="7575" href="Maps.html#7528" class="Bound"
      >w</a
      ><a name="7576" class="Symbol"
      >)</a
      ><a name="7577"
      > </a
      ><a name="7578" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="7579"
      > </a
      ><a name="7580" class="Symbol"
      >(</a
      ><a name="7581" href="Maps.html#7500" class="Bound"
      >&#961;</a
      ><a name="7582"
      > </a
      ><a name="7583" href="Maps.html#4403" class="Function Operator"
      >,</a
      ><a name="7584"
      > </a
      ><a name="7585" href="Maps.html#7517" class="Bound"
      >x</a
      ><a name="7586"
      > </a
      ><a name="7587" href="Maps.html#4403" class="Function Operator"
      >&#8614;</a
      ><a name="7588"
      > </a
      ><a name="7589" href="Maps.html#7528" class="Bound"
      >w</a
      ><a name="7590" class="Symbol"
      >)</a
      ><a name="7591"
      >
  </a
      ><a name="7594" href="Maps.html#7475" class="Function"
      >update-shadow&#8242;</a
      ><a name="7608"
      > </a
      ><a name="7609" href="Maps.html#7609" class="Bound"
      >&#961;</a
      ><a name="7610"
      > </a
      ><a name="7611" href="Maps.html#7611" class="Bound"
      >x</a
      ><a name="7612"
      > </a
      ><a name="7613" href="Maps.html#7613" class="Bound"
      >v</a
      ><a name="7614"
      > </a
      ><a name="7615" href="Maps.html#7615" class="Bound"
      >w</a
      ><a name="7616"
      > </a
      ><a name="7617" class="Symbol"
      >=</a
      ><a name="7618"
      > </a
      ><a name="7619" href="Maps.html#6868" class="Postulate"
      >extensionality</a
      ><a name="7633"
      > </a
      ><a name="7634" href="Maps.html#7654" class="Function"
      >lemma</a
      ><a name="7639"
      >
    </a
      ><a name="7644" class="Keyword"
      >where</a
      ><a name="7649"
      >
    </a
      ><a name="7654" href="Maps.html#7654" class="Function"
      >lemma</a
      ><a name="7659"
      > </a
      ><a name="7660" class="Symbol"
      >:</a
      ><a name="7661"
      > </a
      ><a name="7662" class="Symbol"
      >&#8704;</a
      ><a name="7663"
      > </a
      ><a name="7664" href="Maps.html#7664" class="Bound"
      >y</a
      ><a name="7665"
      > </a
      ><a name="7666" class="Symbol"
      >&#8594;</a
      ><a name="7667"
      > </a
      ><a name="7668" class="Symbol"
      >((</a
      ><a name="7670" href="Maps.html#7609" class="Bound"
      >&#961;</a
      ><a name="7671"
      > </a
      ><a name="7672" href="Maps.html#4403" class="Function Operator"
      >,</a
      ><a name="7673"
      > </a
      ><a name="7674" href="Maps.html#7611" class="Bound"
      >x</a
      ><a name="7675"
      > </a
      ><a name="7676" href="Maps.html#4403" class="Function Operator"
      >&#8614;</a
      ><a name="7677"
      > </a
      ><a name="7678" href="Maps.html#7613" class="Bound"
      >v</a
      ><a name="7679" class="Symbol"
      >)</a
      ><a name="7680"
      > </a
      ><a name="7681" href="Maps.html#4403" class="Function Operator"
      >,</a
      ><a name="7682"
      > </a
      ><a name="7683" href="Maps.html#7611" class="Bound"
      >x</a
      ><a name="7684"
      > </a
      ><a name="7685" href="Maps.html#4403" class="Function Operator"
      >&#8614;</a
      ><a name="7686"
      > </a
      ><a name="7687" href="Maps.html#7615" class="Bound"
      >w</a
      ><a name="7688" class="Symbol"
      >)</a
      ><a name="7689"
      > </a
      ><a name="7690" href="Maps.html#7664" class="Bound"
      >y</a
      ><a name="7691"
      > </a
      ><a name="7692" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="7693"
      > </a
      ><a name="7694" class="Symbol"
      >(</a
      ><a name="7695" href="Maps.html#7609" class="Bound"
      >&#961;</a
      ><a name="7696"
      > </a
      ><a name="7697" href="Maps.html#4403" class="Function Operator"
      >,</a
      ><a name="7698"
      > </a
      ><a name="7699" href="Maps.html#7611" class="Bound"
      >x</a
      ><a name="7700"
      > </a
      ><a name="7701" href="Maps.html#4403" class="Function Operator"
      >&#8614;</a
      ><a name="7702"
      > </a
      ><a name="7703" href="Maps.html#7615" class="Bound"
      >w</a
      ><a name="7704" class="Symbol"
      >)</a
      ><a name="7705"
      > </a
      ><a name="7706" href="Maps.html#7664" class="Bound"
      >y</a
      ><a name="7707"
      >
    </a
      ><a name="7712" href="Maps.html#7654" class="Function"
      >lemma</a
      ><a name="7717"
      > </a
      ><a name="7718" href="Maps.html#7718" class="Bound"
      >y</a
      ><a name="7719"
      > </a
      ><a name="7720" class="Keyword"
      >with</a
      ><a name="7724"
      > </a
      ><a name="7725" href="Maps.html#7611" class="Bound"
      >x</a
      ><a name="7726"
      > </a
      ><a name="7727" href="Maps.html#2558" class="Function Operator"
      >&#8799;</a
      ><a name="7728"
      > </a
      ><a name="7729" href="Maps.html#7718" class="Bound"
      >y</a
      ><a name="7730"
      >
    </a
      ><a name="7735" class="Symbol"
      >...</a
      ><a name="7738"
      > </a
      ><a name="7739" class="Symbol"
      >|</a
      ><a name="7740"
      > </a
      ><a name="7741" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#520" class="InductiveConstructor"
      >yes</a
      ><a name="7744"
      > </a
      ><a name="7745" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="7749"
      > </a
      ><a name="7750" class="Symbol"
      >=</a
      ><a name="7751"
      > </a
      ><a name="7752" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="7756"
      >
    </a
      ><a name="7761" class="Symbol"
      >...</a
      ><a name="7764"
      > </a
      ><a name="7765" class="Symbol"
      >|</a
      ><a name="7766"
      > </a
      ><a name="7767" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#547" class="InductiveConstructor"
      >no</a
      ><a name="7769"
      >  </a
      ><a name="7771" href="Maps.html#7771" class="Bound"
      >x&#8802;y</a
      ><a name="7774"
      >  </a
      ><a name="7776" class="Symbol"
      >=</a
      ><a name="7777"
      > </a
      ><a name="7778" href="Maps.html#6495" class="Function"
      >update-neq</a
      ><a name="7788"
      > </a
      ><a name="7789" href="Maps.html#7609" class="Bound"
      >&#961;</a
      ><a name="7790"
      > </a
      ><a name="7791" href="Maps.html#7611" class="Bound"
      >x</a
      ><a name="7792"
      > </a
      ><a name="7793" href="Maps.html#7613" class="Bound"
      >v</a
      ><a name="7794"
      > </a
      ><a name="7795" href="Maps.html#7718" class="Bound"
      >y</a
      ><a name="7796"
      > </a
      ><a name="7797" href="Maps.html#7771" class="Bound"
      >x&#8802;y</a
      >

</pre>
</div>

#### Exercise: 2 stars (update-same)
Prove the following theorem, which states that if we update a map `ρ` to
assign key `x` the same value as it already has in `ρ`, then the
result is equal to `ρ`:

<pre class="Agda">

  <a name="8035" class="Keyword"
      >postulate</a
      ><a name="8044"
      >
    </a
      ><a name="8049" href="Maps.html#8049" class="Postulate"
      >update-same</a
      ><a name="8060"
      > </a
      ><a name="8061" class="Symbol"
      >:</a
      ><a name="8062"
      > </a
      ><a name="8063" class="Symbol"
      >&#8704;</a
      ><a name="8064"
      > </a
      ><a name="8065" class="Symbol"
      >{</a
      ><a name="8066" href="Maps.html#8066" class="Bound"
      >A</a
      ><a name="8067" class="Symbol"
      >}</a
      ><a name="8068"
      > </a
      ><a name="8069" class="Symbol"
      >(</a
      ><a name="8070" href="Maps.html#8070" class="Bound"
      >&#961;</a
      ><a name="8071"
      > </a
      ><a name="8072" class="Symbol"
      >:</a
      ><a name="8073"
      > </a
      ><a name="8074" href="Maps.html#3738" class="Function"
      >TotalMap</a
      ><a name="8082"
      > </a
      ><a name="8083" href="Maps.html#8066" class="Bound"
      >A</a
      ><a name="8084" class="Symbol"
      >)</a
      ><a name="8085"
      > </a
      ><a name="8086" class="Symbol"
      >(</a
      ><a name="8087" href="Maps.html#8087" class="Bound"
      >x</a
      ><a name="8088"
      > </a
      ><a name="8089" class="Symbol"
      >:</a
      ><a name="8090"
      > </a
      ><a name="8091" href="Maps.html#2215" class="Datatype"
      >Id</a
      ><a name="8093" class="Symbol"
      >)</a
      ><a name="8094"
      > </a
      ><a name="8095" class="Symbol"
      >&#8594;</a
      ><a name="8096"
      > </a
      ><a name="8097" class="Symbol"
      >(</a
      ><a name="8098" href="Maps.html#8070" class="Bound"
      >&#961;</a
      ><a name="8099"
      > </a
      ><a name="8100" href="Maps.html#4403" class="Function Operator"
      >,</a
      ><a name="8101"
      > </a
      ><a name="8102" href="Maps.html#8087" class="Bound"
      >x</a
      ><a name="8103"
      > </a
      ><a name="8104" href="Maps.html#4403" class="Function Operator"
      >&#8614;</a
      ><a name="8105"
      > </a
      ><a name="8106" href="Maps.html#8070" class="Bound"
      >&#961;</a
      ><a name="8107"
      > </a
      ><a name="8108" href="Maps.html#8087" class="Bound"
      >x</a
      ><a name="8109" class="Symbol"
      >)</a
      ><a name="8110"
      > </a
      ><a name="8111" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="8112"
      > </a
      ><a name="8113" href="Maps.html#8070" class="Bound"
      >&#961;</a
      >

</pre>

<div class="hidden">
<pre class="Agda">

  <a name="8163" href="Maps.html#8163" class="Function"
      >update-same&#8242;</a
      ><a name="8175"
      > </a
      ><a name="8176" class="Symbol"
      >:</a
      ><a name="8177"
      > </a
      ><a name="8178" class="Symbol"
      >&#8704;</a
      ><a name="8179"
      > </a
      ><a name="8180" class="Symbol"
      >{</a
      ><a name="8181" href="Maps.html#8181" class="Bound"
      >A</a
      ><a name="8182" class="Symbol"
      >}</a
      ><a name="8183"
      > </a
      ><a name="8184" class="Symbol"
      >(</a
      ><a name="8185" href="Maps.html#8185" class="Bound"
      >&#961;</a
      ><a name="8186"
      > </a
      ><a name="8187" class="Symbol"
      >:</a
      ><a name="8188"
      > </a
      ><a name="8189" href="Maps.html#3738" class="Function"
      >TotalMap</a
      ><a name="8197"
      > </a
      ><a name="8198" href="Maps.html#8181" class="Bound"
      >A</a
      ><a name="8199" class="Symbol"
      >)</a
      ><a name="8200"
      > </a
      ><a name="8201" class="Symbol"
      >(</a
      ><a name="8202" href="Maps.html#8202" class="Bound"
      >x</a
      ><a name="8203"
      > </a
      ><a name="8204" class="Symbol"
      >:</a
      ><a name="8205"
      > </a
      ><a name="8206" href="Maps.html#2215" class="Datatype"
      >Id</a
      ><a name="8208" class="Symbol"
      >)</a
      ><a name="8209"
      > </a
      ><a name="8210" class="Symbol"
      >&#8594;</a
      ><a name="8211"
      > </a
      ><a name="8212" class="Symbol"
      >(</a
      ><a name="8213" href="Maps.html#8185" class="Bound"
      >&#961;</a
      ><a name="8214"
      > </a
      ><a name="8215" href="Maps.html#4403" class="Function Operator"
      >,</a
      ><a name="8216"
      > </a
      ><a name="8217" href="Maps.html#8202" class="Bound"
      >x</a
      ><a name="8218"
      > </a
      ><a name="8219" href="Maps.html#4403" class="Function Operator"
      >&#8614;</a
      ><a name="8220"
      > </a
      ><a name="8221" href="Maps.html#8185" class="Bound"
      >&#961;</a
      ><a name="8222"
      > </a
      ><a name="8223" href="Maps.html#8202" class="Bound"
      >x</a
      ><a name="8224" class="Symbol"
      >)</a
      ><a name="8225"
      > </a
      ><a name="8226" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="8227"
      > </a
      ><a name="8228" href="Maps.html#8185" class="Bound"
      >&#961;</a
      ><a name="8229"
      >
  </a
      ><a name="8232" href="Maps.html#8163" class="Function"
      >update-same&#8242;</a
      ><a name="8244"
      > </a
      ><a name="8245" href="Maps.html#8245" class="Bound"
      >&#961;</a
      ><a name="8246"
      > </a
      ><a name="8247" href="Maps.html#8247" class="Bound"
      >x</a
      ><a name="8248"
      >  </a
      ><a name="8250" class="Symbol"
      >=</a
      ><a name="8251"
      >  </a
      ><a name="8253" href="Maps.html#6868" class="Postulate"
      >extensionality</a
      ><a name="8267"
      > </a
      ><a name="8268" href="Maps.html#8288" class="Function"
      >lemma</a
      ><a name="8273"
      >
    </a
      ><a name="8278" class="Keyword"
      >where</a
      ><a name="8283"
      >
    </a
      ><a name="8288" href="Maps.html#8288" class="Function"
      >lemma</a
      ><a name="8293"
      > </a
      ><a name="8294" class="Symbol"
      >:</a
      ><a name="8295"
      > </a
      ><a name="8296" class="Symbol"
      >&#8704;</a
      ><a name="8297"
      > </a
      ><a name="8298" href="Maps.html#8298" class="Bound"
      >y</a
      ><a name="8299"
      > </a
      ><a name="8300" class="Symbol"
      >&#8594;</a
      ><a name="8301"
      > </a
      ><a name="8302" class="Symbol"
      >(</a
      ><a name="8303" href="Maps.html#8245" class="Bound"
      >&#961;</a
      ><a name="8304"
      > </a
      ><a name="8305" href="Maps.html#4403" class="Function Operator"
      >,</a
      ><a name="8306"
      > </a
      ><a name="8307" href="Maps.html#8247" class="Bound"
      >x</a
      ><a name="8308"
      > </a
      ><a name="8309" href="Maps.html#4403" class="Function Operator"
      >&#8614;</a
      ><a name="8310"
      > </a
      ><a name="8311" href="Maps.html#8245" class="Bound"
      >&#961;</a
      ><a name="8312"
      > </a
      ><a name="8313" href="Maps.html#8247" class="Bound"
      >x</a
      ><a name="8314" class="Symbol"
      >)</a
      ><a name="8315"
      > </a
      ><a name="8316" href="Maps.html#8298" class="Bound"
      >y</a
      ><a name="8317"
      > </a
      ><a name="8318" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="8319"
      > </a
      ><a name="8320" href="Maps.html#8245" class="Bound"
      >&#961;</a
      ><a name="8321"
      > </a
      ><a name="8322" href="Maps.html#8298" class="Bound"
      >y</a
      ><a name="8323"
      >
    </a
      ><a name="8328" href="Maps.html#8288" class="Function"
      >lemma</a
      ><a name="8333"
      > </a
      ><a name="8334" href="Maps.html#8334" class="Bound"
      >y</a
      ><a name="8335"
      > </a
      ><a name="8336" class="Keyword"
      >with</a
      ><a name="8340"
      > </a
      ><a name="8341" href="Maps.html#8247" class="Bound"
      >x</a
      ><a name="8342"
      > </a
      ><a name="8343" href="Maps.html#2558" class="Function Operator"
      >&#8799;</a
      ><a name="8344"
      > </a
      ><a name="8345" href="Maps.html#8334" class="Bound"
      >y</a
      ><a name="8346"
      >
    </a
      ><a name="8351" class="Symbol"
      >...</a
      ><a name="8354"
      > </a
      ><a name="8355" class="Symbol"
      >|</a
      ><a name="8356"
      > </a
      ><a name="8357" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#520" class="InductiveConstructor"
      >yes</a
      ><a name="8360"
      > </a
      ><a name="8361" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="8365"
      > </a
      ><a name="8366" class="Symbol"
      >=</a
      ><a name="8367"
      > </a
      ><a name="8368" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="8372"
      >
    </a
      ><a name="8377" class="Symbol"
      >...</a
      ><a name="8380"
      > </a
      ><a name="8381" class="Symbol"
      >|</a
      ><a name="8382"
      > </a
      ><a name="8383" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#547" class="InductiveConstructor"
      >no</a
      ><a name="8385"
      >  </a
      ><a name="8387" href="Maps.html#8387" class="Bound"
      >x&#8802;y</a
      ><a name="8390"
      >  </a
      ><a name="8392" class="Symbol"
      >=</a
      ><a name="8393"
      > </a
      ><a name="8394" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      >

</pre>
</div>

#### Exercise: 3 stars, recommended (update-permute)
Prove one final property of the `update` function: If we update a map
`m` at two distinct keys, it doesn't matter in which order we do the
updates.

<pre class="Agda">

  <a name="8635" class="Keyword"
      >postulate</a
      ><a name="8644"
      >
    </a
      ><a name="8649" href="Maps.html#8649" class="Postulate"
      >update-permute</a
      ><a name="8663"
      > </a
      ><a name="8664" class="Symbol"
      >:</a
      ><a name="8665"
      > </a
      ><a name="8666" class="Symbol"
      >&#8704;</a
      ><a name="8667"
      > </a
      ><a name="8668" class="Symbol"
      >{</a
      ><a name="8669" href="Maps.html#8669" class="Bound"
      >A</a
      ><a name="8670" class="Symbol"
      >}</a
      ><a name="8671"
      > </a
      ><a name="8672" class="Symbol"
      >(</a
      ><a name="8673" href="Maps.html#8673" class="Bound"
      >&#961;</a
      ><a name="8674"
      > </a
      ><a name="8675" class="Symbol"
      >:</a
      ><a name="8676"
      > </a
      ><a name="8677" href="Maps.html#3738" class="Function"
      >TotalMap</a
      ><a name="8685"
      > </a
      ><a name="8686" href="Maps.html#8669" class="Bound"
      >A</a
      ><a name="8687" class="Symbol"
      >)</a
      ><a name="8688"
      > </a
      ><a name="8689" class="Symbol"
      >(</a
      ><a name="8690" href="Maps.html#8690" class="Bound"
      >x</a
      ><a name="8691"
      > </a
      ><a name="8692" class="Symbol"
      >:</a
      ><a name="8693"
      > </a
      ><a name="8694" href="Maps.html#2215" class="Datatype"
      >Id</a
      ><a name="8696" class="Symbol"
      >)</a
      ><a name="8697"
      > </a
      ><a name="8698" class="Symbol"
      >(</a
      ><a name="8699" href="Maps.html#8699" class="Bound"
      >v</a
      ><a name="8700"
      > </a
      ><a name="8701" class="Symbol"
      >:</a
      ><a name="8702"
      > </a
      ><a name="8703" href="Maps.html#8669" class="Bound"
      >A</a
      ><a name="8704" class="Symbol"
      >)</a
      ><a name="8705"
      > </a
      ><a name="8706" class="Symbol"
      >(</a
      ><a name="8707" href="Maps.html#8707" class="Bound"
      >y</a
      ><a name="8708"
      > </a
      ><a name="8709" class="Symbol"
      >:</a
      ><a name="8710"
      > </a
      ><a name="8711" href="Maps.html#2215" class="Datatype"
      >Id</a
      ><a name="8713" class="Symbol"
      >)</a
      ><a name="8714"
      > </a
      ><a name="8715" class="Symbol"
      >(</a
      ><a name="8716" href="Maps.html#8716" class="Bound"
      >w</a
      ><a name="8717"
      > </a
      ><a name="8718" class="Symbol"
      >:</a
      ><a name="8719"
      > </a
      ><a name="8720" href="Maps.html#8669" class="Bound"
      >A</a
      ><a name="8721" class="Symbol"
      >)</a
      ><a name="8722"
      >
                   </a
      ><a name="8742" class="Symbol"
      >&#8594;</a
      ><a name="8743"
      > </a
      ><a name="8744" href="Maps.html#8690" class="Bound"
      >x</a
      ><a name="8745"
      > </a
      ><a name="8746" href="https://agda.github.io/agda-stdlib/Relation.Binary.Core.html#4493" class="Function Operator"
      >&#8802;</a
      ><a name="8747"
      > </a
      ><a name="8748" href="Maps.html#8707" class="Bound"
      >y</a
      ><a name="8749"
      > </a
      ><a name="8750" class="Symbol"
      >&#8594;</a
      ><a name="8751"
      > </a
      ><a name="8752" class="Symbol"
      >(</a
      ><a name="8753" href="Maps.html#8673" class="Bound"
      >&#961;</a
      ><a name="8754"
      > </a
      ><a name="8755" href="Maps.html#4403" class="Function Operator"
      >,</a
      ><a name="8756"
      > </a
      ><a name="8757" href="Maps.html#8690" class="Bound"
      >x</a
      ><a name="8758"
      > </a
      ><a name="8759" href="Maps.html#4403" class="Function Operator"
      >&#8614;</a
      ><a name="8760"
      > </a
      ><a name="8761" href="Maps.html#8699" class="Bound"
      >v</a
      ><a name="8762"
      > </a
      ><a name="8763" href="Maps.html#4403" class="Function Operator"
      >,</a
      ><a name="8764"
      > </a
      ><a name="8765" href="Maps.html#8707" class="Bound"
      >y</a
      ><a name="8766"
      > </a
      ><a name="8767" href="Maps.html#4403" class="Function Operator"
      >&#8614;</a
      ><a name="8768"
      > </a
      ><a name="8769" href="Maps.html#8716" class="Bound"
      >w</a
      ><a name="8770" class="Symbol"
      >)</a
      ><a name="8771"
      > </a
      ><a name="8772" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="8773"
      > </a
      ><a name="8774" class="Symbol"
      >(</a
      ><a name="8775" href="Maps.html#8673" class="Bound"
      >&#961;</a
      ><a name="8776"
      > </a
      ><a name="8777" href="Maps.html#4403" class="Function Operator"
      >,</a
      ><a name="8778"
      > </a
      ><a name="8779" href="Maps.html#8707" class="Bound"
      >y</a
      ><a name="8780"
      > </a
      ><a name="8781" href="Maps.html#4403" class="Function Operator"
      >&#8614;</a
      ><a name="8782"
      > </a
      ><a name="8783" href="Maps.html#8716" class="Bound"
      >w</a
      ><a name="8784"
      > </a
      ><a name="8785" href="Maps.html#4403" class="Function Operator"
      >,</a
      ><a name="8786"
      > </a
      ><a name="8787" href="Maps.html#8690" class="Bound"
      >x</a
      ><a name="8788"
      > </a
      ><a name="8789" href="Maps.html#4403" class="Function Operator"
      >&#8614;</a
      ><a name="8790"
      > </a
      ><a name="8791" href="Maps.html#8699" class="Bound"
      >v</a
      ><a name="8792" class="Symbol"
      >)</a
      >

</pre>

<div class="hidden">
<pre class="Agda">

  <a name="8842" href="Maps.html#8842" class="Function"
      >update-permute&#8242;</a
      ><a name="8857"
      > </a
      ><a name="8858" class="Symbol"
      >:</a
      ><a name="8859"
      > </a
      ><a name="8860" class="Symbol"
      >&#8704;</a
      ><a name="8861"
      > </a
      ><a name="8862" class="Symbol"
      >{</a
      ><a name="8863" href="Maps.html#8863" class="Bound"
      >A</a
      ><a name="8864" class="Symbol"
      >}</a
      ><a name="8865"
      > </a
      ><a name="8866" class="Symbol"
      >(</a
      ><a name="8867" href="Maps.html#8867" class="Bound"
      >&#961;</a
      ><a name="8868"
      > </a
      ><a name="8869" class="Symbol"
      >:</a
      ><a name="8870"
      > </a
      ><a name="8871" href="Maps.html#3738" class="Function"
      >TotalMap</a
      ><a name="8879"
      > </a
      ><a name="8880" href="Maps.html#8863" class="Bound"
      >A</a
      ><a name="8881" class="Symbol"
      >)</a
      ><a name="8882"
      > </a
      ><a name="8883" class="Symbol"
      >(</a
      ><a name="8884" href="Maps.html#8884" class="Bound"
      >x</a
      ><a name="8885"
      > </a
      ><a name="8886" class="Symbol"
      >:</a
      ><a name="8887"
      > </a
      ><a name="8888" href="Maps.html#2215" class="Datatype"
      >Id</a
      ><a name="8890" class="Symbol"
      >)</a
      ><a name="8891"
      > </a
      ><a name="8892" class="Symbol"
      >(</a
      ><a name="8893" href="Maps.html#8893" class="Bound"
      >v</a
      ><a name="8894"
      > </a
      ><a name="8895" class="Symbol"
      >:</a
      ><a name="8896"
      > </a
      ><a name="8897" href="Maps.html#8863" class="Bound"
      >A</a
      ><a name="8898" class="Symbol"
      >)</a
      ><a name="8899"
      > </a
      ><a name="8900" class="Symbol"
      >(</a
      ><a name="8901" href="Maps.html#8901" class="Bound"
      >y</a
      ><a name="8902"
      > </a
      ><a name="8903" class="Symbol"
      >:</a
      ><a name="8904"
      > </a
      ><a name="8905" href="Maps.html#2215" class="Datatype"
      >Id</a
      ><a name="8907" class="Symbol"
      >)</a
      ><a name="8908"
      > </a
      ><a name="8909" class="Symbol"
      >(</a
      ><a name="8910" href="Maps.html#8910" class="Bound"
      >w</a
      ><a name="8911"
      > </a
      ><a name="8912" class="Symbol"
      >:</a
      ><a name="8913"
      > </a
      ><a name="8914" href="Maps.html#8863" class="Bound"
      >A</a
      ><a name="8915" class="Symbol"
      >)</a
      ><a name="8916"
      >
                   </a
      ><a name="8936" class="Symbol"
      >&#8594;</a
      ><a name="8937"
      > </a
      ><a name="8938" href="Maps.html#8884" class="Bound"
      >x</a
      ><a name="8939"
      > </a
      ><a name="8940" href="https://agda.github.io/agda-stdlib/Relation.Binary.Core.html#4493" class="Function Operator"
      >&#8802;</a
      ><a name="8941"
      > </a
      ><a name="8942" href="Maps.html#8901" class="Bound"
      >y</a
      ><a name="8943"
      > </a
      ><a name="8944" class="Symbol"
      >&#8594;</a
      ><a name="8945"
      > </a
      ><a name="8946" class="Symbol"
      >(</a
      ><a name="8947" href="Maps.html#8867" class="Bound"
      >&#961;</a
      ><a name="8948"
      > </a
      ><a name="8949" href="Maps.html#4403" class="Function Operator"
      >,</a
      ><a name="8950"
      > </a
      ><a name="8951" href="Maps.html#8884" class="Bound"
      >x</a
      ><a name="8952"
      > </a
      ><a name="8953" href="Maps.html#4403" class="Function Operator"
      >&#8614;</a
      ><a name="8954"
      > </a
      ><a name="8955" href="Maps.html#8893" class="Bound"
      >v</a
      ><a name="8956"
      > </a
      ><a name="8957" href="Maps.html#4403" class="Function Operator"
      >,</a
      ><a name="8958"
      > </a
      ><a name="8959" href="Maps.html#8901" class="Bound"
      >y</a
      ><a name="8960"
      > </a
      ><a name="8961" href="Maps.html#4403" class="Function Operator"
      >&#8614;</a
      ><a name="8962"
      > </a
      ><a name="8963" href="Maps.html#8910" class="Bound"
      >w</a
      ><a name="8964" class="Symbol"
      >)</a
      ><a name="8965"
      > </a
      ><a name="8966" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="8967"
      > </a
      ><a name="8968" class="Symbol"
      >(</a
      ><a name="8969" href="Maps.html#8867" class="Bound"
      >&#961;</a
      ><a name="8970"
      > </a
      ><a name="8971" href="Maps.html#4403" class="Function Operator"
      >,</a
      ><a name="8972"
      > </a
      ><a name="8973" href="Maps.html#8901" class="Bound"
      >y</a
      ><a name="8974"
      > </a
      ><a name="8975" href="Maps.html#4403" class="Function Operator"
      >&#8614;</a
      ><a name="8976"
      > </a
      ><a name="8977" href="Maps.html#8910" class="Bound"
      >w</a
      ><a name="8978"
      > </a
      ><a name="8979" href="Maps.html#4403" class="Function Operator"
      >,</a
      ><a name="8980"
      > </a
      ><a name="8981" href="Maps.html#8884" class="Bound"
      >x</a
      ><a name="8982"
      > </a
      ><a name="8983" href="Maps.html#4403" class="Function Operator"
      >&#8614;</a
      ><a name="8984"
      > </a
      ><a name="8985" href="Maps.html#8893" class="Bound"
      >v</a
      ><a name="8986" class="Symbol"
      >)</a
      ><a name="8987"
      >
  </a
      ><a name="8990" href="Maps.html#8842" class="Function"
      >update-permute&#8242;</a
      ><a name="9005"
      > </a
      ><a name="9006" class="Symbol"
      >{</a
      ><a name="9007" href="Maps.html#9007" class="Bound"
      >A</a
      ><a name="9008" class="Symbol"
      >}</a
      ><a name="9009"
      > </a
      ><a name="9010" href="Maps.html#9010" class="Bound"
      >&#961;</a
      ><a name="9011"
      > </a
      ><a name="9012" href="Maps.html#9012" class="Bound"
      >x</a
      ><a name="9013"
      > </a
      ><a name="9014" href="Maps.html#9014" class="Bound"
      >v</a
      ><a name="9015"
      > </a
      ><a name="9016" href="Maps.html#9016" class="Bound"
      >y</a
      ><a name="9017"
      > </a
      ><a name="9018" href="Maps.html#9018" class="Bound"
      >w</a
      ><a name="9019"
      > </a
      ><a name="9020" href="Maps.html#9020" class="Bound"
      >x&#8802;y</a
      ><a name="9023"
      >  </a
      ><a name="9025" class="Symbol"
      >=</a
      ><a name="9026"
      >  </a
      ><a name="9028" href="Maps.html#6868" class="Postulate"
      >extensionality</a
      ><a name="9042"
      > </a
      ><a name="9043" href="Maps.html#9063" class="Function"
      >lemma</a
      ><a name="9048"
      >
    </a
      ><a name="9053" class="Keyword"
      >where</a
      ><a name="9058"
      >
    </a
      ><a name="9063" href="Maps.html#9063" class="Function"
      >lemma</a
      ><a name="9068"
      > </a
      ><a name="9069" class="Symbol"
      >:</a
      ><a name="9070"
      > </a
      ><a name="9071" class="Symbol"
      >&#8704;</a
      ><a name="9072"
      > </a
      ><a name="9073" href="Maps.html#9073" class="Bound"
      >z</a
      ><a name="9074"
      > </a
      ><a name="9075" class="Symbol"
      >&#8594;</a
      ><a name="9076"
      > </a
      ><a name="9077" class="Symbol"
      >(</a
      ><a name="9078" href="Maps.html#9010" class="Bound"
      >&#961;</a
      ><a name="9079"
      > </a
      ><a name="9080" href="Maps.html#4403" class="Function Operator"
      >,</a
      ><a name="9081"
      > </a
      ><a name="9082" href="Maps.html#9012" class="Bound"
      >x</a
      ><a name="9083"
      > </a
      ><a name="9084" href="Maps.html#4403" class="Function Operator"
      >&#8614;</a
      ><a name="9085"
      > </a
      ><a name="9086" href="Maps.html#9014" class="Bound"
      >v</a
      ><a name="9087"
      > </a
      ><a name="9088" href="Maps.html#4403" class="Function Operator"
      >,</a
      ><a name="9089"
      > </a
      ><a name="9090" href="Maps.html#9016" class="Bound"
      >y</a
      ><a name="9091"
      > </a
      ><a name="9092" href="Maps.html#4403" class="Function Operator"
      >&#8614;</a
      ><a name="9093"
      > </a
      ><a name="9094" href="Maps.html#9018" class="Bound"
      >w</a
      ><a name="9095" class="Symbol"
      >)</a
      ><a name="9096"
      > </a
      ><a name="9097" href="Maps.html#9073" class="Bound"
      >z</a
      ><a name="9098"
      > </a
      ><a name="9099" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="9100"
      > </a
      ><a name="9101" class="Symbol"
      >(</a
      ><a name="9102" href="Maps.html#9010" class="Bound"
      >&#961;</a
      ><a name="9103"
      > </a
      ><a name="9104" href="Maps.html#4403" class="Function Operator"
      >,</a
      ><a name="9105"
      > </a
      ><a name="9106" href="Maps.html#9016" class="Bound"
      >y</a
      ><a name="9107"
      > </a
      ><a name="9108" href="Maps.html#4403" class="Function Operator"
      >&#8614;</a
      ><a name="9109"
      > </a
      ><a name="9110" href="Maps.html#9018" class="Bound"
      >w</a
      ><a name="9111"
      > </a
      ><a name="9112" href="Maps.html#4403" class="Function Operator"
      >,</a
      ><a name="9113"
      > </a
      ><a name="9114" href="Maps.html#9012" class="Bound"
      >x</a
      ><a name="9115"
      > </a
      ><a name="9116" href="Maps.html#4403" class="Function Operator"
      >&#8614;</a
      ><a name="9117"
      > </a
      ><a name="9118" href="Maps.html#9014" class="Bound"
      >v</a
      ><a name="9119" class="Symbol"
      >)</a
      ><a name="9120"
      > </a
      ><a name="9121" href="Maps.html#9073" class="Bound"
      >z</a
      ><a name="9122"
      >
    </a
      ><a name="9127" href="Maps.html#9063" class="Function"
      >lemma</a
      ><a name="9132"
      > </a
      ><a name="9133" href="Maps.html#9133" class="Bound"
      >z</a
      ><a name="9134"
      > </a
      ><a name="9135" class="Keyword"
      >with</a
      ><a name="9139"
      > </a
      ><a name="9140" href="Maps.html#9012" class="Bound"
      >x</a
      ><a name="9141"
      > </a
      ><a name="9142" href="Maps.html#2558" class="Function Operator"
      >&#8799;</a
      ><a name="9143"
      > </a
      ><a name="9144" href="Maps.html#9133" class="Bound"
      >z</a
      ><a name="9145"
      > </a
      ><a name="9146" class="Symbol"
      >|</a
      ><a name="9147"
      > </a
      ><a name="9148" href="Maps.html#9016" class="Bound"
      >y</a
      ><a name="9149"
      > </a
      ><a name="9150" href="Maps.html#2558" class="Function Operator"
      >&#8799;</a
      ><a name="9151"
      > </a
      ><a name="9152" href="Maps.html#9133" class="Bound"
      >z</a
      ><a name="9153"
      >
    </a
      ><a name="9158" class="Symbol"
      >...</a
      ><a name="9161"
      > </a
      ><a name="9162" class="Symbol"
      >|</a
      ><a name="9163"
      > </a
      ><a name="9164" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#520" class="InductiveConstructor"
      >yes</a
      ><a name="9167"
      > </a
      ><a name="9168" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="9172"
      > </a
      ><a name="9173" class="Symbol"
      >|</a
      ><a name="9174"
      > </a
      ><a name="9175" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#520" class="InductiveConstructor"
      >yes</a
      ><a name="9178"
      > </a
      ><a name="9179" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="9183"
      >  </a
      ><a name="9185" class="Symbol"
      >=</a
      ><a name="9186"
      >  </a
      ><a name="9188" href="https://agda.github.io/agda-stdlib/Data.Empty.html#360" class="Function"
      >&#8869;-elim</a
      ><a name="9194"
      > </a
      ><a name="9195" class="Symbol"
      >(</a
      ><a name="9196" href="Maps.html#9020" class="Bound"
      >x&#8802;y</a
      ><a name="9199"
      > </a
      ><a name="9200" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="9204" class="Symbol"
      >)</a
      ><a name="9205"
      >
    </a
      ><a name="9210" class="Symbol"
      >...</a
      ><a name="9213"
      > </a
      ><a name="9214" class="Symbol"
      >|</a
      ><a name="9215"
      > </a
      ><a name="9216" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#547" class="InductiveConstructor"
      >no</a
      ><a name="9218"
      >  </a
      ><a name="9220" href="Maps.html#9220" class="Bound"
      >x&#8802;z</a
      ><a name="9223"
      >  </a
      ><a name="9225" class="Symbol"
      >|</a
      ><a name="9226"
      > </a
      ><a name="9227" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#520" class="InductiveConstructor"
      >yes</a
      ><a name="9230"
      > </a
      ><a name="9231" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="9235"
      >  </a
      ><a name="9237" class="Symbol"
      >=</a
      ><a name="9238"
      >  </a
      ><a name="9240" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.Core.html#565" class="Function"
      >sym</a
      ><a name="9243"
      > </a
      ><a name="9244" class="Symbol"
      >(</a
      ><a name="9245" href="Maps.html#6073" class="Function"
      >update-eq&#8242;</a
      ><a name="9255"
      > </a
      ><a name="9256" href="Maps.html#9010" class="Bound"
      >&#961;</a
      ><a name="9257"
      > </a
      ><a name="9258" href="Maps.html#9133" class="Bound"
      >z</a
      ><a name="9259"
      > </a
      ><a name="9260" href="Maps.html#9018" class="Bound"
      >w</a
      ><a name="9261" class="Symbol"
      >)</a
      ><a name="9262"
      >
    </a
      ><a name="9267" class="Symbol"
      >...</a
      ><a name="9270"
      > </a
      ><a name="9271" class="Symbol"
      >|</a
      ><a name="9272"
      > </a
      ><a name="9273" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#520" class="InductiveConstructor"
      >yes</a
      ><a name="9276"
      > </a
      ><a name="9277" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="9281"
      > </a
      ><a name="9282" class="Symbol"
      >|</a
      ><a name="9283"
      > </a
      ><a name="9284" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#547" class="InductiveConstructor"
      >no</a
      ><a name="9286"
      >  </a
      ><a name="9288" href="Maps.html#9288" class="Bound"
      >y&#8802;z</a
      ><a name="9291"
      >   </a
      ><a name="9294" class="Symbol"
      >=</a
      ><a name="9295"
      >  </a
      ><a name="9297" href="Maps.html#6073" class="Function"
      >update-eq&#8242;</a
      ><a name="9307"
      > </a
      ><a name="9308" href="Maps.html#9010" class="Bound"
      >&#961;</a
      ><a name="9309"
      > </a
      ><a name="9310" href="Maps.html#9133" class="Bound"
      >z</a
      ><a name="9311"
      > </a
      ><a name="9312" href="Maps.html#9014" class="Bound"
      >v</a
      ><a name="9313"
      >
    </a
      ><a name="9318" class="Symbol"
      >...</a
      ><a name="9321"
      > </a
      ><a name="9322" class="Symbol"
      >|</a
      ><a name="9323"
      > </a
      ><a name="9324" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#547" class="InductiveConstructor"
      >no</a
      ><a name="9326"
      >  </a
      ><a name="9328" href="Maps.html#9328" class="Bound"
      >x&#8802;z</a
      ><a name="9331"
      >  </a
      ><a name="9333" class="Symbol"
      >|</a
      ><a name="9334"
      > </a
      ><a name="9335" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#547" class="InductiveConstructor"
      >no</a
      ><a name="9337"
      >  </a
      ><a name="9339" href="Maps.html#9339" class="Bound"
      >y&#8802;z</a
      ><a name="9342"
      >   </a
      ><a name="9345" class="Symbol"
      >=</a
      ><a name="9346"
      >  </a
      ><a name="9348" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.Core.html#632" class="Function"
      >trans</a
      ><a name="9353"
      > </a
      ><a name="9354" class="Symbol"
      >(</a
      ><a name="9355" href="Maps.html#6495" class="Function"
      >update-neq</a
      ><a name="9365"
      > </a
      ><a name="9366" href="Maps.html#9010" class="Bound"
      >&#961;</a
      ><a name="9367"
      > </a
      ><a name="9368" href="Maps.html#9012" class="Bound"
      >x</a
      ><a name="9369"
      > </a
      ><a name="9370" href="Maps.html#9014" class="Bound"
      >v</a
      ><a name="9371"
      > </a
      ><a name="9372" href="Maps.html#9133" class="Bound"
      >z</a
      ><a name="9373"
      > </a
      ><a name="9374" href="Maps.html#9328" class="Bound"
      >x&#8802;z</a
      ><a name="9377" class="Symbol"
      >)</a
      ><a name="9378"
      > </a
      ><a name="9379" class="Symbol"
      >(</a
      ><a name="9380" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.Core.html#565" class="Function"
      >sym</a
      ><a name="9383"
      > </a
      ><a name="9384" class="Symbol"
      >(</a
      ><a name="9385" href="Maps.html#6495" class="Function"
      >update-neq</a
      ><a name="9395"
      > </a
      ><a name="9396" href="Maps.html#9010" class="Bound"
      >&#961;</a
      ><a name="9397"
      > </a
      ><a name="9398" href="Maps.html#9016" class="Bound"
      >y</a
      ><a name="9399"
      > </a
      ><a name="9400" href="Maps.html#9018" class="Bound"
      >w</a
      ><a name="9401"
      > </a
      ><a name="9402" href="Maps.html#9133" class="Bound"
      >z</a
      ><a name="9403"
      > </a
      ><a name="9404" href="Maps.html#9339" class="Bound"
      >y&#8802;z</a
      ><a name="9407" class="Symbol"
      >))</a
      >

</pre>

And a slightly different version of the same proof.

<pre class="Agda">

  <a name="9494" href="Maps.html#9494" class="Function"
      >update-permute&#8242;&#8242;</a
      ><a name="9510"
      > </a
      ><a name="9511" class="Symbol"
      >:</a
      ><a name="9512"
      > </a
      ><a name="9513" class="Symbol"
      >&#8704;</a
      ><a name="9514"
      > </a
      ><a name="9515" class="Symbol"
      >{</a
      ><a name="9516" href="Maps.html#9516" class="Bound"
      >A</a
      ><a name="9517" class="Symbol"
      >}</a
      ><a name="9518"
      > </a
      ><a name="9519" class="Symbol"
      >(</a
      ><a name="9520" href="Maps.html#9520" class="Bound"
      >&#961;</a
      ><a name="9521"
      > </a
      ><a name="9522" class="Symbol"
      >:</a
      ><a name="9523"
      > </a
      ><a name="9524" href="Maps.html#3738" class="Function"
      >TotalMap</a
      ><a name="9532"
      > </a
      ><a name="9533" href="Maps.html#9516" class="Bound"
      >A</a
      ><a name="9534" class="Symbol"
      >)</a
      ><a name="9535"
      > </a
      ><a name="9536" class="Symbol"
      >(</a
      ><a name="9537" href="Maps.html#9537" class="Bound"
      >x</a
      ><a name="9538"
      > </a
      ><a name="9539" class="Symbol"
      >:</a
      ><a name="9540"
      > </a
      ><a name="9541" href="Maps.html#2215" class="Datatype"
      >Id</a
      ><a name="9543" class="Symbol"
      >)</a
      ><a name="9544"
      > </a
      ><a name="9545" class="Symbol"
      >(</a
      ><a name="9546" href="Maps.html#9546" class="Bound"
      >v</a
      ><a name="9547"
      > </a
      ><a name="9548" class="Symbol"
      >:</a
      ><a name="9549"
      > </a
      ><a name="9550" href="Maps.html#9516" class="Bound"
      >A</a
      ><a name="9551" class="Symbol"
      >)</a
      ><a name="9552"
      > </a
      ><a name="9553" class="Symbol"
      >(</a
      ><a name="9554" href="Maps.html#9554" class="Bound"
      >y</a
      ><a name="9555"
      > </a
      ><a name="9556" class="Symbol"
      >:</a
      ><a name="9557"
      > </a
      ><a name="9558" href="Maps.html#2215" class="Datatype"
      >Id</a
      ><a name="9560" class="Symbol"
      >)</a
      ><a name="9561"
      > </a
      ><a name="9562" class="Symbol"
      >(</a
      ><a name="9563" href="Maps.html#9563" class="Bound"
      >w</a
      ><a name="9564"
      > </a
      ><a name="9565" class="Symbol"
      >:</a
      ><a name="9566"
      > </a
      ><a name="9567" href="Maps.html#9516" class="Bound"
      >A</a
      ><a name="9568" class="Symbol"
      >)</a
      ><a name="9569"
      > </a
      ><a name="9570" class="Symbol"
      >(</a
      ><a name="9571" href="Maps.html#9571" class="Bound"
      >z</a
      ><a name="9572"
      > </a
      ><a name="9573" class="Symbol"
      >:</a
      ><a name="9574"
      > </a
      ><a name="9575" href="Maps.html#2215" class="Datatype"
      >Id</a
      ><a name="9577" class="Symbol"
      >)</a
      ><a name="9578"
      >
                   </a
      ><a name="9598" class="Symbol"
      >&#8594;</a
      ><a name="9599"
      > </a
      ><a name="9600" href="Maps.html#9537" class="Bound"
      >x</a
      ><a name="9601"
      > </a
      ><a name="9602" href="https://agda.github.io/agda-stdlib/Relation.Binary.Core.html#4493" class="Function Operator"
      >&#8802;</a
      ><a name="9603"
      > </a
      ><a name="9604" href="Maps.html#9554" class="Bound"
      >y</a
      ><a name="9605"
      > </a
      ><a name="9606" class="Symbol"
      >&#8594;</a
      ><a name="9607"
      > </a
      ><a name="9608" class="Symbol"
      >(</a
      ><a name="9609" href="Maps.html#9520" class="Bound"
      >&#961;</a
      ><a name="9610"
      > </a
      ><a name="9611" href="Maps.html#4403" class="Function Operator"
      >,</a
      ><a name="9612"
      > </a
      ><a name="9613" href="Maps.html#9537" class="Bound"
      >x</a
      ><a name="9614"
      > </a
      ><a name="9615" href="Maps.html#4403" class="Function Operator"
      >&#8614;</a
      ><a name="9616"
      > </a
      ><a name="9617" href="Maps.html#9546" class="Bound"
      >v</a
      ><a name="9618"
      > </a
      ><a name="9619" href="Maps.html#4403" class="Function Operator"
      >,</a
      ><a name="9620"
      > </a
      ><a name="9621" href="Maps.html#9554" class="Bound"
      >y</a
      ><a name="9622"
      > </a
      ><a name="9623" href="Maps.html#4403" class="Function Operator"
      >&#8614;</a
      ><a name="9624"
      > </a
      ><a name="9625" href="Maps.html#9563" class="Bound"
      >w</a
      ><a name="9626" class="Symbol"
      >)</a
      ><a name="9627"
      > </a
      ><a name="9628" href="Maps.html#9571" class="Bound"
      >z</a
      ><a name="9629"
      > </a
      ><a name="9630" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="9631"
      > </a
      ><a name="9632" class="Symbol"
      >(</a
      ><a name="9633" href="Maps.html#9520" class="Bound"
      >&#961;</a
      ><a name="9634"
      > </a
      ><a name="9635" href="Maps.html#4403" class="Function Operator"
      >,</a
      ><a name="9636"
      > </a
      ><a name="9637" href="Maps.html#9554" class="Bound"
      >y</a
      ><a name="9638"
      > </a
      ><a name="9639" href="Maps.html#4403" class="Function Operator"
      >&#8614;</a
      ><a name="9640"
      > </a
      ><a name="9641" href="Maps.html#9563" class="Bound"
      >w</a
      ><a name="9642"
      > </a
      ><a name="9643" href="Maps.html#4403" class="Function Operator"
      >,</a
      ><a name="9644"
      > </a
      ><a name="9645" href="Maps.html#9537" class="Bound"
      >x</a
      ><a name="9646"
      > </a
      ><a name="9647" href="Maps.html#4403" class="Function Operator"
      >&#8614;</a
      ><a name="9648"
      > </a
      ><a name="9649" href="Maps.html#9546" class="Bound"
      >v</a
      ><a name="9650" class="Symbol"
      >)</a
      ><a name="9651"
      > </a
      ><a name="9652" href="Maps.html#9571" class="Bound"
      >z</a
      ><a name="9653"
      >
  </a
      ><a name="9656" href="Maps.html#9494" class="Function"
      >update-permute&#8242;&#8242;</a
      ><a name="9672"
      > </a
      ><a name="9673" class="Symbol"
      >{</a
      ><a name="9674" href="Maps.html#9674" class="Bound"
      >A</a
      ><a name="9675" class="Symbol"
      >}</a
      ><a name="9676"
      > </a
      ><a name="9677" href="Maps.html#9677" class="Bound"
      >&#961;</a
      ><a name="9678"
      > </a
      ><a name="9679" href="Maps.html#9679" class="Bound"
      >x</a
      ><a name="9680"
      > </a
      ><a name="9681" href="Maps.html#9681" class="Bound"
      >v</a
      ><a name="9682"
      > </a
      ><a name="9683" href="Maps.html#9683" class="Bound"
      >y</a
      ><a name="9684"
      > </a
      ><a name="9685" href="Maps.html#9685" class="Bound"
      >w</a
      ><a name="9686"
      > </a
      ><a name="9687" href="Maps.html#9687" class="Bound"
      >z</a
      ><a name="9688"
      > </a
      ><a name="9689" href="Maps.html#9689" class="Bound"
      >x&#8802;y</a
      ><a name="9692"
      > </a
      ><a name="9693" class="Keyword"
      >with</a
      ><a name="9697"
      > </a
      ><a name="9698" href="Maps.html#9679" class="Bound"
      >x</a
      ><a name="9699"
      > </a
      ><a name="9700" href="Maps.html#2558" class="Function Operator"
      >&#8799;</a
      ><a name="9701"
      > </a
      ><a name="9702" href="Maps.html#9687" class="Bound"
      >z</a
      ><a name="9703"
      > </a
      ><a name="9704" class="Symbol"
      >|</a
      ><a name="9705"
      > </a
      ><a name="9706" href="Maps.html#9683" class="Bound"
      >y</a
      ><a name="9707"
      > </a
      ><a name="9708" href="Maps.html#2558" class="Function Operator"
      >&#8799;</a
      ><a name="9709"
      > </a
      ><a name="9710" href="Maps.html#9687" class="Bound"
      >z</a
      ><a name="9711"
      >
  </a
      ><a name="9714" class="Symbol"
      >...</a
      ><a name="9717"
      > </a
      ><a name="9718" class="Symbol"
      >|</a
      ><a name="9719"
      > </a
      ><a name="9720" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#520" class="InductiveConstructor"
      >yes</a
      ><a name="9723"
      > </a
      ><a name="9724" href="Maps.html#9724" class="Bound"
      >x&#8801;z</a
      ><a name="9727"
      > </a
      ><a name="9728" class="Symbol"
      >|</a
      ><a name="9729"
      > </a
      ><a name="9730" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#520" class="InductiveConstructor"
      >yes</a
      ><a name="9733"
      > </a
      ><a name="9734" href="Maps.html#9734" class="Bound"
      >y&#8801;z</a
      ><a name="9737"
      > </a
      ><a name="9738" class="Symbol"
      >=</a
      ><a name="9739"
      > </a
      ><a name="9740" href="https://agda.github.io/agda-stdlib/Data.Empty.html#360" class="Function"
      >&#8869;-elim</a
      ><a name="9746"
      > </a
      ><a name="9747" class="Symbol"
      >(</a
      ><a name="9748" href="Maps.html#9689" class="Bound"
      >x&#8802;y</a
      ><a name="9751"
      > </a
      ><a name="9752" class="Symbol"
      >(</a
      ><a name="9753" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.Core.html#632" class="Function"
      >trans</a
      ><a name="9758"
      > </a
      ><a name="9759" href="Maps.html#9724" class="Bound"
      >x&#8801;z</a
      ><a name="9762"
      > </a
      ><a name="9763" class="Symbol"
      >(</a
      ><a name="9764" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.Core.html#565" class="Function"
      >sym</a
      ><a name="9767"
      > </a
      ><a name="9768" href="Maps.html#9734" class="Bound"
      >y&#8801;z</a
      ><a name="9771" class="Symbol"
      >)))</a
      ><a name="9774"
      >
  </a
      ><a name="9777" class="Symbol"
      >...</a
      ><a name="9780"
      > </a
      ><a name="9781" class="Symbol"
      >|</a
      ><a name="9782"
      > </a
      ><a name="9783" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#547" class="InductiveConstructor"
      >no</a
      ><a name="9785"
      >  </a
      ><a name="9787" href="Maps.html#9787" class="Bound"
      >x&#8802;z</a
      ><a name="9790"
      > </a
      ><a name="9791" class="Symbol"
      >|</a
      ><a name="9792"
      > </a
      ><a name="9793" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#520" class="InductiveConstructor"
      >yes</a
      ><a name="9796"
      > </a
      ><a name="9797" href="Maps.html#9797" class="Bound"
      >y&#8801;z</a
      ><a name="9800"
      > </a
      ><a name="9801" class="Keyword"
      >rewrite</a
      ><a name="9808"
      > </a
      ><a name="9809" href="Maps.html#9797" class="Bound"
      >y&#8801;z</a
      ><a name="9812"
      >  </a
      ><a name="9814" class="Symbol"
      >=</a
      ><a name="9815"
      >  </a
      ><a name="9817" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.Core.html#565" class="Function"
      >sym</a
      ><a name="9820"
      > </a
      ><a name="9821" class="Symbol"
      >(</a
      ><a name="9822" href="Maps.html#6073" class="Function"
      >update-eq&#8242;</a
      ><a name="9832"
      > </a
      ><a name="9833" href="Maps.html#9677" class="Bound"
      >&#961;</a
      ><a name="9834"
      > </a
      ><a name="9835" href="Maps.html#9687" class="Bound"
      >z</a
      ><a name="9836"
      > </a
      ><a name="9837" href="Maps.html#9685" class="Bound"
      >w</a
      ><a name="9838" class="Symbol"
      >)</a
      ><a name="9839"
      >  
  </a
      ><a name="9844" class="Symbol"
      >...</a
      ><a name="9847"
      > </a
      ><a name="9848" class="Symbol"
      >|</a
      ><a name="9849"
      > </a
      ><a name="9850" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#520" class="InductiveConstructor"
      >yes</a
      ><a name="9853"
      > </a
      ><a name="9854" href="Maps.html#9854" class="Bound"
      >x&#8801;z</a
      ><a name="9857"
      > </a
      ><a name="9858" class="Symbol"
      >|</a
      ><a name="9859"
      > </a
      ><a name="9860" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#547" class="InductiveConstructor"
      >no</a
      ><a name="9862"
      >  </a
      ><a name="9864" href="Maps.html#9864" class="Bound"
      >y&#8802;z</a
      ><a name="9867"
      > </a
      ><a name="9868" class="Keyword"
      >rewrite</a
      ><a name="9875"
      > </a
      ><a name="9876" href="Maps.html#9854" class="Bound"
      >x&#8801;z</a
      ><a name="9879"
      >  </a
      ><a name="9881" class="Symbol"
      >=</a
      ><a name="9882"
      >  </a
      ><a name="9884" href="Maps.html#6073" class="Function"
      >update-eq&#8242;</a
      ><a name="9894"
      > </a
      ><a name="9895" href="Maps.html#9677" class="Bound"
      >&#961;</a
      ><a name="9896"
      > </a
      ><a name="9897" href="Maps.html#9687" class="Bound"
      >z</a
      ><a name="9898"
      > </a
      ><a name="9899" href="Maps.html#9681" class="Bound"
      >v</a
      ><a name="9900"
      >
  </a
      ><a name="9903" class="Symbol"
      >...</a
      ><a name="9906"
      > </a
      ><a name="9907" class="Symbol"
      >|</a
      ><a name="9908"
      > </a
      ><a name="9909" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#547" class="InductiveConstructor"
      >no</a
      ><a name="9911"
      >  </a
      ><a name="9913" href="Maps.html#9913" class="Bound"
      >x&#8802;z</a
      ><a name="9916"
      > </a
      ><a name="9917" class="Symbol"
      >|</a
      ><a name="9918"
      > </a
      ><a name="9919" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#547" class="InductiveConstructor"
      >no</a
      ><a name="9921"
      >  </a
      ><a name="9923" href="Maps.html#9923" class="Bound"
      >y&#8802;z</a
      ><a name="9926"
      >  </a
      ><a name="9928" class="Symbol"
      >=</a
      ><a name="9929"
      >  </a
      ><a name="9931" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.Core.html#632" class="Function"
      >trans</a
      ><a name="9936"
      > </a
      ><a name="9937" class="Symbol"
      >(</a
      ><a name="9938" href="Maps.html#6495" class="Function"
      >update-neq</a
      ><a name="9948"
      > </a
      ><a name="9949" href="Maps.html#9677" class="Bound"
      >&#961;</a
      ><a name="9950"
      > </a
      ><a name="9951" href="Maps.html#9679" class="Bound"
      >x</a
      ><a name="9952"
      > </a
      ><a name="9953" href="Maps.html#9681" class="Bound"
      >v</a
      ><a name="9954"
      > </a
      ><a name="9955" href="Maps.html#9687" class="Bound"
      >z</a
      ><a name="9956"
      > </a
      ><a name="9957" href="Maps.html#9913" class="Bound"
      >x&#8802;z</a
      ><a name="9960" class="Symbol"
      >)</a
      ><a name="9961"
      > </a
      ><a name="9962" class="Symbol"
      >(</a
      ><a name="9963" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.Core.html#565" class="Function"
      >sym</a
      ><a name="9966"
      > </a
      ><a name="9967" class="Symbol"
      >(</a
      ><a name="9968" href="Maps.html#6495" class="Function"
      >update-neq</a
      ><a name="9978"
      > </a
      ><a name="9979" href="Maps.html#9677" class="Bound"
      >&#961;</a
      ><a name="9980"
      > </a
      ><a name="9981" href="Maps.html#9683" class="Bound"
      >y</a
      ><a name="9982"
      > </a
      ><a name="9983" href="Maps.html#9685" class="Bound"
      >w</a
      ><a name="9984"
      > </a
      ><a name="9985" href="Maps.html#9687" class="Bound"
      >z</a
      ><a name="9986"
      > </a
      ><a name="9987" href="Maps.html#9923" class="Bound"
      >y&#8802;z</a
      ><a name="9990" class="Symbol"
      >))</a
      >

</pre>
</div>

## Partial maps

Finally, we define _partial maps_ on top of total maps.  A partial
map with elements of type `A` is simply a total map with elements
of type `Maybe A` and default element `nothing`.

<pre class="Agda">

<a name="10227" href="Maps.html#10227" class="Function"
      >PartialMap</a
      ><a name="10237"
      > </a
      ><a name="10238" class="Symbol"
      >:</a
      ><a name="10239"
      > </a
      ><a name="10240" class="PrimitiveType"
      >Set</a
      ><a name="10243"
      > </a
      ><a name="10244" class="Symbol"
      >&#8594;</a
      ><a name="10245"
      > </a
      ><a name="10246" class="PrimitiveType"
      >Set</a
      ><a name="10249"
      >
</a
      ><a name="10250" href="Maps.html#10227" class="Function"
      >PartialMap</a
      ><a name="10260"
      > </a
      ><a name="10261" href="Maps.html#10261" class="Bound"
      >A</a
      ><a name="10262"
      > </a
      ><a name="10263" class="Symbol"
      >=</a
      ><a name="10264"
      > </a
      ><a name="10265" href="Maps.html#3738" class="Function"
      >TotalMap</a
      ><a name="10273"
      > </a
      ><a name="10274" class="Symbol"
      >(</a
      ><a name="10275" href="https://agda.github.io/agda-stdlib/Data.Maybe.Base.html#335" class="Datatype"
      >Maybe</a
      ><a name="10280"
      > </a
      ><a name="10281" href="Maps.html#10261" class="Bound"
      >A</a
      ><a name="10282" class="Symbol"
      >)</a
      >

</pre>

<pre class="Agda">

<a name="10309" class="Keyword"
      >module</a
      ><a name="10315"
      > </a
      ><a name="10316" href="Maps.html#10316" class="Module"
      >PartialMap</a
      ><a name="10326"
      > </a
      ><a name="10327" class="Keyword"
      >where</a
      >

</pre>

<pre class="Agda">

  <a name="10360" href="Maps.html#10360" class="Function"
      >&#8709;</a
      ><a name="10361"
      > </a
      ><a name="10362" class="Symbol"
      >:</a
      ><a name="10363"
      > </a
      ><a name="10364" class="Symbol"
      >&#8704;</a
      ><a name="10365"
      > </a
      ><a name="10366" class="Symbol"
      >{</a
      ><a name="10367" href="Maps.html#10367" class="Bound"
      >A</a
      ><a name="10368" class="Symbol"
      >}</a
      ><a name="10369"
      > </a
      ><a name="10370" class="Symbol"
      >&#8594;</a
      ><a name="10371"
      > </a
      ><a name="10372" href="Maps.html#10227" class="Function"
      >PartialMap</a
      ><a name="10382"
      > </a
      ><a name="10383" href="Maps.html#10367" class="Bound"
      >A</a
      ><a name="10384"
      >
  </a
      ><a name="10387" href="Maps.html#10360" class="Function"
      >&#8709;</a
      ><a name="10388"
      > </a
      ><a name="10389" class="Symbol"
      >=</a
      ><a name="10390"
      > </a
      ><a name="10391" href="Maps.html#4109" class="Function"
      >TotalMap.always</a
      ><a name="10406"
      > </a
      ><a name="10407" href="https://agda.github.io/agda-stdlib/Data.Maybe.Base.html#403" class="InductiveConstructor"
      >nothing</a
      >

</pre>

<pre class="Agda">

  <a name="10442" class="Keyword"
      >infixl</a
      ><a name="10448"
      > </a
      ><a name="10449" class="Number"
      >100</a
      ><a name="10452"
      > </a
      ><a name="10453" href="Maps.html#10464" class="Function Operator"
      >_,_&#8614;_</a
      ><a name="10458"
      >  

  </a
      ><a name="10464" href="Maps.html#10464" class="Function Operator"
      >_,_&#8614;_</a
      ><a name="10469"
      > </a
      ><a name="10470" class="Symbol"
      >:</a
      ><a name="10471"
      > </a
      ><a name="10472" class="Symbol"
      >&#8704;</a
      ><a name="10473"
      > </a
      ><a name="10474" class="Symbol"
      >{</a
      ><a name="10475" href="Maps.html#10475" class="Bound"
      >A</a
      ><a name="10476" class="Symbol"
      >}</a
      ><a name="10477"
      > </a
      ><a name="10478" class="Symbol"
      >(</a
      ><a name="10479" href="Maps.html#10479" class="Bound"
      >&#961;</a
      ><a name="10480"
      > </a
      ><a name="10481" class="Symbol"
      >:</a
      ><a name="10482"
      > </a
      ><a name="10483" href="Maps.html#10227" class="Function"
      >PartialMap</a
      ><a name="10493"
      > </a
      ><a name="10494" href="Maps.html#10475" class="Bound"
      >A</a
      ><a name="10495" class="Symbol"
      >)</a
      ><a name="10496"
      > </a
      ><a name="10497" class="Symbol"
      >(</a
      ><a name="10498" href="Maps.html#10498" class="Bound"
      >x</a
      ><a name="10499"
      > </a
      ><a name="10500" class="Symbol"
      >:</a
      ><a name="10501"
      > </a
      ><a name="10502" href="Maps.html#2215" class="Datatype"
      >Id</a
      ><a name="10504" class="Symbol"
      >)</a
      ><a name="10505"
      > </a
      ><a name="10506" class="Symbol"
      >(</a
      ><a name="10507" href="Maps.html#10507" class="Bound"
      >v</a
      ><a name="10508"
      > </a
      ><a name="10509" class="Symbol"
      >:</a
      ><a name="10510"
      > </a
      ><a name="10511" href="Maps.html#10475" class="Bound"
      >A</a
      ><a name="10512" class="Symbol"
      >)</a
      ><a name="10513"
      > </a
      ><a name="10514" class="Symbol"
      >&#8594;</a
      ><a name="10515"
      > </a
      ><a name="10516" href="Maps.html#10227" class="Function"
      >PartialMap</a
      ><a name="10526"
      > </a
      ><a name="10527" href="Maps.html#10475" class="Bound"
      >A</a
      ><a name="10528"
      >
  </a
      ><a name="10531" href="Maps.html#10531" class="Bound"
      >&#961;</a
      ><a name="10532"
      > </a
      ><a name="10533" href="Maps.html#10464" class="Function Operator"
      >,</a
      ><a name="10534"
      > </a
      ><a name="10535" href="Maps.html#10535" class="Bound"
      >x</a
      ><a name="10536"
      > </a
      ><a name="10537" href="Maps.html#10464" class="Function Operator"
      >&#8614;</a
      ><a name="10538"
      > </a
      ><a name="10539" href="Maps.html#10539" class="Bound"
      >v</a
      ><a name="10540"
      > </a
      ><a name="10541" class="Symbol"
      >=</a
      ><a name="10542"
      > </a
      ><a name="10543" href="Maps.html#4403" class="Function Operator"
      >TotalMap._,_&#8614;_</a
      ><a name="10557"
      > </a
      ><a name="10558" href="Maps.html#10531" class="Bound"
      >&#961;</a
      ><a name="10559"
      > </a
      ><a name="10560" href="Maps.html#10535" class="Bound"
      >x</a
      ><a name="10561"
      > </a
      ><a name="10562" class="Symbol"
      >(</a
      ><a name="10563" href="https://agda.github.io/agda-stdlib/Data.Maybe.Base.html#373" class="InductiveConstructor"
      >just</a
      ><a name="10567"
      > </a
      ><a name="10568" href="Maps.html#10539" class="Bound"
      >v</a
      ><a name="10569" class="Symbol"
      >)</a
      >

</pre>

We now lift all of the basic lemmas about total maps to partial maps.

<pre class="Agda">

  <a name="10669" href="Maps.html#10669" class="Function"
      >apply-&#8709;</a
      ><a name="10676"
      > </a
      ><a name="10677" class="Symbol"
      >:</a
      ><a name="10678"
      > </a
      ><a name="10679" class="Symbol"
      >&#8704;</a
      ><a name="10680"
      > </a
      ><a name="10681" class="Symbol"
      >{</a
      ><a name="10682" href="Maps.html#10682" class="Bound"
      >A</a
      ><a name="10683" class="Symbol"
      >}</a
      ><a name="10684"
      > </a
      ><a name="10685" class="Symbol"
      >&#8594;</a
      ><a name="10686"
      > </a
      ><a name="10687" class="Symbol"
      >(</a
      ><a name="10688" href="Maps.html#10688" class="Bound"
      >x</a
      ><a name="10689"
      > </a
      ><a name="10690" class="Symbol"
      >:</a
      ><a name="10691"
      > </a
      ><a name="10692" href="Maps.html#2215" class="Datatype"
      >Id</a
      ><a name="10694" class="Symbol"
      >)</a
      ><a name="10695"
      > </a
      ><a name="10696" class="Symbol"
      >&#8594;</a
      ><a name="10697"
      > </a
      ><a name="10698" class="Symbol"
      >(</a
      ><a name="10699" href="Maps.html#10360" class="Function"
      >&#8709;</a
      ><a name="10700"
      > </a
      ><a name="10701" class="Symbol"
      >{</a
      ><a name="10702" href="Maps.html#10682" class="Bound"
      >A</a
      ><a name="10703" class="Symbol"
      >}</a
      ><a name="10704"
      > </a
      ><a name="10705" href="Maps.html#10688" class="Bound"
      >x</a
      ><a name="10706" class="Symbol"
      >)</a
      ><a name="10707"
      > </a
      ><a name="10708" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="10709"
      > </a
      ><a name="10710" href="https://agda.github.io/agda-stdlib/Data.Maybe.Base.html#403" class="InductiveConstructor"
      >nothing</a
      ><a name="10717"
      >
  </a
      ><a name="10720" href="Maps.html#10669" class="Function"
      >apply-&#8709;</a
      ><a name="10727"
      > </a
      ><a name="10728" href="Maps.html#10728" class="Bound"
      >x</a
      ><a name="10729"
      >  </a
      ><a name="10731" class="Symbol"
      >=</a
      ><a name="10732"
      > </a
      ><a name="10733" href="Maps.html#5520" class="Postulate"
      >TotalMap.apply-always</a
      ><a name="10754"
      > </a
      ><a name="10755" href="https://agda.github.io/agda-stdlib/Data.Maybe.Base.html#403" class="InductiveConstructor"
      >nothing</a
      ><a name="10762"
      > </a
      ><a name="10763" href="Maps.html#10728" class="Bound"
      >x</a
      >

</pre>

<pre class="Agda">

  <a name="10792" href="Maps.html#10792" class="Function"
      >update-eq</a
      ><a name="10801"
      > </a
      ><a name="10802" class="Symbol"
      >:</a
      ><a name="10803"
      > </a
      ><a name="10804" class="Symbol"
      >&#8704;</a
      ><a name="10805"
      > </a
      ><a name="10806" class="Symbol"
      >{</a
      ><a name="10807" href="Maps.html#10807" class="Bound"
      >A</a
      ><a name="10808" class="Symbol"
      >}</a
      ><a name="10809"
      > </a
      ><a name="10810" class="Symbol"
      >(</a
      ><a name="10811" href="Maps.html#10811" class="Bound"
      >&#961;</a
      ><a name="10812"
      > </a
      ><a name="10813" class="Symbol"
      >:</a
      ><a name="10814"
      > </a
      ><a name="10815" href="Maps.html#10227" class="Function"
      >PartialMap</a
      ><a name="10825"
      > </a
      ><a name="10826" href="Maps.html#10807" class="Bound"
      >A</a
      ><a name="10827" class="Symbol"
      >)</a
      ><a name="10828"
      > </a
      ><a name="10829" class="Symbol"
      >(</a
      ><a name="10830" href="Maps.html#10830" class="Bound"
      >x</a
      ><a name="10831"
      > </a
      ><a name="10832" class="Symbol"
      >:</a
      ><a name="10833"
      > </a
      ><a name="10834" href="Maps.html#2215" class="Datatype"
      >Id</a
      ><a name="10836" class="Symbol"
      >)</a
      ><a name="10837"
      > </a
      ><a name="10838" class="Symbol"
      >(</a
      ><a name="10839" href="Maps.html#10839" class="Bound"
      >v</a
      ><a name="10840"
      > </a
      ><a name="10841" class="Symbol"
      >:</a
      ><a name="10842"
      > </a
      ><a name="10843" href="Maps.html#10807" class="Bound"
      >A</a
      ><a name="10844" class="Symbol"
      >)</a
      ><a name="10845"
      >
            </a
      ><a name="10858" class="Symbol"
      >&#8594;</a
      ><a name="10859"
      > </a
      ><a name="10860" class="Symbol"
      >(</a
      ><a name="10861" href="Maps.html#10811" class="Bound"
      >&#961;</a
      ><a name="10862"
      > </a
      ><a name="10863" href="Maps.html#10464" class="Function Operator"
      >,</a
      ><a name="10864"
      > </a
      ><a name="10865" href="Maps.html#10830" class="Bound"
      >x</a
      ><a name="10866"
      > </a
      ><a name="10867" href="Maps.html#10464" class="Function Operator"
      >&#8614;</a
      ><a name="10868"
      > </a
      ><a name="10869" href="Maps.html#10839" class="Bound"
      >v</a
      ><a name="10870" class="Symbol"
      >)</a
      ><a name="10871"
      > </a
      ><a name="10872" href="Maps.html#10830" class="Bound"
      >x</a
      ><a name="10873"
      > </a
      ><a name="10874" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="10875"
      > </a
      ><a name="10876" href="https://agda.github.io/agda-stdlib/Data.Maybe.Base.html#373" class="InductiveConstructor"
      >just</a
      ><a name="10880"
      > </a
      ><a name="10881" href="Maps.html#10839" class="Bound"
      >v</a
      ><a name="10882"
      >
  </a
      ><a name="10885" href="Maps.html#10792" class="Function"
      >update-eq</a
      ><a name="10894"
      > </a
      ><a name="10895" href="Maps.html#10895" class="Bound"
      >&#961;</a
      ><a name="10896"
      > </a
      ><a name="10897" href="Maps.html#10897" class="Bound"
      >x</a
      ><a name="10898"
      > </a
      ><a name="10899" href="Maps.html#10899" class="Bound"
      >v</a
      ><a name="10900"
      > </a
      ><a name="10901" class="Symbol"
      >=</a
      ><a name="10902"
      > </a
      ><a name="10903" href="Maps.html#5939" class="Postulate"
      >TotalMap.update-eq</a
      ><a name="10921"
      > </a
      ><a name="10922" href="Maps.html#10895" class="Bound"
      >&#961;</a
      ><a name="10923"
      > </a
      ><a name="10924" href="Maps.html#10897" class="Bound"
      >x</a
      ><a name="10925"
      > </a
      ><a name="10926" class="Symbol"
      >(</a
      ><a name="10927" href="https://agda.github.io/agda-stdlib/Data.Maybe.Base.html#373" class="InductiveConstructor"
      >just</a
      ><a name="10931"
      > </a
      ><a name="10932" href="Maps.html#10899" class="Bound"
      >v</a
      ><a name="10933" class="Symbol"
      >)</a
      >

</pre>

<pre class="Agda">

  <a name="10962" href="Maps.html#10962" class="Function"
      >update-neq</a
      ><a name="10972"
      > </a
      ><a name="10973" class="Symbol"
      >:</a
      ><a name="10974"
      > </a
      ><a name="10975" class="Symbol"
      >&#8704;</a
      ><a name="10976"
      > </a
      ><a name="10977" class="Symbol"
      >{</a
      ><a name="10978" href="Maps.html#10978" class="Bound"
      >A</a
      ><a name="10979" class="Symbol"
      >}</a
      ><a name="10980"
      > </a
      ><a name="10981" class="Symbol"
      >(</a
      ><a name="10982" href="Maps.html#10982" class="Bound"
      >&#961;</a
      ><a name="10983"
      > </a
      ><a name="10984" class="Symbol"
      >:</a
      ><a name="10985"
      > </a
      ><a name="10986" href="Maps.html#10227" class="Function"
      >PartialMap</a
      ><a name="10996"
      > </a
      ><a name="10997" href="Maps.html#10978" class="Bound"
      >A</a
      ><a name="10998" class="Symbol"
      >)</a
      ><a name="10999"
      > </a
      ><a name="11000" class="Symbol"
      >(</a
      ><a name="11001" href="Maps.html#11001" class="Bound"
      >x</a
      ><a name="11002"
      > </a
      ><a name="11003" class="Symbol"
      >:</a
      ><a name="11004"
      > </a
      ><a name="11005" href="Maps.html#2215" class="Datatype"
      >Id</a
      ><a name="11007" class="Symbol"
      >)</a
      ><a name="11008"
      > </a
      ><a name="11009" class="Symbol"
      >(</a
      ><a name="11010" href="Maps.html#11010" class="Bound"
      >v</a
      ><a name="11011"
      > </a
      ><a name="11012" class="Symbol"
      >:</a
      ><a name="11013"
      > </a
      ><a name="11014" href="Maps.html#10978" class="Bound"
      >A</a
      ><a name="11015" class="Symbol"
      >)</a
      ><a name="11016"
      > </a
      ><a name="11017" class="Symbol"
      >(</a
      ><a name="11018" href="Maps.html#11018" class="Bound"
      >y</a
      ><a name="11019"
      > </a
      ><a name="11020" class="Symbol"
      >:</a
      ><a name="11021"
      > </a
      ><a name="11022" href="Maps.html#2215" class="Datatype"
      >Id</a
      ><a name="11024" class="Symbol"
      >)</a
      ><a name="11025"
      >
             </a
      ><a name="11039" class="Symbol"
      >&#8594;</a
      ><a name="11040"
      > </a
      ><a name="11041" href="Maps.html#11001" class="Bound"
      >x</a
      ><a name="11042"
      > </a
      ><a name="11043" href="https://agda.github.io/agda-stdlib/Relation.Binary.Core.html#4493" class="Function Operator"
      >&#8802;</a
      ><a name="11044"
      > </a
      ><a name="11045" href="Maps.html#11018" class="Bound"
      >y</a
      ><a name="11046"
      > </a
      ><a name="11047" class="Symbol"
      >&#8594;</a
      ><a name="11048"
      > </a
      ><a name="11049" class="Symbol"
      >(</a
      ><a name="11050" href="Maps.html#10982" class="Bound"
      >&#961;</a
      ><a name="11051"
      > </a
      ><a name="11052" href="Maps.html#10464" class="Function Operator"
      >,</a
      ><a name="11053"
      > </a
      ><a name="11054" href="Maps.html#11001" class="Bound"
      >x</a
      ><a name="11055"
      > </a
      ><a name="11056" href="Maps.html#10464" class="Function Operator"
      >&#8614;</a
      ><a name="11057"
      > </a
      ><a name="11058" href="Maps.html#11010" class="Bound"
      >v</a
      ><a name="11059" class="Symbol"
      >)</a
      ><a name="11060"
      > </a
      ><a name="11061" href="Maps.html#11018" class="Bound"
      >y</a
      ><a name="11062"
      > </a
      ><a name="11063" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="11064"
      > </a
      ><a name="11065" href="Maps.html#10982" class="Bound"
      >&#961;</a
      ><a name="11066"
      > </a
      ><a name="11067" href="Maps.html#11018" class="Bound"
      >y</a
      ><a name="11068"
      >
  </a
      ><a name="11071" href="Maps.html#10962" class="Function"
      >update-neq</a
      ><a name="11081"
      > </a
      ><a name="11082" href="Maps.html#11082" class="Bound"
      >&#961;</a
      ><a name="11083"
      > </a
      ><a name="11084" href="Maps.html#11084" class="Bound"
      >x</a
      ><a name="11085"
      > </a
      ><a name="11086" href="Maps.html#11086" class="Bound"
      >v</a
      ><a name="11087"
      > </a
      ><a name="11088" href="Maps.html#11088" class="Bound"
      >y</a
      ><a name="11089"
      > </a
      ><a name="11090" href="Maps.html#11090" class="Bound"
      >x&#8802;y</a
      ><a name="11093"
      > </a
      ><a name="11094" class="Symbol"
      >=</a
      ><a name="11095"
      > </a
      ><a name="11096" href="Maps.html#6495" class="Function"
      >TotalMap.update-neq</a
      ><a name="11115"
      > </a
      ><a name="11116" href="Maps.html#11082" class="Bound"
      >&#961;</a
      ><a name="11117"
      > </a
      ><a name="11118" href="Maps.html#11084" class="Bound"
      >x</a
      ><a name="11119"
      > </a
      ><a name="11120" class="Symbol"
      >(</a
      ><a name="11121" href="https://agda.github.io/agda-stdlib/Data.Maybe.Base.html#373" class="InductiveConstructor"
      >just</a
      ><a name="11125"
      > </a
      ><a name="11126" href="Maps.html#11086" class="Bound"
      >v</a
      ><a name="11127" class="Symbol"
      >)</a
      ><a name="11128"
      > </a
      ><a name="11129" href="Maps.html#11088" class="Bound"
      >y</a
      ><a name="11130"
      > </a
      ><a name="11131" href="Maps.html#11090" class="Bound"
      >x&#8802;y</a
      >

</pre>

<pre class="Agda">

  <a name="11162" href="Maps.html#11162" class="Function"
      >update-shadow</a
      ><a name="11175"
      > </a
      ><a name="11176" class="Symbol"
      >:</a
      ><a name="11177"
      > </a
      ><a name="11178" class="Symbol"
      >&#8704;</a
      ><a name="11179"
      > </a
      ><a name="11180" class="Symbol"
      >{</a
      ><a name="11181" href="Maps.html#11181" class="Bound"
      >A</a
      ><a name="11182" class="Symbol"
      >}</a
      ><a name="11183"
      > </a
      ><a name="11184" class="Symbol"
      >(</a
      ><a name="11185" href="Maps.html#11185" class="Bound"
      >&#961;</a
      ><a name="11186"
      > </a
      ><a name="11187" class="Symbol"
      >:</a
      ><a name="11188"
      > </a
      ><a name="11189" href="Maps.html#10227" class="Function"
      >PartialMap</a
      ><a name="11199"
      > </a
      ><a name="11200" href="Maps.html#11181" class="Bound"
      >A</a
      ><a name="11201" class="Symbol"
      >)</a
      ><a name="11202"
      > </a
      ><a name="11203" class="Symbol"
      >(</a
      ><a name="11204" href="Maps.html#11204" class="Bound"
      >x</a
      ><a name="11205"
      > </a
      ><a name="11206" class="Symbol"
      >:</a
      ><a name="11207"
      > </a
      ><a name="11208" href="Maps.html#2215" class="Datatype"
      >Id</a
      ><a name="11210" class="Symbol"
      >)</a
      ><a name="11211"
      > </a
      ><a name="11212" class="Symbol"
      >(</a
      ><a name="11213" href="Maps.html#11213" class="Bound"
      >v</a
      ><a name="11214"
      > </a
      ><a name="11215" href="Maps.html#11215" class="Bound"
      >w</a
      ><a name="11216"
      > </a
      ><a name="11217" class="Symbol"
      >:</a
      ><a name="11218"
      > </a
      ><a name="11219" href="Maps.html#11181" class="Bound"
      >A</a
      ><a name="11220" class="Symbol"
      >)</a
      ><a name="11221"
      > 
                </a
      ><a name="11239" class="Symbol"
      >&#8594;</a
      ><a name="11240"
      > </a
      ><a name="11241" class="Symbol"
      >(</a
      ><a name="11242" href="Maps.html#11185" class="Bound"
      >&#961;</a
      ><a name="11243"
      > </a
      ><a name="11244" href="Maps.html#10464" class="Function Operator"
      >,</a
      ><a name="11245"
      > </a
      ><a name="11246" href="Maps.html#11204" class="Bound"
      >x</a
      ><a name="11247"
      > </a
      ><a name="11248" href="Maps.html#10464" class="Function Operator"
      >&#8614;</a
      ><a name="11249"
      > </a
      ><a name="11250" href="Maps.html#11213" class="Bound"
      >v</a
      ><a name="11251"
      > </a
      ><a name="11252" href="Maps.html#10464" class="Function Operator"
      >,</a
      ><a name="11253"
      > </a
      ><a name="11254" href="Maps.html#11204" class="Bound"
      >x</a
      ><a name="11255"
      > </a
      ><a name="11256" href="Maps.html#10464" class="Function Operator"
      >&#8614;</a
      ><a name="11257"
      > </a
      ><a name="11258" href="Maps.html#11215" class="Bound"
      >w</a
      ><a name="11259" class="Symbol"
      >)</a
      ><a name="11260"
      > </a
      ><a name="11261" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="11262"
      > </a
      ><a name="11263" class="Symbol"
      >(</a
      ><a name="11264" href="Maps.html#11185" class="Bound"
      >&#961;</a
      ><a name="11265"
      > </a
      ><a name="11266" href="Maps.html#10464" class="Function Operator"
      >,</a
      ><a name="11267"
      > </a
      ><a name="11268" href="Maps.html#11204" class="Bound"
      >x</a
      ><a name="11269"
      > </a
      ><a name="11270" href="Maps.html#10464" class="Function Operator"
      >&#8614;</a
      ><a name="11271"
      > </a
      ><a name="11272" href="Maps.html#11215" class="Bound"
      >w</a
      ><a name="11273" class="Symbol"
      >)</a
      ><a name="11274"
      >
  </a
      ><a name="11277" href="Maps.html#11162" class="Function"
      >update-shadow</a
      ><a name="11290"
      > </a
      ><a name="11291" href="Maps.html#11291" class="Bound"
      >&#961;</a
      ><a name="11292"
      > </a
      ><a name="11293" href="Maps.html#11293" class="Bound"
      >x</a
      ><a name="11294"
      > </a
      ><a name="11295" href="Maps.html#11295" class="Bound"
      >v</a
      ><a name="11296"
      > </a
      ><a name="11297" href="Maps.html#11297" class="Bound"
      >w</a
      ><a name="11298"
      > </a
      ><a name="11299" class="Symbol"
      >=</a
      ><a name="11300"
      > </a
      ><a name="11301" href="Maps.html#7314" class="Postulate"
      >TotalMap.update-shadow</a
      ><a name="11323"
      > </a
      ><a name="11324" href="Maps.html#11291" class="Bound"
      >&#961;</a
      ><a name="11325"
      > </a
      ><a name="11326" href="Maps.html#11293" class="Bound"
      >x</a
      ><a name="11327"
      > </a
      ><a name="11328" class="Symbol"
      >(</a
      ><a name="11329" href="https://agda.github.io/agda-stdlib/Data.Maybe.Base.html#373" class="InductiveConstructor"
      >just</a
      ><a name="11333"
      > </a
      ><a name="11334" href="Maps.html#11295" class="Bound"
      >v</a
      ><a name="11335" class="Symbol"
      >)</a
      ><a name="11336"
      > </a
      ><a name="11337" class="Symbol"
      >(</a
      ><a name="11338" href="https://agda.github.io/agda-stdlib/Data.Maybe.Base.html#373" class="InductiveConstructor"
      >just</a
      ><a name="11342"
      > </a
      ><a name="11343" href="Maps.html#11297" class="Bound"
      >w</a
      ><a name="11344" class="Symbol"
      >)</a
      >

</pre>

<pre class="Agda">

  <a name="11373" href="Maps.html#11373" class="Function"
      >update-same</a
      ><a name="11384"
      > </a
      ><a name="11385" class="Symbol"
      >:</a
      ><a name="11386"
      > </a
      ><a name="11387" class="Symbol"
      >&#8704;</a
      ><a name="11388"
      > </a
      ><a name="11389" class="Symbol"
      >{</a
      ><a name="11390" href="Maps.html#11390" class="Bound"
      >A</a
      ><a name="11391" class="Symbol"
      >}</a
      ><a name="11392"
      > </a
      ><a name="11393" class="Symbol"
      >(</a
      ><a name="11394" href="Maps.html#11394" class="Bound"
      >&#961;</a
      ><a name="11395"
      > </a
      ><a name="11396" class="Symbol"
      >:</a
      ><a name="11397"
      > </a
      ><a name="11398" href="Maps.html#10227" class="Function"
      >PartialMap</a
      ><a name="11408"
      > </a
      ><a name="11409" href="Maps.html#11390" class="Bound"
      >A</a
      ><a name="11410" class="Symbol"
      >)</a
      ><a name="11411"
      > </a
      ><a name="11412" class="Symbol"
      >(</a
      ><a name="11413" href="Maps.html#11413" class="Bound"
      >x</a
      ><a name="11414"
      > </a
      ><a name="11415" class="Symbol"
      >:</a
      ><a name="11416"
      > </a
      ><a name="11417" href="Maps.html#2215" class="Datatype"
      >Id</a
      ><a name="11419" class="Symbol"
      >)</a
      ><a name="11420"
      > </a
      ><a name="11421" class="Symbol"
      >(</a
      ><a name="11422" href="Maps.html#11422" class="Bound"
      >v</a
      ><a name="11423"
      > </a
      ><a name="11424" class="Symbol"
      >:</a
      ><a name="11425"
      > </a
      ><a name="11426" href="Maps.html#11390" class="Bound"
      >A</a
      ><a name="11427" class="Symbol"
      >)</a
      ><a name="11428"
      > 
              </a
      ><a name="11444" class="Symbol"
      >&#8594;</a
      ><a name="11445"
      > </a
      ><a name="11446" href="Maps.html#11394" class="Bound"
      >&#961;</a
      ><a name="11447"
      > </a
      ><a name="11448" href="Maps.html#11413" class="Bound"
      >x</a
      ><a name="11449"
      > </a
      ><a name="11450" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="11451"
      > </a
      ><a name="11452" href="https://agda.github.io/agda-stdlib/Data.Maybe.Base.html#373" class="InductiveConstructor"
      >just</a
      ><a name="11456"
      > </a
      ><a name="11457" href="Maps.html#11422" class="Bound"
      >v</a
      ><a name="11458"
      >
              </a
      ><a name="11473" class="Symbol"
      >&#8594;</a
      ><a name="11474"
      > </a
      ><a name="11475" class="Symbol"
      >(</a
      ><a name="11476" href="Maps.html#11394" class="Bound"
      >&#961;</a
      ><a name="11477"
      > </a
      ><a name="11478" href="Maps.html#10464" class="Function Operator"
      >,</a
      ><a name="11479"
      > </a
      ><a name="11480" href="Maps.html#11413" class="Bound"
      >x</a
      ><a name="11481"
      > </a
      ><a name="11482" href="Maps.html#10464" class="Function Operator"
      >&#8614;</a
      ><a name="11483"
      > </a
      ><a name="11484" href="Maps.html#11422" class="Bound"
      >v</a
      ><a name="11485" class="Symbol"
      >)</a
      ><a name="11486"
      > </a
      ><a name="11487" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="11488"
      > </a
      ><a name="11489" href="Maps.html#11394" class="Bound"
      >&#961;</a
      ><a name="11490"
      >
  </a
      ><a name="11493" href="Maps.html#11373" class="Function"
      >update-same</a
      ><a name="11504"
      > </a
      ><a name="11505" href="Maps.html#11505" class="Bound"
      >&#961;</a
      ><a name="11506"
      > </a
      ><a name="11507" href="Maps.html#11507" class="Bound"
      >x</a
      ><a name="11508"
      > </a
      ><a name="11509" href="Maps.html#11509" class="Bound"
      >v</a
      ><a name="11510"
      > </a
      ><a name="11511" href="Maps.html#11511" class="Bound"
      >&#961;x&#8801;v</a
      ><a name="11515"
      > </a
      ><a name="11516" class="Keyword"
      >rewrite</a
      ><a name="11523"
      > </a
      ><a name="11524" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.Core.html#565" class="Function"
      >sym</a
      ><a name="11527"
      > </a
      ><a name="11528" href="Maps.html#11511" class="Bound"
      >&#961;x&#8801;v</a
      ><a name="11532"
      > </a
      ><a name="11533" class="Symbol"
      >=</a
      ><a name="11534"
      > </a
      ><a name="11535" href="Maps.html#8049" class="Postulate"
      >TotalMap.update-same</a
      ><a name="11555"
      > </a
      ><a name="11556" href="Maps.html#11505" class="Bound"
      >&#961;</a
      ><a name="11557"
      > </a
      ><a name="11558" href="Maps.html#11507" class="Bound"
      >x</a
      >

</pre>

<pre class="Agda">

  <a name="11587" href="Maps.html#11587" class="Function"
      >update-permute</a
      ><a name="11601"
      > </a
      ><a name="11602" class="Symbol"
      >:</a
      ><a name="11603"
      > </a
      ><a name="11604" class="Symbol"
      >&#8704;</a
      ><a name="11605"
      > </a
      ><a name="11606" class="Symbol"
      >{</a
      ><a name="11607" href="Maps.html#11607" class="Bound"
      >A</a
      ><a name="11608" class="Symbol"
      >}</a
      ><a name="11609"
      > </a
      ><a name="11610" class="Symbol"
      >(</a
      ><a name="11611" href="Maps.html#11611" class="Bound"
      >&#961;</a
      ><a name="11612"
      > </a
      ><a name="11613" class="Symbol"
      >:</a
      ><a name="11614"
      > </a
      ><a name="11615" href="Maps.html#10227" class="Function"
      >PartialMap</a
      ><a name="11625"
      > </a
      ><a name="11626" href="Maps.html#11607" class="Bound"
      >A</a
      ><a name="11627" class="Symbol"
      >)</a
      ><a name="11628"
      > </a
      ><a name="11629" class="Symbol"
      >(</a
      ><a name="11630" href="Maps.html#11630" class="Bound"
      >x</a
      ><a name="11631"
      > </a
      ><a name="11632" class="Symbol"
      >:</a
      ><a name="11633"
      > </a
      ><a name="11634" href="Maps.html#2215" class="Datatype"
      >Id</a
      ><a name="11636" class="Symbol"
      >)</a
      ><a name="11637"
      > </a
      ><a name="11638" class="Symbol"
      >(</a
      ><a name="11639" href="Maps.html#11639" class="Bound"
      >v</a
      ><a name="11640"
      > </a
      ><a name="11641" class="Symbol"
      >:</a
      ><a name="11642"
      > </a
      ><a name="11643" href="Maps.html#11607" class="Bound"
      >A</a
      ><a name="11644" class="Symbol"
      >)</a
      ><a name="11645"
      > </a
      ><a name="11646" class="Symbol"
      >(</a
      ><a name="11647" href="Maps.html#11647" class="Bound"
      >y</a
      ><a name="11648"
      > </a
      ><a name="11649" class="Symbol"
      >:</a
      ><a name="11650"
      > </a
      ><a name="11651" href="Maps.html#2215" class="Datatype"
      >Id</a
      ><a name="11653" class="Symbol"
      >)</a
      ><a name="11654"
      > </a
      ><a name="11655" class="Symbol"
      >(</a
      ><a name="11656" href="Maps.html#11656" class="Bound"
      >w</a
      ><a name="11657"
      > </a
      ><a name="11658" class="Symbol"
      >:</a
      ><a name="11659"
      > </a
      ><a name="11660" href="Maps.html#11607" class="Bound"
      >A</a
      ><a name="11661" class="Symbol"
      >)</a
      ><a name="11662"
      > 
                 </a
      ><a name="11681" class="Symbol"
      >&#8594;</a
      ><a name="11682"
      > </a
      ><a name="11683" href="Maps.html#11630" class="Bound"
      >x</a
      ><a name="11684"
      > </a
      ><a name="11685" href="https://agda.github.io/agda-stdlib/Relation.Binary.Core.html#4493" class="Function Operator"
      >&#8802;</a
      ><a name="11686"
      > </a
      ><a name="11687" href="Maps.html#11647" class="Bound"
      >y</a
      ><a name="11688"
      > </a
      ><a name="11689" class="Symbol"
      >&#8594;</a
      ><a name="11690"
      > </a
      ><a name="11691" class="Symbol"
      >(</a
      ><a name="11692" href="Maps.html#11611" class="Bound"
      >&#961;</a
      ><a name="11693"
      > </a
      ><a name="11694" href="Maps.html#10464" class="Function Operator"
      >,</a
      ><a name="11695"
      > </a
      ><a name="11696" href="Maps.html#11630" class="Bound"
      >x</a
      ><a name="11697"
      > </a
      ><a name="11698" href="Maps.html#10464" class="Function Operator"
      >&#8614;</a
      ><a name="11699"
      > </a
      ><a name="11700" href="Maps.html#11639" class="Bound"
      >v</a
      ><a name="11701"
      > </a
      ><a name="11702" href="Maps.html#10464" class="Function Operator"
      >,</a
      ><a name="11703"
      > </a
      ><a name="11704" href="Maps.html#11647" class="Bound"
      >y</a
      ><a name="11705"
      > </a
      ><a name="11706" href="Maps.html#10464" class="Function Operator"
      >&#8614;</a
      ><a name="11707"
      > </a
      ><a name="11708" href="Maps.html#11656" class="Bound"
      >w</a
      ><a name="11709" class="Symbol"
      >)</a
      ><a name="11710"
      > </a
      ><a name="11711" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="11712"
      > </a
      ><a name="11713" class="Symbol"
      >(</a
      ><a name="11714" href="Maps.html#11611" class="Bound"
      >&#961;</a
      ><a name="11715"
      > </a
      ><a name="11716" href="Maps.html#10464" class="Function Operator"
      >,</a
      ><a name="11717"
      > </a
      ><a name="11718" href="Maps.html#11647" class="Bound"
      >y</a
      ><a name="11719"
      > </a
      ><a name="11720" href="Maps.html#10464" class="Function Operator"
      >&#8614;</a
      ><a name="11721"
      > </a
      ><a name="11722" href="Maps.html#11656" class="Bound"
      >w</a
      ><a name="11723"
      > </a
      ><a name="11724" href="Maps.html#10464" class="Function Operator"
      >,</a
      ><a name="11725"
      > </a
      ><a name="11726" href="Maps.html#11630" class="Bound"
      >x</a
      ><a name="11727"
      > </a
      ><a name="11728" href="Maps.html#10464" class="Function Operator"
      >&#8614;</a
      ><a name="11729"
      > </a
      ><a name="11730" href="Maps.html#11639" class="Bound"
      >v</a
      ><a name="11731" class="Symbol"
      >)</a
      ><a name="11732"
      >
  </a
      ><a name="11735" href="Maps.html#11587" class="Function"
      >update-permute</a
      ><a name="11749"
      > </a
      ><a name="11750" href="Maps.html#11750" class="Bound"
      >&#961;</a
      ><a name="11751"
      > </a
      ><a name="11752" href="Maps.html#11752" class="Bound"
      >x</a
      ><a name="11753"
      > </a
      ><a name="11754" href="Maps.html#11754" class="Bound"
      >v</a
      ><a name="11755"
      > </a
      ><a name="11756" href="Maps.html#11756" class="Bound"
      >y</a
      ><a name="11757"
      > </a
      ><a name="11758" href="Maps.html#11758" class="Bound"
      >w</a
      ><a name="11759"
      > </a
      ><a name="11760" href="Maps.html#11760" class="Bound"
      >x&#8802;y</a
      ><a name="11763"
      > </a
      ><a name="11764" class="Symbol"
      >=</a
      ><a name="11765"
      > </a
      ><a name="11766" href="Maps.html#8649" class="Postulate"
      >TotalMap.update-permute</a
      ><a name="11789"
      > </a
      ><a name="11790" href="Maps.html#11750" class="Bound"
      >&#961;</a
      ><a name="11791"
      > </a
      ><a name="11792" href="Maps.html#11752" class="Bound"
      >x</a
      ><a name="11793"
      > </a
      ><a name="11794" class="Symbol"
      >(</a
      ><a name="11795" href="https://agda.github.io/agda-stdlib/Data.Maybe.Base.html#373" class="InductiveConstructor"
      >just</a
      ><a name="11799"
      > </a
      ><a name="11800" href="Maps.html#11754" class="Bound"
      >v</a
      ><a name="11801" class="Symbol"
      >)</a
      ><a name="11802"
      > </a
      ><a name="11803" href="Maps.html#11756" class="Bound"
      >y</a
      ><a name="11804"
      > </a
      ><a name="11805" class="Symbol"
      >(</a
      ><a name="11806" href="https://agda.github.io/agda-stdlib/Data.Maybe.Base.html#373" class="InductiveConstructor"
      >just</a
      ><a name="11810"
      > </a
      ><a name="11811" href="Maps.html#11758" class="Bound"
      >w</a
      ><a name="11812" class="Symbol"
      >)</a
      ><a name="11813"
      > </a
      ><a name="11814" href="Maps.html#11760" class="Bound"
      >x&#8802;y</a
      >

</pre>
