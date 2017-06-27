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

## Extensionality

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

<a name="3757" href="Maps.html#3757" class="Function"
      >TotalMap</a
      ><a name="3765"
      > </a
      ><a name="3766" class="Symbol"
      >:</a
      ><a name="3767"
      > </a
      ><a name="3768" class="PrimitiveType"
      >Set</a
      ><a name="3771"
      > </a
      ><a name="3772" class="Symbol"
      >&#8594;</a
      ><a name="3773"
      > </a
      ><a name="3774" class="PrimitiveType"
      >Set</a
      ><a name="3777"
      >
</a
      ><a name="3778" href="Maps.html#3757" class="Function"
      >TotalMap</a
      ><a name="3786"
      > </a
      ><a name="3787" href="Maps.html#3787" class="Bound"
      >A</a
      ><a name="3788"
      > </a
      ><a name="3789" class="Symbol"
      >=</a
      ><a name="3790"
      > </a
      ><a name="3791" href="Maps.html#2215" class="Datatype"
      >Id</a
      ><a name="3793"
      > </a
      ><a name="3794" class="Symbol"
      >&#8594;</a
      ><a name="3795"
      > </a
      ><a name="3796" href="Maps.html#3787" class="Bound"
      >A</a
      >

</pre>

Intuitively, a total map over anﬁ element type $$A$$ _is_ just a
function that can be used to look up ids, yielding $$A$$s.

<pre class="Agda">

<a name="3948" class="Keyword"
      >module</a
      ><a name="3954"
      > </a
      ><a name="3955" href="Maps.html#3955" class="Module"
      >TotalMap</a
      ><a name="3963"
      > </a
      ><a name="3964" class="Keyword"
      >where</a
      >

</pre>

The function `always` yields a total map given a
default element; this map always returns the default element when
applied to any id.

<pre class="Agda">

  <a name="4132" href="Maps.html#4132" class="Function"
      >always</a
      ><a name="4138"
      > </a
      ><a name="4139" class="Symbol"
      >:</a
      ><a name="4140"
      > </a
      ><a name="4141" class="Symbol"
      >&#8704;</a
      ><a name="4142"
      > </a
      ><a name="4143" class="Symbol"
      >{</a
      ><a name="4144" href="Maps.html#4144" class="Bound"
      >A</a
      ><a name="4145" class="Symbol"
      >}</a
      ><a name="4146"
      > </a
      ><a name="4147" class="Symbol"
      >&#8594;</a
      ><a name="4148"
      > </a
      ><a name="4149" href="Maps.html#4144" class="Bound"
      >A</a
      ><a name="4150"
      > </a
      ><a name="4151" class="Symbol"
      >&#8594;</a
      ><a name="4152"
      > </a
      ><a name="4153" href="Maps.html#3757" class="Function"
      >TotalMap</a
      ><a name="4161"
      > </a
      ><a name="4162" href="Maps.html#4144" class="Bound"
      >A</a
      ><a name="4163"
      >
  </a
      ><a name="4166" href="Maps.html#4132" class="Function"
      >always</a
      ><a name="4172"
      > </a
      ><a name="4173" href="Maps.html#4173" class="Bound"
      >v</a
      ><a name="4174"
      > </a
      ><a name="4175" href="Maps.html#4175" class="Bound"
      >x</a
      ><a name="4176"
      > </a
      ><a name="4177" class="Symbol"
      >=</a
      ><a name="4178"
      > </a
      ><a name="4179" href="Maps.html#4173" class="Bound"
      >v</a
      >

</pre>

More interesting is the update function, which (as before) takes
a map $$ρ$$, a key $$x$$, and a value $$v$$ and returns a new map that
takes $$x$$ to $$v$$ and takes every other key to whatever $$ρ$$ does.

<pre class="Agda">

  <a name="4416" href="Maps.html#4416" class="Function Operator"
      >_,_&#8614;_</a
      ><a name="4421"
      > </a
      ><a name="4422" class="Symbol"
      >:</a
      ><a name="4423"
      > </a
      ><a name="4424" class="Symbol"
      >&#8704;</a
      ><a name="4425"
      > </a
      ><a name="4426" class="Symbol"
      >{</a
      ><a name="4427" href="Maps.html#4427" class="Bound"
      >A</a
      ><a name="4428" class="Symbol"
      >}</a
      ><a name="4429"
      > </a
      ><a name="4430" class="Symbol"
      >&#8594;</a
      ><a name="4431"
      > </a
      ><a name="4432" href="Maps.html#3757" class="Function"
      >TotalMap</a
      ><a name="4440"
      > </a
      ><a name="4441" href="Maps.html#4427" class="Bound"
      >A</a
      ><a name="4442"
      > </a
      ><a name="4443" class="Symbol"
      >&#8594;</a
      ><a name="4444"
      > </a
      ><a name="4445" href="Maps.html#2215" class="Datatype"
      >Id</a
      ><a name="4447"
      > </a
      ><a name="4448" class="Symbol"
      >&#8594;</a
      ><a name="4449"
      > </a
      ><a name="4450" href="Maps.html#4427" class="Bound"
      >A</a
      ><a name="4451"
      > </a
      ><a name="4452" class="Symbol"
      >&#8594;</a
      ><a name="4453"
      > </a
      ><a name="4454" href="Maps.html#3757" class="Function"
      >TotalMap</a
      ><a name="4462"
      > </a
      ><a name="4463" href="Maps.html#4427" class="Bound"
      >A</a
      ><a name="4464"
      >
  </a
      ><a name="4467" class="Symbol"
      >(</a
      ><a name="4468" href="Maps.html#4468" class="Bound"
      >&#961;</a
      ><a name="4469"
      > </a
      ><a name="4470" href="Maps.html#4416" class="Function Operator"
      >,</a
      ><a name="4471"
      > </a
      ><a name="4472" href="Maps.html#4472" class="Bound"
      >x</a
      ><a name="4473"
      > </a
      ><a name="4474" href="Maps.html#4416" class="Function Operator"
      >&#8614;</a
      ><a name="4475"
      > </a
      ><a name="4476" href="Maps.html#4476" class="Bound"
      >v</a
      ><a name="4477" class="Symbol"
      >)</a
      ><a name="4478"
      > </a
      ><a name="4479" href="Maps.html#4479" class="Bound"
      >y</a
      ><a name="4480"
      > </a
      ><a name="4481" class="Keyword"
      >with</a
      ><a name="4485"
      > </a
      ><a name="4486" href="Maps.html#4472" class="Bound"
      >x</a
      ><a name="4487"
      > </a
      ><a name="4488" href="Maps.html#2558" class="Function Operator"
      >&#8799;</a
      ><a name="4489"
      > </a
      ><a name="4490" href="Maps.html#4479" class="Bound"
      >y</a
      ><a name="4491"
      >
  </a
      ><a name="4494" class="Symbol"
      >...</a
      ><a name="4497"
      > </a
      ><a name="4498" class="Symbol"
      >|</a
      ><a name="4499"
      > </a
      ><a name="4500" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#520" class="InductiveConstructor"
      >yes</a
      ><a name="4503"
      > </a
      ><a name="4504" href="Maps.html#4504" class="Bound"
      >x=y</a
      ><a name="4507"
      > </a
      ><a name="4508" class="Symbol"
      >=</a
      ><a name="4509"
      > </a
      ><a name="4510" href="Maps.html#4476" class="Bound"
      >v</a
      ><a name="4511"
      >
  </a
      ><a name="4514" class="Symbol"
      >...</a
      ><a name="4517"
      > </a
      ><a name="4518" class="Symbol"
      >|</a
      ><a name="4519"
      > </a
      ><a name="4520" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#547" class="InductiveConstructor"
      >no</a
      ><a name="4522"
      >  </a
      ><a name="4524" href="Maps.html#4524" class="Bound"
      >x&#8800;y</a
      ><a name="4527"
      > </a
      ><a name="4528" class="Symbol"
      >=</a
      ><a name="4529"
      > </a
      ><a name="4530" href="Maps.html#4468" class="Bound"
      >&#961;</a
      ><a name="4531"
      > </a
      ><a name="4532" href="Maps.html#4479" class="Bound"
      >y</a
      >

</pre>

This definition is a nice example of higher-order programming.
The update function takes a _function_ $$ρ$$ and yields a new
function that behaves like the desired map.

We define handy abbreviations for updating a map two, three, or four times.

<div class="note hidden">
Wen: you don't actually need to define these, you can simply declare `_,_↦_` to
be a left-associative infix operator with an `infixl` statement, and then you'll
be able to just evaluate `M , x ↦ y , z ↦ w` as `(M , x ↦ y) , z ↦ w`.
</div>

<pre class="Agda">

  <a name="5074" href="Maps.html#5074" class="Function Operator"
      >_,_&#8614;_,_&#8614;_</a
      ><a name="5083"
      > </a
      ><a name="5084" class="Symbol"
      >:</a
      ><a name="5085"
      > </a
      ><a name="5086" class="Symbol"
      >&#8704;</a
      ><a name="5087"
      > </a
      ><a name="5088" class="Symbol"
      >{</a
      ><a name="5089" href="Maps.html#5089" class="Bound"
      >A</a
      ><a name="5090" class="Symbol"
      >}</a
      ><a name="5091"
      > </a
      ><a name="5092" class="Symbol"
      >&#8594;</a
      ><a name="5093"
      > </a
      ><a name="5094" href="Maps.html#3757" class="Function"
      >TotalMap</a
      ><a name="5102"
      > </a
      ><a name="5103" href="Maps.html#5089" class="Bound"
      >A</a
      ><a name="5104"
      > </a
      ><a name="5105" class="Symbol"
      >&#8594;</a
      ><a name="5106"
      > </a
      ><a name="5107" href="Maps.html#2215" class="Datatype"
      >Id</a
      ><a name="5109"
      > </a
      ><a name="5110" class="Symbol"
      >&#8594;</a
      ><a name="5111"
      > </a
      ><a name="5112" href="Maps.html#5089" class="Bound"
      >A</a
      ><a name="5113"
      > </a
      ><a name="5114" class="Symbol"
      >&#8594;</a
      ><a name="5115"
      > </a
      ><a name="5116" href="Maps.html#2215" class="Datatype"
      >Id</a
      ><a name="5118"
      > </a
      ><a name="5119" class="Symbol"
      >&#8594;</a
      ><a name="5120"
      > </a
      ><a name="5121" href="Maps.html#5089" class="Bound"
      >A</a
      ><a name="5122"
      > </a
      ><a name="5123" class="Symbol"
      >&#8594;</a
      ><a name="5124"
      > </a
      ><a name="5125" href="Maps.html#3757" class="Function"
      >TotalMap</a
      ><a name="5133"
      > </a
      ><a name="5134" href="Maps.html#5089" class="Bound"
      >A</a
      ><a name="5135"
      >
  </a
      ><a name="5138" href="Maps.html#5138" class="Bound"
      >&#961;</a
      ><a name="5139"
      > </a
      ><a name="5140" href="Maps.html#5074" class="Function Operator"
      >,</a
      ><a name="5141"
      > </a
      ><a name="5142" href="Maps.html#5142" class="Bound"
      >x&#8321;</a
      ><a name="5144"
      > </a
      ><a name="5145" href="Maps.html#5074" class="Function Operator"
      >&#8614;</a
      ><a name="5146"
      > </a
      ><a name="5147" href="Maps.html#5147" class="Bound"
      >v&#8321;</a
      ><a name="5149"
      > </a
      ><a name="5150" href="Maps.html#5074" class="Function Operator"
      >,</a
      ><a name="5151"
      > </a
      ><a name="5152" href="Maps.html#5152" class="Bound"
      >x&#8322;</a
      ><a name="5154"
      > </a
      ><a name="5155" href="Maps.html#5074" class="Function Operator"
      >&#8614;</a
      ><a name="5156"
      > </a
      ><a name="5157" href="Maps.html#5157" class="Bound"
      >v&#8322;</a
      ><a name="5159"
      >  </a
      ><a name="5161" class="Symbol"
      >=</a
      ><a name="5162"
      >  </a
      ><a name="5164" class="Symbol"
      >(</a
      ><a name="5165" href="Maps.html#5138" class="Bound"
      >&#961;</a
      ><a name="5166"
      > </a
      ><a name="5167" href="Maps.html#4416" class="Function Operator"
      >,</a
      ><a name="5168"
      > </a
      ><a name="5169" href="Maps.html#5142" class="Bound"
      >x&#8321;</a
      ><a name="5171"
      > </a
      ><a name="5172" href="Maps.html#4416" class="Function Operator"
      >&#8614;</a
      ><a name="5173"
      > </a
      ><a name="5174" href="Maps.html#5147" class="Bound"
      >v&#8321;</a
      ><a name="5176" class="Symbol"
      >)</a
      ><a name="5177" href="Maps.html#4416" class="Function Operator"
      >,</a
      ><a name="5178"
      > </a
      ><a name="5179" href="Maps.html#5152" class="Bound"
      >x&#8322;</a
      ><a name="5181"
      > </a
      ><a name="5182" href="Maps.html#4416" class="Function Operator"
      >&#8614;</a
      ><a name="5183"
      > </a
      ><a name="5184" href="Maps.html#5157" class="Bound"
      >v&#8322;</a
      ><a name="5186"
      >

  </a
      ><a name="5190" href="Maps.html#5190" class="Function Operator"
      >_,_&#8614;_,_&#8614;_,_&#8614;_</a
      ><a name="5203"
      > </a
      ><a name="5204" class="Symbol"
      >:</a
      ><a name="5205"
      > </a
      ><a name="5206" class="Symbol"
      >&#8704;</a
      ><a name="5207"
      > </a
      ><a name="5208" class="Symbol"
      >{</a
      ><a name="5209" href="Maps.html#5209" class="Bound"
      >A</a
      ><a name="5210" class="Symbol"
      >}</a
      ><a name="5211"
      > </a
      ><a name="5212" class="Symbol"
      >&#8594;</a
      ><a name="5213"
      > </a
      ><a name="5214" href="Maps.html#3757" class="Function"
      >TotalMap</a
      ><a name="5222"
      > </a
      ><a name="5223" href="Maps.html#5209" class="Bound"
      >A</a
      ><a name="5224"
      > </a
      ><a name="5225" class="Symbol"
      >&#8594;</a
      ><a name="5226"
      > </a
      ><a name="5227" href="Maps.html#2215" class="Datatype"
      >Id</a
      ><a name="5229"
      > </a
      ><a name="5230" class="Symbol"
      >&#8594;</a
      ><a name="5231"
      > </a
      ><a name="5232" href="Maps.html#5209" class="Bound"
      >A</a
      ><a name="5233"
      > </a
      ><a name="5234" class="Symbol"
      >&#8594;</a
      ><a name="5235"
      > </a
      ><a name="5236" href="Maps.html#2215" class="Datatype"
      >Id</a
      ><a name="5238"
      > </a
      ><a name="5239" class="Symbol"
      >&#8594;</a
      ><a name="5240"
      > </a
      ><a name="5241" href="Maps.html#5209" class="Bound"
      >A</a
      ><a name="5242"
      > </a
      ><a name="5243" class="Symbol"
      >&#8594;</a
      ><a name="5244"
      > </a
      ><a name="5245" href="Maps.html#2215" class="Datatype"
      >Id</a
      ><a name="5247"
      > </a
      ><a name="5248" class="Symbol"
      >&#8594;</a
      ><a name="5249"
      > </a
      ><a name="5250" href="Maps.html#5209" class="Bound"
      >A</a
      ><a name="5251"
      > </a
      ><a name="5252" class="Symbol"
      >&#8594;</a
      ><a name="5253"
      > </a
      ><a name="5254" href="Maps.html#3757" class="Function"
      >TotalMap</a
      ><a name="5262"
      > </a
      ><a name="5263" href="Maps.html#5209" class="Bound"
      >A</a
      ><a name="5264"
      >
  </a
      ><a name="5267" href="Maps.html#5267" class="Bound"
      >&#961;</a
      ><a name="5268"
      > </a
      ><a name="5269" href="Maps.html#5190" class="Function Operator"
      >,</a
      ><a name="5270"
      > </a
      ><a name="5271" href="Maps.html#5271" class="Bound"
      >x&#8321;</a
      ><a name="5273"
      > </a
      ><a name="5274" href="Maps.html#5190" class="Function Operator"
      >&#8614;</a
      ><a name="5275"
      > </a
      ><a name="5276" href="Maps.html#5276" class="Bound"
      >v&#8321;</a
      ><a name="5278"
      > </a
      ><a name="5279" href="Maps.html#5190" class="Function Operator"
      >,</a
      ><a name="5280"
      > </a
      ><a name="5281" href="Maps.html#5281" class="Bound"
      >x&#8322;</a
      ><a name="5283"
      > </a
      ><a name="5284" href="Maps.html#5190" class="Function Operator"
      >&#8614;</a
      ><a name="5285"
      > </a
      ><a name="5286" href="Maps.html#5286" class="Bound"
      >v&#8322;</a
      ><a name="5288"
      > </a
      ><a name="5289" href="Maps.html#5190" class="Function Operator"
      >,</a
      ><a name="5290"
      > </a
      ><a name="5291" href="Maps.html#5291" class="Bound"
      >x&#8323;</a
      ><a name="5293"
      > </a
      ><a name="5294" href="Maps.html#5190" class="Function Operator"
      >&#8614;</a
      ><a name="5295"
      > </a
      ><a name="5296" href="Maps.html#5296" class="Bound"
      >v&#8323;</a
      ><a name="5298"
      >  </a
      ><a name="5300" class="Symbol"
      >=</a
      ><a name="5301"
      >  </a
      ><a name="5303" class="Symbol"
      >((</a
      ><a name="5305" href="Maps.html#5267" class="Bound"
      >&#961;</a
      ><a name="5306"
      > </a
      ><a name="5307" href="Maps.html#4416" class="Function Operator"
      >,</a
      ><a name="5308"
      > </a
      ><a name="5309" href="Maps.html#5271" class="Bound"
      >x&#8321;</a
      ><a name="5311"
      > </a
      ><a name="5312" href="Maps.html#4416" class="Function Operator"
      >&#8614;</a
      ><a name="5313"
      > </a
      ><a name="5314" href="Maps.html#5276" class="Bound"
      >v&#8321;</a
      ><a name="5316" class="Symbol"
      >)</a
      ><a name="5317" href="Maps.html#4416" class="Function Operator"
      >,</a
      ><a name="5318"
      > </a
      ><a name="5319" href="Maps.html#5281" class="Bound"
      >x&#8322;</a
      ><a name="5321"
      > </a
      ><a name="5322" href="Maps.html#4416" class="Function Operator"
      >&#8614;</a
      ><a name="5323"
      > </a
      ><a name="5324" href="Maps.html#5286" class="Bound"
      >v&#8322;</a
      ><a name="5326" class="Symbol"
      >)</a
      ><a name="5327" href="Maps.html#4416" class="Function Operator"
      >,</a
      ><a name="5328"
      > </a
      ><a name="5329" href="Maps.html#5291" class="Bound"
      >x&#8323;</a
      ><a name="5331"
      > </a
      ><a name="5332" href="Maps.html#4416" class="Function Operator"
      >&#8614;</a
      ><a name="5333"
      > </a
      ><a name="5334" href="Maps.html#5296" class="Bound"
      >v&#8323;</a
      ><a name="5336"
      >

  </a
      ><a name="5340" href="Maps.html#5340" class="Function Operator"
      >_,_&#8614;_,_&#8614;_,_&#8614;_,_&#8614;_</a
      ><a name="5357"
      > </a
      ><a name="5358" class="Symbol"
      >:</a
      ><a name="5359"
      > </a
      ><a name="5360" class="Symbol"
      >&#8704;</a
      ><a name="5361"
      > </a
      ><a name="5362" class="Symbol"
      >{</a
      ><a name="5363" href="Maps.html#5363" class="Bound"
      >A</a
      ><a name="5364" class="Symbol"
      >}</a
      ><a name="5365"
      > </a
      ><a name="5366" class="Symbol"
      >&#8594;</a
      ><a name="5367"
      > </a
      ><a name="5368" href="Maps.html#3757" class="Function"
      >TotalMap</a
      ><a name="5376"
      > </a
      ><a name="5377" href="Maps.html#5363" class="Bound"
      >A</a
      ><a name="5378"
      > </a
      ><a name="5379" class="Symbol"
      >&#8594;</a
      ><a name="5380"
      > </a
      ><a name="5381" href="Maps.html#2215" class="Datatype"
      >Id</a
      ><a name="5383"
      > </a
      ><a name="5384" class="Symbol"
      >&#8594;</a
      ><a name="5385"
      > </a
      ><a name="5386" href="Maps.html#5363" class="Bound"
      >A</a
      ><a name="5387"
      > </a
      ><a name="5388" class="Symbol"
      >&#8594;</a
      ><a name="5389"
      > </a
      ><a name="5390" href="Maps.html#2215" class="Datatype"
      >Id</a
      ><a name="5392"
      > </a
      ><a name="5393" class="Symbol"
      >&#8594;</a
      ><a name="5394"
      > </a
      ><a name="5395" href="Maps.html#5363" class="Bound"
      >A</a
      ><a name="5396"
      > </a
      ><a name="5397" class="Symbol"
      >&#8594;</a
      ><a name="5398"
      > </a
      ><a name="5399" href="Maps.html#2215" class="Datatype"
      >Id</a
      ><a name="5401"
      > </a
      ><a name="5402" class="Symbol"
      >&#8594;</a
      ><a name="5403"
      > </a
      ><a name="5404" href="Maps.html#5363" class="Bound"
      >A</a
      ><a name="5405"
      > </a
      ><a name="5406" class="Symbol"
      >&#8594;</a
      ><a name="5407"
      > </a
      ><a name="5408" href="Maps.html#2215" class="Datatype"
      >Id</a
      ><a name="5410"
      > </a
      ><a name="5411" class="Symbol"
      >&#8594;</a
      ><a name="5412"
      > </a
      ><a name="5413" href="Maps.html#5363" class="Bound"
      >A</a
      ><a name="5414"
      > </a
      ><a name="5415" class="Symbol"
      >&#8594;</a
      ><a name="5416"
      > </a
      ><a name="5417" href="Maps.html#3757" class="Function"
      >TotalMap</a
      ><a name="5425"
      > </a
      ><a name="5426" href="Maps.html#5363" class="Bound"
      >A</a
      ><a name="5427"
      >
  </a
      ><a name="5430" href="Maps.html#5430" class="Bound"
      >&#961;</a
      ><a name="5431"
      > </a
      ><a name="5432" href="Maps.html#5340" class="Function Operator"
      >,</a
      ><a name="5433"
      > </a
      ><a name="5434" href="Maps.html#5434" class="Bound"
      >x&#8321;</a
      ><a name="5436"
      > </a
      ><a name="5437" href="Maps.html#5340" class="Function Operator"
      >&#8614;</a
      ><a name="5438"
      > </a
      ><a name="5439" href="Maps.html#5439" class="Bound"
      >v&#8321;</a
      ><a name="5441"
      > </a
      ><a name="5442" href="Maps.html#5340" class="Function Operator"
      >,</a
      ><a name="5443"
      > </a
      ><a name="5444" href="Maps.html#5444" class="Bound"
      >x&#8322;</a
      ><a name="5446"
      > </a
      ><a name="5447" href="Maps.html#5340" class="Function Operator"
      >&#8614;</a
      ><a name="5448"
      > </a
      ><a name="5449" href="Maps.html#5449" class="Bound"
      >v&#8322;</a
      ><a name="5451"
      > </a
      ><a name="5452" href="Maps.html#5340" class="Function Operator"
      >,</a
      ><a name="5453"
      > </a
      ><a name="5454" href="Maps.html#5454" class="Bound"
      >x&#8323;</a
      ><a name="5456"
      > </a
      ><a name="5457" href="Maps.html#5340" class="Function Operator"
      >&#8614;</a
      ><a name="5458"
      > </a
      ><a name="5459" href="Maps.html#5459" class="Bound"
      >v&#8323;</a
      ><a name="5461"
      > </a
      ><a name="5462" href="Maps.html#5340" class="Function Operator"
      >,</a
      ><a name="5463"
      > </a
      ><a name="5464" href="Maps.html#5464" class="Bound"
      >x&#8324;</a
      ><a name="5466"
      > </a
      ><a name="5467" href="Maps.html#5340" class="Function Operator"
      >&#8614;</a
      ><a name="5468"
      > </a
      ><a name="5469" href="Maps.html#5469" class="Bound"
      >v&#8324;</a
      ><a name="5471"
      > </a
      ><a name="5472" class="Symbol"
      >=</a
      ><a name="5473"
      >  </a
      ><a name="5475" class="Symbol"
      >(((</a
      ><a name="5478" href="Maps.html#5430" class="Bound"
      >&#961;</a
      ><a name="5479"
      > </a
      ><a name="5480" href="Maps.html#4416" class="Function Operator"
      >,</a
      ><a name="5481"
      > </a
      ><a name="5482" href="Maps.html#5434" class="Bound"
      >x&#8321;</a
      ><a name="5484"
      > </a
      ><a name="5485" href="Maps.html#4416" class="Function Operator"
      >&#8614;</a
      ><a name="5486"
      > </a
      ><a name="5487" href="Maps.html#5439" class="Bound"
      >v&#8321;</a
      ><a name="5489" class="Symbol"
      >)</a
      ><a name="5490" href="Maps.html#4416" class="Function Operator"
      >,</a
      ><a name="5491"
      > </a
      ><a name="5492" href="Maps.html#5444" class="Bound"
      >x&#8322;</a
      ><a name="5494"
      > </a
      ><a name="5495" href="Maps.html#4416" class="Function Operator"
      >&#8614;</a
      ><a name="5496"
      > </a
      ><a name="5497" href="Maps.html#5449" class="Bound"
      >v&#8322;</a
      ><a name="5499" class="Symbol"
      >)</a
      ><a name="5500" href="Maps.html#4416" class="Function Operator"
      >,</a
      ><a name="5501"
      > </a
      ><a name="5502" href="Maps.html#5454" class="Bound"
      >x&#8323;</a
      ><a name="5504"
      > </a
      ><a name="5505" href="Maps.html#4416" class="Function Operator"
      >&#8614;</a
      ><a name="5506"
      > </a
      ><a name="5507" href="Maps.html#5459" class="Bound"
      >v&#8323;</a
      ><a name="5509" class="Symbol"
      >)</a
      ><a name="5510" href="Maps.html#4416" class="Function Operator"
      >,</a
      ><a name="5511"
      > </a
      ><a name="5512" href="Maps.html#5464" class="Bound"
      >x&#8324;</a
      ><a name="5514"
      > </a
      ><a name="5515" href="Maps.html#4416" class="Function Operator"
      >&#8614;</a
      ><a name="5516"
      > </a
      ><a name="5517" href="Maps.html#5469" class="Bound"
      >v&#8324;</a
      >

</pre>

For example, we can build a map taking ids to naturals, where $$x$$
maps to 42, $$y$$ maps to 69, and every other key maps to 0, as follows:

<pre class="Agda">

  <a name="5689" href="Maps.html#5689" class="Function"
      >&#961;&#8320;</a
      ><a name="5691"
      > </a
      ><a name="5692" class="Symbol"
      >:</a
      ><a name="5693"
      > </a
      ><a name="5694" href="Maps.html#3757" class="Function"
      >TotalMap</a
      ><a name="5702"
      > </a
      ><a name="5703" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#97" class="Datatype"
      >&#8469;</a
      ><a name="5704"
      >
  </a
      ><a name="5707" href="Maps.html#5689" class="Function"
      >&#961;&#8320;</a
      ><a name="5709"
      > </a
      ><a name="5710" class="Symbol"
      >=</a
      ><a name="5711"
      > </a
      ><a name="5712" href="Maps.html#4132" class="Function"
      >always</a
      ><a name="5718"
      > </a
      ><a name="5719" class="Number"
      >0</a
      ><a name="5720"
      > </a
      ><a name="5721" href="Maps.html#5074" class="Function Operator"
      >,</a
      ><a name="5722"
      > </a
      ><a name="5723" href="Maps.html#2863" class="Function"
      >x</a
      ><a name="5724"
      > </a
      ><a name="5725" href="Maps.html#5074" class="Function Operator"
      >&#8614;</a
      ><a name="5726"
      > </a
      ><a name="5727" class="Number"
      >42</a
      ><a name="5729"
      > </a
      ><a name="5730" href="Maps.html#5074" class="Function Operator"
      >,</a
      ><a name="5731"
      > </a
      ><a name="5732" href="Maps.html#2865" class="Function"
      >y</a
      ><a name="5733"
      > </a
      ><a name="5734" href="Maps.html#5074" class="Function Operator"
      >&#8614;</a
      ><a name="5735"
      > </a
      ><a name="5736" class="Number"
      >69</a
      >

</pre>

This completes the definition of total maps.  Note that we don't
need to define a `find` operation because it is just function
application!

<pre class="Agda">

  <a name="5907" href="Maps.html#5907" class="Function"
      >test&#8321;</a
      ><a name="5912"
      > </a
      ><a name="5913" class="Symbol"
      >:</a
      ><a name="5914"
      > </a
      ><a name="5915" href="Maps.html#5689" class="Function"
      >&#961;&#8320;</a
      ><a name="5917"
      > </a
      ><a name="5918" href="Maps.html#2863" class="Function"
      >x</a
      ><a name="5919"
      > </a
      ><a name="5920" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="5921"
      > </a
      ><a name="5922" class="Number"
      >42</a
      ><a name="5924"
      >
  </a
      ><a name="5927" href="Maps.html#5907" class="Function"
      >test&#8321;</a
      ><a name="5932"
      > </a
      ><a name="5933" class="Symbol"
      >=</a
      ><a name="5934"
      > </a
      ><a name="5935" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="5939"
      >

  </a
      ><a name="5943" href="Maps.html#5943" class="Function"
      >test&#8322;</a
      ><a name="5948"
      > </a
      ><a name="5949" class="Symbol"
      >:</a
      ><a name="5950"
      > </a
      ><a name="5951" href="Maps.html#5689" class="Function"
      >&#961;&#8320;</a
      ><a name="5953"
      > </a
      ><a name="5954" href="Maps.html#2865" class="Function"
      >y</a
      ><a name="5955"
      > </a
      ><a name="5956" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="5957"
      > </a
      ><a name="5958" class="Number"
      >69</a
      ><a name="5960"
      >
  </a
      ><a name="5963" href="Maps.html#5943" class="Function"
      >test&#8322;</a
      ><a name="5968"
      > </a
      ><a name="5969" class="Symbol"
      >=</a
      ><a name="5970"
      > </a
      ><a name="5971" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="5975"
      >

  </a
      ><a name="5979" href="Maps.html#5979" class="Function"
      >test&#8323;</a
      ><a name="5984"
      > </a
      ><a name="5985" class="Symbol"
      >:</a
      ><a name="5986"
      > </a
      ><a name="5987" href="Maps.html#5689" class="Function"
      >&#961;&#8320;</a
      ><a name="5989"
      > </a
      ><a name="5990" href="Maps.html#2867" class="Function"
      >z</a
      ><a name="5991"
      > </a
      ><a name="5992" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="5993"
      > </a
      ><a name="5994" class="Number"
      >0</a
      ><a name="5995"
      >
  </a
      ><a name="5998" href="Maps.html#5979" class="Function"
      >test&#8323;</a
      ><a name="6003"
      > </a
      ><a name="6004" class="Symbol"
      >=</a
      ><a name="6005"
      > </a
      ><a name="6006" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
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

  <a name="6341" class="Keyword"
      >postulate</a
      ><a name="6350"
      >
    </a
      ><a name="6355" href="Maps.html#6355" class="Postulate"
      >apply-always</a
      ><a name="6367"
      > </a
      ><a name="6368" class="Symbol"
      >:</a
      ><a name="6369"
      > </a
      ><a name="6370" class="Symbol"
      >&#8704;</a
      ><a name="6371"
      > </a
      ><a name="6372" class="Symbol"
      >{</a
      ><a name="6373" href="Maps.html#6373" class="Bound"
      >A</a
      ><a name="6374" class="Symbol"
      >}</a
      ><a name="6375"
      > </a
      ><a name="6376" class="Symbol"
      >(</a
      ><a name="6377" href="Maps.html#6377" class="Bound"
      >v</a
      ><a name="6378"
      > </a
      ><a name="6379" class="Symbol"
      >:</a
      ><a name="6380"
      > </a
      ><a name="6381" href="Maps.html#6373" class="Bound"
      >A</a
      ><a name="6382" class="Symbol"
      >)</a
      ><a name="6383"
      > </a
      ><a name="6384" class="Symbol"
      >(</a
      ><a name="6385" href="Maps.html#6385" class="Bound"
      >x</a
      ><a name="6386"
      > </a
      ><a name="6387" class="Symbol"
      >:</a
      ><a name="6388"
      > </a
      ><a name="6389" href="Maps.html#2215" class="Datatype"
      >Id</a
      ><a name="6391" class="Symbol"
      >)</a
      ><a name="6392"
      > </a
      ><a name="6393" class="Symbol"
      >&#8594;</a
      ><a name="6394"
      > </a
      ><a name="6395" href="Maps.html#4132" class="Function"
      >always</a
      ><a name="6401"
      > </a
      ><a name="6402" href="Maps.html#6377" class="Bound"
      >v</a
      ><a name="6403"
      > </a
      ><a name="6404" href="Maps.html#6385" class="Bound"
      >x</a
      ><a name="6405"
      > </a
      ><a name="6406" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="6407"
      > </a
      ><a name="6408" href="Maps.html#6377" class="Bound"
      >v</a
      >

</pre>

<div class="hidden">
<pre class="Agda">

  <a name="6458" href="Maps.html#6458" class="Function"
      >apply-always&#8242;</a
      ><a name="6471"
      > </a
      ><a name="6472" class="Symbol"
      >:</a
      ><a name="6473"
      > </a
      ><a name="6474" class="Symbol"
      >&#8704;</a
      ><a name="6475"
      > </a
      ><a name="6476" class="Symbol"
      >{</a
      ><a name="6477" href="Maps.html#6477" class="Bound"
      >A</a
      ><a name="6478" class="Symbol"
      >}</a
      ><a name="6479"
      > </a
      ><a name="6480" class="Symbol"
      >(</a
      ><a name="6481" href="Maps.html#6481" class="Bound"
      >v</a
      ><a name="6482"
      > </a
      ><a name="6483" class="Symbol"
      >:</a
      ><a name="6484"
      > </a
      ><a name="6485" href="Maps.html#6477" class="Bound"
      >A</a
      ><a name="6486" class="Symbol"
      >)</a
      ><a name="6487"
      > </a
      ><a name="6488" class="Symbol"
      >(</a
      ><a name="6489" href="Maps.html#6489" class="Bound"
      >x</a
      ><a name="6490"
      > </a
      ><a name="6491" class="Symbol"
      >:</a
      ><a name="6492"
      > </a
      ><a name="6493" href="Maps.html#2215" class="Datatype"
      >Id</a
      ><a name="6495" class="Symbol"
      >)</a
      ><a name="6496"
      > </a
      ><a name="6497" class="Symbol"
      >&#8594;</a
      ><a name="6498"
      > </a
      ><a name="6499" href="Maps.html#4132" class="Function"
      >always</a
      ><a name="6505"
      > </a
      ><a name="6506" href="Maps.html#6481" class="Bound"
      >v</a
      ><a name="6507"
      > </a
      ><a name="6508" href="Maps.html#6489" class="Bound"
      >x</a
      ><a name="6509"
      > </a
      ><a name="6510" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="6511"
      > </a
      ><a name="6512" href="Maps.html#6481" class="Bound"
      >v</a
      ><a name="6513"
      >
  </a
      ><a name="6516" href="Maps.html#6458" class="Function"
      >apply-always&#8242;</a
      ><a name="6529"
      > </a
      ><a name="6530" href="Maps.html#6530" class="Bound"
      >v</a
      ><a name="6531"
      > </a
      ><a name="6532" href="Maps.html#6532" class="Bound"
      >x</a
      ><a name="6533"
      > </a
      ><a name="6534" class="Symbol"
      >=</a
      ><a name="6535"
      > </a
      ><a name="6536" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      >

</pre>
</div>

#### Exercise: 2 stars, optional (update-eq)
Next, if we update a map $$ρ$$ at a key $$x$$ with a new value $$v$$
and then look up $$x$$ in the map resulting from the update, we get
back $$v$$:

<pre class="Agda">

  <a name="6770" class="Keyword"
      >postulate</a
      ><a name="6779"
      >
    </a
      ><a name="6784" href="Maps.html#6784" class="Postulate"
      >update-eq</a
      ><a name="6793"
      > </a
      ><a name="6794" class="Symbol"
      >:</a
      ><a name="6795"
      > </a
      ><a name="6796" class="Symbol"
      >&#8704;</a
      ><a name="6797"
      > </a
      ><a name="6798" class="Symbol"
      >{</a
      ><a name="6799" href="Maps.html#6799" class="Bound"
      >A</a
      ><a name="6800" class="Symbol"
      >}</a
      ><a name="6801"
      > </a
      ><a name="6802" class="Symbol"
      >(</a
      ><a name="6803" href="Maps.html#6803" class="Bound"
      >&#961;</a
      ><a name="6804"
      > </a
      ><a name="6805" class="Symbol"
      >:</a
      ><a name="6806"
      > </a
      ><a name="6807" href="Maps.html#3757" class="Function"
      >TotalMap</a
      ><a name="6815"
      > </a
      ><a name="6816" href="Maps.html#6799" class="Bound"
      >A</a
      ><a name="6817" class="Symbol"
      >)</a
      ><a name="6818"
      > </a
      ><a name="6819" class="Symbol"
      >(</a
      ><a name="6820" href="Maps.html#6820" class="Bound"
      >x</a
      ><a name="6821"
      > </a
      ><a name="6822" class="Symbol"
      >:</a
      ><a name="6823"
      > </a
      ><a name="6824" href="Maps.html#2215" class="Datatype"
      >Id</a
      ><a name="6826" class="Symbol"
      >)</a
      ><a name="6827"
      > </a
      ><a name="6828" class="Symbol"
      >(</a
      ><a name="6829" href="Maps.html#6829" class="Bound"
      >v</a
      ><a name="6830"
      > </a
      ><a name="6831" class="Symbol"
      >:</a
      ><a name="6832"
      > </a
      ><a name="6833" href="Maps.html#6799" class="Bound"
      >A</a
      ><a name="6834" class="Symbol"
      >)</a
      ><a name="6835"
      >
              </a
      ><a name="6850" class="Symbol"
      >&#8594;</a
      ><a name="6851"
      > </a
      ><a name="6852" class="Symbol"
      >(</a
      ><a name="6853" href="Maps.html#6803" class="Bound"
      >&#961;</a
      ><a name="6854"
      > </a
      ><a name="6855" href="Maps.html#4416" class="Function Operator"
      >,</a
      ><a name="6856"
      > </a
      ><a name="6857" href="Maps.html#6820" class="Bound"
      >x</a
      ><a name="6858"
      > </a
      ><a name="6859" href="Maps.html#4416" class="Function Operator"
      >&#8614;</a
      ><a name="6860"
      > </a
      ><a name="6861" href="Maps.html#6829" class="Bound"
      >v</a
      ><a name="6862" class="Symbol"
      >)</a
      ><a name="6863"
      > </a
      ><a name="6864" href="Maps.html#6820" class="Bound"
      >x</a
      ><a name="6865"
      > </a
      ><a name="6866" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="6867"
      > </a
      ><a name="6868" href="Maps.html#6829" class="Bound"
      >v</a
      >

</pre>

<div class="hidden">
<pre class="Agda">

  <a name="6918" href="Maps.html#6918" class="Function"
      >update-eq&#8242;</a
      ><a name="6928"
      > </a
      ><a name="6929" class="Symbol"
      >:</a
      ><a name="6930"
      > </a
      ><a name="6931" class="Symbol"
      >&#8704;</a
      ><a name="6932"
      > </a
      ><a name="6933" class="Symbol"
      >{</a
      ><a name="6934" href="Maps.html#6934" class="Bound"
      >A</a
      ><a name="6935" class="Symbol"
      >}</a
      ><a name="6936"
      > </a
      ><a name="6937" class="Symbol"
      >(</a
      ><a name="6938" href="Maps.html#6938" class="Bound"
      >&#961;</a
      ><a name="6939"
      > </a
      ><a name="6940" class="Symbol"
      >:</a
      ><a name="6941"
      > </a
      ><a name="6942" href="Maps.html#3757" class="Function"
      >TotalMap</a
      ><a name="6950"
      > </a
      ><a name="6951" href="Maps.html#6934" class="Bound"
      >A</a
      ><a name="6952" class="Symbol"
      >)</a
      ><a name="6953"
      > </a
      ><a name="6954" class="Symbol"
      >(</a
      ><a name="6955" href="Maps.html#6955" class="Bound"
      >x</a
      ><a name="6956"
      > </a
      ><a name="6957" class="Symbol"
      >:</a
      ><a name="6958"
      > </a
      ><a name="6959" href="Maps.html#2215" class="Datatype"
      >Id</a
      ><a name="6961" class="Symbol"
      >)</a
      ><a name="6962"
      > </a
      ><a name="6963" class="Symbol"
      >(</a
      ><a name="6964" href="Maps.html#6964" class="Bound"
      >v</a
      ><a name="6965"
      > </a
      ><a name="6966" class="Symbol"
      >:</a
      ><a name="6967"
      > </a
      ><a name="6968" href="Maps.html#6934" class="Bound"
      >A</a
      ><a name="6969" class="Symbol"
      >)</a
      ><a name="6970"
      >
             </a
      ><a name="6984" class="Symbol"
      >&#8594;</a
      ><a name="6985"
      > </a
      ><a name="6986" class="Symbol"
      >(</a
      ><a name="6987" href="Maps.html#6938" class="Bound"
      >&#961;</a
      ><a name="6988"
      > </a
      ><a name="6989" href="Maps.html#4416" class="Function Operator"
      >,</a
      ><a name="6990"
      > </a
      ><a name="6991" href="Maps.html#6955" class="Bound"
      >x</a
      ><a name="6992"
      > </a
      ><a name="6993" href="Maps.html#4416" class="Function Operator"
      >&#8614;</a
      ><a name="6994"
      > </a
      ><a name="6995" href="Maps.html#6964" class="Bound"
      >v</a
      ><a name="6996" class="Symbol"
      >)</a
      ><a name="6997"
      > </a
      ><a name="6998" href="Maps.html#6955" class="Bound"
      >x</a
      ><a name="6999"
      > </a
      ><a name="7000" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="7001"
      > </a
      ><a name="7002" href="Maps.html#6964" class="Bound"
      >v</a
      ><a name="7003"
      >
  </a
      ><a name="7006" href="Maps.html#6918" class="Function"
      >update-eq&#8242;</a
      ><a name="7016"
      > </a
      ><a name="7017" href="Maps.html#7017" class="Bound"
      >&#961;</a
      ><a name="7018"
      > </a
      ><a name="7019" href="Maps.html#7019" class="Bound"
      >x</a
      ><a name="7020"
      > </a
      ><a name="7021" href="Maps.html#7021" class="Bound"
      >v</a
      ><a name="7022"
      > </a
      ><a name="7023" class="Keyword"
      >with</a
      ><a name="7027"
      > </a
      ><a name="7028" href="Maps.html#7019" class="Bound"
      >x</a
      ><a name="7029"
      > </a
      ><a name="7030" href="Maps.html#2558" class="Function Operator"
      >&#8799;</a
      ><a name="7031"
      > </a
      ><a name="7032" href="Maps.html#7019" class="Bound"
      >x</a
      ><a name="7033"
      >
  </a
      ><a name="7036" class="Symbol"
      >...</a
      ><a name="7039"
      > </a
      ><a name="7040" class="Symbol"
      >|</a
      ><a name="7041"
      > </a
      ><a name="7042" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#520" class="InductiveConstructor"
      >yes</a
      ><a name="7045"
      > </a
      ><a name="7046" href="Maps.html#7046" class="Bound"
      >x&#8801;x</a
      ><a name="7049"
      > </a
      ><a name="7050" class="Symbol"
      >=</a
      ><a name="7051"
      > </a
      ><a name="7052" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="7056"
      >
  </a
      ><a name="7059" class="Symbol"
      >...</a
      ><a name="7062"
      > </a
      ><a name="7063" class="Symbol"
      >|</a
      ><a name="7064"
      > </a
      ><a name="7065" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#547" class="InductiveConstructor"
      >no</a
      ><a name="7067"
      >  </a
      ><a name="7069" href="Maps.html#7069" class="Bound"
      >x&#8802;x</a
      ><a name="7072"
      > </a
      ><a name="7073" class="Symbol"
      >=</a
      ><a name="7074"
      > </a
      ><a name="7075" href="https://agda.github.io/agda-stdlib/Data.Empty.html#360" class="Function"
      >&#8869;-elim</a
      ><a name="7081"
      > </a
      ><a name="7082" class="Symbol"
      >(</a
      ><a name="7083" href="Maps.html#7069" class="Bound"
      >x&#8802;x</a
      ><a name="7086"
      > </a
      ><a name="7087" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="7091" class="Symbol"
      >)</a
      >

</pre>
</div>

#### Exercise: 2 stars, optional (update-neq)
On the other hand, if we update a map $$m$$ at a key $$x$$ and
then look up a _different_ key $$y$$ in the resulting map, we get
the same result that $$m$$ would have given:

<pre class="Agda">

  <a name="7348" href="Maps.html#7348" class="Function"
      >update-neq</a
      ><a name="7358"
      > </a
      ><a name="7359" class="Symbol"
      >:</a
      ><a name="7360"
      > </a
      ><a name="7361" class="Symbol"
      >&#8704;</a
      ><a name="7362"
      > </a
      ><a name="7363" class="Symbol"
      >{</a
      ><a name="7364" href="Maps.html#7364" class="Bound"
      >A</a
      ><a name="7365" class="Symbol"
      >}</a
      ><a name="7366"
      > </a
      ><a name="7367" class="Symbol"
      >(</a
      ><a name="7368" href="Maps.html#7368" class="Bound"
      >&#961;</a
      ><a name="7369"
      > </a
      ><a name="7370" class="Symbol"
      >:</a
      ><a name="7371"
      > </a
      ><a name="7372" href="Maps.html#3757" class="Function"
      >TotalMap</a
      ><a name="7380"
      > </a
      ><a name="7381" href="Maps.html#7364" class="Bound"
      >A</a
      ><a name="7382" class="Symbol"
      >)</a
      ><a name="7383"
      > </a
      ><a name="7384" class="Symbol"
      >(</a
      ><a name="7385" href="Maps.html#7385" class="Bound"
      >x</a
      ><a name="7386"
      > </a
      ><a name="7387" class="Symbol"
      >:</a
      ><a name="7388"
      > </a
      ><a name="7389" href="Maps.html#2215" class="Datatype"
      >Id</a
      ><a name="7391" class="Symbol"
      >)</a
      ><a name="7392"
      > </a
      ><a name="7393" class="Symbol"
      >(</a
      ><a name="7394" href="Maps.html#7394" class="Bound"
      >v</a
      ><a name="7395"
      > </a
      ><a name="7396" class="Symbol"
      >:</a
      ><a name="7397"
      > </a
      ><a name="7398" href="Maps.html#7364" class="Bound"
      >A</a
      ><a name="7399" class="Symbol"
      >)</a
      ><a name="7400"
      > </a
      ><a name="7401" class="Symbol"
      >(</a
      ><a name="7402" href="Maps.html#7402" class="Bound"
      >y</a
      ><a name="7403"
      > </a
      ><a name="7404" class="Symbol"
      >:</a
      ><a name="7405"
      > </a
      ><a name="7406" href="Maps.html#2215" class="Datatype"
      >Id</a
      ><a name="7408" class="Symbol"
      >)</a
      ><a name="7409"
      >
             </a
      ><a name="7423" class="Symbol"
      >&#8594;</a
      ><a name="7424"
      > </a
      ><a name="7425" href="Maps.html#7385" class="Bound"
      >x</a
      ><a name="7426"
      > </a
      ><a name="7427" href="https://agda.github.io/agda-stdlib/Relation.Binary.Core.html#4493" class="Function Operator"
      >&#8802;</a
      ><a name="7428"
      > </a
      ><a name="7429" href="Maps.html#7402" class="Bound"
      >y</a
      ><a name="7430"
      > </a
      ><a name="7431" class="Symbol"
      >&#8594;</a
      ><a name="7432"
      > </a
      ><a name="7433" class="Symbol"
      >(</a
      ><a name="7434" href="Maps.html#7368" class="Bound"
      >&#961;</a
      ><a name="7435"
      > </a
      ><a name="7436" href="Maps.html#4416" class="Function Operator"
      >,</a
      ><a name="7437"
      > </a
      ><a name="7438" href="Maps.html#7385" class="Bound"
      >x</a
      ><a name="7439"
      > </a
      ><a name="7440" href="Maps.html#4416" class="Function Operator"
      >&#8614;</a
      ><a name="7441"
      > </a
      ><a name="7442" href="Maps.html#7394" class="Bound"
      >v</a
      ><a name="7443" class="Symbol"
      >)</a
      ><a name="7444"
      > </a
      ><a name="7445" href="Maps.html#7402" class="Bound"
      >y</a
      ><a name="7446"
      > </a
      ><a name="7447" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="7448"
      > </a
      ><a name="7449" href="Maps.html#7368" class="Bound"
      >&#961;</a
      ><a name="7450"
      > </a
      ><a name="7451" href="Maps.html#7402" class="Bound"
      >y</a
      ><a name="7452"
      >
  </a
      ><a name="7455" href="Maps.html#7348" class="Function"
      >update-neq</a
      ><a name="7465"
      > </a
      ><a name="7466" href="Maps.html#7466" class="Bound"
      >&#961;</a
      ><a name="7467"
      > </a
      ><a name="7468" href="Maps.html#7468" class="Bound"
      >x</a
      ><a name="7469"
      > </a
      ><a name="7470" href="Maps.html#7470" class="Bound"
      >v</a
      ><a name="7471"
      > </a
      ><a name="7472" href="Maps.html#7472" class="Bound"
      >y</a
      ><a name="7473"
      > </a
      ><a name="7474" href="Maps.html#7474" class="Bound"
      >x&#8802;y</a
      ><a name="7477"
      > </a
      ><a name="7478" class="Keyword"
      >with</a
      ><a name="7482"
      > </a
      ><a name="7483" href="Maps.html#7468" class="Bound"
      >x</a
      ><a name="7484"
      > </a
      ><a name="7485" href="Maps.html#2558" class="Function Operator"
      >&#8799;</a
      ><a name="7486"
      > </a
      ><a name="7487" href="Maps.html#7472" class="Bound"
      >y</a
      ><a name="7488"
      >
  </a
      ><a name="7491" class="Symbol"
      >...</a
      ><a name="7494"
      > </a
      ><a name="7495" class="Symbol"
      >|</a
      ><a name="7496"
      > </a
      ><a name="7497" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#520" class="InductiveConstructor"
      >yes</a
      ><a name="7500"
      > </a
      ><a name="7501" href="Maps.html#7501" class="Bound"
      >x&#8801;y</a
      ><a name="7504"
      > </a
      ><a name="7505" class="Symbol"
      >=</a
      ><a name="7506"
      > </a
      ><a name="7507" href="https://agda.github.io/agda-stdlib/Data.Empty.html#360" class="Function"
      >&#8869;-elim</a
      ><a name="7513"
      > </a
      ><a name="7514" class="Symbol"
      >(</a
      ><a name="7515" href="Maps.html#7474" class="Bound"
      >x&#8802;y</a
      ><a name="7518"
      > </a
      ><a name="7519" href="Maps.html#7501" class="Bound"
      >x&#8801;y</a
      ><a name="7522" class="Symbol"
      >)</a
      ><a name="7523"
      >
  </a
      ><a name="7526" class="Symbol"
      >...</a
      ><a name="7529"
      > </a
      ><a name="7530" class="Symbol"
      >|</a
      ><a name="7531"
      > </a
      ><a name="7532" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#547" class="InductiveConstructor"
      >no</a
      ><a name="7534"
      >  </a
      ><a name="7536" class="Symbol"
      >_</a
      ><a name="7537"
      >   </a
      ><a name="7540" class="Symbol"
      >=</a
      ><a name="7541"
      > </a
      ><a name="7542" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      >

</pre>

For the following lemmas, since maps are represented by functions, to
show two maps equal we will need to postulate extensionality.

<pre class="Agda">

  <a name="7707" class="Keyword"
      >postulate</a
      ><a name="7716"
      >
    </a
      ><a name="7721" href="Maps.html#7721" class="Postulate"
      >extensionality</a
      ><a name="7735"
      > </a
      ><a name="7736" class="Symbol"
      >:</a
      ><a name="7737"
      > </a
      ><a name="7738" class="Symbol"
      >&#8704;</a
      ><a name="7739"
      > </a
      ><a name="7740" class="Symbol"
      >{</a
      ><a name="7741" href="Maps.html#7741" class="Bound"
      >A</a
      ><a name="7742"
      > </a
      ><a name="7743" class="Symbol"
      >:</a
      ><a name="7744"
      > </a
      ><a name="7745" class="PrimitiveType"
      >Set</a
      ><a name="7748" class="Symbol"
      >}</a
      ><a name="7749"
      > </a
      ><a name="7750" class="Symbol"
      >{</a
      ><a name="7751" href="Maps.html#7751" class="Bound"
      >&#961;</a
      ><a name="7752"
      > </a
      ><a name="7753" href="Maps.html#7753" class="Bound"
      >&#961;&#8242;</a
      ><a name="7755"
      > </a
      ><a name="7756" class="Symbol"
      >:</a
      ><a name="7757"
      > </a
      ><a name="7758" href="Maps.html#3757" class="Function"
      >TotalMap</a
      ><a name="7766"
      > </a
      ><a name="7767" href="Maps.html#7741" class="Bound"
      >A</a
      ><a name="7768" class="Symbol"
      >}</a
      ><a name="7769"
      > </a
      ><a name="7770" class="Symbol"
      >&#8594;</a
      ><a name="7771"
      > </a
      ><a name="7772" class="Symbol"
      >(&#8704;</a
      ><a name="7774"
      > </a
      ><a name="7775" href="Maps.html#7775" class="Bound"
      >x</a
      ><a name="7776"
      > </a
      ><a name="7777" class="Symbol"
      >&#8594;</a
      ><a name="7778"
      > </a
      ><a name="7779" href="Maps.html#7751" class="Bound"
      >&#961;</a
      ><a name="7780"
      > </a
      ><a name="7781" href="Maps.html#7775" class="Bound"
      >x</a
      ><a name="7782"
      > </a
      ><a name="7783" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="7784"
      > </a
      ><a name="7785" href="Maps.html#7753" class="Bound"
      >&#961;&#8242;</a
      ><a name="7787"
      > </a
      ><a name="7788" href="Maps.html#7775" class="Bound"
      >x</a
      ><a name="7789" class="Symbol"
      >)</a
      ><a name="7790"
      > </a
      ><a name="7791" class="Symbol"
      >&#8594;</a
      ><a name="7792"
      > </a
      ><a name="7793" href="Maps.html#7751" class="Bound"
      >&#961;</a
      ><a name="7794"
      > </a
      ><a name="7795" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="7796"
      > </a
      ><a name="7797" href="Maps.html#7753" class="Bound"
      >&#961;&#8242;</a
      >

</pre>

#### Exercise: 2 stars, optional (update-shadow)
If we update a map $$ρ$$ at a key $$x$$ with a value $$v$$ and then
update again with the same key $$x$$ and another value $$w$$, the
resulting map behaves the same (gives the same result when applied
to any key) as the simpler map obtained by performing just
the second update on $$ρ$$:

<pre class="Agda">

  <a name="8165" class="Keyword"
      >postulate</a
      ><a name="8174"
      >
    </a
      ><a name="8179" href="Maps.html#8179" class="Postulate"
      >update-shadow</a
      ><a name="8192"
      > </a
      ><a name="8193" class="Symbol"
      >:</a
      ><a name="8194"
      > </a
      ><a name="8195" class="Symbol"
      >&#8704;</a
      ><a name="8196"
      > </a
      ><a name="8197" class="Symbol"
      >{</a
      ><a name="8198" href="Maps.html#8198" class="Bound"
      >A</a
      ><a name="8199" class="Symbol"
      >}</a
      ><a name="8200"
      > </a
      ><a name="8201" class="Symbol"
      >(</a
      ><a name="8202" href="Maps.html#8202" class="Bound"
      >&#961;</a
      ><a name="8203"
      > </a
      ><a name="8204" class="Symbol"
      >:</a
      ><a name="8205"
      > </a
      ><a name="8206" href="Maps.html#3757" class="Function"
      >TotalMap</a
      ><a name="8214"
      > </a
      ><a name="8215" href="Maps.html#8198" class="Bound"
      >A</a
      ><a name="8216" class="Symbol"
      >)</a
      ><a name="8217"
      > </a
      ><a name="8218" class="Symbol"
      >(</a
      ><a name="8219" href="Maps.html#8219" class="Bound"
      >x</a
      ><a name="8220"
      > </a
      ><a name="8221" class="Symbol"
      >:</a
      ><a name="8222"
      > </a
      ><a name="8223" href="Maps.html#2215" class="Datatype"
      >Id</a
      ><a name="8225" class="Symbol"
      >)</a
      ><a name="8226"
      > </a
      ><a name="8227" class="Symbol"
      >(</a
      ><a name="8228" href="Maps.html#8228" class="Bound"
      >v</a
      ><a name="8229"
      > </a
      ><a name="8230" href="Maps.html#8230" class="Bound"
      >w</a
      ><a name="8231"
      > </a
      ><a name="8232" class="Symbol"
      >:</a
      ><a name="8233"
      > </a
      ><a name="8234" href="Maps.html#8198" class="Bound"
      >A</a
      ><a name="8235" class="Symbol"
      >)</a
      ><a name="8236"
      > 
                  </a
      ><a name="8256" class="Symbol"
      >&#8594;</a
      ><a name="8257"
      > </a
      ><a name="8258" class="Symbol"
      >(</a
      ><a name="8259" href="Maps.html#8202" class="Bound"
      >&#961;</a
      ><a name="8260"
      > </a
      ><a name="8261" href="Maps.html#5074" class="Function Operator"
      >,</a
      ><a name="8262"
      > </a
      ><a name="8263" href="Maps.html#8219" class="Bound"
      >x</a
      ><a name="8264"
      > </a
      ><a name="8265" href="Maps.html#5074" class="Function Operator"
      >&#8614;</a
      ><a name="8266"
      > </a
      ><a name="8267" href="Maps.html#8228" class="Bound"
      >v</a
      ><a name="8268"
      > </a
      ><a name="8269" href="Maps.html#5074" class="Function Operator"
      >,</a
      ><a name="8270"
      > </a
      ><a name="8271" href="Maps.html#8219" class="Bound"
      >x</a
      ><a name="8272"
      > </a
      ><a name="8273" href="Maps.html#5074" class="Function Operator"
      >&#8614;</a
      ><a name="8274"
      > </a
      ><a name="8275" href="Maps.html#8230" class="Bound"
      >w</a
      ><a name="8276" class="Symbol"
      >)</a
      ><a name="8277"
      > </a
      ><a name="8278" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="8279"
      > </a
      ><a name="8280" class="Symbol"
      >(</a
      ><a name="8281" href="Maps.html#8202" class="Bound"
      >&#961;</a
      ><a name="8282"
      > </a
      ><a name="8283" href="Maps.html#4416" class="Function Operator"
      >,</a
      ><a name="8284"
      > </a
      ><a name="8285" href="Maps.html#8219" class="Bound"
      >x</a
      ><a name="8286"
      > </a
      ><a name="8287" href="Maps.html#4416" class="Function Operator"
      >&#8614;</a
      ><a name="8288"
      > </a
      ><a name="8289" href="Maps.html#8230" class="Bound"
      >w</a
      ><a name="8290" class="Symbol"
      >)</a
      >

</pre>

<div class="hidden">
<pre class="Agda">

  <a name="8340" href="Maps.html#8340" class="Function"
      >update-shadow&#8242;</a
      ><a name="8354"
      > </a
      ><a name="8355" class="Symbol"
      >:</a
      ><a name="8356"
      >  </a
      ><a name="8358" class="Symbol"
      >&#8704;</a
      ><a name="8359"
      > </a
      ><a name="8360" class="Symbol"
      >{</a
      ><a name="8361" href="Maps.html#8361" class="Bound"
      >A</a
      ><a name="8362" class="Symbol"
      >}</a
      ><a name="8363"
      > </a
      ><a name="8364" class="Symbol"
      >(</a
      ><a name="8365" href="Maps.html#8365" class="Bound"
      >&#961;</a
      ><a name="8366"
      > </a
      ><a name="8367" class="Symbol"
      >:</a
      ><a name="8368"
      > </a
      ><a name="8369" href="Maps.html#3757" class="Function"
      >TotalMap</a
      ><a name="8377"
      > </a
      ><a name="8378" href="Maps.html#8361" class="Bound"
      >A</a
      ><a name="8379" class="Symbol"
      >)</a
      ><a name="8380"
      > </a
      ><a name="8381" class="Symbol"
      >(</a
      ><a name="8382" href="Maps.html#8382" class="Bound"
      >x</a
      ><a name="8383"
      > </a
      ><a name="8384" class="Symbol"
      >:</a
      ><a name="8385"
      > </a
      ><a name="8386" href="Maps.html#2215" class="Datatype"
      >Id</a
      ><a name="8388" class="Symbol"
      >)</a
      ><a name="8389"
      > </a
      ><a name="8390" class="Symbol"
      >(</a
      ><a name="8391" href="Maps.html#8391" class="Bound"
      >v</a
      ><a name="8392"
      > </a
      ><a name="8393" href="Maps.html#8393" class="Bound"
      >w</a
      ><a name="8394"
      > </a
      ><a name="8395" class="Symbol"
      >:</a
      ><a name="8396"
      > </a
      ><a name="8397" href="Maps.html#8361" class="Bound"
      >A</a
      ><a name="8398" class="Symbol"
      >)</a
      ><a name="8399"
      > 
                  </a
      ><a name="8419" class="Symbol"
      >&#8594;</a
      ><a name="8420"
      > </a
      ><a name="8421" class="Symbol"
      >((</a
      ><a name="8423" href="Maps.html#8365" class="Bound"
      >&#961;</a
      ><a name="8424"
      > </a
      ><a name="8425" href="Maps.html#4416" class="Function Operator"
      >,</a
      ><a name="8426"
      > </a
      ><a name="8427" href="Maps.html#8382" class="Bound"
      >x</a
      ><a name="8428"
      > </a
      ><a name="8429" href="Maps.html#4416" class="Function Operator"
      >&#8614;</a
      ><a name="8430"
      > </a
      ><a name="8431" href="Maps.html#8391" class="Bound"
      >v</a
      ><a name="8432" class="Symbol"
      >)</a
      ><a name="8433"
      > </a
      ><a name="8434" href="Maps.html#4416" class="Function Operator"
      >,</a
      ><a name="8435"
      > </a
      ><a name="8436" href="Maps.html#8382" class="Bound"
      >x</a
      ><a name="8437"
      > </a
      ><a name="8438" href="Maps.html#4416" class="Function Operator"
      >&#8614;</a
      ><a name="8439"
      > </a
      ><a name="8440" href="Maps.html#8393" class="Bound"
      >w</a
      ><a name="8441" class="Symbol"
      >)</a
      ><a name="8442"
      > </a
      ><a name="8443" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="8444"
      > </a
      ><a name="8445" class="Symbol"
      >(</a
      ><a name="8446" href="Maps.html#8365" class="Bound"
      >&#961;</a
      ><a name="8447"
      > </a
      ><a name="8448" href="Maps.html#4416" class="Function Operator"
      >,</a
      ><a name="8449"
      > </a
      ><a name="8450" href="Maps.html#8382" class="Bound"
      >x</a
      ><a name="8451"
      > </a
      ><a name="8452" href="Maps.html#4416" class="Function Operator"
      >&#8614;</a
      ><a name="8453"
      > </a
      ><a name="8454" href="Maps.html#8393" class="Bound"
      >w</a
      ><a name="8455" class="Symbol"
      >)</a
      ><a name="8456"
      >
  </a
      ><a name="8459" href="Maps.html#8340" class="Function"
      >update-shadow&#8242;</a
      ><a name="8473"
      > </a
      ><a name="8474" href="Maps.html#8474" class="Bound"
      >&#961;</a
      ><a name="8475"
      > </a
      ><a name="8476" href="Maps.html#8476" class="Bound"
      >x</a
      ><a name="8477"
      > </a
      ><a name="8478" href="Maps.html#8478" class="Bound"
      >v</a
      ><a name="8479"
      > </a
      ><a name="8480" href="Maps.html#8480" class="Bound"
      >w</a
      ><a name="8481"
      > </a
      ><a name="8482" class="Symbol"
      >=</a
      ><a name="8483"
      > </a
      ><a name="8484" href="Maps.html#7721" class="Postulate"
      >extensionality</a
      ><a name="8498"
      > </a
      ><a name="8499" href="Maps.html#8519" class="Function"
      >lemma</a
      ><a name="8504"
      >
    </a
      ><a name="8509" class="Keyword"
      >where</a
      ><a name="8514"
      >
    </a
      ><a name="8519" href="Maps.html#8519" class="Function"
      >lemma</a
      ><a name="8524"
      > </a
      ><a name="8525" class="Symbol"
      >:</a
      ><a name="8526"
      > </a
      ><a name="8527" class="Symbol"
      >&#8704;</a
      ><a name="8528"
      > </a
      ><a name="8529" href="Maps.html#8529" class="Bound"
      >y</a
      ><a name="8530"
      > </a
      ><a name="8531" class="Symbol"
      >&#8594;</a
      ><a name="8532"
      > </a
      ><a name="8533" class="Symbol"
      >((</a
      ><a name="8535" href="Maps.html#8474" class="Bound"
      >&#961;</a
      ><a name="8536"
      > </a
      ><a name="8537" href="Maps.html#4416" class="Function Operator"
      >,</a
      ><a name="8538"
      > </a
      ><a name="8539" href="Maps.html#8476" class="Bound"
      >x</a
      ><a name="8540"
      > </a
      ><a name="8541" href="Maps.html#4416" class="Function Operator"
      >&#8614;</a
      ><a name="8542"
      > </a
      ><a name="8543" href="Maps.html#8478" class="Bound"
      >v</a
      ><a name="8544" class="Symbol"
      >)</a
      ><a name="8545"
      > </a
      ><a name="8546" href="Maps.html#4416" class="Function Operator"
      >,</a
      ><a name="8547"
      > </a
      ><a name="8548" href="Maps.html#8476" class="Bound"
      >x</a
      ><a name="8549"
      > </a
      ><a name="8550" href="Maps.html#4416" class="Function Operator"
      >&#8614;</a
      ><a name="8551"
      > </a
      ><a name="8552" href="Maps.html#8480" class="Bound"
      >w</a
      ><a name="8553" class="Symbol"
      >)</a
      ><a name="8554"
      > </a
      ><a name="8555" href="Maps.html#8529" class="Bound"
      >y</a
      ><a name="8556"
      > </a
      ><a name="8557" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="8558"
      > </a
      ><a name="8559" class="Symbol"
      >(</a
      ><a name="8560" href="Maps.html#8474" class="Bound"
      >&#961;</a
      ><a name="8561"
      > </a
      ><a name="8562" href="Maps.html#4416" class="Function Operator"
      >,</a
      ><a name="8563"
      > </a
      ><a name="8564" href="Maps.html#8476" class="Bound"
      >x</a
      ><a name="8565"
      > </a
      ><a name="8566" href="Maps.html#4416" class="Function Operator"
      >&#8614;</a
      ><a name="8567"
      > </a
      ><a name="8568" href="Maps.html#8480" class="Bound"
      >w</a
      ><a name="8569" class="Symbol"
      >)</a
      ><a name="8570"
      > </a
      ><a name="8571" href="Maps.html#8529" class="Bound"
      >y</a
      ><a name="8572"
      >
    </a
      ><a name="8577" href="Maps.html#8519" class="Function"
      >lemma</a
      ><a name="8582"
      > </a
      ><a name="8583" href="Maps.html#8583" class="Bound"
      >y</a
      ><a name="8584"
      > </a
      ><a name="8585" class="Keyword"
      >with</a
      ><a name="8589"
      > </a
      ><a name="8590" href="Maps.html#8476" class="Bound"
      >x</a
      ><a name="8591"
      > </a
      ><a name="8592" href="Maps.html#2558" class="Function Operator"
      >&#8799;</a
      ><a name="8593"
      > </a
      ><a name="8594" href="Maps.html#8583" class="Bound"
      >y</a
      ><a name="8595"
      >
    </a
      ><a name="8600" class="Symbol"
      >...</a
      ><a name="8603"
      > </a
      ><a name="8604" class="Symbol"
      >|</a
      ><a name="8605"
      > </a
      ><a name="8606" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#520" class="InductiveConstructor"
      >yes</a
      ><a name="8609"
      > </a
      ><a name="8610" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="8614"
      > </a
      ><a name="8615" class="Symbol"
      >=</a
      ><a name="8616"
      > </a
      ><a name="8617" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="8621"
      >
    </a
      ><a name="8626" class="Symbol"
      >...</a
      ><a name="8629"
      > </a
      ><a name="8630" class="Symbol"
      >|</a
      ><a name="8631"
      > </a
      ><a name="8632" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#547" class="InductiveConstructor"
      >no</a
      ><a name="8634"
      >  </a
      ><a name="8636" href="Maps.html#8636" class="Bound"
      >x&#8802;y</a
      ><a name="8639"
      >  </a
      ><a name="8641" class="Symbol"
      >=</a
      ><a name="8642"
      > </a
      ><a name="8643" href="Maps.html#7348" class="Function"
      >update-neq</a
      ><a name="8653"
      > </a
      ><a name="8654" href="Maps.html#8474" class="Bound"
      >&#961;</a
      ><a name="8655"
      > </a
      ><a name="8656" href="Maps.html#8476" class="Bound"
      >x</a
      ><a name="8657"
      > </a
      ><a name="8658" href="Maps.html#8478" class="Bound"
      >v</a
      ><a name="8659"
      > </a
      ><a name="8660" href="Maps.html#8583" class="Bound"
      >y</a
      ><a name="8661"
      > </a
      ><a name="8662" href="Maps.html#8636" class="Bound"
      >x&#8802;y</a
      >

</pre>
</div>

#### Exercise: 2 stars (update-same)
Prove the following theorem, which states that if we update a map $$ρ$$ to
assign key $$x$$ the same value as it already has in $$ρ$$, then the
result is equal to $$ρ$$:

<pre class="Agda">

  <a name="8908" class="Keyword"
      >postulate</a
      ><a name="8917"
      >
    </a
      ><a name="8922" href="Maps.html#8922" class="Postulate"
      >update-same</a
      ><a name="8933"
      > </a
      ><a name="8934" class="Symbol"
      >:</a
      ><a name="8935"
      > </a
      ><a name="8936" class="Symbol"
      >&#8704;</a
      ><a name="8937"
      > </a
      ><a name="8938" class="Symbol"
      >{</a
      ><a name="8939" href="Maps.html#8939" class="Bound"
      >A</a
      ><a name="8940" class="Symbol"
      >}</a
      ><a name="8941"
      > </a
      ><a name="8942" class="Symbol"
      >(</a
      ><a name="8943" href="Maps.html#8943" class="Bound"
      >&#961;</a
      ><a name="8944"
      > </a
      ><a name="8945" class="Symbol"
      >:</a
      ><a name="8946"
      > </a
      ><a name="8947" href="Maps.html#3757" class="Function"
      >TotalMap</a
      ><a name="8955"
      > </a
      ><a name="8956" href="Maps.html#8939" class="Bound"
      >A</a
      ><a name="8957" class="Symbol"
      >)</a
      ><a name="8958"
      > </a
      ><a name="8959" class="Symbol"
      >(</a
      ><a name="8960" href="Maps.html#8960" class="Bound"
      >x</a
      ><a name="8961"
      > </a
      ><a name="8962" class="Symbol"
      >:</a
      ><a name="8963"
      > </a
      ><a name="8964" href="Maps.html#2215" class="Datatype"
      >Id</a
      ><a name="8966" class="Symbol"
      >)</a
      ><a name="8967"
      > </a
      ><a name="8968" class="Symbol"
      >&#8594;</a
      ><a name="8969"
      > </a
      ><a name="8970" class="Symbol"
      >(</a
      ><a name="8971" href="Maps.html#8943" class="Bound"
      >&#961;</a
      ><a name="8972"
      > </a
      ><a name="8973" href="Maps.html#4416" class="Function Operator"
      >,</a
      ><a name="8974"
      > </a
      ><a name="8975" href="Maps.html#8960" class="Bound"
      >x</a
      ><a name="8976"
      > </a
      ><a name="8977" href="Maps.html#4416" class="Function Operator"
      >&#8614;</a
      ><a name="8978"
      > </a
      ><a name="8979" href="Maps.html#8943" class="Bound"
      >&#961;</a
      ><a name="8980"
      > </a
      ><a name="8981" href="Maps.html#8960" class="Bound"
      >x</a
      ><a name="8982" class="Symbol"
      >)</a
      ><a name="8983"
      > </a
      ><a name="8984" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="8985"
      > </a
      ><a name="8986" href="Maps.html#8943" class="Bound"
      >&#961;</a
      >

</pre>

<div class="hidden">
<pre class="Agda">

  <a name="9036" href="Maps.html#9036" class="Function"
      >update-same&#8242;</a
      ><a name="9048"
      > </a
      ><a name="9049" class="Symbol"
      >:</a
      ><a name="9050"
      > </a
      ><a name="9051" class="Symbol"
      >&#8704;</a
      ><a name="9052"
      > </a
      ><a name="9053" class="Symbol"
      >{</a
      ><a name="9054" href="Maps.html#9054" class="Bound"
      >A</a
      ><a name="9055" class="Symbol"
      >}</a
      ><a name="9056"
      > </a
      ><a name="9057" class="Symbol"
      >(</a
      ><a name="9058" href="Maps.html#9058" class="Bound"
      >&#961;</a
      ><a name="9059"
      > </a
      ><a name="9060" class="Symbol"
      >:</a
      ><a name="9061"
      > </a
      ><a name="9062" href="Maps.html#3757" class="Function"
      >TotalMap</a
      ><a name="9070"
      > </a
      ><a name="9071" href="Maps.html#9054" class="Bound"
      >A</a
      ><a name="9072" class="Symbol"
      >)</a
      ><a name="9073"
      > </a
      ><a name="9074" class="Symbol"
      >(</a
      ><a name="9075" href="Maps.html#9075" class="Bound"
      >x</a
      ><a name="9076"
      > </a
      ><a name="9077" class="Symbol"
      >:</a
      ><a name="9078"
      > </a
      ><a name="9079" href="Maps.html#2215" class="Datatype"
      >Id</a
      ><a name="9081" class="Symbol"
      >)</a
      ><a name="9082"
      > </a
      ><a name="9083" class="Symbol"
      >&#8594;</a
      ><a name="9084"
      > </a
      ><a name="9085" class="Symbol"
      >(</a
      ><a name="9086" href="Maps.html#9058" class="Bound"
      >&#961;</a
      ><a name="9087"
      > </a
      ><a name="9088" href="Maps.html#4416" class="Function Operator"
      >,</a
      ><a name="9089"
      > </a
      ><a name="9090" href="Maps.html#9075" class="Bound"
      >x</a
      ><a name="9091"
      > </a
      ><a name="9092" href="Maps.html#4416" class="Function Operator"
      >&#8614;</a
      ><a name="9093"
      > </a
      ><a name="9094" href="Maps.html#9058" class="Bound"
      >&#961;</a
      ><a name="9095"
      > </a
      ><a name="9096" href="Maps.html#9075" class="Bound"
      >x</a
      ><a name="9097" class="Symbol"
      >)</a
      ><a name="9098"
      > </a
      ><a name="9099" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="9100"
      > </a
      ><a name="9101" href="Maps.html#9058" class="Bound"
      >&#961;</a
      ><a name="9102"
      >
  </a
      ><a name="9105" href="Maps.html#9036" class="Function"
      >update-same&#8242;</a
      ><a name="9117"
      > </a
      ><a name="9118" href="Maps.html#9118" class="Bound"
      >&#961;</a
      ><a name="9119"
      > </a
      ><a name="9120" href="Maps.html#9120" class="Bound"
      >x</a
      ><a name="9121"
      >  </a
      ><a name="9123" class="Symbol"
      >=</a
      ><a name="9124"
      >  </a
      ><a name="9126" href="Maps.html#7721" class="Postulate"
      >extensionality</a
      ><a name="9140"
      > </a
      ><a name="9141" href="Maps.html#9161" class="Function"
      >lemma</a
      ><a name="9146"
      >
    </a
      ><a name="9151" class="Keyword"
      >where</a
      ><a name="9156"
      >
    </a
      ><a name="9161" href="Maps.html#9161" class="Function"
      >lemma</a
      ><a name="9166"
      > </a
      ><a name="9167" class="Symbol"
      >:</a
      ><a name="9168"
      > </a
      ><a name="9169" class="Symbol"
      >&#8704;</a
      ><a name="9170"
      > </a
      ><a name="9171" href="Maps.html#9171" class="Bound"
      >y</a
      ><a name="9172"
      > </a
      ><a name="9173" class="Symbol"
      >&#8594;</a
      ><a name="9174"
      > </a
      ><a name="9175" class="Symbol"
      >(</a
      ><a name="9176" href="Maps.html#9118" class="Bound"
      >&#961;</a
      ><a name="9177"
      > </a
      ><a name="9178" href="Maps.html#4416" class="Function Operator"
      >,</a
      ><a name="9179"
      > </a
      ><a name="9180" href="Maps.html#9120" class="Bound"
      >x</a
      ><a name="9181"
      > </a
      ><a name="9182" href="Maps.html#4416" class="Function Operator"
      >&#8614;</a
      ><a name="9183"
      > </a
      ><a name="9184" href="Maps.html#9118" class="Bound"
      >&#961;</a
      ><a name="9185"
      > </a
      ><a name="9186" href="Maps.html#9120" class="Bound"
      >x</a
      ><a name="9187" class="Symbol"
      >)</a
      ><a name="9188"
      > </a
      ><a name="9189" href="Maps.html#9171" class="Bound"
      >y</a
      ><a name="9190"
      > </a
      ><a name="9191" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="9192"
      > </a
      ><a name="9193" href="Maps.html#9118" class="Bound"
      >&#961;</a
      ><a name="9194"
      > </a
      ><a name="9195" href="Maps.html#9171" class="Bound"
      >y</a
      ><a name="9196"
      >
    </a
      ><a name="9201" href="Maps.html#9161" class="Function"
      >lemma</a
      ><a name="9206"
      > </a
      ><a name="9207" href="Maps.html#9207" class="Bound"
      >y</a
      ><a name="9208"
      > </a
      ><a name="9209" class="Keyword"
      >with</a
      ><a name="9213"
      > </a
      ><a name="9214" href="Maps.html#9120" class="Bound"
      >x</a
      ><a name="9215"
      > </a
      ><a name="9216" href="Maps.html#2558" class="Function Operator"
      >&#8799;</a
      ><a name="9217"
      > </a
      ><a name="9218" href="Maps.html#9207" class="Bound"
      >y</a
      ><a name="9219"
      >
    </a
      ><a name="9224" class="Symbol"
      >...</a
      ><a name="9227"
      > </a
      ><a name="9228" class="Symbol"
      >|</a
      ><a name="9229"
      > </a
      ><a name="9230" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#520" class="InductiveConstructor"
      >yes</a
      ><a name="9233"
      > </a
      ><a name="9234" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="9238"
      > </a
      ><a name="9239" class="Symbol"
      >=</a
      ><a name="9240"
      > </a
      ><a name="9241" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="9245"
      >
    </a
      ><a name="9250" class="Symbol"
      >...</a
      ><a name="9253"
      > </a
      ><a name="9254" class="Symbol"
      >|</a
      ><a name="9255"
      > </a
      ><a name="9256" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#547" class="InductiveConstructor"
      >no</a
      ><a name="9258"
      >  </a
      ><a name="9260" href="Maps.html#9260" class="Bound"
      >x&#8802;y</a
      ><a name="9263"
      >  </a
      ><a name="9265" class="Symbol"
      >=</a
      ><a name="9266"
      > </a
      ><a name="9267" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      >

</pre>
</div>

#### Exercise: 3 stars, recommended (update-permute)
Prove one final property of the `update` function: If we update a map
$$m$$ at two distinct keys, it doesn't matter in which order we do the
updates.

<pre class="Agda">

  <a name="9510" class="Keyword"
      >postulate</a
      ><a name="9519"
      >
    </a
      ><a name="9524" href="Maps.html#9524" class="Postulate"
      >update-permute</a
      ><a name="9538"
      > </a
      ><a name="9539" class="Symbol"
      >:</a
      ><a name="9540"
      > </a
      ><a name="9541" class="Symbol"
      >&#8704;</a
      ><a name="9542"
      > </a
      ><a name="9543" class="Symbol"
      >{</a
      ><a name="9544" href="Maps.html#9544" class="Bound"
      >A</a
      ><a name="9545" class="Symbol"
      >}</a
      ><a name="9546"
      > </a
      ><a name="9547" class="Symbol"
      >(</a
      ><a name="9548" href="Maps.html#9548" class="Bound"
      >&#961;</a
      ><a name="9549"
      > </a
      ><a name="9550" class="Symbol"
      >:</a
      ><a name="9551"
      > </a
      ><a name="9552" href="Maps.html#3757" class="Function"
      >TotalMap</a
      ><a name="9560"
      > </a
      ><a name="9561" href="Maps.html#9544" class="Bound"
      >A</a
      ><a name="9562" class="Symbol"
      >)</a
      ><a name="9563"
      > </a
      ><a name="9564" class="Symbol"
      >(</a
      ><a name="9565" href="Maps.html#9565" class="Bound"
      >x</a
      ><a name="9566"
      > </a
      ><a name="9567" class="Symbol"
      >:</a
      ><a name="9568"
      > </a
      ><a name="9569" href="Maps.html#2215" class="Datatype"
      >Id</a
      ><a name="9571" class="Symbol"
      >)</a
      ><a name="9572"
      > </a
      ><a name="9573" class="Symbol"
      >(</a
      ><a name="9574" href="Maps.html#9574" class="Bound"
      >v</a
      ><a name="9575"
      > </a
      ><a name="9576" class="Symbol"
      >:</a
      ><a name="9577"
      > </a
      ><a name="9578" href="Maps.html#9544" class="Bound"
      >A</a
      ><a name="9579" class="Symbol"
      >)</a
      ><a name="9580"
      > </a
      ><a name="9581" class="Symbol"
      >(</a
      ><a name="9582" href="Maps.html#9582" class="Bound"
      >y</a
      ><a name="9583"
      > </a
      ><a name="9584" class="Symbol"
      >:</a
      ><a name="9585"
      > </a
      ><a name="9586" href="Maps.html#2215" class="Datatype"
      >Id</a
      ><a name="9588" class="Symbol"
      >)</a
      ><a name="9589"
      > </a
      ><a name="9590" class="Symbol"
      >(</a
      ><a name="9591" href="Maps.html#9591" class="Bound"
      >w</a
      ><a name="9592"
      > </a
      ><a name="9593" class="Symbol"
      >:</a
      ><a name="9594"
      > </a
      ><a name="9595" href="Maps.html#9544" class="Bound"
      >A</a
      ><a name="9596" class="Symbol"
      >)</a
      ><a name="9597"
      >
                   </a
      ><a name="9617" class="Symbol"
      >&#8594;</a
      ><a name="9618"
      > </a
      ><a name="9619" href="Maps.html#9565" class="Bound"
      >x</a
      ><a name="9620"
      > </a
      ><a name="9621" href="https://agda.github.io/agda-stdlib/Relation.Binary.Core.html#4493" class="Function Operator"
      >&#8802;</a
      ><a name="9622"
      > </a
      ><a name="9623" href="Maps.html#9582" class="Bound"
      >y</a
      ><a name="9624"
      > </a
      ><a name="9625" class="Symbol"
      >&#8594;</a
      ><a name="9626"
      > </a
      ><a name="9627" class="Symbol"
      >(</a
      ><a name="9628" href="Maps.html#9548" class="Bound"
      >&#961;</a
      ><a name="9629"
      > </a
      ><a name="9630" href="Maps.html#5074" class="Function Operator"
      >,</a
      ><a name="9631"
      > </a
      ><a name="9632" href="Maps.html#9565" class="Bound"
      >x</a
      ><a name="9633"
      > </a
      ><a name="9634" href="Maps.html#5074" class="Function Operator"
      >&#8614;</a
      ><a name="9635"
      > </a
      ><a name="9636" href="Maps.html#9574" class="Bound"
      >v</a
      ><a name="9637"
      > </a
      ><a name="9638" href="Maps.html#5074" class="Function Operator"
      >,</a
      ><a name="9639"
      > </a
      ><a name="9640" href="Maps.html#9582" class="Bound"
      >y</a
      ><a name="9641"
      > </a
      ><a name="9642" href="Maps.html#5074" class="Function Operator"
      >&#8614;</a
      ><a name="9643"
      > </a
      ><a name="9644" href="Maps.html#9591" class="Bound"
      >w</a
      ><a name="9645" class="Symbol"
      >)</a
      ><a name="9646"
      > </a
      ><a name="9647" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="9648"
      > </a
      ><a name="9649" class="Symbol"
      >(</a
      ><a name="9650" href="Maps.html#9548" class="Bound"
      >&#961;</a
      ><a name="9651"
      > </a
      ><a name="9652" href="Maps.html#5074" class="Function Operator"
      >,</a
      ><a name="9653"
      > </a
      ><a name="9654" href="Maps.html#9582" class="Bound"
      >y</a
      ><a name="9655"
      > </a
      ><a name="9656" href="Maps.html#5074" class="Function Operator"
      >&#8614;</a
      ><a name="9657"
      > </a
      ><a name="9658" href="Maps.html#9591" class="Bound"
      >w</a
      ><a name="9659"
      > </a
      ><a name="9660" href="Maps.html#5074" class="Function Operator"
      >,</a
      ><a name="9661"
      > </a
      ><a name="9662" href="Maps.html#9565" class="Bound"
      >x</a
      ><a name="9663"
      > </a
      ><a name="9664" href="Maps.html#5074" class="Function Operator"
      >&#8614;</a
      ><a name="9665"
      > </a
      ><a name="9666" href="Maps.html#9574" class="Bound"
      >v</a
      ><a name="9667" class="Symbol"
      >)</a
      >

</pre>

<div class="hidden">
<pre class="Agda">

  <a name="9717" href="Maps.html#9717" class="Function"
      >update-permute&#8242;</a
      ><a name="9732"
      > </a
      ><a name="9733" class="Symbol"
      >:</a
      ><a name="9734"
      > </a
      ><a name="9735" class="Symbol"
      >&#8704;</a
      ><a name="9736"
      > </a
      ><a name="9737" class="Symbol"
      >{</a
      ><a name="9738" href="Maps.html#9738" class="Bound"
      >A</a
      ><a name="9739" class="Symbol"
      >}</a
      ><a name="9740"
      > </a
      ><a name="9741" class="Symbol"
      >(</a
      ><a name="9742" href="Maps.html#9742" class="Bound"
      >&#961;</a
      ><a name="9743"
      > </a
      ><a name="9744" class="Symbol"
      >:</a
      ><a name="9745"
      > </a
      ><a name="9746" href="Maps.html#3757" class="Function"
      >TotalMap</a
      ><a name="9754"
      > </a
      ><a name="9755" href="Maps.html#9738" class="Bound"
      >A</a
      ><a name="9756" class="Symbol"
      >)</a
      ><a name="9757"
      > </a
      ><a name="9758" class="Symbol"
      >(</a
      ><a name="9759" href="Maps.html#9759" class="Bound"
      >x</a
      ><a name="9760"
      > </a
      ><a name="9761" class="Symbol"
      >:</a
      ><a name="9762"
      > </a
      ><a name="9763" href="Maps.html#2215" class="Datatype"
      >Id</a
      ><a name="9765" class="Symbol"
      >)</a
      ><a name="9766"
      > </a
      ><a name="9767" class="Symbol"
      >(</a
      ><a name="9768" href="Maps.html#9768" class="Bound"
      >v</a
      ><a name="9769"
      > </a
      ><a name="9770" class="Symbol"
      >:</a
      ><a name="9771"
      > </a
      ><a name="9772" href="Maps.html#9738" class="Bound"
      >A</a
      ><a name="9773" class="Symbol"
      >)</a
      ><a name="9774"
      > </a
      ><a name="9775" class="Symbol"
      >(</a
      ><a name="9776" href="Maps.html#9776" class="Bound"
      >y</a
      ><a name="9777"
      > </a
      ><a name="9778" class="Symbol"
      >:</a
      ><a name="9779"
      > </a
      ><a name="9780" href="Maps.html#2215" class="Datatype"
      >Id</a
      ><a name="9782" class="Symbol"
      >)</a
      ><a name="9783"
      > </a
      ><a name="9784" class="Symbol"
      >(</a
      ><a name="9785" href="Maps.html#9785" class="Bound"
      >w</a
      ><a name="9786"
      > </a
      ><a name="9787" class="Symbol"
      >:</a
      ><a name="9788"
      > </a
      ><a name="9789" href="Maps.html#9738" class="Bound"
      >A</a
      ><a name="9790" class="Symbol"
      >)</a
      ><a name="9791"
      >
                   </a
      ><a name="9811" class="Symbol"
      >&#8594;</a
      ><a name="9812"
      > </a
      ><a name="9813" href="Maps.html#9759" class="Bound"
      >x</a
      ><a name="9814"
      > </a
      ><a name="9815" href="https://agda.github.io/agda-stdlib/Relation.Binary.Core.html#4493" class="Function Operator"
      >&#8802;</a
      ><a name="9816"
      > </a
      ><a name="9817" href="Maps.html#9776" class="Bound"
      >y</a
      ><a name="9818"
      > </a
      ><a name="9819" class="Symbol"
      >&#8594;</a
      ><a name="9820"
      > </a
      ><a name="9821" class="Symbol"
      >(</a
      ><a name="9822" href="Maps.html#9742" class="Bound"
      >&#961;</a
      ><a name="9823"
      > </a
      ><a name="9824" href="Maps.html#5074" class="Function Operator"
      >,</a
      ><a name="9825"
      > </a
      ><a name="9826" href="Maps.html#9759" class="Bound"
      >x</a
      ><a name="9827"
      > </a
      ><a name="9828" href="Maps.html#5074" class="Function Operator"
      >&#8614;</a
      ><a name="9829"
      > </a
      ><a name="9830" href="Maps.html#9768" class="Bound"
      >v</a
      ><a name="9831"
      > </a
      ><a name="9832" href="Maps.html#5074" class="Function Operator"
      >,</a
      ><a name="9833"
      > </a
      ><a name="9834" href="Maps.html#9776" class="Bound"
      >y</a
      ><a name="9835"
      > </a
      ><a name="9836" href="Maps.html#5074" class="Function Operator"
      >&#8614;</a
      ><a name="9837"
      > </a
      ><a name="9838" href="Maps.html#9785" class="Bound"
      >w</a
      ><a name="9839" class="Symbol"
      >)</a
      ><a name="9840"
      > </a
      ><a name="9841" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="9842"
      > </a
      ><a name="9843" class="Symbol"
      >(</a
      ><a name="9844" href="Maps.html#9742" class="Bound"
      >&#961;</a
      ><a name="9845"
      > </a
      ><a name="9846" href="Maps.html#5074" class="Function Operator"
      >,</a
      ><a name="9847"
      > </a
      ><a name="9848" href="Maps.html#9776" class="Bound"
      >y</a
      ><a name="9849"
      > </a
      ><a name="9850" href="Maps.html#5074" class="Function Operator"
      >&#8614;</a
      ><a name="9851"
      > </a
      ><a name="9852" href="Maps.html#9785" class="Bound"
      >w</a
      ><a name="9853"
      > </a
      ><a name="9854" href="Maps.html#5074" class="Function Operator"
      >,</a
      ><a name="9855"
      > </a
      ><a name="9856" href="Maps.html#9759" class="Bound"
      >x</a
      ><a name="9857"
      > </a
      ><a name="9858" href="Maps.html#5074" class="Function Operator"
      >&#8614;</a
      ><a name="9859"
      > </a
      ><a name="9860" href="Maps.html#9768" class="Bound"
      >v</a
      ><a name="9861" class="Symbol"
      >)</a
      ><a name="9862"
      >
  </a
      ><a name="9865" href="Maps.html#9717" class="Function"
      >update-permute&#8242;</a
      ><a name="9880"
      > </a
      ><a name="9881" class="Symbol"
      >{</a
      ><a name="9882" href="Maps.html#9882" class="Bound"
      >A</a
      ><a name="9883" class="Symbol"
      >}</a
      ><a name="9884"
      > </a
      ><a name="9885" href="Maps.html#9885" class="Bound"
      >&#961;</a
      ><a name="9886"
      > </a
      ><a name="9887" href="Maps.html#9887" class="Bound"
      >x</a
      ><a name="9888"
      > </a
      ><a name="9889" href="Maps.html#9889" class="Bound"
      >v</a
      ><a name="9890"
      > </a
      ><a name="9891" href="Maps.html#9891" class="Bound"
      >y</a
      ><a name="9892"
      > </a
      ><a name="9893" href="Maps.html#9893" class="Bound"
      >w</a
      ><a name="9894"
      > </a
      ><a name="9895" href="Maps.html#9895" class="Bound"
      >x&#8802;y</a
      ><a name="9898"
      >  </a
      ><a name="9900" class="Symbol"
      >=</a
      ><a name="9901"
      >  </a
      ><a name="9903" href="Maps.html#7721" class="Postulate"
      >extensionality</a
      ><a name="9917"
      > </a
      ><a name="9918" href="Maps.html#9938" class="Function"
      >lemma</a
      ><a name="9923"
      >
    </a
      ><a name="9928" class="Keyword"
      >where</a
      ><a name="9933"
      >
    </a
      ><a name="9938" href="Maps.html#9938" class="Function"
      >lemma</a
      ><a name="9943"
      > </a
      ><a name="9944" class="Symbol"
      >:</a
      ><a name="9945"
      > </a
      ><a name="9946" class="Symbol"
      >&#8704;</a
      ><a name="9947"
      > </a
      ><a name="9948" href="Maps.html#9948" class="Bound"
      >z</a
      ><a name="9949"
      > </a
      ><a name="9950" class="Symbol"
      >&#8594;</a
      ><a name="9951"
      > </a
      ><a name="9952" class="Symbol"
      >(</a
      ><a name="9953" href="Maps.html#9885" class="Bound"
      >&#961;</a
      ><a name="9954"
      > </a
      ><a name="9955" href="Maps.html#5074" class="Function Operator"
      >,</a
      ><a name="9956"
      > </a
      ><a name="9957" href="Maps.html#9887" class="Bound"
      >x</a
      ><a name="9958"
      > </a
      ><a name="9959" href="Maps.html#5074" class="Function Operator"
      >&#8614;</a
      ><a name="9960"
      > </a
      ><a name="9961" href="Maps.html#9889" class="Bound"
      >v</a
      ><a name="9962"
      > </a
      ><a name="9963" href="Maps.html#5074" class="Function Operator"
      >,</a
      ><a name="9964"
      > </a
      ><a name="9965" href="Maps.html#9891" class="Bound"
      >y</a
      ><a name="9966"
      > </a
      ><a name="9967" href="Maps.html#5074" class="Function Operator"
      >&#8614;</a
      ><a name="9968"
      > </a
      ><a name="9969" href="Maps.html#9893" class="Bound"
      >w</a
      ><a name="9970" class="Symbol"
      >)</a
      ><a name="9971"
      > </a
      ><a name="9972" href="Maps.html#9948" class="Bound"
      >z</a
      ><a name="9973"
      > </a
      ><a name="9974" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="9975"
      > </a
      ><a name="9976" class="Symbol"
      >(</a
      ><a name="9977" href="Maps.html#9885" class="Bound"
      >&#961;</a
      ><a name="9978"
      > </a
      ><a name="9979" href="Maps.html#5074" class="Function Operator"
      >,</a
      ><a name="9980"
      > </a
      ><a name="9981" href="Maps.html#9891" class="Bound"
      >y</a
      ><a name="9982"
      > </a
      ><a name="9983" href="Maps.html#5074" class="Function Operator"
      >&#8614;</a
      ><a name="9984"
      > </a
      ><a name="9985" href="Maps.html#9893" class="Bound"
      >w</a
      ><a name="9986"
      > </a
      ><a name="9987" href="Maps.html#5074" class="Function Operator"
      >,</a
      ><a name="9988"
      > </a
      ><a name="9989" href="Maps.html#9887" class="Bound"
      >x</a
      ><a name="9990"
      > </a
      ><a name="9991" href="Maps.html#5074" class="Function Operator"
      >&#8614;</a
      ><a name="9992"
      > </a
      ><a name="9993" href="Maps.html#9889" class="Bound"
      >v</a
      ><a name="9994" class="Symbol"
      >)</a
      ><a name="9995"
      > </a
      ><a name="9996" href="Maps.html#9948" class="Bound"
      >z</a
      ><a name="9997"
      >
    </a
      ><a name="10002" href="Maps.html#9938" class="Function"
      >lemma</a
      ><a name="10007"
      > </a
      ><a name="10008" href="Maps.html#10008" class="Bound"
      >z</a
      ><a name="10009"
      > </a
      ><a name="10010" class="Keyword"
      >with</a
      ><a name="10014"
      > </a
      ><a name="10015" href="Maps.html#9887" class="Bound"
      >x</a
      ><a name="10016"
      > </a
      ><a name="10017" href="Maps.html#2558" class="Function Operator"
      >&#8799;</a
      ><a name="10018"
      > </a
      ><a name="10019" href="Maps.html#10008" class="Bound"
      >z</a
      ><a name="10020"
      > </a
      ><a name="10021" class="Symbol"
      >|</a
      ><a name="10022"
      > </a
      ><a name="10023" href="Maps.html#9891" class="Bound"
      >y</a
      ><a name="10024"
      > </a
      ><a name="10025" href="Maps.html#2558" class="Function Operator"
      >&#8799;</a
      ><a name="10026"
      > </a
      ><a name="10027" href="Maps.html#10008" class="Bound"
      >z</a
      ><a name="10028"
      >
    </a
      ><a name="10033" class="Symbol"
      >...</a
      ><a name="10036"
      > </a
      ><a name="10037" class="Symbol"
      >|</a
      ><a name="10038"
      > </a
      ><a name="10039" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#520" class="InductiveConstructor"
      >yes</a
      ><a name="10042"
      > </a
      ><a name="10043" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="10047"
      > </a
      ><a name="10048" class="Symbol"
      >|</a
      ><a name="10049"
      > </a
      ><a name="10050" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#520" class="InductiveConstructor"
      >yes</a
      ><a name="10053"
      > </a
      ><a name="10054" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="10058"
      >  </a
      ><a name="10060" class="Symbol"
      >=</a
      ><a name="10061"
      >  </a
      ><a name="10063" href="https://agda.github.io/agda-stdlib/Data.Empty.html#360" class="Function"
      >&#8869;-elim</a
      ><a name="10069"
      > </a
      ><a name="10070" class="Symbol"
      >(</a
      ><a name="10071" href="Maps.html#9895" class="Bound"
      >x&#8802;y</a
      ><a name="10074"
      > </a
      ><a name="10075" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="10079" class="Symbol"
      >)</a
      ><a name="10080"
      >
    </a
      ><a name="10085" class="Symbol"
      >...</a
      ><a name="10088"
      > </a
      ><a name="10089" class="Symbol"
      >|</a
      ><a name="10090"
      > </a
      ><a name="10091" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#547" class="InductiveConstructor"
      >no</a
      ><a name="10093"
      >  </a
      ><a name="10095" href="Maps.html#10095" class="Bound"
      >x&#8802;z</a
      ><a name="10098"
      >  </a
      ><a name="10100" class="Symbol"
      >|</a
      ><a name="10101"
      > </a
      ><a name="10102" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#520" class="InductiveConstructor"
      >yes</a
      ><a name="10105"
      > </a
      ><a name="10106" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="10110"
      >  </a
      ><a name="10112" class="Symbol"
      >=</a
      ><a name="10113"
      >  </a
      ><a name="10115" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.Core.html#565" class="Function"
      >sym</a
      ><a name="10118"
      > </a
      ><a name="10119" class="Symbol"
      >(</a
      ><a name="10120" href="Maps.html#6918" class="Function"
      >update-eq&#8242;</a
      ><a name="10130"
      > </a
      ><a name="10131" href="Maps.html#9885" class="Bound"
      >&#961;</a
      ><a name="10132"
      > </a
      ><a name="10133" href="Maps.html#10008" class="Bound"
      >z</a
      ><a name="10134"
      > </a
      ><a name="10135" href="Maps.html#9893" class="Bound"
      >w</a
      ><a name="10136" class="Symbol"
      >)</a
      ><a name="10137"
      >
    </a
      ><a name="10142" class="Symbol"
      >...</a
      ><a name="10145"
      > </a
      ><a name="10146" class="Symbol"
      >|</a
      ><a name="10147"
      > </a
      ><a name="10148" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#520" class="InductiveConstructor"
      >yes</a
      ><a name="10151"
      > </a
      ><a name="10152" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="10156"
      > </a
      ><a name="10157" class="Symbol"
      >|</a
      ><a name="10158"
      > </a
      ><a name="10159" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#547" class="InductiveConstructor"
      >no</a
      ><a name="10161"
      >  </a
      ><a name="10163" href="Maps.html#10163" class="Bound"
      >y&#8802;z</a
      ><a name="10166"
      >   </a
      ><a name="10169" class="Symbol"
      >=</a
      ><a name="10170"
      >  </a
      ><a name="10172" href="Maps.html#6918" class="Function"
      >update-eq&#8242;</a
      ><a name="10182"
      > </a
      ><a name="10183" href="Maps.html#9885" class="Bound"
      >&#961;</a
      ><a name="10184"
      > </a
      ><a name="10185" href="Maps.html#10008" class="Bound"
      >z</a
      ><a name="10186"
      > </a
      ><a name="10187" href="Maps.html#9889" class="Bound"
      >v</a
      ><a name="10188"
      >
    </a
      ><a name="10193" class="Symbol"
      >...</a
      ><a name="10196"
      > </a
      ><a name="10197" class="Symbol"
      >|</a
      ><a name="10198"
      > </a
      ><a name="10199" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#547" class="InductiveConstructor"
      >no</a
      ><a name="10201"
      >  </a
      ><a name="10203" href="Maps.html#10203" class="Bound"
      >x&#8802;z</a
      ><a name="10206"
      >  </a
      ><a name="10208" class="Symbol"
      >|</a
      ><a name="10209"
      > </a
      ><a name="10210" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#547" class="InductiveConstructor"
      >no</a
      ><a name="10212"
      >  </a
      ><a name="10214" href="Maps.html#10214" class="Bound"
      >y&#8802;z</a
      ><a name="10217"
      >   </a
      ><a name="10220" class="Symbol"
      >=</a
      ><a name="10221"
      >  </a
      ><a name="10223" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.Core.html#632" class="Function"
      >trans</a
      ><a name="10228"
      > </a
      ><a name="10229" class="Symbol"
      >(</a
      ><a name="10230" href="Maps.html#7348" class="Function"
      >update-neq</a
      ><a name="10240"
      > </a
      ><a name="10241" href="Maps.html#9885" class="Bound"
      >&#961;</a
      ><a name="10242"
      > </a
      ><a name="10243" href="Maps.html#9887" class="Bound"
      >x</a
      ><a name="10244"
      > </a
      ><a name="10245" href="Maps.html#9889" class="Bound"
      >v</a
      ><a name="10246"
      > </a
      ><a name="10247" href="Maps.html#10008" class="Bound"
      >z</a
      ><a name="10248"
      > </a
      ><a name="10249" href="Maps.html#10203" class="Bound"
      >x&#8802;z</a
      ><a name="10252" class="Symbol"
      >)</a
      ><a name="10253"
      > </a
      ><a name="10254" class="Symbol"
      >(</a
      ><a name="10255" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.Core.html#565" class="Function"
      >sym</a
      ><a name="10258"
      > </a
      ><a name="10259" class="Symbol"
      >(</a
      ><a name="10260" href="Maps.html#7348" class="Function"
      >update-neq</a
      ><a name="10270"
      > </a
      ><a name="10271" href="Maps.html#9885" class="Bound"
      >&#961;</a
      ><a name="10272"
      > </a
      ><a name="10273" href="Maps.html#9891" class="Bound"
      >y</a
      ><a name="10274"
      > </a
      ><a name="10275" href="Maps.html#9893" class="Bound"
      >w</a
      ><a name="10276"
      > </a
      ><a name="10277" href="Maps.html#10008" class="Bound"
      >z</a
      ><a name="10278"
      > </a
      ><a name="10279" href="Maps.html#10214" class="Bound"
      >y&#8802;z</a
      ><a name="10282" class="Symbol"
      >))</a
      >

</pre>

And a slightly different version of the same proof.

<pre class="Agda">

  <a name="10369" href="Maps.html#10369" class="Function"
      >update-permute&#8242;&#8242;</a
      ><a name="10385"
      > </a
      ><a name="10386" class="Symbol"
      >:</a
      ><a name="10387"
      > </a
      ><a name="10388" class="Symbol"
      >&#8704;</a
      ><a name="10389"
      > </a
      ><a name="10390" class="Symbol"
      >{</a
      ><a name="10391" href="Maps.html#10391" class="Bound"
      >A</a
      ><a name="10392" class="Symbol"
      >}</a
      ><a name="10393"
      > </a
      ><a name="10394" class="Symbol"
      >(</a
      ><a name="10395" href="Maps.html#10395" class="Bound"
      >&#961;</a
      ><a name="10396"
      > </a
      ><a name="10397" class="Symbol"
      >:</a
      ><a name="10398"
      > </a
      ><a name="10399" href="Maps.html#3757" class="Function"
      >TotalMap</a
      ><a name="10407"
      > </a
      ><a name="10408" href="Maps.html#10391" class="Bound"
      >A</a
      ><a name="10409" class="Symbol"
      >)</a
      ><a name="10410"
      > </a
      ><a name="10411" class="Symbol"
      >(</a
      ><a name="10412" href="Maps.html#10412" class="Bound"
      >x</a
      ><a name="10413"
      > </a
      ><a name="10414" class="Symbol"
      >:</a
      ><a name="10415"
      > </a
      ><a name="10416" href="Maps.html#2215" class="Datatype"
      >Id</a
      ><a name="10418" class="Symbol"
      >)</a
      ><a name="10419"
      > </a
      ><a name="10420" class="Symbol"
      >(</a
      ><a name="10421" href="Maps.html#10421" class="Bound"
      >v</a
      ><a name="10422"
      > </a
      ><a name="10423" class="Symbol"
      >:</a
      ><a name="10424"
      > </a
      ><a name="10425" href="Maps.html#10391" class="Bound"
      >A</a
      ><a name="10426" class="Symbol"
      >)</a
      ><a name="10427"
      > </a
      ><a name="10428" class="Symbol"
      >(</a
      ><a name="10429" href="Maps.html#10429" class="Bound"
      >y</a
      ><a name="10430"
      > </a
      ><a name="10431" class="Symbol"
      >:</a
      ><a name="10432"
      > </a
      ><a name="10433" href="Maps.html#2215" class="Datatype"
      >Id</a
      ><a name="10435" class="Symbol"
      >)</a
      ><a name="10436"
      > </a
      ><a name="10437" class="Symbol"
      >(</a
      ><a name="10438" href="Maps.html#10438" class="Bound"
      >w</a
      ><a name="10439"
      > </a
      ><a name="10440" class="Symbol"
      >:</a
      ><a name="10441"
      > </a
      ><a name="10442" href="Maps.html#10391" class="Bound"
      >A</a
      ><a name="10443" class="Symbol"
      >)</a
      ><a name="10444"
      > </a
      ><a name="10445" class="Symbol"
      >(</a
      ><a name="10446" href="Maps.html#10446" class="Bound"
      >z</a
      ><a name="10447"
      > </a
      ><a name="10448" class="Symbol"
      >:</a
      ><a name="10449"
      > </a
      ><a name="10450" href="Maps.html#2215" class="Datatype"
      >Id</a
      ><a name="10452" class="Symbol"
      >)</a
      ><a name="10453"
      >
                   </a
      ><a name="10473" class="Symbol"
      >&#8594;</a
      ><a name="10474"
      > </a
      ><a name="10475" href="Maps.html#10412" class="Bound"
      >x</a
      ><a name="10476"
      > </a
      ><a name="10477" href="https://agda.github.io/agda-stdlib/Relation.Binary.Core.html#4493" class="Function Operator"
      >&#8802;</a
      ><a name="10478"
      > </a
      ><a name="10479" href="Maps.html#10429" class="Bound"
      >y</a
      ><a name="10480"
      > </a
      ><a name="10481" class="Symbol"
      >&#8594;</a
      ><a name="10482"
      > </a
      ><a name="10483" class="Symbol"
      >(</a
      ><a name="10484" href="Maps.html#10395" class="Bound"
      >&#961;</a
      ><a name="10485"
      > </a
      ><a name="10486" href="Maps.html#5074" class="Function Operator"
      >,</a
      ><a name="10487"
      > </a
      ><a name="10488" href="Maps.html#10412" class="Bound"
      >x</a
      ><a name="10489"
      > </a
      ><a name="10490" href="Maps.html#5074" class="Function Operator"
      >&#8614;</a
      ><a name="10491"
      > </a
      ><a name="10492" href="Maps.html#10421" class="Bound"
      >v</a
      ><a name="10493"
      > </a
      ><a name="10494" href="Maps.html#5074" class="Function Operator"
      >,</a
      ><a name="10495"
      > </a
      ><a name="10496" href="Maps.html#10429" class="Bound"
      >y</a
      ><a name="10497"
      > </a
      ><a name="10498" href="Maps.html#5074" class="Function Operator"
      >&#8614;</a
      ><a name="10499"
      > </a
      ><a name="10500" href="Maps.html#10438" class="Bound"
      >w</a
      ><a name="10501" class="Symbol"
      >)</a
      ><a name="10502"
      > </a
      ><a name="10503" href="Maps.html#10446" class="Bound"
      >z</a
      ><a name="10504"
      > </a
      ><a name="10505" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="10506"
      > </a
      ><a name="10507" class="Symbol"
      >(</a
      ><a name="10508" href="Maps.html#10395" class="Bound"
      >&#961;</a
      ><a name="10509"
      > </a
      ><a name="10510" href="Maps.html#5074" class="Function Operator"
      >,</a
      ><a name="10511"
      > </a
      ><a name="10512" href="Maps.html#10429" class="Bound"
      >y</a
      ><a name="10513"
      > </a
      ><a name="10514" href="Maps.html#5074" class="Function Operator"
      >&#8614;</a
      ><a name="10515"
      > </a
      ><a name="10516" href="Maps.html#10438" class="Bound"
      >w</a
      ><a name="10517"
      > </a
      ><a name="10518" href="Maps.html#5074" class="Function Operator"
      >,</a
      ><a name="10519"
      > </a
      ><a name="10520" href="Maps.html#10412" class="Bound"
      >x</a
      ><a name="10521"
      > </a
      ><a name="10522" href="Maps.html#5074" class="Function Operator"
      >&#8614;</a
      ><a name="10523"
      > </a
      ><a name="10524" href="Maps.html#10421" class="Bound"
      >v</a
      ><a name="10525" class="Symbol"
      >)</a
      ><a name="10526"
      > </a
      ><a name="10527" href="Maps.html#10446" class="Bound"
      >z</a
      ><a name="10528"
      >
  </a
      ><a name="10531" href="Maps.html#10369" class="Function"
      >update-permute&#8242;&#8242;</a
      ><a name="10547"
      > </a
      ><a name="10548" class="Symbol"
      >{</a
      ><a name="10549" href="Maps.html#10549" class="Bound"
      >A</a
      ><a name="10550" class="Symbol"
      >}</a
      ><a name="10551"
      > </a
      ><a name="10552" href="Maps.html#10552" class="Bound"
      >&#961;</a
      ><a name="10553"
      > </a
      ><a name="10554" href="Maps.html#10554" class="Bound"
      >x</a
      ><a name="10555"
      > </a
      ><a name="10556" href="Maps.html#10556" class="Bound"
      >v</a
      ><a name="10557"
      > </a
      ><a name="10558" href="Maps.html#10558" class="Bound"
      >y</a
      ><a name="10559"
      > </a
      ><a name="10560" href="Maps.html#10560" class="Bound"
      >w</a
      ><a name="10561"
      > </a
      ><a name="10562" href="Maps.html#10562" class="Bound"
      >z</a
      ><a name="10563"
      > </a
      ><a name="10564" href="Maps.html#10564" class="Bound"
      >x&#8802;y</a
      ><a name="10567"
      > </a
      ><a name="10568" class="Keyword"
      >with</a
      ><a name="10572"
      > </a
      ><a name="10573" href="Maps.html#10554" class="Bound"
      >x</a
      ><a name="10574"
      > </a
      ><a name="10575" href="Maps.html#2558" class="Function Operator"
      >&#8799;</a
      ><a name="10576"
      > </a
      ><a name="10577" href="Maps.html#10562" class="Bound"
      >z</a
      ><a name="10578"
      > </a
      ><a name="10579" class="Symbol"
      >|</a
      ><a name="10580"
      > </a
      ><a name="10581" href="Maps.html#10558" class="Bound"
      >y</a
      ><a name="10582"
      > </a
      ><a name="10583" href="Maps.html#2558" class="Function Operator"
      >&#8799;</a
      ><a name="10584"
      > </a
      ><a name="10585" href="Maps.html#10562" class="Bound"
      >z</a
      ><a name="10586"
      >
  </a
      ><a name="10589" class="Symbol"
      >...</a
      ><a name="10592"
      > </a
      ><a name="10593" class="Symbol"
      >|</a
      ><a name="10594"
      > </a
      ><a name="10595" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#520" class="InductiveConstructor"
      >yes</a
      ><a name="10598"
      > </a
      ><a name="10599" href="Maps.html#10599" class="Bound"
      >x&#8801;z</a
      ><a name="10602"
      > </a
      ><a name="10603" class="Symbol"
      >|</a
      ><a name="10604"
      > </a
      ><a name="10605" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#520" class="InductiveConstructor"
      >yes</a
      ><a name="10608"
      > </a
      ><a name="10609" href="Maps.html#10609" class="Bound"
      >y&#8801;z</a
      ><a name="10612"
      > </a
      ><a name="10613" class="Symbol"
      >=</a
      ><a name="10614"
      > </a
      ><a name="10615" href="https://agda.github.io/agda-stdlib/Data.Empty.html#360" class="Function"
      >&#8869;-elim</a
      ><a name="10621"
      > </a
      ><a name="10622" class="Symbol"
      >(</a
      ><a name="10623" href="Maps.html#10564" class="Bound"
      >x&#8802;y</a
      ><a name="10626"
      > </a
      ><a name="10627" class="Symbol"
      >(</a
      ><a name="10628" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.Core.html#632" class="Function"
      >trans</a
      ><a name="10633"
      > </a
      ><a name="10634" href="Maps.html#10599" class="Bound"
      >x&#8801;z</a
      ><a name="10637"
      > </a
      ><a name="10638" class="Symbol"
      >(</a
      ><a name="10639" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.Core.html#565" class="Function"
      >sym</a
      ><a name="10642"
      > </a
      ><a name="10643" href="Maps.html#10609" class="Bound"
      >y&#8801;z</a
      ><a name="10646" class="Symbol"
      >)))</a
      ><a name="10649"
      >
  </a
      ><a name="10652" class="Symbol"
      >...</a
      ><a name="10655"
      > </a
      ><a name="10656" class="Symbol"
      >|</a
      ><a name="10657"
      > </a
      ><a name="10658" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#547" class="InductiveConstructor"
      >no</a
      ><a name="10660"
      >  </a
      ><a name="10662" href="Maps.html#10662" class="Bound"
      >x&#8802;z</a
      ><a name="10665"
      > </a
      ><a name="10666" class="Symbol"
      >|</a
      ><a name="10667"
      > </a
      ><a name="10668" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#520" class="InductiveConstructor"
      >yes</a
      ><a name="10671"
      > </a
      ><a name="10672" href="Maps.html#10672" class="Bound"
      >y&#8801;z</a
      ><a name="10675"
      > </a
      ><a name="10676" class="Keyword"
      >rewrite</a
      ><a name="10683"
      > </a
      ><a name="10684" href="Maps.html#10672" class="Bound"
      >y&#8801;z</a
      ><a name="10687"
      >  </a
      ><a name="10689" class="Symbol"
      >=</a
      ><a name="10690"
      >  </a
      ><a name="10692" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.Core.html#565" class="Function"
      >sym</a
      ><a name="10695"
      > </a
      ><a name="10696" class="Symbol"
      >(</a
      ><a name="10697" href="Maps.html#6918" class="Function"
      >update-eq&#8242;</a
      ><a name="10707"
      > </a
      ><a name="10708" href="Maps.html#10552" class="Bound"
      >&#961;</a
      ><a name="10709"
      > </a
      ><a name="10710" href="Maps.html#10562" class="Bound"
      >z</a
      ><a name="10711"
      > </a
      ><a name="10712" href="Maps.html#10560" class="Bound"
      >w</a
      ><a name="10713" class="Symbol"
      >)</a
      ><a name="10714"
      >  
  </a
      ><a name="10719" class="Symbol"
      >...</a
      ><a name="10722"
      > </a
      ><a name="10723" class="Symbol"
      >|</a
      ><a name="10724"
      > </a
      ><a name="10725" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#520" class="InductiveConstructor"
      >yes</a
      ><a name="10728"
      > </a
      ><a name="10729" href="Maps.html#10729" class="Bound"
      >x&#8801;z</a
      ><a name="10732"
      > </a
      ><a name="10733" class="Symbol"
      >|</a
      ><a name="10734"
      > </a
      ><a name="10735" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#547" class="InductiveConstructor"
      >no</a
      ><a name="10737"
      >  </a
      ><a name="10739" href="Maps.html#10739" class="Bound"
      >y&#8802;z</a
      ><a name="10742"
      > </a
      ><a name="10743" class="Keyword"
      >rewrite</a
      ><a name="10750"
      > </a
      ><a name="10751" href="Maps.html#10729" class="Bound"
      >x&#8801;z</a
      ><a name="10754"
      >  </a
      ><a name="10756" class="Symbol"
      >=</a
      ><a name="10757"
      >  </a
      ><a name="10759" href="Maps.html#6918" class="Function"
      >update-eq&#8242;</a
      ><a name="10769"
      > </a
      ><a name="10770" href="Maps.html#10552" class="Bound"
      >&#961;</a
      ><a name="10771"
      > </a
      ><a name="10772" href="Maps.html#10562" class="Bound"
      >z</a
      ><a name="10773"
      > </a
      ><a name="10774" href="Maps.html#10556" class="Bound"
      >v</a
      ><a name="10775"
      >
  </a
      ><a name="10778" class="Symbol"
      >...</a
      ><a name="10781"
      > </a
      ><a name="10782" class="Symbol"
      >|</a
      ><a name="10783"
      > </a
      ><a name="10784" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#547" class="InductiveConstructor"
      >no</a
      ><a name="10786"
      >  </a
      ><a name="10788" href="Maps.html#10788" class="Bound"
      >x&#8802;z</a
      ><a name="10791"
      > </a
      ><a name="10792" class="Symbol"
      >|</a
      ><a name="10793"
      > </a
      ><a name="10794" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#547" class="InductiveConstructor"
      >no</a
      ><a name="10796"
      >  </a
      ><a name="10798" href="Maps.html#10798" class="Bound"
      >y&#8802;z</a
      ><a name="10801"
      >  </a
      ><a name="10803" class="Symbol"
      >=</a
      ><a name="10804"
      >  </a
      ><a name="10806" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.Core.html#632" class="Function"
      >trans</a
      ><a name="10811"
      > </a
      ><a name="10812" class="Symbol"
      >(</a
      ><a name="10813" href="Maps.html#7348" class="Function"
      >update-neq</a
      ><a name="10823"
      > </a
      ><a name="10824" href="Maps.html#10552" class="Bound"
      >&#961;</a
      ><a name="10825"
      > </a
      ><a name="10826" href="Maps.html#10554" class="Bound"
      >x</a
      ><a name="10827"
      > </a
      ><a name="10828" href="Maps.html#10556" class="Bound"
      >v</a
      ><a name="10829"
      > </a
      ><a name="10830" href="Maps.html#10562" class="Bound"
      >z</a
      ><a name="10831"
      > </a
      ><a name="10832" href="Maps.html#10788" class="Bound"
      >x&#8802;z</a
      ><a name="10835" class="Symbol"
      >)</a
      ><a name="10836"
      > </a
      ><a name="10837" class="Symbol"
      >(</a
      ><a name="10838" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.Core.html#565" class="Function"
      >sym</a
      ><a name="10841"
      > </a
      ><a name="10842" class="Symbol"
      >(</a
      ><a name="10843" href="Maps.html#7348" class="Function"
      >update-neq</a
      ><a name="10853"
      > </a
      ><a name="10854" href="Maps.html#10552" class="Bound"
      >&#961;</a
      ><a name="10855"
      > </a
      ><a name="10856" href="Maps.html#10558" class="Bound"
      >y</a
      ><a name="10857"
      > </a
      ><a name="10858" href="Maps.html#10560" class="Bound"
      >w</a
      ><a name="10859"
      > </a
      ><a name="10860" href="Maps.html#10562" class="Bound"
      >z</a
      ><a name="10861"
      > </a
      ><a name="10862" href="Maps.html#10798" class="Bound"
      >y&#8802;z</a
      ><a name="10865" class="Symbol"
      >))</a
      >

</pre>
</div>

## Partial maps

Finally, we define _partial maps_ on top of total maps.  A partial
map with elements of type `A` is simply a total map with elements
of type `Maybe A` and default element `nothing`.

<pre class="Agda">

<a name="11102" href="Maps.html#11102" class="Function"
      >PartialMap</a
      ><a name="11112"
      > </a
      ><a name="11113" class="Symbol"
      >:</a
      ><a name="11114"
      > </a
      ><a name="11115" class="PrimitiveType"
      >Set</a
      ><a name="11118"
      > </a
      ><a name="11119" class="Symbol"
      >&#8594;</a
      ><a name="11120"
      > </a
      ><a name="11121" class="PrimitiveType"
      >Set</a
      ><a name="11124"
      >
</a
      ><a name="11125" href="Maps.html#11102" class="Function"
      >PartialMap</a
      ><a name="11135"
      > </a
      ><a name="11136" href="Maps.html#11136" class="Bound"
      >A</a
      ><a name="11137"
      > </a
      ><a name="11138" class="Symbol"
      >=</a
      ><a name="11139"
      > </a
      ><a name="11140" href="Maps.html#3757" class="Function"
      >TotalMap</a
      ><a name="11148"
      > </a
      ><a name="11149" class="Symbol"
      >(</a
      ><a name="11150" href="https://agda.github.io/agda-stdlib/Data.Maybe.Base.html#335" class="Datatype"
      >Maybe</a
      ><a name="11155"
      > </a
      ><a name="11156" href="Maps.html#11136" class="Bound"
      >A</a
      ><a name="11157" class="Symbol"
      >)</a
      >

</pre>

<pre class="Agda">

<a name="11184" class="Keyword"
      >module</a
      ><a name="11190"
      > </a
      ><a name="11191" href="Maps.html#11191" class="Module"
      >PartialMap</a
      ><a name="11201"
      > </a
      ><a name="11202" class="Keyword"
      >where</a
      >

</pre>

<pre class="Agda">

  <a name="11235" href="Maps.html#11235" class="Function"
      >&#8709;</a
      ><a name="11236"
      > </a
      ><a name="11237" class="Symbol"
      >:</a
      ><a name="11238"
      > </a
      ><a name="11239" class="Symbol"
      >&#8704;</a
      ><a name="11240"
      > </a
      ><a name="11241" class="Symbol"
      >{</a
      ><a name="11242" href="Maps.html#11242" class="Bound"
      >A</a
      ><a name="11243" class="Symbol"
      >}</a
      ><a name="11244"
      > </a
      ><a name="11245" class="Symbol"
      >&#8594;</a
      ><a name="11246"
      > </a
      ><a name="11247" href="Maps.html#11102" class="Function"
      >PartialMap</a
      ><a name="11257"
      > </a
      ><a name="11258" href="Maps.html#11242" class="Bound"
      >A</a
      ><a name="11259"
      >
  </a
      ><a name="11262" href="Maps.html#11235" class="Function"
      >&#8709;</a
      ><a name="11263"
      > </a
      ><a name="11264" class="Symbol"
      >=</a
      ><a name="11265"
      > </a
      ><a name="11266" href="Maps.html#4132" class="Function"
      >TotalMap.always</a
      ><a name="11281"
      > </a
      ><a name="11282" href="https://agda.github.io/agda-stdlib/Data.Maybe.Base.html#403" class="InductiveConstructor"
      >nothing</a
      >

</pre>

<pre class="Agda">

  <a name="11317" href="Maps.html#11317" class="Function Operator"
      >_,_&#8614;_</a
      ><a name="11322"
      > </a
      ><a name="11323" class="Symbol"
      >:</a
      ><a name="11324"
      > </a
      ><a name="11325" class="Symbol"
      >&#8704;</a
      ><a name="11326"
      > </a
      ><a name="11327" class="Symbol"
      >{</a
      ><a name="11328" href="Maps.html#11328" class="Bound"
      >A</a
      ><a name="11329" class="Symbol"
      >}</a
      ><a name="11330"
      > </a
      ><a name="11331" class="Symbol"
      >(</a
      ><a name="11332" href="Maps.html#11332" class="Bound"
      >&#961;</a
      ><a name="11333"
      > </a
      ><a name="11334" class="Symbol"
      >:</a
      ><a name="11335"
      > </a
      ><a name="11336" href="Maps.html#11102" class="Function"
      >PartialMap</a
      ><a name="11346"
      > </a
      ><a name="11347" href="Maps.html#11328" class="Bound"
      >A</a
      ><a name="11348" class="Symbol"
      >)</a
      ><a name="11349"
      > </a
      ><a name="11350" class="Symbol"
      >(</a
      ><a name="11351" href="Maps.html#11351" class="Bound"
      >x</a
      ><a name="11352"
      > </a
      ><a name="11353" class="Symbol"
      >:</a
      ><a name="11354"
      > </a
      ><a name="11355" href="Maps.html#2215" class="Datatype"
      >Id</a
      ><a name="11357" class="Symbol"
      >)</a
      ><a name="11358"
      > </a
      ><a name="11359" class="Symbol"
      >(</a
      ><a name="11360" href="Maps.html#11360" class="Bound"
      >v</a
      ><a name="11361"
      > </a
      ><a name="11362" class="Symbol"
      >:</a
      ><a name="11363"
      > </a
      ><a name="11364" href="Maps.html#11328" class="Bound"
      >A</a
      ><a name="11365" class="Symbol"
      >)</a
      ><a name="11366"
      > </a
      ><a name="11367" class="Symbol"
      >&#8594;</a
      ><a name="11368"
      > </a
      ><a name="11369" href="Maps.html#11102" class="Function"
      >PartialMap</a
      ><a name="11379"
      > </a
      ><a name="11380" href="Maps.html#11328" class="Bound"
      >A</a
      ><a name="11381"
      >
  </a
      ><a name="11384" href="Maps.html#11384" class="Bound"
      >&#961;</a
      ><a name="11385"
      > </a
      ><a name="11386" href="Maps.html#11317" class="Function Operator"
      >,</a
      ><a name="11387"
      > </a
      ><a name="11388" href="Maps.html#11388" class="Bound"
      >x</a
      ><a name="11389"
      > </a
      ><a name="11390" href="Maps.html#11317" class="Function Operator"
      >&#8614;</a
      ><a name="11391"
      > </a
      ><a name="11392" href="Maps.html#11392" class="Bound"
      >v</a
      ><a name="11393"
      > </a
      ><a name="11394" class="Symbol"
      >=</a
      ><a name="11395"
      > </a
      ><a name="11396" href="Maps.html#4416" class="Function Operator"
      >TotalMap._,_&#8614;_</a
      ><a name="11410"
      > </a
      ><a name="11411" href="Maps.html#11384" class="Bound"
      >&#961;</a
      ><a name="11412"
      > </a
      ><a name="11413" href="Maps.html#11388" class="Bound"
      >x</a
      ><a name="11414"
      > </a
      ><a name="11415" class="Symbol"
      >(</a
      ><a name="11416" href="https://agda.github.io/agda-stdlib/Data.Maybe.Base.html#373" class="InductiveConstructor"
      >just</a
      ><a name="11420"
      > </a
      ><a name="11421" href="Maps.html#11392" class="Bound"
      >v</a
      ><a name="11422" class="Symbol"
      >)</a
      >

</pre>
As before, we define handy abbreviations for updating a map two, three, or four times.

<pre class="Agda">

  <a name="11538" href="Maps.html#11538" class="Function Operator"
      >_,_&#8614;_,_&#8614;_</a
      ><a name="11547"
      > </a
      ><a name="11548" class="Symbol"
      >:</a
      ><a name="11549"
      > </a
      ><a name="11550" class="Symbol"
      >&#8704;</a
      ><a name="11551"
      > </a
      ><a name="11552" class="Symbol"
      >{</a
      ><a name="11553" href="Maps.html#11553" class="Bound"
      >A</a
      ><a name="11554" class="Symbol"
      >}</a
      ><a name="11555"
      > </a
      ><a name="11556" class="Symbol"
      >&#8594;</a
      ><a name="11557"
      > </a
      ><a name="11558" href="Maps.html#11102" class="Function"
      >PartialMap</a
      ><a name="11568"
      > </a
      ><a name="11569" href="Maps.html#11553" class="Bound"
      >A</a
      ><a name="11570"
      > </a
      ><a name="11571" class="Symbol"
      >&#8594;</a
      ><a name="11572"
      > </a
      ><a name="11573" href="Maps.html#2215" class="Datatype"
      >Id</a
      ><a name="11575"
      > </a
      ><a name="11576" class="Symbol"
      >&#8594;</a
      ><a name="11577"
      > </a
      ><a name="11578" href="Maps.html#11553" class="Bound"
      >A</a
      ><a name="11579"
      > </a
      ><a name="11580" class="Symbol"
      >&#8594;</a
      ><a name="11581"
      > </a
      ><a name="11582" href="Maps.html#2215" class="Datatype"
      >Id</a
      ><a name="11584"
      > </a
      ><a name="11585" class="Symbol"
      >&#8594;</a
      ><a name="11586"
      > </a
      ><a name="11587" href="Maps.html#11553" class="Bound"
      >A</a
      ><a name="11588"
      > </a
      ><a name="11589" class="Symbol"
      >&#8594;</a
      ><a name="11590"
      > </a
      ><a name="11591" href="Maps.html#11102" class="Function"
      >PartialMap</a
      ><a name="11601"
      > </a
      ><a name="11602" href="Maps.html#11553" class="Bound"
      >A</a
      ><a name="11603"
      >
  </a
      ><a name="11606" href="Maps.html#11606" class="Bound"
      >&#961;</a
      ><a name="11607"
      > </a
      ><a name="11608" href="Maps.html#11538" class="Function Operator"
      >,</a
      ><a name="11609"
      > </a
      ><a name="11610" href="Maps.html#11610" class="Bound"
      >x&#8321;</a
      ><a name="11612"
      > </a
      ><a name="11613" href="Maps.html#11538" class="Function Operator"
      >&#8614;</a
      ><a name="11614"
      > </a
      ><a name="11615" href="Maps.html#11615" class="Bound"
      >v&#8321;</a
      ><a name="11617"
      > </a
      ><a name="11618" href="Maps.html#11538" class="Function Operator"
      >,</a
      ><a name="11619"
      > </a
      ><a name="11620" href="Maps.html#11620" class="Bound"
      >x&#8322;</a
      ><a name="11622"
      > </a
      ><a name="11623" href="Maps.html#11538" class="Function Operator"
      >&#8614;</a
      ><a name="11624"
      > </a
      ><a name="11625" href="Maps.html#11625" class="Bound"
      >v&#8322;</a
      ><a name="11627"
      >  </a
      ><a name="11629" class="Symbol"
      >=</a
      ><a name="11630"
      >  </a
      ><a name="11632" class="Symbol"
      >(</a
      ><a name="11633" href="Maps.html#11606" class="Bound"
      >&#961;</a
      ><a name="11634"
      > </a
      ><a name="11635" href="Maps.html#11317" class="Function Operator"
      >,</a
      ><a name="11636"
      > </a
      ><a name="11637" href="Maps.html#11610" class="Bound"
      >x&#8321;</a
      ><a name="11639"
      > </a
      ><a name="11640" href="Maps.html#11317" class="Function Operator"
      >&#8614;</a
      ><a name="11641"
      > </a
      ><a name="11642" href="Maps.html#11615" class="Bound"
      >v&#8321;</a
      ><a name="11644" class="Symbol"
      >)</a
      ><a name="11645" href="Maps.html#11317" class="Function Operator"
      >,</a
      ><a name="11646"
      > </a
      ><a name="11647" href="Maps.html#11620" class="Bound"
      >x&#8322;</a
      ><a name="11649"
      > </a
      ><a name="11650" href="Maps.html#11317" class="Function Operator"
      >&#8614;</a
      ><a name="11651"
      > </a
      ><a name="11652" href="Maps.html#11625" class="Bound"
      >v&#8322;</a
      ><a name="11654"
      >

  </a
      ><a name="11658" href="Maps.html#11658" class="Function Operator"
      >_,_&#8614;_,_&#8614;_,_&#8614;_</a
      ><a name="11671"
      > </a
      ><a name="11672" class="Symbol"
      >:</a
      ><a name="11673"
      > </a
      ><a name="11674" class="Symbol"
      >&#8704;</a
      ><a name="11675"
      > </a
      ><a name="11676" class="Symbol"
      >{</a
      ><a name="11677" href="Maps.html#11677" class="Bound"
      >A</a
      ><a name="11678" class="Symbol"
      >}</a
      ><a name="11679"
      > </a
      ><a name="11680" class="Symbol"
      >&#8594;</a
      ><a name="11681"
      > </a
      ><a name="11682" href="Maps.html#11102" class="Function"
      >PartialMap</a
      ><a name="11692"
      > </a
      ><a name="11693" href="Maps.html#11677" class="Bound"
      >A</a
      ><a name="11694"
      > </a
      ><a name="11695" class="Symbol"
      >&#8594;</a
      ><a name="11696"
      > </a
      ><a name="11697" href="Maps.html#2215" class="Datatype"
      >Id</a
      ><a name="11699"
      > </a
      ><a name="11700" class="Symbol"
      >&#8594;</a
      ><a name="11701"
      > </a
      ><a name="11702" href="Maps.html#11677" class="Bound"
      >A</a
      ><a name="11703"
      > </a
      ><a name="11704" class="Symbol"
      >&#8594;</a
      ><a name="11705"
      > </a
      ><a name="11706" href="Maps.html#2215" class="Datatype"
      >Id</a
      ><a name="11708"
      > </a
      ><a name="11709" class="Symbol"
      >&#8594;</a
      ><a name="11710"
      > </a
      ><a name="11711" href="Maps.html#11677" class="Bound"
      >A</a
      ><a name="11712"
      > </a
      ><a name="11713" class="Symbol"
      >&#8594;</a
      ><a name="11714"
      > </a
      ><a name="11715" href="Maps.html#2215" class="Datatype"
      >Id</a
      ><a name="11717"
      > </a
      ><a name="11718" class="Symbol"
      >&#8594;</a
      ><a name="11719"
      > </a
      ><a name="11720" href="Maps.html#11677" class="Bound"
      >A</a
      ><a name="11721"
      > </a
      ><a name="11722" class="Symbol"
      >&#8594;</a
      ><a name="11723"
      > </a
      ><a name="11724" href="Maps.html#11102" class="Function"
      >PartialMap</a
      ><a name="11734"
      > </a
      ><a name="11735" href="Maps.html#11677" class="Bound"
      >A</a
      ><a name="11736"
      >
  </a
      ><a name="11739" href="Maps.html#11739" class="Bound"
      >&#961;</a
      ><a name="11740"
      > </a
      ><a name="11741" href="Maps.html#11658" class="Function Operator"
      >,</a
      ><a name="11742"
      > </a
      ><a name="11743" href="Maps.html#11743" class="Bound"
      >x&#8321;</a
      ><a name="11745"
      > </a
      ><a name="11746" href="Maps.html#11658" class="Function Operator"
      >&#8614;</a
      ><a name="11747"
      > </a
      ><a name="11748" href="Maps.html#11748" class="Bound"
      >v&#8321;</a
      ><a name="11750"
      > </a
      ><a name="11751" href="Maps.html#11658" class="Function Operator"
      >,</a
      ><a name="11752"
      > </a
      ><a name="11753" href="Maps.html#11753" class="Bound"
      >x&#8322;</a
      ><a name="11755"
      > </a
      ><a name="11756" href="Maps.html#11658" class="Function Operator"
      >&#8614;</a
      ><a name="11757"
      > </a
      ><a name="11758" href="Maps.html#11758" class="Bound"
      >v&#8322;</a
      ><a name="11760"
      > </a
      ><a name="11761" href="Maps.html#11658" class="Function Operator"
      >,</a
      ><a name="11762"
      > </a
      ><a name="11763" href="Maps.html#11763" class="Bound"
      >x&#8323;</a
      ><a name="11765"
      > </a
      ><a name="11766" href="Maps.html#11658" class="Function Operator"
      >&#8614;</a
      ><a name="11767"
      > </a
      ><a name="11768" href="Maps.html#11768" class="Bound"
      >v&#8323;</a
      ><a name="11770"
      >  </a
      ><a name="11772" class="Symbol"
      >=</a
      ><a name="11773"
      >  </a
      ><a name="11775" class="Symbol"
      >((</a
      ><a name="11777" href="Maps.html#11739" class="Bound"
      >&#961;</a
      ><a name="11778"
      > </a
      ><a name="11779" href="Maps.html#11317" class="Function Operator"
      >,</a
      ><a name="11780"
      > </a
      ><a name="11781" href="Maps.html#11743" class="Bound"
      >x&#8321;</a
      ><a name="11783"
      > </a
      ><a name="11784" href="Maps.html#11317" class="Function Operator"
      >&#8614;</a
      ><a name="11785"
      > </a
      ><a name="11786" href="Maps.html#11748" class="Bound"
      >v&#8321;</a
      ><a name="11788" class="Symbol"
      >)</a
      ><a name="11789" href="Maps.html#11317" class="Function Operator"
      >,</a
      ><a name="11790"
      > </a
      ><a name="11791" href="Maps.html#11753" class="Bound"
      >x&#8322;</a
      ><a name="11793"
      > </a
      ><a name="11794" href="Maps.html#11317" class="Function Operator"
      >&#8614;</a
      ><a name="11795"
      > </a
      ><a name="11796" href="Maps.html#11758" class="Bound"
      >v&#8322;</a
      ><a name="11798" class="Symbol"
      >)</a
      ><a name="11799" href="Maps.html#11317" class="Function Operator"
      >,</a
      ><a name="11800"
      > </a
      ><a name="11801" href="Maps.html#11763" class="Bound"
      >x&#8323;</a
      ><a name="11803"
      > </a
      ><a name="11804" href="Maps.html#11317" class="Function Operator"
      >&#8614;</a
      ><a name="11805"
      > </a
      ><a name="11806" href="Maps.html#11768" class="Bound"
      >v&#8323;</a
      ><a name="11808"
      >

  </a
      ><a name="11812" href="Maps.html#11812" class="Function Operator"
      >_,_&#8614;_,_&#8614;_,_&#8614;_,_&#8614;_</a
      ><a name="11829"
      > </a
      ><a name="11830" class="Symbol"
      >:</a
      ><a name="11831"
      > </a
      ><a name="11832" class="Symbol"
      >&#8704;</a
      ><a name="11833"
      > </a
      ><a name="11834" class="Symbol"
      >{</a
      ><a name="11835" href="Maps.html#11835" class="Bound"
      >A</a
      ><a name="11836" class="Symbol"
      >}</a
      ><a name="11837"
      > </a
      ><a name="11838" class="Symbol"
      >&#8594;</a
      ><a name="11839"
      > </a
      ><a name="11840" href="Maps.html#11102" class="Function"
      >PartialMap</a
      ><a name="11850"
      > </a
      ><a name="11851" href="Maps.html#11835" class="Bound"
      >A</a
      ><a name="11852"
      > </a
      ><a name="11853" class="Symbol"
      >&#8594;</a
      ><a name="11854"
      > </a
      ><a name="11855" href="Maps.html#2215" class="Datatype"
      >Id</a
      ><a name="11857"
      > </a
      ><a name="11858" class="Symbol"
      >&#8594;</a
      ><a name="11859"
      > </a
      ><a name="11860" href="Maps.html#11835" class="Bound"
      >A</a
      ><a name="11861"
      > </a
      ><a name="11862" class="Symbol"
      >&#8594;</a
      ><a name="11863"
      > </a
      ><a name="11864" href="Maps.html#2215" class="Datatype"
      >Id</a
      ><a name="11866"
      > </a
      ><a name="11867" class="Symbol"
      >&#8594;</a
      ><a name="11868"
      > </a
      ><a name="11869" href="Maps.html#11835" class="Bound"
      >A</a
      ><a name="11870"
      > </a
      ><a name="11871" class="Symbol"
      >&#8594;</a
      ><a name="11872"
      > </a
      ><a name="11873" href="Maps.html#2215" class="Datatype"
      >Id</a
      ><a name="11875"
      > </a
      ><a name="11876" class="Symbol"
      >&#8594;</a
      ><a name="11877"
      > </a
      ><a name="11878" href="Maps.html#11835" class="Bound"
      >A</a
      ><a name="11879"
      > </a
      ><a name="11880" class="Symbol"
      >&#8594;</a
      ><a name="11881"
      > </a
      ><a name="11882" href="Maps.html#2215" class="Datatype"
      >Id</a
      ><a name="11884"
      > </a
      ><a name="11885" class="Symbol"
      >&#8594;</a
      ><a name="11886"
      > </a
      ><a name="11887" href="Maps.html#11835" class="Bound"
      >A</a
      ><a name="11888"
      > </a
      ><a name="11889" class="Symbol"
      >&#8594;</a
      ><a name="11890"
      > </a
      ><a name="11891" href="Maps.html#11102" class="Function"
      >PartialMap</a
      ><a name="11901"
      > </a
      ><a name="11902" href="Maps.html#11835" class="Bound"
      >A</a
      ><a name="11903"
      >
  </a
      ><a name="11906" href="Maps.html#11906" class="Bound"
      >&#961;</a
      ><a name="11907"
      > </a
      ><a name="11908" href="Maps.html#11812" class="Function Operator"
      >,</a
      ><a name="11909"
      > </a
      ><a name="11910" href="Maps.html#11910" class="Bound"
      >x&#8321;</a
      ><a name="11912"
      > </a
      ><a name="11913" href="Maps.html#11812" class="Function Operator"
      >&#8614;</a
      ><a name="11914"
      > </a
      ><a name="11915" href="Maps.html#11915" class="Bound"
      >v&#8321;</a
      ><a name="11917"
      > </a
      ><a name="11918" href="Maps.html#11812" class="Function Operator"
      >,</a
      ><a name="11919"
      > </a
      ><a name="11920" href="Maps.html#11920" class="Bound"
      >x&#8322;</a
      ><a name="11922"
      > </a
      ><a name="11923" href="Maps.html#11812" class="Function Operator"
      >&#8614;</a
      ><a name="11924"
      > </a
      ><a name="11925" href="Maps.html#11925" class="Bound"
      >v&#8322;</a
      ><a name="11927"
      > </a
      ><a name="11928" href="Maps.html#11812" class="Function Operator"
      >,</a
      ><a name="11929"
      > </a
      ><a name="11930" href="Maps.html#11930" class="Bound"
      >x&#8323;</a
      ><a name="11932"
      > </a
      ><a name="11933" href="Maps.html#11812" class="Function Operator"
      >&#8614;</a
      ><a name="11934"
      > </a
      ><a name="11935" href="Maps.html#11935" class="Bound"
      >v&#8323;</a
      ><a name="11937"
      > </a
      ><a name="11938" href="Maps.html#11812" class="Function Operator"
      >,</a
      ><a name="11939"
      > </a
      ><a name="11940" href="Maps.html#11940" class="Bound"
      >x&#8324;</a
      ><a name="11942"
      > </a
      ><a name="11943" href="Maps.html#11812" class="Function Operator"
      >&#8614;</a
      ><a name="11944"
      > </a
      ><a name="11945" href="Maps.html#11945" class="Bound"
      >v&#8324;</a
      ><a name="11947"
      > </a
      ><a name="11948" class="Symbol"
      >=</a
      ><a name="11949"
      >  </a
      ><a name="11951" class="Symbol"
      >(((</a
      ><a name="11954" href="Maps.html#11906" class="Bound"
      >&#961;</a
      ><a name="11955"
      > </a
      ><a name="11956" href="Maps.html#11317" class="Function Operator"
      >,</a
      ><a name="11957"
      > </a
      ><a name="11958" href="Maps.html#11910" class="Bound"
      >x&#8321;</a
      ><a name="11960"
      > </a
      ><a name="11961" href="Maps.html#11317" class="Function Operator"
      >&#8614;</a
      ><a name="11962"
      > </a
      ><a name="11963" href="Maps.html#11915" class="Bound"
      >v&#8321;</a
      ><a name="11965" class="Symbol"
      >)</a
      ><a name="11966" href="Maps.html#11317" class="Function Operator"
      >,</a
      ><a name="11967"
      > </a
      ><a name="11968" href="Maps.html#11920" class="Bound"
      >x&#8322;</a
      ><a name="11970"
      > </a
      ><a name="11971" href="Maps.html#11317" class="Function Operator"
      >&#8614;</a
      ><a name="11972"
      > </a
      ><a name="11973" href="Maps.html#11925" class="Bound"
      >v&#8322;</a
      ><a name="11975" class="Symbol"
      >)</a
      ><a name="11976" href="Maps.html#11317" class="Function Operator"
      >,</a
      ><a name="11977"
      > </a
      ><a name="11978" href="Maps.html#11930" class="Bound"
      >x&#8323;</a
      ><a name="11980"
      > </a
      ><a name="11981" href="Maps.html#11317" class="Function Operator"
      >&#8614;</a
      ><a name="11982"
      > </a
      ><a name="11983" href="Maps.html#11935" class="Bound"
      >v&#8323;</a
      ><a name="11985" class="Symbol"
      >)</a
      ><a name="11986" href="Maps.html#11317" class="Function Operator"
      >,</a
      ><a name="11987"
      > </a
      ><a name="11988" href="Maps.html#11940" class="Bound"
      >x&#8324;</a
      ><a name="11990"
      > </a
      ><a name="11991" href="Maps.html#11317" class="Function Operator"
      >&#8614;</a
      ><a name="11992"
      > </a
      ><a name="11993" href="Maps.html#11945" class="Bound"
      >v&#8324;</a
      >

</pre>

We now lift all of the basic lemmas about total maps to partial maps.

<pre class="Agda">

  <a name="12094" href="Maps.html#12094" class="Function"
      >apply-&#8709;</a
      ><a name="12101"
      > </a
      ><a name="12102" class="Symbol"
      >:</a
      ><a name="12103"
      > </a
      ><a name="12104" class="Symbol"
      >&#8704;</a
      ><a name="12105"
      > </a
      ><a name="12106" class="Symbol"
      >{</a
      ><a name="12107" href="Maps.html#12107" class="Bound"
      >A</a
      ><a name="12108" class="Symbol"
      >}</a
      ><a name="12109"
      > </a
      ><a name="12110" class="Symbol"
      >&#8594;</a
      ><a name="12111"
      > </a
      ><a name="12112" class="Symbol"
      >(</a
      ><a name="12113" href="Maps.html#12113" class="Bound"
      >x</a
      ><a name="12114"
      > </a
      ><a name="12115" class="Symbol"
      >:</a
      ><a name="12116"
      > </a
      ><a name="12117" href="Maps.html#2215" class="Datatype"
      >Id</a
      ><a name="12119" class="Symbol"
      >)</a
      ><a name="12120"
      > </a
      ><a name="12121" class="Symbol"
      >&#8594;</a
      ><a name="12122"
      > </a
      ><a name="12123" class="Symbol"
      >(</a
      ><a name="12124" href="Maps.html#11235" class="Function"
      >&#8709;</a
      ><a name="12125"
      > </a
      ><a name="12126" class="Symbol"
      >{</a
      ><a name="12127" href="Maps.html#12107" class="Bound"
      >A</a
      ><a name="12128" class="Symbol"
      >}</a
      ><a name="12129"
      > </a
      ><a name="12130" href="Maps.html#12113" class="Bound"
      >x</a
      ><a name="12131" class="Symbol"
      >)</a
      ><a name="12132"
      > </a
      ><a name="12133" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="12134"
      > </a
      ><a name="12135" href="https://agda.github.io/agda-stdlib/Data.Maybe.Base.html#403" class="InductiveConstructor"
      >nothing</a
      ><a name="12142"
      >
  </a
      ><a name="12145" href="Maps.html#12094" class="Function"
      >apply-&#8709;</a
      ><a name="12152"
      > </a
      ><a name="12153" href="Maps.html#12153" class="Bound"
      >x</a
      ><a name="12154"
      >  </a
      ><a name="12156" class="Symbol"
      >=</a
      ><a name="12157"
      > </a
      ><a name="12158" href="Maps.html#6355" class="Postulate"
      >TotalMap.apply-always</a
      ><a name="12179"
      > </a
      ><a name="12180" href="https://agda.github.io/agda-stdlib/Data.Maybe.Base.html#403" class="InductiveConstructor"
      >nothing</a
      ><a name="12187"
      > </a
      ><a name="12188" href="Maps.html#12153" class="Bound"
      >x</a
      >

</pre>

<pre class="Agda">

  <a name="12217" href="Maps.html#12217" class="Function"
      >update-eq</a
      ><a name="12226"
      > </a
      ><a name="12227" class="Symbol"
      >:</a
      ><a name="12228"
      > </a
      ><a name="12229" class="Symbol"
      >&#8704;</a
      ><a name="12230"
      > </a
      ><a name="12231" class="Symbol"
      >{</a
      ><a name="12232" href="Maps.html#12232" class="Bound"
      >A</a
      ><a name="12233" class="Symbol"
      >}</a
      ><a name="12234"
      > </a
      ><a name="12235" class="Symbol"
      >(</a
      ><a name="12236" href="Maps.html#12236" class="Bound"
      >&#961;</a
      ><a name="12237"
      > </a
      ><a name="12238" class="Symbol"
      >:</a
      ><a name="12239"
      > </a
      ><a name="12240" href="Maps.html#11102" class="Function"
      >PartialMap</a
      ><a name="12250"
      > </a
      ><a name="12251" href="Maps.html#12232" class="Bound"
      >A</a
      ><a name="12252" class="Symbol"
      >)</a
      ><a name="12253"
      > </a
      ><a name="12254" class="Symbol"
      >(</a
      ><a name="12255" href="Maps.html#12255" class="Bound"
      >x</a
      ><a name="12256"
      > </a
      ><a name="12257" class="Symbol"
      >:</a
      ><a name="12258"
      > </a
      ><a name="12259" href="Maps.html#2215" class="Datatype"
      >Id</a
      ><a name="12261" class="Symbol"
      >)</a
      ><a name="12262"
      > </a
      ><a name="12263" class="Symbol"
      >(</a
      ><a name="12264" href="Maps.html#12264" class="Bound"
      >v</a
      ><a name="12265"
      > </a
      ><a name="12266" class="Symbol"
      >:</a
      ><a name="12267"
      > </a
      ><a name="12268" href="Maps.html#12232" class="Bound"
      >A</a
      ><a name="12269" class="Symbol"
      >)</a
      ><a name="12270"
      >
            </a
      ><a name="12283" class="Symbol"
      >&#8594;</a
      ><a name="12284"
      > </a
      ><a name="12285" class="Symbol"
      >(</a
      ><a name="12286" href="Maps.html#12236" class="Bound"
      >&#961;</a
      ><a name="12287"
      > </a
      ><a name="12288" href="Maps.html#11317" class="Function Operator"
      >,</a
      ><a name="12289"
      > </a
      ><a name="12290" href="Maps.html#12255" class="Bound"
      >x</a
      ><a name="12291"
      > </a
      ><a name="12292" href="Maps.html#11317" class="Function Operator"
      >&#8614;</a
      ><a name="12293"
      > </a
      ><a name="12294" href="Maps.html#12264" class="Bound"
      >v</a
      ><a name="12295" class="Symbol"
      >)</a
      ><a name="12296"
      > </a
      ><a name="12297" href="Maps.html#12255" class="Bound"
      >x</a
      ><a name="12298"
      > </a
      ><a name="12299" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="12300"
      > </a
      ><a name="12301" href="https://agda.github.io/agda-stdlib/Data.Maybe.Base.html#373" class="InductiveConstructor"
      >just</a
      ><a name="12305"
      > </a
      ><a name="12306" href="Maps.html#12264" class="Bound"
      >v</a
      ><a name="12307"
      >
  </a
      ><a name="12310" href="Maps.html#12217" class="Function"
      >update-eq</a
      ><a name="12319"
      > </a
      ><a name="12320" href="Maps.html#12320" class="Bound"
      >&#961;</a
      ><a name="12321"
      > </a
      ><a name="12322" href="Maps.html#12322" class="Bound"
      >x</a
      ><a name="12323"
      > </a
      ><a name="12324" href="Maps.html#12324" class="Bound"
      >v</a
      ><a name="12325"
      > </a
      ><a name="12326" class="Symbol"
      >=</a
      ><a name="12327"
      > </a
      ><a name="12328" href="Maps.html#6784" class="Postulate"
      >TotalMap.update-eq</a
      ><a name="12346"
      > </a
      ><a name="12347" href="Maps.html#12320" class="Bound"
      >&#961;</a
      ><a name="12348"
      > </a
      ><a name="12349" href="Maps.html#12322" class="Bound"
      >x</a
      ><a name="12350"
      > </a
      ><a name="12351" class="Symbol"
      >(</a
      ><a name="12352" href="https://agda.github.io/agda-stdlib/Data.Maybe.Base.html#373" class="InductiveConstructor"
      >just</a
      ><a name="12356"
      > </a
      ><a name="12357" href="Maps.html#12324" class="Bound"
      >v</a
      ><a name="12358" class="Symbol"
      >)</a
      >

</pre>

<pre class="Agda">

  <a name="12387" href="Maps.html#12387" class="Function"
      >update-neq</a
      ><a name="12397"
      > </a
      ><a name="12398" class="Symbol"
      >:</a
      ><a name="12399"
      > </a
      ><a name="12400" class="Symbol"
      >&#8704;</a
      ><a name="12401"
      > </a
      ><a name="12402" class="Symbol"
      >{</a
      ><a name="12403" href="Maps.html#12403" class="Bound"
      >A</a
      ><a name="12404" class="Symbol"
      >}</a
      ><a name="12405"
      > </a
      ><a name="12406" class="Symbol"
      >(</a
      ><a name="12407" href="Maps.html#12407" class="Bound"
      >&#961;</a
      ><a name="12408"
      > </a
      ><a name="12409" class="Symbol"
      >:</a
      ><a name="12410"
      > </a
      ><a name="12411" href="Maps.html#11102" class="Function"
      >PartialMap</a
      ><a name="12421"
      > </a
      ><a name="12422" href="Maps.html#12403" class="Bound"
      >A</a
      ><a name="12423" class="Symbol"
      >)</a
      ><a name="12424"
      > </a
      ><a name="12425" class="Symbol"
      >(</a
      ><a name="12426" href="Maps.html#12426" class="Bound"
      >x</a
      ><a name="12427"
      > </a
      ><a name="12428" class="Symbol"
      >:</a
      ><a name="12429"
      > </a
      ><a name="12430" href="Maps.html#2215" class="Datatype"
      >Id</a
      ><a name="12432" class="Symbol"
      >)</a
      ><a name="12433"
      > </a
      ><a name="12434" class="Symbol"
      >(</a
      ><a name="12435" href="Maps.html#12435" class="Bound"
      >v</a
      ><a name="12436"
      > </a
      ><a name="12437" class="Symbol"
      >:</a
      ><a name="12438"
      > </a
      ><a name="12439" href="Maps.html#12403" class="Bound"
      >A</a
      ><a name="12440" class="Symbol"
      >)</a
      ><a name="12441"
      > </a
      ><a name="12442" class="Symbol"
      >(</a
      ><a name="12443" href="Maps.html#12443" class="Bound"
      >y</a
      ><a name="12444"
      > </a
      ><a name="12445" class="Symbol"
      >:</a
      ><a name="12446"
      > </a
      ><a name="12447" href="Maps.html#2215" class="Datatype"
      >Id</a
      ><a name="12449" class="Symbol"
      >)</a
      ><a name="12450"
      >
             </a
      ><a name="12464" class="Symbol"
      >&#8594;</a
      ><a name="12465"
      > </a
      ><a name="12466" href="Maps.html#12426" class="Bound"
      >x</a
      ><a name="12467"
      > </a
      ><a name="12468" href="https://agda.github.io/agda-stdlib/Relation.Binary.Core.html#4493" class="Function Operator"
      >&#8802;</a
      ><a name="12469"
      > </a
      ><a name="12470" href="Maps.html#12443" class="Bound"
      >y</a
      ><a name="12471"
      > </a
      ><a name="12472" class="Symbol"
      >&#8594;</a
      ><a name="12473"
      > </a
      ><a name="12474" class="Symbol"
      >(</a
      ><a name="12475" href="Maps.html#12407" class="Bound"
      >&#961;</a
      ><a name="12476"
      > </a
      ><a name="12477" href="Maps.html#11317" class="Function Operator"
      >,</a
      ><a name="12478"
      > </a
      ><a name="12479" href="Maps.html#12426" class="Bound"
      >x</a
      ><a name="12480"
      > </a
      ><a name="12481" href="Maps.html#11317" class="Function Operator"
      >&#8614;</a
      ><a name="12482"
      > </a
      ><a name="12483" href="Maps.html#12435" class="Bound"
      >v</a
      ><a name="12484" class="Symbol"
      >)</a
      ><a name="12485"
      > </a
      ><a name="12486" href="Maps.html#12443" class="Bound"
      >y</a
      ><a name="12487"
      > </a
      ><a name="12488" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="12489"
      > </a
      ><a name="12490" href="Maps.html#12407" class="Bound"
      >&#961;</a
      ><a name="12491"
      > </a
      ><a name="12492" href="Maps.html#12443" class="Bound"
      >y</a
      ><a name="12493"
      >
  </a
      ><a name="12496" href="Maps.html#12387" class="Function"
      >update-neq</a
      ><a name="12506"
      > </a
      ><a name="12507" href="Maps.html#12507" class="Bound"
      >&#961;</a
      ><a name="12508"
      > </a
      ><a name="12509" href="Maps.html#12509" class="Bound"
      >x</a
      ><a name="12510"
      > </a
      ><a name="12511" href="Maps.html#12511" class="Bound"
      >v</a
      ><a name="12512"
      > </a
      ><a name="12513" href="Maps.html#12513" class="Bound"
      >y</a
      ><a name="12514"
      > </a
      ><a name="12515" href="Maps.html#12515" class="Bound"
      >x&#8802;y</a
      ><a name="12518"
      > </a
      ><a name="12519" class="Symbol"
      >=</a
      ><a name="12520"
      > </a
      ><a name="12521" href="Maps.html#7348" class="Function"
      >TotalMap.update-neq</a
      ><a name="12540"
      > </a
      ><a name="12541" href="Maps.html#12507" class="Bound"
      >&#961;</a
      ><a name="12542"
      > </a
      ><a name="12543" href="Maps.html#12509" class="Bound"
      >x</a
      ><a name="12544"
      > </a
      ><a name="12545" class="Symbol"
      >(</a
      ><a name="12546" href="https://agda.github.io/agda-stdlib/Data.Maybe.Base.html#373" class="InductiveConstructor"
      >just</a
      ><a name="12550"
      > </a
      ><a name="12551" href="Maps.html#12511" class="Bound"
      >v</a
      ><a name="12552" class="Symbol"
      >)</a
      ><a name="12553"
      > </a
      ><a name="12554" href="Maps.html#12513" class="Bound"
      >y</a
      ><a name="12555"
      > </a
      ><a name="12556" href="Maps.html#12515" class="Bound"
      >x&#8802;y</a
      >

</pre>

<pre class="Agda">

  <a name="12587" href="Maps.html#12587" class="Function"
      >update-shadow</a
      ><a name="12600"
      > </a
      ><a name="12601" class="Symbol"
      >:</a
      ><a name="12602"
      > </a
      ><a name="12603" class="Symbol"
      >&#8704;</a
      ><a name="12604"
      > </a
      ><a name="12605" class="Symbol"
      >{</a
      ><a name="12606" href="Maps.html#12606" class="Bound"
      >A</a
      ><a name="12607" class="Symbol"
      >}</a
      ><a name="12608"
      > </a
      ><a name="12609" class="Symbol"
      >(</a
      ><a name="12610" href="Maps.html#12610" class="Bound"
      >&#961;</a
      ><a name="12611"
      > </a
      ><a name="12612" class="Symbol"
      >:</a
      ><a name="12613"
      > </a
      ><a name="12614" href="Maps.html#11102" class="Function"
      >PartialMap</a
      ><a name="12624"
      > </a
      ><a name="12625" href="Maps.html#12606" class="Bound"
      >A</a
      ><a name="12626" class="Symbol"
      >)</a
      ><a name="12627"
      > </a
      ><a name="12628" class="Symbol"
      >(</a
      ><a name="12629" href="Maps.html#12629" class="Bound"
      >x</a
      ><a name="12630"
      > </a
      ><a name="12631" class="Symbol"
      >:</a
      ><a name="12632"
      > </a
      ><a name="12633" href="Maps.html#2215" class="Datatype"
      >Id</a
      ><a name="12635" class="Symbol"
      >)</a
      ><a name="12636"
      > </a
      ><a name="12637" class="Symbol"
      >(</a
      ><a name="12638" href="Maps.html#12638" class="Bound"
      >v</a
      ><a name="12639"
      > </a
      ><a name="12640" href="Maps.html#12640" class="Bound"
      >w</a
      ><a name="12641"
      > </a
      ><a name="12642" class="Symbol"
      >:</a
      ><a name="12643"
      > </a
      ><a name="12644" href="Maps.html#12606" class="Bound"
      >A</a
      ><a name="12645" class="Symbol"
      >)</a
      ><a name="12646"
      > 
                </a
      ><a name="12664" class="Symbol"
      >&#8594;</a
      ><a name="12665"
      > </a
      ><a name="12666" class="Symbol"
      >(</a
      ><a name="12667" href="Maps.html#12610" class="Bound"
      >&#961;</a
      ><a name="12668"
      > </a
      ><a name="12669" href="Maps.html#11538" class="Function Operator"
      >,</a
      ><a name="12670"
      > </a
      ><a name="12671" href="Maps.html#12629" class="Bound"
      >x</a
      ><a name="12672"
      > </a
      ><a name="12673" href="Maps.html#11538" class="Function Operator"
      >&#8614;</a
      ><a name="12674"
      > </a
      ><a name="12675" href="Maps.html#12638" class="Bound"
      >v</a
      ><a name="12676"
      > </a
      ><a name="12677" href="Maps.html#11538" class="Function Operator"
      >,</a
      ><a name="12678"
      > </a
      ><a name="12679" href="Maps.html#12629" class="Bound"
      >x</a
      ><a name="12680"
      > </a
      ><a name="12681" href="Maps.html#11538" class="Function Operator"
      >&#8614;</a
      ><a name="12682"
      > </a
      ><a name="12683" href="Maps.html#12640" class="Bound"
      >w</a
      ><a name="12684" class="Symbol"
      >)</a
      ><a name="12685"
      > </a
      ><a name="12686" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="12687"
      > </a
      ><a name="12688" class="Symbol"
      >(</a
      ><a name="12689" href="Maps.html#12610" class="Bound"
      >&#961;</a
      ><a name="12690"
      > </a
      ><a name="12691" href="Maps.html#11317" class="Function Operator"
      >,</a
      ><a name="12692"
      > </a
      ><a name="12693" href="Maps.html#12629" class="Bound"
      >x</a
      ><a name="12694"
      > </a
      ><a name="12695" href="Maps.html#11317" class="Function Operator"
      >&#8614;</a
      ><a name="12696"
      > </a
      ><a name="12697" href="Maps.html#12640" class="Bound"
      >w</a
      ><a name="12698" class="Symbol"
      >)</a
      ><a name="12699"
      >
  </a
      ><a name="12702" href="Maps.html#12587" class="Function"
      >update-shadow</a
      ><a name="12715"
      > </a
      ><a name="12716" href="Maps.html#12716" class="Bound"
      >&#961;</a
      ><a name="12717"
      > </a
      ><a name="12718" href="Maps.html#12718" class="Bound"
      >x</a
      ><a name="12719"
      > </a
      ><a name="12720" href="Maps.html#12720" class="Bound"
      >v</a
      ><a name="12721"
      > </a
      ><a name="12722" href="Maps.html#12722" class="Bound"
      >w</a
      ><a name="12723"
      > </a
      ><a name="12724" class="Symbol"
      >=</a
      ><a name="12725"
      > </a
      ><a name="12726" href="Maps.html#8179" class="Postulate"
      >TotalMap.update-shadow</a
      ><a name="12748"
      > </a
      ><a name="12749" href="Maps.html#12716" class="Bound"
      >&#961;</a
      ><a name="12750"
      > </a
      ><a name="12751" href="Maps.html#12718" class="Bound"
      >x</a
      ><a name="12752"
      > </a
      ><a name="12753" class="Symbol"
      >(</a
      ><a name="12754" href="https://agda.github.io/agda-stdlib/Data.Maybe.Base.html#373" class="InductiveConstructor"
      >just</a
      ><a name="12758"
      > </a
      ><a name="12759" href="Maps.html#12720" class="Bound"
      >v</a
      ><a name="12760" class="Symbol"
      >)</a
      ><a name="12761"
      > </a
      ><a name="12762" class="Symbol"
      >(</a
      ><a name="12763" href="https://agda.github.io/agda-stdlib/Data.Maybe.Base.html#373" class="InductiveConstructor"
      >just</a
      ><a name="12767"
      > </a
      ><a name="12768" href="Maps.html#12722" class="Bound"
      >w</a
      ><a name="12769" class="Symbol"
      >)</a
      >

</pre>

<pre class="Agda">

  <a name="12798" href="Maps.html#12798" class="Function"
      >update-same</a
      ><a name="12809"
      > </a
      ><a name="12810" class="Symbol"
      >:</a
      ><a name="12811"
      > </a
      ><a name="12812" class="Symbol"
      >&#8704;</a
      ><a name="12813"
      > </a
      ><a name="12814" class="Symbol"
      >{</a
      ><a name="12815" href="Maps.html#12815" class="Bound"
      >A</a
      ><a name="12816" class="Symbol"
      >}</a
      ><a name="12817"
      > </a
      ><a name="12818" class="Symbol"
      >(</a
      ><a name="12819" href="Maps.html#12819" class="Bound"
      >&#961;</a
      ><a name="12820"
      > </a
      ><a name="12821" class="Symbol"
      >:</a
      ><a name="12822"
      > </a
      ><a name="12823" href="Maps.html#11102" class="Function"
      >PartialMap</a
      ><a name="12833"
      > </a
      ><a name="12834" href="Maps.html#12815" class="Bound"
      >A</a
      ><a name="12835" class="Symbol"
      >)</a
      ><a name="12836"
      > </a
      ><a name="12837" class="Symbol"
      >(</a
      ><a name="12838" href="Maps.html#12838" class="Bound"
      >x</a
      ><a name="12839"
      > </a
      ><a name="12840" class="Symbol"
      >:</a
      ><a name="12841"
      > </a
      ><a name="12842" href="Maps.html#2215" class="Datatype"
      >Id</a
      ><a name="12844" class="Symbol"
      >)</a
      ><a name="12845"
      > </a
      ><a name="12846" class="Symbol"
      >(</a
      ><a name="12847" href="Maps.html#12847" class="Bound"
      >v</a
      ><a name="12848"
      > </a
      ><a name="12849" class="Symbol"
      >:</a
      ><a name="12850"
      > </a
      ><a name="12851" href="Maps.html#12815" class="Bound"
      >A</a
      ><a name="12852" class="Symbol"
      >)</a
      ><a name="12853"
      > 
              </a
      ><a name="12869" class="Symbol"
      >&#8594;</a
      ><a name="12870"
      > </a
      ><a name="12871" href="Maps.html#12819" class="Bound"
      >&#961;</a
      ><a name="12872"
      > </a
      ><a name="12873" href="Maps.html#12838" class="Bound"
      >x</a
      ><a name="12874"
      > </a
      ><a name="12875" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="12876"
      > </a
      ><a name="12877" href="https://agda.github.io/agda-stdlib/Data.Maybe.Base.html#373" class="InductiveConstructor"
      >just</a
      ><a name="12881"
      > </a
      ><a name="12882" href="Maps.html#12847" class="Bound"
      >v</a
      ><a name="12883"
      >
              </a
      ><a name="12898" class="Symbol"
      >&#8594;</a
      ><a name="12899"
      > </a
      ><a name="12900" class="Symbol"
      >(</a
      ><a name="12901" href="Maps.html#12819" class="Bound"
      >&#961;</a
      ><a name="12902"
      > </a
      ><a name="12903" href="Maps.html#11317" class="Function Operator"
      >,</a
      ><a name="12904"
      > </a
      ><a name="12905" href="Maps.html#12838" class="Bound"
      >x</a
      ><a name="12906"
      > </a
      ><a name="12907" href="Maps.html#11317" class="Function Operator"
      >&#8614;</a
      ><a name="12908"
      > </a
      ><a name="12909" href="Maps.html#12847" class="Bound"
      >v</a
      ><a name="12910" class="Symbol"
      >)</a
      ><a name="12911"
      > </a
      ><a name="12912" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="12913"
      > </a
      ><a name="12914" href="Maps.html#12819" class="Bound"
      >&#961;</a
      ><a name="12915"
      >
  </a
      ><a name="12918" href="Maps.html#12798" class="Function"
      >update-same</a
      ><a name="12929"
      > </a
      ><a name="12930" href="Maps.html#12930" class="Bound"
      >&#961;</a
      ><a name="12931"
      > </a
      ><a name="12932" href="Maps.html#12932" class="Bound"
      >x</a
      ><a name="12933"
      > </a
      ><a name="12934" href="Maps.html#12934" class="Bound"
      >v</a
      ><a name="12935"
      > </a
      ><a name="12936" href="Maps.html#12936" class="Bound"
      >&#961;x&#8801;v</a
      ><a name="12940"
      > </a
      ><a name="12941" class="Keyword"
      >rewrite</a
      ><a name="12948"
      > </a
      ><a name="12949" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.Core.html#565" class="Function"
      >sym</a
      ><a name="12952"
      > </a
      ><a name="12953" href="Maps.html#12936" class="Bound"
      >&#961;x&#8801;v</a
      ><a name="12957"
      > </a
      ><a name="12958" class="Symbol"
      >=</a
      ><a name="12959"
      > </a
      ><a name="12960" href="Maps.html#8922" class="Postulate"
      >TotalMap.update-same</a
      ><a name="12980"
      > </a
      ><a name="12981" href="Maps.html#12930" class="Bound"
      >&#961;</a
      ><a name="12982"
      > </a
      ><a name="12983" href="Maps.html#12932" class="Bound"
      >x</a
      >

</pre>

<pre class="Agda">

  <a name="13012" href="Maps.html#13012" class="Function"
      >update-permute</a
      ><a name="13026"
      > </a
      ><a name="13027" class="Symbol"
      >:</a
      ><a name="13028"
      > </a
      ><a name="13029" class="Symbol"
      >&#8704;</a
      ><a name="13030"
      > </a
      ><a name="13031" class="Symbol"
      >{</a
      ><a name="13032" href="Maps.html#13032" class="Bound"
      >A</a
      ><a name="13033" class="Symbol"
      >}</a
      ><a name="13034"
      > </a
      ><a name="13035" class="Symbol"
      >(</a
      ><a name="13036" href="Maps.html#13036" class="Bound"
      >&#961;</a
      ><a name="13037"
      > </a
      ><a name="13038" class="Symbol"
      >:</a
      ><a name="13039"
      > </a
      ><a name="13040" href="Maps.html#11102" class="Function"
      >PartialMap</a
      ><a name="13050"
      > </a
      ><a name="13051" href="Maps.html#13032" class="Bound"
      >A</a
      ><a name="13052" class="Symbol"
      >)</a
      ><a name="13053"
      > </a
      ><a name="13054" class="Symbol"
      >(</a
      ><a name="13055" href="Maps.html#13055" class="Bound"
      >x</a
      ><a name="13056"
      > </a
      ><a name="13057" class="Symbol"
      >:</a
      ><a name="13058"
      > </a
      ><a name="13059" href="Maps.html#2215" class="Datatype"
      >Id</a
      ><a name="13061" class="Symbol"
      >)</a
      ><a name="13062"
      > </a
      ><a name="13063" class="Symbol"
      >(</a
      ><a name="13064" href="Maps.html#13064" class="Bound"
      >v</a
      ><a name="13065"
      > </a
      ><a name="13066" class="Symbol"
      >:</a
      ><a name="13067"
      > </a
      ><a name="13068" href="Maps.html#13032" class="Bound"
      >A</a
      ><a name="13069" class="Symbol"
      >)</a
      ><a name="13070"
      > </a
      ><a name="13071" class="Symbol"
      >(</a
      ><a name="13072" href="Maps.html#13072" class="Bound"
      >y</a
      ><a name="13073"
      > </a
      ><a name="13074" class="Symbol"
      >:</a
      ><a name="13075"
      > </a
      ><a name="13076" href="Maps.html#2215" class="Datatype"
      >Id</a
      ><a name="13078" class="Symbol"
      >)</a
      ><a name="13079"
      > </a
      ><a name="13080" class="Symbol"
      >(</a
      ><a name="13081" href="Maps.html#13081" class="Bound"
      >w</a
      ><a name="13082"
      > </a
      ><a name="13083" class="Symbol"
      >:</a
      ><a name="13084"
      > </a
      ><a name="13085" href="Maps.html#13032" class="Bound"
      >A</a
      ><a name="13086" class="Symbol"
      >)</a
      ><a name="13087"
      > 
                 </a
      ><a name="13106" class="Symbol"
      >&#8594;</a
      ><a name="13107"
      > </a
      ><a name="13108" href="Maps.html#13055" class="Bound"
      >x</a
      ><a name="13109"
      > </a
      ><a name="13110" href="https://agda.github.io/agda-stdlib/Relation.Binary.Core.html#4493" class="Function Operator"
      >&#8802;</a
      ><a name="13111"
      > </a
      ><a name="13112" href="Maps.html#13072" class="Bound"
      >y</a
      ><a name="13113"
      > </a
      ><a name="13114" class="Symbol"
      >&#8594;</a
      ><a name="13115"
      > </a
      ><a name="13116" class="Symbol"
      >(</a
      ><a name="13117" href="Maps.html#13036" class="Bound"
      >&#961;</a
      ><a name="13118"
      > </a
      ><a name="13119" href="Maps.html#11538" class="Function Operator"
      >,</a
      ><a name="13120"
      > </a
      ><a name="13121" href="Maps.html#13055" class="Bound"
      >x</a
      ><a name="13122"
      > </a
      ><a name="13123" href="Maps.html#11538" class="Function Operator"
      >&#8614;</a
      ><a name="13124"
      > </a
      ><a name="13125" href="Maps.html#13064" class="Bound"
      >v</a
      ><a name="13126"
      > </a
      ><a name="13127" href="Maps.html#11538" class="Function Operator"
      >,</a
      ><a name="13128"
      > </a
      ><a name="13129" href="Maps.html#13072" class="Bound"
      >y</a
      ><a name="13130"
      > </a
      ><a name="13131" href="Maps.html#11538" class="Function Operator"
      >&#8614;</a
      ><a name="13132"
      > </a
      ><a name="13133" href="Maps.html#13081" class="Bound"
      >w</a
      ><a name="13134" class="Symbol"
      >)</a
      ><a name="13135"
      > </a
      ><a name="13136" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="13137"
      > </a
      ><a name="13138" class="Symbol"
      >(</a
      ><a name="13139" href="Maps.html#13036" class="Bound"
      >&#961;</a
      ><a name="13140"
      > </a
      ><a name="13141" href="Maps.html#11538" class="Function Operator"
      >,</a
      ><a name="13142"
      > </a
      ><a name="13143" href="Maps.html#13072" class="Bound"
      >y</a
      ><a name="13144"
      > </a
      ><a name="13145" href="Maps.html#11538" class="Function Operator"
      >&#8614;</a
      ><a name="13146"
      > </a
      ><a name="13147" href="Maps.html#13081" class="Bound"
      >w</a
      ><a name="13148"
      > </a
      ><a name="13149" href="Maps.html#11538" class="Function Operator"
      >,</a
      ><a name="13150"
      > </a
      ><a name="13151" href="Maps.html#13055" class="Bound"
      >x</a
      ><a name="13152"
      > </a
      ><a name="13153" href="Maps.html#11538" class="Function Operator"
      >&#8614;</a
      ><a name="13154"
      > </a
      ><a name="13155" href="Maps.html#13064" class="Bound"
      >v</a
      ><a name="13156" class="Symbol"
      >)</a
      ><a name="13157"
      >
  </a
      ><a name="13160" href="Maps.html#13012" class="Function"
      >update-permute</a
      ><a name="13174"
      > </a
      ><a name="13175" href="Maps.html#13175" class="Bound"
      >&#961;</a
      ><a name="13176"
      > </a
      ><a name="13177" href="Maps.html#13177" class="Bound"
      >x</a
      ><a name="13178"
      > </a
      ><a name="13179" href="Maps.html#13179" class="Bound"
      >v</a
      ><a name="13180"
      > </a
      ><a name="13181" href="Maps.html#13181" class="Bound"
      >y</a
      ><a name="13182"
      > </a
      ><a name="13183" href="Maps.html#13183" class="Bound"
      >w</a
      ><a name="13184"
      > </a
      ><a name="13185" href="Maps.html#13185" class="Bound"
      >x&#8802;y</a
      ><a name="13188"
      > </a
      ><a name="13189" class="Symbol"
      >=</a
      ><a name="13190"
      > </a
      ><a name="13191" href="Maps.html#9524" class="Postulate"
      >TotalMap.update-permute</a
      ><a name="13214"
      > </a
      ><a name="13215" href="Maps.html#13175" class="Bound"
      >&#961;</a
      ><a name="13216"
      > </a
      ><a name="13217" href="Maps.html#13177" class="Bound"
      >x</a
      ><a name="13218"
      > </a
      ><a name="13219" class="Symbol"
      >(</a
      ><a name="13220" href="https://agda.github.io/agda-stdlib/Data.Maybe.Base.html#373" class="InductiveConstructor"
      >just</a
      ><a name="13224"
      > </a
      ><a name="13225" href="Maps.html#13179" class="Bound"
      >v</a
      ><a name="13226" class="Symbol"
      >)</a
      ><a name="13227"
      > </a
      ><a name="13228" href="Maps.html#13181" class="Bound"
      >y</a
      ><a name="13229"
      > </a
      ><a name="13230" class="Symbol"
      >(</a
      ><a name="13231" href="https://agda.github.io/agda-stdlib/Data.Maybe.Base.html#373" class="InductiveConstructor"
      >just</a
      ><a name="13235"
      > </a
      ><a name="13236" href="Maps.html#13183" class="Bound"
      >w</a
      ><a name="13237" class="Symbol"
      >)</a
      ><a name="13238"
      > </a
      ><a name="13239" href="Maps.html#13185" class="Bound"
      >x&#8802;y</a
      >

</pre>
