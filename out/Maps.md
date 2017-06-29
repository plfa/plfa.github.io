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
{% endraw %}</pre>

Documentation for the standard library can be found at
<https://agda.github.io/agda-stdlib/>.

## Identifiers

First, we need a type for the keys that we use to index into our
maps.  For this purpose, we again use the type `Id` from the
[Lists](sf/Lists.html) chapter.  To make this chapter self contained,
we repeat its definition here.

<pre class="Agda">{% raw %}
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
{% endraw %}</pre>

We recall a standard fact of logic.

<pre class="Agda">{% raw %}
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
{% endraw %}</pre>

Using the above, we can decide equality of two identifiers
by deciding equality on the underlying strings.

<pre class="Agda">{% raw %}
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
{% endraw %}</pre>

We define some identifiers for future use.

<pre class="Agda">{% raw %}
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
{% endraw %}</pre>

Intuitively, a total map over anﬁ element type `A` _is_ just a
function that can be used to look up ids, yielding `A`s.

<pre class="Agda">{% raw %}
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
{% endraw %}</pre>

The function `always` yields a total map given a
default element; this map always returns the default element when
applied to any id.

<pre class="Agda">{% raw %}
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
{% endraw %}</pre>

More interesting is the update function, which (as before) takes
a map `ρ`, a key `x`, and a value `v` and returns a new map that
takes `x` to `v` and takes every other key to whatever `ρ` does.

<pre class="Agda">{% raw %}
  <a name="4381" class="Keyword"
      >infixl</a
      ><a name="4387"
      > </a
      ><a name="4388" class="Number"
      >15</a
      ><a name="4390"
      > </a
      ><a name="4391" href="Maps.html#4402" class="Function Operator"
      >_,_&#8614;_</a
      ><a name="4396"
      >  

  </a
      ><a name="4402" href="Maps.html#4402" class="Function Operator"
      >_,_&#8614;_</a
      ><a name="4407"
      > </a
      ><a name="4408" class="Symbol"
      >:</a
      ><a name="4409"
      > </a
      ><a name="4410" class="Symbol"
      >&#8704;</a
      ><a name="4411"
      > </a
      ><a name="4412" class="Symbol"
      >{</a
      ><a name="4413" href="Maps.html#4413" class="Bound"
      >A</a
      ><a name="4414" class="Symbol"
      >}</a
      ><a name="4415"
      > </a
      ><a name="4416" class="Symbol"
      >&#8594;</a
      ><a name="4417"
      > </a
      ><a name="4418" href="Maps.html#3738" class="Function"
      >TotalMap</a
      ><a name="4426"
      > </a
      ><a name="4427" href="Maps.html#4413" class="Bound"
      >A</a
      ><a name="4428"
      > </a
      ><a name="4429" class="Symbol"
      >&#8594;</a
      ><a name="4430"
      > </a
      ><a name="4431" href="Maps.html#2215" class="Datatype"
      >Id</a
      ><a name="4433"
      > </a
      ><a name="4434" class="Symbol"
      >&#8594;</a
      ><a name="4435"
      > </a
      ><a name="4436" href="Maps.html#4413" class="Bound"
      >A</a
      ><a name="4437"
      > </a
      ><a name="4438" class="Symbol"
      >&#8594;</a
      ><a name="4439"
      > </a
      ><a name="4440" href="Maps.html#3738" class="Function"
      >TotalMap</a
      ><a name="4448"
      > </a
      ><a name="4449" href="Maps.html#4413" class="Bound"
      >A</a
      ><a name="4450"
      >
  </a
      ><a name="4453" class="Symbol"
      >(</a
      ><a name="4454" href="Maps.html#4454" class="Bound"
      >&#961;</a
      ><a name="4455"
      > </a
      ><a name="4456" href="Maps.html#4402" class="Function Operator"
      >,</a
      ><a name="4457"
      > </a
      ><a name="4458" href="Maps.html#4458" class="Bound"
      >x</a
      ><a name="4459"
      > </a
      ><a name="4460" href="Maps.html#4402" class="Function Operator"
      >&#8614;</a
      ><a name="4461"
      > </a
      ><a name="4462" href="Maps.html#4462" class="Bound"
      >v</a
      ><a name="4463" class="Symbol"
      >)</a
      ><a name="4464"
      > </a
      ><a name="4465" href="Maps.html#4465" class="Bound"
      >y</a
      ><a name="4466"
      > </a
      ><a name="4467" class="Keyword"
      >with</a
      ><a name="4471"
      > </a
      ><a name="4472" href="Maps.html#4458" class="Bound"
      >x</a
      ><a name="4473"
      > </a
      ><a name="4474" href="Maps.html#2558" class="Function Operator"
      >&#8799;</a
      ><a name="4475"
      > </a
      ><a name="4476" href="Maps.html#4465" class="Bound"
      >y</a
      ><a name="4477"
      >
  </a
      ><a name="4480" class="Symbol"
      >...</a
      ><a name="4483"
      > </a
      ><a name="4484" class="Symbol"
      >|</a
      ><a name="4485"
      > </a
      ><a name="4486" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#520" class="InductiveConstructor"
      >yes</a
      ><a name="4489"
      > </a
      ><a name="4490" href="Maps.html#4490" class="Bound"
      >x=y</a
      ><a name="4493"
      > </a
      ><a name="4494" class="Symbol"
      >=</a
      ><a name="4495"
      > </a
      ><a name="4496" href="Maps.html#4462" class="Bound"
      >v</a
      ><a name="4497"
      >
  </a
      ><a name="4500" class="Symbol"
      >...</a
      ><a name="4503"
      > </a
      ><a name="4504" class="Symbol"
      >|</a
      ><a name="4505"
      > </a
      ><a name="4506" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#547" class="InductiveConstructor"
      >no</a
      ><a name="4508"
      >  </a
      ><a name="4510" href="Maps.html#4510" class="Bound"
      >x&#8800;y</a
      ><a name="4513"
      > </a
      ><a name="4514" class="Symbol"
      >=</a
      ><a name="4515"
      > </a
      ><a name="4516" href="Maps.html#4454" class="Bound"
      >&#961;</a
      ><a name="4517"
      > </a
      ><a name="4518" href="Maps.html#4465" class="Bound"
      >y</a
      >
{% endraw %}</pre>

This definition is a nice example of higher-order programming.
The update function takes a _function_ `ρ` and yields a new
function that behaves like the desired map.

For example, we can build a map taking ids to naturals, where `x`
maps to 42, `y` maps to 69, and every other key maps to 0, as follows:

<pre class="Agda">{% raw %}
  <a name="4853" href="Maps.html#4853" class="Function"
      >&#961;&#8320;</a
      ><a name="4855"
      > </a
      ><a name="4856" class="Symbol"
      >:</a
      ><a name="4857"
      > </a
      ><a name="4858" href="Maps.html#3738" class="Function"
      >TotalMap</a
      ><a name="4866"
      > </a
      ><a name="4867" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#97" class="Datatype"
      >&#8469;</a
      ><a name="4868"
      >
  </a
      ><a name="4871" href="Maps.html#4853" class="Function"
      >&#961;&#8320;</a
      ><a name="4873"
      > </a
      ><a name="4874" class="Symbol"
      >=</a
      ><a name="4875"
      > </a
      ><a name="4876" href="Maps.html#4109" class="Function"
      >always</a
      ><a name="4882"
      > </a
      ><a name="4883" class="Number"
      >0</a
      ><a name="4884"
      > </a
      ><a name="4885" href="Maps.html#4402" class="Function Operator"
      >,</a
      ><a name="4886"
      > </a
      ><a name="4887" href="Maps.html#2863" class="Function"
      >x</a
      ><a name="4888"
      > </a
      ><a name="4889" href="Maps.html#4402" class="Function Operator"
      >&#8614;</a
      ><a name="4890"
      > </a
      ><a name="4891" class="Number"
      >42</a
      ><a name="4893"
      > </a
      ><a name="4894" href="Maps.html#4402" class="Function Operator"
      >,</a
      ><a name="4895"
      > </a
      ><a name="4896" href="Maps.html#2865" class="Function"
      >y</a
      ><a name="4897"
      > </a
      ><a name="4898" href="Maps.html#4402" class="Function Operator"
      >&#8614;</a
      ><a name="4899"
      > </a
      ><a name="4900" class="Number"
      >69</a
      >
{% endraw %}</pre>

This completes the definition of total maps.  Note that we don't
need to define a `find` operation because it is just function
application!

<pre class="Agda">{% raw %}
  <a name="5071" href="Maps.html#5071" class="Function"
      >test&#8321;</a
      ><a name="5076"
      > </a
      ><a name="5077" class="Symbol"
      >:</a
      ><a name="5078"
      > </a
      ><a name="5079" href="Maps.html#4853" class="Function"
      >&#961;&#8320;</a
      ><a name="5081"
      > </a
      ><a name="5082" href="Maps.html#2863" class="Function"
      >x</a
      ><a name="5083"
      > </a
      ><a name="5084" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="5085"
      > </a
      ><a name="5086" class="Number"
      >42</a
      ><a name="5088"
      >
  </a
      ><a name="5091" href="Maps.html#5071" class="Function"
      >test&#8321;</a
      ><a name="5096"
      > </a
      ><a name="5097" class="Symbol"
      >=</a
      ><a name="5098"
      > </a
      ><a name="5099" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="5103"
      >

  </a
      ><a name="5107" href="Maps.html#5107" class="Function"
      >test&#8322;</a
      ><a name="5112"
      > </a
      ><a name="5113" class="Symbol"
      >:</a
      ><a name="5114"
      > </a
      ><a name="5115" href="Maps.html#4853" class="Function"
      >&#961;&#8320;</a
      ><a name="5117"
      > </a
      ><a name="5118" href="Maps.html#2865" class="Function"
      >y</a
      ><a name="5119"
      > </a
      ><a name="5120" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="5121"
      > </a
      ><a name="5122" class="Number"
      >69</a
      ><a name="5124"
      >
  </a
      ><a name="5127" href="Maps.html#5107" class="Function"
      >test&#8322;</a
      ><a name="5132"
      > </a
      ><a name="5133" class="Symbol"
      >=</a
      ><a name="5134"
      > </a
      ><a name="5135" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="5139"
      >

  </a
      ><a name="5143" href="Maps.html#5143" class="Function"
      >test&#8323;</a
      ><a name="5148"
      > </a
      ><a name="5149" class="Symbol"
      >:</a
      ><a name="5150"
      > </a
      ><a name="5151" href="Maps.html#4853" class="Function"
      >&#961;&#8320;</a
      ><a name="5153"
      > </a
      ><a name="5154" href="Maps.html#2867" class="Function"
      >z</a
      ><a name="5155"
      > </a
      ><a name="5156" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="5157"
      > </a
      ><a name="5158" class="Number"
      >0</a
      ><a name="5159"
      >
  </a
      ><a name="5162" href="Maps.html#5143" class="Function"
      >test&#8323;</a
      ><a name="5167"
      > </a
      ><a name="5168" class="Symbol"
      >=</a
      ><a name="5169"
      > </a
      ><a name="5170" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      >
{% endraw %}</pre>

To use maps in later chapters, we'll need several fundamental
facts about how they behave.  Even if you don't work the following
exercises, make sure you understand the statements of
the lemmas!

#### Exercise: 1 star, optional (apply-always)
The `always` map returns its default element for all keys:

<pre class="Agda">{% raw %}
  <a name="5505" class="Keyword"
      >postulate</a
      ><a name="5514"
      >
    </a
      ><a name="5519" href="Maps.html#5519" class="Postulate"
      >apply-always</a
      ><a name="5531"
      > </a
      ><a name="5532" class="Symbol"
      >:</a
      ><a name="5533"
      > </a
      ><a name="5534" class="Symbol"
      >&#8704;</a
      ><a name="5535"
      > </a
      ><a name="5536" class="Symbol"
      >{</a
      ><a name="5537" href="Maps.html#5537" class="Bound"
      >A</a
      ><a name="5538" class="Symbol"
      >}</a
      ><a name="5539"
      > </a
      ><a name="5540" class="Symbol"
      >(</a
      ><a name="5541" href="Maps.html#5541" class="Bound"
      >v</a
      ><a name="5542"
      > </a
      ><a name="5543" class="Symbol"
      >:</a
      ><a name="5544"
      > </a
      ><a name="5545" href="Maps.html#5537" class="Bound"
      >A</a
      ><a name="5546" class="Symbol"
      >)</a
      ><a name="5547"
      > </a
      ><a name="5548" class="Symbol"
      >(</a
      ><a name="5549" href="Maps.html#5549" class="Bound"
      >x</a
      ><a name="5550"
      > </a
      ><a name="5551" class="Symbol"
      >:</a
      ><a name="5552"
      > </a
      ><a name="5553" href="Maps.html#2215" class="Datatype"
      >Id</a
      ><a name="5555" class="Symbol"
      >)</a
      ><a name="5556"
      > </a
      ><a name="5557" class="Symbol"
      >&#8594;</a
      ><a name="5558"
      > </a
      ><a name="5559" href="Maps.html#4109" class="Function"
      >always</a
      ><a name="5565"
      > </a
      ><a name="5566" href="Maps.html#5541" class="Bound"
      >v</a
      ><a name="5567"
      > </a
      ><a name="5568" href="Maps.html#5549" class="Bound"
      >x</a
      ><a name="5569"
      > </a
      ><a name="5570" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="5571"
      > </a
      ><a name="5572" href="Maps.html#5541" class="Bound"
      >v</a
      >
{% endraw %}</pre>

<div class="hidden">
<pre class="Agda">{% raw %}
  <a name="5622" href="Maps.html#5622" class="Function"
      >apply-always&#8242;</a
      ><a name="5635"
      > </a
      ><a name="5636" class="Symbol"
      >:</a
      ><a name="5637"
      > </a
      ><a name="5638" class="Symbol"
      >&#8704;</a
      ><a name="5639"
      > </a
      ><a name="5640" class="Symbol"
      >{</a
      ><a name="5641" href="Maps.html#5641" class="Bound"
      >A</a
      ><a name="5642" class="Symbol"
      >}</a
      ><a name="5643"
      > </a
      ><a name="5644" class="Symbol"
      >(</a
      ><a name="5645" href="Maps.html#5645" class="Bound"
      >v</a
      ><a name="5646"
      > </a
      ><a name="5647" class="Symbol"
      >:</a
      ><a name="5648"
      > </a
      ><a name="5649" href="Maps.html#5641" class="Bound"
      >A</a
      ><a name="5650" class="Symbol"
      >)</a
      ><a name="5651"
      > </a
      ><a name="5652" class="Symbol"
      >(</a
      ><a name="5653" href="Maps.html#5653" class="Bound"
      >x</a
      ><a name="5654"
      > </a
      ><a name="5655" class="Symbol"
      >:</a
      ><a name="5656"
      > </a
      ><a name="5657" href="Maps.html#2215" class="Datatype"
      >Id</a
      ><a name="5659" class="Symbol"
      >)</a
      ><a name="5660"
      > </a
      ><a name="5661" class="Symbol"
      >&#8594;</a
      ><a name="5662"
      > </a
      ><a name="5663" href="Maps.html#4109" class="Function"
      >always</a
      ><a name="5669"
      > </a
      ><a name="5670" href="Maps.html#5645" class="Bound"
      >v</a
      ><a name="5671"
      > </a
      ><a name="5672" href="Maps.html#5653" class="Bound"
      >x</a
      ><a name="5673"
      > </a
      ><a name="5674" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="5675"
      > </a
      ><a name="5676" href="Maps.html#5645" class="Bound"
      >v</a
      ><a name="5677"
      >
  </a
      ><a name="5680" href="Maps.html#5622" class="Function"
      >apply-always&#8242;</a
      ><a name="5693"
      > </a
      ><a name="5694" href="Maps.html#5694" class="Bound"
      >v</a
      ><a name="5695"
      > </a
      ><a name="5696" href="Maps.html#5696" class="Bound"
      >x</a
      ><a name="5697"
      > </a
      ><a name="5698" class="Symbol"
      >=</a
      ><a name="5699"
      > </a
      ><a name="5700" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      >
{% endraw %}</pre>
</div>

#### Exercise: 2 stars, optional (update-eq)
Next, if we update a map `ρ` at a key `x` with a new value `v`
and then look up `x` in the map resulting from the update, we get
back `v`:

<pre class="Agda">{% raw %}
  <a name="5924" class="Keyword"
      >postulate</a
      ><a name="5933"
      >
    </a
      ><a name="5938" href="Maps.html#5938" class="Postulate"
      >update-eq</a
      ><a name="5947"
      > </a
      ><a name="5948" class="Symbol"
      >:</a
      ><a name="5949"
      > </a
      ><a name="5950" class="Symbol"
      >&#8704;</a
      ><a name="5951"
      > </a
      ><a name="5952" class="Symbol"
      >{</a
      ><a name="5953" href="Maps.html#5953" class="Bound"
      >A</a
      ><a name="5954" class="Symbol"
      >}</a
      ><a name="5955"
      > </a
      ><a name="5956" class="Symbol"
      >(</a
      ><a name="5957" href="Maps.html#5957" class="Bound"
      >&#961;</a
      ><a name="5958"
      > </a
      ><a name="5959" class="Symbol"
      >:</a
      ><a name="5960"
      > </a
      ><a name="5961" href="Maps.html#3738" class="Function"
      >TotalMap</a
      ><a name="5969"
      > </a
      ><a name="5970" href="Maps.html#5953" class="Bound"
      >A</a
      ><a name="5971" class="Symbol"
      >)</a
      ><a name="5972"
      > </a
      ><a name="5973" class="Symbol"
      >(</a
      ><a name="5974" href="Maps.html#5974" class="Bound"
      >x</a
      ><a name="5975"
      > </a
      ><a name="5976" class="Symbol"
      >:</a
      ><a name="5977"
      > </a
      ><a name="5978" href="Maps.html#2215" class="Datatype"
      >Id</a
      ><a name="5980" class="Symbol"
      >)</a
      ><a name="5981"
      > </a
      ><a name="5982" class="Symbol"
      >(</a
      ><a name="5983" href="Maps.html#5983" class="Bound"
      >v</a
      ><a name="5984"
      > </a
      ><a name="5985" class="Symbol"
      >:</a
      ><a name="5986"
      > </a
      ><a name="5987" href="Maps.html#5953" class="Bound"
      >A</a
      ><a name="5988" class="Symbol"
      >)</a
      ><a name="5989"
      >
              </a
      ><a name="6004" class="Symbol"
      >&#8594;</a
      ><a name="6005"
      > </a
      ><a name="6006" class="Symbol"
      >(</a
      ><a name="6007" href="Maps.html#5957" class="Bound"
      >&#961;</a
      ><a name="6008"
      > </a
      ><a name="6009" href="Maps.html#4402" class="Function Operator"
      >,</a
      ><a name="6010"
      > </a
      ><a name="6011" href="Maps.html#5974" class="Bound"
      >x</a
      ><a name="6012"
      > </a
      ><a name="6013" href="Maps.html#4402" class="Function Operator"
      >&#8614;</a
      ><a name="6014"
      > </a
      ><a name="6015" href="Maps.html#5983" class="Bound"
      >v</a
      ><a name="6016" class="Symbol"
      >)</a
      ><a name="6017"
      > </a
      ><a name="6018" href="Maps.html#5974" class="Bound"
      >x</a
      ><a name="6019"
      > </a
      ><a name="6020" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="6021"
      > </a
      ><a name="6022" href="Maps.html#5983" class="Bound"
      >v</a
      >
{% endraw %}</pre>

<div class="hidden">
<pre class="Agda">{% raw %}
  <a name="6072" href="Maps.html#6072" class="Function"
      >update-eq&#8242;</a
      ><a name="6082"
      > </a
      ><a name="6083" class="Symbol"
      >:</a
      ><a name="6084"
      > </a
      ><a name="6085" class="Symbol"
      >&#8704;</a
      ><a name="6086"
      > </a
      ><a name="6087" class="Symbol"
      >{</a
      ><a name="6088" href="Maps.html#6088" class="Bound"
      >A</a
      ><a name="6089" class="Symbol"
      >}</a
      ><a name="6090"
      > </a
      ><a name="6091" class="Symbol"
      >(</a
      ><a name="6092" href="Maps.html#6092" class="Bound"
      >&#961;</a
      ><a name="6093"
      > </a
      ><a name="6094" class="Symbol"
      >:</a
      ><a name="6095"
      > </a
      ><a name="6096" href="Maps.html#3738" class="Function"
      >TotalMap</a
      ><a name="6104"
      > </a
      ><a name="6105" href="Maps.html#6088" class="Bound"
      >A</a
      ><a name="6106" class="Symbol"
      >)</a
      ><a name="6107"
      > </a
      ><a name="6108" class="Symbol"
      >(</a
      ><a name="6109" href="Maps.html#6109" class="Bound"
      >x</a
      ><a name="6110"
      > </a
      ><a name="6111" class="Symbol"
      >:</a
      ><a name="6112"
      > </a
      ><a name="6113" href="Maps.html#2215" class="Datatype"
      >Id</a
      ><a name="6115" class="Symbol"
      >)</a
      ><a name="6116"
      > </a
      ><a name="6117" class="Symbol"
      >(</a
      ><a name="6118" href="Maps.html#6118" class="Bound"
      >v</a
      ><a name="6119"
      > </a
      ><a name="6120" class="Symbol"
      >:</a
      ><a name="6121"
      > </a
      ><a name="6122" href="Maps.html#6088" class="Bound"
      >A</a
      ><a name="6123" class="Symbol"
      >)</a
      ><a name="6124"
      >
             </a
      ><a name="6138" class="Symbol"
      >&#8594;</a
      ><a name="6139"
      > </a
      ><a name="6140" class="Symbol"
      >(</a
      ><a name="6141" href="Maps.html#6092" class="Bound"
      >&#961;</a
      ><a name="6142"
      > </a
      ><a name="6143" href="Maps.html#4402" class="Function Operator"
      >,</a
      ><a name="6144"
      > </a
      ><a name="6145" href="Maps.html#6109" class="Bound"
      >x</a
      ><a name="6146"
      > </a
      ><a name="6147" href="Maps.html#4402" class="Function Operator"
      >&#8614;</a
      ><a name="6148"
      > </a
      ><a name="6149" href="Maps.html#6118" class="Bound"
      >v</a
      ><a name="6150" class="Symbol"
      >)</a
      ><a name="6151"
      > </a
      ><a name="6152" href="Maps.html#6109" class="Bound"
      >x</a
      ><a name="6153"
      > </a
      ><a name="6154" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="6155"
      > </a
      ><a name="6156" href="Maps.html#6118" class="Bound"
      >v</a
      ><a name="6157"
      >
  </a
      ><a name="6160" href="Maps.html#6072" class="Function"
      >update-eq&#8242;</a
      ><a name="6170"
      > </a
      ><a name="6171" href="Maps.html#6171" class="Bound"
      >&#961;</a
      ><a name="6172"
      > </a
      ><a name="6173" href="Maps.html#6173" class="Bound"
      >x</a
      ><a name="6174"
      > </a
      ><a name="6175" href="Maps.html#6175" class="Bound"
      >v</a
      ><a name="6176"
      > </a
      ><a name="6177" class="Keyword"
      >with</a
      ><a name="6181"
      > </a
      ><a name="6182" href="Maps.html#6173" class="Bound"
      >x</a
      ><a name="6183"
      > </a
      ><a name="6184" href="Maps.html#2558" class="Function Operator"
      >&#8799;</a
      ><a name="6185"
      > </a
      ><a name="6186" href="Maps.html#6173" class="Bound"
      >x</a
      ><a name="6187"
      >
  </a
      ><a name="6190" class="Symbol"
      >...</a
      ><a name="6193"
      > </a
      ><a name="6194" class="Symbol"
      >|</a
      ><a name="6195"
      > </a
      ><a name="6196" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#520" class="InductiveConstructor"
      >yes</a
      ><a name="6199"
      > </a
      ><a name="6200" href="Maps.html#6200" class="Bound"
      >x&#8801;x</a
      ><a name="6203"
      > </a
      ><a name="6204" class="Symbol"
      >=</a
      ><a name="6205"
      > </a
      ><a name="6206" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="6210"
      >
  </a
      ><a name="6213" class="Symbol"
      >...</a
      ><a name="6216"
      > </a
      ><a name="6217" class="Symbol"
      >|</a
      ><a name="6218"
      > </a
      ><a name="6219" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#547" class="InductiveConstructor"
      >no</a
      ><a name="6221"
      >  </a
      ><a name="6223" href="Maps.html#6223" class="Bound"
      >x&#8802;x</a
      ><a name="6226"
      > </a
      ><a name="6227" class="Symbol"
      >=</a
      ><a name="6228"
      > </a
      ><a name="6229" href="https://agda.github.io/agda-stdlib/Data.Empty.html#348" class="Function"
      >&#8869;-elim</a
      ><a name="6235"
      > </a
      ><a name="6236" class="Symbol"
      >(</a
      ><a name="6237" href="Maps.html#6223" class="Bound"
      >x&#8802;x</a
      ><a name="6240"
      > </a
      ><a name="6241" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="6245" class="Symbol"
      >)</a
      >
{% endraw %}</pre>
</div>

#### Exercise: 2 stars, optional (update-neq)
On the other hand, if we update a map `m` at a key `x` and
then look up a _different_ key `y` in the resulting map, we get
the same result that `m` would have given:

<pre class="Agda">{% raw %}
  <a name="6494" href="Maps.html#6494" class="Function"
      >update-neq</a
      ><a name="6504"
      > </a
      ><a name="6505" class="Symbol"
      >:</a
      ><a name="6506"
      > </a
      ><a name="6507" class="Symbol"
      >&#8704;</a
      ><a name="6508"
      > </a
      ><a name="6509" class="Symbol"
      >{</a
      ><a name="6510" href="Maps.html#6510" class="Bound"
      >A</a
      ><a name="6511" class="Symbol"
      >}</a
      ><a name="6512"
      > </a
      ><a name="6513" class="Symbol"
      >(</a
      ><a name="6514" href="Maps.html#6514" class="Bound"
      >&#961;</a
      ><a name="6515"
      > </a
      ><a name="6516" class="Symbol"
      >:</a
      ><a name="6517"
      > </a
      ><a name="6518" href="Maps.html#3738" class="Function"
      >TotalMap</a
      ><a name="6526"
      > </a
      ><a name="6527" href="Maps.html#6510" class="Bound"
      >A</a
      ><a name="6528" class="Symbol"
      >)</a
      ><a name="6529"
      > </a
      ><a name="6530" class="Symbol"
      >(</a
      ><a name="6531" href="Maps.html#6531" class="Bound"
      >x</a
      ><a name="6532"
      > </a
      ><a name="6533" class="Symbol"
      >:</a
      ><a name="6534"
      > </a
      ><a name="6535" href="Maps.html#2215" class="Datatype"
      >Id</a
      ><a name="6537" class="Symbol"
      >)</a
      ><a name="6538"
      > </a
      ><a name="6539" class="Symbol"
      >(</a
      ><a name="6540" href="Maps.html#6540" class="Bound"
      >v</a
      ><a name="6541"
      > </a
      ><a name="6542" class="Symbol"
      >:</a
      ><a name="6543"
      > </a
      ><a name="6544" href="Maps.html#6510" class="Bound"
      >A</a
      ><a name="6545" class="Symbol"
      >)</a
      ><a name="6546"
      > </a
      ><a name="6547" class="Symbol"
      >(</a
      ><a name="6548" href="Maps.html#6548" class="Bound"
      >y</a
      ><a name="6549"
      > </a
      ><a name="6550" class="Symbol"
      >:</a
      ><a name="6551"
      > </a
      ><a name="6552" href="Maps.html#2215" class="Datatype"
      >Id</a
      ><a name="6554" class="Symbol"
      >)</a
      ><a name="6555"
      >
             </a
      ><a name="6569" class="Symbol"
      >&#8594;</a
      ><a name="6570"
      > </a
      ><a name="6571" href="Maps.html#6531" class="Bound"
      >x</a
      ><a name="6572"
      > </a
      ><a name="6573" href="https://agda.github.io/agda-stdlib/Relation.Binary.Core.html#4493" class="Function Operator"
      >&#8802;</a
      ><a name="6574"
      > </a
      ><a name="6575" href="Maps.html#6548" class="Bound"
      >y</a
      ><a name="6576"
      > </a
      ><a name="6577" class="Symbol"
      >&#8594;</a
      ><a name="6578"
      > </a
      ><a name="6579" class="Symbol"
      >(</a
      ><a name="6580" href="Maps.html#6514" class="Bound"
      >&#961;</a
      ><a name="6581"
      > </a
      ><a name="6582" href="Maps.html#4402" class="Function Operator"
      >,</a
      ><a name="6583"
      > </a
      ><a name="6584" href="Maps.html#6531" class="Bound"
      >x</a
      ><a name="6585"
      > </a
      ><a name="6586" href="Maps.html#4402" class="Function Operator"
      >&#8614;</a
      ><a name="6587"
      > </a
      ><a name="6588" href="Maps.html#6540" class="Bound"
      >v</a
      ><a name="6589" class="Symbol"
      >)</a
      ><a name="6590"
      > </a
      ><a name="6591" href="Maps.html#6548" class="Bound"
      >y</a
      ><a name="6592"
      > </a
      ><a name="6593" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="6594"
      > </a
      ><a name="6595" href="Maps.html#6514" class="Bound"
      >&#961;</a
      ><a name="6596"
      > </a
      ><a name="6597" href="Maps.html#6548" class="Bound"
      >y</a
      ><a name="6598"
      >
  </a
      ><a name="6601" href="Maps.html#6494" class="Function"
      >update-neq</a
      ><a name="6611"
      > </a
      ><a name="6612" href="Maps.html#6612" class="Bound"
      >&#961;</a
      ><a name="6613"
      > </a
      ><a name="6614" href="Maps.html#6614" class="Bound"
      >x</a
      ><a name="6615"
      > </a
      ><a name="6616" href="Maps.html#6616" class="Bound"
      >v</a
      ><a name="6617"
      > </a
      ><a name="6618" href="Maps.html#6618" class="Bound"
      >y</a
      ><a name="6619"
      > </a
      ><a name="6620" href="Maps.html#6620" class="Bound"
      >x&#8802;y</a
      ><a name="6623"
      > </a
      ><a name="6624" class="Keyword"
      >with</a
      ><a name="6628"
      > </a
      ><a name="6629" href="Maps.html#6614" class="Bound"
      >x</a
      ><a name="6630"
      > </a
      ><a name="6631" href="Maps.html#2558" class="Function Operator"
      >&#8799;</a
      ><a name="6632"
      > </a
      ><a name="6633" href="Maps.html#6618" class="Bound"
      >y</a
      ><a name="6634"
      >
  </a
      ><a name="6637" class="Symbol"
      >...</a
      ><a name="6640"
      > </a
      ><a name="6641" class="Symbol"
      >|</a
      ><a name="6642"
      > </a
      ><a name="6643" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#520" class="InductiveConstructor"
      >yes</a
      ><a name="6646"
      > </a
      ><a name="6647" href="Maps.html#6647" class="Bound"
      >x&#8801;y</a
      ><a name="6650"
      > </a
      ><a name="6651" class="Symbol"
      >=</a
      ><a name="6652"
      > </a
      ><a name="6653" href="https://agda.github.io/agda-stdlib/Data.Empty.html#348" class="Function"
      >&#8869;-elim</a
      ><a name="6659"
      > </a
      ><a name="6660" class="Symbol"
      >(</a
      ><a name="6661" href="Maps.html#6620" class="Bound"
      >x&#8802;y</a
      ><a name="6664"
      > </a
      ><a name="6665" href="Maps.html#6647" class="Bound"
      >x&#8801;y</a
      ><a name="6668" class="Symbol"
      >)</a
      ><a name="6669"
      >
  </a
      ><a name="6672" class="Symbol"
      >...</a
      ><a name="6675"
      > </a
      ><a name="6676" class="Symbol"
      >|</a
      ><a name="6677"
      > </a
      ><a name="6678" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#547" class="InductiveConstructor"
      >no</a
      ><a name="6680"
      >  </a
      ><a name="6682" class="Symbol"
      >_</a
      ><a name="6683"
      >   </a
      ><a name="6686" class="Symbol"
      >=</a
      ><a name="6687"
      > </a
      ><a name="6688" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      >
{% endraw %}</pre>

For the following lemmas, since maps are represented by functions, to
show two maps equal we will need to postulate extensionality.

<pre class="Agda">{% raw %}
  <a name="6853" class="Keyword"
      >postulate</a
      ><a name="6862"
      >
    </a
      ><a name="6867" href="Maps.html#6867" class="Postulate"
      >extensionality</a
      ><a name="6881"
      > </a
      ><a name="6882" class="Symbol"
      >:</a
      ><a name="6883"
      > </a
      ><a name="6884" class="Symbol"
      >&#8704;</a
      ><a name="6885"
      > </a
      ><a name="6886" class="Symbol"
      >{</a
      ><a name="6887" href="Maps.html#6887" class="Bound"
      >A</a
      ><a name="6888"
      > </a
      ><a name="6889" class="Symbol"
      >:</a
      ><a name="6890"
      > </a
      ><a name="6891" class="PrimitiveType"
      >Set</a
      ><a name="6894" class="Symbol"
      >}</a
      ><a name="6895"
      > </a
      ><a name="6896" class="Symbol"
      >{</a
      ><a name="6897" href="Maps.html#6897" class="Bound"
      >&#961;</a
      ><a name="6898"
      > </a
      ><a name="6899" href="Maps.html#6899" class="Bound"
      >&#961;&#8242;</a
      ><a name="6901"
      > </a
      ><a name="6902" class="Symbol"
      >:</a
      ><a name="6903"
      > </a
      ><a name="6904" href="Maps.html#3738" class="Function"
      >TotalMap</a
      ><a name="6912"
      > </a
      ><a name="6913" href="Maps.html#6887" class="Bound"
      >A</a
      ><a name="6914" class="Symbol"
      >}</a
      ><a name="6915"
      > </a
      ><a name="6916" class="Symbol"
      >&#8594;</a
      ><a name="6917"
      > </a
      ><a name="6918" class="Symbol"
      >(&#8704;</a
      ><a name="6920"
      > </a
      ><a name="6921" href="Maps.html#6921" class="Bound"
      >x</a
      ><a name="6922"
      > </a
      ><a name="6923" class="Symbol"
      >&#8594;</a
      ><a name="6924"
      > </a
      ><a name="6925" href="Maps.html#6897" class="Bound"
      >&#961;</a
      ><a name="6926"
      > </a
      ><a name="6927" href="Maps.html#6921" class="Bound"
      >x</a
      ><a name="6928"
      > </a
      ><a name="6929" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="6930"
      > </a
      ><a name="6931" href="Maps.html#6899" class="Bound"
      >&#961;&#8242;</a
      ><a name="6933"
      > </a
      ><a name="6934" href="Maps.html#6921" class="Bound"
      >x</a
      ><a name="6935" class="Symbol"
      >)</a
      ><a name="6936"
      > </a
      ><a name="6937" class="Symbol"
      >&#8594;</a
      ><a name="6938"
      > </a
      ><a name="6939" href="Maps.html#6897" class="Bound"
      >&#961;</a
      ><a name="6940"
      > </a
      ><a name="6941" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="6942"
      > </a
      ><a name="6943" href="Maps.html#6899" class="Bound"
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
  <a name="7299" class="Keyword"
      >postulate</a
      ><a name="7308"
      >
    </a
      ><a name="7313" href="Maps.html#7313" class="Postulate"
      >update-shadow</a
      ><a name="7326"
      > </a
      ><a name="7327" class="Symbol"
      >:</a
      ><a name="7328"
      > </a
      ><a name="7329" class="Symbol"
      >&#8704;</a
      ><a name="7330"
      > </a
      ><a name="7331" class="Symbol"
      >{</a
      ><a name="7332" href="Maps.html#7332" class="Bound"
      >A</a
      ><a name="7333" class="Symbol"
      >}</a
      ><a name="7334"
      > </a
      ><a name="7335" class="Symbol"
      >(</a
      ><a name="7336" href="Maps.html#7336" class="Bound"
      >&#961;</a
      ><a name="7337"
      > </a
      ><a name="7338" class="Symbol"
      >:</a
      ><a name="7339"
      > </a
      ><a name="7340" href="Maps.html#3738" class="Function"
      >TotalMap</a
      ><a name="7348"
      > </a
      ><a name="7349" href="Maps.html#7332" class="Bound"
      >A</a
      ><a name="7350" class="Symbol"
      >)</a
      ><a name="7351"
      > </a
      ><a name="7352" class="Symbol"
      >(</a
      ><a name="7353" href="Maps.html#7353" class="Bound"
      >x</a
      ><a name="7354"
      > </a
      ><a name="7355" class="Symbol"
      >:</a
      ><a name="7356"
      > </a
      ><a name="7357" href="Maps.html#2215" class="Datatype"
      >Id</a
      ><a name="7359" class="Symbol"
      >)</a
      ><a name="7360"
      > </a
      ><a name="7361" class="Symbol"
      >(</a
      ><a name="7362" href="Maps.html#7362" class="Bound"
      >v</a
      ><a name="7363"
      > </a
      ><a name="7364" href="Maps.html#7364" class="Bound"
      >w</a
      ><a name="7365"
      > </a
      ><a name="7366" class="Symbol"
      >:</a
      ><a name="7367"
      > </a
      ><a name="7368" href="Maps.html#7332" class="Bound"
      >A</a
      ><a name="7369" class="Symbol"
      >)</a
      ><a name="7370"
      > 
                  </a
      ><a name="7390" class="Symbol"
      >&#8594;</a
      ><a name="7391"
      > </a
      ><a name="7392" class="Symbol"
      >(</a
      ><a name="7393" href="Maps.html#7336" class="Bound"
      >&#961;</a
      ><a name="7394"
      > </a
      ><a name="7395" href="Maps.html#4402" class="Function Operator"
      >,</a
      ><a name="7396"
      > </a
      ><a name="7397" href="Maps.html#7353" class="Bound"
      >x</a
      ><a name="7398"
      > </a
      ><a name="7399" href="Maps.html#4402" class="Function Operator"
      >&#8614;</a
      ><a name="7400"
      > </a
      ><a name="7401" href="Maps.html#7362" class="Bound"
      >v</a
      ><a name="7402"
      > </a
      ><a name="7403" href="Maps.html#4402" class="Function Operator"
      >,</a
      ><a name="7404"
      > </a
      ><a name="7405" href="Maps.html#7353" class="Bound"
      >x</a
      ><a name="7406"
      > </a
      ><a name="7407" href="Maps.html#4402" class="Function Operator"
      >&#8614;</a
      ><a name="7408"
      > </a
      ><a name="7409" href="Maps.html#7364" class="Bound"
      >w</a
      ><a name="7410" class="Symbol"
      >)</a
      ><a name="7411"
      > </a
      ><a name="7412" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="7413"
      > </a
      ><a name="7414" class="Symbol"
      >(</a
      ><a name="7415" href="Maps.html#7336" class="Bound"
      >&#961;</a
      ><a name="7416"
      > </a
      ><a name="7417" href="Maps.html#4402" class="Function Operator"
      >,</a
      ><a name="7418"
      > </a
      ><a name="7419" href="Maps.html#7353" class="Bound"
      >x</a
      ><a name="7420"
      > </a
      ><a name="7421" href="Maps.html#4402" class="Function Operator"
      >&#8614;</a
      ><a name="7422"
      > </a
      ><a name="7423" href="Maps.html#7364" class="Bound"
      >w</a
      ><a name="7424" class="Symbol"
      >)</a
      >
{% endraw %}</pre>

<div class="hidden">
<pre class="Agda">{% raw %}
  <a name="7474" href="Maps.html#7474" class="Function"
      >update-shadow&#8242;</a
      ><a name="7488"
      > </a
      ><a name="7489" class="Symbol"
      >:</a
      ><a name="7490"
      >  </a
      ><a name="7492" class="Symbol"
      >&#8704;</a
      ><a name="7493"
      > </a
      ><a name="7494" class="Symbol"
      >{</a
      ><a name="7495" href="Maps.html#7495" class="Bound"
      >A</a
      ><a name="7496" class="Symbol"
      >}</a
      ><a name="7497"
      > </a
      ><a name="7498" class="Symbol"
      >(</a
      ><a name="7499" href="Maps.html#7499" class="Bound"
      >&#961;</a
      ><a name="7500"
      > </a
      ><a name="7501" class="Symbol"
      >:</a
      ><a name="7502"
      > </a
      ><a name="7503" href="Maps.html#3738" class="Function"
      >TotalMap</a
      ><a name="7511"
      > </a
      ><a name="7512" href="Maps.html#7495" class="Bound"
      >A</a
      ><a name="7513" class="Symbol"
      >)</a
      ><a name="7514"
      > </a
      ><a name="7515" class="Symbol"
      >(</a
      ><a name="7516" href="Maps.html#7516" class="Bound"
      >x</a
      ><a name="7517"
      > </a
      ><a name="7518" class="Symbol"
      >:</a
      ><a name="7519"
      > </a
      ><a name="7520" href="Maps.html#2215" class="Datatype"
      >Id</a
      ><a name="7522" class="Symbol"
      >)</a
      ><a name="7523"
      > </a
      ><a name="7524" class="Symbol"
      >(</a
      ><a name="7525" href="Maps.html#7525" class="Bound"
      >v</a
      ><a name="7526"
      > </a
      ><a name="7527" href="Maps.html#7527" class="Bound"
      >w</a
      ><a name="7528"
      > </a
      ><a name="7529" class="Symbol"
      >:</a
      ><a name="7530"
      > </a
      ><a name="7531" href="Maps.html#7495" class="Bound"
      >A</a
      ><a name="7532" class="Symbol"
      >)</a
      ><a name="7533"
      > 
                  </a
      ><a name="7553" class="Symbol"
      >&#8594;</a
      ><a name="7554"
      > </a
      ><a name="7555" class="Symbol"
      >((</a
      ><a name="7557" href="Maps.html#7499" class="Bound"
      >&#961;</a
      ><a name="7558"
      > </a
      ><a name="7559" href="Maps.html#4402" class="Function Operator"
      >,</a
      ><a name="7560"
      > </a
      ><a name="7561" href="Maps.html#7516" class="Bound"
      >x</a
      ><a name="7562"
      > </a
      ><a name="7563" href="Maps.html#4402" class="Function Operator"
      >&#8614;</a
      ><a name="7564"
      > </a
      ><a name="7565" href="Maps.html#7525" class="Bound"
      >v</a
      ><a name="7566" class="Symbol"
      >)</a
      ><a name="7567"
      > </a
      ><a name="7568" href="Maps.html#4402" class="Function Operator"
      >,</a
      ><a name="7569"
      > </a
      ><a name="7570" href="Maps.html#7516" class="Bound"
      >x</a
      ><a name="7571"
      > </a
      ><a name="7572" href="Maps.html#4402" class="Function Operator"
      >&#8614;</a
      ><a name="7573"
      > </a
      ><a name="7574" href="Maps.html#7527" class="Bound"
      >w</a
      ><a name="7575" class="Symbol"
      >)</a
      ><a name="7576"
      > </a
      ><a name="7577" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="7578"
      > </a
      ><a name="7579" class="Symbol"
      >(</a
      ><a name="7580" href="Maps.html#7499" class="Bound"
      >&#961;</a
      ><a name="7581"
      > </a
      ><a name="7582" href="Maps.html#4402" class="Function Operator"
      >,</a
      ><a name="7583"
      > </a
      ><a name="7584" href="Maps.html#7516" class="Bound"
      >x</a
      ><a name="7585"
      > </a
      ><a name="7586" href="Maps.html#4402" class="Function Operator"
      >&#8614;</a
      ><a name="7587"
      > </a
      ><a name="7588" href="Maps.html#7527" class="Bound"
      >w</a
      ><a name="7589" class="Symbol"
      >)</a
      ><a name="7590"
      >
  </a
      ><a name="7593" href="Maps.html#7474" class="Function"
      >update-shadow&#8242;</a
      ><a name="7607"
      > </a
      ><a name="7608" href="Maps.html#7608" class="Bound"
      >&#961;</a
      ><a name="7609"
      > </a
      ><a name="7610" href="Maps.html#7610" class="Bound"
      >x</a
      ><a name="7611"
      > </a
      ><a name="7612" href="Maps.html#7612" class="Bound"
      >v</a
      ><a name="7613"
      > </a
      ><a name="7614" href="Maps.html#7614" class="Bound"
      >w</a
      ><a name="7615"
      > </a
      ><a name="7616" class="Symbol"
      >=</a
      ><a name="7617"
      > </a
      ><a name="7618" href="Maps.html#6867" class="Postulate"
      >extensionality</a
      ><a name="7632"
      > </a
      ><a name="7633" href="Maps.html#7653" class="Function"
      >lemma</a
      ><a name="7638"
      >
    </a
      ><a name="7643" class="Keyword"
      >where</a
      ><a name="7648"
      >
    </a
      ><a name="7653" href="Maps.html#7653" class="Function"
      >lemma</a
      ><a name="7658"
      > </a
      ><a name="7659" class="Symbol"
      >:</a
      ><a name="7660"
      > </a
      ><a name="7661" class="Symbol"
      >&#8704;</a
      ><a name="7662"
      > </a
      ><a name="7663" href="Maps.html#7663" class="Bound"
      >y</a
      ><a name="7664"
      > </a
      ><a name="7665" class="Symbol"
      >&#8594;</a
      ><a name="7666"
      > </a
      ><a name="7667" class="Symbol"
      >((</a
      ><a name="7669" href="Maps.html#7608" class="Bound"
      >&#961;</a
      ><a name="7670"
      > </a
      ><a name="7671" href="Maps.html#4402" class="Function Operator"
      >,</a
      ><a name="7672"
      > </a
      ><a name="7673" href="Maps.html#7610" class="Bound"
      >x</a
      ><a name="7674"
      > </a
      ><a name="7675" href="Maps.html#4402" class="Function Operator"
      >&#8614;</a
      ><a name="7676"
      > </a
      ><a name="7677" href="Maps.html#7612" class="Bound"
      >v</a
      ><a name="7678" class="Symbol"
      >)</a
      ><a name="7679"
      > </a
      ><a name="7680" href="Maps.html#4402" class="Function Operator"
      >,</a
      ><a name="7681"
      > </a
      ><a name="7682" href="Maps.html#7610" class="Bound"
      >x</a
      ><a name="7683"
      > </a
      ><a name="7684" href="Maps.html#4402" class="Function Operator"
      >&#8614;</a
      ><a name="7685"
      > </a
      ><a name="7686" href="Maps.html#7614" class="Bound"
      >w</a
      ><a name="7687" class="Symbol"
      >)</a
      ><a name="7688"
      > </a
      ><a name="7689" href="Maps.html#7663" class="Bound"
      >y</a
      ><a name="7690"
      > </a
      ><a name="7691" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="7692"
      > </a
      ><a name="7693" class="Symbol"
      >(</a
      ><a name="7694" href="Maps.html#7608" class="Bound"
      >&#961;</a
      ><a name="7695"
      > </a
      ><a name="7696" href="Maps.html#4402" class="Function Operator"
      >,</a
      ><a name="7697"
      > </a
      ><a name="7698" href="Maps.html#7610" class="Bound"
      >x</a
      ><a name="7699"
      > </a
      ><a name="7700" href="Maps.html#4402" class="Function Operator"
      >&#8614;</a
      ><a name="7701"
      > </a
      ><a name="7702" href="Maps.html#7614" class="Bound"
      >w</a
      ><a name="7703" class="Symbol"
      >)</a
      ><a name="7704"
      > </a
      ><a name="7705" href="Maps.html#7663" class="Bound"
      >y</a
      ><a name="7706"
      >
    </a
      ><a name="7711" href="Maps.html#7653" class="Function"
      >lemma</a
      ><a name="7716"
      > </a
      ><a name="7717" href="Maps.html#7717" class="Bound"
      >y</a
      ><a name="7718"
      > </a
      ><a name="7719" class="Keyword"
      >with</a
      ><a name="7723"
      > </a
      ><a name="7724" href="Maps.html#7610" class="Bound"
      >x</a
      ><a name="7725"
      > </a
      ><a name="7726" href="Maps.html#2558" class="Function Operator"
      >&#8799;</a
      ><a name="7727"
      > </a
      ><a name="7728" href="Maps.html#7717" class="Bound"
      >y</a
      ><a name="7729"
      >
    </a
      ><a name="7734" class="Symbol"
      >...</a
      ><a name="7737"
      > </a
      ><a name="7738" class="Symbol"
      >|</a
      ><a name="7739"
      > </a
      ><a name="7740" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#520" class="InductiveConstructor"
      >yes</a
      ><a name="7743"
      > </a
      ><a name="7744" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="7748"
      > </a
      ><a name="7749" class="Symbol"
      >=</a
      ><a name="7750"
      > </a
      ><a name="7751" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="7755"
      >
    </a
      ><a name="7760" class="Symbol"
      >...</a
      ><a name="7763"
      > </a
      ><a name="7764" class="Symbol"
      >|</a
      ><a name="7765"
      > </a
      ><a name="7766" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#547" class="InductiveConstructor"
      >no</a
      ><a name="7768"
      >  </a
      ><a name="7770" href="Maps.html#7770" class="Bound"
      >x&#8802;y</a
      ><a name="7773"
      >  </a
      ><a name="7775" class="Symbol"
      >=</a
      ><a name="7776"
      > </a
      ><a name="7777" href="Maps.html#6494" class="Function"
      >update-neq</a
      ><a name="7787"
      > </a
      ><a name="7788" href="Maps.html#7608" class="Bound"
      >&#961;</a
      ><a name="7789"
      > </a
      ><a name="7790" href="Maps.html#7610" class="Bound"
      >x</a
      ><a name="7791"
      > </a
      ><a name="7792" href="Maps.html#7612" class="Bound"
      >v</a
      ><a name="7793"
      > </a
      ><a name="7794" href="Maps.html#7717" class="Bound"
      >y</a
      ><a name="7795"
      > </a
      ><a name="7796" href="Maps.html#7770" class="Bound"
      >x&#8802;y</a
      >
{% endraw %}</pre>
</div>

#### Exercise: 2 stars (update-same)
Prove the following theorem, which states that if we update a map `ρ` to
assign key `x` the same value as it already has in `ρ`, then the
result is equal to `ρ`:

<pre class="Agda">{% raw %}
  <a name="8034" class="Keyword"
      >postulate</a
      ><a name="8043"
      >
    </a
      ><a name="8048" href="Maps.html#8048" class="Postulate"
      >update-same</a
      ><a name="8059"
      > </a
      ><a name="8060" class="Symbol"
      >:</a
      ><a name="8061"
      > </a
      ><a name="8062" class="Symbol"
      >&#8704;</a
      ><a name="8063"
      > </a
      ><a name="8064" class="Symbol"
      >{</a
      ><a name="8065" href="Maps.html#8065" class="Bound"
      >A</a
      ><a name="8066" class="Symbol"
      >}</a
      ><a name="8067"
      > </a
      ><a name="8068" class="Symbol"
      >(</a
      ><a name="8069" href="Maps.html#8069" class="Bound"
      >&#961;</a
      ><a name="8070"
      > </a
      ><a name="8071" class="Symbol"
      >:</a
      ><a name="8072"
      > </a
      ><a name="8073" href="Maps.html#3738" class="Function"
      >TotalMap</a
      ><a name="8081"
      > </a
      ><a name="8082" href="Maps.html#8065" class="Bound"
      >A</a
      ><a name="8083" class="Symbol"
      >)</a
      ><a name="8084"
      > </a
      ><a name="8085" class="Symbol"
      >(</a
      ><a name="8086" href="Maps.html#8086" class="Bound"
      >x</a
      ><a name="8087"
      > </a
      ><a name="8088" class="Symbol"
      >:</a
      ><a name="8089"
      > </a
      ><a name="8090" href="Maps.html#2215" class="Datatype"
      >Id</a
      ><a name="8092" class="Symbol"
      >)</a
      ><a name="8093"
      > </a
      ><a name="8094" class="Symbol"
      >&#8594;</a
      ><a name="8095"
      > </a
      ><a name="8096" class="Symbol"
      >(</a
      ><a name="8097" href="Maps.html#8069" class="Bound"
      >&#961;</a
      ><a name="8098"
      > </a
      ><a name="8099" href="Maps.html#4402" class="Function Operator"
      >,</a
      ><a name="8100"
      > </a
      ><a name="8101" href="Maps.html#8086" class="Bound"
      >x</a
      ><a name="8102"
      > </a
      ><a name="8103" href="Maps.html#4402" class="Function Operator"
      >&#8614;</a
      ><a name="8104"
      > </a
      ><a name="8105" href="Maps.html#8069" class="Bound"
      >&#961;</a
      ><a name="8106"
      > </a
      ><a name="8107" href="Maps.html#8086" class="Bound"
      >x</a
      ><a name="8108" class="Symbol"
      >)</a
      ><a name="8109"
      > </a
      ><a name="8110" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="8111"
      > </a
      ><a name="8112" href="Maps.html#8069" class="Bound"
      >&#961;</a
      >
{% endraw %}</pre>

<div class="hidden">
<pre class="Agda">{% raw %}
  <a name="8162" href="Maps.html#8162" class="Function"
      >update-same&#8242;</a
      ><a name="8174"
      > </a
      ><a name="8175" class="Symbol"
      >:</a
      ><a name="8176"
      > </a
      ><a name="8177" class="Symbol"
      >&#8704;</a
      ><a name="8178"
      > </a
      ><a name="8179" class="Symbol"
      >{</a
      ><a name="8180" href="Maps.html#8180" class="Bound"
      >A</a
      ><a name="8181" class="Symbol"
      >}</a
      ><a name="8182"
      > </a
      ><a name="8183" class="Symbol"
      >(</a
      ><a name="8184" href="Maps.html#8184" class="Bound"
      >&#961;</a
      ><a name="8185"
      > </a
      ><a name="8186" class="Symbol"
      >:</a
      ><a name="8187"
      > </a
      ><a name="8188" href="Maps.html#3738" class="Function"
      >TotalMap</a
      ><a name="8196"
      > </a
      ><a name="8197" href="Maps.html#8180" class="Bound"
      >A</a
      ><a name="8198" class="Symbol"
      >)</a
      ><a name="8199"
      > </a
      ><a name="8200" class="Symbol"
      >(</a
      ><a name="8201" href="Maps.html#8201" class="Bound"
      >x</a
      ><a name="8202"
      > </a
      ><a name="8203" class="Symbol"
      >:</a
      ><a name="8204"
      > </a
      ><a name="8205" href="Maps.html#2215" class="Datatype"
      >Id</a
      ><a name="8207" class="Symbol"
      >)</a
      ><a name="8208"
      > </a
      ><a name="8209" class="Symbol"
      >&#8594;</a
      ><a name="8210"
      > </a
      ><a name="8211" class="Symbol"
      >(</a
      ><a name="8212" href="Maps.html#8184" class="Bound"
      >&#961;</a
      ><a name="8213"
      > </a
      ><a name="8214" href="Maps.html#4402" class="Function Operator"
      >,</a
      ><a name="8215"
      > </a
      ><a name="8216" href="Maps.html#8201" class="Bound"
      >x</a
      ><a name="8217"
      > </a
      ><a name="8218" href="Maps.html#4402" class="Function Operator"
      >&#8614;</a
      ><a name="8219"
      > </a
      ><a name="8220" href="Maps.html#8184" class="Bound"
      >&#961;</a
      ><a name="8221"
      > </a
      ><a name="8222" href="Maps.html#8201" class="Bound"
      >x</a
      ><a name="8223" class="Symbol"
      >)</a
      ><a name="8224"
      > </a
      ><a name="8225" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="8226"
      > </a
      ><a name="8227" href="Maps.html#8184" class="Bound"
      >&#961;</a
      ><a name="8228"
      >
  </a
      ><a name="8231" href="Maps.html#8162" class="Function"
      >update-same&#8242;</a
      ><a name="8243"
      > </a
      ><a name="8244" href="Maps.html#8244" class="Bound"
      >&#961;</a
      ><a name="8245"
      > </a
      ><a name="8246" href="Maps.html#8246" class="Bound"
      >x</a
      ><a name="8247"
      >  </a
      ><a name="8249" class="Symbol"
      >=</a
      ><a name="8250"
      >  </a
      ><a name="8252" href="Maps.html#6867" class="Postulate"
      >extensionality</a
      ><a name="8266"
      > </a
      ><a name="8267" href="Maps.html#8287" class="Function"
      >lemma</a
      ><a name="8272"
      >
    </a
      ><a name="8277" class="Keyword"
      >where</a
      ><a name="8282"
      >
    </a
      ><a name="8287" href="Maps.html#8287" class="Function"
      >lemma</a
      ><a name="8292"
      > </a
      ><a name="8293" class="Symbol"
      >:</a
      ><a name="8294"
      > </a
      ><a name="8295" class="Symbol"
      >&#8704;</a
      ><a name="8296"
      > </a
      ><a name="8297" href="Maps.html#8297" class="Bound"
      >y</a
      ><a name="8298"
      > </a
      ><a name="8299" class="Symbol"
      >&#8594;</a
      ><a name="8300"
      > </a
      ><a name="8301" class="Symbol"
      >(</a
      ><a name="8302" href="Maps.html#8244" class="Bound"
      >&#961;</a
      ><a name="8303"
      > </a
      ><a name="8304" href="Maps.html#4402" class="Function Operator"
      >,</a
      ><a name="8305"
      > </a
      ><a name="8306" href="Maps.html#8246" class="Bound"
      >x</a
      ><a name="8307"
      > </a
      ><a name="8308" href="Maps.html#4402" class="Function Operator"
      >&#8614;</a
      ><a name="8309"
      > </a
      ><a name="8310" href="Maps.html#8244" class="Bound"
      >&#961;</a
      ><a name="8311"
      > </a
      ><a name="8312" href="Maps.html#8246" class="Bound"
      >x</a
      ><a name="8313" class="Symbol"
      >)</a
      ><a name="8314"
      > </a
      ><a name="8315" href="Maps.html#8297" class="Bound"
      >y</a
      ><a name="8316"
      > </a
      ><a name="8317" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="8318"
      > </a
      ><a name="8319" href="Maps.html#8244" class="Bound"
      >&#961;</a
      ><a name="8320"
      > </a
      ><a name="8321" href="Maps.html#8297" class="Bound"
      >y</a
      ><a name="8322"
      >
    </a
      ><a name="8327" href="Maps.html#8287" class="Function"
      >lemma</a
      ><a name="8332"
      > </a
      ><a name="8333" href="Maps.html#8333" class="Bound"
      >y</a
      ><a name="8334"
      > </a
      ><a name="8335" class="Keyword"
      >with</a
      ><a name="8339"
      > </a
      ><a name="8340" href="Maps.html#8246" class="Bound"
      >x</a
      ><a name="8341"
      > </a
      ><a name="8342" href="Maps.html#2558" class="Function Operator"
      >&#8799;</a
      ><a name="8343"
      > </a
      ><a name="8344" href="Maps.html#8333" class="Bound"
      >y</a
      ><a name="8345"
      >
    </a
      ><a name="8350" class="Symbol"
      >...</a
      ><a name="8353"
      > </a
      ><a name="8354" class="Symbol"
      >|</a
      ><a name="8355"
      > </a
      ><a name="8356" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#520" class="InductiveConstructor"
      >yes</a
      ><a name="8359"
      > </a
      ><a name="8360" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="8364"
      > </a
      ><a name="8365" class="Symbol"
      >=</a
      ><a name="8366"
      > </a
      ><a name="8367" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="8371"
      >
    </a
      ><a name="8376" class="Symbol"
      >...</a
      ><a name="8379"
      > </a
      ><a name="8380" class="Symbol"
      >|</a
      ><a name="8381"
      > </a
      ><a name="8382" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#547" class="InductiveConstructor"
      >no</a
      ><a name="8384"
      >  </a
      ><a name="8386" href="Maps.html#8386" class="Bound"
      >x&#8802;y</a
      ><a name="8389"
      >  </a
      ><a name="8391" class="Symbol"
      >=</a
      ><a name="8392"
      > </a
      ><a name="8393" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      >
{% endraw %}</pre>
</div>

#### Exercise: 3 stars, recommended (update-permute)
Prove one final property of the `update` function: If we update a map
`m` at two distinct keys, it doesn't matter in which order we do the
updates.

<pre class="Agda">{% raw %}
  <a name="8634" class="Keyword"
      >postulate</a
      ><a name="8643"
      >
    </a
      ><a name="8648" href="Maps.html#8648" class="Postulate"
      >update-permute</a
      ><a name="8662"
      > </a
      ><a name="8663" class="Symbol"
      >:</a
      ><a name="8664"
      > </a
      ><a name="8665" class="Symbol"
      >&#8704;</a
      ><a name="8666"
      > </a
      ><a name="8667" class="Symbol"
      >{</a
      ><a name="8668" href="Maps.html#8668" class="Bound"
      >A</a
      ><a name="8669" class="Symbol"
      >}</a
      ><a name="8670"
      > </a
      ><a name="8671" class="Symbol"
      >(</a
      ><a name="8672" href="Maps.html#8672" class="Bound"
      >&#961;</a
      ><a name="8673"
      > </a
      ><a name="8674" class="Symbol"
      >:</a
      ><a name="8675"
      > </a
      ><a name="8676" href="Maps.html#3738" class="Function"
      >TotalMap</a
      ><a name="8684"
      > </a
      ><a name="8685" href="Maps.html#8668" class="Bound"
      >A</a
      ><a name="8686" class="Symbol"
      >)</a
      ><a name="8687"
      > </a
      ><a name="8688" class="Symbol"
      >(</a
      ><a name="8689" href="Maps.html#8689" class="Bound"
      >x</a
      ><a name="8690"
      > </a
      ><a name="8691" class="Symbol"
      >:</a
      ><a name="8692"
      > </a
      ><a name="8693" href="Maps.html#2215" class="Datatype"
      >Id</a
      ><a name="8695" class="Symbol"
      >)</a
      ><a name="8696"
      > </a
      ><a name="8697" class="Symbol"
      >(</a
      ><a name="8698" href="Maps.html#8698" class="Bound"
      >v</a
      ><a name="8699"
      > </a
      ><a name="8700" class="Symbol"
      >:</a
      ><a name="8701"
      > </a
      ><a name="8702" href="Maps.html#8668" class="Bound"
      >A</a
      ><a name="8703" class="Symbol"
      >)</a
      ><a name="8704"
      > </a
      ><a name="8705" class="Symbol"
      >(</a
      ><a name="8706" href="Maps.html#8706" class="Bound"
      >y</a
      ><a name="8707"
      > </a
      ><a name="8708" class="Symbol"
      >:</a
      ><a name="8709"
      > </a
      ><a name="8710" href="Maps.html#2215" class="Datatype"
      >Id</a
      ><a name="8712" class="Symbol"
      >)</a
      ><a name="8713"
      > </a
      ><a name="8714" class="Symbol"
      >(</a
      ><a name="8715" href="Maps.html#8715" class="Bound"
      >w</a
      ><a name="8716"
      > </a
      ><a name="8717" class="Symbol"
      >:</a
      ><a name="8718"
      > </a
      ><a name="8719" href="Maps.html#8668" class="Bound"
      >A</a
      ><a name="8720" class="Symbol"
      >)</a
      ><a name="8721"
      >
                   </a
      ><a name="8741" class="Symbol"
      >&#8594;</a
      ><a name="8742"
      > </a
      ><a name="8743" href="Maps.html#8689" class="Bound"
      >x</a
      ><a name="8744"
      > </a
      ><a name="8745" href="https://agda.github.io/agda-stdlib/Relation.Binary.Core.html#4493" class="Function Operator"
      >&#8802;</a
      ><a name="8746"
      > </a
      ><a name="8747" href="Maps.html#8706" class="Bound"
      >y</a
      ><a name="8748"
      > </a
      ><a name="8749" class="Symbol"
      >&#8594;</a
      ><a name="8750"
      > </a
      ><a name="8751" class="Symbol"
      >(</a
      ><a name="8752" href="Maps.html#8672" class="Bound"
      >&#961;</a
      ><a name="8753"
      > </a
      ><a name="8754" href="Maps.html#4402" class="Function Operator"
      >,</a
      ><a name="8755"
      > </a
      ><a name="8756" href="Maps.html#8689" class="Bound"
      >x</a
      ><a name="8757"
      > </a
      ><a name="8758" href="Maps.html#4402" class="Function Operator"
      >&#8614;</a
      ><a name="8759"
      > </a
      ><a name="8760" href="Maps.html#8698" class="Bound"
      >v</a
      ><a name="8761"
      > </a
      ><a name="8762" href="Maps.html#4402" class="Function Operator"
      >,</a
      ><a name="8763"
      > </a
      ><a name="8764" href="Maps.html#8706" class="Bound"
      >y</a
      ><a name="8765"
      > </a
      ><a name="8766" href="Maps.html#4402" class="Function Operator"
      >&#8614;</a
      ><a name="8767"
      > </a
      ><a name="8768" href="Maps.html#8715" class="Bound"
      >w</a
      ><a name="8769" class="Symbol"
      >)</a
      ><a name="8770"
      > </a
      ><a name="8771" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="8772"
      > </a
      ><a name="8773" class="Symbol"
      >(</a
      ><a name="8774" href="Maps.html#8672" class="Bound"
      >&#961;</a
      ><a name="8775"
      > </a
      ><a name="8776" href="Maps.html#4402" class="Function Operator"
      >,</a
      ><a name="8777"
      > </a
      ><a name="8778" href="Maps.html#8706" class="Bound"
      >y</a
      ><a name="8779"
      > </a
      ><a name="8780" href="Maps.html#4402" class="Function Operator"
      >&#8614;</a
      ><a name="8781"
      > </a
      ><a name="8782" href="Maps.html#8715" class="Bound"
      >w</a
      ><a name="8783"
      > </a
      ><a name="8784" href="Maps.html#4402" class="Function Operator"
      >,</a
      ><a name="8785"
      > </a
      ><a name="8786" href="Maps.html#8689" class="Bound"
      >x</a
      ><a name="8787"
      > </a
      ><a name="8788" href="Maps.html#4402" class="Function Operator"
      >&#8614;</a
      ><a name="8789"
      > </a
      ><a name="8790" href="Maps.html#8698" class="Bound"
      >v</a
      ><a name="8791" class="Symbol"
      >)</a
      >
{% endraw %}</pre>

<div class="hidden">
<pre class="Agda">{% raw %}
  <a name="8841" href="Maps.html#8841" class="Function"
      >update-permute&#8242;</a
      ><a name="8856"
      > </a
      ><a name="8857" class="Symbol"
      >:</a
      ><a name="8858"
      > </a
      ><a name="8859" class="Symbol"
      >&#8704;</a
      ><a name="8860"
      > </a
      ><a name="8861" class="Symbol"
      >{</a
      ><a name="8862" href="Maps.html#8862" class="Bound"
      >A</a
      ><a name="8863" class="Symbol"
      >}</a
      ><a name="8864"
      > </a
      ><a name="8865" class="Symbol"
      >(</a
      ><a name="8866" href="Maps.html#8866" class="Bound"
      >&#961;</a
      ><a name="8867"
      > </a
      ><a name="8868" class="Symbol"
      >:</a
      ><a name="8869"
      > </a
      ><a name="8870" href="Maps.html#3738" class="Function"
      >TotalMap</a
      ><a name="8878"
      > </a
      ><a name="8879" href="Maps.html#8862" class="Bound"
      >A</a
      ><a name="8880" class="Symbol"
      >)</a
      ><a name="8881"
      > </a
      ><a name="8882" class="Symbol"
      >(</a
      ><a name="8883" href="Maps.html#8883" class="Bound"
      >x</a
      ><a name="8884"
      > </a
      ><a name="8885" class="Symbol"
      >:</a
      ><a name="8886"
      > </a
      ><a name="8887" href="Maps.html#2215" class="Datatype"
      >Id</a
      ><a name="8889" class="Symbol"
      >)</a
      ><a name="8890"
      > </a
      ><a name="8891" class="Symbol"
      >(</a
      ><a name="8892" href="Maps.html#8892" class="Bound"
      >v</a
      ><a name="8893"
      > </a
      ><a name="8894" class="Symbol"
      >:</a
      ><a name="8895"
      > </a
      ><a name="8896" href="Maps.html#8862" class="Bound"
      >A</a
      ><a name="8897" class="Symbol"
      >)</a
      ><a name="8898"
      > </a
      ><a name="8899" class="Symbol"
      >(</a
      ><a name="8900" href="Maps.html#8900" class="Bound"
      >y</a
      ><a name="8901"
      > </a
      ><a name="8902" class="Symbol"
      >:</a
      ><a name="8903"
      > </a
      ><a name="8904" href="Maps.html#2215" class="Datatype"
      >Id</a
      ><a name="8906" class="Symbol"
      >)</a
      ><a name="8907"
      > </a
      ><a name="8908" class="Symbol"
      >(</a
      ><a name="8909" href="Maps.html#8909" class="Bound"
      >w</a
      ><a name="8910"
      > </a
      ><a name="8911" class="Symbol"
      >:</a
      ><a name="8912"
      > </a
      ><a name="8913" href="Maps.html#8862" class="Bound"
      >A</a
      ><a name="8914" class="Symbol"
      >)</a
      ><a name="8915"
      >
                   </a
      ><a name="8935" class="Symbol"
      >&#8594;</a
      ><a name="8936"
      > </a
      ><a name="8937" href="Maps.html#8883" class="Bound"
      >x</a
      ><a name="8938"
      > </a
      ><a name="8939" href="https://agda.github.io/agda-stdlib/Relation.Binary.Core.html#4493" class="Function Operator"
      >&#8802;</a
      ><a name="8940"
      > </a
      ><a name="8941" href="Maps.html#8900" class="Bound"
      >y</a
      ><a name="8942"
      > </a
      ><a name="8943" class="Symbol"
      >&#8594;</a
      ><a name="8944"
      > </a
      ><a name="8945" class="Symbol"
      >(</a
      ><a name="8946" href="Maps.html#8866" class="Bound"
      >&#961;</a
      ><a name="8947"
      > </a
      ><a name="8948" href="Maps.html#4402" class="Function Operator"
      >,</a
      ><a name="8949"
      > </a
      ><a name="8950" href="Maps.html#8883" class="Bound"
      >x</a
      ><a name="8951"
      > </a
      ><a name="8952" href="Maps.html#4402" class="Function Operator"
      >&#8614;</a
      ><a name="8953"
      > </a
      ><a name="8954" href="Maps.html#8892" class="Bound"
      >v</a
      ><a name="8955"
      > </a
      ><a name="8956" href="Maps.html#4402" class="Function Operator"
      >,</a
      ><a name="8957"
      > </a
      ><a name="8958" href="Maps.html#8900" class="Bound"
      >y</a
      ><a name="8959"
      > </a
      ><a name="8960" href="Maps.html#4402" class="Function Operator"
      >&#8614;</a
      ><a name="8961"
      > </a
      ><a name="8962" href="Maps.html#8909" class="Bound"
      >w</a
      ><a name="8963" class="Symbol"
      >)</a
      ><a name="8964"
      > </a
      ><a name="8965" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="8966"
      > </a
      ><a name="8967" class="Symbol"
      >(</a
      ><a name="8968" href="Maps.html#8866" class="Bound"
      >&#961;</a
      ><a name="8969"
      > </a
      ><a name="8970" href="Maps.html#4402" class="Function Operator"
      >,</a
      ><a name="8971"
      > </a
      ><a name="8972" href="Maps.html#8900" class="Bound"
      >y</a
      ><a name="8973"
      > </a
      ><a name="8974" href="Maps.html#4402" class="Function Operator"
      >&#8614;</a
      ><a name="8975"
      > </a
      ><a name="8976" href="Maps.html#8909" class="Bound"
      >w</a
      ><a name="8977"
      > </a
      ><a name="8978" href="Maps.html#4402" class="Function Operator"
      >,</a
      ><a name="8979"
      > </a
      ><a name="8980" href="Maps.html#8883" class="Bound"
      >x</a
      ><a name="8981"
      > </a
      ><a name="8982" href="Maps.html#4402" class="Function Operator"
      >&#8614;</a
      ><a name="8983"
      > </a
      ><a name="8984" href="Maps.html#8892" class="Bound"
      >v</a
      ><a name="8985" class="Symbol"
      >)</a
      ><a name="8986"
      >
  </a
      ><a name="8989" href="Maps.html#8841" class="Function"
      >update-permute&#8242;</a
      ><a name="9004"
      > </a
      ><a name="9005" class="Symbol"
      >{</a
      ><a name="9006" href="Maps.html#9006" class="Bound"
      >A</a
      ><a name="9007" class="Symbol"
      >}</a
      ><a name="9008"
      > </a
      ><a name="9009" href="Maps.html#9009" class="Bound"
      >&#961;</a
      ><a name="9010"
      > </a
      ><a name="9011" href="Maps.html#9011" class="Bound"
      >x</a
      ><a name="9012"
      > </a
      ><a name="9013" href="Maps.html#9013" class="Bound"
      >v</a
      ><a name="9014"
      > </a
      ><a name="9015" href="Maps.html#9015" class="Bound"
      >y</a
      ><a name="9016"
      > </a
      ><a name="9017" href="Maps.html#9017" class="Bound"
      >w</a
      ><a name="9018"
      > </a
      ><a name="9019" href="Maps.html#9019" class="Bound"
      >x&#8802;y</a
      ><a name="9022"
      >  </a
      ><a name="9024" class="Symbol"
      >=</a
      ><a name="9025"
      >  </a
      ><a name="9027" href="Maps.html#6867" class="Postulate"
      >extensionality</a
      ><a name="9041"
      > </a
      ><a name="9042" href="Maps.html#9062" class="Function"
      >lemma</a
      ><a name="9047"
      >
    </a
      ><a name="9052" class="Keyword"
      >where</a
      ><a name="9057"
      >
    </a
      ><a name="9062" href="Maps.html#9062" class="Function"
      >lemma</a
      ><a name="9067"
      > </a
      ><a name="9068" class="Symbol"
      >:</a
      ><a name="9069"
      > </a
      ><a name="9070" class="Symbol"
      >&#8704;</a
      ><a name="9071"
      > </a
      ><a name="9072" href="Maps.html#9072" class="Bound"
      >z</a
      ><a name="9073"
      > </a
      ><a name="9074" class="Symbol"
      >&#8594;</a
      ><a name="9075"
      > </a
      ><a name="9076" class="Symbol"
      >(</a
      ><a name="9077" href="Maps.html#9009" class="Bound"
      >&#961;</a
      ><a name="9078"
      > </a
      ><a name="9079" href="Maps.html#4402" class="Function Operator"
      >,</a
      ><a name="9080"
      > </a
      ><a name="9081" href="Maps.html#9011" class="Bound"
      >x</a
      ><a name="9082"
      > </a
      ><a name="9083" href="Maps.html#4402" class="Function Operator"
      >&#8614;</a
      ><a name="9084"
      > </a
      ><a name="9085" href="Maps.html#9013" class="Bound"
      >v</a
      ><a name="9086"
      > </a
      ><a name="9087" href="Maps.html#4402" class="Function Operator"
      >,</a
      ><a name="9088"
      > </a
      ><a name="9089" href="Maps.html#9015" class="Bound"
      >y</a
      ><a name="9090"
      > </a
      ><a name="9091" href="Maps.html#4402" class="Function Operator"
      >&#8614;</a
      ><a name="9092"
      > </a
      ><a name="9093" href="Maps.html#9017" class="Bound"
      >w</a
      ><a name="9094" class="Symbol"
      >)</a
      ><a name="9095"
      > </a
      ><a name="9096" href="Maps.html#9072" class="Bound"
      >z</a
      ><a name="9097"
      > </a
      ><a name="9098" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="9099"
      > </a
      ><a name="9100" class="Symbol"
      >(</a
      ><a name="9101" href="Maps.html#9009" class="Bound"
      >&#961;</a
      ><a name="9102"
      > </a
      ><a name="9103" href="Maps.html#4402" class="Function Operator"
      >,</a
      ><a name="9104"
      > </a
      ><a name="9105" href="Maps.html#9015" class="Bound"
      >y</a
      ><a name="9106"
      > </a
      ><a name="9107" href="Maps.html#4402" class="Function Operator"
      >&#8614;</a
      ><a name="9108"
      > </a
      ><a name="9109" href="Maps.html#9017" class="Bound"
      >w</a
      ><a name="9110"
      > </a
      ><a name="9111" href="Maps.html#4402" class="Function Operator"
      >,</a
      ><a name="9112"
      > </a
      ><a name="9113" href="Maps.html#9011" class="Bound"
      >x</a
      ><a name="9114"
      > </a
      ><a name="9115" href="Maps.html#4402" class="Function Operator"
      >&#8614;</a
      ><a name="9116"
      > </a
      ><a name="9117" href="Maps.html#9013" class="Bound"
      >v</a
      ><a name="9118" class="Symbol"
      >)</a
      ><a name="9119"
      > </a
      ><a name="9120" href="Maps.html#9072" class="Bound"
      >z</a
      ><a name="9121"
      >
    </a
      ><a name="9126" href="Maps.html#9062" class="Function"
      >lemma</a
      ><a name="9131"
      > </a
      ><a name="9132" href="Maps.html#9132" class="Bound"
      >z</a
      ><a name="9133"
      > </a
      ><a name="9134" class="Keyword"
      >with</a
      ><a name="9138"
      > </a
      ><a name="9139" href="Maps.html#9011" class="Bound"
      >x</a
      ><a name="9140"
      > </a
      ><a name="9141" href="Maps.html#2558" class="Function Operator"
      >&#8799;</a
      ><a name="9142"
      > </a
      ><a name="9143" href="Maps.html#9132" class="Bound"
      >z</a
      ><a name="9144"
      > </a
      ><a name="9145" class="Symbol"
      >|</a
      ><a name="9146"
      > </a
      ><a name="9147" href="Maps.html#9015" class="Bound"
      >y</a
      ><a name="9148"
      > </a
      ><a name="9149" href="Maps.html#2558" class="Function Operator"
      >&#8799;</a
      ><a name="9150"
      > </a
      ><a name="9151" href="Maps.html#9132" class="Bound"
      >z</a
      ><a name="9152"
      >
    </a
      ><a name="9157" class="Symbol"
      >...</a
      ><a name="9160"
      > </a
      ><a name="9161" class="Symbol"
      >|</a
      ><a name="9162"
      > </a
      ><a name="9163" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#520" class="InductiveConstructor"
      >yes</a
      ><a name="9166"
      > </a
      ><a name="9167" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="9171"
      > </a
      ><a name="9172" class="Symbol"
      >|</a
      ><a name="9173"
      > </a
      ><a name="9174" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#520" class="InductiveConstructor"
      >yes</a
      ><a name="9177"
      > </a
      ><a name="9178" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="9182"
      >  </a
      ><a name="9184" class="Symbol"
      >=</a
      ><a name="9185"
      >  </a
      ><a name="9187" href="https://agda.github.io/agda-stdlib/Data.Empty.html#348" class="Function"
      >&#8869;-elim</a
      ><a name="9193"
      > </a
      ><a name="9194" class="Symbol"
      >(</a
      ><a name="9195" href="Maps.html#9019" class="Bound"
      >x&#8802;y</a
      ><a name="9198"
      > </a
      ><a name="9199" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="9203" class="Symbol"
      >)</a
      ><a name="9204"
      >
    </a
      ><a name="9209" class="Symbol"
      >...</a
      ><a name="9212"
      > </a
      ><a name="9213" class="Symbol"
      >|</a
      ><a name="9214"
      > </a
      ><a name="9215" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#547" class="InductiveConstructor"
      >no</a
      ><a name="9217"
      >  </a
      ><a name="9219" href="Maps.html#9219" class="Bound"
      >x&#8802;z</a
      ><a name="9222"
      >  </a
      ><a name="9224" class="Symbol"
      >|</a
      ><a name="9225"
      > </a
      ><a name="9226" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#520" class="InductiveConstructor"
      >yes</a
      ><a name="9229"
      > </a
      ><a name="9230" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="9234"
      >  </a
      ><a name="9236" class="Symbol"
      >=</a
      ><a name="9237"
      >  </a
      ><a name="9239" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.Core.html#565" class="Function"
      >sym</a
      ><a name="9242"
      > </a
      ><a name="9243" class="Symbol"
      >(</a
      ><a name="9244" href="Maps.html#6072" class="Function"
      >update-eq&#8242;</a
      ><a name="9254"
      > </a
      ><a name="9255" href="Maps.html#9009" class="Bound"
      >&#961;</a
      ><a name="9256"
      > </a
      ><a name="9257" href="Maps.html#9132" class="Bound"
      >z</a
      ><a name="9258"
      > </a
      ><a name="9259" href="Maps.html#9017" class="Bound"
      >w</a
      ><a name="9260" class="Symbol"
      >)</a
      ><a name="9261"
      >
    </a
      ><a name="9266" class="Symbol"
      >...</a
      ><a name="9269"
      > </a
      ><a name="9270" class="Symbol"
      >|</a
      ><a name="9271"
      > </a
      ><a name="9272" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#520" class="InductiveConstructor"
      >yes</a
      ><a name="9275"
      > </a
      ><a name="9276" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="9280"
      > </a
      ><a name="9281" class="Symbol"
      >|</a
      ><a name="9282"
      > </a
      ><a name="9283" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#547" class="InductiveConstructor"
      >no</a
      ><a name="9285"
      >  </a
      ><a name="9287" href="Maps.html#9287" class="Bound"
      >y&#8802;z</a
      ><a name="9290"
      >   </a
      ><a name="9293" class="Symbol"
      >=</a
      ><a name="9294"
      >  </a
      ><a name="9296" href="Maps.html#6072" class="Function"
      >update-eq&#8242;</a
      ><a name="9306"
      > </a
      ><a name="9307" href="Maps.html#9009" class="Bound"
      >&#961;</a
      ><a name="9308"
      > </a
      ><a name="9309" href="Maps.html#9132" class="Bound"
      >z</a
      ><a name="9310"
      > </a
      ><a name="9311" href="Maps.html#9013" class="Bound"
      >v</a
      ><a name="9312"
      >
    </a
      ><a name="9317" class="Symbol"
      >...</a
      ><a name="9320"
      > </a
      ><a name="9321" class="Symbol"
      >|</a
      ><a name="9322"
      > </a
      ><a name="9323" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#547" class="InductiveConstructor"
      >no</a
      ><a name="9325"
      >  </a
      ><a name="9327" href="Maps.html#9327" class="Bound"
      >x&#8802;z</a
      ><a name="9330"
      >  </a
      ><a name="9332" class="Symbol"
      >|</a
      ><a name="9333"
      > </a
      ><a name="9334" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#547" class="InductiveConstructor"
      >no</a
      ><a name="9336"
      >  </a
      ><a name="9338" href="Maps.html#9338" class="Bound"
      >y&#8802;z</a
      ><a name="9341"
      >   </a
      ><a name="9344" class="Symbol"
      >=</a
      ><a name="9345"
      >  </a
      ><a name="9347" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.Core.html#632" class="Function"
      >trans</a
      ><a name="9352"
      > </a
      ><a name="9353" class="Symbol"
      >(</a
      ><a name="9354" href="Maps.html#6494" class="Function"
      >update-neq</a
      ><a name="9364"
      > </a
      ><a name="9365" href="Maps.html#9009" class="Bound"
      >&#961;</a
      ><a name="9366"
      > </a
      ><a name="9367" href="Maps.html#9011" class="Bound"
      >x</a
      ><a name="9368"
      > </a
      ><a name="9369" href="Maps.html#9013" class="Bound"
      >v</a
      ><a name="9370"
      > </a
      ><a name="9371" href="Maps.html#9132" class="Bound"
      >z</a
      ><a name="9372"
      > </a
      ><a name="9373" href="Maps.html#9327" class="Bound"
      >x&#8802;z</a
      ><a name="9376" class="Symbol"
      >)</a
      ><a name="9377"
      > </a
      ><a name="9378" class="Symbol"
      >(</a
      ><a name="9379" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.Core.html#565" class="Function"
      >sym</a
      ><a name="9382"
      > </a
      ><a name="9383" class="Symbol"
      >(</a
      ><a name="9384" href="Maps.html#6494" class="Function"
      >update-neq</a
      ><a name="9394"
      > </a
      ><a name="9395" href="Maps.html#9009" class="Bound"
      >&#961;</a
      ><a name="9396"
      > </a
      ><a name="9397" href="Maps.html#9015" class="Bound"
      >y</a
      ><a name="9398"
      > </a
      ><a name="9399" href="Maps.html#9017" class="Bound"
      >w</a
      ><a name="9400"
      > </a
      ><a name="9401" href="Maps.html#9132" class="Bound"
      >z</a
      ><a name="9402"
      > </a
      ><a name="9403" href="Maps.html#9338" class="Bound"
      >y&#8802;z</a
      ><a name="9406" class="Symbol"
      >))</a
      >
{% endraw %}</pre>

And a slightly different version of the same proof.

<pre class="Agda">{% raw %}
  <a name="9493" href="Maps.html#9493" class="Function"
      >update-permute&#8242;&#8242;</a
      ><a name="9509"
      > </a
      ><a name="9510" class="Symbol"
      >:</a
      ><a name="9511"
      > </a
      ><a name="9512" class="Symbol"
      >&#8704;</a
      ><a name="9513"
      > </a
      ><a name="9514" class="Symbol"
      >{</a
      ><a name="9515" href="Maps.html#9515" class="Bound"
      >A</a
      ><a name="9516" class="Symbol"
      >}</a
      ><a name="9517"
      > </a
      ><a name="9518" class="Symbol"
      >(</a
      ><a name="9519" href="Maps.html#9519" class="Bound"
      >&#961;</a
      ><a name="9520"
      > </a
      ><a name="9521" class="Symbol"
      >:</a
      ><a name="9522"
      > </a
      ><a name="9523" href="Maps.html#3738" class="Function"
      >TotalMap</a
      ><a name="9531"
      > </a
      ><a name="9532" href="Maps.html#9515" class="Bound"
      >A</a
      ><a name="9533" class="Symbol"
      >)</a
      ><a name="9534"
      > </a
      ><a name="9535" class="Symbol"
      >(</a
      ><a name="9536" href="Maps.html#9536" class="Bound"
      >x</a
      ><a name="9537"
      > </a
      ><a name="9538" class="Symbol"
      >:</a
      ><a name="9539"
      > </a
      ><a name="9540" href="Maps.html#2215" class="Datatype"
      >Id</a
      ><a name="9542" class="Symbol"
      >)</a
      ><a name="9543"
      > </a
      ><a name="9544" class="Symbol"
      >(</a
      ><a name="9545" href="Maps.html#9545" class="Bound"
      >v</a
      ><a name="9546"
      > </a
      ><a name="9547" class="Symbol"
      >:</a
      ><a name="9548"
      > </a
      ><a name="9549" href="Maps.html#9515" class="Bound"
      >A</a
      ><a name="9550" class="Symbol"
      >)</a
      ><a name="9551"
      > </a
      ><a name="9552" class="Symbol"
      >(</a
      ><a name="9553" href="Maps.html#9553" class="Bound"
      >y</a
      ><a name="9554"
      > </a
      ><a name="9555" class="Symbol"
      >:</a
      ><a name="9556"
      > </a
      ><a name="9557" href="Maps.html#2215" class="Datatype"
      >Id</a
      ><a name="9559" class="Symbol"
      >)</a
      ><a name="9560"
      > </a
      ><a name="9561" class="Symbol"
      >(</a
      ><a name="9562" href="Maps.html#9562" class="Bound"
      >w</a
      ><a name="9563"
      > </a
      ><a name="9564" class="Symbol"
      >:</a
      ><a name="9565"
      > </a
      ><a name="9566" href="Maps.html#9515" class="Bound"
      >A</a
      ><a name="9567" class="Symbol"
      >)</a
      ><a name="9568"
      > </a
      ><a name="9569" class="Symbol"
      >(</a
      ><a name="9570" href="Maps.html#9570" class="Bound"
      >z</a
      ><a name="9571"
      > </a
      ><a name="9572" class="Symbol"
      >:</a
      ><a name="9573"
      > </a
      ><a name="9574" href="Maps.html#2215" class="Datatype"
      >Id</a
      ><a name="9576" class="Symbol"
      >)</a
      ><a name="9577"
      >
                   </a
      ><a name="9597" class="Symbol"
      >&#8594;</a
      ><a name="9598"
      > </a
      ><a name="9599" href="Maps.html#9536" class="Bound"
      >x</a
      ><a name="9600"
      > </a
      ><a name="9601" href="https://agda.github.io/agda-stdlib/Relation.Binary.Core.html#4493" class="Function Operator"
      >&#8802;</a
      ><a name="9602"
      > </a
      ><a name="9603" href="Maps.html#9553" class="Bound"
      >y</a
      ><a name="9604"
      > </a
      ><a name="9605" class="Symbol"
      >&#8594;</a
      ><a name="9606"
      > </a
      ><a name="9607" class="Symbol"
      >(</a
      ><a name="9608" href="Maps.html#9519" class="Bound"
      >&#961;</a
      ><a name="9609"
      > </a
      ><a name="9610" href="Maps.html#4402" class="Function Operator"
      >,</a
      ><a name="9611"
      > </a
      ><a name="9612" href="Maps.html#9536" class="Bound"
      >x</a
      ><a name="9613"
      > </a
      ><a name="9614" href="Maps.html#4402" class="Function Operator"
      >&#8614;</a
      ><a name="9615"
      > </a
      ><a name="9616" href="Maps.html#9545" class="Bound"
      >v</a
      ><a name="9617"
      > </a
      ><a name="9618" href="Maps.html#4402" class="Function Operator"
      >,</a
      ><a name="9619"
      > </a
      ><a name="9620" href="Maps.html#9553" class="Bound"
      >y</a
      ><a name="9621"
      > </a
      ><a name="9622" href="Maps.html#4402" class="Function Operator"
      >&#8614;</a
      ><a name="9623"
      > </a
      ><a name="9624" href="Maps.html#9562" class="Bound"
      >w</a
      ><a name="9625" class="Symbol"
      >)</a
      ><a name="9626"
      > </a
      ><a name="9627" href="Maps.html#9570" class="Bound"
      >z</a
      ><a name="9628"
      > </a
      ><a name="9629" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="9630"
      > </a
      ><a name="9631" class="Symbol"
      >(</a
      ><a name="9632" href="Maps.html#9519" class="Bound"
      >&#961;</a
      ><a name="9633"
      > </a
      ><a name="9634" href="Maps.html#4402" class="Function Operator"
      >,</a
      ><a name="9635"
      > </a
      ><a name="9636" href="Maps.html#9553" class="Bound"
      >y</a
      ><a name="9637"
      > </a
      ><a name="9638" href="Maps.html#4402" class="Function Operator"
      >&#8614;</a
      ><a name="9639"
      > </a
      ><a name="9640" href="Maps.html#9562" class="Bound"
      >w</a
      ><a name="9641"
      > </a
      ><a name="9642" href="Maps.html#4402" class="Function Operator"
      >,</a
      ><a name="9643"
      > </a
      ><a name="9644" href="Maps.html#9536" class="Bound"
      >x</a
      ><a name="9645"
      > </a
      ><a name="9646" href="Maps.html#4402" class="Function Operator"
      >&#8614;</a
      ><a name="9647"
      > </a
      ><a name="9648" href="Maps.html#9545" class="Bound"
      >v</a
      ><a name="9649" class="Symbol"
      >)</a
      ><a name="9650"
      > </a
      ><a name="9651" href="Maps.html#9570" class="Bound"
      >z</a
      ><a name="9652"
      >
  </a
      ><a name="9655" href="Maps.html#9493" class="Function"
      >update-permute&#8242;&#8242;</a
      ><a name="9671"
      > </a
      ><a name="9672" class="Symbol"
      >{</a
      ><a name="9673" href="Maps.html#9673" class="Bound"
      >A</a
      ><a name="9674" class="Symbol"
      >}</a
      ><a name="9675"
      > </a
      ><a name="9676" href="Maps.html#9676" class="Bound"
      >&#961;</a
      ><a name="9677"
      > </a
      ><a name="9678" href="Maps.html#9678" class="Bound"
      >x</a
      ><a name="9679"
      > </a
      ><a name="9680" href="Maps.html#9680" class="Bound"
      >v</a
      ><a name="9681"
      > </a
      ><a name="9682" href="Maps.html#9682" class="Bound"
      >y</a
      ><a name="9683"
      > </a
      ><a name="9684" href="Maps.html#9684" class="Bound"
      >w</a
      ><a name="9685"
      > </a
      ><a name="9686" href="Maps.html#9686" class="Bound"
      >z</a
      ><a name="9687"
      > </a
      ><a name="9688" href="Maps.html#9688" class="Bound"
      >x&#8802;y</a
      ><a name="9691"
      > </a
      ><a name="9692" class="Keyword"
      >with</a
      ><a name="9696"
      > </a
      ><a name="9697" href="Maps.html#9678" class="Bound"
      >x</a
      ><a name="9698"
      > </a
      ><a name="9699" href="Maps.html#2558" class="Function Operator"
      >&#8799;</a
      ><a name="9700"
      > </a
      ><a name="9701" href="Maps.html#9686" class="Bound"
      >z</a
      ><a name="9702"
      > </a
      ><a name="9703" class="Symbol"
      >|</a
      ><a name="9704"
      > </a
      ><a name="9705" href="Maps.html#9682" class="Bound"
      >y</a
      ><a name="9706"
      > </a
      ><a name="9707" href="Maps.html#2558" class="Function Operator"
      >&#8799;</a
      ><a name="9708"
      > </a
      ><a name="9709" href="Maps.html#9686" class="Bound"
      >z</a
      ><a name="9710"
      >
  </a
      ><a name="9713" class="Symbol"
      >...</a
      ><a name="9716"
      > </a
      ><a name="9717" class="Symbol"
      >|</a
      ><a name="9718"
      > </a
      ><a name="9719" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#520" class="InductiveConstructor"
      >yes</a
      ><a name="9722"
      > </a
      ><a name="9723" href="Maps.html#9723" class="Bound"
      >x&#8801;z</a
      ><a name="9726"
      > </a
      ><a name="9727" class="Symbol"
      >|</a
      ><a name="9728"
      > </a
      ><a name="9729" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#520" class="InductiveConstructor"
      >yes</a
      ><a name="9732"
      > </a
      ><a name="9733" href="Maps.html#9733" class="Bound"
      >y&#8801;z</a
      ><a name="9736"
      > </a
      ><a name="9737" class="Symbol"
      >=</a
      ><a name="9738"
      > </a
      ><a name="9739" href="https://agda.github.io/agda-stdlib/Data.Empty.html#348" class="Function"
      >&#8869;-elim</a
      ><a name="9745"
      > </a
      ><a name="9746" class="Symbol"
      >(</a
      ><a name="9747" href="Maps.html#9688" class="Bound"
      >x&#8802;y</a
      ><a name="9750"
      > </a
      ><a name="9751" class="Symbol"
      >(</a
      ><a name="9752" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.Core.html#632" class="Function"
      >trans</a
      ><a name="9757"
      > </a
      ><a name="9758" href="Maps.html#9723" class="Bound"
      >x&#8801;z</a
      ><a name="9761"
      > </a
      ><a name="9762" class="Symbol"
      >(</a
      ><a name="9763" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.Core.html#565" class="Function"
      >sym</a
      ><a name="9766"
      > </a
      ><a name="9767" href="Maps.html#9733" class="Bound"
      >y&#8801;z</a
      ><a name="9770" class="Symbol"
      >)))</a
      ><a name="9773"
      >
  </a
      ><a name="9776" class="Symbol"
      >...</a
      ><a name="9779"
      > </a
      ><a name="9780" class="Symbol"
      >|</a
      ><a name="9781"
      > </a
      ><a name="9782" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#547" class="InductiveConstructor"
      >no</a
      ><a name="9784"
      >  </a
      ><a name="9786" href="Maps.html#9786" class="Bound"
      >x&#8802;z</a
      ><a name="9789"
      > </a
      ><a name="9790" class="Symbol"
      >|</a
      ><a name="9791"
      > </a
      ><a name="9792" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#520" class="InductiveConstructor"
      >yes</a
      ><a name="9795"
      > </a
      ><a name="9796" href="Maps.html#9796" class="Bound"
      >y&#8801;z</a
      ><a name="9799"
      > </a
      ><a name="9800" class="Keyword"
      >rewrite</a
      ><a name="9807"
      > </a
      ><a name="9808" href="Maps.html#9796" class="Bound"
      >y&#8801;z</a
      ><a name="9811"
      >  </a
      ><a name="9813" class="Symbol"
      >=</a
      ><a name="9814"
      >  </a
      ><a name="9816" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.Core.html#565" class="Function"
      >sym</a
      ><a name="9819"
      > </a
      ><a name="9820" class="Symbol"
      >(</a
      ><a name="9821" href="Maps.html#6072" class="Function"
      >update-eq&#8242;</a
      ><a name="9831"
      > </a
      ><a name="9832" href="Maps.html#9676" class="Bound"
      >&#961;</a
      ><a name="9833"
      > </a
      ><a name="9834" href="Maps.html#9686" class="Bound"
      >z</a
      ><a name="9835"
      > </a
      ><a name="9836" href="Maps.html#9684" class="Bound"
      >w</a
      ><a name="9837" class="Symbol"
      >)</a
      ><a name="9838"
      >  
  </a
      ><a name="9843" class="Symbol"
      >...</a
      ><a name="9846"
      > </a
      ><a name="9847" class="Symbol"
      >|</a
      ><a name="9848"
      > </a
      ><a name="9849" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#520" class="InductiveConstructor"
      >yes</a
      ><a name="9852"
      > </a
      ><a name="9853" href="Maps.html#9853" class="Bound"
      >x&#8801;z</a
      ><a name="9856"
      > </a
      ><a name="9857" class="Symbol"
      >|</a
      ><a name="9858"
      > </a
      ><a name="9859" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#547" class="InductiveConstructor"
      >no</a
      ><a name="9861"
      >  </a
      ><a name="9863" href="Maps.html#9863" class="Bound"
      >y&#8802;z</a
      ><a name="9866"
      > </a
      ><a name="9867" class="Keyword"
      >rewrite</a
      ><a name="9874"
      > </a
      ><a name="9875" href="Maps.html#9853" class="Bound"
      >x&#8801;z</a
      ><a name="9878"
      >  </a
      ><a name="9880" class="Symbol"
      >=</a
      ><a name="9881"
      >  </a
      ><a name="9883" href="Maps.html#6072" class="Function"
      >update-eq&#8242;</a
      ><a name="9893"
      > </a
      ><a name="9894" href="Maps.html#9676" class="Bound"
      >&#961;</a
      ><a name="9895"
      > </a
      ><a name="9896" href="Maps.html#9686" class="Bound"
      >z</a
      ><a name="9897"
      > </a
      ><a name="9898" href="Maps.html#9680" class="Bound"
      >v</a
      ><a name="9899"
      >
  </a
      ><a name="9902" class="Symbol"
      >...</a
      ><a name="9905"
      > </a
      ><a name="9906" class="Symbol"
      >|</a
      ><a name="9907"
      > </a
      ><a name="9908" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#547" class="InductiveConstructor"
      >no</a
      ><a name="9910"
      >  </a
      ><a name="9912" href="Maps.html#9912" class="Bound"
      >x&#8802;z</a
      ><a name="9915"
      > </a
      ><a name="9916" class="Symbol"
      >|</a
      ><a name="9917"
      > </a
      ><a name="9918" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#547" class="InductiveConstructor"
      >no</a
      ><a name="9920"
      >  </a
      ><a name="9922" href="Maps.html#9922" class="Bound"
      >y&#8802;z</a
      ><a name="9925"
      >  </a
      ><a name="9927" class="Symbol"
      >=</a
      ><a name="9928"
      >  </a
      ><a name="9930" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.Core.html#632" class="Function"
      >trans</a
      ><a name="9935"
      > </a
      ><a name="9936" class="Symbol"
      >(</a
      ><a name="9937" href="Maps.html#6494" class="Function"
      >update-neq</a
      ><a name="9947"
      > </a
      ><a name="9948" href="Maps.html#9676" class="Bound"
      >&#961;</a
      ><a name="9949"
      > </a
      ><a name="9950" href="Maps.html#9678" class="Bound"
      >x</a
      ><a name="9951"
      > </a
      ><a name="9952" href="Maps.html#9680" class="Bound"
      >v</a
      ><a name="9953"
      > </a
      ><a name="9954" href="Maps.html#9686" class="Bound"
      >z</a
      ><a name="9955"
      > </a
      ><a name="9956" href="Maps.html#9912" class="Bound"
      >x&#8802;z</a
      ><a name="9959" class="Symbol"
      >)</a
      ><a name="9960"
      > </a
      ><a name="9961" class="Symbol"
      >(</a
      ><a name="9962" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.Core.html#565" class="Function"
      >sym</a
      ><a name="9965"
      > </a
      ><a name="9966" class="Symbol"
      >(</a
      ><a name="9967" href="Maps.html#6494" class="Function"
      >update-neq</a
      ><a name="9977"
      > </a
      ><a name="9978" href="Maps.html#9676" class="Bound"
      >&#961;</a
      ><a name="9979"
      > </a
      ><a name="9980" href="Maps.html#9682" class="Bound"
      >y</a
      ><a name="9981"
      > </a
      ><a name="9982" href="Maps.html#9684" class="Bound"
      >w</a
      ><a name="9983"
      > </a
      ><a name="9984" href="Maps.html#9686" class="Bound"
      >z</a
      ><a name="9985"
      > </a
      ><a name="9986" href="Maps.html#9922" class="Bound"
      >y&#8802;z</a
      ><a name="9989" class="Symbol"
      >))</a
      >
{% endraw %}</pre>
</div>

## Partial maps

Finally, we define _partial maps_ on top of total maps.  A partial
map with elements of type `A` is simply a total map with elements
of type `Maybe A` and default element `nothing`.

<pre class="Agda">{% raw %}
<a name="10226" href="Maps.html#10226" class="Function"
      >PartialMap</a
      ><a name="10236"
      > </a
      ><a name="10237" class="Symbol"
      >:</a
      ><a name="10238"
      > </a
      ><a name="10239" class="PrimitiveType"
      >Set</a
      ><a name="10242"
      > </a
      ><a name="10243" class="Symbol"
      >&#8594;</a
      ><a name="10244"
      > </a
      ><a name="10245" class="PrimitiveType"
      >Set</a
      ><a name="10248"
      >
</a
      ><a name="10249" href="Maps.html#10226" class="Function"
      >PartialMap</a
      ><a name="10259"
      > </a
      ><a name="10260" href="Maps.html#10260" class="Bound"
      >A</a
      ><a name="10261"
      > </a
      ><a name="10262" class="Symbol"
      >=</a
      ><a name="10263"
      > </a
      ><a name="10264" href="Maps.html#3738" class="Function"
      >TotalMap</a
      ><a name="10272"
      > </a
      ><a name="10273" class="Symbol"
      >(</a
      ><a name="10274" href="https://agda.github.io/agda-stdlib/Data.Maybe.Base.html#335" class="Datatype"
      >Maybe</a
      ><a name="10279"
      > </a
      ><a name="10280" href="Maps.html#10260" class="Bound"
      >A</a
      ><a name="10281" class="Symbol"
      >)</a
      >
{% endraw %}</pre>

<pre class="Agda">{% raw %}
<a name="10308" class="Keyword"
      >module</a
      ><a name="10314"
      > </a
      ><a name="10315" href="Maps.html#10315" class="Module"
      >PartialMap</a
      ><a name="10325"
      > </a
      ><a name="10326" class="Keyword"
      >where</a
      >
{% endraw %}</pre>

<pre class="Agda">{% raw %}
  <a name="10359" href="Maps.html#10359" class="Function"
      >&#8709;</a
      ><a name="10360"
      > </a
      ><a name="10361" class="Symbol"
      >:</a
      ><a name="10362"
      > </a
      ><a name="10363" class="Symbol"
      >&#8704;</a
      ><a name="10364"
      > </a
      ><a name="10365" class="Symbol"
      >{</a
      ><a name="10366" href="Maps.html#10366" class="Bound"
      >A</a
      ><a name="10367" class="Symbol"
      >}</a
      ><a name="10368"
      > </a
      ><a name="10369" class="Symbol"
      >&#8594;</a
      ><a name="10370"
      > </a
      ><a name="10371" href="Maps.html#10226" class="Function"
      >PartialMap</a
      ><a name="10381"
      > </a
      ><a name="10382" href="Maps.html#10366" class="Bound"
      >A</a
      ><a name="10383"
      >
  </a
      ><a name="10386" href="Maps.html#10359" class="Function"
      >&#8709;</a
      ><a name="10387"
      > </a
      ><a name="10388" class="Symbol"
      >=</a
      ><a name="10389"
      > </a
      ><a name="10390" href="Maps.html#4109" class="Function"
      >TotalMap.always</a
      ><a name="10405"
      > </a
      ><a name="10406" href="https://agda.github.io/agda-stdlib/Data.Maybe.Base.html#403" class="InductiveConstructor"
      >nothing</a
      >
{% endraw %}</pre>

<pre class="Agda">{% raw %}
  <a name="10441" class="Keyword"
      >infixl</a
      ><a name="10447"
      > </a
      ><a name="10448" class="Number"
      >15</a
      ><a name="10450"
      > </a
      ><a name="10451" href="Maps.html#10462" class="Function Operator"
      >_,_&#8614;_</a
      ><a name="10456"
      >  

  </a
      ><a name="10462" href="Maps.html#10462" class="Function Operator"
      >_,_&#8614;_</a
      ><a name="10467"
      > </a
      ><a name="10468" class="Symbol"
      >:</a
      ><a name="10469"
      > </a
      ><a name="10470" class="Symbol"
      >&#8704;</a
      ><a name="10471"
      > </a
      ><a name="10472" class="Symbol"
      >{</a
      ><a name="10473" href="Maps.html#10473" class="Bound"
      >A</a
      ><a name="10474" class="Symbol"
      >}</a
      ><a name="10475"
      > </a
      ><a name="10476" class="Symbol"
      >(</a
      ><a name="10477" href="Maps.html#10477" class="Bound"
      >&#961;</a
      ><a name="10478"
      > </a
      ><a name="10479" class="Symbol"
      >:</a
      ><a name="10480"
      > </a
      ><a name="10481" href="Maps.html#10226" class="Function"
      >PartialMap</a
      ><a name="10491"
      > </a
      ><a name="10492" href="Maps.html#10473" class="Bound"
      >A</a
      ><a name="10493" class="Symbol"
      >)</a
      ><a name="10494"
      > </a
      ><a name="10495" class="Symbol"
      >(</a
      ><a name="10496" href="Maps.html#10496" class="Bound"
      >x</a
      ><a name="10497"
      > </a
      ><a name="10498" class="Symbol"
      >:</a
      ><a name="10499"
      > </a
      ><a name="10500" href="Maps.html#2215" class="Datatype"
      >Id</a
      ><a name="10502" class="Symbol"
      >)</a
      ><a name="10503"
      > </a
      ><a name="10504" class="Symbol"
      >(</a
      ><a name="10505" href="Maps.html#10505" class="Bound"
      >v</a
      ><a name="10506"
      > </a
      ><a name="10507" class="Symbol"
      >:</a
      ><a name="10508"
      > </a
      ><a name="10509" href="Maps.html#10473" class="Bound"
      >A</a
      ><a name="10510" class="Symbol"
      >)</a
      ><a name="10511"
      > </a
      ><a name="10512" class="Symbol"
      >&#8594;</a
      ><a name="10513"
      > </a
      ><a name="10514" href="Maps.html#10226" class="Function"
      >PartialMap</a
      ><a name="10524"
      > </a
      ><a name="10525" href="Maps.html#10473" class="Bound"
      >A</a
      ><a name="10526"
      >
  </a
      ><a name="10529" href="Maps.html#10529" class="Bound"
      >&#961;</a
      ><a name="10530"
      > </a
      ><a name="10531" href="Maps.html#10462" class="Function Operator"
      >,</a
      ><a name="10532"
      > </a
      ><a name="10533" href="Maps.html#10533" class="Bound"
      >x</a
      ><a name="10534"
      > </a
      ><a name="10535" href="Maps.html#10462" class="Function Operator"
      >&#8614;</a
      ><a name="10536"
      > </a
      ><a name="10537" href="Maps.html#10537" class="Bound"
      >v</a
      ><a name="10538"
      > </a
      ><a name="10539" class="Symbol"
      >=</a
      ><a name="10540"
      > </a
      ><a name="10541" href="Maps.html#4402" class="Function Operator"
      >TotalMap._,_&#8614;_</a
      ><a name="10555"
      > </a
      ><a name="10556" href="Maps.html#10529" class="Bound"
      >&#961;</a
      ><a name="10557"
      > </a
      ><a name="10558" href="Maps.html#10533" class="Bound"
      >x</a
      ><a name="10559"
      > </a
      ><a name="10560" class="Symbol"
      >(</a
      ><a name="10561" href="https://agda.github.io/agda-stdlib/Data.Maybe.Base.html#373" class="InductiveConstructor"
      >just</a
      ><a name="10565"
      > </a
      ><a name="10566" href="Maps.html#10537" class="Bound"
      >v</a
      ><a name="10567" class="Symbol"
      >)</a
      >
{% endraw %}</pre>

We now lift all of the basic lemmas about total maps to partial maps.

<pre class="Agda">{% raw %}
  <a name="10667" href="Maps.html#10667" class="Function"
      >apply-&#8709;</a
      ><a name="10674"
      > </a
      ><a name="10675" class="Symbol"
      >:</a
      ><a name="10676"
      > </a
      ><a name="10677" class="Symbol"
      >&#8704;</a
      ><a name="10678"
      > </a
      ><a name="10679" class="Symbol"
      >{</a
      ><a name="10680" href="Maps.html#10680" class="Bound"
      >A</a
      ><a name="10681" class="Symbol"
      >}</a
      ><a name="10682"
      > </a
      ><a name="10683" class="Symbol"
      >&#8594;</a
      ><a name="10684"
      > </a
      ><a name="10685" class="Symbol"
      >(</a
      ><a name="10686" href="Maps.html#10686" class="Bound"
      >x</a
      ><a name="10687"
      > </a
      ><a name="10688" class="Symbol"
      >:</a
      ><a name="10689"
      > </a
      ><a name="10690" href="Maps.html#2215" class="Datatype"
      >Id</a
      ><a name="10692" class="Symbol"
      >)</a
      ><a name="10693"
      > </a
      ><a name="10694" class="Symbol"
      >&#8594;</a
      ><a name="10695"
      > </a
      ><a name="10696" class="Symbol"
      >(</a
      ><a name="10697" href="Maps.html#10359" class="Function"
      >&#8709;</a
      ><a name="10698"
      > </a
      ><a name="10699" class="Symbol"
      >{</a
      ><a name="10700" href="Maps.html#10680" class="Bound"
      >A</a
      ><a name="10701" class="Symbol"
      >}</a
      ><a name="10702"
      > </a
      ><a name="10703" href="Maps.html#10686" class="Bound"
      >x</a
      ><a name="10704" class="Symbol"
      >)</a
      ><a name="10705"
      > </a
      ><a name="10706" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="10707"
      > </a
      ><a name="10708" href="https://agda.github.io/agda-stdlib/Data.Maybe.Base.html#403" class="InductiveConstructor"
      >nothing</a
      ><a name="10715"
      >
  </a
      ><a name="10718" href="Maps.html#10667" class="Function"
      >apply-&#8709;</a
      ><a name="10725"
      > </a
      ><a name="10726" href="Maps.html#10726" class="Bound"
      >x</a
      ><a name="10727"
      >  </a
      ><a name="10729" class="Symbol"
      >=</a
      ><a name="10730"
      > </a
      ><a name="10731" href="Maps.html#5519" class="Postulate"
      >TotalMap.apply-always</a
      ><a name="10752"
      > </a
      ><a name="10753" href="https://agda.github.io/agda-stdlib/Data.Maybe.Base.html#403" class="InductiveConstructor"
      >nothing</a
      ><a name="10760"
      > </a
      ><a name="10761" href="Maps.html#10726" class="Bound"
      >x</a
      >
{% endraw %}</pre>

<pre class="Agda">{% raw %}
  <a name="10790" href="Maps.html#10790" class="Function"
      >update-eq</a
      ><a name="10799"
      > </a
      ><a name="10800" class="Symbol"
      >:</a
      ><a name="10801"
      > </a
      ><a name="10802" class="Symbol"
      >&#8704;</a
      ><a name="10803"
      > </a
      ><a name="10804" class="Symbol"
      >{</a
      ><a name="10805" href="Maps.html#10805" class="Bound"
      >A</a
      ><a name="10806" class="Symbol"
      >}</a
      ><a name="10807"
      > </a
      ><a name="10808" class="Symbol"
      >(</a
      ><a name="10809" href="Maps.html#10809" class="Bound"
      >&#961;</a
      ><a name="10810"
      > </a
      ><a name="10811" class="Symbol"
      >:</a
      ><a name="10812"
      > </a
      ><a name="10813" href="Maps.html#10226" class="Function"
      >PartialMap</a
      ><a name="10823"
      > </a
      ><a name="10824" href="Maps.html#10805" class="Bound"
      >A</a
      ><a name="10825" class="Symbol"
      >)</a
      ><a name="10826"
      > </a
      ><a name="10827" class="Symbol"
      >(</a
      ><a name="10828" href="Maps.html#10828" class="Bound"
      >x</a
      ><a name="10829"
      > </a
      ><a name="10830" class="Symbol"
      >:</a
      ><a name="10831"
      > </a
      ><a name="10832" href="Maps.html#2215" class="Datatype"
      >Id</a
      ><a name="10834" class="Symbol"
      >)</a
      ><a name="10835"
      > </a
      ><a name="10836" class="Symbol"
      >(</a
      ><a name="10837" href="Maps.html#10837" class="Bound"
      >v</a
      ><a name="10838"
      > </a
      ><a name="10839" class="Symbol"
      >:</a
      ><a name="10840"
      > </a
      ><a name="10841" href="Maps.html#10805" class="Bound"
      >A</a
      ><a name="10842" class="Symbol"
      >)</a
      ><a name="10843"
      >
            </a
      ><a name="10856" class="Symbol"
      >&#8594;</a
      ><a name="10857"
      > </a
      ><a name="10858" class="Symbol"
      >(</a
      ><a name="10859" href="Maps.html#10809" class="Bound"
      >&#961;</a
      ><a name="10860"
      > </a
      ><a name="10861" href="Maps.html#10462" class="Function Operator"
      >,</a
      ><a name="10862"
      > </a
      ><a name="10863" href="Maps.html#10828" class="Bound"
      >x</a
      ><a name="10864"
      > </a
      ><a name="10865" href="Maps.html#10462" class="Function Operator"
      >&#8614;</a
      ><a name="10866"
      > </a
      ><a name="10867" href="Maps.html#10837" class="Bound"
      >v</a
      ><a name="10868" class="Symbol"
      >)</a
      ><a name="10869"
      > </a
      ><a name="10870" href="Maps.html#10828" class="Bound"
      >x</a
      ><a name="10871"
      > </a
      ><a name="10872" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="10873"
      > </a
      ><a name="10874" href="https://agda.github.io/agda-stdlib/Data.Maybe.Base.html#373" class="InductiveConstructor"
      >just</a
      ><a name="10878"
      > </a
      ><a name="10879" href="Maps.html#10837" class="Bound"
      >v</a
      ><a name="10880"
      >
  </a
      ><a name="10883" href="Maps.html#10790" class="Function"
      >update-eq</a
      ><a name="10892"
      > </a
      ><a name="10893" href="Maps.html#10893" class="Bound"
      >&#961;</a
      ><a name="10894"
      > </a
      ><a name="10895" href="Maps.html#10895" class="Bound"
      >x</a
      ><a name="10896"
      > </a
      ><a name="10897" href="Maps.html#10897" class="Bound"
      >v</a
      ><a name="10898"
      > </a
      ><a name="10899" class="Symbol"
      >=</a
      ><a name="10900"
      > </a
      ><a name="10901" href="Maps.html#5938" class="Postulate"
      >TotalMap.update-eq</a
      ><a name="10919"
      > </a
      ><a name="10920" href="Maps.html#10893" class="Bound"
      >&#961;</a
      ><a name="10921"
      > </a
      ><a name="10922" href="Maps.html#10895" class="Bound"
      >x</a
      ><a name="10923"
      > </a
      ><a name="10924" class="Symbol"
      >(</a
      ><a name="10925" href="https://agda.github.io/agda-stdlib/Data.Maybe.Base.html#373" class="InductiveConstructor"
      >just</a
      ><a name="10929"
      > </a
      ><a name="10930" href="Maps.html#10897" class="Bound"
      >v</a
      ><a name="10931" class="Symbol"
      >)</a
      >
{% endraw %}</pre>

<pre class="Agda">{% raw %}
  <a name="10960" href="Maps.html#10960" class="Function"
      >update-neq</a
      ><a name="10970"
      > </a
      ><a name="10971" class="Symbol"
      >:</a
      ><a name="10972"
      > </a
      ><a name="10973" class="Symbol"
      >&#8704;</a
      ><a name="10974"
      > </a
      ><a name="10975" class="Symbol"
      >{</a
      ><a name="10976" href="Maps.html#10976" class="Bound"
      >A</a
      ><a name="10977" class="Symbol"
      >}</a
      ><a name="10978"
      > </a
      ><a name="10979" class="Symbol"
      >(</a
      ><a name="10980" href="Maps.html#10980" class="Bound"
      >&#961;</a
      ><a name="10981"
      > </a
      ><a name="10982" class="Symbol"
      >:</a
      ><a name="10983"
      > </a
      ><a name="10984" href="Maps.html#10226" class="Function"
      >PartialMap</a
      ><a name="10994"
      > </a
      ><a name="10995" href="Maps.html#10976" class="Bound"
      >A</a
      ><a name="10996" class="Symbol"
      >)</a
      ><a name="10997"
      > </a
      ><a name="10998" class="Symbol"
      >(</a
      ><a name="10999" href="Maps.html#10999" class="Bound"
      >x</a
      ><a name="11000"
      > </a
      ><a name="11001" class="Symbol"
      >:</a
      ><a name="11002"
      > </a
      ><a name="11003" href="Maps.html#2215" class="Datatype"
      >Id</a
      ><a name="11005" class="Symbol"
      >)</a
      ><a name="11006"
      > </a
      ><a name="11007" class="Symbol"
      >(</a
      ><a name="11008" href="Maps.html#11008" class="Bound"
      >v</a
      ><a name="11009"
      > </a
      ><a name="11010" class="Symbol"
      >:</a
      ><a name="11011"
      > </a
      ><a name="11012" href="Maps.html#10976" class="Bound"
      >A</a
      ><a name="11013" class="Symbol"
      >)</a
      ><a name="11014"
      > </a
      ><a name="11015" class="Symbol"
      >(</a
      ><a name="11016" href="Maps.html#11016" class="Bound"
      >y</a
      ><a name="11017"
      > </a
      ><a name="11018" class="Symbol"
      >:</a
      ><a name="11019"
      > </a
      ><a name="11020" href="Maps.html#2215" class="Datatype"
      >Id</a
      ><a name="11022" class="Symbol"
      >)</a
      ><a name="11023"
      >
             </a
      ><a name="11037" class="Symbol"
      >&#8594;</a
      ><a name="11038"
      > </a
      ><a name="11039" href="Maps.html#10999" class="Bound"
      >x</a
      ><a name="11040"
      > </a
      ><a name="11041" href="https://agda.github.io/agda-stdlib/Relation.Binary.Core.html#4493" class="Function Operator"
      >&#8802;</a
      ><a name="11042"
      > </a
      ><a name="11043" href="Maps.html#11016" class="Bound"
      >y</a
      ><a name="11044"
      > </a
      ><a name="11045" class="Symbol"
      >&#8594;</a
      ><a name="11046"
      > </a
      ><a name="11047" class="Symbol"
      >(</a
      ><a name="11048" href="Maps.html#10980" class="Bound"
      >&#961;</a
      ><a name="11049"
      > </a
      ><a name="11050" href="Maps.html#10462" class="Function Operator"
      >,</a
      ><a name="11051"
      > </a
      ><a name="11052" href="Maps.html#10999" class="Bound"
      >x</a
      ><a name="11053"
      > </a
      ><a name="11054" href="Maps.html#10462" class="Function Operator"
      >&#8614;</a
      ><a name="11055"
      > </a
      ><a name="11056" href="Maps.html#11008" class="Bound"
      >v</a
      ><a name="11057" class="Symbol"
      >)</a
      ><a name="11058"
      > </a
      ><a name="11059" href="Maps.html#11016" class="Bound"
      >y</a
      ><a name="11060"
      > </a
      ><a name="11061" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="11062"
      > </a
      ><a name="11063" href="Maps.html#10980" class="Bound"
      >&#961;</a
      ><a name="11064"
      > </a
      ><a name="11065" href="Maps.html#11016" class="Bound"
      >y</a
      ><a name="11066"
      >
  </a
      ><a name="11069" href="Maps.html#10960" class="Function"
      >update-neq</a
      ><a name="11079"
      > </a
      ><a name="11080" href="Maps.html#11080" class="Bound"
      >&#961;</a
      ><a name="11081"
      > </a
      ><a name="11082" href="Maps.html#11082" class="Bound"
      >x</a
      ><a name="11083"
      > </a
      ><a name="11084" href="Maps.html#11084" class="Bound"
      >v</a
      ><a name="11085"
      > </a
      ><a name="11086" href="Maps.html#11086" class="Bound"
      >y</a
      ><a name="11087"
      > </a
      ><a name="11088" href="Maps.html#11088" class="Bound"
      >x&#8802;y</a
      ><a name="11091"
      > </a
      ><a name="11092" class="Symbol"
      >=</a
      ><a name="11093"
      > </a
      ><a name="11094" href="Maps.html#6494" class="Function"
      >TotalMap.update-neq</a
      ><a name="11113"
      > </a
      ><a name="11114" href="Maps.html#11080" class="Bound"
      >&#961;</a
      ><a name="11115"
      > </a
      ><a name="11116" href="Maps.html#11082" class="Bound"
      >x</a
      ><a name="11117"
      > </a
      ><a name="11118" class="Symbol"
      >(</a
      ><a name="11119" href="https://agda.github.io/agda-stdlib/Data.Maybe.Base.html#373" class="InductiveConstructor"
      >just</a
      ><a name="11123"
      > </a
      ><a name="11124" href="Maps.html#11084" class="Bound"
      >v</a
      ><a name="11125" class="Symbol"
      >)</a
      ><a name="11126"
      > </a
      ><a name="11127" href="Maps.html#11086" class="Bound"
      >y</a
      ><a name="11128"
      > </a
      ><a name="11129" href="Maps.html#11088" class="Bound"
      >x&#8802;y</a
      >
{% endraw %}</pre>

<pre class="Agda">{% raw %}
  <a name="11160" href="Maps.html#11160" class="Function"
      >update-shadow</a
      ><a name="11173"
      > </a
      ><a name="11174" class="Symbol"
      >:</a
      ><a name="11175"
      > </a
      ><a name="11176" class="Symbol"
      >&#8704;</a
      ><a name="11177"
      > </a
      ><a name="11178" class="Symbol"
      >{</a
      ><a name="11179" href="Maps.html#11179" class="Bound"
      >A</a
      ><a name="11180" class="Symbol"
      >}</a
      ><a name="11181"
      > </a
      ><a name="11182" class="Symbol"
      >(</a
      ><a name="11183" href="Maps.html#11183" class="Bound"
      >&#961;</a
      ><a name="11184"
      > </a
      ><a name="11185" class="Symbol"
      >:</a
      ><a name="11186"
      > </a
      ><a name="11187" href="Maps.html#10226" class="Function"
      >PartialMap</a
      ><a name="11197"
      > </a
      ><a name="11198" href="Maps.html#11179" class="Bound"
      >A</a
      ><a name="11199" class="Symbol"
      >)</a
      ><a name="11200"
      > </a
      ><a name="11201" class="Symbol"
      >(</a
      ><a name="11202" href="Maps.html#11202" class="Bound"
      >x</a
      ><a name="11203"
      > </a
      ><a name="11204" class="Symbol"
      >:</a
      ><a name="11205"
      > </a
      ><a name="11206" href="Maps.html#2215" class="Datatype"
      >Id</a
      ><a name="11208" class="Symbol"
      >)</a
      ><a name="11209"
      > </a
      ><a name="11210" class="Symbol"
      >(</a
      ><a name="11211" href="Maps.html#11211" class="Bound"
      >v</a
      ><a name="11212"
      > </a
      ><a name="11213" href="Maps.html#11213" class="Bound"
      >w</a
      ><a name="11214"
      > </a
      ><a name="11215" class="Symbol"
      >:</a
      ><a name="11216"
      > </a
      ><a name="11217" href="Maps.html#11179" class="Bound"
      >A</a
      ><a name="11218" class="Symbol"
      >)</a
      ><a name="11219"
      > 
                </a
      ><a name="11237" class="Symbol"
      >&#8594;</a
      ><a name="11238"
      > </a
      ><a name="11239" class="Symbol"
      >(</a
      ><a name="11240" href="Maps.html#11183" class="Bound"
      >&#961;</a
      ><a name="11241"
      > </a
      ><a name="11242" href="Maps.html#10462" class="Function Operator"
      >,</a
      ><a name="11243"
      > </a
      ><a name="11244" href="Maps.html#11202" class="Bound"
      >x</a
      ><a name="11245"
      > </a
      ><a name="11246" href="Maps.html#10462" class="Function Operator"
      >&#8614;</a
      ><a name="11247"
      > </a
      ><a name="11248" href="Maps.html#11211" class="Bound"
      >v</a
      ><a name="11249"
      > </a
      ><a name="11250" href="Maps.html#10462" class="Function Operator"
      >,</a
      ><a name="11251"
      > </a
      ><a name="11252" href="Maps.html#11202" class="Bound"
      >x</a
      ><a name="11253"
      > </a
      ><a name="11254" href="Maps.html#10462" class="Function Operator"
      >&#8614;</a
      ><a name="11255"
      > </a
      ><a name="11256" href="Maps.html#11213" class="Bound"
      >w</a
      ><a name="11257" class="Symbol"
      >)</a
      ><a name="11258"
      > </a
      ><a name="11259" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="11260"
      > </a
      ><a name="11261" class="Symbol"
      >(</a
      ><a name="11262" href="Maps.html#11183" class="Bound"
      >&#961;</a
      ><a name="11263"
      > </a
      ><a name="11264" href="Maps.html#10462" class="Function Operator"
      >,</a
      ><a name="11265"
      > </a
      ><a name="11266" href="Maps.html#11202" class="Bound"
      >x</a
      ><a name="11267"
      > </a
      ><a name="11268" href="Maps.html#10462" class="Function Operator"
      >&#8614;</a
      ><a name="11269"
      > </a
      ><a name="11270" href="Maps.html#11213" class="Bound"
      >w</a
      ><a name="11271" class="Symbol"
      >)</a
      ><a name="11272"
      >
  </a
      ><a name="11275" href="Maps.html#11160" class="Function"
      >update-shadow</a
      ><a name="11288"
      > </a
      ><a name="11289" href="Maps.html#11289" class="Bound"
      >&#961;</a
      ><a name="11290"
      > </a
      ><a name="11291" href="Maps.html#11291" class="Bound"
      >x</a
      ><a name="11292"
      > </a
      ><a name="11293" href="Maps.html#11293" class="Bound"
      >v</a
      ><a name="11294"
      > </a
      ><a name="11295" href="Maps.html#11295" class="Bound"
      >w</a
      ><a name="11296"
      > </a
      ><a name="11297" class="Symbol"
      >=</a
      ><a name="11298"
      > </a
      ><a name="11299" href="Maps.html#7313" class="Postulate"
      >TotalMap.update-shadow</a
      ><a name="11321"
      > </a
      ><a name="11322" href="Maps.html#11289" class="Bound"
      >&#961;</a
      ><a name="11323"
      > </a
      ><a name="11324" href="Maps.html#11291" class="Bound"
      >x</a
      ><a name="11325"
      > </a
      ><a name="11326" class="Symbol"
      >(</a
      ><a name="11327" href="https://agda.github.io/agda-stdlib/Data.Maybe.Base.html#373" class="InductiveConstructor"
      >just</a
      ><a name="11331"
      > </a
      ><a name="11332" href="Maps.html#11293" class="Bound"
      >v</a
      ><a name="11333" class="Symbol"
      >)</a
      ><a name="11334"
      > </a
      ><a name="11335" class="Symbol"
      >(</a
      ><a name="11336" href="https://agda.github.io/agda-stdlib/Data.Maybe.Base.html#373" class="InductiveConstructor"
      >just</a
      ><a name="11340"
      > </a
      ><a name="11341" href="Maps.html#11295" class="Bound"
      >w</a
      ><a name="11342" class="Symbol"
      >)</a
      >
{% endraw %}</pre>

<pre class="Agda">{% raw %}
  <a name="11371" href="Maps.html#11371" class="Function"
      >update-same</a
      ><a name="11382"
      > </a
      ><a name="11383" class="Symbol"
      >:</a
      ><a name="11384"
      > </a
      ><a name="11385" class="Symbol"
      >&#8704;</a
      ><a name="11386"
      > </a
      ><a name="11387" class="Symbol"
      >{</a
      ><a name="11388" href="Maps.html#11388" class="Bound"
      >A</a
      ><a name="11389" class="Symbol"
      >}</a
      ><a name="11390"
      > </a
      ><a name="11391" class="Symbol"
      >(</a
      ><a name="11392" href="Maps.html#11392" class="Bound"
      >&#961;</a
      ><a name="11393"
      > </a
      ><a name="11394" class="Symbol"
      >:</a
      ><a name="11395"
      > </a
      ><a name="11396" href="Maps.html#10226" class="Function"
      >PartialMap</a
      ><a name="11406"
      > </a
      ><a name="11407" href="Maps.html#11388" class="Bound"
      >A</a
      ><a name="11408" class="Symbol"
      >)</a
      ><a name="11409"
      > </a
      ><a name="11410" class="Symbol"
      >(</a
      ><a name="11411" href="Maps.html#11411" class="Bound"
      >x</a
      ><a name="11412"
      > </a
      ><a name="11413" class="Symbol"
      >:</a
      ><a name="11414"
      > </a
      ><a name="11415" href="Maps.html#2215" class="Datatype"
      >Id</a
      ><a name="11417" class="Symbol"
      >)</a
      ><a name="11418"
      > </a
      ><a name="11419" class="Symbol"
      >(</a
      ><a name="11420" href="Maps.html#11420" class="Bound"
      >v</a
      ><a name="11421"
      > </a
      ><a name="11422" class="Symbol"
      >:</a
      ><a name="11423"
      > </a
      ><a name="11424" href="Maps.html#11388" class="Bound"
      >A</a
      ><a name="11425" class="Symbol"
      >)</a
      ><a name="11426"
      > 
              </a
      ><a name="11442" class="Symbol"
      >&#8594;</a
      ><a name="11443"
      > </a
      ><a name="11444" href="Maps.html#11392" class="Bound"
      >&#961;</a
      ><a name="11445"
      > </a
      ><a name="11446" href="Maps.html#11411" class="Bound"
      >x</a
      ><a name="11447"
      > </a
      ><a name="11448" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="11449"
      > </a
      ><a name="11450" href="https://agda.github.io/agda-stdlib/Data.Maybe.Base.html#373" class="InductiveConstructor"
      >just</a
      ><a name="11454"
      > </a
      ><a name="11455" href="Maps.html#11420" class="Bound"
      >v</a
      ><a name="11456"
      >
              </a
      ><a name="11471" class="Symbol"
      >&#8594;</a
      ><a name="11472"
      > </a
      ><a name="11473" class="Symbol"
      >(</a
      ><a name="11474" href="Maps.html#11392" class="Bound"
      >&#961;</a
      ><a name="11475"
      > </a
      ><a name="11476" href="Maps.html#10462" class="Function Operator"
      >,</a
      ><a name="11477"
      > </a
      ><a name="11478" href="Maps.html#11411" class="Bound"
      >x</a
      ><a name="11479"
      > </a
      ><a name="11480" href="Maps.html#10462" class="Function Operator"
      >&#8614;</a
      ><a name="11481"
      > </a
      ><a name="11482" href="Maps.html#11420" class="Bound"
      >v</a
      ><a name="11483" class="Symbol"
      >)</a
      ><a name="11484"
      > </a
      ><a name="11485" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="11486"
      > </a
      ><a name="11487" href="Maps.html#11392" class="Bound"
      >&#961;</a
      ><a name="11488"
      >
  </a
      ><a name="11491" href="Maps.html#11371" class="Function"
      >update-same</a
      ><a name="11502"
      > </a
      ><a name="11503" href="Maps.html#11503" class="Bound"
      >&#961;</a
      ><a name="11504"
      > </a
      ><a name="11505" href="Maps.html#11505" class="Bound"
      >x</a
      ><a name="11506"
      > </a
      ><a name="11507" href="Maps.html#11507" class="Bound"
      >v</a
      ><a name="11508"
      > </a
      ><a name="11509" href="Maps.html#11509" class="Bound"
      >&#961;x&#8801;v</a
      ><a name="11513"
      > </a
      ><a name="11514" class="Keyword"
      >rewrite</a
      ><a name="11521"
      > </a
      ><a name="11522" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.Core.html#565" class="Function"
      >sym</a
      ><a name="11525"
      > </a
      ><a name="11526" href="Maps.html#11509" class="Bound"
      >&#961;x&#8801;v</a
      ><a name="11530"
      > </a
      ><a name="11531" class="Symbol"
      >=</a
      ><a name="11532"
      > </a
      ><a name="11533" href="Maps.html#8048" class="Postulate"
      >TotalMap.update-same</a
      ><a name="11553"
      > </a
      ><a name="11554" href="Maps.html#11503" class="Bound"
      >&#961;</a
      ><a name="11555"
      > </a
      ><a name="11556" href="Maps.html#11505" class="Bound"
      >x</a
      >
{% endraw %}</pre>

<pre class="Agda">{% raw %}
  <a name="11585" href="Maps.html#11585" class="Function"
      >update-permute</a
      ><a name="11599"
      > </a
      ><a name="11600" class="Symbol"
      >:</a
      ><a name="11601"
      > </a
      ><a name="11602" class="Symbol"
      >&#8704;</a
      ><a name="11603"
      > </a
      ><a name="11604" class="Symbol"
      >{</a
      ><a name="11605" href="Maps.html#11605" class="Bound"
      >A</a
      ><a name="11606" class="Symbol"
      >}</a
      ><a name="11607"
      > </a
      ><a name="11608" class="Symbol"
      >(</a
      ><a name="11609" href="Maps.html#11609" class="Bound"
      >&#961;</a
      ><a name="11610"
      > </a
      ><a name="11611" class="Symbol"
      >:</a
      ><a name="11612"
      > </a
      ><a name="11613" href="Maps.html#10226" class="Function"
      >PartialMap</a
      ><a name="11623"
      > </a
      ><a name="11624" href="Maps.html#11605" class="Bound"
      >A</a
      ><a name="11625" class="Symbol"
      >)</a
      ><a name="11626"
      > </a
      ><a name="11627" class="Symbol"
      >(</a
      ><a name="11628" href="Maps.html#11628" class="Bound"
      >x</a
      ><a name="11629"
      > </a
      ><a name="11630" class="Symbol"
      >:</a
      ><a name="11631"
      > </a
      ><a name="11632" href="Maps.html#2215" class="Datatype"
      >Id</a
      ><a name="11634" class="Symbol"
      >)</a
      ><a name="11635"
      > </a
      ><a name="11636" class="Symbol"
      >(</a
      ><a name="11637" href="Maps.html#11637" class="Bound"
      >v</a
      ><a name="11638"
      > </a
      ><a name="11639" class="Symbol"
      >:</a
      ><a name="11640"
      > </a
      ><a name="11641" href="Maps.html#11605" class="Bound"
      >A</a
      ><a name="11642" class="Symbol"
      >)</a
      ><a name="11643"
      > </a
      ><a name="11644" class="Symbol"
      >(</a
      ><a name="11645" href="Maps.html#11645" class="Bound"
      >y</a
      ><a name="11646"
      > </a
      ><a name="11647" class="Symbol"
      >:</a
      ><a name="11648"
      > </a
      ><a name="11649" href="Maps.html#2215" class="Datatype"
      >Id</a
      ><a name="11651" class="Symbol"
      >)</a
      ><a name="11652"
      > </a
      ><a name="11653" class="Symbol"
      >(</a
      ><a name="11654" href="Maps.html#11654" class="Bound"
      >w</a
      ><a name="11655"
      > </a
      ><a name="11656" class="Symbol"
      >:</a
      ><a name="11657"
      > </a
      ><a name="11658" href="Maps.html#11605" class="Bound"
      >A</a
      ><a name="11659" class="Symbol"
      >)</a
      ><a name="11660"
      > 
                 </a
      ><a name="11679" class="Symbol"
      >&#8594;</a
      ><a name="11680"
      > </a
      ><a name="11681" href="Maps.html#11628" class="Bound"
      >x</a
      ><a name="11682"
      > </a
      ><a name="11683" href="https://agda.github.io/agda-stdlib/Relation.Binary.Core.html#4493" class="Function Operator"
      >&#8802;</a
      ><a name="11684"
      > </a
      ><a name="11685" href="Maps.html#11645" class="Bound"
      >y</a
      ><a name="11686"
      > </a
      ><a name="11687" class="Symbol"
      >&#8594;</a
      ><a name="11688"
      > </a
      ><a name="11689" class="Symbol"
      >(</a
      ><a name="11690" href="Maps.html#11609" class="Bound"
      >&#961;</a
      ><a name="11691"
      > </a
      ><a name="11692" href="Maps.html#10462" class="Function Operator"
      >,</a
      ><a name="11693"
      > </a
      ><a name="11694" href="Maps.html#11628" class="Bound"
      >x</a
      ><a name="11695"
      > </a
      ><a name="11696" href="Maps.html#10462" class="Function Operator"
      >&#8614;</a
      ><a name="11697"
      > </a
      ><a name="11698" href="Maps.html#11637" class="Bound"
      >v</a
      ><a name="11699"
      > </a
      ><a name="11700" href="Maps.html#10462" class="Function Operator"
      >,</a
      ><a name="11701"
      > </a
      ><a name="11702" href="Maps.html#11645" class="Bound"
      >y</a
      ><a name="11703"
      > </a
      ><a name="11704" href="Maps.html#10462" class="Function Operator"
      >&#8614;</a
      ><a name="11705"
      > </a
      ><a name="11706" href="Maps.html#11654" class="Bound"
      >w</a
      ><a name="11707" class="Symbol"
      >)</a
      ><a name="11708"
      > </a
      ><a name="11709" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="11710"
      > </a
      ><a name="11711" class="Symbol"
      >(</a
      ><a name="11712" href="Maps.html#11609" class="Bound"
      >&#961;</a
      ><a name="11713"
      > </a
      ><a name="11714" href="Maps.html#10462" class="Function Operator"
      >,</a
      ><a name="11715"
      > </a
      ><a name="11716" href="Maps.html#11645" class="Bound"
      >y</a
      ><a name="11717"
      > </a
      ><a name="11718" href="Maps.html#10462" class="Function Operator"
      >&#8614;</a
      ><a name="11719"
      > </a
      ><a name="11720" href="Maps.html#11654" class="Bound"
      >w</a
      ><a name="11721"
      > </a
      ><a name="11722" href="Maps.html#10462" class="Function Operator"
      >,</a
      ><a name="11723"
      > </a
      ><a name="11724" href="Maps.html#11628" class="Bound"
      >x</a
      ><a name="11725"
      > </a
      ><a name="11726" href="Maps.html#10462" class="Function Operator"
      >&#8614;</a
      ><a name="11727"
      > </a
      ><a name="11728" href="Maps.html#11637" class="Bound"
      >v</a
      ><a name="11729" class="Symbol"
      >)</a
      ><a name="11730"
      >
  </a
      ><a name="11733" href="Maps.html#11585" class="Function"
      >update-permute</a
      ><a name="11747"
      > </a
      ><a name="11748" href="Maps.html#11748" class="Bound"
      >&#961;</a
      ><a name="11749"
      > </a
      ><a name="11750" href="Maps.html#11750" class="Bound"
      >x</a
      ><a name="11751"
      > </a
      ><a name="11752" href="Maps.html#11752" class="Bound"
      >v</a
      ><a name="11753"
      > </a
      ><a name="11754" href="Maps.html#11754" class="Bound"
      >y</a
      ><a name="11755"
      > </a
      ><a name="11756" href="Maps.html#11756" class="Bound"
      >w</a
      ><a name="11757"
      > </a
      ><a name="11758" href="Maps.html#11758" class="Bound"
      >x&#8802;y</a
      ><a name="11761"
      > </a
      ><a name="11762" class="Symbol"
      >=</a
      ><a name="11763"
      > </a
      ><a name="11764" href="Maps.html#8648" class="Postulate"
      >TotalMap.update-permute</a
      ><a name="11787"
      > </a
      ><a name="11788" href="Maps.html#11748" class="Bound"
      >&#961;</a
      ><a name="11789"
      > </a
      ><a name="11790" href="Maps.html#11750" class="Bound"
      >x</a
      ><a name="11791"
      > </a
      ><a name="11792" class="Symbol"
      >(</a
      ><a name="11793" href="https://agda.github.io/agda-stdlib/Data.Maybe.Base.html#373" class="InductiveConstructor"
      >just</a
      ><a name="11797"
      > </a
      ><a name="11798" href="Maps.html#11752" class="Bound"
      >v</a
      ><a name="11799" class="Symbol"
      >)</a
      ><a name="11800"
      > </a
      ><a name="11801" href="Maps.html#11754" class="Bound"
      >y</a
      ><a name="11802"
      > </a
      ><a name="11803" class="Symbol"
      >(</a
      ><a name="11804" href="https://agda.github.io/agda-stdlib/Data.Maybe.Base.html#373" class="InductiveConstructor"
      >just</a
      ><a name="11808"
      > </a
      ><a name="11809" href="Maps.html#11756" class="Bound"
      >w</a
      ><a name="11810" class="Symbol"
      >)</a
      ><a name="11811"
      > </a
      ><a name="11812" href="Maps.html#11758" class="Bound"
      >x&#8802;y</a
      >
{% endraw %}</pre>
