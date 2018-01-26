---
title     : "Logic: Propositions as Type"
layout    : page
permalink : /Logic
---

This chapter describes the connection between logical connectives
(conjunction, disjunction, implication, for all, there exists,
equivalence) and datatypes (product, sum, function, dependent
function, dependent product, Martin Löf equivalence).

## Imports

<pre class="Agda">{% raw %}
<a name="359" class="Keyword"
      >import</a
      ><a name="365"
      > </a
      ><a name="366" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#1" class="Module"
      >Relation.Binary.PropositionalEquality</a
      ><a name="403"
      > </a
      ><a name="404" class="Symbol"
      >as</a
      ><a name="406"
      > </a
      ><a name="407" class="Module"
      >Eq</a
      ><a name="409"
      >
</a
      ><a name="410" class="Keyword"
      >open</a
      ><a name="414"
      > </a
      ><a name="415" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#1" class="Module"
      >Eq</a
      ><a name="417"
      > </a
      ><a name="418" class="Keyword"
      >using</a
      ><a name="423"
      > </a
      ><a name="424" class="Symbol"
      >(</a
      ><a name="425" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >_&#8801;_</a
      ><a name="428" class="Symbol"
      >;</a
      ><a name="429"
      > </a
      ><a name="430" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="434" class="Symbol"
      >;</a
      ><a name="435"
      > </a
      ><a name="436" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.Core.html#565" class="Function"
      >sym</a
      ><a name="439" class="Symbol"
      >;</a
      ><a name="440"
      > </a
      ><a name="441" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.Core.html#632" class="Function"
      >trans</a
      ><a name="446" class="Symbol"
      >;</a
      ><a name="447"
      > </a
      ><a name="448" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#1036" class="Function"
      >cong</a
      ><a name="452" class="Symbol"
      >;</a
      ><a name="453"
      > </a
      ><a name="454" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#1140" class="Function"
      >cong-app</a
      ><a name="462" class="Symbol"
      >)</a
      ><a name="463"
      >
</a
      ><a name="464" class="Keyword"
      >open</a
      ><a name="468"
      > </a
      ><a name="469" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#243" class="Module"
      >Eq.</a
      ><a name="472" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#5706" class="Module"
      >&#8801;-Reasoning</a
      ><a name="483"
      >
</a
      ><a name="484" class="Keyword"
      >open</a
      ><a name="488"
      > </a
      ><a name="489" class="Keyword"
      >import</a
      ><a name="495"
      > </a
      ><a name="496" href="https://agda.github.io/agda-stdlib/Data.Nat.html#1" class="Module"
      >Data.Nat</a
      ><a name="504"
      > </a
      ><a name="505" class="Keyword"
      >using</a
      ><a name="510"
      > </a
      ><a name="511" class="Symbol"
      >(</a
      ><a name="512" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#97" class="Datatype"
      >&#8469;</a
      ><a name="513" class="Symbol"
      >;</a
      ><a name="514"
      > </a
      ><a name="515" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#115" class="InductiveConstructor"
      >zero</a
      ><a name="519" class="Symbol"
      >;</a
      ><a name="520"
      > </a
      ><a name="521" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor"
      >suc</a
      ><a name="524" class="Symbol"
      >)</a
      ><a name="525"
      >
</a
      ><a name="526" class="Keyword"
      >open</a
      ><a name="530"
      > </a
      ><a name="531" class="Keyword"
      >import</a
      ><a name="537"
      > </a
      ><a name="538" href="Agda.Primitive.html#1" class="Module"
      >Agda.Primitive</a
      ><a name="552"
      > </a
      ><a name="553" class="Keyword"
      >using</a
      ><a name="558"
      > </a
      ><a name="559" class="Symbol"
      >(</a
      ><a name="560" href="Agda.Primitive.html#408" class="Postulate"
      >Level</a
      ><a name="565" class="Symbol"
      >;</a
      ><a name="566"
      > </a
      ><a name="567" href="Agda.Primitive.html#609" class="Primitive"
      >lzero</a
      ><a name="572" class="Symbol"
      >;</a
      ><a name="573"
      > </a
      ><a name="574" href="Agda.Primitive.html#625" class="Primitive"
      >lsuc</a
      ><a name="578" class="Symbol"
      >)</a
      >
{% endraw %}</pre>

This chapter introduces the basic concepts of logic, including
conjunction, disjunction, true, false, implication, negation,
universal quantification, and existential quantification.
Each concept of logic is represented by a corresponding standard
data type.

+ *conjunction* is *product*
+ *disjunction* is *sum*
+ *true* is *unit type*
+ *false* is *empty type*
+ *implication* is *function space*
+ *negation* is *function to empty type*
+ *universal quantification* is *dependent function*
+ *existential quantification* is *dependent product*

We also discuss how equality is represented, and the relation
between *intuitionistic* and *classical* logic.


## Isomorphism

As a prelude, we begin by introducing the notion of isomorphism.
In set theory, two sets are isomorphism if they are in 1-to-1 correspondence.
Here is the formal definition of isomorphism.
<pre class="Agda">{% raw %}
<a name="1471" class="Keyword"
      >record</a
      ><a name="1477"
      > </a
      ><a name="1478" href="Logic.html#1478" class="Record Operator"
      >_&#8771;_</a
      ><a name="1481"
      > </a
      ><a name="1482" class="Symbol"
      >(</a
      ><a name="1483" href="Logic.html#1483" class="Bound"
      >A</a
      ><a name="1484"
      > </a
      ><a name="1485" href="Logic.html#1485" class="Bound"
      >B</a
      ><a name="1486"
      > </a
      ><a name="1487" class="Symbol"
      >:</a
      ><a name="1488"
      > </a
      ><a name="1489" class="PrimitiveType"
      >Set</a
      ><a name="1492" class="Symbol"
      >)</a
      ><a name="1493"
      > </a
      ><a name="1494" class="Symbol"
      >:</a
      ><a name="1495"
      > </a
      ><a name="1496" class="PrimitiveType"
      >Set</a
      ><a name="1499"
      > </a
      ><a name="1500" class="Keyword"
      >where</a
      ><a name="1505"
      >
  </a
      ><a name="1508" class="Keyword"
      >field</a
      ><a name="1513"
      >
    </a
      ><a name="1518" href="Logic.html#1518" class="Field"
      >to</a
      ><a name="1520"
      > </a
      ><a name="1521" class="Symbol"
      >:</a
      ><a name="1522"
      > </a
      ><a name="1523" href="Logic.html#1483" class="Bound"
      >A</a
      ><a name="1524"
      > </a
      ><a name="1525" class="Symbol"
      >&#8594;</a
      ><a name="1526"
      > </a
      ><a name="1527" href="Logic.html#1485" class="Bound"
      >B</a
      ><a name="1528"
      >
    </a
      ><a name="1533" href="Logic.html#1533" class="Field"
      >fro</a
      ><a name="1536"
      > </a
      ><a name="1537" class="Symbol"
      >:</a
      ><a name="1538"
      > </a
      ><a name="1539" href="Logic.html#1485" class="Bound"
      >B</a
      ><a name="1540"
      > </a
      ><a name="1541" class="Symbol"
      >&#8594;</a
      ><a name="1542"
      > </a
      ><a name="1543" href="Logic.html#1483" class="Bound"
      >A</a
      ><a name="1544"
      >
    </a
      ><a name="1549" href="Logic.html#1549" class="Field"
      >inv&#737;</a
      ><a name="1553"
      > </a
      ><a name="1554" class="Symbol"
      >:</a
      ><a name="1555"
      > </a
      ><a name="1556" class="Symbol"
      >&#8704;</a
      ><a name="1557"
      > </a
      ><a name="1558" class="Symbol"
      >(</a
      ><a name="1559" href="Logic.html#1559" class="Bound"
      >x</a
      ><a name="1560"
      > </a
      ><a name="1561" class="Symbol"
      >:</a
      ><a name="1562"
      > </a
      ><a name="1563" href="Logic.html#1483" class="Bound"
      >A</a
      ><a name="1564" class="Symbol"
      >)</a
      ><a name="1565"
      > </a
      ><a name="1566" class="Symbol"
      >&#8594;</a
      ><a name="1567"
      > </a
      ><a name="1568" href="Logic.html#1533" class="Field"
      >fro</a
      ><a name="1571"
      > </a
      ><a name="1572" class="Symbol"
      >(</a
      ><a name="1573" href="Logic.html#1518" class="Field"
      >to</a
      ><a name="1575"
      > </a
      ><a name="1576" href="Logic.html#1559" class="Bound"
      >x</a
      ><a name="1577" class="Symbol"
      >)</a
      ><a name="1578"
      > </a
      ><a name="1579" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="1580"
      > </a
      ><a name="1581" href="Logic.html#1559" class="Bound"
      >x</a
      ><a name="1582"
      >
    </a
      ><a name="1587" href="Logic.html#1587" class="Field"
      >inv&#691;</a
      ><a name="1591"
      > </a
      ><a name="1592" class="Symbol"
      >:</a
      ><a name="1593"
      > </a
      ><a name="1594" class="Symbol"
      >&#8704;</a
      ><a name="1595"
      > </a
      ><a name="1596" class="Symbol"
      >(</a
      ><a name="1597" href="Logic.html#1597" class="Bound"
      >y</a
      ><a name="1598"
      > </a
      ><a name="1599" class="Symbol"
      >:</a
      ><a name="1600"
      > </a
      ><a name="1601" href="Logic.html#1485" class="Bound"
      >B</a
      ><a name="1602" class="Symbol"
      >)</a
      ><a name="1603"
      > </a
      ><a name="1604" class="Symbol"
      >&#8594;</a
      ><a name="1605"
      > </a
      ><a name="1606" href="Logic.html#1518" class="Field"
      >to</a
      ><a name="1608"
      > </a
      ><a name="1609" class="Symbol"
      >(</a
      ><a name="1610" href="Logic.html#1533" class="Field"
      >fro</a
      ><a name="1613"
      > </a
      ><a name="1614" href="Logic.html#1597" class="Bound"
      >y</a
      ><a name="1615" class="Symbol"
      >)</a
      ><a name="1616"
      > </a
      ><a name="1617" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="1618"
      > </a
      ><a name="1619" href="Logic.html#1597" class="Bound"
      >y</a
      ><a name="1620"
      >
</a
      ><a name="1621" class="Keyword"
      >open</a
      ><a name="1625"
      > </a
      ><a name="1626" href="Logic.html#1478" class="Module Operator"
      >_&#8771;_</a
      >
{% endraw %}</pre>
Let's unpack the definition. An isomorphism between sets `A` and `B` consists
of four things:
+ A function `to` from `A` to `B`,
+ A function `fro` from `B` back to `A`,
+ Evidence `invˡ` asserting that `to` followed by `from` is the identity,
+ Evidence `invʳ` asserting that `from` followed by `to` is the identity.
The declaration `open _≃_` makes avaialable the names `to`, `fro`,
`invˡ`, and `invʳ`, otherwise we would need to write `_≃_.to` and so on.

The above is our first example of a record declaration. It is equivalent
to a corresponding inductive data declaration.
<pre class="Agda">{% raw %}
<a name="2233" class="Keyword"
      >data</a
      ><a name="2237"
      > </a
      ><a name="2238" href="Logic.html#2238" class="Datatype Operator"
      >_&#8771;&#8242;_</a
      ><a name="2242"
      > </a
      ><a name="2243" class="Symbol"
      >:</a
      ><a name="2244"
      > </a
      ><a name="2245" class="PrimitiveType"
      >Set</a
      ><a name="2248"
      > </a
      ><a name="2249" class="Symbol"
      >&#8594;</a
      ><a name="2250"
      > </a
      ><a name="2251" class="PrimitiveType"
      >Set</a
      ><a name="2254"
      > </a
      ><a name="2255" class="Symbol"
      >&#8594;</a
      ><a name="2256"
      > </a
      ><a name="2257" class="PrimitiveType"
      >Set</a
      ><a name="2260"
      > </a
      ><a name="2261" class="Keyword"
      >where</a
      ><a name="2266"
      >
  </a
      ><a name="2269" href="Logic.html#2269" class="InductiveConstructor"
      >mk-&#8771;&#8242;</a
      ><a name="2274"
      > </a
      ><a name="2275" class="Symbol"
      >:</a
      ><a name="2276"
      > </a
      ><a name="2277" class="Symbol"
      >&#8704;</a
      ><a name="2278"
      > </a
      ><a name="2279" class="Symbol"
      >{</a
      ><a name="2280" href="Logic.html#2280" class="Bound"
      >A</a
      ><a name="2281"
      > </a
      ><a name="2282" href="Logic.html#2282" class="Bound"
      >B</a
      ><a name="2283"
      > </a
      ><a name="2284" class="Symbol"
      >:</a
      ><a name="2285"
      > </a
      ><a name="2286" class="PrimitiveType"
      >Set</a
      ><a name="2289" class="Symbol"
      >}</a
      ><a name="2290"
      > </a
      ><a name="2291" class="Symbol"
      >&#8594;</a
      ><a name="2292"
      >
         </a
      ><a name="2302" class="Symbol"
      >&#8704;</a
      ><a name="2303"
      > </a
      ><a name="2304" class="Symbol"
      >(</a
      ><a name="2305" href="Logic.html#2305" class="Bound"
      >to</a
      ><a name="2307"
      > </a
      ><a name="2308" class="Symbol"
      >:</a
      ><a name="2309"
      > </a
      ><a name="2310" href="Logic.html#2280" class="Bound"
      >A</a
      ><a name="2311"
      > </a
      ><a name="2312" class="Symbol"
      >&#8594;</a
      ><a name="2313"
      > </a
      ><a name="2314" href="Logic.html#2282" class="Bound"
      >B</a
      ><a name="2315" class="Symbol"
      >)</a
      ><a name="2316"
      > </a
      ><a name="2317" class="Symbol"
      >&#8594;</a
      ><a name="2318"
      >
         </a
      ><a name="2328" class="Symbol"
      >&#8704;</a
      ><a name="2329"
      > </a
      ><a name="2330" class="Symbol"
      >(</a
      ><a name="2331" href="Logic.html#2331" class="Bound"
      >fro</a
      ><a name="2334"
      > </a
      ><a name="2335" class="Symbol"
      >:</a
      ><a name="2336"
      > </a
      ><a name="2337" href="Logic.html#2282" class="Bound"
      >B</a
      ><a name="2338"
      > </a
      ><a name="2339" class="Symbol"
      >&#8594;</a
      ><a name="2340"
      > </a
      ><a name="2341" href="Logic.html#2280" class="Bound"
      >A</a
      ><a name="2342" class="Symbol"
      >)</a
      ><a name="2343"
      > </a
      ><a name="2344" class="Symbol"
      >&#8594;</a
      ><a name="2345"
      > 
         </a
      ><a name="2356" class="Symbol"
      >&#8704;</a
      ><a name="2357"
      > </a
      ><a name="2358" class="Symbol"
      >(</a
      ><a name="2359" href="Logic.html#2359" class="Bound"
      >inv&#737;</a
      ><a name="2363"
      > </a
      ><a name="2364" class="Symbol"
      >:</a
      ><a name="2365"
      > </a
      ><a name="2366" class="Symbol"
      >(&#8704;</a
      ><a name="2368"
      > </a
      ><a name="2369" class="Symbol"
      >(</a
      ><a name="2370" href="Logic.html#2370" class="Bound"
      >x</a
      ><a name="2371"
      > </a
      ><a name="2372" class="Symbol"
      >:</a
      ><a name="2373"
      > </a
      ><a name="2374" href="Logic.html#2280" class="Bound"
      >A</a
      ><a name="2375" class="Symbol"
      >)</a
      ><a name="2376"
      > </a
      ><a name="2377" class="Symbol"
      >&#8594;</a
      ><a name="2378"
      > </a
      ><a name="2379" href="Logic.html#2331" class="Bound"
      >fro</a
      ><a name="2382"
      > </a
      ><a name="2383" class="Symbol"
      >(</a
      ><a name="2384" href="Logic.html#2305" class="Bound"
      >to</a
      ><a name="2386"
      > </a
      ><a name="2387" href="Logic.html#2370" class="Bound"
      >x</a
      ><a name="2388" class="Symbol"
      >)</a
      ><a name="2389"
      > </a
      ><a name="2390" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="2391"
      > </a
      ><a name="2392" href="Logic.html#2370" class="Bound"
      >x</a
      ><a name="2393" class="Symbol"
      >))</a
      ><a name="2395"
      > </a
      ><a name="2396" class="Symbol"
      >&#8594;</a
      ><a name="2397"
      >
         </a
      ><a name="2407" class="Symbol"
      >&#8704;</a
      ><a name="2408"
      > </a
      ><a name="2409" class="Symbol"
      >(</a
      ><a name="2410" href="Logic.html#2410" class="Bound"
      >inv&#691;</a
      ><a name="2414"
      > </a
      ><a name="2415" class="Symbol"
      >:</a
      ><a name="2416"
      > </a
      ><a name="2417" class="Symbol"
      >(&#8704;</a
      ><a name="2419"
      > </a
      ><a name="2420" class="Symbol"
      >(</a
      ><a name="2421" href="Logic.html#2421" class="Bound"
      >y</a
      ><a name="2422"
      > </a
      ><a name="2423" class="Symbol"
      >:</a
      ><a name="2424"
      > </a
      ><a name="2425" href="Logic.html#2282" class="Bound"
      >B</a
      ><a name="2426" class="Symbol"
      >)</a
      ><a name="2427"
      > </a
      ><a name="2428" class="Symbol"
      >&#8594;</a
      ><a name="2429"
      > </a
      ><a name="2430" href="Logic.html#2305" class="Bound"
      >to</a
      ><a name="2432"
      > </a
      ><a name="2433" class="Symbol"
      >(</a
      ><a name="2434" href="Logic.html#2331" class="Bound"
      >fro</a
      ><a name="2437"
      > </a
      ><a name="2438" href="Logic.html#2421" class="Bound"
      >y</a
      ><a name="2439" class="Symbol"
      >)</a
      ><a name="2440"
      > </a
      ><a name="2441" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="2442"
      > </a
      ><a name="2443" href="Logic.html#2421" class="Bound"
      >y</a
      ><a name="2444" class="Symbol"
      >))</a
      ><a name="2446"
      > </a
      ><a name="2447" class="Symbol"
      >&#8594;</a
      ><a name="2448"
      >
         </a
      ><a name="2458" href="Logic.html#2280" class="Bound"
      >A</a
      ><a name="2459"
      > </a
      ><a name="2460" href="Logic.html#2238" class="Datatype Operator"
      >&#8771;&#8242;</a
      ><a name="2462"
      > </a
      ><a name="2463" href="Logic.html#2282" class="Bound"
      >B</a
      ><a name="2464"
      >

</a
      ><a name="2466" href="Logic.html#2466" class="Function"
      >to&#8242;</a
      ><a name="2469"
      > </a
      ><a name="2470" class="Symbol"
      >:</a
      ><a name="2471"
      > </a
      ><a name="2472" class="Symbol"
      >&#8704;</a
      ><a name="2473"
      > </a
      ><a name="2474" class="Symbol"
      >{</a
      ><a name="2475" href="Logic.html#2475" class="Bound"
      >A</a
      ><a name="2476"
      > </a
      ><a name="2477" href="Logic.html#2477" class="Bound"
      >B</a
      ><a name="2478"
      > </a
      ><a name="2479" class="Symbol"
      >:</a
      ><a name="2480"
      > </a
      ><a name="2481" class="PrimitiveType"
      >Set</a
      ><a name="2484" class="Symbol"
      >}</a
      ><a name="2485"
      > </a
      ><a name="2486" class="Symbol"
      >&#8594;</a
      ><a name="2487"
      > </a
      ><a name="2488" class="Symbol"
      >(</a
      ><a name="2489" href="Logic.html#2475" class="Bound"
      >A</a
      ><a name="2490"
      > </a
      ><a name="2491" href="Logic.html#2238" class="Datatype Operator"
      >&#8771;&#8242;</a
      ><a name="2493"
      > </a
      ><a name="2494" href="Logic.html#2477" class="Bound"
      >B</a
      ><a name="2495" class="Symbol"
      >)</a
      ><a name="2496"
      > </a
      ><a name="2497" class="Symbol"
      >&#8594;</a
      ><a name="2498"
      > </a
      ><a name="2499" class="Symbol"
      >(</a
      ><a name="2500" href="Logic.html#2475" class="Bound"
      >A</a
      ><a name="2501"
      > </a
      ><a name="2502" class="Symbol"
      >&#8594;</a
      ><a name="2503"
      > </a
      ><a name="2504" href="Logic.html#2477" class="Bound"
      >B</a
      ><a name="2505" class="Symbol"
      >)</a
      ><a name="2506"
      >
</a
      ><a name="2507" href="Logic.html#2466" class="Function"
      >to&#8242;</a
      ><a name="2510"
      > </a
      ><a name="2511" class="Symbol"
      >(</a
      ><a name="2512" href="Logic.html#2269" class="InductiveConstructor"
      >mk-&#8771;&#8242;</a
      ><a name="2517"
      > </a
      ><a name="2518" href="Logic.html#2518" class="Bound"
      >f</a
      ><a name="2519"
      > </a
      ><a name="2520" href="Logic.html#2520" class="Bound"
      >g</a
      ><a name="2521"
      > </a
      ><a name="2522" href="Logic.html#2522" class="Bound"
      >gfx&#8801;x</a
      ><a name="2527"
      > </a
      ><a name="2528" href="Logic.html#2528" class="Bound"
      >fgy&#8801;y</a
      ><a name="2533" class="Symbol"
      >)</a
      ><a name="2534"
      > </a
      ><a name="2535" class="Symbol"
      >=</a
      ><a name="2536"
      > </a
      ><a name="2537" href="Logic.html#2518" class="Bound"
      >f</a
      ><a name="2538"
      >

</a
      ><a name="2540" href="Logic.html#2540" class="Function"
      >fro&#8242;</a
      ><a name="2544"
      > </a
      ><a name="2545" class="Symbol"
      >:</a
      ><a name="2546"
      > </a
      ><a name="2547" class="Symbol"
      >&#8704;</a
      ><a name="2548"
      > </a
      ><a name="2549" class="Symbol"
      >{</a
      ><a name="2550" href="Logic.html#2550" class="Bound"
      >A</a
      ><a name="2551"
      > </a
      ><a name="2552" href="Logic.html#2552" class="Bound"
      >B</a
      ><a name="2553"
      > </a
      ><a name="2554" class="Symbol"
      >:</a
      ><a name="2555"
      > </a
      ><a name="2556" class="PrimitiveType"
      >Set</a
      ><a name="2559" class="Symbol"
      >}</a
      ><a name="2560"
      > </a
      ><a name="2561" class="Symbol"
      >&#8594;</a
      ><a name="2562"
      > </a
      ><a name="2563" class="Symbol"
      >(</a
      ><a name="2564" href="Logic.html#2550" class="Bound"
      >A</a
      ><a name="2565"
      > </a
      ><a name="2566" href="Logic.html#2238" class="Datatype Operator"
      >&#8771;&#8242;</a
      ><a name="2568"
      > </a
      ><a name="2569" href="Logic.html#2552" class="Bound"
      >B</a
      ><a name="2570" class="Symbol"
      >)</a
      ><a name="2571"
      > </a
      ><a name="2572" class="Symbol"
      >&#8594;</a
      ><a name="2573"
      > </a
      ><a name="2574" class="Symbol"
      >(</a
      ><a name="2575" href="Logic.html#2552" class="Bound"
      >B</a
      ><a name="2576"
      > </a
      ><a name="2577" class="Symbol"
      >&#8594;</a
      ><a name="2578"
      > </a
      ><a name="2579" href="Logic.html#2550" class="Bound"
      >A</a
      ><a name="2580" class="Symbol"
      >)</a
      ><a name="2581"
      >
</a
      ><a name="2582" href="Logic.html#2540" class="Function"
      >fro&#8242;</a
      ><a name="2586"
      > </a
      ><a name="2587" class="Symbol"
      >(</a
      ><a name="2588" href="Logic.html#2269" class="InductiveConstructor"
      >mk-&#8771;&#8242;</a
      ><a name="2593"
      > </a
      ><a name="2594" href="Logic.html#2594" class="Bound"
      >f</a
      ><a name="2595"
      > </a
      ><a name="2596" href="Logic.html#2596" class="Bound"
      >g</a
      ><a name="2597"
      > </a
      ><a name="2598" href="Logic.html#2598" class="Bound"
      >gfx&#8801;x</a
      ><a name="2603"
      > </a
      ><a name="2604" href="Logic.html#2604" class="Bound"
      >fgy&#8801;y</a
      ><a name="2609" class="Symbol"
      >)</a
      ><a name="2610"
      > </a
      ><a name="2611" class="Symbol"
      >=</a
      ><a name="2612"
      > </a
      ><a name="2613" href="Logic.html#2596" class="Bound"
      >g</a
      ><a name="2614"
      >

</a
      ><a name="2616" href="Logic.html#2616" class="Function"
      >inv&#737;&#8242;</a
      ><a name="2621"
      > </a
      ><a name="2622" class="Symbol"
      >:</a
      ><a name="2623"
      > </a
      ><a name="2624" class="Symbol"
      >&#8704;</a
      ><a name="2625"
      > </a
      ><a name="2626" class="Symbol"
      >{</a
      ><a name="2627" href="Logic.html#2627" class="Bound"
      >A</a
      ><a name="2628"
      > </a
      ><a name="2629" href="Logic.html#2629" class="Bound"
      >B</a
      ><a name="2630"
      > </a
      ><a name="2631" class="Symbol"
      >:</a
      ><a name="2632"
      > </a
      ><a name="2633" class="PrimitiveType"
      >Set</a
      ><a name="2636" class="Symbol"
      >}</a
      ><a name="2637"
      > </a
      ><a name="2638" class="Symbol"
      >&#8594;</a
      ><a name="2639"
      > </a
      ><a name="2640" class="Symbol"
      >(</a
      ><a name="2641" href="Logic.html#2641" class="Bound"
      >A&#8771;B</a
      ><a name="2644"
      > </a
      ><a name="2645" class="Symbol"
      >:</a
      ><a name="2646"
      > </a
      ><a name="2647" href="Logic.html#2627" class="Bound"
      >A</a
      ><a name="2648"
      > </a
      ><a name="2649" href="Logic.html#2238" class="Datatype Operator"
      >&#8771;&#8242;</a
      ><a name="2651"
      > </a
      ><a name="2652" href="Logic.html#2629" class="Bound"
      >B</a
      ><a name="2653" class="Symbol"
      >)</a
      ><a name="2654"
      > </a
      ><a name="2655" class="Symbol"
      >&#8594;</a
      ><a name="2656"
      > </a
      ><a name="2657" class="Symbol"
      >(&#8704;</a
      ><a name="2659"
      > </a
      ><a name="2660" class="Symbol"
      >(</a
      ><a name="2661" href="Logic.html#2661" class="Bound"
      >x</a
      ><a name="2662"
      > </a
      ><a name="2663" class="Symbol"
      >:</a
      ><a name="2664"
      > </a
      ><a name="2665" href="Logic.html#2627" class="Bound"
      >A</a
      ><a name="2666" class="Symbol"
      >)</a
      ><a name="2667"
      > </a
      ><a name="2668" class="Symbol"
      >&#8594;</a
      ><a name="2669"
      > </a
      ><a name="2670" href="Logic.html#2540" class="Function"
      >fro&#8242;</a
      ><a name="2674"
      > </a
      ><a name="2675" href="Logic.html#2641" class="Bound"
      >A&#8771;B</a
      ><a name="2678"
      > </a
      ><a name="2679" class="Symbol"
      >(</a
      ><a name="2680" href="Logic.html#2466" class="Function"
      >to&#8242;</a
      ><a name="2683"
      > </a
      ><a name="2684" href="Logic.html#2641" class="Bound"
      >A&#8771;B</a
      ><a name="2687"
      > </a
      ><a name="2688" href="Logic.html#2661" class="Bound"
      >x</a
      ><a name="2689" class="Symbol"
      >)</a
      ><a name="2690"
      > </a
      ><a name="2691" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="2692"
      > </a
      ><a name="2693" href="Logic.html#2661" class="Bound"
      >x</a
      ><a name="2694" class="Symbol"
      >)</a
      ><a name="2695"
      >
</a
      ><a name="2696" href="Logic.html#2616" class="Function"
      >inv&#737;&#8242;</a
      ><a name="2701"
      > </a
      ><a name="2702" class="Symbol"
      >(</a
      ><a name="2703" href="Logic.html#2269" class="InductiveConstructor"
      >mk-&#8771;&#8242;</a
      ><a name="2708"
      > </a
      ><a name="2709" href="Logic.html#2709" class="Bound"
      >f</a
      ><a name="2710"
      > </a
      ><a name="2711" href="Logic.html#2711" class="Bound"
      >g</a
      ><a name="2712"
      > </a
      ><a name="2713" href="Logic.html#2713" class="Bound"
      >gfx&#8801;x</a
      ><a name="2718"
      > </a
      ><a name="2719" href="Logic.html#2719" class="Bound"
      >fgy&#8801;y</a
      ><a name="2724" class="Symbol"
      >)</a
      ><a name="2725"
      > </a
      ><a name="2726" class="Symbol"
      >=</a
      ><a name="2727"
      > </a
      ><a name="2728" href="Logic.html#2713" class="Bound"
      >gfx&#8801;x</a
      ><a name="2733"
      >

</a
      ><a name="2735" href="Logic.html#2735" class="Function"
      >inv&#691;&#8242;</a
      ><a name="2740"
      > </a
      ><a name="2741" class="Symbol"
      >:</a
      ><a name="2742"
      > </a
      ><a name="2743" class="Symbol"
      >&#8704;</a
      ><a name="2744"
      > </a
      ><a name="2745" class="Symbol"
      >{</a
      ><a name="2746" href="Logic.html#2746" class="Bound"
      >A</a
      ><a name="2747"
      > </a
      ><a name="2748" href="Logic.html#2748" class="Bound"
      >B</a
      ><a name="2749"
      > </a
      ><a name="2750" class="Symbol"
      >:</a
      ><a name="2751"
      > </a
      ><a name="2752" class="PrimitiveType"
      >Set</a
      ><a name="2755" class="Symbol"
      >}</a
      ><a name="2756"
      > </a
      ><a name="2757" class="Symbol"
      >&#8594;</a
      ><a name="2758"
      > </a
      ><a name="2759" class="Symbol"
      >(</a
      ><a name="2760" href="Logic.html#2760" class="Bound"
      >A&#8771;B</a
      ><a name="2763"
      > </a
      ><a name="2764" class="Symbol"
      >:</a
      ><a name="2765"
      > </a
      ><a name="2766" href="Logic.html#2746" class="Bound"
      >A</a
      ><a name="2767"
      > </a
      ><a name="2768" href="Logic.html#2238" class="Datatype Operator"
      >&#8771;&#8242;</a
      ><a name="2770"
      > </a
      ><a name="2771" href="Logic.html#2748" class="Bound"
      >B</a
      ><a name="2772" class="Symbol"
      >)</a
      ><a name="2773"
      > </a
      ><a name="2774" class="Symbol"
      >&#8594;</a
      ><a name="2775"
      > </a
      ><a name="2776" class="Symbol"
      >(&#8704;</a
      ><a name="2778"
      > </a
      ><a name="2779" class="Symbol"
      >(</a
      ><a name="2780" href="Logic.html#2780" class="Bound"
      >y</a
      ><a name="2781"
      > </a
      ><a name="2782" class="Symbol"
      >:</a
      ><a name="2783"
      > </a
      ><a name="2784" href="Logic.html#2748" class="Bound"
      >B</a
      ><a name="2785" class="Symbol"
      >)</a
      ><a name="2786"
      > </a
      ><a name="2787" class="Symbol"
      >&#8594;</a
      ><a name="2788"
      > </a
      ><a name="2789" href="Logic.html#2466" class="Function"
      >to&#8242;</a
      ><a name="2792"
      > </a
      ><a name="2793" href="Logic.html#2760" class="Bound"
      >A&#8771;B</a
      ><a name="2796"
      > </a
      ><a name="2797" class="Symbol"
      >(</a
      ><a name="2798" href="Logic.html#2540" class="Function"
      >fro&#8242;</a
      ><a name="2802"
      > </a
      ><a name="2803" href="Logic.html#2760" class="Bound"
      >A&#8771;B</a
      ><a name="2806"
      > </a
      ><a name="2807" href="Logic.html#2780" class="Bound"
      >y</a
      ><a name="2808" class="Symbol"
      >)</a
      ><a name="2809"
      > </a
      ><a name="2810" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="2811"
      > </a
      ><a name="2812" href="Logic.html#2780" class="Bound"
      >y</a
      ><a name="2813" class="Symbol"
      >)</a
      ><a name="2814"
      >
</a
      ><a name="2815" href="Logic.html#2735" class="Function"
      >inv&#691;&#8242;</a
      ><a name="2820"
      > </a
      ><a name="2821" class="Symbol"
      >(</a
      ><a name="2822" href="Logic.html#2269" class="InductiveConstructor"
      >mk-&#8771;&#8242;</a
      ><a name="2827"
      > </a
      ><a name="2828" href="Logic.html#2828" class="Bound"
      >f</a
      ><a name="2829"
      > </a
      ><a name="2830" href="Logic.html#2830" class="Bound"
      >g</a
      ><a name="2831"
      > </a
      ><a name="2832" href="Logic.html#2832" class="Bound"
      >gfx&#8801;x</a
      ><a name="2837"
      > </a
      ><a name="2838" href="Logic.html#2838" class="Bound"
      >fgy&#8801;y</a
      ><a name="2843" class="Symbol"
      >)</a
      ><a name="2844"
      > </a
      ><a name="2845" class="Symbol"
      >=</a
      ><a name="2846"
      > </a
      ><a name="2847" href="Logic.html#2838" class="Bound"
      >fgy&#8801;y</a
      >
{% endraw %}</pre>
We construct values of the record type with the syntax:

    record
      { to = f
      ; fro = g
      ; invˡ = gfx≡x
      ; invʳ = fgy≡y
      }

which corresponds to using the constructor of the corresponding
inductive type:

    mk-≃′ f g gfx≡x fgy≡y

where `f`, `g`, `gfx≡x`, and `fgy≡y` are values of suitable types.
      
Isomorphism is an equivalence, meaning that it is reflexive, symmetric,
and transitive.  To show isomorphism is reflexive, we take both `to`
and `fro` to be the identity function.
<pre class="Agda">{% raw %}
<a name="3389" href="Logic.html#3389" class="Function"
      >&#8771;-refl</a
      ><a name="3395"
      > </a
      ><a name="3396" class="Symbol"
      >:</a
      ><a name="3397"
      > </a
      ><a name="3398" class="Symbol"
      >&#8704;</a
      ><a name="3399"
      > </a
      ><a name="3400" class="Symbol"
      >{</a
      ><a name="3401" href="Logic.html#3401" class="Bound"
      >A</a
      ><a name="3402"
      > </a
      ><a name="3403" class="Symbol"
      >:</a
      ><a name="3404"
      > </a
      ><a name="3405" class="PrimitiveType"
      >Set</a
      ><a name="3408" class="Symbol"
      >}</a
      ><a name="3409"
      > </a
      ><a name="3410" class="Symbol"
      >&#8594;</a
      ><a name="3411"
      > </a
      ><a name="3412" href="Logic.html#3401" class="Bound"
      >A</a
      ><a name="3413"
      > </a
      ><a name="3414" href="Logic.html#1478" class="Record Operator"
      >&#8771;</a
      ><a name="3415"
      > </a
      ><a name="3416" href="Logic.html#3401" class="Bound"
      >A</a
      ><a name="3417"
      >
</a
      ><a name="3418" href="Logic.html#3389" class="Function"
      >&#8771;-refl</a
      ><a name="3424"
      > </a
      ><a name="3425" class="Symbol"
      >=</a
      ><a name="3426"
      >
  </a
      ><a name="3429" class="Keyword"
      >record</a
      ><a name="3435"
      >
    </a
      ><a name="3440" class="Symbol"
      >{</a
      ><a name="3441"
      > </a
      ><a name="3442" class="Field"
      >to</a
      ><a name="3444"
      > </a
      ><a name="3445" class="Symbol"
      >=</a
      ><a name="3446"
      > </a
      ><a name="3447" class="Symbol"
      >&#955;</a
      ><a name="3448"
      > </a
      ><a name="3449" href="Logic.html#3449" class="Bound"
      >x</a
      ><a name="3450"
      > </a
      ><a name="3451" class="Symbol"
      >&#8594;</a
      ><a name="3452"
      > </a
      ><a name="3453" href="Logic.html#3449" class="Bound"
      >x</a
      ><a name="3454"
      >
    </a
      ><a name="3459" class="Symbol"
      >;</a
      ><a name="3460"
      > </a
      ><a name="3461" class="Field"
      >fro</a
      ><a name="3464"
      > </a
      ><a name="3465" class="Symbol"
      >=</a
      ><a name="3466"
      > </a
      ><a name="3467" class="Symbol"
      >&#955;</a
      ><a name="3468"
      > </a
      ><a name="3469" href="Logic.html#3469" class="Bound"
      >y</a
      ><a name="3470"
      > </a
      ><a name="3471" class="Symbol"
      >&#8594;</a
      ><a name="3472"
      > </a
      ><a name="3473" href="Logic.html#3469" class="Bound"
      >y</a
      ><a name="3474"
      >
    </a
      ><a name="3479" class="Symbol"
      >;</a
      ><a name="3480"
      > </a
      ><a name="3481" class="Field"
      >inv&#737;</a
      ><a name="3485"
      > </a
      ><a name="3486" class="Symbol"
      >=</a
      ><a name="3487"
      > </a
      ><a name="3488" class="Symbol"
      >&#955;</a
      ><a name="3489"
      > </a
      ><a name="3490" href="Logic.html#3490" class="Bound"
      >x</a
      ><a name="3491"
      > </a
      ><a name="3492" class="Symbol"
      >&#8594;</a
      ><a name="3493"
      > </a
      ><a name="3494" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="3498"
      >
    </a
      ><a name="3503" class="Symbol"
      >;</a
      ><a name="3504"
      > </a
      ><a name="3505" class="Field"
      >inv&#691;</a
      ><a name="3509"
      > </a
      ><a name="3510" class="Symbol"
      >=</a
      ><a name="3511"
      > </a
      ><a name="3512" class="Symbol"
      >&#955;</a
      ><a name="3513"
      > </a
      ><a name="3514" href="Logic.html#3514" class="Bound"
      >y</a
      ><a name="3515"
      > </a
      ><a name="3516" class="Symbol"
      >&#8594;</a
      ><a name="3517"
      > </a
      ><a name="3518" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="3522"
      >
    </a
      ><a name="3527" class="Symbol"
      >}</a
      >
{% endraw %}</pre>
To show isomorphism is symmetric, we simply swap the roles of `to`
and `fro`, and `invˡ` and `invʳ`.
<pre class="Agda">{% raw %}
<a name="3655" href="Logic.html#3655" class="Function"
      >&#8771;-sym</a
      ><a name="3660"
      > </a
      ><a name="3661" class="Symbol"
      >:</a
      ><a name="3662"
      > </a
      ><a name="3663" class="Symbol"
      >&#8704;</a
      ><a name="3664"
      > </a
      ><a name="3665" class="Symbol"
      >{</a
      ><a name="3666" href="Logic.html#3666" class="Bound"
      >A</a
      ><a name="3667"
      > </a
      ><a name="3668" href="Logic.html#3668" class="Bound"
      >B</a
      ><a name="3669"
      > </a
      ><a name="3670" class="Symbol"
      >:</a
      ><a name="3671"
      > </a
      ><a name="3672" class="PrimitiveType"
      >Set</a
      ><a name="3675" class="Symbol"
      >}</a
      ><a name="3676"
      > </a
      ><a name="3677" class="Symbol"
      >&#8594;</a
      ><a name="3678"
      > </a
      ><a name="3679" href="Logic.html#3666" class="Bound"
      >A</a
      ><a name="3680"
      > </a
      ><a name="3681" href="Logic.html#1478" class="Record Operator"
      >&#8771;</a
      ><a name="3682"
      > </a
      ><a name="3683" href="Logic.html#3668" class="Bound"
      >B</a
      ><a name="3684"
      > </a
      ><a name="3685" class="Symbol"
      >&#8594;</a
      ><a name="3686"
      > </a
      ><a name="3687" href="Logic.html#3668" class="Bound"
      >B</a
      ><a name="3688"
      > </a
      ><a name="3689" href="Logic.html#1478" class="Record Operator"
      >&#8771;</a
      ><a name="3690"
      > </a
      ><a name="3691" href="Logic.html#3666" class="Bound"
      >A</a
      ><a name="3692"
      >
</a
      ><a name="3693" href="Logic.html#3655" class="Function"
      >&#8771;-sym</a
      ><a name="3698"
      > </a
      ><a name="3699" href="Logic.html#3699" class="Bound"
      >A&#8771;B</a
      ><a name="3702"
      > </a
      ><a name="3703" class="Symbol"
      >=</a
      ><a name="3704"
      >
  </a
      ><a name="3707" class="Keyword"
      >record</a
      ><a name="3713"
      >
    </a
      ><a name="3718" class="Symbol"
      >{</a
      ><a name="3719"
      > </a
      ><a name="3720" class="Field"
      >to</a
      ><a name="3722"
      > </a
      ><a name="3723" class="Symbol"
      >=</a
      ><a name="3724"
      > </a
      ><a name="3725" href="Logic.html#1533" class="Field"
      >fro</a
      ><a name="3728"
      > </a
      ><a name="3729" href="Logic.html#3699" class="Bound"
      >A&#8771;B</a
      ><a name="3732"
      >
    </a
      ><a name="3737" class="Symbol"
      >;</a
      ><a name="3738"
      > </a
      ><a name="3739" class="Field"
      >fro</a
      ><a name="3742"
      > </a
      ><a name="3743" class="Symbol"
      >=</a
      ><a name="3744"
      > </a
      ><a name="3745" href="Logic.html#1518" class="Field"
      >to</a
      ><a name="3747"
      > </a
      ><a name="3748" href="Logic.html#3699" class="Bound"
      >A&#8771;B</a
      ><a name="3751"
      >
    </a
      ><a name="3756" class="Symbol"
      >;</a
      ><a name="3757"
      > </a
      ><a name="3758" class="Field"
      >inv&#737;</a
      ><a name="3762"
      > </a
      ><a name="3763" class="Symbol"
      >=</a
      ><a name="3764"
      > </a
      ><a name="3765" href="Logic.html#1587" class="Field"
      >inv&#691;</a
      ><a name="3769"
      > </a
      ><a name="3770" href="Logic.html#3699" class="Bound"
      >A&#8771;B</a
      ><a name="3773"
      >
    </a
      ><a name="3778" class="Symbol"
      >;</a
      ><a name="3779"
      > </a
      ><a name="3780" class="Field"
      >inv&#691;</a
      ><a name="3784"
      > </a
      ><a name="3785" class="Symbol"
      >=</a
      ><a name="3786"
      > </a
      ><a name="3787" href="Logic.html#1549" class="Field"
      >inv&#737;</a
      ><a name="3791"
      > </a
      ><a name="3792" href="Logic.html#3699" class="Bound"
      >A&#8771;B</a
      ><a name="3795"
      >
    </a
      ><a name="3800" class="Symbol"
      >}</a
      >
{% endraw %}</pre>
To show isomorphism is transitive, we compose the `to` and `fro` functions, and use
equational reasoning to combine the inverses.
<pre class="Agda">{% raw %}
<a name="3956" href="Logic.html#3956" class="Function"
      >&#8771;-trans</a
      ><a name="3963"
      > </a
      ><a name="3964" class="Symbol"
      >:</a
      ><a name="3965"
      > </a
      ><a name="3966" class="Symbol"
      >&#8704;</a
      ><a name="3967"
      > </a
      ><a name="3968" class="Symbol"
      >{</a
      ><a name="3969" href="Logic.html#3969" class="Bound"
      >A</a
      ><a name="3970"
      > </a
      ><a name="3971" href="Logic.html#3971" class="Bound"
      >B</a
      ><a name="3972"
      > </a
      ><a name="3973" href="Logic.html#3973" class="Bound"
      >C</a
      ><a name="3974"
      > </a
      ><a name="3975" class="Symbol"
      >:</a
      ><a name="3976"
      > </a
      ><a name="3977" class="PrimitiveType"
      >Set</a
      ><a name="3980" class="Symbol"
      >}</a
      ><a name="3981"
      > </a
      ><a name="3982" class="Symbol"
      >&#8594;</a
      ><a name="3983"
      > </a
      ><a name="3984" href="Logic.html#3969" class="Bound"
      >A</a
      ><a name="3985"
      > </a
      ><a name="3986" href="Logic.html#1478" class="Record Operator"
      >&#8771;</a
      ><a name="3987"
      > </a
      ><a name="3988" href="Logic.html#3971" class="Bound"
      >B</a
      ><a name="3989"
      > </a
      ><a name="3990" class="Symbol"
      >&#8594;</a
      ><a name="3991"
      > </a
      ><a name="3992" href="Logic.html#3971" class="Bound"
      >B</a
      ><a name="3993"
      > </a
      ><a name="3994" href="Logic.html#1478" class="Record Operator"
      >&#8771;</a
      ><a name="3995"
      > </a
      ><a name="3996" href="Logic.html#3973" class="Bound"
      >C</a
      ><a name="3997"
      > </a
      ><a name="3998" class="Symbol"
      >&#8594;</a
      ><a name="3999"
      > </a
      ><a name="4000" href="Logic.html#3969" class="Bound"
      >A</a
      ><a name="4001"
      > </a
      ><a name="4002" href="Logic.html#1478" class="Record Operator"
      >&#8771;</a
      ><a name="4003"
      > </a
      ><a name="4004" href="Logic.html#3973" class="Bound"
      >C</a
      ><a name="4005"
      >
</a
      ><a name="4006" href="Logic.html#3956" class="Function"
      >&#8771;-trans</a
      ><a name="4013"
      > </a
      ><a name="4014" href="Logic.html#4014" class="Bound"
      >A&#8771;B</a
      ><a name="4017"
      > </a
      ><a name="4018" href="Logic.html#4018" class="Bound"
      >B&#8771;C</a
      ><a name="4021"
      > </a
      ><a name="4022" class="Symbol"
      >=</a
      ><a name="4023"
      >
  </a
      ><a name="4026" class="Keyword"
      >record</a
      ><a name="4032"
      >
    </a
      ><a name="4037" class="Symbol"
      >{</a
      ><a name="4038"
      > </a
      ><a name="4039" class="Field"
      >to</a
      ><a name="4041"
      > </a
      ><a name="4042" class="Symbol"
      >=</a
      ><a name="4043"
      > </a
      ><a name="4044" class="Symbol"
      >&#955;</a
      ><a name="4045"
      > </a
      ><a name="4046" href="Logic.html#4046" class="Bound"
      >x</a
      ><a name="4047"
      > </a
      ><a name="4048" class="Symbol"
      >&#8594;</a
      ><a name="4049"
      > </a
      ><a name="4050" href="Logic.html#1518" class="Field"
      >to</a
      ><a name="4052"
      > </a
      ><a name="4053" href="Logic.html#4018" class="Bound"
      >B&#8771;C</a
      ><a name="4056"
      > </a
      ><a name="4057" class="Symbol"
      >(</a
      ><a name="4058" href="Logic.html#1518" class="Field"
      >to</a
      ><a name="4060"
      > </a
      ><a name="4061" href="Logic.html#4014" class="Bound"
      >A&#8771;B</a
      ><a name="4064"
      > </a
      ><a name="4065" href="Logic.html#4046" class="Bound"
      >x</a
      ><a name="4066" class="Symbol"
      >)</a
      ><a name="4067"
      >
    </a
      ><a name="4072" class="Symbol"
      >;</a
      ><a name="4073"
      > </a
      ><a name="4074" class="Field"
      >fro</a
      ><a name="4077"
      > </a
      ><a name="4078" class="Symbol"
      >=</a
      ><a name="4079"
      > </a
      ><a name="4080" class="Symbol"
      >&#955;</a
      ><a name="4081"
      > </a
      ><a name="4082" href="Logic.html#4082" class="Bound"
      >y</a
      ><a name="4083"
      > </a
      ><a name="4084" class="Symbol"
      >&#8594;</a
      ><a name="4085"
      > </a
      ><a name="4086" href="Logic.html#1533" class="Field"
      >fro</a
      ><a name="4089"
      > </a
      ><a name="4090" href="Logic.html#4014" class="Bound"
      >A&#8771;B</a
      ><a name="4093"
      > </a
      ><a name="4094" class="Symbol"
      >(</a
      ><a name="4095" href="Logic.html#1533" class="Field"
      >fro</a
      ><a name="4098"
      > </a
      ><a name="4099" href="Logic.html#4018" class="Bound"
      >B&#8771;C</a
      ><a name="4102"
      > </a
      ><a name="4103" href="Logic.html#4082" class="Bound"
      >y</a
      ><a name="4104" class="Symbol"
      >)</a
      ><a name="4105"
      >
    </a
      ><a name="4110" class="Symbol"
      >;</a
      ><a name="4111"
      > </a
      ><a name="4112" class="Field"
      >inv&#737;</a
      ><a name="4116"
      > </a
      ><a name="4117" class="Symbol"
      >=</a
      ><a name="4118"
      > </a
      ><a name="4119" class="Symbol"
      >&#955;</a
      ><a name="4120"
      > </a
      ><a name="4121" href="Logic.html#4121" class="Bound"
      >x</a
      ><a name="4122"
      > </a
      ><a name="4123" class="Symbol"
      >&#8594;</a
      ><a name="4124"
      >
        </a
      ><a name="4133" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#5807" class="Function Operator"
      >begin</a
      ><a name="4138"
      >
          </a
      ><a name="4149" href="Logic.html#1533" class="Field"
      >fro</a
      ><a name="4152"
      > </a
      ><a name="4153" href="Logic.html#4014" class="Bound"
      >A&#8771;B</a
      ><a name="4156"
      > </a
      ><a name="4157" class="Symbol"
      >(</a
      ><a name="4158" href="Logic.html#1533" class="Field"
      >fro</a
      ><a name="4161"
      > </a
      ><a name="4162" href="Logic.html#4018" class="Bound"
      >B&#8771;C</a
      ><a name="4165"
      > </a
      ><a name="4166" class="Symbol"
      >(</a
      ><a name="4167" href="Logic.html#1518" class="Field"
      >to</a
      ><a name="4169"
      > </a
      ><a name="4170" href="Logic.html#4018" class="Bound"
      >B&#8771;C</a
      ><a name="4173"
      > </a
      ><a name="4174" class="Symbol"
      >(</a
      ><a name="4175" href="Logic.html#1518" class="Field"
      >to</a
      ><a name="4177"
      > </a
      ><a name="4178" href="Logic.html#4014" class="Bound"
      >A&#8771;B</a
      ><a name="4181"
      > </a
      ><a name="4182" href="Logic.html#4121" class="Bound"
      >x</a
      ><a name="4183" class="Symbol"
      >)))</a
      ><a name="4186"
      >
        </a
      ><a name="4195" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#5924" class="Function Operator"
      >&#8801;&#10216;</a
      ><a name="4197"
      > </a
      ><a name="4198" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#1036" class="Function"
      >cong</a
      ><a name="4202"
      > </a
      ><a name="4203" class="Symbol"
      >(</a
      ><a name="4204" href="Logic.html#1533" class="Field"
      >fro</a
      ><a name="4207"
      > </a
      ><a name="4208" href="Logic.html#4014" class="Bound"
      >A&#8771;B</a
      ><a name="4211" class="Symbol"
      >)</a
      ><a name="4212"
      > </a
      ><a name="4213" class="Symbol"
      >(</a
      ><a name="4214" href="Logic.html#1549" class="Field"
      >inv&#737;</a
      ><a name="4218"
      > </a
      ><a name="4219" href="Logic.html#4018" class="Bound"
      >B&#8771;C</a
      ><a name="4222"
      > </a
      ><a name="4223" class="Symbol"
      >(</a
      ><a name="4224" href="Logic.html#1518" class="Field"
      >to</a
      ><a name="4226"
      > </a
      ><a name="4227" href="Logic.html#4014" class="Bound"
      >A&#8771;B</a
      ><a name="4230"
      > </a
      ><a name="4231" href="Logic.html#4121" class="Bound"
      >x</a
      ><a name="4232" class="Symbol"
      >))</a
      ><a name="4234"
      > </a
      ><a name="4235" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#5924" class="Function Operator"
      >&#10217;</a
      ><a name="4236"
      >
          </a
      ><a name="4247" href="Logic.html#1533" class="Field"
      >fro</a
      ><a name="4250"
      > </a
      ><a name="4251" href="Logic.html#4014" class="Bound"
      >A&#8771;B</a
      ><a name="4254"
      > </a
      ><a name="4255" class="Symbol"
      >(</a
      ><a name="4256" href="Logic.html#1518" class="Field"
      >to</a
      ><a name="4258"
      > </a
      ><a name="4259" href="Logic.html#4014" class="Bound"
      >A&#8771;B</a
      ><a name="4262"
      > </a
      ><a name="4263" href="Logic.html#4121" class="Bound"
      >x</a
      ><a name="4264" class="Symbol"
      >)</a
      ><a name="4265"
      >
        </a
      ><a name="4274" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#5924" class="Function Operator"
      >&#8801;&#10216;</a
      ><a name="4276"
      > </a
      ><a name="4277" href="Logic.html#1549" class="Field"
      >inv&#737;</a
      ><a name="4281"
      > </a
      ><a name="4282" href="Logic.html#4014" class="Bound"
      >A&#8771;B</a
      ><a name="4285"
      > </a
      ><a name="4286" href="Logic.html#4121" class="Bound"
      >x</a
      ><a name="4287"
      > </a
      ><a name="4288" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#5924" class="Function Operator"
      >&#10217;</a
      ><a name="4289"
      >
          </a
      ><a name="4300" href="Logic.html#4121" class="Bound"
      >x</a
      ><a name="4301"
      >
        </a
      ><a name="4310" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#6105" class="Function Operator"
      >&#8718;</a
      ><a name="4311"
      > 
    </a
      ><a name="4317" class="Symbol"
      >;</a
      ><a name="4318"
      > </a
      ><a name="4319" class="Field"
      >inv&#691;</a
      ><a name="4323"
      > </a
      ><a name="4324" class="Symbol"
      >=</a
      ><a name="4325"
      > </a
      ><a name="4326" class="Symbol"
      >&#955;</a
      ><a name="4327"
      > </a
      ><a name="4328" href="Logic.html#4328" class="Bound"
      >y</a
      ><a name="4329"
      > </a
      ><a name="4330" class="Symbol"
      >&#8594;</a
      ><a name="4331"
      >
        </a
      ><a name="4340" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#5807" class="Function Operator"
      >begin</a
      ><a name="4345"
      >
          </a
      ><a name="4356" href="Logic.html#1518" class="Field"
      >to</a
      ><a name="4358"
      > </a
      ><a name="4359" href="Logic.html#4018" class="Bound"
      >B&#8771;C</a
      ><a name="4362"
      > </a
      ><a name="4363" class="Symbol"
      >(</a
      ><a name="4364" href="Logic.html#1518" class="Field"
      >to</a
      ><a name="4366"
      > </a
      ><a name="4367" href="Logic.html#4014" class="Bound"
      >A&#8771;B</a
      ><a name="4370"
      > </a
      ><a name="4371" class="Symbol"
      >(</a
      ><a name="4372" href="Logic.html#1533" class="Field"
      >fro</a
      ><a name="4375"
      > </a
      ><a name="4376" href="Logic.html#4014" class="Bound"
      >A&#8771;B</a
      ><a name="4379"
      > </a
      ><a name="4380" class="Symbol"
      >(</a
      ><a name="4381" href="Logic.html#1533" class="Field"
      >fro</a
      ><a name="4384"
      > </a
      ><a name="4385" href="Logic.html#4018" class="Bound"
      >B&#8771;C</a
      ><a name="4388"
      > </a
      ><a name="4389" href="Logic.html#4328" class="Bound"
      >y</a
      ><a name="4390" class="Symbol"
      >)))</a
      ><a name="4393"
      >
        </a
      ><a name="4402" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#5924" class="Function Operator"
      >&#8801;&#10216;</a
      ><a name="4404"
      > </a
      ><a name="4405" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#1036" class="Function"
      >cong</a
      ><a name="4409"
      > </a
      ><a name="4410" class="Symbol"
      >(</a
      ><a name="4411" href="Logic.html#1518" class="Field"
      >to</a
      ><a name="4413"
      > </a
      ><a name="4414" href="Logic.html#4018" class="Bound"
      >B&#8771;C</a
      ><a name="4417" class="Symbol"
      >)</a
      ><a name="4418"
      > </a
      ><a name="4419" class="Symbol"
      >(</a
      ><a name="4420" href="Logic.html#1587" class="Field"
      >inv&#691;</a
      ><a name="4424"
      > </a
      ><a name="4425" href="Logic.html#4014" class="Bound"
      >A&#8771;B</a
      ><a name="4428"
      > </a
      ><a name="4429" class="Symbol"
      >(</a
      ><a name="4430" href="Logic.html#1533" class="Field"
      >fro</a
      ><a name="4433"
      > </a
      ><a name="4434" href="Logic.html#4018" class="Bound"
      >B&#8771;C</a
      ><a name="4437"
      > </a
      ><a name="4438" href="Logic.html#4328" class="Bound"
      >y</a
      ><a name="4439" class="Symbol"
      >))</a
      ><a name="4441"
      > </a
      ><a name="4442" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#5924" class="Function Operator"
      >&#10217;</a
      ><a name="4443"
      >
          </a
      ><a name="4454" href="Logic.html#1518" class="Field"
      >to</a
      ><a name="4456"
      > </a
      ><a name="4457" href="Logic.html#4018" class="Bound"
      >B&#8771;C</a
      ><a name="4460"
      > </a
      ><a name="4461" class="Symbol"
      >(</a
      ><a name="4462" href="Logic.html#1533" class="Field"
      >fro</a
      ><a name="4465"
      > </a
      ><a name="4466" href="Logic.html#4018" class="Bound"
      >B&#8771;C</a
      ><a name="4469"
      > </a
      ><a name="4470" href="Logic.html#4328" class="Bound"
      >y</a
      ><a name="4471" class="Symbol"
      >)</a
      ><a name="4472"
      >
        </a
      ><a name="4481" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#5924" class="Function Operator"
      >&#8801;&#10216;</a
      ><a name="4483"
      > </a
      ><a name="4484" href="Logic.html#1587" class="Field"
      >inv&#691;</a
      ><a name="4488"
      > </a
      ><a name="4489" href="Logic.html#4018" class="Bound"
      >B&#8771;C</a
      ><a name="4492"
      > </a
      ><a name="4493" href="Logic.html#4328" class="Bound"
      >y</a
      ><a name="4494"
      > </a
      ><a name="4495" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#5924" class="Function Operator"
      >&#10217;</a
      ><a name="4496"
      >
          </a
      ><a name="4507" href="Logic.html#4328" class="Bound"
      >y</a
      ><a name="4508"
      >
        </a
      ><a name="4517" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#6105" class="Function Operator"
      >&#8718;</a
      ><a name="4518"
      >
     </a
      ><a name="4524" class="Symbol"
      >}</a
      >
{% endraw %}</pre>

We will make good use of isomorphisms in what follows to demonstrate
that operations on types such as product and sum satisfy properties
akin to associativity, commutativity, and distributivity.

## Embedding

We will also need the notion of *embedding*, which is a weakening
of isomorphism.  While an isomorphism shows that two types are
in one-to-one correspondence, and embedding shows that the first
type is, in a sense, included in the second; or, equivalently,
that there is a many-to-one correspondence between the second
type and the first.

Here is the formal definition of embedding.
<pre class="Agda">{% raw %}
<a name="5145" class="Keyword"
      >record</a
      ><a name="5151"
      > </a
      ><a name="5152" href="Logic.html#5152" class="Record Operator"
      >_&#8818;_</a
      ><a name="5155"
      > </a
      ><a name="5156" class="Symbol"
      >(</a
      ><a name="5157" href="Logic.html#5157" class="Bound"
      >A</a
      ><a name="5158"
      > </a
      ><a name="5159" href="Logic.html#5159" class="Bound"
      >B</a
      ><a name="5160"
      > </a
      ><a name="5161" class="Symbol"
      >:</a
      ><a name="5162"
      > </a
      ><a name="5163" class="PrimitiveType"
      >Set</a
      ><a name="5166" class="Symbol"
      >)</a
      ><a name="5167"
      > </a
      ><a name="5168" class="Symbol"
      >:</a
      ><a name="5169"
      > </a
      ><a name="5170" class="PrimitiveType"
      >Set</a
      ><a name="5173"
      > </a
      ><a name="5174" class="Keyword"
      >where</a
      ><a name="5179"
      >
  </a
      ><a name="5182" class="Keyword"
      >field</a
      ><a name="5187"
      >
    </a
      ><a name="5192" href="Logic.html#5192" class="Field"
      >to</a
      ><a name="5194"
      > </a
      ><a name="5195" class="Symbol"
      >:</a
      ><a name="5196"
      > </a
      ><a name="5197" href="Logic.html#5157" class="Bound"
      >A</a
      ><a name="5198"
      > </a
      ><a name="5199" class="Symbol"
      >&#8594;</a
      ><a name="5200"
      > </a
      ><a name="5201" href="Logic.html#5159" class="Bound"
      >B</a
      ><a name="5202"
      >
    </a
      ><a name="5207" href="Logic.html#5207" class="Field"
      >fro</a
      ><a name="5210"
      > </a
      ><a name="5211" class="Symbol"
      >:</a
      ><a name="5212"
      > </a
      ><a name="5213" href="Logic.html#5159" class="Bound"
      >B</a
      ><a name="5214"
      > </a
      ><a name="5215" class="Symbol"
      >&#8594;</a
      ><a name="5216"
      > </a
      ><a name="5217" href="Logic.html#5157" class="Bound"
      >A</a
      ><a name="5218"
      >
    </a
      ><a name="5223" href="Logic.html#5223" class="Field"
      >inv&#737;</a
      ><a name="5227"
      > </a
      ><a name="5228" class="Symbol"
      >:</a
      ><a name="5229"
      > </a
      ><a name="5230" class="Symbol"
      >&#8704;</a
      ><a name="5231"
      > </a
      ><a name="5232" class="Symbol"
      >(</a
      ><a name="5233" href="Logic.html#5233" class="Bound"
      >x</a
      ><a name="5234"
      > </a
      ><a name="5235" class="Symbol"
      >:</a
      ><a name="5236"
      > </a
      ><a name="5237" href="Logic.html#5157" class="Bound"
      >A</a
      ><a name="5238" class="Symbol"
      >)</a
      ><a name="5239"
      > </a
      ><a name="5240" class="Symbol"
      >&#8594;</a
      ><a name="5241"
      > </a
      ><a name="5242" class="Field"
      >fro</a
      ><a name="5245"
      > </a
      ><a name="5246" class="Symbol"
      >(</a
      ><a name="5247" class="Field"
      >to</a
      ><a name="5249"
      > </a
      ><a name="5250" href="Logic.html#5233" class="Bound"
      >x</a
      ><a name="5251" class="Symbol"
      >)</a
      ><a name="5252"
      > </a
      ><a name="5253" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="5254"
      > </a
      ><a name="5255" href="Logic.html#5233" class="Bound"
      >x</a
      ><a name="5256"
      >
</a
      ><a name="5257" class="Keyword"
      >open</a
      ><a name="5261"
      > </a
      ><a name="5262" href="Logic.html#5152" class="Module Operator"
      >_&#8818;_</a
      >
{% endraw %}</pre>
It is the same as an isomorphism, save that it lacks the `invʳ` field.
Hence, we know that `fro` is left inverse to `to`, but not that it is
a right inverse.

Embedding is reflexive and transitive.  The proofs are cut down
versions of the similar proofs for isomorphism, simply dropping the
right inverses.
<pre class="Agda">{% raw %}
<a name="5597" href="Logic.html#5597" class="Function"
      >&#8818;-refl</a
      ><a name="5603"
      > </a
      ><a name="5604" class="Symbol"
      >:</a
      ><a name="5605"
      > </a
      ><a name="5606" class="Symbol"
      >&#8704;</a
      ><a name="5607"
      > </a
      ><a name="5608" class="Symbol"
      >{</a
      ><a name="5609" href="Logic.html#5609" class="Bound"
      >A</a
      ><a name="5610"
      > </a
      ><a name="5611" class="Symbol"
      >:</a
      ><a name="5612"
      > </a
      ><a name="5613" class="PrimitiveType"
      >Set</a
      ><a name="5616" class="Symbol"
      >}</a
      ><a name="5617"
      > </a
      ><a name="5618" class="Symbol"
      >&#8594;</a
      ><a name="5619"
      > </a
      ><a name="5620" href="Logic.html#5609" class="Bound"
      >A</a
      ><a name="5621"
      > </a
      ><a name="5622" href="Logic.html#5152" class="Record Operator"
      >&#8818;</a
      ><a name="5623"
      > </a
      ><a name="5624" href="Logic.html#5609" class="Bound"
      >A</a
      ><a name="5625"
      >
</a
      ><a name="5626" href="Logic.html#5597" class="Function"
      >&#8818;-refl</a
      ><a name="5632"
      > </a
      ><a name="5633" class="Symbol"
      >=</a
      ><a name="5634"
      >
  </a
      ><a name="5637" class="Keyword"
      >record</a
      ><a name="5643"
      >
    </a
      ><a name="5648" class="Symbol"
      >{</a
      ><a name="5649"
      > </a
      ><a name="5650" class="Field"
      >to</a
      ><a name="5652"
      > </a
      ><a name="5653" class="Symbol"
      >=</a
      ><a name="5654"
      > </a
      ><a name="5655" class="Symbol"
      >&#955;</a
      ><a name="5656"
      > </a
      ><a name="5657" href="Logic.html#5657" class="Bound"
      >x</a
      ><a name="5658"
      > </a
      ><a name="5659" class="Symbol"
      >&#8594;</a
      ><a name="5660"
      > </a
      ><a name="5661" href="Logic.html#5657" class="Bound"
      >x</a
      ><a name="5662"
      >
    </a
      ><a name="5667" class="Symbol"
      >;</a
      ><a name="5668"
      > </a
      ><a name="5669" class="Field"
      >fro</a
      ><a name="5672"
      > </a
      ><a name="5673" class="Symbol"
      >=</a
      ><a name="5674"
      > </a
      ><a name="5675" class="Symbol"
      >&#955;</a
      ><a name="5676"
      > </a
      ><a name="5677" href="Logic.html#5677" class="Bound"
      >y</a
      ><a name="5678"
      > </a
      ><a name="5679" class="Symbol"
      >&#8594;</a
      ><a name="5680"
      > </a
      ><a name="5681" href="Logic.html#5677" class="Bound"
      >y</a
      ><a name="5682"
      >
    </a
      ><a name="5687" class="Symbol"
      >;</a
      ><a name="5688"
      > </a
      ><a name="5689" class="Field"
      >inv&#737;</a
      ><a name="5693"
      > </a
      ><a name="5694" class="Symbol"
      >=</a
      ><a name="5695"
      > </a
      ><a name="5696" class="Symbol"
      >&#955;</a
      ><a name="5697"
      > </a
      ><a name="5698" href="Logic.html#5698" class="Bound"
      >x</a
      ><a name="5699"
      > </a
      ><a name="5700" class="Symbol"
      >&#8594;</a
      ><a name="5701"
      > </a
      ><a name="5702" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="5706"
      >
    </a
      ><a name="5711" class="Symbol"
      >}</a
      ><a name="5712"
      > 

</a
      ><a name="5715" href="Logic.html#5715" class="Function"
      >&#8818;-tran</a
      ><a name="5721"
      > </a
      ><a name="5722" class="Symbol"
      >:</a
      ><a name="5723"
      > </a
      ><a name="5724" class="Symbol"
      >&#8704;</a
      ><a name="5725"
      > </a
      ><a name="5726" class="Symbol"
      >{</a
      ><a name="5727" href="Logic.html#5727" class="Bound"
      >A</a
      ><a name="5728"
      > </a
      ><a name="5729" href="Logic.html#5729" class="Bound"
      >B</a
      ><a name="5730"
      > </a
      ><a name="5731" href="Logic.html#5731" class="Bound"
      >C</a
      ><a name="5732"
      > </a
      ><a name="5733" class="Symbol"
      >:</a
      ><a name="5734"
      > </a
      ><a name="5735" class="PrimitiveType"
      >Set</a
      ><a name="5738" class="Symbol"
      >}</a
      ><a name="5739"
      > </a
      ><a name="5740" class="Symbol"
      >&#8594;</a
      ><a name="5741"
      > </a
      ><a name="5742" href="Logic.html#5727" class="Bound"
      >A</a
      ><a name="5743"
      > </a
      ><a name="5744" href="Logic.html#5152" class="Record Operator"
      >&#8818;</a
      ><a name="5745"
      > </a
      ><a name="5746" href="Logic.html#5729" class="Bound"
      >B</a
      ><a name="5747"
      > </a
      ><a name="5748" class="Symbol"
      >&#8594;</a
      ><a name="5749"
      > </a
      ><a name="5750" href="Logic.html#5729" class="Bound"
      >B</a
      ><a name="5751"
      > </a
      ><a name="5752" href="Logic.html#5152" class="Record Operator"
      >&#8818;</a
      ><a name="5753"
      > </a
      ><a name="5754" href="Logic.html#5731" class="Bound"
      >C</a
      ><a name="5755"
      > </a
      ><a name="5756" class="Symbol"
      >&#8594;</a
      ><a name="5757"
      > </a
      ><a name="5758" href="Logic.html#5727" class="Bound"
      >A</a
      ><a name="5759"
      > </a
      ><a name="5760" href="Logic.html#5152" class="Record Operator"
      >&#8818;</a
      ><a name="5761"
      > </a
      ><a name="5762" href="Logic.html#5731" class="Bound"
      >C</a
      ><a name="5763"
      >
</a
      ><a name="5764" href="Logic.html#5715" class="Function"
      >&#8818;-tran</a
      ><a name="5770"
      > </a
      ><a name="5771" href="Logic.html#5771" class="Bound"
      >A&#8818;B</a
      ><a name="5774"
      > </a
      ><a name="5775" href="Logic.html#5775" class="Bound"
      >B&#8818;C</a
      ><a name="5778"
      > </a
      ><a name="5779" class="Symbol"
      >=</a
      ><a name="5780"
      >
  </a
      ><a name="5783" class="Keyword"
      >record</a
      ><a name="5789"
      >
    </a
      ><a name="5794" class="Symbol"
      >{</a
      ><a name="5795"
      > </a
      ><a name="5796" class="Field"
      >to</a
      ><a name="5798"
      > </a
      ><a name="5799" class="Symbol"
      >=</a
      ><a name="5800"
      > </a
      ><a name="5801" class="Symbol"
      >&#955;</a
      ><a name="5802"
      > </a
      ><a name="5803" href="Logic.html#5803" class="Bound"
      >x</a
      ><a name="5804"
      > </a
      ><a name="5805" class="Symbol"
      >&#8594;</a
      ><a name="5806"
      > </a
      ><a name="5807" href="Logic.html#5192" class="Field"
      >to</a
      ><a name="5809"
      > </a
      ><a name="5810" href="Logic.html#5775" class="Bound"
      >B&#8818;C</a
      ><a name="5813"
      > </a
      ><a name="5814" class="Symbol"
      >(</a
      ><a name="5815" href="Logic.html#5192" class="Field"
      >to</a
      ><a name="5817"
      > </a
      ><a name="5818" href="Logic.html#5771" class="Bound"
      >A&#8818;B</a
      ><a name="5821"
      > </a
      ><a name="5822" href="Logic.html#5803" class="Bound"
      >x</a
      ><a name="5823" class="Symbol"
      >)</a
      ><a name="5824"
      >
    </a
      ><a name="5829" class="Symbol"
      >;</a
      ><a name="5830"
      > </a
      ><a name="5831" class="Field"
      >fro</a
      ><a name="5834"
      > </a
      ><a name="5835" class="Symbol"
      >=</a
      ><a name="5836"
      > </a
      ><a name="5837" class="Symbol"
      >&#955;</a
      ><a name="5838"
      > </a
      ><a name="5839" href="Logic.html#5839" class="Bound"
      >y</a
      ><a name="5840"
      > </a
      ><a name="5841" class="Symbol"
      >&#8594;</a
      ><a name="5842"
      > </a
      ><a name="5843" href="Logic.html#5207" class="Field"
      >fro</a
      ><a name="5846"
      > </a
      ><a name="5847" href="Logic.html#5771" class="Bound"
      >A&#8818;B</a
      ><a name="5850"
      > </a
      ><a name="5851" class="Symbol"
      >(</a
      ><a name="5852" href="Logic.html#5207" class="Field"
      >fro</a
      ><a name="5855"
      > </a
      ><a name="5856" href="Logic.html#5775" class="Bound"
      >B&#8818;C</a
      ><a name="5859"
      > </a
      ><a name="5860" href="Logic.html#5839" class="Bound"
      >y</a
      ><a name="5861" class="Symbol"
      >)</a
      ><a name="5862"
      >
    </a
      ><a name="5867" class="Symbol"
      >;</a
      ><a name="5868"
      > </a
      ><a name="5869" class="Field"
      >inv&#737;</a
      ><a name="5873"
      > </a
      ><a name="5874" class="Symbol"
      >=</a
      ><a name="5875"
      > </a
      ><a name="5876" class="Symbol"
      >&#955;</a
      ><a name="5877"
      > </a
      ><a name="5878" href="Logic.html#5878" class="Bound"
      >x</a
      ><a name="5879"
      > </a
      ><a name="5880" class="Symbol"
      >&#8594;</a
      ><a name="5881"
      >
        </a
      ><a name="5890" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#5807" class="Function Operator"
      >begin</a
      ><a name="5895"
      >
          </a
      ><a name="5906" href="Logic.html#5207" class="Field"
      >fro</a
      ><a name="5909"
      > </a
      ><a name="5910" href="Logic.html#5771" class="Bound"
      >A&#8818;B</a
      ><a name="5913"
      > </a
      ><a name="5914" class="Symbol"
      >(</a
      ><a name="5915" href="Logic.html#5207" class="Field"
      >fro</a
      ><a name="5918"
      > </a
      ><a name="5919" href="Logic.html#5775" class="Bound"
      >B&#8818;C</a
      ><a name="5922"
      > </a
      ><a name="5923" class="Symbol"
      >(</a
      ><a name="5924" href="Logic.html#5192" class="Field"
      >to</a
      ><a name="5926"
      > </a
      ><a name="5927" href="Logic.html#5775" class="Bound"
      >B&#8818;C</a
      ><a name="5930"
      > </a
      ><a name="5931" class="Symbol"
      >(</a
      ><a name="5932" href="Logic.html#5192" class="Field"
      >to</a
      ><a name="5934"
      > </a
      ><a name="5935" href="Logic.html#5771" class="Bound"
      >A&#8818;B</a
      ><a name="5938"
      > </a
      ><a name="5939" href="Logic.html#5878" class="Bound"
      >x</a
      ><a name="5940" class="Symbol"
      >)))</a
      ><a name="5943"
      >
        </a
      ><a name="5952" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#5924" class="Function Operator"
      >&#8801;&#10216;</a
      ><a name="5954"
      > </a
      ><a name="5955" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#1036" class="Function"
      >cong</a
      ><a name="5959"
      > </a
      ><a name="5960" class="Symbol"
      >(</a
      ><a name="5961" href="Logic.html#5207" class="Field"
      >fro</a
      ><a name="5964"
      > </a
      ><a name="5965" href="Logic.html#5771" class="Bound"
      >A&#8818;B</a
      ><a name="5968" class="Symbol"
      >)</a
      ><a name="5969"
      > </a
      ><a name="5970" class="Symbol"
      >(</a
      ><a name="5971" href="Logic.html#5223" class="Field"
      >inv&#737;</a
      ><a name="5975"
      > </a
      ><a name="5976" href="Logic.html#5775" class="Bound"
      >B&#8818;C</a
      ><a name="5979"
      > </a
      ><a name="5980" class="Symbol"
      >(</a
      ><a name="5981" href="Logic.html#5192" class="Field"
      >to</a
      ><a name="5983"
      > </a
      ><a name="5984" href="Logic.html#5771" class="Bound"
      >A&#8818;B</a
      ><a name="5987"
      > </a
      ><a name="5988" href="Logic.html#5878" class="Bound"
      >x</a
      ><a name="5989" class="Symbol"
      >))</a
      ><a name="5991"
      > </a
      ><a name="5992" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#5924" class="Function Operator"
      >&#10217;</a
      ><a name="5993"
      >
          </a
      ><a name="6004" href="Logic.html#5207" class="Field"
      >fro</a
      ><a name="6007"
      > </a
      ><a name="6008" href="Logic.html#5771" class="Bound"
      >A&#8818;B</a
      ><a name="6011"
      > </a
      ><a name="6012" class="Symbol"
      >(</a
      ><a name="6013" href="Logic.html#5192" class="Field"
      >to</a
      ><a name="6015"
      > </a
      ><a name="6016" href="Logic.html#5771" class="Bound"
      >A&#8818;B</a
      ><a name="6019"
      > </a
      ><a name="6020" href="Logic.html#5878" class="Bound"
      >x</a
      ><a name="6021" class="Symbol"
      >)</a
      ><a name="6022"
      >
        </a
      ><a name="6031" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#5924" class="Function Operator"
      >&#8801;&#10216;</a
      ><a name="6033"
      > </a
      ><a name="6034" href="Logic.html#5223" class="Field"
      >inv&#737;</a
      ><a name="6038"
      > </a
      ><a name="6039" href="Logic.html#5771" class="Bound"
      >A&#8818;B</a
      ><a name="6042"
      > </a
      ><a name="6043" href="Logic.html#5878" class="Bound"
      >x</a
      ><a name="6044"
      > </a
      ><a name="6045" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#5924" class="Function Operator"
      >&#10217;</a
      ><a name="6046"
      >
          </a
      ><a name="6057" href="Logic.html#5878" class="Bound"
      >x</a
      ><a name="6058"
      >
        </a
      ><a name="6067" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#6105" class="Function Operator"
      >&#8718;</a
      ><a name="6068"
      > 
     </a
      ><a name="6075" class="Symbol"
      >}</a
      >
{% endraw %}</pre>
It is also easy to see that if two types embed in each other,
and the embedding functions correspond, then they are isomorphic.
This is a weak form of anti-symmetry.
<pre class="Agda">{% raw %}
<a name="6267" href="Logic.html#6267" class="Function"
      >&#8818;-antisym</a
      ><a name="6276"
      > </a
      ><a name="6277" class="Symbol"
      >:</a
      ><a name="6278"
      > </a
      ><a name="6279" class="Symbol"
      >&#8704;</a
      ><a name="6280"
      > </a
      ><a name="6281" class="Symbol"
      >{</a
      ><a name="6282" href="Logic.html#6282" class="Bound"
      >A</a
      ><a name="6283"
      > </a
      ><a name="6284" href="Logic.html#6284" class="Bound"
      >B</a
      ><a name="6285"
      > </a
      ><a name="6286" class="Symbol"
      >:</a
      ><a name="6287"
      > </a
      ><a name="6288" class="PrimitiveType"
      >Set</a
      ><a name="6291" class="Symbol"
      >}</a
      ><a name="6292"
      > </a
      ><a name="6293" class="Symbol"
      >&#8594;</a
      ><a name="6294"
      > </a
      ><a name="6295" class="Symbol"
      >(</a
      ><a name="6296" href="Logic.html#6296" class="Bound"
      >A&#8818;B</a
      ><a name="6299"
      > </a
      ><a name="6300" class="Symbol"
      >:</a
      ><a name="6301"
      > </a
      ><a name="6302" href="Logic.html#6282" class="Bound"
      >A</a
      ><a name="6303"
      > </a
      ><a name="6304" href="Logic.html#5152" class="Record Operator"
      >&#8818;</a
      ><a name="6305"
      > </a
      ><a name="6306" href="Logic.html#6284" class="Bound"
      >B</a
      ><a name="6307" class="Symbol"
      >)</a
      ><a name="6308"
      > </a
      ><a name="6309" class="Symbol"
      >&#8594;</a
      ><a name="6310"
      > </a
      ><a name="6311" class="Symbol"
      >(</a
      ><a name="6312" href="Logic.html#6312" class="Bound"
      >B&#8818;A</a
      ><a name="6315"
      > </a
      ><a name="6316" class="Symbol"
      >:</a
      ><a name="6317"
      > </a
      ><a name="6318" href="Logic.html#6284" class="Bound"
      >B</a
      ><a name="6319"
      > </a
      ><a name="6320" href="Logic.html#5152" class="Record Operator"
      >&#8818;</a
      ><a name="6321"
      > </a
      ><a name="6322" href="Logic.html#6282" class="Bound"
      >A</a
      ><a name="6323" class="Symbol"
      >)</a
      ><a name="6324"
      > </a
      ><a name="6325" class="Symbol"
      >&#8594;</a
      ><a name="6326"
      >
  </a
      ><a name="6329" class="Symbol"
      >(</a
      ><a name="6330" href="Logic.html#5192" class="Field"
      >to</a
      ><a name="6332"
      > </a
      ><a name="6333" href="Logic.html#6296" class="Bound"
      >A&#8818;B</a
      ><a name="6336"
      > </a
      ><a name="6337" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="6338"
      > </a
      ><a name="6339" href="Logic.html#5207" class="Field"
      >fro</a
      ><a name="6342"
      > </a
      ><a name="6343" href="Logic.html#6312" class="Bound"
      >B&#8818;A</a
      ><a name="6346" class="Symbol"
      >)</a
      ><a name="6347"
      > </a
      ><a name="6348" class="Symbol"
      >&#8594;</a
      ><a name="6349"
      > </a
      ><a name="6350" class="Symbol"
      >(</a
      ><a name="6351" href="Logic.html#5207" class="Field"
      >fro</a
      ><a name="6354"
      > </a
      ><a name="6355" href="Logic.html#6296" class="Bound"
      >A&#8818;B</a
      ><a name="6358"
      > </a
      ><a name="6359" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="6360"
      > </a
      ><a name="6361" href="Logic.html#5192" class="Field"
      >to</a
      ><a name="6363"
      > </a
      ><a name="6364" href="Logic.html#6312" class="Bound"
      >B&#8818;A</a
      ><a name="6367" class="Symbol"
      >)</a
      ><a name="6368"
      > </a
      ><a name="6369" class="Symbol"
      >&#8594;</a
      ><a name="6370"
      > </a
      ><a name="6371" href="Logic.html#6282" class="Bound"
      >A</a
      ><a name="6372"
      > </a
      ><a name="6373" href="Logic.html#1478" class="Record Operator"
      >&#8771;</a
      ><a name="6374"
      > </a
      ><a name="6375" href="Logic.html#6284" class="Bound"
      >B</a
      ><a name="6376"
      >
</a
      ><a name="6377" href="Logic.html#6267" class="Function"
      >&#8818;-antisym</a
      ><a name="6386"
      > </a
      ><a name="6387" href="Logic.html#6387" class="Bound"
      >A&#8818;B</a
      ><a name="6390"
      > </a
      ><a name="6391" href="Logic.html#6391" class="Bound"
      >B&#8818;A</a
      ><a name="6394"
      > </a
      ><a name="6395" href="Logic.html#6395" class="Bound"
      >to&#8801;fro</a
      ><a name="6401"
      > </a
      ><a name="6402" href="Logic.html#6402" class="Bound"
      >fro&#8801;to</a
      ><a name="6408"
      > </a
      ><a name="6409" class="Symbol"
      >=</a
      ><a name="6410"
      >
  </a
      ><a name="6413" class="Keyword"
      >record</a
      ><a name="6419"
      >
    </a
      ><a name="6424" class="Symbol"
      >{</a
      ><a name="6425"
      > </a
      ><a name="6426" class="Field"
      >to</a
      ><a name="6428"
      >   </a
      ><a name="6431" class="Symbol"
      >=</a
      ><a name="6432"
      > </a
      ><a name="6433" href="Logic.html#5192" class="Field"
      >to</a
      ><a name="6435"
      > </a
      ><a name="6436" href="Logic.html#6387" class="Bound"
      >A&#8818;B</a
      ><a name="6439"
      >
    </a
      ><a name="6444" class="Symbol"
      >;</a
      ><a name="6445"
      > </a
      ><a name="6446" class="Field"
      >fro</a
      ><a name="6449"
      >  </a
      ><a name="6451" class="Symbol"
      >=</a
      ><a name="6452"
      > </a
      ><a name="6453" href="Logic.html#5207" class="Field"
      >fro</a
      ><a name="6456"
      > </a
      ><a name="6457" href="Logic.html#6387" class="Bound"
      >A&#8818;B</a
      ><a name="6460"
      >
    </a
      ><a name="6465" class="Symbol"
      >;</a
      ><a name="6466"
      > </a
      ><a name="6467" class="Field"
      >inv&#737;</a
      ><a name="6471"
      > </a
      ><a name="6472" class="Symbol"
      >=</a
      ><a name="6473"
      > </a
      ><a name="6474" href="Logic.html#5223" class="Field"
      >inv&#737;</a
      ><a name="6478"
      > </a
      ><a name="6479" href="Logic.html#6387" class="Bound"
      >A&#8818;B</a
      ><a name="6482"
      >
    </a
      ><a name="6487" class="Symbol"
      >;</a
      ><a name="6488"
      > </a
      ><a name="6489" class="Field"
      >inv&#691;</a
      ><a name="6493"
      > </a
      ><a name="6494" class="Symbol"
      >=</a
      ><a name="6495"
      > </a
      ><a name="6496" class="Symbol"
      >&#955;</a
      ><a name="6497"
      > </a
      ><a name="6498" href="Logic.html#6498" class="Bound"
      >y</a
      ><a name="6499"
      > </a
      ><a name="6500" class="Symbol"
      >&#8594;</a
      ><a name="6501"
      >
        </a
      ><a name="6510" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#5807" class="Function Operator"
      >begin</a
      ><a name="6515"
      >
          </a
      ><a name="6526" href="Logic.html#5192" class="Field"
      >to</a
      ><a name="6528"
      > </a
      ><a name="6529" href="Logic.html#6387" class="Bound"
      >A&#8818;B</a
      ><a name="6532"
      > </a
      ><a name="6533" class="Symbol"
      >(</a
      ><a name="6534" href="Logic.html#5207" class="Field"
      >fro</a
      ><a name="6537"
      > </a
      ><a name="6538" href="Logic.html#6387" class="Bound"
      >A&#8818;B</a
      ><a name="6541"
      > </a
      ><a name="6542" href="Logic.html#6498" class="Bound"
      >y</a
      ><a name="6543" class="Symbol"
      >)</a
      ><a name="6544"
      >
        </a
      ><a name="6553" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#5924" class="Function Operator"
      >&#8801;&#10216;</a
      ><a name="6555"
      > </a
      ><a name="6556" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#1036" class="Function"
      >cong</a
      ><a name="6560"
      > </a
      ><a name="6561" class="Symbol"
      >(\</a
      ><a name="6563" href="Logic.html#6563" class="Bound"
      >w</a
      ><a name="6564"
      > </a
      ><a name="6565" class="Symbol"
      >&#8594;</a
      ><a name="6566"
      > </a
      ><a name="6567" href="Logic.html#5192" class="Field"
      >to</a
      ><a name="6569"
      > </a
      ><a name="6570" href="Logic.html#6387" class="Bound"
      >A&#8818;B</a
      ><a name="6573"
      > </a
      ><a name="6574" class="Symbol"
      >(</a
      ><a name="6575" href="Logic.html#6563" class="Bound"
      >w</a
      ><a name="6576"
      > </a
      ><a name="6577" href="Logic.html#6498" class="Bound"
      >y</a
      ><a name="6578" class="Symbol"
      >))</a
      ><a name="6580"
      > </a
      ><a name="6581" href="Logic.html#6402" class="Bound"
      >fro&#8801;to</a
      ><a name="6587"
      > </a
      ><a name="6588" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#5924" class="Function Operator"
      >&#10217;</a
      ><a name="6589"
      >
          </a
      ><a name="6600" href="Logic.html#5192" class="Field"
      >to</a
      ><a name="6602"
      > </a
      ><a name="6603" href="Logic.html#6387" class="Bound"
      >A&#8818;B</a
      ><a name="6606"
      > </a
      ><a name="6607" class="Symbol"
      >(</a
      ><a name="6608" href="Logic.html#5192" class="Field"
      >to</a
      ><a name="6610"
      > </a
      ><a name="6611" href="Logic.html#6391" class="Bound"
      >B&#8818;A</a
      ><a name="6614"
      > </a
      ><a name="6615" href="Logic.html#6498" class="Bound"
      >y</a
      ><a name="6616" class="Symbol"
      >)</a
      ><a name="6617"
      >
        </a
      ><a name="6626" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#5924" class="Function Operator"
      >&#8801;&#10216;</a
      ><a name="6628"
      > </a
      ><a name="6629" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#1036" class="Function"
      >cong</a
      ><a name="6633"
      > </a
      ><a name="6634" class="Symbol"
      >(\</a
      ><a name="6636" href="Logic.html#6636" class="Bound"
      >w</a
      ><a name="6637"
      > </a
      ><a name="6638" class="Symbol"
      >&#8594;</a
      ><a name="6639"
      > </a
      ><a name="6640" href="Logic.html#6636" class="Bound"
      >w</a
      ><a name="6641"
      > </a
      ><a name="6642" class="Symbol"
      >(</a
      ><a name="6643" href="Logic.html#5192" class="Field"
      >to</a
      ><a name="6645"
      > </a
      ><a name="6646" href="Logic.html#6391" class="Bound"
      >B&#8818;A</a
      ><a name="6649"
      > </a
      ><a name="6650" href="Logic.html#6498" class="Bound"
      >y</a
      ><a name="6651" class="Symbol"
      >))</a
      ><a name="6653"
      > </a
      ><a name="6654" href="Logic.html#6395" class="Bound"
      >to&#8801;fro</a
      ><a name="6660"
      > </a
      ><a name="6661" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#5924" class="Function Operator"
      >&#10217;</a
      ><a name="6662"
      >
          </a
      ><a name="6673" href="Logic.html#5207" class="Field"
      >fro</a
      ><a name="6676"
      > </a
      ><a name="6677" href="Logic.html#6391" class="Bound"
      >B&#8818;A</a
      ><a name="6680"
      > </a
      ><a name="6681" class="Symbol"
      >(</a
      ><a name="6682" href="Logic.html#5192" class="Field"
      >to</a
      ><a name="6684"
      > </a
      ><a name="6685" href="Logic.html#6391" class="Bound"
      >B&#8818;A</a
      ><a name="6688"
      > </a
      ><a name="6689" href="Logic.html#6498" class="Bound"
      >y</a
      ><a name="6690" class="Symbol"
      >)</a
      ><a name="6691"
      >
        </a
      ><a name="6700" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#5924" class="Function Operator"
      >&#8801;&#10216;</a
      ><a name="6702"
      > </a
      ><a name="6703" href="Logic.html#5223" class="Field"
      >inv&#737;</a
      ><a name="6707"
      > </a
      ><a name="6708" href="Logic.html#6391" class="Bound"
      >B&#8818;A</a
      ><a name="6711"
      > </a
      ><a name="6712" href="Logic.html#6498" class="Bound"
      >y</a
      ><a name="6713"
      > </a
      ><a name="6714" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#5924" class="Function Operator"
      >&#10217;</a
      ><a name="6715"
      >
          </a
      ><a name="6726" href="Logic.html#6498" class="Bound"
      >y</a
      ><a name="6727"
      >
        </a
      ><a name="6736" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#6105" class="Function Operator"
      >&#8718;</a
      ><a name="6737"
      >
    </a
      ><a name="6742" class="Symbol"
      >}</a
      >
{% endraw %}</pre>
The first three components are copied from the embedding, while the
last combines the left inverse of `B ≲ A` with the equivalences of
the `to` and `fro` components from the two embeddings to obtain
the right inverse of the isomorphism.


## Conjunction is product

Given two propositions `A` and `B`, the conjunction `A × B` holds
if both `A` holds and `B` holds.  We formalise this idea by
declaring a suitable inductive type.
<pre class="Agda">{% raw %}
<a name="7197" class="Keyword"
      >data</a
      ><a name="7201"
      > </a
      ><a name="7202" href="Logic.html#7202" class="Datatype Operator"
      >_&#215;_</a
      ><a name="7205"
      > </a
      ><a name="7206" class="Symbol"
      >:</a
      ><a name="7207"
      > </a
      ><a name="7208" class="PrimitiveType"
      >Set</a
      ><a name="7211"
      > </a
      ><a name="7212" class="Symbol"
      >&#8594;</a
      ><a name="7213"
      > </a
      ><a name="7214" class="PrimitiveType"
      >Set</a
      ><a name="7217"
      > </a
      ><a name="7218" class="Symbol"
      >&#8594;</a
      ><a name="7219"
      > </a
      ><a name="7220" class="PrimitiveType"
      >Set</a
      ><a name="7223"
      > </a
      ><a name="7224" class="Keyword"
      >where</a
      ><a name="7229"
      >
  </a
      ><a name="7232" href="Logic.html#7232" class="InductiveConstructor Operator"
      >_,_</a
      ><a name="7235"
      > </a
      ><a name="7236" class="Symbol"
      >:</a
      ><a name="7237"
      > </a
      ><a name="7238" class="Symbol"
      >&#8704;</a
      ><a name="7239"
      > </a
      ><a name="7240" class="Symbol"
      >{</a
      ><a name="7241" href="Logic.html#7241" class="Bound"
      >A</a
      ><a name="7242"
      > </a
      ><a name="7243" href="Logic.html#7243" class="Bound"
      >B</a
      ><a name="7244"
      > </a
      ><a name="7245" class="Symbol"
      >:</a
      ><a name="7246"
      > </a
      ><a name="7247" class="PrimitiveType"
      >Set</a
      ><a name="7250" class="Symbol"
      >}</a
      ><a name="7251"
      > </a
      ><a name="7252" class="Symbol"
      >&#8594;</a
      ><a name="7253"
      > </a
      ><a name="7254" href="Logic.html#7241" class="Bound"
      >A</a
      ><a name="7255"
      > </a
      ><a name="7256" class="Symbol"
      >&#8594;</a
      ><a name="7257"
      > </a
      ><a name="7258" href="Logic.html#7243" class="Bound"
      >B</a
      ><a name="7259"
      > </a
      ><a name="7260" class="Symbol"
      >&#8594;</a
      ><a name="7261"
      > </a
      ><a name="7262" href="Logic.html#7241" class="Bound"
      >A</a
      ><a name="7263"
      > </a
      ><a name="7264" href="Logic.html#7202" class="Datatype Operator"
      >&#215;</a
      ><a name="7265"
      > </a
      ><a name="7266" href="Logic.html#7243" class="Bound"
      >B</a
      >
{% endraw %}</pre>
Evidence that `A × B` holds is of the form
`(M , N)`, where `M` is evidence that `A` holds and
`N` is evidence that `B` holds.

Given evidence that `A × B` holds, we can conclude that either
`A` holds or `B` holds.
<pre class="Agda">{% raw %}
<a name="7507" href="Logic.html#7507" class="Function"
      >fst</a
      ><a name="7510"
      > </a
      ><a name="7511" class="Symbol"
      >:</a
      ><a name="7512"
      > </a
      ><a name="7513" class="Symbol"
      >&#8704;</a
      ><a name="7514"
      > </a
      ><a name="7515" class="Symbol"
      >{</a
      ><a name="7516" href="Logic.html#7516" class="Bound"
      >A</a
      ><a name="7517"
      > </a
      ><a name="7518" href="Logic.html#7518" class="Bound"
      >B</a
      ><a name="7519"
      > </a
      ><a name="7520" class="Symbol"
      >:</a
      ><a name="7521"
      > </a
      ><a name="7522" class="PrimitiveType"
      >Set</a
      ><a name="7525" class="Symbol"
      >}</a
      ><a name="7526"
      > </a
      ><a name="7527" class="Symbol"
      >&#8594;</a
      ><a name="7528"
      > </a
      ><a name="7529" href="Logic.html#7516" class="Bound"
      >A</a
      ><a name="7530"
      > </a
      ><a name="7531" href="Logic.html#7202" class="Datatype Operator"
      >&#215;</a
      ><a name="7532"
      > </a
      ><a name="7533" href="Logic.html#7518" class="Bound"
      >B</a
      ><a name="7534"
      > </a
      ><a name="7535" class="Symbol"
      >&#8594;</a
      ><a name="7536"
      > </a
      ><a name="7537" href="Logic.html#7516" class="Bound"
      >A</a
      ><a name="7538"
      >
</a
      ><a name="7539" href="Logic.html#7507" class="Function"
      >fst</a
      ><a name="7542"
      > </a
      ><a name="7543" class="Symbol"
      >(</a
      ><a name="7544" href="Logic.html#7544" class="Bound"
      >x</a
      ><a name="7545"
      > </a
      ><a name="7546" href="Logic.html#7232" class="InductiveConstructor Operator"
      >,</a
      ><a name="7547"
      > </a
      ><a name="7548" href="Logic.html#7548" class="Bound"
      >y</a
      ><a name="7549" class="Symbol"
      >)</a
      ><a name="7550"
      > </a
      ><a name="7551" class="Symbol"
      >=</a
      ><a name="7552"
      > </a
      ><a name="7553" href="Logic.html#7544" class="Bound"
      >x</a
      ><a name="7554"
      >

</a
      ><a name="7556" href="Logic.html#7556" class="Function"
      >snd</a
      ><a name="7559"
      > </a
      ><a name="7560" class="Symbol"
      >:</a
      ><a name="7561"
      > </a
      ><a name="7562" class="Symbol"
      >&#8704;</a
      ><a name="7563"
      > </a
      ><a name="7564" class="Symbol"
      >{</a
      ><a name="7565" href="Logic.html#7565" class="Bound"
      >A</a
      ><a name="7566"
      > </a
      ><a name="7567" href="Logic.html#7567" class="Bound"
      >B</a
      ><a name="7568"
      > </a
      ><a name="7569" class="Symbol"
      >:</a
      ><a name="7570"
      > </a
      ><a name="7571" class="PrimitiveType"
      >Set</a
      ><a name="7574" class="Symbol"
      >}</a
      ><a name="7575"
      > </a
      ><a name="7576" class="Symbol"
      >&#8594;</a
      ><a name="7577"
      > </a
      ><a name="7578" href="Logic.html#7565" class="Bound"
      >A</a
      ><a name="7579"
      > </a
      ><a name="7580" href="Logic.html#7202" class="Datatype Operator"
      >&#215;</a
      ><a name="7581"
      > </a
      ><a name="7582" href="Logic.html#7567" class="Bound"
      >B</a
      ><a name="7583"
      > </a
      ><a name="7584" class="Symbol"
      >&#8594;</a
      ><a name="7585"
      > </a
      ><a name="7586" href="Logic.html#7567" class="Bound"
      >B</a
      ><a name="7587"
      >
</a
      ><a name="7588" href="Logic.html#7556" class="Function"
      >snd</a
      ><a name="7591"
      > </a
      ><a name="7592" class="Symbol"
      >(</a
      ><a name="7593" href="Logic.html#7593" class="Bound"
      >x</a
      ><a name="7594"
      > </a
      ><a name="7595" href="Logic.html#7232" class="InductiveConstructor Operator"
      >,</a
      ><a name="7596"
      > </a
      ><a name="7597" href="Logic.html#7597" class="Bound"
      >y</a
      ><a name="7598" class="Symbol"
      >)</a
      ><a name="7599"
      > </a
      ><a name="7600" class="Symbol"
      >=</a
      ><a name="7601"
      > </a
      ><a name="7602" href="Logic.html#7597" class="Bound"
      >y</a
      >
{% endraw %}</pre>
If `L` is evidence that `A × B` holds, then `fst L` is evidence
that `A` holds, and `snd L` is evidence that `B` holds.

Equivalently, we could also declare product as a record type.
<pre class="Agda">{% raw %}
<a name="7811" class="Keyword"
      >record</a
      ><a name="7817"
      > </a
      ><a name="7818" href="Logic.html#7818" class="Record Operator"
      >_&#215;&#8242;_</a
      ><a name="7822"
      > </a
      ><a name="7823" class="Symbol"
      >(</a
      ><a name="7824" href="Logic.html#7824" class="Bound"
      >A</a
      ><a name="7825"
      > </a
      ><a name="7826" href="Logic.html#7826" class="Bound"
      >B</a
      ><a name="7827"
      > </a
      ><a name="7828" class="Symbol"
      >:</a
      ><a name="7829"
      > </a
      ><a name="7830" class="PrimitiveType"
      >Set</a
      ><a name="7833" class="Symbol"
      >)</a
      ><a name="7834"
      > </a
      ><a name="7835" class="Symbol"
      >:</a
      ><a name="7836"
      > </a
      ><a name="7837" class="PrimitiveType"
      >Set</a
      ><a name="7840"
      > </a
      ><a name="7841" class="Keyword"
      >where</a
      ><a name="7846"
      >
  </a
      ><a name="7849" class="Keyword"
      >field</a
      ><a name="7854"
      >
    </a
      ><a name="7859" href="Logic.html#7859" class="Field"
      >fst&#8242;</a
      ><a name="7863"
      > </a
      ><a name="7864" class="Symbol"
      >:</a
      ><a name="7865"
      > </a
      ><a name="7866" href="Logic.html#7824" class="Bound"
      >A</a
      ><a name="7867"
      >
    </a
      ><a name="7872" href="Logic.html#7872" class="Field"
      >snd&#8242;</a
      ><a name="7876"
      > </a
      ><a name="7877" class="Symbol"
      >:</a
      ><a name="7878"
      > </a
      ><a name="7879" href="Logic.html#7826" class="Bound"
      >B</a
      ><a name="7880"
      >
</a
      ><a name="7881" class="Keyword"
      >open</a
      ><a name="7885"
      > </a
      ><a name="7886" href="Logic.html#7818" class="Module Operator"
      >_&#215;&#8242;_</a
      >
{% endraw %}</pre>
We construct values of the record type with the syntax:

    record
      { fst′ = M
      ; snd′ = N
      }

which corresponds to using the constructor of the corresponding
inductive type:

    ( M , N )

where `M` is a term of type `A` and `N` is a term of type `B`.

We set the precedence of conjunction so that it binds less
tightly than anything save disjunction, and of the pairing
operator so that it binds less tightly than any arithmetic
operator.
<pre class="Agda">{% raw %}
<a name="8373" class="Keyword"
      >infixr</a
      ><a name="8379"
      > </a
      ><a name="8380" class="Number"
      >2</a
      ><a name="8381"
      > </a
      ><a name="8382" href="Logic.html#7202" class="Datatype Operator"
      >_&#215;_</a
      ><a name="8385"
      >
</a
      ><a name="8386" class="Keyword"
      >infixr</a
      ><a name="8392"
      > </a
      ><a name="8393" class="Number"
      >4</a
      ><a name="8394"
      > </a
      ><a name="8395" href="Logic.html#39745" class="InductiveConstructor Operator"
      >_,_</a
      >
{% endraw %}</pre>
Thus, `m ≤ n × n ≤ p` parses as `(m ≤ n) × (n ≤ p)` and
`(m * n , p)` parses as `((m * n) , p)`.

Given two types `A` and `B`, we refer to `A x B` as the
*product* of `A` and `B`.  In set theory, it is also sometimes
called the *cartesian product*, and in computing it corresponds
to a *record* type. Among other reasons for
calling it the product, note that if type `A` has `m`
distinct members, and type `B` has `n` distinct members,
then the type `A × B` has `m * n` distinct members.
For instance, consider a type `Bool` with two members, and
a type `Tri` with three members.
<pre class="Agda">{% raw %}
<a name="9003" class="Keyword"
      >data</a
      ><a name="9007"
      > </a
      ><a name="9008" href="Logic.html#9008" class="Datatype"
      >Bool</a
      ><a name="9012"
      > </a
      ><a name="9013" class="Symbol"
      >:</a
      ><a name="9014"
      > </a
      ><a name="9015" class="PrimitiveType"
      >Set</a
      ><a name="9018"
      > </a
      ><a name="9019" class="Keyword"
      >where</a
      ><a name="9024"
      >
  </a
      ><a name="9027" href="Logic.html#9027" class="InductiveConstructor"
      >true</a
      ><a name="9031"
      > </a
      ><a name="9032" class="Symbol"
      >:</a
      ><a name="9033"
      > </a
      ><a name="9034" href="Logic.html#9008" class="Datatype"
      >Bool</a
      ><a name="9038"
      >
  </a
      ><a name="9041" href="Logic.html#9041" class="InductiveConstructor"
      >false</a
      ><a name="9046"
      > </a
      ><a name="9047" class="Symbol"
      >:</a
      ><a name="9048"
      > </a
      ><a name="9049" href="Logic.html#9008" class="Datatype"
      >Bool</a
      ><a name="9053"
      >

</a
      ><a name="9055" class="Keyword"
      >data</a
      ><a name="9059"
      > </a
      ><a name="9060" href="Logic.html#9060" class="Datatype"
      >Tri</a
      ><a name="9063"
      > </a
      ><a name="9064" class="Symbol"
      >:</a
      ><a name="9065"
      > </a
      ><a name="9066" class="PrimitiveType"
      >Set</a
      ><a name="9069"
      > </a
      ><a name="9070" class="Keyword"
      >where</a
      ><a name="9075"
      >
  </a
      ><a name="9078" href="Logic.html#9078" class="InductiveConstructor"
      >aa</a
      ><a name="9080"
      > </a
      ><a name="9081" class="Symbol"
      >:</a
      ><a name="9082"
      > </a
      ><a name="9083" href="Logic.html#9060" class="Datatype"
      >Tri</a
      ><a name="9086"
      >
  </a
      ><a name="9089" href="Logic.html#9089" class="InductiveConstructor"
      >bb</a
      ><a name="9091"
      > </a
      ><a name="9092" class="Symbol"
      >:</a
      ><a name="9093"
      > </a
      ><a name="9094" href="Logic.html#9060" class="Datatype"
      >Tri</a
      ><a name="9097"
      >
  </a
      ><a name="9100" href="Logic.html#9100" class="InductiveConstructor"
      >cc</a
      ><a name="9102"
      > </a
      ><a name="9103" class="Symbol"
      >:</a
      ><a name="9104"
      > </a
      ><a name="9105" href="Logic.html#9060" class="Datatype"
      >Tri</a
      >
{% endraw %}</pre>
Then the type `Bool × Tri` has six members:

    (true  , aa)    (true  , bb)    (true ,  cc)
    (false , aa)    (false , bb)    (false , cc)

For example, the following function enumerates all
possible arguments of type `Bool × Tri`:
<pre class="Agda">{% raw %}
<a name="9369" href="Logic.html#9369" class="Function"
      >&#215;-count</a
      ><a name="9376"
      > </a
      ><a name="9377" class="Symbol"
      >:</a
      ><a name="9378"
      > </a
      ><a name="9379" href="Logic.html#9008" class="Datatype"
      >Bool</a
      ><a name="9383"
      > </a
      ><a name="9384" href="Logic.html#7202" class="Datatype Operator"
      >&#215;</a
      ><a name="9385"
      > </a
      ><a name="9386" href="Logic.html#9060" class="Datatype"
      >Tri</a
      ><a name="9389"
      > </a
      ><a name="9390" class="Symbol"
      >&#8594;</a
      ><a name="9391"
      > </a
      ><a name="9392" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#97" class="Datatype"
      >&#8469;</a
      ><a name="9393"
      >
</a
      ><a name="9394" href="Logic.html#9369" class="Function"
      >&#215;-count</a
      ><a name="9401"
      > </a
      ><a name="9402" class="Symbol"
      >(</a
      ><a name="9403" href="Logic.html#9027" class="InductiveConstructor"
      >true</a
      ><a name="9407"
      > </a
      ><a name="9408" href="Logic.html#7232" class="InductiveConstructor Operator"
      >,</a
      ><a name="9409"
      > </a
      ><a name="9410" href="Logic.html#9078" class="InductiveConstructor"
      >aa</a
      ><a name="9412" class="Symbol"
      >)</a
      ><a name="9413"
      > </a
      ><a name="9414" class="Symbol"
      >=</a
      ><a name="9415"
      > </a
      ><a name="9416" class="Number"
      >1</a
      ><a name="9417"
      >
</a
      ><a name="9418" href="Logic.html#9369" class="Function"
      >&#215;-count</a
      ><a name="9425"
      > </a
      ><a name="9426" class="Symbol"
      >(</a
      ><a name="9427" href="Logic.html#9027" class="InductiveConstructor"
      >true</a
      ><a name="9431"
      > </a
      ><a name="9432" href="Logic.html#7232" class="InductiveConstructor Operator"
      >,</a
      ><a name="9433"
      > </a
      ><a name="9434" href="Logic.html#9089" class="InductiveConstructor"
      >bb</a
      ><a name="9436" class="Symbol"
      >)</a
      ><a name="9437"
      > </a
      ><a name="9438" class="Symbol"
      >=</a
      ><a name="9439"
      > </a
      ><a name="9440" class="Number"
      >2</a
      ><a name="9441"
      >
</a
      ><a name="9442" href="Logic.html#9369" class="Function"
      >&#215;-count</a
      ><a name="9449"
      > </a
      ><a name="9450" class="Symbol"
      >(</a
      ><a name="9451" href="Logic.html#9027" class="InductiveConstructor"
      >true</a
      ><a name="9455"
      > </a
      ><a name="9456" href="Logic.html#7232" class="InductiveConstructor Operator"
      >,</a
      ><a name="9457"
      > </a
      ><a name="9458" href="Logic.html#9100" class="InductiveConstructor"
      >cc</a
      ><a name="9460" class="Symbol"
      >)</a
      ><a name="9461"
      > </a
      ><a name="9462" class="Symbol"
      >=</a
      ><a name="9463"
      > </a
      ><a name="9464" class="Number"
      >3</a
      ><a name="9465"
      >
</a
      ><a name="9466" href="Logic.html#9369" class="Function"
      >&#215;-count</a
      ><a name="9473"
      > </a
      ><a name="9474" class="Symbol"
      >(</a
      ><a name="9475" href="Logic.html#9041" class="InductiveConstructor"
      >false</a
      ><a name="9480"
      > </a
      ><a name="9481" href="Logic.html#7232" class="InductiveConstructor Operator"
      >,</a
      ><a name="9482"
      > </a
      ><a name="9483" href="Logic.html#9078" class="InductiveConstructor"
      >aa</a
      ><a name="9485" class="Symbol"
      >)</a
      ><a name="9486"
      > </a
      ><a name="9487" class="Symbol"
      >=</a
      ><a name="9488"
      > </a
      ><a name="9489" class="Number"
      >4</a
      ><a name="9490"
      >
</a
      ><a name="9491" href="Logic.html#9369" class="Function"
      >&#215;-count</a
      ><a name="9498"
      > </a
      ><a name="9499" class="Symbol"
      >(</a
      ><a name="9500" href="Logic.html#9041" class="InductiveConstructor"
      >false</a
      ><a name="9505"
      > </a
      ><a name="9506" href="Logic.html#7232" class="InductiveConstructor Operator"
      >,</a
      ><a name="9507"
      > </a
      ><a name="9508" href="Logic.html#9089" class="InductiveConstructor"
      >bb</a
      ><a name="9510" class="Symbol"
      >)</a
      ><a name="9511"
      > </a
      ><a name="9512" class="Symbol"
      >=</a
      ><a name="9513"
      > </a
      ><a name="9514" class="Number"
      >5</a
      ><a name="9515"
      >
</a
      ><a name="9516" href="Logic.html#9369" class="Function"
      >&#215;-count</a
      ><a name="9523"
      > </a
      ><a name="9524" class="Symbol"
      >(</a
      ><a name="9525" href="Logic.html#9041" class="InductiveConstructor"
      >false</a
      ><a name="9530"
      > </a
      ><a name="9531" href="Logic.html#7232" class="InductiveConstructor Operator"
      >,</a
      ><a name="9532"
      > </a
      ><a name="9533" href="Logic.html#9100" class="InductiveConstructor"
      >cc</a
      ><a name="9535" class="Symbol"
      >)</a
      ><a name="9536"
      > </a
      ><a name="9537" class="Symbol"
      >=</a
      ><a name="9538"
      > </a
      ><a name="9539" class="Number"
      >6</a
      >
{% endraw %}</pre>

Product on types also shares a property with product on numbers in
that there is a sense in which it is commutative and associative.  In
particular, product is commutative and associative *up to
isomorphism*.

For commutativity, the `to` function swaps a pair, taking `(x , y)` to
`(y , x)`, and the `fro` function does the same (up to renaming).
Instantiating the patterns correctly in `invˡ` and `invʳ` is essential.
Replacing the definition of `invˡ` by `λ w → refl` will not work;
and similarly for `invʳ`, which does the same (up to renaming).
<pre class="Agda">{% raw %}
<a name="10115" href="Logic.html#10115" class="Function"
      >&#215;-comm</a
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
      ><a name="10127" href="Logic.html#10127" class="Bound"
      >A</a
      ><a name="10128"
      > </a
      ><a name="10129" href="Logic.html#10129" class="Bound"
      >B</a
      ><a name="10130"
      > </a
      ><a name="10131" class="Symbol"
      >:</a
      ><a name="10132"
      > </a
      ><a name="10133" class="PrimitiveType"
      >Set</a
      ><a name="10136" class="Symbol"
      >}</a
      ><a name="10137"
      > </a
      ><a name="10138" class="Symbol"
      >&#8594;</a
      ><a name="10139"
      > </a
      ><a name="10140" class="Symbol"
      >(</a
      ><a name="10141" href="Logic.html#10127" class="Bound"
      >A</a
      ><a name="10142"
      > </a
      ><a name="10143" href="Logic.html#7202" class="Datatype Operator"
      >&#215;</a
      ><a name="10144"
      > </a
      ><a name="10145" href="Logic.html#10129" class="Bound"
      >B</a
      ><a name="10146" class="Symbol"
      >)</a
      ><a name="10147"
      > </a
      ><a name="10148" href="Logic.html#1478" class="Record Operator"
      >&#8771;</a
      ><a name="10149"
      > </a
      ><a name="10150" class="Symbol"
      >(</a
      ><a name="10151" href="Logic.html#10129" class="Bound"
      >B</a
      ><a name="10152"
      > </a
      ><a name="10153" href="Logic.html#7202" class="Datatype Operator"
      >&#215;</a
      ><a name="10154"
      > </a
      ><a name="10155" href="Logic.html#10127" class="Bound"
      >A</a
      ><a name="10156" class="Symbol"
      >)</a
      ><a name="10157"
      >
</a
      ><a name="10158" href="Logic.html#10115" class="Function"
      >&#215;-comm</a
      ><a name="10164"
      > </a
      ><a name="10165" class="Symbol"
      >=</a
      ><a name="10166"
      >
  </a
      ><a name="10169" class="Keyword"
      >record</a
      ><a name="10175"
      >
    </a
      ><a name="10180" class="Symbol"
      >{</a
      ><a name="10181"
      > </a
      ><a name="10182" class="Field"
      >to</a
      ><a name="10184"
      > </a
      ><a name="10185" class="Symbol"
      >=</a
      ><a name="10186"
      > </a
      ><a name="10187" class="Symbol"
      >&#955;</a
      ><a name="10188"
      > </a
      ><a name="10189" class="Symbol"
      >{</a
      ><a name="10190"
      > </a
      ><a name="10191" class="Symbol"
      >(</a
      ><a name="10192" href="Logic.html#10192" class="Bound"
      >x</a
      ><a name="10193"
      > </a
      ><a name="10194" href="Logic.html#7232" class="InductiveConstructor Operator"
      >,</a
      ><a name="10195"
      > </a
      ><a name="10196" href="Logic.html#10196" class="Bound"
      >y</a
      ><a name="10197" class="Symbol"
      >)</a
      ><a name="10198"
      > </a
      ><a name="10199" class="Symbol"
      >&#8594;</a
      ><a name="10200"
      > </a
      ><a name="10201" class="Symbol"
      >(</a
      ><a name="10202" href="Logic.html#10196" class="Bound"
      >y</a
      ><a name="10203"
      > </a
      ><a name="10204" href="Logic.html#7232" class="InductiveConstructor Operator"
      >,</a
      ><a name="10205"
      > </a
      ><a name="10206" href="Logic.html#10192" class="Bound"
      >x</a
      ><a name="10207" class="Symbol"
      >)}</a
      ><a name="10209"
      >
    </a
      ><a name="10214" class="Symbol"
      >;</a
      ><a name="10215"
      > </a
      ><a name="10216" class="Field"
      >fro</a
      ><a name="10219"
      > </a
      ><a name="10220" class="Symbol"
      >=</a
      ><a name="10221"
      > </a
      ><a name="10222" class="Symbol"
      >&#955;</a
      ><a name="10223"
      > </a
      ><a name="10224" class="Symbol"
      >{</a
      ><a name="10225"
      > </a
      ><a name="10226" class="Symbol"
      >(</a
      ><a name="10227" href="Logic.html#10227" class="Bound"
      >y</a
      ><a name="10228"
      > </a
      ><a name="10229" href="Logic.html#7232" class="InductiveConstructor Operator"
      >,</a
      ><a name="10230"
      > </a
      ><a name="10231" href="Logic.html#10231" class="Bound"
      >x</a
      ><a name="10232" class="Symbol"
      >)</a
      ><a name="10233"
      > </a
      ><a name="10234" class="Symbol"
      >&#8594;</a
      ><a name="10235"
      > </a
      ><a name="10236" class="Symbol"
      >(</a
      ><a name="10237" href="Logic.html#10231" class="Bound"
      >x</a
      ><a name="10238"
      > </a
      ><a name="10239" href="Logic.html#7232" class="InductiveConstructor Operator"
      >,</a
      ><a name="10240"
      > </a
      ><a name="10241" href="Logic.html#10227" class="Bound"
      >y</a
      ><a name="10242" class="Symbol"
      >)}</a
      ><a name="10244"
      >
    </a
      ><a name="10249" class="Symbol"
      >;</a
      ><a name="10250"
      > </a
      ><a name="10251" class="Field"
      >inv&#737;</a
      ><a name="10255"
      > </a
      ><a name="10256" class="Symbol"
      >=</a
      ><a name="10257"
      > </a
      ><a name="10258" class="Symbol"
      >&#955;</a
      ><a name="10259"
      > </a
      ><a name="10260" class="Symbol"
      >{</a
      ><a name="10261"
      > </a
      ><a name="10262" class="Symbol"
      >(</a
      ><a name="10263" href="Logic.html#10263" class="Bound"
      >x</a
      ><a name="10264"
      > </a
      ><a name="10265" href="Logic.html#7232" class="InductiveConstructor Operator"
      >,</a
      ><a name="10266"
      > </a
      ><a name="10267" href="Logic.html#10267" class="Bound"
      >y</a
      ><a name="10268" class="Symbol"
      >)</a
      ><a name="10269"
      > </a
      ><a name="10270" class="Symbol"
      >&#8594;</a
      ><a name="10271"
      > </a
      ><a name="10272" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="10276"
      > </a
      ><a name="10277" class="Symbol"
      >}</a
      ><a name="10278"
      >
    </a
      ><a name="10283" class="Symbol"
      >;</a
      ><a name="10284"
      > </a
      ><a name="10285" class="Field"
      >inv&#691;</a
      ><a name="10289"
      > </a
      ><a name="10290" class="Symbol"
      >=</a
      ><a name="10291"
      > </a
      ><a name="10292" class="Symbol"
      >&#955;</a
      ><a name="10293"
      > </a
      ><a name="10294" class="Symbol"
      >{</a
      ><a name="10295"
      > </a
      ><a name="10296" class="Symbol"
      >(</a
      ><a name="10297" href="Logic.html#10297" class="Bound"
      >y</a
      ><a name="10298"
      > </a
      ><a name="10299" href="Logic.html#7232" class="InductiveConstructor Operator"
      >,</a
      ><a name="10300"
      > </a
      ><a name="10301" href="Logic.html#10301" class="Bound"
      >x</a
      ><a name="10302" class="Symbol"
      >)</a
      ><a name="10303"
      > </a
      ><a name="10304" class="Symbol"
      >&#8594;</a
      ><a name="10305"
      > </a
      ><a name="10306" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="10310"
      > </a
      ><a name="10311" class="Symbol"
      >}</a
      ><a name="10312"
      >
    </a
      ><a name="10317" class="Symbol"
      >}</a
      >
{% endraw %}</pre>

Being *commutative* is different from being *commutative up to
isomorphism*.  Compare the two statements:

    m * n ≡ n * m
    A × B ≃ B × A

In the first case, we might have that `m` is `2` and `n` is `3`, and
both `m * n` and `n * m` are equal to `6`.  In the second case, we
might have that `A` is `Bool` and `B` is `Tri`, and `Bool × Tri` is
*not* the same as `Tri × Bool`.  But there is an isomorphism
between the two types.  For
instance, `(true , aa)`, which is a member of the former, corresponds
to `(aa , true)`, which is a member of the latter.

For associativity, the `to` function reassociates two uses of pairing,
taking `((x , y) , z)` to `(x , (y , z))`, and the `fro` function does
the inverse.  Again, the evidence of left and right inverse requires
matching against a suitable pattern to enable simplificition.
<pre class="Agda">{% raw %}
<a name="11177" href="Logic.html#11177" class="Function"
      >&#215;-assoc</a
      ><a name="11184"
      > </a
      ><a name="11185" class="Symbol"
      >:</a
      ><a name="11186"
      > </a
      ><a name="11187" class="Symbol"
      >&#8704;</a
      ><a name="11188"
      > </a
      ><a name="11189" class="Symbol"
      >{</a
      ><a name="11190" href="Logic.html#11190" class="Bound"
      >A</a
      ><a name="11191"
      > </a
      ><a name="11192" href="Logic.html#11192" class="Bound"
      >B</a
      ><a name="11193"
      > </a
      ><a name="11194" href="Logic.html#11194" class="Bound"
      >C</a
      ><a name="11195"
      > </a
      ><a name="11196" class="Symbol"
      >:</a
      ><a name="11197"
      > </a
      ><a name="11198" class="PrimitiveType"
      >Set</a
      ><a name="11201" class="Symbol"
      >}</a
      ><a name="11202"
      > </a
      ><a name="11203" class="Symbol"
      >&#8594;</a
      ><a name="11204"
      > </a
      ><a name="11205" class="Symbol"
      >((</a
      ><a name="11207" href="Logic.html#11190" class="Bound"
      >A</a
      ><a name="11208"
      > </a
      ><a name="11209" href="Logic.html#7202" class="Datatype Operator"
      >&#215;</a
      ><a name="11210"
      > </a
      ><a name="11211" href="Logic.html#11192" class="Bound"
      >B</a
      ><a name="11212" class="Symbol"
      >)</a
      ><a name="11213"
      > </a
      ><a name="11214" href="Logic.html#7202" class="Datatype Operator"
      >&#215;</a
      ><a name="11215"
      > </a
      ><a name="11216" href="Logic.html#11194" class="Bound"
      >C</a
      ><a name="11217" class="Symbol"
      >)</a
      ><a name="11218"
      > </a
      ><a name="11219" href="Logic.html#1478" class="Record Operator"
      >&#8771;</a
      ><a name="11220"
      > </a
      ><a name="11221" class="Symbol"
      >(</a
      ><a name="11222" href="Logic.html#11190" class="Bound"
      >A</a
      ><a name="11223"
      > </a
      ><a name="11224" href="Logic.html#7202" class="Datatype Operator"
      >&#215;</a
      ><a name="11225"
      > </a
      ><a name="11226" class="Symbol"
      >(</a
      ><a name="11227" href="Logic.html#11192" class="Bound"
      >B</a
      ><a name="11228"
      > </a
      ><a name="11229" href="Logic.html#7202" class="Datatype Operator"
      >&#215;</a
      ><a name="11230"
      > </a
      ><a name="11231" href="Logic.html#11194" class="Bound"
      >C</a
      ><a name="11232" class="Symbol"
      >))</a
      ><a name="11234"
      >
</a
      ><a name="11235" href="Logic.html#11177" class="Function"
      >&#215;-assoc</a
      ><a name="11242"
      > </a
      ><a name="11243" class="Symbol"
      >=</a
      ><a name="11244"
      >
  </a
      ><a name="11247" class="Keyword"
      >record</a
      ><a name="11253"
      >
    </a
      ><a name="11258" class="Symbol"
      >{</a
      ><a name="11259"
      > </a
      ><a name="11260" class="Field"
      >to</a
      ><a name="11262"
      > </a
      ><a name="11263" class="Symbol"
      >=</a
      ><a name="11264"
      > </a
      ><a name="11265" class="Symbol"
      >&#955;</a
      ><a name="11266"
      > </a
      ><a name="11267" class="Symbol"
      >{</a
      ><a name="11268"
      > </a
      ><a name="11269" class="Symbol"
      >((</a
      ><a name="11271" href="Logic.html#11271" class="Bound"
      >x</a
      ><a name="11272"
      > </a
      ><a name="11273" href="Logic.html#7232" class="InductiveConstructor Operator"
      >,</a
      ><a name="11274"
      > </a
      ><a name="11275" href="Logic.html#11275" class="Bound"
      >y</a
      ><a name="11276" class="Symbol"
      >)</a
      ><a name="11277"
      > </a
      ><a name="11278" href="Logic.html#7232" class="InductiveConstructor Operator"
      >,</a
      ><a name="11279"
      > </a
      ><a name="11280" href="Logic.html#11280" class="Bound"
      >z</a
      ><a name="11281" class="Symbol"
      >)</a
      ><a name="11282"
      > </a
      ><a name="11283" class="Symbol"
      >&#8594;</a
      ><a name="11284"
      > </a
      ><a name="11285" class="Symbol"
      >(</a
      ><a name="11286" href="Logic.html#11271" class="Bound"
      >x</a
      ><a name="11287"
      > </a
      ><a name="11288" href="Logic.html#7232" class="InductiveConstructor Operator"
      >,</a
      ><a name="11289"
      > </a
      ><a name="11290" class="Symbol"
      >(</a
      ><a name="11291" href="Logic.html#11275" class="Bound"
      >y</a
      ><a name="11292"
      > </a
      ><a name="11293" href="Logic.html#7232" class="InductiveConstructor Operator"
      >,</a
      ><a name="11294"
      > </a
      ><a name="11295" href="Logic.html#11280" class="Bound"
      >z</a
      ><a name="11296" class="Symbol"
      >))</a
      ><a name="11298"
      > </a
      ><a name="11299" class="Symbol"
      >}</a
      ><a name="11300"
      >
    </a
      ><a name="11305" class="Symbol"
      >;</a
      ><a name="11306"
      > </a
      ><a name="11307" class="Field"
      >fro</a
      ><a name="11310"
      > </a
      ><a name="11311" class="Symbol"
      >=</a
      ><a name="11312"
      > </a
      ><a name="11313" class="Symbol"
      >&#955;</a
      ><a name="11314"
      > </a
      ><a name="11315" class="Symbol"
      >{</a
      ><a name="11316"
      > </a
      ><a name="11317" class="Symbol"
      >(</a
      ><a name="11318" href="Logic.html#11318" class="Bound"
      >x</a
      ><a name="11319"
      > </a
      ><a name="11320" href="Logic.html#7232" class="InductiveConstructor Operator"
      >,</a
      ><a name="11321"
      > </a
      ><a name="11322" class="Symbol"
      >(</a
      ><a name="11323" href="Logic.html#11323" class="Bound"
      >y</a
      ><a name="11324"
      > </a
      ><a name="11325" href="Logic.html#7232" class="InductiveConstructor Operator"
      >,</a
      ><a name="11326"
      > </a
      ><a name="11327" href="Logic.html#11327" class="Bound"
      >z</a
      ><a name="11328" class="Symbol"
      >))</a
      ><a name="11330"
      > </a
      ><a name="11331" class="Symbol"
      >&#8594;</a
      ><a name="11332"
      > </a
      ><a name="11333" class="Symbol"
      >((</a
      ><a name="11335" href="Logic.html#11318" class="Bound"
      >x</a
      ><a name="11336"
      > </a
      ><a name="11337" href="Logic.html#7232" class="InductiveConstructor Operator"
      >,</a
      ><a name="11338"
      > </a
      ><a name="11339" href="Logic.html#11323" class="Bound"
      >y</a
      ><a name="11340" class="Symbol"
      >)</a
      ><a name="11341"
      > </a
      ><a name="11342" href="Logic.html#7232" class="InductiveConstructor Operator"
      >,</a
      ><a name="11343"
      > </a
      ><a name="11344" href="Logic.html#11327" class="Bound"
      >z</a
      ><a name="11345" class="Symbol"
      >)</a
      ><a name="11346"
      > </a
      ><a name="11347" class="Symbol"
      >}</a
      ><a name="11348"
      >
    </a
      ><a name="11353" class="Symbol"
      >;</a
      ><a name="11354"
      > </a
      ><a name="11355" class="Field"
      >inv&#737;</a
      ><a name="11359"
      > </a
      ><a name="11360" class="Symbol"
      >=</a
      ><a name="11361"
      > </a
      ><a name="11362" class="Symbol"
      >&#955;</a
      ><a name="11363"
      > </a
      ><a name="11364" class="Symbol"
      >{</a
      ><a name="11365"
      > </a
      ><a name="11366" class="Symbol"
      >((</a
      ><a name="11368" href="Logic.html#11368" class="Bound"
      >x</a
      ><a name="11369"
      > </a
      ><a name="11370" href="Logic.html#7232" class="InductiveConstructor Operator"
      >,</a
      ><a name="11371"
      > </a
      ><a name="11372" href="Logic.html#11372" class="Bound"
      >y</a
      ><a name="11373" class="Symbol"
      >)</a
      ><a name="11374"
      > </a
      ><a name="11375" href="Logic.html#7232" class="InductiveConstructor Operator"
      >,</a
      ><a name="11376"
      > </a
      ><a name="11377" href="Logic.html#11377" class="Bound"
      >z</a
      ><a name="11378" class="Symbol"
      >)</a
      ><a name="11379"
      > </a
      ><a name="11380" class="Symbol"
      >&#8594;</a
      ><a name="11381"
      > </a
      ><a name="11382" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="11386"
      > </a
      ><a name="11387" class="Symbol"
      >}</a
      ><a name="11388"
      >
    </a
      ><a name="11393" class="Symbol"
      >;</a
      ><a name="11394"
      > </a
      ><a name="11395" class="Field"
      >inv&#691;</a
      ><a name="11399"
      > </a
      ><a name="11400" class="Symbol"
      >=</a
      ><a name="11401"
      > </a
      ><a name="11402" class="Symbol"
      >&#955;</a
      ><a name="11403"
      > </a
      ><a name="11404" class="Symbol"
      >{</a
      ><a name="11405"
      > </a
      ><a name="11406" class="Symbol"
      >(</a
      ><a name="11407" href="Logic.html#11407" class="Bound"
      >x</a
      ><a name="11408"
      > </a
      ><a name="11409" href="Logic.html#7232" class="InductiveConstructor Operator"
      >,</a
      ><a name="11410"
      > </a
      ><a name="11411" class="Symbol"
      >(</a
      ><a name="11412" href="Logic.html#11412" class="Bound"
      >y</a
      ><a name="11413"
      > </a
      ><a name="11414" href="Logic.html#7232" class="InductiveConstructor Operator"
      >,</a
      ><a name="11415"
      > </a
      ><a name="11416" href="Logic.html#11416" class="Bound"
      >z</a
      ><a name="11417" class="Symbol"
      >))</a
      ><a name="11419"
      > </a
      ><a name="11420" class="Symbol"
      >&#8594;</a
      ><a name="11421"
      > </a
      ><a name="11422" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="11426"
      > </a
      ><a name="11427" class="Symbol"
      >}</a
      ><a name="11428"
      >
    </a
      ><a name="11433" class="Symbol"
      >}</a
      >
{% endraw %}</pre>

Being *associative* is not the same as being *associative
up to isomorphism*.  Compare the two statements:

  (m * n) * p ≡ m * (n * p)
  (A × B) × C ≃ A × (B × C)

For example, the type `(ℕ × Bool) × Tri` is *not* the same as `ℕ ×
(Bool × Tri)`. But there is an isomorphism between the two types. For
instance `((1 , true) , aa)`, which is a member of the former,
corresponds to `(1 , (true , aa))`, which is a member of the latter.

Here we have used lambda-expressions with pattern matching.
For instance, the term

    λ { (x , y) → (y , x) }

corresponds to the function `h`, where `h` is defined by
<pre class="Agda">{% raw %}
<a name="12066" href="Logic.html#12066" class="Function"
      >h</a
      ><a name="12067"
      > </a
      ><a name="12068" class="Symbol"
      >:</a
      ><a name="12069"
      > </a
      ><a name="12070" class="Symbol"
      >&#8704;</a
      ><a name="12071"
      > </a
      ><a name="12072" class="Symbol"
      >{</a
      ><a name="12073" href="Logic.html#12073" class="Bound"
      >A</a
      ><a name="12074"
      > </a
      ><a name="12075" href="Logic.html#12075" class="Bound"
      >B</a
      ><a name="12076"
      > </a
      ><a name="12077" class="Symbol"
      >:</a
      ><a name="12078"
      > </a
      ><a name="12079" class="PrimitiveType"
      >Set</a
      ><a name="12082" class="Symbol"
      >}</a
      ><a name="12083"
      > </a
      ><a name="12084" class="Symbol"
      >&#8594;</a
      ><a name="12085"
      > </a
      ><a name="12086" href="Logic.html#12073" class="Bound"
      >A</a
      ><a name="12087"
      > </a
      ><a name="12088" href="Logic.html#7202" class="Datatype Operator"
      >&#215;</a
      ><a name="12089"
      > </a
      ><a name="12090" href="Logic.html#12075" class="Bound"
      >B</a
      ><a name="12091"
      > </a
      ><a name="12092" class="Symbol"
      >&#8594;</a
      ><a name="12093"
      > </a
      ><a name="12094" href="Logic.html#12075" class="Bound"
      >B</a
      ><a name="12095"
      > </a
      ><a name="12096" href="Logic.html#7202" class="Datatype Operator"
      >&#215;</a
      ><a name="12097"
      > </a
      ><a name="12098" href="Logic.html#12073" class="Bound"
      >A</a
      ><a name="12099"
      >
</a
      ><a name="12100" href="Logic.html#12066" class="Function"
      >h</a
      ><a name="12101"
      > </a
      ><a name="12102" class="Symbol"
      >(</a
      ><a name="12103" href="Logic.html#12103" class="Bound"
      >x</a
      ><a name="12104"
      > </a
      ><a name="12105" href="Logic.html#7232" class="InductiveConstructor Operator"
      >,</a
      ><a name="12106"
      > </a
      ><a name="12107" href="Logic.html#12107" class="Bound"
      >y</a
      ><a name="12108" class="Symbol"
      >)</a
      ><a name="12109"
      > </a
      ><a name="12110" class="Symbol"
      >=</a
      ><a name="12111"
      > </a
      ><a name="12112" class="Symbol"
      >(</a
      ><a name="12113" href="Logic.html#12107" class="Bound"
      >y</a
      ><a name="12114"
      > </a
      ><a name="12115" href="Logic.html#7232" class="InductiveConstructor Operator"
      >,</a
      ><a name="12116"
      > </a
      ><a name="12117" href="Logic.html#12103" class="Bound"
      >x</a
      ><a name="12118" class="Symbol"
      >)</a
      >
{% endraw %}</pre>
Often using an anonymous lambda expression is more convenient than
using a named function: it avoids a lengthy type declaration; and the
definition appears exactly where the function is used, so there is no
need for the writer to remember to declare it in advance, or for the
reader to search for the definition elsewhere in the code.

## Truth is unit

Truth `⊤` always holds. We formalise this idea by
declaring a suitable inductive type.
<pre class="Agda">{% raw %}
<a name="12585" class="Keyword"
      >data</a
      ><a name="12589"
      > </a
      ><a name="12590" href="Logic.html#12590" class="Datatype"
      >&#8868;</a
      ><a name="12591"
      > </a
      ><a name="12592" class="Symbol"
      >:</a
      ><a name="12593"
      > </a
      ><a name="12594" class="PrimitiveType"
      >Set</a
      ><a name="12597"
      > </a
      ><a name="12598" class="Keyword"
      >where</a
      ><a name="12603"
      >
  </a
      ><a name="12606" href="Logic.html#12606" class="InductiveConstructor"
      >tt</a
      ><a name="12608"
      > </a
      ><a name="12609" class="Symbol"
      >:</a
      ><a name="12610"
      > </a
      ><a name="12611" href="Logic.html#12590" class="Datatype"
      >&#8868;</a
      >
{% endraw %}</pre>
Evidence that `⊤` holds is of the form `tt`.

Given evidence that `⊤` holds, there is nothing more of interest we
can conclude.  Since truth always holds, knowing that it holds tells
us nothing new.

We refer to `⊤` as *the unit type* or just *unit*. And, indeed,
type `⊤` has exactly once member, `tt`.  For example, the following
function enumerates all possible arguments of type `⊤`:
<pre class="Agda">{% raw %}
<a name="13025" href="Logic.html#13025" class="Function"
      >&#8868;-count</a
      ><a name="13032"
      > </a
      ><a name="13033" class="Symbol"
      >:</a
      ><a name="13034"
      > </a
      ><a name="13035" href="Logic.html#12590" class="Datatype"
      >&#8868;</a
      ><a name="13036"
      > </a
      ><a name="13037" class="Symbol"
      >&#8594;</a
      ><a name="13038"
      > </a
      ><a name="13039" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#97" class="Datatype"
      >&#8469;</a
      ><a name="13040"
      >
</a
      ><a name="13041" href="Logic.html#13025" class="Function"
      >&#8868;-count</a
      ><a name="13048"
      > </a
      ><a name="13049" href="Logic.html#12606" class="InductiveConstructor"
      >tt</a
      ><a name="13051"
      > </a
      ><a name="13052" class="Symbol"
      >=</a
      ><a name="13053"
      > </a
      ><a name="13054" class="Number"
      >1</a
      >
{% endraw %}</pre>

For numbers, one is the identity of multiplication. Correspondingly,
unit is the identity of product *up to isomorphism*.

For left identity, the `to` function takes `(tt , x)` to `x`, and the `fro` function
does the inverse.  The evidence of left inverse requires matching against
a suitable pattern to enable simplification.
<pre class="Agda">{% raw %}
<a name="13408" href="Logic.html#13408" class="Function"
      >&#8868;-identity&#737;</a
      ><a name="13419"
      > </a
      ><a name="13420" class="Symbol"
      >:</a
      ><a name="13421"
      > </a
      ><a name="13422" class="Symbol"
      >&#8704;</a
      ><a name="13423"
      > </a
      ><a name="13424" class="Symbol"
      >{</a
      ><a name="13425" href="Logic.html#13425" class="Bound"
      >A</a
      ><a name="13426"
      > </a
      ><a name="13427" class="Symbol"
      >:</a
      ><a name="13428"
      > </a
      ><a name="13429" class="PrimitiveType"
      >Set</a
      ><a name="13432" class="Symbol"
      >}</a
      ><a name="13433"
      > </a
      ><a name="13434" class="Symbol"
      >&#8594;</a
      ><a name="13435"
      > </a
      ><a name="13436" class="Symbol"
      >(</a
      ><a name="13437" href="Logic.html#12590" class="Datatype"
      >&#8868;</a
      ><a name="13438"
      > </a
      ><a name="13439" href="Logic.html#7202" class="Datatype Operator"
      >&#215;</a
      ><a name="13440"
      > </a
      ><a name="13441" href="Logic.html#13425" class="Bound"
      >A</a
      ><a name="13442" class="Symbol"
      >)</a
      ><a name="13443"
      > </a
      ><a name="13444" href="Logic.html#1478" class="Record Operator"
      >&#8771;</a
      ><a name="13445"
      > </a
      ><a name="13446" href="Logic.html#13425" class="Bound"
      >A</a
      ><a name="13447"
      >
</a
      ><a name="13448" href="Logic.html#13408" class="Function"
      >&#8868;-identity&#737;</a
      ><a name="13459"
      > </a
      ><a name="13460" class="Symbol"
      >=</a
      ><a name="13461"
      >
  </a
      ><a name="13464" class="Keyword"
      >record</a
      ><a name="13470"
      >
    </a
      ><a name="13475" class="Symbol"
      >{</a
      ><a name="13476"
      > </a
      ><a name="13477" class="Field"
      >to</a
      ><a name="13479"
      >   </a
      ><a name="13482" class="Symbol"
      >=</a
      ><a name="13483"
      > </a
      ><a name="13484" class="Symbol"
      >&#955;</a
      ><a name="13485"
      > </a
      ><a name="13486" class="Symbol"
      >{</a
      ><a name="13487"
      > </a
      ><a name="13488" class="Symbol"
      >(</a
      ><a name="13489" href="Logic.html#12606" class="InductiveConstructor"
      >tt</a
      ><a name="13491"
      > </a
      ><a name="13492" href="Logic.html#7232" class="InductiveConstructor Operator"
      >,</a
      ><a name="13493"
      > </a
      ><a name="13494" href="Logic.html#13494" class="Bound"
      >x</a
      ><a name="13495" class="Symbol"
      >)</a
      ><a name="13496"
      > </a
      ><a name="13497" class="Symbol"
      >&#8594;</a
      ><a name="13498"
      > </a
      ><a name="13499" href="Logic.html#13494" class="Bound"
      >x</a
      ><a name="13500"
      > </a
      ><a name="13501" class="Symbol"
      >}</a
      ><a name="13502"
      >
    </a
      ><a name="13507" class="Symbol"
      >;</a
      ><a name="13508"
      > </a
      ><a name="13509" class="Field"
      >fro</a
      ><a name="13512"
      >  </a
      ><a name="13514" class="Symbol"
      >=</a
      ><a name="13515"
      > </a
      ><a name="13516" class="Symbol"
      >&#955;</a
      ><a name="13517"
      > </a
      ><a name="13518" class="Symbol"
      >{</a
      ><a name="13519"
      > </a
      ><a name="13520" href="Logic.html#13520" class="Bound"
      >x</a
      ><a name="13521"
      > </a
      ><a name="13522" class="Symbol"
      >&#8594;</a
      ><a name="13523"
      > </a
      ><a name="13524" class="Symbol"
      >(</a
      ><a name="13525" href="Logic.html#12606" class="InductiveConstructor"
      >tt</a
      ><a name="13527"
      > </a
      ><a name="13528" href="Logic.html#7232" class="InductiveConstructor Operator"
      >,</a
      ><a name="13529"
      > </a
      ><a name="13530" href="Logic.html#13520" class="Bound"
      >x</a
      ><a name="13531" class="Symbol"
      >)</a
      ><a name="13532"
      > </a
      ><a name="13533" class="Symbol"
      >}</a
      ><a name="13534"
      >
    </a
      ><a name="13539" class="Symbol"
      >;</a
      ><a name="13540"
      > </a
      ><a name="13541" class="Field"
      >inv&#737;</a
      ><a name="13545"
      > </a
      ><a name="13546" class="Symbol"
      >=</a
      ><a name="13547"
      > </a
      ><a name="13548" class="Symbol"
      >&#955;</a
      ><a name="13549"
      > </a
      ><a name="13550" class="Symbol"
      >{</a
      ><a name="13551"
      > </a
      ><a name="13552" class="Symbol"
      >(</a
      ><a name="13553" href="Logic.html#12606" class="InductiveConstructor"
      >tt</a
      ><a name="13555"
      > </a
      ><a name="13556" href="Logic.html#7232" class="InductiveConstructor Operator"
      >,</a
      ><a name="13557"
      > </a
      ><a name="13558" href="Logic.html#13558" class="Bound"
      >x</a
      ><a name="13559" class="Symbol"
      >)</a
      ><a name="13560"
      > </a
      ><a name="13561" class="Symbol"
      >&#8594;</a
      ><a name="13562"
      > </a
      ><a name="13563" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="13567"
      > </a
      ><a name="13568" class="Symbol"
      >}</a
      ><a name="13569"
      >
    </a
      ><a name="13574" class="Symbol"
      >;</a
      ><a name="13575"
      > </a
      ><a name="13576" class="Field"
      >inv&#691;</a
      ><a name="13580"
      > </a
      ><a name="13581" class="Symbol"
      >=</a
      ><a name="13582"
      > </a
      ><a name="13583" class="Symbol"
      >&#955;</a
      ><a name="13584"
      > </a
      ><a name="13585" class="Symbol"
      >{</a
      ><a name="13586"
      > </a
      ><a name="13587" href="Logic.html#13587" class="Bound"
      >x</a
      ><a name="13588"
      > </a
      ><a name="13589" class="Symbol"
      >&#8594;</a
      ><a name="13590"
      > </a
      ><a name="13591" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="13595" class="Symbol"
      >}</a
      ><a name="13596"
      >
    </a
      ><a name="13601" class="Symbol"
      >}</a
      >
{% endraw %}</pre>

Having an *identity* is different from having an identity
*up to isomorphism*.  Compare the two statements:

    1 * m ≡ m
    ⊤ × A ≃ A

In the first case, we might have that `m` is `2`, and both
`1 * m` and `m` are equal to `2`.  In the second
case, we might have that `A` is `Bool`, and `⊤ × Bool` is *not* the
same as `Bool`.  But there is an isomorphism betwee the two types.
For instance, `(tt, true)`, which is a member of the former,
corresponds to `true`, which is a member of the latter.

That unit is also a right identity follows immediately from left
identity, commutativity of product, and symmetry and transitivity of
isomorphism.
<pre class="Agda">{% raw %}
<a name="14274" href="Logic.html#14274" class="Function"
      >&#8868;-identity&#691;</a
      ><a name="14285"
      > </a
      ><a name="14286" class="Symbol"
      >:</a
      ><a name="14287"
      > </a
      ><a name="14288" class="Symbol"
      >&#8704;</a
      ><a name="14289"
      > </a
      ><a name="14290" class="Symbol"
      >{</a
      ><a name="14291" href="Logic.html#14291" class="Bound"
      >A</a
      ><a name="14292"
      > </a
      ><a name="14293" class="Symbol"
      >:</a
      ><a name="14294"
      > </a
      ><a name="14295" class="PrimitiveType"
      >Set</a
      ><a name="14298" class="Symbol"
      >}</a
      ><a name="14299"
      > </a
      ><a name="14300" class="Symbol"
      >&#8594;</a
      ><a name="14301"
      > </a
      ><a name="14302" href="Logic.html#14291" class="Bound"
      >A</a
      ><a name="14303"
      > </a
      ><a name="14304" href="Logic.html#1478" class="Record Operator"
      >&#8771;</a
      ><a name="14305"
      > </a
      ><a name="14306" class="Symbol"
      >(</a
      ><a name="14307" href="Logic.html#14291" class="Bound"
      >A</a
      ><a name="14308"
      > </a
      ><a name="14309" href="Logic.html#7202" class="Datatype Operator"
      >&#215;</a
      ><a name="14310"
      > </a
      ><a name="14311" href="Logic.html#12590" class="Datatype"
      >&#8868;</a
      ><a name="14312" class="Symbol"
      >)</a
      ><a name="14313"
      >
</a
      ><a name="14314" href="Logic.html#14274" class="Function"
      >&#8868;-identity&#691;</a
      ><a name="14325"
      > </a
      ><a name="14326" class="Symbol"
      >=</a
      ><a name="14327"
      > </a
      ><a name="14328" href="Logic.html#3956" class="Function"
      >&#8771;-trans</a
      ><a name="14335"
      > </a
      ><a name="14336" class="Symbol"
      >(</a
      ><a name="14337" href="Logic.html#3655" class="Function"
      >&#8771;-sym</a
      ><a name="14342"
      > </a
      ><a name="14343" href="Logic.html#13408" class="Function"
      >&#8868;-identity&#737;</a
      ><a name="14354" class="Symbol"
      >)</a
      ><a name="14355"
      > </a
      ><a name="14356" href="Logic.html#10115" class="Function"
      >&#215;-comm</a
      >
{% endraw %}</pre>

[TODO: We could introduce a notation similar to that for reasoning on ≡.]


## Disjunction is sum

Given two propositions `A` and `B`, the disjunction `A ⊎ B` holds
if either `A` holds or `B` holds.  We formalise this idea by
declaring a suitable inductive type.
<pre class="Agda">{% raw %}
<a name="14651" class="Keyword"
      >data</a
      ><a name="14655"
      > </a
      ><a name="14656" href="Logic.html#14656" class="Datatype Operator"
      >_&#8846;_</a
      ><a name="14659"
      > </a
      ><a name="14660" class="Symbol"
      >:</a
      ><a name="14661"
      > </a
      ><a name="14662" class="PrimitiveType"
      >Set</a
      ><a name="14665"
      > </a
      ><a name="14666" class="Symbol"
      >&#8594;</a
      ><a name="14667"
      > </a
      ><a name="14668" class="PrimitiveType"
      >Set</a
      ><a name="14671"
      > </a
      ><a name="14672" class="Symbol"
      >&#8594;</a
      ><a name="14673"
      > </a
      ><a name="14674" class="PrimitiveType"
      >Set</a
      ><a name="14677"
      > </a
      ><a name="14678" class="Keyword"
      >where</a
      ><a name="14683"
      >
  </a
      ><a name="14686" href="Logic.html#14686" class="InductiveConstructor"
      >inj&#8321;</a
      ><a name="14690"
      >  </a
      ><a name="14692" class="Symbol"
      >:</a
      ><a name="14693"
      > </a
      ><a name="14694" class="Symbol"
      >&#8704;</a
      ><a name="14695"
      > </a
      ><a name="14696" class="Symbol"
      >{</a
      ><a name="14697" href="Logic.html#14697" class="Bound"
      >A</a
      ><a name="14698"
      > </a
      ><a name="14699" href="Logic.html#14699" class="Bound"
      >B</a
      ><a name="14700"
      > </a
      ><a name="14701" class="Symbol"
      >:</a
      ><a name="14702"
      > </a
      ><a name="14703" class="PrimitiveType"
      >Set</a
      ><a name="14706" class="Symbol"
      >}</a
      ><a name="14707"
      > </a
      ><a name="14708" class="Symbol"
      >&#8594;</a
      ><a name="14709"
      > </a
      ><a name="14710" href="Logic.html#14697" class="Bound"
      >A</a
      ><a name="14711"
      > </a
      ><a name="14712" class="Symbol"
      >&#8594;</a
      ><a name="14713"
      > </a
      ><a name="14714" href="Logic.html#14697" class="Bound"
      >A</a
      ><a name="14715"
      > </a
      ><a name="14716" href="Logic.html#14656" class="Datatype Operator"
      >&#8846;</a
      ><a name="14717"
      > </a
      ><a name="14718" href="Logic.html#14699" class="Bound"
      >B</a
      ><a name="14719"
      >
  </a
      ><a name="14722" href="Logic.html#14722" class="InductiveConstructor"
      >inj&#8322;</a
      ><a name="14726"
      > </a
      ><a name="14727" class="Symbol"
      >:</a
      ><a name="14728"
      > </a
      ><a name="14729" class="Symbol"
      >&#8704;</a
      ><a name="14730"
      > </a
      ><a name="14731" class="Symbol"
      >{</a
      ><a name="14732" href="Logic.html#14732" class="Bound"
      >A</a
      ><a name="14733"
      > </a
      ><a name="14734" href="Logic.html#14734" class="Bound"
      >B</a
      ><a name="14735"
      > </a
      ><a name="14736" class="Symbol"
      >:</a
      ><a name="14737"
      > </a
      ><a name="14738" class="PrimitiveType"
      >Set</a
      ><a name="14741" class="Symbol"
      >}</a
      ><a name="14742"
      > </a
      ><a name="14743" class="Symbol"
      >&#8594;</a
      ><a name="14744"
      > </a
      ><a name="14745" href="Logic.html#14734" class="Bound"
      >B</a
      ><a name="14746"
      > </a
      ><a name="14747" class="Symbol"
      >&#8594;</a
      ><a name="14748"
      > </a
      ><a name="14749" href="Logic.html#14732" class="Bound"
      >A</a
      ><a name="14750"
      > </a
      ><a name="14751" href="Logic.html#14656" class="Datatype Operator"
      >&#8846;</a
      ><a name="14752"
      > </a
      ><a name="14753" href="Logic.html#14734" class="Bound"
      >B</a
      >
{% endraw %}</pre>
Evidence that `A ⊎ B` holds is either of the form
`inj₁ M`, where `M` is evidence that `A` holds, or `inj₂ N`, where
`N` is evidence that `B` holds.

Given evidence that `A → C` and `B → C` both hold, then given
evidence that `A ⊎ B` holds we can conlude that `C` holds.
<pre class="Agda">{% raw %}
<a name="15050" href="Logic.html#15050" class="Function"
      >&#8846;-elim</a
      ><a name="15056"
      > </a
      ><a name="15057" class="Symbol"
      >:</a
      ><a name="15058"
      > </a
      ><a name="15059" class="Symbol"
      >&#8704;</a
      ><a name="15060"
      > </a
      ><a name="15061" class="Symbol"
      >{</a
      ><a name="15062" href="Logic.html#15062" class="Bound"
      >A</a
      ><a name="15063"
      > </a
      ><a name="15064" href="Logic.html#15064" class="Bound"
      >B</a
      ><a name="15065"
      > </a
      ><a name="15066" href="Logic.html#15066" class="Bound"
      >C</a
      ><a name="15067"
      > </a
      ><a name="15068" class="Symbol"
      >:</a
      ><a name="15069"
      > </a
      ><a name="15070" class="PrimitiveType"
      >Set</a
      ><a name="15073" class="Symbol"
      >}</a
      ><a name="15074"
      > </a
      ><a name="15075" class="Symbol"
      >&#8594;</a
      ><a name="15076"
      > </a
      ><a name="15077" class="Symbol"
      >(</a
      ><a name="15078" href="Logic.html#15062" class="Bound"
      >A</a
      ><a name="15079"
      > </a
      ><a name="15080" class="Symbol"
      >&#8594;</a
      ><a name="15081"
      > </a
      ><a name="15082" href="Logic.html#15066" class="Bound"
      >C</a
      ><a name="15083" class="Symbol"
      >)</a
      ><a name="15084"
      > </a
      ><a name="15085" class="Symbol"
      >&#8594;</a
      ><a name="15086"
      > </a
      ><a name="15087" class="Symbol"
      >(</a
      ><a name="15088" href="Logic.html#15064" class="Bound"
      >B</a
      ><a name="15089"
      > </a
      ><a name="15090" class="Symbol"
      >&#8594;</a
      ><a name="15091"
      > </a
      ><a name="15092" href="Logic.html#15066" class="Bound"
      >C</a
      ><a name="15093" class="Symbol"
      >)</a
      ><a name="15094"
      > </a
      ><a name="15095" class="Symbol"
      >&#8594;</a
      ><a name="15096"
      > </a
      ><a name="15097" class="Symbol"
      >(</a
      ><a name="15098" href="Logic.html#15062" class="Bound"
      >A</a
      ><a name="15099"
      > </a
      ><a name="15100" href="Logic.html#14656" class="Datatype Operator"
      >&#8846;</a
      ><a name="15101"
      > </a
      ><a name="15102" href="Logic.html#15064" class="Bound"
      >B</a
      ><a name="15103"
      > </a
      ><a name="15104" class="Symbol"
      >&#8594;</a
      ><a name="15105"
      > </a
      ><a name="15106" href="Logic.html#15066" class="Bound"
      >C</a
      ><a name="15107" class="Symbol"
      >)</a
      ><a name="15108"
      >
</a
      ><a name="15109" href="Logic.html#15050" class="Function"
      >&#8846;-elim</a
      ><a name="15115"
      > </a
      ><a name="15116" href="Logic.html#15116" class="Bound"
      >f</a
      ><a name="15117"
      > </a
      ><a name="15118" href="Logic.html#15118" class="Bound"
      >g</a
      ><a name="15119"
      > </a
      ><a name="15120" class="Symbol"
      >(</a
      ><a name="15121" href="Logic.html#14686" class="InductiveConstructor"
      >inj&#8321;</a
      ><a name="15125"
      > </a
      ><a name="15126" href="Logic.html#15126" class="Bound"
      >x</a
      ><a name="15127" class="Symbol"
      >)</a
      ><a name="15128"
      > </a
      ><a name="15129" class="Symbol"
      >=</a
      ><a name="15130"
      > </a
      ><a name="15131" href="Logic.html#15116" class="Bound"
      >f</a
      ><a name="15132"
      > </a
      ><a name="15133" href="Logic.html#15126" class="Bound"
      >x</a
      ><a name="15134"
      >
</a
      ><a name="15135" href="Logic.html#15050" class="Function"
      >&#8846;-elim</a
      ><a name="15141"
      > </a
      ><a name="15142" href="Logic.html#15142" class="Bound"
      >f</a
      ><a name="15143"
      > </a
      ><a name="15144" href="Logic.html#15144" class="Bound"
      >g</a
      ><a name="15145"
      > </a
      ><a name="15146" class="Symbol"
      >(</a
      ><a name="15147" href="Logic.html#14722" class="InductiveConstructor"
      >inj&#8322;</a
      ><a name="15151"
      > </a
      ><a name="15152" href="Logic.html#15152" class="Bound"
      >y</a
      ><a name="15153" class="Symbol"
      >)</a
      ><a name="15154"
      > </a
      ><a name="15155" class="Symbol"
      >=</a
      ><a name="15156"
      > </a
      ><a name="15157" href="Logic.html#15144" class="Bound"
      >g</a
      ><a name="15158"
      > </a
      ><a name="15159" href="Logic.html#15152" class="Bound"
      >y</a
      >
{% endraw %}</pre>
Pattern matching against `inj₁` and `inj₂` is typical of how we exploit
evidence that a disjunction holds.

We set the precedence of disjunction so that it binds less tightly
than any other declared operator.
<pre class="Agda">{% raw %}
<a name="15394" class="Keyword"
      >infix</a
      ><a name="15399"
      > </a
      ><a name="15400" class="Number"
      >1</a
      ><a name="15401"
      > </a
      ><a name="15402" href="Logic.html#14656" class="Datatype Operator"
      >_&#8846;_</a
      >
{% endraw %}</pre>
Thus, `A × C ⊎ B × C` parses as `(A × C) ⊎ (B × C)`.

Given two types `A` and `B`, we refer to `A ⊎ B` as the
*sum* of `A` and `B`.  In set theory, it is also sometimes
called the *disjoint union*, and in computing it corresponds
to a *variant record* type. Among other reasons for
calling it the sum, note that if type `A` has `m`
distinct members, and type `B` has `n` distinct members,
then the type `A ⊎ B` has `m + n` distinct members.
For instance, consider a type `Bool` with two members, and
a type `Tri` with three members, as defined earlier.
Then the type `Bool ⊎ Tri` has five
members:

    (inj₁ true)     (inj₂ aa)
    (inj₁ false)    (inj₂ bb)
                    (inj₂ cc)

For example, the following function enumerates all
possible arguments of type `Bool ⊎ Tri`:
<pre class="Agda">{% raw %}
<a name="16212" href="Logic.html#16212" class="Function"
      >&#8846;-count</a
      ><a name="16219"
      > </a
      ><a name="16220" class="Symbol"
      >:</a
      ><a name="16221"
      > </a
      ><a name="16222" href="Logic.html#9008" class="Datatype"
      >Bool</a
      ><a name="16226"
      > </a
      ><a name="16227" href="Logic.html#14656" class="Datatype Operator"
      >&#8846;</a
      ><a name="16228"
      > </a
      ><a name="16229" href="Logic.html#9060" class="Datatype"
      >Tri</a
      ><a name="16232"
      > </a
      ><a name="16233" class="Symbol"
      >&#8594;</a
      ><a name="16234"
      > </a
      ><a name="16235" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#97" class="Datatype"
      >&#8469;</a
      ><a name="16236"
      >
</a
      ><a name="16237" href="Logic.html#16212" class="Function"
      >&#8846;-count</a
      ><a name="16244"
      > </a
      ><a name="16245" class="Symbol"
      >(</a
      ><a name="16246" href="Logic.html#14686" class="InductiveConstructor"
      >inj&#8321;</a
      ><a name="16250"
      > </a
      ><a name="16251" href="Logic.html#9027" class="InductiveConstructor"
      >true</a
      ><a name="16255" class="Symbol"
      >)</a
      ><a name="16256"
      >  </a
      ><a name="16258" class="Symbol"
      >=</a
      ><a name="16259"
      > </a
      ><a name="16260" class="Number"
      >1</a
      ><a name="16261"
      >
</a
      ><a name="16262" href="Logic.html#16212" class="Function"
      >&#8846;-count</a
      ><a name="16269"
      > </a
      ><a name="16270" class="Symbol"
      >(</a
      ><a name="16271" href="Logic.html#14686" class="InductiveConstructor"
      >inj&#8321;</a
      ><a name="16275"
      > </a
      ><a name="16276" href="Logic.html#9041" class="InductiveConstructor"
      >false</a
      ><a name="16281" class="Symbol"
      >)</a
      ><a name="16282"
      > </a
      ><a name="16283" class="Symbol"
      >=</a
      ><a name="16284"
      > </a
      ><a name="16285" class="Number"
      >2</a
      ><a name="16286"
      >
</a
      ><a name="16287" href="Logic.html#16212" class="Function"
      >&#8846;-count</a
      ><a name="16294"
      > </a
      ><a name="16295" class="Symbol"
      >(</a
      ><a name="16296" href="Logic.html#14722" class="InductiveConstructor"
      >inj&#8322;</a
      ><a name="16300"
      > </a
      ><a name="16301" href="Logic.html#9078" class="InductiveConstructor"
      >aa</a
      ><a name="16303" class="Symbol"
      >)</a
      ><a name="16304"
      >    </a
      ><a name="16308" class="Symbol"
      >=</a
      ><a name="16309"
      > </a
      ><a name="16310" class="Number"
      >3</a
      ><a name="16311"
      >
</a
      ><a name="16312" href="Logic.html#16212" class="Function"
      >&#8846;-count</a
      ><a name="16319"
      > </a
      ><a name="16320" class="Symbol"
      >(</a
      ><a name="16321" href="Logic.html#14722" class="InductiveConstructor"
      >inj&#8322;</a
      ><a name="16325"
      > </a
      ><a name="16326" href="Logic.html#9089" class="InductiveConstructor"
      >bb</a
      ><a name="16328" class="Symbol"
      >)</a
      ><a name="16329"
      >    </a
      ><a name="16333" class="Symbol"
      >=</a
      ><a name="16334"
      > </a
      ><a name="16335" class="Number"
      >4</a
      ><a name="16336"
      >
</a
      ><a name="16337" href="Logic.html#16212" class="Function"
      >&#8846;-count</a
      ><a name="16344"
      > </a
      ><a name="16345" class="Symbol"
      >(</a
      ><a name="16346" href="Logic.html#14722" class="InductiveConstructor"
      >inj&#8322;</a
      ><a name="16350"
      > </a
      ><a name="16351" href="Logic.html#9100" class="InductiveConstructor"
      >cc</a
      ><a name="16353" class="Symbol"
      >)</a
      ><a name="16354"
      >    </a
      ><a name="16358" class="Symbol"
      >=</a
      ><a name="16359"
      > </a
      ><a name="16360" class="Number"
      >5</a
      >
{% endraw %}</pre>

Sum on types also shares a property with sum on numbers in that it is
commutative and associative *up to isomorphism*.

For commutativity, the `to` function swaps the two constructors,
taking `inj₁ x` to `inj₂ x`, and `inj₂ y` to `inj₁ y`; and the `fro`
function does the same (up to renaming). Replacing the definition of
`invˡ` by `λ w → refl` will not work; and similarly for `invʳ`, which
does the same (up to renaming).
<pre class="Agda">{% raw %}
<a name="16812" href="Logic.html#16812" class="Function"
      >&#8846;-comm</a
      ><a name="16818"
      > </a
      ><a name="16819" class="Symbol"
      >:</a
      ><a name="16820"
      > </a
      ><a name="16821" class="Symbol"
      >&#8704;</a
      ><a name="16822"
      > </a
      ><a name="16823" class="Symbol"
      >{</a
      ><a name="16824" href="Logic.html#16824" class="Bound"
      >A</a
      ><a name="16825"
      > </a
      ><a name="16826" href="Logic.html#16826" class="Bound"
      >B</a
      ><a name="16827"
      > </a
      ><a name="16828" class="Symbol"
      >:</a
      ><a name="16829"
      > </a
      ><a name="16830" class="PrimitiveType"
      >Set</a
      ><a name="16833" class="Symbol"
      >}</a
      ><a name="16834"
      > </a
      ><a name="16835" class="Symbol"
      >&#8594;</a
      ><a name="16836"
      > </a
      ><a name="16837" class="Symbol"
      >(</a
      ><a name="16838" href="Logic.html#16824" class="Bound"
      >A</a
      ><a name="16839"
      > </a
      ><a name="16840" href="Logic.html#14656" class="Datatype Operator"
      >&#8846;</a
      ><a name="16841"
      > </a
      ><a name="16842" href="Logic.html#16826" class="Bound"
      >B</a
      ><a name="16843" class="Symbol"
      >)</a
      ><a name="16844"
      > </a
      ><a name="16845" href="Logic.html#1478" class="Record Operator"
      >&#8771;</a
      ><a name="16846"
      > </a
      ><a name="16847" class="Symbol"
      >(</a
      ><a name="16848" href="Logic.html#16826" class="Bound"
      >B</a
      ><a name="16849"
      > </a
      ><a name="16850" href="Logic.html#14656" class="Datatype Operator"
      >&#8846;</a
      ><a name="16851"
      > </a
      ><a name="16852" href="Logic.html#16824" class="Bound"
      >A</a
      ><a name="16853" class="Symbol"
      >)</a
      ><a name="16854"
      >
</a
      ><a name="16855" href="Logic.html#16812" class="Function"
      >&#8846;-comm</a
      ><a name="16861"
      > </a
      ><a name="16862" class="Symbol"
      >=</a
      ><a name="16863"
      > </a
      ><a name="16864" class="Keyword"
      >record</a
      ><a name="16870"
      >
  </a
      ><a name="16873" class="Symbol"
      >{</a
      ><a name="16874"
      > </a
      ><a name="16875" class="Field"
      >to</a
      ><a name="16877"
      >   </a
      ><a name="16880" class="Symbol"
      >=</a
      ><a name="16881"
      > </a
      ><a name="16882" class="Symbol"
      >&#955;</a
      ><a name="16883"
      > </a
      ><a name="16884" class="Symbol"
      >{</a
      ><a name="16885"
      > </a
      ><a name="16886" class="Symbol"
      >(</a
      ><a name="16887" href="Logic.html#14686" class="InductiveConstructor"
      >inj&#8321;</a
      ><a name="16891"
      > </a
      ><a name="16892" href="Logic.html#16892" class="Bound"
      >x</a
      ><a name="16893" class="Symbol"
      >)</a
      ><a name="16894"
      > </a
      ><a name="16895" class="Symbol"
      >&#8594;</a
      ><a name="16896"
      > </a
      ><a name="16897" class="Symbol"
      >(</a
      ><a name="16898" href="Logic.html#14722" class="InductiveConstructor"
      >inj&#8322;</a
      ><a name="16902"
      > </a
      ><a name="16903" href="Logic.html#16892" class="Bound"
      >x</a
      ><a name="16904" class="Symbol"
      >)</a
      ><a name="16905"
      >
             </a
      ><a name="16919" class="Symbol"
      >;</a
      ><a name="16920"
      > </a
      ><a name="16921" class="Symbol"
      >(</a
      ><a name="16922" href="Logic.html#14722" class="InductiveConstructor"
      >inj&#8322;</a
      ><a name="16926"
      > </a
      ><a name="16927" href="Logic.html#16927" class="Bound"
      >y</a
      ><a name="16928" class="Symbol"
      >)</a
      ><a name="16929"
      > </a
      ><a name="16930" class="Symbol"
      >&#8594;</a
      ><a name="16931"
      > </a
      ><a name="16932" class="Symbol"
      >(</a
      ><a name="16933" href="Logic.html#14686" class="InductiveConstructor"
      >inj&#8321;</a
      ><a name="16937"
      > </a
      ><a name="16938" href="Logic.html#16927" class="Bound"
      >y</a
      ><a name="16939" class="Symbol"
      >)</a
      ><a name="16940"
      >
             </a
      ><a name="16954" class="Symbol"
      >}</a
      ><a name="16955"
      >
  </a
      ><a name="16958" class="Symbol"
      >;</a
      ><a name="16959"
      > </a
      ><a name="16960" class="Field"
      >fro</a
      ><a name="16963"
      >  </a
      ><a name="16965" class="Symbol"
      >=</a
      ><a name="16966"
      > </a
      ><a name="16967" class="Symbol"
      >&#955;</a
      ><a name="16968"
      > </a
      ><a name="16969" class="Symbol"
      >{</a
      ><a name="16970"
      > </a
      ><a name="16971" class="Symbol"
      >(</a
      ><a name="16972" href="Logic.html#14686" class="InductiveConstructor"
      >inj&#8321;</a
      ><a name="16976"
      > </a
      ><a name="16977" href="Logic.html#16977" class="Bound"
      >y</a
      ><a name="16978" class="Symbol"
      >)</a
      ><a name="16979"
      > </a
      ><a name="16980" class="Symbol"
      >&#8594;</a
      ><a name="16981"
      > </a
      ><a name="16982" class="Symbol"
      >(</a
      ><a name="16983" href="Logic.html#14722" class="InductiveConstructor"
      >inj&#8322;</a
      ><a name="16987"
      > </a
      ><a name="16988" href="Logic.html#16977" class="Bound"
      >y</a
      ><a name="16989" class="Symbol"
      >)</a
      ><a name="16990"
      >
             </a
      ><a name="17004" class="Symbol"
      >;</a
      ><a name="17005"
      > </a
      ><a name="17006" class="Symbol"
      >(</a
      ><a name="17007" href="Logic.html#14722" class="InductiveConstructor"
      >inj&#8322;</a
      ><a name="17011"
      > </a
      ><a name="17012" href="Logic.html#17012" class="Bound"
      >x</a
      ><a name="17013" class="Symbol"
      >)</a
      ><a name="17014"
      > </a
      ><a name="17015" class="Symbol"
      >&#8594;</a
      ><a name="17016"
      > </a
      ><a name="17017" class="Symbol"
      >(</a
      ><a name="17018" href="Logic.html#14686" class="InductiveConstructor"
      >inj&#8321;</a
      ><a name="17022"
      > </a
      ><a name="17023" href="Logic.html#17012" class="Bound"
      >x</a
      ><a name="17024" class="Symbol"
      >)</a
      ><a name="17025"
      >
             </a
      ><a name="17039" class="Symbol"
      >}</a
      ><a name="17040"
      >
  </a
      ><a name="17043" class="Symbol"
      >;</a
      ><a name="17044"
      > </a
      ><a name="17045" class="Field"
      >inv&#737;</a
      ><a name="17049"
      > </a
      ><a name="17050" class="Symbol"
      >=</a
      ><a name="17051"
      > </a
      ><a name="17052" class="Symbol"
      >&#955;</a
      ><a name="17053"
      > </a
      ><a name="17054" class="Symbol"
      >{</a
      ><a name="17055"
      > </a
      ><a name="17056" class="Symbol"
      >(</a
      ><a name="17057" href="Logic.html#14686" class="InductiveConstructor"
      >inj&#8321;</a
      ><a name="17061"
      > </a
      ><a name="17062" href="Logic.html#17062" class="Bound"
      >x</a
      ><a name="17063" class="Symbol"
      >)</a
      ><a name="17064"
      > </a
      ><a name="17065" class="Symbol"
      >&#8594;</a
      ><a name="17066"
      > </a
      ><a name="17067" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="17071"
      >
             </a
      ><a name="17085" class="Symbol"
      >;</a
      ><a name="17086"
      > </a
      ><a name="17087" class="Symbol"
      >(</a
      ><a name="17088" href="Logic.html#14722" class="InductiveConstructor"
      >inj&#8322;</a
      ><a name="17092"
      > </a
      ><a name="17093" href="Logic.html#17093" class="Bound"
      >y</a
      ><a name="17094" class="Symbol"
      >)</a
      ><a name="17095"
      > </a
      ><a name="17096" class="Symbol"
      >&#8594;</a
      ><a name="17097"
      > </a
      ><a name="17098" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="17102"
      >
             </a
      ><a name="17116" class="Symbol"
      >}</a
      ><a name="17117"
      >
  </a
      ><a name="17120" class="Symbol"
      >;</a
      ><a name="17121"
      > </a
      ><a name="17122" class="Field"
      >inv&#691;</a
      ><a name="17126"
      > </a
      ><a name="17127" class="Symbol"
      >=</a
      ><a name="17128"
      > </a
      ><a name="17129" class="Symbol"
      >&#955;</a
      ><a name="17130"
      > </a
      ><a name="17131" class="Symbol"
      >{</a
      ><a name="17132"
      > </a
      ><a name="17133" class="Symbol"
      >(</a
      ><a name="17134" href="Logic.html#14686" class="InductiveConstructor"
      >inj&#8321;</a
      ><a name="17138"
      > </a
      ><a name="17139" href="Logic.html#17139" class="Bound"
      >y</a
      ><a name="17140" class="Symbol"
      >)</a
      ><a name="17141"
      > </a
      ><a name="17142" class="Symbol"
      >&#8594;</a
      ><a name="17143"
      > </a
      ><a name="17144" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="17148"
      >
             </a
      ><a name="17162" class="Symbol"
      >;</a
      ><a name="17163"
      > </a
      ><a name="17164" class="Symbol"
      >(</a
      ><a name="17165" href="Logic.html#14722" class="InductiveConstructor"
      >inj&#8322;</a
      ><a name="17169"
      > </a
      ><a name="17170" href="Logic.html#17170" class="Bound"
      >x</a
      ><a name="17171" class="Symbol"
      >)</a
      ><a name="17172"
      > </a
      ><a name="17173" class="Symbol"
      >&#8594;</a
      ><a name="17174"
      > </a
      ><a name="17175" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="17179"
      >
             </a
      ><a name="17193" class="Symbol"
      >}</a
      ><a name="17194"
      >
  </a
      ><a name="17197" class="Symbol"
      >}</a
      >
{% endraw %}</pre>
Being *commutative* is different from being *commutative up to
isomorphism*.  Compare the two statements:

    m + n ≡ n + m
    A ⊎ B ≃ B ⊎ A

In the first case, we might have that `m` is `2` and `n` is `3`, and
both `m + n` and `n + m` are equal to `5`.  In the second case, we
might have that `A` is `Bool` and `B` is `Tri`, and `Bool ⊎ Tri` is
*not* the same as `Tri ⊎ Bool`.  But there is an isomorphism between
the two types.  For instance, `inj₁ true`, which is a member of the
former, corresponds to `inj₂ true`, which is a member of the latter.

For associativity, the `to` function reassociates, and the `fro` function does
the inverse.  Again, the evidence of left and right inverse requires
matching against a suitable pattern to enable simplificition.
<pre class="Agda">{% raw %}
<a name="17988" href="Logic.html#17988" class="Function"
      >&#8846;-assoc</a
      ><a name="17995"
      > </a
      ><a name="17996" class="Symbol"
      >:</a
      ><a name="17997"
      > </a
      ><a name="17998" class="Symbol"
      >&#8704;</a
      ><a name="17999"
      > </a
      ><a name="18000" class="Symbol"
      >{</a
      ><a name="18001" href="Logic.html#18001" class="Bound"
      >A</a
      ><a name="18002"
      > </a
      ><a name="18003" href="Logic.html#18003" class="Bound"
      >B</a
      ><a name="18004"
      > </a
      ><a name="18005" href="Logic.html#18005" class="Bound"
      >C</a
      ><a name="18006"
      > </a
      ><a name="18007" class="Symbol"
      >:</a
      ><a name="18008"
      > </a
      ><a name="18009" class="PrimitiveType"
      >Set</a
      ><a name="18012" class="Symbol"
      >}</a
      ><a name="18013"
      > </a
      ><a name="18014" class="Symbol"
      >&#8594;</a
      ><a name="18015"
      > </a
      ><a name="18016" class="Symbol"
      >((</a
      ><a name="18018" href="Logic.html#18001" class="Bound"
      >A</a
      ><a name="18019"
      > </a
      ><a name="18020" href="Logic.html#14656" class="Datatype Operator"
      >&#8846;</a
      ><a name="18021"
      > </a
      ><a name="18022" href="Logic.html#18003" class="Bound"
      >B</a
      ><a name="18023" class="Symbol"
      >)</a
      ><a name="18024"
      > </a
      ><a name="18025" href="Logic.html#14656" class="Datatype Operator"
      >&#8846;</a
      ><a name="18026"
      > </a
      ><a name="18027" href="Logic.html#18005" class="Bound"
      >C</a
      ><a name="18028" class="Symbol"
      >)</a
      ><a name="18029"
      > </a
      ><a name="18030" href="Logic.html#1478" class="Record Operator"
      >&#8771;</a
      ><a name="18031"
      > </a
      ><a name="18032" class="Symbol"
      >(</a
      ><a name="18033" href="Logic.html#18001" class="Bound"
      >A</a
      ><a name="18034"
      > </a
      ><a name="18035" href="Logic.html#14656" class="Datatype Operator"
      >&#8846;</a
      ><a name="18036"
      > </a
      ><a name="18037" class="Symbol"
      >(</a
      ><a name="18038" href="Logic.html#18003" class="Bound"
      >B</a
      ><a name="18039"
      > </a
      ><a name="18040" href="Logic.html#14656" class="Datatype Operator"
      >&#8846;</a
      ><a name="18041"
      > </a
      ><a name="18042" href="Logic.html#18005" class="Bound"
      >C</a
      ><a name="18043" class="Symbol"
      >))</a
      ><a name="18045"
      >
</a
      ><a name="18046" href="Logic.html#17988" class="Function"
      >&#8846;-assoc</a
      ><a name="18053"
      > </a
      ><a name="18054" class="Symbol"
      >=</a
      ><a name="18055"
      > </a
      ><a name="18056" class="Keyword"
      >record</a
      ><a name="18062"
      >
  </a
      ><a name="18065" class="Symbol"
      >{</a
      ><a name="18066"
      > </a
      ><a name="18067" class="Field"
      >to</a
      ><a name="18069"
      >   </a
      ><a name="18072" class="Symbol"
      >=</a
      ><a name="18073"
      > </a
      ><a name="18074" class="Symbol"
      >&#955;</a
      ><a name="18075"
      > </a
      ><a name="18076" class="Symbol"
      >{</a
      ><a name="18077"
      > </a
      ><a name="18078" class="Symbol"
      >(</a
      ><a name="18079" href="Logic.html#14686" class="InductiveConstructor"
      >inj&#8321;</a
      ><a name="18083"
      > </a
      ><a name="18084" class="Symbol"
      >(</a
      ><a name="18085" href="Logic.html#14686" class="InductiveConstructor"
      >inj&#8321;</a
      ><a name="18089"
      > </a
      ><a name="18090" href="Logic.html#18090" class="Bound"
      >x</a
      ><a name="18091" class="Symbol"
      >))</a
      ><a name="18093"
      > </a
      ><a name="18094" class="Symbol"
      >&#8594;</a
      ><a name="18095"
      > </a
      ><a name="18096" class="Symbol"
      >(</a
      ><a name="18097" href="Logic.html#14686" class="InductiveConstructor"
      >inj&#8321;</a
      ><a name="18101"
      > </a
      ><a name="18102" href="Logic.html#18090" class="Bound"
      >x</a
      ><a name="18103" class="Symbol"
      >)</a
      ><a name="18104"
      >
             </a
      ><a name="18118" class="Symbol"
      >;</a
      ><a name="18119"
      > </a
      ><a name="18120" class="Symbol"
      >(</a
      ><a name="18121" href="Logic.html#14686" class="InductiveConstructor"
      >inj&#8321;</a
      ><a name="18125"
      > </a
      ><a name="18126" class="Symbol"
      >(</a
      ><a name="18127" href="Logic.html#14722" class="InductiveConstructor"
      >inj&#8322;</a
      ><a name="18131"
      > </a
      ><a name="18132" href="Logic.html#18132" class="Bound"
      >y</a
      ><a name="18133" class="Symbol"
      >))</a
      ><a name="18135"
      > </a
      ><a name="18136" class="Symbol"
      >&#8594;</a
      ><a name="18137"
      > </a
      ><a name="18138" class="Symbol"
      >(</a
      ><a name="18139" href="Logic.html#14722" class="InductiveConstructor"
      >inj&#8322;</a
      ><a name="18143"
      > </a
      ><a name="18144" class="Symbol"
      >(</a
      ><a name="18145" href="Logic.html#14686" class="InductiveConstructor"
      >inj&#8321;</a
      ><a name="18149"
      > </a
      ><a name="18150" href="Logic.html#18132" class="Bound"
      >y</a
      ><a name="18151" class="Symbol"
      >))</a
      ><a name="18153"
      >
             </a
      ><a name="18167" class="Symbol"
      >;</a
      ><a name="18168"
      > </a
      ><a name="18169" class="Symbol"
      >(</a
      ><a name="18170" href="Logic.html#14722" class="InductiveConstructor"
      >inj&#8322;</a
      ><a name="18174"
      > </a
      ><a name="18175" href="Logic.html#18175" class="Bound"
      >z</a
      ><a name="18176" class="Symbol"
      >)</a
      ><a name="18177"
      >        </a
      ><a name="18185" class="Symbol"
      >&#8594;</a
      ><a name="18186"
      > </a
      ><a name="18187" class="Symbol"
      >(</a
      ><a name="18188" href="Logic.html#14722" class="InductiveConstructor"
      >inj&#8322;</a
      ><a name="18192"
      > </a
      ><a name="18193" class="Symbol"
      >(</a
      ><a name="18194" href="Logic.html#14722" class="InductiveConstructor"
      >inj&#8322;</a
      ><a name="18198"
      > </a
      ><a name="18199" href="Logic.html#18175" class="Bound"
      >z</a
      ><a name="18200" class="Symbol"
      >))</a
      ><a name="18202"
      >
             </a
      ><a name="18216" class="Symbol"
      >}</a
      ><a name="18217"
      >
  </a
      ><a name="18220" class="Symbol"
      >;</a
      ><a name="18221"
      > </a
      ><a name="18222" class="Field"
      >fro</a
      ><a name="18225"
      >  </a
      ><a name="18227" class="Symbol"
      >=</a
      ><a name="18228"
      > </a
      ><a name="18229" class="Symbol"
      >&#955;</a
      ><a name="18230"
      > </a
      ><a name="18231" class="Symbol"
      >{</a
      ><a name="18232"
      > </a
      ><a name="18233" class="Symbol"
      >(</a
      ><a name="18234" href="Logic.html#14686" class="InductiveConstructor"
      >inj&#8321;</a
      ><a name="18238"
      > </a
      ><a name="18239" href="Logic.html#18239" class="Bound"
      >x</a
      ><a name="18240" class="Symbol"
      >)</a
      ><a name="18241"
      >        </a
      ><a name="18249" class="Symbol"
      >&#8594;</a
      ><a name="18250"
      > </a
      ><a name="18251" class="Symbol"
      >(</a
      ><a name="18252" href="Logic.html#14686" class="InductiveConstructor"
      >inj&#8321;</a
      ><a name="18256"
      > </a
      ><a name="18257" class="Symbol"
      >(</a
      ><a name="18258" href="Logic.html#14686" class="InductiveConstructor"
      >inj&#8321;</a
      ><a name="18262"
      > </a
      ><a name="18263" href="Logic.html#18239" class="Bound"
      >x</a
      ><a name="18264" class="Symbol"
      >))</a
      ><a name="18266"
      >
             </a
      ><a name="18280" class="Symbol"
      >;</a
      ><a name="18281"
      > </a
      ><a name="18282" class="Symbol"
      >(</a
      ><a name="18283" href="Logic.html#14722" class="InductiveConstructor"
      >inj&#8322;</a
      ><a name="18287"
      > </a
      ><a name="18288" class="Symbol"
      >(</a
      ><a name="18289" href="Logic.html#14686" class="InductiveConstructor"
      >inj&#8321;</a
      ><a name="18293"
      > </a
      ><a name="18294" href="Logic.html#18294" class="Bound"
      >y</a
      ><a name="18295" class="Symbol"
      >))</a
      ><a name="18297"
      > </a
      ><a name="18298" class="Symbol"
      >&#8594;</a
      ><a name="18299"
      > </a
      ><a name="18300" class="Symbol"
      >(</a
      ><a name="18301" href="Logic.html#14686" class="InductiveConstructor"
      >inj&#8321;</a
      ><a name="18305"
      > </a
      ><a name="18306" class="Symbol"
      >(</a
      ><a name="18307" href="Logic.html#14722" class="InductiveConstructor"
      >inj&#8322;</a
      ><a name="18311"
      > </a
      ><a name="18312" href="Logic.html#18294" class="Bound"
      >y</a
      ><a name="18313" class="Symbol"
      >))</a
      ><a name="18315"
      >
             </a
      ><a name="18329" class="Symbol"
      >;</a
      ><a name="18330"
      > </a
      ><a name="18331" class="Symbol"
      >(</a
      ><a name="18332" href="Logic.html#14722" class="InductiveConstructor"
      >inj&#8322;</a
      ><a name="18336"
      > </a
      ><a name="18337" class="Symbol"
      >(</a
      ><a name="18338" href="Logic.html#14722" class="InductiveConstructor"
      >inj&#8322;</a
      ><a name="18342"
      > </a
      ><a name="18343" href="Logic.html#18343" class="Bound"
      >z</a
      ><a name="18344" class="Symbol"
      >))</a
      ><a name="18346"
      > </a
      ><a name="18347" class="Symbol"
      >&#8594;</a
      ><a name="18348"
      > </a
      ><a name="18349" class="Symbol"
      >(</a
      ><a name="18350" href="Logic.html#14722" class="InductiveConstructor"
      >inj&#8322;</a
      ><a name="18354"
      > </a
      ><a name="18355" href="Logic.html#18343" class="Bound"
      >z</a
      ><a name="18356" class="Symbol"
      >)</a
      ><a name="18357"
      >
             </a
      ><a name="18371" class="Symbol"
      >}</a
      ><a name="18372"
      >
  </a
      ><a name="18375" class="Symbol"
      >;</a
      ><a name="18376"
      > </a
      ><a name="18377" class="Field"
      >inv&#737;</a
      ><a name="18381"
      > </a
      ><a name="18382" class="Symbol"
      >=</a
      ><a name="18383"
      > </a
      ><a name="18384" class="Symbol"
      >&#955;</a
      ><a name="18385"
      > </a
      ><a name="18386" class="Symbol"
      >{</a
      ><a name="18387"
      > </a
      ><a name="18388" class="Symbol"
      >(</a
      ><a name="18389" href="Logic.html#14686" class="InductiveConstructor"
      >inj&#8321;</a
      ><a name="18393"
      > </a
      ><a name="18394" class="Symbol"
      >(</a
      ><a name="18395" href="Logic.html#14686" class="InductiveConstructor"
      >inj&#8321;</a
      ><a name="18399"
      > </a
      ><a name="18400" href="Logic.html#18400" class="Bound"
      >x</a
      ><a name="18401" class="Symbol"
      >))</a
      ><a name="18403"
      > </a
      ><a name="18404" class="Symbol"
      >&#8594;</a
      ><a name="18405"
      > </a
      ><a name="18406" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="18410"
      >
             </a
      ><a name="18424" class="Symbol"
      >;</a
      ><a name="18425"
      > </a
      ><a name="18426" class="Symbol"
      >(</a
      ><a name="18427" href="Logic.html#14686" class="InductiveConstructor"
      >inj&#8321;</a
      ><a name="18431"
      > </a
      ><a name="18432" class="Symbol"
      >(</a
      ><a name="18433" href="Logic.html#14722" class="InductiveConstructor"
      >inj&#8322;</a
      ><a name="18437"
      > </a
      ><a name="18438" href="Logic.html#18438" class="Bound"
      >y</a
      ><a name="18439" class="Symbol"
      >))</a
      ><a name="18441"
      > </a
      ><a name="18442" class="Symbol"
      >&#8594;</a
      ><a name="18443"
      > </a
      ><a name="18444" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="18448"
      >
             </a
      ><a name="18462" class="Symbol"
      >;</a
      ><a name="18463"
      > </a
      ><a name="18464" class="Symbol"
      >(</a
      ><a name="18465" href="Logic.html#14722" class="InductiveConstructor"
      >inj&#8322;</a
      ><a name="18469"
      > </a
      ><a name="18470" href="Logic.html#18470" class="Bound"
      >z</a
      ><a name="18471" class="Symbol"
      >)</a
      ><a name="18472"
      >        </a
      ><a name="18480" class="Symbol"
      >&#8594;</a
      ><a name="18481"
      > </a
      ><a name="18482" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="18486"
      >
             </a
      ><a name="18500" class="Symbol"
      >}</a
      ><a name="18501"
      >
  </a
      ><a name="18504" class="Symbol"
      >;</a
      ><a name="18505"
      > </a
      ><a name="18506" class="Field"
      >inv&#691;</a
      ><a name="18510"
      > </a
      ><a name="18511" class="Symbol"
      >=</a
      ><a name="18512"
      > </a
      ><a name="18513" class="Symbol"
      >&#955;</a
      ><a name="18514"
      > </a
      ><a name="18515" class="Symbol"
      >{</a
      ><a name="18516"
      > </a
      ><a name="18517" class="Symbol"
      >(</a
      ><a name="18518" href="Logic.html#14686" class="InductiveConstructor"
      >inj&#8321;</a
      ><a name="18522"
      > </a
      ><a name="18523" href="Logic.html#18523" class="Bound"
      >x</a
      ><a name="18524" class="Symbol"
      >)</a
      ><a name="18525"
      >        </a
      ><a name="18533" class="Symbol"
      >&#8594;</a
      ><a name="18534"
      > </a
      ><a name="18535" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="18539"
      >
             </a
      ><a name="18553" class="Symbol"
      >;</a
      ><a name="18554"
      > </a
      ><a name="18555" class="Symbol"
      >(</a
      ><a name="18556" href="Logic.html#14722" class="InductiveConstructor"
      >inj&#8322;</a
      ><a name="18560"
      > </a
      ><a name="18561" class="Symbol"
      >(</a
      ><a name="18562" href="Logic.html#14686" class="InductiveConstructor"
      >inj&#8321;</a
      ><a name="18566"
      > </a
      ><a name="18567" href="Logic.html#18567" class="Bound"
      >y</a
      ><a name="18568" class="Symbol"
      >))</a
      ><a name="18570"
      > </a
      ><a name="18571" class="Symbol"
      >&#8594;</a
      ><a name="18572"
      > </a
      ><a name="18573" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="18577"
      >
             </a
      ><a name="18591" class="Symbol"
      >;</a
      ><a name="18592"
      > </a
      ><a name="18593" class="Symbol"
      >(</a
      ><a name="18594" href="Logic.html#14722" class="InductiveConstructor"
      >inj&#8322;</a
      ><a name="18598"
      > </a
      ><a name="18599" class="Symbol"
      >(</a
      ><a name="18600" href="Logic.html#14722" class="InductiveConstructor"
      >inj&#8322;</a
      ><a name="18604"
      > </a
      ><a name="18605" href="Logic.html#18605" class="Bound"
      >z</a
      ><a name="18606" class="Symbol"
      >))</a
      ><a name="18608"
      > </a
      ><a name="18609" class="Symbol"
      >&#8594;</a
      ><a name="18610"
      > </a
      ><a name="18611" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="18615"
      >
             </a
      ><a name="18629" class="Symbol"
      >}</a
      ><a name="18630"
      >
  </a
      ><a name="18633" class="Symbol"
      >}</a
      >
{% endraw %}</pre>

Again, being *associative* is not the same as being *associative
up to isomorphism*.  For example, the type `(ℕ + Bool) + Tri`
is *not* the same as `ℕ + (Bool + Tri)`. But there is an
isomorphism between the two types. For instance `inj₂ (inj₁ true)`,
which is a member of the former, corresponds to `inj₁ (inj₂ true)`,
which is a member of the latter.

Here we have used lambda-expressions with pattern matching
and multiple cases. For instance, the term

    λ { (inj₁ x) → (inj₂ x)
      ; (inj₂ y) → (inj₁ y)
      }

corresponds to the function `k`, where `k` is defined by
<pre class="Agda">{% raw %}
<a name="19239" href="Logic.html#19239" class="Function"
      >k</a
      ><a name="19240"
      > </a
      ><a name="19241" class="Symbol"
      >:</a
      ><a name="19242"
      > </a
      ><a name="19243" class="Symbol"
      >&#8704;</a
      ><a name="19244"
      > </a
      ><a name="19245" class="Symbol"
      >{</a
      ><a name="19246" href="Logic.html#19246" class="Bound"
      >A</a
      ><a name="19247"
      > </a
      ><a name="19248" href="Logic.html#19248" class="Bound"
      >B</a
      ><a name="19249"
      > </a
      ><a name="19250" class="Symbol"
      >:</a
      ><a name="19251"
      > </a
      ><a name="19252" class="PrimitiveType"
      >Set</a
      ><a name="19255" class="Symbol"
      >}</a
      ><a name="19256"
      > </a
      ><a name="19257" class="Symbol"
      >&#8594;</a
      ><a name="19258"
      > </a
      ><a name="19259" href="Logic.html#19246" class="Bound"
      >A</a
      ><a name="19260"
      > </a
      ><a name="19261" href="Logic.html#14656" class="Datatype Operator"
      >&#8846;</a
      ><a name="19262"
      > </a
      ><a name="19263" href="Logic.html#19248" class="Bound"
      >B</a
      ><a name="19264"
      > </a
      ><a name="19265" class="Symbol"
      >&#8594;</a
      ><a name="19266"
      > </a
      ><a name="19267" href="Logic.html#19248" class="Bound"
      >B</a
      ><a name="19268"
      > </a
      ><a name="19269" href="Logic.html#14656" class="Datatype Operator"
      >&#8846;</a
      ><a name="19270"
      > </a
      ><a name="19271" href="Logic.html#19246" class="Bound"
      >A</a
      ><a name="19272"
      >
</a
      ><a name="19273" href="Logic.html#19239" class="Function"
      >k</a
      ><a name="19274"
      > </a
      ><a name="19275" class="Symbol"
      >(</a
      ><a name="19276" href="Logic.html#14686" class="InductiveConstructor"
      >inj&#8321;</a
      ><a name="19280"
      > </a
      ><a name="19281" href="Logic.html#19281" class="Bound"
      >x</a
      ><a name="19282" class="Symbol"
      >)</a
      ><a name="19283"
      > </a
      ><a name="19284" class="Symbol"
      >=</a
      ><a name="19285"
      > </a
      ><a name="19286" href="Logic.html#14722" class="InductiveConstructor"
      >inj&#8322;</a
      ><a name="19290"
      > </a
      ><a name="19291" href="Logic.html#19281" class="Bound"
      >x</a
      ><a name="19292"
      >
</a
      ><a name="19293" href="Logic.html#19239" class="Function"
      >k</a
      ><a name="19294"
      > </a
      ><a name="19295" class="Symbol"
      >(</a
      ><a name="19296" href="Logic.html#14722" class="InductiveConstructor"
      >inj&#8322;</a
      ><a name="19300"
      > </a
      ><a name="19301" href="Logic.html#19301" class="Bound"
      >y</a
      ><a name="19302" class="Symbol"
      >)</a
      ><a name="19303"
      > </a
      ><a name="19304" class="Symbol"
      >=</a
      ><a name="19305"
      > </a
      ><a name="19306" href="Logic.html#14686" class="InductiveConstructor"
      >inj&#8321;</a
      ><a name="19310"
      > </a
      ><a name="19311" href="Logic.html#19301" class="Bound"
      >y</a
      >
{% endraw %}</pre>


## False is empty

False `⊥` never holds.  We formalise this idea by declaring
a suitable inductive type.
<pre class="Agda">{% raw %}
<a name="19445" class="Keyword"
      >data</a
      ><a name="19449"
      > </a
      ><a name="19450" href="Logic.html#19450" class="Datatype"
      >&#8869;</a
      ><a name="19451"
      > </a
      ><a name="19452" class="Symbol"
      >:</a
      ><a name="19453"
      > </a
      ><a name="19454" class="PrimitiveType"
      >Set</a
      ><a name="19457"
      > </a
      ><a name="19458" class="Keyword"
      >where</a
      ><a name="19463"
      >
  </a
      ><a name="19466" class="Comment"
      >-- no clauses!</a
      >
{% endraw %}</pre>
There is no possible evidence that `⊥` holds.

Given evidence that `⊥` holds, we might conclude anything!  Since
false never holds, knowing that it holds tells us we are in a
paradoxical situation.

is a basic principle of logic, known in medieval times by the
latin phrase *ex falso*, and known to children through phrases
such as "if pigs had wings, then I'd be the Queen of Sheba".
<pre class="Agda">{% raw %}
<a name="19890" href="Logic.html#19890" class="Function"
      >&#8869;-elim</a
      ><a name="19896"
      > </a
      ><a name="19897" class="Symbol"
      >:</a
      ><a name="19898"
      > </a
      ><a name="19899" class="Symbol"
      >&#8704;</a
      ><a name="19900"
      > </a
      ><a name="19901" class="Symbol"
      >{</a
      ><a name="19902" href="Logic.html#19902" class="Bound"
      >A</a
      ><a name="19903"
      > </a
      ><a name="19904" class="Symbol"
      >:</a
      ><a name="19905"
      > </a
      ><a name="19906" class="PrimitiveType"
      >Set</a
      ><a name="19909" class="Symbol"
      >}</a
      ><a name="19910"
      > </a
      ><a name="19911" class="Symbol"
      >&#8594;</a
      ><a name="19912"
      > </a
      ><a name="19913" href="Logic.html#19450" class="Datatype"
      >&#8869;</a
      ><a name="19914"
      > </a
      ><a name="19915" class="Symbol"
      >&#8594;</a
      ><a name="19916"
      > </a
      ><a name="19917" href="Logic.html#19902" class="Bound"
      >A</a
      ><a name="19918"
      >
</a
      ><a name="19919" href="Logic.html#19890" class="Function"
      >&#8869;-elim</a
      ><a name="19925"
      > </a
      ><a name="19926" class="Symbol"
      >()</a
      >
{% endraw %}</pre>
Here since `⊥` is a type with no members, we indicate that it is
*never* possible to match against a value of this type by using
the pattern `()`.  In medieval times, this rule was know by the
latin name *ex falso*.  It is also known to children by phrases
such as "If pigs had wings then I'd be the Queen of Sheba".

We refer to `⊥` as *the empty type* or just *empty*. And, indeed,
type `⊥` has no members. For example, the following function
enumerates all possible arguments of type `⊥`:
<pre class="Agda">{% raw %}
<a name="20445" href="Logic.html#20445" class="Function"
      >&#8869;-count</a
      ><a name="20452"
      > </a
      ><a name="20453" class="Symbol"
      >:</a
      ><a name="20454"
      > </a
      ><a name="20455" href="Logic.html#19450" class="Datatype"
      >&#8869;</a
      ><a name="20456"
      > </a
      ><a name="20457" class="Symbol"
      >&#8594;</a
      ><a name="20458"
      > </a
      ><a name="20459" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#97" class="Datatype"
      >&#8469;</a
      ><a name="20460"
      >
</a
      ><a name="20461" href="Logic.html#20445" class="Function"
      >&#8869;-count</a
      ><a name="20468"
      > </a
      ><a name="20469" class="Symbol"
      >()</a
      >
{% endraw %}</pre>
Here, again, pattern `()` indicates that no value can match
type `⊥`.

For numbers, zero is the identity of additition. Correspondingly,
empty is the identity of sums *up to isomorphism*.

For left identity, the `to` function observes that `inj₁ ()` can never arise,
and takes `inj₂ x` to `x`, and the `fro` function
does the inverse.  The evidence of left inverse requires matching against
a suitable pattern to enable simplification.
<pre class="Agda">{% raw %}
<a name="20932" href="Logic.html#20932" class="Function"
      >&#8869;-identity&#737;</a
      ><a name="20943"
      > </a
      ><a name="20944" class="Symbol"
      >:</a
      ><a name="20945"
      > </a
      ><a name="20946" class="Symbol"
      >&#8704;</a
      ><a name="20947"
      > </a
      ><a name="20948" class="Symbol"
      >{</a
      ><a name="20949" href="Logic.html#20949" class="Bound"
      >A</a
      ><a name="20950"
      > </a
      ><a name="20951" class="Symbol"
      >:</a
      ><a name="20952"
      > </a
      ><a name="20953" class="PrimitiveType"
      >Set</a
      ><a name="20956" class="Symbol"
      >}</a
      ><a name="20957"
      > </a
      ><a name="20958" class="Symbol"
      >&#8594;</a
      ><a name="20959"
      > </a
      ><a name="20960" class="Symbol"
      >(</a
      ><a name="20961" href="Logic.html#19450" class="Datatype"
      >&#8869;</a
      ><a name="20962"
      > </a
      ><a name="20963" href="Logic.html#14656" class="Datatype Operator"
      >&#8846;</a
      ><a name="20964"
      > </a
      ><a name="20965" href="Logic.html#20949" class="Bound"
      >A</a
      ><a name="20966" class="Symbol"
      >)</a
      ><a name="20967"
      > </a
      ><a name="20968" href="Logic.html#1478" class="Record Operator"
      >&#8771;</a
      ><a name="20969"
      > </a
      ><a name="20970" href="Logic.html#20949" class="Bound"
      >A</a
      ><a name="20971"
      >
</a
      ><a name="20972" href="Logic.html#20932" class="Function"
      >&#8869;-identity&#737;</a
      ><a name="20983"
      > </a
      ><a name="20984" class="Symbol"
      >=</a
      ><a name="20985"
      >
  </a
      ><a name="20988" class="Keyword"
      >record</a
      ><a name="20994"
      >
    </a
      ><a name="20999" class="Symbol"
      >{</a
      ><a name="21000"
      > </a
      ><a name="21001" class="Field"
      >to</a
      ><a name="21003"
      >   </a
      ><a name="21006" class="Symbol"
      >=</a
      ><a name="21007"
      > </a
      ><a name="21008" class="Symbol"
      >&#955;</a
      ><a name="21009"
      > </a
      ><a name="21010" class="Symbol"
      >{</a
      ><a name="21011"
      > </a
      ><a name="21012" class="Symbol"
      >(</a
      ><a name="21013" href="Logic.html#14686" class="InductiveConstructor"
      >inj&#8321;</a
      ><a name="21017"
      > </a
      ><a name="21018" class="Symbol"
      >())</a
      ><a name="21021"
      >
               </a
      ><a name="21037" class="Symbol"
      >;</a
      ><a name="21038"
      > </a
      ><a name="21039" class="Symbol"
      >(</a
      ><a name="21040" href="Logic.html#14722" class="InductiveConstructor"
      >inj&#8322;</a
      ><a name="21044"
      > </a
      ><a name="21045" href="Logic.html#21045" class="Bound"
      >x</a
      ><a name="21046" class="Symbol"
      >)</a
      ><a name="21047"
      > </a
      ><a name="21048" class="Symbol"
      >&#8594;</a
      ><a name="21049"
      > </a
      ><a name="21050" href="Logic.html#21045" class="Bound"
      >x</a
      ><a name="21051"
      >
               </a
      ><a name="21067" class="Symbol"
      >}</a
      ><a name="21068"
      >
    </a
      ><a name="21073" class="Symbol"
      >;</a
      ><a name="21074"
      > </a
      ><a name="21075" class="Field"
      >fro</a
      ><a name="21078"
      >  </a
      ><a name="21080" class="Symbol"
      >=</a
      ><a name="21081"
      > </a
      ><a name="21082" class="Symbol"
      >&#955;</a
      ><a name="21083"
      > </a
      ><a name="21084" class="Symbol"
      >{</a
      ><a name="21085"
      > </a
      ><a name="21086" href="Logic.html#21086" class="Bound"
      >x</a
      ><a name="21087"
      > </a
      ><a name="21088" class="Symbol"
      >&#8594;</a
      ><a name="21089"
      > </a
      ><a name="21090" href="Logic.html#14722" class="InductiveConstructor"
      >inj&#8322;</a
      ><a name="21094"
      > </a
      ><a name="21095" href="Logic.html#21086" class="Bound"
      >x</a
      ><a name="21096"
      > </a
      ><a name="21097" class="Symbol"
      >}</a
      ><a name="21098"
      >
    </a
      ><a name="21103" class="Symbol"
      >;</a
      ><a name="21104"
      > </a
      ><a name="21105" class="Field"
      >inv&#737;</a
      ><a name="21109"
      > </a
      ><a name="21110" class="Symbol"
      >=</a
      ><a name="21111"
      > </a
      ><a name="21112" class="Symbol"
      >&#955;</a
      ><a name="21113"
      > </a
      ><a name="21114" class="Symbol"
      >{</a
      ><a name="21115"
      > </a
      ><a name="21116" class="Symbol"
      >(</a
      ><a name="21117" href="Logic.html#14686" class="InductiveConstructor"
      >inj&#8321;</a
      ><a name="21121"
      > </a
      ><a name="21122" class="Symbol"
      >())</a
      ><a name="21125"
      >
               </a
      ><a name="21141" class="Symbol"
      >;</a
      ><a name="21142"
      > </a
      ><a name="21143" class="Symbol"
      >(</a
      ><a name="21144" href="Logic.html#14722" class="InductiveConstructor"
      >inj&#8322;</a
      ><a name="21148"
      > </a
      ><a name="21149" href="Logic.html#21149" class="Bound"
      >x</a
      ><a name="21150" class="Symbol"
      >)</a
      ><a name="21151"
      > </a
      ><a name="21152" class="Symbol"
      >&#8594;</a
      ><a name="21153"
      > </a
      ><a name="21154" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="21158"
      >
               </a
      ><a name="21174" class="Symbol"
      >}</a
      ><a name="21175"
      >
    </a
      ><a name="21180" class="Symbol"
      >;</a
      ><a name="21181"
      > </a
      ><a name="21182" class="Field"
      >inv&#691;</a
      ><a name="21186"
      > </a
      ><a name="21187" class="Symbol"
      >=</a
      ><a name="21188"
      > </a
      ><a name="21189" class="Symbol"
      >&#955;</a
      ><a name="21190"
      > </a
      ><a name="21191" class="Symbol"
      >{</a
      ><a name="21192"
      > </a
      ><a name="21193" href="Logic.html#21193" class="Bound"
      >x</a
      ><a name="21194"
      > </a
      ><a name="21195" class="Symbol"
      >&#8594;</a
      ><a name="21196"
      > </a
      ><a name="21197" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="21201"
      > </a
      ><a name="21202" class="Symbol"
      >}</a
      ><a name="21203"
      >
    </a
      ><a name="21208" class="Symbol"
      >}</a
      >
{% endraw %}</pre>

Having an *identity* is different from having an identity
*up to isomorphism*.  Compare the two statements:

    0 + m ≡ m
    ⊥ ⊎ A ≃ A

In the first case, we might have that `m` is `2`, and both `0 + m` and
`m` are equal to `2`.  In the second case, we might have that `A` is
`Bool`, and `⊥ ⊎ Bool` is *not* the same as `Bool`.  But there is an
isomorphism betwee the two types.  For instance, `inj₂ true`, which is
a member of the former, corresponds to `true`, which is a member of
the latter.

That empty is also a right identity follows immediately from left
identity, commutativity of sum, and symmetry and transitivity of
isomorphism.
<pre class="Agda">{% raw %}
<a name="21878" href="Logic.html#21878" class="Function"
      >&#8869;-identity&#691;</a
      ><a name="21889"
      > </a
      ><a name="21890" class="Symbol"
      >:</a
      ><a name="21891"
      > </a
      ><a name="21892" class="Symbol"
      >&#8704;</a
      ><a name="21893"
      > </a
      ><a name="21894" class="Symbol"
      >{</a
      ><a name="21895" href="Logic.html#21895" class="Bound"
      >A</a
      ><a name="21896"
      > </a
      ><a name="21897" class="Symbol"
      >:</a
      ><a name="21898"
      > </a
      ><a name="21899" class="PrimitiveType"
      >Set</a
      ><a name="21902" class="Symbol"
      >}</a
      ><a name="21903"
      > </a
      ><a name="21904" class="Symbol"
      >&#8594;</a
      ><a name="21905"
      > </a
      ><a name="21906" href="Logic.html#21895" class="Bound"
      >A</a
      ><a name="21907"
      > </a
      ><a name="21908" href="Logic.html#1478" class="Record Operator"
      >&#8771;</a
      ><a name="21909"
      > </a
      ><a name="21910" class="Symbol"
      >(</a
      ><a name="21911" href="Logic.html#21895" class="Bound"
      >A</a
      ><a name="21912"
      > </a
      ><a name="21913" href="Logic.html#14656" class="Datatype Operator"
      >&#8846;</a
      ><a name="21914"
      > </a
      ><a name="21915" href="Logic.html#19450" class="Datatype"
      >&#8869;</a
      ><a name="21916" class="Symbol"
      >)</a
      ><a name="21917"
      >
</a
      ><a name="21918" href="Logic.html#21878" class="Function"
      >&#8869;-identity&#691;</a
      ><a name="21929"
      > </a
      ><a name="21930" class="Symbol"
      >=</a
      ><a name="21931"
      > </a
      ><a name="21932" href="Logic.html#3956" class="Function"
      >&#8771;-trans</a
      ><a name="21939"
      > </a
      ><a name="21940" class="Symbol"
      >(</a
      ><a name="21941" href="Logic.html#3655" class="Function"
      >&#8771;-sym</a
      ><a name="21946"
      > </a
      ><a name="21947" href="Logic.html#20932" class="Function"
      >&#8869;-identity&#737;</a
      ><a name="21958" class="Symbol"
      >)</a
      ><a name="21959"
      > </a
      ><a name="21960" href="Logic.html#16812" class="Function"
      >&#8846;-comm</a
      >
{% endraw %}</pre>


## Implication is function

Given two propositions `A` and `B`, the implication `A → B` holds if
whenever `A` holds then `B` must also hold.  We formalise implication using
the function type, which has appeared throughout this book.

Evidence that `A → B` holds is of the form

    λ (x : A) → N[x]

where `N[x]` is a term of type `B` containing as a free variable `x` of type `A`.
Given a term `L` providing evidence that `A → B` holds, and a term `M`
providing evidence that `A` holds, the term `L M` provides evidence that
`B` holds.  In other words, evidence that `A → B` holds is a function that
converts evidence that `A` holds into evidence that `B` holds.

Put another way, if we know that `A → B` and `A` both hold,
then we may conclude that `B` holds. In medieval times, this rule was
known by the name *modus ponens*.

If we introduce an implication and then immediately eliminate it, we can
always simplify the resulting term.  Thus

    (λ (x : A) → N[x]) M

simplifies to `N[M]` of type `B`, where `N[M]` stands for the term `N[x]` with each
free occurrence of `x` replaced by `M` of type `A`.

<!--
Given evidence that `A → B` holds and that `A` holds, we can conclude that
`B` holds.
<pre class="Agda">{% raw %}
<a name="23193" href="Logic.html#23193" class="Function"
      >&#8594;-elim</a
      ><a name="23199"
      > </a
      ><a name="23200" class="Symbol"
      >:</a
      ><a name="23201"
      > </a
      ><a name="23202" class="Symbol"
      >&#8704;</a
      ><a name="23203"
      > </a
      ><a name="23204" class="Symbol"
      >{</a
      ><a name="23205" href="Logic.html#23205" class="Bound"
      >A</a
      ><a name="23206"
      > </a
      ><a name="23207" href="Logic.html#23207" class="Bound"
      >B</a
      ><a name="23208"
      > </a
      ><a name="23209" class="Symbol"
      >:</a
      ><a name="23210"
      > </a
      ><a name="23211" class="PrimitiveType"
      >Set</a
      ><a name="23214" class="Symbol"
      >}</a
      ><a name="23215"
      > </a
      ><a name="23216" class="Symbol"
      >&#8594;</a
      ><a name="23217"
      > </a
      ><a name="23218" class="Symbol"
      >(</a
      ><a name="23219" href="Logic.html#23205" class="Bound"
      >A</a
      ><a name="23220"
      > </a
      ><a name="23221" class="Symbol"
      >&#8594;</a
      ><a name="23222"
      > </a
      ><a name="23223" href="Logic.html#23207" class="Bound"
      >B</a
      ><a name="23224" class="Symbol"
      >)</a
      ><a name="23225"
      > </a
      ><a name="23226" class="Symbol"
      >&#8594;</a
      ><a name="23227"
      > </a
      ><a name="23228" href="Logic.html#23205" class="Bound"
      >A</a
      ><a name="23229"
      > </a
      ><a name="23230" class="Symbol"
      >&#8594;</a
      ><a name="23231"
      > </a
      ><a name="23232" href="Logic.html#23207" class="Bound"
      >B</a
      ><a name="23233"
      >
</a
      ><a name="23234" href="Logic.html#23193" class="Function"
      >&#8594;-elim</a
      ><a name="23240"
      > </a
      ><a name="23241" href="Logic.html#23241" class="Bound"
      >f</a
      ><a name="23242"
      > </a
      ><a name="23243" href="Logic.html#23243" class="Bound"
      >x</a
      ><a name="23244"
      > </a
      ><a name="23245" class="Symbol"
      >=</a
      ><a name="23246"
      > </a
      ><a name="23247" href="Logic.html#23241" class="Bound"
      >f</a
      ><a name="23248"
      > </a
      ><a name="23249" href="Logic.html#23243" class="Bound"
      >x</a
      >
{% endraw %}</pre>
In medieval times, this rule was known by the latin name *modus ponens*.
-->

Implication binds less tightly than any other operator. Thus, `A ⊎ B →
B ⊎ A` parses as `(A ⊎ B) → (B ⊎ A)`.

Given two types `A` and `B`, we refer to `A → B` as the *function*
from `A` to `B`.  It is also sometimes called the *exponential*,
with `B` raised to the `A` power.  Among other reasons for calling
it the exponential, note that if type `A` has `m` distinct
memebers, and type `B` has `n` distinct members, then the type
`A → B` has `n ^ m` distinct members.  For instance, consider a
type `Bool` with two members and a type `Tri` with three members,
as defined earlier. The the type `Bool → Tri` has nine (that is,
three squared) members:

    {true → aa; false → aa}  {true → aa; false → bb}  {true → aa; false → cc}
    {true → bb; false → aa}  {true → bb; false → bb}  {true → bb; false → cc}
    {true → cc; false → aa}  {true → cc; false → bb}  {true → cc; false → cc}

For example, the following function enumerates all possible
arguments of the type `Bool → Tri`:
<pre class="Agda">{% raw %}
<a name="24335" href="Logic.html#24335" class="Function"
      >&#8594;-count</a
      ><a name="24342"
      > </a
      ><a name="24343" class="Symbol"
      >:</a
      ><a name="24344"
      > </a
      ><a name="24345" class="Symbol"
      >(</a
      ><a name="24346" href="Logic.html#9008" class="Datatype"
      >Bool</a
      ><a name="24350"
      > </a
      ><a name="24351" class="Symbol"
      >&#8594;</a
      ><a name="24352"
      > </a
      ><a name="24353" href="Logic.html#9060" class="Datatype"
      >Tri</a
      ><a name="24356" class="Symbol"
      >)</a
      ><a name="24357"
      > </a
      ><a name="24358" class="Symbol"
      >&#8594;</a
      ><a name="24359"
      > </a
      ><a name="24360" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#97" class="Datatype"
      >&#8469;</a
      ><a name="24361"
      >
</a
      ><a name="24362" href="Logic.html#24335" class="Function"
      >&#8594;-count</a
      ><a name="24369"
      > </a
      ><a name="24370" href="Logic.html#24370" class="Bound"
      >f</a
      ><a name="24371"
      > </a
      ><a name="24372" class="Keyword"
      >with</a
      ><a name="24376"
      > </a
      ><a name="24377" href="Logic.html#24370" class="Bound"
      >f</a
      ><a name="24378"
      > </a
      ><a name="24379" href="Logic.html#9027" class="InductiveConstructor"
      >true</a
      ><a name="24383"
      > </a
      ><a name="24384" class="Symbol"
      >|</a
      ><a name="24385"
      > </a
      ><a name="24386" href="Logic.html#24370" class="Bound"
      >f</a
      ><a name="24387"
      > </a
      ><a name="24388" href="Logic.html#9041" class="InductiveConstructor"
      >false</a
      ><a name="24393"
      >
</a
      ><a name="24394" class="Symbol"
      >...</a
      ><a name="24397"
      >           </a
      ><a name="24408" class="Symbol"
      >|</a
      ><a name="24409"
      > </a
      ><a name="24410" href="Logic.html#9078" class="InductiveConstructor"
      >aa</a
      ><a name="24412"
      >    </a
      ><a name="24416" class="Symbol"
      >|</a
      ><a name="24417"
      > </a
      ><a name="24418" href="Logic.html#9078" class="InductiveConstructor"
      >aa</a
      ><a name="24420"
      >      </a
      ><a name="24426" class="Symbol"
      >=</a
      ><a name="24427"
      > </a
      ><a name="24428" class="Number"
      >1</a
      ><a name="24429"
      >
</a
      ><a name="24430" class="Symbol"
      >...</a
      ><a name="24433"
      >           </a
      ><a name="24444" class="Symbol"
      >|</a
      ><a name="24445"
      > </a
      ><a name="24446" href="Logic.html#9078" class="InductiveConstructor"
      >aa</a
      ><a name="24448"
      >    </a
      ><a name="24452" class="Symbol"
      >|</a
      ><a name="24453"
      > </a
      ><a name="24454" href="Logic.html#9089" class="InductiveConstructor"
      >bb</a
      ><a name="24456"
      >      </a
      ><a name="24462" class="Symbol"
      >=</a
      ><a name="24463"
      > </a
      ><a name="24464" class="Number"
      >2</a
      ><a name="24465"
      >  
</a
      ><a name="24468" class="Symbol"
      >...</a
      ><a name="24471"
      >           </a
      ><a name="24482" class="Symbol"
      >|</a
      ><a name="24483"
      > </a
      ><a name="24484" href="Logic.html#9078" class="InductiveConstructor"
      >aa</a
      ><a name="24486"
      >    </a
      ><a name="24490" class="Symbol"
      >|</a
      ><a name="24491"
      > </a
      ><a name="24492" href="Logic.html#9100" class="InductiveConstructor"
      >cc</a
      ><a name="24494"
      >      </a
      ><a name="24500" class="Symbol"
      >=</a
      ><a name="24501"
      > </a
      ><a name="24502" class="Number"
      >3</a
      ><a name="24503"
      >
</a
      ><a name="24504" class="Symbol"
      >...</a
      ><a name="24507"
      >           </a
      ><a name="24518" class="Symbol"
      >|</a
      ><a name="24519"
      > </a
      ><a name="24520" href="Logic.html#9089" class="InductiveConstructor"
      >bb</a
      ><a name="24522"
      >    </a
      ><a name="24526" class="Symbol"
      >|</a
      ><a name="24527"
      > </a
      ><a name="24528" href="Logic.html#9078" class="InductiveConstructor"
      >aa</a
      ><a name="24530"
      >      </a
      ><a name="24536" class="Symbol"
      >=</a
      ><a name="24537"
      > </a
      ><a name="24538" class="Number"
      >4</a
      ><a name="24539"
      >
</a
      ><a name="24540" class="Symbol"
      >...</a
      ><a name="24543"
      >           </a
      ><a name="24554" class="Symbol"
      >|</a
      ><a name="24555"
      > </a
      ><a name="24556" href="Logic.html#9089" class="InductiveConstructor"
      >bb</a
      ><a name="24558"
      >    </a
      ><a name="24562" class="Symbol"
      >|</a
      ><a name="24563"
      > </a
      ><a name="24564" href="Logic.html#9089" class="InductiveConstructor"
      >bb</a
      ><a name="24566"
      >      </a
      ><a name="24572" class="Symbol"
      >=</a
      ><a name="24573"
      > </a
      ><a name="24574" class="Number"
      >5</a
      ><a name="24575"
      >
</a
      ><a name="24576" class="Symbol"
      >...</a
      ><a name="24579"
      >           </a
      ><a name="24590" class="Symbol"
      >|</a
      ><a name="24591"
      > </a
      ><a name="24592" href="Logic.html#9089" class="InductiveConstructor"
      >bb</a
      ><a name="24594"
      >    </a
      ><a name="24598" class="Symbol"
      >|</a
      ><a name="24599"
      > </a
      ><a name="24600" href="Logic.html#9100" class="InductiveConstructor"
      >cc</a
      ><a name="24602"
      >      </a
      ><a name="24608" class="Symbol"
      >=</a
      ><a name="24609"
      > </a
      ><a name="24610" class="Number"
      >6</a
      ><a name="24611"
      >
</a
      ><a name="24612" class="Symbol"
      >...</a
      ><a name="24615"
      >           </a
      ><a name="24626" class="Symbol"
      >|</a
      ><a name="24627"
      > </a
      ><a name="24628" href="Logic.html#9100" class="InductiveConstructor"
      >cc</a
      ><a name="24630"
      >    </a
      ><a name="24634" class="Symbol"
      >|</a
      ><a name="24635"
      > </a
      ><a name="24636" href="Logic.html#9078" class="InductiveConstructor"
      >aa</a
      ><a name="24638"
      >      </a
      ><a name="24644" class="Symbol"
      >=</a
      ><a name="24645"
      > </a
      ><a name="24646" class="Number"
      >7</a
      ><a name="24647"
      >
</a
      ><a name="24648" class="Symbol"
      >...</a
      ><a name="24651"
      >           </a
      ><a name="24662" class="Symbol"
      >|</a
      ><a name="24663"
      > </a
      ><a name="24664" href="Logic.html#9100" class="InductiveConstructor"
      >cc</a
      ><a name="24666"
      >    </a
      ><a name="24670" class="Symbol"
      >|</a
      ><a name="24671"
      > </a
      ><a name="24672" href="Logic.html#9089" class="InductiveConstructor"
      >bb</a
      ><a name="24674"
      >      </a
      ><a name="24680" class="Symbol"
      >=</a
      ><a name="24681"
      > </a
      ><a name="24682" class="Number"
      >8</a
      ><a name="24683"
      >
</a
      ><a name="24684" class="Symbol"
      >...</a
      ><a name="24687"
      >           </a
      ><a name="24698" class="Symbol"
      >|</a
      ><a name="24699"
      > </a
      ><a name="24700" href="Logic.html#9100" class="InductiveConstructor"
      >cc</a
      ><a name="24702"
      >    </a
      ><a name="24706" class="Symbol"
      >|</a
      ><a name="24707"
      > </a
      ><a name="24708" href="Logic.html#9100" class="InductiveConstructor"
      >cc</a
      ><a name="24710"
      >      </a
      ><a name="24716" class="Symbol"
      >=</a
      ><a name="24717"
      > </a
      ><a name="24718" class="Number"
      >9</a
      >
{% endraw %}</pre>

Exponential on types also share a property with exponential on
numbers in that many of the standard identities for numbers carry
over to the types.

Corresponding to the law

    (p ^ n) ^ m  =  p ^ (n * m)

we have that the types `A → B → C` and `A × B → C` are isomorphic.
Both types can be viewed as functions that given evidence that `A` holds
and evidence that `B` holds can return evidence that `C` holds.
This isomorphism sometimes goes by the name *currying*.
The proof of the right inverse requires extensionality.
<pre class="Agda">{% raw %}
<a name="25271" class="Keyword"
      >postulate</a
      ><a name="25280"
      >
  </a
      ><a name="25283" href="Logic.html#25283" class="Postulate"
      >extensionality</a
      ><a name="25297"
      > </a
      ><a name="25298" class="Symbol"
      >:</a
      ><a name="25299"
      > </a
      ><a name="25300" class="Symbol"
      >&#8704;</a
      ><a name="25301"
      > </a
      ><a name="25302" class="Symbol"
      >{</a
      ><a name="25303" href="Logic.html#25303" class="Bound"
      >A</a
      ><a name="25304"
      > </a
      ><a name="25305" href="Logic.html#25305" class="Bound"
      >B</a
      ><a name="25306"
      > </a
      ><a name="25307" class="Symbol"
      >:</a
      ><a name="25308"
      > </a
      ><a name="25309" class="PrimitiveType"
      >Set</a
      ><a name="25312" class="Symbol"
      >}</a
      ><a name="25313"
      > </a
      ><a name="25314" class="Symbol"
      >&#8594;</a
      ><a name="25315"
      > </a
      ><a name="25316" class="Symbol"
      >{</a
      ><a name="25317" href="Logic.html#25317" class="Bound"
      >f</a
      ><a name="25318"
      > </a
      ><a name="25319" href="Logic.html#25319" class="Bound"
      >g</a
      ><a name="25320"
      > </a
      ><a name="25321" class="Symbol"
      >:</a
      ><a name="25322"
      > </a
      ><a name="25323" href="Logic.html#25303" class="Bound"
      >A</a
      ><a name="25324"
      > </a
      ><a name="25325" class="Symbol"
      >&#8594;</a
      ><a name="25326"
      > </a
      ><a name="25327" href="Logic.html#25305" class="Bound"
      >B</a
      ><a name="25328" class="Symbol"
      >}</a
      ><a name="25329"
      > </a
      ><a name="25330" class="Symbol"
      >&#8594;</a
      ><a name="25331"
      > </a
      ><a name="25332" class="Symbol"
      >(&#8704;</a
      ><a name="25334"
      > </a
      ><a name="25335" class="Symbol"
      >(</a
      ><a name="25336" href="Logic.html#25336" class="Bound"
      >x</a
      ><a name="25337"
      > </a
      ><a name="25338" class="Symbol"
      >:</a
      ><a name="25339"
      > </a
      ><a name="25340" href="Logic.html#25303" class="Bound"
      >A</a
      ><a name="25341" class="Symbol"
      >)</a
      ><a name="25342"
      > </a
      ><a name="25343" class="Symbol"
      >&#8594;</a
      ><a name="25344"
      > </a
      ><a name="25345" href="Logic.html#25317" class="Bound"
      >f</a
      ><a name="25346"
      > </a
      ><a name="25347" href="Logic.html#25336" class="Bound"
      >x</a
      ><a name="25348"
      > </a
      ><a name="25349" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="25350"
      > </a
      ><a name="25351" href="Logic.html#25319" class="Bound"
      >g</a
      ><a name="25352"
      > </a
      ><a name="25353" href="Logic.html#25336" class="Bound"
      >x</a
      ><a name="25354" class="Symbol"
      >)</a
      ><a name="25355"
      > </a
      ><a name="25356" class="Symbol"
      >&#8594;</a
      ><a name="25357"
      > </a
      ><a name="25358" href="Logic.html#25317" class="Bound"
      >f</a
      ><a name="25359"
      > </a
      ><a name="25360" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="25361"
      > </a
      ><a name="25362" href="Logic.html#25319" class="Bound"
      >g</a
      ><a name="25363"
      >
  
</a
      ><a name="25367" href="Logic.html#25367" class="Function"
      >currying</a
      ><a name="25375"
      > </a
      ><a name="25376" class="Symbol"
      >:</a
      ><a name="25377"
      > </a
      ><a name="25378" class="Symbol"
      >&#8704;</a
      ><a name="25379"
      > </a
      ><a name="25380" class="Symbol"
      >{</a
      ><a name="25381" href="Logic.html#25381" class="Bound"
      >A</a
      ><a name="25382"
      > </a
      ><a name="25383" href="Logic.html#25383" class="Bound"
      >B</a
      ><a name="25384"
      > </a
      ><a name="25385" href="Logic.html#25385" class="Bound"
      >C</a
      ><a name="25386"
      > </a
      ><a name="25387" class="Symbol"
      >:</a
      ><a name="25388"
      > </a
      ><a name="25389" class="PrimitiveType"
      >Set</a
      ><a name="25392" class="Symbol"
      >}</a
      ><a name="25393"
      > </a
      ><a name="25394" class="Symbol"
      >&#8594;</a
      ><a name="25395"
      > </a
      ><a name="25396" class="Symbol"
      >(</a
      ><a name="25397" href="Logic.html#25381" class="Bound"
      >A</a
      ><a name="25398"
      > </a
      ><a name="25399" class="Symbol"
      >&#8594;</a
      ><a name="25400"
      > </a
      ><a name="25401" href="Logic.html#25383" class="Bound"
      >B</a
      ><a name="25402"
      > </a
      ><a name="25403" class="Symbol"
      >&#8594;</a
      ><a name="25404"
      > </a
      ><a name="25405" href="Logic.html#25385" class="Bound"
      >C</a
      ><a name="25406" class="Symbol"
      >)</a
      ><a name="25407"
      > </a
      ><a name="25408" href="Logic.html#1478" class="Record Operator"
      >&#8771;</a
      ><a name="25409"
      > </a
      ><a name="25410" class="Symbol"
      >(</a
      ><a name="25411" href="Logic.html#25381" class="Bound"
      >A</a
      ><a name="25412"
      > </a
      ><a name="25413" href="Logic.html#7202" class="Datatype Operator"
      >&#215;</a
      ><a name="25414"
      > </a
      ><a name="25415" href="Logic.html#25383" class="Bound"
      >B</a
      ><a name="25416"
      > </a
      ><a name="25417" class="Symbol"
      >&#8594;</a
      ><a name="25418"
      > </a
      ><a name="25419" href="Logic.html#25385" class="Bound"
      >C</a
      ><a name="25420" class="Symbol"
      >)</a
      ><a name="25421"
      >
</a
      ><a name="25422" href="Logic.html#25367" class="Function"
      >currying</a
      ><a name="25430"
      > </a
      ><a name="25431" class="Symbol"
      >=</a
      ><a name="25432"
      >
  </a
      ><a name="25435" class="Keyword"
      >record</a
      ><a name="25441"
      >
    </a
      ><a name="25446" class="Symbol"
      >{</a
      ><a name="25447"
      > </a
      ><a name="25448" class="Field"
      >to</a
      ><a name="25450"
      >   </a
      ><a name="25453" class="Symbol"
      >=</a
      ><a name="25454"
      >  </a
      ><a name="25456" class="Symbol"
      >&#955;</a
      ><a name="25457"
      > </a
      ><a name="25458" href="Logic.html#25458" class="Bound"
      >f</a
      ><a name="25459"
      > </a
      ><a name="25460" class="Symbol"
      >&#8594;</a
      ><a name="25461"
      > </a
      ><a name="25462" class="Symbol"
      >&#955;</a
      ><a name="25463"
      > </a
      ><a name="25464" class="Symbol"
      >{</a
      ><a name="25465"
      > </a
      ><a name="25466" class="Symbol"
      >(</a
      ><a name="25467" href="Logic.html#25467" class="Bound"
      >x</a
      ><a name="25468"
      > </a
      ><a name="25469" href="Logic.html#7232" class="InductiveConstructor Operator"
      >,</a
      ><a name="25470"
      > </a
      ><a name="25471" href="Logic.html#25471" class="Bound"
      >y</a
      ><a name="25472" class="Symbol"
      >)</a
      ><a name="25473"
      > </a
      ><a name="25474" class="Symbol"
      >&#8594;</a
      ><a name="25475"
      > </a
      ><a name="25476" href="Logic.html#25458" class="Bound"
      >f</a
      ><a name="25477"
      > </a
      ><a name="25478" href="Logic.html#25467" class="Bound"
      >x</a
      ><a name="25479"
      > </a
      ><a name="25480" href="Logic.html#25471" class="Bound"
      >y</a
      ><a name="25481"
      > </a
      ><a name="25482" class="Symbol"
      >}</a
      ><a name="25483"
      >
    </a
      ><a name="25488" class="Symbol"
      >;</a
      ><a name="25489"
      > </a
      ><a name="25490" class="Field"
      >fro</a
      ><a name="25493"
      >  </a
      ><a name="25495" class="Symbol"
      >=</a
      ><a name="25496"
      >  </a
      ><a name="25498" class="Symbol"
      >&#955;</a
      ><a name="25499"
      > </a
      ><a name="25500" href="Logic.html#25500" class="Bound"
      >g</a
      ><a name="25501"
      > </a
      ><a name="25502" class="Symbol"
      >&#8594;</a
      ><a name="25503"
      > </a
      ><a name="25504" class="Symbol"
      >&#955;</a
      ><a name="25505"
      > </a
      ><a name="25506" href="Logic.html#25506" class="Bound"
      >x</a
      ><a name="25507"
      > </a
      ><a name="25508" class="Symbol"
      >&#8594;</a
      ><a name="25509"
      > </a
      ><a name="25510" class="Symbol"
      >&#955;</a
      ><a name="25511"
      > </a
      ><a name="25512" href="Logic.html#25512" class="Bound"
      >y</a
      ><a name="25513"
      > </a
      ><a name="25514" class="Symbol"
      >&#8594;</a
      ><a name="25515"
      > </a
      ><a name="25516" href="Logic.html#25500" class="Bound"
      >g</a
      ><a name="25517"
      > </a
      ><a name="25518" class="Symbol"
      >(</a
      ><a name="25519" href="Logic.html#25506" class="Bound"
      >x</a
      ><a name="25520"
      > </a
      ><a name="25521" href="Logic.html#7232" class="InductiveConstructor Operator"
      >,</a
      ><a name="25522"
      > </a
      ><a name="25523" href="Logic.html#25512" class="Bound"
      >y</a
      ><a name="25524" class="Symbol"
      >)</a
      ><a name="25525"
      >
    </a
      ><a name="25530" class="Symbol"
      >;</a
      ><a name="25531"
      > </a
      ><a name="25532" class="Field"
      >inv&#737;</a
      ><a name="25536"
      > </a
      ><a name="25537" class="Symbol"
      >=</a
      ><a name="25538"
      >  </a
      ><a name="25540" class="Symbol"
      >&#955;</a
      ><a name="25541"
      > </a
      ><a name="25542" href="Logic.html#25542" class="Bound"
      >f</a
      ><a name="25543"
      > </a
      ><a name="25544" class="Symbol"
      >&#8594;</a
      ><a name="25545"
      > </a
      ><a name="25546" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="25550"
      >
    </a
      ><a name="25555" class="Symbol"
      >;</a
      ><a name="25556"
      > </a
      ><a name="25557" class="Field"
      >inv&#691;</a
      ><a name="25561"
      > </a
      ><a name="25562" class="Symbol"
      >=</a
      ><a name="25563"
      >  </a
      ><a name="25565" class="Symbol"
      >&#955;</a
      ><a name="25566"
      > </a
      ><a name="25567" href="Logic.html#25567" class="Bound"
      >g</a
      ><a name="25568"
      > </a
      ><a name="25569" class="Symbol"
      >&#8594;</a
      ><a name="25570"
      > </a
      ><a name="25571" href="Logic.html#25283" class="Postulate"
      >extensionality</a
      ><a name="25585"
      > </a
      ><a name="25586" class="Symbol"
      >(&#955;</a
      ><a name="25588"
      > </a
      ><a name="25589" class="Symbol"
      >{</a
      ><a name="25590"
      > </a
      ><a name="25591" class="Symbol"
      >(</a
      ><a name="25592" href="Logic.html#25592" class="Bound"
      >x</a
      ><a name="25593"
      > </a
      ><a name="25594" href="Logic.html#7232" class="InductiveConstructor Operator"
      >,</a
      ><a name="25595"
      > </a
      ><a name="25596" href="Logic.html#25596" class="Bound"
      >y</a
      ><a name="25597" class="Symbol"
      >)</a
      ><a name="25598"
      > </a
      ><a name="25599" class="Symbol"
      >&#8594;</a
      ><a name="25600"
      > </a
      ><a name="25601" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="25605"
      > </a
      ><a name="25606" class="Symbol"
      >})</a
      ><a name="25608"
      >
    </a
      ><a name="25613" class="Symbol"
      >}</a
      >
{% endraw %}</pre>

Currying tells us that instead of a function that takes a pair of arguments,
we can have a function that takes the first argument and returns a function that
expects the second argument.  Thus, for instance, instead of

    _+′_ : (ℕ × ℕ) → ℕ

we have

    _+_ : ℕ → ℕ → ℕ

The syntax of Agda, like that of other functional languages such as ML and
Haskell, is designed to make currying easy to use.  Function arrows associate
to the left and application associates to the right.  Thus

    A → B → C    *stands for*    A → (B → C)

and

   f x y    *stands for*   (f x) y

Currying is named for Haskell Curry, after whom the programming language Haskell
is also named.  However, Currying was introduced earlier by both Gotlob Frege
and Moses Schönfinkel.  When I first learned about currying, I was told a joke:
"It should be called schönfinkeling, but currying is tastier". Only later did I
learn that the idea actually goes all the way back to Frege!

Corresponding to the law

    p ^ (n + m) = (p ^ n) * (p ^ m)

we have that the types `A ⊎ B → C` and `(A → C) × (B → C)` are isomorphic.
That is, the assertion that if either `A` holds or `B` holds then `C` holds
is the same as the assertion that if `A` holds then `C` holds and if
`B` holds then `C` holds.
<pre class="Agda">{% raw %}
<a name="26904" href="Logic.html#26904" class="Function"
      >&#8594;-distributes-&#8846;</a
      ><a name="26919"
      > </a
      ><a name="26920" class="Symbol"
      >:</a
      ><a name="26921"
      > </a
      ><a name="26922" class="Symbol"
      >&#8704;</a
      ><a name="26923"
      > </a
      ><a name="26924" class="Symbol"
      >{</a
      ><a name="26925" href="Logic.html#26925" class="Bound"
      >A</a
      ><a name="26926"
      > </a
      ><a name="26927" href="Logic.html#26927" class="Bound"
      >B</a
      ><a name="26928"
      > </a
      ><a name="26929" href="Logic.html#26929" class="Bound"
      >C</a
      ><a name="26930"
      > </a
      ><a name="26931" class="Symbol"
      >:</a
      ><a name="26932"
      > </a
      ><a name="26933" class="PrimitiveType"
      >Set</a
      ><a name="26936" class="Symbol"
      >}</a
      ><a name="26937"
      > </a
      ><a name="26938" class="Symbol"
      >&#8594;</a
      ><a name="26939"
      > </a
      ><a name="26940" class="Symbol"
      >(</a
      ><a name="26941" href="Logic.html#26925" class="Bound"
      >A</a
      ><a name="26942"
      > </a
      ><a name="26943" href="Logic.html#14656" class="Datatype Operator"
      >&#8846;</a
      ><a name="26944"
      > </a
      ><a name="26945" href="Logic.html#26927" class="Bound"
      >B</a
      ><a name="26946"
      > </a
      ><a name="26947" class="Symbol"
      >&#8594;</a
      ><a name="26948"
      > </a
      ><a name="26949" href="Logic.html#26929" class="Bound"
      >C</a
      ><a name="26950" class="Symbol"
      >)</a
      ><a name="26951"
      > </a
      ><a name="26952" href="Logic.html#1478" class="Record Operator"
      >&#8771;</a
      ><a name="26953"
      > </a
      ><a name="26954" class="Symbol"
      >((</a
      ><a name="26956" href="Logic.html#26925" class="Bound"
      >A</a
      ><a name="26957"
      > </a
      ><a name="26958" class="Symbol"
      >&#8594;</a
      ><a name="26959"
      > </a
      ><a name="26960" href="Logic.html#26929" class="Bound"
      >C</a
      ><a name="26961" class="Symbol"
      >)</a
      ><a name="26962"
      > </a
      ><a name="26963" href="Logic.html#7202" class="Datatype Operator"
      >&#215;</a
      ><a name="26964"
      > </a
      ><a name="26965" class="Symbol"
      >(</a
      ><a name="26966" href="Logic.html#26927" class="Bound"
      >B</a
      ><a name="26967"
      > </a
      ><a name="26968" class="Symbol"
      >&#8594;</a
      ><a name="26969"
      > </a
      ><a name="26970" href="Logic.html#26929" class="Bound"
      >C</a
      ><a name="26971" class="Symbol"
      >))</a
      ><a name="26973"
      >
</a
      ><a name="26974" href="Logic.html#26904" class="Function"
      >&#8594;-distributes-&#8846;</a
      ><a name="26989"
      > </a
      ><a name="26990" class="Symbol"
      >=</a
      ><a name="26991"
      >
  </a
      ><a name="26994" class="Keyword"
      >record</a
      ><a name="27000"
      >
    </a
      ><a name="27005" class="Symbol"
      >{</a
      ><a name="27006"
      > </a
      ><a name="27007" class="Field"
      >to</a
      ><a name="27009"
      >   </a
      ><a name="27012" class="Symbol"
      >=</a
      ><a name="27013"
      > </a
      ><a name="27014" class="Symbol"
      >&#955;</a
      ><a name="27015"
      > </a
      ><a name="27016" href="Logic.html#27016" class="Bound"
      >f</a
      ><a name="27017"
      > </a
      ><a name="27018" class="Symbol"
      >&#8594;</a
      ><a name="27019"
      > </a
      ><a name="27020" class="Symbol"
      >(</a
      ><a name="27021"
      > </a
      ><a name="27022" class="Symbol"
      >(&#955;</a
      ><a name="27024"
      > </a
      ><a name="27025" href="Logic.html#27025" class="Bound"
      >x</a
      ><a name="27026"
      > </a
      ><a name="27027" class="Symbol"
      >&#8594;</a
      ><a name="27028"
      > </a
      ><a name="27029" href="Logic.html#27016" class="Bound"
      >f</a
      ><a name="27030"
      > </a
      ><a name="27031" class="Symbol"
      >(</a
      ><a name="27032" href="Logic.html#14686" class="InductiveConstructor"
      >inj&#8321;</a
      ><a name="27036"
      > </a
      ><a name="27037" href="Logic.html#27025" class="Bound"
      >x</a
      ><a name="27038" class="Symbol"
      >))</a
      ><a name="27040"
      > </a
      ><a name="27041" href="Logic.html#7232" class="InductiveConstructor Operator"
      >,</a
      ><a name="27042"
      > </a
      ><a name="27043" class="Symbol"
      >(&#955;</a
      ><a name="27045"
      > </a
      ><a name="27046" href="Logic.html#27046" class="Bound"
      >y</a
      ><a name="27047"
      > </a
      ><a name="27048" class="Symbol"
      >&#8594;</a
      ><a name="27049"
      > </a
      ><a name="27050" href="Logic.html#27016" class="Bound"
      >f</a
      ><a name="27051"
      > </a
      ><a name="27052" class="Symbol"
      >(</a
      ><a name="27053" href="Logic.html#14722" class="InductiveConstructor"
      >inj&#8322;</a
      ><a name="27057"
      > </a
      ><a name="27058" href="Logic.html#27046" class="Bound"
      >y</a
      ><a name="27059" class="Symbol"
      >))</a
      ><a name="27061"
      > </a
      ><a name="27062" class="Symbol"
      >)</a
      ><a name="27063"
      > 
    </a
      ><a name="27069" class="Symbol"
      >;</a
      ><a name="27070"
      > </a
      ><a name="27071" class="Field"
      >fro</a
      ><a name="27074"
      >  </a
      ><a name="27076" class="Symbol"
      >=</a
      ><a name="27077"
      > </a
      ><a name="27078" class="Symbol"
      >&#955;</a
      ><a name="27079"
      > </a
      ><a name="27080" class="Symbol"
      >{(</a
      ><a name="27082" href="Logic.html#27082" class="Bound"
      >g</a
      ><a name="27083"
      > </a
      ><a name="27084" href="Logic.html#7232" class="InductiveConstructor Operator"
      >,</a
      ><a name="27085"
      > </a
      ><a name="27086" href="Logic.html#27086" class="Bound"
      >h</a
      ><a name="27087" class="Symbol"
      >)</a
      ><a name="27088"
      > </a
      ><a name="27089" class="Symbol"
      >&#8594;</a
      ><a name="27090"
      > </a
      ><a name="27091" class="Symbol"
      >&#955;</a
      ><a name="27092"
      > </a
      ><a name="27093" class="Symbol"
      >{</a
      ><a name="27094"
      > </a
      ><a name="27095" class="Symbol"
      >(</a
      ><a name="27096" href="Logic.html#14686" class="InductiveConstructor"
      >inj&#8321;</a
      ><a name="27100"
      > </a
      ><a name="27101" href="Logic.html#27101" class="Bound"
      >x</a
      ><a name="27102" class="Symbol"
      >)</a
      ><a name="27103"
      > </a
      ><a name="27104" class="Symbol"
      >&#8594;</a
      ><a name="27105"
      > </a
      ><a name="27106" href="Logic.html#27082" class="Bound"
      >g</a
      ><a name="27107"
      > </a
      ><a name="27108" href="Logic.html#27101" class="Bound"
      >x</a
      ><a name="27109"
      > </a
      ><a name="27110" class="Symbol"
      >;</a
      ><a name="27111"
      > </a
      ><a name="27112" class="Symbol"
      >(</a
      ><a name="27113" href="Logic.html#14722" class="InductiveConstructor"
      >inj&#8322;</a
      ><a name="27117"
      > </a
      ><a name="27118" href="Logic.html#27118" class="Bound"
      >y</a
      ><a name="27119" class="Symbol"
      >)</a
      ><a name="27120"
      > </a
      ><a name="27121" class="Symbol"
      >&#8594;</a
      ><a name="27122"
      > </a
      ><a name="27123" href="Logic.html#27086" class="Bound"
      >h</a
      ><a name="27124"
      > </a
      ><a name="27125" href="Logic.html#27118" class="Bound"
      >y</a
      ><a name="27126"
      > </a
      ><a name="27127" class="Symbol"
      >}</a
      ><a name="27128"
      > </a
      ><a name="27129" class="Symbol"
      >}</a
      ><a name="27130"
      >
    </a
      ><a name="27135" class="Symbol"
      >;</a
      ><a name="27136"
      > </a
      ><a name="27137" class="Field"
      >inv&#737;</a
      ><a name="27141"
      > </a
      ><a name="27142" class="Symbol"
      >=</a
      ><a name="27143"
      > </a
      ><a name="27144" class="Symbol"
      >&#955;</a
      ><a name="27145"
      > </a
      ><a name="27146" href="Logic.html#27146" class="Bound"
      >f</a
      ><a name="27147"
      > </a
      ><a name="27148" class="Symbol"
      >&#8594;</a
      ><a name="27149"
      > </a
      ><a name="27150" href="Logic.html#25283" class="Postulate"
      >extensionality</a
      ><a name="27164"
      > </a
      ><a name="27165" class="Symbol"
      >(&#955;</a
      ><a name="27167"
      > </a
      ><a name="27168" class="Symbol"
      >{</a
      ><a name="27169"
      > </a
      ><a name="27170" class="Symbol"
      >(</a
      ><a name="27171" href="Logic.html#14686" class="InductiveConstructor"
      >inj&#8321;</a
      ><a name="27175"
      > </a
      ><a name="27176" href="Logic.html#27176" class="Bound"
      >x</a
      ><a name="27177" class="Symbol"
      >)</a
      ><a name="27178"
      > </a
      ><a name="27179" class="Symbol"
      >&#8594;</a
      ><a name="27180"
      > </a
      ><a name="27181" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="27185"
      > </a
      ><a name="27186" class="Symbol"
      >;</a
      ><a name="27187"
      > </a
      ><a name="27188" class="Symbol"
      >(</a
      ><a name="27189" href="Logic.html#14722" class="InductiveConstructor"
      >inj&#8322;</a
      ><a name="27193"
      > </a
      ><a name="27194" href="Logic.html#27194" class="Bound"
      >y</a
      ><a name="27195" class="Symbol"
      >)</a
      ><a name="27196"
      > </a
      ><a name="27197" class="Symbol"
      >&#8594;</a
      ><a name="27198"
      > </a
      ><a name="27199" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="27203"
      > </a
      ><a name="27204" class="Symbol"
      >})</a
      ><a name="27206"
      >
    </a
      ><a name="27211" class="Symbol"
      >;</a
      ><a name="27212"
      > </a
      ><a name="27213" class="Field"
      >inv&#691;</a
      ><a name="27217"
      > </a
      ><a name="27218" class="Symbol"
      >=</a
      ><a name="27219"
      > </a
      ><a name="27220" class="Symbol"
      >&#955;</a
      ><a name="27221"
      > </a
      ><a name="27222" class="Symbol"
      >{(</a
      ><a name="27224" href="Logic.html#27224" class="Bound"
      >g</a
      ><a name="27225"
      > </a
      ><a name="27226" href="Logic.html#7232" class="InductiveConstructor Operator"
      >,</a
      ><a name="27227"
      > </a
      ><a name="27228" href="Logic.html#27228" class="Bound"
      >h</a
      ><a name="27229" class="Symbol"
      >)</a
      ><a name="27230"
      > </a
      ><a name="27231" class="Symbol"
      >&#8594;</a
      ><a name="27232"
      > </a
      ><a name="27233" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="27237" class="Symbol"
      >}</a
      ><a name="27238"
      >
    </a
      ><a name="27243" class="Symbol"
      >}</a
      >
{% endraw %}</pre>

Corresponding to the law

    (p * n) ^ m = (p ^ m) * (n ^ m)

we have that the types `A → B × C` and `(A → B) × (A → C)` are isomorphic.
That is, the assertion that if either `A` holds then `B` holds and `C` holds
is the same as the assertion that if `A` holds then `B` holds and if
`A` holds then `C` holds.  The proof requires that we recognise the eta
rule for products, which states that `(fst w , snd w) ≡ w` for any product `w`.
<pre class="Agda">{% raw %}
<a name="27706" class="Keyword"
      >postulate</a
      ><a name="27715"
      >
  </a
      ><a name="27718" href="Logic.html#27718" class="Postulate"
      >&#951;-&#215;</a
      ><a name="27721"
      > </a
      ><a name="27722" class="Symbol"
      >:</a
      ><a name="27723"
      > </a
      ><a name="27724" class="Symbol"
      >&#8704;</a
      ><a name="27725"
      > </a
      ><a name="27726" class="Symbol"
      >{</a
      ><a name="27727" href="Logic.html#27727" class="Bound"
      >A</a
      ><a name="27728"
      > </a
      ><a name="27729" href="Logic.html#27729" class="Bound"
      >B</a
      ><a name="27730"
      > </a
      ><a name="27731" class="Symbol"
      >:</a
      ><a name="27732"
      > </a
      ><a name="27733" class="PrimitiveType"
      >Set</a
      ><a name="27736" class="Symbol"
      >}</a
      ><a name="27737"
      > </a
      ><a name="27738" class="Symbol"
      >&#8594;</a
      ><a name="27739"
      > </a
      ><a name="27740" class="Symbol"
      >&#8704;</a
      ><a name="27741"
      > </a
      ><a name="27742" class="Symbol"
      >(</a
      ><a name="27743" href="Logic.html#27743" class="Bound"
      >w</a
      ><a name="27744"
      > </a
      ><a name="27745" class="Symbol"
      >:</a
      ><a name="27746"
      > </a
      ><a name="27747" href="Logic.html#27727" class="Bound"
      >A</a
      ><a name="27748"
      > </a
      ><a name="27749" href="Logic.html#7202" class="Datatype Operator"
      >&#215;</a
      ><a name="27750"
      > </a
      ><a name="27751" href="Logic.html#27729" class="Bound"
      >B</a
      ><a name="27752" class="Symbol"
      >)</a
      ><a name="27753"
      > </a
      ><a name="27754" class="Symbol"
      >&#8594;</a
      ><a name="27755"
      > </a
      ><a name="27756" class="Symbol"
      >(</a
      ><a name="27757" href="Logic.html#7507" class="Function"
      >fst</a
      ><a name="27760"
      > </a
      ><a name="27761" href="Logic.html#27743" class="Bound"
      >w</a
      ><a name="27762"
      > </a
      ><a name="27763" href="Logic.html#7232" class="InductiveConstructor Operator"
      >,</a
      ><a name="27764"
      > </a
      ><a name="27765" href="Logic.html#7556" class="Function"
      >snd</a
      ><a name="27768"
      > </a
      ><a name="27769" href="Logic.html#27743" class="Bound"
      >w</a
      ><a name="27770" class="Symbol"
      >)</a
      ><a name="27771"
      > </a
      ><a name="27772" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="27773"
      > </a
      ><a name="27774" href="Logic.html#27743" class="Bound"
      >w</a
      ><a name="27775"
      >

</a
      ><a name="27777" href="Logic.html#27777" class="Function"
      >&#8594;-distributes-&#215;</a
      ><a name="27792"
      > </a
      ><a name="27793" class="Symbol"
      >:</a
      ><a name="27794"
      > </a
      ><a name="27795" class="Symbol"
      >&#8704;</a
      ><a name="27796"
      > </a
      ><a name="27797" class="Symbol"
      >{</a
      ><a name="27798" href="Logic.html#27798" class="Bound"
      >A</a
      ><a name="27799"
      > </a
      ><a name="27800" href="Logic.html#27800" class="Bound"
      >B</a
      ><a name="27801"
      > </a
      ><a name="27802" href="Logic.html#27802" class="Bound"
      >C</a
      ><a name="27803"
      > </a
      ><a name="27804" class="Symbol"
      >:</a
      ><a name="27805"
      > </a
      ><a name="27806" class="PrimitiveType"
      >Set</a
      ><a name="27809" class="Symbol"
      >}</a
      ><a name="27810"
      > </a
      ><a name="27811" class="Symbol"
      >&#8594;</a
      ><a name="27812"
      > </a
      ><a name="27813" class="Symbol"
      >(</a
      ><a name="27814" href="Logic.html#27798" class="Bound"
      >A</a
      ><a name="27815"
      > </a
      ><a name="27816" class="Symbol"
      >&#8594;</a
      ><a name="27817"
      > </a
      ><a name="27818" href="Logic.html#27800" class="Bound"
      >B</a
      ><a name="27819"
      > </a
      ><a name="27820" href="Logic.html#7202" class="Datatype Operator"
      >&#215;</a
      ><a name="27821"
      > </a
      ><a name="27822" href="Logic.html#27802" class="Bound"
      >C</a
      ><a name="27823" class="Symbol"
      >)</a
      ><a name="27824"
      > </a
      ><a name="27825" href="Logic.html#1478" class="Record Operator"
      >&#8771;</a
      ><a name="27826"
      > </a
      ><a name="27827" class="Symbol"
      >((</a
      ><a name="27829" href="Logic.html#27798" class="Bound"
      >A</a
      ><a name="27830"
      > </a
      ><a name="27831" class="Symbol"
      >&#8594;</a
      ><a name="27832"
      > </a
      ><a name="27833" href="Logic.html#27800" class="Bound"
      >B</a
      ><a name="27834" class="Symbol"
      >)</a
      ><a name="27835"
      > </a
      ><a name="27836" href="Logic.html#7202" class="Datatype Operator"
      >&#215;</a
      ><a name="27837"
      > </a
      ><a name="27838" class="Symbol"
      >(</a
      ><a name="27839" href="Logic.html#27798" class="Bound"
      >A</a
      ><a name="27840"
      > </a
      ><a name="27841" class="Symbol"
      >&#8594;</a
      ><a name="27842"
      > </a
      ><a name="27843" href="Logic.html#27802" class="Bound"
      >C</a
      ><a name="27844" class="Symbol"
      >))</a
      ><a name="27846"
      >
</a
      ><a name="27847" href="Logic.html#27777" class="Function"
      >&#8594;-distributes-&#215;</a
      ><a name="27862"
      > </a
      ><a name="27863" class="Symbol"
      >=</a
      ><a name="27864"
      >
  </a
      ><a name="27867" class="Keyword"
      >record</a
      ><a name="27873"
      >
    </a
      ><a name="27878" class="Symbol"
      >{</a
      ><a name="27879"
      > </a
      ><a name="27880" class="Field"
      >to</a
      ><a name="27882"
      >   </a
      ><a name="27885" class="Symbol"
      >=</a
      ><a name="27886"
      > </a
      ><a name="27887" class="Symbol"
      >&#955;</a
      ><a name="27888"
      > </a
      ><a name="27889" href="Logic.html#27889" class="Bound"
      >f</a
      ><a name="27890"
      > </a
      ><a name="27891" class="Symbol"
      >&#8594;</a
      ><a name="27892"
      > </a
      ><a name="27893" class="Symbol"
      >(</a
      ><a name="27894"
      > </a
      ><a name="27895" class="Symbol"
      >(&#955;</a
      ><a name="27897"
      > </a
      ><a name="27898" href="Logic.html#27898" class="Bound"
      >x</a
      ><a name="27899"
      > </a
      ><a name="27900" class="Symbol"
      >&#8594;</a
      ><a name="27901"
      > </a
      ><a name="27902" href="Logic.html#7507" class="Function"
      >fst</a
      ><a name="27905"
      > </a
      ><a name="27906" class="Symbol"
      >(</a
      ><a name="27907" href="Logic.html#27889" class="Bound"
      >f</a
      ><a name="27908"
      > </a
      ><a name="27909" href="Logic.html#27898" class="Bound"
      >x</a
      ><a name="27910" class="Symbol"
      >))</a
      ><a name="27912"
      > </a
      ><a name="27913" href="Logic.html#7232" class="InductiveConstructor Operator"
      >,</a
      ><a name="27914"
      > </a
      ><a name="27915" class="Symbol"
      >(&#955;</a
      ><a name="27917"
      > </a
      ><a name="27918" href="Logic.html#27918" class="Bound"
      >y</a
      ><a name="27919"
      > </a
      ><a name="27920" class="Symbol"
      >&#8594;</a
      ><a name="27921"
      > </a
      ><a name="27922" href="Logic.html#7556" class="Function"
      >snd</a
      ><a name="27925"
      > </a
      ><a name="27926" class="Symbol"
      >(</a
      ><a name="27927" href="Logic.html#27889" class="Bound"
      >f</a
      ><a name="27928"
      > </a
      ><a name="27929" href="Logic.html#27918" class="Bound"
      >y</a
      ><a name="27930" class="Symbol"
      >))</a
      ><a name="27932"
      > </a
      ><a name="27933" class="Symbol"
      >)</a
      ><a name="27934"
      > 
    </a
      ><a name="27940" class="Symbol"
      >;</a
      ><a name="27941"
      > </a
      ><a name="27942" class="Field"
      >fro</a
      ><a name="27945"
      >  </a
      ><a name="27947" class="Symbol"
      >=</a
      ><a name="27948"
      > </a
      ><a name="27949" class="Symbol"
      >&#955;</a
      ><a name="27950"
      > </a
      ><a name="27951" class="Symbol"
      >{(</a
      ><a name="27953" href="Logic.html#27953" class="Bound"
      >g</a
      ><a name="27954"
      > </a
      ><a name="27955" href="Logic.html#7232" class="InductiveConstructor Operator"
      >,</a
      ><a name="27956"
      > </a
      ><a name="27957" href="Logic.html#27957" class="Bound"
      >h</a
      ><a name="27958" class="Symbol"
      >)</a
      ><a name="27959"
      > </a
      ><a name="27960" class="Symbol"
      >&#8594;</a
      ><a name="27961"
      > </a
      ><a name="27962" class="Symbol"
      >(&#955;</a
      ><a name="27964"
      > </a
      ><a name="27965" href="Logic.html#27965" class="Bound"
      >x</a
      ><a name="27966"
      > </a
      ><a name="27967" class="Symbol"
      >&#8594;</a
      ><a name="27968"
      > </a
      ><a name="27969" class="Symbol"
      >(</a
      ><a name="27970" href="Logic.html#27953" class="Bound"
      >g</a
      ><a name="27971"
      > </a
      ><a name="27972" href="Logic.html#27965" class="Bound"
      >x</a
      ><a name="27973"
      > </a
      ><a name="27974" href="Logic.html#7232" class="InductiveConstructor Operator"
      >,</a
      ><a name="27975"
      > </a
      ><a name="27976" href="Logic.html#27957" class="Bound"
      >h</a
      ><a name="27977"
      > </a
      ><a name="27978" href="Logic.html#27965" class="Bound"
      >x</a
      ><a name="27979" class="Symbol"
      >))}</a
      ><a name="27982"
      >
    </a
      ><a name="27987" class="Symbol"
      >;</a
      ><a name="27988"
      > </a
      ><a name="27989" class="Field"
      >inv&#737;</a
      ><a name="27993"
      > </a
      ><a name="27994" class="Symbol"
      >=</a
      ><a name="27995"
      > </a
      ><a name="27996" class="Symbol"
      >&#955;</a
      ><a name="27997"
      > </a
      ><a name="27998" href="Logic.html#27998" class="Bound"
      >f</a
      ><a name="27999"
      > </a
      ><a name="28000" class="Symbol"
      >&#8594;</a
      ><a name="28001"
      > </a
      ><a name="28002" href="Logic.html#25283" class="Postulate"
      >extensionality</a
      ><a name="28016"
      > </a
      ><a name="28017" class="Symbol"
      >(&#955;</a
      ><a name="28019"
      > </a
      ><a name="28020" href="Logic.html#28020" class="Bound"
      >x</a
      ><a name="28021"
      > </a
      ><a name="28022" class="Symbol"
      >&#8594;</a
      ><a name="28023"
      > </a
      ><a name="28024" href="Logic.html#27718" class="Postulate"
      >&#951;-&#215;</a
      ><a name="28027"
      > </a
      ><a name="28028" class="Symbol"
      >(</a
      ><a name="28029" href="Logic.html#27998" class="Bound"
      >f</a
      ><a name="28030"
      > </a
      ><a name="28031" href="Logic.html#28020" class="Bound"
      >x</a
      ><a name="28032" class="Symbol"
      >))</a
      ><a name="28034"
      >
    </a
      ><a name="28039" class="Symbol"
      >;</a
      ><a name="28040"
      > </a
      ><a name="28041" class="Field"
      >inv&#691;</a
      ><a name="28045"
      > </a
      ><a name="28046" class="Symbol"
      >=</a
      ><a name="28047"
      > </a
      ><a name="28048" class="Symbol"
      >&#955;</a
      ><a name="28049"
      > </a
      ><a name="28050" class="Symbol"
      >{(</a
      ><a name="28052" href="Logic.html#28052" class="Bound"
      >g</a
      ><a name="28053"
      > </a
      ><a name="28054" href="Logic.html#7232" class="InductiveConstructor Operator"
      >,</a
      ><a name="28055"
      > </a
      ><a name="28056" href="Logic.html#28056" class="Bound"
      >h</a
      ><a name="28057" class="Symbol"
      >)</a
      ><a name="28058"
      > </a
      ><a name="28059" class="Symbol"
      >&#8594;</a
      ><a name="28060"
      > </a
      ><a name="28061" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="28065" class="Symbol"
      >}</a
      ><a name="28066"
      >
    </a
      ><a name="28071" class="Symbol"
      >}</a
      >
{% endraw %}</pre>


## Distribution

Products distributes over sum, up to isomorphism.  The code to validate
this fact is similar in structure to our previous results.
<pre class="Agda">{% raw %}
<a name="28247" href="Logic.html#28247" class="Function"
      >&#215;-distributes-&#8846;</a
      ><a name="28262"
      > </a
      ><a name="28263" class="Symbol"
      >:</a
      ><a name="28264"
      > </a
      ><a name="28265" class="Symbol"
      >&#8704;</a
      ><a name="28266"
      > </a
      ><a name="28267" class="Symbol"
      >{</a
      ><a name="28268" href="Logic.html#28268" class="Bound"
      >A</a
      ><a name="28269"
      > </a
      ><a name="28270" href="Logic.html#28270" class="Bound"
      >B</a
      ><a name="28271"
      > </a
      ><a name="28272" href="Logic.html#28272" class="Bound"
      >C</a
      ><a name="28273"
      > </a
      ><a name="28274" class="Symbol"
      >:</a
      ><a name="28275"
      > </a
      ><a name="28276" class="PrimitiveType"
      >Set</a
      ><a name="28279" class="Symbol"
      >}</a
      ><a name="28280"
      > </a
      ><a name="28281" class="Symbol"
      >&#8594;</a
      ><a name="28282"
      > </a
      ><a name="28283" class="Symbol"
      >((</a
      ><a name="28285" href="Logic.html#28268" class="Bound"
      >A</a
      ><a name="28286"
      > </a
      ><a name="28287" href="Logic.html#14656" class="Datatype Operator"
      >&#8846;</a
      ><a name="28288"
      > </a
      ><a name="28289" href="Logic.html#28270" class="Bound"
      >B</a
      ><a name="28290" class="Symbol"
      >)</a
      ><a name="28291"
      > </a
      ><a name="28292" href="Logic.html#7202" class="Datatype Operator"
      >&#215;</a
      ><a name="28293"
      > </a
      ><a name="28294" href="Logic.html#28272" class="Bound"
      >C</a
      ><a name="28295" class="Symbol"
      >)</a
      ><a name="28296"
      > </a
      ><a name="28297" href="Logic.html#1478" class="Record Operator"
      >&#8771;</a
      ><a name="28298"
      > </a
      ><a name="28299" class="Symbol"
      >((</a
      ><a name="28301" href="Logic.html#28268" class="Bound"
      >A</a
      ><a name="28302"
      > </a
      ><a name="28303" href="Logic.html#7202" class="Datatype Operator"
      >&#215;</a
      ><a name="28304"
      > </a
      ><a name="28305" href="Logic.html#28272" class="Bound"
      >C</a
      ><a name="28306" class="Symbol"
      >)</a
      ><a name="28307"
      > </a
      ><a name="28308" href="Logic.html#14656" class="Datatype Operator"
      >&#8846;</a
      ><a name="28309"
      > </a
      ><a name="28310" class="Symbol"
      >(</a
      ><a name="28311" href="Logic.html#28270" class="Bound"
      >B</a
      ><a name="28312"
      > </a
      ><a name="28313" href="Logic.html#7202" class="Datatype Operator"
      >&#215;</a
      ><a name="28314"
      > </a
      ><a name="28315" href="Logic.html#28272" class="Bound"
      >C</a
      ><a name="28316" class="Symbol"
      >))</a
      ><a name="28318"
      >
</a
      ><a name="28319" href="Logic.html#28247" class="Function"
      >&#215;-distributes-&#8846;</a
      ><a name="28334"
      > </a
      ><a name="28335" class="Symbol"
      >=</a
      ><a name="28336"
      >
  </a
      ><a name="28339" class="Keyword"
      >record</a
      ><a name="28345"
      >
    </a
      ><a name="28350" class="Symbol"
      >{</a
      ><a name="28351"
      > </a
      ><a name="28352" class="Field"
      >to</a
      ><a name="28354"
      >   </a
      ><a name="28357" class="Symbol"
      >=</a
      ><a name="28358"
      > </a
      ><a name="28359" class="Symbol"
      >&#955;</a
      ><a name="28360"
      > </a
      ><a name="28361" class="Symbol"
      >{</a
      ><a name="28362"
      > </a
      ><a name="28363" class="Symbol"
      >((</a
      ><a name="28365" href="Logic.html#14686" class="InductiveConstructor"
      >inj&#8321;</a
      ><a name="28369"
      > </a
      ><a name="28370" href="Logic.html#28370" class="Bound"
      >x</a
      ><a name="28371" class="Symbol"
      >)</a
      ><a name="28372"
      > </a
      ><a name="28373" href="Logic.html#7232" class="InductiveConstructor Operator"
      >,</a
      ><a name="28374"
      > </a
      ><a name="28375" href="Logic.html#28375" class="Bound"
      >z</a
      ><a name="28376" class="Symbol"
      >)</a
      ><a name="28377"
      > </a
      ><a name="28378" class="Symbol"
      >&#8594;</a
      ><a name="28379"
      > </a
      ><a name="28380" class="Symbol"
      >(</a
      ><a name="28381" href="Logic.html#14686" class="InductiveConstructor"
      >inj&#8321;</a
      ><a name="28385"
      > </a
      ><a name="28386" class="Symbol"
      >(</a
      ><a name="28387" href="Logic.html#28370" class="Bound"
      >x</a
      ><a name="28388"
      > </a
      ><a name="28389" href="Logic.html#7232" class="InductiveConstructor Operator"
      >,</a
      ><a name="28390"
      > </a
      ><a name="28391" href="Logic.html#28375" class="Bound"
      >z</a
      ><a name="28392" class="Symbol"
      >))</a
      ><a name="28394"
      > 
               </a
      ><a name="28411" class="Symbol"
      >;</a
      ><a name="28412"
      > </a
      ><a name="28413" class="Symbol"
      >((</a
      ><a name="28415" href="Logic.html#14722" class="InductiveConstructor"
      >inj&#8322;</a
      ><a name="28419"
      > </a
      ><a name="28420" href="Logic.html#28420" class="Bound"
      >y</a
      ><a name="28421" class="Symbol"
      >)</a
      ><a name="28422"
      > </a
      ><a name="28423" href="Logic.html#7232" class="InductiveConstructor Operator"
      >,</a
      ><a name="28424"
      > </a
      ><a name="28425" href="Logic.html#28425" class="Bound"
      >z</a
      ><a name="28426" class="Symbol"
      >)</a
      ><a name="28427"
      > </a
      ><a name="28428" class="Symbol"
      >&#8594;</a
      ><a name="28429"
      > </a
      ><a name="28430" class="Symbol"
      >(</a
      ><a name="28431" href="Logic.html#14722" class="InductiveConstructor"
      >inj&#8322;</a
      ><a name="28435"
      > </a
      ><a name="28436" class="Symbol"
      >(</a
      ><a name="28437" href="Logic.html#28420" class="Bound"
      >y</a
      ><a name="28438"
      > </a
      ><a name="28439" href="Logic.html#7232" class="InductiveConstructor Operator"
      >,</a
      ><a name="28440"
      > </a
      ><a name="28441" href="Logic.html#28425" class="Bound"
      >z</a
      ><a name="28442" class="Symbol"
      >))</a
      ><a name="28444"
      >
               </a
      ><a name="28460" class="Symbol"
      >}</a
      ><a name="28461"
      >
    </a
      ><a name="28466" class="Symbol"
      >;</a
      ><a name="28467"
      > </a
      ><a name="28468" class="Field"
      >fro</a
      ><a name="28471"
      >  </a
      ><a name="28473" class="Symbol"
      >=</a
      ><a name="28474"
      > </a
      ><a name="28475" class="Symbol"
      >&#955;</a
      ><a name="28476"
      > </a
      ><a name="28477" class="Symbol"
      >{</a
      ><a name="28478"
      > </a
      ><a name="28479" class="Symbol"
      >(</a
      ><a name="28480" href="Logic.html#14686" class="InductiveConstructor"
      >inj&#8321;</a
      ><a name="28484"
      > </a
      ><a name="28485" class="Symbol"
      >(</a
      ><a name="28486" href="Logic.html#28486" class="Bound"
      >x</a
      ><a name="28487"
      > </a
      ><a name="28488" href="Logic.html#7232" class="InductiveConstructor Operator"
      >,</a
      ><a name="28489"
      > </a
      ><a name="28490" href="Logic.html#28490" class="Bound"
      >z</a
      ><a name="28491" class="Symbol"
      >))</a
      ><a name="28493"
      > </a
      ><a name="28494" class="Symbol"
      >&#8594;</a
      ><a name="28495"
      > </a
      ><a name="28496" class="Symbol"
      >((</a
      ><a name="28498" href="Logic.html#14686" class="InductiveConstructor"
      >inj&#8321;</a
      ><a name="28502"
      > </a
      ><a name="28503" href="Logic.html#28486" class="Bound"
      >x</a
      ><a name="28504" class="Symbol"
      >)</a
      ><a name="28505"
      > </a
      ><a name="28506" href="Logic.html#7232" class="InductiveConstructor Operator"
      >,</a
      ><a name="28507"
      > </a
      ><a name="28508" href="Logic.html#28490" class="Bound"
      >z</a
      ><a name="28509" class="Symbol"
      >)</a
      ><a name="28510"
      >
               </a
      ><a name="28526" class="Symbol"
      >;</a
      ><a name="28527"
      > </a
      ><a name="28528" class="Symbol"
      >(</a
      ><a name="28529" href="Logic.html#14722" class="InductiveConstructor"
      >inj&#8322;</a
      ><a name="28533"
      > </a
      ><a name="28534" class="Symbol"
      >(</a
      ><a name="28535" href="Logic.html#28535" class="Bound"
      >y</a
      ><a name="28536"
      > </a
      ><a name="28537" href="Logic.html#7232" class="InductiveConstructor Operator"
      >,</a
      ><a name="28538"
      > </a
      ><a name="28539" href="Logic.html#28539" class="Bound"
      >z</a
      ><a name="28540" class="Symbol"
      >))</a
      ><a name="28542"
      > </a
      ><a name="28543" class="Symbol"
      >&#8594;</a
      ><a name="28544"
      > </a
      ><a name="28545" class="Symbol"
      >((</a
      ><a name="28547" href="Logic.html#14722" class="InductiveConstructor"
      >inj&#8322;</a
      ><a name="28551"
      > </a
      ><a name="28552" href="Logic.html#28535" class="Bound"
      >y</a
      ><a name="28553" class="Symbol"
      >)</a
      ><a name="28554"
      > </a
      ><a name="28555" href="Logic.html#7232" class="InductiveConstructor Operator"
      >,</a
      ><a name="28556"
      > </a
      ><a name="28557" href="Logic.html#28539" class="Bound"
      >z</a
      ><a name="28558" class="Symbol"
      >)</a
      ><a name="28559"
      >
               </a
      ><a name="28575" class="Symbol"
      >}</a
      ><a name="28576"
      >
    </a
      ><a name="28581" class="Symbol"
      >;</a
      ><a name="28582"
      > </a
      ><a name="28583" class="Field"
      >inv&#737;</a
      ><a name="28587"
      > </a
      ><a name="28588" class="Symbol"
      >=</a
      ><a name="28589"
      > </a
      ><a name="28590" class="Symbol"
      >&#955;</a
      ><a name="28591"
      > </a
      ><a name="28592" class="Symbol"
      >{</a
      ><a name="28593"
      > </a
      ><a name="28594" class="Symbol"
      >((</a
      ><a name="28596" href="Logic.html#14686" class="InductiveConstructor"
      >inj&#8321;</a
      ><a name="28600"
      > </a
      ><a name="28601" href="Logic.html#28601" class="Bound"
      >x</a
      ><a name="28602" class="Symbol"
      >)</a
      ><a name="28603"
      > </a
      ><a name="28604" href="Logic.html#7232" class="InductiveConstructor Operator"
      >,</a
      ><a name="28605"
      > </a
      ><a name="28606" href="Logic.html#28606" class="Bound"
      >z</a
      ><a name="28607" class="Symbol"
      >)</a
      ><a name="28608"
      > </a
      ><a name="28609" class="Symbol"
      >&#8594;</a
      ><a name="28610"
      > </a
      ><a name="28611" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="28615"
      >
               </a
      ><a name="28631" class="Symbol"
      >;</a
      ><a name="28632"
      > </a
      ><a name="28633" class="Symbol"
      >((</a
      ><a name="28635" href="Logic.html#14722" class="InductiveConstructor"
      >inj&#8322;</a
      ><a name="28639"
      > </a
      ><a name="28640" href="Logic.html#28640" class="Bound"
      >y</a
      ><a name="28641" class="Symbol"
      >)</a
      ><a name="28642"
      > </a
      ><a name="28643" href="Logic.html#7232" class="InductiveConstructor Operator"
      >,</a
      ><a name="28644"
      > </a
      ><a name="28645" href="Logic.html#28645" class="Bound"
      >z</a
      ><a name="28646" class="Symbol"
      >)</a
      ><a name="28647"
      > </a
      ><a name="28648" class="Symbol"
      >&#8594;</a
      ><a name="28649"
      > </a
      ><a name="28650" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="28654"
      >
               </a
      ><a name="28670" class="Symbol"
      >}</a
      ><a name="28671"
      >
    </a
      ><a name="28676" class="Symbol"
      >;</a
      ><a name="28677"
      > </a
      ><a name="28678" class="Field"
      >inv&#691;</a
      ><a name="28682"
      > </a
      ><a name="28683" class="Symbol"
      >=</a
      ><a name="28684"
      > </a
      ><a name="28685" class="Symbol"
      >&#955;</a
      ><a name="28686"
      > </a
      ><a name="28687" class="Symbol"
      >{</a
      ><a name="28688"
      > </a
      ><a name="28689" class="Symbol"
      >(</a
      ><a name="28690" href="Logic.html#14686" class="InductiveConstructor"
      >inj&#8321;</a
      ><a name="28694"
      > </a
      ><a name="28695" class="Symbol"
      >(</a
      ><a name="28696" href="Logic.html#28696" class="Bound"
      >x</a
      ><a name="28697"
      > </a
      ><a name="28698" href="Logic.html#7232" class="InductiveConstructor Operator"
      >,</a
      ><a name="28699"
      > </a
      ><a name="28700" href="Logic.html#28700" class="Bound"
      >z</a
      ><a name="28701" class="Symbol"
      >))</a
      ><a name="28703"
      > </a
      ><a name="28704" class="Symbol"
      >&#8594;</a
      ><a name="28705"
      > </a
      ><a name="28706" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="28710"
      >
               </a
      ><a name="28726" class="Symbol"
      >;</a
      ><a name="28727"
      > </a
      ><a name="28728" class="Symbol"
      >(</a
      ><a name="28729" href="Logic.html#14722" class="InductiveConstructor"
      >inj&#8322;</a
      ><a name="28733"
      > </a
      ><a name="28734" class="Symbol"
      >(</a
      ><a name="28735" href="Logic.html#28735" class="Bound"
      >y</a
      ><a name="28736"
      > </a
      ><a name="28737" href="Logic.html#7232" class="InductiveConstructor Operator"
      >,</a
      ><a name="28738"
      > </a
      ><a name="28739" href="Logic.html#28739" class="Bound"
      >z</a
      ><a name="28740" class="Symbol"
      >))</a
      ><a name="28742"
      > </a
      ><a name="28743" class="Symbol"
      >&#8594;</a
      ><a name="28744"
      > </a
      ><a name="28745" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="28749"
      >
               </a
      ><a name="28765" class="Symbol"
      >}</a
      ><a name="28766"
      >               
    </a
      ><a name="28786" class="Symbol"
      >}</a
      >
{% endraw %}</pre>

Sums do not distribute over products up to isomorphism, but it is an embedding.
<pre class="Agda">{% raw %}
<a name="28893" href="Logic.html#28893" class="Function"
      >&#8846;-distributes-&#215;</a
      ><a name="28908"
      > </a
      ><a name="28909" class="Symbol"
      >:</a
      ><a name="28910"
      > </a
      ><a name="28911" class="Symbol"
      >&#8704;</a
      ><a name="28912"
      > </a
      ><a name="28913" class="Symbol"
      >{</a
      ><a name="28914" href="Logic.html#28914" class="Bound"
      >A</a
      ><a name="28915"
      > </a
      ><a name="28916" href="Logic.html#28916" class="Bound"
      >B</a
      ><a name="28917"
      > </a
      ><a name="28918" href="Logic.html#28918" class="Bound"
      >C</a
      ><a name="28919"
      > </a
      ><a name="28920" class="Symbol"
      >:</a
      ><a name="28921"
      > </a
      ><a name="28922" class="PrimitiveType"
      >Set</a
      ><a name="28925" class="Symbol"
      >}</a
      ><a name="28926"
      > </a
      ><a name="28927" class="Symbol"
      >&#8594;</a
      ><a name="28928"
      > </a
      ><a name="28929" class="Symbol"
      >((</a
      ><a name="28931" href="Logic.html#28914" class="Bound"
      >A</a
      ><a name="28932"
      > </a
      ><a name="28933" href="Logic.html#7202" class="Datatype Operator"
      >&#215;</a
      ><a name="28934"
      > </a
      ><a name="28935" href="Logic.html#28916" class="Bound"
      >B</a
      ><a name="28936" class="Symbol"
      >)</a
      ><a name="28937"
      > </a
      ><a name="28938" href="Logic.html#14656" class="Datatype Operator"
      >&#8846;</a
      ><a name="28939"
      > </a
      ><a name="28940" href="Logic.html#28918" class="Bound"
      >C</a
      ><a name="28941" class="Symbol"
      >)</a
      ><a name="28942"
      > </a
      ><a name="28943" href="Logic.html#5152" class="Record Operator"
      >&#8818;</a
      ><a name="28944"
      > </a
      ><a name="28945" class="Symbol"
      >((</a
      ><a name="28947" href="Logic.html#28914" class="Bound"
      >A</a
      ><a name="28948"
      > </a
      ><a name="28949" href="Logic.html#14656" class="Datatype Operator"
      >&#8846;</a
      ><a name="28950"
      > </a
      ><a name="28951" href="Logic.html#28918" class="Bound"
      >C</a
      ><a name="28952" class="Symbol"
      >)</a
      ><a name="28953"
      > </a
      ><a name="28954" href="Logic.html#7202" class="Datatype Operator"
      >&#215;</a
      ><a name="28955"
      > </a
      ><a name="28956" class="Symbol"
      >(</a
      ><a name="28957" href="Logic.html#28916" class="Bound"
      >B</a
      ><a name="28958"
      > </a
      ><a name="28959" href="Logic.html#14656" class="Datatype Operator"
      >&#8846;</a
      ><a name="28960"
      > </a
      ><a name="28961" href="Logic.html#28918" class="Bound"
      >C</a
      ><a name="28962" class="Symbol"
      >))</a
      ><a name="28964"
      >
</a
      ><a name="28965" href="Logic.html#28893" class="Function"
      >&#8846;-distributes-&#215;</a
      ><a name="28980"
      > </a
      ><a name="28981" class="Symbol"
      >=</a
      ><a name="28982"
      >
  </a
      ><a name="28985" class="Keyword"
      >record</a
      ><a name="28991"
      >
    </a
      ><a name="28996" class="Symbol"
      >{</a
      ><a name="28997"
      > </a
      ><a name="28998" class="Field"
      >to</a
      ><a name="29000"
      >   </a
      ><a name="29003" class="Symbol"
      >=</a
      ><a name="29004"
      > </a
      ><a name="29005" class="Symbol"
      >&#955;</a
      ><a name="29006"
      > </a
      ><a name="29007" class="Symbol"
      >{</a
      ><a name="29008"
      > </a
      ><a name="29009" class="Symbol"
      >(</a
      ><a name="29010" href="Logic.html#14686" class="InductiveConstructor"
      >inj&#8321;</a
      ><a name="29014"
      > </a
      ><a name="29015" class="Symbol"
      >(</a
      ><a name="29016" href="Logic.html#29016" class="Bound"
      >x</a
      ><a name="29017"
      > </a
      ><a name="29018" href="Logic.html#7232" class="InductiveConstructor Operator"
      >,</a
      ><a name="29019"
      > </a
      ><a name="29020" href="Logic.html#29020" class="Bound"
      >y</a
      ><a name="29021" class="Symbol"
      >))</a
      ><a name="29023"
      > </a
      ><a name="29024" class="Symbol"
      >&#8594;</a
      ><a name="29025"
      > </a
      ><a name="29026" class="Symbol"
      >(</a
      ><a name="29027" href="Logic.html#14686" class="InductiveConstructor"
      >inj&#8321;</a
      ><a name="29031"
      > </a
      ><a name="29032" href="Logic.html#29016" class="Bound"
      >x</a
      ><a name="29033"
      > </a
      ><a name="29034" href="Logic.html#7232" class="InductiveConstructor Operator"
      >,</a
      ><a name="29035"
      > </a
      ><a name="29036" href="Logic.html#14686" class="InductiveConstructor"
      >inj&#8321;</a
      ><a name="29040"
      > </a
      ><a name="29041" href="Logic.html#29020" class="Bound"
      >y</a
      ><a name="29042" class="Symbol"
      >)</a
      ><a name="29043"
      >
               </a
      ><a name="29059" class="Symbol"
      >;</a
      ><a name="29060"
      > </a
      ><a name="29061" class="Symbol"
      >(</a
      ><a name="29062" href="Logic.html#14722" class="InductiveConstructor"
      >inj&#8322;</a
      ><a name="29066"
      > </a
      ><a name="29067" href="Logic.html#29067" class="Bound"
      >z</a
      ><a name="29068" class="Symbol"
      >)</a
      ><a name="29069"
      >       </a
      ><a name="29076" class="Symbol"
      >&#8594;</a
      ><a name="29077"
      > </a
      ><a name="29078" class="Symbol"
      >(</a
      ><a name="29079" href="Logic.html#14722" class="InductiveConstructor"
      >inj&#8322;</a
      ><a name="29083"
      > </a
      ><a name="29084" href="Logic.html#29067" class="Bound"
      >z</a
      ><a name="29085"
      > </a
      ><a name="29086" href="Logic.html#7232" class="InductiveConstructor Operator"
      >,</a
      ><a name="29087"
      > </a
      ><a name="29088" href="Logic.html#14722" class="InductiveConstructor"
      >inj&#8322;</a
      ><a name="29092"
      > </a
      ><a name="29093" href="Logic.html#29067" class="Bound"
      >z</a
      ><a name="29094" class="Symbol"
      >)</a
      ><a name="29095"
      >
               </a
      ><a name="29111" class="Symbol"
      >}</a
      ><a name="29112"
      >
    </a
      ><a name="29117" class="Symbol"
      >;</a
      ><a name="29118"
      > </a
      ><a name="29119" class="Field"
      >fro</a
      ><a name="29122"
      >  </a
      ><a name="29124" class="Symbol"
      >=</a
      ><a name="29125"
      > </a
      ><a name="29126" class="Symbol"
      >&#955;</a
      ><a name="29127"
      > </a
      ><a name="29128" class="Symbol"
      >{</a
      ><a name="29129"
      > </a
      ><a name="29130" class="Symbol"
      >(</a
      ><a name="29131" href="Logic.html#14686" class="InductiveConstructor"
      >inj&#8321;</a
      ><a name="29135"
      > </a
      ><a name="29136" href="Logic.html#29136" class="Bound"
      >x</a
      ><a name="29137"
      > </a
      ><a name="29138" href="Logic.html#7232" class="InductiveConstructor Operator"
      >,</a
      ><a name="29139"
      > </a
      ><a name="29140" href="Logic.html#14686" class="InductiveConstructor"
      >inj&#8321;</a
      ><a name="29144"
      > </a
      ><a name="29145" href="Logic.html#29145" class="Bound"
      >y</a
      ><a name="29146" class="Symbol"
      >)</a
      ><a name="29147"
      > </a
      ><a name="29148" class="Symbol"
      >&#8594;</a
      ><a name="29149"
      > </a
      ><a name="29150" class="Symbol"
      >(</a
      ><a name="29151" href="Logic.html#14686" class="InductiveConstructor"
      >inj&#8321;</a
      ><a name="29155"
      > </a
      ><a name="29156" class="Symbol"
      >(</a
      ><a name="29157" href="Logic.html#29136" class="Bound"
      >x</a
      ><a name="29158"
      > </a
      ><a name="29159" href="Logic.html#7232" class="InductiveConstructor Operator"
      >,</a
      ><a name="29160"
      > </a
      ><a name="29161" href="Logic.html#29145" class="Bound"
      >y</a
      ><a name="29162" class="Symbol"
      >))</a
      ><a name="29164"
      >
               </a
      ><a name="29180" class="Symbol"
      >;</a
      ><a name="29181"
      > </a
      ><a name="29182" class="Symbol"
      >(</a
      ><a name="29183" href="Logic.html#14686" class="InductiveConstructor"
      >inj&#8321;</a
      ><a name="29187"
      > </a
      ><a name="29188" href="Logic.html#29188" class="Bound"
      >x</a
      ><a name="29189"
      > </a
      ><a name="29190" href="Logic.html#7232" class="InductiveConstructor Operator"
      >,</a
      ><a name="29191"
      > </a
      ><a name="29192" href="Logic.html#14722" class="InductiveConstructor"
      >inj&#8322;</a
      ><a name="29196"
      > </a
      ><a name="29197" href="Logic.html#29197" class="Bound"
      >z</a
      ><a name="29198" class="Symbol"
      >)</a
      ><a name="29199"
      > </a
      ><a name="29200" class="Symbol"
      >&#8594;</a
      ><a name="29201"
      > </a
      ><a name="29202" class="Symbol"
      >(</a
      ><a name="29203" href="Logic.html#14722" class="InductiveConstructor"
      >inj&#8322;</a
      ><a name="29207"
      > </a
      ><a name="29208" href="Logic.html#29197" class="Bound"
      >z</a
      ><a name="29209" class="Symbol"
      >)</a
      ><a name="29210"
      >
               </a
      ><a name="29226" class="Symbol"
      >;</a
      ><a name="29227"
      > </a
      ><a name="29228" class="Symbol"
      >(</a
      ><a name="29229" href="Logic.html#14722" class="InductiveConstructor"
      >inj&#8322;</a
      ><a name="29233"
      > </a
      ><a name="29234" href="Logic.html#29234" class="Bound"
      >z</a
      ><a name="29235"
      > </a
      ><a name="29236" href="Logic.html#7232" class="InductiveConstructor Operator"
      >,</a
      ><a name="29237"
      > </a
      ><a name="29238" class="Symbol"
      >_</a
      ><a name="29239"
      > </a
      ><a name="29240" class="Symbol"
      >)</a
      ><a name="29241"
      >     </a
      ><a name="29246" class="Symbol"
      >&#8594;</a
      ><a name="29247"
      > </a
      ><a name="29248" class="Symbol"
      >(</a
      ><a name="29249" href="Logic.html#14722" class="InductiveConstructor"
      >inj&#8322;</a
      ><a name="29253"
      > </a
      ><a name="29254" href="Logic.html#29234" class="Bound"
      >z</a
      ><a name="29255" class="Symbol"
      >)</a
      ><a name="29256"
      >
               </a
      ><a name="29272" class="Symbol"
      >}</a
      ><a name="29273"
      >
    </a
      ><a name="29278" class="Symbol"
      >;</a
      ><a name="29279"
      > </a
      ><a name="29280" class="Field"
      >inv&#737;</a
      ><a name="29284"
      > </a
      ><a name="29285" class="Symbol"
      >=</a
      ><a name="29286"
      > </a
      ><a name="29287" class="Symbol"
      >&#955;</a
      ><a name="29288"
      > </a
      ><a name="29289" class="Symbol"
      >{</a
      ><a name="29290"
      > </a
      ><a name="29291" class="Symbol"
      >(</a
      ><a name="29292" href="Logic.html#14686" class="InductiveConstructor"
      >inj&#8321;</a
      ><a name="29296"
      > </a
      ><a name="29297" class="Symbol"
      >(</a
      ><a name="29298" href="Logic.html#29298" class="Bound"
      >x</a
      ><a name="29299"
      > </a
      ><a name="29300" href="Logic.html#7232" class="InductiveConstructor Operator"
      >,</a
      ><a name="29301"
      > </a
      ><a name="29302" href="Logic.html#29302" class="Bound"
      >y</a
      ><a name="29303" class="Symbol"
      >))</a
      ><a name="29305"
      > </a
      ><a name="29306" class="Symbol"
      >&#8594;</a
      ><a name="29307"
      > </a
      ><a name="29308" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="29312"
      >
               </a
      ><a name="29328" class="Symbol"
      >;</a
      ><a name="29329"
      > </a
      ><a name="29330" class="Symbol"
      >(</a
      ><a name="29331" href="Logic.html#14722" class="InductiveConstructor"
      >inj&#8322;</a
      ><a name="29335"
      > </a
      ><a name="29336" href="Logic.html#29336" class="Bound"
      >z</a
      ><a name="29337" class="Symbol"
      >)</a
      ><a name="29338"
      >       </a
      ><a name="29345" class="Symbol"
      >&#8594;</a
      ><a name="29346"
      > </a
      ><a name="29347" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="29351"
      >
               </a
      ><a name="29367" class="Symbol"
      >}</a
      ><a name="29368"
      >
    </a
      ><a name="29373" class="Symbol"
      >}</a
      >
{% endraw %}</pre>
Note that there is a choice in how we write the `fro` function.
As given, it takes `(inj₂ z , inj₂ z′)` to `(inj₂ z)`, but it is
easy to write a variant that instead returns `(inj₂ z′)`.  We have
an embedding rather than an isomorphism because the
`fro` function must discard either `z` or `z′` in this case.

In the usual approach to logic, both of the distribution laws
are given as equivalences, where each side implies the other:

    A & (B ∨ C) ⇔ (A & B) ∨ (A & C)
    A ∨ (B & C) ⇔ (A ∨ B) & (A ∨ C)

But when we consider the two laws in terms of evidence, where `_&_`
corresponds to `_×_` and `_∨_` corresponds to `_⊎_`, then the first
gives rise to an isomorphism, while the second only gives rise to an
embedding, revealing a sense in which one of these laws is "more
true" than the other.


## Negation

Given a proposition `A`, the negation `¬ A` holds if `A` cannot hold.
We formalise this idea by declaring negation to be the same
as implication of false. 
<pre class="Agda">{% raw %}
<a name="30370" href="Logic.html#30370" class="Function Operator"
      >&#172;_</a
      ><a name="30372"
      > </a
      ><a name="30373" class="Symbol"
      >:</a
      ><a name="30374"
      > </a
      ><a name="30375" class="PrimitiveType"
      >Set</a
      ><a name="30378"
      > </a
      ><a name="30379" class="Symbol"
      >&#8594;</a
      ><a name="30380"
      > </a
      ><a name="30381" class="PrimitiveType"
      >Set</a
      ><a name="30384"
      >
</a
      ><a name="30385" href="Logic.html#30370" class="Function Operator"
      >&#172;</a
      ><a name="30386"
      > </a
      ><a name="30387" href="Logic.html#30387" class="Bound"
      >A</a
      ><a name="30388"
      > </a
      ><a name="30389" class="Symbol"
      >=</a
      ><a name="30390"
      > </a
      ><a name="30391" href="Logic.html#30387" class="Bound"
      >A</a
      ><a name="30392"
      > </a
      ><a name="30393" class="Symbol"
      >&#8594;</a
      ><a name="30394"
      > </a
      ><a name="30395" href="Logic.html#19450" class="Datatype"
      >&#8869;</a
      >
{% endraw %}</pre>
This is a form of *proof by contradiction*: if assuming `A` leads
to the conclusion `⊥` (a contradiction), then we must have `¬ A`.

Evidence that `¬ A` holds is of the form

    λ (x : A) → N

where `N` is a term of type `⊥` containing as a free variable `x` of type `A`.
In other words, evidence that `¬ A` holds is a function that converts evidence
that `A` holds into evidence that `⊥` holds.

Given evidence that both `¬ A` and `A` hold, we can conclude that `⊥` holds.
In other words, if both `¬ A` and `A` hold, then we have a contradiction.
<pre class="Agda">{% raw %}
<a name="30970" href="Logic.html#30970" class="Function"
      >&#172;-elim</a
      ><a name="30976"
      > </a
      ><a name="30977" class="Symbol"
      >:</a
      ><a name="30978"
      > </a
      ><a name="30979" class="Symbol"
      >&#8704;</a
      ><a name="30980"
      > </a
      ><a name="30981" class="Symbol"
      >{</a
      ><a name="30982" href="Logic.html#30982" class="Bound"
      >A</a
      ><a name="30983"
      > </a
      ><a name="30984" class="Symbol"
      >:</a
      ><a name="30985"
      > </a
      ><a name="30986" class="PrimitiveType"
      >Set</a
      ><a name="30989" class="Symbol"
      >}</a
      ><a name="30990"
      > </a
      ><a name="30991" class="Symbol"
      >&#8594;</a
      ><a name="30992"
      > </a
      ><a name="30993" href="Logic.html#30370" class="Function Operator"
      >&#172;</a
      ><a name="30994"
      > </a
      ><a name="30995" href="Logic.html#30982" class="Bound"
      >A</a
      ><a name="30996"
      > </a
      ><a name="30997" class="Symbol"
      >&#8594;</a
      ><a name="30998"
      > </a
      ><a name="30999" href="Logic.html#30982" class="Bound"
      >A</a
      ><a name="31000"
      > </a
      ><a name="31001" class="Symbol"
      >&#8594;</a
      ><a name="31002"
      > </a
      ><a name="31003" href="Logic.html#19450" class="Datatype"
      >&#8869;</a
      ><a name="31004"
      >
</a
      ><a name="31005" href="Logic.html#30970" class="Function"
      >&#172;-elim</a
      ><a name="31011"
      > </a
      ><a name="31012" href="Logic.html#31012" class="Bound"
      >&#172;a</a
      ><a name="31014"
      > </a
      ><a name="31015" href="Logic.html#31015" class="Bound"
      >a</a
      ><a name="31016"
      > </a
      ><a name="31017" class="Symbol"
      >=</a
      ><a name="31018"
      > </a
      ><a name="31019" href="Logic.html#31012" class="Bound"
      >&#172;a</a
      ><a name="31021"
      > </a
      ><a name="31022" href="Logic.html#31015" class="Bound"
      >a</a
      >
{% endraw %}</pre>
Here we write `¬a` for evidence of `¬ A` and `a` for evidence of `A`.  This
means that `¬a` must be a function of type `A → ⊥`, and hence the application
`¬a a` must be of type `⊥`.  Note that this rule is just a special case of `→-elim`.

We set the precedence of negation so that it binds more tightly
than disjunction and conjunction, but more tightly than anything else.
<pre class="Agda">{% raw %}
<a name="31423" class="Keyword"
      >infix</a
      ><a name="31428"
      > </a
      ><a name="31429" class="Number"
      >3</a
      ><a name="31430"
      > </a
      ><a name="31431" href="Logic.html#30370" class="Function Operator"
      >&#172;_</a
      >
{% endraw %}</pre>
Thus, `¬ A × ¬ B` parses as `(¬ A) × (¬ B)`.

In *classical* logic, we have that `A` is equivalent to `¬ ¬ A`.
As we discuss below, in Agda we use *intuitionistic* logic, wher
we have only half of this equivalence, namely that `A` implies `¬ ¬ A`.
<pre class="Agda">{% raw %}
<a name="31706" href="Logic.html#31706" class="Function"
      >&#172;&#172;-intro</a
      ><a name="31714"
      > </a
      ><a name="31715" class="Symbol"
      >:</a
      ><a name="31716"
      > </a
      ><a name="31717" class="Symbol"
      >&#8704;</a
      ><a name="31718"
      > </a
      ><a name="31719" class="Symbol"
      >{</a
      ><a name="31720" href="Logic.html#31720" class="Bound"
      >A</a
      ><a name="31721"
      > </a
      ><a name="31722" class="Symbol"
      >:</a
      ><a name="31723"
      > </a
      ><a name="31724" class="PrimitiveType"
      >Set</a
      ><a name="31727" class="Symbol"
      >}</a
      ><a name="31728"
      > </a
      ><a name="31729" class="Symbol"
      >&#8594;</a
      ><a name="31730"
      > </a
      ><a name="31731" href="Logic.html#31720" class="Bound"
      >A</a
      ><a name="31732"
      > </a
      ><a name="31733" class="Symbol"
      >&#8594;</a
      ><a name="31734"
      > </a
      ><a name="31735" href="Logic.html#30370" class="Function Operator"
      >&#172;</a
      ><a name="31736"
      > </a
      ><a name="31737" href="Logic.html#30370" class="Function Operator"
      >&#172;</a
      ><a name="31738"
      > </a
      ><a name="31739" href="Logic.html#31720" class="Bound"
      >A</a
      ><a name="31740"
      >
</a
      ><a name="31741" href="Logic.html#31706" class="Function"
      >&#172;&#172;-intro</a
      ><a name="31749"
      > </a
      ><a name="31750" href="Logic.html#31750" class="Bound"
      >a</a
      ><a name="31751"
      > </a
      ><a name="31752" href="Logic.html#31752" class="Bound"
      >&#172;a</a
      ><a name="31754"
      > </a
      ><a name="31755" class="Symbol"
      >=</a
      ><a name="31756"
      > </a
      ><a name="31757" href="Logic.html#31752" class="Bound"
      >&#172;a</a
      ><a name="31759"
      > </a
      ><a name="31760" href="Logic.html#31750" class="Bound"
      >a</a
      >
{% endraw %}</pre>
Let `a` be evidence of `A`. We will show that assuming
`¬ A` leads to a contradiction, and hence `¬ ¬ A` must hold.
Let `¬a` be evidence of `¬ A`.  Then from `A` and `¬ A`
we have a contradiction (evidenced by `¬a a`).  Hence, we have
shown `¬ ¬ A`.

We cannot show that `¬ ¬ A` implies `A`, but we can show that
`¬ ¬ ¬ A` implies `¬ A`.
<pre class="Agda">{% raw %}
<a name="32124" href="Logic.html#32124" class="Function"
      >&#172;&#172;&#172;-elim</a
      ><a name="32132"
      > </a
      ><a name="32133" class="Symbol"
      >:</a
      ><a name="32134"
      > </a
      ><a name="32135" class="Symbol"
      >&#8704;</a
      ><a name="32136"
      > </a
      ><a name="32137" class="Symbol"
      >{</a
      ><a name="32138" href="Logic.html#32138" class="Bound"
      >A</a
      ><a name="32139"
      > </a
      ><a name="32140" class="Symbol"
      >:</a
      ><a name="32141"
      > </a
      ><a name="32142" class="PrimitiveType"
      >Set</a
      ><a name="32145" class="Symbol"
      >}</a
      ><a name="32146"
      > </a
      ><a name="32147" class="Symbol"
      >&#8594;</a
      ><a name="32148"
      > </a
      ><a name="32149" href="Logic.html#30370" class="Function Operator"
      >&#172;</a
      ><a name="32150"
      > </a
      ><a name="32151" href="Logic.html#30370" class="Function Operator"
      >&#172;</a
      ><a name="32152"
      > </a
      ><a name="32153" href="Logic.html#30370" class="Function Operator"
      >&#172;</a
      ><a name="32154"
      > </a
      ><a name="32155" href="Logic.html#32138" class="Bound"
      >A</a
      ><a name="32156"
      > </a
      ><a name="32157" class="Symbol"
      >&#8594;</a
      ><a name="32158"
      > </a
      ><a name="32159" href="Logic.html#30370" class="Function Operator"
      >&#172;</a
      ><a name="32160"
      > </a
      ><a name="32161" href="Logic.html#32138" class="Bound"
      >A</a
      ><a name="32162"
      >
</a
      ><a name="32163" href="Logic.html#32124" class="Function"
      >&#172;&#172;&#172;-elim</a
      ><a name="32171"
      > </a
      ><a name="32172" href="Logic.html#32172" class="Bound"
      >&#172;&#172;&#172;a</a
      ><a name="32176"
      > </a
      ><a name="32177" href="Logic.html#32177" class="Bound"
      >a</a
      ><a name="32178"
      > </a
      ><a name="32179" class="Symbol"
      >=</a
      ><a name="32180"
      > </a
      ><a name="32181" href="Logic.html#32172" class="Bound"
      >&#172;&#172;&#172;a</a
      ><a name="32185"
      > </a
      ><a name="32186" class="Symbol"
      >(</a
      ><a name="32187" href="Logic.html#31706" class="Function"
      >&#172;&#172;-intro</a
      ><a name="32195"
      > </a
      ><a name="32196" href="Logic.html#32177" class="Bound"
      >a</a
      ><a name="32197" class="Symbol"
      >)</a
      >
{% endraw %}</pre>
Let `¬¬¬a` be evidence of `¬ ¬ ¬ A`. We will show that assuming
`A` leads to a contradiction, and hence `¬ A` must hold.
Let `a` be evidence of `A`. Then by the previous result, we
can conclude `¬ ¬ A` (evidenced by `¬¬-intro a`).  Then from
`¬ ¬ ¬ A` and `¬ ¬ A` we have a contradiction (evidenced by
`¬¬¬a (¬¬-intro a)`.  Hence we have shown `¬ A`.

Another law of logic is the *contrapositive*,
stating that if `A` implies `B`, then `¬ B` implies `¬ A`.
<pre class="Agda">{% raw %}
<a name="32680" href="Logic.html#32680" class="Function"
      >contrapositive</a
      ><a name="32694"
      > </a
      ><a name="32695" class="Symbol"
      >:</a
      ><a name="32696"
      > </a
      ><a name="32697" class="Symbol"
      >&#8704;</a
      ><a name="32698"
      > </a
      ><a name="32699" class="Symbol"
      >{</a
      ><a name="32700" href="Logic.html#32700" class="Bound"
      >A</a
      ><a name="32701"
      > </a
      ><a name="32702" href="Logic.html#32702" class="Bound"
      >B</a
      ><a name="32703"
      > </a
      ><a name="32704" class="Symbol"
      >:</a
      ><a name="32705"
      > </a
      ><a name="32706" class="PrimitiveType"
      >Set</a
      ><a name="32709" class="Symbol"
      >}</a
      ><a name="32710"
      > </a
      ><a name="32711" class="Symbol"
      >&#8594;</a
      ><a name="32712"
      > </a
      ><a name="32713" class="Symbol"
      >(</a
      ><a name="32714" href="Logic.html#32700" class="Bound"
      >A</a
      ><a name="32715"
      > </a
      ><a name="32716" class="Symbol"
      >&#8594;</a
      ><a name="32717"
      > </a
      ><a name="32718" href="Logic.html#32702" class="Bound"
      >B</a
      ><a name="32719" class="Symbol"
      >)</a
      ><a name="32720"
      > </a
      ><a name="32721" class="Symbol"
      >&#8594;</a
      ><a name="32722"
      > </a
      ><a name="32723" class="Symbol"
      >(</a
      ><a name="32724" href="Logic.html#30370" class="Function Operator"
      >&#172;</a
      ><a name="32725"
      > </a
      ><a name="32726" href="Logic.html#32702" class="Bound"
      >B</a
      ><a name="32727"
      > </a
      ><a name="32728" class="Symbol"
      >&#8594;</a
      ><a name="32729"
      > </a
      ><a name="32730" href="Logic.html#30370" class="Function Operator"
      >&#172;</a
      ><a name="32731"
      > </a
      ><a name="32732" href="Logic.html#32700" class="Bound"
      >A</a
      ><a name="32733" class="Symbol"
      >)</a
      ><a name="32734"
      >
</a
      ><a name="32735" href="Logic.html#32680" class="Function"
      >contrapositive</a
      ><a name="32749"
      > </a
      ><a name="32750" href="Logic.html#32750" class="Bound"
      >a&#8594;b</a
      ><a name="32753"
      > </a
      ><a name="32754" href="Logic.html#32754" class="Bound"
      >&#172;b</a
      ><a name="32756"
      > </a
      ><a name="32757" href="Logic.html#32757" class="Bound"
      >a</a
      ><a name="32758"
      > </a
      ><a name="32759" class="Symbol"
      >=</a
      ><a name="32760"
      > </a
      ><a name="32761" href="Logic.html#32754" class="Bound"
      >&#172;b</a
      ><a name="32763"
      > </a
      ><a name="32764" class="Symbol"
      >(</a
      ><a name="32765" href="Logic.html#32750" class="Bound"
      >a&#8594;b</a
      ><a name="32768"
      > </a
      ><a name="32769" href="Logic.html#32757" class="Bound"
      >a</a
      ><a name="32770" class="Symbol"
      >)</a
      >
{% endraw %}</pre>
Let `a→b` be evidence of `A → B` and let `¬b` be evidence of `¬ B`.  We
will show that assuming `A` leads to a contradiction, and hence
`¬ A` must hold. Let `a` be evidence of `A`.  Then from `A → B` and
`A` we may conclude `B` (evidenced by `a→b a`), and from `B` and `¬ B`
we may conclude `⊥` (evidenced by `¬b (a→b a)`).  Hence, we have shown
`¬ A`.

Given the correspondence of implication to exponentiation and
false to the type with no members, we can view negation as
raising to the zero power.  This indeed corresponds to what
we know for arithmetic, where

    0 ^ n  =  1,  if n = 0
           =  0,  if n ≠ 0

Indeed, there is exactly one proof of `⊥ → ⊥`.
<pre class="Agda">{% raw %}
<a name="33464" href="Logic.html#33464" class="Function"
      >id</a
      ><a name="33466"
      > </a
      ><a name="33467" class="Symbol"
      >:</a
      ><a name="33468"
      > </a
      ><a name="33469" href="Logic.html#19450" class="Datatype"
      >&#8869;</a
      ><a name="33470"
      > </a
      ><a name="33471" class="Symbol"
      >&#8594;</a
      ><a name="33472"
      > </a
      ><a name="33473" href="Logic.html#19450" class="Datatype"
      >&#8869;</a
      ><a name="33474"
      >
</a
      ><a name="33475" href="Logic.html#33464" class="Function"
      >id</a
      ><a name="33477"
      > </a
      ><a name="33478" href="Logic.html#33478" class="Bound"
      >x</a
      ><a name="33479"
      > </a
      ><a name="33480" class="Symbol"
      >=</a
      ><a name="33481"
      > </a
      ><a name="33482" href="Logic.html#33478" class="Bound"
      >x</a
      >
{% endraw %}</pre>
However, there are no possible values of type `Bool → ⊥`
or `ℕ → bot`.

[TODO?: Give the proof that one cannot falsify law of the excluded middle,
including a variant of the story from Call-by-Value is Dual to Call-by-Name.]

The law of the excluded middle is irrefutable.
<pre class="Agda">{% raw %}
<a name="33781" href="Logic.html#33781" class="Function"
      >excluded-middle-irrefutable</a
      ><a name="33808"
      > </a
      ><a name="33809" class="Symbol"
      >:</a
      ><a name="33810"
      > </a
      ><a name="33811" class="Symbol"
      >&#8704;</a
      ><a name="33812"
      > </a
      ><a name="33813" class="Symbol"
      >{</a
      ><a name="33814" href="Logic.html#33814" class="Bound"
      >A</a
      ><a name="33815"
      > </a
      ><a name="33816" class="Symbol"
      >:</a
      ><a name="33817"
      > </a
      ><a name="33818" class="PrimitiveType"
      >Set</a
      ><a name="33821" class="Symbol"
      >}</a
      ><a name="33822"
      > </a
      ><a name="33823" class="Symbol"
      >&#8594;</a
      ><a name="33824"
      > </a
      ><a name="33825" href="Logic.html#30370" class="Function Operator"
      >&#172;</a
      ><a name="33826"
      > </a
      ><a name="33827" href="Logic.html#30370" class="Function Operator"
      >&#172;</a
      ><a name="33828"
      > </a
      ><a name="33829" class="Symbol"
      >(</a
      ><a name="33830" href="Logic.html#33814" class="Bound"
      >A</a
      ><a name="33831"
      > </a
      ><a name="33832" href="Logic.html#14656" class="Datatype Operator"
      >&#8846;</a
      ><a name="33833"
      > </a
      ><a name="33834" href="Logic.html#30370" class="Function Operator"
      >&#172;</a
      ><a name="33835"
      > </a
      ><a name="33836" href="Logic.html#33814" class="Bound"
      >A</a
      ><a name="33837" class="Symbol"
      >)</a
      ><a name="33838"
      >
</a
      ><a name="33839" href="Logic.html#33781" class="Function"
      >excluded-middle-irrefutable</a
      ><a name="33866"
      > </a
      ><a name="33867" href="Logic.html#33867" class="Bound"
      >k</a
      ><a name="33868"
      > </a
      ><a name="33869" class="Symbol"
      >=</a
      ><a name="33870"
      > </a
      ><a name="33871" href="Logic.html#33867" class="Bound"
      >k</a
      ><a name="33872"
      > </a
      ><a name="33873" class="Symbol"
      >(</a
      ><a name="33874" href="Logic.html#14722" class="InductiveConstructor"
      >inj&#8322;</a
      ><a name="33878"
      > </a
      ><a name="33879" class="Symbol"
      >(&#955;</a
      ><a name="33881"
      > </a
      ><a name="33882" href="Logic.html#33882" class="Bound"
      >a</a
      ><a name="33883"
      > </a
      ><a name="33884" class="Symbol"
      >&#8594;</a
      ><a name="33885"
      > </a
      ><a name="33886" href="Logic.html#33867" class="Bound"
      >k</a
      ><a name="33887"
      > </a
      ><a name="33888" class="Symbol"
      >(</a
      ><a name="33889" href="Logic.html#14686" class="InductiveConstructor"
      >inj&#8321;</a
      ><a name="33893"
      > </a
      ><a name="33894" href="Logic.html#33882" class="Bound"
      >a</a
      ><a name="33895" class="Symbol"
      >)))</a
      >
{% endraw %}</pre>


## Intuitive and Classical logic

In Gilbert and Sullivan's *The Gondoliers*, Casilda is told that
as an infant she was married to the heir of the King of Batavia, but
that due to a mix-up no one knows which of two individuals, Marco or
Giuseppe, is the heir.  Alarmed, she wails ``Then do you mean to say
that I am married to one of two gondoliers, but it is impossible to
say which?''  To which the response is ``Without any doubt of any kind
whatever.''

Logic comes in many varieties, and one distinction is between
*classical* and *intuitionistic*. Intuitionists, concerned
by cavalier assumptions made by some logicians about the nature of
infinity, insist upon a constructionist notion of truth.  In
particular, they insist that a proof of `A ⊎ B` must show
*which* of `A` or `B` holds, and hence they would reject the
claim that Casilda is married to Marco or Giuseppe until one of the
two was identified as her husband.  Perhaps Gilbert and Sullivan
anticipated intuitionism, for their story's outcome is that the heir
turns out to be a third individual, Luiz, with whom Casilda is,
conveniently, already in love.

Intuitionists also reject the law of the excluded
middle, which asserts `A ⊎ ¬ A` for every `A`, since the law
gives no clue as to *which* of `A` or `¬ A` holds. Heyting
formalised a variant of Hilbert's classical logic that captures the
intuitionistic notion of provability. In particular, the law of the
excluded middle is provable in Hilbert's logic, but not in Heyting's.
Further, if the law of the excluded middle is added as an axiom to
Heyting's logic, then it becomes equivalent to Hilbert's.
Kolmogorov
showed the two logics were closely related: he gave a double-negation
translation, such that a formula is provable in classical logic if and
only if its translation is provable in intuitionistic logic.

Propositions as Types was first formulated for intuitionistic logic.
It is a perfect fit, because in the intuitionist interpretation the
formula `A ⊎ B` is provable exactly when one exhibits either a proof
of `A` or a proof of `B`, so the type corresponding to disjunction is
a disjoint sum.

(The passage above is taken from "Propositions as Types", Philip Wadler,
*Communications of the ACM*, December 2015.)

**Exercise** Prove the following six formulas are equivalent.

<pre class="Agda">{% raw %}
<a name="36239" href="Logic.html#36239" class="Function"
      >lone</a
      ><a name="36243"
      > </a
      ><a name="36244" href="Logic.html#36244" class="Function"
      >ltwo</a
      ><a name="36248"
      > </a
      ><a name="36249" class="Symbol"
      >:</a
      ><a name="36250"
      > </a
      ><a name="36251" href="Agda.Primitive.html#408" class="Postulate"
      >Level</a
      ><a name="36256"
      >
</a
      ><a name="36257" href="Logic.html#36239" class="Function"
      >lone</a
      ><a name="36261"
      > </a
      ><a name="36262" class="Symbol"
      >=</a
      ><a name="36263"
      > </a
      ><a name="36264" href="Agda.Primitive.html#625" class="Primitive"
      >lsuc</a
      ><a name="36268"
      > </a
      ><a name="36269" href="Agda.Primitive.html#609" class="Primitive"
      >lzero</a
      ><a name="36274"
      >
</a
      ><a name="36275" href="Logic.html#36244" class="Function"
      >ltwo</a
      ><a name="36279"
      > </a
      ><a name="36280" class="Symbol"
      >=</a
      ><a name="36281"
      > </a
      ><a name="36282" href="Agda.Primitive.html#625" class="Primitive"
      >lsuc</a
      ><a name="36286"
      > </a
      ><a name="36287" href="Logic.html#36239" class="Function"
      >lone</a
      ><a name="36291"
      >

</a
      ><a name="36293" href="Logic.html#36293" class="Function"
      >&#172;&#172;-elim</a
      ><a name="36300"
      > </a
      ><a name="36301" href="Logic.html#36301" class="Function"
      >excluded-middle</a
      ><a name="36316"
      > </a
      ><a name="36317" href="Logic.html#36317" class="Function"
      >peirce</a
      ><a name="36323"
      > </a
      ><a name="36324" href="Logic.html#36324" class="Function"
      >implication</a
      ><a name="36335"
      > </a
      ><a name="36336" href="Logic.html#36336" class="Function"
      >de-morgan</a
      ><a name="36345"
      > </a
      ><a name="36346" class="Symbol"
      >:</a
      ><a name="36347"
      > </a
      ><a name="36348" class="PrimitiveType"
      >Set</a
      ><a name="36351"
      > </a
      ><a name="36352" href="Logic.html#36239" class="Function"
      >lone</a
      ><a name="36356"
      >
</a
      ><a name="36357" href="Logic.html#36293" class="Function"
      >&#172;&#172;-elim</a
      ><a name="36364"
      > </a
      ><a name="36365" class="Symbol"
      >=</a
      ><a name="36366"
      > </a
      ><a name="36367" class="Symbol"
      >&#8704;</a
      ><a name="36368"
      > </a
      ><a name="36369" class="Symbol"
      >{</a
      ><a name="36370" href="Logic.html#36370" class="Bound"
      >A</a
      ><a name="36371"
      > </a
      ><a name="36372" class="Symbol"
      >:</a
      ><a name="36373"
      > </a
      ><a name="36374" class="PrimitiveType"
      >Set</a
      ><a name="36377" class="Symbol"
      >}</a
      ><a name="36378"
      > </a
      ><a name="36379" class="Symbol"
      >&#8594;</a
      ><a name="36380"
      > </a
      ><a name="36381" href="Logic.html#30370" class="Function Operator"
      >&#172;</a
      ><a name="36382"
      > </a
      ><a name="36383" href="Logic.html#30370" class="Function Operator"
      >&#172;</a
      ><a name="36384"
      > </a
      ><a name="36385" href="Logic.html#36370" class="Bound"
      >A</a
      ><a name="36386"
      > </a
      ><a name="36387" class="Symbol"
      >&#8594;</a
      ><a name="36388"
      > </a
      ><a name="36389" href="Logic.html#36370" class="Bound"
      >A</a
      ><a name="36390"
      >
</a
      ><a name="36391" href="Logic.html#36301" class="Function"
      >excluded-middle</a
      ><a name="36406"
      > </a
      ><a name="36407" class="Symbol"
      >=</a
      ><a name="36408"
      > </a
      ><a name="36409" class="Symbol"
      >&#8704;</a
      ><a name="36410"
      > </a
      ><a name="36411" class="Symbol"
      >{</a
      ><a name="36412" href="Logic.html#36412" class="Bound"
      >A</a
      ><a name="36413"
      > </a
      ><a name="36414" class="Symbol"
      >:</a
      ><a name="36415"
      > </a
      ><a name="36416" class="PrimitiveType"
      >Set</a
      ><a name="36419" class="Symbol"
      >}</a
      ><a name="36420"
      > </a
      ><a name="36421" class="Symbol"
      >&#8594;</a
      ><a name="36422"
      > </a
      ><a name="36423" href="Logic.html#36412" class="Bound"
      >A</a
      ><a name="36424"
      > </a
      ><a name="36425" href="Logic.html#14656" class="Datatype Operator"
      >&#8846;</a
      ><a name="36426"
      > </a
      ><a name="36427" href="Logic.html#30370" class="Function Operator"
      >&#172;</a
      ><a name="36428"
      > </a
      ><a name="36429" href="Logic.html#36412" class="Bound"
      >A</a
      ><a name="36430"
      >
</a
      ><a name="36431" href="Logic.html#36317" class="Function"
      >peirce</a
      ><a name="36437"
      > </a
      ><a name="36438" class="Symbol"
      >=</a
      ><a name="36439"
      > </a
      ><a name="36440" class="Symbol"
      >&#8704;</a
      ><a name="36441"
      > </a
      ><a name="36442" class="Symbol"
      >{</a
      ><a name="36443" href="Logic.html#36443" class="Bound"
      >A</a
      ><a name="36444"
      > </a
      ><a name="36445" href="Logic.html#36445" class="Bound"
      >B</a
      ><a name="36446"
      > </a
      ><a name="36447" class="Symbol"
      >:</a
      ><a name="36448"
      > </a
      ><a name="36449" class="PrimitiveType"
      >Set</a
      ><a name="36452" class="Symbol"
      >}</a
      ><a name="36453"
      > </a
      ><a name="36454" class="Symbol"
      >&#8594;</a
      ><a name="36455"
      > </a
      ><a name="36456" class="Symbol"
      >(((</a
      ><a name="36459" href="Logic.html#36443" class="Bound"
      >A</a
      ><a name="36460"
      > </a
      ><a name="36461" class="Symbol"
      >&#8594;</a
      ><a name="36462"
      > </a
      ><a name="36463" href="Logic.html#36445" class="Bound"
      >B</a
      ><a name="36464" class="Symbol"
      >)</a
      ><a name="36465"
      > </a
      ><a name="36466" class="Symbol"
      >&#8594;</a
      ><a name="36467"
      > </a
      ><a name="36468" href="Logic.html#36443" class="Bound"
      >A</a
      ><a name="36469" class="Symbol"
      >)</a
      ><a name="36470"
      > </a
      ><a name="36471" class="Symbol"
      >&#8594;</a
      ><a name="36472"
      > </a
      ><a name="36473" href="Logic.html#36443" class="Bound"
      >A</a
      ><a name="36474" class="Symbol"
      >)</a
      ><a name="36475"
      >
</a
      ><a name="36476" href="Logic.html#36324" class="Function"
      >implication</a
      ><a name="36487"
      > </a
      ><a name="36488" class="Symbol"
      >=</a
      ><a name="36489"
      > </a
      ><a name="36490" class="Symbol"
      >&#8704;</a
      ><a name="36491"
      > </a
      ><a name="36492" class="Symbol"
      >{</a
      ><a name="36493" href="Logic.html#36493" class="Bound"
      >A</a
      ><a name="36494"
      > </a
      ><a name="36495" href="Logic.html#36495" class="Bound"
      >B</a
      ><a name="36496"
      > </a
      ><a name="36497" class="Symbol"
      >:</a
      ><a name="36498"
      > </a
      ><a name="36499" class="PrimitiveType"
      >Set</a
      ><a name="36502" class="Symbol"
      >}</a
      ><a name="36503"
      > </a
      ><a name="36504" class="Symbol"
      >&#8594;</a
      ><a name="36505"
      > </a
      ><a name="36506" class="Symbol"
      >(</a
      ><a name="36507" href="Logic.html#36493" class="Bound"
      >A</a
      ><a name="36508"
      > </a
      ><a name="36509" class="Symbol"
      >&#8594;</a
      ><a name="36510"
      > </a
      ><a name="36511" href="Logic.html#36495" class="Bound"
      >B</a
      ><a name="36512" class="Symbol"
      >)</a
      ><a name="36513"
      > </a
      ><a name="36514" class="Symbol"
      >&#8594;</a
      ><a name="36515"
      > </a
      ><a name="36516" href="Logic.html#30370" class="Function Operator"
      >&#172;</a
      ><a name="36517"
      > </a
      ><a name="36518" href="Logic.html#36493" class="Bound"
      >A</a
      ><a name="36519"
      > </a
      ><a name="36520" href="Logic.html#14656" class="Datatype Operator"
      >&#8846;</a
      ><a name="36521"
      > </a
      ><a name="36522" href="Logic.html#36495" class="Bound"
      >B</a
      ><a name="36523"
      >
</a
      ><a name="36524" href="Logic.html#36336" class="Function"
      >de-morgan</a
      ><a name="36533"
      > </a
      ><a name="36534" class="Symbol"
      >=</a
      ><a name="36535"
      > </a
      ><a name="36536" class="Symbol"
      >&#8704;</a
      ><a name="36537"
      > </a
      ><a name="36538" class="Symbol"
      >{</a
      ><a name="36539" href="Logic.html#36539" class="Bound"
      >A</a
      ><a name="36540"
      > </a
      ><a name="36541" href="Logic.html#36541" class="Bound"
      >B</a
      ><a name="36542"
      > </a
      ><a name="36543" class="Symbol"
      >:</a
      ><a name="36544"
      > </a
      ><a name="36545" class="PrimitiveType"
      >Set</a
      ><a name="36548" class="Symbol"
      >}</a
      ><a name="36549"
      > </a
      ><a name="36550" class="Symbol"
      >&#8594;</a
      ><a name="36551"
      > </a
      ><a name="36552" href="Logic.html#30370" class="Function Operator"
      >&#172;</a
      ><a name="36553"
      > </a
      ><a name="36554" class="Symbol"
      >(</a
      ><a name="36555" href="Logic.html#30370" class="Function Operator"
      >&#172;</a
      ><a name="36556"
      > </a
      ><a name="36557" href="Logic.html#36539" class="Bound"
      >A</a
      ><a name="36558"
      > </a
      ><a name="36559" href="Logic.html#7202" class="Datatype Operator"
      >&#215;</a
      ><a name="36560"
      > </a
      ><a name="36561" href="Logic.html#30370" class="Function Operator"
      >&#172;</a
      ><a name="36562"
      > </a
      ><a name="36563" href="Logic.html#36541" class="Bound"
      >B</a
      ><a name="36564" class="Symbol"
      >)</a
      ><a name="36565"
      > </a
      ><a name="36566" class="Symbol"
      >&#8594;</a
      ><a name="36567"
      > </a
      ><a name="36568" href="Logic.html#36539" class="Bound"
      >A</a
      ><a name="36569"
      > </a
      ><a name="36570" href="Logic.html#14656" class="Datatype Operator"
      >&#8846;</a
      ><a name="36571"
      > </a
      ><a name="36572" href="Logic.html#36541" class="Bound"
      >B</a
      ><a name="36573"
      >
</a
      ><a name="36574" href="Logic.html#36574" class="Function"
      >de-morgan&#8242;</a
      ><a name="36584"
      > </a
      ><a name="36585" class="Symbol"
      >=</a
      ><a name="36586"
      > </a
      ><a name="36587" class="Symbol"
      >&#8704;</a
      ><a name="36588"
      > </a
      ><a name="36589" class="Symbol"
      >{</a
      ><a name="36590" href="Logic.html#36590" class="Bound"
      >A</a
      ><a name="36591"
      > </a
      ><a name="36592" href="Logic.html#36592" class="Bound"
      >B</a
      ><a name="36593"
      > </a
      ><a name="36594" class="Symbol"
      >:</a
      ><a name="36595"
      > </a
      ><a name="36596" class="PrimitiveType"
      >Set</a
      ><a name="36599" class="Symbol"
      >}</a
      ><a name="36600"
      > </a
      ><a name="36601" class="Symbol"
      >&#8594;</a
      ><a name="36602"
      > </a
      ><a name="36603" href="Logic.html#30370" class="Function Operator"
      >&#172;</a
      ><a name="36604"
      > </a
      ><a name="36605" class="Symbol"
      >(</a
      ><a name="36606" href="Logic.html#30370" class="Function Operator"
      >&#172;</a
      ><a name="36607"
      > </a
      ><a name="36608" href="Logic.html#36590" class="Bound"
      >A</a
      ><a name="36609"
      > </a
      ><a name="36610" href="Logic.html#14656" class="Datatype Operator"
      >&#8846;</a
      ><a name="36611"
      > </a
      ><a name="36612" href="Logic.html#30370" class="Function Operator"
      >&#172;</a
      ><a name="36613"
      > </a
      ><a name="36614" href="Logic.html#36592" class="Bound"
      >B</a
      ><a name="36615" class="Symbol"
      >)</a
      ><a name="36616"
      > </a
      ><a name="36617" class="Symbol"
      >&#8594;</a
      ><a name="36618"
      > </a
      ><a name="36619" href="Logic.html#36590" class="Bound"
      >A</a
      ><a name="36620"
      > </a
      ><a name="36621" href="Logic.html#7202" class="Datatype Operator"
      >&#215;</a
      ><a name="36622"
      > </a
      ><a name="36623" href="Logic.html#36592" class="Bound"
      >B</a
      >
{% endraw %}</pre>

It turns out that an assertion such as `Set : Set` is paradoxical.
Therefore, there are an infinite number of different levels of sets,
where `Set lzero : Set lone` and `Set lone : Set ltwo`, and so on,
where `lone` is `lsuc lzero`, and `ltwo` is `lsuc lone`, analogous to
the way we represent the natural nuambers. So far, we have only used
the type `Set`, Here is the demonstration that the reverse direction of one of the five
formulas equivalent to which is equivalent to `Set lzero`.  Here, since each
of `double-negation` and the others defines a type, we need to use
`Set lone` as the "type of types".


## Universals

Given a variable `x` of type `A` and a proposition `B[x]` which
contains `x` as a free variable, the universally quantified
proposition `∀ (x : A) → B[x]` holds if for every term `M` of type
`A` the proposition `B[M]` holds.  Here `B[M]` stands for
the proposition `B[x]` with each free occurrence of `x` replaced by
`M`.  The variable `x` appears free in `B[x]` but bound in
`∀ (x : A) → B[x]`.  We formalise universal quantification using the
dependent function type, which has appeared throughout this book.

Evidence that `∀ (x : A) → B[x]` holds is of the form

    λ (x : A) → N[x]

where `N[x]` is a term of type `B[x]`; here `N[x]` is a term and `B[x]`
is a proposition (or type) both containing as a free variable `x` of
type `A`.  Given a term `L` providing evidence that `∀ (x : A) → B[x]`
holds and a term `M` of type `A`, the term `L M` provides evidence
that `B[M]` holds.  In other words, evidence that `∀ (x : A) → B[x]`
holds is a function that converts a term `M` of type `A` into evidence
that `B[M]` holds.

Put another way, if we know that `∀ (x : A) → B[x]` holds and that `M`
is a term of type `A` then we may conclude that `B[M]` holds. In
medieval times, this rule was known by the name *dictum de omni*.

If we introduce a universal and the immediately eliminate it, we can
always simplify the resulting term. Thus

    (λ (x : A) → N[x]) M

simplifies to `N[M]` of type `B[M]`, where `N[M]` stands for the term
`N[x]` with each free occurrence of `x` replaced by `M` of type `A`.

Unlike with conjunction, disjunction, and implication, there is no simple
analogy between universals and arithmetic.


## Existentials

Given a variable `x` of type `A` and a proposition `B[x]` which
contains `x` as a free variable, the existentially quantified
proposition `∃ (λ (x : A) → B[x])` holds if for some term `M` of type
`A` the proposition `B[M]` holds.  Here `B[M]` stands for
the proposition `B[x]` with each free occurrence of `x` replaced by
`M`.  The variable `x` appears free in `B[x]` but bound in
`∃ (λ (x : A) → B[x])`.

It is common to adopt a notation such as `∃[ x : A ]→ B[x]`,
which introduces `x` as a bound variable of type `A` that appears
free in `B[x]` and bound in `∃[ x : A ]→ B[x]`.  We won't do
that here, but instead use the lambda notation built-in to Agda
to introduce `x` as a bound variable.

We formalise existential quantification by declaring a suitable
inductive type.
<pre class="Agda">{% raw %}
<a name="39698" class="Keyword"
      >data</a
      ><a name="39702"
      > </a
      ><a name="39703" href="Logic.html#39703" class="Datatype"
      >&#8707;</a
      ><a name="39704"
      > </a
      ><a name="39705" class="Symbol"
      >:</a
      ><a name="39706"
      > </a
      ><a name="39707" class="Symbol"
      >&#8704;</a
      ><a name="39708"
      > </a
      ><a name="39709" class="Symbol"
      >{</a
      ><a name="39710" href="Logic.html#39710" class="Bound"
      >A</a
      ><a name="39711"
      > </a
      ><a name="39712" class="Symbol"
      >:</a
      ><a name="39713"
      > </a
      ><a name="39714" class="PrimitiveType"
      >Set</a
      ><a name="39717" class="Symbol"
      >}</a
      ><a name="39718"
      > </a
      ><a name="39719" class="Symbol"
      >&#8594;</a
      ><a name="39720"
      > </a
      ><a name="39721" class="Symbol"
      >(</a
      ><a name="39722" href="Logic.html#39710" class="Bound"
      >A</a
      ><a name="39723"
      > </a
      ><a name="39724" class="Symbol"
      >&#8594;</a
      ><a name="39725"
      > </a
      ><a name="39726" class="PrimitiveType"
      >Set</a
      ><a name="39729" class="Symbol"
      >)</a
      ><a name="39730"
      > </a
      ><a name="39731" class="Symbol"
      >&#8594;</a
      ><a name="39732"
      > </a
      ><a name="39733" class="PrimitiveType"
      >Set</a
      ><a name="39736"
      > </a
      ><a name="39737" class="Keyword"
      >where</a
      ><a name="39742"
      >
  </a
      ><a name="39745" href="Logic.html#39745" class="InductiveConstructor Operator"
      >_,_</a
      ><a name="39748"
      > </a
      ><a name="39749" class="Symbol"
      >:</a
      ><a name="39750"
      > </a
      ><a name="39751" class="Symbol"
      >&#8704;</a
      ><a name="39752"
      > </a
      ><a name="39753" class="Symbol"
      >{</a
      ><a name="39754" href="Logic.html#39754" class="Bound"
      >A</a
      ><a name="39755"
      > </a
      ><a name="39756" class="Symbol"
      >:</a
      ><a name="39757"
      > </a
      ><a name="39758" class="PrimitiveType"
      >Set</a
      ><a name="39761" class="Symbol"
      >}</a
      ><a name="39762"
      > </a
      ><a name="39763" class="Symbol"
      >{</a
      ><a name="39764" href="Logic.html#39764" class="Bound"
      >B</a
      ><a name="39765"
      > </a
      ><a name="39766" class="Symbol"
      >:</a
      ><a name="39767"
      > </a
      ><a name="39768" href="Logic.html#39754" class="Bound"
      >A</a
      ><a name="39769"
      > </a
      ><a name="39770" class="Symbol"
      >&#8594;</a
      ><a name="39771"
      > </a
      ><a name="39772" class="PrimitiveType"
      >Set</a
      ><a name="39775" class="Symbol"
      >}</a
      ><a name="39776"
      > </a
      ><a name="39777" class="Symbol"
      >&#8594;</a
      ><a name="39778"
      > </a
      ><a name="39779" class="Symbol"
      >(</a
      ><a name="39780" href="Logic.html#39780" class="Bound"
      >x</a
      ><a name="39781"
      > </a
      ><a name="39782" class="Symbol"
      >:</a
      ><a name="39783"
      > </a
      ><a name="39784" href="Logic.html#39754" class="Bound"
      >A</a
      ><a name="39785" class="Symbol"
      >)</a
      ><a name="39786"
      > </a
      ><a name="39787" class="Symbol"
      >&#8594;</a
      ><a name="39788"
      > </a
      ><a name="39789" href="Logic.html#39764" class="Bound"
      >B</a
      ><a name="39790"
      > </a
      ><a name="39791" href="Logic.html#39780" class="Bound"
      >x</a
      ><a name="39792"
      > </a
      ><a name="39793" class="Symbol"
      >&#8594;</a
      ><a name="39794"
      > </a
      ><a name="39795" href="Logic.html#39703" class="Datatype"
      >&#8707;</a
      ><a name="39796"
      > </a
      ><a name="39797" href="Logic.html#39764" class="Bound"
      >B</a
      >
{% endraw %}</pre>
Evidence that `∃ (λ (x : A) → B[x])` holds is of the form
`(M , N)` where `M` is a term of type `A`, and `N` is evidence
that `B[M]` holds.

Given evidence that `∃ (λ (x : A) → B[x])` holds, and
given evidence that `∀ (x : A) → B[x] → C` holds, where `C` does
not contain `x` as a free variable, we may conclude that `C` holds.
<pre class="Agda">{% raw %}
<a name="40151" href="Logic.html#40151" class="Function"
      >&#8707;-elim</a
      ><a name="40157"
      > </a
      ><a name="40158" class="Symbol"
      >:</a
      ><a name="40159"
      > </a
      ><a name="40160" class="Symbol"
      >&#8704;</a
      ><a name="40161"
      > </a
      ><a name="40162" class="Symbol"
      >{</a
      ><a name="40163" href="Logic.html#40163" class="Bound"
      >A</a
      ><a name="40164"
      > </a
      ><a name="40165" class="Symbol"
      >:</a
      ><a name="40166"
      > </a
      ><a name="40167" class="PrimitiveType"
      >Set</a
      ><a name="40170" class="Symbol"
      >}</a
      ><a name="40171"
      > </a
      ><a name="40172" class="Symbol"
      >{</a
      ><a name="40173" href="Logic.html#40173" class="Bound"
      >B</a
      ><a name="40174"
      > </a
      ><a name="40175" class="Symbol"
      >:</a
      ><a name="40176"
      > </a
      ><a name="40177" href="Logic.html#40163" class="Bound"
      >A</a
      ><a name="40178"
      > </a
      ><a name="40179" class="Symbol"
      >&#8594;</a
      ><a name="40180"
      > </a
      ><a name="40181" class="PrimitiveType"
      >Set</a
      ><a name="40184" class="Symbol"
      >}</a
      ><a name="40185"
      > </a
      ><a name="40186" class="Symbol"
      >{</a
      ><a name="40187" href="Logic.html#40187" class="Bound"
      >C</a
      ><a name="40188"
      > </a
      ><a name="40189" class="Symbol"
      >:</a
      ><a name="40190"
      > </a
      ><a name="40191" class="PrimitiveType"
      >Set</a
      ><a name="40194" class="Symbol"
      >}</a
      ><a name="40195"
      > </a
      ><a name="40196" class="Symbol"
      >&#8594;</a
      ><a name="40197"
      > </a
      ><a name="40198" href="Logic.html#39703" class="Datatype"
      >&#8707;</a
      ><a name="40199"
      > </a
      ><a name="40200" href="Logic.html#40173" class="Bound"
      >B</a
      ><a name="40201"
      > </a
      ><a name="40202" class="Symbol"
      >&#8594;</a
      ><a name="40203"
      > </a
      ><a name="40204" class="Symbol"
      >(&#8704;</a
      ><a name="40206"
      > </a
      ><a name="40207" class="Symbol"
      >(</a
      ><a name="40208" href="Logic.html#40208" class="Bound"
      >x</a
      ><a name="40209"
      > </a
      ><a name="40210" class="Symbol"
      >:</a
      ><a name="40211"
      > </a
      ><a name="40212" href="Logic.html#40163" class="Bound"
      >A</a
      ><a name="40213" class="Symbol"
      >)</a
      ><a name="40214"
      > </a
      ><a name="40215" class="Symbol"
      >&#8594;</a
      ><a name="40216"
      > </a
      ><a name="40217" href="Logic.html#40173" class="Bound"
      >B</a
      ><a name="40218"
      > </a
      ><a name="40219" href="Logic.html#40208" class="Bound"
      >x</a
      ><a name="40220"
      > </a
      ><a name="40221" class="Symbol"
      >&#8594;</a
      ><a name="40222"
      > </a
      ><a name="40223" href="Logic.html#40187" class="Bound"
      >C</a
      ><a name="40224" class="Symbol"
      >)</a
      ><a name="40225"
      > </a
      ><a name="40226" class="Symbol"
      >&#8594;</a
      ><a name="40227"
      > </a
      ><a name="40228" href="Logic.html#40187" class="Bound"
      >C</a
      ><a name="40229"
      >
</a
      ><a name="40230" href="Logic.html#40151" class="Function"
      >&#8707;-elim</a
      ><a name="40236"
      > </a
      ><a name="40237" class="Symbol"
      >(</a
      ><a name="40238" href="Logic.html#40238" class="Bound"
      >M</a
      ><a name="40239"
      > </a
      ><a name="40240" href="Logic.html#39745" class="InductiveConstructor Operator"
      >,</a
      ><a name="40241"
      > </a
      ><a name="40242" href="Logic.html#40242" class="Bound"
      >N</a
      ><a name="40243" class="Symbol"
      >)</a
      ><a name="40244"
      > </a
      ><a name="40245" href="Logic.html#40245" class="Bound"
      >P</a
      ><a name="40246"
      > </a
      ><a name="40247" class="Symbol"
      >=</a
      ><a name="40248"
      > </a
      ><a name="40249" href="Logic.html#40245" class="Bound"
      >P</a
      ><a name="40250"
      > </a
      ><a name="40251" href="Logic.html#40238" class="Bound"
      >M</a
      ><a name="40252"
      > </a
      ><a name="40253" href="Logic.html#40242" class="Bound"
      >N</a
      >
{% endraw %}</pre>
In other words, if we know for every `x` of type `A` that `B[x]`
implies `C`, and we know for some `x` of type `A` that `B[x]` holds,
then we may conclude that `C` holds.  This is because we may
instantiate that proof that `∀ (x : A) → B[x] → C` to any `x`, and we
may choose the particular `x` provided by the evidence that `∃ (λ (x :
A) → B[x])`.

[It would be better to have even and odd as an exercise.  Is there
a simpler example that I could start with?]

As an example, recall the definitions of `even` and `odd` from
Chapter [Relations](Relations).  
<pre class="Agda">{% raw %}
<a name="40838" class="Keyword"
      >mutual</a
      ><a name="40844"
      >
  </a
      ><a name="40847" class="Keyword"
      >data</a
      ><a name="40851"
      > </a
      ><a name="40852" href="Logic.html#40852" class="Datatype"
      >even</a
      ><a name="40856"
      > </a
      ><a name="40857" class="Symbol"
      >:</a
      ><a name="40858"
      > </a
      ><a name="40859" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#97" class="Datatype"
      >&#8469;</a
      ><a name="40860"
      > </a
      ><a name="40861" class="Symbol"
      >&#8594;</a
      ><a name="40862"
      > </a
      ><a name="40863" class="PrimitiveType"
      >Set</a
      ><a name="40866"
      > </a
      ><a name="40867" class="Keyword"
      >where</a
      ><a name="40872"
      >
    </a
      ><a name="40877" href="Logic.html#40877" class="InductiveConstructor"
      >ev-zero</a
      ><a name="40884"
      > </a
      ><a name="40885" class="Symbol"
      >:</a
      ><a name="40886"
      > </a
      ><a name="40887" href="Logic.html#40852" class="Datatype"
      >even</a
      ><a name="40891"
      > </a
      ><a name="40892" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#115" class="InductiveConstructor"
      >zero</a
      ><a name="40896"
      >
    </a
      ><a name="40901" href="Logic.html#40901" class="InductiveConstructor"
      >ev-suc</a
      ><a name="40907"
      > </a
      ><a name="40908" class="Symbol"
      >:</a
      ><a name="40909"
      > </a
      ><a name="40910" class="Symbol"
      >&#8704;</a
      ><a name="40911"
      > </a
      ><a name="40912" class="Symbol"
      >{</a
      ><a name="40913" href="Logic.html#40913" class="Bound"
      >n</a
      ><a name="40914"
      > </a
      ><a name="40915" class="Symbol"
      >:</a
      ><a name="40916"
      > </a
      ><a name="40917" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#97" class="Datatype"
      >&#8469;</a
      ><a name="40918" class="Symbol"
      >}</a
      ><a name="40919"
      > </a
      ><a name="40920" class="Symbol"
      >&#8594;</a
      ><a name="40921"
      > </a
      ><a name="40922" href="Logic.html#40950" class="Datatype"
      >odd</a
      ><a name="40925"
      > </a
      ><a name="40926" href="Logic.html#40913" class="Bound"
      >n</a
      ><a name="40927"
      > </a
      ><a name="40928" class="Symbol"
      >&#8594;</a
      ><a name="40929"
      > </a
      ><a name="40930" href="Logic.html#40852" class="Datatype"
      >even</a
      ><a name="40934"
      > </a
      ><a name="40935" class="Symbol"
      >(</a
      ><a name="40936" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor"
      >suc</a
      ><a name="40939"
      > </a
      ><a name="40940" href="Logic.html#40913" class="Bound"
      >n</a
      ><a name="40941" class="Symbol"
      >)</a
      ><a name="40942"
      >
  </a
      ><a name="40945" class="Keyword"
      >data</a
      ><a name="40949"
      > </a
      ><a name="40950" href="Logic.html#40950" class="Datatype"
      >odd</a
      ><a name="40953"
      > </a
      ><a name="40954" class="Symbol"
      >:</a
      ><a name="40955"
      > </a
      ><a name="40956" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#97" class="Datatype"
      >&#8469;</a
      ><a name="40957"
      > </a
      ><a name="40958" class="Symbol"
      >&#8594;</a
      ><a name="40959"
      > </a
      ><a name="40960" class="PrimitiveType"
      >Set</a
      ><a name="40963"
      > </a
      ><a name="40964" class="Keyword"
      >where</a
      ><a name="40969"
      >
    </a
      ><a name="40974" href="Logic.html#40974" class="InductiveConstructor"
      >od-suc</a
      ><a name="40980"
      > </a
      ><a name="40981" class="Symbol"
      >:</a
      ><a name="40982"
      > </a
      ><a name="40983" class="Symbol"
      >&#8704;</a
      ><a name="40984"
      > </a
      ><a name="40985" class="Symbol"
      >{</a
      ><a name="40986" href="Logic.html#40986" class="Bound"
      >n</a
      ><a name="40987"
      > </a
      ><a name="40988" class="Symbol"
      >:</a
      ><a name="40989"
      > </a
      ><a name="40990" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#97" class="Datatype"
      >&#8469;</a
      ><a name="40991" class="Symbol"
      >}</a
      ><a name="40992"
      > </a
      ><a name="40993" class="Symbol"
      >&#8594;</a
      ><a name="40994"
      > </a
      ><a name="40995" href="Logic.html#40852" class="Datatype"
      >even</a
      ><a name="40999"
      > </a
      ><a name="41000" href="Logic.html#40986" class="Bound"
      >n</a
      ><a name="41001"
      > </a
      ><a name="41002" class="Symbol"
      >&#8594;</a
      ><a name="41003"
      > </a
      ><a name="41004" href="Logic.html#40950" class="Datatype"
      >odd</a
      ><a name="41007"
      > </a
      ><a name="41008" class="Symbol"
      >(</a
      ><a name="41009" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor"
      >suc</a
      ><a name="41012"
      > </a
      ><a name="41013" href="Logic.html#40986" class="Bound"
      >n</a
      ><a name="41014" class="Symbol"
      >)</a
      >
{% endraw %}</pre>
We show that a number `n` is even if and only if there exists
another number `m` such that `n ≡ 2 * m`, and is odd if and only
if there is another number `m` such that `n ≡ 1 + 2 * m`.

Here is the proof in the forward direction.
<pre class="Agda">{% raw %}
<a name="41282" class="Comment"
      >
## Decidability

</a
      ><a name="41300"
      >\begin{code}
</a
      ><a name="41313" class="Keyword"
      >data</a
      ><a name="41317"
      > </a
      ><a name="41318" href="Logic.html#41318" class="Datatype"
      >Dec</a
      ><a name="41321"
      > </a
      ><a name="41322" class="Symbol"
      >:</a
      ><a name="41323"
      > </a
      ><a name="41324" class="PrimitiveType"
      >Set</a
      ><a name="41327"
      > </a
      ><a name="41328" class="Symbol"
      >&#8594;</a
      ><a name="41329"
      > </a
      ><a name="41330" class="PrimitiveType"
      >Set</a
      ><a name="41333"
      > </a
      ><a name="41334" class="Keyword"
      >where</a
      ><a name="41339"
      >
  </a
      ><a name="41342" href="Logic.html#41342" class="InductiveConstructor"
      >yes</a
      ><a name="41345"
      > </a
      ><a name="41346" class="Symbol"
      >:</a
      ><a name="41347"
      > </a
      ><a name="41348" class="Symbol"
      >&#8704;</a
      ><a name="41349"
      > </a
      ><a name="41350" class="Symbol"
      >{</a
      ><a name="41351" href="Logic.html#41351" class="Bound"
      >A</a
      ><a name="41352"
      > </a
      ><a name="41353" class="Symbol"
      >:</a
      ><a name="41354"
      > </a
      ><a name="41355" class="PrimitiveType"
      >Set</a
      ><a name="41358" class="Symbol"
      >}</a
      ><a name="41359"
      > </a
      ><a name="41360" class="Symbol"
      >&#8594;</a
      ><a name="41361"
      > </a
      ><a name="41362" href="Logic.html#41351" class="Bound"
      >A</a
      ><a name="41363"
      > </a
      ><a name="41364" class="Symbol"
      >&#8594;</a
      ><a name="41365"
      > </a
      ><a name="41366" href="Logic.html#41318" class="Datatype"
      >Dec</a
      ><a name="41369"
      > </a
      ><a name="41370" href="Logic.html#41351" class="Bound"
      >A</a
      ><a name="41371"
      >
  </a
      ><a name="41374" href="Logic.html#41374" class="InductiveConstructor"
      >no</a
      ><a name="41376"
      >  </a
      ><a name="41378" class="Symbol"
      >:</a
      ><a name="41379"
      > </a
      ><a name="41380" class="Symbol"
      >&#8704;</a
      ><a name="41381"
      > </a
      ><a name="41382" class="Symbol"
      >{</a
      ><a name="41383" href="Logic.html#41383" class="Bound"
      >A</a
      ><a name="41384"
      > </a
      ><a name="41385" class="Symbol"
      >:</a
      ><a name="41386"
      > </a
      ><a name="41387" class="PrimitiveType"
      >Set</a
      ><a name="41390" class="Symbol"
      >}</a
      ><a name="41391"
      > </a
      ><a name="41392" class="Symbol"
      >&#8594;</a
      ><a name="41393"
      > </a
      ><a name="41394" class="Symbol"
      >(</a
      ><a name="41395" href="Logic.html#30370" class="Function Operator"
      >&#172;</a
      ><a name="41396"
      > </a
      ><a name="41397" href="Logic.html#41383" class="Bound"
      >A</a
      ><a name="41398" class="Symbol"
      >)</a
      ><a name="41399"
      > </a
      ><a name="41400" class="Symbol"
      >&#8594;</a
      ><a name="41401"
      > </a
      ><a name="41402" href="Logic.html#41318" class="Datatype"
      >Dec</a
      ><a name="41405"
      > </a
      ><a name="41406" href="Logic.html#41383" class="Bound"
      >A</a
      >
{% endraw %}</pre>

## Decidability

<pre class="Agda">{% raw %}
<a name="41699" href="Logic.html#41699" class="Function"
      >dem1</a
      ><a name="41703"
      > </a
      ><a name="41704" class="Symbol"
      >:</a
      ><a name="41705"
      > </a
      ><a name="41706" class="Symbol"
      >&#8704;</a
      ><a name="41707"
      > </a
      ><a name="41708" class="Symbol"
      >{</a
      ><a name="41709" href="Logic.html#41709" class="Bound"
      >A</a
      ><a name="41710"
      > </a
      ><a name="41711" href="Logic.html#41711" class="Bound"
      >B</a
      ><a name="41712"
      > </a
      ><a name="41713" class="Symbol"
      >:</a
      ><a name="41714"
      > </a
      ><a name="41715" class="PrimitiveType"
      >Set</a
      ><a name="41718" class="Symbol"
      >}</a
      ><a name="41719"
      > </a
      ><a name="41720" class="Symbol"
      >&#8594;</a
      ><a name="41721"
      > </a
      ><a name="41722" href="Logic.html#41709" class="Bound"
      >A</a
      ><a name="41723"
      > </a
      ><a name="41724" href="Logic.html#7202" class="Datatype Operator"
      >&#215;</a
      ><a name="41725"
      > </a
      ><a name="41726" href="Logic.html#41711" class="Bound"
      >B</a
      ><a name="41727"
      > </a
      ><a name="41728" class="Symbol"
      >&#8594;</a
      ><a name="41729"
      > </a
      ><a name="41730" href="Logic.html#30370" class="Function Operator"
      >&#172;</a
      ><a name="41731"
      > </a
      ><a name="41732" class="Symbol"
      >(</a
      ><a name="41733" href="Logic.html#30370" class="Function Operator"
      >&#172;</a
      ><a name="41734"
      > </a
      ><a name="41735" href="Logic.html#41709" class="Bound"
      >A</a
      ><a name="41736"
      > </a
      ><a name="41737" href="Logic.html#14656" class="Datatype Operator"
      >&#8846;</a
      ><a name="41738"
      > </a
      ><a name="41739" href="Logic.html#30370" class="Function Operator"
      >&#172;</a
      ><a name="41740"
      > </a
      ><a name="41741" href="Logic.html#41711" class="Bound"
      >B</a
      ><a name="41742" class="Symbol"
      >)</a
      ><a name="41743"
      >
</a
      ><a name="41744" href="Logic.html#41699" class="Function"
      >dem1</a
      ><a name="41748"
      > </a
      ><a name="41749" class="Symbol"
      >(</a
      ><a name="41750" href="Logic.html#41750" class="Bound"
      >a</a
      ><a name="41751"
      > </a
      ><a name="41752" href="Logic.html#7232" class="InductiveConstructor Operator"
      >,</a
      ><a name="41753"
      > </a
      ><a name="41754" href="Logic.html#41754" class="Bound"
      >b</a
      ><a name="41755" class="Symbol"
      >)</a
      ><a name="41756"
      > </a
      ><a name="41757" class="Symbol"
      >(</a
      ><a name="41758" href="Logic.html#14686" class="InductiveConstructor"
      >inj&#8321;</a
      ><a name="41762"
      > </a
      ><a name="41763" href="Logic.html#41763" class="Bound"
      >&#172;a</a
      ><a name="41765" class="Symbol"
      >)</a
      ><a name="41766"
      > </a
      ><a name="41767" class="Symbol"
      >=</a
      ><a name="41768"
      > </a
      ><a name="41769" href="Logic.html#41763" class="Bound"
      >&#172;a</a
      ><a name="41771"
      > </a
      ><a name="41772" href="Logic.html#41750" class="Bound"
      >a</a
      ><a name="41773"
      >
</a
      ><a name="41774" href="Logic.html#41699" class="Function"
      >dem1</a
      ><a name="41778"
      > </a
      ><a name="41779" class="Symbol"
      >(</a
      ><a name="41780" href="Logic.html#41780" class="Bound"
      >a</a
      ><a name="41781"
      > </a
      ><a name="41782" href="Logic.html#7232" class="InductiveConstructor Operator"
      >,</a
      ><a name="41783"
      > </a
      ><a name="41784" href="Logic.html#41784" class="Bound"
      >b</a
      ><a name="41785" class="Symbol"
      >)</a
      ><a name="41786"
      > </a
      ><a name="41787" class="Symbol"
      >(</a
      ><a name="41788" href="Logic.html#14722" class="InductiveConstructor"
      >inj&#8322;</a
      ><a name="41792"
      > </a
      ><a name="41793" href="Logic.html#41793" class="Bound"
      >&#172;b</a
      ><a name="41795" class="Symbol"
      >)</a
      ><a name="41796"
      > </a
      ><a name="41797" class="Symbol"
      >=</a
      ><a name="41798"
      > </a
      ><a name="41799" href="Logic.html#41793" class="Bound"
      >&#172;b</a
      ><a name="41801"
      > </a
      ><a name="41802" href="Logic.html#41784" class="Bound"
      >b</a
      ><a name="41803"
      >

</a
      ><a name="41805" href="Logic.html#41805" class="Function"
      >dem2</a
      ><a name="41809"
      > </a
      ><a name="41810" class="Symbol"
      >:</a
      ><a name="41811"
      > </a
      ><a name="41812" class="Symbol"
      >&#8704;</a
      ><a name="41813"
      > </a
      ><a name="41814" class="Symbol"
      >{</a
      ><a name="41815" href="Logic.html#41815" class="Bound"
      >A</a
      ><a name="41816"
      > </a
      ><a name="41817" href="Logic.html#41817" class="Bound"
      >B</a
      ><a name="41818"
      > </a
      ><a name="41819" class="Symbol"
      >:</a
      ><a name="41820"
      > </a
      ><a name="41821" class="PrimitiveType"
      >Set</a
      ><a name="41824" class="Symbol"
      >}</a
      ><a name="41825"
      > </a
      ><a name="41826" class="Symbol"
      >&#8594;</a
      ><a name="41827"
      > </a
      ><a name="41828" href="Logic.html#41815" class="Bound"
      >A</a
      ><a name="41829"
      > </a
      ><a name="41830" href="Logic.html#14656" class="Datatype Operator"
      >&#8846;</a
      ><a name="41831"
      > </a
      ><a name="41832" href="Logic.html#41817" class="Bound"
      >B</a
      ><a name="41833"
      > </a
      ><a name="41834" class="Symbol"
      >&#8594;</a
      ><a name="41835"
      > </a
      ><a name="41836" href="Logic.html#30370" class="Function Operator"
      >&#172;</a
      ><a name="41837"
      > </a
      ><a name="41838" class="Symbol"
      >(</a
      ><a name="41839" href="Logic.html#30370" class="Function Operator"
      >&#172;</a
      ><a name="41840"
      > </a
      ><a name="41841" href="Logic.html#41815" class="Bound"
      >A</a
      ><a name="41842"
      > </a
      ><a name="41843" href="Logic.html#7202" class="Datatype Operator"
      >&#215;</a
      ><a name="41844"
      > </a
      ><a name="41845" href="Logic.html#30370" class="Function Operator"
      >&#172;</a
      ><a name="41846"
      > </a
      ><a name="41847" href="Logic.html#41817" class="Bound"
      >B</a
      ><a name="41848" class="Symbol"
      >)</a
      ><a name="41849"
      >
</a
      ><a name="41850" href="Logic.html#41805" class="Function"
      >dem2</a
      ><a name="41854"
      > </a
      ><a name="41855" class="Symbol"
      >(</a
      ><a name="41856" href="Logic.html#14686" class="InductiveConstructor"
      >inj&#8321;</a
      ><a name="41860"
      > </a
      ><a name="41861" href="Logic.html#41861" class="Bound"
      >a</a
      ><a name="41862" class="Symbol"
      >)</a
      ><a name="41863"
      > </a
      ><a name="41864" class="Symbol"
      >(</a
      ><a name="41865" href="Logic.html#41865" class="Bound"
      >&#172;a</a
      ><a name="41867"
      > </a
      ><a name="41868" href="Logic.html#7232" class="InductiveConstructor Operator"
      >,</a
      ><a name="41869"
      > </a
      ><a name="41870" href="Logic.html#41870" class="Bound"
      >&#172;b</a
      ><a name="41872" class="Symbol"
      >)</a
      ><a name="41873"
      > </a
      ><a name="41874" class="Symbol"
      >=</a
      ><a name="41875"
      > </a
      ><a name="41876" href="Logic.html#41865" class="Bound"
      >&#172;a</a
      ><a name="41878"
      > </a
      ><a name="41879" href="Logic.html#41861" class="Bound"
      >a</a
      ><a name="41880"
      >
</a
      ><a name="41881" href="Logic.html#41805" class="Function"
      >dem2</a
      ><a name="41885"
      > </a
      ><a name="41886" class="Symbol"
      >(</a
      ><a name="41887" href="Logic.html#14722" class="InductiveConstructor"
      >inj&#8322;</a
      ><a name="41891"
      > </a
      ><a name="41892" href="Logic.html#41892" class="Bound"
      >b</a
      ><a name="41893" class="Symbol"
      >)</a
      ><a name="41894"
      > </a
      ><a name="41895" class="Symbol"
      >(</a
      ><a name="41896" href="Logic.html#41896" class="Bound"
      >&#172;a</a
      ><a name="41898"
      > </a
      ><a name="41899" href="Logic.html#7232" class="InductiveConstructor Operator"
      >,</a
      ><a name="41900"
      > </a
      ><a name="41901" href="Logic.html#41901" class="Bound"
      >&#172;b</a
      ><a name="41903" class="Symbol"
      >)</a
      ><a name="41904"
      > </a
      ><a name="41905" class="Symbol"
      >=</a
      ><a name="41906"
      > </a
      ><a name="41907" href="Logic.html#41901" class="Bound"
      >&#172;b</a
      ><a name="41909"
      > </a
      ><a name="41910" href="Logic.html#41892" class="Bound"
      >b</a
      >
{% endraw %}</pre>

## Equivalence


## Unicode

This chapter introduces the following unicode.

    ≤  U+2264  LESS-THAN OR EQUAL TO (\<=, \le)


[NOTES]

Two halves of de Morgan's laws hold intuitionistically.  The other two
halves are each equivalent to the law of double negation.

<pre class="Agda">{% raw %}
<a name="42006" href="Logic.html#42006" class="Function"
      >dem-&#8771;</a
      ><a name="42011"
      > </a
      ><a name="42012" class="Symbol"
      >:</a
      ><a name="42013"
      > </a
      ><a name="42014" class="Symbol"
      >&#8704;</a
      ><a name="42015"
      > </a
      ><a name="42016" class="Symbol"
      >{</a
      ><a name="42017" href="Logic.html#42017" class="Bound"
      >A</a
      ><a name="42018"
      > </a
      ><a name="42019" href="Logic.html#42019" class="Bound"
      >B</a
      ><a name="42020"
      > </a
      ><a name="42021" class="Symbol"
      >:</a
      ><a name="42022"
      > </a
      ><a name="42023" class="PrimitiveType"
      >Set</a
      ><a name="42026" class="Symbol"
      >}</a
      ><a name="42027"
      > </a
      ><a name="42028" class="Symbol"
      >&#8594;</a
      ><a name="42029"
      > </a
      ><a name="42030" class="Symbol"
      >(</a
      ><a name="42031" href="Logic.html#30370" class="Function Operator"
      >&#172;</a
      ><a name="42032"
      > </a
      ><a name="42033" class="Symbol"
      >(</a
      ><a name="42034" href="Logic.html#42017" class="Bound"
      >A</a
      ><a name="42035"
      > </a
      ><a name="42036" href="Logic.html#14656" class="Datatype Operator"
      >&#8846;</a
      ><a name="42037"
      > </a
      ><a name="42038" href="Logic.html#42019" class="Bound"
      >B</a
      ><a name="42039" class="Symbol"
      >))</a
      ><a name="42041"
      > </a
      ><a name="42042" href="Logic.html#1478" class="Record Operator"
      >&#8771;</a
      ><a name="42043"
      > </a
      ><a name="42044" class="Symbol"
      >(</a
      ><a name="42045" href="Logic.html#30370" class="Function Operator"
      >&#172;</a
      ><a name="42046"
      > </a
      ><a name="42047" href="Logic.html#42017" class="Bound"
      >A</a
      ><a name="42048"
      > </a
      ><a name="42049" href="Logic.html#7202" class="Datatype Operator"
      >&#215;</a
      ><a name="42050"
      > </a
      ><a name="42051" href="Logic.html#30370" class="Function Operator"
      >&#172;</a
      ><a name="42052"
      > </a
      ><a name="42053" href="Logic.html#42019" class="Bound"
      >B</a
      ><a name="42054" class="Symbol"
      >)</a
      ><a name="42055"
      >
</a
      ><a name="42056" href="Logic.html#42006" class="Function"
      >dem-&#8771;</a
      ><a name="42061"
      > </a
      ><a name="42062" class="Symbol"
      >=</a
      ><a name="42063"
      > </a
      ><a name="42064" href="Logic.html#26904" class="Function"
      >&#8594;-distributes-&#8846;</a
      >
{% endraw %}</pre>

For the other variant of De Morgan's law, one way is an isomorphism.
<pre class="Agda">{% raw %}
<a name="42144" href="Logic.html#42144" class="Function"
      >dem-half</a
      ><a name="42152"
      > </a
      ><a name="42153" class="Symbol"
      >:</a
      ><a name="42154"
      > </a
      ><a name="42155" class="Symbol"
      >&#8704;</a
      ><a name="42156"
      > </a
      ><a name="42157" class="Symbol"
      >{</a
      ><a name="42158" href="Logic.html#42158" class="Bound"
      >A</a
      ><a name="42159"
      > </a
      ><a name="42160" href="Logic.html#42160" class="Bound"
      >B</a
      ><a name="42161"
      > </a
      ><a name="42162" class="Symbol"
      >:</a
      ><a name="42163"
      > </a
      ><a name="42164" class="PrimitiveType"
      >Set</a
      ><a name="42167" class="Symbol"
      >}</a
      ><a name="42168"
      > </a
      ><a name="42169" class="Symbol"
      >&#8594;</a
      ><a name="42170"
      > </a
      ><a name="42171" href="Logic.html#30370" class="Function Operator"
      >&#172;</a
      ><a name="42172"
      > </a
      ><a name="42173" href="Logic.html#42158" class="Bound"
      >A</a
      ><a name="42174"
      > </a
      ><a name="42175" href="Logic.html#14656" class="Datatype Operator"
      >&#8846;</a
      ><a name="42176"
      > </a
      ><a name="42177" href="Logic.html#30370" class="Function Operator"
      >&#172;</a
      ><a name="42178"
      > </a
      ><a name="42179" href="Logic.html#42160" class="Bound"
      >B</a
      ><a name="42180"
      > </a
      ><a name="42181" class="Symbol"
      >&#8594;</a
      ><a name="42182"
      > </a
      ><a name="42183" href="Logic.html#30370" class="Function Operator"
      >&#172;</a
      ><a name="42184"
      > </a
      ><a name="42185" class="Symbol"
      >(</a
      ><a name="42186" href="Logic.html#42158" class="Bound"
      >A</a
      ><a name="42187"
      > </a
      ><a name="42188" href="Logic.html#7202" class="Datatype Operator"
      >&#215;</a
      ><a name="42189"
      > </a
      ><a name="42190" href="Logic.html#42160" class="Bound"
      >B</a
      ><a name="42191" class="Symbol"
      >)</a
      ><a name="42192"
      >
</a
      ><a name="42193" href="Logic.html#42144" class="Function"
      >dem-half</a
      ><a name="42201"
      > </a
      ><a name="42202" class="Symbol"
      >(</a
      ><a name="42203" href="Logic.html#14686" class="InductiveConstructor"
      >inj&#8321;</a
      ><a name="42207"
      > </a
      ><a name="42208" href="Logic.html#42208" class="Bound"
      >&#172;a</a
      ><a name="42210" class="Symbol"
      >)</a
      ><a name="42211"
      > </a
      ><a name="42212" class="Symbol"
      >(</a
      ><a name="42213" href="Logic.html#42213" class="Bound"
      >a</a
      ><a name="42214"
      > </a
      ><a name="42215" href="Logic.html#7232" class="InductiveConstructor Operator"
      >,</a
      ><a name="42216"
      > </a
      ><a name="42217" href="Logic.html#42217" class="Bound"
      >b</a
      ><a name="42218" class="Symbol"
      >)</a
      ><a name="42219"
      > </a
      ><a name="42220" class="Symbol"
      >=</a
      ><a name="42221"
      > </a
      ><a name="42222" href="Logic.html#42208" class="Bound"
      >&#172;a</a
      ><a name="42224"
      > </a
      ><a name="42225" href="Logic.html#42213" class="Bound"
      >a</a
      ><a name="42226"
      >
</a
      ><a name="42227" href="Logic.html#42144" class="Function"
      >dem-half</a
      ><a name="42235"
      > </a
      ><a name="42236" class="Symbol"
      >(</a
      ><a name="42237" href="Logic.html#14722" class="InductiveConstructor"
      >inj&#8322;</a
      ><a name="42241"
      > </a
      ><a name="42242" href="Logic.html#42242" class="Bound"
      >&#172;b</a
      ><a name="42244" class="Symbol"
      >)</a
      ><a name="42245"
      > </a
      ><a name="42246" class="Symbol"
      >(</a
      ><a name="42247" href="Logic.html#42247" class="Bound"
      >a</a
      ><a name="42248"
      > </a
      ><a name="42249" href="Logic.html#7232" class="InductiveConstructor Operator"
      >,</a
      ><a name="42250"
      > </a
      ><a name="42251" href="Logic.html#42251" class="Bound"
      >b</a
      ><a name="42252" class="Symbol"
      >)</a
      ><a name="42253"
      > </a
      ><a name="42254" class="Symbol"
      >=</a
      ><a name="42255"
      > </a
      ><a name="42256" href="Logic.html#42242" class="Bound"
      >&#172;b</a
      ><a name="42258"
      > </a
      ><a name="42259" href="Logic.html#42251" class="Bound"
      >b</a
      >
{% endraw %}</pre>

The other holds in only one direction.
<pre class="Agda">{% raw %}
<a name="42585" href="Logic.html#42585" class="Function"
      >implication-inv</a
      ><a name="42600"
      > </a
      ><a name="42601" class="Symbol"
      >:</a
      ><a name="42602"
      > </a
      ><a name="42603" class="Symbol"
      >&#8704;</a
      ><a name="42604"
      > </a
      ><a name="42605" class="Symbol"
      >{</a
      ><a name="42606" href="Logic.html#42606" class="Bound"
      >A</a
      ><a name="42607"
      > </a
      ><a name="42608" href="Logic.html#42608" class="Bound"
      >B</a
      ><a name="42609"
      > </a
      ><a name="42610" class="Symbol"
      >:</a
      ><a name="42611"
      > </a
      ><a name="42612" class="PrimitiveType"
      >Set</a
      ><a name="42615" class="Symbol"
      >}</a
      ><a name="42616"
      > </a
      ><a name="42617" class="Symbol"
      >&#8594;</a
      ><a name="42618"
      > </a
      ><a name="42619" class="Symbol"
      >(</a
      ><a name="42620" href="Logic.html#30370" class="Function Operator"
      >&#172;</a
      ><a name="42621"
      > </a
      ><a name="42622" href="Logic.html#42606" class="Bound"
      >A</a
      ><a name="42623"
      > </a
      ><a name="42624" href="Logic.html#14656" class="Datatype Operator"
      >&#8846;</a
      ><a name="42625"
      > </a
      ><a name="42626" href="Logic.html#42608" class="Bound"
      >B</a
      ><a name="42627" class="Symbol"
      >)</a
      ><a name="42628"
      > </a
      ><a name="42629" class="Symbol"
      >&#8594;</a
      ><a name="42630"
      > </a
      ><a name="42631" href="Logic.html#42606" class="Bound"
      >A</a
      ><a name="42632"
      > </a
      ><a name="42633" class="Symbol"
      >&#8594;</a
      ><a name="42634"
      > </a
      ><a name="42635" href="Logic.html#42608" class="Bound"
      >B</a
      ><a name="42636"
      >
</a
      ><a name="42637" href="Logic.html#42585" class="Function"
      >implication-inv</a
      ><a name="42652"
      > </a
      ><a name="42653" class="Symbol"
      >(</a
      ><a name="42654" href="Logic.html#14686" class="InductiveConstructor"
      >inj&#8321;</a
      ><a name="42658"
      > </a
      ><a name="42659" href="Logic.html#42659" class="Bound"
      >&#172;a</a
      ><a name="42661" class="Symbol"
      >)</a
      ><a name="42662"
      > </a
      ><a name="42663" href="Logic.html#42663" class="Bound"
      >a</a
      ><a name="42664"
      > </a
      ><a name="42665" class="Symbol"
      >=</a
      ><a name="42666"
      > </a
      ><a name="42667" href="Logic.html#19890" class="Function"
      >&#8869;-elim</a
      ><a name="42673"
      > </a
      ><a name="42674" class="Symbol"
      >(</a
      ><a name="42675" href="Logic.html#42659" class="Bound"
      >&#172;a</a
      ><a name="42677"
      > </a
      ><a name="42678" href="Logic.html#42663" class="Bound"
      >a</a
      ><a name="42679" class="Symbol"
      >)</a
      ><a name="42680"
      >
</a
      ><a name="42681" href="Logic.html#42585" class="Function"
      >implication-inv</a
      ><a name="42696"
      > </a
      ><a name="42697" class="Symbol"
      >(</a
      ><a name="42698" href="Logic.html#14722" class="InductiveConstructor"
      >inj&#8322;</a
      ><a name="42702"
      > </a
      ><a name="42703" href="Logic.html#42703" class="Bound"
      >b</a
      ><a name="42704" class="Symbol"
      >)</a
      ><a name="42705"
      >  </a
      ><a name="42707" href="Logic.html#42707" class="Bound"
      >a</a
      ><a name="42708"
      > </a
      ><a name="42709" class="Symbol"
      >=</a
      ><a name="42710"
      > </a
      ><a name="42711" href="Logic.html#42703" class="Bound"
      >b</a
      ><a name="42712"
      >

</a
      ><a name="42714" href="Logic.html#42714" class="Function"
      >demorgan-inv</a
      ><a name="42726"
      > </a
      ><a name="42727" class="Symbol"
      >:</a
      ><a name="42728"
      > </a
      ><a name="42729" class="Symbol"
      >&#8704;</a
      ><a name="42730"
      > </a
      ><a name="42731" class="Symbol"
      >{</a
      ><a name="42732" href="Logic.html#42732" class="Bound"
      >A</a
      ><a name="42733"
      > </a
      ><a name="42734" href="Logic.html#42734" class="Bound"
      >B</a
      ><a name="42735"
      > </a
      ><a name="42736" class="Symbol"
      >:</a
      ><a name="42737"
      > </a
      ><a name="42738" class="PrimitiveType"
      >Set</a
      ><a name="42741" class="Symbol"
      >}</a
      ><a name="42742"
      > </a
      ><a name="42743" class="Symbol"
      >&#8594;</a
      ><a name="42744"
      > </a
      ><a name="42745" href="Logic.html#42732" class="Bound"
      >A</a
      ><a name="42746"
      > </a
      ><a name="42747" href="Logic.html#14656" class="Datatype Operator"
      >&#8846;</a
      ><a name="42748"
      > </a
      ><a name="42749" href="Logic.html#42734" class="Bound"
      >B</a
      ><a name="42750"
      > </a
      ><a name="42751" class="Symbol"
      >&#8594;</a
      ><a name="42752"
      > </a
      ><a name="42753" href="Logic.html#30370" class="Function Operator"
      >&#172;</a
      ><a name="42754"
      > </a
      ><a name="42755" class="Symbol"
      >(</a
      ><a name="42756" href="Logic.html#30370" class="Function Operator"
      >&#172;</a
      ><a name="42757"
      > </a
      ><a name="42758" href="Logic.html#42732" class="Bound"
      >A</a
      ><a name="42759"
      > </a
      ><a name="42760" href="Logic.html#7202" class="Datatype Operator"
      >&#215;</a
      ><a name="42761"
      > </a
      ><a name="42762" href="Logic.html#30370" class="Function Operator"
      >&#172;</a
      ><a name="42763"
      > </a
      ><a name="42764" href="Logic.html#42734" class="Bound"
      >B</a
      ><a name="42765" class="Symbol"
      >)</a
      ><a name="42766"
      >
</a
      ><a name="42767" href="Logic.html#42714" class="Function"
      >demorgan-inv</a
      ><a name="42779"
      > </a
      ><a name="42780" class="Symbol"
      >(</a
      ><a name="42781" href="Logic.html#14686" class="InductiveConstructor"
      >inj&#8321;</a
      ><a name="42785"
      > </a
      ><a name="42786" href="Logic.html#42786" class="Bound"
      >a</a
      ><a name="42787" class="Symbol"
      >)</a
      ><a name="42788"
      > </a
      ><a name="42789" class="Symbol"
      >(</a
      ><a name="42790" href="Logic.html#42790" class="Bound"
      >&#172;a</a
      ><a name="42792"
      > </a
      ><a name="42793" href="Logic.html#7232" class="InductiveConstructor Operator"
      >,</a
      ><a name="42794"
      > </a
      ><a name="42795" href="Logic.html#42795" class="Bound"
      >&#172;b</a
      ><a name="42797" class="Symbol"
      >)</a
      ><a name="42798"
      > </a
      ><a name="42799" class="Symbol"
      >=</a
      ><a name="42800"
      >  </a
      ><a name="42802" href="Logic.html#42790" class="Bound"
      >&#172;a</a
      ><a name="42804"
      > </a
      ><a name="42805" href="Logic.html#42786" class="Bound"
      >a</a
      ><a name="42806"
      >
</a
      ><a name="42807" href="Logic.html#42714" class="Function"
      >demorgan-inv</a
      ><a name="42819"
      > </a
      ><a name="42820" class="Symbol"
      >(</a
      ><a name="42821" href="Logic.html#14722" class="InductiveConstructor"
      >inj&#8322;</a
      ><a name="42825"
      > </a
      ><a name="42826" href="Logic.html#42826" class="Bound"
      >b</a
      ><a name="42827" class="Symbol"
      >)</a
      ><a name="42828"
      > </a
      ><a name="42829" class="Symbol"
      >(</a
      ><a name="42830" href="Logic.html#42830" class="Bound"
      >&#172;a</a
      ><a name="42832"
      > </a
      ><a name="42833" href="Logic.html#7232" class="InductiveConstructor Operator"
      >,</a
      ><a name="42834"
      > </a
      ><a name="42835" href="Logic.html#42835" class="Bound"
      >&#172;b</a
      ><a name="42837" class="Symbol"
      >)</a
      ><a name="42838"
      > </a
      ><a name="42839" class="Symbol"
      >=</a
      ><a name="42840"
      >  </a
      ><a name="42842" href="Logic.html#42835" class="Bound"
      >&#172;b</a
      ><a name="42844"
      > </a
      ><a name="42845" href="Logic.html#42826" class="Bound"
      >b</a
      >
{% endraw %}</pre>

The other variant does not appear to be equivalent to classical logic.
So that undermines my idea that basic propositions are either true
intuitionistically or equivalent to classical logic.

For several of the laws equivalent to classical logic, the reverse
direction holds in intuitionistic long.



    
