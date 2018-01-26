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
      ><a name="8395" href="Logic.html#7232" class="InductiveConstructor Operator"
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
whenever `A` holds then `B` must also hold.  We formalise this idea in
terms of the function type.  Evidence that `A → B` holds is of the form

    λ (x : A) → N

where `N` is a term of type `B` containing as a free variable `x` of type `A`.
In other words, evidence that `A → B` holds is a function that converts
evidence that `A` holds into evidence that `B` holds.

Given evidence that `A → B` holds and that `A` holds, we can conclude that
`B` holds.
<pre class="Agda">{% raw %}
<a name="22545" href="Logic.html#22545" class="Function"
      >&#8594;-elim</a
      ><a name="22551"
      > </a
      ><a name="22552" class="Symbol"
      >:</a
      ><a name="22553"
      > </a
      ><a name="22554" class="Symbol"
      >&#8704;</a
      ><a name="22555"
      > </a
      ><a name="22556" class="Symbol"
      >{</a
      ><a name="22557" href="Logic.html#22557" class="Bound"
      >A</a
      ><a name="22558"
      > </a
      ><a name="22559" href="Logic.html#22559" class="Bound"
      >B</a
      ><a name="22560"
      > </a
      ><a name="22561" class="Symbol"
      >:</a
      ><a name="22562"
      > </a
      ><a name="22563" class="PrimitiveType"
      >Set</a
      ><a name="22566" class="Symbol"
      >}</a
      ><a name="22567"
      > </a
      ><a name="22568" class="Symbol"
      >&#8594;</a
      ><a name="22569"
      > </a
      ><a name="22570" class="Symbol"
      >(</a
      ><a name="22571" href="Logic.html#22557" class="Bound"
      >A</a
      ><a name="22572"
      > </a
      ><a name="22573" class="Symbol"
      >&#8594;</a
      ><a name="22574"
      > </a
      ><a name="22575" href="Logic.html#22559" class="Bound"
      >B</a
      ><a name="22576" class="Symbol"
      >)</a
      ><a name="22577"
      > </a
      ><a name="22578" class="Symbol"
      >&#8594;</a
      ><a name="22579"
      > </a
      ><a name="22580" href="Logic.html#22557" class="Bound"
      >A</a
      ><a name="22581"
      > </a
      ><a name="22582" class="Symbol"
      >&#8594;</a
      ><a name="22583"
      > </a
      ><a name="22584" href="Logic.html#22559" class="Bound"
      >B</a
      ><a name="22585"
      >
</a
      ><a name="22586" href="Logic.html#22545" class="Function"
      >&#8594;-elim</a
      ><a name="22592"
      > </a
      ><a name="22593" href="Logic.html#22593" class="Bound"
      >f</a
      ><a name="22594"
      > </a
      ><a name="22595" href="Logic.html#22595" class="Bound"
      >x</a
      ><a name="22596"
      > </a
      ><a name="22597" class="Symbol"
      >=</a
      ><a name="22598"
      > </a
      ><a name="22599" href="Logic.html#22593" class="Bound"
      >f</a
      ><a name="22600"
      > </a
      ><a name="22601" href="Logic.html#22595" class="Bound"
      >x</a
      >
{% endraw %}</pre>
In medieval times, this rule was known by the latin name *modus ponens*.

This rule is known by its latin name, *modus ponens*.

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

    {true→aa;false→aa}  {true→aa;false→bb}  {true→aa;false→cc}
    {true→bb;false→aa}  {true→bb;false→bb}  {true→bb;false→cc}
    {true→cc;false→aa}  {true→cc;false→bb}  {true→cc;false→cc}

For example, the following function enumerates all possible
arguments of the type `Bool → Tri`:
<pre class="Agda">{% raw %}
<a name="23693" href="Logic.html#23693" class="Function"
      >&#8594;-count</a
      ><a name="23700"
      > </a
      ><a name="23701" class="Symbol"
      >:</a
      ><a name="23702"
      > </a
      ><a name="23703" class="Symbol"
      >(</a
      ><a name="23704" href="Logic.html#9008" class="Datatype"
      >Bool</a
      ><a name="23708"
      > </a
      ><a name="23709" class="Symbol"
      >&#8594;</a
      ><a name="23710"
      > </a
      ><a name="23711" href="Logic.html#9060" class="Datatype"
      >Tri</a
      ><a name="23714" class="Symbol"
      >)</a
      ><a name="23715"
      > </a
      ><a name="23716" class="Symbol"
      >&#8594;</a
      ><a name="23717"
      > </a
      ><a name="23718" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#97" class="Datatype"
      >&#8469;</a
      ><a name="23719"
      >
</a
      ><a name="23720" href="Logic.html#23693" class="Function"
      >&#8594;-count</a
      ><a name="23727"
      > </a
      ><a name="23728" href="Logic.html#23728" class="Bound"
      >f</a
      ><a name="23729"
      > </a
      ><a name="23730" class="Keyword"
      >with</a
      ><a name="23734"
      > </a
      ><a name="23735" href="Logic.html#23728" class="Bound"
      >f</a
      ><a name="23736"
      > </a
      ><a name="23737" href="Logic.html#9027" class="InductiveConstructor"
      >true</a
      ><a name="23741"
      > </a
      ><a name="23742" class="Symbol"
      >|</a
      ><a name="23743"
      > </a
      ><a name="23744" href="Logic.html#23728" class="Bound"
      >f</a
      ><a name="23745"
      > </a
      ><a name="23746" href="Logic.html#9041" class="InductiveConstructor"
      >false</a
      ><a name="23751"
      >
</a
      ><a name="23752" class="Symbol"
      >...</a
      ><a name="23755"
      >            </a
      ><a name="23767" class="Symbol"
      >|</a
      ><a name="23768"
      > </a
      ><a name="23769" href="Logic.html#9078" class="InductiveConstructor"
      >aa</a
      ><a name="23771"
      >    </a
      ><a name="23775" class="Symbol"
      >|</a
      ><a name="23776"
      > </a
      ><a name="23777" href="Logic.html#9078" class="InductiveConstructor"
      >aa</a
      ><a name="23779"
      >      </a
      ><a name="23785" class="Symbol"
      >=</a
      ><a name="23786"
      > </a
      ><a name="23787" class="Number"
      >1</a
      ><a name="23788"
      >
</a
      ><a name="23789" class="Symbol"
      >...</a
      ><a name="23792"
      >            </a
      ><a name="23804" class="Symbol"
      >|</a
      ><a name="23805"
      > </a
      ><a name="23806" href="Logic.html#9078" class="InductiveConstructor"
      >aa</a
      ><a name="23808"
      >    </a
      ><a name="23812" class="Symbol"
      >|</a
      ><a name="23813"
      > </a
      ><a name="23814" href="Logic.html#9089" class="InductiveConstructor"
      >bb</a
      ><a name="23816"
      >      </a
      ><a name="23822" class="Symbol"
      >=</a
      ><a name="23823"
      > </a
      ><a name="23824" class="Number"
      >2</a
      ><a name="23825"
      >  
</a
      ><a name="23828" class="Symbol"
      >...</a
      ><a name="23831"
      >            </a
      ><a name="23843" class="Symbol"
      >|</a
      ><a name="23844"
      > </a
      ><a name="23845" href="Logic.html#9078" class="InductiveConstructor"
      >aa</a
      ><a name="23847"
      >    </a
      ><a name="23851" class="Symbol"
      >|</a
      ><a name="23852"
      > </a
      ><a name="23853" href="Logic.html#9100" class="InductiveConstructor"
      >cc</a
      ><a name="23855"
      >      </a
      ><a name="23861" class="Symbol"
      >=</a
      ><a name="23862"
      > </a
      ><a name="23863" class="Number"
      >3</a
      ><a name="23864"
      >
</a
      ><a name="23865" class="Symbol"
      >...</a
      ><a name="23868"
      >            </a
      ><a name="23880" class="Symbol"
      >|</a
      ><a name="23881"
      > </a
      ><a name="23882" href="Logic.html#9089" class="InductiveConstructor"
      >bb</a
      ><a name="23884"
      >    </a
      ><a name="23888" class="Symbol"
      >|</a
      ><a name="23889"
      > </a
      ><a name="23890" href="Logic.html#9078" class="InductiveConstructor"
      >aa</a
      ><a name="23892"
      >      </a
      ><a name="23898" class="Symbol"
      >=</a
      ><a name="23899"
      > </a
      ><a name="23900" class="Number"
      >4</a
      ><a name="23901"
      >
</a
      ><a name="23902" class="Symbol"
      >...</a
      ><a name="23905"
      >            </a
      ><a name="23917" class="Symbol"
      >|</a
      ><a name="23918"
      > </a
      ><a name="23919" href="Logic.html#9089" class="InductiveConstructor"
      >bb</a
      ><a name="23921"
      >    </a
      ><a name="23925" class="Symbol"
      >|</a
      ><a name="23926"
      > </a
      ><a name="23927" href="Logic.html#9089" class="InductiveConstructor"
      >bb</a
      ><a name="23929"
      >      </a
      ><a name="23935" class="Symbol"
      >=</a
      ><a name="23936"
      > </a
      ><a name="23937" class="Number"
      >5</a
      ><a name="23938"
      >
</a
      ><a name="23939" class="Symbol"
      >...</a
      ><a name="23942"
      >            </a
      ><a name="23954" class="Symbol"
      >|</a
      ><a name="23955"
      > </a
      ><a name="23956" href="Logic.html#9089" class="InductiveConstructor"
      >bb</a
      ><a name="23958"
      >    </a
      ><a name="23962" class="Symbol"
      >|</a
      ><a name="23963"
      > </a
      ><a name="23964" href="Logic.html#9100" class="InductiveConstructor"
      >cc</a
      ><a name="23966"
      >      </a
      ><a name="23972" class="Symbol"
      >=</a
      ><a name="23973"
      > </a
      ><a name="23974" class="Number"
      >6</a
      ><a name="23975"
      >
</a
      ><a name="23976" class="Symbol"
      >...</a
      ><a name="23979"
      >            </a
      ><a name="23991" class="Symbol"
      >|</a
      ><a name="23992"
      > </a
      ><a name="23993" href="Logic.html#9100" class="InductiveConstructor"
      >cc</a
      ><a name="23995"
      >    </a
      ><a name="23999" class="Symbol"
      >|</a
      ><a name="24000"
      > </a
      ><a name="24001" href="Logic.html#9078" class="InductiveConstructor"
      >aa</a
      ><a name="24003"
      >      </a
      ><a name="24009" class="Symbol"
      >=</a
      ><a name="24010"
      > </a
      ><a name="24011" class="Number"
      >7</a
      ><a name="24012"
      >
</a
      ><a name="24013" class="Symbol"
      >...</a
      ><a name="24016"
      >            </a
      ><a name="24028" class="Symbol"
      >|</a
      ><a name="24029"
      > </a
      ><a name="24030" href="Logic.html#9100" class="InductiveConstructor"
      >cc</a
      ><a name="24032"
      >    </a
      ><a name="24036" class="Symbol"
      >|</a
      ><a name="24037"
      > </a
      ><a name="24038" href="Logic.html#9089" class="InductiveConstructor"
      >bb</a
      ><a name="24040"
      >      </a
      ><a name="24046" class="Symbol"
      >=</a
      ><a name="24047"
      > </a
      ><a name="24048" class="Number"
      >8</a
      ><a name="24049"
      >
</a
      ><a name="24050" class="Symbol"
      >...</a
      ><a name="24053"
      >            </a
      ><a name="24065" class="Symbol"
      >|</a
      ><a name="24066"
      > </a
      ><a name="24067" href="Logic.html#9100" class="InductiveConstructor"
      >cc</a
      ><a name="24069"
      >    </a
      ><a name="24073" class="Symbol"
      >|</a
      ><a name="24074"
      > </a
      ><a name="24075" href="Logic.html#9100" class="InductiveConstructor"
      >cc</a
      ><a name="24077"
      >      </a
      ><a name="24083" class="Symbol"
      >=</a
      ><a name="24084"
      > </a
      ><a name="24085" class="Number"
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
<a name="24638" class="Keyword"
      >postulate</a
      ><a name="24647"
      >
  </a
      ><a name="24650" href="Logic.html#24650" class="Postulate"
      >extensionality</a
      ><a name="24664"
      > </a
      ><a name="24665" class="Symbol"
      >:</a
      ><a name="24666"
      > </a
      ><a name="24667" class="Symbol"
      >&#8704;</a
      ><a name="24668"
      > </a
      ><a name="24669" class="Symbol"
      >{</a
      ><a name="24670" href="Logic.html#24670" class="Bound"
      >A</a
      ><a name="24671"
      > </a
      ><a name="24672" href="Logic.html#24672" class="Bound"
      >B</a
      ><a name="24673"
      > </a
      ><a name="24674" class="Symbol"
      >:</a
      ><a name="24675"
      > </a
      ><a name="24676" class="PrimitiveType"
      >Set</a
      ><a name="24679" class="Symbol"
      >}</a
      ><a name="24680"
      > </a
      ><a name="24681" class="Symbol"
      >&#8594;</a
      ><a name="24682"
      > </a
      ><a name="24683" class="Symbol"
      >{</a
      ><a name="24684" href="Logic.html#24684" class="Bound"
      >f</a
      ><a name="24685"
      > </a
      ><a name="24686" href="Logic.html#24686" class="Bound"
      >g</a
      ><a name="24687"
      > </a
      ><a name="24688" class="Symbol"
      >:</a
      ><a name="24689"
      > </a
      ><a name="24690" href="Logic.html#24670" class="Bound"
      >A</a
      ><a name="24691"
      > </a
      ><a name="24692" class="Symbol"
      >&#8594;</a
      ><a name="24693"
      > </a
      ><a name="24694" href="Logic.html#24672" class="Bound"
      >B</a
      ><a name="24695" class="Symbol"
      >}</a
      ><a name="24696"
      > </a
      ><a name="24697" class="Symbol"
      >&#8594;</a
      ><a name="24698"
      > </a
      ><a name="24699" class="Symbol"
      >(&#8704;</a
      ><a name="24701"
      > </a
      ><a name="24702" class="Symbol"
      >(</a
      ><a name="24703" href="Logic.html#24703" class="Bound"
      >x</a
      ><a name="24704"
      > </a
      ><a name="24705" class="Symbol"
      >:</a
      ><a name="24706"
      > </a
      ><a name="24707" href="Logic.html#24670" class="Bound"
      >A</a
      ><a name="24708" class="Symbol"
      >)</a
      ><a name="24709"
      > </a
      ><a name="24710" class="Symbol"
      >&#8594;</a
      ><a name="24711"
      > </a
      ><a name="24712" href="Logic.html#24684" class="Bound"
      >f</a
      ><a name="24713"
      > </a
      ><a name="24714" href="Logic.html#24703" class="Bound"
      >x</a
      ><a name="24715"
      > </a
      ><a name="24716" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="24717"
      > </a
      ><a name="24718" href="Logic.html#24686" class="Bound"
      >g</a
      ><a name="24719"
      > </a
      ><a name="24720" href="Logic.html#24703" class="Bound"
      >x</a
      ><a name="24721" class="Symbol"
      >)</a
      ><a name="24722"
      > </a
      ><a name="24723" class="Symbol"
      >&#8594;</a
      ><a name="24724"
      > </a
      ><a name="24725" href="Logic.html#24684" class="Bound"
      >f</a
      ><a name="24726"
      > </a
      ><a name="24727" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="24728"
      > </a
      ><a name="24729" href="Logic.html#24686" class="Bound"
      >g</a
      ><a name="24730"
      >
  
</a
      ><a name="24734" href="Logic.html#24734" class="Function"
      >currying</a
      ><a name="24742"
      > </a
      ><a name="24743" class="Symbol"
      >:</a
      ><a name="24744"
      > </a
      ><a name="24745" class="Symbol"
      >&#8704;</a
      ><a name="24746"
      > </a
      ><a name="24747" class="Symbol"
      >{</a
      ><a name="24748" href="Logic.html#24748" class="Bound"
      >A</a
      ><a name="24749"
      > </a
      ><a name="24750" href="Logic.html#24750" class="Bound"
      >B</a
      ><a name="24751"
      > </a
      ><a name="24752" href="Logic.html#24752" class="Bound"
      >C</a
      ><a name="24753"
      > </a
      ><a name="24754" class="Symbol"
      >:</a
      ><a name="24755"
      > </a
      ><a name="24756" class="PrimitiveType"
      >Set</a
      ><a name="24759" class="Symbol"
      >}</a
      ><a name="24760"
      > </a
      ><a name="24761" class="Symbol"
      >&#8594;</a
      ><a name="24762"
      > </a
      ><a name="24763" class="Symbol"
      >(</a
      ><a name="24764" href="Logic.html#24748" class="Bound"
      >A</a
      ><a name="24765"
      > </a
      ><a name="24766" class="Symbol"
      >&#8594;</a
      ><a name="24767"
      > </a
      ><a name="24768" href="Logic.html#24750" class="Bound"
      >B</a
      ><a name="24769"
      > </a
      ><a name="24770" class="Symbol"
      >&#8594;</a
      ><a name="24771"
      > </a
      ><a name="24772" href="Logic.html#24752" class="Bound"
      >C</a
      ><a name="24773" class="Symbol"
      >)</a
      ><a name="24774"
      > </a
      ><a name="24775" href="Logic.html#1478" class="Record Operator"
      >&#8771;</a
      ><a name="24776"
      > </a
      ><a name="24777" class="Symbol"
      >(</a
      ><a name="24778" href="Logic.html#24748" class="Bound"
      >A</a
      ><a name="24779"
      > </a
      ><a name="24780" href="Logic.html#7202" class="Datatype Operator"
      >&#215;</a
      ><a name="24781"
      > </a
      ><a name="24782" href="Logic.html#24750" class="Bound"
      >B</a
      ><a name="24783"
      > </a
      ><a name="24784" class="Symbol"
      >&#8594;</a
      ><a name="24785"
      > </a
      ><a name="24786" href="Logic.html#24752" class="Bound"
      >C</a
      ><a name="24787" class="Symbol"
      >)</a
      ><a name="24788"
      >
</a
      ><a name="24789" href="Logic.html#24734" class="Function"
      >currying</a
      ><a name="24797"
      > </a
      ><a name="24798" class="Symbol"
      >=</a
      ><a name="24799"
      >
  </a
      ><a name="24802" class="Keyword"
      >record</a
      ><a name="24808"
      >
    </a
      ><a name="24813" class="Symbol"
      >{</a
      ><a name="24814"
      > </a
      ><a name="24815" class="Field"
      >to</a
      ><a name="24817"
      >   </a
      ><a name="24820" class="Symbol"
      >=</a
      ><a name="24821"
      >  </a
      ><a name="24823" class="Symbol"
      >&#955;</a
      ><a name="24824"
      > </a
      ><a name="24825" href="Logic.html#24825" class="Bound"
      >f</a
      ><a name="24826"
      > </a
      ><a name="24827" class="Symbol"
      >&#8594;</a
      ><a name="24828"
      > </a
      ><a name="24829" class="Symbol"
      >&#955;</a
      ><a name="24830"
      > </a
      ><a name="24831" class="Symbol"
      >{</a
      ><a name="24832"
      > </a
      ><a name="24833" class="Symbol"
      >(</a
      ><a name="24834" href="Logic.html#24834" class="Bound"
      >x</a
      ><a name="24835"
      > </a
      ><a name="24836" href="Logic.html#7232" class="InductiveConstructor Operator"
      >,</a
      ><a name="24837"
      > </a
      ><a name="24838" href="Logic.html#24838" class="Bound"
      >y</a
      ><a name="24839" class="Symbol"
      >)</a
      ><a name="24840"
      > </a
      ><a name="24841" class="Symbol"
      >&#8594;</a
      ><a name="24842"
      > </a
      ><a name="24843" href="Logic.html#24825" class="Bound"
      >f</a
      ><a name="24844"
      > </a
      ><a name="24845" href="Logic.html#24834" class="Bound"
      >x</a
      ><a name="24846"
      > </a
      ><a name="24847" href="Logic.html#24838" class="Bound"
      >y</a
      ><a name="24848"
      > </a
      ><a name="24849" class="Symbol"
      >}</a
      ><a name="24850"
      >
    </a
      ><a name="24855" class="Symbol"
      >;</a
      ><a name="24856"
      > </a
      ><a name="24857" class="Field"
      >fro</a
      ><a name="24860"
      >  </a
      ><a name="24862" class="Symbol"
      >=</a
      ><a name="24863"
      >  </a
      ><a name="24865" class="Symbol"
      >&#955;</a
      ><a name="24866"
      > </a
      ><a name="24867" href="Logic.html#24867" class="Bound"
      >g</a
      ><a name="24868"
      > </a
      ><a name="24869" class="Symbol"
      >&#8594;</a
      ><a name="24870"
      > </a
      ><a name="24871" class="Symbol"
      >&#955;</a
      ><a name="24872"
      > </a
      ><a name="24873" href="Logic.html#24873" class="Bound"
      >x</a
      ><a name="24874"
      > </a
      ><a name="24875" class="Symbol"
      >&#8594;</a
      ><a name="24876"
      > </a
      ><a name="24877" class="Symbol"
      >&#955;</a
      ><a name="24878"
      > </a
      ><a name="24879" href="Logic.html#24879" class="Bound"
      >y</a
      ><a name="24880"
      > </a
      ><a name="24881" class="Symbol"
      >&#8594;</a
      ><a name="24882"
      > </a
      ><a name="24883" href="Logic.html#24867" class="Bound"
      >g</a
      ><a name="24884"
      > </a
      ><a name="24885" class="Symbol"
      >(</a
      ><a name="24886" href="Logic.html#24873" class="Bound"
      >x</a
      ><a name="24887"
      > </a
      ><a name="24888" href="Logic.html#7232" class="InductiveConstructor Operator"
      >,</a
      ><a name="24889"
      > </a
      ><a name="24890" href="Logic.html#24879" class="Bound"
      >y</a
      ><a name="24891" class="Symbol"
      >)</a
      ><a name="24892"
      >
    </a
      ><a name="24897" class="Symbol"
      >;</a
      ><a name="24898"
      > </a
      ><a name="24899" class="Field"
      >inv&#737;</a
      ><a name="24903"
      > </a
      ><a name="24904" class="Symbol"
      >=</a
      ><a name="24905"
      >  </a
      ><a name="24907" class="Symbol"
      >&#955;</a
      ><a name="24908"
      > </a
      ><a name="24909" href="Logic.html#24909" class="Bound"
      >f</a
      ><a name="24910"
      > </a
      ><a name="24911" class="Symbol"
      >&#8594;</a
      ><a name="24912"
      > </a
      ><a name="24913" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="24917"
      >
    </a
      ><a name="24922" class="Symbol"
      >;</a
      ><a name="24923"
      > </a
      ><a name="24924" class="Field"
      >inv&#691;</a
      ><a name="24928"
      > </a
      ><a name="24929" class="Symbol"
      >=</a
      ><a name="24930"
      >  </a
      ><a name="24932" class="Symbol"
      >&#955;</a
      ><a name="24933"
      > </a
      ><a name="24934" href="Logic.html#24934" class="Bound"
      >g</a
      ><a name="24935"
      > </a
      ><a name="24936" class="Symbol"
      >&#8594;</a
      ><a name="24937"
      > </a
      ><a name="24938" href="Logic.html#24650" class="Postulate"
      >extensionality</a
      ><a name="24952"
      > </a
      ><a name="24953" class="Symbol"
      >(&#955;</a
      ><a name="24955"
      > </a
      ><a name="24956" class="Symbol"
      >{</a
      ><a name="24957"
      > </a
      ><a name="24958" class="Symbol"
      >(</a
      ><a name="24959" href="Logic.html#24959" class="Bound"
      >x</a
      ><a name="24960"
      > </a
      ><a name="24961" href="Logic.html#7232" class="InductiveConstructor Operator"
      >,</a
      ><a name="24962"
      > </a
      ><a name="24963" href="Logic.html#24963" class="Bound"
      >y</a
      ><a name="24964" class="Symbol"
      >)</a
      ><a name="24965"
      > </a
      ><a name="24966" class="Symbol"
      >&#8594;</a
      ><a name="24967"
      > </a
      ><a name="24968" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="24972"
      > </a
      ><a name="24973" class="Symbol"
      >})</a
      ><a name="24975"
      >
    </a
      ><a name="24980" class="Symbol"
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
<a name="26271" href="Logic.html#26271" class="Function"
      >&#8594;-distributes-&#8846;</a
      ><a name="26286"
      > </a
      ><a name="26287" class="Symbol"
      >:</a
      ><a name="26288"
      > </a
      ><a name="26289" class="Symbol"
      >&#8704;</a
      ><a name="26290"
      > </a
      ><a name="26291" class="Symbol"
      >{</a
      ><a name="26292" href="Logic.html#26292" class="Bound"
      >A</a
      ><a name="26293"
      > </a
      ><a name="26294" href="Logic.html#26294" class="Bound"
      >B</a
      ><a name="26295"
      > </a
      ><a name="26296" href="Logic.html#26296" class="Bound"
      >C</a
      ><a name="26297"
      > </a
      ><a name="26298" class="Symbol"
      >:</a
      ><a name="26299"
      > </a
      ><a name="26300" class="PrimitiveType"
      >Set</a
      ><a name="26303" class="Symbol"
      >}</a
      ><a name="26304"
      > </a
      ><a name="26305" class="Symbol"
      >&#8594;</a
      ><a name="26306"
      > </a
      ><a name="26307" class="Symbol"
      >(</a
      ><a name="26308" href="Logic.html#26292" class="Bound"
      >A</a
      ><a name="26309"
      > </a
      ><a name="26310" href="Logic.html#14656" class="Datatype Operator"
      >&#8846;</a
      ><a name="26311"
      > </a
      ><a name="26312" href="Logic.html#26294" class="Bound"
      >B</a
      ><a name="26313"
      > </a
      ><a name="26314" class="Symbol"
      >&#8594;</a
      ><a name="26315"
      > </a
      ><a name="26316" href="Logic.html#26296" class="Bound"
      >C</a
      ><a name="26317" class="Symbol"
      >)</a
      ><a name="26318"
      > </a
      ><a name="26319" href="Logic.html#1478" class="Record Operator"
      >&#8771;</a
      ><a name="26320"
      > </a
      ><a name="26321" class="Symbol"
      >((</a
      ><a name="26323" href="Logic.html#26292" class="Bound"
      >A</a
      ><a name="26324"
      > </a
      ><a name="26325" class="Symbol"
      >&#8594;</a
      ><a name="26326"
      > </a
      ><a name="26327" href="Logic.html#26296" class="Bound"
      >C</a
      ><a name="26328" class="Symbol"
      >)</a
      ><a name="26329"
      > </a
      ><a name="26330" href="Logic.html#7202" class="Datatype Operator"
      >&#215;</a
      ><a name="26331"
      > </a
      ><a name="26332" class="Symbol"
      >(</a
      ><a name="26333" href="Logic.html#26294" class="Bound"
      >B</a
      ><a name="26334"
      > </a
      ><a name="26335" class="Symbol"
      >&#8594;</a
      ><a name="26336"
      > </a
      ><a name="26337" href="Logic.html#26296" class="Bound"
      >C</a
      ><a name="26338" class="Symbol"
      >))</a
      ><a name="26340"
      >
</a
      ><a name="26341" href="Logic.html#26271" class="Function"
      >&#8594;-distributes-&#8846;</a
      ><a name="26356"
      > </a
      ><a name="26357" class="Symbol"
      >=</a
      ><a name="26358"
      >
  </a
      ><a name="26361" class="Keyword"
      >record</a
      ><a name="26367"
      >
    </a
      ><a name="26372" class="Symbol"
      >{</a
      ><a name="26373"
      > </a
      ><a name="26374" class="Field"
      >to</a
      ><a name="26376"
      >   </a
      ><a name="26379" class="Symbol"
      >=</a
      ><a name="26380"
      > </a
      ><a name="26381" class="Symbol"
      >&#955;</a
      ><a name="26382"
      > </a
      ><a name="26383" href="Logic.html#26383" class="Bound"
      >f</a
      ><a name="26384"
      > </a
      ><a name="26385" class="Symbol"
      >&#8594;</a
      ><a name="26386"
      > </a
      ><a name="26387" class="Symbol"
      >(</a
      ><a name="26388"
      > </a
      ><a name="26389" class="Symbol"
      >(&#955;</a
      ><a name="26391"
      > </a
      ><a name="26392" href="Logic.html#26392" class="Bound"
      >x</a
      ><a name="26393"
      > </a
      ><a name="26394" class="Symbol"
      >&#8594;</a
      ><a name="26395"
      > </a
      ><a name="26396" href="Logic.html#26383" class="Bound"
      >f</a
      ><a name="26397"
      > </a
      ><a name="26398" class="Symbol"
      >(</a
      ><a name="26399" href="Logic.html#14686" class="InductiveConstructor"
      >inj&#8321;</a
      ><a name="26403"
      > </a
      ><a name="26404" href="Logic.html#26392" class="Bound"
      >x</a
      ><a name="26405" class="Symbol"
      >))</a
      ><a name="26407"
      > </a
      ><a name="26408" href="Logic.html#7232" class="InductiveConstructor Operator"
      >,</a
      ><a name="26409"
      > </a
      ><a name="26410" class="Symbol"
      >(&#955;</a
      ><a name="26412"
      > </a
      ><a name="26413" href="Logic.html#26413" class="Bound"
      >y</a
      ><a name="26414"
      > </a
      ><a name="26415" class="Symbol"
      >&#8594;</a
      ><a name="26416"
      > </a
      ><a name="26417" href="Logic.html#26383" class="Bound"
      >f</a
      ><a name="26418"
      > </a
      ><a name="26419" class="Symbol"
      >(</a
      ><a name="26420" href="Logic.html#14722" class="InductiveConstructor"
      >inj&#8322;</a
      ><a name="26424"
      > </a
      ><a name="26425" href="Logic.html#26413" class="Bound"
      >y</a
      ><a name="26426" class="Symbol"
      >))</a
      ><a name="26428"
      > </a
      ><a name="26429" class="Symbol"
      >)</a
      ><a name="26430"
      > 
    </a
      ><a name="26436" class="Symbol"
      >;</a
      ><a name="26437"
      > </a
      ><a name="26438" class="Field"
      >fro</a
      ><a name="26441"
      >  </a
      ><a name="26443" class="Symbol"
      >=</a
      ><a name="26444"
      > </a
      ><a name="26445" class="Symbol"
      >&#955;</a
      ><a name="26446"
      > </a
      ><a name="26447" class="Symbol"
      >{(</a
      ><a name="26449" href="Logic.html#26449" class="Bound"
      >g</a
      ><a name="26450"
      > </a
      ><a name="26451" href="Logic.html#7232" class="InductiveConstructor Operator"
      >,</a
      ><a name="26452"
      > </a
      ><a name="26453" href="Logic.html#26453" class="Bound"
      >h</a
      ><a name="26454" class="Symbol"
      >)</a
      ><a name="26455"
      > </a
      ><a name="26456" class="Symbol"
      >&#8594;</a
      ><a name="26457"
      > </a
      ><a name="26458" class="Symbol"
      >&#955;</a
      ><a name="26459"
      > </a
      ><a name="26460" class="Symbol"
      >{</a
      ><a name="26461"
      > </a
      ><a name="26462" class="Symbol"
      >(</a
      ><a name="26463" href="Logic.html#14686" class="InductiveConstructor"
      >inj&#8321;</a
      ><a name="26467"
      > </a
      ><a name="26468" href="Logic.html#26468" class="Bound"
      >x</a
      ><a name="26469" class="Symbol"
      >)</a
      ><a name="26470"
      > </a
      ><a name="26471" class="Symbol"
      >&#8594;</a
      ><a name="26472"
      > </a
      ><a name="26473" href="Logic.html#26449" class="Bound"
      >g</a
      ><a name="26474"
      > </a
      ><a name="26475" href="Logic.html#26468" class="Bound"
      >x</a
      ><a name="26476"
      > </a
      ><a name="26477" class="Symbol"
      >;</a
      ><a name="26478"
      > </a
      ><a name="26479" class="Symbol"
      >(</a
      ><a name="26480" href="Logic.html#14722" class="InductiveConstructor"
      >inj&#8322;</a
      ><a name="26484"
      > </a
      ><a name="26485" href="Logic.html#26485" class="Bound"
      >y</a
      ><a name="26486" class="Symbol"
      >)</a
      ><a name="26487"
      > </a
      ><a name="26488" class="Symbol"
      >&#8594;</a
      ><a name="26489"
      > </a
      ><a name="26490" href="Logic.html#26453" class="Bound"
      >h</a
      ><a name="26491"
      > </a
      ><a name="26492" href="Logic.html#26485" class="Bound"
      >y</a
      ><a name="26493"
      > </a
      ><a name="26494" class="Symbol"
      >}</a
      ><a name="26495"
      > </a
      ><a name="26496" class="Symbol"
      >}</a
      ><a name="26497"
      >
    </a
      ><a name="26502" class="Symbol"
      >;</a
      ><a name="26503"
      > </a
      ><a name="26504" class="Field"
      >inv&#737;</a
      ><a name="26508"
      > </a
      ><a name="26509" class="Symbol"
      >=</a
      ><a name="26510"
      > </a
      ><a name="26511" class="Symbol"
      >&#955;</a
      ><a name="26512"
      > </a
      ><a name="26513" href="Logic.html#26513" class="Bound"
      >f</a
      ><a name="26514"
      > </a
      ><a name="26515" class="Symbol"
      >&#8594;</a
      ><a name="26516"
      > </a
      ><a name="26517" href="Logic.html#24650" class="Postulate"
      >extensionality</a
      ><a name="26531"
      > </a
      ><a name="26532" class="Symbol"
      >(&#955;</a
      ><a name="26534"
      > </a
      ><a name="26535" class="Symbol"
      >{</a
      ><a name="26536"
      > </a
      ><a name="26537" class="Symbol"
      >(</a
      ><a name="26538" href="Logic.html#14686" class="InductiveConstructor"
      >inj&#8321;</a
      ><a name="26542"
      > </a
      ><a name="26543" href="Logic.html#26543" class="Bound"
      >x</a
      ><a name="26544" class="Symbol"
      >)</a
      ><a name="26545"
      > </a
      ><a name="26546" class="Symbol"
      >&#8594;</a
      ><a name="26547"
      > </a
      ><a name="26548" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="26552"
      > </a
      ><a name="26553" class="Symbol"
      >;</a
      ><a name="26554"
      > </a
      ><a name="26555" class="Symbol"
      >(</a
      ><a name="26556" href="Logic.html#14722" class="InductiveConstructor"
      >inj&#8322;</a
      ><a name="26560"
      > </a
      ><a name="26561" href="Logic.html#26561" class="Bound"
      >y</a
      ><a name="26562" class="Symbol"
      >)</a
      ><a name="26563"
      > </a
      ><a name="26564" class="Symbol"
      >&#8594;</a
      ><a name="26565"
      > </a
      ><a name="26566" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="26570"
      > </a
      ><a name="26571" class="Symbol"
      >})</a
      ><a name="26573"
      >
    </a
      ><a name="26578" class="Symbol"
      >;</a
      ><a name="26579"
      > </a
      ><a name="26580" class="Field"
      >inv&#691;</a
      ><a name="26584"
      > </a
      ><a name="26585" class="Symbol"
      >=</a
      ><a name="26586"
      > </a
      ><a name="26587" class="Symbol"
      >&#955;</a
      ><a name="26588"
      > </a
      ><a name="26589" class="Symbol"
      >{(</a
      ><a name="26591" href="Logic.html#26591" class="Bound"
      >g</a
      ><a name="26592"
      > </a
      ><a name="26593" href="Logic.html#7232" class="InductiveConstructor Operator"
      >,</a
      ><a name="26594"
      > </a
      ><a name="26595" href="Logic.html#26595" class="Bound"
      >h</a
      ><a name="26596" class="Symbol"
      >)</a
      ><a name="26597"
      > </a
      ><a name="26598" class="Symbol"
      >&#8594;</a
      ><a name="26599"
      > </a
      ><a name="26600" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="26604" class="Symbol"
      >}</a
      ><a name="26605"
      >
    </a
      ><a name="26610" class="Symbol"
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
<a name="27073" class="Keyword"
      >postulate</a
      ><a name="27082"
      >
  </a
      ><a name="27085" href="Logic.html#27085" class="Postulate"
      >&#951;-&#215;</a
      ><a name="27088"
      > </a
      ><a name="27089" class="Symbol"
      >:</a
      ><a name="27090"
      > </a
      ><a name="27091" class="Symbol"
      >&#8704;</a
      ><a name="27092"
      > </a
      ><a name="27093" class="Symbol"
      >{</a
      ><a name="27094" href="Logic.html#27094" class="Bound"
      >A</a
      ><a name="27095"
      > </a
      ><a name="27096" href="Logic.html#27096" class="Bound"
      >B</a
      ><a name="27097"
      > </a
      ><a name="27098" class="Symbol"
      >:</a
      ><a name="27099"
      > </a
      ><a name="27100" class="PrimitiveType"
      >Set</a
      ><a name="27103" class="Symbol"
      >}</a
      ><a name="27104"
      > </a
      ><a name="27105" class="Symbol"
      >&#8594;</a
      ><a name="27106"
      > </a
      ><a name="27107" class="Symbol"
      >&#8704;</a
      ><a name="27108"
      > </a
      ><a name="27109" class="Symbol"
      >(</a
      ><a name="27110" href="Logic.html#27110" class="Bound"
      >w</a
      ><a name="27111"
      > </a
      ><a name="27112" class="Symbol"
      >:</a
      ><a name="27113"
      > </a
      ><a name="27114" href="Logic.html#27094" class="Bound"
      >A</a
      ><a name="27115"
      > </a
      ><a name="27116" href="Logic.html#7202" class="Datatype Operator"
      >&#215;</a
      ><a name="27117"
      > </a
      ><a name="27118" href="Logic.html#27096" class="Bound"
      >B</a
      ><a name="27119" class="Symbol"
      >)</a
      ><a name="27120"
      > </a
      ><a name="27121" class="Symbol"
      >&#8594;</a
      ><a name="27122"
      > </a
      ><a name="27123" class="Symbol"
      >(</a
      ><a name="27124" href="Logic.html#7507" class="Function"
      >fst</a
      ><a name="27127"
      > </a
      ><a name="27128" href="Logic.html#27110" class="Bound"
      >w</a
      ><a name="27129"
      > </a
      ><a name="27130" href="Logic.html#7232" class="InductiveConstructor Operator"
      >,</a
      ><a name="27131"
      > </a
      ><a name="27132" href="Logic.html#7556" class="Function"
      >snd</a
      ><a name="27135"
      > </a
      ><a name="27136" href="Logic.html#27110" class="Bound"
      >w</a
      ><a name="27137" class="Symbol"
      >)</a
      ><a name="27138"
      > </a
      ><a name="27139" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="27140"
      > </a
      ><a name="27141" href="Logic.html#27110" class="Bound"
      >w</a
      ><a name="27142"
      >

</a
      ><a name="27144" href="Logic.html#27144" class="Function"
      >&#8594;-distributes-&#215;</a
      ><a name="27159"
      > </a
      ><a name="27160" class="Symbol"
      >:</a
      ><a name="27161"
      > </a
      ><a name="27162" class="Symbol"
      >&#8704;</a
      ><a name="27163"
      > </a
      ><a name="27164" class="Symbol"
      >{</a
      ><a name="27165" href="Logic.html#27165" class="Bound"
      >A</a
      ><a name="27166"
      > </a
      ><a name="27167" href="Logic.html#27167" class="Bound"
      >B</a
      ><a name="27168"
      > </a
      ><a name="27169" href="Logic.html#27169" class="Bound"
      >C</a
      ><a name="27170"
      > </a
      ><a name="27171" class="Symbol"
      >:</a
      ><a name="27172"
      > </a
      ><a name="27173" class="PrimitiveType"
      >Set</a
      ><a name="27176" class="Symbol"
      >}</a
      ><a name="27177"
      > </a
      ><a name="27178" class="Symbol"
      >&#8594;</a
      ><a name="27179"
      > </a
      ><a name="27180" class="Symbol"
      >(</a
      ><a name="27181" href="Logic.html#27165" class="Bound"
      >A</a
      ><a name="27182"
      > </a
      ><a name="27183" class="Symbol"
      >&#8594;</a
      ><a name="27184"
      > </a
      ><a name="27185" href="Logic.html#27167" class="Bound"
      >B</a
      ><a name="27186"
      > </a
      ><a name="27187" href="Logic.html#7202" class="Datatype Operator"
      >&#215;</a
      ><a name="27188"
      > </a
      ><a name="27189" href="Logic.html#27169" class="Bound"
      >C</a
      ><a name="27190" class="Symbol"
      >)</a
      ><a name="27191"
      > </a
      ><a name="27192" href="Logic.html#1478" class="Record Operator"
      >&#8771;</a
      ><a name="27193"
      > </a
      ><a name="27194" class="Symbol"
      >((</a
      ><a name="27196" href="Logic.html#27165" class="Bound"
      >A</a
      ><a name="27197"
      > </a
      ><a name="27198" class="Symbol"
      >&#8594;</a
      ><a name="27199"
      > </a
      ><a name="27200" href="Logic.html#27167" class="Bound"
      >B</a
      ><a name="27201" class="Symbol"
      >)</a
      ><a name="27202"
      > </a
      ><a name="27203" href="Logic.html#7202" class="Datatype Operator"
      >&#215;</a
      ><a name="27204"
      > </a
      ><a name="27205" class="Symbol"
      >(</a
      ><a name="27206" href="Logic.html#27165" class="Bound"
      >A</a
      ><a name="27207"
      > </a
      ><a name="27208" class="Symbol"
      >&#8594;</a
      ><a name="27209"
      > </a
      ><a name="27210" href="Logic.html#27169" class="Bound"
      >C</a
      ><a name="27211" class="Symbol"
      >))</a
      ><a name="27213"
      >
</a
      ><a name="27214" href="Logic.html#27144" class="Function"
      >&#8594;-distributes-&#215;</a
      ><a name="27229"
      > </a
      ><a name="27230" class="Symbol"
      >=</a
      ><a name="27231"
      >
  </a
      ><a name="27234" class="Keyword"
      >record</a
      ><a name="27240"
      >
    </a
      ><a name="27245" class="Symbol"
      >{</a
      ><a name="27246"
      > </a
      ><a name="27247" class="Field"
      >to</a
      ><a name="27249"
      >   </a
      ><a name="27252" class="Symbol"
      >=</a
      ><a name="27253"
      > </a
      ><a name="27254" class="Symbol"
      >&#955;</a
      ><a name="27255"
      > </a
      ><a name="27256" href="Logic.html#27256" class="Bound"
      >f</a
      ><a name="27257"
      > </a
      ><a name="27258" class="Symbol"
      >&#8594;</a
      ><a name="27259"
      > </a
      ><a name="27260" class="Symbol"
      >(</a
      ><a name="27261"
      > </a
      ><a name="27262" class="Symbol"
      >(&#955;</a
      ><a name="27264"
      > </a
      ><a name="27265" href="Logic.html#27265" class="Bound"
      >x</a
      ><a name="27266"
      > </a
      ><a name="27267" class="Symbol"
      >&#8594;</a
      ><a name="27268"
      > </a
      ><a name="27269" href="Logic.html#7507" class="Function"
      >fst</a
      ><a name="27272"
      > </a
      ><a name="27273" class="Symbol"
      >(</a
      ><a name="27274" href="Logic.html#27256" class="Bound"
      >f</a
      ><a name="27275"
      > </a
      ><a name="27276" href="Logic.html#27265" class="Bound"
      >x</a
      ><a name="27277" class="Symbol"
      >))</a
      ><a name="27279"
      > </a
      ><a name="27280" href="Logic.html#7232" class="InductiveConstructor Operator"
      >,</a
      ><a name="27281"
      > </a
      ><a name="27282" class="Symbol"
      >(&#955;</a
      ><a name="27284"
      > </a
      ><a name="27285" href="Logic.html#27285" class="Bound"
      >y</a
      ><a name="27286"
      > </a
      ><a name="27287" class="Symbol"
      >&#8594;</a
      ><a name="27288"
      > </a
      ><a name="27289" href="Logic.html#7556" class="Function"
      >snd</a
      ><a name="27292"
      > </a
      ><a name="27293" class="Symbol"
      >(</a
      ><a name="27294" href="Logic.html#27256" class="Bound"
      >f</a
      ><a name="27295"
      > </a
      ><a name="27296" href="Logic.html#27285" class="Bound"
      >y</a
      ><a name="27297" class="Symbol"
      >))</a
      ><a name="27299"
      > </a
      ><a name="27300" class="Symbol"
      >)</a
      ><a name="27301"
      > 
    </a
      ><a name="27307" class="Symbol"
      >;</a
      ><a name="27308"
      > </a
      ><a name="27309" class="Field"
      >fro</a
      ><a name="27312"
      >  </a
      ><a name="27314" class="Symbol"
      >=</a
      ><a name="27315"
      > </a
      ><a name="27316" class="Symbol"
      >&#955;</a
      ><a name="27317"
      > </a
      ><a name="27318" class="Symbol"
      >{(</a
      ><a name="27320" href="Logic.html#27320" class="Bound"
      >g</a
      ><a name="27321"
      > </a
      ><a name="27322" href="Logic.html#7232" class="InductiveConstructor Operator"
      >,</a
      ><a name="27323"
      > </a
      ><a name="27324" href="Logic.html#27324" class="Bound"
      >h</a
      ><a name="27325" class="Symbol"
      >)</a
      ><a name="27326"
      > </a
      ><a name="27327" class="Symbol"
      >&#8594;</a
      ><a name="27328"
      > </a
      ><a name="27329" class="Symbol"
      >(&#955;</a
      ><a name="27331"
      > </a
      ><a name="27332" href="Logic.html#27332" class="Bound"
      >x</a
      ><a name="27333"
      > </a
      ><a name="27334" class="Symbol"
      >&#8594;</a
      ><a name="27335"
      > </a
      ><a name="27336" class="Symbol"
      >(</a
      ><a name="27337" href="Logic.html#27320" class="Bound"
      >g</a
      ><a name="27338"
      > </a
      ><a name="27339" href="Logic.html#27332" class="Bound"
      >x</a
      ><a name="27340"
      > </a
      ><a name="27341" href="Logic.html#7232" class="InductiveConstructor Operator"
      >,</a
      ><a name="27342"
      > </a
      ><a name="27343" href="Logic.html#27324" class="Bound"
      >h</a
      ><a name="27344"
      > </a
      ><a name="27345" href="Logic.html#27332" class="Bound"
      >x</a
      ><a name="27346" class="Symbol"
      >))}</a
      ><a name="27349"
      >
    </a
      ><a name="27354" class="Symbol"
      >;</a
      ><a name="27355"
      > </a
      ><a name="27356" class="Field"
      >inv&#737;</a
      ><a name="27360"
      > </a
      ><a name="27361" class="Symbol"
      >=</a
      ><a name="27362"
      > </a
      ><a name="27363" class="Symbol"
      >&#955;</a
      ><a name="27364"
      > </a
      ><a name="27365" href="Logic.html#27365" class="Bound"
      >f</a
      ><a name="27366"
      > </a
      ><a name="27367" class="Symbol"
      >&#8594;</a
      ><a name="27368"
      > </a
      ><a name="27369" href="Logic.html#24650" class="Postulate"
      >extensionality</a
      ><a name="27383"
      > </a
      ><a name="27384" class="Symbol"
      >(&#955;</a
      ><a name="27386"
      > </a
      ><a name="27387" href="Logic.html#27387" class="Bound"
      >x</a
      ><a name="27388"
      > </a
      ><a name="27389" class="Symbol"
      >&#8594;</a
      ><a name="27390"
      > </a
      ><a name="27391" href="Logic.html#27085" class="Postulate"
      >&#951;-&#215;</a
      ><a name="27394"
      > </a
      ><a name="27395" class="Symbol"
      >(</a
      ><a name="27396" href="Logic.html#27365" class="Bound"
      >f</a
      ><a name="27397"
      > </a
      ><a name="27398" href="Logic.html#27387" class="Bound"
      >x</a
      ><a name="27399" class="Symbol"
      >))</a
      ><a name="27401"
      >
    </a
      ><a name="27406" class="Symbol"
      >;</a
      ><a name="27407"
      > </a
      ><a name="27408" class="Field"
      >inv&#691;</a
      ><a name="27412"
      > </a
      ><a name="27413" class="Symbol"
      >=</a
      ><a name="27414"
      > </a
      ><a name="27415" class="Symbol"
      >&#955;</a
      ><a name="27416"
      > </a
      ><a name="27417" class="Symbol"
      >{(</a
      ><a name="27419" href="Logic.html#27419" class="Bound"
      >g</a
      ><a name="27420"
      > </a
      ><a name="27421" href="Logic.html#7232" class="InductiveConstructor Operator"
      >,</a
      ><a name="27422"
      > </a
      ><a name="27423" href="Logic.html#27423" class="Bound"
      >h</a
      ><a name="27424" class="Symbol"
      >)</a
      ><a name="27425"
      > </a
      ><a name="27426" class="Symbol"
      >&#8594;</a
      ><a name="27427"
      > </a
      ><a name="27428" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="27432" class="Symbol"
      >}</a
      ><a name="27433"
      >
    </a
      ><a name="27438" class="Symbol"
      >}</a
      >
{% endraw %}</pre>


## Distribution

Products distributes over sum, up to isomorphism.  The code to validate
this fact is similar in structure to our previous results.
<pre class="Agda">{% raw %}
<a name="27614" href="Logic.html#27614" class="Function"
      >&#215;-distributes-&#8846;</a
      ><a name="27629"
      > </a
      ><a name="27630" class="Symbol"
      >:</a
      ><a name="27631"
      > </a
      ><a name="27632" class="Symbol"
      >&#8704;</a
      ><a name="27633"
      > </a
      ><a name="27634" class="Symbol"
      >{</a
      ><a name="27635" href="Logic.html#27635" class="Bound"
      >A</a
      ><a name="27636"
      > </a
      ><a name="27637" href="Logic.html#27637" class="Bound"
      >B</a
      ><a name="27638"
      > </a
      ><a name="27639" href="Logic.html#27639" class="Bound"
      >C</a
      ><a name="27640"
      > </a
      ><a name="27641" class="Symbol"
      >:</a
      ><a name="27642"
      > </a
      ><a name="27643" class="PrimitiveType"
      >Set</a
      ><a name="27646" class="Symbol"
      >}</a
      ><a name="27647"
      > </a
      ><a name="27648" class="Symbol"
      >&#8594;</a
      ><a name="27649"
      > </a
      ><a name="27650" class="Symbol"
      >((</a
      ><a name="27652" href="Logic.html#27635" class="Bound"
      >A</a
      ><a name="27653"
      > </a
      ><a name="27654" href="Logic.html#14656" class="Datatype Operator"
      >&#8846;</a
      ><a name="27655"
      > </a
      ><a name="27656" href="Logic.html#27637" class="Bound"
      >B</a
      ><a name="27657" class="Symbol"
      >)</a
      ><a name="27658"
      > </a
      ><a name="27659" href="Logic.html#7202" class="Datatype Operator"
      >&#215;</a
      ><a name="27660"
      > </a
      ><a name="27661" href="Logic.html#27639" class="Bound"
      >C</a
      ><a name="27662" class="Symbol"
      >)</a
      ><a name="27663"
      > </a
      ><a name="27664" href="Logic.html#1478" class="Record Operator"
      >&#8771;</a
      ><a name="27665"
      > </a
      ><a name="27666" class="Symbol"
      >((</a
      ><a name="27668" href="Logic.html#27635" class="Bound"
      >A</a
      ><a name="27669"
      > </a
      ><a name="27670" href="Logic.html#7202" class="Datatype Operator"
      >&#215;</a
      ><a name="27671"
      > </a
      ><a name="27672" href="Logic.html#27639" class="Bound"
      >C</a
      ><a name="27673" class="Symbol"
      >)</a
      ><a name="27674"
      > </a
      ><a name="27675" href="Logic.html#14656" class="Datatype Operator"
      >&#8846;</a
      ><a name="27676"
      > </a
      ><a name="27677" class="Symbol"
      >(</a
      ><a name="27678" href="Logic.html#27637" class="Bound"
      >B</a
      ><a name="27679"
      > </a
      ><a name="27680" href="Logic.html#7202" class="Datatype Operator"
      >&#215;</a
      ><a name="27681"
      > </a
      ><a name="27682" href="Logic.html#27639" class="Bound"
      >C</a
      ><a name="27683" class="Symbol"
      >))</a
      ><a name="27685"
      >
</a
      ><a name="27686" href="Logic.html#27614" class="Function"
      >&#215;-distributes-&#8846;</a
      ><a name="27701"
      > </a
      ><a name="27702" class="Symbol"
      >=</a
      ><a name="27703"
      >
  </a
      ><a name="27706" class="Keyword"
      >record</a
      ><a name="27712"
      >
    </a
      ><a name="27717" class="Symbol"
      >{</a
      ><a name="27718"
      > </a
      ><a name="27719" class="Field"
      >to</a
      ><a name="27721"
      >   </a
      ><a name="27724" class="Symbol"
      >=</a
      ><a name="27725"
      > </a
      ><a name="27726" class="Symbol"
      >&#955;</a
      ><a name="27727"
      > </a
      ><a name="27728" class="Symbol"
      >{</a
      ><a name="27729"
      > </a
      ><a name="27730" class="Symbol"
      >((</a
      ><a name="27732" href="Logic.html#14686" class="InductiveConstructor"
      >inj&#8321;</a
      ><a name="27736"
      > </a
      ><a name="27737" href="Logic.html#27737" class="Bound"
      >x</a
      ><a name="27738" class="Symbol"
      >)</a
      ><a name="27739"
      > </a
      ><a name="27740" href="Logic.html#7232" class="InductiveConstructor Operator"
      >,</a
      ><a name="27741"
      > </a
      ><a name="27742" href="Logic.html#27742" class="Bound"
      >z</a
      ><a name="27743" class="Symbol"
      >)</a
      ><a name="27744"
      > </a
      ><a name="27745" class="Symbol"
      >&#8594;</a
      ><a name="27746"
      > </a
      ><a name="27747" class="Symbol"
      >(</a
      ><a name="27748" href="Logic.html#14686" class="InductiveConstructor"
      >inj&#8321;</a
      ><a name="27752"
      > </a
      ><a name="27753" class="Symbol"
      >(</a
      ><a name="27754" href="Logic.html#27737" class="Bound"
      >x</a
      ><a name="27755"
      > </a
      ><a name="27756" href="Logic.html#7232" class="InductiveConstructor Operator"
      >,</a
      ><a name="27757"
      > </a
      ><a name="27758" href="Logic.html#27742" class="Bound"
      >z</a
      ><a name="27759" class="Symbol"
      >))</a
      ><a name="27761"
      > 
               </a
      ><a name="27778" class="Symbol"
      >;</a
      ><a name="27779"
      > </a
      ><a name="27780" class="Symbol"
      >((</a
      ><a name="27782" href="Logic.html#14722" class="InductiveConstructor"
      >inj&#8322;</a
      ><a name="27786"
      > </a
      ><a name="27787" href="Logic.html#27787" class="Bound"
      >y</a
      ><a name="27788" class="Symbol"
      >)</a
      ><a name="27789"
      > </a
      ><a name="27790" href="Logic.html#7232" class="InductiveConstructor Operator"
      >,</a
      ><a name="27791"
      > </a
      ><a name="27792" href="Logic.html#27792" class="Bound"
      >z</a
      ><a name="27793" class="Symbol"
      >)</a
      ><a name="27794"
      > </a
      ><a name="27795" class="Symbol"
      >&#8594;</a
      ><a name="27796"
      > </a
      ><a name="27797" class="Symbol"
      >(</a
      ><a name="27798" href="Logic.html#14722" class="InductiveConstructor"
      >inj&#8322;</a
      ><a name="27802"
      > </a
      ><a name="27803" class="Symbol"
      >(</a
      ><a name="27804" href="Logic.html#27787" class="Bound"
      >y</a
      ><a name="27805"
      > </a
      ><a name="27806" href="Logic.html#7232" class="InductiveConstructor Operator"
      >,</a
      ><a name="27807"
      > </a
      ><a name="27808" href="Logic.html#27792" class="Bound"
      >z</a
      ><a name="27809" class="Symbol"
      >))</a
      ><a name="27811"
      >
               </a
      ><a name="27827" class="Symbol"
      >}</a
      ><a name="27828"
      >
    </a
      ><a name="27833" class="Symbol"
      >;</a
      ><a name="27834"
      > </a
      ><a name="27835" class="Field"
      >fro</a
      ><a name="27838"
      >  </a
      ><a name="27840" class="Symbol"
      >=</a
      ><a name="27841"
      > </a
      ><a name="27842" class="Symbol"
      >&#955;</a
      ><a name="27843"
      > </a
      ><a name="27844" class="Symbol"
      >{</a
      ><a name="27845"
      > </a
      ><a name="27846" class="Symbol"
      >(</a
      ><a name="27847" href="Logic.html#14686" class="InductiveConstructor"
      >inj&#8321;</a
      ><a name="27851"
      > </a
      ><a name="27852" class="Symbol"
      >(</a
      ><a name="27853" href="Logic.html#27853" class="Bound"
      >x</a
      ><a name="27854"
      > </a
      ><a name="27855" href="Logic.html#7232" class="InductiveConstructor Operator"
      >,</a
      ><a name="27856"
      > </a
      ><a name="27857" href="Logic.html#27857" class="Bound"
      >z</a
      ><a name="27858" class="Symbol"
      >))</a
      ><a name="27860"
      > </a
      ><a name="27861" class="Symbol"
      >&#8594;</a
      ><a name="27862"
      > </a
      ><a name="27863" class="Symbol"
      >((</a
      ><a name="27865" href="Logic.html#14686" class="InductiveConstructor"
      >inj&#8321;</a
      ><a name="27869"
      > </a
      ><a name="27870" href="Logic.html#27853" class="Bound"
      >x</a
      ><a name="27871" class="Symbol"
      >)</a
      ><a name="27872"
      > </a
      ><a name="27873" href="Logic.html#7232" class="InductiveConstructor Operator"
      >,</a
      ><a name="27874"
      > </a
      ><a name="27875" href="Logic.html#27857" class="Bound"
      >z</a
      ><a name="27876" class="Symbol"
      >)</a
      ><a name="27877"
      >
               </a
      ><a name="27893" class="Symbol"
      >;</a
      ><a name="27894"
      > </a
      ><a name="27895" class="Symbol"
      >(</a
      ><a name="27896" href="Logic.html#14722" class="InductiveConstructor"
      >inj&#8322;</a
      ><a name="27900"
      > </a
      ><a name="27901" class="Symbol"
      >(</a
      ><a name="27902" href="Logic.html#27902" class="Bound"
      >y</a
      ><a name="27903"
      > </a
      ><a name="27904" href="Logic.html#7232" class="InductiveConstructor Operator"
      >,</a
      ><a name="27905"
      > </a
      ><a name="27906" href="Logic.html#27906" class="Bound"
      >z</a
      ><a name="27907" class="Symbol"
      >))</a
      ><a name="27909"
      > </a
      ><a name="27910" class="Symbol"
      >&#8594;</a
      ><a name="27911"
      > </a
      ><a name="27912" class="Symbol"
      >((</a
      ><a name="27914" href="Logic.html#14722" class="InductiveConstructor"
      >inj&#8322;</a
      ><a name="27918"
      > </a
      ><a name="27919" href="Logic.html#27902" class="Bound"
      >y</a
      ><a name="27920" class="Symbol"
      >)</a
      ><a name="27921"
      > </a
      ><a name="27922" href="Logic.html#7232" class="InductiveConstructor Operator"
      >,</a
      ><a name="27923"
      > </a
      ><a name="27924" href="Logic.html#27906" class="Bound"
      >z</a
      ><a name="27925" class="Symbol"
      >)</a
      ><a name="27926"
      >
               </a
      ><a name="27942" class="Symbol"
      >}</a
      ><a name="27943"
      >
    </a
      ><a name="27948" class="Symbol"
      >;</a
      ><a name="27949"
      > </a
      ><a name="27950" class="Field"
      >inv&#737;</a
      ><a name="27954"
      > </a
      ><a name="27955" class="Symbol"
      >=</a
      ><a name="27956"
      > </a
      ><a name="27957" class="Symbol"
      >&#955;</a
      ><a name="27958"
      > </a
      ><a name="27959" class="Symbol"
      >{</a
      ><a name="27960"
      > </a
      ><a name="27961" class="Symbol"
      >((</a
      ><a name="27963" href="Logic.html#14686" class="InductiveConstructor"
      >inj&#8321;</a
      ><a name="27967"
      > </a
      ><a name="27968" href="Logic.html#27968" class="Bound"
      >x</a
      ><a name="27969" class="Symbol"
      >)</a
      ><a name="27970"
      > </a
      ><a name="27971" href="Logic.html#7232" class="InductiveConstructor Operator"
      >,</a
      ><a name="27972"
      > </a
      ><a name="27973" href="Logic.html#27973" class="Bound"
      >z</a
      ><a name="27974" class="Symbol"
      >)</a
      ><a name="27975"
      > </a
      ><a name="27976" class="Symbol"
      >&#8594;</a
      ><a name="27977"
      > </a
      ><a name="27978" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="27982"
      >
               </a
      ><a name="27998" class="Symbol"
      >;</a
      ><a name="27999"
      > </a
      ><a name="28000" class="Symbol"
      >((</a
      ><a name="28002" href="Logic.html#14722" class="InductiveConstructor"
      >inj&#8322;</a
      ><a name="28006"
      > </a
      ><a name="28007" href="Logic.html#28007" class="Bound"
      >y</a
      ><a name="28008" class="Symbol"
      >)</a
      ><a name="28009"
      > </a
      ><a name="28010" href="Logic.html#7232" class="InductiveConstructor Operator"
      >,</a
      ><a name="28011"
      > </a
      ><a name="28012" href="Logic.html#28012" class="Bound"
      >z</a
      ><a name="28013" class="Symbol"
      >)</a
      ><a name="28014"
      > </a
      ><a name="28015" class="Symbol"
      >&#8594;</a
      ><a name="28016"
      > </a
      ><a name="28017" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="28021"
      >
               </a
      ><a name="28037" class="Symbol"
      >}</a
      ><a name="28038"
      >
    </a
      ><a name="28043" class="Symbol"
      >;</a
      ><a name="28044"
      > </a
      ><a name="28045" class="Field"
      >inv&#691;</a
      ><a name="28049"
      > </a
      ><a name="28050" class="Symbol"
      >=</a
      ><a name="28051"
      > </a
      ><a name="28052" class="Symbol"
      >&#955;</a
      ><a name="28053"
      > </a
      ><a name="28054" class="Symbol"
      >{</a
      ><a name="28055"
      > </a
      ><a name="28056" class="Symbol"
      >(</a
      ><a name="28057" href="Logic.html#14686" class="InductiveConstructor"
      >inj&#8321;</a
      ><a name="28061"
      > </a
      ><a name="28062" class="Symbol"
      >(</a
      ><a name="28063" href="Logic.html#28063" class="Bound"
      >x</a
      ><a name="28064"
      > </a
      ><a name="28065" href="Logic.html#7232" class="InductiveConstructor Operator"
      >,</a
      ><a name="28066"
      > </a
      ><a name="28067" href="Logic.html#28067" class="Bound"
      >z</a
      ><a name="28068" class="Symbol"
      >))</a
      ><a name="28070"
      > </a
      ><a name="28071" class="Symbol"
      >&#8594;</a
      ><a name="28072"
      > </a
      ><a name="28073" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="28077"
      >
               </a
      ><a name="28093" class="Symbol"
      >;</a
      ><a name="28094"
      > </a
      ><a name="28095" class="Symbol"
      >(</a
      ><a name="28096" href="Logic.html#14722" class="InductiveConstructor"
      >inj&#8322;</a
      ><a name="28100"
      > </a
      ><a name="28101" class="Symbol"
      >(</a
      ><a name="28102" href="Logic.html#28102" class="Bound"
      >y</a
      ><a name="28103"
      > </a
      ><a name="28104" href="Logic.html#7232" class="InductiveConstructor Operator"
      >,</a
      ><a name="28105"
      > </a
      ><a name="28106" href="Logic.html#28106" class="Bound"
      >z</a
      ><a name="28107" class="Symbol"
      >))</a
      ><a name="28109"
      > </a
      ><a name="28110" class="Symbol"
      >&#8594;</a
      ><a name="28111"
      > </a
      ><a name="28112" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="28116"
      >
               </a
      ><a name="28132" class="Symbol"
      >}</a
      ><a name="28133"
      >               
    </a
      ><a name="28153" class="Symbol"
      >}</a
      >
{% endraw %}</pre>

Sums do not distribute over products up to isomorphism, but it is an embedding.
<pre class="Agda">{% raw %}
<a name="28260" href="Logic.html#28260" class="Function"
      >&#8846;-distributes-&#215;</a
      ><a name="28275"
      > </a
      ><a name="28276" class="Symbol"
      >:</a
      ><a name="28277"
      > </a
      ><a name="28278" class="Symbol"
      >&#8704;</a
      ><a name="28279"
      > </a
      ><a name="28280" class="Symbol"
      >{</a
      ><a name="28281" href="Logic.html#28281" class="Bound"
      >A</a
      ><a name="28282"
      > </a
      ><a name="28283" href="Logic.html#28283" class="Bound"
      >B</a
      ><a name="28284"
      > </a
      ><a name="28285" href="Logic.html#28285" class="Bound"
      >C</a
      ><a name="28286"
      > </a
      ><a name="28287" class="Symbol"
      >:</a
      ><a name="28288"
      > </a
      ><a name="28289" class="PrimitiveType"
      >Set</a
      ><a name="28292" class="Symbol"
      >}</a
      ><a name="28293"
      > </a
      ><a name="28294" class="Symbol"
      >&#8594;</a
      ><a name="28295"
      > </a
      ><a name="28296" class="Symbol"
      >((</a
      ><a name="28298" href="Logic.html#28281" class="Bound"
      >A</a
      ><a name="28299"
      > </a
      ><a name="28300" href="Logic.html#7202" class="Datatype Operator"
      >&#215;</a
      ><a name="28301"
      > </a
      ><a name="28302" href="Logic.html#28283" class="Bound"
      >B</a
      ><a name="28303" class="Symbol"
      >)</a
      ><a name="28304"
      > </a
      ><a name="28305" href="Logic.html#14656" class="Datatype Operator"
      >&#8846;</a
      ><a name="28306"
      > </a
      ><a name="28307" href="Logic.html#28285" class="Bound"
      >C</a
      ><a name="28308" class="Symbol"
      >)</a
      ><a name="28309"
      > </a
      ><a name="28310" href="Logic.html#5152" class="Record Operator"
      >&#8818;</a
      ><a name="28311"
      > </a
      ><a name="28312" class="Symbol"
      >((</a
      ><a name="28314" href="Logic.html#28281" class="Bound"
      >A</a
      ><a name="28315"
      > </a
      ><a name="28316" href="Logic.html#14656" class="Datatype Operator"
      >&#8846;</a
      ><a name="28317"
      > </a
      ><a name="28318" href="Logic.html#28285" class="Bound"
      >C</a
      ><a name="28319" class="Symbol"
      >)</a
      ><a name="28320"
      > </a
      ><a name="28321" href="Logic.html#7202" class="Datatype Operator"
      >&#215;</a
      ><a name="28322"
      > </a
      ><a name="28323" class="Symbol"
      >(</a
      ><a name="28324" href="Logic.html#28283" class="Bound"
      >B</a
      ><a name="28325"
      > </a
      ><a name="28326" href="Logic.html#14656" class="Datatype Operator"
      >&#8846;</a
      ><a name="28327"
      > </a
      ><a name="28328" href="Logic.html#28285" class="Bound"
      >C</a
      ><a name="28329" class="Symbol"
      >))</a
      ><a name="28331"
      >
</a
      ><a name="28332" href="Logic.html#28260" class="Function"
      >&#8846;-distributes-&#215;</a
      ><a name="28347"
      > </a
      ><a name="28348" class="Symbol"
      >=</a
      ><a name="28349"
      >
  </a
      ><a name="28352" class="Keyword"
      >record</a
      ><a name="28358"
      >
    </a
      ><a name="28363" class="Symbol"
      >{</a
      ><a name="28364"
      > </a
      ><a name="28365" class="Field"
      >to</a
      ><a name="28367"
      >   </a
      ><a name="28370" class="Symbol"
      >=</a
      ><a name="28371"
      > </a
      ><a name="28372" class="Symbol"
      >&#955;</a
      ><a name="28373"
      > </a
      ><a name="28374" class="Symbol"
      >{</a
      ><a name="28375"
      > </a
      ><a name="28376" class="Symbol"
      >(</a
      ><a name="28377" href="Logic.html#14686" class="InductiveConstructor"
      >inj&#8321;</a
      ><a name="28381"
      > </a
      ><a name="28382" class="Symbol"
      >(</a
      ><a name="28383" href="Logic.html#28383" class="Bound"
      >x</a
      ><a name="28384"
      > </a
      ><a name="28385" href="Logic.html#7232" class="InductiveConstructor Operator"
      >,</a
      ><a name="28386"
      > </a
      ><a name="28387" href="Logic.html#28387" class="Bound"
      >y</a
      ><a name="28388" class="Symbol"
      >))</a
      ><a name="28390"
      > </a
      ><a name="28391" class="Symbol"
      >&#8594;</a
      ><a name="28392"
      > </a
      ><a name="28393" class="Symbol"
      >(</a
      ><a name="28394" href="Logic.html#14686" class="InductiveConstructor"
      >inj&#8321;</a
      ><a name="28398"
      > </a
      ><a name="28399" href="Logic.html#28383" class="Bound"
      >x</a
      ><a name="28400"
      > </a
      ><a name="28401" href="Logic.html#7232" class="InductiveConstructor Operator"
      >,</a
      ><a name="28402"
      > </a
      ><a name="28403" href="Logic.html#14686" class="InductiveConstructor"
      >inj&#8321;</a
      ><a name="28407"
      > </a
      ><a name="28408" href="Logic.html#28387" class="Bound"
      >y</a
      ><a name="28409" class="Symbol"
      >)</a
      ><a name="28410"
      >
               </a
      ><a name="28426" class="Symbol"
      >;</a
      ><a name="28427"
      > </a
      ><a name="28428" class="Symbol"
      >(</a
      ><a name="28429" href="Logic.html#14722" class="InductiveConstructor"
      >inj&#8322;</a
      ><a name="28433"
      > </a
      ><a name="28434" href="Logic.html#28434" class="Bound"
      >z</a
      ><a name="28435" class="Symbol"
      >)</a
      ><a name="28436"
      >       </a
      ><a name="28443" class="Symbol"
      >&#8594;</a
      ><a name="28444"
      > </a
      ><a name="28445" class="Symbol"
      >(</a
      ><a name="28446" href="Logic.html#14722" class="InductiveConstructor"
      >inj&#8322;</a
      ><a name="28450"
      > </a
      ><a name="28451" href="Logic.html#28434" class="Bound"
      >z</a
      ><a name="28452"
      > </a
      ><a name="28453" href="Logic.html#7232" class="InductiveConstructor Operator"
      >,</a
      ><a name="28454"
      > </a
      ><a name="28455" href="Logic.html#14722" class="InductiveConstructor"
      >inj&#8322;</a
      ><a name="28459"
      > </a
      ><a name="28460" href="Logic.html#28434" class="Bound"
      >z</a
      ><a name="28461" class="Symbol"
      >)</a
      ><a name="28462"
      >
               </a
      ><a name="28478" class="Symbol"
      >}</a
      ><a name="28479"
      >
    </a
      ><a name="28484" class="Symbol"
      >;</a
      ><a name="28485"
      > </a
      ><a name="28486" class="Field"
      >fro</a
      ><a name="28489"
      >  </a
      ><a name="28491" class="Symbol"
      >=</a
      ><a name="28492"
      > </a
      ><a name="28493" class="Symbol"
      >&#955;</a
      ><a name="28494"
      > </a
      ><a name="28495" class="Symbol"
      >{</a
      ><a name="28496"
      > </a
      ><a name="28497" class="Symbol"
      >(</a
      ><a name="28498" href="Logic.html#14686" class="InductiveConstructor"
      >inj&#8321;</a
      ><a name="28502"
      > </a
      ><a name="28503" href="Logic.html#28503" class="Bound"
      >x</a
      ><a name="28504"
      > </a
      ><a name="28505" href="Logic.html#7232" class="InductiveConstructor Operator"
      >,</a
      ><a name="28506"
      > </a
      ><a name="28507" href="Logic.html#14686" class="InductiveConstructor"
      >inj&#8321;</a
      ><a name="28511"
      > </a
      ><a name="28512" href="Logic.html#28512" class="Bound"
      >y</a
      ><a name="28513" class="Symbol"
      >)</a
      ><a name="28514"
      > </a
      ><a name="28515" class="Symbol"
      >&#8594;</a
      ><a name="28516"
      > </a
      ><a name="28517" class="Symbol"
      >(</a
      ><a name="28518" href="Logic.html#14686" class="InductiveConstructor"
      >inj&#8321;</a
      ><a name="28522"
      > </a
      ><a name="28523" class="Symbol"
      >(</a
      ><a name="28524" href="Logic.html#28503" class="Bound"
      >x</a
      ><a name="28525"
      > </a
      ><a name="28526" href="Logic.html#7232" class="InductiveConstructor Operator"
      >,</a
      ><a name="28527"
      > </a
      ><a name="28528" href="Logic.html#28512" class="Bound"
      >y</a
      ><a name="28529" class="Symbol"
      >))</a
      ><a name="28531"
      >
               </a
      ><a name="28547" class="Symbol"
      >;</a
      ><a name="28548"
      > </a
      ><a name="28549" class="Symbol"
      >(</a
      ><a name="28550" href="Logic.html#14686" class="InductiveConstructor"
      >inj&#8321;</a
      ><a name="28554"
      > </a
      ><a name="28555" href="Logic.html#28555" class="Bound"
      >x</a
      ><a name="28556"
      > </a
      ><a name="28557" href="Logic.html#7232" class="InductiveConstructor Operator"
      >,</a
      ><a name="28558"
      > </a
      ><a name="28559" href="Logic.html#14722" class="InductiveConstructor"
      >inj&#8322;</a
      ><a name="28563"
      > </a
      ><a name="28564" href="Logic.html#28564" class="Bound"
      >z</a
      ><a name="28565" class="Symbol"
      >)</a
      ><a name="28566"
      > </a
      ><a name="28567" class="Symbol"
      >&#8594;</a
      ><a name="28568"
      > </a
      ><a name="28569" class="Symbol"
      >(</a
      ><a name="28570" href="Logic.html#14722" class="InductiveConstructor"
      >inj&#8322;</a
      ><a name="28574"
      > </a
      ><a name="28575" href="Logic.html#28564" class="Bound"
      >z</a
      ><a name="28576" class="Symbol"
      >)</a
      ><a name="28577"
      >
               </a
      ><a name="28593" class="Symbol"
      >;</a
      ><a name="28594"
      > </a
      ><a name="28595" class="Symbol"
      >(</a
      ><a name="28596" href="Logic.html#14722" class="InductiveConstructor"
      >inj&#8322;</a
      ><a name="28600"
      > </a
      ><a name="28601" href="Logic.html#28601" class="Bound"
      >z</a
      ><a name="28602"
      > </a
      ><a name="28603" href="Logic.html#7232" class="InductiveConstructor Operator"
      >,</a
      ><a name="28604"
      > </a
      ><a name="28605" class="Symbol"
      >_</a
      ><a name="28606"
      > </a
      ><a name="28607" class="Symbol"
      >)</a
      ><a name="28608"
      >     </a
      ><a name="28613" class="Symbol"
      >&#8594;</a
      ><a name="28614"
      > </a
      ><a name="28615" class="Symbol"
      >(</a
      ><a name="28616" href="Logic.html#14722" class="InductiveConstructor"
      >inj&#8322;</a
      ><a name="28620"
      > </a
      ><a name="28621" href="Logic.html#28601" class="Bound"
      >z</a
      ><a name="28622" class="Symbol"
      >)</a
      ><a name="28623"
      >
               </a
      ><a name="28639" class="Symbol"
      >}</a
      ><a name="28640"
      >
    </a
      ><a name="28645" class="Symbol"
      >;</a
      ><a name="28646"
      > </a
      ><a name="28647" class="Field"
      >inv&#737;</a
      ><a name="28651"
      > </a
      ><a name="28652" class="Symbol"
      >=</a
      ><a name="28653"
      > </a
      ><a name="28654" class="Symbol"
      >&#955;</a
      ><a name="28655"
      > </a
      ><a name="28656" class="Symbol"
      >{</a
      ><a name="28657"
      > </a
      ><a name="28658" class="Symbol"
      >(</a
      ><a name="28659" href="Logic.html#14686" class="InductiveConstructor"
      >inj&#8321;</a
      ><a name="28663"
      > </a
      ><a name="28664" class="Symbol"
      >(</a
      ><a name="28665" href="Logic.html#28665" class="Bound"
      >x</a
      ><a name="28666"
      > </a
      ><a name="28667" href="Logic.html#7232" class="InductiveConstructor Operator"
      >,</a
      ><a name="28668"
      > </a
      ><a name="28669" href="Logic.html#28669" class="Bound"
      >y</a
      ><a name="28670" class="Symbol"
      >))</a
      ><a name="28672"
      > </a
      ><a name="28673" class="Symbol"
      >&#8594;</a
      ><a name="28674"
      > </a
      ><a name="28675" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="28679"
      >
               </a
      ><a name="28695" class="Symbol"
      >;</a
      ><a name="28696"
      > </a
      ><a name="28697" class="Symbol"
      >(</a
      ><a name="28698" href="Logic.html#14722" class="InductiveConstructor"
      >inj&#8322;</a
      ><a name="28702"
      > </a
      ><a name="28703" href="Logic.html#28703" class="Bound"
      >z</a
      ><a name="28704" class="Symbol"
      >)</a
      ><a name="28705"
      >       </a
      ><a name="28712" class="Symbol"
      >&#8594;</a
      ><a name="28713"
      > </a
      ><a name="28714" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="28718"
      >
               </a
      ><a name="28734" class="Symbol"
      >}</a
      ><a name="28735"
      >
    </a
      ><a name="28740" class="Symbol"
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
<a name="29737" href="Logic.html#29737" class="Function Operator"
      >&#172;_</a
      ><a name="29739"
      > </a
      ><a name="29740" class="Symbol"
      >:</a
      ><a name="29741"
      > </a
      ><a name="29742" class="PrimitiveType"
      >Set</a
      ><a name="29745"
      > </a
      ><a name="29746" class="Symbol"
      >&#8594;</a
      ><a name="29747"
      > </a
      ><a name="29748" class="PrimitiveType"
      >Set</a
      ><a name="29751"
      >
</a
      ><a name="29752" href="Logic.html#29737" class="Function Operator"
      >&#172;</a
      ><a name="29753"
      > </a
      ><a name="29754" href="Logic.html#29754" class="Bound"
      >A</a
      ><a name="29755"
      > </a
      ><a name="29756" class="Symbol"
      >=</a
      ><a name="29757"
      > </a
      ><a name="29758" href="Logic.html#29754" class="Bound"
      >A</a
      ><a name="29759"
      > </a
      ><a name="29760" class="Symbol"
      >&#8594;</a
      ><a name="29761"
      > </a
      ><a name="29762" href="Logic.html#19450" class="Datatype"
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
<a name="30337" href="Logic.html#30337" class="Function"
      >&#172;-elim</a
      ><a name="30343"
      > </a
      ><a name="30344" class="Symbol"
      >:</a
      ><a name="30345"
      > </a
      ><a name="30346" class="Symbol"
      >&#8704;</a
      ><a name="30347"
      > </a
      ><a name="30348" class="Symbol"
      >{</a
      ><a name="30349" href="Logic.html#30349" class="Bound"
      >A</a
      ><a name="30350"
      > </a
      ><a name="30351" class="Symbol"
      >:</a
      ><a name="30352"
      > </a
      ><a name="30353" class="PrimitiveType"
      >Set</a
      ><a name="30356" class="Symbol"
      >}</a
      ><a name="30357"
      > </a
      ><a name="30358" class="Symbol"
      >&#8594;</a
      ><a name="30359"
      > </a
      ><a name="30360" href="Logic.html#29737" class="Function Operator"
      >&#172;</a
      ><a name="30361"
      > </a
      ><a name="30362" href="Logic.html#30349" class="Bound"
      >A</a
      ><a name="30363"
      > </a
      ><a name="30364" class="Symbol"
      >&#8594;</a
      ><a name="30365"
      > </a
      ><a name="30366" href="Logic.html#30349" class="Bound"
      >A</a
      ><a name="30367"
      > </a
      ><a name="30368" class="Symbol"
      >&#8594;</a
      ><a name="30369"
      > </a
      ><a name="30370" href="Logic.html#19450" class="Datatype"
      >&#8869;</a
      ><a name="30371"
      >
</a
      ><a name="30372" href="Logic.html#30337" class="Function"
      >&#172;-elim</a
      ><a name="30378"
      > </a
      ><a name="30379" href="Logic.html#30379" class="Bound"
      >&#172;a</a
      ><a name="30381"
      > </a
      ><a name="30382" href="Logic.html#30382" class="Bound"
      >a</a
      ><a name="30383"
      > </a
      ><a name="30384" class="Symbol"
      >=</a
      ><a name="30385"
      > </a
      ><a name="30386" href="Logic.html#30379" class="Bound"
      >&#172;a</a
      ><a name="30388"
      > </a
      ><a name="30389" href="Logic.html#30382" class="Bound"
      >a</a
      >
{% endraw %}</pre>
Here we write `¬a` for evidence of `¬ A` and `a` for evidence of `A`.  This
means that `¬a` must be a function of type `A → ⊥`, and hence the application
`¬a a` must be of type `⊥`.  Note that this rule is just a special case of `→-elim`.

We set the precedence of negation so that it binds more tightly
than disjunction and conjunction, but more tightly than anything else.
<pre class="Agda">{% raw %}
<a name="30790" class="Keyword"
      >infix</a
      ><a name="30795"
      > </a
      ><a name="30796" class="Number"
      >3</a
      ><a name="30797"
      > </a
      ><a name="30798" href="Logic.html#29737" class="Function Operator"
      >&#172;_</a
      >
{% endraw %}</pre>
Thus, `¬ A × ¬ B` parses as `(¬ A) × (¬ B)`.

In *classical* logic, we have that `A` is equivalent to `¬ ¬ A`.
As we discuss below, in Agda we use *intuitionistic* logic, wher
we have only half of this equivalence, namely that `A` implies `¬ ¬ A`.
<pre class="Agda">{% raw %}
<a name="31073" href="Logic.html#31073" class="Function"
      >&#172;&#172;-intro</a
      ><a name="31081"
      > </a
      ><a name="31082" class="Symbol"
      >:</a
      ><a name="31083"
      > </a
      ><a name="31084" class="Symbol"
      >&#8704;</a
      ><a name="31085"
      > </a
      ><a name="31086" class="Symbol"
      >{</a
      ><a name="31087" href="Logic.html#31087" class="Bound"
      >A</a
      ><a name="31088"
      > </a
      ><a name="31089" class="Symbol"
      >:</a
      ><a name="31090"
      > </a
      ><a name="31091" class="PrimitiveType"
      >Set</a
      ><a name="31094" class="Symbol"
      >}</a
      ><a name="31095"
      > </a
      ><a name="31096" class="Symbol"
      >&#8594;</a
      ><a name="31097"
      > </a
      ><a name="31098" href="Logic.html#31087" class="Bound"
      >A</a
      ><a name="31099"
      > </a
      ><a name="31100" class="Symbol"
      >&#8594;</a
      ><a name="31101"
      > </a
      ><a name="31102" href="Logic.html#29737" class="Function Operator"
      >&#172;</a
      ><a name="31103"
      > </a
      ><a name="31104" href="Logic.html#29737" class="Function Operator"
      >&#172;</a
      ><a name="31105"
      > </a
      ><a name="31106" href="Logic.html#31087" class="Bound"
      >A</a
      ><a name="31107"
      >
</a
      ><a name="31108" href="Logic.html#31073" class="Function"
      >&#172;&#172;-intro</a
      ><a name="31116"
      > </a
      ><a name="31117" href="Logic.html#31117" class="Bound"
      >a</a
      ><a name="31118"
      > </a
      ><a name="31119" href="Logic.html#31119" class="Bound"
      >&#172;a</a
      ><a name="31121"
      > </a
      ><a name="31122" class="Symbol"
      >=</a
      ><a name="31123"
      > </a
      ><a name="31124" href="Logic.html#31119" class="Bound"
      >&#172;a</a
      ><a name="31126"
      > </a
      ><a name="31127" href="Logic.html#31117" class="Bound"
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
<a name="31491" href="Logic.html#31491" class="Function"
      >&#172;&#172;&#172;-elim</a
      ><a name="31499"
      > </a
      ><a name="31500" class="Symbol"
      >:</a
      ><a name="31501"
      > </a
      ><a name="31502" class="Symbol"
      >&#8704;</a
      ><a name="31503"
      > </a
      ><a name="31504" class="Symbol"
      >{</a
      ><a name="31505" href="Logic.html#31505" class="Bound"
      >A</a
      ><a name="31506"
      > </a
      ><a name="31507" class="Symbol"
      >:</a
      ><a name="31508"
      > </a
      ><a name="31509" class="PrimitiveType"
      >Set</a
      ><a name="31512" class="Symbol"
      >}</a
      ><a name="31513"
      > </a
      ><a name="31514" class="Symbol"
      >&#8594;</a
      ><a name="31515"
      > </a
      ><a name="31516" href="Logic.html#29737" class="Function Operator"
      >&#172;</a
      ><a name="31517"
      > </a
      ><a name="31518" href="Logic.html#29737" class="Function Operator"
      >&#172;</a
      ><a name="31519"
      > </a
      ><a name="31520" href="Logic.html#29737" class="Function Operator"
      >&#172;</a
      ><a name="31521"
      > </a
      ><a name="31522" href="Logic.html#31505" class="Bound"
      >A</a
      ><a name="31523"
      > </a
      ><a name="31524" class="Symbol"
      >&#8594;</a
      ><a name="31525"
      > </a
      ><a name="31526" href="Logic.html#29737" class="Function Operator"
      >&#172;</a
      ><a name="31527"
      > </a
      ><a name="31528" href="Logic.html#31505" class="Bound"
      >A</a
      ><a name="31529"
      >
</a
      ><a name="31530" href="Logic.html#31491" class="Function"
      >&#172;&#172;&#172;-elim</a
      ><a name="31538"
      > </a
      ><a name="31539" href="Logic.html#31539" class="Bound"
      >&#172;&#172;&#172;a</a
      ><a name="31543"
      > </a
      ><a name="31544" href="Logic.html#31544" class="Bound"
      >a</a
      ><a name="31545"
      > </a
      ><a name="31546" class="Symbol"
      >=</a
      ><a name="31547"
      > </a
      ><a name="31548" href="Logic.html#31539" class="Bound"
      >&#172;&#172;&#172;a</a
      ><a name="31552"
      > </a
      ><a name="31553" class="Symbol"
      >(</a
      ><a name="31554" href="Logic.html#31073" class="Function"
      >&#172;&#172;-intro</a
      ><a name="31562"
      > </a
      ><a name="31563" href="Logic.html#31544" class="Bound"
      >a</a
      ><a name="31564" class="Symbol"
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
<a name="32047" href="Logic.html#32047" class="Function"
      >contrapositive</a
      ><a name="32061"
      > </a
      ><a name="32062" class="Symbol"
      >:</a
      ><a name="32063"
      > </a
      ><a name="32064" class="Symbol"
      >&#8704;</a
      ><a name="32065"
      > </a
      ><a name="32066" class="Symbol"
      >{</a
      ><a name="32067" href="Logic.html#32067" class="Bound"
      >A</a
      ><a name="32068"
      > </a
      ><a name="32069" href="Logic.html#32069" class="Bound"
      >B</a
      ><a name="32070"
      > </a
      ><a name="32071" class="Symbol"
      >:</a
      ><a name="32072"
      > </a
      ><a name="32073" class="PrimitiveType"
      >Set</a
      ><a name="32076" class="Symbol"
      >}</a
      ><a name="32077"
      > </a
      ><a name="32078" class="Symbol"
      >&#8594;</a
      ><a name="32079"
      > </a
      ><a name="32080" class="Symbol"
      >(</a
      ><a name="32081" href="Logic.html#32067" class="Bound"
      >A</a
      ><a name="32082"
      > </a
      ><a name="32083" class="Symbol"
      >&#8594;</a
      ><a name="32084"
      > </a
      ><a name="32085" href="Logic.html#32069" class="Bound"
      >B</a
      ><a name="32086" class="Symbol"
      >)</a
      ><a name="32087"
      > </a
      ><a name="32088" class="Symbol"
      >&#8594;</a
      ><a name="32089"
      > </a
      ><a name="32090" class="Symbol"
      >(</a
      ><a name="32091" href="Logic.html#29737" class="Function Operator"
      >&#172;</a
      ><a name="32092"
      > </a
      ><a name="32093" href="Logic.html#32069" class="Bound"
      >B</a
      ><a name="32094"
      > </a
      ><a name="32095" class="Symbol"
      >&#8594;</a
      ><a name="32096"
      > </a
      ><a name="32097" href="Logic.html#29737" class="Function Operator"
      >&#172;</a
      ><a name="32098"
      > </a
      ><a name="32099" href="Logic.html#32067" class="Bound"
      >A</a
      ><a name="32100" class="Symbol"
      >)</a
      ><a name="32101"
      >
</a
      ><a name="32102" href="Logic.html#32047" class="Function"
      >contrapositive</a
      ><a name="32116"
      > </a
      ><a name="32117" href="Logic.html#32117" class="Bound"
      >a&#8594;b</a
      ><a name="32120"
      > </a
      ><a name="32121" href="Logic.html#32121" class="Bound"
      >&#172;b</a
      ><a name="32123"
      > </a
      ><a name="32124" href="Logic.html#32124" class="Bound"
      >a</a
      ><a name="32125"
      > </a
      ><a name="32126" class="Symbol"
      >=</a
      ><a name="32127"
      > </a
      ><a name="32128" href="Logic.html#32121" class="Bound"
      >&#172;b</a
      ><a name="32130"
      > </a
      ><a name="32131" class="Symbol"
      >(</a
      ><a name="32132" href="Logic.html#32117" class="Bound"
      >a&#8594;b</a
      ><a name="32135"
      > </a
      ><a name="32136" href="Logic.html#32124" class="Bound"
      >a</a
      ><a name="32137" class="Symbol"
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
<a name="32831" href="Logic.html#32831" class="Function"
      >id</a
      ><a name="32833"
      > </a
      ><a name="32834" class="Symbol"
      >:</a
      ><a name="32835"
      > </a
      ><a name="32836" href="Logic.html#19450" class="Datatype"
      >&#8869;</a
      ><a name="32837"
      > </a
      ><a name="32838" class="Symbol"
      >&#8594;</a
      ><a name="32839"
      > </a
      ><a name="32840" href="Logic.html#19450" class="Datatype"
      >&#8869;</a
      ><a name="32841"
      >
</a
      ><a name="32842" href="Logic.html#32831" class="Function"
      >id</a
      ><a name="32844"
      > </a
      ><a name="32845" href="Logic.html#32845" class="Bound"
      >x</a
      ><a name="32846"
      > </a
      ><a name="32847" class="Symbol"
      >=</a
      ><a name="32848"
      > </a
      ><a name="32849" href="Logic.html#32845" class="Bound"
      >x</a
      >
{% endraw %}</pre>
However, there are no possible values of type `Bool → ⊥`
or `ℕ → bot`.

[TODO?: Give the proof that one cannot falsify law of the excluded middle,
including a variant of the story from Call-by-Value is Dual to Call-by-Name.]

The law of the excluded middle is irrefutable.
<pre class="Agda">{% raw %}
<a name="33148" href="Logic.html#33148" class="Function"
      >excluded-middle-irrefutable</a
      ><a name="33175"
      > </a
      ><a name="33176" class="Symbol"
      >:</a
      ><a name="33177"
      > </a
      ><a name="33178" class="Symbol"
      >&#8704;</a
      ><a name="33179"
      > </a
      ><a name="33180" class="Symbol"
      >{</a
      ><a name="33181" href="Logic.html#33181" class="Bound"
      >A</a
      ><a name="33182"
      > </a
      ><a name="33183" class="Symbol"
      >:</a
      ><a name="33184"
      > </a
      ><a name="33185" class="PrimitiveType"
      >Set</a
      ><a name="33188" class="Symbol"
      >}</a
      ><a name="33189"
      > </a
      ><a name="33190" class="Symbol"
      >&#8594;</a
      ><a name="33191"
      > </a
      ><a name="33192" href="Logic.html#29737" class="Function Operator"
      >&#172;</a
      ><a name="33193"
      > </a
      ><a name="33194" href="Logic.html#29737" class="Function Operator"
      >&#172;</a
      ><a name="33195"
      > </a
      ><a name="33196" class="Symbol"
      >(</a
      ><a name="33197" href="Logic.html#33181" class="Bound"
      >A</a
      ><a name="33198"
      > </a
      ><a name="33199" href="Logic.html#14656" class="Datatype Operator"
      >&#8846;</a
      ><a name="33200"
      > </a
      ><a name="33201" href="Logic.html#29737" class="Function Operator"
      >&#172;</a
      ><a name="33202"
      > </a
      ><a name="33203" href="Logic.html#33181" class="Bound"
      >A</a
      ><a name="33204" class="Symbol"
      >)</a
      ><a name="33205"
      >
</a
      ><a name="33206" href="Logic.html#33148" class="Function"
      >excluded-middle-irrefutable</a
      ><a name="33233"
      > </a
      ><a name="33234" href="Logic.html#33234" class="Bound"
      >k</a
      ><a name="33235"
      > </a
      ><a name="33236" class="Symbol"
      >=</a
      ><a name="33237"
      > </a
      ><a name="33238" href="Logic.html#33234" class="Bound"
      >k</a
      ><a name="33239"
      > </a
      ><a name="33240" class="Symbol"
      >(</a
      ><a name="33241" href="Logic.html#14722" class="InductiveConstructor"
      >inj&#8322;</a
      ><a name="33245"
      > </a
      ><a name="33246" class="Symbol"
      >(&#955;</a
      ><a name="33248"
      > </a
      ><a name="33249" href="Logic.html#33249" class="Bound"
      >a</a
      ><a name="33250"
      > </a
      ><a name="33251" class="Symbol"
      >&#8594;</a
      ><a name="33252"
      > </a
      ><a name="33253" href="Logic.html#33234" class="Bound"
      >k</a
      ><a name="33254"
      > </a
      ><a name="33255" class="Symbol"
      >(</a
      ><a name="33256" href="Logic.html#14686" class="InductiveConstructor"
      >inj&#8321;</a
      ><a name="33260"
      > </a
      ><a name="33261" href="Logic.html#33249" class="Bound"
      >a</a
      ><a name="33262" class="Symbol"
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
<a name="35606" href="Logic.html#35606" class="Function"
      >lone</a
      ><a name="35610"
      > </a
      ><a name="35611" href="Logic.html#35611" class="Function"
      >ltwo</a
      ><a name="35615"
      > </a
      ><a name="35616" class="Symbol"
      >:</a
      ><a name="35617"
      > </a
      ><a name="35618" href="Agda.Primitive.html#408" class="Postulate"
      >Level</a
      ><a name="35623"
      >
</a
      ><a name="35624" href="Logic.html#35606" class="Function"
      >lone</a
      ><a name="35628"
      > </a
      ><a name="35629" class="Symbol"
      >=</a
      ><a name="35630"
      > </a
      ><a name="35631" href="Agda.Primitive.html#625" class="Primitive"
      >lsuc</a
      ><a name="35635"
      > </a
      ><a name="35636" href="Agda.Primitive.html#609" class="Primitive"
      >lzero</a
      ><a name="35641"
      >
</a
      ><a name="35642" href="Logic.html#35611" class="Function"
      >ltwo</a
      ><a name="35646"
      > </a
      ><a name="35647" class="Symbol"
      >=</a
      ><a name="35648"
      > </a
      ><a name="35649" href="Agda.Primitive.html#625" class="Primitive"
      >lsuc</a
      ><a name="35653"
      > </a
      ><a name="35654" href="Logic.html#35606" class="Function"
      >lone</a
      ><a name="35658"
      >

</a
      ><a name="35660" href="Logic.html#35660" class="Function"
      >&#172;&#172;-elim</a
      ><a name="35667"
      > </a
      ><a name="35668" href="Logic.html#35668" class="Function"
      >excluded-middle</a
      ><a name="35683"
      > </a
      ><a name="35684" href="Logic.html#35684" class="Function"
      >peirce</a
      ><a name="35690"
      > </a
      ><a name="35691" href="Logic.html#35691" class="Function"
      >implication</a
      ><a name="35702"
      > </a
      ><a name="35703" href="Logic.html#35703" class="Function"
      >de-morgan</a
      ><a name="35712"
      > </a
      ><a name="35713" class="Symbol"
      >:</a
      ><a name="35714"
      > </a
      ><a name="35715" class="PrimitiveType"
      >Set</a
      ><a name="35718"
      > </a
      ><a name="35719" href="Logic.html#35606" class="Function"
      >lone</a
      ><a name="35723"
      >
</a
      ><a name="35724" href="Logic.html#35660" class="Function"
      >&#172;&#172;-elim</a
      ><a name="35731"
      > </a
      ><a name="35732" class="Symbol"
      >=</a
      ><a name="35733"
      > </a
      ><a name="35734" class="Symbol"
      >&#8704;</a
      ><a name="35735"
      > </a
      ><a name="35736" class="Symbol"
      >{</a
      ><a name="35737" href="Logic.html#35737" class="Bound"
      >A</a
      ><a name="35738"
      > </a
      ><a name="35739" class="Symbol"
      >:</a
      ><a name="35740"
      > </a
      ><a name="35741" class="PrimitiveType"
      >Set</a
      ><a name="35744" class="Symbol"
      >}</a
      ><a name="35745"
      > </a
      ><a name="35746" class="Symbol"
      >&#8594;</a
      ><a name="35747"
      > </a
      ><a name="35748" href="Logic.html#29737" class="Function Operator"
      >&#172;</a
      ><a name="35749"
      > </a
      ><a name="35750" href="Logic.html#29737" class="Function Operator"
      >&#172;</a
      ><a name="35751"
      > </a
      ><a name="35752" href="Logic.html#35737" class="Bound"
      >A</a
      ><a name="35753"
      > </a
      ><a name="35754" class="Symbol"
      >&#8594;</a
      ><a name="35755"
      > </a
      ><a name="35756" href="Logic.html#35737" class="Bound"
      >A</a
      ><a name="35757"
      >
</a
      ><a name="35758" href="Logic.html#35668" class="Function"
      >excluded-middle</a
      ><a name="35773"
      > </a
      ><a name="35774" class="Symbol"
      >=</a
      ><a name="35775"
      > </a
      ><a name="35776" class="Symbol"
      >&#8704;</a
      ><a name="35777"
      > </a
      ><a name="35778" class="Symbol"
      >{</a
      ><a name="35779" href="Logic.html#35779" class="Bound"
      >A</a
      ><a name="35780"
      > </a
      ><a name="35781" class="Symbol"
      >:</a
      ><a name="35782"
      > </a
      ><a name="35783" class="PrimitiveType"
      >Set</a
      ><a name="35786" class="Symbol"
      >}</a
      ><a name="35787"
      > </a
      ><a name="35788" class="Symbol"
      >&#8594;</a
      ><a name="35789"
      > </a
      ><a name="35790" href="Logic.html#35779" class="Bound"
      >A</a
      ><a name="35791"
      > </a
      ><a name="35792" href="Logic.html#14656" class="Datatype Operator"
      >&#8846;</a
      ><a name="35793"
      > </a
      ><a name="35794" href="Logic.html#29737" class="Function Operator"
      >&#172;</a
      ><a name="35795"
      > </a
      ><a name="35796" href="Logic.html#35779" class="Bound"
      >A</a
      ><a name="35797"
      >
</a
      ><a name="35798" href="Logic.html#35684" class="Function"
      >peirce</a
      ><a name="35804"
      > </a
      ><a name="35805" class="Symbol"
      >=</a
      ><a name="35806"
      > </a
      ><a name="35807" class="Symbol"
      >&#8704;</a
      ><a name="35808"
      > </a
      ><a name="35809" class="Symbol"
      >{</a
      ><a name="35810" href="Logic.html#35810" class="Bound"
      >A</a
      ><a name="35811"
      > </a
      ><a name="35812" href="Logic.html#35812" class="Bound"
      >B</a
      ><a name="35813"
      > </a
      ><a name="35814" class="Symbol"
      >:</a
      ><a name="35815"
      > </a
      ><a name="35816" class="PrimitiveType"
      >Set</a
      ><a name="35819" class="Symbol"
      >}</a
      ><a name="35820"
      > </a
      ><a name="35821" class="Symbol"
      >&#8594;</a
      ><a name="35822"
      > </a
      ><a name="35823" class="Symbol"
      >(((</a
      ><a name="35826" href="Logic.html#35810" class="Bound"
      >A</a
      ><a name="35827"
      > </a
      ><a name="35828" class="Symbol"
      >&#8594;</a
      ><a name="35829"
      > </a
      ><a name="35830" href="Logic.html#35812" class="Bound"
      >B</a
      ><a name="35831" class="Symbol"
      >)</a
      ><a name="35832"
      > </a
      ><a name="35833" class="Symbol"
      >&#8594;</a
      ><a name="35834"
      > </a
      ><a name="35835" href="Logic.html#35810" class="Bound"
      >A</a
      ><a name="35836" class="Symbol"
      >)</a
      ><a name="35837"
      > </a
      ><a name="35838" class="Symbol"
      >&#8594;</a
      ><a name="35839"
      > </a
      ><a name="35840" href="Logic.html#35810" class="Bound"
      >A</a
      ><a name="35841" class="Symbol"
      >)</a
      ><a name="35842"
      >
</a
      ><a name="35843" href="Logic.html#35691" class="Function"
      >implication</a
      ><a name="35854"
      > </a
      ><a name="35855" class="Symbol"
      >=</a
      ><a name="35856"
      > </a
      ><a name="35857" class="Symbol"
      >&#8704;</a
      ><a name="35858"
      > </a
      ><a name="35859" class="Symbol"
      >{</a
      ><a name="35860" href="Logic.html#35860" class="Bound"
      >A</a
      ><a name="35861"
      > </a
      ><a name="35862" href="Logic.html#35862" class="Bound"
      >B</a
      ><a name="35863"
      > </a
      ><a name="35864" class="Symbol"
      >:</a
      ><a name="35865"
      > </a
      ><a name="35866" class="PrimitiveType"
      >Set</a
      ><a name="35869" class="Symbol"
      >}</a
      ><a name="35870"
      > </a
      ><a name="35871" class="Symbol"
      >&#8594;</a
      ><a name="35872"
      > </a
      ><a name="35873" class="Symbol"
      >(</a
      ><a name="35874" href="Logic.html#35860" class="Bound"
      >A</a
      ><a name="35875"
      > </a
      ><a name="35876" class="Symbol"
      >&#8594;</a
      ><a name="35877"
      > </a
      ><a name="35878" href="Logic.html#35862" class="Bound"
      >B</a
      ><a name="35879" class="Symbol"
      >)</a
      ><a name="35880"
      > </a
      ><a name="35881" class="Symbol"
      >&#8594;</a
      ><a name="35882"
      > </a
      ><a name="35883" href="Logic.html#29737" class="Function Operator"
      >&#172;</a
      ><a name="35884"
      > </a
      ><a name="35885" href="Logic.html#35860" class="Bound"
      >A</a
      ><a name="35886"
      > </a
      ><a name="35887" href="Logic.html#14656" class="Datatype Operator"
      >&#8846;</a
      ><a name="35888"
      > </a
      ><a name="35889" href="Logic.html#35862" class="Bound"
      >B</a
      ><a name="35890"
      >
</a
      ><a name="35891" href="Logic.html#35703" class="Function"
      >de-morgan</a
      ><a name="35900"
      > </a
      ><a name="35901" class="Symbol"
      >=</a
      ><a name="35902"
      > </a
      ><a name="35903" class="Symbol"
      >&#8704;</a
      ><a name="35904"
      > </a
      ><a name="35905" class="Symbol"
      >{</a
      ><a name="35906" href="Logic.html#35906" class="Bound"
      >A</a
      ><a name="35907"
      > </a
      ><a name="35908" href="Logic.html#35908" class="Bound"
      >B</a
      ><a name="35909"
      > </a
      ><a name="35910" class="Symbol"
      >:</a
      ><a name="35911"
      > </a
      ><a name="35912" class="PrimitiveType"
      >Set</a
      ><a name="35915" class="Symbol"
      >}</a
      ><a name="35916"
      > </a
      ><a name="35917" class="Symbol"
      >&#8594;</a
      ><a name="35918"
      > </a
      ><a name="35919" href="Logic.html#29737" class="Function Operator"
      >&#172;</a
      ><a name="35920"
      > </a
      ><a name="35921" class="Symbol"
      >(</a
      ><a name="35922" href="Logic.html#29737" class="Function Operator"
      >&#172;</a
      ><a name="35923"
      > </a
      ><a name="35924" href="Logic.html#35906" class="Bound"
      >A</a
      ><a name="35925"
      > </a
      ><a name="35926" href="Logic.html#7202" class="Datatype Operator"
      >&#215;</a
      ><a name="35927"
      > </a
      ><a name="35928" href="Logic.html#29737" class="Function Operator"
      >&#172;</a
      ><a name="35929"
      > </a
      ><a name="35930" href="Logic.html#35908" class="Bound"
      >B</a
      ><a name="35931" class="Symbol"
      >)</a
      ><a name="35932"
      > </a
      ><a name="35933" class="Symbol"
      >&#8594;</a
      ><a name="35934"
      > </a
      ><a name="35935" href="Logic.html#35906" class="Bound"
      >A</a
      ><a name="35936"
      > </a
      ><a name="35937" href="Logic.html#14656" class="Datatype Operator"
      >&#8846;</a
      ><a name="35938"
      > </a
      ><a name="35939" href="Logic.html#35908" class="Bound"
      >B</a
      ><a name="35940"
      >
</a
      ><a name="35941" href="Logic.html#35941" class="Function"
      >de-morgan&#8242;</a
      ><a name="35951"
      > </a
      ><a name="35952" class="Symbol"
      >=</a
      ><a name="35953"
      > </a
      ><a name="35954" class="Symbol"
      >&#8704;</a
      ><a name="35955"
      > </a
      ><a name="35956" class="Symbol"
      >{</a
      ><a name="35957" href="Logic.html#35957" class="Bound"
      >A</a
      ><a name="35958"
      > </a
      ><a name="35959" href="Logic.html#35959" class="Bound"
      >B</a
      ><a name="35960"
      > </a
      ><a name="35961" class="Symbol"
      >:</a
      ><a name="35962"
      > </a
      ><a name="35963" class="PrimitiveType"
      >Set</a
      ><a name="35966" class="Symbol"
      >}</a
      ><a name="35967"
      > </a
      ><a name="35968" class="Symbol"
      >&#8594;</a
      ><a name="35969"
      > </a
      ><a name="35970" href="Logic.html#29737" class="Function Operator"
      >&#172;</a
      ><a name="35971"
      > </a
      ><a name="35972" class="Symbol"
      >(</a
      ><a name="35973" href="Logic.html#29737" class="Function Operator"
      >&#172;</a
      ><a name="35974"
      > </a
      ><a name="35975" href="Logic.html#35957" class="Bound"
      >A</a
      ><a name="35976"
      > </a
      ><a name="35977" href="Logic.html#14656" class="Datatype Operator"
      >&#8846;</a
      ><a name="35978"
      > </a
      ><a name="35979" href="Logic.html#29737" class="Function Operator"
      >&#172;</a
      ><a name="35980"
      > </a
      ><a name="35981" href="Logic.html#35959" class="Bound"
      >B</a
      ><a name="35982" class="Symbol"
      >)</a
      ><a name="35983"
      > </a
      ><a name="35984" class="Symbol"
      >&#8594;</a
      ><a name="35985"
      > </a
      ><a name="35986" href="Logic.html#35957" class="Bound"
      >A</a
      ><a name="35987"
      > </a
      ><a name="35988" href="Logic.html#7202" class="Datatype Operator"
      >&#215;</a
      ><a name="35989"
      > </a
      ><a name="35990" href="Logic.html#35959" class="Bound"
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

## Existentials

## Decidability

<pre class="Agda">{% raw %}
<a name="36678" class="Keyword"
      >data</a
      ><a name="36682"
      > </a
      ><a name="36683" href="Logic.html#36683" class="Datatype"
      >Dec</a
      ><a name="36686"
      > </a
      ><a name="36687" class="Symbol"
      >:</a
      ><a name="36688"
      > </a
      ><a name="36689" class="PrimitiveType"
      >Set</a
      ><a name="36692"
      > </a
      ><a name="36693" class="Symbol"
      >&#8594;</a
      ><a name="36694"
      > </a
      ><a name="36695" class="PrimitiveType"
      >Set</a
      ><a name="36698"
      > </a
      ><a name="36699" class="Keyword"
      >where</a
      ><a name="36704"
      >
  </a
      ><a name="36707" href="Logic.html#36707" class="InductiveConstructor"
      >yes</a
      ><a name="36710"
      > </a
      ><a name="36711" class="Symbol"
      >:</a
      ><a name="36712"
      > </a
      ><a name="36713" class="Symbol"
      >&#8704;</a
      ><a name="36714"
      > </a
      ><a name="36715" class="Symbol"
      >{</a
      ><a name="36716" href="Logic.html#36716" class="Bound"
      >A</a
      ><a name="36717"
      > </a
      ><a name="36718" class="Symbol"
      >:</a
      ><a name="36719"
      > </a
      ><a name="36720" class="PrimitiveType"
      >Set</a
      ><a name="36723" class="Symbol"
      >}</a
      ><a name="36724"
      > </a
      ><a name="36725" class="Symbol"
      >&#8594;</a
      ><a name="36726"
      > </a
      ><a name="36727" href="Logic.html#36716" class="Bound"
      >A</a
      ><a name="36728"
      > </a
      ><a name="36729" class="Symbol"
      >&#8594;</a
      ><a name="36730"
      > </a
      ><a name="36731" href="Logic.html#36683" class="Datatype"
      >Dec</a
      ><a name="36734"
      > </a
      ><a name="36735" href="Logic.html#36716" class="Bound"
      >A</a
      ><a name="36736"
      >
  </a
      ><a name="36739" href="Logic.html#36739" class="InductiveConstructor"
      >no</a
      ><a name="36741"
      >  </a
      ><a name="36743" class="Symbol"
      >:</a
      ><a name="36744"
      > </a
      ><a name="36745" class="Symbol"
      >&#8704;</a
      ><a name="36746"
      > </a
      ><a name="36747" class="Symbol"
      >{</a
      ><a name="36748" href="Logic.html#36748" class="Bound"
      >A</a
      ><a name="36749"
      > </a
      ><a name="36750" class="Symbol"
      >:</a
      ><a name="36751"
      > </a
      ><a name="36752" class="PrimitiveType"
      >Set</a
      ><a name="36755" class="Symbol"
      >}</a
      ><a name="36756"
      > </a
      ><a name="36757" class="Symbol"
      >&#8594;</a
      ><a name="36758"
      > </a
      ><a name="36759" class="Symbol"
      >(</a
      ><a name="36760" href="Logic.html#29737" class="Function Operator"
      >&#172;</a
      ><a name="36761"
      > </a
      ><a name="36762" href="Logic.html#36748" class="Bound"
      >A</a
      ><a name="36763" class="Symbol"
      >)</a
      ><a name="36764"
      > </a
      ><a name="36765" class="Symbol"
      >&#8594;</a
      ><a name="36766"
      > </a
      ><a name="36767" href="Logic.html#36683" class="Datatype"
      >Dec</a
      ><a name="36770"
      > </a
      ><a name="36771" href="Logic.html#36748" class="Bound"
      >A</a
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
<a name="37064" href="Logic.html#37064" class="Function"
      >dem1</a
      ><a name="37068"
      > </a
      ><a name="37069" class="Symbol"
      >:</a
      ><a name="37070"
      > </a
      ><a name="37071" class="Symbol"
      >&#8704;</a
      ><a name="37072"
      > </a
      ><a name="37073" class="Symbol"
      >{</a
      ><a name="37074" href="Logic.html#37074" class="Bound"
      >A</a
      ><a name="37075"
      > </a
      ><a name="37076" href="Logic.html#37076" class="Bound"
      >B</a
      ><a name="37077"
      > </a
      ><a name="37078" class="Symbol"
      >:</a
      ><a name="37079"
      > </a
      ><a name="37080" class="PrimitiveType"
      >Set</a
      ><a name="37083" class="Symbol"
      >}</a
      ><a name="37084"
      > </a
      ><a name="37085" class="Symbol"
      >&#8594;</a
      ><a name="37086"
      > </a
      ><a name="37087" href="Logic.html#37074" class="Bound"
      >A</a
      ><a name="37088"
      > </a
      ><a name="37089" href="Logic.html#7202" class="Datatype Operator"
      >&#215;</a
      ><a name="37090"
      > </a
      ><a name="37091" href="Logic.html#37076" class="Bound"
      >B</a
      ><a name="37092"
      > </a
      ><a name="37093" class="Symbol"
      >&#8594;</a
      ><a name="37094"
      > </a
      ><a name="37095" href="Logic.html#29737" class="Function Operator"
      >&#172;</a
      ><a name="37096"
      > </a
      ><a name="37097" class="Symbol"
      >(</a
      ><a name="37098" href="Logic.html#29737" class="Function Operator"
      >&#172;</a
      ><a name="37099"
      > </a
      ><a name="37100" href="Logic.html#37074" class="Bound"
      >A</a
      ><a name="37101"
      > </a
      ><a name="37102" href="Logic.html#14656" class="Datatype Operator"
      >&#8846;</a
      ><a name="37103"
      > </a
      ><a name="37104" href="Logic.html#29737" class="Function Operator"
      >&#172;</a
      ><a name="37105"
      > </a
      ><a name="37106" href="Logic.html#37076" class="Bound"
      >B</a
      ><a name="37107" class="Symbol"
      >)</a
      ><a name="37108"
      >
</a
      ><a name="37109" href="Logic.html#37064" class="Function"
      >dem1</a
      ><a name="37113"
      > </a
      ><a name="37114" class="Symbol"
      >(</a
      ><a name="37115" href="Logic.html#37115" class="Bound"
      >a</a
      ><a name="37116"
      > </a
      ><a name="37117" href="Logic.html#7232" class="InductiveConstructor Operator"
      >,</a
      ><a name="37118"
      > </a
      ><a name="37119" href="Logic.html#37119" class="Bound"
      >b</a
      ><a name="37120" class="Symbol"
      >)</a
      ><a name="37121"
      > </a
      ><a name="37122" class="Symbol"
      >(</a
      ><a name="37123" href="Logic.html#14686" class="InductiveConstructor"
      >inj&#8321;</a
      ><a name="37127"
      > </a
      ><a name="37128" href="Logic.html#37128" class="Bound"
      >&#172;a</a
      ><a name="37130" class="Symbol"
      >)</a
      ><a name="37131"
      > </a
      ><a name="37132" class="Symbol"
      >=</a
      ><a name="37133"
      > </a
      ><a name="37134" href="Logic.html#37128" class="Bound"
      >&#172;a</a
      ><a name="37136"
      > </a
      ><a name="37137" href="Logic.html#37115" class="Bound"
      >a</a
      ><a name="37138"
      >
</a
      ><a name="37139" href="Logic.html#37064" class="Function"
      >dem1</a
      ><a name="37143"
      > </a
      ><a name="37144" class="Symbol"
      >(</a
      ><a name="37145" href="Logic.html#37145" class="Bound"
      >a</a
      ><a name="37146"
      > </a
      ><a name="37147" href="Logic.html#7232" class="InductiveConstructor Operator"
      >,</a
      ><a name="37148"
      > </a
      ><a name="37149" href="Logic.html#37149" class="Bound"
      >b</a
      ><a name="37150" class="Symbol"
      >)</a
      ><a name="37151"
      > </a
      ><a name="37152" class="Symbol"
      >(</a
      ><a name="37153" href="Logic.html#14722" class="InductiveConstructor"
      >inj&#8322;</a
      ><a name="37157"
      > </a
      ><a name="37158" href="Logic.html#37158" class="Bound"
      >&#172;b</a
      ><a name="37160" class="Symbol"
      >)</a
      ><a name="37161"
      > </a
      ><a name="37162" class="Symbol"
      >=</a
      ><a name="37163"
      > </a
      ><a name="37164" href="Logic.html#37158" class="Bound"
      >&#172;b</a
      ><a name="37166"
      > </a
      ><a name="37167" href="Logic.html#37149" class="Bound"
      >b</a
      ><a name="37168"
      >

</a
      ><a name="37170" href="Logic.html#37170" class="Function"
      >dem2</a
      ><a name="37174"
      > </a
      ><a name="37175" class="Symbol"
      >:</a
      ><a name="37176"
      > </a
      ><a name="37177" class="Symbol"
      >&#8704;</a
      ><a name="37178"
      > </a
      ><a name="37179" class="Symbol"
      >{</a
      ><a name="37180" href="Logic.html#37180" class="Bound"
      >A</a
      ><a name="37181"
      > </a
      ><a name="37182" href="Logic.html#37182" class="Bound"
      >B</a
      ><a name="37183"
      > </a
      ><a name="37184" class="Symbol"
      >:</a
      ><a name="37185"
      > </a
      ><a name="37186" class="PrimitiveType"
      >Set</a
      ><a name="37189" class="Symbol"
      >}</a
      ><a name="37190"
      > </a
      ><a name="37191" class="Symbol"
      >&#8594;</a
      ><a name="37192"
      > </a
      ><a name="37193" href="Logic.html#37180" class="Bound"
      >A</a
      ><a name="37194"
      > </a
      ><a name="37195" href="Logic.html#14656" class="Datatype Operator"
      >&#8846;</a
      ><a name="37196"
      > </a
      ><a name="37197" href="Logic.html#37182" class="Bound"
      >B</a
      ><a name="37198"
      > </a
      ><a name="37199" class="Symbol"
      >&#8594;</a
      ><a name="37200"
      > </a
      ><a name="37201" href="Logic.html#29737" class="Function Operator"
      >&#172;</a
      ><a name="37202"
      > </a
      ><a name="37203" class="Symbol"
      >(</a
      ><a name="37204" href="Logic.html#29737" class="Function Operator"
      >&#172;</a
      ><a name="37205"
      > </a
      ><a name="37206" href="Logic.html#37180" class="Bound"
      >A</a
      ><a name="37207"
      > </a
      ><a name="37208" href="Logic.html#7202" class="Datatype Operator"
      >&#215;</a
      ><a name="37209"
      > </a
      ><a name="37210" href="Logic.html#29737" class="Function Operator"
      >&#172;</a
      ><a name="37211"
      > </a
      ><a name="37212" href="Logic.html#37182" class="Bound"
      >B</a
      ><a name="37213" class="Symbol"
      >)</a
      ><a name="37214"
      >
</a
      ><a name="37215" href="Logic.html#37170" class="Function"
      >dem2</a
      ><a name="37219"
      > </a
      ><a name="37220" class="Symbol"
      >(</a
      ><a name="37221" href="Logic.html#14686" class="InductiveConstructor"
      >inj&#8321;</a
      ><a name="37225"
      > </a
      ><a name="37226" href="Logic.html#37226" class="Bound"
      >a</a
      ><a name="37227" class="Symbol"
      >)</a
      ><a name="37228"
      > </a
      ><a name="37229" class="Symbol"
      >(</a
      ><a name="37230" href="Logic.html#37230" class="Bound"
      >&#172;a</a
      ><a name="37232"
      > </a
      ><a name="37233" href="Logic.html#7232" class="InductiveConstructor Operator"
      >,</a
      ><a name="37234"
      > </a
      ><a name="37235" href="Logic.html#37235" class="Bound"
      >&#172;b</a
      ><a name="37237" class="Symbol"
      >)</a
      ><a name="37238"
      > </a
      ><a name="37239" class="Symbol"
      >=</a
      ><a name="37240"
      > </a
      ><a name="37241" href="Logic.html#37230" class="Bound"
      >&#172;a</a
      ><a name="37243"
      > </a
      ><a name="37244" href="Logic.html#37226" class="Bound"
      >a</a
      ><a name="37245"
      >
</a
      ><a name="37246" href="Logic.html#37170" class="Function"
      >dem2</a
      ><a name="37250"
      > </a
      ><a name="37251" class="Symbol"
      >(</a
      ><a name="37252" href="Logic.html#14722" class="InductiveConstructor"
      >inj&#8322;</a
      ><a name="37256"
      > </a
      ><a name="37257" href="Logic.html#37257" class="Bound"
      >b</a
      ><a name="37258" class="Symbol"
      >)</a
      ><a name="37259"
      > </a
      ><a name="37260" class="Symbol"
      >(</a
      ><a name="37261" href="Logic.html#37261" class="Bound"
      >&#172;a</a
      ><a name="37263"
      > </a
      ><a name="37264" href="Logic.html#7232" class="InductiveConstructor Operator"
      >,</a
      ><a name="37265"
      > </a
      ><a name="37266" href="Logic.html#37266" class="Bound"
      >&#172;b</a
      ><a name="37268" class="Symbol"
      >)</a
      ><a name="37269"
      > </a
      ><a name="37270" class="Symbol"
      >=</a
      ><a name="37271"
      > </a
      ><a name="37272" href="Logic.html#37266" class="Bound"
      >&#172;b</a
      ><a name="37274"
      > </a
      ><a name="37275" href="Logic.html#37257" class="Bound"
      >b</a
      >
{% endraw %}</pre>

For the other variant of De Morgan's law, one way is an isomorphism.
<pre class="Agda">{% raw %}
<a name="37371" href="Logic.html#37371" class="Function"
      >dem-&#8771;</a
      ><a name="37376"
      > </a
      ><a name="37377" class="Symbol"
      >:</a
      ><a name="37378"
      > </a
      ><a name="37379" class="Symbol"
      >&#8704;</a
      ><a name="37380"
      > </a
      ><a name="37381" class="Symbol"
      >{</a
      ><a name="37382" href="Logic.html#37382" class="Bound"
      >A</a
      ><a name="37383"
      > </a
      ><a name="37384" href="Logic.html#37384" class="Bound"
      >B</a
      ><a name="37385"
      > </a
      ><a name="37386" class="Symbol"
      >:</a
      ><a name="37387"
      > </a
      ><a name="37388" class="PrimitiveType"
      >Set</a
      ><a name="37391" class="Symbol"
      >}</a
      ><a name="37392"
      > </a
      ><a name="37393" class="Symbol"
      >&#8594;</a
      ><a name="37394"
      > </a
      ><a name="37395" class="Symbol"
      >(</a
      ><a name="37396" href="Logic.html#29737" class="Function Operator"
      >&#172;</a
      ><a name="37397"
      > </a
      ><a name="37398" class="Symbol"
      >(</a
      ><a name="37399" href="Logic.html#37382" class="Bound"
      >A</a
      ><a name="37400"
      > </a
      ><a name="37401" href="Logic.html#14656" class="Datatype Operator"
      >&#8846;</a
      ><a name="37402"
      > </a
      ><a name="37403" href="Logic.html#37384" class="Bound"
      >B</a
      ><a name="37404" class="Symbol"
      >))</a
      ><a name="37406"
      > </a
      ><a name="37407" href="Logic.html#1478" class="Record Operator"
      >&#8771;</a
      ><a name="37408"
      > </a
      ><a name="37409" class="Symbol"
      >(</a
      ><a name="37410" href="Logic.html#29737" class="Function Operator"
      >&#172;</a
      ><a name="37411"
      > </a
      ><a name="37412" href="Logic.html#37382" class="Bound"
      >A</a
      ><a name="37413"
      > </a
      ><a name="37414" href="Logic.html#7202" class="Datatype Operator"
      >&#215;</a
      ><a name="37415"
      > </a
      ><a name="37416" href="Logic.html#29737" class="Function Operator"
      >&#172;</a
      ><a name="37417"
      > </a
      ><a name="37418" href="Logic.html#37384" class="Bound"
      >B</a
      ><a name="37419" class="Symbol"
      >)</a
      ><a name="37420"
      >
</a
      ><a name="37421" href="Logic.html#37371" class="Function"
      >dem-&#8771;</a
      ><a name="37426"
      > </a
      ><a name="37427" class="Symbol"
      >=</a
      ><a name="37428"
      > </a
      ><a name="37429" href="Logic.html#26271" class="Function"
      >&#8594;-distributes-&#8846;</a
      >
{% endraw %}</pre>

The other holds in only one direction.
<pre class="Agda">{% raw %}
<a name="37509" href="Logic.html#37509" class="Function"
      >dem-half</a
      ><a name="37517"
      > </a
      ><a name="37518" class="Symbol"
      >:</a
      ><a name="37519"
      > </a
      ><a name="37520" class="Symbol"
      >&#8704;</a
      ><a name="37521"
      > </a
      ><a name="37522" class="Symbol"
      >{</a
      ><a name="37523" href="Logic.html#37523" class="Bound"
      >A</a
      ><a name="37524"
      > </a
      ><a name="37525" href="Logic.html#37525" class="Bound"
      >B</a
      ><a name="37526"
      > </a
      ><a name="37527" class="Symbol"
      >:</a
      ><a name="37528"
      > </a
      ><a name="37529" class="PrimitiveType"
      >Set</a
      ><a name="37532" class="Symbol"
      >}</a
      ><a name="37533"
      > </a
      ><a name="37534" class="Symbol"
      >&#8594;</a
      ><a name="37535"
      > </a
      ><a name="37536" href="Logic.html#29737" class="Function Operator"
      >&#172;</a
      ><a name="37537"
      > </a
      ><a name="37538" href="Logic.html#37523" class="Bound"
      >A</a
      ><a name="37539"
      > </a
      ><a name="37540" href="Logic.html#14656" class="Datatype Operator"
      >&#8846;</a
      ><a name="37541"
      > </a
      ><a name="37542" href="Logic.html#29737" class="Function Operator"
      >&#172;</a
      ><a name="37543"
      > </a
      ><a name="37544" href="Logic.html#37525" class="Bound"
      >B</a
      ><a name="37545"
      > </a
      ><a name="37546" class="Symbol"
      >&#8594;</a
      ><a name="37547"
      > </a
      ><a name="37548" href="Logic.html#29737" class="Function Operator"
      >&#172;</a
      ><a name="37549"
      > </a
      ><a name="37550" class="Symbol"
      >(</a
      ><a name="37551" href="Logic.html#37523" class="Bound"
      >A</a
      ><a name="37552"
      > </a
      ><a name="37553" href="Logic.html#7202" class="Datatype Operator"
      >&#215;</a
      ><a name="37554"
      > </a
      ><a name="37555" href="Logic.html#37525" class="Bound"
      >B</a
      ><a name="37556" class="Symbol"
      >)</a
      ><a name="37557"
      >
</a
      ><a name="37558" href="Logic.html#37509" class="Function"
      >dem-half</a
      ><a name="37566"
      > </a
      ><a name="37567" class="Symbol"
      >(</a
      ><a name="37568" href="Logic.html#14686" class="InductiveConstructor"
      >inj&#8321;</a
      ><a name="37572"
      > </a
      ><a name="37573" href="Logic.html#37573" class="Bound"
      >&#172;a</a
      ><a name="37575" class="Symbol"
      >)</a
      ><a name="37576"
      > </a
      ><a name="37577" class="Symbol"
      >(</a
      ><a name="37578" href="Logic.html#37578" class="Bound"
      >a</a
      ><a name="37579"
      > </a
      ><a name="37580" href="Logic.html#7232" class="InductiveConstructor Operator"
      >,</a
      ><a name="37581"
      > </a
      ><a name="37582" href="Logic.html#37582" class="Bound"
      >b</a
      ><a name="37583" class="Symbol"
      >)</a
      ><a name="37584"
      > </a
      ><a name="37585" class="Symbol"
      >=</a
      ><a name="37586"
      > </a
      ><a name="37587" href="Logic.html#37573" class="Bound"
      >&#172;a</a
      ><a name="37589"
      > </a
      ><a name="37590" href="Logic.html#37578" class="Bound"
      >a</a
      ><a name="37591"
      >
</a
      ><a name="37592" href="Logic.html#37509" class="Function"
      >dem-half</a
      ><a name="37600"
      > </a
      ><a name="37601" class="Symbol"
      >(</a
      ><a name="37602" href="Logic.html#14722" class="InductiveConstructor"
      >inj&#8322;</a
      ><a name="37606"
      > </a
      ><a name="37607" href="Logic.html#37607" class="Bound"
      >&#172;b</a
      ><a name="37609" class="Symbol"
      >)</a
      ><a name="37610"
      > </a
      ><a name="37611" class="Symbol"
      >(</a
      ><a name="37612" href="Logic.html#37612" class="Bound"
      >a</a
      ><a name="37613"
      > </a
      ><a name="37614" href="Logic.html#7232" class="InductiveConstructor Operator"
      >,</a
      ><a name="37615"
      > </a
      ><a name="37616" href="Logic.html#37616" class="Bound"
      >b</a
      ><a name="37617" class="Symbol"
      >)</a
      ><a name="37618"
      > </a
      ><a name="37619" class="Symbol"
      >=</a
      ><a name="37620"
      > </a
      ><a name="37621" href="Logic.html#37607" class="Bound"
      >&#172;b</a
      ><a name="37623"
      > </a
      ><a name="37624" href="Logic.html#37616" class="Bound"
      >b</a
      >
{% endraw %}</pre>

The other variant does not appear to be equivalent to classical logic.
So that undermines my idea that basic propositions are either true
intuitionistically or equivalent to classical logic.

For several of the laws equivalent to classical logic, the reverse
direction holds in intuitionistic long.
<pre class="Agda">{% raw %}
<a name="37950" href="Logic.html#37950" class="Function"
      >implication-inv</a
      ><a name="37965"
      > </a
      ><a name="37966" class="Symbol"
      >:</a
      ><a name="37967"
      > </a
      ><a name="37968" class="Symbol"
      >&#8704;</a
      ><a name="37969"
      > </a
      ><a name="37970" class="Symbol"
      >{</a
      ><a name="37971" href="Logic.html#37971" class="Bound"
      >A</a
      ><a name="37972"
      > </a
      ><a name="37973" href="Logic.html#37973" class="Bound"
      >B</a
      ><a name="37974"
      > </a
      ><a name="37975" class="Symbol"
      >:</a
      ><a name="37976"
      > </a
      ><a name="37977" class="PrimitiveType"
      >Set</a
      ><a name="37980" class="Symbol"
      >}</a
      ><a name="37981"
      > </a
      ><a name="37982" class="Symbol"
      >&#8594;</a
      ><a name="37983"
      > </a
      ><a name="37984" class="Symbol"
      >(</a
      ><a name="37985" href="Logic.html#29737" class="Function Operator"
      >&#172;</a
      ><a name="37986"
      > </a
      ><a name="37987" href="Logic.html#37971" class="Bound"
      >A</a
      ><a name="37988"
      > </a
      ><a name="37989" href="Logic.html#14656" class="Datatype Operator"
      >&#8846;</a
      ><a name="37990"
      > </a
      ><a name="37991" href="Logic.html#37973" class="Bound"
      >B</a
      ><a name="37992" class="Symbol"
      >)</a
      ><a name="37993"
      > </a
      ><a name="37994" class="Symbol"
      >&#8594;</a
      ><a name="37995"
      > </a
      ><a name="37996" href="Logic.html#37971" class="Bound"
      >A</a
      ><a name="37997"
      > </a
      ><a name="37998" class="Symbol"
      >&#8594;</a
      ><a name="37999"
      > </a
      ><a name="38000" href="Logic.html#37973" class="Bound"
      >B</a
      ><a name="38001"
      >
</a
      ><a name="38002" href="Logic.html#37950" class="Function"
      >implication-inv</a
      ><a name="38017"
      > </a
      ><a name="38018" class="Symbol"
      >(</a
      ><a name="38019" href="Logic.html#14686" class="InductiveConstructor"
      >inj&#8321;</a
      ><a name="38023"
      > </a
      ><a name="38024" href="Logic.html#38024" class="Bound"
      >&#172;a</a
      ><a name="38026" class="Symbol"
      >)</a
      ><a name="38027"
      > </a
      ><a name="38028" href="Logic.html#38028" class="Bound"
      >a</a
      ><a name="38029"
      > </a
      ><a name="38030" class="Symbol"
      >=</a
      ><a name="38031"
      > </a
      ><a name="38032" href="Logic.html#19890" class="Function"
      >&#8869;-elim</a
      ><a name="38038"
      > </a
      ><a name="38039" class="Symbol"
      >(</a
      ><a name="38040" href="Logic.html#38024" class="Bound"
      >&#172;a</a
      ><a name="38042"
      > </a
      ><a name="38043" href="Logic.html#38028" class="Bound"
      >a</a
      ><a name="38044" class="Symbol"
      >)</a
      ><a name="38045"
      >
</a
      ><a name="38046" href="Logic.html#37950" class="Function"
      >implication-inv</a
      ><a name="38061"
      > </a
      ><a name="38062" class="Symbol"
      >(</a
      ><a name="38063" href="Logic.html#14722" class="InductiveConstructor"
      >inj&#8322;</a
      ><a name="38067"
      > </a
      ><a name="38068" href="Logic.html#38068" class="Bound"
      >b</a
      ><a name="38069" class="Symbol"
      >)</a
      ><a name="38070"
      >  </a
      ><a name="38072" href="Logic.html#38072" class="Bound"
      >a</a
      ><a name="38073"
      > </a
      ><a name="38074" class="Symbol"
      >=</a
      ><a name="38075"
      > </a
      ><a name="38076" href="Logic.html#38068" class="Bound"
      >b</a
      ><a name="38077"
      >

</a
      ><a name="38079" href="Logic.html#38079" class="Function"
      >demorgan-inv</a
      ><a name="38091"
      > </a
      ><a name="38092" class="Symbol"
      >:</a
      ><a name="38093"
      > </a
      ><a name="38094" class="Symbol"
      >&#8704;</a
      ><a name="38095"
      > </a
      ><a name="38096" class="Symbol"
      >{</a
      ><a name="38097" href="Logic.html#38097" class="Bound"
      >A</a
      ><a name="38098"
      > </a
      ><a name="38099" href="Logic.html#38099" class="Bound"
      >B</a
      ><a name="38100"
      > </a
      ><a name="38101" class="Symbol"
      >:</a
      ><a name="38102"
      > </a
      ><a name="38103" class="PrimitiveType"
      >Set</a
      ><a name="38106" class="Symbol"
      >}</a
      ><a name="38107"
      > </a
      ><a name="38108" class="Symbol"
      >&#8594;</a
      ><a name="38109"
      > </a
      ><a name="38110" href="Logic.html#38097" class="Bound"
      >A</a
      ><a name="38111"
      > </a
      ><a name="38112" href="Logic.html#14656" class="Datatype Operator"
      >&#8846;</a
      ><a name="38113"
      > </a
      ><a name="38114" href="Logic.html#38099" class="Bound"
      >B</a
      ><a name="38115"
      > </a
      ><a name="38116" class="Symbol"
      >&#8594;</a
      ><a name="38117"
      > </a
      ><a name="38118" href="Logic.html#29737" class="Function Operator"
      >&#172;</a
      ><a name="38119"
      > </a
      ><a name="38120" class="Symbol"
      >(</a
      ><a name="38121" href="Logic.html#29737" class="Function Operator"
      >&#172;</a
      ><a name="38122"
      > </a
      ><a name="38123" href="Logic.html#38097" class="Bound"
      >A</a
      ><a name="38124"
      > </a
      ><a name="38125" href="Logic.html#7202" class="Datatype Operator"
      >&#215;</a
      ><a name="38126"
      > </a
      ><a name="38127" href="Logic.html#29737" class="Function Operator"
      >&#172;</a
      ><a name="38128"
      > </a
      ><a name="38129" href="Logic.html#38099" class="Bound"
      >B</a
      ><a name="38130" class="Symbol"
      >)</a
      ><a name="38131"
      >
</a
      ><a name="38132" href="Logic.html#38079" class="Function"
      >demorgan-inv</a
      ><a name="38144"
      > </a
      ><a name="38145" class="Symbol"
      >(</a
      ><a name="38146" href="Logic.html#14686" class="InductiveConstructor"
      >inj&#8321;</a
      ><a name="38150"
      > </a
      ><a name="38151" href="Logic.html#38151" class="Bound"
      >a</a
      ><a name="38152" class="Symbol"
      >)</a
      ><a name="38153"
      > </a
      ><a name="38154" class="Symbol"
      >(</a
      ><a name="38155" href="Logic.html#38155" class="Bound"
      >&#172;a</a
      ><a name="38157"
      > </a
      ><a name="38158" href="Logic.html#7232" class="InductiveConstructor Operator"
      >,</a
      ><a name="38159"
      > </a
      ><a name="38160" href="Logic.html#38160" class="Bound"
      >&#172;b</a
      ><a name="38162" class="Symbol"
      >)</a
      ><a name="38163"
      > </a
      ><a name="38164" class="Symbol"
      >=</a
      ><a name="38165"
      >  </a
      ><a name="38167" href="Logic.html#38155" class="Bound"
      >&#172;a</a
      ><a name="38169"
      > </a
      ><a name="38170" href="Logic.html#38151" class="Bound"
      >a</a
      ><a name="38171"
      >
</a
      ><a name="38172" href="Logic.html#38079" class="Function"
      >demorgan-inv</a
      ><a name="38184"
      > </a
      ><a name="38185" class="Symbol"
      >(</a
      ><a name="38186" href="Logic.html#14722" class="InductiveConstructor"
      >inj&#8322;</a
      ><a name="38190"
      > </a
      ><a name="38191" href="Logic.html#38191" class="Bound"
      >b</a
      ><a name="38192" class="Symbol"
      >)</a
      ><a name="38193"
      > </a
      ><a name="38194" class="Symbol"
      >(</a
      ><a name="38195" href="Logic.html#38195" class="Bound"
      >&#172;a</a
      ><a name="38197"
      > </a
      ><a name="38198" href="Logic.html#7232" class="InductiveConstructor Operator"
      >,</a
      ><a name="38199"
      > </a
      ><a name="38200" href="Logic.html#38200" class="Bound"
      >&#172;b</a
      ><a name="38202" class="Symbol"
      >)</a
      ><a name="38203"
      > </a
      ><a name="38204" class="Symbol"
      >=</a
      ><a name="38205"
      >  </a
      ><a name="38207" href="Logic.html#38200" class="Bound"
      >&#172;b</a
      ><a name="38209"
      > </a
      ><a name="38210" href="Logic.html#38191" class="Bound"
      >b</a
      >
{% endraw %}</pre>



    
