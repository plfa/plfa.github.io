---
title     : "StlcProp: Properties of STLC"
layout    : page
permalink : /StlcProp
---

In this chapter, we develop the fundamental theory of the Simply
Typed Lambda Calculus---in particular, the type safety
theorem.

## Imports

<pre class="Agda">

<a name="247" class="Keyword"
      >open</a
      ><a name="251"
      > </a
      ><a name="252" class="Keyword"
      >import</a
      ><a name="258"
      > </a
      ><a name="259" href="https://agda.github.io/agda-stdlib/Function.html#1" class="Module"
      >Function</a
      ><a name="267"
      > </a
      ><a name="268" class="Keyword"
      >using</a
      ><a name="273"
      > </a
      ><a name="274" class="Symbol"
      >(</a
      ><a name="275" href="https://agda.github.io/agda-stdlib/Function.html#713" class="Function Operator"
      >_&#8728;_</a
      ><a name="278" class="Symbol"
      >)</a
      ><a name="279"
      >
</a
      ><a name="280" class="Keyword"
      >open</a
      ><a name="284"
      > </a
      ><a name="285" class="Keyword"
      >import</a
      ><a name="291"
      > </a
      ><a name="292" href="https://agda.github.io/agda-stdlib/Data.Empty.html#1" class="Module"
      >Data.Empty</a
      ><a name="302"
      > </a
      ><a name="303" class="Keyword"
      >using</a
      ><a name="308"
      > </a
      ><a name="309" class="Symbol"
      >(</a
      ><a name="310" href="https://agda.github.io/agda-stdlib/Data.Empty.html#243" class="Datatype"
      >&#8869;</a
      ><a name="311" class="Symbol"
      >;</a
      ><a name="312"
      > </a
      ><a name="313" href="https://agda.github.io/agda-stdlib/Data.Empty.html#348" class="Function"
      >&#8869;-elim</a
      ><a name="319" class="Symbol"
      >)</a
      ><a name="320"
      >
</a
      ><a name="321" class="Keyword"
      >open</a
      ><a name="325"
      > </a
      ><a name="326" class="Keyword"
      >import</a
      ><a name="332"
      > </a
      ><a name="333" href="https://agda.github.io/agda-stdlib/Data.Maybe.html#1" class="Module"
      >Data.Maybe</a
      ><a name="343"
      > </a
      ><a name="344" class="Keyword"
      >using</a
      ><a name="349"
      > </a
      ><a name="350" class="Symbol"
      >(</a
      ><a name="351" href="https://agda.github.io/agda-stdlib/Data.Maybe.Base.html#335" class="Datatype"
      >Maybe</a
      ><a name="356" class="Symbol"
      >;</a
      ><a name="357"
      > </a
      ><a name="358" href="https://agda.github.io/agda-stdlib/Data.Maybe.html#1527" class="InductiveConstructor"
      >just</a
      ><a name="362" class="Symbol"
      >;</a
      ><a name="363"
      > </a
      ><a name="364" href="https://agda.github.io/agda-stdlib/Data.Maybe.html#1588" class="InductiveConstructor"
      >nothing</a
      ><a name="371" class="Symbol"
      >)</a
      ><a name="372"
      >
</a
      ><a name="373" class="Keyword"
      >open</a
      ><a name="377"
      > </a
      ><a name="378" class="Keyword"
      >import</a
      ><a name="384"
      > </a
      ><a name="385" href="https://agda.github.io/agda-stdlib/Data.Product.html#1" class="Module"
      >Data.Product</a
      ><a name="397"
      > </a
      ><a name="398" class="Keyword"
      >using</a
      ><a name="403"
      > </a
      ><a name="404" class="Symbol"
      >(</a
      ><a name="405" href="https://agda.github.io/agda-stdlib/Data.Product.html#1073" class="Function Operator"
      >_&#215;_</a
      ><a name="408" class="Symbol"
      >;</a
      ><a name="409"
      > </a
      ><a name="410" href="https://agda.github.io/agda-stdlib/Data.Product.html#823" class="Function"
      >&#8707;</a
      ><a name="411" class="Symbol"
      >;</a
      ><a name="412"
      > </a
      ><a name="413" href="https://agda.github.io/agda-stdlib/Data.Product.html#949" class="Function"
      >&#8707;&#8322;</a
      ><a name="415" class="Symbol"
      >;</a
      ><a name="416"
      > </a
      ><a name="417" href="https://agda.github.io/agda-stdlib/Data.Product.html#509" class="InductiveConstructor Operator"
      >_,_</a
      ><a name="420" class="Symbol"
      >;</a
      ><a name="421"
      > </a
      ><a name="422" href="https://agda.github.io/agda-stdlib/Data.Product.html#1621" class="Function Operator"
      >,_</a
      ><a name="424" class="Symbol"
      >)</a
      ><a name="425"
      >
</a
      ><a name="426" class="Keyword"
      >open</a
      ><a name="430"
      > </a
      ><a name="431" class="Keyword"
      >import</a
      ><a name="437"
      > </a
      ><a name="438" href="https://agda.github.io/agda-stdlib/Data.Sum.html#1" class="Module"
      >Data.Sum</a
      ><a name="446"
      > </a
      ><a name="447" class="Keyword"
      >using</a
      ><a name="452"
      > </a
      ><a name="453" class="Symbol"
      >(</a
      ><a name="454" href="https://agda.github.io/agda-stdlib/Data.Sum.html#433" class="Datatype Operator"
      >_&#8846;_</a
      ><a name="457" class="Symbol"
      >;</a
      ><a name="458"
      > </a
      ><a name="459" href="https://agda.github.io/agda-stdlib/Data.Sum.html#489" class="InductiveConstructor"
      >inj&#8321;</a
      ><a name="463" class="Symbol"
      >;</a
      ><a name="464"
      > </a
      ><a name="465" href="https://agda.github.io/agda-stdlib/Data.Sum.html#514" class="InductiveConstructor"
      >inj&#8322;</a
      ><a name="469" class="Symbol"
      >)</a
      ><a name="470"
      >
</a
      ><a name="471" class="Keyword"
      >open</a
      ><a name="475"
      > </a
      ><a name="476" class="Keyword"
      >import</a
      ><a name="482"
      > </a
      ><a name="483" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#1" class="Module"
      >Relation.Nullary</a
      ><a name="499"
      > </a
      ><a name="500" class="Keyword"
      >using</a
      ><a name="505"
      > </a
      ><a name="506" class="Symbol"
      >(</a
      ><a name="507" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#414" class="Function Operator"
      >&#172;_</a
      ><a name="509" class="Symbol"
      >;</a
      ><a name="510"
      > </a
      ><a name="511" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#484" class="Datatype"
      >Dec</a
      ><a name="514" class="Symbol"
      >;</a
      ><a name="515"
      > </a
      ><a name="516" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#520" class="InductiveConstructor"
      >yes</a
      ><a name="519" class="Symbol"
      >;</a
      ><a name="520"
      > </a
      ><a name="521" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#547" class="InductiveConstructor"
      >no</a
      ><a name="523" class="Symbol"
      >)</a
      ><a name="524"
      >
</a
      ><a name="525" class="Keyword"
      >open</a
      ><a name="529"
      > </a
      ><a name="530" class="Keyword"
      >import</a
      ><a name="536"
      > </a
      ><a name="537" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#1" class="Module"
      >Relation.Binary.PropositionalEquality</a
      ><a name="574"
      > </a
      ><a name="575" class="Keyword"
      >using</a
      ><a name="580"
      > </a
      ><a name="581" class="Symbol"
      >(</a
      ><a name="582" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >_&#8801;_</a
      ><a name="585" class="Symbol"
      >;</a
      ><a name="586"
      > </a
      ><a name="587" href="https://agda.github.io/agda-stdlib/Relation.Binary.Core.html#4493" class="Function Operator"
      >_&#8802;_</a
      ><a name="590" class="Symbol"
      >;</a
      ><a name="591"
      > </a
      ><a name="592" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="596" class="Symbol"
      >;</a
      ><a name="597"
      > </a
      ><a name="598" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.Core.html#632" class="Function"
      >trans</a
      ><a name="603" class="Symbol"
      >;</a
      ><a name="604"
      > </a
      ><a name="605" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.Core.html#565" class="Function"
      >sym</a
      ><a name="608" class="Symbol"
      >)</a
      ><a name="609"
      >
</a
      ><a name="610" class="Keyword"
      >open</a
      ><a name="614"
      > </a
      ><a name="615" class="Keyword"
      >import</a
      ><a name="621"
      > </a
      ><a name="622" class="Module"
      >Maps</a
      ><a name="626"
      > </a
      ><a name="627" class="Keyword"
      >using</a
      ><a name="632"
      > </a
      ><a name="633" class="Symbol"
      >(</a
      ><a name="634" href="Maps.html#2171" class="Datatype"
      >Id</a
      ><a name="636" class="Symbol"
      >;</a
      ><a name="637"
      > </a
      ><a name="638" href="Maps.html#2509" class="Function Operator"
      >_&#8799;_</a
      ><a name="641" class="Symbol"
      >;</a
      ><a name="642"
      > </a
      ><a name="643" href="Maps.html#10132" class="Function"
      >PartialMap</a
      ><a name="653" class="Symbol"
      >)</a
      ><a name="654"
      >
</a
      ><a name="655" class="Keyword"
      >open</a
      ><a name="659"
      > </a
      ><a name="660" class="Module"
      >Maps.</a
      ><a name="665" href="Maps.html#10221" class="Module"
      >PartialMap</a
      ><a name="675"
      > </a
      ><a name="676" class="Keyword"
      >using</a
      ><a name="681"
      > </a
      ><a name="682" class="Symbol"
      >(</a
      ><a name="683" href="Maps.html#10265" class="Function"
      >&#8709;</a
      ><a name="684" class="Symbol"
      >;</a
      ><a name="685"
      > </a
      ><a name="686" href="Maps.html#10573" class="Function"
      >apply-&#8709;</a
      ><a name="693" class="Symbol"
      >;</a
      ><a name="694"
      > </a
      ><a name="695" href="Maps.html#11491" class="Function"
      >update-permute</a
      ><a name="709" class="Symbol"
      >;</a
      ><a name="710"
      > </a
      ><a name="711" href="Maps.html#11818" class="Function"
      >just&#8802;nothing</a
      ><a name="723" class="Symbol"
      >;</a
      ><a name="724"
      > </a
      ><a name="725" href="Maps.html#11919" class="Function"
      >just-injective</a
      ><a name="739" class="Symbol"
      >)</a
      ><a name="740"
      >
                     </a
      ><a name="762" class="Keyword"
      >renaming</a
      ><a name="770"
      > </a
      ><a name="771" class="Symbol"
      >(</a
      ><a name="772" href="Maps.html#10368" class="Function Operator"
      >_,_&#8614;_</a
      ><a name="777"
      > </a
      ><a name="778" class="Symbol"
      >to</a
      ><a name="780"
      > </a
      ><a name="781" href="Maps.html#10368" class="Function Operator"
      >_,_&#8758;_</a
      ><a name="786" class="Symbol"
      >)</a
      ><a name="787"
      >
</a
      ><a name="788" class="Keyword"
      >open</a
      ><a name="792"
      > </a
      ><a name="793" class="Keyword"
      >import</a
      ><a name="799"
      > </a
      ><a name="800" class="Module"
      >Stlc</a
      ><a name="804"
      >
</a
      ><a name="805" class="Keyword"
      >import</a
      ><a name="811"
      > </a
      ><a name="812" href="https://agda.github.io/agda-stdlib/Data.Nat.html#1" class="Module"
      >Data.Nat</a
      ><a name="820"
      > </a
      ><a name="821" class="Keyword"
      >using</a
      ><a name="826"
      > </a
      ><a name="827" class="Symbol"
      >(</a
      ><a name="828" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#97" class="Datatype"
      >&#8469;</a
      ><a name="829" class="Symbol"
      >)</a
      >

</pre>


## Canonical Forms

<!--
As we saw for the simple calculus in Chapter [Types]({{ "Types" | relative_url }}),
-->

The first step in establishing basic properties of reduction and typing
is to identify the possible _canonical forms_ (i.e., well-typed closed values)
belonging to each type.  For function types the canonical forms are lambda-abstractions,
while for boolean types they are values `true` and `false`.  

<pre class="Agda">

<a name="1274" class="Keyword"
      >data</a
      ><a name="1278"
      > </a
      ><a name="1279" href="StlcProp.html#1279" class="Datatype Operator"
      >canonical_for_</a
      ><a name="1293"
      > </a
      ><a name="1294" class="Symbol"
      >:</a
      ><a name="1295"
      > </a
      ><a name="1296" href="Stlc.html#3637" class="Datatype"
      >Term</a
      ><a name="1300"
      > </a
      ><a name="1301" class="Symbol"
      >&#8594;</a
      ><a name="1302"
      > </a
      ><a name="1303" href="Stlc.html#2564" class="Datatype"
      >Type</a
      ><a name="1307"
      > </a
      ><a name="1308" class="Symbol"
      >&#8594;</a
      ><a name="1309"
      > </a
      ><a name="1310" class="PrimitiveType"
      >Set</a
      ><a name="1313"
      > </a
      ><a name="1314" class="Keyword"
      >where</a
      ><a name="1319"
      >
  </a
      ><a name="1322" href="StlcProp.html#1322" class="InductiveConstructor"
      >canonical-&#955;</a
      ><a name="1333"
      > </a
      ><a name="1334" class="Symbol"
      >:</a
      ><a name="1335"
      > </a
      ><a name="1336" class="Symbol"
      >&#8704;</a
      ><a name="1337"
      > </a
      ><a name="1338" class="Symbol"
      >{</a
      ><a name="1339" href="StlcProp.html#1339" class="Bound"
      >x</a
      ><a name="1340"
      > </a
      ><a name="1341" href="StlcProp.html#1341" class="Bound"
      >A</a
      ><a name="1342"
      > </a
      ><a name="1343" href="StlcProp.html#1343" class="Bound"
      >N</a
      ><a name="1344"
      > </a
      ><a name="1345" href="StlcProp.html#1345" class="Bound"
      >B</a
      ><a name="1346" class="Symbol"
      >}</a
      ><a name="1347"
      > </a
      ><a name="1348" class="Symbol"
      >&#8594;</a
      ><a name="1349"
      > </a
      ><a name="1350" href="StlcProp.html#1279" class="Datatype Operator"
      >canonical</a
      ><a name="1359"
      > </a
      ><a name="1360" class="Symbol"
      >(</a
      ><a name="1361" href="Stlc.html#3672" class="InductiveConstructor Operator"
      >&#955;[</a
      ><a name="1363"
      > </a
      ><a name="1364" href="StlcProp.html#1339" class="Bound"
      >x</a
      ><a name="1365"
      > </a
      ><a name="1366" href="Stlc.html#3672" class="InductiveConstructor Operator"
      >&#8758;</a
      ><a name="1367"
      > </a
      ><a name="1368" href="StlcProp.html#1341" class="Bound"
      >A</a
      ><a name="1369"
      > </a
      ><a name="1370" href="Stlc.html#3672" class="InductiveConstructor Operator"
      >]</a
      ><a name="1371"
      > </a
      ><a name="1372" href="StlcProp.html#1343" class="Bound"
      >N</a
      ><a name="1373" class="Symbol"
      >)</a
      ><a name="1374"
      > </a
      ><a name="1375" href="StlcProp.html#1279" class="Datatype Operator"
      >for</a
      ><a name="1378"
      > </a
      ><a name="1379" class="Symbol"
      >(</a
      ><a name="1380" href="StlcProp.html#1341" class="Bound"
      >A</a
      ><a name="1381"
      > </a
      ><a name="1382" href="Stlc.html#2583" class="InductiveConstructor Operator"
      >&#8658;</a
      ><a name="1383"
      > </a
      ><a name="1384" href="StlcProp.html#1345" class="Bound"
      >B</a
      ><a name="1385" class="Symbol"
      >)</a
      ><a name="1386"
      >
  </a
      ><a name="1389" href="StlcProp.html#1389" class="InductiveConstructor"
      >canonical-true</a
      ><a name="1403"
      > </a
      ><a name="1404" class="Symbol"
      >:</a
      ><a name="1405"
      > </a
      ><a name="1406" href="StlcProp.html#1279" class="Datatype Operator"
      >canonical</a
      ><a name="1415"
      > </a
      ><a name="1416" href="Stlc.html#3735" class="InductiveConstructor"
      >true</a
      ><a name="1420"
      > </a
      ><a name="1421" href="StlcProp.html#1279" class="Datatype Operator"
      >for</a
      ><a name="1424"
      > </a
      ><a name="1425" href="Stlc.html#2610" class="InductiveConstructor"
      >&#120121;</a
      ><a name="1426"
      >
  </a
      ><a name="1429" href="StlcProp.html#1429" class="InductiveConstructor"
      >canonical-false</a
      ><a name="1444"
      > </a
      ><a name="1445" class="Symbol"
      >:</a
      ><a name="1446"
      > </a
      ><a name="1447" href="StlcProp.html#1279" class="Datatype Operator"
      >canonical</a
      ><a name="1456"
      > </a
      ><a name="1457" href="Stlc.html#3749" class="InductiveConstructor"
      >false</a
      ><a name="1462"
      > </a
      ><a name="1463" href="StlcProp.html#1279" class="Datatype Operator"
      >for</a
      ><a name="1466"
      > </a
      ><a name="1467" href="Stlc.html#2610" class="InductiveConstructor"
      >&#120121;</a
      ><a name="1468"
      >

</a
      ><a name="1470" href="StlcProp.html#1470" class="Function"
      >canonical-forms</a
      ><a name="1485"
      > </a
      ><a name="1486" class="Symbol"
      >:</a
      ><a name="1487"
      > </a
      ><a name="1488" class="Symbol"
      >&#8704;</a
      ><a name="1489"
      > </a
      ><a name="1490" class="Symbol"
      >{</a
      ><a name="1491" href="StlcProp.html#1491" class="Bound"
      >L</a
      ><a name="1492"
      > </a
      ><a name="1493" href="StlcProp.html#1493" class="Bound"
      >A</a
      ><a name="1494" class="Symbol"
      >}</a
      ><a name="1495"
      > </a
      ><a name="1496" class="Symbol"
      >&#8594;</a
      ><a name="1497"
      > </a
      ><a name="1498" href="Maps.html#10265" class="Function"
      >&#8709;</a
      ><a name="1499"
      > </a
      ><a name="1500" href="Stlc.html#21569" class="Datatype Operator"
      >&#8866;</a
      ><a name="1501"
      > </a
      ><a name="1502" href="StlcProp.html#1491" class="Bound"
      >L</a
      ><a name="1503"
      > </a
      ><a name="1504" href="Stlc.html#21569" class="Datatype Operator"
      >&#8758;</a
      ><a name="1505"
      > </a
      ><a name="1506" href="StlcProp.html#1493" class="Bound"
      >A</a
      ><a name="1507"
      > </a
      ><a name="1508" class="Symbol"
      >&#8594;</a
      ><a name="1509"
      > </a
      ><a name="1510" href="Stlc.html#9535" class="Datatype"
      >Value</a
      ><a name="1515"
      > </a
      ><a name="1516" href="StlcProp.html#1491" class="Bound"
      >L</a
      ><a name="1517"
      > </a
      ><a name="1518" class="Symbol"
      >&#8594;</a
      ><a name="1519"
      > </a
      ><a name="1520" href="StlcProp.html#1279" class="Datatype Operator"
      >canonical</a
      ><a name="1529"
      > </a
      ><a name="1530" href="StlcProp.html#1491" class="Bound"
      >L</a
      ><a name="1531"
      > </a
      ><a name="1532" href="StlcProp.html#1279" class="Datatype Operator"
      >for</a
      ><a name="1535"
      > </a
      ><a name="1536" href="StlcProp.html#1493" class="Bound"
      >A</a
      ><a name="1537"
      >
</a
      ><a name="1538" href="StlcProp.html#1470" class="Function"
      >canonical-forms</a
      ><a name="1553"
      > </a
      ><a name="1554" class="Symbol"
      >(</a
      ><a name="1555" href="Stlc.html#21613" class="InductiveConstructor"
      >Ax</a
      ><a name="1557"
      > </a
      ><a name="1558" class="Symbol"
      >())</a
      ><a name="1561"
      > </a
      ><a name="1562" class="Symbol"
      >()</a
      ><a name="1564"
      >
</a
      ><a name="1565" href="StlcProp.html#1470" class="Function"
      >canonical-forms</a
      ><a name="1580"
      > </a
      ><a name="1581" class="Symbol"
      >(</a
      ><a name="1582" href="Stlc.html#21667" class="InductiveConstructor"
      >&#8658;-I</a
      ><a name="1585"
      > </a
      ><a name="1586" href="StlcProp.html#1586" class="Bound"
      >&#8866;N</a
      ><a name="1588" class="Symbol"
      >)</a
      ><a name="1589"
      > </a
      ><a name="1590" href="Stlc.html#9562" class="InductiveConstructor"
      >value-&#955;</a
      ><a name="1597"
      > </a
      ><a name="1598" class="Symbol"
      >=</a
      ><a name="1599"
      > </a
      ><a name="1600" href="StlcProp.html#1322" class="InductiveConstructor"
      >canonical-&#955;</a
      ><a name="1611"
      >
</a
      ><a name="1612" href="StlcProp.html#1470" class="Function"
      >canonical-forms</a
      ><a name="1627"
      > </a
      ><a name="1628" class="Symbol"
      >(</a
      ><a name="1629" href="Stlc.html#21744" class="InductiveConstructor"
      >&#8658;-E</a
      ><a name="1632"
      > </a
      ><a name="1633" href="StlcProp.html#1633" class="Bound"
      >&#8866;L</a
      ><a name="1635"
      > </a
      ><a name="1636" href="StlcProp.html#1636" class="Bound"
      >&#8866;M</a
      ><a name="1638" class="Symbol"
      >)</a
      ><a name="1639"
      > </a
      ><a name="1640" class="Symbol"
      >()</a
      ><a name="1642"
      >
</a
      ><a name="1643" href="StlcProp.html#1470" class="Function"
      >canonical-forms</a
      ><a name="1658"
      > </a
      ><a name="1659" href="Stlc.html#21822" class="InductiveConstructor"
      >&#120121;-I&#8321;</a
      ><a name="1663"
      > </a
      ><a name="1664" href="Stlc.html#9611" class="InductiveConstructor"
      >value-true</a
      ><a name="1674"
      > </a
      ><a name="1675" class="Symbol"
      >=</a
      ><a name="1676"
      > </a
      ><a name="1677" href="StlcProp.html#1389" class="InductiveConstructor"
      >canonical-true</a
      ><a name="1691"
      >
</a
      ><a name="1692" href="StlcProp.html#1470" class="Function"
      >canonical-forms</a
      ><a name="1707"
      > </a
      ><a name="1708" href="Stlc.html#21856" class="InductiveConstructor"
      >&#120121;-I&#8322;</a
      ><a name="1712"
      > </a
      ><a name="1713" href="Stlc.html#9638" class="InductiveConstructor"
      >value-false</a
      ><a name="1724"
      > </a
      ><a name="1725" class="Symbol"
      >=</a
      ><a name="1726"
      > </a
      ><a name="1727" href="StlcProp.html#1429" class="InductiveConstructor"
      >canonical-false</a
      ><a name="1742"
      >
</a
      ><a name="1743" href="StlcProp.html#1470" class="Function"
      >canonical-forms</a
      ><a name="1758"
      > </a
      ><a name="1759" class="Symbol"
      >(</a
      ><a name="1760" href="Stlc.html#21891" class="InductiveConstructor"
      >&#120121;-E</a
      ><a name="1763"
      > </a
      ><a name="1764" href="StlcProp.html#1764" class="Bound"
      >&#8866;L</a
      ><a name="1766"
      > </a
      ><a name="1767" href="StlcProp.html#1767" class="Bound"
      >&#8866;M</a
      ><a name="1769"
      > </a
      ><a name="1770" href="StlcProp.html#1770" class="Bound"
      >&#8866;N</a
      ><a name="1772" class="Symbol"
      >)</a
      ><a name="1773"
      > </a
      ><a name="1774" class="Symbol"
      >()</a
      >

</pre>

## Progress

As before, the _progress_ theorem tells us that closed, well-typed
terms are not stuck: either a well-typed term can take a reduction
step or it is a value.

<pre class="Agda">

<a name="1973" class="Keyword"
      >data</a
      ><a name="1977"
      > </a
      ><a name="1978" href="StlcProp.html#1978" class="Datatype"
      >Progress</a
      ><a name="1986"
      > </a
      ><a name="1987" class="Symbol"
      >:</a
      ><a name="1988"
      > </a
      ><a name="1989" href="Stlc.html#3637" class="Datatype"
      >Term</a
      ><a name="1993"
      > </a
      ><a name="1994" class="Symbol"
      >&#8594;</a
      ><a name="1995"
      > </a
      ><a name="1996" class="PrimitiveType"
      >Set</a
      ><a name="1999"
      > </a
      ><a name="2000" class="Keyword"
      >where</a
      ><a name="2005"
      >
  </a
      ><a name="2008" href="StlcProp.html#2008" class="InductiveConstructor"
      >steps</a
      ><a name="2013"
      > </a
      ><a name="2014" class="Symbol"
      >:</a
      ><a name="2015"
      > </a
      ><a name="2016" class="Symbol"
      >&#8704;</a
      ><a name="2017"
      > </a
      ><a name="2018" class="Symbol"
      >{</a
      ><a name="2019" href="StlcProp.html#2019" class="Bound"
      >M</a
      ><a name="2020"
      > </a
      ><a name="2021" href="StlcProp.html#2021" class="Bound"
      >N</a
      ><a name="2022" class="Symbol"
      >}</a
      ><a name="2023"
      > </a
      ><a name="2024" class="Symbol"
      >&#8594;</a
      ><a name="2025"
      > </a
      ><a name="2026" href="StlcProp.html#2019" class="Bound"
      >M</a
      ><a name="2027"
      > </a
      ><a name="2028" href="Stlc.html#15832" class="Datatype Operator"
      >&#10233;</a
      ><a name="2029"
      > </a
      ><a name="2030" href="StlcProp.html#2021" class="Bound"
      >N</a
      ><a name="2031"
      > </a
      ><a name="2032" class="Symbol"
      >&#8594;</a
      ><a name="2033"
      > </a
      ><a name="2034" href="StlcProp.html#1978" class="Datatype"
      >Progress</a
      ><a name="2042"
      > </a
      ><a name="2043" href="StlcProp.html#2019" class="Bound"
      >M</a
      ><a name="2044"
      >
  </a
      ><a name="2047" href="StlcProp.html#2047" class="InductiveConstructor"
      >done</a
      ><a name="2051"
      >  </a
      ><a name="2053" class="Symbol"
      >:</a
      ><a name="2054"
      > </a
      ><a name="2055" class="Symbol"
      >&#8704;</a
      ><a name="2056"
      > </a
      ><a name="2057" class="Symbol"
      >{</a
      ><a name="2058" href="StlcProp.html#2058" class="Bound"
      >M</a
      ><a name="2059" class="Symbol"
      >}</a
      ><a name="2060"
      > </a
      ><a name="2061" class="Symbol"
      >&#8594;</a
      ><a name="2062"
      > </a
      ><a name="2063" href="Stlc.html#9535" class="Datatype"
      >Value</a
      ><a name="2068"
      > </a
      ><a name="2069" href="StlcProp.html#2058" class="Bound"
      >M</a
      ><a name="2070"
      > </a
      ><a name="2071" class="Symbol"
      >&#8594;</a
      ><a name="2072"
      > </a
      ><a name="2073" href="StlcProp.html#1978" class="Datatype"
      >Progress</a
      ><a name="2081"
      > </a
      ><a name="2082" href="StlcProp.html#2058" class="Bound"
      >M</a
      ><a name="2083"
      >

</a
      ><a name="2085" href="StlcProp.html#2085" class="Function"
      >progress</a
      ><a name="2093"
      > </a
      ><a name="2094" class="Symbol"
      >:</a
      ><a name="2095"
      > </a
      ><a name="2096" class="Symbol"
      >&#8704;</a
      ><a name="2097"
      > </a
      ><a name="2098" class="Symbol"
      >{</a
      ><a name="2099" href="StlcProp.html#2099" class="Bound"
      >M</a
      ><a name="2100"
      > </a
      ><a name="2101" href="StlcProp.html#2101" class="Bound"
      >A</a
      ><a name="2102" class="Symbol"
      >}</a
      ><a name="2103"
      > </a
      ><a name="2104" class="Symbol"
      >&#8594;</a
      ><a name="2105"
      > </a
      ><a name="2106" href="Maps.html#10265" class="Function"
      >&#8709;</a
      ><a name="2107"
      > </a
      ><a name="2108" href="Stlc.html#21569" class="Datatype Operator"
      >&#8866;</a
      ><a name="2109"
      > </a
      ><a name="2110" href="StlcProp.html#2099" class="Bound"
      >M</a
      ><a name="2111"
      > </a
      ><a name="2112" href="Stlc.html#21569" class="Datatype Operator"
      >&#8758;</a
      ><a name="2113"
      > </a
      ><a name="2114" href="StlcProp.html#2101" class="Bound"
      >A</a
      ><a name="2115"
      > </a
      ><a name="2116" class="Symbol"
      >&#8594;</a
      ><a name="2117"
      > </a
      ><a name="2118" href="StlcProp.html#1978" class="Datatype"
      >Progress</a
      ><a name="2126"
      > </a
      ><a name="2127" href="StlcProp.html#2099" class="Bound"
      >M</a
      >

</pre>

<!--
The proof is a relatively straightforward extension of the progress proof we saw in
[Types]({{ "Types" | relative_url }}).
-->

We give the proof in English first, then the formal version.

_Proof_: By induction on the derivation of `∅ ⊢ M ∶ A`.

  - The last rule of the derivation cannot be `Ax`,
    since a variable is never well typed in an empty context.

  - If the last rule of the derivation is `⇒-I`, `𝔹-I₁`, or `𝔹-I₂`
    then, trivially, the term is a value.

  - If the last rule of the derivation is `⇒-E`, then the term has the
    form `L · M` for some `L` and `M`, where we know that `L` and `M`
    are also well typed in the empty context, giving us two induction
    hypotheses.  By the first induction hypothesis, either `L`
    can take a step or is a value.

    - If `L` can take a step, then so can `L · M` by `ξ·₁`.

    - If `L` is a value then consider `M`. By the second induction
      hypothesis, either `M` can take a step or is a value.

      - If `M` can take a step, then so can `L · M` by `ξ·₂`.

      - If `M` is a value, then since `L` is a value with a
        function type we know from the canonical forms lemma
        that it must be a lambda abstraction,
        and hence `L · M` can take a step by `βλ·`.

  - If the last rule of the derivation is `𝔹-E`, then the term has
    the form `if L then M else N` where `L` has type `𝔹`.
    By the induction hypothesis, either `L` can take a step or is
    a value.

    - If `L` can take a step, then so can `if L then M else N` by `ξif`.

    - If `L` is a value, then since it has type boolean we know from
      the canonical forms lemma that it must be either `true` or
      `false`.

      - If `L` is `true`, then `if L then M else N` steps by `βif-true`

      - If `L` is `false`, then `if L then M else N` steps by `βif-false`

This completes the proof.

<pre class="Agda">

<a name="4017" href="StlcProp.html#2085" class="Function"
      >progress</a
      ><a name="4025"
      > </a
      ><a name="4026" class="Symbol"
      >(</a
      ><a name="4027" href="Stlc.html#21613" class="InductiveConstructor"
      >Ax</a
      ><a name="4029"
      > </a
      ><a name="4030" class="Symbol"
      >())</a
      ><a name="4033"
      >
</a
      ><a name="4034" href="StlcProp.html#2085" class="Function"
      >progress</a
      ><a name="4042"
      > </a
      ><a name="4043" class="Symbol"
      >(</a
      ><a name="4044" href="Stlc.html#21667" class="InductiveConstructor"
      >&#8658;-I</a
      ><a name="4047"
      > </a
      ><a name="4048" href="StlcProp.html#4048" class="Bound"
      >&#8866;N</a
      ><a name="4050" class="Symbol"
      >)</a
      ><a name="4051"
      > </a
      ><a name="4052" class="Symbol"
      >=</a
      ><a name="4053"
      > </a
      ><a name="4054" href="StlcProp.html#2047" class="InductiveConstructor"
      >done</a
      ><a name="4058"
      > </a
      ><a name="4059" href="Stlc.html#9562" class="InductiveConstructor"
      >value-&#955;</a
      ><a name="4066"
      >
</a
      ><a name="4067" href="StlcProp.html#2085" class="Function"
      >progress</a
      ><a name="4075"
      > </a
      ><a name="4076" class="Symbol"
      >(</a
      ><a name="4077" href="Stlc.html#21744" class="InductiveConstructor"
      >&#8658;-E</a
      ><a name="4080"
      > </a
      ><a name="4081" href="StlcProp.html#4081" class="Bound"
      >&#8866;L</a
      ><a name="4083"
      > </a
      ><a name="4084" href="StlcProp.html#4084" class="Bound"
      >&#8866;M</a
      ><a name="4086" class="Symbol"
      >)</a
      ><a name="4087"
      > </a
      ><a name="4088" class="Keyword"
      >with</a
      ><a name="4092"
      > </a
      ><a name="4093" href="StlcProp.html#2085" class="Function"
      >progress</a
      ><a name="4101"
      > </a
      ><a name="4102" href="StlcProp.html#4081" class="Bound"
      >&#8866;L</a
      ><a name="4104"
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
      ><a name="4111" href="StlcProp.html#2008" class="InductiveConstructor"
      >steps</a
      ><a name="4116"
      > </a
      ><a name="4117" href="StlcProp.html#4117" class="Bound"
      >L&#10233;L&#8242;</a
      ><a name="4121"
      > </a
      ><a name="4122" class="Symbol"
      >=</a
      ><a name="4123"
      > </a
      ><a name="4124" href="StlcProp.html#2008" class="InductiveConstructor"
      >steps</a
      ><a name="4129"
      > </a
      ><a name="4130" class="Symbol"
      >(</a
      ><a name="4131" href="Stlc.html#15864" class="InductiveConstructor"
      >&#958;&#183;&#8321;</a
      ><a name="4134"
      > </a
      ><a name="4135" href="StlcProp.html#4117" class="Bound"
      >L&#10233;L&#8242;</a
      ><a name="4139" class="Symbol"
      >)</a
      ><a name="4140"
      >
</a
      ><a name="4141" class="Symbol"
      >...</a
      ><a name="4144"
      > </a
      ><a name="4145" class="Symbol"
      >|</a
      ><a name="4146"
      > </a
      ><a name="4147" href="StlcProp.html#2047" class="InductiveConstructor"
      >done</a
      ><a name="4151"
      > </a
      ><a name="4152" href="StlcProp.html#4152" class="Bound"
      >valueL</a
      ><a name="4158"
      > </a
      ><a name="4159" class="Keyword"
      >with</a
      ><a name="4163"
      > </a
      ><a name="4164" href="StlcProp.html#2085" class="Function"
      >progress</a
      ><a name="4172"
      > </a
      ><a name="4173" href="StlcProp.html#4084" class="Bound"
      >&#8866;M</a
      ><a name="4175"
      >
</a
      ><a name="4176" class="Symbol"
      >...</a
      ><a name="4179"
      > </a
      ><a name="4180" class="Symbol"
      >|</a
      ><a name="4181"
      > </a
      ><a name="4182" href="StlcProp.html#2008" class="InductiveConstructor"
      >steps</a
      ><a name="4187"
      > </a
      ><a name="4188" href="StlcProp.html#4188" class="Bound"
      >M&#10233;M&#8242;</a
      ><a name="4192"
      > </a
      ><a name="4193" class="Symbol"
      >=</a
      ><a name="4194"
      > </a
      ><a name="4195" href="StlcProp.html#2008" class="InductiveConstructor"
      >steps</a
      ><a name="4200"
      > </a
      ><a name="4201" class="Symbol"
      >(</a
      ><a name="4202" href="Stlc.html#15917" class="InductiveConstructor"
      >&#958;&#183;&#8322;</a
      ><a name="4205"
      > </a
      ><a name="4206" href="StlcProp.html#4152" class="Bound"
      >valueL</a
      ><a name="4212"
      > </a
      ><a name="4213" href="StlcProp.html#4188" class="Bound"
      >M&#10233;M&#8242;</a
      ><a name="4217" class="Symbol"
      >)</a
      ><a name="4218"
      >
</a
      ><a name="4219" class="Symbol"
      >...</a
      ><a name="4222"
      > </a
      ><a name="4223" class="Symbol"
      >|</a
      ><a name="4224"
      > </a
      ><a name="4225" href="StlcProp.html#2047" class="InductiveConstructor"
      >done</a
      ><a name="4229"
      > </a
      ><a name="4230" href="StlcProp.html#4230" class="Bound"
      >valueM</a
      ><a name="4236"
      > </a
      ><a name="4237" class="Keyword"
      >with</a
      ><a name="4241"
      > </a
      ><a name="4242" href="StlcProp.html#1470" class="Function"
      >canonical-forms</a
      ><a name="4257"
      > </a
      ><a name="4258" href="StlcProp.html#4081" class="Bound"
      >&#8866;L</a
      ><a name="4260"
      > </a
      ><a name="4261" href="StlcProp.html#4152" class="Bound"
      >valueL</a
      ><a name="4267"
      >
</a
      ><a name="4268" class="Symbol"
      >...</a
      ><a name="4271"
      > </a
      ><a name="4272" class="Symbol"
      >|</a
      ><a name="4273"
      > </a
      ><a name="4274" href="StlcProp.html#1322" class="InductiveConstructor"
      >canonical-&#955;</a
      ><a name="4285"
      > </a
      ><a name="4286" class="Symbol"
      >=</a
      ><a name="4287"
      > </a
      ><a name="4288" href="StlcProp.html#2008" class="InductiveConstructor"
      >steps</a
      ><a name="4293"
      > </a
      ><a name="4294" class="Symbol"
      >(</a
      ><a name="4295" href="Stlc.html#15984" class="InductiveConstructor"
      >&#946;&#955;&#183;</a
      ><a name="4298"
      > </a
      ><a name="4299" href="StlcProp.html#4230" class="Bound"
      >valueM</a
      ><a name="4305" class="Symbol"
      >)</a
      ><a name="4306"
      >
</a
      ><a name="4307" href="StlcProp.html#2085" class="Function"
      >progress</a
      ><a name="4315"
      > </a
      ><a name="4316" href="Stlc.html#21822" class="InductiveConstructor"
      >&#120121;-I&#8321;</a
      ><a name="4320"
      > </a
      ><a name="4321" class="Symbol"
      >=</a
      ><a name="4322"
      > </a
      ><a name="4323" href="StlcProp.html#2047" class="InductiveConstructor"
      >done</a
      ><a name="4327"
      > </a
      ><a name="4328" href="Stlc.html#9611" class="InductiveConstructor"
      >value-true</a
      ><a name="4338"
      >
</a
      ><a name="4339" href="StlcProp.html#2085" class="Function"
      >progress</a
      ><a name="4347"
      > </a
      ><a name="4348" href="Stlc.html#21856" class="InductiveConstructor"
      >&#120121;-I&#8322;</a
      ><a name="4352"
      > </a
      ><a name="4353" class="Symbol"
      >=</a
      ><a name="4354"
      > </a
      ><a name="4355" href="StlcProp.html#2047" class="InductiveConstructor"
      >done</a
      ><a name="4359"
      > </a
      ><a name="4360" href="Stlc.html#9638" class="InductiveConstructor"
      >value-false</a
      ><a name="4371"
      >
</a
      ><a name="4372" href="StlcProp.html#2085" class="Function"
      >progress</a
      ><a name="4380"
      > </a
      ><a name="4381" class="Symbol"
      >(</a
      ><a name="4382" href="Stlc.html#21891" class="InductiveConstructor"
      >&#120121;-E</a
      ><a name="4385"
      > </a
      ><a name="4386" href="StlcProp.html#4386" class="Bound"
      >&#8866;L</a
      ><a name="4388"
      > </a
      ><a name="4389" href="StlcProp.html#4389" class="Bound"
      >&#8866;M</a
      ><a name="4391"
      > </a
      ><a name="4392" href="StlcProp.html#4392" class="Bound"
      >&#8866;N</a
      ><a name="4394" class="Symbol"
      >)</a
      ><a name="4395"
      > </a
      ><a name="4396" class="Keyword"
      >with</a
      ><a name="4400"
      > </a
      ><a name="4401" href="StlcProp.html#2085" class="Function"
      >progress</a
      ><a name="4409"
      > </a
      ><a name="4410" href="StlcProp.html#4386" class="Bound"
      >&#8866;L</a
      ><a name="4412"
      >
</a
      ><a name="4413" class="Symbol"
      >...</a
      ><a name="4416"
      > </a
      ><a name="4417" class="Symbol"
      >|</a
      ><a name="4418"
      > </a
      ><a name="4419" href="StlcProp.html#2008" class="InductiveConstructor"
      >steps</a
      ><a name="4424"
      > </a
      ><a name="4425" href="StlcProp.html#4425" class="Bound"
      >L&#10233;L&#8242;</a
      ><a name="4429"
      > </a
      ><a name="4430" class="Symbol"
      >=</a
      ><a name="4431"
      > </a
      ><a name="4432" href="StlcProp.html#2008" class="InductiveConstructor"
      >steps</a
      ><a name="4437"
      > </a
      ><a name="4438" class="Symbol"
      >(</a
      ><a name="4439" href="Stlc.html#16054" class="InductiveConstructor"
      >&#958;if</a
      ><a name="4442"
      > </a
      ><a name="4443" href="StlcProp.html#4425" class="Bound"
      >L&#10233;L&#8242;</a
      ><a name="4447" class="Symbol"
      >)</a
      ><a name="4448"
      >
</a
      ><a name="4449" class="Symbol"
      >...</a
      ><a name="4452"
      > </a
      ><a name="4453" class="Symbol"
      >|</a
      ><a name="4454"
      > </a
      ><a name="4455" href="StlcProp.html#2047" class="InductiveConstructor"
      >done</a
      ><a name="4459"
      > </a
      ><a name="4460" href="StlcProp.html#4460" class="Bound"
      >valueL</a
      ><a name="4466"
      > </a
      ><a name="4467" class="Keyword"
      >with</a
      ><a name="4471"
      > </a
      ><a name="4472" href="StlcProp.html#1470" class="Function"
      >canonical-forms</a
      ><a name="4487"
      > </a
      ><a name="4488" href="StlcProp.html#4386" class="Bound"
      >&#8866;L</a
      ><a name="4490"
      > </a
      ><a name="4491" href="StlcProp.html#4460" class="Bound"
      >valueL</a
      ><a name="4497"
      >
</a
      ><a name="4498" class="Symbol"
      >...</a
      ><a name="4501"
      > </a
      ><a name="4502" class="Symbol"
      >|</a
      ><a name="4503"
      > </a
      ><a name="4504" href="StlcProp.html#1389" class="InductiveConstructor"
      >canonical-true</a
      ><a name="4518"
      > </a
      ><a name="4519" class="Symbol"
      >=</a
      ><a name="4520"
      > </a
      ><a name="4521" href="StlcProp.html#2008" class="InductiveConstructor"
      >steps</a
      ><a name="4526"
      > </a
      ><a name="4527" href="Stlc.html#16139" class="InductiveConstructor"
      >&#946;if-true</a
      ><a name="4535"
      >
</a
      ><a name="4536" class="Symbol"
      >...</a
      ><a name="4539"
      > </a
      ><a name="4540" class="Symbol"
      >|</a
      ><a name="4541"
      > </a
      ><a name="4542" href="StlcProp.html#1429" class="InductiveConstructor"
      >canonical-false</a
      ><a name="4557"
      > </a
      ><a name="4558" class="Symbol"
      >=</a
      ><a name="4559"
      > </a
      ><a name="4560" href="StlcProp.html#2008" class="InductiveConstructor"
      >steps</a
      ><a name="4565"
      > </a
      ><a name="4566" href="Stlc.html#16192" class="InductiveConstructor"
      >&#946;if-false</a
      >

</pre>

This code reads neatly in part because we consider the
`steps` option before the `done` option. We could, of course,
do it the other way around, but then the `...` abbreviation
no longer works, and we will need to write out all the arguments
in full. In general, the rule of thumb is to consider the easy case
(here `steps`) before the hard case (here `done`).
If you have two hard cases, you will have to expand out `...`
or introduce subsidiary functions.

#### Exercise: 3 stars, optional (progress_from_term_ind)
Show that progress can also be proved by induction on terms
instead of induction on typing derivations.

<pre class="Agda">

<a name="5223" class="Keyword"
      >postulate</a
      ><a name="5232"
      >
  </a
      ><a name="5235" href="StlcProp.html#5235" class="Postulate"
      >progress&#8242;</a
      ><a name="5244"
      > </a
      ><a name="5245" class="Symbol"
      >:</a
      ><a name="5246"
      > </a
      ><a name="5247" class="Symbol"
      >&#8704;</a
      ><a name="5248"
      > </a
      ><a name="5249" href="StlcProp.html#5249" class="Bound"
      >M</a
      ><a name="5250"
      > </a
      ><a name="5251" class="Symbol"
      >{</a
      ><a name="5252" href="StlcProp.html#5252" class="Bound"
      >A</a
      ><a name="5253" class="Symbol"
      >}</a
      ><a name="5254"
      > </a
      ><a name="5255" class="Symbol"
      >&#8594;</a
      ><a name="5256"
      > </a
      ><a name="5257" href="Maps.html#10265" class="Function"
      >&#8709;</a
      ><a name="5258"
      > </a
      ><a name="5259" href="Stlc.html#21569" class="Datatype Operator"
      >&#8866;</a
      ><a name="5260"
      > </a
      ><a name="5261" href="StlcProp.html#5249" class="Bound"
      >M</a
      ><a name="5262"
      > </a
      ><a name="5263" href="Stlc.html#21569" class="Datatype Operator"
      >&#8758;</a
      ><a name="5264"
      > </a
      ><a name="5265" href="StlcProp.html#5252" class="Bound"
      >A</a
      ><a name="5266"
      > </a
      ><a name="5267" class="Symbol"
      >&#8594;</a
      ><a name="5268"
      > </a
      ><a name="5269" href="StlcProp.html#1978" class="Datatype"
      >Progress</a
      ><a name="5277"
      > </a
      ><a name="5278" href="StlcProp.html#5249" class="Bound"
      >M</a
      >

</pre>

## Preservation

The other half of the type soundness property is the preservation
of types during reduction.  For this, we need to develop
technical machinery for reasoning about variables and
substitution.  Working from top to bottom (from the high-level
property we are actually interested in to the lowest-level
technical lemmas), the story goes like this:

  <!--
  - The _preservation theorem_ is proved by induction on a typing derivation.
    derivation, pretty much as we did in chapter [Types]({{ "Types" | relative_url }})
  -->

  - The one case that is significantly different is the one for the
    `βλ·` rule, whose definition uses the substitution operation.  To see that
    this step preserves typing, we need to know that the substitution itself
    does.  So we prove a ... 

  - _substitution lemma_, stating that substituting a (closed) term
    `V` for a variable `x` in a term `N` preserves the type of `N`.
    The proof goes by induction on the form of `N` and requires
    looking at all the different cases in the definition of
    substitition. The lemma does not require that `V` be a value,
    though in practice we only substitute values.  The tricky cases
    are the ones for variables and for function abstractions.  In both
    cases, we discover that we need to take a term `V` that has been
    shown to be well-typed in some context `Γ` and consider the same
    term in a different context `Γ′`.  For this we prove a ...

  - _context invariance_ lemma, showing that typing is preserved
    under "inessential changes" to the context---a term `M`
    well typed in `Γ` is also well typed in `Γ′`, so long as
    all the free variables of `M` appear in both contexts.
    And finally, for this, we need a careful definition of ...

  - _free variables_ of a term---i.e., those variables
    mentioned in a term and not bound in an enclosing
    lambda abstraction.

To make Agda happy, we need to formalize the story in the opposite
order.


### Free Occurrences

A variable `x` appears _free_ in a term `M` if `M` contains an
occurrence of `x` that is not bound in an enclosing lambda abstraction.
For example:

  - `x` appears free, but `f` does not, in `λ[ f ∶ (𝔹 ⇒ 𝔹) ] ` f · ` x`
  - both `f` and `x` appear free in `(λ[ f ∶ (𝔹 ⇒ 𝔹) ] ` f · ` x) · ` f`;
    indeed, `f` appears both bound and free in this term
  - no variables appear free in `λ[ f ∶ (𝔹 ⇒ 𝔹) ] λ[ x ∶ 𝔹 ] ` f · ` x`

Formally:

<pre class="Agda">

<a name="7745" class="Keyword"
      >data</a
      ><a name="7749"
      > </a
      ><a name="7750" href="StlcProp.html#7750" class="Datatype Operator"
      >_&#8712;_</a
      ><a name="7753"
      > </a
      ><a name="7754" class="Symbol"
      >:</a
      ><a name="7755"
      > </a
      ><a name="7756" href="Maps.html#2171" class="Datatype"
      >Id</a
      ><a name="7758"
      > </a
      ><a name="7759" class="Symbol"
      >&#8594;</a
      ><a name="7760"
      > </a
      ><a name="7761" href="Stlc.html#3637" class="Datatype"
      >Term</a
      ><a name="7765"
      > </a
      ><a name="7766" class="Symbol"
      >&#8594;</a
      ><a name="7767"
      > </a
      ><a name="7768" class="PrimitiveType"
      >Set</a
      ><a name="7771"
      > </a
      ><a name="7772" class="Keyword"
      >where</a
      ><a name="7777"
      >
  </a
      ><a name="7780" href="StlcProp.html#7780" class="InductiveConstructor"
      >free-`</a
      ><a name="7786"
      >  </a
      ><a name="7788" class="Symbol"
      >:</a
      ><a name="7789"
      > </a
      ><a name="7790" class="Symbol"
      >&#8704;</a
      ><a name="7791"
      > </a
      ><a name="7792" class="Symbol"
      >{</a
      ><a name="7793" href="StlcProp.html#7793" class="Bound"
      >x</a
      ><a name="7794" class="Symbol"
      >}</a
      ><a name="7795"
      > </a
      ><a name="7796" class="Symbol"
      >&#8594;</a
      ><a name="7797"
      > </a
      ><a name="7798" href="StlcProp.html#7793" class="Bound"
      >x</a
      ><a name="7799"
      > </a
      ><a name="7800" href="StlcProp.html#7750" class="Datatype Operator"
      >&#8712;</a
      ><a name="7801"
      > </a
      ><a name="7802" href="Stlc.html#3656" class="InductiveConstructor"
      >`</a
      ><a name="7803"
      > </a
      ><a name="7804" href="StlcProp.html#7793" class="Bound"
      >x</a
      ><a name="7805"
      >
  </a
      ><a name="7808" href="StlcProp.html#7808" class="InductiveConstructor"
      >free-&#955;</a
      ><a name="7814"
      >  </a
      ><a name="7816" class="Symbol"
      >:</a
      ><a name="7817"
      > </a
      ><a name="7818" class="Symbol"
      >&#8704;</a
      ><a name="7819"
      > </a
      ><a name="7820" class="Symbol"
      >{</a
      ><a name="7821" href="StlcProp.html#7821" class="Bound"
      >x</a
      ><a name="7822"
      > </a
      ><a name="7823" href="StlcProp.html#7823" class="Bound"
      >y</a
      ><a name="7824"
      > </a
      ><a name="7825" href="StlcProp.html#7825" class="Bound"
      >A</a
      ><a name="7826"
      > </a
      ><a name="7827" href="StlcProp.html#7827" class="Bound"
      >N</a
      ><a name="7828" class="Symbol"
      >}</a
      ><a name="7829"
      > </a
      ><a name="7830" class="Symbol"
      >&#8594;</a
      ><a name="7831"
      > </a
      ><a name="7832" href="StlcProp.html#7823" class="Bound"
      >y</a
      ><a name="7833"
      > </a
      ><a name="7834" href="https://agda.github.io/agda-stdlib/Relation.Binary.Core.html#4493" class="Function Operator"
      >&#8802;</a
      ><a name="7835"
      > </a
      ><a name="7836" href="StlcProp.html#7821" class="Bound"
      >x</a
      ><a name="7837"
      > </a
      ><a name="7838" class="Symbol"
      >&#8594;</a
      ><a name="7839"
      > </a
      ><a name="7840" href="StlcProp.html#7821" class="Bound"
      >x</a
      ><a name="7841"
      > </a
      ><a name="7842" href="StlcProp.html#7750" class="Datatype Operator"
      >&#8712;</a
      ><a name="7843"
      > </a
      ><a name="7844" href="StlcProp.html#7827" class="Bound"
      >N</a
      ><a name="7845"
      > </a
      ><a name="7846" class="Symbol"
      >&#8594;</a
      ><a name="7847"
      > </a
      ><a name="7848" href="StlcProp.html#7821" class="Bound"
      >x</a
      ><a name="7849"
      > </a
      ><a name="7850" href="StlcProp.html#7750" class="Datatype Operator"
      >&#8712;</a
      ><a name="7851"
      > </a
      ><a name="7852" class="Symbol"
      >(</a
      ><a name="7853" href="Stlc.html#3672" class="InductiveConstructor Operator"
      >&#955;[</a
      ><a name="7855"
      > </a
      ><a name="7856" href="StlcProp.html#7823" class="Bound"
      >y</a
      ><a name="7857"
      > </a
      ><a name="7858" href="Stlc.html#3672" class="InductiveConstructor Operator"
      >&#8758;</a
      ><a name="7859"
      > </a
      ><a name="7860" href="StlcProp.html#7825" class="Bound"
      >A</a
      ><a name="7861"
      > </a
      ><a name="7862" href="Stlc.html#3672" class="InductiveConstructor Operator"
      >]</a
      ><a name="7863"
      > </a
      ><a name="7864" href="StlcProp.html#7827" class="Bound"
      >N</a
      ><a name="7865" class="Symbol"
      >)</a
      ><a name="7866"
      >
  </a
      ><a name="7869" href="StlcProp.html#7869" class="InductiveConstructor"
      >free-&#183;&#8321;</a
      ><a name="7876"
      > </a
      ><a name="7877" class="Symbol"
      >:</a
      ><a name="7878"
      > </a
      ><a name="7879" class="Symbol"
      >&#8704;</a
      ><a name="7880"
      > </a
      ><a name="7881" class="Symbol"
      >{</a
      ><a name="7882" href="StlcProp.html#7882" class="Bound"
      >x</a
      ><a name="7883"
      > </a
      ><a name="7884" href="StlcProp.html#7884" class="Bound"
      >L</a
      ><a name="7885"
      > </a
      ><a name="7886" href="StlcProp.html#7886" class="Bound"
      >M</a
      ><a name="7887" class="Symbol"
      >}</a
      ><a name="7888"
      > </a
      ><a name="7889" class="Symbol"
      >&#8594;</a
      ><a name="7890"
      > </a
      ><a name="7891" href="StlcProp.html#7882" class="Bound"
      >x</a
      ><a name="7892"
      > </a
      ><a name="7893" href="StlcProp.html#7750" class="Datatype Operator"
      >&#8712;</a
      ><a name="7894"
      > </a
      ><a name="7895" href="StlcProp.html#7884" class="Bound"
      >L</a
      ><a name="7896"
      > </a
      ><a name="7897" class="Symbol"
      >&#8594;</a
      ><a name="7898"
      > </a
      ><a name="7899" href="StlcProp.html#7882" class="Bound"
      >x</a
      ><a name="7900"
      > </a
      ><a name="7901" href="StlcProp.html#7750" class="Datatype Operator"
      >&#8712;</a
      ><a name="7902"
      > </a
      ><a name="7903" class="Symbol"
      >(</a
      ><a name="7904" href="StlcProp.html#7884" class="Bound"
      >L</a
      ><a name="7905"
      > </a
      ><a name="7906" href="Stlc.html#3708" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="7907"
      > </a
      ><a name="7908" href="StlcProp.html#7886" class="Bound"
      >M</a
      ><a name="7909" class="Symbol"
      >)</a
      ><a name="7910"
      >
  </a
      ><a name="7913" href="StlcProp.html#7913" class="InductiveConstructor"
      >free-&#183;&#8322;</a
      ><a name="7920"
      > </a
      ><a name="7921" class="Symbol"
      >:</a
      ><a name="7922"
      > </a
      ><a name="7923" class="Symbol"
      >&#8704;</a
      ><a name="7924"
      > </a
      ><a name="7925" class="Symbol"
      >{</a
      ><a name="7926" href="StlcProp.html#7926" class="Bound"
      >x</a
      ><a name="7927"
      > </a
      ><a name="7928" href="StlcProp.html#7928" class="Bound"
      >L</a
      ><a name="7929"
      > </a
      ><a name="7930" href="StlcProp.html#7930" class="Bound"
      >M</a
      ><a name="7931" class="Symbol"
      >}</a
      ><a name="7932"
      > </a
      ><a name="7933" class="Symbol"
      >&#8594;</a
      ><a name="7934"
      > </a
      ><a name="7935" href="StlcProp.html#7926" class="Bound"
      >x</a
      ><a name="7936"
      > </a
      ><a name="7937" href="StlcProp.html#7750" class="Datatype Operator"
      >&#8712;</a
      ><a name="7938"
      > </a
      ><a name="7939" href="StlcProp.html#7930" class="Bound"
      >M</a
      ><a name="7940"
      > </a
      ><a name="7941" class="Symbol"
      >&#8594;</a
      ><a name="7942"
      > </a
      ><a name="7943" href="StlcProp.html#7926" class="Bound"
      >x</a
      ><a name="7944"
      > </a
      ><a name="7945" href="StlcProp.html#7750" class="Datatype Operator"
      >&#8712;</a
      ><a name="7946"
      > </a
      ><a name="7947" class="Symbol"
      >(</a
      ><a name="7948" href="StlcProp.html#7928" class="Bound"
      >L</a
      ><a name="7949"
      > </a
      ><a name="7950" href="Stlc.html#3708" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="7951"
      > </a
      ><a name="7952" href="StlcProp.html#7930" class="Bound"
      >M</a
      ><a name="7953" class="Symbol"
      >)</a
      ><a name="7954"
      >
  </a
      ><a name="7957" href="StlcProp.html#7957" class="InductiveConstructor"
      >free-if&#8321;</a
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
      ><a name="7971" href="StlcProp.html#7971" class="Bound"
      >x</a
      ><a name="7972"
      > </a
      ><a name="7973" href="StlcProp.html#7973" class="Bound"
      >L</a
      ><a name="7974"
      > </a
      ><a name="7975" href="StlcProp.html#7975" class="Bound"
      >M</a
      ><a name="7976"
      > </a
      ><a name="7977" href="StlcProp.html#7977" class="Bound"
      >N</a
      ><a name="7978" class="Symbol"
      >}</a
      ><a name="7979"
      > </a
      ><a name="7980" class="Symbol"
      >&#8594;</a
      ><a name="7981"
      > </a
      ><a name="7982" href="StlcProp.html#7971" class="Bound"
      >x</a
      ><a name="7983"
      > </a
      ><a name="7984" href="StlcProp.html#7750" class="Datatype Operator"
      >&#8712;</a
      ><a name="7985"
      > </a
      ><a name="7986" href="StlcProp.html#7973" class="Bound"
      >L</a
      ><a name="7987"
      > </a
      ><a name="7988" class="Symbol"
      >&#8594;</a
      ><a name="7989"
      > </a
      ><a name="7990" href="StlcProp.html#7971" class="Bound"
      >x</a
      ><a name="7991"
      > </a
      ><a name="7992" href="StlcProp.html#7750" class="Datatype Operator"
      >&#8712;</a
      ><a name="7993"
      > </a
      ><a name="7994" class="Symbol"
      >(</a
      ><a name="7995" href="Stlc.html#3764" class="InductiveConstructor Operator"
      >if</a
      ><a name="7997"
      > </a
      ><a name="7998" href="StlcProp.html#7973" class="Bound"
      >L</a
      ><a name="7999"
      > </a
      ><a name="8000" href="Stlc.html#3764" class="InductiveConstructor Operator"
      >then</a
      ><a name="8004"
      > </a
      ><a name="8005" href="StlcProp.html#7975" class="Bound"
      >M</a
      ><a name="8006"
      > </a
      ><a name="8007" href="Stlc.html#3764" class="InductiveConstructor Operator"
      >else</a
      ><a name="8011"
      > </a
      ><a name="8012" href="StlcProp.html#7977" class="Bound"
      >N</a
      ><a name="8013" class="Symbol"
      >)</a
      ><a name="8014"
      >
  </a
      ><a name="8017" href="StlcProp.html#8017" class="InductiveConstructor"
      >free-if&#8322;</a
      ><a name="8025"
      > </a
      ><a name="8026" class="Symbol"
      >:</a
      ><a name="8027"
      > </a
      ><a name="8028" class="Symbol"
      >&#8704;</a
      ><a name="8029"
      > </a
      ><a name="8030" class="Symbol"
      >{</a
      ><a name="8031" href="StlcProp.html#8031" class="Bound"
      >x</a
      ><a name="8032"
      > </a
      ><a name="8033" href="StlcProp.html#8033" class="Bound"
      >L</a
      ><a name="8034"
      > </a
      ><a name="8035" href="StlcProp.html#8035" class="Bound"
      >M</a
      ><a name="8036"
      > </a
      ><a name="8037" href="StlcProp.html#8037" class="Bound"
      >N</a
      ><a name="8038" class="Symbol"
      >}</a
      ><a name="8039"
      > </a
      ><a name="8040" class="Symbol"
      >&#8594;</a
      ><a name="8041"
      > </a
      ><a name="8042" href="StlcProp.html#8031" class="Bound"
      >x</a
      ><a name="8043"
      > </a
      ><a name="8044" href="StlcProp.html#7750" class="Datatype Operator"
      >&#8712;</a
      ><a name="8045"
      > </a
      ><a name="8046" href="StlcProp.html#8035" class="Bound"
      >M</a
      ><a name="8047"
      > </a
      ><a name="8048" class="Symbol"
      >&#8594;</a
      ><a name="8049"
      > </a
      ><a name="8050" href="StlcProp.html#8031" class="Bound"
      >x</a
      ><a name="8051"
      > </a
      ><a name="8052" href="StlcProp.html#7750" class="Datatype Operator"
      >&#8712;</a
      ><a name="8053"
      > </a
      ><a name="8054" class="Symbol"
      >(</a
      ><a name="8055" href="Stlc.html#3764" class="InductiveConstructor Operator"
      >if</a
      ><a name="8057"
      > </a
      ><a name="8058" href="StlcProp.html#8033" class="Bound"
      >L</a
      ><a name="8059"
      > </a
      ><a name="8060" href="Stlc.html#3764" class="InductiveConstructor Operator"
      >then</a
      ><a name="8064"
      > </a
      ><a name="8065" href="StlcProp.html#8035" class="Bound"
      >M</a
      ><a name="8066"
      > </a
      ><a name="8067" href="Stlc.html#3764" class="InductiveConstructor Operator"
      >else</a
      ><a name="8071"
      > </a
      ><a name="8072" href="StlcProp.html#8037" class="Bound"
      >N</a
      ><a name="8073" class="Symbol"
      >)</a
      ><a name="8074"
      >
  </a
      ><a name="8077" href="StlcProp.html#8077" class="InductiveConstructor"
      >free-if&#8323;</a
      ><a name="8085"
      > </a
      ><a name="8086" class="Symbol"
      >:</a
      ><a name="8087"
      > </a
      ><a name="8088" class="Symbol"
      >&#8704;</a
      ><a name="8089"
      > </a
      ><a name="8090" class="Symbol"
      >{</a
      ><a name="8091" href="StlcProp.html#8091" class="Bound"
      >x</a
      ><a name="8092"
      > </a
      ><a name="8093" href="StlcProp.html#8093" class="Bound"
      >L</a
      ><a name="8094"
      > </a
      ><a name="8095" href="StlcProp.html#8095" class="Bound"
      >M</a
      ><a name="8096"
      > </a
      ><a name="8097" href="StlcProp.html#8097" class="Bound"
      >N</a
      ><a name="8098" class="Symbol"
      >}</a
      ><a name="8099"
      > </a
      ><a name="8100" class="Symbol"
      >&#8594;</a
      ><a name="8101"
      > </a
      ><a name="8102" href="StlcProp.html#8091" class="Bound"
      >x</a
      ><a name="8103"
      > </a
      ><a name="8104" href="StlcProp.html#7750" class="Datatype Operator"
      >&#8712;</a
      ><a name="8105"
      > </a
      ><a name="8106" href="StlcProp.html#8097" class="Bound"
      >N</a
      ><a name="8107"
      > </a
      ><a name="8108" class="Symbol"
      >&#8594;</a
      ><a name="8109"
      > </a
      ><a name="8110" href="StlcProp.html#8091" class="Bound"
      >x</a
      ><a name="8111"
      > </a
      ><a name="8112" href="StlcProp.html#7750" class="Datatype Operator"
      >&#8712;</a
      ><a name="8113"
      > </a
      ><a name="8114" class="Symbol"
      >(</a
      ><a name="8115" href="Stlc.html#3764" class="InductiveConstructor Operator"
      >if</a
      ><a name="8117"
      > </a
      ><a name="8118" href="StlcProp.html#8093" class="Bound"
      >L</a
      ><a name="8119"
      > </a
      ><a name="8120" href="Stlc.html#3764" class="InductiveConstructor Operator"
      >then</a
      ><a name="8124"
      > </a
      ><a name="8125" href="StlcProp.html#8095" class="Bound"
      >M</a
      ><a name="8126"
      > </a
      ><a name="8127" href="Stlc.html#3764" class="InductiveConstructor Operator"
      >else</a
      ><a name="8131"
      > </a
      ><a name="8132" href="StlcProp.html#8097" class="Bound"
      >N</a
      ><a name="8133" class="Symbol"
      >)</a
      >

</pre>

A term in which no variables appear free is said to be _closed_.

<pre class="Agda">

<a name="8226" href="StlcProp.html#8226" class="Function Operator"
      >_&#8713;_</a
      ><a name="8229"
      > </a
      ><a name="8230" class="Symbol"
      >:</a
      ><a name="8231"
      > </a
      ><a name="8232" href="Maps.html#2171" class="Datatype"
      >Id</a
      ><a name="8234"
      > </a
      ><a name="8235" class="Symbol"
      >&#8594;</a
      ><a name="8236"
      > </a
      ><a name="8237" href="Stlc.html#3637" class="Datatype"
      >Term</a
      ><a name="8241"
      > </a
      ><a name="8242" class="Symbol"
      >&#8594;</a
      ><a name="8243"
      > </a
      ><a name="8244" class="PrimitiveType"
      >Set</a
      ><a name="8247"
      >
</a
      ><a name="8248" href="StlcProp.html#8248" class="Bound"
      >x</a
      ><a name="8249"
      > </a
      ><a name="8250" href="StlcProp.html#8226" class="Function Operator"
      >&#8713;</a
      ><a name="8251"
      > </a
      ><a name="8252" href="StlcProp.html#8252" class="Bound"
      >M</a
      ><a name="8253"
      > </a
      ><a name="8254" class="Symbol"
      >=</a
      ><a name="8255"
      > </a
      ><a name="8256" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#414" class="Function Operator"
      >&#172;</a
      ><a name="8257"
      > </a
      ><a name="8258" class="Symbol"
      >(</a
      ><a name="8259" href="StlcProp.html#8248" class="Bound"
      >x</a
      ><a name="8260"
      > </a
      ><a name="8261" href="StlcProp.html#7750" class="Datatype Operator"
      >&#8712;</a
      ><a name="8262"
      > </a
      ><a name="8263" href="StlcProp.html#8252" class="Bound"
      >M</a
      ><a name="8264" class="Symbol"
      >)</a
      ><a name="8265"
      >

</a
      ><a name="8267" href="StlcProp.html#8267" class="Function"
      >closed</a
      ><a name="8273"
      > </a
      ><a name="8274" class="Symbol"
      >:</a
      ><a name="8275"
      > </a
      ><a name="8276" href="Stlc.html#3637" class="Datatype"
      >Term</a
      ><a name="8280"
      > </a
      ><a name="8281" class="Symbol"
      >&#8594;</a
      ><a name="8282"
      > </a
      ><a name="8283" class="PrimitiveType"
      >Set</a
      ><a name="8286"
      >
</a
      ><a name="8287" href="StlcProp.html#8267" class="Function"
      >closed</a
      ><a name="8293"
      > </a
      ><a name="8294" href="StlcProp.html#8294" class="Bound"
      >M</a
      ><a name="8295"
      > </a
      ><a name="8296" class="Symbol"
      >=</a
      ><a name="8297"
      > </a
      ><a name="8298" class="Symbol"
      >&#8704;</a
      ><a name="8299"
      > </a
      ><a name="8300" class="Symbol"
      >{</a
      ><a name="8301" href="StlcProp.html#8301" class="Bound"
      >x</a
      ><a name="8302" class="Symbol"
      >}</a
      ><a name="8303"
      > </a
      ><a name="8304" class="Symbol"
      >&#8594;</a
      ><a name="8305"
      > </a
      ><a name="8306" href="StlcProp.html#8301" class="Bound"
      >x</a
      ><a name="8307"
      > </a
      ><a name="8308" href="StlcProp.html#8226" class="Function Operator"
      >&#8713;</a
      ><a name="8309"
      > </a
      ><a name="8310" href="StlcProp.html#8294" class="Bound"
      >M</a
      >

</pre>

Here are proofs corresponding to the first two examples above.

<pre class="Agda">

<a name="8401" href="StlcProp.html#8401" class="Function"
      >f&#8802;x</a
      ><a name="8404"
      > </a
      ><a name="8405" class="Symbol"
      >:</a
      ><a name="8406"
      > </a
      ><a name="8407" href="Stlc.html#5678" class="Function"
      >f</a
      ><a name="8408"
      > </a
      ><a name="8409" href="https://agda.github.io/agda-stdlib/Relation.Binary.Core.html#4493" class="Function Operator"
      >&#8802;</a
      ><a name="8410"
      > </a
      ><a name="8411" href="Stlc.html#5680" class="Function"
      >x</a
      ><a name="8412"
      >
</a
      ><a name="8413" href="StlcProp.html#8401" class="Function"
      >f&#8802;x</a
      ><a name="8416"
      > </a
      ><a name="8417" class="Symbol"
      >()</a
      ><a name="8419"
      >

</a
      ><a name="8421" href="StlcProp.html#8421" class="Function"
      >example-free&#8321;</a
      ><a name="8434"
      > </a
      ><a name="8435" class="Symbol"
      >:</a
      ><a name="8436"
      > </a
      ><a name="8437" href="Stlc.html#5680" class="Function"
      >x</a
      ><a name="8438"
      > </a
      ><a name="8439" href="StlcProp.html#7750" class="Datatype Operator"
      >&#8712;</a
      ><a name="8440"
      > </a
      ><a name="8441" class="Symbol"
      >(</a
      ><a name="8442" href="Stlc.html#3672" class="InductiveConstructor Operator"
      >&#955;[</a
      ><a name="8444"
      > </a
      ><a name="8445" href="Stlc.html#5678" class="Function"
      >f</a
      ><a name="8446"
      > </a
      ><a name="8447" href="Stlc.html#3672" class="InductiveConstructor Operator"
      >&#8758;</a
      ><a name="8448"
      > </a
      ><a name="8449" class="Symbol"
      >(</a
      ><a name="8450" href="Stlc.html#2610" class="InductiveConstructor"
      >&#120121;</a
      ><a name="8451"
      > </a
      ><a name="8452" href="Stlc.html#2583" class="InductiveConstructor Operator"
      >&#8658;</a
      ><a name="8453"
      > </a
      ><a name="8454" href="Stlc.html#2610" class="InductiveConstructor"
      >&#120121;</a
      ><a name="8455" class="Symbol"
      >)</a
      ><a name="8456"
      > </a
      ><a name="8457" href="Stlc.html#3672" class="InductiveConstructor Operator"
      >]</a
      ><a name="8458"
      > </a
      ><a name="8459" href="Stlc.html#3656" class="InductiveConstructor"
      >`</a
      ><a name="8460"
      > </a
      ><a name="8461" href="Stlc.html#5678" class="Function"
      >f</a
      ><a name="8462"
      > </a
      ><a name="8463" href="Stlc.html#3708" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="8464"
      > </a
      ><a name="8465" href="Stlc.html#3656" class="InductiveConstructor"
      >`</a
      ><a name="8466"
      > </a
      ><a name="8467" href="Stlc.html#5680" class="Function"
      >x</a
      ><a name="8468" class="Symbol"
      >)</a
      ><a name="8469"
      >
</a
      ><a name="8470" href="StlcProp.html#8421" class="Function"
      >example-free&#8321;</a
      ><a name="8483"
      > </a
      ><a name="8484" class="Symbol"
      >=</a
      ><a name="8485"
      > </a
      ><a name="8486" href="StlcProp.html#7808" class="InductiveConstructor"
      >free-&#955;</a
      ><a name="8492"
      > </a
      ><a name="8493" href="StlcProp.html#8401" class="Function"
      >f&#8802;x</a
      ><a name="8496"
      > </a
      ><a name="8497" class="Symbol"
      >(</a
      ><a name="8498" href="StlcProp.html#7913" class="InductiveConstructor"
      >free-&#183;&#8322;</a
      ><a name="8505"
      > </a
      ><a name="8506" href="StlcProp.html#7780" class="InductiveConstructor"
      >free-`</a
      ><a name="8512" class="Symbol"
      >)</a
      ><a name="8513"
      >

</a
      ><a name="8515" href="StlcProp.html#8515" class="Function"
      >example-free&#8322;</a
      ><a name="8528"
      > </a
      ><a name="8529" class="Symbol"
      >:</a
      ><a name="8530"
      > </a
      ><a name="8531" href="Stlc.html#5678" class="Function"
      >f</a
      ><a name="8532"
      > </a
      ><a name="8533" href="StlcProp.html#8226" class="Function Operator"
      >&#8713;</a
      ><a name="8534"
      > </a
      ><a name="8535" class="Symbol"
      >(</a
      ><a name="8536" href="Stlc.html#3672" class="InductiveConstructor Operator"
      >&#955;[</a
      ><a name="8538"
      > </a
      ><a name="8539" href="Stlc.html#5678" class="Function"
      >f</a
      ><a name="8540"
      > </a
      ><a name="8541" href="Stlc.html#3672" class="InductiveConstructor Operator"
      >&#8758;</a
      ><a name="8542"
      > </a
      ><a name="8543" class="Symbol"
      >(</a
      ><a name="8544" href="Stlc.html#2610" class="InductiveConstructor"
      >&#120121;</a
      ><a name="8545"
      > </a
      ><a name="8546" href="Stlc.html#2583" class="InductiveConstructor Operator"
      >&#8658;</a
      ><a name="8547"
      > </a
      ><a name="8548" href="Stlc.html#2610" class="InductiveConstructor"
      >&#120121;</a
      ><a name="8549" class="Symbol"
      >)</a
      ><a name="8550"
      > </a
      ><a name="8551" href="Stlc.html#3672" class="InductiveConstructor Operator"
      >]</a
      ><a name="8552"
      > </a
      ><a name="8553" href="Stlc.html#3656" class="InductiveConstructor"
      >`</a
      ><a name="8554"
      > </a
      ><a name="8555" href="Stlc.html#5678" class="Function"
      >f</a
      ><a name="8556"
      > </a
      ><a name="8557" href="Stlc.html#3708" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="8558"
      > </a
      ><a name="8559" href="Stlc.html#3656" class="InductiveConstructor"
      >`</a
      ><a name="8560"
      > </a
      ><a name="8561" href="Stlc.html#5680" class="Function"
      >x</a
      ><a name="8562" class="Symbol"
      >)</a
      ><a name="8563"
      >
</a
      ><a name="8564" href="StlcProp.html#8515" class="Function"
      >example-free&#8322;</a
      ><a name="8577"
      > </a
      ><a name="8578" class="Symbol"
      >(</a
      ><a name="8579" href="StlcProp.html#7808" class="InductiveConstructor"
      >free-&#955;</a
      ><a name="8585"
      > </a
      ><a name="8586" href="StlcProp.html#8586" class="Bound"
      >f&#8802;f</a
      ><a name="8589"
      > </a
      ><a name="8590" class="Symbol"
      >_)</a
      ><a name="8592"
      > </a
      ><a name="8593" class="Symbol"
      >=</a
      ><a name="8594"
      > </a
      ><a name="8595" href="StlcProp.html#8586" class="Bound"
      >f&#8802;f</a
      ><a name="8598"
      > </a
      ><a name="8599" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      >

</pre>


#### Exercise: 1 star (free-in)
Prove formally the remaining examples given above.

<pre class="Agda">

<a name="8714" class="Keyword"
      >postulate</a
      ><a name="8723"
      >
  </a
      ><a name="8726" href="StlcProp.html#8726" class="Postulate"
      >example-free&#8323;</a
      ><a name="8739"
      > </a
      ><a name="8740" class="Symbol"
      >:</a
      ><a name="8741"
      > </a
      ><a name="8742" href="Stlc.html#5680" class="Function"
      >x</a
      ><a name="8743"
      > </a
      ><a name="8744" href="StlcProp.html#7750" class="Datatype Operator"
      >&#8712;</a
      ><a name="8745"
      > </a
      ><a name="8746" class="Symbol"
      >((</a
      ><a name="8748" href="Stlc.html#3672" class="InductiveConstructor Operator"
      >&#955;[</a
      ><a name="8750"
      > </a
      ><a name="8751" href="Stlc.html#5678" class="Function"
      >f</a
      ><a name="8752"
      > </a
      ><a name="8753" href="Stlc.html#3672" class="InductiveConstructor Operator"
      >&#8758;</a
      ><a name="8754"
      > </a
      ><a name="8755" class="Symbol"
      >(</a
      ><a name="8756" href="Stlc.html#2610" class="InductiveConstructor"
      >&#120121;</a
      ><a name="8757"
      > </a
      ><a name="8758" href="Stlc.html#2583" class="InductiveConstructor Operator"
      >&#8658;</a
      ><a name="8759"
      > </a
      ><a name="8760" href="Stlc.html#2610" class="InductiveConstructor"
      >&#120121;</a
      ><a name="8761" class="Symbol"
      >)</a
      ><a name="8762"
      > </a
      ><a name="8763" href="Stlc.html#3672" class="InductiveConstructor Operator"
      >]</a
      ><a name="8764"
      > </a
      ><a name="8765" href="Stlc.html#3656" class="InductiveConstructor"
      >`</a
      ><a name="8766"
      > </a
      ><a name="8767" href="Stlc.html#5678" class="Function"
      >f</a
      ><a name="8768"
      > </a
      ><a name="8769" href="Stlc.html#3708" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="8770"
      > </a
      ><a name="8771" href="Stlc.html#3656" class="InductiveConstructor"
      >`</a
      ><a name="8772"
      > </a
      ><a name="8773" href="Stlc.html#5680" class="Function"
      >x</a
      ><a name="8774" class="Symbol"
      >)</a
      ><a name="8775"
      > </a
      ><a name="8776" href="Stlc.html#3708" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="8777"
      > </a
      ><a name="8778" href="Stlc.html#3656" class="InductiveConstructor"
      >`</a
      ><a name="8779"
      > </a
      ><a name="8780" href="Stlc.html#5678" class="Function"
      >f</a
      ><a name="8781" class="Symbol"
      >)</a
      ><a name="8782"
      >
  </a
      ><a name="8785" href="StlcProp.html#8785" class="Postulate"
      >example-free&#8324;</a
      ><a name="8798"
      > </a
      ><a name="8799" class="Symbol"
      >:</a
      ><a name="8800"
      > </a
      ><a name="8801" href="Stlc.html#5678" class="Function"
      >f</a
      ><a name="8802"
      > </a
      ><a name="8803" href="StlcProp.html#7750" class="Datatype Operator"
      >&#8712;</a
      ><a name="8804"
      > </a
      ><a name="8805" class="Symbol"
      >((</a
      ><a name="8807" href="Stlc.html#3672" class="InductiveConstructor Operator"
      >&#955;[</a
      ><a name="8809"
      > </a
      ><a name="8810" href="Stlc.html#5678" class="Function"
      >f</a
      ><a name="8811"
      > </a
      ><a name="8812" href="Stlc.html#3672" class="InductiveConstructor Operator"
      >&#8758;</a
      ><a name="8813"
      > </a
      ><a name="8814" class="Symbol"
      >(</a
      ><a name="8815" href="Stlc.html#2610" class="InductiveConstructor"
      >&#120121;</a
      ><a name="8816"
      > </a
      ><a name="8817" href="Stlc.html#2583" class="InductiveConstructor Operator"
      >&#8658;</a
      ><a name="8818"
      > </a
      ><a name="8819" href="Stlc.html#2610" class="InductiveConstructor"
      >&#120121;</a
      ><a name="8820" class="Symbol"
      >)</a
      ><a name="8821"
      > </a
      ><a name="8822" href="Stlc.html#3672" class="InductiveConstructor Operator"
      >]</a
      ><a name="8823"
      > </a
      ><a name="8824" href="Stlc.html#3656" class="InductiveConstructor"
      >`</a
      ><a name="8825"
      > </a
      ><a name="8826" href="Stlc.html#5678" class="Function"
      >f</a
      ><a name="8827"
      > </a
      ><a name="8828" href="Stlc.html#3708" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="8829"
      > </a
      ><a name="8830" href="Stlc.html#3656" class="InductiveConstructor"
      >`</a
      ><a name="8831"
      > </a
      ><a name="8832" href="Stlc.html#5680" class="Function"
      >x</a
      ><a name="8833" class="Symbol"
      >)</a
      ><a name="8834"
      > </a
      ><a name="8835" href="Stlc.html#3708" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="8836"
      > </a
      ><a name="8837" href="Stlc.html#3656" class="InductiveConstructor"
      >`</a
      ><a name="8838"
      > </a
      ><a name="8839" href="Stlc.html#5678" class="Function"
      >f</a
      ><a name="8840" class="Symbol"
      >)</a
      ><a name="8841"
      >
  </a
      ><a name="8844" href="StlcProp.html#8844" class="Postulate"
      >example-free&#8325;</a
      ><a name="8857"
      > </a
      ><a name="8858" class="Symbol"
      >:</a
      ><a name="8859"
      > </a
      ><a name="8860" href="Stlc.html#5680" class="Function"
      >x</a
      ><a name="8861"
      > </a
      ><a name="8862" href="StlcProp.html#8226" class="Function Operator"
      >&#8713;</a
      ><a name="8863"
      > </a
      ><a name="8864" class="Symbol"
      >(</a
      ><a name="8865" href="Stlc.html#3672" class="InductiveConstructor Operator"
      >&#955;[</a
      ><a name="8867"
      > </a
      ><a name="8868" href="Stlc.html#5678" class="Function"
      >f</a
      ><a name="8869"
      > </a
      ><a name="8870" href="Stlc.html#3672" class="InductiveConstructor Operator"
      >&#8758;</a
      ><a name="8871"
      > </a
      ><a name="8872" class="Symbol"
      >(</a
      ><a name="8873" href="Stlc.html#2610" class="InductiveConstructor"
      >&#120121;</a
      ><a name="8874"
      > </a
      ><a name="8875" href="Stlc.html#2583" class="InductiveConstructor Operator"
      >&#8658;</a
      ><a name="8876"
      > </a
      ><a name="8877" href="Stlc.html#2610" class="InductiveConstructor"
      >&#120121;</a
      ><a name="8878" class="Symbol"
      >)</a
      ><a name="8879"
      > </a
      ><a name="8880" href="Stlc.html#3672" class="InductiveConstructor Operator"
      >]</a
      ><a name="8881"
      > </a
      ><a name="8882" href="Stlc.html#3672" class="InductiveConstructor Operator"
      >&#955;[</a
      ><a name="8884"
      > </a
      ><a name="8885" href="Stlc.html#5680" class="Function"
      >x</a
      ><a name="8886"
      > </a
      ><a name="8887" href="Stlc.html#3672" class="InductiveConstructor Operator"
      >&#8758;</a
      ><a name="8888"
      > </a
      ><a name="8889" href="Stlc.html#2610" class="InductiveConstructor"
      >&#120121;</a
      ><a name="8890"
      > </a
      ><a name="8891" href="Stlc.html#3672" class="InductiveConstructor Operator"
      >]</a
      ><a name="8892"
      > </a
      ><a name="8893" href="Stlc.html#3656" class="InductiveConstructor"
      >`</a
      ><a name="8894"
      > </a
      ><a name="8895" href="Stlc.html#5678" class="Function"
      >f</a
      ><a name="8896"
      > </a
      ><a name="8897" href="Stlc.html#3708" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="8898"
      > </a
      ><a name="8899" href="Stlc.html#3656" class="InductiveConstructor"
      >`</a
      ><a name="8900"
      > </a
      ><a name="8901" href="Stlc.html#5680" class="Function"
      >x</a
      ><a name="8902" class="Symbol"
      >)</a
      ><a name="8903"
      >
  </a
      ><a name="8906" href="StlcProp.html#8906" class="Postulate"
      >example-free&#8326;</a
      ><a name="8919"
      > </a
      ><a name="8920" class="Symbol"
      >:</a
      ><a name="8921"
      > </a
      ><a name="8922" href="Stlc.html#5678" class="Function"
      >f</a
      ><a name="8923"
      > </a
      ><a name="8924" href="StlcProp.html#8226" class="Function Operator"
      >&#8713;</a
      ><a name="8925"
      > </a
      ><a name="8926" class="Symbol"
      >(</a
      ><a name="8927" href="Stlc.html#3672" class="InductiveConstructor Operator"
      >&#955;[</a
      ><a name="8929"
      > </a
      ><a name="8930" href="Stlc.html#5678" class="Function"
      >f</a
      ><a name="8931"
      > </a
      ><a name="8932" href="Stlc.html#3672" class="InductiveConstructor Operator"
      >&#8758;</a
      ><a name="8933"
      > </a
      ><a name="8934" class="Symbol"
      >(</a
      ><a name="8935" href="Stlc.html#2610" class="InductiveConstructor"
      >&#120121;</a
      ><a name="8936"
      > </a
      ><a name="8937" href="Stlc.html#2583" class="InductiveConstructor Operator"
      >&#8658;</a
      ><a name="8938"
      > </a
      ><a name="8939" href="Stlc.html#2610" class="InductiveConstructor"
      >&#120121;</a
      ><a name="8940" class="Symbol"
      >)</a
      ><a name="8941"
      > </a
      ><a name="8942" href="Stlc.html#3672" class="InductiveConstructor Operator"
      >]</a
      ><a name="8943"
      > </a
      ><a name="8944" href="Stlc.html#3672" class="InductiveConstructor Operator"
      >&#955;[</a
      ><a name="8946"
      > </a
      ><a name="8947" href="Stlc.html#5680" class="Function"
      >x</a
      ><a name="8948"
      > </a
      ><a name="8949" href="Stlc.html#3672" class="InductiveConstructor Operator"
      >&#8758;</a
      ><a name="8950"
      > </a
      ><a name="8951" href="Stlc.html#2610" class="InductiveConstructor"
      >&#120121;</a
      ><a name="8952"
      > </a
      ><a name="8953" href="Stlc.html#3672" class="InductiveConstructor Operator"
      >]</a
      ><a name="8954"
      > </a
      ><a name="8955" href="Stlc.html#3656" class="InductiveConstructor"
      >`</a
      ><a name="8956"
      > </a
      ><a name="8957" href="Stlc.html#5678" class="Function"
      >f</a
      ><a name="8958"
      > </a
      ><a name="8959" href="Stlc.html#3708" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="8960"
      > </a
      ><a name="8961" href="Stlc.html#3656" class="InductiveConstructor"
      >`</a
      ><a name="8962"
      > </a
      ><a name="8963" href="Stlc.html#5680" class="Function"
      >x</a
      ><a name="8964" class="Symbol"
      >)</a
      >

</pre>

Although `_∈_` may appear to be a low-level technical definition,
understanding it is crucial to understanding the properties of
substitution, which are really the crux of the lambda calculus.

### Substitution

To prove that substitution preserves typing, we first need a technical
lemma connecting free variables and typing contexts. If variable `x`
appears free in term `M`, and if `M` is well typed in context `Γ`,
then `Γ` must assign a type to `x`.

<pre class="Agda">

<a name="9447" href="StlcProp.html#9447" class="Function"
      >free-lemma</a
      ><a name="9457"
      > </a
      ><a name="9458" class="Symbol"
      >:</a
      ><a name="9459"
      > </a
      ><a name="9460" class="Symbol"
      >&#8704;</a
      ><a name="9461"
      > </a
      ><a name="9462" class="Symbol"
      >{</a
      ><a name="9463" href="StlcProp.html#9463" class="Bound"
      >x</a
      ><a name="9464"
      > </a
      ><a name="9465" href="StlcProp.html#9465" class="Bound"
      >M</a
      ><a name="9466"
      > </a
      ><a name="9467" href="StlcProp.html#9467" class="Bound"
      >A</a
      ><a name="9468"
      > </a
      ><a name="9469" href="StlcProp.html#9469" class="Bound"
      >&#915;</a
      ><a name="9470" class="Symbol"
      >}</a
      ><a name="9471"
      > </a
      ><a name="9472" class="Symbol"
      >&#8594;</a
      ><a name="9473"
      > </a
      ><a name="9474" href="StlcProp.html#9463" class="Bound"
      >x</a
      ><a name="9475"
      > </a
      ><a name="9476" href="StlcProp.html#7750" class="Datatype Operator"
      >&#8712;</a
      ><a name="9477"
      > </a
      ><a name="9478" href="StlcProp.html#9465" class="Bound"
      >M</a
      ><a name="9479"
      > </a
      ><a name="9480" class="Symbol"
      >&#8594;</a
      ><a name="9481"
      > </a
      ><a name="9482" href="StlcProp.html#9469" class="Bound"
      >&#915;</a
      ><a name="9483"
      > </a
      ><a name="9484" href="Stlc.html#21569" class="Datatype Operator"
      >&#8866;</a
      ><a name="9485"
      > </a
      ><a name="9486" href="StlcProp.html#9465" class="Bound"
      >M</a
      ><a name="9487"
      > </a
      ><a name="9488" href="Stlc.html#21569" class="Datatype Operator"
      >&#8758;</a
      ><a name="9489"
      > </a
      ><a name="9490" href="StlcProp.html#9467" class="Bound"
      >A</a
      ><a name="9491"
      > </a
      ><a name="9492" class="Symbol"
      >&#8594;</a
      ><a name="9493"
      > </a
      ><a name="9494" href="https://agda.github.io/agda-stdlib/Data.Product.html#823" class="Function"
      >&#8707;</a
      ><a name="9495"
      > </a
      ><a name="9496" class="Symbol"
      >&#955;</a
      ><a name="9497"
      > </a
      ><a name="9498" href="StlcProp.html#9498" class="Bound"
      >B</a
      ><a name="9499"
      > </a
      ><a name="9500" class="Symbol"
      >&#8594;</a
      ><a name="9501"
      > </a
      ><a name="9502" href="StlcProp.html#9469" class="Bound"
      >&#915;</a
      ><a name="9503"
      > </a
      ><a name="9504" href="StlcProp.html#9463" class="Bound"
      >x</a
      ><a name="9505"
      > </a
      ><a name="9506" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="9507"
      > </a
      ><a name="9508" href="https://agda.github.io/agda-stdlib/Data.Maybe.Base.html#373" class="InductiveConstructor"
      >just</a
      ><a name="9512"
      > </a
      ><a name="9513" href="StlcProp.html#9498" class="Bound"
      >B</a
      >

</pre>

_Proof_: We show, by induction on the proof that `x` appears
  free in `M`, that, for all contexts `Γ`, if `M` is well
  typed under `Γ`, then `Γ` assigns some type to `x`.

  - If the last rule used was `` free-` ``, then `M = `` `x ``, and from
    the assumption that `M` is well typed under `Γ` we have
    immediately that `Γ` assigns a type to `x`.

  - If the last rule used was `free-·₁`, then `M = L · M` and `x`
    appears free in `L`.  Since `L` is well typed under `Γ`,
    we can see from the typing rules that `L` must also be, and
    the IH then tells us that `Γ` assigns `x` a type.

  - Almost all the other cases are similar: `x` appears free in a
    subterm of `M`, and since `M` is well typed under `Γ`, we
    know the subterm of `M` in which `x` appears is well typed
    under `Γ` as well, and the IH yields the desired conclusion.

  - The only remaining case is `free-λ`.  In this case `M =
    λ[ y ∶ A ] N`, and `x` appears free in `N`; we also know that
    `x` is different from `y`.  The difference from the previous
    cases is that whereas `M` is well typed under `Γ`, its
    body `N` is well typed under `(Γ , y ∶ A)`, so the IH
    allows us to conclude that `x` is assigned some type by the
    extended context `(Γ , y ∶ A)`.  To conclude that `Γ`
    assigns a type to `x`, we appeal the decidable equality for names
    `_≟_`, and note that `x` and `y` are different variables.

<pre class="Agda">

<a name="10962" href="StlcProp.html#9447" class="Function"
      >free-lemma</a
      ><a name="10972"
      > </a
      ><a name="10973" href="StlcProp.html#7780" class="InductiveConstructor"
      >free-`</a
      ><a name="10979"
      > </a
      ><a name="10980" class="Symbol"
      >(</a
      ><a name="10981" href="Stlc.html#21613" class="InductiveConstructor"
      >Ax</a
      ><a name="10983"
      > </a
      ><a name="10984" href="StlcProp.html#10984" class="Bound"
      >&#915;x&#8801;A</a
      ><a name="10988" class="Symbol"
      >)</a
      ><a name="10989"
      > </a
      ><a name="10990" class="Symbol"
      >=</a
      ><a name="10991"
      > </a
      ><a name="10992" class="Symbol"
      >(_</a
      ><a name="10994"
      > </a
      ><a name="10995" href="https://agda.github.io/agda-stdlib/Data.Product.html#509" class="InductiveConstructor Operator"
      >,</a
      ><a name="10996"
      > </a
      ><a name="10997" href="StlcProp.html#10984" class="Bound"
      >&#915;x&#8801;A</a
      ><a name="11001" class="Symbol"
      >)</a
      ><a name="11002"
      >
</a
      ><a name="11003" href="StlcProp.html#9447" class="Function"
      >free-lemma</a
      ><a name="11013"
      > </a
      ><a name="11014" class="Symbol"
      >(</a
      ><a name="11015" href="StlcProp.html#7869" class="InductiveConstructor"
      >free-&#183;&#8321;</a
      ><a name="11022"
      > </a
      ><a name="11023" href="StlcProp.html#11023" class="Bound"
      >x&#8712;L</a
      ><a name="11026" class="Symbol"
      >)</a
      ><a name="11027"
      > </a
      ><a name="11028" class="Symbol"
      >(</a
      ><a name="11029" href="Stlc.html#21744" class="InductiveConstructor"
      >&#8658;-E</a
      ><a name="11032"
      > </a
      ><a name="11033" href="StlcProp.html#11033" class="Bound"
      >&#8866;L</a
      ><a name="11035"
      > </a
      ><a name="11036" href="StlcProp.html#11036" class="Bound"
      >&#8866;M</a
      ><a name="11038" class="Symbol"
      >)</a
      ><a name="11039"
      > </a
      ><a name="11040" class="Symbol"
      >=</a
      ><a name="11041"
      > </a
      ><a name="11042" href="StlcProp.html#9447" class="Function"
      >free-lemma</a
      ><a name="11052"
      > </a
      ><a name="11053" href="StlcProp.html#11023" class="Bound"
      >x&#8712;L</a
      ><a name="11056"
      > </a
      ><a name="11057" href="StlcProp.html#11033" class="Bound"
      >&#8866;L</a
      ><a name="11059"
      >
</a
      ><a name="11060" href="StlcProp.html#9447" class="Function"
      >free-lemma</a
      ><a name="11070"
      > </a
      ><a name="11071" class="Symbol"
      >(</a
      ><a name="11072" href="StlcProp.html#7913" class="InductiveConstructor"
      >free-&#183;&#8322;</a
      ><a name="11079"
      > </a
      ><a name="11080" href="StlcProp.html#11080" class="Bound"
      >x&#8712;M</a
      ><a name="11083" class="Symbol"
      >)</a
      ><a name="11084"
      > </a
      ><a name="11085" class="Symbol"
      >(</a
      ><a name="11086" href="Stlc.html#21744" class="InductiveConstructor"
      >&#8658;-E</a
      ><a name="11089"
      > </a
      ><a name="11090" href="StlcProp.html#11090" class="Bound"
      >&#8866;L</a
      ><a name="11092"
      > </a
      ><a name="11093" href="StlcProp.html#11093" class="Bound"
      >&#8866;M</a
      ><a name="11095" class="Symbol"
      >)</a
      ><a name="11096"
      > </a
      ><a name="11097" class="Symbol"
      >=</a
      ><a name="11098"
      > </a
      ><a name="11099" href="StlcProp.html#9447" class="Function"
      >free-lemma</a
      ><a name="11109"
      > </a
      ><a name="11110" href="StlcProp.html#11080" class="Bound"
      >x&#8712;M</a
      ><a name="11113"
      > </a
      ><a name="11114" href="StlcProp.html#11093" class="Bound"
      >&#8866;M</a
      ><a name="11116"
      >
</a
      ><a name="11117" href="StlcProp.html#9447" class="Function"
      >free-lemma</a
      ><a name="11127"
      > </a
      ><a name="11128" class="Symbol"
      >(</a
      ><a name="11129" href="StlcProp.html#7957" class="InductiveConstructor"
      >free-if&#8321;</a
      ><a name="11137"
      > </a
      ><a name="11138" href="StlcProp.html#11138" class="Bound"
      >x&#8712;L</a
      ><a name="11141" class="Symbol"
      >)</a
      ><a name="11142"
      > </a
      ><a name="11143" class="Symbol"
      >(</a
      ><a name="11144" href="Stlc.html#21891" class="InductiveConstructor"
      >&#120121;-E</a
      ><a name="11147"
      > </a
      ><a name="11148" href="StlcProp.html#11148" class="Bound"
      >&#8866;L</a
      ><a name="11150"
      > </a
      ><a name="11151" href="StlcProp.html#11151" class="Bound"
      >&#8866;M</a
      ><a name="11153"
      > </a
      ><a name="11154" href="StlcProp.html#11154" class="Bound"
      >&#8866;N</a
      ><a name="11156" class="Symbol"
      >)</a
      ><a name="11157"
      > </a
      ><a name="11158" class="Symbol"
      >=</a
      ><a name="11159"
      > </a
      ><a name="11160" href="StlcProp.html#9447" class="Function"
      >free-lemma</a
      ><a name="11170"
      > </a
      ><a name="11171" href="StlcProp.html#11138" class="Bound"
      >x&#8712;L</a
      ><a name="11174"
      > </a
      ><a name="11175" href="StlcProp.html#11148" class="Bound"
      >&#8866;L</a
      ><a name="11177"
      >
</a
      ><a name="11178" href="StlcProp.html#9447" class="Function"
      >free-lemma</a
      ><a name="11188"
      > </a
      ><a name="11189" class="Symbol"
      >(</a
      ><a name="11190" href="StlcProp.html#8017" class="InductiveConstructor"
      >free-if&#8322;</a
      ><a name="11198"
      > </a
      ><a name="11199" href="StlcProp.html#11199" class="Bound"
      >x&#8712;M</a
      ><a name="11202" class="Symbol"
      >)</a
      ><a name="11203"
      > </a
      ><a name="11204" class="Symbol"
      >(</a
      ><a name="11205" href="Stlc.html#21891" class="InductiveConstructor"
      >&#120121;-E</a
      ><a name="11208"
      > </a
      ><a name="11209" href="StlcProp.html#11209" class="Bound"
      >&#8866;L</a
      ><a name="11211"
      > </a
      ><a name="11212" href="StlcProp.html#11212" class="Bound"
      >&#8866;M</a
      ><a name="11214"
      > </a
      ><a name="11215" href="StlcProp.html#11215" class="Bound"
      >&#8866;N</a
      ><a name="11217" class="Symbol"
      >)</a
      ><a name="11218"
      > </a
      ><a name="11219" class="Symbol"
      >=</a
      ><a name="11220"
      > </a
      ><a name="11221" href="StlcProp.html#9447" class="Function"
      >free-lemma</a
      ><a name="11231"
      > </a
      ><a name="11232" href="StlcProp.html#11199" class="Bound"
      >x&#8712;M</a
      ><a name="11235"
      > </a
      ><a name="11236" href="StlcProp.html#11212" class="Bound"
      >&#8866;M</a
      ><a name="11238"
      >
</a
      ><a name="11239" href="StlcProp.html#9447" class="Function"
      >free-lemma</a
      ><a name="11249"
      > </a
      ><a name="11250" class="Symbol"
      >(</a
      ><a name="11251" href="StlcProp.html#8077" class="InductiveConstructor"
      >free-if&#8323;</a
      ><a name="11259"
      > </a
      ><a name="11260" href="StlcProp.html#11260" class="Bound"
      >x&#8712;N</a
      ><a name="11263" class="Symbol"
      >)</a
      ><a name="11264"
      > </a
      ><a name="11265" class="Symbol"
      >(</a
      ><a name="11266" href="Stlc.html#21891" class="InductiveConstructor"
      >&#120121;-E</a
      ><a name="11269"
      > </a
      ><a name="11270" href="StlcProp.html#11270" class="Bound"
      >&#8866;L</a
      ><a name="11272"
      > </a
      ><a name="11273" href="StlcProp.html#11273" class="Bound"
      >&#8866;M</a
      ><a name="11275"
      > </a
      ><a name="11276" href="StlcProp.html#11276" class="Bound"
      >&#8866;N</a
      ><a name="11278" class="Symbol"
      >)</a
      ><a name="11279"
      > </a
      ><a name="11280" class="Symbol"
      >=</a
      ><a name="11281"
      > </a
      ><a name="11282" href="StlcProp.html#9447" class="Function"
      >free-lemma</a
      ><a name="11292"
      > </a
      ><a name="11293" href="StlcProp.html#11260" class="Bound"
      >x&#8712;N</a
      ><a name="11296"
      > </a
      ><a name="11297" href="StlcProp.html#11276" class="Bound"
      >&#8866;N</a
      ><a name="11299"
      >
</a
      ><a name="11300" href="StlcProp.html#9447" class="Function"
      >free-lemma</a
      ><a name="11310"
      > </a
      ><a name="11311" class="Symbol"
      >(</a
      ><a name="11312" href="StlcProp.html#7808" class="InductiveConstructor"
      >free-&#955;</a
      ><a name="11318"
      > </a
      ><a name="11319" class="Symbol"
      >{</a
      ><a name="11320" href="StlcProp.html#11320" class="Bound"
      >x</a
      ><a name="11321" class="Symbol"
      >}</a
      ><a name="11322"
      > </a
      ><a name="11323" class="Symbol"
      >{</a
      ><a name="11324" href="StlcProp.html#11324" class="Bound"
      >y</a
      ><a name="11325" class="Symbol"
      >}</a
      ><a name="11326"
      > </a
      ><a name="11327" href="StlcProp.html#11327" class="Bound"
      >y&#8802;x</a
      ><a name="11330"
      > </a
      ><a name="11331" href="StlcProp.html#11331" class="Bound"
      >x&#8712;N</a
      ><a name="11334" class="Symbol"
      >)</a
      ><a name="11335"
      > </a
      ><a name="11336" class="Symbol"
      >(</a
      ><a name="11337" href="Stlc.html#21667" class="InductiveConstructor"
      >&#8658;-I</a
      ><a name="11340"
      > </a
      ><a name="11341" href="StlcProp.html#11341" class="Bound"
      >&#8866;N</a
      ><a name="11343" class="Symbol"
      >)</a
      ><a name="11344"
      > </a
      ><a name="11345" class="Keyword"
      >with</a
      ><a name="11349"
      > </a
      ><a name="11350" href="StlcProp.html#9447" class="Function"
      >free-lemma</a
      ><a name="11360"
      > </a
      ><a name="11361" href="StlcProp.html#11331" class="Bound"
      >x&#8712;N</a
      ><a name="11364"
      > </a
      ><a name="11365" href="StlcProp.html#11341" class="Bound"
      >&#8866;N</a
      ><a name="11367"
      >
</a
      ><a name="11368" class="Symbol"
      >...</a
      ><a name="11371"
      > </a
      ><a name="11372" class="Symbol"
      >|</a
      ><a name="11373"
      > </a
      ><a name="11374" href="StlcProp.html#11374" class="Bound"
      >&#915;x&#8801;C</a
      ><a name="11378"
      > </a
      ><a name="11379" class="Keyword"
      >with</a
      ><a name="11383"
      > </a
      ><a name="11384" href="StlcProp.html#11324" class="Bound"
      >y</a
      ><a name="11385"
      > </a
      ><a name="11386" href="Maps.html#2509" class="Function Operator"
      >&#8799;</a
      ><a name="11387"
      > </a
      ><a name="11388" href="StlcProp.html#11320" class="Bound"
      >x</a
      ><a name="11389"
      >
</a
      ><a name="11390" class="Symbol"
      >...</a
      ><a name="11393"
      > </a
      ><a name="11394" class="Symbol"
      >|</a
      ><a name="11395"
      > </a
      ><a name="11396" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#520" class="InductiveConstructor"
      >yes</a
      ><a name="11399"
      > </a
      ><a name="11400" href="StlcProp.html#11400" class="Bound"
      >y&#8801;x</a
      ><a name="11403"
      > </a
      ><a name="11404" class="Symbol"
      >=</a
      ><a name="11405"
      > </a
      ><a name="11406" href="https://agda.github.io/agda-stdlib/Data.Empty.html#348" class="Function"
      >&#8869;-elim</a
      ><a name="11412"
      > </a
      ><a name="11413" class="Symbol"
      >(</a
      ><a name="11414" href="StlcProp.html#11327" class="Bound"
      >y&#8802;x</a
      ><a name="11417"
      > </a
      ><a name="11418" href="StlcProp.html#11400" class="Bound"
      >y&#8801;x</a
      ><a name="11421" class="Symbol"
      >)</a
      ><a name="11422"
      >
</a
      ><a name="11423" class="Symbol"
      >...</a
      ><a name="11426"
      > </a
      ><a name="11427" class="Symbol"
      >|</a
      ><a name="11428"
      > </a
      ><a name="11429" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#547" class="InductiveConstructor"
      >no</a
      ><a name="11431"
      >  </a
      ><a name="11433" class="Symbol"
      >_</a
      ><a name="11434"
      >   </a
      ><a name="11437" class="Symbol"
      >=</a
      ><a name="11438"
      > </a
      ><a name="11439" href="StlcProp.html#11374" class="Bound"
      >&#915;x&#8801;C</a
      >

</pre>

A subtle point: if the first argument of `free-λ` was of type
`x ≢ y` rather than of type `y ≢ x`, then the type of the
term `Γx≡C` would not simplify properly; instead, one would need
to rewrite with the symmetric equivalence.

As a second technical lemma, we need that any term `M` which is well
typed in the empty context is closed (has no free variables).

#### Exercise: 2 stars, optional (∅⊢-closed)

<pre class="Agda">

<a name="11876" class="Keyword"
      >postulate</a
      ><a name="11885"
      >
  </a
      ><a name="11888" href="StlcProp.html#11888" class="Postulate"
      >&#8709;&#8866;-closed</a
      ><a name="11897"
      > </a
      ><a name="11898" class="Symbol"
      >:</a
      ><a name="11899"
      > </a
      ><a name="11900" class="Symbol"
      >&#8704;</a
      ><a name="11901"
      > </a
      ><a name="11902" class="Symbol"
      >{</a
      ><a name="11903" href="StlcProp.html#11903" class="Bound"
      >M</a
      ><a name="11904"
      > </a
      ><a name="11905" href="StlcProp.html#11905" class="Bound"
      >A</a
      ><a name="11906" class="Symbol"
      >}</a
      ><a name="11907"
      > </a
      ><a name="11908" class="Symbol"
      >&#8594;</a
      ><a name="11909"
      > </a
      ><a name="11910" href="Maps.html#10265" class="Function"
      >&#8709;</a
      ><a name="11911"
      > </a
      ><a name="11912" href="Stlc.html#21569" class="Datatype Operator"
      >&#8866;</a
      ><a name="11913"
      > </a
      ><a name="11914" href="StlcProp.html#11903" class="Bound"
      >M</a
      ><a name="11915"
      > </a
      ><a name="11916" href="Stlc.html#21569" class="Datatype Operator"
      >&#8758;</a
      ><a name="11917"
      > </a
      ><a name="11918" href="StlcProp.html#11905" class="Bound"
      >A</a
      ><a name="11919"
      > </a
      ><a name="11920" class="Symbol"
      >&#8594;</a
      ><a name="11921"
      > </a
      ><a name="11922" href="StlcProp.html#8267" class="Function"
      >closed</a
      ><a name="11928"
      > </a
      ><a name="11929" href="StlcProp.html#11903" class="Bound"
      >M</a
      >

</pre>

<div class="hidden">
<pre class="Agda">

<a name="11977" href="StlcProp.html#11977" class="Function"
      >&#8709;&#8866;-closed&#8242;</a
      ><a name="11987"
      > </a
      ><a name="11988" class="Symbol"
      >:</a
      ><a name="11989"
      > </a
      ><a name="11990" class="Symbol"
      >&#8704;</a
      ><a name="11991"
      > </a
      ><a name="11992" class="Symbol"
      >{</a
      ><a name="11993" href="StlcProp.html#11993" class="Bound"
      >M</a
      ><a name="11994"
      > </a
      ><a name="11995" href="StlcProp.html#11995" class="Bound"
      >A</a
      ><a name="11996" class="Symbol"
      >}</a
      ><a name="11997"
      > </a
      ><a name="11998" class="Symbol"
      >&#8594;</a
      ><a name="11999"
      > </a
      ><a name="12000" href="Maps.html#10265" class="Function"
      >&#8709;</a
      ><a name="12001"
      > </a
      ><a name="12002" href="Stlc.html#21569" class="Datatype Operator"
      >&#8866;</a
      ><a name="12003"
      > </a
      ><a name="12004" href="StlcProp.html#11993" class="Bound"
      >M</a
      ><a name="12005"
      > </a
      ><a name="12006" href="Stlc.html#21569" class="Datatype Operator"
      >&#8758;</a
      ><a name="12007"
      > </a
      ><a name="12008" href="StlcProp.html#11995" class="Bound"
      >A</a
      ><a name="12009"
      > </a
      ><a name="12010" class="Symbol"
      >&#8594;</a
      ><a name="12011"
      > </a
      ><a name="12012" href="StlcProp.html#8267" class="Function"
      >closed</a
      ><a name="12018"
      > </a
      ><a name="12019" href="StlcProp.html#11993" class="Bound"
      >M</a
      ><a name="12020"
      >
</a
      ><a name="12021" href="StlcProp.html#11977" class="Function"
      >&#8709;&#8866;-closed&#8242;</a
      ><a name="12031"
      > </a
      ><a name="12032" class="Symbol"
      >{</a
      ><a name="12033" href="StlcProp.html#12033" class="Bound"
      >M</a
      ><a name="12034" class="Symbol"
      >}</a
      ><a name="12035"
      > </a
      ><a name="12036" class="Symbol"
      >{</a
      ><a name="12037" href="StlcProp.html#12037" class="Bound"
      >A</a
      ><a name="12038" class="Symbol"
      >}</a
      ><a name="12039"
      > </a
      ><a name="12040" href="StlcProp.html#12040" class="Bound"
      >&#8866;M</a
      ><a name="12042"
      > </a
      ><a name="12043" class="Symbol"
      >{</a
      ><a name="12044" href="StlcProp.html#12044" class="Bound"
      >x</a
      ><a name="12045" class="Symbol"
      >}</a
      ><a name="12046"
      > </a
      ><a name="12047" href="StlcProp.html#12047" class="Bound"
      >x&#8712;M</a
      ><a name="12050"
      > </a
      ><a name="12051" class="Keyword"
      >with</a
      ><a name="12055"
      > </a
      ><a name="12056" href="StlcProp.html#9447" class="Function"
      >free-lemma</a
      ><a name="12066"
      > </a
      ><a name="12067" href="StlcProp.html#12047" class="Bound"
      >x&#8712;M</a
      ><a name="12070"
      > </a
      ><a name="12071" href="StlcProp.html#12040" class="Bound"
      >&#8866;M</a
      ><a name="12073"
      >
</a
      ><a name="12074" class="Symbol"
      >...</a
      ><a name="12077"
      > </a
      ><a name="12078" class="Symbol"
      >|</a
      ><a name="12079"
      > </a
      ><a name="12080" class="Symbol"
      >(</a
      ><a name="12081" href="StlcProp.html#12081" class="Bound"
      >B</a
      ><a name="12082"
      > </a
      ><a name="12083" href="https://agda.github.io/agda-stdlib/Data.Product.html#509" class="InductiveConstructor Operator"
      >,</a
      ><a name="12084"
      > </a
      ><a name="12085" href="StlcProp.html#12085" class="Bound"
      >&#8709;x&#8801;B</a
      ><a name="12089" class="Symbol"
      >)</a
      ><a name="12090"
      > </a
      ><a name="12091" class="Symbol"
      >=</a
      ><a name="12092"
      > </a
      ><a name="12093" href="Maps.html#11818" class="Function"
      >just&#8802;nothing</a
      ><a name="12105"
      > </a
      ><a name="12106" class="Symbol"
      >(</a
      ><a name="12107" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.Core.html#632" class="Function"
      >trans</a
      ><a name="12112"
      > </a
      ><a name="12113" class="Symbol"
      >(</a
      ><a name="12114" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.Core.html#565" class="Function"
      >sym</a
      ><a name="12117"
      > </a
      ><a name="12118" href="StlcProp.html#12085" class="Bound"
      >&#8709;x&#8801;B</a
      ><a name="12122" class="Symbol"
      >)</a
      ><a name="12123"
      > </a
      ><a name="12124" class="Symbol"
      >(</a
      ><a name="12125" href="Maps.html#10573" class="Function"
      >apply-&#8709;</a
      ><a name="12132"
      > </a
      ><a name="12133" href="StlcProp.html#12044" class="Bound"
      >x</a
      ><a name="12134" class="Symbol"
      >))</a
      >

</pre>
</div>

Sometimes, when we have a proof `Γ ⊢ M ∶ A`, we will need to
replace `Γ` by a different context `Γ′`.  When is it safe
to do this?  Intuitively, the only variables we care about
in the context are those that appear free in `M`. So long
as the two contexts agree on those variables, one can be
exchanged for the other.

<pre class="Agda">

<a name="12488" href="StlcProp.html#12488" class="Function"
      >context-lemma</a
      ><a name="12501"
      > </a
      ><a name="12502" class="Symbol"
      >:</a
      ><a name="12503"
      > </a
      ><a name="12504" class="Symbol"
      >&#8704;</a
      ><a name="12505"
      > </a
      ><a name="12506" class="Symbol"
      >{</a
      ><a name="12507" href="StlcProp.html#12507" class="Bound"
      >&#915;</a
      ><a name="12508"
      > </a
      ><a name="12509" href="StlcProp.html#12509" class="Bound"
      >&#915;&#8242;</a
      ><a name="12511"
      > </a
      ><a name="12512" href="StlcProp.html#12512" class="Bound"
      >M</a
      ><a name="12513"
      > </a
      ><a name="12514" href="StlcProp.html#12514" class="Bound"
      >A</a
      ><a name="12515" class="Symbol"
      >}</a
      ><a name="12516"
      >
        </a
      ><a name="12525" class="Symbol"
      >&#8594;</a
      ><a name="12526"
      > </a
      ><a name="12527" class="Symbol"
      >(&#8704;</a
      ><a name="12529"
      > </a
      ><a name="12530" class="Symbol"
      >{</a
      ><a name="12531" href="StlcProp.html#12531" class="Bound"
      >x</a
      ><a name="12532" class="Symbol"
      >}</a
      ><a name="12533"
      > </a
      ><a name="12534" class="Symbol"
      >&#8594;</a
      ><a name="12535"
      > </a
      ><a name="12536" href="StlcProp.html#12531" class="Bound"
      >x</a
      ><a name="12537"
      > </a
      ><a name="12538" href="StlcProp.html#7750" class="Datatype Operator"
      >&#8712;</a
      ><a name="12539"
      > </a
      ><a name="12540" href="StlcProp.html#12512" class="Bound"
      >M</a
      ><a name="12541"
      > </a
      ><a name="12542" class="Symbol"
      >&#8594;</a
      ><a name="12543"
      > </a
      ><a name="12544" href="StlcProp.html#12507" class="Bound"
      >&#915;</a
      ><a name="12545"
      > </a
      ><a name="12546" href="StlcProp.html#12531" class="Bound"
      >x</a
      ><a name="12547"
      > </a
      ><a name="12548" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="12549"
      > </a
      ><a name="12550" href="StlcProp.html#12509" class="Bound"
      >&#915;&#8242;</a
      ><a name="12552"
      > </a
      ><a name="12553" href="StlcProp.html#12531" class="Bound"
      >x</a
      ><a name="12554" class="Symbol"
      >)</a
      ><a name="12555"
      >
        </a
      ><a name="12564" class="Symbol"
      >&#8594;</a
      ><a name="12565"
      > </a
      ><a name="12566" href="StlcProp.html#12507" class="Bound"
      >&#915;</a
      ><a name="12567"
      >  </a
      ><a name="12569" href="Stlc.html#21569" class="Datatype Operator"
      >&#8866;</a
      ><a name="12570"
      > </a
      ><a name="12571" href="StlcProp.html#12512" class="Bound"
      >M</a
      ><a name="12572"
      > </a
      ><a name="12573" href="Stlc.html#21569" class="Datatype Operator"
      >&#8758;</a
      ><a name="12574"
      > </a
      ><a name="12575" href="StlcProp.html#12514" class="Bound"
      >A</a
      ><a name="12576"
      >
        </a
      ><a name="12585" class="Symbol"
      >&#8594;</a
      ><a name="12586"
      > </a
      ><a name="12587" href="StlcProp.html#12509" class="Bound"
      >&#915;&#8242;</a
      ><a name="12589"
      > </a
      ><a name="12590" href="Stlc.html#21569" class="Datatype Operator"
      >&#8866;</a
      ><a name="12591"
      > </a
      ><a name="12592" href="StlcProp.html#12512" class="Bound"
      >M</a
      ><a name="12593"
      > </a
      ><a name="12594" href="Stlc.html#21569" class="Datatype Operator"
      >&#8758;</a
      ><a name="12595"
      > </a
      ><a name="12596" href="StlcProp.html#12514" class="Bound"
      >A</a
      >

</pre>

_Proof_: By induction on the derivation of `Γ ⊢ M ∶ A`.

  - If the last rule in the derivation was `Ax`, then `M = x`
    and `Γ x ≡ just A`.  By assumption, `Γ′ x = just A` as well, and
    hence `Γ′ ⊢ M : A` by `Ax`.

  - If the last rule was `⇒-I`, then `M = λ[ y : A] N`, with
    `A = A ⇒ B` and `Γ , y ∶ A ⊢ N ∶ B`.  The
    induction hypothesis is that, for any context `Γ″`, if
    `Γ , y : A` and `Γ″` assign the same types to all the
    free variables in `N`, then `N` has type `B` under
    `Γ″`.  Let `Γ′` be a context which agrees with
    `Γ` on the free variables in `N`; we must show
    `Γ′ ⊢ λ[ y ∶ A] N ∶ A ⇒ B`.

    By `⇒-I`, it suffices to show that `Γ′ , y:A ⊢ N ∶ B`.
    By the IH (setting `Γ″ = Γ′ , y : A`), it suffices to show
    that `Γ , y : A` and `Γ′ , y : A` agree on all the variables
    that appear free in `N`.

    Any variable occurring free in `N` must be either `y` or
    some other variable.  Clearly, `Γ , y : A` and `Γ′ , y : A`
    agree on `y`.  Otherwise, any variable other
    than `y` that occurs free in `N` also occurs free in
    `λ[ y : A] N`, and by assumption `Γ` and
    `Γ′` agree on all such variables; hence so do
    `Γ , y : A` and `Γ′ , y : A`.

  - If the last rule was `⇒-E`, then `M = L · M`, with `Γ ⊢ L ∶ A ⇒ B`
    and `Γ ⊢ M ∶ B`.  One induction hypothesis states that for all
    contexts `Γ′`, if `Γ′` agrees with `Γ` on the free variables in
    `L` then `L` has type `A ⇒ B` under `Γ′`; there is a similar IH
    for `M`.  We must show that `L · M` also has type `B` under `Γ′`,
    given the assumption that `Γ′` agrees with `Γ` on all the free
    variables in `L · M`.  By `⇒-E`, it suffices to show that `L` and
    `M` each have the same type under `Γ′` as under `Γ`.  But all free
    variables in `L` are also free in `L · M`; in the proof, this is
    expressed by composing `free-·₁ : ∀ {x} → x ∈ L → x ∈ L · M` with
    `Γ~Γ′ : (∀ {x} → x ∈ L · M → Γ x ≡ Γ′ x)` to yield `Γ~Γ′ ∘ free-·₁
    : ∀ {x} → x ∈ L → Γ x ≡ Γ′ x`.  Similarly for `M`; hence the
    desired result follows from the induction hypotheses.

  - The remaining cases are similar to `⇒-E`.

<pre class="Agda">

<a name="14769" href="StlcProp.html#12488" class="Function"
      >context-lemma</a
      ><a name="14782"
      > </a
      ><a name="14783" href="StlcProp.html#14783" class="Bound"
      >&#915;~&#915;&#8242;</a
      ><a name="14787"
      > </a
      ><a name="14788" class="Symbol"
      >(</a
      ><a name="14789" href="Stlc.html#21613" class="InductiveConstructor"
      >Ax</a
      ><a name="14791"
      > </a
      ><a name="14792" href="StlcProp.html#14792" class="Bound"
      >&#915;x&#8801;A</a
      ><a name="14796" class="Symbol"
      >)</a
      ><a name="14797"
      > </a
      ><a name="14798" class="Keyword"
      >rewrite</a
      ><a name="14805"
      > </a
      ><a name="14806" class="Symbol"
      >(</a
      ><a name="14807" href="StlcProp.html#14783" class="Bound"
      >&#915;~&#915;&#8242;</a
      ><a name="14811"
      > </a
      ><a name="14812" href="StlcProp.html#7780" class="InductiveConstructor"
      >free-`</a
      ><a name="14818" class="Symbol"
      >)</a
      ><a name="14819"
      > </a
      ><a name="14820" class="Symbol"
      >=</a
      ><a name="14821"
      > </a
      ><a name="14822" href="Stlc.html#21613" class="InductiveConstructor"
      >Ax</a
      ><a name="14824"
      > </a
      ><a name="14825" href="StlcProp.html#14792" class="Bound"
      >&#915;x&#8801;A</a
      ><a name="14829"
      >
</a
      ><a name="14830" href="StlcProp.html#12488" class="Function"
      >context-lemma</a
      ><a name="14843"
      > </a
      ><a name="14844" class="Symbol"
      >{</a
      ><a name="14845" href="StlcProp.html#14845" class="Bound"
      >&#915;</a
      ><a name="14846" class="Symbol"
      >}</a
      ><a name="14847"
      > </a
      ><a name="14848" class="Symbol"
      >{</a
      ><a name="14849" href="StlcProp.html#14849" class="Bound"
      >&#915;&#8242;</a
      ><a name="14851" class="Symbol"
      >}</a
      ><a name="14852"
      > </a
      ><a name="14853" class="Symbol"
      >{</a
      ><a name="14854" href="Stlc.html#3672" class="InductiveConstructor Operator"
      >&#955;[</a
      ><a name="14856"
      > </a
      ><a name="14857" href="StlcProp.html#14857" class="Bound"
      >x</a
      ><a name="14858"
      > </a
      ><a name="14859" href="Stlc.html#3672" class="InductiveConstructor Operator"
      >&#8758;</a
      ><a name="14860"
      > </a
      ><a name="14861" href="StlcProp.html#14861" class="Bound"
      >A</a
      ><a name="14862"
      > </a
      ><a name="14863" href="Stlc.html#3672" class="InductiveConstructor Operator"
      >]</a
      ><a name="14864"
      > </a
      ><a name="14865" href="StlcProp.html#14865" class="Bound"
      >N</a
      ><a name="14866" class="Symbol"
      >}</a
      ><a name="14867"
      > </a
      ><a name="14868" href="StlcProp.html#14868" class="Bound"
      >&#915;~&#915;&#8242;</a
      ><a name="14872"
      > </a
      ><a name="14873" class="Symbol"
      >(</a
      ><a name="14874" href="Stlc.html#21667" class="InductiveConstructor"
      >&#8658;-I</a
      ><a name="14877"
      > </a
      ><a name="14878" href="StlcProp.html#14878" class="Bound"
      >&#8866;N</a
      ><a name="14880" class="Symbol"
      >)</a
      ><a name="14881"
      > </a
      ><a name="14882" class="Symbol"
      >=</a
      ><a name="14883"
      > </a
      ><a name="14884" href="Stlc.html#21667" class="InductiveConstructor"
      >&#8658;-I</a
      ><a name="14887"
      > </a
      ><a name="14888" class="Symbol"
      >(</a
      ><a name="14889" href="StlcProp.html#12488" class="Function"
      >context-lemma</a
      ><a name="14902"
      > </a
      ><a name="14903" href="StlcProp.html#14924" class="Function"
      >&#915;x~&#915;&#8242;x</a
      ><a name="14909"
      > </a
      ><a name="14910" href="StlcProp.html#14878" class="Bound"
      >&#8866;N</a
      ><a name="14912" class="Symbol"
      >)</a
      ><a name="14913"
      >
  </a
      ><a name="14916" class="Keyword"
      >where</a
      ><a name="14921"
      >
  </a
      ><a name="14924" href="StlcProp.html#14924" class="Function"
      >&#915;x~&#915;&#8242;x</a
      ><a name="14930"
      > </a
      ><a name="14931" class="Symbol"
      >:</a
      ><a name="14932"
      > </a
      ><a name="14933" class="Symbol"
      >&#8704;</a
      ><a name="14934"
      > </a
      ><a name="14935" class="Symbol"
      >{</a
      ><a name="14936" href="StlcProp.html#14936" class="Bound"
      >y</a
      ><a name="14937" class="Symbol"
      >}</a
      ><a name="14938"
      > </a
      ><a name="14939" class="Symbol"
      >&#8594;</a
      ><a name="14940"
      > </a
      ><a name="14941" href="StlcProp.html#14936" class="Bound"
      >y</a
      ><a name="14942"
      > </a
      ><a name="14943" href="StlcProp.html#7750" class="Datatype Operator"
      >&#8712;</a
      ><a name="14944"
      > </a
      ><a name="14945" href="StlcProp.html#14865" class="Bound"
      >N</a
      ><a name="14946"
      > </a
      ><a name="14947" class="Symbol"
      >&#8594;</a
      ><a name="14948"
      > </a
      ><a name="14949" class="Symbol"
      >(</a
      ><a name="14950" href="StlcProp.html#14845" class="Bound"
      >&#915;</a
      ><a name="14951"
      > </a
      ><a name="14952" href="Maps.html#10368" class="Function Operator"
      >,</a
      ><a name="14953"
      > </a
      ><a name="14954" href="StlcProp.html#14857" class="Bound"
      >x</a
      ><a name="14955"
      > </a
      ><a name="14956" href="Maps.html#10368" class="Function Operator"
      >&#8758;</a
      ><a name="14957"
      > </a
      ><a name="14958" href="StlcProp.html#14861" class="Bound"
      >A</a
      ><a name="14959" class="Symbol"
      >)</a
      ><a name="14960"
      > </a
      ><a name="14961" href="StlcProp.html#14936" class="Bound"
      >y</a
      ><a name="14962"
      > </a
      ><a name="14963" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="14964"
      > </a
      ><a name="14965" class="Symbol"
      >(</a
      ><a name="14966" href="StlcProp.html#14849" class="Bound"
      >&#915;&#8242;</a
      ><a name="14968"
      > </a
      ><a name="14969" href="Maps.html#10368" class="Function Operator"
      >,</a
      ><a name="14970"
      > </a
      ><a name="14971" href="StlcProp.html#14857" class="Bound"
      >x</a
      ><a name="14972"
      > </a
      ><a name="14973" href="Maps.html#10368" class="Function Operator"
      >&#8758;</a
      ><a name="14974"
      > </a
      ><a name="14975" href="StlcProp.html#14861" class="Bound"
      >A</a
      ><a name="14976" class="Symbol"
      >)</a
      ><a name="14977"
      > </a
      ><a name="14978" href="StlcProp.html#14936" class="Bound"
      >y</a
      ><a name="14979"
      >
  </a
      ><a name="14982" href="StlcProp.html#14924" class="Function"
      >&#915;x~&#915;&#8242;x</a
      ><a name="14988"
      > </a
      ><a name="14989" class="Symbol"
      >{</a
      ><a name="14990" href="StlcProp.html#14990" class="Bound"
      >y</a
      ><a name="14991" class="Symbol"
      >}</a
      ><a name="14992"
      > </a
      ><a name="14993" href="StlcProp.html#14993" class="Bound"
      >y&#8712;N</a
      ><a name="14996"
      > </a
      ><a name="14997" class="Keyword"
      >with</a
      ><a name="15001"
      > </a
      ><a name="15002" href="StlcProp.html#14857" class="Bound"
      >x</a
      ><a name="15003"
      > </a
      ><a name="15004" href="Maps.html#2509" class="Function Operator"
      >&#8799;</a
      ><a name="15005"
      > </a
      ><a name="15006" href="StlcProp.html#14990" class="Bound"
      >y</a
      ><a name="15007"
      >
  </a
      ><a name="15010" class="Symbol"
      >...</a
      ><a name="15013"
      > </a
      ><a name="15014" class="Symbol"
      >|</a
      ><a name="15015"
      > </a
      ><a name="15016" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#520" class="InductiveConstructor"
      >yes</a
      ><a name="15019"
      > </a
      ><a name="15020" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="15024"
      > </a
      ><a name="15025" class="Symbol"
      >=</a
      ><a name="15026"
      > </a
      ><a name="15027" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="15031"
      >
  </a
      ><a name="15034" class="Symbol"
      >...</a
      ><a name="15037"
      > </a
      ><a name="15038" class="Symbol"
      >|</a
      ><a name="15039"
      > </a
      ><a name="15040" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#547" class="InductiveConstructor"
      >no</a
      ><a name="15042"
      >  </a
      ><a name="15044" href="StlcProp.html#15044" class="Bound"
      >x&#8802;y</a
      ><a name="15047"
      >  </a
      ><a name="15049" class="Symbol"
      >=</a
      ><a name="15050"
      > </a
      ><a name="15051" href="StlcProp.html#14868" class="Bound"
      >&#915;~&#915;&#8242;</a
      ><a name="15055"
      > </a
      ><a name="15056" class="Symbol"
      >(</a
      ><a name="15057" href="StlcProp.html#7808" class="InductiveConstructor"
      >free-&#955;</a
      ><a name="15063"
      > </a
      ><a name="15064" href="StlcProp.html#15044" class="Bound"
      >x&#8802;y</a
      ><a name="15067"
      > </a
      ><a name="15068" href="StlcProp.html#14993" class="Bound"
      >y&#8712;N</a
      ><a name="15071" class="Symbol"
      >)</a
      ><a name="15072"
      >
</a
      ><a name="15073" href="StlcProp.html#12488" class="Function"
      >context-lemma</a
      ><a name="15086"
      > </a
      ><a name="15087" href="StlcProp.html#15087" class="Bound"
      >&#915;~&#915;&#8242;</a
      ><a name="15091"
      > </a
      ><a name="15092" class="Symbol"
      >(</a
      ><a name="15093" href="Stlc.html#21744" class="InductiveConstructor"
      >&#8658;-E</a
      ><a name="15096"
      > </a
      ><a name="15097" href="StlcProp.html#15097" class="Bound"
      >&#8866;L</a
      ><a name="15099"
      > </a
      ><a name="15100" href="StlcProp.html#15100" class="Bound"
      >&#8866;M</a
      ><a name="15102" class="Symbol"
      >)</a
      ><a name="15103"
      > </a
      ><a name="15104" class="Symbol"
      >=</a
      ><a name="15105"
      > </a
      ><a name="15106" href="Stlc.html#21744" class="InductiveConstructor"
      >&#8658;-E</a
      ><a name="15109"
      > </a
      ><a name="15110" class="Symbol"
      >(</a
      ><a name="15111" href="StlcProp.html#12488" class="Function"
      >context-lemma</a
      ><a name="15124"
      > </a
      ><a name="15125" class="Symbol"
      >(</a
      ><a name="15126" href="StlcProp.html#15087" class="Bound"
      >&#915;~&#915;&#8242;</a
      ><a name="15130"
      > </a
      ><a name="15131" href="https://agda.github.io/agda-stdlib/Function.html#713" class="Function Operator"
      >&#8728;</a
      ><a name="15132"
      > </a
      ><a name="15133" href="StlcProp.html#7869" class="InductiveConstructor"
      >free-&#183;&#8321;</a
      ><a name="15140" class="Symbol"
      >)</a
      ><a name="15141"
      >  </a
      ><a name="15143" href="StlcProp.html#15097" class="Bound"
      >&#8866;L</a
      ><a name="15145" class="Symbol"
      >)</a
      ><a name="15146"
      >
                                       </a
      ><a name="15186" class="Symbol"
      >(</a
      ><a name="15187" href="StlcProp.html#12488" class="Function"
      >context-lemma</a
      ><a name="15200"
      > </a
      ><a name="15201" class="Symbol"
      >(</a
      ><a name="15202" href="StlcProp.html#15087" class="Bound"
      >&#915;~&#915;&#8242;</a
      ><a name="15206"
      > </a
      ><a name="15207" href="https://agda.github.io/agda-stdlib/Function.html#713" class="Function Operator"
      >&#8728;</a
      ><a name="15208"
      > </a
      ><a name="15209" href="StlcProp.html#7913" class="InductiveConstructor"
      >free-&#183;&#8322;</a
      ><a name="15216" class="Symbol"
      >)</a
      ><a name="15217"
      > </a
      ><a name="15218" href="StlcProp.html#15100" class="Bound"
      >&#8866;M</a
      ><a name="15220" class="Symbol"
      >)</a
      ><a name="15221"
      > 
</a
      ><a name="15223" href="StlcProp.html#12488" class="Function"
      >context-lemma</a
      ><a name="15236"
      > </a
      ><a name="15237" href="StlcProp.html#15237" class="Bound"
      >&#915;~&#915;&#8242;</a
      ><a name="15241"
      > </a
      ><a name="15242" href="Stlc.html#21822" class="InductiveConstructor"
      >&#120121;-I&#8321;</a
      ><a name="15246"
      > </a
      ><a name="15247" class="Symbol"
      >=</a
      ><a name="15248"
      > </a
      ><a name="15249" href="Stlc.html#21822" class="InductiveConstructor"
      >&#120121;-I&#8321;</a
      ><a name="15253"
      >
</a
      ><a name="15254" href="StlcProp.html#12488" class="Function"
      >context-lemma</a
      ><a name="15267"
      > </a
      ><a name="15268" href="StlcProp.html#15268" class="Bound"
      >&#915;~&#915;&#8242;</a
      ><a name="15272"
      > </a
      ><a name="15273" href="Stlc.html#21856" class="InductiveConstructor"
      >&#120121;-I&#8322;</a
      ><a name="15277"
      > </a
      ><a name="15278" class="Symbol"
      >=</a
      ><a name="15279"
      > </a
      ><a name="15280" href="Stlc.html#21856" class="InductiveConstructor"
      >&#120121;-I&#8322;</a
      ><a name="15284"
      >
</a
      ><a name="15285" href="StlcProp.html#12488" class="Function"
      >context-lemma</a
      ><a name="15298"
      > </a
      ><a name="15299" href="StlcProp.html#15299" class="Bound"
      >&#915;~&#915;&#8242;</a
      ><a name="15303"
      > </a
      ><a name="15304" class="Symbol"
      >(</a
      ><a name="15305" href="Stlc.html#21891" class="InductiveConstructor"
      >&#120121;-E</a
      ><a name="15308"
      > </a
      ><a name="15309" href="StlcProp.html#15309" class="Bound"
      >&#8866;L</a
      ><a name="15311"
      > </a
      ><a name="15312" href="StlcProp.html#15312" class="Bound"
      >&#8866;M</a
      ><a name="15314"
      > </a
      ><a name="15315" href="StlcProp.html#15315" class="Bound"
      >&#8866;N</a
      ><a name="15317" class="Symbol"
      >)</a
      ><a name="15318"
      > </a
      ><a name="15319" class="Symbol"
      >=</a
      ><a name="15320"
      > </a
      ><a name="15321" href="Stlc.html#21891" class="InductiveConstructor"
      >&#120121;-E</a
      ><a name="15324"
      > </a
      ><a name="15325" class="Symbol"
      >(</a
      ><a name="15326" href="StlcProp.html#12488" class="Function"
      >context-lemma</a
      ><a name="15339"
      > </a
      ><a name="15340" class="Symbol"
      >(</a
      ><a name="15341" href="StlcProp.html#15299" class="Bound"
      >&#915;~&#915;&#8242;</a
      ><a name="15345"
      > </a
      ><a name="15346" href="https://agda.github.io/agda-stdlib/Function.html#713" class="Function Operator"
      >&#8728;</a
      ><a name="15347"
      > </a
      ><a name="15348" href="StlcProp.html#7957" class="InductiveConstructor"
      >free-if&#8321;</a
      ><a name="15356" class="Symbol"
      >)</a
      ><a name="15357"
      > </a
      ><a name="15358" href="StlcProp.html#15309" class="Bound"
      >&#8866;L</a
      ><a name="15360" class="Symbol"
      >)</a
      ><a name="15361"
      >
                                         </a
      ><a name="15403" class="Symbol"
      >(</a
      ><a name="15404" href="StlcProp.html#12488" class="Function"
      >context-lemma</a
      ><a name="15417"
      > </a
      ><a name="15418" class="Symbol"
      >(</a
      ><a name="15419" href="StlcProp.html#15299" class="Bound"
      >&#915;~&#915;&#8242;</a
      ><a name="15423"
      > </a
      ><a name="15424" href="https://agda.github.io/agda-stdlib/Function.html#713" class="Function Operator"
      >&#8728;</a
      ><a name="15425"
      > </a
      ><a name="15426" href="StlcProp.html#8017" class="InductiveConstructor"
      >free-if&#8322;</a
      ><a name="15434" class="Symbol"
      >)</a
      ><a name="15435"
      > </a
      ><a name="15436" href="StlcProp.html#15312" class="Bound"
      >&#8866;M</a
      ><a name="15438" class="Symbol"
      >)</a
      ><a name="15439"
      >
                                         </a
      ><a name="15481" class="Symbol"
      >(</a
      ><a name="15482" href="StlcProp.html#12488" class="Function"
      >context-lemma</a
      ><a name="15495"
      > </a
      ><a name="15496" class="Symbol"
      >(</a
      ><a name="15497" href="StlcProp.html#15299" class="Bound"
      >&#915;~&#915;&#8242;</a
      ><a name="15501"
      > </a
      ><a name="15502" href="https://agda.github.io/agda-stdlib/Function.html#713" class="Function Operator"
      >&#8728;</a
      ><a name="15503"
      > </a
      ><a name="15504" href="StlcProp.html#8077" class="InductiveConstructor"
      >free-if&#8323;</a
      ><a name="15512" class="Symbol"
      >)</a
      ><a name="15513"
      > </a
      ><a name="15514" href="StlcProp.html#15315" class="Bound"
      >&#8866;N</a
      ><a name="15516" class="Symbol"
      >)</a
      >

</pre>


Now we come to the conceptual heart of the proof that reduction
preserves types---namely, the observation that _substitution_
preserves types.

Formally, the _Substitution Lemma_ says this: Suppose we
have a term `N` with a free variable `x`, where `N` has
type `B` under the assumption that `x` has some type `A`.
Also, suppose that we have some other term `V`,
where `V` has type `A`.  Then, since `V` satisfies
the assumption we made about `x` when typing `N`, we should be
able to substitute `V` for each of the occurrences of `x` in `N`
and obtain a new term that still has type `B`.

_Lemma_: If `Γ , x ∶ A ⊢ N ∶ B` and `∅ ⊢ V ∶ A`, then
`Γ ⊢ (N [ x := V ]) ∶ B`.

<pre class="Agda">

<a name="16215" href="StlcProp.html#16215" class="Function"
      >preservation-[:=]</a
      ><a name="16232"
      > </a
      ><a name="16233" class="Symbol"
      >:</a
      ><a name="16234"
      > </a
      ><a name="16235" class="Symbol"
      >&#8704;</a
      ><a name="16236"
      > </a
      ><a name="16237" class="Symbol"
      >{</a
      ><a name="16238" href="StlcProp.html#16238" class="Bound"
      >&#915;</a
      ><a name="16239"
      > </a
      ><a name="16240" href="StlcProp.html#16240" class="Bound"
      >x</a
      ><a name="16241"
      > </a
      ><a name="16242" href="StlcProp.html#16242" class="Bound"
      >A</a
      ><a name="16243"
      > </a
      ><a name="16244" href="StlcProp.html#16244" class="Bound"
      >N</a
      ><a name="16245"
      > </a
      ><a name="16246" href="StlcProp.html#16246" class="Bound"
      >B</a
      ><a name="16247"
      > </a
      ><a name="16248" href="StlcProp.html#16248" class="Bound"
      >V</a
      ><a name="16249" class="Symbol"
      >}</a
      ><a name="16250"
      >
                 </a
      ><a name="16268" class="Symbol"
      >&#8594;</a
      ><a name="16269"
      > </a
      ><a name="16270" class="Symbol"
      >(</a
      ><a name="16271" href="StlcProp.html#16238" class="Bound"
      >&#915;</a
      ><a name="16272"
      > </a
      ><a name="16273" href="Maps.html#10368" class="Function Operator"
      >,</a
      ><a name="16274"
      > </a
      ><a name="16275" href="StlcProp.html#16240" class="Bound"
      >x</a
      ><a name="16276"
      > </a
      ><a name="16277" href="Maps.html#10368" class="Function Operator"
      >&#8758;</a
      ><a name="16278"
      > </a
      ><a name="16279" href="StlcProp.html#16242" class="Bound"
      >A</a
      ><a name="16280" class="Symbol"
      >)</a
      ><a name="16281"
      > </a
      ><a name="16282" href="Stlc.html#21569" class="Datatype Operator"
      >&#8866;</a
      ><a name="16283"
      > </a
      ><a name="16284" href="StlcProp.html#16244" class="Bound"
      >N</a
      ><a name="16285"
      > </a
      ><a name="16286" href="Stlc.html#21569" class="Datatype Operator"
      >&#8758;</a
      ><a name="16287"
      > </a
      ><a name="16288" href="StlcProp.html#16246" class="Bound"
      >B</a
      ><a name="16289"
      >
                 </a
      ><a name="16307" class="Symbol"
      >&#8594;</a
      ><a name="16308"
      > </a
      ><a name="16309" href="Maps.html#10265" class="Function"
      >&#8709;</a
      ><a name="16310"
      > </a
      ><a name="16311" href="Stlc.html#21569" class="Datatype Operator"
      >&#8866;</a
      ><a name="16312"
      > </a
      ><a name="16313" href="StlcProp.html#16248" class="Bound"
      >V</a
      ><a name="16314"
      > </a
      ><a name="16315" href="Stlc.html#21569" class="Datatype Operator"
      >&#8758;</a
      ><a name="16316"
      > </a
      ><a name="16317" href="StlcProp.html#16242" class="Bound"
      >A</a
      ><a name="16318"
      >
                 </a
      ><a name="16336" class="Symbol"
      >&#8594;</a
      ><a name="16337"
      > </a
      ><a name="16338" href="StlcProp.html#16238" class="Bound"
      >&#915;</a
      ><a name="16339"
      > </a
      ><a name="16340" href="Stlc.html#21569" class="Datatype Operator"
      >&#8866;</a
      ><a name="16341"
      > </a
      ><a name="16342" class="Symbol"
      >(</a
      ><a name="16343" href="StlcProp.html#16244" class="Bound"
      >N</a
      ><a name="16344"
      > </a
      ><a name="16345" href="Stlc.html#12079" class="Function Operator"
      >[</a
      ><a name="16346"
      > </a
      ><a name="16347" href="StlcProp.html#16240" class="Bound"
      >x</a
      ><a name="16348"
      > </a
      ><a name="16349" href="Stlc.html#12079" class="Function Operator"
      >:=</a
      ><a name="16351"
      > </a
      ><a name="16352" href="StlcProp.html#16248" class="Bound"
      >V</a
      ><a name="16353"
      > </a
      ><a name="16354" href="Stlc.html#12079" class="Function Operator"
      >]</a
      ><a name="16355" class="Symbol"
      >)</a
      ><a name="16356"
      > </a
      ><a name="16357" href="Stlc.html#21569" class="Datatype Operator"
      >&#8758;</a
      ><a name="16358"
      > </a
      ><a name="16359" href="StlcProp.html#16246" class="Bound"
      >B</a
      >

</pre>

One technical subtlety in the statement of the lemma is that we assume
`V` is closed; it has type `A` in the _empty_ context.  This
assumption simplifies the `λ` case of the proof because the context
invariance lemma then tells us that `V` has type `A` in any context at
all---we don't have to worry about free variables in `V` clashing with
the variable being introduced into the context by `λ`. It is possible
to prove the theorem under the more general assumption `Γ ⊢ V ∶ A`,
but the proof is more difficult.

<!--
Intuitively, the substitution lemma says that substitution and typing can
be done in either order: we can either assign types to the terms
`N` and `V` separately (under suitable contexts) and then combine
them using substitution, or we can substitute first and then
assign a type to `N [ x := V ]`---the result is the same either
way.
-->

_Proof_:  By induction on the derivation of `Γ , x ∶ A ⊢ N ∶ B`,
we show that if `∅ ⊢ V ∶ A` then `Γ ⊢ N [ x := V ] ∶ B`.

  - If `N` is a variable there are two cases to consider,
    depending on whether `N` is `x` or some other variable.

      - If `N = `` `x ``, then from `Γ , x ∶ A ⊢ x ∶ B`
        we know that looking up `x` in `Γ , x : A` gives
        `just B`, but we already know it gives `just A`;
        applying injectivity for `just` we conclude that `A ≡ B`.
        We must show that `x [ x := V] = V`
        has type `A` under `Γ`, given the assumption that
        `V` has type `A` under the empty context.  This
        follows from context invariance: if a closed term has type
        `A` in the empty context, it has that type in any context.

      - If `N` is some variable `x′` different from `x`, then
        we need only note that `x′` has the same type under `Γ , x ∶ A`
        as under `Γ`.

  - If `N` is an abstraction `λ[ x′ ∶ A′ ] N′`, then the IH tells us,
    for all `Γ′`́ and `B′`, that if `Γ′ , x ∶ A ⊢ N′ ∶ B′`
    and `∅ ⊢ V ∶ A`, then `Γ′ ⊢ N′ [ x := V ] ∶ B′`.

    The substitution in the conclusion behaves differently
    depending on whether `x` and `x′` are the same variable.

    First, suppose `x ≡ x′`.  Then, by the definition of
    substitution, `N [ x := V] = N`, so we just need to show `Γ ⊢ N ∶ B`.
    But we know `Γ , x ∶ A ⊢ N ∶ B` and, since `x ≡ x′`
    does not appear free in `λ[ x′ ∶ A′ ] N′`, the context invariance
    lemma yields `Γ ⊢ N ∶ B`.

    Second, suppose `x ≢ x′`.  We know `Γ , x ∶ A , x′ ∶ A′ ⊢ N′ ∶ B′`
    by inversion of the typing relation, from which
    `Γ , x′ ∶ A′ , x ∶ A ⊢ N′ ∶ B′` follows by update permute,
    so the IH applies, giving us `Γ , x′ ∶ A′ ⊢ N′ [ x := V ] ∶ B′`
    By `⇒-I`, we have `Γ ⊢ λ[ x′ ∶ A′ ] (N′ [ x := V ]) ∶ A′ ⇒ B′`
    and the definition of substitution (noting `x ≢ x′`) gives
    `Γ ⊢ (λ[ x′ ∶ A′ ] N′) [ x := V ] ∶ A′ ⇒ B′` as required.

  - If `N` is an application `L′ · M′`, the result follows
    straightforwardly from the definition of substitution and the
    induction hypotheses.

  - The remaining cases are similar to application.

We need a couple of lemmas. A closed term can be weakened to any context, and `just` is injective.
<pre class="Agda">

<a name="19516" href="StlcProp.html#19516" class="Function"
      >weaken-closed</a
      ><a name="19529"
      > </a
      ><a name="19530" class="Symbol"
      >:</a
      ><a name="19531"
      > </a
      ><a name="19532" class="Symbol"
      >&#8704;</a
      ><a name="19533"
      > </a
      ><a name="19534" class="Symbol"
      >{</a
      ><a name="19535" href="StlcProp.html#19535" class="Bound"
      >V</a
      ><a name="19536"
      > </a
      ><a name="19537" href="StlcProp.html#19537" class="Bound"
      >A</a
      ><a name="19538"
      > </a
      ><a name="19539" href="StlcProp.html#19539" class="Bound"
      >&#915;</a
      ><a name="19540" class="Symbol"
      >}</a
      ><a name="19541"
      > </a
      ><a name="19542" class="Symbol"
      >&#8594;</a
      ><a name="19543"
      > </a
      ><a name="19544" href="Maps.html#10265" class="Function"
      >&#8709;</a
      ><a name="19545"
      > </a
      ><a name="19546" href="Stlc.html#21569" class="Datatype Operator"
      >&#8866;</a
      ><a name="19547"
      > </a
      ><a name="19548" href="StlcProp.html#19535" class="Bound"
      >V</a
      ><a name="19549"
      > </a
      ><a name="19550" href="Stlc.html#21569" class="Datatype Operator"
      >&#8758;</a
      ><a name="19551"
      > </a
      ><a name="19552" href="StlcProp.html#19537" class="Bound"
      >A</a
      ><a name="19553"
      > </a
      ><a name="19554" class="Symbol"
      >&#8594;</a
      ><a name="19555"
      > </a
      ><a name="19556" href="StlcProp.html#19539" class="Bound"
      >&#915;</a
      ><a name="19557"
      > </a
      ><a name="19558" href="Stlc.html#21569" class="Datatype Operator"
      >&#8866;</a
      ><a name="19559"
      > </a
      ><a name="19560" href="StlcProp.html#19535" class="Bound"
      >V</a
      ><a name="19561"
      > </a
      ><a name="19562" href="Stlc.html#21569" class="Datatype Operator"
      >&#8758;</a
      ><a name="19563"
      > </a
      ><a name="19564" href="StlcProp.html#19537" class="Bound"
      >A</a
      ><a name="19565"
      >
</a
      ><a name="19566" href="StlcProp.html#19516" class="Function"
      >weaken-closed</a
      ><a name="19579"
      > </a
      ><a name="19580" class="Symbol"
      >{</a
      ><a name="19581" href="StlcProp.html#19581" class="Bound"
      >V</a
      ><a name="19582" class="Symbol"
      >}</a
      ><a name="19583"
      > </a
      ><a name="19584" class="Symbol"
      >{</a
      ><a name="19585" href="StlcProp.html#19585" class="Bound"
      >A</a
      ><a name="19586" class="Symbol"
      >}</a
      ><a name="19587"
      > </a
      ><a name="19588" class="Symbol"
      >{</a
      ><a name="19589" href="StlcProp.html#19589" class="Bound"
      >&#915;</a
      ><a name="19590" class="Symbol"
      >}</a
      ><a name="19591"
      > </a
      ><a name="19592" href="StlcProp.html#19592" class="Bound"
      >&#8866;V</a
      ><a name="19594"
      > </a
      ><a name="19595" class="Symbol"
      >=</a
      ><a name="19596"
      > </a
      ><a name="19597" href="StlcProp.html#12488" class="Function"
      >context-lemma</a
      ><a name="19610"
      > </a
      ><a name="19611" href="StlcProp.html#19629" class="Function"
      >&#915;~&#915;&#8242;</a
      ><a name="19615"
      > </a
      ><a name="19616" href="StlcProp.html#19592" class="Bound"
      >&#8866;V</a
      ><a name="19618"
      >
  </a
      ><a name="19621" class="Keyword"
      >where</a
      ><a name="19626"
      >
  </a
      ><a name="19629" href="StlcProp.html#19629" class="Function"
      >&#915;~&#915;&#8242;</a
      ><a name="19633"
      > </a
      ><a name="19634" class="Symbol"
      >:</a
      ><a name="19635"
      > </a
      ><a name="19636" class="Symbol"
      >&#8704;</a
      ><a name="19637"
      > </a
      ><a name="19638" class="Symbol"
      >{</a
      ><a name="19639" href="StlcProp.html#19639" class="Bound"
      >x</a
      ><a name="19640" class="Symbol"
      >}</a
      ><a name="19641"
      > </a
      ><a name="19642" class="Symbol"
      >&#8594;</a
      ><a name="19643"
      > </a
      ><a name="19644" href="StlcProp.html#19639" class="Bound"
      >x</a
      ><a name="19645"
      > </a
      ><a name="19646" href="StlcProp.html#7750" class="Datatype Operator"
      >&#8712;</a
      ><a name="19647"
      > </a
      ><a name="19648" href="StlcProp.html#19581" class="Bound"
      >V</a
      ><a name="19649"
      > </a
      ><a name="19650" class="Symbol"
      >&#8594;</a
      ><a name="19651"
      > </a
      ><a name="19652" href="Maps.html#10265" class="Function"
      >&#8709;</a
      ><a name="19653"
      > </a
      ><a name="19654" href="StlcProp.html#19639" class="Bound"
      >x</a
      ><a name="19655"
      > </a
      ><a name="19656" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="19657"
      > </a
      ><a name="19658" href="StlcProp.html#19589" class="Bound"
      >&#915;</a
      ><a name="19659"
      > </a
      ><a name="19660" href="StlcProp.html#19639" class="Bound"
      >x</a
      ><a name="19661"
      >
  </a
      ><a name="19664" href="StlcProp.html#19629" class="Function"
      >&#915;~&#915;&#8242;</a
      ><a name="19668"
      > </a
      ><a name="19669" class="Symbol"
      >{</a
      ><a name="19670" href="StlcProp.html#19670" class="Bound"
      >x</a
      ><a name="19671" class="Symbol"
      >}</a
      ><a name="19672"
      > </a
      ><a name="19673" href="StlcProp.html#19673" class="Bound"
      >x&#8712;V</a
      ><a name="19676"
      > </a
      ><a name="19677" class="Symbol"
      >=</a
      ><a name="19678"
      > </a
      ><a name="19679" href="https://agda.github.io/agda-stdlib/Data.Empty.html#348" class="Function"
      >&#8869;-elim</a
      ><a name="19685"
      > </a
      ><a name="19686" class="Symbol"
      >(</a
      ><a name="19687" href="StlcProp.html#19710" class="Function"
      >x&#8713;V</a
      ><a name="19690"
      > </a
      ><a name="19691" href="StlcProp.html#19673" class="Bound"
      >x&#8712;V</a
      ><a name="19694" class="Symbol"
      >)</a
      ><a name="19695"
      >
    </a
      ><a name="19700" class="Keyword"
      >where</a
      ><a name="19705"
      >
    </a
      ><a name="19710" href="StlcProp.html#19710" class="Function"
      >x&#8713;V</a
      ><a name="19713"
      > </a
      ><a name="19714" class="Symbol"
      >:</a
      ><a name="19715"
      > </a
      ><a name="19716" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#414" class="Function Operator"
      >&#172;</a
      ><a name="19717"
      > </a
      ><a name="19718" class="Symbol"
      >(</a
      ><a name="19719" href="StlcProp.html#19670" class="Bound"
      >x</a
      ><a name="19720"
      > </a
      ><a name="19721" href="StlcProp.html#7750" class="Datatype Operator"
      >&#8712;</a
      ><a name="19722"
      > </a
      ><a name="19723" href="StlcProp.html#19581" class="Bound"
      >V</a
      ><a name="19724" class="Symbol"
      >)</a
      ><a name="19725"
      >
    </a
      ><a name="19730" href="StlcProp.html#19710" class="Function"
      >x&#8713;V</a
      ><a name="19733"
      > </a
      ><a name="19734" class="Symbol"
      >=</a
      ><a name="19735"
      > </a
      ><a name="19736" href="StlcProp.html#11888" class="Postulate"
      >&#8709;&#8866;-closed</a
      ><a name="19745"
      > </a
      ><a name="19746" href="StlcProp.html#19592" class="Bound"
      >&#8866;V</a
      ><a name="19748"
      > </a
      ><a name="19749" class="Symbol"
      >{</a
      ><a name="19750" href="StlcProp.html#19670" class="Bound"
      >x</a
      ><a name="19751" class="Symbol"
      >}</a
      >

</pre>

<pre class="Agda">

<a name="19779" href="StlcProp.html#16215" class="Function"
      >preservation-[:=]</a
      ><a name="19796"
      > </a
      ><a name="19797" class="Symbol"
      >{</a
      ><a name="19798" href="StlcProp.html#19798" class="Bound"
      >&#915;</a
      ><a name="19799" class="Symbol"
      >}</a
      ><a name="19800"
      > </a
      ><a name="19801" class="Symbol"
      >{</a
      ><a name="19802" href="StlcProp.html#19802" class="Bound"
      >x</a
      ><a name="19803" class="Symbol"
      >}</a
      ><a name="19804"
      > </a
      ><a name="19805" class="Symbol"
      >{</a
      ><a name="19806" href="StlcProp.html#19806" class="Bound"
      >A</a
      ><a name="19807" class="Symbol"
      >}</a
      ><a name="19808"
      > </a
      ><a name="19809" class="Symbol"
      >(</a
      ><a name="19810" href="Stlc.html#21613" class="InductiveConstructor"
      >Ax</a
      ><a name="19812"
      > </a
      ><a name="19813" class="Symbol"
      >{</a
      ><a name="19814" href="StlcProp.html#19814" class="Bound"
      >&#915;,x&#8758;A</a
      ><a name="19819" class="Symbol"
      >}</a
      ><a name="19820"
      > </a
      ><a name="19821" class="Symbol"
      >{</a
      ><a name="19822" href="StlcProp.html#19822" class="Bound"
      >x&#8242;</a
      ><a name="19824" class="Symbol"
      >}</a
      ><a name="19825"
      > </a
      ><a name="19826" class="Symbol"
      >{</a
      ><a name="19827" href="StlcProp.html#19827" class="Bound"
      >B</a
      ><a name="19828" class="Symbol"
      >}</a
      ><a name="19829"
      > </a
      ><a name="19830" href="StlcProp.html#19830" class="Bound"
      >[&#915;,x&#8758;A]x&#8242;&#8801;B</a
      ><a name="19841" class="Symbol"
      >)</a
      ><a name="19842"
      > </a
      ><a name="19843" href="StlcProp.html#19843" class="Bound"
      >&#8866;V</a
      ><a name="19845"
      > </a
      ><a name="19846" class="Keyword"
      >with</a
      ><a name="19850"
      > </a
      ><a name="19851" href="StlcProp.html#19802" class="Bound"
      >x</a
      ><a name="19852"
      > </a
      ><a name="19853" href="Maps.html#2509" class="Function Operator"
      >&#8799;</a
      ><a name="19854"
      > </a
      ><a name="19855" href="StlcProp.html#19822" class="Bound"
      >x&#8242;</a
      ><a name="19857"
      >
</a
      ><a name="19858" class="Symbol"
      >...|</a
      ><a name="19862"
      > </a
      ><a name="19863" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#520" class="InductiveConstructor"
      >yes</a
      ><a name="19866"
      > </a
      ><a name="19867" href="StlcProp.html#19867" class="Bound"
      >x&#8801;x&#8242;</a
      ><a name="19871"
      > </a
      ><a name="19872" class="Keyword"
      >rewrite</a
      ><a name="19879"
      > </a
      ><a name="19880" href="Maps.html#11919" class="Function"
      >just-injective</a
      ><a name="19894"
      > </a
      ><a name="19895" href="StlcProp.html#19830" class="Bound"
      >[&#915;,x&#8758;A]x&#8242;&#8801;B</a
      ><a name="19906"
      >  </a
      ><a name="19908" class="Symbol"
      >=</a
      ><a name="19909"
      >  </a
      ><a name="19911" href="StlcProp.html#19516" class="Function"
      >weaken-closed</a
      ><a name="19924"
      > </a
      ><a name="19925" href="StlcProp.html#19843" class="Bound"
      >&#8866;V</a
      ><a name="19927"
      >
</a
      ><a name="19928" class="Symbol"
      >...|</a
      ><a name="19932"
      > </a
      ><a name="19933" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#547" class="InductiveConstructor"
      >no</a
      ><a name="19935"
      >  </a
      ><a name="19937" href="StlcProp.html#19937" class="Bound"
      >x&#8802;x&#8242;</a
      ><a name="19941"
      >  </a
      ><a name="19943" class="Symbol"
      >=</a
      ><a name="19944"
      >  </a
      ><a name="19946" href="Stlc.html#21613" class="InductiveConstructor"
      >Ax</a
      ><a name="19948"
      > </a
      ><a name="19949" href="StlcProp.html#19830" class="Bound"
      >[&#915;,x&#8758;A]x&#8242;&#8801;B</a
      ><a name="19960"
      >
</a
      ><a name="19961" href="StlcProp.html#16215" class="Function"
      >preservation-[:=]</a
      ><a name="19978"
      > </a
      ><a name="19979" class="Symbol"
      >{</a
      ><a name="19980" href="StlcProp.html#19980" class="Bound"
      >&#915;</a
      ><a name="19981" class="Symbol"
      >}</a
      ><a name="19982"
      > </a
      ><a name="19983" class="Symbol"
      >{</a
      ><a name="19984" href="StlcProp.html#19984" class="Bound"
      >x</a
      ><a name="19985" class="Symbol"
      >}</a
      ><a name="19986"
      > </a
      ><a name="19987" class="Symbol"
      >{</a
      ><a name="19988" href="StlcProp.html#19988" class="Bound"
      >A</a
      ><a name="19989" class="Symbol"
      >}</a
      ><a name="19990"
      > </a
      ><a name="19991" class="Symbol"
      >{</a
      ><a name="19992" href="Stlc.html#3672" class="InductiveConstructor Operator"
      >&#955;[</a
      ><a name="19994"
      > </a
      ><a name="19995" href="StlcProp.html#19995" class="Bound"
      >x&#8242;</a
      ><a name="19997"
      > </a
      ><a name="19998" href="Stlc.html#3672" class="InductiveConstructor Operator"
      >&#8758;</a
      ><a name="19999"
      > </a
      ><a name="20000" href="StlcProp.html#20000" class="Bound"
      >A&#8242;</a
      ><a name="20002"
      > </a
      ><a name="20003" href="Stlc.html#3672" class="InductiveConstructor Operator"
      >]</a
      ><a name="20004"
      > </a
      ><a name="20005" href="StlcProp.html#20005" class="Bound"
      >N&#8242;</a
      ><a name="20007" class="Symbol"
      >}</a
      ><a name="20008"
      > </a
      ><a name="20009" class="Symbol"
      >{</a
      ><a name="20010" class="DottedPattern Symbol"
      >.</a
      ><a name="20011" href="StlcProp.html#20000" class="DottedPattern Bound"
      >A&#8242;</a
      ><a name="20013"
      > </a
      ><a name="20014" href="Stlc.html#2583" class="InductiveConstructor Operator"
      >&#8658;</a
      ><a name="20015"
      > </a
      ><a name="20016" href="StlcProp.html#20016" class="Bound"
      >B&#8242;</a
      ><a name="20018" class="Symbol"
      >}</a
      ><a name="20019"
      > </a
      ><a name="20020" class="Symbol"
      >{</a
      ><a name="20021" href="StlcProp.html#20021" class="Bound"
      >V</a
      ><a name="20022" class="Symbol"
      >}</a
      ><a name="20023"
      > </a
      ><a name="20024" class="Symbol"
      >(</a
      ><a name="20025" href="Stlc.html#21667" class="InductiveConstructor"
      >&#8658;-I</a
      ><a name="20028"
      > </a
      ><a name="20029" href="StlcProp.html#20029" class="Bound"
      >&#8866;N&#8242;</a
      ><a name="20032" class="Symbol"
      >)</a
      ><a name="20033"
      > </a
      ><a name="20034" href="StlcProp.html#20034" class="Bound"
      >&#8866;V</a
      ><a name="20036"
      > </a
      ><a name="20037" class="Keyword"
      >with</a
      ><a name="20041"
      > </a
      ><a name="20042" href="StlcProp.html#19984" class="Bound"
      >x</a
      ><a name="20043"
      > </a
      ><a name="20044" href="Maps.html#2509" class="Function Operator"
      >&#8799;</a
      ><a name="20045"
      > </a
      ><a name="20046" href="StlcProp.html#19995" class="Bound"
      >x&#8242;</a
      ><a name="20048"
      >
</a
      ><a name="20049" class="Symbol"
      >...|</a
      ><a name="20053"
      > </a
      ><a name="20054" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#520" class="InductiveConstructor"
      >yes</a
      ><a name="20057"
      > </a
      ><a name="20058" href="StlcProp.html#20058" class="Bound"
      >x&#8801;x&#8242;</a
      ><a name="20062"
      > </a
      ><a name="20063" class="Keyword"
      >rewrite</a
      ><a name="20070"
      > </a
      ><a name="20071" href="StlcProp.html#20058" class="Bound"
      >x&#8801;x&#8242;</a
      ><a name="20075"
      > </a
      ><a name="20076" class="Symbol"
      >=</a
      ><a name="20077"
      > </a
      ><a name="20078" href="StlcProp.html#12488" class="Function"
      >context-lemma</a
      ><a name="20091"
      > </a
      ><a name="20092" href="StlcProp.html#20117" class="Function"
      >&#915;&#8242;~&#915;</a
      ><a name="20096"
      > </a
      ><a name="20097" class="Symbol"
      >(</a
      ><a name="20098" href="Stlc.html#21667" class="InductiveConstructor"
      >&#8658;-I</a
      ><a name="20101"
      > </a
      ><a name="20102" href="StlcProp.html#20029" class="Bound"
      >&#8866;N&#8242;</a
      ><a name="20105" class="Symbol"
      >)</a
      ><a name="20106"
      >
  </a
      ><a name="20109" class="Keyword"
      >where</a
      ><a name="20114"
      >
  </a
      ><a name="20117" href="StlcProp.html#20117" class="Function"
      >&#915;&#8242;~&#915;</a
      ><a name="20121"
      > </a
      ><a name="20122" class="Symbol"
      >:</a
      ><a name="20123"
      > </a
      ><a name="20124" class="Symbol"
      >&#8704;</a
      ><a name="20125"
      > </a
      ><a name="20126" class="Symbol"
      >{</a
      ><a name="20127" href="StlcProp.html#20127" class="Bound"
      >y</a
      ><a name="20128" class="Symbol"
      >}</a
      ><a name="20129"
      > </a
      ><a name="20130" class="Symbol"
      >&#8594;</a
      ><a name="20131"
      > </a
      ><a name="20132" href="StlcProp.html#20127" class="Bound"
      >y</a
      ><a name="20133"
      > </a
      ><a name="20134" href="StlcProp.html#7750" class="Datatype Operator"
      >&#8712;</a
      ><a name="20135"
      > </a
      ><a name="20136" class="Symbol"
      >(</a
      ><a name="20137" href="Stlc.html#3672" class="InductiveConstructor Operator"
      >&#955;[</a
      ><a name="20139"
      > </a
      ><a name="20140" href="StlcProp.html#19995" class="Bound"
      >x&#8242;</a
      ><a name="20142"
      > </a
      ><a name="20143" href="Stlc.html#3672" class="InductiveConstructor Operator"
      >&#8758;</a
      ><a name="20144"
      > </a
      ><a name="20145" href="StlcProp.html#20000" class="Bound"
      >A&#8242;</a
      ><a name="20147"
      > </a
      ><a name="20148" href="Stlc.html#3672" class="InductiveConstructor Operator"
      >]</a
      ><a name="20149"
      > </a
      ><a name="20150" href="StlcProp.html#20005" class="Bound"
      >N&#8242;</a
      ><a name="20152" class="Symbol"
      >)</a
      ><a name="20153"
      > </a
      ><a name="20154" class="Symbol"
      >&#8594;</a
      ><a name="20155"
      > </a
      ><a name="20156" class="Symbol"
      >(</a
      ><a name="20157" href="StlcProp.html#19980" class="Bound"
      >&#915;</a
      ><a name="20158"
      > </a
      ><a name="20159" href="Maps.html#10368" class="Function Operator"
      >,</a
      ><a name="20160"
      > </a
      ><a name="20161" href="StlcProp.html#19995" class="Bound"
      >x&#8242;</a
      ><a name="20163"
      > </a
      ><a name="20164" href="Maps.html#10368" class="Function Operator"
      >&#8758;</a
      ><a name="20165"
      > </a
      ><a name="20166" href="StlcProp.html#19988" class="Bound"
      >A</a
      ><a name="20167" class="Symbol"
      >)</a
      ><a name="20168"
      > </a
      ><a name="20169" href="StlcProp.html#20127" class="Bound"
      >y</a
      ><a name="20170"
      > </a
      ><a name="20171" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="20172"
      > </a
      ><a name="20173" href="StlcProp.html#19980" class="Bound"
      >&#915;</a
      ><a name="20174"
      > </a
      ><a name="20175" href="StlcProp.html#20127" class="Bound"
      >y</a
      ><a name="20176"
      >
  </a
      ><a name="20179" href="StlcProp.html#20117" class="Function"
      >&#915;&#8242;~&#915;</a
      ><a name="20183"
      > </a
      ><a name="20184" class="Symbol"
      >{</a
      ><a name="20185" href="StlcProp.html#20185" class="Bound"
      >y</a
      ><a name="20186" class="Symbol"
      >}</a
      ><a name="20187"
      > </a
      ><a name="20188" class="Symbol"
      >(</a
      ><a name="20189" href="StlcProp.html#7808" class="InductiveConstructor"
      >free-&#955;</a
      ><a name="20195"
      > </a
      ><a name="20196" href="StlcProp.html#20196" class="Bound"
      >x&#8242;&#8802;y</a
      ><a name="20200"
      > </a
      ><a name="20201" href="StlcProp.html#20201" class="Bound"
      >y&#8712;N&#8242;</a
      ><a name="20205" class="Symbol"
      >)</a
      ><a name="20206"
      > </a
      ><a name="20207" class="Keyword"
      >with</a
      ><a name="20211"
      > </a
      ><a name="20212" href="StlcProp.html#19995" class="Bound"
      >x&#8242;</a
      ><a name="20214"
      > </a
      ><a name="20215" href="Maps.html#2509" class="Function Operator"
      >&#8799;</a
      ><a name="20216"
      > </a
      ><a name="20217" href="StlcProp.html#20185" class="Bound"
      >y</a
      ><a name="20218"
      >
  </a
      ><a name="20221" class="Symbol"
      >...|</a
      ><a name="20225"
      > </a
      ><a name="20226" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#520" class="InductiveConstructor"
      >yes</a
      ><a name="20229"
      > </a
      ><a name="20230" href="StlcProp.html#20230" class="Bound"
      >x&#8242;&#8801;y</a
      ><a name="20234"
      >  </a
      ><a name="20236" class="Symbol"
      >=</a
      ><a name="20237"
      > </a
      ><a name="20238" href="https://agda.github.io/agda-stdlib/Data.Empty.html#348" class="Function"
      >&#8869;-elim</a
      ><a name="20244"
      > </a
      ><a name="20245" class="Symbol"
      >(</a
      ><a name="20246" href="StlcProp.html#20196" class="Bound"
      >x&#8242;&#8802;y</a
      ><a name="20250"
      > </a
      ><a name="20251" href="StlcProp.html#20230" class="Bound"
      >x&#8242;&#8801;y</a
      ><a name="20255" class="Symbol"
      >)</a
      ><a name="20256"
      >
  </a
      ><a name="20259" class="Symbol"
      >...|</a
      ><a name="20263"
      > </a
      ><a name="20264" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#547" class="InductiveConstructor"
      >no</a
      ><a name="20266"
      >  </a
      ><a name="20268" class="Symbol"
      >_</a
      ><a name="20269"
      >     </a
      ><a name="20274" class="Symbol"
      >=</a
      ><a name="20275"
      > </a
      ><a name="20276" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="20280"
      >
</a
      ><a name="20281" class="Symbol"
      >...|</a
      ><a name="20285"
      > </a
      ><a name="20286" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#547" class="InductiveConstructor"
      >no</a
      ><a name="20288"
      >  </a
      ><a name="20290" href="StlcProp.html#20290" class="Bound"
      >x&#8802;x&#8242;</a
      ><a name="20294"
      > </a
      ><a name="20295" class="Symbol"
      >=</a
      ><a name="20296"
      > </a
      ><a name="20297" href="Stlc.html#21667" class="InductiveConstructor"
      >&#8658;-I</a
      ><a name="20300"
      > </a
      ><a name="20301" href="StlcProp.html#20412" class="Function"
      >&#8866;N&#8242;V</a
      ><a name="20305"
      >
  </a
      ><a name="20308" class="Keyword"
      >where</a
      ><a name="20313"
      >
  </a
      ><a name="20316" href="StlcProp.html#20316" class="Function"
      >x&#8242;x&#8866;N&#8242;</a
      ><a name="20322"
      > </a
      ><a name="20323" class="Symbol"
      >:</a
      ><a name="20324"
      > </a
      ><a name="20325" href="StlcProp.html#19980" class="Bound"
      >&#915;</a
      ><a name="20326"
      > </a
      ><a name="20327" href="Maps.html#10368" class="Function Operator"
      >,</a
      ><a name="20328"
      > </a
      ><a name="20329" href="StlcProp.html#19995" class="Bound"
      >x&#8242;</a
      ><a name="20331"
      > </a
      ><a name="20332" href="Maps.html#10368" class="Function Operator"
      >&#8758;</a
      ><a name="20333"
      > </a
      ><a name="20334" href="StlcProp.html#20000" class="Bound"
      >A&#8242;</a
      ><a name="20336"
      > </a
      ><a name="20337" href="Maps.html#10368" class="Function Operator"
      >,</a
      ><a name="20338"
      > </a
      ><a name="20339" href="StlcProp.html#19984" class="Bound"
      >x</a
      ><a name="20340"
      > </a
      ><a name="20341" href="Maps.html#10368" class="Function Operator"
      >&#8758;</a
      ><a name="20342"
      > </a
      ><a name="20343" href="StlcProp.html#19988" class="Bound"
      >A</a
      ><a name="20344"
      > </a
      ><a name="20345" href="Stlc.html#21569" class="Datatype Operator"
      >&#8866;</a
      ><a name="20346"
      > </a
      ><a name="20347" href="StlcProp.html#20005" class="Bound"
      >N&#8242;</a
      ><a name="20349"
      > </a
      ><a name="20350" href="Stlc.html#21569" class="Datatype Operator"
      >&#8758;</a
      ><a name="20351"
      > </a
      ><a name="20352" href="StlcProp.html#20016" class="Bound"
      >B&#8242;</a
      ><a name="20354"
      >
  </a
      ><a name="20357" href="StlcProp.html#20316" class="Function"
      >x&#8242;x&#8866;N&#8242;</a
      ><a name="20363"
      > </a
      ><a name="20364" class="Keyword"
      >rewrite</a
      ><a name="20371"
      > </a
      ><a name="20372" href="Maps.html#11491" class="Function"
      >update-permute</a
      ><a name="20386"
      > </a
      ><a name="20387" href="StlcProp.html#19980" class="Bound"
      >&#915;</a
      ><a name="20388"
      > </a
      ><a name="20389" href="StlcProp.html#19984" class="Bound"
      >x</a
      ><a name="20390"
      > </a
      ><a name="20391" href="StlcProp.html#19988" class="Bound"
      >A</a
      ><a name="20392"
      > </a
      ><a name="20393" href="StlcProp.html#19995" class="Bound"
      >x&#8242;</a
      ><a name="20395"
      > </a
      ><a name="20396" href="StlcProp.html#20000" class="Bound"
      >A&#8242;</a
      ><a name="20398"
      > </a
      ><a name="20399" href="StlcProp.html#20290" class="Bound"
      >x&#8802;x&#8242;</a
      ><a name="20403"
      > </a
      ><a name="20404" class="Symbol"
      >=</a
      ><a name="20405"
      > </a
      ><a name="20406" href="StlcProp.html#20029" class="Bound"
      >&#8866;N&#8242;</a
      ><a name="20409"
      >
  </a
      ><a name="20412" href="StlcProp.html#20412" class="Function"
      >&#8866;N&#8242;V</a
      ><a name="20416"
      > </a
      ><a name="20417" class="Symbol"
      >:</a
      ><a name="20418"
      > </a
      ><a name="20419" class="Symbol"
      >(</a
      ><a name="20420" href="StlcProp.html#19980" class="Bound"
      >&#915;</a
      ><a name="20421"
      > </a
      ><a name="20422" href="Maps.html#10368" class="Function Operator"
      >,</a
      ><a name="20423"
      > </a
      ><a name="20424" href="StlcProp.html#19995" class="Bound"
      >x&#8242;</a
      ><a name="20426"
      > </a
      ><a name="20427" href="Maps.html#10368" class="Function Operator"
      >&#8758;</a
      ><a name="20428"
      > </a
      ><a name="20429" href="StlcProp.html#20000" class="Bound"
      >A&#8242;</a
      ><a name="20431" class="Symbol"
      >)</a
      ><a name="20432"
      > </a
      ><a name="20433" href="Stlc.html#21569" class="Datatype Operator"
      >&#8866;</a
      ><a name="20434"
      > </a
      ><a name="20435" href="StlcProp.html#20005" class="Bound"
      >N&#8242;</a
      ><a name="20437"
      > </a
      ><a name="20438" href="Stlc.html#12079" class="Function Operator"
      >[</a
      ><a name="20439"
      > </a
      ><a name="20440" href="StlcProp.html#19984" class="Bound"
      >x</a
      ><a name="20441"
      > </a
      ><a name="20442" href="Stlc.html#12079" class="Function Operator"
      >:=</a
      ><a name="20444"
      > </a
      ><a name="20445" href="StlcProp.html#20021" class="Bound"
      >V</a
      ><a name="20446"
      > </a
      ><a name="20447" href="Stlc.html#12079" class="Function Operator"
      >]</a
      ><a name="20448"
      > </a
      ><a name="20449" href="Stlc.html#21569" class="Datatype Operator"
      >&#8758;</a
      ><a name="20450"
      > </a
      ><a name="20451" href="StlcProp.html#20016" class="Bound"
      >B&#8242;</a
      ><a name="20453"
      >
  </a
      ><a name="20456" href="StlcProp.html#20412" class="Function"
      >&#8866;N&#8242;V</a
      ><a name="20460"
      > </a
      ><a name="20461" class="Symbol"
      >=</a
      ><a name="20462"
      > </a
      ><a name="20463" href="StlcProp.html#16215" class="Function"
      >preservation-[:=]</a
      ><a name="20480"
      > </a
      ><a name="20481" href="StlcProp.html#20316" class="Function"
      >x&#8242;x&#8866;N&#8242;</a
      ><a name="20487"
      > </a
      ><a name="20488" href="StlcProp.html#20034" class="Bound"
      >&#8866;V</a
      ><a name="20490"
      >
</a
      ><a name="20491" href="StlcProp.html#16215" class="Function"
      >preservation-[:=]</a
      ><a name="20508"
      > </a
      ><a name="20509" class="Symbol"
      >(</a
      ><a name="20510" href="Stlc.html#21744" class="InductiveConstructor"
      >&#8658;-E</a
      ><a name="20513"
      > </a
      ><a name="20514" href="StlcProp.html#20514" class="Bound"
      >&#8866;L</a
      ><a name="20516"
      > </a
      ><a name="20517" href="StlcProp.html#20517" class="Bound"
      >&#8866;M</a
      ><a name="20519" class="Symbol"
      >)</a
      ><a name="20520"
      > </a
      ><a name="20521" href="StlcProp.html#20521" class="Bound"
      >&#8866;V</a
      ><a name="20523"
      > </a
      ><a name="20524" class="Symbol"
      >=</a
      ><a name="20525"
      > </a
      ><a name="20526" href="Stlc.html#21744" class="InductiveConstructor"
      >&#8658;-E</a
      ><a name="20529"
      > </a
      ><a name="20530" class="Symbol"
      >(</a
      ><a name="20531" href="StlcProp.html#16215" class="Function"
      >preservation-[:=]</a
      ><a name="20548"
      > </a
      ><a name="20549" href="StlcProp.html#20514" class="Bound"
      >&#8866;L</a
      ><a name="20551"
      > </a
      ><a name="20552" href="StlcProp.html#20521" class="Bound"
      >&#8866;V</a
      ><a name="20554" class="Symbol"
      >)</a
      ><a name="20555"
      > </a
      ><a name="20556" class="Symbol"
      >(</a
      ><a name="20557" href="StlcProp.html#16215" class="Function"
      >preservation-[:=]</a
      ><a name="20574"
      > </a
      ><a name="20575" href="StlcProp.html#20517" class="Bound"
      >&#8866;M</a
      ><a name="20577"
      > </a
      ><a name="20578" href="StlcProp.html#20521" class="Bound"
      >&#8866;V</a
      ><a name="20580" class="Symbol"
      >)</a
      ><a name="20581"
      >
</a
      ><a name="20582" href="StlcProp.html#16215" class="Function"
      >preservation-[:=]</a
      ><a name="20599"
      > </a
      ><a name="20600" href="Stlc.html#21822" class="InductiveConstructor"
      >&#120121;-I&#8321;</a
      ><a name="20604"
      > </a
      ><a name="20605" href="StlcProp.html#20605" class="Bound"
      >&#8866;V</a
      ><a name="20607"
      > </a
      ><a name="20608" class="Symbol"
      >=</a
      ><a name="20609"
      > </a
      ><a name="20610" href="Stlc.html#21822" class="InductiveConstructor"
      >&#120121;-I&#8321;</a
      ><a name="20614"
      >
</a
      ><a name="20615" href="StlcProp.html#16215" class="Function"
      >preservation-[:=]</a
      ><a name="20632"
      > </a
      ><a name="20633" href="Stlc.html#21856" class="InductiveConstructor"
      >&#120121;-I&#8322;</a
      ><a name="20637"
      > </a
      ><a name="20638" href="StlcProp.html#20638" class="Bound"
      >&#8866;V</a
      ><a name="20640"
      > </a
      ><a name="20641" class="Symbol"
      >=</a
      ><a name="20642"
      > </a
      ><a name="20643" href="Stlc.html#21856" class="InductiveConstructor"
      >&#120121;-I&#8322;</a
      ><a name="20647"
      >
</a
      ><a name="20648" href="StlcProp.html#16215" class="Function"
      >preservation-[:=]</a
      ><a name="20665"
      > </a
      ><a name="20666" class="Symbol"
      >(</a
      ><a name="20667" href="Stlc.html#21891" class="InductiveConstructor"
      >&#120121;-E</a
      ><a name="20670"
      > </a
      ><a name="20671" href="StlcProp.html#20671" class="Bound"
      >&#8866;L</a
      ><a name="20673"
      > </a
      ><a name="20674" href="StlcProp.html#20674" class="Bound"
      >&#8866;M</a
      ><a name="20676"
      > </a
      ><a name="20677" href="StlcProp.html#20677" class="Bound"
      >&#8866;N</a
      ><a name="20679" class="Symbol"
      >)</a
      ><a name="20680"
      > </a
      ><a name="20681" href="StlcProp.html#20681" class="Bound"
      >&#8866;V</a
      ><a name="20683"
      > </a
      ><a name="20684" class="Symbol"
      >=</a
      ><a name="20685"
      >
  </a
      ><a name="20688" href="Stlc.html#21891" class="InductiveConstructor"
      >&#120121;-E</a
      ><a name="20691"
      > </a
      ><a name="20692" class="Symbol"
      >(</a
      ><a name="20693" href="StlcProp.html#16215" class="Function"
      >preservation-[:=]</a
      ><a name="20710"
      > </a
      ><a name="20711" href="StlcProp.html#20671" class="Bound"
      >&#8866;L</a
      ><a name="20713"
      > </a
      ><a name="20714" href="StlcProp.html#20681" class="Bound"
      >&#8866;V</a
      ><a name="20716" class="Symbol"
      >)</a
      ><a name="20717"
      > </a
      ><a name="20718" class="Symbol"
      >(</a
      ><a name="20719" href="StlcProp.html#16215" class="Function"
      >preservation-[:=]</a
      ><a name="20736"
      > </a
      ><a name="20737" href="StlcProp.html#20674" class="Bound"
      >&#8866;M</a
      ><a name="20739"
      > </a
      ><a name="20740" href="StlcProp.html#20681" class="Bound"
      >&#8866;V</a
      ><a name="20742" class="Symbol"
      >)</a
      ><a name="20743"
      > </a
      ><a name="20744" class="Symbol"
      >(</a
      ><a name="20745" href="StlcProp.html#16215" class="Function"
      >preservation-[:=]</a
      ><a name="20762"
      > </a
      ><a name="20763" href="StlcProp.html#20677" class="Bound"
      >&#8866;N</a
      ><a name="20765"
      > </a
      ><a name="20766" href="StlcProp.html#20681" class="Bound"
      >&#8866;V</a
      ><a name="20768" class="Symbol"
      >)</a
      >

</pre>


### Main Theorem

We now have the tools we need to prove preservation: if a closed
term `M` has type `A` and takes a step to `N`, then `N`
is also a closed term with type `A`.  In other words, small-step
reduction preserves types.

<pre class="Agda">

<a name="21028" href="StlcProp.html#21028" class="Function"
      >preservation</a
      ><a name="21040"
      > </a
      ><a name="21041" class="Symbol"
      >:</a
      ><a name="21042"
      > </a
      ><a name="21043" class="Symbol"
      >&#8704;</a
      ><a name="21044"
      > </a
      ><a name="21045" class="Symbol"
      >{</a
      ><a name="21046" href="StlcProp.html#21046" class="Bound"
      >M</a
      ><a name="21047"
      > </a
      ><a name="21048" href="StlcProp.html#21048" class="Bound"
      >N</a
      ><a name="21049"
      > </a
      ><a name="21050" href="StlcProp.html#21050" class="Bound"
      >A</a
      ><a name="21051" class="Symbol"
      >}</a
      ><a name="21052"
      > </a
      ><a name="21053" class="Symbol"
      >&#8594;</a
      ><a name="21054"
      > </a
      ><a name="21055" href="Maps.html#10265" class="Function"
      >&#8709;</a
      ><a name="21056"
      > </a
      ><a name="21057" href="Stlc.html#21569" class="Datatype Operator"
      >&#8866;</a
      ><a name="21058"
      > </a
      ><a name="21059" href="StlcProp.html#21046" class="Bound"
      >M</a
      ><a name="21060"
      > </a
      ><a name="21061" href="Stlc.html#21569" class="Datatype Operator"
      >&#8758;</a
      ><a name="21062"
      > </a
      ><a name="21063" href="StlcProp.html#21050" class="Bound"
      >A</a
      ><a name="21064"
      > </a
      ><a name="21065" class="Symbol"
      >&#8594;</a
      ><a name="21066"
      > </a
      ><a name="21067" href="StlcProp.html#21046" class="Bound"
      >M</a
      ><a name="21068"
      > </a
      ><a name="21069" href="Stlc.html#15832" class="Datatype Operator"
      >&#10233;</a
      ><a name="21070"
      > </a
      ><a name="21071" href="StlcProp.html#21048" class="Bound"
      >N</a
      ><a name="21072"
      > </a
      ><a name="21073" class="Symbol"
      >&#8594;</a
      ><a name="21074"
      > </a
      ><a name="21075" href="Maps.html#10265" class="Function"
      >&#8709;</a
      ><a name="21076"
      > </a
      ><a name="21077" href="Stlc.html#21569" class="Datatype Operator"
      >&#8866;</a
      ><a name="21078"
      > </a
      ><a name="21079" href="StlcProp.html#21048" class="Bound"
      >N</a
      ><a name="21080"
      > </a
      ><a name="21081" href="Stlc.html#21569" class="Datatype Operator"
      >&#8758;</a
      ><a name="21082"
      > </a
      ><a name="21083" href="StlcProp.html#21050" class="Bound"
      >A</a
      >

</pre>

_Proof_: By induction on the derivation of `∅ ⊢ M ∶ A`.

- We can immediately rule out `Ax`, `⇒-I`, `𝔹-I₁`, and
  `𝔹-I₂` as the final rules in the derivation, since in each of
  these cases `M` cannot take a step.

- If the last rule in the derivation was `⇒-E`, then `M = L · M`.
  There are three cases to consider, one for each rule that
  could have been used to show that `L · M` takes a step to `N`.

    - If `L · M` takes a step by `ξ·₁`, with `L` stepping to
      `L′`, then by the IH `L′` has the same type as `L`, and
      hence `L′ · M` has the same type as `L · M`.

    - The `ξ·₂` case is similar.

    - If `L · M` takes a step by `β⇒`, then `L = λ[ x ∶ A ] N` and `M
      = V` and `L · M` steps to `N [ x := V]`; the desired result now
      follows from the fact that substitution preserves types.

- If the last rule in the derivation was `if`, then `M = if L
  then M else N`, and there are again three cases depending on
  how `if L then M else N` steps.

    - If it steps via `β𝔹₁` or `βB₂`, the result is immediate, since
      `M` and `N` have the same type as `if L then M else N`.

    - Otherwise, `L` steps by `ξif`, and the desired conclusion
      follows directly from the induction hypothesis.

<pre class="Agda">

<a name="22341" href="StlcProp.html#21028" class="Function"
      >preservation</a
      ><a name="22353"
      > </a
      ><a name="22354" class="Symbol"
      >(</a
      ><a name="22355" href="Stlc.html#21613" class="InductiveConstructor"
      >Ax</a
      ><a name="22357"
      > </a
      ><a name="22358" href="StlcProp.html#22358" class="Bound"
      >&#915;x&#8801;A</a
      ><a name="22362" class="Symbol"
      >)</a
      ><a name="22363"
      > </a
      ><a name="22364" class="Symbol"
      >()</a
      ><a name="22366"
      >
</a
      ><a name="22367" href="StlcProp.html#21028" class="Function"
      >preservation</a
      ><a name="22379"
      > </a
      ><a name="22380" class="Symbol"
      >(</a
      ><a name="22381" href="Stlc.html#21667" class="InductiveConstructor"
      >&#8658;-I</a
      ><a name="22384"
      > </a
      ><a name="22385" href="StlcProp.html#22385" class="Bound"
      >&#8866;N</a
      ><a name="22387" class="Symbol"
      >)</a
      ><a name="22388"
      > </a
      ><a name="22389" class="Symbol"
      >()</a
      ><a name="22391"
      >
</a
      ><a name="22392" href="StlcProp.html#21028" class="Function"
      >preservation</a
      ><a name="22404"
      > </a
      ><a name="22405" class="Symbol"
      >(</a
      ><a name="22406" href="Stlc.html#21744" class="InductiveConstructor"
      >&#8658;-E</a
      ><a name="22409"
      > </a
      ><a name="22410" class="Symbol"
      >(</a
      ><a name="22411" href="Stlc.html#21667" class="InductiveConstructor"
      >&#8658;-I</a
      ><a name="22414"
      > </a
      ><a name="22415" href="StlcProp.html#22415" class="Bound"
      >&#8866;N</a
      ><a name="22417" class="Symbol"
      >)</a
      ><a name="22418"
      > </a
      ><a name="22419" href="StlcProp.html#22419" class="Bound"
      >&#8866;V</a
      ><a name="22421" class="Symbol"
      >)</a
      ><a name="22422"
      > </a
      ><a name="22423" class="Symbol"
      >(</a
      ><a name="22424" href="Stlc.html#15984" class="InductiveConstructor"
      >&#946;&#955;&#183;</a
      ><a name="22427"
      > </a
      ><a name="22428" href="StlcProp.html#22428" class="Bound"
      >valueV</a
      ><a name="22434" class="Symbol"
      >)</a
      ><a name="22435"
      > </a
      ><a name="22436" class="Symbol"
      >=</a
      ><a name="22437"
      > </a
      ><a name="22438" href="StlcProp.html#16215" class="Function"
      >preservation-[:=]</a
      ><a name="22455"
      > </a
      ><a name="22456" href="StlcProp.html#22415" class="Bound"
      >&#8866;N</a
      ><a name="22458"
      > </a
      ><a name="22459" href="StlcProp.html#22419" class="Bound"
      >&#8866;V</a
      ><a name="22461"
      >
</a
      ><a name="22462" href="StlcProp.html#21028" class="Function"
      >preservation</a
      ><a name="22474"
      > </a
      ><a name="22475" class="Symbol"
      >(</a
      ><a name="22476" href="Stlc.html#21744" class="InductiveConstructor"
      >&#8658;-E</a
      ><a name="22479"
      > </a
      ><a name="22480" href="StlcProp.html#22480" class="Bound"
      >&#8866;L</a
      ><a name="22482"
      > </a
      ><a name="22483" href="StlcProp.html#22483" class="Bound"
      >&#8866;M</a
      ><a name="22485" class="Symbol"
      >)</a
      ><a name="22486"
      > </a
      ><a name="22487" class="Symbol"
      >(</a
      ><a name="22488" href="Stlc.html#15864" class="InductiveConstructor"
      >&#958;&#183;&#8321;</a
      ><a name="22491"
      > </a
      ><a name="22492" href="StlcProp.html#22492" class="Bound"
      >L&#10233;L&#8242;</a
      ><a name="22496" class="Symbol"
      >)</a
      ><a name="22497"
      > </a
      ><a name="22498" class="Keyword"
      >with</a
      ><a name="22502"
      > </a
      ><a name="22503" href="StlcProp.html#21028" class="Function"
      >preservation</a
      ><a name="22515"
      > </a
      ><a name="22516" href="StlcProp.html#22480" class="Bound"
      >&#8866;L</a
      ><a name="22518"
      > </a
      ><a name="22519" href="StlcProp.html#22492" class="Bound"
      >L&#10233;L&#8242;</a
      ><a name="22523"
      >
</a
      ><a name="22524" class="Symbol"
      >...|</a
      ><a name="22528"
      > </a
      ><a name="22529" href="StlcProp.html#22529" class="Bound"
      >&#8866;L&#8242;</a
      ><a name="22532"
      > </a
      ><a name="22533" class="Symbol"
      >=</a
      ><a name="22534"
      > </a
      ><a name="22535" href="Stlc.html#21744" class="InductiveConstructor"
      >&#8658;-E</a
      ><a name="22538"
      > </a
      ><a name="22539" href="StlcProp.html#22529" class="Bound"
      >&#8866;L&#8242;</a
      ><a name="22542"
      > </a
      ><a name="22543" href="StlcProp.html#22483" class="Bound"
      >&#8866;M</a
      ><a name="22545"
      >
</a
      ><a name="22546" href="StlcProp.html#21028" class="Function"
      >preservation</a
      ><a name="22558"
      > </a
      ><a name="22559" class="Symbol"
      >(</a
      ><a name="22560" href="Stlc.html#21744" class="InductiveConstructor"
      >&#8658;-E</a
      ><a name="22563"
      > </a
      ><a name="22564" href="StlcProp.html#22564" class="Bound"
      >&#8866;L</a
      ><a name="22566"
      > </a
      ><a name="22567" href="StlcProp.html#22567" class="Bound"
      >&#8866;M</a
      ><a name="22569" class="Symbol"
      >)</a
      ><a name="22570"
      > </a
      ><a name="22571" class="Symbol"
      >(</a
      ><a name="22572" href="Stlc.html#15917" class="InductiveConstructor"
      >&#958;&#183;&#8322;</a
      ><a name="22575"
      > </a
      ><a name="22576" href="StlcProp.html#22576" class="Bound"
      >valueL</a
      ><a name="22582"
      > </a
      ><a name="22583" href="StlcProp.html#22583" class="Bound"
      >M&#10233;M&#8242;</a
      ><a name="22587" class="Symbol"
      >)</a
      ><a name="22588"
      > </a
      ><a name="22589" class="Keyword"
      >with</a
      ><a name="22593"
      > </a
      ><a name="22594" href="StlcProp.html#21028" class="Function"
      >preservation</a
      ><a name="22606"
      > </a
      ><a name="22607" href="StlcProp.html#22567" class="Bound"
      >&#8866;M</a
      ><a name="22609"
      > </a
      ><a name="22610" href="StlcProp.html#22583" class="Bound"
      >M&#10233;M&#8242;</a
      ><a name="22614"
      >
</a
      ><a name="22615" class="Symbol"
      >...|</a
      ><a name="22619"
      > </a
      ><a name="22620" href="StlcProp.html#22620" class="Bound"
      >&#8866;M&#8242;</a
      ><a name="22623"
      > </a
      ><a name="22624" class="Symbol"
      >=</a
      ><a name="22625"
      > </a
      ><a name="22626" href="Stlc.html#21744" class="InductiveConstructor"
      >&#8658;-E</a
      ><a name="22629"
      > </a
      ><a name="22630" href="StlcProp.html#22564" class="Bound"
      >&#8866;L</a
      ><a name="22632"
      > </a
      ><a name="22633" href="StlcProp.html#22620" class="Bound"
      >&#8866;M&#8242;</a
      ><a name="22636"
      >
</a
      ><a name="22637" href="StlcProp.html#21028" class="Function"
      >preservation</a
      ><a name="22649"
      > </a
      ><a name="22650" href="Stlc.html#21822" class="InductiveConstructor"
      >&#120121;-I&#8321;</a
      ><a name="22654"
      > </a
      ><a name="22655" class="Symbol"
      >()</a
      ><a name="22657"
      >
</a
      ><a name="22658" href="StlcProp.html#21028" class="Function"
      >preservation</a
      ><a name="22670"
      > </a
      ><a name="22671" href="Stlc.html#21856" class="InductiveConstructor"
      >&#120121;-I&#8322;</a
      ><a name="22675"
      > </a
      ><a name="22676" class="Symbol"
      >()</a
      ><a name="22678"
      >
</a
      ><a name="22679" href="StlcProp.html#21028" class="Function"
      >preservation</a
      ><a name="22691"
      > </a
      ><a name="22692" class="Symbol"
      >(</a
      ><a name="22693" href="Stlc.html#21891" class="InductiveConstructor"
      >&#120121;-E</a
      ><a name="22696"
      > </a
      ><a name="22697" href="Stlc.html#21822" class="InductiveConstructor"
      >&#120121;-I&#8321;</a
      ><a name="22701"
      > </a
      ><a name="22702" href="StlcProp.html#22702" class="Bound"
      >&#8866;M</a
      ><a name="22704"
      > </a
      ><a name="22705" href="StlcProp.html#22705" class="Bound"
      >&#8866;N</a
      ><a name="22707" class="Symbol"
      >)</a
      ><a name="22708"
      > </a
      ><a name="22709" href="Stlc.html#16139" class="InductiveConstructor"
      >&#946;if-true</a
      ><a name="22717"
      > </a
      ><a name="22718" class="Symbol"
      >=</a
      ><a name="22719"
      > </a
      ><a name="22720" href="StlcProp.html#22702" class="Bound"
      >&#8866;M</a
      ><a name="22722"
      >
</a
      ><a name="22723" href="StlcProp.html#21028" class="Function"
      >preservation</a
      ><a name="22735"
      > </a
      ><a name="22736" class="Symbol"
      >(</a
      ><a name="22737" href="Stlc.html#21891" class="InductiveConstructor"
      >&#120121;-E</a
      ><a name="22740"
      > </a
      ><a name="22741" href="Stlc.html#21856" class="InductiveConstructor"
      >&#120121;-I&#8322;</a
      ><a name="22745"
      > </a
      ><a name="22746" href="StlcProp.html#22746" class="Bound"
      >&#8866;M</a
      ><a name="22748"
      > </a
      ><a name="22749" href="StlcProp.html#22749" class="Bound"
      >&#8866;N</a
      ><a name="22751" class="Symbol"
      >)</a
      ><a name="22752"
      > </a
      ><a name="22753" href="Stlc.html#16192" class="InductiveConstructor"
      >&#946;if-false</a
      ><a name="22762"
      > </a
      ><a name="22763" class="Symbol"
      >=</a
      ><a name="22764"
      > </a
      ><a name="22765" href="StlcProp.html#22749" class="Bound"
      >&#8866;N</a
      ><a name="22767"
      >
</a
      ><a name="22768" href="StlcProp.html#21028" class="Function"
      >preservation</a
      ><a name="22780"
      > </a
      ><a name="22781" class="Symbol"
      >(</a
      ><a name="22782" href="Stlc.html#21891" class="InductiveConstructor"
      >&#120121;-E</a
      ><a name="22785"
      > </a
      ><a name="22786" href="StlcProp.html#22786" class="Bound"
      >&#8866;L</a
      ><a name="22788"
      > </a
      ><a name="22789" href="StlcProp.html#22789" class="Bound"
      >&#8866;M</a
      ><a name="22791"
      > </a
      ><a name="22792" href="StlcProp.html#22792" class="Bound"
      >&#8866;N</a
      ><a name="22794" class="Symbol"
      >)</a
      ><a name="22795"
      > </a
      ><a name="22796" class="Symbol"
      >(</a
      ><a name="22797" href="Stlc.html#16054" class="InductiveConstructor"
      >&#958;if</a
      ><a name="22800"
      > </a
      ><a name="22801" href="StlcProp.html#22801" class="Bound"
      >L&#10233;L&#8242;</a
      ><a name="22805" class="Symbol"
      >)</a
      ><a name="22806"
      > </a
      ><a name="22807" class="Keyword"
      >with</a
      ><a name="22811"
      > </a
      ><a name="22812" href="StlcProp.html#21028" class="Function"
      >preservation</a
      ><a name="22824"
      > </a
      ><a name="22825" href="StlcProp.html#22786" class="Bound"
      >&#8866;L</a
      ><a name="22827"
      > </a
      ><a name="22828" href="StlcProp.html#22801" class="Bound"
      >L&#10233;L&#8242;</a
      ><a name="22832"
      >
</a
      ><a name="22833" class="Symbol"
      >...|</a
      ><a name="22837"
      > </a
      ><a name="22838" href="StlcProp.html#22838" class="Bound"
      >&#8866;L&#8242;</a
      ><a name="22841"
      > </a
      ><a name="22842" class="Symbol"
      >=</a
      ><a name="22843"
      > </a
      ><a name="22844" href="Stlc.html#21891" class="InductiveConstructor"
      >&#120121;-E</a
      ><a name="22847"
      > </a
      ><a name="22848" href="StlcProp.html#22838" class="Bound"
      >&#8866;L&#8242;</a
      ><a name="22851"
      > </a
      ><a name="22852" href="StlcProp.html#22789" class="Bound"
      >&#8866;M</a
      ><a name="22854"
      > </a
      ><a name="22855" href="StlcProp.html#22792" class="Bound"
      >&#8866;N</a
      >

</pre>


#### Exercise: 2 stars, recommended (subject_expansion_stlc)

<!--
An exercise in the [Types]({{ "Types" | relative_url }}) chapter asked about the
subject expansion property for the simple language of arithmetic and boolean
expressions.  Does this property hold for STLC?  That is, is it always the case
that, if `M ==> N` and `∅ ⊢ N ∶ A`, then `∅ ⊢ M ∶ A`?  It is easy to find a
counter-example with conditionals, find one not involving conditionals.
-->

We say that `M` _reduces_ to `N` if `M ⟹ N`,
and that `M` _expands_ to `N` if `N ⟹ M`.
The preservation property is sometimes called _subject reduction_.
Its opposite is _subject expansion_, which holds if
`M ==> N` and `∅ ⊢ N ∶ A`, then `∅ ⊢ M ∶ A`.
Find two counter-examples to subject expansion, one
with conditionals and one not involving conditionals.

## Type Soundness

#### Exercise: 2 stars, optional (type_soundness)

Put progress and preservation together and show that a well-typed
term can _never_ reach a stuck state.

<pre class="Agda">

<a name="23875" href="StlcProp.html#23875" class="Function"
      >Normal</a
      ><a name="23881"
      > </a
      ><a name="23882" class="Symbol"
      >:</a
      ><a name="23883"
      > </a
      ><a name="23884" href="Stlc.html#3637" class="Datatype"
      >Term</a
      ><a name="23888"
      > </a
      ><a name="23889" class="Symbol"
      >&#8594;</a
      ><a name="23890"
      > </a
      ><a name="23891" class="PrimitiveType"
      >Set</a
      ><a name="23894"
      >
</a
      ><a name="23895" href="StlcProp.html#23875" class="Function"
      >Normal</a
      ><a name="23901"
      > </a
      ><a name="23902" href="StlcProp.html#23902" class="Bound"
      >M</a
      ><a name="23903"
      > </a
      ><a name="23904" class="Symbol"
      >=</a
      ><a name="23905"
      > </a
      ><a name="23906" class="Symbol"
      >&#8704;</a
      ><a name="23907"
      > </a
      ><a name="23908" class="Symbol"
      >{</a
      ><a name="23909" href="StlcProp.html#23909" class="Bound"
      >N</a
      ><a name="23910" class="Symbol"
      >}</a
      ><a name="23911"
      > </a
      ><a name="23912" class="Symbol"
      >&#8594;</a
      ><a name="23913"
      > </a
      ><a name="23914" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#414" class="Function Operator"
      >&#172;</a
      ><a name="23915"
      > </a
      ><a name="23916" class="Symbol"
      >(</a
      ><a name="23917" href="StlcProp.html#23902" class="Bound"
      >M</a
      ><a name="23918"
      > </a
      ><a name="23919" href="Stlc.html#15832" class="Datatype Operator"
      >&#10233;</a
      ><a name="23920"
      > </a
      ><a name="23921" href="StlcProp.html#23909" class="Bound"
      >N</a
      ><a name="23922" class="Symbol"
      >)</a
      ><a name="23923"
      >

</a
      ><a name="23925" href="StlcProp.html#23925" class="Function"
      >Stuck</a
      ><a name="23930"
      > </a
      ><a name="23931" class="Symbol"
      >:</a
      ><a name="23932"
      > </a
      ><a name="23933" href="Stlc.html#3637" class="Datatype"
      >Term</a
      ><a name="23937"
      > </a
      ><a name="23938" class="Symbol"
      >&#8594;</a
      ><a name="23939"
      > </a
      ><a name="23940" class="PrimitiveType"
      >Set</a
      ><a name="23943"
      >
</a
      ><a name="23944" href="StlcProp.html#23925" class="Function"
      >Stuck</a
      ><a name="23949"
      > </a
      ><a name="23950" href="StlcProp.html#23950" class="Bound"
      >M</a
      ><a name="23951"
      > </a
      ><a name="23952" class="Symbol"
      >=</a
      ><a name="23953"
      > </a
      ><a name="23954" href="StlcProp.html#23875" class="Function"
      >Normal</a
      ><a name="23960"
      > </a
      ><a name="23961" href="StlcProp.html#23950" class="Bound"
      >M</a
      ><a name="23962"
      > </a
      ><a name="23963" href="https://agda.github.io/agda-stdlib/Data.Product.html#1073" class="Function Operator"
      >&#215;</a
      ><a name="23964"
      > </a
      ><a name="23965" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#414" class="Function Operator"
      >&#172;</a
      ><a name="23966"
      > </a
      ><a name="23967" href="Stlc.html#9535" class="Datatype"
      >Value</a
      ><a name="23972"
      > </a
      ><a name="23973" href="StlcProp.html#23950" class="Bound"
      >M</a
      ><a name="23974"
      >

</a
      ><a name="23976" class="Keyword"
      >postulate</a
      ><a name="23985"
      >
  </a
      ><a name="23988" href="StlcProp.html#23988" class="Postulate"
      >Soundness</a
      ><a name="23997"
      > </a
      ><a name="23998" class="Symbol"
      >:</a
      ><a name="23999"
      > </a
      ><a name="24000" class="Symbol"
      >&#8704;</a
      ><a name="24001"
      > </a
      ><a name="24002" class="Symbol"
      >{</a
      ><a name="24003" href="StlcProp.html#24003" class="Bound"
      >M</a
      ><a name="24004"
      > </a
      ><a name="24005" href="StlcProp.html#24005" class="Bound"
      >N</a
      ><a name="24006"
      > </a
      ><a name="24007" href="StlcProp.html#24007" class="Bound"
      >A</a
      ><a name="24008" class="Symbol"
      >}</a
      ><a name="24009"
      > </a
      ><a name="24010" class="Symbol"
      >&#8594;</a
      ><a name="24011"
      > </a
      ><a name="24012" href="Maps.html#10265" class="Function"
      >&#8709;</a
      ><a name="24013"
      > </a
      ><a name="24014" href="Stlc.html#21569" class="Datatype Operator"
      >&#8866;</a
      ><a name="24015"
      > </a
      ><a name="24016" href="StlcProp.html#24003" class="Bound"
      >M</a
      ><a name="24017"
      > </a
      ><a name="24018" href="Stlc.html#21569" class="Datatype Operator"
      >&#8758;</a
      ><a name="24019"
      > </a
      ><a name="24020" href="StlcProp.html#24007" class="Bound"
      >A</a
      ><a name="24021"
      > </a
      ><a name="24022" class="Symbol"
      >&#8594;</a
      ><a name="24023"
      > </a
      ><a name="24024" href="StlcProp.html#24003" class="Bound"
      >M</a
      ><a name="24025"
      > </a
      ><a name="24026" href="Stlc.html#17866" class="Datatype Operator"
      >&#10233;*</a
      ><a name="24028"
      > </a
      ><a name="24029" href="StlcProp.html#24005" class="Bound"
      >N</a
      ><a name="24030"
      > </a
      ><a name="24031" class="Symbol"
      >&#8594;</a
      ><a name="24032"
      > </a
      ><a name="24033" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#414" class="Function Operator"
      >&#172;</a
      ><a name="24034"
      > </a
      ><a name="24035" class="Symbol"
      >(</a
      ><a name="24036" href="StlcProp.html#23925" class="Function"
      >Stuck</a
      ><a name="24041"
      > </a
      ><a name="24042" href="StlcProp.html#24005" class="Bound"
      >N</a
      ><a name="24043" class="Symbol"
      >)</a
      >

</pre>

<div class="hidden">
<pre class="Agda">

<a name="24091" href="StlcProp.html#24091" class="Function"
      >Soundness&#8242;</a
      ><a name="24101"
      > </a
      ><a name="24102" class="Symbol"
      >:</a
      ><a name="24103"
      > </a
      ><a name="24104" class="Symbol"
      >&#8704;</a
      ><a name="24105"
      > </a
      ><a name="24106" class="Symbol"
      >{</a
      ><a name="24107" href="StlcProp.html#24107" class="Bound"
      >M</a
      ><a name="24108"
      > </a
      ><a name="24109" href="StlcProp.html#24109" class="Bound"
      >N</a
      ><a name="24110"
      > </a
      ><a name="24111" href="StlcProp.html#24111" class="Bound"
      >A</a
      ><a name="24112" class="Symbol"
      >}</a
      ><a name="24113"
      > </a
      ><a name="24114" class="Symbol"
      >&#8594;</a
      ><a name="24115"
      > </a
      ><a name="24116" href="Maps.html#10265" class="Function"
      >&#8709;</a
      ><a name="24117"
      > </a
      ><a name="24118" href="Stlc.html#21569" class="Datatype Operator"
      >&#8866;</a
      ><a name="24119"
      > </a
      ><a name="24120" href="StlcProp.html#24107" class="Bound"
      >M</a
      ><a name="24121"
      > </a
      ><a name="24122" href="Stlc.html#21569" class="Datatype Operator"
      >&#8758;</a
      ><a name="24123"
      > </a
      ><a name="24124" href="StlcProp.html#24111" class="Bound"
      >A</a
      ><a name="24125"
      > </a
      ><a name="24126" class="Symbol"
      >&#8594;</a
      ><a name="24127"
      > </a
      ><a name="24128" href="StlcProp.html#24107" class="Bound"
      >M</a
      ><a name="24129"
      > </a
      ><a name="24130" href="Stlc.html#17866" class="Datatype Operator"
      >&#10233;*</a
      ><a name="24132"
      > </a
      ><a name="24133" href="StlcProp.html#24109" class="Bound"
      >N</a
      ><a name="24134"
      > </a
      ><a name="24135" class="Symbol"
      >&#8594;</a
      ><a name="24136"
      > </a
      ><a name="24137" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#414" class="Function Operator"
      >&#172;</a
      ><a name="24138"
      > </a
      ><a name="24139" class="Symbol"
      >(</a
      ><a name="24140" href="StlcProp.html#23925" class="Function"
      >Stuck</a
      ><a name="24145"
      > </a
      ><a name="24146" href="StlcProp.html#24109" class="Bound"
      >N</a
      ><a name="24147" class="Symbol"
      >)</a
      ><a name="24148"
      >
</a
      ><a name="24149" href="StlcProp.html#24091" class="Function"
      >Soundness&#8242;</a
      ><a name="24159"
      > </a
      ><a name="24160" href="StlcProp.html#24160" class="Bound"
      >&#8866;M</a
      ><a name="24162"
      > </a
      ><a name="24163" class="Symbol"
      >(</a
      ><a name="24164" href="StlcProp.html#24164" class="Bound"
      >M</a
      ><a name="24165"
      > </a
      ><a name="24166" href="Stlc.html#17899" class="InductiveConstructor Operator"
      >&#8718;</a
      ><a name="24167" class="Symbol"
      >)</a
      ><a name="24168"
      > </a
      ><a name="24169" class="Symbol"
      >(</a
      ><a name="24170" href="StlcProp.html#24170" class="Bound"
      >&#172;M&#10233;N</a
      ><a name="24174"
      > </a
      ><a name="24175" href="https://agda.github.io/agda-stdlib/Data.Product.html#509" class="InductiveConstructor Operator"
      >,</a
      ><a name="24176"
      > </a
      ><a name="24177" href="StlcProp.html#24177" class="Bound"
      >&#172;ValueM</a
      ><a name="24184" class="Symbol"
      >)</a
      ><a name="24185"
      > </a
      ><a name="24186" class="Keyword"
      >with</a
      ><a name="24190"
      > </a
      ><a name="24191" href="StlcProp.html#2085" class="Function"
      >progress</a
      ><a name="24199"
      > </a
      ><a name="24200" href="StlcProp.html#24160" class="Bound"
      >&#8866;M</a
      ><a name="24202"
      >
</a
      ><a name="24203" class="Symbol"
      >...</a
      ><a name="24206"
      > </a
      ><a name="24207" class="Symbol"
      >|</a
      ><a name="24208"
      > </a
      ><a name="24209" href="StlcProp.html#2008" class="InductiveConstructor"
      >steps</a
      ><a name="24214"
      > </a
      ><a name="24215" href="StlcProp.html#24215" class="Bound"
      >M&#10233;N</a
      ><a name="24218"
      >  </a
      ><a name="24220" class="Symbol"
      >=</a
      ><a name="24221"
      > </a
      ><a name="24222" href="StlcProp.html#24170" class="Bound"
      >&#172;M&#10233;N</a
      ><a name="24226"
      > </a
      ><a name="24227" href="StlcProp.html#24215" class="Bound"
      >M&#10233;N</a
      ><a name="24230"
      >
</a
      ><a name="24231" class="Symbol"
      >...</a
      ><a name="24234"
      > </a
      ><a name="24235" class="Symbol"
      >|</a
      ><a name="24236"
      > </a
      ><a name="24237" href="StlcProp.html#2047" class="InductiveConstructor"
      >done</a
      ><a name="24241"
      > </a
      ><a name="24242" href="StlcProp.html#24242" class="Bound"
      >ValueM</a
      ><a name="24248"
      >  </a
      ><a name="24250" class="Symbol"
      >=</a
      ><a name="24251"
      > </a
      ><a name="24252" href="StlcProp.html#24177" class="Bound"
      >&#172;ValueM</a
      ><a name="24259"
      > </a
      ><a name="24260" href="StlcProp.html#24242" class="Bound"
      >ValueM</a
      ><a name="24266"
      >
</a
      ><a name="24267" href="StlcProp.html#24091" class="Function"
      >Soundness&#8242;</a
      ><a name="24277"
      > </a
      ><a name="24278" class="Symbol"
      >{</a
      ><a name="24279" href="StlcProp.html#24279" class="Bound"
      >L</a
      ><a name="24280" class="Symbol"
      >}</a
      ><a name="24281"
      > </a
      ><a name="24282" class="Symbol"
      >{</a
      ><a name="24283" href="StlcProp.html#24283" class="Bound"
      >N</a
      ><a name="24284" class="Symbol"
      >}</a
      ><a name="24285"
      > </a
      ><a name="24286" class="Symbol"
      >{</a
      ><a name="24287" href="StlcProp.html#24287" class="Bound"
      >A</a
      ><a name="24288" class="Symbol"
      >}</a
      ><a name="24289"
      > </a
      ><a name="24290" href="StlcProp.html#24290" class="Bound"
      >&#8866;L</a
      ><a name="24292"
      > </a
      ><a name="24293" class="Symbol"
      >(</a
      ><a name="24294" href="Stlc.html#17919" class="InductiveConstructor Operator"
      >_&#10233;&#10216;_&#10217;_</a
      ><a name="24300"
      > </a
      ><a name="24301" class="DottedPattern Symbol"
      >.</a
      ><a name="24302" href="StlcProp.html#24279" class="DottedPattern Bound"
      >L</a
      ><a name="24303"
      > </a
      ><a name="24304" class="Symbol"
      >{</a
      ><a name="24305" href="StlcProp.html#24305" class="Bound"
      >M</a
      ><a name="24306" class="Symbol"
      >}</a
      ><a name="24307"
      > </a
      ><a name="24308" class="Symbol"
      >{</a
      ><a name="24309" class="DottedPattern Symbol"
      >.</a
      ><a name="24310" href="StlcProp.html#24283" class="DottedPattern Bound"
      >N</a
      ><a name="24311" class="Symbol"
      >}</a
      ><a name="24312"
      > </a
      ><a name="24313" href="StlcProp.html#24313" class="Bound"
      >L&#10233;M</a
      ><a name="24316"
      > </a
      ><a name="24317" href="StlcProp.html#24317" class="Bound"
      >M&#10233;*N</a
      ><a name="24321" class="Symbol"
      >)</a
      ><a name="24322"
      > </a
      ><a name="24323" class="Symbol"
      >=</a
      ><a name="24324"
      > </a
      ><a name="24325" href="StlcProp.html#24091" class="Function"
      >Soundness&#8242;</a
      ><a name="24335"
      > </a
      ><a name="24336" href="StlcProp.html#24354" class="Function"
      >&#8866;M</a
      ><a name="24338"
      > </a
      ><a name="24339" href="StlcProp.html#24317" class="Bound"
      >M&#10233;*N</a
      ><a name="24343"
      >
  </a
      ><a name="24346" class="Keyword"
      >where</a
      ><a name="24351"
      >
  </a
      ><a name="24354" href="StlcProp.html#24354" class="Function"
      >&#8866;M</a
      ><a name="24356"
      > </a
      ><a name="24357" class="Symbol"
      >:</a
      ><a name="24358"
      > </a
      ><a name="24359" href="Maps.html#10265" class="Function"
      >&#8709;</a
      ><a name="24360"
      > </a
      ><a name="24361" href="Stlc.html#21569" class="Datatype Operator"
      >&#8866;</a
      ><a name="24362"
      > </a
      ><a name="24363" href="StlcProp.html#24305" class="Bound"
      >M</a
      ><a name="24364"
      > </a
      ><a name="24365" href="Stlc.html#21569" class="Datatype Operator"
      >&#8758;</a
      ><a name="24366"
      > </a
      ><a name="24367" href="StlcProp.html#24287" class="Bound"
      >A</a
      ><a name="24368"
      >
  </a
      ><a name="24371" href="StlcProp.html#24354" class="Function"
      >&#8866;M</a
      ><a name="24373"
      > </a
      ><a name="24374" class="Symbol"
      >=</a
      ><a name="24375"
      > </a
      ><a name="24376" href="StlcProp.html#21028" class="Function"
      >preservation</a
      ><a name="24388"
      > </a
      ><a name="24389" href="StlcProp.html#24290" class="Bound"
      >&#8866;L</a
      ><a name="24391"
      > </a
      ><a name="24392" href="StlcProp.html#24313" class="Bound"
      >L&#10233;M</a
      >

</pre>
</div>


## Uniqueness of Types

#### Exercise: 3 stars (types_unique)

Another nice property of the STLC is that types are unique: a
given term (in a given context) has at most one type.
Formalize this statement and prove it.


## Additional Exercises

#### Exercise: 1 star (progress_preservation_statement)

Without peeking at their statements above, write down the progress
and preservation theorems for the simply typed lambda-calculus.

#### Exercise: 2 stars (stlc_variation1)

Suppose we add a new term `zap` with the following reduction rule

                     ---------                  (ST_Zap)
                     M ⟹ zap

and the following typing rule:

                    -----------                 (T_Zap)
                    Γ ⊢ zap : A

Which of the following properties of the STLC remain true in
the presence of these rules?  For each property, write either
"remains true" or "becomes false." If a property becomes
false, give a counterexample.

  - Determinism of `step`

  - Progress

  - Preservation


#### Exercise: 2 stars (stlc_variation2)

Suppose instead that we add a new term `foo` with the following
reduction rules:

                 ----------------------             (ST_Foo1)
                 (λ[ x ∶ A ] ` x) ⟹ foo

                     -----------                    (ST_Foo2)
                     foo ⟹ true

Which of the following properties of the STLC remain true in
the presence of this rule?  For each one, write either
"remains true" or else "becomes false." If a property becomes
false, give a counterexample.

  - Determinism of `step`

  - Progress

  - Preservation

#### Exercise: 2 stars (stlc_variation3)

Suppose instead that we remove the rule `ξ·₁` from the `⟹`
relation. Which of the following properties of the STLC remain
true in the absence of this rule?  For each one, write either
"remains true" or else "becomes false." If a property becomes
false, give a counterexample.

  - Determinism of `step`

  - Progress

  - Preservation

#### Exercise: 2 stars, optional (stlc_variation4)
Suppose instead that we add the following new rule to the
reduction relation:

        ----------------------------------        (ST_FunnyIfTrue)
        (if true then t_1 else t_2) ⟹ true

Which of the following properties of the STLC remain true in
the presence of this rule?  For each one, write either
"remains true" or else "becomes false." If a property becomes
false, give a counterexample.

  - Determinism of `step`

  - Progress

  - Preservation


#### Exercise: 2 stars, optional (stlc_variation5)

Suppose instead that we add the following new rule to the typing
relation:

             Γ ⊢ L ∶ 𝔹 ⇒ 𝔹 ⇒ 𝔹
             Γ ⊢ M ∶ 𝔹
             ------------------------------          (T_FunnyApp)
             Γ ⊢ L · M ∶ 𝔹

Which of the following properties of the STLC remain true in
the presence of this rule?  For each one, write either
"remains true" or else "becomes false." If a property becomes
false, give a counterexample.

  - Determinism of `step`

  - Progress

  - Preservation



#### Exercise: 2 stars, optional (stlc_variation6)
Suppose instead that we add the following new rule to the typing
relation:

                Γ ⊢ L ∶ 𝔹
                Γ ⊢ M ∶ 𝔹
                ---------------------               (T_FunnyApp')
                Γ ⊢ L · M ∶ 𝔹

Which of the following properties of the STLC remain true in
the presence of this rule?  For each one, write either
"remains true" or else "becomes false." If a property becomes
false, give a counterexample.

  - Determinism of `step`

  - Progress

  - Preservation



#### Exercise: 2 stars, optional (stlc_variation7)

Suppose we add the following new rule to the typing relation
of the STLC:

                --------------------              (T_FunnyAbs)
                ∅ ⊢ λ[ x ∶ 𝔹 ] N ∶ 𝔹

Which of the following properties of the STLC remain true in
the presence of this rule?  For each one, write either
"remains true" or else "becomes false." If a property becomes
false, give a counterexample.

  - Determinism of `step`

  - Progress

  - Preservation


### Exercise: STLC with Arithmetic

To see how the STLC might function as the core of a real
programming language, let's extend it with a concrete base
type of numbers and some constants and primitive
operators.

To types, we add a base type of numbers (and remove
booleans, for brevity).

<pre class="Agda">

<a name="28808" class="Keyword"
      >data</a
      ><a name="28812"
      > </a
      ><a name="28813" href="StlcProp.html#28813" class="Datatype"
      >Type&#8242;</a
      ><a name="28818"
      > </a
      ><a name="28819" class="Symbol"
      >:</a
      ><a name="28820"
      > </a
      ><a name="28821" class="PrimitiveType"
      >Set</a
      ><a name="28824"
      > </a
      ><a name="28825" class="Keyword"
      >where</a
      ><a name="28830"
      >
  </a
      ><a name="28833" href="StlcProp.html#28833" class="InductiveConstructor Operator"
      >_&#8658;_</a
      ><a name="28836"
      > </a
      ><a name="28837" class="Symbol"
      >:</a
      ><a name="28838"
      > </a
      ><a name="28839" href="StlcProp.html#28813" class="Datatype"
      >Type&#8242;</a
      ><a name="28844"
      > </a
      ><a name="28845" class="Symbol"
      >&#8594;</a
      ><a name="28846"
      > </a
      ><a name="28847" href="StlcProp.html#28813" class="Datatype"
      >Type&#8242;</a
      ><a name="28852"
      > </a
      ><a name="28853" class="Symbol"
      >&#8594;</a
      ><a name="28854"
      > </a
      ><a name="28855" href="StlcProp.html#28813" class="Datatype"
      >Type&#8242;</a
      ><a name="28860"
      >
  </a
      ><a name="28863" href="StlcProp.html#28863" class="InductiveConstructor"
      >&#8469;</a
      ><a name="28864"
      > </a
      ><a name="28865" class="Symbol"
      >:</a
      ><a name="28866"
      > </a
      ><a name="28867" href="StlcProp.html#28813" class="Datatype"
      >Type&#8242;</a
      >

</pre>

To terms, we add natural number constants, along with
plus, minus, and testing for zero.

<pre class="Agda">

<a name="28988" class="Keyword"
      >data</a
      ><a name="28992"
      > </a
      ><a name="28993" href="StlcProp.html#28993" class="Datatype"
      >Term&#8242;</a
      ><a name="28998"
      > </a
      ><a name="28999" class="Symbol"
      >:</a
      ><a name="29000"
      > </a
      ><a name="29001" class="PrimitiveType"
      >Set</a
      ><a name="29004"
      > </a
      ><a name="29005" class="Keyword"
      >where</a
      ><a name="29010"
      >
  </a
      ><a name="29013" href="StlcProp.html#29013" class="InductiveConstructor Operator"
      >`_</a
      ><a name="29015"
      > </a
      ><a name="29016" class="Symbol"
      >:</a
      ><a name="29017"
      > </a
      ><a name="29018" href="Maps.html#2171" class="Datatype"
      >Id</a
      ><a name="29020"
      > </a
      ><a name="29021" class="Symbol"
      >&#8594;</a
      ><a name="29022"
      > </a
      ><a name="29023" href="StlcProp.html#28993" class="Datatype"
      >Term&#8242;</a
      ><a name="29028"
      >
  </a
      ><a name="29031" href="StlcProp.html#29031" class="InductiveConstructor Operator"
      >&#955;[_&#8758;_]_</a
      ><a name="29038"
      > </a
      ><a name="29039" class="Symbol"
      >:</a
      ><a name="29040"
      > </a
      ><a name="29041" href="Maps.html#2171" class="Datatype"
      >Id</a
      ><a name="29043"
      > </a
      ><a name="29044" class="Symbol"
      >&#8594;</a
      ><a name="29045"
      > </a
      ><a name="29046" href="StlcProp.html#28813" class="Datatype"
      >Type&#8242;</a
      ><a name="29051"
      > </a
      ><a name="29052" class="Symbol"
      >&#8594;</a
      ><a name="29053"
      > </a
      ><a name="29054" href="StlcProp.html#28993" class="Datatype"
      >Term&#8242;</a
      ><a name="29059"
      > </a
      ><a name="29060" class="Symbol"
      >&#8594;</a
      ><a name="29061"
      > </a
      ><a name="29062" href="StlcProp.html#28993" class="Datatype"
      >Term&#8242;</a
      ><a name="29067"
      >
  </a
      ><a name="29070" href="StlcProp.html#29070" class="InductiveConstructor Operator"
      >_&#183;_</a
      ><a name="29073"
      > </a
      ><a name="29074" class="Symbol"
      >:</a
      ><a name="29075"
      > </a
      ><a name="29076" href="StlcProp.html#28993" class="Datatype"
      >Term&#8242;</a
      ><a name="29081"
      > </a
      ><a name="29082" class="Symbol"
      >&#8594;</a
      ><a name="29083"
      > </a
      ><a name="29084" href="StlcProp.html#28993" class="Datatype"
      >Term&#8242;</a
      ><a name="29089"
      > </a
      ><a name="29090" class="Symbol"
      >&#8594;</a
      ><a name="29091"
      > </a
      ><a name="29092" href="StlcProp.html#28993" class="Datatype"
      >Term&#8242;</a
      ><a name="29097"
      >
  </a
      ><a name="29100" href="StlcProp.html#29100" class="InductiveConstructor Operator"
      >#_</a
      ><a name="29102"
      > </a
      ><a name="29103" class="Symbol"
      >:</a
      ><a name="29104"
      > </a
      ><a name="29105" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#97" class="Datatype"
      >Data.Nat.&#8469;</a
      ><a name="29115"
      > </a
      ><a name="29116" class="Symbol"
      >&#8594;</a
      ><a name="29117"
      > </a
      ><a name="29118" href="StlcProp.html#28993" class="Datatype"
      >Term&#8242;</a
      ><a name="29123"
      >
  </a
      ><a name="29126" href="StlcProp.html#29126" class="InductiveConstructor Operator"
      >_+_</a
      ><a name="29129"
      > </a
      ><a name="29130" class="Symbol"
      >:</a
      ><a name="29131"
      > </a
      ><a name="29132" href="StlcProp.html#28993" class="Datatype"
      >Term&#8242;</a
      ><a name="29137"
      > </a
      ><a name="29138" class="Symbol"
      >&#8594;</a
      ><a name="29139"
      > </a
      ><a name="29140" href="StlcProp.html#28993" class="Datatype"
      >Term&#8242;</a
      ><a name="29145"
      > </a
      ><a name="29146" class="Symbol"
      >&#8594;</a
      ><a name="29147"
      > </a
      ><a name="29148" href="StlcProp.html#28993" class="Datatype"
      >Term&#8242;</a
      ><a name="29153"
      >
  </a
      ><a name="29156" href="StlcProp.html#29156" class="InductiveConstructor Operator"
      >_-_</a
      ><a name="29159"
      > </a
      ><a name="29160" class="Symbol"
      >:</a
      ><a name="29161"
      > </a
      ><a name="29162" href="StlcProp.html#28993" class="Datatype"
      >Term&#8242;</a
      ><a name="29167"
      > </a
      ><a name="29168" class="Symbol"
      >&#8594;</a
      ><a name="29169"
      > </a
      ><a name="29170" href="StlcProp.html#28993" class="Datatype"
      >Term&#8242;</a
      ><a name="29175"
      > </a
      ><a name="29176" class="Symbol"
      >&#8594;</a
      ><a name="29177"
      > </a
      ><a name="29178" href="StlcProp.html#28993" class="Datatype"
      >Term&#8242;</a
      ><a name="29183"
      >
  </a
      ><a name="29186" href="StlcProp.html#29186" class="InductiveConstructor Operator"
      >if0_then_else_</a
      ><a name="29200"
      > </a
      ><a name="29201" class="Symbol"
      >:</a
      ><a name="29202"
      > </a
      ><a name="29203" href="StlcProp.html#28993" class="Datatype"
      >Term&#8242;</a
      ><a name="29208"
      > </a
      ><a name="29209" class="Symbol"
      >&#8594;</a
      ><a name="29210"
      > </a
      ><a name="29211" href="StlcProp.html#28993" class="Datatype"
      >Term&#8242;</a
      ><a name="29216"
      > </a
      ><a name="29217" class="Symbol"
      >&#8594;</a
      ><a name="29218"
      > </a
      ><a name="29219" href="StlcProp.html#28993" class="Datatype"
      >Term&#8242;</a
      ><a name="29224"
      > </a
      ><a name="29225" class="Symbol"
      >&#8594;</a
      ><a name="29226"
      > </a
      ><a name="29227" href="StlcProp.html#28993" class="Datatype"
      >Term&#8242;</a
      >

</pre>

(Assume that `m - n` returns `0` if `m` is less than `n`.)

#### Exercise: 4 stars (stlc_arith)

Finish formalizing the definition and properties of the STLC extended
with arithmetic.  Specifically:

  - Copy the whole development of STLC that we went through above (from
    the definition of values through the Type Soundness theorem), and
    paste it into the file at this point.

  - Extend the definitions of the `subst` operation and the `step`
     relation to include appropriate clauses for the arithmetic operators.

  - Extend the proofs of all the properties (up to `soundness`) of
    the original STLC to deal with the new syntactic forms.  Make
    sure Agda accepts the whole file.

