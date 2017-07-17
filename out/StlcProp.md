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

As we saw for the simple calculus in Chapter [Types]({{ "Types" | relative_url }}),
the first step in establishing basic properties of reduction and typing
is to identify the possible _canonical forms_ (i.e., well-typed closed values)
belonging to each type.  For function types the canonical forms are lambda-abstractions,
while for boolean types they are values `true` and `false`.  

<pre class="Agda">

<a name="1264" class="Keyword"
      >data</a
      ><a name="1268"
      > </a
      ><a name="1269" href="StlcProp.html#1269" class="Datatype Operator"
      >canonical_for_</a
      ><a name="1283"
      > </a
      ><a name="1284" class="Symbol"
      >:</a
      ><a name="1285"
      > </a
      ><a name="1286" href="Stlc.html#3628" class="Datatype"
      >Term</a
      ><a name="1290"
      > </a
      ><a name="1291" class="Symbol"
      >&#8594;</a
      ><a name="1292"
      > </a
      ><a name="1293" href="Stlc.html#2555" class="Datatype"
      >Type</a
      ><a name="1297"
      > </a
      ><a name="1298" class="Symbol"
      >&#8594;</a
      ><a name="1299"
      > </a
      ><a name="1300" class="PrimitiveType"
      >Set</a
      ><a name="1303"
      > </a
      ><a name="1304" class="Keyword"
      >where</a
      ><a name="1309"
      >
  </a
      ><a name="1312" href="StlcProp.html#1312" class="InductiveConstructor"
      >canonical-&#955;</a
      ><a name="1323"
      > </a
      ><a name="1324" class="Symbol"
      >:</a
      ><a name="1325"
      > </a
      ><a name="1326" class="Symbol"
      >&#8704;</a
      ><a name="1327"
      > </a
      ><a name="1328" class="Symbol"
      >{</a
      ><a name="1329" href="StlcProp.html#1329" class="Bound"
      >x</a
      ><a name="1330"
      > </a
      ><a name="1331" href="StlcProp.html#1331" class="Bound"
      >A</a
      ><a name="1332"
      > </a
      ><a name="1333" href="StlcProp.html#1333" class="Bound"
      >N</a
      ><a name="1334"
      > </a
      ><a name="1335" href="StlcProp.html#1335" class="Bound"
      >B</a
      ><a name="1336" class="Symbol"
      >}</a
      ><a name="1337"
      > </a
      ><a name="1338" class="Symbol"
      >&#8594;</a
      ><a name="1339"
      > </a
      ><a name="1340" href="StlcProp.html#1269" class="Datatype Operator"
      >canonical</a
      ><a name="1349"
      > </a
      ><a name="1350" class="Symbol"
      >(</a
      ><a name="1351" href="Stlc.html#3663" class="InductiveConstructor Operator"
      >&#955;[</a
      ><a name="1353"
      > </a
      ><a name="1354" href="StlcProp.html#1329" class="Bound"
      >x</a
      ><a name="1355"
      > </a
      ><a name="1356" href="Stlc.html#3663" class="InductiveConstructor Operator"
      >&#8758;</a
      ><a name="1357"
      > </a
      ><a name="1358" href="StlcProp.html#1331" class="Bound"
      >A</a
      ><a name="1359"
      > </a
      ><a name="1360" href="Stlc.html#3663" class="InductiveConstructor Operator"
      >]</a
      ><a name="1361"
      > </a
      ><a name="1362" href="StlcProp.html#1333" class="Bound"
      >N</a
      ><a name="1363" class="Symbol"
      >)</a
      ><a name="1364"
      > </a
      ><a name="1365" href="StlcProp.html#1269" class="Datatype Operator"
      >for</a
      ><a name="1368"
      > </a
      ><a name="1369" class="Symbol"
      >(</a
      ><a name="1370" href="StlcProp.html#1331" class="Bound"
      >A</a
      ><a name="1371"
      > </a
      ><a name="1372" href="Stlc.html#2574" class="InductiveConstructor Operator"
      >&#8658;</a
      ><a name="1373"
      > </a
      ><a name="1374" href="StlcProp.html#1335" class="Bound"
      >B</a
      ><a name="1375" class="Symbol"
      >)</a
      ><a name="1376"
      >
  </a
      ><a name="1379" href="StlcProp.html#1379" class="InductiveConstructor"
      >canonical-true</a
      ><a name="1393"
      > </a
      ><a name="1394" class="Symbol"
      >:</a
      ><a name="1395"
      > </a
      ><a name="1396" href="StlcProp.html#1269" class="Datatype Operator"
      >canonical</a
      ><a name="1405"
      > </a
      ><a name="1406" href="Stlc.html#3726" class="InductiveConstructor"
      >true</a
      ><a name="1410"
      > </a
      ><a name="1411" href="StlcProp.html#1269" class="Datatype Operator"
      >for</a
      ><a name="1414"
      > </a
      ><a name="1415" href="Stlc.html#2601" class="InductiveConstructor"
      >&#120121;</a
      ><a name="1416"
      >
  </a
      ><a name="1419" href="StlcProp.html#1419" class="InductiveConstructor"
      >canonical-false</a
      ><a name="1434"
      > </a
      ><a name="1435" class="Symbol"
      >:</a
      ><a name="1436"
      > </a
      ><a name="1437" href="StlcProp.html#1269" class="Datatype Operator"
      >canonical</a
      ><a name="1446"
      > </a
      ><a name="1447" href="Stlc.html#3740" class="InductiveConstructor"
      >false</a
      ><a name="1452"
      > </a
      ><a name="1453" href="StlcProp.html#1269" class="Datatype Operator"
      >for</a
      ><a name="1456"
      > </a
      ><a name="1457" href="Stlc.html#2601" class="InductiveConstructor"
      >&#120121;</a
      ><a name="1458"
      >

</a
      ><a name="1460" href="StlcProp.html#1460" class="Function"
      >canonical-forms</a
      ><a name="1475"
      > </a
      ><a name="1476" class="Symbol"
      >:</a
      ><a name="1477"
      > </a
      ><a name="1478" class="Symbol"
      >&#8704;</a
      ><a name="1479"
      > </a
      ><a name="1480" class="Symbol"
      >{</a
      ><a name="1481" href="StlcProp.html#1481" class="Bound"
      >L</a
      ><a name="1482"
      > </a
      ><a name="1483" href="StlcProp.html#1483" class="Bound"
      >A</a
      ><a name="1484" class="Symbol"
      >}</a
      ><a name="1485"
      > </a
      ><a name="1486" class="Symbol"
      >&#8594;</a
      ><a name="1487"
      > </a
      ><a name="1488" href="Maps.html#10265" class="Function"
      >&#8709;</a
      ><a name="1489"
      > </a
      ><a name="1490" href="Stlc.html#21560" class="Datatype Operator"
      >&#8866;</a
      ><a name="1491"
      > </a
      ><a name="1492" href="StlcProp.html#1481" class="Bound"
      >L</a
      ><a name="1493"
      > </a
      ><a name="1494" href="Stlc.html#21560" class="Datatype Operator"
      >&#8758;</a
      ><a name="1495"
      > </a
      ><a name="1496" href="StlcProp.html#1483" class="Bound"
      >A</a
      ><a name="1497"
      > </a
      ><a name="1498" class="Symbol"
      >&#8594;</a
      ><a name="1499"
      > </a
      ><a name="1500" href="Stlc.html#9526" class="Datatype"
      >Value</a
      ><a name="1505"
      > </a
      ><a name="1506" href="StlcProp.html#1481" class="Bound"
      >L</a
      ><a name="1507"
      > </a
      ><a name="1508" class="Symbol"
      >&#8594;</a
      ><a name="1509"
      > </a
      ><a name="1510" href="StlcProp.html#1269" class="Datatype Operator"
      >canonical</a
      ><a name="1519"
      > </a
      ><a name="1520" href="StlcProp.html#1481" class="Bound"
      >L</a
      ><a name="1521"
      > </a
      ><a name="1522" href="StlcProp.html#1269" class="Datatype Operator"
      >for</a
      ><a name="1525"
      > </a
      ><a name="1526" href="StlcProp.html#1483" class="Bound"
      >A</a
      ><a name="1527"
      >
</a
      ><a name="1528" href="StlcProp.html#1460" class="Function"
      >canonical-forms</a
      ><a name="1543"
      > </a
      ><a name="1544" class="Symbol"
      >(</a
      ><a name="1545" href="Stlc.html#21604" class="InductiveConstructor"
      >Ax</a
      ><a name="1547"
      > </a
      ><a name="1548" class="Symbol"
      >())</a
      ><a name="1551"
      > </a
      ><a name="1552" class="Symbol"
      >()</a
      ><a name="1554"
      >
</a
      ><a name="1555" href="StlcProp.html#1460" class="Function"
      >canonical-forms</a
      ><a name="1570"
      > </a
      ><a name="1571" class="Symbol"
      >(</a
      ><a name="1572" href="Stlc.html#21658" class="InductiveConstructor"
      >&#8658;-I</a
      ><a name="1575"
      > </a
      ><a name="1576" href="StlcProp.html#1576" class="Bound"
      >&#8866;N</a
      ><a name="1578" class="Symbol"
      >)</a
      ><a name="1579"
      > </a
      ><a name="1580" href="Stlc.html#9553" class="InductiveConstructor"
      >value-&#955;</a
      ><a name="1587"
      > </a
      ><a name="1588" class="Symbol"
      >=</a
      ><a name="1589"
      > </a
      ><a name="1590" href="StlcProp.html#1312" class="InductiveConstructor"
      >canonical-&#955;</a
      ><a name="1601"
      >
</a
      ><a name="1602" href="StlcProp.html#1460" class="Function"
      >canonical-forms</a
      ><a name="1617"
      > </a
      ><a name="1618" class="Symbol"
      >(</a
      ><a name="1619" href="Stlc.html#21735" class="InductiveConstructor"
      >&#8658;-E</a
      ><a name="1622"
      > </a
      ><a name="1623" href="StlcProp.html#1623" class="Bound"
      >&#8866;L</a
      ><a name="1625"
      > </a
      ><a name="1626" href="StlcProp.html#1626" class="Bound"
      >&#8866;M</a
      ><a name="1628" class="Symbol"
      >)</a
      ><a name="1629"
      > </a
      ><a name="1630" class="Symbol"
      >()</a
      ><a name="1632"
      >
</a
      ><a name="1633" href="StlcProp.html#1460" class="Function"
      >canonical-forms</a
      ><a name="1648"
      > </a
      ><a name="1649" href="Stlc.html#21813" class="InductiveConstructor"
      >&#120121;-I&#8321;</a
      ><a name="1653"
      > </a
      ><a name="1654" href="Stlc.html#9602" class="InductiveConstructor"
      >value-true</a
      ><a name="1664"
      > </a
      ><a name="1665" class="Symbol"
      >=</a
      ><a name="1666"
      > </a
      ><a name="1667" href="StlcProp.html#1379" class="InductiveConstructor"
      >canonical-true</a
      ><a name="1681"
      >
</a
      ><a name="1682" href="StlcProp.html#1460" class="Function"
      >canonical-forms</a
      ><a name="1697"
      > </a
      ><a name="1698" href="Stlc.html#21847" class="InductiveConstructor"
      >&#120121;-I&#8322;</a
      ><a name="1702"
      > </a
      ><a name="1703" href="Stlc.html#9629" class="InductiveConstructor"
      >value-false</a
      ><a name="1714"
      > </a
      ><a name="1715" class="Symbol"
      >=</a
      ><a name="1716"
      > </a
      ><a name="1717" href="StlcProp.html#1419" class="InductiveConstructor"
      >canonical-false</a
      ><a name="1732"
      >
</a
      ><a name="1733" href="StlcProp.html#1460" class="Function"
      >canonical-forms</a
      ><a name="1748"
      > </a
      ><a name="1749" class="Symbol"
      >(</a
      ><a name="1750" href="Stlc.html#21882" class="InductiveConstructor"
      >&#120121;-E</a
      ><a name="1753"
      > </a
      ><a name="1754" href="StlcProp.html#1754" class="Bound"
      >&#8866;L</a
      ><a name="1756"
      > </a
      ><a name="1757" href="StlcProp.html#1757" class="Bound"
      >&#8866;M</a
      ><a name="1759"
      > </a
      ><a name="1760" href="StlcProp.html#1760" class="Bound"
      >&#8866;N</a
      ><a name="1762" class="Symbol"
      >)</a
      ><a name="1763"
      > </a
      ><a name="1764" class="Symbol"
      >()</a
      >

</pre>

## Progress

As before, the _progress_ theorem tells us that closed, well-typed
terms are not stuck: either a well-typed term can take a reduction
step or it is a value.

<pre class="Agda">

<a name="1963" class="Keyword"
      >data</a
      ><a name="1967"
      > </a
      ><a name="1968" href="StlcProp.html#1968" class="Datatype"
      >Progress</a
      ><a name="1976"
      > </a
      ><a name="1977" class="Symbol"
      >:</a
      ><a name="1978"
      > </a
      ><a name="1979" href="Stlc.html#3628" class="Datatype"
      >Term</a
      ><a name="1983"
      > </a
      ><a name="1984" class="Symbol"
      >&#8594;</a
      ><a name="1985"
      > </a
      ><a name="1986" class="PrimitiveType"
      >Set</a
      ><a name="1989"
      > </a
      ><a name="1990" class="Keyword"
      >where</a
      ><a name="1995"
      >
  </a
      ><a name="1998" href="StlcProp.html#1998" class="InductiveConstructor"
      >steps</a
      ><a name="2003"
      > </a
      ><a name="2004" class="Symbol"
      >:</a
      ><a name="2005"
      > </a
      ><a name="2006" class="Symbol"
      >&#8704;</a
      ><a name="2007"
      > </a
      ><a name="2008" class="Symbol"
      >{</a
      ><a name="2009" href="StlcProp.html#2009" class="Bound"
      >M</a
      ><a name="2010"
      > </a
      ><a name="2011" href="StlcProp.html#2011" class="Bound"
      >N</a
      ><a name="2012" class="Symbol"
      >}</a
      ><a name="2013"
      > </a
      ><a name="2014" class="Symbol"
      >&#8594;</a
      ><a name="2015"
      > </a
      ><a name="2016" href="StlcProp.html#2009" class="Bound"
      >M</a
      ><a name="2017"
      > </a
      ><a name="2018" href="Stlc.html#15823" class="Datatype Operator"
      >&#10233;</a
      ><a name="2019"
      > </a
      ><a name="2020" href="StlcProp.html#2011" class="Bound"
      >N</a
      ><a name="2021"
      > </a
      ><a name="2022" class="Symbol"
      >&#8594;</a
      ><a name="2023"
      > </a
      ><a name="2024" href="StlcProp.html#1968" class="Datatype"
      >Progress</a
      ><a name="2032"
      > </a
      ><a name="2033" href="StlcProp.html#2009" class="Bound"
      >M</a
      ><a name="2034"
      >
  </a
      ><a name="2037" href="StlcProp.html#2037" class="InductiveConstructor"
      >done</a
      ><a name="2041"
      >  </a
      ><a name="2043" class="Symbol"
      >:</a
      ><a name="2044"
      > </a
      ><a name="2045" class="Symbol"
      >&#8704;</a
      ><a name="2046"
      > </a
      ><a name="2047" class="Symbol"
      >{</a
      ><a name="2048" href="StlcProp.html#2048" class="Bound"
      >M</a
      ><a name="2049" class="Symbol"
      >}</a
      ><a name="2050"
      > </a
      ><a name="2051" class="Symbol"
      >&#8594;</a
      ><a name="2052"
      > </a
      ><a name="2053" href="Stlc.html#9526" class="Datatype"
      >Value</a
      ><a name="2058"
      > </a
      ><a name="2059" href="StlcProp.html#2048" class="Bound"
      >M</a
      ><a name="2060"
      > </a
      ><a name="2061" class="Symbol"
      >&#8594;</a
      ><a name="2062"
      > </a
      ><a name="2063" href="StlcProp.html#1968" class="Datatype"
      >Progress</a
      ><a name="2071"
      > </a
      ><a name="2072" href="StlcProp.html#2048" class="Bound"
      >M</a
      ><a name="2073"
      >

</a
      ><a name="2075" href="StlcProp.html#2075" class="Function"
      >progress</a
      ><a name="2083"
      > </a
      ><a name="2084" class="Symbol"
      >:</a
      ><a name="2085"
      > </a
      ><a name="2086" class="Symbol"
      >&#8704;</a
      ><a name="2087"
      > </a
      ><a name="2088" class="Symbol"
      >{</a
      ><a name="2089" href="StlcProp.html#2089" class="Bound"
      >M</a
      ><a name="2090"
      > </a
      ><a name="2091" href="StlcProp.html#2091" class="Bound"
      >A</a
      ><a name="2092" class="Symbol"
      >}</a
      ><a name="2093"
      > </a
      ><a name="2094" class="Symbol"
      >&#8594;</a
      ><a name="2095"
      > </a
      ><a name="2096" href="Maps.html#10265" class="Function"
      >&#8709;</a
      ><a name="2097"
      > </a
      ><a name="2098" href="Stlc.html#21560" class="Datatype Operator"
      >&#8866;</a
      ><a name="2099"
      > </a
      ><a name="2100" href="StlcProp.html#2089" class="Bound"
      >M</a
      ><a name="2101"
      > </a
      ><a name="2102" href="Stlc.html#21560" class="Datatype Operator"
      >&#8758;</a
      ><a name="2103"
      > </a
      ><a name="2104" href="StlcProp.html#2091" class="Bound"
      >A</a
      ><a name="2105"
      > </a
      ><a name="2106" class="Symbol"
      >&#8594;</a
      ><a name="2107"
      > </a
      ><a name="2108" href="StlcProp.html#1968" class="Datatype"
      >Progress</a
      ><a name="2116"
      > </a
      ><a name="2117" href="StlcProp.html#2089" class="Bound"
      >M</a
      >

</pre>

The proof is a relatively
straightforward extension of the progress proof we saw in
[Types]({{ "Types" | relative_url }}).
We give the proof in English
first, then the formal version.

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

<a name="3997" href="StlcProp.html#2075" class="Function"
      >progress</a
      ><a name="4005"
      > </a
      ><a name="4006" class="Symbol"
      >(</a
      ><a name="4007" href="Stlc.html#21604" class="InductiveConstructor"
      >Ax</a
      ><a name="4009"
      > </a
      ><a name="4010" class="Symbol"
      >())</a
      ><a name="4013"
      >
</a
      ><a name="4014" href="StlcProp.html#2075" class="Function"
      >progress</a
      ><a name="4022"
      > </a
      ><a name="4023" class="Symbol"
      >(</a
      ><a name="4024" href="Stlc.html#21658" class="InductiveConstructor"
      >&#8658;-I</a
      ><a name="4027"
      > </a
      ><a name="4028" href="StlcProp.html#4028" class="Bound"
      >&#8866;N</a
      ><a name="4030" class="Symbol"
      >)</a
      ><a name="4031"
      > </a
      ><a name="4032" class="Symbol"
      >=</a
      ><a name="4033"
      > </a
      ><a name="4034" href="StlcProp.html#2037" class="InductiveConstructor"
      >done</a
      ><a name="4038"
      > </a
      ><a name="4039" href="Stlc.html#9553" class="InductiveConstructor"
      >value-&#955;</a
      ><a name="4046"
      >
</a
      ><a name="4047" href="StlcProp.html#2075" class="Function"
      >progress</a
      ><a name="4055"
      > </a
      ><a name="4056" class="Symbol"
      >(</a
      ><a name="4057" href="Stlc.html#21735" class="InductiveConstructor"
      >&#8658;-E</a
      ><a name="4060"
      > </a
      ><a name="4061" href="StlcProp.html#4061" class="Bound"
      >&#8866;L</a
      ><a name="4063"
      > </a
      ><a name="4064" href="StlcProp.html#4064" class="Bound"
      >&#8866;M</a
      ><a name="4066" class="Symbol"
      >)</a
      ><a name="4067"
      > </a
      ><a name="4068" class="Keyword"
      >with</a
      ><a name="4072"
      > </a
      ><a name="4073" href="StlcProp.html#2075" class="Function"
      >progress</a
      ><a name="4081"
      > </a
      ><a name="4082" href="StlcProp.html#4061" class="Bound"
      >&#8866;L</a
      ><a name="4084"
      >
</a
      ><a name="4085" class="Symbol"
      >...</a
      ><a name="4088"
      > </a
      ><a name="4089" class="Symbol"
      >|</a
      ><a name="4090"
      > </a
      ><a name="4091" href="StlcProp.html#1998" class="InductiveConstructor"
      >steps</a
      ><a name="4096"
      > </a
      ><a name="4097" href="StlcProp.html#4097" class="Bound"
      >L&#10233;L&#8242;</a
      ><a name="4101"
      > </a
      ><a name="4102" class="Symbol"
      >=</a
      ><a name="4103"
      > </a
      ><a name="4104" href="StlcProp.html#1998" class="InductiveConstructor"
      >steps</a
      ><a name="4109"
      > </a
      ><a name="4110" class="Symbol"
      >(</a
      ><a name="4111" href="Stlc.html#15855" class="InductiveConstructor"
      >&#958;&#183;&#8321;</a
      ><a name="4114"
      > </a
      ><a name="4115" href="StlcProp.html#4097" class="Bound"
      >L&#10233;L&#8242;</a
      ><a name="4119" class="Symbol"
      >)</a
      ><a name="4120"
      >
</a
      ><a name="4121" class="Symbol"
      >...</a
      ><a name="4124"
      > </a
      ><a name="4125" class="Symbol"
      >|</a
      ><a name="4126"
      > </a
      ><a name="4127" href="StlcProp.html#2037" class="InductiveConstructor"
      >done</a
      ><a name="4131"
      > </a
      ><a name="4132" href="StlcProp.html#4132" class="Bound"
      >valueL</a
      ><a name="4138"
      > </a
      ><a name="4139" class="Keyword"
      >with</a
      ><a name="4143"
      > </a
      ><a name="4144" href="StlcProp.html#2075" class="Function"
      >progress</a
      ><a name="4152"
      > </a
      ><a name="4153" href="StlcProp.html#4064" class="Bound"
      >&#8866;M</a
      ><a name="4155"
      >
</a
      ><a name="4156" class="Symbol"
      >...</a
      ><a name="4159"
      > </a
      ><a name="4160" class="Symbol"
      >|</a
      ><a name="4161"
      > </a
      ><a name="4162" href="StlcProp.html#1998" class="InductiveConstructor"
      >steps</a
      ><a name="4167"
      > </a
      ><a name="4168" href="StlcProp.html#4168" class="Bound"
      >M&#10233;M&#8242;</a
      ><a name="4172"
      > </a
      ><a name="4173" class="Symbol"
      >=</a
      ><a name="4174"
      > </a
      ><a name="4175" href="StlcProp.html#1998" class="InductiveConstructor"
      >steps</a
      ><a name="4180"
      > </a
      ><a name="4181" class="Symbol"
      >(</a
      ><a name="4182" href="Stlc.html#15908" class="InductiveConstructor"
      >&#958;&#183;&#8322;</a
      ><a name="4185"
      > </a
      ><a name="4186" href="StlcProp.html#4132" class="Bound"
      >valueL</a
      ><a name="4192"
      > </a
      ><a name="4193" href="StlcProp.html#4168" class="Bound"
      >M&#10233;M&#8242;</a
      ><a name="4197" class="Symbol"
      >)</a
      ><a name="4198"
      >
</a
      ><a name="4199" class="Symbol"
      >...</a
      ><a name="4202"
      > </a
      ><a name="4203" class="Symbol"
      >|</a
      ><a name="4204"
      > </a
      ><a name="4205" href="StlcProp.html#2037" class="InductiveConstructor"
      >done</a
      ><a name="4209"
      > </a
      ><a name="4210" href="StlcProp.html#4210" class="Bound"
      >valueM</a
      ><a name="4216"
      > </a
      ><a name="4217" class="Keyword"
      >with</a
      ><a name="4221"
      > </a
      ><a name="4222" href="StlcProp.html#1460" class="Function"
      >canonical-forms</a
      ><a name="4237"
      > </a
      ><a name="4238" href="StlcProp.html#4061" class="Bound"
      >&#8866;L</a
      ><a name="4240"
      > </a
      ><a name="4241" href="StlcProp.html#4132" class="Bound"
      >valueL</a
      ><a name="4247"
      >
</a
      ><a name="4248" class="Symbol"
      >...</a
      ><a name="4251"
      > </a
      ><a name="4252" class="Symbol"
      >|</a
      ><a name="4253"
      > </a
      ><a name="4254" href="StlcProp.html#1312" class="InductiveConstructor"
      >canonical-&#955;</a
      ><a name="4265"
      > </a
      ><a name="4266" class="Symbol"
      >=</a
      ><a name="4267"
      > </a
      ><a name="4268" href="StlcProp.html#1998" class="InductiveConstructor"
      >steps</a
      ><a name="4273"
      > </a
      ><a name="4274" class="Symbol"
      >(</a
      ><a name="4275" href="Stlc.html#15975" class="InductiveConstructor"
      >&#946;&#955;&#183;</a
      ><a name="4278"
      > </a
      ><a name="4279" href="StlcProp.html#4210" class="Bound"
      >valueM</a
      ><a name="4285" class="Symbol"
      >)</a
      ><a name="4286"
      >
</a
      ><a name="4287" href="StlcProp.html#2075" class="Function"
      >progress</a
      ><a name="4295"
      > </a
      ><a name="4296" href="Stlc.html#21813" class="InductiveConstructor"
      >&#120121;-I&#8321;</a
      ><a name="4300"
      > </a
      ><a name="4301" class="Symbol"
      >=</a
      ><a name="4302"
      > </a
      ><a name="4303" href="StlcProp.html#2037" class="InductiveConstructor"
      >done</a
      ><a name="4307"
      > </a
      ><a name="4308" href="Stlc.html#9602" class="InductiveConstructor"
      >value-true</a
      ><a name="4318"
      >
</a
      ><a name="4319" href="StlcProp.html#2075" class="Function"
      >progress</a
      ><a name="4327"
      > </a
      ><a name="4328" href="Stlc.html#21847" class="InductiveConstructor"
      >&#120121;-I&#8322;</a
      ><a name="4332"
      > </a
      ><a name="4333" class="Symbol"
      >=</a
      ><a name="4334"
      > </a
      ><a name="4335" href="StlcProp.html#2037" class="InductiveConstructor"
      >done</a
      ><a name="4339"
      > </a
      ><a name="4340" href="Stlc.html#9629" class="InductiveConstructor"
      >value-false</a
      ><a name="4351"
      >
</a
      ><a name="4352" href="StlcProp.html#2075" class="Function"
      >progress</a
      ><a name="4360"
      > </a
      ><a name="4361" class="Symbol"
      >(</a
      ><a name="4362" href="Stlc.html#21882" class="InductiveConstructor"
      >&#120121;-E</a
      ><a name="4365"
      > </a
      ><a name="4366" href="StlcProp.html#4366" class="Bound"
      >&#8866;L</a
      ><a name="4368"
      > </a
      ><a name="4369" href="StlcProp.html#4369" class="Bound"
      >&#8866;M</a
      ><a name="4371"
      > </a
      ><a name="4372" href="StlcProp.html#4372" class="Bound"
      >&#8866;N</a
      ><a name="4374" class="Symbol"
      >)</a
      ><a name="4375"
      > </a
      ><a name="4376" class="Keyword"
      >with</a
      ><a name="4380"
      > </a
      ><a name="4381" href="StlcProp.html#2075" class="Function"
      >progress</a
      ><a name="4389"
      > </a
      ><a name="4390" href="StlcProp.html#4366" class="Bound"
      >&#8866;L</a
      ><a name="4392"
      >
</a
      ><a name="4393" class="Symbol"
      >...</a
      ><a name="4396"
      > </a
      ><a name="4397" class="Symbol"
      >|</a
      ><a name="4398"
      > </a
      ><a name="4399" href="StlcProp.html#1998" class="InductiveConstructor"
      >steps</a
      ><a name="4404"
      > </a
      ><a name="4405" href="StlcProp.html#4405" class="Bound"
      >L&#10233;L&#8242;</a
      ><a name="4409"
      > </a
      ><a name="4410" class="Symbol"
      >=</a
      ><a name="4411"
      > </a
      ><a name="4412" href="StlcProp.html#1998" class="InductiveConstructor"
      >steps</a
      ><a name="4417"
      > </a
      ><a name="4418" class="Symbol"
      >(</a
      ><a name="4419" href="Stlc.html#16045" class="InductiveConstructor"
      >&#958;if</a
      ><a name="4422"
      > </a
      ><a name="4423" href="StlcProp.html#4405" class="Bound"
      >L&#10233;L&#8242;</a
      ><a name="4427" class="Symbol"
      >)</a
      ><a name="4428"
      >
</a
      ><a name="4429" class="Symbol"
      >...</a
      ><a name="4432"
      > </a
      ><a name="4433" class="Symbol"
      >|</a
      ><a name="4434"
      > </a
      ><a name="4435" href="StlcProp.html#2037" class="InductiveConstructor"
      >done</a
      ><a name="4439"
      > </a
      ><a name="4440" href="StlcProp.html#4440" class="Bound"
      >valueL</a
      ><a name="4446"
      > </a
      ><a name="4447" class="Keyword"
      >with</a
      ><a name="4451"
      > </a
      ><a name="4452" href="StlcProp.html#1460" class="Function"
      >canonical-forms</a
      ><a name="4467"
      > </a
      ><a name="4468" href="StlcProp.html#4366" class="Bound"
      >&#8866;L</a
      ><a name="4470"
      > </a
      ><a name="4471" href="StlcProp.html#4440" class="Bound"
      >valueL</a
      ><a name="4477"
      >
</a
      ><a name="4478" class="Symbol"
      >...</a
      ><a name="4481"
      > </a
      ><a name="4482" class="Symbol"
      >|</a
      ><a name="4483"
      > </a
      ><a name="4484" href="StlcProp.html#1379" class="InductiveConstructor"
      >canonical-true</a
      ><a name="4498"
      > </a
      ><a name="4499" class="Symbol"
      >=</a
      ><a name="4500"
      > </a
      ><a name="4501" href="StlcProp.html#1998" class="InductiveConstructor"
      >steps</a
      ><a name="4506"
      > </a
      ><a name="4507" href="Stlc.html#16130" class="InductiveConstructor"
      >&#946;if-true</a
      ><a name="4515"
      >
</a
      ><a name="4516" class="Symbol"
      >...</a
      ><a name="4519"
      > </a
      ><a name="4520" class="Symbol"
      >|</a
      ><a name="4521"
      > </a
      ><a name="4522" href="StlcProp.html#1419" class="InductiveConstructor"
      >canonical-false</a
      ><a name="4537"
      > </a
      ><a name="4538" class="Symbol"
      >=</a
      ><a name="4539"
      > </a
      ><a name="4540" href="StlcProp.html#1998" class="InductiveConstructor"
      >steps</a
      ><a name="4545"
      > </a
      ><a name="4546" href="Stlc.html#16183" class="InductiveConstructor"
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

<a name="5203" class="Keyword"
      >postulate</a
      ><a name="5212"
      >
  </a
      ><a name="5215" href="StlcProp.html#5215" class="Postulate"
      >progress&#8242;</a
      ><a name="5224"
      > </a
      ><a name="5225" class="Symbol"
      >:</a
      ><a name="5226"
      > </a
      ><a name="5227" class="Symbol"
      >&#8704;</a
      ><a name="5228"
      > </a
      ><a name="5229" href="StlcProp.html#5229" class="Bound"
      >M</a
      ><a name="5230"
      > </a
      ><a name="5231" class="Symbol"
      >{</a
      ><a name="5232" href="StlcProp.html#5232" class="Bound"
      >A</a
      ><a name="5233" class="Symbol"
      >}</a
      ><a name="5234"
      > </a
      ><a name="5235" class="Symbol"
      >&#8594;</a
      ><a name="5236"
      > </a
      ><a name="5237" href="Maps.html#10265" class="Function"
      >&#8709;</a
      ><a name="5238"
      > </a
      ><a name="5239" href="Stlc.html#21560" class="Datatype Operator"
      >&#8866;</a
      ><a name="5240"
      > </a
      ><a name="5241" href="StlcProp.html#5229" class="Bound"
      >M</a
      ><a name="5242"
      > </a
      ><a name="5243" href="Stlc.html#21560" class="Datatype Operator"
      >&#8758;</a
      ><a name="5244"
      > </a
      ><a name="5245" href="StlcProp.html#5232" class="Bound"
      >A</a
      ><a name="5246"
      > </a
      ><a name="5247" class="Symbol"
      >&#8594;</a
      ><a name="5248"
      > </a
      ><a name="5249" href="StlcProp.html#1968" class="Datatype"
      >Progress</a
      ><a name="5257"
      > </a
      ><a name="5258" href="StlcProp.html#5229" class="Bound"
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

  - The _preservation theorem_ is proved by induction on a typing
    derivation, pretty much as we did in the [Types]({{ "Types" | relative_url }})
    chapter.  The one case that is significantly different is the one for the
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

<a name="7705" class="Keyword"
      >data</a
      ><a name="7709"
      > </a
      ><a name="7710" href="StlcProp.html#7710" class="Datatype Operator"
      >_&#8712;_</a
      ><a name="7713"
      > </a
      ><a name="7714" class="Symbol"
      >:</a
      ><a name="7715"
      > </a
      ><a name="7716" href="Maps.html#2171" class="Datatype"
      >Id</a
      ><a name="7718"
      > </a
      ><a name="7719" class="Symbol"
      >&#8594;</a
      ><a name="7720"
      > </a
      ><a name="7721" href="Stlc.html#3628" class="Datatype"
      >Term</a
      ><a name="7725"
      > </a
      ><a name="7726" class="Symbol"
      >&#8594;</a
      ><a name="7727"
      > </a
      ><a name="7728" class="PrimitiveType"
      >Set</a
      ><a name="7731"
      > </a
      ><a name="7732" class="Keyword"
      >where</a
      ><a name="7737"
      >
  </a
      ><a name="7740" href="StlcProp.html#7740" class="InductiveConstructor"
      >free-`</a
      ><a name="7746"
      >  </a
      ><a name="7748" class="Symbol"
      >:</a
      ><a name="7749"
      > </a
      ><a name="7750" class="Symbol"
      >&#8704;</a
      ><a name="7751"
      > </a
      ><a name="7752" class="Symbol"
      >{</a
      ><a name="7753" href="StlcProp.html#7753" class="Bound"
      >x</a
      ><a name="7754" class="Symbol"
      >}</a
      ><a name="7755"
      > </a
      ><a name="7756" class="Symbol"
      >&#8594;</a
      ><a name="7757"
      > </a
      ><a name="7758" href="StlcProp.html#7753" class="Bound"
      >x</a
      ><a name="7759"
      > </a
      ><a name="7760" href="StlcProp.html#7710" class="Datatype Operator"
      >&#8712;</a
      ><a name="7761"
      > </a
      ><a name="7762" href="Stlc.html#3647" class="InductiveConstructor"
      >`</a
      ><a name="7763"
      > </a
      ><a name="7764" href="StlcProp.html#7753" class="Bound"
      >x</a
      ><a name="7765"
      >
  </a
      ><a name="7768" href="StlcProp.html#7768" class="InductiveConstructor"
      >free-&#955;</a
      ><a name="7774"
      >  </a
      ><a name="7776" class="Symbol"
      >:</a
      ><a name="7777"
      > </a
      ><a name="7778" class="Symbol"
      >&#8704;</a
      ><a name="7779"
      > </a
      ><a name="7780" class="Symbol"
      >{</a
      ><a name="7781" href="StlcProp.html#7781" class="Bound"
      >x</a
      ><a name="7782"
      > </a
      ><a name="7783" href="StlcProp.html#7783" class="Bound"
      >y</a
      ><a name="7784"
      > </a
      ><a name="7785" href="StlcProp.html#7785" class="Bound"
      >A</a
      ><a name="7786"
      > </a
      ><a name="7787" href="StlcProp.html#7787" class="Bound"
      >N</a
      ><a name="7788" class="Symbol"
      >}</a
      ><a name="7789"
      > </a
      ><a name="7790" class="Symbol"
      >&#8594;</a
      ><a name="7791"
      > </a
      ><a name="7792" href="StlcProp.html#7783" class="Bound"
      >y</a
      ><a name="7793"
      > </a
      ><a name="7794" href="https://agda.github.io/agda-stdlib/Relation.Binary.Core.html#4493" class="Function Operator"
      >&#8802;</a
      ><a name="7795"
      > </a
      ><a name="7796" href="StlcProp.html#7781" class="Bound"
      >x</a
      ><a name="7797"
      > </a
      ><a name="7798" class="Symbol"
      >&#8594;</a
      ><a name="7799"
      > </a
      ><a name="7800" href="StlcProp.html#7781" class="Bound"
      >x</a
      ><a name="7801"
      > </a
      ><a name="7802" href="StlcProp.html#7710" class="Datatype Operator"
      >&#8712;</a
      ><a name="7803"
      > </a
      ><a name="7804" href="StlcProp.html#7787" class="Bound"
      >N</a
      ><a name="7805"
      > </a
      ><a name="7806" class="Symbol"
      >&#8594;</a
      ><a name="7807"
      > </a
      ><a name="7808" href="StlcProp.html#7781" class="Bound"
      >x</a
      ><a name="7809"
      > </a
      ><a name="7810" href="StlcProp.html#7710" class="Datatype Operator"
      >&#8712;</a
      ><a name="7811"
      > </a
      ><a name="7812" class="Symbol"
      >(</a
      ><a name="7813" href="Stlc.html#3663" class="InductiveConstructor Operator"
      >&#955;[</a
      ><a name="7815"
      > </a
      ><a name="7816" href="StlcProp.html#7783" class="Bound"
      >y</a
      ><a name="7817"
      > </a
      ><a name="7818" href="Stlc.html#3663" class="InductiveConstructor Operator"
      >&#8758;</a
      ><a name="7819"
      > </a
      ><a name="7820" href="StlcProp.html#7785" class="Bound"
      >A</a
      ><a name="7821"
      > </a
      ><a name="7822" href="Stlc.html#3663" class="InductiveConstructor Operator"
      >]</a
      ><a name="7823"
      > </a
      ><a name="7824" href="StlcProp.html#7787" class="Bound"
      >N</a
      ><a name="7825" class="Symbol"
      >)</a
      ><a name="7826"
      >
  </a
      ><a name="7829" href="StlcProp.html#7829" class="InductiveConstructor"
      >free-&#183;&#8321;</a
      ><a name="7836"
      > </a
      ><a name="7837" class="Symbol"
      >:</a
      ><a name="7838"
      > </a
      ><a name="7839" class="Symbol"
      >&#8704;</a
      ><a name="7840"
      > </a
      ><a name="7841" class="Symbol"
      >{</a
      ><a name="7842" href="StlcProp.html#7842" class="Bound"
      >x</a
      ><a name="7843"
      > </a
      ><a name="7844" href="StlcProp.html#7844" class="Bound"
      >L</a
      ><a name="7845"
      > </a
      ><a name="7846" href="StlcProp.html#7846" class="Bound"
      >M</a
      ><a name="7847" class="Symbol"
      >}</a
      ><a name="7848"
      > </a
      ><a name="7849" class="Symbol"
      >&#8594;</a
      ><a name="7850"
      > </a
      ><a name="7851" href="StlcProp.html#7842" class="Bound"
      >x</a
      ><a name="7852"
      > </a
      ><a name="7853" href="StlcProp.html#7710" class="Datatype Operator"
      >&#8712;</a
      ><a name="7854"
      > </a
      ><a name="7855" href="StlcProp.html#7844" class="Bound"
      >L</a
      ><a name="7856"
      > </a
      ><a name="7857" class="Symbol"
      >&#8594;</a
      ><a name="7858"
      > </a
      ><a name="7859" href="StlcProp.html#7842" class="Bound"
      >x</a
      ><a name="7860"
      > </a
      ><a name="7861" href="StlcProp.html#7710" class="Datatype Operator"
      >&#8712;</a
      ><a name="7862"
      > </a
      ><a name="7863" class="Symbol"
      >(</a
      ><a name="7864" href="StlcProp.html#7844" class="Bound"
      >L</a
      ><a name="7865"
      > </a
      ><a name="7866" href="Stlc.html#3699" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="7867"
      > </a
      ><a name="7868" href="StlcProp.html#7846" class="Bound"
      >M</a
      ><a name="7869" class="Symbol"
      >)</a
      ><a name="7870"
      >
  </a
      ><a name="7873" href="StlcProp.html#7873" class="InductiveConstructor"
      >free-&#183;&#8322;</a
      ><a name="7880"
      > </a
      ><a name="7881" class="Symbol"
      >:</a
      ><a name="7882"
      > </a
      ><a name="7883" class="Symbol"
      >&#8704;</a
      ><a name="7884"
      > </a
      ><a name="7885" class="Symbol"
      >{</a
      ><a name="7886" href="StlcProp.html#7886" class="Bound"
      >x</a
      ><a name="7887"
      > </a
      ><a name="7888" href="StlcProp.html#7888" class="Bound"
      >L</a
      ><a name="7889"
      > </a
      ><a name="7890" href="StlcProp.html#7890" class="Bound"
      >M</a
      ><a name="7891" class="Symbol"
      >}</a
      ><a name="7892"
      > </a
      ><a name="7893" class="Symbol"
      >&#8594;</a
      ><a name="7894"
      > </a
      ><a name="7895" href="StlcProp.html#7886" class="Bound"
      >x</a
      ><a name="7896"
      > </a
      ><a name="7897" href="StlcProp.html#7710" class="Datatype Operator"
      >&#8712;</a
      ><a name="7898"
      > </a
      ><a name="7899" href="StlcProp.html#7890" class="Bound"
      >M</a
      ><a name="7900"
      > </a
      ><a name="7901" class="Symbol"
      >&#8594;</a
      ><a name="7902"
      > </a
      ><a name="7903" href="StlcProp.html#7886" class="Bound"
      >x</a
      ><a name="7904"
      > </a
      ><a name="7905" href="StlcProp.html#7710" class="Datatype Operator"
      >&#8712;</a
      ><a name="7906"
      > </a
      ><a name="7907" class="Symbol"
      >(</a
      ><a name="7908" href="StlcProp.html#7888" class="Bound"
      >L</a
      ><a name="7909"
      > </a
      ><a name="7910" href="Stlc.html#3699" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="7911"
      > </a
      ><a name="7912" href="StlcProp.html#7890" class="Bound"
      >M</a
      ><a name="7913" class="Symbol"
      >)</a
      ><a name="7914"
      >
  </a
      ><a name="7917" href="StlcProp.html#7917" class="InductiveConstructor"
      >free-if&#8321;</a
      ><a name="7925"
      > </a
      ><a name="7926" class="Symbol"
      >:</a
      ><a name="7927"
      > </a
      ><a name="7928" class="Symbol"
      >&#8704;</a
      ><a name="7929"
      > </a
      ><a name="7930" class="Symbol"
      >{</a
      ><a name="7931" href="StlcProp.html#7931" class="Bound"
      >x</a
      ><a name="7932"
      > </a
      ><a name="7933" href="StlcProp.html#7933" class="Bound"
      >L</a
      ><a name="7934"
      > </a
      ><a name="7935" href="StlcProp.html#7935" class="Bound"
      >M</a
      ><a name="7936"
      > </a
      ><a name="7937" href="StlcProp.html#7937" class="Bound"
      >N</a
      ><a name="7938" class="Symbol"
      >}</a
      ><a name="7939"
      > </a
      ><a name="7940" class="Symbol"
      >&#8594;</a
      ><a name="7941"
      > </a
      ><a name="7942" href="StlcProp.html#7931" class="Bound"
      >x</a
      ><a name="7943"
      > </a
      ><a name="7944" href="StlcProp.html#7710" class="Datatype Operator"
      >&#8712;</a
      ><a name="7945"
      > </a
      ><a name="7946" href="StlcProp.html#7933" class="Bound"
      >L</a
      ><a name="7947"
      > </a
      ><a name="7948" class="Symbol"
      >&#8594;</a
      ><a name="7949"
      > </a
      ><a name="7950" href="StlcProp.html#7931" class="Bound"
      >x</a
      ><a name="7951"
      > </a
      ><a name="7952" href="StlcProp.html#7710" class="Datatype Operator"
      >&#8712;</a
      ><a name="7953"
      > </a
      ><a name="7954" class="Symbol"
      >(</a
      ><a name="7955" href="Stlc.html#3755" class="InductiveConstructor Operator"
      >if</a
      ><a name="7957"
      > </a
      ><a name="7958" href="StlcProp.html#7933" class="Bound"
      >L</a
      ><a name="7959"
      > </a
      ><a name="7960" href="Stlc.html#3755" class="InductiveConstructor Operator"
      >then</a
      ><a name="7964"
      > </a
      ><a name="7965" href="StlcProp.html#7935" class="Bound"
      >M</a
      ><a name="7966"
      > </a
      ><a name="7967" href="Stlc.html#3755" class="InductiveConstructor Operator"
      >else</a
      ><a name="7971"
      > </a
      ><a name="7972" href="StlcProp.html#7937" class="Bound"
      >N</a
      ><a name="7973" class="Symbol"
      >)</a
      ><a name="7974"
      >
  </a
      ><a name="7977" href="StlcProp.html#7977" class="InductiveConstructor"
      >free-if&#8322;</a
      ><a name="7985"
      > </a
      ><a name="7986" class="Symbol"
      >:</a
      ><a name="7987"
      > </a
      ><a name="7988" class="Symbol"
      >&#8704;</a
      ><a name="7989"
      > </a
      ><a name="7990" class="Symbol"
      >{</a
      ><a name="7991" href="StlcProp.html#7991" class="Bound"
      >x</a
      ><a name="7992"
      > </a
      ><a name="7993" href="StlcProp.html#7993" class="Bound"
      >L</a
      ><a name="7994"
      > </a
      ><a name="7995" href="StlcProp.html#7995" class="Bound"
      >M</a
      ><a name="7996"
      > </a
      ><a name="7997" href="StlcProp.html#7997" class="Bound"
      >N</a
      ><a name="7998" class="Symbol"
      >}</a
      ><a name="7999"
      > </a
      ><a name="8000" class="Symbol"
      >&#8594;</a
      ><a name="8001"
      > </a
      ><a name="8002" href="StlcProp.html#7991" class="Bound"
      >x</a
      ><a name="8003"
      > </a
      ><a name="8004" href="StlcProp.html#7710" class="Datatype Operator"
      >&#8712;</a
      ><a name="8005"
      > </a
      ><a name="8006" href="StlcProp.html#7995" class="Bound"
      >M</a
      ><a name="8007"
      > </a
      ><a name="8008" class="Symbol"
      >&#8594;</a
      ><a name="8009"
      > </a
      ><a name="8010" href="StlcProp.html#7991" class="Bound"
      >x</a
      ><a name="8011"
      > </a
      ><a name="8012" href="StlcProp.html#7710" class="Datatype Operator"
      >&#8712;</a
      ><a name="8013"
      > </a
      ><a name="8014" class="Symbol"
      >(</a
      ><a name="8015" href="Stlc.html#3755" class="InductiveConstructor Operator"
      >if</a
      ><a name="8017"
      > </a
      ><a name="8018" href="StlcProp.html#7993" class="Bound"
      >L</a
      ><a name="8019"
      > </a
      ><a name="8020" href="Stlc.html#3755" class="InductiveConstructor Operator"
      >then</a
      ><a name="8024"
      > </a
      ><a name="8025" href="StlcProp.html#7995" class="Bound"
      >M</a
      ><a name="8026"
      > </a
      ><a name="8027" href="Stlc.html#3755" class="InductiveConstructor Operator"
      >else</a
      ><a name="8031"
      > </a
      ><a name="8032" href="StlcProp.html#7997" class="Bound"
      >N</a
      ><a name="8033" class="Symbol"
      >)</a
      ><a name="8034"
      >
  </a
      ><a name="8037" href="StlcProp.html#8037" class="InductiveConstructor"
      >free-if&#8323;</a
      ><a name="8045"
      > </a
      ><a name="8046" class="Symbol"
      >:</a
      ><a name="8047"
      > </a
      ><a name="8048" class="Symbol"
      >&#8704;</a
      ><a name="8049"
      > </a
      ><a name="8050" class="Symbol"
      >{</a
      ><a name="8051" href="StlcProp.html#8051" class="Bound"
      >x</a
      ><a name="8052"
      > </a
      ><a name="8053" href="StlcProp.html#8053" class="Bound"
      >L</a
      ><a name="8054"
      > </a
      ><a name="8055" href="StlcProp.html#8055" class="Bound"
      >M</a
      ><a name="8056"
      > </a
      ><a name="8057" href="StlcProp.html#8057" class="Bound"
      >N</a
      ><a name="8058" class="Symbol"
      >}</a
      ><a name="8059"
      > </a
      ><a name="8060" class="Symbol"
      >&#8594;</a
      ><a name="8061"
      > </a
      ><a name="8062" href="StlcProp.html#8051" class="Bound"
      >x</a
      ><a name="8063"
      > </a
      ><a name="8064" href="StlcProp.html#7710" class="Datatype Operator"
      >&#8712;</a
      ><a name="8065"
      > </a
      ><a name="8066" href="StlcProp.html#8057" class="Bound"
      >N</a
      ><a name="8067"
      > </a
      ><a name="8068" class="Symbol"
      >&#8594;</a
      ><a name="8069"
      > </a
      ><a name="8070" href="StlcProp.html#8051" class="Bound"
      >x</a
      ><a name="8071"
      > </a
      ><a name="8072" href="StlcProp.html#7710" class="Datatype Operator"
      >&#8712;</a
      ><a name="8073"
      > </a
      ><a name="8074" class="Symbol"
      >(</a
      ><a name="8075" href="Stlc.html#3755" class="InductiveConstructor Operator"
      >if</a
      ><a name="8077"
      > </a
      ><a name="8078" href="StlcProp.html#8053" class="Bound"
      >L</a
      ><a name="8079"
      > </a
      ><a name="8080" href="Stlc.html#3755" class="InductiveConstructor Operator"
      >then</a
      ><a name="8084"
      > </a
      ><a name="8085" href="StlcProp.html#8055" class="Bound"
      >M</a
      ><a name="8086"
      > </a
      ><a name="8087" href="Stlc.html#3755" class="InductiveConstructor Operator"
      >else</a
      ><a name="8091"
      > </a
      ><a name="8092" href="StlcProp.html#8057" class="Bound"
      >N</a
      ><a name="8093" class="Symbol"
      >)</a
      >

</pre>

A term in which no variables appear free is said to be _closed_.

<pre class="Agda">

<a name="8186" href="StlcProp.html#8186" class="Function Operator"
      >_&#8713;_</a
      ><a name="8189"
      > </a
      ><a name="8190" class="Symbol"
      >:</a
      ><a name="8191"
      > </a
      ><a name="8192" href="Maps.html#2171" class="Datatype"
      >Id</a
      ><a name="8194"
      > </a
      ><a name="8195" class="Symbol"
      >&#8594;</a
      ><a name="8196"
      > </a
      ><a name="8197" href="Stlc.html#3628" class="Datatype"
      >Term</a
      ><a name="8201"
      > </a
      ><a name="8202" class="Symbol"
      >&#8594;</a
      ><a name="8203"
      > </a
      ><a name="8204" class="PrimitiveType"
      >Set</a
      ><a name="8207"
      >
</a
      ><a name="8208" href="StlcProp.html#8208" class="Bound"
      >x</a
      ><a name="8209"
      > </a
      ><a name="8210" href="StlcProp.html#8186" class="Function Operator"
      >&#8713;</a
      ><a name="8211"
      > </a
      ><a name="8212" href="StlcProp.html#8212" class="Bound"
      >M</a
      ><a name="8213"
      > </a
      ><a name="8214" class="Symbol"
      >=</a
      ><a name="8215"
      > </a
      ><a name="8216" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#414" class="Function Operator"
      >&#172;</a
      ><a name="8217"
      > </a
      ><a name="8218" class="Symbol"
      >(</a
      ><a name="8219" href="StlcProp.html#8208" class="Bound"
      >x</a
      ><a name="8220"
      > </a
      ><a name="8221" href="StlcProp.html#7710" class="Datatype Operator"
      >&#8712;</a
      ><a name="8222"
      > </a
      ><a name="8223" href="StlcProp.html#8212" class="Bound"
      >M</a
      ><a name="8224" class="Symbol"
      >)</a
      ><a name="8225"
      >

</a
      ><a name="8227" href="StlcProp.html#8227" class="Function"
      >closed</a
      ><a name="8233"
      > </a
      ><a name="8234" class="Symbol"
      >:</a
      ><a name="8235"
      > </a
      ><a name="8236" href="Stlc.html#3628" class="Datatype"
      >Term</a
      ><a name="8240"
      > </a
      ><a name="8241" class="Symbol"
      >&#8594;</a
      ><a name="8242"
      > </a
      ><a name="8243" class="PrimitiveType"
      >Set</a
      ><a name="8246"
      >
</a
      ><a name="8247" href="StlcProp.html#8227" class="Function"
      >closed</a
      ><a name="8253"
      > </a
      ><a name="8254" href="StlcProp.html#8254" class="Bound"
      >M</a
      ><a name="8255"
      > </a
      ><a name="8256" class="Symbol"
      >=</a
      ><a name="8257"
      > </a
      ><a name="8258" class="Symbol"
      >&#8704;</a
      ><a name="8259"
      > </a
      ><a name="8260" class="Symbol"
      >{</a
      ><a name="8261" href="StlcProp.html#8261" class="Bound"
      >x</a
      ><a name="8262" class="Symbol"
      >}</a
      ><a name="8263"
      > </a
      ><a name="8264" class="Symbol"
      >&#8594;</a
      ><a name="8265"
      > </a
      ><a name="8266" href="StlcProp.html#8261" class="Bound"
      >x</a
      ><a name="8267"
      > </a
      ><a name="8268" href="StlcProp.html#8186" class="Function Operator"
      >&#8713;</a
      ><a name="8269"
      > </a
      ><a name="8270" href="StlcProp.html#8254" class="Bound"
      >M</a
      >

</pre>

Here are proofs corresponding to the first two examples above.

<pre class="Agda">

<a name="8361" href="StlcProp.html#8361" class="Function"
      >f&#8802;x</a
      ><a name="8364"
      > </a
      ><a name="8365" class="Symbol"
      >:</a
      ><a name="8366"
      > </a
      ><a name="8367" href="Stlc.html#5669" class="Function"
      >f</a
      ><a name="8368"
      > </a
      ><a name="8369" href="https://agda.github.io/agda-stdlib/Relation.Binary.Core.html#4493" class="Function Operator"
      >&#8802;</a
      ><a name="8370"
      > </a
      ><a name="8371" href="Stlc.html#5671" class="Function"
      >x</a
      ><a name="8372"
      >
</a
      ><a name="8373" href="StlcProp.html#8361" class="Function"
      >f&#8802;x</a
      ><a name="8376"
      > </a
      ><a name="8377" class="Symbol"
      >()</a
      ><a name="8379"
      >

</a
      ><a name="8381" href="StlcProp.html#8381" class="Function"
      >example-free&#8321;</a
      ><a name="8394"
      > </a
      ><a name="8395" class="Symbol"
      >:</a
      ><a name="8396"
      > </a
      ><a name="8397" href="Stlc.html#5671" class="Function"
      >x</a
      ><a name="8398"
      > </a
      ><a name="8399" href="StlcProp.html#7710" class="Datatype Operator"
      >&#8712;</a
      ><a name="8400"
      > </a
      ><a name="8401" class="Symbol"
      >(</a
      ><a name="8402" href="Stlc.html#3663" class="InductiveConstructor Operator"
      >&#955;[</a
      ><a name="8404"
      > </a
      ><a name="8405" href="Stlc.html#5669" class="Function"
      >f</a
      ><a name="8406"
      > </a
      ><a name="8407" href="Stlc.html#3663" class="InductiveConstructor Operator"
      >&#8758;</a
      ><a name="8408"
      > </a
      ><a name="8409" class="Symbol"
      >(</a
      ><a name="8410" href="Stlc.html#2601" class="InductiveConstructor"
      >&#120121;</a
      ><a name="8411"
      > </a
      ><a name="8412" href="Stlc.html#2574" class="InductiveConstructor Operator"
      >&#8658;</a
      ><a name="8413"
      > </a
      ><a name="8414" href="Stlc.html#2601" class="InductiveConstructor"
      >&#120121;</a
      ><a name="8415" class="Symbol"
      >)</a
      ><a name="8416"
      > </a
      ><a name="8417" href="Stlc.html#3663" class="InductiveConstructor Operator"
      >]</a
      ><a name="8418"
      > </a
      ><a name="8419" href="Stlc.html#3647" class="InductiveConstructor"
      >`</a
      ><a name="8420"
      > </a
      ><a name="8421" href="Stlc.html#5669" class="Function"
      >f</a
      ><a name="8422"
      > </a
      ><a name="8423" href="Stlc.html#3699" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="8424"
      > </a
      ><a name="8425" href="Stlc.html#3647" class="InductiveConstructor"
      >`</a
      ><a name="8426"
      > </a
      ><a name="8427" href="Stlc.html#5671" class="Function"
      >x</a
      ><a name="8428" class="Symbol"
      >)</a
      ><a name="8429"
      >
</a
      ><a name="8430" href="StlcProp.html#8381" class="Function"
      >example-free&#8321;</a
      ><a name="8443"
      > </a
      ><a name="8444" class="Symbol"
      >=</a
      ><a name="8445"
      > </a
      ><a name="8446" href="StlcProp.html#7768" class="InductiveConstructor"
      >free-&#955;</a
      ><a name="8452"
      > </a
      ><a name="8453" href="StlcProp.html#8361" class="Function"
      >f&#8802;x</a
      ><a name="8456"
      > </a
      ><a name="8457" class="Symbol"
      >(</a
      ><a name="8458" href="StlcProp.html#7873" class="InductiveConstructor"
      >free-&#183;&#8322;</a
      ><a name="8465"
      > </a
      ><a name="8466" href="StlcProp.html#7740" class="InductiveConstructor"
      >free-`</a
      ><a name="8472" class="Symbol"
      >)</a
      ><a name="8473"
      >

</a
      ><a name="8475" href="StlcProp.html#8475" class="Function"
      >example-free&#8322;</a
      ><a name="8488"
      > </a
      ><a name="8489" class="Symbol"
      >:</a
      ><a name="8490"
      > </a
      ><a name="8491" href="Stlc.html#5669" class="Function"
      >f</a
      ><a name="8492"
      > </a
      ><a name="8493" href="StlcProp.html#8186" class="Function Operator"
      >&#8713;</a
      ><a name="8494"
      > </a
      ><a name="8495" class="Symbol"
      >(</a
      ><a name="8496" href="Stlc.html#3663" class="InductiveConstructor Operator"
      >&#955;[</a
      ><a name="8498"
      > </a
      ><a name="8499" href="Stlc.html#5669" class="Function"
      >f</a
      ><a name="8500"
      > </a
      ><a name="8501" href="Stlc.html#3663" class="InductiveConstructor Operator"
      >&#8758;</a
      ><a name="8502"
      > </a
      ><a name="8503" class="Symbol"
      >(</a
      ><a name="8504" href="Stlc.html#2601" class="InductiveConstructor"
      >&#120121;</a
      ><a name="8505"
      > </a
      ><a name="8506" href="Stlc.html#2574" class="InductiveConstructor Operator"
      >&#8658;</a
      ><a name="8507"
      > </a
      ><a name="8508" href="Stlc.html#2601" class="InductiveConstructor"
      >&#120121;</a
      ><a name="8509" class="Symbol"
      >)</a
      ><a name="8510"
      > </a
      ><a name="8511" href="Stlc.html#3663" class="InductiveConstructor Operator"
      >]</a
      ><a name="8512"
      > </a
      ><a name="8513" href="Stlc.html#3647" class="InductiveConstructor"
      >`</a
      ><a name="8514"
      > </a
      ><a name="8515" href="Stlc.html#5669" class="Function"
      >f</a
      ><a name="8516"
      > </a
      ><a name="8517" href="Stlc.html#3699" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="8518"
      > </a
      ><a name="8519" href="Stlc.html#3647" class="InductiveConstructor"
      >`</a
      ><a name="8520"
      > </a
      ><a name="8521" href="Stlc.html#5671" class="Function"
      >x</a
      ><a name="8522" class="Symbol"
      >)</a
      ><a name="8523"
      >
</a
      ><a name="8524" href="StlcProp.html#8475" class="Function"
      >example-free&#8322;</a
      ><a name="8537"
      > </a
      ><a name="8538" class="Symbol"
      >(</a
      ><a name="8539" href="StlcProp.html#7768" class="InductiveConstructor"
      >free-&#955;</a
      ><a name="8545"
      > </a
      ><a name="8546" href="StlcProp.html#8546" class="Bound"
      >f&#8802;f</a
      ><a name="8549"
      > </a
      ><a name="8550" class="Symbol"
      >_)</a
      ><a name="8552"
      > </a
      ><a name="8553" class="Symbol"
      >=</a
      ><a name="8554"
      > </a
      ><a name="8555" href="StlcProp.html#8546" class="Bound"
      >f&#8802;f</a
      ><a name="8558"
      > </a
      ><a name="8559" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      >

</pre>


#### Exercise: 1 star (free-in)
Prove formally the remaining examples given above.

<pre class="Agda">

<a name="8674" class="Keyword"
      >postulate</a
      ><a name="8683"
      >
  </a
      ><a name="8686" href="StlcProp.html#8686" class="Postulate"
      >example-free&#8323;</a
      ><a name="8699"
      > </a
      ><a name="8700" class="Symbol"
      >:</a
      ><a name="8701"
      > </a
      ><a name="8702" href="Stlc.html#5671" class="Function"
      >x</a
      ><a name="8703"
      > </a
      ><a name="8704" href="StlcProp.html#7710" class="Datatype Operator"
      >&#8712;</a
      ><a name="8705"
      > </a
      ><a name="8706" class="Symbol"
      >((</a
      ><a name="8708" href="Stlc.html#3663" class="InductiveConstructor Operator"
      >&#955;[</a
      ><a name="8710"
      > </a
      ><a name="8711" href="Stlc.html#5669" class="Function"
      >f</a
      ><a name="8712"
      > </a
      ><a name="8713" href="Stlc.html#3663" class="InductiveConstructor Operator"
      >&#8758;</a
      ><a name="8714"
      > </a
      ><a name="8715" class="Symbol"
      >(</a
      ><a name="8716" href="Stlc.html#2601" class="InductiveConstructor"
      >&#120121;</a
      ><a name="8717"
      > </a
      ><a name="8718" href="Stlc.html#2574" class="InductiveConstructor Operator"
      >&#8658;</a
      ><a name="8719"
      > </a
      ><a name="8720" href="Stlc.html#2601" class="InductiveConstructor"
      >&#120121;</a
      ><a name="8721" class="Symbol"
      >)</a
      ><a name="8722"
      > </a
      ><a name="8723" href="Stlc.html#3663" class="InductiveConstructor Operator"
      >]</a
      ><a name="8724"
      > </a
      ><a name="8725" href="Stlc.html#3647" class="InductiveConstructor"
      >`</a
      ><a name="8726"
      > </a
      ><a name="8727" href="Stlc.html#5669" class="Function"
      >f</a
      ><a name="8728"
      > </a
      ><a name="8729" href="Stlc.html#3699" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="8730"
      > </a
      ><a name="8731" href="Stlc.html#3647" class="InductiveConstructor"
      >`</a
      ><a name="8732"
      > </a
      ><a name="8733" href="Stlc.html#5671" class="Function"
      >x</a
      ><a name="8734" class="Symbol"
      >)</a
      ><a name="8735"
      > </a
      ><a name="8736" href="Stlc.html#3699" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="8737"
      > </a
      ><a name="8738" href="Stlc.html#3647" class="InductiveConstructor"
      >`</a
      ><a name="8739"
      > </a
      ><a name="8740" href="Stlc.html#5669" class="Function"
      >f</a
      ><a name="8741" class="Symbol"
      >)</a
      ><a name="8742"
      >
  </a
      ><a name="8745" href="StlcProp.html#8745" class="Postulate"
      >example-free&#8324;</a
      ><a name="8758"
      > </a
      ><a name="8759" class="Symbol"
      >:</a
      ><a name="8760"
      > </a
      ><a name="8761" href="Stlc.html#5669" class="Function"
      >f</a
      ><a name="8762"
      > </a
      ><a name="8763" href="StlcProp.html#7710" class="Datatype Operator"
      >&#8712;</a
      ><a name="8764"
      > </a
      ><a name="8765" class="Symbol"
      >((</a
      ><a name="8767" href="Stlc.html#3663" class="InductiveConstructor Operator"
      >&#955;[</a
      ><a name="8769"
      > </a
      ><a name="8770" href="Stlc.html#5669" class="Function"
      >f</a
      ><a name="8771"
      > </a
      ><a name="8772" href="Stlc.html#3663" class="InductiveConstructor Operator"
      >&#8758;</a
      ><a name="8773"
      > </a
      ><a name="8774" class="Symbol"
      >(</a
      ><a name="8775" href="Stlc.html#2601" class="InductiveConstructor"
      >&#120121;</a
      ><a name="8776"
      > </a
      ><a name="8777" href="Stlc.html#2574" class="InductiveConstructor Operator"
      >&#8658;</a
      ><a name="8778"
      > </a
      ><a name="8779" href="Stlc.html#2601" class="InductiveConstructor"
      >&#120121;</a
      ><a name="8780" class="Symbol"
      >)</a
      ><a name="8781"
      > </a
      ><a name="8782" href="Stlc.html#3663" class="InductiveConstructor Operator"
      >]</a
      ><a name="8783"
      > </a
      ><a name="8784" href="Stlc.html#3647" class="InductiveConstructor"
      >`</a
      ><a name="8785"
      > </a
      ><a name="8786" href="Stlc.html#5669" class="Function"
      >f</a
      ><a name="8787"
      > </a
      ><a name="8788" href="Stlc.html#3699" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="8789"
      > </a
      ><a name="8790" href="Stlc.html#3647" class="InductiveConstructor"
      >`</a
      ><a name="8791"
      > </a
      ><a name="8792" href="Stlc.html#5671" class="Function"
      >x</a
      ><a name="8793" class="Symbol"
      >)</a
      ><a name="8794"
      > </a
      ><a name="8795" href="Stlc.html#3699" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="8796"
      > </a
      ><a name="8797" href="Stlc.html#3647" class="InductiveConstructor"
      >`</a
      ><a name="8798"
      > </a
      ><a name="8799" href="Stlc.html#5669" class="Function"
      >f</a
      ><a name="8800" class="Symbol"
      >)</a
      ><a name="8801"
      >
  </a
      ><a name="8804" href="StlcProp.html#8804" class="Postulate"
      >example-free&#8325;</a
      ><a name="8817"
      > </a
      ><a name="8818" class="Symbol"
      >:</a
      ><a name="8819"
      > </a
      ><a name="8820" href="Stlc.html#5671" class="Function"
      >x</a
      ><a name="8821"
      > </a
      ><a name="8822" href="StlcProp.html#8186" class="Function Operator"
      >&#8713;</a
      ><a name="8823"
      > </a
      ><a name="8824" class="Symbol"
      >(</a
      ><a name="8825" href="Stlc.html#3663" class="InductiveConstructor Operator"
      >&#955;[</a
      ><a name="8827"
      > </a
      ><a name="8828" href="Stlc.html#5669" class="Function"
      >f</a
      ><a name="8829"
      > </a
      ><a name="8830" href="Stlc.html#3663" class="InductiveConstructor Operator"
      >&#8758;</a
      ><a name="8831"
      > </a
      ><a name="8832" class="Symbol"
      >(</a
      ><a name="8833" href="Stlc.html#2601" class="InductiveConstructor"
      >&#120121;</a
      ><a name="8834"
      > </a
      ><a name="8835" href="Stlc.html#2574" class="InductiveConstructor Operator"
      >&#8658;</a
      ><a name="8836"
      > </a
      ><a name="8837" href="Stlc.html#2601" class="InductiveConstructor"
      >&#120121;</a
      ><a name="8838" class="Symbol"
      >)</a
      ><a name="8839"
      > </a
      ><a name="8840" href="Stlc.html#3663" class="InductiveConstructor Operator"
      >]</a
      ><a name="8841"
      > </a
      ><a name="8842" href="Stlc.html#3663" class="InductiveConstructor Operator"
      >&#955;[</a
      ><a name="8844"
      > </a
      ><a name="8845" href="Stlc.html#5671" class="Function"
      >x</a
      ><a name="8846"
      > </a
      ><a name="8847" href="Stlc.html#3663" class="InductiveConstructor Operator"
      >&#8758;</a
      ><a name="8848"
      > </a
      ><a name="8849" href="Stlc.html#2601" class="InductiveConstructor"
      >&#120121;</a
      ><a name="8850"
      > </a
      ><a name="8851" href="Stlc.html#3663" class="InductiveConstructor Operator"
      >]</a
      ><a name="8852"
      > </a
      ><a name="8853" href="Stlc.html#3647" class="InductiveConstructor"
      >`</a
      ><a name="8854"
      > </a
      ><a name="8855" href="Stlc.html#5669" class="Function"
      >f</a
      ><a name="8856"
      > </a
      ><a name="8857" href="Stlc.html#3699" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="8858"
      > </a
      ><a name="8859" href="Stlc.html#3647" class="InductiveConstructor"
      >`</a
      ><a name="8860"
      > </a
      ><a name="8861" href="Stlc.html#5671" class="Function"
      >x</a
      ><a name="8862" class="Symbol"
      >)</a
      ><a name="8863"
      >
  </a
      ><a name="8866" href="StlcProp.html#8866" class="Postulate"
      >example-free&#8326;</a
      ><a name="8879"
      > </a
      ><a name="8880" class="Symbol"
      >:</a
      ><a name="8881"
      > </a
      ><a name="8882" href="Stlc.html#5669" class="Function"
      >f</a
      ><a name="8883"
      > </a
      ><a name="8884" href="StlcProp.html#8186" class="Function Operator"
      >&#8713;</a
      ><a name="8885"
      > </a
      ><a name="8886" class="Symbol"
      >(</a
      ><a name="8887" href="Stlc.html#3663" class="InductiveConstructor Operator"
      >&#955;[</a
      ><a name="8889"
      > </a
      ><a name="8890" href="Stlc.html#5669" class="Function"
      >f</a
      ><a name="8891"
      > </a
      ><a name="8892" href="Stlc.html#3663" class="InductiveConstructor Operator"
      >&#8758;</a
      ><a name="8893"
      > </a
      ><a name="8894" class="Symbol"
      >(</a
      ><a name="8895" href="Stlc.html#2601" class="InductiveConstructor"
      >&#120121;</a
      ><a name="8896"
      > </a
      ><a name="8897" href="Stlc.html#2574" class="InductiveConstructor Operator"
      >&#8658;</a
      ><a name="8898"
      > </a
      ><a name="8899" href="Stlc.html#2601" class="InductiveConstructor"
      >&#120121;</a
      ><a name="8900" class="Symbol"
      >)</a
      ><a name="8901"
      > </a
      ><a name="8902" href="Stlc.html#3663" class="InductiveConstructor Operator"
      >]</a
      ><a name="8903"
      > </a
      ><a name="8904" href="Stlc.html#3663" class="InductiveConstructor Operator"
      >&#955;[</a
      ><a name="8906"
      > </a
      ><a name="8907" href="Stlc.html#5671" class="Function"
      >x</a
      ><a name="8908"
      > </a
      ><a name="8909" href="Stlc.html#3663" class="InductiveConstructor Operator"
      >&#8758;</a
      ><a name="8910"
      > </a
      ><a name="8911" href="Stlc.html#2601" class="InductiveConstructor"
      >&#120121;</a
      ><a name="8912"
      > </a
      ><a name="8913" href="Stlc.html#3663" class="InductiveConstructor Operator"
      >]</a
      ><a name="8914"
      > </a
      ><a name="8915" href="Stlc.html#3647" class="InductiveConstructor"
      >`</a
      ><a name="8916"
      > </a
      ><a name="8917" href="Stlc.html#5669" class="Function"
      >f</a
      ><a name="8918"
      > </a
      ><a name="8919" href="Stlc.html#3699" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="8920"
      > </a
      ><a name="8921" href="Stlc.html#3647" class="InductiveConstructor"
      >`</a
      ><a name="8922"
      > </a
      ><a name="8923" href="Stlc.html#5671" class="Function"
      >x</a
      ><a name="8924" class="Symbol"
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

<a name="9407" href="StlcProp.html#9407" class="Function"
      >free-lemma</a
      ><a name="9417"
      > </a
      ><a name="9418" class="Symbol"
      >:</a
      ><a name="9419"
      > </a
      ><a name="9420" class="Symbol"
      >&#8704;</a
      ><a name="9421"
      > </a
      ><a name="9422" class="Symbol"
      >{</a
      ><a name="9423" href="StlcProp.html#9423" class="Bound"
      >x</a
      ><a name="9424"
      > </a
      ><a name="9425" href="StlcProp.html#9425" class="Bound"
      >M</a
      ><a name="9426"
      > </a
      ><a name="9427" href="StlcProp.html#9427" class="Bound"
      >A</a
      ><a name="9428"
      > </a
      ><a name="9429" href="StlcProp.html#9429" class="Bound"
      >&#915;</a
      ><a name="9430" class="Symbol"
      >}</a
      ><a name="9431"
      > </a
      ><a name="9432" class="Symbol"
      >&#8594;</a
      ><a name="9433"
      > </a
      ><a name="9434" href="StlcProp.html#9423" class="Bound"
      >x</a
      ><a name="9435"
      > </a
      ><a name="9436" href="StlcProp.html#7710" class="Datatype Operator"
      >&#8712;</a
      ><a name="9437"
      > </a
      ><a name="9438" href="StlcProp.html#9425" class="Bound"
      >M</a
      ><a name="9439"
      > </a
      ><a name="9440" class="Symbol"
      >&#8594;</a
      ><a name="9441"
      > </a
      ><a name="9442" href="StlcProp.html#9429" class="Bound"
      >&#915;</a
      ><a name="9443"
      > </a
      ><a name="9444" href="Stlc.html#21560" class="Datatype Operator"
      >&#8866;</a
      ><a name="9445"
      > </a
      ><a name="9446" href="StlcProp.html#9425" class="Bound"
      >M</a
      ><a name="9447"
      > </a
      ><a name="9448" href="Stlc.html#21560" class="Datatype Operator"
      >&#8758;</a
      ><a name="9449"
      > </a
      ><a name="9450" href="StlcProp.html#9427" class="Bound"
      >A</a
      ><a name="9451"
      > </a
      ><a name="9452" class="Symbol"
      >&#8594;</a
      ><a name="9453"
      > </a
      ><a name="9454" href="https://agda.github.io/agda-stdlib/Data.Product.html#823" class="Function"
      >&#8707;</a
      ><a name="9455"
      > </a
      ><a name="9456" class="Symbol"
      >&#955;</a
      ><a name="9457"
      > </a
      ><a name="9458" href="StlcProp.html#9458" class="Bound"
      >B</a
      ><a name="9459"
      > </a
      ><a name="9460" class="Symbol"
      >&#8594;</a
      ><a name="9461"
      > </a
      ><a name="9462" href="StlcProp.html#9429" class="Bound"
      >&#915;</a
      ><a name="9463"
      > </a
      ><a name="9464" href="StlcProp.html#9423" class="Bound"
      >x</a
      ><a name="9465"
      > </a
      ><a name="9466" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="9467"
      > </a
      ><a name="9468" href="https://agda.github.io/agda-stdlib/Data.Maybe.Base.html#373" class="InductiveConstructor"
      >just</a
      ><a name="9472"
      > </a
      ><a name="9473" href="StlcProp.html#9458" class="Bound"
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

<a name="10922" href="StlcProp.html#9407" class="Function"
      >free-lemma</a
      ><a name="10932"
      > </a
      ><a name="10933" href="StlcProp.html#7740" class="InductiveConstructor"
      >free-`</a
      ><a name="10939"
      > </a
      ><a name="10940" class="Symbol"
      >(</a
      ><a name="10941" href="Stlc.html#21604" class="InductiveConstructor"
      >Ax</a
      ><a name="10943"
      > </a
      ><a name="10944" href="StlcProp.html#10944" class="Bound"
      >&#915;x&#8801;A</a
      ><a name="10948" class="Symbol"
      >)</a
      ><a name="10949"
      > </a
      ><a name="10950" class="Symbol"
      >=</a
      ><a name="10951"
      > </a
      ><a name="10952" class="Symbol"
      >(_</a
      ><a name="10954"
      > </a
      ><a name="10955" href="https://agda.github.io/agda-stdlib/Data.Product.html#509" class="InductiveConstructor Operator"
      >,</a
      ><a name="10956"
      > </a
      ><a name="10957" href="StlcProp.html#10944" class="Bound"
      >&#915;x&#8801;A</a
      ><a name="10961" class="Symbol"
      >)</a
      ><a name="10962"
      >
</a
      ><a name="10963" href="StlcProp.html#9407" class="Function"
      >free-lemma</a
      ><a name="10973"
      > </a
      ><a name="10974" class="Symbol"
      >(</a
      ><a name="10975" href="StlcProp.html#7829" class="InductiveConstructor"
      >free-&#183;&#8321;</a
      ><a name="10982"
      > </a
      ><a name="10983" href="StlcProp.html#10983" class="Bound"
      >x&#8712;L</a
      ><a name="10986" class="Symbol"
      >)</a
      ><a name="10987"
      > </a
      ><a name="10988" class="Symbol"
      >(</a
      ><a name="10989" href="Stlc.html#21735" class="InductiveConstructor"
      >&#8658;-E</a
      ><a name="10992"
      > </a
      ><a name="10993" href="StlcProp.html#10993" class="Bound"
      >&#8866;L</a
      ><a name="10995"
      > </a
      ><a name="10996" href="StlcProp.html#10996" class="Bound"
      >&#8866;M</a
      ><a name="10998" class="Symbol"
      >)</a
      ><a name="10999"
      > </a
      ><a name="11000" class="Symbol"
      >=</a
      ><a name="11001"
      > </a
      ><a name="11002" href="StlcProp.html#9407" class="Function"
      >free-lemma</a
      ><a name="11012"
      > </a
      ><a name="11013" href="StlcProp.html#10983" class="Bound"
      >x&#8712;L</a
      ><a name="11016"
      > </a
      ><a name="11017" href="StlcProp.html#10993" class="Bound"
      >&#8866;L</a
      ><a name="11019"
      >
</a
      ><a name="11020" href="StlcProp.html#9407" class="Function"
      >free-lemma</a
      ><a name="11030"
      > </a
      ><a name="11031" class="Symbol"
      >(</a
      ><a name="11032" href="StlcProp.html#7873" class="InductiveConstructor"
      >free-&#183;&#8322;</a
      ><a name="11039"
      > </a
      ><a name="11040" href="StlcProp.html#11040" class="Bound"
      >x&#8712;M</a
      ><a name="11043" class="Symbol"
      >)</a
      ><a name="11044"
      > </a
      ><a name="11045" class="Symbol"
      >(</a
      ><a name="11046" href="Stlc.html#21735" class="InductiveConstructor"
      >&#8658;-E</a
      ><a name="11049"
      > </a
      ><a name="11050" href="StlcProp.html#11050" class="Bound"
      >&#8866;L</a
      ><a name="11052"
      > </a
      ><a name="11053" href="StlcProp.html#11053" class="Bound"
      >&#8866;M</a
      ><a name="11055" class="Symbol"
      >)</a
      ><a name="11056"
      > </a
      ><a name="11057" class="Symbol"
      >=</a
      ><a name="11058"
      > </a
      ><a name="11059" href="StlcProp.html#9407" class="Function"
      >free-lemma</a
      ><a name="11069"
      > </a
      ><a name="11070" href="StlcProp.html#11040" class="Bound"
      >x&#8712;M</a
      ><a name="11073"
      > </a
      ><a name="11074" href="StlcProp.html#11053" class="Bound"
      >&#8866;M</a
      ><a name="11076"
      >
</a
      ><a name="11077" href="StlcProp.html#9407" class="Function"
      >free-lemma</a
      ><a name="11087"
      > </a
      ><a name="11088" class="Symbol"
      >(</a
      ><a name="11089" href="StlcProp.html#7917" class="InductiveConstructor"
      >free-if&#8321;</a
      ><a name="11097"
      > </a
      ><a name="11098" href="StlcProp.html#11098" class="Bound"
      >x&#8712;L</a
      ><a name="11101" class="Symbol"
      >)</a
      ><a name="11102"
      > </a
      ><a name="11103" class="Symbol"
      >(</a
      ><a name="11104" href="Stlc.html#21882" class="InductiveConstructor"
      >&#120121;-E</a
      ><a name="11107"
      > </a
      ><a name="11108" href="StlcProp.html#11108" class="Bound"
      >&#8866;L</a
      ><a name="11110"
      > </a
      ><a name="11111" href="StlcProp.html#11111" class="Bound"
      >&#8866;M</a
      ><a name="11113"
      > </a
      ><a name="11114" href="StlcProp.html#11114" class="Bound"
      >&#8866;N</a
      ><a name="11116" class="Symbol"
      >)</a
      ><a name="11117"
      > </a
      ><a name="11118" class="Symbol"
      >=</a
      ><a name="11119"
      > </a
      ><a name="11120" href="StlcProp.html#9407" class="Function"
      >free-lemma</a
      ><a name="11130"
      > </a
      ><a name="11131" href="StlcProp.html#11098" class="Bound"
      >x&#8712;L</a
      ><a name="11134"
      > </a
      ><a name="11135" href="StlcProp.html#11108" class="Bound"
      >&#8866;L</a
      ><a name="11137"
      >
</a
      ><a name="11138" href="StlcProp.html#9407" class="Function"
      >free-lemma</a
      ><a name="11148"
      > </a
      ><a name="11149" class="Symbol"
      >(</a
      ><a name="11150" href="StlcProp.html#7977" class="InductiveConstructor"
      >free-if&#8322;</a
      ><a name="11158"
      > </a
      ><a name="11159" href="StlcProp.html#11159" class="Bound"
      >x&#8712;M</a
      ><a name="11162" class="Symbol"
      >)</a
      ><a name="11163"
      > </a
      ><a name="11164" class="Symbol"
      >(</a
      ><a name="11165" href="Stlc.html#21882" class="InductiveConstructor"
      >&#120121;-E</a
      ><a name="11168"
      > </a
      ><a name="11169" href="StlcProp.html#11169" class="Bound"
      >&#8866;L</a
      ><a name="11171"
      > </a
      ><a name="11172" href="StlcProp.html#11172" class="Bound"
      >&#8866;M</a
      ><a name="11174"
      > </a
      ><a name="11175" href="StlcProp.html#11175" class="Bound"
      >&#8866;N</a
      ><a name="11177" class="Symbol"
      >)</a
      ><a name="11178"
      > </a
      ><a name="11179" class="Symbol"
      >=</a
      ><a name="11180"
      > </a
      ><a name="11181" href="StlcProp.html#9407" class="Function"
      >free-lemma</a
      ><a name="11191"
      > </a
      ><a name="11192" href="StlcProp.html#11159" class="Bound"
      >x&#8712;M</a
      ><a name="11195"
      > </a
      ><a name="11196" href="StlcProp.html#11172" class="Bound"
      >&#8866;M</a
      ><a name="11198"
      >
</a
      ><a name="11199" href="StlcProp.html#9407" class="Function"
      >free-lemma</a
      ><a name="11209"
      > </a
      ><a name="11210" class="Symbol"
      >(</a
      ><a name="11211" href="StlcProp.html#8037" class="InductiveConstructor"
      >free-if&#8323;</a
      ><a name="11219"
      > </a
      ><a name="11220" href="StlcProp.html#11220" class="Bound"
      >x&#8712;N</a
      ><a name="11223" class="Symbol"
      >)</a
      ><a name="11224"
      > </a
      ><a name="11225" class="Symbol"
      >(</a
      ><a name="11226" href="Stlc.html#21882" class="InductiveConstructor"
      >&#120121;-E</a
      ><a name="11229"
      > </a
      ><a name="11230" href="StlcProp.html#11230" class="Bound"
      >&#8866;L</a
      ><a name="11232"
      > </a
      ><a name="11233" href="StlcProp.html#11233" class="Bound"
      >&#8866;M</a
      ><a name="11235"
      > </a
      ><a name="11236" href="StlcProp.html#11236" class="Bound"
      >&#8866;N</a
      ><a name="11238" class="Symbol"
      >)</a
      ><a name="11239"
      > </a
      ><a name="11240" class="Symbol"
      >=</a
      ><a name="11241"
      > </a
      ><a name="11242" href="StlcProp.html#9407" class="Function"
      >free-lemma</a
      ><a name="11252"
      > </a
      ><a name="11253" href="StlcProp.html#11220" class="Bound"
      >x&#8712;N</a
      ><a name="11256"
      > </a
      ><a name="11257" href="StlcProp.html#11236" class="Bound"
      >&#8866;N</a
      ><a name="11259"
      >
</a
      ><a name="11260" href="StlcProp.html#9407" class="Function"
      >free-lemma</a
      ><a name="11270"
      > </a
      ><a name="11271" class="Symbol"
      >(</a
      ><a name="11272" href="StlcProp.html#7768" class="InductiveConstructor"
      >free-&#955;</a
      ><a name="11278"
      > </a
      ><a name="11279" class="Symbol"
      >{</a
      ><a name="11280" href="StlcProp.html#11280" class="Bound"
      >x</a
      ><a name="11281" class="Symbol"
      >}</a
      ><a name="11282"
      > </a
      ><a name="11283" class="Symbol"
      >{</a
      ><a name="11284" href="StlcProp.html#11284" class="Bound"
      >y</a
      ><a name="11285" class="Symbol"
      >}</a
      ><a name="11286"
      > </a
      ><a name="11287" href="StlcProp.html#11287" class="Bound"
      >y&#8802;x</a
      ><a name="11290"
      > </a
      ><a name="11291" href="StlcProp.html#11291" class="Bound"
      >x&#8712;N</a
      ><a name="11294" class="Symbol"
      >)</a
      ><a name="11295"
      > </a
      ><a name="11296" class="Symbol"
      >(</a
      ><a name="11297" href="Stlc.html#21658" class="InductiveConstructor"
      >&#8658;-I</a
      ><a name="11300"
      > </a
      ><a name="11301" href="StlcProp.html#11301" class="Bound"
      >&#8866;N</a
      ><a name="11303" class="Symbol"
      >)</a
      ><a name="11304"
      > </a
      ><a name="11305" class="Keyword"
      >with</a
      ><a name="11309"
      > </a
      ><a name="11310" href="StlcProp.html#9407" class="Function"
      >free-lemma</a
      ><a name="11320"
      > </a
      ><a name="11321" href="StlcProp.html#11291" class="Bound"
      >x&#8712;N</a
      ><a name="11324"
      > </a
      ><a name="11325" href="StlcProp.html#11301" class="Bound"
      >&#8866;N</a
      ><a name="11327"
      >
</a
      ><a name="11328" class="Symbol"
      >...</a
      ><a name="11331"
      > </a
      ><a name="11332" class="Symbol"
      >|</a
      ><a name="11333"
      > </a
      ><a name="11334" href="StlcProp.html#11334" class="Bound"
      >&#915;x&#8801;C</a
      ><a name="11338"
      > </a
      ><a name="11339" class="Keyword"
      >with</a
      ><a name="11343"
      > </a
      ><a name="11344" href="StlcProp.html#11284" class="Bound"
      >y</a
      ><a name="11345"
      > </a
      ><a name="11346" href="Maps.html#2509" class="Function Operator"
      >&#8799;</a
      ><a name="11347"
      > </a
      ><a name="11348" href="StlcProp.html#11280" class="Bound"
      >x</a
      ><a name="11349"
      >
</a
      ><a name="11350" class="Symbol"
      >...</a
      ><a name="11353"
      > </a
      ><a name="11354" class="Symbol"
      >|</a
      ><a name="11355"
      > </a
      ><a name="11356" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#520" class="InductiveConstructor"
      >yes</a
      ><a name="11359"
      > </a
      ><a name="11360" href="StlcProp.html#11360" class="Bound"
      >y&#8801;x</a
      ><a name="11363"
      > </a
      ><a name="11364" class="Symbol"
      >=</a
      ><a name="11365"
      > </a
      ><a name="11366" href="https://agda.github.io/agda-stdlib/Data.Empty.html#348" class="Function"
      >&#8869;-elim</a
      ><a name="11372"
      > </a
      ><a name="11373" class="Symbol"
      >(</a
      ><a name="11374" href="StlcProp.html#11287" class="Bound"
      >y&#8802;x</a
      ><a name="11377"
      > </a
      ><a name="11378" href="StlcProp.html#11360" class="Bound"
      >y&#8801;x</a
      ><a name="11381" class="Symbol"
      >)</a
      ><a name="11382"
      >
</a
      ><a name="11383" class="Symbol"
      >...</a
      ><a name="11386"
      > </a
      ><a name="11387" class="Symbol"
      >|</a
      ><a name="11388"
      > </a
      ><a name="11389" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#547" class="InductiveConstructor"
      >no</a
      ><a name="11391"
      >  </a
      ><a name="11393" class="Symbol"
      >_</a
      ><a name="11394"
      >   </a
      ><a name="11397" class="Symbol"
      >=</a
      ><a name="11398"
      > </a
      ><a name="11399" href="StlcProp.html#11334" class="Bound"
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

<a name="11836" class="Keyword"
      >postulate</a
      ><a name="11845"
      >
  </a
      ><a name="11848" href="StlcProp.html#11848" class="Postulate"
      >&#8709;&#8866;-closed</a
      ><a name="11857"
      > </a
      ><a name="11858" class="Symbol"
      >:</a
      ><a name="11859"
      > </a
      ><a name="11860" class="Symbol"
      >&#8704;</a
      ><a name="11861"
      > </a
      ><a name="11862" class="Symbol"
      >{</a
      ><a name="11863" href="StlcProp.html#11863" class="Bound"
      >M</a
      ><a name="11864"
      > </a
      ><a name="11865" href="StlcProp.html#11865" class="Bound"
      >A</a
      ><a name="11866" class="Symbol"
      >}</a
      ><a name="11867"
      > </a
      ><a name="11868" class="Symbol"
      >&#8594;</a
      ><a name="11869"
      > </a
      ><a name="11870" href="Maps.html#10265" class="Function"
      >&#8709;</a
      ><a name="11871"
      > </a
      ><a name="11872" href="Stlc.html#21560" class="Datatype Operator"
      >&#8866;</a
      ><a name="11873"
      > </a
      ><a name="11874" href="StlcProp.html#11863" class="Bound"
      >M</a
      ><a name="11875"
      > </a
      ><a name="11876" href="Stlc.html#21560" class="Datatype Operator"
      >&#8758;</a
      ><a name="11877"
      > </a
      ><a name="11878" href="StlcProp.html#11865" class="Bound"
      >A</a
      ><a name="11879"
      > </a
      ><a name="11880" class="Symbol"
      >&#8594;</a
      ><a name="11881"
      > </a
      ><a name="11882" href="StlcProp.html#8227" class="Function"
      >closed</a
      ><a name="11888"
      > </a
      ><a name="11889" href="StlcProp.html#11863" class="Bound"
      >M</a
      >

</pre>

<div class="hidden">
<pre class="Agda">

<a name="11937" href="StlcProp.html#11937" class="Function"
      >&#8709;&#8866;-closed&#8242;</a
      ><a name="11947"
      > </a
      ><a name="11948" class="Symbol"
      >:</a
      ><a name="11949"
      > </a
      ><a name="11950" class="Symbol"
      >&#8704;</a
      ><a name="11951"
      > </a
      ><a name="11952" class="Symbol"
      >{</a
      ><a name="11953" href="StlcProp.html#11953" class="Bound"
      >M</a
      ><a name="11954"
      > </a
      ><a name="11955" href="StlcProp.html#11955" class="Bound"
      >A</a
      ><a name="11956" class="Symbol"
      >}</a
      ><a name="11957"
      > </a
      ><a name="11958" class="Symbol"
      >&#8594;</a
      ><a name="11959"
      > </a
      ><a name="11960" href="Maps.html#10265" class="Function"
      >&#8709;</a
      ><a name="11961"
      > </a
      ><a name="11962" href="Stlc.html#21560" class="Datatype Operator"
      >&#8866;</a
      ><a name="11963"
      > </a
      ><a name="11964" href="StlcProp.html#11953" class="Bound"
      >M</a
      ><a name="11965"
      > </a
      ><a name="11966" href="Stlc.html#21560" class="Datatype Operator"
      >&#8758;</a
      ><a name="11967"
      > </a
      ><a name="11968" href="StlcProp.html#11955" class="Bound"
      >A</a
      ><a name="11969"
      > </a
      ><a name="11970" class="Symbol"
      >&#8594;</a
      ><a name="11971"
      > </a
      ><a name="11972" href="StlcProp.html#8227" class="Function"
      >closed</a
      ><a name="11978"
      > </a
      ><a name="11979" href="StlcProp.html#11953" class="Bound"
      >M</a
      ><a name="11980"
      >
</a
      ><a name="11981" href="StlcProp.html#11937" class="Function"
      >&#8709;&#8866;-closed&#8242;</a
      ><a name="11991"
      > </a
      ><a name="11992" class="Symbol"
      >{</a
      ><a name="11993" href="StlcProp.html#11993" class="Bound"
      >M</a
      ><a name="11994" class="Symbol"
      >}</a
      ><a name="11995"
      > </a
      ><a name="11996" class="Symbol"
      >{</a
      ><a name="11997" href="StlcProp.html#11997" class="Bound"
      >A</a
      ><a name="11998" class="Symbol"
      >}</a
      ><a name="11999"
      > </a
      ><a name="12000" href="StlcProp.html#12000" class="Bound"
      >&#8866;M</a
      ><a name="12002"
      > </a
      ><a name="12003" class="Symbol"
      >{</a
      ><a name="12004" href="StlcProp.html#12004" class="Bound"
      >x</a
      ><a name="12005" class="Symbol"
      >}</a
      ><a name="12006"
      > </a
      ><a name="12007" href="StlcProp.html#12007" class="Bound"
      >x&#8712;M</a
      ><a name="12010"
      > </a
      ><a name="12011" class="Keyword"
      >with</a
      ><a name="12015"
      > </a
      ><a name="12016" href="StlcProp.html#9407" class="Function"
      >free-lemma</a
      ><a name="12026"
      > </a
      ><a name="12027" href="StlcProp.html#12007" class="Bound"
      >x&#8712;M</a
      ><a name="12030"
      > </a
      ><a name="12031" href="StlcProp.html#12000" class="Bound"
      >&#8866;M</a
      ><a name="12033"
      >
</a
      ><a name="12034" class="Symbol"
      >...</a
      ><a name="12037"
      > </a
      ><a name="12038" class="Symbol"
      >|</a
      ><a name="12039"
      > </a
      ><a name="12040" class="Symbol"
      >(</a
      ><a name="12041" href="StlcProp.html#12041" class="Bound"
      >B</a
      ><a name="12042"
      > </a
      ><a name="12043" href="https://agda.github.io/agda-stdlib/Data.Product.html#509" class="InductiveConstructor Operator"
      >,</a
      ><a name="12044"
      > </a
      ><a name="12045" href="StlcProp.html#12045" class="Bound"
      >&#8709;x&#8801;B</a
      ><a name="12049" class="Symbol"
      >)</a
      ><a name="12050"
      > </a
      ><a name="12051" class="Symbol"
      >=</a
      ><a name="12052"
      > </a
      ><a name="12053" href="Maps.html#11818" class="Function"
      >just&#8802;nothing</a
      ><a name="12065"
      > </a
      ><a name="12066" class="Symbol"
      >(</a
      ><a name="12067" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.Core.html#632" class="Function"
      >trans</a
      ><a name="12072"
      > </a
      ><a name="12073" class="Symbol"
      >(</a
      ><a name="12074" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.Core.html#565" class="Function"
      >sym</a
      ><a name="12077"
      > </a
      ><a name="12078" href="StlcProp.html#12045" class="Bound"
      >&#8709;x&#8801;B</a
      ><a name="12082" class="Symbol"
      >)</a
      ><a name="12083"
      > </a
      ><a name="12084" class="Symbol"
      >(</a
      ><a name="12085" href="Maps.html#10573" class="Function"
      >apply-&#8709;</a
      ><a name="12092"
      > </a
      ><a name="12093" href="StlcProp.html#12004" class="Bound"
      >x</a
      ><a name="12094" class="Symbol"
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

<a name="12448" href="StlcProp.html#12448" class="Function"
      >context-lemma</a
      ><a name="12461"
      > </a
      ><a name="12462" class="Symbol"
      >:</a
      ><a name="12463"
      > </a
      ><a name="12464" class="Symbol"
      >&#8704;</a
      ><a name="12465"
      > </a
      ><a name="12466" class="Symbol"
      >{</a
      ><a name="12467" href="StlcProp.html#12467" class="Bound"
      >&#915;</a
      ><a name="12468"
      > </a
      ><a name="12469" href="StlcProp.html#12469" class="Bound"
      >&#915;&#8242;</a
      ><a name="12471"
      > </a
      ><a name="12472" href="StlcProp.html#12472" class="Bound"
      >M</a
      ><a name="12473"
      > </a
      ><a name="12474" href="StlcProp.html#12474" class="Bound"
      >A</a
      ><a name="12475" class="Symbol"
      >}</a
      ><a name="12476"
      >
        </a
      ><a name="12485" class="Symbol"
      >&#8594;</a
      ><a name="12486"
      > </a
      ><a name="12487" class="Symbol"
      >(&#8704;</a
      ><a name="12489"
      > </a
      ><a name="12490" class="Symbol"
      >{</a
      ><a name="12491" href="StlcProp.html#12491" class="Bound"
      >x</a
      ><a name="12492" class="Symbol"
      >}</a
      ><a name="12493"
      > </a
      ><a name="12494" class="Symbol"
      >&#8594;</a
      ><a name="12495"
      > </a
      ><a name="12496" href="StlcProp.html#12491" class="Bound"
      >x</a
      ><a name="12497"
      > </a
      ><a name="12498" href="StlcProp.html#7710" class="Datatype Operator"
      >&#8712;</a
      ><a name="12499"
      > </a
      ><a name="12500" href="StlcProp.html#12472" class="Bound"
      >M</a
      ><a name="12501"
      > </a
      ><a name="12502" class="Symbol"
      >&#8594;</a
      ><a name="12503"
      > </a
      ><a name="12504" href="StlcProp.html#12467" class="Bound"
      >&#915;</a
      ><a name="12505"
      > </a
      ><a name="12506" href="StlcProp.html#12491" class="Bound"
      >x</a
      ><a name="12507"
      > </a
      ><a name="12508" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="12509"
      > </a
      ><a name="12510" href="StlcProp.html#12469" class="Bound"
      >&#915;&#8242;</a
      ><a name="12512"
      > </a
      ><a name="12513" href="StlcProp.html#12491" class="Bound"
      >x</a
      ><a name="12514" class="Symbol"
      >)</a
      ><a name="12515"
      >
        </a
      ><a name="12524" class="Symbol"
      >&#8594;</a
      ><a name="12525"
      > </a
      ><a name="12526" href="StlcProp.html#12467" class="Bound"
      >&#915;</a
      ><a name="12527"
      >  </a
      ><a name="12529" href="Stlc.html#21560" class="Datatype Operator"
      >&#8866;</a
      ><a name="12530"
      > </a
      ><a name="12531" href="StlcProp.html#12472" class="Bound"
      >M</a
      ><a name="12532"
      > </a
      ><a name="12533" href="Stlc.html#21560" class="Datatype Operator"
      >&#8758;</a
      ><a name="12534"
      > </a
      ><a name="12535" href="StlcProp.html#12474" class="Bound"
      >A</a
      ><a name="12536"
      >
        </a
      ><a name="12545" class="Symbol"
      >&#8594;</a
      ><a name="12546"
      > </a
      ><a name="12547" href="StlcProp.html#12469" class="Bound"
      >&#915;&#8242;</a
      ><a name="12549"
      > </a
      ><a name="12550" href="Stlc.html#21560" class="Datatype Operator"
      >&#8866;</a
      ><a name="12551"
      > </a
      ><a name="12552" href="StlcProp.html#12472" class="Bound"
      >M</a
      ><a name="12553"
      > </a
      ><a name="12554" href="Stlc.html#21560" class="Datatype Operator"
      >&#8758;</a
      ><a name="12555"
      > </a
      ><a name="12556" href="StlcProp.html#12474" class="Bound"
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

<a name="14729" href="StlcProp.html#12448" class="Function"
      >context-lemma</a
      ><a name="14742"
      > </a
      ><a name="14743" href="StlcProp.html#14743" class="Bound"
      >&#915;~&#915;&#8242;</a
      ><a name="14747"
      > </a
      ><a name="14748" class="Symbol"
      >(</a
      ><a name="14749" href="Stlc.html#21604" class="InductiveConstructor"
      >Ax</a
      ><a name="14751"
      > </a
      ><a name="14752" href="StlcProp.html#14752" class="Bound"
      >&#915;x&#8801;A</a
      ><a name="14756" class="Symbol"
      >)</a
      ><a name="14757"
      > </a
      ><a name="14758" class="Keyword"
      >rewrite</a
      ><a name="14765"
      > </a
      ><a name="14766" class="Symbol"
      >(</a
      ><a name="14767" href="StlcProp.html#14743" class="Bound"
      >&#915;~&#915;&#8242;</a
      ><a name="14771"
      > </a
      ><a name="14772" href="StlcProp.html#7740" class="InductiveConstructor"
      >free-`</a
      ><a name="14778" class="Symbol"
      >)</a
      ><a name="14779"
      > </a
      ><a name="14780" class="Symbol"
      >=</a
      ><a name="14781"
      > </a
      ><a name="14782" href="Stlc.html#21604" class="InductiveConstructor"
      >Ax</a
      ><a name="14784"
      > </a
      ><a name="14785" href="StlcProp.html#14752" class="Bound"
      >&#915;x&#8801;A</a
      ><a name="14789"
      >
</a
      ><a name="14790" href="StlcProp.html#12448" class="Function"
      >context-lemma</a
      ><a name="14803"
      > </a
      ><a name="14804" class="Symbol"
      >{</a
      ><a name="14805" href="StlcProp.html#14805" class="Bound"
      >&#915;</a
      ><a name="14806" class="Symbol"
      >}</a
      ><a name="14807"
      > </a
      ><a name="14808" class="Symbol"
      >{</a
      ><a name="14809" href="StlcProp.html#14809" class="Bound"
      >&#915;&#8242;</a
      ><a name="14811" class="Symbol"
      >}</a
      ><a name="14812"
      > </a
      ><a name="14813" class="Symbol"
      >{</a
      ><a name="14814" href="Stlc.html#3663" class="InductiveConstructor Operator"
      >&#955;[</a
      ><a name="14816"
      > </a
      ><a name="14817" href="StlcProp.html#14817" class="Bound"
      >x</a
      ><a name="14818"
      > </a
      ><a name="14819" href="Stlc.html#3663" class="InductiveConstructor Operator"
      >&#8758;</a
      ><a name="14820"
      > </a
      ><a name="14821" href="StlcProp.html#14821" class="Bound"
      >A</a
      ><a name="14822"
      > </a
      ><a name="14823" href="Stlc.html#3663" class="InductiveConstructor Operator"
      >]</a
      ><a name="14824"
      > </a
      ><a name="14825" href="StlcProp.html#14825" class="Bound"
      >N</a
      ><a name="14826" class="Symbol"
      >}</a
      ><a name="14827"
      > </a
      ><a name="14828" href="StlcProp.html#14828" class="Bound"
      >&#915;~&#915;&#8242;</a
      ><a name="14832"
      > </a
      ><a name="14833" class="Symbol"
      >(</a
      ><a name="14834" href="Stlc.html#21658" class="InductiveConstructor"
      >&#8658;-I</a
      ><a name="14837"
      > </a
      ><a name="14838" href="StlcProp.html#14838" class="Bound"
      >&#8866;N</a
      ><a name="14840" class="Symbol"
      >)</a
      ><a name="14841"
      > </a
      ><a name="14842" class="Symbol"
      >=</a
      ><a name="14843"
      > </a
      ><a name="14844" href="Stlc.html#21658" class="InductiveConstructor"
      >&#8658;-I</a
      ><a name="14847"
      > </a
      ><a name="14848" class="Symbol"
      >(</a
      ><a name="14849" href="StlcProp.html#12448" class="Function"
      >context-lemma</a
      ><a name="14862"
      > </a
      ><a name="14863" href="StlcProp.html#14884" class="Function"
      >&#915;x~&#915;&#8242;x</a
      ><a name="14869"
      > </a
      ><a name="14870" href="StlcProp.html#14838" class="Bound"
      >&#8866;N</a
      ><a name="14872" class="Symbol"
      >)</a
      ><a name="14873"
      >
  </a
      ><a name="14876" class="Keyword"
      >where</a
      ><a name="14881"
      >
  </a
      ><a name="14884" href="StlcProp.html#14884" class="Function"
      >&#915;x~&#915;&#8242;x</a
      ><a name="14890"
      > </a
      ><a name="14891" class="Symbol"
      >:</a
      ><a name="14892"
      > </a
      ><a name="14893" class="Symbol"
      >&#8704;</a
      ><a name="14894"
      > </a
      ><a name="14895" class="Symbol"
      >{</a
      ><a name="14896" href="StlcProp.html#14896" class="Bound"
      >y</a
      ><a name="14897" class="Symbol"
      >}</a
      ><a name="14898"
      > </a
      ><a name="14899" class="Symbol"
      >&#8594;</a
      ><a name="14900"
      > </a
      ><a name="14901" href="StlcProp.html#14896" class="Bound"
      >y</a
      ><a name="14902"
      > </a
      ><a name="14903" href="StlcProp.html#7710" class="Datatype Operator"
      >&#8712;</a
      ><a name="14904"
      > </a
      ><a name="14905" href="StlcProp.html#14825" class="Bound"
      >N</a
      ><a name="14906"
      > </a
      ><a name="14907" class="Symbol"
      >&#8594;</a
      ><a name="14908"
      > </a
      ><a name="14909" class="Symbol"
      >(</a
      ><a name="14910" href="StlcProp.html#14805" class="Bound"
      >&#915;</a
      ><a name="14911"
      > </a
      ><a name="14912" href="Maps.html#10368" class="Function Operator"
      >,</a
      ><a name="14913"
      > </a
      ><a name="14914" href="StlcProp.html#14817" class="Bound"
      >x</a
      ><a name="14915"
      > </a
      ><a name="14916" href="Maps.html#10368" class="Function Operator"
      >&#8758;</a
      ><a name="14917"
      > </a
      ><a name="14918" href="StlcProp.html#14821" class="Bound"
      >A</a
      ><a name="14919" class="Symbol"
      >)</a
      ><a name="14920"
      > </a
      ><a name="14921" href="StlcProp.html#14896" class="Bound"
      >y</a
      ><a name="14922"
      > </a
      ><a name="14923" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="14924"
      > </a
      ><a name="14925" class="Symbol"
      >(</a
      ><a name="14926" href="StlcProp.html#14809" class="Bound"
      >&#915;&#8242;</a
      ><a name="14928"
      > </a
      ><a name="14929" href="Maps.html#10368" class="Function Operator"
      >,</a
      ><a name="14930"
      > </a
      ><a name="14931" href="StlcProp.html#14817" class="Bound"
      >x</a
      ><a name="14932"
      > </a
      ><a name="14933" href="Maps.html#10368" class="Function Operator"
      >&#8758;</a
      ><a name="14934"
      > </a
      ><a name="14935" href="StlcProp.html#14821" class="Bound"
      >A</a
      ><a name="14936" class="Symbol"
      >)</a
      ><a name="14937"
      > </a
      ><a name="14938" href="StlcProp.html#14896" class="Bound"
      >y</a
      ><a name="14939"
      >
  </a
      ><a name="14942" href="StlcProp.html#14884" class="Function"
      >&#915;x~&#915;&#8242;x</a
      ><a name="14948"
      > </a
      ><a name="14949" class="Symbol"
      >{</a
      ><a name="14950" href="StlcProp.html#14950" class="Bound"
      >y</a
      ><a name="14951" class="Symbol"
      >}</a
      ><a name="14952"
      > </a
      ><a name="14953" href="StlcProp.html#14953" class="Bound"
      >y&#8712;N</a
      ><a name="14956"
      > </a
      ><a name="14957" class="Keyword"
      >with</a
      ><a name="14961"
      > </a
      ><a name="14962" href="StlcProp.html#14817" class="Bound"
      >x</a
      ><a name="14963"
      > </a
      ><a name="14964" href="Maps.html#2509" class="Function Operator"
      >&#8799;</a
      ><a name="14965"
      > </a
      ><a name="14966" href="StlcProp.html#14950" class="Bound"
      >y</a
      ><a name="14967"
      >
  </a
      ><a name="14970" class="Symbol"
      >...</a
      ><a name="14973"
      > </a
      ><a name="14974" class="Symbol"
      >|</a
      ><a name="14975"
      > </a
      ><a name="14976" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#520" class="InductiveConstructor"
      >yes</a
      ><a name="14979"
      > </a
      ><a name="14980" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="14984"
      > </a
      ><a name="14985" class="Symbol"
      >=</a
      ><a name="14986"
      > </a
      ><a name="14987" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="14991"
      >
  </a
      ><a name="14994" class="Symbol"
      >...</a
      ><a name="14997"
      > </a
      ><a name="14998" class="Symbol"
      >|</a
      ><a name="14999"
      > </a
      ><a name="15000" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#547" class="InductiveConstructor"
      >no</a
      ><a name="15002"
      >  </a
      ><a name="15004" href="StlcProp.html#15004" class="Bound"
      >x&#8802;y</a
      ><a name="15007"
      >  </a
      ><a name="15009" class="Symbol"
      >=</a
      ><a name="15010"
      > </a
      ><a name="15011" href="StlcProp.html#14828" class="Bound"
      >&#915;~&#915;&#8242;</a
      ><a name="15015"
      > </a
      ><a name="15016" class="Symbol"
      >(</a
      ><a name="15017" href="StlcProp.html#7768" class="InductiveConstructor"
      >free-&#955;</a
      ><a name="15023"
      > </a
      ><a name="15024" href="StlcProp.html#15004" class="Bound"
      >x&#8802;y</a
      ><a name="15027"
      > </a
      ><a name="15028" href="StlcProp.html#14953" class="Bound"
      >y&#8712;N</a
      ><a name="15031" class="Symbol"
      >)</a
      ><a name="15032"
      >
</a
      ><a name="15033" href="StlcProp.html#12448" class="Function"
      >context-lemma</a
      ><a name="15046"
      > </a
      ><a name="15047" href="StlcProp.html#15047" class="Bound"
      >&#915;~&#915;&#8242;</a
      ><a name="15051"
      > </a
      ><a name="15052" class="Symbol"
      >(</a
      ><a name="15053" href="Stlc.html#21735" class="InductiveConstructor"
      >&#8658;-E</a
      ><a name="15056"
      > </a
      ><a name="15057" href="StlcProp.html#15057" class="Bound"
      >&#8866;L</a
      ><a name="15059"
      > </a
      ><a name="15060" href="StlcProp.html#15060" class="Bound"
      >&#8866;M</a
      ><a name="15062" class="Symbol"
      >)</a
      ><a name="15063"
      > </a
      ><a name="15064" class="Symbol"
      >=</a
      ><a name="15065"
      > </a
      ><a name="15066" href="Stlc.html#21735" class="InductiveConstructor"
      >&#8658;-E</a
      ><a name="15069"
      > </a
      ><a name="15070" class="Symbol"
      >(</a
      ><a name="15071" href="StlcProp.html#12448" class="Function"
      >context-lemma</a
      ><a name="15084"
      > </a
      ><a name="15085" class="Symbol"
      >(</a
      ><a name="15086" href="StlcProp.html#15047" class="Bound"
      >&#915;~&#915;&#8242;</a
      ><a name="15090"
      > </a
      ><a name="15091" href="https://agda.github.io/agda-stdlib/Function.html#713" class="Function Operator"
      >&#8728;</a
      ><a name="15092"
      > </a
      ><a name="15093" href="StlcProp.html#7829" class="InductiveConstructor"
      >free-&#183;&#8321;</a
      ><a name="15100" class="Symbol"
      >)</a
      ><a name="15101"
      >  </a
      ><a name="15103" href="StlcProp.html#15057" class="Bound"
      >&#8866;L</a
      ><a name="15105" class="Symbol"
      >)</a
      ><a name="15106"
      >
                                       </a
      ><a name="15146" class="Symbol"
      >(</a
      ><a name="15147" href="StlcProp.html#12448" class="Function"
      >context-lemma</a
      ><a name="15160"
      > </a
      ><a name="15161" class="Symbol"
      >(</a
      ><a name="15162" href="StlcProp.html#15047" class="Bound"
      >&#915;~&#915;&#8242;</a
      ><a name="15166"
      > </a
      ><a name="15167" href="https://agda.github.io/agda-stdlib/Function.html#713" class="Function Operator"
      >&#8728;</a
      ><a name="15168"
      > </a
      ><a name="15169" href="StlcProp.html#7873" class="InductiveConstructor"
      >free-&#183;&#8322;</a
      ><a name="15176" class="Symbol"
      >)</a
      ><a name="15177"
      > </a
      ><a name="15178" href="StlcProp.html#15060" class="Bound"
      >&#8866;M</a
      ><a name="15180" class="Symbol"
      >)</a
      ><a name="15181"
      > 
</a
      ><a name="15183" href="StlcProp.html#12448" class="Function"
      >context-lemma</a
      ><a name="15196"
      > </a
      ><a name="15197" href="StlcProp.html#15197" class="Bound"
      >&#915;~&#915;&#8242;</a
      ><a name="15201"
      > </a
      ><a name="15202" href="Stlc.html#21813" class="InductiveConstructor"
      >&#120121;-I&#8321;</a
      ><a name="15206"
      > </a
      ><a name="15207" class="Symbol"
      >=</a
      ><a name="15208"
      > </a
      ><a name="15209" href="Stlc.html#21813" class="InductiveConstructor"
      >&#120121;-I&#8321;</a
      ><a name="15213"
      >
</a
      ><a name="15214" href="StlcProp.html#12448" class="Function"
      >context-lemma</a
      ><a name="15227"
      > </a
      ><a name="15228" href="StlcProp.html#15228" class="Bound"
      >&#915;~&#915;&#8242;</a
      ><a name="15232"
      > </a
      ><a name="15233" href="Stlc.html#21847" class="InductiveConstructor"
      >&#120121;-I&#8322;</a
      ><a name="15237"
      > </a
      ><a name="15238" class="Symbol"
      >=</a
      ><a name="15239"
      > </a
      ><a name="15240" href="Stlc.html#21847" class="InductiveConstructor"
      >&#120121;-I&#8322;</a
      ><a name="15244"
      >
</a
      ><a name="15245" href="StlcProp.html#12448" class="Function"
      >context-lemma</a
      ><a name="15258"
      > </a
      ><a name="15259" href="StlcProp.html#15259" class="Bound"
      >&#915;~&#915;&#8242;</a
      ><a name="15263"
      > </a
      ><a name="15264" class="Symbol"
      >(</a
      ><a name="15265" href="Stlc.html#21882" class="InductiveConstructor"
      >&#120121;-E</a
      ><a name="15268"
      > </a
      ><a name="15269" href="StlcProp.html#15269" class="Bound"
      >&#8866;L</a
      ><a name="15271"
      > </a
      ><a name="15272" href="StlcProp.html#15272" class="Bound"
      >&#8866;M</a
      ><a name="15274"
      > </a
      ><a name="15275" href="StlcProp.html#15275" class="Bound"
      >&#8866;N</a
      ><a name="15277" class="Symbol"
      >)</a
      ><a name="15278"
      > </a
      ><a name="15279" class="Symbol"
      >=</a
      ><a name="15280"
      > </a
      ><a name="15281" href="Stlc.html#21882" class="InductiveConstructor"
      >&#120121;-E</a
      ><a name="15284"
      > </a
      ><a name="15285" class="Symbol"
      >(</a
      ><a name="15286" href="StlcProp.html#12448" class="Function"
      >context-lemma</a
      ><a name="15299"
      > </a
      ><a name="15300" class="Symbol"
      >(</a
      ><a name="15301" href="StlcProp.html#15259" class="Bound"
      >&#915;~&#915;&#8242;</a
      ><a name="15305"
      > </a
      ><a name="15306" href="https://agda.github.io/agda-stdlib/Function.html#713" class="Function Operator"
      >&#8728;</a
      ><a name="15307"
      > </a
      ><a name="15308" href="StlcProp.html#7917" class="InductiveConstructor"
      >free-if&#8321;</a
      ><a name="15316" class="Symbol"
      >)</a
      ><a name="15317"
      > </a
      ><a name="15318" href="StlcProp.html#15269" class="Bound"
      >&#8866;L</a
      ><a name="15320" class="Symbol"
      >)</a
      ><a name="15321"
      >
                                         </a
      ><a name="15363" class="Symbol"
      >(</a
      ><a name="15364" href="StlcProp.html#12448" class="Function"
      >context-lemma</a
      ><a name="15377"
      > </a
      ><a name="15378" class="Symbol"
      >(</a
      ><a name="15379" href="StlcProp.html#15259" class="Bound"
      >&#915;~&#915;&#8242;</a
      ><a name="15383"
      > </a
      ><a name="15384" href="https://agda.github.io/agda-stdlib/Function.html#713" class="Function Operator"
      >&#8728;</a
      ><a name="15385"
      > </a
      ><a name="15386" href="StlcProp.html#7977" class="InductiveConstructor"
      >free-if&#8322;</a
      ><a name="15394" class="Symbol"
      >)</a
      ><a name="15395"
      > </a
      ><a name="15396" href="StlcProp.html#15272" class="Bound"
      >&#8866;M</a
      ><a name="15398" class="Symbol"
      >)</a
      ><a name="15399"
      >
                                         </a
      ><a name="15441" class="Symbol"
      >(</a
      ><a name="15442" href="StlcProp.html#12448" class="Function"
      >context-lemma</a
      ><a name="15455"
      > </a
      ><a name="15456" class="Symbol"
      >(</a
      ><a name="15457" href="StlcProp.html#15259" class="Bound"
      >&#915;~&#915;&#8242;</a
      ><a name="15461"
      > </a
      ><a name="15462" href="https://agda.github.io/agda-stdlib/Function.html#713" class="Function Operator"
      >&#8728;</a
      ><a name="15463"
      > </a
      ><a name="15464" href="StlcProp.html#8037" class="InductiveConstructor"
      >free-if&#8323;</a
      ><a name="15472" class="Symbol"
      >)</a
      ><a name="15473"
      > </a
      ><a name="15474" href="StlcProp.html#15275" class="Bound"
      >&#8866;N</a
      ><a name="15476" class="Symbol"
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

<a name="16175" href="StlcProp.html#16175" class="Function"
      >preservation-[:=]</a
      ><a name="16192"
      > </a
      ><a name="16193" class="Symbol"
      >:</a
      ><a name="16194"
      > </a
      ><a name="16195" class="Symbol"
      >&#8704;</a
      ><a name="16196"
      > </a
      ><a name="16197" class="Symbol"
      >{</a
      ><a name="16198" href="StlcProp.html#16198" class="Bound"
      >&#915;</a
      ><a name="16199"
      > </a
      ><a name="16200" href="StlcProp.html#16200" class="Bound"
      >x</a
      ><a name="16201"
      > </a
      ><a name="16202" href="StlcProp.html#16202" class="Bound"
      >A</a
      ><a name="16203"
      > </a
      ><a name="16204" href="StlcProp.html#16204" class="Bound"
      >N</a
      ><a name="16205"
      > </a
      ><a name="16206" href="StlcProp.html#16206" class="Bound"
      >B</a
      ><a name="16207"
      > </a
      ><a name="16208" href="StlcProp.html#16208" class="Bound"
      >V</a
      ><a name="16209" class="Symbol"
      >}</a
      ><a name="16210"
      >
                 </a
      ><a name="16228" class="Symbol"
      >&#8594;</a
      ><a name="16229"
      > </a
      ><a name="16230" class="Symbol"
      >(</a
      ><a name="16231" href="StlcProp.html#16198" class="Bound"
      >&#915;</a
      ><a name="16232"
      > </a
      ><a name="16233" href="Maps.html#10368" class="Function Operator"
      >,</a
      ><a name="16234"
      > </a
      ><a name="16235" href="StlcProp.html#16200" class="Bound"
      >x</a
      ><a name="16236"
      > </a
      ><a name="16237" href="Maps.html#10368" class="Function Operator"
      >&#8758;</a
      ><a name="16238"
      > </a
      ><a name="16239" href="StlcProp.html#16202" class="Bound"
      >A</a
      ><a name="16240" class="Symbol"
      >)</a
      ><a name="16241"
      > </a
      ><a name="16242" href="Stlc.html#21560" class="Datatype Operator"
      >&#8866;</a
      ><a name="16243"
      > </a
      ><a name="16244" href="StlcProp.html#16204" class="Bound"
      >N</a
      ><a name="16245"
      > </a
      ><a name="16246" href="Stlc.html#21560" class="Datatype Operator"
      >&#8758;</a
      ><a name="16247"
      > </a
      ><a name="16248" href="StlcProp.html#16206" class="Bound"
      >B</a
      ><a name="16249"
      >
                 </a
      ><a name="16267" class="Symbol"
      >&#8594;</a
      ><a name="16268"
      > </a
      ><a name="16269" href="Maps.html#10265" class="Function"
      >&#8709;</a
      ><a name="16270"
      > </a
      ><a name="16271" href="Stlc.html#21560" class="Datatype Operator"
      >&#8866;</a
      ><a name="16272"
      > </a
      ><a name="16273" href="StlcProp.html#16208" class="Bound"
      >V</a
      ><a name="16274"
      > </a
      ><a name="16275" href="Stlc.html#21560" class="Datatype Operator"
      >&#8758;</a
      ><a name="16276"
      > </a
      ><a name="16277" href="StlcProp.html#16202" class="Bound"
      >A</a
      ><a name="16278"
      >
                 </a
      ><a name="16296" class="Symbol"
      >&#8594;</a
      ><a name="16297"
      > </a
      ><a name="16298" href="StlcProp.html#16198" class="Bound"
      >&#915;</a
      ><a name="16299"
      > </a
      ><a name="16300" href="Stlc.html#21560" class="Datatype Operator"
      >&#8866;</a
      ><a name="16301"
      > </a
      ><a name="16302" class="Symbol"
      >(</a
      ><a name="16303" href="StlcProp.html#16204" class="Bound"
      >N</a
      ><a name="16304"
      > </a
      ><a name="16305" href="Stlc.html#12070" class="Function Operator"
      >[</a
      ><a name="16306"
      > </a
      ><a name="16307" href="StlcProp.html#16200" class="Bound"
      >x</a
      ><a name="16308"
      > </a
      ><a name="16309" href="Stlc.html#12070" class="Function Operator"
      >:=</a
      ><a name="16311"
      > </a
      ><a name="16312" href="StlcProp.html#16208" class="Bound"
      >V</a
      ><a name="16313"
      > </a
      ><a name="16314" href="Stlc.html#12070" class="Function Operator"
      >]</a
      ><a name="16315" class="Symbol"
      >)</a
      ><a name="16316"
      > </a
      ><a name="16317" href="Stlc.html#21560" class="Datatype Operator"
      >&#8758;</a
      ><a name="16318"
      > </a
      ><a name="16319" href="StlcProp.html#16206" class="Bound"
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

<a name="19476" href="StlcProp.html#19476" class="Function"
      >weaken-closed</a
      ><a name="19489"
      > </a
      ><a name="19490" class="Symbol"
      >:</a
      ><a name="19491"
      > </a
      ><a name="19492" class="Symbol"
      >&#8704;</a
      ><a name="19493"
      > </a
      ><a name="19494" class="Symbol"
      >{</a
      ><a name="19495" href="StlcProp.html#19495" class="Bound"
      >V</a
      ><a name="19496"
      > </a
      ><a name="19497" href="StlcProp.html#19497" class="Bound"
      >A</a
      ><a name="19498"
      > </a
      ><a name="19499" href="StlcProp.html#19499" class="Bound"
      >&#915;</a
      ><a name="19500" class="Symbol"
      >}</a
      ><a name="19501"
      > </a
      ><a name="19502" class="Symbol"
      >&#8594;</a
      ><a name="19503"
      > </a
      ><a name="19504" href="Maps.html#10265" class="Function"
      >&#8709;</a
      ><a name="19505"
      > </a
      ><a name="19506" href="Stlc.html#21560" class="Datatype Operator"
      >&#8866;</a
      ><a name="19507"
      > </a
      ><a name="19508" href="StlcProp.html#19495" class="Bound"
      >V</a
      ><a name="19509"
      > </a
      ><a name="19510" href="Stlc.html#21560" class="Datatype Operator"
      >&#8758;</a
      ><a name="19511"
      > </a
      ><a name="19512" href="StlcProp.html#19497" class="Bound"
      >A</a
      ><a name="19513"
      > </a
      ><a name="19514" class="Symbol"
      >&#8594;</a
      ><a name="19515"
      > </a
      ><a name="19516" href="StlcProp.html#19499" class="Bound"
      >&#915;</a
      ><a name="19517"
      > </a
      ><a name="19518" href="Stlc.html#21560" class="Datatype Operator"
      >&#8866;</a
      ><a name="19519"
      > </a
      ><a name="19520" href="StlcProp.html#19495" class="Bound"
      >V</a
      ><a name="19521"
      > </a
      ><a name="19522" href="Stlc.html#21560" class="Datatype Operator"
      >&#8758;</a
      ><a name="19523"
      > </a
      ><a name="19524" href="StlcProp.html#19497" class="Bound"
      >A</a
      ><a name="19525"
      >
</a
      ><a name="19526" href="StlcProp.html#19476" class="Function"
      >weaken-closed</a
      ><a name="19539"
      > </a
      ><a name="19540" class="Symbol"
      >{</a
      ><a name="19541" href="StlcProp.html#19541" class="Bound"
      >V</a
      ><a name="19542" class="Symbol"
      >}</a
      ><a name="19543"
      > </a
      ><a name="19544" class="Symbol"
      >{</a
      ><a name="19545" href="StlcProp.html#19545" class="Bound"
      >A</a
      ><a name="19546" class="Symbol"
      >}</a
      ><a name="19547"
      > </a
      ><a name="19548" class="Symbol"
      >{</a
      ><a name="19549" href="StlcProp.html#19549" class="Bound"
      >&#915;</a
      ><a name="19550" class="Symbol"
      >}</a
      ><a name="19551"
      > </a
      ><a name="19552" href="StlcProp.html#19552" class="Bound"
      >&#8866;V</a
      ><a name="19554"
      > </a
      ><a name="19555" class="Symbol"
      >=</a
      ><a name="19556"
      > </a
      ><a name="19557" href="StlcProp.html#12448" class="Function"
      >context-lemma</a
      ><a name="19570"
      > </a
      ><a name="19571" href="StlcProp.html#19589" class="Function"
      >&#915;~&#915;&#8242;</a
      ><a name="19575"
      > </a
      ><a name="19576" href="StlcProp.html#19552" class="Bound"
      >&#8866;V</a
      ><a name="19578"
      >
  </a
      ><a name="19581" class="Keyword"
      >where</a
      ><a name="19586"
      >
  </a
      ><a name="19589" href="StlcProp.html#19589" class="Function"
      >&#915;~&#915;&#8242;</a
      ><a name="19593"
      > </a
      ><a name="19594" class="Symbol"
      >:</a
      ><a name="19595"
      > </a
      ><a name="19596" class="Symbol"
      >&#8704;</a
      ><a name="19597"
      > </a
      ><a name="19598" class="Symbol"
      >{</a
      ><a name="19599" href="StlcProp.html#19599" class="Bound"
      >x</a
      ><a name="19600" class="Symbol"
      >}</a
      ><a name="19601"
      > </a
      ><a name="19602" class="Symbol"
      >&#8594;</a
      ><a name="19603"
      > </a
      ><a name="19604" href="StlcProp.html#19599" class="Bound"
      >x</a
      ><a name="19605"
      > </a
      ><a name="19606" href="StlcProp.html#7710" class="Datatype Operator"
      >&#8712;</a
      ><a name="19607"
      > </a
      ><a name="19608" href="StlcProp.html#19541" class="Bound"
      >V</a
      ><a name="19609"
      > </a
      ><a name="19610" class="Symbol"
      >&#8594;</a
      ><a name="19611"
      > </a
      ><a name="19612" href="Maps.html#10265" class="Function"
      >&#8709;</a
      ><a name="19613"
      > </a
      ><a name="19614" href="StlcProp.html#19599" class="Bound"
      >x</a
      ><a name="19615"
      > </a
      ><a name="19616" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="19617"
      > </a
      ><a name="19618" href="StlcProp.html#19549" class="Bound"
      >&#915;</a
      ><a name="19619"
      > </a
      ><a name="19620" href="StlcProp.html#19599" class="Bound"
      >x</a
      ><a name="19621"
      >
  </a
      ><a name="19624" href="StlcProp.html#19589" class="Function"
      >&#915;~&#915;&#8242;</a
      ><a name="19628"
      > </a
      ><a name="19629" class="Symbol"
      >{</a
      ><a name="19630" href="StlcProp.html#19630" class="Bound"
      >x</a
      ><a name="19631" class="Symbol"
      >}</a
      ><a name="19632"
      > </a
      ><a name="19633" href="StlcProp.html#19633" class="Bound"
      >x&#8712;V</a
      ><a name="19636"
      > </a
      ><a name="19637" class="Symbol"
      >=</a
      ><a name="19638"
      > </a
      ><a name="19639" href="https://agda.github.io/agda-stdlib/Data.Empty.html#348" class="Function"
      >&#8869;-elim</a
      ><a name="19645"
      > </a
      ><a name="19646" class="Symbol"
      >(</a
      ><a name="19647" href="StlcProp.html#19670" class="Function"
      >x&#8713;V</a
      ><a name="19650"
      > </a
      ><a name="19651" href="StlcProp.html#19633" class="Bound"
      >x&#8712;V</a
      ><a name="19654" class="Symbol"
      >)</a
      ><a name="19655"
      >
    </a
      ><a name="19660" class="Keyword"
      >where</a
      ><a name="19665"
      >
    </a
      ><a name="19670" href="StlcProp.html#19670" class="Function"
      >x&#8713;V</a
      ><a name="19673"
      > </a
      ><a name="19674" class="Symbol"
      >:</a
      ><a name="19675"
      > </a
      ><a name="19676" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#414" class="Function Operator"
      >&#172;</a
      ><a name="19677"
      > </a
      ><a name="19678" class="Symbol"
      >(</a
      ><a name="19679" href="StlcProp.html#19630" class="Bound"
      >x</a
      ><a name="19680"
      > </a
      ><a name="19681" href="StlcProp.html#7710" class="Datatype Operator"
      >&#8712;</a
      ><a name="19682"
      > </a
      ><a name="19683" href="StlcProp.html#19541" class="Bound"
      >V</a
      ><a name="19684" class="Symbol"
      >)</a
      ><a name="19685"
      >
    </a
      ><a name="19690" href="StlcProp.html#19670" class="Function"
      >x&#8713;V</a
      ><a name="19693"
      > </a
      ><a name="19694" class="Symbol"
      >=</a
      ><a name="19695"
      > </a
      ><a name="19696" href="StlcProp.html#11848" class="Postulate"
      >&#8709;&#8866;-closed</a
      ><a name="19705"
      > </a
      ><a name="19706" href="StlcProp.html#19552" class="Bound"
      >&#8866;V</a
      ><a name="19708"
      > </a
      ><a name="19709" class="Symbol"
      >{</a
      ><a name="19710" href="StlcProp.html#19630" class="Bound"
      >x</a
      ><a name="19711" class="Symbol"
      >}</a
      >

</pre>

<pre class="Agda">

<a name="19739" href="StlcProp.html#16175" class="Function"
      >preservation-[:=]</a
      ><a name="19756"
      > </a
      ><a name="19757" class="Symbol"
      >{</a
      ><a name="19758" href="StlcProp.html#19758" class="Bound"
      >&#915;</a
      ><a name="19759" class="Symbol"
      >}</a
      ><a name="19760"
      > </a
      ><a name="19761" class="Symbol"
      >{</a
      ><a name="19762" href="StlcProp.html#19762" class="Bound"
      >x</a
      ><a name="19763" class="Symbol"
      >}</a
      ><a name="19764"
      > </a
      ><a name="19765" class="Symbol"
      >{</a
      ><a name="19766" href="StlcProp.html#19766" class="Bound"
      >A</a
      ><a name="19767" class="Symbol"
      >}</a
      ><a name="19768"
      > </a
      ><a name="19769" class="Symbol"
      >(</a
      ><a name="19770" href="Stlc.html#21604" class="InductiveConstructor"
      >Ax</a
      ><a name="19772"
      > </a
      ><a name="19773" class="Symbol"
      >{</a
      ><a name="19774" href="StlcProp.html#19774" class="Bound"
      >&#915;,x&#8758;A</a
      ><a name="19779" class="Symbol"
      >}</a
      ><a name="19780"
      > </a
      ><a name="19781" class="Symbol"
      >{</a
      ><a name="19782" href="StlcProp.html#19782" class="Bound"
      >x&#8242;</a
      ><a name="19784" class="Symbol"
      >}</a
      ><a name="19785"
      > </a
      ><a name="19786" class="Symbol"
      >{</a
      ><a name="19787" href="StlcProp.html#19787" class="Bound"
      >B</a
      ><a name="19788" class="Symbol"
      >}</a
      ><a name="19789"
      > </a
      ><a name="19790" href="StlcProp.html#19790" class="Bound"
      >[&#915;,x&#8758;A]x&#8242;&#8801;B</a
      ><a name="19801" class="Symbol"
      >)</a
      ><a name="19802"
      > </a
      ><a name="19803" href="StlcProp.html#19803" class="Bound"
      >&#8866;V</a
      ><a name="19805"
      > </a
      ><a name="19806" class="Keyword"
      >with</a
      ><a name="19810"
      > </a
      ><a name="19811" href="StlcProp.html#19762" class="Bound"
      >x</a
      ><a name="19812"
      > </a
      ><a name="19813" href="Maps.html#2509" class="Function Operator"
      >&#8799;</a
      ><a name="19814"
      > </a
      ><a name="19815" href="StlcProp.html#19782" class="Bound"
      >x&#8242;</a
      ><a name="19817"
      >
</a
      ><a name="19818" class="Symbol"
      >...|</a
      ><a name="19822"
      > </a
      ><a name="19823" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#520" class="InductiveConstructor"
      >yes</a
      ><a name="19826"
      > </a
      ><a name="19827" href="StlcProp.html#19827" class="Bound"
      >x&#8801;x&#8242;</a
      ><a name="19831"
      > </a
      ><a name="19832" class="Keyword"
      >rewrite</a
      ><a name="19839"
      > </a
      ><a name="19840" href="Maps.html#11919" class="Function"
      >just-injective</a
      ><a name="19854"
      > </a
      ><a name="19855" href="StlcProp.html#19790" class="Bound"
      >[&#915;,x&#8758;A]x&#8242;&#8801;B</a
      ><a name="19866"
      >  </a
      ><a name="19868" class="Symbol"
      >=</a
      ><a name="19869"
      >  </a
      ><a name="19871" href="StlcProp.html#19476" class="Function"
      >weaken-closed</a
      ><a name="19884"
      > </a
      ><a name="19885" href="StlcProp.html#19803" class="Bound"
      >&#8866;V</a
      ><a name="19887"
      >
</a
      ><a name="19888" class="Symbol"
      >...|</a
      ><a name="19892"
      > </a
      ><a name="19893" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#547" class="InductiveConstructor"
      >no</a
      ><a name="19895"
      >  </a
      ><a name="19897" href="StlcProp.html#19897" class="Bound"
      >x&#8802;x&#8242;</a
      ><a name="19901"
      >  </a
      ><a name="19903" class="Symbol"
      >=</a
      ><a name="19904"
      >  </a
      ><a name="19906" href="Stlc.html#21604" class="InductiveConstructor"
      >Ax</a
      ><a name="19908"
      > </a
      ><a name="19909" href="StlcProp.html#19790" class="Bound"
      >[&#915;,x&#8758;A]x&#8242;&#8801;B</a
      ><a name="19920"
      >
</a
      ><a name="19921" href="StlcProp.html#16175" class="Function"
      >preservation-[:=]</a
      ><a name="19938"
      > </a
      ><a name="19939" class="Symbol"
      >{</a
      ><a name="19940" href="StlcProp.html#19940" class="Bound"
      >&#915;</a
      ><a name="19941" class="Symbol"
      >}</a
      ><a name="19942"
      > </a
      ><a name="19943" class="Symbol"
      >{</a
      ><a name="19944" href="StlcProp.html#19944" class="Bound"
      >x</a
      ><a name="19945" class="Symbol"
      >}</a
      ><a name="19946"
      > </a
      ><a name="19947" class="Symbol"
      >{</a
      ><a name="19948" href="StlcProp.html#19948" class="Bound"
      >A</a
      ><a name="19949" class="Symbol"
      >}</a
      ><a name="19950"
      > </a
      ><a name="19951" class="Symbol"
      >{</a
      ><a name="19952" href="Stlc.html#3663" class="InductiveConstructor Operator"
      >&#955;[</a
      ><a name="19954"
      > </a
      ><a name="19955" href="StlcProp.html#19955" class="Bound"
      >x&#8242;</a
      ><a name="19957"
      > </a
      ><a name="19958" href="Stlc.html#3663" class="InductiveConstructor Operator"
      >&#8758;</a
      ><a name="19959"
      > </a
      ><a name="19960" href="StlcProp.html#19960" class="Bound"
      >A&#8242;</a
      ><a name="19962"
      > </a
      ><a name="19963" href="Stlc.html#3663" class="InductiveConstructor Operator"
      >]</a
      ><a name="19964"
      > </a
      ><a name="19965" href="StlcProp.html#19965" class="Bound"
      >N&#8242;</a
      ><a name="19967" class="Symbol"
      >}</a
      ><a name="19968"
      > </a
      ><a name="19969" class="Symbol"
      >{</a
      ><a name="19970" class="DottedPattern Symbol"
      >.</a
      ><a name="19971" href="StlcProp.html#19960" class="DottedPattern Bound"
      >A&#8242;</a
      ><a name="19973"
      > </a
      ><a name="19974" href="Stlc.html#2574" class="InductiveConstructor Operator"
      >&#8658;</a
      ><a name="19975"
      > </a
      ><a name="19976" href="StlcProp.html#19976" class="Bound"
      >B&#8242;</a
      ><a name="19978" class="Symbol"
      >}</a
      ><a name="19979"
      > </a
      ><a name="19980" class="Symbol"
      >{</a
      ><a name="19981" href="StlcProp.html#19981" class="Bound"
      >V</a
      ><a name="19982" class="Symbol"
      >}</a
      ><a name="19983"
      > </a
      ><a name="19984" class="Symbol"
      >(</a
      ><a name="19985" href="Stlc.html#21658" class="InductiveConstructor"
      >&#8658;-I</a
      ><a name="19988"
      > </a
      ><a name="19989" href="StlcProp.html#19989" class="Bound"
      >&#8866;N&#8242;</a
      ><a name="19992" class="Symbol"
      >)</a
      ><a name="19993"
      > </a
      ><a name="19994" href="StlcProp.html#19994" class="Bound"
      >&#8866;V</a
      ><a name="19996"
      > </a
      ><a name="19997" class="Keyword"
      >with</a
      ><a name="20001"
      > </a
      ><a name="20002" href="StlcProp.html#19944" class="Bound"
      >x</a
      ><a name="20003"
      > </a
      ><a name="20004" href="Maps.html#2509" class="Function Operator"
      >&#8799;</a
      ><a name="20005"
      > </a
      ><a name="20006" href="StlcProp.html#19955" class="Bound"
      >x&#8242;</a
      ><a name="20008"
      >
</a
      ><a name="20009" class="Symbol"
      >...|</a
      ><a name="20013"
      > </a
      ><a name="20014" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#520" class="InductiveConstructor"
      >yes</a
      ><a name="20017"
      > </a
      ><a name="20018" href="StlcProp.html#20018" class="Bound"
      >x&#8801;x&#8242;</a
      ><a name="20022"
      > </a
      ><a name="20023" class="Keyword"
      >rewrite</a
      ><a name="20030"
      > </a
      ><a name="20031" href="StlcProp.html#20018" class="Bound"
      >x&#8801;x&#8242;</a
      ><a name="20035"
      > </a
      ><a name="20036" class="Symbol"
      >=</a
      ><a name="20037"
      > </a
      ><a name="20038" href="StlcProp.html#12448" class="Function"
      >context-lemma</a
      ><a name="20051"
      > </a
      ><a name="20052" href="StlcProp.html#20077" class="Function"
      >&#915;&#8242;~&#915;</a
      ><a name="20056"
      > </a
      ><a name="20057" class="Symbol"
      >(</a
      ><a name="20058" href="Stlc.html#21658" class="InductiveConstructor"
      >&#8658;-I</a
      ><a name="20061"
      > </a
      ><a name="20062" href="StlcProp.html#19989" class="Bound"
      >&#8866;N&#8242;</a
      ><a name="20065" class="Symbol"
      >)</a
      ><a name="20066"
      >
  </a
      ><a name="20069" class="Keyword"
      >where</a
      ><a name="20074"
      >
  </a
      ><a name="20077" href="StlcProp.html#20077" class="Function"
      >&#915;&#8242;~&#915;</a
      ><a name="20081"
      > </a
      ><a name="20082" class="Symbol"
      >:</a
      ><a name="20083"
      > </a
      ><a name="20084" class="Symbol"
      >&#8704;</a
      ><a name="20085"
      > </a
      ><a name="20086" class="Symbol"
      >{</a
      ><a name="20087" href="StlcProp.html#20087" class="Bound"
      >y</a
      ><a name="20088" class="Symbol"
      >}</a
      ><a name="20089"
      > </a
      ><a name="20090" class="Symbol"
      >&#8594;</a
      ><a name="20091"
      > </a
      ><a name="20092" href="StlcProp.html#20087" class="Bound"
      >y</a
      ><a name="20093"
      > </a
      ><a name="20094" href="StlcProp.html#7710" class="Datatype Operator"
      >&#8712;</a
      ><a name="20095"
      > </a
      ><a name="20096" class="Symbol"
      >(</a
      ><a name="20097" href="Stlc.html#3663" class="InductiveConstructor Operator"
      >&#955;[</a
      ><a name="20099"
      > </a
      ><a name="20100" href="StlcProp.html#19955" class="Bound"
      >x&#8242;</a
      ><a name="20102"
      > </a
      ><a name="20103" href="Stlc.html#3663" class="InductiveConstructor Operator"
      >&#8758;</a
      ><a name="20104"
      > </a
      ><a name="20105" href="StlcProp.html#19960" class="Bound"
      >A&#8242;</a
      ><a name="20107"
      > </a
      ><a name="20108" href="Stlc.html#3663" class="InductiveConstructor Operator"
      >]</a
      ><a name="20109"
      > </a
      ><a name="20110" href="StlcProp.html#19965" class="Bound"
      >N&#8242;</a
      ><a name="20112" class="Symbol"
      >)</a
      ><a name="20113"
      > </a
      ><a name="20114" class="Symbol"
      >&#8594;</a
      ><a name="20115"
      > </a
      ><a name="20116" class="Symbol"
      >(</a
      ><a name="20117" href="StlcProp.html#19940" class="Bound"
      >&#915;</a
      ><a name="20118"
      > </a
      ><a name="20119" href="Maps.html#10368" class="Function Operator"
      >,</a
      ><a name="20120"
      > </a
      ><a name="20121" href="StlcProp.html#19955" class="Bound"
      >x&#8242;</a
      ><a name="20123"
      > </a
      ><a name="20124" href="Maps.html#10368" class="Function Operator"
      >&#8758;</a
      ><a name="20125"
      > </a
      ><a name="20126" href="StlcProp.html#19948" class="Bound"
      >A</a
      ><a name="20127" class="Symbol"
      >)</a
      ><a name="20128"
      > </a
      ><a name="20129" href="StlcProp.html#20087" class="Bound"
      >y</a
      ><a name="20130"
      > </a
      ><a name="20131" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="20132"
      > </a
      ><a name="20133" href="StlcProp.html#19940" class="Bound"
      >&#915;</a
      ><a name="20134"
      > </a
      ><a name="20135" href="StlcProp.html#20087" class="Bound"
      >y</a
      ><a name="20136"
      >
  </a
      ><a name="20139" href="StlcProp.html#20077" class="Function"
      >&#915;&#8242;~&#915;</a
      ><a name="20143"
      > </a
      ><a name="20144" class="Symbol"
      >{</a
      ><a name="20145" href="StlcProp.html#20145" class="Bound"
      >y</a
      ><a name="20146" class="Symbol"
      >}</a
      ><a name="20147"
      > </a
      ><a name="20148" class="Symbol"
      >(</a
      ><a name="20149" href="StlcProp.html#7768" class="InductiveConstructor"
      >free-&#955;</a
      ><a name="20155"
      > </a
      ><a name="20156" href="StlcProp.html#20156" class="Bound"
      >x&#8242;&#8802;y</a
      ><a name="20160"
      > </a
      ><a name="20161" href="StlcProp.html#20161" class="Bound"
      >y&#8712;N&#8242;</a
      ><a name="20165" class="Symbol"
      >)</a
      ><a name="20166"
      > </a
      ><a name="20167" class="Keyword"
      >with</a
      ><a name="20171"
      > </a
      ><a name="20172" href="StlcProp.html#19955" class="Bound"
      >x&#8242;</a
      ><a name="20174"
      > </a
      ><a name="20175" href="Maps.html#2509" class="Function Operator"
      >&#8799;</a
      ><a name="20176"
      > </a
      ><a name="20177" href="StlcProp.html#20145" class="Bound"
      >y</a
      ><a name="20178"
      >
  </a
      ><a name="20181" class="Symbol"
      >...|</a
      ><a name="20185"
      > </a
      ><a name="20186" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#520" class="InductiveConstructor"
      >yes</a
      ><a name="20189"
      > </a
      ><a name="20190" href="StlcProp.html#20190" class="Bound"
      >x&#8242;&#8801;y</a
      ><a name="20194"
      >  </a
      ><a name="20196" class="Symbol"
      >=</a
      ><a name="20197"
      > </a
      ><a name="20198" href="https://agda.github.io/agda-stdlib/Data.Empty.html#348" class="Function"
      >&#8869;-elim</a
      ><a name="20204"
      > </a
      ><a name="20205" class="Symbol"
      >(</a
      ><a name="20206" href="StlcProp.html#20156" class="Bound"
      >x&#8242;&#8802;y</a
      ><a name="20210"
      > </a
      ><a name="20211" href="StlcProp.html#20190" class="Bound"
      >x&#8242;&#8801;y</a
      ><a name="20215" class="Symbol"
      >)</a
      ><a name="20216"
      >
  </a
      ><a name="20219" class="Symbol"
      >...|</a
      ><a name="20223"
      > </a
      ><a name="20224" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#547" class="InductiveConstructor"
      >no</a
      ><a name="20226"
      >  </a
      ><a name="20228" class="Symbol"
      >_</a
      ><a name="20229"
      >     </a
      ><a name="20234" class="Symbol"
      >=</a
      ><a name="20235"
      > </a
      ><a name="20236" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="20240"
      >
</a
      ><a name="20241" class="Symbol"
      >...|</a
      ><a name="20245"
      > </a
      ><a name="20246" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#547" class="InductiveConstructor"
      >no</a
      ><a name="20248"
      >  </a
      ><a name="20250" href="StlcProp.html#20250" class="Bound"
      >x&#8802;x&#8242;</a
      ><a name="20254"
      > </a
      ><a name="20255" class="Symbol"
      >=</a
      ><a name="20256"
      > </a
      ><a name="20257" href="Stlc.html#21658" class="InductiveConstructor"
      >&#8658;-I</a
      ><a name="20260"
      > </a
      ><a name="20261" href="StlcProp.html#20372" class="Function"
      >&#8866;N&#8242;V</a
      ><a name="20265"
      >
  </a
      ><a name="20268" class="Keyword"
      >where</a
      ><a name="20273"
      >
  </a
      ><a name="20276" href="StlcProp.html#20276" class="Function"
      >x&#8242;x&#8866;N&#8242;</a
      ><a name="20282"
      > </a
      ><a name="20283" class="Symbol"
      >:</a
      ><a name="20284"
      > </a
      ><a name="20285" href="StlcProp.html#19940" class="Bound"
      >&#915;</a
      ><a name="20286"
      > </a
      ><a name="20287" href="Maps.html#10368" class="Function Operator"
      >,</a
      ><a name="20288"
      > </a
      ><a name="20289" href="StlcProp.html#19955" class="Bound"
      >x&#8242;</a
      ><a name="20291"
      > </a
      ><a name="20292" href="Maps.html#10368" class="Function Operator"
      >&#8758;</a
      ><a name="20293"
      > </a
      ><a name="20294" href="StlcProp.html#19960" class="Bound"
      >A&#8242;</a
      ><a name="20296"
      > </a
      ><a name="20297" href="Maps.html#10368" class="Function Operator"
      >,</a
      ><a name="20298"
      > </a
      ><a name="20299" href="StlcProp.html#19944" class="Bound"
      >x</a
      ><a name="20300"
      > </a
      ><a name="20301" href="Maps.html#10368" class="Function Operator"
      >&#8758;</a
      ><a name="20302"
      > </a
      ><a name="20303" href="StlcProp.html#19948" class="Bound"
      >A</a
      ><a name="20304"
      > </a
      ><a name="20305" href="Stlc.html#21560" class="Datatype Operator"
      >&#8866;</a
      ><a name="20306"
      > </a
      ><a name="20307" href="StlcProp.html#19965" class="Bound"
      >N&#8242;</a
      ><a name="20309"
      > </a
      ><a name="20310" href="Stlc.html#21560" class="Datatype Operator"
      >&#8758;</a
      ><a name="20311"
      > </a
      ><a name="20312" href="StlcProp.html#19976" class="Bound"
      >B&#8242;</a
      ><a name="20314"
      >
  </a
      ><a name="20317" href="StlcProp.html#20276" class="Function"
      >x&#8242;x&#8866;N&#8242;</a
      ><a name="20323"
      > </a
      ><a name="20324" class="Keyword"
      >rewrite</a
      ><a name="20331"
      > </a
      ><a name="20332" href="Maps.html#11491" class="Function"
      >update-permute</a
      ><a name="20346"
      > </a
      ><a name="20347" href="StlcProp.html#19940" class="Bound"
      >&#915;</a
      ><a name="20348"
      > </a
      ><a name="20349" href="StlcProp.html#19944" class="Bound"
      >x</a
      ><a name="20350"
      > </a
      ><a name="20351" href="StlcProp.html#19948" class="Bound"
      >A</a
      ><a name="20352"
      > </a
      ><a name="20353" href="StlcProp.html#19955" class="Bound"
      >x&#8242;</a
      ><a name="20355"
      > </a
      ><a name="20356" href="StlcProp.html#19960" class="Bound"
      >A&#8242;</a
      ><a name="20358"
      > </a
      ><a name="20359" href="StlcProp.html#20250" class="Bound"
      >x&#8802;x&#8242;</a
      ><a name="20363"
      > </a
      ><a name="20364" class="Symbol"
      >=</a
      ><a name="20365"
      > </a
      ><a name="20366" href="StlcProp.html#19989" class="Bound"
      >&#8866;N&#8242;</a
      ><a name="20369"
      >
  </a
      ><a name="20372" href="StlcProp.html#20372" class="Function"
      >&#8866;N&#8242;V</a
      ><a name="20376"
      > </a
      ><a name="20377" class="Symbol"
      >:</a
      ><a name="20378"
      > </a
      ><a name="20379" class="Symbol"
      >(</a
      ><a name="20380" href="StlcProp.html#19940" class="Bound"
      >&#915;</a
      ><a name="20381"
      > </a
      ><a name="20382" href="Maps.html#10368" class="Function Operator"
      >,</a
      ><a name="20383"
      > </a
      ><a name="20384" href="StlcProp.html#19955" class="Bound"
      >x&#8242;</a
      ><a name="20386"
      > </a
      ><a name="20387" href="Maps.html#10368" class="Function Operator"
      >&#8758;</a
      ><a name="20388"
      > </a
      ><a name="20389" href="StlcProp.html#19960" class="Bound"
      >A&#8242;</a
      ><a name="20391" class="Symbol"
      >)</a
      ><a name="20392"
      > </a
      ><a name="20393" href="Stlc.html#21560" class="Datatype Operator"
      >&#8866;</a
      ><a name="20394"
      > </a
      ><a name="20395" href="StlcProp.html#19965" class="Bound"
      >N&#8242;</a
      ><a name="20397"
      > </a
      ><a name="20398" href="Stlc.html#12070" class="Function Operator"
      >[</a
      ><a name="20399"
      > </a
      ><a name="20400" href="StlcProp.html#19944" class="Bound"
      >x</a
      ><a name="20401"
      > </a
      ><a name="20402" href="Stlc.html#12070" class="Function Operator"
      >:=</a
      ><a name="20404"
      > </a
      ><a name="20405" href="StlcProp.html#19981" class="Bound"
      >V</a
      ><a name="20406"
      > </a
      ><a name="20407" href="Stlc.html#12070" class="Function Operator"
      >]</a
      ><a name="20408"
      > </a
      ><a name="20409" href="Stlc.html#21560" class="Datatype Operator"
      >&#8758;</a
      ><a name="20410"
      > </a
      ><a name="20411" href="StlcProp.html#19976" class="Bound"
      >B&#8242;</a
      ><a name="20413"
      >
  </a
      ><a name="20416" href="StlcProp.html#20372" class="Function"
      >&#8866;N&#8242;V</a
      ><a name="20420"
      > </a
      ><a name="20421" class="Symbol"
      >=</a
      ><a name="20422"
      > </a
      ><a name="20423" href="StlcProp.html#16175" class="Function"
      >preservation-[:=]</a
      ><a name="20440"
      > </a
      ><a name="20441" href="StlcProp.html#20276" class="Function"
      >x&#8242;x&#8866;N&#8242;</a
      ><a name="20447"
      > </a
      ><a name="20448" href="StlcProp.html#19994" class="Bound"
      >&#8866;V</a
      ><a name="20450"
      >
</a
      ><a name="20451" href="StlcProp.html#16175" class="Function"
      >preservation-[:=]</a
      ><a name="20468"
      > </a
      ><a name="20469" class="Symbol"
      >(</a
      ><a name="20470" href="Stlc.html#21735" class="InductiveConstructor"
      >&#8658;-E</a
      ><a name="20473"
      > </a
      ><a name="20474" href="StlcProp.html#20474" class="Bound"
      >&#8866;L</a
      ><a name="20476"
      > </a
      ><a name="20477" href="StlcProp.html#20477" class="Bound"
      >&#8866;M</a
      ><a name="20479" class="Symbol"
      >)</a
      ><a name="20480"
      > </a
      ><a name="20481" href="StlcProp.html#20481" class="Bound"
      >&#8866;V</a
      ><a name="20483"
      > </a
      ><a name="20484" class="Symbol"
      >=</a
      ><a name="20485"
      > </a
      ><a name="20486" href="Stlc.html#21735" class="InductiveConstructor"
      >&#8658;-E</a
      ><a name="20489"
      > </a
      ><a name="20490" class="Symbol"
      >(</a
      ><a name="20491" href="StlcProp.html#16175" class="Function"
      >preservation-[:=]</a
      ><a name="20508"
      > </a
      ><a name="20509" href="StlcProp.html#20474" class="Bound"
      >&#8866;L</a
      ><a name="20511"
      > </a
      ><a name="20512" href="StlcProp.html#20481" class="Bound"
      >&#8866;V</a
      ><a name="20514" class="Symbol"
      >)</a
      ><a name="20515"
      > </a
      ><a name="20516" class="Symbol"
      >(</a
      ><a name="20517" href="StlcProp.html#16175" class="Function"
      >preservation-[:=]</a
      ><a name="20534"
      > </a
      ><a name="20535" href="StlcProp.html#20477" class="Bound"
      >&#8866;M</a
      ><a name="20537"
      > </a
      ><a name="20538" href="StlcProp.html#20481" class="Bound"
      >&#8866;V</a
      ><a name="20540" class="Symbol"
      >)</a
      ><a name="20541"
      >
</a
      ><a name="20542" href="StlcProp.html#16175" class="Function"
      >preservation-[:=]</a
      ><a name="20559"
      > </a
      ><a name="20560" href="Stlc.html#21813" class="InductiveConstructor"
      >&#120121;-I&#8321;</a
      ><a name="20564"
      > </a
      ><a name="20565" href="StlcProp.html#20565" class="Bound"
      >&#8866;V</a
      ><a name="20567"
      > </a
      ><a name="20568" class="Symbol"
      >=</a
      ><a name="20569"
      > </a
      ><a name="20570" href="Stlc.html#21813" class="InductiveConstructor"
      >&#120121;-I&#8321;</a
      ><a name="20574"
      >
</a
      ><a name="20575" href="StlcProp.html#16175" class="Function"
      >preservation-[:=]</a
      ><a name="20592"
      > </a
      ><a name="20593" href="Stlc.html#21847" class="InductiveConstructor"
      >&#120121;-I&#8322;</a
      ><a name="20597"
      > </a
      ><a name="20598" href="StlcProp.html#20598" class="Bound"
      >&#8866;V</a
      ><a name="20600"
      > </a
      ><a name="20601" class="Symbol"
      >=</a
      ><a name="20602"
      > </a
      ><a name="20603" href="Stlc.html#21847" class="InductiveConstructor"
      >&#120121;-I&#8322;</a
      ><a name="20607"
      >
</a
      ><a name="20608" href="StlcProp.html#16175" class="Function"
      >preservation-[:=]</a
      ><a name="20625"
      > </a
      ><a name="20626" class="Symbol"
      >(</a
      ><a name="20627" href="Stlc.html#21882" class="InductiveConstructor"
      >&#120121;-E</a
      ><a name="20630"
      > </a
      ><a name="20631" href="StlcProp.html#20631" class="Bound"
      >&#8866;L</a
      ><a name="20633"
      > </a
      ><a name="20634" href="StlcProp.html#20634" class="Bound"
      >&#8866;M</a
      ><a name="20636"
      > </a
      ><a name="20637" href="StlcProp.html#20637" class="Bound"
      >&#8866;N</a
      ><a name="20639" class="Symbol"
      >)</a
      ><a name="20640"
      > </a
      ><a name="20641" href="StlcProp.html#20641" class="Bound"
      >&#8866;V</a
      ><a name="20643"
      > </a
      ><a name="20644" class="Symbol"
      >=</a
      ><a name="20645"
      >
  </a
      ><a name="20648" href="Stlc.html#21882" class="InductiveConstructor"
      >&#120121;-E</a
      ><a name="20651"
      > </a
      ><a name="20652" class="Symbol"
      >(</a
      ><a name="20653" href="StlcProp.html#16175" class="Function"
      >preservation-[:=]</a
      ><a name="20670"
      > </a
      ><a name="20671" href="StlcProp.html#20631" class="Bound"
      >&#8866;L</a
      ><a name="20673"
      > </a
      ><a name="20674" href="StlcProp.html#20641" class="Bound"
      >&#8866;V</a
      ><a name="20676" class="Symbol"
      >)</a
      ><a name="20677"
      > </a
      ><a name="20678" class="Symbol"
      >(</a
      ><a name="20679" href="StlcProp.html#16175" class="Function"
      >preservation-[:=]</a
      ><a name="20696"
      > </a
      ><a name="20697" href="StlcProp.html#20634" class="Bound"
      >&#8866;M</a
      ><a name="20699"
      > </a
      ><a name="20700" href="StlcProp.html#20641" class="Bound"
      >&#8866;V</a
      ><a name="20702" class="Symbol"
      >)</a
      ><a name="20703"
      > </a
      ><a name="20704" class="Symbol"
      >(</a
      ><a name="20705" href="StlcProp.html#16175" class="Function"
      >preservation-[:=]</a
      ><a name="20722"
      > </a
      ><a name="20723" href="StlcProp.html#20637" class="Bound"
      >&#8866;N</a
      ><a name="20725"
      > </a
      ><a name="20726" href="StlcProp.html#20641" class="Bound"
      >&#8866;V</a
      ><a name="20728" class="Symbol"
      >)</a
      >

</pre>


### Main Theorem

We now have the tools we need to prove preservation: if a closed
term `M` has type `A` and takes a step to `N`, then `N`
is also a closed term with type `A`.  In other words, small-step
reduction preserves types.

<pre class="Agda">

<a name="20988" href="StlcProp.html#20988" class="Function"
      >preservation</a
      ><a name="21000"
      > </a
      ><a name="21001" class="Symbol"
      >:</a
      ><a name="21002"
      > </a
      ><a name="21003" class="Symbol"
      >&#8704;</a
      ><a name="21004"
      > </a
      ><a name="21005" class="Symbol"
      >{</a
      ><a name="21006" href="StlcProp.html#21006" class="Bound"
      >M</a
      ><a name="21007"
      > </a
      ><a name="21008" href="StlcProp.html#21008" class="Bound"
      >N</a
      ><a name="21009"
      > </a
      ><a name="21010" href="StlcProp.html#21010" class="Bound"
      >A</a
      ><a name="21011" class="Symbol"
      >}</a
      ><a name="21012"
      > </a
      ><a name="21013" class="Symbol"
      >&#8594;</a
      ><a name="21014"
      > </a
      ><a name="21015" href="Maps.html#10265" class="Function"
      >&#8709;</a
      ><a name="21016"
      > </a
      ><a name="21017" href="Stlc.html#21560" class="Datatype Operator"
      >&#8866;</a
      ><a name="21018"
      > </a
      ><a name="21019" href="StlcProp.html#21006" class="Bound"
      >M</a
      ><a name="21020"
      > </a
      ><a name="21021" href="Stlc.html#21560" class="Datatype Operator"
      >&#8758;</a
      ><a name="21022"
      > </a
      ><a name="21023" href="StlcProp.html#21010" class="Bound"
      >A</a
      ><a name="21024"
      > </a
      ><a name="21025" class="Symbol"
      >&#8594;</a
      ><a name="21026"
      > </a
      ><a name="21027" href="StlcProp.html#21006" class="Bound"
      >M</a
      ><a name="21028"
      > </a
      ><a name="21029" href="Stlc.html#15823" class="Datatype Operator"
      >&#10233;</a
      ><a name="21030"
      > </a
      ><a name="21031" href="StlcProp.html#21008" class="Bound"
      >N</a
      ><a name="21032"
      > </a
      ><a name="21033" class="Symbol"
      >&#8594;</a
      ><a name="21034"
      > </a
      ><a name="21035" href="Maps.html#10265" class="Function"
      >&#8709;</a
      ><a name="21036"
      > </a
      ><a name="21037" href="Stlc.html#21560" class="Datatype Operator"
      >&#8866;</a
      ><a name="21038"
      > </a
      ><a name="21039" href="StlcProp.html#21008" class="Bound"
      >N</a
      ><a name="21040"
      > </a
      ><a name="21041" href="Stlc.html#21560" class="Datatype Operator"
      >&#8758;</a
      ><a name="21042"
      > </a
      ><a name="21043" href="StlcProp.html#21010" class="Bound"
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

<a name="22301" href="StlcProp.html#20988" class="Function"
      >preservation</a
      ><a name="22313"
      > </a
      ><a name="22314" class="Symbol"
      >(</a
      ><a name="22315" href="Stlc.html#21604" class="InductiveConstructor"
      >Ax</a
      ><a name="22317"
      > </a
      ><a name="22318" href="StlcProp.html#22318" class="Bound"
      >&#915;x&#8801;A</a
      ><a name="22322" class="Symbol"
      >)</a
      ><a name="22323"
      > </a
      ><a name="22324" class="Symbol"
      >()</a
      ><a name="22326"
      >
</a
      ><a name="22327" href="StlcProp.html#20988" class="Function"
      >preservation</a
      ><a name="22339"
      > </a
      ><a name="22340" class="Symbol"
      >(</a
      ><a name="22341" href="Stlc.html#21658" class="InductiveConstructor"
      >&#8658;-I</a
      ><a name="22344"
      > </a
      ><a name="22345" href="StlcProp.html#22345" class="Bound"
      >&#8866;N</a
      ><a name="22347" class="Symbol"
      >)</a
      ><a name="22348"
      > </a
      ><a name="22349" class="Symbol"
      >()</a
      ><a name="22351"
      >
</a
      ><a name="22352" href="StlcProp.html#20988" class="Function"
      >preservation</a
      ><a name="22364"
      > </a
      ><a name="22365" class="Symbol"
      >(</a
      ><a name="22366" href="Stlc.html#21735" class="InductiveConstructor"
      >&#8658;-E</a
      ><a name="22369"
      > </a
      ><a name="22370" class="Symbol"
      >(</a
      ><a name="22371" href="Stlc.html#21658" class="InductiveConstructor"
      >&#8658;-I</a
      ><a name="22374"
      > </a
      ><a name="22375" href="StlcProp.html#22375" class="Bound"
      >&#8866;N</a
      ><a name="22377" class="Symbol"
      >)</a
      ><a name="22378"
      > </a
      ><a name="22379" href="StlcProp.html#22379" class="Bound"
      >&#8866;V</a
      ><a name="22381" class="Symbol"
      >)</a
      ><a name="22382"
      > </a
      ><a name="22383" class="Symbol"
      >(</a
      ><a name="22384" href="Stlc.html#15975" class="InductiveConstructor"
      >&#946;&#955;&#183;</a
      ><a name="22387"
      > </a
      ><a name="22388" href="StlcProp.html#22388" class="Bound"
      >valueV</a
      ><a name="22394" class="Symbol"
      >)</a
      ><a name="22395"
      > </a
      ><a name="22396" class="Symbol"
      >=</a
      ><a name="22397"
      > </a
      ><a name="22398" href="StlcProp.html#16175" class="Function"
      >preservation-[:=]</a
      ><a name="22415"
      > </a
      ><a name="22416" href="StlcProp.html#22375" class="Bound"
      >&#8866;N</a
      ><a name="22418"
      > </a
      ><a name="22419" href="StlcProp.html#22379" class="Bound"
      >&#8866;V</a
      ><a name="22421"
      >
</a
      ><a name="22422" href="StlcProp.html#20988" class="Function"
      >preservation</a
      ><a name="22434"
      > </a
      ><a name="22435" class="Symbol"
      >(</a
      ><a name="22436" href="Stlc.html#21735" class="InductiveConstructor"
      >&#8658;-E</a
      ><a name="22439"
      > </a
      ><a name="22440" href="StlcProp.html#22440" class="Bound"
      >&#8866;L</a
      ><a name="22442"
      > </a
      ><a name="22443" href="StlcProp.html#22443" class="Bound"
      >&#8866;M</a
      ><a name="22445" class="Symbol"
      >)</a
      ><a name="22446"
      > </a
      ><a name="22447" class="Symbol"
      >(</a
      ><a name="22448" href="Stlc.html#15855" class="InductiveConstructor"
      >&#958;&#183;&#8321;</a
      ><a name="22451"
      > </a
      ><a name="22452" href="StlcProp.html#22452" class="Bound"
      >L&#10233;L&#8242;</a
      ><a name="22456" class="Symbol"
      >)</a
      ><a name="22457"
      > </a
      ><a name="22458" class="Keyword"
      >with</a
      ><a name="22462"
      > </a
      ><a name="22463" href="StlcProp.html#20988" class="Function"
      >preservation</a
      ><a name="22475"
      > </a
      ><a name="22476" href="StlcProp.html#22440" class="Bound"
      >&#8866;L</a
      ><a name="22478"
      > </a
      ><a name="22479" href="StlcProp.html#22452" class="Bound"
      >L&#10233;L&#8242;</a
      ><a name="22483"
      >
</a
      ><a name="22484" class="Symbol"
      >...|</a
      ><a name="22488"
      > </a
      ><a name="22489" href="StlcProp.html#22489" class="Bound"
      >&#8866;L&#8242;</a
      ><a name="22492"
      > </a
      ><a name="22493" class="Symbol"
      >=</a
      ><a name="22494"
      > </a
      ><a name="22495" href="Stlc.html#21735" class="InductiveConstructor"
      >&#8658;-E</a
      ><a name="22498"
      > </a
      ><a name="22499" href="StlcProp.html#22489" class="Bound"
      >&#8866;L&#8242;</a
      ><a name="22502"
      > </a
      ><a name="22503" href="StlcProp.html#22443" class="Bound"
      >&#8866;M</a
      ><a name="22505"
      >
</a
      ><a name="22506" href="StlcProp.html#20988" class="Function"
      >preservation</a
      ><a name="22518"
      > </a
      ><a name="22519" class="Symbol"
      >(</a
      ><a name="22520" href="Stlc.html#21735" class="InductiveConstructor"
      >&#8658;-E</a
      ><a name="22523"
      > </a
      ><a name="22524" href="StlcProp.html#22524" class="Bound"
      >&#8866;L</a
      ><a name="22526"
      > </a
      ><a name="22527" href="StlcProp.html#22527" class="Bound"
      >&#8866;M</a
      ><a name="22529" class="Symbol"
      >)</a
      ><a name="22530"
      > </a
      ><a name="22531" class="Symbol"
      >(</a
      ><a name="22532" href="Stlc.html#15908" class="InductiveConstructor"
      >&#958;&#183;&#8322;</a
      ><a name="22535"
      > </a
      ><a name="22536" href="StlcProp.html#22536" class="Bound"
      >valueL</a
      ><a name="22542"
      > </a
      ><a name="22543" href="StlcProp.html#22543" class="Bound"
      >M&#10233;M&#8242;</a
      ><a name="22547" class="Symbol"
      >)</a
      ><a name="22548"
      > </a
      ><a name="22549" class="Keyword"
      >with</a
      ><a name="22553"
      > </a
      ><a name="22554" href="StlcProp.html#20988" class="Function"
      >preservation</a
      ><a name="22566"
      > </a
      ><a name="22567" href="StlcProp.html#22527" class="Bound"
      >&#8866;M</a
      ><a name="22569"
      > </a
      ><a name="22570" href="StlcProp.html#22543" class="Bound"
      >M&#10233;M&#8242;</a
      ><a name="22574"
      >
</a
      ><a name="22575" class="Symbol"
      >...|</a
      ><a name="22579"
      > </a
      ><a name="22580" href="StlcProp.html#22580" class="Bound"
      >&#8866;M&#8242;</a
      ><a name="22583"
      > </a
      ><a name="22584" class="Symbol"
      >=</a
      ><a name="22585"
      > </a
      ><a name="22586" href="Stlc.html#21735" class="InductiveConstructor"
      >&#8658;-E</a
      ><a name="22589"
      > </a
      ><a name="22590" href="StlcProp.html#22524" class="Bound"
      >&#8866;L</a
      ><a name="22592"
      > </a
      ><a name="22593" href="StlcProp.html#22580" class="Bound"
      >&#8866;M&#8242;</a
      ><a name="22596"
      >
</a
      ><a name="22597" href="StlcProp.html#20988" class="Function"
      >preservation</a
      ><a name="22609"
      > </a
      ><a name="22610" href="Stlc.html#21813" class="InductiveConstructor"
      >&#120121;-I&#8321;</a
      ><a name="22614"
      > </a
      ><a name="22615" class="Symbol"
      >()</a
      ><a name="22617"
      >
</a
      ><a name="22618" href="StlcProp.html#20988" class="Function"
      >preservation</a
      ><a name="22630"
      > </a
      ><a name="22631" href="Stlc.html#21847" class="InductiveConstructor"
      >&#120121;-I&#8322;</a
      ><a name="22635"
      > </a
      ><a name="22636" class="Symbol"
      >()</a
      ><a name="22638"
      >
</a
      ><a name="22639" href="StlcProp.html#20988" class="Function"
      >preservation</a
      ><a name="22651"
      > </a
      ><a name="22652" class="Symbol"
      >(</a
      ><a name="22653" href="Stlc.html#21882" class="InductiveConstructor"
      >&#120121;-E</a
      ><a name="22656"
      > </a
      ><a name="22657" href="Stlc.html#21813" class="InductiveConstructor"
      >&#120121;-I&#8321;</a
      ><a name="22661"
      > </a
      ><a name="22662" href="StlcProp.html#22662" class="Bound"
      >&#8866;M</a
      ><a name="22664"
      > </a
      ><a name="22665" href="StlcProp.html#22665" class="Bound"
      >&#8866;N</a
      ><a name="22667" class="Symbol"
      >)</a
      ><a name="22668"
      > </a
      ><a name="22669" href="Stlc.html#16130" class="InductiveConstructor"
      >&#946;if-true</a
      ><a name="22677"
      > </a
      ><a name="22678" class="Symbol"
      >=</a
      ><a name="22679"
      > </a
      ><a name="22680" href="StlcProp.html#22662" class="Bound"
      >&#8866;M</a
      ><a name="22682"
      >
</a
      ><a name="22683" href="StlcProp.html#20988" class="Function"
      >preservation</a
      ><a name="22695"
      > </a
      ><a name="22696" class="Symbol"
      >(</a
      ><a name="22697" href="Stlc.html#21882" class="InductiveConstructor"
      >&#120121;-E</a
      ><a name="22700"
      > </a
      ><a name="22701" href="Stlc.html#21847" class="InductiveConstructor"
      >&#120121;-I&#8322;</a
      ><a name="22705"
      > </a
      ><a name="22706" href="StlcProp.html#22706" class="Bound"
      >&#8866;M</a
      ><a name="22708"
      > </a
      ><a name="22709" href="StlcProp.html#22709" class="Bound"
      >&#8866;N</a
      ><a name="22711" class="Symbol"
      >)</a
      ><a name="22712"
      > </a
      ><a name="22713" href="Stlc.html#16183" class="InductiveConstructor"
      >&#946;if-false</a
      ><a name="22722"
      > </a
      ><a name="22723" class="Symbol"
      >=</a
      ><a name="22724"
      > </a
      ><a name="22725" href="StlcProp.html#22709" class="Bound"
      >&#8866;N</a
      ><a name="22727"
      >
</a
      ><a name="22728" href="StlcProp.html#20988" class="Function"
      >preservation</a
      ><a name="22740"
      > </a
      ><a name="22741" class="Symbol"
      >(</a
      ><a name="22742" href="Stlc.html#21882" class="InductiveConstructor"
      >&#120121;-E</a
      ><a name="22745"
      > </a
      ><a name="22746" href="StlcProp.html#22746" class="Bound"
      >&#8866;L</a
      ><a name="22748"
      > </a
      ><a name="22749" href="StlcProp.html#22749" class="Bound"
      >&#8866;M</a
      ><a name="22751"
      > </a
      ><a name="22752" href="StlcProp.html#22752" class="Bound"
      >&#8866;N</a
      ><a name="22754" class="Symbol"
      >)</a
      ><a name="22755"
      > </a
      ><a name="22756" class="Symbol"
      >(</a
      ><a name="22757" href="Stlc.html#16045" class="InductiveConstructor"
      >&#958;if</a
      ><a name="22760"
      > </a
      ><a name="22761" href="StlcProp.html#22761" class="Bound"
      >L&#10233;L&#8242;</a
      ><a name="22765" class="Symbol"
      >)</a
      ><a name="22766"
      > </a
      ><a name="22767" class="Keyword"
      >with</a
      ><a name="22771"
      > </a
      ><a name="22772" href="StlcProp.html#20988" class="Function"
      >preservation</a
      ><a name="22784"
      > </a
      ><a name="22785" href="StlcProp.html#22746" class="Bound"
      >&#8866;L</a
      ><a name="22787"
      > </a
      ><a name="22788" href="StlcProp.html#22761" class="Bound"
      >L&#10233;L&#8242;</a
      ><a name="22792"
      >
</a
      ><a name="22793" class="Symbol"
      >...|</a
      ><a name="22797"
      > </a
      ><a name="22798" href="StlcProp.html#22798" class="Bound"
      >&#8866;L&#8242;</a
      ><a name="22801"
      > </a
      ><a name="22802" class="Symbol"
      >=</a
      ><a name="22803"
      > </a
      ><a name="22804" href="Stlc.html#21882" class="InductiveConstructor"
      >&#120121;-E</a
      ><a name="22807"
      > </a
      ><a name="22808" href="StlcProp.html#22798" class="Bound"
      >&#8866;L&#8242;</a
      ><a name="22811"
      > </a
      ><a name="22812" href="StlcProp.html#22749" class="Bound"
      >&#8866;M</a
      ><a name="22814"
      > </a
      ><a name="22815" href="StlcProp.html#22752" class="Bound"
      >&#8866;N</a
      >

</pre>


#### Exercise: 2 stars, recommended (subject_expansion_stlc)

An exercise in the [Types]({{ "Types" | relative_url }}) chapter asked about the
subject expansion property for the simple language of arithmetic and boolean
expressions.  Does this property hold for STLC?  That is, is it always the case
that, if `M ==> N` and `∅ ⊢ N ∶ A`, then `∅ ⊢ M ∶ A`?  It is easy to find a
counter-example with conditionals, find one not involving conditionals.

## Type Soundness

#### Exercise: 2 stars, optional (type_soundness)

Put progress and preservation together and show that a well-typed
term can _never_ reach a stuck state.

<pre class="Agda">

<a name="23468" href="StlcProp.html#23468" class="Function"
      >Normal</a
      ><a name="23474"
      > </a
      ><a name="23475" class="Symbol"
      >:</a
      ><a name="23476"
      > </a
      ><a name="23477" href="Stlc.html#3628" class="Datatype"
      >Term</a
      ><a name="23481"
      > </a
      ><a name="23482" class="Symbol"
      >&#8594;</a
      ><a name="23483"
      > </a
      ><a name="23484" class="PrimitiveType"
      >Set</a
      ><a name="23487"
      >
</a
      ><a name="23488" href="StlcProp.html#23468" class="Function"
      >Normal</a
      ><a name="23494"
      > </a
      ><a name="23495" href="StlcProp.html#23495" class="Bound"
      >M</a
      ><a name="23496"
      > </a
      ><a name="23497" class="Symbol"
      >=</a
      ><a name="23498"
      > </a
      ><a name="23499" class="Symbol"
      >&#8704;</a
      ><a name="23500"
      > </a
      ><a name="23501" class="Symbol"
      >{</a
      ><a name="23502" href="StlcProp.html#23502" class="Bound"
      >N</a
      ><a name="23503" class="Symbol"
      >}</a
      ><a name="23504"
      > </a
      ><a name="23505" class="Symbol"
      >&#8594;</a
      ><a name="23506"
      > </a
      ><a name="23507" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#414" class="Function Operator"
      >&#172;</a
      ><a name="23508"
      > </a
      ><a name="23509" class="Symbol"
      >(</a
      ><a name="23510" href="StlcProp.html#23495" class="Bound"
      >M</a
      ><a name="23511"
      > </a
      ><a name="23512" href="Stlc.html#15823" class="Datatype Operator"
      >&#10233;</a
      ><a name="23513"
      > </a
      ><a name="23514" href="StlcProp.html#23502" class="Bound"
      >N</a
      ><a name="23515" class="Symbol"
      >)</a
      ><a name="23516"
      >

</a
      ><a name="23518" href="StlcProp.html#23518" class="Function"
      >Stuck</a
      ><a name="23523"
      > </a
      ><a name="23524" class="Symbol"
      >:</a
      ><a name="23525"
      > </a
      ><a name="23526" href="Stlc.html#3628" class="Datatype"
      >Term</a
      ><a name="23530"
      > </a
      ><a name="23531" class="Symbol"
      >&#8594;</a
      ><a name="23532"
      > </a
      ><a name="23533" class="PrimitiveType"
      >Set</a
      ><a name="23536"
      >
</a
      ><a name="23537" href="StlcProp.html#23518" class="Function"
      >Stuck</a
      ><a name="23542"
      > </a
      ><a name="23543" href="StlcProp.html#23543" class="Bound"
      >M</a
      ><a name="23544"
      > </a
      ><a name="23545" class="Symbol"
      >=</a
      ><a name="23546"
      > </a
      ><a name="23547" href="StlcProp.html#23468" class="Function"
      >Normal</a
      ><a name="23553"
      > </a
      ><a name="23554" href="StlcProp.html#23543" class="Bound"
      >M</a
      ><a name="23555"
      > </a
      ><a name="23556" href="https://agda.github.io/agda-stdlib/Data.Product.html#1073" class="Function Operator"
      >&#215;</a
      ><a name="23557"
      > </a
      ><a name="23558" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#414" class="Function Operator"
      >&#172;</a
      ><a name="23559"
      > </a
      ><a name="23560" href="Stlc.html#9526" class="Datatype"
      >Value</a
      ><a name="23565"
      > </a
      ><a name="23566" href="StlcProp.html#23543" class="Bound"
      >M</a
      ><a name="23567"
      >

</a
      ><a name="23569" class="Keyword"
      >postulate</a
      ><a name="23578"
      >
  </a
      ><a name="23581" href="StlcProp.html#23581" class="Postulate"
      >Soundness</a
      ><a name="23590"
      > </a
      ><a name="23591" class="Symbol"
      >:</a
      ><a name="23592"
      > </a
      ><a name="23593" class="Symbol"
      >&#8704;</a
      ><a name="23594"
      > </a
      ><a name="23595" class="Symbol"
      >{</a
      ><a name="23596" href="StlcProp.html#23596" class="Bound"
      >M</a
      ><a name="23597"
      > </a
      ><a name="23598" href="StlcProp.html#23598" class="Bound"
      >N</a
      ><a name="23599"
      > </a
      ><a name="23600" href="StlcProp.html#23600" class="Bound"
      >A</a
      ><a name="23601" class="Symbol"
      >}</a
      ><a name="23602"
      > </a
      ><a name="23603" class="Symbol"
      >&#8594;</a
      ><a name="23604"
      > </a
      ><a name="23605" href="Maps.html#10265" class="Function"
      >&#8709;</a
      ><a name="23606"
      > </a
      ><a name="23607" href="Stlc.html#21560" class="Datatype Operator"
      >&#8866;</a
      ><a name="23608"
      > </a
      ><a name="23609" href="StlcProp.html#23596" class="Bound"
      >M</a
      ><a name="23610"
      > </a
      ><a name="23611" href="Stlc.html#21560" class="Datatype Operator"
      >&#8758;</a
      ><a name="23612"
      > </a
      ><a name="23613" href="StlcProp.html#23600" class="Bound"
      >A</a
      ><a name="23614"
      > </a
      ><a name="23615" class="Symbol"
      >&#8594;</a
      ><a name="23616"
      > </a
      ><a name="23617" href="StlcProp.html#23596" class="Bound"
      >M</a
      ><a name="23618"
      > </a
      ><a name="23619" href="Stlc.html#17857" class="Datatype Operator"
      >&#10233;*</a
      ><a name="23621"
      > </a
      ><a name="23622" href="StlcProp.html#23598" class="Bound"
      >N</a
      ><a name="23623"
      > </a
      ><a name="23624" class="Symbol"
      >&#8594;</a
      ><a name="23625"
      > </a
      ><a name="23626" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#414" class="Function Operator"
      >&#172;</a
      ><a name="23627"
      > </a
      ><a name="23628" class="Symbol"
      >(</a
      ><a name="23629" href="StlcProp.html#23518" class="Function"
      >Stuck</a
      ><a name="23634"
      > </a
      ><a name="23635" href="StlcProp.html#23598" class="Bound"
      >N</a
      ><a name="23636" class="Symbol"
      >)</a
      >

</pre>

<div class="hidden">
<pre class="Agda">

<a name="23684" href="StlcProp.html#23684" class="Function"
      >Soundness&#8242;</a
      ><a name="23694"
      > </a
      ><a name="23695" class="Symbol"
      >:</a
      ><a name="23696"
      > </a
      ><a name="23697" class="Symbol"
      >&#8704;</a
      ><a name="23698"
      > </a
      ><a name="23699" class="Symbol"
      >{</a
      ><a name="23700" href="StlcProp.html#23700" class="Bound"
      >M</a
      ><a name="23701"
      > </a
      ><a name="23702" href="StlcProp.html#23702" class="Bound"
      >N</a
      ><a name="23703"
      > </a
      ><a name="23704" href="StlcProp.html#23704" class="Bound"
      >A</a
      ><a name="23705" class="Symbol"
      >}</a
      ><a name="23706"
      > </a
      ><a name="23707" class="Symbol"
      >&#8594;</a
      ><a name="23708"
      > </a
      ><a name="23709" href="Maps.html#10265" class="Function"
      >&#8709;</a
      ><a name="23710"
      > </a
      ><a name="23711" href="Stlc.html#21560" class="Datatype Operator"
      >&#8866;</a
      ><a name="23712"
      > </a
      ><a name="23713" href="StlcProp.html#23700" class="Bound"
      >M</a
      ><a name="23714"
      > </a
      ><a name="23715" href="Stlc.html#21560" class="Datatype Operator"
      >&#8758;</a
      ><a name="23716"
      > </a
      ><a name="23717" href="StlcProp.html#23704" class="Bound"
      >A</a
      ><a name="23718"
      > </a
      ><a name="23719" class="Symbol"
      >&#8594;</a
      ><a name="23720"
      > </a
      ><a name="23721" href="StlcProp.html#23700" class="Bound"
      >M</a
      ><a name="23722"
      > </a
      ><a name="23723" href="Stlc.html#17857" class="Datatype Operator"
      >&#10233;*</a
      ><a name="23725"
      > </a
      ><a name="23726" href="StlcProp.html#23702" class="Bound"
      >N</a
      ><a name="23727"
      > </a
      ><a name="23728" class="Symbol"
      >&#8594;</a
      ><a name="23729"
      > </a
      ><a name="23730" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#414" class="Function Operator"
      >&#172;</a
      ><a name="23731"
      > </a
      ><a name="23732" class="Symbol"
      >(</a
      ><a name="23733" href="StlcProp.html#23518" class="Function"
      >Stuck</a
      ><a name="23738"
      > </a
      ><a name="23739" href="StlcProp.html#23702" class="Bound"
      >N</a
      ><a name="23740" class="Symbol"
      >)</a
      ><a name="23741"
      >
</a
      ><a name="23742" href="StlcProp.html#23684" class="Function"
      >Soundness&#8242;</a
      ><a name="23752"
      > </a
      ><a name="23753" href="StlcProp.html#23753" class="Bound"
      >&#8866;M</a
      ><a name="23755"
      > </a
      ><a name="23756" class="Symbol"
      >(</a
      ><a name="23757" href="StlcProp.html#23757" class="Bound"
      >M</a
      ><a name="23758"
      > </a
      ><a name="23759" href="Stlc.html#17890" class="InductiveConstructor Operator"
      >&#8718;</a
      ><a name="23760" class="Symbol"
      >)</a
      ><a name="23761"
      > </a
      ><a name="23762" class="Symbol"
      >(</a
      ><a name="23763" href="StlcProp.html#23763" class="Bound"
      >&#172;M&#10233;N</a
      ><a name="23767"
      > </a
      ><a name="23768" href="https://agda.github.io/agda-stdlib/Data.Product.html#509" class="InductiveConstructor Operator"
      >,</a
      ><a name="23769"
      > </a
      ><a name="23770" href="StlcProp.html#23770" class="Bound"
      >&#172;ValueM</a
      ><a name="23777" class="Symbol"
      >)</a
      ><a name="23778"
      > </a
      ><a name="23779" class="Keyword"
      >with</a
      ><a name="23783"
      > </a
      ><a name="23784" href="StlcProp.html#2075" class="Function"
      >progress</a
      ><a name="23792"
      > </a
      ><a name="23793" href="StlcProp.html#23753" class="Bound"
      >&#8866;M</a
      ><a name="23795"
      >
</a
      ><a name="23796" class="Symbol"
      >...</a
      ><a name="23799"
      > </a
      ><a name="23800" class="Symbol"
      >|</a
      ><a name="23801"
      > </a
      ><a name="23802" href="StlcProp.html#1998" class="InductiveConstructor"
      >steps</a
      ><a name="23807"
      > </a
      ><a name="23808" href="StlcProp.html#23808" class="Bound"
      >M&#10233;N</a
      ><a name="23811"
      >  </a
      ><a name="23813" class="Symbol"
      >=</a
      ><a name="23814"
      > </a
      ><a name="23815" href="StlcProp.html#23763" class="Bound"
      >&#172;M&#10233;N</a
      ><a name="23819"
      > </a
      ><a name="23820" href="StlcProp.html#23808" class="Bound"
      >M&#10233;N</a
      ><a name="23823"
      >
</a
      ><a name="23824" class="Symbol"
      >...</a
      ><a name="23827"
      > </a
      ><a name="23828" class="Symbol"
      >|</a
      ><a name="23829"
      > </a
      ><a name="23830" href="StlcProp.html#2037" class="InductiveConstructor"
      >done</a
      ><a name="23834"
      > </a
      ><a name="23835" href="StlcProp.html#23835" class="Bound"
      >ValueM</a
      ><a name="23841"
      >  </a
      ><a name="23843" class="Symbol"
      >=</a
      ><a name="23844"
      > </a
      ><a name="23845" href="StlcProp.html#23770" class="Bound"
      >&#172;ValueM</a
      ><a name="23852"
      > </a
      ><a name="23853" href="StlcProp.html#23835" class="Bound"
      >ValueM</a
      ><a name="23859"
      >
</a
      ><a name="23860" href="StlcProp.html#23684" class="Function"
      >Soundness&#8242;</a
      ><a name="23870"
      > </a
      ><a name="23871" class="Symbol"
      >{</a
      ><a name="23872" href="StlcProp.html#23872" class="Bound"
      >L</a
      ><a name="23873" class="Symbol"
      >}</a
      ><a name="23874"
      > </a
      ><a name="23875" class="Symbol"
      >{</a
      ><a name="23876" href="StlcProp.html#23876" class="Bound"
      >N</a
      ><a name="23877" class="Symbol"
      >}</a
      ><a name="23878"
      > </a
      ><a name="23879" class="Symbol"
      >{</a
      ><a name="23880" href="StlcProp.html#23880" class="Bound"
      >A</a
      ><a name="23881" class="Symbol"
      >}</a
      ><a name="23882"
      > </a
      ><a name="23883" href="StlcProp.html#23883" class="Bound"
      >&#8866;L</a
      ><a name="23885"
      > </a
      ><a name="23886" class="Symbol"
      >(</a
      ><a name="23887" href="Stlc.html#17910" class="InductiveConstructor Operator"
      >_&#10233;&#10216;_&#10217;_</a
      ><a name="23893"
      > </a
      ><a name="23894" class="DottedPattern Symbol"
      >.</a
      ><a name="23895" href="StlcProp.html#23872" class="DottedPattern Bound"
      >L</a
      ><a name="23896"
      > </a
      ><a name="23897" class="Symbol"
      >{</a
      ><a name="23898" href="StlcProp.html#23898" class="Bound"
      >M</a
      ><a name="23899" class="Symbol"
      >}</a
      ><a name="23900"
      > </a
      ><a name="23901" class="Symbol"
      >{</a
      ><a name="23902" class="DottedPattern Symbol"
      >.</a
      ><a name="23903" href="StlcProp.html#23876" class="DottedPattern Bound"
      >N</a
      ><a name="23904" class="Symbol"
      >}</a
      ><a name="23905"
      > </a
      ><a name="23906" href="StlcProp.html#23906" class="Bound"
      >L&#10233;M</a
      ><a name="23909"
      > </a
      ><a name="23910" href="StlcProp.html#23910" class="Bound"
      >M&#10233;*N</a
      ><a name="23914" class="Symbol"
      >)</a
      ><a name="23915"
      > </a
      ><a name="23916" class="Symbol"
      >=</a
      ><a name="23917"
      > </a
      ><a name="23918" href="StlcProp.html#23684" class="Function"
      >Soundness&#8242;</a
      ><a name="23928"
      > </a
      ><a name="23929" href="StlcProp.html#23947" class="Function"
      >&#8866;M</a
      ><a name="23931"
      > </a
      ><a name="23932" href="StlcProp.html#23910" class="Bound"
      >M&#10233;*N</a
      ><a name="23936"
      >
  </a
      ><a name="23939" class="Keyword"
      >where</a
      ><a name="23944"
      >
  </a
      ><a name="23947" href="StlcProp.html#23947" class="Function"
      >&#8866;M</a
      ><a name="23949"
      > </a
      ><a name="23950" class="Symbol"
      >:</a
      ><a name="23951"
      > </a
      ><a name="23952" href="Maps.html#10265" class="Function"
      >&#8709;</a
      ><a name="23953"
      > </a
      ><a name="23954" href="Stlc.html#21560" class="Datatype Operator"
      >&#8866;</a
      ><a name="23955"
      > </a
      ><a name="23956" href="StlcProp.html#23898" class="Bound"
      >M</a
      ><a name="23957"
      > </a
      ><a name="23958" href="Stlc.html#21560" class="Datatype Operator"
      >&#8758;</a
      ><a name="23959"
      > </a
      ><a name="23960" href="StlcProp.html#23880" class="Bound"
      >A</a
      ><a name="23961"
      >
  </a
      ><a name="23964" href="StlcProp.html#23947" class="Function"
      >&#8866;M</a
      ><a name="23966"
      > </a
      ><a name="23967" class="Symbol"
      >=</a
      ><a name="23968"
      > </a
      ><a name="23969" href="StlcProp.html#20988" class="Function"
      >preservation</a
      ><a name="23981"
      > </a
      ><a name="23982" href="StlcProp.html#23883" class="Bound"
      >&#8866;L</a
      ><a name="23984"
      > </a
      ><a name="23985" href="StlcProp.html#23906" class="Bound"
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

<a name="28401" class="Keyword"
      >data</a
      ><a name="28405"
      > </a
      ><a name="28406" href="StlcProp.html#28406" class="Datatype"
      >Type&#8242;</a
      ><a name="28411"
      > </a
      ><a name="28412" class="Symbol"
      >:</a
      ><a name="28413"
      > </a
      ><a name="28414" class="PrimitiveType"
      >Set</a
      ><a name="28417"
      > </a
      ><a name="28418" class="Keyword"
      >where</a
      ><a name="28423"
      >
  </a
      ><a name="28426" href="StlcProp.html#28426" class="InductiveConstructor Operator"
      >_&#8658;_</a
      ><a name="28429"
      > </a
      ><a name="28430" class="Symbol"
      >:</a
      ><a name="28431"
      > </a
      ><a name="28432" href="StlcProp.html#28406" class="Datatype"
      >Type&#8242;</a
      ><a name="28437"
      > </a
      ><a name="28438" class="Symbol"
      >&#8594;</a
      ><a name="28439"
      > </a
      ><a name="28440" href="StlcProp.html#28406" class="Datatype"
      >Type&#8242;</a
      ><a name="28445"
      > </a
      ><a name="28446" class="Symbol"
      >&#8594;</a
      ><a name="28447"
      > </a
      ><a name="28448" href="StlcProp.html#28406" class="Datatype"
      >Type&#8242;</a
      ><a name="28453"
      >
  </a
      ><a name="28456" href="StlcProp.html#28456" class="InductiveConstructor"
      >&#8469;</a
      ><a name="28457"
      > </a
      ><a name="28458" class="Symbol"
      >:</a
      ><a name="28459"
      > </a
      ><a name="28460" href="StlcProp.html#28406" class="Datatype"
      >Type&#8242;</a
      >

</pre>

To terms, we add natural number constants, along with
plus, minus, and testing for zero.

<pre class="Agda">

<a name="28581" class="Keyword"
      >data</a
      ><a name="28585"
      > </a
      ><a name="28586" href="StlcProp.html#28586" class="Datatype"
      >Term&#8242;</a
      ><a name="28591"
      > </a
      ><a name="28592" class="Symbol"
      >:</a
      ><a name="28593"
      > </a
      ><a name="28594" class="PrimitiveType"
      >Set</a
      ><a name="28597"
      > </a
      ><a name="28598" class="Keyword"
      >where</a
      ><a name="28603"
      >
  </a
      ><a name="28606" href="StlcProp.html#28606" class="InductiveConstructor Operator"
      >`_</a
      ><a name="28608"
      > </a
      ><a name="28609" class="Symbol"
      >:</a
      ><a name="28610"
      > </a
      ><a name="28611" href="Maps.html#2171" class="Datatype"
      >Id</a
      ><a name="28613"
      > </a
      ><a name="28614" class="Symbol"
      >&#8594;</a
      ><a name="28615"
      > </a
      ><a name="28616" href="StlcProp.html#28586" class="Datatype"
      >Term&#8242;</a
      ><a name="28621"
      >
  </a
      ><a name="28624" href="StlcProp.html#28624" class="InductiveConstructor Operator"
      >&#955;[_&#8758;_]_</a
      ><a name="28631"
      > </a
      ><a name="28632" class="Symbol"
      >:</a
      ><a name="28633"
      > </a
      ><a name="28634" href="Maps.html#2171" class="Datatype"
      >Id</a
      ><a name="28636"
      > </a
      ><a name="28637" class="Symbol"
      >&#8594;</a
      ><a name="28638"
      > </a
      ><a name="28639" href="StlcProp.html#28406" class="Datatype"
      >Type&#8242;</a
      ><a name="28644"
      > </a
      ><a name="28645" class="Symbol"
      >&#8594;</a
      ><a name="28646"
      > </a
      ><a name="28647" href="StlcProp.html#28586" class="Datatype"
      >Term&#8242;</a
      ><a name="28652"
      > </a
      ><a name="28653" class="Symbol"
      >&#8594;</a
      ><a name="28654"
      > </a
      ><a name="28655" href="StlcProp.html#28586" class="Datatype"
      >Term&#8242;</a
      ><a name="28660"
      >
  </a
      ><a name="28663" href="StlcProp.html#28663" class="InductiveConstructor Operator"
      >_&#183;_</a
      ><a name="28666"
      > </a
      ><a name="28667" class="Symbol"
      >:</a
      ><a name="28668"
      > </a
      ><a name="28669" href="StlcProp.html#28586" class="Datatype"
      >Term&#8242;</a
      ><a name="28674"
      > </a
      ><a name="28675" class="Symbol"
      >&#8594;</a
      ><a name="28676"
      > </a
      ><a name="28677" href="StlcProp.html#28586" class="Datatype"
      >Term&#8242;</a
      ><a name="28682"
      > </a
      ><a name="28683" class="Symbol"
      >&#8594;</a
      ><a name="28684"
      > </a
      ><a name="28685" href="StlcProp.html#28586" class="Datatype"
      >Term&#8242;</a
      ><a name="28690"
      >
  </a
      ><a name="28693" href="StlcProp.html#28693" class="InductiveConstructor Operator"
      >#_</a
      ><a name="28695"
      > </a
      ><a name="28696" class="Symbol"
      >:</a
      ><a name="28697"
      > </a
      ><a name="28698" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#97" class="Datatype"
      >Data.Nat.&#8469;</a
      ><a name="28708"
      > </a
      ><a name="28709" class="Symbol"
      >&#8594;</a
      ><a name="28710"
      > </a
      ><a name="28711" href="StlcProp.html#28586" class="Datatype"
      >Term&#8242;</a
      ><a name="28716"
      >
  </a
      ><a name="28719" href="StlcProp.html#28719" class="InductiveConstructor Operator"
      >_+_</a
      ><a name="28722"
      > </a
      ><a name="28723" class="Symbol"
      >:</a
      ><a name="28724"
      > </a
      ><a name="28725" href="StlcProp.html#28586" class="Datatype"
      >Term&#8242;</a
      ><a name="28730"
      > </a
      ><a name="28731" class="Symbol"
      >&#8594;</a
      ><a name="28732"
      > </a
      ><a name="28733" href="StlcProp.html#28586" class="Datatype"
      >Term&#8242;</a
      ><a name="28738"
      > </a
      ><a name="28739" class="Symbol"
      >&#8594;</a
      ><a name="28740"
      > </a
      ><a name="28741" href="StlcProp.html#28586" class="Datatype"
      >Term&#8242;</a
      ><a name="28746"
      >
  </a
      ><a name="28749" href="StlcProp.html#28749" class="InductiveConstructor Operator"
      >_-_</a
      ><a name="28752"
      > </a
      ><a name="28753" class="Symbol"
      >:</a
      ><a name="28754"
      > </a
      ><a name="28755" href="StlcProp.html#28586" class="Datatype"
      >Term&#8242;</a
      ><a name="28760"
      > </a
      ><a name="28761" class="Symbol"
      >&#8594;</a
      ><a name="28762"
      > </a
      ><a name="28763" href="StlcProp.html#28586" class="Datatype"
      >Term&#8242;</a
      ><a name="28768"
      > </a
      ><a name="28769" class="Symbol"
      >&#8594;</a
      ><a name="28770"
      > </a
      ><a name="28771" href="StlcProp.html#28586" class="Datatype"
      >Term&#8242;</a
      ><a name="28776"
      >
  </a
      ><a name="28779" href="StlcProp.html#28779" class="InductiveConstructor Operator"
      >if0_then_else_</a
      ><a name="28793"
      > </a
      ><a name="28794" class="Symbol"
      >:</a
      ><a name="28795"
      > </a
      ><a name="28796" href="StlcProp.html#28586" class="Datatype"
      >Term&#8242;</a
      ><a name="28801"
      > </a
      ><a name="28802" class="Symbol"
      >&#8594;</a
      ><a name="28803"
      > </a
      ><a name="28804" href="StlcProp.html#28586" class="Datatype"
      >Term&#8242;</a
      ><a name="28809"
      > </a
      ><a name="28810" class="Symbol"
      >&#8594;</a
      ><a name="28811"
      > </a
      ><a name="28812" href="StlcProp.html#28586" class="Datatype"
      >Term&#8242;</a
      ><a name="28817"
      > </a
      ><a name="28818" class="Symbol"
      >&#8594;</a
      ><a name="28819"
      > </a
      ><a name="28820" href="StlcProp.html#28586" class="Datatype"
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

