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
      >)</a
      ><a name="710"
      > </a
      ><a name="711" class="Keyword"
      >renaming</a
      ><a name="719"
      > </a
      ><a name="720" class="Symbol"
      >(</a
      ><a name="721" href="Maps.html#10368" class="Function Operator"
      >_,_&#8614;_</a
      ><a name="726"
      > </a
      ><a name="727" class="Symbol"
      >to</a
      ><a name="729"
      > </a
      ><a name="730" href="Maps.html#10368" class="Function Operator"
      >_,_&#8758;_</a
      ><a name="735" class="Symbol"
      >)</a
      ><a name="736"
      >
</a
      ><a name="737" class="Keyword"
      >open</a
      ><a name="741"
      > </a
      ><a name="742" class="Keyword"
      >import</a
      ><a name="748"
      > </a
      ><a name="749" class="Module"
      >Stlc</a
      ><a name="753"
      >
</a
      ><a name="754" class="Keyword"
      >import</a
      ><a name="760"
      > </a
      ><a name="761" href="https://agda.github.io/agda-stdlib/Data.Nat.html#1" class="Module"
      >Data.Nat</a
      ><a name="769"
      > </a
      ><a name="770" class="Keyword"
      >using</a
      ><a name="775"
      > </a
      ><a name="776" class="Symbol"
      >(</a
      ><a name="777" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#97" class="Datatype"
      >&#8469;</a
      ><a name="778" class="Symbol"
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

<a name="1213" class="Keyword"
      >data</a
      ><a name="1217"
      > </a
      ><a name="1218" href="StlcProp.html#1218" class="Datatype Operator"
      >canonical_for_</a
      ><a name="1232"
      > </a
      ><a name="1233" class="Symbol"
      >:</a
      ><a name="1234"
      > </a
      ><a name="1235" href="Stlc.html#708" class="Datatype"
      >Term</a
      ><a name="1239"
      > </a
      ><a name="1240" class="Symbol"
      >&#8594;</a
      ><a name="1241"
      > </a
      ><a name="1242" href="Stlc.html#590" class="Datatype"
      >Type</a
      ><a name="1246"
      > </a
      ><a name="1247" class="Symbol"
      >&#8594;</a
      ><a name="1248"
      > </a
      ><a name="1249" class="PrimitiveType"
      >Set</a
      ><a name="1252"
      > </a
      ><a name="1253" class="Keyword"
      >where</a
      ><a name="1258"
      >
  </a
      ><a name="1261" href="StlcProp.html#1261" class="InductiveConstructor"
      >canonical-&#955;</a
      ><a name="1272"
      > </a
      ><a name="1273" class="Symbol"
      >:</a
      ><a name="1274"
      > </a
      ><a name="1275" class="Symbol"
      >&#8704;</a
      ><a name="1276"
      > </a
      ><a name="1277" class="Symbol"
      >{</a
      ><a name="1278" href="StlcProp.html#1278" class="Bound"
      >x</a
      ><a name="1279"
      > </a
      ><a name="1280" href="StlcProp.html#1280" class="Bound"
      >A</a
      ><a name="1281"
      > </a
      ><a name="1282" href="StlcProp.html#1282" class="Bound"
      >N</a
      ><a name="1283"
      > </a
      ><a name="1284" href="StlcProp.html#1284" class="Bound"
      >B</a
      ><a name="1285" class="Symbol"
      >}</a
      ><a name="1286"
      > </a
      ><a name="1287" class="Symbol"
      >&#8594;</a
      ><a name="1288"
      > </a
      ><a name="1289" href="StlcProp.html#1218" class="Datatype Operator"
      >canonical</a
      ><a name="1298"
      > </a
      ><a name="1299" class="Symbol"
      >(</a
      ><a name="1300" href="Stlc.html#743" class="InductiveConstructor Operator"
      >&#955;[</a
      ><a name="1302"
      > </a
      ><a name="1303" href="StlcProp.html#1278" class="Bound"
      >x</a
      ><a name="1304"
      > </a
      ><a name="1305" href="Stlc.html#743" class="InductiveConstructor Operator"
      >&#8758;</a
      ><a name="1306"
      > </a
      ><a name="1307" href="StlcProp.html#1280" class="Bound"
      >A</a
      ><a name="1308"
      > </a
      ><a name="1309" href="Stlc.html#743" class="InductiveConstructor Operator"
      >]</a
      ><a name="1310"
      > </a
      ><a name="1311" href="StlcProp.html#1282" class="Bound"
      >N</a
      ><a name="1312" class="Symbol"
      >)</a
      ><a name="1313"
      > </a
      ><a name="1314" href="StlcProp.html#1218" class="Datatype Operator"
      >for</a
      ><a name="1317"
      > </a
      ><a name="1318" class="Symbol"
      >(</a
      ><a name="1319" href="StlcProp.html#1280" class="Bound"
      >A</a
      ><a name="1320"
      > </a
      ><a name="1321" href="Stlc.html#609" class="InductiveConstructor Operator"
      >&#8658;</a
      ><a name="1322"
      > </a
      ><a name="1323" href="StlcProp.html#1284" class="Bound"
      >B</a
      ><a name="1324" class="Symbol"
      >)</a
      ><a name="1325"
      >
  </a
      ><a name="1328" href="StlcProp.html#1328" class="InductiveConstructor"
      >canonical-true</a
      ><a name="1342"
      > </a
      ><a name="1343" class="Symbol"
      >:</a
      ><a name="1344"
      > </a
      ><a name="1345" href="StlcProp.html#1218" class="Datatype Operator"
      >canonical</a
      ><a name="1354"
      > </a
      ><a name="1355" href="Stlc.html#806" class="InductiveConstructor"
      >true</a
      ><a name="1359"
      > </a
      ><a name="1360" href="StlcProp.html#1218" class="Datatype Operator"
      >for</a
      ><a name="1363"
      > </a
      ><a name="1364" href="Stlc.html#636" class="InductiveConstructor"
      >&#120121;</a
      ><a name="1365"
      >
  </a
      ><a name="1368" href="StlcProp.html#1368" class="InductiveConstructor"
      >canonical-false</a
      ><a name="1383"
      > </a
      ><a name="1384" class="Symbol"
      >:</a
      ><a name="1385"
      > </a
      ><a name="1386" href="StlcProp.html#1218" class="Datatype Operator"
      >canonical</a
      ><a name="1395"
      > </a
      ><a name="1396" href="Stlc.html#820" class="InductiveConstructor"
      >false</a
      ><a name="1401"
      > </a
      ><a name="1402" href="StlcProp.html#1218" class="Datatype Operator"
      >for</a
      ><a name="1405"
      > </a
      ><a name="1406" href="Stlc.html#636" class="InductiveConstructor"
      >&#120121;</a
      ><a name="1407"
      >

</a
      ><a name="1409" href="StlcProp.html#1409" class="Function"
      >canonical-forms</a
      ><a name="1424"
      > </a
      ><a name="1425" class="Symbol"
      >:</a
      ><a name="1426"
      > </a
      ><a name="1427" class="Symbol"
      >&#8704;</a
      ><a name="1428"
      > </a
      ><a name="1429" class="Symbol"
      >{</a
      ><a name="1430" href="StlcProp.html#1430" class="Bound"
      >L</a
      ><a name="1431"
      > </a
      ><a name="1432" href="StlcProp.html#1432" class="Bound"
      >A</a
      ><a name="1433" class="Symbol"
      >}</a
      ><a name="1434"
      > </a
      ><a name="1435" class="Symbol"
      >&#8594;</a
      ><a name="1436"
      > </a
      ><a name="1437" href="Maps.html#10265" class="Function"
      >&#8709;</a
      ><a name="1438"
      > </a
      ><a name="1439" href="Stlc.html#3112" class="Datatype Operator"
      >&#8866;</a
      ><a name="1440"
      > </a
      ><a name="1441" href="StlcProp.html#1430" class="Bound"
      >L</a
      ><a name="1442"
      > </a
      ><a name="1443" href="Stlc.html#3112" class="Datatype Operator"
      >&#8758;</a
      ><a name="1444"
      > </a
      ><a name="1445" href="StlcProp.html#1432" class="Bound"
      >A</a
      ><a name="1446"
      > </a
      ><a name="1447" class="Symbol"
      >&#8594;</a
      ><a name="1448"
      > </a
      ><a name="1449" href="Stlc.html#1105" class="Datatype"
      >Value</a
      ><a name="1454"
      > </a
      ><a name="1455" href="StlcProp.html#1430" class="Bound"
      >L</a
      ><a name="1456"
      > </a
      ><a name="1457" class="Symbol"
      >&#8594;</a
      ><a name="1458"
      > </a
      ><a name="1459" href="StlcProp.html#1218" class="Datatype Operator"
      >canonical</a
      ><a name="1468"
      > </a
      ><a name="1469" href="StlcProp.html#1430" class="Bound"
      >L</a
      ><a name="1470"
      > </a
      ><a name="1471" href="StlcProp.html#1218" class="Datatype Operator"
      >for</a
      ><a name="1474"
      > </a
      ><a name="1475" href="StlcProp.html#1432" class="Bound"
      >A</a
      ><a name="1476"
      >
</a
      ><a name="1477" href="StlcProp.html#1409" class="Function"
      >canonical-forms</a
      ><a name="1492"
      > </a
      ><a name="1493" class="Symbol"
      >(</a
      ><a name="1494" href="Stlc.html#3156" class="InductiveConstructor"
      >Ax</a
      ><a name="1496"
      > </a
      ><a name="1497" class="Symbol"
      >())</a
      ><a name="1500"
      > </a
      ><a name="1501" class="Symbol"
      >()</a
      ><a name="1503"
      >
</a
      ><a name="1504" href="StlcProp.html#1409" class="Function"
      >canonical-forms</a
      ><a name="1519"
      > </a
      ><a name="1520" class="Symbol"
      >(</a
      ><a name="1521" href="Stlc.html#3210" class="InductiveConstructor"
      >&#8658;-I</a
      ><a name="1524"
      > </a
      ><a name="1525" href="StlcProp.html#1525" class="Bound"
      >&#8866;N</a
      ><a name="1527" class="Symbol"
      >)</a
      ><a name="1528"
      > </a
      ><a name="1529" href="Stlc.html#1132" class="InductiveConstructor"
      >value-&#955;</a
      ><a name="1536"
      > </a
      ><a name="1537" class="Symbol"
      >=</a
      ><a name="1538"
      > </a
      ><a name="1539" href="StlcProp.html#1261" class="InductiveConstructor"
      >canonical-&#955;</a
      ><a name="1550"
      >
</a
      ><a name="1551" href="StlcProp.html#1409" class="Function"
      >canonical-forms</a
      ><a name="1566"
      > </a
      ><a name="1567" class="Symbol"
      >(</a
      ><a name="1568" href="Stlc.html#3287" class="InductiveConstructor"
      >&#8658;-E</a
      ><a name="1571"
      > </a
      ><a name="1572" href="StlcProp.html#1572" class="Bound"
      >&#8866;L</a
      ><a name="1574"
      > </a
      ><a name="1575" href="StlcProp.html#1575" class="Bound"
      >&#8866;M</a
      ><a name="1577" class="Symbol"
      >)</a
      ><a name="1578"
      > </a
      ><a name="1579" class="Symbol"
      >()</a
      ><a name="1581"
      >
</a
      ><a name="1582" href="StlcProp.html#1409" class="Function"
      >canonical-forms</a
      ><a name="1597"
      > </a
      ><a name="1598" href="Stlc.html#3365" class="InductiveConstructor"
      >&#120121;-I&#8321;</a
      ><a name="1602"
      > </a
      ><a name="1603" href="Stlc.html#1181" class="InductiveConstructor"
      >value-true</a
      ><a name="1613"
      > </a
      ><a name="1614" class="Symbol"
      >=</a
      ><a name="1615"
      > </a
      ><a name="1616" href="StlcProp.html#1328" class="InductiveConstructor"
      >canonical-true</a
      ><a name="1630"
      >
</a
      ><a name="1631" href="StlcProp.html#1409" class="Function"
      >canonical-forms</a
      ><a name="1646"
      > </a
      ><a name="1647" href="Stlc.html#3399" class="InductiveConstructor"
      >&#120121;-I&#8322;</a
      ><a name="1651"
      > </a
      ><a name="1652" href="Stlc.html#1208" class="InductiveConstructor"
      >value-false</a
      ><a name="1663"
      > </a
      ><a name="1664" class="Symbol"
      >=</a
      ><a name="1665"
      > </a
      ><a name="1666" href="StlcProp.html#1368" class="InductiveConstructor"
      >canonical-false</a
      ><a name="1681"
      >
</a
      ><a name="1682" href="StlcProp.html#1409" class="Function"
      >canonical-forms</a
      ><a name="1697"
      > </a
      ><a name="1698" class="Symbol"
      >(</a
      ><a name="1699" href="Stlc.html#3434" class="InductiveConstructor"
      >&#120121;-E</a
      ><a name="1702"
      > </a
      ><a name="1703" href="StlcProp.html#1703" class="Bound"
      >&#8866;L</a
      ><a name="1705"
      > </a
      ><a name="1706" href="StlcProp.html#1706" class="Bound"
      >&#8866;M</a
      ><a name="1708"
      > </a
      ><a name="1709" href="StlcProp.html#1709" class="Bound"
      >&#8866;N</a
      ><a name="1711" class="Symbol"
      >)</a
      ><a name="1712"
      > </a
      ><a name="1713" class="Symbol"
      >()</a
      >

</pre>

## Progress

As before, the _progress_ theorem tells us that closed, well-typed
terms are not stuck: either a well-typed term can take a reduction
step or it is a value.

<pre class="Agda">

<a name="1912" class="Keyword"
      >data</a
      ><a name="1916"
      > </a
      ><a name="1917" href="StlcProp.html#1917" class="Datatype"
      >Progress</a
      ><a name="1925"
      > </a
      ><a name="1926" class="Symbol"
      >:</a
      ><a name="1927"
      > </a
      ><a name="1928" href="Stlc.html#708" class="Datatype"
      >Term</a
      ><a name="1932"
      > </a
      ><a name="1933" class="Symbol"
      >&#8594;</a
      ><a name="1934"
      > </a
      ><a name="1935" class="PrimitiveType"
      >Set</a
      ><a name="1938"
      > </a
      ><a name="1939" class="Keyword"
      >where</a
      ><a name="1944"
      >
  </a
      ><a name="1947" href="StlcProp.html#1947" class="InductiveConstructor"
      >steps</a
      ><a name="1952"
      > </a
      ><a name="1953" class="Symbol"
      >:</a
      ><a name="1954"
      > </a
      ><a name="1955" class="Symbol"
      >&#8704;</a
      ><a name="1956"
      > </a
      ><a name="1957" class="Symbol"
      >{</a
      ><a name="1958" href="StlcProp.html#1958" class="Bound"
      >M</a
      ><a name="1959"
      > </a
      ><a name="1960" href="StlcProp.html#1960" class="Bound"
      >N</a
      ><a name="1961" class="Symbol"
      >}</a
      ><a name="1962"
      > </a
      ><a name="1963" class="Symbol"
      >&#8594;</a
      ><a name="1964"
      > </a
      ><a name="1965" href="StlcProp.html#1958" class="Bound"
      >M</a
      ><a name="1966"
      > </a
      ><a name="1967" href="Stlc.html#1762" class="Datatype Operator"
      >&#10233;</a
      ><a name="1968"
      > </a
      ><a name="1969" href="StlcProp.html#1960" class="Bound"
      >N</a
      ><a name="1970"
      > </a
      ><a name="1971" class="Symbol"
      >&#8594;</a
      ><a name="1972"
      > </a
      ><a name="1973" href="StlcProp.html#1917" class="Datatype"
      >Progress</a
      ><a name="1981"
      > </a
      ><a name="1982" href="StlcProp.html#1958" class="Bound"
      >M</a
      ><a name="1983"
      >
  </a
      ><a name="1986" href="StlcProp.html#1986" class="InductiveConstructor"
      >done</a
      ><a name="1990"
      >  </a
      ><a name="1992" class="Symbol"
      >:</a
      ><a name="1993"
      > </a
      ><a name="1994" class="Symbol"
      >&#8704;</a
      ><a name="1995"
      > </a
      ><a name="1996" class="Symbol"
      >{</a
      ><a name="1997" href="StlcProp.html#1997" class="Bound"
      >M</a
      ><a name="1998" class="Symbol"
      >}</a
      ><a name="1999"
      > </a
      ><a name="2000" class="Symbol"
      >&#8594;</a
      ><a name="2001"
      > </a
      ><a name="2002" href="Stlc.html#1105" class="Datatype"
      >Value</a
      ><a name="2007"
      > </a
      ><a name="2008" href="StlcProp.html#1997" class="Bound"
      >M</a
      ><a name="2009"
      > </a
      ><a name="2010" class="Symbol"
      >&#8594;</a
      ><a name="2011"
      > </a
      ><a name="2012" href="StlcProp.html#1917" class="Datatype"
      >Progress</a
      ><a name="2020"
      > </a
      ><a name="2021" href="StlcProp.html#1997" class="Bound"
      >M</a
      ><a name="2022"
      >

</a
      ><a name="2024" href="StlcProp.html#2024" class="Function"
      >progress</a
      ><a name="2032"
      > </a
      ><a name="2033" class="Symbol"
      >:</a
      ><a name="2034"
      > </a
      ><a name="2035" class="Symbol"
      >&#8704;</a
      ><a name="2036"
      > </a
      ><a name="2037" class="Symbol"
      >{</a
      ><a name="2038" href="StlcProp.html#2038" class="Bound"
      >M</a
      ><a name="2039"
      > </a
      ><a name="2040" href="StlcProp.html#2040" class="Bound"
      >A</a
      ><a name="2041" class="Symbol"
      >}</a
      ><a name="2042"
      > </a
      ><a name="2043" class="Symbol"
      >&#8594;</a
      ><a name="2044"
      > </a
      ><a name="2045" href="Maps.html#10265" class="Function"
      >&#8709;</a
      ><a name="2046"
      > </a
      ><a name="2047" href="Stlc.html#3112" class="Datatype Operator"
      >&#8866;</a
      ><a name="2048"
      > </a
      ><a name="2049" href="StlcProp.html#2038" class="Bound"
      >M</a
      ><a name="2050"
      > </a
      ><a name="2051" href="Stlc.html#3112" class="Datatype Operator"
      >&#8758;</a
      ><a name="2052"
      > </a
      ><a name="2053" href="StlcProp.html#2040" class="Bound"
      >A</a
      ><a name="2054"
      > </a
      ><a name="2055" class="Symbol"
      >&#8594;</a
      ><a name="2056"
      > </a
      ><a name="2057" href="StlcProp.html#1917" class="Datatype"
      >Progress</a
      ><a name="2065"
      > </a
      ><a name="2066" href="StlcProp.html#2038" class="Bound"
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

<a name="3946" href="StlcProp.html#2024" class="Function"
      >progress</a
      ><a name="3954"
      > </a
      ><a name="3955" class="Symbol"
      >(</a
      ><a name="3956" href="Stlc.html#3156" class="InductiveConstructor"
      >Ax</a
      ><a name="3958"
      > </a
      ><a name="3959" class="Symbol"
      >())</a
      ><a name="3962"
      >
</a
      ><a name="3963" href="StlcProp.html#2024" class="Function"
      >progress</a
      ><a name="3971"
      > </a
      ><a name="3972" class="Symbol"
      >(</a
      ><a name="3973" href="Stlc.html#3210" class="InductiveConstructor"
      >&#8658;-I</a
      ><a name="3976"
      > </a
      ><a name="3977" href="StlcProp.html#3977" class="Bound"
      >&#8866;N</a
      ><a name="3979" class="Symbol"
      >)</a
      ><a name="3980"
      > </a
      ><a name="3981" class="Symbol"
      >=</a
      ><a name="3982"
      > </a
      ><a name="3983" href="StlcProp.html#1986" class="InductiveConstructor"
      >done</a
      ><a name="3987"
      > </a
      ><a name="3988" href="Stlc.html#1132" class="InductiveConstructor"
      >value-&#955;</a
      ><a name="3995"
      >
</a
      ><a name="3996" href="StlcProp.html#2024" class="Function"
      >progress</a
      ><a name="4004"
      > </a
      ><a name="4005" class="Symbol"
      >(</a
      ><a name="4006" href="Stlc.html#3287" class="InductiveConstructor"
      >&#8658;-E</a
      ><a name="4009"
      > </a
      ><a name="4010" href="StlcProp.html#4010" class="Bound"
      >&#8866;L</a
      ><a name="4012"
      > </a
      ><a name="4013" href="StlcProp.html#4013" class="Bound"
      >&#8866;M</a
      ><a name="4015" class="Symbol"
      >)</a
      ><a name="4016"
      > </a
      ><a name="4017" class="Keyword"
      >with</a
      ><a name="4021"
      > </a
      ><a name="4022" href="StlcProp.html#2024" class="Function"
      >progress</a
      ><a name="4030"
      > </a
      ><a name="4031" href="StlcProp.html#4010" class="Bound"
      >&#8866;L</a
      ><a name="4033"
      >
</a
      ><a name="4034" class="Symbol"
      >...</a
      ><a name="4037"
      > </a
      ><a name="4038" class="Symbol"
      >|</a
      ><a name="4039"
      > </a
      ><a name="4040" href="StlcProp.html#1947" class="InductiveConstructor"
      >steps</a
      ><a name="4045"
      > </a
      ><a name="4046" href="StlcProp.html#4046" class="Bound"
      >L&#10233;L&#8242;</a
      ><a name="4050"
      > </a
      ><a name="4051" class="Symbol"
      >=</a
      ><a name="4052"
      > </a
      ><a name="4053" href="StlcProp.html#1947" class="InductiveConstructor"
      >steps</a
      ><a name="4058"
      > </a
      ><a name="4059" class="Symbol"
      >(</a
      ><a name="4060" href="Stlc.html#1864" class="InductiveConstructor"
      >&#958;&#183;&#8321;</a
      ><a name="4063"
      > </a
      ><a name="4064" href="StlcProp.html#4046" class="Bound"
      >L&#10233;L&#8242;</a
      ><a name="4068" class="Symbol"
      >)</a
      ><a name="4069"
      >
</a
      ><a name="4070" class="Symbol"
      >...</a
      ><a name="4073"
      > </a
      ><a name="4074" class="Symbol"
      >|</a
      ><a name="4075"
      > </a
      ><a name="4076" href="StlcProp.html#1986" class="InductiveConstructor"
      >done</a
      ><a name="4080"
      > </a
      ><a name="4081" href="StlcProp.html#4081" class="Bound"
      >valueL</a
      ><a name="4087"
      > </a
      ><a name="4088" class="Keyword"
      >with</a
      ><a name="4092"
      > </a
      ><a name="4093" href="StlcProp.html#2024" class="Function"
      >progress</a
      ><a name="4101"
      > </a
      ><a name="4102" href="StlcProp.html#4013" class="Bound"
      >&#8866;M</a
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
      ><a name="4111" href="StlcProp.html#1947" class="InductiveConstructor"
      >steps</a
      ><a name="4116"
      > </a
      ><a name="4117" href="StlcProp.html#4117" class="Bound"
      >M&#10233;M&#8242;</a
      ><a name="4121"
      > </a
      ><a name="4122" class="Symbol"
      >=</a
      ><a name="4123"
      > </a
      ><a name="4124" href="StlcProp.html#1947" class="InductiveConstructor"
      >steps</a
      ><a name="4129"
      > </a
      ><a name="4130" class="Symbol"
      >(</a
      ><a name="4131" href="Stlc.html#1917" class="InductiveConstructor"
      >&#958;&#183;&#8322;</a
      ><a name="4134"
      > </a
      ><a name="4135" href="StlcProp.html#4081" class="Bound"
      >valueL</a
      ><a name="4141"
      > </a
      ><a name="4142" href="StlcProp.html#4117" class="Bound"
      >M&#10233;M&#8242;</a
      ><a name="4146" class="Symbol"
      >)</a
      ><a name="4147"
      >
</a
      ><a name="4148" class="Symbol"
      >...</a
      ><a name="4151"
      > </a
      ><a name="4152" class="Symbol"
      >|</a
      ><a name="4153"
      > </a
      ><a name="4154" href="StlcProp.html#1986" class="InductiveConstructor"
      >done</a
      ><a name="4158"
      > </a
      ><a name="4159" href="StlcProp.html#4159" class="Bound"
      >valueM</a
      ><a name="4165"
      > </a
      ><a name="4166" class="Keyword"
      >with</a
      ><a name="4170"
      > </a
      ><a name="4171" href="StlcProp.html#1409" class="Function"
      >canonical-forms</a
      ><a name="4186"
      > </a
      ><a name="4187" href="StlcProp.html#4010" class="Bound"
      >&#8866;L</a
      ><a name="4189"
      > </a
      ><a name="4190" href="StlcProp.html#4081" class="Bound"
      >valueL</a
      ><a name="4196"
      >
</a
      ><a name="4197" class="Symbol"
      >...</a
      ><a name="4200"
      > </a
      ><a name="4201" class="Symbol"
      >|</a
      ><a name="4202"
      > </a
      ><a name="4203" href="StlcProp.html#1261" class="InductiveConstructor"
      >canonical-&#955;</a
      ><a name="4214"
      > </a
      ><a name="4215" class="Symbol"
      >=</a
      ><a name="4216"
      > </a
      ><a name="4217" href="StlcProp.html#1947" class="InductiveConstructor"
      >steps</a
      ><a name="4222"
      > </a
      ><a name="4223" class="Symbol"
      >(</a
      ><a name="4224" href="Stlc.html#1794" class="InductiveConstructor"
      >&#946;&#955;&#183;</a
      ><a name="4227"
      > </a
      ><a name="4228" href="StlcProp.html#4159" class="Bound"
      >valueM</a
      ><a name="4234" class="Symbol"
      >)</a
      ><a name="4235"
      >
</a
      ><a name="4236" href="StlcProp.html#2024" class="Function"
      >progress</a
      ><a name="4244"
      > </a
      ><a name="4245" href="Stlc.html#3365" class="InductiveConstructor"
      >&#120121;-I&#8321;</a
      ><a name="4249"
      > </a
      ><a name="4250" class="Symbol"
      >=</a
      ><a name="4251"
      > </a
      ><a name="4252" href="StlcProp.html#1986" class="InductiveConstructor"
      >done</a
      ><a name="4256"
      > </a
      ><a name="4257" href="Stlc.html#1181" class="InductiveConstructor"
      >value-true</a
      ><a name="4267"
      >
</a
      ><a name="4268" href="StlcProp.html#2024" class="Function"
      >progress</a
      ><a name="4276"
      > </a
      ><a name="4277" href="Stlc.html#3399" class="InductiveConstructor"
      >&#120121;-I&#8322;</a
      ><a name="4281"
      > </a
      ><a name="4282" class="Symbol"
      >=</a
      ><a name="4283"
      > </a
      ><a name="4284" href="StlcProp.html#1986" class="InductiveConstructor"
      >done</a
      ><a name="4288"
      > </a
      ><a name="4289" href="Stlc.html#1208" class="InductiveConstructor"
      >value-false</a
      ><a name="4300"
      >
</a
      ><a name="4301" href="StlcProp.html#2024" class="Function"
      >progress</a
      ><a name="4309"
      > </a
      ><a name="4310" class="Symbol"
      >(</a
      ><a name="4311" href="Stlc.html#3434" class="InductiveConstructor"
      >&#120121;-E</a
      ><a name="4314"
      > </a
      ><a name="4315" href="StlcProp.html#4315" class="Bound"
      >&#8866;L</a
      ><a name="4317"
      > </a
      ><a name="4318" href="StlcProp.html#4318" class="Bound"
      >&#8866;M</a
      ><a name="4320"
      > </a
      ><a name="4321" href="StlcProp.html#4321" class="Bound"
      >&#8866;N</a
      ><a name="4323" class="Symbol"
      >)</a
      ><a name="4324"
      > </a
      ><a name="4325" class="Keyword"
      >with</a
      ><a name="4329"
      > </a
      ><a name="4330" href="StlcProp.html#2024" class="Function"
      >progress</a
      ><a name="4338"
      > </a
      ><a name="4339" href="StlcProp.html#4315" class="Bound"
      >&#8866;L</a
      ><a name="4341"
      >
</a
      ><a name="4342" class="Symbol"
      >...</a
      ><a name="4345"
      > </a
      ><a name="4346" class="Symbol"
      >|</a
      ><a name="4347"
      > </a
      ><a name="4348" href="StlcProp.html#1947" class="InductiveConstructor"
      >steps</a
      ><a name="4353"
      > </a
      ><a name="4354" href="StlcProp.html#4354" class="Bound"
      >L&#10233;L&#8242;</a
      ><a name="4358"
      > </a
      ><a name="4359" class="Symbol"
      >=</a
      ><a name="4360"
      > </a
      ><a name="4361" href="StlcProp.html#1947" class="InductiveConstructor"
      >steps</a
      ><a name="4366"
      > </a
      ><a name="4367" class="Symbol"
      >(</a
      ><a name="4368" href="Stlc.html#2092" class="InductiveConstructor"
      >&#958;if</a
      ><a name="4371"
      > </a
      ><a name="4372" href="StlcProp.html#4354" class="Bound"
      >L&#10233;L&#8242;</a
      ><a name="4376" class="Symbol"
      >)</a
      ><a name="4377"
      >
</a
      ><a name="4378" class="Symbol"
      >...</a
      ><a name="4381"
      > </a
      ><a name="4382" class="Symbol"
      >|</a
      ><a name="4383"
      > </a
      ><a name="4384" href="StlcProp.html#1986" class="InductiveConstructor"
      >done</a
      ><a name="4388"
      > </a
      ><a name="4389" href="StlcProp.html#4389" class="Bound"
      >valueL</a
      ><a name="4395"
      > </a
      ><a name="4396" class="Keyword"
      >with</a
      ><a name="4400"
      > </a
      ><a name="4401" href="StlcProp.html#1409" class="Function"
      >canonical-forms</a
      ><a name="4416"
      > </a
      ><a name="4417" href="StlcProp.html#4315" class="Bound"
      >&#8866;L</a
      ><a name="4419"
      > </a
      ><a name="4420" href="StlcProp.html#4389" class="Bound"
      >valueL</a
      ><a name="4426"
      >
</a
      ><a name="4427" class="Symbol"
      >...</a
      ><a name="4430"
      > </a
      ><a name="4431" class="Symbol"
      >|</a
      ><a name="4432"
      > </a
      ><a name="4433" href="StlcProp.html#1328" class="InductiveConstructor"
      >canonical-true</a
      ><a name="4447"
      > </a
      ><a name="4448" class="Symbol"
      >=</a
      ><a name="4449"
      > </a
      ><a name="4450" href="StlcProp.html#1947" class="InductiveConstructor"
      >steps</a
      ><a name="4455"
      > </a
      ><a name="4456" href="Stlc.html#1984" class="InductiveConstructor"
      >&#946;if-true</a
      ><a name="4464"
      >
</a
      ><a name="4465" class="Symbol"
      >...</a
      ><a name="4468"
      > </a
      ><a name="4469" class="Symbol"
      >|</a
      ><a name="4470"
      > </a
      ><a name="4471" href="StlcProp.html#1368" class="InductiveConstructor"
      >canonical-false</a
      ><a name="4486"
      > </a
      ><a name="4487" class="Symbol"
      >=</a
      ><a name="4488"
      > </a
      ><a name="4489" href="StlcProp.html#1947" class="InductiveConstructor"
      >steps</a
      ><a name="4494"
      > </a
      ><a name="4495" href="Stlc.html#2037" class="InductiveConstructor"
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

<a name="5152" class="Keyword"
      >postulate</a
      ><a name="5161"
      >
  </a
      ><a name="5164" href="StlcProp.html#5164" class="Postulate"
      >progress&#8242;</a
      ><a name="5173"
      > </a
      ><a name="5174" class="Symbol"
      >:</a
      ><a name="5175"
      > </a
      ><a name="5176" class="Symbol"
      >&#8704;</a
      ><a name="5177"
      > </a
      ><a name="5178" href="StlcProp.html#5178" class="Bound"
      >M</a
      ><a name="5179"
      > </a
      ><a name="5180" class="Symbol"
      >{</a
      ><a name="5181" href="StlcProp.html#5181" class="Bound"
      >A</a
      ><a name="5182" class="Symbol"
      >}</a
      ><a name="5183"
      > </a
      ><a name="5184" class="Symbol"
      >&#8594;</a
      ><a name="5185"
      > </a
      ><a name="5186" href="Maps.html#10265" class="Function"
      >&#8709;</a
      ><a name="5187"
      > </a
      ><a name="5188" href="Stlc.html#3112" class="Datatype Operator"
      >&#8866;</a
      ><a name="5189"
      > </a
      ><a name="5190" href="StlcProp.html#5178" class="Bound"
      >M</a
      ><a name="5191"
      > </a
      ><a name="5192" href="Stlc.html#3112" class="Datatype Operator"
      >&#8758;</a
      ><a name="5193"
      > </a
      ><a name="5194" href="StlcProp.html#5181" class="Bound"
      >A</a
      ><a name="5195"
      > </a
      ><a name="5196" class="Symbol"
      >&#8594;</a
      ><a name="5197"
      > </a
      ><a name="5198" href="StlcProp.html#1917" class="Datatype"
      >Progress</a
      ><a name="5206"
      > </a
      ><a name="5207" href="StlcProp.html#5178" class="Bound"
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

<a name="7654" class="Keyword"
      >data</a
      ><a name="7658"
      > </a
      ><a name="7659" href="StlcProp.html#7659" class="Datatype Operator"
      >_&#8712;_</a
      ><a name="7662"
      > </a
      ><a name="7663" class="Symbol"
      >:</a
      ><a name="7664"
      > </a
      ><a name="7665" href="Maps.html#2171" class="Datatype"
      >Id</a
      ><a name="7667"
      > </a
      ><a name="7668" class="Symbol"
      >&#8594;</a
      ><a name="7669"
      > </a
      ><a name="7670" href="Stlc.html#708" class="Datatype"
      >Term</a
      ><a name="7674"
      > </a
      ><a name="7675" class="Symbol"
      >&#8594;</a
      ><a name="7676"
      > </a
      ><a name="7677" class="PrimitiveType"
      >Set</a
      ><a name="7680"
      > </a
      ><a name="7681" class="Keyword"
      >where</a
      ><a name="7686"
      >
  </a
      ><a name="7689" href="StlcProp.html#7689" class="InductiveConstructor"
      >free-`</a
      ><a name="7695"
      >  </a
      ><a name="7697" class="Symbol"
      >:</a
      ><a name="7698"
      > </a
      ><a name="7699" class="Symbol"
      >&#8704;</a
      ><a name="7700"
      > </a
      ><a name="7701" class="Symbol"
      >{</a
      ><a name="7702" href="StlcProp.html#7702" class="Bound"
      >x</a
      ><a name="7703" class="Symbol"
      >}</a
      ><a name="7704"
      > </a
      ><a name="7705" class="Symbol"
      >&#8594;</a
      ><a name="7706"
      > </a
      ><a name="7707" href="StlcProp.html#7702" class="Bound"
      >x</a
      ><a name="7708"
      > </a
      ><a name="7709" href="StlcProp.html#7659" class="Datatype Operator"
      >&#8712;</a
      ><a name="7710"
      > </a
      ><a name="7711" href="Stlc.html#727" class="InductiveConstructor"
      >`</a
      ><a name="7712"
      > </a
      ><a name="7713" href="StlcProp.html#7702" class="Bound"
      >x</a
      ><a name="7714"
      >
  </a
      ><a name="7717" href="StlcProp.html#7717" class="InductiveConstructor"
      >free-&#955;</a
      ><a name="7723"
      >  </a
      ><a name="7725" class="Symbol"
      >:</a
      ><a name="7726"
      > </a
      ><a name="7727" class="Symbol"
      >&#8704;</a
      ><a name="7728"
      > </a
      ><a name="7729" class="Symbol"
      >{</a
      ><a name="7730" href="StlcProp.html#7730" class="Bound"
      >x</a
      ><a name="7731"
      > </a
      ><a name="7732" href="StlcProp.html#7732" class="Bound"
      >y</a
      ><a name="7733"
      > </a
      ><a name="7734" href="StlcProp.html#7734" class="Bound"
      >A</a
      ><a name="7735"
      > </a
      ><a name="7736" href="StlcProp.html#7736" class="Bound"
      >N</a
      ><a name="7737" class="Symbol"
      >}</a
      ><a name="7738"
      > </a
      ><a name="7739" class="Symbol"
      >&#8594;</a
      ><a name="7740"
      > </a
      ><a name="7741" href="StlcProp.html#7732" class="Bound"
      >y</a
      ><a name="7742"
      > </a
      ><a name="7743" href="https://agda.github.io/agda-stdlib/Relation.Binary.Core.html#4493" class="Function Operator"
      >&#8802;</a
      ><a name="7744"
      > </a
      ><a name="7745" href="StlcProp.html#7730" class="Bound"
      >x</a
      ><a name="7746"
      > </a
      ><a name="7747" class="Symbol"
      >&#8594;</a
      ><a name="7748"
      > </a
      ><a name="7749" href="StlcProp.html#7730" class="Bound"
      >x</a
      ><a name="7750"
      > </a
      ><a name="7751" href="StlcProp.html#7659" class="Datatype Operator"
      >&#8712;</a
      ><a name="7752"
      > </a
      ><a name="7753" href="StlcProp.html#7736" class="Bound"
      >N</a
      ><a name="7754"
      > </a
      ><a name="7755" class="Symbol"
      >&#8594;</a
      ><a name="7756"
      > </a
      ><a name="7757" href="StlcProp.html#7730" class="Bound"
      >x</a
      ><a name="7758"
      > </a
      ><a name="7759" href="StlcProp.html#7659" class="Datatype Operator"
      >&#8712;</a
      ><a name="7760"
      > </a
      ><a name="7761" class="Symbol"
      >(</a
      ><a name="7762" href="Stlc.html#743" class="InductiveConstructor Operator"
      >&#955;[</a
      ><a name="7764"
      > </a
      ><a name="7765" href="StlcProp.html#7732" class="Bound"
      >y</a
      ><a name="7766"
      > </a
      ><a name="7767" href="Stlc.html#743" class="InductiveConstructor Operator"
      >&#8758;</a
      ><a name="7768"
      > </a
      ><a name="7769" href="StlcProp.html#7734" class="Bound"
      >A</a
      ><a name="7770"
      > </a
      ><a name="7771" href="Stlc.html#743" class="InductiveConstructor Operator"
      >]</a
      ><a name="7772"
      > </a
      ><a name="7773" href="StlcProp.html#7736" class="Bound"
      >N</a
      ><a name="7774" class="Symbol"
      >)</a
      ><a name="7775"
      >
  </a
      ><a name="7778" href="StlcProp.html#7778" class="InductiveConstructor"
      >free-&#183;&#8321;</a
      ><a name="7785"
      > </a
      ><a name="7786" class="Symbol"
      >:</a
      ><a name="7787"
      > </a
      ><a name="7788" class="Symbol"
      >&#8704;</a
      ><a name="7789"
      > </a
      ><a name="7790" class="Symbol"
      >{</a
      ><a name="7791" href="StlcProp.html#7791" class="Bound"
      >x</a
      ><a name="7792"
      > </a
      ><a name="7793" href="StlcProp.html#7793" class="Bound"
      >L</a
      ><a name="7794"
      > </a
      ><a name="7795" href="StlcProp.html#7795" class="Bound"
      >M</a
      ><a name="7796" class="Symbol"
      >}</a
      ><a name="7797"
      > </a
      ><a name="7798" class="Symbol"
      >&#8594;</a
      ><a name="7799"
      > </a
      ><a name="7800" href="StlcProp.html#7791" class="Bound"
      >x</a
      ><a name="7801"
      > </a
      ><a name="7802" href="StlcProp.html#7659" class="Datatype Operator"
      >&#8712;</a
      ><a name="7803"
      > </a
      ><a name="7804" href="StlcProp.html#7793" class="Bound"
      >L</a
      ><a name="7805"
      > </a
      ><a name="7806" class="Symbol"
      >&#8594;</a
      ><a name="7807"
      > </a
      ><a name="7808" href="StlcProp.html#7791" class="Bound"
      >x</a
      ><a name="7809"
      > </a
      ><a name="7810" href="StlcProp.html#7659" class="Datatype Operator"
      >&#8712;</a
      ><a name="7811"
      > </a
      ><a name="7812" class="Symbol"
      >(</a
      ><a name="7813" href="StlcProp.html#7793" class="Bound"
      >L</a
      ><a name="7814"
      > </a
      ><a name="7815" href="Stlc.html#779" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="7816"
      > </a
      ><a name="7817" href="StlcProp.html#7795" class="Bound"
      >M</a
      ><a name="7818" class="Symbol"
      >)</a
      ><a name="7819"
      >
  </a
      ><a name="7822" href="StlcProp.html#7822" class="InductiveConstructor"
      >free-&#183;&#8322;</a
      ><a name="7829"
      > </a
      ><a name="7830" class="Symbol"
      >:</a
      ><a name="7831"
      > </a
      ><a name="7832" class="Symbol"
      >&#8704;</a
      ><a name="7833"
      > </a
      ><a name="7834" class="Symbol"
      >{</a
      ><a name="7835" href="StlcProp.html#7835" class="Bound"
      >x</a
      ><a name="7836"
      > </a
      ><a name="7837" href="StlcProp.html#7837" class="Bound"
      >L</a
      ><a name="7838"
      > </a
      ><a name="7839" href="StlcProp.html#7839" class="Bound"
      >M</a
      ><a name="7840" class="Symbol"
      >}</a
      ><a name="7841"
      > </a
      ><a name="7842" class="Symbol"
      >&#8594;</a
      ><a name="7843"
      > </a
      ><a name="7844" href="StlcProp.html#7835" class="Bound"
      >x</a
      ><a name="7845"
      > </a
      ><a name="7846" href="StlcProp.html#7659" class="Datatype Operator"
      >&#8712;</a
      ><a name="7847"
      > </a
      ><a name="7848" href="StlcProp.html#7839" class="Bound"
      >M</a
      ><a name="7849"
      > </a
      ><a name="7850" class="Symbol"
      >&#8594;</a
      ><a name="7851"
      > </a
      ><a name="7852" href="StlcProp.html#7835" class="Bound"
      >x</a
      ><a name="7853"
      > </a
      ><a name="7854" href="StlcProp.html#7659" class="Datatype Operator"
      >&#8712;</a
      ><a name="7855"
      > </a
      ><a name="7856" class="Symbol"
      >(</a
      ><a name="7857" href="StlcProp.html#7837" class="Bound"
      >L</a
      ><a name="7858"
      > </a
      ><a name="7859" href="Stlc.html#779" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="7860"
      > </a
      ><a name="7861" href="StlcProp.html#7839" class="Bound"
      >M</a
      ><a name="7862" class="Symbol"
      >)</a
      ><a name="7863"
      >
  </a
      ><a name="7866" href="StlcProp.html#7866" class="InductiveConstructor"
      >free-if&#8321;</a
      ><a name="7874"
      > </a
      ><a name="7875" class="Symbol"
      >:</a
      ><a name="7876"
      > </a
      ><a name="7877" class="Symbol"
      >&#8704;</a
      ><a name="7878"
      > </a
      ><a name="7879" class="Symbol"
      >{</a
      ><a name="7880" href="StlcProp.html#7880" class="Bound"
      >x</a
      ><a name="7881"
      > </a
      ><a name="7882" href="StlcProp.html#7882" class="Bound"
      >L</a
      ><a name="7883"
      > </a
      ><a name="7884" href="StlcProp.html#7884" class="Bound"
      >M</a
      ><a name="7885"
      > </a
      ><a name="7886" href="StlcProp.html#7886" class="Bound"
      >N</a
      ><a name="7887" class="Symbol"
      >}</a
      ><a name="7888"
      > </a
      ><a name="7889" class="Symbol"
      >&#8594;</a
      ><a name="7890"
      > </a
      ><a name="7891" href="StlcProp.html#7880" class="Bound"
      >x</a
      ><a name="7892"
      > </a
      ><a name="7893" href="StlcProp.html#7659" class="Datatype Operator"
      >&#8712;</a
      ><a name="7894"
      > </a
      ><a name="7895" href="StlcProp.html#7882" class="Bound"
      >L</a
      ><a name="7896"
      > </a
      ><a name="7897" class="Symbol"
      >&#8594;</a
      ><a name="7898"
      > </a
      ><a name="7899" href="StlcProp.html#7880" class="Bound"
      >x</a
      ><a name="7900"
      > </a
      ><a name="7901" href="StlcProp.html#7659" class="Datatype Operator"
      >&#8712;</a
      ><a name="7902"
      > </a
      ><a name="7903" class="Symbol"
      >(</a
      ><a name="7904" href="Stlc.html#835" class="InductiveConstructor Operator"
      >if</a
      ><a name="7906"
      > </a
      ><a name="7907" href="StlcProp.html#7882" class="Bound"
      >L</a
      ><a name="7908"
      > </a
      ><a name="7909" href="Stlc.html#835" class="InductiveConstructor Operator"
      >then</a
      ><a name="7913"
      > </a
      ><a name="7914" href="StlcProp.html#7884" class="Bound"
      >M</a
      ><a name="7915"
      > </a
      ><a name="7916" href="Stlc.html#835" class="InductiveConstructor Operator"
      >else</a
      ><a name="7920"
      > </a
      ><a name="7921" href="StlcProp.html#7886" class="Bound"
      >N</a
      ><a name="7922" class="Symbol"
      >)</a
      ><a name="7923"
      >
  </a
      ><a name="7926" href="StlcProp.html#7926" class="InductiveConstructor"
      >free-if&#8322;</a
      ><a name="7934"
      > </a
      ><a name="7935" class="Symbol"
      >:</a
      ><a name="7936"
      > </a
      ><a name="7937" class="Symbol"
      >&#8704;</a
      ><a name="7938"
      > </a
      ><a name="7939" class="Symbol"
      >{</a
      ><a name="7940" href="StlcProp.html#7940" class="Bound"
      >x</a
      ><a name="7941"
      > </a
      ><a name="7942" href="StlcProp.html#7942" class="Bound"
      >L</a
      ><a name="7943"
      > </a
      ><a name="7944" href="StlcProp.html#7944" class="Bound"
      >M</a
      ><a name="7945"
      > </a
      ><a name="7946" href="StlcProp.html#7946" class="Bound"
      >N</a
      ><a name="7947" class="Symbol"
      >}</a
      ><a name="7948"
      > </a
      ><a name="7949" class="Symbol"
      >&#8594;</a
      ><a name="7950"
      > </a
      ><a name="7951" href="StlcProp.html#7940" class="Bound"
      >x</a
      ><a name="7952"
      > </a
      ><a name="7953" href="StlcProp.html#7659" class="Datatype Operator"
      >&#8712;</a
      ><a name="7954"
      > </a
      ><a name="7955" href="StlcProp.html#7944" class="Bound"
      >M</a
      ><a name="7956"
      > </a
      ><a name="7957" class="Symbol"
      >&#8594;</a
      ><a name="7958"
      > </a
      ><a name="7959" href="StlcProp.html#7940" class="Bound"
      >x</a
      ><a name="7960"
      > </a
      ><a name="7961" href="StlcProp.html#7659" class="Datatype Operator"
      >&#8712;</a
      ><a name="7962"
      > </a
      ><a name="7963" class="Symbol"
      >(</a
      ><a name="7964" href="Stlc.html#835" class="InductiveConstructor Operator"
      >if</a
      ><a name="7966"
      > </a
      ><a name="7967" href="StlcProp.html#7942" class="Bound"
      >L</a
      ><a name="7968"
      > </a
      ><a name="7969" href="Stlc.html#835" class="InductiveConstructor Operator"
      >then</a
      ><a name="7973"
      > </a
      ><a name="7974" href="StlcProp.html#7944" class="Bound"
      >M</a
      ><a name="7975"
      > </a
      ><a name="7976" href="Stlc.html#835" class="InductiveConstructor Operator"
      >else</a
      ><a name="7980"
      > </a
      ><a name="7981" href="StlcProp.html#7946" class="Bound"
      >N</a
      ><a name="7982" class="Symbol"
      >)</a
      ><a name="7983"
      >
  </a
      ><a name="7986" href="StlcProp.html#7986" class="InductiveConstructor"
      >free-if&#8323;</a
      ><a name="7994"
      > </a
      ><a name="7995" class="Symbol"
      >:</a
      ><a name="7996"
      > </a
      ><a name="7997" class="Symbol"
      >&#8704;</a
      ><a name="7998"
      > </a
      ><a name="7999" class="Symbol"
      >{</a
      ><a name="8000" href="StlcProp.html#8000" class="Bound"
      >x</a
      ><a name="8001"
      > </a
      ><a name="8002" href="StlcProp.html#8002" class="Bound"
      >L</a
      ><a name="8003"
      > </a
      ><a name="8004" href="StlcProp.html#8004" class="Bound"
      >M</a
      ><a name="8005"
      > </a
      ><a name="8006" href="StlcProp.html#8006" class="Bound"
      >N</a
      ><a name="8007" class="Symbol"
      >}</a
      ><a name="8008"
      > </a
      ><a name="8009" class="Symbol"
      >&#8594;</a
      ><a name="8010"
      > </a
      ><a name="8011" href="StlcProp.html#8000" class="Bound"
      >x</a
      ><a name="8012"
      > </a
      ><a name="8013" href="StlcProp.html#7659" class="Datatype Operator"
      >&#8712;</a
      ><a name="8014"
      > </a
      ><a name="8015" href="StlcProp.html#8006" class="Bound"
      >N</a
      ><a name="8016"
      > </a
      ><a name="8017" class="Symbol"
      >&#8594;</a
      ><a name="8018"
      > </a
      ><a name="8019" href="StlcProp.html#8000" class="Bound"
      >x</a
      ><a name="8020"
      > </a
      ><a name="8021" href="StlcProp.html#7659" class="Datatype Operator"
      >&#8712;</a
      ><a name="8022"
      > </a
      ><a name="8023" class="Symbol"
      >(</a
      ><a name="8024" href="Stlc.html#835" class="InductiveConstructor Operator"
      >if</a
      ><a name="8026"
      > </a
      ><a name="8027" href="StlcProp.html#8002" class="Bound"
      >L</a
      ><a name="8028"
      > </a
      ><a name="8029" href="Stlc.html#835" class="InductiveConstructor Operator"
      >then</a
      ><a name="8033"
      > </a
      ><a name="8034" href="StlcProp.html#8004" class="Bound"
      >M</a
      ><a name="8035"
      > </a
      ><a name="8036" href="Stlc.html#835" class="InductiveConstructor Operator"
      >else</a
      ><a name="8040"
      > </a
      ><a name="8041" href="StlcProp.html#8006" class="Bound"
      >N</a
      ><a name="8042" class="Symbol"
      >)</a
      >

</pre>

A term in which no variables appear free is said to be _closed_.

<pre class="Agda">

<a name="8135" href="StlcProp.html#8135" class="Function Operator"
      >_&#8713;_</a
      ><a name="8138"
      > </a
      ><a name="8139" class="Symbol"
      >:</a
      ><a name="8140"
      > </a
      ><a name="8141" href="Maps.html#2171" class="Datatype"
      >Id</a
      ><a name="8143"
      > </a
      ><a name="8144" class="Symbol"
      >&#8594;</a
      ><a name="8145"
      > </a
      ><a name="8146" href="Stlc.html#708" class="Datatype"
      >Term</a
      ><a name="8150"
      > </a
      ><a name="8151" class="Symbol"
      >&#8594;</a
      ><a name="8152"
      > </a
      ><a name="8153" class="PrimitiveType"
      >Set</a
      ><a name="8156"
      >
</a
      ><a name="8157" href="StlcProp.html#8157" class="Bound"
      >x</a
      ><a name="8158"
      > </a
      ><a name="8159" href="StlcProp.html#8135" class="Function Operator"
      >&#8713;</a
      ><a name="8160"
      > </a
      ><a name="8161" href="StlcProp.html#8161" class="Bound"
      >M</a
      ><a name="8162"
      > </a
      ><a name="8163" class="Symbol"
      >=</a
      ><a name="8164"
      > </a
      ><a name="8165" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#414" class="Function Operator"
      >&#172;</a
      ><a name="8166"
      > </a
      ><a name="8167" class="Symbol"
      >(</a
      ><a name="8168" href="StlcProp.html#8157" class="Bound"
      >x</a
      ><a name="8169"
      > </a
      ><a name="8170" href="StlcProp.html#7659" class="Datatype Operator"
      >&#8712;</a
      ><a name="8171"
      > </a
      ><a name="8172" href="StlcProp.html#8161" class="Bound"
      >M</a
      ><a name="8173" class="Symbol"
      >)</a
      ><a name="8174"
      >

</a
      ><a name="8176" href="StlcProp.html#8176" class="Function"
      >closed</a
      ><a name="8182"
      > </a
      ><a name="8183" class="Symbol"
      >:</a
      ><a name="8184"
      > </a
      ><a name="8185" href="Stlc.html#708" class="Datatype"
      >Term</a
      ><a name="8189"
      > </a
      ><a name="8190" class="Symbol"
      >&#8594;</a
      ><a name="8191"
      > </a
      ><a name="8192" class="PrimitiveType"
      >Set</a
      ><a name="8195"
      >
</a
      ><a name="8196" href="StlcProp.html#8176" class="Function"
      >closed</a
      ><a name="8202"
      > </a
      ><a name="8203" href="StlcProp.html#8203" class="Bound"
      >M</a
      ><a name="8204"
      > </a
      ><a name="8205" class="Symbol"
      >=</a
      ><a name="8206"
      > </a
      ><a name="8207" class="Symbol"
      >&#8704;</a
      ><a name="8208"
      > </a
      ><a name="8209" class="Symbol"
      >{</a
      ><a name="8210" href="StlcProp.html#8210" class="Bound"
      >x</a
      ><a name="8211" class="Symbol"
      >}</a
      ><a name="8212"
      > </a
      ><a name="8213" class="Symbol"
      >&#8594;</a
      ><a name="8214"
      > </a
      ><a name="8215" href="StlcProp.html#8210" class="Bound"
      >x</a
      ><a name="8216"
      > </a
      ><a name="8217" href="StlcProp.html#8135" class="Function Operator"
      >&#8713;</a
      ><a name="8218"
      > </a
      ><a name="8219" href="StlcProp.html#8203" class="Bound"
      >M</a
      >

</pre>

Here are proofs corresponding to the first two examples above.

<pre class="Agda">

<a name="8310" href="StlcProp.html#8310" class="Function"
      >f&#8802;x</a
      ><a name="8313"
      > </a
      ><a name="8314" class="Symbol"
      >:</a
      ><a name="8315"
      > </a
      ><a name="8316" href="Stlc.html#917" class="Function"
      >f</a
      ><a name="8317"
      > </a
      ><a name="8318" href="https://agda.github.io/agda-stdlib/Relation.Binary.Core.html#4493" class="Function Operator"
      >&#8802;</a
      ><a name="8319"
      > </a
      ><a name="8320" href="Stlc.html#919" class="Function"
      >x</a
      ><a name="8321"
      >
</a
      ><a name="8322" href="StlcProp.html#8310" class="Function"
      >f&#8802;x</a
      ><a name="8325"
      > </a
      ><a name="8326" class="Symbol"
      >()</a
      ><a name="8328"
      >

</a
      ><a name="8330" href="StlcProp.html#8330" class="Function"
      >example-free&#8321;</a
      ><a name="8343"
      > </a
      ><a name="8344" class="Symbol"
      >:</a
      ><a name="8345"
      > </a
      ><a name="8346" href="Stlc.html#919" class="Function"
      >x</a
      ><a name="8347"
      > </a
      ><a name="8348" href="StlcProp.html#7659" class="Datatype Operator"
      >&#8712;</a
      ><a name="8349"
      > </a
      ><a name="8350" class="Symbol"
      >(</a
      ><a name="8351" href="Stlc.html#743" class="InductiveConstructor Operator"
      >&#955;[</a
      ><a name="8353"
      > </a
      ><a name="8354" href="Stlc.html#917" class="Function"
      >f</a
      ><a name="8355"
      > </a
      ><a name="8356" href="Stlc.html#743" class="InductiveConstructor Operator"
      >&#8758;</a
      ><a name="8357"
      > </a
      ><a name="8358" class="Symbol"
      >(</a
      ><a name="8359" href="Stlc.html#636" class="InductiveConstructor"
      >&#120121;</a
      ><a name="8360"
      > </a
      ><a name="8361" href="Stlc.html#609" class="InductiveConstructor Operator"
      >&#8658;</a
      ><a name="8362"
      > </a
      ><a name="8363" href="Stlc.html#636" class="InductiveConstructor"
      >&#120121;</a
      ><a name="8364" class="Symbol"
      >)</a
      ><a name="8365"
      > </a
      ><a name="8366" href="Stlc.html#743" class="InductiveConstructor Operator"
      >]</a
      ><a name="8367"
      > </a
      ><a name="8368" href="Stlc.html#727" class="InductiveConstructor"
      >`</a
      ><a name="8369"
      > </a
      ><a name="8370" href="Stlc.html#917" class="Function"
      >f</a
      ><a name="8371"
      > </a
      ><a name="8372" href="Stlc.html#779" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="8373"
      > </a
      ><a name="8374" href="Stlc.html#727" class="InductiveConstructor"
      >`</a
      ><a name="8375"
      > </a
      ><a name="8376" href="Stlc.html#919" class="Function"
      >x</a
      ><a name="8377" class="Symbol"
      >)</a
      ><a name="8378"
      >
</a
      ><a name="8379" href="StlcProp.html#8330" class="Function"
      >example-free&#8321;</a
      ><a name="8392"
      > </a
      ><a name="8393" class="Symbol"
      >=</a
      ><a name="8394"
      > </a
      ><a name="8395" href="StlcProp.html#7717" class="InductiveConstructor"
      >free-&#955;</a
      ><a name="8401"
      > </a
      ><a name="8402" href="StlcProp.html#8310" class="Function"
      >f&#8802;x</a
      ><a name="8405"
      > </a
      ><a name="8406" class="Symbol"
      >(</a
      ><a name="8407" href="StlcProp.html#7822" class="InductiveConstructor"
      >free-&#183;&#8322;</a
      ><a name="8414"
      > </a
      ><a name="8415" href="StlcProp.html#7689" class="InductiveConstructor"
      >free-`</a
      ><a name="8421" class="Symbol"
      >)</a
      ><a name="8422"
      >

</a
      ><a name="8424" href="StlcProp.html#8424" class="Function"
      >example-free&#8322;</a
      ><a name="8437"
      > </a
      ><a name="8438" class="Symbol"
      >:</a
      ><a name="8439"
      > </a
      ><a name="8440" href="Stlc.html#917" class="Function"
      >f</a
      ><a name="8441"
      > </a
      ><a name="8442" href="StlcProp.html#8135" class="Function Operator"
      >&#8713;</a
      ><a name="8443"
      > </a
      ><a name="8444" class="Symbol"
      >(</a
      ><a name="8445" href="Stlc.html#743" class="InductiveConstructor Operator"
      >&#955;[</a
      ><a name="8447"
      > </a
      ><a name="8448" href="Stlc.html#917" class="Function"
      >f</a
      ><a name="8449"
      > </a
      ><a name="8450" href="Stlc.html#743" class="InductiveConstructor Operator"
      >&#8758;</a
      ><a name="8451"
      > </a
      ><a name="8452" class="Symbol"
      >(</a
      ><a name="8453" href="Stlc.html#636" class="InductiveConstructor"
      >&#120121;</a
      ><a name="8454"
      > </a
      ><a name="8455" href="Stlc.html#609" class="InductiveConstructor Operator"
      >&#8658;</a
      ><a name="8456"
      > </a
      ><a name="8457" href="Stlc.html#636" class="InductiveConstructor"
      >&#120121;</a
      ><a name="8458" class="Symbol"
      >)</a
      ><a name="8459"
      > </a
      ><a name="8460" href="Stlc.html#743" class="InductiveConstructor Operator"
      >]</a
      ><a name="8461"
      > </a
      ><a name="8462" href="Stlc.html#727" class="InductiveConstructor"
      >`</a
      ><a name="8463"
      > </a
      ><a name="8464" href="Stlc.html#917" class="Function"
      >f</a
      ><a name="8465"
      > </a
      ><a name="8466" href="Stlc.html#779" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="8467"
      > </a
      ><a name="8468" href="Stlc.html#727" class="InductiveConstructor"
      >`</a
      ><a name="8469"
      > </a
      ><a name="8470" href="Stlc.html#919" class="Function"
      >x</a
      ><a name="8471" class="Symbol"
      >)</a
      ><a name="8472"
      >
</a
      ><a name="8473" href="StlcProp.html#8424" class="Function"
      >example-free&#8322;</a
      ><a name="8486"
      > </a
      ><a name="8487" class="Symbol"
      >(</a
      ><a name="8488" href="StlcProp.html#7717" class="InductiveConstructor"
      >free-&#955;</a
      ><a name="8494"
      > </a
      ><a name="8495" href="StlcProp.html#8495" class="Bound"
      >f&#8802;f</a
      ><a name="8498"
      > </a
      ><a name="8499" class="Symbol"
      >_)</a
      ><a name="8501"
      > </a
      ><a name="8502" class="Symbol"
      >=</a
      ><a name="8503"
      > </a
      ><a name="8504" href="StlcProp.html#8495" class="Bound"
      >f&#8802;f</a
      ><a name="8507"
      > </a
      ><a name="8508" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      >

</pre>


#### Exercise: 1 star (free-in)
Prove formally the remaining examples given above.

<pre class="Agda">

<a name="8623" class="Keyword"
      >postulate</a
      ><a name="8632"
      >
  </a
      ><a name="8635" href="StlcProp.html#8635" class="Postulate"
      >example-free&#8323;</a
      ><a name="8648"
      > </a
      ><a name="8649" class="Symbol"
      >:</a
      ><a name="8650"
      > </a
      ><a name="8651" href="Stlc.html#919" class="Function"
      >x</a
      ><a name="8652"
      > </a
      ><a name="8653" href="StlcProp.html#7659" class="Datatype Operator"
      >&#8712;</a
      ><a name="8654"
      > </a
      ><a name="8655" class="Symbol"
      >((</a
      ><a name="8657" href="Stlc.html#743" class="InductiveConstructor Operator"
      >&#955;[</a
      ><a name="8659"
      > </a
      ><a name="8660" href="Stlc.html#917" class="Function"
      >f</a
      ><a name="8661"
      > </a
      ><a name="8662" href="Stlc.html#743" class="InductiveConstructor Operator"
      >&#8758;</a
      ><a name="8663"
      > </a
      ><a name="8664" class="Symbol"
      >(</a
      ><a name="8665" href="Stlc.html#636" class="InductiveConstructor"
      >&#120121;</a
      ><a name="8666"
      > </a
      ><a name="8667" href="Stlc.html#609" class="InductiveConstructor Operator"
      >&#8658;</a
      ><a name="8668"
      > </a
      ><a name="8669" href="Stlc.html#636" class="InductiveConstructor"
      >&#120121;</a
      ><a name="8670" class="Symbol"
      >)</a
      ><a name="8671"
      > </a
      ><a name="8672" href="Stlc.html#743" class="InductiveConstructor Operator"
      >]</a
      ><a name="8673"
      > </a
      ><a name="8674" href="Stlc.html#727" class="InductiveConstructor"
      >`</a
      ><a name="8675"
      > </a
      ><a name="8676" href="Stlc.html#917" class="Function"
      >f</a
      ><a name="8677"
      > </a
      ><a name="8678" href="Stlc.html#779" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="8679"
      > </a
      ><a name="8680" href="Stlc.html#727" class="InductiveConstructor"
      >`</a
      ><a name="8681"
      > </a
      ><a name="8682" href="Stlc.html#919" class="Function"
      >x</a
      ><a name="8683" class="Symbol"
      >)</a
      ><a name="8684"
      > </a
      ><a name="8685" href="Stlc.html#779" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="8686"
      > </a
      ><a name="8687" href="Stlc.html#727" class="InductiveConstructor"
      >`</a
      ><a name="8688"
      > </a
      ><a name="8689" href="Stlc.html#917" class="Function"
      >f</a
      ><a name="8690" class="Symbol"
      >)</a
      ><a name="8691"
      >
  </a
      ><a name="8694" href="StlcProp.html#8694" class="Postulate"
      >example-free&#8324;</a
      ><a name="8707"
      > </a
      ><a name="8708" class="Symbol"
      >:</a
      ><a name="8709"
      > </a
      ><a name="8710" href="Stlc.html#917" class="Function"
      >f</a
      ><a name="8711"
      > </a
      ><a name="8712" href="StlcProp.html#7659" class="Datatype Operator"
      >&#8712;</a
      ><a name="8713"
      > </a
      ><a name="8714" class="Symbol"
      >((</a
      ><a name="8716" href="Stlc.html#743" class="InductiveConstructor Operator"
      >&#955;[</a
      ><a name="8718"
      > </a
      ><a name="8719" href="Stlc.html#917" class="Function"
      >f</a
      ><a name="8720"
      > </a
      ><a name="8721" href="Stlc.html#743" class="InductiveConstructor Operator"
      >&#8758;</a
      ><a name="8722"
      > </a
      ><a name="8723" class="Symbol"
      >(</a
      ><a name="8724" href="Stlc.html#636" class="InductiveConstructor"
      >&#120121;</a
      ><a name="8725"
      > </a
      ><a name="8726" href="Stlc.html#609" class="InductiveConstructor Operator"
      >&#8658;</a
      ><a name="8727"
      > </a
      ><a name="8728" href="Stlc.html#636" class="InductiveConstructor"
      >&#120121;</a
      ><a name="8729" class="Symbol"
      >)</a
      ><a name="8730"
      > </a
      ><a name="8731" href="Stlc.html#743" class="InductiveConstructor Operator"
      >]</a
      ><a name="8732"
      > </a
      ><a name="8733" href="Stlc.html#727" class="InductiveConstructor"
      >`</a
      ><a name="8734"
      > </a
      ><a name="8735" href="Stlc.html#917" class="Function"
      >f</a
      ><a name="8736"
      > </a
      ><a name="8737" href="Stlc.html#779" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="8738"
      > </a
      ><a name="8739" href="Stlc.html#727" class="InductiveConstructor"
      >`</a
      ><a name="8740"
      > </a
      ><a name="8741" href="Stlc.html#919" class="Function"
      >x</a
      ><a name="8742" class="Symbol"
      >)</a
      ><a name="8743"
      > </a
      ><a name="8744" href="Stlc.html#779" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="8745"
      > </a
      ><a name="8746" href="Stlc.html#727" class="InductiveConstructor"
      >`</a
      ><a name="8747"
      > </a
      ><a name="8748" href="Stlc.html#917" class="Function"
      >f</a
      ><a name="8749" class="Symbol"
      >)</a
      ><a name="8750"
      >
  </a
      ><a name="8753" href="StlcProp.html#8753" class="Postulate"
      >example-free&#8325;</a
      ><a name="8766"
      > </a
      ><a name="8767" class="Symbol"
      >:</a
      ><a name="8768"
      > </a
      ><a name="8769" href="Stlc.html#919" class="Function"
      >x</a
      ><a name="8770"
      > </a
      ><a name="8771" href="StlcProp.html#8135" class="Function Operator"
      >&#8713;</a
      ><a name="8772"
      > </a
      ><a name="8773" class="Symbol"
      >(</a
      ><a name="8774" href="Stlc.html#743" class="InductiveConstructor Operator"
      >&#955;[</a
      ><a name="8776"
      > </a
      ><a name="8777" href="Stlc.html#917" class="Function"
      >f</a
      ><a name="8778"
      > </a
      ><a name="8779" href="Stlc.html#743" class="InductiveConstructor Operator"
      >&#8758;</a
      ><a name="8780"
      > </a
      ><a name="8781" class="Symbol"
      >(</a
      ><a name="8782" href="Stlc.html#636" class="InductiveConstructor"
      >&#120121;</a
      ><a name="8783"
      > </a
      ><a name="8784" href="Stlc.html#609" class="InductiveConstructor Operator"
      >&#8658;</a
      ><a name="8785"
      > </a
      ><a name="8786" href="Stlc.html#636" class="InductiveConstructor"
      >&#120121;</a
      ><a name="8787" class="Symbol"
      >)</a
      ><a name="8788"
      > </a
      ><a name="8789" href="Stlc.html#743" class="InductiveConstructor Operator"
      >]</a
      ><a name="8790"
      > </a
      ><a name="8791" href="Stlc.html#743" class="InductiveConstructor Operator"
      >&#955;[</a
      ><a name="8793"
      > </a
      ><a name="8794" href="Stlc.html#919" class="Function"
      >x</a
      ><a name="8795"
      > </a
      ><a name="8796" href="Stlc.html#743" class="InductiveConstructor Operator"
      >&#8758;</a
      ><a name="8797"
      > </a
      ><a name="8798" href="Stlc.html#636" class="InductiveConstructor"
      >&#120121;</a
      ><a name="8799"
      > </a
      ><a name="8800" href="Stlc.html#743" class="InductiveConstructor Operator"
      >]</a
      ><a name="8801"
      > </a
      ><a name="8802" href="Stlc.html#727" class="InductiveConstructor"
      >`</a
      ><a name="8803"
      > </a
      ><a name="8804" href="Stlc.html#917" class="Function"
      >f</a
      ><a name="8805"
      > </a
      ><a name="8806" href="Stlc.html#779" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="8807"
      > </a
      ><a name="8808" href="Stlc.html#727" class="InductiveConstructor"
      >`</a
      ><a name="8809"
      > </a
      ><a name="8810" href="Stlc.html#919" class="Function"
      >x</a
      ><a name="8811" class="Symbol"
      >)</a
      ><a name="8812"
      >
  </a
      ><a name="8815" href="StlcProp.html#8815" class="Postulate"
      >example-free&#8326;</a
      ><a name="8828"
      > </a
      ><a name="8829" class="Symbol"
      >:</a
      ><a name="8830"
      > </a
      ><a name="8831" href="Stlc.html#917" class="Function"
      >f</a
      ><a name="8832"
      > </a
      ><a name="8833" href="StlcProp.html#8135" class="Function Operator"
      >&#8713;</a
      ><a name="8834"
      > </a
      ><a name="8835" class="Symbol"
      >(</a
      ><a name="8836" href="Stlc.html#743" class="InductiveConstructor Operator"
      >&#955;[</a
      ><a name="8838"
      > </a
      ><a name="8839" href="Stlc.html#917" class="Function"
      >f</a
      ><a name="8840"
      > </a
      ><a name="8841" href="Stlc.html#743" class="InductiveConstructor Operator"
      >&#8758;</a
      ><a name="8842"
      > </a
      ><a name="8843" class="Symbol"
      >(</a
      ><a name="8844" href="Stlc.html#636" class="InductiveConstructor"
      >&#120121;</a
      ><a name="8845"
      > </a
      ><a name="8846" href="Stlc.html#609" class="InductiveConstructor Operator"
      >&#8658;</a
      ><a name="8847"
      > </a
      ><a name="8848" href="Stlc.html#636" class="InductiveConstructor"
      >&#120121;</a
      ><a name="8849" class="Symbol"
      >)</a
      ><a name="8850"
      > </a
      ><a name="8851" href="Stlc.html#743" class="InductiveConstructor Operator"
      >]</a
      ><a name="8852"
      > </a
      ><a name="8853" href="Stlc.html#743" class="InductiveConstructor Operator"
      >&#955;[</a
      ><a name="8855"
      > </a
      ><a name="8856" href="Stlc.html#919" class="Function"
      >x</a
      ><a name="8857"
      > </a
      ><a name="8858" href="Stlc.html#743" class="InductiveConstructor Operator"
      >&#8758;</a
      ><a name="8859"
      > </a
      ><a name="8860" href="Stlc.html#636" class="InductiveConstructor"
      >&#120121;</a
      ><a name="8861"
      > </a
      ><a name="8862" href="Stlc.html#743" class="InductiveConstructor Operator"
      >]</a
      ><a name="8863"
      > </a
      ><a name="8864" href="Stlc.html#727" class="InductiveConstructor"
      >`</a
      ><a name="8865"
      > </a
      ><a name="8866" href="Stlc.html#917" class="Function"
      >f</a
      ><a name="8867"
      > </a
      ><a name="8868" href="Stlc.html#779" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="8869"
      > </a
      ><a name="8870" href="Stlc.html#727" class="InductiveConstructor"
      >`</a
      ><a name="8871"
      > </a
      ><a name="8872" href="Stlc.html#919" class="Function"
      >x</a
      ><a name="8873" class="Symbol"
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

<a name="9356" href="StlcProp.html#9356" class="Function"
      >free-lemma</a
      ><a name="9366"
      > </a
      ><a name="9367" class="Symbol"
      >:</a
      ><a name="9368"
      > </a
      ><a name="9369" class="Symbol"
      >&#8704;</a
      ><a name="9370"
      > </a
      ><a name="9371" class="Symbol"
      >{</a
      ><a name="9372" href="StlcProp.html#9372" class="Bound"
      >x</a
      ><a name="9373"
      > </a
      ><a name="9374" href="StlcProp.html#9374" class="Bound"
      >M</a
      ><a name="9375"
      > </a
      ><a name="9376" href="StlcProp.html#9376" class="Bound"
      >A</a
      ><a name="9377"
      > </a
      ><a name="9378" href="StlcProp.html#9378" class="Bound"
      >&#915;</a
      ><a name="9379" class="Symbol"
      >}</a
      ><a name="9380"
      > </a
      ><a name="9381" class="Symbol"
      >&#8594;</a
      ><a name="9382"
      > </a
      ><a name="9383" href="StlcProp.html#9372" class="Bound"
      >x</a
      ><a name="9384"
      > </a
      ><a name="9385" href="StlcProp.html#7659" class="Datatype Operator"
      >&#8712;</a
      ><a name="9386"
      > </a
      ><a name="9387" href="StlcProp.html#9374" class="Bound"
      >M</a
      ><a name="9388"
      > </a
      ><a name="9389" class="Symbol"
      >&#8594;</a
      ><a name="9390"
      > </a
      ><a name="9391" href="StlcProp.html#9378" class="Bound"
      >&#915;</a
      ><a name="9392"
      > </a
      ><a name="9393" href="Stlc.html#3112" class="Datatype Operator"
      >&#8866;</a
      ><a name="9394"
      > </a
      ><a name="9395" href="StlcProp.html#9374" class="Bound"
      >M</a
      ><a name="9396"
      > </a
      ><a name="9397" href="Stlc.html#3112" class="Datatype Operator"
      >&#8758;</a
      ><a name="9398"
      > </a
      ><a name="9399" href="StlcProp.html#9376" class="Bound"
      >A</a
      ><a name="9400"
      > </a
      ><a name="9401" class="Symbol"
      >&#8594;</a
      ><a name="9402"
      > </a
      ><a name="9403" href="https://agda.github.io/agda-stdlib/Data.Product.html#823" class="Function"
      >&#8707;</a
      ><a name="9404"
      > </a
      ><a name="9405" class="Symbol"
      >&#955;</a
      ><a name="9406"
      > </a
      ><a name="9407" href="StlcProp.html#9407" class="Bound"
      >B</a
      ><a name="9408"
      > </a
      ><a name="9409" class="Symbol"
      >&#8594;</a
      ><a name="9410"
      > </a
      ><a name="9411" href="StlcProp.html#9378" class="Bound"
      >&#915;</a
      ><a name="9412"
      > </a
      ><a name="9413" href="StlcProp.html#9372" class="Bound"
      >x</a
      ><a name="9414"
      > </a
      ><a name="9415" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="9416"
      > </a
      ><a name="9417" href="https://agda.github.io/agda-stdlib/Data.Maybe.Base.html#373" class="InductiveConstructor"
      >just</a
      ><a name="9421"
      > </a
      ><a name="9422" href="StlcProp.html#9407" class="Bound"
      >B</a
      >

</pre>

_Proof_: We show, by induction on the proof that `x` appears
  free in `M`, that, for all contexts `Γ`, if `M` is well
  typed under `Γ`, then `Γ` assigns some type to `x`.

  - If the last rule used was `free-\``, then `M = \` x`, and from
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

<a name="10865" href="StlcProp.html#9356" class="Function"
      >free-lemma</a
      ><a name="10875"
      > </a
      ><a name="10876" href="StlcProp.html#7689" class="InductiveConstructor"
      >free-`</a
      ><a name="10882"
      > </a
      ><a name="10883" class="Symbol"
      >(</a
      ><a name="10884" href="Stlc.html#3156" class="InductiveConstructor"
      >Ax</a
      ><a name="10886"
      > </a
      ><a name="10887" href="StlcProp.html#10887" class="Bound"
      >&#915;x&#8801;A</a
      ><a name="10891" class="Symbol"
      >)</a
      ><a name="10892"
      > </a
      ><a name="10893" class="Symbol"
      >=</a
      ><a name="10894"
      > </a
      ><a name="10895" class="Symbol"
      >(_</a
      ><a name="10897"
      > </a
      ><a name="10898" href="https://agda.github.io/agda-stdlib/Data.Product.html#509" class="InductiveConstructor Operator"
      >,</a
      ><a name="10899"
      > </a
      ><a name="10900" href="StlcProp.html#10887" class="Bound"
      >&#915;x&#8801;A</a
      ><a name="10904" class="Symbol"
      >)</a
      ><a name="10905"
      >
</a
      ><a name="10906" href="StlcProp.html#9356" class="Function"
      >free-lemma</a
      ><a name="10916"
      > </a
      ><a name="10917" class="Symbol"
      >(</a
      ><a name="10918" href="StlcProp.html#7778" class="InductiveConstructor"
      >free-&#183;&#8321;</a
      ><a name="10925"
      > </a
      ><a name="10926" href="StlcProp.html#10926" class="Bound"
      >x&#8712;L</a
      ><a name="10929" class="Symbol"
      >)</a
      ><a name="10930"
      > </a
      ><a name="10931" class="Symbol"
      >(</a
      ><a name="10932" href="Stlc.html#3287" class="InductiveConstructor"
      >&#8658;-E</a
      ><a name="10935"
      > </a
      ><a name="10936" href="StlcProp.html#10936" class="Bound"
      >&#8866;L</a
      ><a name="10938"
      > </a
      ><a name="10939" href="StlcProp.html#10939" class="Bound"
      >&#8866;M</a
      ><a name="10941" class="Symbol"
      >)</a
      ><a name="10942"
      > </a
      ><a name="10943" class="Symbol"
      >=</a
      ><a name="10944"
      > </a
      ><a name="10945" href="StlcProp.html#9356" class="Function"
      >free-lemma</a
      ><a name="10955"
      > </a
      ><a name="10956" href="StlcProp.html#10926" class="Bound"
      >x&#8712;L</a
      ><a name="10959"
      > </a
      ><a name="10960" href="StlcProp.html#10936" class="Bound"
      >&#8866;L</a
      ><a name="10962"
      >
</a
      ><a name="10963" href="StlcProp.html#9356" class="Function"
      >free-lemma</a
      ><a name="10973"
      > </a
      ><a name="10974" class="Symbol"
      >(</a
      ><a name="10975" href="StlcProp.html#7822" class="InductiveConstructor"
      >free-&#183;&#8322;</a
      ><a name="10982"
      > </a
      ><a name="10983" href="StlcProp.html#10983" class="Bound"
      >x&#8712;M</a
      ><a name="10986" class="Symbol"
      >)</a
      ><a name="10987"
      > </a
      ><a name="10988" class="Symbol"
      >(</a
      ><a name="10989" href="Stlc.html#3287" class="InductiveConstructor"
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
      ><a name="11002" href="StlcProp.html#9356" class="Function"
      >free-lemma</a
      ><a name="11012"
      > </a
      ><a name="11013" href="StlcProp.html#10983" class="Bound"
      >x&#8712;M</a
      ><a name="11016"
      > </a
      ><a name="11017" href="StlcProp.html#10996" class="Bound"
      >&#8866;M</a
      ><a name="11019"
      >
</a
      ><a name="11020" href="StlcProp.html#9356" class="Function"
      >free-lemma</a
      ><a name="11030"
      > </a
      ><a name="11031" class="Symbol"
      >(</a
      ><a name="11032" href="StlcProp.html#7866" class="InductiveConstructor"
      >free-if&#8321;</a
      ><a name="11040"
      > </a
      ><a name="11041" href="StlcProp.html#11041" class="Bound"
      >x&#8712;L</a
      ><a name="11044" class="Symbol"
      >)</a
      ><a name="11045"
      > </a
      ><a name="11046" class="Symbol"
      >(</a
      ><a name="11047" href="Stlc.html#3434" class="InductiveConstructor"
      >&#120121;-E</a
      ><a name="11050"
      > </a
      ><a name="11051" href="StlcProp.html#11051" class="Bound"
      >&#8866;L</a
      ><a name="11053"
      > </a
      ><a name="11054" href="StlcProp.html#11054" class="Bound"
      >&#8866;M</a
      ><a name="11056"
      > </a
      ><a name="11057" href="StlcProp.html#11057" class="Bound"
      >&#8866;N</a
      ><a name="11059" class="Symbol"
      >)</a
      ><a name="11060"
      > </a
      ><a name="11061" class="Symbol"
      >=</a
      ><a name="11062"
      > </a
      ><a name="11063" href="StlcProp.html#9356" class="Function"
      >free-lemma</a
      ><a name="11073"
      > </a
      ><a name="11074" href="StlcProp.html#11041" class="Bound"
      >x&#8712;L</a
      ><a name="11077"
      > </a
      ><a name="11078" href="StlcProp.html#11051" class="Bound"
      >&#8866;L</a
      ><a name="11080"
      >
</a
      ><a name="11081" href="StlcProp.html#9356" class="Function"
      >free-lemma</a
      ><a name="11091"
      > </a
      ><a name="11092" class="Symbol"
      >(</a
      ><a name="11093" href="StlcProp.html#7926" class="InductiveConstructor"
      >free-if&#8322;</a
      ><a name="11101"
      > </a
      ><a name="11102" href="StlcProp.html#11102" class="Bound"
      >x&#8712;M</a
      ><a name="11105" class="Symbol"
      >)</a
      ><a name="11106"
      > </a
      ><a name="11107" class="Symbol"
      >(</a
      ><a name="11108" href="Stlc.html#3434" class="InductiveConstructor"
      >&#120121;-E</a
      ><a name="11111"
      > </a
      ><a name="11112" href="StlcProp.html#11112" class="Bound"
      >&#8866;L</a
      ><a name="11114"
      > </a
      ><a name="11115" href="StlcProp.html#11115" class="Bound"
      >&#8866;M</a
      ><a name="11117"
      > </a
      ><a name="11118" href="StlcProp.html#11118" class="Bound"
      >&#8866;N</a
      ><a name="11120" class="Symbol"
      >)</a
      ><a name="11121"
      > </a
      ><a name="11122" class="Symbol"
      >=</a
      ><a name="11123"
      > </a
      ><a name="11124" href="StlcProp.html#9356" class="Function"
      >free-lemma</a
      ><a name="11134"
      > </a
      ><a name="11135" href="StlcProp.html#11102" class="Bound"
      >x&#8712;M</a
      ><a name="11138"
      > </a
      ><a name="11139" href="StlcProp.html#11115" class="Bound"
      >&#8866;M</a
      ><a name="11141"
      >
</a
      ><a name="11142" href="StlcProp.html#9356" class="Function"
      >free-lemma</a
      ><a name="11152"
      > </a
      ><a name="11153" class="Symbol"
      >(</a
      ><a name="11154" href="StlcProp.html#7986" class="InductiveConstructor"
      >free-if&#8323;</a
      ><a name="11162"
      > </a
      ><a name="11163" href="StlcProp.html#11163" class="Bound"
      >x&#8712;N</a
      ><a name="11166" class="Symbol"
      >)</a
      ><a name="11167"
      > </a
      ><a name="11168" class="Symbol"
      >(</a
      ><a name="11169" href="Stlc.html#3434" class="InductiveConstructor"
      >&#120121;-E</a
      ><a name="11172"
      > </a
      ><a name="11173" href="StlcProp.html#11173" class="Bound"
      >&#8866;L</a
      ><a name="11175"
      > </a
      ><a name="11176" href="StlcProp.html#11176" class="Bound"
      >&#8866;M</a
      ><a name="11178"
      > </a
      ><a name="11179" href="StlcProp.html#11179" class="Bound"
      >&#8866;N</a
      ><a name="11181" class="Symbol"
      >)</a
      ><a name="11182"
      > </a
      ><a name="11183" class="Symbol"
      >=</a
      ><a name="11184"
      > </a
      ><a name="11185" href="StlcProp.html#9356" class="Function"
      >free-lemma</a
      ><a name="11195"
      > </a
      ><a name="11196" href="StlcProp.html#11163" class="Bound"
      >x&#8712;N</a
      ><a name="11199"
      > </a
      ><a name="11200" href="StlcProp.html#11179" class="Bound"
      >&#8866;N</a
      ><a name="11202"
      >
</a
      ><a name="11203" href="StlcProp.html#9356" class="Function"
      >free-lemma</a
      ><a name="11213"
      > </a
      ><a name="11214" class="Symbol"
      >(</a
      ><a name="11215" href="StlcProp.html#7717" class="InductiveConstructor"
      >free-&#955;</a
      ><a name="11221"
      > </a
      ><a name="11222" class="Symbol"
      >{</a
      ><a name="11223" href="StlcProp.html#11223" class="Bound"
      >x</a
      ><a name="11224" class="Symbol"
      >}</a
      ><a name="11225"
      > </a
      ><a name="11226" class="Symbol"
      >{</a
      ><a name="11227" href="StlcProp.html#11227" class="Bound"
      >y</a
      ><a name="11228" class="Symbol"
      >}</a
      ><a name="11229"
      > </a
      ><a name="11230" href="StlcProp.html#11230" class="Bound"
      >y&#8802;x</a
      ><a name="11233"
      > </a
      ><a name="11234" href="StlcProp.html#11234" class="Bound"
      >x&#8712;N</a
      ><a name="11237" class="Symbol"
      >)</a
      ><a name="11238"
      > </a
      ><a name="11239" class="Symbol"
      >(</a
      ><a name="11240" href="Stlc.html#3210" class="InductiveConstructor"
      >&#8658;-I</a
      ><a name="11243"
      > </a
      ><a name="11244" href="StlcProp.html#11244" class="Bound"
      >&#8866;N</a
      ><a name="11246" class="Symbol"
      >)</a
      ><a name="11247"
      > </a
      ><a name="11248" class="Keyword"
      >with</a
      ><a name="11252"
      > </a
      ><a name="11253" href="StlcProp.html#9356" class="Function"
      >free-lemma</a
      ><a name="11263"
      > </a
      ><a name="11264" href="StlcProp.html#11234" class="Bound"
      >x&#8712;N</a
      ><a name="11267"
      > </a
      ><a name="11268" href="StlcProp.html#11244" class="Bound"
      >&#8866;N</a
      ><a name="11270"
      >
</a
      ><a name="11271" class="Symbol"
      >...</a
      ><a name="11274"
      > </a
      ><a name="11275" class="Symbol"
      >|</a
      ><a name="11276"
      > </a
      ><a name="11277" href="StlcProp.html#11277" class="Bound"
      >&#915;x&#8801;C</a
      ><a name="11281"
      > </a
      ><a name="11282" class="Keyword"
      >with</a
      ><a name="11286"
      > </a
      ><a name="11287" href="StlcProp.html#11227" class="Bound"
      >y</a
      ><a name="11288"
      > </a
      ><a name="11289" href="Maps.html#2509" class="Function Operator"
      >&#8799;</a
      ><a name="11290"
      > </a
      ><a name="11291" href="StlcProp.html#11223" class="Bound"
      >x</a
      ><a name="11292"
      >
</a
      ><a name="11293" class="Symbol"
      >...</a
      ><a name="11296"
      > </a
      ><a name="11297" class="Symbol"
      >|</a
      ><a name="11298"
      > </a
      ><a name="11299" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#520" class="InductiveConstructor"
      >yes</a
      ><a name="11302"
      > </a
      ><a name="11303" href="StlcProp.html#11303" class="Bound"
      >y&#8801;x</a
      ><a name="11306"
      > </a
      ><a name="11307" class="Symbol"
      >=</a
      ><a name="11308"
      > </a
      ><a name="11309" href="https://agda.github.io/agda-stdlib/Data.Empty.html#348" class="Function"
      >&#8869;-elim</a
      ><a name="11315"
      > </a
      ><a name="11316" class="Symbol"
      >(</a
      ><a name="11317" href="StlcProp.html#11230" class="Bound"
      >y&#8802;x</a
      ><a name="11320"
      > </a
      ><a name="11321" href="StlcProp.html#11303" class="Bound"
      >y&#8801;x</a
      ><a name="11324" class="Symbol"
      >)</a
      ><a name="11325"
      >
</a
      ><a name="11326" class="Symbol"
      >...</a
      ><a name="11329"
      > </a
      ><a name="11330" class="Symbol"
      >|</a
      ><a name="11331"
      > </a
      ><a name="11332" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#547" class="InductiveConstructor"
      >no</a
      ><a name="11334"
      >  </a
      ><a name="11336" class="Symbol"
      >_</a
      ><a name="11337"
      >   </a
      ><a name="11340" class="Symbol"
      >=</a
      ><a name="11341"
      > </a
      ><a name="11342" href="StlcProp.html#11277" class="Bound"
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

<a name="11779" class="Keyword"
      >postulate</a
      ><a name="11788"
      >
  </a
      ><a name="11791" href="StlcProp.html#11791" class="Postulate"
      >&#8709;&#8866;-closed</a
      ><a name="11800"
      > </a
      ><a name="11801" class="Symbol"
      >:</a
      ><a name="11802"
      > </a
      ><a name="11803" class="Symbol"
      >&#8704;</a
      ><a name="11804"
      > </a
      ><a name="11805" class="Symbol"
      >{</a
      ><a name="11806" href="StlcProp.html#11806" class="Bound"
      >M</a
      ><a name="11807"
      > </a
      ><a name="11808" href="StlcProp.html#11808" class="Bound"
      >A</a
      ><a name="11809" class="Symbol"
      >}</a
      ><a name="11810"
      > </a
      ><a name="11811" class="Symbol"
      >&#8594;</a
      ><a name="11812"
      > </a
      ><a name="11813" href="Maps.html#10265" class="Function"
      >&#8709;</a
      ><a name="11814"
      > </a
      ><a name="11815" href="Stlc.html#3112" class="Datatype Operator"
      >&#8866;</a
      ><a name="11816"
      > </a
      ><a name="11817" href="StlcProp.html#11806" class="Bound"
      >M</a
      ><a name="11818"
      > </a
      ><a name="11819" href="Stlc.html#3112" class="Datatype Operator"
      >&#8758;</a
      ><a name="11820"
      > </a
      ><a name="11821" href="StlcProp.html#11808" class="Bound"
      >A</a
      ><a name="11822"
      > </a
      ><a name="11823" class="Symbol"
      >&#8594;</a
      ><a name="11824"
      > </a
      ><a name="11825" href="StlcProp.html#8176" class="Function"
      >closed</a
      ><a name="11831"
      > </a
      ><a name="11832" href="StlcProp.html#11806" class="Bound"
      >M</a
      >

</pre>

<div class="hidden">
<pre class="Agda">

<a name="11880" href="StlcProp.html#11880" class="Function"
      >contradiction</a
      ><a name="11893"
      > </a
      ><a name="11894" class="Symbol"
      >:</a
      ><a name="11895"
      > </a
      ><a name="11896" class="Symbol"
      >&#8704;</a
      ><a name="11897"
      > </a
      ><a name="11898" class="Symbol"
      >{</a
      ><a name="11899" href="StlcProp.html#11899" class="Bound"
      >X</a
      ><a name="11900"
      > </a
      ><a name="11901" class="Symbol"
      >:</a
      ><a name="11902"
      > </a
      ><a name="11903" class="PrimitiveType"
      >Set</a
      ><a name="11906" class="Symbol"
      >}</a
      ><a name="11907"
      > </a
      ><a name="11908" class="Symbol"
      >&#8594;</a
      ><a name="11909"
      > </a
      ><a name="11910" class="Symbol"
      >&#8704;</a
      ><a name="11911"
      > </a
      ><a name="11912" class="Symbol"
      >{</a
      ><a name="11913" href="StlcProp.html#11913" class="Bound"
      >x</a
      ><a name="11914"
      > </a
      ><a name="11915" class="Symbol"
      >:</a
      ><a name="11916"
      > </a
      ><a name="11917" href="StlcProp.html#11899" class="Bound"
      >X</a
      ><a name="11918" class="Symbol"
      >}</a
      ><a name="11919"
      > </a
      ><a name="11920" class="Symbol"
      >&#8594;</a
      ><a name="11921"
      > </a
      ><a name="11922" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#414" class="Function Operator"
      >&#172;</a
      ><a name="11923"
      > </a
      ><a name="11924" class="Symbol"
      >(</a
      ><a name="11925" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >_&#8801;_</a
      ><a name="11928"
      > </a
      ><a name="11929" class="Symbol"
      >{</a
      ><a name="11930" class="Argument"
      >A</a
      ><a name="11931"
      > </a
      ><a name="11932" class="Symbol"
      >=</a
      ><a name="11933"
      > </a
      ><a name="11934" href="https://agda.github.io/agda-stdlib/Data.Maybe.Base.html#335" class="Datatype"
      >Maybe</a
      ><a name="11939"
      > </a
      ><a name="11940" href="StlcProp.html#11899" class="Bound"
      >X</a
      ><a name="11941" class="Symbol"
      >}</a
      ><a name="11942"
      > </a
      ><a name="11943" class="Symbol"
      >(</a
      ><a name="11944" href="https://agda.github.io/agda-stdlib/Data.Maybe.Base.html#373" class="InductiveConstructor"
      >just</a
      ><a name="11948"
      > </a
      ><a name="11949" href="StlcProp.html#11913" class="Bound"
      >x</a
      ><a name="11950" class="Symbol"
      >)</a
      ><a name="11951"
      > </a
      ><a name="11952" href="https://agda.github.io/agda-stdlib/Data.Maybe.Base.html#403" class="InductiveConstructor"
      >nothing</a
      ><a name="11959" class="Symbol"
      >)</a
      ><a name="11960"
      >
</a
      ><a name="11961" href="StlcProp.html#11880" class="Function"
      >contradiction</a
      ><a name="11974"
      > </a
      ><a name="11975" class="Symbol"
      >()</a
      ><a name="11977"
      >

</a
      ><a name="11979" href="StlcProp.html#11979" class="Function"
      >&#8709;&#8866;-closed&#8242;</a
      ><a name="11989"
      > </a
      ><a name="11990" class="Symbol"
      >:</a
      ><a name="11991"
      > </a
      ><a name="11992" class="Symbol"
      >&#8704;</a
      ><a name="11993"
      > </a
      ><a name="11994" class="Symbol"
      >{</a
      ><a name="11995" href="StlcProp.html#11995" class="Bound"
      >M</a
      ><a name="11996"
      > </a
      ><a name="11997" href="StlcProp.html#11997" class="Bound"
      >A</a
      ><a name="11998" class="Symbol"
      >}</a
      ><a name="11999"
      > </a
      ><a name="12000" class="Symbol"
      >&#8594;</a
      ><a name="12001"
      > </a
      ><a name="12002" href="Maps.html#10265" class="Function"
      >&#8709;</a
      ><a name="12003"
      > </a
      ><a name="12004" href="Stlc.html#3112" class="Datatype Operator"
      >&#8866;</a
      ><a name="12005"
      > </a
      ><a name="12006" href="StlcProp.html#11995" class="Bound"
      >M</a
      ><a name="12007"
      > </a
      ><a name="12008" href="Stlc.html#3112" class="Datatype Operator"
      >&#8758;</a
      ><a name="12009"
      > </a
      ><a name="12010" href="StlcProp.html#11997" class="Bound"
      >A</a
      ><a name="12011"
      > </a
      ><a name="12012" class="Symbol"
      >&#8594;</a
      ><a name="12013"
      > </a
      ><a name="12014" href="StlcProp.html#8176" class="Function"
      >closed</a
      ><a name="12020"
      > </a
      ><a name="12021" href="StlcProp.html#11995" class="Bound"
      >M</a
      ><a name="12022"
      >
</a
      ><a name="12023" href="StlcProp.html#11979" class="Function"
      >&#8709;&#8866;-closed&#8242;</a
      ><a name="12033"
      > </a
      ><a name="12034" class="Symbol"
      >{</a
      ><a name="12035" href="StlcProp.html#12035" class="Bound"
      >M</a
      ><a name="12036" class="Symbol"
      >}</a
      ><a name="12037"
      > </a
      ><a name="12038" class="Symbol"
      >{</a
      ><a name="12039" href="StlcProp.html#12039" class="Bound"
      >A</a
      ><a name="12040" class="Symbol"
      >}</a
      ><a name="12041"
      > </a
      ><a name="12042" href="StlcProp.html#12042" class="Bound"
      >&#8866;M</a
      ><a name="12044"
      > </a
      ><a name="12045" class="Symbol"
      >{</a
      ><a name="12046" href="StlcProp.html#12046" class="Bound"
      >x</a
      ><a name="12047" class="Symbol"
      >}</a
      ><a name="12048"
      > </a
      ><a name="12049" href="StlcProp.html#12049" class="Bound"
      >x&#8712;M</a
      ><a name="12052"
      > </a
      ><a name="12053" class="Keyword"
      >with</a
      ><a name="12057"
      > </a
      ><a name="12058" href="StlcProp.html#9356" class="Function"
      >free-lemma</a
      ><a name="12068"
      > </a
      ><a name="12069" href="StlcProp.html#12049" class="Bound"
      >x&#8712;M</a
      ><a name="12072"
      > </a
      ><a name="12073" href="StlcProp.html#12042" class="Bound"
      >&#8866;M</a
      ><a name="12075"
      >
</a
      ><a name="12076" class="Symbol"
      >...</a
      ><a name="12079"
      > </a
      ><a name="12080" class="Symbol"
      >|</a
      ><a name="12081"
      > </a
      ><a name="12082" class="Symbol"
      >(</a
      ><a name="12083" href="StlcProp.html#12083" class="Bound"
      >B</a
      ><a name="12084"
      > </a
      ><a name="12085" href="https://agda.github.io/agda-stdlib/Data.Product.html#509" class="InductiveConstructor Operator"
      >,</a
      ><a name="12086"
      > </a
      ><a name="12087" href="StlcProp.html#12087" class="Bound"
      >&#8709;x&#8801;B</a
      ><a name="12091" class="Symbol"
      >)</a
      ><a name="12092"
      > </a
      ><a name="12093" class="Symbol"
      >=</a
      ><a name="12094"
      > </a
      ><a name="12095" href="StlcProp.html#11880" class="Function"
      >contradiction</a
      ><a name="12108"
      > </a
      ><a name="12109" class="Symbol"
      >(</a
      ><a name="12110" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.Core.html#632" class="Function"
      >trans</a
      ><a name="12115"
      > </a
      ><a name="12116" class="Symbol"
      >(</a
      ><a name="12117" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.Core.html#565" class="Function"
      >sym</a
      ><a name="12120"
      > </a
      ><a name="12121" href="StlcProp.html#12087" class="Bound"
      >&#8709;x&#8801;B</a
      ><a name="12125" class="Symbol"
      >)</a
      ><a name="12126"
      > </a
      ><a name="12127" class="Symbol"
      >(</a
      ><a name="12128" href="Maps.html#10573" class="Function"
      >apply-&#8709;</a
      ><a name="12135"
      > </a
      ><a name="12136" href="StlcProp.html#12046" class="Bound"
      >x</a
      ><a name="12137" class="Symbol"
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

<a name="12491" href="StlcProp.html#12491" class="Function"
      >context-lemma</a
      ><a name="12504"
      > </a
      ><a name="12505" class="Symbol"
      >:</a
      ><a name="12506"
      > </a
      ><a name="12507" class="Symbol"
      >&#8704;</a
      ><a name="12508"
      > </a
      ><a name="12509" class="Symbol"
      >{</a
      ><a name="12510" href="StlcProp.html#12510" class="Bound"
      >&#915;</a
      ><a name="12511"
      > </a
      ><a name="12512" href="StlcProp.html#12512" class="Bound"
      >&#915;&#8242;</a
      ><a name="12514"
      > </a
      ><a name="12515" href="StlcProp.html#12515" class="Bound"
      >M</a
      ><a name="12516"
      > </a
      ><a name="12517" href="StlcProp.html#12517" class="Bound"
      >A</a
      ><a name="12518" class="Symbol"
      >}</a
      ><a name="12519"
      >
        </a
      ><a name="12528" class="Symbol"
      >&#8594;</a
      ><a name="12529"
      > </a
      ><a name="12530" class="Symbol"
      >(&#8704;</a
      ><a name="12532"
      > </a
      ><a name="12533" class="Symbol"
      >{</a
      ><a name="12534" href="StlcProp.html#12534" class="Bound"
      >x</a
      ><a name="12535" class="Symbol"
      >}</a
      ><a name="12536"
      > </a
      ><a name="12537" class="Symbol"
      >&#8594;</a
      ><a name="12538"
      > </a
      ><a name="12539" href="StlcProp.html#12534" class="Bound"
      >x</a
      ><a name="12540"
      > </a
      ><a name="12541" href="StlcProp.html#7659" class="Datatype Operator"
      >&#8712;</a
      ><a name="12542"
      > </a
      ><a name="12543" href="StlcProp.html#12515" class="Bound"
      >M</a
      ><a name="12544"
      > </a
      ><a name="12545" class="Symbol"
      >&#8594;</a
      ><a name="12546"
      > </a
      ><a name="12547" href="StlcProp.html#12510" class="Bound"
      >&#915;</a
      ><a name="12548"
      > </a
      ><a name="12549" href="StlcProp.html#12534" class="Bound"
      >x</a
      ><a name="12550"
      > </a
      ><a name="12551" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="12552"
      > </a
      ><a name="12553" href="StlcProp.html#12512" class="Bound"
      >&#915;&#8242;</a
      ><a name="12555"
      > </a
      ><a name="12556" href="StlcProp.html#12534" class="Bound"
      >x</a
      ><a name="12557" class="Symbol"
      >)</a
      ><a name="12558"
      >
        </a
      ><a name="12567" class="Symbol"
      >&#8594;</a
      ><a name="12568"
      > </a
      ><a name="12569" href="StlcProp.html#12510" class="Bound"
      >&#915;</a
      ><a name="12570"
      >  </a
      ><a name="12572" href="Stlc.html#3112" class="Datatype Operator"
      >&#8866;</a
      ><a name="12573"
      > </a
      ><a name="12574" href="StlcProp.html#12515" class="Bound"
      >M</a
      ><a name="12575"
      > </a
      ><a name="12576" href="Stlc.html#3112" class="Datatype Operator"
      >&#8758;</a
      ><a name="12577"
      > </a
      ><a name="12578" href="StlcProp.html#12517" class="Bound"
      >A</a
      ><a name="12579"
      >
        </a
      ><a name="12588" class="Symbol"
      >&#8594;</a
      ><a name="12589"
      > </a
      ><a name="12590" href="StlcProp.html#12512" class="Bound"
      >&#915;&#8242;</a
      ><a name="12592"
      > </a
      ><a name="12593" href="Stlc.html#3112" class="Datatype Operator"
      >&#8866;</a
      ><a name="12594"
      > </a
      ><a name="12595" href="StlcProp.html#12515" class="Bound"
      >M</a
      ><a name="12596"
      > </a
      ><a name="12597" href="Stlc.html#3112" class="Datatype Operator"
      >&#8758;</a
      ><a name="12598"
      > </a
      ><a name="12599" href="StlcProp.html#12517" class="Bound"
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

<a name="14772" href="StlcProp.html#12491" class="Function"
      >context-lemma</a
      ><a name="14785"
      > </a
      ><a name="14786" href="StlcProp.html#14786" class="Bound"
      >&#915;~&#915;&#8242;</a
      ><a name="14790"
      > </a
      ><a name="14791" class="Symbol"
      >(</a
      ><a name="14792" href="Stlc.html#3156" class="InductiveConstructor"
      >Ax</a
      ><a name="14794"
      > </a
      ><a name="14795" href="StlcProp.html#14795" class="Bound"
      >&#915;x&#8801;A</a
      ><a name="14799" class="Symbol"
      >)</a
      ><a name="14800"
      > </a
      ><a name="14801" class="Keyword"
      >rewrite</a
      ><a name="14808"
      > </a
      ><a name="14809" class="Symbol"
      >(</a
      ><a name="14810" href="StlcProp.html#14786" class="Bound"
      >&#915;~&#915;&#8242;</a
      ><a name="14814"
      > </a
      ><a name="14815" href="StlcProp.html#7689" class="InductiveConstructor"
      >free-`</a
      ><a name="14821" class="Symbol"
      >)</a
      ><a name="14822"
      > </a
      ><a name="14823" class="Symbol"
      >=</a
      ><a name="14824"
      > </a
      ><a name="14825" href="Stlc.html#3156" class="InductiveConstructor"
      >Ax</a
      ><a name="14827"
      > </a
      ><a name="14828" href="StlcProp.html#14795" class="Bound"
      >&#915;x&#8801;A</a
      ><a name="14832"
      >
</a
      ><a name="14833" href="StlcProp.html#12491" class="Function"
      >context-lemma</a
      ><a name="14846"
      > </a
      ><a name="14847" class="Symbol"
      >{</a
      ><a name="14848" href="StlcProp.html#14848" class="Bound"
      >&#915;</a
      ><a name="14849" class="Symbol"
      >}</a
      ><a name="14850"
      > </a
      ><a name="14851" class="Symbol"
      >{</a
      ><a name="14852" href="StlcProp.html#14852" class="Bound"
      >&#915;&#8242;</a
      ><a name="14854" class="Symbol"
      >}</a
      ><a name="14855"
      > </a
      ><a name="14856" class="Symbol"
      >{</a
      ><a name="14857" href="Stlc.html#743" class="InductiveConstructor Operator"
      >&#955;[</a
      ><a name="14859"
      > </a
      ><a name="14860" href="StlcProp.html#14860" class="Bound"
      >x</a
      ><a name="14861"
      > </a
      ><a name="14862" href="Stlc.html#743" class="InductiveConstructor Operator"
      >&#8758;</a
      ><a name="14863"
      > </a
      ><a name="14864" href="StlcProp.html#14864" class="Bound"
      >A</a
      ><a name="14865"
      > </a
      ><a name="14866" href="Stlc.html#743" class="InductiveConstructor Operator"
      >]</a
      ><a name="14867"
      > </a
      ><a name="14868" href="StlcProp.html#14868" class="Bound"
      >N</a
      ><a name="14869" class="Symbol"
      >}</a
      ><a name="14870"
      > </a
      ><a name="14871" href="StlcProp.html#14871" class="Bound"
      >&#915;~&#915;&#8242;</a
      ><a name="14875"
      > </a
      ><a name="14876" class="Symbol"
      >(</a
      ><a name="14877" href="Stlc.html#3210" class="InductiveConstructor"
      >&#8658;-I</a
      ><a name="14880"
      > </a
      ><a name="14881" href="StlcProp.html#14881" class="Bound"
      >&#8866;N</a
      ><a name="14883" class="Symbol"
      >)</a
      ><a name="14884"
      > </a
      ><a name="14885" class="Symbol"
      >=</a
      ><a name="14886"
      > </a
      ><a name="14887" href="Stlc.html#3210" class="InductiveConstructor"
      >&#8658;-I</a
      ><a name="14890"
      > </a
      ><a name="14891" class="Symbol"
      >(</a
      ><a name="14892" href="StlcProp.html#12491" class="Function"
      >context-lemma</a
      ><a name="14905"
      > </a
      ><a name="14906" href="StlcProp.html#14927" class="Function"
      >&#915;x~&#915;&#8242;x</a
      ><a name="14912"
      > </a
      ><a name="14913" href="StlcProp.html#14881" class="Bound"
      >&#8866;N</a
      ><a name="14915" class="Symbol"
      >)</a
      ><a name="14916"
      >
  </a
      ><a name="14919" class="Keyword"
      >where</a
      ><a name="14924"
      >
  </a
      ><a name="14927" href="StlcProp.html#14927" class="Function"
      >&#915;x~&#915;&#8242;x</a
      ><a name="14933"
      > </a
      ><a name="14934" class="Symbol"
      >:</a
      ><a name="14935"
      > </a
      ><a name="14936" class="Symbol"
      >&#8704;</a
      ><a name="14937"
      > </a
      ><a name="14938" class="Symbol"
      >{</a
      ><a name="14939" href="StlcProp.html#14939" class="Bound"
      >y</a
      ><a name="14940" class="Symbol"
      >}</a
      ><a name="14941"
      > </a
      ><a name="14942" class="Symbol"
      >&#8594;</a
      ><a name="14943"
      > </a
      ><a name="14944" href="StlcProp.html#14939" class="Bound"
      >y</a
      ><a name="14945"
      > </a
      ><a name="14946" href="StlcProp.html#7659" class="Datatype Operator"
      >&#8712;</a
      ><a name="14947"
      > </a
      ><a name="14948" href="StlcProp.html#14868" class="Bound"
      >N</a
      ><a name="14949"
      > </a
      ><a name="14950" class="Symbol"
      >&#8594;</a
      ><a name="14951"
      > </a
      ><a name="14952" class="Symbol"
      >(</a
      ><a name="14953" href="StlcProp.html#14848" class="Bound"
      >&#915;</a
      ><a name="14954"
      > </a
      ><a name="14955" href="Maps.html#10368" class="Function Operator"
      >,</a
      ><a name="14956"
      > </a
      ><a name="14957" href="StlcProp.html#14860" class="Bound"
      >x</a
      ><a name="14958"
      > </a
      ><a name="14959" href="Maps.html#10368" class="Function Operator"
      >&#8758;</a
      ><a name="14960"
      > </a
      ><a name="14961" href="StlcProp.html#14864" class="Bound"
      >A</a
      ><a name="14962" class="Symbol"
      >)</a
      ><a name="14963"
      > </a
      ><a name="14964" href="StlcProp.html#14939" class="Bound"
      >y</a
      ><a name="14965"
      > </a
      ><a name="14966" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="14967"
      > </a
      ><a name="14968" class="Symbol"
      >(</a
      ><a name="14969" href="StlcProp.html#14852" class="Bound"
      >&#915;&#8242;</a
      ><a name="14971"
      > </a
      ><a name="14972" href="Maps.html#10368" class="Function Operator"
      >,</a
      ><a name="14973"
      > </a
      ><a name="14974" href="StlcProp.html#14860" class="Bound"
      >x</a
      ><a name="14975"
      > </a
      ><a name="14976" href="Maps.html#10368" class="Function Operator"
      >&#8758;</a
      ><a name="14977"
      > </a
      ><a name="14978" href="StlcProp.html#14864" class="Bound"
      >A</a
      ><a name="14979" class="Symbol"
      >)</a
      ><a name="14980"
      > </a
      ><a name="14981" href="StlcProp.html#14939" class="Bound"
      >y</a
      ><a name="14982"
      >
  </a
      ><a name="14985" href="StlcProp.html#14927" class="Function"
      >&#915;x~&#915;&#8242;x</a
      ><a name="14991"
      > </a
      ><a name="14992" class="Symbol"
      >{</a
      ><a name="14993" href="StlcProp.html#14993" class="Bound"
      >y</a
      ><a name="14994" class="Symbol"
      >}</a
      ><a name="14995"
      > </a
      ><a name="14996" href="StlcProp.html#14996" class="Bound"
      >y&#8712;N</a
      ><a name="14999"
      > </a
      ><a name="15000" class="Keyword"
      >with</a
      ><a name="15004"
      > </a
      ><a name="15005" href="StlcProp.html#14860" class="Bound"
      >x</a
      ><a name="15006"
      > </a
      ><a name="15007" href="Maps.html#2509" class="Function Operator"
      >&#8799;</a
      ><a name="15008"
      > </a
      ><a name="15009" href="StlcProp.html#14993" class="Bound"
      >y</a
      ><a name="15010"
      >
  </a
      ><a name="15013" class="Symbol"
      >...</a
      ><a name="15016"
      > </a
      ><a name="15017" class="Symbol"
      >|</a
      ><a name="15018"
      > </a
      ><a name="15019" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#520" class="InductiveConstructor"
      >yes</a
      ><a name="15022"
      > </a
      ><a name="15023" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="15027"
      > </a
      ><a name="15028" class="Symbol"
      >=</a
      ><a name="15029"
      > </a
      ><a name="15030" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="15034"
      >
  </a
      ><a name="15037" class="Symbol"
      >...</a
      ><a name="15040"
      > </a
      ><a name="15041" class="Symbol"
      >|</a
      ><a name="15042"
      > </a
      ><a name="15043" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#547" class="InductiveConstructor"
      >no</a
      ><a name="15045"
      >  </a
      ><a name="15047" href="StlcProp.html#15047" class="Bound"
      >x&#8802;y</a
      ><a name="15050"
      >  </a
      ><a name="15052" class="Symbol"
      >=</a
      ><a name="15053"
      > </a
      ><a name="15054" href="StlcProp.html#14871" class="Bound"
      >&#915;~&#915;&#8242;</a
      ><a name="15058"
      > </a
      ><a name="15059" class="Symbol"
      >(</a
      ><a name="15060" href="StlcProp.html#7717" class="InductiveConstructor"
      >free-&#955;</a
      ><a name="15066"
      > </a
      ><a name="15067" href="StlcProp.html#15047" class="Bound"
      >x&#8802;y</a
      ><a name="15070"
      > </a
      ><a name="15071" href="StlcProp.html#14996" class="Bound"
      >y&#8712;N</a
      ><a name="15074" class="Symbol"
      >)</a
      ><a name="15075"
      >
</a
      ><a name="15076" href="StlcProp.html#12491" class="Function"
      >context-lemma</a
      ><a name="15089"
      > </a
      ><a name="15090" href="StlcProp.html#15090" class="Bound"
      >&#915;~&#915;&#8242;</a
      ><a name="15094"
      > </a
      ><a name="15095" class="Symbol"
      >(</a
      ><a name="15096" href="Stlc.html#3287" class="InductiveConstructor"
      >&#8658;-E</a
      ><a name="15099"
      > </a
      ><a name="15100" href="StlcProp.html#15100" class="Bound"
      >&#8866;L</a
      ><a name="15102"
      > </a
      ><a name="15103" href="StlcProp.html#15103" class="Bound"
      >&#8866;M</a
      ><a name="15105" class="Symbol"
      >)</a
      ><a name="15106"
      > </a
      ><a name="15107" class="Symbol"
      >=</a
      ><a name="15108"
      > </a
      ><a name="15109" href="Stlc.html#3287" class="InductiveConstructor"
      >&#8658;-E</a
      ><a name="15112"
      > </a
      ><a name="15113" class="Symbol"
      >(</a
      ><a name="15114" href="StlcProp.html#12491" class="Function"
      >context-lemma</a
      ><a name="15127"
      > </a
      ><a name="15128" class="Symbol"
      >(</a
      ><a name="15129" href="StlcProp.html#15090" class="Bound"
      >&#915;~&#915;&#8242;</a
      ><a name="15133"
      > </a
      ><a name="15134" href="https://agda.github.io/agda-stdlib/Function.html#713" class="Function Operator"
      >&#8728;</a
      ><a name="15135"
      > </a
      ><a name="15136" href="StlcProp.html#7778" class="InductiveConstructor"
      >free-&#183;&#8321;</a
      ><a name="15143" class="Symbol"
      >)</a
      ><a name="15144"
      >  </a
      ><a name="15146" href="StlcProp.html#15100" class="Bound"
      >&#8866;L</a
      ><a name="15148" class="Symbol"
      >)</a
      ><a name="15149"
      >
                                       </a
      ><a name="15189" class="Symbol"
      >(</a
      ><a name="15190" href="StlcProp.html#12491" class="Function"
      >context-lemma</a
      ><a name="15203"
      > </a
      ><a name="15204" class="Symbol"
      >(</a
      ><a name="15205" href="StlcProp.html#15090" class="Bound"
      >&#915;~&#915;&#8242;</a
      ><a name="15209"
      > </a
      ><a name="15210" href="https://agda.github.io/agda-stdlib/Function.html#713" class="Function Operator"
      >&#8728;</a
      ><a name="15211"
      > </a
      ><a name="15212" href="StlcProp.html#7822" class="InductiveConstructor"
      >free-&#183;&#8322;</a
      ><a name="15219" class="Symbol"
      >)</a
      ><a name="15220"
      > </a
      ><a name="15221" href="StlcProp.html#15103" class="Bound"
      >&#8866;M</a
      ><a name="15223" class="Symbol"
      >)</a
      ><a name="15224"
      > 
</a
      ><a name="15226" href="StlcProp.html#12491" class="Function"
      >context-lemma</a
      ><a name="15239"
      > </a
      ><a name="15240" href="StlcProp.html#15240" class="Bound"
      >&#915;~&#915;&#8242;</a
      ><a name="15244"
      > </a
      ><a name="15245" href="Stlc.html#3365" class="InductiveConstructor"
      >&#120121;-I&#8321;</a
      ><a name="15249"
      > </a
      ><a name="15250" class="Symbol"
      >=</a
      ><a name="15251"
      > </a
      ><a name="15252" href="Stlc.html#3365" class="InductiveConstructor"
      >&#120121;-I&#8321;</a
      ><a name="15256"
      >
</a
      ><a name="15257" href="StlcProp.html#12491" class="Function"
      >context-lemma</a
      ><a name="15270"
      > </a
      ><a name="15271" href="StlcProp.html#15271" class="Bound"
      >&#915;~&#915;&#8242;</a
      ><a name="15275"
      > </a
      ><a name="15276" href="Stlc.html#3399" class="InductiveConstructor"
      >&#120121;-I&#8322;</a
      ><a name="15280"
      > </a
      ><a name="15281" class="Symbol"
      >=</a
      ><a name="15282"
      > </a
      ><a name="15283" href="Stlc.html#3399" class="InductiveConstructor"
      >&#120121;-I&#8322;</a
      ><a name="15287"
      >
</a
      ><a name="15288" href="StlcProp.html#12491" class="Function"
      >context-lemma</a
      ><a name="15301"
      > </a
      ><a name="15302" href="StlcProp.html#15302" class="Bound"
      >&#915;~&#915;&#8242;</a
      ><a name="15306"
      > </a
      ><a name="15307" class="Symbol"
      >(</a
      ><a name="15308" href="Stlc.html#3434" class="InductiveConstructor"
      >&#120121;-E</a
      ><a name="15311"
      > </a
      ><a name="15312" href="StlcProp.html#15312" class="Bound"
      >&#8866;L</a
      ><a name="15314"
      > </a
      ><a name="15315" href="StlcProp.html#15315" class="Bound"
      >&#8866;M</a
      ><a name="15317"
      > </a
      ><a name="15318" href="StlcProp.html#15318" class="Bound"
      >&#8866;N</a
      ><a name="15320" class="Symbol"
      >)</a
      ><a name="15321"
      > </a
      ><a name="15322" class="Symbol"
      >=</a
      ><a name="15323"
      > </a
      ><a name="15324" href="Stlc.html#3434" class="InductiveConstructor"
      >&#120121;-E</a
      ><a name="15327"
      > </a
      ><a name="15328" class="Symbol"
      >(</a
      ><a name="15329" href="StlcProp.html#12491" class="Function"
      >context-lemma</a
      ><a name="15342"
      > </a
      ><a name="15343" class="Symbol"
      >(</a
      ><a name="15344" href="StlcProp.html#15302" class="Bound"
      >&#915;~&#915;&#8242;</a
      ><a name="15348"
      > </a
      ><a name="15349" href="https://agda.github.io/agda-stdlib/Function.html#713" class="Function Operator"
      >&#8728;</a
      ><a name="15350"
      > </a
      ><a name="15351" href="StlcProp.html#7866" class="InductiveConstructor"
      >free-if&#8321;</a
      ><a name="15359" class="Symbol"
      >)</a
      ><a name="15360"
      > </a
      ><a name="15361" href="StlcProp.html#15312" class="Bound"
      >&#8866;L</a
      ><a name="15363" class="Symbol"
      >)</a
      ><a name="15364"
      >
                                         </a
      ><a name="15406" class="Symbol"
      >(</a
      ><a name="15407" href="StlcProp.html#12491" class="Function"
      >context-lemma</a
      ><a name="15420"
      > </a
      ><a name="15421" class="Symbol"
      >(</a
      ><a name="15422" href="StlcProp.html#15302" class="Bound"
      >&#915;~&#915;&#8242;</a
      ><a name="15426"
      > </a
      ><a name="15427" href="https://agda.github.io/agda-stdlib/Function.html#713" class="Function Operator"
      >&#8728;</a
      ><a name="15428"
      > </a
      ><a name="15429" href="StlcProp.html#7926" class="InductiveConstructor"
      >free-if&#8322;</a
      ><a name="15437" class="Symbol"
      >)</a
      ><a name="15438"
      > </a
      ><a name="15439" href="StlcProp.html#15315" class="Bound"
      >&#8866;M</a
      ><a name="15441" class="Symbol"
      >)</a
      ><a name="15442"
      >
                                         </a
      ><a name="15484" class="Symbol"
      >(</a
      ><a name="15485" href="StlcProp.html#12491" class="Function"
      >context-lemma</a
      ><a name="15498"
      > </a
      ><a name="15499" class="Symbol"
      >(</a
      ><a name="15500" href="StlcProp.html#15302" class="Bound"
      >&#915;~&#915;&#8242;</a
      ><a name="15504"
      > </a
      ><a name="15505" href="https://agda.github.io/agda-stdlib/Function.html#713" class="Function Operator"
      >&#8728;</a
      ><a name="15506"
      > </a
      ><a name="15507" href="StlcProp.html#7986" class="InductiveConstructor"
      >free-if&#8323;</a
      ><a name="15515" class="Symbol"
      >)</a
      ><a name="15516"
      > </a
      ><a name="15517" href="StlcProp.html#15318" class="Bound"
      >&#8866;N</a
      ><a name="15519" class="Symbol"
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

<a name="16218" href="StlcProp.html#16218" class="Function"
      >preservation-[:=]</a
      ><a name="16235"
      > </a
      ><a name="16236" class="Symbol"
      >:</a
      ><a name="16237"
      > </a
      ><a name="16238" class="Symbol"
      >&#8704;</a
      ><a name="16239"
      > </a
      ><a name="16240" class="Symbol"
      >{</a
      ><a name="16241" href="StlcProp.html#16241" class="Bound"
      >&#915;</a
      ><a name="16242"
      > </a
      ><a name="16243" href="StlcProp.html#16243" class="Bound"
      >x</a
      ><a name="16244"
      > </a
      ><a name="16245" href="StlcProp.html#16245" class="Bound"
      >A</a
      ><a name="16246"
      > </a
      ><a name="16247" href="StlcProp.html#16247" class="Bound"
      >N</a
      ><a name="16248"
      > </a
      ><a name="16249" href="StlcProp.html#16249" class="Bound"
      >B</a
      ><a name="16250"
      > </a
      ><a name="16251" href="StlcProp.html#16251" class="Bound"
      >V</a
      ><a name="16252" class="Symbol"
      >}</a
      ><a name="16253"
      >
                 </a
      ><a name="16271" class="Symbol"
      >&#8594;</a
      ><a name="16272"
      > </a
      ><a name="16273" class="Symbol"
      >(</a
      ><a name="16274" href="StlcProp.html#16241" class="Bound"
      >&#915;</a
      ><a name="16275"
      > </a
      ><a name="16276" href="Maps.html#10368" class="Function Operator"
      >,</a
      ><a name="16277"
      > </a
      ><a name="16278" href="StlcProp.html#16243" class="Bound"
      >x</a
      ><a name="16279"
      > </a
      ><a name="16280" href="Maps.html#10368" class="Function Operator"
      >&#8758;</a
      ><a name="16281"
      > </a
      ><a name="16282" href="StlcProp.html#16245" class="Bound"
      >A</a
      ><a name="16283" class="Symbol"
      >)</a
      ><a name="16284"
      > </a
      ><a name="16285" href="Stlc.html#3112" class="Datatype Operator"
      >&#8866;</a
      ><a name="16286"
      > </a
      ><a name="16287" href="StlcProp.html#16247" class="Bound"
      >N</a
      ><a name="16288"
      > </a
      ><a name="16289" href="Stlc.html#3112" class="Datatype Operator"
      >&#8758;</a
      ><a name="16290"
      > </a
      ><a name="16291" href="StlcProp.html#16249" class="Bound"
      >B</a
      ><a name="16292"
      >
                 </a
      ><a name="16310" class="Symbol"
      >&#8594;</a
      ><a name="16311"
      > </a
      ><a name="16312" href="Maps.html#10265" class="Function"
      >&#8709;</a
      ><a name="16313"
      > </a
      ><a name="16314" href="Stlc.html#3112" class="Datatype Operator"
      >&#8866;</a
      ><a name="16315"
      > </a
      ><a name="16316" href="StlcProp.html#16251" class="Bound"
      >V</a
      ><a name="16317"
      > </a
      ><a name="16318" href="Stlc.html#3112" class="Datatype Operator"
      >&#8758;</a
      ><a name="16319"
      > </a
      ><a name="16320" href="StlcProp.html#16245" class="Bound"
      >A</a
      ><a name="16321"
      >
                 </a
      ><a name="16339" class="Symbol"
      >&#8594;</a
      ><a name="16340"
      > </a
      ><a name="16341" href="StlcProp.html#16241" class="Bound"
      >&#915;</a
      ><a name="16342"
      > </a
      ><a name="16343" href="Stlc.html#3112" class="Datatype Operator"
      >&#8866;</a
      ><a name="16344"
      > </a
      ><a name="16345" class="Symbol"
      >(</a
      ><a name="16346" href="StlcProp.html#16247" class="Bound"
      >N</a
      ><a name="16347"
      > </a
      ><a name="16348" href="Stlc.html#1276" class="Function Operator"
      >[</a
      ><a name="16349"
      > </a
      ><a name="16350" href="StlcProp.html#16243" class="Bound"
      >x</a
      ><a name="16351"
      > </a
      ><a name="16352" href="Stlc.html#1276" class="Function Operator"
      >:=</a
      ><a name="16354"
      > </a
      ><a name="16355" href="StlcProp.html#16251" class="Bound"
      >V</a
      ><a name="16356"
      > </a
      ><a name="16357" href="Stlc.html#1276" class="Function Operator"
      >]</a
      ><a name="16358" class="Symbol"
      >)</a
      ><a name="16359"
      > </a
      ><a name="16360" href="Stlc.html#3112" class="Datatype Operator"
      >&#8758;</a
      ><a name="16361"
      > </a
      ><a name="16362" href="StlcProp.html#16249" class="Bound"
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

      - If `N = \` x`, then from `Γ , x ∶ A ⊢ x ∶ B`
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
      ><a name="19546" href="Stlc.html#3112" class="Datatype Operator"
      >&#8866;</a
      ><a name="19547"
      > </a
      ><a name="19548" href="StlcProp.html#19535" class="Bound"
      >V</a
      ><a name="19549"
      > </a
      ><a name="19550" href="Stlc.html#3112" class="Datatype Operator"
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
      ><a name="19558" href="Stlc.html#3112" class="Datatype Operator"
      >&#8866;</a
      ><a name="19559"
      > </a
      ><a name="19560" href="StlcProp.html#19535" class="Bound"
      >V</a
      ><a name="19561"
      > </a
      ><a name="19562" href="Stlc.html#3112" class="Datatype Operator"
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
      ><a name="19597" href="StlcProp.html#12491" class="Function"
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
      ><a name="19646" href="StlcProp.html#7659" class="Datatype Operator"
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
      ><a name="19721" href="StlcProp.html#7659" class="Datatype Operator"
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
      ><a name="19736" href="StlcProp.html#11791" class="Postulate"
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
      ><a name="19752"
      >

</a
      ><a name="19754" href="StlcProp.html#19754" class="Function"
      >just-injective</a
      ><a name="19768"
      > </a
      ><a name="19769" class="Symbol"
      >:</a
      ><a name="19770"
      > </a
      ><a name="19771" class="Symbol"
      >&#8704;</a
      ><a name="19772"
      > </a
      ><a name="19773" class="Symbol"
      >{</a
      ><a name="19774" href="StlcProp.html#19774" class="Bound"
      >X</a
      ><a name="19775"
      > </a
      ><a name="19776" class="Symbol"
      >:</a
      ><a name="19777"
      > </a
      ><a name="19778" class="PrimitiveType"
      >Set</a
      ><a name="19781" class="Symbol"
      >}</a
      ><a name="19782"
      > </a
      ><a name="19783" class="Symbol"
      >{</a
      ><a name="19784" href="StlcProp.html#19784" class="Bound"
      >x</a
      ><a name="19785"
      > </a
      ><a name="19786" href="StlcProp.html#19786" class="Bound"
      >y</a
      ><a name="19787"
      > </a
      ><a name="19788" class="Symbol"
      >:</a
      ><a name="19789"
      > </a
      ><a name="19790" href="StlcProp.html#19774" class="Bound"
      >X</a
      ><a name="19791" class="Symbol"
      >}</a
      ><a name="19792"
      > </a
      ><a name="19793" class="Symbol"
      >&#8594;</a
      ><a name="19794"
      > </a
      ><a name="19795" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >_&#8801;_</a
      ><a name="19798"
      > </a
      ><a name="19799" class="Symbol"
      >{</a
      ><a name="19800" class="Argument"
      >A</a
      ><a name="19801"
      > </a
      ><a name="19802" class="Symbol"
      >=</a
      ><a name="19803"
      > </a
      ><a name="19804" href="https://agda.github.io/agda-stdlib/Data.Maybe.Base.html#335" class="Datatype"
      >Maybe</a
      ><a name="19809"
      > </a
      ><a name="19810" href="StlcProp.html#19774" class="Bound"
      >X</a
      ><a name="19811" class="Symbol"
      >}</a
      ><a name="19812"
      > </a
      ><a name="19813" class="Symbol"
      >(</a
      ><a name="19814" href="https://agda.github.io/agda-stdlib/Data.Maybe.Base.html#373" class="InductiveConstructor"
      >just</a
      ><a name="19818"
      > </a
      ><a name="19819" href="StlcProp.html#19784" class="Bound"
      >x</a
      ><a name="19820" class="Symbol"
      >)</a
      ><a name="19821"
      > </a
      ><a name="19822" class="Symbol"
      >(</a
      ><a name="19823" href="https://agda.github.io/agda-stdlib/Data.Maybe.Base.html#373" class="InductiveConstructor"
      >just</a
      ><a name="19827"
      > </a
      ><a name="19828" href="StlcProp.html#19786" class="Bound"
      >y</a
      ><a name="19829" class="Symbol"
      >)</a
      ><a name="19830"
      > </a
      ><a name="19831" class="Symbol"
      >&#8594;</a
      ><a name="19832"
      > </a
      ><a name="19833" href="StlcProp.html#19784" class="Bound"
      >x</a
      ><a name="19834"
      > </a
      ><a name="19835" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="19836"
      > </a
      ><a name="19837" href="StlcProp.html#19786" class="Bound"
      >y</a
      ><a name="19838"
      >
</a
      ><a name="19839" href="StlcProp.html#19754" class="Function"
      >just-injective</a
      ><a name="19853"
      > </a
      ><a name="19854" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="19858"
      > </a
      ><a name="19859" class="Symbol"
      >=</a
      ><a name="19860"
      > </a
      ><a name="19861" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      >

</pre>

<pre class="Agda">

<a name="19891" href="StlcProp.html#16218" class="Function"
      >preservation-[:=]</a
      ><a name="19908"
      > </a
      ><a name="19909" class="Symbol"
      >{</a
      ><a name="19910" href="StlcProp.html#19910" class="Bound"
      >&#915;</a
      ><a name="19911" class="Symbol"
      >}</a
      ><a name="19912"
      > </a
      ><a name="19913" class="Symbol"
      >{</a
      ><a name="19914" href="StlcProp.html#19914" class="Bound"
      >x</a
      ><a name="19915" class="Symbol"
      >}</a
      ><a name="19916"
      > </a
      ><a name="19917" class="Symbol"
      >{</a
      ><a name="19918" href="StlcProp.html#19918" class="Bound"
      >A</a
      ><a name="19919" class="Symbol"
      >}</a
      ><a name="19920"
      > </a
      ><a name="19921" class="Symbol"
      >(</a
      ><a name="19922" href="Stlc.html#3156" class="InductiveConstructor"
      >Ax</a
      ><a name="19924"
      > </a
      ><a name="19925" class="Symbol"
      >{</a
      ><a name="19926" href="StlcProp.html#19926" class="Bound"
      >&#915;,x&#8758;A</a
      ><a name="19931" class="Symbol"
      >}</a
      ><a name="19932"
      > </a
      ><a name="19933" class="Symbol"
      >{</a
      ><a name="19934" href="StlcProp.html#19934" class="Bound"
      >x&#8242;</a
      ><a name="19936" class="Symbol"
      >}</a
      ><a name="19937"
      > </a
      ><a name="19938" class="Symbol"
      >{</a
      ><a name="19939" href="StlcProp.html#19939" class="Bound"
      >B</a
      ><a name="19940" class="Symbol"
      >}</a
      ><a name="19941"
      > </a
      ><a name="19942" href="StlcProp.html#19942" class="Bound"
      >[&#915;,x&#8758;A]x&#8242;&#8801;B</a
      ><a name="19953" class="Symbol"
      >)</a
      ><a name="19954"
      > </a
      ><a name="19955" href="StlcProp.html#19955" class="Bound"
      >&#8866;V</a
      ><a name="19957"
      > </a
      ><a name="19958" class="Keyword"
      >with</a
      ><a name="19962"
      > </a
      ><a name="19963" href="StlcProp.html#19914" class="Bound"
      >x</a
      ><a name="19964"
      > </a
      ><a name="19965" href="Maps.html#2509" class="Function Operator"
      >&#8799;</a
      ><a name="19966"
      > </a
      ><a name="19967" href="StlcProp.html#19934" class="Bound"
      >x&#8242;</a
      ><a name="19969"
      >
</a
      ><a name="19970" class="Symbol"
      >...|</a
      ><a name="19974"
      > </a
      ><a name="19975" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#520" class="InductiveConstructor"
      >yes</a
      ><a name="19978"
      > </a
      ><a name="19979" href="StlcProp.html#19979" class="Bound"
      >x&#8801;x&#8242;</a
      ><a name="19983"
      > </a
      ><a name="19984" class="Keyword"
      >rewrite</a
      ><a name="19991"
      > </a
      ><a name="19992" href="StlcProp.html#19754" class="Function"
      >just-injective</a
      ><a name="20006"
      > </a
      ><a name="20007" href="StlcProp.html#19942" class="Bound"
      >[&#915;,x&#8758;A]x&#8242;&#8801;B</a
      ><a name="20018"
      >  </a
      ><a name="20020" class="Symbol"
      >=</a
      ><a name="20021"
      >  </a
      ><a name="20023" href="StlcProp.html#19516" class="Function"
      >weaken-closed</a
      ><a name="20036"
      > </a
      ><a name="20037" href="StlcProp.html#19955" class="Bound"
      >&#8866;V</a
      ><a name="20039"
      >
</a
      ><a name="20040" class="Symbol"
      >...|</a
      ><a name="20044"
      > </a
      ><a name="20045" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#547" class="InductiveConstructor"
      >no</a
      ><a name="20047"
      >  </a
      ><a name="20049" href="StlcProp.html#20049" class="Bound"
      >x&#8802;x&#8242;</a
      ><a name="20053"
      >  </a
      ><a name="20055" class="Symbol"
      >=</a
      ><a name="20056"
      >  </a
      ><a name="20058" href="Stlc.html#3156" class="InductiveConstructor"
      >Ax</a
      ><a name="20060"
      > </a
      ><a name="20061" href="StlcProp.html#19942" class="Bound"
      >[&#915;,x&#8758;A]x&#8242;&#8801;B</a
      ><a name="20072"
      >
</a
      ><a name="20073" href="StlcProp.html#16218" class="Function"
      >preservation-[:=]</a
      ><a name="20090"
      > </a
      ><a name="20091" class="Symbol"
      >{</a
      ><a name="20092" href="StlcProp.html#20092" class="Bound"
      >&#915;</a
      ><a name="20093" class="Symbol"
      >}</a
      ><a name="20094"
      > </a
      ><a name="20095" class="Symbol"
      >{</a
      ><a name="20096" href="StlcProp.html#20096" class="Bound"
      >x</a
      ><a name="20097" class="Symbol"
      >}</a
      ><a name="20098"
      > </a
      ><a name="20099" class="Symbol"
      >{</a
      ><a name="20100" href="StlcProp.html#20100" class="Bound"
      >A</a
      ><a name="20101" class="Symbol"
      >}</a
      ><a name="20102"
      > </a
      ><a name="20103" class="Symbol"
      >{</a
      ><a name="20104" href="Stlc.html#743" class="InductiveConstructor Operator"
      >&#955;[</a
      ><a name="20106"
      > </a
      ><a name="20107" href="StlcProp.html#20107" class="Bound"
      >x&#8242;</a
      ><a name="20109"
      > </a
      ><a name="20110" href="Stlc.html#743" class="InductiveConstructor Operator"
      >&#8758;</a
      ><a name="20111"
      > </a
      ><a name="20112" href="StlcProp.html#20112" class="Bound"
      >A&#8242;</a
      ><a name="20114"
      > </a
      ><a name="20115" href="Stlc.html#743" class="InductiveConstructor Operator"
      >]</a
      ><a name="20116"
      > </a
      ><a name="20117" href="StlcProp.html#20117" class="Bound"
      >N&#8242;</a
      ><a name="20119" class="Symbol"
      >}</a
      ><a name="20120"
      > </a
      ><a name="20121" class="Symbol"
      >{</a
      ><a name="20122" class="DottedPattern Symbol"
      >.</a
      ><a name="20123" href="StlcProp.html#20112" class="DottedPattern Bound"
      >A&#8242;</a
      ><a name="20125"
      > </a
      ><a name="20126" href="Stlc.html#609" class="InductiveConstructor Operator"
      >&#8658;</a
      ><a name="20127"
      > </a
      ><a name="20128" href="StlcProp.html#20128" class="Bound"
      >B&#8242;</a
      ><a name="20130" class="Symbol"
      >}</a
      ><a name="20131"
      > </a
      ><a name="20132" class="Symbol"
      >{</a
      ><a name="20133" href="StlcProp.html#20133" class="Bound"
      >V</a
      ><a name="20134" class="Symbol"
      >}</a
      ><a name="20135"
      > </a
      ><a name="20136" class="Symbol"
      >(</a
      ><a name="20137" href="Stlc.html#3210" class="InductiveConstructor"
      >&#8658;-I</a
      ><a name="20140"
      > </a
      ><a name="20141" href="StlcProp.html#20141" class="Bound"
      >&#8866;N&#8242;</a
      ><a name="20144" class="Symbol"
      >)</a
      ><a name="20145"
      > </a
      ><a name="20146" href="StlcProp.html#20146" class="Bound"
      >&#8866;V</a
      ><a name="20148"
      > </a
      ><a name="20149" class="Keyword"
      >with</a
      ><a name="20153"
      > </a
      ><a name="20154" href="StlcProp.html#20096" class="Bound"
      >x</a
      ><a name="20155"
      > </a
      ><a name="20156" href="Maps.html#2509" class="Function Operator"
      >&#8799;</a
      ><a name="20157"
      > </a
      ><a name="20158" href="StlcProp.html#20107" class="Bound"
      >x&#8242;</a
      ><a name="20160"
      >
</a
      ><a name="20161" class="Symbol"
      >...|</a
      ><a name="20165"
      > </a
      ><a name="20166" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#520" class="InductiveConstructor"
      >yes</a
      ><a name="20169"
      > </a
      ><a name="20170" href="StlcProp.html#20170" class="Bound"
      >x&#8801;x&#8242;</a
      ><a name="20174"
      > </a
      ><a name="20175" class="Keyword"
      >rewrite</a
      ><a name="20182"
      > </a
      ><a name="20183" href="StlcProp.html#20170" class="Bound"
      >x&#8801;x&#8242;</a
      ><a name="20187"
      > </a
      ><a name="20188" class="Symbol"
      >=</a
      ><a name="20189"
      > </a
      ><a name="20190" href="StlcProp.html#12491" class="Function"
      >context-lemma</a
      ><a name="20203"
      > </a
      ><a name="20204" href="StlcProp.html#20229" class="Function"
      >&#915;&#8242;~&#915;</a
      ><a name="20208"
      > </a
      ><a name="20209" class="Symbol"
      >(</a
      ><a name="20210" href="Stlc.html#3210" class="InductiveConstructor"
      >&#8658;-I</a
      ><a name="20213"
      > </a
      ><a name="20214" href="StlcProp.html#20141" class="Bound"
      >&#8866;N&#8242;</a
      ><a name="20217" class="Symbol"
      >)</a
      ><a name="20218"
      >
  </a
      ><a name="20221" class="Keyword"
      >where</a
      ><a name="20226"
      >
  </a
      ><a name="20229" href="StlcProp.html#20229" class="Function"
      >&#915;&#8242;~&#915;</a
      ><a name="20233"
      > </a
      ><a name="20234" class="Symbol"
      >:</a
      ><a name="20235"
      > </a
      ><a name="20236" class="Symbol"
      >&#8704;</a
      ><a name="20237"
      > </a
      ><a name="20238" class="Symbol"
      >{</a
      ><a name="20239" href="StlcProp.html#20239" class="Bound"
      >y</a
      ><a name="20240" class="Symbol"
      >}</a
      ><a name="20241"
      > </a
      ><a name="20242" class="Symbol"
      >&#8594;</a
      ><a name="20243"
      > </a
      ><a name="20244" href="StlcProp.html#20239" class="Bound"
      >y</a
      ><a name="20245"
      > </a
      ><a name="20246" href="StlcProp.html#7659" class="Datatype Operator"
      >&#8712;</a
      ><a name="20247"
      > </a
      ><a name="20248" class="Symbol"
      >(</a
      ><a name="20249" href="Stlc.html#743" class="InductiveConstructor Operator"
      >&#955;[</a
      ><a name="20251"
      > </a
      ><a name="20252" href="StlcProp.html#20107" class="Bound"
      >x&#8242;</a
      ><a name="20254"
      > </a
      ><a name="20255" href="Stlc.html#743" class="InductiveConstructor Operator"
      >&#8758;</a
      ><a name="20256"
      > </a
      ><a name="20257" href="StlcProp.html#20112" class="Bound"
      >A&#8242;</a
      ><a name="20259"
      > </a
      ><a name="20260" href="Stlc.html#743" class="InductiveConstructor Operator"
      >]</a
      ><a name="20261"
      > </a
      ><a name="20262" href="StlcProp.html#20117" class="Bound"
      >N&#8242;</a
      ><a name="20264" class="Symbol"
      >)</a
      ><a name="20265"
      > </a
      ><a name="20266" class="Symbol"
      >&#8594;</a
      ><a name="20267"
      > </a
      ><a name="20268" class="Symbol"
      >(</a
      ><a name="20269" href="StlcProp.html#20092" class="Bound"
      >&#915;</a
      ><a name="20270"
      > </a
      ><a name="20271" href="Maps.html#10368" class="Function Operator"
      >,</a
      ><a name="20272"
      > </a
      ><a name="20273" href="StlcProp.html#20107" class="Bound"
      >x&#8242;</a
      ><a name="20275"
      > </a
      ><a name="20276" href="Maps.html#10368" class="Function Operator"
      >&#8758;</a
      ><a name="20277"
      > </a
      ><a name="20278" href="StlcProp.html#20100" class="Bound"
      >A</a
      ><a name="20279" class="Symbol"
      >)</a
      ><a name="20280"
      > </a
      ><a name="20281" href="StlcProp.html#20239" class="Bound"
      >y</a
      ><a name="20282"
      > </a
      ><a name="20283" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="20284"
      > </a
      ><a name="20285" href="StlcProp.html#20092" class="Bound"
      >&#915;</a
      ><a name="20286"
      > </a
      ><a name="20287" href="StlcProp.html#20239" class="Bound"
      >y</a
      ><a name="20288"
      >
  </a
      ><a name="20291" href="StlcProp.html#20229" class="Function"
      >&#915;&#8242;~&#915;</a
      ><a name="20295"
      > </a
      ><a name="20296" class="Symbol"
      >{</a
      ><a name="20297" href="StlcProp.html#20297" class="Bound"
      >y</a
      ><a name="20298" class="Symbol"
      >}</a
      ><a name="20299"
      > </a
      ><a name="20300" class="Symbol"
      >(</a
      ><a name="20301" href="StlcProp.html#7717" class="InductiveConstructor"
      >free-&#955;</a
      ><a name="20307"
      > </a
      ><a name="20308" href="StlcProp.html#20308" class="Bound"
      >x&#8242;&#8802;y</a
      ><a name="20312"
      > </a
      ><a name="20313" href="StlcProp.html#20313" class="Bound"
      >y&#8712;N&#8242;</a
      ><a name="20317" class="Symbol"
      >)</a
      ><a name="20318"
      > </a
      ><a name="20319" class="Keyword"
      >with</a
      ><a name="20323"
      > </a
      ><a name="20324" href="StlcProp.html#20107" class="Bound"
      >x&#8242;</a
      ><a name="20326"
      > </a
      ><a name="20327" href="Maps.html#2509" class="Function Operator"
      >&#8799;</a
      ><a name="20328"
      > </a
      ><a name="20329" href="StlcProp.html#20297" class="Bound"
      >y</a
      ><a name="20330"
      >
  </a
      ><a name="20333" class="Symbol"
      >...|</a
      ><a name="20337"
      > </a
      ><a name="20338" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#520" class="InductiveConstructor"
      >yes</a
      ><a name="20341"
      > </a
      ><a name="20342" href="StlcProp.html#20342" class="Bound"
      >x&#8242;&#8801;y</a
      ><a name="20346"
      >  </a
      ><a name="20348" class="Symbol"
      >=</a
      ><a name="20349"
      > </a
      ><a name="20350" href="https://agda.github.io/agda-stdlib/Data.Empty.html#348" class="Function"
      >&#8869;-elim</a
      ><a name="20356"
      > </a
      ><a name="20357" class="Symbol"
      >(</a
      ><a name="20358" href="StlcProp.html#20308" class="Bound"
      >x&#8242;&#8802;y</a
      ><a name="20362"
      > </a
      ><a name="20363" href="StlcProp.html#20342" class="Bound"
      >x&#8242;&#8801;y</a
      ><a name="20367" class="Symbol"
      >)</a
      ><a name="20368"
      >
  </a
      ><a name="20371" class="Symbol"
      >...|</a
      ><a name="20375"
      > </a
      ><a name="20376" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#547" class="InductiveConstructor"
      >no</a
      ><a name="20378"
      >  </a
      ><a name="20380" class="Symbol"
      >_</a
      ><a name="20381"
      >     </a
      ><a name="20386" class="Symbol"
      >=</a
      ><a name="20387"
      > </a
      ><a name="20388" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="20392"
      >
</a
      ><a name="20393" class="Symbol"
      >...|</a
      ><a name="20397"
      > </a
      ><a name="20398" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#547" class="InductiveConstructor"
      >no</a
      ><a name="20400"
      >  </a
      ><a name="20402" href="StlcProp.html#20402" class="Bound"
      >x&#8802;x&#8242;</a
      ><a name="20406"
      > </a
      ><a name="20407" class="Symbol"
      >=</a
      ><a name="20408"
      > </a
      ><a name="20409" href="Stlc.html#3210" class="InductiveConstructor"
      >&#8658;-I</a
      ><a name="20412"
      > </a
      ><a name="20413" href="StlcProp.html#20524" class="Function"
      >&#8866;N&#8242;V</a
      ><a name="20417"
      >
  </a
      ><a name="20420" class="Keyword"
      >where</a
      ><a name="20425"
      >
  </a
      ><a name="20428" href="StlcProp.html#20428" class="Function"
      >x&#8242;x&#8866;N&#8242;</a
      ><a name="20434"
      > </a
      ><a name="20435" class="Symbol"
      >:</a
      ><a name="20436"
      > </a
      ><a name="20437" href="StlcProp.html#20092" class="Bound"
      >&#915;</a
      ><a name="20438"
      > </a
      ><a name="20439" href="Maps.html#10368" class="Function Operator"
      >,</a
      ><a name="20440"
      > </a
      ><a name="20441" href="StlcProp.html#20107" class="Bound"
      >x&#8242;</a
      ><a name="20443"
      > </a
      ><a name="20444" href="Maps.html#10368" class="Function Operator"
      >&#8758;</a
      ><a name="20445"
      > </a
      ><a name="20446" href="StlcProp.html#20112" class="Bound"
      >A&#8242;</a
      ><a name="20448"
      > </a
      ><a name="20449" href="Maps.html#10368" class="Function Operator"
      >,</a
      ><a name="20450"
      > </a
      ><a name="20451" href="StlcProp.html#20096" class="Bound"
      >x</a
      ><a name="20452"
      > </a
      ><a name="20453" href="Maps.html#10368" class="Function Operator"
      >&#8758;</a
      ><a name="20454"
      > </a
      ><a name="20455" href="StlcProp.html#20100" class="Bound"
      >A</a
      ><a name="20456"
      > </a
      ><a name="20457" href="Stlc.html#3112" class="Datatype Operator"
      >&#8866;</a
      ><a name="20458"
      > </a
      ><a name="20459" href="StlcProp.html#20117" class="Bound"
      >N&#8242;</a
      ><a name="20461"
      > </a
      ><a name="20462" href="Stlc.html#3112" class="Datatype Operator"
      >&#8758;</a
      ><a name="20463"
      > </a
      ><a name="20464" href="StlcProp.html#20128" class="Bound"
      >B&#8242;</a
      ><a name="20466"
      >
  </a
      ><a name="20469" href="StlcProp.html#20428" class="Function"
      >x&#8242;x&#8866;N&#8242;</a
      ><a name="20475"
      > </a
      ><a name="20476" class="Keyword"
      >rewrite</a
      ><a name="20483"
      > </a
      ><a name="20484" href="Maps.html#11491" class="Function"
      >update-permute</a
      ><a name="20498"
      > </a
      ><a name="20499" href="StlcProp.html#20092" class="Bound"
      >&#915;</a
      ><a name="20500"
      > </a
      ><a name="20501" href="StlcProp.html#20096" class="Bound"
      >x</a
      ><a name="20502"
      > </a
      ><a name="20503" href="StlcProp.html#20100" class="Bound"
      >A</a
      ><a name="20504"
      > </a
      ><a name="20505" href="StlcProp.html#20107" class="Bound"
      >x&#8242;</a
      ><a name="20507"
      > </a
      ><a name="20508" href="StlcProp.html#20112" class="Bound"
      >A&#8242;</a
      ><a name="20510"
      > </a
      ><a name="20511" href="StlcProp.html#20402" class="Bound"
      >x&#8802;x&#8242;</a
      ><a name="20515"
      > </a
      ><a name="20516" class="Symbol"
      >=</a
      ><a name="20517"
      > </a
      ><a name="20518" href="StlcProp.html#20141" class="Bound"
      >&#8866;N&#8242;</a
      ><a name="20521"
      >
  </a
      ><a name="20524" href="StlcProp.html#20524" class="Function"
      >&#8866;N&#8242;V</a
      ><a name="20528"
      > </a
      ><a name="20529" class="Symbol"
      >:</a
      ><a name="20530"
      > </a
      ><a name="20531" class="Symbol"
      >(</a
      ><a name="20532" href="StlcProp.html#20092" class="Bound"
      >&#915;</a
      ><a name="20533"
      > </a
      ><a name="20534" href="Maps.html#10368" class="Function Operator"
      >,</a
      ><a name="20535"
      > </a
      ><a name="20536" href="StlcProp.html#20107" class="Bound"
      >x&#8242;</a
      ><a name="20538"
      > </a
      ><a name="20539" href="Maps.html#10368" class="Function Operator"
      >&#8758;</a
      ><a name="20540"
      > </a
      ><a name="20541" href="StlcProp.html#20112" class="Bound"
      >A&#8242;</a
      ><a name="20543" class="Symbol"
      >)</a
      ><a name="20544"
      > </a
      ><a name="20545" href="Stlc.html#3112" class="Datatype Operator"
      >&#8866;</a
      ><a name="20546"
      > </a
      ><a name="20547" href="StlcProp.html#20117" class="Bound"
      >N&#8242;</a
      ><a name="20549"
      > </a
      ><a name="20550" href="Stlc.html#1276" class="Function Operator"
      >[</a
      ><a name="20551"
      > </a
      ><a name="20552" href="StlcProp.html#20096" class="Bound"
      >x</a
      ><a name="20553"
      > </a
      ><a name="20554" href="Stlc.html#1276" class="Function Operator"
      >:=</a
      ><a name="20556"
      > </a
      ><a name="20557" href="StlcProp.html#20133" class="Bound"
      >V</a
      ><a name="20558"
      > </a
      ><a name="20559" href="Stlc.html#1276" class="Function Operator"
      >]</a
      ><a name="20560"
      > </a
      ><a name="20561" href="Stlc.html#3112" class="Datatype Operator"
      >&#8758;</a
      ><a name="20562"
      > </a
      ><a name="20563" href="StlcProp.html#20128" class="Bound"
      >B&#8242;</a
      ><a name="20565"
      >
  </a
      ><a name="20568" href="StlcProp.html#20524" class="Function"
      >&#8866;N&#8242;V</a
      ><a name="20572"
      > </a
      ><a name="20573" class="Symbol"
      >=</a
      ><a name="20574"
      > </a
      ><a name="20575" href="StlcProp.html#16218" class="Function"
      >preservation-[:=]</a
      ><a name="20592"
      > </a
      ><a name="20593" href="StlcProp.html#20428" class="Function"
      >x&#8242;x&#8866;N&#8242;</a
      ><a name="20599"
      > </a
      ><a name="20600" href="StlcProp.html#20146" class="Bound"
      >&#8866;V</a
      ><a name="20602"
      >
</a
      ><a name="20603" href="StlcProp.html#16218" class="Function"
      >preservation-[:=]</a
      ><a name="20620"
      > </a
      ><a name="20621" class="Symbol"
      >(</a
      ><a name="20622" href="Stlc.html#3287" class="InductiveConstructor"
      >&#8658;-E</a
      ><a name="20625"
      > </a
      ><a name="20626" href="StlcProp.html#20626" class="Bound"
      >&#8866;L</a
      ><a name="20628"
      > </a
      ><a name="20629" href="StlcProp.html#20629" class="Bound"
      >&#8866;M</a
      ><a name="20631" class="Symbol"
      >)</a
      ><a name="20632"
      > </a
      ><a name="20633" href="StlcProp.html#20633" class="Bound"
      >&#8866;V</a
      ><a name="20635"
      > </a
      ><a name="20636" class="Symbol"
      >=</a
      ><a name="20637"
      > </a
      ><a name="20638" href="Stlc.html#3287" class="InductiveConstructor"
      >&#8658;-E</a
      ><a name="20641"
      > </a
      ><a name="20642" class="Symbol"
      >(</a
      ><a name="20643" href="StlcProp.html#16218" class="Function"
      >preservation-[:=]</a
      ><a name="20660"
      > </a
      ><a name="20661" href="StlcProp.html#20626" class="Bound"
      >&#8866;L</a
      ><a name="20663"
      > </a
      ><a name="20664" href="StlcProp.html#20633" class="Bound"
      >&#8866;V</a
      ><a name="20666" class="Symbol"
      >)</a
      ><a name="20667"
      > </a
      ><a name="20668" class="Symbol"
      >(</a
      ><a name="20669" href="StlcProp.html#16218" class="Function"
      >preservation-[:=]</a
      ><a name="20686"
      > </a
      ><a name="20687" href="StlcProp.html#20629" class="Bound"
      >&#8866;M</a
      ><a name="20689"
      > </a
      ><a name="20690" href="StlcProp.html#20633" class="Bound"
      >&#8866;V</a
      ><a name="20692" class="Symbol"
      >)</a
      ><a name="20693"
      >
</a
      ><a name="20694" href="StlcProp.html#16218" class="Function"
      >preservation-[:=]</a
      ><a name="20711"
      > </a
      ><a name="20712" href="Stlc.html#3365" class="InductiveConstructor"
      >&#120121;-I&#8321;</a
      ><a name="20716"
      > </a
      ><a name="20717" href="StlcProp.html#20717" class="Bound"
      >&#8866;V</a
      ><a name="20719"
      > </a
      ><a name="20720" class="Symbol"
      >=</a
      ><a name="20721"
      > </a
      ><a name="20722" href="Stlc.html#3365" class="InductiveConstructor"
      >&#120121;-I&#8321;</a
      ><a name="20726"
      >
</a
      ><a name="20727" href="StlcProp.html#16218" class="Function"
      >preservation-[:=]</a
      ><a name="20744"
      > </a
      ><a name="20745" href="Stlc.html#3399" class="InductiveConstructor"
      >&#120121;-I&#8322;</a
      ><a name="20749"
      > </a
      ><a name="20750" href="StlcProp.html#20750" class="Bound"
      >&#8866;V</a
      ><a name="20752"
      > </a
      ><a name="20753" class="Symbol"
      >=</a
      ><a name="20754"
      > </a
      ><a name="20755" href="Stlc.html#3399" class="InductiveConstructor"
      >&#120121;-I&#8322;</a
      ><a name="20759"
      >
</a
      ><a name="20760" href="StlcProp.html#16218" class="Function"
      >preservation-[:=]</a
      ><a name="20777"
      > </a
      ><a name="20778" class="Symbol"
      >(</a
      ><a name="20779" href="Stlc.html#3434" class="InductiveConstructor"
      >&#120121;-E</a
      ><a name="20782"
      > </a
      ><a name="20783" href="StlcProp.html#20783" class="Bound"
      >&#8866;L</a
      ><a name="20785"
      > </a
      ><a name="20786" href="StlcProp.html#20786" class="Bound"
      >&#8866;M</a
      ><a name="20788"
      > </a
      ><a name="20789" href="StlcProp.html#20789" class="Bound"
      >&#8866;N</a
      ><a name="20791" class="Symbol"
      >)</a
      ><a name="20792"
      > </a
      ><a name="20793" href="StlcProp.html#20793" class="Bound"
      >&#8866;V</a
      ><a name="20795"
      > </a
      ><a name="20796" class="Symbol"
      >=</a
      ><a name="20797"
      >
  </a
      ><a name="20800" href="Stlc.html#3434" class="InductiveConstructor"
      >&#120121;-E</a
      ><a name="20803"
      > </a
      ><a name="20804" class="Symbol"
      >(</a
      ><a name="20805" href="StlcProp.html#16218" class="Function"
      >preservation-[:=]</a
      ><a name="20822"
      > </a
      ><a name="20823" href="StlcProp.html#20783" class="Bound"
      >&#8866;L</a
      ><a name="20825"
      > </a
      ><a name="20826" href="StlcProp.html#20793" class="Bound"
      >&#8866;V</a
      ><a name="20828" class="Symbol"
      >)</a
      ><a name="20829"
      > </a
      ><a name="20830" class="Symbol"
      >(</a
      ><a name="20831" href="StlcProp.html#16218" class="Function"
      >preservation-[:=]</a
      ><a name="20848"
      > </a
      ><a name="20849" href="StlcProp.html#20786" class="Bound"
      >&#8866;M</a
      ><a name="20851"
      > </a
      ><a name="20852" href="StlcProp.html#20793" class="Bound"
      >&#8866;V</a
      ><a name="20854" class="Symbol"
      >)</a
      ><a name="20855"
      > </a
      ><a name="20856" class="Symbol"
      >(</a
      ><a name="20857" href="StlcProp.html#16218" class="Function"
      >preservation-[:=]</a
      ><a name="20874"
      > </a
      ><a name="20875" href="StlcProp.html#20789" class="Bound"
      >&#8866;N</a
      ><a name="20877"
      > </a
      ><a name="20878" href="StlcProp.html#20793" class="Bound"
      >&#8866;V</a
      ><a name="20880" class="Symbol"
      >)</a
      >

</pre>


### Main Theorem

We now have the tools we need to prove preservation: if a closed
term `M` has type `A` and takes a step to `N`, then `N`
is also a closed term with type `A`.  In other words, small-step
reduction preserves types.

<pre class="Agda">

<a name="21140" href="StlcProp.html#21140" class="Function"
      >preservation</a
      ><a name="21152"
      > </a
      ><a name="21153" class="Symbol"
      >:</a
      ><a name="21154"
      > </a
      ><a name="21155" class="Symbol"
      >&#8704;</a
      ><a name="21156"
      > </a
      ><a name="21157" class="Symbol"
      >{</a
      ><a name="21158" href="StlcProp.html#21158" class="Bound"
      >M</a
      ><a name="21159"
      > </a
      ><a name="21160" href="StlcProp.html#21160" class="Bound"
      >N</a
      ><a name="21161"
      > </a
      ><a name="21162" href="StlcProp.html#21162" class="Bound"
      >A</a
      ><a name="21163" class="Symbol"
      >}</a
      ><a name="21164"
      > </a
      ><a name="21165" class="Symbol"
      >&#8594;</a
      ><a name="21166"
      > </a
      ><a name="21167" href="Maps.html#10265" class="Function"
      >&#8709;</a
      ><a name="21168"
      > </a
      ><a name="21169" href="Stlc.html#3112" class="Datatype Operator"
      >&#8866;</a
      ><a name="21170"
      > </a
      ><a name="21171" href="StlcProp.html#21158" class="Bound"
      >M</a
      ><a name="21172"
      > </a
      ><a name="21173" href="Stlc.html#3112" class="Datatype Operator"
      >&#8758;</a
      ><a name="21174"
      > </a
      ><a name="21175" href="StlcProp.html#21162" class="Bound"
      >A</a
      ><a name="21176"
      > </a
      ><a name="21177" class="Symbol"
      >&#8594;</a
      ><a name="21178"
      > </a
      ><a name="21179" href="StlcProp.html#21158" class="Bound"
      >M</a
      ><a name="21180"
      > </a
      ><a name="21181" href="Stlc.html#1762" class="Datatype Operator"
      >&#10233;</a
      ><a name="21182"
      > </a
      ><a name="21183" href="StlcProp.html#21160" class="Bound"
      >N</a
      ><a name="21184"
      > </a
      ><a name="21185" class="Symbol"
      >&#8594;</a
      ><a name="21186"
      > </a
      ><a name="21187" href="Maps.html#10265" class="Function"
      >&#8709;</a
      ><a name="21188"
      > </a
      ><a name="21189" href="Stlc.html#3112" class="Datatype Operator"
      >&#8866;</a
      ><a name="21190"
      > </a
      ><a name="21191" href="StlcProp.html#21160" class="Bound"
      >N</a
      ><a name="21192"
      > </a
      ><a name="21193" href="Stlc.html#3112" class="Datatype Operator"
      >&#8758;</a
      ><a name="21194"
      > </a
      ><a name="21195" href="StlcProp.html#21162" class="Bound"
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

<a name="22453" href="StlcProp.html#21140" class="Function"
      >preservation</a
      ><a name="22465"
      > </a
      ><a name="22466" class="Symbol"
      >(</a
      ><a name="22467" href="Stlc.html#3156" class="InductiveConstructor"
      >Ax</a
      ><a name="22469"
      > </a
      ><a name="22470" href="StlcProp.html#22470" class="Bound"
      >&#915;x&#8801;A</a
      ><a name="22474" class="Symbol"
      >)</a
      ><a name="22475"
      > </a
      ><a name="22476" class="Symbol"
      >()</a
      ><a name="22478"
      >
</a
      ><a name="22479" href="StlcProp.html#21140" class="Function"
      >preservation</a
      ><a name="22491"
      > </a
      ><a name="22492" class="Symbol"
      >(</a
      ><a name="22493" href="Stlc.html#3210" class="InductiveConstructor"
      >&#8658;-I</a
      ><a name="22496"
      > </a
      ><a name="22497" href="StlcProp.html#22497" class="Bound"
      >&#8866;N</a
      ><a name="22499" class="Symbol"
      >)</a
      ><a name="22500"
      > </a
      ><a name="22501" class="Symbol"
      >()</a
      ><a name="22503"
      >
</a
      ><a name="22504" href="StlcProp.html#21140" class="Function"
      >preservation</a
      ><a name="22516"
      > </a
      ><a name="22517" class="Symbol"
      >(</a
      ><a name="22518" href="Stlc.html#3287" class="InductiveConstructor"
      >&#8658;-E</a
      ><a name="22521"
      > </a
      ><a name="22522" class="Symbol"
      >(</a
      ><a name="22523" href="Stlc.html#3210" class="InductiveConstructor"
      >&#8658;-I</a
      ><a name="22526"
      > </a
      ><a name="22527" href="StlcProp.html#22527" class="Bound"
      >&#8866;N</a
      ><a name="22529" class="Symbol"
      >)</a
      ><a name="22530"
      > </a
      ><a name="22531" href="StlcProp.html#22531" class="Bound"
      >&#8866;V</a
      ><a name="22533" class="Symbol"
      >)</a
      ><a name="22534"
      > </a
      ><a name="22535" class="Symbol"
      >(</a
      ><a name="22536" href="Stlc.html#1794" class="InductiveConstructor"
      >&#946;&#955;&#183;</a
      ><a name="22539"
      > </a
      ><a name="22540" href="StlcProp.html#22540" class="Bound"
      >valueV</a
      ><a name="22546" class="Symbol"
      >)</a
      ><a name="22547"
      > </a
      ><a name="22548" class="Symbol"
      >=</a
      ><a name="22549"
      > </a
      ><a name="22550" href="StlcProp.html#16218" class="Function"
      >preservation-[:=]</a
      ><a name="22567"
      > </a
      ><a name="22568" href="StlcProp.html#22527" class="Bound"
      >&#8866;N</a
      ><a name="22570"
      > </a
      ><a name="22571" href="StlcProp.html#22531" class="Bound"
      >&#8866;V</a
      ><a name="22573"
      >
</a
      ><a name="22574" href="StlcProp.html#21140" class="Function"
      >preservation</a
      ><a name="22586"
      > </a
      ><a name="22587" class="Symbol"
      >(</a
      ><a name="22588" href="Stlc.html#3287" class="InductiveConstructor"
      >&#8658;-E</a
      ><a name="22591"
      > </a
      ><a name="22592" href="StlcProp.html#22592" class="Bound"
      >&#8866;L</a
      ><a name="22594"
      > </a
      ><a name="22595" href="StlcProp.html#22595" class="Bound"
      >&#8866;M</a
      ><a name="22597" class="Symbol"
      >)</a
      ><a name="22598"
      > </a
      ><a name="22599" class="Symbol"
      >(</a
      ><a name="22600" href="Stlc.html#1864" class="InductiveConstructor"
      >&#958;&#183;&#8321;</a
      ><a name="22603"
      > </a
      ><a name="22604" href="StlcProp.html#22604" class="Bound"
      >L&#10233;L&#8242;</a
      ><a name="22608" class="Symbol"
      >)</a
      ><a name="22609"
      > </a
      ><a name="22610" class="Keyword"
      >with</a
      ><a name="22614"
      > </a
      ><a name="22615" href="StlcProp.html#21140" class="Function"
      >preservation</a
      ><a name="22627"
      > </a
      ><a name="22628" href="StlcProp.html#22592" class="Bound"
      >&#8866;L</a
      ><a name="22630"
      > </a
      ><a name="22631" href="StlcProp.html#22604" class="Bound"
      >L&#10233;L&#8242;</a
      ><a name="22635"
      >
</a
      ><a name="22636" class="Symbol"
      >...|</a
      ><a name="22640"
      > </a
      ><a name="22641" href="StlcProp.html#22641" class="Bound"
      >&#8866;L&#8242;</a
      ><a name="22644"
      > </a
      ><a name="22645" class="Symbol"
      >=</a
      ><a name="22646"
      > </a
      ><a name="22647" href="Stlc.html#3287" class="InductiveConstructor"
      >&#8658;-E</a
      ><a name="22650"
      > </a
      ><a name="22651" href="StlcProp.html#22641" class="Bound"
      >&#8866;L&#8242;</a
      ><a name="22654"
      > </a
      ><a name="22655" href="StlcProp.html#22595" class="Bound"
      >&#8866;M</a
      ><a name="22657"
      >
</a
      ><a name="22658" href="StlcProp.html#21140" class="Function"
      >preservation</a
      ><a name="22670"
      > </a
      ><a name="22671" class="Symbol"
      >(</a
      ><a name="22672" href="Stlc.html#3287" class="InductiveConstructor"
      >&#8658;-E</a
      ><a name="22675"
      > </a
      ><a name="22676" href="StlcProp.html#22676" class="Bound"
      >&#8866;L</a
      ><a name="22678"
      > </a
      ><a name="22679" href="StlcProp.html#22679" class="Bound"
      >&#8866;M</a
      ><a name="22681" class="Symbol"
      >)</a
      ><a name="22682"
      > </a
      ><a name="22683" class="Symbol"
      >(</a
      ><a name="22684" href="Stlc.html#1917" class="InductiveConstructor"
      >&#958;&#183;&#8322;</a
      ><a name="22687"
      > </a
      ><a name="22688" href="StlcProp.html#22688" class="Bound"
      >valueL</a
      ><a name="22694"
      > </a
      ><a name="22695" href="StlcProp.html#22695" class="Bound"
      >M&#10233;M&#8242;</a
      ><a name="22699" class="Symbol"
      >)</a
      ><a name="22700"
      > </a
      ><a name="22701" class="Keyword"
      >with</a
      ><a name="22705"
      > </a
      ><a name="22706" href="StlcProp.html#21140" class="Function"
      >preservation</a
      ><a name="22718"
      > </a
      ><a name="22719" href="StlcProp.html#22679" class="Bound"
      >&#8866;M</a
      ><a name="22721"
      > </a
      ><a name="22722" href="StlcProp.html#22695" class="Bound"
      >M&#10233;M&#8242;</a
      ><a name="22726"
      >
</a
      ><a name="22727" class="Symbol"
      >...|</a
      ><a name="22731"
      > </a
      ><a name="22732" href="StlcProp.html#22732" class="Bound"
      >&#8866;M&#8242;</a
      ><a name="22735"
      > </a
      ><a name="22736" class="Symbol"
      >=</a
      ><a name="22737"
      > </a
      ><a name="22738" href="Stlc.html#3287" class="InductiveConstructor"
      >&#8658;-E</a
      ><a name="22741"
      > </a
      ><a name="22742" href="StlcProp.html#22676" class="Bound"
      >&#8866;L</a
      ><a name="22744"
      > </a
      ><a name="22745" href="StlcProp.html#22732" class="Bound"
      >&#8866;M&#8242;</a
      ><a name="22748"
      >
</a
      ><a name="22749" href="StlcProp.html#21140" class="Function"
      >preservation</a
      ><a name="22761"
      > </a
      ><a name="22762" href="Stlc.html#3365" class="InductiveConstructor"
      >&#120121;-I&#8321;</a
      ><a name="22766"
      > </a
      ><a name="22767" class="Symbol"
      >()</a
      ><a name="22769"
      >
</a
      ><a name="22770" href="StlcProp.html#21140" class="Function"
      >preservation</a
      ><a name="22782"
      > </a
      ><a name="22783" href="Stlc.html#3399" class="InductiveConstructor"
      >&#120121;-I&#8322;</a
      ><a name="22787"
      > </a
      ><a name="22788" class="Symbol"
      >()</a
      ><a name="22790"
      >
</a
      ><a name="22791" href="StlcProp.html#21140" class="Function"
      >preservation</a
      ><a name="22803"
      > </a
      ><a name="22804" class="Symbol"
      >(</a
      ><a name="22805" href="Stlc.html#3434" class="InductiveConstructor"
      >&#120121;-E</a
      ><a name="22808"
      > </a
      ><a name="22809" href="Stlc.html#3365" class="InductiveConstructor"
      >&#120121;-I&#8321;</a
      ><a name="22813"
      > </a
      ><a name="22814" href="StlcProp.html#22814" class="Bound"
      >&#8866;M</a
      ><a name="22816"
      > </a
      ><a name="22817" href="StlcProp.html#22817" class="Bound"
      >&#8866;N</a
      ><a name="22819" class="Symbol"
      >)</a
      ><a name="22820"
      > </a
      ><a name="22821" href="Stlc.html#1984" class="InductiveConstructor"
      >&#946;if-true</a
      ><a name="22829"
      > </a
      ><a name="22830" class="Symbol"
      >=</a
      ><a name="22831"
      > </a
      ><a name="22832" href="StlcProp.html#22814" class="Bound"
      >&#8866;M</a
      ><a name="22834"
      >
</a
      ><a name="22835" href="StlcProp.html#21140" class="Function"
      >preservation</a
      ><a name="22847"
      > </a
      ><a name="22848" class="Symbol"
      >(</a
      ><a name="22849" href="Stlc.html#3434" class="InductiveConstructor"
      >&#120121;-E</a
      ><a name="22852"
      > </a
      ><a name="22853" href="Stlc.html#3399" class="InductiveConstructor"
      >&#120121;-I&#8322;</a
      ><a name="22857"
      > </a
      ><a name="22858" href="StlcProp.html#22858" class="Bound"
      >&#8866;M</a
      ><a name="22860"
      > </a
      ><a name="22861" href="StlcProp.html#22861" class="Bound"
      >&#8866;N</a
      ><a name="22863" class="Symbol"
      >)</a
      ><a name="22864"
      > </a
      ><a name="22865" href="Stlc.html#2037" class="InductiveConstructor"
      >&#946;if-false</a
      ><a name="22874"
      > </a
      ><a name="22875" class="Symbol"
      >=</a
      ><a name="22876"
      > </a
      ><a name="22877" href="StlcProp.html#22861" class="Bound"
      >&#8866;N</a
      ><a name="22879"
      >
</a
      ><a name="22880" href="StlcProp.html#21140" class="Function"
      >preservation</a
      ><a name="22892"
      > </a
      ><a name="22893" class="Symbol"
      >(</a
      ><a name="22894" href="Stlc.html#3434" class="InductiveConstructor"
      >&#120121;-E</a
      ><a name="22897"
      > </a
      ><a name="22898" href="StlcProp.html#22898" class="Bound"
      >&#8866;L</a
      ><a name="22900"
      > </a
      ><a name="22901" href="StlcProp.html#22901" class="Bound"
      >&#8866;M</a
      ><a name="22903"
      > </a
      ><a name="22904" href="StlcProp.html#22904" class="Bound"
      >&#8866;N</a
      ><a name="22906" class="Symbol"
      >)</a
      ><a name="22907"
      > </a
      ><a name="22908" class="Symbol"
      >(</a
      ><a name="22909" href="Stlc.html#2092" class="InductiveConstructor"
      >&#958;if</a
      ><a name="22912"
      > </a
      ><a name="22913" href="StlcProp.html#22913" class="Bound"
      >L&#10233;L&#8242;</a
      ><a name="22917" class="Symbol"
      >)</a
      ><a name="22918"
      > </a
      ><a name="22919" class="Keyword"
      >with</a
      ><a name="22923"
      > </a
      ><a name="22924" href="StlcProp.html#21140" class="Function"
      >preservation</a
      ><a name="22936"
      > </a
      ><a name="22937" href="StlcProp.html#22898" class="Bound"
      >&#8866;L</a
      ><a name="22939"
      > </a
      ><a name="22940" href="StlcProp.html#22913" class="Bound"
      >L&#10233;L&#8242;</a
      ><a name="22944"
      >
</a
      ><a name="22945" class="Symbol"
      >...|</a
      ><a name="22949"
      > </a
      ><a name="22950" href="StlcProp.html#22950" class="Bound"
      >&#8866;L&#8242;</a
      ><a name="22953"
      > </a
      ><a name="22954" class="Symbol"
      >=</a
      ><a name="22955"
      > </a
      ><a name="22956" href="Stlc.html#3434" class="InductiveConstructor"
      >&#120121;-E</a
      ><a name="22959"
      > </a
      ><a name="22960" href="StlcProp.html#22950" class="Bound"
      >&#8866;L&#8242;</a
      ><a name="22963"
      > </a
      ><a name="22964" href="StlcProp.html#22901" class="Bound"
      >&#8866;M</a
      ><a name="22966"
      > </a
      ><a name="22967" href="StlcProp.html#22904" class="Bound"
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

<a name="23620" href="StlcProp.html#23620" class="Function"
      >Normal</a
      ><a name="23626"
      > </a
      ><a name="23627" class="Symbol"
      >:</a
      ><a name="23628"
      > </a
      ><a name="23629" href="Stlc.html#708" class="Datatype"
      >Term</a
      ><a name="23633"
      > </a
      ><a name="23634" class="Symbol"
      >&#8594;</a
      ><a name="23635"
      > </a
      ><a name="23636" class="PrimitiveType"
      >Set</a
      ><a name="23639"
      >
</a
      ><a name="23640" href="StlcProp.html#23620" class="Function"
      >Normal</a
      ><a name="23646"
      > </a
      ><a name="23647" href="StlcProp.html#23647" class="Bound"
      >M</a
      ><a name="23648"
      > </a
      ><a name="23649" class="Symbol"
      >=</a
      ><a name="23650"
      > </a
      ><a name="23651" class="Symbol"
      >&#8704;</a
      ><a name="23652"
      > </a
      ><a name="23653" class="Symbol"
      >{</a
      ><a name="23654" href="StlcProp.html#23654" class="Bound"
      >N</a
      ><a name="23655" class="Symbol"
      >}</a
      ><a name="23656"
      > </a
      ><a name="23657" class="Symbol"
      >&#8594;</a
      ><a name="23658"
      > </a
      ><a name="23659" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#414" class="Function Operator"
      >&#172;</a
      ><a name="23660"
      > </a
      ><a name="23661" class="Symbol"
      >(</a
      ><a name="23662" href="StlcProp.html#23647" class="Bound"
      >M</a
      ><a name="23663"
      > </a
      ><a name="23664" href="Stlc.html#1762" class="Datatype Operator"
      >&#10233;</a
      ><a name="23665"
      > </a
      ><a name="23666" href="StlcProp.html#23654" class="Bound"
      >N</a
      ><a name="23667" class="Symbol"
      >)</a
      ><a name="23668"
      >

</a
      ><a name="23670" href="StlcProp.html#23670" class="Function"
      >Stuck</a
      ><a name="23675"
      > </a
      ><a name="23676" class="Symbol"
      >:</a
      ><a name="23677"
      > </a
      ><a name="23678" href="Stlc.html#708" class="Datatype"
      >Term</a
      ><a name="23682"
      > </a
      ><a name="23683" class="Symbol"
      >&#8594;</a
      ><a name="23684"
      > </a
      ><a name="23685" class="PrimitiveType"
      >Set</a
      ><a name="23688"
      >
</a
      ><a name="23689" href="StlcProp.html#23670" class="Function"
      >Stuck</a
      ><a name="23694"
      > </a
      ><a name="23695" href="StlcProp.html#23695" class="Bound"
      >M</a
      ><a name="23696"
      > </a
      ><a name="23697" class="Symbol"
      >=</a
      ><a name="23698"
      > </a
      ><a name="23699" href="StlcProp.html#23620" class="Function"
      >Normal</a
      ><a name="23705"
      > </a
      ><a name="23706" href="StlcProp.html#23695" class="Bound"
      >M</a
      ><a name="23707"
      > </a
      ><a name="23708" href="https://agda.github.io/agda-stdlib/Data.Product.html#1073" class="Function Operator"
      >&#215;</a
      ><a name="23709"
      > </a
      ><a name="23710" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#414" class="Function Operator"
      >&#172;</a
      ><a name="23711"
      > </a
      ><a name="23712" href="Stlc.html#1105" class="Datatype"
      >Value</a
      ><a name="23717"
      > </a
      ><a name="23718" href="StlcProp.html#23695" class="Bound"
      >M</a
      ><a name="23719"
      >

</a
      ><a name="23721" class="Keyword"
      >postulate</a
      ><a name="23730"
      >
  </a
      ><a name="23733" href="StlcProp.html#23733" class="Postulate"
      >Soundness</a
      ><a name="23742"
      > </a
      ><a name="23743" class="Symbol"
      >:</a
      ><a name="23744"
      > </a
      ><a name="23745" class="Symbol"
      >&#8704;</a
      ><a name="23746"
      > </a
      ><a name="23747" class="Symbol"
      >{</a
      ><a name="23748" href="StlcProp.html#23748" class="Bound"
      >M</a
      ><a name="23749"
      > </a
      ><a name="23750" href="StlcProp.html#23750" class="Bound"
      >N</a
      ><a name="23751"
      > </a
      ><a name="23752" href="StlcProp.html#23752" class="Bound"
      >A</a
      ><a name="23753" class="Symbol"
      >}</a
      ><a name="23754"
      > </a
      ><a name="23755" class="Symbol"
      >&#8594;</a
      ><a name="23756"
      > </a
      ><a name="23757" href="Maps.html#10265" class="Function"
      >&#8709;</a
      ><a name="23758"
      > </a
      ><a name="23759" href="Stlc.html#3112" class="Datatype Operator"
      >&#8866;</a
      ><a name="23760"
      > </a
      ><a name="23761" href="StlcProp.html#23748" class="Bound"
      >M</a
      ><a name="23762"
      > </a
      ><a name="23763" href="Stlc.html#3112" class="Datatype Operator"
      >&#8758;</a
      ><a name="23764"
      > </a
      ><a name="23765" href="StlcProp.html#23752" class="Bound"
      >A</a
      ><a name="23766"
      > </a
      ><a name="23767" class="Symbol"
      >&#8594;</a
      ><a name="23768"
      > </a
      ><a name="23769" href="StlcProp.html#23748" class="Bound"
      >M</a
      ><a name="23770"
      > </a
      ><a name="23771" href="Stlc.html#2287" class="Datatype Operator"
      >&#10233;*</a
      ><a name="23773"
      > </a
      ><a name="23774" href="StlcProp.html#23750" class="Bound"
      >N</a
      ><a name="23775"
      > </a
      ><a name="23776" class="Symbol"
      >&#8594;</a
      ><a name="23777"
      > </a
      ><a name="23778" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#414" class="Function Operator"
      >&#172;</a
      ><a name="23779"
      > </a
      ><a name="23780" class="Symbol"
      >(</a
      ><a name="23781" href="StlcProp.html#23670" class="Function"
      >Stuck</a
      ><a name="23786"
      > </a
      ><a name="23787" href="StlcProp.html#23750" class="Bound"
      >N</a
      ><a name="23788" class="Symbol"
      >)</a
      >

</pre>

<div class="hidden">
<pre class="Agda">

<a name="23836" href="StlcProp.html#23836" class="Function"
      >Soundness&#8242;</a
      ><a name="23846"
      > </a
      ><a name="23847" class="Symbol"
      >:</a
      ><a name="23848"
      > </a
      ><a name="23849" class="Symbol"
      >&#8704;</a
      ><a name="23850"
      > </a
      ><a name="23851" class="Symbol"
      >{</a
      ><a name="23852" href="StlcProp.html#23852" class="Bound"
      >M</a
      ><a name="23853"
      > </a
      ><a name="23854" href="StlcProp.html#23854" class="Bound"
      >N</a
      ><a name="23855"
      > </a
      ><a name="23856" href="StlcProp.html#23856" class="Bound"
      >A</a
      ><a name="23857" class="Symbol"
      >}</a
      ><a name="23858"
      > </a
      ><a name="23859" class="Symbol"
      >&#8594;</a
      ><a name="23860"
      > </a
      ><a name="23861" href="Maps.html#10265" class="Function"
      >&#8709;</a
      ><a name="23862"
      > </a
      ><a name="23863" href="Stlc.html#3112" class="Datatype Operator"
      >&#8866;</a
      ><a name="23864"
      > </a
      ><a name="23865" href="StlcProp.html#23852" class="Bound"
      >M</a
      ><a name="23866"
      > </a
      ><a name="23867" href="Stlc.html#3112" class="Datatype Operator"
      >&#8758;</a
      ><a name="23868"
      > </a
      ><a name="23869" href="StlcProp.html#23856" class="Bound"
      >A</a
      ><a name="23870"
      > </a
      ><a name="23871" class="Symbol"
      >&#8594;</a
      ><a name="23872"
      > </a
      ><a name="23873" href="StlcProp.html#23852" class="Bound"
      >M</a
      ><a name="23874"
      > </a
      ><a name="23875" href="Stlc.html#2287" class="Datatype Operator"
      >&#10233;*</a
      ><a name="23877"
      > </a
      ><a name="23878" href="StlcProp.html#23854" class="Bound"
      >N</a
      ><a name="23879"
      > </a
      ><a name="23880" class="Symbol"
      >&#8594;</a
      ><a name="23881"
      > </a
      ><a name="23882" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#414" class="Function Operator"
      >&#172;</a
      ><a name="23883"
      > </a
      ><a name="23884" class="Symbol"
      >(</a
      ><a name="23885" href="StlcProp.html#23670" class="Function"
      >Stuck</a
      ><a name="23890"
      > </a
      ><a name="23891" href="StlcProp.html#23854" class="Bound"
      >N</a
      ><a name="23892" class="Symbol"
      >)</a
      ><a name="23893"
      >
</a
      ><a name="23894" href="StlcProp.html#23836" class="Function"
      >Soundness&#8242;</a
      ><a name="23904"
      > </a
      ><a name="23905" href="StlcProp.html#23905" class="Bound"
      >&#8866;M</a
      ><a name="23907"
      > </a
      ><a name="23908" class="Symbol"
      >(</a
      ><a name="23909" href="StlcProp.html#23909" class="Bound"
      >M</a
      ><a name="23910"
      > </a
      ><a name="23911" href="Stlc.html#2320" class="InductiveConstructor Operator"
      >&#8718;</a
      ><a name="23912" class="Symbol"
      >)</a
      ><a name="23913"
      > </a
      ><a name="23914" class="Symbol"
      >(</a
      ><a name="23915" href="StlcProp.html#23915" class="Bound"
      >&#172;M&#10233;N</a
      ><a name="23919"
      > </a
      ><a name="23920" href="https://agda.github.io/agda-stdlib/Data.Product.html#509" class="InductiveConstructor Operator"
      >,</a
      ><a name="23921"
      > </a
      ><a name="23922" href="StlcProp.html#23922" class="Bound"
      >&#172;ValueM</a
      ><a name="23929" class="Symbol"
      >)</a
      ><a name="23930"
      > </a
      ><a name="23931" class="Keyword"
      >with</a
      ><a name="23935"
      > </a
      ><a name="23936" href="StlcProp.html#2024" class="Function"
      >progress</a
      ><a name="23944"
      > </a
      ><a name="23945" href="StlcProp.html#23905" class="Bound"
      >&#8866;M</a
      ><a name="23947"
      >
</a
      ><a name="23948" class="Symbol"
      >...</a
      ><a name="23951"
      > </a
      ><a name="23952" class="Symbol"
      >|</a
      ><a name="23953"
      > </a
      ><a name="23954" href="StlcProp.html#1947" class="InductiveConstructor"
      >steps</a
      ><a name="23959"
      > </a
      ><a name="23960" href="StlcProp.html#23960" class="Bound"
      >M&#10233;N</a
      ><a name="23963"
      >  </a
      ><a name="23965" class="Symbol"
      >=</a
      ><a name="23966"
      > </a
      ><a name="23967" href="StlcProp.html#23915" class="Bound"
      >&#172;M&#10233;N</a
      ><a name="23971"
      > </a
      ><a name="23972" href="StlcProp.html#23960" class="Bound"
      >M&#10233;N</a
      ><a name="23975"
      >
</a
      ><a name="23976" class="Symbol"
      >...</a
      ><a name="23979"
      > </a
      ><a name="23980" class="Symbol"
      >|</a
      ><a name="23981"
      > </a
      ><a name="23982" href="StlcProp.html#1986" class="InductiveConstructor"
      >done</a
      ><a name="23986"
      > </a
      ><a name="23987" href="StlcProp.html#23987" class="Bound"
      >ValueM</a
      ><a name="23993"
      >  </a
      ><a name="23995" class="Symbol"
      >=</a
      ><a name="23996"
      > </a
      ><a name="23997" href="StlcProp.html#23922" class="Bound"
      >&#172;ValueM</a
      ><a name="24004"
      > </a
      ><a name="24005" href="StlcProp.html#23987" class="Bound"
      >ValueM</a
      ><a name="24011"
      >
</a
      ><a name="24012" href="StlcProp.html#23836" class="Function"
      >Soundness&#8242;</a
      ><a name="24022"
      > </a
      ><a name="24023" class="Symbol"
      >{</a
      ><a name="24024" href="StlcProp.html#24024" class="Bound"
      >L</a
      ><a name="24025" class="Symbol"
      >}</a
      ><a name="24026"
      > </a
      ><a name="24027" class="Symbol"
      >{</a
      ><a name="24028" href="StlcProp.html#24028" class="Bound"
      >N</a
      ><a name="24029" class="Symbol"
      >}</a
      ><a name="24030"
      > </a
      ><a name="24031" class="Symbol"
      >{</a
      ><a name="24032" href="StlcProp.html#24032" class="Bound"
      >A</a
      ><a name="24033" class="Symbol"
      >}</a
      ><a name="24034"
      > </a
      ><a name="24035" href="StlcProp.html#24035" class="Bound"
      >&#8866;L</a
      ><a name="24037"
      > </a
      ><a name="24038" class="Symbol"
      >(</a
      ><a name="24039" href="Stlc.html#2340" class="InductiveConstructor Operator"
      >_&#10233;&#10216;_&#10217;_</a
      ><a name="24045"
      > </a
      ><a name="24046" class="DottedPattern Symbol"
      >.</a
      ><a name="24047" href="StlcProp.html#24024" class="DottedPattern Bound"
      >L</a
      ><a name="24048"
      > </a
      ><a name="24049" class="Symbol"
      >{</a
      ><a name="24050" href="StlcProp.html#24050" class="Bound"
      >M</a
      ><a name="24051" class="Symbol"
      >}</a
      ><a name="24052"
      > </a
      ><a name="24053" class="Symbol"
      >{</a
      ><a name="24054" class="DottedPattern Symbol"
      >.</a
      ><a name="24055" href="StlcProp.html#24028" class="DottedPattern Bound"
      >N</a
      ><a name="24056" class="Symbol"
      >}</a
      ><a name="24057"
      > </a
      ><a name="24058" href="StlcProp.html#24058" class="Bound"
      >L&#10233;M</a
      ><a name="24061"
      > </a
      ><a name="24062" href="StlcProp.html#24062" class="Bound"
      >M&#10233;*N</a
      ><a name="24066" class="Symbol"
      >)</a
      ><a name="24067"
      > </a
      ><a name="24068" class="Symbol"
      >=</a
      ><a name="24069"
      > </a
      ><a name="24070" href="StlcProp.html#23836" class="Function"
      >Soundness&#8242;</a
      ><a name="24080"
      > </a
      ><a name="24081" href="StlcProp.html#24099" class="Function"
      >&#8866;M</a
      ><a name="24083"
      > </a
      ><a name="24084" href="StlcProp.html#24062" class="Bound"
      >M&#10233;*N</a
      ><a name="24088"
      >
  </a
      ><a name="24091" class="Keyword"
      >where</a
      ><a name="24096"
      >
  </a
      ><a name="24099" href="StlcProp.html#24099" class="Function"
      >&#8866;M</a
      ><a name="24101"
      > </a
      ><a name="24102" class="Symbol"
      >:</a
      ><a name="24103"
      > </a
      ><a name="24104" href="Maps.html#10265" class="Function"
      >&#8709;</a
      ><a name="24105"
      > </a
      ><a name="24106" href="Stlc.html#3112" class="Datatype Operator"
      >&#8866;</a
      ><a name="24107"
      > </a
      ><a name="24108" href="StlcProp.html#24050" class="Bound"
      >M</a
      ><a name="24109"
      > </a
      ><a name="24110" href="Stlc.html#3112" class="Datatype Operator"
      >&#8758;</a
      ><a name="24111"
      > </a
      ><a name="24112" href="StlcProp.html#24032" class="Bound"
      >A</a
      ><a name="24113"
      >
  </a
      ><a name="24116" href="StlcProp.html#24099" class="Function"
      >&#8866;M</a
      ><a name="24118"
      > </a
      ><a name="24119" class="Symbol"
      >=</a
      ><a name="24120"
      > </a
      ><a name="24121" href="StlcProp.html#21140" class="Function"
      >preservation</a
      ><a name="24133"
      > </a
      ><a name="24134" href="StlcProp.html#24035" class="Bound"
      >&#8866;L</a
      ><a name="24136"
      > </a
      ><a name="24137" href="StlcProp.html#24058" class="Bound"
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

<a name="28553" class="Keyword"
      >data</a
      ><a name="28557"
      > </a
      ><a name="28558" href="StlcProp.html#28558" class="Datatype"
      >Type&#8242;</a
      ><a name="28563"
      > </a
      ><a name="28564" class="Symbol"
      >:</a
      ><a name="28565"
      > </a
      ><a name="28566" class="PrimitiveType"
      >Set</a
      ><a name="28569"
      > </a
      ><a name="28570" class="Keyword"
      >where</a
      ><a name="28575"
      >
  </a
      ><a name="28578" href="StlcProp.html#28578" class="InductiveConstructor Operator"
      >_&#8658;_</a
      ><a name="28581"
      > </a
      ><a name="28582" class="Symbol"
      >:</a
      ><a name="28583"
      > </a
      ><a name="28584" href="StlcProp.html#28558" class="Datatype"
      >Type&#8242;</a
      ><a name="28589"
      > </a
      ><a name="28590" class="Symbol"
      >&#8594;</a
      ><a name="28591"
      > </a
      ><a name="28592" href="StlcProp.html#28558" class="Datatype"
      >Type&#8242;</a
      ><a name="28597"
      > </a
      ><a name="28598" class="Symbol"
      >&#8594;</a
      ><a name="28599"
      > </a
      ><a name="28600" href="StlcProp.html#28558" class="Datatype"
      >Type&#8242;</a
      ><a name="28605"
      >
  </a
      ><a name="28608" href="StlcProp.html#28608" class="InductiveConstructor"
      >&#8469;</a
      ><a name="28609"
      > </a
      ><a name="28610" class="Symbol"
      >:</a
      ><a name="28611"
      > </a
      ><a name="28612" href="StlcProp.html#28558" class="Datatype"
      >Type&#8242;</a
      >

</pre>

To terms, we add natural number constants, along with
plus, minus, and testing for zero.

<pre class="Agda">

<a name="28733" class="Keyword"
      >data</a
      ><a name="28737"
      > </a
      ><a name="28738" href="StlcProp.html#28738" class="Datatype"
      >Term&#8242;</a
      ><a name="28743"
      > </a
      ><a name="28744" class="Symbol"
      >:</a
      ><a name="28745"
      > </a
      ><a name="28746" class="PrimitiveType"
      >Set</a
      ><a name="28749"
      > </a
      ><a name="28750" class="Keyword"
      >where</a
      ><a name="28755"
      >
  </a
      ><a name="28758" href="StlcProp.html#28758" class="InductiveConstructor Operator"
      >`_</a
      ><a name="28760"
      > </a
      ><a name="28761" class="Symbol"
      >:</a
      ><a name="28762"
      > </a
      ><a name="28763" href="Maps.html#2171" class="Datatype"
      >Id</a
      ><a name="28765"
      > </a
      ><a name="28766" class="Symbol"
      >&#8594;</a
      ><a name="28767"
      > </a
      ><a name="28768" href="StlcProp.html#28738" class="Datatype"
      >Term&#8242;</a
      ><a name="28773"
      >
  </a
      ><a name="28776" href="StlcProp.html#28776" class="InductiveConstructor Operator"
      >&#955;[_&#8758;_]_</a
      ><a name="28783"
      > </a
      ><a name="28784" class="Symbol"
      >:</a
      ><a name="28785"
      > </a
      ><a name="28786" href="Maps.html#2171" class="Datatype"
      >Id</a
      ><a name="28788"
      > </a
      ><a name="28789" class="Symbol"
      >&#8594;</a
      ><a name="28790"
      > </a
      ><a name="28791" href="StlcProp.html#28558" class="Datatype"
      >Type&#8242;</a
      ><a name="28796"
      > </a
      ><a name="28797" class="Symbol"
      >&#8594;</a
      ><a name="28798"
      > </a
      ><a name="28799" href="StlcProp.html#28738" class="Datatype"
      >Term&#8242;</a
      ><a name="28804"
      > </a
      ><a name="28805" class="Symbol"
      >&#8594;</a
      ><a name="28806"
      > </a
      ><a name="28807" href="StlcProp.html#28738" class="Datatype"
      >Term&#8242;</a
      ><a name="28812"
      >
  </a
      ><a name="28815" href="StlcProp.html#28815" class="InductiveConstructor Operator"
      >_&#183;_</a
      ><a name="28818"
      > </a
      ><a name="28819" class="Symbol"
      >:</a
      ><a name="28820"
      > </a
      ><a name="28821" href="StlcProp.html#28738" class="Datatype"
      >Term&#8242;</a
      ><a name="28826"
      > </a
      ><a name="28827" class="Symbol"
      >&#8594;</a
      ><a name="28828"
      > </a
      ><a name="28829" href="StlcProp.html#28738" class="Datatype"
      >Term&#8242;</a
      ><a name="28834"
      > </a
      ><a name="28835" class="Symbol"
      >&#8594;</a
      ><a name="28836"
      > </a
      ><a name="28837" href="StlcProp.html#28738" class="Datatype"
      >Term&#8242;</a
      ><a name="28842"
      >
  </a
      ><a name="28845" href="StlcProp.html#28845" class="InductiveConstructor Operator"
      >&#8246;_</a
      ><a name="28847"
      > </a
      ><a name="28848" class="Symbol"
      >:</a
      ><a name="28849"
      > </a
      ><a name="28850" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#97" class="Datatype"
      >Data.Nat.&#8469;</a
      ><a name="28860"
      > </a
      ><a name="28861" class="Symbol"
      >&#8594;</a
      ><a name="28862"
      > </a
      ><a name="28863" href="StlcProp.html#28738" class="Datatype"
      >Term&#8242;</a
      ><a name="28868"
      >
  </a
      ><a name="28871" href="StlcProp.html#28871" class="InductiveConstructor Operator"
      >_+_</a
      ><a name="28874"
      > </a
      ><a name="28875" class="Symbol"
      >:</a
      ><a name="28876"
      > </a
      ><a name="28877" href="StlcProp.html#28738" class="Datatype"
      >Term&#8242;</a
      ><a name="28882"
      > </a
      ><a name="28883" class="Symbol"
      >&#8594;</a
      ><a name="28884"
      > </a
      ><a name="28885" href="StlcProp.html#28738" class="Datatype"
      >Term&#8242;</a
      ><a name="28890"
      > </a
      ><a name="28891" class="Symbol"
      >&#8594;</a
      ><a name="28892"
      > </a
      ><a name="28893" href="StlcProp.html#28738" class="Datatype"
      >Term&#8242;</a
      ><a name="28898"
      >
  </a
      ><a name="28901" href="StlcProp.html#28901" class="InductiveConstructor Operator"
      >_-_</a
      ><a name="28904"
      > </a
      ><a name="28905" class="Symbol"
      >:</a
      ><a name="28906"
      > </a
      ><a name="28907" href="StlcProp.html#28738" class="Datatype"
      >Term&#8242;</a
      ><a name="28912"
      > </a
      ><a name="28913" class="Symbol"
      >&#8594;</a
      ><a name="28914"
      > </a
      ><a name="28915" href="StlcProp.html#28738" class="Datatype"
      >Term&#8242;</a
      ><a name="28920"
      > </a
      ><a name="28921" class="Symbol"
      >&#8594;</a
      ><a name="28922"
      > </a
      ><a name="28923" href="StlcProp.html#28738" class="Datatype"
      >Term&#8242;</a
      ><a name="28928"
      >
  </a
      ><a name="28931" href="StlcProp.html#28931" class="InductiveConstructor Operator"
      >if0_then_else_</a
      ><a name="28945"
      > </a
      ><a name="28946" class="Symbol"
      >:</a
      ><a name="28947"
      > </a
      ><a name="28948" href="StlcProp.html#28738" class="Datatype"
      >Term&#8242;</a
      ><a name="28953"
      > </a
      ><a name="28954" class="Symbol"
      >&#8594;</a
      ><a name="28955"
      > </a
      ><a name="28956" href="StlcProp.html#28738" class="Datatype"
      >Term&#8242;</a
      ><a name="28961"
      > </a
      ><a name="28962" class="Symbol"
      >&#8594;</a
      ><a name="28963"
      > </a
      ><a name="28964" href="StlcProp.html#28738" class="Datatype"
      >Term&#8242;</a
      ><a name="28969"
      > </a
      ><a name="28970" class="Symbol"
      >&#8594;</a
      ><a name="28971"
      > </a
      ><a name="28972" href="StlcProp.html#28738" class="Datatype"
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

