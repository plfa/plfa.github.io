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
      >
</a
      ><a name="627" class="Keyword"
      >open</a
      ><a name="631"
      > </a
      ><a name="632" class="Module"
      >Maps.</a
      ><a name="637" href="Maps.html#10221" class="Module"
      >PartialMap</a
      ><a name="647"
      > </a
      ><a name="648" class="Keyword"
      >using</a
      ><a name="653"
      > </a
      ><a name="654" class="Symbol"
      >(</a
      ><a name="655" href="Maps.html#10265" class="Function"
      >&#8709;</a
      ><a name="656" class="Symbol"
      >;</a
      ><a name="657"
      > </a
      ><a name="658" href="Maps.html#10573" class="Function"
      >apply-&#8709;</a
      ><a name="665" class="Symbol"
      >;</a
      ><a name="666"
      > </a
      ><a name="667" href="Maps.html#11491" class="Function"
      >update-permute</a
      ><a name="681" class="Symbol"
      >)</a
      ><a name="682"
      > </a
      ><a name="683" class="Keyword"
      >renaming</a
      ><a name="691"
      > </a
      ><a name="692" class="Symbol"
      >(</a
      ><a name="693" href="Maps.html#10368" class="Function Operator"
      >_,_&#8614;_</a
      ><a name="698"
      > </a
      ><a name="699" class="Symbol"
      >to</a
      ><a name="701"
      > </a
      ><a name="702" href="Maps.html#10368" class="Function Operator"
      >_,_&#8758;_</a
      ><a name="707" class="Symbol"
      >)</a
      ><a name="708"
      >
</a
      ><a name="709" class="Keyword"
      >open</a
      ><a name="713"
      > </a
      ><a name="714" class="Keyword"
      >import</a
      ><a name="720"
      > </a
      ><a name="721" class="Module"
      >Stlc</a
      >

</pre>


## Canonical Forms

As we saw for the simple calculus in Chapter [Types]({{ "Types" | relative_url }}),
the first step in establishing basic properties of reduction and typing
is to identify the possible _canonical forms_ (i.e., well-typed closed values)
belonging to each type.  For function types the canonical forms are lambda-abstractions,
while for boolean types they are values `true` and `false`.  

<pre class="Agda">

<a name="1159" class="Keyword"
      >data</a
      ><a name="1163"
      > </a
      ><a name="1164" href="StlcProp.html#1164" class="Datatype Operator"
      >canonical_for_</a
      ><a name="1178"
      > </a
      ><a name="1179" class="Symbol"
      >:</a
      ><a name="1180"
      > </a
      ><a name="1181" href="Stlc.html#708" class="Datatype"
      >Term</a
      ><a name="1185"
      > </a
      ><a name="1186" class="Symbol"
      >&#8594;</a
      ><a name="1187"
      > </a
      ><a name="1188" href="Stlc.html#590" class="Datatype"
      >Type</a
      ><a name="1192"
      > </a
      ><a name="1193" class="Symbol"
      >&#8594;</a
      ><a name="1194"
      > </a
      ><a name="1195" class="PrimitiveType"
      >Set</a
      ><a name="1198"
      > </a
      ><a name="1199" class="Keyword"
      >where</a
      ><a name="1204"
      >
  </a
      ><a name="1207" href="StlcProp.html#1207" class="InductiveConstructor"
      >canonical-&#955;</a
      ><a name="1218"
      > </a
      ><a name="1219" class="Symbol"
      >:</a
      ><a name="1220"
      > </a
      ><a name="1221" class="Symbol"
      >&#8704;</a
      ><a name="1222"
      > </a
      ><a name="1223" class="Symbol"
      >{</a
      ><a name="1224" href="StlcProp.html#1224" class="Bound"
      >x</a
      ><a name="1225"
      > </a
      ><a name="1226" href="StlcProp.html#1226" class="Bound"
      >A</a
      ><a name="1227"
      > </a
      ><a name="1228" href="StlcProp.html#1228" class="Bound"
      >N</a
      ><a name="1229"
      > </a
      ><a name="1230" href="StlcProp.html#1230" class="Bound"
      >B</a
      ><a name="1231" class="Symbol"
      >}</a
      ><a name="1232"
      > </a
      ><a name="1233" class="Symbol"
      >&#8594;</a
      ><a name="1234"
      > </a
      ><a name="1235" href="StlcProp.html#1164" class="Datatype Operator"
      >canonical</a
      ><a name="1244"
      > </a
      ><a name="1245" class="Symbol"
      >(</a
      ><a name="1246" href="Stlc.html#743" class="InductiveConstructor Operator"
      >&#955;[</a
      ><a name="1248"
      > </a
      ><a name="1249" href="StlcProp.html#1224" class="Bound"
      >x</a
      ><a name="1250"
      > </a
      ><a name="1251" href="Stlc.html#743" class="InductiveConstructor Operator"
      >&#8758;</a
      ><a name="1252"
      > </a
      ><a name="1253" href="StlcProp.html#1226" class="Bound"
      >A</a
      ><a name="1254"
      > </a
      ><a name="1255" href="Stlc.html#743" class="InductiveConstructor Operator"
      >]</a
      ><a name="1256"
      > </a
      ><a name="1257" href="StlcProp.html#1228" class="Bound"
      >N</a
      ><a name="1258" class="Symbol"
      >)</a
      ><a name="1259"
      > </a
      ><a name="1260" href="StlcProp.html#1164" class="Datatype Operator"
      >for</a
      ><a name="1263"
      > </a
      ><a name="1264" class="Symbol"
      >(</a
      ><a name="1265" href="StlcProp.html#1226" class="Bound"
      >A</a
      ><a name="1266"
      > </a
      ><a name="1267" href="Stlc.html#620" class="InductiveConstructor Operator"
      >&#8658;</a
      ><a name="1268"
      > </a
      ><a name="1269" href="StlcProp.html#1230" class="Bound"
      >B</a
      ><a name="1270" class="Symbol"
      >)</a
      ><a name="1271"
      >
  </a
      ><a name="1274" href="StlcProp.html#1274" class="InductiveConstructor"
      >canonical-true</a
      ><a name="1288"
      > </a
      ><a name="1289" class="Symbol"
      >:</a
      ><a name="1290"
      > </a
      ><a name="1291" href="StlcProp.html#1164" class="Datatype Operator"
      >canonical</a
      ><a name="1300"
      > </a
      ><a name="1301" href="Stlc.html#806" class="InductiveConstructor"
      >true</a
      ><a name="1305"
      > </a
      ><a name="1306" href="StlcProp.html#1164" class="Datatype Operator"
      >for</a
      ><a name="1309"
      > </a
      ><a name="1310" href="Stlc.html#609" class="InductiveConstructor"
      >&#120121;</a
      ><a name="1311"
      >
  </a
      ><a name="1314" href="StlcProp.html#1314" class="InductiveConstructor"
      >canonical-false</a
      ><a name="1329"
      > </a
      ><a name="1330" class="Symbol"
      >:</a
      ><a name="1331"
      > </a
      ><a name="1332" href="StlcProp.html#1164" class="Datatype Operator"
      >canonical</a
      ><a name="1341"
      > </a
      ><a name="1342" href="Stlc.html#820" class="InductiveConstructor"
      >false</a
      ><a name="1347"
      > </a
      ><a name="1348" href="StlcProp.html#1164" class="Datatype Operator"
      >for</a
      ><a name="1351"
      > </a
      ><a name="1352" href="Stlc.html#609" class="InductiveConstructor"
      >&#120121;</a
      ><a name="1353"
      >

</a
      ><a name="1355" href="StlcProp.html#1355" class="Function"
      >canonicalFormsLemma</a
      ><a name="1374"
      > </a
      ><a name="1375" class="Symbol"
      >:</a
      ><a name="1376"
      > </a
      ><a name="1377" class="Symbol"
      >&#8704;</a
      ><a name="1378"
      > </a
      ><a name="1379" class="Symbol"
      >{</a
      ><a name="1380" href="StlcProp.html#1380" class="Bound"
      >L</a
      ><a name="1381"
      > </a
      ><a name="1382" href="StlcProp.html#1382" class="Bound"
      >A</a
      ><a name="1383" class="Symbol"
      >}</a
      ><a name="1384"
      > </a
      ><a name="1385" class="Symbol"
      >&#8594;</a
      ><a name="1386"
      > </a
      ><a name="1387" href="Maps.html#10265" class="Function"
      >&#8709;</a
      ><a name="1388"
      > </a
      ><a name="1389" href="Stlc.html#3112" class="Datatype Operator"
      >&#8866;</a
      ><a name="1390"
      > </a
      ><a name="1391" href="StlcProp.html#1380" class="Bound"
      >L</a
      ><a name="1392"
      > </a
      ><a name="1393" href="Stlc.html#3112" class="Datatype Operator"
      >&#8758;</a
      ><a name="1394"
      > </a
      ><a name="1395" href="StlcProp.html#1382" class="Bound"
      >A</a
      ><a name="1396"
      > </a
      ><a name="1397" class="Symbol"
      >&#8594;</a
      ><a name="1398"
      > </a
      ><a name="1399" href="Stlc.html#1105" class="Datatype"
      >Value</a
      ><a name="1404"
      > </a
      ><a name="1405" href="StlcProp.html#1380" class="Bound"
      >L</a
      ><a name="1406"
      > </a
      ><a name="1407" class="Symbol"
      >&#8594;</a
      ><a name="1408"
      > </a
      ><a name="1409" href="StlcProp.html#1164" class="Datatype Operator"
      >canonical</a
      ><a name="1418"
      > </a
      ><a name="1419" href="StlcProp.html#1380" class="Bound"
      >L</a
      ><a name="1420"
      > </a
      ><a name="1421" href="StlcProp.html#1164" class="Datatype Operator"
      >for</a
      ><a name="1424"
      > </a
      ><a name="1425" href="StlcProp.html#1382" class="Bound"
      >A</a
      ><a name="1426"
      >
</a
      ><a name="1427" href="StlcProp.html#1355" class="Function"
      >canonicalFormsLemma</a
      ><a name="1446"
      > </a
      ><a name="1447" class="Symbol"
      >(</a
      ><a name="1448" href="Stlc.html#3156" class="InductiveConstructor"
      >Ax</a
      ><a name="1450"
      > </a
      ><a name="1451" class="Symbol"
      >())</a
      ><a name="1454"
      > </a
      ><a name="1455" class="Symbol"
      >()</a
      ><a name="1457"
      >
</a
      ><a name="1458" href="StlcProp.html#1355" class="Function"
      >canonicalFormsLemma</a
      ><a name="1477"
      > </a
      ><a name="1478" class="Symbol"
      >(</a
      ><a name="1479" href="Stlc.html#3210" class="InductiveConstructor"
      >&#8658;-I</a
      ><a name="1482"
      > </a
      ><a name="1483" href="StlcProp.html#1483" class="Bound"
      >&#8866;N</a
      ><a name="1485" class="Symbol"
      >)</a
      ><a name="1486"
      > </a
      ><a name="1487" href="Stlc.html#1132" class="InductiveConstructor"
      >value-&#955;</a
      ><a name="1494"
      > </a
      ><a name="1495" class="Symbol"
      >=</a
      ><a name="1496"
      > </a
      ><a name="1497" href="StlcProp.html#1207" class="InductiveConstructor"
      >canonical-&#955;</a
      ><a name="1508"
      >
</a
      ><a name="1509" href="StlcProp.html#1355" class="Function"
      >canonicalFormsLemma</a
      ><a name="1528"
      > </a
      ><a name="1529" class="Symbol"
      >(</a
      ><a name="1530" href="Stlc.html#3287" class="InductiveConstructor"
      >&#8658;-E</a
      ><a name="1533"
      > </a
      ><a name="1534" href="StlcProp.html#1534" class="Bound"
      >&#8866;L</a
      ><a name="1536"
      > </a
      ><a name="1537" href="StlcProp.html#1537" class="Bound"
      >&#8866;M</a
      ><a name="1539" class="Symbol"
      >)</a
      ><a name="1540"
      > </a
      ><a name="1541" class="Symbol"
      >()</a
      ><a name="1543"
      >
</a
      ><a name="1544" href="StlcProp.html#1355" class="Function"
      >canonicalFormsLemma</a
      ><a name="1563"
      > </a
      ><a name="1564" href="Stlc.html#3365" class="InductiveConstructor"
      >&#120121;-I&#8321;</a
      ><a name="1568"
      > </a
      ><a name="1569" href="Stlc.html#1181" class="InductiveConstructor"
      >value-true</a
      ><a name="1579"
      > </a
      ><a name="1580" class="Symbol"
      >=</a
      ><a name="1581"
      > </a
      ><a name="1582" href="StlcProp.html#1274" class="InductiveConstructor"
      >canonical-true</a
      ><a name="1596"
      >
</a
      ><a name="1597" href="StlcProp.html#1355" class="Function"
      >canonicalFormsLemma</a
      ><a name="1616"
      > </a
      ><a name="1617" href="Stlc.html#3399" class="InductiveConstructor"
      >&#120121;-I&#8322;</a
      ><a name="1621"
      > </a
      ><a name="1622" href="Stlc.html#1208" class="InductiveConstructor"
      >value-false</a
      ><a name="1633"
      > </a
      ><a name="1634" class="Symbol"
      >=</a
      ><a name="1635"
      > </a
      ><a name="1636" href="StlcProp.html#1314" class="InductiveConstructor"
      >canonical-false</a
      ><a name="1651"
      >
</a
      ><a name="1652" href="StlcProp.html#1355" class="Function"
      >canonicalFormsLemma</a
      ><a name="1671"
      > </a
      ><a name="1672" class="Symbol"
      >(</a
      ><a name="1673" href="Stlc.html#3434" class="InductiveConstructor"
      >&#120121;-E</a
      ><a name="1676"
      > </a
      ><a name="1677" href="StlcProp.html#1677" class="Bound"
      >&#8866;L</a
      ><a name="1679"
      > </a
      ><a name="1680" href="StlcProp.html#1680" class="Bound"
      >&#8866;M</a
      ><a name="1682"
      > </a
      ><a name="1683" href="StlcProp.html#1683" class="Bound"
      >&#8866;N</a
      ><a name="1685" class="Symbol"
      >)</a
      ><a name="1686"
      > </a
      ><a name="1687" class="Symbol"
      >()</a
      >

</pre>

## Progress

As before, the _progress_ theorem tells us that closed, well-typed
terms are not stuck: either a well-typed term can take a reduction
step or it is a value.

<pre class="Agda">

<a name="1886" class="Keyword"
      >data</a
      ><a name="1890"
      > </a
      ><a name="1891" href="StlcProp.html#1891" class="Datatype"
      >Progress</a
      ><a name="1899"
      > </a
      ><a name="1900" class="Symbol"
      >:</a
      ><a name="1901"
      > </a
      ><a name="1902" href="Stlc.html#708" class="Datatype"
      >Term</a
      ><a name="1906"
      > </a
      ><a name="1907" class="Symbol"
      >&#8594;</a
      ><a name="1908"
      > </a
      ><a name="1909" class="PrimitiveType"
      >Set</a
      ><a name="1912"
      > </a
      ><a name="1913" class="Keyword"
      >where</a
      ><a name="1918"
      >
  </a
      ><a name="1921" href="StlcProp.html#1921" class="InductiveConstructor"
      >steps</a
      ><a name="1926"
      > </a
      ><a name="1927" class="Symbol"
      >:</a
      ><a name="1928"
      > </a
      ><a name="1929" class="Symbol"
      >&#8704;</a
      ><a name="1930"
      > </a
      ><a name="1931" class="Symbol"
      >{</a
      ><a name="1932" href="StlcProp.html#1932" class="Bound"
      >M</a
      ><a name="1933"
      > </a
      ><a name="1934" href="StlcProp.html#1934" class="Bound"
      >N</a
      ><a name="1935" class="Symbol"
      >}</a
      ><a name="1936"
      > </a
      ><a name="1937" class="Symbol"
      >&#8594;</a
      ><a name="1938"
      > </a
      ><a name="1939" href="StlcProp.html#1932" class="Bound"
      >M</a
      ><a name="1940"
      > </a
      ><a name="1941" href="Stlc.html#1762" class="Datatype Operator"
      >&#10233;</a
      ><a name="1942"
      > </a
      ><a name="1943" href="StlcProp.html#1934" class="Bound"
      >N</a
      ><a name="1944"
      > </a
      ><a name="1945" class="Symbol"
      >&#8594;</a
      ><a name="1946"
      > </a
      ><a name="1947" href="StlcProp.html#1891" class="Datatype"
      >Progress</a
      ><a name="1955"
      > </a
      ><a name="1956" href="StlcProp.html#1932" class="Bound"
      >M</a
      ><a name="1957"
      >
  </a
      ><a name="1960" href="StlcProp.html#1960" class="InductiveConstructor"
      >done</a
      ><a name="1964"
      >  </a
      ><a name="1966" class="Symbol"
      >:</a
      ><a name="1967"
      > </a
      ><a name="1968" class="Symbol"
      >&#8704;</a
      ><a name="1969"
      > </a
      ><a name="1970" class="Symbol"
      >{</a
      ><a name="1971" href="StlcProp.html#1971" class="Bound"
      >M</a
      ><a name="1972" class="Symbol"
      >}</a
      ><a name="1973"
      > </a
      ><a name="1974" class="Symbol"
      >&#8594;</a
      ><a name="1975"
      > </a
      ><a name="1976" href="Stlc.html#1105" class="Datatype"
      >Value</a
      ><a name="1981"
      > </a
      ><a name="1982" href="StlcProp.html#1971" class="Bound"
      >M</a
      ><a name="1983"
      > </a
      ><a name="1984" class="Symbol"
      >&#8594;</a
      ><a name="1985"
      > </a
      ><a name="1986" href="StlcProp.html#1891" class="Datatype"
      >Progress</a
      ><a name="1994"
      > </a
      ><a name="1995" href="StlcProp.html#1971" class="Bound"
      >M</a
      ><a name="1996"
      >

</a
      ><a name="1998" href="StlcProp.html#1998" class="Function"
      >progress</a
      ><a name="2006"
      > </a
      ><a name="2007" class="Symbol"
      >:</a
      ><a name="2008"
      > </a
      ><a name="2009" class="Symbol"
      >&#8704;</a
      ><a name="2010"
      > </a
      ><a name="2011" class="Symbol"
      >{</a
      ><a name="2012" href="StlcProp.html#2012" class="Bound"
      >M</a
      ><a name="2013"
      > </a
      ><a name="2014" href="StlcProp.html#2014" class="Bound"
      >A</a
      ><a name="2015" class="Symbol"
      >}</a
      ><a name="2016"
      > </a
      ><a name="2017" class="Symbol"
      >&#8594;</a
      ><a name="2018"
      > </a
      ><a name="2019" href="Maps.html#10265" class="Function"
      >&#8709;</a
      ><a name="2020"
      > </a
      ><a name="2021" href="Stlc.html#3112" class="Datatype Operator"
      >&#8866;</a
      ><a name="2022"
      > </a
      ><a name="2023" href="StlcProp.html#2012" class="Bound"
      >M</a
      ><a name="2024"
      > </a
      ><a name="2025" href="Stlc.html#3112" class="Datatype Operator"
      >&#8758;</a
      ><a name="2026"
      > </a
      ><a name="2027" href="StlcProp.html#2014" class="Bound"
      >A</a
      ><a name="2028"
      > </a
      ><a name="2029" class="Symbol"
      >&#8594;</a
      ><a name="2030"
      > </a
      ><a name="2031" href="StlcProp.html#1891" class="Datatype"
      >Progress</a
      ><a name="2039"
      > </a
      ><a name="2040" href="StlcProp.html#2012" class="Bound"
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

<a name="3920" href="StlcProp.html#1998" class="Function"
      >progress</a
      ><a name="3928"
      > </a
      ><a name="3929" class="Symbol"
      >(</a
      ><a name="3930" href="Stlc.html#3156" class="InductiveConstructor"
      >Ax</a
      ><a name="3932"
      > </a
      ><a name="3933" class="Symbol"
      >())</a
      ><a name="3936"
      >
</a
      ><a name="3937" href="StlcProp.html#1998" class="Function"
      >progress</a
      ><a name="3945"
      > </a
      ><a name="3946" class="Symbol"
      >(</a
      ><a name="3947" href="Stlc.html#3210" class="InductiveConstructor"
      >&#8658;-I</a
      ><a name="3950"
      > </a
      ><a name="3951" href="StlcProp.html#3951" class="Bound"
      >&#8866;N</a
      ><a name="3953" class="Symbol"
      >)</a
      ><a name="3954"
      > </a
      ><a name="3955" class="Symbol"
      >=</a
      ><a name="3956"
      > </a
      ><a name="3957" href="StlcProp.html#1960" class="InductiveConstructor"
      >done</a
      ><a name="3961"
      > </a
      ><a name="3962" href="Stlc.html#1132" class="InductiveConstructor"
      >value-&#955;</a
      ><a name="3969"
      >
</a
      ><a name="3970" href="StlcProp.html#1998" class="Function"
      >progress</a
      ><a name="3978"
      > </a
      ><a name="3979" class="Symbol"
      >(</a
      ><a name="3980" href="Stlc.html#3287" class="InductiveConstructor"
      >&#8658;-E</a
      ><a name="3983"
      > </a
      ><a name="3984" href="StlcProp.html#3984" class="Bound"
      >&#8866;L</a
      ><a name="3986"
      > </a
      ><a name="3987" href="StlcProp.html#3987" class="Bound"
      >&#8866;M</a
      ><a name="3989" class="Symbol"
      >)</a
      ><a name="3990"
      > </a
      ><a name="3991" class="Keyword"
      >with</a
      ><a name="3995"
      > </a
      ><a name="3996" href="StlcProp.html#1998" class="Function"
      >progress</a
      ><a name="4004"
      > </a
      ><a name="4005" href="StlcProp.html#3984" class="Bound"
      >&#8866;L</a
      ><a name="4007"
      >
</a
      ><a name="4008" class="Symbol"
      >...</a
      ><a name="4011"
      > </a
      ><a name="4012" class="Symbol"
      >|</a
      ><a name="4013"
      > </a
      ><a name="4014" href="StlcProp.html#1921" class="InductiveConstructor"
      >steps</a
      ><a name="4019"
      > </a
      ><a name="4020" href="StlcProp.html#4020" class="Bound"
      >L&#10233;L&#8242;</a
      ><a name="4024"
      > </a
      ><a name="4025" class="Symbol"
      >=</a
      ><a name="4026"
      > </a
      ><a name="4027" href="StlcProp.html#1921" class="InductiveConstructor"
      >steps</a
      ><a name="4032"
      > </a
      ><a name="4033" class="Symbol"
      >(</a
      ><a name="4034" href="Stlc.html#1864" class="InductiveConstructor"
      >&#958;&#183;&#8321;</a
      ><a name="4037"
      > </a
      ><a name="4038" href="StlcProp.html#4020" class="Bound"
      >L&#10233;L&#8242;</a
      ><a name="4042" class="Symbol"
      >)</a
      ><a name="4043"
      >
</a
      ><a name="4044" class="Symbol"
      >...</a
      ><a name="4047"
      > </a
      ><a name="4048" class="Symbol"
      >|</a
      ><a name="4049"
      > </a
      ><a name="4050" href="StlcProp.html#1960" class="InductiveConstructor"
      >done</a
      ><a name="4054"
      > </a
      ><a name="4055" href="StlcProp.html#4055" class="Bound"
      >valueL</a
      ><a name="4061"
      > </a
      ><a name="4062" class="Keyword"
      >with</a
      ><a name="4066"
      > </a
      ><a name="4067" href="StlcProp.html#1998" class="Function"
      >progress</a
      ><a name="4075"
      > </a
      ><a name="4076" href="StlcProp.html#3987" class="Bound"
      >&#8866;M</a
      ><a name="4078"
      >
</a
      ><a name="4079" class="Symbol"
      >...</a
      ><a name="4082"
      > </a
      ><a name="4083" class="Symbol"
      >|</a
      ><a name="4084"
      > </a
      ><a name="4085" href="StlcProp.html#1921" class="InductiveConstructor"
      >steps</a
      ><a name="4090"
      > </a
      ><a name="4091" href="StlcProp.html#4091" class="Bound"
      >M&#10233;M&#8242;</a
      ><a name="4095"
      > </a
      ><a name="4096" class="Symbol"
      >=</a
      ><a name="4097"
      > </a
      ><a name="4098" href="StlcProp.html#1921" class="InductiveConstructor"
      >steps</a
      ><a name="4103"
      > </a
      ><a name="4104" class="Symbol"
      >(</a
      ><a name="4105" href="Stlc.html#1917" class="InductiveConstructor"
      >&#958;&#183;&#8322;</a
      ><a name="4108"
      > </a
      ><a name="4109" href="StlcProp.html#4055" class="Bound"
      >valueL</a
      ><a name="4115"
      > </a
      ><a name="4116" href="StlcProp.html#4091" class="Bound"
      >M&#10233;M&#8242;</a
      ><a name="4120" class="Symbol"
      >)</a
      ><a name="4121"
      >
</a
      ><a name="4122" class="Symbol"
      >...</a
      ><a name="4125"
      > </a
      ><a name="4126" class="Symbol"
      >|</a
      ><a name="4127"
      > </a
      ><a name="4128" href="StlcProp.html#1960" class="InductiveConstructor"
      >done</a
      ><a name="4132"
      > </a
      ><a name="4133" href="StlcProp.html#4133" class="Bound"
      >valueM</a
      ><a name="4139"
      > </a
      ><a name="4140" class="Keyword"
      >with</a
      ><a name="4144"
      > </a
      ><a name="4145" href="StlcProp.html#1355" class="Function"
      >canonicalFormsLemma</a
      ><a name="4164"
      > </a
      ><a name="4165" href="StlcProp.html#3984" class="Bound"
      >&#8866;L</a
      ><a name="4167"
      > </a
      ><a name="4168" href="StlcProp.html#4055" class="Bound"
      >valueL</a
      ><a name="4174"
      >
</a
      ><a name="4175" class="Symbol"
      >...</a
      ><a name="4178"
      > </a
      ><a name="4179" class="Symbol"
      >|</a
      ><a name="4180"
      > </a
      ><a name="4181" href="StlcProp.html#1207" class="InductiveConstructor"
      >canonical-&#955;</a
      ><a name="4192"
      > </a
      ><a name="4193" class="Symbol"
      >=</a
      ><a name="4194"
      > </a
      ><a name="4195" href="StlcProp.html#1921" class="InductiveConstructor"
      >steps</a
      ><a name="4200"
      > </a
      ><a name="4201" class="Symbol"
      >(</a
      ><a name="4202" href="Stlc.html#1794" class="InductiveConstructor"
      >&#946;&#955;&#183;</a
      ><a name="4205"
      > </a
      ><a name="4206" href="StlcProp.html#4133" class="Bound"
      >valueM</a
      ><a name="4212" class="Symbol"
      >)</a
      ><a name="4213"
      >
</a
      ><a name="4214" href="StlcProp.html#1998" class="Function"
      >progress</a
      ><a name="4222"
      > </a
      ><a name="4223" href="Stlc.html#3365" class="InductiveConstructor"
      >&#120121;-I&#8321;</a
      ><a name="4227"
      > </a
      ><a name="4228" class="Symbol"
      >=</a
      ><a name="4229"
      > </a
      ><a name="4230" href="StlcProp.html#1960" class="InductiveConstructor"
      >done</a
      ><a name="4234"
      > </a
      ><a name="4235" href="Stlc.html#1181" class="InductiveConstructor"
      >value-true</a
      ><a name="4245"
      >
</a
      ><a name="4246" href="StlcProp.html#1998" class="Function"
      >progress</a
      ><a name="4254"
      > </a
      ><a name="4255" href="Stlc.html#3399" class="InductiveConstructor"
      >&#120121;-I&#8322;</a
      ><a name="4259"
      > </a
      ><a name="4260" class="Symbol"
      >=</a
      ><a name="4261"
      > </a
      ><a name="4262" href="StlcProp.html#1960" class="InductiveConstructor"
      >done</a
      ><a name="4266"
      > </a
      ><a name="4267" href="Stlc.html#1208" class="InductiveConstructor"
      >value-false</a
      ><a name="4278"
      >
</a
      ><a name="4279" href="StlcProp.html#1998" class="Function"
      >progress</a
      ><a name="4287"
      > </a
      ><a name="4288" class="Symbol"
      >(</a
      ><a name="4289" href="Stlc.html#3434" class="InductiveConstructor"
      >&#120121;-E</a
      ><a name="4292"
      > </a
      ><a name="4293" href="StlcProp.html#4293" class="Bound"
      >&#8866;L</a
      ><a name="4295"
      > </a
      ><a name="4296" href="StlcProp.html#4296" class="Bound"
      >&#8866;M</a
      ><a name="4298"
      > </a
      ><a name="4299" href="StlcProp.html#4299" class="Bound"
      >&#8866;N</a
      ><a name="4301" class="Symbol"
      >)</a
      ><a name="4302"
      > </a
      ><a name="4303" class="Keyword"
      >with</a
      ><a name="4307"
      > </a
      ><a name="4308" href="StlcProp.html#1998" class="Function"
      >progress</a
      ><a name="4316"
      > </a
      ><a name="4317" href="StlcProp.html#4293" class="Bound"
      >&#8866;L</a
      ><a name="4319"
      >
</a
      ><a name="4320" class="Symbol"
      >...</a
      ><a name="4323"
      > </a
      ><a name="4324" class="Symbol"
      >|</a
      ><a name="4325"
      > </a
      ><a name="4326" href="StlcProp.html#1921" class="InductiveConstructor"
      >steps</a
      ><a name="4331"
      > </a
      ><a name="4332" href="StlcProp.html#4332" class="Bound"
      >L&#10233;L&#8242;</a
      ><a name="4336"
      > </a
      ><a name="4337" class="Symbol"
      >=</a
      ><a name="4338"
      > </a
      ><a name="4339" href="StlcProp.html#1921" class="InductiveConstructor"
      >steps</a
      ><a name="4344"
      > </a
      ><a name="4345" class="Symbol"
      >(</a
      ><a name="4346" href="Stlc.html#2092" class="InductiveConstructor"
      >&#958;if</a
      ><a name="4349"
      > </a
      ><a name="4350" href="StlcProp.html#4332" class="Bound"
      >L&#10233;L&#8242;</a
      ><a name="4354" class="Symbol"
      >)</a
      ><a name="4355"
      >
</a
      ><a name="4356" class="Symbol"
      >...</a
      ><a name="4359"
      > </a
      ><a name="4360" class="Symbol"
      >|</a
      ><a name="4361"
      > </a
      ><a name="4362" href="StlcProp.html#1960" class="InductiveConstructor"
      >done</a
      ><a name="4366"
      > </a
      ><a name="4367" href="StlcProp.html#4367" class="Bound"
      >valueL</a
      ><a name="4373"
      > </a
      ><a name="4374" class="Keyword"
      >with</a
      ><a name="4378"
      > </a
      ><a name="4379" href="StlcProp.html#1355" class="Function"
      >canonicalFormsLemma</a
      ><a name="4398"
      > </a
      ><a name="4399" href="StlcProp.html#4293" class="Bound"
      >&#8866;L</a
      ><a name="4401"
      > </a
      ><a name="4402" href="StlcProp.html#4367" class="Bound"
      >valueL</a
      ><a name="4408"
      >
</a
      ><a name="4409" class="Symbol"
      >...</a
      ><a name="4412"
      > </a
      ><a name="4413" class="Symbol"
      >|</a
      ><a name="4414"
      > </a
      ><a name="4415" href="StlcProp.html#1274" class="InductiveConstructor"
      >canonical-true</a
      ><a name="4429"
      > </a
      ><a name="4430" class="Symbol"
      >=</a
      ><a name="4431"
      > </a
      ><a name="4432" href="StlcProp.html#1921" class="InductiveConstructor"
      >steps</a
      ><a name="4437"
      > </a
      ><a name="4438" href="Stlc.html#1984" class="InductiveConstructor"
      >&#946;if-true</a
      ><a name="4446"
      >
</a
      ><a name="4447" class="Symbol"
      >...</a
      ><a name="4450"
      > </a
      ><a name="4451" class="Symbol"
      >|</a
      ><a name="4452"
      > </a
      ><a name="4453" href="StlcProp.html#1314" class="InductiveConstructor"
      >canonical-false</a
      ><a name="4468"
      > </a
      ><a name="4469" class="Symbol"
      >=</a
      ><a name="4470"
      > </a
      ><a name="4471" href="StlcProp.html#1921" class="InductiveConstructor"
      >steps</a
      ><a name="4476"
      > </a
      ><a name="4477" href="Stlc.html#2037" class="InductiveConstructor"
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

<a name="5134" class="Keyword"
      >postulate</a
      ><a name="5143"
      >
  </a
      ><a name="5146" href="StlcProp.html#5146" class="Postulate"
      >progress&#8242;</a
      ><a name="5155"
      > </a
      ><a name="5156" class="Symbol"
      >:</a
      ><a name="5157"
      > </a
      ><a name="5158" class="Symbol"
      >&#8704;</a
      ><a name="5159"
      > </a
      ><a name="5160" href="StlcProp.html#5160" class="Bound"
      >M</a
      ><a name="5161"
      > </a
      ><a name="5162" class="Symbol"
      >{</a
      ><a name="5163" href="StlcProp.html#5163" class="Bound"
      >A</a
      ><a name="5164" class="Symbol"
      >}</a
      ><a name="5165"
      > </a
      ><a name="5166" class="Symbol"
      >&#8594;</a
      ><a name="5167"
      > </a
      ><a name="5168" href="Maps.html#10265" class="Function"
      >&#8709;</a
      ><a name="5169"
      > </a
      ><a name="5170" href="Stlc.html#3112" class="Datatype Operator"
      >&#8866;</a
      ><a name="5171"
      > </a
      ><a name="5172" href="StlcProp.html#5160" class="Bound"
      >M</a
      ><a name="5173"
      > </a
      ><a name="5174" href="Stlc.html#3112" class="Datatype Operator"
      >&#8758;</a
      ><a name="5175"
      > </a
      ><a name="5176" href="StlcProp.html#5163" class="Bound"
      >A</a
      ><a name="5177"
      > </a
      ><a name="5178" class="Symbol"
      >&#8594;</a
      ><a name="5179"
      > </a
      ><a name="5180" href="StlcProp.html#1891" class="Datatype"
      >Progress</a
      ><a name="5188"
      > </a
      ><a name="5189" href="StlcProp.html#5160" class="Bound"
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

<a name="7636" class="Keyword"
      >data</a
      ><a name="7640"
      > </a
      ><a name="7641" href="StlcProp.html#7641" class="Datatype Operator"
      >_&#8712;_</a
      ><a name="7644"
      > </a
      ><a name="7645" class="Symbol"
      >:</a
      ><a name="7646"
      > </a
      ><a name="7647" href="Maps.html#2171" class="Datatype"
      >Id</a
      ><a name="7649"
      > </a
      ><a name="7650" class="Symbol"
      >&#8594;</a
      ><a name="7651"
      > </a
      ><a name="7652" href="Stlc.html#708" class="Datatype"
      >Term</a
      ><a name="7656"
      > </a
      ><a name="7657" class="Symbol"
      >&#8594;</a
      ><a name="7658"
      > </a
      ><a name="7659" class="PrimitiveType"
      >Set</a
      ><a name="7662"
      > </a
      ><a name="7663" class="Keyword"
      >where</a
      ><a name="7668"
      >
  </a
      ><a name="7671" href="StlcProp.html#7671" class="InductiveConstructor"
      >free-`</a
      ><a name="7677"
      >  </a
      ><a name="7679" class="Symbol"
      >:</a
      ><a name="7680"
      > </a
      ><a name="7681" class="Symbol"
      >&#8704;</a
      ><a name="7682"
      > </a
      ><a name="7683" class="Symbol"
      >{</a
      ><a name="7684" href="StlcProp.html#7684" class="Bound"
      >x</a
      ><a name="7685" class="Symbol"
      >}</a
      ><a name="7686"
      > </a
      ><a name="7687" class="Symbol"
      >&#8594;</a
      ><a name="7688"
      > </a
      ><a name="7689" href="StlcProp.html#7684" class="Bound"
      >x</a
      ><a name="7690"
      > </a
      ><a name="7691" href="StlcProp.html#7641" class="Datatype Operator"
      >&#8712;</a
      ><a name="7692"
      > </a
      ><a name="7693" href="Stlc.html#727" class="InductiveConstructor"
      >`</a
      ><a name="7694"
      > </a
      ><a name="7695" href="StlcProp.html#7684" class="Bound"
      >x</a
      ><a name="7696"
      >
  </a
      ><a name="7699" href="StlcProp.html#7699" class="InductiveConstructor"
      >free-&#955;</a
      ><a name="7705"
      >  </a
      ><a name="7707" class="Symbol"
      >:</a
      ><a name="7708"
      > </a
      ><a name="7709" class="Symbol"
      >&#8704;</a
      ><a name="7710"
      > </a
      ><a name="7711" class="Symbol"
      >{</a
      ><a name="7712" href="StlcProp.html#7712" class="Bound"
      >x</a
      ><a name="7713"
      > </a
      ><a name="7714" href="StlcProp.html#7714" class="Bound"
      >y</a
      ><a name="7715"
      > </a
      ><a name="7716" href="StlcProp.html#7716" class="Bound"
      >A</a
      ><a name="7717"
      > </a
      ><a name="7718" href="StlcProp.html#7718" class="Bound"
      >N</a
      ><a name="7719" class="Symbol"
      >}</a
      ><a name="7720"
      > </a
      ><a name="7721" class="Symbol"
      >&#8594;</a
      ><a name="7722"
      > </a
      ><a name="7723" href="StlcProp.html#7714" class="Bound"
      >y</a
      ><a name="7724"
      > </a
      ><a name="7725" href="https://agda.github.io/agda-stdlib/Relation.Binary.Core.html#4493" class="Function Operator"
      >&#8802;</a
      ><a name="7726"
      > </a
      ><a name="7727" href="StlcProp.html#7712" class="Bound"
      >x</a
      ><a name="7728"
      > </a
      ><a name="7729" class="Symbol"
      >&#8594;</a
      ><a name="7730"
      > </a
      ><a name="7731" href="StlcProp.html#7712" class="Bound"
      >x</a
      ><a name="7732"
      > </a
      ><a name="7733" href="StlcProp.html#7641" class="Datatype Operator"
      >&#8712;</a
      ><a name="7734"
      > </a
      ><a name="7735" href="StlcProp.html#7718" class="Bound"
      >N</a
      ><a name="7736"
      > </a
      ><a name="7737" class="Symbol"
      >&#8594;</a
      ><a name="7738"
      > </a
      ><a name="7739" href="StlcProp.html#7712" class="Bound"
      >x</a
      ><a name="7740"
      > </a
      ><a name="7741" href="StlcProp.html#7641" class="Datatype Operator"
      >&#8712;</a
      ><a name="7742"
      > </a
      ><a name="7743" class="Symbol"
      >(</a
      ><a name="7744" href="Stlc.html#743" class="InductiveConstructor Operator"
      >&#955;[</a
      ><a name="7746"
      > </a
      ><a name="7747" href="StlcProp.html#7714" class="Bound"
      >y</a
      ><a name="7748"
      > </a
      ><a name="7749" href="Stlc.html#743" class="InductiveConstructor Operator"
      >&#8758;</a
      ><a name="7750"
      > </a
      ><a name="7751" href="StlcProp.html#7716" class="Bound"
      >A</a
      ><a name="7752"
      > </a
      ><a name="7753" href="Stlc.html#743" class="InductiveConstructor Operator"
      >]</a
      ><a name="7754"
      > </a
      ><a name="7755" href="StlcProp.html#7718" class="Bound"
      >N</a
      ><a name="7756" class="Symbol"
      >)</a
      ><a name="7757"
      >
  </a
      ><a name="7760" href="StlcProp.html#7760" class="InductiveConstructor"
      >free-&#183;&#8321;</a
      ><a name="7767"
      > </a
      ><a name="7768" class="Symbol"
      >:</a
      ><a name="7769"
      > </a
      ><a name="7770" class="Symbol"
      >&#8704;</a
      ><a name="7771"
      > </a
      ><a name="7772" class="Symbol"
      >{</a
      ><a name="7773" href="StlcProp.html#7773" class="Bound"
      >x</a
      ><a name="7774"
      > </a
      ><a name="7775" href="StlcProp.html#7775" class="Bound"
      >L</a
      ><a name="7776"
      > </a
      ><a name="7777" href="StlcProp.html#7777" class="Bound"
      >M</a
      ><a name="7778" class="Symbol"
      >}</a
      ><a name="7779"
      > </a
      ><a name="7780" class="Symbol"
      >&#8594;</a
      ><a name="7781"
      > </a
      ><a name="7782" href="StlcProp.html#7773" class="Bound"
      >x</a
      ><a name="7783"
      > </a
      ><a name="7784" href="StlcProp.html#7641" class="Datatype Operator"
      >&#8712;</a
      ><a name="7785"
      > </a
      ><a name="7786" href="StlcProp.html#7775" class="Bound"
      >L</a
      ><a name="7787"
      > </a
      ><a name="7788" class="Symbol"
      >&#8594;</a
      ><a name="7789"
      > </a
      ><a name="7790" href="StlcProp.html#7773" class="Bound"
      >x</a
      ><a name="7791"
      > </a
      ><a name="7792" href="StlcProp.html#7641" class="Datatype Operator"
      >&#8712;</a
      ><a name="7793"
      > </a
      ><a name="7794" class="Symbol"
      >(</a
      ><a name="7795" href="StlcProp.html#7775" class="Bound"
      >L</a
      ><a name="7796"
      > </a
      ><a name="7797" href="Stlc.html#779" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="7798"
      > </a
      ><a name="7799" href="StlcProp.html#7777" class="Bound"
      >M</a
      ><a name="7800" class="Symbol"
      >)</a
      ><a name="7801"
      >
  </a
      ><a name="7804" href="StlcProp.html#7804" class="InductiveConstructor"
      >free-&#183;&#8322;</a
      ><a name="7811"
      > </a
      ><a name="7812" class="Symbol"
      >:</a
      ><a name="7813"
      > </a
      ><a name="7814" class="Symbol"
      >&#8704;</a
      ><a name="7815"
      > </a
      ><a name="7816" class="Symbol"
      >{</a
      ><a name="7817" href="StlcProp.html#7817" class="Bound"
      >x</a
      ><a name="7818"
      > </a
      ><a name="7819" href="StlcProp.html#7819" class="Bound"
      >L</a
      ><a name="7820"
      > </a
      ><a name="7821" href="StlcProp.html#7821" class="Bound"
      >M</a
      ><a name="7822" class="Symbol"
      >}</a
      ><a name="7823"
      > </a
      ><a name="7824" class="Symbol"
      >&#8594;</a
      ><a name="7825"
      > </a
      ><a name="7826" href="StlcProp.html#7817" class="Bound"
      >x</a
      ><a name="7827"
      > </a
      ><a name="7828" href="StlcProp.html#7641" class="Datatype Operator"
      >&#8712;</a
      ><a name="7829"
      > </a
      ><a name="7830" href="StlcProp.html#7821" class="Bound"
      >M</a
      ><a name="7831"
      > </a
      ><a name="7832" class="Symbol"
      >&#8594;</a
      ><a name="7833"
      > </a
      ><a name="7834" href="StlcProp.html#7817" class="Bound"
      >x</a
      ><a name="7835"
      > </a
      ><a name="7836" href="StlcProp.html#7641" class="Datatype Operator"
      >&#8712;</a
      ><a name="7837"
      > </a
      ><a name="7838" class="Symbol"
      >(</a
      ><a name="7839" href="StlcProp.html#7819" class="Bound"
      >L</a
      ><a name="7840"
      > </a
      ><a name="7841" href="Stlc.html#779" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="7842"
      > </a
      ><a name="7843" href="StlcProp.html#7821" class="Bound"
      >M</a
      ><a name="7844" class="Symbol"
      >)</a
      ><a name="7845"
      >
  </a
      ><a name="7848" href="StlcProp.html#7848" class="InductiveConstructor"
      >free-if&#8321;</a
      ><a name="7856"
      > </a
      ><a name="7857" class="Symbol"
      >:</a
      ><a name="7858"
      > </a
      ><a name="7859" class="Symbol"
      >&#8704;</a
      ><a name="7860"
      > </a
      ><a name="7861" class="Symbol"
      >{</a
      ><a name="7862" href="StlcProp.html#7862" class="Bound"
      >x</a
      ><a name="7863"
      > </a
      ><a name="7864" href="StlcProp.html#7864" class="Bound"
      >L</a
      ><a name="7865"
      > </a
      ><a name="7866" href="StlcProp.html#7866" class="Bound"
      >M</a
      ><a name="7867"
      > </a
      ><a name="7868" href="StlcProp.html#7868" class="Bound"
      >N</a
      ><a name="7869" class="Symbol"
      >}</a
      ><a name="7870"
      > </a
      ><a name="7871" class="Symbol"
      >&#8594;</a
      ><a name="7872"
      > </a
      ><a name="7873" href="StlcProp.html#7862" class="Bound"
      >x</a
      ><a name="7874"
      > </a
      ><a name="7875" href="StlcProp.html#7641" class="Datatype Operator"
      >&#8712;</a
      ><a name="7876"
      > </a
      ><a name="7877" href="StlcProp.html#7864" class="Bound"
      >L</a
      ><a name="7878"
      > </a
      ><a name="7879" class="Symbol"
      >&#8594;</a
      ><a name="7880"
      > </a
      ><a name="7881" href="StlcProp.html#7862" class="Bound"
      >x</a
      ><a name="7882"
      > </a
      ><a name="7883" href="StlcProp.html#7641" class="Datatype Operator"
      >&#8712;</a
      ><a name="7884"
      > </a
      ><a name="7885" class="Symbol"
      >(</a
      ><a name="7886" href="Stlc.html#835" class="InductiveConstructor Operator"
      >if</a
      ><a name="7888"
      > </a
      ><a name="7889" href="StlcProp.html#7864" class="Bound"
      >L</a
      ><a name="7890"
      > </a
      ><a name="7891" href="Stlc.html#835" class="InductiveConstructor Operator"
      >then</a
      ><a name="7895"
      > </a
      ><a name="7896" href="StlcProp.html#7866" class="Bound"
      >M</a
      ><a name="7897"
      > </a
      ><a name="7898" href="Stlc.html#835" class="InductiveConstructor Operator"
      >else</a
      ><a name="7902"
      > </a
      ><a name="7903" href="StlcProp.html#7868" class="Bound"
      >N</a
      ><a name="7904" class="Symbol"
      >)</a
      ><a name="7905"
      >
  </a
      ><a name="7908" href="StlcProp.html#7908" class="InductiveConstructor"
      >free-if&#8322;</a
      ><a name="7916"
      > </a
      ><a name="7917" class="Symbol"
      >:</a
      ><a name="7918"
      > </a
      ><a name="7919" class="Symbol"
      >&#8704;</a
      ><a name="7920"
      > </a
      ><a name="7921" class="Symbol"
      >{</a
      ><a name="7922" href="StlcProp.html#7922" class="Bound"
      >x</a
      ><a name="7923"
      > </a
      ><a name="7924" href="StlcProp.html#7924" class="Bound"
      >L</a
      ><a name="7925"
      > </a
      ><a name="7926" href="StlcProp.html#7926" class="Bound"
      >M</a
      ><a name="7927"
      > </a
      ><a name="7928" href="StlcProp.html#7928" class="Bound"
      >N</a
      ><a name="7929" class="Symbol"
      >}</a
      ><a name="7930"
      > </a
      ><a name="7931" class="Symbol"
      >&#8594;</a
      ><a name="7932"
      > </a
      ><a name="7933" href="StlcProp.html#7922" class="Bound"
      >x</a
      ><a name="7934"
      > </a
      ><a name="7935" href="StlcProp.html#7641" class="Datatype Operator"
      >&#8712;</a
      ><a name="7936"
      > </a
      ><a name="7937" href="StlcProp.html#7926" class="Bound"
      >M</a
      ><a name="7938"
      > </a
      ><a name="7939" class="Symbol"
      >&#8594;</a
      ><a name="7940"
      > </a
      ><a name="7941" href="StlcProp.html#7922" class="Bound"
      >x</a
      ><a name="7942"
      > </a
      ><a name="7943" href="StlcProp.html#7641" class="Datatype Operator"
      >&#8712;</a
      ><a name="7944"
      > </a
      ><a name="7945" class="Symbol"
      >(</a
      ><a name="7946" href="Stlc.html#835" class="InductiveConstructor Operator"
      >if</a
      ><a name="7948"
      > </a
      ><a name="7949" href="StlcProp.html#7924" class="Bound"
      >L</a
      ><a name="7950"
      > </a
      ><a name="7951" href="Stlc.html#835" class="InductiveConstructor Operator"
      >then</a
      ><a name="7955"
      > </a
      ><a name="7956" href="StlcProp.html#7926" class="Bound"
      >M</a
      ><a name="7957"
      > </a
      ><a name="7958" href="Stlc.html#835" class="InductiveConstructor Operator"
      >else</a
      ><a name="7962"
      > </a
      ><a name="7963" href="StlcProp.html#7928" class="Bound"
      >N</a
      ><a name="7964" class="Symbol"
      >)</a
      ><a name="7965"
      >
  </a
      ><a name="7968" href="StlcProp.html#7968" class="InductiveConstructor"
      >free-if&#8323;</a
      ><a name="7976"
      > </a
      ><a name="7977" class="Symbol"
      >:</a
      ><a name="7978"
      > </a
      ><a name="7979" class="Symbol"
      >&#8704;</a
      ><a name="7980"
      > </a
      ><a name="7981" class="Symbol"
      >{</a
      ><a name="7982" href="StlcProp.html#7982" class="Bound"
      >x</a
      ><a name="7983"
      > </a
      ><a name="7984" href="StlcProp.html#7984" class="Bound"
      >L</a
      ><a name="7985"
      > </a
      ><a name="7986" href="StlcProp.html#7986" class="Bound"
      >M</a
      ><a name="7987"
      > </a
      ><a name="7988" href="StlcProp.html#7988" class="Bound"
      >N</a
      ><a name="7989" class="Symbol"
      >}</a
      ><a name="7990"
      > </a
      ><a name="7991" class="Symbol"
      >&#8594;</a
      ><a name="7992"
      > </a
      ><a name="7993" href="StlcProp.html#7982" class="Bound"
      >x</a
      ><a name="7994"
      > </a
      ><a name="7995" href="StlcProp.html#7641" class="Datatype Operator"
      >&#8712;</a
      ><a name="7996"
      > </a
      ><a name="7997" href="StlcProp.html#7988" class="Bound"
      >N</a
      ><a name="7998"
      > </a
      ><a name="7999" class="Symbol"
      >&#8594;</a
      ><a name="8000"
      > </a
      ><a name="8001" href="StlcProp.html#7982" class="Bound"
      >x</a
      ><a name="8002"
      > </a
      ><a name="8003" href="StlcProp.html#7641" class="Datatype Operator"
      >&#8712;</a
      ><a name="8004"
      > </a
      ><a name="8005" class="Symbol"
      >(</a
      ><a name="8006" href="Stlc.html#835" class="InductiveConstructor Operator"
      >if</a
      ><a name="8008"
      > </a
      ><a name="8009" href="StlcProp.html#7984" class="Bound"
      >L</a
      ><a name="8010"
      > </a
      ><a name="8011" href="Stlc.html#835" class="InductiveConstructor Operator"
      >then</a
      ><a name="8015"
      > </a
      ><a name="8016" href="StlcProp.html#7986" class="Bound"
      >M</a
      ><a name="8017"
      > </a
      ><a name="8018" href="Stlc.html#835" class="InductiveConstructor Operator"
      >else</a
      ><a name="8022"
      > </a
      ><a name="8023" href="StlcProp.html#7988" class="Bound"
      >N</a
      ><a name="8024" class="Symbol"
      >)</a
      >

</pre>

A term in which no variables appear free is said to be _closed_.

<pre class="Agda">

<a name="8117" href="StlcProp.html#8117" class="Function Operator"
      >_&#8713;_</a
      ><a name="8120"
      > </a
      ><a name="8121" class="Symbol"
      >:</a
      ><a name="8122"
      > </a
      ><a name="8123" href="Maps.html#2171" class="Datatype"
      >Id</a
      ><a name="8125"
      > </a
      ><a name="8126" class="Symbol"
      >&#8594;</a
      ><a name="8127"
      > </a
      ><a name="8128" href="Stlc.html#708" class="Datatype"
      >Term</a
      ><a name="8132"
      > </a
      ><a name="8133" class="Symbol"
      >&#8594;</a
      ><a name="8134"
      > </a
      ><a name="8135" class="PrimitiveType"
      >Set</a
      ><a name="8138"
      >
</a
      ><a name="8139" href="StlcProp.html#8139" class="Bound"
      >x</a
      ><a name="8140"
      > </a
      ><a name="8141" href="StlcProp.html#8117" class="Function Operator"
      >&#8713;</a
      ><a name="8142"
      > </a
      ><a name="8143" href="StlcProp.html#8143" class="Bound"
      >M</a
      ><a name="8144"
      > </a
      ><a name="8145" class="Symbol"
      >=</a
      ><a name="8146"
      > </a
      ><a name="8147" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#414" class="Function Operator"
      >&#172;</a
      ><a name="8148"
      > </a
      ><a name="8149" class="Symbol"
      >(</a
      ><a name="8150" href="StlcProp.html#8139" class="Bound"
      >x</a
      ><a name="8151"
      > </a
      ><a name="8152" href="StlcProp.html#7641" class="Datatype Operator"
      >&#8712;</a
      ><a name="8153"
      > </a
      ><a name="8154" href="StlcProp.html#8143" class="Bound"
      >M</a
      ><a name="8155" class="Symbol"
      >)</a
      ><a name="8156"
      >

</a
      ><a name="8158" href="StlcProp.html#8158" class="Function"
      >closed</a
      ><a name="8164"
      > </a
      ><a name="8165" class="Symbol"
      >:</a
      ><a name="8166"
      > </a
      ><a name="8167" href="Stlc.html#708" class="Datatype"
      >Term</a
      ><a name="8171"
      > </a
      ><a name="8172" class="Symbol"
      >&#8594;</a
      ><a name="8173"
      > </a
      ><a name="8174" class="PrimitiveType"
      >Set</a
      ><a name="8177"
      >
</a
      ><a name="8178" href="StlcProp.html#8158" class="Function"
      >closed</a
      ><a name="8184"
      > </a
      ><a name="8185" href="StlcProp.html#8185" class="Bound"
      >M</a
      ><a name="8186"
      > </a
      ><a name="8187" class="Symbol"
      >=</a
      ><a name="8188"
      > </a
      ><a name="8189" class="Symbol"
      >&#8704;</a
      ><a name="8190"
      > </a
      ><a name="8191" class="Symbol"
      >{</a
      ><a name="8192" href="StlcProp.html#8192" class="Bound"
      >x</a
      ><a name="8193" class="Symbol"
      >}</a
      ><a name="8194"
      > </a
      ><a name="8195" class="Symbol"
      >&#8594;</a
      ><a name="8196"
      > </a
      ><a name="8197" href="StlcProp.html#8192" class="Bound"
      >x</a
      ><a name="8198"
      > </a
      ><a name="8199" href="StlcProp.html#8117" class="Function Operator"
      >&#8713;</a
      ><a name="8200"
      > </a
      ><a name="8201" href="StlcProp.html#8185" class="Bound"
      >M</a
      >

</pre>

Here are proofs corresponding to the first two examples above.

<pre class="Agda">

<a name="8292" href="StlcProp.html#8292" class="Function"
      >f&#8802;x</a
      ><a name="8295"
      > </a
      ><a name="8296" class="Symbol"
      >:</a
      ><a name="8297"
      > </a
      ><a name="8298" href="Stlc.html#917" class="Function"
      >f</a
      ><a name="8299"
      > </a
      ><a name="8300" href="https://agda.github.io/agda-stdlib/Relation.Binary.Core.html#4493" class="Function Operator"
      >&#8802;</a
      ><a name="8301"
      > </a
      ><a name="8302" href="Stlc.html#919" class="Function"
      >x</a
      ><a name="8303"
      >
</a
      ><a name="8304" href="StlcProp.html#8292" class="Function"
      >f&#8802;x</a
      ><a name="8307"
      > </a
      ><a name="8308" class="Symbol"
      >()</a
      ><a name="8310"
      >

</a
      ><a name="8312" href="StlcProp.html#8312" class="Function"
      >example-free&#8321;</a
      ><a name="8325"
      > </a
      ><a name="8326" class="Symbol"
      >:</a
      ><a name="8327"
      > </a
      ><a name="8328" href="Stlc.html#919" class="Function"
      >x</a
      ><a name="8329"
      > </a
      ><a name="8330" href="StlcProp.html#7641" class="Datatype Operator"
      >&#8712;</a
      ><a name="8331"
      > </a
      ><a name="8332" class="Symbol"
      >(</a
      ><a name="8333" href="Stlc.html#743" class="InductiveConstructor Operator"
      >&#955;[</a
      ><a name="8335"
      > </a
      ><a name="8336" href="Stlc.html#917" class="Function"
      >f</a
      ><a name="8337"
      > </a
      ><a name="8338" href="Stlc.html#743" class="InductiveConstructor Operator"
      >&#8758;</a
      ><a name="8339"
      > </a
      ><a name="8340" class="Symbol"
      >(</a
      ><a name="8341" href="Stlc.html#609" class="InductiveConstructor"
      >&#120121;</a
      ><a name="8342"
      > </a
      ><a name="8343" href="Stlc.html#620" class="InductiveConstructor Operator"
      >&#8658;</a
      ><a name="8344"
      > </a
      ><a name="8345" href="Stlc.html#609" class="InductiveConstructor"
      >&#120121;</a
      ><a name="8346" class="Symbol"
      >)</a
      ><a name="8347"
      > </a
      ><a name="8348" href="Stlc.html#743" class="InductiveConstructor Operator"
      >]</a
      ><a name="8349"
      > </a
      ><a name="8350" href="Stlc.html#727" class="InductiveConstructor"
      >`</a
      ><a name="8351"
      > </a
      ><a name="8352" href="Stlc.html#917" class="Function"
      >f</a
      ><a name="8353"
      > </a
      ><a name="8354" href="Stlc.html#779" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="8355"
      > </a
      ><a name="8356" href="Stlc.html#727" class="InductiveConstructor"
      >`</a
      ><a name="8357"
      > </a
      ><a name="8358" href="Stlc.html#919" class="Function"
      >x</a
      ><a name="8359" class="Symbol"
      >)</a
      ><a name="8360"
      >
</a
      ><a name="8361" href="StlcProp.html#8312" class="Function"
      >example-free&#8321;</a
      ><a name="8374"
      > </a
      ><a name="8375" class="Symbol"
      >=</a
      ><a name="8376"
      > </a
      ><a name="8377" href="StlcProp.html#7699" class="InductiveConstructor"
      >free-&#955;</a
      ><a name="8383"
      > </a
      ><a name="8384" href="StlcProp.html#8292" class="Function"
      >f&#8802;x</a
      ><a name="8387"
      > </a
      ><a name="8388" class="Symbol"
      >(</a
      ><a name="8389" href="StlcProp.html#7804" class="InductiveConstructor"
      >free-&#183;&#8322;</a
      ><a name="8396"
      > </a
      ><a name="8397" href="StlcProp.html#7671" class="InductiveConstructor"
      >free-`</a
      ><a name="8403" class="Symbol"
      >)</a
      ><a name="8404"
      >

</a
      ><a name="8406" href="StlcProp.html#8406" class="Function"
      >example-free&#8322;</a
      ><a name="8419"
      > </a
      ><a name="8420" class="Symbol"
      >:</a
      ><a name="8421"
      > </a
      ><a name="8422" href="Stlc.html#917" class="Function"
      >f</a
      ><a name="8423"
      > </a
      ><a name="8424" href="StlcProp.html#8117" class="Function Operator"
      >&#8713;</a
      ><a name="8425"
      > </a
      ><a name="8426" class="Symbol"
      >(</a
      ><a name="8427" href="Stlc.html#743" class="InductiveConstructor Operator"
      >&#955;[</a
      ><a name="8429"
      > </a
      ><a name="8430" href="Stlc.html#917" class="Function"
      >f</a
      ><a name="8431"
      > </a
      ><a name="8432" href="Stlc.html#743" class="InductiveConstructor Operator"
      >&#8758;</a
      ><a name="8433"
      > </a
      ><a name="8434" class="Symbol"
      >(</a
      ><a name="8435" href="Stlc.html#609" class="InductiveConstructor"
      >&#120121;</a
      ><a name="8436"
      > </a
      ><a name="8437" href="Stlc.html#620" class="InductiveConstructor Operator"
      >&#8658;</a
      ><a name="8438"
      > </a
      ><a name="8439" href="Stlc.html#609" class="InductiveConstructor"
      >&#120121;</a
      ><a name="8440" class="Symbol"
      >)</a
      ><a name="8441"
      > </a
      ><a name="8442" href="Stlc.html#743" class="InductiveConstructor Operator"
      >]</a
      ><a name="8443"
      > </a
      ><a name="8444" href="Stlc.html#727" class="InductiveConstructor"
      >`</a
      ><a name="8445"
      > </a
      ><a name="8446" href="Stlc.html#917" class="Function"
      >f</a
      ><a name="8447"
      > </a
      ><a name="8448" href="Stlc.html#779" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="8449"
      > </a
      ><a name="8450" href="Stlc.html#727" class="InductiveConstructor"
      >`</a
      ><a name="8451"
      > </a
      ><a name="8452" href="Stlc.html#919" class="Function"
      >x</a
      ><a name="8453" class="Symbol"
      >)</a
      ><a name="8454"
      >
</a
      ><a name="8455" href="StlcProp.html#8406" class="Function"
      >example-free&#8322;</a
      ><a name="8468"
      > </a
      ><a name="8469" class="Symbol"
      >(</a
      ><a name="8470" href="StlcProp.html#7699" class="InductiveConstructor"
      >free-&#955;</a
      ><a name="8476"
      > </a
      ><a name="8477" href="StlcProp.html#8477" class="Bound"
      >f&#8802;f</a
      ><a name="8480"
      > </a
      ><a name="8481" class="Symbol"
      >_)</a
      ><a name="8483"
      > </a
      ><a name="8484" class="Symbol"
      >=</a
      ><a name="8485"
      > </a
      ><a name="8486" href="StlcProp.html#8477" class="Bound"
      >f&#8802;f</a
      ><a name="8489"
      > </a
      ><a name="8490" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      >

</pre>


#### Exercise: 1 star (free-in)
Prove formally the remaining examples given above.

<pre class="Agda">

<a name="8605" class="Keyword"
      >postulate</a
      ><a name="8614"
      >
  </a
      ><a name="8617" href="StlcProp.html#8617" class="Postulate"
      >example-free&#8323;</a
      ><a name="8630"
      > </a
      ><a name="8631" class="Symbol"
      >:</a
      ><a name="8632"
      > </a
      ><a name="8633" href="Stlc.html#919" class="Function"
      >x</a
      ><a name="8634"
      > </a
      ><a name="8635" href="StlcProp.html#7641" class="Datatype Operator"
      >&#8712;</a
      ><a name="8636"
      > </a
      ><a name="8637" class="Symbol"
      >((</a
      ><a name="8639" href="Stlc.html#743" class="InductiveConstructor Operator"
      >&#955;[</a
      ><a name="8641"
      > </a
      ><a name="8642" href="Stlc.html#917" class="Function"
      >f</a
      ><a name="8643"
      > </a
      ><a name="8644" href="Stlc.html#743" class="InductiveConstructor Operator"
      >&#8758;</a
      ><a name="8645"
      > </a
      ><a name="8646" class="Symbol"
      >(</a
      ><a name="8647" href="Stlc.html#609" class="InductiveConstructor"
      >&#120121;</a
      ><a name="8648"
      > </a
      ><a name="8649" href="Stlc.html#620" class="InductiveConstructor Operator"
      >&#8658;</a
      ><a name="8650"
      > </a
      ><a name="8651" href="Stlc.html#609" class="InductiveConstructor"
      >&#120121;</a
      ><a name="8652" class="Symbol"
      >)</a
      ><a name="8653"
      > </a
      ><a name="8654" href="Stlc.html#743" class="InductiveConstructor Operator"
      >]</a
      ><a name="8655"
      > </a
      ><a name="8656" href="Stlc.html#727" class="InductiveConstructor"
      >`</a
      ><a name="8657"
      > </a
      ><a name="8658" href="Stlc.html#917" class="Function"
      >f</a
      ><a name="8659"
      > </a
      ><a name="8660" href="Stlc.html#779" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="8661"
      > </a
      ><a name="8662" href="Stlc.html#727" class="InductiveConstructor"
      >`</a
      ><a name="8663"
      > </a
      ><a name="8664" href="Stlc.html#919" class="Function"
      >x</a
      ><a name="8665" class="Symbol"
      >)</a
      ><a name="8666"
      > </a
      ><a name="8667" href="Stlc.html#779" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="8668"
      > </a
      ><a name="8669" href="Stlc.html#727" class="InductiveConstructor"
      >`</a
      ><a name="8670"
      > </a
      ><a name="8671" href="Stlc.html#917" class="Function"
      >f</a
      ><a name="8672" class="Symbol"
      >)</a
      ><a name="8673"
      >
  </a
      ><a name="8676" href="StlcProp.html#8676" class="Postulate"
      >example-free&#8324;</a
      ><a name="8689"
      > </a
      ><a name="8690" class="Symbol"
      >:</a
      ><a name="8691"
      > </a
      ><a name="8692" href="Stlc.html#917" class="Function"
      >f</a
      ><a name="8693"
      > </a
      ><a name="8694" href="StlcProp.html#7641" class="Datatype Operator"
      >&#8712;</a
      ><a name="8695"
      > </a
      ><a name="8696" class="Symbol"
      >((</a
      ><a name="8698" href="Stlc.html#743" class="InductiveConstructor Operator"
      >&#955;[</a
      ><a name="8700"
      > </a
      ><a name="8701" href="Stlc.html#917" class="Function"
      >f</a
      ><a name="8702"
      > </a
      ><a name="8703" href="Stlc.html#743" class="InductiveConstructor Operator"
      >&#8758;</a
      ><a name="8704"
      > </a
      ><a name="8705" class="Symbol"
      >(</a
      ><a name="8706" href="Stlc.html#609" class="InductiveConstructor"
      >&#120121;</a
      ><a name="8707"
      > </a
      ><a name="8708" href="Stlc.html#620" class="InductiveConstructor Operator"
      >&#8658;</a
      ><a name="8709"
      > </a
      ><a name="8710" href="Stlc.html#609" class="InductiveConstructor"
      >&#120121;</a
      ><a name="8711" class="Symbol"
      >)</a
      ><a name="8712"
      > </a
      ><a name="8713" href="Stlc.html#743" class="InductiveConstructor Operator"
      >]</a
      ><a name="8714"
      > </a
      ><a name="8715" href="Stlc.html#727" class="InductiveConstructor"
      >`</a
      ><a name="8716"
      > </a
      ><a name="8717" href="Stlc.html#917" class="Function"
      >f</a
      ><a name="8718"
      > </a
      ><a name="8719" href="Stlc.html#779" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="8720"
      > </a
      ><a name="8721" href="Stlc.html#727" class="InductiveConstructor"
      >`</a
      ><a name="8722"
      > </a
      ><a name="8723" href="Stlc.html#919" class="Function"
      >x</a
      ><a name="8724" class="Symbol"
      >)</a
      ><a name="8725"
      > </a
      ><a name="8726" href="Stlc.html#779" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="8727"
      > </a
      ><a name="8728" href="Stlc.html#727" class="InductiveConstructor"
      >`</a
      ><a name="8729"
      > </a
      ><a name="8730" href="Stlc.html#917" class="Function"
      >f</a
      ><a name="8731" class="Symbol"
      >)</a
      ><a name="8732"
      >
  </a
      ><a name="8735" href="StlcProp.html#8735" class="Postulate"
      >example-free&#8325;</a
      ><a name="8748"
      > </a
      ><a name="8749" class="Symbol"
      >:</a
      ><a name="8750"
      > </a
      ><a name="8751" href="Stlc.html#919" class="Function"
      >x</a
      ><a name="8752"
      > </a
      ><a name="8753" href="StlcProp.html#8117" class="Function Operator"
      >&#8713;</a
      ><a name="8754"
      > </a
      ><a name="8755" class="Symbol"
      >(</a
      ><a name="8756" href="Stlc.html#743" class="InductiveConstructor Operator"
      >&#955;[</a
      ><a name="8758"
      > </a
      ><a name="8759" href="Stlc.html#917" class="Function"
      >f</a
      ><a name="8760"
      > </a
      ><a name="8761" href="Stlc.html#743" class="InductiveConstructor Operator"
      >&#8758;</a
      ><a name="8762"
      > </a
      ><a name="8763" class="Symbol"
      >(</a
      ><a name="8764" href="Stlc.html#609" class="InductiveConstructor"
      >&#120121;</a
      ><a name="8765"
      > </a
      ><a name="8766" href="Stlc.html#620" class="InductiveConstructor Operator"
      >&#8658;</a
      ><a name="8767"
      > </a
      ><a name="8768" href="Stlc.html#609" class="InductiveConstructor"
      >&#120121;</a
      ><a name="8769" class="Symbol"
      >)</a
      ><a name="8770"
      > </a
      ><a name="8771" href="Stlc.html#743" class="InductiveConstructor Operator"
      >]</a
      ><a name="8772"
      > </a
      ><a name="8773" href="Stlc.html#743" class="InductiveConstructor Operator"
      >&#955;[</a
      ><a name="8775"
      > </a
      ><a name="8776" href="Stlc.html#919" class="Function"
      >x</a
      ><a name="8777"
      > </a
      ><a name="8778" href="Stlc.html#743" class="InductiveConstructor Operator"
      >&#8758;</a
      ><a name="8779"
      > </a
      ><a name="8780" href="Stlc.html#609" class="InductiveConstructor"
      >&#120121;</a
      ><a name="8781"
      > </a
      ><a name="8782" href="Stlc.html#743" class="InductiveConstructor Operator"
      >]</a
      ><a name="8783"
      > </a
      ><a name="8784" href="Stlc.html#727" class="InductiveConstructor"
      >`</a
      ><a name="8785"
      > </a
      ><a name="8786" href="Stlc.html#917" class="Function"
      >f</a
      ><a name="8787"
      > </a
      ><a name="8788" href="Stlc.html#779" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="8789"
      > </a
      ><a name="8790" href="Stlc.html#727" class="InductiveConstructor"
      >`</a
      ><a name="8791"
      > </a
      ><a name="8792" href="Stlc.html#919" class="Function"
      >x</a
      ><a name="8793" class="Symbol"
      >)</a
      ><a name="8794"
      >
  </a
      ><a name="8797" href="StlcProp.html#8797" class="Postulate"
      >example-free&#8326;</a
      ><a name="8810"
      > </a
      ><a name="8811" class="Symbol"
      >:</a
      ><a name="8812"
      > </a
      ><a name="8813" href="Stlc.html#917" class="Function"
      >f</a
      ><a name="8814"
      > </a
      ><a name="8815" href="StlcProp.html#8117" class="Function Operator"
      >&#8713;</a
      ><a name="8816"
      > </a
      ><a name="8817" class="Symbol"
      >(</a
      ><a name="8818" href="Stlc.html#743" class="InductiveConstructor Operator"
      >&#955;[</a
      ><a name="8820"
      > </a
      ><a name="8821" href="Stlc.html#917" class="Function"
      >f</a
      ><a name="8822"
      > </a
      ><a name="8823" href="Stlc.html#743" class="InductiveConstructor Operator"
      >&#8758;</a
      ><a name="8824"
      > </a
      ><a name="8825" class="Symbol"
      >(</a
      ><a name="8826" href="Stlc.html#609" class="InductiveConstructor"
      >&#120121;</a
      ><a name="8827"
      > </a
      ><a name="8828" href="Stlc.html#620" class="InductiveConstructor Operator"
      >&#8658;</a
      ><a name="8829"
      > </a
      ><a name="8830" href="Stlc.html#609" class="InductiveConstructor"
      >&#120121;</a
      ><a name="8831" class="Symbol"
      >)</a
      ><a name="8832"
      > </a
      ><a name="8833" href="Stlc.html#743" class="InductiveConstructor Operator"
      >]</a
      ><a name="8834"
      > </a
      ><a name="8835" href="Stlc.html#743" class="InductiveConstructor Operator"
      >&#955;[</a
      ><a name="8837"
      > </a
      ><a name="8838" href="Stlc.html#919" class="Function"
      >x</a
      ><a name="8839"
      > </a
      ><a name="8840" href="Stlc.html#743" class="InductiveConstructor Operator"
      >&#8758;</a
      ><a name="8841"
      > </a
      ><a name="8842" href="Stlc.html#609" class="InductiveConstructor"
      >&#120121;</a
      ><a name="8843"
      > </a
      ><a name="8844" href="Stlc.html#743" class="InductiveConstructor Operator"
      >]</a
      ><a name="8845"
      > </a
      ><a name="8846" href="Stlc.html#727" class="InductiveConstructor"
      >`</a
      ><a name="8847"
      > </a
      ><a name="8848" href="Stlc.html#917" class="Function"
      >f</a
      ><a name="8849"
      > </a
      ><a name="8850" href="Stlc.html#779" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="8851"
      > </a
      ><a name="8852" href="Stlc.html#727" class="InductiveConstructor"
      >`</a
      ><a name="8853"
      > </a
      ><a name="8854" href="Stlc.html#919" class="Function"
      >x</a
      ><a name="8855" class="Symbol"
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

<a name="9338" href="StlcProp.html#9338" class="Function"
      >freeLemma</a
      ><a name="9347"
      > </a
      ><a name="9348" class="Symbol"
      >:</a
      ><a name="9349"
      > </a
      ><a name="9350" class="Symbol"
      >&#8704;</a
      ><a name="9351"
      > </a
      ><a name="9352" class="Symbol"
      >{</a
      ><a name="9353" href="StlcProp.html#9353" class="Bound"
      >x</a
      ><a name="9354"
      > </a
      ><a name="9355" href="StlcProp.html#9355" class="Bound"
      >M</a
      ><a name="9356"
      > </a
      ><a name="9357" href="StlcProp.html#9357" class="Bound"
      >A</a
      ><a name="9358"
      > </a
      ><a name="9359" href="StlcProp.html#9359" class="Bound"
      >&#915;</a
      ><a name="9360" class="Symbol"
      >}</a
      ><a name="9361"
      > </a
      ><a name="9362" class="Symbol"
      >&#8594;</a
      ><a name="9363"
      > </a
      ><a name="9364" href="StlcProp.html#9353" class="Bound"
      >x</a
      ><a name="9365"
      > </a
      ><a name="9366" href="StlcProp.html#7641" class="Datatype Operator"
      >&#8712;</a
      ><a name="9367"
      > </a
      ><a name="9368" href="StlcProp.html#9355" class="Bound"
      >M</a
      ><a name="9369"
      > </a
      ><a name="9370" class="Symbol"
      >&#8594;</a
      ><a name="9371"
      > </a
      ><a name="9372" href="StlcProp.html#9359" class="Bound"
      >&#915;</a
      ><a name="9373"
      > </a
      ><a name="9374" href="Stlc.html#3112" class="Datatype Operator"
      >&#8866;</a
      ><a name="9375"
      > </a
      ><a name="9376" href="StlcProp.html#9355" class="Bound"
      >M</a
      ><a name="9377"
      > </a
      ><a name="9378" href="Stlc.html#3112" class="Datatype Operator"
      >&#8758;</a
      ><a name="9379"
      > </a
      ><a name="9380" href="StlcProp.html#9357" class="Bound"
      >A</a
      ><a name="9381"
      > </a
      ><a name="9382" class="Symbol"
      >&#8594;</a
      ><a name="9383"
      > </a
      ><a name="9384" href="https://agda.github.io/agda-stdlib/Data.Product.html#823" class="Function"
      >&#8707;</a
      ><a name="9385"
      > </a
      ><a name="9386" class="Symbol"
      >&#955;</a
      ><a name="9387"
      > </a
      ><a name="9388" href="StlcProp.html#9388" class="Bound"
      >B</a
      ><a name="9389"
      > </a
      ><a name="9390" class="Symbol"
      >&#8594;</a
      ><a name="9391"
      > </a
      ><a name="9392" href="StlcProp.html#9359" class="Bound"
      >&#915;</a
      ><a name="9393"
      > </a
      ><a name="9394" href="StlcProp.html#9353" class="Bound"
      >x</a
      ><a name="9395"
      > </a
      ><a name="9396" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="9397"
      > </a
      ><a name="9398" href="https://agda.github.io/agda-stdlib/Data.Maybe.Base.html#373" class="InductiveConstructor"
      >just</a
      ><a name="9402"
      > </a
      ><a name="9403" href="StlcProp.html#9388" class="Bound"
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

<a name="10846" href="StlcProp.html#9338" class="Function"
      >freeLemma</a
      ><a name="10855"
      > </a
      ><a name="10856" href="StlcProp.html#7671" class="InductiveConstructor"
      >free-`</a
      ><a name="10862"
      > </a
      ><a name="10863" class="Symbol"
      >(</a
      ><a name="10864" href="Stlc.html#3156" class="InductiveConstructor"
      >Ax</a
      ><a name="10866"
      > </a
      ><a name="10867" href="StlcProp.html#10867" class="Bound"
      >&#915;x&#8801;A</a
      ><a name="10871" class="Symbol"
      >)</a
      ><a name="10872"
      > </a
      ><a name="10873" class="Symbol"
      >=</a
      ><a name="10874"
      > </a
      ><a name="10875" class="Symbol"
      >(_</a
      ><a name="10877"
      > </a
      ><a name="10878" href="https://agda.github.io/agda-stdlib/Data.Product.html#509" class="InductiveConstructor Operator"
      >,</a
      ><a name="10879"
      > </a
      ><a name="10880" href="StlcProp.html#10867" class="Bound"
      >&#915;x&#8801;A</a
      ><a name="10884" class="Symbol"
      >)</a
      ><a name="10885"
      >
</a
      ><a name="10886" href="StlcProp.html#9338" class="Function"
      >freeLemma</a
      ><a name="10895"
      > </a
      ><a name="10896" class="Symbol"
      >(</a
      ><a name="10897" href="StlcProp.html#7760" class="InductiveConstructor"
      >free-&#183;&#8321;</a
      ><a name="10904"
      > </a
      ><a name="10905" href="StlcProp.html#10905" class="Bound"
      >x&#8712;L</a
      ><a name="10908" class="Symbol"
      >)</a
      ><a name="10909"
      > </a
      ><a name="10910" class="Symbol"
      >(</a
      ><a name="10911" href="Stlc.html#3287" class="InductiveConstructor"
      >&#8658;-E</a
      ><a name="10914"
      > </a
      ><a name="10915" href="StlcProp.html#10915" class="Bound"
      >&#8866;L</a
      ><a name="10917"
      > </a
      ><a name="10918" href="StlcProp.html#10918" class="Bound"
      >&#8866;M</a
      ><a name="10920" class="Symbol"
      >)</a
      ><a name="10921"
      > </a
      ><a name="10922" class="Symbol"
      >=</a
      ><a name="10923"
      > </a
      ><a name="10924" href="StlcProp.html#9338" class="Function"
      >freeLemma</a
      ><a name="10933"
      > </a
      ><a name="10934" href="StlcProp.html#10905" class="Bound"
      >x&#8712;L</a
      ><a name="10937"
      > </a
      ><a name="10938" href="StlcProp.html#10915" class="Bound"
      >&#8866;L</a
      ><a name="10940"
      >
</a
      ><a name="10941" href="StlcProp.html#9338" class="Function"
      >freeLemma</a
      ><a name="10950"
      > </a
      ><a name="10951" class="Symbol"
      >(</a
      ><a name="10952" href="StlcProp.html#7804" class="InductiveConstructor"
      >free-&#183;&#8322;</a
      ><a name="10959"
      > </a
      ><a name="10960" href="StlcProp.html#10960" class="Bound"
      >x&#8712;M</a
      ><a name="10963" class="Symbol"
      >)</a
      ><a name="10964"
      > </a
      ><a name="10965" class="Symbol"
      >(</a
      ><a name="10966" href="Stlc.html#3287" class="InductiveConstructor"
      >&#8658;-E</a
      ><a name="10969"
      > </a
      ><a name="10970" href="StlcProp.html#10970" class="Bound"
      >&#8866;L</a
      ><a name="10972"
      > </a
      ><a name="10973" href="StlcProp.html#10973" class="Bound"
      >&#8866;M</a
      ><a name="10975" class="Symbol"
      >)</a
      ><a name="10976"
      > </a
      ><a name="10977" class="Symbol"
      >=</a
      ><a name="10978"
      > </a
      ><a name="10979" href="StlcProp.html#9338" class="Function"
      >freeLemma</a
      ><a name="10988"
      > </a
      ><a name="10989" href="StlcProp.html#10960" class="Bound"
      >x&#8712;M</a
      ><a name="10992"
      > </a
      ><a name="10993" href="StlcProp.html#10973" class="Bound"
      >&#8866;M</a
      ><a name="10995"
      >
</a
      ><a name="10996" href="StlcProp.html#9338" class="Function"
      >freeLemma</a
      ><a name="11005"
      > </a
      ><a name="11006" class="Symbol"
      >(</a
      ><a name="11007" href="StlcProp.html#7848" class="InductiveConstructor"
      >free-if&#8321;</a
      ><a name="11015"
      > </a
      ><a name="11016" href="StlcProp.html#11016" class="Bound"
      >x&#8712;L</a
      ><a name="11019" class="Symbol"
      >)</a
      ><a name="11020"
      > </a
      ><a name="11021" class="Symbol"
      >(</a
      ><a name="11022" href="Stlc.html#3434" class="InductiveConstructor"
      >&#120121;-E</a
      ><a name="11025"
      > </a
      ><a name="11026" href="StlcProp.html#11026" class="Bound"
      >&#8866;L</a
      ><a name="11028"
      > </a
      ><a name="11029" href="StlcProp.html#11029" class="Bound"
      >&#8866;M</a
      ><a name="11031"
      > </a
      ><a name="11032" href="StlcProp.html#11032" class="Bound"
      >&#8866;N</a
      ><a name="11034" class="Symbol"
      >)</a
      ><a name="11035"
      > </a
      ><a name="11036" class="Symbol"
      >=</a
      ><a name="11037"
      > </a
      ><a name="11038" href="StlcProp.html#9338" class="Function"
      >freeLemma</a
      ><a name="11047"
      > </a
      ><a name="11048" href="StlcProp.html#11016" class="Bound"
      >x&#8712;L</a
      ><a name="11051"
      > </a
      ><a name="11052" href="StlcProp.html#11026" class="Bound"
      >&#8866;L</a
      ><a name="11054"
      >
</a
      ><a name="11055" href="StlcProp.html#9338" class="Function"
      >freeLemma</a
      ><a name="11064"
      > </a
      ><a name="11065" class="Symbol"
      >(</a
      ><a name="11066" href="StlcProp.html#7908" class="InductiveConstructor"
      >free-if&#8322;</a
      ><a name="11074"
      > </a
      ><a name="11075" href="StlcProp.html#11075" class="Bound"
      >x&#8712;M</a
      ><a name="11078" class="Symbol"
      >)</a
      ><a name="11079"
      > </a
      ><a name="11080" class="Symbol"
      >(</a
      ><a name="11081" href="Stlc.html#3434" class="InductiveConstructor"
      >&#120121;-E</a
      ><a name="11084"
      > </a
      ><a name="11085" href="StlcProp.html#11085" class="Bound"
      >&#8866;L</a
      ><a name="11087"
      > </a
      ><a name="11088" href="StlcProp.html#11088" class="Bound"
      >&#8866;M</a
      ><a name="11090"
      > </a
      ><a name="11091" href="StlcProp.html#11091" class="Bound"
      >&#8866;N</a
      ><a name="11093" class="Symbol"
      >)</a
      ><a name="11094"
      > </a
      ><a name="11095" class="Symbol"
      >=</a
      ><a name="11096"
      > </a
      ><a name="11097" href="StlcProp.html#9338" class="Function"
      >freeLemma</a
      ><a name="11106"
      > </a
      ><a name="11107" href="StlcProp.html#11075" class="Bound"
      >x&#8712;M</a
      ><a name="11110"
      > </a
      ><a name="11111" href="StlcProp.html#11088" class="Bound"
      >&#8866;M</a
      ><a name="11113"
      >
</a
      ><a name="11114" href="StlcProp.html#9338" class="Function"
      >freeLemma</a
      ><a name="11123"
      > </a
      ><a name="11124" class="Symbol"
      >(</a
      ><a name="11125" href="StlcProp.html#7968" class="InductiveConstructor"
      >free-if&#8323;</a
      ><a name="11133"
      > </a
      ><a name="11134" href="StlcProp.html#11134" class="Bound"
      >x&#8712;N</a
      ><a name="11137" class="Symbol"
      >)</a
      ><a name="11138"
      > </a
      ><a name="11139" class="Symbol"
      >(</a
      ><a name="11140" href="Stlc.html#3434" class="InductiveConstructor"
      >&#120121;-E</a
      ><a name="11143"
      > </a
      ><a name="11144" href="StlcProp.html#11144" class="Bound"
      >&#8866;L</a
      ><a name="11146"
      > </a
      ><a name="11147" href="StlcProp.html#11147" class="Bound"
      >&#8866;M</a
      ><a name="11149"
      > </a
      ><a name="11150" href="StlcProp.html#11150" class="Bound"
      >&#8866;N</a
      ><a name="11152" class="Symbol"
      >)</a
      ><a name="11153"
      > </a
      ><a name="11154" class="Symbol"
      >=</a
      ><a name="11155"
      > </a
      ><a name="11156" href="StlcProp.html#9338" class="Function"
      >freeLemma</a
      ><a name="11165"
      > </a
      ><a name="11166" href="StlcProp.html#11134" class="Bound"
      >x&#8712;N</a
      ><a name="11169"
      > </a
      ><a name="11170" href="StlcProp.html#11150" class="Bound"
      >&#8866;N</a
      ><a name="11172"
      >
</a
      ><a name="11173" href="StlcProp.html#9338" class="Function"
      >freeLemma</a
      ><a name="11182"
      > </a
      ><a name="11183" class="Symbol"
      >(</a
      ><a name="11184" href="StlcProp.html#7699" class="InductiveConstructor"
      >free-&#955;</a
      ><a name="11190"
      > </a
      ><a name="11191" class="Symbol"
      >{</a
      ><a name="11192" href="StlcProp.html#11192" class="Bound"
      >x</a
      ><a name="11193" class="Symbol"
      >}</a
      ><a name="11194"
      > </a
      ><a name="11195" class="Symbol"
      >{</a
      ><a name="11196" href="StlcProp.html#11196" class="Bound"
      >y</a
      ><a name="11197" class="Symbol"
      >}</a
      ><a name="11198"
      > </a
      ><a name="11199" href="StlcProp.html#11199" class="Bound"
      >y&#8802;x</a
      ><a name="11202"
      > </a
      ><a name="11203" href="StlcProp.html#11203" class="Bound"
      >x&#8712;N</a
      ><a name="11206" class="Symbol"
      >)</a
      ><a name="11207"
      > </a
      ><a name="11208" class="Symbol"
      >(</a
      ><a name="11209" href="Stlc.html#3210" class="InductiveConstructor"
      >&#8658;-I</a
      ><a name="11212"
      > </a
      ><a name="11213" href="StlcProp.html#11213" class="Bound"
      >&#8866;N</a
      ><a name="11215" class="Symbol"
      >)</a
      ><a name="11216"
      > </a
      ><a name="11217" class="Keyword"
      >with</a
      ><a name="11221"
      > </a
      ><a name="11222" href="StlcProp.html#9338" class="Function"
      >freeLemma</a
      ><a name="11231"
      > </a
      ><a name="11232" href="StlcProp.html#11203" class="Bound"
      >x&#8712;N</a
      ><a name="11235"
      > </a
      ><a name="11236" href="StlcProp.html#11213" class="Bound"
      >&#8866;N</a
      ><a name="11238"
      >
</a
      ><a name="11239" class="Symbol"
      >...</a
      ><a name="11242"
      > </a
      ><a name="11243" class="Symbol"
      >|</a
      ><a name="11244"
      > </a
      ><a name="11245" href="StlcProp.html#11245" class="Bound"
      >&#915;x&#8801;C</a
      ><a name="11249"
      > </a
      ><a name="11250" class="Keyword"
      >with</a
      ><a name="11254"
      > </a
      ><a name="11255" href="StlcProp.html#11196" class="Bound"
      >y</a
      ><a name="11256"
      > </a
      ><a name="11257" href="Maps.html#2509" class="Function Operator"
      >&#8799;</a
      ><a name="11258"
      > </a
      ><a name="11259" href="StlcProp.html#11192" class="Bound"
      >x</a
      ><a name="11260"
      >
</a
      ><a name="11261" class="Symbol"
      >...</a
      ><a name="11264"
      > </a
      ><a name="11265" class="Symbol"
      >|</a
      ><a name="11266"
      > </a
      ><a name="11267" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#520" class="InductiveConstructor"
      >yes</a
      ><a name="11270"
      > </a
      ><a name="11271" href="StlcProp.html#11271" class="Bound"
      >y&#8801;x</a
      ><a name="11274"
      > </a
      ><a name="11275" class="Symbol"
      >=</a
      ><a name="11276"
      > </a
      ><a name="11277" href="https://agda.github.io/agda-stdlib/Data.Empty.html#348" class="Function"
      >&#8869;-elim</a
      ><a name="11283"
      > </a
      ><a name="11284" class="Symbol"
      >(</a
      ><a name="11285" href="StlcProp.html#11199" class="Bound"
      >y&#8802;x</a
      ><a name="11288"
      > </a
      ><a name="11289" href="StlcProp.html#11271" class="Bound"
      >y&#8801;x</a
      ><a name="11292" class="Symbol"
      >)</a
      ><a name="11293"
      >
</a
      ><a name="11294" class="Symbol"
      >...</a
      ><a name="11297"
      > </a
      ><a name="11298" class="Symbol"
      >|</a
      ><a name="11299"
      > </a
      ><a name="11300" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#547" class="InductiveConstructor"
      >no</a
      ><a name="11302"
      >  </a
      ><a name="11304" class="Symbol"
      >_</a
      ><a name="11305"
      >   </a
      ><a name="11308" class="Symbol"
      >=</a
      ><a name="11309"
      > </a
      ><a name="11310" href="StlcProp.html#11245" class="Bound"
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

<a name="11747" class="Keyword"
      >postulate</a
      ><a name="11756"
      >
  </a
      ><a name="11759" href="StlcProp.html#11759" class="Postulate"
      >&#8709;&#8866;-closed</a
      ><a name="11768"
      > </a
      ><a name="11769" class="Symbol"
      >:</a
      ><a name="11770"
      > </a
      ><a name="11771" class="Symbol"
      >&#8704;</a
      ><a name="11772"
      > </a
      ><a name="11773" class="Symbol"
      >{</a
      ><a name="11774" href="StlcProp.html#11774" class="Bound"
      >M</a
      ><a name="11775"
      > </a
      ><a name="11776" href="StlcProp.html#11776" class="Bound"
      >A</a
      ><a name="11777" class="Symbol"
      >}</a
      ><a name="11778"
      > </a
      ><a name="11779" class="Symbol"
      >&#8594;</a
      ><a name="11780"
      > </a
      ><a name="11781" href="Maps.html#10265" class="Function"
      >&#8709;</a
      ><a name="11782"
      > </a
      ><a name="11783" href="Stlc.html#3112" class="Datatype Operator"
      >&#8866;</a
      ><a name="11784"
      > </a
      ><a name="11785" href="StlcProp.html#11774" class="Bound"
      >M</a
      ><a name="11786"
      > </a
      ><a name="11787" href="Stlc.html#3112" class="Datatype Operator"
      >&#8758;</a
      ><a name="11788"
      > </a
      ><a name="11789" href="StlcProp.html#11776" class="Bound"
      >A</a
      ><a name="11790"
      > </a
      ><a name="11791" class="Symbol"
      >&#8594;</a
      ><a name="11792"
      > </a
      ><a name="11793" href="StlcProp.html#8158" class="Function"
      >closed</a
      ><a name="11799"
      > </a
      ><a name="11800" href="StlcProp.html#11774" class="Bound"
      >M</a
      >

</pre>

<div class="hidden">
<pre class="Agda">

<a name="11848" href="StlcProp.html#11848" class="Function"
      >contradiction</a
      ><a name="11861"
      > </a
      ><a name="11862" class="Symbol"
      >:</a
      ><a name="11863"
      > </a
      ><a name="11864" class="Symbol"
      >&#8704;</a
      ><a name="11865"
      > </a
      ><a name="11866" class="Symbol"
      >{</a
      ><a name="11867" href="StlcProp.html#11867" class="Bound"
      >X</a
      ><a name="11868"
      > </a
      ><a name="11869" class="Symbol"
      >:</a
      ><a name="11870"
      > </a
      ><a name="11871" class="PrimitiveType"
      >Set</a
      ><a name="11874" class="Symbol"
      >}</a
      ><a name="11875"
      > </a
      ><a name="11876" class="Symbol"
      >&#8594;</a
      ><a name="11877"
      > </a
      ><a name="11878" class="Symbol"
      >&#8704;</a
      ><a name="11879"
      > </a
      ><a name="11880" class="Symbol"
      >{</a
      ><a name="11881" href="StlcProp.html#11881" class="Bound"
      >x</a
      ><a name="11882"
      > </a
      ><a name="11883" class="Symbol"
      >:</a
      ><a name="11884"
      > </a
      ><a name="11885" href="StlcProp.html#11867" class="Bound"
      >X</a
      ><a name="11886" class="Symbol"
      >}</a
      ><a name="11887"
      > </a
      ><a name="11888" class="Symbol"
      >&#8594;</a
      ><a name="11889"
      > </a
      ><a name="11890" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#414" class="Function Operator"
      >&#172;</a
      ><a name="11891"
      > </a
      ><a name="11892" class="Symbol"
      >(</a
      ><a name="11893" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >_&#8801;_</a
      ><a name="11896"
      > </a
      ><a name="11897" class="Symbol"
      >{</a
      ><a name="11898" class="Argument"
      >A</a
      ><a name="11899"
      > </a
      ><a name="11900" class="Symbol"
      >=</a
      ><a name="11901"
      > </a
      ><a name="11902" href="https://agda.github.io/agda-stdlib/Data.Maybe.Base.html#335" class="Datatype"
      >Maybe</a
      ><a name="11907"
      > </a
      ><a name="11908" href="StlcProp.html#11867" class="Bound"
      >X</a
      ><a name="11909" class="Symbol"
      >}</a
      ><a name="11910"
      > </a
      ><a name="11911" class="Symbol"
      >(</a
      ><a name="11912" href="https://agda.github.io/agda-stdlib/Data.Maybe.Base.html#373" class="InductiveConstructor"
      >just</a
      ><a name="11916"
      > </a
      ><a name="11917" href="StlcProp.html#11881" class="Bound"
      >x</a
      ><a name="11918" class="Symbol"
      >)</a
      ><a name="11919"
      > </a
      ><a name="11920" href="https://agda.github.io/agda-stdlib/Data.Maybe.Base.html#403" class="InductiveConstructor"
      >nothing</a
      ><a name="11927" class="Symbol"
      >)</a
      ><a name="11928"
      >
</a
      ><a name="11929" href="StlcProp.html#11848" class="Function"
      >contradiction</a
      ><a name="11942"
      > </a
      ><a name="11943" class="Symbol"
      >()</a
      ><a name="11945"
      >

</a
      ><a name="11947" href="StlcProp.html#11947" class="Function"
      >&#8709;&#8866;-closed&#8242;</a
      ><a name="11957"
      > </a
      ><a name="11958" class="Symbol"
      >:</a
      ><a name="11959"
      > </a
      ><a name="11960" class="Symbol"
      >&#8704;</a
      ><a name="11961"
      > </a
      ><a name="11962" class="Symbol"
      >{</a
      ><a name="11963" href="StlcProp.html#11963" class="Bound"
      >M</a
      ><a name="11964"
      > </a
      ><a name="11965" href="StlcProp.html#11965" class="Bound"
      >A</a
      ><a name="11966" class="Symbol"
      >}</a
      ><a name="11967"
      > </a
      ><a name="11968" class="Symbol"
      >&#8594;</a
      ><a name="11969"
      > </a
      ><a name="11970" href="Maps.html#10265" class="Function"
      >&#8709;</a
      ><a name="11971"
      > </a
      ><a name="11972" href="Stlc.html#3112" class="Datatype Operator"
      >&#8866;</a
      ><a name="11973"
      > </a
      ><a name="11974" href="StlcProp.html#11963" class="Bound"
      >M</a
      ><a name="11975"
      > </a
      ><a name="11976" href="Stlc.html#3112" class="Datatype Operator"
      >&#8758;</a
      ><a name="11977"
      > </a
      ><a name="11978" href="StlcProp.html#11965" class="Bound"
      >A</a
      ><a name="11979"
      > </a
      ><a name="11980" class="Symbol"
      >&#8594;</a
      ><a name="11981"
      > </a
      ><a name="11982" href="StlcProp.html#8158" class="Function"
      >closed</a
      ><a name="11988"
      > </a
      ><a name="11989" href="StlcProp.html#11963" class="Bound"
      >M</a
      ><a name="11990"
      >
</a
      ><a name="11991" href="StlcProp.html#11947" class="Function"
      >&#8709;&#8866;-closed&#8242;</a
      ><a name="12001"
      > </a
      ><a name="12002" class="Symbol"
      >{</a
      ><a name="12003" href="StlcProp.html#12003" class="Bound"
      >M</a
      ><a name="12004" class="Symbol"
      >}</a
      ><a name="12005"
      > </a
      ><a name="12006" class="Symbol"
      >{</a
      ><a name="12007" href="StlcProp.html#12007" class="Bound"
      >A</a
      ><a name="12008" class="Symbol"
      >}</a
      ><a name="12009"
      > </a
      ><a name="12010" href="StlcProp.html#12010" class="Bound"
      >&#8866;M</a
      ><a name="12012"
      > </a
      ><a name="12013" class="Symbol"
      >{</a
      ><a name="12014" href="StlcProp.html#12014" class="Bound"
      >x</a
      ><a name="12015" class="Symbol"
      >}</a
      ><a name="12016"
      > </a
      ><a name="12017" href="StlcProp.html#12017" class="Bound"
      >x&#8712;M</a
      ><a name="12020"
      > </a
      ><a name="12021" class="Keyword"
      >with</a
      ><a name="12025"
      > </a
      ><a name="12026" href="StlcProp.html#9338" class="Function"
      >freeLemma</a
      ><a name="12035"
      > </a
      ><a name="12036" href="StlcProp.html#12017" class="Bound"
      >x&#8712;M</a
      ><a name="12039"
      > </a
      ><a name="12040" href="StlcProp.html#12010" class="Bound"
      >&#8866;M</a
      ><a name="12042"
      >
</a
      ><a name="12043" class="Symbol"
      >...</a
      ><a name="12046"
      > </a
      ><a name="12047" class="Symbol"
      >|</a
      ><a name="12048"
      > </a
      ><a name="12049" class="Symbol"
      >(</a
      ><a name="12050" href="StlcProp.html#12050" class="Bound"
      >B</a
      ><a name="12051"
      > </a
      ><a name="12052" href="https://agda.github.io/agda-stdlib/Data.Product.html#509" class="InductiveConstructor Operator"
      >,</a
      ><a name="12053"
      > </a
      ><a name="12054" href="StlcProp.html#12054" class="Bound"
      >&#8709;x&#8801;B</a
      ><a name="12058" class="Symbol"
      >)</a
      ><a name="12059"
      > </a
      ><a name="12060" class="Symbol"
      >=</a
      ><a name="12061"
      > </a
      ><a name="12062" href="StlcProp.html#11848" class="Function"
      >contradiction</a
      ><a name="12075"
      > </a
      ><a name="12076" class="Symbol"
      >(</a
      ><a name="12077" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.Core.html#632" class="Function"
      >trans</a
      ><a name="12082"
      > </a
      ><a name="12083" class="Symbol"
      >(</a
      ><a name="12084" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.Core.html#565" class="Function"
      >sym</a
      ><a name="12087"
      > </a
      ><a name="12088" href="StlcProp.html#12054" class="Bound"
      >&#8709;x&#8801;B</a
      ><a name="12092" class="Symbol"
      >)</a
      ><a name="12093"
      > </a
      ><a name="12094" class="Symbol"
      >(</a
      ><a name="12095" href="Maps.html#10573" class="Function"
      >apply-&#8709;</a
      ><a name="12102"
      > </a
      ><a name="12103" href="StlcProp.html#12014" class="Bound"
      >x</a
      ><a name="12104" class="Symbol"
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

<a name="12458" href="StlcProp.html#12458" class="Function"
      >contextLemma</a
      ><a name="12470"
      > </a
      ><a name="12471" class="Symbol"
      >:</a
      ><a name="12472"
      > </a
      ><a name="12473" class="Symbol"
      >&#8704;</a
      ><a name="12474"
      > </a
      ><a name="12475" class="Symbol"
      >{</a
      ><a name="12476" href="StlcProp.html#12476" class="Bound"
      >&#915;</a
      ><a name="12477"
      > </a
      ><a name="12478" href="StlcProp.html#12478" class="Bound"
      >&#915;&#8242;</a
      ><a name="12480"
      > </a
      ><a name="12481" href="StlcProp.html#12481" class="Bound"
      >M</a
      ><a name="12482"
      > </a
      ><a name="12483" href="StlcProp.html#12483" class="Bound"
      >A</a
      ><a name="12484" class="Symbol"
      >}</a
      ><a name="12485"
      >
        </a
      ><a name="12494" class="Symbol"
      >&#8594;</a
      ><a name="12495"
      > </a
      ><a name="12496" class="Symbol"
      >(&#8704;</a
      ><a name="12498"
      > </a
      ><a name="12499" class="Symbol"
      >{</a
      ><a name="12500" href="StlcProp.html#12500" class="Bound"
      >x</a
      ><a name="12501" class="Symbol"
      >}</a
      ><a name="12502"
      > </a
      ><a name="12503" class="Symbol"
      >&#8594;</a
      ><a name="12504"
      > </a
      ><a name="12505" href="StlcProp.html#12500" class="Bound"
      >x</a
      ><a name="12506"
      > </a
      ><a name="12507" href="StlcProp.html#7641" class="Datatype Operator"
      >&#8712;</a
      ><a name="12508"
      > </a
      ><a name="12509" href="StlcProp.html#12481" class="Bound"
      >M</a
      ><a name="12510"
      > </a
      ><a name="12511" class="Symbol"
      >&#8594;</a
      ><a name="12512"
      > </a
      ><a name="12513" href="StlcProp.html#12476" class="Bound"
      >&#915;</a
      ><a name="12514"
      > </a
      ><a name="12515" href="StlcProp.html#12500" class="Bound"
      >x</a
      ><a name="12516"
      > </a
      ><a name="12517" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="12518"
      > </a
      ><a name="12519" href="StlcProp.html#12478" class="Bound"
      >&#915;&#8242;</a
      ><a name="12521"
      > </a
      ><a name="12522" href="StlcProp.html#12500" class="Bound"
      >x</a
      ><a name="12523" class="Symbol"
      >)</a
      ><a name="12524"
      >
        </a
      ><a name="12533" class="Symbol"
      >&#8594;</a
      ><a name="12534"
      > </a
      ><a name="12535" href="StlcProp.html#12476" class="Bound"
      >&#915;</a
      ><a name="12536"
      >  </a
      ><a name="12538" href="Stlc.html#3112" class="Datatype Operator"
      >&#8866;</a
      ><a name="12539"
      > </a
      ><a name="12540" href="StlcProp.html#12481" class="Bound"
      >M</a
      ><a name="12541"
      > </a
      ><a name="12542" href="Stlc.html#3112" class="Datatype Operator"
      >&#8758;</a
      ><a name="12543"
      > </a
      ><a name="12544" href="StlcProp.html#12483" class="Bound"
      >A</a
      ><a name="12545"
      >
        </a
      ><a name="12554" class="Symbol"
      >&#8594;</a
      ><a name="12555"
      > </a
      ><a name="12556" href="StlcProp.html#12478" class="Bound"
      >&#915;&#8242;</a
      ><a name="12558"
      > </a
      ><a name="12559" href="Stlc.html#3112" class="Datatype Operator"
      >&#8866;</a
      ><a name="12560"
      > </a
      ><a name="12561" href="StlcProp.html#12481" class="Bound"
      >M</a
      ><a name="12562"
      > </a
      ><a name="12563" href="Stlc.html#3112" class="Datatype Operator"
      >&#8758;</a
      ><a name="12564"
      > </a
      ><a name="12565" href="StlcProp.html#12483" class="Bound"
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

<a name="14738" href="StlcProp.html#12458" class="Function"
      >contextLemma</a
      ><a name="14750"
      > </a
      ><a name="14751" href="StlcProp.html#14751" class="Bound"
      >&#915;~&#915;&#8242;</a
      ><a name="14755"
      > </a
      ><a name="14756" class="Symbol"
      >(</a
      ><a name="14757" href="Stlc.html#3156" class="InductiveConstructor"
      >Ax</a
      ><a name="14759"
      > </a
      ><a name="14760" href="StlcProp.html#14760" class="Bound"
      >&#915;x&#8801;A</a
      ><a name="14764" class="Symbol"
      >)</a
      ><a name="14765"
      > </a
      ><a name="14766" class="Keyword"
      >rewrite</a
      ><a name="14773"
      > </a
      ><a name="14774" class="Symbol"
      >(</a
      ><a name="14775" href="StlcProp.html#14751" class="Bound"
      >&#915;~&#915;&#8242;</a
      ><a name="14779"
      > </a
      ><a name="14780" href="StlcProp.html#7671" class="InductiveConstructor"
      >free-`</a
      ><a name="14786" class="Symbol"
      >)</a
      ><a name="14787"
      > </a
      ><a name="14788" class="Symbol"
      >=</a
      ><a name="14789"
      > </a
      ><a name="14790" href="Stlc.html#3156" class="InductiveConstructor"
      >Ax</a
      ><a name="14792"
      > </a
      ><a name="14793" href="StlcProp.html#14760" class="Bound"
      >&#915;x&#8801;A</a
      ><a name="14797"
      >
</a
      ><a name="14798" href="StlcProp.html#12458" class="Function"
      >contextLemma</a
      ><a name="14810"
      > </a
      ><a name="14811" class="Symbol"
      >{</a
      ><a name="14812" href="StlcProp.html#14812" class="Bound"
      >&#915;</a
      ><a name="14813" class="Symbol"
      >}</a
      ><a name="14814"
      > </a
      ><a name="14815" class="Symbol"
      >{</a
      ><a name="14816" href="StlcProp.html#14816" class="Bound"
      >&#915;&#8242;</a
      ><a name="14818" class="Symbol"
      >}</a
      ><a name="14819"
      > </a
      ><a name="14820" class="Symbol"
      >{</a
      ><a name="14821" href="Stlc.html#743" class="InductiveConstructor Operator"
      >&#955;[</a
      ><a name="14823"
      > </a
      ><a name="14824" href="StlcProp.html#14824" class="Bound"
      >x</a
      ><a name="14825"
      > </a
      ><a name="14826" href="Stlc.html#743" class="InductiveConstructor Operator"
      >&#8758;</a
      ><a name="14827"
      > </a
      ><a name="14828" href="StlcProp.html#14828" class="Bound"
      >A</a
      ><a name="14829"
      > </a
      ><a name="14830" href="Stlc.html#743" class="InductiveConstructor Operator"
      >]</a
      ><a name="14831"
      > </a
      ><a name="14832" href="StlcProp.html#14832" class="Bound"
      >N</a
      ><a name="14833" class="Symbol"
      >}</a
      ><a name="14834"
      > </a
      ><a name="14835" href="StlcProp.html#14835" class="Bound"
      >&#915;~&#915;&#8242;</a
      ><a name="14839"
      > </a
      ><a name="14840" class="Symbol"
      >(</a
      ><a name="14841" href="Stlc.html#3210" class="InductiveConstructor"
      >&#8658;-I</a
      ><a name="14844"
      > </a
      ><a name="14845" href="StlcProp.html#14845" class="Bound"
      >&#8866;N</a
      ><a name="14847" class="Symbol"
      >)</a
      ><a name="14848"
      > </a
      ><a name="14849" class="Symbol"
      >=</a
      ><a name="14850"
      > </a
      ><a name="14851" href="Stlc.html#3210" class="InductiveConstructor"
      >&#8658;-I</a
      ><a name="14854"
      > </a
      ><a name="14855" class="Symbol"
      >(</a
      ><a name="14856" href="StlcProp.html#12458" class="Function"
      >contextLemma</a
      ><a name="14868"
      > </a
      ><a name="14869" href="StlcProp.html#14890" class="Function"
      >&#915;x~&#915;&#8242;x</a
      ><a name="14875"
      > </a
      ><a name="14876" href="StlcProp.html#14845" class="Bound"
      >&#8866;N</a
      ><a name="14878" class="Symbol"
      >)</a
      ><a name="14879"
      >
  </a
      ><a name="14882" class="Keyword"
      >where</a
      ><a name="14887"
      >
  </a
      ><a name="14890" href="StlcProp.html#14890" class="Function"
      >&#915;x~&#915;&#8242;x</a
      ><a name="14896"
      > </a
      ><a name="14897" class="Symbol"
      >:</a
      ><a name="14898"
      > </a
      ><a name="14899" class="Symbol"
      >&#8704;</a
      ><a name="14900"
      > </a
      ><a name="14901" class="Symbol"
      >{</a
      ><a name="14902" href="StlcProp.html#14902" class="Bound"
      >y</a
      ><a name="14903" class="Symbol"
      >}</a
      ><a name="14904"
      > </a
      ><a name="14905" class="Symbol"
      >&#8594;</a
      ><a name="14906"
      > </a
      ><a name="14907" href="StlcProp.html#14902" class="Bound"
      >y</a
      ><a name="14908"
      > </a
      ><a name="14909" href="StlcProp.html#7641" class="Datatype Operator"
      >&#8712;</a
      ><a name="14910"
      > </a
      ><a name="14911" href="StlcProp.html#14832" class="Bound"
      >N</a
      ><a name="14912"
      > </a
      ><a name="14913" class="Symbol"
      >&#8594;</a
      ><a name="14914"
      > </a
      ><a name="14915" class="Symbol"
      >(</a
      ><a name="14916" href="StlcProp.html#14812" class="Bound"
      >&#915;</a
      ><a name="14917"
      > </a
      ><a name="14918" href="Maps.html#10368" class="Function Operator"
      >,</a
      ><a name="14919"
      > </a
      ><a name="14920" href="StlcProp.html#14824" class="Bound"
      >x</a
      ><a name="14921"
      > </a
      ><a name="14922" href="Maps.html#10368" class="Function Operator"
      >&#8758;</a
      ><a name="14923"
      > </a
      ><a name="14924" href="StlcProp.html#14828" class="Bound"
      >A</a
      ><a name="14925" class="Symbol"
      >)</a
      ><a name="14926"
      > </a
      ><a name="14927" href="StlcProp.html#14902" class="Bound"
      >y</a
      ><a name="14928"
      > </a
      ><a name="14929" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="14930"
      > </a
      ><a name="14931" class="Symbol"
      >(</a
      ><a name="14932" href="StlcProp.html#14816" class="Bound"
      >&#915;&#8242;</a
      ><a name="14934"
      > </a
      ><a name="14935" href="Maps.html#10368" class="Function Operator"
      >,</a
      ><a name="14936"
      > </a
      ><a name="14937" href="StlcProp.html#14824" class="Bound"
      >x</a
      ><a name="14938"
      > </a
      ><a name="14939" href="Maps.html#10368" class="Function Operator"
      >&#8758;</a
      ><a name="14940"
      > </a
      ><a name="14941" href="StlcProp.html#14828" class="Bound"
      >A</a
      ><a name="14942" class="Symbol"
      >)</a
      ><a name="14943"
      > </a
      ><a name="14944" href="StlcProp.html#14902" class="Bound"
      >y</a
      ><a name="14945"
      >
  </a
      ><a name="14948" href="StlcProp.html#14890" class="Function"
      >&#915;x~&#915;&#8242;x</a
      ><a name="14954"
      > </a
      ><a name="14955" class="Symbol"
      >{</a
      ><a name="14956" href="StlcProp.html#14956" class="Bound"
      >y</a
      ><a name="14957" class="Symbol"
      >}</a
      ><a name="14958"
      > </a
      ><a name="14959" href="StlcProp.html#14959" class="Bound"
      >y&#8712;N</a
      ><a name="14962"
      > </a
      ><a name="14963" class="Keyword"
      >with</a
      ><a name="14967"
      > </a
      ><a name="14968" href="StlcProp.html#14824" class="Bound"
      >x</a
      ><a name="14969"
      > </a
      ><a name="14970" href="Maps.html#2509" class="Function Operator"
      >&#8799;</a
      ><a name="14971"
      > </a
      ><a name="14972" href="StlcProp.html#14956" class="Bound"
      >y</a
      ><a name="14973"
      >
  </a
      ><a name="14976" class="Symbol"
      >...</a
      ><a name="14979"
      > </a
      ><a name="14980" class="Symbol"
      >|</a
      ><a name="14981"
      > </a
      ><a name="14982" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#520" class="InductiveConstructor"
      >yes</a
      ><a name="14985"
      > </a
      ><a name="14986" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="14990"
      > </a
      ><a name="14991" class="Symbol"
      >=</a
      ><a name="14992"
      > </a
      ><a name="14993" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="14997"
      >
  </a
      ><a name="15000" class="Symbol"
      >...</a
      ><a name="15003"
      > </a
      ><a name="15004" class="Symbol"
      >|</a
      ><a name="15005"
      > </a
      ><a name="15006" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#547" class="InductiveConstructor"
      >no</a
      ><a name="15008"
      >  </a
      ><a name="15010" href="StlcProp.html#15010" class="Bound"
      >x&#8802;y</a
      ><a name="15013"
      >  </a
      ><a name="15015" class="Symbol"
      >=</a
      ><a name="15016"
      > </a
      ><a name="15017" href="StlcProp.html#14835" class="Bound"
      >&#915;~&#915;&#8242;</a
      ><a name="15021"
      > </a
      ><a name="15022" class="Symbol"
      >(</a
      ><a name="15023" href="StlcProp.html#7699" class="InductiveConstructor"
      >free-&#955;</a
      ><a name="15029"
      > </a
      ><a name="15030" href="StlcProp.html#15010" class="Bound"
      >x&#8802;y</a
      ><a name="15033"
      > </a
      ><a name="15034" href="StlcProp.html#14959" class="Bound"
      >y&#8712;N</a
      ><a name="15037" class="Symbol"
      >)</a
      ><a name="15038"
      >
</a
      ><a name="15039" href="StlcProp.html#12458" class="Function"
      >contextLemma</a
      ><a name="15051"
      > </a
      ><a name="15052" href="StlcProp.html#15052" class="Bound"
      >&#915;~&#915;&#8242;</a
      ><a name="15056"
      > </a
      ><a name="15057" class="Symbol"
      >(</a
      ><a name="15058" href="Stlc.html#3287" class="InductiveConstructor"
      >&#8658;-E</a
      ><a name="15061"
      > </a
      ><a name="15062" href="StlcProp.html#15062" class="Bound"
      >&#8866;L</a
      ><a name="15064"
      > </a
      ><a name="15065" href="StlcProp.html#15065" class="Bound"
      >&#8866;M</a
      ><a name="15067" class="Symbol"
      >)</a
      ><a name="15068"
      > </a
      ><a name="15069" class="Symbol"
      >=</a
      ><a name="15070"
      > </a
      ><a name="15071" href="Stlc.html#3287" class="InductiveConstructor"
      >&#8658;-E</a
      ><a name="15074"
      > </a
      ><a name="15075" class="Symbol"
      >(</a
      ><a name="15076" href="StlcProp.html#12458" class="Function"
      >contextLemma</a
      ><a name="15088"
      > </a
      ><a name="15089" class="Symbol"
      >(</a
      ><a name="15090" href="StlcProp.html#15052" class="Bound"
      >&#915;~&#915;&#8242;</a
      ><a name="15094"
      > </a
      ><a name="15095" href="https://agda.github.io/agda-stdlib/Function.html#713" class="Function Operator"
      >&#8728;</a
      ><a name="15096"
      > </a
      ><a name="15097" href="StlcProp.html#7760" class="InductiveConstructor"
      >free-&#183;&#8321;</a
      ><a name="15104" class="Symbol"
      >)</a
      ><a name="15105"
      >  </a
      ><a name="15107" href="StlcProp.html#15062" class="Bound"
      >&#8866;L</a
      ><a name="15109" class="Symbol"
      >)</a
      ><a name="15110"
      > </a
      ><a name="15111" class="Symbol"
      >(</a
      ><a name="15112" href="StlcProp.html#12458" class="Function"
      >contextLemma</a
      ><a name="15124"
      > </a
      ><a name="15125" class="Symbol"
      >(</a
      ><a name="15126" href="StlcProp.html#15052" class="Bound"
      >&#915;~&#915;&#8242;</a
      ><a name="15130"
      > </a
      ><a name="15131" href="https://agda.github.io/agda-stdlib/Function.html#713" class="Function Operator"
      >&#8728;</a
      ><a name="15132"
      > </a
      ><a name="15133" href="StlcProp.html#7804" class="InductiveConstructor"
      >free-&#183;&#8322;</a
      ><a name="15140" class="Symbol"
      >)</a
      ><a name="15141"
      > </a
      ><a name="15142" href="StlcProp.html#15065" class="Bound"
      >&#8866;M</a
      ><a name="15144" class="Symbol"
      >)</a
      ><a name="15145"
      > 
</a
      ><a name="15147" href="StlcProp.html#12458" class="Function"
      >contextLemma</a
      ><a name="15159"
      > </a
      ><a name="15160" href="StlcProp.html#15160" class="Bound"
      >&#915;~&#915;&#8242;</a
      ><a name="15164"
      > </a
      ><a name="15165" href="Stlc.html#3365" class="InductiveConstructor"
      >&#120121;-I&#8321;</a
      ><a name="15169"
      > </a
      ><a name="15170" class="Symbol"
      >=</a
      ><a name="15171"
      > </a
      ><a name="15172" href="Stlc.html#3365" class="InductiveConstructor"
      >&#120121;-I&#8321;</a
      ><a name="15176"
      >
</a
      ><a name="15177" href="StlcProp.html#12458" class="Function"
      >contextLemma</a
      ><a name="15189"
      > </a
      ><a name="15190" href="StlcProp.html#15190" class="Bound"
      >&#915;~&#915;&#8242;</a
      ><a name="15194"
      > </a
      ><a name="15195" href="Stlc.html#3399" class="InductiveConstructor"
      >&#120121;-I&#8322;</a
      ><a name="15199"
      > </a
      ><a name="15200" class="Symbol"
      >=</a
      ><a name="15201"
      > </a
      ><a name="15202" href="Stlc.html#3399" class="InductiveConstructor"
      >&#120121;-I&#8322;</a
      ><a name="15206"
      >
</a
      ><a name="15207" href="StlcProp.html#12458" class="Function"
      >contextLemma</a
      ><a name="15219"
      > </a
      ><a name="15220" href="StlcProp.html#15220" class="Bound"
      >&#915;~&#915;&#8242;</a
      ><a name="15224"
      > </a
      ><a name="15225" class="Symbol"
      >(</a
      ><a name="15226" href="Stlc.html#3434" class="InductiveConstructor"
      >&#120121;-E</a
      ><a name="15229"
      > </a
      ><a name="15230" href="StlcProp.html#15230" class="Bound"
      >&#8866;L</a
      ><a name="15232"
      > </a
      ><a name="15233" href="StlcProp.html#15233" class="Bound"
      >&#8866;M</a
      ><a name="15235"
      > </a
      ><a name="15236" href="StlcProp.html#15236" class="Bound"
      >&#8866;N</a
      ><a name="15238" class="Symbol"
      >)</a
      ><a name="15239"
      >
  </a
      ><a name="15242" class="Symbol"
      >=</a
      ><a name="15243"
      > </a
      ><a name="15244" href="Stlc.html#3434" class="InductiveConstructor"
      >&#120121;-E</a
      ><a name="15247"
      > </a
      ><a name="15248" class="Symbol"
      >(</a
      ><a name="15249" href="StlcProp.html#12458" class="Function"
      >contextLemma</a
      ><a name="15261"
      > </a
      ><a name="15262" class="Symbol"
      >(</a
      ><a name="15263" href="StlcProp.html#15220" class="Bound"
      >&#915;~&#915;&#8242;</a
      ><a name="15267"
      > </a
      ><a name="15268" href="https://agda.github.io/agda-stdlib/Function.html#713" class="Function Operator"
      >&#8728;</a
      ><a name="15269"
      > </a
      ><a name="15270" href="StlcProp.html#7848" class="InductiveConstructor"
      >free-if&#8321;</a
      ><a name="15278" class="Symbol"
      >)</a
      ><a name="15279"
      > </a
      ><a name="15280" href="StlcProp.html#15230" class="Bound"
      >&#8866;L</a
      ><a name="15282" class="Symbol"
      >)</a
      ><a name="15283"
      > </a
      ><a name="15284" class="Symbol"
      >(</a
      ><a name="15285" href="StlcProp.html#12458" class="Function"
      >contextLemma</a
      ><a name="15297"
      > </a
      ><a name="15298" class="Symbol"
      >(</a
      ><a name="15299" href="StlcProp.html#15220" class="Bound"
      >&#915;~&#915;&#8242;</a
      ><a name="15303"
      > </a
      ><a name="15304" href="https://agda.github.io/agda-stdlib/Function.html#713" class="Function Operator"
      >&#8728;</a
      ><a name="15305"
      > </a
      ><a name="15306" href="StlcProp.html#7908" class="InductiveConstructor"
      >free-if&#8322;</a
      ><a name="15314" class="Symbol"
      >)</a
      ><a name="15315"
      > </a
      ><a name="15316" href="StlcProp.html#15233" class="Bound"
      >&#8866;M</a
      ><a name="15318" class="Symbol"
      >)</a
      ><a name="15319"
      > </a
      ><a name="15320" class="Symbol"
      >(</a
      ><a name="15321" href="StlcProp.html#12458" class="Function"
      >contextLemma</a
      ><a name="15333"
      > </a
      ><a name="15334" class="Symbol"
      >(</a
      ><a name="15335" href="StlcProp.html#15220" class="Bound"
      >&#915;~&#915;&#8242;</a
      ><a name="15339"
      > </a
      ><a name="15340" href="https://agda.github.io/agda-stdlib/Function.html#713" class="Function Operator"
      >&#8728;</a
      ><a name="15341"
      > </a
      ><a name="15342" href="StlcProp.html#7968" class="InductiveConstructor"
      >free-if&#8323;</a
      ><a name="15350" class="Symbol"
      >)</a
      ><a name="15351"
      > </a
      ><a name="15352" href="StlcProp.html#15236" class="Bound"
      >&#8866;N</a
      ><a name="15354" class="Symbol"
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

<a name="16053" href="StlcProp.html#16053" class="Function"
      >preservation-[:=]</a
      ><a name="16070"
      > </a
      ><a name="16071" class="Symbol"
      >:</a
      ><a name="16072"
      > </a
      ><a name="16073" class="Symbol"
      >&#8704;</a
      ><a name="16074"
      > </a
      ><a name="16075" class="Symbol"
      >{</a
      ><a name="16076" href="StlcProp.html#16076" class="Bound"
      >&#915;</a
      ><a name="16077"
      > </a
      ><a name="16078" href="StlcProp.html#16078" class="Bound"
      >x</a
      ><a name="16079"
      > </a
      ><a name="16080" href="StlcProp.html#16080" class="Bound"
      >A</a
      ><a name="16081"
      > </a
      ><a name="16082" href="StlcProp.html#16082" class="Bound"
      >N</a
      ><a name="16083"
      > </a
      ><a name="16084" href="StlcProp.html#16084" class="Bound"
      >B</a
      ><a name="16085"
      > </a
      ><a name="16086" href="StlcProp.html#16086" class="Bound"
      >V</a
      ><a name="16087" class="Symbol"
      >}</a
      ><a name="16088"
      >
                 </a
      ><a name="16106" class="Symbol"
      >&#8594;</a
      ><a name="16107"
      > </a
      ><a name="16108" class="Symbol"
      >(</a
      ><a name="16109" href="StlcProp.html#16076" class="Bound"
      >&#915;</a
      ><a name="16110"
      > </a
      ><a name="16111" href="Maps.html#10368" class="Function Operator"
      >,</a
      ><a name="16112"
      > </a
      ><a name="16113" href="StlcProp.html#16078" class="Bound"
      >x</a
      ><a name="16114"
      > </a
      ><a name="16115" href="Maps.html#10368" class="Function Operator"
      >&#8758;</a
      ><a name="16116"
      > </a
      ><a name="16117" href="StlcProp.html#16080" class="Bound"
      >A</a
      ><a name="16118" class="Symbol"
      >)</a
      ><a name="16119"
      > </a
      ><a name="16120" href="Stlc.html#3112" class="Datatype Operator"
      >&#8866;</a
      ><a name="16121"
      > </a
      ><a name="16122" href="StlcProp.html#16082" class="Bound"
      >N</a
      ><a name="16123"
      > </a
      ><a name="16124" href="Stlc.html#3112" class="Datatype Operator"
      >&#8758;</a
      ><a name="16125"
      > </a
      ><a name="16126" href="StlcProp.html#16084" class="Bound"
      >B</a
      ><a name="16127"
      >
                 </a
      ><a name="16145" class="Symbol"
      >&#8594;</a
      ><a name="16146"
      > </a
      ><a name="16147" href="Maps.html#10265" class="Function"
      >&#8709;</a
      ><a name="16148"
      > </a
      ><a name="16149" href="Stlc.html#3112" class="Datatype Operator"
      >&#8866;</a
      ><a name="16150"
      > </a
      ><a name="16151" href="StlcProp.html#16086" class="Bound"
      >V</a
      ><a name="16152"
      > </a
      ><a name="16153" href="Stlc.html#3112" class="Datatype Operator"
      >&#8758;</a
      ><a name="16154"
      > </a
      ><a name="16155" href="StlcProp.html#16080" class="Bound"
      >A</a
      ><a name="16156"
      >
                 </a
      ><a name="16174" class="Symbol"
      >&#8594;</a
      ><a name="16175"
      > </a
      ><a name="16176" href="StlcProp.html#16076" class="Bound"
      >&#915;</a
      ><a name="16177"
      > </a
      ><a name="16178" href="Stlc.html#3112" class="Datatype Operator"
      >&#8866;</a
      ><a name="16179"
      > </a
      ><a name="16180" class="Symbol"
      >(</a
      ><a name="16181" href="StlcProp.html#16082" class="Bound"
      >N</a
      ><a name="16182"
      > </a
      ><a name="16183" href="Stlc.html#1276" class="Function Operator"
      >[</a
      ><a name="16184"
      > </a
      ><a name="16185" href="StlcProp.html#16078" class="Bound"
      >x</a
      ><a name="16186"
      > </a
      ><a name="16187" href="Stlc.html#1276" class="Function Operator"
      >:=</a
      ><a name="16189"
      > </a
      ><a name="16190" href="StlcProp.html#16086" class="Bound"
      >V</a
      ><a name="16191"
      > </a
      ><a name="16192" href="Stlc.html#1276" class="Function Operator"
      >]</a
      ><a name="16193" class="Symbol"
      >)</a
      ><a name="16194"
      > </a
      ><a name="16195" href="Stlc.html#3112" class="Datatype Operator"
      >&#8758;</a
      ><a name="16196"
      > </a
      ><a name="16197" href="StlcProp.html#16084" class="Bound"
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

<a name="19351" href="StlcProp.html#19351" class="Function"
      >weaken-closed</a
      ><a name="19364"
      > </a
      ><a name="19365" class="Symbol"
      >:</a
      ><a name="19366"
      > </a
      ><a name="19367" class="Symbol"
      >&#8704;</a
      ><a name="19368"
      > </a
      ><a name="19369" class="Symbol"
      >{</a
      ><a name="19370" href="StlcProp.html#19370" class="Bound"
      >V</a
      ><a name="19371"
      > </a
      ><a name="19372" href="StlcProp.html#19372" class="Bound"
      >A</a
      ><a name="19373"
      > </a
      ><a name="19374" href="StlcProp.html#19374" class="Bound"
      >&#915;</a
      ><a name="19375" class="Symbol"
      >}</a
      ><a name="19376"
      > </a
      ><a name="19377" class="Symbol"
      >&#8594;</a
      ><a name="19378"
      > </a
      ><a name="19379" href="Maps.html#10265" class="Function"
      >&#8709;</a
      ><a name="19380"
      > </a
      ><a name="19381" href="Stlc.html#3112" class="Datatype Operator"
      >&#8866;</a
      ><a name="19382"
      > </a
      ><a name="19383" href="StlcProp.html#19370" class="Bound"
      >V</a
      ><a name="19384"
      > </a
      ><a name="19385" href="Stlc.html#3112" class="Datatype Operator"
      >&#8758;</a
      ><a name="19386"
      > </a
      ><a name="19387" href="StlcProp.html#19372" class="Bound"
      >A</a
      ><a name="19388"
      > </a
      ><a name="19389" class="Symbol"
      >&#8594;</a
      ><a name="19390"
      > </a
      ><a name="19391" href="StlcProp.html#19374" class="Bound"
      >&#915;</a
      ><a name="19392"
      > </a
      ><a name="19393" href="Stlc.html#3112" class="Datatype Operator"
      >&#8866;</a
      ><a name="19394"
      > </a
      ><a name="19395" href="StlcProp.html#19370" class="Bound"
      >V</a
      ><a name="19396"
      > </a
      ><a name="19397" href="Stlc.html#3112" class="Datatype Operator"
      >&#8758;</a
      ><a name="19398"
      > </a
      ><a name="19399" href="StlcProp.html#19372" class="Bound"
      >A</a
      ><a name="19400"
      >
</a
      ><a name="19401" href="StlcProp.html#19351" class="Function"
      >weaken-closed</a
      ><a name="19414"
      > </a
      ><a name="19415" class="Symbol"
      >{</a
      ><a name="19416" href="StlcProp.html#19416" class="Bound"
      >V</a
      ><a name="19417" class="Symbol"
      >}</a
      ><a name="19418"
      > </a
      ><a name="19419" class="Symbol"
      >{</a
      ><a name="19420" href="StlcProp.html#19420" class="Bound"
      >A</a
      ><a name="19421" class="Symbol"
      >}</a
      ><a name="19422"
      > </a
      ><a name="19423" class="Symbol"
      >{</a
      ><a name="19424" href="StlcProp.html#19424" class="Bound"
      >&#915;</a
      ><a name="19425" class="Symbol"
      >}</a
      ><a name="19426"
      > </a
      ><a name="19427" href="StlcProp.html#19427" class="Bound"
      >&#8866;V</a
      ><a name="19429"
      > </a
      ><a name="19430" class="Symbol"
      >=</a
      ><a name="19431"
      > </a
      ><a name="19432" href="StlcProp.html#12458" class="Function"
      >contextLemma</a
      ><a name="19444"
      > </a
      ><a name="19445" href="StlcProp.html#19463" class="Function"
      >&#915;~&#915;&#8242;</a
      ><a name="19449"
      > </a
      ><a name="19450" href="StlcProp.html#19427" class="Bound"
      >&#8866;V</a
      ><a name="19452"
      >
  </a
      ><a name="19455" class="Keyword"
      >where</a
      ><a name="19460"
      >
  </a
      ><a name="19463" href="StlcProp.html#19463" class="Function"
      >&#915;~&#915;&#8242;</a
      ><a name="19467"
      > </a
      ><a name="19468" class="Symbol"
      >:</a
      ><a name="19469"
      > </a
      ><a name="19470" class="Symbol"
      >&#8704;</a
      ><a name="19471"
      > </a
      ><a name="19472" class="Symbol"
      >{</a
      ><a name="19473" href="StlcProp.html#19473" class="Bound"
      >x</a
      ><a name="19474" class="Symbol"
      >}</a
      ><a name="19475"
      > </a
      ><a name="19476" class="Symbol"
      >&#8594;</a
      ><a name="19477"
      > </a
      ><a name="19478" href="StlcProp.html#19473" class="Bound"
      >x</a
      ><a name="19479"
      > </a
      ><a name="19480" href="StlcProp.html#7641" class="Datatype Operator"
      >&#8712;</a
      ><a name="19481"
      > </a
      ><a name="19482" href="StlcProp.html#19416" class="Bound"
      >V</a
      ><a name="19483"
      > </a
      ><a name="19484" class="Symbol"
      >&#8594;</a
      ><a name="19485"
      > </a
      ><a name="19486" href="Maps.html#10265" class="Function"
      >&#8709;</a
      ><a name="19487"
      > </a
      ><a name="19488" href="StlcProp.html#19473" class="Bound"
      >x</a
      ><a name="19489"
      > </a
      ><a name="19490" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="19491"
      > </a
      ><a name="19492" href="StlcProp.html#19424" class="Bound"
      >&#915;</a
      ><a name="19493"
      > </a
      ><a name="19494" href="StlcProp.html#19473" class="Bound"
      >x</a
      ><a name="19495"
      >
  </a
      ><a name="19498" href="StlcProp.html#19463" class="Function"
      >&#915;~&#915;&#8242;</a
      ><a name="19502"
      > </a
      ><a name="19503" class="Symbol"
      >{</a
      ><a name="19504" href="StlcProp.html#19504" class="Bound"
      >x</a
      ><a name="19505" class="Symbol"
      >}</a
      ><a name="19506"
      > </a
      ><a name="19507" href="StlcProp.html#19507" class="Bound"
      >x&#8712;V</a
      ><a name="19510"
      > </a
      ><a name="19511" class="Symbol"
      >=</a
      ><a name="19512"
      > </a
      ><a name="19513" href="https://agda.github.io/agda-stdlib/Data.Empty.html#348" class="Function"
      >&#8869;-elim</a
      ><a name="19519"
      > </a
      ><a name="19520" class="Symbol"
      >(</a
      ><a name="19521" href="StlcProp.html#19544" class="Function"
      >x&#8713;V</a
      ><a name="19524"
      > </a
      ><a name="19525" href="StlcProp.html#19507" class="Bound"
      >x&#8712;V</a
      ><a name="19528" class="Symbol"
      >)</a
      ><a name="19529"
      >
    </a
      ><a name="19534" class="Keyword"
      >where</a
      ><a name="19539"
      >
    </a
      ><a name="19544" href="StlcProp.html#19544" class="Function"
      >x&#8713;V</a
      ><a name="19547"
      > </a
      ><a name="19548" class="Symbol"
      >:</a
      ><a name="19549"
      > </a
      ><a name="19550" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#414" class="Function Operator"
      >&#172;</a
      ><a name="19551"
      > </a
      ><a name="19552" class="Symbol"
      >(</a
      ><a name="19553" href="StlcProp.html#19504" class="Bound"
      >x</a
      ><a name="19554"
      > </a
      ><a name="19555" href="StlcProp.html#7641" class="Datatype Operator"
      >&#8712;</a
      ><a name="19556"
      > </a
      ><a name="19557" href="StlcProp.html#19416" class="Bound"
      >V</a
      ><a name="19558" class="Symbol"
      >)</a
      ><a name="19559"
      >
    </a
      ><a name="19564" href="StlcProp.html#19544" class="Function"
      >x&#8713;V</a
      ><a name="19567"
      > </a
      ><a name="19568" class="Symbol"
      >=</a
      ><a name="19569"
      > </a
      ><a name="19570" href="StlcProp.html#11759" class="Postulate"
      >&#8709;&#8866;-closed</a
      ><a name="19579"
      > </a
      ><a name="19580" href="StlcProp.html#19427" class="Bound"
      >&#8866;V</a
      ><a name="19582"
      > </a
      ><a name="19583" class="Symbol"
      >{</a
      ><a name="19584" href="StlcProp.html#19504" class="Bound"
      >x</a
      ><a name="19585" class="Symbol"
      >}</a
      ><a name="19586"
      >

</a
      ><a name="19588" href="StlcProp.html#19588" class="Function"
      >just-injective</a
      ><a name="19602"
      > </a
      ><a name="19603" class="Symbol"
      >:</a
      ><a name="19604"
      > </a
      ><a name="19605" class="Symbol"
      >&#8704;</a
      ><a name="19606"
      > </a
      ><a name="19607" class="Symbol"
      >{</a
      ><a name="19608" href="StlcProp.html#19608" class="Bound"
      >X</a
      ><a name="19609"
      > </a
      ><a name="19610" class="Symbol"
      >:</a
      ><a name="19611"
      > </a
      ><a name="19612" class="PrimitiveType"
      >Set</a
      ><a name="19615" class="Symbol"
      >}</a
      ><a name="19616"
      > </a
      ><a name="19617" class="Symbol"
      >{</a
      ><a name="19618" href="StlcProp.html#19618" class="Bound"
      >x</a
      ><a name="19619"
      > </a
      ><a name="19620" href="StlcProp.html#19620" class="Bound"
      >y</a
      ><a name="19621"
      > </a
      ><a name="19622" class="Symbol"
      >:</a
      ><a name="19623"
      > </a
      ><a name="19624" href="StlcProp.html#19608" class="Bound"
      >X</a
      ><a name="19625" class="Symbol"
      >}</a
      ><a name="19626"
      > </a
      ><a name="19627" class="Symbol"
      >&#8594;</a
      ><a name="19628"
      > </a
      ><a name="19629" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >_&#8801;_</a
      ><a name="19632"
      > </a
      ><a name="19633" class="Symbol"
      >{</a
      ><a name="19634" class="Argument"
      >A</a
      ><a name="19635"
      > </a
      ><a name="19636" class="Symbol"
      >=</a
      ><a name="19637"
      > </a
      ><a name="19638" href="https://agda.github.io/agda-stdlib/Data.Maybe.Base.html#335" class="Datatype"
      >Maybe</a
      ><a name="19643"
      > </a
      ><a name="19644" href="StlcProp.html#19608" class="Bound"
      >X</a
      ><a name="19645" class="Symbol"
      >}</a
      ><a name="19646"
      > </a
      ><a name="19647" class="Symbol"
      >(</a
      ><a name="19648" href="https://agda.github.io/agda-stdlib/Data.Maybe.Base.html#373" class="InductiveConstructor"
      >just</a
      ><a name="19652"
      > </a
      ><a name="19653" href="StlcProp.html#19618" class="Bound"
      >x</a
      ><a name="19654" class="Symbol"
      >)</a
      ><a name="19655"
      > </a
      ><a name="19656" class="Symbol"
      >(</a
      ><a name="19657" href="https://agda.github.io/agda-stdlib/Data.Maybe.Base.html#373" class="InductiveConstructor"
      >just</a
      ><a name="19661"
      > </a
      ><a name="19662" href="StlcProp.html#19620" class="Bound"
      >y</a
      ><a name="19663" class="Symbol"
      >)</a
      ><a name="19664"
      > </a
      ><a name="19665" class="Symbol"
      >&#8594;</a
      ><a name="19666"
      > </a
      ><a name="19667" href="StlcProp.html#19618" class="Bound"
      >x</a
      ><a name="19668"
      > </a
      ><a name="19669" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="19670"
      > </a
      ><a name="19671" href="StlcProp.html#19620" class="Bound"
      >y</a
      ><a name="19672"
      >
</a
      ><a name="19673" href="StlcProp.html#19588" class="Function"
      >just-injective</a
      ><a name="19687"
      > </a
      ><a name="19688" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="19692"
      > </a
      ><a name="19693" class="Symbol"
      >=</a
      ><a name="19694"
      > </a
      ><a name="19695" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      >

</pre>

<pre class="Agda">

<a name="19725" href="StlcProp.html#16053" class="Function"
      >preservation-[:=]</a
      ><a name="19742"
      > </a
      ><a name="19743" class="Symbol"
      >{</a
      ><a name="19744" href="StlcProp.html#19744" class="Bound"
      >&#915;</a
      ><a name="19745" class="Symbol"
      >}</a
      ><a name="19746"
      > </a
      ><a name="19747" class="Symbol"
      >{</a
      ><a name="19748" href="StlcProp.html#19748" class="Bound"
      >x</a
      ><a name="19749" class="Symbol"
      >}</a
      ><a name="19750"
      > </a
      ><a name="19751" class="Symbol"
      >{</a
      ><a name="19752" href="StlcProp.html#19752" class="Bound"
      >A</a
      ><a name="19753" class="Symbol"
      >}</a
      ><a name="19754"
      > </a
      ><a name="19755" class="Symbol"
      >(</a
      ><a name="19756" href="Stlc.html#3156" class="InductiveConstructor"
      >Ax</a
      ><a name="19758"
      > </a
      ><a name="19759" class="Symbol"
      >{</a
      ><a name="19760" href="StlcProp.html#19760" class="Bound"
      >&#915;,x&#8758;A</a
      ><a name="19765" class="Symbol"
      >}</a
      ><a name="19766"
      > </a
      ><a name="19767" class="Symbol"
      >{</a
      ><a name="19768" href="StlcProp.html#19768" class="Bound"
      >x&#8242;</a
      ><a name="19770" class="Symbol"
      >}</a
      ><a name="19771"
      > </a
      ><a name="19772" class="Symbol"
      >{</a
      ><a name="19773" href="StlcProp.html#19773" class="Bound"
      >B</a
      ><a name="19774" class="Symbol"
      >}</a
      ><a name="19775"
      > </a
      ><a name="19776" href="StlcProp.html#19776" class="Bound"
      >[&#915;,x&#8758;A]x&#8242;&#8801;B</a
      ><a name="19787" class="Symbol"
      >)</a
      ><a name="19788"
      > </a
      ><a name="19789" href="StlcProp.html#19789" class="Bound"
      >&#8866;V</a
      ><a name="19791"
      > </a
      ><a name="19792" class="Keyword"
      >with</a
      ><a name="19796"
      > </a
      ><a name="19797" href="StlcProp.html#19748" class="Bound"
      >x</a
      ><a name="19798"
      > </a
      ><a name="19799" href="Maps.html#2509" class="Function Operator"
      >&#8799;</a
      ><a name="19800"
      > </a
      ><a name="19801" href="StlcProp.html#19768" class="Bound"
      >x&#8242;</a
      ><a name="19803"
      >
</a
      ><a name="19804" class="Symbol"
      >...|</a
      ><a name="19808"
      > </a
      ><a name="19809" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#520" class="InductiveConstructor"
      >yes</a
      ><a name="19812"
      > </a
      ><a name="19813" href="StlcProp.html#19813" class="Bound"
      >x&#8801;x&#8242;</a
      ><a name="19817"
      > </a
      ><a name="19818" class="Keyword"
      >rewrite</a
      ><a name="19825"
      > </a
      ><a name="19826" href="StlcProp.html#19588" class="Function"
      >just-injective</a
      ><a name="19840"
      > </a
      ><a name="19841" href="StlcProp.html#19776" class="Bound"
      >[&#915;,x&#8758;A]x&#8242;&#8801;B</a
      ><a name="19852"
      >  </a
      ><a name="19854" class="Symbol"
      >=</a
      ><a name="19855"
      >  </a
      ><a name="19857" href="StlcProp.html#19351" class="Function"
      >weaken-closed</a
      ><a name="19870"
      > </a
      ><a name="19871" href="StlcProp.html#19789" class="Bound"
      >&#8866;V</a
      ><a name="19873"
      >
</a
      ><a name="19874" class="Symbol"
      >...|</a
      ><a name="19878"
      > </a
      ><a name="19879" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#547" class="InductiveConstructor"
      >no</a
      ><a name="19881"
      >  </a
      ><a name="19883" href="StlcProp.html#19883" class="Bound"
      >x&#8802;x&#8242;</a
      ><a name="19887"
      >  </a
      ><a name="19889" class="Symbol"
      >=</a
      ><a name="19890"
      >  </a
      ><a name="19892" href="Stlc.html#3156" class="InductiveConstructor"
      >Ax</a
      ><a name="19894"
      > </a
      ><a name="19895" href="StlcProp.html#19776" class="Bound"
      >[&#915;,x&#8758;A]x&#8242;&#8801;B</a
      ><a name="19906"
      >
</a
      ><a name="19907" href="StlcProp.html#16053" class="Function"
      >preservation-[:=]</a
      ><a name="19924"
      > </a
      ><a name="19925" class="Symbol"
      >{</a
      ><a name="19926" href="StlcProp.html#19926" class="Bound"
      >&#915;</a
      ><a name="19927" class="Symbol"
      >}</a
      ><a name="19928"
      > </a
      ><a name="19929" class="Symbol"
      >{</a
      ><a name="19930" href="StlcProp.html#19930" class="Bound"
      >x</a
      ><a name="19931" class="Symbol"
      >}</a
      ><a name="19932"
      > </a
      ><a name="19933" class="Symbol"
      >{</a
      ><a name="19934" href="StlcProp.html#19934" class="Bound"
      >A</a
      ><a name="19935" class="Symbol"
      >}</a
      ><a name="19936"
      > </a
      ><a name="19937" class="Symbol"
      >{</a
      ><a name="19938" href="Stlc.html#743" class="InductiveConstructor Operator"
      >&#955;[</a
      ><a name="19940"
      > </a
      ><a name="19941" href="StlcProp.html#19941" class="Bound"
      >x&#8242;</a
      ><a name="19943"
      > </a
      ><a name="19944" href="Stlc.html#743" class="InductiveConstructor Operator"
      >&#8758;</a
      ><a name="19945"
      > </a
      ><a name="19946" href="StlcProp.html#19946" class="Bound"
      >A&#8242;</a
      ><a name="19948"
      > </a
      ><a name="19949" href="Stlc.html#743" class="InductiveConstructor Operator"
      >]</a
      ><a name="19950"
      > </a
      ><a name="19951" href="StlcProp.html#19951" class="Bound"
      >N&#8242;</a
      ><a name="19953" class="Symbol"
      >}</a
      ><a name="19954"
      > </a
      ><a name="19955" class="Symbol"
      >{</a
      ><a name="19956" class="DottedPattern Symbol"
      >.</a
      ><a name="19957" href="StlcProp.html#19946" class="DottedPattern Bound"
      >A&#8242;</a
      ><a name="19959"
      > </a
      ><a name="19960" href="Stlc.html#620" class="InductiveConstructor Operator"
      >&#8658;</a
      ><a name="19961"
      > </a
      ><a name="19962" href="StlcProp.html#19962" class="Bound"
      >B&#8242;</a
      ><a name="19964" class="Symbol"
      >}</a
      ><a name="19965"
      > </a
      ><a name="19966" class="Symbol"
      >{</a
      ><a name="19967" href="StlcProp.html#19967" class="Bound"
      >V</a
      ><a name="19968" class="Symbol"
      >}</a
      ><a name="19969"
      > </a
      ><a name="19970" class="Symbol"
      >(</a
      ><a name="19971" href="Stlc.html#3210" class="InductiveConstructor"
      >&#8658;-I</a
      ><a name="19974"
      > </a
      ><a name="19975" href="StlcProp.html#19975" class="Bound"
      >&#8866;N&#8242;</a
      ><a name="19978" class="Symbol"
      >)</a
      ><a name="19979"
      > </a
      ><a name="19980" href="StlcProp.html#19980" class="Bound"
      >&#8866;V</a
      ><a name="19982"
      > </a
      ><a name="19983" class="Keyword"
      >with</a
      ><a name="19987"
      > </a
      ><a name="19988" href="StlcProp.html#19930" class="Bound"
      >x</a
      ><a name="19989"
      > </a
      ><a name="19990" href="Maps.html#2509" class="Function Operator"
      >&#8799;</a
      ><a name="19991"
      > </a
      ><a name="19992" href="StlcProp.html#19941" class="Bound"
      >x&#8242;</a
      ><a name="19994"
      >
</a
      ><a name="19995" class="Symbol"
      >...|</a
      ><a name="19999"
      > </a
      ><a name="20000" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#520" class="InductiveConstructor"
      >yes</a
      ><a name="20003"
      > </a
      ><a name="20004" href="StlcProp.html#20004" class="Bound"
      >x&#8801;x&#8242;</a
      ><a name="20008"
      > </a
      ><a name="20009" class="Keyword"
      >rewrite</a
      ><a name="20016"
      > </a
      ><a name="20017" href="StlcProp.html#20004" class="Bound"
      >x&#8801;x&#8242;</a
      ><a name="20021"
      > </a
      ><a name="20022" class="Symbol"
      >=</a
      ><a name="20023"
      > </a
      ><a name="20024" href="StlcProp.html#12458" class="Function"
      >contextLemma</a
      ><a name="20036"
      > </a
      ><a name="20037" href="StlcProp.html#20062" class="Function"
      >&#915;&#8242;~&#915;</a
      ><a name="20041"
      > </a
      ><a name="20042" class="Symbol"
      >(</a
      ><a name="20043" href="Stlc.html#3210" class="InductiveConstructor"
      >&#8658;-I</a
      ><a name="20046"
      > </a
      ><a name="20047" href="StlcProp.html#19975" class="Bound"
      >&#8866;N&#8242;</a
      ><a name="20050" class="Symbol"
      >)</a
      ><a name="20051"
      >
  </a
      ><a name="20054" class="Keyword"
      >where</a
      ><a name="20059"
      >
  </a
      ><a name="20062" href="StlcProp.html#20062" class="Function"
      >&#915;&#8242;~&#915;</a
      ><a name="20066"
      > </a
      ><a name="20067" class="Symbol"
      >:</a
      ><a name="20068"
      > </a
      ><a name="20069" class="Symbol"
      >&#8704;</a
      ><a name="20070"
      > </a
      ><a name="20071" class="Symbol"
      >{</a
      ><a name="20072" href="StlcProp.html#20072" class="Bound"
      >y</a
      ><a name="20073" class="Symbol"
      >}</a
      ><a name="20074"
      > </a
      ><a name="20075" class="Symbol"
      >&#8594;</a
      ><a name="20076"
      > </a
      ><a name="20077" href="StlcProp.html#20072" class="Bound"
      >y</a
      ><a name="20078"
      > </a
      ><a name="20079" href="StlcProp.html#7641" class="Datatype Operator"
      >&#8712;</a
      ><a name="20080"
      > </a
      ><a name="20081" class="Symbol"
      >(</a
      ><a name="20082" href="Stlc.html#743" class="InductiveConstructor Operator"
      >&#955;[</a
      ><a name="20084"
      > </a
      ><a name="20085" href="StlcProp.html#19941" class="Bound"
      >x&#8242;</a
      ><a name="20087"
      > </a
      ><a name="20088" href="Stlc.html#743" class="InductiveConstructor Operator"
      >&#8758;</a
      ><a name="20089"
      > </a
      ><a name="20090" href="StlcProp.html#19946" class="Bound"
      >A&#8242;</a
      ><a name="20092"
      > </a
      ><a name="20093" href="Stlc.html#743" class="InductiveConstructor Operator"
      >]</a
      ><a name="20094"
      > </a
      ><a name="20095" href="StlcProp.html#19951" class="Bound"
      >N&#8242;</a
      ><a name="20097" class="Symbol"
      >)</a
      ><a name="20098"
      > </a
      ><a name="20099" class="Symbol"
      >&#8594;</a
      ><a name="20100"
      > </a
      ><a name="20101" class="Symbol"
      >(</a
      ><a name="20102" href="StlcProp.html#19926" class="Bound"
      >&#915;</a
      ><a name="20103"
      > </a
      ><a name="20104" href="Maps.html#10368" class="Function Operator"
      >,</a
      ><a name="20105"
      > </a
      ><a name="20106" href="StlcProp.html#19941" class="Bound"
      >x&#8242;</a
      ><a name="20108"
      > </a
      ><a name="20109" href="Maps.html#10368" class="Function Operator"
      >&#8758;</a
      ><a name="20110"
      > </a
      ><a name="20111" href="StlcProp.html#19934" class="Bound"
      >A</a
      ><a name="20112" class="Symbol"
      >)</a
      ><a name="20113"
      > </a
      ><a name="20114" href="StlcProp.html#20072" class="Bound"
      >y</a
      ><a name="20115"
      > </a
      ><a name="20116" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="20117"
      > </a
      ><a name="20118" href="StlcProp.html#19926" class="Bound"
      >&#915;</a
      ><a name="20119"
      > </a
      ><a name="20120" href="StlcProp.html#20072" class="Bound"
      >y</a
      ><a name="20121"
      >
  </a
      ><a name="20124" href="StlcProp.html#20062" class="Function"
      >&#915;&#8242;~&#915;</a
      ><a name="20128"
      > </a
      ><a name="20129" class="Symbol"
      >{</a
      ><a name="20130" href="StlcProp.html#20130" class="Bound"
      >y</a
      ><a name="20131" class="Symbol"
      >}</a
      ><a name="20132"
      > </a
      ><a name="20133" class="Symbol"
      >(</a
      ><a name="20134" href="StlcProp.html#7699" class="InductiveConstructor"
      >free-&#955;</a
      ><a name="20140"
      > </a
      ><a name="20141" href="StlcProp.html#20141" class="Bound"
      >x&#8242;&#8802;y</a
      ><a name="20145"
      > </a
      ><a name="20146" href="StlcProp.html#20146" class="Bound"
      >y&#8712;N&#8242;</a
      ><a name="20150" class="Symbol"
      >)</a
      ><a name="20151"
      > </a
      ><a name="20152" class="Keyword"
      >with</a
      ><a name="20156"
      > </a
      ><a name="20157" href="StlcProp.html#19941" class="Bound"
      >x&#8242;</a
      ><a name="20159"
      > </a
      ><a name="20160" href="Maps.html#2509" class="Function Operator"
      >&#8799;</a
      ><a name="20161"
      > </a
      ><a name="20162" href="StlcProp.html#20130" class="Bound"
      >y</a
      ><a name="20163"
      >
  </a
      ><a name="20166" class="Symbol"
      >...|</a
      ><a name="20170"
      > </a
      ><a name="20171" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#520" class="InductiveConstructor"
      >yes</a
      ><a name="20174"
      > </a
      ><a name="20175" href="StlcProp.html#20175" class="Bound"
      >x&#8242;&#8801;y</a
      ><a name="20179"
      >  </a
      ><a name="20181" class="Symbol"
      >=</a
      ><a name="20182"
      > </a
      ><a name="20183" href="https://agda.github.io/agda-stdlib/Data.Empty.html#348" class="Function"
      >&#8869;-elim</a
      ><a name="20189"
      > </a
      ><a name="20190" class="Symbol"
      >(</a
      ><a name="20191" href="StlcProp.html#20141" class="Bound"
      >x&#8242;&#8802;y</a
      ><a name="20195"
      > </a
      ><a name="20196" href="StlcProp.html#20175" class="Bound"
      >x&#8242;&#8801;y</a
      ><a name="20200" class="Symbol"
      >)</a
      ><a name="20201"
      >
  </a
      ><a name="20204" class="Symbol"
      >...|</a
      ><a name="20208"
      > </a
      ><a name="20209" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#547" class="InductiveConstructor"
      >no</a
      ><a name="20211"
      >  </a
      ><a name="20213" class="Symbol"
      >_</a
      ><a name="20214"
      >     </a
      ><a name="20219" class="Symbol"
      >=</a
      ><a name="20220"
      > </a
      ><a name="20221" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="20225"
      >
</a
      ><a name="20226" class="Symbol"
      >...|</a
      ><a name="20230"
      > </a
      ><a name="20231" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#547" class="InductiveConstructor"
      >no</a
      ><a name="20233"
      >  </a
      ><a name="20235" href="StlcProp.html#20235" class="Bound"
      >x&#8802;x&#8242;</a
      ><a name="20239"
      > </a
      ><a name="20240" class="Symbol"
      >=</a
      ><a name="20241"
      > </a
      ><a name="20242" href="Stlc.html#3210" class="InductiveConstructor"
      >&#8658;-I</a
      ><a name="20245"
      > </a
      ><a name="20246" href="StlcProp.html#20357" class="Function"
      >&#8866;N&#8242;V</a
      ><a name="20250"
      >
  </a
      ><a name="20253" class="Keyword"
      >where</a
      ><a name="20258"
      >
  </a
      ><a name="20261" href="StlcProp.html#20261" class="Function"
      >x&#8242;x&#8866;N&#8242;</a
      ><a name="20267"
      > </a
      ><a name="20268" class="Symbol"
      >:</a
      ><a name="20269"
      > </a
      ><a name="20270" href="StlcProp.html#19926" class="Bound"
      >&#915;</a
      ><a name="20271"
      > </a
      ><a name="20272" href="Maps.html#10368" class="Function Operator"
      >,</a
      ><a name="20273"
      > </a
      ><a name="20274" href="StlcProp.html#19941" class="Bound"
      >x&#8242;</a
      ><a name="20276"
      > </a
      ><a name="20277" href="Maps.html#10368" class="Function Operator"
      >&#8758;</a
      ><a name="20278"
      > </a
      ><a name="20279" href="StlcProp.html#19946" class="Bound"
      >A&#8242;</a
      ><a name="20281"
      > </a
      ><a name="20282" href="Maps.html#10368" class="Function Operator"
      >,</a
      ><a name="20283"
      > </a
      ><a name="20284" href="StlcProp.html#19930" class="Bound"
      >x</a
      ><a name="20285"
      > </a
      ><a name="20286" href="Maps.html#10368" class="Function Operator"
      >&#8758;</a
      ><a name="20287"
      > </a
      ><a name="20288" href="StlcProp.html#19934" class="Bound"
      >A</a
      ><a name="20289"
      > </a
      ><a name="20290" href="Stlc.html#3112" class="Datatype Operator"
      >&#8866;</a
      ><a name="20291"
      > </a
      ><a name="20292" href="StlcProp.html#19951" class="Bound"
      >N&#8242;</a
      ><a name="20294"
      > </a
      ><a name="20295" href="Stlc.html#3112" class="Datatype Operator"
      >&#8758;</a
      ><a name="20296"
      > </a
      ><a name="20297" href="StlcProp.html#19962" class="Bound"
      >B&#8242;</a
      ><a name="20299"
      >
  </a
      ><a name="20302" href="StlcProp.html#20261" class="Function"
      >x&#8242;x&#8866;N&#8242;</a
      ><a name="20308"
      > </a
      ><a name="20309" class="Keyword"
      >rewrite</a
      ><a name="20316"
      > </a
      ><a name="20317" href="Maps.html#11491" class="Function"
      >update-permute</a
      ><a name="20331"
      > </a
      ><a name="20332" href="StlcProp.html#19926" class="Bound"
      >&#915;</a
      ><a name="20333"
      > </a
      ><a name="20334" href="StlcProp.html#19930" class="Bound"
      >x</a
      ><a name="20335"
      > </a
      ><a name="20336" href="StlcProp.html#19934" class="Bound"
      >A</a
      ><a name="20337"
      > </a
      ><a name="20338" href="StlcProp.html#19941" class="Bound"
      >x&#8242;</a
      ><a name="20340"
      > </a
      ><a name="20341" href="StlcProp.html#19946" class="Bound"
      >A&#8242;</a
      ><a name="20343"
      > </a
      ><a name="20344" href="StlcProp.html#20235" class="Bound"
      >x&#8802;x&#8242;</a
      ><a name="20348"
      > </a
      ><a name="20349" class="Symbol"
      >=</a
      ><a name="20350"
      > </a
      ><a name="20351" href="StlcProp.html#19975" class="Bound"
      >&#8866;N&#8242;</a
      ><a name="20354"
      >
  </a
      ><a name="20357" href="StlcProp.html#20357" class="Function"
      >&#8866;N&#8242;V</a
      ><a name="20361"
      > </a
      ><a name="20362" class="Symbol"
      >:</a
      ><a name="20363"
      > </a
      ><a name="20364" class="Symbol"
      >(</a
      ><a name="20365" href="StlcProp.html#19926" class="Bound"
      >&#915;</a
      ><a name="20366"
      > </a
      ><a name="20367" href="Maps.html#10368" class="Function Operator"
      >,</a
      ><a name="20368"
      > </a
      ><a name="20369" href="StlcProp.html#19941" class="Bound"
      >x&#8242;</a
      ><a name="20371"
      > </a
      ><a name="20372" href="Maps.html#10368" class="Function Operator"
      >&#8758;</a
      ><a name="20373"
      > </a
      ><a name="20374" href="StlcProp.html#19946" class="Bound"
      >A&#8242;</a
      ><a name="20376" class="Symbol"
      >)</a
      ><a name="20377"
      > </a
      ><a name="20378" href="Stlc.html#3112" class="Datatype Operator"
      >&#8866;</a
      ><a name="20379"
      > </a
      ><a name="20380" href="StlcProp.html#19951" class="Bound"
      >N&#8242;</a
      ><a name="20382"
      > </a
      ><a name="20383" href="Stlc.html#1276" class="Function Operator"
      >[</a
      ><a name="20384"
      > </a
      ><a name="20385" href="StlcProp.html#19930" class="Bound"
      >x</a
      ><a name="20386"
      > </a
      ><a name="20387" href="Stlc.html#1276" class="Function Operator"
      >:=</a
      ><a name="20389"
      > </a
      ><a name="20390" href="StlcProp.html#19967" class="Bound"
      >V</a
      ><a name="20391"
      > </a
      ><a name="20392" href="Stlc.html#1276" class="Function Operator"
      >]</a
      ><a name="20393"
      > </a
      ><a name="20394" href="Stlc.html#3112" class="Datatype Operator"
      >&#8758;</a
      ><a name="20395"
      > </a
      ><a name="20396" href="StlcProp.html#19962" class="Bound"
      >B&#8242;</a
      ><a name="20398"
      >
  </a
      ><a name="20401" href="StlcProp.html#20357" class="Function"
      >&#8866;N&#8242;V</a
      ><a name="20405"
      > </a
      ><a name="20406" class="Symbol"
      >=</a
      ><a name="20407"
      > </a
      ><a name="20408" href="StlcProp.html#16053" class="Function"
      >preservation-[:=]</a
      ><a name="20425"
      > </a
      ><a name="20426" href="StlcProp.html#20261" class="Function"
      >x&#8242;x&#8866;N&#8242;</a
      ><a name="20432"
      > </a
      ><a name="20433" href="StlcProp.html#19980" class="Bound"
      >&#8866;V</a
      ><a name="20435"
      >
</a
      ><a name="20436" href="StlcProp.html#16053" class="Function"
      >preservation-[:=]</a
      ><a name="20453"
      > </a
      ><a name="20454" class="Symbol"
      >(</a
      ><a name="20455" href="Stlc.html#3287" class="InductiveConstructor"
      >&#8658;-E</a
      ><a name="20458"
      > </a
      ><a name="20459" href="StlcProp.html#20459" class="Bound"
      >&#8866;L</a
      ><a name="20461"
      > </a
      ><a name="20462" href="StlcProp.html#20462" class="Bound"
      >&#8866;M</a
      ><a name="20464" class="Symbol"
      >)</a
      ><a name="20465"
      > </a
      ><a name="20466" href="StlcProp.html#20466" class="Bound"
      >&#8866;V</a
      ><a name="20468"
      > </a
      ><a name="20469" class="Symbol"
      >=</a
      ><a name="20470"
      > </a
      ><a name="20471" href="Stlc.html#3287" class="InductiveConstructor"
      >&#8658;-E</a
      ><a name="20474"
      > </a
      ><a name="20475" class="Symbol"
      >(</a
      ><a name="20476" href="StlcProp.html#16053" class="Function"
      >preservation-[:=]</a
      ><a name="20493"
      > </a
      ><a name="20494" href="StlcProp.html#20459" class="Bound"
      >&#8866;L</a
      ><a name="20496"
      > </a
      ><a name="20497" href="StlcProp.html#20466" class="Bound"
      >&#8866;V</a
      ><a name="20499" class="Symbol"
      >)</a
      ><a name="20500"
      > </a
      ><a name="20501" class="Symbol"
      >(</a
      ><a name="20502" href="StlcProp.html#16053" class="Function"
      >preservation-[:=]</a
      ><a name="20519"
      > </a
      ><a name="20520" href="StlcProp.html#20462" class="Bound"
      >&#8866;M</a
      ><a name="20522"
      > </a
      ><a name="20523" href="StlcProp.html#20466" class="Bound"
      >&#8866;V</a
      ><a name="20525" class="Symbol"
      >)</a
      ><a name="20526"
      >
</a
      ><a name="20527" href="StlcProp.html#16053" class="Function"
      >preservation-[:=]</a
      ><a name="20544"
      > </a
      ><a name="20545" href="Stlc.html#3365" class="InductiveConstructor"
      >&#120121;-I&#8321;</a
      ><a name="20549"
      > </a
      ><a name="20550" href="StlcProp.html#20550" class="Bound"
      >&#8866;V</a
      ><a name="20552"
      > </a
      ><a name="20553" class="Symbol"
      >=</a
      ><a name="20554"
      > </a
      ><a name="20555" href="Stlc.html#3365" class="InductiveConstructor"
      >&#120121;-I&#8321;</a
      ><a name="20559"
      >
</a
      ><a name="20560" href="StlcProp.html#16053" class="Function"
      >preservation-[:=]</a
      ><a name="20577"
      > </a
      ><a name="20578" href="Stlc.html#3399" class="InductiveConstructor"
      >&#120121;-I&#8322;</a
      ><a name="20582"
      > </a
      ><a name="20583" href="StlcProp.html#20583" class="Bound"
      >&#8866;V</a
      ><a name="20585"
      > </a
      ><a name="20586" class="Symbol"
      >=</a
      ><a name="20587"
      > </a
      ><a name="20588" href="Stlc.html#3399" class="InductiveConstructor"
      >&#120121;-I&#8322;</a
      ><a name="20592"
      >
</a
      ><a name="20593" href="StlcProp.html#16053" class="Function"
      >preservation-[:=]</a
      ><a name="20610"
      > </a
      ><a name="20611" class="Symbol"
      >(</a
      ><a name="20612" href="Stlc.html#3434" class="InductiveConstructor"
      >&#120121;-E</a
      ><a name="20615"
      > </a
      ><a name="20616" href="StlcProp.html#20616" class="Bound"
      >&#8866;L</a
      ><a name="20618"
      > </a
      ><a name="20619" href="StlcProp.html#20619" class="Bound"
      >&#8866;M</a
      ><a name="20621"
      > </a
      ><a name="20622" href="StlcProp.html#20622" class="Bound"
      >&#8866;N</a
      ><a name="20624" class="Symbol"
      >)</a
      ><a name="20625"
      > </a
      ><a name="20626" href="StlcProp.html#20626" class="Bound"
      >&#8866;V</a
      ><a name="20628"
      > </a
      ><a name="20629" class="Symbol"
      >=</a
      ><a name="20630"
      >
  </a
      ><a name="20633" href="Stlc.html#3434" class="InductiveConstructor"
      >&#120121;-E</a
      ><a name="20636"
      > </a
      ><a name="20637" class="Symbol"
      >(</a
      ><a name="20638" href="StlcProp.html#16053" class="Function"
      >preservation-[:=]</a
      ><a name="20655"
      > </a
      ><a name="20656" href="StlcProp.html#20616" class="Bound"
      >&#8866;L</a
      ><a name="20658"
      > </a
      ><a name="20659" href="StlcProp.html#20626" class="Bound"
      >&#8866;V</a
      ><a name="20661" class="Symbol"
      >)</a
      ><a name="20662"
      > </a
      ><a name="20663" class="Symbol"
      >(</a
      ><a name="20664" href="StlcProp.html#16053" class="Function"
      >preservation-[:=]</a
      ><a name="20681"
      > </a
      ><a name="20682" href="StlcProp.html#20619" class="Bound"
      >&#8866;M</a
      ><a name="20684"
      > </a
      ><a name="20685" href="StlcProp.html#20626" class="Bound"
      >&#8866;V</a
      ><a name="20687" class="Symbol"
      >)</a
      ><a name="20688"
      > </a
      ><a name="20689" class="Symbol"
      >(</a
      ><a name="20690" href="StlcProp.html#16053" class="Function"
      >preservation-[:=]</a
      ><a name="20707"
      > </a
      ><a name="20708" href="StlcProp.html#20622" class="Bound"
      >&#8866;N</a
      ><a name="20710"
      > </a
      ><a name="20711" href="StlcProp.html#20626" class="Bound"
      >&#8866;V</a
      ><a name="20713" class="Symbol"
      >)</a
      >

</pre>


### Main Theorem

We now have the tools we need to prove preservation: if a closed
term `M` has type `A` and takes a step to `N`, then `N`
is also a closed term with type `A`.  In other words, small-step
reduction preserves types.

<pre class="Agda">

<a name="20973" href="StlcProp.html#20973" class="Function"
      >preservation</a
      ><a name="20985"
      > </a
      ><a name="20986" class="Symbol"
      >:</a
      ><a name="20987"
      > </a
      ><a name="20988" class="Symbol"
      >&#8704;</a
      ><a name="20989"
      > </a
      ><a name="20990" class="Symbol"
      >{</a
      ><a name="20991" href="StlcProp.html#20991" class="Bound"
      >M</a
      ><a name="20992"
      > </a
      ><a name="20993" href="StlcProp.html#20993" class="Bound"
      >N</a
      ><a name="20994"
      > </a
      ><a name="20995" href="StlcProp.html#20995" class="Bound"
      >A</a
      ><a name="20996" class="Symbol"
      >}</a
      ><a name="20997"
      > </a
      ><a name="20998" class="Symbol"
      >&#8594;</a
      ><a name="20999"
      > </a
      ><a name="21000" href="Maps.html#10265" class="Function"
      >&#8709;</a
      ><a name="21001"
      > </a
      ><a name="21002" href="Stlc.html#3112" class="Datatype Operator"
      >&#8866;</a
      ><a name="21003"
      > </a
      ><a name="21004" href="StlcProp.html#20991" class="Bound"
      >M</a
      ><a name="21005"
      > </a
      ><a name="21006" href="Stlc.html#3112" class="Datatype Operator"
      >&#8758;</a
      ><a name="21007"
      > </a
      ><a name="21008" href="StlcProp.html#20995" class="Bound"
      >A</a
      ><a name="21009"
      > </a
      ><a name="21010" class="Symbol"
      >&#8594;</a
      ><a name="21011"
      > </a
      ><a name="21012" href="StlcProp.html#20991" class="Bound"
      >M</a
      ><a name="21013"
      > </a
      ><a name="21014" href="Stlc.html#1762" class="Datatype Operator"
      >&#10233;</a
      ><a name="21015"
      > </a
      ><a name="21016" href="StlcProp.html#20993" class="Bound"
      >N</a
      ><a name="21017"
      > </a
      ><a name="21018" class="Symbol"
      >&#8594;</a
      ><a name="21019"
      > </a
      ><a name="21020" href="Maps.html#10265" class="Function"
      >&#8709;</a
      ><a name="21021"
      > </a
      ><a name="21022" href="Stlc.html#3112" class="Datatype Operator"
      >&#8866;</a
      ><a name="21023"
      > </a
      ><a name="21024" href="StlcProp.html#20993" class="Bound"
      >N</a
      ><a name="21025"
      > </a
      ><a name="21026" href="Stlc.html#3112" class="Datatype Operator"
      >&#8758;</a
      ><a name="21027"
      > </a
      ><a name="21028" href="StlcProp.html#20995" class="Bound"
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

<a name="22286" href="StlcProp.html#20973" class="Function"
      >preservation</a
      ><a name="22298"
      > </a
      ><a name="22299" class="Symbol"
      >(</a
      ><a name="22300" href="Stlc.html#3156" class="InductiveConstructor"
      >Ax</a
      ><a name="22302"
      > </a
      ><a name="22303" href="StlcProp.html#22303" class="Bound"
      >&#915;x&#8801;A</a
      ><a name="22307" class="Symbol"
      >)</a
      ><a name="22308"
      > </a
      ><a name="22309" class="Symbol"
      >()</a
      ><a name="22311"
      >
</a
      ><a name="22312" href="StlcProp.html#20973" class="Function"
      >preservation</a
      ><a name="22324"
      > </a
      ><a name="22325" class="Symbol"
      >(</a
      ><a name="22326" href="Stlc.html#3210" class="InductiveConstructor"
      >&#8658;-I</a
      ><a name="22329"
      > </a
      ><a name="22330" href="StlcProp.html#22330" class="Bound"
      >&#8866;N</a
      ><a name="22332" class="Symbol"
      >)</a
      ><a name="22333"
      > </a
      ><a name="22334" class="Symbol"
      >()</a
      ><a name="22336"
      >
</a
      ><a name="22337" href="StlcProp.html#20973" class="Function"
      >preservation</a
      ><a name="22349"
      > </a
      ><a name="22350" class="Symbol"
      >(</a
      ><a name="22351" href="Stlc.html#3287" class="InductiveConstructor"
      >&#8658;-E</a
      ><a name="22354"
      > </a
      ><a name="22355" class="Symbol"
      >(</a
      ><a name="22356" href="Stlc.html#3210" class="InductiveConstructor"
      >&#8658;-I</a
      ><a name="22359"
      > </a
      ><a name="22360" href="StlcProp.html#22360" class="Bound"
      >&#8866;N</a
      ><a name="22362" class="Symbol"
      >)</a
      ><a name="22363"
      > </a
      ><a name="22364" href="StlcProp.html#22364" class="Bound"
      >&#8866;V</a
      ><a name="22366" class="Symbol"
      >)</a
      ><a name="22367"
      > </a
      ><a name="22368" class="Symbol"
      >(</a
      ><a name="22369" href="Stlc.html#1794" class="InductiveConstructor"
      >&#946;&#955;&#183;</a
      ><a name="22372"
      > </a
      ><a name="22373" href="StlcProp.html#22373" class="Bound"
      >valueV</a
      ><a name="22379" class="Symbol"
      >)</a
      ><a name="22380"
      > </a
      ><a name="22381" class="Symbol"
      >=</a
      ><a name="22382"
      > </a
      ><a name="22383" href="StlcProp.html#16053" class="Function"
      >preservation-[:=]</a
      ><a name="22400"
      > </a
      ><a name="22401" href="StlcProp.html#22360" class="Bound"
      >&#8866;N</a
      ><a name="22403"
      > </a
      ><a name="22404" href="StlcProp.html#22364" class="Bound"
      >&#8866;V</a
      ><a name="22406"
      >
</a
      ><a name="22407" href="StlcProp.html#20973" class="Function"
      >preservation</a
      ><a name="22419"
      > </a
      ><a name="22420" class="Symbol"
      >(</a
      ><a name="22421" href="Stlc.html#3287" class="InductiveConstructor"
      >&#8658;-E</a
      ><a name="22424"
      > </a
      ><a name="22425" href="StlcProp.html#22425" class="Bound"
      >&#8866;L</a
      ><a name="22427"
      > </a
      ><a name="22428" href="StlcProp.html#22428" class="Bound"
      >&#8866;M</a
      ><a name="22430" class="Symbol"
      >)</a
      ><a name="22431"
      > </a
      ><a name="22432" class="Symbol"
      >(</a
      ><a name="22433" href="Stlc.html#1864" class="InductiveConstructor"
      >&#958;&#183;&#8321;</a
      ><a name="22436"
      > </a
      ><a name="22437" href="StlcProp.html#22437" class="Bound"
      >L&#10233;L&#8242;</a
      ><a name="22441" class="Symbol"
      >)</a
      ><a name="22442"
      > </a
      ><a name="22443" class="Keyword"
      >with</a
      ><a name="22447"
      > </a
      ><a name="22448" href="StlcProp.html#20973" class="Function"
      >preservation</a
      ><a name="22460"
      > </a
      ><a name="22461" href="StlcProp.html#22425" class="Bound"
      >&#8866;L</a
      ><a name="22463"
      > </a
      ><a name="22464" href="StlcProp.html#22437" class="Bound"
      >L&#10233;L&#8242;</a
      ><a name="22468"
      >
</a
      ><a name="22469" class="Symbol"
      >...|</a
      ><a name="22473"
      > </a
      ><a name="22474" href="StlcProp.html#22474" class="Bound"
      >&#8866;L&#8242;</a
      ><a name="22477"
      > </a
      ><a name="22478" class="Symbol"
      >=</a
      ><a name="22479"
      > </a
      ><a name="22480" href="Stlc.html#3287" class="InductiveConstructor"
      >&#8658;-E</a
      ><a name="22483"
      > </a
      ><a name="22484" href="StlcProp.html#22474" class="Bound"
      >&#8866;L&#8242;</a
      ><a name="22487"
      > </a
      ><a name="22488" href="StlcProp.html#22428" class="Bound"
      >&#8866;M</a
      ><a name="22490"
      >
</a
      ><a name="22491" href="StlcProp.html#20973" class="Function"
      >preservation</a
      ><a name="22503"
      > </a
      ><a name="22504" class="Symbol"
      >(</a
      ><a name="22505" href="Stlc.html#3287" class="InductiveConstructor"
      >&#8658;-E</a
      ><a name="22508"
      > </a
      ><a name="22509" href="StlcProp.html#22509" class="Bound"
      >&#8866;L</a
      ><a name="22511"
      > </a
      ><a name="22512" href="StlcProp.html#22512" class="Bound"
      >&#8866;M</a
      ><a name="22514" class="Symbol"
      >)</a
      ><a name="22515"
      > </a
      ><a name="22516" class="Symbol"
      >(</a
      ><a name="22517" href="Stlc.html#1917" class="InductiveConstructor"
      >&#958;&#183;&#8322;</a
      ><a name="22520"
      > </a
      ><a name="22521" href="StlcProp.html#22521" class="Bound"
      >valueL</a
      ><a name="22527"
      > </a
      ><a name="22528" href="StlcProp.html#22528" class="Bound"
      >M&#10233;M&#8242;</a
      ><a name="22532" class="Symbol"
      >)</a
      ><a name="22533"
      > </a
      ><a name="22534" class="Keyword"
      >with</a
      ><a name="22538"
      > </a
      ><a name="22539" href="StlcProp.html#20973" class="Function"
      >preservation</a
      ><a name="22551"
      > </a
      ><a name="22552" href="StlcProp.html#22512" class="Bound"
      >&#8866;M</a
      ><a name="22554"
      > </a
      ><a name="22555" href="StlcProp.html#22528" class="Bound"
      >M&#10233;M&#8242;</a
      ><a name="22559"
      >
</a
      ><a name="22560" class="Symbol"
      >...|</a
      ><a name="22564"
      > </a
      ><a name="22565" href="StlcProp.html#22565" class="Bound"
      >&#8866;M&#8242;</a
      ><a name="22568"
      > </a
      ><a name="22569" class="Symbol"
      >=</a
      ><a name="22570"
      > </a
      ><a name="22571" href="Stlc.html#3287" class="InductiveConstructor"
      >&#8658;-E</a
      ><a name="22574"
      > </a
      ><a name="22575" href="StlcProp.html#22509" class="Bound"
      >&#8866;L</a
      ><a name="22577"
      > </a
      ><a name="22578" href="StlcProp.html#22565" class="Bound"
      >&#8866;M&#8242;</a
      ><a name="22581"
      >
</a
      ><a name="22582" href="StlcProp.html#20973" class="Function"
      >preservation</a
      ><a name="22594"
      > </a
      ><a name="22595" href="Stlc.html#3365" class="InductiveConstructor"
      >&#120121;-I&#8321;</a
      ><a name="22599"
      > </a
      ><a name="22600" class="Symbol"
      >()</a
      ><a name="22602"
      >
</a
      ><a name="22603" href="StlcProp.html#20973" class="Function"
      >preservation</a
      ><a name="22615"
      > </a
      ><a name="22616" href="Stlc.html#3399" class="InductiveConstructor"
      >&#120121;-I&#8322;</a
      ><a name="22620"
      > </a
      ><a name="22621" class="Symbol"
      >()</a
      ><a name="22623"
      >
</a
      ><a name="22624" href="StlcProp.html#20973" class="Function"
      >preservation</a
      ><a name="22636"
      > </a
      ><a name="22637" class="Symbol"
      >(</a
      ><a name="22638" href="Stlc.html#3434" class="InductiveConstructor"
      >&#120121;-E</a
      ><a name="22641"
      > </a
      ><a name="22642" href="Stlc.html#3365" class="InductiveConstructor"
      >&#120121;-I&#8321;</a
      ><a name="22646"
      > </a
      ><a name="22647" href="StlcProp.html#22647" class="Bound"
      >&#8866;M</a
      ><a name="22649"
      > </a
      ><a name="22650" href="StlcProp.html#22650" class="Bound"
      >&#8866;N</a
      ><a name="22652" class="Symbol"
      >)</a
      ><a name="22653"
      > </a
      ><a name="22654" href="Stlc.html#1984" class="InductiveConstructor"
      >&#946;if-true</a
      ><a name="22662"
      > </a
      ><a name="22663" class="Symbol"
      >=</a
      ><a name="22664"
      > </a
      ><a name="22665" href="StlcProp.html#22647" class="Bound"
      >&#8866;M</a
      ><a name="22667"
      >
</a
      ><a name="22668" href="StlcProp.html#20973" class="Function"
      >preservation</a
      ><a name="22680"
      > </a
      ><a name="22681" class="Symbol"
      >(</a
      ><a name="22682" href="Stlc.html#3434" class="InductiveConstructor"
      >&#120121;-E</a
      ><a name="22685"
      > </a
      ><a name="22686" href="Stlc.html#3399" class="InductiveConstructor"
      >&#120121;-I&#8322;</a
      ><a name="22690"
      > </a
      ><a name="22691" href="StlcProp.html#22691" class="Bound"
      >&#8866;M</a
      ><a name="22693"
      > </a
      ><a name="22694" href="StlcProp.html#22694" class="Bound"
      >&#8866;N</a
      ><a name="22696" class="Symbol"
      >)</a
      ><a name="22697"
      > </a
      ><a name="22698" href="Stlc.html#2037" class="InductiveConstructor"
      >&#946;if-false</a
      ><a name="22707"
      > </a
      ><a name="22708" class="Symbol"
      >=</a
      ><a name="22709"
      > </a
      ><a name="22710" href="StlcProp.html#22694" class="Bound"
      >&#8866;N</a
      ><a name="22712"
      >
</a
      ><a name="22713" href="StlcProp.html#20973" class="Function"
      >preservation</a
      ><a name="22725"
      > </a
      ><a name="22726" class="Symbol"
      >(</a
      ><a name="22727" href="Stlc.html#3434" class="InductiveConstructor"
      >&#120121;-E</a
      ><a name="22730"
      > </a
      ><a name="22731" href="StlcProp.html#22731" class="Bound"
      >&#8866;L</a
      ><a name="22733"
      > </a
      ><a name="22734" href="StlcProp.html#22734" class="Bound"
      >&#8866;M</a
      ><a name="22736"
      > </a
      ><a name="22737" href="StlcProp.html#22737" class="Bound"
      >&#8866;N</a
      ><a name="22739" class="Symbol"
      >)</a
      ><a name="22740"
      > </a
      ><a name="22741" class="Symbol"
      >(</a
      ><a name="22742" href="Stlc.html#2092" class="InductiveConstructor"
      >&#958;if</a
      ><a name="22745"
      > </a
      ><a name="22746" href="StlcProp.html#22746" class="Bound"
      >L&#10233;L&#8242;</a
      ><a name="22750" class="Symbol"
      >)</a
      ><a name="22751"
      > </a
      ><a name="22752" class="Keyword"
      >with</a
      ><a name="22756"
      > </a
      ><a name="22757" href="StlcProp.html#20973" class="Function"
      >preservation</a
      ><a name="22769"
      > </a
      ><a name="22770" href="StlcProp.html#22731" class="Bound"
      >&#8866;L</a
      ><a name="22772"
      > </a
      ><a name="22773" href="StlcProp.html#22746" class="Bound"
      >L&#10233;L&#8242;</a
      ><a name="22777"
      >
</a
      ><a name="22778" class="Symbol"
      >...|</a
      ><a name="22782"
      > </a
      ><a name="22783" href="StlcProp.html#22783" class="Bound"
      >&#8866;L&#8242;</a
      ><a name="22786"
      > </a
      ><a name="22787" class="Symbol"
      >=</a
      ><a name="22788"
      > </a
      ><a name="22789" href="Stlc.html#3434" class="InductiveConstructor"
      >&#120121;-E</a
      ><a name="22792"
      > </a
      ><a name="22793" href="StlcProp.html#22783" class="Bound"
      >&#8866;L&#8242;</a
      ><a name="22796"
      > </a
      ><a name="22797" href="StlcProp.html#22734" class="Bound"
      >&#8866;M</a
      ><a name="22799"
      > </a
      ><a name="22800" href="StlcProp.html#22737" class="Bound"
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

<a name="23453" href="StlcProp.html#23453" class="Function"
      >Normal</a
      ><a name="23459"
      > </a
      ><a name="23460" class="Symbol"
      >:</a
      ><a name="23461"
      > </a
      ><a name="23462" href="Stlc.html#708" class="Datatype"
      >Term</a
      ><a name="23466"
      > </a
      ><a name="23467" class="Symbol"
      >&#8594;</a
      ><a name="23468"
      > </a
      ><a name="23469" class="PrimitiveType"
      >Set</a
      ><a name="23472"
      >
</a
      ><a name="23473" href="StlcProp.html#23453" class="Function"
      >Normal</a
      ><a name="23479"
      > </a
      ><a name="23480" href="StlcProp.html#23480" class="Bound"
      >M</a
      ><a name="23481"
      > </a
      ><a name="23482" class="Symbol"
      >=</a
      ><a name="23483"
      > </a
      ><a name="23484" class="Symbol"
      >&#8704;</a
      ><a name="23485"
      > </a
      ><a name="23486" class="Symbol"
      >{</a
      ><a name="23487" href="StlcProp.html#23487" class="Bound"
      >N</a
      ><a name="23488" class="Symbol"
      >}</a
      ><a name="23489"
      > </a
      ><a name="23490" class="Symbol"
      >&#8594;</a
      ><a name="23491"
      > </a
      ><a name="23492" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#414" class="Function Operator"
      >&#172;</a
      ><a name="23493"
      > </a
      ><a name="23494" class="Symbol"
      >(</a
      ><a name="23495" href="StlcProp.html#23480" class="Bound"
      >M</a
      ><a name="23496"
      > </a
      ><a name="23497" href="Stlc.html#1762" class="Datatype Operator"
      >&#10233;</a
      ><a name="23498"
      > </a
      ><a name="23499" href="StlcProp.html#23487" class="Bound"
      >N</a
      ><a name="23500" class="Symbol"
      >)</a
      ><a name="23501"
      >

</a
      ><a name="23503" href="StlcProp.html#23503" class="Function"
      >Stuck</a
      ><a name="23508"
      > </a
      ><a name="23509" class="Symbol"
      >:</a
      ><a name="23510"
      > </a
      ><a name="23511" href="Stlc.html#708" class="Datatype"
      >Term</a
      ><a name="23515"
      > </a
      ><a name="23516" class="Symbol"
      >&#8594;</a
      ><a name="23517"
      > </a
      ><a name="23518" class="PrimitiveType"
      >Set</a
      ><a name="23521"
      >
</a
      ><a name="23522" href="StlcProp.html#23503" class="Function"
      >Stuck</a
      ><a name="23527"
      > </a
      ><a name="23528" href="StlcProp.html#23528" class="Bound"
      >M</a
      ><a name="23529"
      > </a
      ><a name="23530" class="Symbol"
      >=</a
      ><a name="23531"
      > </a
      ><a name="23532" href="StlcProp.html#23453" class="Function"
      >Normal</a
      ><a name="23538"
      > </a
      ><a name="23539" href="StlcProp.html#23528" class="Bound"
      >M</a
      ><a name="23540"
      > </a
      ><a name="23541" href="https://agda.github.io/agda-stdlib/Data.Product.html#1073" class="Function Operator"
      >&#215;</a
      ><a name="23542"
      > </a
      ><a name="23543" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#414" class="Function Operator"
      >&#172;</a
      ><a name="23544"
      > </a
      ><a name="23545" href="Stlc.html#1105" class="Datatype"
      >Value</a
      ><a name="23550"
      > </a
      ><a name="23551" href="StlcProp.html#23528" class="Bound"
      >M</a
      ><a name="23552"
      >

</a
      ><a name="23554" class="Keyword"
      >postulate</a
      ><a name="23563"
      >
  </a
      ><a name="23566" href="StlcProp.html#23566" class="Postulate"
      >Soundness</a
      ><a name="23575"
      > </a
      ><a name="23576" class="Symbol"
      >:</a
      ><a name="23577"
      > </a
      ><a name="23578" class="Symbol"
      >&#8704;</a
      ><a name="23579"
      > </a
      ><a name="23580" class="Symbol"
      >{</a
      ><a name="23581" href="StlcProp.html#23581" class="Bound"
      >M</a
      ><a name="23582"
      > </a
      ><a name="23583" href="StlcProp.html#23583" class="Bound"
      >N</a
      ><a name="23584"
      > </a
      ><a name="23585" href="StlcProp.html#23585" class="Bound"
      >A</a
      ><a name="23586" class="Symbol"
      >}</a
      ><a name="23587"
      > </a
      ><a name="23588" class="Symbol"
      >&#8594;</a
      ><a name="23589"
      > </a
      ><a name="23590" href="Maps.html#10265" class="Function"
      >&#8709;</a
      ><a name="23591"
      > </a
      ><a name="23592" href="Stlc.html#3112" class="Datatype Operator"
      >&#8866;</a
      ><a name="23593"
      > </a
      ><a name="23594" href="StlcProp.html#23581" class="Bound"
      >M</a
      ><a name="23595"
      > </a
      ><a name="23596" href="Stlc.html#3112" class="Datatype Operator"
      >&#8758;</a
      ><a name="23597"
      > </a
      ><a name="23598" href="StlcProp.html#23585" class="Bound"
      >A</a
      ><a name="23599"
      > </a
      ><a name="23600" class="Symbol"
      >&#8594;</a
      ><a name="23601"
      > </a
      ><a name="23602" href="StlcProp.html#23581" class="Bound"
      >M</a
      ><a name="23603"
      > </a
      ><a name="23604" href="Stlc.html#2287" class="Datatype Operator"
      >&#10233;*</a
      ><a name="23606"
      > </a
      ><a name="23607" href="StlcProp.html#23583" class="Bound"
      >N</a
      ><a name="23608"
      > </a
      ><a name="23609" class="Symbol"
      >&#8594;</a
      ><a name="23610"
      > </a
      ><a name="23611" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#414" class="Function Operator"
      >&#172;</a
      ><a name="23612"
      > </a
      ><a name="23613" class="Symbol"
      >(</a
      ><a name="23614" href="StlcProp.html#23503" class="Function"
      >Stuck</a
      ><a name="23619"
      > </a
      ><a name="23620" href="StlcProp.html#23583" class="Bound"
      >N</a
      ><a name="23621" class="Symbol"
      >)</a
      >

</pre>

<div class="hidden">
<pre class="Agda">

<a name="23669" href="StlcProp.html#23669" class="Function"
      >Soundness&#8242;</a
      ><a name="23679"
      > </a
      ><a name="23680" class="Symbol"
      >:</a
      ><a name="23681"
      > </a
      ><a name="23682" class="Symbol"
      >&#8704;</a
      ><a name="23683"
      > </a
      ><a name="23684" class="Symbol"
      >{</a
      ><a name="23685" href="StlcProp.html#23685" class="Bound"
      >M</a
      ><a name="23686"
      > </a
      ><a name="23687" href="StlcProp.html#23687" class="Bound"
      >N</a
      ><a name="23688"
      > </a
      ><a name="23689" href="StlcProp.html#23689" class="Bound"
      >A</a
      ><a name="23690" class="Symbol"
      >}</a
      ><a name="23691"
      > </a
      ><a name="23692" class="Symbol"
      >&#8594;</a
      ><a name="23693"
      > </a
      ><a name="23694" href="Maps.html#10265" class="Function"
      >&#8709;</a
      ><a name="23695"
      > </a
      ><a name="23696" href="Stlc.html#3112" class="Datatype Operator"
      >&#8866;</a
      ><a name="23697"
      > </a
      ><a name="23698" href="StlcProp.html#23685" class="Bound"
      >M</a
      ><a name="23699"
      > </a
      ><a name="23700" href="Stlc.html#3112" class="Datatype Operator"
      >&#8758;</a
      ><a name="23701"
      > </a
      ><a name="23702" href="StlcProp.html#23689" class="Bound"
      >A</a
      ><a name="23703"
      > </a
      ><a name="23704" class="Symbol"
      >&#8594;</a
      ><a name="23705"
      > </a
      ><a name="23706" href="StlcProp.html#23685" class="Bound"
      >M</a
      ><a name="23707"
      > </a
      ><a name="23708" href="Stlc.html#2287" class="Datatype Operator"
      >&#10233;*</a
      ><a name="23710"
      > </a
      ><a name="23711" href="StlcProp.html#23687" class="Bound"
      >N</a
      ><a name="23712"
      > </a
      ><a name="23713" class="Symbol"
      >&#8594;</a
      ><a name="23714"
      > </a
      ><a name="23715" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#414" class="Function Operator"
      >&#172;</a
      ><a name="23716"
      > </a
      ><a name="23717" class="Symbol"
      >(</a
      ><a name="23718" href="StlcProp.html#23503" class="Function"
      >Stuck</a
      ><a name="23723"
      > </a
      ><a name="23724" href="StlcProp.html#23687" class="Bound"
      >N</a
      ><a name="23725" class="Symbol"
      >)</a
      ><a name="23726"
      >
</a
      ><a name="23727" href="StlcProp.html#23669" class="Function"
      >Soundness&#8242;</a
      ><a name="23737"
      > </a
      ><a name="23738" href="StlcProp.html#23738" class="Bound"
      >&#8866;M</a
      ><a name="23740"
      > </a
      ><a name="23741" class="Symbol"
      >(</a
      ><a name="23742" href="StlcProp.html#23742" class="Bound"
      >M</a
      ><a name="23743"
      > </a
      ><a name="23744" href="Stlc.html#2320" class="InductiveConstructor Operator"
      >&#8718;</a
      ><a name="23745" class="Symbol"
      >)</a
      ><a name="23746"
      > </a
      ><a name="23747" class="Symbol"
      >(</a
      ><a name="23748" href="StlcProp.html#23748" class="Bound"
      >&#172;M&#10233;N</a
      ><a name="23752"
      > </a
      ><a name="23753" href="https://agda.github.io/agda-stdlib/Data.Product.html#509" class="InductiveConstructor Operator"
      >,</a
      ><a name="23754"
      > </a
      ><a name="23755" href="StlcProp.html#23755" class="Bound"
      >&#172;ValueM</a
      ><a name="23762" class="Symbol"
      >)</a
      ><a name="23763"
      > </a
      ><a name="23764" class="Keyword"
      >with</a
      ><a name="23768"
      > </a
      ><a name="23769" href="StlcProp.html#1998" class="Function"
      >progress</a
      ><a name="23777"
      > </a
      ><a name="23778" href="StlcProp.html#23738" class="Bound"
      >&#8866;M</a
      ><a name="23780"
      >
</a
      ><a name="23781" class="Symbol"
      >...</a
      ><a name="23784"
      > </a
      ><a name="23785" class="Symbol"
      >|</a
      ><a name="23786"
      > </a
      ><a name="23787" href="StlcProp.html#1921" class="InductiveConstructor"
      >steps</a
      ><a name="23792"
      > </a
      ><a name="23793" href="StlcProp.html#23793" class="Bound"
      >M&#10233;N</a
      ><a name="23796"
      >  </a
      ><a name="23798" class="Symbol"
      >=</a
      ><a name="23799"
      > </a
      ><a name="23800" href="StlcProp.html#23748" class="Bound"
      >&#172;M&#10233;N</a
      ><a name="23804"
      > </a
      ><a name="23805" href="StlcProp.html#23793" class="Bound"
      >M&#10233;N</a
      ><a name="23808"
      >
</a
      ><a name="23809" class="Symbol"
      >...</a
      ><a name="23812"
      > </a
      ><a name="23813" class="Symbol"
      >|</a
      ><a name="23814"
      > </a
      ><a name="23815" href="StlcProp.html#1960" class="InductiveConstructor"
      >done</a
      ><a name="23819"
      > </a
      ><a name="23820" href="StlcProp.html#23820" class="Bound"
      >ValueM</a
      ><a name="23826"
      >  </a
      ><a name="23828" class="Symbol"
      >=</a
      ><a name="23829"
      > </a
      ><a name="23830" href="StlcProp.html#23755" class="Bound"
      >&#172;ValueM</a
      ><a name="23837"
      > </a
      ><a name="23838" href="StlcProp.html#23820" class="Bound"
      >ValueM</a
      ><a name="23844"
      >
</a
      ><a name="23845" href="StlcProp.html#23669" class="Function"
      >Soundness&#8242;</a
      ><a name="23855"
      > </a
      ><a name="23856" class="Symbol"
      >{</a
      ><a name="23857" href="StlcProp.html#23857" class="Bound"
      >L</a
      ><a name="23858" class="Symbol"
      >}</a
      ><a name="23859"
      > </a
      ><a name="23860" class="Symbol"
      >{</a
      ><a name="23861" href="StlcProp.html#23861" class="Bound"
      >N</a
      ><a name="23862" class="Symbol"
      >}</a
      ><a name="23863"
      > </a
      ><a name="23864" class="Symbol"
      >{</a
      ><a name="23865" href="StlcProp.html#23865" class="Bound"
      >A</a
      ><a name="23866" class="Symbol"
      >}</a
      ><a name="23867"
      > </a
      ><a name="23868" href="StlcProp.html#23868" class="Bound"
      >&#8866;L</a
      ><a name="23870"
      > </a
      ><a name="23871" class="Symbol"
      >(</a
      ><a name="23872" href="Stlc.html#2340" class="InductiveConstructor Operator"
      >_&#10233;&#10216;_&#10217;_</a
      ><a name="23878"
      > </a
      ><a name="23879" class="DottedPattern Symbol"
      >.</a
      ><a name="23880" href="StlcProp.html#23857" class="DottedPattern Bound"
      >L</a
      ><a name="23881"
      > </a
      ><a name="23882" class="Symbol"
      >{</a
      ><a name="23883" href="StlcProp.html#23883" class="Bound"
      >M</a
      ><a name="23884" class="Symbol"
      >}</a
      ><a name="23885"
      > </a
      ><a name="23886" class="Symbol"
      >{</a
      ><a name="23887" class="DottedPattern Symbol"
      >.</a
      ><a name="23888" href="StlcProp.html#23861" class="DottedPattern Bound"
      >N</a
      ><a name="23889" class="Symbol"
      >}</a
      ><a name="23890"
      > </a
      ><a name="23891" href="StlcProp.html#23891" class="Bound"
      >L&#10233;M</a
      ><a name="23894"
      > </a
      ><a name="23895" href="StlcProp.html#23895" class="Bound"
      >M&#10233;*N</a
      ><a name="23899" class="Symbol"
      >)</a
      ><a name="23900"
      > </a
      ><a name="23901" class="Symbol"
      >=</a
      ><a name="23902"
      > </a
      ><a name="23903" href="StlcProp.html#23669" class="Function"
      >Soundness&#8242;</a
      ><a name="23913"
      > </a
      ><a name="23914" href="StlcProp.html#23932" class="Function"
      >&#8866;M</a
      ><a name="23916"
      > </a
      ><a name="23917" href="StlcProp.html#23895" class="Bound"
      >M&#10233;*N</a
      ><a name="23921"
      >
  </a
      ><a name="23924" class="Keyword"
      >where</a
      ><a name="23929"
      >
  </a
      ><a name="23932" href="StlcProp.html#23932" class="Function"
      >&#8866;M</a
      ><a name="23934"
      > </a
      ><a name="23935" class="Symbol"
      >:</a
      ><a name="23936"
      > </a
      ><a name="23937" href="Maps.html#10265" class="Function"
      >&#8709;</a
      ><a name="23938"
      > </a
      ><a name="23939" href="Stlc.html#3112" class="Datatype Operator"
      >&#8866;</a
      ><a name="23940"
      > </a
      ><a name="23941" href="StlcProp.html#23883" class="Bound"
      >M</a
      ><a name="23942"
      > </a
      ><a name="23943" href="Stlc.html#3112" class="Datatype Operator"
      >&#8758;</a
      ><a name="23944"
      > </a
      ><a name="23945" href="StlcProp.html#23865" class="Bound"
      >A</a
      ><a name="23946"
      >
  </a
      ><a name="23949" href="StlcProp.html#23932" class="Function"
      >&#8866;M</a
      ><a name="23951"
      > </a
      ><a name="23952" class="Symbol"
      >=</a
      ><a name="23953"
      > </a
      ><a name="23954" href="StlcProp.html#20973" class="Function"
      >preservation</a
      ><a name="23966"
      > </a
      ><a name="23967" href="StlcProp.html#23868" class="Bound"
      >&#8866;L</a
      ><a name="23969"
      > </a
      ><a name="23970" href="StlcProp.html#23891" class="Bound"
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
``

#### Exercise: 2 stars (stlc_variation1)
Suppose we add a new term `zap` with the following reduction rule

                     ---------                  (ST_Zap)
                     t ==> zap

and the following typing rule:

                  ----------------               (T_Zap)
                  Gamma \vdash zap : T

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

                   -----------------                (ST_Foo1)
                   (\lambda x:A. x) ==> foo

                     ------------                   (ST_Foo2)
                     foo ==> true

Which of the following properties of the STLC remain true in
the presence of this rule?  For each one, write either
"remains true" or else "becomes false." If a property becomes
false, give a counterexample.

  - Determinism of `step`

  - Progress

  - Preservation

#### Exercise: 2 stars (stlc_variation3)
Suppose instead that we remove the rule `Sapp1` from the `step`
relation. Which of the following properties of the STLC remain
true in the presence of this rule?  For each one, write either
"remains true" or else "becomes false." If a property becomes
false, give a counterexample.

  - Determinism of `step`

  - Progress

  - Preservation

#### Exercise: 2 stars, optional (stlc_variation4)
Suppose instead that we add the following new rule to the
reduction relation:

        ----------------------------------        (ST_FunnyIfTrue)
        (if true then t_1 else t_2) ==> true

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

             Gamma \vdash t_1 : bool→bool→bool
                 Gamma \vdash t_2 : bool
             ------------------------------          (T_FunnyApp)
                Gamma \vdash t_1 t_2 : bool

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

                 Gamma \vdash t_1 : bool
                 Gamma \vdash t_2 : bool
                ---------------------               (T_FunnyApp')
                Gamma \vdash t_1 t_2 : bool

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

                     ------------------- (T_FunnyAbs)
                     \vdash \lambda x:bool.t : bool

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

To types, we add a base type of natural numbers (and remove
booleans, for brevity).

Inductive ty : Type :=
  | TArrow : ty → ty → ty
  | TNat   : ty.

To terms, we add natural number constants, along with
successor, predecessor, multiplication, and zero-testing.

Inductive tm : Type :=
  | tvar : id → tm
  | tapp : tm → tm → tm
  | tabs : id → ty → tm → tm
  | tnat  : nat → tm
  | tsucc : tm → tm
  | tpred : tm → tm
  | tmult : tm → tm → tm
  | tif0  : tm → tm → tm → tm.

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

