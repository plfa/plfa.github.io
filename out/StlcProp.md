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
      >canonical-forms</a
      ><a name="1370"
      > </a
      ><a name="1371" class="Symbol"
      >:</a
      ><a name="1372"
      > </a
      ><a name="1373" class="Symbol"
      >&#8704;</a
      ><a name="1374"
      > </a
      ><a name="1375" class="Symbol"
      >{</a
      ><a name="1376" href="StlcProp.html#1376" class="Bound"
      >L</a
      ><a name="1377"
      > </a
      ><a name="1378" href="StlcProp.html#1378" class="Bound"
      >A</a
      ><a name="1379" class="Symbol"
      >}</a
      ><a name="1380"
      > </a
      ><a name="1381" class="Symbol"
      >&#8594;</a
      ><a name="1382"
      > </a
      ><a name="1383" href="Maps.html#10265" class="Function"
      >&#8709;</a
      ><a name="1384"
      > </a
      ><a name="1385" href="Stlc.html#3112" class="Datatype Operator"
      >&#8866;</a
      ><a name="1386"
      > </a
      ><a name="1387" href="StlcProp.html#1376" class="Bound"
      >L</a
      ><a name="1388"
      > </a
      ><a name="1389" href="Stlc.html#3112" class="Datatype Operator"
      >&#8758;</a
      ><a name="1390"
      > </a
      ><a name="1391" href="StlcProp.html#1378" class="Bound"
      >A</a
      ><a name="1392"
      > </a
      ><a name="1393" class="Symbol"
      >&#8594;</a
      ><a name="1394"
      > </a
      ><a name="1395" href="Stlc.html#1105" class="Datatype"
      >Value</a
      ><a name="1400"
      > </a
      ><a name="1401" href="StlcProp.html#1376" class="Bound"
      >L</a
      ><a name="1402"
      > </a
      ><a name="1403" class="Symbol"
      >&#8594;</a
      ><a name="1404"
      > </a
      ><a name="1405" href="StlcProp.html#1164" class="Datatype Operator"
      >canonical</a
      ><a name="1414"
      > </a
      ><a name="1415" href="StlcProp.html#1376" class="Bound"
      >L</a
      ><a name="1416"
      > </a
      ><a name="1417" href="StlcProp.html#1164" class="Datatype Operator"
      >for</a
      ><a name="1420"
      > </a
      ><a name="1421" href="StlcProp.html#1378" class="Bound"
      >A</a
      ><a name="1422"
      >
</a
      ><a name="1423" href="StlcProp.html#1355" class="Function"
      >canonical-forms</a
      ><a name="1438"
      > </a
      ><a name="1439" class="Symbol"
      >(</a
      ><a name="1440" href="Stlc.html#3156" class="InductiveConstructor"
      >Ax</a
      ><a name="1442"
      > </a
      ><a name="1443" class="Symbol"
      >())</a
      ><a name="1446"
      > </a
      ><a name="1447" class="Symbol"
      >()</a
      ><a name="1449"
      >
</a
      ><a name="1450" href="StlcProp.html#1355" class="Function"
      >canonical-forms</a
      ><a name="1465"
      > </a
      ><a name="1466" class="Symbol"
      >(</a
      ><a name="1467" href="Stlc.html#3210" class="InductiveConstructor"
      >&#8658;-I</a
      ><a name="1470"
      > </a
      ><a name="1471" href="StlcProp.html#1471" class="Bound"
      >&#8866;N</a
      ><a name="1473" class="Symbol"
      >)</a
      ><a name="1474"
      > </a
      ><a name="1475" href="Stlc.html#1132" class="InductiveConstructor"
      >value-&#955;</a
      ><a name="1482"
      > </a
      ><a name="1483" class="Symbol"
      >=</a
      ><a name="1484"
      > </a
      ><a name="1485" href="StlcProp.html#1207" class="InductiveConstructor"
      >canonical-&#955;</a
      ><a name="1496"
      >
</a
      ><a name="1497" href="StlcProp.html#1355" class="Function"
      >canonical-forms</a
      ><a name="1512"
      > </a
      ><a name="1513" class="Symbol"
      >(</a
      ><a name="1514" href="Stlc.html#3287" class="InductiveConstructor"
      >&#8658;-E</a
      ><a name="1517"
      > </a
      ><a name="1518" href="StlcProp.html#1518" class="Bound"
      >&#8866;L</a
      ><a name="1520"
      > </a
      ><a name="1521" href="StlcProp.html#1521" class="Bound"
      >&#8866;M</a
      ><a name="1523" class="Symbol"
      >)</a
      ><a name="1524"
      > </a
      ><a name="1525" class="Symbol"
      >()</a
      ><a name="1527"
      >
</a
      ><a name="1528" href="StlcProp.html#1355" class="Function"
      >canonical-forms</a
      ><a name="1543"
      > </a
      ><a name="1544" href="Stlc.html#3365" class="InductiveConstructor"
      >&#120121;-I&#8321;</a
      ><a name="1548"
      > </a
      ><a name="1549" href="Stlc.html#1181" class="InductiveConstructor"
      >value-true</a
      ><a name="1559"
      > </a
      ><a name="1560" class="Symbol"
      >=</a
      ><a name="1561"
      > </a
      ><a name="1562" href="StlcProp.html#1274" class="InductiveConstructor"
      >canonical-true</a
      ><a name="1576"
      >
</a
      ><a name="1577" href="StlcProp.html#1355" class="Function"
      >canonical-forms</a
      ><a name="1592"
      > </a
      ><a name="1593" href="Stlc.html#3399" class="InductiveConstructor"
      >&#120121;-I&#8322;</a
      ><a name="1597"
      > </a
      ><a name="1598" href="Stlc.html#1208" class="InductiveConstructor"
      >value-false</a
      ><a name="1609"
      > </a
      ><a name="1610" class="Symbol"
      >=</a
      ><a name="1611"
      > </a
      ><a name="1612" href="StlcProp.html#1314" class="InductiveConstructor"
      >canonical-false</a
      ><a name="1627"
      >
</a
      ><a name="1628" href="StlcProp.html#1355" class="Function"
      >canonical-forms</a
      ><a name="1643"
      > </a
      ><a name="1644" class="Symbol"
      >(</a
      ><a name="1645" href="Stlc.html#3434" class="InductiveConstructor"
      >&#120121;-E</a
      ><a name="1648"
      > </a
      ><a name="1649" href="StlcProp.html#1649" class="Bound"
      >&#8866;L</a
      ><a name="1651"
      > </a
      ><a name="1652" href="StlcProp.html#1652" class="Bound"
      >&#8866;M</a
      ><a name="1654"
      > </a
      ><a name="1655" href="StlcProp.html#1655" class="Bound"
      >&#8866;N</a
      ><a name="1657" class="Symbol"
      >)</a
      ><a name="1658"
      > </a
      ><a name="1659" class="Symbol"
      >()</a
      >

</pre>

## Progress

As before, the _progress_ theorem tells us that closed, well-typed
terms are not stuck: either a well-typed term can take a reduction
step or it is a value.

<pre class="Agda">

<a name="1858" class="Keyword"
      >data</a
      ><a name="1862"
      > </a
      ><a name="1863" href="StlcProp.html#1863" class="Datatype"
      >Progress</a
      ><a name="1871"
      > </a
      ><a name="1872" class="Symbol"
      >:</a
      ><a name="1873"
      > </a
      ><a name="1874" href="Stlc.html#708" class="Datatype"
      >Term</a
      ><a name="1878"
      > </a
      ><a name="1879" class="Symbol"
      >&#8594;</a
      ><a name="1880"
      > </a
      ><a name="1881" class="PrimitiveType"
      >Set</a
      ><a name="1884"
      > </a
      ><a name="1885" class="Keyword"
      >where</a
      ><a name="1890"
      >
  </a
      ><a name="1893" href="StlcProp.html#1893" class="InductiveConstructor"
      >steps</a
      ><a name="1898"
      > </a
      ><a name="1899" class="Symbol"
      >:</a
      ><a name="1900"
      > </a
      ><a name="1901" class="Symbol"
      >&#8704;</a
      ><a name="1902"
      > </a
      ><a name="1903" class="Symbol"
      >{</a
      ><a name="1904" href="StlcProp.html#1904" class="Bound"
      >M</a
      ><a name="1905"
      > </a
      ><a name="1906" href="StlcProp.html#1906" class="Bound"
      >N</a
      ><a name="1907" class="Symbol"
      >}</a
      ><a name="1908"
      > </a
      ><a name="1909" class="Symbol"
      >&#8594;</a
      ><a name="1910"
      > </a
      ><a name="1911" href="StlcProp.html#1904" class="Bound"
      >M</a
      ><a name="1912"
      > </a
      ><a name="1913" href="Stlc.html#1762" class="Datatype Operator"
      >&#10233;</a
      ><a name="1914"
      > </a
      ><a name="1915" href="StlcProp.html#1906" class="Bound"
      >N</a
      ><a name="1916"
      > </a
      ><a name="1917" class="Symbol"
      >&#8594;</a
      ><a name="1918"
      > </a
      ><a name="1919" href="StlcProp.html#1863" class="Datatype"
      >Progress</a
      ><a name="1927"
      > </a
      ><a name="1928" href="StlcProp.html#1904" class="Bound"
      >M</a
      ><a name="1929"
      >
  </a
      ><a name="1932" href="StlcProp.html#1932" class="InductiveConstructor"
      >done</a
      ><a name="1936"
      >  </a
      ><a name="1938" class="Symbol"
      >:</a
      ><a name="1939"
      > </a
      ><a name="1940" class="Symbol"
      >&#8704;</a
      ><a name="1941"
      > </a
      ><a name="1942" class="Symbol"
      >{</a
      ><a name="1943" href="StlcProp.html#1943" class="Bound"
      >M</a
      ><a name="1944" class="Symbol"
      >}</a
      ><a name="1945"
      > </a
      ><a name="1946" class="Symbol"
      >&#8594;</a
      ><a name="1947"
      > </a
      ><a name="1948" href="Stlc.html#1105" class="Datatype"
      >Value</a
      ><a name="1953"
      > </a
      ><a name="1954" href="StlcProp.html#1943" class="Bound"
      >M</a
      ><a name="1955"
      > </a
      ><a name="1956" class="Symbol"
      >&#8594;</a
      ><a name="1957"
      > </a
      ><a name="1958" href="StlcProp.html#1863" class="Datatype"
      >Progress</a
      ><a name="1966"
      > </a
      ><a name="1967" href="StlcProp.html#1943" class="Bound"
      >M</a
      ><a name="1968"
      >

</a
      ><a name="1970" href="StlcProp.html#1970" class="Function"
      >progress</a
      ><a name="1978"
      > </a
      ><a name="1979" class="Symbol"
      >:</a
      ><a name="1980"
      > </a
      ><a name="1981" class="Symbol"
      >&#8704;</a
      ><a name="1982"
      > </a
      ><a name="1983" class="Symbol"
      >{</a
      ><a name="1984" href="StlcProp.html#1984" class="Bound"
      >M</a
      ><a name="1985"
      > </a
      ><a name="1986" href="StlcProp.html#1986" class="Bound"
      >A</a
      ><a name="1987" class="Symbol"
      >}</a
      ><a name="1988"
      > </a
      ><a name="1989" class="Symbol"
      >&#8594;</a
      ><a name="1990"
      > </a
      ><a name="1991" href="Maps.html#10265" class="Function"
      >&#8709;</a
      ><a name="1992"
      > </a
      ><a name="1993" href="Stlc.html#3112" class="Datatype Operator"
      >&#8866;</a
      ><a name="1994"
      > </a
      ><a name="1995" href="StlcProp.html#1984" class="Bound"
      >M</a
      ><a name="1996"
      > </a
      ><a name="1997" href="Stlc.html#3112" class="Datatype Operator"
      >&#8758;</a
      ><a name="1998"
      > </a
      ><a name="1999" href="StlcProp.html#1986" class="Bound"
      >A</a
      ><a name="2000"
      > </a
      ><a name="2001" class="Symbol"
      >&#8594;</a
      ><a name="2002"
      > </a
      ><a name="2003" href="StlcProp.html#1863" class="Datatype"
      >Progress</a
      ><a name="2011"
      > </a
      ><a name="2012" href="StlcProp.html#1984" class="Bound"
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

<a name="3892" href="StlcProp.html#1970" class="Function"
      >progress</a
      ><a name="3900"
      > </a
      ><a name="3901" class="Symbol"
      >(</a
      ><a name="3902" href="Stlc.html#3156" class="InductiveConstructor"
      >Ax</a
      ><a name="3904"
      > </a
      ><a name="3905" class="Symbol"
      >())</a
      ><a name="3908"
      >
</a
      ><a name="3909" href="StlcProp.html#1970" class="Function"
      >progress</a
      ><a name="3917"
      > </a
      ><a name="3918" class="Symbol"
      >(</a
      ><a name="3919" href="Stlc.html#3210" class="InductiveConstructor"
      >&#8658;-I</a
      ><a name="3922"
      > </a
      ><a name="3923" href="StlcProp.html#3923" class="Bound"
      >&#8866;N</a
      ><a name="3925" class="Symbol"
      >)</a
      ><a name="3926"
      > </a
      ><a name="3927" class="Symbol"
      >=</a
      ><a name="3928"
      > </a
      ><a name="3929" href="StlcProp.html#1932" class="InductiveConstructor"
      >done</a
      ><a name="3933"
      > </a
      ><a name="3934" href="Stlc.html#1132" class="InductiveConstructor"
      >value-&#955;</a
      ><a name="3941"
      >
</a
      ><a name="3942" href="StlcProp.html#1970" class="Function"
      >progress</a
      ><a name="3950"
      > </a
      ><a name="3951" class="Symbol"
      >(</a
      ><a name="3952" href="Stlc.html#3287" class="InductiveConstructor"
      >&#8658;-E</a
      ><a name="3955"
      > </a
      ><a name="3956" href="StlcProp.html#3956" class="Bound"
      >&#8866;L</a
      ><a name="3958"
      > </a
      ><a name="3959" href="StlcProp.html#3959" class="Bound"
      >&#8866;M</a
      ><a name="3961" class="Symbol"
      >)</a
      ><a name="3962"
      > </a
      ><a name="3963" class="Keyword"
      >with</a
      ><a name="3967"
      > </a
      ><a name="3968" href="StlcProp.html#1970" class="Function"
      >progress</a
      ><a name="3976"
      > </a
      ><a name="3977" href="StlcProp.html#3956" class="Bound"
      >&#8866;L</a
      ><a name="3979"
      >
</a
      ><a name="3980" class="Symbol"
      >...</a
      ><a name="3983"
      > </a
      ><a name="3984" class="Symbol"
      >|</a
      ><a name="3985"
      > </a
      ><a name="3986" href="StlcProp.html#1893" class="InductiveConstructor"
      >steps</a
      ><a name="3991"
      > </a
      ><a name="3992" href="StlcProp.html#3992" class="Bound"
      >L&#10233;L&#8242;</a
      ><a name="3996"
      > </a
      ><a name="3997" class="Symbol"
      >=</a
      ><a name="3998"
      > </a
      ><a name="3999" href="StlcProp.html#1893" class="InductiveConstructor"
      >steps</a
      ><a name="4004"
      > </a
      ><a name="4005" class="Symbol"
      >(</a
      ><a name="4006" href="Stlc.html#1864" class="InductiveConstructor"
      >&#958;&#183;&#8321;</a
      ><a name="4009"
      > </a
      ><a name="4010" href="StlcProp.html#3992" class="Bound"
      >L&#10233;L&#8242;</a
      ><a name="4014" class="Symbol"
      >)</a
      ><a name="4015"
      >
</a
      ><a name="4016" class="Symbol"
      >...</a
      ><a name="4019"
      > </a
      ><a name="4020" class="Symbol"
      >|</a
      ><a name="4021"
      > </a
      ><a name="4022" href="StlcProp.html#1932" class="InductiveConstructor"
      >done</a
      ><a name="4026"
      > </a
      ><a name="4027" href="StlcProp.html#4027" class="Bound"
      >valueL</a
      ><a name="4033"
      > </a
      ><a name="4034" class="Keyword"
      >with</a
      ><a name="4038"
      > </a
      ><a name="4039" href="StlcProp.html#1970" class="Function"
      >progress</a
      ><a name="4047"
      > </a
      ><a name="4048" href="StlcProp.html#3959" class="Bound"
      >&#8866;M</a
      ><a name="4050"
      >
</a
      ><a name="4051" class="Symbol"
      >...</a
      ><a name="4054"
      > </a
      ><a name="4055" class="Symbol"
      >|</a
      ><a name="4056"
      > </a
      ><a name="4057" href="StlcProp.html#1893" class="InductiveConstructor"
      >steps</a
      ><a name="4062"
      > </a
      ><a name="4063" href="StlcProp.html#4063" class="Bound"
      >M&#10233;M&#8242;</a
      ><a name="4067"
      > </a
      ><a name="4068" class="Symbol"
      >=</a
      ><a name="4069"
      > </a
      ><a name="4070" href="StlcProp.html#1893" class="InductiveConstructor"
      >steps</a
      ><a name="4075"
      > </a
      ><a name="4076" class="Symbol"
      >(</a
      ><a name="4077" href="Stlc.html#1917" class="InductiveConstructor"
      >&#958;&#183;&#8322;</a
      ><a name="4080"
      > </a
      ><a name="4081" href="StlcProp.html#4027" class="Bound"
      >valueL</a
      ><a name="4087"
      > </a
      ><a name="4088" href="StlcProp.html#4063" class="Bound"
      >M&#10233;M&#8242;</a
      ><a name="4092" class="Symbol"
      >)</a
      ><a name="4093"
      >
</a
      ><a name="4094" class="Symbol"
      >...</a
      ><a name="4097"
      > </a
      ><a name="4098" class="Symbol"
      >|</a
      ><a name="4099"
      > </a
      ><a name="4100" href="StlcProp.html#1932" class="InductiveConstructor"
      >done</a
      ><a name="4104"
      > </a
      ><a name="4105" href="StlcProp.html#4105" class="Bound"
      >valueM</a
      ><a name="4111"
      > </a
      ><a name="4112" class="Keyword"
      >with</a
      ><a name="4116"
      > </a
      ><a name="4117" href="StlcProp.html#1355" class="Function"
      >canonical-forms</a
      ><a name="4132"
      > </a
      ><a name="4133" href="StlcProp.html#3956" class="Bound"
      >&#8866;L</a
      ><a name="4135"
      > </a
      ><a name="4136" href="StlcProp.html#4027" class="Bound"
      >valueL</a
      ><a name="4142"
      >
</a
      ><a name="4143" class="Symbol"
      >...</a
      ><a name="4146"
      > </a
      ><a name="4147" class="Symbol"
      >|</a
      ><a name="4148"
      > </a
      ><a name="4149" href="StlcProp.html#1207" class="InductiveConstructor"
      >canonical-&#955;</a
      ><a name="4160"
      > </a
      ><a name="4161" class="Symbol"
      >=</a
      ><a name="4162"
      > </a
      ><a name="4163" href="StlcProp.html#1893" class="InductiveConstructor"
      >steps</a
      ><a name="4168"
      > </a
      ><a name="4169" class="Symbol"
      >(</a
      ><a name="4170" href="Stlc.html#1794" class="InductiveConstructor"
      >&#946;&#955;&#183;</a
      ><a name="4173"
      > </a
      ><a name="4174" href="StlcProp.html#4105" class="Bound"
      >valueM</a
      ><a name="4180" class="Symbol"
      >)</a
      ><a name="4181"
      >
</a
      ><a name="4182" href="StlcProp.html#1970" class="Function"
      >progress</a
      ><a name="4190"
      > </a
      ><a name="4191" href="Stlc.html#3365" class="InductiveConstructor"
      >&#120121;-I&#8321;</a
      ><a name="4195"
      > </a
      ><a name="4196" class="Symbol"
      >=</a
      ><a name="4197"
      > </a
      ><a name="4198" href="StlcProp.html#1932" class="InductiveConstructor"
      >done</a
      ><a name="4202"
      > </a
      ><a name="4203" href="Stlc.html#1181" class="InductiveConstructor"
      >value-true</a
      ><a name="4213"
      >
</a
      ><a name="4214" href="StlcProp.html#1970" class="Function"
      >progress</a
      ><a name="4222"
      > </a
      ><a name="4223" href="Stlc.html#3399" class="InductiveConstructor"
      >&#120121;-I&#8322;</a
      ><a name="4227"
      > </a
      ><a name="4228" class="Symbol"
      >=</a
      ><a name="4229"
      > </a
      ><a name="4230" href="StlcProp.html#1932" class="InductiveConstructor"
      >done</a
      ><a name="4234"
      > </a
      ><a name="4235" href="Stlc.html#1208" class="InductiveConstructor"
      >value-false</a
      ><a name="4246"
      >
</a
      ><a name="4247" href="StlcProp.html#1970" class="Function"
      >progress</a
      ><a name="4255"
      > </a
      ><a name="4256" class="Symbol"
      >(</a
      ><a name="4257" href="Stlc.html#3434" class="InductiveConstructor"
      >&#120121;-E</a
      ><a name="4260"
      > </a
      ><a name="4261" href="StlcProp.html#4261" class="Bound"
      >&#8866;L</a
      ><a name="4263"
      > </a
      ><a name="4264" href="StlcProp.html#4264" class="Bound"
      >&#8866;M</a
      ><a name="4266"
      > </a
      ><a name="4267" href="StlcProp.html#4267" class="Bound"
      >&#8866;N</a
      ><a name="4269" class="Symbol"
      >)</a
      ><a name="4270"
      > </a
      ><a name="4271" class="Keyword"
      >with</a
      ><a name="4275"
      > </a
      ><a name="4276" href="StlcProp.html#1970" class="Function"
      >progress</a
      ><a name="4284"
      > </a
      ><a name="4285" href="StlcProp.html#4261" class="Bound"
      >&#8866;L</a
      ><a name="4287"
      >
</a
      ><a name="4288" class="Symbol"
      >...</a
      ><a name="4291"
      > </a
      ><a name="4292" class="Symbol"
      >|</a
      ><a name="4293"
      > </a
      ><a name="4294" href="StlcProp.html#1893" class="InductiveConstructor"
      >steps</a
      ><a name="4299"
      > </a
      ><a name="4300" href="StlcProp.html#4300" class="Bound"
      >L&#10233;L&#8242;</a
      ><a name="4304"
      > </a
      ><a name="4305" class="Symbol"
      >=</a
      ><a name="4306"
      > </a
      ><a name="4307" href="StlcProp.html#1893" class="InductiveConstructor"
      >steps</a
      ><a name="4312"
      > </a
      ><a name="4313" class="Symbol"
      >(</a
      ><a name="4314" href="Stlc.html#2092" class="InductiveConstructor"
      >&#958;if</a
      ><a name="4317"
      > </a
      ><a name="4318" href="StlcProp.html#4300" class="Bound"
      >L&#10233;L&#8242;</a
      ><a name="4322" class="Symbol"
      >)</a
      ><a name="4323"
      >
</a
      ><a name="4324" class="Symbol"
      >...</a
      ><a name="4327"
      > </a
      ><a name="4328" class="Symbol"
      >|</a
      ><a name="4329"
      > </a
      ><a name="4330" href="StlcProp.html#1932" class="InductiveConstructor"
      >done</a
      ><a name="4334"
      > </a
      ><a name="4335" href="StlcProp.html#4335" class="Bound"
      >valueL</a
      ><a name="4341"
      > </a
      ><a name="4342" class="Keyword"
      >with</a
      ><a name="4346"
      > </a
      ><a name="4347" href="StlcProp.html#1355" class="Function"
      >canonical-forms</a
      ><a name="4362"
      > </a
      ><a name="4363" href="StlcProp.html#4261" class="Bound"
      >&#8866;L</a
      ><a name="4365"
      > </a
      ><a name="4366" href="StlcProp.html#4335" class="Bound"
      >valueL</a
      ><a name="4372"
      >
</a
      ><a name="4373" class="Symbol"
      >...</a
      ><a name="4376"
      > </a
      ><a name="4377" class="Symbol"
      >|</a
      ><a name="4378"
      > </a
      ><a name="4379" href="StlcProp.html#1274" class="InductiveConstructor"
      >canonical-true</a
      ><a name="4393"
      > </a
      ><a name="4394" class="Symbol"
      >=</a
      ><a name="4395"
      > </a
      ><a name="4396" href="StlcProp.html#1893" class="InductiveConstructor"
      >steps</a
      ><a name="4401"
      > </a
      ><a name="4402" href="Stlc.html#1984" class="InductiveConstructor"
      >&#946;if-true</a
      ><a name="4410"
      >
</a
      ><a name="4411" class="Symbol"
      >...</a
      ><a name="4414"
      > </a
      ><a name="4415" class="Symbol"
      >|</a
      ><a name="4416"
      > </a
      ><a name="4417" href="StlcProp.html#1314" class="InductiveConstructor"
      >canonical-false</a
      ><a name="4432"
      > </a
      ><a name="4433" class="Symbol"
      >=</a
      ><a name="4434"
      > </a
      ><a name="4435" href="StlcProp.html#1893" class="InductiveConstructor"
      >steps</a
      ><a name="4440"
      > </a
      ><a name="4441" href="Stlc.html#2037" class="InductiveConstructor"
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

<a name="5098" class="Keyword"
      >postulate</a
      ><a name="5107"
      >
  </a
      ><a name="5110" href="StlcProp.html#5110" class="Postulate"
      >progress&#8242;</a
      ><a name="5119"
      > </a
      ><a name="5120" class="Symbol"
      >:</a
      ><a name="5121"
      > </a
      ><a name="5122" class="Symbol"
      >&#8704;</a
      ><a name="5123"
      > </a
      ><a name="5124" href="StlcProp.html#5124" class="Bound"
      >M</a
      ><a name="5125"
      > </a
      ><a name="5126" class="Symbol"
      >{</a
      ><a name="5127" href="StlcProp.html#5127" class="Bound"
      >A</a
      ><a name="5128" class="Symbol"
      >}</a
      ><a name="5129"
      > </a
      ><a name="5130" class="Symbol"
      >&#8594;</a
      ><a name="5131"
      > </a
      ><a name="5132" href="Maps.html#10265" class="Function"
      >&#8709;</a
      ><a name="5133"
      > </a
      ><a name="5134" href="Stlc.html#3112" class="Datatype Operator"
      >&#8866;</a
      ><a name="5135"
      > </a
      ><a name="5136" href="StlcProp.html#5124" class="Bound"
      >M</a
      ><a name="5137"
      > </a
      ><a name="5138" href="Stlc.html#3112" class="Datatype Operator"
      >&#8758;</a
      ><a name="5139"
      > </a
      ><a name="5140" href="StlcProp.html#5127" class="Bound"
      >A</a
      ><a name="5141"
      > </a
      ><a name="5142" class="Symbol"
      >&#8594;</a
      ><a name="5143"
      > </a
      ><a name="5144" href="StlcProp.html#1863" class="Datatype"
      >Progress</a
      ><a name="5152"
      > </a
      ><a name="5153" href="StlcProp.html#5124" class="Bound"
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

<a name="7600" class="Keyword"
      >data</a
      ><a name="7604"
      > </a
      ><a name="7605" href="StlcProp.html#7605" class="Datatype Operator"
      >_&#8712;_</a
      ><a name="7608"
      > </a
      ><a name="7609" class="Symbol"
      >:</a
      ><a name="7610"
      > </a
      ><a name="7611" href="Maps.html#2171" class="Datatype"
      >Id</a
      ><a name="7613"
      > </a
      ><a name="7614" class="Symbol"
      >&#8594;</a
      ><a name="7615"
      > </a
      ><a name="7616" href="Stlc.html#708" class="Datatype"
      >Term</a
      ><a name="7620"
      > </a
      ><a name="7621" class="Symbol"
      >&#8594;</a
      ><a name="7622"
      > </a
      ><a name="7623" class="PrimitiveType"
      >Set</a
      ><a name="7626"
      > </a
      ><a name="7627" class="Keyword"
      >where</a
      ><a name="7632"
      >
  </a
      ><a name="7635" href="StlcProp.html#7635" class="InductiveConstructor"
      >free-`</a
      ><a name="7641"
      >  </a
      ><a name="7643" class="Symbol"
      >:</a
      ><a name="7644"
      > </a
      ><a name="7645" class="Symbol"
      >&#8704;</a
      ><a name="7646"
      > </a
      ><a name="7647" class="Symbol"
      >{</a
      ><a name="7648" href="StlcProp.html#7648" class="Bound"
      >x</a
      ><a name="7649" class="Symbol"
      >}</a
      ><a name="7650"
      > </a
      ><a name="7651" class="Symbol"
      >&#8594;</a
      ><a name="7652"
      > </a
      ><a name="7653" href="StlcProp.html#7648" class="Bound"
      >x</a
      ><a name="7654"
      > </a
      ><a name="7655" href="StlcProp.html#7605" class="Datatype Operator"
      >&#8712;</a
      ><a name="7656"
      > </a
      ><a name="7657" href="Stlc.html#727" class="InductiveConstructor"
      >`</a
      ><a name="7658"
      > </a
      ><a name="7659" href="StlcProp.html#7648" class="Bound"
      >x</a
      ><a name="7660"
      >
  </a
      ><a name="7663" href="StlcProp.html#7663" class="InductiveConstructor"
      >free-&#955;</a
      ><a name="7669"
      >  </a
      ><a name="7671" class="Symbol"
      >:</a
      ><a name="7672"
      > </a
      ><a name="7673" class="Symbol"
      >&#8704;</a
      ><a name="7674"
      > </a
      ><a name="7675" class="Symbol"
      >{</a
      ><a name="7676" href="StlcProp.html#7676" class="Bound"
      >x</a
      ><a name="7677"
      > </a
      ><a name="7678" href="StlcProp.html#7678" class="Bound"
      >y</a
      ><a name="7679"
      > </a
      ><a name="7680" href="StlcProp.html#7680" class="Bound"
      >A</a
      ><a name="7681"
      > </a
      ><a name="7682" href="StlcProp.html#7682" class="Bound"
      >N</a
      ><a name="7683" class="Symbol"
      >}</a
      ><a name="7684"
      > </a
      ><a name="7685" class="Symbol"
      >&#8594;</a
      ><a name="7686"
      > </a
      ><a name="7687" href="StlcProp.html#7678" class="Bound"
      >y</a
      ><a name="7688"
      > </a
      ><a name="7689" href="https://agda.github.io/agda-stdlib/Relation.Binary.Core.html#4493" class="Function Operator"
      >&#8802;</a
      ><a name="7690"
      > </a
      ><a name="7691" href="StlcProp.html#7676" class="Bound"
      >x</a
      ><a name="7692"
      > </a
      ><a name="7693" class="Symbol"
      >&#8594;</a
      ><a name="7694"
      > </a
      ><a name="7695" href="StlcProp.html#7676" class="Bound"
      >x</a
      ><a name="7696"
      > </a
      ><a name="7697" href="StlcProp.html#7605" class="Datatype Operator"
      >&#8712;</a
      ><a name="7698"
      > </a
      ><a name="7699" href="StlcProp.html#7682" class="Bound"
      >N</a
      ><a name="7700"
      > </a
      ><a name="7701" class="Symbol"
      >&#8594;</a
      ><a name="7702"
      > </a
      ><a name="7703" href="StlcProp.html#7676" class="Bound"
      >x</a
      ><a name="7704"
      > </a
      ><a name="7705" href="StlcProp.html#7605" class="Datatype Operator"
      >&#8712;</a
      ><a name="7706"
      > </a
      ><a name="7707" class="Symbol"
      >(</a
      ><a name="7708" href="Stlc.html#743" class="InductiveConstructor Operator"
      >&#955;[</a
      ><a name="7710"
      > </a
      ><a name="7711" href="StlcProp.html#7678" class="Bound"
      >y</a
      ><a name="7712"
      > </a
      ><a name="7713" href="Stlc.html#743" class="InductiveConstructor Operator"
      >&#8758;</a
      ><a name="7714"
      > </a
      ><a name="7715" href="StlcProp.html#7680" class="Bound"
      >A</a
      ><a name="7716"
      > </a
      ><a name="7717" href="Stlc.html#743" class="InductiveConstructor Operator"
      >]</a
      ><a name="7718"
      > </a
      ><a name="7719" href="StlcProp.html#7682" class="Bound"
      >N</a
      ><a name="7720" class="Symbol"
      >)</a
      ><a name="7721"
      >
  </a
      ><a name="7724" href="StlcProp.html#7724" class="InductiveConstructor"
      >free-&#183;&#8321;</a
      ><a name="7731"
      > </a
      ><a name="7732" class="Symbol"
      >:</a
      ><a name="7733"
      > </a
      ><a name="7734" class="Symbol"
      >&#8704;</a
      ><a name="7735"
      > </a
      ><a name="7736" class="Symbol"
      >{</a
      ><a name="7737" href="StlcProp.html#7737" class="Bound"
      >x</a
      ><a name="7738"
      > </a
      ><a name="7739" href="StlcProp.html#7739" class="Bound"
      >L</a
      ><a name="7740"
      > </a
      ><a name="7741" href="StlcProp.html#7741" class="Bound"
      >M</a
      ><a name="7742" class="Symbol"
      >}</a
      ><a name="7743"
      > </a
      ><a name="7744" class="Symbol"
      >&#8594;</a
      ><a name="7745"
      > </a
      ><a name="7746" href="StlcProp.html#7737" class="Bound"
      >x</a
      ><a name="7747"
      > </a
      ><a name="7748" href="StlcProp.html#7605" class="Datatype Operator"
      >&#8712;</a
      ><a name="7749"
      > </a
      ><a name="7750" href="StlcProp.html#7739" class="Bound"
      >L</a
      ><a name="7751"
      > </a
      ><a name="7752" class="Symbol"
      >&#8594;</a
      ><a name="7753"
      > </a
      ><a name="7754" href="StlcProp.html#7737" class="Bound"
      >x</a
      ><a name="7755"
      > </a
      ><a name="7756" href="StlcProp.html#7605" class="Datatype Operator"
      >&#8712;</a
      ><a name="7757"
      > </a
      ><a name="7758" class="Symbol"
      >(</a
      ><a name="7759" href="StlcProp.html#7739" class="Bound"
      >L</a
      ><a name="7760"
      > </a
      ><a name="7761" href="Stlc.html#779" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="7762"
      > </a
      ><a name="7763" href="StlcProp.html#7741" class="Bound"
      >M</a
      ><a name="7764" class="Symbol"
      >)</a
      ><a name="7765"
      >
  </a
      ><a name="7768" href="StlcProp.html#7768" class="InductiveConstructor"
      >free-&#183;&#8322;</a
      ><a name="7775"
      > </a
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
      >L</a
      ><a name="7784"
      > </a
      ><a name="7785" href="StlcProp.html#7785" class="Bound"
      >M</a
      ><a name="7786" class="Symbol"
      >}</a
      ><a name="7787"
      > </a
      ><a name="7788" class="Symbol"
      >&#8594;</a
      ><a name="7789"
      > </a
      ><a name="7790" href="StlcProp.html#7781" class="Bound"
      >x</a
      ><a name="7791"
      > </a
      ><a name="7792" href="StlcProp.html#7605" class="Datatype Operator"
      >&#8712;</a
      ><a name="7793"
      > </a
      ><a name="7794" href="StlcProp.html#7785" class="Bound"
      >M</a
      ><a name="7795"
      > </a
      ><a name="7796" class="Symbol"
      >&#8594;</a
      ><a name="7797"
      > </a
      ><a name="7798" href="StlcProp.html#7781" class="Bound"
      >x</a
      ><a name="7799"
      > </a
      ><a name="7800" href="StlcProp.html#7605" class="Datatype Operator"
      >&#8712;</a
      ><a name="7801"
      > </a
      ><a name="7802" class="Symbol"
      >(</a
      ><a name="7803" href="StlcProp.html#7783" class="Bound"
      >L</a
      ><a name="7804"
      > </a
      ><a name="7805" href="Stlc.html#779" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="7806"
      > </a
      ><a name="7807" href="StlcProp.html#7785" class="Bound"
      >M</a
      ><a name="7808" class="Symbol"
      >)</a
      ><a name="7809"
      >
  </a
      ><a name="7812" href="StlcProp.html#7812" class="InductiveConstructor"
      >free-if&#8321;</a
      ><a name="7820"
      > </a
      ><a name="7821" class="Symbol"
      >:</a
      ><a name="7822"
      > </a
      ><a name="7823" class="Symbol"
      >&#8704;</a
      ><a name="7824"
      > </a
      ><a name="7825" class="Symbol"
      >{</a
      ><a name="7826" href="StlcProp.html#7826" class="Bound"
      >x</a
      ><a name="7827"
      > </a
      ><a name="7828" href="StlcProp.html#7828" class="Bound"
      >L</a
      ><a name="7829"
      > </a
      ><a name="7830" href="StlcProp.html#7830" class="Bound"
      >M</a
      ><a name="7831"
      > </a
      ><a name="7832" href="StlcProp.html#7832" class="Bound"
      >N</a
      ><a name="7833" class="Symbol"
      >}</a
      ><a name="7834"
      > </a
      ><a name="7835" class="Symbol"
      >&#8594;</a
      ><a name="7836"
      > </a
      ><a name="7837" href="StlcProp.html#7826" class="Bound"
      >x</a
      ><a name="7838"
      > </a
      ><a name="7839" href="StlcProp.html#7605" class="Datatype Operator"
      >&#8712;</a
      ><a name="7840"
      > </a
      ><a name="7841" href="StlcProp.html#7828" class="Bound"
      >L</a
      ><a name="7842"
      > </a
      ><a name="7843" class="Symbol"
      >&#8594;</a
      ><a name="7844"
      > </a
      ><a name="7845" href="StlcProp.html#7826" class="Bound"
      >x</a
      ><a name="7846"
      > </a
      ><a name="7847" href="StlcProp.html#7605" class="Datatype Operator"
      >&#8712;</a
      ><a name="7848"
      > </a
      ><a name="7849" class="Symbol"
      >(</a
      ><a name="7850" href="Stlc.html#835" class="InductiveConstructor Operator"
      >if</a
      ><a name="7852"
      > </a
      ><a name="7853" href="StlcProp.html#7828" class="Bound"
      >L</a
      ><a name="7854"
      > </a
      ><a name="7855" href="Stlc.html#835" class="InductiveConstructor Operator"
      >then</a
      ><a name="7859"
      > </a
      ><a name="7860" href="StlcProp.html#7830" class="Bound"
      >M</a
      ><a name="7861"
      > </a
      ><a name="7862" href="Stlc.html#835" class="InductiveConstructor Operator"
      >else</a
      ><a name="7866"
      > </a
      ><a name="7867" href="StlcProp.html#7832" class="Bound"
      >N</a
      ><a name="7868" class="Symbol"
      >)</a
      ><a name="7869"
      >
  </a
      ><a name="7872" href="StlcProp.html#7872" class="InductiveConstructor"
      >free-if&#8322;</a
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
      ><a name="7891"
      > </a
      ><a name="7892" href="StlcProp.html#7892" class="Bound"
      >N</a
      ><a name="7893" class="Symbol"
      >}</a
      ><a name="7894"
      > </a
      ><a name="7895" class="Symbol"
      >&#8594;</a
      ><a name="7896"
      > </a
      ><a name="7897" href="StlcProp.html#7886" class="Bound"
      >x</a
      ><a name="7898"
      > </a
      ><a name="7899" href="StlcProp.html#7605" class="Datatype Operator"
      >&#8712;</a
      ><a name="7900"
      > </a
      ><a name="7901" href="StlcProp.html#7890" class="Bound"
      >M</a
      ><a name="7902"
      > </a
      ><a name="7903" class="Symbol"
      >&#8594;</a
      ><a name="7904"
      > </a
      ><a name="7905" href="StlcProp.html#7886" class="Bound"
      >x</a
      ><a name="7906"
      > </a
      ><a name="7907" href="StlcProp.html#7605" class="Datatype Operator"
      >&#8712;</a
      ><a name="7908"
      > </a
      ><a name="7909" class="Symbol"
      >(</a
      ><a name="7910" href="Stlc.html#835" class="InductiveConstructor Operator"
      >if</a
      ><a name="7912"
      > </a
      ><a name="7913" href="StlcProp.html#7888" class="Bound"
      >L</a
      ><a name="7914"
      > </a
      ><a name="7915" href="Stlc.html#835" class="InductiveConstructor Operator"
      >then</a
      ><a name="7919"
      > </a
      ><a name="7920" href="StlcProp.html#7890" class="Bound"
      >M</a
      ><a name="7921"
      > </a
      ><a name="7922" href="Stlc.html#835" class="InductiveConstructor Operator"
      >else</a
      ><a name="7926"
      > </a
      ><a name="7927" href="StlcProp.html#7892" class="Bound"
      >N</a
      ><a name="7928" class="Symbol"
      >)</a
      ><a name="7929"
      >
  </a
      ><a name="7932" href="StlcProp.html#7932" class="InductiveConstructor"
      >free-if&#8323;</a
      ><a name="7940"
      > </a
      ><a name="7941" class="Symbol"
      >:</a
      ><a name="7942"
      > </a
      ><a name="7943" class="Symbol"
      >&#8704;</a
      ><a name="7944"
      > </a
      ><a name="7945" class="Symbol"
      >{</a
      ><a name="7946" href="StlcProp.html#7946" class="Bound"
      >x</a
      ><a name="7947"
      > </a
      ><a name="7948" href="StlcProp.html#7948" class="Bound"
      >L</a
      ><a name="7949"
      > </a
      ><a name="7950" href="StlcProp.html#7950" class="Bound"
      >M</a
      ><a name="7951"
      > </a
      ><a name="7952" href="StlcProp.html#7952" class="Bound"
      >N</a
      ><a name="7953" class="Symbol"
      >}</a
      ><a name="7954"
      > </a
      ><a name="7955" class="Symbol"
      >&#8594;</a
      ><a name="7956"
      > </a
      ><a name="7957" href="StlcProp.html#7946" class="Bound"
      >x</a
      ><a name="7958"
      > </a
      ><a name="7959" href="StlcProp.html#7605" class="Datatype Operator"
      >&#8712;</a
      ><a name="7960"
      > </a
      ><a name="7961" href="StlcProp.html#7952" class="Bound"
      >N</a
      ><a name="7962"
      > </a
      ><a name="7963" class="Symbol"
      >&#8594;</a
      ><a name="7964"
      > </a
      ><a name="7965" href="StlcProp.html#7946" class="Bound"
      >x</a
      ><a name="7966"
      > </a
      ><a name="7967" href="StlcProp.html#7605" class="Datatype Operator"
      >&#8712;</a
      ><a name="7968"
      > </a
      ><a name="7969" class="Symbol"
      >(</a
      ><a name="7970" href="Stlc.html#835" class="InductiveConstructor Operator"
      >if</a
      ><a name="7972"
      > </a
      ><a name="7973" href="StlcProp.html#7948" class="Bound"
      >L</a
      ><a name="7974"
      > </a
      ><a name="7975" href="Stlc.html#835" class="InductiveConstructor Operator"
      >then</a
      ><a name="7979"
      > </a
      ><a name="7980" href="StlcProp.html#7950" class="Bound"
      >M</a
      ><a name="7981"
      > </a
      ><a name="7982" href="Stlc.html#835" class="InductiveConstructor Operator"
      >else</a
      ><a name="7986"
      > </a
      ><a name="7987" href="StlcProp.html#7952" class="Bound"
      >N</a
      ><a name="7988" class="Symbol"
      >)</a
      >

</pre>

A term in which no variables appear free is said to be _closed_.

<pre class="Agda">

<a name="8081" href="StlcProp.html#8081" class="Function Operator"
      >_&#8713;_</a
      ><a name="8084"
      > </a
      ><a name="8085" class="Symbol"
      >:</a
      ><a name="8086"
      > </a
      ><a name="8087" href="Maps.html#2171" class="Datatype"
      >Id</a
      ><a name="8089"
      > </a
      ><a name="8090" class="Symbol"
      >&#8594;</a
      ><a name="8091"
      > </a
      ><a name="8092" href="Stlc.html#708" class="Datatype"
      >Term</a
      ><a name="8096"
      > </a
      ><a name="8097" class="Symbol"
      >&#8594;</a
      ><a name="8098"
      > </a
      ><a name="8099" class="PrimitiveType"
      >Set</a
      ><a name="8102"
      >
</a
      ><a name="8103" href="StlcProp.html#8103" class="Bound"
      >x</a
      ><a name="8104"
      > </a
      ><a name="8105" href="StlcProp.html#8081" class="Function Operator"
      >&#8713;</a
      ><a name="8106"
      > </a
      ><a name="8107" href="StlcProp.html#8107" class="Bound"
      >M</a
      ><a name="8108"
      > </a
      ><a name="8109" class="Symbol"
      >=</a
      ><a name="8110"
      > </a
      ><a name="8111" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#414" class="Function Operator"
      >&#172;</a
      ><a name="8112"
      > </a
      ><a name="8113" class="Symbol"
      >(</a
      ><a name="8114" href="StlcProp.html#8103" class="Bound"
      >x</a
      ><a name="8115"
      > </a
      ><a name="8116" href="StlcProp.html#7605" class="Datatype Operator"
      >&#8712;</a
      ><a name="8117"
      > </a
      ><a name="8118" href="StlcProp.html#8107" class="Bound"
      >M</a
      ><a name="8119" class="Symbol"
      >)</a
      ><a name="8120"
      >

</a
      ><a name="8122" href="StlcProp.html#8122" class="Function"
      >closed</a
      ><a name="8128"
      > </a
      ><a name="8129" class="Symbol"
      >:</a
      ><a name="8130"
      > </a
      ><a name="8131" href="Stlc.html#708" class="Datatype"
      >Term</a
      ><a name="8135"
      > </a
      ><a name="8136" class="Symbol"
      >&#8594;</a
      ><a name="8137"
      > </a
      ><a name="8138" class="PrimitiveType"
      >Set</a
      ><a name="8141"
      >
</a
      ><a name="8142" href="StlcProp.html#8122" class="Function"
      >closed</a
      ><a name="8148"
      > </a
      ><a name="8149" href="StlcProp.html#8149" class="Bound"
      >M</a
      ><a name="8150"
      > </a
      ><a name="8151" class="Symbol"
      >=</a
      ><a name="8152"
      > </a
      ><a name="8153" class="Symbol"
      >&#8704;</a
      ><a name="8154"
      > </a
      ><a name="8155" class="Symbol"
      >{</a
      ><a name="8156" href="StlcProp.html#8156" class="Bound"
      >x</a
      ><a name="8157" class="Symbol"
      >}</a
      ><a name="8158"
      > </a
      ><a name="8159" class="Symbol"
      >&#8594;</a
      ><a name="8160"
      > </a
      ><a name="8161" href="StlcProp.html#8156" class="Bound"
      >x</a
      ><a name="8162"
      > </a
      ><a name="8163" href="StlcProp.html#8081" class="Function Operator"
      >&#8713;</a
      ><a name="8164"
      > </a
      ><a name="8165" href="StlcProp.html#8149" class="Bound"
      >M</a
      >

</pre>

Here are proofs corresponding to the first two examples above.

<pre class="Agda">

<a name="8256" href="StlcProp.html#8256" class="Function"
      >f&#8802;x</a
      ><a name="8259"
      > </a
      ><a name="8260" class="Symbol"
      >:</a
      ><a name="8261"
      > </a
      ><a name="8262" href="Stlc.html#917" class="Function"
      >f</a
      ><a name="8263"
      > </a
      ><a name="8264" href="https://agda.github.io/agda-stdlib/Relation.Binary.Core.html#4493" class="Function Operator"
      >&#8802;</a
      ><a name="8265"
      > </a
      ><a name="8266" href="Stlc.html#919" class="Function"
      >x</a
      ><a name="8267"
      >
</a
      ><a name="8268" href="StlcProp.html#8256" class="Function"
      >f&#8802;x</a
      ><a name="8271"
      > </a
      ><a name="8272" class="Symbol"
      >()</a
      ><a name="8274"
      >

</a
      ><a name="8276" href="StlcProp.html#8276" class="Function"
      >example-free&#8321;</a
      ><a name="8289"
      > </a
      ><a name="8290" class="Symbol"
      >:</a
      ><a name="8291"
      > </a
      ><a name="8292" href="Stlc.html#919" class="Function"
      >x</a
      ><a name="8293"
      > </a
      ><a name="8294" href="StlcProp.html#7605" class="Datatype Operator"
      >&#8712;</a
      ><a name="8295"
      > </a
      ><a name="8296" class="Symbol"
      >(</a
      ><a name="8297" href="Stlc.html#743" class="InductiveConstructor Operator"
      >&#955;[</a
      ><a name="8299"
      > </a
      ><a name="8300" href="Stlc.html#917" class="Function"
      >f</a
      ><a name="8301"
      > </a
      ><a name="8302" href="Stlc.html#743" class="InductiveConstructor Operator"
      >&#8758;</a
      ><a name="8303"
      > </a
      ><a name="8304" class="Symbol"
      >(</a
      ><a name="8305" href="Stlc.html#609" class="InductiveConstructor"
      >&#120121;</a
      ><a name="8306"
      > </a
      ><a name="8307" href="Stlc.html#620" class="InductiveConstructor Operator"
      >&#8658;</a
      ><a name="8308"
      > </a
      ><a name="8309" href="Stlc.html#609" class="InductiveConstructor"
      >&#120121;</a
      ><a name="8310" class="Symbol"
      >)</a
      ><a name="8311"
      > </a
      ><a name="8312" href="Stlc.html#743" class="InductiveConstructor Operator"
      >]</a
      ><a name="8313"
      > </a
      ><a name="8314" href="Stlc.html#727" class="InductiveConstructor"
      >`</a
      ><a name="8315"
      > </a
      ><a name="8316" href="Stlc.html#917" class="Function"
      >f</a
      ><a name="8317"
      > </a
      ><a name="8318" href="Stlc.html#779" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="8319"
      > </a
      ><a name="8320" href="Stlc.html#727" class="InductiveConstructor"
      >`</a
      ><a name="8321"
      > </a
      ><a name="8322" href="Stlc.html#919" class="Function"
      >x</a
      ><a name="8323" class="Symbol"
      >)</a
      ><a name="8324"
      >
</a
      ><a name="8325" href="StlcProp.html#8276" class="Function"
      >example-free&#8321;</a
      ><a name="8338"
      > </a
      ><a name="8339" class="Symbol"
      >=</a
      ><a name="8340"
      > </a
      ><a name="8341" href="StlcProp.html#7663" class="InductiveConstructor"
      >free-&#955;</a
      ><a name="8347"
      > </a
      ><a name="8348" href="StlcProp.html#8256" class="Function"
      >f&#8802;x</a
      ><a name="8351"
      > </a
      ><a name="8352" class="Symbol"
      >(</a
      ><a name="8353" href="StlcProp.html#7768" class="InductiveConstructor"
      >free-&#183;&#8322;</a
      ><a name="8360"
      > </a
      ><a name="8361" href="StlcProp.html#7635" class="InductiveConstructor"
      >free-`</a
      ><a name="8367" class="Symbol"
      >)</a
      ><a name="8368"
      >

</a
      ><a name="8370" href="StlcProp.html#8370" class="Function"
      >example-free&#8322;</a
      ><a name="8383"
      > </a
      ><a name="8384" class="Symbol"
      >:</a
      ><a name="8385"
      > </a
      ><a name="8386" href="Stlc.html#917" class="Function"
      >f</a
      ><a name="8387"
      > </a
      ><a name="8388" href="StlcProp.html#8081" class="Function Operator"
      >&#8713;</a
      ><a name="8389"
      > </a
      ><a name="8390" class="Symbol"
      >(</a
      ><a name="8391" href="Stlc.html#743" class="InductiveConstructor Operator"
      >&#955;[</a
      ><a name="8393"
      > </a
      ><a name="8394" href="Stlc.html#917" class="Function"
      >f</a
      ><a name="8395"
      > </a
      ><a name="8396" href="Stlc.html#743" class="InductiveConstructor Operator"
      >&#8758;</a
      ><a name="8397"
      > </a
      ><a name="8398" class="Symbol"
      >(</a
      ><a name="8399" href="Stlc.html#609" class="InductiveConstructor"
      >&#120121;</a
      ><a name="8400"
      > </a
      ><a name="8401" href="Stlc.html#620" class="InductiveConstructor Operator"
      >&#8658;</a
      ><a name="8402"
      > </a
      ><a name="8403" href="Stlc.html#609" class="InductiveConstructor"
      >&#120121;</a
      ><a name="8404" class="Symbol"
      >)</a
      ><a name="8405"
      > </a
      ><a name="8406" href="Stlc.html#743" class="InductiveConstructor Operator"
      >]</a
      ><a name="8407"
      > </a
      ><a name="8408" href="Stlc.html#727" class="InductiveConstructor"
      >`</a
      ><a name="8409"
      > </a
      ><a name="8410" href="Stlc.html#917" class="Function"
      >f</a
      ><a name="8411"
      > </a
      ><a name="8412" href="Stlc.html#779" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="8413"
      > </a
      ><a name="8414" href="Stlc.html#727" class="InductiveConstructor"
      >`</a
      ><a name="8415"
      > </a
      ><a name="8416" href="Stlc.html#919" class="Function"
      >x</a
      ><a name="8417" class="Symbol"
      >)</a
      ><a name="8418"
      >
</a
      ><a name="8419" href="StlcProp.html#8370" class="Function"
      >example-free&#8322;</a
      ><a name="8432"
      > </a
      ><a name="8433" class="Symbol"
      >(</a
      ><a name="8434" href="StlcProp.html#7663" class="InductiveConstructor"
      >free-&#955;</a
      ><a name="8440"
      > </a
      ><a name="8441" href="StlcProp.html#8441" class="Bound"
      >f&#8802;f</a
      ><a name="8444"
      > </a
      ><a name="8445" class="Symbol"
      >_)</a
      ><a name="8447"
      > </a
      ><a name="8448" class="Symbol"
      >=</a
      ><a name="8449"
      > </a
      ><a name="8450" href="StlcProp.html#8441" class="Bound"
      >f&#8802;f</a
      ><a name="8453"
      > </a
      ><a name="8454" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      >

</pre>


#### Exercise: 1 star (free-in)
Prove formally the remaining examples given above.

<pre class="Agda">

<a name="8569" class="Keyword"
      >postulate</a
      ><a name="8578"
      >
  </a
      ><a name="8581" href="StlcProp.html#8581" class="Postulate"
      >example-free&#8323;</a
      ><a name="8594"
      > </a
      ><a name="8595" class="Symbol"
      >:</a
      ><a name="8596"
      > </a
      ><a name="8597" href="Stlc.html#919" class="Function"
      >x</a
      ><a name="8598"
      > </a
      ><a name="8599" href="StlcProp.html#7605" class="Datatype Operator"
      >&#8712;</a
      ><a name="8600"
      > </a
      ><a name="8601" class="Symbol"
      >((</a
      ><a name="8603" href="Stlc.html#743" class="InductiveConstructor Operator"
      >&#955;[</a
      ><a name="8605"
      > </a
      ><a name="8606" href="Stlc.html#917" class="Function"
      >f</a
      ><a name="8607"
      > </a
      ><a name="8608" href="Stlc.html#743" class="InductiveConstructor Operator"
      >&#8758;</a
      ><a name="8609"
      > </a
      ><a name="8610" class="Symbol"
      >(</a
      ><a name="8611" href="Stlc.html#609" class="InductiveConstructor"
      >&#120121;</a
      ><a name="8612"
      > </a
      ><a name="8613" href="Stlc.html#620" class="InductiveConstructor Operator"
      >&#8658;</a
      ><a name="8614"
      > </a
      ><a name="8615" href="Stlc.html#609" class="InductiveConstructor"
      >&#120121;</a
      ><a name="8616" class="Symbol"
      >)</a
      ><a name="8617"
      > </a
      ><a name="8618" href="Stlc.html#743" class="InductiveConstructor Operator"
      >]</a
      ><a name="8619"
      > </a
      ><a name="8620" href="Stlc.html#727" class="InductiveConstructor"
      >`</a
      ><a name="8621"
      > </a
      ><a name="8622" href="Stlc.html#917" class="Function"
      >f</a
      ><a name="8623"
      > </a
      ><a name="8624" href="Stlc.html#779" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="8625"
      > </a
      ><a name="8626" href="Stlc.html#727" class="InductiveConstructor"
      >`</a
      ><a name="8627"
      > </a
      ><a name="8628" href="Stlc.html#919" class="Function"
      >x</a
      ><a name="8629" class="Symbol"
      >)</a
      ><a name="8630"
      > </a
      ><a name="8631" href="Stlc.html#779" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="8632"
      > </a
      ><a name="8633" href="Stlc.html#727" class="InductiveConstructor"
      >`</a
      ><a name="8634"
      > </a
      ><a name="8635" href="Stlc.html#917" class="Function"
      >f</a
      ><a name="8636" class="Symbol"
      >)</a
      ><a name="8637"
      >
  </a
      ><a name="8640" href="StlcProp.html#8640" class="Postulate"
      >example-free&#8324;</a
      ><a name="8653"
      > </a
      ><a name="8654" class="Symbol"
      >:</a
      ><a name="8655"
      > </a
      ><a name="8656" href="Stlc.html#917" class="Function"
      >f</a
      ><a name="8657"
      > </a
      ><a name="8658" href="StlcProp.html#7605" class="Datatype Operator"
      >&#8712;</a
      ><a name="8659"
      > </a
      ><a name="8660" class="Symbol"
      >((</a
      ><a name="8662" href="Stlc.html#743" class="InductiveConstructor Operator"
      >&#955;[</a
      ><a name="8664"
      > </a
      ><a name="8665" href="Stlc.html#917" class="Function"
      >f</a
      ><a name="8666"
      > </a
      ><a name="8667" href="Stlc.html#743" class="InductiveConstructor Operator"
      >&#8758;</a
      ><a name="8668"
      > </a
      ><a name="8669" class="Symbol"
      >(</a
      ><a name="8670" href="Stlc.html#609" class="InductiveConstructor"
      >&#120121;</a
      ><a name="8671"
      > </a
      ><a name="8672" href="Stlc.html#620" class="InductiveConstructor Operator"
      >&#8658;</a
      ><a name="8673"
      > </a
      ><a name="8674" href="Stlc.html#609" class="InductiveConstructor"
      >&#120121;</a
      ><a name="8675" class="Symbol"
      >)</a
      ><a name="8676"
      > </a
      ><a name="8677" href="Stlc.html#743" class="InductiveConstructor Operator"
      >]</a
      ><a name="8678"
      > </a
      ><a name="8679" href="Stlc.html#727" class="InductiveConstructor"
      >`</a
      ><a name="8680"
      > </a
      ><a name="8681" href="Stlc.html#917" class="Function"
      >f</a
      ><a name="8682"
      > </a
      ><a name="8683" href="Stlc.html#779" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="8684"
      > </a
      ><a name="8685" href="Stlc.html#727" class="InductiveConstructor"
      >`</a
      ><a name="8686"
      > </a
      ><a name="8687" href="Stlc.html#919" class="Function"
      >x</a
      ><a name="8688" class="Symbol"
      >)</a
      ><a name="8689"
      > </a
      ><a name="8690" href="Stlc.html#779" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="8691"
      > </a
      ><a name="8692" href="Stlc.html#727" class="InductiveConstructor"
      >`</a
      ><a name="8693"
      > </a
      ><a name="8694" href="Stlc.html#917" class="Function"
      >f</a
      ><a name="8695" class="Symbol"
      >)</a
      ><a name="8696"
      >
  </a
      ><a name="8699" href="StlcProp.html#8699" class="Postulate"
      >example-free&#8325;</a
      ><a name="8712"
      > </a
      ><a name="8713" class="Symbol"
      >:</a
      ><a name="8714"
      > </a
      ><a name="8715" href="Stlc.html#919" class="Function"
      >x</a
      ><a name="8716"
      > </a
      ><a name="8717" href="StlcProp.html#8081" class="Function Operator"
      >&#8713;</a
      ><a name="8718"
      > </a
      ><a name="8719" class="Symbol"
      >(</a
      ><a name="8720" href="Stlc.html#743" class="InductiveConstructor Operator"
      >&#955;[</a
      ><a name="8722"
      > </a
      ><a name="8723" href="Stlc.html#917" class="Function"
      >f</a
      ><a name="8724"
      > </a
      ><a name="8725" href="Stlc.html#743" class="InductiveConstructor Operator"
      >&#8758;</a
      ><a name="8726"
      > </a
      ><a name="8727" class="Symbol"
      >(</a
      ><a name="8728" href="Stlc.html#609" class="InductiveConstructor"
      >&#120121;</a
      ><a name="8729"
      > </a
      ><a name="8730" href="Stlc.html#620" class="InductiveConstructor Operator"
      >&#8658;</a
      ><a name="8731"
      > </a
      ><a name="8732" href="Stlc.html#609" class="InductiveConstructor"
      >&#120121;</a
      ><a name="8733" class="Symbol"
      >)</a
      ><a name="8734"
      > </a
      ><a name="8735" href="Stlc.html#743" class="InductiveConstructor Operator"
      >]</a
      ><a name="8736"
      > </a
      ><a name="8737" href="Stlc.html#743" class="InductiveConstructor Operator"
      >&#955;[</a
      ><a name="8739"
      > </a
      ><a name="8740" href="Stlc.html#919" class="Function"
      >x</a
      ><a name="8741"
      > </a
      ><a name="8742" href="Stlc.html#743" class="InductiveConstructor Operator"
      >&#8758;</a
      ><a name="8743"
      > </a
      ><a name="8744" href="Stlc.html#609" class="InductiveConstructor"
      >&#120121;</a
      ><a name="8745"
      > </a
      ><a name="8746" href="Stlc.html#743" class="InductiveConstructor Operator"
      >]</a
      ><a name="8747"
      > </a
      ><a name="8748" href="Stlc.html#727" class="InductiveConstructor"
      >`</a
      ><a name="8749"
      > </a
      ><a name="8750" href="Stlc.html#917" class="Function"
      >f</a
      ><a name="8751"
      > </a
      ><a name="8752" href="Stlc.html#779" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="8753"
      > </a
      ><a name="8754" href="Stlc.html#727" class="InductiveConstructor"
      >`</a
      ><a name="8755"
      > </a
      ><a name="8756" href="Stlc.html#919" class="Function"
      >x</a
      ><a name="8757" class="Symbol"
      >)</a
      ><a name="8758"
      >
  </a
      ><a name="8761" href="StlcProp.html#8761" class="Postulate"
      >example-free&#8326;</a
      ><a name="8774"
      > </a
      ><a name="8775" class="Symbol"
      >:</a
      ><a name="8776"
      > </a
      ><a name="8777" href="Stlc.html#917" class="Function"
      >f</a
      ><a name="8778"
      > </a
      ><a name="8779" href="StlcProp.html#8081" class="Function Operator"
      >&#8713;</a
      ><a name="8780"
      > </a
      ><a name="8781" class="Symbol"
      >(</a
      ><a name="8782" href="Stlc.html#743" class="InductiveConstructor Operator"
      >&#955;[</a
      ><a name="8784"
      > </a
      ><a name="8785" href="Stlc.html#917" class="Function"
      >f</a
      ><a name="8786"
      > </a
      ><a name="8787" href="Stlc.html#743" class="InductiveConstructor Operator"
      >&#8758;</a
      ><a name="8788"
      > </a
      ><a name="8789" class="Symbol"
      >(</a
      ><a name="8790" href="Stlc.html#609" class="InductiveConstructor"
      >&#120121;</a
      ><a name="8791"
      > </a
      ><a name="8792" href="Stlc.html#620" class="InductiveConstructor Operator"
      >&#8658;</a
      ><a name="8793"
      > </a
      ><a name="8794" href="Stlc.html#609" class="InductiveConstructor"
      >&#120121;</a
      ><a name="8795" class="Symbol"
      >)</a
      ><a name="8796"
      > </a
      ><a name="8797" href="Stlc.html#743" class="InductiveConstructor Operator"
      >]</a
      ><a name="8798"
      > </a
      ><a name="8799" href="Stlc.html#743" class="InductiveConstructor Operator"
      >&#955;[</a
      ><a name="8801"
      > </a
      ><a name="8802" href="Stlc.html#919" class="Function"
      >x</a
      ><a name="8803"
      > </a
      ><a name="8804" href="Stlc.html#743" class="InductiveConstructor Operator"
      >&#8758;</a
      ><a name="8805"
      > </a
      ><a name="8806" href="Stlc.html#609" class="InductiveConstructor"
      >&#120121;</a
      ><a name="8807"
      > </a
      ><a name="8808" href="Stlc.html#743" class="InductiveConstructor Operator"
      >]</a
      ><a name="8809"
      > </a
      ><a name="8810" href="Stlc.html#727" class="InductiveConstructor"
      >`</a
      ><a name="8811"
      > </a
      ><a name="8812" href="Stlc.html#917" class="Function"
      >f</a
      ><a name="8813"
      > </a
      ><a name="8814" href="Stlc.html#779" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="8815"
      > </a
      ><a name="8816" href="Stlc.html#727" class="InductiveConstructor"
      >`</a
      ><a name="8817"
      > </a
      ><a name="8818" href="Stlc.html#919" class="Function"
      >x</a
      ><a name="8819" class="Symbol"
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

<a name="9302" href="StlcProp.html#9302" class="Function"
      >free-lemma</a
      ><a name="9312"
      > </a
      ><a name="9313" class="Symbol"
      >:</a
      ><a name="9314"
      > </a
      ><a name="9315" class="Symbol"
      >&#8704;</a
      ><a name="9316"
      > </a
      ><a name="9317" class="Symbol"
      >{</a
      ><a name="9318" href="StlcProp.html#9318" class="Bound"
      >x</a
      ><a name="9319"
      > </a
      ><a name="9320" href="StlcProp.html#9320" class="Bound"
      >M</a
      ><a name="9321"
      > </a
      ><a name="9322" href="StlcProp.html#9322" class="Bound"
      >A</a
      ><a name="9323"
      > </a
      ><a name="9324" href="StlcProp.html#9324" class="Bound"
      >&#915;</a
      ><a name="9325" class="Symbol"
      >}</a
      ><a name="9326"
      > </a
      ><a name="9327" class="Symbol"
      >&#8594;</a
      ><a name="9328"
      > </a
      ><a name="9329" href="StlcProp.html#9318" class="Bound"
      >x</a
      ><a name="9330"
      > </a
      ><a name="9331" href="StlcProp.html#7605" class="Datatype Operator"
      >&#8712;</a
      ><a name="9332"
      > </a
      ><a name="9333" href="StlcProp.html#9320" class="Bound"
      >M</a
      ><a name="9334"
      > </a
      ><a name="9335" class="Symbol"
      >&#8594;</a
      ><a name="9336"
      > </a
      ><a name="9337" href="StlcProp.html#9324" class="Bound"
      >&#915;</a
      ><a name="9338"
      > </a
      ><a name="9339" href="Stlc.html#3112" class="Datatype Operator"
      >&#8866;</a
      ><a name="9340"
      > </a
      ><a name="9341" href="StlcProp.html#9320" class="Bound"
      >M</a
      ><a name="9342"
      > </a
      ><a name="9343" href="Stlc.html#3112" class="Datatype Operator"
      >&#8758;</a
      ><a name="9344"
      > </a
      ><a name="9345" href="StlcProp.html#9322" class="Bound"
      >A</a
      ><a name="9346"
      > </a
      ><a name="9347" class="Symbol"
      >&#8594;</a
      ><a name="9348"
      > </a
      ><a name="9349" href="https://agda.github.io/agda-stdlib/Data.Product.html#823" class="Function"
      >&#8707;</a
      ><a name="9350"
      > </a
      ><a name="9351" class="Symbol"
      >&#955;</a
      ><a name="9352"
      > </a
      ><a name="9353" href="StlcProp.html#9353" class="Bound"
      >B</a
      ><a name="9354"
      > </a
      ><a name="9355" class="Symbol"
      >&#8594;</a
      ><a name="9356"
      > </a
      ><a name="9357" href="StlcProp.html#9324" class="Bound"
      >&#915;</a
      ><a name="9358"
      > </a
      ><a name="9359" href="StlcProp.html#9318" class="Bound"
      >x</a
      ><a name="9360"
      > </a
      ><a name="9361" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="9362"
      > </a
      ><a name="9363" href="https://agda.github.io/agda-stdlib/Data.Maybe.Base.html#373" class="InductiveConstructor"
      >just</a
      ><a name="9367"
      > </a
      ><a name="9368" href="StlcProp.html#9353" class="Bound"
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

<a name="10811" href="StlcProp.html#9302" class="Function"
      >free-lemma</a
      ><a name="10821"
      > </a
      ><a name="10822" href="StlcProp.html#7635" class="InductiveConstructor"
      >free-`</a
      ><a name="10828"
      > </a
      ><a name="10829" class="Symbol"
      >(</a
      ><a name="10830" href="Stlc.html#3156" class="InductiveConstructor"
      >Ax</a
      ><a name="10832"
      > </a
      ><a name="10833" href="StlcProp.html#10833" class="Bound"
      >&#915;x&#8801;A</a
      ><a name="10837" class="Symbol"
      >)</a
      ><a name="10838"
      > </a
      ><a name="10839" class="Symbol"
      >=</a
      ><a name="10840"
      > </a
      ><a name="10841" class="Symbol"
      >(_</a
      ><a name="10843"
      > </a
      ><a name="10844" href="https://agda.github.io/agda-stdlib/Data.Product.html#509" class="InductiveConstructor Operator"
      >,</a
      ><a name="10845"
      > </a
      ><a name="10846" href="StlcProp.html#10833" class="Bound"
      >&#915;x&#8801;A</a
      ><a name="10850" class="Symbol"
      >)</a
      ><a name="10851"
      >
</a
      ><a name="10852" href="StlcProp.html#9302" class="Function"
      >free-lemma</a
      ><a name="10862"
      > </a
      ><a name="10863" class="Symbol"
      >(</a
      ><a name="10864" href="StlcProp.html#7724" class="InductiveConstructor"
      >free-&#183;&#8321;</a
      ><a name="10871"
      > </a
      ><a name="10872" href="StlcProp.html#10872" class="Bound"
      >x&#8712;L</a
      ><a name="10875" class="Symbol"
      >)</a
      ><a name="10876"
      > </a
      ><a name="10877" class="Symbol"
      >(</a
      ><a name="10878" href="Stlc.html#3287" class="InductiveConstructor"
      >&#8658;-E</a
      ><a name="10881"
      > </a
      ><a name="10882" href="StlcProp.html#10882" class="Bound"
      >&#8866;L</a
      ><a name="10884"
      > </a
      ><a name="10885" href="StlcProp.html#10885" class="Bound"
      >&#8866;M</a
      ><a name="10887" class="Symbol"
      >)</a
      ><a name="10888"
      > </a
      ><a name="10889" class="Symbol"
      >=</a
      ><a name="10890"
      > </a
      ><a name="10891" href="StlcProp.html#9302" class="Function"
      >free-lemma</a
      ><a name="10901"
      > </a
      ><a name="10902" href="StlcProp.html#10872" class="Bound"
      >x&#8712;L</a
      ><a name="10905"
      > </a
      ><a name="10906" href="StlcProp.html#10882" class="Bound"
      >&#8866;L</a
      ><a name="10908"
      >
</a
      ><a name="10909" href="StlcProp.html#9302" class="Function"
      >free-lemma</a
      ><a name="10919"
      > </a
      ><a name="10920" class="Symbol"
      >(</a
      ><a name="10921" href="StlcProp.html#7768" class="InductiveConstructor"
      >free-&#183;&#8322;</a
      ><a name="10928"
      > </a
      ><a name="10929" href="StlcProp.html#10929" class="Bound"
      >x&#8712;M</a
      ><a name="10932" class="Symbol"
      >)</a
      ><a name="10933"
      > </a
      ><a name="10934" class="Symbol"
      >(</a
      ><a name="10935" href="Stlc.html#3287" class="InductiveConstructor"
      >&#8658;-E</a
      ><a name="10938"
      > </a
      ><a name="10939" href="StlcProp.html#10939" class="Bound"
      >&#8866;L</a
      ><a name="10941"
      > </a
      ><a name="10942" href="StlcProp.html#10942" class="Bound"
      >&#8866;M</a
      ><a name="10944" class="Symbol"
      >)</a
      ><a name="10945"
      > </a
      ><a name="10946" class="Symbol"
      >=</a
      ><a name="10947"
      > </a
      ><a name="10948" href="StlcProp.html#9302" class="Function"
      >free-lemma</a
      ><a name="10958"
      > </a
      ><a name="10959" href="StlcProp.html#10929" class="Bound"
      >x&#8712;M</a
      ><a name="10962"
      > </a
      ><a name="10963" href="StlcProp.html#10942" class="Bound"
      >&#8866;M</a
      ><a name="10965"
      >
</a
      ><a name="10966" href="StlcProp.html#9302" class="Function"
      >free-lemma</a
      ><a name="10976"
      > </a
      ><a name="10977" class="Symbol"
      >(</a
      ><a name="10978" href="StlcProp.html#7812" class="InductiveConstructor"
      >free-if&#8321;</a
      ><a name="10986"
      > </a
      ><a name="10987" href="StlcProp.html#10987" class="Bound"
      >x&#8712;L</a
      ><a name="10990" class="Symbol"
      >)</a
      ><a name="10991"
      > </a
      ><a name="10992" class="Symbol"
      >(</a
      ><a name="10993" href="Stlc.html#3434" class="InductiveConstructor"
      >&#120121;-E</a
      ><a name="10996"
      > </a
      ><a name="10997" href="StlcProp.html#10997" class="Bound"
      >&#8866;L</a
      ><a name="10999"
      > </a
      ><a name="11000" href="StlcProp.html#11000" class="Bound"
      >&#8866;M</a
      ><a name="11002"
      > </a
      ><a name="11003" href="StlcProp.html#11003" class="Bound"
      >&#8866;N</a
      ><a name="11005" class="Symbol"
      >)</a
      ><a name="11006"
      > </a
      ><a name="11007" class="Symbol"
      >=</a
      ><a name="11008"
      > </a
      ><a name="11009" href="StlcProp.html#9302" class="Function"
      >free-lemma</a
      ><a name="11019"
      > </a
      ><a name="11020" href="StlcProp.html#10987" class="Bound"
      >x&#8712;L</a
      ><a name="11023"
      > </a
      ><a name="11024" href="StlcProp.html#10997" class="Bound"
      >&#8866;L</a
      ><a name="11026"
      >
</a
      ><a name="11027" href="StlcProp.html#9302" class="Function"
      >free-lemma</a
      ><a name="11037"
      > </a
      ><a name="11038" class="Symbol"
      >(</a
      ><a name="11039" href="StlcProp.html#7872" class="InductiveConstructor"
      >free-if&#8322;</a
      ><a name="11047"
      > </a
      ><a name="11048" href="StlcProp.html#11048" class="Bound"
      >x&#8712;M</a
      ><a name="11051" class="Symbol"
      >)</a
      ><a name="11052"
      > </a
      ><a name="11053" class="Symbol"
      >(</a
      ><a name="11054" href="Stlc.html#3434" class="InductiveConstructor"
      >&#120121;-E</a
      ><a name="11057"
      > </a
      ><a name="11058" href="StlcProp.html#11058" class="Bound"
      >&#8866;L</a
      ><a name="11060"
      > </a
      ><a name="11061" href="StlcProp.html#11061" class="Bound"
      >&#8866;M</a
      ><a name="11063"
      > </a
      ><a name="11064" href="StlcProp.html#11064" class="Bound"
      >&#8866;N</a
      ><a name="11066" class="Symbol"
      >)</a
      ><a name="11067"
      > </a
      ><a name="11068" class="Symbol"
      >=</a
      ><a name="11069"
      > </a
      ><a name="11070" href="StlcProp.html#9302" class="Function"
      >free-lemma</a
      ><a name="11080"
      > </a
      ><a name="11081" href="StlcProp.html#11048" class="Bound"
      >x&#8712;M</a
      ><a name="11084"
      > </a
      ><a name="11085" href="StlcProp.html#11061" class="Bound"
      >&#8866;M</a
      ><a name="11087"
      >
</a
      ><a name="11088" href="StlcProp.html#9302" class="Function"
      >free-lemma</a
      ><a name="11098"
      > </a
      ><a name="11099" class="Symbol"
      >(</a
      ><a name="11100" href="StlcProp.html#7932" class="InductiveConstructor"
      >free-if&#8323;</a
      ><a name="11108"
      > </a
      ><a name="11109" href="StlcProp.html#11109" class="Bound"
      >x&#8712;N</a
      ><a name="11112" class="Symbol"
      >)</a
      ><a name="11113"
      > </a
      ><a name="11114" class="Symbol"
      >(</a
      ><a name="11115" href="Stlc.html#3434" class="InductiveConstructor"
      >&#120121;-E</a
      ><a name="11118"
      > </a
      ><a name="11119" href="StlcProp.html#11119" class="Bound"
      >&#8866;L</a
      ><a name="11121"
      > </a
      ><a name="11122" href="StlcProp.html#11122" class="Bound"
      >&#8866;M</a
      ><a name="11124"
      > </a
      ><a name="11125" href="StlcProp.html#11125" class="Bound"
      >&#8866;N</a
      ><a name="11127" class="Symbol"
      >)</a
      ><a name="11128"
      > </a
      ><a name="11129" class="Symbol"
      >=</a
      ><a name="11130"
      > </a
      ><a name="11131" href="StlcProp.html#9302" class="Function"
      >free-lemma</a
      ><a name="11141"
      > </a
      ><a name="11142" href="StlcProp.html#11109" class="Bound"
      >x&#8712;N</a
      ><a name="11145"
      > </a
      ><a name="11146" href="StlcProp.html#11125" class="Bound"
      >&#8866;N</a
      ><a name="11148"
      >
</a
      ><a name="11149" href="StlcProp.html#9302" class="Function"
      >free-lemma</a
      ><a name="11159"
      > </a
      ><a name="11160" class="Symbol"
      >(</a
      ><a name="11161" href="StlcProp.html#7663" class="InductiveConstructor"
      >free-&#955;</a
      ><a name="11167"
      > </a
      ><a name="11168" class="Symbol"
      >{</a
      ><a name="11169" href="StlcProp.html#11169" class="Bound"
      >x</a
      ><a name="11170" class="Symbol"
      >}</a
      ><a name="11171"
      > </a
      ><a name="11172" class="Symbol"
      >{</a
      ><a name="11173" href="StlcProp.html#11173" class="Bound"
      >y</a
      ><a name="11174" class="Symbol"
      >}</a
      ><a name="11175"
      > </a
      ><a name="11176" href="StlcProp.html#11176" class="Bound"
      >y&#8802;x</a
      ><a name="11179"
      > </a
      ><a name="11180" href="StlcProp.html#11180" class="Bound"
      >x&#8712;N</a
      ><a name="11183" class="Symbol"
      >)</a
      ><a name="11184"
      > </a
      ><a name="11185" class="Symbol"
      >(</a
      ><a name="11186" href="Stlc.html#3210" class="InductiveConstructor"
      >&#8658;-I</a
      ><a name="11189"
      > </a
      ><a name="11190" href="StlcProp.html#11190" class="Bound"
      >&#8866;N</a
      ><a name="11192" class="Symbol"
      >)</a
      ><a name="11193"
      > </a
      ><a name="11194" class="Keyword"
      >with</a
      ><a name="11198"
      > </a
      ><a name="11199" href="StlcProp.html#9302" class="Function"
      >free-lemma</a
      ><a name="11209"
      > </a
      ><a name="11210" href="StlcProp.html#11180" class="Bound"
      >x&#8712;N</a
      ><a name="11213"
      > </a
      ><a name="11214" href="StlcProp.html#11190" class="Bound"
      >&#8866;N</a
      ><a name="11216"
      >
</a
      ><a name="11217" class="Symbol"
      >...</a
      ><a name="11220"
      > </a
      ><a name="11221" class="Symbol"
      >|</a
      ><a name="11222"
      > </a
      ><a name="11223" href="StlcProp.html#11223" class="Bound"
      >&#915;x&#8801;C</a
      ><a name="11227"
      > </a
      ><a name="11228" class="Keyword"
      >with</a
      ><a name="11232"
      > </a
      ><a name="11233" href="StlcProp.html#11173" class="Bound"
      >y</a
      ><a name="11234"
      > </a
      ><a name="11235" href="Maps.html#2509" class="Function Operator"
      >&#8799;</a
      ><a name="11236"
      > </a
      ><a name="11237" href="StlcProp.html#11169" class="Bound"
      >x</a
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
      ><a name="11245" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#520" class="InductiveConstructor"
      >yes</a
      ><a name="11248"
      > </a
      ><a name="11249" href="StlcProp.html#11249" class="Bound"
      >y&#8801;x</a
      ><a name="11252"
      > </a
      ><a name="11253" class="Symbol"
      >=</a
      ><a name="11254"
      > </a
      ><a name="11255" href="https://agda.github.io/agda-stdlib/Data.Empty.html#348" class="Function"
      >&#8869;-elim</a
      ><a name="11261"
      > </a
      ><a name="11262" class="Symbol"
      >(</a
      ><a name="11263" href="StlcProp.html#11176" class="Bound"
      >y&#8802;x</a
      ><a name="11266"
      > </a
      ><a name="11267" href="StlcProp.html#11249" class="Bound"
      >y&#8801;x</a
      ><a name="11270" class="Symbol"
      >)</a
      ><a name="11271"
      >
</a
      ><a name="11272" class="Symbol"
      >...</a
      ><a name="11275"
      > </a
      ><a name="11276" class="Symbol"
      >|</a
      ><a name="11277"
      > </a
      ><a name="11278" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#547" class="InductiveConstructor"
      >no</a
      ><a name="11280"
      >  </a
      ><a name="11282" class="Symbol"
      >_</a
      ><a name="11283"
      >   </a
      ><a name="11286" class="Symbol"
      >=</a
      ><a name="11287"
      > </a
      ><a name="11288" href="StlcProp.html#11223" class="Bound"
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

<a name="11725" class="Keyword"
      >postulate</a
      ><a name="11734"
      >
  </a
      ><a name="11737" href="StlcProp.html#11737" class="Postulate"
      >&#8709;&#8866;-closed</a
      ><a name="11746"
      > </a
      ><a name="11747" class="Symbol"
      >:</a
      ><a name="11748"
      > </a
      ><a name="11749" class="Symbol"
      >&#8704;</a
      ><a name="11750"
      > </a
      ><a name="11751" class="Symbol"
      >{</a
      ><a name="11752" href="StlcProp.html#11752" class="Bound"
      >M</a
      ><a name="11753"
      > </a
      ><a name="11754" href="StlcProp.html#11754" class="Bound"
      >A</a
      ><a name="11755" class="Symbol"
      >}</a
      ><a name="11756"
      > </a
      ><a name="11757" class="Symbol"
      >&#8594;</a
      ><a name="11758"
      > </a
      ><a name="11759" href="Maps.html#10265" class="Function"
      >&#8709;</a
      ><a name="11760"
      > </a
      ><a name="11761" href="Stlc.html#3112" class="Datatype Operator"
      >&#8866;</a
      ><a name="11762"
      > </a
      ><a name="11763" href="StlcProp.html#11752" class="Bound"
      >M</a
      ><a name="11764"
      > </a
      ><a name="11765" href="Stlc.html#3112" class="Datatype Operator"
      >&#8758;</a
      ><a name="11766"
      > </a
      ><a name="11767" href="StlcProp.html#11754" class="Bound"
      >A</a
      ><a name="11768"
      > </a
      ><a name="11769" class="Symbol"
      >&#8594;</a
      ><a name="11770"
      > </a
      ><a name="11771" href="StlcProp.html#8122" class="Function"
      >closed</a
      ><a name="11777"
      > </a
      ><a name="11778" href="StlcProp.html#11752" class="Bound"
      >M</a
      >

</pre>

<div class="hidden">
<pre class="Agda">

<a name="11826" href="StlcProp.html#11826" class="Function"
      >contradiction</a
      ><a name="11839"
      > </a
      ><a name="11840" class="Symbol"
      >:</a
      ><a name="11841"
      > </a
      ><a name="11842" class="Symbol"
      >&#8704;</a
      ><a name="11843"
      > </a
      ><a name="11844" class="Symbol"
      >{</a
      ><a name="11845" href="StlcProp.html#11845" class="Bound"
      >X</a
      ><a name="11846"
      > </a
      ><a name="11847" class="Symbol"
      >:</a
      ><a name="11848"
      > </a
      ><a name="11849" class="PrimitiveType"
      >Set</a
      ><a name="11852" class="Symbol"
      >}</a
      ><a name="11853"
      > </a
      ><a name="11854" class="Symbol"
      >&#8594;</a
      ><a name="11855"
      > </a
      ><a name="11856" class="Symbol"
      >&#8704;</a
      ><a name="11857"
      > </a
      ><a name="11858" class="Symbol"
      >{</a
      ><a name="11859" href="StlcProp.html#11859" class="Bound"
      >x</a
      ><a name="11860"
      > </a
      ><a name="11861" class="Symbol"
      >:</a
      ><a name="11862"
      > </a
      ><a name="11863" href="StlcProp.html#11845" class="Bound"
      >X</a
      ><a name="11864" class="Symbol"
      >}</a
      ><a name="11865"
      > </a
      ><a name="11866" class="Symbol"
      >&#8594;</a
      ><a name="11867"
      > </a
      ><a name="11868" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#414" class="Function Operator"
      >&#172;</a
      ><a name="11869"
      > </a
      ><a name="11870" class="Symbol"
      >(</a
      ><a name="11871" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >_&#8801;_</a
      ><a name="11874"
      > </a
      ><a name="11875" class="Symbol"
      >{</a
      ><a name="11876" class="Argument"
      >A</a
      ><a name="11877"
      > </a
      ><a name="11878" class="Symbol"
      >=</a
      ><a name="11879"
      > </a
      ><a name="11880" href="https://agda.github.io/agda-stdlib/Data.Maybe.Base.html#335" class="Datatype"
      >Maybe</a
      ><a name="11885"
      > </a
      ><a name="11886" href="StlcProp.html#11845" class="Bound"
      >X</a
      ><a name="11887" class="Symbol"
      >}</a
      ><a name="11888"
      > </a
      ><a name="11889" class="Symbol"
      >(</a
      ><a name="11890" href="https://agda.github.io/agda-stdlib/Data.Maybe.Base.html#373" class="InductiveConstructor"
      >just</a
      ><a name="11894"
      > </a
      ><a name="11895" href="StlcProp.html#11859" class="Bound"
      >x</a
      ><a name="11896" class="Symbol"
      >)</a
      ><a name="11897"
      > </a
      ><a name="11898" href="https://agda.github.io/agda-stdlib/Data.Maybe.Base.html#403" class="InductiveConstructor"
      >nothing</a
      ><a name="11905" class="Symbol"
      >)</a
      ><a name="11906"
      >
</a
      ><a name="11907" href="StlcProp.html#11826" class="Function"
      >contradiction</a
      ><a name="11920"
      > </a
      ><a name="11921" class="Symbol"
      >()</a
      ><a name="11923"
      >

</a
      ><a name="11925" href="StlcProp.html#11925" class="Function"
      >&#8709;&#8866;-closed&#8242;</a
      ><a name="11935"
      > </a
      ><a name="11936" class="Symbol"
      >:</a
      ><a name="11937"
      > </a
      ><a name="11938" class="Symbol"
      >&#8704;</a
      ><a name="11939"
      > </a
      ><a name="11940" class="Symbol"
      >{</a
      ><a name="11941" href="StlcProp.html#11941" class="Bound"
      >M</a
      ><a name="11942"
      > </a
      ><a name="11943" href="StlcProp.html#11943" class="Bound"
      >A</a
      ><a name="11944" class="Symbol"
      >}</a
      ><a name="11945"
      > </a
      ><a name="11946" class="Symbol"
      >&#8594;</a
      ><a name="11947"
      > </a
      ><a name="11948" href="Maps.html#10265" class="Function"
      >&#8709;</a
      ><a name="11949"
      > </a
      ><a name="11950" href="Stlc.html#3112" class="Datatype Operator"
      >&#8866;</a
      ><a name="11951"
      > </a
      ><a name="11952" href="StlcProp.html#11941" class="Bound"
      >M</a
      ><a name="11953"
      > </a
      ><a name="11954" href="Stlc.html#3112" class="Datatype Operator"
      >&#8758;</a
      ><a name="11955"
      > </a
      ><a name="11956" href="StlcProp.html#11943" class="Bound"
      >A</a
      ><a name="11957"
      > </a
      ><a name="11958" class="Symbol"
      >&#8594;</a
      ><a name="11959"
      > </a
      ><a name="11960" href="StlcProp.html#8122" class="Function"
      >closed</a
      ><a name="11966"
      > </a
      ><a name="11967" href="StlcProp.html#11941" class="Bound"
      >M</a
      ><a name="11968"
      >
</a
      ><a name="11969" href="StlcProp.html#11925" class="Function"
      >&#8709;&#8866;-closed&#8242;</a
      ><a name="11979"
      > </a
      ><a name="11980" class="Symbol"
      >{</a
      ><a name="11981" href="StlcProp.html#11981" class="Bound"
      >M</a
      ><a name="11982" class="Symbol"
      >}</a
      ><a name="11983"
      > </a
      ><a name="11984" class="Symbol"
      >{</a
      ><a name="11985" href="StlcProp.html#11985" class="Bound"
      >A</a
      ><a name="11986" class="Symbol"
      >}</a
      ><a name="11987"
      > </a
      ><a name="11988" href="StlcProp.html#11988" class="Bound"
      >&#8866;M</a
      ><a name="11990"
      > </a
      ><a name="11991" class="Symbol"
      >{</a
      ><a name="11992" href="StlcProp.html#11992" class="Bound"
      >x</a
      ><a name="11993" class="Symbol"
      >}</a
      ><a name="11994"
      > </a
      ><a name="11995" href="StlcProp.html#11995" class="Bound"
      >x&#8712;M</a
      ><a name="11998"
      > </a
      ><a name="11999" class="Keyword"
      >with</a
      ><a name="12003"
      > </a
      ><a name="12004" href="StlcProp.html#9302" class="Function"
      >free-lemma</a
      ><a name="12014"
      > </a
      ><a name="12015" href="StlcProp.html#11995" class="Bound"
      >x&#8712;M</a
      ><a name="12018"
      > </a
      ><a name="12019" href="StlcProp.html#11988" class="Bound"
      >&#8866;M</a
      ><a name="12021"
      >
</a
      ><a name="12022" class="Symbol"
      >...</a
      ><a name="12025"
      > </a
      ><a name="12026" class="Symbol"
      >|</a
      ><a name="12027"
      > </a
      ><a name="12028" class="Symbol"
      >(</a
      ><a name="12029" href="StlcProp.html#12029" class="Bound"
      >B</a
      ><a name="12030"
      > </a
      ><a name="12031" href="https://agda.github.io/agda-stdlib/Data.Product.html#509" class="InductiveConstructor Operator"
      >,</a
      ><a name="12032"
      > </a
      ><a name="12033" href="StlcProp.html#12033" class="Bound"
      >&#8709;x&#8801;B</a
      ><a name="12037" class="Symbol"
      >)</a
      ><a name="12038"
      > </a
      ><a name="12039" class="Symbol"
      >=</a
      ><a name="12040"
      > </a
      ><a name="12041" href="StlcProp.html#11826" class="Function"
      >contradiction</a
      ><a name="12054"
      > </a
      ><a name="12055" class="Symbol"
      >(</a
      ><a name="12056" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.Core.html#632" class="Function"
      >trans</a
      ><a name="12061"
      > </a
      ><a name="12062" class="Symbol"
      >(</a
      ><a name="12063" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.Core.html#565" class="Function"
      >sym</a
      ><a name="12066"
      > </a
      ><a name="12067" href="StlcProp.html#12033" class="Bound"
      >&#8709;x&#8801;B</a
      ><a name="12071" class="Symbol"
      >)</a
      ><a name="12072"
      > </a
      ><a name="12073" class="Symbol"
      >(</a
      ><a name="12074" href="Maps.html#10573" class="Function"
      >apply-&#8709;</a
      ><a name="12081"
      > </a
      ><a name="12082" href="StlcProp.html#11992" class="Bound"
      >x</a
      ><a name="12083" class="Symbol"
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

<a name="12437" href="StlcProp.html#12437" class="Function"
      >context-lemma</a
      ><a name="12450"
      > </a
      ><a name="12451" class="Symbol"
      >:</a
      ><a name="12452"
      > </a
      ><a name="12453" class="Symbol"
      >&#8704;</a
      ><a name="12454"
      > </a
      ><a name="12455" class="Symbol"
      >{</a
      ><a name="12456" href="StlcProp.html#12456" class="Bound"
      >&#915;</a
      ><a name="12457"
      > </a
      ><a name="12458" href="StlcProp.html#12458" class="Bound"
      >&#915;&#8242;</a
      ><a name="12460"
      > </a
      ><a name="12461" href="StlcProp.html#12461" class="Bound"
      >M</a
      ><a name="12462"
      > </a
      ><a name="12463" href="StlcProp.html#12463" class="Bound"
      >A</a
      ><a name="12464" class="Symbol"
      >}</a
      ><a name="12465"
      >
        </a
      ><a name="12474" class="Symbol"
      >&#8594;</a
      ><a name="12475"
      > </a
      ><a name="12476" class="Symbol"
      >(&#8704;</a
      ><a name="12478"
      > </a
      ><a name="12479" class="Symbol"
      >{</a
      ><a name="12480" href="StlcProp.html#12480" class="Bound"
      >x</a
      ><a name="12481" class="Symbol"
      >}</a
      ><a name="12482"
      > </a
      ><a name="12483" class="Symbol"
      >&#8594;</a
      ><a name="12484"
      > </a
      ><a name="12485" href="StlcProp.html#12480" class="Bound"
      >x</a
      ><a name="12486"
      > </a
      ><a name="12487" href="StlcProp.html#7605" class="Datatype Operator"
      >&#8712;</a
      ><a name="12488"
      > </a
      ><a name="12489" href="StlcProp.html#12461" class="Bound"
      >M</a
      ><a name="12490"
      > </a
      ><a name="12491" class="Symbol"
      >&#8594;</a
      ><a name="12492"
      > </a
      ><a name="12493" href="StlcProp.html#12456" class="Bound"
      >&#915;</a
      ><a name="12494"
      > </a
      ><a name="12495" href="StlcProp.html#12480" class="Bound"
      >x</a
      ><a name="12496"
      > </a
      ><a name="12497" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="12498"
      > </a
      ><a name="12499" href="StlcProp.html#12458" class="Bound"
      >&#915;&#8242;</a
      ><a name="12501"
      > </a
      ><a name="12502" href="StlcProp.html#12480" class="Bound"
      >x</a
      ><a name="12503" class="Symbol"
      >)</a
      ><a name="12504"
      >
        </a
      ><a name="12513" class="Symbol"
      >&#8594;</a
      ><a name="12514"
      > </a
      ><a name="12515" href="StlcProp.html#12456" class="Bound"
      >&#915;</a
      ><a name="12516"
      >  </a
      ><a name="12518" href="Stlc.html#3112" class="Datatype Operator"
      >&#8866;</a
      ><a name="12519"
      > </a
      ><a name="12520" href="StlcProp.html#12461" class="Bound"
      >M</a
      ><a name="12521"
      > </a
      ><a name="12522" href="Stlc.html#3112" class="Datatype Operator"
      >&#8758;</a
      ><a name="12523"
      > </a
      ><a name="12524" href="StlcProp.html#12463" class="Bound"
      >A</a
      ><a name="12525"
      >
        </a
      ><a name="12534" class="Symbol"
      >&#8594;</a
      ><a name="12535"
      > </a
      ><a name="12536" href="StlcProp.html#12458" class="Bound"
      >&#915;&#8242;</a
      ><a name="12538"
      > </a
      ><a name="12539" href="Stlc.html#3112" class="Datatype Operator"
      >&#8866;</a
      ><a name="12540"
      > </a
      ><a name="12541" href="StlcProp.html#12461" class="Bound"
      >M</a
      ><a name="12542"
      > </a
      ><a name="12543" href="Stlc.html#3112" class="Datatype Operator"
      >&#8758;</a
      ><a name="12544"
      > </a
      ><a name="12545" href="StlcProp.html#12463" class="Bound"
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

<a name="14718" href="StlcProp.html#12437" class="Function"
      >context-lemma</a
      ><a name="14731"
      > </a
      ><a name="14732" href="StlcProp.html#14732" class="Bound"
      >&#915;~&#915;&#8242;</a
      ><a name="14736"
      > </a
      ><a name="14737" class="Symbol"
      >(</a
      ><a name="14738" href="Stlc.html#3156" class="InductiveConstructor"
      >Ax</a
      ><a name="14740"
      > </a
      ><a name="14741" href="StlcProp.html#14741" class="Bound"
      >&#915;x&#8801;A</a
      ><a name="14745" class="Symbol"
      >)</a
      ><a name="14746"
      > </a
      ><a name="14747" class="Keyword"
      >rewrite</a
      ><a name="14754"
      > </a
      ><a name="14755" class="Symbol"
      >(</a
      ><a name="14756" href="StlcProp.html#14732" class="Bound"
      >&#915;~&#915;&#8242;</a
      ><a name="14760"
      > </a
      ><a name="14761" href="StlcProp.html#7635" class="InductiveConstructor"
      >free-`</a
      ><a name="14767" class="Symbol"
      >)</a
      ><a name="14768"
      > </a
      ><a name="14769" class="Symbol"
      >=</a
      ><a name="14770"
      > </a
      ><a name="14771" href="Stlc.html#3156" class="InductiveConstructor"
      >Ax</a
      ><a name="14773"
      > </a
      ><a name="14774" href="StlcProp.html#14741" class="Bound"
      >&#915;x&#8801;A</a
      ><a name="14778"
      >
</a
      ><a name="14779" href="StlcProp.html#12437" class="Function"
      >context-lemma</a
      ><a name="14792"
      > </a
      ><a name="14793" class="Symbol"
      >{</a
      ><a name="14794" href="StlcProp.html#14794" class="Bound"
      >&#915;</a
      ><a name="14795" class="Symbol"
      >}</a
      ><a name="14796"
      > </a
      ><a name="14797" class="Symbol"
      >{</a
      ><a name="14798" href="StlcProp.html#14798" class="Bound"
      >&#915;&#8242;</a
      ><a name="14800" class="Symbol"
      >}</a
      ><a name="14801"
      > </a
      ><a name="14802" class="Symbol"
      >{</a
      ><a name="14803" href="Stlc.html#743" class="InductiveConstructor Operator"
      >&#955;[</a
      ><a name="14805"
      > </a
      ><a name="14806" href="StlcProp.html#14806" class="Bound"
      >x</a
      ><a name="14807"
      > </a
      ><a name="14808" href="Stlc.html#743" class="InductiveConstructor Operator"
      >&#8758;</a
      ><a name="14809"
      > </a
      ><a name="14810" href="StlcProp.html#14810" class="Bound"
      >A</a
      ><a name="14811"
      > </a
      ><a name="14812" href="Stlc.html#743" class="InductiveConstructor Operator"
      >]</a
      ><a name="14813"
      > </a
      ><a name="14814" href="StlcProp.html#14814" class="Bound"
      >N</a
      ><a name="14815" class="Symbol"
      >}</a
      ><a name="14816"
      > </a
      ><a name="14817" href="StlcProp.html#14817" class="Bound"
      >&#915;~&#915;&#8242;</a
      ><a name="14821"
      > </a
      ><a name="14822" class="Symbol"
      >(</a
      ><a name="14823" href="Stlc.html#3210" class="InductiveConstructor"
      >&#8658;-I</a
      ><a name="14826"
      > </a
      ><a name="14827" href="StlcProp.html#14827" class="Bound"
      >&#8866;N</a
      ><a name="14829" class="Symbol"
      >)</a
      ><a name="14830"
      > </a
      ><a name="14831" class="Symbol"
      >=</a
      ><a name="14832"
      > </a
      ><a name="14833" href="Stlc.html#3210" class="InductiveConstructor"
      >&#8658;-I</a
      ><a name="14836"
      > </a
      ><a name="14837" class="Symbol"
      >(</a
      ><a name="14838" href="StlcProp.html#12437" class="Function"
      >context-lemma</a
      ><a name="14851"
      > </a
      ><a name="14852" href="StlcProp.html#14873" class="Function"
      >&#915;x~&#915;&#8242;x</a
      ><a name="14858"
      > </a
      ><a name="14859" href="StlcProp.html#14827" class="Bound"
      >&#8866;N</a
      ><a name="14861" class="Symbol"
      >)</a
      ><a name="14862"
      >
  </a
      ><a name="14865" class="Keyword"
      >where</a
      ><a name="14870"
      >
  </a
      ><a name="14873" href="StlcProp.html#14873" class="Function"
      >&#915;x~&#915;&#8242;x</a
      ><a name="14879"
      > </a
      ><a name="14880" class="Symbol"
      >:</a
      ><a name="14881"
      > </a
      ><a name="14882" class="Symbol"
      >&#8704;</a
      ><a name="14883"
      > </a
      ><a name="14884" class="Symbol"
      >{</a
      ><a name="14885" href="StlcProp.html#14885" class="Bound"
      >y</a
      ><a name="14886" class="Symbol"
      >}</a
      ><a name="14887"
      > </a
      ><a name="14888" class="Symbol"
      >&#8594;</a
      ><a name="14889"
      > </a
      ><a name="14890" href="StlcProp.html#14885" class="Bound"
      >y</a
      ><a name="14891"
      > </a
      ><a name="14892" href="StlcProp.html#7605" class="Datatype Operator"
      >&#8712;</a
      ><a name="14893"
      > </a
      ><a name="14894" href="StlcProp.html#14814" class="Bound"
      >N</a
      ><a name="14895"
      > </a
      ><a name="14896" class="Symbol"
      >&#8594;</a
      ><a name="14897"
      > </a
      ><a name="14898" class="Symbol"
      >(</a
      ><a name="14899" href="StlcProp.html#14794" class="Bound"
      >&#915;</a
      ><a name="14900"
      > </a
      ><a name="14901" href="Maps.html#10368" class="Function Operator"
      >,</a
      ><a name="14902"
      > </a
      ><a name="14903" href="StlcProp.html#14806" class="Bound"
      >x</a
      ><a name="14904"
      > </a
      ><a name="14905" href="Maps.html#10368" class="Function Operator"
      >&#8758;</a
      ><a name="14906"
      > </a
      ><a name="14907" href="StlcProp.html#14810" class="Bound"
      >A</a
      ><a name="14908" class="Symbol"
      >)</a
      ><a name="14909"
      > </a
      ><a name="14910" href="StlcProp.html#14885" class="Bound"
      >y</a
      ><a name="14911"
      > </a
      ><a name="14912" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="14913"
      > </a
      ><a name="14914" class="Symbol"
      >(</a
      ><a name="14915" href="StlcProp.html#14798" class="Bound"
      >&#915;&#8242;</a
      ><a name="14917"
      > </a
      ><a name="14918" href="Maps.html#10368" class="Function Operator"
      >,</a
      ><a name="14919"
      > </a
      ><a name="14920" href="StlcProp.html#14806" class="Bound"
      >x</a
      ><a name="14921"
      > </a
      ><a name="14922" href="Maps.html#10368" class="Function Operator"
      >&#8758;</a
      ><a name="14923"
      > </a
      ><a name="14924" href="StlcProp.html#14810" class="Bound"
      >A</a
      ><a name="14925" class="Symbol"
      >)</a
      ><a name="14926"
      > </a
      ><a name="14927" href="StlcProp.html#14885" class="Bound"
      >y</a
      ><a name="14928"
      >
  </a
      ><a name="14931" href="StlcProp.html#14873" class="Function"
      >&#915;x~&#915;&#8242;x</a
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
      ><a name="14942" href="StlcProp.html#14942" class="Bound"
      >y&#8712;N</a
      ><a name="14945"
      > </a
      ><a name="14946" class="Keyword"
      >with</a
      ><a name="14950"
      > </a
      ><a name="14951" href="StlcProp.html#14806" class="Bound"
      >x</a
      ><a name="14952"
      > </a
      ><a name="14953" href="Maps.html#2509" class="Function Operator"
      >&#8799;</a
      ><a name="14954"
      > </a
      ><a name="14955" href="StlcProp.html#14939" class="Bound"
      >y</a
      ><a name="14956"
      >
  </a
      ><a name="14959" class="Symbol"
      >...</a
      ><a name="14962"
      > </a
      ><a name="14963" class="Symbol"
      >|</a
      ><a name="14964"
      > </a
      ><a name="14965" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#520" class="InductiveConstructor"
      >yes</a
      ><a name="14968"
      > </a
      ><a name="14969" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="14973"
      > </a
      ><a name="14974" class="Symbol"
      >=</a
      ><a name="14975"
      > </a
      ><a name="14976" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="14980"
      >
  </a
      ><a name="14983" class="Symbol"
      >...</a
      ><a name="14986"
      > </a
      ><a name="14987" class="Symbol"
      >|</a
      ><a name="14988"
      > </a
      ><a name="14989" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#547" class="InductiveConstructor"
      >no</a
      ><a name="14991"
      >  </a
      ><a name="14993" href="StlcProp.html#14993" class="Bound"
      >x&#8802;y</a
      ><a name="14996"
      >  </a
      ><a name="14998" class="Symbol"
      >=</a
      ><a name="14999"
      > </a
      ><a name="15000" href="StlcProp.html#14817" class="Bound"
      >&#915;~&#915;&#8242;</a
      ><a name="15004"
      > </a
      ><a name="15005" class="Symbol"
      >(</a
      ><a name="15006" href="StlcProp.html#7663" class="InductiveConstructor"
      >free-&#955;</a
      ><a name="15012"
      > </a
      ><a name="15013" href="StlcProp.html#14993" class="Bound"
      >x&#8802;y</a
      ><a name="15016"
      > </a
      ><a name="15017" href="StlcProp.html#14942" class="Bound"
      >y&#8712;N</a
      ><a name="15020" class="Symbol"
      >)</a
      ><a name="15021"
      >
</a
      ><a name="15022" href="StlcProp.html#12437" class="Function"
      >context-lemma</a
      ><a name="15035"
      > </a
      ><a name="15036" href="StlcProp.html#15036" class="Bound"
      >&#915;~&#915;&#8242;</a
      ><a name="15040"
      > </a
      ><a name="15041" class="Symbol"
      >(</a
      ><a name="15042" href="Stlc.html#3287" class="InductiveConstructor"
      >&#8658;-E</a
      ><a name="15045"
      > </a
      ><a name="15046" href="StlcProp.html#15046" class="Bound"
      >&#8866;L</a
      ><a name="15048"
      > </a
      ><a name="15049" href="StlcProp.html#15049" class="Bound"
      >&#8866;M</a
      ><a name="15051" class="Symbol"
      >)</a
      ><a name="15052"
      > </a
      ><a name="15053" class="Symbol"
      >=</a
      ><a name="15054"
      > </a
      ><a name="15055" href="Stlc.html#3287" class="InductiveConstructor"
      >&#8658;-E</a
      ><a name="15058"
      > </a
      ><a name="15059" class="Symbol"
      >(</a
      ><a name="15060" href="StlcProp.html#12437" class="Function"
      >context-lemma</a
      ><a name="15073"
      > </a
      ><a name="15074" class="Symbol"
      >(</a
      ><a name="15075" href="StlcProp.html#15036" class="Bound"
      >&#915;~&#915;&#8242;</a
      ><a name="15079"
      > </a
      ><a name="15080" href="https://agda.github.io/agda-stdlib/Function.html#713" class="Function Operator"
      >&#8728;</a
      ><a name="15081"
      > </a
      ><a name="15082" href="StlcProp.html#7724" class="InductiveConstructor"
      >free-&#183;&#8321;</a
      ><a name="15089" class="Symbol"
      >)</a
      ><a name="15090"
      >  </a
      ><a name="15092" href="StlcProp.html#15046" class="Bound"
      >&#8866;L</a
      ><a name="15094" class="Symbol"
      >)</a
      ><a name="15095"
      > </a
      ><a name="15096" class="Symbol"
      >(</a
      ><a name="15097" href="StlcProp.html#12437" class="Function"
      >context-lemma</a
      ><a name="15110"
      > </a
      ><a name="15111" class="Symbol"
      >(</a
      ><a name="15112" href="StlcProp.html#15036" class="Bound"
      >&#915;~&#915;&#8242;</a
      ><a name="15116"
      > </a
      ><a name="15117" href="https://agda.github.io/agda-stdlib/Function.html#713" class="Function Operator"
      >&#8728;</a
      ><a name="15118"
      > </a
      ><a name="15119" href="StlcProp.html#7768" class="InductiveConstructor"
      >free-&#183;&#8322;</a
      ><a name="15126" class="Symbol"
      >)</a
      ><a name="15127"
      > </a
      ><a name="15128" href="StlcProp.html#15049" class="Bound"
      >&#8866;M</a
      ><a name="15130" class="Symbol"
      >)</a
      ><a name="15131"
      > 
</a
      ><a name="15133" href="StlcProp.html#12437" class="Function"
      >context-lemma</a
      ><a name="15146"
      > </a
      ><a name="15147" href="StlcProp.html#15147" class="Bound"
      >&#915;~&#915;&#8242;</a
      ><a name="15151"
      > </a
      ><a name="15152" href="Stlc.html#3365" class="InductiveConstructor"
      >&#120121;-I&#8321;</a
      ><a name="15156"
      > </a
      ><a name="15157" class="Symbol"
      >=</a
      ><a name="15158"
      > </a
      ><a name="15159" href="Stlc.html#3365" class="InductiveConstructor"
      >&#120121;-I&#8321;</a
      ><a name="15163"
      >
</a
      ><a name="15164" href="StlcProp.html#12437" class="Function"
      >context-lemma</a
      ><a name="15177"
      > </a
      ><a name="15178" href="StlcProp.html#15178" class="Bound"
      >&#915;~&#915;&#8242;</a
      ><a name="15182"
      > </a
      ><a name="15183" href="Stlc.html#3399" class="InductiveConstructor"
      >&#120121;-I&#8322;</a
      ><a name="15187"
      > </a
      ><a name="15188" class="Symbol"
      >=</a
      ><a name="15189"
      > </a
      ><a name="15190" href="Stlc.html#3399" class="InductiveConstructor"
      >&#120121;-I&#8322;</a
      ><a name="15194"
      >
</a
      ><a name="15195" href="StlcProp.html#12437" class="Function"
      >context-lemma</a
      ><a name="15208"
      > </a
      ><a name="15209" href="StlcProp.html#15209" class="Bound"
      >&#915;~&#915;&#8242;</a
      ><a name="15213"
      > </a
      ><a name="15214" class="Symbol"
      >(</a
      ><a name="15215" href="Stlc.html#3434" class="InductiveConstructor"
      >&#120121;-E</a
      ><a name="15218"
      > </a
      ><a name="15219" href="StlcProp.html#15219" class="Bound"
      >&#8866;L</a
      ><a name="15221"
      > </a
      ><a name="15222" href="StlcProp.html#15222" class="Bound"
      >&#8866;M</a
      ><a name="15224"
      > </a
      ><a name="15225" href="StlcProp.html#15225" class="Bound"
      >&#8866;N</a
      ><a name="15227" class="Symbol"
      >)</a
      ><a name="15228"
      >
  </a
      ><a name="15231" class="Symbol"
      >=</a
      ><a name="15232"
      > </a
      ><a name="15233" href="Stlc.html#3434" class="InductiveConstructor"
      >&#120121;-E</a
      ><a name="15236"
      > </a
      ><a name="15237" class="Symbol"
      >(</a
      ><a name="15238" href="StlcProp.html#12437" class="Function"
      >context-lemma</a
      ><a name="15251"
      > </a
      ><a name="15252" class="Symbol"
      >(</a
      ><a name="15253" href="StlcProp.html#15209" class="Bound"
      >&#915;~&#915;&#8242;</a
      ><a name="15257"
      > </a
      ><a name="15258" href="https://agda.github.io/agda-stdlib/Function.html#713" class="Function Operator"
      >&#8728;</a
      ><a name="15259"
      > </a
      ><a name="15260" href="StlcProp.html#7812" class="InductiveConstructor"
      >free-if&#8321;</a
      ><a name="15268" class="Symbol"
      >)</a
      ><a name="15269"
      > </a
      ><a name="15270" href="StlcProp.html#15219" class="Bound"
      >&#8866;L</a
      ><a name="15272" class="Symbol"
      >)</a
      ><a name="15273"
      > </a
      ><a name="15274" class="Symbol"
      >(</a
      ><a name="15275" href="StlcProp.html#12437" class="Function"
      >context-lemma</a
      ><a name="15288"
      > </a
      ><a name="15289" class="Symbol"
      >(</a
      ><a name="15290" href="StlcProp.html#15209" class="Bound"
      >&#915;~&#915;&#8242;</a
      ><a name="15294"
      > </a
      ><a name="15295" href="https://agda.github.io/agda-stdlib/Function.html#713" class="Function Operator"
      >&#8728;</a
      ><a name="15296"
      > </a
      ><a name="15297" href="StlcProp.html#7872" class="InductiveConstructor"
      >free-if&#8322;</a
      ><a name="15305" class="Symbol"
      >)</a
      ><a name="15306"
      > </a
      ><a name="15307" href="StlcProp.html#15222" class="Bound"
      >&#8866;M</a
      ><a name="15309" class="Symbol"
      >)</a
      ><a name="15310"
      > </a
      ><a name="15311" class="Symbol"
      >(</a
      ><a name="15312" href="StlcProp.html#12437" class="Function"
      >context-lemma</a
      ><a name="15325"
      > </a
      ><a name="15326" class="Symbol"
      >(</a
      ><a name="15327" href="StlcProp.html#15209" class="Bound"
      >&#915;~&#915;&#8242;</a
      ><a name="15331"
      > </a
      ><a name="15332" href="https://agda.github.io/agda-stdlib/Function.html#713" class="Function Operator"
      >&#8728;</a
      ><a name="15333"
      > </a
      ><a name="15334" href="StlcProp.html#7932" class="InductiveConstructor"
      >free-if&#8323;</a
      ><a name="15342" class="Symbol"
      >)</a
      ><a name="15343"
      > </a
      ><a name="15344" href="StlcProp.html#15225" class="Bound"
      >&#8866;N</a
      ><a name="15346" class="Symbol"
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

<a name="16045" href="StlcProp.html#16045" class="Function"
      >preservation-[:=]</a
      ><a name="16062"
      > </a
      ><a name="16063" class="Symbol"
      >:</a
      ><a name="16064"
      > </a
      ><a name="16065" class="Symbol"
      >&#8704;</a
      ><a name="16066"
      > </a
      ><a name="16067" class="Symbol"
      >{</a
      ><a name="16068" href="StlcProp.html#16068" class="Bound"
      >&#915;</a
      ><a name="16069"
      > </a
      ><a name="16070" href="StlcProp.html#16070" class="Bound"
      >x</a
      ><a name="16071"
      > </a
      ><a name="16072" href="StlcProp.html#16072" class="Bound"
      >A</a
      ><a name="16073"
      > </a
      ><a name="16074" href="StlcProp.html#16074" class="Bound"
      >N</a
      ><a name="16075"
      > </a
      ><a name="16076" href="StlcProp.html#16076" class="Bound"
      >B</a
      ><a name="16077"
      > </a
      ><a name="16078" href="StlcProp.html#16078" class="Bound"
      >V</a
      ><a name="16079" class="Symbol"
      >}</a
      ><a name="16080"
      >
                 </a
      ><a name="16098" class="Symbol"
      >&#8594;</a
      ><a name="16099"
      > </a
      ><a name="16100" class="Symbol"
      >(</a
      ><a name="16101" href="StlcProp.html#16068" class="Bound"
      >&#915;</a
      ><a name="16102"
      > </a
      ><a name="16103" href="Maps.html#10368" class="Function Operator"
      >,</a
      ><a name="16104"
      > </a
      ><a name="16105" href="StlcProp.html#16070" class="Bound"
      >x</a
      ><a name="16106"
      > </a
      ><a name="16107" href="Maps.html#10368" class="Function Operator"
      >&#8758;</a
      ><a name="16108"
      > </a
      ><a name="16109" href="StlcProp.html#16072" class="Bound"
      >A</a
      ><a name="16110" class="Symbol"
      >)</a
      ><a name="16111"
      > </a
      ><a name="16112" href="Stlc.html#3112" class="Datatype Operator"
      >&#8866;</a
      ><a name="16113"
      > </a
      ><a name="16114" href="StlcProp.html#16074" class="Bound"
      >N</a
      ><a name="16115"
      > </a
      ><a name="16116" href="Stlc.html#3112" class="Datatype Operator"
      >&#8758;</a
      ><a name="16117"
      > </a
      ><a name="16118" href="StlcProp.html#16076" class="Bound"
      >B</a
      ><a name="16119"
      >
                 </a
      ><a name="16137" class="Symbol"
      >&#8594;</a
      ><a name="16138"
      > </a
      ><a name="16139" href="Maps.html#10265" class="Function"
      >&#8709;</a
      ><a name="16140"
      > </a
      ><a name="16141" href="Stlc.html#3112" class="Datatype Operator"
      >&#8866;</a
      ><a name="16142"
      > </a
      ><a name="16143" href="StlcProp.html#16078" class="Bound"
      >V</a
      ><a name="16144"
      > </a
      ><a name="16145" href="Stlc.html#3112" class="Datatype Operator"
      >&#8758;</a
      ><a name="16146"
      > </a
      ><a name="16147" href="StlcProp.html#16072" class="Bound"
      >A</a
      ><a name="16148"
      >
                 </a
      ><a name="16166" class="Symbol"
      >&#8594;</a
      ><a name="16167"
      > </a
      ><a name="16168" href="StlcProp.html#16068" class="Bound"
      >&#915;</a
      ><a name="16169"
      > </a
      ><a name="16170" href="Stlc.html#3112" class="Datatype Operator"
      >&#8866;</a
      ><a name="16171"
      > </a
      ><a name="16172" class="Symbol"
      >(</a
      ><a name="16173" href="StlcProp.html#16074" class="Bound"
      >N</a
      ><a name="16174"
      > </a
      ><a name="16175" href="Stlc.html#1276" class="Function Operator"
      >[</a
      ><a name="16176"
      > </a
      ><a name="16177" href="StlcProp.html#16070" class="Bound"
      >x</a
      ><a name="16178"
      > </a
      ><a name="16179" href="Stlc.html#1276" class="Function Operator"
      >:=</a
      ><a name="16181"
      > </a
      ><a name="16182" href="StlcProp.html#16078" class="Bound"
      >V</a
      ><a name="16183"
      > </a
      ><a name="16184" href="Stlc.html#1276" class="Function Operator"
      >]</a
      ><a name="16185" class="Symbol"
      >)</a
      ><a name="16186"
      > </a
      ><a name="16187" href="Stlc.html#3112" class="Datatype Operator"
      >&#8758;</a
      ><a name="16188"
      > </a
      ><a name="16189" href="StlcProp.html#16076" class="Bound"
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

<a name="19343" href="StlcProp.html#19343" class="Function"
      >weaken-closed</a
      ><a name="19356"
      > </a
      ><a name="19357" class="Symbol"
      >:</a
      ><a name="19358"
      > </a
      ><a name="19359" class="Symbol"
      >&#8704;</a
      ><a name="19360"
      > </a
      ><a name="19361" class="Symbol"
      >{</a
      ><a name="19362" href="StlcProp.html#19362" class="Bound"
      >V</a
      ><a name="19363"
      > </a
      ><a name="19364" href="StlcProp.html#19364" class="Bound"
      >A</a
      ><a name="19365"
      > </a
      ><a name="19366" href="StlcProp.html#19366" class="Bound"
      >&#915;</a
      ><a name="19367" class="Symbol"
      >}</a
      ><a name="19368"
      > </a
      ><a name="19369" class="Symbol"
      >&#8594;</a
      ><a name="19370"
      > </a
      ><a name="19371" href="Maps.html#10265" class="Function"
      >&#8709;</a
      ><a name="19372"
      > </a
      ><a name="19373" href="Stlc.html#3112" class="Datatype Operator"
      >&#8866;</a
      ><a name="19374"
      > </a
      ><a name="19375" href="StlcProp.html#19362" class="Bound"
      >V</a
      ><a name="19376"
      > </a
      ><a name="19377" href="Stlc.html#3112" class="Datatype Operator"
      >&#8758;</a
      ><a name="19378"
      > </a
      ><a name="19379" href="StlcProp.html#19364" class="Bound"
      >A</a
      ><a name="19380"
      > </a
      ><a name="19381" class="Symbol"
      >&#8594;</a
      ><a name="19382"
      > </a
      ><a name="19383" href="StlcProp.html#19366" class="Bound"
      >&#915;</a
      ><a name="19384"
      > </a
      ><a name="19385" href="Stlc.html#3112" class="Datatype Operator"
      >&#8866;</a
      ><a name="19386"
      > </a
      ><a name="19387" href="StlcProp.html#19362" class="Bound"
      >V</a
      ><a name="19388"
      > </a
      ><a name="19389" href="Stlc.html#3112" class="Datatype Operator"
      >&#8758;</a
      ><a name="19390"
      > </a
      ><a name="19391" href="StlcProp.html#19364" class="Bound"
      >A</a
      ><a name="19392"
      >
</a
      ><a name="19393" href="StlcProp.html#19343" class="Function"
      >weaken-closed</a
      ><a name="19406"
      > </a
      ><a name="19407" class="Symbol"
      >{</a
      ><a name="19408" href="StlcProp.html#19408" class="Bound"
      >V</a
      ><a name="19409" class="Symbol"
      >}</a
      ><a name="19410"
      > </a
      ><a name="19411" class="Symbol"
      >{</a
      ><a name="19412" href="StlcProp.html#19412" class="Bound"
      >A</a
      ><a name="19413" class="Symbol"
      >}</a
      ><a name="19414"
      > </a
      ><a name="19415" class="Symbol"
      >{</a
      ><a name="19416" href="StlcProp.html#19416" class="Bound"
      >&#915;</a
      ><a name="19417" class="Symbol"
      >}</a
      ><a name="19418"
      > </a
      ><a name="19419" href="StlcProp.html#19419" class="Bound"
      >&#8866;V</a
      ><a name="19421"
      > </a
      ><a name="19422" class="Symbol"
      >=</a
      ><a name="19423"
      > </a
      ><a name="19424" href="StlcProp.html#12437" class="Function"
      >context-lemma</a
      ><a name="19437"
      > </a
      ><a name="19438" href="StlcProp.html#19456" class="Function"
      >&#915;~&#915;&#8242;</a
      ><a name="19442"
      > </a
      ><a name="19443" href="StlcProp.html#19419" class="Bound"
      >&#8866;V</a
      ><a name="19445"
      >
  </a
      ><a name="19448" class="Keyword"
      >where</a
      ><a name="19453"
      >
  </a
      ><a name="19456" href="StlcProp.html#19456" class="Function"
      >&#915;~&#915;&#8242;</a
      ><a name="19460"
      > </a
      ><a name="19461" class="Symbol"
      >:</a
      ><a name="19462"
      > </a
      ><a name="19463" class="Symbol"
      >&#8704;</a
      ><a name="19464"
      > </a
      ><a name="19465" class="Symbol"
      >{</a
      ><a name="19466" href="StlcProp.html#19466" class="Bound"
      >x</a
      ><a name="19467" class="Symbol"
      >}</a
      ><a name="19468"
      > </a
      ><a name="19469" class="Symbol"
      >&#8594;</a
      ><a name="19470"
      > </a
      ><a name="19471" href="StlcProp.html#19466" class="Bound"
      >x</a
      ><a name="19472"
      > </a
      ><a name="19473" href="StlcProp.html#7605" class="Datatype Operator"
      >&#8712;</a
      ><a name="19474"
      > </a
      ><a name="19475" href="StlcProp.html#19408" class="Bound"
      >V</a
      ><a name="19476"
      > </a
      ><a name="19477" class="Symbol"
      >&#8594;</a
      ><a name="19478"
      > </a
      ><a name="19479" href="Maps.html#10265" class="Function"
      >&#8709;</a
      ><a name="19480"
      > </a
      ><a name="19481" href="StlcProp.html#19466" class="Bound"
      >x</a
      ><a name="19482"
      > </a
      ><a name="19483" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="19484"
      > </a
      ><a name="19485" href="StlcProp.html#19416" class="Bound"
      >&#915;</a
      ><a name="19486"
      > </a
      ><a name="19487" href="StlcProp.html#19466" class="Bound"
      >x</a
      ><a name="19488"
      >
  </a
      ><a name="19491" href="StlcProp.html#19456" class="Function"
      >&#915;~&#915;&#8242;</a
      ><a name="19495"
      > </a
      ><a name="19496" class="Symbol"
      >{</a
      ><a name="19497" href="StlcProp.html#19497" class="Bound"
      >x</a
      ><a name="19498" class="Symbol"
      >}</a
      ><a name="19499"
      > </a
      ><a name="19500" href="StlcProp.html#19500" class="Bound"
      >x&#8712;V</a
      ><a name="19503"
      > </a
      ><a name="19504" class="Symbol"
      >=</a
      ><a name="19505"
      > </a
      ><a name="19506" href="https://agda.github.io/agda-stdlib/Data.Empty.html#348" class="Function"
      >&#8869;-elim</a
      ><a name="19512"
      > </a
      ><a name="19513" class="Symbol"
      >(</a
      ><a name="19514" href="StlcProp.html#19537" class="Function"
      >x&#8713;V</a
      ><a name="19517"
      > </a
      ><a name="19518" href="StlcProp.html#19500" class="Bound"
      >x&#8712;V</a
      ><a name="19521" class="Symbol"
      >)</a
      ><a name="19522"
      >
    </a
      ><a name="19527" class="Keyword"
      >where</a
      ><a name="19532"
      >
    </a
      ><a name="19537" href="StlcProp.html#19537" class="Function"
      >x&#8713;V</a
      ><a name="19540"
      > </a
      ><a name="19541" class="Symbol"
      >:</a
      ><a name="19542"
      > </a
      ><a name="19543" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#414" class="Function Operator"
      >&#172;</a
      ><a name="19544"
      > </a
      ><a name="19545" class="Symbol"
      >(</a
      ><a name="19546" href="StlcProp.html#19497" class="Bound"
      >x</a
      ><a name="19547"
      > </a
      ><a name="19548" href="StlcProp.html#7605" class="Datatype Operator"
      >&#8712;</a
      ><a name="19549"
      > </a
      ><a name="19550" href="StlcProp.html#19408" class="Bound"
      >V</a
      ><a name="19551" class="Symbol"
      >)</a
      ><a name="19552"
      >
    </a
      ><a name="19557" href="StlcProp.html#19537" class="Function"
      >x&#8713;V</a
      ><a name="19560"
      > </a
      ><a name="19561" class="Symbol"
      >=</a
      ><a name="19562"
      > </a
      ><a name="19563" href="StlcProp.html#11737" class="Postulate"
      >&#8709;&#8866;-closed</a
      ><a name="19572"
      > </a
      ><a name="19573" href="StlcProp.html#19419" class="Bound"
      >&#8866;V</a
      ><a name="19575"
      > </a
      ><a name="19576" class="Symbol"
      >{</a
      ><a name="19577" href="StlcProp.html#19497" class="Bound"
      >x</a
      ><a name="19578" class="Symbol"
      >}</a
      ><a name="19579"
      >

</a
      ><a name="19581" href="StlcProp.html#19581" class="Function"
      >just-injective</a
      ><a name="19595"
      > </a
      ><a name="19596" class="Symbol"
      >:</a
      ><a name="19597"
      > </a
      ><a name="19598" class="Symbol"
      >&#8704;</a
      ><a name="19599"
      > </a
      ><a name="19600" class="Symbol"
      >{</a
      ><a name="19601" href="StlcProp.html#19601" class="Bound"
      >X</a
      ><a name="19602"
      > </a
      ><a name="19603" class="Symbol"
      >:</a
      ><a name="19604"
      > </a
      ><a name="19605" class="PrimitiveType"
      >Set</a
      ><a name="19608" class="Symbol"
      >}</a
      ><a name="19609"
      > </a
      ><a name="19610" class="Symbol"
      >{</a
      ><a name="19611" href="StlcProp.html#19611" class="Bound"
      >x</a
      ><a name="19612"
      > </a
      ><a name="19613" href="StlcProp.html#19613" class="Bound"
      >y</a
      ><a name="19614"
      > </a
      ><a name="19615" class="Symbol"
      >:</a
      ><a name="19616"
      > </a
      ><a name="19617" href="StlcProp.html#19601" class="Bound"
      >X</a
      ><a name="19618" class="Symbol"
      >}</a
      ><a name="19619"
      > </a
      ><a name="19620" class="Symbol"
      >&#8594;</a
      ><a name="19621"
      > </a
      ><a name="19622" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >_&#8801;_</a
      ><a name="19625"
      > </a
      ><a name="19626" class="Symbol"
      >{</a
      ><a name="19627" class="Argument"
      >A</a
      ><a name="19628"
      > </a
      ><a name="19629" class="Symbol"
      >=</a
      ><a name="19630"
      > </a
      ><a name="19631" href="https://agda.github.io/agda-stdlib/Data.Maybe.Base.html#335" class="Datatype"
      >Maybe</a
      ><a name="19636"
      > </a
      ><a name="19637" href="StlcProp.html#19601" class="Bound"
      >X</a
      ><a name="19638" class="Symbol"
      >}</a
      ><a name="19639"
      > </a
      ><a name="19640" class="Symbol"
      >(</a
      ><a name="19641" href="https://agda.github.io/agda-stdlib/Data.Maybe.Base.html#373" class="InductiveConstructor"
      >just</a
      ><a name="19645"
      > </a
      ><a name="19646" href="StlcProp.html#19611" class="Bound"
      >x</a
      ><a name="19647" class="Symbol"
      >)</a
      ><a name="19648"
      > </a
      ><a name="19649" class="Symbol"
      >(</a
      ><a name="19650" href="https://agda.github.io/agda-stdlib/Data.Maybe.Base.html#373" class="InductiveConstructor"
      >just</a
      ><a name="19654"
      > </a
      ><a name="19655" href="StlcProp.html#19613" class="Bound"
      >y</a
      ><a name="19656" class="Symbol"
      >)</a
      ><a name="19657"
      > </a
      ><a name="19658" class="Symbol"
      >&#8594;</a
      ><a name="19659"
      > </a
      ><a name="19660" href="StlcProp.html#19611" class="Bound"
      >x</a
      ><a name="19661"
      > </a
      ><a name="19662" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="19663"
      > </a
      ><a name="19664" href="StlcProp.html#19613" class="Bound"
      >y</a
      ><a name="19665"
      >
</a
      ><a name="19666" href="StlcProp.html#19581" class="Function"
      >just-injective</a
      ><a name="19680"
      > </a
      ><a name="19681" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="19685"
      > </a
      ><a name="19686" class="Symbol"
      >=</a
      ><a name="19687"
      > </a
      ><a name="19688" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      >

</pre>

<pre class="Agda">

<a name="19718" href="StlcProp.html#16045" class="Function"
      >preservation-[:=]</a
      ><a name="19735"
      > </a
      ><a name="19736" class="Symbol"
      >{</a
      ><a name="19737" href="StlcProp.html#19737" class="Bound"
      >&#915;</a
      ><a name="19738" class="Symbol"
      >}</a
      ><a name="19739"
      > </a
      ><a name="19740" class="Symbol"
      >{</a
      ><a name="19741" href="StlcProp.html#19741" class="Bound"
      >x</a
      ><a name="19742" class="Symbol"
      >}</a
      ><a name="19743"
      > </a
      ><a name="19744" class="Symbol"
      >{</a
      ><a name="19745" href="StlcProp.html#19745" class="Bound"
      >A</a
      ><a name="19746" class="Symbol"
      >}</a
      ><a name="19747"
      > </a
      ><a name="19748" class="Symbol"
      >(</a
      ><a name="19749" href="Stlc.html#3156" class="InductiveConstructor"
      >Ax</a
      ><a name="19751"
      > </a
      ><a name="19752" class="Symbol"
      >{</a
      ><a name="19753" href="StlcProp.html#19753" class="Bound"
      >&#915;,x&#8758;A</a
      ><a name="19758" class="Symbol"
      >}</a
      ><a name="19759"
      > </a
      ><a name="19760" class="Symbol"
      >{</a
      ><a name="19761" href="StlcProp.html#19761" class="Bound"
      >x&#8242;</a
      ><a name="19763" class="Symbol"
      >}</a
      ><a name="19764"
      > </a
      ><a name="19765" class="Symbol"
      >{</a
      ><a name="19766" href="StlcProp.html#19766" class="Bound"
      >B</a
      ><a name="19767" class="Symbol"
      >}</a
      ><a name="19768"
      > </a
      ><a name="19769" href="StlcProp.html#19769" class="Bound"
      >[&#915;,x&#8758;A]x&#8242;&#8801;B</a
      ><a name="19780" class="Symbol"
      >)</a
      ><a name="19781"
      > </a
      ><a name="19782" href="StlcProp.html#19782" class="Bound"
      >&#8866;V</a
      ><a name="19784"
      > </a
      ><a name="19785" class="Keyword"
      >with</a
      ><a name="19789"
      > </a
      ><a name="19790" href="StlcProp.html#19741" class="Bound"
      >x</a
      ><a name="19791"
      > </a
      ><a name="19792" href="Maps.html#2509" class="Function Operator"
      >&#8799;</a
      ><a name="19793"
      > </a
      ><a name="19794" href="StlcProp.html#19761" class="Bound"
      >x&#8242;</a
      ><a name="19796"
      >
</a
      ><a name="19797" class="Symbol"
      >...|</a
      ><a name="19801"
      > </a
      ><a name="19802" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#520" class="InductiveConstructor"
      >yes</a
      ><a name="19805"
      > </a
      ><a name="19806" href="StlcProp.html#19806" class="Bound"
      >x&#8801;x&#8242;</a
      ><a name="19810"
      > </a
      ><a name="19811" class="Keyword"
      >rewrite</a
      ><a name="19818"
      > </a
      ><a name="19819" href="StlcProp.html#19581" class="Function"
      >just-injective</a
      ><a name="19833"
      > </a
      ><a name="19834" href="StlcProp.html#19769" class="Bound"
      >[&#915;,x&#8758;A]x&#8242;&#8801;B</a
      ><a name="19845"
      >  </a
      ><a name="19847" class="Symbol"
      >=</a
      ><a name="19848"
      >  </a
      ><a name="19850" href="StlcProp.html#19343" class="Function"
      >weaken-closed</a
      ><a name="19863"
      > </a
      ><a name="19864" href="StlcProp.html#19782" class="Bound"
      >&#8866;V</a
      ><a name="19866"
      >
</a
      ><a name="19867" class="Symbol"
      >...|</a
      ><a name="19871"
      > </a
      ><a name="19872" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#547" class="InductiveConstructor"
      >no</a
      ><a name="19874"
      >  </a
      ><a name="19876" href="StlcProp.html#19876" class="Bound"
      >x&#8802;x&#8242;</a
      ><a name="19880"
      >  </a
      ><a name="19882" class="Symbol"
      >=</a
      ><a name="19883"
      >  </a
      ><a name="19885" href="Stlc.html#3156" class="InductiveConstructor"
      >Ax</a
      ><a name="19887"
      > </a
      ><a name="19888" href="StlcProp.html#19769" class="Bound"
      >[&#915;,x&#8758;A]x&#8242;&#8801;B</a
      ><a name="19899"
      >
</a
      ><a name="19900" href="StlcProp.html#16045" class="Function"
      >preservation-[:=]</a
      ><a name="19917"
      > </a
      ><a name="19918" class="Symbol"
      >{</a
      ><a name="19919" href="StlcProp.html#19919" class="Bound"
      >&#915;</a
      ><a name="19920" class="Symbol"
      >}</a
      ><a name="19921"
      > </a
      ><a name="19922" class="Symbol"
      >{</a
      ><a name="19923" href="StlcProp.html#19923" class="Bound"
      >x</a
      ><a name="19924" class="Symbol"
      >}</a
      ><a name="19925"
      > </a
      ><a name="19926" class="Symbol"
      >{</a
      ><a name="19927" href="StlcProp.html#19927" class="Bound"
      >A</a
      ><a name="19928" class="Symbol"
      >}</a
      ><a name="19929"
      > </a
      ><a name="19930" class="Symbol"
      >{</a
      ><a name="19931" href="Stlc.html#743" class="InductiveConstructor Operator"
      >&#955;[</a
      ><a name="19933"
      > </a
      ><a name="19934" href="StlcProp.html#19934" class="Bound"
      >x&#8242;</a
      ><a name="19936"
      > </a
      ><a name="19937" href="Stlc.html#743" class="InductiveConstructor Operator"
      >&#8758;</a
      ><a name="19938"
      > </a
      ><a name="19939" href="StlcProp.html#19939" class="Bound"
      >A&#8242;</a
      ><a name="19941"
      > </a
      ><a name="19942" href="Stlc.html#743" class="InductiveConstructor Operator"
      >]</a
      ><a name="19943"
      > </a
      ><a name="19944" href="StlcProp.html#19944" class="Bound"
      >N&#8242;</a
      ><a name="19946" class="Symbol"
      >}</a
      ><a name="19947"
      > </a
      ><a name="19948" class="Symbol"
      >{</a
      ><a name="19949" class="DottedPattern Symbol"
      >.</a
      ><a name="19950" href="StlcProp.html#19939" class="DottedPattern Bound"
      >A&#8242;</a
      ><a name="19952"
      > </a
      ><a name="19953" href="Stlc.html#620" class="InductiveConstructor Operator"
      >&#8658;</a
      ><a name="19954"
      > </a
      ><a name="19955" href="StlcProp.html#19955" class="Bound"
      >B&#8242;</a
      ><a name="19957" class="Symbol"
      >}</a
      ><a name="19958"
      > </a
      ><a name="19959" class="Symbol"
      >{</a
      ><a name="19960" href="StlcProp.html#19960" class="Bound"
      >V</a
      ><a name="19961" class="Symbol"
      >}</a
      ><a name="19962"
      > </a
      ><a name="19963" class="Symbol"
      >(</a
      ><a name="19964" href="Stlc.html#3210" class="InductiveConstructor"
      >&#8658;-I</a
      ><a name="19967"
      > </a
      ><a name="19968" href="StlcProp.html#19968" class="Bound"
      >&#8866;N&#8242;</a
      ><a name="19971" class="Symbol"
      >)</a
      ><a name="19972"
      > </a
      ><a name="19973" href="StlcProp.html#19973" class="Bound"
      >&#8866;V</a
      ><a name="19975"
      > </a
      ><a name="19976" class="Keyword"
      >with</a
      ><a name="19980"
      > </a
      ><a name="19981" href="StlcProp.html#19923" class="Bound"
      >x</a
      ><a name="19982"
      > </a
      ><a name="19983" href="Maps.html#2509" class="Function Operator"
      >&#8799;</a
      ><a name="19984"
      > </a
      ><a name="19985" href="StlcProp.html#19934" class="Bound"
      >x&#8242;</a
      ><a name="19987"
      >
</a
      ><a name="19988" class="Symbol"
      >...|</a
      ><a name="19992"
      > </a
      ><a name="19993" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#520" class="InductiveConstructor"
      >yes</a
      ><a name="19996"
      > </a
      ><a name="19997" href="StlcProp.html#19997" class="Bound"
      >x&#8801;x&#8242;</a
      ><a name="20001"
      > </a
      ><a name="20002" class="Keyword"
      >rewrite</a
      ><a name="20009"
      > </a
      ><a name="20010" href="StlcProp.html#19997" class="Bound"
      >x&#8801;x&#8242;</a
      ><a name="20014"
      > </a
      ><a name="20015" class="Symbol"
      >=</a
      ><a name="20016"
      > </a
      ><a name="20017" href="StlcProp.html#12437" class="Function"
      >context-lemma</a
      ><a name="20030"
      > </a
      ><a name="20031" href="StlcProp.html#20056" class="Function"
      >&#915;&#8242;~&#915;</a
      ><a name="20035"
      > </a
      ><a name="20036" class="Symbol"
      >(</a
      ><a name="20037" href="Stlc.html#3210" class="InductiveConstructor"
      >&#8658;-I</a
      ><a name="20040"
      > </a
      ><a name="20041" href="StlcProp.html#19968" class="Bound"
      >&#8866;N&#8242;</a
      ><a name="20044" class="Symbol"
      >)</a
      ><a name="20045"
      >
  </a
      ><a name="20048" class="Keyword"
      >where</a
      ><a name="20053"
      >
  </a
      ><a name="20056" href="StlcProp.html#20056" class="Function"
      >&#915;&#8242;~&#915;</a
      ><a name="20060"
      > </a
      ><a name="20061" class="Symbol"
      >:</a
      ><a name="20062"
      > </a
      ><a name="20063" class="Symbol"
      >&#8704;</a
      ><a name="20064"
      > </a
      ><a name="20065" class="Symbol"
      >{</a
      ><a name="20066" href="StlcProp.html#20066" class="Bound"
      >y</a
      ><a name="20067" class="Symbol"
      >}</a
      ><a name="20068"
      > </a
      ><a name="20069" class="Symbol"
      >&#8594;</a
      ><a name="20070"
      > </a
      ><a name="20071" href="StlcProp.html#20066" class="Bound"
      >y</a
      ><a name="20072"
      > </a
      ><a name="20073" href="StlcProp.html#7605" class="Datatype Operator"
      >&#8712;</a
      ><a name="20074"
      > </a
      ><a name="20075" class="Symbol"
      >(</a
      ><a name="20076" href="Stlc.html#743" class="InductiveConstructor Operator"
      >&#955;[</a
      ><a name="20078"
      > </a
      ><a name="20079" href="StlcProp.html#19934" class="Bound"
      >x&#8242;</a
      ><a name="20081"
      > </a
      ><a name="20082" href="Stlc.html#743" class="InductiveConstructor Operator"
      >&#8758;</a
      ><a name="20083"
      > </a
      ><a name="20084" href="StlcProp.html#19939" class="Bound"
      >A&#8242;</a
      ><a name="20086"
      > </a
      ><a name="20087" href="Stlc.html#743" class="InductiveConstructor Operator"
      >]</a
      ><a name="20088"
      > </a
      ><a name="20089" href="StlcProp.html#19944" class="Bound"
      >N&#8242;</a
      ><a name="20091" class="Symbol"
      >)</a
      ><a name="20092"
      > </a
      ><a name="20093" class="Symbol"
      >&#8594;</a
      ><a name="20094"
      > </a
      ><a name="20095" class="Symbol"
      >(</a
      ><a name="20096" href="StlcProp.html#19919" class="Bound"
      >&#915;</a
      ><a name="20097"
      > </a
      ><a name="20098" href="Maps.html#10368" class="Function Operator"
      >,</a
      ><a name="20099"
      > </a
      ><a name="20100" href="StlcProp.html#19934" class="Bound"
      >x&#8242;</a
      ><a name="20102"
      > </a
      ><a name="20103" href="Maps.html#10368" class="Function Operator"
      >&#8758;</a
      ><a name="20104"
      > </a
      ><a name="20105" href="StlcProp.html#19927" class="Bound"
      >A</a
      ><a name="20106" class="Symbol"
      >)</a
      ><a name="20107"
      > </a
      ><a name="20108" href="StlcProp.html#20066" class="Bound"
      >y</a
      ><a name="20109"
      > </a
      ><a name="20110" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="20111"
      > </a
      ><a name="20112" href="StlcProp.html#19919" class="Bound"
      >&#915;</a
      ><a name="20113"
      > </a
      ><a name="20114" href="StlcProp.html#20066" class="Bound"
      >y</a
      ><a name="20115"
      >
  </a
      ><a name="20118" href="StlcProp.html#20056" class="Function"
      >&#915;&#8242;~&#915;</a
      ><a name="20122"
      > </a
      ><a name="20123" class="Symbol"
      >{</a
      ><a name="20124" href="StlcProp.html#20124" class="Bound"
      >y</a
      ><a name="20125" class="Symbol"
      >}</a
      ><a name="20126"
      > </a
      ><a name="20127" class="Symbol"
      >(</a
      ><a name="20128" href="StlcProp.html#7663" class="InductiveConstructor"
      >free-&#955;</a
      ><a name="20134"
      > </a
      ><a name="20135" href="StlcProp.html#20135" class="Bound"
      >x&#8242;&#8802;y</a
      ><a name="20139"
      > </a
      ><a name="20140" href="StlcProp.html#20140" class="Bound"
      >y&#8712;N&#8242;</a
      ><a name="20144" class="Symbol"
      >)</a
      ><a name="20145"
      > </a
      ><a name="20146" class="Keyword"
      >with</a
      ><a name="20150"
      > </a
      ><a name="20151" href="StlcProp.html#19934" class="Bound"
      >x&#8242;</a
      ><a name="20153"
      > </a
      ><a name="20154" href="Maps.html#2509" class="Function Operator"
      >&#8799;</a
      ><a name="20155"
      > </a
      ><a name="20156" href="StlcProp.html#20124" class="Bound"
      >y</a
      ><a name="20157"
      >
  </a
      ><a name="20160" class="Symbol"
      >...|</a
      ><a name="20164"
      > </a
      ><a name="20165" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#520" class="InductiveConstructor"
      >yes</a
      ><a name="20168"
      > </a
      ><a name="20169" href="StlcProp.html#20169" class="Bound"
      >x&#8242;&#8801;y</a
      ><a name="20173"
      >  </a
      ><a name="20175" class="Symbol"
      >=</a
      ><a name="20176"
      > </a
      ><a name="20177" href="https://agda.github.io/agda-stdlib/Data.Empty.html#348" class="Function"
      >&#8869;-elim</a
      ><a name="20183"
      > </a
      ><a name="20184" class="Symbol"
      >(</a
      ><a name="20185" href="StlcProp.html#20135" class="Bound"
      >x&#8242;&#8802;y</a
      ><a name="20189"
      > </a
      ><a name="20190" href="StlcProp.html#20169" class="Bound"
      >x&#8242;&#8801;y</a
      ><a name="20194" class="Symbol"
      >)</a
      ><a name="20195"
      >
  </a
      ><a name="20198" class="Symbol"
      >...|</a
      ><a name="20202"
      > </a
      ><a name="20203" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#547" class="InductiveConstructor"
      >no</a
      ><a name="20205"
      >  </a
      ><a name="20207" class="Symbol"
      >_</a
      ><a name="20208"
      >     </a
      ><a name="20213" class="Symbol"
      >=</a
      ><a name="20214"
      > </a
      ><a name="20215" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="20219"
      >
</a
      ><a name="20220" class="Symbol"
      >...|</a
      ><a name="20224"
      > </a
      ><a name="20225" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#547" class="InductiveConstructor"
      >no</a
      ><a name="20227"
      >  </a
      ><a name="20229" href="StlcProp.html#20229" class="Bound"
      >x&#8802;x&#8242;</a
      ><a name="20233"
      > </a
      ><a name="20234" class="Symbol"
      >=</a
      ><a name="20235"
      > </a
      ><a name="20236" href="Stlc.html#3210" class="InductiveConstructor"
      >&#8658;-I</a
      ><a name="20239"
      > </a
      ><a name="20240" href="StlcProp.html#20351" class="Function"
      >&#8866;N&#8242;V</a
      ><a name="20244"
      >
  </a
      ><a name="20247" class="Keyword"
      >where</a
      ><a name="20252"
      >
  </a
      ><a name="20255" href="StlcProp.html#20255" class="Function"
      >x&#8242;x&#8866;N&#8242;</a
      ><a name="20261"
      > </a
      ><a name="20262" class="Symbol"
      >:</a
      ><a name="20263"
      > </a
      ><a name="20264" href="StlcProp.html#19919" class="Bound"
      >&#915;</a
      ><a name="20265"
      > </a
      ><a name="20266" href="Maps.html#10368" class="Function Operator"
      >,</a
      ><a name="20267"
      > </a
      ><a name="20268" href="StlcProp.html#19934" class="Bound"
      >x&#8242;</a
      ><a name="20270"
      > </a
      ><a name="20271" href="Maps.html#10368" class="Function Operator"
      >&#8758;</a
      ><a name="20272"
      > </a
      ><a name="20273" href="StlcProp.html#19939" class="Bound"
      >A&#8242;</a
      ><a name="20275"
      > </a
      ><a name="20276" href="Maps.html#10368" class="Function Operator"
      >,</a
      ><a name="20277"
      > </a
      ><a name="20278" href="StlcProp.html#19923" class="Bound"
      >x</a
      ><a name="20279"
      > </a
      ><a name="20280" href="Maps.html#10368" class="Function Operator"
      >&#8758;</a
      ><a name="20281"
      > </a
      ><a name="20282" href="StlcProp.html#19927" class="Bound"
      >A</a
      ><a name="20283"
      > </a
      ><a name="20284" href="Stlc.html#3112" class="Datatype Operator"
      >&#8866;</a
      ><a name="20285"
      > </a
      ><a name="20286" href="StlcProp.html#19944" class="Bound"
      >N&#8242;</a
      ><a name="20288"
      > </a
      ><a name="20289" href="Stlc.html#3112" class="Datatype Operator"
      >&#8758;</a
      ><a name="20290"
      > </a
      ><a name="20291" href="StlcProp.html#19955" class="Bound"
      >B&#8242;</a
      ><a name="20293"
      >
  </a
      ><a name="20296" href="StlcProp.html#20255" class="Function"
      >x&#8242;x&#8866;N&#8242;</a
      ><a name="20302"
      > </a
      ><a name="20303" class="Keyword"
      >rewrite</a
      ><a name="20310"
      > </a
      ><a name="20311" href="Maps.html#11491" class="Function"
      >update-permute</a
      ><a name="20325"
      > </a
      ><a name="20326" href="StlcProp.html#19919" class="Bound"
      >&#915;</a
      ><a name="20327"
      > </a
      ><a name="20328" href="StlcProp.html#19923" class="Bound"
      >x</a
      ><a name="20329"
      > </a
      ><a name="20330" href="StlcProp.html#19927" class="Bound"
      >A</a
      ><a name="20331"
      > </a
      ><a name="20332" href="StlcProp.html#19934" class="Bound"
      >x&#8242;</a
      ><a name="20334"
      > </a
      ><a name="20335" href="StlcProp.html#19939" class="Bound"
      >A&#8242;</a
      ><a name="20337"
      > </a
      ><a name="20338" href="StlcProp.html#20229" class="Bound"
      >x&#8802;x&#8242;</a
      ><a name="20342"
      > </a
      ><a name="20343" class="Symbol"
      >=</a
      ><a name="20344"
      > </a
      ><a name="20345" href="StlcProp.html#19968" class="Bound"
      >&#8866;N&#8242;</a
      ><a name="20348"
      >
  </a
      ><a name="20351" href="StlcProp.html#20351" class="Function"
      >&#8866;N&#8242;V</a
      ><a name="20355"
      > </a
      ><a name="20356" class="Symbol"
      >:</a
      ><a name="20357"
      > </a
      ><a name="20358" class="Symbol"
      >(</a
      ><a name="20359" href="StlcProp.html#19919" class="Bound"
      >&#915;</a
      ><a name="20360"
      > </a
      ><a name="20361" href="Maps.html#10368" class="Function Operator"
      >,</a
      ><a name="20362"
      > </a
      ><a name="20363" href="StlcProp.html#19934" class="Bound"
      >x&#8242;</a
      ><a name="20365"
      > </a
      ><a name="20366" href="Maps.html#10368" class="Function Operator"
      >&#8758;</a
      ><a name="20367"
      > </a
      ><a name="20368" href="StlcProp.html#19939" class="Bound"
      >A&#8242;</a
      ><a name="20370" class="Symbol"
      >)</a
      ><a name="20371"
      > </a
      ><a name="20372" href="Stlc.html#3112" class="Datatype Operator"
      >&#8866;</a
      ><a name="20373"
      > </a
      ><a name="20374" href="StlcProp.html#19944" class="Bound"
      >N&#8242;</a
      ><a name="20376"
      > </a
      ><a name="20377" href="Stlc.html#1276" class="Function Operator"
      >[</a
      ><a name="20378"
      > </a
      ><a name="20379" href="StlcProp.html#19923" class="Bound"
      >x</a
      ><a name="20380"
      > </a
      ><a name="20381" href="Stlc.html#1276" class="Function Operator"
      >:=</a
      ><a name="20383"
      > </a
      ><a name="20384" href="StlcProp.html#19960" class="Bound"
      >V</a
      ><a name="20385"
      > </a
      ><a name="20386" href="Stlc.html#1276" class="Function Operator"
      >]</a
      ><a name="20387"
      > </a
      ><a name="20388" href="Stlc.html#3112" class="Datatype Operator"
      >&#8758;</a
      ><a name="20389"
      > </a
      ><a name="20390" href="StlcProp.html#19955" class="Bound"
      >B&#8242;</a
      ><a name="20392"
      >
  </a
      ><a name="20395" href="StlcProp.html#20351" class="Function"
      >&#8866;N&#8242;V</a
      ><a name="20399"
      > </a
      ><a name="20400" class="Symbol"
      >=</a
      ><a name="20401"
      > </a
      ><a name="20402" href="StlcProp.html#16045" class="Function"
      >preservation-[:=]</a
      ><a name="20419"
      > </a
      ><a name="20420" href="StlcProp.html#20255" class="Function"
      >x&#8242;x&#8866;N&#8242;</a
      ><a name="20426"
      > </a
      ><a name="20427" href="StlcProp.html#19973" class="Bound"
      >&#8866;V</a
      ><a name="20429"
      >
</a
      ><a name="20430" href="StlcProp.html#16045" class="Function"
      >preservation-[:=]</a
      ><a name="20447"
      > </a
      ><a name="20448" class="Symbol"
      >(</a
      ><a name="20449" href="Stlc.html#3287" class="InductiveConstructor"
      >&#8658;-E</a
      ><a name="20452"
      > </a
      ><a name="20453" href="StlcProp.html#20453" class="Bound"
      >&#8866;L</a
      ><a name="20455"
      > </a
      ><a name="20456" href="StlcProp.html#20456" class="Bound"
      >&#8866;M</a
      ><a name="20458" class="Symbol"
      >)</a
      ><a name="20459"
      > </a
      ><a name="20460" href="StlcProp.html#20460" class="Bound"
      >&#8866;V</a
      ><a name="20462"
      > </a
      ><a name="20463" class="Symbol"
      >=</a
      ><a name="20464"
      > </a
      ><a name="20465" href="Stlc.html#3287" class="InductiveConstructor"
      >&#8658;-E</a
      ><a name="20468"
      > </a
      ><a name="20469" class="Symbol"
      >(</a
      ><a name="20470" href="StlcProp.html#16045" class="Function"
      >preservation-[:=]</a
      ><a name="20487"
      > </a
      ><a name="20488" href="StlcProp.html#20453" class="Bound"
      >&#8866;L</a
      ><a name="20490"
      > </a
      ><a name="20491" href="StlcProp.html#20460" class="Bound"
      >&#8866;V</a
      ><a name="20493" class="Symbol"
      >)</a
      ><a name="20494"
      > </a
      ><a name="20495" class="Symbol"
      >(</a
      ><a name="20496" href="StlcProp.html#16045" class="Function"
      >preservation-[:=]</a
      ><a name="20513"
      > </a
      ><a name="20514" href="StlcProp.html#20456" class="Bound"
      >&#8866;M</a
      ><a name="20516"
      > </a
      ><a name="20517" href="StlcProp.html#20460" class="Bound"
      >&#8866;V</a
      ><a name="20519" class="Symbol"
      >)</a
      ><a name="20520"
      >
</a
      ><a name="20521" href="StlcProp.html#16045" class="Function"
      >preservation-[:=]</a
      ><a name="20538"
      > </a
      ><a name="20539" href="Stlc.html#3365" class="InductiveConstructor"
      >&#120121;-I&#8321;</a
      ><a name="20543"
      > </a
      ><a name="20544" href="StlcProp.html#20544" class="Bound"
      >&#8866;V</a
      ><a name="20546"
      > </a
      ><a name="20547" class="Symbol"
      >=</a
      ><a name="20548"
      > </a
      ><a name="20549" href="Stlc.html#3365" class="InductiveConstructor"
      >&#120121;-I&#8321;</a
      ><a name="20553"
      >
</a
      ><a name="20554" href="StlcProp.html#16045" class="Function"
      >preservation-[:=]</a
      ><a name="20571"
      > </a
      ><a name="20572" href="Stlc.html#3399" class="InductiveConstructor"
      >&#120121;-I&#8322;</a
      ><a name="20576"
      > </a
      ><a name="20577" href="StlcProp.html#20577" class="Bound"
      >&#8866;V</a
      ><a name="20579"
      > </a
      ><a name="20580" class="Symbol"
      >=</a
      ><a name="20581"
      > </a
      ><a name="20582" href="Stlc.html#3399" class="InductiveConstructor"
      >&#120121;-I&#8322;</a
      ><a name="20586"
      >
</a
      ><a name="20587" href="StlcProp.html#16045" class="Function"
      >preservation-[:=]</a
      ><a name="20604"
      > </a
      ><a name="20605" class="Symbol"
      >(</a
      ><a name="20606" href="Stlc.html#3434" class="InductiveConstructor"
      >&#120121;-E</a
      ><a name="20609"
      > </a
      ><a name="20610" href="StlcProp.html#20610" class="Bound"
      >&#8866;L</a
      ><a name="20612"
      > </a
      ><a name="20613" href="StlcProp.html#20613" class="Bound"
      >&#8866;M</a
      ><a name="20615"
      > </a
      ><a name="20616" href="StlcProp.html#20616" class="Bound"
      >&#8866;N</a
      ><a name="20618" class="Symbol"
      >)</a
      ><a name="20619"
      > </a
      ><a name="20620" href="StlcProp.html#20620" class="Bound"
      >&#8866;V</a
      ><a name="20622"
      > </a
      ><a name="20623" class="Symbol"
      >=</a
      ><a name="20624"
      >
  </a
      ><a name="20627" href="Stlc.html#3434" class="InductiveConstructor"
      >&#120121;-E</a
      ><a name="20630"
      > </a
      ><a name="20631" class="Symbol"
      >(</a
      ><a name="20632" href="StlcProp.html#16045" class="Function"
      >preservation-[:=]</a
      ><a name="20649"
      > </a
      ><a name="20650" href="StlcProp.html#20610" class="Bound"
      >&#8866;L</a
      ><a name="20652"
      > </a
      ><a name="20653" href="StlcProp.html#20620" class="Bound"
      >&#8866;V</a
      ><a name="20655" class="Symbol"
      >)</a
      ><a name="20656"
      > </a
      ><a name="20657" class="Symbol"
      >(</a
      ><a name="20658" href="StlcProp.html#16045" class="Function"
      >preservation-[:=]</a
      ><a name="20675"
      > </a
      ><a name="20676" href="StlcProp.html#20613" class="Bound"
      >&#8866;M</a
      ><a name="20678"
      > </a
      ><a name="20679" href="StlcProp.html#20620" class="Bound"
      >&#8866;V</a
      ><a name="20681" class="Symbol"
      >)</a
      ><a name="20682"
      > </a
      ><a name="20683" class="Symbol"
      >(</a
      ><a name="20684" href="StlcProp.html#16045" class="Function"
      >preservation-[:=]</a
      ><a name="20701"
      > </a
      ><a name="20702" href="StlcProp.html#20616" class="Bound"
      >&#8866;N</a
      ><a name="20704"
      > </a
      ><a name="20705" href="StlcProp.html#20620" class="Bound"
      >&#8866;V</a
      ><a name="20707" class="Symbol"
      >)</a
      >

</pre>


### Main Theorem

We now have the tools we need to prove preservation: if a closed
term `M` has type `A` and takes a step to `N`, then `N`
is also a closed term with type `A`.  In other words, small-step
reduction preserves types.

<pre class="Agda">

<a name="20967" href="StlcProp.html#20967" class="Function"
      >preservation</a
      ><a name="20979"
      > </a
      ><a name="20980" class="Symbol"
      >:</a
      ><a name="20981"
      > </a
      ><a name="20982" class="Symbol"
      >&#8704;</a
      ><a name="20983"
      > </a
      ><a name="20984" class="Symbol"
      >{</a
      ><a name="20985" href="StlcProp.html#20985" class="Bound"
      >M</a
      ><a name="20986"
      > </a
      ><a name="20987" href="StlcProp.html#20987" class="Bound"
      >N</a
      ><a name="20988"
      > </a
      ><a name="20989" href="StlcProp.html#20989" class="Bound"
      >A</a
      ><a name="20990" class="Symbol"
      >}</a
      ><a name="20991"
      > </a
      ><a name="20992" class="Symbol"
      >&#8594;</a
      ><a name="20993"
      > </a
      ><a name="20994" href="Maps.html#10265" class="Function"
      >&#8709;</a
      ><a name="20995"
      > </a
      ><a name="20996" href="Stlc.html#3112" class="Datatype Operator"
      >&#8866;</a
      ><a name="20997"
      > </a
      ><a name="20998" href="StlcProp.html#20985" class="Bound"
      >M</a
      ><a name="20999"
      > </a
      ><a name="21000" href="Stlc.html#3112" class="Datatype Operator"
      >&#8758;</a
      ><a name="21001"
      > </a
      ><a name="21002" href="StlcProp.html#20989" class="Bound"
      >A</a
      ><a name="21003"
      > </a
      ><a name="21004" class="Symbol"
      >&#8594;</a
      ><a name="21005"
      > </a
      ><a name="21006" href="StlcProp.html#20985" class="Bound"
      >M</a
      ><a name="21007"
      > </a
      ><a name="21008" href="Stlc.html#1762" class="Datatype Operator"
      >&#10233;</a
      ><a name="21009"
      > </a
      ><a name="21010" href="StlcProp.html#20987" class="Bound"
      >N</a
      ><a name="21011"
      > </a
      ><a name="21012" class="Symbol"
      >&#8594;</a
      ><a name="21013"
      > </a
      ><a name="21014" href="Maps.html#10265" class="Function"
      >&#8709;</a
      ><a name="21015"
      > </a
      ><a name="21016" href="Stlc.html#3112" class="Datatype Operator"
      >&#8866;</a
      ><a name="21017"
      > </a
      ><a name="21018" href="StlcProp.html#20987" class="Bound"
      >N</a
      ><a name="21019"
      > </a
      ><a name="21020" href="Stlc.html#3112" class="Datatype Operator"
      >&#8758;</a
      ><a name="21021"
      > </a
      ><a name="21022" href="StlcProp.html#20989" class="Bound"
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

<a name="22280" href="StlcProp.html#20967" class="Function"
      >preservation</a
      ><a name="22292"
      > </a
      ><a name="22293" class="Symbol"
      >(</a
      ><a name="22294" href="Stlc.html#3156" class="InductiveConstructor"
      >Ax</a
      ><a name="22296"
      > </a
      ><a name="22297" href="StlcProp.html#22297" class="Bound"
      >&#915;x&#8801;A</a
      ><a name="22301" class="Symbol"
      >)</a
      ><a name="22302"
      > </a
      ><a name="22303" class="Symbol"
      >()</a
      ><a name="22305"
      >
</a
      ><a name="22306" href="StlcProp.html#20967" class="Function"
      >preservation</a
      ><a name="22318"
      > </a
      ><a name="22319" class="Symbol"
      >(</a
      ><a name="22320" href="Stlc.html#3210" class="InductiveConstructor"
      >&#8658;-I</a
      ><a name="22323"
      > </a
      ><a name="22324" href="StlcProp.html#22324" class="Bound"
      >&#8866;N</a
      ><a name="22326" class="Symbol"
      >)</a
      ><a name="22327"
      > </a
      ><a name="22328" class="Symbol"
      >()</a
      ><a name="22330"
      >
</a
      ><a name="22331" href="StlcProp.html#20967" class="Function"
      >preservation</a
      ><a name="22343"
      > </a
      ><a name="22344" class="Symbol"
      >(</a
      ><a name="22345" href="Stlc.html#3287" class="InductiveConstructor"
      >&#8658;-E</a
      ><a name="22348"
      > </a
      ><a name="22349" class="Symbol"
      >(</a
      ><a name="22350" href="Stlc.html#3210" class="InductiveConstructor"
      >&#8658;-I</a
      ><a name="22353"
      > </a
      ><a name="22354" href="StlcProp.html#22354" class="Bound"
      >&#8866;N</a
      ><a name="22356" class="Symbol"
      >)</a
      ><a name="22357"
      > </a
      ><a name="22358" href="StlcProp.html#22358" class="Bound"
      >&#8866;V</a
      ><a name="22360" class="Symbol"
      >)</a
      ><a name="22361"
      > </a
      ><a name="22362" class="Symbol"
      >(</a
      ><a name="22363" href="Stlc.html#1794" class="InductiveConstructor"
      >&#946;&#955;&#183;</a
      ><a name="22366"
      > </a
      ><a name="22367" href="StlcProp.html#22367" class="Bound"
      >valueV</a
      ><a name="22373" class="Symbol"
      >)</a
      ><a name="22374"
      > </a
      ><a name="22375" class="Symbol"
      >=</a
      ><a name="22376"
      > </a
      ><a name="22377" href="StlcProp.html#16045" class="Function"
      >preservation-[:=]</a
      ><a name="22394"
      > </a
      ><a name="22395" href="StlcProp.html#22354" class="Bound"
      >&#8866;N</a
      ><a name="22397"
      > </a
      ><a name="22398" href="StlcProp.html#22358" class="Bound"
      >&#8866;V</a
      ><a name="22400"
      >
</a
      ><a name="22401" href="StlcProp.html#20967" class="Function"
      >preservation</a
      ><a name="22413"
      > </a
      ><a name="22414" class="Symbol"
      >(</a
      ><a name="22415" href="Stlc.html#3287" class="InductiveConstructor"
      >&#8658;-E</a
      ><a name="22418"
      > </a
      ><a name="22419" href="StlcProp.html#22419" class="Bound"
      >&#8866;L</a
      ><a name="22421"
      > </a
      ><a name="22422" href="StlcProp.html#22422" class="Bound"
      >&#8866;M</a
      ><a name="22424" class="Symbol"
      >)</a
      ><a name="22425"
      > </a
      ><a name="22426" class="Symbol"
      >(</a
      ><a name="22427" href="Stlc.html#1864" class="InductiveConstructor"
      >&#958;&#183;&#8321;</a
      ><a name="22430"
      > </a
      ><a name="22431" href="StlcProp.html#22431" class="Bound"
      >L&#10233;L&#8242;</a
      ><a name="22435" class="Symbol"
      >)</a
      ><a name="22436"
      > </a
      ><a name="22437" class="Keyword"
      >with</a
      ><a name="22441"
      > </a
      ><a name="22442" href="StlcProp.html#20967" class="Function"
      >preservation</a
      ><a name="22454"
      > </a
      ><a name="22455" href="StlcProp.html#22419" class="Bound"
      >&#8866;L</a
      ><a name="22457"
      > </a
      ><a name="22458" href="StlcProp.html#22431" class="Bound"
      >L&#10233;L&#8242;</a
      ><a name="22462"
      >
</a
      ><a name="22463" class="Symbol"
      >...|</a
      ><a name="22467"
      > </a
      ><a name="22468" href="StlcProp.html#22468" class="Bound"
      >&#8866;L&#8242;</a
      ><a name="22471"
      > </a
      ><a name="22472" class="Symbol"
      >=</a
      ><a name="22473"
      > </a
      ><a name="22474" href="Stlc.html#3287" class="InductiveConstructor"
      >&#8658;-E</a
      ><a name="22477"
      > </a
      ><a name="22478" href="StlcProp.html#22468" class="Bound"
      >&#8866;L&#8242;</a
      ><a name="22481"
      > </a
      ><a name="22482" href="StlcProp.html#22422" class="Bound"
      >&#8866;M</a
      ><a name="22484"
      >
</a
      ><a name="22485" href="StlcProp.html#20967" class="Function"
      >preservation</a
      ><a name="22497"
      > </a
      ><a name="22498" class="Symbol"
      >(</a
      ><a name="22499" href="Stlc.html#3287" class="InductiveConstructor"
      >&#8658;-E</a
      ><a name="22502"
      > </a
      ><a name="22503" href="StlcProp.html#22503" class="Bound"
      >&#8866;L</a
      ><a name="22505"
      > </a
      ><a name="22506" href="StlcProp.html#22506" class="Bound"
      >&#8866;M</a
      ><a name="22508" class="Symbol"
      >)</a
      ><a name="22509"
      > </a
      ><a name="22510" class="Symbol"
      >(</a
      ><a name="22511" href="Stlc.html#1917" class="InductiveConstructor"
      >&#958;&#183;&#8322;</a
      ><a name="22514"
      > </a
      ><a name="22515" href="StlcProp.html#22515" class="Bound"
      >valueL</a
      ><a name="22521"
      > </a
      ><a name="22522" href="StlcProp.html#22522" class="Bound"
      >M&#10233;M&#8242;</a
      ><a name="22526" class="Symbol"
      >)</a
      ><a name="22527"
      > </a
      ><a name="22528" class="Keyword"
      >with</a
      ><a name="22532"
      > </a
      ><a name="22533" href="StlcProp.html#20967" class="Function"
      >preservation</a
      ><a name="22545"
      > </a
      ><a name="22546" href="StlcProp.html#22506" class="Bound"
      >&#8866;M</a
      ><a name="22548"
      > </a
      ><a name="22549" href="StlcProp.html#22522" class="Bound"
      >M&#10233;M&#8242;</a
      ><a name="22553"
      >
</a
      ><a name="22554" class="Symbol"
      >...|</a
      ><a name="22558"
      > </a
      ><a name="22559" href="StlcProp.html#22559" class="Bound"
      >&#8866;M&#8242;</a
      ><a name="22562"
      > </a
      ><a name="22563" class="Symbol"
      >=</a
      ><a name="22564"
      > </a
      ><a name="22565" href="Stlc.html#3287" class="InductiveConstructor"
      >&#8658;-E</a
      ><a name="22568"
      > </a
      ><a name="22569" href="StlcProp.html#22503" class="Bound"
      >&#8866;L</a
      ><a name="22571"
      > </a
      ><a name="22572" href="StlcProp.html#22559" class="Bound"
      >&#8866;M&#8242;</a
      ><a name="22575"
      >
</a
      ><a name="22576" href="StlcProp.html#20967" class="Function"
      >preservation</a
      ><a name="22588"
      > </a
      ><a name="22589" href="Stlc.html#3365" class="InductiveConstructor"
      >&#120121;-I&#8321;</a
      ><a name="22593"
      > </a
      ><a name="22594" class="Symbol"
      >()</a
      ><a name="22596"
      >
</a
      ><a name="22597" href="StlcProp.html#20967" class="Function"
      >preservation</a
      ><a name="22609"
      > </a
      ><a name="22610" href="Stlc.html#3399" class="InductiveConstructor"
      >&#120121;-I&#8322;</a
      ><a name="22614"
      > </a
      ><a name="22615" class="Symbol"
      >()</a
      ><a name="22617"
      >
</a
      ><a name="22618" href="StlcProp.html#20967" class="Function"
      >preservation</a
      ><a name="22630"
      > </a
      ><a name="22631" class="Symbol"
      >(</a
      ><a name="22632" href="Stlc.html#3434" class="InductiveConstructor"
      >&#120121;-E</a
      ><a name="22635"
      > </a
      ><a name="22636" href="Stlc.html#3365" class="InductiveConstructor"
      >&#120121;-I&#8321;</a
      ><a name="22640"
      > </a
      ><a name="22641" href="StlcProp.html#22641" class="Bound"
      >&#8866;M</a
      ><a name="22643"
      > </a
      ><a name="22644" href="StlcProp.html#22644" class="Bound"
      >&#8866;N</a
      ><a name="22646" class="Symbol"
      >)</a
      ><a name="22647"
      > </a
      ><a name="22648" href="Stlc.html#1984" class="InductiveConstructor"
      >&#946;if-true</a
      ><a name="22656"
      > </a
      ><a name="22657" class="Symbol"
      >=</a
      ><a name="22658"
      > </a
      ><a name="22659" href="StlcProp.html#22641" class="Bound"
      >&#8866;M</a
      ><a name="22661"
      >
</a
      ><a name="22662" href="StlcProp.html#20967" class="Function"
      >preservation</a
      ><a name="22674"
      > </a
      ><a name="22675" class="Symbol"
      >(</a
      ><a name="22676" href="Stlc.html#3434" class="InductiveConstructor"
      >&#120121;-E</a
      ><a name="22679"
      > </a
      ><a name="22680" href="Stlc.html#3399" class="InductiveConstructor"
      >&#120121;-I&#8322;</a
      ><a name="22684"
      > </a
      ><a name="22685" href="StlcProp.html#22685" class="Bound"
      >&#8866;M</a
      ><a name="22687"
      > </a
      ><a name="22688" href="StlcProp.html#22688" class="Bound"
      >&#8866;N</a
      ><a name="22690" class="Symbol"
      >)</a
      ><a name="22691"
      > </a
      ><a name="22692" href="Stlc.html#2037" class="InductiveConstructor"
      >&#946;if-false</a
      ><a name="22701"
      > </a
      ><a name="22702" class="Symbol"
      >=</a
      ><a name="22703"
      > </a
      ><a name="22704" href="StlcProp.html#22688" class="Bound"
      >&#8866;N</a
      ><a name="22706"
      >
</a
      ><a name="22707" href="StlcProp.html#20967" class="Function"
      >preservation</a
      ><a name="22719"
      > </a
      ><a name="22720" class="Symbol"
      >(</a
      ><a name="22721" href="Stlc.html#3434" class="InductiveConstructor"
      >&#120121;-E</a
      ><a name="22724"
      > </a
      ><a name="22725" href="StlcProp.html#22725" class="Bound"
      >&#8866;L</a
      ><a name="22727"
      > </a
      ><a name="22728" href="StlcProp.html#22728" class="Bound"
      >&#8866;M</a
      ><a name="22730"
      > </a
      ><a name="22731" href="StlcProp.html#22731" class="Bound"
      >&#8866;N</a
      ><a name="22733" class="Symbol"
      >)</a
      ><a name="22734"
      > </a
      ><a name="22735" class="Symbol"
      >(</a
      ><a name="22736" href="Stlc.html#2092" class="InductiveConstructor"
      >&#958;if</a
      ><a name="22739"
      > </a
      ><a name="22740" href="StlcProp.html#22740" class="Bound"
      >L&#10233;L&#8242;</a
      ><a name="22744" class="Symbol"
      >)</a
      ><a name="22745"
      > </a
      ><a name="22746" class="Keyword"
      >with</a
      ><a name="22750"
      > </a
      ><a name="22751" href="StlcProp.html#20967" class="Function"
      >preservation</a
      ><a name="22763"
      > </a
      ><a name="22764" href="StlcProp.html#22725" class="Bound"
      >&#8866;L</a
      ><a name="22766"
      > </a
      ><a name="22767" href="StlcProp.html#22740" class="Bound"
      >L&#10233;L&#8242;</a
      ><a name="22771"
      >
</a
      ><a name="22772" class="Symbol"
      >...|</a
      ><a name="22776"
      > </a
      ><a name="22777" href="StlcProp.html#22777" class="Bound"
      >&#8866;L&#8242;</a
      ><a name="22780"
      > </a
      ><a name="22781" class="Symbol"
      >=</a
      ><a name="22782"
      > </a
      ><a name="22783" href="Stlc.html#3434" class="InductiveConstructor"
      >&#120121;-E</a
      ><a name="22786"
      > </a
      ><a name="22787" href="StlcProp.html#22777" class="Bound"
      >&#8866;L&#8242;</a
      ><a name="22790"
      > </a
      ><a name="22791" href="StlcProp.html#22728" class="Bound"
      >&#8866;M</a
      ><a name="22793"
      > </a
      ><a name="22794" href="StlcProp.html#22731" class="Bound"
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

<a name="23447" href="StlcProp.html#23447" class="Function"
      >Normal</a
      ><a name="23453"
      > </a
      ><a name="23454" class="Symbol"
      >:</a
      ><a name="23455"
      > </a
      ><a name="23456" href="Stlc.html#708" class="Datatype"
      >Term</a
      ><a name="23460"
      > </a
      ><a name="23461" class="Symbol"
      >&#8594;</a
      ><a name="23462"
      > </a
      ><a name="23463" class="PrimitiveType"
      >Set</a
      ><a name="23466"
      >
</a
      ><a name="23467" href="StlcProp.html#23447" class="Function"
      >Normal</a
      ><a name="23473"
      > </a
      ><a name="23474" href="StlcProp.html#23474" class="Bound"
      >M</a
      ><a name="23475"
      > </a
      ><a name="23476" class="Symbol"
      >=</a
      ><a name="23477"
      > </a
      ><a name="23478" class="Symbol"
      >&#8704;</a
      ><a name="23479"
      > </a
      ><a name="23480" class="Symbol"
      >{</a
      ><a name="23481" href="StlcProp.html#23481" class="Bound"
      >N</a
      ><a name="23482" class="Symbol"
      >}</a
      ><a name="23483"
      > </a
      ><a name="23484" class="Symbol"
      >&#8594;</a
      ><a name="23485"
      > </a
      ><a name="23486" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#414" class="Function Operator"
      >&#172;</a
      ><a name="23487"
      > </a
      ><a name="23488" class="Symbol"
      >(</a
      ><a name="23489" href="StlcProp.html#23474" class="Bound"
      >M</a
      ><a name="23490"
      > </a
      ><a name="23491" href="Stlc.html#1762" class="Datatype Operator"
      >&#10233;</a
      ><a name="23492"
      > </a
      ><a name="23493" href="StlcProp.html#23481" class="Bound"
      >N</a
      ><a name="23494" class="Symbol"
      >)</a
      ><a name="23495"
      >

</a
      ><a name="23497" href="StlcProp.html#23497" class="Function"
      >Stuck</a
      ><a name="23502"
      > </a
      ><a name="23503" class="Symbol"
      >:</a
      ><a name="23504"
      > </a
      ><a name="23505" href="Stlc.html#708" class="Datatype"
      >Term</a
      ><a name="23509"
      > </a
      ><a name="23510" class="Symbol"
      >&#8594;</a
      ><a name="23511"
      > </a
      ><a name="23512" class="PrimitiveType"
      >Set</a
      ><a name="23515"
      >
</a
      ><a name="23516" href="StlcProp.html#23497" class="Function"
      >Stuck</a
      ><a name="23521"
      > </a
      ><a name="23522" href="StlcProp.html#23522" class="Bound"
      >M</a
      ><a name="23523"
      > </a
      ><a name="23524" class="Symbol"
      >=</a
      ><a name="23525"
      > </a
      ><a name="23526" href="StlcProp.html#23447" class="Function"
      >Normal</a
      ><a name="23532"
      > </a
      ><a name="23533" href="StlcProp.html#23522" class="Bound"
      >M</a
      ><a name="23534"
      > </a
      ><a name="23535" href="https://agda.github.io/agda-stdlib/Data.Product.html#1073" class="Function Operator"
      >&#215;</a
      ><a name="23536"
      > </a
      ><a name="23537" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#414" class="Function Operator"
      >&#172;</a
      ><a name="23538"
      > </a
      ><a name="23539" href="Stlc.html#1105" class="Datatype"
      >Value</a
      ><a name="23544"
      > </a
      ><a name="23545" href="StlcProp.html#23522" class="Bound"
      >M</a
      ><a name="23546"
      >

</a
      ><a name="23548" class="Keyword"
      >postulate</a
      ><a name="23557"
      >
  </a
      ><a name="23560" href="StlcProp.html#23560" class="Postulate"
      >Soundness</a
      ><a name="23569"
      > </a
      ><a name="23570" class="Symbol"
      >:</a
      ><a name="23571"
      > </a
      ><a name="23572" class="Symbol"
      >&#8704;</a
      ><a name="23573"
      > </a
      ><a name="23574" class="Symbol"
      >{</a
      ><a name="23575" href="StlcProp.html#23575" class="Bound"
      >M</a
      ><a name="23576"
      > </a
      ><a name="23577" href="StlcProp.html#23577" class="Bound"
      >N</a
      ><a name="23578"
      > </a
      ><a name="23579" href="StlcProp.html#23579" class="Bound"
      >A</a
      ><a name="23580" class="Symbol"
      >}</a
      ><a name="23581"
      > </a
      ><a name="23582" class="Symbol"
      >&#8594;</a
      ><a name="23583"
      > </a
      ><a name="23584" href="Maps.html#10265" class="Function"
      >&#8709;</a
      ><a name="23585"
      > </a
      ><a name="23586" href="Stlc.html#3112" class="Datatype Operator"
      >&#8866;</a
      ><a name="23587"
      > </a
      ><a name="23588" href="StlcProp.html#23575" class="Bound"
      >M</a
      ><a name="23589"
      > </a
      ><a name="23590" href="Stlc.html#3112" class="Datatype Operator"
      >&#8758;</a
      ><a name="23591"
      > </a
      ><a name="23592" href="StlcProp.html#23579" class="Bound"
      >A</a
      ><a name="23593"
      > </a
      ><a name="23594" class="Symbol"
      >&#8594;</a
      ><a name="23595"
      > </a
      ><a name="23596" href="StlcProp.html#23575" class="Bound"
      >M</a
      ><a name="23597"
      > </a
      ><a name="23598" href="Stlc.html#2287" class="Datatype Operator"
      >&#10233;*</a
      ><a name="23600"
      > </a
      ><a name="23601" href="StlcProp.html#23577" class="Bound"
      >N</a
      ><a name="23602"
      > </a
      ><a name="23603" class="Symbol"
      >&#8594;</a
      ><a name="23604"
      > </a
      ><a name="23605" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#414" class="Function Operator"
      >&#172;</a
      ><a name="23606"
      > </a
      ><a name="23607" class="Symbol"
      >(</a
      ><a name="23608" href="StlcProp.html#23497" class="Function"
      >Stuck</a
      ><a name="23613"
      > </a
      ><a name="23614" href="StlcProp.html#23577" class="Bound"
      >N</a
      ><a name="23615" class="Symbol"
      >)</a
      >

</pre>

<div class="hidden">
<pre class="Agda">

<a name="23663" href="StlcProp.html#23663" class="Function"
      >Soundness&#8242;</a
      ><a name="23673"
      > </a
      ><a name="23674" class="Symbol"
      >:</a
      ><a name="23675"
      > </a
      ><a name="23676" class="Symbol"
      >&#8704;</a
      ><a name="23677"
      > </a
      ><a name="23678" class="Symbol"
      >{</a
      ><a name="23679" href="StlcProp.html#23679" class="Bound"
      >M</a
      ><a name="23680"
      > </a
      ><a name="23681" href="StlcProp.html#23681" class="Bound"
      >N</a
      ><a name="23682"
      > </a
      ><a name="23683" href="StlcProp.html#23683" class="Bound"
      >A</a
      ><a name="23684" class="Symbol"
      >}</a
      ><a name="23685"
      > </a
      ><a name="23686" class="Symbol"
      >&#8594;</a
      ><a name="23687"
      > </a
      ><a name="23688" href="Maps.html#10265" class="Function"
      >&#8709;</a
      ><a name="23689"
      > </a
      ><a name="23690" href="Stlc.html#3112" class="Datatype Operator"
      >&#8866;</a
      ><a name="23691"
      > </a
      ><a name="23692" href="StlcProp.html#23679" class="Bound"
      >M</a
      ><a name="23693"
      > </a
      ><a name="23694" href="Stlc.html#3112" class="Datatype Operator"
      >&#8758;</a
      ><a name="23695"
      > </a
      ><a name="23696" href="StlcProp.html#23683" class="Bound"
      >A</a
      ><a name="23697"
      > </a
      ><a name="23698" class="Symbol"
      >&#8594;</a
      ><a name="23699"
      > </a
      ><a name="23700" href="StlcProp.html#23679" class="Bound"
      >M</a
      ><a name="23701"
      > </a
      ><a name="23702" href="Stlc.html#2287" class="Datatype Operator"
      >&#10233;*</a
      ><a name="23704"
      > </a
      ><a name="23705" href="StlcProp.html#23681" class="Bound"
      >N</a
      ><a name="23706"
      > </a
      ><a name="23707" class="Symbol"
      >&#8594;</a
      ><a name="23708"
      > </a
      ><a name="23709" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#414" class="Function Operator"
      >&#172;</a
      ><a name="23710"
      > </a
      ><a name="23711" class="Symbol"
      >(</a
      ><a name="23712" href="StlcProp.html#23497" class="Function"
      >Stuck</a
      ><a name="23717"
      > </a
      ><a name="23718" href="StlcProp.html#23681" class="Bound"
      >N</a
      ><a name="23719" class="Symbol"
      >)</a
      ><a name="23720"
      >
</a
      ><a name="23721" href="StlcProp.html#23663" class="Function"
      >Soundness&#8242;</a
      ><a name="23731"
      > </a
      ><a name="23732" href="StlcProp.html#23732" class="Bound"
      >&#8866;M</a
      ><a name="23734"
      > </a
      ><a name="23735" class="Symbol"
      >(</a
      ><a name="23736" href="StlcProp.html#23736" class="Bound"
      >M</a
      ><a name="23737"
      > </a
      ><a name="23738" href="Stlc.html#2320" class="InductiveConstructor Operator"
      >&#8718;</a
      ><a name="23739" class="Symbol"
      >)</a
      ><a name="23740"
      > </a
      ><a name="23741" class="Symbol"
      >(</a
      ><a name="23742" href="StlcProp.html#23742" class="Bound"
      >&#172;M&#10233;N</a
      ><a name="23746"
      > </a
      ><a name="23747" href="https://agda.github.io/agda-stdlib/Data.Product.html#509" class="InductiveConstructor Operator"
      >,</a
      ><a name="23748"
      > </a
      ><a name="23749" href="StlcProp.html#23749" class="Bound"
      >&#172;ValueM</a
      ><a name="23756" class="Symbol"
      >)</a
      ><a name="23757"
      > </a
      ><a name="23758" class="Keyword"
      >with</a
      ><a name="23762"
      > </a
      ><a name="23763" href="StlcProp.html#1970" class="Function"
      >progress</a
      ><a name="23771"
      > </a
      ><a name="23772" href="StlcProp.html#23732" class="Bound"
      >&#8866;M</a
      ><a name="23774"
      >
</a
      ><a name="23775" class="Symbol"
      >...</a
      ><a name="23778"
      > </a
      ><a name="23779" class="Symbol"
      >|</a
      ><a name="23780"
      > </a
      ><a name="23781" href="StlcProp.html#1893" class="InductiveConstructor"
      >steps</a
      ><a name="23786"
      > </a
      ><a name="23787" href="StlcProp.html#23787" class="Bound"
      >M&#10233;N</a
      ><a name="23790"
      >  </a
      ><a name="23792" class="Symbol"
      >=</a
      ><a name="23793"
      > </a
      ><a name="23794" href="StlcProp.html#23742" class="Bound"
      >&#172;M&#10233;N</a
      ><a name="23798"
      > </a
      ><a name="23799" href="StlcProp.html#23787" class="Bound"
      >M&#10233;N</a
      ><a name="23802"
      >
</a
      ><a name="23803" class="Symbol"
      >...</a
      ><a name="23806"
      > </a
      ><a name="23807" class="Symbol"
      >|</a
      ><a name="23808"
      > </a
      ><a name="23809" href="StlcProp.html#1932" class="InductiveConstructor"
      >done</a
      ><a name="23813"
      > </a
      ><a name="23814" href="StlcProp.html#23814" class="Bound"
      >ValueM</a
      ><a name="23820"
      >  </a
      ><a name="23822" class="Symbol"
      >=</a
      ><a name="23823"
      > </a
      ><a name="23824" href="StlcProp.html#23749" class="Bound"
      >&#172;ValueM</a
      ><a name="23831"
      > </a
      ><a name="23832" href="StlcProp.html#23814" class="Bound"
      >ValueM</a
      ><a name="23838"
      >
</a
      ><a name="23839" href="StlcProp.html#23663" class="Function"
      >Soundness&#8242;</a
      ><a name="23849"
      > </a
      ><a name="23850" class="Symbol"
      >{</a
      ><a name="23851" href="StlcProp.html#23851" class="Bound"
      >L</a
      ><a name="23852" class="Symbol"
      >}</a
      ><a name="23853"
      > </a
      ><a name="23854" class="Symbol"
      >{</a
      ><a name="23855" href="StlcProp.html#23855" class="Bound"
      >N</a
      ><a name="23856" class="Symbol"
      >}</a
      ><a name="23857"
      > </a
      ><a name="23858" class="Symbol"
      >{</a
      ><a name="23859" href="StlcProp.html#23859" class="Bound"
      >A</a
      ><a name="23860" class="Symbol"
      >}</a
      ><a name="23861"
      > </a
      ><a name="23862" href="StlcProp.html#23862" class="Bound"
      >&#8866;L</a
      ><a name="23864"
      > </a
      ><a name="23865" class="Symbol"
      >(</a
      ><a name="23866" href="Stlc.html#2340" class="InductiveConstructor Operator"
      >_&#10233;&#10216;_&#10217;_</a
      ><a name="23872"
      > </a
      ><a name="23873" class="DottedPattern Symbol"
      >.</a
      ><a name="23874" href="StlcProp.html#23851" class="DottedPattern Bound"
      >L</a
      ><a name="23875"
      > </a
      ><a name="23876" class="Symbol"
      >{</a
      ><a name="23877" href="StlcProp.html#23877" class="Bound"
      >M</a
      ><a name="23878" class="Symbol"
      >}</a
      ><a name="23879"
      > </a
      ><a name="23880" class="Symbol"
      >{</a
      ><a name="23881" class="DottedPattern Symbol"
      >.</a
      ><a name="23882" href="StlcProp.html#23855" class="DottedPattern Bound"
      >N</a
      ><a name="23883" class="Symbol"
      >}</a
      ><a name="23884"
      > </a
      ><a name="23885" href="StlcProp.html#23885" class="Bound"
      >L&#10233;M</a
      ><a name="23888"
      > </a
      ><a name="23889" href="StlcProp.html#23889" class="Bound"
      >M&#10233;*N</a
      ><a name="23893" class="Symbol"
      >)</a
      ><a name="23894"
      > </a
      ><a name="23895" class="Symbol"
      >=</a
      ><a name="23896"
      > </a
      ><a name="23897" href="StlcProp.html#23663" class="Function"
      >Soundness&#8242;</a
      ><a name="23907"
      > </a
      ><a name="23908" href="StlcProp.html#23926" class="Function"
      >&#8866;M</a
      ><a name="23910"
      > </a
      ><a name="23911" href="StlcProp.html#23889" class="Bound"
      >M&#10233;*N</a
      ><a name="23915"
      >
  </a
      ><a name="23918" class="Keyword"
      >where</a
      ><a name="23923"
      >
  </a
      ><a name="23926" href="StlcProp.html#23926" class="Function"
      >&#8866;M</a
      ><a name="23928"
      > </a
      ><a name="23929" class="Symbol"
      >:</a
      ><a name="23930"
      > </a
      ><a name="23931" href="Maps.html#10265" class="Function"
      >&#8709;</a
      ><a name="23932"
      > </a
      ><a name="23933" href="Stlc.html#3112" class="Datatype Operator"
      >&#8866;</a
      ><a name="23934"
      > </a
      ><a name="23935" href="StlcProp.html#23877" class="Bound"
      >M</a
      ><a name="23936"
      > </a
      ><a name="23937" href="Stlc.html#3112" class="Datatype Operator"
      >&#8758;</a
      ><a name="23938"
      > </a
      ><a name="23939" href="StlcProp.html#23859" class="Bound"
      >A</a
      ><a name="23940"
      >
  </a
      ><a name="23943" href="StlcProp.html#23926" class="Function"
      >&#8866;M</a
      ><a name="23945"
      > </a
      ><a name="23946" class="Symbol"
      >=</a
      ><a name="23947"
      > </a
      ><a name="23948" href="StlcProp.html#20967" class="Function"
      >preservation</a
      ><a name="23960"
      > </a
      ><a name="23961" href="StlcProp.html#23862" class="Bound"
      >&#8866;L</a
      ><a name="23963"
      > </a
      ><a name="23964" href="StlcProp.html#23885" class="Bound"
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

