---
title     : "StlcProp: Properties of STLC"
layout    : page
permalink : /StlcProp
---

In this chapter, we develop the fundamental theory of the Simply
Typed Lambda Calculus---in particular, the type safety
theorem.

## Imports

<pre class="Agda">{% raw %}
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
      ><a name="405" href="https://agda.github.io/agda-stdlib/Data.Product.html#823" class="Function"
      >&#8707;</a
      ><a name="406" class="Symbol"
      >;</a
      ><a name="407"
      > </a
      ><a name="408" href="https://agda.github.io/agda-stdlib/Data.Product.html#949" class="Function"
      >&#8707;&#8322;</a
      ><a name="410" class="Symbol"
      >;</a
      ><a name="411"
      > </a
      ><a name="412" href="https://agda.github.io/agda-stdlib/Data.Product.html#509" class="InductiveConstructor Operator"
      >_,_</a
      ><a name="415" class="Symbol"
      >;</a
      ><a name="416"
      > </a
      ><a name="417" href="https://agda.github.io/agda-stdlib/Data.Product.html#1621" class="Function Operator"
      >,_</a
      ><a name="419" class="Symbol"
      >)</a
      ><a name="420"
      >
</a
      ><a name="421" class="Keyword"
      >open</a
      ><a name="425"
      > </a
      ><a name="426" class="Keyword"
      >import</a
      ><a name="432"
      > </a
      ><a name="433" href="https://agda.github.io/agda-stdlib/Data.Sum.html#1" class="Module"
      >Data.Sum</a
      ><a name="441"
      > </a
      ><a name="442" class="Keyword"
      >using</a
      ><a name="447"
      > </a
      ><a name="448" class="Symbol"
      >(</a
      ><a name="449" href="https://agda.github.io/agda-stdlib/Data.Sum.html#433" class="Datatype Operator"
      >_&#8846;_</a
      ><a name="452" class="Symbol"
      >;</a
      ><a name="453"
      > </a
      ><a name="454" href="https://agda.github.io/agda-stdlib/Data.Sum.html#489" class="InductiveConstructor"
      >inj&#8321;</a
      ><a name="458" class="Symbol"
      >;</a
      ><a name="459"
      > </a
      ><a name="460" href="https://agda.github.io/agda-stdlib/Data.Sum.html#514" class="InductiveConstructor"
      >inj&#8322;</a
      ><a name="464" class="Symbol"
      >)</a
      ><a name="465"
      >
</a
      ><a name="466" class="Keyword"
      >open</a
      ><a name="470"
      > </a
      ><a name="471" class="Keyword"
      >import</a
      ><a name="477"
      > </a
      ><a name="478" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#1" class="Module"
      >Relation.Nullary</a
      ><a name="494"
      > </a
      ><a name="495" class="Keyword"
      >using</a
      ><a name="500"
      > </a
      ><a name="501" class="Symbol"
      >(</a
      ><a name="502" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#414" class="Function Operator"
      >&#172;_</a
      ><a name="504" class="Symbol"
      >;</a
      ><a name="505"
      > </a
      ><a name="506" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#484" class="Datatype"
      >Dec</a
      ><a name="509" class="Symbol"
      >;</a
      ><a name="510"
      > </a
      ><a name="511" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#520" class="InductiveConstructor"
      >yes</a
      ><a name="514" class="Symbol"
      >;</a
      ><a name="515"
      > </a
      ><a name="516" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#547" class="InductiveConstructor"
      >no</a
      ><a name="518" class="Symbol"
      >)</a
      ><a name="519"
      >
</a
      ><a name="520" class="Keyword"
      >open</a
      ><a name="524"
      > </a
      ><a name="525" class="Keyword"
      >import</a
      ><a name="531"
      > </a
      ><a name="532" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#1" class="Module"
      >Relation.Binary.PropositionalEquality</a
      ><a name="569"
      > </a
      ><a name="570" class="Keyword"
      >using</a
      ><a name="575"
      > </a
      ><a name="576" class="Symbol"
      >(</a
      ><a name="577" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >_&#8801;_</a
      ><a name="580" class="Symbol"
      >;</a
      ><a name="581"
      > </a
      ><a name="582" href="https://agda.github.io/agda-stdlib/Relation.Binary.Core.html#4493" class="Function Operator"
      >_&#8802;_</a
      ><a name="585" class="Symbol"
      >;</a
      ><a name="586"
      > </a
      ><a name="587" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="591" class="Symbol"
      >;</a
      ><a name="592"
      > </a
      ><a name="593" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.Core.html#632" class="Function"
      >trans</a
      ><a name="598" class="Symbol"
      >;</a
      ><a name="599"
      > </a
      ><a name="600" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.Core.html#565" class="Function"
      >sym</a
      ><a name="603" class="Symbol"
      >)</a
      ><a name="604"
      >
</a
      ><a name="605" class="Keyword"
      >open</a
      ><a name="609"
      > </a
      ><a name="610" class="Keyword"
      >import</a
      ><a name="616"
      > </a
      ><a name="617" class="Module"
      >Maps</a
      ><a name="621"
      >
</a
      ><a name="622" class="Keyword"
      >open</a
      ><a name="626"
      > </a
      ><a name="627" class="Module"
      >Maps.</a
      ><a name="632" href="Maps.html#10315" class="Module"
      >PartialMap</a
      ><a name="642"
      > </a
      ><a name="643" class="Keyword"
      >using</a
      ><a name="648"
      > </a
      ><a name="649" class="Symbol"
      >(</a
      ><a name="650" href="Maps.html#10359" class="Function"
      >&#8709;</a
      ><a name="651" class="Symbol"
      >;</a
      ><a name="652"
      > </a
      ><a name="653" href="Maps.html#10667" class="Function"
      >apply-&#8709;</a
      ><a name="660" class="Symbol"
      >;</a
      ><a name="661"
      > </a
      ><a name="662" href="Maps.html#11585" class="Function"
      >update-permute</a
      ><a name="676" class="Symbol"
      >)</a
      ><a name="677"
      > </a
      ><a name="678" class="Keyword"
      >renaming</a
      ><a name="686"
      > </a
      ><a name="687" class="Symbol"
      >(</a
      ><a name="688" href="Maps.html#10462" class="Function Operator"
      >_,_&#8614;_</a
      ><a name="693"
      > </a
      ><a name="694" class="Symbol"
      >to</a
      ><a name="696"
      > </a
      ><a name="697" href="Maps.html#10462" class="Function Operator"
      >_,_&#8758;_</a
      ><a name="702" class="Symbol"
      >)</a
      ><a name="703"
      >
</a
      ><a name="704" class="Keyword"
      >open</a
      ><a name="708"
      > </a
      ><a name="709" class="Keyword"
      >import</a
      ><a name="715"
      > </a
      ><a name="716" class="Module"
      >Stlc</a
      >
{% endraw %}</pre>


## Canonical Forms

As we saw for the simple calculus in Chapter [Types]({{ "Types" | relative_url }}),
the first step in establishing basic properties of reduction and typing
is to identify the possible _canonical forms_ (i.e., well-typed closed values)
belonging to each type.  For function types the canonical forms are lambda-abstractions,
while for boolean types they are values `true` and `false`.  

<pre class="Agda">{% raw %}
<a name="1154" class="Keyword"
      >data</a
      ><a name="1158"
      > </a
      ><a name="1159" href="StlcProp.html#1159" class="Datatype Operator"
      >canonical_for_</a
      ><a name="1173"
      > </a
      ><a name="1174" class="Symbol"
      >:</a
      ><a name="1175"
      > </a
      ><a name="1176" href="Stlc.html#715" class="Datatype"
      >Term</a
      ><a name="1180"
      > </a
      ><a name="1181" class="Symbol"
      >&#8594;</a
      ><a name="1182"
      > </a
      ><a name="1183" href="Stlc.html#597" class="Datatype"
      >Type</a
      ><a name="1187"
      > </a
      ><a name="1188" class="Symbol"
      >&#8594;</a
      ><a name="1189"
      > </a
      ><a name="1190" class="PrimitiveType"
      >Set</a
      ><a name="1193"
      > </a
      ><a name="1194" class="Keyword"
      >where</a
      ><a name="1199"
      >
  </a
      ><a name="1202" href="StlcProp.html#1202" class="InductiveConstructor"
      >canonical-&#955;</a
      ><a name="1213"
      > </a
      ><a name="1214" class="Symbol"
      >:</a
      ><a name="1215"
      > </a
      ><a name="1216" class="Symbol"
      >&#8704;</a
      ><a name="1217"
      > </a
      ><a name="1218" class="Symbol"
      >{</a
      ><a name="1219" href="StlcProp.html#1219" class="Bound"
      >x</a
      ><a name="1220"
      > </a
      ><a name="1221" href="StlcProp.html#1221" class="Bound"
      >A</a
      ><a name="1222"
      > </a
      ><a name="1223" href="StlcProp.html#1223" class="Bound"
      >N</a
      ><a name="1224"
      > </a
      ><a name="1225" href="StlcProp.html#1225" class="Bound"
      >B</a
      ><a name="1226" class="Symbol"
      >}</a
      ><a name="1227"
      > </a
      ><a name="1228" class="Symbol"
      >&#8594;</a
      ><a name="1229"
      > </a
      ><a name="1230" href="StlcProp.html#1159" class="Datatype Operator"
      >canonical</a
      ><a name="1239"
      > </a
      ><a name="1240" class="Symbol"
      >(</a
      ><a name="1241" href="Stlc.html#752" class="InductiveConstructor Operator"
      >&#955;[</a
      ><a name="1243"
      > </a
      ><a name="1244" href="StlcProp.html#1219" class="Bound"
      >x</a
      ><a name="1245"
      > </a
      ><a name="1246" href="Stlc.html#752" class="InductiveConstructor Operator"
      >&#8758;</a
      ><a name="1247"
      > </a
      ><a name="1248" href="StlcProp.html#1221" class="Bound"
      >A</a
      ><a name="1249"
      > </a
      ><a name="1250" href="Stlc.html#752" class="InductiveConstructor Operator"
      >]</a
      ><a name="1251"
      > </a
      ><a name="1252" href="StlcProp.html#1223" class="Bound"
      >N</a
      ><a name="1253" class="Symbol"
      >)</a
      ><a name="1254"
      > </a
      ><a name="1255" href="StlcProp.html#1159" class="Datatype Operator"
      >for</a
      ><a name="1258"
      > </a
      ><a name="1259" class="Symbol"
      >(</a
      ><a name="1260" href="StlcProp.html#1221" class="Bound"
      >A</a
      ><a name="1261"
      > </a
      ><a name="1262" href="Stlc.html#627" class="InductiveConstructor Operator"
      >&#8658;</a
      ><a name="1263"
      > </a
      ><a name="1264" href="StlcProp.html#1225" class="Bound"
      >B</a
      ><a name="1265" class="Symbol"
      >)</a
      ><a name="1266"
      >
  </a
      ><a name="1269" href="StlcProp.html#1269" class="InductiveConstructor"
      >canonical-true</a
      ><a name="1283"
      > </a
      ><a name="1284" class="Symbol"
      >:</a
      ><a name="1285"
      > </a
      ><a name="1286" href="StlcProp.html#1159" class="Datatype Operator"
      >canonical</a
      ><a name="1295"
      > </a
      ><a name="1296" href="Stlc.html#815" class="InductiveConstructor"
      >true</a
      ><a name="1300"
      > </a
      ><a name="1301" href="StlcProp.html#1159" class="Datatype Operator"
      >for</a
      ><a name="1304"
      > </a
      ><a name="1305" href="Stlc.html#616" class="InductiveConstructor"
      >&#120121;</a
      ><a name="1306"
      >
  </a
      ><a name="1309" href="StlcProp.html#1309" class="InductiveConstructor"
      >canonical-false</a
      ><a name="1324"
      > </a
      ><a name="1325" class="Symbol"
      >:</a
      ><a name="1326"
      > </a
      ><a name="1327" href="StlcProp.html#1159" class="Datatype Operator"
      >canonical</a
      ><a name="1336"
      > </a
      ><a name="1337" href="Stlc.html#829" class="InductiveConstructor"
      >false</a
      ><a name="1342"
      > </a
      ><a name="1343" href="StlcProp.html#1159" class="Datatype Operator"
      >for</a
      ><a name="1346"
      > </a
      ><a name="1347" href="Stlc.html#616" class="InductiveConstructor"
      >&#120121;</a
      ><a name="1348"
      >

</a
      ><a name="1350" href="StlcProp.html#1350" class="Function"
      >canonicalFormsLemma</a
      ><a name="1369"
      > </a
      ><a name="1370" class="Symbol"
      >:</a
      ><a name="1371"
      > </a
      ><a name="1372" class="Symbol"
      >&#8704;</a
      ><a name="1373"
      > </a
      ><a name="1374" class="Symbol"
      >{</a
      ><a name="1375" href="StlcProp.html#1375" class="Bound"
      >L</a
      ><a name="1376"
      > </a
      ><a name="1377" href="StlcProp.html#1377" class="Bound"
      >A</a
      ><a name="1378" class="Symbol"
      >}</a
      ><a name="1379"
      > </a
      ><a name="1380" class="Symbol"
      >&#8594;</a
      ><a name="1381"
      > </a
      ><a name="1382" href="Maps.html#10359" class="Function"
      >&#8709;</a
      ><a name="1383"
      > </a
      ><a name="1384" href="Stlc.html#3408" class="Datatype Operator"
      >&#8866;</a
      ><a name="1385"
      > </a
      ><a name="1386" href="StlcProp.html#1375" class="Bound"
      >L</a
      ><a name="1387"
      > </a
      ><a name="1388" href="Stlc.html#3408" class="Datatype Operator"
      >&#8758;</a
      ><a name="1389"
      > </a
      ><a name="1390" href="StlcProp.html#1377" class="Bound"
      >A</a
      ><a name="1391"
      > </a
      ><a name="1392" class="Symbol"
      >&#8594;</a
      ><a name="1393"
      > </a
      ><a name="1394" href="Stlc.html#1126" class="Datatype"
      >Value</a
      ><a name="1399"
      > </a
      ><a name="1400" href="StlcProp.html#1375" class="Bound"
      >L</a
      ><a name="1401"
      > </a
      ><a name="1402" class="Symbol"
      >&#8594;</a
      ><a name="1403"
      > </a
      ><a name="1404" href="StlcProp.html#1159" class="Datatype Operator"
      >canonical</a
      ><a name="1413"
      > </a
      ><a name="1414" href="StlcProp.html#1375" class="Bound"
      >L</a
      ><a name="1415"
      > </a
      ><a name="1416" href="StlcProp.html#1159" class="Datatype Operator"
      >for</a
      ><a name="1419"
      > </a
      ><a name="1420" href="StlcProp.html#1377" class="Bound"
      >A</a
      ><a name="1421"
      >
</a
      ><a name="1422" href="StlcProp.html#1350" class="Function"
      >canonicalFormsLemma</a
      ><a name="1441"
      > </a
      ><a name="1442" class="Symbol"
      >(</a
      ><a name="1443" href="Stlc.html#3452" class="InductiveConstructor"
      >Ax</a
      ><a name="1445"
      > </a
      ><a name="1446" href="StlcProp.html#1446" class="Bound"
      >&#8866;x</a
      ><a name="1448" class="Symbol"
      >)</a
      ><a name="1449"
      > </a
      ><a name="1450" class="Symbol"
      >()</a
      ><a name="1452"
      >
</a
      ><a name="1453" href="StlcProp.html#1350" class="Function"
      >canonicalFormsLemma</a
      ><a name="1472"
      > </a
      ><a name="1473" class="Symbol"
      >(</a
      ><a name="1474" href="Stlc.html#3508" class="InductiveConstructor"
      >&#8658;-I</a
      ><a name="1477"
      > </a
      ><a name="1478" href="StlcProp.html#1478" class="Bound"
      >&#8866;N</a
      ><a name="1480" class="Symbol"
      >)</a
      ><a name="1481"
      > </a
      ><a name="1482" href="Stlc.html#1153" class="InductiveConstructor"
      >value-&#955;</a
      ><a name="1489"
      > </a
      ><a name="1490" class="Symbol"
      >=</a
      ><a name="1491"
      > </a
      ><a name="1492" href="StlcProp.html#1202" class="InductiveConstructor"
      >canonical-&#955;</a
      ><a name="1503"
      >
</a
      ><a name="1504" href="StlcProp.html#1350" class="Function"
      >canonicalFormsLemma</a
      ><a name="1523"
      > </a
      ><a name="1524" class="Symbol"
      >(</a
      ><a name="1525" href="Stlc.html#3585" class="InductiveConstructor"
      >&#8658;-E</a
      ><a name="1528"
      > </a
      ><a name="1529" href="StlcProp.html#1529" class="Bound"
      >&#8866;L</a
      ><a name="1531"
      > </a
      ><a name="1532" href="StlcProp.html#1532" class="Bound"
      >&#8866;M</a
      ><a name="1534" class="Symbol"
      >)</a
      ><a name="1535"
      > </a
      ><a name="1536" class="Symbol"
      >()</a
      ><a name="1538"
      >
</a
      ><a name="1539" href="StlcProp.html#1350" class="Function"
      >canonicalFormsLemma</a
      ><a name="1558"
      > </a
      ><a name="1559" href="Stlc.html#3663" class="InductiveConstructor"
      >&#120121;-I&#8321;</a
      ><a name="1563"
      > </a
      ><a name="1564" href="Stlc.html#1202" class="InductiveConstructor"
      >value-true</a
      ><a name="1574"
      > </a
      ><a name="1575" class="Symbol"
      >=</a
      ><a name="1576"
      > </a
      ><a name="1577" href="StlcProp.html#1269" class="InductiveConstructor"
      >canonical-true</a
      ><a name="1591"
      >
</a
      ><a name="1592" href="StlcProp.html#1350" class="Function"
      >canonicalFormsLemma</a
      ><a name="1611"
      > </a
      ><a name="1612" href="Stlc.html#3697" class="InductiveConstructor"
      >&#120121;-I&#8322;</a
      ><a name="1616"
      > </a
      ><a name="1617" href="Stlc.html#1229" class="InductiveConstructor"
      >value-false</a
      ><a name="1628"
      > </a
      ><a name="1629" class="Symbol"
      >=</a
      ><a name="1630"
      > </a
      ><a name="1631" href="StlcProp.html#1309" class="InductiveConstructor"
      >canonical-false</a
      ><a name="1646"
      >
</a
      ><a name="1647" href="StlcProp.html#1350" class="Function"
      >canonicalFormsLemma</a
      ><a name="1666"
      > </a
      ><a name="1667" class="Symbol"
      >(</a
      ><a name="1668" href="Stlc.html#3732" class="InductiveConstructor"
      >&#120121;-E</a
      ><a name="1671"
      > </a
      ><a name="1672" href="StlcProp.html#1672" class="Bound"
      >&#8866;L</a
      ><a name="1674"
      > </a
      ><a name="1675" href="StlcProp.html#1675" class="Bound"
      >&#8866;M</a
      ><a name="1677"
      > </a
      ><a name="1678" href="StlcProp.html#1678" class="Bound"
      >&#8866;N</a
      ><a name="1680" class="Symbol"
      >)</a
      ><a name="1681"
      > </a
      ><a name="1682" class="Symbol"
      >()</a
      >
{% endraw %}</pre>

## Progress

As before, the _progress_ theorem tells us that closed, well-typed
terms are not stuck: either a well-typed term is a value, or it
can take a reduction step.  

<pre class="Agda">{% raw %}
<a name="1884" href="StlcProp.html#1884" class="Function"
      >progress</a
      ><a name="1892"
      > </a
      ><a name="1893" class="Symbol"
      >:</a
      ><a name="1894"
      > </a
      ><a name="1895" class="Symbol"
      >&#8704;</a
      ><a name="1896"
      > </a
      ><a name="1897" class="Symbol"
      >{</a
      ><a name="1898" href="StlcProp.html#1898" class="Bound"
      >M</a
      ><a name="1899"
      > </a
      ><a name="1900" href="StlcProp.html#1900" class="Bound"
      >A</a
      ><a name="1901" class="Symbol"
      >}</a
      ><a name="1902"
      > </a
      ><a name="1903" class="Symbol"
      >&#8594;</a
      ><a name="1904"
      > </a
      ><a name="1905" href="Maps.html#10359" class="Function"
      >&#8709;</a
      ><a name="1906"
      > </a
      ><a name="1907" href="Stlc.html#3408" class="Datatype Operator"
      >&#8866;</a
      ><a name="1908"
      > </a
      ><a name="1909" href="StlcProp.html#1898" class="Bound"
      >M</a
      ><a name="1910"
      > </a
      ><a name="1911" href="Stlc.html#3408" class="Datatype Operator"
      >&#8758;</a
      ><a name="1912"
      > </a
      ><a name="1913" href="StlcProp.html#1900" class="Bound"
      >A</a
      ><a name="1914"
      > </a
      ><a name="1915" class="Symbol"
      >&#8594;</a
      ><a name="1916"
      > </a
      ><a name="1917" href="Stlc.html#1126" class="Datatype"
      >Value</a
      ><a name="1922"
      > </a
      ><a name="1923" href="StlcProp.html#1898" class="Bound"
      >M</a
      ><a name="1924"
      > </a
      ><a name="1925" href="https://agda.github.io/agda-stdlib/Data.Sum.html#433" class="Datatype Operator"
      >&#8846;</a
      ><a name="1926"
      > </a
      ><a name="1927" href="https://agda.github.io/agda-stdlib/Data.Product.html#823" class="Function"
      >&#8707;</a
      ><a name="1928"
      > </a
      ><a name="1929" class="Symbol"
      >&#955;</a
      ><a name="1930"
      > </a
      ><a name="1931" href="StlcProp.html#1931" class="Bound"
      >N</a
      ><a name="1932"
      > </a
      ><a name="1933" class="Symbol"
      >&#8594;</a
      ><a name="1934"
      > </a
      ><a name="1935" href="StlcProp.html#1898" class="Bound"
      >M</a
      ><a name="1936"
      > </a
      ><a name="1937" href="Stlc.html#1787" class="Datatype Operator"
      >&#10233;</a
      ><a name="1938"
      > </a
      ><a name="1939" href="StlcProp.html#1931" class="Bound"
      >N</a
      >
{% endraw %}</pre>

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
    hypotheses.  By the first induction hypothesis, either `L` is a
    value or it can take a step.

    - If `L` is a value then consider `M`. By the second induction
      hypothesis, either `M` is a value or it can take a step.

      - If `M` is a value, then since `L` is a value with a
        function type we know it must be a lambda abstraction,
        and hence `L · M` can take a step by `β⇒`.

      - If `M` can take a step, then so can `L · M` by `γ⇒₂`.

    - If `L` can take a step, then so can `L · M` by `γ⇒₁`.

  - If the last rule of the derivation is `𝔹-E`, then the term has
    the form `if L then M else N` where `L` has type `𝔹`.
    By the induction hypothesis, either `L` is a value or it can
    take a step.

    - If `L` is a value, then since it has type boolean it must be
      either `true` or `false`.

      - If `L` is `true`, then then term steps by `β𝔹₁`

      - If `L` is `false`, then then term steps by `β𝔹₂`

    - If `L` can take a step, then so can `if L then M else N` by `γ𝔹`.

This completes the proof.

<pre class="Agda">{% raw %}
<a name="3699" href="StlcProp.html#1884" class="Function"
      >progress</a
      ><a name="3707"
      > </a
      ><a name="3708" class="Symbol"
      >(</a
      ><a name="3709" href="Stlc.html#3452" class="InductiveConstructor"
      >Ax</a
      ><a name="3711"
      > </a
      ><a name="3712" class="Symbol"
      >())</a
      ><a name="3715"
      >
</a
      ><a name="3716" href="StlcProp.html#1884" class="Function"
      >progress</a
      ><a name="3724"
      > </a
      ><a name="3725" class="Symbol"
      >(</a
      ><a name="3726" href="Stlc.html#3508" class="InductiveConstructor"
      >&#8658;-I</a
      ><a name="3729"
      > </a
      ><a name="3730" href="StlcProp.html#3730" class="Bound"
      >&#8866;N</a
      ><a name="3732" class="Symbol"
      >)</a
      ><a name="3733"
      > </a
      ><a name="3734" class="Symbol"
      >=</a
      ><a name="3735"
      > </a
      ><a name="3736" href="https://agda.github.io/agda-stdlib/Data.Sum.html#489" class="InductiveConstructor"
      >inj&#8321;</a
      ><a name="3740"
      > </a
      ><a name="3741" href="Stlc.html#1153" class="InductiveConstructor"
      >value-&#955;</a
      ><a name="3748"
      >
</a
      ><a name="3749" href="StlcProp.html#1884" class="Function"
      >progress</a
      ><a name="3757"
      > </a
      ><a name="3758" class="Symbol"
      >(</a
      ><a name="3759" href="Stlc.html#3585" class="InductiveConstructor"
      >&#8658;-E</a
      ><a name="3762"
      > </a
      ><a name="3763" class="Symbol"
      >{</a
      ><a name="3764" href="StlcProp.html#3764" class="Bound"
      >&#915;</a
      ><a name="3765" class="Symbol"
      >}</a
      ><a name="3766"
      > </a
      ><a name="3767" class="Symbol"
      >{</a
      ><a name="3768" href="StlcProp.html#3768" class="Bound"
      >L</a
      ><a name="3769" class="Symbol"
      >}</a
      ><a name="3770"
      > </a
      ><a name="3771" class="Symbol"
      >{</a
      ><a name="3772" href="StlcProp.html#3772" class="Bound"
      >M</a
      ><a name="3773" class="Symbol"
      >}</a
      ><a name="3774"
      > </a
      ><a name="3775" class="Symbol"
      >{</a
      ><a name="3776" href="StlcProp.html#3776" class="Bound"
      >A</a
      ><a name="3777" class="Symbol"
      >}</a
      ><a name="3778"
      > </a
      ><a name="3779" class="Symbol"
      >{</a
      ><a name="3780" href="StlcProp.html#3780" class="Bound"
      >B</a
      ><a name="3781" class="Symbol"
      >}</a
      ><a name="3782"
      > </a
      ><a name="3783" href="StlcProp.html#3783" class="Bound"
      >&#8866;L</a
      ><a name="3785"
      > </a
      ><a name="3786" href="StlcProp.html#3786" class="Bound"
      >&#8866;M</a
      ><a name="3788" class="Symbol"
      >)</a
      ><a name="3789"
      > </a
      ><a name="3790" class="Keyword"
      >with</a
      ><a name="3794"
      > </a
      ><a name="3795" href="StlcProp.html#1884" class="Function"
      >progress</a
      ><a name="3803"
      > </a
      ><a name="3804" href="StlcProp.html#3783" class="Bound"
      >&#8866;L</a
      ><a name="3806"
      >
</a
      ><a name="3807" class="Symbol"
      >...</a
      ><a name="3810"
      > </a
      ><a name="3811" class="Symbol"
      >|</a
      ><a name="3812"
      > </a
      ><a name="3813" href="https://agda.github.io/agda-stdlib/Data.Sum.html#514" class="InductiveConstructor"
      >inj&#8322;</a
      ><a name="3817"
      > </a
      ><a name="3818" class="Symbol"
      >(</a
      ><a name="3819" href="StlcProp.html#3819" class="Bound"
      >L&#8242;</a
      ><a name="3821"
      > </a
      ><a name="3822" href="https://agda.github.io/agda-stdlib/Data.Product.html#509" class="InductiveConstructor Operator"
      >,</a
      ><a name="3823"
      > </a
      ><a name="3824" href="StlcProp.html#3824" class="Bound"
      >L&#10233;L&#8242;</a
      ><a name="3828" class="Symbol"
      >)</a
      ><a name="3829"
      > </a
      ><a name="3830" class="Symbol"
      >=</a
      ><a name="3831"
      > </a
      ><a name="3832" href="https://agda.github.io/agda-stdlib/Data.Sum.html#514" class="InductiveConstructor"
      >inj&#8322;</a
      ><a name="3836"
      > </a
      ><a name="3837" class="Symbol"
      >(</a
      ><a name="3838" href="StlcProp.html#3819" class="Bound"
      >L&#8242;</a
      ><a name="3840"
      > </a
      ><a name="3841" href="Stlc.html#788" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="3842"
      > </a
      ><a name="3843" href="StlcProp.html#3772" class="Bound"
      >M</a
      ><a name="3844"
      > </a
      ><a name="3845" href="https://agda.github.io/agda-stdlib/Data.Product.html#509" class="InductiveConstructor Operator"
      >,</a
      ><a name="3846"
      > </a
      ><a name="3847" href="Stlc.html#1888" class="InductiveConstructor"
      >&#947;&#8658;&#8321;</a
      ><a name="3850"
      > </a
      ><a name="3851" href="StlcProp.html#3824" class="Bound"
      >L&#10233;L&#8242;</a
      ><a name="3855" class="Symbol"
      >)</a
      ><a name="3856"
      >
</a
      ><a name="3857" class="Symbol"
      >...</a
      ><a name="3860"
      > </a
      ><a name="3861" class="Symbol"
      >|</a
      ><a name="3862"
      > </a
      ><a name="3863" href="https://agda.github.io/agda-stdlib/Data.Sum.html#489" class="InductiveConstructor"
      >inj&#8321;</a
      ><a name="3867"
      > </a
      ><a name="3868" href="StlcProp.html#3868" class="Bound"
      >valueL</a
      ><a name="3874"
      > </a
      ><a name="3875" class="Keyword"
      >with</a
      ><a name="3879"
      > </a
      ><a name="3880" href="StlcProp.html#1884" class="Function"
      >progress</a
      ><a name="3888"
      > </a
      ><a name="3889" href="StlcProp.html#3786" class="Bound"
      >&#8866;M</a
      ><a name="3891"
      >
</a
      ><a name="3892" class="Symbol"
      >...</a
      ><a name="3895"
      > </a
      ><a name="3896" class="Symbol"
      >|</a
      ><a name="3897"
      > </a
      ><a name="3898" href="https://agda.github.io/agda-stdlib/Data.Sum.html#514" class="InductiveConstructor"
      >inj&#8322;</a
      ><a name="3902"
      > </a
      ><a name="3903" class="Symbol"
      >(</a
      ><a name="3904" href="StlcProp.html#3904" class="Bound"
      >M&#8242;</a
      ><a name="3906"
      > </a
      ><a name="3907" href="https://agda.github.io/agda-stdlib/Data.Product.html#509" class="InductiveConstructor Operator"
      >,</a
      ><a name="3908"
      > </a
      ><a name="3909" href="StlcProp.html#3909" class="Bound"
      >M&#10233;M&#8242;</a
      ><a name="3913" class="Symbol"
      >)</a
      ><a name="3914"
      > </a
      ><a name="3915" class="Symbol"
      >=</a
      ><a name="3916"
      > </a
      ><a name="3917" href="https://agda.github.io/agda-stdlib/Data.Sum.html#514" class="InductiveConstructor"
      >inj&#8322;</a
      ><a name="3921"
      > </a
      ><a name="3922" class="Symbol"
      >(</a
      ><a name="3923" href="StlcProp.html#3768" class="Bound"
      >L</a
      ><a name="3924"
      > </a
      ><a name="3925" href="Stlc.html#788" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="3926"
      > </a
      ><a name="3927" href="StlcProp.html#3904" class="Bound"
      >M&#8242;</a
      ><a name="3929"
      > </a
      ><a name="3930" href="https://agda.github.io/agda-stdlib/Data.Product.html#509" class="InductiveConstructor Operator"
      >,</a
      ><a name="3931"
      > </a
      ><a name="3932" href="Stlc.html#1941" class="InductiveConstructor"
      >&#947;&#8658;&#8322;</a
      ><a name="3935"
      > </a
      ><a name="3936" href="StlcProp.html#3868" class="Bound"
      >valueL</a
      ><a name="3942"
      > </a
      ><a name="3943" href="StlcProp.html#3909" class="Bound"
      >M&#10233;M&#8242;</a
      ><a name="3947" class="Symbol"
      >)</a
      ><a name="3948"
      >
</a
      ><a name="3949" class="Symbol"
      >...</a
      ><a name="3952"
      > </a
      ><a name="3953" class="Symbol"
      >|</a
      ><a name="3954"
      > </a
      ><a name="3955" href="https://agda.github.io/agda-stdlib/Data.Sum.html#489" class="InductiveConstructor"
      >inj&#8321;</a
      ><a name="3959"
      > </a
      ><a name="3960" href="StlcProp.html#3960" class="Bound"
      >valueM</a
      ><a name="3966"
      > </a
      ><a name="3967" class="Keyword"
      >with</a
      ><a name="3971"
      > </a
      ><a name="3972" href="StlcProp.html#1350" class="Function"
      >canonicalFormsLemma</a
      ><a name="3991"
      > </a
      ><a name="3992" href="StlcProp.html#3783" class="Bound"
      >&#8866;L</a
      ><a name="3994"
      > </a
      ><a name="3995" href="StlcProp.html#3868" class="Bound"
      >valueL</a
      ><a name="4001"
      >
</a
      ><a name="4002" class="Symbol"
      >...</a
      ><a name="4005"
      > </a
      ><a name="4006" class="Symbol"
      >|</a
      ><a name="4007"
      > </a
      ><a name="4008" href="StlcProp.html#1202" class="InductiveConstructor"
      >canonical-&#955;</a
      ><a name="4019"
      > </a
      ><a name="4020" class="Symbol"
      >{</a
      ><a name="4021" href="StlcProp.html#4021" class="Bound"
      >x</a
      ><a name="4022" class="Symbol"
      >}</a
      ><a name="4023"
      > </a
      ><a name="4024" class="Symbol"
      >{</a
      ><a name="4025" class="DottedPattern Symbol"
      >.</a
      ><a name="4026" href="StlcProp.html#3776" class="DottedPattern Bound"
      >A</a
      ><a name="4027" class="Symbol"
      >}</a
      ><a name="4028"
      > </a
      ><a name="4029" class="Symbol"
      >{</a
      ><a name="4030" href="StlcProp.html#4030" class="Bound"
      >N</a
      ><a name="4031" class="Symbol"
      >}</a
      ><a name="4032"
      > </a
      ><a name="4033" class="Symbol"
      >{</a
      ><a name="4034" class="DottedPattern Symbol"
      >.</a
      ><a name="4035" href="StlcProp.html#3780" class="DottedPattern Bound"
      >B</a
      ><a name="4036" class="Symbol"
      >}</a
      ><a name="4037"
      > </a
      ><a name="4038" class="Symbol"
      >=</a
      ><a name="4039"
      > </a
      ><a name="4040" href="https://agda.github.io/agda-stdlib/Data.Sum.html#514" class="InductiveConstructor"
      >inj&#8322;</a
      ><a name="4044"
      > </a
      ><a name="4045" class="Symbol"
      >((</a
      ><a name="4047" href="StlcProp.html#4030" class="Bound"
      >N</a
      ><a name="4048"
      > </a
      ><a name="4049" href="Stlc.html#1297" class="Function Operator"
      >[</a
      ><a name="4050"
      > </a
      ><a name="4051" href="StlcProp.html#4021" class="Bound"
      >x</a
      ><a name="4052"
      > </a
      ><a name="4053" href="Stlc.html#1297" class="Function Operator"
      >&#8758;=</a
      ><a name="4055"
      > </a
      ><a name="4056" href="StlcProp.html#3772" class="Bound"
      >M</a
      ><a name="4057"
      > </a
      ><a name="4058" href="Stlc.html#1297" class="Function Operator"
      >]</a
      ><a name="4059" class="Symbol"
      >)</a
      ><a name="4060"
      > </a
      ><a name="4061" href="https://agda.github.io/agda-stdlib/Data.Product.html#509" class="InductiveConstructor Operator"
      >,</a
      ><a name="4062"
      > </a
      ><a name="4063" href="Stlc.html#1819" class="InductiveConstructor"
      >&#946;&#8658;</a
      ><a name="4065"
      > </a
      ><a name="4066" href="StlcProp.html#3960" class="Bound"
      >valueM</a
      ><a name="4072" class="Symbol"
      >)</a
      ><a name="4073"
      >
</a
      ><a name="4074" href="StlcProp.html#1884" class="Function"
      >progress</a
      ><a name="4082"
      > </a
      ><a name="4083" href="Stlc.html#3663" class="InductiveConstructor"
      >&#120121;-I&#8321;</a
      ><a name="4087"
      > </a
      ><a name="4088" class="Symbol"
      >=</a
      ><a name="4089"
      > </a
      ><a name="4090" href="https://agda.github.io/agda-stdlib/Data.Sum.html#489" class="InductiveConstructor"
      >inj&#8321;</a
      ><a name="4094"
      > </a
      ><a name="4095" href="Stlc.html#1202" class="InductiveConstructor"
      >value-true</a
      ><a name="4105"
      >
</a
      ><a name="4106" href="StlcProp.html#1884" class="Function"
      >progress</a
      ><a name="4114"
      > </a
      ><a name="4115" href="Stlc.html#3697" class="InductiveConstructor"
      >&#120121;-I&#8322;</a
      ><a name="4119"
      > </a
      ><a name="4120" class="Symbol"
      >=</a
      ><a name="4121"
      > </a
      ><a name="4122" href="https://agda.github.io/agda-stdlib/Data.Sum.html#489" class="InductiveConstructor"
      >inj&#8321;</a
      ><a name="4126"
      > </a
      ><a name="4127" href="Stlc.html#1229" class="InductiveConstructor"
      >value-false</a
      ><a name="4138"
      >
</a
      ><a name="4139" href="StlcProp.html#1884" class="Function"
      >progress</a
      ><a name="4147"
      > </a
      ><a name="4148" class="Symbol"
      >(</a
      ><a name="4149" href="Stlc.html#3732" class="InductiveConstructor"
      >&#120121;-E</a
      ><a name="4152"
      > </a
      ><a name="4153" class="Symbol"
      >{</a
      ><a name="4154" href="StlcProp.html#4154" class="Bound"
      >&#915;</a
      ><a name="4155" class="Symbol"
      >}</a
      ><a name="4156"
      > </a
      ><a name="4157" class="Symbol"
      >{</a
      ><a name="4158" href="StlcProp.html#4158" class="Bound"
      >L</a
      ><a name="4159" class="Symbol"
      >}</a
      ><a name="4160"
      > </a
      ><a name="4161" class="Symbol"
      >{</a
      ><a name="4162" href="StlcProp.html#4162" class="Bound"
      >M</a
      ><a name="4163" class="Symbol"
      >}</a
      ><a name="4164"
      > </a
      ><a name="4165" class="Symbol"
      >{</a
      ><a name="4166" href="StlcProp.html#4166" class="Bound"
      >N</a
      ><a name="4167" class="Symbol"
      >}</a
      ><a name="4168"
      > </a
      ><a name="4169" class="Symbol"
      >{</a
      ><a name="4170" href="StlcProp.html#4170" class="Bound"
      >A</a
      ><a name="4171" class="Symbol"
      >}</a
      ><a name="4172"
      > </a
      ><a name="4173" href="StlcProp.html#4173" class="Bound"
      >&#8866;L</a
      ><a name="4175"
      > </a
      ><a name="4176" href="StlcProp.html#4176" class="Bound"
      >&#8866;M</a
      ><a name="4178"
      > </a
      ><a name="4179" href="StlcProp.html#4179" class="Bound"
      >&#8866;N</a
      ><a name="4181" class="Symbol"
      >)</a
      ><a name="4182"
      > </a
      ><a name="4183" class="Keyword"
      >with</a
      ><a name="4187"
      > </a
      ><a name="4188" href="StlcProp.html#1884" class="Function"
      >progress</a
      ><a name="4196"
      > </a
      ><a name="4197" href="StlcProp.html#4173" class="Bound"
      >&#8866;L</a
      ><a name="4199"
      >
</a
      ><a name="4200" class="Symbol"
      >...</a
      ><a name="4203"
      > </a
      ><a name="4204" class="Symbol"
      >|</a
      ><a name="4205"
      > </a
      ><a name="4206" href="https://agda.github.io/agda-stdlib/Data.Sum.html#514" class="InductiveConstructor"
      >inj&#8322;</a
      ><a name="4210"
      > </a
      ><a name="4211" class="Symbol"
      >(</a
      ><a name="4212" href="StlcProp.html#4212" class="Bound"
      >L&#8242;</a
      ><a name="4214"
      > </a
      ><a name="4215" href="https://agda.github.io/agda-stdlib/Data.Product.html#509" class="InductiveConstructor Operator"
      >,</a
      ><a name="4216"
      > </a
      ><a name="4217" href="StlcProp.html#4217" class="Bound"
      >L&#10233;L&#8242;</a
      ><a name="4221" class="Symbol"
      >)</a
      ><a name="4222"
      > </a
      ><a name="4223" class="Symbol"
      >=</a
      ><a name="4224"
      > </a
      ><a name="4225" href="https://agda.github.io/agda-stdlib/Data.Sum.html#514" class="InductiveConstructor"
      >inj&#8322;</a
      ><a name="4229"
      > </a
      ><a name="4230" class="Symbol"
      >((</a
      ><a name="4232" href="Stlc.html#844" class="InductiveConstructor Operator"
      >if</a
      ><a name="4234"
      > </a
      ><a name="4235" href="StlcProp.html#4212" class="Bound"
      >L&#8242;</a
      ><a name="4237"
      > </a
      ><a name="4238" href="Stlc.html#844" class="InductiveConstructor Operator"
      >then</a
      ><a name="4242"
      > </a
      ><a name="4243" href="StlcProp.html#4162" class="Bound"
      >M</a
      ><a name="4244"
      > </a
      ><a name="4245" href="Stlc.html#844" class="InductiveConstructor Operator"
      >else</a
      ><a name="4249"
      > </a
      ><a name="4250" href="StlcProp.html#4166" class="Bound"
      >N</a
      ><a name="4251" class="Symbol"
      >)</a
      ><a name="4252"
      > </a
      ><a name="4253" href="https://agda.github.io/agda-stdlib/Data.Product.html#509" class="InductiveConstructor Operator"
      >,</a
      ><a name="4254"
      > </a
      ><a name="4255" href="Stlc.html#2105" class="InductiveConstructor"
      >&#947;&#120121;</a
      ><a name="4257"
      > </a
      ><a name="4258" href="StlcProp.html#4217" class="Bound"
      >L&#10233;L&#8242;</a
      ><a name="4262" class="Symbol"
      >)</a
      ><a name="4263"
      >
</a
      ><a name="4264" class="Symbol"
      >...</a
      ><a name="4267"
      > </a
      ><a name="4268" class="Symbol"
      >|</a
      ><a name="4269"
      > </a
      ><a name="4270" href="https://agda.github.io/agda-stdlib/Data.Sum.html#489" class="InductiveConstructor"
      >inj&#8321;</a
      ><a name="4274"
      > </a
      ><a name="4275" href="StlcProp.html#4275" class="Bound"
      >valueL</a
      ><a name="4281"
      > </a
      ><a name="4282" class="Keyword"
      >with</a
      ><a name="4286"
      > </a
      ><a name="4287" href="StlcProp.html#1350" class="Function"
      >canonicalFormsLemma</a
      ><a name="4306"
      > </a
      ><a name="4307" href="StlcProp.html#4173" class="Bound"
      >&#8866;L</a
      ><a name="4309"
      > </a
      ><a name="4310" href="StlcProp.html#4275" class="Bound"
      >valueL</a
      ><a name="4316"
      >
</a
      ><a name="4317" class="Symbol"
      >...</a
      ><a name="4320"
      > </a
      ><a name="4321" class="Symbol"
      >|</a
      ><a name="4322"
      > </a
      ><a name="4323" href="StlcProp.html#1269" class="InductiveConstructor"
      >canonical-true</a
      ><a name="4337"
      > </a
      ><a name="4338" class="Symbol"
      >=</a
      ><a name="4339"
      > </a
      ><a name="4340" href="https://agda.github.io/agda-stdlib/Data.Sum.html#514" class="InductiveConstructor"
      >inj&#8322;</a
      ><a name="4344"
      > </a
      ><a name="4345" class="Symbol"
      >(</a
      ><a name="4346" href="StlcProp.html#4162" class="Bound"
      >M</a
      ><a name="4347"
      > </a
      ><a name="4348" href="https://agda.github.io/agda-stdlib/Data.Product.html#509" class="InductiveConstructor Operator"
      >,</a
      ><a name="4349"
      > </a
      ><a name="4350" href="Stlc.html#2008" class="InductiveConstructor"
      >&#946;&#120121;&#8321;</a
      ><a name="4353" class="Symbol"
      >)</a
      ><a name="4354"
      >
</a
      ><a name="4355" class="Symbol"
      >...</a
      ><a name="4358"
      > </a
      ><a name="4359" class="Symbol"
      >|</a
      ><a name="4360"
      > </a
      ><a name="4361" href="StlcProp.html#1309" class="InductiveConstructor"
      >canonical-false</a
      ><a name="4376"
      > </a
      ><a name="4377" class="Symbol"
      >=</a
      ><a name="4378"
      > </a
      ><a name="4379" href="https://agda.github.io/agda-stdlib/Data.Sum.html#514" class="InductiveConstructor"
      >inj&#8322;</a
      ><a name="4383"
      > </a
      ><a name="4384" class="Symbol"
      >(</a
      ><a name="4385" href="StlcProp.html#4166" class="Bound"
      >N</a
      ><a name="4386"
      > </a
      ><a name="4387" href="https://agda.github.io/agda-stdlib/Data.Product.html#509" class="InductiveConstructor Operator"
      >,</a
      ><a name="4388"
      > </a
      ><a name="4389" href="Stlc.html#2056" class="InductiveConstructor"
      >&#946;&#120121;&#8322;</a
      ><a name="4392" class="Symbol"
      >)</a
      >
{% endraw %}</pre>

#### Exercise: 3 stars, optional (progress_from_term_ind)
Show that progress can also be proved by induction on terms
instead of induction on typing derivations.

<pre class="Agda">{% raw %}
<a name="4582" class="Keyword"
      >postulate</a
      ><a name="4591"
      >
  </a
      ><a name="4594" href="StlcProp.html#4594" class="Postulate"
      >progress&#8242;</a
      ><a name="4603"
      > </a
      ><a name="4604" class="Symbol"
      >:</a
      ><a name="4605"
      > </a
      ><a name="4606" class="Symbol"
      >&#8704;</a
      ><a name="4607"
      > </a
      ><a name="4608" class="Symbol"
      >{</a
      ><a name="4609" href="StlcProp.html#4609" class="Bound"
      >M</a
      ><a name="4610"
      > </a
      ><a name="4611" href="StlcProp.html#4611" class="Bound"
      >A</a
      ><a name="4612" class="Symbol"
      >}</a
      ><a name="4613"
      > </a
      ><a name="4614" class="Symbol"
      >&#8594;</a
      ><a name="4615"
      > </a
      ><a name="4616" href="Maps.html#10359" class="Function"
      >&#8709;</a
      ><a name="4617"
      > </a
      ><a name="4618" href="Stlc.html#3408" class="Datatype Operator"
      >&#8866;</a
      ><a name="4619"
      > </a
      ><a name="4620" href="StlcProp.html#4609" class="Bound"
      >M</a
      ><a name="4621"
      > </a
      ><a name="4622" href="Stlc.html#3408" class="Datatype Operator"
      >&#8758;</a
      ><a name="4623"
      > </a
      ><a name="4624" href="StlcProp.html#4611" class="Bound"
      >A</a
      ><a name="4625"
      > </a
      ><a name="4626" class="Symbol"
      >&#8594;</a
      ><a name="4627"
      > </a
      ><a name="4628" href="Stlc.html#1126" class="Datatype"
      >Value</a
      ><a name="4633"
      > </a
      ><a name="4634" href="StlcProp.html#4609" class="Bound"
      >M</a
      ><a name="4635"
      > </a
      ><a name="4636" href="https://agda.github.io/agda-stdlib/Data.Sum.html#433" class="Datatype Operator"
      >&#8846;</a
      ><a name="4637"
      > </a
      ><a name="4638" href="https://agda.github.io/agda-stdlib/Data.Product.html#823" class="Function"
      >&#8707;</a
      ><a name="4639"
      > </a
      ><a name="4640" class="Symbol"
      >&#955;</a
      ><a name="4641"
      > </a
      ><a name="4642" href="StlcProp.html#4642" class="Bound"
      >N</a
      ><a name="4643"
      > </a
      ><a name="4644" class="Symbol"
      >&#8594;</a
      ><a name="4645"
      > </a
      ><a name="4646" href="StlcProp.html#4609" class="Bound"
      >M</a
      ><a name="4647"
      > </a
      ><a name="4648" href="Stlc.html#1787" class="Datatype Operator"
      >&#10233;</a
      ><a name="4649"
      > </a
      ><a name="4650" href="StlcProp.html#4642" class="Bound"
      >N</a
      >
{% endraw %}</pre>

## Preservation

The other half of the type soundness property is the preservation
of types during reduction.  For this, we need to develop some
technical machinery for reasoning about variables and
substitution.  Working from top to bottom (from the high-level
property we are actually interested in to the lowest-level
technical lemmas that are needed by various cases of the more
interesting proofs), the story goes like this:

  - The _preservation theorem_ is proved by induction on a typing
    derivation, pretty much as we did in the [Stlc]({{ "Stlc" | relative_url }})
    chapter.  The one case that is significantly different is the one for the
    `red` rule, whose definition uses the substitution operation.  To see that
    this step preserves typing, we need to know that the substitution itself
    does.  So we prove a... 

  - _substitution lemma_, stating that substituting a (closed)
    term `s` for a variable `x` in a term `t` preserves the type
    of `t`.  The proof goes by induction on the form of `t` and
    requires looking at all the different cases in the definition
    of substitition.  This time, the tricky cases are the ones for
    variables and for function abstractions.  In both cases, we
    discover that we need to take a term `s` that has been shown
    to be well-typed in some context `\Gamma` and consider the same
    term `s` in a slightly different context `\Gamma'`.  For this
    we prove a...

  - _context invariance_ lemma, showing that typing is preserved
    under "inessential changes" to the context `\Gamma`---in
    particular, changes that do not affect any of the free
    variables of the term.  And finally, for this, we need a
    careful definition of...

  - the _free variables_ of a term---i.e., those variables
    mentioned in a term and not in the scope of an enclosing
    function abstraction binding a variable of the same name.

To make Agda happy, we need to formalize the story in the opposite
order...


### Free Occurrences

A variable `x` _appears free in_ a term `M` if `M` contains some
occurrence of `x` that is not under an abstraction over `x`.
For example:

  - `y` appears free, but `x` does not, in `λ[ x ∶ (A ⇒ B) ] x · y`
  - both `x` and `y` appear free in `(λ[ x ∶ (A ⇒ B) ] x · y) · x`
  - no variables appear free in `λ[ x ∶ (A ⇒ B) ] (λ[ y ∶ A ] x · y)`

Formally:

<pre class="Agda">{% raw %}
<a name="7042" class="Keyword"
      >data</a
      ><a name="7046"
      > </a
      ><a name="7047" href="StlcProp.html#7047" class="Datatype Operator"
      >_&#8712;_</a
      ><a name="7050"
      > </a
      ><a name="7051" class="Symbol"
      >:</a
      ><a name="7052"
      > </a
      ><a name="7053" href="Maps.html#2215" class="Datatype"
      >Id</a
      ><a name="7055"
      > </a
      ><a name="7056" class="Symbol"
      >&#8594;</a
      ><a name="7057"
      > </a
      ><a name="7058" href="Stlc.html#715" class="Datatype"
      >Term</a
      ><a name="7062"
      > </a
      ><a name="7063" class="Symbol"
      >&#8594;</a
      ><a name="7064"
      > </a
      ><a name="7065" class="PrimitiveType"
      >Set</a
      ><a name="7068"
      > </a
      ><a name="7069" class="Keyword"
      >where</a
      ><a name="7074"
      >
  </a
      ><a name="7077" href="StlcProp.html#7077" class="InductiveConstructor"
      >free-var</a
      ><a name="7085"
      >  </a
      ><a name="7087" class="Symbol"
      >:</a
      ><a name="7088"
      > </a
      ><a name="7089" class="Symbol"
      >&#8704;</a
      ><a name="7090"
      > </a
      ><a name="7091" class="Symbol"
      >{</a
      ><a name="7092" href="StlcProp.html#7092" class="Bound"
      >x</a
      ><a name="7093" class="Symbol"
      >}</a
      ><a name="7094"
      > </a
      ><a name="7095" class="Symbol"
      >&#8594;</a
      ><a name="7096"
      > </a
      ><a name="7097" href="StlcProp.html#7092" class="Bound"
      >x</a
      ><a name="7098"
      > </a
      ><a name="7099" href="StlcProp.html#7047" class="Datatype Operator"
      >&#8712;</a
      ><a name="7100"
      > </a
      ><a name="7101" class="Symbol"
      >(</a
      ><a name="7102" href="Stlc.html#734" class="InductiveConstructor"
      >var</a
      ><a name="7105"
      > </a
      ><a name="7106" href="StlcProp.html#7092" class="Bound"
      >x</a
      ><a name="7107" class="Symbol"
      >)</a
      ><a name="7108"
      >
  </a
      ><a name="7111" href="StlcProp.html#7111" class="InductiveConstructor"
      >free-&#955;</a
      ><a name="7117"
      >  </a
      ><a name="7119" class="Symbol"
      >:</a
      ><a name="7120"
      > </a
      ><a name="7121" class="Symbol"
      >&#8704;</a
      ><a name="7122"
      > </a
      ><a name="7123" class="Symbol"
      >{</a
      ><a name="7124" href="StlcProp.html#7124" class="Bound"
      >x</a
      ><a name="7125"
      > </a
      ><a name="7126" href="StlcProp.html#7126" class="Bound"
      >y</a
      ><a name="7127"
      > </a
      ><a name="7128" href="StlcProp.html#7128" class="Bound"
      >A</a
      ><a name="7129"
      > </a
      ><a name="7130" href="StlcProp.html#7130" class="Bound"
      >N</a
      ><a name="7131" class="Symbol"
      >}</a
      ><a name="7132"
      > </a
      ><a name="7133" class="Symbol"
      >&#8594;</a
      ><a name="7134"
      > </a
      ><a name="7135" href="StlcProp.html#7126" class="Bound"
      >y</a
      ><a name="7136"
      > </a
      ><a name="7137" href="https://agda.github.io/agda-stdlib/Relation.Binary.Core.html#4493" class="Function Operator"
      >&#8802;</a
      ><a name="7138"
      > </a
      ><a name="7139" href="StlcProp.html#7124" class="Bound"
      >x</a
      ><a name="7140"
      > </a
      ><a name="7141" class="Symbol"
      >&#8594;</a
      ><a name="7142"
      > </a
      ><a name="7143" href="StlcProp.html#7124" class="Bound"
      >x</a
      ><a name="7144"
      > </a
      ><a name="7145" href="StlcProp.html#7047" class="Datatype Operator"
      >&#8712;</a
      ><a name="7146"
      > </a
      ><a name="7147" href="StlcProp.html#7130" class="Bound"
      >N</a
      ><a name="7148"
      > </a
      ><a name="7149" class="Symbol"
      >&#8594;</a
      ><a name="7150"
      > </a
      ><a name="7151" href="StlcProp.html#7124" class="Bound"
      >x</a
      ><a name="7152"
      > </a
      ><a name="7153" href="StlcProp.html#7047" class="Datatype Operator"
      >&#8712;</a
      ><a name="7154"
      > </a
      ><a name="7155" class="Symbol"
      >(</a
      ><a name="7156" href="Stlc.html#752" class="InductiveConstructor Operator"
      >&#955;[</a
      ><a name="7158"
      > </a
      ><a name="7159" href="StlcProp.html#7126" class="Bound"
      >y</a
      ><a name="7160"
      > </a
      ><a name="7161" href="Stlc.html#752" class="InductiveConstructor Operator"
      >&#8758;</a
      ><a name="7162"
      > </a
      ><a name="7163" href="StlcProp.html#7128" class="Bound"
      >A</a
      ><a name="7164"
      > </a
      ><a name="7165" href="Stlc.html#752" class="InductiveConstructor Operator"
      >]</a
      ><a name="7166"
      > </a
      ><a name="7167" href="StlcProp.html#7130" class="Bound"
      >N</a
      ><a name="7168" class="Symbol"
      >)</a
      ><a name="7169"
      >
  </a
      ><a name="7172" href="StlcProp.html#7172" class="InductiveConstructor"
      >free-&#183;&#8321;</a
      ><a name="7179"
      > </a
      ><a name="7180" class="Symbol"
      >:</a
      ><a name="7181"
      > </a
      ><a name="7182" class="Symbol"
      >&#8704;</a
      ><a name="7183"
      > </a
      ><a name="7184" class="Symbol"
      >{</a
      ><a name="7185" href="StlcProp.html#7185" class="Bound"
      >x</a
      ><a name="7186"
      > </a
      ><a name="7187" href="StlcProp.html#7187" class="Bound"
      >L</a
      ><a name="7188"
      > </a
      ><a name="7189" href="StlcProp.html#7189" class="Bound"
      >M</a
      ><a name="7190" class="Symbol"
      >}</a
      ><a name="7191"
      > </a
      ><a name="7192" class="Symbol"
      >&#8594;</a
      ><a name="7193"
      > </a
      ><a name="7194" href="StlcProp.html#7185" class="Bound"
      >x</a
      ><a name="7195"
      > </a
      ><a name="7196" href="StlcProp.html#7047" class="Datatype Operator"
      >&#8712;</a
      ><a name="7197"
      > </a
      ><a name="7198" href="StlcProp.html#7187" class="Bound"
      >L</a
      ><a name="7199"
      > </a
      ><a name="7200" class="Symbol"
      >&#8594;</a
      ><a name="7201"
      > </a
      ><a name="7202" href="StlcProp.html#7185" class="Bound"
      >x</a
      ><a name="7203"
      > </a
      ><a name="7204" href="StlcProp.html#7047" class="Datatype Operator"
      >&#8712;</a
      ><a name="7205"
      > </a
      ><a name="7206" class="Symbol"
      >(</a
      ><a name="7207" href="StlcProp.html#7187" class="Bound"
      >L</a
      ><a name="7208"
      > </a
      ><a name="7209" href="Stlc.html#788" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="7210"
      > </a
      ><a name="7211" href="StlcProp.html#7189" class="Bound"
      >M</a
      ><a name="7212" class="Symbol"
      >)</a
      ><a name="7213"
      >
  </a
      ><a name="7216" href="StlcProp.html#7216" class="InductiveConstructor"
      >free-&#183;&#8322;</a
      ><a name="7223"
      > </a
      ><a name="7224" class="Symbol"
      >:</a
      ><a name="7225"
      > </a
      ><a name="7226" class="Symbol"
      >&#8704;</a
      ><a name="7227"
      > </a
      ><a name="7228" class="Symbol"
      >{</a
      ><a name="7229" href="StlcProp.html#7229" class="Bound"
      >x</a
      ><a name="7230"
      > </a
      ><a name="7231" href="StlcProp.html#7231" class="Bound"
      >L</a
      ><a name="7232"
      > </a
      ><a name="7233" href="StlcProp.html#7233" class="Bound"
      >M</a
      ><a name="7234" class="Symbol"
      >}</a
      ><a name="7235"
      > </a
      ><a name="7236" class="Symbol"
      >&#8594;</a
      ><a name="7237"
      > </a
      ><a name="7238" href="StlcProp.html#7229" class="Bound"
      >x</a
      ><a name="7239"
      > </a
      ><a name="7240" href="StlcProp.html#7047" class="Datatype Operator"
      >&#8712;</a
      ><a name="7241"
      > </a
      ><a name="7242" href="StlcProp.html#7233" class="Bound"
      >M</a
      ><a name="7243"
      > </a
      ><a name="7244" class="Symbol"
      >&#8594;</a
      ><a name="7245"
      > </a
      ><a name="7246" href="StlcProp.html#7229" class="Bound"
      >x</a
      ><a name="7247"
      > </a
      ><a name="7248" href="StlcProp.html#7047" class="Datatype Operator"
      >&#8712;</a
      ><a name="7249"
      > </a
      ><a name="7250" class="Symbol"
      >(</a
      ><a name="7251" href="StlcProp.html#7231" class="Bound"
      >L</a
      ><a name="7252"
      > </a
      ><a name="7253" href="Stlc.html#788" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="7254"
      > </a
      ><a name="7255" href="StlcProp.html#7233" class="Bound"
      >M</a
      ><a name="7256" class="Symbol"
      >)</a
      ><a name="7257"
      >
  </a
      ><a name="7260" href="StlcProp.html#7260" class="InductiveConstructor"
      >free-if&#8321;</a
      ><a name="7268"
      > </a
      ><a name="7269" class="Symbol"
      >:</a
      ><a name="7270"
      > </a
      ><a name="7271" class="Symbol"
      >&#8704;</a
      ><a name="7272"
      > </a
      ><a name="7273" class="Symbol"
      >{</a
      ><a name="7274" href="StlcProp.html#7274" class="Bound"
      >x</a
      ><a name="7275"
      > </a
      ><a name="7276" href="StlcProp.html#7276" class="Bound"
      >L</a
      ><a name="7277"
      > </a
      ><a name="7278" href="StlcProp.html#7278" class="Bound"
      >M</a
      ><a name="7279"
      > </a
      ><a name="7280" href="StlcProp.html#7280" class="Bound"
      >N</a
      ><a name="7281" class="Symbol"
      >}</a
      ><a name="7282"
      > </a
      ><a name="7283" class="Symbol"
      >&#8594;</a
      ><a name="7284"
      > </a
      ><a name="7285" href="StlcProp.html#7274" class="Bound"
      >x</a
      ><a name="7286"
      > </a
      ><a name="7287" href="StlcProp.html#7047" class="Datatype Operator"
      >&#8712;</a
      ><a name="7288"
      > </a
      ><a name="7289" href="StlcProp.html#7276" class="Bound"
      >L</a
      ><a name="7290"
      > </a
      ><a name="7291" class="Symbol"
      >&#8594;</a
      ><a name="7292"
      > </a
      ><a name="7293" href="StlcProp.html#7274" class="Bound"
      >x</a
      ><a name="7294"
      > </a
      ><a name="7295" href="StlcProp.html#7047" class="Datatype Operator"
      >&#8712;</a
      ><a name="7296"
      > </a
      ><a name="7297" class="Symbol"
      >(</a
      ><a name="7298" href="Stlc.html#844" class="InductiveConstructor Operator"
      >if</a
      ><a name="7300"
      > </a
      ><a name="7301" href="StlcProp.html#7276" class="Bound"
      >L</a
      ><a name="7302"
      > </a
      ><a name="7303" href="Stlc.html#844" class="InductiveConstructor Operator"
      >then</a
      ><a name="7307"
      > </a
      ><a name="7308" href="StlcProp.html#7278" class="Bound"
      >M</a
      ><a name="7309"
      > </a
      ><a name="7310" href="Stlc.html#844" class="InductiveConstructor Operator"
      >else</a
      ><a name="7314"
      > </a
      ><a name="7315" href="StlcProp.html#7280" class="Bound"
      >N</a
      ><a name="7316" class="Symbol"
      >)</a
      ><a name="7317"
      >
  </a
      ><a name="7320" href="StlcProp.html#7320" class="InductiveConstructor"
      >free-if&#8322;</a
      ><a name="7328"
      > </a
      ><a name="7329" class="Symbol"
      >:</a
      ><a name="7330"
      > </a
      ><a name="7331" class="Symbol"
      >&#8704;</a
      ><a name="7332"
      > </a
      ><a name="7333" class="Symbol"
      >{</a
      ><a name="7334" href="StlcProp.html#7334" class="Bound"
      >x</a
      ><a name="7335"
      > </a
      ><a name="7336" href="StlcProp.html#7336" class="Bound"
      >L</a
      ><a name="7337"
      > </a
      ><a name="7338" href="StlcProp.html#7338" class="Bound"
      >M</a
      ><a name="7339"
      > </a
      ><a name="7340" href="StlcProp.html#7340" class="Bound"
      >N</a
      ><a name="7341" class="Symbol"
      >}</a
      ><a name="7342"
      > </a
      ><a name="7343" class="Symbol"
      >&#8594;</a
      ><a name="7344"
      > </a
      ><a name="7345" href="StlcProp.html#7334" class="Bound"
      >x</a
      ><a name="7346"
      > </a
      ><a name="7347" href="StlcProp.html#7047" class="Datatype Operator"
      >&#8712;</a
      ><a name="7348"
      > </a
      ><a name="7349" href="StlcProp.html#7338" class="Bound"
      >M</a
      ><a name="7350"
      > </a
      ><a name="7351" class="Symbol"
      >&#8594;</a
      ><a name="7352"
      > </a
      ><a name="7353" href="StlcProp.html#7334" class="Bound"
      >x</a
      ><a name="7354"
      > </a
      ><a name="7355" href="StlcProp.html#7047" class="Datatype Operator"
      >&#8712;</a
      ><a name="7356"
      > </a
      ><a name="7357" class="Symbol"
      >(</a
      ><a name="7358" href="Stlc.html#844" class="InductiveConstructor Operator"
      >if</a
      ><a name="7360"
      > </a
      ><a name="7361" href="StlcProp.html#7336" class="Bound"
      >L</a
      ><a name="7362"
      > </a
      ><a name="7363" href="Stlc.html#844" class="InductiveConstructor Operator"
      >then</a
      ><a name="7367"
      > </a
      ><a name="7368" href="StlcProp.html#7338" class="Bound"
      >M</a
      ><a name="7369"
      > </a
      ><a name="7370" href="Stlc.html#844" class="InductiveConstructor Operator"
      >else</a
      ><a name="7374"
      > </a
      ><a name="7375" href="StlcProp.html#7340" class="Bound"
      >N</a
      ><a name="7376" class="Symbol"
      >)</a
      ><a name="7377"
      >
  </a
      ><a name="7380" href="StlcProp.html#7380" class="InductiveConstructor"
      >free-if&#8323;</a
      ><a name="7388"
      > </a
      ><a name="7389" class="Symbol"
      >:</a
      ><a name="7390"
      > </a
      ><a name="7391" class="Symbol"
      >&#8704;</a
      ><a name="7392"
      > </a
      ><a name="7393" class="Symbol"
      >{</a
      ><a name="7394" href="StlcProp.html#7394" class="Bound"
      >x</a
      ><a name="7395"
      > </a
      ><a name="7396" href="StlcProp.html#7396" class="Bound"
      >L</a
      ><a name="7397"
      > </a
      ><a name="7398" href="StlcProp.html#7398" class="Bound"
      >M</a
      ><a name="7399"
      > </a
      ><a name="7400" href="StlcProp.html#7400" class="Bound"
      >N</a
      ><a name="7401" class="Symbol"
      >}</a
      ><a name="7402"
      > </a
      ><a name="7403" class="Symbol"
      >&#8594;</a
      ><a name="7404"
      > </a
      ><a name="7405" href="StlcProp.html#7394" class="Bound"
      >x</a
      ><a name="7406"
      > </a
      ><a name="7407" href="StlcProp.html#7047" class="Datatype Operator"
      >&#8712;</a
      ><a name="7408"
      > </a
      ><a name="7409" href="StlcProp.html#7400" class="Bound"
      >N</a
      ><a name="7410"
      > </a
      ><a name="7411" class="Symbol"
      >&#8594;</a
      ><a name="7412"
      > </a
      ><a name="7413" href="StlcProp.html#7394" class="Bound"
      >x</a
      ><a name="7414"
      > </a
      ><a name="7415" href="StlcProp.html#7047" class="Datatype Operator"
      >&#8712;</a
      ><a name="7416"
      > </a
      ><a name="7417" class="Symbol"
      >(</a
      ><a name="7418" href="Stlc.html#844" class="InductiveConstructor Operator"
      >if</a
      ><a name="7420"
      > </a
      ><a name="7421" href="StlcProp.html#7396" class="Bound"
      >L</a
      ><a name="7422"
      > </a
      ><a name="7423" href="Stlc.html#844" class="InductiveConstructor Operator"
      >then</a
      ><a name="7427"
      > </a
      ><a name="7428" href="StlcProp.html#7398" class="Bound"
      >M</a
      ><a name="7429"
      > </a
      ><a name="7430" href="Stlc.html#844" class="InductiveConstructor Operator"
      >else</a
      ><a name="7434"
      > </a
      ><a name="7435" href="StlcProp.html#7400" class="Bound"
      >N</a
      ><a name="7436" class="Symbol"
      >)</a
      >
{% endraw %}</pre>

A term in which no variables appear free is said to be _closed_.

<pre class="Agda">{% raw %}
<a name="7529" href="StlcProp.html#7529" class="Function"
      >closed</a
      ><a name="7535"
      > </a
      ><a name="7536" class="Symbol"
      >:</a
      ><a name="7537"
      > </a
      ><a name="7538" href="Stlc.html#715" class="Datatype"
      >Term</a
      ><a name="7542"
      > </a
      ><a name="7543" class="Symbol"
      >&#8594;</a
      ><a name="7544"
      > </a
      ><a name="7545" class="PrimitiveType"
      >Set</a
      ><a name="7548"
      >
</a
      ><a name="7549" href="StlcProp.html#7529" class="Function"
      >closed</a
      ><a name="7555"
      > </a
      ><a name="7556" href="StlcProp.html#7556" class="Bound"
      >M</a
      ><a name="7557"
      > </a
      ><a name="7558" class="Symbol"
      >=</a
      ><a name="7559"
      > </a
      ><a name="7560" class="Symbol"
      >&#8704;</a
      ><a name="7561"
      > </a
      ><a name="7562" class="Symbol"
      >{</a
      ><a name="7563" href="StlcProp.html#7563" class="Bound"
      >x</a
      ><a name="7564" class="Symbol"
      >}</a
      ><a name="7565"
      > </a
      ><a name="7566" class="Symbol"
      >&#8594;</a
      ><a name="7567"
      > </a
      ><a name="7568" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#414" class="Function Operator"
      >&#172;</a
      ><a name="7569"
      > </a
      ><a name="7570" class="Symbol"
      >(</a
      ><a name="7571" href="StlcProp.html#7563" class="Bound"
      >x</a
      ><a name="7572"
      > </a
      ><a name="7573" href="StlcProp.html#7047" class="Datatype Operator"
      >&#8712;</a
      ><a name="7574"
      > </a
      ><a name="7575" href="StlcProp.html#7556" class="Bound"
      >M</a
      ><a name="7576" class="Symbol"
      >)</a
      >
{% endraw %}</pre>

#### Exercise: 1 star (free-in)
If the definition of `_∈_` is not crystal clear to
you, it is a good idea to take a piece of paper and write out the
rules in informal inference-rule notation.  (Although it is a
rather low-level, technical definition, understanding it is
crucial to understanding substitution and its properties, which
are really the crux of the lambda-calculus.)

### Substitution
To prove that substitution preserves typing, we first need a
technical lemma connecting free variables and typing contexts: If
a variable `x` appears free in a term `M`, and if we know `M` is
well typed in context `Γ`, then it must be the case that
`Γ` assigns a type to `x`.

<pre class="Agda">{% raw %}
<a name="8278" href="StlcProp.html#8278" class="Function"
      >freeLemma</a
      ><a name="8287"
      > </a
      ><a name="8288" class="Symbol"
      >:</a
      ><a name="8289"
      > </a
      ><a name="8290" class="Symbol"
      >&#8704;</a
      ><a name="8291"
      > </a
      ><a name="8292" class="Symbol"
      >{</a
      ><a name="8293" href="StlcProp.html#8293" class="Bound"
      >x</a
      ><a name="8294"
      > </a
      ><a name="8295" href="StlcProp.html#8295" class="Bound"
      >M</a
      ><a name="8296"
      > </a
      ><a name="8297" href="StlcProp.html#8297" class="Bound"
      >A</a
      ><a name="8298"
      > </a
      ><a name="8299" href="StlcProp.html#8299" class="Bound"
      >&#915;</a
      ><a name="8300" class="Symbol"
      >}</a
      ><a name="8301"
      > </a
      ><a name="8302" class="Symbol"
      >&#8594;</a
      ><a name="8303"
      > </a
      ><a name="8304" href="StlcProp.html#8293" class="Bound"
      >x</a
      ><a name="8305"
      > </a
      ><a name="8306" href="StlcProp.html#7047" class="Datatype Operator"
      >&#8712;</a
      ><a name="8307"
      > </a
      ><a name="8308" href="StlcProp.html#8295" class="Bound"
      >M</a
      ><a name="8309"
      > </a
      ><a name="8310" class="Symbol"
      >&#8594;</a
      ><a name="8311"
      > </a
      ><a name="8312" href="StlcProp.html#8299" class="Bound"
      >&#915;</a
      ><a name="8313"
      > </a
      ><a name="8314" href="Stlc.html#3408" class="Datatype Operator"
      >&#8866;</a
      ><a name="8315"
      > </a
      ><a name="8316" href="StlcProp.html#8295" class="Bound"
      >M</a
      ><a name="8317"
      > </a
      ><a name="8318" href="Stlc.html#3408" class="Datatype Operator"
      >&#8758;</a
      ><a name="8319"
      > </a
      ><a name="8320" href="StlcProp.html#8297" class="Bound"
      >A</a
      ><a name="8321"
      > </a
      ><a name="8322" class="Symbol"
      >&#8594;</a
      ><a name="8323"
      > </a
      ><a name="8324" href="https://agda.github.io/agda-stdlib/Data.Product.html#823" class="Function"
      >&#8707;</a
      ><a name="8325"
      > </a
      ><a name="8326" class="Symbol"
      >&#955;</a
      ><a name="8327"
      > </a
      ><a name="8328" href="StlcProp.html#8328" class="Bound"
      >B</a
      ><a name="8329"
      > </a
      ><a name="8330" class="Symbol"
      >&#8594;</a
      ><a name="8331"
      > </a
      ><a name="8332" href="StlcProp.html#8299" class="Bound"
      >&#915;</a
      ><a name="8333"
      > </a
      ><a name="8334" href="StlcProp.html#8293" class="Bound"
      >x</a
      ><a name="8335"
      > </a
      ><a name="8336" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="8337"
      > </a
      ><a name="8338" href="https://agda.github.io/agda-stdlib/Data.Maybe.Base.html#373" class="InductiveConstructor"
      >just</a
      ><a name="8342"
      > </a
      ><a name="8343" href="StlcProp.html#8328" class="Bound"
      >B</a
      >
{% endraw %}</pre>

_Proof_: We show, by induction on the proof that `x` appears
  free in `P`, that, for all contexts `Γ`, if `P` is well
  typed under `Γ`, then `Γ` assigns some type to `x`.

  - If the last rule used was `free-var`, then `P = x`, and from
    the assumption that `M` is well typed under `Γ` we have
    immediately that `Γ` assigns a type to `x`.

  - If the last rule used was `free-·₁`, then `P = L · M` and `x`
    appears free in `L`.  Since `L` is well typed under `\Gamma`,
    we can see from the typing rules that `L` must also be, and
    the IH then tells us that `Γ` assigns `x` a type.

  - Almost all the other cases are similar: `x` appears free in a
    subterm of `P`, and since `P` is well typed under `Γ`, we
    know the subterm of `M` in which `x` appears is well typed
    under `Γ` as well, and the IH gives us exactly the
    conclusion we want.

  - The only remaining case is `free-λ`.  In this case `P =
    λ[ y ∶ A ] N`, and `x` appears free in `N`; we also know that
    `x` is different from `y`.  The difference from the previous
    cases is that whereas `P` is well typed under `\Gamma`, its
    body `N` is well typed under `(Γ , y ∶ A)`, so the IH
    allows us to conclude that `x` is assigned some type by the
    extended context `(Γ , y ∶ A)`.  To conclude that `Γ`
    assigns a type to `x`, we appeal the decidable equality for names
    `_≟_`, noting that `x` and `y` are different variables.

<pre class="Agda">{% raw %}
<a name="9806" href="StlcProp.html#8278" class="Function"
      >freeLemma</a
      ><a name="9815"
      > </a
      ><a name="9816" href="StlcProp.html#7077" class="InductiveConstructor"
      >free-var</a
      ><a name="9824"
      > </a
      ><a name="9825" class="Symbol"
      >(</a
      ><a name="9826" href="Stlc.html#3452" class="InductiveConstructor"
      >Ax</a
      ><a name="9828"
      > </a
      ><a name="9829" href="StlcProp.html#9829" class="Bound"
      >&#915;x&#8801;justA</a
      ><a name="9837" class="Symbol"
      >)</a
      ><a name="9838"
      > </a
      ><a name="9839" class="Symbol"
      >=</a
      ><a name="9840"
      > </a
      ><a name="9841" class="Symbol"
      >(_</a
      ><a name="9843"
      > </a
      ><a name="9844" href="https://agda.github.io/agda-stdlib/Data.Product.html#509" class="InductiveConstructor Operator"
      >,</a
      ><a name="9845"
      > </a
      ><a name="9846" href="StlcProp.html#9829" class="Bound"
      >&#915;x&#8801;justA</a
      ><a name="9854" class="Symbol"
      >)</a
      ><a name="9855"
      >
</a
      ><a name="9856" href="StlcProp.html#8278" class="Function"
      >freeLemma</a
      ><a name="9865"
      > </a
      ><a name="9866" class="Symbol"
      >(</a
      ><a name="9867" href="StlcProp.html#7172" class="InductiveConstructor"
      >free-&#183;&#8321;</a
      ><a name="9874"
      > </a
      ><a name="9875" href="StlcProp.html#9875" class="Bound"
      >x&#8712;L</a
      ><a name="9878" class="Symbol"
      >)</a
      ><a name="9879"
      > </a
      ><a name="9880" class="Symbol"
      >(</a
      ><a name="9881" href="Stlc.html#3585" class="InductiveConstructor"
      >&#8658;-E</a
      ><a name="9884"
      > </a
      ><a name="9885" href="StlcProp.html#9885" class="Bound"
      >&#8866;L</a
      ><a name="9887"
      > </a
      ><a name="9888" href="StlcProp.html#9888" class="Bound"
      >&#8866;M</a
      ><a name="9890" class="Symbol"
      >)</a
      ><a name="9891"
      > </a
      ><a name="9892" class="Symbol"
      >=</a
      ><a name="9893"
      > </a
      ><a name="9894" href="StlcProp.html#8278" class="Function"
      >freeLemma</a
      ><a name="9903"
      > </a
      ><a name="9904" href="StlcProp.html#9875" class="Bound"
      >x&#8712;L</a
      ><a name="9907"
      > </a
      ><a name="9908" href="StlcProp.html#9885" class="Bound"
      >&#8866;L</a
      ><a name="9910"
      >
</a
      ><a name="9911" href="StlcProp.html#8278" class="Function"
      >freeLemma</a
      ><a name="9920"
      > </a
      ><a name="9921" class="Symbol"
      >(</a
      ><a name="9922" href="StlcProp.html#7216" class="InductiveConstructor"
      >free-&#183;&#8322;</a
      ><a name="9929"
      > </a
      ><a name="9930" href="StlcProp.html#9930" class="Bound"
      >x&#8712;M</a
      ><a name="9933" class="Symbol"
      >)</a
      ><a name="9934"
      > </a
      ><a name="9935" class="Symbol"
      >(</a
      ><a name="9936" href="Stlc.html#3585" class="InductiveConstructor"
      >&#8658;-E</a
      ><a name="9939"
      > </a
      ><a name="9940" href="StlcProp.html#9940" class="Bound"
      >&#8866;L</a
      ><a name="9942"
      > </a
      ><a name="9943" href="StlcProp.html#9943" class="Bound"
      >&#8866;M</a
      ><a name="9945" class="Symbol"
      >)</a
      ><a name="9946"
      > </a
      ><a name="9947" class="Symbol"
      >=</a
      ><a name="9948"
      > </a
      ><a name="9949" href="StlcProp.html#8278" class="Function"
      >freeLemma</a
      ><a name="9958"
      > </a
      ><a name="9959" href="StlcProp.html#9930" class="Bound"
      >x&#8712;M</a
      ><a name="9962"
      > </a
      ><a name="9963" href="StlcProp.html#9943" class="Bound"
      >&#8866;M</a
      ><a name="9965"
      >
</a
      ><a name="9966" href="StlcProp.html#8278" class="Function"
      >freeLemma</a
      ><a name="9975"
      > </a
      ><a name="9976" class="Symbol"
      >(</a
      ><a name="9977" href="StlcProp.html#7260" class="InductiveConstructor"
      >free-if&#8321;</a
      ><a name="9985"
      > </a
      ><a name="9986" href="StlcProp.html#9986" class="Bound"
      >x&#8712;L</a
      ><a name="9989" class="Symbol"
      >)</a
      ><a name="9990"
      > </a
      ><a name="9991" class="Symbol"
      >(</a
      ><a name="9992" href="Stlc.html#3732" class="InductiveConstructor"
      >&#120121;-E</a
      ><a name="9995"
      > </a
      ><a name="9996" href="StlcProp.html#9996" class="Bound"
      >&#8866;L</a
      ><a name="9998"
      > </a
      ><a name="9999" href="StlcProp.html#9999" class="Bound"
      >&#8866;M</a
      ><a name="10001"
      > </a
      ><a name="10002" href="StlcProp.html#10002" class="Bound"
      >&#8866;N</a
      ><a name="10004" class="Symbol"
      >)</a
      ><a name="10005"
      > </a
      ><a name="10006" class="Symbol"
      >=</a
      ><a name="10007"
      > </a
      ><a name="10008" href="StlcProp.html#8278" class="Function"
      >freeLemma</a
      ><a name="10017"
      > </a
      ><a name="10018" href="StlcProp.html#9986" class="Bound"
      >x&#8712;L</a
      ><a name="10021"
      > </a
      ><a name="10022" href="StlcProp.html#9996" class="Bound"
      >&#8866;L</a
      ><a name="10024"
      >
</a
      ><a name="10025" href="StlcProp.html#8278" class="Function"
      >freeLemma</a
      ><a name="10034"
      > </a
      ><a name="10035" class="Symbol"
      >(</a
      ><a name="10036" href="StlcProp.html#7320" class="InductiveConstructor"
      >free-if&#8322;</a
      ><a name="10044"
      > </a
      ><a name="10045" href="StlcProp.html#10045" class="Bound"
      >x&#8712;M</a
      ><a name="10048" class="Symbol"
      >)</a
      ><a name="10049"
      > </a
      ><a name="10050" class="Symbol"
      >(</a
      ><a name="10051" href="Stlc.html#3732" class="InductiveConstructor"
      >&#120121;-E</a
      ><a name="10054"
      > </a
      ><a name="10055" href="StlcProp.html#10055" class="Bound"
      >&#8866;L</a
      ><a name="10057"
      > </a
      ><a name="10058" href="StlcProp.html#10058" class="Bound"
      >&#8866;M</a
      ><a name="10060"
      > </a
      ><a name="10061" href="StlcProp.html#10061" class="Bound"
      >&#8866;N</a
      ><a name="10063" class="Symbol"
      >)</a
      ><a name="10064"
      > </a
      ><a name="10065" class="Symbol"
      >=</a
      ><a name="10066"
      > </a
      ><a name="10067" href="StlcProp.html#8278" class="Function"
      >freeLemma</a
      ><a name="10076"
      > </a
      ><a name="10077" href="StlcProp.html#10045" class="Bound"
      >x&#8712;M</a
      ><a name="10080"
      > </a
      ><a name="10081" href="StlcProp.html#10058" class="Bound"
      >&#8866;M</a
      ><a name="10083"
      >
</a
      ><a name="10084" href="StlcProp.html#8278" class="Function"
      >freeLemma</a
      ><a name="10093"
      > </a
      ><a name="10094" class="Symbol"
      >(</a
      ><a name="10095" href="StlcProp.html#7380" class="InductiveConstructor"
      >free-if&#8323;</a
      ><a name="10103"
      > </a
      ><a name="10104" href="StlcProp.html#10104" class="Bound"
      >x&#8712;N</a
      ><a name="10107" class="Symbol"
      >)</a
      ><a name="10108"
      > </a
      ><a name="10109" class="Symbol"
      >(</a
      ><a name="10110" href="Stlc.html#3732" class="InductiveConstructor"
      >&#120121;-E</a
      ><a name="10113"
      > </a
      ><a name="10114" href="StlcProp.html#10114" class="Bound"
      >&#8866;L</a
      ><a name="10116"
      > </a
      ><a name="10117" href="StlcProp.html#10117" class="Bound"
      >&#8866;M</a
      ><a name="10119"
      > </a
      ><a name="10120" href="StlcProp.html#10120" class="Bound"
      >&#8866;N</a
      ><a name="10122" class="Symbol"
      >)</a
      ><a name="10123"
      > </a
      ><a name="10124" class="Symbol"
      >=</a
      ><a name="10125"
      > </a
      ><a name="10126" href="StlcProp.html#8278" class="Function"
      >freeLemma</a
      ><a name="10135"
      > </a
      ><a name="10136" href="StlcProp.html#10104" class="Bound"
      >x&#8712;N</a
      ><a name="10139"
      > </a
      ><a name="10140" href="StlcProp.html#10120" class="Bound"
      >&#8866;N</a
      ><a name="10142"
      >
</a
      ><a name="10143" href="StlcProp.html#8278" class="Function"
      >freeLemma</a
      ><a name="10152"
      > </a
      ><a name="10153" class="Symbol"
      >(</a
      ><a name="10154" href="StlcProp.html#7111" class="InductiveConstructor"
      >free-&#955;</a
      ><a name="10160"
      > </a
      ><a name="10161" class="Symbol"
      >{</a
      ><a name="10162" href="StlcProp.html#10162" class="Bound"
      >x</a
      ><a name="10163" class="Symbol"
      >}</a
      ><a name="10164"
      > </a
      ><a name="10165" class="Symbol"
      >{</a
      ><a name="10166" href="StlcProp.html#10166" class="Bound"
      >y</a
      ><a name="10167" class="Symbol"
      >}</a
      ><a name="10168"
      > </a
      ><a name="10169" href="StlcProp.html#10169" class="Bound"
      >y&#8802;x</a
      ><a name="10172"
      > </a
      ><a name="10173" href="StlcProp.html#10173" class="Bound"
      >x&#8712;N</a
      ><a name="10176" class="Symbol"
      >)</a
      ><a name="10177"
      > </a
      ><a name="10178" class="Symbol"
      >(</a
      ><a name="10179" href="Stlc.html#3508" class="InductiveConstructor"
      >&#8658;-I</a
      ><a name="10182"
      > </a
      ><a name="10183" href="StlcProp.html#10183" class="Bound"
      >&#8866;N</a
      ><a name="10185" class="Symbol"
      >)</a
      ><a name="10186"
      > </a
      ><a name="10187" class="Keyword"
      >with</a
      ><a name="10191"
      > </a
      ><a name="10192" href="StlcProp.html#8278" class="Function"
      >freeLemma</a
      ><a name="10201"
      > </a
      ><a name="10202" href="StlcProp.html#10173" class="Bound"
      >x&#8712;N</a
      ><a name="10205"
      > </a
      ><a name="10206" href="StlcProp.html#10183" class="Bound"
      >&#8866;N</a
      ><a name="10208"
      >
</a
      ><a name="10209" class="Symbol"
      >...</a
      ><a name="10212"
      > </a
      ><a name="10213" class="Symbol"
      >|</a
      ><a name="10214"
      > </a
      ><a name="10215" href="StlcProp.html#10215" class="Bound"
      >&#915;x=justC</a
      ><a name="10223"
      > </a
      ><a name="10224" class="Keyword"
      >with</a
      ><a name="10228"
      > </a
      ><a name="10229" href="StlcProp.html#10166" class="Bound"
      >y</a
      ><a name="10230"
      > </a
      ><a name="10231" href="Maps.html#2558" class="Function Operator"
      >&#8799;</a
      ><a name="10232"
      > </a
      ><a name="10233" href="StlcProp.html#10162" class="Bound"
      >x</a
      ><a name="10234"
      >
</a
      ><a name="10235" class="Symbol"
      >...</a
      ><a name="10238"
      > </a
      ><a name="10239" class="Symbol"
      >|</a
      ><a name="10240"
      > </a
      ><a name="10241" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#520" class="InductiveConstructor"
      >yes</a
      ><a name="10244"
      > </a
      ><a name="10245" href="StlcProp.html#10245" class="Bound"
      >y&#8801;x</a
      ><a name="10248"
      > </a
      ><a name="10249" class="Symbol"
      >=</a
      ><a name="10250"
      > </a
      ><a name="10251" href="https://agda.github.io/agda-stdlib/Data.Empty.html#348" class="Function"
      >&#8869;-elim</a
      ><a name="10257"
      > </a
      ><a name="10258" class="Symbol"
      >(</a
      ><a name="10259" href="StlcProp.html#10169" class="Bound"
      >y&#8802;x</a
      ><a name="10262"
      > </a
      ><a name="10263" href="StlcProp.html#10245" class="Bound"
      >y&#8801;x</a
      ><a name="10266" class="Symbol"
      >)</a
      ><a name="10267"
      >
</a
      ><a name="10268" class="Symbol"
      >...</a
      ><a name="10271"
      > </a
      ><a name="10272" class="Symbol"
      >|</a
      ><a name="10273"
      > </a
      ><a name="10274" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#547" class="InductiveConstructor"
      >no</a
      ><a name="10276"
      >  </a
      ><a name="10278" class="Symbol"
      >_</a
      ><a name="10279"
      >   </a
      ><a name="10282" class="Symbol"
      >=</a
      ><a name="10283"
      > </a
      ><a name="10284" href="StlcProp.html#10215" class="Bound"
      >&#915;x=justC</a
      >
{% endraw %}</pre>

[A subtle point: if the first argument of `free-λ` was of type
`x ≢ y` rather than of type `y ≢ x`, then the type of the
term `Γx=justC` would not simplify properly.]

Next, we'll need the fact that any term `M` which is well typed in
the empty context is closed (it has no free variables).

#### Exercise: 2 stars, optional (∅⊢-closed)

<pre class="Agda">{% raw %}
<a name="10656" class="Keyword"
      >postulate</a
      ><a name="10665"
      >
  </a
      ><a name="10668" href="StlcProp.html#10668" class="Postulate"
      >&#8709;&#8866;-closed</a
      ><a name="10677"
      > </a
      ><a name="10678" class="Symbol"
      >:</a
      ><a name="10679"
      > </a
      ><a name="10680" class="Symbol"
      >&#8704;</a
      ><a name="10681"
      > </a
      ><a name="10682" class="Symbol"
      >{</a
      ><a name="10683" href="StlcProp.html#10683" class="Bound"
      >M</a
      ><a name="10684"
      > </a
      ><a name="10685" href="StlcProp.html#10685" class="Bound"
      >A</a
      ><a name="10686" class="Symbol"
      >}</a
      ><a name="10687"
      > </a
      ><a name="10688" class="Symbol"
      >&#8594;</a
      ><a name="10689"
      > </a
      ><a name="10690" href="Maps.html#10359" class="Function"
      >&#8709;</a
      ><a name="10691"
      > </a
      ><a name="10692" href="Stlc.html#3408" class="Datatype Operator"
      >&#8866;</a
      ><a name="10693"
      > </a
      ><a name="10694" href="StlcProp.html#10683" class="Bound"
      >M</a
      ><a name="10695"
      > </a
      ><a name="10696" href="Stlc.html#3408" class="Datatype Operator"
      >&#8758;</a
      ><a name="10697"
      > </a
      ><a name="10698" href="StlcProp.html#10685" class="Bound"
      >A</a
      ><a name="10699"
      > </a
      ><a name="10700" class="Symbol"
      >&#8594;</a
      ><a name="10701"
      > </a
      ><a name="10702" href="StlcProp.html#7529" class="Function"
      >closed</a
      ><a name="10708"
      > </a
      ><a name="10709" href="StlcProp.html#10683" class="Bound"
      >M</a
      >
{% endraw %}</pre>

<div class="hidden">
<pre class="Agda">{% raw %}
<a name="10757" href="StlcProp.html#10757" class="Function"
      >contradiction</a
      ><a name="10770"
      > </a
      ><a name="10771" class="Symbol"
      >:</a
      ><a name="10772"
      > </a
      ><a name="10773" class="Symbol"
      >&#8704;</a
      ><a name="10774"
      > </a
      ><a name="10775" class="Symbol"
      >{</a
      ><a name="10776" href="StlcProp.html#10776" class="Bound"
      >X</a
      ><a name="10777"
      > </a
      ><a name="10778" class="Symbol"
      >:</a
      ><a name="10779"
      > </a
      ><a name="10780" class="PrimitiveType"
      >Set</a
      ><a name="10783" class="Symbol"
      >}</a
      ><a name="10784"
      > </a
      ><a name="10785" class="Symbol"
      >&#8594;</a
      ><a name="10786"
      > </a
      ><a name="10787" class="Symbol"
      >&#8704;</a
      ><a name="10788"
      > </a
      ><a name="10789" class="Symbol"
      >{</a
      ><a name="10790" href="StlcProp.html#10790" class="Bound"
      >x</a
      ><a name="10791"
      > </a
      ><a name="10792" class="Symbol"
      >:</a
      ><a name="10793"
      > </a
      ><a name="10794" href="StlcProp.html#10776" class="Bound"
      >X</a
      ><a name="10795" class="Symbol"
      >}</a
      ><a name="10796"
      > </a
      ><a name="10797" class="Symbol"
      >&#8594;</a
      ><a name="10798"
      > </a
      ><a name="10799" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#414" class="Function Operator"
      >&#172;</a
      ><a name="10800"
      > </a
      ><a name="10801" class="Symbol"
      >(</a
      ><a name="10802" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >_&#8801;_</a
      ><a name="10805"
      > </a
      ><a name="10806" class="Symbol"
      >{</a
      ><a name="10807" class="Argument"
      >A</a
      ><a name="10808"
      > </a
      ><a name="10809" class="Symbol"
      >=</a
      ><a name="10810"
      > </a
      ><a name="10811" href="https://agda.github.io/agda-stdlib/Data.Maybe.Base.html#335" class="Datatype"
      >Maybe</a
      ><a name="10816"
      > </a
      ><a name="10817" href="StlcProp.html#10776" class="Bound"
      >X</a
      ><a name="10818" class="Symbol"
      >}</a
      ><a name="10819"
      > </a
      ><a name="10820" class="Symbol"
      >(</a
      ><a name="10821" href="https://agda.github.io/agda-stdlib/Data.Maybe.Base.html#373" class="InductiveConstructor"
      >just</a
      ><a name="10825"
      > </a
      ><a name="10826" href="StlcProp.html#10790" class="Bound"
      >x</a
      ><a name="10827" class="Symbol"
      >)</a
      ><a name="10828"
      > </a
      ><a name="10829" href="https://agda.github.io/agda-stdlib/Data.Maybe.Base.html#403" class="InductiveConstructor"
      >nothing</a
      ><a name="10836" class="Symbol"
      >)</a
      ><a name="10837"
      >
</a
      ><a name="10838" href="StlcProp.html#10757" class="Function"
      >contradiction</a
      ><a name="10851"
      > </a
      ><a name="10852" class="Symbol"
      >()</a
      ><a name="10854"
      >

</a
      ><a name="10856" href="StlcProp.html#10856" class="Function"
      >&#8709;&#8866;-closed&#8242;</a
      ><a name="10866"
      > </a
      ><a name="10867" class="Symbol"
      >:</a
      ><a name="10868"
      > </a
      ><a name="10869" class="Symbol"
      >&#8704;</a
      ><a name="10870"
      > </a
      ><a name="10871" class="Symbol"
      >{</a
      ><a name="10872" href="StlcProp.html#10872" class="Bound"
      >M</a
      ><a name="10873"
      > </a
      ><a name="10874" href="StlcProp.html#10874" class="Bound"
      >A</a
      ><a name="10875" class="Symbol"
      >}</a
      ><a name="10876"
      > </a
      ><a name="10877" class="Symbol"
      >&#8594;</a
      ><a name="10878"
      > </a
      ><a name="10879" href="Maps.html#10359" class="Function"
      >&#8709;</a
      ><a name="10880"
      > </a
      ><a name="10881" href="Stlc.html#3408" class="Datatype Operator"
      >&#8866;</a
      ><a name="10882"
      > </a
      ><a name="10883" href="StlcProp.html#10872" class="Bound"
      >M</a
      ><a name="10884"
      > </a
      ><a name="10885" href="Stlc.html#3408" class="Datatype Operator"
      >&#8758;</a
      ><a name="10886"
      > </a
      ><a name="10887" href="StlcProp.html#10874" class="Bound"
      >A</a
      ><a name="10888"
      > </a
      ><a name="10889" class="Symbol"
      >&#8594;</a
      ><a name="10890"
      > </a
      ><a name="10891" href="StlcProp.html#7529" class="Function"
      >closed</a
      ><a name="10897"
      > </a
      ><a name="10898" href="StlcProp.html#10872" class="Bound"
      >M</a
      ><a name="10899"
      >
</a
      ><a name="10900" href="StlcProp.html#10856" class="Function"
      >&#8709;&#8866;-closed&#8242;</a
      ><a name="10910"
      > </a
      ><a name="10911" class="Symbol"
      >{</a
      ><a name="10912" href="StlcProp.html#10912" class="Bound"
      >M</a
      ><a name="10913" class="Symbol"
      >}</a
      ><a name="10914"
      > </a
      ><a name="10915" class="Symbol"
      >{</a
      ><a name="10916" href="StlcProp.html#10916" class="Bound"
      >A</a
      ><a name="10917" class="Symbol"
      >}</a
      ><a name="10918"
      > </a
      ><a name="10919" href="StlcProp.html#10919" class="Bound"
      >&#8866;M</a
      ><a name="10921"
      > </a
      ><a name="10922" class="Symbol"
      >{</a
      ><a name="10923" href="StlcProp.html#10923" class="Bound"
      >x</a
      ><a name="10924" class="Symbol"
      >}</a
      ><a name="10925"
      > </a
      ><a name="10926" href="StlcProp.html#10926" class="Bound"
      >x&#8712;M</a
      ><a name="10929"
      > </a
      ><a name="10930" class="Keyword"
      >with</a
      ><a name="10934"
      > </a
      ><a name="10935" href="StlcProp.html#8278" class="Function"
      >freeLemma</a
      ><a name="10944"
      > </a
      ><a name="10945" href="StlcProp.html#10926" class="Bound"
      >x&#8712;M</a
      ><a name="10948"
      > </a
      ><a name="10949" href="StlcProp.html#10919" class="Bound"
      >&#8866;M</a
      ><a name="10951"
      >
</a
      ><a name="10952" class="Symbol"
      >...</a
      ><a name="10955"
      > </a
      ><a name="10956" class="Symbol"
      >|</a
      ><a name="10957"
      > </a
      ><a name="10958" class="Symbol"
      >(</a
      ><a name="10959" href="StlcProp.html#10959" class="Bound"
      >B</a
      ><a name="10960"
      > </a
      ><a name="10961" href="https://agda.github.io/agda-stdlib/Data.Product.html#509" class="InductiveConstructor Operator"
      >,</a
      ><a name="10962"
      > </a
      ><a name="10963" href="StlcProp.html#10963" class="Bound"
      >&#8709;x&#8801;justB</a
      ><a name="10971" class="Symbol"
      >)</a
      ><a name="10972"
      > </a
      ><a name="10973" class="Symbol"
      >=</a
      ><a name="10974"
      > </a
      ><a name="10975" href="StlcProp.html#10757" class="Function"
      >contradiction</a
      ><a name="10988"
      > </a
      ><a name="10989" class="Symbol"
      >(</a
      ><a name="10990" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.Core.html#632" class="Function"
      >trans</a
      ><a name="10995"
      > </a
      ><a name="10996" class="Symbol"
      >(</a
      ><a name="10997" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.Core.html#565" class="Function"
      >sym</a
      ><a name="11000"
      > </a
      ><a name="11001" href="StlcProp.html#10963" class="Bound"
      >&#8709;x&#8801;justB</a
      ><a name="11009" class="Symbol"
      >)</a
      ><a name="11010"
      > </a
      ><a name="11011" class="Symbol"
      >(</a
      ><a name="11012" href="Maps.html#10667" class="Function"
      >apply-&#8709;</a
      ><a name="11019"
      > </a
      ><a name="11020" href="StlcProp.html#10923" class="Bound"
      >x</a
      ><a name="11021" class="Symbol"
      >))</a
      >
{% endraw %}</pre>
</div>

Sometimes, when we have a proof `Γ ⊢ M ∶ A`, we will need to
replace `Γ` by a different context `Γ′`.  When is it safe
to do this?  Intuitively, it must at least be the case that
`Γ′` assigns the same types as `Γ` to all the variables
that appear free in `M`. In fact, this is the only condition that
is needed.

<pre class="Agda">{% raw %}
<a name="11369" href="StlcProp.html#11369" class="Function"
      >contextLemma</a
      ><a name="11381"
      > </a
      ><a name="11382" class="Symbol"
      >:</a
      ><a name="11383"
      > </a
      ><a name="11384" class="Symbol"
      >&#8704;</a
      ><a name="11385"
      > </a
      ><a name="11386" class="Symbol"
      >{</a
      ><a name="11387" href="StlcProp.html#11387" class="Bound"
      >&#915;</a
      ><a name="11388"
      > </a
      ><a name="11389" href="StlcProp.html#11389" class="Bound"
      >&#915;&#8242;</a
      ><a name="11391"
      > </a
      ><a name="11392" href="StlcProp.html#11392" class="Bound"
      >M</a
      ><a name="11393"
      > </a
      ><a name="11394" href="StlcProp.html#11394" class="Bound"
      >A</a
      ><a name="11395" class="Symbol"
      >}</a
      ><a name="11396"
      >
        </a
      ><a name="11405" class="Symbol"
      >&#8594;</a
      ><a name="11406"
      > </a
      ><a name="11407" class="Symbol"
      >(&#8704;</a
      ><a name="11409"
      > </a
      ><a name="11410" class="Symbol"
      >{</a
      ><a name="11411" href="StlcProp.html#11411" class="Bound"
      >x</a
      ><a name="11412" class="Symbol"
      >}</a
      ><a name="11413"
      > </a
      ><a name="11414" class="Symbol"
      >&#8594;</a
      ><a name="11415"
      > </a
      ><a name="11416" href="StlcProp.html#11411" class="Bound"
      >x</a
      ><a name="11417"
      > </a
      ><a name="11418" href="StlcProp.html#7047" class="Datatype Operator"
      >&#8712;</a
      ><a name="11419"
      > </a
      ><a name="11420" href="StlcProp.html#11392" class="Bound"
      >M</a
      ><a name="11421"
      > </a
      ><a name="11422" class="Symbol"
      >&#8594;</a
      ><a name="11423"
      > </a
      ><a name="11424" href="StlcProp.html#11387" class="Bound"
      >&#915;</a
      ><a name="11425"
      > </a
      ><a name="11426" href="StlcProp.html#11411" class="Bound"
      >x</a
      ><a name="11427"
      > </a
      ><a name="11428" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="11429"
      > </a
      ><a name="11430" href="StlcProp.html#11389" class="Bound"
      >&#915;&#8242;</a
      ><a name="11432"
      > </a
      ><a name="11433" href="StlcProp.html#11411" class="Bound"
      >x</a
      ><a name="11434" class="Symbol"
      >)</a
      ><a name="11435"
      >
        </a
      ><a name="11444" class="Symbol"
      >&#8594;</a
      ><a name="11445"
      > </a
      ><a name="11446" href="StlcProp.html#11387" class="Bound"
      >&#915;</a
      ><a name="11447"
      >  </a
      ><a name="11449" href="Stlc.html#3408" class="Datatype Operator"
      >&#8866;</a
      ><a name="11450"
      > </a
      ><a name="11451" href="StlcProp.html#11392" class="Bound"
      >M</a
      ><a name="11452"
      > </a
      ><a name="11453" href="Stlc.html#3408" class="Datatype Operator"
      >&#8758;</a
      ><a name="11454"
      > </a
      ><a name="11455" href="StlcProp.html#11394" class="Bound"
      >A</a
      ><a name="11456"
      >
        </a
      ><a name="11465" class="Symbol"
      >&#8594;</a
      ><a name="11466"
      > </a
      ><a name="11467" href="StlcProp.html#11389" class="Bound"
      >&#915;&#8242;</a
      ><a name="11469"
      > </a
      ><a name="11470" href="Stlc.html#3408" class="Datatype Operator"
      >&#8866;</a
      ><a name="11471"
      > </a
      ><a name="11472" href="StlcProp.html#11392" class="Bound"
      >M</a
      ><a name="11473"
      > </a
      ><a name="11474" href="Stlc.html#3408" class="Datatype Operator"
      >&#8758;</a
      ><a name="11475"
      > </a
      ><a name="11476" href="StlcProp.html#11394" class="Bound"
      >A</a
      >
{% endraw %}</pre>

_Proof_: By induction on the derivation of
`Γ ⊢ M ∶ A`.

  - If the last rule in the derivation was `var`, then `t = x`
    and `\Gamma x = T`.  By assumption, `\Gamma' x = T` as well, and
    hence `\Gamma' \vdash t : T` by `var`.

  - If the last rule was `abs`, then `t = \lambda y:A. t'`, with
    `T = A\to B` and `\Gamma, y : A \vdash t' : B`.  The
    induction hypothesis is that, for any context `\Gamma''`, if
    `\Gamma, y:A` and `\Gamma''` assign the same types to all the
    free variables in `t'`, then `t'` has type `B` under
    `\Gamma''`.  Let `\Gamma'` be a context which agrees with
    `\Gamma` on the free variables in `t`; we must show
    `\Gamma' \vdash \lambda y:A. t' : A\to B`.

    By `abs`, it suffices to show that `\Gamma', y:A \vdash t' : t'`.
    By the IH (setting `\Gamma'' = \Gamma', y:A`), it suffices to show
    that `\Gamma, y:A` and `\Gamma', y:A` agree on all the variables
    that appear free in `t'`.

    Any variable occurring free in `t'` must be either `y` or
    some other variable.  `\Gamma, y:A` and `\Gamma', y:A`
    clearly agree on `y`.  Otherwise, note that any variable other
    than `y` that occurs free in `t'` also occurs free in
    `t = \lambda y:A. t'`, and by assumption `\Gamma` and
    `\Gamma'` agree on all such variables; hence so do `\Gamma, y:A` and
    `\Gamma', y:A`.

  - If the last rule was `app`, then `t = t_1\;t_2`, with
    `\Gamma \vdash t_1:A\to T` and `\Gamma \vdash t_2:A`.
    One induction hypothesis states that for all contexts `\Gamma'`,
    if `\Gamma'` agrees with `\Gamma` on the free variables in `t_1`,
    then `t_1` has type `A\to T` under `\Gamma'`; there is a similar IH
    for `t_2`.  We must show that `t_1\;t_2` also has type `T` under
    `\Gamma'`, given the assumption that `\Gamma'` agrees with
    `\Gamma` on all the free variables in `t_1\;t_2`.  By `app`, it
    suffices to show that `t_1` and `t_2` each have the same type
    under `\Gamma'` as under `\Gamma`.  But all free variables in
    `t_1` are also free in `t_1\;t_2`, and similarly for `t_2`;
    hence the desired result follows from the induction hypotheses.

<pre class="Agda">{% raw %}
<a name="13643" href="StlcProp.html#11369" class="Function"
      >contextLemma</a
      ><a name="13655"
      > </a
      ><a name="13656" href="StlcProp.html#13656" class="Bound"
      >&#915;~&#915;&#8242;</a
      ><a name="13660"
      > </a
      ><a name="13661" class="Symbol"
      >(</a
      ><a name="13662" href="Stlc.html#3452" class="InductiveConstructor"
      >Ax</a
      ><a name="13664"
      > </a
      ><a name="13665" href="StlcProp.html#13665" class="Bound"
      >&#915;x&#8801;justA</a
      ><a name="13673" class="Symbol"
      >)</a
      ><a name="13674"
      > </a
      ><a name="13675" class="Keyword"
      >rewrite</a
      ><a name="13682"
      > </a
      ><a name="13683" class="Symbol"
      >(</a
      ><a name="13684" href="StlcProp.html#13656" class="Bound"
      >&#915;~&#915;&#8242;</a
      ><a name="13688"
      > </a
      ><a name="13689" href="StlcProp.html#7077" class="InductiveConstructor"
      >free-var</a
      ><a name="13697" class="Symbol"
      >)</a
      ><a name="13698"
      > </a
      ><a name="13699" class="Symbol"
      >=</a
      ><a name="13700"
      > </a
      ><a name="13701" href="Stlc.html#3452" class="InductiveConstructor"
      >Ax</a
      ><a name="13703"
      > </a
      ><a name="13704" href="StlcProp.html#13665" class="Bound"
      >&#915;x&#8801;justA</a
      ><a name="13712"
      >
</a
      ><a name="13713" href="StlcProp.html#11369" class="Function"
      >contextLemma</a
      ><a name="13725"
      > </a
      ><a name="13726" class="Symbol"
      >{</a
      ><a name="13727" href="StlcProp.html#13727" class="Bound"
      >&#915;</a
      ><a name="13728" class="Symbol"
      >}</a
      ><a name="13729"
      > </a
      ><a name="13730" class="Symbol"
      >{</a
      ><a name="13731" href="StlcProp.html#13731" class="Bound"
      >&#915;&#8242;</a
      ><a name="13733" class="Symbol"
      >}</a
      ><a name="13734"
      > </a
      ><a name="13735" class="Symbol"
      >{</a
      ><a name="13736" href="Stlc.html#752" class="InductiveConstructor Operator"
      >&#955;[</a
      ><a name="13738"
      > </a
      ><a name="13739" href="StlcProp.html#13739" class="Bound"
      >x</a
      ><a name="13740"
      > </a
      ><a name="13741" href="Stlc.html#752" class="InductiveConstructor Operator"
      >&#8758;</a
      ><a name="13742"
      > </a
      ><a name="13743" href="StlcProp.html#13743" class="Bound"
      >A</a
      ><a name="13744"
      > </a
      ><a name="13745" href="Stlc.html#752" class="InductiveConstructor Operator"
      >]</a
      ><a name="13746"
      > </a
      ><a name="13747" href="StlcProp.html#13747" class="Bound"
      >N</a
      ><a name="13748" class="Symbol"
      >}</a
      ><a name="13749"
      > </a
      ><a name="13750" href="StlcProp.html#13750" class="Bound"
      >&#915;~&#915;&#8242;</a
      ><a name="13754"
      > </a
      ><a name="13755" class="Symbol"
      >(</a
      ><a name="13756" href="Stlc.html#3508" class="InductiveConstructor"
      >&#8658;-I</a
      ><a name="13759"
      > </a
      ><a name="13760" href="StlcProp.html#13760" class="Bound"
      >&#8866;N</a
      ><a name="13762" class="Symbol"
      >)</a
      ><a name="13763"
      > </a
      ><a name="13764" class="Symbol"
      >=</a
      ><a name="13765"
      > </a
      ><a name="13766" href="Stlc.html#3508" class="InductiveConstructor"
      >&#8658;-I</a
      ><a name="13769"
      > </a
      ><a name="13770" class="Symbol"
      >(</a
      ><a name="13771" href="StlcProp.html#11369" class="Function"
      >contextLemma</a
      ><a name="13783"
      > </a
      ><a name="13784" href="StlcProp.html#13805" class="Function"
      >&#915;x~&#915;&#8242;x</a
      ><a name="13790"
      > </a
      ><a name="13791" href="StlcProp.html#13760" class="Bound"
      >&#8866;N</a
      ><a name="13793" class="Symbol"
      >)</a
      ><a name="13794"
      >
  </a
      ><a name="13797" class="Keyword"
      >where</a
      ><a name="13802"
      >
  </a
      ><a name="13805" href="StlcProp.html#13805" class="Function"
      >&#915;x~&#915;&#8242;x</a
      ><a name="13811"
      > </a
      ><a name="13812" class="Symbol"
      >:</a
      ><a name="13813"
      > </a
      ><a name="13814" class="Symbol"
      >&#8704;</a
      ><a name="13815"
      > </a
      ><a name="13816" class="Symbol"
      >{</a
      ><a name="13817" href="StlcProp.html#13817" class="Bound"
      >y</a
      ><a name="13818" class="Symbol"
      >}</a
      ><a name="13819"
      > </a
      ><a name="13820" class="Symbol"
      >&#8594;</a
      ><a name="13821"
      > </a
      ><a name="13822" href="StlcProp.html#13817" class="Bound"
      >y</a
      ><a name="13823"
      > </a
      ><a name="13824" href="StlcProp.html#7047" class="Datatype Operator"
      >&#8712;</a
      ><a name="13825"
      > </a
      ><a name="13826" href="StlcProp.html#13747" class="Bound"
      >N</a
      ><a name="13827"
      > </a
      ><a name="13828" class="Symbol"
      >&#8594;</a
      ><a name="13829"
      > </a
      ><a name="13830" class="Symbol"
      >(</a
      ><a name="13831" href="StlcProp.html#13727" class="Bound"
      >&#915;</a
      ><a name="13832"
      > </a
      ><a name="13833" href="Maps.html#10462" class="Function Operator"
      >,</a
      ><a name="13834"
      > </a
      ><a name="13835" href="StlcProp.html#13739" class="Bound"
      >x</a
      ><a name="13836"
      > </a
      ><a name="13837" href="Maps.html#10462" class="Function Operator"
      >&#8758;</a
      ><a name="13838"
      > </a
      ><a name="13839" href="StlcProp.html#13743" class="Bound"
      >A</a
      ><a name="13840" class="Symbol"
      >)</a
      ><a name="13841"
      > </a
      ><a name="13842" href="StlcProp.html#13817" class="Bound"
      >y</a
      ><a name="13843"
      > </a
      ><a name="13844" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="13845"
      > </a
      ><a name="13846" class="Symbol"
      >(</a
      ><a name="13847" href="StlcProp.html#13731" class="Bound"
      >&#915;&#8242;</a
      ><a name="13849"
      > </a
      ><a name="13850" href="Maps.html#10462" class="Function Operator"
      >,</a
      ><a name="13851"
      > </a
      ><a name="13852" href="StlcProp.html#13739" class="Bound"
      >x</a
      ><a name="13853"
      > </a
      ><a name="13854" href="Maps.html#10462" class="Function Operator"
      >&#8758;</a
      ><a name="13855"
      > </a
      ><a name="13856" href="StlcProp.html#13743" class="Bound"
      >A</a
      ><a name="13857" class="Symbol"
      >)</a
      ><a name="13858"
      > </a
      ><a name="13859" href="StlcProp.html#13817" class="Bound"
      >y</a
      ><a name="13860"
      >
  </a
      ><a name="13863" href="StlcProp.html#13805" class="Function"
      >&#915;x~&#915;&#8242;x</a
      ><a name="13869"
      > </a
      ><a name="13870" class="Symbol"
      >{</a
      ><a name="13871" href="StlcProp.html#13871" class="Bound"
      >y</a
      ><a name="13872" class="Symbol"
      >}</a
      ><a name="13873"
      > </a
      ><a name="13874" href="StlcProp.html#13874" class="Bound"
      >y&#8712;N</a
      ><a name="13877"
      > </a
      ><a name="13878" class="Keyword"
      >with</a
      ><a name="13882"
      > </a
      ><a name="13883" href="StlcProp.html#13739" class="Bound"
      >x</a
      ><a name="13884"
      > </a
      ><a name="13885" href="Maps.html#2558" class="Function Operator"
      >&#8799;</a
      ><a name="13886"
      > </a
      ><a name="13887" href="StlcProp.html#13871" class="Bound"
      >y</a
      ><a name="13888"
      >
  </a
      ><a name="13891" class="Symbol"
      >...</a
      ><a name="13894"
      > </a
      ><a name="13895" class="Symbol"
      >|</a
      ><a name="13896"
      > </a
      ><a name="13897" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#520" class="InductiveConstructor"
      >yes</a
      ><a name="13900"
      > </a
      ><a name="13901" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="13905"
      > </a
      ><a name="13906" class="Symbol"
      >=</a
      ><a name="13907"
      > </a
      ><a name="13908" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="13912"
      >
  </a
      ><a name="13915" class="Symbol"
      >...</a
      ><a name="13918"
      > </a
      ><a name="13919" class="Symbol"
      >|</a
      ><a name="13920"
      > </a
      ><a name="13921" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#547" class="InductiveConstructor"
      >no</a
      ><a name="13923"
      >  </a
      ><a name="13925" href="StlcProp.html#13925" class="Bound"
      >x&#8802;y</a
      ><a name="13928"
      >  </a
      ><a name="13930" class="Symbol"
      >=</a
      ><a name="13931"
      > </a
      ><a name="13932" href="StlcProp.html#13750" class="Bound"
      >&#915;~&#915;&#8242;</a
      ><a name="13936"
      > </a
      ><a name="13937" class="Symbol"
      >(</a
      ><a name="13938" href="StlcProp.html#7111" class="InductiveConstructor"
      >free-&#955;</a
      ><a name="13944"
      > </a
      ><a name="13945" href="StlcProp.html#13925" class="Bound"
      >x&#8802;y</a
      ><a name="13948"
      > </a
      ><a name="13949" href="StlcProp.html#13874" class="Bound"
      >y&#8712;N</a
      ><a name="13952" class="Symbol"
      >)</a
      ><a name="13953"
      >
</a
      ><a name="13954" href="StlcProp.html#11369" class="Function"
      >contextLemma</a
      ><a name="13966"
      > </a
      ><a name="13967" href="StlcProp.html#13967" class="Bound"
      >&#915;~&#915;&#8242;</a
      ><a name="13971"
      > </a
      ><a name="13972" class="Symbol"
      >(</a
      ><a name="13973" href="Stlc.html#3585" class="InductiveConstructor"
      >&#8658;-E</a
      ><a name="13976"
      > </a
      ><a name="13977" href="StlcProp.html#13977" class="Bound"
      >&#8866;L</a
      ><a name="13979"
      > </a
      ><a name="13980" href="StlcProp.html#13980" class="Bound"
      >&#8866;M</a
      ><a name="13982" class="Symbol"
      >)</a
      ><a name="13983"
      > </a
      ><a name="13984" class="Symbol"
      >=</a
      ><a name="13985"
      > </a
      ><a name="13986" href="Stlc.html#3585" class="InductiveConstructor"
      >&#8658;-E</a
      ><a name="13989"
      > </a
      ><a name="13990" class="Symbol"
      >(</a
      ><a name="13991" href="StlcProp.html#11369" class="Function"
      >contextLemma</a
      ><a name="14003"
      > </a
      ><a name="14004" class="Symbol"
      >(</a
      ><a name="14005" href="StlcProp.html#13967" class="Bound"
      >&#915;~&#915;&#8242;</a
      ><a name="14009"
      > </a
      ><a name="14010" href="https://agda.github.io/agda-stdlib/Function.html#713" class="Function Operator"
      >&#8728;</a
      ><a name="14011"
      > </a
      ><a name="14012" href="StlcProp.html#7172" class="InductiveConstructor"
      >free-&#183;&#8321;</a
      ><a name="14019" class="Symbol"
      >)</a
      ><a name="14020"
      >  </a
      ><a name="14022" href="StlcProp.html#13977" class="Bound"
      >&#8866;L</a
      ><a name="14024" class="Symbol"
      >)</a
      ><a name="14025"
      > </a
      ><a name="14026" class="Symbol"
      >(</a
      ><a name="14027" href="StlcProp.html#11369" class="Function"
      >contextLemma</a
      ><a name="14039"
      > </a
      ><a name="14040" class="Symbol"
      >(</a
      ><a name="14041" href="StlcProp.html#13967" class="Bound"
      >&#915;~&#915;&#8242;</a
      ><a name="14045"
      > </a
      ><a name="14046" href="https://agda.github.io/agda-stdlib/Function.html#713" class="Function Operator"
      >&#8728;</a
      ><a name="14047"
      > </a
      ><a name="14048" href="StlcProp.html#7216" class="InductiveConstructor"
      >free-&#183;&#8322;</a
      ><a name="14055" class="Symbol"
      >)</a
      ><a name="14056"
      > </a
      ><a name="14057" href="StlcProp.html#13980" class="Bound"
      >&#8866;M</a
      ><a name="14059" class="Symbol"
      >)</a
      ><a name="14060"
      > 
</a
      ><a name="14062" href="StlcProp.html#11369" class="Function"
      >contextLemma</a
      ><a name="14074"
      > </a
      ><a name="14075" href="StlcProp.html#14075" class="Bound"
      >&#915;~&#915;&#8242;</a
      ><a name="14079"
      > </a
      ><a name="14080" href="Stlc.html#3663" class="InductiveConstructor"
      >&#120121;-I&#8321;</a
      ><a name="14084"
      > </a
      ><a name="14085" class="Symbol"
      >=</a
      ><a name="14086"
      > </a
      ><a name="14087" href="Stlc.html#3663" class="InductiveConstructor"
      >&#120121;-I&#8321;</a
      ><a name="14091"
      >
</a
      ><a name="14092" href="StlcProp.html#11369" class="Function"
      >contextLemma</a
      ><a name="14104"
      > </a
      ><a name="14105" href="StlcProp.html#14105" class="Bound"
      >&#915;~&#915;&#8242;</a
      ><a name="14109"
      > </a
      ><a name="14110" href="Stlc.html#3697" class="InductiveConstructor"
      >&#120121;-I&#8322;</a
      ><a name="14114"
      > </a
      ><a name="14115" class="Symbol"
      >=</a
      ><a name="14116"
      > </a
      ><a name="14117" href="Stlc.html#3697" class="InductiveConstructor"
      >&#120121;-I&#8322;</a
      ><a name="14121"
      >
</a
      ><a name="14122" href="StlcProp.html#11369" class="Function"
      >contextLemma</a
      ><a name="14134"
      > </a
      ><a name="14135" href="StlcProp.html#14135" class="Bound"
      >&#915;~&#915;&#8242;</a
      ><a name="14139"
      > </a
      ><a name="14140" class="Symbol"
      >(</a
      ><a name="14141" href="Stlc.html#3732" class="InductiveConstructor"
      >&#120121;-E</a
      ><a name="14144"
      > </a
      ><a name="14145" href="StlcProp.html#14145" class="Bound"
      >&#8866;L</a
      ><a name="14147"
      > </a
      ><a name="14148" href="StlcProp.html#14148" class="Bound"
      >&#8866;M</a
      ><a name="14150"
      > </a
      ><a name="14151" href="StlcProp.html#14151" class="Bound"
      >&#8866;N</a
      ><a name="14153" class="Symbol"
      >)</a
      ><a name="14154"
      >
  </a
      ><a name="14157" class="Symbol"
      >=</a
      ><a name="14158"
      > </a
      ><a name="14159" href="Stlc.html#3732" class="InductiveConstructor"
      >&#120121;-E</a
      ><a name="14162"
      > </a
      ><a name="14163" class="Symbol"
      >(</a
      ><a name="14164" href="StlcProp.html#11369" class="Function"
      >contextLemma</a
      ><a name="14176"
      > </a
      ><a name="14177" class="Symbol"
      >(</a
      ><a name="14178" href="StlcProp.html#14135" class="Bound"
      >&#915;~&#915;&#8242;</a
      ><a name="14182"
      > </a
      ><a name="14183" href="https://agda.github.io/agda-stdlib/Function.html#713" class="Function Operator"
      >&#8728;</a
      ><a name="14184"
      > </a
      ><a name="14185" href="StlcProp.html#7260" class="InductiveConstructor"
      >free-if&#8321;</a
      ><a name="14193" class="Symbol"
      >)</a
      ><a name="14194"
      > </a
      ><a name="14195" href="StlcProp.html#14145" class="Bound"
      >&#8866;L</a
      ><a name="14197" class="Symbol"
      >)</a
      ><a name="14198"
      > </a
      ><a name="14199" class="Symbol"
      >(</a
      ><a name="14200" href="StlcProp.html#11369" class="Function"
      >contextLemma</a
      ><a name="14212"
      > </a
      ><a name="14213" class="Symbol"
      >(</a
      ><a name="14214" href="StlcProp.html#14135" class="Bound"
      >&#915;~&#915;&#8242;</a
      ><a name="14218"
      > </a
      ><a name="14219" href="https://agda.github.io/agda-stdlib/Function.html#713" class="Function Operator"
      >&#8728;</a
      ><a name="14220"
      > </a
      ><a name="14221" href="StlcProp.html#7320" class="InductiveConstructor"
      >free-if&#8322;</a
      ><a name="14229" class="Symbol"
      >)</a
      ><a name="14230"
      > </a
      ><a name="14231" href="StlcProp.html#14148" class="Bound"
      >&#8866;M</a
      ><a name="14233" class="Symbol"
      >)</a
      ><a name="14234"
      > </a
      ><a name="14235" class="Symbol"
      >(</a
      ><a name="14236" href="StlcProp.html#11369" class="Function"
      >contextLemma</a
      ><a name="14248"
      > </a
      ><a name="14249" class="Symbol"
      >(</a
      ><a name="14250" href="StlcProp.html#14135" class="Bound"
      >&#915;~&#915;&#8242;</a
      ><a name="14254"
      > </a
      ><a name="14255" href="https://agda.github.io/agda-stdlib/Function.html#713" class="Function Operator"
      >&#8728;</a
      ><a name="14256"
      > </a
      ><a name="14257" href="StlcProp.html#7380" class="InductiveConstructor"
      >free-if&#8323;</a
      ><a name="14265" class="Symbol"
      >)</a
      ><a name="14266"
      > </a
      ><a name="14267" href="StlcProp.html#14151" class="Bound"
      >&#8866;N</a
      ><a name="14269" class="Symbol"
      >)</a
      ><a name="14270"
      >

</a
      ><a name="14272" class="Comment"
      >{-
replaceCtxt f (var x x&#8758;A
) rewrite f var = var x x&#8758;A
replaceCtxt f (app t&#8321;&#8758;A&#8658;B t&#8322;&#8758;A)
  = app (replaceCtxt (f &#8728; app1) t&#8321;&#8758;A&#8658;B) (replaceCtxt (f &#8728; app2) t&#8322;&#8758;A)
replaceCtxt {&#915;} {&#915;&#8242;} f (abs {.&#915;} {x} {A} {B} {t&#8242;} t&#8242;&#8758;B)
  = abs (replaceCtxt f&#8242; t&#8242;&#8758;B)
  where
    f&#8242; : &#8704; {y} &#8594; y &#8712; t&#8242; &#8594; (&#915; , x &#8758; A) y &#8801; (&#915;&#8242; , x &#8758; A) y
    f&#8242; {y} y&#8712;t&#8242; with x &#8799; y
    ... | yes _   = refl
    ... | no  x&#8800;y = f (abs x&#8800;y y&#8712;t&#8242;)
replaceCtxt _ true  = true
replaceCtxt _ false = false
replaceCtxt f (if t&#8321;&#8758;bool then t&#8322;&#8758;A else t&#8323;&#8758;A)
  = if   replaceCtxt (f &#8728; if1) t&#8321;&#8758;bool
    then replaceCtxt (f &#8728; if2) t&#8322;&#8758;A
    else replaceCtxt (f &#8728; if3) t&#8323;&#8758;A
-}</a
      >
{% endraw %}</pre>


Now we come to the conceptual heart of the proof that reduction
preserves types---namely, the observation that _substitution_
preserves types.

Formally, the so-called _Substitution Lemma_ says this: Suppose we
have a term `N` with a free variable `x`, and suppose we've been
able to assign a type `B` to `N` under the assumption that `x` has
some type `A`.  Also, suppose that we have some other term `V` and
that we've shown that `V` has type `A`.  Then, since `V` satisfies
the assumption we made about `x` when typing `N`, we should be
able to substitute `V` for each of the occurrences of `x` in `N`
and obtain a new term that still has type `B`.

_Lemma_: If `Γ , x ∶ A ⊢ N ∶ B` and `∅ ⊢ V ∶ A`, then
`Γ ⊢ (N [ x ∶= V ]) ∶ B`.

<pre class="Agda">{% raw %}
<a name="15646" href="StlcProp.html#15646" class="Function"
      >preservation-[&#8758;=]</a
      ><a name="15663"
      > </a
      ><a name="15664" class="Symbol"
      >:</a
      ><a name="15665"
      > </a
      ><a name="15666" class="Symbol"
      >&#8704;</a
      ><a name="15667"
      > </a
      ><a name="15668" class="Symbol"
      >{</a
      ><a name="15669" href="StlcProp.html#15669" class="Bound"
      >&#915;</a
      ><a name="15670"
      > </a
      ><a name="15671" href="StlcProp.html#15671" class="Bound"
      >x</a
      ><a name="15672"
      > </a
      ><a name="15673" href="StlcProp.html#15673" class="Bound"
      >A</a
      ><a name="15674"
      > </a
      ><a name="15675" href="StlcProp.html#15675" class="Bound"
      >N</a
      ><a name="15676"
      > </a
      ><a name="15677" href="StlcProp.html#15677" class="Bound"
      >B</a
      ><a name="15678"
      > </a
      ><a name="15679" href="StlcProp.html#15679" class="Bound"
      >V</a
      ><a name="15680" class="Symbol"
      >}</a
      ><a name="15681"
      >
                 </a
      ><a name="15699" class="Symbol"
      >&#8594;</a
      ><a name="15700"
      > </a
      ><a name="15701" class="Symbol"
      >(</a
      ><a name="15702" href="StlcProp.html#15669" class="Bound"
      >&#915;</a
      ><a name="15703"
      > </a
      ><a name="15704" href="Maps.html#10462" class="Function Operator"
      >,</a
      ><a name="15705"
      > </a
      ><a name="15706" href="StlcProp.html#15671" class="Bound"
      >x</a
      ><a name="15707"
      > </a
      ><a name="15708" href="Maps.html#10462" class="Function Operator"
      >&#8758;</a
      ><a name="15709"
      > </a
      ><a name="15710" href="StlcProp.html#15673" class="Bound"
      >A</a
      ><a name="15711" class="Symbol"
      >)</a
      ><a name="15712"
      > </a
      ><a name="15713" href="Stlc.html#3408" class="Datatype Operator"
      >&#8866;</a
      ><a name="15714"
      > </a
      ><a name="15715" href="StlcProp.html#15675" class="Bound"
      >N</a
      ><a name="15716"
      > </a
      ><a name="15717" href="Stlc.html#3408" class="Datatype Operator"
      >&#8758;</a
      ><a name="15718"
      > </a
      ><a name="15719" href="StlcProp.html#15677" class="Bound"
      >B</a
      ><a name="15720"
      >
                 </a
      ><a name="15738" class="Symbol"
      >&#8594;</a
      ><a name="15739"
      > </a
      ><a name="15740" href="Maps.html#10359" class="Function"
      >&#8709;</a
      ><a name="15741"
      > </a
      ><a name="15742" href="Stlc.html#3408" class="Datatype Operator"
      >&#8866;</a
      ><a name="15743"
      > </a
      ><a name="15744" href="StlcProp.html#15679" class="Bound"
      >V</a
      ><a name="15745"
      > </a
      ><a name="15746" href="Stlc.html#3408" class="Datatype Operator"
      >&#8758;</a
      ><a name="15747"
      > </a
      ><a name="15748" href="StlcProp.html#15673" class="Bound"
      >A</a
      ><a name="15749"
      >
                 </a
      ><a name="15767" class="Symbol"
      >&#8594;</a
      ><a name="15768"
      > </a
      ><a name="15769" href="StlcProp.html#15669" class="Bound"
      >&#915;</a
      ><a name="15770"
      > </a
      ><a name="15771" href="Stlc.html#3408" class="Datatype Operator"
      >&#8866;</a
      ><a name="15772"
      > </a
      ><a name="15773" class="Symbol"
      >(</a
      ><a name="15774" href="StlcProp.html#15675" class="Bound"
      >N</a
      ><a name="15775"
      > </a
      ><a name="15776" href="Stlc.html#1297" class="Function Operator"
      >[</a
      ><a name="15777"
      > </a
      ><a name="15778" href="StlcProp.html#15671" class="Bound"
      >x</a
      ><a name="15779"
      > </a
      ><a name="15780" href="Stlc.html#1297" class="Function Operator"
      >&#8758;=</a
      ><a name="15782"
      > </a
      ><a name="15783" href="StlcProp.html#15679" class="Bound"
      >V</a
      ><a name="15784"
      > </a
      ><a name="15785" href="Stlc.html#1297" class="Function Operator"
      >]</a
      ><a name="15786" class="Symbol"
      >)</a
      ><a name="15787"
      > </a
      ><a name="15788" href="Stlc.html#3408" class="Datatype Operator"
      >&#8758;</a
      ><a name="15789"
      > </a
      ><a name="15790" href="StlcProp.html#15677" class="Bound"
      >B</a
      >
{% endraw %}</pre>

One technical subtlety in the statement of the lemma is that
we assign `V` the type `A` in the _empty_ context---in other
words, we assume `V` is closed.  This assumption considerably
simplifies the `λ` case of the proof (compared to assuming
`Γ ⊢ V ∶ A`, which would be the other reasonable assumption
at this point) because the context invariance lemma then tells us
that `V` has type `A` in any context at all---we don't have to
worry about free variables in `V` clashing with the variable being
introduced into the context by `λ`.

The substitution lemma can be viewed as a kind of "commutation"
property.  Intuitively, it says that substitution and typing can
be done in either order: we can either assign types to the terms
`N` and `V` separately (under suitable contexts) and then combine
them using substitution, or we can substitute first and then
assign a type to `N [ x ∶= V ]`---the result is the same either
way.

_Proof_: We show, by induction on `N`, that for all `A` and
`Γ`, if `Γ , x ∶ A \vdash N ∶ B` and `∅ ⊢ V ∶ A`, then
`Γ \vdash N [ x ∶= V ] ∶ B`.

  - If `N` is a variable there are two cases to consider,
    depending on whether `N` is `x` or some other variable.

      - If `N = var x`, then from the fact that `Γ , x ∶ A ⊢ N ∶ B`
        we conclude that `A = B`.  We must show that `x [ x ∶= V] =
        V` has type `A` under `Γ`, given the assumption that
        `V` has type `A` under the empty context.  This
        follows from context invariance: if a closed term has type
        `A` in the empty context, it has that type in any context.

      - If `N` is some variable `x′` different from `x`, then
        we need only note that `x′` has the same type under `Γ , x ∶ A`
        as under `Γ`.

  - If `N` is an abstraction `λ[ x′ ∶ A′ ] N′`, then the IH tells us,
    for all `Γ′`́ and `B′`, that if `Γ′ , x ∶ A ⊢ N′ ∶ B′`
    and `∅ ⊢ V ∶ A`, then `Γ′ ⊢ N′ [ x ∶= V ] ∶ B′`.

    The substitution in the conclusion behaves differently
    depending on whether `x` and `x′` are the same variable.

    First, suppose `x ≡ x′`.  Then, by the definition of
    substitution, `N [ x ∶= V] = N`, so we just need to show `Γ ⊢ N ∶ B`.
    But we know `Γ , x ∶ A ⊢ N ∶ B` and, since `x ≡ x′`
    does not appear free in `λ[ x′ ∶ A′ ] N′`, the context invariance
    lemma yields `Γ ⊢ N ∶ B`.

    Second, suppose `x ≢ x′`.  We know `Γ , x ∶ A , x′ ∶ A′ ⊢ N′ ∶ B′`
    by inversion of the typing relation, from which
    `Γ , x′ ∶ A′ , x ∶ A ⊢ N′ ∶ B′` follows by update permute,
    so the IH applies, giving us `Γ , x′ ∶ A′ ⊢ N′ [ x ∶= V ] ∶ B′`
    By `⇒-I`, we have `Γ ⊢ λ[ x′ ∶ A′ ] (N′ [ x ∶= V ]) ∶ A′ ⇒ B′`
    and the definition of substitution (noting `x ≢ x′`) gives
    `Γ ⊢ (λ[ x′ ∶ A′ ] N′) [ x ∶= V ] ∶ A′ ⇒ B′` as required.

  - If `N` is an application `L′ · M′`, the result follows
    straightforwardly from the definition of substitution and the
    induction hypotheses.

  - The remaining cases are similar to the application case.

We need a couple of lemmas. A closed term can be weakened to any context, and just is injective.
<pre class="Agda">{% raw %}
<a name="18903" href="StlcProp.html#18903" class="Function"
      >weaken-closed</a
      ><a name="18916"
      > </a
      ><a name="18917" class="Symbol"
      >:</a
      ><a name="18918"
      > </a
      ><a name="18919" class="Symbol"
      >&#8704;</a
      ><a name="18920"
      > </a
      ><a name="18921" class="Symbol"
      >{</a
      ><a name="18922" href="StlcProp.html#18922" class="Bound"
      >V</a
      ><a name="18923"
      > </a
      ><a name="18924" href="StlcProp.html#18924" class="Bound"
      >A</a
      ><a name="18925"
      > </a
      ><a name="18926" href="StlcProp.html#18926" class="Bound"
      >&#915;</a
      ><a name="18927" class="Symbol"
      >}</a
      ><a name="18928"
      > </a
      ><a name="18929" class="Symbol"
      >&#8594;</a
      ><a name="18930"
      > </a
      ><a name="18931" href="Maps.html#10359" class="Function"
      >&#8709;</a
      ><a name="18932"
      > </a
      ><a name="18933" href="Stlc.html#3408" class="Datatype Operator"
      >&#8866;</a
      ><a name="18934"
      > </a
      ><a name="18935" href="StlcProp.html#18922" class="Bound"
      >V</a
      ><a name="18936"
      > </a
      ><a name="18937" href="Stlc.html#3408" class="Datatype Operator"
      >&#8758;</a
      ><a name="18938"
      > </a
      ><a name="18939" href="StlcProp.html#18924" class="Bound"
      >A</a
      ><a name="18940"
      > </a
      ><a name="18941" class="Symbol"
      >&#8594;</a
      ><a name="18942"
      > </a
      ><a name="18943" href="StlcProp.html#18926" class="Bound"
      >&#915;</a
      ><a name="18944"
      > </a
      ><a name="18945" href="Stlc.html#3408" class="Datatype Operator"
      >&#8866;</a
      ><a name="18946"
      > </a
      ><a name="18947" href="StlcProp.html#18922" class="Bound"
      >V</a
      ><a name="18948"
      > </a
      ><a name="18949" href="Stlc.html#3408" class="Datatype Operator"
      >&#8758;</a
      ><a name="18950"
      > </a
      ><a name="18951" href="StlcProp.html#18924" class="Bound"
      >A</a
      ><a name="18952"
      >
</a
      ><a name="18953" href="StlcProp.html#18903" class="Function"
      >weaken-closed</a
      ><a name="18966"
      > </a
      ><a name="18967" class="Symbol"
      >{</a
      ><a name="18968" href="StlcProp.html#18968" class="Bound"
      >V</a
      ><a name="18969" class="Symbol"
      >}</a
      ><a name="18970"
      > </a
      ><a name="18971" class="Symbol"
      >{</a
      ><a name="18972" href="StlcProp.html#18972" class="Bound"
      >A</a
      ><a name="18973" class="Symbol"
      >}</a
      ><a name="18974"
      > </a
      ><a name="18975" class="Symbol"
      >{</a
      ><a name="18976" href="StlcProp.html#18976" class="Bound"
      >&#915;</a
      ><a name="18977" class="Symbol"
      >}</a
      ><a name="18978"
      > </a
      ><a name="18979" href="StlcProp.html#18979" class="Bound"
      >&#8866;V</a
      ><a name="18981"
      > </a
      ><a name="18982" class="Symbol"
      >=</a
      ><a name="18983"
      > </a
      ><a name="18984" href="StlcProp.html#11369" class="Function"
      >contextLemma</a
      ><a name="18996"
      > </a
      ><a name="18997" href="StlcProp.html#19015" class="Function"
      >&#915;~&#915;&#8242;</a
      ><a name="19001"
      > </a
      ><a name="19002" href="StlcProp.html#18979" class="Bound"
      >&#8866;V</a
      ><a name="19004"
      >
  </a
      ><a name="19007" class="Keyword"
      >where</a
      ><a name="19012"
      >
  </a
      ><a name="19015" href="StlcProp.html#19015" class="Function"
      >&#915;~&#915;&#8242;</a
      ><a name="19019"
      > </a
      ><a name="19020" class="Symbol"
      >:</a
      ><a name="19021"
      > </a
      ><a name="19022" class="Symbol"
      >&#8704;</a
      ><a name="19023"
      > </a
      ><a name="19024" class="Symbol"
      >{</a
      ><a name="19025" href="StlcProp.html#19025" class="Bound"
      >x</a
      ><a name="19026" class="Symbol"
      >}</a
      ><a name="19027"
      > </a
      ><a name="19028" class="Symbol"
      >&#8594;</a
      ><a name="19029"
      > </a
      ><a name="19030" href="StlcProp.html#19025" class="Bound"
      >x</a
      ><a name="19031"
      > </a
      ><a name="19032" href="StlcProp.html#7047" class="Datatype Operator"
      >&#8712;</a
      ><a name="19033"
      > </a
      ><a name="19034" href="StlcProp.html#18968" class="Bound"
      >V</a
      ><a name="19035"
      > </a
      ><a name="19036" class="Symbol"
      >&#8594;</a
      ><a name="19037"
      > </a
      ><a name="19038" href="Maps.html#10359" class="Function"
      >&#8709;</a
      ><a name="19039"
      > </a
      ><a name="19040" href="StlcProp.html#19025" class="Bound"
      >x</a
      ><a name="19041"
      > </a
      ><a name="19042" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="19043"
      > </a
      ><a name="19044" href="StlcProp.html#18976" class="Bound"
      >&#915;</a
      ><a name="19045"
      > </a
      ><a name="19046" href="StlcProp.html#19025" class="Bound"
      >x</a
      ><a name="19047"
      >
  </a
      ><a name="19050" href="StlcProp.html#19015" class="Function"
      >&#915;~&#915;&#8242;</a
      ><a name="19054"
      > </a
      ><a name="19055" class="Symbol"
      >{</a
      ><a name="19056" href="StlcProp.html#19056" class="Bound"
      >x</a
      ><a name="19057" class="Symbol"
      >}</a
      ><a name="19058"
      > </a
      ><a name="19059" href="StlcProp.html#19059" class="Bound"
      >x&#8712;V</a
      ><a name="19062"
      > </a
      ><a name="19063" class="Symbol"
      >=</a
      ><a name="19064"
      > </a
      ><a name="19065" href="https://agda.github.io/agda-stdlib/Data.Empty.html#348" class="Function"
      >&#8869;-elim</a
      ><a name="19071"
      > </a
      ><a name="19072" class="Symbol"
      >(</a
      ><a name="19073" href="StlcProp.html#19096" class="Function"
      >x&#8713;V</a
      ><a name="19076"
      > </a
      ><a name="19077" href="StlcProp.html#19059" class="Bound"
      >x&#8712;V</a
      ><a name="19080" class="Symbol"
      >)</a
      ><a name="19081"
      >
    </a
      ><a name="19086" class="Keyword"
      >where</a
      ><a name="19091"
      >
    </a
      ><a name="19096" href="StlcProp.html#19096" class="Function"
      >x&#8713;V</a
      ><a name="19099"
      > </a
      ><a name="19100" class="Symbol"
      >:</a
      ><a name="19101"
      > </a
      ><a name="19102" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#414" class="Function Operator"
      >&#172;</a
      ><a name="19103"
      > </a
      ><a name="19104" class="Symbol"
      >(</a
      ><a name="19105" href="StlcProp.html#19056" class="Bound"
      >x</a
      ><a name="19106"
      > </a
      ><a name="19107" href="StlcProp.html#7047" class="Datatype Operator"
      >&#8712;</a
      ><a name="19108"
      > </a
      ><a name="19109" href="StlcProp.html#18968" class="Bound"
      >V</a
      ><a name="19110" class="Symbol"
      >)</a
      ><a name="19111"
      >
    </a
      ><a name="19116" href="StlcProp.html#19096" class="Function"
      >x&#8713;V</a
      ><a name="19119"
      > </a
      ><a name="19120" class="Symbol"
      >=</a
      ><a name="19121"
      > </a
      ><a name="19122" href="StlcProp.html#10668" class="Postulate"
      >&#8709;&#8866;-closed</a
      ><a name="19131"
      > </a
      ><a name="19132" href="StlcProp.html#18979" class="Bound"
      >&#8866;V</a
      ><a name="19134"
      > </a
      ><a name="19135" class="Symbol"
      >{</a
      ><a name="19136" href="StlcProp.html#19056" class="Bound"
      >x</a
      ><a name="19137" class="Symbol"
      >}</a
      ><a name="19138"
      >

</a
      ><a name="19140" href="StlcProp.html#19140" class="Function"
      >just-injective</a
      ><a name="19154"
      > </a
      ><a name="19155" class="Symbol"
      >:</a
      ><a name="19156"
      > </a
      ><a name="19157" class="Symbol"
      >&#8704;</a
      ><a name="19158"
      > </a
      ><a name="19159" class="Symbol"
      >{</a
      ><a name="19160" href="StlcProp.html#19160" class="Bound"
      >X</a
      ><a name="19161"
      > </a
      ><a name="19162" class="Symbol"
      >:</a
      ><a name="19163"
      > </a
      ><a name="19164" class="PrimitiveType"
      >Set</a
      ><a name="19167" class="Symbol"
      >}</a
      ><a name="19168"
      > </a
      ><a name="19169" class="Symbol"
      >{</a
      ><a name="19170" href="StlcProp.html#19170" class="Bound"
      >x</a
      ><a name="19171"
      > </a
      ><a name="19172" href="StlcProp.html#19172" class="Bound"
      >y</a
      ><a name="19173"
      > </a
      ><a name="19174" class="Symbol"
      >:</a
      ><a name="19175"
      > </a
      ><a name="19176" href="StlcProp.html#19160" class="Bound"
      >X</a
      ><a name="19177" class="Symbol"
      >}</a
      ><a name="19178"
      > </a
      ><a name="19179" class="Symbol"
      >&#8594;</a
      ><a name="19180"
      > </a
      ><a name="19181" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >_&#8801;_</a
      ><a name="19184"
      > </a
      ><a name="19185" class="Symbol"
      >{</a
      ><a name="19186" class="Argument"
      >A</a
      ><a name="19187"
      > </a
      ><a name="19188" class="Symbol"
      >=</a
      ><a name="19189"
      > </a
      ><a name="19190" href="https://agda.github.io/agda-stdlib/Data.Maybe.Base.html#335" class="Datatype"
      >Maybe</a
      ><a name="19195"
      > </a
      ><a name="19196" href="StlcProp.html#19160" class="Bound"
      >X</a
      ><a name="19197" class="Symbol"
      >}</a
      ><a name="19198"
      > </a
      ><a name="19199" class="Symbol"
      >(</a
      ><a name="19200" href="https://agda.github.io/agda-stdlib/Data.Maybe.Base.html#373" class="InductiveConstructor"
      >just</a
      ><a name="19204"
      > </a
      ><a name="19205" href="StlcProp.html#19170" class="Bound"
      >x</a
      ><a name="19206" class="Symbol"
      >)</a
      ><a name="19207"
      > </a
      ><a name="19208" class="Symbol"
      >(</a
      ><a name="19209" href="https://agda.github.io/agda-stdlib/Data.Maybe.Base.html#373" class="InductiveConstructor"
      >just</a
      ><a name="19213"
      > </a
      ><a name="19214" href="StlcProp.html#19172" class="Bound"
      >y</a
      ><a name="19215" class="Symbol"
      >)</a
      ><a name="19216"
      > </a
      ><a name="19217" class="Symbol"
      >&#8594;</a
      ><a name="19218"
      > </a
      ><a name="19219" href="StlcProp.html#19170" class="Bound"
      >x</a
      ><a name="19220"
      > </a
      ><a name="19221" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="19222"
      > </a
      ><a name="19223" href="StlcProp.html#19172" class="Bound"
      >y</a
      ><a name="19224"
      >
</a
      ><a name="19225" href="StlcProp.html#19140" class="Function"
      >just-injective</a
      ><a name="19239"
      > </a
      ><a name="19240" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="19244"
      > </a
      ><a name="19245" class="Symbol"
      >=</a
      ><a name="19246"
      > </a
      ><a name="19247" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      >
{% endraw %}</pre>

<pre class="Agda">{% raw %}
<a name="19277" href="StlcProp.html#15646" class="Function"
      >preservation-[&#8758;=]</a
      ><a name="19294"
      > </a
      ><a name="19295" class="Symbol"
      >{_}</a
      ><a name="19298"
      > </a
      ><a name="19299" class="Symbol"
      >{</a
      ><a name="19300" href="StlcProp.html#19300" class="Bound"
      >x</a
      ><a name="19301" class="Symbol"
      >}</a
      ><a name="19302"
      > </a
      ><a name="19303" class="Symbol"
      >(</a
      ><a name="19304" href="Stlc.html#3452" class="InductiveConstructor"
      >Ax</a
      ><a name="19306"
      > </a
      ><a name="19307" class="Symbol"
      >{_}</a
      ><a name="19310"
      > </a
      ><a name="19311" class="Symbol"
      >{</a
      ><a name="19312" href="StlcProp.html#19312" class="Bound"
      >x&#8242;</a
      ><a name="19314" class="Symbol"
      >}</a
      ><a name="19315"
      > </a
      ><a name="19316" href="StlcProp.html#19316" class="Bound"
      >[&#915;,x&#8758;A]x&#8242;&#8801;B</a
      ><a name="19327" class="Symbol"
      >)</a
      ><a name="19328"
      > </a
      ><a name="19329" href="StlcProp.html#19329" class="Bound"
      >&#8866;V</a
      ><a name="19331"
      > </a
      ><a name="19332" class="Keyword"
      >with</a
      ><a name="19336"
      > </a
      ><a name="19337" href="StlcProp.html#19300" class="Bound"
      >x</a
      ><a name="19338"
      > </a
      ><a name="19339" href="Maps.html#2558" class="Function Operator"
      >&#8799;</a
      ><a name="19340"
      > </a
      ><a name="19341" href="StlcProp.html#19312" class="Bound"
      >x&#8242;</a
      ><a name="19343"
      >
</a
      ><a name="19344" class="Symbol"
      >...|</a
      ><a name="19348"
      > </a
      ><a name="19349" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#520" class="InductiveConstructor"
      >yes</a
      ><a name="19352"
      > </a
      ><a name="19353" href="StlcProp.html#19353" class="Bound"
      >x&#8801;x&#8242;</a
      ><a name="19357"
      > </a
      ><a name="19358" class="Keyword"
      >rewrite</a
      ><a name="19365"
      > </a
      ><a name="19366" href="StlcProp.html#19140" class="Function"
      >just-injective</a
      ><a name="19380"
      > </a
      ><a name="19381" href="StlcProp.html#19316" class="Bound"
      >[&#915;,x&#8758;A]x&#8242;&#8801;B</a
      ><a name="19392"
      >  </a
      ><a name="19394" class="Symbol"
      >=</a
      ><a name="19395"
      >  </a
      ><a name="19397" href="StlcProp.html#18903" class="Function"
      >weaken-closed</a
      ><a name="19410"
      > </a
      ><a name="19411" href="StlcProp.html#19329" class="Bound"
      >&#8866;V</a
      ><a name="19413"
      >
</a
      ><a name="19414" class="Symbol"
      >...|</a
      ><a name="19418"
      > </a
      ><a name="19419" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#547" class="InductiveConstructor"
      >no</a
      ><a name="19421"
      >  </a
      ><a name="19423" href="StlcProp.html#19423" class="Bound"
      >x&#8802;x&#8242;</a
      ><a name="19427"
      >  </a
      ><a name="19429" class="Symbol"
      >=</a
      ><a name="19430"
      >  </a
      ><a name="19432" href="Stlc.html#3452" class="InductiveConstructor"
      >Ax</a
      ><a name="19434"
      > </a
      ><a name="19435" href="StlcProp.html#19316" class="Bound"
      >[&#915;,x&#8758;A]x&#8242;&#8801;B</a
      ><a name="19446"
      >
</a
      ><a name="19447" href="StlcProp.html#15646" class="Function"
      >preservation-[&#8758;=]</a
      ><a name="19464"
      > </a
      ><a name="19465" class="Symbol"
      >{</a
      ><a name="19466" href="StlcProp.html#19466" class="Bound"
      >&#915;</a
      ><a name="19467" class="Symbol"
      >}</a
      ><a name="19468"
      > </a
      ><a name="19469" class="Symbol"
      >{</a
      ><a name="19470" href="StlcProp.html#19470" class="Bound"
      >x</a
      ><a name="19471" class="Symbol"
      >}</a
      ><a name="19472"
      > </a
      ><a name="19473" class="Symbol"
      >{</a
      ><a name="19474" href="StlcProp.html#19474" class="Bound"
      >A</a
      ><a name="19475" class="Symbol"
      >}</a
      ><a name="19476"
      > </a
      ><a name="19477" class="Symbol"
      >{</a
      ><a name="19478" href="Stlc.html#752" class="InductiveConstructor Operator"
      >&#955;[</a
      ><a name="19480"
      > </a
      ><a name="19481" href="StlcProp.html#19481" class="Bound"
      >x&#8242;</a
      ><a name="19483"
      > </a
      ><a name="19484" href="Stlc.html#752" class="InductiveConstructor Operator"
      >&#8758;</a
      ><a name="19485"
      > </a
      ><a name="19486" href="StlcProp.html#19486" class="Bound"
      >A&#8242;</a
      ><a name="19488"
      > </a
      ><a name="19489" href="Stlc.html#752" class="InductiveConstructor Operator"
      >]</a
      ><a name="19490"
      > </a
      ><a name="19491" href="StlcProp.html#19491" class="Bound"
      >N&#8242;</a
      ><a name="19493" class="Symbol"
      >}</a
      ><a name="19494"
      > </a
      ><a name="19495" class="Symbol"
      >{</a
      ><a name="19496" class="DottedPattern Symbol"
      >.</a
      ><a name="19497" href="StlcProp.html#19486" class="DottedPattern Bound"
      >A&#8242;</a
      ><a name="19499"
      > </a
      ><a name="19500" href="Stlc.html#627" class="InductiveConstructor Operator"
      >&#8658;</a
      ><a name="19501"
      > </a
      ><a name="19502" href="StlcProp.html#19502" class="Bound"
      >B&#8242;</a
      ><a name="19504" class="Symbol"
      >}</a
      ><a name="19505"
      > </a
      ><a name="19506" class="Symbol"
      >{</a
      ><a name="19507" href="StlcProp.html#19507" class="Bound"
      >V</a
      ><a name="19508" class="Symbol"
      >}</a
      ><a name="19509"
      > </a
      ><a name="19510" class="Symbol"
      >(</a
      ><a name="19511" href="Stlc.html#3508" class="InductiveConstructor"
      >&#8658;-I</a
      ><a name="19514"
      > </a
      ><a name="19515" href="StlcProp.html#19515" class="Bound"
      >&#8866;N&#8242;</a
      ><a name="19518" class="Symbol"
      >)</a
      ><a name="19519"
      > </a
      ><a name="19520" href="StlcProp.html#19520" class="Bound"
      >&#8866;V</a
      ><a name="19522"
      > </a
      ><a name="19523" class="Keyword"
      >with</a
      ><a name="19527"
      > </a
      ><a name="19528" href="StlcProp.html#19470" class="Bound"
      >x</a
      ><a name="19529"
      > </a
      ><a name="19530" href="Maps.html#2558" class="Function Operator"
      >&#8799;</a
      ><a name="19531"
      > </a
      ><a name="19532" href="StlcProp.html#19481" class="Bound"
      >x&#8242;</a
      ><a name="19534"
      >
</a
      ><a name="19535" class="Symbol"
      >...|</a
      ><a name="19539"
      > </a
      ><a name="19540" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#520" class="InductiveConstructor"
      >yes</a
      ><a name="19543"
      > </a
      ><a name="19544" href="StlcProp.html#19544" class="Bound"
      >x&#8801;x&#8242;</a
      ><a name="19548"
      > </a
      ><a name="19549" class="Keyword"
      >rewrite</a
      ><a name="19556"
      > </a
      ><a name="19557" href="StlcProp.html#19544" class="Bound"
      >x&#8801;x&#8242;</a
      ><a name="19561"
      > </a
      ><a name="19562" class="Symbol"
      >=</a
      ><a name="19563"
      > </a
      ><a name="19564" href="StlcProp.html#11369" class="Function"
      >contextLemma</a
      ><a name="19576"
      > </a
      ><a name="19577" href="StlcProp.html#19602" class="Function"
      >&#915;&#8242;~&#915;</a
      ><a name="19581"
      > </a
      ><a name="19582" class="Symbol"
      >(</a
      ><a name="19583" href="Stlc.html#3508" class="InductiveConstructor"
      >&#8658;-I</a
      ><a name="19586"
      > </a
      ><a name="19587" href="StlcProp.html#19515" class="Bound"
      >&#8866;N&#8242;</a
      ><a name="19590" class="Symbol"
      >)</a
      ><a name="19591"
      >
  </a
      ><a name="19594" class="Keyword"
      >where</a
      ><a name="19599"
      >
  </a
      ><a name="19602" href="StlcProp.html#19602" class="Function"
      >&#915;&#8242;~&#915;</a
      ><a name="19606"
      > </a
      ><a name="19607" class="Symbol"
      >:</a
      ><a name="19608"
      > </a
      ><a name="19609" class="Symbol"
      >&#8704;</a
      ><a name="19610"
      > </a
      ><a name="19611" class="Symbol"
      >{</a
      ><a name="19612" href="StlcProp.html#19612" class="Bound"
      >y</a
      ><a name="19613" class="Symbol"
      >}</a
      ><a name="19614"
      > </a
      ><a name="19615" class="Symbol"
      >&#8594;</a
      ><a name="19616"
      > </a
      ><a name="19617" href="StlcProp.html#19612" class="Bound"
      >y</a
      ><a name="19618"
      > </a
      ><a name="19619" href="StlcProp.html#7047" class="Datatype Operator"
      >&#8712;</a
      ><a name="19620"
      > </a
      ><a name="19621" class="Symbol"
      >(</a
      ><a name="19622" href="Stlc.html#752" class="InductiveConstructor Operator"
      >&#955;[</a
      ><a name="19624"
      > </a
      ><a name="19625" href="StlcProp.html#19481" class="Bound"
      >x&#8242;</a
      ><a name="19627"
      > </a
      ><a name="19628" href="Stlc.html#752" class="InductiveConstructor Operator"
      >&#8758;</a
      ><a name="19629"
      > </a
      ><a name="19630" href="StlcProp.html#19486" class="Bound"
      >A&#8242;</a
      ><a name="19632"
      > </a
      ><a name="19633" href="Stlc.html#752" class="InductiveConstructor Operator"
      >]</a
      ><a name="19634"
      > </a
      ><a name="19635" href="StlcProp.html#19491" class="Bound"
      >N&#8242;</a
      ><a name="19637" class="Symbol"
      >)</a
      ><a name="19638"
      > </a
      ><a name="19639" class="Symbol"
      >&#8594;</a
      ><a name="19640"
      > </a
      ><a name="19641" class="Symbol"
      >(</a
      ><a name="19642" href="StlcProp.html#19466" class="Bound"
      >&#915;</a
      ><a name="19643"
      > </a
      ><a name="19644" href="Maps.html#10462" class="Function Operator"
      >,</a
      ><a name="19645"
      > </a
      ><a name="19646" href="StlcProp.html#19481" class="Bound"
      >x&#8242;</a
      ><a name="19648"
      > </a
      ><a name="19649" href="Maps.html#10462" class="Function Operator"
      >&#8758;</a
      ><a name="19650"
      > </a
      ><a name="19651" href="StlcProp.html#19474" class="Bound"
      >A</a
      ><a name="19652" class="Symbol"
      >)</a
      ><a name="19653"
      > </a
      ><a name="19654" href="StlcProp.html#19612" class="Bound"
      >y</a
      ><a name="19655"
      > </a
      ><a name="19656" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="19657"
      > </a
      ><a name="19658" href="StlcProp.html#19466" class="Bound"
      >&#915;</a
      ><a name="19659"
      > </a
      ><a name="19660" href="StlcProp.html#19612" class="Bound"
      >y</a
      ><a name="19661"
      >
  </a
      ><a name="19664" href="StlcProp.html#19602" class="Function"
      >&#915;&#8242;~&#915;</a
      ><a name="19668"
      > </a
      ><a name="19669" class="Symbol"
      >{</a
      ><a name="19670" href="StlcProp.html#19670" class="Bound"
      >y</a
      ><a name="19671" class="Symbol"
      >}</a
      ><a name="19672"
      > </a
      ><a name="19673" class="Symbol"
      >(</a
      ><a name="19674" href="StlcProp.html#7111" class="InductiveConstructor"
      >free-&#955;</a
      ><a name="19680"
      > </a
      ><a name="19681" href="StlcProp.html#19681" class="Bound"
      >x&#8242;&#8802;y</a
      ><a name="19685"
      > </a
      ><a name="19686" href="StlcProp.html#19686" class="Bound"
      >y&#8712;N&#8242;</a
      ><a name="19690" class="Symbol"
      >)</a
      ><a name="19691"
      > </a
      ><a name="19692" class="Keyword"
      >with</a
      ><a name="19696"
      > </a
      ><a name="19697" href="StlcProp.html#19481" class="Bound"
      >x&#8242;</a
      ><a name="19699"
      > </a
      ><a name="19700" href="Maps.html#2558" class="Function Operator"
      >&#8799;</a
      ><a name="19701"
      > </a
      ><a name="19702" href="StlcProp.html#19670" class="Bound"
      >y</a
      ><a name="19703"
      >
  </a
      ><a name="19706" class="Symbol"
      >...|</a
      ><a name="19710"
      > </a
      ><a name="19711" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#520" class="InductiveConstructor"
      >yes</a
      ><a name="19714"
      > </a
      ><a name="19715" href="StlcProp.html#19715" class="Bound"
      >x&#8242;&#8801;y</a
      ><a name="19719"
      >  </a
      ><a name="19721" class="Symbol"
      >=</a
      ><a name="19722"
      > </a
      ><a name="19723" href="https://agda.github.io/agda-stdlib/Data.Empty.html#348" class="Function"
      >&#8869;-elim</a
      ><a name="19729"
      > </a
      ><a name="19730" class="Symbol"
      >(</a
      ><a name="19731" href="StlcProp.html#19681" class="Bound"
      >x&#8242;&#8802;y</a
      ><a name="19735"
      > </a
      ><a name="19736" href="StlcProp.html#19715" class="Bound"
      >x&#8242;&#8801;y</a
      ><a name="19740" class="Symbol"
      >)</a
      ><a name="19741"
      >
  </a
      ><a name="19744" class="Symbol"
      >...|</a
      ><a name="19748"
      > </a
      ><a name="19749" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#547" class="InductiveConstructor"
      >no</a
      ><a name="19751"
      >  </a
      ><a name="19753" class="Symbol"
      >_</a
      ><a name="19754"
      >     </a
      ><a name="19759" class="Symbol"
      >=</a
      ><a name="19760"
      > </a
      ><a name="19761" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="19765"
      >
</a
      ><a name="19766" class="Symbol"
      >...|</a
      ><a name="19770"
      > </a
      ><a name="19771" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#547" class="InductiveConstructor"
      >no</a
      ><a name="19773"
      >  </a
      ><a name="19775" href="StlcProp.html#19775" class="Bound"
      >x&#8802;x&#8242;</a
      ><a name="19779"
      > </a
      ><a name="19780" class="Symbol"
      >=</a
      ><a name="19781"
      > </a
      ><a name="19782" href="Stlc.html#3508" class="InductiveConstructor"
      >&#8658;-I</a
      ><a name="19785"
      > </a
      ><a name="19786" href="StlcProp.html#19897" class="Function"
      >&#8866;N&#8242;V</a
      ><a name="19790"
      >
  </a
      ><a name="19793" class="Keyword"
      >where</a
      ><a name="19798"
      >
  </a
      ><a name="19801" href="StlcProp.html#19801" class="Function"
      >x&#8242;x&#8866;N&#8242;</a
      ><a name="19807"
      > </a
      ><a name="19808" class="Symbol"
      >:</a
      ><a name="19809"
      > </a
      ><a name="19810" href="StlcProp.html#19466" class="Bound"
      >&#915;</a
      ><a name="19811"
      > </a
      ><a name="19812" href="Maps.html#10462" class="Function Operator"
      >,</a
      ><a name="19813"
      > </a
      ><a name="19814" href="StlcProp.html#19481" class="Bound"
      >x&#8242;</a
      ><a name="19816"
      > </a
      ><a name="19817" href="Maps.html#10462" class="Function Operator"
      >&#8758;</a
      ><a name="19818"
      > </a
      ><a name="19819" href="StlcProp.html#19486" class="Bound"
      >A&#8242;</a
      ><a name="19821"
      > </a
      ><a name="19822" href="Maps.html#10462" class="Function Operator"
      >,</a
      ><a name="19823"
      > </a
      ><a name="19824" href="StlcProp.html#19470" class="Bound"
      >x</a
      ><a name="19825"
      > </a
      ><a name="19826" href="Maps.html#10462" class="Function Operator"
      >&#8758;</a
      ><a name="19827"
      > </a
      ><a name="19828" href="StlcProp.html#19474" class="Bound"
      >A</a
      ><a name="19829"
      > </a
      ><a name="19830" href="Stlc.html#3408" class="Datatype Operator"
      >&#8866;</a
      ><a name="19831"
      > </a
      ><a name="19832" href="StlcProp.html#19491" class="Bound"
      >N&#8242;</a
      ><a name="19834"
      > </a
      ><a name="19835" href="Stlc.html#3408" class="Datatype Operator"
      >&#8758;</a
      ><a name="19836"
      > </a
      ><a name="19837" href="StlcProp.html#19502" class="Bound"
      >B&#8242;</a
      ><a name="19839"
      >
  </a
      ><a name="19842" href="StlcProp.html#19801" class="Function"
      >x&#8242;x&#8866;N&#8242;</a
      ><a name="19848"
      > </a
      ><a name="19849" class="Keyword"
      >rewrite</a
      ><a name="19856"
      > </a
      ><a name="19857" href="Maps.html#11585" class="Function"
      >update-permute</a
      ><a name="19871"
      > </a
      ><a name="19872" href="StlcProp.html#19466" class="Bound"
      >&#915;</a
      ><a name="19873"
      > </a
      ><a name="19874" href="StlcProp.html#19470" class="Bound"
      >x</a
      ><a name="19875"
      > </a
      ><a name="19876" href="StlcProp.html#19474" class="Bound"
      >A</a
      ><a name="19877"
      > </a
      ><a name="19878" href="StlcProp.html#19481" class="Bound"
      >x&#8242;</a
      ><a name="19880"
      > </a
      ><a name="19881" href="StlcProp.html#19486" class="Bound"
      >A&#8242;</a
      ><a name="19883"
      > </a
      ><a name="19884" href="StlcProp.html#19775" class="Bound"
      >x&#8802;x&#8242;</a
      ><a name="19888"
      > </a
      ><a name="19889" class="Symbol"
      >=</a
      ><a name="19890"
      > </a
      ><a name="19891" href="StlcProp.html#19515" class="Bound"
      >&#8866;N&#8242;</a
      ><a name="19894"
      >
  </a
      ><a name="19897" href="StlcProp.html#19897" class="Function"
      >&#8866;N&#8242;V</a
      ><a name="19901"
      > </a
      ><a name="19902" class="Symbol"
      >:</a
      ><a name="19903"
      > </a
      ><a name="19904" class="Symbol"
      >(</a
      ><a name="19905" href="StlcProp.html#19466" class="Bound"
      >&#915;</a
      ><a name="19906"
      > </a
      ><a name="19907" href="Maps.html#10462" class="Function Operator"
      >,</a
      ><a name="19908"
      > </a
      ><a name="19909" href="StlcProp.html#19481" class="Bound"
      >x&#8242;</a
      ><a name="19911"
      > </a
      ><a name="19912" href="Maps.html#10462" class="Function Operator"
      >&#8758;</a
      ><a name="19913"
      > </a
      ><a name="19914" href="StlcProp.html#19486" class="Bound"
      >A&#8242;</a
      ><a name="19916" class="Symbol"
      >)</a
      ><a name="19917"
      > </a
      ><a name="19918" href="Stlc.html#3408" class="Datatype Operator"
      >&#8866;</a
      ><a name="19919"
      > </a
      ><a name="19920" href="StlcProp.html#19491" class="Bound"
      >N&#8242;</a
      ><a name="19922"
      > </a
      ><a name="19923" href="Stlc.html#1297" class="Function Operator"
      >[</a
      ><a name="19924"
      > </a
      ><a name="19925" href="StlcProp.html#19470" class="Bound"
      >x</a
      ><a name="19926"
      > </a
      ><a name="19927" href="Stlc.html#1297" class="Function Operator"
      >&#8758;=</a
      ><a name="19929"
      > </a
      ><a name="19930" href="StlcProp.html#19507" class="Bound"
      >V</a
      ><a name="19931"
      > </a
      ><a name="19932" href="Stlc.html#1297" class="Function Operator"
      >]</a
      ><a name="19933"
      > </a
      ><a name="19934" href="Stlc.html#3408" class="Datatype Operator"
      >&#8758;</a
      ><a name="19935"
      > </a
      ><a name="19936" href="StlcProp.html#19502" class="Bound"
      >B&#8242;</a
      ><a name="19938"
      >
  </a
      ><a name="19941" href="StlcProp.html#19897" class="Function"
      >&#8866;N&#8242;V</a
      ><a name="19945"
      > </a
      ><a name="19946" class="Symbol"
      >=</a
      ><a name="19947"
      > </a
      ><a name="19948" href="StlcProp.html#15646" class="Function"
      >preservation-[&#8758;=]</a
      ><a name="19965"
      > </a
      ><a name="19966" href="StlcProp.html#19801" class="Function"
      >x&#8242;x&#8866;N&#8242;</a
      ><a name="19972"
      > </a
      ><a name="19973" href="StlcProp.html#19520" class="Bound"
      >&#8866;V</a
      ><a name="19975"
      >
</a
      ><a name="19976" href="StlcProp.html#15646" class="Function"
      >preservation-[&#8758;=]</a
      ><a name="19993"
      > </a
      ><a name="19994" class="Symbol"
      >(</a
      ><a name="19995" href="Stlc.html#3585" class="InductiveConstructor"
      >&#8658;-E</a
      ><a name="19998"
      > </a
      ><a name="19999" href="StlcProp.html#19999" class="Bound"
      >&#8866;L</a
      ><a name="20001"
      > </a
      ><a name="20002" href="StlcProp.html#20002" class="Bound"
      >&#8866;M</a
      ><a name="20004" class="Symbol"
      >)</a
      ><a name="20005"
      > </a
      ><a name="20006" href="StlcProp.html#20006" class="Bound"
      >&#8866;V</a
      ><a name="20008"
      > </a
      ><a name="20009" class="Symbol"
      >=</a
      ><a name="20010"
      > </a
      ><a name="20011" href="Stlc.html#3585" class="InductiveConstructor"
      >&#8658;-E</a
      ><a name="20014"
      > </a
      ><a name="20015" class="Symbol"
      >(</a
      ><a name="20016" href="StlcProp.html#15646" class="Function"
      >preservation-[&#8758;=]</a
      ><a name="20033"
      > </a
      ><a name="20034" href="StlcProp.html#19999" class="Bound"
      >&#8866;L</a
      ><a name="20036"
      > </a
      ><a name="20037" href="StlcProp.html#20006" class="Bound"
      >&#8866;V</a
      ><a name="20039" class="Symbol"
      >)</a
      ><a name="20040"
      > </a
      ><a name="20041" class="Symbol"
      >(</a
      ><a name="20042" href="StlcProp.html#15646" class="Function"
      >preservation-[&#8758;=]</a
      ><a name="20059"
      > </a
      ><a name="20060" href="StlcProp.html#20002" class="Bound"
      >&#8866;M</a
      ><a name="20062"
      > </a
      ><a name="20063" href="StlcProp.html#20006" class="Bound"
      >&#8866;V</a
      ><a name="20065" class="Symbol"
      >)</a
      ><a name="20066"
      >
</a
      ><a name="20067" href="StlcProp.html#15646" class="Function"
      >preservation-[&#8758;=]</a
      ><a name="20084"
      > </a
      ><a name="20085" href="Stlc.html#3663" class="InductiveConstructor"
      >&#120121;-I&#8321;</a
      ><a name="20089"
      > </a
      ><a name="20090" href="StlcProp.html#20090" class="Bound"
      >&#8866;V</a
      ><a name="20092"
      > </a
      ><a name="20093" class="Symbol"
      >=</a
      ><a name="20094"
      > </a
      ><a name="20095" href="Stlc.html#3663" class="InductiveConstructor"
      >&#120121;-I&#8321;</a
      ><a name="20099"
      >
</a
      ><a name="20100" href="StlcProp.html#15646" class="Function"
      >preservation-[&#8758;=]</a
      ><a name="20117"
      > </a
      ><a name="20118" href="Stlc.html#3697" class="InductiveConstructor"
      >&#120121;-I&#8322;</a
      ><a name="20122"
      > </a
      ><a name="20123" href="StlcProp.html#20123" class="Bound"
      >&#8866;V</a
      ><a name="20125"
      > </a
      ><a name="20126" class="Symbol"
      >=</a
      ><a name="20127"
      > </a
      ><a name="20128" href="Stlc.html#3697" class="InductiveConstructor"
      >&#120121;-I&#8322;</a
      ><a name="20132"
      >
</a
      ><a name="20133" href="StlcProp.html#15646" class="Function"
      >preservation-[&#8758;=]</a
      ><a name="20150"
      > </a
      ><a name="20151" class="Symbol"
      >(</a
      ><a name="20152" href="Stlc.html#3732" class="InductiveConstructor"
      >&#120121;-E</a
      ><a name="20155"
      > </a
      ><a name="20156" href="StlcProp.html#20156" class="Bound"
      >&#8866;L</a
      ><a name="20158"
      > </a
      ><a name="20159" href="StlcProp.html#20159" class="Bound"
      >&#8866;M</a
      ><a name="20161"
      > </a
      ><a name="20162" href="StlcProp.html#20162" class="Bound"
      >&#8866;N</a
      ><a name="20164" class="Symbol"
      >)</a
      ><a name="20165"
      > </a
      ><a name="20166" href="StlcProp.html#20166" class="Bound"
      >&#8866;V</a
      ><a name="20168"
      > </a
      ><a name="20169" class="Symbol"
      >=</a
      ><a name="20170"
      >
  </a
      ><a name="20173" href="Stlc.html#3732" class="InductiveConstructor"
      >&#120121;-E</a
      ><a name="20176"
      > </a
      ><a name="20177" class="Symbol"
      >(</a
      ><a name="20178" href="StlcProp.html#15646" class="Function"
      >preservation-[&#8758;=]</a
      ><a name="20195"
      > </a
      ><a name="20196" href="StlcProp.html#20156" class="Bound"
      >&#8866;L</a
      ><a name="20198"
      > </a
      ><a name="20199" href="StlcProp.html#20166" class="Bound"
      >&#8866;V</a
      ><a name="20201" class="Symbol"
      >)</a
      ><a name="20202"
      > </a
      ><a name="20203" class="Symbol"
      >(</a
      ><a name="20204" href="StlcProp.html#15646" class="Function"
      >preservation-[&#8758;=]</a
      ><a name="20221"
      > </a
      ><a name="20222" href="StlcProp.html#20159" class="Bound"
      >&#8866;M</a
      ><a name="20224"
      > </a
      ><a name="20225" href="StlcProp.html#20166" class="Bound"
      >&#8866;V</a
      ><a name="20227" class="Symbol"
      >)</a
      ><a name="20228"
      > </a
      ><a name="20229" class="Symbol"
      >(</a
      ><a name="20230" href="StlcProp.html#15646" class="Function"
      >preservation-[&#8758;=]</a
      ><a name="20247"
      > </a
      ><a name="20248" href="StlcProp.html#20162" class="Bound"
      >&#8866;N</a
      ><a name="20250"
      > </a
      ><a name="20251" href="StlcProp.html#20166" class="Bound"
      >&#8866;V</a
      ><a name="20253" class="Symbol"
      >)</a
      >
{% endraw %}</pre>


### Main Theorem

We now have the tools we need to prove preservation: if a closed
term `M` has type `A` and takes a step to `N`, then `N`
is also a closed term with type `A`.  In other words, small-step
reduction preserves types.

<pre class="Agda">{% raw %}
<a name="20513" href="StlcProp.html#20513" class="Function"
      >preservation</a
      ><a name="20525"
      > </a
      ><a name="20526" class="Symbol"
      >:</a
      ><a name="20527"
      > </a
      ><a name="20528" class="Symbol"
      >&#8704;</a
      ><a name="20529"
      > </a
      ><a name="20530" class="Symbol"
      >{</a
      ><a name="20531" href="StlcProp.html#20531" class="Bound"
      >M</a
      ><a name="20532"
      > </a
      ><a name="20533" href="StlcProp.html#20533" class="Bound"
      >N</a
      ><a name="20534"
      > </a
      ><a name="20535" href="StlcProp.html#20535" class="Bound"
      >A</a
      ><a name="20536" class="Symbol"
      >}</a
      ><a name="20537"
      > </a
      ><a name="20538" class="Symbol"
      >&#8594;</a
      ><a name="20539"
      > </a
      ><a name="20540" href="Maps.html#10359" class="Function"
      >&#8709;</a
      ><a name="20541"
      > </a
      ><a name="20542" href="Stlc.html#3408" class="Datatype Operator"
      >&#8866;</a
      ><a name="20543"
      > </a
      ><a name="20544" href="StlcProp.html#20531" class="Bound"
      >M</a
      ><a name="20545"
      > </a
      ><a name="20546" href="Stlc.html#3408" class="Datatype Operator"
      >&#8758;</a
      ><a name="20547"
      > </a
      ><a name="20548" href="StlcProp.html#20535" class="Bound"
      >A</a
      ><a name="20549"
      > </a
      ><a name="20550" class="Symbol"
      >&#8594;</a
      ><a name="20551"
      > </a
      ><a name="20552" href="StlcProp.html#20531" class="Bound"
      >M</a
      ><a name="20553"
      > </a
      ><a name="20554" href="Stlc.html#1787" class="Datatype Operator"
      >&#10233;</a
      ><a name="20555"
      > </a
      ><a name="20556" href="StlcProp.html#20533" class="Bound"
      >N</a
      ><a name="20557"
      > </a
      ><a name="20558" class="Symbol"
      >&#8594;</a
      ><a name="20559"
      > </a
      ><a name="20560" href="Maps.html#10359" class="Function"
      >&#8709;</a
      ><a name="20561"
      > </a
      ><a name="20562" href="Stlc.html#3408" class="Datatype Operator"
      >&#8866;</a
      ><a name="20563"
      > </a
      ><a name="20564" href="StlcProp.html#20533" class="Bound"
      >N</a
      ><a name="20565"
      > </a
      ><a name="20566" href="Stlc.html#3408" class="Datatype Operator"
      >&#8758;</a
      ><a name="20567"
      > </a
      ><a name="20568" href="StlcProp.html#20535" class="Bound"
      >A</a
      >
{% endraw %}</pre>

_Proof_: By induction on the derivation of `\vdash t : T`.

- We can immediately rule out `var`, `abs`, `T_True`, and
  `T_False` as the final rules in the derivation, since in each of
  these cases `t` cannot take a step.

- If the last rule in the derivation was `app`, then `t = t_1
  t_2`.  There are three cases to consider, one for each rule that
  could have been used to show that `t_1 t_2` takes a step to `t'`.

    - If `t_1 t_2` takes a step by `Sapp1`, with `t_1` stepping to
      `t_1'`, then by the IH `t_1'` has the same type as `t_1`, and
      hence `t_1' t_2` has the same type as `t_1 t_2`.

    - The `Sapp2` case is similar.

    - If `t_1 t_2` takes a step by `Sred`, then `t_1 =
      \lambda x:t_{11}.t_{12}` and `t_1 t_2` steps to ``x∶=t_2`t_{12}`; the
      desired result now follows from the fact that substitution
      preserves types.

    - If the last rule in the derivation was `if`, then `t = if t_1
      then t_2 else t_3`, and there are again three cases depending on
      how `t` steps.

    - If `t` steps to `t_2` or `t_3`, the result is immediate, since
      `t_2` and `t_3` have the same type as `t`.

    - Otherwise, `t` steps by `Sif`, and the desired conclusion
      follows directly from the induction hypothesis.

<pre class="Agda">{% raw %}
<a name="21863" href="StlcProp.html#20513" class="Function"
      >preservation</a
      ><a name="21875"
      > </a
      ><a name="21876" class="Symbol"
      >(</a
      ><a name="21877" href="Stlc.html#3452" class="InductiveConstructor"
      >Ax</a
      ><a name="21879"
      > </a
      ><a name="21880" href="StlcProp.html#21880" class="Bound"
      >x&#8321;</a
      ><a name="21882" class="Symbol"
      >)</a
      ><a name="21883"
      > </a
      ><a name="21884" class="Symbol"
      >()</a
      ><a name="21886"
      >
</a
      ><a name="21887" href="StlcProp.html#20513" class="Function"
      >preservation</a
      ><a name="21899"
      > </a
      ><a name="21900" class="Symbol"
      >(</a
      ><a name="21901" href="Stlc.html#3508" class="InductiveConstructor"
      >&#8658;-I</a
      ><a name="21904"
      > </a
      ><a name="21905" href="StlcProp.html#21905" class="Bound"
      >&#8866;N</a
      ><a name="21907" class="Symbol"
      >)</a
      ><a name="21908"
      > </a
      ><a name="21909" class="Symbol"
      >()</a
      ><a name="21911"
      >
</a
      ><a name="21912" href="StlcProp.html#20513" class="Function"
      >preservation</a
      ><a name="21924"
      > </a
      ><a name="21925" class="Symbol"
      >(</a
      ><a name="21926" href="Stlc.html#3585" class="InductiveConstructor"
      >&#8658;-E</a
      ><a name="21929"
      > </a
      ><a name="21930" class="Symbol"
      >(</a
      ><a name="21931" href="Stlc.html#3508" class="InductiveConstructor"
      >&#8658;-I</a
      ><a name="21934"
      > </a
      ><a name="21935" href="StlcProp.html#21935" class="Bound"
      >&#8866;N</a
      ><a name="21937" class="Symbol"
      >)</a
      ><a name="21938"
      > </a
      ><a name="21939" href="StlcProp.html#21939" class="Bound"
      >&#8866;V</a
      ><a name="21941" class="Symbol"
      >)</a
      ><a name="21942"
      > </a
      ><a name="21943" class="Symbol"
      >(</a
      ><a name="21944" href="Stlc.html#1819" class="InductiveConstructor"
      >&#946;&#8658;</a
      ><a name="21946"
      > </a
      ><a name="21947" href="StlcProp.html#21947" class="Bound"
      >valueV</a
      ><a name="21953" class="Symbol"
      >)</a
      ><a name="21954"
      > </a
      ><a name="21955" class="Symbol"
      >=</a
      ><a name="21956"
      > </a
      ><a name="21957" href="StlcProp.html#15646" class="Function"
      >preservation-[&#8758;=]</a
      ><a name="21974"
      > </a
      ><a name="21975" href="StlcProp.html#21935" class="Bound"
      >&#8866;N</a
      ><a name="21977"
      > </a
      ><a name="21978" href="StlcProp.html#21939" class="Bound"
      >&#8866;V</a
      ><a name="21980"
      >
</a
      ><a name="21981" href="StlcProp.html#20513" class="Function"
      >preservation</a
      ><a name="21993"
      > </a
      ><a name="21994" class="Symbol"
      >(</a
      ><a name="21995" href="Stlc.html#3585" class="InductiveConstructor"
      >&#8658;-E</a
      ><a name="21998"
      > </a
      ><a name="21999" href="StlcProp.html#21999" class="Bound"
      >&#8866;L</a
      ><a name="22001"
      > </a
      ><a name="22002" href="StlcProp.html#22002" class="Bound"
      >&#8866;M</a
      ><a name="22004" class="Symbol"
      >)</a
      ><a name="22005"
      > </a
      ><a name="22006" class="Symbol"
      >(</a
      ><a name="22007" href="Stlc.html#1888" class="InductiveConstructor"
      >&#947;&#8658;&#8321;</a
      ><a name="22010"
      > </a
      ><a name="22011" href="StlcProp.html#22011" class="Bound"
      >L&#10233;L&#8242;</a
      ><a name="22015" class="Symbol"
      >)</a
      ><a name="22016"
      > </a
      ><a name="22017" class="Keyword"
      >with</a
      ><a name="22021"
      > </a
      ><a name="22022" href="StlcProp.html#20513" class="Function"
      >preservation</a
      ><a name="22034"
      > </a
      ><a name="22035" href="StlcProp.html#21999" class="Bound"
      >&#8866;L</a
      ><a name="22037"
      > </a
      ><a name="22038" href="StlcProp.html#22011" class="Bound"
      >L&#10233;L&#8242;</a
      ><a name="22042"
      >
</a
      ><a name="22043" class="Symbol"
      >...|</a
      ><a name="22047"
      > </a
      ><a name="22048" href="StlcProp.html#22048" class="Bound"
      >&#8866;L&#8242;</a
      ><a name="22051"
      > </a
      ><a name="22052" class="Symbol"
      >=</a
      ><a name="22053"
      > </a
      ><a name="22054" href="Stlc.html#3585" class="InductiveConstructor"
      >&#8658;-E</a
      ><a name="22057"
      > </a
      ><a name="22058" href="StlcProp.html#22048" class="Bound"
      >&#8866;L&#8242;</a
      ><a name="22061"
      > </a
      ><a name="22062" href="StlcProp.html#22002" class="Bound"
      >&#8866;M</a
      ><a name="22064"
      >
</a
      ><a name="22065" href="StlcProp.html#20513" class="Function"
      >preservation</a
      ><a name="22077"
      > </a
      ><a name="22078" class="Symbol"
      >(</a
      ><a name="22079" href="Stlc.html#3585" class="InductiveConstructor"
      >&#8658;-E</a
      ><a name="22082"
      > </a
      ><a name="22083" href="StlcProp.html#22083" class="Bound"
      >&#8866;L</a
      ><a name="22085"
      > </a
      ><a name="22086" href="StlcProp.html#22086" class="Bound"
      >&#8866;M</a
      ><a name="22088" class="Symbol"
      >)</a
      ><a name="22089"
      > </a
      ><a name="22090" class="Symbol"
      >(</a
      ><a name="22091" href="Stlc.html#1941" class="InductiveConstructor"
      >&#947;&#8658;&#8322;</a
      ><a name="22094"
      > </a
      ><a name="22095" href="StlcProp.html#22095" class="Bound"
      >valueL</a
      ><a name="22101"
      > </a
      ><a name="22102" href="StlcProp.html#22102" class="Bound"
      >M&#10233;M&#8242;</a
      ><a name="22106" class="Symbol"
      >)</a
      ><a name="22107"
      > </a
      ><a name="22108" class="Keyword"
      >with</a
      ><a name="22112"
      > </a
      ><a name="22113" href="StlcProp.html#20513" class="Function"
      >preservation</a
      ><a name="22125"
      > </a
      ><a name="22126" href="StlcProp.html#22086" class="Bound"
      >&#8866;M</a
      ><a name="22128"
      > </a
      ><a name="22129" href="StlcProp.html#22102" class="Bound"
      >M&#10233;M&#8242;</a
      ><a name="22133"
      >
</a
      ><a name="22134" class="Symbol"
      >...|</a
      ><a name="22138"
      > </a
      ><a name="22139" href="StlcProp.html#22139" class="Bound"
      >&#8866;M&#8242;</a
      ><a name="22142"
      > </a
      ><a name="22143" class="Symbol"
      >=</a
      ><a name="22144"
      > </a
      ><a name="22145" href="Stlc.html#3585" class="InductiveConstructor"
      >&#8658;-E</a
      ><a name="22148"
      > </a
      ><a name="22149" href="StlcProp.html#22083" class="Bound"
      >&#8866;L</a
      ><a name="22151"
      > </a
      ><a name="22152" href="StlcProp.html#22139" class="Bound"
      >&#8866;M&#8242;</a
      ><a name="22155"
      >
</a
      ><a name="22156" href="StlcProp.html#20513" class="Function"
      >preservation</a
      ><a name="22168"
      > </a
      ><a name="22169" href="Stlc.html#3663" class="InductiveConstructor"
      >&#120121;-I&#8321;</a
      ><a name="22173"
      > </a
      ><a name="22174" class="Symbol"
      >()</a
      ><a name="22176"
      >
</a
      ><a name="22177" href="StlcProp.html#20513" class="Function"
      >preservation</a
      ><a name="22189"
      > </a
      ><a name="22190" href="Stlc.html#3697" class="InductiveConstructor"
      >&#120121;-I&#8322;</a
      ><a name="22194"
      > </a
      ><a name="22195" class="Symbol"
      >()</a
      ><a name="22197"
      >
</a
      ><a name="22198" href="StlcProp.html#20513" class="Function"
      >preservation</a
      ><a name="22210"
      > </a
      ><a name="22211" class="Symbol"
      >(</a
      ><a name="22212" href="Stlc.html#3732" class="InductiveConstructor"
      >&#120121;-E</a
      ><a name="22215"
      > </a
      ><a name="22216" href="Stlc.html#3663" class="InductiveConstructor"
      >&#120121;-I&#8321;</a
      ><a name="22220"
      > </a
      ><a name="22221" href="StlcProp.html#22221" class="Bound"
      >&#8866;M</a
      ><a name="22223"
      > </a
      ><a name="22224" href="StlcProp.html#22224" class="Bound"
      >&#8866;N</a
      ><a name="22226" class="Symbol"
      >)</a
      ><a name="22227"
      > </a
      ><a name="22228" href="Stlc.html#2008" class="InductiveConstructor"
      >&#946;&#120121;&#8321;</a
      ><a name="22231"
      > </a
      ><a name="22232" class="Symbol"
      >=</a
      ><a name="22233"
      > </a
      ><a name="22234" href="StlcProp.html#22221" class="Bound"
      >&#8866;M</a
      ><a name="22236"
      >
</a
      ><a name="22237" href="StlcProp.html#20513" class="Function"
      >preservation</a
      ><a name="22249"
      > </a
      ><a name="22250" class="Symbol"
      >(</a
      ><a name="22251" href="Stlc.html#3732" class="InductiveConstructor"
      >&#120121;-E</a
      ><a name="22254"
      > </a
      ><a name="22255" href="Stlc.html#3697" class="InductiveConstructor"
      >&#120121;-I&#8322;</a
      ><a name="22259"
      > </a
      ><a name="22260" href="StlcProp.html#22260" class="Bound"
      >&#8866;M</a
      ><a name="22262"
      > </a
      ><a name="22263" href="StlcProp.html#22263" class="Bound"
      >&#8866;N</a
      ><a name="22265" class="Symbol"
      >)</a
      ><a name="22266"
      > </a
      ><a name="22267" href="Stlc.html#2056" class="InductiveConstructor"
      >&#946;&#120121;&#8322;</a
      ><a name="22270"
      > </a
      ><a name="22271" class="Symbol"
      >=</a
      ><a name="22272"
      > </a
      ><a name="22273" href="StlcProp.html#22263" class="Bound"
      >&#8866;N</a
      ><a name="22275"
      >
</a
      ><a name="22276" href="StlcProp.html#20513" class="Function"
      >preservation</a
      ><a name="22288"
      > </a
      ><a name="22289" class="Symbol"
      >(</a
      ><a name="22290" href="Stlc.html#3732" class="InductiveConstructor"
      >&#120121;-E</a
      ><a name="22293"
      > </a
      ><a name="22294" href="StlcProp.html#22294" class="Bound"
      >&#8866;L</a
      ><a name="22296"
      > </a
      ><a name="22297" href="StlcProp.html#22297" class="Bound"
      >&#8866;M</a
      ><a name="22299"
      > </a
      ><a name="22300" href="StlcProp.html#22300" class="Bound"
      >&#8866;N</a
      ><a name="22302" class="Symbol"
      >)</a
      ><a name="22303"
      > </a
      ><a name="22304" class="Symbol"
      >(</a
      ><a name="22305" href="Stlc.html#2105" class="InductiveConstructor"
      >&#947;&#120121;</a
      ><a name="22307"
      > </a
      ><a name="22308" href="StlcProp.html#22308" class="Bound"
      >L&#10233;L&#8242;</a
      ><a name="22312" class="Symbol"
      >)</a
      ><a name="22313"
      > </a
      ><a name="22314" class="Keyword"
      >with</a
      ><a name="22318"
      > </a
      ><a name="22319" href="StlcProp.html#20513" class="Function"
      >preservation</a
      ><a name="22331"
      > </a
      ><a name="22332" href="StlcProp.html#22294" class="Bound"
      >&#8866;L</a
      ><a name="22334"
      > </a
      ><a name="22335" href="StlcProp.html#22308" class="Bound"
      >L&#10233;L&#8242;</a
      ><a name="22339"
      >
</a
      ><a name="22340" class="Symbol"
      >...|</a
      ><a name="22344"
      > </a
      ><a name="22345" href="StlcProp.html#22345" class="Bound"
      >&#8866;L&#8242;</a
      ><a name="22348"
      > </a
      ><a name="22349" class="Symbol"
      >=</a
      ><a name="22350"
      > </a
      ><a name="22351" href="Stlc.html#3732" class="InductiveConstructor"
      >&#120121;-E</a
      ><a name="22354"
      > </a
      ><a name="22355" href="StlcProp.html#22345" class="Bound"
      >&#8866;L&#8242;</a
      ><a name="22358"
      > </a
      ><a name="22359" href="StlcProp.html#22297" class="Bound"
      >&#8866;M</a
      ><a name="22361"
      > </a
      ><a name="22362" href="StlcProp.html#22300" class="Bound"
      >&#8866;N</a
      >
{% endraw %}</pre>

Proof with eauto.
  remember (@empty ty) as Gamma.
  intros t t' T HT. generalize dependent t'.
  induction HT;
       intros t' HE; subst Gamma; subst;
       try solve `inversion HE; subst; auto`.
  - (* app
    inversion HE; subst...
    (* Most of the cases are immediate by induction,
       and `eauto` takes care of them
    + (* Sred
      apply substitution_preserves_typing with t_{11}...
      inversion HT_1...
Qed.

#### Exercise: 2 stars, recommended (subject_expansion_stlc)
An exercise in the [Stlc]({{ "Stlc" | relative_url }}) chapter asked about the
subject expansion property for the simple language of arithmetic and boolean
expressions.  Does this property hold for STLC?  That is, is it always the case
that, if `t ==> t'` and `has_type t' T`, then `empty \vdash t : T`?  If
so, prove it.  If not, give a counter-example not involving conditionals. 


## Type Soundness

#### Exercise: 2 stars, optional (type_soundness)
Put progress and preservation together and show that a well-typed
term can _never_ reach a stuck state.

Definition stuck (t:tm) : Prop :=
  (normal_form step) t /\ ~ Value t.

Corollary soundness : forall t t' T,
  empty \vdash t : T →
  t ==>* t' →
  ~(stuck t').
Proof.
  intros t t' T Hhas_type Hmulti. unfold stuck.
  intros `Hnf Hnot_val`. unfold normal_form in Hnf.
  induction Hmulti.


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

