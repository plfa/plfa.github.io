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
      ><a name="1446" class="Symbol"
      >())</a
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
terms are not stuck: either a well-typed term can take a reduction
step or it is a value.

<pre class="Agda">{% raw %}
<a name="1881" class="Keyword"
      >data</a
      ><a name="1885"
      > </a
      ><a name="1886" href="StlcProp.html#1886" class="Datatype"
      >Progress</a
      ><a name="1894"
      > </a
      ><a name="1895" class="Symbol"
      >:</a
      ><a name="1896"
      > </a
      ><a name="1897" href="Stlc.html#715" class="Datatype"
      >Term</a
      ><a name="1901"
      > </a
      ><a name="1902" class="Symbol"
      >&#8594;</a
      ><a name="1903"
      > </a
      ><a name="1904" class="PrimitiveType"
      >Set</a
      ><a name="1907"
      > </a
      ><a name="1908" class="Keyword"
      >where</a
      ><a name="1913"
      >
  </a
      ><a name="1916" href="StlcProp.html#1916" class="InductiveConstructor"
      >steps</a
      ><a name="1921"
      > </a
      ><a name="1922" class="Symbol"
      >:</a
      ><a name="1923"
      > </a
      ><a name="1924" class="Symbol"
      >&#8704;</a
      ><a name="1925"
      > </a
      ><a name="1926" class="Symbol"
      >{</a
      ><a name="1927" href="StlcProp.html#1927" class="Bound"
      >M</a
      ><a name="1928"
      > </a
      ><a name="1929" href="StlcProp.html#1929" class="Bound"
      >N</a
      ><a name="1930" class="Symbol"
      >}</a
      ><a name="1931"
      > </a
      ><a name="1932" class="Symbol"
      >&#8594;</a
      ><a name="1933"
      > </a
      ><a name="1934" href="StlcProp.html#1927" class="Bound"
      >M</a
      ><a name="1935"
      > </a
      ><a name="1936" href="Stlc.html#1787" class="Datatype Operator"
      >&#10233;</a
      ><a name="1937"
      > </a
      ><a name="1938" href="StlcProp.html#1929" class="Bound"
      >N</a
      ><a name="1939"
      > </a
      ><a name="1940" class="Symbol"
      >&#8594;</a
      ><a name="1941"
      > </a
      ><a name="1942" href="StlcProp.html#1886" class="Datatype"
      >Progress</a
      ><a name="1950"
      > </a
      ><a name="1951" href="StlcProp.html#1927" class="Bound"
      >M</a
      ><a name="1952"
      >
  </a
      ><a name="1955" href="StlcProp.html#1955" class="InductiveConstructor"
      >done</a
      ><a name="1959"
      >  </a
      ><a name="1961" class="Symbol"
      >:</a
      ><a name="1962"
      > </a
      ><a name="1963" class="Symbol"
      >&#8704;</a
      ><a name="1964"
      > </a
      ><a name="1965" class="Symbol"
      >{</a
      ><a name="1966" href="StlcProp.html#1966" class="Bound"
      >M</a
      ><a name="1967" class="Symbol"
      >}</a
      ><a name="1968"
      > </a
      ><a name="1969" class="Symbol"
      >&#8594;</a
      ><a name="1970"
      > </a
      ><a name="1971" href="Stlc.html#1126" class="Datatype"
      >Value</a
      ><a name="1976"
      > </a
      ><a name="1977" href="StlcProp.html#1966" class="Bound"
      >M</a
      ><a name="1978"
      > </a
      ><a name="1979" class="Symbol"
      >&#8594;</a
      ><a name="1980"
      > </a
      ><a name="1981" href="StlcProp.html#1886" class="Datatype"
      >Progress</a
      ><a name="1989"
      > </a
      ><a name="1990" href="StlcProp.html#1966" class="Bound"
      >M</a
      ><a name="1991"
      >

</a
      ><a name="1993" href="StlcProp.html#1993" class="Function"
      >progress</a
      ><a name="2001"
      > </a
      ><a name="2002" class="Symbol"
      >:</a
      ><a name="2003"
      > </a
      ><a name="2004" class="Symbol"
      >&#8704;</a
      ><a name="2005"
      > </a
      ><a name="2006" class="Symbol"
      >{</a
      ><a name="2007" href="StlcProp.html#2007" class="Bound"
      >M</a
      ><a name="2008"
      > </a
      ><a name="2009" href="StlcProp.html#2009" class="Bound"
      >A</a
      ><a name="2010" class="Symbol"
      >}</a
      ><a name="2011"
      > </a
      ><a name="2012" class="Symbol"
      >&#8594;</a
      ><a name="2013"
      > </a
      ><a name="2014" href="Maps.html#10359" class="Function"
      >&#8709;</a
      ><a name="2015"
      > </a
      ><a name="2016" href="Stlc.html#3408" class="Datatype Operator"
      >&#8866;</a
      ><a name="2017"
      > </a
      ><a name="2018" href="StlcProp.html#2007" class="Bound"
      >M</a
      ><a name="2019"
      > </a
      ><a name="2020" href="Stlc.html#3408" class="Datatype Operator"
      >&#8758;</a
      ><a name="2021"
      > </a
      ><a name="2022" href="StlcProp.html#2009" class="Bound"
      >A</a
      ><a name="2023"
      > </a
      ><a name="2024" class="Symbol"
      >&#8594;</a
      ><a name="2025"
      > </a
      ><a name="2026" href="StlcProp.html#1886" class="Datatype"
      >Progress</a
      ><a name="2034"
      > </a
      ><a name="2035" href="StlcProp.html#2007" class="Bound"
      >M</a
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
    hypotheses.  By the first induction hypothesis, either `L`
    can take a step or is a value.

    - If `L` can take a step, then so can `L · M` by `γ⇒₁`.

    - If `L` is a value then consider `M`. By the second induction
      hypothesis, either `M` can take a step or is a value.

      - If `M` can take a step, then so can `L · M` by `γ⇒₂`.

      - If `M` is a value, then since `L` is a value with a
        function type we know from the canonical forms lemma
        that it must be a lambda abstraction,
        and hence `L · M` can take a step by `β⇒`.

  - If the last rule of the derivation is `𝔹-E`, then the term has
    the form `if L then M else N` where `L` has type `𝔹`.
    By the induction hypothesis, either `L` can take a step or is
    a value.

    - If `L` can take a step, then so can `if L then M else N` by `γ𝔹`.

    - If `L` is a value, then since it has type boolean we know from
      the canonical forms lemma that it must be either `true` or
      `false`.

      - If `L` is `true`, then `if L then M else N` steps by `β𝔹₁`

      - If `L` is `false`, then `if L then M else N` steps by `β𝔹₂`

This completes the proof.

<pre class="Agda">{% raw %}
<a name="3902" href="StlcProp.html#1993" class="Function"
      >progress</a
      ><a name="3910"
      > </a
      ><a name="3911" class="Symbol"
      >(</a
      ><a name="3912" href="Stlc.html#3452" class="InductiveConstructor"
      >Ax</a
      ><a name="3914"
      > </a
      ><a name="3915" class="Symbol"
      >())</a
      ><a name="3918"
      >
</a
      ><a name="3919" href="StlcProp.html#1993" class="Function"
      >progress</a
      ><a name="3927"
      > </a
      ><a name="3928" class="Symbol"
      >(</a
      ><a name="3929" href="Stlc.html#3508" class="InductiveConstructor"
      >&#8658;-I</a
      ><a name="3932"
      > </a
      ><a name="3933" href="StlcProp.html#3933" class="Bound"
      >&#8866;N</a
      ><a name="3935" class="Symbol"
      >)</a
      ><a name="3936"
      > </a
      ><a name="3937" class="Symbol"
      >=</a
      ><a name="3938"
      > </a
      ><a name="3939" href="StlcProp.html#1955" class="InductiveConstructor"
      >done</a
      ><a name="3943"
      > </a
      ><a name="3944" href="Stlc.html#1153" class="InductiveConstructor"
      >value-&#955;</a
      ><a name="3951"
      >
</a
      ><a name="3952" href="StlcProp.html#1993" class="Function"
      >progress</a
      ><a name="3960"
      > </a
      ><a name="3961" class="Symbol"
      >(</a
      ><a name="3962" href="Stlc.html#3585" class="InductiveConstructor"
      >&#8658;-E</a
      ><a name="3965"
      > </a
      ><a name="3966" href="StlcProp.html#3966" class="Bound"
      >&#8866;L</a
      ><a name="3968"
      > </a
      ><a name="3969" href="StlcProp.html#3969" class="Bound"
      >&#8866;M</a
      ><a name="3971" class="Symbol"
      >)</a
      ><a name="3972"
      > </a
      ><a name="3973" class="Keyword"
      >with</a
      ><a name="3977"
      > </a
      ><a name="3978" href="StlcProp.html#1993" class="Function"
      >progress</a
      ><a name="3986"
      > </a
      ><a name="3987" href="StlcProp.html#3966" class="Bound"
      >&#8866;L</a
      ><a name="3989"
      >
</a
      ><a name="3990" class="Symbol"
      >...</a
      ><a name="3993"
      > </a
      ><a name="3994" class="Symbol"
      >|</a
      ><a name="3995"
      > </a
      ><a name="3996" href="StlcProp.html#1916" class="InductiveConstructor"
      >steps</a
      ><a name="4001"
      > </a
      ><a name="4002" href="StlcProp.html#4002" class="Bound"
      >L&#10233;L&#8242;</a
      ><a name="4006"
      > </a
      ><a name="4007" class="Symbol"
      >=</a
      ><a name="4008"
      > </a
      ><a name="4009" href="StlcProp.html#1916" class="InductiveConstructor"
      >steps</a
      ><a name="4014"
      > </a
      ><a name="4015" class="Symbol"
      >(</a
      ><a name="4016" href="Stlc.html#1888" class="InductiveConstructor"
      >&#947;&#8658;&#8321;</a
      ><a name="4019"
      > </a
      ><a name="4020" href="StlcProp.html#4002" class="Bound"
      >L&#10233;L&#8242;</a
      ><a name="4024" class="Symbol"
      >)</a
      ><a name="4025"
      >
</a
      ><a name="4026" class="Symbol"
      >...</a
      ><a name="4029"
      > </a
      ><a name="4030" class="Symbol"
      >|</a
      ><a name="4031"
      > </a
      ><a name="4032" href="StlcProp.html#1955" class="InductiveConstructor"
      >done</a
      ><a name="4036"
      > </a
      ><a name="4037" href="StlcProp.html#4037" class="Bound"
      >valueL</a
      ><a name="4043"
      > </a
      ><a name="4044" class="Keyword"
      >with</a
      ><a name="4048"
      > </a
      ><a name="4049" href="StlcProp.html#1993" class="Function"
      >progress</a
      ><a name="4057"
      > </a
      ><a name="4058" href="StlcProp.html#3969" class="Bound"
      >&#8866;M</a
      ><a name="4060"
      >
</a
      ><a name="4061" class="Symbol"
      >...</a
      ><a name="4064"
      > </a
      ><a name="4065" class="Symbol"
      >|</a
      ><a name="4066"
      > </a
      ><a name="4067" href="StlcProp.html#1916" class="InductiveConstructor"
      >steps</a
      ><a name="4072"
      > </a
      ><a name="4073" href="StlcProp.html#4073" class="Bound"
      >M&#10233;M&#8242;</a
      ><a name="4077"
      > </a
      ><a name="4078" class="Symbol"
      >=</a
      ><a name="4079"
      > </a
      ><a name="4080" href="StlcProp.html#1916" class="InductiveConstructor"
      >steps</a
      ><a name="4085"
      > </a
      ><a name="4086" class="Symbol"
      >(</a
      ><a name="4087" href="Stlc.html#1941" class="InductiveConstructor"
      >&#947;&#8658;&#8322;</a
      ><a name="4090"
      > </a
      ><a name="4091" href="StlcProp.html#4037" class="Bound"
      >valueL</a
      ><a name="4097"
      > </a
      ><a name="4098" href="StlcProp.html#4073" class="Bound"
      >M&#10233;M&#8242;</a
      ><a name="4102" class="Symbol"
      >)</a
      ><a name="4103"
      >
</a
      ><a name="4104" class="Symbol"
      >...</a
      ><a name="4107"
      > </a
      ><a name="4108" class="Symbol"
      >|</a
      ><a name="4109"
      > </a
      ><a name="4110" href="StlcProp.html#1955" class="InductiveConstructor"
      >done</a
      ><a name="4114"
      > </a
      ><a name="4115" href="StlcProp.html#4115" class="Bound"
      >valueM</a
      ><a name="4121"
      > </a
      ><a name="4122" class="Keyword"
      >with</a
      ><a name="4126"
      > </a
      ><a name="4127" href="StlcProp.html#1350" class="Function"
      >canonicalFormsLemma</a
      ><a name="4146"
      > </a
      ><a name="4147" href="StlcProp.html#3966" class="Bound"
      >&#8866;L</a
      ><a name="4149"
      > </a
      ><a name="4150" href="StlcProp.html#4037" class="Bound"
      >valueL</a
      ><a name="4156"
      >
</a
      ><a name="4157" class="Symbol"
      >...</a
      ><a name="4160"
      > </a
      ><a name="4161" class="Symbol"
      >|</a
      ><a name="4162"
      > </a
      ><a name="4163" href="StlcProp.html#1202" class="InductiveConstructor"
      >canonical-&#955;</a
      ><a name="4174"
      > </a
      ><a name="4175" class="Symbol"
      >=</a
      ><a name="4176"
      > </a
      ><a name="4177" href="StlcProp.html#1916" class="InductiveConstructor"
      >steps</a
      ><a name="4182"
      > </a
      ><a name="4183" class="Symbol"
      >(</a
      ><a name="4184" href="Stlc.html#1819" class="InductiveConstructor"
      >&#946;&#8658;</a
      ><a name="4186"
      > </a
      ><a name="4187" href="StlcProp.html#4115" class="Bound"
      >valueM</a
      ><a name="4193" class="Symbol"
      >)</a
      ><a name="4194"
      >
</a
      ><a name="4195" href="StlcProp.html#1993" class="Function"
      >progress</a
      ><a name="4203"
      > </a
      ><a name="4204" href="Stlc.html#3663" class="InductiveConstructor"
      >&#120121;-I&#8321;</a
      ><a name="4208"
      > </a
      ><a name="4209" class="Symbol"
      >=</a
      ><a name="4210"
      > </a
      ><a name="4211" href="StlcProp.html#1955" class="InductiveConstructor"
      >done</a
      ><a name="4215"
      > </a
      ><a name="4216" href="Stlc.html#1202" class="InductiveConstructor"
      >value-true</a
      ><a name="4226"
      >
</a
      ><a name="4227" href="StlcProp.html#1993" class="Function"
      >progress</a
      ><a name="4235"
      > </a
      ><a name="4236" href="Stlc.html#3697" class="InductiveConstructor"
      >&#120121;-I&#8322;</a
      ><a name="4240"
      > </a
      ><a name="4241" class="Symbol"
      >=</a
      ><a name="4242"
      > </a
      ><a name="4243" href="StlcProp.html#1955" class="InductiveConstructor"
      >done</a
      ><a name="4247"
      > </a
      ><a name="4248" href="Stlc.html#1229" class="InductiveConstructor"
      >value-false</a
      ><a name="4259"
      >
</a
      ><a name="4260" href="StlcProp.html#1993" class="Function"
      >progress</a
      ><a name="4268"
      > </a
      ><a name="4269" class="Symbol"
      >(</a
      ><a name="4270" href="Stlc.html#3732" class="InductiveConstructor"
      >&#120121;-E</a
      ><a name="4273"
      > </a
      ><a name="4274" href="StlcProp.html#4274" class="Bound"
      >&#8866;L</a
      ><a name="4276"
      > </a
      ><a name="4277" href="StlcProp.html#4277" class="Bound"
      >&#8866;M</a
      ><a name="4279"
      > </a
      ><a name="4280" href="StlcProp.html#4280" class="Bound"
      >&#8866;N</a
      ><a name="4282" class="Symbol"
      >)</a
      ><a name="4283"
      > </a
      ><a name="4284" class="Keyword"
      >with</a
      ><a name="4288"
      > </a
      ><a name="4289" href="StlcProp.html#1993" class="Function"
      >progress</a
      ><a name="4297"
      > </a
      ><a name="4298" href="StlcProp.html#4274" class="Bound"
      >&#8866;L</a
      ><a name="4300"
      >
</a
      ><a name="4301" class="Symbol"
      >...</a
      ><a name="4304"
      > </a
      ><a name="4305" class="Symbol"
      >|</a
      ><a name="4306"
      > </a
      ><a name="4307" href="StlcProp.html#1916" class="InductiveConstructor"
      >steps</a
      ><a name="4312"
      > </a
      ><a name="4313" href="StlcProp.html#4313" class="Bound"
      >L&#10233;L&#8242;</a
      ><a name="4317"
      > </a
      ><a name="4318" class="Symbol"
      >=</a
      ><a name="4319"
      > </a
      ><a name="4320" href="StlcProp.html#1916" class="InductiveConstructor"
      >steps</a
      ><a name="4325"
      > </a
      ><a name="4326" class="Symbol"
      >(</a
      ><a name="4327" href="Stlc.html#2105" class="InductiveConstructor"
      >&#947;&#120121;</a
      ><a name="4329"
      > </a
      ><a name="4330" href="StlcProp.html#4313" class="Bound"
      >L&#10233;L&#8242;</a
      ><a name="4334" class="Symbol"
      >)</a
      ><a name="4335"
      >
</a
      ><a name="4336" class="Symbol"
      >...</a
      ><a name="4339"
      > </a
      ><a name="4340" class="Symbol"
      >|</a
      ><a name="4341"
      > </a
      ><a name="4342" href="StlcProp.html#1955" class="InductiveConstructor"
      >done</a
      ><a name="4346"
      > </a
      ><a name="4347" href="StlcProp.html#4347" class="Bound"
      >valueL</a
      ><a name="4353"
      > </a
      ><a name="4354" class="Keyword"
      >with</a
      ><a name="4358"
      > </a
      ><a name="4359" href="StlcProp.html#1350" class="Function"
      >canonicalFormsLemma</a
      ><a name="4378"
      > </a
      ><a name="4379" href="StlcProp.html#4274" class="Bound"
      >&#8866;L</a
      ><a name="4381"
      > </a
      ><a name="4382" href="StlcProp.html#4347" class="Bound"
      >valueL</a
      ><a name="4388"
      >
</a
      ><a name="4389" class="Symbol"
      >...</a
      ><a name="4392"
      > </a
      ><a name="4393" class="Symbol"
      >|</a
      ><a name="4394"
      > </a
      ><a name="4395" href="StlcProp.html#1269" class="InductiveConstructor"
      >canonical-true</a
      ><a name="4409"
      > </a
      ><a name="4410" class="Symbol"
      >=</a
      ><a name="4411"
      > </a
      ><a name="4412" href="StlcProp.html#1916" class="InductiveConstructor"
      >steps</a
      ><a name="4417"
      > </a
      ><a name="4418" href="Stlc.html#2008" class="InductiveConstructor"
      >&#946;&#120121;&#8321;</a
      ><a name="4421"
      >
</a
      ><a name="4422" class="Symbol"
      >...</a
      ><a name="4425"
      > </a
      ><a name="4426" class="Symbol"
      >|</a
      ><a name="4427"
      > </a
      ><a name="4428" href="StlcProp.html#1309" class="InductiveConstructor"
      >canonical-false</a
      ><a name="4443"
      > </a
      ><a name="4444" class="Symbol"
      >=</a
      ><a name="4445"
      > </a
      ><a name="4446" href="StlcProp.html#1916" class="InductiveConstructor"
      >steps</a
      ><a name="4451"
      > </a
      ><a name="4452" href="Stlc.html#2056" class="InductiveConstructor"
      >&#946;&#120121;&#8322;</a
      >
{% endraw %}</pre>

#### Exercise: 3 stars, optional (progress_from_term_ind)
Show that progress can also be proved by induction on terms
instead of induction on typing derivations.

<pre class="Agda">{% raw %}
<a name="4644" class="Keyword"
      >postulate</a
      ><a name="4653"
      >
  </a
      ><a name="4656" href="StlcProp.html#4656" class="Postulate"
      >progress&#8242;</a
      ><a name="4665"
      > </a
      ><a name="4666" class="Symbol"
      >:</a
      ><a name="4667"
      > </a
      ><a name="4668" class="Symbol"
      >&#8704;</a
      ><a name="4669"
      > </a
      ><a name="4670" href="StlcProp.html#4670" class="Bound"
      >M</a
      ><a name="4671"
      > </a
      ><a name="4672" class="Symbol"
      >{</a
      ><a name="4673" href="StlcProp.html#4673" class="Bound"
      >A</a
      ><a name="4674" class="Symbol"
      >}</a
      ><a name="4675"
      > </a
      ><a name="4676" class="Symbol"
      >&#8594;</a
      ><a name="4677"
      > </a
      ><a name="4678" href="Maps.html#10359" class="Function"
      >&#8709;</a
      ><a name="4679"
      > </a
      ><a name="4680" href="Stlc.html#3408" class="Datatype Operator"
      >&#8866;</a
      ><a name="4681"
      > </a
      ><a name="4682" href="StlcProp.html#4670" class="Bound"
      >M</a
      ><a name="4683"
      > </a
      ><a name="4684" href="Stlc.html#3408" class="Datatype Operator"
      >&#8758;</a
      ><a name="4685"
      > </a
      ><a name="4686" href="StlcProp.html#4673" class="Bound"
      >A</a
      ><a name="4687"
      > </a
      ><a name="4688" class="Symbol"
      >&#8594;</a
      ><a name="4689"
      > </a
      ><a name="4690" href="StlcProp.html#1886" class="Datatype"
      >Progress</a
      ><a name="4698"
      > </a
      ><a name="4699" href="StlcProp.html#4670" class="Bound"
      >M</a
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
<a name="7091" class="Keyword"
      >data</a
      ><a name="7095"
      > </a
      ><a name="7096" href="StlcProp.html#7096" class="Datatype Operator"
      >_&#8712;_</a
      ><a name="7099"
      > </a
      ><a name="7100" class="Symbol"
      >:</a
      ><a name="7101"
      > </a
      ><a name="7102" href="Maps.html#2215" class="Datatype"
      >Id</a
      ><a name="7104"
      > </a
      ><a name="7105" class="Symbol"
      >&#8594;</a
      ><a name="7106"
      > </a
      ><a name="7107" href="Stlc.html#715" class="Datatype"
      >Term</a
      ><a name="7111"
      > </a
      ><a name="7112" class="Symbol"
      >&#8594;</a
      ><a name="7113"
      > </a
      ><a name="7114" class="PrimitiveType"
      >Set</a
      ><a name="7117"
      > </a
      ><a name="7118" class="Keyword"
      >where</a
      ><a name="7123"
      >
  </a
      ><a name="7126" href="StlcProp.html#7126" class="InductiveConstructor"
      >free-var</a
      ><a name="7134"
      >  </a
      ><a name="7136" class="Symbol"
      >:</a
      ><a name="7137"
      > </a
      ><a name="7138" class="Symbol"
      >&#8704;</a
      ><a name="7139"
      > </a
      ><a name="7140" class="Symbol"
      >{</a
      ><a name="7141" href="StlcProp.html#7141" class="Bound"
      >x</a
      ><a name="7142" class="Symbol"
      >}</a
      ><a name="7143"
      > </a
      ><a name="7144" class="Symbol"
      >&#8594;</a
      ><a name="7145"
      > </a
      ><a name="7146" href="StlcProp.html#7141" class="Bound"
      >x</a
      ><a name="7147"
      > </a
      ><a name="7148" href="StlcProp.html#7096" class="Datatype Operator"
      >&#8712;</a
      ><a name="7149"
      > </a
      ><a name="7150" class="Symbol"
      >(</a
      ><a name="7151" href="Stlc.html#734" class="InductiveConstructor"
      >var</a
      ><a name="7154"
      > </a
      ><a name="7155" href="StlcProp.html#7141" class="Bound"
      >x</a
      ><a name="7156" class="Symbol"
      >)</a
      ><a name="7157"
      >
  </a
      ><a name="7160" href="StlcProp.html#7160" class="InductiveConstructor"
      >free-&#955;</a
      ><a name="7166"
      >  </a
      ><a name="7168" class="Symbol"
      >:</a
      ><a name="7169"
      > </a
      ><a name="7170" class="Symbol"
      >&#8704;</a
      ><a name="7171"
      > </a
      ><a name="7172" class="Symbol"
      >{</a
      ><a name="7173" href="StlcProp.html#7173" class="Bound"
      >x</a
      ><a name="7174"
      > </a
      ><a name="7175" href="StlcProp.html#7175" class="Bound"
      >y</a
      ><a name="7176"
      > </a
      ><a name="7177" href="StlcProp.html#7177" class="Bound"
      >A</a
      ><a name="7178"
      > </a
      ><a name="7179" href="StlcProp.html#7179" class="Bound"
      >N</a
      ><a name="7180" class="Symbol"
      >}</a
      ><a name="7181"
      > </a
      ><a name="7182" class="Symbol"
      >&#8594;</a
      ><a name="7183"
      > </a
      ><a name="7184" href="StlcProp.html#7175" class="Bound"
      >y</a
      ><a name="7185"
      > </a
      ><a name="7186" href="https://agda.github.io/agda-stdlib/Relation.Binary.Core.html#4493" class="Function Operator"
      >&#8802;</a
      ><a name="7187"
      > </a
      ><a name="7188" href="StlcProp.html#7173" class="Bound"
      >x</a
      ><a name="7189"
      > </a
      ><a name="7190" class="Symbol"
      >&#8594;</a
      ><a name="7191"
      > </a
      ><a name="7192" href="StlcProp.html#7173" class="Bound"
      >x</a
      ><a name="7193"
      > </a
      ><a name="7194" href="StlcProp.html#7096" class="Datatype Operator"
      >&#8712;</a
      ><a name="7195"
      > </a
      ><a name="7196" href="StlcProp.html#7179" class="Bound"
      >N</a
      ><a name="7197"
      > </a
      ><a name="7198" class="Symbol"
      >&#8594;</a
      ><a name="7199"
      > </a
      ><a name="7200" href="StlcProp.html#7173" class="Bound"
      >x</a
      ><a name="7201"
      > </a
      ><a name="7202" href="StlcProp.html#7096" class="Datatype Operator"
      >&#8712;</a
      ><a name="7203"
      > </a
      ><a name="7204" class="Symbol"
      >(</a
      ><a name="7205" href="Stlc.html#752" class="InductiveConstructor Operator"
      >&#955;[</a
      ><a name="7207"
      > </a
      ><a name="7208" href="StlcProp.html#7175" class="Bound"
      >y</a
      ><a name="7209"
      > </a
      ><a name="7210" href="Stlc.html#752" class="InductiveConstructor Operator"
      >&#8758;</a
      ><a name="7211"
      > </a
      ><a name="7212" href="StlcProp.html#7177" class="Bound"
      >A</a
      ><a name="7213"
      > </a
      ><a name="7214" href="Stlc.html#752" class="InductiveConstructor Operator"
      >]</a
      ><a name="7215"
      > </a
      ><a name="7216" href="StlcProp.html#7179" class="Bound"
      >N</a
      ><a name="7217" class="Symbol"
      >)</a
      ><a name="7218"
      >
  </a
      ><a name="7221" href="StlcProp.html#7221" class="InductiveConstructor"
      >free-&#183;&#8321;</a
      ><a name="7228"
      > </a
      ><a name="7229" class="Symbol"
      >:</a
      ><a name="7230"
      > </a
      ><a name="7231" class="Symbol"
      >&#8704;</a
      ><a name="7232"
      > </a
      ><a name="7233" class="Symbol"
      >{</a
      ><a name="7234" href="StlcProp.html#7234" class="Bound"
      >x</a
      ><a name="7235"
      > </a
      ><a name="7236" href="StlcProp.html#7236" class="Bound"
      >L</a
      ><a name="7237"
      > </a
      ><a name="7238" href="StlcProp.html#7238" class="Bound"
      >M</a
      ><a name="7239" class="Symbol"
      >}</a
      ><a name="7240"
      > </a
      ><a name="7241" class="Symbol"
      >&#8594;</a
      ><a name="7242"
      > </a
      ><a name="7243" href="StlcProp.html#7234" class="Bound"
      >x</a
      ><a name="7244"
      > </a
      ><a name="7245" href="StlcProp.html#7096" class="Datatype Operator"
      >&#8712;</a
      ><a name="7246"
      > </a
      ><a name="7247" href="StlcProp.html#7236" class="Bound"
      >L</a
      ><a name="7248"
      > </a
      ><a name="7249" class="Symbol"
      >&#8594;</a
      ><a name="7250"
      > </a
      ><a name="7251" href="StlcProp.html#7234" class="Bound"
      >x</a
      ><a name="7252"
      > </a
      ><a name="7253" href="StlcProp.html#7096" class="Datatype Operator"
      >&#8712;</a
      ><a name="7254"
      > </a
      ><a name="7255" class="Symbol"
      >(</a
      ><a name="7256" href="StlcProp.html#7236" class="Bound"
      >L</a
      ><a name="7257"
      > </a
      ><a name="7258" href="Stlc.html#788" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="7259"
      > </a
      ><a name="7260" href="StlcProp.html#7238" class="Bound"
      >M</a
      ><a name="7261" class="Symbol"
      >)</a
      ><a name="7262"
      >
  </a
      ><a name="7265" href="StlcProp.html#7265" class="InductiveConstructor"
      >free-&#183;&#8322;</a
      ><a name="7272"
      > </a
      ><a name="7273" class="Symbol"
      >:</a
      ><a name="7274"
      > </a
      ><a name="7275" class="Symbol"
      >&#8704;</a
      ><a name="7276"
      > </a
      ><a name="7277" class="Symbol"
      >{</a
      ><a name="7278" href="StlcProp.html#7278" class="Bound"
      >x</a
      ><a name="7279"
      > </a
      ><a name="7280" href="StlcProp.html#7280" class="Bound"
      >L</a
      ><a name="7281"
      > </a
      ><a name="7282" href="StlcProp.html#7282" class="Bound"
      >M</a
      ><a name="7283" class="Symbol"
      >}</a
      ><a name="7284"
      > </a
      ><a name="7285" class="Symbol"
      >&#8594;</a
      ><a name="7286"
      > </a
      ><a name="7287" href="StlcProp.html#7278" class="Bound"
      >x</a
      ><a name="7288"
      > </a
      ><a name="7289" href="StlcProp.html#7096" class="Datatype Operator"
      >&#8712;</a
      ><a name="7290"
      > </a
      ><a name="7291" href="StlcProp.html#7282" class="Bound"
      >M</a
      ><a name="7292"
      > </a
      ><a name="7293" class="Symbol"
      >&#8594;</a
      ><a name="7294"
      > </a
      ><a name="7295" href="StlcProp.html#7278" class="Bound"
      >x</a
      ><a name="7296"
      > </a
      ><a name="7297" href="StlcProp.html#7096" class="Datatype Operator"
      >&#8712;</a
      ><a name="7298"
      > </a
      ><a name="7299" class="Symbol"
      >(</a
      ><a name="7300" href="StlcProp.html#7280" class="Bound"
      >L</a
      ><a name="7301"
      > </a
      ><a name="7302" href="Stlc.html#788" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="7303"
      > </a
      ><a name="7304" href="StlcProp.html#7282" class="Bound"
      >M</a
      ><a name="7305" class="Symbol"
      >)</a
      ><a name="7306"
      >
  </a
      ><a name="7309" href="StlcProp.html#7309" class="InductiveConstructor"
      >free-if&#8321;</a
      ><a name="7317"
      > </a
      ><a name="7318" class="Symbol"
      >:</a
      ><a name="7319"
      > </a
      ><a name="7320" class="Symbol"
      >&#8704;</a
      ><a name="7321"
      > </a
      ><a name="7322" class="Symbol"
      >{</a
      ><a name="7323" href="StlcProp.html#7323" class="Bound"
      >x</a
      ><a name="7324"
      > </a
      ><a name="7325" href="StlcProp.html#7325" class="Bound"
      >L</a
      ><a name="7326"
      > </a
      ><a name="7327" href="StlcProp.html#7327" class="Bound"
      >M</a
      ><a name="7328"
      > </a
      ><a name="7329" href="StlcProp.html#7329" class="Bound"
      >N</a
      ><a name="7330" class="Symbol"
      >}</a
      ><a name="7331"
      > </a
      ><a name="7332" class="Symbol"
      >&#8594;</a
      ><a name="7333"
      > </a
      ><a name="7334" href="StlcProp.html#7323" class="Bound"
      >x</a
      ><a name="7335"
      > </a
      ><a name="7336" href="StlcProp.html#7096" class="Datatype Operator"
      >&#8712;</a
      ><a name="7337"
      > </a
      ><a name="7338" href="StlcProp.html#7325" class="Bound"
      >L</a
      ><a name="7339"
      > </a
      ><a name="7340" class="Symbol"
      >&#8594;</a
      ><a name="7341"
      > </a
      ><a name="7342" href="StlcProp.html#7323" class="Bound"
      >x</a
      ><a name="7343"
      > </a
      ><a name="7344" href="StlcProp.html#7096" class="Datatype Operator"
      >&#8712;</a
      ><a name="7345"
      > </a
      ><a name="7346" class="Symbol"
      >(</a
      ><a name="7347" href="Stlc.html#844" class="InductiveConstructor Operator"
      >if</a
      ><a name="7349"
      > </a
      ><a name="7350" href="StlcProp.html#7325" class="Bound"
      >L</a
      ><a name="7351"
      > </a
      ><a name="7352" href="Stlc.html#844" class="InductiveConstructor Operator"
      >then</a
      ><a name="7356"
      > </a
      ><a name="7357" href="StlcProp.html#7327" class="Bound"
      >M</a
      ><a name="7358"
      > </a
      ><a name="7359" href="Stlc.html#844" class="InductiveConstructor Operator"
      >else</a
      ><a name="7363"
      > </a
      ><a name="7364" href="StlcProp.html#7329" class="Bound"
      >N</a
      ><a name="7365" class="Symbol"
      >)</a
      ><a name="7366"
      >
  </a
      ><a name="7369" href="StlcProp.html#7369" class="InductiveConstructor"
      >free-if&#8322;</a
      ><a name="7377"
      > </a
      ><a name="7378" class="Symbol"
      >:</a
      ><a name="7379"
      > </a
      ><a name="7380" class="Symbol"
      >&#8704;</a
      ><a name="7381"
      > </a
      ><a name="7382" class="Symbol"
      >{</a
      ><a name="7383" href="StlcProp.html#7383" class="Bound"
      >x</a
      ><a name="7384"
      > </a
      ><a name="7385" href="StlcProp.html#7385" class="Bound"
      >L</a
      ><a name="7386"
      > </a
      ><a name="7387" href="StlcProp.html#7387" class="Bound"
      >M</a
      ><a name="7388"
      > </a
      ><a name="7389" href="StlcProp.html#7389" class="Bound"
      >N</a
      ><a name="7390" class="Symbol"
      >}</a
      ><a name="7391"
      > </a
      ><a name="7392" class="Symbol"
      >&#8594;</a
      ><a name="7393"
      > </a
      ><a name="7394" href="StlcProp.html#7383" class="Bound"
      >x</a
      ><a name="7395"
      > </a
      ><a name="7396" href="StlcProp.html#7096" class="Datatype Operator"
      >&#8712;</a
      ><a name="7397"
      > </a
      ><a name="7398" href="StlcProp.html#7387" class="Bound"
      >M</a
      ><a name="7399"
      > </a
      ><a name="7400" class="Symbol"
      >&#8594;</a
      ><a name="7401"
      > </a
      ><a name="7402" href="StlcProp.html#7383" class="Bound"
      >x</a
      ><a name="7403"
      > </a
      ><a name="7404" href="StlcProp.html#7096" class="Datatype Operator"
      >&#8712;</a
      ><a name="7405"
      > </a
      ><a name="7406" class="Symbol"
      >(</a
      ><a name="7407" href="Stlc.html#844" class="InductiveConstructor Operator"
      >if</a
      ><a name="7409"
      > </a
      ><a name="7410" href="StlcProp.html#7385" class="Bound"
      >L</a
      ><a name="7411"
      > </a
      ><a name="7412" href="Stlc.html#844" class="InductiveConstructor Operator"
      >then</a
      ><a name="7416"
      > </a
      ><a name="7417" href="StlcProp.html#7387" class="Bound"
      >M</a
      ><a name="7418"
      > </a
      ><a name="7419" href="Stlc.html#844" class="InductiveConstructor Operator"
      >else</a
      ><a name="7423"
      > </a
      ><a name="7424" href="StlcProp.html#7389" class="Bound"
      >N</a
      ><a name="7425" class="Symbol"
      >)</a
      ><a name="7426"
      >
  </a
      ><a name="7429" href="StlcProp.html#7429" class="InductiveConstructor"
      >free-if&#8323;</a
      ><a name="7437"
      > </a
      ><a name="7438" class="Symbol"
      >:</a
      ><a name="7439"
      > </a
      ><a name="7440" class="Symbol"
      >&#8704;</a
      ><a name="7441"
      > </a
      ><a name="7442" class="Symbol"
      >{</a
      ><a name="7443" href="StlcProp.html#7443" class="Bound"
      >x</a
      ><a name="7444"
      > </a
      ><a name="7445" href="StlcProp.html#7445" class="Bound"
      >L</a
      ><a name="7446"
      > </a
      ><a name="7447" href="StlcProp.html#7447" class="Bound"
      >M</a
      ><a name="7448"
      > </a
      ><a name="7449" href="StlcProp.html#7449" class="Bound"
      >N</a
      ><a name="7450" class="Symbol"
      >}</a
      ><a name="7451"
      > </a
      ><a name="7452" class="Symbol"
      >&#8594;</a
      ><a name="7453"
      > </a
      ><a name="7454" href="StlcProp.html#7443" class="Bound"
      >x</a
      ><a name="7455"
      > </a
      ><a name="7456" href="StlcProp.html#7096" class="Datatype Operator"
      >&#8712;</a
      ><a name="7457"
      > </a
      ><a name="7458" href="StlcProp.html#7449" class="Bound"
      >N</a
      ><a name="7459"
      > </a
      ><a name="7460" class="Symbol"
      >&#8594;</a
      ><a name="7461"
      > </a
      ><a name="7462" href="StlcProp.html#7443" class="Bound"
      >x</a
      ><a name="7463"
      > </a
      ><a name="7464" href="StlcProp.html#7096" class="Datatype Operator"
      >&#8712;</a
      ><a name="7465"
      > </a
      ><a name="7466" class="Symbol"
      >(</a
      ><a name="7467" href="Stlc.html#844" class="InductiveConstructor Operator"
      >if</a
      ><a name="7469"
      > </a
      ><a name="7470" href="StlcProp.html#7445" class="Bound"
      >L</a
      ><a name="7471"
      > </a
      ><a name="7472" href="Stlc.html#844" class="InductiveConstructor Operator"
      >then</a
      ><a name="7476"
      > </a
      ><a name="7477" href="StlcProp.html#7447" class="Bound"
      >M</a
      ><a name="7478"
      > </a
      ><a name="7479" href="Stlc.html#844" class="InductiveConstructor Operator"
      >else</a
      ><a name="7483"
      > </a
      ><a name="7484" href="StlcProp.html#7449" class="Bound"
      >N</a
      ><a name="7485" class="Symbol"
      >)</a
      >
{% endraw %}</pre>

A term in which no variables appear free is said to be _closed_.

<pre class="Agda">{% raw %}
<a name="7578" href="StlcProp.html#7578" class="Function"
      >closed</a
      ><a name="7584"
      > </a
      ><a name="7585" class="Symbol"
      >:</a
      ><a name="7586"
      > </a
      ><a name="7587" href="Stlc.html#715" class="Datatype"
      >Term</a
      ><a name="7591"
      > </a
      ><a name="7592" class="Symbol"
      >&#8594;</a
      ><a name="7593"
      > </a
      ><a name="7594" class="PrimitiveType"
      >Set</a
      ><a name="7597"
      >
</a
      ><a name="7598" href="StlcProp.html#7578" class="Function"
      >closed</a
      ><a name="7604"
      > </a
      ><a name="7605" href="StlcProp.html#7605" class="Bound"
      >M</a
      ><a name="7606"
      > </a
      ><a name="7607" class="Symbol"
      >=</a
      ><a name="7608"
      > </a
      ><a name="7609" class="Symbol"
      >&#8704;</a
      ><a name="7610"
      > </a
      ><a name="7611" class="Symbol"
      >{</a
      ><a name="7612" href="StlcProp.html#7612" class="Bound"
      >x</a
      ><a name="7613" class="Symbol"
      >}</a
      ><a name="7614"
      > </a
      ><a name="7615" class="Symbol"
      >&#8594;</a
      ><a name="7616"
      > </a
      ><a name="7617" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#414" class="Function Operator"
      >&#172;</a
      ><a name="7618"
      > </a
      ><a name="7619" class="Symbol"
      >(</a
      ><a name="7620" href="StlcProp.html#7612" class="Bound"
      >x</a
      ><a name="7621"
      > </a
      ><a name="7622" href="StlcProp.html#7096" class="Datatype Operator"
      >&#8712;</a
      ><a name="7623"
      > </a
      ><a name="7624" href="StlcProp.html#7605" class="Bound"
      >M</a
      ><a name="7625" class="Symbol"
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
<a name="8327" href="StlcProp.html#8327" class="Function"
      >freeLemma</a
      ><a name="8336"
      > </a
      ><a name="8337" class="Symbol"
      >:</a
      ><a name="8338"
      > </a
      ><a name="8339" class="Symbol"
      >&#8704;</a
      ><a name="8340"
      > </a
      ><a name="8341" class="Symbol"
      >{</a
      ><a name="8342" href="StlcProp.html#8342" class="Bound"
      >x</a
      ><a name="8343"
      > </a
      ><a name="8344" href="StlcProp.html#8344" class="Bound"
      >M</a
      ><a name="8345"
      > </a
      ><a name="8346" href="StlcProp.html#8346" class="Bound"
      >A</a
      ><a name="8347"
      > </a
      ><a name="8348" href="StlcProp.html#8348" class="Bound"
      >&#915;</a
      ><a name="8349" class="Symbol"
      >}</a
      ><a name="8350"
      > </a
      ><a name="8351" class="Symbol"
      >&#8594;</a
      ><a name="8352"
      > </a
      ><a name="8353" href="StlcProp.html#8342" class="Bound"
      >x</a
      ><a name="8354"
      > </a
      ><a name="8355" href="StlcProp.html#7096" class="Datatype Operator"
      >&#8712;</a
      ><a name="8356"
      > </a
      ><a name="8357" href="StlcProp.html#8344" class="Bound"
      >M</a
      ><a name="8358"
      > </a
      ><a name="8359" class="Symbol"
      >&#8594;</a
      ><a name="8360"
      > </a
      ><a name="8361" href="StlcProp.html#8348" class="Bound"
      >&#915;</a
      ><a name="8362"
      > </a
      ><a name="8363" href="Stlc.html#3408" class="Datatype Operator"
      >&#8866;</a
      ><a name="8364"
      > </a
      ><a name="8365" href="StlcProp.html#8344" class="Bound"
      >M</a
      ><a name="8366"
      > </a
      ><a name="8367" href="Stlc.html#3408" class="Datatype Operator"
      >&#8758;</a
      ><a name="8368"
      > </a
      ><a name="8369" href="StlcProp.html#8346" class="Bound"
      >A</a
      ><a name="8370"
      > </a
      ><a name="8371" class="Symbol"
      >&#8594;</a
      ><a name="8372"
      > </a
      ><a name="8373" href="https://agda.github.io/agda-stdlib/Data.Product.html#823" class="Function"
      >&#8707;</a
      ><a name="8374"
      > </a
      ><a name="8375" class="Symbol"
      >&#955;</a
      ><a name="8376"
      > </a
      ><a name="8377" href="StlcProp.html#8377" class="Bound"
      >B</a
      ><a name="8378"
      > </a
      ><a name="8379" class="Symbol"
      >&#8594;</a
      ><a name="8380"
      > </a
      ><a name="8381" href="StlcProp.html#8348" class="Bound"
      >&#915;</a
      ><a name="8382"
      > </a
      ><a name="8383" href="StlcProp.html#8342" class="Bound"
      >x</a
      ><a name="8384"
      > </a
      ><a name="8385" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="8386"
      > </a
      ><a name="8387" href="https://agda.github.io/agda-stdlib/Data.Maybe.Base.html#373" class="InductiveConstructor"
      >just</a
      ><a name="8391"
      > </a
      ><a name="8392" href="StlcProp.html#8377" class="Bound"
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
<a name="9855" href="StlcProp.html#8327" class="Function"
      >freeLemma</a
      ><a name="9864"
      > </a
      ><a name="9865" href="StlcProp.html#7126" class="InductiveConstructor"
      >free-var</a
      ><a name="9873"
      > </a
      ><a name="9874" class="Symbol"
      >(</a
      ><a name="9875" href="Stlc.html#3452" class="InductiveConstructor"
      >Ax</a
      ><a name="9877"
      > </a
      ><a name="9878" href="StlcProp.html#9878" class="Bound"
      >&#915;x&#8801;justA</a
      ><a name="9886" class="Symbol"
      >)</a
      ><a name="9887"
      > </a
      ><a name="9888" class="Symbol"
      >=</a
      ><a name="9889"
      > </a
      ><a name="9890" class="Symbol"
      >(_</a
      ><a name="9892"
      > </a
      ><a name="9893" href="https://agda.github.io/agda-stdlib/Data.Product.html#509" class="InductiveConstructor Operator"
      >,</a
      ><a name="9894"
      > </a
      ><a name="9895" href="StlcProp.html#9878" class="Bound"
      >&#915;x&#8801;justA</a
      ><a name="9903" class="Symbol"
      >)</a
      ><a name="9904"
      >
</a
      ><a name="9905" href="StlcProp.html#8327" class="Function"
      >freeLemma</a
      ><a name="9914"
      > </a
      ><a name="9915" class="Symbol"
      >(</a
      ><a name="9916" href="StlcProp.html#7221" class="InductiveConstructor"
      >free-&#183;&#8321;</a
      ><a name="9923"
      > </a
      ><a name="9924" href="StlcProp.html#9924" class="Bound"
      >x&#8712;L</a
      ><a name="9927" class="Symbol"
      >)</a
      ><a name="9928"
      > </a
      ><a name="9929" class="Symbol"
      >(</a
      ><a name="9930" href="Stlc.html#3585" class="InductiveConstructor"
      >&#8658;-E</a
      ><a name="9933"
      > </a
      ><a name="9934" href="StlcProp.html#9934" class="Bound"
      >&#8866;L</a
      ><a name="9936"
      > </a
      ><a name="9937" href="StlcProp.html#9937" class="Bound"
      >&#8866;M</a
      ><a name="9939" class="Symbol"
      >)</a
      ><a name="9940"
      > </a
      ><a name="9941" class="Symbol"
      >=</a
      ><a name="9942"
      > </a
      ><a name="9943" href="StlcProp.html#8327" class="Function"
      >freeLemma</a
      ><a name="9952"
      > </a
      ><a name="9953" href="StlcProp.html#9924" class="Bound"
      >x&#8712;L</a
      ><a name="9956"
      > </a
      ><a name="9957" href="StlcProp.html#9934" class="Bound"
      >&#8866;L</a
      ><a name="9959"
      >
</a
      ><a name="9960" href="StlcProp.html#8327" class="Function"
      >freeLemma</a
      ><a name="9969"
      > </a
      ><a name="9970" class="Symbol"
      >(</a
      ><a name="9971" href="StlcProp.html#7265" class="InductiveConstructor"
      >free-&#183;&#8322;</a
      ><a name="9978"
      > </a
      ><a name="9979" href="StlcProp.html#9979" class="Bound"
      >x&#8712;M</a
      ><a name="9982" class="Symbol"
      >)</a
      ><a name="9983"
      > </a
      ><a name="9984" class="Symbol"
      >(</a
      ><a name="9985" href="Stlc.html#3585" class="InductiveConstructor"
      >&#8658;-E</a
      ><a name="9988"
      > </a
      ><a name="9989" href="StlcProp.html#9989" class="Bound"
      >&#8866;L</a
      ><a name="9991"
      > </a
      ><a name="9992" href="StlcProp.html#9992" class="Bound"
      >&#8866;M</a
      ><a name="9994" class="Symbol"
      >)</a
      ><a name="9995"
      > </a
      ><a name="9996" class="Symbol"
      >=</a
      ><a name="9997"
      > </a
      ><a name="9998" href="StlcProp.html#8327" class="Function"
      >freeLemma</a
      ><a name="10007"
      > </a
      ><a name="10008" href="StlcProp.html#9979" class="Bound"
      >x&#8712;M</a
      ><a name="10011"
      > </a
      ><a name="10012" href="StlcProp.html#9992" class="Bound"
      >&#8866;M</a
      ><a name="10014"
      >
</a
      ><a name="10015" href="StlcProp.html#8327" class="Function"
      >freeLemma</a
      ><a name="10024"
      > </a
      ><a name="10025" class="Symbol"
      >(</a
      ><a name="10026" href="StlcProp.html#7309" class="InductiveConstructor"
      >free-if&#8321;</a
      ><a name="10034"
      > </a
      ><a name="10035" href="StlcProp.html#10035" class="Bound"
      >x&#8712;L</a
      ><a name="10038" class="Symbol"
      >)</a
      ><a name="10039"
      > </a
      ><a name="10040" class="Symbol"
      >(</a
      ><a name="10041" href="Stlc.html#3732" class="InductiveConstructor"
      >&#120121;-E</a
      ><a name="10044"
      > </a
      ><a name="10045" href="StlcProp.html#10045" class="Bound"
      >&#8866;L</a
      ><a name="10047"
      > </a
      ><a name="10048" href="StlcProp.html#10048" class="Bound"
      >&#8866;M</a
      ><a name="10050"
      > </a
      ><a name="10051" href="StlcProp.html#10051" class="Bound"
      >&#8866;N</a
      ><a name="10053" class="Symbol"
      >)</a
      ><a name="10054"
      > </a
      ><a name="10055" class="Symbol"
      >=</a
      ><a name="10056"
      > </a
      ><a name="10057" href="StlcProp.html#8327" class="Function"
      >freeLemma</a
      ><a name="10066"
      > </a
      ><a name="10067" href="StlcProp.html#10035" class="Bound"
      >x&#8712;L</a
      ><a name="10070"
      > </a
      ><a name="10071" href="StlcProp.html#10045" class="Bound"
      >&#8866;L</a
      ><a name="10073"
      >
</a
      ><a name="10074" href="StlcProp.html#8327" class="Function"
      >freeLemma</a
      ><a name="10083"
      > </a
      ><a name="10084" class="Symbol"
      >(</a
      ><a name="10085" href="StlcProp.html#7369" class="InductiveConstructor"
      >free-if&#8322;</a
      ><a name="10093"
      > </a
      ><a name="10094" href="StlcProp.html#10094" class="Bound"
      >x&#8712;M</a
      ><a name="10097" class="Symbol"
      >)</a
      ><a name="10098"
      > </a
      ><a name="10099" class="Symbol"
      >(</a
      ><a name="10100" href="Stlc.html#3732" class="InductiveConstructor"
      >&#120121;-E</a
      ><a name="10103"
      > </a
      ><a name="10104" href="StlcProp.html#10104" class="Bound"
      >&#8866;L</a
      ><a name="10106"
      > </a
      ><a name="10107" href="StlcProp.html#10107" class="Bound"
      >&#8866;M</a
      ><a name="10109"
      > </a
      ><a name="10110" href="StlcProp.html#10110" class="Bound"
      >&#8866;N</a
      ><a name="10112" class="Symbol"
      >)</a
      ><a name="10113"
      > </a
      ><a name="10114" class="Symbol"
      >=</a
      ><a name="10115"
      > </a
      ><a name="10116" href="StlcProp.html#8327" class="Function"
      >freeLemma</a
      ><a name="10125"
      > </a
      ><a name="10126" href="StlcProp.html#10094" class="Bound"
      >x&#8712;M</a
      ><a name="10129"
      > </a
      ><a name="10130" href="StlcProp.html#10107" class="Bound"
      >&#8866;M</a
      ><a name="10132"
      >
</a
      ><a name="10133" href="StlcProp.html#8327" class="Function"
      >freeLemma</a
      ><a name="10142"
      > </a
      ><a name="10143" class="Symbol"
      >(</a
      ><a name="10144" href="StlcProp.html#7429" class="InductiveConstructor"
      >free-if&#8323;</a
      ><a name="10152"
      > </a
      ><a name="10153" href="StlcProp.html#10153" class="Bound"
      >x&#8712;N</a
      ><a name="10156" class="Symbol"
      >)</a
      ><a name="10157"
      > </a
      ><a name="10158" class="Symbol"
      >(</a
      ><a name="10159" href="Stlc.html#3732" class="InductiveConstructor"
      >&#120121;-E</a
      ><a name="10162"
      > </a
      ><a name="10163" href="StlcProp.html#10163" class="Bound"
      >&#8866;L</a
      ><a name="10165"
      > </a
      ><a name="10166" href="StlcProp.html#10166" class="Bound"
      >&#8866;M</a
      ><a name="10168"
      > </a
      ><a name="10169" href="StlcProp.html#10169" class="Bound"
      >&#8866;N</a
      ><a name="10171" class="Symbol"
      >)</a
      ><a name="10172"
      > </a
      ><a name="10173" class="Symbol"
      >=</a
      ><a name="10174"
      > </a
      ><a name="10175" href="StlcProp.html#8327" class="Function"
      >freeLemma</a
      ><a name="10184"
      > </a
      ><a name="10185" href="StlcProp.html#10153" class="Bound"
      >x&#8712;N</a
      ><a name="10188"
      > </a
      ><a name="10189" href="StlcProp.html#10169" class="Bound"
      >&#8866;N</a
      ><a name="10191"
      >
</a
      ><a name="10192" href="StlcProp.html#8327" class="Function"
      >freeLemma</a
      ><a name="10201"
      > </a
      ><a name="10202" class="Symbol"
      >(</a
      ><a name="10203" href="StlcProp.html#7160" class="InductiveConstructor"
      >free-&#955;</a
      ><a name="10209"
      > </a
      ><a name="10210" class="Symbol"
      >{</a
      ><a name="10211" href="StlcProp.html#10211" class="Bound"
      >x</a
      ><a name="10212" class="Symbol"
      >}</a
      ><a name="10213"
      > </a
      ><a name="10214" class="Symbol"
      >{</a
      ><a name="10215" href="StlcProp.html#10215" class="Bound"
      >y</a
      ><a name="10216" class="Symbol"
      >}</a
      ><a name="10217"
      > </a
      ><a name="10218" href="StlcProp.html#10218" class="Bound"
      >y&#8802;x</a
      ><a name="10221"
      > </a
      ><a name="10222" href="StlcProp.html#10222" class="Bound"
      >x&#8712;N</a
      ><a name="10225" class="Symbol"
      >)</a
      ><a name="10226"
      > </a
      ><a name="10227" class="Symbol"
      >(</a
      ><a name="10228" href="Stlc.html#3508" class="InductiveConstructor"
      >&#8658;-I</a
      ><a name="10231"
      > </a
      ><a name="10232" href="StlcProp.html#10232" class="Bound"
      >&#8866;N</a
      ><a name="10234" class="Symbol"
      >)</a
      ><a name="10235"
      > </a
      ><a name="10236" class="Keyword"
      >with</a
      ><a name="10240"
      > </a
      ><a name="10241" href="StlcProp.html#8327" class="Function"
      >freeLemma</a
      ><a name="10250"
      > </a
      ><a name="10251" href="StlcProp.html#10222" class="Bound"
      >x&#8712;N</a
      ><a name="10254"
      > </a
      ><a name="10255" href="StlcProp.html#10232" class="Bound"
      >&#8866;N</a
      ><a name="10257"
      >
</a
      ><a name="10258" class="Symbol"
      >...</a
      ><a name="10261"
      > </a
      ><a name="10262" class="Symbol"
      >|</a
      ><a name="10263"
      > </a
      ><a name="10264" href="StlcProp.html#10264" class="Bound"
      >&#915;x=justC</a
      ><a name="10272"
      > </a
      ><a name="10273" class="Keyword"
      >with</a
      ><a name="10277"
      > </a
      ><a name="10278" href="StlcProp.html#10215" class="Bound"
      >y</a
      ><a name="10279"
      > </a
      ><a name="10280" href="Maps.html#2558" class="Function Operator"
      >&#8799;</a
      ><a name="10281"
      > </a
      ><a name="10282" href="StlcProp.html#10211" class="Bound"
      >x</a
      ><a name="10283"
      >
</a
      ><a name="10284" class="Symbol"
      >...</a
      ><a name="10287"
      > </a
      ><a name="10288" class="Symbol"
      >|</a
      ><a name="10289"
      > </a
      ><a name="10290" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#520" class="InductiveConstructor"
      >yes</a
      ><a name="10293"
      > </a
      ><a name="10294" href="StlcProp.html#10294" class="Bound"
      >y&#8801;x</a
      ><a name="10297"
      > </a
      ><a name="10298" class="Symbol"
      >=</a
      ><a name="10299"
      > </a
      ><a name="10300" href="https://agda.github.io/agda-stdlib/Data.Empty.html#348" class="Function"
      >&#8869;-elim</a
      ><a name="10306"
      > </a
      ><a name="10307" class="Symbol"
      >(</a
      ><a name="10308" href="StlcProp.html#10218" class="Bound"
      >y&#8802;x</a
      ><a name="10311"
      > </a
      ><a name="10312" href="StlcProp.html#10294" class="Bound"
      >y&#8801;x</a
      ><a name="10315" class="Symbol"
      >)</a
      ><a name="10316"
      >
</a
      ><a name="10317" class="Symbol"
      >...</a
      ><a name="10320"
      > </a
      ><a name="10321" class="Symbol"
      >|</a
      ><a name="10322"
      > </a
      ><a name="10323" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#547" class="InductiveConstructor"
      >no</a
      ><a name="10325"
      >  </a
      ><a name="10327" class="Symbol"
      >_</a
      ><a name="10328"
      >   </a
      ><a name="10331" class="Symbol"
      >=</a
      ><a name="10332"
      > </a
      ><a name="10333" href="StlcProp.html#10264" class="Bound"
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
<a name="10705" class="Keyword"
      >postulate</a
      ><a name="10714"
      >
  </a
      ><a name="10717" href="StlcProp.html#10717" class="Postulate"
      >&#8709;&#8866;-closed</a
      ><a name="10726"
      > </a
      ><a name="10727" class="Symbol"
      >:</a
      ><a name="10728"
      > </a
      ><a name="10729" class="Symbol"
      >&#8704;</a
      ><a name="10730"
      > </a
      ><a name="10731" class="Symbol"
      >{</a
      ><a name="10732" href="StlcProp.html#10732" class="Bound"
      >M</a
      ><a name="10733"
      > </a
      ><a name="10734" href="StlcProp.html#10734" class="Bound"
      >A</a
      ><a name="10735" class="Symbol"
      >}</a
      ><a name="10736"
      > </a
      ><a name="10737" class="Symbol"
      >&#8594;</a
      ><a name="10738"
      > </a
      ><a name="10739" href="Maps.html#10359" class="Function"
      >&#8709;</a
      ><a name="10740"
      > </a
      ><a name="10741" href="Stlc.html#3408" class="Datatype Operator"
      >&#8866;</a
      ><a name="10742"
      > </a
      ><a name="10743" href="StlcProp.html#10732" class="Bound"
      >M</a
      ><a name="10744"
      > </a
      ><a name="10745" href="Stlc.html#3408" class="Datatype Operator"
      >&#8758;</a
      ><a name="10746"
      > </a
      ><a name="10747" href="StlcProp.html#10734" class="Bound"
      >A</a
      ><a name="10748"
      > </a
      ><a name="10749" class="Symbol"
      >&#8594;</a
      ><a name="10750"
      > </a
      ><a name="10751" href="StlcProp.html#7578" class="Function"
      >closed</a
      ><a name="10757"
      > </a
      ><a name="10758" href="StlcProp.html#10732" class="Bound"
      >M</a
      >
{% endraw %}</pre>

<div class="hidden">
<pre class="Agda">{% raw %}
<a name="10806" href="StlcProp.html#10806" class="Function"
      >contradiction</a
      ><a name="10819"
      > </a
      ><a name="10820" class="Symbol"
      >:</a
      ><a name="10821"
      > </a
      ><a name="10822" class="Symbol"
      >&#8704;</a
      ><a name="10823"
      > </a
      ><a name="10824" class="Symbol"
      >{</a
      ><a name="10825" href="StlcProp.html#10825" class="Bound"
      >X</a
      ><a name="10826"
      > </a
      ><a name="10827" class="Symbol"
      >:</a
      ><a name="10828"
      > </a
      ><a name="10829" class="PrimitiveType"
      >Set</a
      ><a name="10832" class="Symbol"
      >}</a
      ><a name="10833"
      > </a
      ><a name="10834" class="Symbol"
      >&#8594;</a
      ><a name="10835"
      > </a
      ><a name="10836" class="Symbol"
      >&#8704;</a
      ><a name="10837"
      > </a
      ><a name="10838" class="Symbol"
      >{</a
      ><a name="10839" href="StlcProp.html#10839" class="Bound"
      >x</a
      ><a name="10840"
      > </a
      ><a name="10841" class="Symbol"
      >:</a
      ><a name="10842"
      > </a
      ><a name="10843" href="StlcProp.html#10825" class="Bound"
      >X</a
      ><a name="10844" class="Symbol"
      >}</a
      ><a name="10845"
      > </a
      ><a name="10846" class="Symbol"
      >&#8594;</a
      ><a name="10847"
      > </a
      ><a name="10848" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#414" class="Function Operator"
      >&#172;</a
      ><a name="10849"
      > </a
      ><a name="10850" class="Symbol"
      >(</a
      ><a name="10851" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >_&#8801;_</a
      ><a name="10854"
      > </a
      ><a name="10855" class="Symbol"
      >{</a
      ><a name="10856" class="Argument"
      >A</a
      ><a name="10857"
      > </a
      ><a name="10858" class="Symbol"
      >=</a
      ><a name="10859"
      > </a
      ><a name="10860" href="https://agda.github.io/agda-stdlib/Data.Maybe.Base.html#335" class="Datatype"
      >Maybe</a
      ><a name="10865"
      > </a
      ><a name="10866" href="StlcProp.html#10825" class="Bound"
      >X</a
      ><a name="10867" class="Symbol"
      >}</a
      ><a name="10868"
      > </a
      ><a name="10869" class="Symbol"
      >(</a
      ><a name="10870" href="https://agda.github.io/agda-stdlib/Data.Maybe.Base.html#373" class="InductiveConstructor"
      >just</a
      ><a name="10874"
      > </a
      ><a name="10875" href="StlcProp.html#10839" class="Bound"
      >x</a
      ><a name="10876" class="Symbol"
      >)</a
      ><a name="10877"
      > </a
      ><a name="10878" href="https://agda.github.io/agda-stdlib/Data.Maybe.Base.html#403" class="InductiveConstructor"
      >nothing</a
      ><a name="10885" class="Symbol"
      >)</a
      ><a name="10886"
      >
</a
      ><a name="10887" href="StlcProp.html#10806" class="Function"
      >contradiction</a
      ><a name="10900"
      > </a
      ><a name="10901" class="Symbol"
      >()</a
      ><a name="10903"
      >

</a
      ><a name="10905" href="StlcProp.html#10905" class="Function"
      >&#8709;&#8866;-closed&#8242;</a
      ><a name="10915"
      > </a
      ><a name="10916" class="Symbol"
      >:</a
      ><a name="10917"
      > </a
      ><a name="10918" class="Symbol"
      >&#8704;</a
      ><a name="10919"
      > </a
      ><a name="10920" class="Symbol"
      >{</a
      ><a name="10921" href="StlcProp.html#10921" class="Bound"
      >M</a
      ><a name="10922"
      > </a
      ><a name="10923" href="StlcProp.html#10923" class="Bound"
      >A</a
      ><a name="10924" class="Symbol"
      >}</a
      ><a name="10925"
      > </a
      ><a name="10926" class="Symbol"
      >&#8594;</a
      ><a name="10927"
      > </a
      ><a name="10928" href="Maps.html#10359" class="Function"
      >&#8709;</a
      ><a name="10929"
      > </a
      ><a name="10930" href="Stlc.html#3408" class="Datatype Operator"
      >&#8866;</a
      ><a name="10931"
      > </a
      ><a name="10932" href="StlcProp.html#10921" class="Bound"
      >M</a
      ><a name="10933"
      > </a
      ><a name="10934" href="Stlc.html#3408" class="Datatype Operator"
      >&#8758;</a
      ><a name="10935"
      > </a
      ><a name="10936" href="StlcProp.html#10923" class="Bound"
      >A</a
      ><a name="10937"
      > </a
      ><a name="10938" class="Symbol"
      >&#8594;</a
      ><a name="10939"
      > </a
      ><a name="10940" href="StlcProp.html#7578" class="Function"
      >closed</a
      ><a name="10946"
      > </a
      ><a name="10947" href="StlcProp.html#10921" class="Bound"
      >M</a
      ><a name="10948"
      >
</a
      ><a name="10949" href="StlcProp.html#10905" class="Function"
      >&#8709;&#8866;-closed&#8242;</a
      ><a name="10959"
      > </a
      ><a name="10960" class="Symbol"
      >{</a
      ><a name="10961" href="StlcProp.html#10961" class="Bound"
      >M</a
      ><a name="10962" class="Symbol"
      >}</a
      ><a name="10963"
      > </a
      ><a name="10964" class="Symbol"
      >{</a
      ><a name="10965" href="StlcProp.html#10965" class="Bound"
      >A</a
      ><a name="10966" class="Symbol"
      >}</a
      ><a name="10967"
      > </a
      ><a name="10968" href="StlcProp.html#10968" class="Bound"
      >&#8866;M</a
      ><a name="10970"
      > </a
      ><a name="10971" class="Symbol"
      >{</a
      ><a name="10972" href="StlcProp.html#10972" class="Bound"
      >x</a
      ><a name="10973" class="Symbol"
      >}</a
      ><a name="10974"
      > </a
      ><a name="10975" href="StlcProp.html#10975" class="Bound"
      >x&#8712;M</a
      ><a name="10978"
      > </a
      ><a name="10979" class="Keyword"
      >with</a
      ><a name="10983"
      > </a
      ><a name="10984" href="StlcProp.html#8327" class="Function"
      >freeLemma</a
      ><a name="10993"
      > </a
      ><a name="10994" href="StlcProp.html#10975" class="Bound"
      >x&#8712;M</a
      ><a name="10997"
      > </a
      ><a name="10998" href="StlcProp.html#10968" class="Bound"
      >&#8866;M</a
      ><a name="11000"
      >
</a
      ><a name="11001" class="Symbol"
      >...</a
      ><a name="11004"
      > </a
      ><a name="11005" class="Symbol"
      >|</a
      ><a name="11006"
      > </a
      ><a name="11007" class="Symbol"
      >(</a
      ><a name="11008" href="StlcProp.html#11008" class="Bound"
      >B</a
      ><a name="11009"
      > </a
      ><a name="11010" href="https://agda.github.io/agda-stdlib/Data.Product.html#509" class="InductiveConstructor Operator"
      >,</a
      ><a name="11011"
      > </a
      ><a name="11012" href="StlcProp.html#11012" class="Bound"
      >&#8709;x&#8801;justB</a
      ><a name="11020" class="Symbol"
      >)</a
      ><a name="11021"
      > </a
      ><a name="11022" class="Symbol"
      >=</a
      ><a name="11023"
      > </a
      ><a name="11024" href="StlcProp.html#10806" class="Function"
      >contradiction</a
      ><a name="11037"
      > </a
      ><a name="11038" class="Symbol"
      >(</a
      ><a name="11039" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.Core.html#632" class="Function"
      >trans</a
      ><a name="11044"
      > </a
      ><a name="11045" class="Symbol"
      >(</a
      ><a name="11046" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.Core.html#565" class="Function"
      >sym</a
      ><a name="11049"
      > </a
      ><a name="11050" href="StlcProp.html#11012" class="Bound"
      >&#8709;x&#8801;justB</a
      ><a name="11058" class="Symbol"
      >)</a
      ><a name="11059"
      > </a
      ><a name="11060" class="Symbol"
      >(</a
      ><a name="11061" href="Maps.html#10667" class="Function"
      >apply-&#8709;</a
      ><a name="11068"
      > </a
      ><a name="11069" href="StlcProp.html#10972" class="Bound"
      >x</a
      ><a name="11070" class="Symbol"
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
<a name="11418" href="StlcProp.html#11418" class="Function"
      >contextLemma</a
      ><a name="11430"
      > </a
      ><a name="11431" class="Symbol"
      >:</a
      ><a name="11432"
      > </a
      ><a name="11433" class="Symbol"
      >&#8704;</a
      ><a name="11434"
      > </a
      ><a name="11435" class="Symbol"
      >{</a
      ><a name="11436" href="StlcProp.html#11436" class="Bound"
      >&#915;</a
      ><a name="11437"
      > </a
      ><a name="11438" href="StlcProp.html#11438" class="Bound"
      >&#915;&#8242;</a
      ><a name="11440"
      > </a
      ><a name="11441" href="StlcProp.html#11441" class="Bound"
      >M</a
      ><a name="11442"
      > </a
      ><a name="11443" href="StlcProp.html#11443" class="Bound"
      >A</a
      ><a name="11444" class="Symbol"
      >}</a
      ><a name="11445"
      >
        </a
      ><a name="11454" class="Symbol"
      >&#8594;</a
      ><a name="11455"
      > </a
      ><a name="11456" class="Symbol"
      >(&#8704;</a
      ><a name="11458"
      > </a
      ><a name="11459" class="Symbol"
      >{</a
      ><a name="11460" href="StlcProp.html#11460" class="Bound"
      >x</a
      ><a name="11461" class="Symbol"
      >}</a
      ><a name="11462"
      > </a
      ><a name="11463" class="Symbol"
      >&#8594;</a
      ><a name="11464"
      > </a
      ><a name="11465" href="StlcProp.html#11460" class="Bound"
      >x</a
      ><a name="11466"
      > </a
      ><a name="11467" href="StlcProp.html#7096" class="Datatype Operator"
      >&#8712;</a
      ><a name="11468"
      > </a
      ><a name="11469" href="StlcProp.html#11441" class="Bound"
      >M</a
      ><a name="11470"
      > </a
      ><a name="11471" class="Symbol"
      >&#8594;</a
      ><a name="11472"
      > </a
      ><a name="11473" href="StlcProp.html#11436" class="Bound"
      >&#915;</a
      ><a name="11474"
      > </a
      ><a name="11475" href="StlcProp.html#11460" class="Bound"
      >x</a
      ><a name="11476"
      > </a
      ><a name="11477" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="11478"
      > </a
      ><a name="11479" href="StlcProp.html#11438" class="Bound"
      >&#915;&#8242;</a
      ><a name="11481"
      > </a
      ><a name="11482" href="StlcProp.html#11460" class="Bound"
      >x</a
      ><a name="11483" class="Symbol"
      >)</a
      ><a name="11484"
      >
        </a
      ><a name="11493" class="Symbol"
      >&#8594;</a
      ><a name="11494"
      > </a
      ><a name="11495" href="StlcProp.html#11436" class="Bound"
      >&#915;</a
      ><a name="11496"
      >  </a
      ><a name="11498" href="Stlc.html#3408" class="Datatype Operator"
      >&#8866;</a
      ><a name="11499"
      > </a
      ><a name="11500" href="StlcProp.html#11441" class="Bound"
      >M</a
      ><a name="11501"
      > </a
      ><a name="11502" href="Stlc.html#3408" class="Datatype Operator"
      >&#8758;</a
      ><a name="11503"
      > </a
      ><a name="11504" href="StlcProp.html#11443" class="Bound"
      >A</a
      ><a name="11505"
      >
        </a
      ><a name="11514" class="Symbol"
      >&#8594;</a
      ><a name="11515"
      > </a
      ><a name="11516" href="StlcProp.html#11438" class="Bound"
      >&#915;&#8242;</a
      ><a name="11518"
      > </a
      ><a name="11519" href="Stlc.html#3408" class="Datatype Operator"
      >&#8866;</a
      ><a name="11520"
      > </a
      ><a name="11521" href="StlcProp.html#11441" class="Bound"
      >M</a
      ><a name="11522"
      > </a
      ><a name="11523" href="Stlc.html#3408" class="Datatype Operator"
      >&#8758;</a
      ><a name="11524"
      > </a
      ><a name="11525" href="StlcProp.html#11443" class="Bound"
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
<a name="13692" href="StlcProp.html#11418" class="Function"
      >contextLemma</a
      ><a name="13704"
      > </a
      ><a name="13705" href="StlcProp.html#13705" class="Bound"
      >&#915;~&#915;&#8242;</a
      ><a name="13709"
      > </a
      ><a name="13710" class="Symbol"
      >(</a
      ><a name="13711" href="Stlc.html#3452" class="InductiveConstructor"
      >Ax</a
      ><a name="13713"
      > </a
      ><a name="13714" href="StlcProp.html#13714" class="Bound"
      >&#915;x&#8801;justA</a
      ><a name="13722" class="Symbol"
      >)</a
      ><a name="13723"
      > </a
      ><a name="13724" class="Keyword"
      >rewrite</a
      ><a name="13731"
      > </a
      ><a name="13732" class="Symbol"
      >(</a
      ><a name="13733" href="StlcProp.html#13705" class="Bound"
      >&#915;~&#915;&#8242;</a
      ><a name="13737"
      > </a
      ><a name="13738" href="StlcProp.html#7126" class="InductiveConstructor"
      >free-var</a
      ><a name="13746" class="Symbol"
      >)</a
      ><a name="13747"
      > </a
      ><a name="13748" class="Symbol"
      >=</a
      ><a name="13749"
      > </a
      ><a name="13750" href="Stlc.html#3452" class="InductiveConstructor"
      >Ax</a
      ><a name="13752"
      > </a
      ><a name="13753" href="StlcProp.html#13714" class="Bound"
      >&#915;x&#8801;justA</a
      ><a name="13761"
      >
</a
      ><a name="13762" href="StlcProp.html#11418" class="Function"
      >contextLemma</a
      ><a name="13774"
      > </a
      ><a name="13775" class="Symbol"
      >{</a
      ><a name="13776" href="StlcProp.html#13776" class="Bound"
      >&#915;</a
      ><a name="13777" class="Symbol"
      >}</a
      ><a name="13778"
      > </a
      ><a name="13779" class="Symbol"
      >{</a
      ><a name="13780" href="StlcProp.html#13780" class="Bound"
      >&#915;&#8242;</a
      ><a name="13782" class="Symbol"
      >}</a
      ><a name="13783"
      > </a
      ><a name="13784" class="Symbol"
      >{</a
      ><a name="13785" href="Stlc.html#752" class="InductiveConstructor Operator"
      >&#955;[</a
      ><a name="13787"
      > </a
      ><a name="13788" href="StlcProp.html#13788" class="Bound"
      >x</a
      ><a name="13789"
      > </a
      ><a name="13790" href="Stlc.html#752" class="InductiveConstructor Operator"
      >&#8758;</a
      ><a name="13791"
      > </a
      ><a name="13792" href="StlcProp.html#13792" class="Bound"
      >A</a
      ><a name="13793"
      > </a
      ><a name="13794" href="Stlc.html#752" class="InductiveConstructor Operator"
      >]</a
      ><a name="13795"
      > </a
      ><a name="13796" href="StlcProp.html#13796" class="Bound"
      >N</a
      ><a name="13797" class="Symbol"
      >}</a
      ><a name="13798"
      > </a
      ><a name="13799" href="StlcProp.html#13799" class="Bound"
      >&#915;~&#915;&#8242;</a
      ><a name="13803"
      > </a
      ><a name="13804" class="Symbol"
      >(</a
      ><a name="13805" href="Stlc.html#3508" class="InductiveConstructor"
      >&#8658;-I</a
      ><a name="13808"
      > </a
      ><a name="13809" href="StlcProp.html#13809" class="Bound"
      >&#8866;N</a
      ><a name="13811" class="Symbol"
      >)</a
      ><a name="13812"
      > </a
      ><a name="13813" class="Symbol"
      >=</a
      ><a name="13814"
      > </a
      ><a name="13815" href="Stlc.html#3508" class="InductiveConstructor"
      >&#8658;-I</a
      ><a name="13818"
      > </a
      ><a name="13819" class="Symbol"
      >(</a
      ><a name="13820" href="StlcProp.html#11418" class="Function"
      >contextLemma</a
      ><a name="13832"
      > </a
      ><a name="13833" href="StlcProp.html#13854" class="Function"
      >&#915;x~&#915;&#8242;x</a
      ><a name="13839"
      > </a
      ><a name="13840" href="StlcProp.html#13809" class="Bound"
      >&#8866;N</a
      ><a name="13842" class="Symbol"
      >)</a
      ><a name="13843"
      >
  </a
      ><a name="13846" class="Keyword"
      >where</a
      ><a name="13851"
      >
  </a
      ><a name="13854" href="StlcProp.html#13854" class="Function"
      >&#915;x~&#915;&#8242;x</a
      ><a name="13860"
      > </a
      ><a name="13861" class="Symbol"
      >:</a
      ><a name="13862"
      > </a
      ><a name="13863" class="Symbol"
      >&#8704;</a
      ><a name="13864"
      > </a
      ><a name="13865" class="Symbol"
      >{</a
      ><a name="13866" href="StlcProp.html#13866" class="Bound"
      >y</a
      ><a name="13867" class="Symbol"
      >}</a
      ><a name="13868"
      > </a
      ><a name="13869" class="Symbol"
      >&#8594;</a
      ><a name="13870"
      > </a
      ><a name="13871" href="StlcProp.html#13866" class="Bound"
      >y</a
      ><a name="13872"
      > </a
      ><a name="13873" href="StlcProp.html#7096" class="Datatype Operator"
      >&#8712;</a
      ><a name="13874"
      > </a
      ><a name="13875" href="StlcProp.html#13796" class="Bound"
      >N</a
      ><a name="13876"
      > </a
      ><a name="13877" class="Symbol"
      >&#8594;</a
      ><a name="13878"
      > </a
      ><a name="13879" class="Symbol"
      >(</a
      ><a name="13880" href="StlcProp.html#13776" class="Bound"
      >&#915;</a
      ><a name="13881"
      > </a
      ><a name="13882" href="Maps.html#10462" class="Function Operator"
      >,</a
      ><a name="13883"
      > </a
      ><a name="13884" href="StlcProp.html#13788" class="Bound"
      >x</a
      ><a name="13885"
      > </a
      ><a name="13886" href="Maps.html#10462" class="Function Operator"
      >&#8758;</a
      ><a name="13887"
      > </a
      ><a name="13888" href="StlcProp.html#13792" class="Bound"
      >A</a
      ><a name="13889" class="Symbol"
      >)</a
      ><a name="13890"
      > </a
      ><a name="13891" href="StlcProp.html#13866" class="Bound"
      >y</a
      ><a name="13892"
      > </a
      ><a name="13893" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="13894"
      > </a
      ><a name="13895" class="Symbol"
      >(</a
      ><a name="13896" href="StlcProp.html#13780" class="Bound"
      >&#915;&#8242;</a
      ><a name="13898"
      > </a
      ><a name="13899" href="Maps.html#10462" class="Function Operator"
      >,</a
      ><a name="13900"
      > </a
      ><a name="13901" href="StlcProp.html#13788" class="Bound"
      >x</a
      ><a name="13902"
      > </a
      ><a name="13903" href="Maps.html#10462" class="Function Operator"
      >&#8758;</a
      ><a name="13904"
      > </a
      ><a name="13905" href="StlcProp.html#13792" class="Bound"
      >A</a
      ><a name="13906" class="Symbol"
      >)</a
      ><a name="13907"
      > </a
      ><a name="13908" href="StlcProp.html#13866" class="Bound"
      >y</a
      ><a name="13909"
      >
  </a
      ><a name="13912" href="StlcProp.html#13854" class="Function"
      >&#915;x~&#915;&#8242;x</a
      ><a name="13918"
      > </a
      ><a name="13919" class="Symbol"
      >{</a
      ><a name="13920" href="StlcProp.html#13920" class="Bound"
      >y</a
      ><a name="13921" class="Symbol"
      >}</a
      ><a name="13922"
      > </a
      ><a name="13923" href="StlcProp.html#13923" class="Bound"
      >y&#8712;N</a
      ><a name="13926"
      > </a
      ><a name="13927" class="Keyword"
      >with</a
      ><a name="13931"
      > </a
      ><a name="13932" href="StlcProp.html#13788" class="Bound"
      >x</a
      ><a name="13933"
      > </a
      ><a name="13934" href="Maps.html#2558" class="Function Operator"
      >&#8799;</a
      ><a name="13935"
      > </a
      ><a name="13936" href="StlcProp.html#13920" class="Bound"
      >y</a
      ><a name="13937"
      >
  </a
      ><a name="13940" class="Symbol"
      >...</a
      ><a name="13943"
      > </a
      ><a name="13944" class="Symbol"
      >|</a
      ><a name="13945"
      > </a
      ><a name="13946" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#520" class="InductiveConstructor"
      >yes</a
      ><a name="13949"
      > </a
      ><a name="13950" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="13954"
      > </a
      ><a name="13955" class="Symbol"
      >=</a
      ><a name="13956"
      > </a
      ><a name="13957" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="13961"
      >
  </a
      ><a name="13964" class="Symbol"
      >...</a
      ><a name="13967"
      > </a
      ><a name="13968" class="Symbol"
      >|</a
      ><a name="13969"
      > </a
      ><a name="13970" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#547" class="InductiveConstructor"
      >no</a
      ><a name="13972"
      >  </a
      ><a name="13974" href="StlcProp.html#13974" class="Bound"
      >x&#8802;y</a
      ><a name="13977"
      >  </a
      ><a name="13979" class="Symbol"
      >=</a
      ><a name="13980"
      > </a
      ><a name="13981" href="StlcProp.html#13799" class="Bound"
      >&#915;~&#915;&#8242;</a
      ><a name="13985"
      > </a
      ><a name="13986" class="Symbol"
      >(</a
      ><a name="13987" href="StlcProp.html#7160" class="InductiveConstructor"
      >free-&#955;</a
      ><a name="13993"
      > </a
      ><a name="13994" href="StlcProp.html#13974" class="Bound"
      >x&#8802;y</a
      ><a name="13997"
      > </a
      ><a name="13998" href="StlcProp.html#13923" class="Bound"
      >y&#8712;N</a
      ><a name="14001" class="Symbol"
      >)</a
      ><a name="14002"
      >
</a
      ><a name="14003" href="StlcProp.html#11418" class="Function"
      >contextLemma</a
      ><a name="14015"
      > </a
      ><a name="14016" href="StlcProp.html#14016" class="Bound"
      >&#915;~&#915;&#8242;</a
      ><a name="14020"
      > </a
      ><a name="14021" class="Symbol"
      >(</a
      ><a name="14022" href="Stlc.html#3585" class="InductiveConstructor"
      >&#8658;-E</a
      ><a name="14025"
      > </a
      ><a name="14026" href="StlcProp.html#14026" class="Bound"
      >&#8866;L</a
      ><a name="14028"
      > </a
      ><a name="14029" href="StlcProp.html#14029" class="Bound"
      >&#8866;M</a
      ><a name="14031" class="Symbol"
      >)</a
      ><a name="14032"
      > </a
      ><a name="14033" class="Symbol"
      >=</a
      ><a name="14034"
      > </a
      ><a name="14035" href="Stlc.html#3585" class="InductiveConstructor"
      >&#8658;-E</a
      ><a name="14038"
      > </a
      ><a name="14039" class="Symbol"
      >(</a
      ><a name="14040" href="StlcProp.html#11418" class="Function"
      >contextLemma</a
      ><a name="14052"
      > </a
      ><a name="14053" class="Symbol"
      >(</a
      ><a name="14054" href="StlcProp.html#14016" class="Bound"
      >&#915;~&#915;&#8242;</a
      ><a name="14058"
      > </a
      ><a name="14059" href="https://agda.github.io/agda-stdlib/Function.html#713" class="Function Operator"
      >&#8728;</a
      ><a name="14060"
      > </a
      ><a name="14061" href="StlcProp.html#7221" class="InductiveConstructor"
      >free-&#183;&#8321;</a
      ><a name="14068" class="Symbol"
      >)</a
      ><a name="14069"
      >  </a
      ><a name="14071" href="StlcProp.html#14026" class="Bound"
      >&#8866;L</a
      ><a name="14073" class="Symbol"
      >)</a
      ><a name="14074"
      > </a
      ><a name="14075" class="Symbol"
      >(</a
      ><a name="14076" href="StlcProp.html#11418" class="Function"
      >contextLemma</a
      ><a name="14088"
      > </a
      ><a name="14089" class="Symbol"
      >(</a
      ><a name="14090" href="StlcProp.html#14016" class="Bound"
      >&#915;~&#915;&#8242;</a
      ><a name="14094"
      > </a
      ><a name="14095" href="https://agda.github.io/agda-stdlib/Function.html#713" class="Function Operator"
      >&#8728;</a
      ><a name="14096"
      > </a
      ><a name="14097" href="StlcProp.html#7265" class="InductiveConstructor"
      >free-&#183;&#8322;</a
      ><a name="14104" class="Symbol"
      >)</a
      ><a name="14105"
      > </a
      ><a name="14106" href="StlcProp.html#14029" class="Bound"
      >&#8866;M</a
      ><a name="14108" class="Symbol"
      >)</a
      ><a name="14109"
      > 
</a
      ><a name="14111" href="StlcProp.html#11418" class="Function"
      >contextLemma</a
      ><a name="14123"
      > </a
      ><a name="14124" href="StlcProp.html#14124" class="Bound"
      >&#915;~&#915;&#8242;</a
      ><a name="14128"
      > </a
      ><a name="14129" href="Stlc.html#3663" class="InductiveConstructor"
      >&#120121;-I&#8321;</a
      ><a name="14133"
      > </a
      ><a name="14134" class="Symbol"
      >=</a
      ><a name="14135"
      > </a
      ><a name="14136" href="Stlc.html#3663" class="InductiveConstructor"
      >&#120121;-I&#8321;</a
      ><a name="14140"
      >
</a
      ><a name="14141" href="StlcProp.html#11418" class="Function"
      >contextLemma</a
      ><a name="14153"
      > </a
      ><a name="14154" href="StlcProp.html#14154" class="Bound"
      >&#915;~&#915;&#8242;</a
      ><a name="14158"
      > </a
      ><a name="14159" href="Stlc.html#3697" class="InductiveConstructor"
      >&#120121;-I&#8322;</a
      ><a name="14163"
      > </a
      ><a name="14164" class="Symbol"
      >=</a
      ><a name="14165"
      > </a
      ><a name="14166" href="Stlc.html#3697" class="InductiveConstructor"
      >&#120121;-I&#8322;</a
      ><a name="14170"
      >
</a
      ><a name="14171" href="StlcProp.html#11418" class="Function"
      >contextLemma</a
      ><a name="14183"
      > </a
      ><a name="14184" href="StlcProp.html#14184" class="Bound"
      >&#915;~&#915;&#8242;</a
      ><a name="14188"
      > </a
      ><a name="14189" class="Symbol"
      >(</a
      ><a name="14190" href="Stlc.html#3732" class="InductiveConstructor"
      >&#120121;-E</a
      ><a name="14193"
      > </a
      ><a name="14194" href="StlcProp.html#14194" class="Bound"
      >&#8866;L</a
      ><a name="14196"
      > </a
      ><a name="14197" href="StlcProp.html#14197" class="Bound"
      >&#8866;M</a
      ><a name="14199"
      > </a
      ><a name="14200" href="StlcProp.html#14200" class="Bound"
      >&#8866;N</a
      ><a name="14202" class="Symbol"
      >)</a
      ><a name="14203"
      >
  </a
      ><a name="14206" class="Symbol"
      >=</a
      ><a name="14207"
      > </a
      ><a name="14208" href="Stlc.html#3732" class="InductiveConstructor"
      >&#120121;-E</a
      ><a name="14211"
      > </a
      ><a name="14212" class="Symbol"
      >(</a
      ><a name="14213" href="StlcProp.html#11418" class="Function"
      >contextLemma</a
      ><a name="14225"
      > </a
      ><a name="14226" class="Symbol"
      >(</a
      ><a name="14227" href="StlcProp.html#14184" class="Bound"
      >&#915;~&#915;&#8242;</a
      ><a name="14231"
      > </a
      ><a name="14232" href="https://agda.github.io/agda-stdlib/Function.html#713" class="Function Operator"
      >&#8728;</a
      ><a name="14233"
      > </a
      ><a name="14234" href="StlcProp.html#7309" class="InductiveConstructor"
      >free-if&#8321;</a
      ><a name="14242" class="Symbol"
      >)</a
      ><a name="14243"
      > </a
      ><a name="14244" href="StlcProp.html#14194" class="Bound"
      >&#8866;L</a
      ><a name="14246" class="Symbol"
      >)</a
      ><a name="14247"
      > </a
      ><a name="14248" class="Symbol"
      >(</a
      ><a name="14249" href="StlcProp.html#11418" class="Function"
      >contextLemma</a
      ><a name="14261"
      > </a
      ><a name="14262" class="Symbol"
      >(</a
      ><a name="14263" href="StlcProp.html#14184" class="Bound"
      >&#915;~&#915;&#8242;</a
      ><a name="14267"
      > </a
      ><a name="14268" href="https://agda.github.io/agda-stdlib/Function.html#713" class="Function Operator"
      >&#8728;</a
      ><a name="14269"
      > </a
      ><a name="14270" href="StlcProp.html#7369" class="InductiveConstructor"
      >free-if&#8322;</a
      ><a name="14278" class="Symbol"
      >)</a
      ><a name="14279"
      > </a
      ><a name="14280" href="StlcProp.html#14197" class="Bound"
      >&#8866;M</a
      ><a name="14282" class="Symbol"
      >)</a
      ><a name="14283"
      > </a
      ><a name="14284" class="Symbol"
      >(</a
      ><a name="14285" href="StlcProp.html#11418" class="Function"
      >contextLemma</a
      ><a name="14297"
      > </a
      ><a name="14298" class="Symbol"
      >(</a
      ><a name="14299" href="StlcProp.html#14184" class="Bound"
      >&#915;~&#915;&#8242;</a
      ><a name="14303"
      > </a
      ><a name="14304" href="https://agda.github.io/agda-stdlib/Function.html#713" class="Function Operator"
      >&#8728;</a
      ><a name="14305"
      > </a
      ><a name="14306" href="StlcProp.html#7429" class="InductiveConstructor"
      >free-if&#8323;</a
      ><a name="14314" class="Symbol"
      >)</a
      ><a name="14315"
      > </a
      ><a name="14316" href="StlcProp.html#14200" class="Bound"
      >&#8866;N</a
      ><a name="14318" class="Symbol"
      >)</a
      ><a name="14319"
      >

</a
      ><a name="14321" class="Comment"
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
<a name="15695" href="StlcProp.html#15695" class="Function"
      >preservation-[&#8758;=]</a
      ><a name="15712"
      > </a
      ><a name="15713" class="Symbol"
      >:</a
      ><a name="15714"
      > </a
      ><a name="15715" class="Symbol"
      >&#8704;</a
      ><a name="15716"
      > </a
      ><a name="15717" class="Symbol"
      >{</a
      ><a name="15718" href="StlcProp.html#15718" class="Bound"
      >&#915;</a
      ><a name="15719"
      > </a
      ><a name="15720" href="StlcProp.html#15720" class="Bound"
      >x</a
      ><a name="15721"
      > </a
      ><a name="15722" href="StlcProp.html#15722" class="Bound"
      >A</a
      ><a name="15723"
      > </a
      ><a name="15724" href="StlcProp.html#15724" class="Bound"
      >N</a
      ><a name="15725"
      > </a
      ><a name="15726" href="StlcProp.html#15726" class="Bound"
      >B</a
      ><a name="15727"
      > </a
      ><a name="15728" href="StlcProp.html#15728" class="Bound"
      >V</a
      ><a name="15729" class="Symbol"
      >}</a
      ><a name="15730"
      >
                 </a
      ><a name="15748" class="Symbol"
      >&#8594;</a
      ><a name="15749"
      > </a
      ><a name="15750" class="Symbol"
      >(</a
      ><a name="15751" href="StlcProp.html#15718" class="Bound"
      >&#915;</a
      ><a name="15752"
      > </a
      ><a name="15753" href="Maps.html#10462" class="Function Operator"
      >,</a
      ><a name="15754"
      > </a
      ><a name="15755" href="StlcProp.html#15720" class="Bound"
      >x</a
      ><a name="15756"
      > </a
      ><a name="15757" href="Maps.html#10462" class="Function Operator"
      >&#8758;</a
      ><a name="15758"
      > </a
      ><a name="15759" href="StlcProp.html#15722" class="Bound"
      >A</a
      ><a name="15760" class="Symbol"
      >)</a
      ><a name="15761"
      > </a
      ><a name="15762" href="Stlc.html#3408" class="Datatype Operator"
      >&#8866;</a
      ><a name="15763"
      > </a
      ><a name="15764" href="StlcProp.html#15724" class="Bound"
      >N</a
      ><a name="15765"
      > </a
      ><a name="15766" href="Stlc.html#3408" class="Datatype Operator"
      >&#8758;</a
      ><a name="15767"
      > </a
      ><a name="15768" href="StlcProp.html#15726" class="Bound"
      >B</a
      ><a name="15769"
      >
                 </a
      ><a name="15787" class="Symbol"
      >&#8594;</a
      ><a name="15788"
      > </a
      ><a name="15789" href="Maps.html#10359" class="Function"
      >&#8709;</a
      ><a name="15790"
      > </a
      ><a name="15791" href="Stlc.html#3408" class="Datatype Operator"
      >&#8866;</a
      ><a name="15792"
      > </a
      ><a name="15793" href="StlcProp.html#15728" class="Bound"
      >V</a
      ><a name="15794"
      > </a
      ><a name="15795" href="Stlc.html#3408" class="Datatype Operator"
      >&#8758;</a
      ><a name="15796"
      > </a
      ><a name="15797" href="StlcProp.html#15722" class="Bound"
      >A</a
      ><a name="15798"
      >
                 </a
      ><a name="15816" class="Symbol"
      >&#8594;</a
      ><a name="15817"
      > </a
      ><a name="15818" href="StlcProp.html#15718" class="Bound"
      >&#915;</a
      ><a name="15819"
      > </a
      ><a name="15820" href="Stlc.html#3408" class="Datatype Operator"
      >&#8866;</a
      ><a name="15821"
      > </a
      ><a name="15822" class="Symbol"
      >(</a
      ><a name="15823" href="StlcProp.html#15724" class="Bound"
      >N</a
      ><a name="15824"
      > </a
      ><a name="15825" href="Stlc.html#1297" class="Function Operator"
      >[</a
      ><a name="15826"
      > </a
      ><a name="15827" href="StlcProp.html#15720" class="Bound"
      >x</a
      ><a name="15828"
      > </a
      ><a name="15829" href="Stlc.html#1297" class="Function Operator"
      >&#8758;=</a
      ><a name="15831"
      > </a
      ><a name="15832" href="StlcProp.html#15728" class="Bound"
      >V</a
      ><a name="15833"
      > </a
      ><a name="15834" href="Stlc.html#1297" class="Function Operator"
      >]</a
      ><a name="15835" class="Symbol"
      >)</a
      ><a name="15836"
      > </a
      ><a name="15837" href="Stlc.html#3408" class="Datatype Operator"
      >&#8758;</a
      ><a name="15838"
      > </a
      ><a name="15839" href="StlcProp.html#15726" class="Bound"
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
<a name="18952" href="StlcProp.html#18952" class="Function"
      >weaken-closed</a
      ><a name="18965"
      > </a
      ><a name="18966" class="Symbol"
      >:</a
      ><a name="18967"
      > </a
      ><a name="18968" class="Symbol"
      >&#8704;</a
      ><a name="18969"
      > </a
      ><a name="18970" class="Symbol"
      >{</a
      ><a name="18971" href="StlcProp.html#18971" class="Bound"
      >V</a
      ><a name="18972"
      > </a
      ><a name="18973" href="StlcProp.html#18973" class="Bound"
      >A</a
      ><a name="18974"
      > </a
      ><a name="18975" href="StlcProp.html#18975" class="Bound"
      >&#915;</a
      ><a name="18976" class="Symbol"
      >}</a
      ><a name="18977"
      > </a
      ><a name="18978" class="Symbol"
      >&#8594;</a
      ><a name="18979"
      > </a
      ><a name="18980" href="Maps.html#10359" class="Function"
      >&#8709;</a
      ><a name="18981"
      > </a
      ><a name="18982" href="Stlc.html#3408" class="Datatype Operator"
      >&#8866;</a
      ><a name="18983"
      > </a
      ><a name="18984" href="StlcProp.html#18971" class="Bound"
      >V</a
      ><a name="18985"
      > </a
      ><a name="18986" href="Stlc.html#3408" class="Datatype Operator"
      >&#8758;</a
      ><a name="18987"
      > </a
      ><a name="18988" href="StlcProp.html#18973" class="Bound"
      >A</a
      ><a name="18989"
      > </a
      ><a name="18990" class="Symbol"
      >&#8594;</a
      ><a name="18991"
      > </a
      ><a name="18992" href="StlcProp.html#18975" class="Bound"
      >&#915;</a
      ><a name="18993"
      > </a
      ><a name="18994" href="Stlc.html#3408" class="Datatype Operator"
      >&#8866;</a
      ><a name="18995"
      > </a
      ><a name="18996" href="StlcProp.html#18971" class="Bound"
      >V</a
      ><a name="18997"
      > </a
      ><a name="18998" href="Stlc.html#3408" class="Datatype Operator"
      >&#8758;</a
      ><a name="18999"
      > </a
      ><a name="19000" href="StlcProp.html#18973" class="Bound"
      >A</a
      ><a name="19001"
      >
</a
      ><a name="19002" href="StlcProp.html#18952" class="Function"
      >weaken-closed</a
      ><a name="19015"
      > </a
      ><a name="19016" class="Symbol"
      >{</a
      ><a name="19017" href="StlcProp.html#19017" class="Bound"
      >V</a
      ><a name="19018" class="Symbol"
      >}</a
      ><a name="19019"
      > </a
      ><a name="19020" class="Symbol"
      >{</a
      ><a name="19021" href="StlcProp.html#19021" class="Bound"
      >A</a
      ><a name="19022" class="Symbol"
      >}</a
      ><a name="19023"
      > </a
      ><a name="19024" class="Symbol"
      >{</a
      ><a name="19025" href="StlcProp.html#19025" class="Bound"
      >&#915;</a
      ><a name="19026" class="Symbol"
      >}</a
      ><a name="19027"
      > </a
      ><a name="19028" href="StlcProp.html#19028" class="Bound"
      >&#8866;V</a
      ><a name="19030"
      > </a
      ><a name="19031" class="Symbol"
      >=</a
      ><a name="19032"
      > </a
      ><a name="19033" href="StlcProp.html#11418" class="Function"
      >contextLemma</a
      ><a name="19045"
      > </a
      ><a name="19046" href="StlcProp.html#19064" class="Function"
      >&#915;~&#915;&#8242;</a
      ><a name="19050"
      > </a
      ><a name="19051" href="StlcProp.html#19028" class="Bound"
      >&#8866;V</a
      ><a name="19053"
      >
  </a
      ><a name="19056" class="Keyword"
      >where</a
      ><a name="19061"
      >
  </a
      ><a name="19064" href="StlcProp.html#19064" class="Function"
      >&#915;~&#915;&#8242;</a
      ><a name="19068"
      > </a
      ><a name="19069" class="Symbol"
      >:</a
      ><a name="19070"
      > </a
      ><a name="19071" class="Symbol"
      >&#8704;</a
      ><a name="19072"
      > </a
      ><a name="19073" class="Symbol"
      >{</a
      ><a name="19074" href="StlcProp.html#19074" class="Bound"
      >x</a
      ><a name="19075" class="Symbol"
      >}</a
      ><a name="19076"
      > </a
      ><a name="19077" class="Symbol"
      >&#8594;</a
      ><a name="19078"
      > </a
      ><a name="19079" href="StlcProp.html#19074" class="Bound"
      >x</a
      ><a name="19080"
      > </a
      ><a name="19081" href="StlcProp.html#7096" class="Datatype Operator"
      >&#8712;</a
      ><a name="19082"
      > </a
      ><a name="19083" href="StlcProp.html#19017" class="Bound"
      >V</a
      ><a name="19084"
      > </a
      ><a name="19085" class="Symbol"
      >&#8594;</a
      ><a name="19086"
      > </a
      ><a name="19087" href="Maps.html#10359" class="Function"
      >&#8709;</a
      ><a name="19088"
      > </a
      ><a name="19089" href="StlcProp.html#19074" class="Bound"
      >x</a
      ><a name="19090"
      > </a
      ><a name="19091" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="19092"
      > </a
      ><a name="19093" href="StlcProp.html#19025" class="Bound"
      >&#915;</a
      ><a name="19094"
      > </a
      ><a name="19095" href="StlcProp.html#19074" class="Bound"
      >x</a
      ><a name="19096"
      >
  </a
      ><a name="19099" href="StlcProp.html#19064" class="Function"
      >&#915;~&#915;&#8242;</a
      ><a name="19103"
      > </a
      ><a name="19104" class="Symbol"
      >{</a
      ><a name="19105" href="StlcProp.html#19105" class="Bound"
      >x</a
      ><a name="19106" class="Symbol"
      >}</a
      ><a name="19107"
      > </a
      ><a name="19108" href="StlcProp.html#19108" class="Bound"
      >x&#8712;V</a
      ><a name="19111"
      > </a
      ><a name="19112" class="Symbol"
      >=</a
      ><a name="19113"
      > </a
      ><a name="19114" href="https://agda.github.io/agda-stdlib/Data.Empty.html#348" class="Function"
      >&#8869;-elim</a
      ><a name="19120"
      > </a
      ><a name="19121" class="Symbol"
      >(</a
      ><a name="19122" href="StlcProp.html#19145" class="Function"
      >x&#8713;V</a
      ><a name="19125"
      > </a
      ><a name="19126" href="StlcProp.html#19108" class="Bound"
      >x&#8712;V</a
      ><a name="19129" class="Symbol"
      >)</a
      ><a name="19130"
      >
    </a
      ><a name="19135" class="Keyword"
      >where</a
      ><a name="19140"
      >
    </a
      ><a name="19145" href="StlcProp.html#19145" class="Function"
      >x&#8713;V</a
      ><a name="19148"
      > </a
      ><a name="19149" class="Symbol"
      >:</a
      ><a name="19150"
      > </a
      ><a name="19151" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#414" class="Function Operator"
      >&#172;</a
      ><a name="19152"
      > </a
      ><a name="19153" class="Symbol"
      >(</a
      ><a name="19154" href="StlcProp.html#19105" class="Bound"
      >x</a
      ><a name="19155"
      > </a
      ><a name="19156" href="StlcProp.html#7096" class="Datatype Operator"
      >&#8712;</a
      ><a name="19157"
      > </a
      ><a name="19158" href="StlcProp.html#19017" class="Bound"
      >V</a
      ><a name="19159" class="Symbol"
      >)</a
      ><a name="19160"
      >
    </a
      ><a name="19165" href="StlcProp.html#19145" class="Function"
      >x&#8713;V</a
      ><a name="19168"
      > </a
      ><a name="19169" class="Symbol"
      >=</a
      ><a name="19170"
      > </a
      ><a name="19171" href="StlcProp.html#10717" class="Postulate"
      >&#8709;&#8866;-closed</a
      ><a name="19180"
      > </a
      ><a name="19181" href="StlcProp.html#19028" class="Bound"
      >&#8866;V</a
      ><a name="19183"
      > </a
      ><a name="19184" class="Symbol"
      >{</a
      ><a name="19185" href="StlcProp.html#19105" class="Bound"
      >x</a
      ><a name="19186" class="Symbol"
      >}</a
      ><a name="19187"
      >

</a
      ><a name="19189" href="StlcProp.html#19189" class="Function"
      >just-injective</a
      ><a name="19203"
      > </a
      ><a name="19204" class="Symbol"
      >:</a
      ><a name="19205"
      > </a
      ><a name="19206" class="Symbol"
      >&#8704;</a
      ><a name="19207"
      > </a
      ><a name="19208" class="Symbol"
      >{</a
      ><a name="19209" href="StlcProp.html#19209" class="Bound"
      >X</a
      ><a name="19210"
      > </a
      ><a name="19211" class="Symbol"
      >:</a
      ><a name="19212"
      > </a
      ><a name="19213" class="PrimitiveType"
      >Set</a
      ><a name="19216" class="Symbol"
      >}</a
      ><a name="19217"
      > </a
      ><a name="19218" class="Symbol"
      >{</a
      ><a name="19219" href="StlcProp.html#19219" class="Bound"
      >x</a
      ><a name="19220"
      > </a
      ><a name="19221" href="StlcProp.html#19221" class="Bound"
      >y</a
      ><a name="19222"
      > </a
      ><a name="19223" class="Symbol"
      >:</a
      ><a name="19224"
      > </a
      ><a name="19225" href="StlcProp.html#19209" class="Bound"
      >X</a
      ><a name="19226" class="Symbol"
      >}</a
      ><a name="19227"
      > </a
      ><a name="19228" class="Symbol"
      >&#8594;</a
      ><a name="19229"
      > </a
      ><a name="19230" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >_&#8801;_</a
      ><a name="19233"
      > </a
      ><a name="19234" class="Symbol"
      >{</a
      ><a name="19235" class="Argument"
      >A</a
      ><a name="19236"
      > </a
      ><a name="19237" class="Symbol"
      >=</a
      ><a name="19238"
      > </a
      ><a name="19239" href="https://agda.github.io/agda-stdlib/Data.Maybe.Base.html#335" class="Datatype"
      >Maybe</a
      ><a name="19244"
      > </a
      ><a name="19245" href="StlcProp.html#19209" class="Bound"
      >X</a
      ><a name="19246" class="Symbol"
      >}</a
      ><a name="19247"
      > </a
      ><a name="19248" class="Symbol"
      >(</a
      ><a name="19249" href="https://agda.github.io/agda-stdlib/Data.Maybe.Base.html#373" class="InductiveConstructor"
      >just</a
      ><a name="19253"
      > </a
      ><a name="19254" href="StlcProp.html#19219" class="Bound"
      >x</a
      ><a name="19255" class="Symbol"
      >)</a
      ><a name="19256"
      > </a
      ><a name="19257" class="Symbol"
      >(</a
      ><a name="19258" href="https://agda.github.io/agda-stdlib/Data.Maybe.Base.html#373" class="InductiveConstructor"
      >just</a
      ><a name="19262"
      > </a
      ><a name="19263" href="StlcProp.html#19221" class="Bound"
      >y</a
      ><a name="19264" class="Symbol"
      >)</a
      ><a name="19265"
      > </a
      ><a name="19266" class="Symbol"
      >&#8594;</a
      ><a name="19267"
      > </a
      ><a name="19268" href="StlcProp.html#19219" class="Bound"
      >x</a
      ><a name="19269"
      > </a
      ><a name="19270" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="19271"
      > </a
      ><a name="19272" href="StlcProp.html#19221" class="Bound"
      >y</a
      ><a name="19273"
      >
</a
      ><a name="19274" href="StlcProp.html#19189" class="Function"
      >just-injective</a
      ><a name="19288"
      > </a
      ><a name="19289" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="19293"
      > </a
      ><a name="19294" class="Symbol"
      >=</a
      ><a name="19295"
      > </a
      ><a name="19296" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      >
{% endraw %}</pre>

<pre class="Agda">{% raw %}
<a name="19326" href="StlcProp.html#15695" class="Function"
      >preservation-[&#8758;=]</a
      ><a name="19343"
      > </a
      ><a name="19344" class="Symbol"
      >{_}</a
      ><a name="19347"
      > </a
      ><a name="19348" class="Symbol"
      >{</a
      ><a name="19349" href="StlcProp.html#19349" class="Bound"
      >x</a
      ><a name="19350" class="Symbol"
      >}</a
      ><a name="19351"
      > </a
      ><a name="19352" class="Symbol"
      >(</a
      ><a name="19353" href="Stlc.html#3452" class="InductiveConstructor"
      >Ax</a
      ><a name="19355"
      > </a
      ><a name="19356" class="Symbol"
      >{_}</a
      ><a name="19359"
      > </a
      ><a name="19360" class="Symbol"
      >{</a
      ><a name="19361" href="StlcProp.html#19361" class="Bound"
      >x&#8242;</a
      ><a name="19363" class="Symbol"
      >}</a
      ><a name="19364"
      > </a
      ><a name="19365" href="StlcProp.html#19365" class="Bound"
      >[&#915;,x&#8758;A]x&#8242;&#8801;B</a
      ><a name="19376" class="Symbol"
      >)</a
      ><a name="19377"
      > </a
      ><a name="19378" href="StlcProp.html#19378" class="Bound"
      >&#8866;V</a
      ><a name="19380"
      > </a
      ><a name="19381" class="Keyword"
      >with</a
      ><a name="19385"
      > </a
      ><a name="19386" href="StlcProp.html#19349" class="Bound"
      >x</a
      ><a name="19387"
      > </a
      ><a name="19388" href="Maps.html#2558" class="Function Operator"
      >&#8799;</a
      ><a name="19389"
      > </a
      ><a name="19390" href="StlcProp.html#19361" class="Bound"
      >x&#8242;</a
      ><a name="19392"
      >
</a
      ><a name="19393" class="Symbol"
      >...|</a
      ><a name="19397"
      > </a
      ><a name="19398" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#520" class="InductiveConstructor"
      >yes</a
      ><a name="19401"
      > </a
      ><a name="19402" href="StlcProp.html#19402" class="Bound"
      >x&#8801;x&#8242;</a
      ><a name="19406"
      > </a
      ><a name="19407" class="Keyword"
      >rewrite</a
      ><a name="19414"
      > </a
      ><a name="19415" href="StlcProp.html#19189" class="Function"
      >just-injective</a
      ><a name="19429"
      > </a
      ><a name="19430" href="StlcProp.html#19365" class="Bound"
      >[&#915;,x&#8758;A]x&#8242;&#8801;B</a
      ><a name="19441"
      >  </a
      ><a name="19443" class="Symbol"
      >=</a
      ><a name="19444"
      >  </a
      ><a name="19446" href="StlcProp.html#18952" class="Function"
      >weaken-closed</a
      ><a name="19459"
      > </a
      ><a name="19460" href="StlcProp.html#19378" class="Bound"
      >&#8866;V</a
      ><a name="19462"
      >
</a
      ><a name="19463" class="Symbol"
      >...|</a
      ><a name="19467"
      > </a
      ><a name="19468" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#547" class="InductiveConstructor"
      >no</a
      ><a name="19470"
      >  </a
      ><a name="19472" href="StlcProp.html#19472" class="Bound"
      >x&#8802;x&#8242;</a
      ><a name="19476"
      >  </a
      ><a name="19478" class="Symbol"
      >=</a
      ><a name="19479"
      >  </a
      ><a name="19481" href="Stlc.html#3452" class="InductiveConstructor"
      >Ax</a
      ><a name="19483"
      > </a
      ><a name="19484" href="StlcProp.html#19365" class="Bound"
      >[&#915;,x&#8758;A]x&#8242;&#8801;B</a
      ><a name="19495"
      >
</a
      ><a name="19496" href="StlcProp.html#15695" class="Function"
      >preservation-[&#8758;=]</a
      ><a name="19513"
      > </a
      ><a name="19514" class="Symbol"
      >{</a
      ><a name="19515" href="StlcProp.html#19515" class="Bound"
      >&#915;</a
      ><a name="19516" class="Symbol"
      >}</a
      ><a name="19517"
      > </a
      ><a name="19518" class="Symbol"
      >{</a
      ><a name="19519" href="StlcProp.html#19519" class="Bound"
      >x</a
      ><a name="19520" class="Symbol"
      >}</a
      ><a name="19521"
      > </a
      ><a name="19522" class="Symbol"
      >{</a
      ><a name="19523" href="StlcProp.html#19523" class="Bound"
      >A</a
      ><a name="19524" class="Symbol"
      >}</a
      ><a name="19525"
      > </a
      ><a name="19526" class="Symbol"
      >{</a
      ><a name="19527" href="Stlc.html#752" class="InductiveConstructor Operator"
      >&#955;[</a
      ><a name="19529"
      > </a
      ><a name="19530" href="StlcProp.html#19530" class="Bound"
      >x&#8242;</a
      ><a name="19532"
      > </a
      ><a name="19533" href="Stlc.html#752" class="InductiveConstructor Operator"
      >&#8758;</a
      ><a name="19534"
      > </a
      ><a name="19535" href="StlcProp.html#19535" class="Bound"
      >A&#8242;</a
      ><a name="19537"
      > </a
      ><a name="19538" href="Stlc.html#752" class="InductiveConstructor Operator"
      >]</a
      ><a name="19539"
      > </a
      ><a name="19540" href="StlcProp.html#19540" class="Bound"
      >N&#8242;</a
      ><a name="19542" class="Symbol"
      >}</a
      ><a name="19543"
      > </a
      ><a name="19544" class="Symbol"
      >{</a
      ><a name="19545" class="DottedPattern Symbol"
      >.</a
      ><a name="19546" href="StlcProp.html#19535" class="DottedPattern Bound"
      >A&#8242;</a
      ><a name="19548"
      > </a
      ><a name="19549" href="Stlc.html#627" class="InductiveConstructor Operator"
      >&#8658;</a
      ><a name="19550"
      > </a
      ><a name="19551" href="StlcProp.html#19551" class="Bound"
      >B&#8242;</a
      ><a name="19553" class="Symbol"
      >}</a
      ><a name="19554"
      > </a
      ><a name="19555" class="Symbol"
      >{</a
      ><a name="19556" href="StlcProp.html#19556" class="Bound"
      >V</a
      ><a name="19557" class="Symbol"
      >}</a
      ><a name="19558"
      > </a
      ><a name="19559" class="Symbol"
      >(</a
      ><a name="19560" href="Stlc.html#3508" class="InductiveConstructor"
      >&#8658;-I</a
      ><a name="19563"
      > </a
      ><a name="19564" href="StlcProp.html#19564" class="Bound"
      >&#8866;N&#8242;</a
      ><a name="19567" class="Symbol"
      >)</a
      ><a name="19568"
      > </a
      ><a name="19569" href="StlcProp.html#19569" class="Bound"
      >&#8866;V</a
      ><a name="19571"
      > </a
      ><a name="19572" class="Keyword"
      >with</a
      ><a name="19576"
      > </a
      ><a name="19577" href="StlcProp.html#19519" class="Bound"
      >x</a
      ><a name="19578"
      > </a
      ><a name="19579" href="Maps.html#2558" class="Function Operator"
      >&#8799;</a
      ><a name="19580"
      > </a
      ><a name="19581" href="StlcProp.html#19530" class="Bound"
      >x&#8242;</a
      ><a name="19583"
      >
</a
      ><a name="19584" class="Symbol"
      >...|</a
      ><a name="19588"
      > </a
      ><a name="19589" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#520" class="InductiveConstructor"
      >yes</a
      ><a name="19592"
      > </a
      ><a name="19593" href="StlcProp.html#19593" class="Bound"
      >x&#8801;x&#8242;</a
      ><a name="19597"
      > </a
      ><a name="19598" class="Keyword"
      >rewrite</a
      ><a name="19605"
      > </a
      ><a name="19606" href="StlcProp.html#19593" class="Bound"
      >x&#8801;x&#8242;</a
      ><a name="19610"
      > </a
      ><a name="19611" class="Symbol"
      >=</a
      ><a name="19612"
      > </a
      ><a name="19613" href="StlcProp.html#11418" class="Function"
      >contextLemma</a
      ><a name="19625"
      > </a
      ><a name="19626" href="StlcProp.html#19651" class="Function"
      >&#915;&#8242;~&#915;</a
      ><a name="19630"
      > </a
      ><a name="19631" class="Symbol"
      >(</a
      ><a name="19632" href="Stlc.html#3508" class="InductiveConstructor"
      >&#8658;-I</a
      ><a name="19635"
      > </a
      ><a name="19636" href="StlcProp.html#19564" class="Bound"
      >&#8866;N&#8242;</a
      ><a name="19639" class="Symbol"
      >)</a
      ><a name="19640"
      >
  </a
      ><a name="19643" class="Keyword"
      >where</a
      ><a name="19648"
      >
  </a
      ><a name="19651" href="StlcProp.html#19651" class="Function"
      >&#915;&#8242;~&#915;</a
      ><a name="19655"
      > </a
      ><a name="19656" class="Symbol"
      >:</a
      ><a name="19657"
      > </a
      ><a name="19658" class="Symbol"
      >&#8704;</a
      ><a name="19659"
      > </a
      ><a name="19660" class="Symbol"
      >{</a
      ><a name="19661" href="StlcProp.html#19661" class="Bound"
      >y</a
      ><a name="19662" class="Symbol"
      >}</a
      ><a name="19663"
      > </a
      ><a name="19664" class="Symbol"
      >&#8594;</a
      ><a name="19665"
      > </a
      ><a name="19666" href="StlcProp.html#19661" class="Bound"
      >y</a
      ><a name="19667"
      > </a
      ><a name="19668" href="StlcProp.html#7096" class="Datatype Operator"
      >&#8712;</a
      ><a name="19669"
      > </a
      ><a name="19670" class="Symbol"
      >(</a
      ><a name="19671" href="Stlc.html#752" class="InductiveConstructor Operator"
      >&#955;[</a
      ><a name="19673"
      > </a
      ><a name="19674" href="StlcProp.html#19530" class="Bound"
      >x&#8242;</a
      ><a name="19676"
      > </a
      ><a name="19677" href="Stlc.html#752" class="InductiveConstructor Operator"
      >&#8758;</a
      ><a name="19678"
      > </a
      ><a name="19679" href="StlcProp.html#19535" class="Bound"
      >A&#8242;</a
      ><a name="19681"
      > </a
      ><a name="19682" href="Stlc.html#752" class="InductiveConstructor Operator"
      >]</a
      ><a name="19683"
      > </a
      ><a name="19684" href="StlcProp.html#19540" class="Bound"
      >N&#8242;</a
      ><a name="19686" class="Symbol"
      >)</a
      ><a name="19687"
      > </a
      ><a name="19688" class="Symbol"
      >&#8594;</a
      ><a name="19689"
      > </a
      ><a name="19690" class="Symbol"
      >(</a
      ><a name="19691" href="StlcProp.html#19515" class="Bound"
      >&#915;</a
      ><a name="19692"
      > </a
      ><a name="19693" href="Maps.html#10462" class="Function Operator"
      >,</a
      ><a name="19694"
      > </a
      ><a name="19695" href="StlcProp.html#19530" class="Bound"
      >x&#8242;</a
      ><a name="19697"
      > </a
      ><a name="19698" href="Maps.html#10462" class="Function Operator"
      >&#8758;</a
      ><a name="19699"
      > </a
      ><a name="19700" href="StlcProp.html#19523" class="Bound"
      >A</a
      ><a name="19701" class="Symbol"
      >)</a
      ><a name="19702"
      > </a
      ><a name="19703" href="StlcProp.html#19661" class="Bound"
      >y</a
      ><a name="19704"
      > </a
      ><a name="19705" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="19706"
      > </a
      ><a name="19707" href="StlcProp.html#19515" class="Bound"
      >&#915;</a
      ><a name="19708"
      > </a
      ><a name="19709" href="StlcProp.html#19661" class="Bound"
      >y</a
      ><a name="19710"
      >
  </a
      ><a name="19713" href="StlcProp.html#19651" class="Function"
      >&#915;&#8242;~&#915;</a
      ><a name="19717"
      > </a
      ><a name="19718" class="Symbol"
      >{</a
      ><a name="19719" href="StlcProp.html#19719" class="Bound"
      >y</a
      ><a name="19720" class="Symbol"
      >}</a
      ><a name="19721"
      > </a
      ><a name="19722" class="Symbol"
      >(</a
      ><a name="19723" href="StlcProp.html#7160" class="InductiveConstructor"
      >free-&#955;</a
      ><a name="19729"
      > </a
      ><a name="19730" href="StlcProp.html#19730" class="Bound"
      >x&#8242;&#8802;y</a
      ><a name="19734"
      > </a
      ><a name="19735" href="StlcProp.html#19735" class="Bound"
      >y&#8712;N&#8242;</a
      ><a name="19739" class="Symbol"
      >)</a
      ><a name="19740"
      > </a
      ><a name="19741" class="Keyword"
      >with</a
      ><a name="19745"
      > </a
      ><a name="19746" href="StlcProp.html#19530" class="Bound"
      >x&#8242;</a
      ><a name="19748"
      > </a
      ><a name="19749" href="Maps.html#2558" class="Function Operator"
      >&#8799;</a
      ><a name="19750"
      > </a
      ><a name="19751" href="StlcProp.html#19719" class="Bound"
      >y</a
      ><a name="19752"
      >
  </a
      ><a name="19755" class="Symbol"
      >...|</a
      ><a name="19759"
      > </a
      ><a name="19760" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#520" class="InductiveConstructor"
      >yes</a
      ><a name="19763"
      > </a
      ><a name="19764" href="StlcProp.html#19764" class="Bound"
      >x&#8242;&#8801;y</a
      ><a name="19768"
      >  </a
      ><a name="19770" class="Symbol"
      >=</a
      ><a name="19771"
      > </a
      ><a name="19772" href="https://agda.github.io/agda-stdlib/Data.Empty.html#348" class="Function"
      >&#8869;-elim</a
      ><a name="19778"
      > </a
      ><a name="19779" class="Symbol"
      >(</a
      ><a name="19780" href="StlcProp.html#19730" class="Bound"
      >x&#8242;&#8802;y</a
      ><a name="19784"
      > </a
      ><a name="19785" href="StlcProp.html#19764" class="Bound"
      >x&#8242;&#8801;y</a
      ><a name="19789" class="Symbol"
      >)</a
      ><a name="19790"
      >
  </a
      ><a name="19793" class="Symbol"
      >...|</a
      ><a name="19797"
      > </a
      ><a name="19798" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#547" class="InductiveConstructor"
      >no</a
      ><a name="19800"
      >  </a
      ><a name="19802" class="Symbol"
      >_</a
      ><a name="19803"
      >     </a
      ><a name="19808" class="Symbol"
      >=</a
      ><a name="19809"
      > </a
      ><a name="19810" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="19814"
      >
</a
      ><a name="19815" class="Symbol"
      >...|</a
      ><a name="19819"
      > </a
      ><a name="19820" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#547" class="InductiveConstructor"
      >no</a
      ><a name="19822"
      >  </a
      ><a name="19824" href="StlcProp.html#19824" class="Bound"
      >x&#8802;x&#8242;</a
      ><a name="19828"
      > </a
      ><a name="19829" class="Symbol"
      >=</a
      ><a name="19830"
      > </a
      ><a name="19831" href="Stlc.html#3508" class="InductiveConstructor"
      >&#8658;-I</a
      ><a name="19834"
      > </a
      ><a name="19835" href="StlcProp.html#19946" class="Function"
      >&#8866;N&#8242;V</a
      ><a name="19839"
      >
  </a
      ><a name="19842" class="Keyword"
      >where</a
      ><a name="19847"
      >
  </a
      ><a name="19850" href="StlcProp.html#19850" class="Function"
      >x&#8242;x&#8866;N&#8242;</a
      ><a name="19856"
      > </a
      ><a name="19857" class="Symbol"
      >:</a
      ><a name="19858"
      > </a
      ><a name="19859" href="StlcProp.html#19515" class="Bound"
      >&#915;</a
      ><a name="19860"
      > </a
      ><a name="19861" href="Maps.html#10462" class="Function Operator"
      >,</a
      ><a name="19862"
      > </a
      ><a name="19863" href="StlcProp.html#19530" class="Bound"
      >x&#8242;</a
      ><a name="19865"
      > </a
      ><a name="19866" href="Maps.html#10462" class="Function Operator"
      >&#8758;</a
      ><a name="19867"
      > </a
      ><a name="19868" href="StlcProp.html#19535" class="Bound"
      >A&#8242;</a
      ><a name="19870"
      > </a
      ><a name="19871" href="Maps.html#10462" class="Function Operator"
      >,</a
      ><a name="19872"
      > </a
      ><a name="19873" href="StlcProp.html#19519" class="Bound"
      >x</a
      ><a name="19874"
      > </a
      ><a name="19875" href="Maps.html#10462" class="Function Operator"
      >&#8758;</a
      ><a name="19876"
      > </a
      ><a name="19877" href="StlcProp.html#19523" class="Bound"
      >A</a
      ><a name="19878"
      > </a
      ><a name="19879" href="Stlc.html#3408" class="Datatype Operator"
      >&#8866;</a
      ><a name="19880"
      > </a
      ><a name="19881" href="StlcProp.html#19540" class="Bound"
      >N&#8242;</a
      ><a name="19883"
      > </a
      ><a name="19884" href="Stlc.html#3408" class="Datatype Operator"
      >&#8758;</a
      ><a name="19885"
      > </a
      ><a name="19886" href="StlcProp.html#19551" class="Bound"
      >B&#8242;</a
      ><a name="19888"
      >
  </a
      ><a name="19891" href="StlcProp.html#19850" class="Function"
      >x&#8242;x&#8866;N&#8242;</a
      ><a name="19897"
      > </a
      ><a name="19898" class="Keyword"
      >rewrite</a
      ><a name="19905"
      > </a
      ><a name="19906" href="Maps.html#11585" class="Function"
      >update-permute</a
      ><a name="19920"
      > </a
      ><a name="19921" href="StlcProp.html#19515" class="Bound"
      >&#915;</a
      ><a name="19922"
      > </a
      ><a name="19923" href="StlcProp.html#19519" class="Bound"
      >x</a
      ><a name="19924"
      > </a
      ><a name="19925" href="StlcProp.html#19523" class="Bound"
      >A</a
      ><a name="19926"
      > </a
      ><a name="19927" href="StlcProp.html#19530" class="Bound"
      >x&#8242;</a
      ><a name="19929"
      > </a
      ><a name="19930" href="StlcProp.html#19535" class="Bound"
      >A&#8242;</a
      ><a name="19932"
      > </a
      ><a name="19933" href="StlcProp.html#19824" class="Bound"
      >x&#8802;x&#8242;</a
      ><a name="19937"
      > </a
      ><a name="19938" class="Symbol"
      >=</a
      ><a name="19939"
      > </a
      ><a name="19940" href="StlcProp.html#19564" class="Bound"
      >&#8866;N&#8242;</a
      ><a name="19943"
      >
  </a
      ><a name="19946" href="StlcProp.html#19946" class="Function"
      >&#8866;N&#8242;V</a
      ><a name="19950"
      > </a
      ><a name="19951" class="Symbol"
      >:</a
      ><a name="19952"
      > </a
      ><a name="19953" class="Symbol"
      >(</a
      ><a name="19954" href="StlcProp.html#19515" class="Bound"
      >&#915;</a
      ><a name="19955"
      > </a
      ><a name="19956" href="Maps.html#10462" class="Function Operator"
      >,</a
      ><a name="19957"
      > </a
      ><a name="19958" href="StlcProp.html#19530" class="Bound"
      >x&#8242;</a
      ><a name="19960"
      > </a
      ><a name="19961" href="Maps.html#10462" class="Function Operator"
      >&#8758;</a
      ><a name="19962"
      > </a
      ><a name="19963" href="StlcProp.html#19535" class="Bound"
      >A&#8242;</a
      ><a name="19965" class="Symbol"
      >)</a
      ><a name="19966"
      > </a
      ><a name="19967" href="Stlc.html#3408" class="Datatype Operator"
      >&#8866;</a
      ><a name="19968"
      > </a
      ><a name="19969" href="StlcProp.html#19540" class="Bound"
      >N&#8242;</a
      ><a name="19971"
      > </a
      ><a name="19972" href="Stlc.html#1297" class="Function Operator"
      >[</a
      ><a name="19973"
      > </a
      ><a name="19974" href="StlcProp.html#19519" class="Bound"
      >x</a
      ><a name="19975"
      > </a
      ><a name="19976" href="Stlc.html#1297" class="Function Operator"
      >&#8758;=</a
      ><a name="19978"
      > </a
      ><a name="19979" href="StlcProp.html#19556" class="Bound"
      >V</a
      ><a name="19980"
      > </a
      ><a name="19981" href="Stlc.html#1297" class="Function Operator"
      >]</a
      ><a name="19982"
      > </a
      ><a name="19983" href="Stlc.html#3408" class="Datatype Operator"
      >&#8758;</a
      ><a name="19984"
      > </a
      ><a name="19985" href="StlcProp.html#19551" class="Bound"
      >B&#8242;</a
      ><a name="19987"
      >
  </a
      ><a name="19990" href="StlcProp.html#19946" class="Function"
      >&#8866;N&#8242;V</a
      ><a name="19994"
      > </a
      ><a name="19995" class="Symbol"
      >=</a
      ><a name="19996"
      > </a
      ><a name="19997" href="StlcProp.html#15695" class="Function"
      >preservation-[&#8758;=]</a
      ><a name="20014"
      > </a
      ><a name="20015" href="StlcProp.html#19850" class="Function"
      >x&#8242;x&#8866;N&#8242;</a
      ><a name="20021"
      > </a
      ><a name="20022" href="StlcProp.html#19569" class="Bound"
      >&#8866;V</a
      ><a name="20024"
      >
</a
      ><a name="20025" href="StlcProp.html#15695" class="Function"
      >preservation-[&#8758;=]</a
      ><a name="20042"
      > </a
      ><a name="20043" class="Symbol"
      >(</a
      ><a name="20044" href="Stlc.html#3585" class="InductiveConstructor"
      >&#8658;-E</a
      ><a name="20047"
      > </a
      ><a name="20048" href="StlcProp.html#20048" class="Bound"
      >&#8866;L</a
      ><a name="20050"
      > </a
      ><a name="20051" href="StlcProp.html#20051" class="Bound"
      >&#8866;M</a
      ><a name="20053" class="Symbol"
      >)</a
      ><a name="20054"
      > </a
      ><a name="20055" href="StlcProp.html#20055" class="Bound"
      >&#8866;V</a
      ><a name="20057"
      > </a
      ><a name="20058" class="Symbol"
      >=</a
      ><a name="20059"
      > </a
      ><a name="20060" href="Stlc.html#3585" class="InductiveConstructor"
      >&#8658;-E</a
      ><a name="20063"
      > </a
      ><a name="20064" class="Symbol"
      >(</a
      ><a name="20065" href="StlcProp.html#15695" class="Function"
      >preservation-[&#8758;=]</a
      ><a name="20082"
      > </a
      ><a name="20083" href="StlcProp.html#20048" class="Bound"
      >&#8866;L</a
      ><a name="20085"
      > </a
      ><a name="20086" href="StlcProp.html#20055" class="Bound"
      >&#8866;V</a
      ><a name="20088" class="Symbol"
      >)</a
      ><a name="20089"
      > </a
      ><a name="20090" class="Symbol"
      >(</a
      ><a name="20091" href="StlcProp.html#15695" class="Function"
      >preservation-[&#8758;=]</a
      ><a name="20108"
      > </a
      ><a name="20109" href="StlcProp.html#20051" class="Bound"
      >&#8866;M</a
      ><a name="20111"
      > </a
      ><a name="20112" href="StlcProp.html#20055" class="Bound"
      >&#8866;V</a
      ><a name="20114" class="Symbol"
      >)</a
      ><a name="20115"
      >
</a
      ><a name="20116" href="StlcProp.html#15695" class="Function"
      >preservation-[&#8758;=]</a
      ><a name="20133"
      > </a
      ><a name="20134" href="Stlc.html#3663" class="InductiveConstructor"
      >&#120121;-I&#8321;</a
      ><a name="20138"
      > </a
      ><a name="20139" href="StlcProp.html#20139" class="Bound"
      >&#8866;V</a
      ><a name="20141"
      > </a
      ><a name="20142" class="Symbol"
      >=</a
      ><a name="20143"
      > </a
      ><a name="20144" href="Stlc.html#3663" class="InductiveConstructor"
      >&#120121;-I&#8321;</a
      ><a name="20148"
      >
</a
      ><a name="20149" href="StlcProp.html#15695" class="Function"
      >preservation-[&#8758;=]</a
      ><a name="20166"
      > </a
      ><a name="20167" href="Stlc.html#3697" class="InductiveConstructor"
      >&#120121;-I&#8322;</a
      ><a name="20171"
      > </a
      ><a name="20172" href="StlcProp.html#20172" class="Bound"
      >&#8866;V</a
      ><a name="20174"
      > </a
      ><a name="20175" class="Symbol"
      >=</a
      ><a name="20176"
      > </a
      ><a name="20177" href="Stlc.html#3697" class="InductiveConstructor"
      >&#120121;-I&#8322;</a
      ><a name="20181"
      >
</a
      ><a name="20182" href="StlcProp.html#15695" class="Function"
      >preservation-[&#8758;=]</a
      ><a name="20199"
      > </a
      ><a name="20200" class="Symbol"
      >(</a
      ><a name="20201" href="Stlc.html#3732" class="InductiveConstructor"
      >&#120121;-E</a
      ><a name="20204"
      > </a
      ><a name="20205" href="StlcProp.html#20205" class="Bound"
      >&#8866;L</a
      ><a name="20207"
      > </a
      ><a name="20208" href="StlcProp.html#20208" class="Bound"
      >&#8866;M</a
      ><a name="20210"
      > </a
      ><a name="20211" href="StlcProp.html#20211" class="Bound"
      >&#8866;N</a
      ><a name="20213" class="Symbol"
      >)</a
      ><a name="20214"
      > </a
      ><a name="20215" href="StlcProp.html#20215" class="Bound"
      >&#8866;V</a
      ><a name="20217"
      > </a
      ><a name="20218" class="Symbol"
      >=</a
      ><a name="20219"
      >
  </a
      ><a name="20222" href="Stlc.html#3732" class="InductiveConstructor"
      >&#120121;-E</a
      ><a name="20225"
      > </a
      ><a name="20226" class="Symbol"
      >(</a
      ><a name="20227" href="StlcProp.html#15695" class="Function"
      >preservation-[&#8758;=]</a
      ><a name="20244"
      > </a
      ><a name="20245" href="StlcProp.html#20205" class="Bound"
      >&#8866;L</a
      ><a name="20247"
      > </a
      ><a name="20248" href="StlcProp.html#20215" class="Bound"
      >&#8866;V</a
      ><a name="20250" class="Symbol"
      >)</a
      ><a name="20251"
      > </a
      ><a name="20252" class="Symbol"
      >(</a
      ><a name="20253" href="StlcProp.html#15695" class="Function"
      >preservation-[&#8758;=]</a
      ><a name="20270"
      > </a
      ><a name="20271" href="StlcProp.html#20208" class="Bound"
      >&#8866;M</a
      ><a name="20273"
      > </a
      ><a name="20274" href="StlcProp.html#20215" class="Bound"
      >&#8866;V</a
      ><a name="20276" class="Symbol"
      >)</a
      ><a name="20277"
      > </a
      ><a name="20278" class="Symbol"
      >(</a
      ><a name="20279" href="StlcProp.html#15695" class="Function"
      >preservation-[&#8758;=]</a
      ><a name="20296"
      > </a
      ><a name="20297" href="StlcProp.html#20211" class="Bound"
      >&#8866;N</a
      ><a name="20299"
      > </a
      ><a name="20300" href="StlcProp.html#20215" class="Bound"
      >&#8866;V</a
      ><a name="20302" class="Symbol"
      >)</a
      >
{% endraw %}</pre>


### Main Theorem

We now have the tools we need to prove preservation: if a closed
term `M` has type `A` and takes a step to `N`, then `N`
is also a closed term with type `A`.  In other words, small-step
reduction preserves types.

<pre class="Agda">{% raw %}
<a name="20562" href="StlcProp.html#20562" class="Function"
      >preservation</a
      ><a name="20574"
      > </a
      ><a name="20575" class="Symbol"
      >:</a
      ><a name="20576"
      > </a
      ><a name="20577" class="Symbol"
      >&#8704;</a
      ><a name="20578"
      > </a
      ><a name="20579" class="Symbol"
      >{</a
      ><a name="20580" href="StlcProp.html#20580" class="Bound"
      >M</a
      ><a name="20581"
      > </a
      ><a name="20582" href="StlcProp.html#20582" class="Bound"
      >N</a
      ><a name="20583"
      > </a
      ><a name="20584" href="StlcProp.html#20584" class="Bound"
      >A</a
      ><a name="20585" class="Symbol"
      >}</a
      ><a name="20586"
      > </a
      ><a name="20587" class="Symbol"
      >&#8594;</a
      ><a name="20588"
      > </a
      ><a name="20589" href="Maps.html#10359" class="Function"
      >&#8709;</a
      ><a name="20590"
      > </a
      ><a name="20591" href="Stlc.html#3408" class="Datatype Operator"
      >&#8866;</a
      ><a name="20592"
      > </a
      ><a name="20593" href="StlcProp.html#20580" class="Bound"
      >M</a
      ><a name="20594"
      > </a
      ><a name="20595" href="Stlc.html#3408" class="Datatype Operator"
      >&#8758;</a
      ><a name="20596"
      > </a
      ><a name="20597" href="StlcProp.html#20584" class="Bound"
      >A</a
      ><a name="20598"
      > </a
      ><a name="20599" class="Symbol"
      >&#8594;</a
      ><a name="20600"
      > </a
      ><a name="20601" href="StlcProp.html#20580" class="Bound"
      >M</a
      ><a name="20602"
      > </a
      ><a name="20603" href="Stlc.html#1787" class="Datatype Operator"
      >&#10233;</a
      ><a name="20604"
      > </a
      ><a name="20605" href="StlcProp.html#20582" class="Bound"
      >N</a
      ><a name="20606"
      > </a
      ><a name="20607" class="Symbol"
      >&#8594;</a
      ><a name="20608"
      > </a
      ><a name="20609" href="Maps.html#10359" class="Function"
      >&#8709;</a
      ><a name="20610"
      > </a
      ><a name="20611" href="Stlc.html#3408" class="Datatype Operator"
      >&#8866;</a
      ><a name="20612"
      > </a
      ><a name="20613" href="StlcProp.html#20582" class="Bound"
      >N</a
      ><a name="20614"
      > </a
      ><a name="20615" href="Stlc.html#3408" class="Datatype Operator"
      >&#8758;</a
      ><a name="20616"
      > </a
      ><a name="20617" href="StlcProp.html#20584" class="Bound"
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
<a name="21912" href="StlcProp.html#20562" class="Function"
      >preservation</a
      ><a name="21924"
      > </a
      ><a name="21925" class="Symbol"
      >(</a
      ><a name="21926" href="Stlc.html#3452" class="InductiveConstructor"
      >Ax</a
      ><a name="21928"
      > </a
      ><a name="21929" href="StlcProp.html#21929" class="Bound"
      >x&#8321;</a
      ><a name="21931" class="Symbol"
      >)</a
      ><a name="21932"
      > </a
      ><a name="21933" class="Symbol"
      >()</a
      ><a name="21935"
      >
</a
      ><a name="21936" href="StlcProp.html#20562" class="Function"
      >preservation</a
      ><a name="21948"
      > </a
      ><a name="21949" class="Symbol"
      >(</a
      ><a name="21950" href="Stlc.html#3508" class="InductiveConstructor"
      >&#8658;-I</a
      ><a name="21953"
      > </a
      ><a name="21954" href="StlcProp.html#21954" class="Bound"
      >&#8866;N</a
      ><a name="21956" class="Symbol"
      >)</a
      ><a name="21957"
      > </a
      ><a name="21958" class="Symbol"
      >()</a
      ><a name="21960"
      >
</a
      ><a name="21961" href="StlcProp.html#20562" class="Function"
      >preservation</a
      ><a name="21973"
      > </a
      ><a name="21974" class="Symbol"
      >(</a
      ><a name="21975" href="Stlc.html#3585" class="InductiveConstructor"
      >&#8658;-E</a
      ><a name="21978"
      > </a
      ><a name="21979" class="Symbol"
      >(</a
      ><a name="21980" href="Stlc.html#3508" class="InductiveConstructor"
      >&#8658;-I</a
      ><a name="21983"
      > </a
      ><a name="21984" href="StlcProp.html#21984" class="Bound"
      >&#8866;N</a
      ><a name="21986" class="Symbol"
      >)</a
      ><a name="21987"
      > </a
      ><a name="21988" href="StlcProp.html#21988" class="Bound"
      >&#8866;V</a
      ><a name="21990" class="Symbol"
      >)</a
      ><a name="21991"
      > </a
      ><a name="21992" class="Symbol"
      >(</a
      ><a name="21993" href="Stlc.html#1819" class="InductiveConstructor"
      >&#946;&#8658;</a
      ><a name="21995"
      > </a
      ><a name="21996" href="StlcProp.html#21996" class="Bound"
      >valueV</a
      ><a name="22002" class="Symbol"
      >)</a
      ><a name="22003"
      > </a
      ><a name="22004" class="Symbol"
      >=</a
      ><a name="22005"
      > </a
      ><a name="22006" href="StlcProp.html#15695" class="Function"
      >preservation-[&#8758;=]</a
      ><a name="22023"
      > </a
      ><a name="22024" href="StlcProp.html#21984" class="Bound"
      >&#8866;N</a
      ><a name="22026"
      > </a
      ><a name="22027" href="StlcProp.html#21988" class="Bound"
      >&#8866;V</a
      ><a name="22029"
      >
</a
      ><a name="22030" href="StlcProp.html#20562" class="Function"
      >preservation</a
      ><a name="22042"
      > </a
      ><a name="22043" class="Symbol"
      >(</a
      ><a name="22044" href="Stlc.html#3585" class="InductiveConstructor"
      >&#8658;-E</a
      ><a name="22047"
      > </a
      ><a name="22048" href="StlcProp.html#22048" class="Bound"
      >&#8866;L</a
      ><a name="22050"
      > </a
      ><a name="22051" href="StlcProp.html#22051" class="Bound"
      >&#8866;M</a
      ><a name="22053" class="Symbol"
      >)</a
      ><a name="22054"
      > </a
      ><a name="22055" class="Symbol"
      >(</a
      ><a name="22056" href="Stlc.html#1888" class="InductiveConstructor"
      >&#947;&#8658;&#8321;</a
      ><a name="22059"
      > </a
      ><a name="22060" href="StlcProp.html#22060" class="Bound"
      >L&#10233;L&#8242;</a
      ><a name="22064" class="Symbol"
      >)</a
      ><a name="22065"
      > </a
      ><a name="22066" class="Keyword"
      >with</a
      ><a name="22070"
      > </a
      ><a name="22071" href="StlcProp.html#20562" class="Function"
      >preservation</a
      ><a name="22083"
      > </a
      ><a name="22084" href="StlcProp.html#22048" class="Bound"
      >&#8866;L</a
      ><a name="22086"
      > </a
      ><a name="22087" href="StlcProp.html#22060" class="Bound"
      >L&#10233;L&#8242;</a
      ><a name="22091"
      >
</a
      ><a name="22092" class="Symbol"
      >...|</a
      ><a name="22096"
      > </a
      ><a name="22097" href="StlcProp.html#22097" class="Bound"
      >&#8866;L&#8242;</a
      ><a name="22100"
      > </a
      ><a name="22101" class="Symbol"
      >=</a
      ><a name="22102"
      > </a
      ><a name="22103" href="Stlc.html#3585" class="InductiveConstructor"
      >&#8658;-E</a
      ><a name="22106"
      > </a
      ><a name="22107" href="StlcProp.html#22097" class="Bound"
      >&#8866;L&#8242;</a
      ><a name="22110"
      > </a
      ><a name="22111" href="StlcProp.html#22051" class="Bound"
      >&#8866;M</a
      ><a name="22113"
      >
</a
      ><a name="22114" href="StlcProp.html#20562" class="Function"
      >preservation</a
      ><a name="22126"
      > </a
      ><a name="22127" class="Symbol"
      >(</a
      ><a name="22128" href="Stlc.html#3585" class="InductiveConstructor"
      >&#8658;-E</a
      ><a name="22131"
      > </a
      ><a name="22132" href="StlcProp.html#22132" class="Bound"
      >&#8866;L</a
      ><a name="22134"
      > </a
      ><a name="22135" href="StlcProp.html#22135" class="Bound"
      >&#8866;M</a
      ><a name="22137" class="Symbol"
      >)</a
      ><a name="22138"
      > </a
      ><a name="22139" class="Symbol"
      >(</a
      ><a name="22140" href="Stlc.html#1941" class="InductiveConstructor"
      >&#947;&#8658;&#8322;</a
      ><a name="22143"
      > </a
      ><a name="22144" href="StlcProp.html#22144" class="Bound"
      >valueL</a
      ><a name="22150"
      > </a
      ><a name="22151" href="StlcProp.html#22151" class="Bound"
      >M&#10233;M&#8242;</a
      ><a name="22155" class="Symbol"
      >)</a
      ><a name="22156"
      > </a
      ><a name="22157" class="Keyword"
      >with</a
      ><a name="22161"
      > </a
      ><a name="22162" href="StlcProp.html#20562" class="Function"
      >preservation</a
      ><a name="22174"
      > </a
      ><a name="22175" href="StlcProp.html#22135" class="Bound"
      >&#8866;M</a
      ><a name="22177"
      > </a
      ><a name="22178" href="StlcProp.html#22151" class="Bound"
      >M&#10233;M&#8242;</a
      ><a name="22182"
      >
</a
      ><a name="22183" class="Symbol"
      >...|</a
      ><a name="22187"
      > </a
      ><a name="22188" href="StlcProp.html#22188" class="Bound"
      >&#8866;M&#8242;</a
      ><a name="22191"
      > </a
      ><a name="22192" class="Symbol"
      >=</a
      ><a name="22193"
      > </a
      ><a name="22194" href="Stlc.html#3585" class="InductiveConstructor"
      >&#8658;-E</a
      ><a name="22197"
      > </a
      ><a name="22198" href="StlcProp.html#22132" class="Bound"
      >&#8866;L</a
      ><a name="22200"
      > </a
      ><a name="22201" href="StlcProp.html#22188" class="Bound"
      >&#8866;M&#8242;</a
      ><a name="22204"
      >
</a
      ><a name="22205" href="StlcProp.html#20562" class="Function"
      >preservation</a
      ><a name="22217"
      > </a
      ><a name="22218" href="Stlc.html#3663" class="InductiveConstructor"
      >&#120121;-I&#8321;</a
      ><a name="22222"
      > </a
      ><a name="22223" class="Symbol"
      >()</a
      ><a name="22225"
      >
</a
      ><a name="22226" href="StlcProp.html#20562" class="Function"
      >preservation</a
      ><a name="22238"
      > </a
      ><a name="22239" href="Stlc.html#3697" class="InductiveConstructor"
      >&#120121;-I&#8322;</a
      ><a name="22243"
      > </a
      ><a name="22244" class="Symbol"
      >()</a
      ><a name="22246"
      >
</a
      ><a name="22247" href="StlcProp.html#20562" class="Function"
      >preservation</a
      ><a name="22259"
      > </a
      ><a name="22260" class="Symbol"
      >(</a
      ><a name="22261" href="Stlc.html#3732" class="InductiveConstructor"
      >&#120121;-E</a
      ><a name="22264"
      > </a
      ><a name="22265" href="Stlc.html#3663" class="InductiveConstructor"
      >&#120121;-I&#8321;</a
      ><a name="22269"
      > </a
      ><a name="22270" href="StlcProp.html#22270" class="Bound"
      >&#8866;M</a
      ><a name="22272"
      > </a
      ><a name="22273" href="StlcProp.html#22273" class="Bound"
      >&#8866;N</a
      ><a name="22275" class="Symbol"
      >)</a
      ><a name="22276"
      > </a
      ><a name="22277" href="Stlc.html#2008" class="InductiveConstructor"
      >&#946;&#120121;&#8321;</a
      ><a name="22280"
      > </a
      ><a name="22281" class="Symbol"
      >=</a
      ><a name="22282"
      > </a
      ><a name="22283" href="StlcProp.html#22270" class="Bound"
      >&#8866;M</a
      ><a name="22285"
      >
</a
      ><a name="22286" href="StlcProp.html#20562" class="Function"
      >preservation</a
      ><a name="22298"
      > </a
      ><a name="22299" class="Symbol"
      >(</a
      ><a name="22300" href="Stlc.html#3732" class="InductiveConstructor"
      >&#120121;-E</a
      ><a name="22303"
      > </a
      ><a name="22304" href="Stlc.html#3697" class="InductiveConstructor"
      >&#120121;-I&#8322;</a
      ><a name="22308"
      > </a
      ><a name="22309" href="StlcProp.html#22309" class="Bound"
      >&#8866;M</a
      ><a name="22311"
      > </a
      ><a name="22312" href="StlcProp.html#22312" class="Bound"
      >&#8866;N</a
      ><a name="22314" class="Symbol"
      >)</a
      ><a name="22315"
      > </a
      ><a name="22316" href="Stlc.html#2056" class="InductiveConstructor"
      >&#946;&#120121;&#8322;</a
      ><a name="22319"
      > </a
      ><a name="22320" class="Symbol"
      >=</a
      ><a name="22321"
      > </a
      ><a name="22322" href="StlcProp.html#22312" class="Bound"
      >&#8866;N</a
      ><a name="22324"
      >
</a
      ><a name="22325" href="StlcProp.html#20562" class="Function"
      >preservation</a
      ><a name="22337"
      > </a
      ><a name="22338" class="Symbol"
      >(</a
      ><a name="22339" href="Stlc.html#3732" class="InductiveConstructor"
      >&#120121;-E</a
      ><a name="22342"
      > </a
      ><a name="22343" href="StlcProp.html#22343" class="Bound"
      >&#8866;L</a
      ><a name="22345"
      > </a
      ><a name="22346" href="StlcProp.html#22346" class="Bound"
      >&#8866;M</a
      ><a name="22348"
      > </a
      ><a name="22349" href="StlcProp.html#22349" class="Bound"
      >&#8866;N</a
      ><a name="22351" class="Symbol"
      >)</a
      ><a name="22352"
      > </a
      ><a name="22353" class="Symbol"
      >(</a
      ><a name="22354" href="Stlc.html#2105" class="InductiveConstructor"
      >&#947;&#120121;</a
      ><a name="22356"
      > </a
      ><a name="22357" href="StlcProp.html#22357" class="Bound"
      >L&#10233;L&#8242;</a
      ><a name="22361" class="Symbol"
      >)</a
      ><a name="22362"
      > </a
      ><a name="22363" class="Keyword"
      >with</a
      ><a name="22367"
      > </a
      ><a name="22368" href="StlcProp.html#20562" class="Function"
      >preservation</a
      ><a name="22380"
      > </a
      ><a name="22381" href="StlcProp.html#22343" class="Bound"
      >&#8866;L</a
      ><a name="22383"
      > </a
      ><a name="22384" href="StlcProp.html#22357" class="Bound"
      >L&#10233;L&#8242;</a
      ><a name="22388"
      >
</a
      ><a name="22389" class="Symbol"
      >...|</a
      ><a name="22393"
      > </a
      ><a name="22394" href="StlcProp.html#22394" class="Bound"
      >&#8866;L&#8242;</a
      ><a name="22397"
      > </a
      ><a name="22398" class="Symbol"
      >=</a
      ><a name="22399"
      > </a
      ><a name="22400" href="Stlc.html#3732" class="InductiveConstructor"
      >&#120121;-E</a
      ><a name="22403"
      > </a
      ><a name="22404" href="StlcProp.html#22394" class="Bound"
      >&#8866;L&#8242;</a
      ><a name="22407"
      > </a
      ><a name="22408" href="StlcProp.html#22346" class="Bound"
      >&#8866;M</a
      ><a name="22410"
      > </a
      ><a name="22411" href="StlcProp.html#22349" class="Bound"
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

