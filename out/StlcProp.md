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
      ><a name="632" href="Maps.html#10221" class="Module"
      >PartialMap</a
      ><a name="642"
      > </a
      ><a name="643" class="Keyword"
      >using</a
      ><a name="648"
      > </a
      ><a name="649" class="Symbol"
      >(</a
      ><a name="650" href="Maps.html#10265" class="Function"
      >&#8709;</a
      ><a name="651" class="Symbol"
      >;</a
      ><a name="652"
      > </a
      ><a name="653" href="Maps.html#10573" class="Function"
      >apply-&#8709;</a
      ><a name="660" class="Symbol"
      >;</a
      ><a name="661"
      > </a
      ><a name="662" href="Maps.html#11491" class="Function"
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
      ><a name="688" href="Maps.html#10368" class="Function Operator"
      >_,_&#8614;_</a
      ><a name="693"
      > </a
      ><a name="694" class="Symbol"
      >to</a
      ><a name="696"
      > </a
      ><a name="697" href="Maps.html#10368" class="Function Operator"
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
      ><a name="1176" href="Stlc.html#708" class="Datatype"
      >Term</a
      ><a name="1180"
      > </a
      ><a name="1181" class="Symbol"
      >&#8594;</a
      ><a name="1182"
      > </a
      ><a name="1183" href="Stlc.html#590" class="Datatype"
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
      ><a name="1241" href="Stlc.html#745" class="InductiveConstructor Operator"
      >&#955;[</a
      ><a name="1243"
      > </a
      ><a name="1244" href="StlcProp.html#1219" class="Bound"
      >x</a
      ><a name="1245"
      > </a
      ><a name="1246" href="Stlc.html#745" class="InductiveConstructor Operator"
      >&#8758;</a
      ><a name="1247"
      > </a
      ><a name="1248" href="StlcProp.html#1221" class="Bound"
      >A</a
      ><a name="1249"
      > </a
      ><a name="1250" href="Stlc.html#745" class="InductiveConstructor Operator"
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
      ><a name="1262" href="Stlc.html#620" class="InductiveConstructor Operator"
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
      ><a name="1296" href="Stlc.html#808" class="InductiveConstructor"
      >true</a
      ><a name="1300"
      > </a
      ><a name="1301" href="StlcProp.html#1159" class="Datatype Operator"
      >for</a
      ><a name="1304"
      > </a
      ><a name="1305" href="Stlc.html#609" class="InductiveConstructor"
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
      ><a name="1337" href="Stlc.html#822" class="InductiveConstructor"
      >false</a
      ><a name="1342"
      > </a
      ><a name="1343" href="StlcProp.html#1159" class="Datatype Operator"
      >for</a
      ><a name="1346"
      > </a
      ><a name="1347" href="Stlc.html#609" class="InductiveConstructor"
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
      ><a name="1382" href="Maps.html#10265" class="Function"
      >&#8709;</a
      ><a name="1383"
      > </a
      ><a name="1384" href="Stlc.html#3094" class="Datatype Operator"
      >&#8866;</a
      ><a name="1385"
      > </a
      ><a name="1386" href="StlcProp.html#1375" class="Bound"
      >L</a
      ><a name="1387"
      > </a
      ><a name="1388" href="Stlc.html#3094" class="Datatype Operator"
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
      ><a name="1394" href="Stlc.html#1115" class="Datatype"
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
      ><a name="1443" href="Stlc.html#3138" class="InductiveConstructor"
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
      ><a name="1474" href="Stlc.html#3194" class="InductiveConstructor"
      >&#8658;-I</a
      ><a name="1477"
      > </a
      ><a name="1478" href="StlcProp.html#1478" class="Bound"
      >&#8866;N</a
      ><a name="1480" class="Symbol"
      >)</a
      ><a name="1481"
      > </a
      ><a name="1482" href="Stlc.html#1142" class="InductiveConstructor"
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
      ><a name="1525" href="Stlc.html#3271" class="InductiveConstructor"
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
      ><a name="1559" href="Stlc.html#3349" class="InductiveConstructor"
      >&#120121;-I&#8321;</a
      ><a name="1563"
      > </a
      ><a name="1564" href="Stlc.html#1191" class="InductiveConstructor"
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
      ><a name="1612" href="Stlc.html#3383" class="InductiveConstructor"
      >&#120121;-I&#8322;</a
      ><a name="1616"
      > </a
      ><a name="1617" href="Stlc.html#1218" class="InductiveConstructor"
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
      ><a name="1668" href="Stlc.html#3418" class="InductiveConstructor"
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
      ><a name="1897" href="Stlc.html#708" class="Datatype"
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
      ><a name="1936" href="Stlc.html#1776" class="Datatype Operator"
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
      ><a name="1971" href="Stlc.html#1115" class="Datatype"
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
      ><a name="2014" href="Maps.html#10265" class="Function"
      >&#8709;</a
      ><a name="2015"
      > </a
      ><a name="2016" href="Stlc.html#3094" class="Datatype Operator"
      >&#8866;</a
      ><a name="2017"
      > </a
      ><a name="2018" href="StlcProp.html#2007" class="Bound"
      >M</a
      ><a name="2019"
      > </a
      ><a name="2020" href="Stlc.html#3094" class="Datatype Operator"
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
      ><a name="3912" href="Stlc.html#3138" class="InductiveConstructor"
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
      ><a name="3929" href="Stlc.html#3194" class="InductiveConstructor"
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
      ><a name="3944" href="Stlc.html#1142" class="InductiveConstructor"
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
      ><a name="3962" href="Stlc.html#3271" class="InductiveConstructor"
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
      ><a name="4016" href="Stlc.html#1877" class="InductiveConstructor"
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
      ><a name="4087" href="Stlc.html#1930" class="InductiveConstructor"
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
      ><a name="4184" href="Stlc.html#1808" class="InductiveConstructor"
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
      ><a name="4204" href="Stlc.html#3349" class="InductiveConstructor"
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
      ><a name="4216" href="Stlc.html#1191" class="InductiveConstructor"
      >value-true</a
      ><a name="4226"
      >
</a
      ><a name="4227" href="StlcProp.html#1993" class="Function"
      >progress</a
      ><a name="4235"
      > </a
      ><a name="4236" href="Stlc.html#3383" class="InductiveConstructor"
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
      ><a name="4248" href="Stlc.html#1218" class="InductiveConstructor"
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
      ><a name="4270" href="Stlc.html#3418" class="InductiveConstructor"
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
      ><a name="4327" href="Stlc.html#2094" class="InductiveConstructor"
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
      ><a name="4418" href="Stlc.html#1997" class="InductiveConstructor"
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
      ><a name="4452" href="Stlc.html#2045" class="InductiveConstructor"
      >&#946;&#120121;&#8322;</a
      >
{% endraw %}</pre>

This code reads neatly in part because we look at the
`steps` option before the `done` option. We could, of course,
look at it the other way around, but then the `...` abbreviation
no longer works, and we will need to write out all the arguments
in full. In general, the rule of thumb is to look at the easy case
(here `steps`) before the hard case (her `done`).
If you have two hard cases, you will have to expand out `...`
or introduce subsidiary functions.

#### Exercise: 3 stars, optional (progress_from_term_ind)
Show that progress can also be proved by induction on terms
instead of induction on typing derivations.

<pre class="Agda">{% raw %}
<a name="5105" class="Keyword"
      >postulate</a
      ><a name="5114"
      >
  </a
      ><a name="5117" href="StlcProp.html#5117" class="Postulate"
      >progress&#8242;</a
      ><a name="5126"
      > </a
      ><a name="5127" class="Symbol"
      >:</a
      ><a name="5128"
      > </a
      ><a name="5129" class="Symbol"
      >&#8704;</a
      ><a name="5130"
      > </a
      ><a name="5131" href="StlcProp.html#5131" class="Bound"
      >M</a
      ><a name="5132"
      > </a
      ><a name="5133" class="Symbol"
      >{</a
      ><a name="5134" href="StlcProp.html#5134" class="Bound"
      >A</a
      ><a name="5135" class="Symbol"
      >}</a
      ><a name="5136"
      > </a
      ><a name="5137" class="Symbol"
      >&#8594;</a
      ><a name="5138"
      > </a
      ><a name="5139" href="Maps.html#10265" class="Function"
      >&#8709;</a
      ><a name="5140"
      > </a
      ><a name="5141" href="Stlc.html#3094" class="Datatype Operator"
      >&#8866;</a
      ><a name="5142"
      > </a
      ><a name="5143" href="StlcProp.html#5131" class="Bound"
      >M</a
      ><a name="5144"
      > </a
      ><a name="5145" href="Stlc.html#3094" class="Datatype Operator"
      >&#8758;</a
      ><a name="5146"
      > </a
      ><a name="5147" href="StlcProp.html#5134" class="Bound"
      >A</a
      ><a name="5148"
      > </a
      ><a name="5149" class="Symbol"
      >&#8594;</a
      ><a name="5150"
      > </a
      ><a name="5151" href="StlcProp.html#1886" class="Datatype"
      >Progress</a
      ><a name="5159"
      > </a
      ><a name="5160" href="StlcProp.html#5131" class="Bound"
      >M</a
      >
{% endraw %}</pre>

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
    `β⇒` rule, whose definition uses the substitution operation.  To see that
    this step preserves typing, we need to know that the substitution itself
    does.  So we prove a ... 

  - _substitution lemma_, stating that substituting a (closed)
    term `V` for a variable `x` in a term `N` preserves the type
    of `N`.  The proof goes by induction on the form of `N` and
    requires looking at all the different cases in the definition
    of substitition.  The tricky cases are the ones for
    variables and for function abstractions.  In both cases, we
    discover that we need to take a term `V` that has been shown
    to be well-typed in some context `Γ` and consider the same
    term in a different context `Γ′`.  For this
    we prove a...

  - _context invariance_ lemma, showing that typing is preserved
    under "inessential changes" to the context---a term `M`
    well typed in `Γ` is also well typed in `Γ′`, so long as
    all the free variables of `M` appear in both contexts.
    And finally, for this, we need a careful definition of ...

  - _free variables_ of a term---i.e., those variables
    mentioned in a term and not in the scope of an enclosing
    function abstraction binding a variable of the same name.

To make Agda happy, we need to formalize the story in the opposite
order.


### Free Occurrences

A variable `x` appears _free_ in a term `M` if `M` contains an
occurrence of `x` that is not bound in an outer lambda abstraction.
For example:

  - `x` appears free, but `f` does not, in `λ[ f ∶ (𝔹 ⇒ 𝔹) ] var f · var x`
  - both `f` and `x` appear free in `(λ[ f ∶ (𝔹 ⇒ 𝔹) ] var f · var x) · var f`;
    note that `f` appears both bound and free in this term
  - no variables appear free in `λ[ f ∶ (𝔹 ⇒ 𝔹) ] λ[ x ∶ 𝔹 ] var f · var x`

Formally:

<pre class="Agda">{% raw %}
<a name="7569" class="Keyword"
      >data</a
      ><a name="7573"
      > </a
      ><a name="7574" href="StlcProp.html#7574" class="Datatype Operator"
      >_&#8712;_</a
      ><a name="7577"
      > </a
      ><a name="7578" class="Symbol"
      >:</a
      ><a name="7579"
      > </a
      ><a name="7580" href="Maps.html#2171" class="Datatype"
      >Id</a
      ><a name="7582"
      > </a
      ><a name="7583" class="Symbol"
      >&#8594;</a
      ><a name="7584"
      > </a
      ><a name="7585" href="Stlc.html#708" class="Datatype"
      >Term</a
      ><a name="7589"
      > </a
      ><a name="7590" class="Symbol"
      >&#8594;</a
      ><a name="7591"
      > </a
      ><a name="7592" class="PrimitiveType"
      >Set</a
      ><a name="7595"
      > </a
      ><a name="7596" class="Keyword"
      >where</a
      ><a name="7601"
      >
  </a
      ><a name="7604" href="StlcProp.html#7604" class="InductiveConstructor"
      >free-var</a
      ><a name="7612"
      >  </a
      ><a name="7614" class="Symbol"
      >:</a
      ><a name="7615"
      > </a
      ><a name="7616" class="Symbol"
      >&#8704;</a
      ><a name="7617"
      > </a
      ><a name="7618" class="Symbol"
      >{</a
      ><a name="7619" href="StlcProp.html#7619" class="Bound"
      >x</a
      ><a name="7620" class="Symbol"
      >}</a
      ><a name="7621"
      > </a
      ><a name="7622" class="Symbol"
      >&#8594;</a
      ><a name="7623"
      > </a
      ><a name="7624" href="StlcProp.html#7619" class="Bound"
      >x</a
      ><a name="7625"
      > </a
      ><a name="7626" href="StlcProp.html#7574" class="Datatype Operator"
      >&#8712;</a
      ><a name="7627"
      > </a
      ><a name="7628" href="Stlc.html#727" class="InductiveConstructor"
      >var</a
      ><a name="7631"
      > </a
      ><a name="7632" href="StlcProp.html#7619" class="Bound"
      >x</a
      ><a name="7633"
      >
  </a
      ><a name="7636" href="StlcProp.html#7636" class="InductiveConstructor"
      >free-&#955;</a
      ><a name="7642"
      >  </a
      ><a name="7644" class="Symbol"
      >:</a
      ><a name="7645"
      > </a
      ><a name="7646" class="Symbol"
      >&#8704;</a
      ><a name="7647"
      > </a
      ><a name="7648" class="Symbol"
      >{</a
      ><a name="7649" href="StlcProp.html#7649" class="Bound"
      >x</a
      ><a name="7650"
      > </a
      ><a name="7651" href="StlcProp.html#7651" class="Bound"
      >y</a
      ><a name="7652"
      > </a
      ><a name="7653" href="StlcProp.html#7653" class="Bound"
      >A</a
      ><a name="7654"
      > </a
      ><a name="7655" href="StlcProp.html#7655" class="Bound"
      >N</a
      ><a name="7656" class="Symbol"
      >}</a
      ><a name="7657"
      > </a
      ><a name="7658" class="Symbol"
      >&#8594;</a
      ><a name="7659"
      > </a
      ><a name="7660" href="StlcProp.html#7651" class="Bound"
      >y</a
      ><a name="7661"
      > </a
      ><a name="7662" href="https://agda.github.io/agda-stdlib/Relation.Binary.Core.html#4493" class="Function Operator"
      >&#8802;</a
      ><a name="7663"
      > </a
      ><a name="7664" href="StlcProp.html#7649" class="Bound"
      >x</a
      ><a name="7665"
      > </a
      ><a name="7666" class="Symbol"
      >&#8594;</a
      ><a name="7667"
      > </a
      ><a name="7668" href="StlcProp.html#7649" class="Bound"
      >x</a
      ><a name="7669"
      > </a
      ><a name="7670" href="StlcProp.html#7574" class="Datatype Operator"
      >&#8712;</a
      ><a name="7671"
      > </a
      ><a name="7672" href="StlcProp.html#7655" class="Bound"
      >N</a
      ><a name="7673"
      > </a
      ><a name="7674" class="Symbol"
      >&#8594;</a
      ><a name="7675"
      > </a
      ><a name="7676" href="StlcProp.html#7649" class="Bound"
      >x</a
      ><a name="7677"
      > </a
      ><a name="7678" href="StlcProp.html#7574" class="Datatype Operator"
      >&#8712;</a
      ><a name="7679"
      > </a
      ><a name="7680" class="Symbol"
      >(</a
      ><a name="7681" href="Stlc.html#745" class="InductiveConstructor Operator"
      >&#955;[</a
      ><a name="7683"
      > </a
      ><a name="7684" href="StlcProp.html#7651" class="Bound"
      >y</a
      ><a name="7685"
      > </a
      ><a name="7686" href="Stlc.html#745" class="InductiveConstructor Operator"
      >&#8758;</a
      ><a name="7687"
      > </a
      ><a name="7688" href="StlcProp.html#7653" class="Bound"
      >A</a
      ><a name="7689"
      > </a
      ><a name="7690" href="Stlc.html#745" class="InductiveConstructor Operator"
      >]</a
      ><a name="7691"
      > </a
      ><a name="7692" href="StlcProp.html#7655" class="Bound"
      >N</a
      ><a name="7693" class="Symbol"
      >)</a
      ><a name="7694"
      >
  </a
      ><a name="7697" href="StlcProp.html#7697" class="InductiveConstructor"
      >free-&#183;&#8321;</a
      ><a name="7704"
      > </a
      ><a name="7705" class="Symbol"
      >:</a
      ><a name="7706"
      > </a
      ><a name="7707" class="Symbol"
      >&#8704;</a
      ><a name="7708"
      > </a
      ><a name="7709" class="Symbol"
      >{</a
      ><a name="7710" href="StlcProp.html#7710" class="Bound"
      >x</a
      ><a name="7711"
      > </a
      ><a name="7712" href="StlcProp.html#7712" class="Bound"
      >L</a
      ><a name="7713"
      > </a
      ><a name="7714" href="StlcProp.html#7714" class="Bound"
      >M</a
      ><a name="7715" class="Symbol"
      >}</a
      ><a name="7716"
      > </a
      ><a name="7717" class="Symbol"
      >&#8594;</a
      ><a name="7718"
      > </a
      ><a name="7719" href="StlcProp.html#7710" class="Bound"
      >x</a
      ><a name="7720"
      > </a
      ><a name="7721" href="StlcProp.html#7574" class="Datatype Operator"
      >&#8712;</a
      ><a name="7722"
      > </a
      ><a name="7723" href="StlcProp.html#7712" class="Bound"
      >L</a
      ><a name="7724"
      > </a
      ><a name="7725" class="Symbol"
      >&#8594;</a
      ><a name="7726"
      > </a
      ><a name="7727" href="StlcProp.html#7710" class="Bound"
      >x</a
      ><a name="7728"
      > </a
      ><a name="7729" href="StlcProp.html#7574" class="Datatype Operator"
      >&#8712;</a
      ><a name="7730"
      > </a
      ><a name="7731" class="Symbol"
      >(</a
      ><a name="7732" href="StlcProp.html#7712" class="Bound"
      >L</a
      ><a name="7733"
      > </a
      ><a name="7734" href="Stlc.html#781" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="7735"
      > </a
      ><a name="7736" href="StlcProp.html#7714" class="Bound"
      >M</a
      ><a name="7737" class="Symbol"
      >)</a
      ><a name="7738"
      >
  </a
      ><a name="7741" href="StlcProp.html#7741" class="InductiveConstructor"
      >free-&#183;&#8322;</a
      ><a name="7748"
      > </a
      ><a name="7749" class="Symbol"
      >:</a
      ><a name="7750"
      > </a
      ><a name="7751" class="Symbol"
      >&#8704;</a
      ><a name="7752"
      > </a
      ><a name="7753" class="Symbol"
      >{</a
      ><a name="7754" href="StlcProp.html#7754" class="Bound"
      >x</a
      ><a name="7755"
      > </a
      ><a name="7756" href="StlcProp.html#7756" class="Bound"
      >L</a
      ><a name="7757"
      > </a
      ><a name="7758" href="StlcProp.html#7758" class="Bound"
      >M</a
      ><a name="7759" class="Symbol"
      >}</a
      ><a name="7760"
      > </a
      ><a name="7761" class="Symbol"
      >&#8594;</a
      ><a name="7762"
      > </a
      ><a name="7763" href="StlcProp.html#7754" class="Bound"
      >x</a
      ><a name="7764"
      > </a
      ><a name="7765" href="StlcProp.html#7574" class="Datatype Operator"
      >&#8712;</a
      ><a name="7766"
      > </a
      ><a name="7767" href="StlcProp.html#7758" class="Bound"
      >M</a
      ><a name="7768"
      > </a
      ><a name="7769" class="Symbol"
      >&#8594;</a
      ><a name="7770"
      > </a
      ><a name="7771" href="StlcProp.html#7754" class="Bound"
      >x</a
      ><a name="7772"
      > </a
      ><a name="7773" href="StlcProp.html#7574" class="Datatype Operator"
      >&#8712;</a
      ><a name="7774"
      > </a
      ><a name="7775" class="Symbol"
      >(</a
      ><a name="7776" href="StlcProp.html#7756" class="Bound"
      >L</a
      ><a name="7777"
      > </a
      ><a name="7778" href="Stlc.html#781" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="7779"
      > </a
      ><a name="7780" href="StlcProp.html#7758" class="Bound"
      >M</a
      ><a name="7781" class="Symbol"
      >)</a
      ><a name="7782"
      >
  </a
      ><a name="7785" href="StlcProp.html#7785" class="InductiveConstructor"
      >free-if&#8321;</a
      ><a name="7793"
      > </a
      ><a name="7794" class="Symbol"
      >:</a
      ><a name="7795"
      > </a
      ><a name="7796" class="Symbol"
      >&#8704;</a
      ><a name="7797"
      > </a
      ><a name="7798" class="Symbol"
      >{</a
      ><a name="7799" href="StlcProp.html#7799" class="Bound"
      >x</a
      ><a name="7800"
      > </a
      ><a name="7801" href="StlcProp.html#7801" class="Bound"
      >L</a
      ><a name="7802"
      > </a
      ><a name="7803" href="StlcProp.html#7803" class="Bound"
      >M</a
      ><a name="7804"
      > </a
      ><a name="7805" href="StlcProp.html#7805" class="Bound"
      >N</a
      ><a name="7806" class="Symbol"
      >}</a
      ><a name="7807"
      > </a
      ><a name="7808" class="Symbol"
      >&#8594;</a
      ><a name="7809"
      > </a
      ><a name="7810" href="StlcProp.html#7799" class="Bound"
      >x</a
      ><a name="7811"
      > </a
      ><a name="7812" href="StlcProp.html#7574" class="Datatype Operator"
      >&#8712;</a
      ><a name="7813"
      > </a
      ><a name="7814" href="StlcProp.html#7801" class="Bound"
      >L</a
      ><a name="7815"
      > </a
      ><a name="7816" class="Symbol"
      >&#8594;</a
      ><a name="7817"
      > </a
      ><a name="7818" href="StlcProp.html#7799" class="Bound"
      >x</a
      ><a name="7819"
      > </a
      ><a name="7820" href="StlcProp.html#7574" class="Datatype Operator"
      >&#8712;</a
      ><a name="7821"
      > </a
      ><a name="7822" class="Symbol"
      >(</a
      ><a name="7823" href="Stlc.html#837" class="InductiveConstructor Operator"
      >if</a
      ><a name="7825"
      > </a
      ><a name="7826" href="StlcProp.html#7801" class="Bound"
      >L</a
      ><a name="7827"
      > </a
      ><a name="7828" href="Stlc.html#837" class="InductiveConstructor Operator"
      >then</a
      ><a name="7832"
      > </a
      ><a name="7833" href="StlcProp.html#7803" class="Bound"
      >M</a
      ><a name="7834"
      > </a
      ><a name="7835" href="Stlc.html#837" class="InductiveConstructor Operator"
      >else</a
      ><a name="7839"
      > </a
      ><a name="7840" href="StlcProp.html#7805" class="Bound"
      >N</a
      ><a name="7841" class="Symbol"
      >)</a
      ><a name="7842"
      >
  </a
      ><a name="7845" href="StlcProp.html#7845" class="InductiveConstructor"
      >free-if&#8322;</a
      ><a name="7853"
      > </a
      ><a name="7854" class="Symbol"
      >:</a
      ><a name="7855"
      > </a
      ><a name="7856" class="Symbol"
      >&#8704;</a
      ><a name="7857"
      > </a
      ><a name="7858" class="Symbol"
      >{</a
      ><a name="7859" href="StlcProp.html#7859" class="Bound"
      >x</a
      ><a name="7860"
      > </a
      ><a name="7861" href="StlcProp.html#7861" class="Bound"
      >L</a
      ><a name="7862"
      > </a
      ><a name="7863" href="StlcProp.html#7863" class="Bound"
      >M</a
      ><a name="7864"
      > </a
      ><a name="7865" href="StlcProp.html#7865" class="Bound"
      >N</a
      ><a name="7866" class="Symbol"
      >}</a
      ><a name="7867"
      > </a
      ><a name="7868" class="Symbol"
      >&#8594;</a
      ><a name="7869"
      > </a
      ><a name="7870" href="StlcProp.html#7859" class="Bound"
      >x</a
      ><a name="7871"
      > </a
      ><a name="7872" href="StlcProp.html#7574" class="Datatype Operator"
      >&#8712;</a
      ><a name="7873"
      > </a
      ><a name="7874" href="StlcProp.html#7863" class="Bound"
      >M</a
      ><a name="7875"
      > </a
      ><a name="7876" class="Symbol"
      >&#8594;</a
      ><a name="7877"
      > </a
      ><a name="7878" href="StlcProp.html#7859" class="Bound"
      >x</a
      ><a name="7879"
      > </a
      ><a name="7880" href="StlcProp.html#7574" class="Datatype Operator"
      >&#8712;</a
      ><a name="7881"
      > </a
      ><a name="7882" class="Symbol"
      >(</a
      ><a name="7883" href="Stlc.html#837" class="InductiveConstructor Operator"
      >if</a
      ><a name="7885"
      > </a
      ><a name="7886" href="StlcProp.html#7861" class="Bound"
      >L</a
      ><a name="7887"
      > </a
      ><a name="7888" href="Stlc.html#837" class="InductiveConstructor Operator"
      >then</a
      ><a name="7892"
      > </a
      ><a name="7893" href="StlcProp.html#7863" class="Bound"
      >M</a
      ><a name="7894"
      > </a
      ><a name="7895" href="Stlc.html#837" class="InductiveConstructor Operator"
      >else</a
      ><a name="7899"
      > </a
      ><a name="7900" href="StlcProp.html#7865" class="Bound"
      >N</a
      ><a name="7901" class="Symbol"
      >)</a
      ><a name="7902"
      >
  </a
      ><a name="7905" href="StlcProp.html#7905" class="InductiveConstructor"
      >free-if&#8323;</a
      ><a name="7913"
      > </a
      ><a name="7914" class="Symbol"
      >:</a
      ><a name="7915"
      > </a
      ><a name="7916" class="Symbol"
      >&#8704;</a
      ><a name="7917"
      > </a
      ><a name="7918" class="Symbol"
      >{</a
      ><a name="7919" href="StlcProp.html#7919" class="Bound"
      >x</a
      ><a name="7920"
      > </a
      ><a name="7921" href="StlcProp.html#7921" class="Bound"
      >L</a
      ><a name="7922"
      > </a
      ><a name="7923" href="StlcProp.html#7923" class="Bound"
      >M</a
      ><a name="7924"
      > </a
      ><a name="7925" href="StlcProp.html#7925" class="Bound"
      >N</a
      ><a name="7926" class="Symbol"
      >}</a
      ><a name="7927"
      > </a
      ><a name="7928" class="Symbol"
      >&#8594;</a
      ><a name="7929"
      > </a
      ><a name="7930" href="StlcProp.html#7919" class="Bound"
      >x</a
      ><a name="7931"
      > </a
      ><a name="7932" href="StlcProp.html#7574" class="Datatype Operator"
      >&#8712;</a
      ><a name="7933"
      > </a
      ><a name="7934" href="StlcProp.html#7925" class="Bound"
      >N</a
      ><a name="7935"
      > </a
      ><a name="7936" class="Symbol"
      >&#8594;</a
      ><a name="7937"
      > </a
      ><a name="7938" href="StlcProp.html#7919" class="Bound"
      >x</a
      ><a name="7939"
      > </a
      ><a name="7940" href="StlcProp.html#7574" class="Datatype Operator"
      >&#8712;</a
      ><a name="7941"
      > </a
      ><a name="7942" class="Symbol"
      >(</a
      ><a name="7943" href="Stlc.html#837" class="InductiveConstructor Operator"
      >if</a
      ><a name="7945"
      > </a
      ><a name="7946" href="StlcProp.html#7921" class="Bound"
      >L</a
      ><a name="7947"
      > </a
      ><a name="7948" href="Stlc.html#837" class="InductiveConstructor Operator"
      >then</a
      ><a name="7952"
      > </a
      ><a name="7953" href="StlcProp.html#7923" class="Bound"
      >M</a
      ><a name="7954"
      > </a
      ><a name="7955" href="Stlc.html#837" class="InductiveConstructor Operator"
      >else</a
      ><a name="7959"
      > </a
      ><a name="7960" href="StlcProp.html#7925" class="Bound"
      >N</a
      ><a name="7961" class="Symbol"
      >)</a
      >
{% endraw %}</pre>

A term in which no variables appear free is said to be _closed_.

<pre class="Agda">{% raw %}
<a name="8054" href="StlcProp.html#8054" class="Function Operator"
      >_&#8713;_</a
      ><a name="8057"
      > </a
      ><a name="8058" class="Symbol"
      >:</a
      ><a name="8059"
      > </a
      ><a name="8060" href="Maps.html#2171" class="Datatype"
      >Id</a
      ><a name="8062"
      > </a
      ><a name="8063" class="Symbol"
      >&#8594;</a
      ><a name="8064"
      > </a
      ><a name="8065" href="Stlc.html#708" class="Datatype"
      >Term</a
      ><a name="8069"
      > </a
      ><a name="8070" class="Symbol"
      >&#8594;</a
      ><a name="8071"
      > </a
      ><a name="8072" class="PrimitiveType"
      >Set</a
      ><a name="8075"
      >
</a
      ><a name="8076" href="StlcProp.html#8076" class="Bound"
      >x</a
      ><a name="8077"
      > </a
      ><a name="8078" href="StlcProp.html#8054" class="Function Operator"
      >&#8713;</a
      ><a name="8079"
      > </a
      ><a name="8080" href="StlcProp.html#8080" class="Bound"
      >M</a
      ><a name="8081"
      > </a
      ><a name="8082" class="Symbol"
      >=</a
      ><a name="8083"
      > </a
      ><a name="8084" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#414" class="Function Operator"
      >&#172;</a
      ><a name="8085"
      > </a
      ><a name="8086" class="Symbol"
      >(</a
      ><a name="8087" href="StlcProp.html#8076" class="Bound"
      >x</a
      ><a name="8088"
      > </a
      ><a name="8089" href="StlcProp.html#7574" class="Datatype Operator"
      >&#8712;</a
      ><a name="8090"
      > </a
      ><a name="8091" href="StlcProp.html#8080" class="Bound"
      >M</a
      ><a name="8092" class="Symbol"
      >)</a
      ><a name="8093"
      >

</a
      ><a name="8095" href="StlcProp.html#8095" class="Function"
      >closed</a
      ><a name="8101"
      > </a
      ><a name="8102" class="Symbol"
      >:</a
      ><a name="8103"
      > </a
      ><a name="8104" href="Stlc.html#708" class="Datatype"
      >Term</a
      ><a name="8108"
      > </a
      ><a name="8109" class="Symbol"
      >&#8594;</a
      ><a name="8110"
      > </a
      ><a name="8111" class="PrimitiveType"
      >Set</a
      ><a name="8114"
      >
</a
      ><a name="8115" href="StlcProp.html#8095" class="Function"
      >closed</a
      ><a name="8121"
      > </a
      ><a name="8122" href="StlcProp.html#8122" class="Bound"
      >M</a
      ><a name="8123"
      > </a
      ><a name="8124" class="Symbol"
      >=</a
      ><a name="8125"
      > </a
      ><a name="8126" class="Symbol"
      >&#8704;</a
      ><a name="8127"
      > </a
      ><a name="8128" class="Symbol"
      >{</a
      ><a name="8129" href="StlcProp.html#8129" class="Bound"
      >x</a
      ><a name="8130" class="Symbol"
      >}</a
      ><a name="8131"
      > </a
      ><a name="8132" class="Symbol"
      >&#8594;</a
      ><a name="8133"
      > </a
      ><a name="8134" href="StlcProp.html#8129" class="Bound"
      >x</a
      ><a name="8135"
      > </a
      ><a name="8136" href="StlcProp.html#8054" class="Function Operator"
      >&#8713;</a
      ><a name="8137"
      > </a
      ><a name="8138" href="StlcProp.html#8122" class="Bound"
      >M</a
      >
{% endraw %}</pre>

Here are proofs corresponding to the first two examples above.

<pre class="Agda">{% raw %}
<a name="8229" href="StlcProp.html#8229" class="Function"
      >f&#8802;x</a
      ><a name="8232"
      > </a
      ><a name="8233" class="Symbol"
      >:</a
      ><a name="8234"
      > </a
      ><a name="8235" href="Stlc.html#919" class="Function"
      >f</a
      ><a name="8236"
      > </a
      ><a name="8237" href="https://agda.github.io/agda-stdlib/Relation.Binary.Core.html#4493" class="Function Operator"
      >&#8802;</a
      ><a name="8238"
      > </a
      ><a name="8239" href="Stlc.html#921" class="Function"
      >x</a
      ><a name="8240"
      >
</a
      ><a name="8241" href="StlcProp.html#8229" class="Function"
      >f&#8802;x</a
      ><a name="8244"
      > </a
      ><a name="8245" class="Symbol"
      >()</a
      ><a name="8247"
      >

</a
      ><a name="8249" href="StlcProp.html#8249" class="Function"
      >example-free&#8321;</a
      ><a name="8262"
      > </a
      ><a name="8263" class="Symbol"
      >:</a
      ><a name="8264"
      > </a
      ><a name="8265" href="Stlc.html#921" class="Function"
      >x</a
      ><a name="8266"
      > </a
      ><a name="8267" href="StlcProp.html#7574" class="Datatype Operator"
      >&#8712;</a
      ><a name="8268"
      > </a
      ><a name="8269" class="Symbol"
      >(</a
      ><a name="8270" href="Stlc.html#745" class="InductiveConstructor Operator"
      >&#955;[</a
      ><a name="8272"
      > </a
      ><a name="8273" href="Stlc.html#919" class="Function"
      >f</a
      ><a name="8274"
      > </a
      ><a name="8275" href="Stlc.html#745" class="InductiveConstructor Operator"
      >&#8758;</a
      ><a name="8276"
      > </a
      ><a name="8277" class="Symbol"
      >(</a
      ><a name="8278" href="Stlc.html#609" class="InductiveConstructor"
      >&#120121;</a
      ><a name="8279"
      > </a
      ><a name="8280" href="Stlc.html#620" class="InductiveConstructor Operator"
      >&#8658;</a
      ><a name="8281"
      > </a
      ><a name="8282" href="Stlc.html#609" class="InductiveConstructor"
      >&#120121;</a
      ><a name="8283" class="Symbol"
      >)</a
      ><a name="8284"
      > </a
      ><a name="8285" href="Stlc.html#745" class="InductiveConstructor Operator"
      >]</a
      ><a name="8286"
      > </a
      ><a name="8287" href="Stlc.html#727" class="InductiveConstructor"
      >var</a
      ><a name="8290"
      > </a
      ><a name="8291" href="Stlc.html#919" class="Function"
      >f</a
      ><a name="8292"
      > </a
      ><a name="8293" href="Stlc.html#781" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="8294"
      > </a
      ><a name="8295" href="Stlc.html#727" class="InductiveConstructor"
      >var</a
      ><a name="8298"
      > </a
      ><a name="8299" href="Stlc.html#921" class="Function"
      >x</a
      ><a name="8300" class="Symbol"
      >)</a
      ><a name="8301"
      >
</a
      ><a name="8302" href="StlcProp.html#8249" class="Function"
      >example-free&#8321;</a
      ><a name="8315"
      > </a
      ><a name="8316" class="Symbol"
      >=</a
      ><a name="8317"
      > </a
      ><a name="8318" href="StlcProp.html#7636" class="InductiveConstructor"
      >free-&#955;</a
      ><a name="8324"
      > </a
      ><a name="8325" href="StlcProp.html#8229" class="Function"
      >f&#8802;x</a
      ><a name="8328"
      > </a
      ><a name="8329" class="Symbol"
      >(</a
      ><a name="8330" href="StlcProp.html#7741" class="InductiveConstructor"
      >free-&#183;&#8322;</a
      ><a name="8337"
      > </a
      ><a name="8338" href="StlcProp.html#7604" class="InductiveConstructor"
      >free-var</a
      ><a name="8346" class="Symbol"
      >)</a
      ><a name="8347"
      >

</a
      ><a name="8349" href="StlcProp.html#8349" class="Function"
      >example-free&#8322;</a
      ><a name="8362"
      > </a
      ><a name="8363" class="Symbol"
      >:</a
      ><a name="8364"
      > </a
      ><a name="8365" href="Stlc.html#919" class="Function"
      >f</a
      ><a name="8366"
      > </a
      ><a name="8367" href="StlcProp.html#8054" class="Function Operator"
      >&#8713;</a
      ><a name="8368"
      > </a
      ><a name="8369" class="Symbol"
      >(</a
      ><a name="8370" href="Stlc.html#745" class="InductiveConstructor Operator"
      >&#955;[</a
      ><a name="8372"
      > </a
      ><a name="8373" href="Stlc.html#919" class="Function"
      >f</a
      ><a name="8374"
      > </a
      ><a name="8375" href="Stlc.html#745" class="InductiveConstructor Operator"
      >&#8758;</a
      ><a name="8376"
      > </a
      ><a name="8377" class="Symbol"
      >(</a
      ><a name="8378" href="Stlc.html#609" class="InductiveConstructor"
      >&#120121;</a
      ><a name="8379"
      > </a
      ><a name="8380" href="Stlc.html#620" class="InductiveConstructor Operator"
      >&#8658;</a
      ><a name="8381"
      > </a
      ><a name="8382" href="Stlc.html#609" class="InductiveConstructor"
      >&#120121;</a
      ><a name="8383" class="Symbol"
      >)</a
      ><a name="8384"
      > </a
      ><a name="8385" href="Stlc.html#745" class="InductiveConstructor Operator"
      >]</a
      ><a name="8386"
      > </a
      ><a name="8387" href="Stlc.html#727" class="InductiveConstructor"
      >var</a
      ><a name="8390"
      > </a
      ><a name="8391" href="Stlc.html#919" class="Function"
      >f</a
      ><a name="8392"
      > </a
      ><a name="8393" href="Stlc.html#781" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="8394"
      > </a
      ><a name="8395" href="Stlc.html#727" class="InductiveConstructor"
      >var</a
      ><a name="8398"
      > </a
      ><a name="8399" href="Stlc.html#921" class="Function"
      >x</a
      ><a name="8400" class="Symbol"
      >)</a
      ><a name="8401"
      >
</a
      ><a name="8402" href="StlcProp.html#8349" class="Function"
      >example-free&#8322;</a
      ><a name="8415"
      > </a
      ><a name="8416" class="Symbol"
      >(</a
      ><a name="8417" href="StlcProp.html#7636" class="InductiveConstructor"
      >free-&#955;</a
      ><a name="8423"
      > </a
      ><a name="8424" href="StlcProp.html#8424" class="Bound"
      >f&#8802;f</a
      ><a name="8427"
      > </a
      ><a name="8428" class="Symbol"
      >_)</a
      ><a name="8430"
      > </a
      ><a name="8431" class="Symbol"
      >=</a
      ><a name="8432"
      > </a
      ><a name="8433" href="StlcProp.html#8424" class="Bound"
      >f&#8802;f</a
      ><a name="8436"
      > </a
      ><a name="8437" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      >
{% endraw %}</pre>


#### Exercise: 1 star (free-in)
Prove formally the remaining examples given above.

<pre class="Agda">{% raw %}
<a name="8552" class="Keyword"
      >postulate</a
      ><a name="8561"
      >
  </a
      ><a name="8564" href="StlcProp.html#8564" class="Postulate"
      >example-free&#8323;</a
      ><a name="8577"
      > </a
      ><a name="8578" class="Symbol"
      >:</a
      ><a name="8579"
      > </a
      ><a name="8580" href="Stlc.html#921" class="Function"
      >x</a
      ><a name="8581"
      > </a
      ><a name="8582" href="StlcProp.html#7574" class="Datatype Operator"
      >&#8712;</a
      ><a name="8583"
      > </a
      ><a name="8584" class="Symbol"
      >((</a
      ><a name="8586" href="Stlc.html#745" class="InductiveConstructor Operator"
      >&#955;[</a
      ><a name="8588"
      > </a
      ><a name="8589" href="Stlc.html#919" class="Function"
      >f</a
      ><a name="8590"
      > </a
      ><a name="8591" href="Stlc.html#745" class="InductiveConstructor Operator"
      >&#8758;</a
      ><a name="8592"
      > </a
      ><a name="8593" class="Symbol"
      >(</a
      ><a name="8594" href="Stlc.html#609" class="InductiveConstructor"
      >&#120121;</a
      ><a name="8595"
      > </a
      ><a name="8596" href="Stlc.html#620" class="InductiveConstructor Operator"
      >&#8658;</a
      ><a name="8597"
      > </a
      ><a name="8598" href="Stlc.html#609" class="InductiveConstructor"
      >&#120121;</a
      ><a name="8599" class="Symbol"
      >)</a
      ><a name="8600"
      > </a
      ><a name="8601" href="Stlc.html#745" class="InductiveConstructor Operator"
      >]</a
      ><a name="8602"
      > </a
      ><a name="8603" href="Stlc.html#727" class="InductiveConstructor"
      >var</a
      ><a name="8606"
      > </a
      ><a name="8607" href="Stlc.html#919" class="Function"
      >f</a
      ><a name="8608"
      > </a
      ><a name="8609" href="Stlc.html#781" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="8610"
      > </a
      ><a name="8611" href="Stlc.html#727" class="InductiveConstructor"
      >var</a
      ><a name="8614"
      > </a
      ><a name="8615" href="Stlc.html#921" class="Function"
      >x</a
      ><a name="8616" class="Symbol"
      >)</a
      ><a name="8617"
      > </a
      ><a name="8618" href="Stlc.html#781" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="8619"
      > </a
      ><a name="8620" href="Stlc.html#727" class="InductiveConstructor"
      >var</a
      ><a name="8623"
      > </a
      ><a name="8624" href="Stlc.html#919" class="Function"
      >f</a
      ><a name="8625" class="Symbol"
      >)</a
      ><a name="8626"
      >
  </a
      ><a name="8629" href="StlcProp.html#8629" class="Postulate"
      >example-free&#8324;</a
      ><a name="8642"
      > </a
      ><a name="8643" class="Symbol"
      >:</a
      ><a name="8644"
      > </a
      ><a name="8645" href="Stlc.html#919" class="Function"
      >f</a
      ><a name="8646"
      > </a
      ><a name="8647" href="StlcProp.html#7574" class="Datatype Operator"
      >&#8712;</a
      ><a name="8648"
      > </a
      ><a name="8649" class="Symbol"
      >((</a
      ><a name="8651" href="Stlc.html#745" class="InductiveConstructor Operator"
      >&#955;[</a
      ><a name="8653"
      > </a
      ><a name="8654" href="Stlc.html#919" class="Function"
      >f</a
      ><a name="8655"
      > </a
      ><a name="8656" href="Stlc.html#745" class="InductiveConstructor Operator"
      >&#8758;</a
      ><a name="8657"
      > </a
      ><a name="8658" class="Symbol"
      >(</a
      ><a name="8659" href="Stlc.html#609" class="InductiveConstructor"
      >&#120121;</a
      ><a name="8660"
      > </a
      ><a name="8661" href="Stlc.html#620" class="InductiveConstructor Operator"
      >&#8658;</a
      ><a name="8662"
      > </a
      ><a name="8663" href="Stlc.html#609" class="InductiveConstructor"
      >&#120121;</a
      ><a name="8664" class="Symbol"
      >)</a
      ><a name="8665"
      > </a
      ><a name="8666" href="Stlc.html#745" class="InductiveConstructor Operator"
      >]</a
      ><a name="8667"
      > </a
      ><a name="8668" href="Stlc.html#727" class="InductiveConstructor"
      >var</a
      ><a name="8671"
      > </a
      ><a name="8672" href="Stlc.html#919" class="Function"
      >f</a
      ><a name="8673"
      > </a
      ><a name="8674" href="Stlc.html#781" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="8675"
      > </a
      ><a name="8676" href="Stlc.html#727" class="InductiveConstructor"
      >var</a
      ><a name="8679"
      > </a
      ><a name="8680" href="Stlc.html#921" class="Function"
      >x</a
      ><a name="8681" class="Symbol"
      >)</a
      ><a name="8682"
      > </a
      ><a name="8683" href="Stlc.html#781" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="8684"
      > </a
      ><a name="8685" href="Stlc.html#727" class="InductiveConstructor"
      >var</a
      ><a name="8688"
      > </a
      ><a name="8689" href="Stlc.html#919" class="Function"
      >f</a
      ><a name="8690" class="Symbol"
      >)</a
      ><a name="8691"
      >
  </a
      ><a name="8694" href="StlcProp.html#8694" class="Postulate"
      >example-free&#8325;</a
      ><a name="8707"
      > </a
      ><a name="8708" class="Symbol"
      >:</a
      ><a name="8709"
      > </a
      ><a name="8710" href="Stlc.html#921" class="Function"
      >x</a
      ><a name="8711"
      > </a
      ><a name="8712" href="StlcProp.html#8054" class="Function Operator"
      >&#8713;</a
      ><a name="8713"
      > </a
      ><a name="8714" class="Symbol"
      >(</a
      ><a name="8715" href="Stlc.html#745" class="InductiveConstructor Operator"
      >&#955;[</a
      ><a name="8717"
      > </a
      ><a name="8718" href="Stlc.html#919" class="Function"
      >f</a
      ><a name="8719"
      > </a
      ><a name="8720" href="Stlc.html#745" class="InductiveConstructor Operator"
      >&#8758;</a
      ><a name="8721"
      > </a
      ><a name="8722" class="Symbol"
      >(</a
      ><a name="8723" href="Stlc.html#609" class="InductiveConstructor"
      >&#120121;</a
      ><a name="8724"
      > </a
      ><a name="8725" href="Stlc.html#620" class="InductiveConstructor Operator"
      >&#8658;</a
      ><a name="8726"
      > </a
      ><a name="8727" href="Stlc.html#609" class="InductiveConstructor"
      >&#120121;</a
      ><a name="8728" class="Symbol"
      >)</a
      ><a name="8729"
      > </a
      ><a name="8730" href="Stlc.html#745" class="InductiveConstructor Operator"
      >]</a
      ><a name="8731"
      > </a
      ><a name="8732" href="Stlc.html#745" class="InductiveConstructor Operator"
      >&#955;[</a
      ><a name="8734"
      > </a
      ><a name="8735" href="Stlc.html#921" class="Function"
      >x</a
      ><a name="8736"
      > </a
      ><a name="8737" href="Stlc.html#745" class="InductiveConstructor Operator"
      >&#8758;</a
      ><a name="8738"
      > </a
      ><a name="8739" href="Stlc.html#609" class="InductiveConstructor"
      >&#120121;</a
      ><a name="8740"
      > </a
      ><a name="8741" href="Stlc.html#745" class="InductiveConstructor Operator"
      >]</a
      ><a name="8742"
      > </a
      ><a name="8743" href="Stlc.html#727" class="InductiveConstructor"
      >var</a
      ><a name="8746"
      > </a
      ><a name="8747" href="Stlc.html#919" class="Function"
      >f</a
      ><a name="8748"
      > </a
      ><a name="8749" href="Stlc.html#781" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="8750"
      > </a
      ><a name="8751" href="Stlc.html#727" class="InductiveConstructor"
      >var</a
      ><a name="8754"
      > </a
      ><a name="8755" href="Stlc.html#921" class="Function"
      >x</a
      ><a name="8756" class="Symbol"
      >)</a
      ><a name="8757"
      >
  </a
      ><a name="8760" href="StlcProp.html#8760" class="Postulate"
      >example-free&#8326;</a
      ><a name="8773"
      > </a
      ><a name="8774" class="Symbol"
      >:</a
      ><a name="8775"
      > </a
      ><a name="8776" href="Stlc.html#919" class="Function"
      >f</a
      ><a name="8777"
      > </a
      ><a name="8778" href="StlcProp.html#8054" class="Function Operator"
      >&#8713;</a
      ><a name="8779"
      > </a
      ><a name="8780" class="Symbol"
      >(</a
      ><a name="8781" href="Stlc.html#745" class="InductiveConstructor Operator"
      >&#955;[</a
      ><a name="8783"
      > </a
      ><a name="8784" href="Stlc.html#919" class="Function"
      >f</a
      ><a name="8785"
      > </a
      ><a name="8786" href="Stlc.html#745" class="InductiveConstructor Operator"
      >&#8758;</a
      ><a name="8787"
      > </a
      ><a name="8788" class="Symbol"
      >(</a
      ><a name="8789" href="Stlc.html#609" class="InductiveConstructor"
      >&#120121;</a
      ><a name="8790"
      > </a
      ><a name="8791" href="Stlc.html#620" class="InductiveConstructor Operator"
      >&#8658;</a
      ><a name="8792"
      > </a
      ><a name="8793" href="Stlc.html#609" class="InductiveConstructor"
      >&#120121;</a
      ><a name="8794" class="Symbol"
      >)</a
      ><a name="8795"
      > </a
      ><a name="8796" href="Stlc.html#745" class="InductiveConstructor Operator"
      >]</a
      ><a name="8797"
      > </a
      ><a name="8798" href="Stlc.html#745" class="InductiveConstructor Operator"
      >&#955;[</a
      ><a name="8800"
      > </a
      ><a name="8801" href="Stlc.html#921" class="Function"
      >x</a
      ><a name="8802"
      > </a
      ><a name="8803" href="Stlc.html#745" class="InductiveConstructor Operator"
      >&#8758;</a
      ><a name="8804"
      > </a
      ><a name="8805" href="Stlc.html#609" class="InductiveConstructor"
      >&#120121;</a
      ><a name="8806"
      > </a
      ><a name="8807" href="Stlc.html#745" class="InductiveConstructor Operator"
      >]</a
      ><a name="8808"
      > </a
      ><a name="8809" href="Stlc.html#727" class="InductiveConstructor"
      >var</a
      ><a name="8812"
      > </a
      ><a name="8813" href="Stlc.html#919" class="Function"
      >f</a
      ><a name="8814"
      > </a
      ><a name="8815" href="Stlc.html#781" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="8816"
      > </a
      ><a name="8817" href="Stlc.html#727" class="InductiveConstructor"
      >var</a
      ><a name="8820"
      > </a
      ><a name="8821" href="Stlc.html#921" class="Function"
      >x</a
      ><a name="8822" class="Symbol"
      >)</a
      >
{% endraw %}</pre>

Although `_∈_` may apperar to be a low-level technical definition,
understanding it is crucial to understanding the properties of
substitution, which are really the crux of the lambda calculus.

### Substitution

To prove that substitution preserves typing, we first need a
technical lemma connecting free variables and typing contexts: If
a variable `x` appears free in a term `M`, and if we know `M` is
well typed in context `Γ`, then it must be the case that
`Γ` assigns a type to `x`.

<pre class="Agda">{% raw %}
<a name="9339" href="StlcProp.html#9339" class="Function"
      >freeLemma</a
      ><a name="9348"
      > </a
      ><a name="9349" class="Symbol"
      >:</a
      ><a name="9350"
      > </a
      ><a name="9351" class="Symbol"
      >&#8704;</a
      ><a name="9352"
      > </a
      ><a name="9353" class="Symbol"
      >{</a
      ><a name="9354" href="StlcProp.html#9354" class="Bound"
      >x</a
      ><a name="9355"
      > </a
      ><a name="9356" href="StlcProp.html#9356" class="Bound"
      >M</a
      ><a name="9357"
      > </a
      ><a name="9358" href="StlcProp.html#9358" class="Bound"
      >A</a
      ><a name="9359"
      > </a
      ><a name="9360" href="StlcProp.html#9360" class="Bound"
      >&#915;</a
      ><a name="9361" class="Symbol"
      >}</a
      ><a name="9362"
      > </a
      ><a name="9363" class="Symbol"
      >&#8594;</a
      ><a name="9364"
      > </a
      ><a name="9365" href="StlcProp.html#9354" class="Bound"
      >x</a
      ><a name="9366"
      > </a
      ><a name="9367" href="StlcProp.html#7574" class="Datatype Operator"
      >&#8712;</a
      ><a name="9368"
      > </a
      ><a name="9369" href="StlcProp.html#9356" class="Bound"
      >M</a
      ><a name="9370"
      > </a
      ><a name="9371" class="Symbol"
      >&#8594;</a
      ><a name="9372"
      > </a
      ><a name="9373" href="StlcProp.html#9360" class="Bound"
      >&#915;</a
      ><a name="9374"
      > </a
      ><a name="9375" href="Stlc.html#3094" class="Datatype Operator"
      >&#8866;</a
      ><a name="9376"
      > </a
      ><a name="9377" href="StlcProp.html#9356" class="Bound"
      >M</a
      ><a name="9378"
      > </a
      ><a name="9379" href="Stlc.html#3094" class="Datatype Operator"
      >&#8758;</a
      ><a name="9380"
      > </a
      ><a name="9381" href="StlcProp.html#9358" class="Bound"
      >A</a
      ><a name="9382"
      > </a
      ><a name="9383" class="Symbol"
      >&#8594;</a
      ><a name="9384"
      > </a
      ><a name="9385" href="https://agda.github.io/agda-stdlib/Data.Product.html#823" class="Function"
      >&#8707;</a
      ><a name="9386"
      > </a
      ><a name="9387" class="Symbol"
      >&#955;</a
      ><a name="9388"
      > </a
      ><a name="9389" href="StlcProp.html#9389" class="Bound"
      >B</a
      ><a name="9390"
      > </a
      ><a name="9391" class="Symbol"
      >&#8594;</a
      ><a name="9392"
      > </a
      ><a name="9393" href="StlcProp.html#9360" class="Bound"
      >&#915;</a
      ><a name="9394"
      > </a
      ><a name="9395" href="StlcProp.html#9354" class="Bound"
      >x</a
      ><a name="9396"
      > </a
      ><a name="9397" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="9398"
      > </a
      ><a name="9399" href="https://agda.github.io/agda-stdlib/Data.Maybe.Base.html#373" class="InductiveConstructor"
      >just</a
      ><a name="9403"
      > </a
      ><a name="9404" href="StlcProp.html#9389" class="Bound"
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
<a name="10867" href="StlcProp.html#9339" class="Function"
      >freeLemma</a
      ><a name="10876"
      > </a
      ><a name="10877" href="StlcProp.html#7604" class="InductiveConstructor"
      >free-var</a
      ><a name="10885"
      > </a
      ><a name="10886" class="Symbol"
      >(</a
      ><a name="10887" href="Stlc.html#3138" class="InductiveConstructor"
      >Ax</a
      ><a name="10889"
      > </a
      ><a name="10890" href="StlcProp.html#10890" class="Bound"
      >&#915;x&#8801;justA</a
      ><a name="10898" class="Symbol"
      >)</a
      ><a name="10899"
      > </a
      ><a name="10900" class="Symbol"
      >=</a
      ><a name="10901"
      > </a
      ><a name="10902" class="Symbol"
      >(_</a
      ><a name="10904"
      > </a
      ><a name="10905" href="https://agda.github.io/agda-stdlib/Data.Product.html#509" class="InductiveConstructor Operator"
      >,</a
      ><a name="10906"
      > </a
      ><a name="10907" href="StlcProp.html#10890" class="Bound"
      >&#915;x&#8801;justA</a
      ><a name="10915" class="Symbol"
      >)</a
      ><a name="10916"
      >
</a
      ><a name="10917" href="StlcProp.html#9339" class="Function"
      >freeLemma</a
      ><a name="10926"
      > </a
      ><a name="10927" class="Symbol"
      >(</a
      ><a name="10928" href="StlcProp.html#7697" class="InductiveConstructor"
      >free-&#183;&#8321;</a
      ><a name="10935"
      > </a
      ><a name="10936" href="StlcProp.html#10936" class="Bound"
      >x&#8712;L</a
      ><a name="10939" class="Symbol"
      >)</a
      ><a name="10940"
      > </a
      ><a name="10941" class="Symbol"
      >(</a
      ><a name="10942" href="Stlc.html#3271" class="InductiveConstructor"
      >&#8658;-E</a
      ><a name="10945"
      > </a
      ><a name="10946" href="StlcProp.html#10946" class="Bound"
      >&#8866;L</a
      ><a name="10948"
      > </a
      ><a name="10949" href="StlcProp.html#10949" class="Bound"
      >&#8866;M</a
      ><a name="10951" class="Symbol"
      >)</a
      ><a name="10952"
      > </a
      ><a name="10953" class="Symbol"
      >=</a
      ><a name="10954"
      > </a
      ><a name="10955" href="StlcProp.html#9339" class="Function"
      >freeLemma</a
      ><a name="10964"
      > </a
      ><a name="10965" href="StlcProp.html#10936" class="Bound"
      >x&#8712;L</a
      ><a name="10968"
      > </a
      ><a name="10969" href="StlcProp.html#10946" class="Bound"
      >&#8866;L</a
      ><a name="10971"
      >
</a
      ><a name="10972" href="StlcProp.html#9339" class="Function"
      >freeLemma</a
      ><a name="10981"
      > </a
      ><a name="10982" class="Symbol"
      >(</a
      ><a name="10983" href="StlcProp.html#7741" class="InductiveConstructor"
      >free-&#183;&#8322;</a
      ><a name="10990"
      > </a
      ><a name="10991" href="StlcProp.html#10991" class="Bound"
      >x&#8712;M</a
      ><a name="10994" class="Symbol"
      >)</a
      ><a name="10995"
      > </a
      ><a name="10996" class="Symbol"
      >(</a
      ><a name="10997" href="Stlc.html#3271" class="InductiveConstructor"
      >&#8658;-E</a
      ><a name="11000"
      > </a
      ><a name="11001" href="StlcProp.html#11001" class="Bound"
      >&#8866;L</a
      ><a name="11003"
      > </a
      ><a name="11004" href="StlcProp.html#11004" class="Bound"
      >&#8866;M</a
      ><a name="11006" class="Symbol"
      >)</a
      ><a name="11007"
      > </a
      ><a name="11008" class="Symbol"
      >=</a
      ><a name="11009"
      > </a
      ><a name="11010" href="StlcProp.html#9339" class="Function"
      >freeLemma</a
      ><a name="11019"
      > </a
      ><a name="11020" href="StlcProp.html#10991" class="Bound"
      >x&#8712;M</a
      ><a name="11023"
      > </a
      ><a name="11024" href="StlcProp.html#11004" class="Bound"
      >&#8866;M</a
      ><a name="11026"
      >
</a
      ><a name="11027" href="StlcProp.html#9339" class="Function"
      >freeLemma</a
      ><a name="11036"
      > </a
      ><a name="11037" class="Symbol"
      >(</a
      ><a name="11038" href="StlcProp.html#7785" class="InductiveConstructor"
      >free-if&#8321;</a
      ><a name="11046"
      > </a
      ><a name="11047" href="StlcProp.html#11047" class="Bound"
      >x&#8712;L</a
      ><a name="11050" class="Symbol"
      >)</a
      ><a name="11051"
      > </a
      ><a name="11052" class="Symbol"
      >(</a
      ><a name="11053" href="Stlc.html#3418" class="InductiveConstructor"
      >&#120121;-E</a
      ><a name="11056"
      > </a
      ><a name="11057" href="StlcProp.html#11057" class="Bound"
      >&#8866;L</a
      ><a name="11059"
      > </a
      ><a name="11060" href="StlcProp.html#11060" class="Bound"
      >&#8866;M</a
      ><a name="11062"
      > </a
      ><a name="11063" href="StlcProp.html#11063" class="Bound"
      >&#8866;N</a
      ><a name="11065" class="Symbol"
      >)</a
      ><a name="11066"
      > </a
      ><a name="11067" class="Symbol"
      >=</a
      ><a name="11068"
      > </a
      ><a name="11069" href="StlcProp.html#9339" class="Function"
      >freeLemma</a
      ><a name="11078"
      > </a
      ><a name="11079" href="StlcProp.html#11047" class="Bound"
      >x&#8712;L</a
      ><a name="11082"
      > </a
      ><a name="11083" href="StlcProp.html#11057" class="Bound"
      >&#8866;L</a
      ><a name="11085"
      >
</a
      ><a name="11086" href="StlcProp.html#9339" class="Function"
      >freeLemma</a
      ><a name="11095"
      > </a
      ><a name="11096" class="Symbol"
      >(</a
      ><a name="11097" href="StlcProp.html#7845" class="InductiveConstructor"
      >free-if&#8322;</a
      ><a name="11105"
      > </a
      ><a name="11106" href="StlcProp.html#11106" class="Bound"
      >x&#8712;M</a
      ><a name="11109" class="Symbol"
      >)</a
      ><a name="11110"
      > </a
      ><a name="11111" class="Symbol"
      >(</a
      ><a name="11112" href="Stlc.html#3418" class="InductiveConstructor"
      >&#120121;-E</a
      ><a name="11115"
      > </a
      ><a name="11116" href="StlcProp.html#11116" class="Bound"
      >&#8866;L</a
      ><a name="11118"
      > </a
      ><a name="11119" href="StlcProp.html#11119" class="Bound"
      >&#8866;M</a
      ><a name="11121"
      > </a
      ><a name="11122" href="StlcProp.html#11122" class="Bound"
      >&#8866;N</a
      ><a name="11124" class="Symbol"
      >)</a
      ><a name="11125"
      > </a
      ><a name="11126" class="Symbol"
      >=</a
      ><a name="11127"
      > </a
      ><a name="11128" href="StlcProp.html#9339" class="Function"
      >freeLemma</a
      ><a name="11137"
      > </a
      ><a name="11138" href="StlcProp.html#11106" class="Bound"
      >x&#8712;M</a
      ><a name="11141"
      > </a
      ><a name="11142" href="StlcProp.html#11119" class="Bound"
      >&#8866;M</a
      ><a name="11144"
      >
</a
      ><a name="11145" href="StlcProp.html#9339" class="Function"
      >freeLemma</a
      ><a name="11154"
      > </a
      ><a name="11155" class="Symbol"
      >(</a
      ><a name="11156" href="StlcProp.html#7905" class="InductiveConstructor"
      >free-if&#8323;</a
      ><a name="11164"
      > </a
      ><a name="11165" href="StlcProp.html#11165" class="Bound"
      >x&#8712;N</a
      ><a name="11168" class="Symbol"
      >)</a
      ><a name="11169"
      > </a
      ><a name="11170" class="Symbol"
      >(</a
      ><a name="11171" href="Stlc.html#3418" class="InductiveConstructor"
      >&#120121;-E</a
      ><a name="11174"
      > </a
      ><a name="11175" href="StlcProp.html#11175" class="Bound"
      >&#8866;L</a
      ><a name="11177"
      > </a
      ><a name="11178" href="StlcProp.html#11178" class="Bound"
      >&#8866;M</a
      ><a name="11180"
      > </a
      ><a name="11181" href="StlcProp.html#11181" class="Bound"
      >&#8866;N</a
      ><a name="11183" class="Symbol"
      >)</a
      ><a name="11184"
      > </a
      ><a name="11185" class="Symbol"
      >=</a
      ><a name="11186"
      > </a
      ><a name="11187" href="StlcProp.html#9339" class="Function"
      >freeLemma</a
      ><a name="11196"
      > </a
      ><a name="11197" href="StlcProp.html#11165" class="Bound"
      >x&#8712;N</a
      ><a name="11200"
      > </a
      ><a name="11201" href="StlcProp.html#11181" class="Bound"
      >&#8866;N</a
      ><a name="11203"
      >
</a
      ><a name="11204" href="StlcProp.html#9339" class="Function"
      >freeLemma</a
      ><a name="11213"
      > </a
      ><a name="11214" class="Symbol"
      >(</a
      ><a name="11215" href="StlcProp.html#7636" class="InductiveConstructor"
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
      ><a name="11240" href="Stlc.html#3194" class="InductiveConstructor"
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
      ><a name="11253" href="StlcProp.html#9339" class="Function"
      >freeLemma</a
      ><a name="11262"
      > </a
      ><a name="11263" href="StlcProp.html#11234" class="Bound"
      >x&#8712;N</a
      ><a name="11266"
      > </a
      ><a name="11267" href="StlcProp.html#11244" class="Bound"
      >&#8866;N</a
      ><a name="11269"
      >
</a
      ><a name="11270" class="Symbol"
      >...</a
      ><a name="11273"
      > </a
      ><a name="11274" class="Symbol"
      >|</a
      ><a name="11275"
      > </a
      ><a name="11276" href="StlcProp.html#11276" class="Bound"
      >&#915;x=justC</a
      ><a name="11284"
      > </a
      ><a name="11285" class="Keyword"
      >with</a
      ><a name="11289"
      > </a
      ><a name="11290" href="StlcProp.html#11227" class="Bound"
      >y</a
      ><a name="11291"
      > </a
      ><a name="11292" href="Maps.html#2509" class="Function Operator"
      >&#8799;</a
      ><a name="11293"
      > </a
      ><a name="11294" href="StlcProp.html#11223" class="Bound"
      >x</a
      ><a name="11295"
      >
</a
      ><a name="11296" class="Symbol"
      >...</a
      ><a name="11299"
      > </a
      ><a name="11300" class="Symbol"
      >|</a
      ><a name="11301"
      > </a
      ><a name="11302" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#520" class="InductiveConstructor"
      >yes</a
      ><a name="11305"
      > </a
      ><a name="11306" href="StlcProp.html#11306" class="Bound"
      >y&#8801;x</a
      ><a name="11309"
      > </a
      ><a name="11310" class="Symbol"
      >=</a
      ><a name="11311"
      > </a
      ><a name="11312" href="https://agda.github.io/agda-stdlib/Data.Empty.html#348" class="Function"
      >&#8869;-elim</a
      ><a name="11318"
      > </a
      ><a name="11319" class="Symbol"
      >(</a
      ><a name="11320" href="StlcProp.html#11230" class="Bound"
      >y&#8802;x</a
      ><a name="11323"
      > </a
      ><a name="11324" href="StlcProp.html#11306" class="Bound"
      >y&#8801;x</a
      ><a name="11327" class="Symbol"
      >)</a
      ><a name="11328"
      >
</a
      ><a name="11329" class="Symbol"
      >...</a
      ><a name="11332"
      > </a
      ><a name="11333" class="Symbol"
      >|</a
      ><a name="11334"
      > </a
      ><a name="11335" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#547" class="InductiveConstructor"
      >no</a
      ><a name="11337"
      >  </a
      ><a name="11339" class="Symbol"
      >_</a
      ><a name="11340"
      >   </a
      ><a name="11343" class="Symbol"
      >=</a
      ><a name="11344"
      > </a
      ><a name="11345" href="StlcProp.html#11276" class="Bound"
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
<a name="11717" class="Keyword"
      >postulate</a
      ><a name="11726"
      >
  </a
      ><a name="11729" href="StlcProp.html#11729" class="Postulate"
      >&#8709;&#8866;-closed</a
      ><a name="11738"
      > </a
      ><a name="11739" class="Symbol"
      >:</a
      ><a name="11740"
      > </a
      ><a name="11741" class="Symbol"
      >&#8704;</a
      ><a name="11742"
      > </a
      ><a name="11743" class="Symbol"
      >{</a
      ><a name="11744" href="StlcProp.html#11744" class="Bound"
      >M</a
      ><a name="11745"
      > </a
      ><a name="11746" href="StlcProp.html#11746" class="Bound"
      >A</a
      ><a name="11747" class="Symbol"
      >}</a
      ><a name="11748"
      > </a
      ><a name="11749" class="Symbol"
      >&#8594;</a
      ><a name="11750"
      > </a
      ><a name="11751" href="Maps.html#10265" class="Function"
      >&#8709;</a
      ><a name="11752"
      > </a
      ><a name="11753" href="Stlc.html#3094" class="Datatype Operator"
      >&#8866;</a
      ><a name="11754"
      > </a
      ><a name="11755" href="StlcProp.html#11744" class="Bound"
      >M</a
      ><a name="11756"
      > </a
      ><a name="11757" href="Stlc.html#3094" class="Datatype Operator"
      >&#8758;</a
      ><a name="11758"
      > </a
      ><a name="11759" href="StlcProp.html#11746" class="Bound"
      >A</a
      ><a name="11760"
      > </a
      ><a name="11761" class="Symbol"
      >&#8594;</a
      ><a name="11762"
      > </a
      ><a name="11763" href="StlcProp.html#8095" class="Function"
      >closed</a
      ><a name="11769"
      > </a
      ><a name="11770" href="StlcProp.html#11744" class="Bound"
      >M</a
      >
{% endraw %}</pre>

<div class="hidden">
<pre class="Agda">{% raw %}
<a name="11818" href="StlcProp.html#11818" class="Function"
      >contradiction</a
      ><a name="11831"
      > </a
      ><a name="11832" class="Symbol"
      >:</a
      ><a name="11833"
      > </a
      ><a name="11834" class="Symbol"
      >&#8704;</a
      ><a name="11835"
      > </a
      ><a name="11836" class="Symbol"
      >{</a
      ><a name="11837" href="StlcProp.html#11837" class="Bound"
      >X</a
      ><a name="11838"
      > </a
      ><a name="11839" class="Symbol"
      >:</a
      ><a name="11840"
      > </a
      ><a name="11841" class="PrimitiveType"
      >Set</a
      ><a name="11844" class="Symbol"
      >}</a
      ><a name="11845"
      > </a
      ><a name="11846" class="Symbol"
      >&#8594;</a
      ><a name="11847"
      > </a
      ><a name="11848" class="Symbol"
      >&#8704;</a
      ><a name="11849"
      > </a
      ><a name="11850" class="Symbol"
      >{</a
      ><a name="11851" href="StlcProp.html#11851" class="Bound"
      >x</a
      ><a name="11852"
      > </a
      ><a name="11853" class="Symbol"
      >:</a
      ><a name="11854"
      > </a
      ><a name="11855" href="StlcProp.html#11837" class="Bound"
      >X</a
      ><a name="11856" class="Symbol"
      >}</a
      ><a name="11857"
      > </a
      ><a name="11858" class="Symbol"
      >&#8594;</a
      ><a name="11859"
      > </a
      ><a name="11860" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#414" class="Function Operator"
      >&#172;</a
      ><a name="11861"
      > </a
      ><a name="11862" class="Symbol"
      >(</a
      ><a name="11863" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >_&#8801;_</a
      ><a name="11866"
      > </a
      ><a name="11867" class="Symbol"
      >{</a
      ><a name="11868" class="Argument"
      >A</a
      ><a name="11869"
      > </a
      ><a name="11870" class="Symbol"
      >=</a
      ><a name="11871"
      > </a
      ><a name="11872" href="https://agda.github.io/agda-stdlib/Data.Maybe.Base.html#335" class="Datatype"
      >Maybe</a
      ><a name="11877"
      > </a
      ><a name="11878" href="StlcProp.html#11837" class="Bound"
      >X</a
      ><a name="11879" class="Symbol"
      >}</a
      ><a name="11880"
      > </a
      ><a name="11881" class="Symbol"
      >(</a
      ><a name="11882" href="https://agda.github.io/agda-stdlib/Data.Maybe.Base.html#373" class="InductiveConstructor"
      >just</a
      ><a name="11886"
      > </a
      ><a name="11887" href="StlcProp.html#11851" class="Bound"
      >x</a
      ><a name="11888" class="Symbol"
      >)</a
      ><a name="11889"
      > </a
      ><a name="11890" href="https://agda.github.io/agda-stdlib/Data.Maybe.Base.html#403" class="InductiveConstructor"
      >nothing</a
      ><a name="11897" class="Symbol"
      >)</a
      ><a name="11898"
      >
</a
      ><a name="11899" href="StlcProp.html#11818" class="Function"
      >contradiction</a
      ><a name="11912"
      > </a
      ><a name="11913" class="Symbol"
      >()</a
      ><a name="11915"
      >

</a
      ><a name="11917" href="StlcProp.html#11917" class="Function"
      >&#8709;&#8866;-closed&#8242;</a
      ><a name="11927"
      > </a
      ><a name="11928" class="Symbol"
      >:</a
      ><a name="11929"
      > </a
      ><a name="11930" class="Symbol"
      >&#8704;</a
      ><a name="11931"
      > </a
      ><a name="11932" class="Symbol"
      >{</a
      ><a name="11933" href="StlcProp.html#11933" class="Bound"
      >M</a
      ><a name="11934"
      > </a
      ><a name="11935" href="StlcProp.html#11935" class="Bound"
      >A</a
      ><a name="11936" class="Symbol"
      >}</a
      ><a name="11937"
      > </a
      ><a name="11938" class="Symbol"
      >&#8594;</a
      ><a name="11939"
      > </a
      ><a name="11940" href="Maps.html#10265" class="Function"
      >&#8709;</a
      ><a name="11941"
      > </a
      ><a name="11942" href="Stlc.html#3094" class="Datatype Operator"
      >&#8866;</a
      ><a name="11943"
      > </a
      ><a name="11944" href="StlcProp.html#11933" class="Bound"
      >M</a
      ><a name="11945"
      > </a
      ><a name="11946" href="Stlc.html#3094" class="Datatype Operator"
      >&#8758;</a
      ><a name="11947"
      > </a
      ><a name="11948" href="StlcProp.html#11935" class="Bound"
      >A</a
      ><a name="11949"
      > </a
      ><a name="11950" class="Symbol"
      >&#8594;</a
      ><a name="11951"
      > </a
      ><a name="11952" href="StlcProp.html#8095" class="Function"
      >closed</a
      ><a name="11958"
      > </a
      ><a name="11959" href="StlcProp.html#11933" class="Bound"
      >M</a
      ><a name="11960"
      >
</a
      ><a name="11961" href="StlcProp.html#11917" class="Function"
      >&#8709;&#8866;-closed&#8242;</a
      ><a name="11971"
      > </a
      ><a name="11972" class="Symbol"
      >{</a
      ><a name="11973" href="StlcProp.html#11973" class="Bound"
      >M</a
      ><a name="11974" class="Symbol"
      >}</a
      ><a name="11975"
      > </a
      ><a name="11976" class="Symbol"
      >{</a
      ><a name="11977" href="StlcProp.html#11977" class="Bound"
      >A</a
      ><a name="11978" class="Symbol"
      >}</a
      ><a name="11979"
      > </a
      ><a name="11980" href="StlcProp.html#11980" class="Bound"
      >&#8866;M</a
      ><a name="11982"
      > </a
      ><a name="11983" class="Symbol"
      >{</a
      ><a name="11984" href="StlcProp.html#11984" class="Bound"
      >x</a
      ><a name="11985" class="Symbol"
      >}</a
      ><a name="11986"
      > </a
      ><a name="11987" href="StlcProp.html#11987" class="Bound"
      >x&#8712;M</a
      ><a name="11990"
      > </a
      ><a name="11991" class="Keyword"
      >with</a
      ><a name="11995"
      > </a
      ><a name="11996" href="StlcProp.html#9339" class="Function"
      >freeLemma</a
      ><a name="12005"
      > </a
      ><a name="12006" href="StlcProp.html#11987" class="Bound"
      >x&#8712;M</a
      ><a name="12009"
      > </a
      ><a name="12010" href="StlcProp.html#11980" class="Bound"
      >&#8866;M</a
      ><a name="12012"
      >
</a
      ><a name="12013" class="Symbol"
      >...</a
      ><a name="12016"
      > </a
      ><a name="12017" class="Symbol"
      >|</a
      ><a name="12018"
      > </a
      ><a name="12019" class="Symbol"
      >(</a
      ><a name="12020" href="StlcProp.html#12020" class="Bound"
      >B</a
      ><a name="12021"
      > </a
      ><a name="12022" href="https://agda.github.io/agda-stdlib/Data.Product.html#509" class="InductiveConstructor Operator"
      >,</a
      ><a name="12023"
      > </a
      ><a name="12024" href="StlcProp.html#12024" class="Bound"
      >&#8709;x&#8801;justB</a
      ><a name="12032" class="Symbol"
      >)</a
      ><a name="12033"
      > </a
      ><a name="12034" class="Symbol"
      >=</a
      ><a name="12035"
      > </a
      ><a name="12036" href="StlcProp.html#11818" class="Function"
      >contradiction</a
      ><a name="12049"
      > </a
      ><a name="12050" class="Symbol"
      >(</a
      ><a name="12051" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.Core.html#632" class="Function"
      >trans</a
      ><a name="12056"
      > </a
      ><a name="12057" class="Symbol"
      >(</a
      ><a name="12058" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.Core.html#565" class="Function"
      >sym</a
      ><a name="12061"
      > </a
      ><a name="12062" href="StlcProp.html#12024" class="Bound"
      >&#8709;x&#8801;justB</a
      ><a name="12070" class="Symbol"
      >)</a
      ><a name="12071"
      > </a
      ><a name="12072" class="Symbol"
      >(</a
      ><a name="12073" href="Maps.html#10573" class="Function"
      >apply-&#8709;</a
      ><a name="12080"
      > </a
      ><a name="12081" href="StlcProp.html#11984" class="Bound"
      >x</a
      ><a name="12082" class="Symbol"
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
<a name="12430" href="StlcProp.html#12430" class="Function"
      >contextLemma</a
      ><a name="12442"
      > </a
      ><a name="12443" class="Symbol"
      >:</a
      ><a name="12444"
      > </a
      ><a name="12445" class="Symbol"
      >&#8704;</a
      ><a name="12446"
      > </a
      ><a name="12447" class="Symbol"
      >{</a
      ><a name="12448" href="StlcProp.html#12448" class="Bound"
      >&#915;</a
      ><a name="12449"
      > </a
      ><a name="12450" href="StlcProp.html#12450" class="Bound"
      >&#915;&#8242;</a
      ><a name="12452"
      > </a
      ><a name="12453" href="StlcProp.html#12453" class="Bound"
      >M</a
      ><a name="12454"
      > </a
      ><a name="12455" href="StlcProp.html#12455" class="Bound"
      >A</a
      ><a name="12456" class="Symbol"
      >}</a
      ><a name="12457"
      >
        </a
      ><a name="12466" class="Symbol"
      >&#8594;</a
      ><a name="12467"
      > </a
      ><a name="12468" class="Symbol"
      >(&#8704;</a
      ><a name="12470"
      > </a
      ><a name="12471" class="Symbol"
      >{</a
      ><a name="12472" href="StlcProp.html#12472" class="Bound"
      >x</a
      ><a name="12473" class="Symbol"
      >}</a
      ><a name="12474"
      > </a
      ><a name="12475" class="Symbol"
      >&#8594;</a
      ><a name="12476"
      > </a
      ><a name="12477" href="StlcProp.html#12472" class="Bound"
      >x</a
      ><a name="12478"
      > </a
      ><a name="12479" href="StlcProp.html#7574" class="Datatype Operator"
      >&#8712;</a
      ><a name="12480"
      > </a
      ><a name="12481" href="StlcProp.html#12453" class="Bound"
      >M</a
      ><a name="12482"
      > </a
      ><a name="12483" class="Symbol"
      >&#8594;</a
      ><a name="12484"
      > </a
      ><a name="12485" href="StlcProp.html#12448" class="Bound"
      >&#915;</a
      ><a name="12486"
      > </a
      ><a name="12487" href="StlcProp.html#12472" class="Bound"
      >x</a
      ><a name="12488"
      > </a
      ><a name="12489" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="12490"
      > </a
      ><a name="12491" href="StlcProp.html#12450" class="Bound"
      >&#915;&#8242;</a
      ><a name="12493"
      > </a
      ><a name="12494" href="StlcProp.html#12472" class="Bound"
      >x</a
      ><a name="12495" class="Symbol"
      >)</a
      ><a name="12496"
      >
        </a
      ><a name="12505" class="Symbol"
      >&#8594;</a
      ><a name="12506"
      > </a
      ><a name="12507" href="StlcProp.html#12448" class="Bound"
      >&#915;</a
      ><a name="12508"
      >  </a
      ><a name="12510" href="Stlc.html#3094" class="Datatype Operator"
      >&#8866;</a
      ><a name="12511"
      > </a
      ><a name="12512" href="StlcProp.html#12453" class="Bound"
      >M</a
      ><a name="12513"
      > </a
      ><a name="12514" href="Stlc.html#3094" class="Datatype Operator"
      >&#8758;</a
      ><a name="12515"
      > </a
      ><a name="12516" href="StlcProp.html#12455" class="Bound"
      >A</a
      ><a name="12517"
      >
        </a
      ><a name="12526" class="Symbol"
      >&#8594;</a
      ><a name="12527"
      > </a
      ><a name="12528" href="StlcProp.html#12450" class="Bound"
      >&#915;&#8242;</a
      ><a name="12530"
      > </a
      ><a name="12531" href="Stlc.html#3094" class="Datatype Operator"
      >&#8866;</a
      ><a name="12532"
      > </a
      ><a name="12533" href="StlcProp.html#12453" class="Bound"
      >M</a
      ><a name="12534"
      > </a
      ><a name="12535" href="Stlc.html#3094" class="Datatype Operator"
      >&#8758;</a
      ><a name="12536"
      > </a
      ><a name="12537" href="StlcProp.html#12455" class="Bound"
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
<a name="14704" href="StlcProp.html#12430" class="Function"
      >contextLemma</a
      ><a name="14716"
      > </a
      ><a name="14717" href="StlcProp.html#14717" class="Bound"
      >&#915;~&#915;&#8242;</a
      ><a name="14721"
      > </a
      ><a name="14722" class="Symbol"
      >(</a
      ><a name="14723" href="Stlc.html#3138" class="InductiveConstructor"
      >Ax</a
      ><a name="14725"
      > </a
      ><a name="14726" href="StlcProp.html#14726" class="Bound"
      >&#915;x&#8801;justA</a
      ><a name="14734" class="Symbol"
      >)</a
      ><a name="14735"
      > </a
      ><a name="14736" class="Keyword"
      >rewrite</a
      ><a name="14743"
      > </a
      ><a name="14744" class="Symbol"
      >(</a
      ><a name="14745" href="StlcProp.html#14717" class="Bound"
      >&#915;~&#915;&#8242;</a
      ><a name="14749"
      > </a
      ><a name="14750" href="StlcProp.html#7604" class="InductiveConstructor"
      >free-var</a
      ><a name="14758" class="Symbol"
      >)</a
      ><a name="14759"
      > </a
      ><a name="14760" class="Symbol"
      >=</a
      ><a name="14761"
      > </a
      ><a name="14762" href="Stlc.html#3138" class="InductiveConstructor"
      >Ax</a
      ><a name="14764"
      > </a
      ><a name="14765" href="StlcProp.html#14726" class="Bound"
      >&#915;x&#8801;justA</a
      ><a name="14773"
      >
</a
      ><a name="14774" href="StlcProp.html#12430" class="Function"
      >contextLemma</a
      ><a name="14786"
      > </a
      ><a name="14787" class="Symbol"
      >{</a
      ><a name="14788" href="StlcProp.html#14788" class="Bound"
      >&#915;</a
      ><a name="14789" class="Symbol"
      >}</a
      ><a name="14790"
      > </a
      ><a name="14791" class="Symbol"
      >{</a
      ><a name="14792" href="StlcProp.html#14792" class="Bound"
      >&#915;&#8242;</a
      ><a name="14794" class="Symbol"
      >}</a
      ><a name="14795"
      > </a
      ><a name="14796" class="Symbol"
      >{</a
      ><a name="14797" href="Stlc.html#745" class="InductiveConstructor Operator"
      >&#955;[</a
      ><a name="14799"
      > </a
      ><a name="14800" href="StlcProp.html#14800" class="Bound"
      >x</a
      ><a name="14801"
      > </a
      ><a name="14802" href="Stlc.html#745" class="InductiveConstructor Operator"
      >&#8758;</a
      ><a name="14803"
      > </a
      ><a name="14804" href="StlcProp.html#14804" class="Bound"
      >A</a
      ><a name="14805"
      > </a
      ><a name="14806" href="Stlc.html#745" class="InductiveConstructor Operator"
      >]</a
      ><a name="14807"
      > </a
      ><a name="14808" href="StlcProp.html#14808" class="Bound"
      >N</a
      ><a name="14809" class="Symbol"
      >}</a
      ><a name="14810"
      > </a
      ><a name="14811" href="StlcProp.html#14811" class="Bound"
      >&#915;~&#915;&#8242;</a
      ><a name="14815"
      > </a
      ><a name="14816" class="Symbol"
      >(</a
      ><a name="14817" href="Stlc.html#3194" class="InductiveConstructor"
      >&#8658;-I</a
      ><a name="14820"
      > </a
      ><a name="14821" href="StlcProp.html#14821" class="Bound"
      >&#8866;N</a
      ><a name="14823" class="Symbol"
      >)</a
      ><a name="14824"
      > </a
      ><a name="14825" class="Symbol"
      >=</a
      ><a name="14826"
      > </a
      ><a name="14827" href="Stlc.html#3194" class="InductiveConstructor"
      >&#8658;-I</a
      ><a name="14830"
      > </a
      ><a name="14831" class="Symbol"
      >(</a
      ><a name="14832" href="StlcProp.html#12430" class="Function"
      >contextLemma</a
      ><a name="14844"
      > </a
      ><a name="14845" href="StlcProp.html#14866" class="Function"
      >&#915;x~&#915;&#8242;x</a
      ><a name="14851"
      > </a
      ><a name="14852" href="StlcProp.html#14821" class="Bound"
      >&#8866;N</a
      ><a name="14854" class="Symbol"
      >)</a
      ><a name="14855"
      >
  </a
      ><a name="14858" class="Keyword"
      >where</a
      ><a name="14863"
      >
  </a
      ><a name="14866" href="StlcProp.html#14866" class="Function"
      >&#915;x~&#915;&#8242;x</a
      ><a name="14872"
      > </a
      ><a name="14873" class="Symbol"
      >:</a
      ><a name="14874"
      > </a
      ><a name="14875" class="Symbol"
      >&#8704;</a
      ><a name="14876"
      > </a
      ><a name="14877" class="Symbol"
      >{</a
      ><a name="14878" href="StlcProp.html#14878" class="Bound"
      >y</a
      ><a name="14879" class="Symbol"
      >}</a
      ><a name="14880"
      > </a
      ><a name="14881" class="Symbol"
      >&#8594;</a
      ><a name="14882"
      > </a
      ><a name="14883" href="StlcProp.html#14878" class="Bound"
      >y</a
      ><a name="14884"
      > </a
      ><a name="14885" href="StlcProp.html#7574" class="Datatype Operator"
      >&#8712;</a
      ><a name="14886"
      > </a
      ><a name="14887" href="StlcProp.html#14808" class="Bound"
      >N</a
      ><a name="14888"
      > </a
      ><a name="14889" class="Symbol"
      >&#8594;</a
      ><a name="14890"
      > </a
      ><a name="14891" class="Symbol"
      >(</a
      ><a name="14892" href="StlcProp.html#14788" class="Bound"
      >&#915;</a
      ><a name="14893"
      > </a
      ><a name="14894" href="Maps.html#10368" class="Function Operator"
      >,</a
      ><a name="14895"
      > </a
      ><a name="14896" href="StlcProp.html#14800" class="Bound"
      >x</a
      ><a name="14897"
      > </a
      ><a name="14898" href="Maps.html#10368" class="Function Operator"
      >&#8758;</a
      ><a name="14899"
      > </a
      ><a name="14900" href="StlcProp.html#14804" class="Bound"
      >A</a
      ><a name="14901" class="Symbol"
      >)</a
      ><a name="14902"
      > </a
      ><a name="14903" href="StlcProp.html#14878" class="Bound"
      >y</a
      ><a name="14904"
      > </a
      ><a name="14905" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="14906"
      > </a
      ><a name="14907" class="Symbol"
      >(</a
      ><a name="14908" href="StlcProp.html#14792" class="Bound"
      >&#915;&#8242;</a
      ><a name="14910"
      > </a
      ><a name="14911" href="Maps.html#10368" class="Function Operator"
      >,</a
      ><a name="14912"
      > </a
      ><a name="14913" href="StlcProp.html#14800" class="Bound"
      >x</a
      ><a name="14914"
      > </a
      ><a name="14915" href="Maps.html#10368" class="Function Operator"
      >&#8758;</a
      ><a name="14916"
      > </a
      ><a name="14917" href="StlcProp.html#14804" class="Bound"
      >A</a
      ><a name="14918" class="Symbol"
      >)</a
      ><a name="14919"
      > </a
      ><a name="14920" href="StlcProp.html#14878" class="Bound"
      >y</a
      ><a name="14921"
      >
  </a
      ><a name="14924" href="StlcProp.html#14866" class="Function"
      >&#915;x~&#915;&#8242;x</a
      ><a name="14930"
      > </a
      ><a name="14931" class="Symbol"
      >{</a
      ><a name="14932" href="StlcProp.html#14932" class="Bound"
      >y</a
      ><a name="14933" class="Symbol"
      >}</a
      ><a name="14934"
      > </a
      ><a name="14935" href="StlcProp.html#14935" class="Bound"
      >y&#8712;N</a
      ><a name="14938"
      > </a
      ><a name="14939" class="Keyword"
      >with</a
      ><a name="14943"
      > </a
      ><a name="14944" href="StlcProp.html#14800" class="Bound"
      >x</a
      ><a name="14945"
      > </a
      ><a name="14946" href="Maps.html#2509" class="Function Operator"
      >&#8799;</a
      ><a name="14947"
      > </a
      ><a name="14948" href="StlcProp.html#14932" class="Bound"
      >y</a
      ><a name="14949"
      >
  </a
      ><a name="14952" class="Symbol"
      >...</a
      ><a name="14955"
      > </a
      ><a name="14956" class="Symbol"
      >|</a
      ><a name="14957"
      > </a
      ><a name="14958" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#520" class="InductiveConstructor"
      >yes</a
      ><a name="14961"
      > </a
      ><a name="14962" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="14966"
      > </a
      ><a name="14967" class="Symbol"
      >=</a
      ><a name="14968"
      > </a
      ><a name="14969" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
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
      ><a name="14982" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#547" class="InductiveConstructor"
      >no</a
      ><a name="14984"
      >  </a
      ><a name="14986" href="StlcProp.html#14986" class="Bound"
      >x&#8802;y</a
      ><a name="14989"
      >  </a
      ><a name="14991" class="Symbol"
      >=</a
      ><a name="14992"
      > </a
      ><a name="14993" href="StlcProp.html#14811" class="Bound"
      >&#915;~&#915;&#8242;</a
      ><a name="14997"
      > </a
      ><a name="14998" class="Symbol"
      >(</a
      ><a name="14999" href="StlcProp.html#7636" class="InductiveConstructor"
      >free-&#955;</a
      ><a name="15005"
      > </a
      ><a name="15006" href="StlcProp.html#14986" class="Bound"
      >x&#8802;y</a
      ><a name="15009"
      > </a
      ><a name="15010" href="StlcProp.html#14935" class="Bound"
      >y&#8712;N</a
      ><a name="15013" class="Symbol"
      >)</a
      ><a name="15014"
      >
</a
      ><a name="15015" href="StlcProp.html#12430" class="Function"
      >contextLemma</a
      ><a name="15027"
      > </a
      ><a name="15028" href="StlcProp.html#15028" class="Bound"
      >&#915;~&#915;&#8242;</a
      ><a name="15032"
      > </a
      ><a name="15033" class="Symbol"
      >(</a
      ><a name="15034" href="Stlc.html#3271" class="InductiveConstructor"
      >&#8658;-E</a
      ><a name="15037"
      > </a
      ><a name="15038" href="StlcProp.html#15038" class="Bound"
      >&#8866;L</a
      ><a name="15040"
      > </a
      ><a name="15041" href="StlcProp.html#15041" class="Bound"
      >&#8866;M</a
      ><a name="15043" class="Symbol"
      >)</a
      ><a name="15044"
      > </a
      ><a name="15045" class="Symbol"
      >=</a
      ><a name="15046"
      > </a
      ><a name="15047" href="Stlc.html#3271" class="InductiveConstructor"
      >&#8658;-E</a
      ><a name="15050"
      > </a
      ><a name="15051" class="Symbol"
      >(</a
      ><a name="15052" href="StlcProp.html#12430" class="Function"
      >contextLemma</a
      ><a name="15064"
      > </a
      ><a name="15065" class="Symbol"
      >(</a
      ><a name="15066" href="StlcProp.html#15028" class="Bound"
      >&#915;~&#915;&#8242;</a
      ><a name="15070"
      > </a
      ><a name="15071" href="https://agda.github.io/agda-stdlib/Function.html#713" class="Function Operator"
      >&#8728;</a
      ><a name="15072"
      > </a
      ><a name="15073" href="StlcProp.html#7697" class="InductiveConstructor"
      >free-&#183;&#8321;</a
      ><a name="15080" class="Symbol"
      >)</a
      ><a name="15081"
      >  </a
      ><a name="15083" href="StlcProp.html#15038" class="Bound"
      >&#8866;L</a
      ><a name="15085" class="Symbol"
      >)</a
      ><a name="15086"
      > </a
      ><a name="15087" class="Symbol"
      >(</a
      ><a name="15088" href="StlcProp.html#12430" class="Function"
      >contextLemma</a
      ><a name="15100"
      > </a
      ><a name="15101" class="Symbol"
      >(</a
      ><a name="15102" href="StlcProp.html#15028" class="Bound"
      >&#915;~&#915;&#8242;</a
      ><a name="15106"
      > </a
      ><a name="15107" href="https://agda.github.io/agda-stdlib/Function.html#713" class="Function Operator"
      >&#8728;</a
      ><a name="15108"
      > </a
      ><a name="15109" href="StlcProp.html#7741" class="InductiveConstructor"
      >free-&#183;&#8322;</a
      ><a name="15116" class="Symbol"
      >)</a
      ><a name="15117"
      > </a
      ><a name="15118" href="StlcProp.html#15041" class="Bound"
      >&#8866;M</a
      ><a name="15120" class="Symbol"
      >)</a
      ><a name="15121"
      > 
</a
      ><a name="15123" href="StlcProp.html#12430" class="Function"
      >contextLemma</a
      ><a name="15135"
      > </a
      ><a name="15136" href="StlcProp.html#15136" class="Bound"
      >&#915;~&#915;&#8242;</a
      ><a name="15140"
      > </a
      ><a name="15141" href="Stlc.html#3349" class="InductiveConstructor"
      >&#120121;-I&#8321;</a
      ><a name="15145"
      > </a
      ><a name="15146" class="Symbol"
      >=</a
      ><a name="15147"
      > </a
      ><a name="15148" href="Stlc.html#3349" class="InductiveConstructor"
      >&#120121;-I&#8321;</a
      ><a name="15152"
      >
</a
      ><a name="15153" href="StlcProp.html#12430" class="Function"
      >contextLemma</a
      ><a name="15165"
      > </a
      ><a name="15166" href="StlcProp.html#15166" class="Bound"
      >&#915;~&#915;&#8242;</a
      ><a name="15170"
      > </a
      ><a name="15171" href="Stlc.html#3383" class="InductiveConstructor"
      >&#120121;-I&#8322;</a
      ><a name="15175"
      > </a
      ><a name="15176" class="Symbol"
      >=</a
      ><a name="15177"
      > </a
      ><a name="15178" href="Stlc.html#3383" class="InductiveConstructor"
      >&#120121;-I&#8322;</a
      ><a name="15182"
      >
</a
      ><a name="15183" href="StlcProp.html#12430" class="Function"
      >contextLemma</a
      ><a name="15195"
      > </a
      ><a name="15196" href="StlcProp.html#15196" class="Bound"
      >&#915;~&#915;&#8242;</a
      ><a name="15200"
      > </a
      ><a name="15201" class="Symbol"
      >(</a
      ><a name="15202" href="Stlc.html#3418" class="InductiveConstructor"
      >&#120121;-E</a
      ><a name="15205"
      > </a
      ><a name="15206" href="StlcProp.html#15206" class="Bound"
      >&#8866;L</a
      ><a name="15208"
      > </a
      ><a name="15209" href="StlcProp.html#15209" class="Bound"
      >&#8866;M</a
      ><a name="15211"
      > </a
      ><a name="15212" href="StlcProp.html#15212" class="Bound"
      >&#8866;N</a
      ><a name="15214" class="Symbol"
      >)</a
      ><a name="15215"
      >
  </a
      ><a name="15218" class="Symbol"
      >=</a
      ><a name="15219"
      > </a
      ><a name="15220" href="Stlc.html#3418" class="InductiveConstructor"
      >&#120121;-E</a
      ><a name="15223"
      > </a
      ><a name="15224" class="Symbol"
      >(</a
      ><a name="15225" href="StlcProp.html#12430" class="Function"
      >contextLemma</a
      ><a name="15237"
      > </a
      ><a name="15238" class="Symbol"
      >(</a
      ><a name="15239" href="StlcProp.html#15196" class="Bound"
      >&#915;~&#915;&#8242;</a
      ><a name="15243"
      > </a
      ><a name="15244" href="https://agda.github.io/agda-stdlib/Function.html#713" class="Function Operator"
      >&#8728;</a
      ><a name="15245"
      > </a
      ><a name="15246" href="StlcProp.html#7785" class="InductiveConstructor"
      >free-if&#8321;</a
      ><a name="15254" class="Symbol"
      >)</a
      ><a name="15255"
      > </a
      ><a name="15256" href="StlcProp.html#15206" class="Bound"
      >&#8866;L</a
      ><a name="15258" class="Symbol"
      >)</a
      ><a name="15259"
      > </a
      ><a name="15260" class="Symbol"
      >(</a
      ><a name="15261" href="StlcProp.html#12430" class="Function"
      >contextLemma</a
      ><a name="15273"
      > </a
      ><a name="15274" class="Symbol"
      >(</a
      ><a name="15275" href="StlcProp.html#15196" class="Bound"
      >&#915;~&#915;&#8242;</a
      ><a name="15279"
      > </a
      ><a name="15280" href="https://agda.github.io/agda-stdlib/Function.html#713" class="Function Operator"
      >&#8728;</a
      ><a name="15281"
      > </a
      ><a name="15282" href="StlcProp.html#7845" class="InductiveConstructor"
      >free-if&#8322;</a
      ><a name="15290" class="Symbol"
      >)</a
      ><a name="15291"
      > </a
      ><a name="15292" href="StlcProp.html#15209" class="Bound"
      >&#8866;M</a
      ><a name="15294" class="Symbol"
      >)</a
      ><a name="15295"
      > </a
      ><a name="15296" class="Symbol"
      >(</a
      ><a name="15297" href="StlcProp.html#12430" class="Function"
      >contextLemma</a
      ><a name="15309"
      > </a
      ><a name="15310" class="Symbol"
      >(</a
      ><a name="15311" href="StlcProp.html#15196" class="Bound"
      >&#915;~&#915;&#8242;</a
      ><a name="15315"
      > </a
      ><a name="15316" href="https://agda.github.io/agda-stdlib/Function.html#713" class="Function Operator"
      >&#8728;</a
      ><a name="15317"
      > </a
      ><a name="15318" href="StlcProp.html#7905" class="InductiveConstructor"
      >free-if&#8323;</a
      ><a name="15326" class="Symbol"
      >)</a
      ><a name="15327"
      > </a
      ><a name="15328" href="StlcProp.html#15212" class="Bound"
      >&#8866;N</a
      ><a name="15330" class="Symbol"
      >)</a
      ><a name="15331"
      >

</a
      ><a name="15333" class="Comment"
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
<a name="16707" href="StlcProp.html#16707" class="Function"
      >preservation-[&#8758;=]</a
      ><a name="16724"
      > </a
      ><a name="16725" class="Symbol"
      >:</a
      ><a name="16726"
      > </a
      ><a name="16727" class="Symbol"
      >&#8704;</a
      ><a name="16728"
      > </a
      ><a name="16729" class="Symbol"
      >{</a
      ><a name="16730" href="StlcProp.html#16730" class="Bound"
      >&#915;</a
      ><a name="16731"
      > </a
      ><a name="16732" href="StlcProp.html#16732" class="Bound"
      >x</a
      ><a name="16733"
      > </a
      ><a name="16734" href="StlcProp.html#16734" class="Bound"
      >A</a
      ><a name="16735"
      > </a
      ><a name="16736" href="StlcProp.html#16736" class="Bound"
      >N</a
      ><a name="16737"
      > </a
      ><a name="16738" href="StlcProp.html#16738" class="Bound"
      >B</a
      ><a name="16739"
      > </a
      ><a name="16740" href="StlcProp.html#16740" class="Bound"
      >V</a
      ><a name="16741" class="Symbol"
      >}</a
      ><a name="16742"
      >
                 </a
      ><a name="16760" class="Symbol"
      >&#8594;</a
      ><a name="16761"
      > </a
      ><a name="16762" class="Symbol"
      >(</a
      ><a name="16763" href="StlcProp.html#16730" class="Bound"
      >&#915;</a
      ><a name="16764"
      > </a
      ><a name="16765" href="Maps.html#10368" class="Function Operator"
      >,</a
      ><a name="16766"
      > </a
      ><a name="16767" href="StlcProp.html#16732" class="Bound"
      >x</a
      ><a name="16768"
      > </a
      ><a name="16769" href="Maps.html#10368" class="Function Operator"
      >&#8758;</a
      ><a name="16770"
      > </a
      ><a name="16771" href="StlcProp.html#16734" class="Bound"
      >A</a
      ><a name="16772" class="Symbol"
      >)</a
      ><a name="16773"
      > </a
      ><a name="16774" href="Stlc.html#3094" class="Datatype Operator"
      >&#8866;</a
      ><a name="16775"
      > </a
      ><a name="16776" href="StlcProp.html#16736" class="Bound"
      >N</a
      ><a name="16777"
      > </a
      ><a name="16778" href="Stlc.html#3094" class="Datatype Operator"
      >&#8758;</a
      ><a name="16779"
      > </a
      ><a name="16780" href="StlcProp.html#16738" class="Bound"
      >B</a
      ><a name="16781"
      >
                 </a
      ><a name="16799" class="Symbol"
      >&#8594;</a
      ><a name="16800"
      > </a
      ><a name="16801" href="Maps.html#10265" class="Function"
      >&#8709;</a
      ><a name="16802"
      > </a
      ><a name="16803" href="Stlc.html#3094" class="Datatype Operator"
      >&#8866;</a
      ><a name="16804"
      > </a
      ><a name="16805" href="StlcProp.html#16740" class="Bound"
      >V</a
      ><a name="16806"
      > </a
      ><a name="16807" href="Stlc.html#3094" class="Datatype Operator"
      >&#8758;</a
      ><a name="16808"
      > </a
      ><a name="16809" href="StlcProp.html#16734" class="Bound"
      >A</a
      ><a name="16810"
      >
                 </a
      ><a name="16828" class="Symbol"
      >&#8594;</a
      ><a name="16829"
      > </a
      ><a name="16830" href="StlcProp.html#16730" class="Bound"
      >&#915;</a
      ><a name="16831"
      > </a
      ><a name="16832" href="Stlc.html#3094" class="Datatype Operator"
      >&#8866;</a
      ><a name="16833"
      > </a
      ><a name="16834" class="Symbol"
      >(</a
      ><a name="16835" href="StlcProp.html#16736" class="Bound"
      >N</a
      ><a name="16836"
      > </a
      ><a name="16837" href="Stlc.html#1286" class="Function Operator"
      >[</a
      ><a name="16838"
      > </a
      ><a name="16839" href="StlcProp.html#16732" class="Bound"
      >x</a
      ><a name="16840"
      > </a
      ><a name="16841" href="Stlc.html#1286" class="Function Operator"
      >&#8758;=</a
      ><a name="16843"
      > </a
      ><a name="16844" href="StlcProp.html#16740" class="Bound"
      >V</a
      ><a name="16845"
      > </a
      ><a name="16846" href="Stlc.html#1286" class="Function Operator"
      >]</a
      ><a name="16847" class="Symbol"
      >)</a
      ><a name="16848"
      > </a
      ><a name="16849" href="Stlc.html#3094" class="Datatype Operator"
      >&#8758;</a
      ><a name="16850"
      > </a
      ><a name="16851" href="StlcProp.html#16738" class="Bound"
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
<a name="19964" href="StlcProp.html#19964" class="Function"
      >weaken-closed</a
      ><a name="19977"
      > </a
      ><a name="19978" class="Symbol"
      >:</a
      ><a name="19979"
      > </a
      ><a name="19980" class="Symbol"
      >&#8704;</a
      ><a name="19981"
      > </a
      ><a name="19982" class="Symbol"
      >{</a
      ><a name="19983" href="StlcProp.html#19983" class="Bound"
      >V</a
      ><a name="19984"
      > </a
      ><a name="19985" href="StlcProp.html#19985" class="Bound"
      >A</a
      ><a name="19986"
      > </a
      ><a name="19987" href="StlcProp.html#19987" class="Bound"
      >&#915;</a
      ><a name="19988" class="Symbol"
      >}</a
      ><a name="19989"
      > </a
      ><a name="19990" class="Symbol"
      >&#8594;</a
      ><a name="19991"
      > </a
      ><a name="19992" href="Maps.html#10265" class="Function"
      >&#8709;</a
      ><a name="19993"
      > </a
      ><a name="19994" href="Stlc.html#3094" class="Datatype Operator"
      >&#8866;</a
      ><a name="19995"
      > </a
      ><a name="19996" href="StlcProp.html#19983" class="Bound"
      >V</a
      ><a name="19997"
      > </a
      ><a name="19998" href="Stlc.html#3094" class="Datatype Operator"
      >&#8758;</a
      ><a name="19999"
      > </a
      ><a name="20000" href="StlcProp.html#19985" class="Bound"
      >A</a
      ><a name="20001"
      > </a
      ><a name="20002" class="Symbol"
      >&#8594;</a
      ><a name="20003"
      > </a
      ><a name="20004" href="StlcProp.html#19987" class="Bound"
      >&#915;</a
      ><a name="20005"
      > </a
      ><a name="20006" href="Stlc.html#3094" class="Datatype Operator"
      >&#8866;</a
      ><a name="20007"
      > </a
      ><a name="20008" href="StlcProp.html#19983" class="Bound"
      >V</a
      ><a name="20009"
      > </a
      ><a name="20010" href="Stlc.html#3094" class="Datatype Operator"
      >&#8758;</a
      ><a name="20011"
      > </a
      ><a name="20012" href="StlcProp.html#19985" class="Bound"
      >A</a
      ><a name="20013"
      >
</a
      ><a name="20014" href="StlcProp.html#19964" class="Function"
      >weaken-closed</a
      ><a name="20027"
      > </a
      ><a name="20028" class="Symbol"
      >{</a
      ><a name="20029" href="StlcProp.html#20029" class="Bound"
      >V</a
      ><a name="20030" class="Symbol"
      >}</a
      ><a name="20031"
      > </a
      ><a name="20032" class="Symbol"
      >{</a
      ><a name="20033" href="StlcProp.html#20033" class="Bound"
      >A</a
      ><a name="20034" class="Symbol"
      >}</a
      ><a name="20035"
      > </a
      ><a name="20036" class="Symbol"
      >{</a
      ><a name="20037" href="StlcProp.html#20037" class="Bound"
      >&#915;</a
      ><a name="20038" class="Symbol"
      >}</a
      ><a name="20039"
      > </a
      ><a name="20040" href="StlcProp.html#20040" class="Bound"
      >&#8866;V</a
      ><a name="20042"
      > </a
      ><a name="20043" class="Symbol"
      >=</a
      ><a name="20044"
      > </a
      ><a name="20045" href="StlcProp.html#12430" class="Function"
      >contextLemma</a
      ><a name="20057"
      > </a
      ><a name="20058" href="StlcProp.html#20076" class="Function"
      >&#915;~&#915;&#8242;</a
      ><a name="20062"
      > </a
      ><a name="20063" href="StlcProp.html#20040" class="Bound"
      >&#8866;V</a
      ><a name="20065"
      >
  </a
      ><a name="20068" class="Keyword"
      >where</a
      ><a name="20073"
      >
  </a
      ><a name="20076" href="StlcProp.html#20076" class="Function"
      >&#915;~&#915;&#8242;</a
      ><a name="20080"
      > </a
      ><a name="20081" class="Symbol"
      >:</a
      ><a name="20082"
      > </a
      ><a name="20083" class="Symbol"
      >&#8704;</a
      ><a name="20084"
      > </a
      ><a name="20085" class="Symbol"
      >{</a
      ><a name="20086" href="StlcProp.html#20086" class="Bound"
      >x</a
      ><a name="20087" class="Symbol"
      >}</a
      ><a name="20088"
      > </a
      ><a name="20089" class="Symbol"
      >&#8594;</a
      ><a name="20090"
      > </a
      ><a name="20091" href="StlcProp.html#20086" class="Bound"
      >x</a
      ><a name="20092"
      > </a
      ><a name="20093" href="StlcProp.html#7574" class="Datatype Operator"
      >&#8712;</a
      ><a name="20094"
      > </a
      ><a name="20095" href="StlcProp.html#20029" class="Bound"
      >V</a
      ><a name="20096"
      > </a
      ><a name="20097" class="Symbol"
      >&#8594;</a
      ><a name="20098"
      > </a
      ><a name="20099" href="Maps.html#10265" class="Function"
      >&#8709;</a
      ><a name="20100"
      > </a
      ><a name="20101" href="StlcProp.html#20086" class="Bound"
      >x</a
      ><a name="20102"
      > </a
      ><a name="20103" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="20104"
      > </a
      ><a name="20105" href="StlcProp.html#20037" class="Bound"
      >&#915;</a
      ><a name="20106"
      > </a
      ><a name="20107" href="StlcProp.html#20086" class="Bound"
      >x</a
      ><a name="20108"
      >
  </a
      ><a name="20111" href="StlcProp.html#20076" class="Function"
      >&#915;~&#915;&#8242;</a
      ><a name="20115"
      > </a
      ><a name="20116" class="Symbol"
      >{</a
      ><a name="20117" href="StlcProp.html#20117" class="Bound"
      >x</a
      ><a name="20118" class="Symbol"
      >}</a
      ><a name="20119"
      > </a
      ><a name="20120" href="StlcProp.html#20120" class="Bound"
      >x&#8712;V</a
      ><a name="20123"
      > </a
      ><a name="20124" class="Symbol"
      >=</a
      ><a name="20125"
      > </a
      ><a name="20126" href="https://agda.github.io/agda-stdlib/Data.Empty.html#348" class="Function"
      >&#8869;-elim</a
      ><a name="20132"
      > </a
      ><a name="20133" class="Symbol"
      >(</a
      ><a name="20134" href="StlcProp.html#20157" class="Function"
      >x&#8713;V</a
      ><a name="20137"
      > </a
      ><a name="20138" href="StlcProp.html#20120" class="Bound"
      >x&#8712;V</a
      ><a name="20141" class="Symbol"
      >)</a
      ><a name="20142"
      >
    </a
      ><a name="20147" class="Keyword"
      >where</a
      ><a name="20152"
      >
    </a
      ><a name="20157" href="StlcProp.html#20157" class="Function"
      >x&#8713;V</a
      ><a name="20160"
      > </a
      ><a name="20161" class="Symbol"
      >:</a
      ><a name="20162"
      > </a
      ><a name="20163" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#414" class="Function Operator"
      >&#172;</a
      ><a name="20164"
      > </a
      ><a name="20165" class="Symbol"
      >(</a
      ><a name="20166" href="StlcProp.html#20117" class="Bound"
      >x</a
      ><a name="20167"
      > </a
      ><a name="20168" href="StlcProp.html#7574" class="Datatype Operator"
      >&#8712;</a
      ><a name="20169"
      > </a
      ><a name="20170" href="StlcProp.html#20029" class="Bound"
      >V</a
      ><a name="20171" class="Symbol"
      >)</a
      ><a name="20172"
      >
    </a
      ><a name="20177" href="StlcProp.html#20157" class="Function"
      >x&#8713;V</a
      ><a name="20180"
      > </a
      ><a name="20181" class="Symbol"
      >=</a
      ><a name="20182"
      > </a
      ><a name="20183" href="StlcProp.html#11729" class="Postulate"
      >&#8709;&#8866;-closed</a
      ><a name="20192"
      > </a
      ><a name="20193" href="StlcProp.html#20040" class="Bound"
      >&#8866;V</a
      ><a name="20195"
      > </a
      ><a name="20196" class="Symbol"
      >{</a
      ><a name="20197" href="StlcProp.html#20117" class="Bound"
      >x</a
      ><a name="20198" class="Symbol"
      >}</a
      ><a name="20199"
      >

</a
      ><a name="20201" href="StlcProp.html#20201" class="Function"
      >just-injective</a
      ><a name="20215"
      > </a
      ><a name="20216" class="Symbol"
      >:</a
      ><a name="20217"
      > </a
      ><a name="20218" class="Symbol"
      >&#8704;</a
      ><a name="20219"
      > </a
      ><a name="20220" class="Symbol"
      >{</a
      ><a name="20221" href="StlcProp.html#20221" class="Bound"
      >X</a
      ><a name="20222"
      > </a
      ><a name="20223" class="Symbol"
      >:</a
      ><a name="20224"
      > </a
      ><a name="20225" class="PrimitiveType"
      >Set</a
      ><a name="20228" class="Symbol"
      >}</a
      ><a name="20229"
      > </a
      ><a name="20230" class="Symbol"
      >{</a
      ><a name="20231" href="StlcProp.html#20231" class="Bound"
      >x</a
      ><a name="20232"
      > </a
      ><a name="20233" href="StlcProp.html#20233" class="Bound"
      >y</a
      ><a name="20234"
      > </a
      ><a name="20235" class="Symbol"
      >:</a
      ><a name="20236"
      > </a
      ><a name="20237" href="StlcProp.html#20221" class="Bound"
      >X</a
      ><a name="20238" class="Symbol"
      >}</a
      ><a name="20239"
      > </a
      ><a name="20240" class="Symbol"
      >&#8594;</a
      ><a name="20241"
      > </a
      ><a name="20242" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >_&#8801;_</a
      ><a name="20245"
      > </a
      ><a name="20246" class="Symbol"
      >{</a
      ><a name="20247" class="Argument"
      >A</a
      ><a name="20248"
      > </a
      ><a name="20249" class="Symbol"
      >=</a
      ><a name="20250"
      > </a
      ><a name="20251" href="https://agda.github.io/agda-stdlib/Data.Maybe.Base.html#335" class="Datatype"
      >Maybe</a
      ><a name="20256"
      > </a
      ><a name="20257" href="StlcProp.html#20221" class="Bound"
      >X</a
      ><a name="20258" class="Symbol"
      >}</a
      ><a name="20259"
      > </a
      ><a name="20260" class="Symbol"
      >(</a
      ><a name="20261" href="https://agda.github.io/agda-stdlib/Data.Maybe.Base.html#373" class="InductiveConstructor"
      >just</a
      ><a name="20265"
      > </a
      ><a name="20266" href="StlcProp.html#20231" class="Bound"
      >x</a
      ><a name="20267" class="Symbol"
      >)</a
      ><a name="20268"
      > </a
      ><a name="20269" class="Symbol"
      >(</a
      ><a name="20270" href="https://agda.github.io/agda-stdlib/Data.Maybe.Base.html#373" class="InductiveConstructor"
      >just</a
      ><a name="20274"
      > </a
      ><a name="20275" href="StlcProp.html#20233" class="Bound"
      >y</a
      ><a name="20276" class="Symbol"
      >)</a
      ><a name="20277"
      > </a
      ><a name="20278" class="Symbol"
      >&#8594;</a
      ><a name="20279"
      > </a
      ><a name="20280" href="StlcProp.html#20231" class="Bound"
      >x</a
      ><a name="20281"
      > </a
      ><a name="20282" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="20283"
      > </a
      ><a name="20284" href="StlcProp.html#20233" class="Bound"
      >y</a
      ><a name="20285"
      >
</a
      ><a name="20286" href="StlcProp.html#20201" class="Function"
      >just-injective</a
      ><a name="20300"
      > </a
      ><a name="20301" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="20305"
      > </a
      ><a name="20306" class="Symbol"
      >=</a
      ><a name="20307"
      > </a
      ><a name="20308" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      >
{% endraw %}</pre>

<pre class="Agda">{% raw %}
<a name="20338" href="StlcProp.html#16707" class="Function"
      >preservation-[&#8758;=]</a
      ><a name="20355"
      > </a
      ><a name="20356" class="Symbol"
      >{_}</a
      ><a name="20359"
      > </a
      ><a name="20360" class="Symbol"
      >{</a
      ><a name="20361" href="StlcProp.html#20361" class="Bound"
      >x</a
      ><a name="20362" class="Symbol"
      >}</a
      ><a name="20363"
      > </a
      ><a name="20364" class="Symbol"
      >(</a
      ><a name="20365" href="Stlc.html#3138" class="InductiveConstructor"
      >Ax</a
      ><a name="20367"
      > </a
      ><a name="20368" class="Symbol"
      >{_}</a
      ><a name="20371"
      > </a
      ><a name="20372" class="Symbol"
      >{</a
      ><a name="20373" href="StlcProp.html#20373" class="Bound"
      >x&#8242;</a
      ><a name="20375" class="Symbol"
      >}</a
      ><a name="20376"
      > </a
      ><a name="20377" href="StlcProp.html#20377" class="Bound"
      >[&#915;,x&#8758;A]x&#8242;&#8801;B</a
      ><a name="20388" class="Symbol"
      >)</a
      ><a name="20389"
      > </a
      ><a name="20390" href="StlcProp.html#20390" class="Bound"
      >&#8866;V</a
      ><a name="20392"
      > </a
      ><a name="20393" class="Keyword"
      >with</a
      ><a name="20397"
      > </a
      ><a name="20398" href="StlcProp.html#20361" class="Bound"
      >x</a
      ><a name="20399"
      > </a
      ><a name="20400" href="Maps.html#2509" class="Function Operator"
      >&#8799;</a
      ><a name="20401"
      > </a
      ><a name="20402" href="StlcProp.html#20373" class="Bound"
      >x&#8242;</a
      ><a name="20404"
      >
</a
      ><a name="20405" class="Symbol"
      >...|</a
      ><a name="20409"
      > </a
      ><a name="20410" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#520" class="InductiveConstructor"
      >yes</a
      ><a name="20413"
      > </a
      ><a name="20414" href="StlcProp.html#20414" class="Bound"
      >x&#8801;x&#8242;</a
      ><a name="20418"
      > </a
      ><a name="20419" class="Keyword"
      >rewrite</a
      ><a name="20426"
      > </a
      ><a name="20427" href="StlcProp.html#20201" class="Function"
      >just-injective</a
      ><a name="20441"
      > </a
      ><a name="20442" href="StlcProp.html#20377" class="Bound"
      >[&#915;,x&#8758;A]x&#8242;&#8801;B</a
      ><a name="20453"
      >  </a
      ><a name="20455" class="Symbol"
      >=</a
      ><a name="20456"
      >  </a
      ><a name="20458" href="StlcProp.html#19964" class="Function"
      >weaken-closed</a
      ><a name="20471"
      > </a
      ><a name="20472" href="StlcProp.html#20390" class="Bound"
      >&#8866;V</a
      ><a name="20474"
      >
</a
      ><a name="20475" class="Symbol"
      >...|</a
      ><a name="20479"
      > </a
      ><a name="20480" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#547" class="InductiveConstructor"
      >no</a
      ><a name="20482"
      >  </a
      ><a name="20484" href="StlcProp.html#20484" class="Bound"
      >x&#8802;x&#8242;</a
      ><a name="20488"
      >  </a
      ><a name="20490" class="Symbol"
      >=</a
      ><a name="20491"
      >  </a
      ><a name="20493" href="Stlc.html#3138" class="InductiveConstructor"
      >Ax</a
      ><a name="20495"
      > </a
      ><a name="20496" href="StlcProp.html#20377" class="Bound"
      >[&#915;,x&#8758;A]x&#8242;&#8801;B</a
      ><a name="20507"
      >
</a
      ><a name="20508" href="StlcProp.html#16707" class="Function"
      >preservation-[&#8758;=]</a
      ><a name="20525"
      > </a
      ><a name="20526" class="Symbol"
      >{</a
      ><a name="20527" href="StlcProp.html#20527" class="Bound"
      >&#915;</a
      ><a name="20528" class="Symbol"
      >}</a
      ><a name="20529"
      > </a
      ><a name="20530" class="Symbol"
      >{</a
      ><a name="20531" href="StlcProp.html#20531" class="Bound"
      >x</a
      ><a name="20532" class="Symbol"
      >}</a
      ><a name="20533"
      > </a
      ><a name="20534" class="Symbol"
      >{</a
      ><a name="20535" href="StlcProp.html#20535" class="Bound"
      >A</a
      ><a name="20536" class="Symbol"
      >}</a
      ><a name="20537"
      > </a
      ><a name="20538" class="Symbol"
      >{</a
      ><a name="20539" href="Stlc.html#745" class="InductiveConstructor Operator"
      >&#955;[</a
      ><a name="20541"
      > </a
      ><a name="20542" href="StlcProp.html#20542" class="Bound"
      >x&#8242;</a
      ><a name="20544"
      > </a
      ><a name="20545" href="Stlc.html#745" class="InductiveConstructor Operator"
      >&#8758;</a
      ><a name="20546"
      > </a
      ><a name="20547" href="StlcProp.html#20547" class="Bound"
      >A&#8242;</a
      ><a name="20549"
      > </a
      ><a name="20550" href="Stlc.html#745" class="InductiveConstructor Operator"
      >]</a
      ><a name="20551"
      > </a
      ><a name="20552" href="StlcProp.html#20552" class="Bound"
      >N&#8242;</a
      ><a name="20554" class="Symbol"
      >}</a
      ><a name="20555"
      > </a
      ><a name="20556" class="Symbol"
      >{</a
      ><a name="20557" class="DottedPattern Symbol"
      >.</a
      ><a name="20558" href="StlcProp.html#20547" class="DottedPattern Bound"
      >A&#8242;</a
      ><a name="20560"
      > </a
      ><a name="20561" href="Stlc.html#620" class="InductiveConstructor Operator"
      >&#8658;</a
      ><a name="20562"
      > </a
      ><a name="20563" href="StlcProp.html#20563" class="Bound"
      >B&#8242;</a
      ><a name="20565" class="Symbol"
      >}</a
      ><a name="20566"
      > </a
      ><a name="20567" class="Symbol"
      >{</a
      ><a name="20568" href="StlcProp.html#20568" class="Bound"
      >V</a
      ><a name="20569" class="Symbol"
      >}</a
      ><a name="20570"
      > </a
      ><a name="20571" class="Symbol"
      >(</a
      ><a name="20572" href="Stlc.html#3194" class="InductiveConstructor"
      >&#8658;-I</a
      ><a name="20575"
      > </a
      ><a name="20576" href="StlcProp.html#20576" class="Bound"
      >&#8866;N&#8242;</a
      ><a name="20579" class="Symbol"
      >)</a
      ><a name="20580"
      > </a
      ><a name="20581" href="StlcProp.html#20581" class="Bound"
      >&#8866;V</a
      ><a name="20583"
      > </a
      ><a name="20584" class="Keyword"
      >with</a
      ><a name="20588"
      > </a
      ><a name="20589" href="StlcProp.html#20531" class="Bound"
      >x</a
      ><a name="20590"
      > </a
      ><a name="20591" href="Maps.html#2509" class="Function Operator"
      >&#8799;</a
      ><a name="20592"
      > </a
      ><a name="20593" href="StlcProp.html#20542" class="Bound"
      >x&#8242;</a
      ><a name="20595"
      >
</a
      ><a name="20596" class="Symbol"
      >...|</a
      ><a name="20600"
      > </a
      ><a name="20601" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#520" class="InductiveConstructor"
      >yes</a
      ><a name="20604"
      > </a
      ><a name="20605" href="StlcProp.html#20605" class="Bound"
      >x&#8801;x&#8242;</a
      ><a name="20609"
      > </a
      ><a name="20610" class="Keyword"
      >rewrite</a
      ><a name="20617"
      > </a
      ><a name="20618" href="StlcProp.html#20605" class="Bound"
      >x&#8801;x&#8242;</a
      ><a name="20622"
      > </a
      ><a name="20623" class="Symbol"
      >=</a
      ><a name="20624"
      > </a
      ><a name="20625" href="StlcProp.html#12430" class="Function"
      >contextLemma</a
      ><a name="20637"
      > </a
      ><a name="20638" href="StlcProp.html#20663" class="Function"
      >&#915;&#8242;~&#915;</a
      ><a name="20642"
      > </a
      ><a name="20643" class="Symbol"
      >(</a
      ><a name="20644" href="Stlc.html#3194" class="InductiveConstructor"
      >&#8658;-I</a
      ><a name="20647"
      > </a
      ><a name="20648" href="StlcProp.html#20576" class="Bound"
      >&#8866;N&#8242;</a
      ><a name="20651" class="Symbol"
      >)</a
      ><a name="20652"
      >
  </a
      ><a name="20655" class="Keyword"
      >where</a
      ><a name="20660"
      >
  </a
      ><a name="20663" href="StlcProp.html#20663" class="Function"
      >&#915;&#8242;~&#915;</a
      ><a name="20667"
      > </a
      ><a name="20668" class="Symbol"
      >:</a
      ><a name="20669"
      > </a
      ><a name="20670" class="Symbol"
      >&#8704;</a
      ><a name="20671"
      > </a
      ><a name="20672" class="Symbol"
      >{</a
      ><a name="20673" href="StlcProp.html#20673" class="Bound"
      >y</a
      ><a name="20674" class="Symbol"
      >}</a
      ><a name="20675"
      > </a
      ><a name="20676" class="Symbol"
      >&#8594;</a
      ><a name="20677"
      > </a
      ><a name="20678" href="StlcProp.html#20673" class="Bound"
      >y</a
      ><a name="20679"
      > </a
      ><a name="20680" href="StlcProp.html#7574" class="Datatype Operator"
      >&#8712;</a
      ><a name="20681"
      > </a
      ><a name="20682" class="Symbol"
      >(</a
      ><a name="20683" href="Stlc.html#745" class="InductiveConstructor Operator"
      >&#955;[</a
      ><a name="20685"
      > </a
      ><a name="20686" href="StlcProp.html#20542" class="Bound"
      >x&#8242;</a
      ><a name="20688"
      > </a
      ><a name="20689" href="Stlc.html#745" class="InductiveConstructor Operator"
      >&#8758;</a
      ><a name="20690"
      > </a
      ><a name="20691" href="StlcProp.html#20547" class="Bound"
      >A&#8242;</a
      ><a name="20693"
      > </a
      ><a name="20694" href="Stlc.html#745" class="InductiveConstructor Operator"
      >]</a
      ><a name="20695"
      > </a
      ><a name="20696" href="StlcProp.html#20552" class="Bound"
      >N&#8242;</a
      ><a name="20698" class="Symbol"
      >)</a
      ><a name="20699"
      > </a
      ><a name="20700" class="Symbol"
      >&#8594;</a
      ><a name="20701"
      > </a
      ><a name="20702" class="Symbol"
      >(</a
      ><a name="20703" href="StlcProp.html#20527" class="Bound"
      >&#915;</a
      ><a name="20704"
      > </a
      ><a name="20705" href="Maps.html#10368" class="Function Operator"
      >,</a
      ><a name="20706"
      > </a
      ><a name="20707" href="StlcProp.html#20542" class="Bound"
      >x&#8242;</a
      ><a name="20709"
      > </a
      ><a name="20710" href="Maps.html#10368" class="Function Operator"
      >&#8758;</a
      ><a name="20711"
      > </a
      ><a name="20712" href="StlcProp.html#20535" class="Bound"
      >A</a
      ><a name="20713" class="Symbol"
      >)</a
      ><a name="20714"
      > </a
      ><a name="20715" href="StlcProp.html#20673" class="Bound"
      >y</a
      ><a name="20716"
      > </a
      ><a name="20717" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="20718"
      > </a
      ><a name="20719" href="StlcProp.html#20527" class="Bound"
      >&#915;</a
      ><a name="20720"
      > </a
      ><a name="20721" href="StlcProp.html#20673" class="Bound"
      >y</a
      ><a name="20722"
      >
  </a
      ><a name="20725" href="StlcProp.html#20663" class="Function"
      >&#915;&#8242;~&#915;</a
      ><a name="20729"
      > </a
      ><a name="20730" class="Symbol"
      >{</a
      ><a name="20731" href="StlcProp.html#20731" class="Bound"
      >y</a
      ><a name="20732" class="Symbol"
      >}</a
      ><a name="20733"
      > </a
      ><a name="20734" class="Symbol"
      >(</a
      ><a name="20735" href="StlcProp.html#7636" class="InductiveConstructor"
      >free-&#955;</a
      ><a name="20741"
      > </a
      ><a name="20742" href="StlcProp.html#20742" class="Bound"
      >x&#8242;&#8802;y</a
      ><a name="20746"
      > </a
      ><a name="20747" href="StlcProp.html#20747" class="Bound"
      >y&#8712;N&#8242;</a
      ><a name="20751" class="Symbol"
      >)</a
      ><a name="20752"
      > </a
      ><a name="20753" class="Keyword"
      >with</a
      ><a name="20757"
      > </a
      ><a name="20758" href="StlcProp.html#20542" class="Bound"
      >x&#8242;</a
      ><a name="20760"
      > </a
      ><a name="20761" href="Maps.html#2509" class="Function Operator"
      >&#8799;</a
      ><a name="20762"
      > </a
      ><a name="20763" href="StlcProp.html#20731" class="Bound"
      >y</a
      ><a name="20764"
      >
  </a
      ><a name="20767" class="Symbol"
      >...|</a
      ><a name="20771"
      > </a
      ><a name="20772" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#520" class="InductiveConstructor"
      >yes</a
      ><a name="20775"
      > </a
      ><a name="20776" href="StlcProp.html#20776" class="Bound"
      >x&#8242;&#8801;y</a
      ><a name="20780"
      >  </a
      ><a name="20782" class="Symbol"
      >=</a
      ><a name="20783"
      > </a
      ><a name="20784" href="https://agda.github.io/agda-stdlib/Data.Empty.html#348" class="Function"
      >&#8869;-elim</a
      ><a name="20790"
      > </a
      ><a name="20791" class="Symbol"
      >(</a
      ><a name="20792" href="StlcProp.html#20742" class="Bound"
      >x&#8242;&#8802;y</a
      ><a name="20796"
      > </a
      ><a name="20797" href="StlcProp.html#20776" class="Bound"
      >x&#8242;&#8801;y</a
      ><a name="20801" class="Symbol"
      >)</a
      ><a name="20802"
      >
  </a
      ><a name="20805" class="Symbol"
      >...|</a
      ><a name="20809"
      > </a
      ><a name="20810" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#547" class="InductiveConstructor"
      >no</a
      ><a name="20812"
      >  </a
      ><a name="20814" class="Symbol"
      >_</a
      ><a name="20815"
      >     </a
      ><a name="20820" class="Symbol"
      >=</a
      ><a name="20821"
      > </a
      ><a name="20822" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="20826"
      >
</a
      ><a name="20827" class="Symbol"
      >...|</a
      ><a name="20831"
      > </a
      ><a name="20832" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#547" class="InductiveConstructor"
      >no</a
      ><a name="20834"
      >  </a
      ><a name="20836" href="StlcProp.html#20836" class="Bound"
      >x&#8802;x&#8242;</a
      ><a name="20840"
      > </a
      ><a name="20841" class="Symbol"
      >=</a
      ><a name="20842"
      > </a
      ><a name="20843" href="Stlc.html#3194" class="InductiveConstructor"
      >&#8658;-I</a
      ><a name="20846"
      > </a
      ><a name="20847" href="StlcProp.html#20958" class="Function"
      >&#8866;N&#8242;V</a
      ><a name="20851"
      >
  </a
      ><a name="20854" class="Keyword"
      >where</a
      ><a name="20859"
      >
  </a
      ><a name="20862" href="StlcProp.html#20862" class="Function"
      >x&#8242;x&#8866;N&#8242;</a
      ><a name="20868"
      > </a
      ><a name="20869" class="Symbol"
      >:</a
      ><a name="20870"
      > </a
      ><a name="20871" href="StlcProp.html#20527" class="Bound"
      >&#915;</a
      ><a name="20872"
      > </a
      ><a name="20873" href="Maps.html#10368" class="Function Operator"
      >,</a
      ><a name="20874"
      > </a
      ><a name="20875" href="StlcProp.html#20542" class="Bound"
      >x&#8242;</a
      ><a name="20877"
      > </a
      ><a name="20878" href="Maps.html#10368" class="Function Operator"
      >&#8758;</a
      ><a name="20879"
      > </a
      ><a name="20880" href="StlcProp.html#20547" class="Bound"
      >A&#8242;</a
      ><a name="20882"
      > </a
      ><a name="20883" href="Maps.html#10368" class="Function Operator"
      >,</a
      ><a name="20884"
      > </a
      ><a name="20885" href="StlcProp.html#20531" class="Bound"
      >x</a
      ><a name="20886"
      > </a
      ><a name="20887" href="Maps.html#10368" class="Function Operator"
      >&#8758;</a
      ><a name="20888"
      > </a
      ><a name="20889" href="StlcProp.html#20535" class="Bound"
      >A</a
      ><a name="20890"
      > </a
      ><a name="20891" href="Stlc.html#3094" class="Datatype Operator"
      >&#8866;</a
      ><a name="20892"
      > </a
      ><a name="20893" href="StlcProp.html#20552" class="Bound"
      >N&#8242;</a
      ><a name="20895"
      > </a
      ><a name="20896" href="Stlc.html#3094" class="Datatype Operator"
      >&#8758;</a
      ><a name="20897"
      > </a
      ><a name="20898" href="StlcProp.html#20563" class="Bound"
      >B&#8242;</a
      ><a name="20900"
      >
  </a
      ><a name="20903" href="StlcProp.html#20862" class="Function"
      >x&#8242;x&#8866;N&#8242;</a
      ><a name="20909"
      > </a
      ><a name="20910" class="Keyword"
      >rewrite</a
      ><a name="20917"
      > </a
      ><a name="20918" href="Maps.html#11491" class="Function"
      >update-permute</a
      ><a name="20932"
      > </a
      ><a name="20933" href="StlcProp.html#20527" class="Bound"
      >&#915;</a
      ><a name="20934"
      > </a
      ><a name="20935" href="StlcProp.html#20531" class="Bound"
      >x</a
      ><a name="20936"
      > </a
      ><a name="20937" href="StlcProp.html#20535" class="Bound"
      >A</a
      ><a name="20938"
      > </a
      ><a name="20939" href="StlcProp.html#20542" class="Bound"
      >x&#8242;</a
      ><a name="20941"
      > </a
      ><a name="20942" href="StlcProp.html#20547" class="Bound"
      >A&#8242;</a
      ><a name="20944"
      > </a
      ><a name="20945" href="StlcProp.html#20836" class="Bound"
      >x&#8802;x&#8242;</a
      ><a name="20949"
      > </a
      ><a name="20950" class="Symbol"
      >=</a
      ><a name="20951"
      > </a
      ><a name="20952" href="StlcProp.html#20576" class="Bound"
      >&#8866;N&#8242;</a
      ><a name="20955"
      >
  </a
      ><a name="20958" href="StlcProp.html#20958" class="Function"
      >&#8866;N&#8242;V</a
      ><a name="20962"
      > </a
      ><a name="20963" class="Symbol"
      >:</a
      ><a name="20964"
      > </a
      ><a name="20965" class="Symbol"
      >(</a
      ><a name="20966" href="StlcProp.html#20527" class="Bound"
      >&#915;</a
      ><a name="20967"
      > </a
      ><a name="20968" href="Maps.html#10368" class="Function Operator"
      >,</a
      ><a name="20969"
      > </a
      ><a name="20970" href="StlcProp.html#20542" class="Bound"
      >x&#8242;</a
      ><a name="20972"
      > </a
      ><a name="20973" href="Maps.html#10368" class="Function Operator"
      >&#8758;</a
      ><a name="20974"
      > </a
      ><a name="20975" href="StlcProp.html#20547" class="Bound"
      >A&#8242;</a
      ><a name="20977" class="Symbol"
      >)</a
      ><a name="20978"
      > </a
      ><a name="20979" href="Stlc.html#3094" class="Datatype Operator"
      >&#8866;</a
      ><a name="20980"
      > </a
      ><a name="20981" href="StlcProp.html#20552" class="Bound"
      >N&#8242;</a
      ><a name="20983"
      > </a
      ><a name="20984" href="Stlc.html#1286" class="Function Operator"
      >[</a
      ><a name="20985"
      > </a
      ><a name="20986" href="StlcProp.html#20531" class="Bound"
      >x</a
      ><a name="20987"
      > </a
      ><a name="20988" href="Stlc.html#1286" class="Function Operator"
      >&#8758;=</a
      ><a name="20990"
      > </a
      ><a name="20991" href="StlcProp.html#20568" class="Bound"
      >V</a
      ><a name="20992"
      > </a
      ><a name="20993" href="Stlc.html#1286" class="Function Operator"
      >]</a
      ><a name="20994"
      > </a
      ><a name="20995" href="Stlc.html#3094" class="Datatype Operator"
      >&#8758;</a
      ><a name="20996"
      > </a
      ><a name="20997" href="StlcProp.html#20563" class="Bound"
      >B&#8242;</a
      ><a name="20999"
      >
  </a
      ><a name="21002" href="StlcProp.html#20958" class="Function"
      >&#8866;N&#8242;V</a
      ><a name="21006"
      > </a
      ><a name="21007" class="Symbol"
      >=</a
      ><a name="21008"
      > </a
      ><a name="21009" href="StlcProp.html#16707" class="Function"
      >preservation-[&#8758;=]</a
      ><a name="21026"
      > </a
      ><a name="21027" href="StlcProp.html#20862" class="Function"
      >x&#8242;x&#8866;N&#8242;</a
      ><a name="21033"
      > </a
      ><a name="21034" href="StlcProp.html#20581" class="Bound"
      >&#8866;V</a
      ><a name="21036"
      >
</a
      ><a name="21037" href="StlcProp.html#16707" class="Function"
      >preservation-[&#8758;=]</a
      ><a name="21054"
      > </a
      ><a name="21055" class="Symbol"
      >(</a
      ><a name="21056" href="Stlc.html#3271" class="InductiveConstructor"
      >&#8658;-E</a
      ><a name="21059"
      > </a
      ><a name="21060" href="StlcProp.html#21060" class="Bound"
      >&#8866;L</a
      ><a name="21062"
      > </a
      ><a name="21063" href="StlcProp.html#21063" class="Bound"
      >&#8866;M</a
      ><a name="21065" class="Symbol"
      >)</a
      ><a name="21066"
      > </a
      ><a name="21067" href="StlcProp.html#21067" class="Bound"
      >&#8866;V</a
      ><a name="21069"
      > </a
      ><a name="21070" class="Symbol"
      >=</a
      ><a name="21071"
      > </a
      ><a name="21072" href="Stlc.html#3271" class="InductiveConstructor"
      >&#8658;-E</a
      ><a name="21075"
      > </a
      ><a name="21076" class="Symbol"
      >(</a
      ><a name="21077" href="StlcProp.html#16707" class="Function"
      >preservation-[&#8758;=]</a
      ><a name="21094"
      > </a
      ><a name="21095" href="StlcProp.html#21060" class="Bound"
      >&#8866;L</a
      ><a name="21097"
      > </a
      ><a name="21098" href="StlcProp.html#21067" class="Bound"
      >&#8866;V</a
      ><a name="21100" class="Symbol"
      >)</a
      ><a name="21101"
      > </a
      ><a name="21102" class="Symbol"
      >(</a
      ><a name="21103" href="StlcProp.html#16707" class="Function"
      >preservation-[&#8758;=]</a
      ><a name="21120"
      > </a
      ><a name="21121" href="StlcProp.html#21063" class="Bound"
      >&#8866;M</a
      ><a name="21123"
      > </a
      ><a name="21124" href="StlcProp.html#21067" class="Bound"
      >&#8866;V</a
      ><a name="21126" class="Symbol"
      >)</a
      ><a name="21127"
      >
</a
      ><a name="21128" href="StlcProp.html#16707" class="Function"
      >preservation-[&#8758;=]</a
      ><a name="21145"
      > </a
      ><a name="21146" href="Stlc.html#3349" class="InductiveConstructor"
      >&#120121;-I&#8321;</a
      ><a name="21150"
      > </a
      ><a name="21151" href="StlcProp.html#21151" class="Bound"
      >&#8866;V</a
      ><a name="21153"
      > </a
      ><a name="21154" class="Symbol"
      >=</a
      ><a name="21155"
      > </a
      ><a name="21156" href="Stlc.html#3349" class="InductiveConstructor"
      >&#120121;-I&#8321;</a
      ><a name="21160"
      >
</a
      ><a name="21161" href="StlcProp.html#16707" class="Function"
      >preservation-[&#8758;=]</a
      ><a name="21178"
      > </a
      ><a name="21179" href="Stlc.html#3383" class="InductiveConstructor"
      >&#120121;-I&#8322;</a
      ><a name="21183"
      > </a
      ><a name="21184" href="StlcProp.html#21184" class="Bound"
      >&#8866;V</a
      ><a name="21186"
      > </a
      ><a name="21187" class="Symbol"
      >=</a
      ><a name="21188"
      > </a
      ><a name="21189" href="Stlc.html#3383" class="InductiveConstructor"
      >&#120121;-I&#8322;</a
      ><a name="21193"
      >
</a
      ><a name="21194" href="StlcProp.html#16707" class="Function"
      >preservation-[&#8758;=]</a
      ><a name="21211"
      > </a
      ><a name="21212" class="Symbol"
      >(</a
      ><a name="21213" href="Stlc.html#3418" class="InductiveConstructor"
      >&#120121;-E</a
      ><a name="21216"
      > </a
      ><a name="21217" href="StlcProp.html#21217" class="Bound"
      >&#8866;L</a
      ><a name="21219"
      > </a
      ><a name="21220" href="StlcProp.html#21220" class="Bound"
      >&#8866;M</a
      ><a name="21222"
      > </a
      ><a name="21223" href="StlcProp.html#21223" class="Bound"
      >&#8866;N</a
      ><a name="21225" class="Symbol"
      >)</a
      ><a name="21226"
      > </a
      ><a name="21227" href="StlcProp.html#21227" class="Bound"
      >&#8866;V</a
      ><a name="21229"
      > </a
      ><a name="21230" class="Symbol"
      >=</a
      ><a name="21231"
      >
  </a
      ><a name="21234" href="Stlc.html#3418" class="InductiveConstructor"
      >&#120121;-E</a
      ><a name="21237"
      > </a
      ><a name="21238" class="Symbol"
      >(</a
      ><a name="21239" href="StlcProp.html#16707" class="Function"
      >preservation-[&#8758;=]</a
      ><a name="21256"
      > </a
      ><a name="21257" href="StlcProp.html#21217" class="Bound"
      >&#8866;L</a
      ><a name="21259"
      > </a
      ><a name="21260" href="StlcProp.html#21227" class="Bound"
      >&#8866;V</a
      ><a name="21262" class="Symbol"
      >)</a
      ><a name="21263"
      > </a
      ><a name="21264" class="Symbol"
      >(</a
      ><a name="21265" href="StlcProp.html#16707" class="Function"
      >preservation-[&#8758;=]</a
      ><a name="21282"
      > </a
      ><a name="21283" href="StlcProp.html#21220" class="Bound"
      >&#8866;M</a
      ><a name="21285"
      > </a
      ><a name="21286" href="StlcProp.html#21227" class="Bound"
      >&#8866;V</a
      ><a name="21288" class="Symbol"
      >)</a
      ><a name="21289"
      > </a
      ><a name="21290" class="Symbol"
      >(</a
      ><a name="21291" href="StlcProp.html#16707" class="Function"
      >preservation-[&#8758;=]</a
      ><a name="21308"
      > </a
      ><a name="21309" href="StlcProp.html#21223" class="Bound"
      >&#8866;N</a
      ><a name="21311"
      > </a
      ><a name="21312" href="StlcProp.html#21227" class="Bound"
      >&#8866;V</a
      ><a name="21314" class="Symbol"
      >)</a
      >
{% endraw %}</pre>


### Main Theorem

We now have the tools we need to prove preservation: if a closed
term `M` has type `A` and takes a step to `N`, then `N`
is also a closed term with type `A`.  In other words, small-step
reduction preserves types.

<pre class="Agda">{% raw %}
<a name="21574" href="StlcProp.html#21574" class="Function"
      >preservation</a
      ><a name="21586"
      > </a
      ><a name="21587" class="Symbol"
      >:</a
      ><a name="21588"
      > </a
      ><a name="21589" class="Symbol"
      >&#8704;</a
      ><a name="21590"
      > </a
      ><a name="21591" class="Symbol"
      >{</a
      ><a name="21592" href="StlcProp.html#21592" class="Bound"
      >M</a
      ><a name="21593"
      > </a
      ><a name="21594" href="StlcProp.html#21594" class="Bound"
      >N</a
      ><a name="21595"
      > </a
      ><a name="21596" href="StlcProp.html#21596" class="Bound"
      >A</a
      ><a name="21597" class="Symbol"
      >}</a
      ><a name="21598"
      > </a
      ><a name="21599" class="Symbol"
      >&#8594;</a
      ><a name="21600"
      > </a
      ><a name="21601" href="Maps.html#10265" class="Function"
      >&#8709;</a
      ><a name="21602"
      > </a
      ><a name="21603" href="Stlc.html#3094" class="Datatype Operator"
      >&#8866;</a
      ><a name="21604"
      > </a
      ><a name="21605" href="StlcProp.html#21592" class="Bound"
      >M</a
      ><a name="21606"
      > </a
      ><a name="21607" href="Stlc.html#3094" class="Datatype Operator"
      >&#8758;</a
      ><a name="21608"
      > </a
      ><a name="21609" href="StlcProp.html#21596" class="Bound"
      >A</a
      ><a name="21610"
      > </a
      ><a name="21611" class="Symbol"
      >&#8594;</a
      ><a name="21612"
      > </a
      ><a name="21613" href="StlcProp.html#21592" class="Bound"
      >M</a
      ><a name="21614"
      > </a
      ><a name="21615" href="Stlc.html#1776" class="Datatype Operator"
      >&#10233;</a
      ><a name="21616"
      > </a
      ><a name="21617" href="StlcProp.html#21594" class="Bound"
      >N</a
      ><a name="21618"
      > </a
      ><a name="21619" class="Symbol"
      >&#8594;</a
      ><a name="21620"
      > </a
      ><a name="21621" href="Maps.html#10265" class="Function"
      >&#8709;</a
      ><a name="21622"
      > </a
      ><a name="21623" href="Stlc.html#3094" class="Datatype Operator"
      >&#8866;</a
      ><a name="21624"
      > </a
      ><a name="21625" href="StlcProp.html#21594" class="Bound"
      >N</a
      ><a name="21626"
      > </a
      ><a name="21627" href="Stlc.html#3094" class="Datatype Operator"
      >&#8758;</a
      ><a name="21628"
      > </a
      ><a name="21629" href="StlcProp.html#21596" class="Bound"
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
<a name="22924" href="StlcProp.html#21574" class="Function"
      >preservation</a
      ><a name="22936"
      > </a
      ><a name="22937" class="Symbol"
      >(</a
      ><a name="22938" href="Stlc.html#3138" class="InductiveConstructor"
      >Ax</a
      ><a name="22940"
      > </a
      ><a name="22941" href="StlcProp.html#22941" class="Bound"
      >x&#8321;</a
      ><a name="22943" class="Symbol"
      >)</a
      ><a name="22944"
      > </a
      ><a name="22945" class="Symbol"
      >()</a
      ><a name="22947"
      >
</a
      ><a name="22948" href="StlcProp.html#21574" class="Function"
      >preservation</a
      ><a name="22960"
      > </a
      ><a name="22961" class="Symbol"
      >(</a
      ><a name="22962" href="Stlc.html#3194" class="InductiveConstructor"
      >&#8658;-I</a
      ><a name="22965"
      > </a
      ><a name="22966" href="StlcProp.html#22966" class="Bound"
      >&#8866;N</a
      ><a name="22968" class="Symbol"
      >)</a
      ><a name="22969"
      > </a
      ><a name="22970" class="Symbol"
      >()</a
      ><a name="22972"
      >
</a
      ><a name="22973" href="StlcProp.html#21574" class="Function"
      >preservation</a
      ><a name="22985"
      > </a
      ><a name="22986" class="Symbol"
      >(</a
      ><a name="22987" href="Stlc.html#3271" class="InductiveConstructor"
      >&#8658;-E</a
      ><a name="22990"
      > </a
      ><a name="22991" class="Symbol"
      >(</a
      ><a name="22992" href="Stlc.html#3194" class="InductiveConstructor"
      >&#8658;-I</a
      ><a name="22995"
      > </a
      ><a name="22996" href="StlcProp.html#22996" class="Bound"
      >&#8866;N</a
      ><a name="22998" class="Symbol"
      >)</a
      ><a name="22999"
      > </a
      ><a name="23000" href="StlcProp.html#23000" class="Bound"
      >&#8866;V</a
      ><a name="23002" class="Symbol"
      >)</a
      ><a name="23003"
      > </a
      ><a name="23004" class="Symbol"
      >(</a
      ><a name="23005" href="Stlc.html#1808" class="InductiveConstructor"
      >&#946;&#8658;</a
      ><a name="23007"
      > </a
      ><a name="23008" href="StlcProp.html#23008" class="Bound"
      >valueV</a
      ><a name="23014" class="Symbol"
      >)</a
      ><a name="23015"
      > </a
      ><a name="23016" class="Symbol"
      >=</a
      ><a name="23017"
      > </a
      ><a name="23018" href="StlcProp.html#16707" class="Function"
      >preservation-[&#8758;=]</a
      ><a name="23035"
      > </a
      ><a name="23036" href="StlcProp.html#22996" class="Bound"
      >&#8866;N</a
      ><a name="23038"
      > </a
      ><a name="23039" href="StlcProp.html#23000" class="Bound"
      >&#8866;V</a
      ><a name="23041"
      >
</a
      ><a name="23042" href="StlcProp.html#21574" class="Function"
      >preservation</a
      ><a name="23054"
      > </a
      ><a name="23055" class="Symbol"
      >(</a
      ><a name="23056" href="Stlc.html#3271" class="InductiveConstructor"
      >&#8658;-E</a
      ><a name="23059"
      > </a
      ><a name="23060" href="StlcProp.html#23060" class="Bound"
      >&#8866;L</a
      ><a name="23062"
      > </a
      ><a name="23063" href="StlcProp.html#23063" class="Bound"
      >&#8866;M</a
      ><a name="23065" class="Symbol"
      >)</a
      ><a name="23066"
      > </a
      ><a name="23067" class="Symbol"
      >(</a
      ><a name="23068" href="Stlc.html#1877" class="InductiveConstructor"
      >&#947;&#8658;&#8321;</a
      ><a name="23071"
      > </a
      ><a name="23072" href="StlcProp.html#23072" class="Bound"
      >L&#10233;L&#8242;</a
      ><a name="23076" class="Symbol"
      >)</a
      ><a name="23077"
      > </a
      ><a name="23078" class="Keyword"
      >with</a
      ><a name="23082"
      > </a
      ><a name="23083" href="StlcProp.html#21574" class="Function"
      >preservation</a
      ><a name="23095"
      > </a
      ><a name="23096" href="StlcProp.html#23060" class="Bound"
      >&#8866;L</a
      ><a name="23098"
      > </a
      ><a name="23099" href="StlcProp.html#23072" class="Bound"
      >L&#10233;L&#8242;</a
      ><a name="23103"
      >
</a
      ><a name="23104" class="Symbol"
      >...|</a
      ><a name="23108"
      > </a
      ><a name="23109" href="StlcProp.html#23109" class="Bound"
      >&#8866;L&#8242;</a
      ><a name="23112"
      > </a
      ><a name="23113" class="Symbol"
      >=</a
      ><a name="23114"
      > </a
      ><a name="23115" href="Stlc.html#3271" class="InductiveConstructor"
      >&#8658;-E</a
      ><a name="23118"
      > </a
      ><a name="23119" href="StlcProp.html#23109" class="Bound"
      >&#8866;L&#8242;</a
      ><a name="23122"
      > </a
      ><a name="23123" href="StlcProp.html#23063" class="Bound"
      >&#8866;M</a
      ><a name="23125"
      >
</a
      ><a name="23126" href="StlcProp.html#21574" class="Function"
      >preservation</a
      ><a name="23138"
      > </a
      ><a name="23139" class="Symbol"
      >(</a
      ><a name="23140" href="Stlc.html#3271" class="InductiveConstructor"
      >&#8658;-E</a
      ><a name="23143"
      > </a
      ><a name="23144" href="StlcProp.html#23144" class="Bound"
      >&#8866;L</a
      ><a name="23146"
      > </a
      ><a name="23147" href="StlcProp.html#23147" class="Bound"
      >&#8866;M</a
      ><a name="23149" class="Symbol"
      >)</a
      ><a name="23150"
      > </a
      ><a name="23151" class="Symbol"
      >(</a
      ><a name="23152" href="Stlc.html#1930" class="InductiveConstructor"
      >&#947;&#8658;&#8322;</a
      ><a name="23155"
      > </a
      ><a name="23156" href="StlcProp.html#23156" class="Bound"
      >valueL</a
      ><a name="23162"
      > </a
      ><a name="23163" href="StlcProp.html#23163" class="Bound"
      >M&#10233;M&#8242;</a
      ><a name="23167" class="Symbol"
      >)</a
      ><a name="23168"
      > </a
      ><a name="23169" class="Keyword"
      >with</a
      ><a name="23173"
      > </a
      ><a name="23174" href="StlcProp.html#21574" class="Function"
      >preservation</a
      ><a name="23186"
      > </a
      ><a name="23187" href="StlcProp.html#23147" class="Bound"
      >&#8866;M</a
      ><a name="23189"
      > </a
      ><a name="23190" href="StlcProp.html#23163" class="Bound"
      >M&#10233;M&#8242;</a
      ><a name="23194"
      >
</a
      ><a name="23195" class="Symbol"
      >...|</a
      ><a name="23199"
      > </a
      ><a name="23200" href="StlcProp.html#23200" class="Bound"
      >&#8866;M&#8242;</a
      ><a name="23203"
      > </a
      ><a name="23204" class="Symbol"
      >=</a
      ><a name="23205"
      > </a
      ><a name="23206" href="Stlc.html#3271" class="InductiveConstructor"
      >&#8658;-E</a
      ><a name="23209"
      > </a
      ><a name="23210" href="StlcProp.html#23144" class="Bound"
      >&#8866;L</a
      ><a name="23212"
      > </a
      ><a name="23213" href="StlcProp.html#23200" class="Bound"
      >&#8866;M&#8242;</a
      ><a name="23216"
      >
</a
      ><a name="23217" href="StlcProp.html#21574" class="Function"
      >preservation</a
      ><a name="23229"
      > </a
      ><a name="23230" href="Stlc.html#3349" class="InductiveConstructor"
      >&#120121;-I&#8321;</a
      ><a name="23234"
      > </a
      ><a name="23235" class="Symbol"
      >()</a
      ><a name="23237"
      >
</a
      ><a name="23238" href="StlcProp.html#21574" class="Function"
      >preservation</a
      ><a name="23250"
      > </a
      ><a name="23251" href="Stlc.html#3383" class="InductiveConstructor"
      >&#120121;-I&#8322;</a
      ><a name="23255"
      > </a
      ><a name="23256" class="Symbol"
      >()</a
      ><a name="23258"
      >
</a
      ><a name="23259" href="StlcProp.html#21574" class="Function"
      >preservation</a
      ><a name="23271"
      > </a
      ><a name="23272" class="Symbol"
      >(</a
      ><a name="23273" href="Stlc.html#3418" class="InductiveConstructor"
      >&#120121;-E</a
      ><a name="23276"
      > </a
      ><a name="23277" href="Stlc.html#3349" class="InductiveConstructor"
      >&#120121;-I&#8321;</a
      ><a name="23281"
      > </a
      ><a name="23282" href="StlcProp.html#23282" class="Bound"
      >&#8866;M</a
      ><a name="23284"
      > </a
      ><a name="23285" href="StlcProp.html#23285" class="Bound"
      >&#8866;N</a
      ><a name="23287" class="Symbol"
      >)</a
      ><a name="23288"
      > </a
      ><a name="23289" href="Stlc.html#1997" class="InductiveConstructor"
      >&#946;&#120121;&#8321;</a
      ><a name="23292"
      > </a
      ><a name="23293" class="Symbol"
      >=</a
      ><a name="23294"
      > </a
      ><a name="23295" href="StlcProp.html#23282" class="Bound"
      >&#8866;M</a
      ><a name="23297"
      >
</a
      ><a name="23298" href="StlcProp.html#21574" class="Function"
      >preservation</a
      ><a name="23310"
      > </a
      ><a name="23311" class="Symbol"
      >(</a
      ><a name="23312" href="Stlc.html#3418" class="InductiveConstructor"
      >&#120121;-E</a
      ><a name="23315"
      > </a
      ><a name="23316" href="Stlc.html#3383" class="InductiveConstructor"
      >&#120121;-I&#8322;</a
      ><a name="23320"
      > </a
      ><a name="23321" href="StlcProp.html#23321" class="Bound"
      >&#8866;M</a
      ><a name="23323"
      > </a
      ><a name="23324" href="StlcProp.html#23324" class="Bound"
      >&#8866;N</a
      ><a name="23326" class="Symbol"
      >)</a
      ><a name="23327"
      > </a
      ><a name="23328" href="Stlc.html#2045" class="InductiveConstructor"
      >&#946;&#120121;&#8322;</a
      ><a name="23331"
      > </a
      ><a name="23332" class="Symbol"
      >=</a
      ><a name="23333"
      > </a
      ><a name="23334" href="StlcProp.html#23324" class="Bound"
      >&#8866;N</a
      ><a name="23336"
      >
</a
      ><a name="23337" href="StlcProp.html#21574" class="Function"
      >preservation</a
      ><a name="23349"
      > </a
      ><a name="23350" class="Symbol"
      >(</a
      ><a name="23351" href="Stlc.html#3418" class="InductiveConstructor"
      >&#120121;-E</a
      ><a name="23354"
      > </a
      ><a name="23355" href="StlcProp.html#23355" class="Bound"
      >&#8866;L</a
      ><a name="23357"
      > </a
      ><a name="23358" href="StlcProp.html#23358" class="Bound"
      >&#8866;M</a
      ><a name="23360"
      > </a
      ><a name="23361" href="StlcProp.html#23361" class="Bound"
      >&#8866;N</a
      ><a name="23363" class="Symbol"
      >)</a
      ><a name="23364"
      > </a
      ><a name="23365" class="Symbol"
      >(</a
      ><a name="23366" href="Stlc.html#2094" class="InductiveConstructor"
      >&#947;&#120121;</a
      ><a name="23368"
      > </a
      ><a name="23369" href="StlcProp.html#23369" class="Bound"
      >L&#10233;L&#8242;</a
      ><a name="23373" class="Symbol"
      >)</a
      ><a name="23374"
      > </a
      ><a name="23375" class="Keyword"
      >with</a
      ><a name="23379"
      > </a
      ><a name="23380" href="StlcProp.html#21574" class="Function"
      >preservation</a
      ><a name="23392"
      > </a
      ><a name="23393" href="StlcProp.html#23355" class="Bound"
      >&#8866;L</a
      ><a name="23395"
      > </a
      ><a name="23396" href="StlcProp.html#23369" class="Bound"
      >L&#10233;L&#8242;</a
      ><a name="23400"
      >
</a
      ><a name="23401" class="Symbol"
      >...|</a
      ><a name="23405"
      > </a
      ><a name="23406" href="StlcProp.html#23406" class="Bound"
      >&#8866;L&#8242;</a
      ><a name="23409"
      > </a
      ><a name="23410" class="Symbol"
      >=</a
      ><a name="23411"
      > </a
      ><a name="23412" href="Stlc.html#3418" class="InductiveConstructor"
      >&#120121;-E</a
      ><a name="23415"
      > </a
      ><a name="23416" href="StlcProp.html#23406" class="Bound"
      >&#8866;L&#8242;</a
      ><a name="23419"
      > </a
      ><a name="23420" href="StlcProp.html#23358" class="Bound"
      >&#8866;M</a
      ><a name="23422"
      > </a
      ><a name="23423" href="StlcProp.html#23361" class="Bound"
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

