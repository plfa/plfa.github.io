---
title     : "StlcProp: Properties of STLC"
layout    : page
permalink : /StlcProp
---

<pre class="Agda">

<a name="105" class="Keyword"
      >open</a
      ><a name="109"
      > </a
      ><a name="110" class="Keyword"
      >import</a
      ><a name="116"
      > </a
      ><a name="117" href="https://agda.github.io/agda-stdlib/Function.html#1" class="Module"
      >Function</a
      ><a name="125"
      > </a
      ><a name="126" class="Keyword"
      >using</a
      ><a name="131"
      > </a
      ><a name="132" class="Symbol"
      >(</a
      ><a name="133" href="https://agda.github.io/agda-stdlib/Function.html#713" class="Function Operator"
      >_&#8728;_</a
      ><a name="136" class="Symbol"
      >)</a
      ><a name="137"
      >
</a
      ><a name="138" class="Keyword"
      >open</a
      ><a name="142"
      > </a
      ><a name="143" class="Keyword"
      >import</a
      ><a name="149"
      > </a
      ><a name="150" href="https://agda.github.io/agda-stdlib/Data.Empty.html#1" class="Module"
      >Data.Empty</a
      ><a name="160"
      > </a
      ><a name="161" class="Keyword"
      >using</a
      ><a name="166"
      > </a
      ><a name="167" class="Symbol"
      >(</a
      ><a name="168" href="https://agda.github.io/agda-stdlib/Data.Empty.html#243" class="Datatype"
      >&#8869;</a
      ><a name="169" class="Symbol"
      >;</a
      ><a name="170"
      > </a
      ><a name="171" href="https://agda.github.io/agda-stdlib/Data.Empty.html#360" class="Function"
      >&#8869;-elim</a
      ><a name="177" class="Symbol"
      >)</a
      ><a name="178"
      >
</a
      ><a name="179" class="Keyword"
      >open</a
      ><a name="183"
      > </a
      ><a name="184" class="Keyword"
      >import</a
      ><a name="190"
      > </a
      ><a name="191" href="https://agda.github.io/agda-stdlib/Data.Bool.html#1" class="Module"
      >Data.Bool</a
      ><a name="200"
      > </a
      ><a name="201" class="Keyword"
      >using</a
      ><a name="206"
      > </a
      ><a name="207" class="Symbol"
      >(</a
      ><a name="208" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Bool.html#67" class="Datatype"
      >Bool</a
      ><a name="212" class="Symbol"
      >;</a
      ><a name="213"
      > </a
      ><a name="214" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Bool.html#92" class="InductiveConstructor"
      >true</a
      ><a name="218" class="Symbol"
      >;</a
      ><a name="219"
      > </a
      ><a name="220" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Bool.html#86" class="InductiveConstructor"
      >false</a
      ><a name="225" class="Symbol"
      >)</a
      ><a name="226"
      >
</a
      ><a name="227" class="Keyword"
      >open</a
      ><a name="231"
      > </a
      ><a name="232" class="Keyword"
      >import</a
      ><a name="238"
      > </a
      ><a name="239" href="https://agda.github.io/agda-stdlib/Data.Maybe.html#1" class="Module"
      >Data.Maybe</a
      ><a name="249"
      > </a
      ><a name="250" class="Keyword"
      >using</a
      ><a name="255"
      > </a
      ><a name="256" class="Symbol"
      >(</a
      ><a name="257" href="https://agda.github.io/agda-stdlib/Data.Maybe.Base.html#335" class="Datatype"
      >Maybe</a
      ><a name="262" class="Symbol"
      >;</a
      ><a name="263"
      > </a
      ><a name="264" href="https://agda.github.io/agda-stdlib/Data.Maybe.html#1527" class="InductiveConstructor"
      >just</a
      ><a name="268" class="Symbol"
      >;</a
      ><a name="269"
      > </a
      ><a name="270" href="https://agda.github.io/agda-stdlib/Data.Maybe.html#1588" class="InductiveConstructor"
      >nothing</a
      ><a name="277" class="Symbol"
      >)</a
      ><a name="278"
      >
</a
      ><a name="279" class="Keyword"
      >open</a
      ><a name="283"
      > </a
      ><a name="284" class="Keyword"
      >import</a
      ><a name="290"
      > </a
      ><a name="291" href="https://agda.github.io/agda-stdlib/Data.Product.html#1" class="Module"
      >Data.Product</a
      ><a name="303"
      > </a
      ><a name="304" class="Keyword"
      >using</a
      ><a name="309"
      > </a
      ><a name="310" class="Symbol"
      >(</a
      ><a name="311" href="https://agda.github.io/agda-stdlib/Data.Product.html#823" class="Function"
      >&#8707;</a
      ><a name="312" class="Symbol"
      >;</a
      ><a name="313"
      > </a
      ><a name="314" href="https://agda.github.io/agda-stdlib/Data.Product.html#1171" class="Function"
      >&#8707;&#8322;</a
      ><a name="316" class="Symbol"
      >;</a
      ><a name="317"
      > </a
      ><a name="318" href="https://agda.github.io/agda-stdlib/Data.Product.html#509" class="InductiveConstructor Operator"
      >_,_</a
      ><a name="321" class="Symbol"
      >;</a
      ><a name="322"
      > </a
      ><a name="323" href="https://agda.github.io/agda-stdlib/Data.Product.html#1843" class="Function Operator"
      >,_</a
      ><a name="325" class="Symbol"
      >)</a
      ><a name="326"
      >
</a
      ><a name="327" class="Keyword"
      >open</a
      ><a name="331"
      > </a
      ><a name="332" class="Keyword"
      >import</a
      ><a name="338"
      > </a
      ><a name="339" href="https://agda.github.io/agda-stdlib/Data.Sum.html#1" class="Module"
      >Data.Sum</a
      ><a name="347"
      > </a
      ><a name="348" class="Keyword"
      >using</a
      ><a name="353"
      > </a
      ><a name="354" class="Symbol"
      >(</a
      ><a name="355" href="https://agda.github.io/agda-stdlib/Data.Sum.html#433" class="Datatype Operator"
      >_&#8846;_</a
      ><a name="358" class="Symbol"
      >;</a
      ><a name="359"
      > </a
      ><a name="360" href="https://agda.github.io/agda-stdlib/Data.Sum.html#489" class="InductiveConstructor"
      >inj&#8321;</a
      ><a name="364" class="Symbol"
      >;</a
      ><a name="365"
      > </a
      ><a name="366" href="https://agda.github.io/agda-stdlib/Data.Sum.html#514" class="InductiveConstructor"
      >inj&#8322;</a
      ><a name="370" class="Symbol"
      >)</a
      ><a name="371"
      >
</a
      ><a name="372" class="Keyword"
      >open</a
      ><a name="376"
      > </a
      ><a name="377" class="Keyword"
      >import</a
      ><a name="383"
      > </a
      ><a name="384" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#1" class="Module"
      >Relation.Nullary</a
      ><a name="400"
      > </a
      ><a name="401" class="Keyword"
      >using</a
      ><a name="406"
      > </a
      ><a name="407" class="Symbol"
      >(</a
      ><a name="408" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#414" class="Function Operator"
      >&#172;_</a
      ><a name="410" class="Symbol"
      >;</a
      ><a name="411"
      > </a
      ><a name="412" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#484" class="Datatype"
      >Dec</a
      ><a name="415" class="Symbol"
      >;</a
      ><a name="416"
      > </a
      ><a name="417" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#520" class="InductiveConstructor"
      >yes</a
      ><a name="420" class="Symbol"
      >;</a
      ><a name="421"
      > </a
      ><a name="422" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#547" class="InductiveConstructor"
      >no</a
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
      ><a name="438" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#1" class="Module"
      >Relation.Binary.PropositionalEquality</a
      ><a name="475"
      > </a
      ><a name="476" class="Keyword"
      >using</a
      ><a name="481"
      > </a
      ><a name="482" class="Symbol"
      >(</a
      ><a name="483" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >_&#8801;_</a
      ><a name="486" class="Symbol"
      >;</a
      ><a name="487"
      > </a
      ><a name="488" href="https://agda.github.io/agda-stdlib/Relation.Binary.Core.html#4493" class="Function Operator"
      >_&#8802;_</a
      ><a name="491" class="Symbol"
      >;</a
      ><a name="492"
      > </a
      ><a name="493" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="497" class="Symbol"
      >;</a
      ><a name="498"
      > </a
      ><a name="499" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.Core.html#632" class="Function"
      >trans</a
      ><a name="504" class="Symbol"
      >;</a
      ><a name="505"
      > </a
      ><a name="506" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.Core.html#565" class="Function"
      >sym</a
      ><a name="509" class="Symbol"
      >)</a
      ><a name="510"
      >
</a
      ><a name="511" class="Keyword"
      >open</a
      ><a name="515"
      > </a
      ><a name="516" class="Keyword"
      >import</a
      ><a name="522"
      > </a
      ><a name="523" class="Module"
      >Maps</a
      ><a name="527"
      >
</a
      ><a name="528" class="Keyword"
      >open</a
      ><a name="532"
      > </a
      ><a name="533" class="Module"
      >Maps.</a
      ><a name="538" href="Maps.html#11191" class="Module"
      >PartialMap</a
      ><a name="548"
      >
</a
      ><a name="549" class="Keyword"
      >open</a
      ><a name="553"
      > </a
      ><a name="554" class="Keyword"
      >import</a
      ><a name="560"
      > </a
      ><a name="561" class="Module"
      >Stlc</a
      >

</pre>

In this chapter, we develop the fundamental theory of the Simply
Typed Lambda Calculus---in particular, the type safety
theorem.


## Canonical Forms

As we saw for the simple calculus in the [Stlc]({{ "Stlc" | relative_url }})
chapter, the first step in establishing basic properties of reduction and types
is to identify the possible _canonical forms_ (i.e., well-typed closed values)
belonging to each type.  For $$bool$$, these are the boolean values $$true$$ and
$$false$$.  For arrow types, the canonical forms are lambda-abstractions. 

<pre class="Agda">

<a name="1135" class="Keyword"
      >data</a
      ><a name="1139"
      > </a
      ><a name="1140" href="StlcProp.html#1140" class="Datatype Operator"
      >canonical_for_</a
      ><a name="1154"
      > </a
      ><a name="1155" class="Symbol"
      >:</a
      ><a name="1156"
      > </a
      ><a name="1157" href="Stlc.html#1032" class="Datatype"
      >Term</a
      ><a name="1161"
      > </a
      ><a name="1162" class="Symbol"
      >&#8594;</a
      ><a name="1163"
      > </a
      ><a name="1164" href="Stlc.html#971" class="Datatype"
      >Type</a
      ><a name="1168"
      > </a
      ><a name="1169" class="Symbol"
      >&#8594;</a
      ><a name="1170"
      > </a
      ><a name="1171" class="PrimitiveType"
      >Set</a
      ><a name="1174"
      > </a
      ><a name="1175" class="Keyword"
      >where</a
      ><a name="1180"
      >
  </a
      ><a name="1183" href="StlcProp.html#1183" class="InductiveConstructor"
      >canonical-&#955;&#7488;</a
      ><a name="1195"
      > </a
      ><a name="1196" class="Symbol"
      >:</a
      ><a name="1197"
      > </a
      ><a name="1198" class="Symbol"
      >&#8704;</a
      ><a name="1199"
      > </a
      ><a name="1200" class="Symbol"
      >{</a
      ><a name="1201" href="StlcProp.html#1201" class="Bound"
      >x</a
      ><a name="1202"
      > </a
      ><a name="1203" href="StlcProp.html#1203" class="Bound"
      >A</a
      ><a name="1204"
      > </a
      ><a name="1205" href="StlcProp.html#1205" class="Bound"
      >N</a
      ><a name="1206"
      > </a
      ><a name="1207" href="StlcProp.html#1207" class="Bound"
      >B</a
      ><a name="1208" class="Symbol"
      >}</a
      ><a name="1209"
      > </a
      ><a name="1210" class="Symbol"
      >&#8594;</a
      ><a name="1211"
      > </a
      ><a name="1212" href="StlcProp.html#1140" class="Datatype Operator"
      >canonical</a
      ><a name="1221"
      > </a
      ><a name="1222" class="Symbol"
      >(</a
      ><a name="1223" href="Stlc.html#1070" class="InductiveConstructor Operator"
      >&#955;&#7488;</a
      ><a name="1225"
      > </a
      ><a name="1226" href="StlcProp.html#1201" class="Bound"
      >x</a
      ><a name="1227"
      > </a
      ><a name="1228" href="Stlc.html#1070" class="InductiveConstructor Operator"
      >&#8712;</a
      ><a name="1229"
      > </a
      ><a name="1230" href="StlcProp.html#1203" class="Bound"
      >A</a
      ><a name="1231"
      > </a
      ><a name="1232" href="Stlc.html#1070" class="InductiveConstructor Operator"
      >&#8658;</a
      ><a name="1233"
      > </a
      ><a name="1234" href="StlcProp.html#1205" class="Bound"
      >N</a
      ><a name="1235" class="Symbol"
      >)</a
      ><a name="1236"
      > </a
      ><a name="1237" href="StlcProp.html#1140" class="Datatype Operator"
      >for</a
      ><a name="1240"
      > </a
      ><a name="1241" class="Symbol"
      >(</a
      ><a name="1242" href="StlcProp.html#1203" class="Bound"
      >A</a
      ><a name="1243"
      > </a
      ><a name="1244" href="Stlc.html#1001" class="InductiveConstructor Operator"
      >&#8658;</a
      ><a name="1245"
      > </a
      ><a name="1246" href="StlcProp.html#1207" class="Bound"
      >B</a
      ><a name="1247" class="Symbol"
      >)</a
      ><a name="1248"
      >
  </a
      ><a name="1251" href="StlcProp.html#1251" class="InductiveConstructor"
      >canonical-true&#7488;</a
      ><a name="1266"
      > </a
      ><a name="1267" class="Symbol"
      >:</a
      ><a name="1268"
      > </a
      ><a name="1269" href="StlcProp.html#1140" class="Datatype Operator"
      >canonical</a
      ><a name="1278"
      > </a
      ><a name="1279" href="Stlc.html#1134" class="InductiveConstructor"
      >true&#7488;</a
      ><a name="1284"
      > </a
      ><a name="1285" href="StlcProp.html#1140" class="Datatype Operator"
      >for</a
      ><a name="1288"
      > </a
      ><a name="1289" href="Stlc.html#990" class="InductiveConstructor"
      >&#120121;</a
      ><a name="1290"
      >
  </a
      ><a name="1293" href="StlcProp.html#1293" class="InductiveConstructor"
      >canonical-false&#7488;</a
      ><a name="1309"
      > </a
      ><a name="1310" class="Symbol"
      >:</a
      ><a name="1311"
      > </a
      ><a name="1312" href="StlcProp.html#1140" class="Datatype Operator"
      >canonical</a
      ><a name="1321"
      > </a
      ><a name="1322" href="Stlc.html#1149" class="InductiveConstructor"
      >false&#7488;</a
      ><a name="1328"
      > </a
      ><a name="1329" href="StlcProp.html#1140" class="Datatype Operator"
      >for</a
      ><a name="1332"
      > </a
      ><a name="1333" href="Stlc.html#990" class="InductiveConstructor"
      >&#120121;</a
      ><a name="1334"
      >
  
</a
      ><a name="1338" class="Comment"
      >-- canonical_for_ : Term &#8594; Type &#8594; Set</a
      ><a name="1375"
      >
</a
      ><a name="1376" class="Comment"
      >-- canonical L for &#120121;       = L &#8801; true&#7488; &#8846; L &#8801; false&#7488;</a
      ><a name="1427"
      >
</a
      ><a name="1428" class="Comment"
      >-- canonical L for (A &#8658; B) = &#8707;&#8322; &#955; x N &#8594; L &#8801; &#955;&#7488; x &#8712; A &#8658; N</a
      ><a name="1484"
      >

</a
      ><a name="1486" href="StlcProp.html#1486" class="Function"
      >canonicalFormsLemma</a
      ><a name="1505"
      > </a
      ><a name="1506" class="Symbol"
      >:</a
      ><a name="1507"
      > </a
      ><a name="1508" class="Symbol"
      >&#8704;</a
      ><a name="1509"
      > </a
      ><a name="1510" class="Symbol"
      >{</a
      ><a name="1511" href="StlcProp.html#1511" class="Bound"
      >L</a
      ><a name="1512"
      > </a
      ><a name="1513" href="StlcProp.html#1513" class="Bound"
      >A</a
      ><a name="1514" class="Symbol"
      >}</a
      ><a name="1515"
      > </a
      ><a name="1516" class="Symbol"
      >&#8594;</a
      ><a name="1517"
      > </a
      ><a name="1518" href="Maps.html#11235" class="Function"
      >&#8709;</a
      ><a name="1519"
      > </a
      ><a name="1520" href="Stlc.html#4116" class="Datatype Operator"
      >&#8866;</a
      ><a name="1521"
      > </a
      ><a name="1522" href="StlcProp.html#1511" class="Bound"
      >L</a
      ><a name="1523"
      > </a
      ><a name="1524" href="Stlc.html#4116" class="Datatype Operator"
      >&#8712;</a
      ><a name="1525"
      > </a
      ><a name="1526" href="StlcProp.html#1513" class="Bound"
      >A</a
      ><a name="1527"
      > </a
      ><a name="1528" class="Symbol"
      >&#8594;</a
      ><a name="1529"
      > </a
      ><a name="1530" href="Stlc.html#1581" class="Datatype"
      >value</a
      ><a name="1535"
      > </a
      ><a name="1536" href="StlcProp.html#1511" class="Bound"
      >L</a
      ><a name="1537"
      > </a
      ><a name="1538" class="Symbol"
      >&#8594;</a
      ><a name="1539"
      > </a
      ><a name="1540" href="StlcProp.html#1140" class="Datatype Operator"
      >canonical</a
      ><a name="1549"
      > </a
      ><a name="1550" href="StlcProp.html#1511" class="Bound"
      >L</a
      ><a name="1551"
      > </a
      ><a name="1552" href="StlcProp.html#1140" class="Datatype Operator"
      >for</a
      ><a name="1555"
      > </a
      ><a name="1556" href="StlcProp.html#1513" class="Bound"
      >A</a
      ><a name="1557"
      >
</a
      ><a name="1558" href="StlcProp.html#1486" class="Function"
      >canonicalFormsLemma</a
      ><a name="1577"
      > </a
      ><a name="1578" class="Symbol"
      >(</a
      ><a name="1579" href="Stlc.html#4160" class="InductiveConstructor"
      >Ax</a
      ><a name="1581"
      > </a
      ><a name="1582" href="StlcProp.html#1582" class="Bound"
      >&#8866;x</a
      ><a name="1584" class="Symbol"
      >)</a
      ><a name="1585"
      > </a
      ><a name="1586" class="Symbol"
      >()</a
      ><a name="1588"
      >
</a
      ><a name="1589" href="StlcProp.html#1486" class="Function"
      >canonicalFormsLemma</a
      ><a name="1608"
      > </a
      ><a name="1609" class="Symbol"
      >(</a
      ><a name="1610" href="Stlc.html#4217" class="InductiveConstructor"
      >&#8658;-I</a
      ><a name="1613"
      > </a
      ><a name="1614" href="StlcProp.html#1614" class="Bound"
      >&#8866;N</a
      ><a name="1616" class="Symbol"
      >)</a
      ><a name="1617"
      > </a
      ><a name="1618" href="Stlc.html#1608" class="InductiveConstructor"
      >value-&#955;&#7488;</a
      ><a name="1626"
      > </a
      ><a name="1627" class="Symbol"
      >=</a
      ><a name="1628"
      > </a
      ><a name="1629" href="StlcProp.html#1183" class="InductiveConstructor"
      >canonical-&#955;&#7488;</a
      ><a name="1641"
      >      </a
      ><a name="1647" class="Comment"
      >-- _ , _ , refl</a
      ><a name="1662"
      >
</a
      ><a name="1663" href="StlcProp.html#1486" class="Function"
      >canonicalFormsLemma</a
      ><a name="1682"
      > </a
      ><a name="1683" class="Symbol"
      >(</a
      ><a name="1684" href="Stlc.html#4300" class="InductiveConstructor"
      >&#8658;-E</a
      ><a name="1687"
      > </a
      ><a name="1688" href="StlcProp.html#1688" class="Bound"
      >&#8866;L</a
      ><a name="1690"
      > </a
      ><a name="1691" href="StlcProp.html#1691" class="Bound"
      >&#8866;M</a
      ><a name="1693" class="Symbol"
      >)</a
      ><a name="1694"
      > </a
      ><a name="1695" class="Symbol"
      >()</a
      ><a name="1697"
      >
</a
      ><a name="1698" href="StlcProp.html#1486" class="Function"
      >canonicalFormsLemma</a
      ><a name="1717"
      > </a
      ><a name="1718" href="Stlc.html#4381" class="InductiveConstructor"
      >&#120121;-I&#8321;</a
      ><a name="1722"
      > </a
      ><a name="1723" href="Stlc.html#1654" class="InductiveConstructor"
      >value-true&#7488;</a
      ><a name="1734"
      > </a
      ><a name="1735" class="Symbol"
      >=</a
      ><a name="1736"
      > </a
      ><a name="1737" href="StlcProp.html#1251" class="InductiveConstructor"
      >canonical-true&#7488;</a
      ><a name="1752"
      >    </a
      ><a name="1756" class="Comment"
      >-- inj&#8321; refl</a
      ><a name="1768"
      >
</a
      ><a name="1769" href="StlcProp.html#1486" class="Function"
      >canonicalFormsLemma</a
      ><a name="1788"
      > </a
      ><a name="1789" href="Stlc.html#4416" class="InductiveConstructor"
      >&#120121;-I&#8322;</a
      ><a name="1793"
      > </a
      ><a name="1794" href="Stlc.html#1684" class="InductiveConstructor"
      >value-false&#7488;</a
      ><a name="1806"
      > </a
      ><a name="1807" class="Symbol"
      >=</a
      ><a name="1808"
      > </a
      ><a name="1809" href="StlcProp.html#1293" class="InductiveConstructor"
      >canonical-false&#7488;</a
      ><a name="1825"
      >  </a
      ><a name="1827" class="Comment"
      >-- inj&#8322; refl</a
      ><a name="1839"
      >
</a
      ><a name="1840" href="StlcProp.html#1486" class="Function"
      >canonicalFormsLemma</a
      ><a name="1859"
      > </a
      ><a name="1860" class="Symbol"
      >(</a
      ><a name="1861" href="Stlc.html#4452" class="InductiveConstructor"
      >&#120121;-E</a
      ><a name="1864"
      > </a
      ><a name="1865" href="StlcProp.html#1865" class="Bound"
      >&#8866;L</a
      ><a name="1867"
      > </a
      ><a name="1868" href="StlcProp.html#1868" class="Bound"
      >&#8866;M</a
      ><a name="1870"
      > </a
      ><a name="1871" href="StlcProp.html#1871" class="Bound"
      >&#8866;N</a
      ><a name="1873" class="Symbol"
      >)</a
      ><a name="1874"
      > </a
      ><a name="1875" class="Symbol"
      >()</a
      >

</pre>

## Progress

As before, the _progress_ theorem tells us that closed, well-typed
terms are not stuck: either a well-typed term is a value, or it
can take a reduction step.  The proof is a relatively
straightforward extension of the progress proof we saw in the
[Stlc]({{ "Stlc" | relative_url }}) chapter.  We'll give the proof in English
first, then the formal version.

<pre class="Agda">

<a name="2274" href="StlcProp.html#2274" class="Function"
      >progress</a
      ><a name="2282"
      > </a
      ><a name="2283" class="Symbol"
      >:</a
      ><a name="2284"
      > </a
      ><a name="2285" class="Symbol"
      >&#8704;</a
      ><a name="2286"
      > </a
      ><a name="2287" class="Symbol"
      >{</a
      ><a name="2288" href="StlcProp.html#2288" class="Bound"
      >M</a
      ><a name="2289"
      > </a
      ><a name="2290" href="StlcProp.html#2290" class="Bound"
      >A</a
      ><a name="2291" class="Symbol"
      >}</a
      ><a name="2292"
      > </a
      ><a name="2293" class="Symbol"
      >&#8594;</a
      ><a name="2294"
      > </a
      ><a name="2295" href="Maps.html#11235" class="Function"
      >&#8709;</a
      ><a name="2296"
      > </a
      ><a name="2297" href="Stlc.html#4116" class="Datatype Operator"
      >&#8866;</a
      ><a name="2298"
      > </a
      ><a name="2299" href="StlcProp.html#2288" class="Bound"
      >M</a
      ><a name="2300"
      > </a
      ><a name="2301" href="Stlc.html#4116" class="Datatype Operator"
      >&#8712;</a
      ><a name="2302"
      > </a
      ><a name="2303" href="StlcProp.html#2290" class="Bound"
      >A</a
      ><a name="2304"
      > </a
      ><a name="2305" class="Symbol"
      >&#8594;</a
      ><a name="2306"
      > </a
      ><a name="2307" href="Stlc.html#1581" class="Datatype"
      >value</a
      ><a name="2312"
      > </a
      ><a name="2313" href="StlcProp.html#2288" class="Bound"
      >M</a
      ><a name="2314"
      > </a
      ><a name="2315" href="https://agda.github.io/agda-stdlib/Data.Sum.html#433" class="Datatype Operator"
      >&#8846;</a
      ><a name="2316"
      > </a
      ><a name="2317" href="https://agda.github.io/agda-stdlib/Data.Product.html#823" class="Function"
      >&#8707;</a
      ><a name="2318"
      > </a
      ><a name="2319" class="Symbol"
      >&#955;</a
      ><a name="2320"
      > </a
      ><a name="2321" href="StlcProp.html#2321" class="Bound"
      >N</a
      ><a name="2322"
      > </a
      ><a name="2323" class="Symbol"
      >&#8594;</a
      ><a name="2324"
      > </a
      ><a name="2325" href="StlcProp.html#2288" class="Bound"
      >M</a
      ><a name="2326"
      > </a
      ><a name="2327" href="Stlc.html#2241" class="Datatype Operator"
      >&#10233;</a
      ><a name="2328"
      > </a
      ><a name="2329" href="StlcProp.html#2321" class="Bound"
      >N</a
      >

</pre>

_Proof_: By induction on the derivation of $$\vdash t : A$$.

  - The last rule of the derivation cannot be `var`,
    since a variable is never well typed in an empty context.

  - The `true`, `false`, and `abs` cases are trivial, since in
    each of these cases we can see by inspecting the rule that $$t$$
    is a value.

  - If the last rule of the derivation is `app`, then $$t$$ has the
    form $$t_1\;t_2$$ for som e$$t_1$$ and $$t_2$$, where we know that
    $$t_1$$ and $$t_2$$ are also well typed in the empty context; in particular,
    there exists a type $$B$$ such that $$\vdash t_1 : A\to T$$ and
    $$\vdash t_2 : B$$.  By the induction hypothesis, either $$t_1$$ is a
    value or it can take a reduction step.

  - If $$t_1$$ is a value, then consider $$t_2$$, which by the other
    induction hypothesis must also either be a value or take a step.

    - Suppose $$t_2$$ is a value.  Since $$t_1$$ is a value with an
      arrow type, it must be a lambda abstraction; hence $$t_1\;t_2$$
      can take a step by `red`.

    - Otherwise, $$t_2$$ can take a step, and hence so can $$t_1\;t_2$$
      by `app2`.

  - If $$t_1$$ can take a step, then so can $$t_1 t_2$$ by `app1`.

  - If the last rule of the derivation is `if`, then $$t = \text{if }t_1
    \text{ then }t_2\text{ else }t_3$$, where $$t_1$$ has type $$bool$$.  By
    the IH, $$t_1$$ either is a value or takes a step.

  - If $$t_1$$ is a value, then since it has type $$bool$$ it must be
    either $$true$$ or $$false$$.  If it is $$true$$, then $$t$$ steps
    to $$t_2$$; otherwise it steps to $$t_3$$.

  - Otherwise, $$t_1$$ takes a step, and therefore so does $$t$$ (by `if`).

<pre class="Agda">

<a name="4029" href="StlcProp.html#2274" class="Function"
      >progress</a
      ><a name="4037"
      > </a
      ><a name="4038" class="Symbol"
      >(</a
      ><a name="4039" href="Stlc.html#4160" class="InductiveConstructor"
      >Ax</a
      ><a name="4041"
      > </a
      ><a name="4042" class="Symbol"
      >())</a
      ><a name="4045"
      >
</a
      ><a name="4046" href="StlcProp.html#2274" class="Function"
      >progress</a
      ><a name="4054"
      > </a
      ><a name="4055" class="Symbol"
      >(</a
      ><a name="4056" href="Stlc.html#4217" class="InductiveConstructor"
      >&#8658;-I</a
      ><a name="4059"
      > </a
      ><a name="4060" href="StlcProp.html#4060" class="Bound"
      >&#8866;N</a
      ><a name="4062" class="Symbol"
      >)</a
      ><a name="4063"
      > </a
      ><a name="4064" class="Symbol"
      >=</a
      ><a name="4065"
      > </a
      ><a name="4066" href="https://agda.github.io/agda-stdlib/Data.Sum.html#489" class="InductiveConstructor"
      >inj&#8321;</a
      ><a name="4070"
      > </a
      ><a name="4071" href="Stlc.html#1608" class="InductiveConstructor"
      >value-&#955;&#7488;</a
      ><a name="4079"
      >
</a
      ><a name="4080" href="StlcProp.html#2274" class="Function"
      >progress</a
      ><a name="4088"
      > </a
      ><a name="4089" class="Symbol"
      >(</a
      ><a name="4090" href="Stlc.html#4300" class="InductiveConstructor"
      >&#8658;-E</a
      ><a name="4093"
      > </a
      ><a name="4094" class="Symbol"
      >{</a
      ><a name="4095" href="StlcProp.html#4095" class="Bound"
      >&#915;</a
      ><a name="4096" class="Symbol"
      >}</a
      ><a name="4097"
      > </a
      ><a name="4098" class="Symbol"
      >{</a
      ><a name="4099" href="StlcProp.html#4099" class="Bound"
      >L</a
      ><a name="4100" class="Symbol"
      >}</a
      ><a name="4101"
      > </a
      ><a name="4102" class="Symbol"
      >{</a
      ><a name="4103" href="StlcProp.html#4103" class="Bound"
      >M</a
      ><a name="4104" class="Symbol"
      >}</a
      ><a name="4105"
      > </a
      ><a name="4106" class="Symbol"
      >{</a
      ><a name="4107" href="StlcProp.html#4107" class="Bound"
      >A</a
      ><a name="4108" class="Symbol"
      >}</a
      ><a name="4109"
      > </a
      ><a name="4110" class="Symbol"
      >{</a
      ><a name="4111" href="StlcProp.html#4111" class="Bound"
      >B</a
      ><a name="4112" class="Symbol"
      >}</a
      ><a name="4113"
      > </a
      ><a name="4114" href="StlcProp.html#4114" class="Bound"
      >&#8866;L</a
      ><a name="4116"
      > </a
      ><a name="4117" href="StlcProp.html#4117" class="Bound"
      >&#8866;M</a
      ><a name="4119" class="Symbol"
      >)</a
      ><a name="4120"
      > </a
      ><a name="4121" class="Keyword"
      >with</a
      ><a name="4125"
      > </a
      ><a name="4126" href="StlcProp.html#2274" class="Function"
      >progress</a
      ><a name="4134"
      > </a
      ><a name="4135" href="StlcProp.html#4114" class="Bound"
      >&#8866;L</a
      ><a name="4137"
      >
</a
      ><a name="4138" class="Symbol"
      >...</a
      ><a name="4141"
      > </a
      ><a name="4142" class="Symbol"
      >|</a
      ><a name="4143"
      > </a
      ><a name="4144" href="https://agda.github.io/agda-stdlib/Data.Sum.html#514" class="InductiveConstructor"
      >inj&#8322;</a
      ><a name="4148"
      > </a
      ><a name="4149" class="Symbol"
      >(</a
      ><a name="4150" href="StlcProp.html#4150" class="Bound"
      >L&#8242;</a
      ><a name="4152"
      > </a
      ><a name="4153" href="https://agda.github.io/agda-stdlib/Data.Product.html#509" class="InductiveConstructor Operator"
      >,</a
      ><a name="4154"
      > </a
      ><a name="4155" href="StlcProp.html#4155" class="Bound"
      >L&#10233;L&#8242;</a
      ><a name="4159" class="Symbol"
      >)</a
      ><a name="4160"
      > </a
      ><a name="4161" class="Symbol"
      >=</a
      ><a name="4162"
      > </a
      ><a name="4163" href="https://agda.github.io/agda-stdlib/Data.Sum.html#514" class="InductiveConstructor"
      >inj&#8322;</a
      ><a name="4167"
      > </a
      ><a name="4168" class="Symbol"
      >(</a
      ><a name="4169" href="StlcProp.html#4150" class="Bound"
      >L&#8242;</a
      ><a name="4171"
      > </a
      ><a name="4172" href="Stlc.html#1106" class="InductiveConstructor Operator"
      >&#183;&#7488;</a
      ><a name="4174"
      > </a
      ><a name="4175" href="StlcProp.html#4103" class="Bound"
      >M</a
      ><a name="4176"
      > </a
      ><a name="4177" href="https://agda.github.io/agda-stdlib/Data.Product.html#509" class="InductiveConstructor Operator"
      >,</a
      ><a name="4178"
      > </a
      ><a name="4179" href="Stlc.html#2347" class="InductiveConstructor"
      >&#947;&#8658;&#8321;</a
      ><a name="4182"
      > </a
      ><a name="4183" href="StlcProp.html#4155" class="Bound"
      >L&#10233;L&#8242;</a
      ><a name="4187" class="Symbol"
      >)</a
      ><a name="4188"
      >
</a
      ><a name="4189" class="Symbol"
      >...</a
      ><a name="4192"
      > </a
      ><a name="4193" class="Symbol"
      >|</a
      ><a name="4194"
      > </a
      ><a name="4195" href="https://agda.github.io/agda-stdlib/Data.Sum.html#489" class="InductiveConstructor"
      >inj&#8321;</a
      ><a name="4199"
      > </a
      ><a name="4200" href="StlcProp.html#4200" class="Bound"
      >valueL</a
      ><a name="4206"
      > </a
      ><a name="4207" class="Keyword"
      >with</a
      ><a name="4211"
      > </a
      ><a name="4212" href="StlcProp.html#2274" class="Function"
      >progress</a
      ><a name="4220"
      > </a
      ><a name="4221" href="StlcProp.html#4117" class="Bound"
      >&#8866;M</a
      ><a name="4223"
      >
</a
      ><a name="4224" class="Symbol"
      >...</a
      ><a name="4227"
      > </a
      ><a name="4228" class="Symbol"
      >|</a
      ><a name="4229"
      > </a
      ><a name="4230" href="https://agda.github.io/agda-stdlib/Data.Sum.html#514" class="InductiveConstructor"
      >inj&#8322;</a
      ><a name="4234"
      > </a
      ><a name="4235" class="Symbol"
      >(</a
      ><a name="4236" href="StlcProp.html#4236" class="Bound"
      >M&#8242;</a
      ><a name="4238"
      > </a
      ><a name="4239" href="https://agda.github.io/agda-stdlib/Data.Product.html#509" class="InductiveConstructor Operator"
      >,</a
      ><a name="4240"
      > </a
      ><a name="4241" href="StlcProp.html#4241" class="Bound"
      >M&#10233;M&#8242;</a
      ><a name="4245" class="Symbol"
      >)</a
      ><a name="4246"
      > </a
      ><a name="4247" class="Symbol"
      >=</a
      ><a name="4248"
      > </a
      ><a name="4249" href="https://agda.github.io/agda-stdlib/Data.Sum.html#514" class="InductiveConstructor"
      >inj&#8322;</a
      ><a name="4253"
      > </a
      ><a name="4254" class="Symbol"
      >(</a
      ><a name="4255" href="StlcProp.html#4099" class="Bound"
      >L</a
      ><a name="4256"
      > </a
      ><a name="4257" href="Stlc.html#1106" class="InductiveConstructor Operator"
      >&#183;&#7488;</a
      ><a name="4259"
      > </a
      ><a name="4260" href="StlcProp.html#4236" class="Bound"
      >M&#8242;</a
      ><a name="4262"
      > </a
      ><a name="4263" href="https://agda.github.io/agda-stdlib/Data.Product.html#509" class="InductiveConstructor Operator"
      >,</a
      ><a name="4264"
      > </a
      ><a name="4265" href="Stlc.html#2406" class="InductiveConstructor"
      >&#947;&#8658;&#8322;</a
      ><a name="4268"
      > </a
      ><a name="4269" href="StlcProp.html#4200" class="Bound"
      >valueL</a
      ><a name="4275"
      > </a
      ><a name="4276" href="StlcProp.html#4241" class="Bound"
      >M&#10233;M&#8242;</a
      ><a name="4280" class="Symbol"
      >)</a
      ><a name="4281"
      >
</a
      ><a name="4282" class="Symbol"
      >...</a
      ><a name="4285"
      > </a
      ><a name="4286" class="Symbol"
      >|</a
      ><a name="4287"
      > </a
      ><a name="4288" href="https://agda.github.io/agda-stdlib/Data.Sum.html#489" class="InductiveConstructor"
      >inj&#8321;</a
      ><a name="4292"
      > </a
      ><a name="4293" href="StlcProp.html#4293" class="Bound"
      >valueM</a
      ><a name="4299"
      > </a
      ><a name="4300" class="Keyword"
      >with</a
      ><a name="4304"
      > </a
      ><a name="4305" href="StlcProp.html#1486" class="Function"
      >canonicalFormsLemma</a
      ><a name="4324"
      > </a
      ><a name="4325" href="StlcProp.html#4114" class="Bound"
      >&#8866;L</a
      ><a name="4327"
      > </a
      ><a name="4328" href="StlcProp.html#4200" class="Bound"
      >valueL</a
      ><a name="4334"
      >
</a
      ><a name="4335" class="Symbol"
      >...</a
      ><a name="4338"
      > </a
      ><a name="4339" class="Symbol"
      >|</a
      ><a name="4340"
      > </a
      ><a name="4341" href="StlcProp.html#1183" class="InductiveConstructor"
      >canonical-&#955;&#7488;</a
      ><a name="4353"
      > </a
      ><a name="4354" class="Symbol"
      >{</a
      ><a name="4355" href="StlcProp.html#4355" class="Bound"
      >x</a
      ><a name="4356" class="Symbol"
      >}</a
      ><a name="4357"
      > </a
      ><a name="4358" class="Symbol"
      >{</a
      ><a name="4359" class="DottedPattern Symbol"
      >.</a
      ><a name="4360" href="StlcProp.html#4107" class="DottedPattern Bound"
      >A</a
      ><a name="4361" class="Symbol"
      >}</a
      ><a name="4362"
      > </a
      ><a name="4363" class="Symbol"
      >{</a
      ><a name="4364" href="StlcProp.html#4364" class="Bound"
      >N</a
      ><a name="4365" class="Symbol"
      >}</a
      ><a name="4366"
      > </a
      ><a name="4367" class="Symbol"
      >{</a
      ><a name="4368" class="DottedPattern Symbol"
      >.</a
      ><a name="4369" href="StlcProp.html#4111" class="DottedPattern Bound"
      >B</a
      ><a name="4370" class="Symbol"
      >}</a
      ><a name="4371"
      > </a
      ><a name="4372" class="Symbol"
      >=</a
      ><a name="4373"
      > </a
      ><a name="4374" href="https://agda.github.io/agda-stdlib/Data.Sum.html#514" class="InductiveConstructor"
      >inj&#8322;</a
      ><a name="4378"
      > </a
      ><a name="4379" class="Symbol"
      >((</a
      ><a name="4381" href="StlcProp.html#4364" class="Bound"
      >N</a
      ><a name="4382"
      > </a
      ><a name="4383" href="Stlc.html#1756" class="Function Operator"
      >[</a
      ><a name="4384"
      > </a
      ><a name="4385" href="StlcProp.html#4355" class="Bound"
      >x</a
      ><a name="4386"
      > </a
      ><a name="4387" href="Stlc.html#1756" class="Function Operator"
      >:=</a
      ><a name="4389"
      > </a
      ><a name="4390" href="StlcProp.html#4103" class="Bound"
      >M</a
      ><a name="4391"
      > </a
      ><a name="4392" href="Stlc.html#1756" class="Function Operator"
      >]</a
      ><a name="4393" class="Symbol"
      >)</a
      ><a name="4394"
      > </a
      ><a name="4395" href="https://agda.github.io/agda-stdlib/Data.Product.html#509" class="InductiveConstructor Operator"
      >,</a
      ><a name="4396"
      > </a
      ><a name="4397" href="Stlc.html#2273" class="InductiveConstructor"
      >&#946;&#8658;</a
      ><a name="4399"
      > </a
      ><a name="4400" href="StlcProp.html#4293" class="Bound"
      >valueM</a
      ><a name="4406" class="Symbol"
      >)</a
      ><a name="4407"
      >
</a
      ><a name="4408" href="StlcProp.html#2274" class="Function"
      >progress</a
      ><a name="4416"
      > </a
      ><a name="4417" href="Stlc.html#4381" class="InductiveConstructor"
      >&#120121;-I&#8321;</a
      ><a name="4421"
      > </a
      ><a name="4422" class="Symbol"
      >=</a
      ><a name="4423"
      > </a
      ><a name="4424" href="https://agda.github.io/agda-stdlib/Data.Sum.html#489" class="InductiveConstructor"
      >inj&#8321;</a
      ><a name="4428"
      > </a
      ><a name="4429" href="Stlc.html#1654" class="InductiveConstructor"
      >value-true&#7488;</a
      ><a name="4440"
      >
</a
      ><a name="4441" href="StlcProp.html#2274" class="Function"
      >progress</a
      ><a name="4449"
      > </a
      ><a name="4450" href="Stlc.html#4416" class="InductiveConstructor"
      >&#120121;-I&#8322;</a
      ><a name="4454"
      > </a
      ><a name="4455" class="Symbol"
      >=</a
      ><a name="4456"
      > </a
      ><a name="4457" href="https://agda.github.io/agda-stdlib/Data.Sum.html#489" class="InductiveConstructor"
      >inj&#8321;</a
      ><a name="4461"
      > </a
      ><a name="4462" href="Stlc.html#1684" class="InductiveConstructor"
      >value-false&#7488;</a
      ><a name="4474"
      >
</a
      ><a name="4475" href="StlcProp.html#2274" class="Function"
      >progress</a
      ><a name="4483"
      > </a
      ><a name="4484" class="Symbol"
      >(</a
      ><a name="4485" href="Stlc.html#4452" class="InductiveConstructor"
      >&#120121;-E</a
      ><a name="4488"
      > </a
      ><a name="4489" class="Symbol"
      >{</a
      ><a name="4490" href="StlcProp.html#4490" class="Bound"
      >&#915;</a
      ><a name="4491" class="Symbol"
      >}</a
      ><a name="4492"
      > </a
      ><a name="4493" class="Symbol"
      >{</a
      ><a name="4494" href="StlcProp.html#4494" class="Bound"
      >L</a
      ><a name="4495" class="Symbol"
      >}</a
      ><a name="4496"
      > </a
      ><a name="4497" class="Symbol"
      >{</a
      ><a name="4498" href="StlcProp.html#4498" class="Bound"
      >M</a
      ><a name="4499" class="Symbol"
      >}</a
      ><a name="4500"
      > </a
      ><a name="4501" class="Symbol"
      >{</a
      ><a name="4502" href="StlcProp.html#4502" class="Bound"
      >N</a
      ><a name="4503" class="Symbol"
      >}</a
      ><a name="4504"
      > </a
      ><a name="4505" class="Symbol"
      >{</a
      ><a name="4506" href="StlcProp.html#4506" class="Bound"
      >A</a
      ><a name="4507" class="Symbol"
      >}</a
      ><a name="4508"
      > </a
      ><a name="4509" href="StlcProp.html#4509" class="Bound"
      >&#8866;L</a
      ><a name="4511"
      > </a
      ><a name="4512" href="StlcProp.html#4512" class="Bound"
      >&#8866;M</a
      ><a name="4514"
      > </a
      ><a name="4515" href="StlcProp.html#4515" class="Bound"
      >&#8866;N</a
      ><a name="4517" class="Symbol"
      >)</a
      ><a name="4518"
      > </a
      ><a name="4519" class="Keyword"
      >with</a
      ><a name="4523"
      > </a
      ><a name="4524" href="StlcProp.html#2274" class="Function"
      >progress</a
      ><a name="4532"
      > </a
      ><a name="4533" href="StlcProp.html#4509" class="Bound"
      >&#8866;L</a
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
      ><a name="4542" href="https://agda.github.io/agda-stdlib/Data.Sum.html#514" class="InductiveConstructor"
      >inj&#8322;</a
      ><a name="4546"
      > </a
      ><a name="4547" class="Symbol"
      >(</a
      ><a name="4548" href="StlcProp.html#4548" class="Bound"
      >L&#8242;</a
      ><a name="4550"
      > </a
      ><a name="4551" href="https://agda.github.io/agda-stdlib/Data.Product.html#509" class="InductiveConstructor Operator"
      >,</a
      ><a name="4552"
      > </a
      ><a name="4553" href="StlcProp.html#4553" class="Bound"
      >L&#10233;L&#8242;</a
      ><a name="4557" class="Symbol"
      >)</a
      ><a name="4558"
      > </a
      ><a name="4559" class="Symbol"
      >=</a
      ><a name="4560"
      > </a
      ><a name="4561" href="https://agda.github.io/agda-stdlib/Data.Sum.html#514" class="InductiveConstructor"
      >inj&#8322;</a
      ><a name="4565"
      > </a
      ><a name="4566" class="Symbol"
      >((</a
      ><a name="4568" href="Stlc.html#1165" class="InductiveConstructor Operator"
      >if&#7488;</a
      ><a name="4571"
      > </a
      ><a name="4572" href="StlcProp.html#4548" class="Bound"
      >L&#8242;</a
      ><a name="4574"
      > </a
      ><a name="4575" href="Stlc.html#1165" class="InductiveConstructor Operator"
      >then</a
      ><a name="4579"
      > </a
      ><a name="4580" href="StlcProp.html#4498" class="Bound"
      >M</a
      ><a name="4581"
      > </a
      ><a name="4582" href="Stlc.html#1165" class="InductiveConstructor Operator"
      >else</a
      ><a name="4586"
      > </a
      ><a name="4587" href="StlcProp.html#4502" class="Bound"
      >N</a
      ><a name="4588" class="Symbol"
      >)</a
      ><a name="4589"
      > </a
      ><a name="4590" href="https://agda.github.io/agda-stdlib/Data.Product.html#509" class="InductiveConstructor Operator"
      >,</a
      ><a name="4591"
      > </a
      ><a name="4592" href="Stlc.html#2584" class="InductiveConstructor"
      >&#947;&#120121;</a
      ><a name="4594"
      > </a
      ><a name="4595" href="StlcProp.html#4553" class="Bound"
      >L&#10233;L&#8242;</a
      ><a name="4599" class="Symbol"
      >)</a
      ><a name="4600"
      >
</a
      ><a name="4601" class="Symbol"
      >...</a
      ><a name="4604"
      > </a
      ><a name="4605" class="Symbol"
      >|</a
      ><a name="4606"
      > </a
      ><a name="4607" href="https://agda.github.io/agda-stdlib/Data.Sum.html#489" class="InductiveConstructor"
      >inj&#8321;</a
      ><a name="4611"
      > </a
      ><a name="4612" href="StlcProp.html#4612" class="Bound"
      >valueL</a
      ><a name="4618"
      > </a
      ><a name="4619" class="Keyword"
      >with</a
      ><a name="4623"
      > </a
      ><a name="4624" href="StlcProp.html#1486" class="Function"
      >canonicalFormsLemma</a
      ><a name="4643"
      > </a
      ><a name="4644" href="StlcProp.html#4509" class="Bound"
      >&#8866;L</a
      ><a name="4646"
      > </a
      ><a name="4647" href="StlcProp.html#4612" class="Bound"
      >valueL</a
      ><a name="4653"
      >
</a
      ><a name="4654" class="Symbol"
      >...</a
      ><a name="4657"
      > </a
      ><a name="4658" class="Symbol"
      >|</a
      ><a name="4659"
      > </a
      ><a name="4660" href="StlcProp.html#1251" class="InductiveConstructor"
      >canonical-true&#7488;</a
      ><a name="4675"
      > </a
      ><a name="4676" class="Symbol"
      >=</a
      ><a name="4677"
      > </a
      ><a name="4678" href="https://agda.github.io/agda-stdlib/Data.Sum.html#514" class="InductiveConstructor"
      >inj&#8322;</a
      ><a name="4682"
      > </a
      ><a name="4683" class="Symbol"
      >(</a
      ><a name="4684" href="StlcProp.html#4498" class="Bound"
      >M</a
      ><a name="4685"
      > </a
      ><a name="4686" href="https://agda.github.io/agda-stdlib/Data.Product.html#509" class="InductiveConstructor Operator"
      >,</a
      ><a name="4687"
      > </a
      ><a name="4688" href="Stlc.html#2479" class="InductiveConstructor"
      >&#946;&#120121;&#8321;</a
      ><a name="4691" class="Symbol"
      >)</a
      ><a name="4692"
      >
</a
      ><a name="4693" class="Symbol"
      >...</a
      ><a name="4696"
      > </a
      ><a name="4697" class="Symbol"
      >|</a
      ><a name="4698"
      > </a
      ><a name="4699" href="StlcProp.html#1293" class="InductiveConstructor"
      >canonical-false&#7488;</a
      ><a name="4715"
      > </a
      ><a name="4716" class="Symbol"
      >=</a
      ><a name="4717"
      > </a
      ><a name="4718" href="https://agda.github.io/agda-stdlib/Data.Sum.html#514" class="InductiveConstructor"
      >inj&#8322;</a
      ><a name="4722"
      > </a
      ><a name="4723" class="Symbol"
      >(</a
      ><a name="4724" href="StlcProp.html#4502" class="Bound"
      >N</a
      ><a name="4725"
      > </a
      ><a name="4726" href="https://agda.github.io/agda-stdlib/Data.Product.html#509" class="InductiveConstructor Operator"
      >,</a
      ><a name="4727"
      > </a
      ><a name="4728" href="Stlc.html#2531" class="InductiveConstructor"
      >&#946;&#120121;&#8322;</a
      ><a name="4731" class="Symbol"
      >)</a
      >

</pre>

#### Exercise: 3 stars, optional (progress_from_term_ind)
Show that progress can also be proved by induction on terms
instead of induction on typing derivations.

<pre class="Agda">

<a name="4921" class="Keyword"
      >postulate</a
      ><a name="4930"
      >
  </a
      ><a name="4933" href="StlcProp.html#4933" class="Postulate"
      >progress&#8242;</a
      ><a name="4942"
      > </a
      ><a name="4943" class="Symbol"
      >:</a
      ><a name="4944"
      > </a
      ><a name="4945" class="Symbol"
      >&#8704;</a
      ><a name="4946"
      > </a
      ><a name="4947" class="Symbol"
      >{</a
      ><a name="4948" href="StlcProp.html#4948" class="Bound"
      >M</a
      ><a name="4949"
      > </a
      ><a name="4950" href="StlcProp.html#4950" class="Bound"
      >A</a
      ><a name="4951" class="Symbol"
      >}</a
      ><a name="4952"
      > </a
      ><a name="4953" class="Symbol"
      >&#8594;</a
      ><a name="4954"
      > </a
      ><a name="4955" href="Maps.html#11235" class="Function"
      >&#8709;</a
      ><a name="4956"
      > </a
      ><a name="4957" href="Stlc.html#4116" class="Datatype Operator"
      >&#8866;</a
      ><a name="4958"
      > </a
      ><a name="4959" href="StlcProp.html#4948" class="Bound"
      >M</a
      ><a name="4960"
      > </a
      ><a name="4961" href="Stlc.html#4116" class="Datatype Operator"
      >&#8712;</a
      ><a name="4962"
      > </a
      ><a name="4963" href="StlcProp.html#4950" class="Bound"
      >A</a
      ><a name="4964"
      > </a
      ><a name="4965" class="Symbol"
      >&#8594;</a
      ><a name="4966"
      > </a
      ><a name="4967" href="Stlc.html#1581" class="Datatype"
      >value</a
      ><a name="4972"
      > </a
      ><a name="4973" href="StlcProp.html#4948" class="Bound"
      >M</a
      ><a name="4974"
      > </a
      ><a name="4975" href="https://agda.github.io/agda-stdlib/Data.Sum.html#433" class="Datatype Operator"
      >&#8846;</a
      ><a name="4976"
      > </a
      ><a name="4977" href="https://agda.github.io/agda-stdlib/Data.Product.html#823" class="Function"
      >&#8707;</a
      ><a name="4978"
      > </a
      ><a name="4979" class="Symbol"
      >&#955;</a
      ><a name="4980"
      > </a
      ><a name="4981" href="StlcProp.html#4981" class="Bound"
      >N</a
      ><a name="4982"
      > </a
      ><a name="4983" class="Symbol"
      >&#8594;</a
      ><a name="4984"
      > </a
      ><a name="4985" href="StlcProp.html#4948" class="Bound"
      >M</a
      ><a name="4986"
      > </a
      ><a name="4987" href="Stlc.html#2241" class="Datatype Operator"
      >&#10233;</a
      ><a name="4988"
      > </a
      ><a name="4989" href="StlcProp.html#4981" class="Bound"
      >N</a
      >

</pre>

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
    $$red$$ rule, whose definition uses the substitution operation.  To see that
    this step preserves typing, we need to know that the substitution itself
    does.  So we prove a... 

  - _substitution lemma_, stating that substituting a (closed)
    term $$s$$ for a variable $$x$$ in a term $$t$$ preserves the type
    of $$t$$.  The proof goes by induction on the form of $$t$$ and
    requires looking at all the different cases in the definition
    of substitition.  This time, the tricky cases are the ones for
    variables and for function abstractions.  In both cases, we
    discover that we need to take a term $$s$$ that has been shown
    to be well-typed in some context $$\Gamma$$ and consider the same
    term $$s$$ in a slightly different context $$\Gamma'$$.  For this
    we prove a...

  - _context invariance_ lemma, showing that typing is preserved
    under "inessential changes" to the context $$\Gamma$$---in
    particular, changes that do not affect any of the free
    variables of the term.  And finally, for this, we need a
    careful definition of...

  - the _free variables_ of a term---i.e., those variables
    mentioned in a term and not in the scope of an enclosing
    function abstraction binding a variable of the same name.

To make Agda happy, we need to formalize the story in the opposite
order...


### Free Occurrences

A variable $$x$$ _appears free in_ a term $$M$$ if $$M$$ contains some
occurrence of $$x$$ that is not under an abstraction over $$x$$.
For example:

  - $$y$$ appears free, but $$x$$ does not, in $$λᵀ x ∈ (A ⇒ B) ⇒ x ·ᵀ y$$
  - both $$x$$ and $$y$$ appear free in $$(λᵀ x ∈ (A ⇒ B) ⇒ x ·ᵀ y) ·ᵀ x$$
  - no variables appear free in $$λᵀ x ∈ (A ⇒ B) ⇒ (λᵀ y ∈ A ⇒ x ·ᵀ y)$$

Formally:

<pre class="Agda">

<a name="7431" class="Keyword"
      >data</a
      ><a name="7435"
      > </a
      ><a name="7436" href="StlcProp.html#7436" class="Datatype Operator"
      >_FreeIn_</a
      ><a name="7444"
      > </a
      ><a name="7445" class="Symbol"
      >:</a
      ><a name="7446"
      > </a
      ><a name="7447" href="Maps.html#2215" class="Datatype"
      >Id</a
      ><a name="7449"
      > </a
      ><a name="7450" class="Symbol"
      >&#8594;</a
      ><a name="7451"
      > </a
      ><a name="7452" href="Stlc.html#1032" class="Datatype"
      >Term</a
      ><a name="7456"
      > </a
      ><a name="7457" class="Symbol"
      >&#8594;</a
      ><a name="7458"
      > </a
      ><a name="7459" class="PrimitiveType"
      >Set</a
      ><a name="7462"
      > </a
      ><a name="7463" class="Keyword"
      >where</a
      ><a name="7468"
      >
  </a
      ><a name="7471" href="StlcProp.html#7471" class="InductiveConstructor"
      >free-var&#7488;</a
      ><a name="7480"
      >  </a
      ><a name="7482" class="Symbol"
      >:</a
      ><a name="7483"
      > </a
      ><a name="7484" class="Symbol"
      >&#8704;</a
      ><a name="7485"
      > </a
      ><a name="7486" class="Symbol"
      >{</a
      ><a name="7487" href="StlcProp.html#7487" class="Bound"
      >x</a
      ><a name="7488" class="Symbol"
      >}</a
      ><a name="7489"
      > </a
      ><a name="7490" class="Symbol"
      >&#8594;</a
      ><a name="7491"
      > </a
      ><a name="7492" href="StlcProp.html#7487" class="Bound"
      >x</a
      ><a name="7493"
      > </a
      ><a name="7494" href="StlcProp.html#7436" class="Datatype Operator"
      >FreeIn</a
      ><a name="7500"
      > </a
      ><a name="7501" class="Symbol"
      >(</a
      ><a name="7502" href="Stlc.html#1051" class="InductiveConstructor"
      >var&#7488;</a
      ><a name="7506"
      > </a
      ><a name="7507" href="StlcProp.html#7487" class="Bound"
      >x</a
      ><a name="7508" class="Symbol"
      >)</a
      ><a name="7509"
      >
  </a
      ><a name="7512" href="StlcProp.html#7512" class="InductiveConstructor"
      >free-&#955;&#7488;</a
      ><a name="7519"
      >  </a
      ><a name="7521" class="Symbol"
      >:</a
      ><a name="7522"
      > </a
      ><a name="7523" class="Symbol"
      >&#8704;</a
      ><a name="7524"
      > </a
      ><a name="7525" class="Symbol"
      >{</a
      ><a name="7526" href="StlcProp.html#7526" class="Bound"
      >x</a
      ><a name="7527"
      > </a
      ><a name="7528" href="StlcProp.html#7528" class="Bound"
      >y</a
      ><a name="7529"
      > </a
      ><a name="7530" href="StlcProp.html#7530" class="Bound"
      >A</a
      ><a name="7531"
      > </a
      ><a name="7532" href="StlcProp.html#7532" class="Bound"
      >N</a
      ><a name="7533" class="Symbol"
      >}</a
      ><a name="7534"
      > </a
      ><a name="7535" class="Symbol"
      >&#8594;</a
      ><a name="7536"
      > </a
      ><a name="7537" href="StlcProp.html#7528" class="Bound"
      >y</a
      ><a name="7538"
      > </a
      ><a name="7539" href="https://agda.github.io/agda-stdlib/Relation.Binary.Core.html#4493" class="Function Operator"
      >&#8802;</a
      ><a name="7540"
      > </a
      ><a name="7541" href="StlcProp.html#7526" class="Bound"
      >x</a
      ><a name="7542"
      > </a
      ><a name="7543" class="Symbol"
      >&#8594;</a
      ><a name="7544"
      > </a
      ><a name="7545" href="StlcProp.html#7526" class="Bound"
      >x</a
      ><a name="7546"
      > </a
      ><a name="7547" href="StlcProp.html#7436" class="Datatype Operator"
      >FreeIn</a
      ><a name="7553"
      > </a
      ><a name="7554" href="StlcProp.html#7532" class="Bound"
      >N</a
      ><a name="7555"
      > </a
      ><a name="7556" class="Symbol"
      >&#8594;</a
      ><a name="7557"
      > </a
      ><a name="7558" href="StlcProp.html#7526" class="Bound"
      >x</a
      ><a name="7559"
      > </a
      ><a name="7560" href="StlcProp.html#7436" class="Datatype Operator"
      >FreeIn</a
      ><a name="7566"
      > </a
      ><a name="7567" class="Symbol"
      >(</a
      ><a name="7568" href="Stlc.html#1070" class="InductiveConstructor Operator"
      >&#955;&#7488;</a
      ><a name="7570"
      > </a
      ><a name="7571" href="StlcProp.html#7528" class="Bound"
      >y</a
      ><a name="7572"
      > </a
      ><a name="7573" href="Stlc.html#1070" class="InductiveConstructor Operator"
      >&#8712;</a
      ><a name="7574"
      > </a
      ><a name="7575" href="StlcProp.html#7530" class="Bound"
      >A</a
      ><a name="7576"
      > </a
      ><a name="7577" href="Stlc.html#1070" class="InductiveConstructor Operator"
      >&#8658;</a
      ><a name="7578"
      > </a
      ><a name="7579" href="StlcProp.html#7532" class="Bound"
      >N</a
      ><a name="7580" class="Symbol"
      >)</a
      ><a name="7581"
      >
  </a
      ><a name="7584" href="StlcProp.html#7584" class="InductiveConstructor"
      >free-&#183;&#7488;&#8321;</a
      ><a name="7592"
      > </a
      ><a name="7593" class="Symbol"
      >:</a
      ><a name="7594"
      > </a
      ><a name="7595" class="Symbol"
      >&#8704;</a
      ><a name="7596"
      > </a
      ><a name="7597" class="Symbol"
      >{</a
      ><a name="7598" href="StlcProp.html#7598" class="Bound"
      >x</a
      ><a name="7599"
      > </a
      ><a name="7600" href="StlcProp.html#7600" class="Bound"
      >L</a
      ><a name="7601"
      > </a
      ><a name="7602" href="StlcProp.html#7602" class="Bound"
      >M</a
      ><a name="7603" class="Symbol"
      >}</a
      ><a name="7604"
      > </a
      ><a name="7605" class="Symbol"
      >&#8594;</a
      ><a name="7606"
      > </a
      ><a name="7607" href="StlcProp.html#7598" class="Bound"
      >x</a
      ><a name="7608"
      > </a
      ><a name="7609" href="StlcProp.html#7436" class="Datatype Operator"
      >FreeIn</a
      ><a name="7615"
      > </a
      ><a name="7616" href="StlcProp.html#7600" class="Bound"
      >L</a
      ><a name="7617"
      > </a
      ><a name="7618" class="Symbol"
      >&#8594;</a
      ><a name="7619"
      > </a
      ><a name="7620" href="StlcProp.html#7598" class="Bound"
      >x</a
      ><a name="7621"
      > </a
      ><a name="7622" href="StlcProp.html#7436" class="Datatype Operator"
      >FreeIn</a
      ><a name="7628"
      > </a
      ><a name="7629" class="Symbol"
      >(</a
      ><a name="7630" href="StlcProp.html#7600" class="Bound"
      >L</a
      ><a name="7631"
      > </a
      ><a name="7632" href="Stlc.html#1106" class="InductiveConstructor Operator"
      >&#183;&#7488;</a
      ><a name="7634"
      > </a
      ><a name="7635" href="StlcProp.html#7602" class="Bound"
      >M</a
      ><a name="7636" class="Symbol"
      >)</a
      ><a name="7637"
      >
  </a
      ><a name="7640" href="StlcProp.html#7640" class="InductiveConstructor"
      >free-&#183;&#7488;&#8322;</a
      ><a name="7648"
      > </a
      ><a name="7649" class="Symbol"
      >:</a
      ><a name="7650"
      > </a
      ><a name="7651" class="Symbol"
      >&#8704;</a
      ><a name="7652"
      > </a
      ><a name="7653" class="Symbol"
      >{</a
      ><a name="7654" href="StlcProp.html#7654" class="Bound"
      >x</a
      ><a name="7655"
      > </a
      ><a name="7656" href="StlcProp.html#7656" class="Bound"
      >L</a
      ><a name="7657"
      > </a
      ><a name="7658" href="StlcProp.html#7658" class="Bound"
      >M</a
      ><a name="7659" class="Symbol"
      >}</a
      ><a name="7660"
      > </a
      ><a name="7661" class="Symbol"
      >&#8594;</a
      ><a name="7662"
      > </a
      ><a name="7663" href="StlcProp.html#7654" class="Bound"
      >x</a
      ><a name="7664"
      > </a
      ><a name="7665" href="StlcProp.html#7436" class="Datatype Operator"
      >FreeIn</a
      ><a name="7671"
      > </a
      ><a name="7672" href="StlcProp.html#7658" class="Bound"
      >M</a
      ><a name="7673"
      > </a
      ><a name="7674" class="Symbol"
      >&#8594;</a
      ><a name="7675"
      > </a
      ><a name="7676" href="StlcProp.html#7654" class="Bound"
      >x</a
      ><a name="7677"
      > </a
      ><a name="7678" href="StlcProp.html#7436" class="Datatype Operator"
      >FreeIn</a
      ><a name="7684"
      > </a
      ><a name="7685" class="Symbol"
      >(</a
      ><a name="7686" href="StlcProp.html#7656" class="Bound"
      >L</a
      ><a name="7687"
      > </a
      ><a name="7688" href="Stlc.html#1106" class="InductiveConstructor Operator"
      >&#183;&#7488;</a
      ><a name="7690"
      > </a
      ><a name="7691" href="StlcProp.html#7658" class="Bound"
      >M</a
      ><a name="7692" class="Symbol"
      >)</a
      ><a name="7693"
      >
  </a
      ><a name="7696" href="StlcProp.html#7696" class="InductiveConstructor"
      >free-if&#7488;&#8321;</a
      ><a name="7705"
      > </a
      ><a name="7706" class="Symbol"
      >:</a
      ><a name="7707"
      > </a
      ><a name="7708" class="Symbol"
      >&#8704;</a
      ><a name="7709"
      > </a
      ><a name="7710" class="Symbol"
      >{</a
      ><a name="7711" href="StlcProp.html#7711" class="Bound"
      >x</a
      ><a name="7712"
      > </a
      ><a name="7713" href="StlcProp.html#7713" class="Bound"
      >L</a
      ><a name="7714"
      > </a
      ><a name="7715" href="StlcProp.html#7715" class="Bound"
      >M</a
      ><a name="7716"
      > </a
      ><a name="7717" href="StlcProp.html#7717" class="Bound"
      >N</a
      ><a name="7718" class="Symbol"
      >}</a
      ><a name="7719"
      > </a
      ><a name="7720" class="Symbol"
      >&#8594;</a
      ><a name="7721"
      > </a
      ><a name="7722" href="StlcProp.html#7711" class="Bound"
      >x</a
      ><a name="7723"
      > </a
      ><a name="7724" href="StlcProp.html#7436" class="Datatype Operator"
      >FreeIn</a
      ><a name="7730"
      > </a
      ><a name="7731" href="StlcProp.html#7713" class="Bound"
      >L</a
      ><a name="7732"
      > </a
      ><a name="7733" class="Symbol"
      >&#8594;</a
      ><a name="7734"
      > </a
      ><a name="7735" href="StlcProp.html#7711" class="Bound"
      >x</a
      ><a name="7736"
      > </a
      ><a name="7737" href="StlcProp.html#7436" class="Datatype Operator"
      >FreeIn</a
      ><a name="7743"
      > </a
      ><a name="7744" class="Symbol"
      >(</a
      ><a name="7745" href="Stlc.html#1165" class="InductiveConstructor Operator"
      >if&#7488;</a
      ><a name="7748"
      > </a
      ><a name="7749" href="StlcProp.html#7713" class="Bound"
      >L</a
      ><a name="7750"
      > </a
      ><a name="7751" href="Stlc.html#1165" class="InductiveConstructor Operator"
      >then</a
      ><a name="7755"
      > </a
      ><a name="7756" href="StlcProp.html#7715" class="Bound"
      >M</a
      ><a name="7757"
      > </a
      ><a name="7758" href="Stlc.html#1165" class="InductiveConstructor Operator"
      >else</a
      ><a name="7762"
      > </a
      ><a name="7763" href="StlcProp.html#7717" class="Bound"
      >N</a
      ><a name="7764" class="Symbol"
      >)</a
      ><a name="7765"
      >
  </a
      ><a name="7768" href="StlcProp.html#7768" class="InductiveConstructor"
      >free-if&#7488;&#8322;</a
      ><a name="7777"
      > </a
      ><a name="7778" class="Symbol"
      >:</a
      ><a name="7779"
      > </a
      ><a name="7780" class="Symbol"
      >&#8704;</a
      ><a name="7781"
      > </a
      ><a name="7782" class="Symbol"
      >{</a
      ><a name="7783" href="StlcProp.html#7783" class="Bound"
      >x</a
      ><a name="7784"
      > </a
      ><a name="7785" href="StlcProp.html#7785" class="Bound"
      >L</a
      ><a name="7786"
      > </a
      ><a name="7787" href="StlcProp.html#7787" class="Bound"
      >M</a
      ><a name="7788"
      > </a
      ><a name="7789" href="StlcProp.html#7789" class="Bound"
      >N</a
      ><a name="7790" class="Symbol"
      >}</a
      ><a name="7791"
      > </a
      ><a name="7792" class="Symbol"
      >&#8594;</a
      ><a name="7793"
      > </a
      ><a name="7794" href="StlcProp.html#7783" class="Bound"
      >x</a
      ><a name="7795"
      > </a
      ><a name="7796" href="StlcProp.html#7436" class="Datatype Operator"
      >FreeIn</a
      ><a name="7802"
      > </a
      ><a name="7803" href="StlcProp.html#7787" class="Bound"
      >M</a
      ><a name="7804"
      > </a
      ><a name="7805" class="Symbol"
      >&#8594;</a
      ><a name="7806"
      > </a
      ><a name="7807" href="StlcProp.html#7783" class="Bound"
      >x</a
      ><a name="7808"
      > </a
      ><a name="7809" href="StlcProp.html#7436" class="Datatype Operator"
      >FreeIn</a
      ><a name="7815"
      > </a
      ><a name="7816" class="Symbol"
      >(</a
      ><a name="7817" href="Stlc.html#1165" class="InductiveConstructor Operator"
      >if&#7488;</a
      ><a name="7820"
      > </a
      ><a name="7821" href="StlcProp.html#7785" class="Bound"
      >L</a
      ><a name="7822"
      > </a
      ><a name="7823" href="Stlc.html#1165" class="InductiveConstructor Operator"
      >then</a
      ><a name="7827"
      > </a
      ><a name="7828" href="StlcProp.html#7787" class="Bound"
      >M</a
      ><a name="7829"
      > </a
      ><a name="7830" href="Stlc.html#1165" class="InductiveConstructor Operator"
      >else</a
      ><a name="7834"
      > </a
      ><a name="7835" href="StlcProp.html#7789" class="Bound"
      >N</a
      ><a name="7836" class="Symbol"
      >)</a
      ><a name="7837"
      >
  </a
      ><a name="7840" href="StlcProp.html#7840" class="InductiveConstructor"
      >free-if&#7488;&#8323;</a
      ><a name="7849"
      > </a
      ><a name="7850" class="Symbol"
      >:</a
      ><a name="7851"
      > </a
      ><a name="7852" class="Symbol"
      >&#8704;</a
      ><a name="7853"
      > </a
      ><a name="7854" class="Symbol"
      >{</a
      ><a name="7855" href="StlcProp.html#7855" class="Bound"
      >x</a
      ><a name="7856"
      > </a
      ><a name="7857" href="StlcProp.html#7857" class="Bound"
      >L</a
      ><a name="7858"
      > </a
      ><a name="7859" href="StlcProp.html#7859" class="Bound"
      >M</a
      ><a name="7860"
      > </a
      ><a name="7861" href="StlcProp.html#7861" class="Bound"
      >N</a
      ><a name="7862" class="Symbol"
      >}</a
      ><a name="7863"
      > </a
      ><a name="7864" class="Symbol"
      >&#8594;</a
      ><a name="7865"
      > </a
      ><a name="7866" href="StlcProp.html#7855" class="Bound"
      >x</a
      ><a name="7867"
      > </a
      ><a name="7868" href="StlcProp.html#7436" class="Datatype Operator"
      >FreeIn</a
      ><a name="7874"
      > </a
      ><a name="7875" href="StlcProp.html#7861" class="Bound"
      >N</a
      ><a name="7876"
      > </a
      ><a name="7877" class="Symbol"
      >&#8594;</a
      ><a name="7878"
      > </a
      ><a name="7879" href="StlcProp.html#7855" class="Bound"
      >x</a
      ><a name="7880"
      > </a
      ><a name="7881" href="StlcProp.html#7436" class="Datatype Operator"
      >FreeIn</a
      ><a name="7887"
      > </a
      ><a name="7888" class="Symbol"
      >(</a
      ><a name="7889" href="Stlc.html#1165" class="InductiveConstructor Operator"
      >if&#7488;</a
      ><a name="7892"
      > </a
      ><a name="7893" href="StlcProp.html#7857" class="Bound"
      >L</a
      ><a name="7894"
      > </a
      ><a name="7895" href="Stlc.html#1165" class="InductiveConstructor Operator"
      >then</a
      ><a name="7899"
      > </a
      ><a name="7900" href="StlcProp.html#7859" class="Bound"
      >M</a
      ><a name="7901"
      > </a
      ><a name="7902" href="Stlc.html#1165" class="InductiveConstructor Operator"
      >else</a
      ><a name="7906"
      > </a
      ><a name="7907" href="StlcProp.html#7861" class="Bound"
      >N</a
      ><a name="7908" class="Symbol"
      >)</a
      >

</pre>

A term in which no variables appear free is said to be _closed_.

<pre class="Agda">

<a name="8001" href="StlcProp.html#8001" class="Function"
      >closed</a
      ><a name="8007"
      > </a
      ><a name="8008" class="Symbol"
      >:</a
      ><a name="8009"
      > </a
      ><a name="8010" href="Stlc.html#1032" class="Datatype"
      >Term</a
      ><a name="8014"
      > </a
      ><a name="8015" class="Symbol"
      >&#8594;</a
      ><a name="8016"
      > </a
      ><a name="8017" class="PrimitiveType"
      >Set</a
      ><a name="8020"
      >
</a
      ><a name="8021" href="StlcProp.html#8001" class="Function"
      >closed</a
      ><a name="8027"
      > </a
      ><a name="8028" href="StlcProp.html#8028" class="Bound"
      >M</a
      ><a name="8029"
      > </a
      ><a name="8030" class="Symbol"
      >=</a
      ><a name="8031"
      > </a
      ><a name="8032" class="Symbol"
      >&#8704;</a
      ><a name="8033"
      > </a
      ><a name="8034" class="Symbol"
      >{</a
      ><a name="8035" href="StlcProp.html#8035" class="Bound"
      >x</a
      ><a name="8036" class="Symbol"
      >}</a
      ><a name="8037"
      > </a
      ><a name="8038" class="Symbol"
      >&#8594;</a
      ><a name="8039"
      > </a
      ><a name="8040" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#414" class="Function Operator"
      >&#172;</a
      ><a name="8041"
      > </a
      ><a name="8042" class="Symbol"
      >(</a
      ><a name="8043" href="StlcProp.html#8035" class="Bound"
      >x</a
      ><a name="8044"
      > </a
      ><a name="8045" href="StlcProp.html#7436" class="Datatype Operator"
      >FreeIn</a
      ><a name="8051"
      > </a
      ><a name="8052" href="StlcProp.html#8028" class="Bound"
      >M</a
      ><a name="8053" class="Symbol"
      >)</a
      >

</pre>

#### Exercise: 1 star (free-in)
If the definition of `_FreeIn_` is not crystal clear to
you, it is a good idea to take a piece of paper and write out the
rules in informal inference-rule notation.  (Although it is a
rather low-level, technical definition, understanding it is
crucial to understanding substitution and its properties, which
are really the crux of the lambda-calculus.)

### Substitution
To prove that substitution preserves typing, we first need a
technical lemma connecting free variables and typing contexts: If
a variable $$x$$ appears free in a term $$M$$, and if we know $$M$$ is
well typed in context $$Γ$$, then it must be the case that
$$Γ$$ assigns a type to $$x$$.

<pre class="Agda">

<a name="8772" href="StlcProp.html#8772" class="Function"
      >freeLemma</a
      ><a name="8781"
      > </a
      ><a name="8782" class="Symbol"
      >:</a
      ><a name="8783"
      > </a
      ><a name="8784" class="Symbol"
      >&#8704;</a
      ><a name="8785"
      > </a
      ><a name="8786" class="Symbol"
      >{</a
      ><a name="8787" href="StlcProp.html#8787" class="Bound"
      >x</a
      ><a name="8788"
      > </a
      ><a name="8789" href="StlcProp.html#8789" class="Bound"
      >M</a
      ><a name="8790"
      > </a
      ><a name="8791" href="StlcProp.html#8791" class="Bound"
      >A</a
      ><a name="8792"
      > </a
      ><a name="8793" href="StlcProp.html#8793" class="Bound"
      >&#915;</a
      ><a name="8794" class="Symbol"
      >}</a
      ><a name="8795"
      > </a
      ><a name="8796" class="Symbol"
      >&#8594;</a
      ><a name="8797"
      > </a
      ><a name="8798" href="StlcProp.html#8787" class="Bound"
      >x</a
      ><a name="8799"
      > </a
      ><a name="8800" href="StlcProp.html#7436" class="Datatype Operator"
      >FreeIn</a
      ><a name="8806"
      > </a
      ><a name="8807" href="StlcProp.html#8789" class="Bound"
      >M</a
      ><a name="8808"
      > </a
      ><a name="8809" class="Symbol"
      >&#8594;</a
      ><a name="8810"
      > </a
      ><a name="8811" href="StlcProp.html#8793" class="Bound"
      >&#915;</a
      ><a name="8812"
      > </a
      ><a name="8813" href="Stlc.html#4116" class="Datatype Operator"
      >&#8866;</a
      ><a name="8814"
      > </a
      ><a name="8815" href="StlcProp.html#8789" class="Bound"
      >M</a
      ><a name="8816"
      > </a
      ><a name="8817" href="Stlc.html#4116" class="Datatype Operator"
      >&#8712;</a
      ><a name="8818"
      > </a
      ><a name="8819" href="StlcProp.html#8791" class="Bound"
      >A</a
      ><a name="8820"
      > </a
      ><a name="8821" class="Symbol"
      >&#8594;</a
      ><a name="8822"
      > </a
      ><a name="8823" href="https://agda.github.io/agda-stdlib/Data.Product.html#823" class="Function"
      >&#8707;</a
      ><a name="8824"
      > </a
      ><a name="8825" class="Symbol"
      >&#955;</a
      ><a name="8826"
      > </a
      ><a name="8827" href="StlcProp.html#8827" class="Bound"
      >B</a
      ><a name="8828"
      > </a
      ><a name="8829" class="Symbol"
      >&#8594;</a
      ><a name="8830"
      > </a
      ><a name="8831" href="StlcProp.html#8793" class="Bound"
      >&#915;</a
      ><a name="8832"
      > </a
      ><a name="8833" href="StlcProp.html#8787" class="Bound"
      >x</a
      ><a name="8834"
      > </a
      ><a name="8835" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="8836"
      > </a
      ><a name="8837" href="https://agda.github.io/agda-stdlib/Data.Maybe.Base.html#373" class="InductiveConstructor"
      >just</a
      ><a name="8841"
      > </a
      ><a name="8842" href="StlcProp.html#8827" class="Bound"
      >B</a
      >

</pre>

_Proof_: We show, by induction on the proof that $$x$$ appears
  free in $$P$$, that, for all contexts $$Γ$$, if $$P$$ is well
  typed under $$Γ$$, then $$Γ$$ assigns some type to $$x$$.

  - If the last rule used was `free-varᵀ`, then $$P = x$$, and from
    the assumption that $$M$$ is well typed under $$Γ$$ we have
    immediately that $$Γ$$ assigns a type to $$x$$.

  - If the last rule used was `free-·₁`, then $$P = L ·ᵀ M$$ and $$x$$
    appears free in $$L$$.  Since $$L$$ is well typed under $$\Gamma$$,
    we can see from the typing rules that $$L$$ must also be, and
    the IH then tells us that $$Γ$$ assigns $$x$$ a type.

  - Almost all the other cases are similar: $$x$$ appears free in a
    subterm of $$P$$, and since $$P$$ is well typed under $$Γ$$, we
    know the subterm of $$M$$ in which $$x$$ appears is well typed
    under $$Γ$$ as well, and the IH gives us exactly the
    conclusion we want.

  - The only remaining case is `free-λᵀ`.  In this case $$P =
    λᵀ y ∈ A ⇒ N$$, and $$x$$ appears free in $$N$$; we also know that
    $$x$$ is different from $$y$$.  The difference from the previous
    cases is that whereas $$P$$ is well typed under $$\Gamma$$, its
    body $$N$$ is well typed under $$(Γ , y ↦ A)$$, so the IH
    allows us to conclude that $$x$$ is assigned some type by the
    extended context $$(Γ , y ↦ A)$$.  To conclude that $$Γ$$
    assigns a type to $$x$$, we appeal the decidable equality for names
    `_≟_`, noting that $$x$$ and $$y$$ are different variables.

<pre class="Agda">

<a name="10392" href="StlcProp.html#8772" class="Function"
      >freeLemma</a
      ><a name="10401"
      > </a
      ><a name="10402" href="StlcProp.html#7471" class="InductiveConstructor"
      >free-var&#7488;</a
      ><a name="10411"
      > </a
      ><a name="10412" class="Symbol"
      >(</a
      ><a name="10413" href="Stlc.html#4160" class="InductiveConstructor"
      >Ax</a
      ><a name="10415"
      > </a
      ><a name="10416" href="StlcProp.html#10416" class="Bound"
      >&#915;x&#8801;justA</a
      ><a name="10424" class="Symbol"
      >)</a
      ><a name="10425"
      > </a
      ><a name="10426" class="Symbol"
      >=</a
      ><a name="10427"
      > </a
      ><a name="10428" class="Symbol"
      >(_</a
      ><a name="10430"
      > </a
      ><a name="10431" href="https://agda.github.io/agda-stdlib/Data.Product.html#509" class="InductiveConstructor Operator"
      >,</a
      ><a name="10432"
      > </a
      ><a name="10433" href="StlcProp.html#10416" class="Bound"
      >&#915;x&#8801;justA</a
      ><a name="10441" class="Symbol"
      >)</a
      ><a name="10442"
      >
</a
      ><a name="10443" href="StlcProp.html#8772" class="Function"
      >freeLemma</a
      ><a name="10452"
      > </a
      ><a name="10453" class="Symbol"
      >(</a
      ><a name="10454" href="StlcProp.html#7584" class="InductiveConstructor"
      >free-&#183;&#7488;&#8321;</a
      ><a name="10462"
      > </a
      ><a name="10463" href="StlcProp.html#10463" class="Bound"
      >x&#8712;L</a
      ><a name="10466" class="Symbol"
      >)</a
      ><a name="10467"
      > </a
      ><a name="10468" class="Symbol"
      >(</a
      ><a name="10469" href="Stlc.html#4300" class="InductiveConstructor"
      >&#8658;-E</a
      ><a name="10472"
      > </a
      ><a name="10473" href="StlcProp.html#10473" class="Bound"
      >&#8866;L</a
      ><a name="10475"
      > </a
      ><a name="10476" href="StlcProp.html#10476" class="Bound"
      >&#8866;M</a
      ><a name="10478" class="Symbol"
      >)</a
      ><a name="10479"
      > </a
      ><a name="10480" class="Symbol"
      >=</a
      ><a name="10481"
      > </a
      ><a name="10482" href="StlcProp.html#8772" class="Function"
      >freeLemma</a
      ><a name="10491"
      > </a
      ><a name="10492" href="StlcProp.html#10463" class="Bound"
      >x&#8712;L</a
      ><a name="10495"
      > </a
      ><a name="10496" href="StlcProp.html#10473" class="Bound"
      >&#8866;L</a
      ><a name="10498"
      >
</a
      ><a name="10499" href="StlcProp.html#8772" class="Function"
      >freeLemma</a
      ><a name="10508"
      > </a
      ><a name="10509" class="Symbol"
      >(</a
      ><a name="10510" href="StlcProp.html#7640" class="InductiveConstructor"
      >free-&#183;&#7488;&#8322;</a
      ><a name="10518"
      > </a
      ><a name="10519" href="StlcProp.html#10519" class="Bound"
      >x&#8712;M</a
      ><a name="10522" class="Symbol"
      >)</a
      ><a name="10523"
      > </a
      ><a name="10524" class="Symbol"
      >(</a
      ><a name="10525" href="Stlc.html#4300" class="InductiveConstructor"
      >&#8658;-E</a
      ><a name="10528"
      > </a
      ><a name="10529" href="StlcProp.html#10529" class="Bound"
      >&#8866;L</a
      ><a name="10531"
      > </a
      ><a name="10532" href="StlcProp.html#10532" class="Bound"
      >&#8866;M</a
      ><a name="10534" class="Symbol"
      >)</a
      ><a name="10535"
      > </a
      ><a name="10536" class="Symbol"
      >=</a
      ><a name="10537"
      > </a
      ><a name="10538" href="StlcProp.html#8772" class="Function"
      >freeLemma</a
      ><a name="10547"
      > </a
      ><a name="10548" href="StlcProp.html#10519" class="Bound"
      >x&#8712;M</a
      ><a name="10551"
      > </a
      ><a name="10552" href="StlcProp.html#10532" class="Bound"
      >&#8866;M</a
      ><a name="10554"
      >
</a
      ><a name="10555" href="StlcProp.html#8772" class="Function"
      >freeLemma</a
      ><a name="10564"
      > </a
      ><a name="10565" class="Symbol"
      >(</a
      ><a name="10566" href="StlcProp.html#7696" class="InductiveConstructor"
      >free-if&#7488;&#8321;</a
      ><a name="10575"
      > </a
      ><a name="10576" href="StlcProp.html#10576" class="Bound"
      >x&#8712;L</a
      ><a name="10579" class="Symbol"
      >)</a
      ><a name="10580"
      > </a
      ><a name="10581" class="Symbol"
      >(</a
      ><a name="10582" href="Stlc.html#4452" class="InductiveConstructor"
      >&#120121;-E</a
      ><a name="10585"
      > </a
      ><a name="10586" href="StlcProp.html#10586" class="Bound"
      >&#8866;L</a
      ><a name="10588"
      > </a
      ><a name="10589" href="StlcProp.html#10589" class="Bound"
      >&#8866;M</a
      ><a name="10591"
      > </a
      ><a name="10592" href="StlcProp.html#10592" class="Bound"
      >&#8866;N</a
      ><a name="10594" class="Symbol"
      >)</a
      ><a name="10595"
      > </a
      ><a name="10596" class="Symbol"
      >=</a
      ><a name="10597"
      > </a
      ><a name="10598" href="StlcProp.html#8772" class="Function"
      >freeLemma</a
      ><a name="10607"
      > </a
      ><a name="10608" href="StlcProp.html#10576" class="Bound"
      >x&#8712;L</a
      ><a name="10611"
      > </a
      ><a name="10612" href="StlcProp.html#10586" class="Bound"
      >&#8866;L</a
      ><a name="10614"
      >
</a
      ><a name="10615" href="StlcProp.html#8772" class="Function"
      >freeLemma</a
      ><a name="10624"
      > </a
      ><a name="10625" class="Symbol"
      >(</a
      ><a name="10626" href="StlcProp.html#7768" class="InductiveConstructor"
      >free-if&#7488;&#8322;</a
      ><a name="10635"
      > </a
      ><a name="10636" href="StlcProp.html#10636" class="Bound"
      >x&#8712;M</a
      ><a name="10639" class="Symbol"
      >)</a
      ><a name="10640"
      > </a
      ><a name="10641" class="Symbol"
      >(</a
      ><a name="10642" href="Stlc.html#4452" class="InductiveConstructor"
      >&#120121;-E</a
      ><a name="10645"
      > </a
      ><a name="10646" href="StlcProp.html#10646" class="Bound"
      >&#8866;L</a
      ><a name="10648"
      > </a
      ><a name="10649" href="StlcProp.html#10649" class="Bound"
      >&#8866;M</a
      ><a name="10651"
      > </a
      ><a name="10652" href="StlcProp.html#10652" class="Bound"
      >&#8866;N</a
      ><a name="10654" class="Symbol"
      >)</a
      ><a name="10655"
      > </a
      ><a name="10656" class="Symbol"
      >=</a
      ><a name="10657"
      > </a
      ><a name="10658" href="StlcProp.html#8772" class="Function"
      >freeLemma</a
      ><a name="10667"
      > </a
      ><a name="10668" href="StlcProp.html#10636" class="Bound"
      >x&#8712;M</a
      ><a name="10671"
      > </a
      ><a name="10672" href="StlcProp.html#10649" class="Bound"
      >&#8866;M</a
      ><a name="10674"
      >
</a
      ><a name="10675" href="StlcProp.html#8772" class="Function"
      >freeLemma</a
      ><a name="10684"
      > </a
      ><a name="10685" class="Symbol"
      >(</a
      ><a name="10686" href="StlcProp.html#7840" class="InductiveConstructor"
      >free-if&#7488;&#8323;</a
      ><a name="10695"
      > </a
      ><a name="10696" href="StlcProp.html#10696" class="Bound"
      >x&#8712;N</a
      ><a name="10699" class="Symbol"
      >)</a
      ><a name="10700"
      > </a
      ><a name="10701" class="Symbol"
      >(</a
      ><a name="10702" href="Stlc.html#4452" class="InductiveConstructor"
      >&#120121;-E</a
      ><a name="10705"
      > </a
      ><a name="10706" href="StlcProp.html#10706" class="Bound"
      >&#8866;L</a
      ><a name="10708"
      > </a
      ><a name="10709" href="StlcProp.html#10709" class="Bound"
      >&#8866;M</a
      ><a name="10711"
      > </a
      ><a name="10712" href="StlcProp.html#10712" class="Bound"
      >&#8866;N</a
      ><a name="10714" class="Symbol"
      >)</a
      ><a name="10715"
      > </a
      ><a name="10716" class="Symbol"
      >=</a
      ><a name="10717"
      > </a
      ><a name="10718" href="StlcProp.html#8772" class="Function"
      >freeLemma</a
      ><a name="10727"
      > </a
      ><a name="10728" href="StlcProp.html#10696" class="Bound"
      >x&#8712;N</a
      ><a name="10731"
      > </a
      ><a name="10732" href="StlcProp.html#10712" class="Bound"
      >&#8866;N</a
      ><a name="10734"
      >
</a
      ><a name="10735" href="StlcProp.html#8772" class="Function"
      >freeLemma</a
      ><a name="10744"
      > </a
      ><a name="10745" class="Symbol"
      >(</a
      ><a name="10746" href="StlcProp.html#7512" class="InductiveConstructor"
      >free-&#955;&#7488;</a
      ><a name="10753"
      > </a
      ><a name="10754" class="Symbol"
      >{</a
      ><a name="10755" href="StlcProp.html#10755" class="Bound"
      >x</a
      ><a name="10756" class="Symbol"
      >}</a
      ><a name="10757"
      > </a
      ><a name="10758" class="Symbol"
      >{</a
      ><a name="10759" href="StlcProp.html#10759" class="Bound"
      >y</a
      ><a name="10760" class="Symbol"
      >}</a
      ><a name="10761"
      > </a
      ><a name="10762" href="StlcProp.html#10762" class="Bound"
      >y&#8802;x</a
      ><a name="10765"
      > </a
      ><a name="10766" href="StlcProp.html#10766" class="Bound"
      >x&#8712;N</a
      ><a name="10769" class="Symbol"
      >)</a
      ><a name="10770"
      > </a
      ><a name="10771" class="Symbol"
      >(</a
      ><a name="10772" href="Stlc.html#4217" class="InductiveConstructor"
      >&#8658;-I</a
      ><a name="10775"
      > </a
      ><a name="10776" href="StlcProp.html#10776" class="Bound"
      >&#8866;N</a
      ><a name="10778" class="Symbol"
      >)</a
      ><a name="10779"
      > </a
      ><a name="10780" class="Keyword"
      >with</a
      ><a name="10784"
      > </a
      ><a name="10785" href="StlcProp.html#8772" class="Function"
      >freeLemma</a
      ><a name="10794"
      > </a
      ><a name="10795" href="StlcProp.html#10766" class="Bound"
      >x&#8712;N</a
      ><a name="10798"
      > </a
      ><a name="10799" href="StlcProp.html#10776" class="Bound"
      >&#8866;N</a
      ><a name="10801"
      >
</a
      ><a name="10802" class="Symbol"
      >...</a
      ><a name="10805"
      > </a
      ><a name="10806" class="Symbol"
      >|</a
      ><a name="10807"
      > </a
      ><a name="10808" href="StlcProp.html#10808" class="Bound"
      >&#915;x=justC</a
      ><a name="10816"
      > </a
      ><a name="10817" class="Keyword"
      >with</a
      ><a name="10821"
      > </a
      ><a name="10822" href="StlcProp.html#10759" class="Bound"
      >y</a
      ><a name="10823"
      > </a
      ><a name="10824" href="Maps.html#2558" class="Function Operator"
      >&#8799;</a
      ><a name="10825"
      > </a
      ><a name="10826" href="StlcProp.html#10755" class="Bound"
      >x</a
      ><a name="10827"
      >
</a
      ><a name="10828" class="Symbol"
      >...</a
      ><a name="10831"
      > </a
      ><a name="10832" class="Symbol"
      >|</a
      ><a name="10833"
      > </a
      ><a name="10834" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#520" class="InductiveConstructor"
      >yes</a
      ><a name="10837"
      > </a
      ><a name="10838" href="StlcProp.html#10838" class="Bound"
      >y&#8801;x</a
      ><a name="10841"
      > </a
      ><a name="10842" class="Symbol"
      >=</a
      ><a name="10843"
      > </a
      ><a name="10844" href="https://agda.github.io/agda-stdlib/Data.Empty.html#360" class="Function"
      >&#8869;-elim</a
      ><a name="10850"
      > </a
      ><a name="10851" class="Symbol"
      >(</a
      ><a name="10852" href="StlcProp.html#10762" class="Bound"
      >y&#8802;x</a
      ><a name="10855"
      > </a
      ><a name="10856" href="StlcProp.html#10838" class="Bound"
      >y&#8801;x</a
      ><a name="10859" class="Symbol"
      >)</a
      ><a name="10860"
      >
</a
      ><a name="10861" class="Symbol"
      >...</a
      ><a name="10864"
      > </a
      ><a name="10865" class="Symbol"
      >|</a
      ><a name="10866"
      > </a
      ><a name="10867" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#547" class="InductiveConstructor"
      >no</a
      ><a name="10869"
      >  </a
      ><a name="10871" class="Symbol"
      >_</a
      ><a name="10872"
      >   </a
      ><a name="10875" class="Symbol"
      >=</a
      ><a name="10876"
      > </a
      ><a name="10877" href="StlcProp.html#10808" class="Bound"
      >&#915;x=justC</a
      >

</pre>

[A subtle point: if the first argument of $$free-λᵀ$$ was of type
$$x ≢ y$$ rather than of type $$y ≢ x$$, then the type of the
term $$Γx=justC$$ would not simplify properly.]

Next, we'll need the fact that any term $$M$$ which is well typed in
the empty context is closed (it has no free variables).

#### Exercise: 2 stars, optional (∅⊢-closed)

<pre class="Agda">

<a name="11260" class="Keyword"
      >postulate</a
      ><a name="11269"
      >
  </a
      ><a name="11272" href="StlcProp.html#11272" class="Postulate"
      >&#8709;&#8866;-closed</a
      ><a name="11281"
      > </a
      ><a name="11282" class="Symbol"
      >:</a
      ><a name="11283"
      > </a
      ><a name="11284" class="Symbol"
      >&#8704;</a
      ><a name="11285"
      > </a
      ><a name="11286" class="Symbol"
      >{</a
      ><a name="11287" href="StlcProp.html#11287" class="Bound"
      >M</a
      ><a name="11288"
      > </a
      ><a name="11289" href="StlcProp.html#11289" class="Bound"
      >A</a
      ><a name="11290" class="Symbol"
      >}</a
      ><a name="11291"
      > </a
      ><a name="11292" class="Symbol"
      >&#8594;</a
      ><a name="11293"
      > </a
      ><a name="11294" href="Maps.html#11235" class="Function"
      >&#8709;</a
      ><a name="11295"
      > </a
      ><a name="11296" href="Stlc.html#4116" class="Datatype Operator"
      >&#8866;</a
      ><a name="11297"
      > </a
      ><a name="11298" href="StlcProp.html#11287" class="Bound"
      >M</a
      ><a name="11299"
      > </a
      ><a name="11300" href="Stlc.html#4116" class="Datatype Operator"
      >&#8712;</a
      ><a name="11301"
      > </a
      ><a name="11302" href="StlcProp.html#11289" class="Bound"
      >A</a
      ><a name="11303"
      > </a
      ><a name="11304" class="Symbol"
      >&#8594;</a
      ><a name="11305"
      > </a
      ><a name="11306" href="StlcProp.html#8001" class="Function"
      >closed</a
      ><a name="11312"
      > </a
      ><a name="11313" href="StlcProp.html#11287" class="Bound"
      >M</a
      >

</pre>

<div class="hidden">
<pre class="Agda">

<a name="11361" href="StlcProp.html#11361" class="Function"
      >contradiction</a
      ><a name="11374"
      > </a
      ><a name="11375" class="Symbol"
      >:</a
      ><a name="11376"
      > </a
      ><a name="11377" class="Symbol"
      >&#8704;</a
      ><a name="11378"
      > </a
      ><a name="11379" class="Symbol"
      >{</a
      ><a name="11380" href="StlcProp.html#11380" class="Bound"
      >X</a
      ><a name="11381"
      > </a
      ><a name="11382" class="Symbol"
      >:</a
      ><a name="11383"
      > </a
      ><a name="11384" class="PrimitiveType"
      >Set</a
      ><a name="11387" class="Symbol"
      >}</a
      ><a name="11388"
      > </a
      ><a name="11389" class="Symbol"
      >&#8594;</a
      ><a name="11390"
      > </a
      ><a name="11391" class="Symbol"
      >&#8704;</a
      ><a name="11392"
      > </a
      ><a name="11393" class="Symbol"
      >{</a
      ><a name="11394" href="StlcProp.html#11394" class="Bound"
      >x</a
      ><a name="11395"
      > </a
      ><a name="11396" class="Symbol"
      >:</a
      ><a name="11397"
      > </a
      ><a name="11398" href="StlcProp.html#11380" class="Bound"
      >X</a
      ><a name="11399" class="Symbol"
      >}</a
      ><a name="11400"
      > </a
      ><a name="11401" class="Symbol"
      >&#8594;</a
      ><a name="11402"
      > </a
      ><a name="11403" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#414" class="Function Operator"
      >&#172;</a
      ><a name="11404"
      > </a
      ><a name="11405" class="Symbol"
      >(</a
      ><a name="11406" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >_&#8801;_</a
      ><a name="11409"
      > </a
      ><a name="11410" class="Symbol"
      >{</a
      ><a name="11411" class="Argument"
      >A</a
      ><a name="11412"
      > </a
      ><a name="11413" class="Symbol"
      >=</a
      ><a name="11414"
      > </a
      ><a name="11415" href="https://agda.github.io/agda-stdlib/Data.Maybe.Base.html#335" class="Datatype"
      >Maybe</a
      ><a name="11420"
      > </a
      ><a name="11421" href="StlcProp.html#11380" class="Bound"
      >X</a
      ><a name="11422" class="Symbol"
      >}</a
      ><a name="11423"
      > </a
      ><a name="11424" class="Symbol"
      >(</a
      ><a name="11425" href="https://agda.github.io/agda-stdlib/Data.Maybe.Base.html#373" class="InductiveConstructor"
      >just</a
      ><a name="11429"
      > </a
      ><a name="11430" href="StlcProp.html#11394" class="Bound"
      >x</a
      ><a name="11431" class="Symbol"
      >)</a
      ><a name="11432"
      > </a
      ><a name="11433" href="https://agda.github.io/agda-stdlib/Data.Maybe.Base.html#403" class="InductiveConstructor"
      >nothing</a
      ><a name="11440" class="Symbol"
      >)</a
      ><a name="11441"
      >
</a
      ><a name="11442" href="StlcProp.html#11361" class="Function"
      >contradiction</a
      ><a name="11455"
      > </a
      ><a name="11456" class="Symbol"
      >()</a
      ><a name="11458"
      >

</a
      ><a name="11460" href="StlcProp.html#11460" class="Function"
      >&#8709;&#8866;-closed&#8242;</a
      ><a name="11470"
      > </a
      ><a name="11471" class="Symbol"
      >:</a
      ><a name="11472"
      > </a
      ><a name="11473" class="Symbol"
      >&#8704;</a
      ><a name="11474"
      > </a
      ><a name="11475" class="Symbol"
      >{</a
      ><a name="11476" href="StlcProp.html#11476" class="Bound"
      >M</a
      ><a name="11477"
      > </a
      ><a name="11478" href="StlcProp.html#11478" class="Bound"
      >A</a
      ><a name="11479" class="Symbol"
      >}</a
      ><a name="11480"
      > </a
      ><a name="11481" class="Symbol"
      >&#8594;</a
      ><a name="11482"
      > </a
      ><a name="11483" href="Maps.html#11235" class="Function"
      >&#8709;</a
      ><a name="11484"
      > </a
      ><a name="11485" href="Stlc.html#4116" class="Datatype Operator"
      >&#8866;</a
      ><a name="11486"
      > </a
      ><a name="11487" href="StlcProp.html#11476" class="Bound"
      >M</a
      ><a name="11488"
      > </a
      ><a name="11489" href="Stlc.html#4116" class="Datatype Operator"
      >&#8712;</a
      ><a name="11490"
      > </a
      ><a name="11491" href="StlcProp.html#11478" class="Bound"
      >A</a
      ><a name="11492"
      > </a
      ><a name="11493" class="Symbol"
      >&#8594;</a
      ><a name="11494"
      > </a
      ><a name="11495" href="StlcProp.html#8001" class="Function"
      >closed</a
      ><a name="11501"
      > </a
      ><a name="11502" href="StlcProp.html#11476" class="Bound"
      >M</a
      ><a name="11503"
      >
</a
      ><a name="11504" href="StlcProp.html#11460" class="Function"
      >&#8709;&#8866;-closed&#8242;</a
      ><a name="11514"
      > </a
      ><a name="11515" class="Symbol"
      >{</a
      ><a name="11516" href="StlcProp.html#11516" class="Bound"
      >M</a
      ><a name="11517" class="Symbol"
      >}</a
      ><a name="11518"
      > </a
      ><a name="11519" class="Symbol"
      >{</a
      ><a name="11520" href="StlcProp.html#11520" class="Bound"
      >A</a
      ><a name="11521" class="Symbol"
      >}</a
      ><a name="11522"
      > </a
      ><a name="11523" href="StlcProp.html#11523" class="Bound"
      >&#8866;M</a
      ><a name="11525"
      > </a
      ><a name="11526" class="Symbol"
      >{</a
      ><a name="11527" href="StlcProp.html#11527" class="Bound"
      >x</a
      ><a name="11528" class="Symbol"
      >}</a
      ><a name="11529"
      > </a
      ><a name="11530" href="StlcProp.html#11530" class="Bound"
      >x&#8712;M</a
      ><a name="11533"
      > </a
      ><a name="11534" class="Keyword"
      >with</a
      ><a name="11538"
      > </a
      ><a name="11539" href="StlcProp.html#8772" class="Function"
      >freeLemma</a
      ><a name="11548"
      > </a
      ><a name="11549" href="StlcProp.html#11530" class="Bound"
      >x&#8712;M</a
      ><a name="11552"
      > </a
      ><a name="11553" href="StlcProp.html#11523" class="Bound"
      >&#8866;M</a
      ><a name="11555"
      >
</a
      ><a name="11556" class="Symbol"
      >...</a
      ><a name="11559"
      > </a
      ><a name="11560" class="Symbol"
      >|</a
      ><a name="11561"
      > </a
      ><a name="11562" class="Symbol"
      >(</a
      ><a name="11563" href="StlcProp.html#11563" class="Bound"
      >B</a
      ><a name="11564"
      > </a
      ><a name="11565" href="https://agda.github.io/agda-stdlib/Data.Product.html#509" class="InductiveConstructor Operator"
      >,</a
      ><a name="11566"
      > </a
      ><a name="11567" href="StlcProp.html#11567" class="Bound"
      >&#8709;x&#8801;justB</a
      ><a name="11575" class="Symbol"
      >)</a
      ><a name="11576"
      > </a
      ><a name="11577" class="Symbol"
      >=</a
      ><a name="11578"
      > </a
      ><a name="11579" href="StlcProp.html#11361" class="Function"
      >contradiction</a
      ><a name="11592"
      > </a
      ><a name="11593" class="Symbol"
      >(</a
      ><a name="11594" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.Core.html#632" class="Function"
      >trans</a
      ><a name="11599"
      > </a
      ><a name="11600" class="Symbol"
      >(</a
      ><a name="11601" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.Core.html#565" class="Function"
      >sym</a
      ><a name="11604"
      > </a
      ><a name="11605" href="StlcProp.html#11567" class="Bound"
      >&#8709;x&#8801;justB</a
      ><a name="11613" class="Symbol"
      >)</a
      ><a name="11614"
      > </a
      ><a name="11615" class="Symbol"
      >(</a
      ><a name="11616" href="Maps.html#12094" class="Function"
      >apply-&#8709;</a
      ><a name="11623"
      > </a
      ><a name="11624" href="StlcProp.html#11527" class="Bound"
      >x</a
      ><a name="11625" class="Symbol"
      >))</a
      >

</pre>
</div>

Sometimes, when we have a proof $$Γ ⊢ M ∈ A$$, we will need to
replace $$Γ$$ by a different context $$Γ′$$.  When is it safe
to do this?  Intuitively, it must at least be the case that
$$Γ′$$ assigns the same types as $$Γ$$ to all the variables
that appear free in $$M$$. In fact, this is the only condition that
is needed.

<pre class="Agda">

<a name="11985" href="StlcProp.html#11985" class="Function"
      >weaken</a
      ><a name="11991"
      > </a
      ><a name="11992" class="Symbol"
      >:</a
      ><a name="11993"
      > </a
      ><a name="11994" class="Symbol"
      >&#8704;</a
      ><a name="11995"
      > </a
      ><a name="11996" class="Symbol"
      >{</a
      ><a name="11997" href="StlcProp.html#11997" class="Bound"
      >&#915;</a
      ><a name="11998"
      > </a
      ><a name="11999" href="StlcProp.html#11999" class="Bound"
      >&#915;&#8242;</a
      ><a name="12001"
      > </a
      ><a name="12002" href="StlcProp.html#12002" class="Bound"
      >M</a
      ><a name="12003"
      > </a
      ><a name="12004" href="StlcProp.html#12004" class="Bound"
      >A</a
      ><a name="12005" class="Symbol"
      >}</a
      ><a name="12006"
      >
        </a
      ><a name="12015" class="Symbol"
      >&#8594;</a
      ><a name="12016"
      > </a
      ><a name="12017" class="Symbol"
      >(&#8704;</a
      ><a name="12019"
      > </a
      ><a name="12020" class="Symbol"
      >{</a
      ><a name="12021" href="StlcProp.html#12021" class="Bound"
      >x</a
      ><a name="12022" class="Symbol"
      >}</a
      ><a name="12023"
      > </a
      ><a name="12024" class="Symbol"
      >&#8594;</a
      ><a name="12025"
      > </a
      ><a name="12026" href="StlcProp.html#12021" class="Bound"
      >x</a
      ><a name="12027"
      > </a
      ><a name="12028" href="StlcProp.html#7436" class="Datatype Operator"
      >FreeIn</a
      ><a name="12034"
      > </a
      ><a name="12035" href="StlcProp.html#12002" class="Bound"
      >M</a
      ><a name="12036"
      > </a
      ><a name="12037" class="Symbol"
      >&#8594;</a
      ><a name="12038"
      > </a
      ><a name="12039" href="StlcProp.html#11997" class="Bound"
      >&#915;</a
      ><a name="12040"
      > </a
      ><a name="12041" href="StlcProp.html#12021" class="Bound"
      >x</a
      ><a name="12042"
      > </a
      ><a name="12043" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="12044"
      > </a
      ><a name="12045" href="StlcProp.html#11999" class="Bound"
      >&#915;&#8242;</a
      ><a name="12047"
      > </a
      ><a name="12048" href="StlcProp.html#12021" class="Bound"
      >x</a
      ><a name="12049" class="Symbol"
      >)</a
      ><a name="12050"
      >
        </a
      ><a name="12059" class="Symbol"
      >&#8594;</a
      ><a name="12060"
      > </a
      ><a name="12061" href="StlcProp.html#11997" class="Bound"
      >&#915;</a
      ><a name="12062"
      >  </a
      ><a name="12064" href="Stlc.html#4116" class="Datatype Operator"
      >&#8866;</a
      ><a name="12065"
      > </a
      ><a name="12066" href="StlcProp.html#12002" class="Bound"
      >M</a
      ><a name="12067"
      > </a
      ><a name="12068" href="Stlc.html#4116" class="Datatype Operator"
      >&#8712;</a
      ><a name="12069"
      > </a
      ><a name="12070" href="StlcProp.html#12004" class="Bound"
      >A</a
      ><a name="12071"
      >
        </a
      ><a name="12080" class="Symbol"
      >&#8594;</a
      ><a name="12081"
      > </a
      ><a name="12082" href="StlcProp.html#11999" class="Bound"
      >&#915;&#8242;</a
      ><a name="12084"
      > </a
      ><a name="12085" href="Stlc.html#4116" class="Datatype Operator"
      >&#8866;</a
      ><a name="12086"
      > </a
      ><a name="12087" href="StlcProp.html#12002" class="Bound"
      >M</a
      ><a name="12088"
      > </a
      ><a name="12089" href="Stlc.html#4116" class="Datatype Operator"
      >&#8712;</a
      ><a name="12090"
      > </a
      ><a name="12091" href="StlcProp.html#12004" class="Bound"
      >A</a
      >

</pre>

_Proof_: By induction on the derivation of
$$Γ ⊢ M ∈ A$$.

  - If the last rule in the derivation was `var`, then $$t = x$$
    and $$\Gamma x = T$$.  By assumption, $$\Gamma' x = T$$ as well, and
    hence $$\Gamma' \vdash t : T$$ by `var`.

  - If the last rule was `abs`, then $$t = \lambda y:A. t'$$, with
    $$T = A\to B$$ and $$\Gamma, y : A \vdash t' : B$$.  The
    induction hypothesis is that, for any context $$\Gamma''$$, if
    $$\Gamma, y:A$$ and $$\Gamma''$$ assign the same types to all the
    free variables in $$t'$$, then $$t'$$ has type $$B$$ under
    $$\Gamma''$$.  Let $$\Gamma'$$ be a context which agrees with
    $$\Gamma$$ on the free variables in $$t$$; we must show
    $$\Gamma' \vdash \lambda y:A. t' : A\to B$$.

    By $$abs$$, it suffices to show that $$\Gamma', y:A \vdash t' : t'$$.
    By the IH (setting $$\Gamma'' = \Gamma', y:A$$), it suffices to show
    that $$\Gamma, y:A$$ and $$\Gamma', y:A$$ agree on all the variables
    that appear free in $$t'$$.

    Any variable occurring free in $$t'$$ must be either $$y$$ or
    some other variable.  $$\Gamma, y:A$$ and $$\Gamma', y:A$$
    clearly agree on $$y$$.  Otherwise, note that any variable other
    than $$y$$ that occurs free in $$t'$$ also occurs free in
    $$t = \lambda y:A. t'$$, and by assumption $$\Gamma$$ and
    $$\Gamma'$$ agree on all such variables; hence so do $$\Gamma, y:A$$ and
    $$\Gamma', y:A$$.

  - If the last rule was `app`, then $$t = t_1\;t_2$$, with
    $$\Gamma \vdash t_1:A\to T$$ and $$\Gamma \vdash t_2:A$$.
    One induction hypothesis states that for all contexts $$\Gamma'$$,
    if $$\Gamma'$$ agrees with $$\Gamma$$ on the free variables in $$t_1$$,
    then $$t_1$$ has type $$A\to T$$ under $$\Gamma'$$; there is a similar IH
    for $$t_2$$.  We must show that $$t_1\;t_2$$ also has type $$T$$ under
    $$\Gamma'$$, given the assumption that $$\Gamma'$$ agrees with
    $$\Gamma$$ on all the free variables in $$t_1\;t_2$$.  By `app`, it
    suffices to show that $$t_1$$ and $$t_2$$ each have the same type
    under $$\Gamma'$$ as under $$\Gamma$$.  But all free variables in
    $$t_1$$ are also free in $$t_1\;t_2$$, and similarly for $$t_2$$;
    hence the desired result follows from the induction hypotheses.

<pre class="Agda">

<a name="14380" href="StlcProp.html#11985" class="Function"
      >weaken</a
      ><a name="14386"
      > </a
      ><a name="14387" href="StlcProp.html#14387" class="Bound"
      >&#915;~&#915;&#8242;</a
      ><a name="14391"
      > </a
      ><a name="14392" class="Symbol"
      >(</a
      ><a name="14393" href="Stlc.html#4160" class="InductiveConstructor"
      >Ax</a
      ><a name="14395"
      > </a
      ><a name="14396" href="StlcProp.html#14396" class="Bound"
      >&#915;x&#8801;justA</a
      ><a name="14404" class="Symbol"
      >)</a
      ><a name="14405"
      > </a
      ><a name="14406" class="Keyword"
      >rewrite</a
      ><a name="14413"
      > </a
      ><a name="14414" class="Symbol"
      >(</a
      ><a name="14415" href="StlcProp.html#14387" class="Bound"
      >&#915;~&#915;&#8242;</a
      ><a name="14419"
      > </a
      ><a name="14420" href="StlcProp.html#7471" class="InductiveConstructor"
      >free-var&#7488;</a
      ><a name="14429" class="Symbol"
      >)</a
      ><a name="14430"
      > </a
      ><a name="14431" class="Symbol"
      >=</a
      ><a name="14432"
      > </a
      ><a name="14433" href="Stlc.html#4160" class="InductiveConstructor"
      >Ax</a
      ><a name="14435"
      > </a
      ><a name="14436" href="StlcProp.html#14396" class="Bound"
      >&#915;x&#8801;justA</a
      ><a name="14444"
      >
</a
      ><a name="14445" href="StlcProp.html#11985" class="Function"
      >weaken</a
      ><a name="14451"
      > </a
      ><a name="14452" class="Symbol"
      >{</a
      ><a name="14453" href="StlcProp.html#14453" class="Bound"
      >&#915;</a
      ><a name="14454" class="Symbol"
      >}</a
      ><a name="14455"
      > </a
      ><a name="14456" class="Symbol"
      >{</a
      ><a name="14457" href="StlcProp.html#14457" class="Bound"
      >&#915;&#8242;</a
      ><a name="14459" class="Symbol"
      >}</a
      ><a name="14460"
      > </a
      ><a name="14461" class="Symbol"
      >{</a
      ><a name="14462" href="Stlc.html#1070" class="InductiveConstructor Operator"
      >&#955;&#7488;</a
      ><a name="14464"
      > </a
      ><a name="14465" href="StlcProp.html#14465" class="Bound"
      >x</a
      ><a name="14466"
      > </a
      ><a name="14467" href="Stlc.html#1070" class="InductiveConstructor Operator"
      >&#8712;</a
      ><a name="14468"
      > </a
      ><a name="14469" href="StlcProp.html#14469" class="Bound"
      >A</a
      ><a name="14470"
      > </a
      ><a name="14471" href="Stlc.html#1070" class="InductiveConstructor Operator"
      >&#8658;</a
      ><a name="14472"
      > </a
      ><a name="14473" href="StlcProp.html#14473" class="Bound"
      >N</a
      ><a name="14474" class="Symbol"
      >}</a
      ><a name="14475"
      > </a
      ><a name="14476" href="StlcProp.html#14476" class="Bound"
      >&#915;~&#915;&#8242;</a
      ><a name="14480"
      > </a
      ><a name="14481" class="Symbol"
      >(</a
      ><a name="14482" href="Stlc.html#4217" class="InductiveConstructor"
      >&#8658;-I</a
      ><a name="14485"
      > </a
      ><a name="14486" href="StlcProp.html#14486" class="Bound"
      >&#8866;N</a
      ><a name="14488" class="Symbol"
      >)</a
      ><a name="14489"
      > </a
      ><a name="14490" class="Symbol"
      >=</a
      ><a name="14491"
      > </a
      ><a name="14492" href="Stlc.html#4217" class="InductiveConstructor"
      >&#8658;-I</a
      ><a name="14495"
      > </a
      ><a name="14496" class="Symbol"
      >(</a
      ><a name="14497" href="StlcProp.html#11985" class="Function"
      >weaken</a
      ><a name="14503"
      > </a
      ><a name="14504" href="StlcProp.html#14525" class="Function"
      >&#915;x~&#915;&#8242;x</a
      ><a name="14510"
      > </a
      ><a name="14511" href="StlcProp.html#14486" class="Bound"
      >&#8866;N</a
      ><a name="14513" class="Symbol"
      >)</a
      ><a name="14514"
      >
  </a
      ><a name="14517" class="Keyword"
      >where</a
      ><a name="14522"
      >
  </a
      ><a name="14525" href="StlcProp.html#14525" class="Function"
      >&#915;x~&#915;&#8242;x</a
      ><a name="14531"
      > </a
      ><a name="14532" class="Symbol"
      >:</a
      ><a name="14533"
      > </a
      ><a name="14534" class="Symbol"
      >&#8704;</a
      ><a name="14535"
      > </a
      ><a name="14536" class="Symbol"
      >{</a
      ><a name="14537" href="StlcProp.html#14537" class="Bound"
      >y</a
      ><a name="14538" class="Symbol"
      >}</a
      ><a name="14539"
      > </a
      ><a name="14540" class="Symbol"
      >&#8594;</a
      ><a name="14541"
      > </a
      ><a name="14542" href="StlcProp.html#14537" class="Bound"
      >y</a
      ><a name="14543"
      > </a
      ><a name="14544" href="StlcProp.html#7436" class="Datatype Operator"
      >FreeIn</a
      ><a name="14550"
      > </a
      ><a name="14551" href="StlcProp.html#14473" class="Bound"
      >N</a
      ><a name="14552"
      > </a
      ><a name="14553" class="Symbol"
      >&#8594;</a
      ><a name="14554"
      > </a
      ><a name="14555" class="Symbol"
      >(</a
      ><a name="14556" href="StlcProp.html#14453" class="Bound"
      >&#915;</a
      ><a name="14557"
      > </a
      ><a name="14558" href="Maps.html#11317" class="Function Operator"
      >,</a
      ><a name="14559"
      > </a
      ><a name="14560" href="StlcProp.html#14465" class="Bound"
      >x</a
      ><a name="14561"
      > </a
      ><a name="14562" href="Maps.html#11317" class="Function Operator"
      >&#8614;</a
      ><a name="14563"
      > </a
      ><a name="14564" href="StlcProp.html#14469" class="Bound"
      >A</a
      ><a name="14565" class="Symbol"
      >)</a
      ><a name="14566"
      > </a
      ><a name="14567" href="StlcProp.html#14537" class="Bound"
      >y</a
      ><a name="14568"
      > </a
      ><a name="14569" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="14570"
      > </a
      ><a name="14571" class="Symbol"
      >(</a
      ><a name="14572" href="StlcProp.html#14457" class="Bound"
      >&#915;&#8242;</a
      ><a name="14574"
      > </a
      ><a name="14575" href="Maps.html#11317" class="Function Operator"
      >,</a
      ><a name="14576"
      > </a
      ><a name="14577" href="StlcProp.html#14465" class="Bound"
      >x</a
      ><a name="14578"
      > </a
      ><a name="14579" href="Maps.html#11317" class="Function Operator"
      >&#8614;</a
      ><a name="14580"
      > </a
      ><a name="14581" href="StlcProp.html#14469" class="Bound"
      >A</a
      ><a name="14582" class="Symbol"
      >)</a
      ><a name="14583"
      > </a
      ><a name="14584" href="StlcProp.html#14537" class="Bound"
      >y</a
      ><a name="14585"
      >
  </a
      ><a name="14588" href="StlcProp.html#14525" class="Function"
      >&#915;x~&#915;&#8242;x</a
      ><a name="14594"
      > </a
      ><a name="14595" class="Symbol"
      >{</a
      ><a name="14596" href="StlcProp.html#14596" class="Bound"
      >y</a
      ><a name="14597" class="Symbol"
      >}</a
      ><a name="14598"
      > </a
      ><a name="14599" href="StlcProp.html#14599" class="Bound"
      >y&#8712;N</a
      ><a name="14602"
      > </a
      ><a name="14603" class="Keyword"
      >with</a
      ><a name="14607"
      > </a
      ><a name="14608" href="StlcProp.html#14465" class="Bound"
      >x</a
      ><a name="14609"
      > </a
      ><a name="14610" href="Maps.html#2558" class="Function Operator"
      >&#8799;</a
      ><a name="14611"
      > </a
      ><a name="14612" href="StlcProp.html#14596" class="Bound"
      >y</a
      ><a name="14613"
      >
  </a
      ><a name="14616" class="Symbol"
      >...</a
      ><a name="14619"
      > </a
      ><a name="14620" class="Symbol"
      >|</a
      ><a name="14621"
      > </a
      ><a name="14622" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#520" class="InductiveConstructor"
      >yes</a
      ><a name="14625"
      > </a
      ><a name="14626" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="14630"
      > </a
      ><a name="14631" class="Symbol"
      >=</a
      ><a name="14632"
      > </a
      ><a name="14633" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="14637"
      >
  </a
      ><a name="14640" class="Symbol"
      >...</a
      ><a name="14643"
      > </a
      ><a name="14644" class="Symbol"
      >|</a
      ><a name="14645"
      > </a
      ><a name="14646" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#547" class="InductiveConstructor"
      >no</a
      ><a name="14648"
      >  </a
      ><a name="14650" href="StlcProp.html#14650" class="Bound"
      >x&#8802;y</a
      ><a name="14653"
      >  </a
      ><a name="14655" class="Symbol"
      >=</a
      ><a name="14656"
      > </a
      ><a name="14657" href="StlcProp.html#14476" class="Bound"
      >&#915;~&#915;&#8242;</a
      ><a name="14661"
      > </a
      ><a name="14662" class="Symbol"
      >(</a
      ><a name="14663" href="StlcProp.html#7512" class="InductiveConstructor"
      >free-&#955;&#7488;</a
      ><a name="14670"
      > </a
      ><a name="14671" href="StlcProp.html#14650" class="Bound"
      >x&#8802;y</a
      ><a name="14674"
      > </a
      ><a name="14675" href="StlcProp.html#14599" class="Bound"
      >y&#8712;N</a
      ><a name="14678" class="Symbol"
      >)</a
      ><a name="14679"
      >
</a
      ><a name="14680" href="StlcProp.html#11985" class="Function"
      >weaken</a
      ><a name="14686"
      > </a
      ><a name="14687" href="StlcProp.html#14687" class="Bound"
      >&#915;~&#915;&#8242;</a
      ><a name="14691"
      > </a
      ><a name="14692" class="Symbol"
      >(</a
      ><a name="14693" href="Stlc.html#4300" class="InductiveConstructor"
      >&#8658;-E</a
      ><a name="14696"
      > </a
      ><a name="14697" href="StlcProp.html#14697" class="Bound"
      >&#8866;L</a
      ><a name="14699"
      > </a
      ><a name="14700" href="StlcProp.html#14700" class="Bound"
      >&#8866;M</a
      ><a name="14702" class="Symbol"
      >)</a
      ><a name="14703"
      > </a
      ><a name="14704" class="Symbol"
      >=</a
      ><a name="14705"
      > </a
      ><a name="14706" href="Stlc.html#4300" class="InductiveConstructor"
      >&#8658;-E</a
      ><a name="14709"
      > </a
      ><a name="14710" class="Symbol"
      >(</a
      ><a name="14711" href="StlcProp.html#11985" class="Function"
      >weaken</a
      ><a name="14717"
      > </a
      ><a name="14718" class="Symbol"
      >(</a
      ><a name="14719" href="StlcProp.html#14687" class="Bound"
      >&#915;~&#915;&#8242;</a
      ><a name="14723"
      > </a
      ><a name="14724" href="https://agda.github.io/agda-stdlib/Function.html#713" class="Function Operator"
      >&#8728;</a
      ><a name="14725"
      > </a
      ><a name="14726" href="StlcProp.html#7584" class="InductiveConstructor"
      >free-&#183;&#7488;&#8321;</a
      ><a name="14734" class="Symbol"
      >)</a
      ><a name="14735"
      >  </a
      ><a name="14737" href="StlcProp.html#14697" class="Bound"
      >&#8866;L</a
      ><a name="14739" class="Symbol"
      >)</a
      ><a name="14740"
      > </a
      ><a name="14741" class="Symbol"
      >(</a
      ><a name="14742" href="StlcProp.html#11985" class="Function"
      >weaken</a
      ><a name="14748"
      > </a
      ><a name="14749" class="Symbol"
      >(</a
      ><a name="14750" href="StlcProp.html#14687" class="Bound"
      >&#915;~&#915;&#8242;</a
      ><a name="14754"
      > </a
      ><a name="14755" href="https://agda.github.io/agda-stdlib/Function.html#713" class="Function Operator"
      >&#8728;</a
      ><a name="14756"
      > </a
      ><a name="14757" href="StlcProp.html#7640" class="InductiveConstructor"
      >free-&#183;&#7488;&#8322;</a
      ><a name="14765" class="Symbol"
      >)</a
      ><a name="14766"
      > </a
      ><a name="14767" href="StlcProp.html#14700" class="Bound"
      >&#8866;M</a
      ><a name="14769" class="Symbol"
      >)</a
      ><a name="14770"
      > 
</a
      ><a name="14772" href="StlcProp.html#11985" class="Function"
      >weaken</a
      ><a name="14778"
      > </a
      ><a name="14779" href="StlcProp.html#14779" class="Bound"
      >&#915;~&#915;&#8242;</a
      ><a name="14783"
      > </a
      ><a name="14784" href="Stlc.html#4381" class="InductiveConstructor"
      >&#120121;-I&#8321;</a
      ><a name="14788"
      > </a
      ><a name="14789" class="Symbol"
      >=</a
      ><a name="14790"
      > </a
      ><a name="14791" href="Stlc.html#4381" class="InductiveConstructor"
      >&#120121;-I&#8321;</a
      ><a name="14795"
      >
</a
      ><a name="14796" href="StlcProp.html#11985" class="Function"
      >weaken</a
      ><a name="14802"
      > </a
      ><a name="14803" href="StlcProp.html#14803" class="Bound"
      >&#915;~&#915;&#8242;</a
      ><a name="14807"
      > </a
      ><a name="14808" href="Stlc.html#4416" class="InductiveConstructor"
      >&#120121;-I&#8322;</a
      ><a name="14812"
      > </a
      ><a name="14813" class="Symbol"
      >=</a
      ><a name="14814"
      > </a
      ><a name="14815" href="Stlc.html#4416" class="InductiveConstructor"
      >&#120121;-I&#8322;</a
      ><a name="14819"
      >
</a
      ><a name="14820" href="StlcProp.html#11985" class="Function"
      >weaken</a
      ><a name="14826"
      > </a
      ><a name="14827" href="StlcProp.html#14827" class="Bound"
      >&#915;~&#915;&#8242;</a
      ><a name="14831"
      > </a
      ><a name="14832" class="Symbol"
      >(</a
      ><a name="14833" href="Stlc.html#4452" class="InductiveConstructor"
      >&#120121;-E</a
      ><a name="14836"
      > </a
      ><a name="14837" href="StlcProp.html#14837" class="Bound"
      >&#8866;L</a
      ><a name="14839"
      > </a
      ><a name="14840" href="StlcProp.html#14840" class="Bound"
      >&#8866;M</a
      ><a name="14842"
      > </a
      ><a name="14843" href="StlcProp.html#14843" class="Bound"
      >&#8866;N</a
      ><a name="14845" class="Symbol"
      >)</a
      ><a name="14846"
      >
  </a
      ><a name="14849" class="Symbol"
      >=</a
      ><a name="14850"
      > </a
      ><a name="14851" href="Stlc.html#4452" class="InductiveConstructor"
      >&#120121;-E</a
      ><a name="14854"
      > </a
      ><a name="14855" class="Symbol"
      >(</a
      ><a name="14856" href="StlcProp.html#11985" class="Function"
      >weaken</a
      ><a name="14862"
      > </a
      ><a name="14863" class="Symbol"
      >(</a
      ><a name="14864" href="StlcProp.html#14827" class="Bound"
      >&#915;~&#915;&#8242;</a
      ><a name="14868"
      > </a
      ><a name="14869" href="https://agda.github.io/agda-stdlib/Function.html#713" class="Function Operator"
      >&#8728;</a
      ><a name="14870"
      > </a
      ><a name="14871" href="StlcProp.html#7696" class="InductiveConstructor"
      >free-if&#7488;&#8321;</a
      ><a name="14880" class="Symbol"
      >)</a
      ><a name="14881"
      > </a
      ><a name="14882" href="StlcProp.html#14837" class="Bound"
      >&#8866;L</a
      ><a name="14884" class="Symbol"
      >)</a
      ><a name="14885"
      > </a
      ><a name="14886" class="Symbol"
      >(</a
      ><a name="14887" href="StlcProp.html#11985" class="Function"
      >weaken</a
      ><a name="14893"
      > </a
      ><a name="14894" class="Symbol"
      >(</a
      ><a name="14895" href="StlcProp.html#14827" class="Bound"
      >&#915;~&#915;&#8242;</a
      ><a name="14899"
      > </a
      ><a name="14900" href="https://agda.github.io/agda-stdlib/Function.html#713" class="Function Operator"
      >&#8728;</a
      ><a name="14901"
      > </a
      ><a name="14902" href="StlcProp.html#7768" class="InductiveConstructor"
      >free-if&#7488;&#8322;</a
      ><a name="14911" class="Symbol"
      >)</a
      ><a name="14912"
      > </a
      ><a name="14913" href="StlcProp.html#14840" class="Bound"
      >&#8866;M</a
      ><a name="14915" class="Symbol"
      >)</a
      ><a name="14916"
      > </a
      ><a name="14917" class="Symbol"
      >(</a
      ><a name="14918" href="StlcProp.html#11985" class="Function"
      >weaken</a
      ><a name="14924"
      > </a
      ><a name="14925" class="Symbol"
      >(</a
      ><a name="14926" href="StlcProp.html#14827" class="Bound"
      >&#915;~&#915;&#8242;</a
      ><a name="14930"
      > </a
      ><a name="14931" href="https://agda.github.io/agda-stdlib/Function.html#713" class="Function Operator"
      >&#8728;</a
      ><a name="14932"
      > </a
      ><a name="14933" href="StlcProp.html#7840" class="InductiveConstructor"
      >free-if&#7488;&#8323;</a
      ><a name="14942" class="Symbol"
      >)</a
      ><a name="14943"
      > </a
      ><a name="14944" href="StlcProp.html#14843" class="Bound"
      >&#8866;N</a
      ><a name="14946" class="Symbol"
      >)</a
      ><a name="14947"
      >

</a
      ><a name="14949" class="Comment"
      >{-
replaceCtxt f (var x x&#8758;A
) rewrite f var = var x x&#8758;A
replaceCtxt f (app t&#8321;&#8758;A&#8658;B t&#8322;&#8758;A)
  = app (replaceCtxt (f &#8728; app1) t&#8321;&#8758;A&#8658;B) (replaceCtxt (f &#8728; app2) t&#8322;&#8758;A)
replaceCtxt {&#915;} {&#915;&#8242;} f (abs {.&#915;} {x} {A} {B} {t&#8242;} t&#8242;&#8758;B)
  = abs (replaceCtxt f&#8242; t&#8242;&#8758;B)
  where
    f&#8242; : &#8704; {y} &#8594; y FreeIn t&#8242; &#8594; (&#915; , x &#8758; A) y &#8801; (&#915;&#8242; , x &#8758; A) y
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

</pre>


Now we come to the conceptual heart of the proof that reduction
preserves types---namely, the observation that _substitution_
preserves types.

Formally, the so-called _Substitution Lemma_ says this: Suppose we
have a term $$N$$ with a free variable $$x$$, and suppose we've been
able to assign a type $$B$$ to $$N$$ under the assumption that $$x$$ has
some type $$A$$.  Also, suppose that we have some other term $$V$$ and
that we've shown that $$V$$ has type $$A$$.  Then, since $$V$$ satisfies
the assumption we made about $$x$$ when typing $$N$$, we should be
able to substitute $$V$$ for each of the occurrences of $$x$$ in $$N$$
and obtain a new term that still has type $$B$$.

_Lemma_: If $$Γ , x ↦ A ⊢ N ∈ B$$ and $$∅ ⊢ V ∈ A$$, then
$$Γ ⊢ (N [ x := V ]) ∈ B$$.

<pre class="Agda">

<a name="16366" href="StlcProp.html#16366" class="Function"
      >preservation-[:=]</a
      ><a name="16383"
      > </a
      ><a name="16384" class="Symbol"
      >:</a
      ><a name="16385"
      > </a
      ><a name="16386" class="Symbol"
      >&#8704;</a
      ><a name="16387"
      > </a
      ><a name="16388" class="Symbol"
      >{</a
      ><a name="16389" href="StlcProp.html#16389" class="Bound"
      >&#915;</a
      ><a name="16390"
      > </a
      ><a name="16391" href="StlcProp.html#16391" class="Bound"
      >x</a
      ><a name="16392"
      > </a
      ><a name="16393" href="StlcProp.html#16393" class="Bound"
      >A</a
      ><a name="16394"
      > </a
      ><a name="16395" href="StlcProp.html#16395" class="Bound"
      >N</a
      ><a name="16396"
      > </a
      ><a name="16397" href="StlcProp.html#16397" class="Bound"
      >B</a
      ><a name="16398"
      > </a
      ><a name="16399" href="StlcProp.html#16399" class="Bound"
      >V</a
      ><a name="16400" class="Symbol"
      >}</a
      ><a name="16401"
      >
                 </a
      ><a name="16419" class="Symbol"
      >&#8594;</a
      ><a name="16420"
      > </a
      ><a name="16421" class="Symbol"
      >(</a
      ><a name="16422" href="StlcProp.html#16389" class="Bound"
      >&#915;</a
      ><a name="16423"
      > </a
      ><a name="16424" href="Maps.html#11317" class="Function Operator"
      >,</a
      ><a name="16425"
      > </a
      ><a name="16426" href="StlcProp.html#16391" class="Bound"
      >x</a
      ><a name="16427"
      > </a
      ><a name="16428" href="Maps.html#11317" class="Function Operator"
      >&#8614;</a
      ><a name="16429"
      > </a
      ><a name="16430" href="StlcProp.html#16393" class="Bound"
      >A</a
      ><a name="16431" class="Symbol"
      >)</a
      ><a name="16432"
      > </a
      ><a name="16433" href="Stlc.html#4116" class="Datatype Operator"
      >&#8866;</a
      ><a name="16434"
      > </a
      ><a name="16435" href="StlcProp.html#16395" class="Bound"
      >N</a
      ><a name="16436"
      > </a
      ><a name="16437" href="Stlc.html#4116" class="Datatype Operator"
      >&#8712;</a
      ><a name="16438"
      > </a
      ><a name="16439" href="StlcProp.html#16397" class="Bound"
      >B</a
      ><a name="16440"
      >
                 </a
      ><a name="16458" class="Symbol"
      >&#8594;</a
      ><a name="16459"
      > </a
      ><a name="16460" href="Maps.html#11235" class="Function"
      >&#8709;</a
      ><a name="16461"
      > </a
      ><a name="16462" href="Stlc.html#4116" class="Datatype Operator"
      >&#8866;</a
      ><a name="16463"
      > </a
      ><a name="16464" href="StlcProp.html#16399" class="Bound"
      >V</a
      ><a name="16465"
      > </a
      ><a name="16466" href="Stlc.html#4116" class="Datatype Operator"
      >&#8712;</a
      ><a name="16467"
      > </a
      ><a name="16468" href="StlcProp.html#16393" class="Bound"
      >A</a
      ><a name="16469"
      >
                 </a
      ><a name="16487" class="Symbol"
      >&#8594;</a
      ><a name="16488"
      > </a
      ><a name="16489" href="StlcProp.html#16389" class="Bound"
      >&#915;</a
      ><a name="16490"
      > </a
      ><a name="16491" href="Stlc.html#4116" class="Datatype Operator"
      >&#8866;</a
      ><a name="16492"
      > </a
      ><a name="16493" class="Symbol"
      >(</a
      ><a name="16494" href="StlcProp.html#16395" class="Bound"
      >N</a
      ><a name="16495"
      > </a
      ><a name="16496" href="Stlc.html#1756" class="Function Operator"
      >[</a
      ><a name="16497"
      > </a
      ><a name="16498" href="StlcProp.html#16391" class="Bound"
      >x</a
      ><a name="16499"
      > </a
      ><a name="16500" href="Stlc.html#1756" class="Function Operator"
      >:=</a
      ><a name="16502"
      > </a
      ><a name="16503" href="StlcProp.html#16399" class="Bound"
      >V</a
      ><a name="16504"
      > </a
      ><a name="16505" href="Stlc.html#1756" class="Function Operator"
      >]</a
      ><a name="16506" class="Symbol"
      >)</a
      ><a name="16507"
      > </a
      ><a name="16508" href="Stlc.html#4116" class="Datatype Operator"
      >&#8712;</a
      ><a name="16509"
      > </a
      ><a name="16510" href="StlcProp.html#16397" class="Bound"
      >B</a
      >

</pre>

One technical subtlety in the statement of the lemma is that
we assign $$V$$ the type $$A$$ in the _empty_ context---in other
words, we assume $$V$$ is closed.  This assumption considerably
simplifies the $$λᵀ$$ case of the proof (compared to assuming
$$Γ ⊢ V ∈ A$$, which would be the other reasonable assumption
at this point) because the context invariance lemma then tells us
that $$V$$ has type $$A$$ in any context at all---we don't have to
worry about free variables in $$V$$ clashing with the variable being
introduced into the context by $$λᵀ$$.

The substitution lemma can be viewed as a kind of "commutation"
property.  Intuitively, it says that substitution and typing can
be done in either order: we can either assign types to the terms
$$N$$ and $$V$$ separately (under suitable contexts) and then combine
them using substitution, or we can substitute first and then
assign a type to $$N [ x := V ]$$---the result is the same either
way.

_Proof_: We show, by induction on $$N$$, that for all $$A$$ and
$$Γ$$, if $$Γ , x ↦ A \vdash N ∈ B$$ and $$∅ ⊢ V ∈ A$$, then
$$Γ \vdash N [ x := V ] ∈ B$$.

  - If $$N$$ is a variable there are two cases to consider,
    depending on whether $$N$$ is $$x$$ or some other variable.

      - If $$N = varᵀ x$$, then from the fact that $$Γ , x ↦ A ⊢ N ∈ B$$
        we conclude that $$A = B$$.  We must show that $$x [ x := V] =
        V$$ has type $$A$$ under $$Γ$$, given the assumption that
        $$V$$ has type $$A$$ under the empty context.  This
        follows from context invariance: if a closed term has type
        $$A$$ in the empty context, it has that type in any context.

      - If $$N$$ is some variable $$x′$$ different from $$x$$, then
        we need only note that $$x′$$ has the same type under $$Γ , x ↦ A$$
        as under $$Γ$$.

  - If $$N$$ is an abstraction $$λᵀ x′ ∈ A′ ⇒ N′$$, then the IH tells us,
    for all $$Γ′$$́ and $$B′$$, that if $$Γ′ , x ↦ A ⊢ N′ ∈ B′$$
    and $$∅ ⊢ V ∈ A$$, then $$Γ′ ⊢ N′ [ x := V ] ∈ B′$$.

    The substitution in the conclusion behaves differently
    depending on whether $$x$$ and $$x′$$ are the same variable.

    First, suppose $$x ≡ x′$$.  Then, by the definition of
    substitution, $$N [ x := V] = N$$, so we just need to show $$Γ ⊢ N ∈ B$$.
    But we know $$Γ , x ↦ A ⊢ N ∈ B$$ and, since $$x ≡ x′$$
    does not appear free in $$λᵀ x′ ∈ A′ ⇒ N′$$, the context invariance
    lemma yields $$Γ ⊢ N ∈ B$$.

    Second, suppose $$x ≢ x′$$.  We know $$Γ , x ↦ A , x′ ↦ A′ ⊢ N′ ∈ B′$$
    by inversion of the typing relation, from which
    $$Γ , x′ ↦ A′ , x ↦ A ⊢ N′ ∈ B′$$ follows by update permute,
    so the IH applies, giving us $$Γ , x′ ↦ A′ ⊢ N′ [ x := V ] ∈ B′$$
    By $$⇒-I$$, we have $$Γ ⊢ λᵀ x′ ∈ A′ ⇒ (N′ [ x := V ]) ∈ A′ ⇒ B′$$
    and the definition of substitution (noting $$x ≢ x′$$) gives
    $$Γ ⊢ (λᵀ x′ ∈ A′ ⇒ N′) [ x := V ] ∈ A′ ⇒ B′$$ as required.

  - If $$N$$ is an application $$L′ ·ᵀ M′$$, the result follows
    straightforwardly from the definition of substitution and the
    induction hypotheses.

  - The remaining cases are similar to the application case.

We need a couple of lemmas. A closed term can be weakened to any context, and just is injective.
<pre class="Agda">

<a name="19751" href="StlcProp.html#19751" class="Function"
      >weaken-closed</a
      ><a name="19764"
      > </a
      ><a name="19765" class="Symbol"
      >:</a
      ><a name="19766"
      > </a
      ><a name="19767" class="Symbol"
      >&#8704;</a
      ><a name="19768"
      > </a
      ><a name="19769" class="Symbol"
      >{</a
      ><a name="19770" href="StlcProp.html#19770" class="Bound"
      >V</a
      ><a name="19771"
      > </a
      ><a name="19772" href="StlcProp.html#19772" class="Bound"
      >A</a
      ><a name="19773"
      > </a
      ><a name="19774" href="StlcProp.html#19774" class="Bound"
      >&#915;</a
      ><a name="19775" class="Symbol"
      >}</a
      ><a name="19776"
      > </a
      ><a name="19777" class="Symbol"
      >&#8594;</a
      ><a name="19778"
      > </a
      ><a name="19779" href="Maps.html#11235" class="Function"
      >&#8709;</a
      ><a name="19780"
      > </a
      ><a name="19781" href="Stlc.html#4116" class="Datatype Operator"
      >&#8866;</a
      ><a name="19782"
      > </a
      ><a name="19783" href="StlcProp.html#19770" class="Bound"
      >V</a
      ><a name="19784"
      > </a
      ><a name="19785" href="Stlc.html#4116" class="Datatype Operator"
      >&#8712;</a
      ><a name="19786"
      > </a
      ><a name="19787" href="StlcProp.html#19772" class="Bound"
      >A</a
      ><a name="19788"
      > </a
      ><a name="19789" class="Symbol"
      >&#8594;</a
      ><a name="19790"
      > </a
      ><a name="19791" href="StlcProp.html#19774" class="Bound"
      >&#915;</a
      ><a name="19792"
      > </a
      ><a name="19793" href="Stlc.html#4116" class="Datatype Operator"
      >&#8866;</a
      ><a name="19794"
      > </a
      ><a name="19795" href="StlcProp.html#19770" class="Bound"
      >V</a
      ><a name="19796"
      > </a
      ><a name="19797" href="Stlc.html#4116" class="Datatype Operator"
      >&#8712;</a
      ><a name="19798"
      > </a
      ><a name="19799" href="StlcProp.html#19772" class="Bound"
      >A</a
      ><a name="19800"
      >
</a
      ><a name="19801" href="StlcProp.html#19751" class="Function"
      >weaken-closed</a
      ><a name="19814"
      > </a
      ><a name="19815" class="Symbol"
      >{</a
      ><a name="19816" href="StlcProp.html#19816" class="Bound"
      >V</a
      ><a name="19817" class="Symbol"
      >}</a
      ><a name="19818"
      > </a
      ><a name="19819" class="Symbol"
      >{</a
      ><a name="19820" href="StlcProp.html#19820" class="Bound"
      >A</a
      ><a name="19821" class="Symbol"
      >}</a
      ><a name="19822"
      > </a
      ><a name="19823" class="Symbol"
      >{</a
      ><a name="19824" href="StlcProp.html#19824" class="Bound"
      >&#915;</a
      ><a name="19825" class="Symbol"
      >}</a
      ><a name="19826"
      > </a
      ><a name="19827" href="StlcProp.html#19827" class="Bound"
      >&#8866;V</a
      ><a name="19829"
      > </a
      ><a name="19830" class="Symbol"
      >=</a
      ><a name="19831"
      > </a
      ><a name="19832" href="StlcProp.html#11985" class="Function"
      >weaken</a
      ><a name="19838"
      > </a
      ><a name="19839" href="StlcProp.html#19857" class="Function"
      >&#915;~&#915;&#8242;</a
      ><a name="19843"
      > </a
      ><a name="19844" href="StlcProp.html#19827" class="Bound"
      >&#8866;V</a
      ><a name="19846"
      >
  </a
      ><a name="19849" class="Keyword"
      >where</a
      ><a name="19854"
      >
  </a
      ><a name="19857" href="StlcProp.html#19857" class="Function"
      >&#915;~&#915;&#8242;</a
      ><a name="19861"
      > </a
      ><a name="19862" class="Symbol"
      >:</a
      ><a name="19863"
      > </a
      ><a name="19864" class="Symbol"
      >&#8704;</a
      ><a name="19865"
      > </a
      ><a name="19866" class="Symbol"
      >{</a
      ><a name="19867" href="StlcProp.html#19867" class="Bound"
      >x</a
      ><a name="19868" class="Symbol"
      >}</a
      ><a name="19869"
      > </a
      ><a name="19870" class="Symbol"
      >&#8594;</a
      ><a name="19871"
      > </a
      ><a name="19872" href="StlcProp.html#19867" class="Bound"
      >x</a
      ><a name="19873"
      > </a
      ><a name="19874" href="StlcProp.html#7436" class="Datatype Operator"
      >FreeIn</a
      ><a name="19880"
      > </a
      ><a name="19881" href="StlcProp.html#19816" class="Bound"
      >V</a
      ><a name="19882"
      > </a
      ><a name="19883" class="Symbol"
      >&#8594;</a
      ><a name="19884"
      > </a
      ><a name="19885" href="Maps.html#11235" class="Function"
      >&#8709;</a
      ><a name="19886"
      > </a
      ><a name="19887" href="StlcProp.html#19867" class="Bound"
      >x</a
      ><a name="19888"
      > </a
      ><a name="19889" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="19890"
      > </a
      ><a name="19891" href="StlcProp.html#19824" class="Bound"
      >&#915;</a
      ><a name="19892"
      > </a
      ><a name="19893" href="StlcProp.html#19867" class="Bound"
      >x</a
      ><a name="19894"
      >
  </a
      ><a name="19897" href="StlcProp.html#19857" class="Function"
      >&#915;~&#915;&#8242;</a
      ><a name="19901"
      > </a
      ><a name="19902" class="Symbol"
      >{</a
      ><a name="19903" href="StlcProp.html#19903" class="Bound"
      >x</a
      ><a name="19904" class="Symbol"
      >}</a
      ><a name="19905"
      > </a
      ><a name="19906" href="StlcProp.html#19906" class="Bound"
      >x&#8712;V</a
      ><a name="19909"
      > </a
      ><a name="19910" class="Symbol"
      >=</a
      ><a name="19911"
      > </a
      ><a name="19912" href="https://agda.github.io/agda-stdlib/Data.Empty.html#360" class="Function"
      >&#8869;-elim</a
      ><a name="19918"
      > </a
      ><a name="19919" class="Symbol"
      >(</a
      ><a name="19920" href="StlcProp.html#19943" class="Function"
      >x&#8713;V</a
      ><a name="19923"
      > </a
      ><a name="19924" href="StlcProp.html#19906" class="Bound"
      >x&#8712;V</a
      ><a name="19927" class="Symbol"
      >)</a
      ><a name="19928"
      >
    </a
      ><a name="19933" class="Keyword"
      >where</a
      ><a name="19938"
      >
    </a
      ><a name="19943" href="StlcProp.html#19943" class="Function"
      >x&#8713;V</a
      ><a name="19946"
      > </a
      ><a name="19947" class="Symbol"
      >:</a
      ><a name="19948"
      > </a
      ><a name="19949" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#414" class="Function Operator"
      >&#172;</a
      ><a name="19950"
      > </a
      ><a name="19951" class="Symbol"
      >(</a
      ><a name="19952" href="StlcProp.html#19903" class="Bound"
      >x</a
      ><a name="19953"
      > </a
      ><a name="19954" href="StlcProp.html#7436" class="Datatype Operator"
      >FreeIn</a
      ><a name="19960"
      > </a
      ><a name="19961" href="StlcProp.html#19816" class="Bound"
      >V</a
      ><a name="19962" class="Symbol"
      >)</a
      ><a name="19963"
      >
    </a
      ><a name="19968" href="StlcProp.html#19943" class="Function"
      >x&#8713;V</a
      ><a name="19971"
      > </a
      ><a name="19972" class="Symbol"
      >=</a
      ><a name="19973"
      > </a
      ><a name="19974" href="StlcProp.html#11272" class="Postulate"
      >&#8709;&#8866;-closed</a
      ><a name="19983"
      > </a
      ><a name="19984" href="StlcProp.html#19827" class="Bound"
      >&#8866;V</a
      ><a name="19986"
      > </a
      ><a name="19987" class="Symbol"
      >{</a
      ><a name="19988" href="StlcProp.html#19903" class="Bound"
      >x</a
      ><a name="19989" class="Symbol"
      >}</a
      ><a name="19990"
      >

</a
      ><a name="19992" href="StlcProp.html#19992" class="Function"
      >just-injective</a
      ><a name="20006"
      > </a
      ><a name="20007" class="Symbol"
      >:</a
      ><a name="20008"
      > </a
      ><a name="20009" class="Symbol"
      >&#8704;</a
      ><a name="20010"
      > </a
      ><a name="20011" class="Symbol"
      >{</a
      ><a name="20012" href="StlcProp.html#20012" class="Bound"
      >X</a
      ><a name="20013"
      > </a
      ><a name="20014" class="Symbol"
      >:</a
      ><a name="20015"
      > </a
      ><a name="20016" class="PrimitiveType"
      >Set</a
      ><a name="20019" class="Symbol"
      >}</a
      ><a name="20020"
      > </a
      ><a name="20021" class="Symbol"
      >{</a
      ><a name="20022" href="StlcProp.html#20022" class="Bound"
      >x</a
      ><a name="20023"
      > </a
      ><a name="20024" href="StlcProp.html#20024" class="Bound"
      >y</a
      ><a name="20025"
      > </a
      ><a name="20026" class="Symbol"
      >:</a
      ><a name="20027"
      > </a
      ><a name="20028" href="StlcProp.html#20012" class="Bound"
      >X</a
      ><a name="20029" class="Symbol"
      >}</a
      ><a name="20030"
      > </a
      ><a name="20031" class="Symbol"
      >&#8594;</a
      ><a name="20032"
      > </a
      ><a name="20033" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >_&#8801;_</a
      ><a name="20036"
      > </a
      ><a name="20037" class="Symbol"
      >{</a
      ><a name="20038" class="Argument"
      >A</a
      ><a name="20039"
      > </a
      ><a name="20040" class="Symbol"
      >=</a
      ><a name="20041"
      > </a
      ><a name="20042" href="https://agda.github.io/agda-stdlib/Data.Maybe.Base.html#335" class="Datatype"
      >Maybe</a
      ><a name="20047"
      > </a
      ><a name="20048" href="StlcProp.html#20012" class="Bound"
      >X</a
      ><a name="20049" class="Symbol"
      >}</a
      ><a name="20050"
      > </a
      ><a name="20051" class="Symbol"
      >(</a
      ><a name="20052" href="https://agda.github.io/agda-stdlib/Data.Maybe.Base.html#373" class="InductiveConstructor"
      >just</a
      ><a name="20056"
      > </a
      ><a name="20057" href="StlcProp.html#20022" class="Bound"
      >x</a
      ><a name="20058" class="Symbol"
      >)</a
      ><a name="20059"
      > </a
      ><a name="20060" class="Symbol"
      >(</a
      ><a name="20061" href="https://agda.github.io/agda-stdlib/Data.Maybe.Base.html#373" class="InductiveConstructor"
      >just</a
      ><a name="20065"
      > </a
      ><a name="20066" href="StlcProp.html#20024" class="Bound"
      >y</a
      ><a name="20067" class="Symbol"
      >)</a
      ><a name="20068"
      > </a
      ><a name="20069" class="Symbol"
      >&#8594;</a
      ><a name="20070"
      > </a
      ><a name="20071" href="StlcProp.html#20022" class="Bound"
      >x</a
      ><a name="20072"
      > </a
      ><a name="20073" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="20074"
      > </a
      ><a name="20075" href="StlcProp.html#20024" class="Bound"
      >y</a
      ><a name="20076"
      >
</a
      ><a name="20077" href="StlcProp.html#19992" class="Function"
      >just-injective</a
      ><a name="20091"
      > </a
      ><a name="20092" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="20096"
      > </a
      ><a name="20097" class="Symbol"
      >=</a
      ><a name="20098"
      > </a
      ><a name="20099" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      >

</pre>

<pre class="Agda">

<a name="20129" href="StlcProp.html#16366" class="Function"
      >preservation-[:=]</a
      ><a name="20146"
      > </a
      ><a name="20147" class="Symbol"
      >{_}</a
      ><a name="20150"
      > </a
      ><a name="20151" class="Symbol"
      >{</a
      ><a name="20152" href="StlcProp.html#20152" class="Bound"
      >x</a
      ><a name="20153" class="Symbol"
      >}</a
      ><a name="20154"
      > </a
      ><a name="20155" class="Symbol"
      >(</a
      ><a name="20156" href="Stlc.html#4160" class="InductiveConstructor"
      >Ax</a
      ><a name="20158"
      > </a
      ><a name="20159" class="Symbol"
      >{_}</a
      ><a name="20162"
      > </a
      ><a name="20163" class="Symbol"
      >{</a
      ><a name="20164" href="StlcProp.html#20164" class="Bound"
      >x&#8242;</a
      ><a name="20166" class="Symbol"
      >}</a
      ><a name="20167"
      > </a
      ><a name="20168" href="StlcProp.html#20168" class="Bound"
      >[&#915;,x&#8614;A]x&#8242;&#8801;B</a
      ><a name="20179" class="Symbol"
      >)</a
      ><a name="20180"
      > </a
      ><a name="20181" href="StlcProp.html#20181" class="Bound"
      >&#8866;V</a
      ><a name="20183"
      > </a
      ><a name="20184" class="Keyword"
      >with</a
      ><a name="20188"
      > </a
      ><a name="20189" href="StlcProp.html#20152" class="Bound"
      >x</a
      ><a name="20190"
      > </a
      ><a name="20191" href="Maps.html#2558" class="Function Operator"
      >&#8799;</a
      ><a name="20192"
      > </a
      ><a name="20193" href="StlcProp.html#20164" class="Bound"
      >x&#8242;</a
      ><a name="20195"
      >
</a
      ><a name="20196" class="Symbol"
      >...|</a
      ><a name="20200"
      > </a
      ><a name="20201" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#520" class="InductiveConstructor"
      >yes</a
      ><a name="20204"
      > </a
      ><a name="20205" href="StlcProp.html#20205" class="Bound"
      >x&#8801;x&#8242;</a
      ><a name="20209"
      > </a
      ><a name="20210" class="Keyword"
      >rewrite</a
      ><a name="20217"
      > </a
      ><a name="20218" href="StlcProp.html#19992" class="Function"
      >just-injective</a
      ><a name="20232"
      > </a
      ><a name="20233" href="StlcProp.html#20168" class="Bound"
      >[&#915;,x&#8614;A]x&#8242;&#8801;B</a
      ><a name="20244"
      >  </a
      ><a name="20246" class="Symbol"
      >=</a
      ><a name="20247"
      >  </a
      ><a name="20249" href="StlcProp.html#19751" class="Function"
      >weaken-closed</a
      ><a name="20262"
      > </a
      ><a name="20263" href="StlcProp.html#20181" class="Bound"
      >&#8866;V</a
      ><a name="20265"
      >
</a
      ><a name="20266" class="Symbol"
      >...|</a
      ><a name="20270"
      > </a
      ><a name="20271" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#547" class="InductiveConstructor"
      >no</a
      ><a name="20273"
      >  </a
      ><a name="20275" href="StlcProp.html#20275" class="Bound"
      >x&#8802;x&#8242;</a
      ><a name="20279"
      >  </a
      ><a name="20281" class="Symbol"
      >=</a
      ><a name="20282"
      >  </a
      ><a name="20284" href="Stlc.html#4160" class="InductiveConstructor"
      >Ax</a
      ><a name="20286"
      > </a
      ><a name="20287" href="StlcProp.html#20168" class="Bound"
      >[&#915;,x&#8614;A]x&#8242;&#8801;B</a
      ><a name="20298"
      >
</a
      ><a name="20299" class="Comment"
      >{-
preservation-[:=] {&#915;} {x} {A} {var&#7488; x&#8242;} {B} {V} (Ax {.(&#915; , x &#8614; A)} {.x&#8242;} {.B} &#915;x&#8242;&#8801;B) &#8866;V with x &#8799; x&#8242;
...| yes x&#8801;x&#8242; rewrite just-injective &#915;x&#8242;&#8801;B  =  weaken-closed &#8866;V
...| no  x&#8802;x&#8242;  =  Ax {&#915;} {x&#8242;} {B} &#915;x&#8242;&#8801;B
-}</a
      ><a name="20508"
      >
</a
      ><a name="20509" href="StlcProp.html#16366" class="Function"
      >preservation-[:=]</a
      ><a name="20526"
      > </a
      ><a name="20527" class="Symbol"
      >{</a
      ><a name="20528" href="StlcProp.html#20528" class="Bound"
      >&#915;</a
      ><a name="20529" class="Symbol"
      >}</a
      ><a name="20530"
      > </a
      ><a name="20531" class="Symbol"
      >{</a
      ><a name="20532" href="StlcProp.html#20532" class="Bound"
      >x</a
      ><a name="20533" class="Symbol"
      >}</a
      ><a name="20534"
      > </a
      ><a name="20535" class="Symbol"
      >{</a
      ><a name="20536" href="StlcProp.html#20536" class="Bound"
      >A</a
      ><a name="20537" class="Symbol"
      >}</a
      ><a name="20538"
      > </a
      ><a name="20539" class="Symbol"
      >{</a
      ><a name="20540" href="Stlc.html#1070" class="InductiveConstructor Operator"
      >&#955;&#7488;</a
      ><a name="20542"
      > </a
      ><a name="20543" href="StlcProp.html#20543" class="Bound"
      >x&#8242;</a
      ><a name="20545"
      > </a
      ><a name="20546" href="Stlc.html#1070" class="InductiveConstructor Operator"
      >&#8712;</a
      ><a name="20547"
      > </a
      ><a name="20548" href="StlcProp.html#20548" class="Bound"
      >A&#8242;</a
      ><a name="20550"
      > </a
      ><a name="20551" href="Stlc.html#1070" class="InductiveConstructor Operator"
      >&#8658;</a
      ><a name="20552"
      > </a
      ><a name="20553" href="StlcProp.html#20553" class="Bound"
      >N&#8242;</a
      ><a name="20555" class="Symbol"
      >}</a
      ><a name="20556"
      > </a
      ><a name="20557" class="Symbol"
      >{</a
      ><a name="20558" class="DottedPattern Symbol"
      >.</a
      ><a name="20559" href="StlcProp.html#20548" class="DottedPattern Bound"
      >A&#8242;</a
      ><a name="20561"
      > </a
      ><a name="20562" href="Stlc.html#1001" class="InductiveConstructor Operator"
      >&#8658;</a
      ><a name="20563"
      > </a
      ><a name="20564" href="StlcProp.html#20564" class="Bound"
      >B&#8242;</a
      ><a name="20566" class="Symbol"
      >}</a
      ><a name="20567"
      > </a
      ><a name="20568" class="Symbol"
      >{</a
      ><a name="20569" href="StlcProp.html#20569" class="Bound"
      >V</a
      ><a name="20570" class="Symbol"
      >}</a
      ><a name="20571"
      > </a
      ><a name="20572" class="Symbol"
      >(</a
      ><a name="20573" href="Stlc.html#4217" class="InductiveConstructor"
      >&#8658;-I</a
      ><a name="20576"
      > </a
      ><a name="20577" class="Symbol"
      >{</a
      ><a name="20578" class="DottedPattern Symbol"
      >.(</a
      ><a name="20580" href="StlcProp.html#20528" class="DottedPattern Bound"
      >&#915;</a
      ><a name="20581"
      > </a
      ><a name="20582" href="Maps.html#11317" class="DottedPattern Function Operator"
      >,</a
      ><a name="20583"
      > </a
      ><a name="20584" href="StlcProp.html#20532" class="DottedPattern Bound"
      >x</a
      ><a name="20585"
      > </a
      ><a name="20586" href="Maps.html#11317" class="DottedPattern Function Operator"
      >&#8614;</a
      ><a name="20587"
      > </a
      ><a name="20588" href="StlcProp.html#20536" class="DottedPattern Bound"
      >A</a
      ><a name="20589" class="DottedPattern Symbol"
      >)</a
      ><a name="20590" class="Symbol"
      >}</a
      ><a name="20591"
      > </a
      ><a name="20592" class="Symbol"
      >{</a
      ><a name="20593" class="DottedPattern Symbol"
      >.</a
      ><a name="20594" href="StlcProp.html#20543" class="DottedPattern Bound"
      >x&#8242;</a
      ><a name="20596" class="Symbol"
      >}</a
      ><a name="20597"
      > </a
      ><a name="20598" class="Symbol"
      >{</a
      ><a name="20599" class="DottedPattern Symbol"
      >.</a
      ><a name="20600" href="StlcProp.html#20553" class="DottedPattern Bound"
      >N&#8242;</a
      ><a name="20602" class="Symbol"
      >}</a
      ><a name="20603"
      > </a
      ><a name="20604" class="Symbol"
      >{</a
      ><a name="20605" class="DottedPattern Symbol"
      >.</a
      ><a name="20606" href="StlcProp.html#20548" class="DottedPattern Bound"
      >A&#8242;</a
      ><a name="20608" class="Symbol"
      >}</a
      ><a name="20609"
      > </a
      ><a name="20610" class="Symbol"
      >{</a
      ><a name="20611" class="DottedPattern Symbol"
      >.</a
      ><a name="20612" href="StlcProp.html#20564" class="DottedPattern Bound"
      >B&#8242;</a
      ><a name="20614" class="Symbol"
      >}</a
      ><a name="20615"
      > </a
      ><a name="20616" href="StlcProp.html#20616" class="Bound"
      >&#8866;N&#8242;</a
      ><a name="20619" class="Symbol"
      >)</a
      ><a name="20620"
      > </a
      ><a name="20621" href="StlcProp.html#20621" class="Bound"
      >&#8866;V</a
      ><a name="20623"
      > </a
      ><a name="20624" class="Keyword"
      >with</a
      ><a name="20628"
      > </a
      ><a name="20629" href="StlcProp.html#20532" class="Bound"
      >x</a
      ><a name="20630"
      > </a
      ><a name="20631" href="Maps.html#2558" class="Function Operator"
      >&#8799;</a
      ><a name="20632"
      > </a
      ><a name="20633" href="StlcProp.html#20543" class="Bound"
      >x&#8242;</a
      ><a name="20635"
      >
</a
      ><a name="20636" class="Symbol"
      >...|</a
      ><a name="20640"
      > </a
      ><a name="20641" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#520" class="InductiveConstructor"
      >yes</a
      ><a name="20644"
      > </a
      ><a name="20645" href="StlcProp.html#20645" class="Bound"
      >x&#8801;x&#8242;</a
      ><a name="20649"
      > </a
      ><a name="20650" class="Keyword"
      >rewrite</a
      ><a name="20657"
      > </a
      ><a name="20658" href="StlcProp.html#20645" class="Bound"
      >x&#8801;x&#8242;</a
      ><a name="20662"
      > </a
      ><a name="20663" class="Symbol"
      >=</a
      ><a name="20664"
      > </a
      ><a name="20665" href="StlcProp.html#11985" class="Function"
      >weaken</a
      ><a name="20671"
      > </a
      ><a name="20672" href="StlcProp.html#20697" class="Function"
      >&#915;&#8242;~&#915;</a
      ><a name="20676"
      > </a
      ><a name="20677" class="Symbol"
      >(</a
      ><a name="20678" href="Stlc.html#4217" class="InductiveConstructor"
      >&#8658;-I</a
      ><a name="20681"
      > </a
      ><a name="20682" href="StlcProp.html#20616" class="Bound"
      >&#8866;N&#8242;</a
      ><a name="20685" class="Symbol"
      >)</a
      ><a name="20686"
      >
  </a
      ><a name="20689" class="Keyword"
      >where</a
      ><a name="20694"
      >
  </a
      ><a name="20697" href="StlcProp.html#20697" class="Function"
      >&#915;&#8242;~&#915;</a
      ><a name="20701"
      > </a
      ><a name="20702" class="Symbol"
      >:</a
      ><a name="20703"
      > </a
      ><a name="20704" class="Symbol"
      >&#8704;</a
      ><a name="20705"
      > </a
      ><a name="20706" class="Symbol"
      >{</a
      ><a name="20707" href="StlcProp.html#20707" class="Bound"
      >y</a
      ><a name="20708" class="Symbol"
      >}</a
      ><a name="20709"
      > </a
      ><a name="20710" class="Symbol"
      >&#8594;</a
      ><a name="20711"
      > </a
      ><a name="20712" href="StlcProp.html#20707" class="Bound"
      >y</a
      ><a name="20713"
      > </a
      ><a name="20714" href="StlcProp.html#7436" class="Datatype Operator"
      >FreeIn</a
      ><a name="20720"
      > </a
      ><a name="20721" class="Symbol"
      >(</a
      ><a name="20722" href="Stlc.html#1070" class="InductiveConstructor Operator"
      >&#955;&#7488;</a
      ><a name="20724"
      > </a
      ><a name="20725" href="StlcProp.html#20543" class="Bound"
      >x&#8242;</a
      ><a name="20727"
      > </a
      ><a name="20728" href="Stlc.html#1070" class="InductiveConstructor Operator"
      >&#8712;</a
      ><a name="20729"
      > </a
      ><a name="20730" href="StlcProp.html#20548" class="Bound"
      >A&#8242;</a
      ><a name="20732"
      > </a
      ><a name="20733" href="Stlc.html#1070" class="InductiveConstructor Operator"
      >&#8658;</a
      ><a name="20734"
      > </a
      ><a name="20735" href="StlcProp.html#20553" class="Bound"
      >N&#8242;</a
      ><a name="20737" class="Symbol"
      >)</a
      ><a name="20738"
      > </a
      ><a name="20739" class="Symbol"
      >&#8594;</a
      ><a name="20740"
      > </a
      ><a name="20741" class="Symbol"
      >(</a
      ><a name="20742" href="StlcProp.html#20528" class="Bound"
      >&#915;</a
      ><a name="20743"
      > </a
      ><a name="20744" href="Maps.html#11317" class="Function Operator"
      >,</a
      ><a name="20745"
      > </a
      ><a name="20746" href="StlcProp.html#20543" class="Bound"
      >x&#8242;</a
      ><a name="20748"
      > </a
      ><a name="20749" href="Maps.html#11317" class="Function Operator"
      >&#8614;</a
      ><a name="20750"
      > </a
      ><a name="20751" href="StlcProp.html#20536" class="Bound"
      >A</a
      ><a name="20752" class="Symbol"
      >)</a
      ><a name="20753"
      > </a
      ><a name="20754" href="StlcProp.html#20707" class="Bound"
      >y</a
      ><a name="20755"
      > </a
      ><a name="20756" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="20757"
      > </a
      ><a name="20758" href="StlcProp.html#20528" class="Bound"
      >&#915;</a
      ><a name="20759"
      > </a
      ><a name="20760" href="StlcProp.html#20707" class="Bound"
      >y</a
      ><a name="20761"
      >
  </a
      ><a name="20764" href="StlcProp.html#20697" class="Function"
      >&#915;&#8242;~&#915;</a
      ><a name="20768"
      > </a
      ><a name="20769" class="Symbol"
      >{</a
      ><a name="20770" href="StlcProp.html#20770" class="Bound"
      >y</a
      ><a name="20771" class="Symbol"
      >}</a
      ><a name="20772"
      > </a
      ><a name="20773" class="Symbol"
      >(</a
      ><a name="20774" href="StlcProp.html#7512" class="InductiveConstructor"
      >free-&#955;&#7488;</a
      ><a name="20781"
      > </a
      ><a name="20782" href="StlcProp.html#20782" class="Bound"
      >x&#8242;&#8802;y</a
      ><a name="20786"
      > </a
      ><a name="20787" href="StlcProp.html#20787" class="Bound"
      >y&#8712;N&#8242;</a
      ><a name="20791" class="Symbol"
      >)</a
      ><a name="20792"
      > </a
      ><a name="20793" class="Keyword"
      >with</a
      ><a name="20797"
      > </a
      ><a name="20798" href="StlcProp.html#20543" class="Bound"
      >x&#8242;</a
      ><a name="20800"
      > </a
      ><a name="20801" href="Maps.html#2558" class="Function Operator"
      >&#8799;</a
      ><a name="20802"
      > </a
      ><a name="20803" href="StlcProp.html#20770" class="Bound"
      >y</a
      ><a name="20804"
      >
  </a
      ><a name="20807" class="Symbol"
      >...|</a
      ><a name="20811"
      > </a
      ><a name="20812" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#520" class="InductiveConstructor"
      >yes</a
      ><a name="20815"
      > </a
      ><a name="20816" href="StlcProp.html#20816" class="Bound"
      >x&#8242;&#8801;y</a
      ><a name="20820"
      >  </a
      ><a name="20822" class="Symbol"
      >=</a
      ><a name="20823"
      > </a
      ><a name="20824" href="https://agda.github.io/agda-stdlib/Data.Empty.html#360" class="Function"
      >&#8869;-elim</a
      ><a name="20830"
      > </a
      ><a name="20831" class="Symbol"
      >(</a
      ><a name="20832" href="StlcProp.html#20782" class="Bound"
      >x&#8242;&#8802;y</a
      ><a name="20836"
      > </a
      ><a name="20837" href="StlcProp.html#20816" class="Bound"
      >x&#8242;&#8801;y</a
      ><a name="20841" class="Symbol"
      >)</a
      ><a name="20842"
      >
  </a
      ><a name="20845" class="Symbol"
      >...|</a
      ><a name="20849"
      > </a
      ><a name="20850" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#547" class="InductiveConstructor"
      >no</a
      ><a name="20852"
      >  </a
      ><a name="20854" class="Symbol"
      >_</a
      ><a name="20855"
      >     </a
      ><a name="20860" class="Symbol"
      >=</a
      ><a name="20861"
      > </a
      ><a name="20862" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="20866"
      >
</a
      ><a name="20867" class="Symbol"
      >...|</a
      ><a name="20871"
      > </a
      ><a name="20872" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#547" class="InductiveConstructor"
      >no</a
      ><a name="20874"
      >  </a
      ><a name="20876" href="StlcProp.html#20876" class="Bound"
      >x&#8802;x&#8242;</a
      ><a name="20880"
      > </a
      ><a name="20881" class="Symbol"
      >=</a
      ><a name="20882"
      > </a
      ><a name="20883" href="Stlc.html#4217" class="InductiveConstructor"
      >&#8658;-I</a
      ><a name="20886"
      > </a
      ><a name="20887" href="StlcProp.html#21004" class="Function"
      >&#8866;N&#8242;V</a
      ><a name="20891"
      >
  </a
      ><a name="20894" class="Keyword"
      >where</a
      ><a name="20899"
      >
  </a
      ><a name="20902" href="StlcProp.html#20902" class="Function"
      >x&#8242;x&#8866;N&#8242;</a
      ><a name="20908"
      > </a
      ><a name="20909" class="Symbol"
      >:</a
      ><a name="20910"
      > </a
      ><a name="20911" class="Symbol"
      >(</a
      ><a name="20912" href="StlcProp.html#20528" class="Bound"
      >&#915;</a
      ><a name="20913"
      > </a
      ><a name="20914" href="Maps.html#11538" class="Function Operator"
      >,</a
      ><a name="20915"
      > </a
      ><a name="20916" href="StlcProp.html#20543" class="Bound"
      >x&#8242;</a
      ><a name="20918"
      > </a
      ><a name="20919" href="Maps.html#11538" class="Function Operator"
      >&#8614;</a
      ><a name="20920"
      > </a
      ><a name="20921" href="StlcProp.html#20548" class="Bound"
      >A&#8242;</a
      ><a name="20923"
      > </a
      ><a name="20924" href="Maps.html#11538" class="Function Operator"
      >,</a
      ><a name="20925"
      > </a
      ><a name="20926" href="StlcProp.html#20532" class="Bound"
      >x</a
      ><a name="20927"
      > </a
      ><a name="20928" href="Maps.html#11538" class="Function Operator"
      >&#8614;</a
      ><a name="20929"
      > </a
      ><a name="20930" href="StlcProp.html#20536" class="Bound"
      >A</a
      ><a name="20931" class="Symbol"
      >)</a
      ><a name="20932"
      > </a
      ><a name="20933" href="Stlc.html#4116" class="Datatype Operator"
      >&#8866;</a
      ><a name="20934"
      > </a
      ><a name="20935" href="StlcProp.html#20553" class="Bound"
      >N&#8242;</a
      ><a name="20937"
      > </a
      ><a name="20938" href="Stlc.html#4116" class="Datatype Operator"
      >&#8712;</a
      ><a name="20939"
      > </a
      ><a name="20940" href="StlcProp.html#20564" class="Bound"
      >B&#8242;</a
      ><a name="20942"
      >
  </a
      ><a name="20945" href="StlcProp.html#20902" class="Function"
      >x&#8242;x&#8866;N&#8242;</a
      ><a name="20951"
      > </a
      ><a name="20952" class="Keyword"
      >rewrite</a
      ><a name="20959"
      > </a
      ><a name="20960" href="Maps.html#13012" class="Function"
      >update-permute</a
      ><a name="20974"
      > </a
      ><a name="20975" href="StlcProp.html#20528" class="Bound"
      >&#915;</a
      ><a name="20976"
      > </a
      ><a name="20977" href="StlcProp.html#20532" class="Bound"
      >x</a
      ><a name="20978"
      > </a
      ><a name="20979" href="StlcProp.html#20536" class="Bound"
      >A</a
      ><a name="20980"
      > </a
      ><a name="20981" href="StlcProp.html#20543" class="Bound"
      >x&#8242;</a
      ><a name="20983"
      > </a
      ><a name="20984" href="StlcProp.html#20548" class="Bound"
      >A&#8242;</a
      ><a name="20986"
      > </a
      ><a name="20987" href="StlcProp.html#20876" class="Bound"
      >x&#8802;x&#8242;</a
      ><a name="20991"
      > </a
      ><a name="20992" class="Symbol"
      >=</a
      ><a name="20993"
      > </a
      ><a name="20994" class="Symbol"
      >{!&#8866;N&#8242;!}</a
      ><a name="21001"
      >
  </a
      ><a name="21004" href="StlcProp.html#21004" class="Function"
      >&#8866;N&#8242;V</a
      ><a name="21008"
      > </a
      ><a name="21009" class="Symbol"
      >:</a
      ><a name="21010"
      > </a
      ><a name="21011" class="Symbol"
      >(</a
      ><a name="21012" href="StlcProp.html#20528" class="Bound"
      >&#915;</a
      ><a name="21013"
      > </a
      ><a name="21014" href="Maps.html#11317" class="Function Operator"
      >,</a
      ><a name="21015"
      > </a
      ><a name="21016" href="StlcProp.html#20543" class="Bound"
      >x&#8242;</a
      ><a name="21018"
      > </a
      ><a name="21019" href="Maps.html#11317" class="Function Operator"
      >&#8614;</a
      ><a name="21020"
      > </a
      ><a name="21021" href="StlcProp.html#20548" class="Bound"
      >A&#8242;</a
      ><a name="21023" class="Symbol"
      >)</a
      ><a name="21024"
      > </a
      ><a name="21025" href="Stlc.html#4116" class="Datatype Operator"
      >&#8866;</a
      ><a name="21026"
      > </a
      ><a name="21027" href="StlcProp.html#20553" class="Bound"
      >N&#8242;</a
      ><a name="21029"
      > </a
      ><a name="21030" href="Stlc.html#1756" class="Function Operator"
      >[</a
      ><a name="21031"
      > </a
      ><a name="21032" href="StlcProp.html#20532" class="Bound"
      >x</a
      ><a name="21033"
      > </a
      ><a name="21034" href="Stlc.html#1756" class="Function Operator"
      >:=</a
      ><a name="21036"
      > </a
      ><a name="21037" href="StlcProp.html#20569" class="Bound"
      >V</a
      ><a name="21038"
      > </a
      ><a name="21039" href="Stlc.html#1756" class="Function Operator"
      >]</a
      ><a name="21040"
      > </a
      ><a name="21041" href="Stlc.html#4116" class="Datatype Operator"
      >&#8712;</a
      ><a name="21042"
      > </a
      ><a name="21043" href="StlcProp.html#20564" class="Bound"
      >B&#8242;</a
      ><a name="21045"
      >
  </a
      ><a name="21048" href="StlcProp.html#21004" class="Function"
      >&#8866;N&#8242;V</a
      ><a name="21052"
      > </a
      ><a name="21053" class="Symbol"
      >=</a
      ><a name="21054"
      > </a
      ><a name="21055" href="StlcProp.html#16366" class="Function"
      >preservation-[:=]</a
      ><a name="21072"
      > </a
      ><a name="21073" href="StlcProp.html#20902" class="Function"
      >x&#8242;x&#8866;N&#8242;</a
      ><a name="21079"
      > </a
      ><a name="21080" href="StlcProp.html#20621" class="Bound"
      >&#8866;V</a
      ><a name="21082"
      >
</a
      ><a name="21083" class="Comment"
      >{-
...| yes x&#8242;&#8801;x rewrite x&#8242;&#8801;x | update-shadow &#915; x A A&#8242;  =  {!!}
  -- &#8658;-I &#8866;N&#8242;
...| no  x&#8242;&#8802;x rewrite update-permute &#915; x&#8242; A&#8242; x A x&#8242;&#8802;x  =  {!!}
  --  &#8658;-I {&#915;} {x&#8242;} {N&#8242;} {A&#8242;} {B&#8242;} (preservation-[:=] {(&#915; , x&#8242; &#8614; A&#8242;)} {x} {A} &#8866;N&#8242; &#8866;V)
-}</a
      ><a name="21310"
      >
</a
      ><a name="21311" href="StlcProp.html#16366" class="Function"
      >preservation-[:=]</a
      ><a name="21328"
      > </a
      ><a name="21329" class="Symbol"
      >(</a
      ><a name="21330" href="Stlc.html#4300" class="InductiveConstructor"
      >&#8658;-E</a
      ><a name="21333"
      > </a
      ><a name="21334" href="StlcProp.html#21334" class="Bound"
      >&#8866;L</a
      ><a name="21336"
      > </a
      ><a name="21337" href="StlcProp.html#21337" class="Bound"
      >&#8866;M</a
      ><a name="21339" class="Symbol"
      >)</a
      ><a name="21340"
      > </a
      ><a name="21341" href="StlcProp.html#21341" class="Bound"
      >&#8866;V</a
      ><a name="21343"
      > </a
      ><a name="21344" class="Symbol"
      >=</a
      ><a name="21345"
      > </a
      ><a name="21346" href="Stlc.html#4300" class="InductiveConstructor"
      >&#8658;-E</a
      ><a name="21349"
      > </a
      ><a name="21350" class="Symbol"
      >(</a
      ><a name="21351" href="StlcProp.html#16366" class="Function"
      >preservation-[:=]</a
      ><a name="21368"
      > </a
      ><a name="21369" href="StlcProp.html#21334" class="Bound"
      >&#8866;L</a
      ><a name="21371"
      > </a
      ><a name="21372" href="StlcProp.html#21341" class="Bound"
      >&#8866;V</a
      ><a name="21374" class="Symbol"
      >)</a
      ><a name="21375"
      > </a
      ><a name="21376" class="Symbol"
      >(</a
      ><a name="21377" href="StlcProp.html#16366" class="Function"
      >preservation-[:=]</a
      ><a name="21394"
      > </a
      ><a name="21395" href="StlcProp.html#21337" class="Bound"
      >&#8866;M</a
      ><a name="21397"
      > </a
      ><a name="21398" href="StlcProp.html#21341" class="Bound"
      >&#8866;V</a
      ><a name="21400" class="Symbol"
      >)</a
      ><a name="21401"
      >
</a
      ><a name="21402" href="StlcProp.html#16366" class="Function"
      >preservation-[:=]</a
      ><a name="21419"
      > </a
      ><a name="21420" href="Stlc.html#4381" class="InductiveConstructor"
      >&#120121;-I&#8321;</a
      ><a name="21424"
      > </a
      ><a name="21425" href="StlcProp.html#21425" class="Bound"
      >&#8866;V</a
      ><a name="21427"
      > </a
      ><a name="21428" class="Symbol"
      >=</a
      ><a name="21429"
      > </a
      ><a name="21430" href="Stlc.html#4381" class="InductiveConstructor"
      >&#120121;-I&#8321;</a
      ><a name="21434"
      >
</a
      ><a name="21435" href="StlcProp.html#16366" class="Function"
      >preservation-[:=]</a
      ><a name="21452"
      > </a
      ><a name="21453" href="Stlc.html#4416" class="InductiveConstructor"
      >&#120121;-I&#8322;</a
      ><a name="21457"
      > </a
      ><a name="21458" href="StlcProp.html#21458" class="Bound"
      >&#8866;V</a
      ><a name="21460"
      > </a
      ><a name="21461" class="Symbol"
      >=</a
      ><a name="21462"
      > </a
      ><a name="21463" href="Stlc.html#4416" class="InductiveConstructor"
      >&#120121;-I&#8322;</a
      ><a name="21467"
      >
</a
      ><a name="21468" href="StlcProp.html#16366" class="Function"
      >preservation-[:=]</a
      ><a name="21485"
      > </a
      ><a name="21486" class="Symbol"
      >(</a
      ><a name="21487" href="Stlc.html#4452" class="InductiveConstructor"
      >&#120121;-E</a
      ><a name="21490"
      > </a
      ><a name="21491" href="StlcProp.html#21491" class="Bound"
      >&#8866;L</a
      ><a name="21493"
      > </a
      ><a name="21494" href="StlcProp.html#21494" class="Bound"
      >&#8866;M</a
      ><a name="21496"
      > </a
      ><a name="21497" href="StlcProp.html#21497" class="Bound"
      >&#8866;N</a
      ><a name="21499" class="Symbol"
      >)</a
      ><a name="21500"
      > </a
      ><a name="21501" href="StlcProp.html#21501" class="Bound"
      >&#8866;V</a
      ><a name="21503"
      > </a
      ><a name="21504" class="Symbol"
      >=</a
      ><a name="21505"
      >
  </a
      ><a name="21508" href="Stlc.html#4452" class="InductiveConstructor"
      >&#120121;-E</a
      ><a name="21511"
      > </a
      ><a name="21512" class="Symbol"
      >(</a
      ><a name="21513" href="StlcProp.html#16366" class="Function"
      >preservation-[:=]</a
      ><a name="21530"
      > </a
      ><a name="21531" href="StlcProp.html#21491" class="Bound"
      >&#8866;L</a
      ><a name="21533"
      > </a
      ><a name="21534" href="StlcProp.html#21501" class="Bound"
      >&#8866;V</a
      ><a name="21536" class="Symbol"
      >)</a
      ><a name="21537"
      > </a
      ><a name="21538" class="Symbol"
      >(</a
      ><a name="21539" href="StlcProp.html#16366" class="Function"
      >preservation-[:=]</a
      ><a name="21556"
      > </a
      ><a name="21557" href="StlcProp.html#21494" class="Bound"
      >&#8866;M</a
      ><a name="21559"
      > </a
      ><a name="21560" href="StlcProp.html#21501" class="Bound"
      >&#8866;V</a
      ><a name="21562" class="Symbol"
      >)</a
      ><a name="21563"
      > </a
      ><a name="21564" class="Symbol"
      >(</a
      ><a name="21565" href="StlcProp.html#16366" class="Function"
      >preservation-[:=]</a
      ><a name="21582"
      > </a
      ><a name="21583" href="StlcProp.html#21497" class="Bound"
      >&#8866;N</a
      ><a name="21585"
      > </a
      ><a name="21586" href="StlcProp.html#21501" class="Bound"
      >&#8866;V</a
      ><a name="21588" class="Symbol"
      >)</a
      ><a name="21589"
      >

</a
      ><a name="21591" class="Comment"
      >{-
[:=]-preserves-&#8866; {&#915;} {x} v&#8758;A (var y y&#8712;&#915;) with x &#8799; y
... | yes x=y = {!!}
... | no  x&#8800;y = {!!}
[:=]-preserves-&#8866; v&#8758;A (abs t&#8242;&#8758;B) = {!!}
[:=]-preserves-&#8866; v&#8758;A (app t&#8321;&#8758;A&#8658;B t&#8322;&#8758;A) =
  app ([:=]-preserves-&#8866; v&#8758;A t&#8321;&#8758;A&#8658;B) ([:=]-preserves-&#8866; v&#8758;A t&#8322;&#8758;A)
[:=]-preserves-&#8866; v&#8758;A true  = true
[:=]-preserves-&#8866; v&#8758;A false = false
[:=]-preserves-&#8866; v&#8758;A (if t&#8321;&#8758;bool then t&#8322;&#8758;B else t&#8323;&#8758;B) =
  if   [:=]-preserves-&#8866; v&#8758;A t&#8321;&#8758;bool
  then [:=]-preserves-&#8866; v&#8758;A t&#8322;&#8758;B
  else [:=]-preserves-&#8866; v&#8758;A t&#8323;&#8758;B
-}</a
      >

</pre>


### Main Theorem

We now have the tools we need to prove preservation: if a closed
term $$M$$ has type $$A$$ and takes a step to $$N$$, then $$N$$
is also a closed term with type $$A$$.  In other words, small-step
reduction preserves types.

<pre class="Agda">

<a name="22330" href="StlcProp.html#22330" class="Function"
      >preservation</a
      ><a name="22342"
      > </a
      ><a name="22343" class="Symbol"
      >:</a
      ><a name="22344"
      > </a
      ><a name="22345" class="Symbol"
      >&#8704;</a
      ><a name="22346"
      > </a
      ><a name="22347" class="Symbol"
      >{</a
      ><a name="22348" href="StlcProp.html#22348" class="Bound"
      >M</a
      ><a name="22349"
      > </a
      ><a name="22350" href="StlcProp.html#22350" class="Bound"
      >N</a
      ><a name="22351"
      > </a
      ><a name="22352" href="StlcProp.html#22352" class="Bound"
      >A</a
      ><a name="22353" class="Symbol"
      >}</a
      ><a name="22354"
      > </a
      ><a name="22355" class="Symbol"
      >&#8594;</a
      ><a name="22356"
      > </a
      ><a name="22357" href="Maps.html#11235" class="Function"
      >&#8709;</a
      ><a name="22358"
      > </a
      ><a name="22359" href="Stlc.html#4116" class="Datatype Operator"
      >&#8866;</a
      ><a name="22360"
      > </a
      ><a name="22361" href="StlcProp.html#22348" class="Bound"
      >M</a
      ><a name="22362"
      > </a
      ><a name="22363" href="Stlc.html#4116" class="Datatype Operator"
      >&#8712;</a
      ><a name="22364"
      > </a
      ><a name="22365" href="StlcProp.html#22352" class="Bound"
      >A</a
      ><a name="22366"
      > </a
      ><a name="22367" class="Symbol"
      >&#8594;</a
      ><a name="22368"
      > </a
      ><a name="22369" href="StlcProp.html#22348" class="Bound"
      >M</a
      ><a name="22370"
      > </a
      ><a name="22371" href="Stlc.html#2241" class="Datatype Operator"
      >&#10233;</a
      ><a name="22372"
      > </a
      ><a name="22373" href="StlcProp.html#22350" class="Bound"
      >N</a
      ><a name="22374"
      > </a
      ><a name="22375" class="Symbol"
      >&#8594;</a
      ><a name="22376"
      > </a
      ><a name="22377" href="Maps.html#11235" class="Function"
      >&#8709;</a
      ><a name="22378"
      > </a
      ><a name="22379" href="Stlc.html#4116" class="Datatype Operator"
      >&#8866;</a
      ><a name="22380"
      > </a
      ><a name="22381" href="StlcProp.html#22350" class="Bound"
      >N</a
      ><a name="22382"
      > </a
      ><a name="22383" href="Stlc.html#4116" class="Datatype Operator"
      >&#8712;</a
      ><a name="22384"
      > </a
      ><a name="22385" href="StlcProp.html#22352" class="Bound"
      >A</a
      >

</pre>

_Proof_: By induction on the derivation of $$\vdash t : T$$.

- We can immediately rule out $$var$$, $$abs$$, $$T_True$$, and
  $$T_False$$ as the final rules in the derivation, since in each of
  these cases $$t$$ cannot take a step.

- If the last rule in the derivation was $$app$$, then $$t = t_1
  t_2$$.  There are three cases to consider, one for each rule that
  could have been used to show that $$t_1 t_2$$ takes a step to $$t'$$.

    - If $$t_1 t_2$$ takes a step by $$Sapp1$$, with $$t_1$$ stepping to
      $$t_1'$$, then by the IH $$t_1'$$ has the same type as $$t_1$$, and
      hence $$t_1' t_2$$ has the same type as $$t_1 t_2$$.

    - The $$Sapp2$$ case is similar.

    - If $$t_1 t_2$$ takes a step by $$Sred$$, then $$t_1 =
      \lambda x:t_{11}.t_{12}$$ and $$t_1 t_2$$ steps to $$$$x:=t_2$$t_{12}$$; the
      desired result now follows from the fact that substitution
      preserves types.

    - If the last rule in the derivation was $$if$$, then $$t = if t_1
      then t_2 else t_3$$, and there are again three cases depending on
      how $$t$$ steps.

    - If $$t$$ steps to $$t_2$$ or $$t_3$$, the result is immediate, since
      $$t_2$$ and $$t_3$$ have the same type as $$t$$.

    - Otherwise, $$t$$ steps by $$Sif$$, and the desired conclusion
      follows directly from the induction hypothesis.

<pre class="Agda">

<a name="23752" href="StlcProp.html#22330" class="Function"
      >preservation</a
      ><a name="23764"
      > </a
      ><a name="23765" class="Symbol"
      >(</a
      ><a name="23766" href="Stlc.html#4160" class="InductiveConstructor"
      >Ax</a
      ><a name="23768"
      > </a
      ><a name="23769" href="StlcProp.html#23769" class="Bound"
      >x&#8321;</a
      ><a name="23771" class="Symbol"
      >)</a
      ><a name="23772"
      > </a
      ><a name="23773" class="Symbol"
      >()</a
      ><a name="23775"
      >
</a
      ><a name="23776" href="StlcProp.html#22330" class="Function"
      >preservation</a
      ><a name="23788"
      > </a
      ><a name="23789" class="Symbol"
      >(</a
      ><a name="23790" href="Stlc.html#4217" class="InductiveConstructor"
      >&#8658;-I</a
      ><a name="23793"
      > </a
      ><a name="23794" href="StlcProp.html#23794" class="Bound"
      >&#8866;N</a
      ><a name="23796" class="Symbol"
      >)</a
      ><a name="23797"
      > </a
      ><a name="23798" class="Symbol"
      >()</a
      ><a name="23800"
      >
</a
      ><a name="23801" href="StlcProp.html#22330" class="Function"
      >preservation</a
      ><a name="23813"
      > </a
      ><a name="23814" class="Symbol"
      >(</a
      ><a name="23815" href="Stlc.html#4300" class="InductiveConstructor"
      >&#8658;-E</a
      ><a name="23818"
      > </a
      ><a name="23819" class="Symbol"
      >(</a
      ><a name="23820" href="Stlc.html#4217" class="InductiveConstructor"
      >&#8658;-I</a
      ><a name="23823"
      > </a
      ><a name="23824" href="StlcProp.html#23824" class="Bound"
      >&#8866;N</a
      ><a name="23826" class="Symbol"
      >)</a
      ><a name="23827"
      > </a
      ><a name="23828" href="StlcProp.html#23828" class="Bound"
      >&#8866;V</a
      ><a name="23830" class="Symbol"
      >)</a
      ><a name="23831"
      > </a
      ><a name="23832" class="Symbol"
      >(</a
      ><a name="23833" href="Stlc.html#2273" class="InductiveConstructor"
      >&#946;&#8658;</a
      ><a name="23835"
      > </a
      ><a name="23836" href="StlcProp.html#23836" class="Bound"
      >valueV</a
      ><a name="23842" class="Symbol"
      >)</a
      ><a name="23843"
      > </a
      ><a name="23844" class="Symbol"
      >=</a
      ><a name="23845"
      > </a
      ><a name="23846" href="StlcProp.html#16366" class="Function"
      >preservation-[:=]</a
      ><a name="23863"
      > </a
      ><a name="23864" href="StlcProp.html#23824" class="Bound"
      >&#8866;N</a
      ><a name="23866"
      > </a
      ><a name="23867" href="StlcProp.html#23828" class="Bound"
      >&#8866;V</a
      ><a name="23869"
      >
</a
      ><a name="23870" href="StlcProp.html#22330" class="Function"
      >preservation</a
      ><a name="23882"
      > </a
      ><a name="23883" class="Symbol"
      >(</a
      ><a name="23884" href="Stlc.html#4300" class="InductiveConstructor"
      >&#8658;-E</a
      ><a name="23887"
      > </a
      ><a name="23888" href="StlcProp.html#23888" class="Bound"
      >&#8866;L</a
      ><a name="23890"
      > </a
      ><a name="23891" href="StlcProp.html#23891" class="Bound"
      >&#8866;M</a
      ><a name="23893" class="Symbol"
      >)</a
      ><a name="23894"
      > </a
      ><a name="23895" class="Symbol"
      >(</a
      ><a name="23896" href="Stlc.html#2347" class="InductiveConstructor"
      >&#947;&#8658;&#8321;</a
      ><a name="23899"
      > </a
      ><a name="23900" href="StlcProp.html#23900" class="Bound"
      >L&#10233;L&#8242;</a
      ><a name="23904" class="Symbol"
      >)</a
      ><a name="23905"
      > </a
      ><a name="23906" class="Keyword"
      >with</a
      ><a name="23910"
      > </a
      ><a name="23911" href="StlcProp.html#22330" class="Function"
      >preservation</a
      ><a name="23923"
      > </a
      ><a name="23924" href="StlcProp.html#23888" class="Bound"
      >&#8866;L</a
      ><a name="23926"
      > </a
      ><a name="23927" href="StlcProp.html#23900" class="Bound"
      >L&#10233;L&#8242;</a
      ><a name="23931"
      >
</a
      ><a name="23932" class="Symbol"
      >...|</a
      ><a name="23936"
      > </a
      ><a name="23937" href="StlcProp.html#23937" class="Bound"
      >&#8866;L&#8242;</a
      ><a name="23940"
      > </a
      ><a name="23941" class="Symbol"
      >=</a
      ><a name="23942"
      > </a
      ><a name="23943" href="Stlc.html#4300" class="InductiveConstructor"
      >&#8658;-E</a
      ><a name="23946"
      > </a
      ><a name="23947" href="StlcProp.html#23937" class="Bound"
      >&#8866;L&#8242;</a
      ><a name="23950"
      > </a
      ><a name="23951" href="StlcProp.html#23891" class="Bound"
      >&#8866;M</a
      ><a name="23953"
      >
</a
      ><a name="23954" href="StlcProp.html#22330" class="Function"
      >preservation</a
      ><a name="23966"
      > </a
      ><a name="23967" class="Symbol"
      >(</a
      ><a name="23968" href="Stlc.html#4300" class="InductiveConstructor"
      >&#8658;-E</a
      ><a name="23971"
      > </a
      ><a name="23972" href="StlcProp.html#23972" class="Bound"
      >&#8866;L</a
      ><a name="23974"
      > </a
      ><a name="23975" href="StlcProp.html#23975" class="Bound"
      >&#8866;M</a
      ><a name="23977" class="Symbol"
      >)</a
      ><a name="23978"
      > </a
      ><a name="23979" class="Symbol"
      >(</a
      ><a name="23980" href="Stlc.html#2406" class="InductiveConstructor"
      >&#947;&#8658;&#8322;</a
      ><a name="23983"
      > </a
      ><a name="23984" href="StlcProp.html#23984" class="Bound"
      >valueL</a
      ><a name="23990"
      > </a
      ><a name="23991" href="StlcProp.html#23991" class="Bound"
      >M&#10233;M&#8242;</a
      ><a name="23995" class="Symbol"
      >)</a
      ><a name="23996"
      > </a
      ><a name="23997" class="Keyword"
      >with</a
      ><a name="24001"
      > </a
      ><a name="24002" href="StlcProp.html#22330" class="Function"
      >preservation</a
      ><a name="24014"
      > </a
      ><a name="24015" href="StlcProp.html#23975" class="Bound"
      >&#8866;M</a
      ><a name="24017"
      > </a
      ><a name="24018" href="StlcProp.html#23991" class="Bound"
      >M&#10233;M&#8242;</a
      ><a name="24022"
      >
</a
      ><a name="24023" class="Symbol"
      >...|</a
      ><a name="24027"
      > </a
      ><a name="24028" href="StlcProp.html#24028" class="Bound"
      >&#8866;M&#8242;</a
      ><a name="24031"
      > </a
      ><a name="24032" class="Symbol"
      >=</a
      ><a name="24033"
      > </a
      ><a name="24034" href="Stlc.html#4300" class="InductiveConstructor"
      >&#8658;-E</a
      ><a name="24037"
      > </a
      ><a name="24038" href="StlcProp.html#23972" class="Bound"
      >&#8866;L</a
      ><a name="24040"
      > </a
      ><a name="24041" href="StlcProp.html#24028" class="Bound"
      >&#8866;M&#8242;</a
      ><a name="24044"
      >
</a
      ><a name="24045" href="StlcProp.html#22330" class="Function"
      >preservation</a
      ><a name="24057"
      > </a
      ><a name="24058" href="Stlc.html#4381" class="InductiveConstructor"
      >&#120121;-I&#8321;</a
      ><a name="24062"
      > </a
      ><a name="24063" class="Symbol"
      >()</a
      ><a name="24065"
      >
</a
      ><a name="24066" href="StlcProp.html#22330" class="Function"
      >preservation</a
      ><a name="24078"
      > </a
      ><a name="24079" href="Stlc.html#4416" class="InductiveConstructor"
      >&#120121;-I&#8322;</a
      ><a name="24083"
      > </a
      ><a name="24084" class="Symbol"
      >()</a
      ><a name="24086"
      >
</a
      ><a name="24087" href="StlcProp.html#22330" class="Function"
      >preservation</a
      ><a name="24099"
      > </a
      ><a name="24100" class="Symbol"
      >(</a
      ><a name="24101" href="Stlc.html#4452" class="InductiveConstructor"
      >&#120121;-E</a
      ><a name="24104"
      > </a
      ><a name="24105" href="Stlc.html#4381" class="InductiveConstructor"
      >&#120121;-I&#8321;</a
      ><a name="24109"
      > </a
      ><a name="24110" href="StlcProp.html#24110" class="Bound"
      >&#8866;M</a
      ><a name="24112"
      > </a
      ><a name="24113" href="StlcProp.html#24113" class="Bound"
      >&#8866;N</a
      ><a name="24115" class="Symbol"
      >)</a
      ><a name="24116"
      > </a
      ><a name="24117" href="Stlc.html#2479" class="InductiveConstructor"
      >&#946;&#120121;&#8321;</a
      ><a name="24120"
      > </a
      ><a name="24121" class="Symbol"
      >=</a
      ><a name="24122"
      > </a
      ><a name="24123" href="StlcProp.html#24110" class="Bound"
      >&#8866;M</a
      ><a name="24125"
      >
</a
      ><a name="24126" href="StlcProp.html#22330" class="Function"
      >preservation</a
      ><a name="24138"
      > </a
      ><a name="24139" class="Symbol"
      >(</a
      ><a name="24140" href="Stlc.html#4452" class="InductiveConstructor"
      >&#120121;-E</a
      ><a name="24143"
      > </a
      ><a name="24144" href="Stlc.html#4416" class="InductiveConstructor"
      >&#120121;-I&#8322;</a
      ><a name="24148"
      > </a
      ><a name="24149" href="StlcProp.html#24149" class="Bound"
      >&#8866;M</a
      ><a name="24151"
      > </a
      ><a name="24152" href="StlcProp.html#24152" class="Bound"
      >&#8866;N</a
      ><a name="24154" class="Symbol"
      >)</a
      ><a name="24155"
      > </a
      ><a name="24156" href="Stlc.html#2531" class="InductiveConstructor"
      >&#946;&#120121;&#8322;</a
      ><a name="24159"
      > </a
      ><a name="24160" class="Symbol"
      >=</a
      ><a name="24161"
      > </a
      ><a name="24162" href="StlcProp.html#24152" class="Bound"
      >&#8866;N</a
      ><a name="24164"
      >
</a
      ><a name="24165" href="StlcProp.html#22330" class="Function"
      >preservation</a
      ><a name="24177"
      > </a
      ><a name="24178" class="Symbol"
      >(</a
      ><a name="24179" href="Stlc.html#4452" class="InductiveConstructor"
      >&#120121;-E</a
      ><a name="24182"
      > </a
      ><a name="24183" href="StlcProp.html#24183" class="Bound"
      >&#8866;L</a
      ><a name="24185"
      > </a
      ><a name="24186" href="StlcProp.html#24186" class="Bound"
      >&#8866;M</a
      ><a name="24188"
      > </a
      ><a name="24189" href="StlcProp.html#24189" class="Bound"
      >&#8866;N</a
      ><a name="24191" class="Symbol"
      >)</a
      ><a name="24192"
      > </a
      ><a name="24193" class="Symbol"
      >(</a
      ><a name="24194" href="Stlc.html#2584" class="InductiveConstructor"
      >&#947;&#120121;</a
      ><a name="24196"
      > </a
      ><a name="24197" href="StlcProp.html#24197" class="Bound"
      >L&#10233;L&#8242;</a
      ><a name="24201" class="Symbol"
      >)</a
      ><a name="24202"
      > </a
      ><a name="24203" class="Keyword"
      >with</a
      ><a name="24207"
      > </a
      ><a name="24208" href="StlcProp.html#22330" class="Function"
      >preservation</a
      ><a name="24220"
      > </a
      ><a name="24221" href="StlcProp.html#24183" class="Bound"
      >&#8866;L</a
      ><a name="24223"
      > </a
      ><a name="24224" href="StlcProp.html#24197" class="Bound"
      >L&#10233;L&#8242;</a
      ><a name="24228"
      >
</a
      ><a name="24229" class="Symbol"
      >...|</a
      ><a name="24233"
      > </a
      ><a name="24234" href="StlcProp.html#24234" class="Bound"
      >&#8866;L&#8242;</a
      ><a name="24237"
      > </a
      ><a name="24238" class="Symbol"
      >=</a
      ><a name="24239"
      > </a
      ><a name="24240" href="Stlc.html#4452" class="InductiveConstructor"
      >&#120121;-E</a
      ><a name="24243"
      > </a
      ><a name="24244" href="StlcProp.html#24234" class="Bound"
      >&#8866;L&#8242;</a
      ><a name="24247"
      > </a
      ><a name="24248" href="StlcProp.html#24186" class="Bound"
      >&#8866;M</a
      ><a name="24250"
      > </a
      ><a name="24251" href="StlcProp.html#24189" class="Bound"
      >&#8866;N</a
      ><a name="24253"
      >

</a
      ><a name="24255" class="Comment"
      >-- Writing out implicit parameters in full</a
      ><a name="24297"
      >
</a
      ><a name="24298" class="Comment"
      >-- preservation (&#8658;-E {&#915;} {&#955;&#7488; x &#8712; A &#8658; N} {M} {.A} {B} (&#8658;-I {.&#915;} {.x} {.N} {.A} {.B} &#8866;N) &#8866;M) (&#946;&#8658; {.x} {.A} {.N} {.M} valueM)</a
      ><a name="24420"
      >
</a
      ><a name="24421" class="Comment"
      >--  =  preservation-[:=] {&#915;} {x} {A} {M} {N} {B} &#8866;M &#8866;N</a
      >

</pre>

Proof with eauto.
  remember (@empty ty) as Gamma.
  intros t t' T HT. generalize dependent t'.
  induction HT;
       intros t' HE; subst Gamma; subst;
       try solve $$inversion HE; subst; auto$$.
  - (* app
    inversion HE; subst...
    (* Most of the cases are immediate by induction,
       and $$eauto$$ takes care of them
    + (* Sred
      apply substitution_preserves_typing with t_{11}...
      inversion HT_1...
Qed.

#### Exercise: 2 stars, recommended (subject_expansion_stlc)
An exercise in the [Stlc]({{ "Stlc" | relative_url }}) chapter asked about the
subject expansion property for the simple language of arithmetic and boolean
expressions.  Does this property hold for STLC?  That is, is it always the case
that, if $$t ==> t'$$ and $$has_type t' T$$, then $$empty \vdash t : T$$?  If
so, prove it.  If not, give a counter-example not involving conditionals. 


## Type Soundness

#### Exercise: 2 stars, optional (type_soundness)
Put progress and preservation together and show that a well-typed
term can _never_ reach a stuck state.

Definition stuck (t:tm) : Prop :=
  (normal_form step) t /\ ~ value t.

Corollary soundness : forall t t' T,
  empty \vdash t : T →
  t ==>* t' →
  ~(stuck t').
Proof.
  intros t t' T Hhas_type Hmulti. unfold stuck.
  intros $$Hnf Hnot_val$$. unfold normal_form in Hnf.
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
$$$$

#### Exercise: 2 stars (stlc_variation1)
Suppose we add a new term $$zap$$ with the following reduction rule

                     ---------                  (ST_Zap)
                     t ==> zap

and the following typing rule:

                  ----------------               (T_Zap)
                  Gamma \vdash zap : T

Which of the following properties of the STLC remain true in
the presence of these rules?  For each property, write either
"remains true" or "becomes false." If a property becomes
false, give a counterexample.

  - Determinism of $$step$$

  - Progress

  - Preservation


#### Exercise: 2 stars (stlc_variation2)
Suppose instead that we add a new term $$foo$$ with the following
reduction rules:

                   -----------------                (ST_Foo1)
                   (\lambda x:A. x) ==> foo

                     ------------                   (ST_Foo2)
                     foo ==> true

Which of the following properties of the STLC remain true in
the presence of this rule?  For each one, write either
"remains true" or else "becomes false." If a property becomes
false, give a counterexample.

  - Determinism of $$step$$

  - Progress

  - Preservation

#### Exercise: 2 stars (stlc_variation3)
Suppose instead that we remove the rule $$Sapp1$$ from the $$step$$
relation. Which of the following properties of the STLC remain
true in the presence of this rule?  For each one, write either
"remains true" or else "becomes false." If a property becomes
false, give a counterexample.

  - Determinism of $$step$$

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

  - Determinism of $$step$$

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

  - Determinism of $$step$$

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

  - Determinism of $$step$$

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

  - Determinism of $$step$$

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

  - Extend the definitions of the $$subst$$ operation and the $$step$$
     relation to include appropriate clauses for the arithmetic operators.

  - Extend the proofs of all the properties (up to $$soundness$$) of
    the original STLC to deal with the new syntactic forms.  Make
    sure Agda accepts the whole file.

