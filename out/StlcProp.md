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
      ><a name="171" href="https://agda.github.io/agda-stdlib/Data.Empty.html#348" class="Function"
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
      ><a name="314" href="https://agda.github.io/agda-stdlib/Data.Product.html#949" class="Function"
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
      ><a name="323" href="https://agda.github.io/agda-stdlib/Data.Product.html#1621" class="Function Operator"
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
      ><a name="538" href="Maps.html#10316" class="Module"
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
belonging to each type.  For `bool`, these are the boolean values `true` and
`false`.  For arrow types, the canonical forms are lambda-abstractions. 

<pre class="Agda">

<a name="1129" class="Keyword"
      >data</a
      ><a name="1133"
      > </a
      ><a name="1134" href="StlcProp.html#1134" class="Datatype Operator"
      >canonical_for_</a
      ><a name="1148"
      > </a
      ><a name="1149" class="Symbol"
      >:</a
      ><a name="1150"
      > </a
      ><a name="1151" href="Stlc.html#1032" class="Datatype"
      >Term</a
      ><a name="1155"
      > </a
      ><a name="1156" class="Symbol"
      >&#8594;</a
      ><a name="1157"
      > </a
      ><a name="1158" href="Stlc.html#971" class="Datatype"
      >Type</a
      ><a name="1162"
      > </a
      ><a name="1163" class="Symbol"
      >&#8594;</a
      ><a name="1164"
      > </a
      ><a name="1165" class="PrimitiveType"
      >Set</a
      ><a name="1168"
      > </a
      ><a name="1169" class="Keyword"
      >where</a
      ><a name="1174"
      >
  </a
      ><a name="1177" href="StlcProp.html#1177" class="InductiveConstructor"
      >canonical-&#955;&#7488;</a
      ><a name="1189"
      > </a
      ><a name="1190" class="Symbol"
      >:</a
      ><a name="1191"
      > </a
      ><a name="1192" class="Symbol"
      >&#8704;</a
      ><a name="1193"
      > </a
      ><a name="1194" class="Symbol"
      >{</a
      ><a name="1195" href="StlcProp.html#1195" class="Bound"
      >x</a
      ><a name="1196"
      > </a
      ><a name="1197" href="StlcProp.html#1197" class="Bound"
      >A</a
      ><a name="1198"
      > </a
      ><a name="1199" href="StlcProp.html#1199" class="Bound"
      >N</a
      ><a name="1200"
      > </a
      ><a name="1201" href="StlcProp.html#1201" class="Bound"
      >B</a
      ><a name="1202" class="Symbol"
      >}</a
      ><a name="1203"
      > </a
      ><a name="1204" class="Symbol"
      >&#8594;</a
      ><a name="1205"
      > </a
      ><a name="1206" href="StlcProp.html#1134" class="Datatype Operator"
      >canonical</a
      ><a name="1215"
      > </a
      ><a name="1216" class="Symbol"
      >(</a
      ><a name="1217" href="Stlc.html#1070" class="InductiveConstructor Operator"
      >&#955;&#7488;</a
      ><a name="1219"
      > </a
      ><a name="1220" href="StlcProp.html#1195" class="Bound"
      >x</a
      ><a name="1221"
      > </a
      ><a name="1222" href="Stlc.html#1070" class="InductiveConstructor Operator"
      >&#8712;</a
      ><a name="1223"
      > </a
      ><a name="1224" href="StlcProp.html#1197" class="Bound"
      >A</a
      ><a name="1225"
      > </a
      ><a name="1226" href="Stlc.html#1070" class="InductiveConstructor Operator"
      >&#8658;</a
      ><a name="1227"
      > </a
      ><a name="1228" href="StlcProp.html#1199" class="Bound"
      >N</a
      ><a name="1229" class="Symbol"
      >)</a
      ><a name="1230"
      > </a
      ><a name="1231" href="StlcProp.html#1134" class="Datatype Operator"
      >for</a
      ><a name="1234"
      > </a
      ><a name="1235" class="Symbol"
      >(</a
      ><a name="1236" href="StlcProp.html#1197" class="Bound"
      >A</a
      ><a name="1237"
      > </a
      ><a name="1238" href="Stlc.html#1001" class="InductiveConstructor Operator"
      >&#8658;</a
      ><a name="1239"
      > </a
      ><a name="1240" href="StlcProp.html#1201" class="Bound"
      >B</a
      ><a name="1241" class="Symbol"
      >)</a
      ><a name="1242"
      >
  </a
      ><a name="1245" href="StlcProp.html#1245" class="InductiveConstructor"
      >canonical-true&#7488;</a
      ><a name="1260"
      > </a
      ><a name="1261" class="Symbol"
      >:</a
      ><a name="1262"
      > </a
      ><a name="1263" href="StlcProp.html#1134" class="Datatype Operator"
      >canonical</a
      ><a name="1272"
      > </a
      ><a name="1273" href="Stlc.html#1134" class="InductiveConstructor"
      >true&#7488;</a
      ><a name="1278"
      > </a
      ><a name="1279" href="StlcProp.html#1134" class="Datatype Operator"
      >for</a
      ><a name="1282"
      > </a
      ><a name="1283" href="Stlc.html#990" class="InductiveConstructor"
      >&#120121;</a
      ><a name="1284"
      >
  </a
      ><a name="1287" href="StlcProp.html#1287" class="InductiveConstructor"
      >canonical-false&#7488;</a
      ><a name="1303"
      > </a
      ><a name="1304" class="Symbol"
      >:</a
      ><a name="1305"
      > </a
      ><a name="1306" href="StlcProp.html#1134" class="Datatype Operator"
      >canonical</a
      ><a name="1315"
      > </a
      ><a name="1316" href="Stlc.html#1149" class="InductiveConstructor"
      >false&#7488;</a
      ><a name="1322"
      > </a
      ><a name="1323" href="StlcProp.html#1134" class="Datatype Operator"
      >for</a
      ><a name="1326"
      > </a
      ><a name="1327" href="Stlc.html#990" class="InductiveConstructor"
      >&#120121;</a
      ><a name="1328"
      >
  
</a
      ><a name="1332" class="Comment"
      >-- canonical_for_ : Term &#8594; Type &#8594; Set</a
      ><a name="1369"
      >
</a
      ><a name="1370" class="Comment"
      >-- canonical L for &#120121;       = L &#8801; true&#7488; &#8846; L &#8801; false&#7488;</a
      ><a name="1421"
      >
</a
      ><a name="1422" class="Comment"
      >-- canonical L for (A &#8658; B) = &#8707;&#8322; &#955; x N &#8594; L &#8801; &#955;&#7488; x &#8712; A &#8658; N</a
      ><a name="1478"
      >

</a
      ><a name="1480" href="StlcProp.html#1480" class="Function"
      >canonicalFormsLemma</a
      ><a name="1499"
      > </a
      ><a name="1500" class="Symbol"
      >:</a
      ><a name="1501"
      > </a
      ><a name="1502" class="Symbol"
      >&#8704;</a
      ><a name="1503"
      > </a
      ><a name="1504" class="Symbol"
      >{</a
      ><a name="1505" href="StlcProp.html#1505" class="Bound"
      >L</a
      ><a name="1506"
      > </a
      ><a name="1507" href="StlcProp.html#1507" class="Bound"
      >A</a
      ><a name="1508" class="Symbol"
      >}</a
      ><a name="1509"
      > </a
      ><a name="1510" class="Symbol"
      >&#8594;</a
      ><a name="1511"
      > </a
      ><a name="1512" href="Maps.html#10360" class="Function"
      >&#8709;</a
      ><a name="1513"
      > </a
      ><a name="1514" href="Stlc.html#4132" class="Datatype Operator"
      >&#8866;</a
      ><a name="1515"
      > </a
      ><a name="1516" href="StlcProp.html#1505" class="Bound"
      >L</a
      ><a name="1517"
      > </a
      ><a name="1518" href="Stlc.html#4132" class="Datatype Operator"
      >&#8712;</a
      ><a name="1519"
      > </a
      ><a name="1520" href="StlcProp.html#1507" class="Bound"
      >A</a
      ><a name="1521"
      > </a
      ><a name="1522" class="Symbol"
      >&#8594;</a
      ><a name="1523"
      > </a
      ><a name="1524" href="Stlc.html#1581" class="Datatype"
      >value</a
      ><a name="1529"
      > </a
      ><a name="1530" href="StlcProp.html#1505" class="Bound"
      >L</a
      ><a name="1531"
      > </a
      ><a name="1532" class="Symbol"
      >&#8594;</a
      ><a name="1533"
      > </a
      ><a name="1534" href="StlcProp.html#1134" class="Datatype Operator"
      >canonical</a
      ><a name="1543"
      > </a
      ><a name="1544" href="StlcProp.html#1505" class="Bound"
      >L</a
      ><a name="1545"
      > </a
      ><a name="1546" href="StlcProp.html#1134" class="Datatype Operator"
      >for</a
      ><a name="1549"
      > </a
      ><a name="1550" href="StlcProp.html#1507" class="Bound"
      >A</a
      ><a name="1551"
      >
</a
      ><a name="1552" href="StlcProp.html#1480" class="Function"
      >canonicalFormsLemma</a
      ><a name="1571"
      > </a
      ><a name="1572" class="Symbol"
      >(</a
      ><a name="1573" href="Stlc.html#4176" class="InductiveConstructor"
      >Ax</a
      ><a name="1575"
      > </a
      ><a name="1576" href="StlcProp.html#1576" class="Bound"
      >&#8866;x</a
      ><a name="1578" class="Symbol"
      >)</a
      ><a name="1579"
      > </a
      ><a name="1580" class="Symbol"
      >()</a
      ><a name="1582"
      >
</a
      ><a name="1583" href="StlcProp.html#1480" class="Function"
      >canonicalFormsLemma</a
      ><a name="1602"
      > </a
      ><a name="1603" class="Symbol"
      >(</a
      ><a name="1604" href="Stlc.html#4233" class="InductiveConstructor"
      >&#8658;-I</a
      ><a name="1607"
      > </a
      ><a name="1608" href="StlcProp.html#1608" class="Bound"
      >&#8866;N</a
      ><a name="1610" class="Symbol"
      >)</a
      ><a name="1611"
      > </a
      ><a name="1612" href="Stlc.html#1608" class="InductiveConstructor"
      >value-&#955;&#7488;</a
      ><a name="1620"
      > </a
      ><a name="1621" class="Symbol"
      >=</a
      ><a name="1622"
      > </a
      ><a name="1623" href="StlcProp.html#1177" class="InductiveConstructor"
      >canonical-&#955;&#7488;</a
      ><a name="1635"
      >      </a
      ><a name="1641" class="Comment"
      >-- _ , _ , refl</a
      ><a name="1656"
      >
</a
      ><a name="1657" href="StlcProp.html#1480" class="Function"
      >canonicalFormsLemma</a
      ><a name="1676"
      > </a
      ><a name="1677" class="Symbol"
      >(</a
      ><a name="1678" href="Stlc.html#4316" class="InductiveConstructor"
      >&#8658;-E</a
      ><a name="1681"
      > </a
      ><a name="1682" href="StlcProp.html#1682" class="Bound"
      >&#8866;L</a
      ><a name="1684"
      > </a
      ><a name="1685" href="StlcProp.html#1685" class="Bound"
      >&#8866;M</a
      ><a name="1687" class="Symbol"
      >)</a
      ><a name="1688"
      > </a
      ><a name="1689" class="Symbol"
      >()</a
      ><a name="1691"
      >
</a
      ><a name="1692" href="StlcProp.html#1480" class="Function"
      >canonicalFormsLemma</a
      ><a name="1711"
      > </a
      ><a name="1712" href="Stlc.html#4397" class="InductiveConstructor"
      >&#120121;-I&#8321;</a
      ><a name="1716"
      > </a
      ><a name="1717" href="Stlc.html#1654" class="InductiveConstructor"
      >value-true&#7488;</a
      ><a name="1728"
      > </a
      ><a name="1729" class="Symbol"
      >=</a
      ><a name="1730"
      > </a
      ><a name="1731" href="StlcProp.html#1245" class="InductiveConstructor"
      >canonical-true&#7488;</a
      ><a name="1746"
      >    </a
      ><a name="1750" class="Comment"
      >-- inj&#8321; refl</a
      ><a name="1762"
      >
</a
      ><a name="1763" href="StlcProp.html#1480" class="Function"
      >canonicalFormsLemma</a
      ><a name="1782"
      > </a
      ><a name="1783" href="Stlc.html#4432" class="InductiveConstructor"
      >&#120121;-I&#8322;</a
      ><a name="1787"
      > </a
      ><a name="1788" href="Stlc.html#1684" class="InductiveConstructor"
      >value-false&#7488;</a
      ><a name="1800"
      > </a
      ><a name="1801" class="Symbol"
      >=</a
      ><a name="1802"
      > </a
      ><a name="1803" href="StlcProp.html#1287" class="InductiveConstructor"
      >canonical-false&#7488;</a
      ><a name="1819"
      >  </a
      ><a name="1821" class="Comment"
      >-- inj&#8322; refl</a
      ><a name="1833"
      >
</a
      ><a name="1834" href="StlcProp.html#1480" class="Function"
      >canonicalFormsLemma</a
      ><a name="1853"
      > </a
      ><a name="1854" class="Symbol"
      >(</a
      ><a name="1855" href="Stlc.html#4468" class="InductiveConstructor"
      >&#120121;-E</a
      ><a name="1858"
      > </a
      ><a name="1859" href="StlcProp.html#1859" class="Bound"
      >&#8866;L</a
      ><a name="1861"
      > </a
      ><a name="1862" href="StlcProp.html#1862" class="Bound"
      >&#8866;M</a
      ><a name="1864"
      > </a
      ><a name="1865" href="StlcProp.html#1865" class="Bound"
      >&#8866;N</a
      ><a name="1867" class="Symbol"
      >)</a
      ><a name="1868"
      > </a
      ><a name="1869" class="Symbol"
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

<a name="2268" href="StlcProp.html#2268" class="Function"
      >progress</a
      ><a name="2276"
      > </a
      ><a name="2277" class="Symbol"
      >:</a
      ><a name="2278"
      > </a
      ><a name="2279" class="Symbol"
      >&#8704;</a
      ><a name="2280"
      > </a
      ><a name="2281" class="Symbol"
      >{</a
      ><a name="2282" href="StlcProp.html#2282" class="Bound"
      >M</a
      ><a name="2283"
      > </a
      ><a name="2284" href="StlcProp.html#2284" class="Bound"
      >A</a
      ><a name="2285" class="Symbol"
      >}</a
      ><a name="2286"
      > </a
      ><a name="2287" class="Symbol"
      >&#8594;</a
      ><a name="2288"
      > </a
      ><a name="2289" href="Maps.html#10360" class="Function"
      >&#8709;</a
      ><a name="2290"
      > </a
      ><a name="2291" href="Stlc.html#4132" class="Datatype Operator"
      >&#8866;</a
      ><a name="2292"
      > </a
      ><a name="2293" href="StlcProp.html#2282" class="Bound"
      >M</a
      ><a name="2294"
      > </a
      ><a name="2295" href="Stlc.html#4132" class="Datatype Operator"
      >&#8712;</a
      ><a name="2296"
      > </a
      ><a name="2297" href="StlcProp.html#2284" class="Bound"
      >A</a
      ><a name="2298"
      > </a
      ><a name="2299" class="Symbol"
      >&#8594;</a
      ><a name="2300"
      > </a
      ><a name="2301" href="Stlc.html#1581" class="Datatype"
      >value</a
      ><a name="2306"
      > </a
      ><a name="2307" href="StlcProp.html#2282" class="Bound"
      >M</a
      ><a name="2308"
      > </a
      ><a name="2309" href="https://agda.github.io/agda-stdlib/Data.Sum.html#433" class="Datatype Operator"
      >&#8846;</a
      ><a name="2310"
      > </a
      ><a name="2311" href="https://agda.github.io/agda-stdlib/Data.Product.html#823" class="Function"
      >&#8707;</a
      ><a name="2312"
      > </a
      ><a name="2313" class="Symbol"
      >&#955;</a
      ><a name="2314"
      > </a
      ><a name="2315" href="StlcProp.html#2315" class="Bound"
      >N</a
      ><a name="2316"
      > </a
      ><a name="2317" class="Symbol"
      >&#8594;</a
      ><a name="2318"
      > </a
      ><a name="2319" href="StlcProp.html#2282" class="Bound"
      >M</a
      ><a name="2320"
      > </a
      ><a name="2321" href="Stlc.html#2241" class="Datatype Operator"
      >&#10233;</a
      ><a name="2322"
      > </a
      ><a name="2323" href="StlcProp.html#2315" class="Bound"
      >N</a
      >

</pre>

_Proof_: By induction on the derivation of `\vdash t : A`.

  - The last rule of the derivation cannot be `var`,
    since a variable is never well typed in an empty context.

  - The `true`, `false`, and `abs` cases are trivial, since in
    each of these cases we can see by inspecting the rule that `t`
    is a value.

  - If the last rule of the derivation is `app`, then `t` has the
    form `t_1\;t_2` for som e`t_1` and `t_2`, where we know that
    `t_1` and `t_2` are also well typed in the empty context; in particular,
    there exists a type `B` such that `\vdash t_1 : A\to T` and
    `\vdash t_2 : B`.  By the induction hypothesis, either `t_1` is a
    value or it can take a reduction step.

  - If `t_1` is a value, then consider `t_2`, which by the other
    induction hypothesis must also either be a value or take a step.

    - Suppose `t_2` is a value.  Since `t_1` is a value with an
      arrow type, it must be a lambda abstraction; hence `t_1\;t_2`
      can take a step by `red`.

    - Otherwise, `t_2` can take a step, and hence so can `t_1\;t_2`
      by `app2`.

  - If `t_1` can take a step, then so can `t_1 t_2` by `app1`.

  - If the last rule of the derivation is `if`, then `t = \text{if }t_1
    \text{ then }t_2\text{ else }t_3`, where `t_1` has type `bool`.  By
    the IH, `t_1` either is a value or takes a step.

  - If `t_1` is a value, then since it has type `bool` it must be
    either `true` or `false`.  If it is `true`, then `t` steps
    to `t_2`; otherwise it steps to `t_3`.

  - Otherwise, `t_1` takes a step, and therefore so does `t` (by `if`).

<pre class="Agda">

<a name="3953" href="StlcProp.html#2268" class="Function"
      >progress</a
      ><a name="3961"
      > </a
      ><a name="3962" class="Symbol"
      >(</a
      ><a name="3963" href="Stlc.html#4176" class="InductiveConstructor"
      >Ax</a
      ><a name="3965"
      > </a
      ><a name="3966" class="Symbol"
      >())</a
      ><a name="3969"
      >
</a
      ><a name="3970" href="StlcProp.html#2268" class="Function"
      >progress</a
      ><a name="3978"
      > </a
      ><a name="3979" class="Symbol"
      >(</a
      ><a name="3980" href="Stlc.html#4233" class="InductiveConstructor"
      >&#8658;-I</a
      ><a name="3983"
      > </a
      ><a name="3984" href="StlcProp.html#3984" class="Bound"
      >&#8866;N</a
      ><a name="3986" class="Symbol"
      >)</a
      ><a name="3987"
      > </a
      ><a name="3988" class="Symbol"
      >=</a
      ><a name="3989"
      > </a
      ><a name="3990" href="https://agda.github.io/agda-stdlib/Data.Sum.html#489" class="InductiveConstructor"
      >inj&#8321;</a
      ><a name="3994"
      > </a
      ><a name="3995" href="Stlc.html#1608" class="InductiveConstructor"
      >value-&#955;&#7488;</a
      ><a name="4003"
      >
</a
      ><a name="4004" href="StlcProp.html#2268" class="Function"
      >progress</a
      ><a name="4012"
      > </a
      ><a name="4013" class="Symbol"
      >(</a
      ><a name="4014" href="Stlc.html#4316" class="InductiveConstructor"
      >&#8658;-E</a
      ><a name="4017"
      > </a
      ><a name="4018" class="Symbol"
      >{</a
      ><a name="4019" href="StlcProp.html#4019" class="Bound"
      >&#915;</a
      ><a name="4020" class="Symbol"
      >}</a
      ><a name="4021"
      > </a
      ><a name="4022" class="Symbol"
      >{</a
      ><a name="4023" href="StlcProp.html#4023" class="Bound"
      >L</a
      ><a name="4024" class="Symbol"
      >}</a
      ><a name="4025"
      > </a
      ><a name="4026" class="Symbol"
      >{</a
      ><a name="4027" href="StlcProp.html#4027" class="Bound"
      >M</a
      ><a name="4028" class="Symbol"
      >}</a
      ><a name="4029"
      > </a
      ><a name="4030" class="Symbol"
      >{</a
      ><a name="4031" href="StlcProp.html#4031" class="Bound"
      >A</a
      ><a name="4032" class="Symbol"
      >}</a
      ><a name="4033"
      > </a
      ><a name="4034" class="Symbol"
      >{</a
      ><a name="4035" href="StlcProp.html#4035" class="Bound"
      >B</a
      ><a name="4036" class="Symbol"
      >}</a
      ><a name="4037"
      > </a
      ><a name="4038" href="StlcProp.html#4038" class="Bound"
      >&#8866;L</a
      ><a name="4040"
      > </a
      ><a name="4041" href="StlcProp.html#4041" class="Bound"
      >&#8866;M</a
      ><a name="4043" class="Symbol"
      >)</a
      ><a name="4044"
      > </a
      ><a name="4045" class="Keyword"
      >with</a
      ><a name="4049"
      > </a
      ><a name="4050" href="StlcProp.html#2268" class="Function"
      >progress</a
      ><a name="4058"
      > </a
      ><a name="4059" href="StlcProp.html#4038" class="Bound"
      >&#8866;L</a
      ><a name="4061"
      >
</a
      ><a name="4062" class="Symbol"
      >...</a
      ><a name="4065"
      > </a
      ><a name="4066" class="Symbol"
      >|</a
      ><a name="4067"
      > </a
      ><a name="4068" href="https://agda.github.io/agda-stdlib/Data.Sum.html#514" class="InductiveConstructor"
      >inj&#8322;</a
      ><a name="4072"
      > </a
      ><a name="4073" class="Symbol"
      >(</a
      ><a name="4074" href="StlcProp.html#4074" class="Bound"
      >L&#8242;</a
      ><a name="4076"
      > </a
      ><a name="4077" href="https://agda.github.io/agda-stdlib/Data.Product.html#509" class="InductiveConstructor Operator"
      >,</a
      ><a name="4078"
      > </a
      ><a name="4079" href="StlcProp.html#4079" class="Bound"
      >L&#10233;L&#8242;</a
      ><a name="4083" class="Symbol"
      >)</a
      ><a name="4084"
      > </a
      ><a name="4085" class="Symbol"
      >=</a
      ><a name="4086"
      > </a
      ><a name="4087" href="https://agda.github.io/agda-stdlib/Data.Sum.html#514" class="InductiveConstructor"
      >inj&#8322;</a
      ><a name="4091"
      > </a
      ><a name="4092" class="Symbol"
      >(</a
      ><a name="4093" href="StlcProp.html#4074" class="Bound"
      >L&#8242;</a
      ><a name="4095"
      > </a
      ><a name="4096" href="Stlc.html#1106" class="InductiveConstructor Operator"
      >&#183;&#7488;</a
      ><a name="4098"
      > </a
      ><a name="4099" href="StlcProp.html#4027" class="Bound"
      >M</a
      ><a name="4100"
      > </a
      ><a name="4101" href="https://agda.github.io/agda-stdlib/Data.Product.html#509" class="InductiveConstructor Operator"
      >,</a
      ><a name="4102"
      > </a
      ><a name="4103" href="Stlc.html#2347" class="InductiveConstructor"
      >&#947;&#8658;&#8321;</a
      ><a name="4106"
      > </a
      ><a name="4107" href="StlcProp.html#4079" class="Bound"
      >L&#10233;L&#8242;</a
      ><a name="4111" class="Symbol"
      >)</a
      ><a name="4112"
      >
</a
      ><a name="4113" class="Symbol"
      >...</a
      ><a name="4116"
      > </a
      ><a name="4117" class="Symbol"
      >|</a
      ><a name="4118"
      > </a
      ><a name="4119" href="https://agda.github.io/agda-stdlib/Data.Sum.html#489" class="InductiveConstructor"
      >inj&#8321;</a
      ><a name="4123"
      > </a
      ><a name="4124" href="StlcProp.html#4124" class="Bound"
      >valueL</a
      ><a name="4130"
      > </a
      ><a name="4131" class="Keyword"
      >with</a
      ><a name="4135"
      > </a
      ><a name="4136" href="StlcProp.html#2268" class="Function"
      >progress</a
      ><a name="4144"
      > </a
      ><a name="4145" href="StlcProp.html#4041" class="Bound"
      >&#8866;M</a
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
      ><a name="4154" href="https://agda.github.io/agda-stdlib/Data.Sum.html#514" class="InductiveConstructor"
      >inj&#8322;</a
      ><a name="4158"
      > </a
      ><a name="4159" class="Symbol"
      >(</a
      ><a name="4160" href="StlcProp.html#4160" class="Bound"
      >M&#8242;</a
      ><a name="4162"
      > </a
      ><a name="4163" href="https://agda.github.io/agda-stdlib/Data.Product.html#509" class="InductiveConstructor Operator"
      >,</a
      ><a name="4164"
      > </a
      ><a name="4165" href="StlcProp.html#4165" class="Bound"
      >M&#10233;M&#8242;</a
      ><a name="4169" class="Symbol"
      >)</a
      ><a name="4170"
      > </a
      ><a name="4171" class="Symbol"
      >=</a
      ><a name="4172"
      > </a
      ><a name="4173" href="https://agda.github.io/agda-stdlib/Data.Sum.html#514" class="InductiveConstructor"
      >inj&#8322;</a
      ><a name="4177"
      > </a
      ><a name="4178" class="Symbol"
      >(</a
      ><a name="4179" href="StlcProp.html#4023" class="Bound"
      >L</a
      ><a name="4180"
      > </a
      ><a name="4181" href="Stlc.html#1106" class="InductiveConstructor Operator"
      >&#183;&#7488;</a
      ><a name="4183"
      > </a
      ><a name="4184" href="StlcProp.html#4160" class="Bound"
      >M&#8242;</a
      ><a name="4186"
      > </a
      ><a name="4187" href="https://agda.github.io/agda-stdlib/Data.Product.html#509" class="InductiveConstructor Operator"
      >,</a
      ><a name="4188"
      > </a
      ><a name="4189" href="Stlc.html#2406" class="InductiveConstructor"
      >&#947;&#8658;&#8322;</a
      ><a name="4192"
      > </a
      ><a name="4193" href="StlcProp.html#4124" class="Bound"
      >valueL</a
      ><a name="4199"
      > </a
      ><a name="4200" href="StlcProp.html#4165" class="Bound"
      >M&#10233;M&#8242;</a
      ><a name="4204" class="Symbol"
      >)</a
      ><a name="4205"
      >
</a
      ><a name="4206" class="Symbol"
      >...</a
      ><a name="4209"
      > </a
      ><a name="4210" class="Symbol"
      >|</a
      ><a name="4211"
      > </a
      ><a name="4212" href="https://agda.github.io/agda-stdlib/Data.Sum.html#489" class="InductiveConstructor"
      >inj&#8321;</a
      ><a name="4216"
      > </a
      ><a name="4217" href="StlcProp.html#4217" class="Bound"
      >valueM</a
      ><a name="4223"
      > </a
      ><a name="4224" class="Keyword"
      >with</a
      ><a name="4228"
      > </a
      ><a name="4229" href="StlcProp.html#1480" class="Function"
      >canonicalFormsLemma</a
      ><a name="4248"
      > </a
      ><a name="4249" href="StlcProp.html#4038" class="Bound"
      >&#8866;L</a
      ><a name="4251"
      > </a
      ><a name="4252" href="StlcProp.html#4124" class="Bound"
      >valueL</a
      ><a name="4258"
      >
</a
      ><a name="4259" class="Symbol"
      >...</a
      ><a name="4262"
      > </a
      ><a name="4263" class="Symbol"
      >|</a
      ><a name="4264"
      > </a
      ><a name="4265" href="StlcProp.html#1177" class="InductiveConstructor"
      >canonical-&#955;&#7488;</a
      ><a name="4277"
      > </a
      ><a name="4278" class="Symbol"
      >{</a
      ><a name="4279" href="StlcProp.html#4279" class="Bound"
      >x</a
      ><a name="4280" class="Symbol"
      >}</a
      ><a name="4281"
      > </a
      ><a name="4282" class="Symbol"
      >{</a
      ><a name="4283" class="DottedPattern Symbol"
      >.</a
      ><a name="4284" href="StlcProp.html#4031" class="DottedPattern Bound"
      >A</a
      ><a name="4285" class="Symbol"
      >}</a
      ><a name="4286"
      > </a
      ><a name="4287" class="Symbol"
      >{</a
      ><a name="4288" href="StlcProp.html#4288" class="Bound"
      >N</a
      ><a name="4289" class="Symbol"
      >}</a
      ><a name="4290"
      > </a
      ><a name="4291" class="Symbol"
      >{</a
      ><a name="4292" class="DottedPattern Symbol"
      >.</a
      ><a name="4293" href="StlcProp.html#4035" class="DottedPattern Bound"
      >B</a
      ><a name="4294" class="Symbol"
      >}</a
      ><a name="4295"
      > </a
      ><a name="4296" class="Symbol"
      >=</a
      ><a name="4297"
      > </a
      ><a name="4298" href="https://agda.github.io/agda-stdlib/Data.Sum.html#514" class="InductiveConstructor"
      >inj&#8322;</a
      ><a name="4302"
      > </a
      ><a name="4303" class="Symbol"
      >((</a
      ><a name="4305" href="StlcProp.html#4288" class="Bound"
      >N</a
      ><a name="4306"
      > </a
      ><a name="4307" href="Stlc.html#1756" class="Function Operator"
      >[</a
      ><a name="4308"
      > </a
      ><a name="4309" href="StlcProp.html#4279" class="Bound"
      >x</a
      ><a name="4310"
      > </a
      ><a name="4311" href="Stlc.html#1756" class="Function Operator"
      >:=</a
      ><a name="4313"
      > </a
      ><a name="4314" href="StlcProp.html#4027" class="Bound"
      >M</a
      ><a name="4315"
      > </a
      ><a name="4316" href="Stlc.html#1756" class="Function Operator"
      >]</a
      ><a name="4317" class="Symbol"
      >)</a
      ><a name="4318"
      > </a
      ><a name="4319" href="https://agda.github.io/agda-stdlib/Data.Product.html#509" class="InductiveConstructor Operator"
      >,</a
      ><a name="4320"
      > </a
      ><a name="4321" href="Stlc.html#2273" class="InductiveConstructor"
      >&#946;&#8658;</a
      ><a name="4323"
      > </a
      ><a name="4324" href="StlcProp.html#4217" class="Bound"
      >valueM</a
      ><a name="4330" class="Symbol"
      >)</a
      ><a name="4331"
      >
</a
      ><a name="4332" href="StlcProp.html#2268" class="Function"
      >progress</a
      ><a name="4340"
      > </a
      ><a name="4341" href="Stlc.html#4397" class="InductiveConstructor"
      >&#120121;-I&#8321;</a
      ><a name="4345"
      > </a
      ><a name="4346" class="Symbol"
      >=</a
      ><a name="4347"
      > </a
      ><a name="4348" href="https://agda.github.io/agda-stdlib/Data.Sum.html#489" class="InductiveConstructor"
      >inj&#8321;</a
      ><a name="4352"
      > </a
      ><a name="4353" href="Stlc.html#1654" class="InductiveConstructor"
      >value-true&#7488;</a
      ><a name="4364"
      >
</a
      ><a name="4365" href="StlcProp.html#2268" class="Function"
      >progress</a
      ><a name="4373"
      > </a
      ><a name="4374" href="Stlc.html#4432" class="InductiveConstructor"
      >&#120121;-I&#8322;</a
      ><a name="4378"
      > </a
      ><a name="4379" class="Symbol"
      >=</a
      ><a name="4380"
      > </a
      ><a name="4381" href="https://agda.github.io/agda-stdlib/Data.Sum.html#489" class="InductiveConstructor"
      >inj&#8321;</a
      ><a name="4385"
      > </a
      ><a name="4386" href="Stlc.html#1684" class="InductiveConstructor"
      >value-false&#7488;</a
      ><a name="4398"
      >
</a
      ><a name="4399" href="StlcProp.html#2268" class="Function"
      >progress</a
      ><a name="4407"
      > </a
      ><a name="4408" class="Symbol"
      >(</a
      ><a name="4409" href="Stlc.html#4468" class="InductiveConstructor"
      >&#120121;-E</a
      ><a name="4412"
      > </a
      ><a name="4413" class="Symbol"
      >{</a
      ><a name="4414" href="StlcProp.html#4414" class="Bound"
      >&#915;</a
      ><a name="4415" class="Symbol"
      >}</a
      ><a name="4416"
      > </a
      ><a name="4417" class="Symbol"
      >{</a
      ><a name="4418" href="StlcProp.html#4418" class="Bound"
      >L</a
      ><a name="4419" class="Symbol"
      >}</a
      ><a name="4420"
      > </a
      ><a name="4421" class="Symbol"
      >{</a
      ><a name="4422" href="StlcProp.html#4422" class="Bound"
      >M</a
      ><a name="4423" class="Symbol"
      >}</a
      ><a name="4424"
      > </a
      ><a name="4425" class="Symbol"
      >{</a
      ><a name="4426" href="StlcProp.html#4426" class="Bound"
      >N</a
      ><a name="4427" class="Symbol"
      >}</a
      ><a name="4428"
      > </a
      ><a name="4429" class="Symbol"
      >{</a
      ><a name="4430" href="StlcProp.html#4430" class="Bound"
      >A</a
      ><a name="4431" class="Symbol"
      >}</a
      ><a name="4432"
      > </a
      ><a name="4433" href="StlcProp.html#4433" class="Bound"
      >&#8866;L</a
      ><a name="4435"
      > </a
      ><a name="4436" href="StlcProp.html#4436" class="Bound"
      >&#8866;M</a
      ><a name="4438"
      > </a
      ><a name="4439" href="StlcProp.html#4439" class="Bound"
      >&#8866;N</a
      ><a name="4441" class="Symbol"
      >)</a
      ><a name="4442"
      > </a
      ><a name="4443" class="Keyword"
      >with</a
      ><a name="4447"
      > </a
      ><a name="4448" href="StlcProp.html#2268" class="Function"
      >progress</a
      ><a name="4456"
      > </a
      ><a name="4457" href="StlcProp.html#4433" class="Bound"
      >&#8866;L</a
      ><a name="4459"
      >
</a
      ><a name="4460" class="Symbol"
      >...</a
      ><a name="4463"
      > </a
      ><a name="4464" class="Symbol"
      >|</a
      ><a name="4465"
      > </a
      ><a name="4466" href="https://agda.github.io/agda-stdlib/Data.Sum.html#514" class="InductiveConstructor"
      >inj&#8322;</a
      ><a name="4470"
      > </a
      ><a name="4471" class="Symbol"
      >(</a
      ><a name="4472" href="StlcProp.html#4472" class="Bound"
      >L&#8242;</a
      ><a name="4474"
      > </a
      ><a name="4475" href="https://agda.github.io/agda-stdlib/Data.Product.html#509" class="InductiveConstructor Operator"
      >,</a
      ><a name="4476"
      > </a
      ><a name="4477" href="StlcProp.html#4477" class="Bound"
      >L&#10233;L&#8242;</a
      ><a name="4481" class="Symbol"
      >)</a
      ><a name="4482"
      > </a
      ><a name="4483" class="Symbol"
      >=</a
      ><a name="4484"
      > </a
      ><a name="4485" href="https://agda.github.io/agda-stdlib/Data.Sum.html#514" class="InductiveConstructor"
      >inj&#8322;</a
      ><a name="4489"
      > </a
      ><a name="4490" class="Symbol"
      >((</a
      ><a name="4492" href="Stlc.html#1165" class="InductiveConstructor Operator"
      >if&#7488;</a
      ><a name="4495"
      > </a
      ><a name="4496" href="StlcProp.html#4472" class="Bound"
      >L&#8242;</a
      ><a name="4498"
      > </a
      ><a name="4499" href="Stlc.html#1165" class="InductiveConstructor Operator"
      >then</a
      ><a name="4503"
      > </a
      ><a name="4504" href="StlcProp.html#4422" class="Bound"
      >M</a
      ><a name="4505"
      > </a
      ><a name="4506" href="Stlc.html#1165" class="InductiveConstructor Operator"
      >else</a
      ><a name="4510"
      > </a
      ><a name="4511" href="StlcProp.html#4426" class="Bound"
      >N</a
      ><a name="4512" class="Symbol"
      >)</a
      ><a name="4513"
      > </a
      ><a name="4514" href="https://agda.github.io/agda-stdlib/Data.Product.html#509" class="InductiveConstructor Operator"
      >,</a
      ><a name="4515"
      > </a
      ><a name="4516" href="Stlc.html#2584" class="InductiveConstructor"
      >&#947;&#120121;</a
      ><a name="4518"
      > </a
      ><a name="4519" href="StlcProp.html#4477" class="Bound"
      >L&#10233;L&#8242;</a
      ><a name="4523" class="Symbol"
      >)</a
      ><a name="4524"
      >
</a
      ><a name="4525" class="Symbol"
      >...</a
      ><a name="4528"
      > </a
      ><a name="4529" class="Symbol"
      >|</a
      ><a name="4530"
      > </a
      ><a name="4531" href="https://agda.github.io/agda-stdlib/Data.Sum.html#489" class="InductiveConstructor"
      >inj&#8321;</a
      ><a name="4535"
      > </a
      ><a name="4536" href="StlcProp.html#4536" class="Bound"
      >valueL</a
      ><a name="4542"
      > </a
      ><a name="4543" class="Keyword"
      >with</a
      ><a name="4547"
      > </a
      ><a name="4548" href="StlcProp.html#1480" class="Function"
      >canonicalFormsLemma</a
      ><a name="4567"
      > </a
      ><a name="4568" href="StlcProp.html#4433" class="Bound"
      >&#8866;L</a
      ><a name="4570"
      > </a
      ><a name="4571" href="StlcProp.html#4536" class="Bound"
      >valueL</a
      ><a name="4577"
      >
</a
      ><a name="4578" class="Symbol"
      >...</a
      ><a name="4581"
      > </a
      ><a name="4582" class="Symbol"
      >|</a
      ><a name="4583"
      > </a
      ><a name="4584" href="StlcProp.html#1245" class="InductiveConstructor"
      >canonical-true&#7488;</a
      ><a name="4599"
      > </a
      ><a name="4600" class="Symbol"
      >=</a
      ><a name="4601"
      > </a
      ><a name="4602" href="https://agda.github.io/agda-stdlib/Data.Sum.html#514" class="InductiveConstructor"
      >inj&#8322;</a
      ><a name="4606"
      > </a
      ><a name="4607" class="Symbol"
      >(</a
      ><a name="4608" href="StlcProp.html#4422" class="Bound"
      >M</a
      ><a name="4609"
      > </a
      ><a name="4610" href="https://agda.github.io/agda-stdlib/Data.Product.html#509" class="InductiveConstructor Operator"
      >,</a
      ><a name="4611"
      > </a
      ><a name="4612" href="Stlc.html#2479" class="InductiveConstructor"
      >&#946;&#120121;&#8321;</a
      ><a name="4615" class="Symbol"
      >)</a
      ><a name="4616"
      >
</a
      ><a name="4617" class="Symbol"
      >...</a
      ><a name="4620"
      > </a
      ><a name="4621" class="Symbol"
      >|</a
      ><a name="4622"
      > </a
      ><a name="4623" href="StlcProp.html#1287" class="InductiveConstructor"
      >canonical-false&#7488;</a
      ><a name="4639"
      > </a
      ><a name="4640" class="Symbol"
      >=</a
      ><a name="4641"
      > </a
      ><a name="4642" href="https://agda.github.io/agda-stdlib/Data.Sum.html#514" class="InductiveConstructor"
      >inj&#8322;</a
      ><a name="4646"
      > </a
      ><a name="4647" class="Symbol"
      >(</a
      ><a name="4648" href="StlcProp.html#4426" class="Bound"
      >N</a
      ><a name="4649"
      > </a
      ><a name="4650" href="https://agda.github.io/agda-stdlib/Data.Product.html#509" class="InductiveConstructor Operator"
      >,</a
      ><a name="4651"
      > </a
      ><a name="4652" href="Stlc.html#2531" class="InductiveConstructor"
      >&#946;&#120121;&#8322;</a
      ><a name="4655" class="Symbol"
      >)</a
      >

</pre>

#### Exercise: 3 stars, optional (progress_from_term_ind)
Show that progress can also be proved by induction on terms
instead of induction on typing derivations.

<pre class="Agda">

<a name="4845" class="Keyword"
      >postulate</a
      ><a name="4854"
      >
  </a
      ><a name="4857" href="StlcProp.html#4857" class="Postulate"
      >progress&#8242;</a
      ><a name="4866"
      > </a
      ><a name="4867" class="Symbol"
      >:</a
      ><a name="4868"
      > </a
      ><a name="4869" class="Symbol"
      >&#8704;</a
      ><a name="4870"
      > </a
      ><a name="4871" class="Symbol"
      >{</a
      ><a name="4872" href="StlcProp.html#4872" class="Bound"
      >M</a
      ><a name="4873"
      > </a
      ><a name="4874" href="StlcProp.html#4874" class="Bound"
      >A</a
      ><a name="4875" class="Symbol"
      >}</a
      ><a name="4876"
      > </a
      ><a name="4877" class="Symbol"
      >&#8594;</a
      ><a name="4878"
      > </a
      ><a name="4879" href="Maps.html#10360" class="Function"
      >&#8709;</a
      ><a name="4880"
      > </a
      ><a name="4881" href="Stlc.html#4132" class="Datatype Operator"
      >&#8866;</a
      ><a name="4882"
      > </a
      ><a name="4883" href="StlcProp.html#4872" class="Bound"
      >M</a
      ><a name="4884"
      > </a
      ><a name="4885" href="Stlc.html#4132" class="Datatype Operator"
      >&#8712;</a
      ><a name="4886"
      > </a
      ><a name="4887" href="StlcProp.html#4874" class="Bound"
      >A</a
      ><a name="4888"
      > </a
      ><a name="4889" class="Symbol"
      >&#8594;</a
      ><a name="4890"
      > </a
      ><a name="4891" href="Stlc.html#1581" class="Datatype"
      >value</a
      ><a name="4896"
      > </a
      ><a name="4897" href="StlcProp.html#4872" class="Bound"
      >M</a
      ><a name="4898"
      > </a
      ><a name="4899" href="https://agda.github.io/agda-stdlib/Data.Sum.html#433" class="Datatype Operator"
      >&#8846;</a
      ><a name="4900"
      > </a
      ><a name="4901" href="https://agda.github.io/agda-stdlib/Data.Product.html#823" class="Function"
      >&#8707;</a
      ><a name="4902"
      > </a
      ><a name="4903" class="Symbol"
      >&#955;</a
      ><a name="4904"
      > </a
      ><a name="4905" href="StlcProp.html#4905" class="Bound"
      >N</a
      ><a name="4906"
      > </a
      ><a name="4907" class="Symbol"
      >&#8594;</a
      ><a name="4908"
      > </a
      ><a name="4909" href="StlcProp.html#4872" class="Bound"
      >M</a
      ><a name="4910"
      > </a
      ><a name="4911" href="Stlc.html#2241" class="Datatype Operator"
      >&#10233;</a
      ><a name="4912"
      > </a
      ><a name="4913" href="StlcProp.html#4905" class="Bound"
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

  - `y` appears free, but `x` does not, in `λᵀ x ∈ (A ⇒ B) ⇒ x ·ᵀ y`
  - both `x` and `y` appear free in `(λᵀ x ∈ (A ⇒ B) ⇒ x ·ᵀ y) ·ᵀ x`
  - no variables appear free in `λᵀ x ∈ (A ⇒ B) ⇒ (λᵀ y ∈ A ⇒ x ·ᵀ y)`

Formally:

<pre class="Agda">

<a name="7309" class="Keyword"
      >data</a
      ><a name="7313"
      > </a
      ><a name="7314" href="StlcProp.html#7314" class="Datatype Operator"
      >_FreeIn_</a
      ><a name="7322"
      > </a
      ><a name="7323" class="Symbol"
      >:</a
      ><a name="7324"
      > </a
      ><a name="7325" href="Maps.html#2215" class="Datatype"
      >Id</a
      ><a name="7327"
      > </a
      ><a name="7328" class="Symbol"
      >&#8594;</a
      ><a name="7329"
      > </a
      ><a name="7330" href="Stlc.html#1032" class="Datatype"
      >Term</a
      ><a name="7334"
      > </a
      ><a name="7335" class="Symbol"
      >&#8594;</a
      ><a name="7336"
      > </a
      ><a name="7337" class="PrimitiveType"
      >Set</a
      ><a name="7340"
      > </a
      ><a name="7341" class="Keyword"
      >where</a
      ><a name="7346"
      >
  </a
      ><a name="7349" href="StlcProp.html#7349" class="InductiveConstructor"
      >free-var&#7488;</a
      ><a name="7358"
      >  </a
      ><a name="7360" class="Symbol"
      >:</a
      ><a name="7361"
      > </a
      ><a name="7362" class="Symbol"
      >&#8704;</a
      ><a name="7363"
      > </a
      ><a name="7364" class="Symbol"
      >{</a
      ><a name="7365" href="StlcProp.html#7365" class="Bound"
      >x</a
      ><a name="7366" class="Symbol"
      >}</a
      ><a name="7367"
      > </a
      ><a name="7368" class="Symbol"
      >&#8594;</a
      ><a name="7369"
      > </a
      ><a name="7370" href="StlcProp.html#7365" class="Bound"
      >x</a
      ><a name="7371"
      > </a
      ><a name="7372" href="StlcProp.html#7314" class="Datatype Operator"
      >FreeIn</a
      ><a name="7378"
      > </a
      ><a name="7379" class="Symbol"
      >(</a
      ><a name="7380" href="Stlc.html#1051" class="InductiveConstructor"
      >var&#7488;</a
      ><a name="7384"
      > </a
      ><a name="7385" href="StlcProp.html#7365" class="Bound"
      >x</a
      ><a name="7386" class="Symbol"
      >)</a
      ><a name="7387"
      >
  </a
      ><a name="7390" href="StlcProp.html#7390" class="InductiveConstructor"
      >free-&#955;&#7488;</a
      ><a name="7397"
      >  </a
      ><a name="7399" class="Symbol"
      >:</a
      ><a name="7400"
      > </a
      ><a name="7401" class="Symbol"
      >&#8704;</a
      ><a name="7402"
      > </a
      ><a name="7403" class="Symbol"
      >{</a
      ><a name="7404" href="StlcProp.html#7404" class="Bound"
      >x</a
      ><a name="7405"
      > </a
      ><a name="7406" href="StlcProp.html#7406" class="Bound"
      >y</a
      ><a name="7407"
      > </a
      ><a name="7408" href="StlcProp.html#7408" class="Bound"
      >A</a
      ><a name="7409"
      > </a
      ><a name="7410" href="StlcProp.html#7410" class="Bound"
      >N</a
      ><a name="7411" class="Symbol"
      >}</a
      ><a name="7412"
      > </a
      ><a name="7413" class="Symbol"
      >&#8594;</a
      ><a name="7414"
      > </a
      ><a name="7415" href="StlcProp.html#7406" class="Bound"
      >y</a
      ><a name="7416"
      > </a
      ><a name="7417" href="https://agda.github.io/agda-stdlib/Relation.Binary.Core.html#4493" class="Function Operator"
      >&#8802;</a
      ><a name="7418"
      > </a
      ><a name="7419" href="StlcProp.html#7404" class="Bound"
      >x</a
      ><a name="7420"
      > </a
      ><a name="7421" class="Symbol"
      >&#8594;</a
      ><a name="7422"
      > </a
      ><a name="7423" href="StlcProp.html#7404" class="Bound"
      >x</a
      ><a name="7424"
      > </a
      ><a name="7425" href="StlcProp.html#7314" class="Datatype Operator"
      >FreeIn</a
      ><a name="7431"
      > </a
      ><a name="7432" href="StlcProp.html#7410" class="Bound"
      >N</a
      ><a name="7433"
      > </a
      ><a name="7434" class="Symbol"
      >&#8594;</a
      ><a name="7435"
      > </a
      ><a name="7436" href="StlcProp.html#7404" class="Bound"
      >x</a
      ><a name="7437"
      > </a
      ><a name="7438" href="StlcProp.html#7314" class="Datatype Operator"
      >FreeIn</a
      ><a name="7444"
      > </a
      ><a name="7445" class="Symbol"
      >(</a
      ><a name="7446" href="Stlc.html#1070" class="InductiveConstructor Operator"
      >&#955;&#7488;</a
      ><a name="7448"
      > </a
      ><a name="7449" href="StlcProp.html#7406" class="Bound"
      >y</a
      ><a name="7450"
      > </a
      ><a name="7451" href="Stlc.html#1070" class="InductiveConstructor Operator"
      >&#8712;</a
      ><a name="7452"
      > </a
      ><a name="7453" href="StlcProp.html#7408" class="Bound"
      >A</a
      ><a name="7454"
      > </a
      ><a name="7455" href="Stlc.html#1070" class="InductiveConstructor Operator"
      >&#8658;</a
      ><a name="7456"
      > </a
      ><a name="7457" href="StlcProp.html#7410" class="Bound"
      >N</a
      ><a name="7458" class="Symbol"
      >)</a
      ><a name="7459"
      >
  </a
      ><a name="7462" href="StlcProp.html#7462" class="InductiveConstructor"
      >free-&#183;&#7488;&#8321;</a
      ><a name="7470"
      > </a
      ><a name="7471" class="Symbol"
      >:</a
      ><a name="7472"
      > </a
      ><a name="7473" class="Symbol"
      >&#8704;</a
      ><a name="7474"
      > </a
      ><a name="7475" class="Symbol"
      >{</a
      ><a name="7476" href="StlcProp.html#7476" class="Bound"
      >x</a
      ><a name="7477"
      > </a
      ><a name="7478" href="StlcProp.html#7478" class="Bound"
      >L</a
      ><a name="7479"
      > </a
      ><a name="7480" href="StlcProp.html#7480" class="Bound"
      >M</a
      ><a name="7481" class="Symbol"
      >}</a
      ><a name="7482"
      > </a
      ><a name="7483" class="Symbol"
      >&#8594;</a
      ><a name="7484"
      > </a
      ><a name="7485" href="StlcProp.html#7476" class="Bound"
      >x</a
      ><a name="7486"
      > </a
      ><a name="7487" href="StlcProp.html#7314" class="Datatype Operator"
      >FreeIn</a
      ><a name="7493"
      > </a
      ><a name="7494" href="StlcProp.html#7478" class="Bound"
      >L</a
      ><a name="7495"
      > </a
      ><a name="7496" class="Symbol"
      >&#8594;</a
      ><a name="7497"
      > </a
      ><a name="7498" href="StlcProp.html#7476" class="Bound"
      >x</a
      ><a name="7499"
      > </a
      ><a name="7500" href="StlcProp.html#7314" class="Datatype Operator"
      >FreeIn</a
      ><a name="7506"
      > </a
      ><a name="7507" class="Symbol"
      >(</a
      ><a name="7508" href="StlcProp.html#7478" class="Bound"
      >L</a
      ><a name="7509"
      > </a
      ><a name="7510" href="Stlc.html#1106" class="InductiveConstructor Operator"
      >&#183;&#7488;</a
      ><a name="7512"
      > </a
      ><a name="7513" href="StlcProp.html#7480" class="Bound"
      >M</a
      ><a name="7514" class="Symbol"
      >)</a
      ><a name="7515"
      >
  </a
      ><a name="7518" href="StlcProp.html#7518" class="InductiveConstructor"
      >free-&#183;&#7488;&#8322;</a
      ><a name="7526"
      > </a
      ><a name="7527" class="Symbol"
      >:</a
      ><a name="7528"
      > </a
      ><a name="7529" class="Symbol"
      >&#8704;</a
      ><a name="7530"
      > </a
      ><a name="7531" class="Symbol"
      >{</a
      ><a name="7532" href="StlcProp.html#7532" class="Bound"
      >x</a
      ><a name="7533"
      > </a
      ><a name="7534" href="StlcProp.html#7534" class="Bound"
      >L</a
      ><a name="7535"
      > </a
      ><a name="7536" href="StlcProp.html#7536" class="Bound"
      >M</a
      ><a name="7537" class="Symbol"
      >}</a
      ><a name="7538"
      > </a
      ><a name="7539" class="Symbol"
      >&#8594;</a
      ><a name="7540"
      > </a
      ><a name="7541" href="StlcProp.html#7532" class="Bound"
      >x</a
      ><a name="7542"
      > </a
      ><a name="7543" href="StlcProp.html#7314" class="Datatype Operator"
      >FreeIn</a
      ><a name="7549"
      > </a
      ><a name="7550" href="StlcProp.html#7536" class="Bound"
      >M</a
      ><a name="7551"
      > </a
      ><a name="7552" class="Symbol"
      >&#8594;</a
      ><a name="7553"
      > </a
      ><a name="7554" href="StlcProp.html#7532" class="Bound"
      >x</a
      ><a name="7555"
      > </a
      ><a name="7556" href="StlcProp.html#7314" class="Datatype Operator"
      >FreeIn</a
      ><a name="7562"
      > </a
      ><a name="7563" class="Symbol"
      >(</a
      ><a name="7564" href="StlcProp.html#7534" class="Bound"
      >L</a
      ><a name="7565"
      > </a
      ><a name="7566" href="Stlc.html#1106" class="InductiveConstructor Operator"
      >&#183;&#7488;</a
      ><a name="7568"
      > </a
      ><a name="7569" href="StlcProp.html#7536" class="Bound"
      >M</a
      ><a name="7570" class="Symbol"
      >)</a
      ><a name="7571"
      >
  </a
      ><a name="7574" href="StlcProp.html#7574" class="InductiveConstructor"
      >free-if&#7488;&#8321;</a
      ><a name="7583"
      > </a
      ><a name="7584" class="Symbol"
      >:</a
      ><a name="7585"
      > </a
      ><a name="7586" class="Symbol"
      >&#8704;</a
      ><a name="7587"
      > </a
      ><a name="7588" class="Symbol"
      >{</a
      ><a name="7589" href="StlcProp.html#7589" class="Bound"
      >x</a
      ><a name="7590"
      > </a
      ><a name="7591" href="StlcProp.html#7591" class="Bound"
      >L</a
      ><a name="7592"
      > </a
      ><a name="7593" href="StlcProp.html#7593" class="Bound"
      >M</a
      ><a name="7594"
      > </a
      ><a name="7595" href="StlcProp.html#7595" class="Bound"
      >N</a
      ><a name="7596" class="Symbol"
      >}</a
      ><a name="7597"
      > </a
      ><a name="7598" class="Symbol"
      >&#8594;</a
      ><a name="7599"
      > </a
      ><a name="7600" href="StlcProp.html#7589" class="Bound"
      >x</a
      ><a name="7601"
      > </a
      ><a name="7602" href="StlcProp.html#7314" class="Datatype Operator"
      >FreeIn</a
      ><a name="7608"
      > </a
      ><a name="7609" href="StlcProp.html#7591" class="Bound"
      >L</a
      ><a name="7610"
      > </a
      ><a name="7611" class="Symbol"
      >&#8594;</a
      ><a name="7612"
      > </a
      ><a name="7613" href="StlcProp.html#7589" class="Bound"
      >x</a
      ><a name="7614"
      > </a
      ><a name="7615" href="StlcProp.html#7314" class="Datatype Operator"
      >FreeIn</a
      ><a name="7621"
      > </a
      ><a name="7622" class="Symbol"
      >(</a
      ><a name="7623" href="Stlc.html#1165" class="InductiveConstructor Operator"
      >if&#7488;</a
      ><a name="7626"
      > </a
      ><a name="7627" href="StlcProp.html#7591" class="Bound"
      >L</a
      ><a name="7628"
      > </a
      ><a name="7629" href="Stlc.html#1165" class="InductiveConstructor Operator"
      >then</a
      ><a name="7633"
      > </a
      ><a name="7634" href="StlcProp.html#7593" class="Bound"
      >M</a
      ><a name="7635"
      > </a
      ><a name="7636" href="Stlc.html#1165" class="InductiveConstructor Operator"
      >else</a
      ><a name="7640"
      > </a
      ><a name="7641" href="StlcProp.html#7595" class="Bound"
      >N</a
      ><a name="7642" class="Symbol"
      >)</a
      ><a name="7643"
      >
  </a
      ><a name="7646" href="StlcProp.html#7646" class="InductiveConstructor"
      >free-if&#7488;&#8322;</a
      ><a name="7655"
      > </a
      ><a name="7656" class="Symbol"
      >:</a
      ><a name="7657"
      > </a
      ><a name="7658" class="Symbol"
      >&#8704;</a
      ><a name="7659"
      > </a
      ><a name="7660" class="Symbol"
      >{</a
      ><a name="7661" href="StlcProp.html#7661" class="Bound"
      >x</a
      ><a name="7662"
      > </a
      ><a name="7663" href="StlcProp.html#7663" class="Bound"
      >L</a
      ><a name="7664"
      > </a
      ><a name="7665" href="StlcProp.html#7665" class="Bound"
      >M</a
      ><a name="7666"
      > </a
      ><a name="7667" href="StlcProp.html#7667" class="Bound"
      >N</a
      ><a name="7668" class="Symbol"
      >}</a
      ><a name="7669"
      > </a
      ><a name="7670" class="Symbol"
      >&#8594;</a
      ><a name="7671"
      > </a
      ><a name="7672" href="StlcProp.html#7661" class="Bound"
      >x</a
      ><a name="7673"
      > </a
      ><a name="7674" href="StlcProp.html#7314" class="Datatype Operator"
      >FreeIn</a
      ><a name="7680"
      > </a
      ><a name="7681" href="StlcProp.html#7665" class="Bound"
      >M</a
      ><a name="7682"
      > </a
      ><a name="7683" class="Symbol"
      >&#8594;</a
      ><a name="7684"
      > </a
      ><a name="7685" href="StlcProp.html#7661" class="Bound"
      >x</a
      ><a name="7686"
      > </a
      ><a name="7687" href="StlcProp.html#7314" class="Datatype Operator"
      >FreeIn</a
      ><a name="7693"
      > </a
      ><a name="7694" class="Symbol"
      >(</a
      ><a name="7695" href="Stlc.html#1165" class="InductiveConstructor Operator"
      >if&#7488;</a
      ><a name="7698"
      > </a
      ><a name="7699" href="StlcProp.html#7663" class="Bound"
      >L</a
      ><a name="7700"
      > </a
      ><a name="7701" href="Stlc.html#1165" class="InductiveConstructor Operator"
      >then</a
      ><a name="7705"
      > </a
      ><a name="7706" href="StlcProp.html#7665" class="Bound"
      >M</a
      ><a name="7707"
      > </a
      ><a name="7708" href="Stlc.html#1165" class="InductiveConstructor Operator"
      >else</a
      ><a name="7712"
      > </a
      ><a name="7713" href="StlcProp.html#7667" class="Bound"
      >N</a
      ><a name="7714" class="Symbol"
      >)</a
      ><a name="7715"
      >
  </a
      ><a name="7718" href="StlcProp.html#7718" class="InductiveConstructor"
      >free-if&#7488;&#8323;</a
      ><a name="7727"
      > </a
      ><a name="7728" class="Symbol"
      >:</a
      ><a name="7729"
      > </a
      ><a name="7730" class="Symbol"
      >&#8704;</a
      ><a name="7731"
      > </a
      ><a name="7732" class="Symbol"
      >{</a
      ><a name="7733" href="StlcProp.html#7733" class="Bound"
      >x</a
      ><a name="7734"
      > </a
      ><a name="7735" href="StlcProp.html#7735" class="Bound"
      >L</a
      ><a name="7736"
      > </a
      ><a name="7737" href="StlcProp.html#7737" class="Bound"
      >M</a
      ><a name="7738"
      > </a
      ><a name="7739" href="StlcProp.html#7739" class="Bound"
      >N</a
      ><a name="7740" class="Symbol"
      >}</a
      ><a name="7741"
      > </a
      ><a name="7742" class="Symbol"
      >&#8594;</a
      ><a name="7743"
      > </a
      ><a name="7744" href="StlcProp.html#7733" class="Bound"
      >x</a
      ><a name="7745"
      > </a
      ><a name="7746" href="StlcProp.html#7314" class="Datatype Operator"
      >FreeIn</a
      ><a name="7752"
      > </a
      ><a name="7753" href="StlcProp.html#7739" class="Bound"
      >N</a
      ><a name="7754"
      > </a
      ><a name="7755" class="Symbol"
      >&#8594;</a
      ><a name="7756"
      > </a
      ><a name="7757" href="StlcProp.html#7733" class="Bound"
      >x</a
      ><a name="7758"
      > </a
      ><a name="7759" href="StlcProp.html#7314" class="Datatype Operator"
      >FreeIn</a
      ><a name="7765"
      > </a
      ><a name="7766" class="Symbol"
      >(</a
      ><a name="7767" href="Stlc.html#1165" class="InductiveConstructor Operator"
      >if&#7488;</a
      ><a name="7770"
      > </a
      ><a name="7771" href="StlcProp.html#7735" class="Bound"
      >L</a
      ><a name="7772"
      > </a
      ><a name="7773" href="Stlc.html#1165" class="InductiveConstructor Operator"
      >then</a
      ><a name="7777"
      > </a
      ><a name="7778" href="StlcProp.html#7737" class="Bound"
      >M</a
      ><a name="7779"
      > </a
      ><a name="7780" href="Stlc.html#1165" class="InductiveConstructor Operator"
      >else</a
      ><a name="7784"
      > </a
      ><a name="7785" href="StlcProp.html#7739" class="Bound"
      >N</a
      ><a name="7786" class="Symbol"
      >)</a
      >

</pre>

A term in which no variables appear free is said to be _closed_.

<pre class="Agda">

<a name="7879" href="StlcProp.html#7879" class="Function"
      >closed</a
      ><a name="7885"
      > </a
      ><a name="7886" class="Symbol"
      >:</a
      ><a name="7887"
      > </a
      ><a name="7888" href="Stlc.html#1032" class="Datatype"
      >Term</a
      ><a name="7892"
      > </a
      ><a name="7893" class="Symbol"
      >&#8594;</a
      ><a name="7894"
      > </a
      ><a name="7895" class="PrimitiveType"
      >Set</a
      ><a name="7898"
      >
</a
      ><a name="7899" href="StlcProp.html#7879" class="Function"
      >closed</a
      ><a name="7905"
      > </a
      ><a name="7906" href="StlcProp.html#7906" class="Bound"
      >M</a
      ><a name="7907"
      > </a
      ><a name="7908" class="Symbol"
      >=</a
      ><a name="7909"
      > </a
      ><a name="7910" class="Symbol"
      >&#8704;</a
      ><a name="7911"
      > </a
      ><a name="7912" class="Symbol"
      >{</a
      ><a name="7913" href="StlcProp.html#7913" class="Bound"
      >x</a
      ><a name="7914" class="Symbol"
      >}</a
      ><a name="7915"
      > </a
      ><a name="7916" class="Symbol"
      >&#8594;</a
      ><a name="7917"
      > </a
      ><a name="7918" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#414" class="Function Operator"
      >&#172;</a
      ><a name="7919"
      > </a
      ><a name="7920" class="Symbol"
      >(</a
      ><a name="7921" href="StlcProp.html#7913" class="Bound"
      >x</a
      ><a name="7922"
      > </a
      ><a name="7923" href="StlcProp.html#7314" class="Datatype Operator"
      >FreeIn</a
      ><a name="7929"
      > </a
      ><a name="7930" href="StlcProp.html#7906" class="Bound"
      >M</a
      ><a name="7931" class="Symbol"
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
a variable `x` appears free in a term `M`, and if we know `M` is
well typed in context `Γ`, then it must be the case that
`Γ` assigns a type to `x`.

<pre class="Agda">

<a name="8638" href="StlcProp.html#8638" class="Function"
      >freeLemma</a
      ><a name="8647"
      > </a
      ><a name="8648" class="Symbol"
      >:</a
      ><a name="8649"
      > </a
      ><a name="8650" class="Symbol"
      >&#8704;</a
      ><a name="8651"
      > </a
      ><a name="8652" class="Symbol"
      >{</a
      ><a name="8653" href="StlcProp.html#8653" class="Bound"
      >x</a
      ><a name="8654"
      > </a
      ><a name="8655" href="StlcProp.html#8655" class="Bound"
      >M</a
      ><a name="8656"
      > </a
      ><a name="8657" href="StlcProp.html#8657" class="Bound"
      >A</a
      ><a name="8658"
      > </a
      ><a name="8659" href="StlcProp.html#8659" class="Bound"
      >&#915;</a
      ><a name="8660" class="Symbol"
      >}</a
      ><a name="8661"
      > </a
      ><a name="8662" class="Symbol"
      >&#8594;</a
      ><a name="8663"
      > </a
      ><a name="8664" href="StlcProp.html#8653" class="Bound"
      >x</a
      ><a name="8665"
      > </a
      ><a name="8666" href="StlcProp.html#7314" class="Datatype Operator"
      >FreeIn</a
      ><a name="8672"
      > </a
      ><a name="8673" href="StlcProp.html#8655" class="Bound"
      >M</a
      ><a name="8674"
      > </a
      ><a name="8675" class="Symbol"
      >&#8594;</a
      ><a name="8676"
      > </a
      ><a name="8677" href="StlcProp.html#8659" class="Bound"
      >&#915;</a
      ><a name="8678"
      > </a
      ><a name="8679" href="Stlc.html#4132" class="Datatype Operator"
      >&#8866;</a
      ><a name="8680"
      > </a
      ><a name="8681" href="StlcProp.html#8655" class="Bound"
      >M</a
      ><a name="8682"
      > </a
      ><a name="8683" href="Stlc.html#4132" class="Datatype Operator"
      >&#8712;</a
      ><a name="8684"
      > </a
      ><a name="8685" href="StlcProp.html#8657" class="Bound"
      >A</a
      ><a name="8686"
      > </a
      ><a name="8687" class="Symbol"
      >&#8594;</a
      ><a name="8688"
      > </a
      ><a name="8689" href="https://agda.github.io/agda-stdlib/Data.Product.html#823" class="Function"
      >&#8707;</a
      ><a name="8690"
      > </a
      ><a name="8691" class="Symbol"
      >&#955;</a
      ><a name="8692"
      > </a
      ><a name="8693" href="StlcProp.html#8693" class="Bound"
      >B</a
      ><a name="8694"
      > </a
      ><a name="8695" class="Symbol"
      >&#8594;</a
      ><a name="8696"
      > </a
      ><a name="8697" href="StlcProp.html#8659" class="Bound"
      >&#915;</a
      ><a name="8698"
      > </a
      ><a name="8699" href="StlcProp.html#8653" class="Bound"
      >x</a
      ><a name="8700"
      > </a
      ><a name="8701" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="8702"
      > </a
      ><a name="8703" href="https://agda.github.io/agda-stdlib/Data.Maybe.Base.html#373" class="InductiveConstructor"
      >just</a
      ><a name="8707"
      > </a
      ><a name="8708" href="StlcProp.html#8693" class="Bound"
      >B</a
      >

</pre>

_Proof_: We show, by induction on the proof that `x` appears
  free in `P`, that, for all contexts `Γ`, if `P` is well
  typed under `Γ`, then `Γ` assigns some type to `x`.

  - If the last rule used was `free-varᵀ`, then `P = x`, and from
    the assumption that `M` is well typed under `Γ` we have
    immediately that `Γ` assigns a type to `x`.

  - If the last rule used was `free-·₁`, then `P = L ·ᵀ M` and `x`
    appears free in `L`.  Since `L` is well typed under `\Gamma`,
    we can see from the typing rules that `L` must also be, and
    the IH then tells us that `Γ` assigns `x` a type.

  - Almost all the other cases are similar: `x` appears free in a
    subterm of `P`, and since `P` is well typed under `Γ`, we
    know the subterm of `M` in which `x` appears is well typed
    under `Γ` as well, and the IH gives us exactly the
    conclusion we want.

  - The only remaining case is `free-λᵀ`.  In this case `P =
    λᵀ y ∈ A ⇒ N`, and `x` appears free in `N`; we also know that
    `x` is different from `y`.  The difference from the previous
    cases is that whereas `P` is well typed under `\Gamma`, its
    body `N` is well typed under `(Γ , y ↦ A)`, so the IH
    allows us to conclude that `x` is assigned some type by the
    extended context `(Γ , y ↦ A)`.  To conclude that `Γ`
    assigns a type to `x`, we appeal the decidable equality for names
    `_≟_`, noting that `x` and `y` are different variables.

<pre class="Agda">

<a name="10174" href="StlcProp.html#8638" class="Function"
      >freeLemma</a
      ><a name="10183"
      > </a
      ><a name="10184" href="StlcProp.html#7349" class="InductiveConstructor"
      >free-var&#7488;</a
      ><a name="10193"
      > </a
      ><a name="10194" class="Symbol"
      >(</a
      ><a name="10195" href="Stlc.html#4176" class="InductiveConstructor"
      >Ax</a
      ><a name="10197"
      > </a
      ><a name="10198" href="StlcProp.html#10198" class="Bound"
      >&#915;x&#8801;justA</a
      ><a name="10206" class="Symbol"
      >)</a
      ><a name="10207"
      > </a
      ><a name="10208" class="Symbol"
      >=</a
      ><a name="10209"
      > </a
      ><a name="10210" class="Symbol"
      >(_</a
      ><a name="10212"
      > </a
      ><a name="10213" href="https://agda.github.io/agda-stdlib/Data.Product.html#509" class="InductiveConstructor Operator"
      >,</a
      ><a name="10214"
      > </a
      ><a name="10215" href="StlcProp.html#10198" class="Bound"
      >&#915;x&#8801;justA</a
      ><a name="10223" class="Symbol"
      >)</a
      ><a name="10224"
      >
</a
      ><a name="10225" href="StlcProp.html#8638" class="Function"
      >freeLemma</a
      ><a name="10234"
      > </a
      ><a name="10235" class="Symbol"
      >(</a
      ><a name="10236" href="StlcProp.html#7462" class="InductiveConstructor"
      >free-&#183;&#7488;&#8321;</a
      ><a name="10244"
      > </a
      ><a name="10245" href="StlcProp.html#10245" class="Bound"
      >x&#8712;L</a
      ><a name="10248" class="Symbol"
      >)</a
      ><a name="10249"
      > </a
      ><a name="10250" class="Symbol"
      >(</a
      ><a name="10251" href="Stlc.html#4316" class="InductiveConstructor"
      >&#8658;-E</a
      ><a name="10254"
      > </a
      ><a name="10255" href="StlcProp.html#10255" class="Bound"
      >&#8866;L</a
      ><a name="10257"
      > </a
      ><a name="10258" href="StlcProp.html#10258" class="Bound"
      >&#8866;M</a
      ><a name="10260" class="Symbol"
      >)</a
      ><a name="10261"
      > </a
      ><a name="10262" class="Symbol"
      >=</a
      ><a name="10263"
      > </a
      ><a name="10264" href="StlcProp.html#8638" class="Function"
      >freeLemma</a
      ><a name="10273"
      > </a
      ><a name="10274" href="StlcProp.html#10245" class="Bound"
      >x&#8712;L</a
      ><a name="10277"
      > </a
      ><a name="10278" href="StlcProp.html#10255" class="Bound"
      >&#8866;L</a
      ><a name="10280"
      >
</a
      ><a name="10281" href="StlcProp.html#8638" class="Function"
      >freeLemma</a
      ><a name="10290"
      > </a
      ><a name="10291" class="Symbol"
      >(</a
      ><a name="10292" href="StlcProp.html#7518" class="InductiveConstructor"
      >free-&#183;&#7488;&#8322;</a
      ><a name="10300"
      > </a
      ><a name="10301" href="StlcProp.html#10301" class="Bound"
      >x&#8712;M</a
      ><a name="10304" class="Symbol"
      >)</a
      ><a name="10305"
      > </a
      ><a name="10306" class="Symbol"
      >(</a
      ><a name="10307" href="Stlc.html#4316" class="InductiveConstructor"
      >&#8658;-E</a
      ><a name="10310"
      > </a
      ><a name="10311" href="StlcProp.html#10311" class="Bound"
      >&#8866;L</a
      ><a name="10313"
      > </a
      ><a name="10314" href="StlcProp.html#10314" class="Bound"
      >&#8866;M</a
      ><a name="10316" class="Symbol"
      >)</a
      ><a name="10317"
      > </a
      ><a name="10318" class="Symbol"
      >=</a
      ><a name="10319"
      > </a
      ><a name="10320" href="StlcProp.html#8638" class="Function"
      >freeLemma</a
      ><a name="10329"
      > </a
      ><a name="10330" href="StlcProp.html#10301" class="Bound"
      >x&#8712;M</a
      ><a name="10333"
      > </a
      ><a name="10334" href="StlcProp.html#10314" class="Bound"
      >&#8866;M</a
      ><a name="10336"
      >
</a
      ><a name="10337" href="StlcProp.html#8638" class="Function"
      >freeLemma</a
      ><a name="10346"
      > </a
      ><a name="10347" class="Symbol"
      >(</a
      ><a name="10348" href="StlcProp.html#7574" class="InductiveConstructor"
      >free-if&#7488;&#8321;</a
      ><a name="10357"
      > </a
      ><a name="10358" href="StlcProp.html#10358" class="Bound"
      >x&#8712;L</a
      ><a name="10361" class="Symbol"
      >)</a
      ><a name="10362"
      > </a
      ><a name="10363" class="Symbol"
      >(</a
      ><a name="10364" href="Stlc.html#4468" class="InductiveConstructor"
      >&#120121;-E</a
      ><a name="10367"
      > </a
      ><a name="10368" href="StlcProp.html#10368" class="Bound"
      >&#8866;L</a
      ><a name="10370"
      > </a
      ><a name="10371" href="StlcProp.html#10371" class="Bound"
      >&#8866;M</a
      ><a name="10373"
      > </a
      ><a name="10374" href="StlcProp.html#10374" class="Bound"
      >&#8866;N</a
      ><a name="10376" class="Symbol"
      >)</a
      ><a name="10377"
      > </a
      ><a name="10378" class="Symbol"
      >=</a
      ><a name="10379"
      > </a
      ><a name="10380" href="StlcProp.html#8638" class="Function"
      >freeLemma</a
      ><a name="10389"
      > </a
      ><a name="10390" href="StlcProp.html#10358" class="Bound"
      >x&#8712;L</a
      ><a name="10393"
      > </a
      ><a name="10394" href="StlcProp.html#10368" class="Bound"
      >&#8866;L</a
      ><a name="10396"
      >
</a
      ><a name="10397" href="StlcProp.html#8638" class="Function"
      >freeLemma</a
      ><a name="10406"
      > </a
      ><a name="10407" class="Symbol"
      >(</a
      ><a name="10408" href="StlcProp.html#7646" class="InductiveConstructor"
      >free-if&#7488;&#8322;</a
      ><a name="10417"
      > </a
      ><a name="10418" href="StlcProp.html#10418" class="Bound"
      >x&#8712;M</a
      ><a name="10421" class="Symbol"
      >)</a
      ><a name="10422"
      > </a
      ><a name="10423" class="Symbol"
      >(</a
      ><a name="10424" href="Stlc.html#4468" class="InductiveConstructor"
      >&#120121;-E</a
      ><a name="10427"
      > </a
      ><a name="10428" href="StlcProp.html#10428" class="Bound"
      >&#8866;L</a
      ><a name="10430"
      > </a
      ><a name="10431" href="StlcProp.html#10431" class="Bound"
      >&#8866;M</a
      ><a name="10433"
      > </a
      ><a name="10434" href="StlcProp.html#10434" class="Bound"
      >&#8866;N</a
      ><a name="10436" class="Symbol"
      >)</a
      ><a name="10437"
      > </a
      ><a name="10438" class="Symbol"
      >=</a
      ><a name="10439"
      > </a
      ><a name="10440" href="StlcProp.html#8638" class="Function"
      >freeLemma</a
      ><a name="10449"
      > </a
      ><a name="10450" href="StlcProp.html#10418" class="Bound"
      >x&#8712;M</a
      ><a name="10453"
      > </a
      ><a name="10454" href="StlcProp.html#10431" class="Bound"
      >&#8866;M</a
      ><a name="10456"
      >
</a
      ><a name="10457" href="StlcProp.html#8638" class="Function"
      >freeLemma</a
      ><a name="10466"
      > </a
      ><a name="10467" class="Symbol"
      >(</a
      ><a name="10468" href="StlcProp.html#7718" class="InductiveConstructor"
      >free-if&#7488;&#8323;</a
      ><a name="10477"
      > </a
      ><a name="10478" href="StlcProp.html#10478" class="Bound"
      >x&#8712;N</a
      ><a name="10481" class="Symbol"
      >)</a
      ><a name="10482"
      > </a
      ><a name="10483" class="Symbol"
      >(</a
      ><a name="10484" href="Stlc.html#4468" class="InductiveConstructor"
      >&#120121;-E</a
      ><a name="10487"
      > </a
      ><a name="10488" href="StlcProp.html#10488" class="Bound"
      >&#8866;L</a
      ><a name="10490"
      > </a
      ><a name="10491" href="StlcProp.html#10491" class="Bound"
      >&#8866;M</a
      ><a name="10493"
      > </a
      ><a name="10494" href="StlcProp.html#10494" class="Bound"
      >&#8866;N</a
      ><a name="10496" class="Symbol"
      >)</a
      ><a name="10497"
      > </a
      ><a name="10498" class="Symbol"
      >=</a
      ><a name="10499"
      > </a
      ><a name="10500" href="StlcProp.html#8638" class="Function"
      >freeLemma</a
      ><a name="10509"
      > </a
      ><a name="10510" href="StlcProp.html#10478" class="Bound"
      >x&#8712;N</a
      ><a name="10513"
      > </a
      ><a name="10514" href="StlcProp.html#10494" class="Bound"
      >&#8866;N</a
      ><a name="10516"
      >
</a
      ><a name="10517" href="StlcProp.html#8638" class="Function"
      >freeLemma</a
      ><a name="10526"
      > </a
      ><a name="10527" class="Symbol"
      >(</a
      ><a name="10528" href="StlcProp.html#7390" class="InductiveConstructor"
      >free-&#955;&#7488;</a
      ><a name="10535"
      > </a
      ><a name="10536" class="Symbol"
      >{</a
      ><a name="10537" href="StlcProp.html#10537" class="Bound"
      >x</a
      ><a name="10538" class="Symbol"
      >}</a
      ><a name="10539"
      > </a
      ><a name="10540" class="Symbol"
      >{</a
      ><a name="10541" href="StlcProp.html#10541" class="Bound"
      >y</a
      ><a name="10542" class="Symbol"
      >}</a
      ><a name="10543"
      > </a
      ><a name="10544" href="StlcProp.html#10544" class="Bound"
      >y&#8802;x</a
      ><a name="10547"
      > </a
      ><a name="10548" href="StlcProp.html#10548" class="Bound"
      >x&#8712;N</a
      ><a name="10551" class="Symbol"
      >)</a
      ><a name="10552"
      > </a
      ><a name="10553" class="Symbol"
      >(</a
      ><a name="10554" href="Stlc.html#4233" class="InductiveConstructor"
      >&#8658;-I</a
      ><a name="10557"
      > </a
      ><a name="10558" href="StlcProp.html#10558" class="Bound"
      >&#8866;N</a
      ><a name="10560" class="Symbol"
      >)</a
      ><a name="10561"
      > </a
      ><a name="10562" class="Keyword"
      >with</a
      ><a name="10566"
      > </a
      ><a name="10567" href="StlcProp.html#8638" class="Function"
      >freeLemma</a
      ><a name="10576"
      > </a
      ><a name="10577" href="StlcProp.html#10548" class="Bound"
      >x&#8712;N</a
      ><a name="10580"
      > </a
      ><a name="10581" href="StlcProp.html#10558" class="Bound"
      >&#8866;N</a
      ><a name="10583"
      >
</a
      ><a name="10584" class="Symbol"
      >...</a
      ><a name="10587"
      > </a
      ><a name="10588" class="Symbol"
      >|</a
      ><a name="10589"
      > </a
      ><a name="10590" href="StlcProp.html#10590" class="Bound"
      >&#915;x=justC</a
      ><a name="10598"
      > </a
      ><a name="10599" class="Keyword"
      >with</a
      ><a name="10603"
      > </a
      ><a name="10604" href="StlcProp.html#10541" class="Bound"
      >y</a
      ><a name="10605"
      > </a
      ><a name="10606" href="Maps.html#2558" class="Function Operator"
      >&#8799;</a
      ><a name="10607"
      > </a
      ><a name="10608" href="StlcProp.html#10537" class="Bound"
      >x</a
      ><a name="10609"
      >
</a
      ><a name="10610" class="Symbol"
      >...</a
      ><a name="10613"
      > </a
      ><a name="10614" class="Symbol"
      >|</a
      ><a name="10615"
      > </a
      ><a name="10616" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#520" class="InductiveConstructor"
      >yes</a
      ><a name="10619"
      > </a
      ><a name="10620" href="StlcProp.html#10620" class="Bound"
      >y&#8801;x</a
      ><a name="10623"
      > </a
      ><a name="10624" class="Symbol"
      >=</a
      ><a name="10625"
      > </a
      ><a name="10626" href="https://agda.github.io/agda-stdlib/Data.Empty.html#348" class="Function"
      >&#8869;-elim</a
      ><a name="10632"
      > </a
      ><a name="10633" class="Symbol"
      >(</a
      ><a name="10634" href="StlcProp.html#10544" class="Bound"
      >y&#8802;x</a
      ><a name="10637"
      > </a
      ><a name="10638" href="StlcProp.html#10620" class="Bound"
      >y&#8801;x</a
      ><a name="10641" class="Symbol"
      >)</a
      ><a name="10642"
      >
</a
      ><a name="10643" class="Symbol"
      >...</a
      ><a name="10646"
      > </a
      ><a name="10647" class="Symbol"
      >|</a
      ><a name="10648"
      > </a
      ><a name="10649" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#547" class="InductiveConstructor"
      >no</a
      ><a name="10651"
      >  </a
      ><a name="10653" class="Symbol"
      >_</a
      ><a name="10654"
      >   </a
      ><a name="10657" class="Symbol"
      >=</a
      ><a name="10658"
      > </a
      ><a name="10659" href="StlcProp.html#10590" class="Bound"
      >&#915;x=justC</a
      >

</pre>

[A subtle point: if the first argument of `free-λᵀ` was of type
`x ≢ y` rather than of type `y ≢ x`, then the type of the
term `Γx=justC` would not simplify properly.]

Next, we'll need the fact that any term `M` which is well typed in
the empty context is closed (it has no free variables).

#### Exercise: 2 stars, optional (∅⊢-closed)

<pre class="Agda">

<a name="11032" class="Keyword"
      >postulate</a
      ><a name="11041"
      >
  </a
      ><a name="11044" href="StlcProp.html#11044" class="Postulate"
      >&#8709;&#8866;-closed</a
      ><a name="11053"
      > </a
      ><a name="11054" class="Symbol"
      >:</a
      ><a name="11055"
      > </a
      ><a name="11056" class="Symbol"
      >&#8704;</a
      ><a name="11057"
      > </a
      ><a name="11058" class="Symbol"
      >{</a
      ><a name="11059" href="StlcProp.html#11059" class="Bound"
      >M</a
      ><a name="11060"
      > </a
      ><a name="11061" href="StlcProp.html#11061" class="Bound"
      >A</a
      ><a name="11062" class="Symbol"
      >}</a
      ><a name="11063"
      > </a
      ><a name="11064" class="Symbol"
      >&#8594;</a
      ><a name="11065"
      > </a
      ><a name="11066" href="Maps.html#10360" class="Function"
      >&#8709;</a
      ><a name="11067"
      > </a
      ><a name="11068" href="Stlc.html#4132" class="Datatype Operator"
      >&#8866;</a
      ><a name="11069"
      > </a
      ><a name="11070" href="StlcProp.html#11059" class="Bound"
      >M</a
      ><a name="11071"
      > </a
      ><a name="11072" href="Stlc.html#4132" class="Datatype Operator"
      >&#8712;</a
      ><a name="11073"
      > </a
      ><a name="11074" href="StlcProp.html#11061" class="Bound"
      >A</a
      ><a name="11075"
      > </a
      ><a name="11076" class="Symbol"
      >&#8594;</a
      ><a name="11077"
      > </a
      ><a name="11078" href="StlcProp.html#7879" class="Function"
      >closed</a
      ><a name="11084"
      > </a
      ><a name="11085" href="StlcProp.html#11059" class="Bound"
      >M</a
      >

</pre>

<div class="hidden">
<pre class="Agda">

<a name="11133" href="StlcProp.html#11133" class="Function"
      >contradiction</a
      ><a name="11146"
      > </a
      ><a name="11147" class="Symbol"
      >:</a
      ><a name="11148"
      > </a
      ><a name="11149" class="Symbol"
      >&#8704;</a
      ><a name="11150"
      > </a
      ><a name="11151" class="Symbol"
      >{</a
      ><a name="11152" href="StlcProp.html#11152" class="Bound"
      >X</a
      ><a name="11153"
      > </a
      ><a name="11154" class="Symbol"
      >:</a
      ><a name="11155"
      > </a
      ><a name="11156" class="PrimitiveType"
      >Set</a
      ><a name="11159" class="Symbol"
      >}</a
      ><a name="11160"
      > </a
      ><a name="11161" class="Symbol"
      >&#8594;</a
      ><a name="11162"
      > </a
      ><a name="11163" class="Symbol"
      >&#8704;</a
      ><a name="11164"
      > </a
      ><a name="11165" class="Symbol"
      >{</a
      ><a name="11166" href="StlcProp.html#11166" class="Bound"
      >x</a
      ><a name="11167"
      > </a
      ><a name="11168" class="Symbol"
      >:</a
      ><a name="11169"
      > </a
      ><a name="11170" href="StlcProp.html#11152" class="Bound"
      >X</a
      ><a name="11171" class="Symbol"
      >}</a
      ><a name="11172"
      > </a
      ><a name="11173" class="Symbol"
      >&#8594;</a
      ><a name="11174"
      > </a
      ><a name="11175" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#414" class="Function Operator"
      >&#172;</a
      ><a name="11176"
      > </a
      ><a name="11177" class="Symbol"
      >(</a
      ><a name="11178" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >_&#8801;_</a
      ><a name="11181"
      > </a
      ><a name="11182" class="Symbol"
      >{</a
      ><a name="11183" class="Argument"
      >A</a
      ><a name="11184"
      > </a
      ><a name="11185" class="Symbol"
      >=</a
      ><a name="11186"
      > </a
      ><a name="11187" href="https://agda.github.io/agda-stdlib/Data.Maybe.Base.html#335" class="Datatype"
      >Maybe</a
      ><a name="11192"
      > </a
      ><a name="11193" href="StlcProp.html#11152" class="Bound"
      >X</a
      ><a name="11194" class="Symbol"
      >}</a
      ><a name="11195"
      > </a
      ><a name="11196" class="Symbol"
      >(</a
      ><a name="11197" href="https://agda.github.io/agda-stdlib/Data.Maybe.Base.html#373" class="InductiveConstructor"
      >just</a
      ><a name="11201"
      > </a
      ><a name="11202" href="StlcProp.html#11166" class="Bound"
      >x</a
      ><a name="11203" class="Symbol"
      >)</a
      ><a name="11204"
      > </a
      ><a name="11205" href="https://agda.github.io/agda-stdlib/Data.Maybe.Base.html#403" class="InductiveConstructor"
      >nothing</a
      ><a name="11212" class="Symbol"
      >)</a
      ><a name="11213"
      >
</a
      ><a name="11214" href="StlcProp.html#11133" class="Function"
      >contradiction</a
      ><a name="11227"
      > </a
      ><a name="11228" class="Symbol"
      >()</a
      ><a name="11230"
      >

</a
      ><a name="11232" href="StlcProp.html#11232" class="Function"
      >&#8709;&#8866;-closed&#8242;</a
      ><a name="11242"
      > </a
      ><a name="11243" class="Symbol"
      >:</a
      ><a name="11244"
      > </a
      ><a name="11245" class="Symbol"
      >&#8704;</a
      ><a name="11246"
      > </a
      ><a name="11247" class="Symbol"
      >{</a
      ><a name="11248" href="StlcProp.html#11248" class="Bound"
      >M</a
      ><a name="11249"
      > </a
      ><a name="11250" href="StlcProp.html#11250" class="Bound"
      >A</a
      ><a name="11251" class="Symbol"
      >}</a
      ><a name="11252"
      > </a
      ><a name="11253" class="Symbol"
      >&#8594;</a
      ><a name="11254"
      > </a
      ><a name="11255" href="Maps.html#10360" class="Function"
      >&#8709;</a
      ><a name="11256"
      > </a
      ><a name="11257" href="Stlc.html#4132" class="Datatype Operator"
      >&#8866;</a
      ><a name="11258"
      > </a
      ><a name="11259" href="StlcProp.html#11248" class="Bound"
      >M</a
      ><a name="11260"
      > </a
      ><a name="11261" href="Stlc.html#4132" class="Datatype Operator"
      >&#8712;</a
      ><a name="11262"
      > </a
      ><a name="11263" href="StlcProp.html#11250" class="Bound"
      >A</a
      ><a name="11264"
      > </a
      ><a name="11265" class="Symbol"
      >&#8594;</a
      ><a name="11266"
      > </a
      ><a name="11267" href="StlcProp.html#7879" class="Function"
      >closed</a
      ><a name="11273"
      > </a
      ><a name="11274" href="StlcProp.html#11248" class="Bound"
      >M</a
      ><a name="11275"
      >
</a
      ><a name="11276" href="StlcProp.html#11232" class="Function"
      >&#8709;&#8866;-closed&#8242;</a
      ><a name="11286"
      > </a
      ><a name="11287" class="Symbol"
      >{</a
      ><a name="11288" href="StlcProp.html#11288" class="Bound"
      >M</a
      ><a name="11289" class="Symbol"
      >}</a
      ><a name="11290"
      > </a
      ><a name="11291" class="Symbol"
      >{</a
      ><a name="11292" href="StlcProp.html#11292" class="Bound"
      >A</a
      ><a name="11293" class="Symbol"
      >}</a
      ><a name="11294"
      > </a
      ><a name="11295" href="StlcProp.html#11295" class="Bound"
      >&#8866;M</a
      ><a name="11297"
      > </a
      ><a name="11298" class="Symbol"
      >{</a
      ><a name="11299" href="StlcProp.html#11299" class="Bound"
      >x</a
      ><a name="11300" class="Symbol"
      >}</a
      ><a name="11301"
      > </a
      ><a name="11302" href="StlcProp.html#11302" class="Bound"
      >x&#8712;M</a
      ><a name="11305"
      > </a
      ><a name="11306" class="Keyword"
      >with</a
      ><a name="11310"
      > </a
      ><a name="11311" href="StlcProp.html#8638" class="Function"
      >freeLemma</a
      ><a name="11320"
      > </a
      ><a name="11321" href="StlcProp.html#11302" class="Bound"
      >x&#8712;M</a
      ><a name="11324"
      > </a
      ><a name="11325" href="StlcProp.html#11295" class="Bound"
      >&#8866;M</a
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
      ><a name="11334" class="Symbol"
      >(</a
      ><a name="11335" href="StlcProp.html#11335" class="Bound"
      >B</a
      ><a name="11336"
      > </a
      ><a name="11337" href="https://agda.github.io/agda-stdlib/Data.Product.html#509" class="InductiveConstructor Operator"
      >,</a
      ><a name="11338"
      > </a
      ><a name="11339" href="StlcProp.html#11339" class="Bound"
      >&#8709;x&#8801;justB</a
      ><a name="11347" class="Symbol"
      >)</a
      ><a name="11348"
      > </a
      ><a name="11349" class="Symbol"
      >=</a
      ><a name="11350"
      > </a
      ><a name="11351" href="StlcProp.html#11133" class="Function"
      >contradiction</a
      ><a name="11364"
      > </a
      ><a name="11365" class="Symbol"
      >(</a
      ><a name="11366" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.Core.html#632" class="Function"
      >trans</a
      ><a name="11371"
      > </a
      ><a name="11372" class="Symbol"
      >(</a
      ><a name="11373" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.Core.html#565" class="Function"
      >sym</a
      ><a name="11376"
      > </a
      ><a name="11377" href="StlcProp.html#11339" class="Bound"
      >&#8709;x&#8801;justB</a
      ><a name="11385" class="Symbol"
      >)</a
      ><a name="11386"
      > </a
      ><a name="11387" class="Symbol"
      >(</a
      ><a name="11388" href="Maps.html#10669" class="Function"
      >apply-&#8709;</a
      ><a name="11395"
      > </a
      ><a name="11396" href="StlcProp.html#11299" class="Bound"
      >x</a
      ><a name="11397" class="Symbol"
      >))</a
      >

</pre>
</div>

Sometimes, when we have a proof `Γ ⊢ M ∈ A`, we will need to
replace `Γ` by a different context `Γ′`.  When is it safe
to do this?  Intuitively, it must at least be the case that
`Γ′` assigns the same types as `Γ` to all the variables
that appear free in `M`. In fact, this is the only condition that
is needed.

<pre class="Agda">

<a name="11745" href="StlcProp.html#11745" class="Function"
      >weaken</a
      ><a name="11751"
      > </a
      ><a name="11752" class="Symbol"
      >:</a
      ><a name="11753"
      > </a
      ><a name="11754" class="Symbol"
      >&#8704;</a
      ><a name="11755"
      > </a
      ><a name="11756" class="Symbol"
      >{</a
      ><a name="11757" href="StlcProp.html#11757" class="Bound"
      >&#915;</a
      ><a name="11758"
      > </a
      ><a name="11759" href="StlcProp.html#11759" class="Bound"
      >&#915;&#8242;</a
      ><a name="11761"
      > </a
      ><a name="11762" href="StlcProp.html#11762" class="Bound"
      >M</a
      ><a name="11763"
      > </a
      ><a name="11764" href="StlcProp.html#11764" class="Bound"
      >A</a
      ><a name="11765" class="Symbol"
      >}</a
      ><a name="11766"
      >
        </a
      ><a name="11775" class="Symbol"
      >&#8594;</a
      ><a name="11776"
      > </a
      ><a name="11777" class="Symbol"
      >(&#8704;</a
      ><a name="11779"
      > </a
      ><a name="11780" class="Symbol"
      >{</a
      ><a name="11781" href="StlcProp.html#11781" class="Bound"
      >x</a
      ><a name="11782" class="Symbol"
      >}</a
      ><a name="11783"
      > </a
      ><a name="11784" class="Symbol"
      >&#8594;</a
      ><a name="11785"
      > </a
      ><a name="11786" href="StlcProp.html#11781" class="Bound"
      >x</a
      ><a name="11787"
      > </a
      ><a name="11788" href="StlcProp.html#7314" class="Datatype Operator"
      >FreeIn</a
      ><a name="11794"
      > </a
      ><a name="11795" href="StlcProp.html#11762" class="Bound"
      >M</a
      ><a name="11796"
      > </a
      ><a name="11797" class="Symbol"
      >&#8594;</a
      ><a name="11798"
      > </a
      ><a name="11799" href="StlcProp.html#11757" class="Bound"
      >&#915;</a
      ><a name="11800"
      > </a
      ><a name="11801" href="StlcProp.html#11781" class="Bound"
      >x</a
      ><a name="11802"
      > </a
      ><a name="11803" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="11804"
      > </a
      ><a name="11805" href="StlcProp.html#11759" class="Bound"
      >&#915;&#8242;</a
      ><a name="11807"
      > </a
      ><a name="11808" href="StlcProp.html#11781" class="Bound"
      >x</a
      ><a name="11809" class="Symbol"
      >)</a
      ><a name="11810"
      >
        </a
      ><a name="11819" class="Symbol"
      >&#8594;</a
      ><a name="11820"
      > </a
      ><a name="11821" href="StlcProp.html#11757" class="Bound"
      >&#915;</a
      ><a name="11822"
      >  </a
      ><a name="11824" href="Stlc.html#4132" class="Datatype Operator"
      >&#8866;</a
      ><a name="11825"
      > </a
      ><a name="11826" href="StlcProp.html#11762" class="Bound"
      >M</a
      ><a name="11827"
      > </a
      ><a name="11828" href="Stlc.html#4132" class="Datatype Operator"
      >&#8712;</a
      ><a name="11829"
      > </a
      ><a name="11830" href="StlcProp.html#11764" class="Bound"
      >A</a
      ><a name="11831"
      >
        </a
      ><a name="11840" class="Symbol"
      >&#8594;</a
      ><a name="11841"
      > </a
      ><a name="11842" href="StlcProp.html#11759" class="Bound"
      >&#915;&#8242;</a
      ><a name="11844"
      > </a
      ><a name="11845" href="Stlc.html#4132" class="Datatype Operator"
      >&#8866;</a
      ><a name="11846"
      > </a
      ><a name="11847" href="StlcProp.html#11762" class="Bound"
      >M</a
      ><a name="11848"
      > </a
      ><a name="11849" href="Stlc.html#4132" class="Datatype Operator"
      >&#8712;</a
      ><a name="11850"
      > </a
      ><a name="11851" href="StlcProp.html#11764" class="Bound"
      >A</a
      >

</pre>

_Proof_: By induction on the derivation of
`Γ ⊢ M ∈ A`.

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

<pre class="Agda">

<a name="14018" href="StlcProp.html#11745" class="Function"
      >weaken</a
      ><a name="14024"
      > </a
      ><a name="14025" href="StlcProp.html#14025" class="Bound"
      >&#915;~&#915;&#8242;</a
      ><a name="14029"
      > </a
      ><a name="14030" class="Symbol"
      >(</a
      ><a name="14031" href="Stlc.html#4176" class="InductiveConstructor"
      >Ax</a
      ><a name="14033"
      > </a
      ><a name="14034" href="StlcProp.html#14034" class="Bound"
      >&#915;x&#8801;justA</a
      ><a name="14042" class="Symbol"
      >)</a
      ><a name="14043"
      > </a
      ><a name="14044" class="Keyword"
      >rewrite</a
      ><a name="14051"
      > </a
      ><a name="14052" class="Symbol"
      >(</a
      ><a name="14053" href="StlcProp.html#14025" class="Bound"
      >&#915;~&#915;&#8242;</a
      ><a name="14057"
      > </a
      ><a name="14058" href="StlcProp.html#7349" class="InductiveConstructor"
      >free-var&#7488;</a
      ><a name="14067" class="Symbol"
      >)</a
      ><a name="14068"
      > </a
      ><a name="14069" class="Symbol"
      >=</a
      ><a name="14070"
      > </a
      ><a name="14071" href="Stlc.html#4176" class="InductiveConstructor"
      >Ax</a
      ><a name="14073"
      > </a
      ><a name="14074" href="StlcProp.html#14034" class="Bound"
      >&#915;x&#8801;justA</a
      ><a name="14082"
      >
</a
      ><a name="14083" href="StlcProp.html#11745" class="Function"
      >weaken</a
      ><a name="14089"
      > </a
      ><a name="14090" class="Symbol"
      >{</a
      ><a name="14091" href="StlcProp.html#14091" class="Bound"
      >&#915;</a
      ><a name="14092" class="Symbol"
      >}</a
      ><a name="14093"
      > </a
      ><a name="14094" class="Symbol"
      >{</a
      ><a name="14095" href="StlcProp.html#14095" class="Bound"
      >&#915;&#8242;</a
      ><a name="14097" class="Symbol"
      >}</a
      ><a name="14098"
      > </a
      ><a name="14099" class="Symbol"
      >{</a
      ><a name="14100" href="Stlc.html#1070" class="InductiveConstructor Operator"
      >&#955;&#7488;</a
      ><a name="14102"
      > </a
      ><a name="14103" href="StlcProp.html#14103" class="Bound"
      >x</a
      ><a name="14104"
      > </a
      ><a name="14105" href="Stlc.html#1070" class="InductiveConstructor Operator"
      >&#8712;</a
      ><a name="14106"
      > </a
      ><a name="14107" href="StlcProp.html#14107" class="Bound"
      >A</a
      ><a name="14108"
      > </a
      ><a name="14109" href="Stlc.html#1070" class="InductiveConstructor Operator"
      >&#8658;</a
      ><a name="14110"
      > </a
      ><a name="14111" href="StlcProp.html#14111" class="Bound"
      >N</a
      ><a name="14112" class="Symbol"
      >}</a
      ><a name="14113"
      > </a
      ><a name="14114" href="StlcProp.html#14114" class="Bound"
      >&#915;~&#915;&#8242;</a
      ><a name="14118"
      > </a
      ><a name="14119" class="Symbol"
      >(</a
      ><a name="14120" href="Stlc.html#4233" class="InductiveConstructor"
      >&#8658;-I</a
      ><a name="14123"
      > </a
      ><a name="14124" href="StlcProp.html#14124" class="Bound"
      >&#8866;N</a
      ><a name="14126" class="Symbol"
      >)</a
      ><a name="14127"
      > </a
      ><a name="14128" class="Symbol"
      >=</a
      ><a name="14129"
      > </a
      ><a name="14130" href="Stlc.html#4233" class="InductiveConstructor"
      >&#8658;-I</a
      ><a name="14133"
      > </a
      ><a name="14134" class="Symbol"
      >(</a
      ><a name="14135" href="StlcProp.html#11745" class="Function"
      >weaken</a
      ><a name="14141"
      > </a
      ><a name="14142" href="StlcProp.html#14163" class="Function"
      >&#915;x~&#915;&#8242;x</a
      ><a name="14148"
      > </a
      ><a name="14149" href="StlcProp.html#14124" class="Bound"
      >&#8866;N</a
      ><a name="14151" class="Symbol"
      >)</a
      ><a name="14152"
      >
  </a
      ><a name="14155" class="Keyword"
      >where</a
      ><a name="14160"
      >
  </a
      ><a name="14163" href="StlcProp.html#14163" class="Function"
      >&#915;x~&#915;&#8242;x</a
      ><a name="14169"
      > </a
      ><a name="14170" class="Symbol"
      >:</a
      ><a name="14171"
      > </a
      ><a name="14172" class="Symbol"
      >&#8704;</a
      ><a name="14173"
      > </a
      ><a name="14174" class="Symbol"
      >{</a
      ><a name="14175" href="StlcProp.html#14175" class="Bound"
      >y</a
      ><a name="14176" class="Symbol"
      >}</a
      ><a name="14177"
      > </a
      ><a name="14178" class="Symbol"
      >&#8594;</a
      ><a name="14179"
      > </a
      ><a name="14180" href="StlcProp.html#14175" class="Bound"
      >y</a
      ><a name="14181"
      > </a
      ><a name="14182" href="StlcProp.html#7314" class="Datatype Operator"
      >FreeIn</a
      ><a name="14188"
      > </a
      ><a name="14189" href="StlcProp.html#14111" class="Bound"
      >N</a
      ><a name="14190"
      > </a
      ><a name="14191" class="Symbol"
      >&#8594;</a
      ><a name="14192"
      > </a
      ><a name="14193" class="Symbol"
      >(</a
      ><a name="14194" href="StlcProp.html#14091" class="Bound"
      >&#915;</a
      ><a name="14195"
      > </a
      ><a name="14196" href="Maps.html#10464" class="Function Operator"
      >,</a
      ><a name="14197"
      > </a
      ><a name="14198" href="StlcProp.html#14103" class="Bound"
      >x</a
      ><a name="14199"
      > </a
      ><a name="14200" href="Maps.html#10464" class="Function Operator"
      >&#8614;</a
      ><a name="14201"
      > </a
      ><a name="14202" href="StlcProp.html#14107" class="Bound"
      >A</a
      ><a name="14203" class="Symbol"
      >)</a
      ><a name="14204"
      > </a
      ><a name="14205" href="StlcProp.html#14175" class="Bound"
      >y</a
      ><a name="14206"
      > </a
      ><a name="14207" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="14208"
      > </a
      ><a name="14209" class="Symbol"
      >(</a
      ><a name="14210" href="StlcProp.html#14095" class="Bound"
      >&#915;&#8242;</a
      ><a name="14212"
      > </a
      ><a name="14213" href="Maps.html#10464" class="Function Operator"
      >,</a
      ><a name="14214"
      > </a
      ><a name="14215" href="StlcProp.html#14103" class="Bound"
      >x</a
      ><a name="14216"
      > </a
      ><a name="14217" href="Maps.html#10464" class="Function Operator"
      >&#8614;</a
      ><a name="14218"
      > </a
      ><a name="14219" href="StlcProp.html#14107" class="Bound"
      >A</a
      ><a name="14220" class="Symbol"
      >)</a
      ><a name="14221"
      > </a
      ><a name="14222" href="StlcProp.html#14175" class="Bound"
      >y</a
      ><a name="14223"
      >
  </a
      ><a name="14226" href="StlcProp.html#14163" class="Function"
      >&#915;x~&#915;&#8242;x</a
      ><a name="14232"
      > </a
      ><a name="14233" class="Symbol"
      >{</a
      ><a name="14234" href="StlcProp.html#14234" class="Bound"
      >y</a
      ><a name="14235" class="Symbol"
      >}</a
      ><a name="14236"
      > </a
      ><a name="14237" href="StlcProp.html#14237" class="Bound"
      >y&#8712;N</a
      ><a name="14240"
      > </a
      ><a name="14241" class="Keyword"
      >with</a
      ><a name="14245"
      > </a
      ><a name="14246" href="StlcProp.html#14103" class="Bound"
      >x</a
      ><a name="14247"
      > </a
      ><a name="14248" href="Maps.html#2558" class="Function Operator"
      >&#8799;</a
      ><a name="14249"
      > </a
      ><a name="14250" href="StlcProp.html#14234" class="Bound"
      >y</a
      ><a name="14251"
      >
  </a
      ><a name="14254" class="Symbol"
      >...</a
      ><a name="14257"
      > </a
      ><a name="14258" class="Symbol"
      >|</a
      ><a name="14259"
      > </a
      ><a name="14260" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#520" class="InductiveConstructor"
      >yes</a
      ><a name="14263"
      > </a
      ><a name="14264" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="14268"
      > </a
      ><a name="14269" class="Symbol"
      >=</a
      ><a name="14270"
      > </a
      ><a name="14271" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="14275"
      >
  </a
      ><a name="14278" class="Symbol"
      >...</a
      ><a name="14281"
      > </a
      ><a name="14282" class="Symbol"
      >|</a
      ><a name="14283"
      > </a
      ><a name="14284" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#547" class="InductiveConstructor"
      >no</a
      ><a name="14286"
      >  </a
      ><a name="14288" href="StlcProp.html#14288" class="Bound"
      >x&#8802;y</a
      ><a name="14291"
      >  </a
      ><a name="14293" class="Symbol"
      >=</a
      ><a name="14294"
      > </a
      ><a name="14295" href="StlcProp.html#14114" class="Bound"
      >&#915;~&#915;&#8242;</a
      ><a name="14299"
      > </a
      ><a name="14300" class="Symbol"
      >(</a
      ><a name="14301" href="StlcProp.html#7390" class="InductiveConstructor"
      >free-&#955;&#7488;</a
      ><a name="14308"
      > </a
      ><a name="14309" href="StlcProp.html#14288" class="Bound"
      >x&#8802;y</a
      ><a name="14312"
      > </a
      ><a name="14313" href="StlcProp.html#14237" class="Bound"
      >y&#8712;N</a
      ><a name="14316" class="Symbol"
      >)</a
      ><a name="14317"
      >
</a
      ><a name="14318" href="StlcProp.html#11745" class="Function"
      >weaken</a
      ><a name="14324"
      > </a
      ><a name="14325" href="StlcProp.html#14325" class="Bound"
      >&#915;~&#915;&#8242;</a
      ><a name="14329"
      > </a
      ><a name="14330" class="Symbol"
      >(</a
      ><a name="14331" href="Stlc.html#4316" class="InductiveConstructor"
      >&#8658;-E</a
      ><a name="14334"
      > </a
      ><a name="14335" href="StlcProp.html#14335" class="Bound"
      >&#8866;L</a
      ><a name="14337"
      > </a
      ><a name="14338" href="StlcProp.html#14338" class="Bound"
      >&#8866;M</a
      ><a name="14340" class="Symbol"
      >)</a
      ><a name="14341"
      > </a
      ><a name="14342" class="Symbol"
      >=</a
      ><a name="14343"
      > </a
      ><a name="14344" href="Stlc.html#4316" class="InductiveConstructor"
      >&#8658;-E</a
      ><a name="14347"
      > </a
      ><a name="14348" class="Symbol"
      >(</a
      ><a name="14349" href="StlcProp.html#11745" class="Function"
      >weaken</a
      ><a name="14355"
      > </a
      ><a name="14356" class="Symbol"
      >(</a
      ><a name="14357" href="StlcProp.html#14325" class="Bound"
      >&#915;~&#915;&#8242;</a
      ><a name="14361"
      > </a
      ><a name="14362" href="https://agda.github.io/agda-stdlib/Function.html#713" class="Function Operator"
      >&#8728;</a
      ><a name="14363"
      > </a
      ><a name="14364" href="StlcProp.html#7462" class="InductiveConstructor"
      >free-&#183;&#7488;&#8321;</a
      ><a name="14372" class="Symbol"
      >)</a
      ><a name="14373"
      >  </a
      ><a name="14375" href="StlcProp.html#14335" class="Bound"
      >&#8866;L</a
      ><a name="14377" class="Symbol"
      >)</a
      ><a name="14378"
      > </a
      ><a name="14379" class="Symbol"
      >(</a
      ><a name="14380" href="StlcProp.html#11745" class="Function"
      >weaken</a
      ><a name="14386"
      > </a
      ><a name="14387" class="Symbol"
      >(</a
      ><a name="14388" href="StlcProp.html#14325" class="Bound"
      >&#915;~&#915;&#8242;</a
      ><a name="14392"
      > </a
      ><a name="14393" href="https://agda.github.io/agda-stdlib/Function.html#713" class="Function Operator"
      >&#8728;</a
      ><a name="14394"
      > </a
      ><a name="14395" href="StlcProp.html#7518" class="InductiveConstructor"
      >free-&#183;&#7488;&#8322;</a
      ><a name="14403" class="Symbol"
      >)</a
      ><a name="14404"
      > </a
      ><a name="14405" href="StlcProp.html#14338" class="Bound"
      >&#8866;M</a
      ><a name="14407" class="Symbol"
      >)</a
      ><a name="14408"
      > 
</a
      ><a name="14410" href="StlcProp.html#11745" class="Function"
      >weaken</a
      ><a name="14416"
      > </a
      ><a name="14417" href="StlcProp.html#14417" class="Bound"
      >&#915;~&#915;&#8242;</a
      ><a name="14421"
      > </a
      ><a name="14422" href="Stlc.html#4397" class="InductiveConstructor"
      >&#120121;-I&#8321;</a
      ><a name="14426"
      > </a
      ><a name="14427" class="Symbol"
      >=</a
      ><a name="14428"
      > </a
      ><a name="14429" href="Stlc.html#4397" class="InductiveConstructor"
      >&#120121;-I&#8321;</a
      ><a name="14433"
      >
</a
      ><a name="14434" href="StlcProp.html#11745" class="Function"
      >weaken</a
      ><a name="14440"
      > </a
      ><a name="14441" href="StlcProp.html#14441" class="Bound"
      >&#915;~&#915;&#8242;</a
      ><a name="14445"
      > </a
      ><a name="14446" href="Stlc.html#4432" class="InductiveConstructor"
      >&#120121;-I&#8322;</a
      ><a name="14450"
      > </a
      ><a name="14451" class="Symbol"
      >=</a
      ><a name="14452"
      > </a
      ><a name="14453" href="Stlc.html#4432" class="InductiveConstructor"
      >&#120121;-I&#8322;</a
      ><a name="14457"
      >
</a
      ><a name="14458" href="StlcProp.html#11745" class="Function"
      >weaken</a
      ><a name="14464"
      > </a
      ><a name="14465" href="StlcProp.html#14465" class="Bound"
      >&#915;~&#915;&#8242;</a
      ><a name="14469"
      > </a
      ><a name="14470" class="Symbol"
      >(</a
      ><a name="14471" href="Stlc.html#4468" class="InductiveConstructor"
      >&#120121;-E</a
      ><a name="14474"
      > </a
      ><a name="14475" href="StlcProp.html#14475" class="Bound"
      >&#8866;L</a
      ><a name="14477"
      > </a
      ><a name="14478" href="StlcProp.html#14478" class="Bound"
      >&#8866;M</a
      ><a name="14480"
      > </a
      ><a name="14481" href="StlcProp.html#14481" class="Bound"
      >&#8866;N</a
      ><a name="14483" class="Symbol"
      >)</a
      ><a name="14484"
      >
  </a
      ><a name="14487" class="Symbol"
      >=</a
      ><a name="14488"
      > </a
      ><a name="14489" href="Stlc.html#4468" class="InductiveConstructor"
      >&#120121;-E</a
      ><a name="14492"
      > </a
      ><a name="14493" class="Symbol"
      >(</a
      ><a name="14494" href="StlcProp.html#11745" class="Function"
      >weaken</a
      ><a name="14500"
      > </a
      ><a name="14501" class="Symbol"
      >(</a
      ><a name="14502" href="StlcProp.html#14465" class="Bound"
      >&#915;~&#915;&#8242;</a
      ><a name="14506"
      > </a
      ><a name="14507" href="https://agda.github.io/agda-stdlib/Function.html#713" class="Function Operator"
      >&#8728;</a
      ><a name="14508"
      > </a
      ><a name="14509" href="StlcProp.html#7574" class="InductiveConstructor"
      >free-if&#7488;&#8321;</a
      ><a name="14518" class="Symbol"
      >)</a
      ><a name="14519"
      > </a
      ><a name="14520" href="StlcProp.html#14475" class="Bound"
      >&#8866;L</a
      ><a name="14522" class="Symbol"
      >)</a
      ><a name="14523"
      > </a
      ><a name="14524" class="Symbol"
      >(</a
      ><a name="14525" href="StlcProp.html#11745" class="Function"
      >weaken</a
      ><a name="14531"
      > </a
      ><a name="14532" class="Symbol"
      >(</a
      ><a name="14533" href="StlcProp.html#14465" class="Bound"
      >&#915;~&#915;&#8242;</a
      ><a name="14537"
      > </a
      ><a name="14538" href="https://agda.github.io/agda-stdlib/Function.html#713" class="Function Operator"
      >&#8728;</a
      ><a name="14539"
      > </a
      ><a name="14540" href="StlcProp.html#7646" class="InductiveConstructor"
      >free-if&#7488;&#8322;</a
      ><a name="14549" class="Symbol"
      >)</a
      ><a name="14550"
      > </a
      ><a name="14551" href="StlcProp.html#14478" class="Bound"
      >&#8866;M</a
      ><a name="14553" class="Symbol"
      >)</a
      ><a name="14554"
      > </a
      ><a name="14555" class="Symbol"
      >(</a
      ><a name="14556" href="StlcProp.html#11745" class="Function"
      >weaken</a
      ><a name="14562"
      > </a
      ><a name="14563" class="Symbol"
      >(</a
      ><a name="14564" href="StlcProp.html#14465" class="Bound"
      >&#915;~&#915;&#8242;</a
      ><a name="14568"
      > </a
      ><a name="14569" href="https://agda.github.io/agda-stdlib/Function.html#713" class="Function Operator"
      >&#8728;</a
      ><a name="14570"
      > </a
      ><a name="14571" href="StlcProp.html#7718" class="InductiveConstructor"
      >free-if&#7488;&#8323;</a
      ><a name="14580" class="Symbol"
      >)</a
      ><a name="14581"
      > </a
      ><a name="14582" href="StlcProp.html#14481" class="Bound"
      >&#8866;N</a
      ><a name="14584" class="Symbol"
      >)</a
      ><a name="14585"
      >

</a
      ><a name="14587" class="Comment"
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
have a term `N` with a free variable `x`, and suppose we've been
able to assign a type `B` to `N` under the assumption that `x` has
some type `A`.  Also, suppose that we have some other term `V` and
that we've shown that `V` has type `A`.  Then, since `V` satisfies
the assumption we made about `x` when typing `N`, we should be
able to substitute `V` for each of the occurrences of `x` in `N`
and obtain a new term that still has type `B`.

_Lemma_: If `Γ , x ↦ A ⊢ N ∈ B` and `∅ ⊢ V ∈ A`, then
`Γ ⊢ (N [ x := V ]) ∈ B`.

<pre class="Agda">

<a name="15966" href="StlcProp.html#15966" class="Function"
      >preservation-[:=]</a
      ><a name="15983"
      > </a
      ><a name="15984" class="Symbol"
      >:</a
      ><a name="15985"
      > </a
      ><a name="15986" class="Symbol"
      >&#8704;</a
      ><a name="15987"
      > </a
      ><a name="15988" class="Symbol"
      >{</a
      ><a name="15989" href="StlcProp.html#15989" class="Bound"
      >&#915;</a
      ><a name="15990"
      > </a
      ><a name="15991" href="StlcProp.html#15991" class="Bound"
      >x</a
      ><a name="15992"
      > </a
      ><a name="15993" href="StlcProp.html#15993" class="Bound"
      >A</a
      ><a name="15994"
      > </a
      ><a name="15995" href="StlcProp.html#15995" class="Bound"
      >N</a
      ><a name="15996"
      > </a
      ><a name="15997" href="StlcProp.html#15997" class="Bound"
      >B</a
      ><a name="15998"
      > </a
      ><a name="15999" href="StlcProp.html#15999" class="Bound"
      >V</a
      ><a name="16000" class="Symbol"
      >}</a
      ><a name="16001"
      >
                 </a
      ><a name="16019" class="Symbol"
      >&#8594;</a
      ><a name="16020"
      > </a
      ><a name="16021" class="Symbol"
      >(</a
      ><a name="16022" href="StlcProp.html#15989" class="Bound"
      >&#915;</a
      ><a name="16023"
      > </a
      ><a name="16024" href="Maps.html#10464" class="Function Operator"
      >,</a
      ><a name="16025"
      > </a
      ><a name="16026" href="StlcProp.html#15991" class="Bound"
      >x</a
      ><a name="16027"
      > </a
      ><a name="16028" href="Maps.html#10464" class="Function Operator"
      >&#8614;</a
      ><a name="16029"
      > </a
      ><a name="16030" href="StlcProp.html#15993" class="Bound"
      >A</a
      ><a name="16031" class="Symbol"
      >)</a
      ><a name="16032"
      > </a
      ><a name="16033" href="Stlc.html#4132" class="Datatype Operator"
      >&#8866;</a
      ><a name="16034"
      > </a
      ><a name="16035" href="StlcProp.html#15995" class="Bound"
      >N</a
      ><a name="16036"
      > </a
      ><a name="16037" href="Stlc.html#4132" class="Datatype Operator"
      >&#8712;</a
      ><a name="16038"
      > </a
      ><a name="16039" href="StlcProp.html#15997" class="Bound"
      >B</a
      ><a name="16040"
      >
                 </a
      ><a name="16058" class="Symbol"
      >&#8594;</a
      ><a name="16059"
      > </a
      ><a name="16060" href="Maps.html#10360" class="Function"
      >&#8709;</a
      ><a name="16061"
      > </a
      ><a name="16062" href="Stlc.html#4132" class="Datatype Operator"
      >&#8866;</a
      ><a name="16063"
      > </a
      ><a name="16064" href="StlcProp.html#15999" class="Bound"
      >V</a
      ><a name="16065"
      > </a
      ><a name="16066" href="Stlc.html#4132" class="Datatype Operator"
      >&#8712;</a
      ><a name="16067"
      > </a
      ><a name="16068" href="StlcProp.html#15993" class="Bound"
      >A</a
      ><a name="16069"
      >
                 </a
      ><a name="16087" class="Symbol"
      >&#8594;</a
      ><a name="16088"
      > </a
      ><a name="16089" href="StlcProp.html#15989" class="Bound"
      >&#915;</a
      ><a name="16090"
      > </a
      ><a name="16091" href="Stlc.html#4132" class="Datatype Operator"
      >&#8866;</a
      ><a name="16092"
      > </a
      ><a name="16093" class="Symbol"
      >(</a
      ><a name="16094" href="StlcProp.html#15995" class="Bound"
      >N</a
      ><a name="16095"
      > </a
      ><a name="16096" href="Stlc.html#1756" class="Function Operator"
      >[</a
      ><a name="16097"
      > </a
      ><a name="16098" href="StlcProp.html#15991" class="Bound"
      >x</a
      ><a name="16099"
      > </a
      ><a name="16100" href="Stlc.html#1756" class="Function Operator"
      >:=</a
      ><a name="16102"
      > </a
      ><a name="16103" href="StlcProp.html#15999" class="Bound"
      >V</a
      ><a name="16104"
      > </a
      ><a name="16105" href="Stlc.html#1756" class="Function Operator"
      >]</a
      ><a name="16106" class="Symbol"
      >)</a
      ><a name="16107"
      > </a
      ><a name="16108" href="Stlc.html#4132" class="Datatype Operator"
      >&#8712;</a
      ><a name="16109"
      > </a
      ><a name="16110" href="StlcProp.html#15997" class="Bound"
      >B</a
      >

</pre>

One technical subtlety in the statement of the lemma is that
we assign `V` the type `A` in the _empty_ context---in other
words, we assume `V` is closed.  This assumption considerably
simplifies the `λᵀ` case of the proof (compared to assuming
`Γ ⊢ V ∈ A`, which would be the other reasonable assumption
at this point) because the context invariance lemma then tells us
that `V` has type `A` in any context at all---we don't have to
worry about free variables in `V` clashing with the variable being
introduced into the context by `λᵀ`.

The substitution lemma can be viewed as a kind of "commutation"
property.  Intuitively, it says that substitution and typing can
be done in either order: we can either assign types to the terms
`N` and `V` separately (under suitable contexts) and then combine
them using substitution, or we can substitute first and then
assign a type to `N [ x := V ]`---the result is the same either
way.

_Proof_: We show, by induction on `N`, that for all `A` and
`Γ`, if `Γ , x ↦ A \vdash N ∈ B` and `∅ ⊢ V ∈ A`, then
`Γ \vdash N [ x := V ] ∈ B`.

  - If `N` is a variable there are two cases to consider,
    depending on whether `N` is `x` or some other variable.

      - If `N = varᵀ x`, then from the fact that `Γ , x ↦ A ⊢ N ∈ B`
        we conclude that `A = B`.  We must show that `x [ x := V] =
        V` has type `A` under `Γ`, given the assumption that
        `V` has type `A` under the empty context.  This
        follows from context invariance: if a closed term has type
        `A` in the empty context, it has that type in any context.

      - If `N` is some variable `x′` different from `x`, then
        we need only note that `x′` has the same type under `Γ , x ↦ A`
        as under `Γ`.

  - If `N` is an abstraction `λᵀ x′ ∈ A′ ⇒ N′`, then the IH tells us,
    for all `Γ′`́ and `B′`, that if `Γ′ , x ↦ A ⊢ N′ ∈ B′`
    and `∅ ⊢ V ∈ A`, then `Γ′ ⊢ N′ [ x := V ] ∈ B′`.

    The substitution in the conclusion behaves differently
    depending on whether `x` and `x′` are the same variable.

    First, suppose `x ≡ x′`.  Then, by the definition of
    substitution, `N [ x := V] = N`, so we just need to show `Γ ⊢ N ∈ B`.
    But we know `Γ , x ↦ A ⊢ N ∈ B` and, since `x ≡ x′`
    does not appear free in `λᵀ x′ ∈ A′ ⇒ N′`, the context invariance
    lemma yields `Γ ⊢ N ∈ B`.

    Second, suppose `x ≢ x′`.  We know `Γ , x ↦ A , x′ ↦ A′ ⊢ N′ ∈ B′`
    by inversion of the typing relation, from which
    `Γ , x′ ↦ A′ , x ↦ A ⊢ N′ ∈ B′` follows by update permute,
    so the IH applies, giving us `Γ , x′ ↦ A′ ⊢ N′ [ x := V ] ∈ B′`
    By `⇒-I`, we have `Γ ⊢ λᵀ x′ ∈ A′ ⇒ (N′ [ x := V ]) ∈ A′ ⇒ B′`
    and the definition of substitution (noting `x ≢ x′`) gives
    `Γ ⊢ (λᵀ x′ ∈ A′ ⇒ N′) [ x := V ] ∈ A′ ⇒ B′` as required.

  - If `N` is an application `L′ ·ᵀ M′`, the result follows
    straightforwardly from the definition of substitution and the
    induction hypotheses.

  - The remaining cases are similar to the application case.

We need a couple of lemmas. A closed term can be weakened to any context, and just is injective.
<pre class="Agda">

<a name="19227" href="StlcProp.html#19227" class="Function"
      >weaken-closed</a
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
      ><a name="19246" href="StlcProp.html#19246" class="Bound"
      >V</a
      ><a name="19247"
      > </a
      ><a name="19248" href="StlcProp.html#19248" class="Bound"
      >A</a
      ><a name="19249"
      > </a
      ><a name="19250" href="StlcProp.html#19250" class="Bound"
      >&#915;</a
      ><a name="19251" class="Symbol"
      >}</a
      ><a name="19252"
      > </a
      ><a name="19253" class="Symbol"
      >&#8594;</a
      ><a name="19254"
      > </a
      ><a name="19255" href="Maps.html#10360" class="Function"
      >&#8709;</a
      ><a name="19256"
      > </a
      ><a name="19257" href="Stlc.html#4132" class="Datatype Operator"
      >&#8866;</a
      ><a name="19258"
      > </a
      ><a name="19259" href="StlcProp.html#19246" class="Bound"
      >V</a
      ><a name="19260"
      > </a
      ><a name="19261" href="Stlc.html#4132" class="Datatype Operator"
      >&#8712;</a
      ><a name="19262"
      > </a
      ><a name="19263" href="StlcProp.html#19248" class="Bound"
      >A</a
      ><a name="19264"
      > </a
      ><a name="19265" class="Symbol"
      >&#8594;</a
      ><a name="19266"
      > </a
      ><a name="19267" href="StlcProp.html#19250" class="Bound"
      >&#915;</a
      ><a name="19268"
      > </a
      ><a name="19269" href="Stlc.html#4132" class="Datatype Operator"
      >&#8866;</a
      ><a name="19270"
      > </a
      ><a name="19271" href="StlcProp.html#19246" class="Bound"
      >V</a
      ><a name="19272"
      > </a
      ><a name="19273" href="Stlc.html#4132" class="Datatype Operator"
      >&#8712;</a
      ><a name="19274"
      > </a
      ><a name="19275" href="StlcProp.html#19248" class="Bound"
      >A</a
      ><a name="19276"
      >
</a
      ><a name="19277" href="StlcProp.html#19227" class="Function"
      >weaken-closed</a
      ><a name="19290"
      > </a
      ><a name="19291" class="Symbol"
      >{</a
      ><a name="19292" href="StlcProp.html#19292" class="Bound"
      >V</a
      ><a name="19293" class="Symbol"
      >}</a
      ><a name="19294"
      > </a
      ><a name="19295" class="Symbol"
      >{</a
      ><a name="19296" href="StlcProp.html#19296" class="Bound"
      >A</a
      ><a name="19297" class="Symbol"
      >}</a
      ><a name="19298"
      > </a
      ><a name="19299" class="Symbol"
      >{</a
      ><a name="19300" href="StlcProp.html#19300" class="Bound"
      >&#915;</a
      ><a name="19301" class="Symbol"
      >}</a
      ><a name="19302"
      > </a
      ><a name="19303" href="StlcProp.html#19303" class="Bound"
      >&#8866;V</a
      ><a name="19305"
      > </a
      ><a name="19306" class="Symbol"
      >=</a
      ><a name="19307"
      > </a
      ><a name="19308" href="StlcProp.html#11745" class="Function"
      >weaken</a
      ><a name="19314"
      > </a
      ><a name="19315" href="StlcProp.html#19333" class="Function"
      >&#915;~&#915;&#8242;</a
      ><a name="19319"
      > </a
      ><a name="19320" href="StlcProp.html#19303" class="Bound"
      >&#8866;V</a
      ><a name="19322"
      >
  </a
      ><a name="19325" class="Keyword"
      >where</a
      ><a name="19330"
      >
  </a
      ><a name="19333" href="StlcProp.html#19333" class="Function"
      >&#915;~&#915;&#8242;</a
      ><a name="19337"
      > </a
      ><a name="19338" class="Symbol"
      >:</a
      ><a name="19339"
      > </a
      ><a name="19340" class="Symbol"
      >&#8704;</a
      ><a name="19341"
      > </a
      ><a name="19342" class="Symbol"
      >{</a
      ><a name="19343" href="StlcProp.html#19343" class="Bound"
      >x</a
      ><a name="19344" class="Symbol"
      >}</a
      ><a name="19345"
      > </a
      ><a name="19346" class="Symbol"
      >&#8594;</a
      ><a name="19347"
      > </a
      ><a name="19348" href="StlcProp.html#19343" class="Bound"
      >x</a
      ><a name="19349"
      > </a
      ><a name="19350" href="StlcProp.html#7314" class="Datatype Operator"
      >FreeIn</a
      ><a name="19356"
      > </a
      ><a name="19357" href="StlcProp.html#19292" class="Bound"
      >V</a
      ><a name="19358"
      > </a
      ><a name="19359" class="Symbol"
      >&#8594;</a
      ><a name="19360"
      > </a
      ><a name="19361" href="Maps.html#10360" class="Function"
      >&#8709;</a
      ><a name="19362"
      > </a
      ><a name="19363" href="StlcProp.html#19343" class="Bound"
      >x</a
      ><a name="19364"
      > </a
      ><a name="19365" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="19366"
      > </a
      ><a name="19367" href="StlcProp.html#19300" class="Bound"
      >&#915;</a
      ><a name="19368"
      > </a
      ><a name="19369" href="StlcProp.html#19343" class="Bound"
      >x</a
      ><a name="19370"
      >
  </a
      ><a name="19373" href="StlcProp.html#19333" class="Function"
      >&#915;~&#915;&#8242;</a
      ><a name="19377"
      > </a
      ><a name="19378" class="Symbol"
      >{</a
      ><a name="19379" href="StlcProp.html#19379" class="Bound"
      >x</a
      ><a name="19380" class="Symbol"
      >}</a
      ><a name="19381"
      > </a
      ><a name="19382" href="StlcProp.html#19382" class="Bound"
      >x&#8712;V</a
      ><a name="19385"
      > </a
      ><a name="19386" class="Symbol"
      >=</a
      ><a name="19387"
      > </a
      ><a name="19388" href="https://agda.github.io/agda-stdlib/Data.Empty.html#348" class="Function"
      >&#8869;-elim</a
      ><a name="19394"
      > </a
      ><a name="19395" class="Symbol"
      >(</a
      ><a name="19396" href="StlcProp.html#19419" class="Function"
      >x&#8713;V</a
      ><a name="19399"
      > </a
      ><a name="19400" href="StlcProp.html#19382" class="Bound"
      >x&#8712;V</a
      ><a name="19403" class="Symbol"
      >)</a
      ><a name="19404"
      >
    </a
      ><a name="19409" class="Keyword"
      >where</a
      ><a name="19414"
      >
    </a
      ><a name="19419" href="StlcProp.html#19419" class="Function"
      >x&#8713;V</a
      ><a name="19422"
      > </a
      ><a name="19423" class="Symbol"
      >:</a
      ><a name="19424"
      > </a
      ><a name="19425" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#414" class="Function Operator"
      >&#172;</a
      ><a name="19426"
      > </a
      ><a name="19427" class="Symbol"
      >(</a
      ><a name="19428" href="StlcProp.html#19379" class="Bound"
      >x</a
      ><a name="19429"
      > </a
      ><a name="19430" href="StlcProp.html#7314" class="Datatype Operator"
      >FreeIn</a
      ><a name="19436"
      > </a
      ><a name="19437" href="StlcProp.html#19292" class="Bound"
      >V</a
      ><a name="19438" class="Symbol"
      >)</a
      ><a name="19439"
      >
    </a
      ><a name="19444" href="StlcProp.html#19419" class="Function"
      >x&#8713;V</a
      ><a name="19447"
      > </a
      ><a name="19448" class="Symbol"
      >=</a
      ><a name="19449"
      > </a
      ><a name="19450" href="StlcProp.html#11044" class="Postulate"
      >&#8709;&#8866;-closed</a
      ><a name="19459"
      > </a
      ><a name="19460" href="StlcProp.html#19303" class="Bound"
      >&#8866;V</a
      ><a name="19462"
      > </a
      ><a name="19463" class="Symbol"
      >{</a
      ><a name="19464" href="StlcProp.html#19379" class="Bound"
      >x</a
      ><a name="19465" class="Symbol"
      >}</a
      ><a name="19466"
      >

</a
      ><a name="19468" href="StlcProp.html#19468" class="Function"
      >just-injective</a
      ><a name="19482"
      > </a
      ><a name="19483" class="Symbol"
      >:</a
      ><a name="19484"
      > </a
      ><a name="19485" class="Symbol"
      >&#8704;</a
      ><a name="19486"
      > </a
      ><a name="19487" class="Symbol"
      >{</a
      ><a name="19488" href="StlcProp.html#19488" class="Bound"
      >X</a
      ><a name="19489"
      > </a
      ><a name="19490" class="Symbol"
      >:</a
      ><a name="19491"
      > </a
      ><a name="19492" class="PrimitiveType"
      >Set</a
      ><a name="19495" class="Symbol"
      >}</a
      ><a name="19496"
      > </a
      ><a name="19497" class="Symbol"
      >{</a
      ><a name="19498" href="StlcProp.html#19498" class="Bound"
      >x</a
      ><a name="19499"
      > </a
      ><a name="19500" href="StlcProp.html#19500" class="Bound"
      >y</a
      ><a name="19501"
      > </a
      ><a name="19502" class="Symbol"
      >:</a
      ><a name="19503"
      > </a
      ><a name="19504" href="StlcProp.html#19488" class="Bound"
      >X</a
      ><a name="19505" class="Symbol"
      >}</a
      ><a name="19506"
      > </a
      ><a name="19507" class="Symbol"
      >&#8594;</a
      ><a name="19508"
      > </a
      ><a name="19509" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >_&#8801;_</a
      ><a name="19512"
      > </a
      ><a name="19513" class="Symbol"
      >{</a
      ><a name="19514" class="Argument"
      >A</a
      ><a name="19515"
      > </a
      ><a name="19516" class="Symbol"
      >=</a
      ><a name="19517"
      > </a
      ><a name="19518" href="https://agda.github.io/agda-stdlib/Data.Maybe.Base.html#335" class="Datatype"
      >Maybe</a
      ><a name="19523"
      > </a
      ><a name="19524" href="StlcProp.html#19488" class="Bound"
      >X</a
      ><a name="19525" class="Symbol"
      >}</a
      ><a name="19526"
      > </a
      ><a name="19527" class="Symbol"
      >(</a
      ><a name="19528" href="https://agda.github.io/agda-stdlib/Data.Maybe.Base.html#373" class="InductiveConstructor"
      >just</a
      ><a name="19532"
      > </a
      ><a name="19533" href="StlcProp.html#19498" class="Bound"
      >x</a
      ><a name="19534" class="Symbol"
      >)</a
      ><a name="19535"
      > </a
      ><a name="19536" class="Symbol"
      >(</a
      ><a name="19537" href="https://agda.github.io/agda-stdlib/Data.Maybe.Base.html#373" class="InductiveConstructor"
      >just</a
      ><a name="19541"
      > </a
      ><a name="19542" href="StlcProp.html#19500" class="Bound"
      >y</a
      ><a name="19543" class="Symbol"
      >)</a
      ><a name="19544"
      > </a
      ><a name="19545" class="Symbol"
      >&#8594;</a
      ><a name="19546"
      > </a
      ><a name="19547" href="StlcProp.html#19498" class="Bound"
      >x</a
      ><a name="19548"
      > </a
      ><a name="19549" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="19550"
      > </a
      ><a name="19551" href="StlcProp.html#19500" class="Bound"
      >y</a
      ><a name="19552"
      >
</a
      ><a name="19553" href="StlcProp.html#19468" class="Function"
      >just-injective</a
      ><a name="19567"
      > </a
      ><a name="19568" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="19572"
      > </a
      ><a name="19573" class="Symbol"
      >=</a
      ><a name="19574"
      > </a
      ><a name="19575" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      >

</pre>

<pre class="Agda">

<a name="19605" href="StlcProp.html#15966" class="Function"
      >preservation-[:=]</a
      ><a name="19622"
      > </a
      ><a name="19623" class="Symbol"
      >{_}</a
      ><a name="19626"
      > </a
      ><a name="19627" class="Symbol"
      >{</a
      ><a name="19628" href="StlcProp.html#19628" class="Bound"
      >x</a
      ><a name="19629" class="Symbol"
      >}</a
      ><a name="19630"
      > </a
      ><a name="19631" class="Symbol"
      >(</a
      ><a name="19632" href="Stlc.html#4176" class="InductiveConstructor"
      >Ax</a
      ><a name="19634"
      > </a
      ><a name="19635" class="Symbol"
      >{_}</a
      ><a name="19638"
      > </a
      ><a name="19639" class="Symbol"
      >{</a
      ><a name="19640" href="StlcProp.html#19640" class="Bound"
      >x&#8242;</a
      ><a name="19642" class="Symbol"
      >}</a
      ><a name="19643"
      > </a
      ><a name="19644" href="StlcProp.html#19644" class="Bound"
      >[&#915;,x&#8614;A]x&#8242;&#8801;B</a
      ><a name="19655" class="Symbol"
      >)</a
      ><a name="19656"
      > </a
      ><a name="19657" href="StlcProp.html#19657" class="Bound"
      >&#8866;V</a
      ><a name="19659"
      > </a
      ><a name="19660" class="Keyword"
      >with</a
      ><a name="19664"
      > </a
      ><a name="19665" href="StlcProp.html#19628" class="Bound"
      >x</a
      ><a name="19666"
      > </a
      ><a name="19667" href="Maps.html#2558" class="Function Operator"
      >&#8799;</a
      ><a name="19668"
      > </a
      ><a name="19669" href="StlcProp.html#19640" class="Bound"
      >x&#8242;</a
      ><a name="19671"
      >
</a
      ><a name="19672" class="Symbol"
      >...|</a
      ><a name="19676"
      > </a
      ><a name="19677" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#520" class="InductiveConstructor"
      >yes</a
      ><a name="19680"
      > </a
      ><a name="19681" href="StlcProp.html#19681" class="Bound"
      >x&#8801;x&#8242;</a
      ><a name="19685"
      > </a
      ><a name="19686" class="Keyword"
      >rewrite</a
      ><a name="19693"
      > </a
      ><a name="19694" href="StlcProp.html#19468" class="Function"
      >just-injective</a
      ><a name="19708"
      > </a
      ><a name="19709" href="StlcProp.html#19644" class="Bound"
      >[&#915;,x&#8614;A]x&#8242;&#8801;B</a
      ><a name="19720"
      >  </a
      ><a name="19722" class="Symbol"
      >=</a
      ><a name="19723"
      >  </a
      ><a name="19725" href="StlcProp.html#19227" class="Function"
      >weaken-closed</a
      ><a name="19738"
      > </a
      ><a name="19739" href="StlcProp.html#19657" class="Bound"
      >&#8866;V</a
      ><a name="19741"
      >
</a
      ><a name="19742" class="Symbol"
      >...|</a
      ><a name="19746"
      > </a
      ><a name="19747" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#547" class="InductiveConstructor"
      >no</a
      ><a name="19749"
      >  </a
      ><a name="19751" href="StlcProp.html#19751" class="Bound"
      >x&#8802;x&#8242;</a
      ><a name="19755"
      >  </a
      ><a name="19757" class="Symbol"
      >=</a
      ><a name="19758"
      >  </a
      ><a name="19760" href="Stlc.html#4176" class="InductiveConstructor"
      >Ax</a
      ><a name="19762"
      > </a
      ><a name="19763" href="StlcProp.html#19644" class="Bound"
      >[&#915;,x&#8614;A]x&#8242;&#8801;B</a
      ><a name="19774"
      >
</a
      ><a name="19775" href="StlcProp.html#15966" class="Function"
      >preservation-[:=]</a
      ><a name="19792"
      > </a
      ><a name="19793" class="Symbol"
      >{</a
      ><a name="19794" href="StlcProp.html#19794" class="Bound"
      >&#915;</a
      ><a name="19795" class="Symbol"
      >}</a
      ><a name="19796"
      > </a
      ><a name="19797" class="Symbol"
      >{</a
      ><a name="19798" href="StlcProp.html#19798" class="Bound"
      >x</a
      ><a name="19799" class="Symbol"
      >}</a
      ><a name="19800"
      > </a
      ><a name="19801" class="Symbol"
      >{</a
      ><a name="19802" href="StlcProp.html#19802" class="Bound"
      >A</a
      ><a name="19803" class="Symbol"
      >}</a
      ><a name="19804"
      > </a
      ><a name="19805" class="Symbol"
      >{</a
      ><a name="19806" href="Stlc.html#1070" class="InductiveConstructor Operator"
      >&#955;&#7488;</a
      ><a name="19808"
      > </a
      ><a name="19809" href="StlcProp.html#19809" class="Bound"
      >x&#8242;</a
      ><a name="19811"
      > </a
      ><a name="19812" href="Stlc.html#1070" class="InductiveConstructor Operator"
      >&#8712;</a
      ><a name="19813"
      > </a
      ><a name="19814" href="StlcProp.html#19814" class="Bound"
      >A&#8242;</a
      ><a name="19816"
      > </a
      ><a name="19817" href="Stlc.html#1070" class="InductiveConstructor Operator"
      >&#8658;</a
      ><a name="19818"
      > </a
      ><a name="19819" href="StlcProp.html#19819" class="Bound"
      >N&#8242;</a
      ><a name="19821" class="Symbol"
      >}</a
      ><a name="19822"
      > </a
      ><a name="19823" class="Symbol"
      >{</a
      ><a name="19824" class="DottedPattern Symbol"
      >.</a
      ><a name="19825" href="StlcProp.html#19814" class="DottedPattern Bound"
      >A&#8242;</a
      ><a name="19827"
      > </a
      ><a name="19828" href="Stlc.html#1001" class="InductiveConstructor Operator"
      >&#8658;</a
      ><a name="19829"
      > </a
      ><a name="19830" href="StlcProp.html#19830" class="Bound"
      >B&#8242;</a
      ><a name="19832" class="Symbol"
      >}</a
      ><a name="19833"
      > </a
      ><a name="19834" class="Symbol"
      >{</a
      ><a name="19835" href="StlcProp.html#19835" class="Bound"
      >V</a
      ><a name="19836" class="Symbol"
      >}</a
      ><a name="19837"
      > </a
      ><a name="19838" class="Symbol"
      >(</a
      ><a name="19839" href="Stlc.html#4233" class="InductiveConstructor"
      >&#8658;-I</a
      ><a name="19842"
      > </a
      ><a name="19843" href="StlcProp.html#19843" class="Bound"
      >&#8866;N&#8242;</a
      ><a name="19846" class="Symbol"
      >)</a
      ><a name="19847"
      > </a
      ><a name="19848" href="StlcProp.html#19848" class="Bound"
      >&#8866;V</a
      ><a name="19850"
      > </a
      ><a name="19851" class="Keyword"
      >with</a
      ><a name="19855"
      > </a
      ><a name="19856" href="StlcProp.html#19798" class="Bound"
      >x</a
      ><a name="19857"
      > </a
      ><a name="19858" href="Maps.html#2558" class="Function Operator"
      >&#8799;</a
      ><a name="19859"
      > </a
      ><a name="19860" href="StlcProp.html#19809" class="Bound"
      >x&#8242;</a
      ><a name="19862"
      >
</a
      ><a name="19863" class="Symbol"
      >...|</a
      ><a name="19867"
      > </a
      ><a name="19868" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#520" class="InductiveConstructor"
      >yes</a
      ><a name="19871"
      > </a
      ><a name="19872" href="StlcProp.html#19872" class="Bound"
      >x&#8801;x&#8242;</a
      ><a name="19876"
      > </a
      ><a name="19877" class="Keyword"
      >rewrite</a
      ><a name="19884"
      > </a
      ><a name="19885" href="StlcProp.html#19872" class="Bound"
      >x&#8801;x&#8242;</a
      ><a name="19889"
      > </a
      ><a name="19890" class="Symbol"
      >=</a
      ><a name="19891"
      > </a
      ><a name="19892" href="StlcProp.html#11745" class="Function"
      >weaken</a
      ><a name="19898"
      > </a
      ><a name="19899" href="StlcProp.html#19924" class="Function"
      >&#915;&#8242;~&#915;</a
      ><a name="19903"
      > </a
      ><a name="19904" class="Symbol"
      >(</a
      ><a name="19905" href="Stlc.html#4233" class="InductiveConstructor"
      >&#8658;-I</a
      ><a name="19908"
      > </a
      ><a name="19909" href="StlcProp.html#19843" class="Bound"
      >&#8866;N&#8242;</a
      ><a name="19912" class="Symbol"
      >)</a
      ><a name="19913"
      >
  </a
      ><a name="19916" class="Keyword"
      >where</a
      ><a name="19921"
      >
  </a
      ><a name="19924" href="StlcProp.html#19924" class="Function"
      >&#915;&#8242;~&#915;</a
      ><a name="19928"
      > </a
      ><a name="19929" class="Symbol"
      >:</a
      ><a name="19930"
      > </a
      ><a name="19931" class="Symbol"
      >&#8704;</a
      ><a name="19932"
      > </a
      ><a name="19933" class="Symbol"
      >{</a
      ><a name="19934" href="StlcProp.html#19934" class="Bound"
      >y</a
      ><a name="19935" class="Symbol"
      >}</a
      ><a name="19936"
      > </a
      ><a name="19937" class="Symbol"
      >&#8594;</a
      ><a name="19938"
      > </a
      ><a name="19939" href="StlcProp.html#19934" class="Bound"
      >y</a
      ><a name="19940"
      > </a
      ><a name="19941" href="StlcProp.html#7314" class="Datatype Operator"
      >FreeIn</a
      ><a name="19947"
      > </a
      ><a name="19948" class="Symbol"
      >(</a
      ><a name="19949" href="Stlc.html#1070" class="InductiveConstructor Operator"
      >&#955;&#7488;</a
      ><a name="19951"
      > </a
      ><a name="19952" href="StlcProp.html#19809" class="Bound"
      >x&#8242;</a
      ><a name="19954"
      > </a
      ><a name="19955" href="Stlc.html#1070" class="InductiveConstructor Operator"
      >&#8712;</a
      ><a name="19956"
      > </a
      ><a name="19957" href="StlcProp.html#19814" class="Bound"
      >A&#8242;</a
      ><a name="19959"
      > </a
      ><a name="19960" href="Stlc.html#1070" class="InductiveConstructor Operator"
      >&#8658;</a
      ><a name="19961"
      > </a
      ><a name="19962" href="StlcProp.html#19819" class="Bound"
      >N&#8242;</a
      ><a name="19964" class="Symbol"
      >)</a
      ><a name="19965"
      > </a
      ><a name="19966" class="Symbol"
      >&#8594;</a
      ><a name="19967"
      > </a
      ><a name="19968" class="Symbol"
      >(</a
      ><a name="19969" href="StlcProp.html#19794" class="Bound"
      >&#915;</a
      ><a name="19970"
      > </a
      ><a name="19971" href="Maps.html#10464" class="Function Operator"
      >,</a
      ><a name="19972"
      > </a
      ><a name="19973" href="StlcProp.html#19809" class="Bound"
      >x&#8242;</a
      ><a name="19975"
      > </a
      ><a name="19976" href="Maps.html#10464" class="Function Operator"
      >&#8614;</a
      ><a name="19977"
      > </a
      ><a name="19978" href="StlcProp.html#19802" class="Bound"
      >A</a
      ><a name="19979" class="Symbol"
      >)</a
      ><a name="19980"
      > </a
      ><a name="19981" href="StlcProp.html#19934" class="Bound"
      >y</a
      ><a name="19982"
      > </a
      ><a name="19983" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="19984"
      > </a
      ><a name="19985" href="StlcProp.html#19794" class="Bound"
      >&#915;</a
      ><a name="19986"
      > </a
      ><a name="19987" href="StlcProp.html#19934" class="Bound"
      >y</a
      ><a name="19988"
      >
  </a
      ><a name="19991" href="StlcProp.html#19924" class="Function"
      >&#915;&#8242;~&#915;</a
      ><a name="19995"
      > </a
      ><a name="19996" class="Symbol"
      >{</a
      ><a name="19997" href="StlcProp.html#19997" class="Bound"
      >y</a
      ><a name="19998" class="Symbol"
      >}</a
      ><a name="19999"
      > </a
      ><a name="20000" class="Symbol"
      >(</a
      ><a name="20001" href="StlcProp.html#7390" class="InductiveConstructor"
      >free-&#955;&#7488;</a
      ><a name="20008"
      > </a
      ><a name="20009" href="StlcProp.html#20009" class="Bound"
      >x&#8242;&#8802;y</a
      ><a name="20013"
      > </a
      ><a name="20014" href="StlcProp.html#20014" class="Bound"
      >y&#8712;N&#8242;</a
      ><a name="20018" class="Symbol"
      >)</a
      ><a name="20019"
      > </a
      ><a name="20020" class="Keyword"
      >with</a
      ><a name="20024"
      > </a
      ><a name="20025" href="StlcProp.html#19809" class="Bound"
      >x&#8242;</a
      ><a name="20027"
      > </a
      ><a name="20028" href="Maps.html#2558" class="Function Operator"
      >&#8799;</a
      ><a name="20029"
      > </a
      ><a name="20030" href="StlcProp.html#19997" class="Bound"
      >y</a
      ><a name="20031"
      >
  </a
      ><a name="20034" class="Symbol"
      >...|</a
      ><a name="20038"
      > </a
      ><a name="20039" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#520" class="InductiveConstructor"
      >yes</a
      ><a name="20042"
      > </a
      ><a name="20043" href="StlcProp.html#20043" class="Bound"
      >x&#8242;&#8801;y</a
      ><a name="20047"
      >  </a
      ><a name="20049" class="Symbol"
      >=</a
      ><a name="20050"
      > </a
      ><a name="20051" href="https://agda.github.io/agda-stdlib/Data.Empty.html#348" class="Function"
      >&#8869;-elim</a
      ><a name="20057"
      > </a
      ><a name="20058" class="Symbol"
      >(</a
      ><a name="20059" href="StlcProp.html#20009" class="Bound"
      >x&#8242;&#8802;y</a
      ><a name="20063"
      > </a
      ><a name="20064" href="StlcProp.html#20043" class="Bound"
      >x&#8242;&#8801;y</a
      ><a name="20068" class="Symbol"
      >)</a
      ><a name="20069"
      >
  </a
      ><a name="20072" class="Symbol"
      >...|</a
      ><a name="20076"
      > </a
      ><a name="20077" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#547" class="InductiveConstructor"
      >no</a
      ><a name="20079"
      >  </a
      ><a name="20081" class="Symbol"
      >_</a
      ><a name="20082"
      >     </a
      ><a name="20087" class="Symbol"
      >=</a
      ><a name="20088"
      > </a
      ><a name="20089" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="20093"
      >
</a
      ><a name="20094" class="Symbol"
      >...|</a
      ><a name="20098"
      > </a
      ><a name="20099" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#547" class="InductiveConstructor"
      >no</a
      ><a name="20101"
      >  </a
      ><a name="20103" href="StlcProp.html#20103" class="Bound"
      >x&#8802;x&#8242;</a
      ><a name="20107"
      > </a
      ><a name="20108" class="Symbol"
      >=</a
      ><a name="20109"
      > </a
      ><a name="20110" href="Stlc.html#4233" class="InductiveConstructor"
      >&#8658;-I</a
      ><a name="20113"
      > </a
      ><a name="20114" href="StlcProp.html#20225" class="Function"
      >&#8866;N&#8242;V</a
      ><a name="20118"
      >
  </a
      ><a name="20121" class="Keyword"
      >where</a
      ><a name="20126"
      >
  </a
      ><a name="20129" href="StlcProp.html#20129" class="Function"
      >x&#8242;x&#8866;N&#8242;</a
      ><a name="20135"
      > </a
      ><a name="20136" class="Symbol"
      >:</a
      ><a name="20137"
      > </a
      ><a name="20138" href="StlcProp.html#19794" class="Bound"
      >&#915;</a
      ><a name="20139"
      > </a
      ><a name="20140" href="Maps.html#10464" class="Function Operator"
      >,</a
      ><a name="20141"
      > </a
      ><a name="20142" href="StlcProp.html#19809" class="Bound"
      >x&#8242;</a
      ><a name="20144"
      > </a
      ><a name="20145" href="Maps.html#10464" class="Function Operator"
      >&#8614;</a
      ><a name="20146"
      > </a
      ><a name="20147" href="StlcProp.html#19814" class="Bound"
      >A&#8242;</a
      ><a name="20149"
      > </a
      ><a name="20150" href="Maps.html#10464" class="Function Operator"
      >,</a
      ><a name="20151"
      > </a
      ><a name="20152" href="StlcProp.html#19798" class="Bound"
      >x</a
      ><a name="20153"
      > </a
      ><a name="20154" href="Maps.html#10464" class="Function Operator"
      >&#8614;</a
      ><a name="20155"
      > </a
      ><a name="20156" href="StlcProp.html#19802" class="Bound"
      >A</a
      ><a name="20157"
      > </a
      ><a name="20158" href="Stlc.html#4132" class="Datatype Operator"
      >&#8866;</a
      ><a name="20159"
      > </a
      ><a name="20160" href="StlcProp.html#19819" class="Bound"
      >N&#8242;</a
      ><a name="20162"
      > </a
      ><a name="20163" href="Stlc.html#4132" class="Datatype Operator"
      >&#8712;</a
      ><a name="20164"
      > </a
      ><a name="20165" href="StlcProp.html#19830" class="Bound"
      >B&#8242;</a
      ><a name="20167"
      >
  </a
      ><a name="20170" href="StlcProp.html#20129" class="Function"
      >x&#8242;x&#8866;N&#8242;</a
      ><a name="20176"
      > </a
      ><a name="20177" class="Keyword"
      >rewrite</a
      ><a name="20184"
      > </a
      ><a name="20185" href="Maps.html#11587" class="Function"
      >update-permute</a
      ><a name="20199"
      > </a
      ><a name="20200" href="StlcProp.html#19794" class="Bound"
      >&#915;</a
      ><a name="20201"
      > </a
      ><a name="20202" href="StlcProp.html#19798" class="Bound"
      >x</a
      ><a name="20203"
      > </a
      ><a name="20204" href="StlcProp.html#19802" class="Bound"
      >A</a
      ><a name="20205"
      > </a
      ><a name="20206" href="StlcProp.html#19809" class="Bound"
      >x&#8242;</a
      ><a name="20208"
      > </a
      ><a name="20209" href="StlcProp.html#19814" class="Bound"
      >A&#8242;</a
      ><a name="20211"
      > </a
      ><a name="20212" href="StlcProp.html#20103" class="Bound"
      >x&#8802;x&#8242;</a
      ><a name="20216"
      > </a
      ><a name="20217" class="Symbol"
      >=</a
      ><a name="20218"
      > </a
      ><a name="20219" href="StlcProp.html#19843" class="Bound"
      >&#8866;N&#8242;</a
      ><a name="20222"
      >
  </a
      ><a name="20225" href="StlcProp.html#20225" class="Function"
      >&#8866;N&#8242;V</a
      ><a name="20229"
      > </a
      ><a name="20230" class="Symbol"
      >:</a
      ><a name="20231"
      > </a
      ><a name="20232" class="Symbol"
      >(</a
      ><a name="20233" href="StlcProp.html#19794" class="Bound"
      >&#915;</a
      ><a name="20234"
      > </a
      ><a name="20235" href="Maps.html#10464" class="Function Operator"
      >,</a
      ><a name="20236"
      > </a
      ><a name="20237" href="StlcProp.html#19809" class="Bound"
      >x&#8242;</a
      ><a name="20239"
      > </a
      ><a name="20240" href="Maps.html#10464" class="Function Operator"
      >&#8614;</a
      ><a name="20241"
      > </a
      ><a name="20242" href="StlcProp.html#19814" class="Bound"
      >A&#8242;</a
      ><a name="20244" class="Symbol"
      >)</a
      ><a name="20245"
      > </a
      ><a name="20246" href="Stlc.html#4132" class="Datatype Operator"
      >&#8866;</a
      ><a name="20247"
      > </a
      ><a name="20248" href="StlcProp.html#19819" class="Bound"
      >N&#8242;</a
      ><a name="20250"
      > </a
      ><a name="20251" href="Stlc.html#1756" class="Function Operator"
      >[</a
      ><a name="20252"
      > </a
      ><a name="20253" href="StlcProp.html#19798" class="Bound"
      >x</a
      ><a name="20254"
      > </a
      ><a name="20255" href="Stlc.html#1756" class="Function Operator"
      >:=</a
      ><a name="20257"
      > </a
      ><a name="20258" href="StlcProp.html#19835" class="Bound"
      >V</a
      ><a name="20259"
      > </a
      ><a name="20260" href="Stlc.html#1756" class="Function Operator"
      >]</a
      ><a name="20261"
      > </a
      ><a name="20262" href="Stlc.html#4132" class="Datatype Operator"
      >&#8712;</a
      ><a name="20263"
      > </a
      ><a name="20264" href="StlcProp.html#19830" class="Bound"
      >B&#8242;</a
      ><a name="20266"
      >
  </a
      ><a name="20269" href="StlcProp.html#20225" class="Function"
      >&#8866;N&#8242;V</a
      ><a name="20273"
      > </a
      ><a name="20274" class="Symbol"
      >=</a
      ><a name="20275"
      > </a
      ><a name="20276" href="StlcProp.html#15966" class="Function"
      >preservation-[:=]</a
      ><a name="20293"
      > </a
      ><a name="20294" href="StlcProp.html#20129" class="Function"
      >x&#8242;x&#8866;N&#8242;</a
      ><a name="20300"
      > </a
      ><a name="20301" href="StlcProp.html#19848" class="Bound"
      >&#8866;V</a
      ><a name="20303"
      >
</a
      ><a name="20304" href="StlcProp.html#15966" class="Function"
      >preservation-[:=]</a
      ><a name="20321"
      > </a
      ><a name="20322" class="Symbol"
      >(</a
      ><a name="20323" href="Stlc.html#4316" class="InductiveConstructor"
      >&#8658;-E</a
      ><a name="20326"
      > </a
      ><a name="20327" href="StlcProp.html#20327" class="Bound"
      >&#8866;L</a
      ><a name="20329"
      > </a
      ><a name="20330" href="StlcProp.html#20330" class="Bound"
      >&#8866;M</a
      ><a name="20332" class="Symbol"
      >)</a
      ><a name="20333"
      > </a
      ><a name="20334" href="StlcProp.html#20334" class="Bound"
      >&#8866;V</a
      ><a name="20336"
      > </a
      ><a name="20337" class="Symbol"
      >=</a
      ><a name="20338"
      > </a
      ><a name="20339" href="Stlc.html#4316" class="InductiveConstructor"
      >&#8658;-E</a
      ><a name="20342"
      > </a
      ><a name="20343" class="Symbol"
      >(</a
      ><a name="20344" href="StlcProp.html#15966" class="Function"
      >preservation-[:=]</a
      ><a name="20361"
      > </a
      ><a name="20362" href="StlcProp.html#20327" class="Bound"
      >&#8866;L</a
      ><a name="20364"
      > </a
      ><a name="20365" href="StlcProp.html#20334" class="Bound"
      >&#8866;V</a
      ><a name="20367" class="Symbol"
      >)</a
      ><a name="20368"
      > </a
      ><a name="20369" class="Symbol"
      >(</a
      ><a name="20370" href="StlcProp.html#15966" class="Function"
      >preservation-[:=]</a
      ><a name="20387"
      > </a
      ><a name="20388" href="StlcProp.html#20330" class="Bound"
      >&#8866;M</a
      ><a name="20390"
      > </a
      ><a name="20391" href="StlcProp.html#20334" class="Bound"
      >&#8866;V</a
      ><a name="20393" class="Symbol"
      >)</a
      ><a name="20394"
      >
</a
      ><a name="20395" href="StlcProp.html#15966" class="Function"
      >preservation-[:=]</a
      ><a name="20412"
      > </a
      ><a name="20413" href="Stlc.html#4397" class="InductiveConstructor"
      >&#120121;-I&#8321;</a
      ><a name="20417"
      > </a
      ><a name="20418" href="StlcProp.html#20418" class="Bound"
      >&#8866;V</a
      ><a name="20420"
      > </a
      ><a name="20421" class="Symbol"
      >=</a
      ><a name="20422"
      > </a
      ><a name="20423" href="Stlc.html#4397" class="InductiveConstructor"
      >&#120121;-I&#8321;</a
      ><a name="20427"
      >
</a
      ><a name="20428" href="StlcProp.html#15966" class="Function"
      >preservation-[:=]</a
      ><a name="20445"
      > </a
      ><a name="20446" href="Stlc.html#4432" class="InductiveConstructor"
      >&#120121;-I&#8322;</a
      ><a name="20450"
      > </a
      ><a name="20451" href="StlcProp.html#20451" class="Bound"
      >&#8866;V</a
      ><a name="20453"
      > </a
      ><a name="20454" class="Symbol"
      >=</a
      ><a name="20455"
      > </a
      ><a name="20456" href="Stlc.html#4432" class="InductiveConstructor"
      >&#120121;-I&#8322;</a
      ><a name="20460"
      >
</a
      ><a name="20461" href="StlcProp.html#15966" class="Function"
      >preservation-[:=]</a
      ><a name="20478"
      > </a
      ><a name="20479" class="Symbol"
      >(</a
      ><a name="20480" href="Stlc.html#4468" class="InductiveConstructor"
      >&#120121;-E</a
      ><a name="20483"
      > </a
      ><a name="20484" href="StlcProp.html#20484" class="Bound"
      >&#8866;L</a
      ><a name="20486"
      > </a
      ><a name="20487" href="StlcProp.html#20487" class="Bound"
      >&#8866;M</a
      ><a name="20489"
      > </a
      ><a name="20490" href="StlcProp.html#20490" class="Bound"
      >&#8866;N</a
      ><a name="20492" class="Symbol"
      >)</a
      ><a name="20493"
      > </a
      ><a name="20494" href="StlcProp.html#20494" class="Bound"
      >&#8866;V</a
      ><a name="20496"
      > </a
      ><a name="20497" class="Symbol"
      >=</a
      ><a name="20498"
      >
  </a
      ><a name="20501" href="Stlc.html#4468" class="InductiveConstructor"
      >&#120121;-E</a
      ><a name="20504"
      > </a
      ><a name="20505" class="Symbol"
      >(</a
      ><a name="20506" href="StlcProp.html#15966" class="Function"
      >preservation-[:=]</a
      ><a name="20523"
      > </a
      ><a name="20524" href="StlcProp.html#20484" class="Bound"
      >&#8866;L</a
      ><a name="20526"
      > </a
      ><a name="20527" href="StlcProp.html#20494" class="Bound"
      >&#8866;V</a
      ><a name="20529" class="Symbol"
      >)</a
      ><a name="20530"
      > </a
      ><a name="20531" class="Symbol"
      >(</a
      ><a name="20532" href="StlcProp.html#15966" class="Function"
      >preservation-[:=]</a
      ><a name="20549"
      > </a
      ><a name="20550" href="StlcProp.html#20487" class="Bound"
      >&#8866;M</a
      ><a name="20552"
      > </a
      ><a name="20553" href="StlcProp.html#20494" class="Bound"
      >&#8866;V</a
      ><a name="20555" class="Symbol"
      >)</a
      ><a name="20556"
      > </a
      ><a name="20557" class="Symbol"
      >(</a
      ><a name="20558" href="StlcProp.html#15966" class="Function"
      >preservation-[:=]</a
      ><a name="20575"
      > </a
      ><a name="20576" href="StlcProp.html#20490" class="Bound"
      >&#8866;N</a
      ><a name="20578"
      > </a
      ><a name="20579" href="StlcProp.html#20494" class="Bound"
      >&#8866;V</a
      ><a name="20581" class="Symbol"
      >)</a
      >

</pre>


### Main Theorem

We now have the tools we need to prove preservation: if a closed
term `M` has type `A` and takes a step to `N`, then `N`
is also a closed term with type `A`.  In other words, small-step
reduction preserves types.

<pre class="Agda">

<a name="20841" href="StlcProp.html#20841" class="Function"
      >preservation</a
      ><a name="20853"
      > </a
      ><a name="20854" class="Symbol"
      >:</a
      ><a name="20855"
      > </a
      ><a name="20856" class="Symbol"
      >&#8704;</a
      ><a name="20857"
      > </a
      ><a name="20858" class="Symbol"
      >{</a
      ><a name="20859" href="StlcProp.html#20859" class="Bound"
      >M</a
      ><a name="20860"
      > </a
      ><a name="20861" href="StlcProp.html#20861" class="Bound"
      >N</a
      ><a name="20862"
      > </a
      ><a name="20863" href="StlcProp.html#20863" class="Bound"
      >A</a
      ><a name="20864" class="Symbol"
      >}</a
      ><a name="20865"
      > </a
      ><a name="20866" class="Symbol"
      >&#8594;</a
      ><a name="20867"
      > </a
      ><a name="20868" href="Maps.html#10360" class="Function"
      >&#8709;</a
      ><a name="20869"
      > </a
      ><a name="20870" href="Stlc.html#4132" class="Datatype Operator"
      >&#8866;</a
      ><a name="20871"
      > </a
      ><a name="20872" href="StlcProp.html#20859" class="Bound"
      >M</a
      ><a name="20873"
      > </a
      ><a name="20874" href="Stlc.html#4132" class="Datatype Operator"
      >&#8712;</a
      ><a name="20875"
      > </a
      ><a name="20876" href="StlcProp.html#20863" class="Bound"
      >A</a
      ><a name="20877"
      > </a
      ><a name="20878" class="Symbol"
      >&#8594;</a
      ><a name="20879"
      > </a
      ><a name="20880" href="StlcProp.html#20859" class="Bound"
      >M</a
      ><a name="20881"
      > </a
      ><a name="20882" href="Stlc.html#2241" class="Datatype Operator"
      >&#10233;</a
      ><a name="20883"
      > </a
      ><a name="20884" href="StlcProp.html#20861" class="Bound"
      >N</a
      ><a name="20885"
      > </a
      ><a name="20886" class="Symbol"
      >&#8594;</a
      ><a name="20887"
      > </a
      ><a name="20888" href="Maps.html#10360" class="Function"
      >&#8709;</a
      ><a name="20889"
      > </a
      ><a name="20890" href="Stlc.html#4132" class="Datatype Operator"
      >&#8866;</a
      ><a name="20891"
      > </a
      ><a name="20892" href="StlcProp.html#20861" class="Bound"
      >N</a
      ><a name="20893"
      > </a
      ><a name="20894" href="Stlc.html#4132" class="Datatype Operator"
      >&#8712;</a
      ><a name="20895"
      > </a
      ><a name="20896" href="StlcProp.html#20863" class="Bound"
      >A</a
      >

</pre>

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
      \lambda x:t_{11}.t_{12}` and `t_1 t_2` steps to ``x:=t_2`t_{12}`; the
      desired result now follows from the fact that substitution
      preserves types.

    - If the last rule in the derivation was `if`, then `t = if t_1
      then t_2 else t_3`, and there are again three cases depending on
      how `t` steps.

    - If `t` steps to `t_2` or `t_3`, the result is immediate, since
      `t_2` and `t_3` have the same type as `t`.

    - Otherwise, `t` steps by `Sif`, and the desired conclusion
      follows directly from the induction hypothesis.

<pre class="Agda">

<a name="22191" href="StlcProp.html#20841" class="Function"
      >preservation</a
      ><a name="22203"
      > </a
      ><a name="22204" class="Symbol"
      >(</a
      ><a name="22205" href="Stlc.html#4176" class="InductiveConstructor"
      >Ax</a
      ><a name="22207"
      > </a
      ><a name="22208" href="StlcProp.html#22208" class="Bound"
      >x&#8321;</a
      ><a name="22210" class="Symbol"
      >)</a
      ><a name="22211"
      > </a
      ><a name="22212" class="Symbol"
      >()</a
      ><a name="22214"
      >
</a
      ><a name="22215" href="StlcProp.html#20841" class="Function"
      >preservation</a
      ><a name="22227"
      > </a
      ><a name="22228" class="Symbol"
      >(</a
      ><a name="22229" href="Stlc.html#4233" class="InductiveConstructor"
      >&#8658;-I</a
      ><a name="22232"
      > </a
      ><a name="22233" href="StlcProp.html#22233" class="Bound"
      >&#8866;N</a
      ><a name="22235" class="Symbol"
      >)</a
      ><a name="22236"
      > </a
      ><a name="22237" class="Symbol"
      >()</a
      ><a name="22239"
      >
</a
      ><a name="22240" href="StlcProp.html#20841" class="Function"
      >preservation</a
      ><a name="22252"
      > </a
      ><a name="22253" class="Symbol"
      >(</a
      ><a name="22254" href="Stlc.html#4316" class="InductiveConstructor"
      >&#8658;-E</a
      ><a name="22257"
      > </a
      ><a name="22258" class="Symbol"
      >(</a
      ><a name="22259" href="Stlc.html#4233" class="InductiveConstructor"
      >&#8658;-I</a
      ><a name="22262"
      > </a
      ><a name="22263" href="StlcProp.html#22263" class="Bound"
      >&#8866;N</a
      ><a name="22265" class="Symbol"
      >)</a
      ><a name="22266"
      > </a
      ><a name="22267" href="StlcProp.html#22267" class="Bound"
      >&#8866;V</a
      ><a name="22269" class="Symbol"
      >)</a
      ><a name="22270"
      > </a
      ><a name="22271" class="Symbol"
      >(</a
      ><a name="22272" href="Stlc.html#2273" class="InductiveConstructor"
      >&#946;&#8658;</a
      ><a name="22274"
      > </a
      ><a name="22275" href="StlcProp.html#22275" class="Bound"
      >valueV</a
      ><a name="22281" class="Symbol"
      >)</a
      ><a name="22282"
      > </a
      ><a name="22283" class="Symbol"
      >=</a
      ><a name="22284"
      > </a
      ><a name="22285" href="StlcProp.html#15966" class="Function"
      >preservation-[:=]</a
      ><a name="22302"
      > </a
      ><a name="22303" href="StlcProp.html#22263" class="Bound"
      >&#8866;N</a
      ><a name="22305"
      > </a
      ><a name="22306" href="StlcProp.html#22267" class="Bound"
      >&#8866;V</a
      ><a name="22308"
      >
</a
      ><a name="22309" href="StlcProp.html#20841" class="Function"
      >preservation</a
      ><a name="22321"
      > </a
      ><a name="22322" class="Symbol"
      >(</a
      ><a name="22323" href="Stlc.html#4316" class="InductiveConstructor"
      >&#8658;-E</a
      ><a name="22326"
      > </a
      ><a name="22327" href="StlcProp.html#22327" class="Bound"
      >&#8866;L</a
      ><a name="22329"
      > </a
      ><a name="22330" href="StlcProp.html#22330" class="Bound"
      >&#8866;M</a
      ><a name="22332" class="Symbol"
      >)</a
      ><a name="22333"
      > </a
      ><a name="22334" class="Symbol"
      >(</a
      ><a name="22335" href="Stlc.html#2347" class="InductiveConstructor"
      >&#947;&#8658;&#8321;</a
      ><a name="22338"
      > </a
      ><a name="22339" href="StlcProp.html#22339" class="Bound"
      >L&#10233;L&#8242;</a
      ><a name="22343" class="Symbol"
      >)</a
      ><a name="22344"
      > </a
      ><a name="22345" class="Keyword"
      >with</a
      ><a name="22349"
      > </a
      ><a name="22350" href="StlcProp.html#20841" class="Function"
      >preservation</a
      ><a name="22362"
      > </a
      ><a name="22363" href="StlcProp.html#22327" class="Bound"
      >&#8866;L</a
      ><a name="22365"
      > </a
      ><a name="22366" href="StlcProp.html#22339" class="Bound"
      >L&#10233;L&#8242;</a
      ><a name="22370"
      >
</a
      ><a name="22371" class="Symbol"
      >...|</a
      ><a name="22375"
      > </a
      ><a name="22376" href="StlcProp.html#22376" class="Bound"
      >&#8866;L&#8242;</a
      ><a name="22379"
      > </a
      ><a name="22380" class="Symbol"
      >=</a
      ><a name="22381"
      > </a
      ><a name="22382" href="Stlc.html#4316" class="InductiveConstructor"
      >&#8658;-E</a
      ><a name="22385"
      > </a
      ><a name="22386" href="StlcProp.html#22376" class="Bound"
      >&#8866;L&#8242;</a
      ><a name="22389"
      > </a
      ><a name="22390" href="StlcProp.html#22330" class="Bound"
      >&#8866;M</a
      ><a name="22392"
      >
</a
      ><a name="22393" href="StlcProp.html#20841" class="Function"
      >preservation</a
      ><a name="22405"
      > </a
      ><a name="22406" class="Symbol"
      >(</a
      ><a name="22407" href="Stlc.html#4316" class="InductiveConstructor"
      >&#8658;-E</a
      ><a name="22410"
      > </a
      ><a name="22411" href="StlcProp.html#22411" class="Bound"
      >&#8866;L</a
      ><a name="22413"
      > </a
      ><a name="22414" href="StlcProp.html#22414" class="Bound"
      >&#8866;M</a
      ><a name="22416" class="Symbol"
      >)</a
      ><a name="22417"
      > </a
      ><a name="22418" class="Symbol"
      >(</a
      ><a name="22419" href="Stlc.html#2406" class="InductiveConstructor"
      >&#947;&#8658;&#8322;</a
      ><a name="22422"
      > </a
      ><a name="22423" href="StlcProp.html#22423" class="Bound"
      >valueL</a
      ><a name="22429"
      > </a
      ><a name="22430" href="StlcProp.html#22430" class="Bound"
      >M&#10233;M&#8242;</a
      ><a name="22434" class="Symbol"
      >)</a
      ><a name="22435"
      > </a
      ><a name="22436" class="Keyword"
      >with</a
      ><a name="22440"
      > </a
      ><a name="22441" href="StlcProp.html#20841" class="Function"
      >preservation</a
      ><a name="22453"
      > </a
      ><a name="22454" href="StlcProp.html#22414" class="Bound"
      >&#8866;M</a
      ><a name="22456"
      > </a
      ><a name="22457" href="StlcProp.html#22430" class="Bound"
      >M&#10233;M&#8242;</a
      ><a name="22461"
      >
</a
      ><a name="22462" class="Symbol"
      >...|</a
      ><a name="22466"
      > </a
      ><a name="22467" href="StlcProp.html#22467" class="Bound"
      >&#8866;M&#8242;</a
      ><a name="22470"
      > </a
      ><a name="22471" class="Symbol"
      >=</a
      ><a name="22472"
      > </a
      ><a name="22473" href="Stlc.html#4316" class="InductiveConstructor"
      >&#8658;-E</a
      ><a name="22476"
      > </a
      ><a name="22477" href="StlcProp.html#22411" class="Bound"
      >&#8866;L</a
      ><a name="22479"
      > </a
      ><a name="22480" href="StlcProp.html#22467" class="Bound"
      >&#8866;M&#8242;</a
      ><a name="22483"
      >
</a
      ><a name="22484" href="StlcProp.html#20841" class="Function"
      >preservation</a
      ><a name="22496"
      > </a
      ><a name="22497" href="Stlc.html#4397" class="InductiveConstructor"
      >&#120121;-I&#8321;</a
      ><a name="22501"
      > </a
      ><a name="22502" class="Symbol"
      >()</a
      ><a name="22504"
      >
</a
      ><a name="22505" href="StlcProp.html#20841" class="Function"
      >preservation</a
      ><a name="22517"
      > </a
      ><a name="22518" href="Stlc.html#4432" class="InductiveConstructor"
      >&#120121;-I&#8322;</a
      ><a name="22522"
      > </a
      ><a name="22523" class="Symbol"
      >()</a
      ><a name="22525"
      >
</a
      ><a name="22526" href="StlcProp.html#20841" class="Function"
      >preservation</a
      ><a name="22538"
      > </a
      ><a name="22539" class="Symbol"
      >(</a
      ><a name="22540" href="Stlc.html#4468" class="InductiveConstructor"
      >&#120121;-E</a
      ><a name="22543"
      > </a
      ><a name="22544" href="Stlc.html#4397" class="InductiveConstructor"
      >&#120121;-I&#8321;</a
      ><a name="22548"
      > </a
      ><a name="22549" href="StlcProp.html#22549" class="Bound"
      >&#8866;M</a
      ><a name="22551"
      > </a
      ><a name="22552" href="StlcProp.html#22552" class="Bound"
      >&#8866;N</a
      ><a name="22554" class="Symbol"
      >)</a
      ><a name="22555"
      > </a
      ><a name="22556" href="Stlc.html#2479" class="InductiveConstructor"
      >&#946;&#120121;&#8321;</a
      ><a name="22559"
      > </a
      ><a name="22560" class="Symbol"
      >=</a
      ><a name="22561"
      > </a
      ><a name="22562" href="StlcProp.html#22549" class="Bound"
      >&#8866;M</a
      ><a name="22564"
      >
</a
      ><a name="22565" href="StlcProp.html#20841" class="Function"
      >preservation</a
      ><a name="22577"
      > </a
      ><a name="22578" class="Symbol"
      >(</a
      ><a name="22579" href="Stlc.html#4468" class="InductiveConstructor"
      >&#120121;-E</a
      ><a name="22582"
      > </a
      ><a name="22583" href="Stlc.html#4432" class="InductiveConstructor"
      >&#120121;-I&#8322;</a
      ><a name="22587"
      > </a
      ><a name="22588" href="StlcProp.html#22588" class="Bound"
      >&#8866;M</a
      ><a name="22590"
      > </a
      ><a name="22591" href="StlcProp.html#22591" class="Bound"
      >&#8866;N</a
      ><a name="22593" class="Symbol"
      >)</a
      ><a name="22594"
      > </a
      ><a name="22595" href="Stlc.html#2531" class="InductiveConstructor"
      >&#946;&#120121;&#8322;</a
      ><a name="22598"
      > </a
      ><a name="22599" class="Symbol"
      >=</a
      ><a name="22600"
      > </a
      ><a name="22601" href="StlcProp.html#22591" class="Bound"
      >&#8866;N</a
      ><a name="22603"
      >
</a
      ><a name="22604" href="StlcProp.html#20841" class="Function"
      >preservation</a
      ><a name="22616"
      > </a
      ><a name="22617" class="Symbol"
      >(</a
      ><a name="22618" href="Stlc.html#4468" class="InductiveConstructor"
      >&#120121;-E</a
      ><a name="22621"
      > </a
      ><a name="22622" href="StlcProp.html#22622" class="Bound"
      >&#8866;L</a
      ><a name="22624"
      > </a
      ><a name="22625" href="StlcProp.html#22625" class="Bound"
      >&#8866;M</a
      ><a name="22627"
      > </a
      ><a name="22628" href="StlcProp.html#22628" class="Bound"
      >&#8866;N</a
      ><a name="22630" class="Symbol"
      >)</a
      ><a name="22631"
      > </a
      ><a name="22632" class="Symbol"
      >(</a
      ><a name="22633" href="Stlc.html#2584" class="InductiveConstructor"
      >&#947;&#120121;</a
      ><a name="22635"
      > </a
      ><a name="22636" href="StlcProp.html#22636" class="Bound"
      >L&#10233;L&#8242;</a
      ><a name="22640" class="Symbol"
      >)</a
      ><a name="22641"
      > </a
      ><a name="22642" class="Keyword"
      >with</a
      ><a name="22646"
      > </a
      ><a name="22647" href="StlcProp.html#20841" class="Function"
      >preservation</a
      ><a name="22659"
      > </a
      ><a name="22660" href="StlcProp.html#22622" class="Bound"
      >&#8866;L</a
      ><a name="22662"
      > </a
      ><a name="22663" href="StlcProp.html#22636" class="Bound"
      >L&#10233;L&#8242;</a
      ><a name="22667"
      >
</a
      ><a name="22668" class="Symbol"
      >...|</a
      ><a name="22672"
      > </a
      ><a name="22673" href="StlcProp.html#22673" class="Bound"
      >&#8866;L&#8242;</a
      ><a name="22676"
      > </a
      ><a name="22677" class="Symbol"
      >=</a
      ><a name="22678"
      > </a
      ><a name="22679" href="Stlc.html#4468" class="InductiveConstructor"
      >&#120121;-E</a
      ><a name="22682"
      > </a
      ><a name="22683" href="StlcProp.html#22673" class="Bound"
      >&#8866;L&#8242;</a
      ><a name="22686"
      > </a
      ><a name="22687" href="StlcProp.html#22625" class="Bound"
      >&#8866;M</a
      ><a name="22689"
      > </a
      ><a name="22690" href="StlcProp.html#22628" class="Bound"
      >&#8866;N</a
      ><a name="22692"
      >

</a
      ><a name="22694" class="Comment"
      >-- Writing out implicit parameters in full</a
      ><a name="22736"
      >
</a
      ><a name="22737" class="Comment"
      >-- preservation (&#8658;-E {&#915;} {&#955;&#7488; x &#8712; A &#8658; N} {M} {.A} {B} (&#8658;-I {.&#915;} {.x} {.N} {.A} {.B} &#8866;N) &#8866;M) (&#946;&#8658; {.x} {.A} {.N} {.M} valueM)</a
      ><a name="22859"
      >
</a
      ><a name="22860" class="Comment"
      >--  =  preservation-[:=] {&#915;} {x} {A} {M} {N} {B} &#8866;M &#8866;N</a
      >

</pre>

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
  (normal_form step) t /\ ~ value t.

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

