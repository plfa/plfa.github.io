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
      ><a name="333" href="https://agda.github.io/agda-stdlib/Data.Bool.html#1" class="Module"
      >Data.Bool</a
      ><a name="342"
      > </a
      ><a name="343" class="Keyword"
      >using</a
      ><a name="348"
      > </a
      ><a name="349" class="Symbol"
      >(</a
      ><a name="350" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Bool.html#67" class="Datatype"
      >Bool</a
      ><a name="354" class="Symbol"
      >;</a
      ><a name="355"
      > </a
      ><a name="356" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Bool.html#92" class="InductiveConstructor"
      >true</a
      ><a name="360" class="Symbol"
      >;</a
      ><a name="361"
      > </a
      ><a name="362" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Bool.html#86" class="InductiveConstructor"
      >false</a
      ><a name="367" class="Symbol"
      >)</a
      ><a name="368"
      >
</a
      ><a name="369" class="Keyword"
      >open</a
      ><a name="373"
      > </a
      ><a name="374" class="Keyword"
      >import</a
      ><a name="380"
      > </a
      ><a name="381" href="https://agda.github.io/agda-stdlib/Data.Maybe.html#1" class="Module"
      >Data.Maybe</a
      ><a name="391"
      > </a
      ><a name="392" class="Keyword"
      >using</a
      ><a name="397"
      > </a
      ><a name="398" class="Symbol"
      >(</a
      ><a name="399" href="https://agda.github.io/agda-stdlib/Data.Maybe.Base.html#335" class="Datatype"
      >Maybe</a
      ><a name="404" class="Symbol"
      >;</a
      ><a name="405"
      > </a
      ><a name="406" href="https://agda.github.io/agda-stdlib/Data.Maybe.html#1527" class="InductiveConstructor"
      >just</a
      ><a name="410" class="Symbol"
      >;</a
      ><a name="411"
      > </a
      ><a name="412" href="https://agda.github.io/agda-stdlib/Data.Maybe.html#1588" class="InductiveConstructor"
      >nothing</a
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
      ><a name="433" href="https://agda.github.io/agda-stdlib/Data.Product.html#1" class="Module"
      >Data.Product</a
      ><a name="445"
      > </a
      ><a name="446" class="Keyword"
      >using</a
      ><a name="451"
      > </a
      ><a name="452" class="Symbol"
      >(</a
      ><a name="453" href="https://agda.github.io/agda-stdlib/Data.Product.html#823" class="Function"
      >&#8707;</a
      ><a name="454" class="Symbol"
      >;</a
      ><a name="455"
      > </a
      ><a name="456" href="https://agda.github.io/agda-stdlib/Data.Product.html#949" class="Function"
      >&#8707;&#8322;</a
      ><a name="458" class="Symbol"
      >;</a
      ><a name="459"
      > </a
      ><a name="460" href="https://agda.github.io/agda-stdlib/Data.Product.html#509" class="InductiveConstructor Operator"
      >_,_</a
      ><a name="463" class="Symbol"
      >;</a
      ><a name="464"
      > </a
      ><a name="465" href="https://agda.github.io/agda-stdlib/Data.Product.html#1621" class="Function Operator"
      >,_</a
      ><a name="467" class="Symbol"
      >)</a
      ><a name="468"
      >
</a
      ><a name="469" class="Keyword"
      >open</a
      ><a name="473"
      > </a
      ><a name="474" class="Keyword"
      >import</a
      ><a name="480"
      > </a
      ><a name="481" href="https://agda.github.io/agda-stdlib/Data.Sum.html#1" class="Module"
      >Data.Sum</a
      ><a name="489"
      > </a
      ><a name="490" class="Keyword"
      >using</a
      ><a name="495"
      > </a
      ><a name="496" class="Symbol"
      >(</a
      ><a name="497" href="https://agda.github.io/agda-stdlib/Data.Sum.html#433" class="Datatype Operator"
      >_&#8846;_</a
      ><a name="500" class="Symbol"
      >;</a
      ><a name="501"
      > </a
      ><a name="502" href="https://agda.github.io/agda-stdlib/Data.Sum.html#489" class="InductiveConstructor"
      >inj&#8321;</a
      ><a name="506" class="Symbol"
      >;</a
      ><a name="507"
      > </a
      ><a name="508" href="https://agda.github.io/agda-stdlib/Data.Sum.html#514" class="InductiveConstructor"
      >inj&#8322;</a
      ><a name="512" class="Symbol"
      >)</a
      ><a name="513"
      >
</a
      ><a name="514" class="Keyword"
      >open</a
      ><a name="518"
      > </a
      ><a name="519" class="Keyword"
      >import</a
      ><a name="525"
      > </a
      ><a name="526" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#1" class="Module"
      >Relation.Nullary</a
      ><a name="542"
      > </a
      ><a name="543" class="Keyword"
      >using</a
      ><a name="548"
      > </a
      ><a name="549" class="Symbol"
      >(</a
      ><a name="550" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#414" class="Function Operator"
      >&#172;_</a
      ><a name="552" class="Symbol"
      >;</a
      ><a name="553"
      > </a
      ><a name="554" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#484" class="Datatype"
      >Dec</a
      ><a name="557" class="Symbol"
      >;</a
      ><a name="558"
      > </a
      ><a name="559" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#520" class="InductiveConstructor"
      >yes</a
      ><a name="562" class="Symbol"
      >;</a
      ><a name="563"
      > </a
      ><a name="564" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#547" class="InductiveConstructor"
      >no</a
      ><a name="566" class="Symbol"
      >)</a
      ><a name="567"
      >
</a
      ><a name="568" class="Keyword"
      >open</a
      ><a name="572"
      > </a
      ><a name="573" class="Keyword"
      >import</a
      ><a name="579"
      > </a
      ><a name="580" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#1" class="Module"
      >Relation.Binary.PropositionalEquality</a
      ><a name="617"
      > </a
      ><a name="618" class="Keyword"
      >using</a
      ><a name="623"
      > </a
      ><a name="624" class="Symbol"
      >(</a
      ><a name="625" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >_&#8801;_</a
      ><a name="628" class="Symbol"
      >;</a
      ><a name="629"
      > </a
      ><a name="630" href="https://agda.github.io/agda-stdlib/Relation.Binary.Core.html#4493" class="Function Operator"
      >_&#8802;_</a
      ><a name="633" class="Symbol"
      >;</a
      ><a name="634"
      > </a
      ><a name="635" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="639" class="Symbol"
      >;</a
      ><a name="640"
      > </a
      ><a name="641" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.Core.html#632" class="Function"
      >trans</a
      ><a name="646" class="Symbol"
      >;</a
      ><a name="647"
      > </a
      ><a name="648" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.Core.html#565" class="Function"
      >sym</a
      ><a name="651" class="Symbol"
      >)</a
      ><a name="652"
      >
</a
      ><a name="653" class="Keyword"
      >open</a
      ><a name="657"
      > </a
      ><a name="658" class="Keyword"
      >import</a
      ><a name="664"
      > </a
      ><a name="665" class="Module"
      >Maps</a
      ><a name="669"
      >
</a
      ><a name="670" class="Keyword"
      >open</a
      ><a name="674"
      > </a
      ><a name="675" class="Module"
      >Maps.</a
      ><a name="680" href="Maps.html#10316" class="Module"
      >PartialMap</a
      ><a name="690"
      >
</a
      ><a name="691" class="Keyword"
      >open</a
      ><a name="695"
      > </a
      ><a name="696" class="Keyword"
      >import</a
      ><a name="702"
      > </a
      ><a name="703" class="Module"
      >Stlc</a
      >
{% endraw %}</pre>


## Canonical Forms

As we saw for the simple calculus in the [Stlc]
chapter, the first step in establishing basic properties of reduction and types
is to identify the possible _canonical forms_ (i.e., well-typed closed values)
belonging to each type.  For `bool`, these are the boolean values `true` and
`false`.  For arrow types, the canonical forms are lambda-abstractions. 

<pre class="Agda">{% raw %}
<a name="1112" class="Keyword"
      >data</a
      ><a name="1116"
      > </a
      ><a name="1117" href="StlcProp.html#1117" class="Datatype Operator"
      >canonical_for_</a
      ><a name="1131"
      > </a
      ><a name="1132" class="Symbol"
      >:</a
      ><a name="1133"
      > </a
      ><a name="1134" href="Stlc.html#1144" class="Datatype"
      >Term</a
      ><a name="1138"
      > </a
      ><a name="1139" class="Symbol"
      >&#8594;</a
      ><a name="1140"
      > </a
      ><a name="1141" href="Stlc.html#1083" class="Datatype"
      >Type</a
      ><a name="1145"
      > </a
      ><a name="1146" class="Symbol"
      >&#8594;</a
      ><a name="1147"
      > </a
      ><a name="1148" class="PrimitiveType"
      >Set</a
      ><a name="1151"
      > </a
      ><a name="1152" class="Keyword"
      >where</a
      ><a name="1157"
      >
  </a
      ><a name="1160" href="StlcProp.html#1160" class="InductiveConstructor"
      >canonical-&#955;&#7488;</a
      ><a name="1172"
      > </a
      ><a name="1173" class="Symbol"
      >:</a
      ><a name="1174"
      > </a
      ><a name="1175" class="Symbol"
      >&#8704;</a
      ><a name="1176"
      > </a
      ><a name="1177" class="Symbol"
      >{</a
      ><a name="1178" href="StlcProp.html#1178" class="Bound"
      >x</a
      ><a name="1179"
      > </a
      ><a name="1180" href="StlcProp.html#1180" class="Bound"
      >A</a
      ><a name="1181"
      > </a
      ><a name="1182" href="StlcProp.html#1182" class="Bound"
      >N</a
      ><a name="1183"
      > </a
      ><a name="1184" href="StlcProp.html#1184" class="Bound"
      >B</a
      ><a name="1185" class="Symbol"
      >}</a
      ><a name="1186"
      > </a
      ><a name="1187" class="Symbol"
      >&#8594;</a
      ><a name="1188"
      > </a
      ><a name="1189" href="StlcProp.html#1117" class="Datatype Operator"
      >canonical</a
      ><a name="1198"
      > </a
      ><a name="1199" class="Symbol"
      >(</a
      ><a name="1200" href="Stlc.html#1182" class="InductiveConstructor Operator"
      >&#955;&#7488;</a
      ><a name="1202"
      > </a
      ><a name="1203" href="StlcProp.html#1178" class="Bound"
      >x</a
      ><a name="1204"
      > </a
      ><a name="1205" href="Stlc.html#1182" class="InductiveConstructor Operator"
      >&#8712;</a
      ><a name="1206"
      > </a
      ><a name="1207" href="StlcProp.html#1180" class="Bound"
      >A</a
      ><a name="1208"
      > </a
      ><a name="1209" href="Stlc.html#1182" class="InductiveConstructor Operator"
      >&#8658;</a
      ><a name="1210"
      > </a
      ><a name="1211" href="StlcProp.html#1182" class="Bound"
      >N</a
      ><a name="1212" class="Symbol"
      >)</a
      ><a name="1213"
      > </a
      ><a name="1214" href="StlcProp.html#1117" class="Datatype Operator"
      >for</a
      ><a name="1217"
      > </a
      ><a name="1218" class="Symbol"
      >(</a
      ><a name="1219" href="StlcProp.html#1180" class="Bound"
      >A</a
      ><a name="1220"
      > </a
      ><a name="1221" href="Stlc.html#1113" class="InductiveConstructor Operator"
      >&#8658;</a
      ><a name="1222"
      > </a
      ><a name="1223" href="StlcProp.html#1184" class="Bound"
      >B</a
      ><a name="1224" class="Symbol"
      >)</a
      ><a name="1225"
      >
  </a
      ><a name="1228" href="StlcProp.html#1228" class="InductiveConstructor"
      >canonical-true&#7488;</a
      ><a name="1243"
      > </a
      ><a name="1244" class="Symbol"
      >:</a
      ><a name="1245"
      > </a
      ><a name="1246" href="StlcProp.html#1117" class="Datatype Operator"
      >canonical</a
      ><a name="1255"
      > </a
      ><a name="1256" href="Stlc.html#1246" class="InductiveConstructor"
      >true&#7488;</a
      ><a name="1261"
      > </a
      ><a name="1262" href="StlcProp.html#1117" class="Datatype Operator"
      >for</a
      ><a name="1265"
      > </a
      ><a name="1266" href="Stlc.html#1102" class="InductiveConstructor"
      >&#120121;</a
      ><a name="1267"
      >
  </a
      ><a name="1270" href="StlcProp.html#1270" class="InductiveConstructor"
      >canonical-false&#7488;</a
      ><a name="1286"
      > </a
      ><a name="1287" class="Symbol"
      >:</a
      ><a name="1288"
      > </a
      ><a name="1289" href="StlcProp.html#1117" class="Datatype Operator"
      >canonical</a
      ><a name="1298"
      > </a
      ><a name="1299" href="Stlc.html#1261" class="InductiveConstructor"
      >false&#7488;</a
      ><a name="1305"
      > </a
      ><a name="1306" href="StlcProp.html#1117" class="Datatype Operator"
      >for</a
      ><a name="1309"
      > </a
      ><a name="1310" href="Stlc.html#1102" class="InductiveConstructor"
      >&#120121;</a
      ><a name="1311"
      >
  
</a
      ><a name="1315" class="Comment"
      >-- canonical_for_ : Term &#8594; Type &#8594; Set</a
      ><a name="1352"
      >
</a
      ><a name="1353" class="Comment"
      >-- canonical L for &#120121;       = L &#8801; true&#7488; &#8846; L &#8801; false&#7488;</a
      ><a name="1404"
      >
</a
      ><a name="1405" class="Comment"
      >-- canonical L for (A &#8658; B) = &#8707;&#8322; &#955; x N &#8594; L &#8801; &#955;&#7488; x &#8712; A &#8658; N</a
      ><a name="1461"
      >

</a
      ><a name="1463" href="StlcProp.html#1463" class="Function"
      >canonicalFormsLemma</a
      ><a name="1482"
      > </a
      ><a name="1483" class="Symbol"
      >:</a
      ><a name="1484"
      > </a
      ><a name="1485" class="Symbol"
      >&#8704;</a
      ><a name="1486"
      > </a
      ><a name="1487" class="Symbol"
      >{</a
      ><a name="1488" href="StlcProp.html#1488" class="Bound"
      >L</a
      ><a name="1489"
      > </a
      ><a name="1490" href="StlcProp.html#1490" class="Bound"
      >A</a
      ><a name="1491" class="Symbol"
      >}</a
      ><a name="1492"
      > </a
      ><a name="1493" class="Symbol"
      >&#8594;</a
      ><a name="1494"
      > </a
      ><a name="1495" href="Maps.html#10360" class="Function"
      >&#8709;</a
      ><a name="1496"
      > </a
      ><a name="1497" href="Stlc.html#4815" class="Datatype Operator"
      >&#8866;</a
      ><a name="1498"
      > </a
      ><a name="1499" href="StlcProp.html#1488" class="Bound"
      >L</a
      ><a name="1500"
      > </a
      ><a name="1501" href="Stlc.html#4815" class="Datatype Operator"
      >&#8712;</a
      ><a name="1502"
      > </a
      ><a name="1503" href="StlcProp.html#1490" class="Bound"
      >A</a
      ><a name="1504"
      > </a
      ><a name="1505" class="Symbol"
      >&#8594;</a
      ><a name="1506"
      > </a
      ><a name="1507" href="Stlc.html#1693" class="Datatype"
      >value</a
      ><a name="1512"
      > </a
      ><a name="1513" href="StlcProp.html#1488" class="Bound"
      >L</a
      ><a name="1514"
      > </a
      ><a name="1515" class="Symbol"
      >&#8594;</a
      ><a name="1516"
      > </a
      ><a name="1517" href="StlcProp.html#1117" class="Datatype Operator"
      >canonical</a
      ><a name="1526"
      > </a
      ><a name="1527" href="StlcProp.html#1488" class="Bound"
      >L</a
      ><a name="1528"
      > </a
      ><a name="1529" href="StlcProp.html#1117" class="Datatype Operator"
      >for</a
      ><a name="1532"
      > </a
      ><a name="1533" href="StlcProp.html#1490" class="Bound"
      >A</a
      ><a name="1534"
      >
</a
      ><a name="1535" href="StlcProp.html#1463" class="Function"
      >canonicalFormsLemma</a
      ><a name="1554"
      > </a
      ><a name="1555" class="Symbol"
      >(</a
      ><a name="1556" href="Stlc.html#4859" class="InductiveConstructor"
      >Ax</a
      ><a name="1558"
      > </a
      ><a name="1559" href="StlcProp.html#1559" class="Bound"
      >&#8866;x</a
      ><a name="1561" class="Symbol"
      >)</a
      ><a name="1562"
      > </a
      ><a name="1563" class="Symbol"
      >()</a
      ><a name="1565"
      >
</a
      ><a name="1566" href="StlcProp.html#1463" class="Function"
      >canonicalFormsLemma</a
      ><a name="1585"
      > </a
      ><a name="1586" class="Symbol"
      >(</a
      ><a name="1587" href="Stlc.html#4916" class="InductiveConstructor"
      >&#8658;-I</a
      ><a name="1590"
      > </a
      ><a name="1591" href="StlcProp.html#1591" class="Bound"
      >&#8866;N</a
      ><a name="1593" class="Symbol"
      >)</a
      ><a name="1594"
      > </a
      ><a name="1595" href="Stlc.html#1720" class="InductiveConstructor"
      >value-&#955;&#7488;</a
      ><a name="1603"
      > </a
      ><a name="1604" class="Symbol"
      >=</a
      ><a name="1605"
      > </a
      ><a name="1606" href="StlcProp.html#1160" class="InductiveConstructor"
      >canonical-&#955;&#7488;</a
      ><a name="1618"
      >      </a
      ><a name="1624" class="Comment"
      >-- _ , _ , refl</a
      ><a name="1639"
      >
</a
      ><a name="1640" href="StlcProp.html#1463" class="Function"
      >canonicalFormsLemma</a
      ><a name="1659"
      > </a
      ><a name="1660" class="Symbol"
      >(</a
      ><a name="1661" href="Stlc.html#4999" class="InductiveConstructor"
      >&#8658;-E</a
      ><a name="1664"
      > </a
      ><a name="1665" href="StlcProp.html#1665" class="Bound"
      >&#8866;L</a
      ><a name="1667"
      > </a
      ><a name="1668" href="StlcProp.html#1668" class="Bound"
      >&#8866;M</a
      ><a name="1670" class="Symbol"
      >)</a
      ><a name="1671"
      > </a
      ><a name="1672" class="Symbol"
      >()</a
      ><a name="1674"
      >
</a
      ><a name="1675" href="StlcProp.html#1463" class="Function"
      >canonicalFormsLemma</a
      ><a name="1694"
      > </a
      ><a name="1695" href="Stlc.html#5080" class="InductiveConstructor"
      >&#120121;-I&#8321;</a
      ><a name="1699"
      > </a
      ><a name="1700" href="Stlc.html#1766" class="InductiveConstructor"
      >value-true&#7488;</a
      ><a name="1711"
      > </a
      ><a name="1712" class="Symbol"
      >=</a
      ><a name="1713"
      > </a
      ><a name="1714" href="StlcProp.html#1228" class="InductiveConstructor"
      >canonical-true&#7488;</a
      ><a name="1729"
      >    </a
      ><a name="1733" class="Comment"
      >-- inj&#8321; refl</a
      ><a name="1745"
      >
</a
      ><a name="1746" href="StlcProp.html#1463" class="Function"
      >canonicalFormsLemma</a
      ><a name="1765"
      > </a
      ><a name="1766" href="Stlc.html#5115" class="InductiveConstructor"
      >&#120121;-I&#8322;</a
      ><a name="1770"
      > </a
      ><a name="1771" href="Stlc.html#1796" class="InductiveConstructor"
      >value-false&#7488;</a
      ><a name="1783"
      > </a
      ><a name="1784" class="Symbol"
      >=</a
      ><a name="1785"
      > </a
      ><a name="1786" href="StlcProp.html#1270" class="InductiveConstructor"
      >canonical-false&#7488;</a
      ><a name="1802"
      >  </a
      ><a name="1804" class="Comment"
      >-- inj&#8322; refl</a
      ><a name="1816"
      >
</a
      ><a name="1817" href="StlcProp.html#1463" class="Function"
      >canonicalFormsLemma</a
      ><a name="1836"
      > </a
      ><a name="1837" class="Symbol"
      >(</a
      ><a name="1838" href="Stlc.html#5151" class="InductiveConstructor"
      >&#120121;-E</a
      ><a name="1841"
      > </a
      ><a name="1842" href="StlcProp.html#1842" class="Bound"
      >&#8866;L</a
      ><a name="1844"
      > </a
      ><a name="1845" href="StlcProp.html#1845" class="Bound"
      >&#8866;M</a
      ><a name="1847"
      > </a
      ><a name="1848" href="StlcProp.html#1848" class="Bound"
      >&#8866;N</a
      ><a name="1850" class="Symbol"
      >)</a
      ><a name="1851"
      > </a
      ><a name="1852" class="Symbol"
      >()</a
      >
{% endraw %}</pre>

## Progress

As before, the _progress_ theorem tells us that closed, well-typed
terms are not stuck: either a well-typed term is a value, or it
can take a reduction step.  The proof is a relatively
straightforward extension of the progress proof we saw in the
[Stlc]({{ "Stlc" | relative_url }}) chapter.  We'll give the proof in English
first, then the formal version.

<pre class="Agda">{% raw %}
<a name="2251" href="StlcProp.html#2251" class="Function"
      >progress</a
      ><a name="2259"
      > </a
      ><a name="2260" class="Symbol"
      >:</a
      ><a name="2261"
      > </a
      ><a name="2262" class="Symbol"
      >&#8704;</a
      ><a name="2263"
      > </a
      ><a name="2264" class="Symbol"
      >{</a
      ><a name="2265" href="StlcProp.html#2265" class="Bound"
      >M</a
      ><a name="2266"
      > </a
      ><a name="2267" href="StlcProp.html#2267" class="Bound"
      >A</a
      ><a name="2268" class="Symbol"
      >}</a
      ><a name="2269"
      > </a
      ><a name="2270" class="Symbol"
      >&#8594;</a
      ><a name="2271"
      > </a
      ><a name="2272" href="Maps.html#10360" class="Function"
      >&#8709;</a
      ><a name="2273"
      > </a
      ><a name="2274" href="Stlc.html#4815" class="Datatype Operator"
      >&#8866;</a
      ><a name="2275"
      > </a
      ><a name="2276" href="StlcProp.html#2265" class="Bound"
      >M</a
      ><a name="2277"
      > </a
      ><a name="2278" href="Stlc.html#4815" class="Datatype Operator"
      >&#8712;</a
      ><a name="2279"
      > </a
      ><a name="2280" href="StlcProp.html#2267" class="Bound"
      >A</a
      ><a name="2281"
      > </a
      ><a name="2282" class="Symbol"
      >&#8594;</a
      ><a name="2283"
      > </a
      ><a name="2284" href="Stlc.html#1693" class="Datatype"
      >value</a
      ><a name="2289"
      > </a
      ><a name="2290" href="StlcProp.html#2265" class="Bound"
      >M</a
      ><a name="2291"
      > </a
      ><a name="2292" href="https://agda.github.io/agda-stdlib/Data.Sum.html#433" class="Datatype Operator"
      >&#8846;</a
      ><a name="2293"
      > </a
      ><a name="2294" href="https://agda.github.io/agda-stdlib/Data.Product.html#823" class="Function"
      >&#8707;</a
      ><a name="2295"
      > </a
      ><a name="2296" class="Symbol"
      >&#955;</a
      ><a name="2297"
      > </a
      ><a name="2298" href="StlcProp.html#2298" class="Bound"
      >N</a
      ><a name="2299"
      > </a
      ><a name="2300" class="Symbol"
      >&#8594;</a
      ><a name="2301"
      > </a
      ><a name="2302" href="StlcProp.html#2265" class="Bound"
      >M</a
      ><a name="2303"
      > </a
      ><a name="2304" href="Stlc.html#2353" class="Datatype Operator"
      >&#10233;</a
      ><a name="2305"
      > </a
      ><a name="2306" href="StlcProp.html#2298" class="Bound"
      >N</a
      >
{% endraw %}</pre>

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

<pre class="Agda">{% raw %}
<a name="3936" href="StlcProp.html#2251" class="Function"
      >progress</a
      ><a name="3944"
      > </a
      ><a name="3945" class="Symbol"
      >(</a
      ><a name="3946" href="Stlc.html#4859" class="InductiveConstructor"
      >Ax</a
      ><a name="3948"
      > </a
      ><a name="3949" class="Symbol"
      >())</a
      ><a name="3952"
      >
</a
      ><a name="3953" href="StlcProp.html#2251" class="Function"
      >progress</a
      ><a name="3961"
      > </a
      ><a name="3962" class="Symbol"
      >(</a
      ><a name="3963" href="Stlc.html#4916" class="InductiveConstructor"
      >&#8658;-I</a
      ><a name="3966"
      > </a
      ><a name="3967" href="StlcProp.html#3967" class="Bound"
      >&#8866;N</a
      ><a name="3969" class="Symbol"
      >)</a
      ><a name="3970"
      > </a
      ><a name="3971" class="Symbol"
      >=</a
      ><a name="3972"
      > </a
      ><a name="3973" href="https://agda.github.io/agda-stdlib/Data.Sum.html#489" class="InductiveConstructor"
      >inj&#8321;</a
      ><a name="3977"
      > </a
      ><a name="3978" href="Stlc.html#1720" class="InductiveConstructor"
      >value-&#955;&#7488;</a
      ><a name="3986"
      >
</a
      ><a name="3987" href="StlcProp.html#2251" class="Function"
      >progress</a
      ><a name="3995"
      > </a
      ><a name="3996" class="Symbol"
      >(</a
      ><a name="3997" href="Stlc.html#4999" class="InductiveConstructor"
      >&#8658;-E</a
      ><a name="4000"
      > </a
      ><a name="4001" class="Symbol"
      >{</a
      ><a name="4002" href="StlcProp.html#4002" class="Bound"
      >&#915;</a
      ><a name="4003" class="Symbol"
      >}</a
      ><a name="4004"
      > </a
      ><a name="4005" class="Symbol"
      >{</a
      ><a name="4006" href="StlcProp.html#4006" class="Bound"
      >L</a
      ><a name="4007" class="Symbol"
      >}</a
      ><a name="4008"
      > </a
      ><a name="4009" class="Symbol"
      >{</a
      ><a name="4010" href="StlcProp.html#4010" class="Bound"
      >M</a
      ><a name="4011" class="Symbol"
      >}</a
      ><a name="4012"
      > </a
      ><a name="4013" class="Symbol"
      >{</a
      ><a name="4014" href="StlcProp.html#4014" class="Bound"
      >A</a
      ><a name="4015" class="Symbol"
      >}</a
      ><a name="4016"
      > </a
      ><a name="4017" class="Symbol"
      >{</a
      ><a name="4018" href="StlcProp.html#4018" class="Bound"
      >B</a
      ><a name="4019" class="Symbol"
      >}</a
      ><a name="4020"
      > </a
      ><a name="4021" href="StlcProp.html#4021" class="Bound"
      >&#8866;L</a
      ><a name="4023"
      > </a
      ><a name="4024" href="StlcProp.html#4024" class="Bound"
      >&#8866;M</a
      ><a name="4026" class="Symbol"
      >)</a
      ><a name="4027"
      > </a
      ><a name="4028" class="Keyword"
      >with</a
      ><a name="4032"
      > </a
      ><a name="4033" href="StlcProp.html#2251" class="Function"
      >progress</a
      ><a name="4041"
      > </a
      ><a name="4042" href="StlcProp.html#4021" class="Bound"
      >&#8866;L</a
      ><a name="4044"
      >
</a
      ><a name="4045" class="Symbol"
      >...</a
      ><a name="4048"
      > </a
      ><a name="4049" class="Symbol"
      >|</a
      ><a name="4050"
      > </a
      ><a name="4051" href="https://agda.github.io/agda-stdlib/Data.Sum.html#514" class="InductiveConstructor"
      >inj&#8322;</a
      ><a name="4055"
      > </a
      ><a name="4056" class="Symbol"
      >(</a
      ><a name="4057" href="StlcProp.html#4057" class="Bound"
      >L&#8242;</a
      ><a name="4059"
      > </a
      ><a name="4060" href="https://agda.github.io/agda-stdlib/Data.Product.html#509" class="InductiveConstructor Operator"
      >,</a
      ><a name="4061"
      > </a
      ><a name="4062" href="StlcProp.html#4062" class="Bound"
      >L&#10233;L&#8242;</a
      ><a name="4066" class="Symbol"
      >)</a
      ><a name="4067"
      > </a
      ><a name="4068" class="Symbol"
      >=</a
      ><a name="4069"
      > </a
      ><a name="4070" href="https://agda.github.io/agda-stdlib/Data.Sum.html#514" class="InductiveConstructor"
      >inj&#8322;</a
      ><a name="4074"
      > </a
      ><a name="4075" class="Symbol"
      >(</a
      ><a name="4076" href="StlcProp.html#4057" class="Bound"
      >L&#8242;</a
      ><a name="4078"
      > </a
      ><a name="4079" href="Stlc.html#1218" class="InductiveConstructor Operator"
      >&#183;&#7488;</a
      ><a name="4081"
      > </a
      ><a name="4082" href="StlcProp.html#4010" class="Bound"
      >M</a
      ><a name="4083"
      > </a
      ><a name="4084" href="https://agda.github.io/agda-stdlib/Data.Product.html#509" class="InductiveConstructor Operator"
      >,</a
      ><a name="4085"
      > </a
      ><a name="4086" href="Stlc.html#2459" class="InductiveConstructor"
      >&#947;&#8658;&#8321;</a
      ><a name="4089"
      > </a
      ><a name="4090" href="StlcProp.html#4062" class="Bound"
      >L&#10233;L&#8242;</a
      ><a name="4094" class="Symbol"
      >)</a
      ><a name="4095"
      >
</a
      ><a name="4096" class="Symbol"
      >...</a
      ><a name="4099"
      > </a
      ><a name="4100" class="Symbol"
      >|</a
      ><a name="4101"
      > </a
      ><a name="4102" href="https://agda.github.io/agda-stdlib/Data.Sum.html#489" class="InductiveConstructor"
      >inj&#8321;</a
      ><a name="4106"
      > </a
      ><a name="4107" href="StlcProp.html#4107" class="Bound"
      >valueL</a
      ><a name="4113"
      > </a
      ><a name="4114" class="Keyword"
      >with</a
      ><a name="4118"
      > </a
      ><a name="4119" href="StlcProp.html#2251" class="Function"
      >progress</a
      ><a name="4127"
      > </a
      ><a name="4128" href="StlcProp.html#4024" class="Bound"
      >&#8866;M</a
      ><a name="4130"
      >
</a
      ><a name="4131" class="Symbol"
      >...</a
      ><a name="4134"
      > </a
      ><a name="4135" class="Symbol"
      >|</a
      ><a name="4136"
      > </a
      ><a name="4137" href="https://agda.github.io/agda-stdlib/Data.Sum.html#514" class="InductiveConstructor"
      >inj&#8322;</a
      ><a name="4141"
      > </a
      ><a name="4142" class="Symbol"
      >(</a
      ><a name="4143" href="StlcProp.html#4143" class="Bound"
      >M&#8242;</a
      ><a name="4145"
      > </a
      ><a name="4146" href="https://agda.github.io/agda-stdlib/Data.Product.html#509" class="InductiveConstructor Operator"
      >,</a
      ><a name="4147"
      > </a
      ><a name="4148" href="StlcProp.html#4148" class="Bound"
      >M&#10233;M&#8242;</a
      ><a name="4152" class="Symbol"
      >)</a
      ><a name="4153"
      > </a
      ><a name="4154" class="Symbol"
      >=</a
      ><a name="4155"
      > </a
      ><a name="4156" href="https://agda.github.io/agda-stdlib/Data.Sum.html#514" class="InductiveConstructor"
      >inj&#8322;</a
      ><a name="4160"
      > </a
      ><a name="4161" class="Symbol"
      >(</a
      ><a name="4162" href="StlcProp.html#4006" class="Bound"
      >L</a
      ><a name="4163"
      > </a
      ><a name="4164" href="Stlc.html#1218" class="InductiveConstructor Operator"
      >&#183;&#7488;</a
      ><a name="4166"
      > </a
      ><a name="4167" href="StlcProp.html#4143" class="Bound"
      >M&#8242;</a
      ><a name="4169"
      > </a
      ><a name="4170" href="https://agda.github.io/agda-stdlib/Data.Product.html#509" class="InductiveConstructor Operator"
      >,</a
      ><a name="4171"
      > </a
      ><a name="4172" href="Stlc.html#2518" class="InductiveConstructor"
      >&#947;&#8658;&#8322;</a
      ><a name="4175"
      > </a
      ><a name="4176" href="StlcProp.html#4107" class="Bound"
      >valueL</a
      ><a name="4182"
      > </a
      ><a name="4183" href="StlcProp.html#4148" class="Bound"
      >M&#10233;M&#8242;</a
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
      >valueM</a
      ><a name="4206"
      > </a
      ><a name="4207" class="Keyword"
      >with</a
      ><a name="4211"
      > </a
      ><a name="4212" href="StlcProp.html#1463" class="Function"
      >canonicalFormsLemma</a
      ><a name="4231"
      > </a
      ><a name="4232" href="StlcProp.html#4021" class="Bound"
      >&#8866;L</a
      ><a name="4234"
      > </a
      ><a name="4235" href="StlcProp.html#4107" class="Bound"
      >valueL</a
      ><a name="4241"
      >
</a
      ><a name="4242" class="Symbol"
      >...</a
      ><a name="4245"
      > </a
      ><a name="4246" class="Symbol"
      >|</a
      ><a name="4247"
      > </a
      ><a name="4248" href="StlcProp.html#1160" class="InductiveConstructor"
      >canonical-&#955;&#7488;</a
      ><a name="4260"
      > </a
      ><a name="4261" class="Symbol"
      >{</a
      ><a name="4262" href="StlcProp.html#4262" class="Bound"
      >x</a
      ><a name="4263" class="Symbol"
      >}</a
      ><a name="4264"
      > </a
      ><a name="4265" class="Symbol"
      >{</a
      ><a name="4266" class="DottedPattern Symbol"
      >.</a
      ><a name="4267" href="StlcProp.html#4014" class="DottedPattern Bound"
      >A</a
      ><a name="4268" class="Symbol"
      >}</a
      ><a name="4269"
      > </a
      ><a name="4270" class="Symbol"
      >{</a
      ><a name="4271" href="StlcProp.html#4271" class="Bound"
      >N</a
      ><a name="4272" class="Symbol"
      >}</a
      ><a name="4273"
      > </a
      ><a name="4274" class="Symbol"
      >{</a
      ><a name="4275" class="DottedPattern Symbol"
      >.</a
      ><a name="4276" href="StlcProp.html#4018" class="DottedPattern Bound"
      >B</a
      ><a name="4277" class="Symbol"
      >}</a
      ><a name="4278"
      > </a
      ><a name="4279" class="Symbol"
      >=</a
      ><a name="4280"
      > </a
      ><a name="4281" href="https://agda.github.io/agda-stdlib/Data.Sum.html#514" class="InductiveConstructor"
      >inj&#8322;</a
      ><a name="4285"
      > </a
      ><a name="4286" class="Symbol"
      >((</a
      ><a name="4288" href="StlcProp.html#4271" class="Bound"
      >N</a
      ><a name="4289"
      > </a
      ><a name="4290" href="Stlc.html#1868" class="Function Operator"
      >[</a
      ><a name="4291"
      > </a
      ><a name="4292" href="StlcProp.html#4262" class="Bound"
      >x</a
      ><a name="4293"
      > </a
      ><a name="4294" href="Stlc.html#1868" class="Function Operator"
      >:=</a
      ><a name="4296"
      > </a
      ><a name="4297" href="StlcProp.html#4010" class="Bound"
      >M</a
      ><a name="4298"
      > </a
      ><a name="4299" href="Stlc.html#1868" class="Function Operator"
      >]</a
      ><a name="4300" class="Symbol"
      >)</a
      ><a name="4301"
      > </a
      ><a name="4302" href="https://agda.github.io/agda-stdlib/Data.Product.html#509" class="InductiveConstructor Operator"
      >,</a
      ><a name="4303"
      > </a
      ><a name="4304" href="Stlc.html#2385" class="InductiveConstructor"
      >&#946;&#8658;</a
      ><a name="4306"
      > </a
      ><a name="4307" href="StlcProp.html#4200" class="Bound"
      >valueM</a
      ><a name="4313" class="Symbol"
      >)</a
      ><a name="4314"
      >
</a
      ><a name="4315" href="StlcProp.html#2251" class="Function"
      >progress</a
      ><a name="4323"
      > </a
      ><a name="4324" href="Stlc.html#5080" class="InductiveConstructor"
      >&#120121;-I&#8321;</a
      ><a name="4328"
      > </a
      ><a name="4329" class="Symbol"
      >=</a
      ><a name="4330"
      > </a
      ><a name="4331" href="https://agda.github.io/agda-stdlib/Data.Sum.html#489" class="InductiveConstructor"
      >inj&#8321;</a
      ><a name="4335"
      > </a
      ><a name="4336" href="Stlc.html#1766" class="InductiveConstructor"
      >value-true&#7488;</a
      ><a name="4347"
      >
</a
      ><a name="4348" href="StlcProp.html#2251" class="Function"
      >progress</a
      ><a name="4356"
      > </a
      ><a name="4357" href="Stlc.html#5115" class="InductiveConstructor"
      >&#120121;-I&#8322;</a
      ><a name="4361"
      > </a
      ><a name="4362" class="Symbol"
      >=</a
      ><a name="4363"
      > </a
      ><a name="4364" href="https://agda.github.io/agda-stdlib/Data.Sum.html#489" class="InductiveConstructor"
      >inj&#8321;</a
      ><a name="4368"
      > </a
      ><a name="4369" href="Stlc.html#1796" class="InductiveConstructor"
      >value-false&#7488;</a
      ><a name="4381"
      >
</a
      ><a name="4382" href="StlcProp.html#2251" class="Function"
      >progress</a
      ><a name="4390"
      > </a
      ><a name="4391" class="Symbol"
      >(</a
      ><a name="4392" href="Stlc.html#5151" class="InductiveConstructor"
      >&#120121;-E</a
      ><a name="4395"
      > </a
      ><a name="4396" class="Symbol"
      >{</a
      ><a name="4397" href="StlcProp.html#4397" class="Bound"
      >&#915;</a
      ><a name="4398" class="Symbol"
      >}</a
      ><a name="4399"
      > </a
      ><a name="4400" class="Symbol"
      >{</a
      ><a name="4401" href="StlcProp.html#4401" class="Bound"
      >L</a
      ><a name="4402" class="Symbol"
      >}</a
      ><a name="4403"
      > </a
      ><a name="4404" class="Symbol"
      >{</a
      ><a name="4405" href="StlcProp.html#4405" class="Bound"
      >M</a
      ><a name="4406" class="Symbol"
      >}</a
      ><a name="4407"
      > </a
      ><a name="4408" class="Symbol"
      >{</a
      ><a name="4409" href="StlcProp.html#4409" class="Bound"
      >N</a
      ><a name="4410" class="Symbol"
      >}</a
      ><a name="4411"
      > </a
      ><a name="4412" class="Symbol"
      >{</a
      ><a name="4413" href="StlcProp.html#4413" class="Bound"
      >A</a
      ><a name="4414" class="Symbol"
      >}</a
      ><a name="4415"
      > </a
      ><a name="4416" href="StlcProp.html#4416" class="Bound"
      >&#8866;L</a
      ><a name="4418"
      > </a
      ><a name="4419" href="StlcProp.html#4419" class="Bound"
      >&#8866;M</a
      ><a name="4421"
      > </a
      ><a name="4422" href="StlcProp.html#4422" class="Bound"
      >&#8866;N</a
      ><a name="4424" class="Symbol"
      >)</a
      ><a name="4425"
      > </a
      ><a name="4426" class="Keyword"
      >with</a
      ><a name="4430"
      > </a
      ><a name="4431" href="StlcProp.html#2251" class="Function"
      >progress</a
      ><a name="4439"
      > </a
      ><a name="4440" href="StlcProp.html#4416" class="Bound"
      >&#8866;L</a
      ><a name="4442"
      >
</a
      ><a name="4443" class="Symbol"
      >...</a
      ><a name="4446"
      > </a
      ><a name="4447" class="Symbol"
      >|</a
      ><a name="4448"
      > </a
      ><a name="4449" href="https://agda.github.io/agda-stdlib/Data.Sum.html#514" class="InductiveConstructor"
      >inj&#8322;</a
      ><a name="4453"
      > </a
      ><a name="4454" class="Symbol"
      >(</a
      ><a name="4455" href="StlcProp.html#4455" class="Bound"
      >L&#8242;</a
      ><a name="4457"
      > </a
      ><a name="4458" href="https://agda.github.io/agda-stdlib/Data.Product.html#509" class="InductiveConstructor Operator"
      >,</a
      ><a name="4459"
      > </a
      ><a name="4460" href="StlcProp.html#4460" class="Bound"
      >L&#10233;L&#8242;</a
      ><a name="4464" class="Symbol"
      >)</a
      ><a name="4465"
      > </a
      ><a name="4466" class="Symbol"
      >=</a
      ><a name="4467"
      > </a
      ><a name="4468" href="https://agda.github.io/agda-stdlib/Data.Sum.html#514" class="InductiveConstructor"
      >inj&#8322;</a
      ><a name="4472"
      > </a
      ><a name="4473" class="Symbol"
      >((</a
      ><a name="4475" href="Stlc.html#1277" class="InductiveConstructor Operator"
      >if&#7488;</a
      ><a name="4478"
      > </a
      ><a name="4479" href="StlcProp.html#4455" class="Bound"
      >L&#8242;</a
      ><a name="4481"
      > </a
      ><a name="4482" href="Stlc.html#1277" class="InductiveConstructor Operator"
      >then</a
      ><a name="4486"
      > </a
      ><a name="4487" href="StlcProp.html#4405" class="Bound"
      >M</a
      ><a name="4488"
      > </a
      ><a name="4489" href="Stlc.html#1277" class="InductiveConstructor Operator"
      >else</a
      ><a name="4493"
      > </a
      ><a name="4494" href="StlcProp.html#4409" class="Bound"
      >N</a
      ><a name="4495" class="Symbol"
      >)</a
      ><a name="4496"
      > </a
      ><a name="4497" href="https://agda.github.io/agda-stdlib/Data.Product.html#509" class="InductiveConstructor Operator"
      >,</a
      ><a name="4498"
      > </a
      ><a name="4499" href="Stlc.html#2696" class="InductiveConstructor"
      >&#947;&#120121;</a
      ><a name="4501"
      > </a
      ><a name="4502" href="StlcProp.html#4460" class="Bound"
      >L&#10233;L&#8242;</a
      ><a name="4506" class="Symbol"
      >)</a
      ><a name="4507"
      >
</a
      ><a name="4508" class="Symbol"
      >...</a
      ><a name="4511"
      > </a
      ><a name="4512" class="Symbol"
      >|</a
      ><a name="4513"
      > </a
      ><a name="4514" href="https://agda.github.io/agda-stdlib/Data.Sum.html#489" class="InductiveConstructor"
      >inj&#8321;</a
      ><a name="4518"
      > </a
      ><a name="4519" href="StlcProp.html#4519" class="Bound"
      >valueL</a
      ><a name="4525"
      > </a
      ><a name="4526" class="Keyword"
      >with</a
      ><a name="4530"
      > </a
      ><a name="4531" href="StlcProp.html#1463" class="Function"
      >canonicalFormsLemma</a
      ><a name="4550"
      > </a
      ><a name="4551" href="StlcProp.html#4416" class="Bound"
      >&#8866;L</a
      ><a name="4553"
      > </a
      ><a name="4554" href="StlcProp.html#4519" class="Bound"
      >valueL</a
      ><a name="4560"
      >
</a
      ><a name="4561" class="Symbol"
      >...</a
      ><a name="4564"
      > </a
      ><a name="4565" class="Symbol"
      >|</a
      ><a name="4566"
      > </a
      ><a name="4567" href="StlcProp.html#1228" class="InductiveConstructor"
      >canonical-true&#7488;</a
      ><a name="4582"
      > </a
      ><a name="4583" class="Symbol"
      >=</a
      ><a name="4584"
      > </a
      ><a name="4585" href="https://agda.github.io/agda-stdlib/Data.Sum.html#514" class="InductiveConstructor"
      >inj&#8322;</a
      ><a name="4589"
      > </a
      ><a name="4590" class="Symbol"
      >(</a
      ><a name="4591" href="StlcProp.html#4405" class="Bound"
      >M</a
      ><a name="4592"
      > </a
      ><a name="4593" href="https://agda.github.io/agda-stdlib/Data.Product.html#509" class="InductiveConstructor Operator"
      >,</a
      ><a name="4594"
      > </a
      ><a name="4595" href="Stlc.html#2591" class="InductiveConstructor"
      >&#946;&#120121;&#8321;</a
      ><a name="4598" class="Symbol"
      >)</a
      ><a name="4599"
      >
</a
      ><a name="4600" class="Symbol"
      >...</a
      ><a name="4603"
      > </a
      ><a name="4604" class="Symbol"
      >|</a
      ><a name="4605"
      > </a
      ><a name="4606" href="StlcProp.html#1270" class="InductiveConstructor"
      >canonical-false&#7488;</a
      ><a name="4622"
      > </a
      ><a name="4623" class="Symbol"
      >=</a
      ><a name="4624"
      > </a
      ><a name="4625" href="https://agda.github.io/agda-stdlib/Data.Sum.html#514" class="InductiveConstructor"
      >inj&#8322;</a
      ><a name="4629"
      > </a
      ><a name="4630" class="Symbol"
      >(</a
      ><a name="4631" href="StlcProp.html#4409" class="Bound"
      >N</a
      ><a name="4632"
      > </a
      ><a name="4633" href="https://agda.github.io/agda-stdlib/Data.Product.html#509" class="InductiveConstructor Operator"
      >,</a
      ><a name="4634"
      > </a
      ><a name="4635" href="Stlc.html#2643" class="InductiveConstructor"
      >&#946;&#120121;&#8322;</a
      ><a name="4638" class="Symbol"
      >)</a
      >
{% endraw %}</pre>

#### Exercise: 3 stars, optional (progress_from_term_ind)
Show that progress can also be proved by induction on terms
instead of induction on typing derivations.

<pre class="Agda">{% raw %}
<a name="4828" class="Keyword"
      >postulate</a
      ><a name="4837"
      >
  </a
      ><a name="4840" href="StlcProp.html#4840" class="Postulate"
      >progress&#8242;</a
      ><a name="4849"
      > </a
      ><a name="4850" class="Symbol"
      >:</a
      ><a name="4851"
      > </a
      ><a name="4852" class="Symbol"
      >&#8704;</a
      ><a name="4853"
      > </a
      ><a name="4854" class="Symbol"
      >{</a
      ><a name="4855" href="StlcProp.html#4855" class="Bound"
      >M</a
      ><a name="4856"
      > </a
      ><a name="4857" href="StlcProp.html#4857" class="Bound"
      >A</a
      ><a name="4858" class="Symbol"
      >}</a
      ><a name="4859"
      > </a
      ><a name="4860" class="Symbol"
      >&#8594;</a
      ><a name="4861"
      > </a
      ><a name="4862" href="Maps.html#10360" class="Function"
      >&#8709;</a
      ><a name="4863"
      > </a
      ><a name="4864" href="Stlc.html#4815" class="Datatype Operator"
      >&#8866;</a
      ><a name="4865"
      > </a
      ><a name="4866" href="StlcProp.html#4855" class="Bound"
      >M</a
      ><a name="4867"
      > </a
      ><a name="4868" href="Stlc.html#4815" class="Datatype Operator"
      >&#8712;</a
      ><a name="4869"
      > </a
      ><a name="4870" href="StlcProp.html#4857" class="Bound"
      >A</a
      ><a name="4871"
      > </a
      ><a name="4872" class="Symbol"
      >&#8594;</a
      ><a name="4873"
      > </a
      ><a name="4874" href="Stlc.html#1693" class="Datatype"
      >value</a
      ><a name="4879"
      > </a
      ><a name="4880" href="StlcProp.html#4855" class="Bound"
      >M</a
      ><a name="4881"
      > </a
      ><a name="4882" href="https://agda.github.io/agda-stdlib/Data.Sum.html#433" class="Datatype Operator"
      >&#8846;</a
      ><a name="4883"
      > </a
      ><a name="4884" href="https://agda.github.io/agda-stdlib/Data.Product.html#823" class="Function"
      >&#8707;</a
      ><a name="4885"
      > </a
      ><a name="4886" class="Symbol"
      >&#955;</a
      ><a name="4887"
      > </a
      ><a name="4888" href="StlcProp.html#4888" class="Bound"
      >N</a
      ><a name="4889"
      > </a
      ><a name="4890" class="Symbol"
      >&#8594;</a
      ><a name="4891"
      > </a
      ><a name="4892" href="StlcProp.html#4855" class="Bound"
      >M</a
      ><a name="4893"
      > </a
      ><a name="4894" href="Stlc.html#2353" class="Datatype Operator"
      >&#10233;</a
      ><a name="4895"
      > </a
      ><a name="4896" href="StlcProp.html#4888" class="Bound"
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

  - `y` appears free, but `x` does not, in `λᵀ x ∈ (A ⇒ B) ⇒ x ·ᵀ y`
  - both `x` and `y` appear free in `(λᵀ x ∈ (A ⇒ B) ⇒ x ·ᵀ y) ·ᵀ x`
  - no variables appear free in `λᵀ x ∈ (A ⇒ B) ⇒ (λᵀ y ∈ A ⇒ x ·ᵀ y)`

Formally:

<pre class="Agda">{% raw %}
<a name="7292" class="Keyword"
      >data</a
      ><a name="7296"
      > </a
      ><a name="7297" href="StlcProp.html#7297" class="Datatype Operator"
      >_FreeIn_</a
      ><a name="7305"
      > </a
      ><a name="7306" class="Symbol"
      >:</a
      ><a name="7307"
      > </a
      ><a name="7308" href="Maps.html#2215" class="Datatype"
      >Id</a
      ><a name="7310"
      > </a
      ><a name="7311" class="Symbol"
      >&#8594;</a
      ><a name="7312"
      > </a
      ><a name="7313" href="Stlc.html#1144" class="Datatype"
      >Term</a
      ><a name="7317"
      > </a
      ><a name="7318" class="Symbol"
      >&#8594;</a
      ><a name="7319"
      > </a
      ><a name="7320" class="PrimitiveType"
      >Set</a
      ><a name="7323"
      > </a
      ><a name="7324" class="Keyword"
      >where</a
      ><a name="7329"
      >
  </a
      ><a name="7332" href="StlcProp.html#7332" class="InductiveConstructor"
      >free-var&#7488;</a
      ><a name="7341"
      >  </a
      ><a name="7343" class="Symbol"
      >:</a
      ><a name="7344"
      > </a
      ><a name="7345" class="Symbol"
      >&#8704;</a
      ><a name="7346"
      > </a
      ><a name="7347" class="Symbol"
      >{</a
      ><a name="7348" href="StlcProp.html#7348" class="Bound"
      >x</a
      ><a name="7349" class="Symbol"
      >}</a
      ><a name="7350"
      > </a
      ><a name="7351" class="Symbol"
      >&#8594;</a
      ><a name="7352"
      > </a
      ><a name="7353" href="StlcProp.html#7348" class="Bound"
      >x</a
      ><a name="7354"
      > </a
      ><a name="7355" href="StlcProp.html#7297" class="Datatype Operator"
      >FreeIn</a
      ><a name="7361"
      > </a
      ><a name="7362" class="Symbol"
      >(</a
      ><a name="7363" href="Stlc.html#1163" class="InductiveConstructor"
      >var&#7488;</a
      ><a name="7367"
      > </a
      ><a name="7368" href="StlcProp.html#7348" class="Bound"
      >x</a
      ><a name="7369" class="Symbol"
      >)</a
      ><a name="7370"
      >
  </a
      ><a name="7373" href="StlcProp.html#7373" class="InductiveConstructor"
      >free-&#955;&#7488;</a
      ><a name="7380"
      >  </a
      ><a name="7382" class="Symbol"
      >:</a
      ><a name="7383"
      > </a
      ><a name="7384" class="Symbol"
      >&#8704;</a
      ><a name="7385"
      > </a
      ><a name="7386" class="Symbol"
      >{</a
      ><a name="7387" href="StlcProp.html#7387" class="Bound"
      >x</a
      ><a name="7388"
      > </a
      ><a name="7389" href="StlcProp.html#7389" class="Bound"
      >y</a
      ><a name="7390"
      > </a
      ><a name="7391" href="StlcProp.html#7391" class="Bound"
      >A</a
      ><a name="7392"
      > </a
      ><a name="7393" href="StlcProp.html#7393" class="Bound"
      >N</a
      ><a name="7394" class="Symbol"
      >}</a
      ><a name="7395"
      > </a
      ><a name="7396" class="Symbol"
      >&#8594;</a
      ><a name="7397"
      > </a
      ><a name="7398" href="StlcProp.html#7389" class="Bound"
      >y</a
      ><a name="7399"
      > </a
      ><a name="7400" href="https://agda.github.io/agda-stdlib/Relation.Binary.Core.html#4493" class="Function Operator"
      >&#8802;</a
      ><a name="7401"
      > </a
      ><a name="7402" href="StlcProp.html#7387" class="Bound"
      >x</a
      ><a name="7403"
      > </a
      ><a name="7404" class="Symbol"
      >&#8594;</a
      ><a name="7405"
      > </a
      ><a name="7406" href="StlcProp.html#7387" class="Bound"
      >x</a
      ><a name="7407"
      > </a
      ><a name="7408" href="StlcProp.html#7297" class="Datatype Operator"
      >FreeIn</a
      ><a name="7414"
      > </a
      ><a name="7415" href="StlcProp.html#7393" class="Bound"
      >N</a
      ><a name="7416"
      > </a
      ><a name="7417" class="Symbol"
      >&#8594;</a
      ><a name="7418"
      > </a
      ><a name="7419" href="StlcProp.html#7387" class="Bound"
      >x</a
      ><a name="7420"
      > </a
      ><a name="7421" href="StlcProp.html#7297" class="Datatype Operator"
      >FreeIn</a
      ><a name="7427"
      > </a
      ><a name="7428" class="Symbol"
      >(</a
      ><a name="7429" href="Stlc.html#1182" class="InductiveConstructor Operator"
      >&#955;&#7488;</a
      ><a name="7431"
      > </a
      ><a name="7432" href="StlcProp.html#7389" class="Bound"
      >y</a
      ><a name="7433"
      > </a
      ><a name="7434" href="Stlc.html#1182" class="InductiveConstructor Operator"
      >&#8712;</a
      ><a name="7435"
      > </a
      ><a name="7436" href="StlcProp.html#7391" class="Bound"
      >A</a
      ><a name="7437"
      > </a
      ><a name="7438" href="Stlc.html#1182" class="InductiveConstructor Operator"
      >&#8658;</a
      ><a name="7439"
      > </a
      ><a name="7440" href="StlcProp.html#7393" class="Bound"
      >N</a
      ><a name="7441" class="Symbol"
      >)</a
      ><a name="7442"
      >
  </a
      ><a name="7445" href="StlcProp.html#7445" class="InductiveConstructor"
      >free-&#183;&#7488;&#8321;</a
      ><a name="7453"
      > </a
      ><a name="7454" class="Symbol"
      >:</a
      ><a name="7455"
      > </a
      ><a name="7456" class="Symbol"
      >&#8704;</a
      ><a name="7457"
      > </a
      ><a name="7458" class="Symbol"
      >{</a
      ><a name="7459" href="StlcProp.html#7459" class="Bound"
      >x</a
      ><a name="7460"
      > </a
      ><a name="7461" href="StlcProp.html#7461" class="Bound"
      >L</a
      ><a name="7462"
      > </a
      ><a name="7463" href="StlcProp.html#7463" class="Bound"
      >M</a
      ><a name="7464" class="Symbol"
      >}</a
      ><a name="7465"
      > </a
      ><a name="7466" class="Symbol"
      >&#8594;</a
      ><a name="7467"
      > </a
      ><a name="7468" href="StlcProp.html#7459" class="Bound"
      >x</a
      ><a name="7469"
      > </a
      ><a name="7470" href="StlcProp.html#7297" class="Datatype Operator"
      >FreeIn</a
      ><a name="7476"
      > </a
      ><a name="7477" href="StlcProp.html#7461" class="Bound"
      >L</a
      ><a name="7478"
      > </a
      ><a name="7479" class="Symbol"
      >&#8594;</a
      ><a name="7480"
      > </a
      ><a name="7481" href="StlcProp.html#7459" class="Bound"
      >x</a
      ><a name="7482"
      > </a
      ><a name="7483" href="StlcProp.html#7297" class="Datatype Operator"
      >FreeIn</a
      ><a name="7489"
      > </a
      ><a name="7490" class="Symbol"
      >(</a
      ><a name="7491" href="StlcProp.html#7461" class="Bound"
      >L</a
      ><a name="7492"
      > </a
      ><a name="7493" href="Stlc.html#1218" class="InductiveConstructor Operator"
      >&#183;&#7488;</a
      ><a name="7495"
      > </a
      ><a name="7496" href="StlcProp.html#7463" class="Bound"
      >M</a
      ><a name="7497" class="Symbol"
      >)</a
      ><a name="7498"
      >
  </a
      ><a name="7501" href="StlcProp.html#7501" class="InductiveConstructor"
      >free-&#183;&#7488;&#8322;</a
      ><a name="7509"
      > </a
      ><a name="7510" class="Symbol"
      >:</a
      ><a name="7511"
      > </a
      ><a name="7512" class="Symbol"
      >&#8704;</a
      ><a name="7513"
      > </a
      ><a name="7514" class="Symbol"
      >{</a
      ><a name="7515" href="StlcProp.html#7515" class="Bound"
      >x</a
      ><a name="7516"
      > </a
      ><a name="7517" href="StlcProp.html#7517" class="Bound"
      >L</a
      ><a name="7518"
      > </a
      ><a name="7519" href="StlcProp.html#7519" class="Bound"
      >M</a
      ><a name="7520" class="Symbol"
      >}</a
      ><a name="7521"
      > </a
      ><a name="7522" class="Symbol"
      >&#8594;</a
      ><a name="7523"
      > </a
      ><a name="7524" href="StlcProp.html#7515" class="Bound"
      >x</a
      ><a name="7525"
      > </a
      ><a name="7526" href="StlcProp.html#7297" class="Datatype Operator"
      >FreeIn</a
      ><a name="7532"
      > </a
      ><a name="7533" href="StlcProp.html#7519" class="Bound"
      >M</a
      ><a name="7534"
      > </a
      ><a name="7535" class="Symbol"
      >&#8594;</a
      ><a name="7536"
      > </a
      ><a name="7537" href="StlcProp.html#7515" class="Bound"
      >x</a
      ><a name="7538"
      > </a
      ><a name="7539" href="StlcProp.html#7297" class="Datatype Operator"
      >FreeIn</a
      ><a name="7545"
      > </a
      ><a name="7546" class="Symbol"
      >(</a
      ><a name="7547" href="StlcProp.html#7517" class="Bound"
      >L</a
      ><a name="7548"
      > </a
      ><a name="7549" href="Stlc.html#1218" class="InductiveConstructor Operator"
      >&#183;&#7488;</a
      ><a name="7551"
      > </a
      ><a name="7552" href="StlcProp.html#7519" class="Bound"
      >M</a
      ><a name="7553" class="Symbol"
      >)</a
      ><a name="7554"
      >
  </a
      ><a name="7557" href="StlcProp.html#7557" class="InductiveConstructor"
      >free-if&#7488;&#8321;</a
      ><a name="7566"
      > </a
      ><a name="7567" class="Symbol"
      >:</a
      ><a name="7568"
      > </a
      ><a name="7569" class="Symbol"
      >&#8704;</a
      ><a name="7570"
      > </a
      ><a name="7571" class="Symbol"
      >{</a
      ><a name="7572" href="StlcProp.html#7572" class="Bound"
      >x</a
      ><a name="7573"
      > </a
      ><a name="7574" href="StlcProp.html#7574" class="Bound"
      >L</a
      ><a name="7575"
      > </a
      ><a name="7576" href="StlcProp.html#7576" class="Bound"
      >M</a
      ><a name="7577"
      > </a
      ><a name="7578" href="StlcProp.html#7578" class="Bound"
      >N</a
      ><a name="7579" class="Symbol"
      >}</a
      ><a name="7580"
      > </a
      ><a name="7581" class="Symbol"
      >&#8594;</a
      ><a name="7582"
      > </a
      ><a name="7583" href="StlcProp.html#7572" class="Bound"
      >x</a
      ><a name="7584"
      > </a
      ><a name="7585" href="StlcProp.html#7297" class="Datatype Operator"
      >FreeIn</a
      ><a name="7591"
      > </a
      ><a name="7592" href="StlcProp.html#7574" class="Bound"
      >L</a
      ><a name="7593"
      > </a
      ><a name="7594" class="Symbol"
      >&#8594;</a
      ><a name="7595"
      > </a
      ><a name="7596" href="StlcProp.html#7572" class="Bound"
      >x</a
      ><a name="7597"
      > </a
      ><a name="7598" href="StlcProp.html#7297" class="Datatype Operator"
      >FreeIn</a
      ><a name="7604"
      > </a
      ><a name="7605" class="Symbol"
      >(</a
      ><a name="7606" href="Stlc.html#1277" class="InductiveConstructor Operator"
      >if&#7488;</a
      ><a name="7609"
      > </a
      ><a name="7610" href="StlcProp.html#7574" class="Bound"
      >L</a
      ><a name="7611"
      > </a
      ><a name="7612" href="Stlc.html#1277" class="InductiveConstructor Operator"
      >then</a
      ><a name="7616"
      > </a
      ><a name="7617" href="StlcProp.html#7576" class="Bound"
      >M</a
      ><a name="7618"
      > </a
      ><a name="7619" href="Stlc.html#1277" class="InductiveConstructor Operator"
      >else</a
      ><a name="7623"
      > </a
      ><a name="7624" href="StlcProp.html#7578" class="Bound"
      >N</a
      ><a name="7625" class="Symbol"
      >)</a
      ><a name="7626"
      >
  </a
      ><a name="7629" href="StlcProp.html#7629" class="InductiveConstructor"
      >free-if&#7488;&#8322;</a
      ><a name="7638"
      > </a
      ><a name="7639" class="Symbol"
      >:</a
      ><a name="7640"
      > </a
      ><a name="7641" class="Symbol"
      >&#8704;</a
      ><a name="7642"
      > </a
      ><a name="7643" class="Symbol"
      >{</a
      ><a name="7644" href="StlcProp.html#7644" class="Bound"
      >x</a
      ><a name="7645"
      > </a
      ><a name="7646" href="StlcProp.html#7646" class="Bound"
      >L</a
      ><a name="7647"
      > </a
      ><a name="7648" href="StlcProp.html#7648" class="Bound"
      >M</a
      ><a name="7649"
      > </a
      ><a name="7650" href="StlcProp.html#7650" class="Bound"
      >N</a
      ><a name="7651" class="Symbol"
      >}</a
      ><a name="7652"
      > </a
      ><a name="7653" class="Symbol"
      >&#8594;</a
      ><a name="7654"
      > </a
      ><a name="7655" href="StlcProp.html#7644" class="Bound"
      >x</a
      ><a name="7656"
      > </a
      ><a name="7657" href="StlcProp.html#7297" class="Datatype Operator"
      >FreeIn</a
      ><a name="7663"
      > </a
      ><a name="7664" href="StlcProp.html#7648" class="Bound"
      >M</a
      ><a name="7665"
      > </a
      ><a name="7666" class="Symbol"
      >&#8594;</a
      ><a name="7667"
      > </a
      ><a name="7668" href="StlcProp.html#7644" class="Bound"
      >x</a
      ><a name="7669"
      > </a
      ><a name="7670" href="StlcProp.html#7297" class="Datatype Operator"
      >FreeIn</a
      ><a name="7676"
      > </a
      ><a name="7677" class="Symbol"
      >(</a
      ><a name="7678" href="Stlc.html#1277" class="InductiveConstructor Operator"
      >if&#7488;</a
      ><a name="7681"
      > </a
      ><a name="7682" href="StlcProp.html#7646" class="Bound"
      >L</a
      ><a name="7683"
      > </a
      ><a name="7684" href="Stlc.html#1277" class="InductiveConstructor Operator"
      >then</a
      ><a name="7688"
      > </a
      ><a name="7689" href="StlcProp.html#7648" class="Bound"
      >M</a
      ><a name="7690"
      > </a
      ><a name="7691" href="Stlc.html#1277" class="InductiveConstructor Operator"
      >else</a
      ><a name="7695"
      > </a
      ><a name="7696" href="StlcProp.html#7650" class="Bound"
      >N</a
      ><a name="7697" class="Symbol"
      >)</a
      ><a name="7698"
      >
  </a
      ><a name="7701" href="StlcProp.html#7701" class="InductiveConstructor"
      >free-if&#7488;&#8323;</a
      ><a name="7710"
      > </a
      ><a name="7711" class="Symbol"
      >:</a
      ><a name="7712"
      > </a
      ><a name="7713" class="Symbol"
      >&#8704;</a
      ><a name="7714"
      > </a
      ><a name="7715" class="Symbol"
      >{</a
      ><a name="7716" href="StlcProp.html#7716" class="Bound"
      >x</a
      ><a name="7717"
      > </a
      ><a name="7718" href="StlcProp.html#7718" class="Bound"
      >L</a
      ><a name="7719"
      > </a
      ><a name="7720" href="StlcProp.html#7720" class="Bound"
      >M</a
      ><a name="7721"
      > </a
      ><a name="7722" href="StlcProp.html#7722" class="Bound"
      >N</a
      ><a name="7723" class="Symbol"
      >}</a
      ><a name="7724"
      > </a
      ><a name="7725" class="Symbol"
      >&#8594;</a
      ><a name="7726"
      > </a
      ><a name="7727" href="StlcProp.html#7716" class="Bound"
      >x</a
      ><a name="7728"
      > </a
      ><a name="7729" href="StlcProp.html#7297" class="Datatype Operator"
      >FreeIn</a
      ><a name="7735"
      > </a
      ><a name="7736" href="StlcProp.html#7722" class="Bound"
      >N</a
      ><a name="7737"
      > </a
      ><a name="7738" class="Symbol"
      >&#8594;</a
      ><a name="7739"
      > </a
      ><a name="7740" href="StlcProp.html#7716" class="Bound"
      >x</a
      ><a name="7741"
      > </a
      ><a name="7742" href="StlcProp.html#7297" class="Datatype Operator"
      >FreeIn</a
      ><a name="7748"
      > </a
      ><a name="7749" class="Symbol"
      >(</a
      ><a name="7750" href="Stlc.html#1277" class="InductiveConstructor Operator"
      >if&#7488;</a
      ><a name="7753"
      > </a
      ><a name="7754" href="StlcProp.html#7718" class="Bound"
      >L</a
      ><a name="7755"
      > </a
      ><a name="7756" href="Stlc.html#1277" class="InductiveConstructor Operator"
      >then</a
      ><a name="7760"
      > </a
      ><a name="7761" href="StlcProp.html#7720" class="Bound"
      >M</a
      ><a name="7762"
      > </a
      ><a name="7763" href="Stlc.html#1277" class="InductiveConstructor Operator"
      >else</a
      ><a name="7767"
      > </a
      ><a name="7768" href="StlcProp.html#7722" class="Bound"
      >N</a
      ><a name="7769" class="Symbol"
      >)</a
      >
{% endraw %}</pre>

A term in which no variables appear free is said to be _closed_.

<pre class="Agda">{% raw %}
<a name="7862" href="StlcProp.html#7862" class="Function"
      >closed</a
      ><a name="7868"
      > </a
      ><a name="7869" class="Symbol"
      >:</a
      ><a name="7870"
      > </a
      ><a name="7871" href="Stlc.html#1144" class="Datatype"
      >Term</a
      ><a name="7875"
      > </a
      ><a name="7876" class="Symbol"
      >&#8594;</a
      ><a name="7877"
      > </a
      ><a name="7878" class="PrimitiveType"
      >Set</a
      ><a name="7881"
      >
</a
      ><a name="7882" href="StlcProp.html#7862" class="Function"
      >closed</a
      ><a name="7888"
      > </a
      ><a name="7889" href="StlcProp.html#7889" class="Bound"
      >M</a
      ><a name="7890"
      > </a
      ><a name="7891" class="Symbol"
      >=</a
      ><a name="7892"
      > </a
      ><a name="7893" class="Symbol"
      >&#8704;</a
      ><a name="7894"
      > </a
      ><a name="7895" class="Symbol"
      >{</a
      ><a name="7896" href="StlcProp.html#7896" class="Bound"
      >x</a
      ><a name="7897" class="Symbol"
      >}</a
      ><a name="7898"
      > </a
      ><a name="7899" class="Symbol"
      >&#8594;</a
      ><a name="7900"
      > </a
      ><a name="7901" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#414" class="Function Operator"
      >&#172;</a
      ><a name="7902"
      > </a
      ><a name="7903" class="Symbol"
      >(</a
      ><a name="7904" href="StlcProp.html#7896" class="Bound"
      >x</a
      ><a name="7905"
      > </a
      ><a name="7906" href="StlcProp.html#7297" class="Datatype Operator"
      >FreeIn</a
      ><a name="7912"
      > </a
      ><a name="7913" href="StlcProp.html#7889" class="Bound"
      >M</a
      ><a name="7914" class="Symbol"
      >)</a
      >
{% endraw %}</pre>

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

<pre class="Agda">{% raw %}
<a name="8621" href="StlcProp.html#8621" class="Function"
      >freeLemma</a
      ><a name="8630"
      > </a
      ><a name="8631" class="Symbol"
      >:</a
      ><a name="8632"
      > </a
      ><a name="8633" class="Symbol"
      >&#8704;</a
      ><a name="8634"
      > </a
      ><a name="8635" class="Symbol"
      >{</a
      ><a name="8636" href="StlcProp.html#8636" class="Bound"
      >x</a
      ><a name="8637"
      > </a
      ><a name="8638" href="StlcProp.html#8638" class="Bound"
      >M</a
      ><a name="8639"
      > </a
      ><a name="8640" href="StlcProp.html#8640" class="Bound"
      >A</a
      ><a name="8641"
      > </a
      ><a name="8642" href="StlcProp.html#8642" class="Bound"
      >&#915;</a
      ><a name="8643" class="Symbol"
      >}</a
      ><a name="8644"
      > </a
      ><a name="8645" class="Symbol"
      >&#8594;</a
      ><a name="8646"
      > </a
      ><a name="8647" href="StlcProp.html#8636" class="Bound"
      >x</a
      ><a name="8648"
      > </a
      ><a name="8649" href="StlcProp.html#7297" class="Datatype Operator"
      >FreeIn</a
      ><a name="8655"
      > </a
      ><a name="8656" href="StlcProp.html#8638" class="Bound"
      >M</a
      ><a name="8657"
      > </a
      ><a name="8658" class="Symbol"
      >&#8594;</a
      ><a name="8659"
      > </a
      ><a name="8660" href="StlcProp.html#8642" class="Bound"
      >&#915;</a
      ><a name="8661"
      > </a
      ><a name="8662" href="Stlc.html#4815" class="Datatype Operator"
      >&#8866;</a
      ><a name="8663"
      > </a
      ><a name="8664" href="StlcProp.html#8638" class="Bound"
      >M</a
      ><a name="8665"
      > </a
      ><a name="8666" href="Stlc.html#4815" class="Datatype Operator"
      >&#8712;</a
      ><a name="8667"
      > </a
      ><a name="8668" href="StlcProp.html#8640" class="Bound"
      >A</a
      ><a name="8669"
      > </a
      ><a name="8670" class="Symbol"
      >&#8594;</a
      ><a name="8671"
      > </a
      ><a name="8672" href="https://agda.github.io/agda-stdlib/Data.Product.html#823" class="Function"
      >&#8707;</a
      ><a name="8673"
      > </a
      ><a name="8674" class="Symbol"
      >&#955;</a
      ><a name="8675"
      > </a
      ><a name="8676" href="StlcProp.html#8676" class="Bound"
      >B</a
      ><a name="8677"
      > </a
      ><a name="8678" class="Symbol"
      >&#8594;</a
      ><a name="8679"
      > </a
      ><a name="8680" href="StlcProp.html#8642" class="Bound"
      >&#915;</a
      ><a name="8681"
      > </a
      ><a name="8682" href="StlcProp.html#8636" class="Bound"
      >x</a
      ><a name="8683"
      > </a
      ><a name="8684" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="8685"
      > </a
      ><a name="8686" href="https://agda.github.io/agda-stdlib/Data.Maybe.Base.html#373" class="InductiveConstructor"
      >just</a
      ><a name="8690"
      > </a
      ><a name="8691" href="StlcProp.html#8676" class="Bound"
      >B</a
      >
{% endraw %}</pre>

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

<pre class="Agda">{% raw %}
<a name="10157" href="StlcProp.html#8621" class="Function"
      >freeLemma</a
      ><a name="10166"
      > </a
      ><a name="10167" href="StlcProp.html#7332" class="InductiveConstructor"
      >free-var&#7488;</a
      ><a name="10176"
      > </a
      ><a name="10177" class="Symbol"
      >(</a
      ><a name="10178" href="Stlc.html#4859" class="InductiveConstructor"
      >Ax</a
      ><a name="10180"
      > </a
      ><a name="10181" href="StlcProp.html#10181" class="Bound"
      >&#915;x&#8801;justA</a
      ><a name="10189" class="Symbol"
      >)</a
      ><a name="10190"
      > </a
      ><a name="10191" class="Symbol"
      >=</a
      ><a name="10192"
      > </a
      ><a name="10193" class="Symbol"
      >(_</a
      ><a name="10195"
      > </a
      ><a name="10196" href="https://agda.github.io/agda-stdlib/Data.Product.html#509" class="InductiveConstructor Operator"
      >,</a
      ><a name="10197"
      > </a
      ><a name="10198" href="StlcProp.html#10181" class="Bound"
      >&#915;x&#8801;justA</a
      ><a name="10206" class="Symbol"
      >)</a
      ><a name="10207"
      >
</a
      ><a name="10208" href="StlcProp.html#8621" class="Function"
      >freeLemma</a
      ><a name="10217"
      > </a
      ><a name="10218" class="Symbol"
      >(</a
      ><a name="10219" href="StlcProp.html#7445" class="InductiveConstructor"
      >free-&#183;&#7488;&#8321;</a
      ><a name="10227"
      > </a
      ><a name="10228" href="StlcProp.html#10228" class="Bound"
      >x&#8712;L</a
      ><a name="10231" class="Symbol"
      >)</a
      ><a name="10232"
      > </a
      ><a name="10233" class="Symbol"
      >(</a
      ><a name="10234" href="Stlc.html#4999" class="InductiveConstructor"
      >&#8658;-E</a
      ><a name="10237"
      > </a
      ><a name="10238" href="StlcProp.html#10238" class="Bound"
      >&#8866;L</a
      ><a name="10240"
      > </a
      ><a name="10241" href="StlcProp.html#10241" class="Bound"
      >&#8866;M</a
      ><a name="10243" class="Symbol"
      >)</a
      ><a name="10244"
      > </a
      ><a name="10245" class="Symbol"
      >=</a
      ><a name="10246"
      > </a
      ><a name="10247" href="StlcProp.html#8621" class="Function"
      >freeLemma</a
      ><a name="10256"
      > </a
      ><a name="10257" href="StlcProp.html#10228" class="Bound"
      >x&#8712;L</a
      ><a name="10260"
      > </a
      ><a name="10261" href="StlcProp.html#10238" class="Bound"
      >&#8866;L</a
      ><a name="10263"
      >
</a
      ><a name="10264" href="StlcProp.html#8621" class="Function"
      >freeLemma</a
      ><a name="10273"
      > </a
      ><a name="10274" class="Symbol"
      >(</a
      ><a name="10275" href="StlcProp.html#7501" class="InductiveConstructor"
      >free-&#183;&#7488;&#8322;</a
      ><a name="10283"
      > </a
      ><a name="10284" href="StlcProp.html#10284" class="Bound"
      >x&#8712;M</a
      ><a name="10287" class="Symbol"
      >)</a
      ><a name="10288"
      > </a
      ><a name="10289" class="Symbol"
      >(</a
      ><a name="10290" href="Stlc.html#4999" class="InductiveConstructor"
      >&#8658;-E</a
      ><a name="10293"
      > </a
      ><a name="10294" href="StlcProp.html#10294" class="Bound"
      >&#8866;L</a
      ><a name="10296"
      > </a
      ><a name="10297" href="StlcProp.html#10297" class="Bound"
      >&#8866;M</a
      ><a name="10299" class="Symbol"
      >)</a
      ><a name="10300"
      > </a
      ><a name="10301" class="Symbol"
      >=</a
      ><a name="10302"
      > </a
      ><a name="10303" href="StlcProp.html#8621" class="Function"
      >freeLemma</a
      ><a name="10312"
      > </a
      ><a name="10313" href="StlcProp.html#10284" class="Bound"
      >x&#8712;M</a
      ><a name="10316"
      > </a
      ><a name="10317" href="StlcProp.html#10297" class="Bound"
      >&#8866;M</a
      ><a name="10319"
      >
</a
      ><a name="10320" href="StlcProp.html#8621" class="Function"
      >freeLemma</a
      ><a name="10329"
      > </a
      ><a name="10330" class="Symbol"
      >(</a
      ><a name="10331" href="StlcProp.html#7557" class="InductiveConstructor"
      >free-if&#7488;&#8321;</a
      ><a name="10340"
      > </a
      ><a name="10341" href="StlcProp.html#10341" class="Bound"
      >x&#8712;L</a
      ><a name="10344" class="Symbol"
      >)</a
      ><a name="10345"
      > </a
      ><a name="10346" class="Symbol"
      >(</a
      ><a name="10347" href="Stlc.html#5151" class="InductiveConstructor"
      >&#120121;-E</a
      ><a name="10350"
      > </a
      ><a name="10351" href="StlcProp.html#10351" class="Bound"
      >&#8866;L</a
      ><a name="10353"
      > </a
      ><a name="10354" href="StlcProp.html#10354" class="Bound"
      >&#8866;M</a
      ><a name="10356"
      > </a
      ><a name="10357" href="StlcProp.html#10357" class="Bound"
      >&#8866;N</a
      ><a name="10359" class="Symbol"
      >)</a
      ><a name="10360"
      > </a
      ><a name="10361" class="Symbol"
      >=</a
      ><a name="10362"
      > </a
      ><a name="10363" href="StlcProp.html#8621" class="Function"
      >freeLemma</a
      ><a name="10372"
      > </a
      ><a name="10373" href="StlcProp.html#10341" class="Bound"
      >x&#8712;L</a
      ><a name="10376"
      > </a
      ><a name="10377" href="StlcProp.html#10351" class="Bound"
      >&#8866;L</a
      ><a name="10379"
      >
</a
      ><a name="10380" href="StlcProp.html#8621" class="Function"
      >freeLemma</a
      ><a name="10389"
      > </a
      ><a name="10390" class="Symbol"
      >(</a
      ><a name="10391" href="StlcProp.html#7629" class="InductiveConstructor"
      >free-if&#7488;&#8322;</a
      ><a name="10400"
      > </a
      ><a name="10401" href="StlcProp.html#10401" class="Bound"
      >x&#8712;M</a
      ><a name="10404" class="Symbol"
      >)</a
      ><a name="10405"
      > </a
      ><a name="10406" class="Symbol"
      >(</a
      ><a name="10407" href="Stlc.html#5151" class="InductiveConstructor"
      >&#120121;-E</a
      ><a name="10410"
      > </a
      ><a name="10411" href="StlcProp.html#10411" class="Bound"
      >&#8866;L</a
      ><a name="10413"
      > </a
      ><a name="10414" href="StlcProp.html#10414" class="Bound"
      >&#8866;M</a
      ><a name="10416"
      > </a
      ><a name="10417" href="StlcProp.html#10417" class="Bound"
      >&#8866;N</a
      ><a name="10419" class="Symbol"
      >)</a
      ><a name="10420"
      > </a
      ><a name="10421" class="Symbol"
      >=</a
      ><a name="10422"
      > </a
      ><a name="10423" href="StlcProp.html#8621" class="Function"
      >freeLemma</a
      ><a name="10432"
      > </a
      ><a name="10433" href="StlcProp.html#10401" class="Bound"
      >x&#8712;M</a
      ><a name="10436"
      > </a
      ><a name="10437" href="StlcProp.html#10414" class="Bound"
      >&#8866;M</a
      ><a name="10439"
      >
</a
      ><a name="10440" href="StlcProp.html#8621" class="Function"
      >freeLemma</a
      ><a name="10449"
      > </a
      ><a name="10450" class="Symbol"
      >(</a
      ><a name="10451" href="StlcProp.html#7701" class="InductiveConstructor"
      >free-if&#7488;&#8323;</a
      ><a name="10460"
      > </a
      ><a name="10461" href="StlcProp.html#10461" class="Bound"
      >x&#8712;N</a
      ><a name="10464" class="Symbol"
      >)</a
      ><a name="10465"
      > </a
      ><a name="10466" class="Symbol"
      >(</a
      ><a name="10467" href="Stlc.html#5151" class="InductiveConstructor"
      >&#120121;-E</a
      ><a name="10470"
      > </a
      ><a name="10471" href="StlcProp.html#10471" class="Bound"
      >&#8866;L</a
      ><a name="10473"
      > </a
      ><a name="10474" href="StlcProp.html#10474" class="Bound"
      >&#8866;M</a
      ><a name="10476"
      > </a
      ><a name="10477" href="StlcProp.html#10477" class="Bound"
      >&#8866;N</a
      ><a name="10479" class="Symbol"
      >)</a
      ><a name="10480"
      > </a
      ><a name="10481" class="Symbol"
      >=</a
      ><a name="10482"
      > </a
      ><a name="10483" href="StlcProp.html#8621" class="Function"
      >freeLemma</a
      ><a name="10492"
      > </a
      ><a name="10493" href="StlcProp.html#10461" class="Bound"
      >x&#8712;N</a
      ><a name="10496"
      > </a
      ><a name="10497" href="StlcProp.html#10477" class="Bound"
      >&#8866;N</a
      ><a name="10499"
      >
</a
      ><a name="10500" href="StlcProp.html#8621" class="Function"
      >freeLemma</a
      ><a name="10509"
      > </a
      ><a name="10510" class="Symbol"
      >(</a
      ><a name="10511" href="StlcProp.html#7373" class="InductiveConstructor"
      >free-&#955;&#7488;</a
      ><a name="10518"
      > </a
      ><a name="10519" class="Symbol"
      >{</a
      ><a name="10520" href="StlcProp.html#10520" class="Bound"
      >x</a
      ><a name="10521" class="Symbol"
      >}</a
      ><a name="10522"
      > </a
      ><a name="10523" class="Symbol"
      >{</a
      ><a name="10524" href="StlcProp.html#10524" class="Bound"
      >y</a
      ><a name="10525" class="Symbol"
      >}</a
      ><a name="10526"
      > </a
      ><a name="10527" href="StlcProp.html#10527" class="Bound"
      >y&#8802;x</a
      ><a name="10530"
      > </a
      ><a name="10531" href="StlcProp.html#10531" class="Bound"
      >x&#8712;N</a
      ><a name="10534" class="Symbol"
      >)</a
      ><a name="10535"
      > </a
      ><a name="10536" class="Symbol"
      >(</a
      ><a name="10537" href="Stlc.html#4916" class="InductiveConstructor"
      >&#8658;-I</a
      ><a name="10540"
      > </a
      ><a name="10541" href="StlcProp.html#10541" class="Bound"
      >&#8866;N</a
      ><a name="10543" class="Symbol"
      >)</a
      ><a name="10544"
      > </a
      ><a name="10545" class="Keyword"
      >with</a
      ><a name="10549"
      > </a
      ><a name="10550" href="StlcProp.html#8621" class="Function"
      >freeLemma</a
      ><a name="10559"
      > </a
      ><a name="10560" href="StlcProp.html#10531" class="Bound"
      >x&#8712;N</a
      ><a name="10563"
      > </a
      ><a name="10564" href="StlcProp.html#10541" class="Bound"
      >&#8866;N</a
      ><a name="10566"
      >
</a
      ><a name="10567" class="Symbol"
      >...</a
      ><a name="10570"
      > </a
      ><a name="10571" class="Symbol"
      >|</a
      ><a name="10572"
      > </a
      ><a name="10573" href="StlcProp.html#10573" class="Bound"
      >&#915;x=justC</a
      ><a name="10581"
      > </a
      ><a name="10582" class="Keyword"
      >with</a
      ><a name="10586"
      > </a
      ><a name="10587" href="StlcProp.html#10524" class="Bound"
      >y</a
      ><a name="10588"
      > </a
      ><a name="10589" href="Maps.html#2558" class="Function Operator"
      >&#8799;</a
      ><a name="10590"
      > </a
      ><a name="10591" href="StlcProp.html#10520" class="Bound"
      >x</a
      ><a name="10592"
      >
</a
      ><a name="10593" class="Symbol"
      >...</a
      ><a name="10596"
      > </a
      ><a name="10597" class="Symbol"
      >|</a
      ><a name="10598"
      > </a
      ><a name="10599" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#520" class="InductiveConstructor"
      >yes</a
      ><a name="10602"
      > </a
      ><a name="10603" href="StlcProp.html#10603" class="Bound"
      >y&#8801;x</a
      ><a name="10606"
      > </a
      ><a name="10607" class="Symbol"
      >=</a
      ><a name="10608"
      > </a
      ><a name="10609" href="https://agda.github.io/agda-stdlib/Data.Empty.html#348" class="Function"
      >&#8869;-elim</a
      ><a name="10615"
      > </a
      ><a name="10616" class="Symbol"
      >(</a
      ><a name="10617" href="StlcProp.html#10527" class="Bound"
      >y&#8802;x</a
      ><a name="10620"
      > </a
      ><a name="10621" href="StlcProp.html#10603" class="Bound"
      >y&#8801;x</a
      ><a name="10624" class="Symbol"
      >)</a
      ><a name="10625"
      >
</a
      ><a name="10626" class="Symbol"
      >...</a
      ><a name="10629"
      > </a
      ><a name="10630" class="Symbol"
      >|</a
      ><a name="10631"
      > </a
      ><a name="10632" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#547" class="InductiveConstructor"
      >no</a
      ><a name="10634"
      >  </a
      ><a name="10636" class="Symbol"
      >_</a
      ><a name="10637"
      >   </a
      ><a name="10640" class="Symbol"
      >=</a
      ><a name="10641"
      > </a
      ><a name="10642" href="StlcProp.html#10573" class="Bound"
      >&#915;x=justC</a
      >
{% endraw %}</pre>

[A subtle point: if the first argument of `free-λᵀ` was of type
`x ≢ y` rather than of type `y ≢ x`, then the type of the
term `Γx=justC` would not simplify properly.]

Next, we'll need the fact that any term `M` which is well typed in
the empty context is closed (it has no free variables).

#### Exercise: 2 stars, optional (∅⊢-closed)

<pre class="Agda">{% raw %}
<a name="11015" class="Keyword"
      >postulate</a
      ><a name="11024"
      >
  </a
      ><a name="11027" href="StlcProp.html#11027" class="Postulate"
      >&#8709;&#8866;-closed</a
      ><a name="11036"
      > </a
      ><a name="11037" class="Symbol"
      >:</a
      ><a name="11038"
      > </a
      ><a name="11039" class="Symbol"
      >&#8704;</a
      ><a name="11040"
      > </a
      ><a name="11041" class="Symbol"
      >{</a
      ><a name="11042" href="StlcProp.html#11042" class="Bound"
      >M</a
      ><a name="11043"
      > </a
      ><a name="11044" href="StlcProp.html#11044" class="Bound"
      >A</a
      ><a name="11045" class="Symbol"
      >}</a
      ><a name="11046"
      > </a
      ><a name="11047" class="Symbol"
      >&#8594;</a
      ><a name="11048"
      > </a
      ><a name="11049" href="Maps.html#10360" class="Function"
      >&#8709;</a
      ><a name="11050"
      > </a
      ><a name="11051" href="Stlc.html#4815" class="Datatype Operator"
      >&#8866;</a
      ><a name="11052"
      > </a
      ><a name="11053" href="StlcProp.html#11042" class="Bound"
      >M</a
      ><a name="11054"
      > </a
      ><a name="11055" href="Stlc.html#4815" class="Datatype Operator"
      >&#8712;</a
      ><a name="11056"
      > </a
      ><a name="11057" href="StlcProp.html#11044" class="Bound"
      >A</a
      ><a name="11058"
      > </a
      ><a name="11059" class="Symbol"
      >&#8594;</a
      ><a name="11060"
      > </a
      ><a name="11061" href="StlcProp.html#7862" class="Function"
      >closed</a
      ><a name="11067"
      > </a
      ><a name="11068" href="StlcProp.html#11042" class="Bound"
      >M</a
      >
{% endraw %}</pre>

<div class="hidden">
<pre class="Agda">{% raw %}
<a name="11116" href="StlcProp.html#11116" class="Function"
      >contradiction</a
      ><a name="11129"
      > </a
      ><a name="11130" class="Symbol"
      >:</a
      ><a name="11131"
      > </a
      ><a name="11132" class="Symbol"
      >&#8704;</a
      ><a name="11133"
      > </a
      ><a name="11134" class="Symbol"
      >{</a
      ><a name="11135" href="StlcProp.html#11135" class="Bound"
      >X</a
      ><a name="11136"
      > </a
      ><a name="11137" class="Symbol"
      >:</a
      ><a name="11138"
      > </a
      ><a name="11139" class="PrimitiveType"
      >Set</a
      ><a name="11142" class="Symbol"
      >}</a
      ><a name="11143"
      > </a
      ><a name="11144" class="Symbol"
      >&#8594;</a
      ><a name="11145"
      > </a
      ><a name="11146" class="Symbol"
      >&#8704;</a
      ><a name="11147"
      > </a
      ><a name="11148" class="Symbol"
      >{</a
      ><a name="11149" href="StlcProp.html#11149" class="Bound"
      >x</a
      ><a name="11150"
      > </a
      ><a name="11151" class="Symbol"
      >:</a
      ><a name="11152"
      > </a
      ><a name="11153" href="StlcProp.html#11135" class="Bound"
      >X</a
      ><a name="11154" class="Symbol"
      >}</a
      ><a name="11155"
      > </a
      ><a name="11156" class="Symbol"
      >&#8594;</a
      ><a name="11157"
      > </a
      ><a name="11158" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#414" class="Function Operator"
      >&#172;</a
      ><a name="11159"
      > </a
      ><a name="11160" class="Symbol"
      >(</a
      ><a name="11161" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >_&#8801;_</a
      ><a name="11164"
      > </a
      ><a name="11165" class="Symbol"
      >{</a
      ><a name="11166" class="Argument"
      >A</a
      ><a name="11167"
      > </a
      ><a name="11168" class="Symbol"
      >=</a
      ><a name="11169"
      > </a
      ><a name="11170" href="https://agda.github.io/agda-stdlib/Data.Maybe.Base.html#335" class="Datatype"
      >Maybe</a
      ><a name="11175"
      > </a
      ><a name="11176" href="StlcProp.html#11135" class="Bound"
      >X</a
      ><a name="11177" class="Symbol"
      >}</a
      ><a name="11178"
      > </a
      ><a name="11179" class="Symbol"
      >(</a
      ><a name="11180" href="https://agda.github.io/agda-stdlib/Data.Maybe.Base.html#373" class="InductiveConstructor"
      >just</a
      ><a name="11184"
      > </a
      ><a name="11185" href="StlcProp.html#11149" class="Bound"
      >x</a
      ><a name="11186" class="Symbol"
      >)</a
      ><a name="11187"
      > </a
      ><a name="11188" href="https://agda.github.io/agda-stdlib/Data.Maybe.Base.html#403" class="InductiveConstructor"
      >nothing</a
      ><a name="11195" class="Symbol"
      >)</a
      ><a name="11196"
      >
</a
      ><a name="11197" href="StlcProp.html#11116" class="Function"
      >contradiction</a
      ><a name="11210"
      > </a
      ><a name="11211" class="Symbol"
      >()</a
      ><a name="11213"
      >

</a
      ><a name="11215" href="StlcProp.html#11215" class="Function"
      >&#8709;&#8866;-closed&#8242;</a
      ><a name="11225"
      > </a
      ><a name="11226" class="Symbol"
      >:</a
      ><a name="11227"
      > </a
      ><a name="11228" class="Symbol"
      >&#8704;</a
      ><a name="11229"
      > </a
      ><a name="11230" class="Symbol"
      >{</a
      ><a name="11231" href="StlcProp.html#11231" class="Bound"
      >M</a
      ><a name="11232"
      > </a
      ><a name="11233" href="StlcProp.html#11233" class="Bound"
      >A</a
      ><a name="11234" class="Symbol"
      >}</a
      ><a name="11235"
      > </a
      ><a name="11236" class="Symbol"
      >&#8594;</a
      ><a name="11237"
      > </a
      ><a name="11238" href="Maps.html#10360" class="Function"
      >&#8709;</a
      ><a name="11239"
      > </a
      ><a name="11240" href="Stlc.html#4815" class="Datatype Operator"
      >&#8866;</a
      ><a name="11241"
      > </a
      ><a name="11242" href="StlcProp.html#11231" class="Bound"
      >M</a
      ><a name="11243"
      > </a
      ><a name="11244" href="Stlc.html#4815" class="Datatype Operator"
      >&#8712;</a
      ><a name="11245"
      > </a
      ><a name="11246" href="StlcProp.html#11233" class="Bound"
      >A</a
      ><a name="11247"
      > </a
      ><a name="11248" class="Symbol"
      >&#8594;</a
      ><a name="11249"
      > </a
      ><a name="11250" href="StlcProp.html#7862" class="Function"
      >closed</a
      ><a name="11256"
      > </a
      ><a name="11257" href="StlcProp.html#11231" class="Bound"
      >M</a
      ><a name="11258"
      >
</a
      ><a name="11259" href="StlcProp.html#11215" class="Function"
      >&#8709;&#8866;-closed&#8242;</a
      ><a name="11269"
      > </a
      ><a name="11270" class="Symbol"
      >{</a
      ><a name="11271" href="StlcProp.html#11271" class="Bound"
      >M</a
      ><a name="11272" class="Symbol"
      >}</a
      ><a name="11273"
      > </a
      ><a name="11274" class="Symbol"
      >{</a
      ><a name="11275" href="StlcProp.html#11275" class="Bound"
      >A</a
      ><a name="11276" class="Symbol"
      >}</a
      ><a name="11277"
      > </a
      ><a name="11278" href="StlcProp.html#11278" class="Bound"
      >&#8866;M</a
      ><a name="11280"
      > </a
      ><a name="11281" class="Symbol"
      >{</a
      ><a name="11282" href="StlcProp.html#11282" class="Bound"
      >x</a
      ><a name="11283" class="Symbol"
      >}</a
      ><a name="11284"
      > </a
      ><a name="11285" href="StlcProp.html#11285" class="Bound"
      >x&#8712;M</a
      ><a name="11288"
      > </a
      ><a name="11289" class="Keyword"
      >with</a
      ><a name="11293"
      > </a
      ><a name="11294" href="StlcProp.html#8621" class="Function"
      >freeLemma</a
      ><a name="11303"
      > </a
      ><a name="11304" href="StlcProp.html#11285" class="Bound"
      >x&#8712;M</a
      ><a name="11307"
      > </a
      ><a name="11308" href="StlcProp.html#11278" class="Bound"
      >&#8866;M</a
      ><a name="11310"
      >
</a
      ><a name="11311" class="Symbol"
      >...</a
      ><a name="11314"
      > </a
      ><a name="11315" class="Symbol"
      >|</a
      ><a name="11316"
      > </a
      ><a name="11317" class="Symbol"
      >(</a
      ><a name="11318" href="StlcProp.html#11318" class="Bound"
      >B</a
      ><a name="11319"
      > </a
      ><a name="11320" href="https://agda.github.io/agda-stdlib/Data.Product.html#509" class="InductiveConstructor Operator"
      >,</a
      ><a name="11321"
      > </a
      ><a name="11322" href="StlcProp.html#11322" class="Bound"
      >&#8709;x&#8801;justB</a
      ><a name="11330" class="Symbol"
      >)</a
      ><a name="11331"
      > </a
      ><a name="11332" class="Symbol"
      >=</a
      ><a name="11333"
      > </a
      ><a name="11334" href="StlcProp.html#11116" class="Function"
      >contradiction</a
      ><a name="11347"
      > </a
      ><a name="11348" class="Symbol"
      >(</a
      ><a name="11349" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.Core.html#632" class="Function"
      >trans</a
      ><a name="11354"
      > </a
      ><a name="11355" class="Symbol"
      >(</a
      ><a name="11356" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.Core.html#565" class="Function"
      >sym</a
      ><a name="11359"
      > </a
      ><a name="11360" href="StlcProp.html#11322" class="Bound"
      >&#8709;x&#8801;justB</a
      ><a name="11368" class="Symbol"
      >)</a
      ><a name="11369"
      > </a
      ><a name="11370" class="Symbol"
      >(</a
      ><a name="11371" href="Maps.html#10669" class="Function"
      >apply-&#8709;</a
      ><a name="11378"
      > </a
      ><a name="11379" href="StlcProp.html#11282" class="Bound"
      >x</a
      ><a name="11380" class="Symbol"
      >))</a
      >
{% endraw %}</pre>
</div>

Sometimes, when we have a proof `Γ ⊢ M ∈ A`, we will need to
replace `Γ` by a different context `Γ′`.  When is it safe
to do this?  Intuitively, it must at least be the case that
`Γ′` assigns the same types as `Γ` to all the variables
that appear free in `M`. In fact, this is the only condition that
is needed.

<pre class="Agda">{% raw %}
<a name="11728" href="StlcProp.html#11728" class="Function"
      >weaken</a
      ><a name="11734"
      > </a
      ><a name="11735" class="Symbol"
      >:</a
      ><a name="11736"
      > </a
      ><a name="11737" class="Symbol"
      >&#8704;</a
      ><a name="11738"
      > </a
      ><a name="11739" class="Symbol"
      >{</a
      ><a name="11740" href="StlcProp.html#11740" class="Bound"
      >&#915;</a
      ><a name="11741"
      > </a
      ><a name="11742" href="StlcProp.html#11742" class="Bound"
      >&#915;&#8242;</a
      ><a name="11744"
      > </a
      ><a name="11745" href="StlcProp.html#11745" class="Bound"
      >M</a
      ><a name="11746"
      > </a
      ><a name="11747" href="StlcProp.html#11747" class="Bound"
      >A</a
      ><a name="11748" class="Symbol"
      >}</a
      ><a name="11749"
      >
        </a
      ><a name="11758" class="Symbol"
      >&#8594;</a
      ><a name="11759"
      > </a
      ><a name="11760" class="Symbol"
      >(&#8704;</a
      ><a name="11762"
      > </a
      ><a name="11763" class="Symbol"
      >{</a
      ><a name="11764" href="StlcProp.html#11764" class="Bound"
      >x</a
      ><a name="11765" class="Symbol"
      >}</a
      ><a name="11766"
      > </a
      ><a name="11767" class="Symbol"
      >&#8594;</a
      ><a name="11768"
      > </a
      ><a name="11769" href="StlcProp.html#11764" class="Bound"
      >x</a
      ><a name="11770"
      > </a
      ><a name="11771" href="StlcProp.html#7297" class="Datatype Operator"
      >FreeIn</a
      ><a name="11777"
      > </a
      ><a name="11778" href="StlcProp.html#11745" class="Bound"
      >M</a
      ><a name="11779"
      > </a
      ><a name="11780" class="Symbol"
      >&#8594;</a
      ><a name="11781"
      > </a
      ><a name="11782" href="StlcProp.html#11740" class="Bound"
      >&#915;</a
      ><a name="11783"
      > </a
      ><a name="11784" href="StlcProp.html#11764" class="Bound"
      >x</a
      ><a name="11785"
      > </a
      ><a name="11786" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="11787"
      > </a
      ><a name="11788" href="StlcProp.html#11742" class="Bound"
      >&#915;&#8242;</a
      ><a name="11790"
      > </a
      ><a name="11791" href="StlcProp.html#11764" class="Bound"
      >x</a
      ><a name="11792" class="Symbol"
      >)</a
      ><a name="11793"
      >
        </a
      ><a name="11802" class="Symbol"
      >&#8594;</a
      ><a name="11803"
      > </a
      ><a name="11804" href="StlcProp.html#11740" class="Bound"
      >&#915;</a
      ><a name="11805"
      >  </a
      ><a name="11807" href="Stlc.html#4815" class="Datatype Operator"
      >&#8866;</a
      ><a name="11808"
      > </a
      ><a name="11809" href="StlcProp.html#11745" class="Bound"
      >M</a
      ><a name="11810"
      > </a
      ><a name="11811" href="Stlc.html#4815" class="Datatype Operator"
      >&#8712;</a
      ><a name="11812"
      > </a
      ><a name="11813" href="StlcProp.html#11747" class="Bound"
      >A</a
      ><a name="11814"
      >
        </a
      ><a name="11823" class="Symbol"
      >&#8594;</a
      ><a name="11824"
      > </a
      ><a name="11825" href="StlcProp.html#11742" class="Bound"
      >&#915;&#8242;</a
      ><a name="11827"
      > </a
      ><a name="11828" href="Stlc.html#4815" class="Datatype Operator"
      >&#8866;</a
      ><a name="11829"
      > </a
      ><a name="11830" href="StlcProp.html#11745" class="Bound"
      >M</a
      ><a name="11831"
      > </a
      ><a name="11832" href="Stlc.html#4815" class="Datatype Operator"
      >&#8712;</a
      ><a name="11833"
      > </a
      ><a name="11834" href="StlcProp.html#11747" class="Bound"
      >A</a
      >
{% endraw %}</pre>

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

<pre class="Agda">{% raw %}
<a name="14001" href="StlcProp.html#11728" class="Function"
      >weaken</a
      ><a name="14007"
      > </a
      ><a name="14008" href="StlcProp.html#14008" class="Bound"
      >&#915;~&#915;&#8242;</a
      ><a name="14012"
      > </a
      ><a name="14013" class="Symbol"
      >(</a
      ><a name="14014" href="Stlc.html#4859" class="InductiveConstructor"
      >Ax</a
      ><a name="14016"
      > </a
      ><a name="14017" href="StlcProp.html#14017" class="Bound"
      >&#915;x&#8801;justA</a
      ><a name="14025" class="Symbol"
      >)</a
      ><a name="14026"
      > </a
      ><a name="14027" class="Keyword"
      >rewrite</a
      ><a name="14034"
      > </a
      ><a name="14035" class="Symbol"
      >(</a
      ><a name="14036" href="StlcProp.html#14008" class="Bound"
      >&#915;~&#915;&#8242;</a
      ><a name="14040"
      > </a
      ><a name="14041" href="StlcProp.html#7332" class="InductiveConstructor"
      >free-var&#7488;</a
      ><a name="14050" class="Symbol"
      >)</a
      ><a name="14051"
      > </a
      ><a name="14052" class="Symbol"
      >=</a
      ><a name="14053"
      > </a
      ><a name="14054" href="Stlc.html#4859" class="InductiveConstructor"
      >Ax</a
      ><a name="14056"
      > </a
      ><a name="14057" href="StlcProp.html#14017" class="Bound"
      >&#915;x&#8801;justA</a
      ><a name="14065"
      >
</a
      ><a name="14066" href="StlcProp.html#11728" class="Function"
      >weaken</a
      ><a name="14072"
      > </a
      ><a name="14073" class="Symbol"
      >{</a
      ><a name="14074" href="StlcProp.html#14074" class="Bound"
      >&#915;</a
      ><a name="14075" class="Symbol"
      >}</a
      ><a name="14076"
      > </a
      ><a name="14077" class="Symbol"
      >{</a
      ><a name="14078" href="StlcProp.html#14078" class="Bound"
      >&#915;&#8242;</a
      ><a name="14080" class="Symbol"
      >}</a
      ><a name="14081"
      > </a
      ><a name="14082" class="Symbol"
      >{</a
      ><a name="14083" href="Stlc.html#1182" class="InductiveConstructor Operator"
      >&#955;&#7488;</a
      ><a name="14085"
      > </a
      ><a name="14086" href="StlcProp.html#14086" class="Bound"
      >x</a
      ><a name="14087"
      > </a
      ><a name="14088" href="Stlc.html#1182" class="InductiveConstructor Operator"
      >&#8712;</a
      ><a name="14089"
      > </a
      ><a name="14090" href="StlcProp.html#14090" class="Bound"
      >A</a
      ><a name="14091"
      > </a
      ><a name="14092" href="Stlc.html#1182" class="InductiveConstructor Operator"
      >&#8658;</a
      ><a name="14093"
      > </a
      ><a name="14094" href="StlcProp.html#14094" class="Bound"
      >N</a
      ><a name="14095" class="Symbol"
      >}</a
      ><a name="14096"
      > </a
      ><a name="14097" href="StlcProp.html#14097" class="Bound"
      >&#915;~&#915;&#8242;</a
      ><a name="14101"
      > </a
      ><a name="14102" class="Symbol"
      >(</a
      ><a name="14103" href="Stlc.html#4916" class="InductiveConstructor"
      >&#8658;-I</a
      ><a name="14106"
      > </a
      ><a name="14107" href="StlcProp.html#14107" class="Bound"
      >&#8866;N</a
      ><a name="14109" class="Symbol"
      >)</a
      ><a name="14110"
      > </a
      ><a name="14111" class="Symbol"
      >=</a
      ><a name="14112"
      > </a
      ><a name="14113" href="Stlc.html#4916" class="InductiveConstructor"
      >&#8658;-I</a
      ><a name="14116"
      > </a
      ><a name="14117" class="Symbol"
      >(</a
      ><a name="14118" href="StlcProp.html#11728" class="Function"
      >weaken</a
      ><a name="14124"
      > </a
      ><a name="14125" href="StlcProp.html#14146" class="Function"
      >&#915;x~&#915;&#8242;x</a
      ><a name="14131"
      > </a
      ><a name="14132" href="StlcProp.html#14107" class="Bound"
      >&#8866;N</a
      ><a name="14134" class="Symbol"
      >)</a
      ><a name="14135"
      >
  </a
      ><a name="14138" class="Keyword"
      >where</a
      ><a name="14143"
      >
  </a
      ><a name="14146" href="StlcProp.html#14146" class="Function"
      >&#915;x~&#915;&#8242;x</a
      ><a name="14152"
      > </a
      ><a name="14153" class="Symbol"
      >:</a
      ><a name="14154"
      > </a
      ><a name="14155" class="Symbol"
      >&#8704;</a
      ><a name="14156"
      > </a
      ><a name="14157" class="Symbol"
      >{</a
      ><a name="14158" href="StlcProp.html#14158" class="Bound"
      >y</a
      ><a name="14159" class="Symbol"
      >}</a
      ><a name="14160"
      > </a
      ><a name="14161" class="Symbol"
      >&#8594;</a
      ><a name="14162"
      > </a
      ><a name="14163" href="StlcProp.html#14158" class="Bound"
      >y</a
      ><a name="14164"
      > </a
      ><a name="14165" href="StlcProp.html#7297" class="Datatype Operator"
      >FreeIn</a
      ><a name="14171"
      > </a
      ><a name="14172" href="StlcProp.html#14094" class="Bound"
      >N</a
      ><a name="14173"
      > </a
      ><a name="14174" class="Symbol"
      >&#8594;</a
      ><a name="14175"
      > </a
      ><a name="14176" class="Symbol"
      >(</a
      ><a name="14177" href="StlcProp.html#14074" class="Bound"
      >&#915;</a
      ><a name="14178"
      > </a
      ><a name="14179" href="Maps.html#10464" class="Function Operator"
      >,</a
      ><a name="14180"
      > </a
      ><a name="14181" href="StlcProp.html#14086" class="Bound"
      >x</a
      ><a name="14182"
      > </a
      ><a name="14183" href="Maps.html#10464" class="Function Operator"
      >&#8614;</a
      ><a name="14184"
      > </a
      ><a name="14185" href="StlcProp.html#14090" class="Bound"
      >A</a
      ><a name="14186" class="Symbol"
      >)</a
      ><a name="14187"
      > </a
      ><a name="14188" href="StlcProp.html#14158" class="Bound"
      >y</a
      ><a name="14189"
      > </a
      ><a name="14190" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="14191"
      > </a
      ><a name="14192" class="Symbol"
      >(</a
      ><a name="14193" href="StlcProp.html#14078" class="Bound"
      >&#915;&#8242;</a
      ><a name="14195"
      > </a
      ><a name="14196" href="Maps.html#10464" class="Function Operator"
      >,</a
      ><a name="14197"
      > </a
      ><a name="14198" href="StlcProp.html#14086" class="Bound"
      >x</a
      ><a name="14199"
      > </a
      ><a name="14200" href="Maps.html#10464" class="Function Operator"
      >&#8614;</a
      ><a name="14201"
      > </a
      ><a name="14202" href="StlcProp.html#14090" class="Bound"
      >A</a
      ><a name="14203" class="Symbol"
      >)</a
      ><a name="14204"
      > </a
      ><a name="14205" href="StlcProp.html#14158" class="Bound"
      >y</a
      ><a name="14206"
      >
  </a
      ><a name="14209" href="StlcProp.html#14146" class="Function"
      >&#915;x~&#915;&#8242;x</a
      ><a name="14215"
      > </a
      ><a name="14216" class="Symbol"
      >{</a
      ><a name="14217" href="StlcProp.html#14217" class="Bound"
      >y</a
      ><a name="14218" class="Symbol"
      >}</a
      ><a name="14219"
      > </a
      ><a name="14220" href="StlcProp.html#14220" class="Bound"
      >y&#8712;N</a
      ><a name="14223"
      > </a
      ><a name="14224" class="Keyword"
      >with</a
      ><a name="14228"
      > </a
      ><a name="14229" href="StlcProp.html#14086" class="Bound"
      >x</a
      ><a name="14230"
      > </a
      ><a name="14231" href="Maps.html#2558" class="Function Operator"
      >&#8799;</a
      ><a name="14232"
      > </a
      ><a name="14233" href="StlcProp.html#14217" class="Bound"
      >y</a
      ><a name="14234"
      >
  </a
      ><a name="14237" class="Symbol"
      >...</a
      ><a name="14240"
      > </a
      ><a name="14241" class="Symbol"
      >|</a
      ><a name="14242"
      > </a
      ><a name="14243" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#520" class="InductiveConstructor"
      >yes</a
      ><a name="14246"
      > </a
      ><a name="14247" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="14251"
      > </a
      ><a name="14252" class="Symbol"
      >=</a
      ><a name="14253"
      > </a
      ><a name="14254" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="14258"
      >
  </a
      ><a name="14261" class="Symbol"
      >...</a
      ><a name="14264"
      > </a
      ><a name="14265" class="Symbol"
      >|</a
      ><a name="14266"
      > </a
      ><a name="14267" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#547" class="InductiveConstructor"
      >no</a
      ><a name="14269"
      >  </a
      ><a name="14271" href="StlcProp.html#14271" class="Bound"
      >x&#8802;y</a
      ><a name="14274"
      >  </a
      ><a name="14276" class="Symbol"
      >=</a
      ><a name="14277"
      > </a
      ><a name="14278" href="StlcProp.html#14097" class="Bound"
      >&#915;~&#915;&#8242;</a
      ><a name="14282"
      > </a
      ><a name="14283" class="Symbol"
      >(</a
      ><a name="14284" href="StlcProp.html#7373" class="InductiveConstructor"
      >free-&#955;&#7488;</a
      ><a name="14291"
      > </a
      ><a name="14292" href="StlcProp.html#14271" class="Bound"
      >x&#8802;y</a
      ><a name="14295"
      > </a
      ><a name="14296" href="StlcProp.html#14220" class="Bound"
      >y&#8712;N</a
      ><a name="14299" class="Symbol"
      >)</a
      ><a name="14300"
      >
</a
      ><a name="14301" href="StlcProp.html#11728" class="Function"
      >weaken</a
      ><a name="14307"
      > </a
      ><a name="14308" href="StlcProp.html#14308" class="Bound"
      >&#915;~&#915;&#8242;</a
      ><a name="14312"
      > </a
      ><a name="14313" class="Symbol"
      >(</a
      ><a name="14314" href="Stlc.html#4999" class="InductiveConstructor"
      >&#8658;-E</a
      ><a name="14317"
      > </a
      ><a name="14318" href="StlcProp.html#14318" class="Bound"
      >&#8866;L</a
      ><a name="14320"
      > </a
      ><a name="14321" href="StlcProp.html#14321" class="Bound"
      >&#8866;M</a
      ><a name="14323" class="Symbol"
      >)</a
      ><a name="14324"
      > </a
      ><a name="14325" class="Symbol"
      >=</a
      ><a name="14326"
      > </a
      ><a name="14327" href="Stlc.html#4999" class="InductiveConstructor"
      >&#8658;-E</a
      ><a name="14330"
      > </a
      ><a name="14331" class="Symbol"
      >(</a
      ><a name="14332" href="StlcProp.html#11728" class="Function"
      >weaken</a
      ><a name="14338"
      > </a
      ><a name="14339" class="Symbol"
      >(</a
      ><a name="14340" href="StlcProp.html#14308" class="Bound"
      >&#915;~&#915;&#8242;</a
      ><a name="14344"
      > </a
      ><a name="14345" href="https://agda.github.io/agda-stdlib/Function.html#713" class="Function Operator"
      >&#8728;</a
      ><a name="14346"
      > </a
      ><a name="14347" href="StlcProp.html#7445" class="InductiveConstructor"
      >free-&#183;&#7488;&#8321;</a
      ><a name="14355" class="Symbol"
      >)</a
      ><a name="14356"
      >  </a
      ><a name="14358" href="StlcProp.html#14318" class="Bound"
      >&#8866;L</a
      ><a name="14360" class="Symbol"
      >)</a
      ><a name="14361"
      > </a
      ><a name="14362" class="Symbol"
      >(</a
      ><a name="14363" href="StlcProp.html#11728" class="Function"
      >weaken</a
      ><a name="14369"
      > </a
      ><a name="14370" class="Symbol"
      >(</a
      ><a name="14371" href="StlcProp.html#14308" class="Bound"
      >&#915;~&#915;&#8242;</a
      ><a name="14375"
      > </a
      ><a name="14376" href="https://agda.github.io/agda-stdlib/Function.html#713" class="Function Operator"
      >&#8728;</a
      ><a name="14377"
      > </a
      ><a name="14378" href="StlcProp.html#7501" class="InductiveConstructor"
      >free-&#183;&#7488;&#8322;</a
      ><a name="14386" class="Symbol"
      >)</a
      ><a name="14387"
      > </a
      ><a name="14388" href="StlcProp.html#14321" class="Bound"
      >&#8866;M</a
      ><a name="14390" class="Symbol"
      >)</a
      ><a name="14391"
      > 
</a
      ><a name="14393" href="StlcProp.html#11728" class="Function"
      >weaken</a
      ><a name="14399"
      > </a
      ><a name="14400" href="StlcProp.html#14400" class="Bound"
      >&#915;~&#915;&#8242;</a
      ><a name="14404"
      > </a
      ><a name="14405" href="Stlc.html#5080" class="InductiveConstructor"
      >&#120121;-I&#8321;</a
      ><a name="14409"
      > </a
      ><a name="14410" class="Symbol"
      >=</a
      ><a name="14411"
      > </a
      ><a name="14412" href="Stlc.html#5080" class="InductiveConstructor"
      >&#120121;-I&#8321;</a
      ><a name="14416"
      >
</a
      ><a name="14417" href="StlcProp.html#11728" class="Function"
      >weaken</a
      ><a name="14423"
      > </a
      ><a name="14424" href="StlcProp.html#14424" class="Bound"
      >&#915;~&#915;&#8242;</a
      ><a name="14428"
      > </a
      ><a name="14429" href="Stlc.html#5115" class="InductiveConstructor"
      >&#120121;-I&#8322;</a
      ><a name="14433"
      > </a
      ><a name="14434" class="Symbol"
      >=</a
      ><a name="14435"
      > </a
      ><a name="14436" href="Stlc.html#5115" class="InductiveConstructor"
      >&#120121;-I&#8322;</a
      ><a name="14440"
      >
</a
      ><a name="14441" href="StlcProp.html#11728" class="Function"
      >weaken</a
      ><a name="14447"
      > </a
      ><a name="14448" href="StlcProp.html#14448" class="Bound"
      >&#915;~&#915;&#8242;</a
      ><a name="14452"
      > </a
      ><a name="14453" class="Symbol"
      >(</a
      ><a name="14454" href="Stlc.html#5151" class="InductiveConstructor"
      >&#120121;-E</a
      ><a name="14457"
      > </a
      ><a name="14458" href="StlcProp.html#14458" class="Bound"
      >&#8866;L</a
      ><a name="14460"
      > </a
      ><a name="14461" href="StlcProp.html#14461" class="Bound"
      >&#8866;M</a
      ><a name="14463"
      > </a
      ><a name="14464" href="StlcProp.html#14464" class="Bound"
      >&#8866;N</a
      ><a name="14466" class="Symbol"
      >)</a
      ><a name="14467"
      >
  </a
      ><a name="14470" class="Symbol"
      >=</a
      ><a name="14471"
      > </a
      ><a name="14472" href="Stlc.html#5151" class="InductiveConstructor"
      >&#120121;-E</a
      ><a name="14475"
      > </a
      ><a name="14476" class="Symbol"
      >(</a
      ><a name="14477" href="StlcProp.html#11728" class="Function"
      >weaken</a
      ><a name="14483"
      > </a
      ><a name="14484" class="Symbol"
      >(</a
      ><a name="14485" href="StlcProp.html#14448" class="Bound"
      >&#915;~&#915;&#8242;</a
      ><a name="14489"
      > </a
      ><a name="14490" href="https://agda.github.io/agda-stdlib/Function.html#713" class="Function Operator"
      >&#8728;</a
      ><a name="14491"
      > </a
      ><a name="14492" href="StlcProp.html#7557" class="InductiveConstructor"
      >free-if&#7488;&#8321;</a
      ><a name="14501" class="Symbol"
      >)</a
      ><a name="14502"
      > </a
      ><a name="14503" href="StlcProp.html#14458" class="Bound"
      >&#8866;L</a
      ><a name="14505" class="Symbol"
      >)</a
      ><a name="14506"
      > </a
      ><a name="14507" class="Symbol"
      >(</a
      ><a name="14508" href="StlcProp.html#11728" class="Function"
      >weaken</a
      ><a name="14514"
      > </a
      ><a name="14515" class="Symbol"
      >(</a
      ><a name="14516" href="StlcProp.html#14448" class="Bound"
      >&#915;~&#915;&#8242;</a
      ><a name="14520"
      > </a
      ><a name="14521" href="https://agda.github.io/agda-stdlib/Function.html#713" class="Function Operator"
      >&#8728;</a
      ><a name="14522"
      > </a
      ><a name="14523" href="StlcProp.html#7629" class="InductiveConstructor"
      >free-if&#7488;&#8322;</a
      ><a name="14532" class="Symbol"
      >)</a
      ><a name="14533"
      > </a
      ><a name="14534" href="StlcProp.html#14461" class="Bound"
      >&#8866;M</a
      ><a name="14536" class="Symbol"
      >)</a
      ><a name="14537"
      > </a
      ><a name="14538" class="Symbol"
      >(</a
      ><a name="14539" href="StlcProp.html#11728" class="Function"
      >weaken</a
      ><a name="14545"
      > </a
      ><a name="14546" class="Symbol"
      >(</a
      ><a name="14547" href="StlcProp.html#14448" class="Bound"
      >&#915;~&#915;&#8242;</a
      ><a name="14551"
      > </a
      ><a name="14552" href="https://agda.github.io/agda-stdlib/Function.html#713" class="Function Operator"
      >&#8728;</a
      ><a name="14553"
      > </a
      ><a name="14554" href="StlcProp.html#7701" class="InductiveConstructor"
      >free-if&#7488;&#8323;</a
      ><a name="14563" class="Symbol"
      >)</a
      ><a name="14564"
      > </a
      ><a name="14565" href="StlcProp.html#14464" class="Bound"
      >&#8866;N</a
      ><a name="14567" class="Symbol"
      >)</a
      ><a name="14568"
      >

</a
      ><a name="14570" class="Comment"
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

_Lemma_: If `Γ , x ↦ A ⊢ N ∈ B` and `∅ ⊢ V ∈ A`, then
`Γ ⊢ (N [ x := V ]) ∈ B`.

<pre class="Agda">{% raw %}
<a name="15949" href="StlcProp.html#15949" class="Function"
      >preservation-[:=]</a
      ><a name="15966"
      > </a
      ><a name="15967" class="Symbol"
      >:</a
      ><a name="15968"
      > </a
      ><a name="15969" class="Symbol"
      >&#8704;</a
      ><a name="15970"
      > </a
      ><a name="15971" class="Symbol"
      >{</a
      ><a name="15972" href="StlcProp.html#15972" class="Bound"
      >&#915;</a
      ><a name="15973"
      > </a
      ><a name="15974" href="StlcProp.html#15974" class="Bound"
      >x</a
      ><a name="15975"
      > </a
      ><a name="15976" href="StlcProp.html#15976" class="Bound"
      >A</a
      ><a name="15977"
      > </a
      ><a name="15978" href="StlcProp.html#15978" class="Bound"
      >N</a
      ><a name="15979"
      > </a
      ><a name="15980" href="StlcProp.html#15980" class="Bound"
      >B</a
      ><a name="15981"
      > </a
      ><a name="15982" href="StlcProp.html#15982" class="Bound"
      >V</a
      ><a name="15983" class="Symbol"
      >}</a
      ><a name="15984"
      >
                 </a
      ><a name="16002" class="Symbol"
      >&#8594;</a
      ><a name="16003"
      > </a
      ><a name="16004" class="Symbol"
      >(</a
      ><a name="16005" href="StlcProp.html#15972" class="Bound"
      >&#915;</a
      ><a name="16006"
      > </a
      ><a name="16007" href="Maps.html#10464" class="Function Operator"
      >,</a
      ><a name="16008"
      > </a
      ><a name="16009" href="StlcProp.html#15974" class="Bound"
      >x</a
      ><a name="16010"
      > </a
      ><a name="16011" href="Maps.html#10464" class="Function Operator"
      >&#8614;</a
      ><a name="16012"
      > </a
      ><a name="16013" href="StlcProp.html#15976" class="Bound"
      >A</a
      ><a name="16014" class="Symbol"
      >)</a
      ><a name="16015"
      > </a
      ><a name="16016" href="Stlc.html#4815" class="Datatype Operator"
      >&#8866;</a
      ><a name="16017"
      > </a
      ><a name="16018" href="StlcProp.html#15978" class="Bound"
      >N</a
      ><a name="16019"
      > </a
      ><a name="16020" href="Stlc.html#4815" class="Datatype Operator"
      >&#8712;</a
      ><a name="16021"
      > </a
      ><a name="16022" href="StlcProp.html#15980" class="Bound"
      >B</a
      ><a name="16023"
      >
                 </a
      ><a name="16041" class="Symbol"
      >&#8594;</a
      ><a name="16042"
      > </a
      ><a name="16043" href="Maps.html#10360" class="Function"
      >&#8709;</a
      ><a name="16044"
      > </a
      ><a name="16045" href="Stlc.html#4815" class="Datatype Operator"
      >&#8866;</a
      ><a name="16046"
      > </a
      ><a name="16047" href="StlcProp.html#15982" class="Bound"
      >V</a
      ><a name="16048"
      > </a
      ><a name="16049" href="Stlc.html#4815" class="Datatype Operator"
      >&#8712;</a
      ><a name="16050"
      > </a
      ><a name="16051" href="StlcProp.html#15976" class="Bound"
      >A</a
      ><a name="16052"
      >
                 </a
      ><a name="16070" class="Symbol"
      >&#8594;</a
      ><a name="16071"
      > </a
      ><a name="16072" href="StlcProp.html#15972" class="Bound"
      >&#915;</a
      ><a name="16073"
      > </a
      ><a name="16074" href="Stlc.html#4815" class="Datatype Operator"
      >&#8866;</a
      ><a name="16075"
      > </a
      ><a name="16076" class="Symbol"
      >(</a
      ><a name="16077" href="StlcProp.html#15978" class="Bound"
      >N</a
      ><a name="16078"
      > </a
      ><a name="16079" href="Stlc.html#1868" class="Function Operator"
      >[</a
      ><a name="16080"
      > </a
      ><a name="16081" href="StlcProp.html#15974" class="Bound"
      >x</a
      ><a name="16082"
      > </a
      ><a name="16083" href="Stlc.html#1868" class="Function Operator"
      >:=</a
      ><a name="16085"
      > </a
      ><a name="16086" href="StlcProp.html#15982" class="Bound"
      >V</a
      ><a name="16087"
      > </a
      ><a name="16088" href="Stlc.html#1868" class="Function Operator"
      >]</a
      ><a name="16089" class="Symbol"
      >)</a
      ><a name="16090"
      > </a
      ><a name="16091" href="Stlc.html#4815" class="Datatype Operator"
      >&#8712;</a
      ><a name="16092"
      > </a
      ><a name="16093" href="StlcProp.html#15980" class="Bound"
      >B</a
      >
{% endraw %}</pre>

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
<pre class="Agda">{% raw %}
<a name="19210" href="StlcProp.html#19210" class="Function"
      >weaken-closed</a
      ><a name="19223"
      > </a
      ><a name="19224" class="Symbol"
      >:</a
      ><a name="19225"
      > </a
      ><a name="19226" class="Symbol"
      >&#8704;</a
      ><a name="19227"
      > </a
      ><a name="19228" class="Symbol"
      >{</a
      ><a name="19229" href="StlcProp.html#19229" class="Bound"
      >V</a
      ><a name="19230"
      > </a
      ><a name="19231" href="StlcProp.html#19231" class="Bound"
      >A</a
      ><a name="19232"
      > </a
      ><a name="19233" href="StlcProp.html#19233" class="Bound"
      >&#915;</a
      ><a name="19234" class="Symbol"
      >}</a
      ><a name="19235"
      > </a
      ><a name="19236" class="Symbol"
      >&#8594;</a
      ><a name="19237"
      > </a
      ><a name="19238" href="Maps.html#10360" class="Function"
      >&#8709;</a
      ><a name="19239"
      > </a
      ><a name="19240" href="Stlc.html#4815" class="Datatype Operator"
      >&#8866;</a
      ><a name="19241"
      > </a
      ><a name="19242" href="StlcProp.html#19229" class="Bound"
      >V</a
      ><a name="19243"
      > </a
      ><a name="19244" href="Stlc.html#4815" class="Datatype Operator"
      >&#8712;</a
      ><a name="19245"
      > </a
      ><a name="19246" href="StlcProp.html#19231" class="Bound"
      >A</a
      ><a name="19247"
      > </a
      ><a name="19248" class="Symbol"
      >&#8594;</a
      ><a name="19249"
      > </a
      ><a name="19250" href="StlcProp.html#19233" class="Bound"
      >&#915;</a
      ><a name="19251"
      > </a
      ><a name="19252" href="Stlc.html#4815" class="Datatype Operator"
      >&#8866;</a
      ><a name="19253"
      > </a
      ><a name="19254" href="StlcProp.html#19229" class="Bound"
      >V</a
      ><a name="19255"
      > </a
      ><a name="19256" href="Stlc.html#4815" class="Datatype Operator"
      >&#8712;</a
      ><a name="19257"
      > </a
      ><a name="19258" href="StlcProp.html#19231" class="Bound"
      >A</a
      ><a name="19259"
      >
</a
      ><a name="19260" href="StlcProp.html#19210" class="Function"
      >weaken-closed</a
      ><a name="19273"
      > </a
      ><a name="19274" class="Symbol"
      >{</a
      ><a name="19275" href="StlcProp.html#19275" class="Bound"
      >V</a
      ><a name="19276" class="Symbol"
      >}</a
      ><a name="19277"
      > </a
      ><a name="19278" class="Symbol"
      >{</a
      ><a name="19279" href="StlcProp.html#19279" class="Bound"
      >A</a
      ><a name="19280" class="Symbol"
      >}</a
      ><a name="19281"
      > </a
      ><a name="19282" class="Symbol"
      >{</a
      ><a name="19283" href="StlcProp.html#19283" class="Bound"
      >&#915;</a
      ><a name="19284" class="Symbol"
      >}</a
      ><a name="19285"
      > </a
      ><a name="19286" href="StlcProp.html#19286" class="Bound"
      >&#8866;V</a
      ><a name="19288"
      > </a
      ><a name="19289" class="Symbol"
      >=</a
      ><a name="19290"
      > </a
      ><a name="19291" href="StlcProp.html#11728" class="Function"
      >weaken</a
      ><a name="19297"
      > </a
      ><a name="19298" href="StlcProp.html#19316" class="Function"
      >&#915;~&#915;&#8242;</a
      ><a name="19302"
      > </a
      ><a name="19303" href="StlcProp.html#19286" class="Bound"
      >&#8866;V</a
      ><a name="19305"
      >
  </a
      ><a name="19308" class="Keyword"
      >where</a
      ><a name="19313"
      >
  </a
      ><a name="19316" href="StlcProp.html#19316" class="Function"
      >&#915;~&#915;&#8242;</a
      ><a name="19320"
      > </a
      ><a name="19321" class="Symbol"
      >:</a
      ><a name="19322"
      > </a
      ><a name="19323" class="Symbol"
      >&#8704;</a
      ><a name="19324"
      > </a
      ><a name="19325" class="Symbol"
      >{</a
      ><a name="19326" href="StlcProp.html#19326" class="Bound"
      >x</a
      ><a name="19327" class="Symbol"
      >}</a
      ><a name="19328"
      > </a
      ><a name="19329" class="Symbol"
      >&#8594;</a
      ><a name="19330"
      > </a
      ><a name="19331" href="StlcProp.html#19326" class="Bound"
      >x</a
      ><a name="19332"
      > </a
      ><a name="19333" href="StlcProp.html#7297" class="Datatype Operator"
      >FreeIn</a
      ><a name="19339"
      > </a
      ><a name="19340" href="StlcProp.html#19275" class="Bound"
      >V</a
      ><a name="19341"
      > </a
      ><a name="19342" class="Symbol"
      >&#8594;</a
      ><a name="19343"
      > </a
      ><a name="19344" href="Maps.html#10360" class="Function"
      >&#8709;</a
      ><a name="19345"
      > </a
      ><a name="19346" href="StlcProp.html#19326" class="Bound"
      >x</a
      ><a name="19347"
      > </a
      ><a name="19348" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="19349"
      > </a
      ><a name="19350" href="StlcProp.html#19283" class="Bound"
      >&#915;</a
      ><a name="19351"
      > </a
      ><a name="19352" href="StlcProp.html#19326" class="Bound"
      >x</a
      ><a name="19353"
      >
  </a
      ><a name="19356" href="StlcProp.html#19316" class="Function"
      >&#915;~&#915;&#8242;</a
      ><a name="19360"
      > </a
      ><a name="19361" class="Symbol"
      >{</a
      ><a name="19362" href="StlcProp.html#19362" class="Bound"
      >x</a
      ><a name="19363" class="Symbol"
      >}</a
      ><a name="19364"
      > </a
      ><a name="19365" href="StlcProp.html#19365" class="Bound"
      >x&#8712;V</a
      ><a name="19368"
      > </a
      ><a name="19369" class="Symbol"
      >=</a
      ><a name="19370"
      > </a
      ><a name="19371" href="https://agda.github.io/agda-stdlib/Data.Empty.html#348" class="Function"
      >&#8869;-elim</a
      ><a name="19377"
      > </a
      ><a name="19378" class="Symbol"
      >(</a
      ><a name="19379" href="StlcProp.html#19402" class="Function"
      >x&#8713;V</a
      ><a name="19382"
      > </a
      ><a name="19383" href="StlcProp.html#19365" class="Bound"
      >x&#8712;V</a
      ><a name="19386" class="Symbol"
      >)</a
      ><a name="19387"
      >
    </a
      ><a name="19392" class="Keyword"
      >where</a
      ><a name="19397"
      >
    </a
      ><a name="19402" href="StlcProp.html#19402" class="Function"
      >x&#8713;V</a
      ><a name="19405"
      > </a
      ><a name="19406" class="Symbol"
      >:</a
      ><a name="19407"
      > </a
      ><a name="19408" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#414" class="Function Operator"
      >&#172;</a
      ><a name="19409"
      > </a
      ><a name="19410" class="Symbol"
      >(</a
      ><a name="19411" href="StlcProp.html#19362" class="Bound"
      >x</a
      ><a name="19412"
      > </a
      ><a name="19413" href="StlcProp.html#7297" class="Datatype Operator"
      >FreeIn</a
      ><a name="19419"
      > </a
      ><a name="19420" href="StlcProp.html#19275" class="Bound"
      >V</a
      ><a name="19421" class="Symbol"
      >)</a
      ><a name="19422"
      >
    </a
      ><a name="19427" href="StlcProp.html#19402" class="Function"
      >x&#8713;V</a
      ><a name="19430"
      > </a
      ><a name="19431" class="Symbol"
      >=</a
      ><a name="19432"
      > </a
      ><a name="19433" href="StlcProp.html#11027" class="Postulate"
      >&#8709;&#8866;-closed</a
      ><a name="19442"
      > </a
      ><a name="19443" href="StlcProp.html#19286" class="Bound"
      >&#8866;V</a
      ><a name="19445"
      > </a
      ><a name="19446" class="Symbol"
      >{</a
      ><a name="19447" href="StlcProp.html#19362" class="Bound"
      >x</a
      ><a name="19448" class="Symbol"
      >}</a
      ><a name="19449"
      >

</a
      ><a name="19451" href="StlcProp.html#19451" class="Function"
      >just-injective</a
      ><a name="19465"
      > </a
      ><a name="19466" class="Symbol"
      >:</a
      ><a name="19467"
      > </a
      ><a name="19468" class="Symbol"
      >&#8704;</a
      ><a name="19469"
      > </a
      ><a name="19470" class="Symbol"
      >{</a
      ><a name="19471" href="StlcProp.html#19471" class="Bound"
      >X</a
      ><a name="19472"
      > </a
      ><a name="19473" class="Symbol"
      >:</a
      ><a name="19474"
      > </a
      ><a name="19475" class="PrimitiveType"
      >Set</a
      ><a name="19478" class="Symbol"
      >}</a
      ><a name="19479"
      > </a
      ><a name="19480" class="Symbol"
      >{</a
      ><a name="19481" href="StlcProp.html#19481" class="Bound"
      >x</a
      ><a name="19482"
      > </a
      ><a name="19483" href="StlcProp.html#19483" class="Bound"
      >y</a
      ><a name="19484"
      > </a
      ><a name="19485" class="Symbol"
      >:</a
      ><a name="19486"
      > </a
      ><a name="19487" href="StlcProp.html#19471" class="Bound"
      >X</a
      ><a name="19488" class="Symbol"
      >}</a
      ><a name="19489"
      > </a
      ><a name="19490" class="Symbol"
      >&#8594;</a
      ><a name="19491"
      > </a
      ><a name="19492" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >_&#8801;_</a
      ><a name="19495"
      > </a
      ><a name="19496" class="Symbol"
      >{</a
      ><a name="19497" class="Argument"
      >A</a
      ><a name="19498"
      > </a
      ><a name="19499" class="Symbol"
      >=</a
      ><a name="19500"
      > </a
      ><a name="19501" href="https://agda.github.io/agda-stdlib/Data.Maybe.Base.html#335" class="Datatype"
      >Maybe</a
      ><a name="19506"
      > </a
      ><a name="19507" href="StlcProp.html#19471" class="Bound"
      >X</a
      ><a name="19508" class="Symbol"
      >}</a
      ><a name="19509"
      > </a
      ><a name="19510" class="Symbol"
      >(</a
      ><a name="19511" href="https://agda.github.io/agda-stdlib/Data.Maybe.Base.html#373" class="InductiveConstructor"
      >just</a
      ><a name="19515"
      > </a
      ><a name="19516" href="StlcProp.html#19481" class="Bound"
      >x</a
      ><a name="19517" class="Symbol"
      >)</a
      ><a name="19518"
      > </a
      ><a name="19519" class="Symbol"
      >(</a
      ><a name="19520" href="https://agda.github.io/agda-stdlib/Data.Maybe.Base.html#373" class="InductiveConstructor"
      >just</a
      ><a name="19524"
      > </a
      ><a name="19525" href="StlcProp.html#19483" class="Bound"
      >y</a
      ><a name="19526" class="Symbol"
      >)</a
      ><a name="19527"
      > </a
      ><a name="19528" class="Symbol"
      >&#8594;</a
      ><a name="19529"
      > </a
      ><a name="19530" href="StlcProp.html#19481" class="Bound"
      >x</a
      ><a name="19531"
      > </a
      ><a name="19532" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="19533"
      > </a
      ><a name="19534" href="StlcProp.html#19483" class="Bound"
      >y</a
      ><a name="19535"
      >
</a
      ><a name="19536" href="StlcProp.html#19451" class="Function"
      >just-injective</a
      ><a name="19550"
      > </a
      ><a name="19551" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="19555"
      > </a
      ><a name="19556" class="Symbol"
      >=</a
      ><a name="19557"
      > </a
      ><a name="19558" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      >
{% endraw %}</pre>

<pre class="Agda">{% raw %}
<a name="19588" href="StlcProp.html#15949" class="Function"
      >preservation-[:=]</a
      ><a name="19605"
      > </a
      ><a name="19606" class="Symbol"
      >{_}</a
      ><a name="19609"
      > </a
      ><a name="19610" class="Symbol"
      >{</a
      ><a name="19611" href="StlcProp.html#19611" class="Bound"
      >x</a
      ><a name="19612" class="Symbol"
      >}</a
      ><a name="19613"
      > </a
      ><a name="19614" class="Symbol"
      >(</a
      ><a name="19615" href="Stlc.html#4859" class="InductiveConstructor"
      >Ax</a
      ><a name="19617"
      > </a
      ><a name="19618" class="Symbol"
      >{_}</a
      ><a name="19621"
      > </a
      ><a name="19622" class="Symbol"
      >{</a
      ><a name="19623" href="StlcProp.html#19623" class="Bound"
      >x&#8242;</a
      ><a name="19625" class="Symbol"
      >}</a
      ><a name="19626"
      > </a
      ><a name="19627" href="StlcProp.html#19627" class="Bound"
      >[&#915;,x&#8614;A]x&#8242;&#8801;B</a
      ><a name="19638" class="Symbol"
      >)</a
      ><a name="19639"
      > </a
      ><a name="19640" href="StlcProp.html#19640" class="Bound"
      >&#8866;V</a
      ><a name="19642"
      > </a
      ><a name="19643" class="Keyword"
      >with</a
      ><a name="19647"
      > </a
      ><a name="19648" href="StlcProp.html#19611" class="Bound"
      >x</a
      ><a name="19649"
      > </a
      ><a name="19650" href="Maps.html#2558" class="Function Operator"
      >&#8799;</a
      ><a name="19651"
      > </a
      ><a name="19652" href="StlcProp.html#19623" class="Bound"
      >x&#8242;</a
      ><a name="19654"
      >
</a
      ><a name="19655" class="Symbol"
      >...|</a
      ><a name="19659"
      > </a
      ><a name="19660" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#520" class="InductiveConstructor"
      >yes</a
      ><a name="19663"
      > </a
      ><a name="19664" href="StlcProp.html#19664" class="Bound"
      >x&#8801;x&#8242;</a
      ><a name="19668"
      > </a
      ><a name="19669" class="Keyword"
      >rewrite</a
      ><a name="19676"
      > </a
      ><a name="19677" href="StlcProp.html#19451" class="Function"
      >just-injective</a
      ><a name="19691"
      > </a
      ><a name="19692" href="StlcProp.html#19627" class="Bound"
      >[&#915;,x&#8614;A]x&#8242;&#8801;B</a
      ><a name="19703"
      >  </a
      ><a name="19705" class="Symbol"
      >=</a
      ><a name="19706"
      >  </a
      ><a name="19708" href="StlcProp.html#19210" class="Function"
      >weaken-closed</a
      ><a name="19721"
      > </a
      ><a name="19722" href="StlcProp.html#19640" class="Bound"
      >&#8866;V</a
      ><a name="19724"
      >
</a
      ><a name="19725" class="Symbol"
      >...|</a
      ><a name="19729"
      > </a
      ><a name="19730" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#547" class="InductiveConstructor"
      >no</a
      ><a name="19732"
      >  </a
      ><a name="19734" href="StlcProp.html#19734" class="Bound"
      >x&#8802;x&#8242;</a
      ><a name="19738"
      >  </a
      ><a name="19740" class="Symbol"
      >=</a
      ><a name="19741"
      >  </a
      ><a name="19743" href="Stlc.html#4859" class="InductiveConstructor"
      >Ax</a
      ><a name="19745"
      > </a
      ><a name="19746" href="StlcProp.html#19627" class="Bound"
      >[&#915;,x&#8614;A]x&#8242;&#8801;B</a
      ><a name="19757"
      >
</a
      ><a name="19758" href="StlcProp.html#15949" class="Function"
      >preservation-[:=]</a
      ><a name="19775"
      > </a
      ><a name="19776" class="Symbol"
      >{</a
      ><a name="19777" href="StlcProp.html#19777" class="Bound"
      >&#915;</a
      ><a name="19778" class="Symbol"
      >}</a
      ><a name="19779"
      > </a
      ><a name="19780" class="Symbol"
      >{</a
      ><a name="19781" href="StlcProp.html#19781" class="Bound"
      >x</a
      ><a name="19782" class="Symbol"
      >}</a
      ><a name="19783"
      > </a
      ><a name="19784" class="Symbol"
      >{</a
      ><a name="19785" href="StlcProp.html#19785" class="Bound"
      >A</a
      ><a name="19786" class="Symbol"
      >}</a
      ><a name="19787"
      > </a
      ><a name="19788" class="Symbol"
      >{</a
      ><a name="19789" href="Stlc.html#1182" class="InductiveConstructor Operator"
      >&#955;&#7488;</a
      ><a name="19791"
      > </a
      ><a name="19792" href="StlcProp.html#19792" class="Bound"
      >x&#8242;</a
      ><a name="19794"
      > </a
      ><a name="19795" href="Stlc.html#1182" class="InductiveConstructor Operator"
      >&#8712;</a
      ><a name="19796"
      > </a
      ><a name="19797" href="StlcProp.html#19797" class="Bound"
      >A&#8242;</a
      ><a name="19799"
      > </a
      ><a name="19800" href="Stlc.html#1182" class="InductiveConstructor Operator"
      >&#8658;</a
      ><a name="19801"
      > </a
      ><a name="19802" href="StlcProp.html#19802" class="Bound"
      >N&#8242;</a
      ><a name="19804" class="Symbol"
      >}</a
      ><a name="19805"
      > </a
      ><a name="19806" class="Symbol"
      >{</a
      ><a name="19807" class="DottedPattern Symbol"
      >.</a
      ><a name="19808" href="StlcProp.html#19797" class="DottedPattern Bound"
      >A&#8242;</a
      ><a name="19810"
      > </a
      ><a name="19811" href="Stlc.html#1113" class="InductiveConstructor Operator"
      >&#8658;</a
      ><a name="19812"
      > </a
      ><a name="19813" href="StlcProp.html#19813" class="Bound"
      >B&#8242;</a
      ><a name="19815" class="Symbol"
      >}</a
      ><a name="19816"
      > </a
      ><a name="19817" class="Symbol"
      >{</a
      ><a name="19818" href="StlcProp.html#19818" class="Bound"
      >V</a
      ><a name="19819" class="Symbol"
      >}</a
      ><a name="19820"
      > </a
      ><a name="19821" class="Symbol"
      >(</a
      ><a name="19822" href="Stlc.html#4916" class="InductiveConstructor"
      >&#8658;-I</a
      ><a name="19825"
      > </a
      ><a name="19826" href="StlcProp.html#19826" class="Bound"
      >&#8866;N&#8242;</a
      ><a name="19829" class="Symbol"
      >)</a
      ><a name="19830"
      > </a
      ><a name="19831" href="StlcProp.html#19831" class="Bound"
      >&#8866;V</a
      ><a name="19833"
      > </a
      ><a name="19834" class="Keyword"
      >with</a
      ><a name="19838"
      > </a
      ><a name="19839" href="StlcProp.html#19781" class="Bound"
      >x</a
      ><a name="19840"
      > </a
      ><a name="19841" href="Maps.html#2558" class="Function Operator"
      >&#8799;</a
      ><a name="19842"
      > </a
      ><a name="19843" href="StlcProp.html#19792" class="Bound"
      >x&#8242;</a
      ><a name="19845"
      >
</a
      ><a name="19846" class="Symbol"
      >...|</a
      ><a name="19850"
      > </a
      ><a name="19851" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#520" class="InductiveConstructor"
      >yes</a
      ><a name="19854"
      > </a
      ><a name="19855" href="StlcProp.html#19855" class="Bound"
      >x&#8801;x&#8242;</a
      ><a name="19859"
      > </a
      ><a name="19860" class="Keyword"
      >rewrite</a
      ><a name="19867"
      > </a
      ><a name="19868" href="StlcProp.html#19855" class="Bound"
      >x&#8801;x&#8242;</a
      ><a name="19872"
      > </a
      ><a name="19873" class="Symbol"
      >=</a
      ><a name="19874"
      > </a
      ><a name="19875" href="StlcProp.html#11728" class="Function"
      >weaken</a
      ><a name="19881"
      > </a
      ><a name="19882" href="StlcProp.html#19907" class="Function"
      >&#915;&#8242;~&#915;</a
      ><a name="19886"
      > </a
      ><a name="19887" class="Symbol"
      >(</a
      ><a name="19888" href="Stlc.html#4916" class="InductiveConstructor"
      >&#8658;-I</a
      ><a name="19891"
      > </a
      ><a name="19892" href="StlcProp.html#19826" class="Bound"
      >&#8866;N&#8242;</a
      ><a name="19895" class="Symbol"
      >)</a
      ><a name="19896"
      >
  </a
      ><a name="19899" class="Keyword"
      >where</a
      ><a name="19904"
      >
  </a
      ><a name="19907" href="StlcProp.html#19907" class="Function"
      >&#915;&#8242;~&#915;</a
      ><a name="19911"
      > </a
      ><a name="19912" class="Symbol"
      >:</a
      ><a name="19913"
      > </a
      ><a name="19914" class="Symbol"
      >&#8704;</a
      ><a name="19915"
      > </a
      ><a name="19916" class="Symbol"
      >{</a
      ><a name="19917" href="StlcProp.html#19917" class="Bound"
      >y</a
      ><a name="19918" class="Symbol"
      >}</a
      ><a name="19919"
      > </a
      ><a name="19920" class="Symbol"
      >&#8594;</a
      ><a name="19921"
      > </a
      ><a name="19922" href="StlcProp.html#19917" class="Bound"
      >y</a
      ><a name="19923"
      > </a
      ><a name="19924" href="StlcProp.html#7297" class="Datatype Operator"
      >FreeIn</a
      ><a name="19930"
      > </a
      ><a name="19931" class="Symbol"
      >(</a
      ><a name="19932" href="Stlc.html#1182" class="InductiveConstructor Operator"
      >&#955;&#7488;</a
      ><a name="19934"
      > </a
      ><a name="19935" href="StlcProp.html#19792" class="Bound"
      >x&#8242;</a
      ><a name="19937"
      > </a
      ><a name="19938" href="Stlc.html#1182" class="InductiveConstructor Operator"
      >&#8712;</a
      ><a name="19939"
      > </a
      ><a name="19940" href="StlcProp.html#19797" class="Bound"
      >A&#8242;</a
      ><a name="19942"
      > </a
      ><a name="19943" href="Stlc.html#1182" class="InductiveConstructor Operator"
      >&#8658;</a
      ><a name="19944"
      > </a
      ><a name="19945" href="StlcProp.html#19802" class="Bound"
      >N&#8242;</a
      ><a name="19947" class="Symbol"
      >)</a
      ><a name="19948"
      > </a
      ><a name="19949" class="Symbol"
      >&#8594;</a
      ><a name="19950"
      > </a
      ><a name="19951" class="Symbol"
      >(</a
      ><a name="19952" href="StlcProp.html#19777" class="Bound"
      >&#915;</a
      ><a name="19953"
      > </a
      ><a name="19954" href="Maps.html#10464" class="Function Operator"
      >,</a
      ><a name="19955"
      > </a
      ><a name="19956" href="StlcProp.html#19792" class="Bound"
      >x&#8242;</a
      ><a name="19958"
      > </a
      ><a name="19959" href="Maps.html#10464" class="Function Operator"
      >&#8614;</a
      ><a name="19960"
      > </a
      ><a name="19961" href="StlcProp.html#19785" class="Bound"
      >A</a
      ><a name="19962" class="Symbol"
      >)</a
      ><a name="19963"
      > </a
      ><a name="19964" href="StlcProp.html#19917" class="Bound"
      >y</a
      ><a name="19965"
      > </a
      ><a name="19966" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="19967"
      > </a
      ><a name="19968" href="StlcProp.html#19777" class="Bound"
      >&#915;</a
      ><a name="19969"
      > </a
      ><a name="19970" href="StlcProp.html#19917" class="Bound"
      >y</a
      ><a name="19971"
      >
  </a
      ><a name="19974" href="StlcProp.html#19907" class="Function"
      >&#915;&#8242;~&#915;</a
      ><a name="19978"
      > </a
      ><a name="19979" class="Symbol"
      >{</a
      ><a name="19980" href="StlcProp.html#19980" class="Bound"
      >y</a
      ><a name="19981" class="Symbol"
      >}</a
      ><a name="19982"
      > </a
      ><a name="19983" class="Symbol"
      >(</a
      ><a name="19984" href="StlcProp.html#7373" class="InductiveConstructor"
      >free-&#955;&#7488;</a
      ><a name="19991"
      > </a
      ><a name="19992" href="StlcProp.html#19992" class="Bound"
      >x&#8242;&#8802;y</a
      ><a name="19996"
      > </a
      ><a name="19997" href="StlcProp.html#19997" class="Bound"
      >y&#8712;N&#8242;</a
      ><a name="20001" class="Symbol"
      >)</a
      ><a name="20002"
      > </a
      ><a name="20003" class="Keyword"
      >with</a
      ><a name="20007"
      > </a
      ><a name="20008" href="StlcProp.html#19792" class="Bound"
      >x&#8242;</a
      ><a name="20010"
      > </a
      ><a name="20011" href="Maps.html#2558" class="Function Operator"
      >&#8799;</a
      ><a name="20012"
      > </a
      ><a name="20013" href="StlcProp.html#19980" class="Bound"
      >y</a
      ><a name="20014"
      >
  </a
      ><a name="20017" class="Symbol"
      >...|</a
      ><a name="20021"
      > </a
      ><a name="20022" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#520" class="InductiveConstructor"
      >yes</a
      ><a name="20025"
      > </a
      ><a name="20026" href="StlcProp.html#20026" class="Bound"
      >x&#8242;&#8801;y</a
      ><a name="20030"
      >  </a
      ><a name="20032" class="Symbol"
      >=</a
      ><a name="20033"
      > </a
      ><a name="20034" href="https://agda.github.io/agda-stdlib/Data.Empty.html#348" class="Function"
      >&#8869;-elim</a
      ><a name="20040"
      > </a
      ><a name="20041" class="Symbol"
      >(</a
      ><a name="20042" href="StlcProp.html#19992" class="Bound"
      >x&#8242;&#8802;y</a
      ><a name="20046"
      > </a
      ><a name="20047" href="StlcProp.html#20026" class="Bound"
      >x&#8242;&#8801;y</a
      ><a name="20051" class="Symbol"
      >)</a
      ><a name="20052"
      >
  </a
      ><a name="20055" class="Symbol"
      >...|</a
      ><a name="20059"
      > </a
      ><a name="20060" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#547" class="InductiveConstructor"
      >no</a
      ><a name="20062"
      >  </a
      ><a name="20064" class="Symbol"
      >_</a
      ><a name="20065"
      >     </a
      ><a name="20070" class="Symbol"
      >=</a
      ><a name="20071"
      > </a
      ><a name="20072" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="20076"
      >
</a
      ><a name="20077" class="Symbol"
      >...|</a
      ><a name="20081"
      > </a
      ><a name="20082" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#547" class="InductiveConstructor"
      >no</a
      ><a name="20084"
      >  </a
      ><a name="20086" href="StlcProp.html#20086" class="Bound"
      >x&#8802;x&#8242;</a
      ><a name="20090"
      > </a
      ><a name="20091" class="Symbol"
      >=</a
      ><a name="20092"
      > </a
      ><a name="20093" href="Stlc.html#4916" class="InductiveConstructor"
      >&#8658;-I</a
      ><a name="20096"
      > </a
      ><a name="20097" href="StlcProp.html#20208" class="Function"
      >&#8866;N&#8242;V</a
      ><a name="20101"
      >
  </a
      ><a name="20104" class="Keyword"
      >where</a
      ><a name="20109"
      >
  </a
      ><a name="20112" href="StlcProp.html#20112" class="Function"
      >x&#8242;x&#8866;N&#8242;</a
      ><a name="20118"
      > </a
      ><a name="20119" class="Symbol"
      >:</a
      ><a name="20120"
      > </a
      ><a name="20121" href="StlcProp.html#19777" class="Bound"
      >&#915;</a
      ><a name="20122"
      > </a
      ><a name="20123" href="Maps.html#10464" class="Function Operator"
      >,</a
      ><a name="20124"
      > </a
      ><a name="20125" href="StlcProp.html#19792" class="Bound"
      >x&#8242;</a
      ><a name="20127"
      > </a
      ><a name="20128" href="Maps.html#10464" class="Function Operator"
      >&#8614;</a
      ><a name="20129"
      > </a
      ><a name="20130" href="StlcProp.html#19797" class="Bound"
      >A&#8242;</a
      ><a name="20132"
      > </a
      ><a name="20133" href="Maps.html#10464" class="Function Operator"
      >,</a
      ><a name="20134"
      > </a
      ><a name="20135" href="StlcProp.html#19781" class="Bound"
      >x</a
      ><a name="20136"
      > </a
      ><a name="20137" href="Maps.html#10464" class="Function Operator"
      >&#8614;</a
      ><a name="20138"
      > </a
      ><a name="20139" href="StlcProp.html#19785" class="Bound"
      >A</a
      ><a name="20140"
      > </a
      ><a name="20141" href="Stlc.html#4815" class="Datatype Operator"
      >&#8866;</a
      ><a name="20142"
      > </a
      ><a name="20143" href="StlcProp.html#19802" class="Bound"
      >N&#8242;</a
      ><a name="20145"
      > </a
      ><a name="20146" href="Stlc.html#4815" class="Datatype Operator"
      >&#8712;</a
      ><a name="20147"
      > </a
      ><a name="20148" href="StlcProp.html#19813" class="Bound"
      >B&#8242;</a
      ><a name="20150"
      >
  </a
      ><a name="20153" href="StlcProp.html#20112" class="Function"
      >x&#8242;x&#8866;N&#8242;</a
      ><a name="20159"
      > </a
      ><a name="20160" class="Keyword"
      >rewrite</a
      ><a name="20167"
      > </a
      ><a name="20168" href="Maps.html#11587" class="Function"
      >update-permute</a
      ><a name="20182"
      > </a
      ><a name="20183" href="StlcProp.html#19777" class="Bound"
      >&#915;</a
      ><a name="20184"
      > </a
      ><a name="20185" href="StlcProp.html#19781" class="Bound"
      >x</a
      ><a name="20186"
      > </a
      ><a name="20187" href="StlcProp.html#19785" class="Bound"
      >A</a
      ><a name="20188"
      > </a
      ><a name="20189" href="StlcProp.html#19792" class="Bound"
      >x&#8242;</a
      ><a name="20191"
      > </a
      ><a name="20192" href="StlcProp.html#19797" class="Bound"
      >A&#8242;</a
      ><a name="20194"
      > </a
      ><a name="20195" href="StlcProp.html#20086" class="Bound"
      >x&#8802;x&#8242;</a
      ><a name="20199"
      > </a
      ><a name="20200" class="Symbol"
      >=</a
      ><a name="20201"
      > </a
      ><a name="20202" href="StlcProp.html#19826" class="Bound"
      >&#8866;N&#8242;</a
      ><a name="20205"
      >
  </a
      ><a name="20208" href="StlcProp.html#20208" class="Function"
      >&#8866;N&#8242;V</a
      ><a name="20212"
      > </a
      ><a name="20213" class="Symbol"
      >:</a
      ><a name="20214"
      > </a
      ><a name="20215" class="Symbol"
      >(</a
      ><a name="20216" href="StlcProp.html#19777" class="Bound"
      >&#915;</a
      ><a name="20217"
      > </a
      ><a name="20218" href="Maps.html#10464" class="Function Operator"
      >,</a
      ><a name="20219"
      > </a
      ><a name="20220" href="StlcProp.html#19792" class="Bound"
      >x&#8242;</a
      ><a name="20222"
      > </a
      ><a name="20223" href="Maps.html#10464" class="Function Operator"
      >&#8614;</a
      ><a name="20224"
      > </a
      ><a name="20225" href="StlcProp.html#19797" class="Bound"
      >A&#8242;</a
      ><a name="20227" class="Symbol"
      >)</a
      ><a name="20228"
      > </a
      ><a name="20229" href="Stlc.html#4815" class="Datatype Operator"
      >&#8866;</a
      ><a name="20230"
      > </a
      ><a name="20231" href="StlcProp.html#19802" class="Bound"
      >N&#8242;</a
      ><a name="20233"
      > </a
      ><a name="20234" href="Stlc.html#1868" class="Function Operator"
      >[</a
      ><a name="20235"
      > </a
      ><a name="20236" href="StlcProp.html#19781" class="Bound"
      >x</a
      ><a name="20237"
      > </a
      ><a name="20238" href="Stlc.html#1868" class="Function Operator"
      >:=</a
      ><a name="20240"
      > </a
      ><a name="20241" href="StlcProp.html#19818" class="Bound"
      >V</a
      ><a name="20242"
      > </a
      ><a name="20243" href="Stlc.html#1868" class="Function Operator"
      >]</a
      ><a name="20244"
      > </a
      ><a name="20245" href="Stlc.html#4815" class="Datatype Operator"
      >&#8712;</a
      ><a name="20246"
      > </a
      ><a name="20247" href="StlcProp.html#19813" class="Bound"
      >B&#8242;</a
      ><a name="20249"
      >
  </a
      ><a name="20252" href="StlcProp.html#20208" class="Function"
      >&#8866;N&#8242;V</a
      ><a name="20256"
      > </a
      ><a name="20257" class="Symbol"
      >=</a
      ><a name="20258"
      > </a
      ><a name="20259" href="StlcProp.html#15949" class="Function"
      >preservation-[:=]</a
      ><a name="20276"
      > </a
      ><a name="20277" href="StlcProp.html#20112" class="Function"
      >x&#8242;x&#8866;N&#8242;</a
      ><a name="20283"
      > </a
      ><a name="20284" href="StlcProp.html#19831" class="Bound"
      >&#8866;V</a
      ><a name="20286"
      >
</a
      ><a name="20287" href="StlcProp.html#15949" class="Function"
      >preservation-[:=]</a
      ><a name="20304"
      > </a
      ><a name="20305" class="Symbol"
      >(</a
      ><a name="20306" href="Stlc.html#4999" class="InductiveConstructor"
      >&#8658;-E</a
      ><a name="20309"
      > </a
      ><a name="20310" href="StlcProp.html#20310" class="Bound"
      >&#8866;L</a
      ><a name="20312"
      > </a
      ><a name="20313" href="StlcProp.html#20313" class="Bound"
      >&#8866;M</a
      ><a name="20315" class="Symbol"
      >)</a
      ><a name="20316"
      > </a
      ><a name="20317" href="StlcProp.html#20317" class="Bound"
      >&#8866;V</a
      ><a name="20319"
      > </a
      ><a name="20320" class="Symbol"
      >=</a
      ><a name="20321"
      > </a
      ><a name="20322" href="Stlc.html#4999" class="InductiveConstructor"
      >&#8658;-E</a
      ><a name="20325"
      > </a
      ><a name="20326" class="Symbol"
      >(</a
      ><a name="20327" href="StlcProp.html#15949" class="Function"
      >preservation-[:=]</a
      ><a name="20344"
      > </a
      ><a name="20345" href="StlcProp.html#20310" class="Bound"
      >&#8866;L</a
      ><a name="20347"
      > </a
      ><a name="20348" href="StlcProp.html#20317" class="Bound"
      >&#8866;V</a
      ><a name="20350" class="Symbol"
      >)</a
      ><a name="20351"
      > </a
      ><a name="20352" class="Symbol"
      >(</a
      ><a name="20353" href="StlcProp.html#15949" class="Function"
      >preservation-[:=]</a
      ><a name="20370"
      > </a
      ><a name="20371" href="StlcProp.html#20313" class="Bound"
      >&#8866;M</a
      ><a name="20373"
      > </a
      ><a name="20374" href="StlcProp.html#20317" class="Bound"
      >&#8866;V</a
      ><a name="20376" class="Symbol"
      >)</a
      ><a name="20377"
      >
</a
      ><a name="20378" href="StlcProp.html#15949" class="Function"
      >preservation-[:=]</a
      ><a name="20395"
      > </a
      ><a name="20396" href="Stlc.html#5080" class="InductiveConstructor"
      >&#120121;-I&#8321;</a
      ><a name="20400"
      > </a
      ><a name="20401" href="StlcProp.html#20401" class="Bound"
      >&#8866;V</a
      ><a name="20403"
      > </a
      ><a name="20404" class="Symbol"
      >=</a
      ><a name="20405"
      > </a
      ><a name="20406" href="Stlc.html#5080" class="InductiveConstructor"
      >&#120121;-I&#8321;</a
      ><a name="20410"
      >
</a
      ><a name="20411" href="StlcProp.html#15949" class="Function"
      >preservation-[:=]</a
      ><a name="20428"
      > </a
      ><a name="20429" href="Stlc.html#5115" class="InductiveConstructor"
      >&#120121;-I&#8322;</a
      ><a name="20433"
      > </a
      ><a name="20434" href="StlcProp.html#20434" class="Bound"
      >&#8866;V</a
      ><a name="20436"
      > </a
      ><a name="20437" class="Symbol"
      >=</a
      ><a name="20438"
      > </a
      ><a name="20439" href="Stlc.html#5115" class="InductiveConstructor"
      >&#120121;-I&#8322;</a
      ><a name="20443"
      >
</a
      ><a name="20444" href="StlcProp.html#15949" class="Function"
      >preservation-[:=]</a
      ><a name="20461"
      > </a
      ><a name="20462" class="Symbol"
      >(</a
      ><a name="20463" href="Stlc.html#5151" class="InductiveConstructor"
      >&#120121;-E</a
      ><a name="20466"
      > </a
      ><a name="20467" href="StlcProp.html#20467" class="Bound"
      >&#8866;L</a
      ><a name="20469"
      > </a
      ><a name="20470" href="StlcProp.html#20470" class="Bound"
      >&#8866;M</a
      ><a name="20472"
      > </a
      ><a name="20473" href="StlcProp.html#20473" class="Bound"
      >&#8866;N</a
      ><a name="20475" class="Symbol"
      >)</a
      ><a name="20476"
      > </a
      ><a name="20477" href="StlcProp.html#20477" class="Bound"
      >&#8866;V</a
      ><a name="20479"
      > </a
      ><a name="20480" class="Symbol"
      >=</a
      ><a name="20481"
      >
  </a
      ><a name="20484" href="Stlc.html#5151" class="InductiveConstructor"
      >&#120121;-E</a
      ><a name="20487"
      > </a
      ><a name="20488" class="Symbol"
      >(</a
      ><a name="20489" href="StlcProp.html#15949" class="Function"
      >preservation-[:=]</a
      ><a name="20506"
      > </a
      ><a name="20507" href="StlcProp.html#20467" class="Bound"
      >&#8866;L</a
      ><a name="20509"
      > </a
      ><a name="20510" href="StlcProp.html#20477" class="Bound"
      >&#8866;V</a
      ><a name="20512" class="Symbol"
      >)</a
      ><a name="20513"
      > </a
      ><a name="20514" class="Symbol"
      >(</a
      ><a name="20515" href="StlcProp.html#15949" class="Function"
      >preservation-[:=]</a
      ><a name="20532"
      > </a
      ><a name="20533" href="StlcProp.html#20470" class="Bound"
      >&#8866;M</a
      ><a name="20535"
      > </a
      ><a name="20536" href="StlcProp.html#20477" class="Bound"
      >&#8866;V</a
      ><a name="20538" class="Symbol"
      >)</a
      ><a name="20539"
      > </a
      ><a name="20540" class="Symbol"
      >(</a
      ><a name="20541" href="StlcProp.html#15949" class="Function"
      >preservation-[:=]</a
      ><a name="20558"
      > </a
      ><a name="20559" href="StlcProp.html#20473" class="Bound"
      >&#8866;N</a
      ><a name="20561"
      > </a
      ><a name="20562" href="StlcProp.html#20477" class="Bound"
      >&#8866;V</a
      ><a name="20564" class="Symbol"
      >)</a
      >
{% endraw %}</pre>


### Main Theorem

We now have the tools we need to prove preservation: if a closed
term `M` has type `A` and takes a step to `N`, then `N`
is also a closed term with type `A`.  In other words, small-step
reduction preserves types.

<pre class="Agda">{% raw %}
<a name="20824" href="StlcProp.html#20824" class="Function"
      >preservation</a
      ><a name="20836"
      > </a
      ><a name="20837" class="Symbol"
      >:</a
      ><a name="20838"
      > </a
      ><a name="20839" class="Symbol"
      >&#8704;</a
      ><a name="20840"
      > </a
      ><a name="20841" class="Symbol"
      >{</a
      ><a name="20842" href="StlcProp.html#20842" class="Bound"
      >M</a
      ><a name="20843"
      > </a
      ><a name="20844" href="StlcProp.html#20844" class="Bound"
      >N</a
      ><a name="20845"
      > </a
      ><a name="20846" href="StlcProp.html#20846" class="Bound"
      >A</a
      ><a name="20847" class="Symbol"
      >}</a
      ><a name="20848"
      > </a
      ><a name="20849" class="Symbol"
      >&#8594;</a
      ><a name="20850"
      > </a
      ><a name="20851" href="Maps.html#10360" class="Function"
      >&#8709;</a
      ><a name="20852"
      > </a
      ><a name="20853" href="Stlc.html#4815" class="Datatype Operator"
      >&#8866;</a
      ><a name="20854"
      > </a
      ><a name="20855" href="StlcProp.html#20842" class="Bound"
      >M</a
      ><a name="20856"
      > </a
      ><a name="20857" href="Stlc.html#4815" class="Datatype Operator"
      >&#8712;</a
      ><a name="20858"
      > </a
      ><a name="20859" href="StlcProp.html#20846" class="Bound"
      >A</a
      ><a name="20860"
      > </a
      ><a name="20861" class="Symbol"
      >&#8594;</a
      ><a name="20862"
      > </a
      ><a name="20863" href="StlcProp.html#20842" class="Bound"
      >M</a
      ><a name="20864"
      > </a
      ><a name="20865" href="Stlc.html#2353" class="Datatype Operator"
      >&#10233;</a
      ><a name="20866"
      > </a
      ><a name="20867" href="StlcProp.html#20844" class="Bound"
      >N</a
      ><a name="20868"
      > </a
      ><a name="20869" class="Symbol"
      >&#8594;</a
      ><a name="20870"
      > </a
      ><a name="20871" href="Maps.html#10360" class="Function"
      >&#8709;</a
      ><a name="20872"
      > </a
      ><a name="20873" href="Stlc.html#4815" class="Datatype Operator"
      >&#8866;</a
      ><a name="20874"
      > </a
      ><a name="20875" href="StlcProp.html#20844" class="Bound"
      >N</a
      ><a name="20876"
      > </a
      ><a name="20877" href="Stlc.html#4815" class="Datatype Operator"
      >&#8712;</a
      ><a name="20878"
      > </a
      ><a name="20879" href="StlcProp.html#20846" class="Bound"
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

<pre class="Agda">{% raw %}
<a name="22174" href="StlcProp.html#20824" class="Function"
      >preservation</a
      ><a name="22186"
      > </a
      ><a name="22187" class="Symbol"
      >(</a
      ><a name="22188" href="Stlc.html#4859" class="InductiveConstructor"
      >Ax</a
      ><a name="22190"
      > </a
      ><a name="22191" href="StlcProp.html#22191" class="Bound"
      >x&#8321;</a
      ><a name="22193" class="Symbol"
      >)</a
      ><a name="22194"
      > </a
      ><a name="22195" class="Symbol"
      >()</a
      ><a name="22197"
      >
</a
      ><a name="22198" href="StlcProp.html#20824" class="Function"
      >preservation</a
      ><a name="22210"
      > </a
      ><a name="22211" class="Symbol"
      >(</a
      ><a name="22212" href="Stlc.html#4916" class="InductiveConstructor"
      >&#8658;-I</a
      ><a name="22215"
      > </a
      ><a name="22216" href="StlcProp.html#22216" class="Bound"
      >&#8866;N</a
      ><a name="22218" class="Symbol"
      >)</a
      ><a name="22219"
      > </a
      ><a name="22220" class="Symbol"
      >()</a
      ><a name="22222"
      >
</a
      ><a name="22223" href="StlcProp.html#20824" class="Function"
      >preservation</a
      ><a name="22235"
      > </a
      ><a name="22236" class="Symbol"
      >(</a
      ><a name="22237" href="Stlc.html#4999" class="InductiveConstructor"
      >&#8658;-E</a
      ><a name="22240"
      > </a
      ><a name="22241" class="Symbol"
      >(</a
      ><a name="22242" href="Stlc.html#4916" class="InductiveConstructor"
      >&#8658;-I</a
      ><a name="22245"
      > </a
      ><a name="22246" href="StlcProp.html#22246" class="Bound"
      >&#8866;N</a
      ><a name="22248" class="Symbol"
      >)</a
      ><a name="22249"
      > </a
      ><a name="22250" href="StlcProp.html#22250" class="Bound"
      >&#8866;V</a
      ><a name="22252" class="Symbol"
      >)</a
      ><a name="22253"
      > </a
      ><a name="22254" class="Symbol"
      >(</a
      ><a name="22255" href="Stlc.html#2385" class="InductiveConstructor"
      >&#946;&#8658;</a
      ><a name="22257"
      > </a
      ><a name="22258" href="StlcProp.html#22258" class="Bound"
      >valueV</a
      ><a name="22264" class="Symbol"
      >)</a
      ><a name="22265"
      > </a
      ><a name="22266" class="Symbol"
      >=</a
      ><a name="22267"
      > </a
      ><a name="22268" href="StlcProp.html#15949" class="Function"
      >preservation-[:=]</a
      ><a name="22285"
      > </a
      ><a name="22286" href="StlcProp.html#22246" class="Bound"
      >&#8866;N</a
      ><a name="22288"
      > </a
      ><a name="22289" href="StlcProp.html#22250" class="Bound"
      >&#8866;V</a
      ><a name="22291"
      >
</a
      ><a name="22292" href="StlcProp.html#20824" class="Function"
      >preservation</a
      ><a name="22304"
      > </a
      ><a name="22305" class="Symbol"
      >(</a
      ><a name="22306" href="Stlc.html#4999" class="InductiveConstructor"
      >&#8658;-E</a
      ><a name="22309"
      > </a
      ><a name="22310" href="StlcProp.html#22310" class="Bound"
      >&#8866;L</a
      ><a name="22312"
      > </a
      ><a name="22313" href="StlcProp.html#22313" class="Bound"
      >&#8866;M</a
      ><a name="22315" class="Symbol"
      >)</a
      ><a name="22316"
      > </a
      ><a name="22317" class="Symbol"
      >(</a
      ><a name="22318" href="Stlc.html#2459" class="InductiveConstructor"
      >&#947;&#8658;&#8321;</a
      ><a name="22321"
      > </a
      ><a name="22322" href="StlcProp.html#22322" class="Bound"
      >L&#10233;L&#8242;</a
      ><a name="22326" class="Symbol"
      >)</a
      ><a name="22327"
      > </a
      ><a name="22328" class="Keyword"
      >with</a
      ><a name="22332"
      > </a
      ><a name="22333" href="StlcProp.html#20824" class="Function"
      >preservation</a
      ><a name="22345"
      > </a
      ><a name="22346" href="StlcProp.html#22310" class="Bound"
      >&#8866;L</a
      ><a name="22348"
      > </a
      ><a name="22349" href="StlcProp.html#22322" class="Bound"
      >L&#10233;L&#8242;</a
      ><a name="22353"
      >
</a
      ><a name="22354" class="Symbol"
      >...|</a
      ><a name="22358"
      > </a
      ><a name="22359" href="StlcProp.html#22359" class="Bound"
      >&#8866;L&#8242;</a
      ><a name="22362"
      > </a
      ><a name="22363" class="Symbol"
      >=</a
      ><a name="22364"
      > </a
      ><a name="22365" href="Stlc.html#4999" class="InductiveConstructor"
      >&#8658;-E</a
      ><a name="22368"
      > </a
      ><a name="22369" href="StlcProp.html#22359" class="Bound"
      >&#8866;L&#8242;</a
      ><a name="22372"
      > </a
      ><a name="22373" href="StlcProp.html#22313" class="Bound"
      >&#8866;M</a
      ><a name="22375"
      >
</a
      ><a name="22376" href="StlcProp.html#20824" class="Function"
      >preservation</a
      ><a name="22388"
      > </a
      ><a name="22389" class="Symbol"
      >(</a
      ><a name="22390" href="Stlc.html#4999" class="InductiveConstructor"
      >&#8658;-E</a
      ><a name="22393"
      > </a
      ><a name="22394" href="StlcProp.html#22394" class="Bound"
      >&#8866;L</a
      ><a name="22396"
      > </a
      ><a name="22397" href="StlcProp.html#22397" class="Bound"
      >&#8866;M</a
      ><a name="22399" class="Symbol"
      >)</a
      ><a name="22400"
      > </a
      ><a name="22401" class="Symbol"
      >(</a
      ><a name="22402" href="Stlc.html#2518" class="InductiveConstructor"
      >&#947;&#8658;&#8322;</a
      ><a name="22405"
      > </a
      ><a name="22406" href="StlcProp.html#22406" class="Bound"
      >valueL</a
      ><a name="22412"
      > </a
      ><a name="22413" href="StlcProp.html#22413" class="Bound"
      >M&#10233;M&#8242;</a
      ><a name="22417" class="Symbol"
      >)</a
      ><a name="22418"
      > </a
      ><a name="22419" class="Keyword"
      >with</a
      ><a name="22423"
      > </a
      ><a name="22424" href="StlcProp.html#20824" class="Function"
      >preservation</a
      ><a name="22436"
      > </a
      ><a name="22437" href="StlcProp.html#22397" class="Bound"
      >&#8866;M</a
      ><a name="22439"
      > </a
      ><a name="22440" href="StlcProp.html#22413" class="Bound"
      >M&#10233;M&#8242;</a
      ><a name="22444"
      >
</a
      ><a name="22445" class="Symbol"
      >...|</a
      ><a name="22449"
      > </a
      ><a name="22450" href="StlcProp.html#22450" class="Bound"
      >&#8866;M&#8242;</a
      ><a name="22453"
      > </a
      ><a name="22454" class="Symbol"
      >=</a
      ><a name="22455"
      > </a
      ><a name="22456" href="Stlc.html#4999" class="InductiveConstructor"
      >&#8658;-E</a
      ><a name="22459"
      > </a
      ><a name="22460" href="StlcProp.html#22394" class="Bound"
      >&#8866;L</a
      ><a name="22462"
      > </a
      ><a name="22463" href="StlcProp.html#22450" class="Bound"
      >&#8866;M&#8242;</a
      ><a name="22466"
      >
</a
      ><a name="22467" href="StlcProp.html#20824" class="Function"
      >preservation</a
      ><a name="22479"
      > </a
      ><a name="22480" href="Stlc.html#5080" class="InductiveConstructor"
      >&#120121;-I&#8321;</a
      ><a name="22484"
      > </a
      ><a name="22485" class="Symbol"
      >()</a
      ><a name="22487"
      >
</a
      ><a name="22488" href="StlcProp.html#20824" class="Function"
      >preservation</a
      ><a name="22500"
      > </a
      ><a name="22501" href="Stlc.html#5115" class="InductiveConstructor"
      >&#120121;-I&#8322;</a
      ><a name="22505"
      > </a
      ><a name="22506" class="Symbol"
      >()</a
      ><a name="22508"
      >
</a
      ><a name="22509" href="StlcProp.html#20824" class="Function"
      >preservation</a
      ><a name="22521"
      > </a
      ><a name="22522" class="Symbol"
      >(</a
      ><a name="22523" href="Stlc.html#5151" class="InductiveConstructor"
      >&#120121;-E</a
      ><a name="22526"
      > </a
      ><a name="22527" href="Stlc.html#5080" class="InductiveConstructor"
      >&#120121;-I&#8321;</a
      ><a name="22531"
      > </a
      ><a name="22532" href="StlcProp.html#22532" class="Bound"
      >&#8866;M</a
      ><a name="22534"
      > </a
      ><a name="22535" href="StlcProp.html#22535" class="Bound"
      >&#8866;N</a
      ><a name="22537" class="Symbol"
      >)</a
      ><a name="22538"
      > </a
      ><a name="22539" href="Stlc.html#2591" class="InductiveConstructor"
      >&#946;&#120121;&#8321;</a
      ><a name="22542"
      > </a
      ><a name="22543" class="Symbol"
      >=</a
      ><a name="22544"
      > </a
      ><a name="22545" href="StlcProp.html#22532" class="Bound"
      >&#8866;M</a
      ><a name="22547"
      >
</a
      ><a name="22548" href="StlcProp.html#20824" class="Function"
      >preservation</a
      ><a name="22560"
      > </a
      ><a name="22561" class="Symbol"
      >(</a
      ><a name="22562" href="Stlc.html#5151" class="InductiveConstructor"
      >&#120121;-E</a
      ><a name="22565"
      > </a
      ><a name="22566" href="Stlc.html#5115" class="InductiveConstructor"
      >&#120121;-I&#8322;</a
      ><a name="22570"
      > </a
      ><a name="22571" href="StlcProp.html#22571" class="Bound"
      >&#8866;M</a
      ><a name="22573"
      > </a
      ><a name="22574" href="StlcProp.html#22574" class="Bound"
      >&#8866;N</a
      ><a name="22576" class="Symbol"
      >)</a
      ><a name="22577"
      > </a
      ><a name="22578" href="Stlc.html#2643" class="InductiveConstructor"
      >&#946;&#120121;&#8322;</a
      ><a name="22581"
      > </a
      ><a name="22582" class="Symbol"
      >=</a
      ><a name="22583"
      > </a
      ><a name="22584" href="StlcProp.html#22574" class="Bound"
      >&#8866;N</a
      ><a name="22586"
      >
</a
      ><a name="22587" href="StlcProp.html#20824" class="Function"
      >preservation</a
      ><a name="22599"
      > </a
      ><a name="22600" class="Symbol"
      >(</a
      ><a name="22601" href="Stlc.html#5151" class="InductiveConstructor"
      >&#120121;-E</a
      ><a name="22604"
      > </a
      ><a name="22605" href="StlcProp.html#22605" class="Bound"
      >&#8866;L</a
      ><a name="22607"
      > </a
      ><a name="22608" href="StlcProp.html#22608" class="Bound"
      >&#8866;M</a
      ><a name="22610"
      > </a
      ><a name="22611" href="StlcProp.html#22611" class="Bound"
      >&#8866;N</a
      ><a name="22613" class="Symbol"
      >)</a
      ><a name="22614"
      > </a
      ><a name="22615" class="Symbol"
      >(</a
      ><a name="22616" href="Stlc.html#2696" class="InductiveConstructor"
      >&#947;&#120121;</a
      ><a name="22618"
      > </a
      ><a name="22619" href="StlcProp.html#22619" class="Bound"
      >L&#10233;L&#8242;</a
      ><a name="22623" class="Symbol"
      >)</a
      ><a name="22624"
      > </a
      ><a name="22625" class="Keyword"
      >with</a
      ><a name="22629"
      > </a
      ><a name="22630" href="StlcProp.html#20824" class="Function"
      >preservation</a
      ><a name="22642"
      > </a
      ><a name="22643" href="StlcProp.html#22605" class="Bound"
      >&#8866;L</a
      ><a name="22645"
      > </a
      ><a name="22646" href="StlcProp.html#22619" class="Bound"
      >L&#10233;L&#8242;</a
      ><a name="22650"
      >
</a
      ><a name="22651" class="Symbol"
      >...|</a
      ><a name="22655"
      > </a
      ><a name="22656" href="StlcProp.html#22656" class="Bound"
      >&#8866;L&#8242;</a
      ><a name="22659"
      > </a
      ><a name="22660" class="Symbol"
      >=</a
      ><a name="22661"
      > </a
      ><a name="22662" href="Stlc.html#5151" class="InductiveConstructor"
      >&#120121;-E</a
      ><a name="22665"
      > </a
      ><a name="22666" href="StlcProp.html#22656" class="Bound"
      >&#8866;L&#8242;</a
      ><a name="22669"
      > </a
      ><a name="22670" href="StlcProp.html#22608" class="Bound"
      >&#8866;M</a
      ><a name="22672"
      > </a
      ><a name="22673" href="StlcProp.html#22611" class="Bound"
      >&#8866;N</a
      ><a name="22675"
      >

</a
      ><a name="22677" class="Comment"
      >-- Writing out implicit parameters in full</a
      ><a name="22719"
      >
</a
      ><a name="22720" class="Comment"
      >-- preservation (&#8658;-E {&#915;} {&#955;&#7488; x &#8712; A &#8658; N} {M} {.A} {B} (&#8658;-I {.&#915;} {.x} {.N} {.A} {.B} &#8866;N) &#8866;M) (&#946;&#8658; {.x} {.A} {.N} {.M} valueM)</a
      ><a name="22842"
      >
</a
      ><a name="22843" class="Comment"
      >--  =  preservation-[:=] {&#915;} {x} {A} {M} {N} {B} &#8866;M &#8866;N</a
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

