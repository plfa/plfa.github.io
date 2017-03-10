---
title         : "StlcProp: Properties of STLC"
layout        : default
hide-implicit : false
extra-script : [agda-extra-script.html]
extra-style  : [agda-extra-style.html]
permalink     : "sf/StlcProp.html"
---

<!--{% raw %}--><pre class="Agda">
<a name="230" class="Keyword"
      >module</a
      ><a name="236"
      > </a
      ><a name="237" href="StlcProp.html#1" class="Module"
      >StlcProp</a
      ><a name="245"
      > </a
      ><a name="246" class="Keyword"
      >where</a
      >
</pre><!--{% endraw %}-->

<div class="hidden">
<!--{% raw %}--><pre class="Agda">
<a name="298" class="Keyword"
      >open</a
      ><a name="302"
      > </a
      ><a name="303" class="Keyword"
      >import</a
      ><a name="309"
      > </a
      ><a name="310" href="https://agda.github.io/agda-stdlib/Function.html#1" class="Module"
      >Function</a
      ><a name="318"
      > </a
      ><a name="319" class="Keyword"
      >using</a
      ><a name="324"
      > </a
      ><a name="325" class="Symbol"
      >(</a
      ><a name="326" href="https://agda.github.io/agda-stdlib/Function.html#713" class="Function Operator"
      >_&#8728;_</a
      ><a name="329" class="Symbol"
      >)</a
      ><a name="330"
      >
</a
      ><a name="331" class="Keyword"
      >open</a
      ><a name="335"
      > </a
      ><a name="336" class="Keyword"
      >import</a
      ><a name="342"
      > </a
      ><a name="343" href="https://agda.github.io/agda-stdlib/Data.Empty.html#1" class="Module"
      >Data.Empty</a
      ><a name="353"
      > </a
      ><a name="354" class="Keyword"
      >using</a
      ><a name="359"
      > </a
      ><a name="360" class="Symbol"
      >(</a
      ><a name="361" href="https://agda.github.io/agda-stdlib/Data.Empty.html#243" class="Datatype"
      >&#8869;</a
      ><a name="362" class="Symbol"
      >;</a
      ><a name="363"
      > </a
      ><a name="364" href="https://agda.github.io/agda-stdlib/Data.Empty.html#348" class="Function"
      >&#8869;-elim</a
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
      ><a name="384" href="https://agda.github.io/agda-stdlib/Data.Maybe.html#1" class="Module"
      >Data.Maybe</a
      ><a name="394"
      > </a
      ><a name="395" class="Keyword"
      >using</a
      ><a name="400"
      > </a
      ><a name="401" class="Symbol"
      >(</a
      ><a name="402" href="https://agda.github.io/agda-stdlib/Data.Maybe.Base.html#335" class="Datatype"
      >Maybe</a
      ><a name="407" class="Symbol"
      >;</a
      ><a name="408"
      > </a
      ><a name="409" href="https://agda.github.io/agda-stdlib/Data.Maybe.html#1527" class="InductiveConstructor"
      >just</a
      ><a name="413" class="Symbol"
      >;</a
      ><a name="414"
      > </a
      ><a name="415" href="https://agda.github.io/agda-stdlib/Data.Maybe.html#1588" class="InductiveConstructor"
      >nothing</a
      ><a name="422" class="Symbol"
      >)</a
      ><a name="423"
      >
</a
      ><a name="424" class="Keyword"
      >open</a
      ><a name="428"
      > </a
      ><a name="429" class="Keyword"
      >import</a
      ><a name="435"
      > </a
      ><a name="436" href="https://agda.github.io/agda-stdlib/Data.Product.html#1" class="Module"
      >Data.Product</a
      ><a name="448"
      > </a
      ><a name="449" class="Keyword"
      >using</a
      ><a name="454"
      > </a
      ><a name="455" class="Symbol"
      >(</a
      ><a name="456" href="https://agda.github.io/agda-stdlib/Data.Product.html#823" class="Function"
      >&#8707;</a
      ><a name="457" class="Symbol"
      >;</a
      ><a name="458"
      > </a
      ><a name="459" href="https://agda.github.io/agda-stdlib/Data.Product.html#949" class="Function"
      >&#8707;&#8322;</a
      ><a name="461" class="Symbol"
      >;</a
      ><a name="462"
      > </a
      ><a name="463" href="https://agda.github.io/agda-stdlib/Data.Product.html#509" class="InductiveConstructor Operator"
      >_,_</a
      ><a name="466" class="Symbol"
      >;</a
      ><a name="467"
      > </a
      ><a name="468" href="https://agda.github.io/agda-stdlib/Data.Product.html#1621" class="Function Operator"
      >,_</a
      ><a name="470" class="Symbol"
      >)</a
      ><a name="471"
      >
</a
      ><a name="472" class="Keyword"
      >open</a
      ><a name="476"
      > </a
      ><a name="477" class="Keyword"
      >import</a
      ><a name="483"
      > </a
      ><a name="484" href="https://agda.github.io/agda-stdlib/Data.Sum.html#1" class="Module"
      >Data.Sum</a
      ><a name="492"
      > </a
      ><a name="493" class="Keyword"
      >using</a
      ><a name="498"
      > </a
      ><a name="499" class="Symbol"
      >(</a
      ><a name="500" href="https://agda.github.io/agda-stdlib/Data.Sum.html#433" class="Datatype Operator"
      >_&#8846;_</a
      ><a name="503" class="Symbol"
      >;</a
      ><a name="504"
      > </a
      ><a name="505" href="https://agda.github.io/agda-stdlib/Data.Sum.html#489" class="InductiveConstructor"
      >inj&#8321;</a
      ><a name="509" class="Symbol"
      >;</a
      ><a name="510"
      > </a
      ><a name="511" href="https://agda.github.io/agda-stdlib/Data.Sum.html#514" class="InductiveConstructor"
      >inj&#8322;</a
      ><a name="515" class="Symbol"
      >)</a
      ><a name="516"
      >
</a
      ><a name="517" class="Keyword"
      >open</a
      ><a name="521"
      > </a
      ><a name="522" class="Keyword"
      >import</a
      ><a name="528"
      > </a
      ><a name="529" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#1" class="Module"
      >Relation.Nullary</a
      ><a name="545"
      > </a
      ><a name="546" class="Keyword"
      >using</a
      ><a name="551"
      > </a
      ><a name="552" class="Symbol"
      >(</a
      ><a name="553" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#414" class="Function Operator"
      >&#172;_</a
      ><a name="555" class="Symbol"
      >;</a
      ><a name="556"
      > </a
      ><a name="557" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#484" class="Datatype"
      >Dec</a
      ><a name="560" class="Symbol"
      >;</a
      ><a name="561"
      > </a
      ><a name="562" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#520" class="InductiveConstructor"
      >yes</a
      ><a name="565" class="Symbol"
      >;</a
      ><a name="566"
      > </a
      ><a name="567" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#547" class="InductiveConstructor"
      >no</a
      ><a name="569" class="Symbol"
      >)</a
      ><a name="570"
      >
</a
      ><a name="571" class="Keyword"
      >open</a
      ><a name="575"
      > </a
      ><a name="576" class="Keyword"
      >import</a
      ><a name="582"
      > </a
      ><a name="583" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#1" class="Module"
      >Relation.Binary.PropositionalEquality</a
      ><a name="620"
      > </a
      ><a name="621" class="Keyword"
      >using</a
      ><a name="626"
      > </a
      ><a name="627" class="Symbol"
      >(</a
      ><a name="628" href="Agda.Builtin.Equality.html#55" class="Datatype Operator"
      >_&#8801;_</a
      ><a name="631" class="Symbol"
      >;</a
      ><a name="632"
      > </a
      ><a name="633" href="https://agda.github.io/agda-stdlib/Relation.Binary.Core.html#4493" class="Function Operator"
      >_&#8802;_</a
      ><a name="636" class="Symbol"
      >;</a
      ><a name="637"
      > </a
      ><a name="638" href="Agda.Builtin.Equality.html#112" class="InductiveConstructor"
      >refl</a
      ><a name="642" class="Symbol"
      >)</a
      ><a name="643"
      >
</a
      ><a name="644" class="Keyword"
      >open</a
      ><a name="648"
      > </a
      ><a name="649" class="Keyword"
      >import</a
      ><a name="655"
      > </a
      ><a name="656" class="Module"
      >Maps</a
      ><a name="660"
      >
</a
      ><a name="661" class="Keyword"
      >open</a
      ><a name="665"
      > </a
      ><a name="666" class="Keyword"
      >import</a
      ><a name="672"
      > </a
      ><a name="673" href="Stlc.html#1" class="Module"
      >Stlc</a
      >
</pre><!--{% endraw %}-->
</div>

#  Properties of STLC

In this chapter, we develop the fundamental theory of the Simply
Typed Lambda Calculus -- in particular, the type safety
theorem.


## Canonical Forms

As we saw for the simple calculus in the [Stlc](Stlc.html) chapter, the
first step in establishing basic properties of reduction and types
is to identify the possible _canonical forms_ (i.e., well-typed
closed values) belonging to each type.  For $$bool$$, these are the boolean
values $$true$$ and $$false$$.  For arrow types, the canonical forms
are lambda-abstractions.

<!--{% raw %}--><pre class="Agda">
<a name="1259" href="StlcProp.html#1259" class="Function"
      >CanonicalForms</a
      ><a name="1273"
      > </a
      ><a name="1274" class="Symbol"
      >:</a
      ><a name="1275"
      > </a
      ><a name="1276" href="Stlc.html#5755" class="Datatype"
      >Term</a
      ><a name="1280"
      > </a
      ><a name="1281" class="Symbol"
      >&#8594;</a
      ><a name="1282"
      > </a
      ><a name="1283" href="Stlc.html#5588" class="Datatype"
      >Type</a
      ><a name="1287"
      > </a
      ><a name="1288" class="Symbol"
      >&#8594;</a
      ><a name="1289"
      > </a
      ><a name="1290" class="PrimitiveType"
      >Set</a
      ><a name="1293"
      >
</a
      ><a name="1294" href="StlcProp.html#1259" class="Function"
      >CanonicalForms</a
      ><a name="1308"
      > </a
      ><a name="1309" href="StlcProp.html#1309" class="Bound"
      >t</a
      ><a name="1310"
      > </a
      ><a name="1311" href="Stlc.html#5607" class="InductiveConstructor"
      >bool</a
      ><a name="1315"
      >    </a
      ><a name="1319" class="Symbol"
      >=</a
      ><a name="1320"
      > </a
      ><a name="1321" href="StlcProp.html#1309" class="Bound"
      >t</a
      ><a name="1322"
      > </a
      ><a name="1323" href="Agda.Builtin.Equality.html#55" class="Datatype Operator"
      >&#8801;</a
      ><a name="1324"
      > </a
      ><a name="1325" href="Stlc.html#5857" class="InductiveConstructor"
      >true</a
      ><a name="1329"
      > </a
      ><a name="1330" href="https://agda.github.io/agda-stdlib/Data.Sum.html#433" class="Datatype Operator"
      >&#8846;</a
      ><a name="1331"
      > </a
      ><a name="1332" href="StlcProp.html#1309" class="Bound"
      >t</a
      ><a name="1333"
      > </a
      ><a name="1334" href="Agda.Builtin.Equality.html#55" class="Datatype Operator"
      >&#8801;</a
      ><a name="1335"
      > </a
      ><a name="1336" href="Stlc.html#5872" class="InductiveConstructor"
      >false</a
      ><a name="1341"
      >
</a
      ><a name="1342" href="StlcProp.html#1259" class="Function"
      >CanonicalForms</a
      ><a name="1356"
      > </a
      ><a name="1357" href="StlcProp.html#1357" class="Bound"
      >t</a
      ><a name="1358"
      > </a
      ><a name="1359" class="Symbol"
      >(</a
      ><a name="1360" href="StlcProp.html#1360" class="Bound"
      >A</a
      ><a name="1361"
      > </a
      ><a name="1362" href="Stlc.html#5621" class="InductiveConstructor Operator"
      >&#8658;</a
      ><a name="1363"
      > </a
      ><a name="1364" href="StlcProp.html#1364" class="Bound"
      >B</a
      ><a name="1365" class="Symbol"
      >)</a
      ><a name="1366"
      > </a
      ><a name="1367" class="Symbol"
      >=</a
      ><a name="1368"
      > </a
      ><a name="1369" href="https://agda.github.io/agda-stdlib/Data.Product.html#949" class="Function"
      >&#8707;&#8322;</a
      ><a name="1371"
      > </a
      ><a name="1372" class="Symbol"
      >&#955;</a
      ><a name="1373"
      > </a
      ><a name="1374" href="StlcProp.html#1374" class="Bound"
      >x</a
      ><a name="1375"
      > </a
      ><a name="1376" href="StlcProp.html#1376" class="Bound"
      >t&#8242;</a
      ><a name="1378"
      > </a
      ><a name="1379" class="Symbol"
      >&#8594;</a
      ><a name="1380"
      > </a
      ><a name="1381" href="StlcProp.html#1357" class="Bound"
      >t</a
      ><a name="1382"
      > </a
      ><a name="1383" href="Agda.Builtin.Equality.html#55" class="Datatype Operator"
      >&#8801;</a
      ><a name="1384"
      > </a
      ><a name="1385" href="Stlc.html#5823" class="InductiveConstructor"
      >abs</a
      ><a name="1388"
      > </a
      ><a name="1389" href="StlcProp.html#1374" class="Bound"
      >x</a
      ><a name="1390"
      > </a
      ><a name="1391" href="StlcProp.html#1360" class="Bound"
      >A</a
      ><a name="1392"
      > </a
      ><a name="1393" href="StlcProp.html#1376" class="Bound"
      >t&#8242;</a
      ><a name="1395"
      >

</a
      ><a name="1397" href="StlcProp.html#1397" class="Function"
      >canonicalForms</a
      ><a name="1411"
      > </a
      ><a name="1412" class="Symbol"
      >:</a
      ><a name="1413"
      > </a
      ><a name="1414" class="Symbol"
      >&#8704;</a
      ><a name="1415"
      > </a
      ><a name="1416" class="Symbol"
      >{</a
      ><a name="1417" href="StlcProp.html#1417" class="Bound"
      >t</a
      ><a name="1418"
      > </a
      ><a name="1419" href="StlcProp.html#1419" class="Bound"
      >A</a
      ><a name="1420" class="Symbol"
      >}</a
      ><a name="1421"
      > </a
      ><a name="1422" class="Symbol"
      >&#8594;</a
      ><a name="1423"
      > </a
      ><a name="1424" href="Stlc.html#18299" class="Function"
      >&#8709;</a
      ><a name="1425"
      > </a
      ><a name="1426" href="Stlc.html#19231" class="Datatype Operator"
      >&#8866;</a
      ><a name="1427"
      > </a
      ><a name="1428" href="StlcProp.html#1417" class="Bound"
      >t</a
      ><a name="1429"
      > </a
      ><a name="1430" href="Stlc.html#19231" class="Datatype Operator"
      >&#8758;</a
      ><a name="1431"
      > </a
      ><a name="1432" href="StlcProp.html#1419" class="Bound"
      >A</a
      ><a name="1433"
      > </a
      ><a name="1434" class="Symbol"
      >&#8594;</a
      ><a name="1435"
      > </a
      ><a name="1436" href="Stlc.html#9080" class="Datatype"
      >Value</a
      ><a name="1441"
      > </a
      ><a name="1442" href="StlcProp.html#1417" class="Bound"
      >t</a
      ><a name="1443"
      > </a
      ><a name="1444" class="Symbol"
      >&#8594;</a
      ><a name="1445"
      > </a
      ><a name="1446" href="StlcProp.html#1259" class="Function"
      >CanonicalForms</a
      ><a name="1460"
      > </a
      ><a name="1461" href="StlcProp.html#1417" class="Bound"
      >t</a
      ><a name="1462"
      > </a
      ><a name="1463" href="StlcProp.html#1419" class="Bound"
      >A</a
      ><a name="1464"
      >
</a
      ><a name="1465" href="StlcProp.html#1397" class="Function"
      >canonicalForms</a
      ><a name="1479"
      > </a
      ><a name="1480" class="Symbol"
      >(</a
      ><a name="1481" href="Stlc.html#19368" class="InductiveConstructor"
      >abs</a
      ><a name="1484"
      > </a
      ><a name="1485" href="StlcProp.html#1485" class="Bound"
      >t&#8242;</a
      ><a name="1487" class="Symbol"
      >)</a
      ><a name="1488"
      > </a
      ><a name="1489" href="Stlc.html#9107" class="InductiveConstructor"
      >abs</a
      ><a name="1492"
      >   </a
      ><a name="1495" class="Symbol"
      >=</a
      ><a name="1496"
      > </a
      ><a name="1497" class="Symbol"
      >_</a
      ><a name="1498"
      > </a
      ><a name="1499" href="https://agda.github.io/agda-stdlib/Data.Product.html#509" class="InductiveConstructor Operator"
      >,</a
      ><a name="1500"
      > </a
      ><a name="1501" class="Symbol"
      >_</a
      ><a name="1502"
      > </a
      ><a name="1503" href="https://agda.github.io/agda-stdlib/Data.Product.html#509" class="InductiveConstructor Operator"
      >,</a
      ><a name="1504"
      > </a
      ><a name="1505" href="Agda.Builtin.Equality.html#112" class="InductiveConstructor"
      >refl</a
      ><a name="1509"
      >
</a
      ><a name="1510" href="StlcProp.html#1397" class="Function"
      >canonicalForms</a
      ><a name="1524"
      > </a
      ><a name="1525" href="Stlc.html#19618" class="InductiveConstructor"
      >true</a
      ><a name="1529"
      >     </a
      ><a name="1534" href="Stlc.html#9155" class="InductiveConstructor"
      >true</a
      ><a name="1538"
      >  </a
      ><a name="1540" class="Symbol"
      >=</a
      ><a name="1541"
      > </a
      ><a name="1542" href="https://agda.github.io/agda-stdlib/Data.Sum.html#489" class="InductiveConstructor"
      >inj&#8321;</a
      ><a name="1546"
      > </a
      ><a name="1547" href="Agda.Builtin.Equality.html#112" class="InductiveConstructor"
      >refl</a
      ><a name="1551"
      >
</a
      ><a name="1552" href="StlcProp.html#1397" class="Function"
      >canonicalForms</a
      ><a name="1566"
      > </a
      ><a name="1567" href="Stlc.html#19677" class="InductiveConstructor"
      >false</a
      ><a name="1572"
      >    </a
      ><a name="1576" href="Stlc.html#9176" class="InductiveConstructor"
      >false</a
      ><a name="1581"
      > </a
      ><a name="1582" class="Symbol"
      >=</a
      ><a name="1583"
      > </a
      ><a name="1584" href="https://agda.github.io/agda-stdlib/Data.Sum.html#514" class="InductiveConstructor"
      >inj&#8322;</a
      ><a name="1588"
      > </a
      ><a name="1589" href="Agda.Builtin.Equality.html#112" class="InductiveConstructor"
      >refl</a
      >
</pre><!--{% endraw %}-->

## Progress

As before, the _progress_ theorem tells us that closed, well-typed
terms are not stuck: either a well-typed term is a value, or it
can take a reduction step.  The proof is a relatively
straightforward extension of the progress proof we saw in the
[Stlc](Stlc.html) chapter.  We'll give the proof in English first,
then the formal version.

<!--{% raw %}--><pre class="Agda">
<a name="1972" href="StlcProp.html#1972" class="Function"
      >progress</a
      ><a name="1980"
      > </a
      ><a name="1981" class="Symbol"
      >:</a
      ><a name="1982"
      > </a
      ><a name="1983" class="Symbol"
      >&#8704;</a
      ><a name="1984"
      > </a
      ><a name="1985" class="Symbol"
      >{</a
      ><a name="1986" href="StlcProp.html#1986" class="Bound"
      >t</a
      ><a name="1987"
      > </a
      ><a name="1988" href="StlcProp.html#1988" class="Bound"
      >A</a
      ><a name="1989" class="Symbol"
      >}</a
      ><a name="1990"
      > </a
      ><a name="1991" class="Symbol"
      >&#8594;</a
      ><a name="1992"
      > </a
      ><a name="1993" href="Stlc.html#18299" class="Function"
      >&#8709;</a
      ><a name="1994"
      > </a
      ><a name="1995" href="Stlc.html#19231" class="Datatype Operator"
      >&#8866;</a
      ><a name="1996"
      > </a
      ><a name="1997" href="StlcProp.html#1986" class="Bound"
      >t</a
      ><a name="1998"
      > </a
      ><a name="1999" href="Stlc.html#19231" class="Datatype Operator"
      >&#8758;</a
      ><a name="2000"
      > </a
      ><a name="2001" href="StlcProp.html#1988" class="Bound"
      >A</a
      ><a name="2002"
      > </a
      ><a name="2003" class="Symbol"
      >&#8594;</a
      ><a name="2004"
      > </a
      ><a name="2005" href="Stlc.html#9080" class="Datatype"
      >Value</a
      ><a name="2010"
      > </a
      ><a name="2011" href="StlcProp.html#1986" class="Bound"
      >t</a
      ><a name="2012"
      > </a
      ><a name="2013" href="https://agda.github.io/agda-stdlib/Data.Sum.html#433" class="Datatype Operator"
      >&#8846;</a
      ><a name="2014"
      > </a
      ><a name="2015" href="https://agda.github.io/agda-stdlib/Data.Product.html#823" class="Function"
      >&#8707;</a
      ><a name="2016"
      > </a
      ><a name="2017" class="Symbol"
      >&#955;</a
      ><a name="2018"
      > </a
      ><a name="2019" href="StlcProp.html#2019" class="Bound"
      >t&#8242;</a
      ><a name="2021"
      > </a
      ><a name="2022" class="Symbol"
      >&#8594;</a
      ><a name="2023"
      > </a
      ><a name="2024" href="StlcProp.html#1986" class="Bound"
      >t</a
      ><a name="2025"
      > </a
      ><a name="2026" href="Stlc.html#15217" class="Datatype Operator"
      >==&gt;</a
      ><a name="2029"
      > </a
      ><a name="2030" href="StlcProp.html#2019" class="Bound"
      >t&#8242;</a
      >
</pre><!--{% endraw %}-->

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

<!--{% raw %}--><pre class="Agda">
<a name="3731" href="StlcProp.html#1972" class="Function"
      >progress</a
      ><a name="3739"
      > </a
      ><a name="3740" class="Symbol"
      >(</a
      ><a name="3741" href="Stlc.html#19275" class="InductiveConstructor"
      >var</a
      ><a name="3744"
      > </a
      ><a name="3745" href="StlcProp.html#3745" class="Bound"
      >x</a
      ><a name="3746"
      > </a
      ><a name="3747" class="Symbol"
      >())</a
      ><a name="3750"
      >
</a
      ><a name="3751" href="StlcProp.html#1972" class="Function"
      >progress</a
      ><a name="3759"
      > </a
      ><a name="3760" href="Stlc.html#19618" class="InductiveConstructor"
      >true</a
      ><a name="3764"
      >      </a
      ><a name="3770" class="Symbol"
      >=</a
      ><a name="3771"
      > </a
      ><a name="3772" href="https://agda.github.io/agda-stdlib/Data.Sum.html#489" class="InductiveConstructor"
      >inj&#8321;</a
      ><a name="3776"
      > </a
      ><a name="3777" href="Stlc.html#9155" class="InductiveConstructor"
      >true</a
      ><a name="3781"
      >
</a
      ><a name="3782" href="StlcProp.html#1972" class="Function"
      >progress</a
      ><a name="3790"
      > </a
      ><a name="3791" href="Stlc.html#19677" class="InductiveConstructor"
      >false</a
      ><a name="3796"
      >     </a
      ><a name="3801" class="Symbol"
      >=</a
      ><a name="3802"
      > </a
      ><a name="3803" href="https://agda.github.io/agda-stdlib/Data.Sum.html#489" class="InductiveConstructor"
      >inj&#8321;</a
      ><a name="3807"
      > </a
      ><a name="3808" href="Stlc.html#9176" class="InductiveConstructor"
      >false</a
      ><a name="3813"
      >
</a
      ><a name="3814" href="StlcProp.html#1972" class="Function"
      >progress</a
      ><a name="3822"
      > </a
      ><a name="3823" class="Symbol"
      >(</a
      ><a name="3824" href="Stlc.html#19368" class="InductiveConstructor"
      >abs</a
      ><a name="3827"
      > </a
      ><a name="3828" href="StlcProp.html#3828" class="Bound"
      >t&#8758;A</a
      ><a name="3831" class="Symbol"
      >)</a
      ><a name="3832"
      > </a
      ><a name="3833" class="Symbol"
      >=</a
      ><a name="3834"
      > </a
      ><a name="3835" href="https://agda.github.io/agda-stdlib/Data.Sum.html#489" class="InductiveConstructor"
      >inj&#8321;</a
      ><a name="3839"
      > </a
      ><a name="3840" href="Stlc.html#9107" class="InductiveConstructor"
      >abs</a
      ><a name="3843"
      >
</a
      ><a name="3844" href="StlcProp.html#1972" class="Function"
      >progress</a
      ><a name="3852"
      > </a
      ><a name="3853" class="Symbol"
      >(</a
      ><a name="3854" href="Stlc.html#19484" class="InductiveConstructor"
      >app</a
      ><a name="3857"
      > </a
      ><a name="3858" href="StlcProp.html#3858" class="Bound"
      >t&#8321;&#8758;A&#8658;B</a
      ><a name="3864"
      > </a
      ><a name="3865" href="StlcProp.html#3865" class="Bound"
      >t&#8322;&#8758;B</a
      ><a name="3869" class="Symbol"
      >)</a
      ><a name="3870"
      >
    </a
      ><a name="3875" class="Keyword"
      >with</a
      ><a name="3879"
      > </a
      ><a name="3880" href="StlcProp.html#1972" class="Function"
      >progress</a
      ><a name="3888"
      > </a
      ><a name="3889" href="StlcProp.html#3858" class="Bound"
      >t&#8321;&#8758;A&#8658;B</a
      ><a name="3895"
      >
</a
      ><a name="3896" class="Symbol"
      >...</a
      ><a name="3899"
      > </a
      ><a name="3900" class="Symbol"
      >|</a
      ><a name="3901"
      > </a
      ><a name="3902" href="https://agda.github.io/agda-stdlib/Data.Sum.html#514" class="InductiveConstructor"
      >inj&#8322;</a
      ><a name="3906"
      > </a
      ><a name="3907" class="Symbol"
      >(_</a
      ><a name="3909"
      > </a
      ><a name="3910" href="https://agda.github.io/agda-stdlib/Data.Product.html#509" class="InductiveConstructor Operator"
      >,</a
      ><a name="3911"
      > </a
      ><a name="3912" href="StlcProp.html#3912" class="Bound"
      >t&#8321;&#8658;t&#8321;&#8242;</a
      ><a name="3918" class="Symbol"
      >)</a
      ><a name="3919"
      > </a
      ><a name="3920" class="Symbol"
      >=</a
      ><a name="3921"
      > </a
      ><a name="3922" href="https://agda.github.io/agda-stdlib/Data.Sum.html#514" class="InductiveConstructor"
      >inj&#8322;</a
      ><a name="3926"
      > </a
      ><a name="3927" class="Symbol"
      >(_</a
      ><a name="3929"
      > </a
      ><a name="3930" href="https://agda.github.io/agda-stdlib/Data.Product.html#509" class="InductiveConstructor Operator"
      >,</a
      ><a name="3931"
      > </a
      ><a name="3932" href="Stlc.html#15342" class="InductiveConstructor"
      >app1</a
      ><a name="3936"
      > </a
      ><a name="3937" href="StlcProp.html#3912" class="Bound"
      >t&#8321;&#8658;t&#8321;&#8242;</a
      ><a name="3943" class="Symbol"
      >)</a
      ><a name="3944"
      >
</a
      ><a name="3945" class="Symbol"
      >...</a
      ><a name="3948"
      > </a
      ><a name="3949" class="Symbol"
      >|</a
      ><a name="3950"
      > </a
      ><a name="3951" href="https://agda.github.io/agda-stdlib/Data.Sum.html#489" class="InductiveConstructor"
      >inj&#8321;</a
      ><a name="3955"
      > </a
      ><a name="3956" href="StlcProp.html#3956" class="Bound"
      >v&#8321;</a
      ><a name="3958"
      >
    </a
      ><a name="3963" class="Keyword"
      >with</a
      ><a name="3967"
      > </a
      ><a name="3968" href="StlcProp.html#1972" class="Function"
      >progress</a
      ><a name="3976"
      > </a
      ><a name="3977" href="StlcProp.html#3865" class="Bound"
      >t&#8322;&#8758;B</a
      ><a name="3981"
      >
</a
      ><a name="3982" class="Symbol"
      >...</a
      ><a name="3985"
      > </a
      ><a name="3986" class="Symbol"
      >|</a
      ><a name="3987"
      > </a
      ><a name="3988" href="https://agda.github.io/agda-stdlib/Data.Sum.html#514" class="InductiveConstructor"
      >inj&#8322;</a
      ><a name="3992"
      > </a
      ><a name="3993" class="Symbol"
      >(_</a
      ><a name="3995"
      > </a
      ><a name="3996" href="https://agda.github.io/agda-stdlib/Data.Product.html#509" class="InductiveConstructor Operator"
      >,</a
      ><a name="3997"
      > </a
      ><a name="3998" href="StlcProp.html#3998" class="Bound"
      >t&#8322;&#8658;t&#8322;&#8242;</a
      ><a name="4004" class="Symbol"
      >)</a
      ><a name="4005"
      > </a
      ><a name="4006" class="Symbol"
      >=</a
      ><a name="4007"
      > </a
      ><a name="4008" href="https://agda.github.io/agda-stdlib/Data.Sum.html#514" class="InductiveConstructor"
      >inj&#8322;</a
      ><a name="4012"
      > </a
      ><a name="4013" class="Symbol"
      >(_</a
      ><a name="4015"
      > </a
      ><a name="4016" href="https://agda.github.io/agda-stdlib/Data.Product.html#509" class="InductiveConstructor Operator"
      >,</a
      ><a name="4017"
      > </a
      ><a name="4018" href="Stlc.html#15419" class="InductiveConstructor"
      >app2</a
      ><a name="4022"
      > </a
      ><a name="4023" href="StlcProp.html#3956" class="Bound"
      >v&#8321;</a
      ><a name="4025"
      > </a
      ><a name="4026" href="StlcProp.html#3998" class="Bound"
      >t&#8322;&#8658;t&#8322;&#8242;</a
      ><a name="4032" class="Symbol"
      >)</a
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
      ><a name="4040" href="https://agda.github.io/agda-stdlib/Data.Sum.html#489" class="InductiveConstructor"
      >inj&#8321;</a
      ><a name="4044"
      > </a
      ><a name="4045" href="StlcProp.html#4045" class="Bound"
      >v&#8322;</a
      ><a name="4047"
      >
    </a
      ><a name="4052" class="Keyword"
      >with</a
      ><a name="4056"
      > </a
      ><a name="4057" href="StlcProp.html#1397" class="Function"
      >canonicalForms</a
      ><a name="4071"
      > </a
      ><a name="4072" href="StlcProp.html#3858" class="Bound"
      >t&#8321;&#8758;A&#8658;B</a
      ><a name="4078"
      > </a
      ><a name="4079" href="StlcProp.html#3956" class="Bound"
      >v&#8321;</a
      ><a name="4081"
      >
</a
      ><a name="4082" class="Symbol"
      >...</a
      ><a name="4085"
      > </a
      ><a name="4086" class="Symbol"
      >|</a
      ><a name="4087"
      > </a
      ><a name="4088" class="Symbol"
      >(_</a
      ><a name="4090"
      > </a
      ><a name="4091" href="https://agda.github.io/agda-stdlib/Data.Product.html#509" class="InductiveConstructor Operator"
      >,</a
      ><a name="4092"
      > </a
      ><a name="4093" class="Symbol"
      >_</a
      ><a name="4094"
      > </a
      ><a name="4095" href="https://agda.github.io/agda-stdlib/Data.Product.html#509" class="InductiveConstructor Operator"
      >,</a
      ><a name="4096"
      > </a
      ><a name="4097" href="Agda.Builtin.Equality.html#112" class="InductiveConstructor"
      >refl</a
      ><a name="4101" class="Symbol"
      >)</a
      ><a name="4102"
      > </a
      ><a name="4103" class="Symbol"
      >=</a
      ><a name="4104"
      > </a
      ><a name="4105" href="https://agda.github.io/agda-stdlib/Data.Sum.html#514" class="InductiveConstructor"
      >inj&#8322;</a
      ><a name="4109"
      > </a
      ><a name="4110" class="Symbol"
      >(_</a
      ><a name="4112"
      > </a
      ><a name="4113" href="https://agda.github.io/agda-stdlib/Data.Product.html#509" class="InductiveConstructor Operator"
      >,</a
      ><a name="4114"
      > </a
      ><a name="4115" href="Stlc.html#15251" class="InductiveConstructor"
      >red</a
      ><a name="4118"
      > </a
      ><a name="4119" href="StlcProp.html#4045" class="Bound"
      >v&#8322;</a
      ><a name="4121" class="Symbol"
      >)</a
      ><a name="4122"
      >
</a
      ><a name="4123" href="StlcProp.html#1972" class="Function"
      >progress</a
      ><a name="4131"
      > </a
      ><a name="4132" class="Symbol"
      >(</a
      ><a name="4133" href="Stlc.html#19736" class="InductiveConstructor Operator"
      >if</a
      ><a name="4135"
      > </a
      ><a name="4136" href="StlcProp.html#4136" class="Bound"
      >t&#8321;&#8758;bool</a
      ><a name="4143"
      > </a
      ><a name="4144" href="Stlc.html#19736" class="InductiveConstructor Operator"
      >then</a
      ><a name="4148"
      > </a
      ><a name="4149" href="StlcProp.html#4149" class="Bound"
      >t&#8322;&#8758;A</a
      ><a name="4153"
      > </a
      ><a name="4154" href="Stlc.html#19736" class="InductiveConstructor Operator"
      >else</a
      ><a name="4158"
      > </a
      ><a name="4159" href="StlcProp.html#4159" class="Bound"
      >t&#8323;&#8758;A</a
      ><a name="4163" class="Symbol"
      >)</a
      ><a name="4164"
      >
    </a
      ><a name="4169" class="Keyword"
      >with</a
      ><a name="4173"
      > </a
      ><a name="4174" href="StlcProp.html#1972" class="Function"
      >progress</a
      ><a name="4182"
      > </a
      ><a name="4183" href="StlcProp.html#4136" class="Bound"
      >t&#8321;&#8758;bool</a
      ><a name="4190"
      >
</a
      ><a name="4191" class="Symbol"
      >...</a
      ><a name="4194"
      > </a
      ><a name="4195" class="Symbol"
      >|</a
      ><a name="4196"
      > </a
      ><a name="4197" href="https://agda.github.io/agda-stdlib/Data.Sum.html#514" class="InductiveConstructor"
      >inj&#8322;</a
      ><a name="4201"
      > </a
      ><a name="4202" class="Symbol"
      >(_</a
      ><a name="4204"
      > </a
      ><a name="4205" href="https://agda.github.io/agda-stdlib/Data.Product.html#509" class="InductiveConstructor Operator"
      >,</a
      ><a name="4206"
      > </a
      ><a name="4207" href="StlcProp.html#4207" class="Bound"
      >t&#8321;&#8658;t&#8321;&#8242;</a
      ><a name="4213" class="Symbol"
      >)</a
      ><a name="4214"
      > </a
      ><a name="4215" class="Symbol"
      >=</a
      ><a name="4216"
      > </a
      ><a name="4217" href="https://agda.github.io/agda-stdlib/Data.Sum.html#514" class="InductiveConstructor"
      >inj&#8322;</a
      ><a name="4221"
      > </a
      ><a name="4222" class="Symbol"
      >(_</a
      ><a name="4224"
      > </a
      ><a name="4225" href="https://agda.github.io/agda-stdlib/Data.Product.html#509" class="InductiveConstructor Operator"
      >,</a
      ><a name="4226"
      > </a
      ><a name="4227" href="Stlc.html#15516" class="InductiveConstructor"
      >if</a
      ><a name="4229"
      > </a
      ><a name="4230" href="StlcProp.html#4207" class="Bound"
      >t&#8321;&#8658;t&#8321;&#8242;</a
      ><a name="4236" class="Symbol"
      >)</a
      ><a name="4237"
      >
</a
      ><a name="4238" class="Symbol"
      >...</a
      ><a name="4241"
      > </a
      ><a name="4242" class="Symbol"
      >|</a
      ><a name="4243"
      > </a
      ><a name="4244" href="https://agda.github.io/agda-stdlib/Data.Sum.html#489" class="InductiveConstructor"
      >inj&#8321;</a
      ><a name="4248"
      > </a
      ><a name="4249" href="StlcProp.html#4249" class="Bound"
      >v&#8321;</a
      ><a name="4251"
      >
    </a
      ><a name="4256" class="Keyword"
      >with</a
      ><a name="4260"
      > </a
      ><a name="4261" href="StlcProp.html#1397" class="Function"
      >canonicalForms</a
      ><a name="4275"
      > </a
      ><a name="4276" href="StlcProp.html#4136" class="Bound"
      >t&#8321;&#8758;bool</a
      ><a name="4283"
      > </a
      ><a name="4284" href="StlcProp.html#4249" class="Bound"
      >v&#8321;</a
      ><a name="4286"
      >
</a
      ><a name="4287" class="Symbol"
      >...</a
      ><a name="4290"
      > </a
      ><a name="4291" class="Symbol"
      >|</a
      ><a name="4292"
      > </a
      ><a name="4293" href="https://agda.github.io/agda-stdlib/Data.Sum.html#489" class="InductiveConstructor"
      >inj&#8321;</a
      ><a name="4297"
      > </a
      ><a name="4298" href="Agda.Builtin.Equality.html#112" class="InductiveConstructor"
      >refl</a
      ><a name="4302"
      > </a
      ><a name="4303" class="Symbol"
      >=</a
      ><a name="4304"
      > </a
      ><a name="4305" href="https://agda.github.io/agda-stdlib/Data.Sum.html#514" class="InductiveConstructor"
      >inj&#8322;</a
      ><a name="4309"
      > </a
      ><a name="4310" class="Symbol"
      >(_</a
      ><a name="4312"
      > </a
      ><a name="4313" href="https://agda.github.io/agda-stdlib/Data.Product.html#509" class="InductiveConstructor Operator"
      >,</a
      ><a name="4314"
      > </a
      ><a name="4315" href="Stlc.html#15617" class="InductiveConstructor"
      >iftrue</a
      ><a name="4321" class="Symbol"
      >)</a
      ><a name="4322"
      >
</a
      ><a name="4323" class="Symbol"
      >...</a
      ><a name="4326"
      > </a
      ><a name="4327" class="Symbol"
      >|</a
      ><a name="4328"
      > </a
      ><a name="4329" href="https://agda.github.io/agda-stdlib/Data.Sum.html#514" class="InductiveConstructor"
      >inj&#8322;</a
      ><a name="4333"
      > </a
      ><a name="4334" href="Agda.Builtin.Equality.html#112" class="InductiveConstructor"
      >refl</a
      ><a name="4338"
      > </a
      ><a name="4339" class="Symbol"
      >=</a
      ><a name="4340"
      > </a
      ><a name="4341" href="https://agda.github.io/agda-stdlib/Data.Sum.html#514" class="InductiveConstructor"
      >inj&#8322;</a
      ><a name="4345"
      > </a
      ><a name="4346" class="Symbol"
      >(_</a
      ><a name="4348"
      > </a
      ><a name="4349" href="https://agda.github.io/agda-stdlib/Data.Product.html#509" class="InductiveConstructor Operator"
      >,</a
      ><a name="4350"
      > </a
      ><a name="4351" href="Stlc.html#15677" class="InductiveConstructor"
      >iffalse</a
      ><a name="4358" class="Symbol"
      >)</a
      >
</pre><!--{% endraw %}-->

#### Exercise: 3 stars, optional (progress_from_term_ind)
Show that progress can also be proved by induction on terms
instead of induction on typing derivations.

<!--{% raw %}--><pre class="Agda">
<a name="4548" class="Keyword"
      >postulate</a
      ><a name="4557"
      >
  </a
      ><a name="4560" href="StlcProp.html#4560" class="Postulate"
      >progress&#8242;</a
      ><a name="4569"
      > </a
      ><a name="4570" class="Symbol"
      >:</a
      ><a name="4571"
      > </a
      ><a name="4572" class="Symbol"
      >&#8704;</a
      ><a name="4573"
      > </a
      ><a name="4574" class="Symbol"
      >{</a
      ><a name="4575" href="StlcProp.html#4575" class="Bound"
      >t</a
      ><a name="4576"
      > </a
      ><a name="4577" href="StlcProp.html#4577" class="Bound"
      >A</a
      ><a name="4578" class="Symbol"
      >}</a
      ><a name="4579"
      > </a
      ><a name="4580" class="Symbol"
      >&#8594;</a
      ><a name="4581"
      > </a
      ><a name="4582" href="Stlc.html#18299" class="Function"
      >&#8709;</a
      ><a name="4583"
      > </a
      ><a name="4584" href="Stlc.html#19231" class="Datatype Operator"
      >&#8866;</a
      ><a name="4585"
      > </a
      ><a name="4586" href="StlcProp.html#4575" class="Bound"
      >t</a
      ><a name="4587"
      > </a
      ><a name="4588" href="Stlc.html#19231" class="Datatype Operator"
      >&#8758;</a
      ><a name="4589"
      > </a
      ><a name="4590" href="StlcProp.html#4577" class="Bound"
      >A</a
      ><a name="4591"
      > </a
      ><a name="4592" class="Symbol"
      >&#8594;</a
      ><a name="4593"
      > </a
      ><a name="4594" href="Stlc.html#9080" class="Datatype"
      >Value</a
      ><a name="4599"
      > </a
      ><a name="4600" href="StlcProp.html#4575" class="Bound"
      >t</a
      ><a name="4601"
      > </a
      ><a name="4602" href="https://agda.github.io/agda-stdlib/Data.Sum.html#433" class="Datatype Operator"
      >&#8846;</a
      ><a name="4603"
      > </a
      ><a name="4604" href="https://agda.github.io/agda-stdlib/Data.Product.html#823" class="Function"
      >&#8707;</a
      ><a name="4605"
      > </a
      ><a name="4606" class="Symbol"
      >&#955;</a
      ><a name="4607"
      > </a
      ><a name="4608" href="StlcProp.html#4608" class="Bound"
      >t&#8242;</a
      ><a name="4610"
      > </a
      ><a name="4611" class="Symbol"
      >&#8594;</a
      ><a name="4612"
      > </a
      ><a name="4613" href="StlcProp.html#4575" class="Bound"
      >t</a
      ><a name="4614"
      > </a
      ><a name="4615" href="Stlc.html#15217" class="Datatype Operator"
      >==&gt;</a
      ><a name="4618"
      > </a
      ><a name="4619" href="StlcProp.html#4608" class="Bound"
      >t&#8242;</a
      >
</pre><!--{% endraw %}-->

## Preservation

The other half of the type soundness property is the preservation
of types during reduction.  For this, we need to develop some
technical machinery for reasoning about variables and
substitution.  Working from top to bottom (from the high-level
property we are actually interested in to the lowest-level
technical lemmas that are needed by various cases of the more
interesting proofs), the story goes like this:

  - The _preservation theorem_ is proved by induction on a typing
    derivation, pretty much as we did in the [Stlc](Stlc.html)
    chapter.  The one case that is significantly different is the
    one for the $$red$$ rule, whose definition uses the substitution
    operation.  To see that this step preserves typing, we need to
    know that the substitution itself does.  So we prove a...

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
    under "inessential changes" to the context $$\Gamma$$ -- in
    particular, changes that do not affect any of the free
    variables of the term.  And finally, for this, we need a
    careful definition of...

  - the _free variables_ of a term -- i.e., those variables
    mentioned in a term and not in the scope of an enclosing
    function abstraction binding a variable of the same name.

To make Agda happy, we need to formalize the story in the opposite
order...


### Free Occurrences

A variable $$x$$ _appears free in_ a term _t_ if $$t$$ contains some
occurrence of $$x$$ that is not under an abstraction labeled $$x$$.
For example:

  - $$y$$ appears free, but $$x$$ does not, in $$\lambda x : A\to B. x\;y$$
  - both $$x$$ and $$y$$ appear free in $$(\lambda x:A\to B. x\;y) x$$
  - no variables appear free in $$\lambda x:A\to B. \lambda y:A. x\;y$$

Formally:

<!--{% raw %}--><pre class="Agda">
<a name="7042" class="Keyword"
      >data</a
      ><a name="7046"
      > </a
      ><a name="7047" href="StlcProp.html#7047" class="Datatype Operator"
      >_FreeIn_</a
      ><a name="7055"
      > </a
      ><a name="7056" class="Symbol"
      >(</a
      ><a name="7057" href="StlcProp.html#7057" class="Bound"
      >x</a
      ><a name="7058"
      > </a
      ><a name="7059" class="Symbol"
      >:</a
      ><a name="7060"
      > </a
      ><a name="7061" href="Maps.html#2400" class="Datatype"
      >Id</a
      ><a name="7063" class="Symbol"
      >)</a
      ><a name="7064"
      > </a
      ><a name="7065" class="Symbol"
      >:</a
      ><a name="7066"
      > </a
      ><a name="7067" href="Stlc.html#5755" class="Datatype"
      >Term</a
      ><a name="7071"
      > </a
      ><a name="7072" class="Symbol"
      >&#8594;</a
      ><a name="7073"
      > </a
      ><a name="7074" class="PrimitiveType"
      >Set</a
      ><a name="7077"
      > </a
      ><a name="7078" class="Keyword"
      >where</a
      ><a name="7083"
      >
  </a
      ><a name="7086" href="StlcProp.html#7086" class="InductiveConstructor"
      >var</a
      ><a name="7089"
      >  </a
      ><a name="7091" class="Symbol"
      >:</a
      ><a name="7092"
      > </a
      ><a name="7093" href="StlcProp.html#7057" class="Bound"
      >x</a
      ><a name="7094"
      > </a
      ><a name="7095" href="StlcProp.html#7047" class="Datatype Operator"
      >FreeIn</a
      ><a name="7101"
      > </a
      ><a name="7102" href="Stlc.html#5774" class="InductiveConstructor"
      >var</a
      ><a name="7105"
      > </a
      ><a name="7106" href="StlcProp.html#7057" class="Bound"
      >x</a
      ><a name="7107"
      >
  </a
      ><a name="7110" href="StlcProp.html#7110" class="InductiveConstructor"
      >abs</a
      ><a name="7113"
      >  </a
      ><a name="7115" class="Symbol"
      >:</a
      ><a name="7116"
      > </a
      ><a name="7117" class="Symbol"
      >&#8704;</a
      ><a name="7118"
      > </a
      ><a name="7119" class="Symbol"
      >{</a
      ><a name="7120" href="StlcProp.html#7120" class="Bound"
      >y</a
      ><a name="7121"
      > </a
      ><a name="7122" href="StlcProp.html#7122" class="Bound"
      >A</a
      ><a name="7123"
      > </a
      ><a name="7124" href="StlcProp.html#7124" class="Bound"
      >t</a
      ><a name="7125" class="Symbol"
      >}</a
      ><a name="7126"
      > </a
      ><a name="7127" class="Symbol"
      >&#8594;</a
      ><a name="7128"
      > </a
      ><a name="7129" href="StlcProp.html#7120" class="Bound"
      >y</a
      ><a name="7130"
      > </a
      ><a name="7131" href="https://agda.github.io/agda-stdlib/Relation.Binary.Core.html#4493" class="Function Operator"
      >&#8802;</a
      ><a name="7132"
      > </a
      ><a name="7133" href="StlcProp.html#7057" class="Bound"
      >x</a
      ><a name="7134"
      > </a
      ><a name="7135" class="Symbol"
      >&#8594;</a
      ><a name="7136"
      > </a
      ><a name="7137" href="StlcProp.html#7057" class="Bound"
      >x</a
      ><a name="7138"
      > </a
      ><a name="7139" href="StlcProp.html#7047" class="Datatype Operator"
      >FreeIn</a
      ><a name="7145"
      > </a
      ><a name="7146" href="StlcProp.html#7124" class="Bound"
      >t</a
      ><a name="7147"
      > </a
      ><a name="7148" class="Symbol"
      >&#8594;</a
      ><a name="7149"
      > </a
      ><a name="7150" href="StlcProp.html#7057" class="Bound"
      >x</a
      ><a name="7151"
      > </a
      ><a name="7152" href="StlcProp.html#7047" class="Datatype Operator"
      >FreeIn</a
      ><a name="7158"
      > </a
      ><a name="7159" href="Stlc.html#5823" class="InductiveConstructor"
      >abs</a
      ><a name="7162"
      > </a
      ><a name="7163" href="StlcProp.html#7120" class="Bound"
      >y</a
      ><a name="7164"
      > </a
      ><a name="7165" href="StlcProp.html#7122" class="Bound"
      >A</a
      ><a name="7166"
      > </a
      ><a name="7167" href="StlcProp.html#7124" class="Bound"
      >t</a
      ><a name="7168"
      >
  </a
      ><a name="7171" href="StlcProp.html#7171" class="InductiveConstructor"
      >app1</a
      ><a name="7175"
      > </a
      ><a name="7176" class="Symbol"
      >:</a
      ><a name="7177"
      > </a
      ><a name="7178" class="Symbol"
      >&#8704;</a
      ><a name="7179"
      > </a
      ><a name="7180" class="Symbol"
      >{</a
      ><a name="7181" href="StlcProp.html#7181" class="Bound"
      >t&#8321;</a
      ><a name="7183"
      > </a
      ><a name="7184" href="StlcProp.html#7184" class="Bound"
      >t&#8322;</a
      ><a name="7186" class="Symbol"
      >}</a
      ><a name="7187"
      > </a
      ><a name="7188" class="Symbol"
      >&#8594;</a
      ><a name="7189"
      > </a
      ><a name="7190" href="StlcProp.html#7057" class="Bound"
      >x</a
      ><a name="7191"
      > </a
      ><a name="7192" href="StlcProp.html#7047" class="Datatype Operator"
      >FreeIn</a
      ><a name="7198"
      > </a
      ><a name="7199" href="StlcProp.html#7181" class="Bound"
      >t&#8321;</a
      ><a name="7201"
      > </a
      ><a name="7202" class="Symbol"
      >&#8594;</a
      ><a name="7203"
      > </a
      ><a name="7204" href="StlcProp.html#7057" class="Bound"
      >x</a
      ><a name="7205"
      > </a
      ><a name="7206" href="StlcProp.html#7047" class="Datatype Operator"
      >FreeIn</a
      ><a name="7212"
      > </a
      ><a name="7213" href="Stlc.html#5794" class="InductiveConstructor"
      >app</a
      ><a name="7216"
      > </a
      ><a name="7217" href="StlcProp.html#7181" class="Bound"
      >t&#8321;</a
      ><a name="7219"
      > </a
      ><a name="7220" href="StlcProp.html#7184" class="Bound"
      >t&#8322;</a
      ><a name="7222"
      >
  </a
      ><a name="7225" href="StlcProp.html#7225" class="InductiveConstructor"
      >app2</a
      ><a name="7229"
      > </a
      ><a name="7230" class="Symbol"
      >:</a
      ><a name="7231"
      > </a
      ><a name="7232" class="Symbol"
      >&#8704;</a
      ><a name="7233"
      > </a
      ><a name="7234" class="Symbol"
      >{</a
      ><a name="7235" href="StlcProp.html#7235" class="Bound"
      >t&#8321;</a
      ><a name="7237"
      > </a
      ><a name="7238" href="StlcProp.html#7238" class="Bound"
      >t&#8322;</a
      ><a name="7240" class="Symbol"
      >}</a
      ><a name="7241"
      > </a
      ><a name="7242" class="Symbol"
      >&#8594;</a
      ><a name="7243"
      > </a
      ><a name="7244" href="StlcProp.html#7057" class="Bound"
      >x</a
      ><a name="7245"
      > </a
      ><a name="7246" href="StlcProp.html#7047" class="Datatype Operator"
      >FreeIn</a
      ><a name="7252"
      > </a
      ><a name="7253" href="StlcProp.html#7238" class="Bound"
      >t&#8322;</a
      ><a name="7255"
      > </a
      ><a name="7256" class="Symbol"
      >&#8594;</a
      ><a name="7257"
      > </a
      ><a name="7258" href="StlcProp.html#7057" class="Bound"
      >x</a
      ><a name="7259"
      > </a
      ><a name="7260" href="StlcProp.html#7047" class="Datatype Operator"
      >FreeIn</a
      ><a name="7266"
      > </a
      ><a name="7267" href="Stlc.html#5794" class="InductiveConstructor"
      >app</a
      ><a name="7270"
      > </a
      ><a name="7271" href="StlcProp.html#7235" class="Bound"
      >t&#8321;</a
      ><a name="7273"
      > </a
      ><a name="7274" href="StlcProp.html#7238" class="Bound"
      >t&#8322;</a
      ><a name="7276"
      >
  </a
      ><a name="7279" href="StlcProp.html#7279" class="InductiveConstructor"
      >if1</a
      ><a name="7282"
      >  </a
      ><a name="7284" class="Symbol"
      >:</a
      ><a name="7285"
      > </a
      ><a name="7286" class="Symbol"
      >&#8704;</a
      ><a name="7287"
      > </a
      ><a name="7288" class="Symbol"
      >{</a
      ><a name="7289" href="StlcProp.html#7289" class="Bound"
      >t&#8321;</a
      ><a name="7291"
      > </a
      ><a name="7292" href="StlcProp.html#7292" class="Bound"
      >t&#8322;</a
      ><a name="7294"
      > </a
      ><a name="7295" href="StlcProp.html#7295" class="Bound"
      >t&#8323;</a
      ><a name="7297" class="Symbol"
      >}</a
      ><a name="7298"
      > </a
      ><a name="7299" class="Symbol"
      >&#8594;</a
      ><a name="7300"
      > </a
      ><a name="7301" href="StlcProp.html#7057" class="Bound"
      >x</a
      ><a name="7302"
      > </a
      ><a name="7303" href="StlcProp.html#7047" class="Datatype Operator"
      >FreeIn</a
      ><a name="7309"
      > </a
      ><a name="7310" href="StlcProp.html#7289" class="Bound"
      >t&#8321;</a
      ><a name="7312"
      > </a
      ><a name="7313" class="Symbol"
      >&#8594;</a
      ><a name="7314"
      > </a
      ><a name="7315" href="StlcProp.html#7057" class="Bound"
      >x</a
      ><a name="7316"
      > </a
      ><a name="7317" href="StlcProp.html#7047" class="Datatype Operator"
      >FreeIn</a
      ><a name="7323"
      > </a
      ><a name="7324" class="Symbol"
      >(</a
      ><a name="7325" href="Stlc.html#5887" class="InductiveConstructor Operator"
      >if</a
      ><a name="7327"
      > </a
      ><a name="7328" href="StlcProp.html#7289" class="Bound"
      >t&#8321;</a
      ><a name="7330"
      > </a
      ><a name="7331" href="Stlc.html#5887" class="InductiveConstructor Operator"
      >then</a
      ><a name="7335"
      > </a
      ><a name="7336" href="StlcProp.html#7292" class="Bound"
      >t&#8322;</a
      ><a name="7338"
      > </a
      ><a name="7339" href="Stlc.html#5887" class="InductiveConstructor Operator"
      >else</a
      ><a name="7343"
      > </a
      ><a name="7344" href="StlcProp.html#7295" class="Bound"
      >t&#8323;</a
      ><a name="7346" class="Symbol"
      >)</a
      ><a name="7347"
      >
  </a
      ><a name="7350" href="StlcProp.html#7350" class="InductiveConstructor"
      >if2</a
      ><a name="7353"
      >  </a
      ><a name="7355" class="Symbol"
      >:</a
      ><a name="7356"
      > </a
      ><a name="7357" class="Symbol"
      >&#8704;</a
      ><a name="7358"
      > </a
      ><a name="7359" class="Symbol"
      >{</a
      ><a name="7360" href="StlcProp.html#7360" class="Bound"
      >t&#8321;</a
      ><a name="7362"
      > </a
      ><a name="7363" href="StlcProp.html#7363" class="Bound"
      >t&#8322;</a
      ><a name="7365"
      > </a
      ><a name="7366" href="StlcProp.html#7366" class="Bound"
      >t&#8323;</a
      ><a name="7368" class="Symbol"
      >}</a
      ><a name="7369"
      > </a
      ><a name="7370" class="Symbol"
      >&#8594;</a
      ><a name="7371"
      > </a
      ><a name="7372" href="StlcProp.html#7057" class="Bound"
      >x</a
      ><a name="7373"
      > </a
      ><a name="7374" href="StlcProp.html#7047" class="Datatype Operator"
      >FreeIn</a
      ><a name="7380"
      > </a
      ><a name="7381" href="StlcProp.html#7363" class="Bound"
      >t&#8322;</a
      ><a name="7383"
      > </a
      ><a name="7384" class="Symbol"
      >&#8594;</a
      ><a name="7385"
      > </a
      ><a name="7386" href="StlcProp.html#7057" class="Bound"
      >x</a
      ><a name="7387"
      > </a
      ><a name="7388" href="StlcProp.html#7047" class="Datatype Operator"
      >FreeIn</a
      ><a name="7394"
      > </a
      ><a name="7395" class="Symbol"
      >(</a
      ><a name="7396" href="Stlc.html#5887" class="InductiveConstructor Operator"
      >if</a
      ><a name="7398"
      > </a
      ><a name="7399" href="StlcProp.html#7360" class="Bound"
      >t&#8321;</a
      ><a name="7401"
      > </a
      ><a name="7402" href="Stlc.html#5887" class="InductiveConstructor Operator"
      >then</a
      ><a name="7406"
      > </a
      ><a name="7407" href="StlcProp.html#7363" class="Bound"
      >t&#8322;</a
      ><a name="7409"
      > </a
      ><a name="7410" href="Stlc.html#5887" class="InductiveConstructor Operator"
      >else</a
      ><a name="7414"
      > </a
      ><a name="7415" href="StlcProp.html#7366" class="Bound"
      >t&#8323;</a
      ><a name="7417" class="Symbol"
      >)</a
      ><a name="7418"
      >
  </a
      ><a name="7421" href="StlcProp.html#7421" class="InductiveConstructor"
      >if3</a
      ><a name="7424"
      >  </a
      ><a name="7426" class="Symbol"
      >:</a
      ><a name="7427"
      > </a
      ><a name="7428" class="Symbol"
      >&#8704;</a
      ><a name="7429"
      > </a
      ><a name="7430" class="Symbol"
      >{</a
      ><a name="7431" href="StlcProp.html#7431" class="Bound"
      >t&#8321;</a
      ><a name="7433"
      > </a
      ><a name="7434" href="StlcProp.html#7434" class="Bound"
      >t&#8322;</a
      ><a name="7436"
      > </a
      ><a name="7437" href="StlcProp.html#7437" class="Bound"
      >t&#8323;</a
      ><a name="7439" class="Symbol"
      >}</a
      ><a name="7440"
      > </a
      ><a name="7441" class="Symbol"
      >&#8594;</a
      ><a name="7442"
      > </a
      ><a name="7443" href="StlcProp.html#7057" class="Bound"
      >x</a
      ><a name="7444"
      > </a
      ><a name="7445" href="StlcProp.html#7047" class="Datatype Operator"
      >FreeIn</a
      ><a name="7451"
      > </a
      ><a name="7452" href="StlcProp.html#7437" class="Bound"
      >t&#8323;</a
      ><a name="7454"
      > </a
      ><a name="7455" class="Symbol"
      >&#8594;</a
      ><a name="7456"
      > </a
      ><a name="7457" href="StlcProp.html#7057" class="Bound"
      >x</a
      ><a name="7458"
      > </a
      ><a name="7459" href="StlcProp.html#7047" class="Datatype Operator"
      >FreeIn</a
      ><a name="7465"
      > </a
      ><a name="7466" class="Symbol"
      >(</a
      ><a name="7467" href="Stlc.html#5887" class="InductiveConstructor Operator"
      >if</a
      ><a name="7469"
      > </a
      ><a name="7470" href="StlcProp.html#7431" class="Bound"
      >t&#8321;</a
      ><a name="7472"
      > </a
      ><a name="7473" href="Stlc.html#5887" class="InductiveConstructor Operator"
      >then</a
      ><a name="7477"
      > </a
      ><a name="7478" href="StlcProp.html#7434" class="Bound"
      >t&#8322;</a
      ><a name="7480"
      > </a
      ><a name="7481" href="Stlc.html#5887" class="InductiveConstructor Operator"
      >else</a
      ><a name="7485"
      > </a
      ><a name="7486" href="StlcProp.html#7437" class="Bound"
      >t&#8323;</a
      ><a name="7488" class="Symbol"
      >)</a
      >
</pre><!--{% endraw %}-->

A term in which no variables appear free is said to be _closed_.

<!--{% raw %}--><pre class="Agda">
<a name="7581" href="StlcProp.html#7581" class="Function"
      >Closed</a
      ><a name="7587"
      > </a
      ><a name="7588" class="Symbol"
      >:</a
      ><a name="7589"
      > </a
      ><a name="7590" href="Stlc.html#5755" class="Datatype"
      >Term</a
      ><a name="7594"
      > </a
      ><a name="7595" class="Symbol"
      >&#8594;</a
      ><a name="7596"
      > </a
      ><a name="7597" class="PrimitiveType"
      >Set</a
      ><a name="7600"
      >
</a
      ><a name="7601" href="StlcProp.html#7581" class="Function"
      >Closed</a
      ><a name="7607"
      > </a
      ><a name="7608" href="StlcProp.html#7608" class="Bound"
      >t</a
      ><a name="7609"
      > </a
      ><a name="7610" class="Symbol"
      >=</a
      ><a name="7611"
      > </a
      ><a name="7612" class="Symbol"
      >&#8704;</a
      ><a name="7613"
      > </a
      ><a name="7614" class="Symbol"
      >{</a
      ><a name="7615" href="StlcProp.html#7615" class="Bound"
      >x</a
      ><a name="7616" class="Symbol"
      >}</a
      ><a name="7617"
      > </a
      ><a name="7618" class="Symbol"
      >&#8594;</a
      ><a name="7619"
      > </a
      ><a name="7620" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#414" class="Function Operator"
      >&#172;</a
      ><a name="7621"
      > </a
      ><a name="7622" class="Symbol"
      >(</a
      ><a name="7623" href="StlcProp.html#7615" class="Bound"
      >x</a
      ><a name="7624"
      > </a
      ><a name="7625" href="StlcProp.html#7047" class="Datatype Operator"
      >FreeIn</a
      ><a name="7631"
      > </a
      ><a name="7632" href="StlcProp.html#7608" class="Bound"
      >t</a
      ><a name="7633" class="Symbol"
      >)</a
      >
</pre><!--{% endraw %}-->

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
a variable $$x$$ appears free in a term $$t$$, and if we know $$t$$ is
well typed in context $$\Gamma$$, then it must be the case that
$$\Gamma$$ assigns a type to $$x$$.

<!--{% raw %}--><pre class="Agda">
<a name="8362" href="StlcProp.html#8362" class="Function"
      >freeInCtxt</a
      ><a name="8372"
      > </a
      ><a name="8373" class="Symbol"
      >:</a
      ><a name="8374"
      > </a
      ><a name="8375" class="Symbol"
      >&#8704;</a
      ><a name="8376"
      > </a
      ><a name="8377" class="Symbol"
      >{</a
      ><a name="8378" href="StlcProp.html#8378" class="Bound"
      >x</a
      ><a name="8379"
      > </a
      ><a name="8380" href="StlcProp.html#8380" class="Bound"
      >t</a
      ><a name="8381"
      > </a
      ><a name="8382" href="StlcProp.html#8382" class="Bound"
      >A</a
      ><a name="8383"
      > </a
      ><a name="8384" href="StlcProp.html#8384" class="Bound"
      >&#915;</a
      ><a name="8385" class="Symbol"
      >}</a
      ><a name="8386"
      > </a
      ><a name="8387" class="Symbol"
      >&#8594;</a
      ><a name="8388"
      > </a
      ><a name="8389" href="StlcProp.html#8378" class="Bound"
      >x</a
      ><a name="8390"
      > </a
      ><a name="8391" href="StlcProp.html#7047" class="Datatype Operator"
      >FreeIn</a
      ><a name="8397"
      > </a
      ><a name="8398" href="StlcProp.html#8380" class="Bound"
      >t</a
      ><a name="8399"
      > </a
      ><a name="8400" class="Symbol"
      >&#8594;</a
      ><a name="8401"
      > </a
      ><a name="8402" href="StlcProp.html#8384" class="Bound"
      >&#915;</a
      ><a name="8403"
      > </a
      ><a name="8404" href="Stlc.html#19231" class="Datatype Operator"
      >&#8866;</a
      ><a name="8405"
      > </a
      ><a name="8406" href="StlcProp.html#8380" class="Bound"
      >t</a
      ><a name="8407"
      > </a
      ><a name="8408" href="Stlc.html#19231" class="Datatype Operator"
      >&#8758;</a
      ><a name="8409"
      > </a
      ><a name="8410" href="StlcProp.html#8382" class="Bound"
      >A</a
      ><a name="8411"
      > </a
      ><a name="8412" class="Symbol"
      >&#8594;</a
      ><a name="8413"
      > </a
      ><a name="8414" href="https://agda.github.io/agda-stdlib/Data.Product.html#823" class="Function"
      >&#8707;</a
      ><a name="8415"
      > </a
      ><a name="8416" class="Symbol"
      >&#955;</a
      ><a name="8417"
      > </a
      ><a name="8418" href="StlcProp.html#8418" class="Bound"
      >B</a
      ><a name="8419"
      > </a
      ><a name="8420" class="Symbol"
      >&#8594;</a
      ><a name="8421"
      > </a
      ><a name="8422" href="StlcProp.html#8384" class="Bound"
      >&#915;</a
      ><a name="8423"
      > </a
      ><a name="8424" href="StlcProp.html#8378" class="Bound"
      >x</a
      ><a name="8425"
      > </a
      ><a name="8426" href="Agda.Builtin.Equality.html#55" class="Datatype Operator"
      >&#8801;</a
      ><a name="8427"
      > </a
      ><a name="8428" href="https://agda.github.io/agda-stdlib/Data.Maybe.Base.html#373" class="InductiveConstructor"
      >just</a
      ><a name="8432"
      > </a
      ><a name="8433" href="StlcProp.html#8418" class="Bound"
      >B</a
      >
</pre><!--{% endraw %}-->

_Proof_: We show, by induction on the proof that $$x$$ appears
  free in $$t$$, that, for all contexts $$\Gamma$$, if $$t$$ is well
  typed under $$\Gamma$$, then $$\Gamma$$ assigns some type to $$x$$.

  - If the last rule used was `var`, then $$t = x$$, and from
    the assumption that $$t$$ is well typed under $$\Gamma$$ we have
    immediately that $$\Gamma$$ assigns a type to $$x$$.

  - If the last rule used was `app1`, then $$t = t_1\;t_2$$ and $$x$$
    appears free in $$t_1$$.  Since $$t$$ is well typed under $$\Gamma$$,
    we can see from the typing rules that $$t_1$$ must also be, and
    the IH then tells us that $$\Gamma$$ assigns $$x$$ a type.

  - Almost all the other cases are similar: $$x$$ appears free in a
    subterm of $$t$$, and since $$t$$ is well typed under $$\Gamma$$, we
    know the subterm of $$t$$ in which $$x$$ appears is well typed
    under $$\Gamma$$ as well, and the IH gives us exactly the
    conclusion we want.

  - The only remaining case is `abs`.  In this case $$t =
    \lambda y:A.t'$$, and $$x$$ appears free in $$t'$$; we also know that
    $$x$$ is different from $$y$$.  The difference from the previous
    cases is that whereas $$t$$ is well typed under $$\Gamma$$, its
    body $$t'$$ is well typed under $$(\Gamma, y:A)$$, so the IH
    allows us to conclude that $$x$$ is assigned some type by the
    extended context $$(\Gamma, y:A)$$.  To conclude that $$\Gamma$$
    assigns a type to $$x$$, we appeal the decidable equality for names
    `_≟_`, noting that $$x$$ and $$y$$ are different variables.

<!--{% raw %}--><pre class="Agda">
<a name="10029" href="StlcProp.html#8362" class="Function"
      >freeInCtxt</a
      ><a name="10039"
      > </a
      ><a name="10040" href="StlcProp.html#7086" class="InductiveConstructor"
      >var</a
      ><a name="10043"
      > </a
      ><a name="10044" class="Symbol"
      >(</a
      ><a name="10045" href="Stlc.html#19275" class="InductiveConstructor"
      >var</a
      ><a name="10048"
      > </a
      ><a name="10049" class="Symbol"
      >_</a
      ><a name="10050"
      > </a
      ><a name="10051" href="StlcProp.html#10051" class="Bound"
      >x&#8758;A</a
      ><a name="10054" class="Symbol"
      >)</a
      ><a name="10055"
      > </a
      ><a name="10056" class="Symbol"
      >=</a
      ><a name="10057"
      > </a
      ><a name="10058" class="Symbol"
      >(_</a
      ><a name="10060"
      > </a
      ><a name="10061" href="https://agda.github.io/agda-stdlib/Data.Product.html#509" class="InductiveConstructor Operator"
      >,</a
      ><a name="10062"
      > </a
      ><a name="10063" href="StlcProp.html#10051" class="Bound"
      >x&#8758;A</a
      ><a name="10066" class="Symbol"
      >)</a
      ><a name="10067"
      >
</a
      ><a name="10068" href="StlcProp.html#8362" class="Function"
      >freeInCtxt</a
      ><a name="10078"
      > </a
      ><a name="10079" class="Symbol"
      >(</a
      ><a name="10080" href="StlcProp.html#7171" class="InductiveConstructor"
      >app1</a
      ><a name="10084"
      > </a
      ><a name="10085" href="StlcProp.html#10085" class="Bound"
      >x&#8712;t&#8321;</a
      ><a name="10089" class="Symbol"
      >)</a
      ><a name="10090"
      > </a
      ><a name="10091" class="Symbol"
      >(</a
      ><a name="10092" href="Stlc.html#19484" class="InductiveConstructor"
      >app</a
      ><a name="10095"
      > </a
      ><a name="10096" href="StlcProp.html#10096" class="Bound"
      >t&#8321;&#8758;A</a
      ><a name="10100"
      > </a
      ><a name="10101" class="Symbol"
      >_</a
      ><a name="10102"
      >   </a
      ><a name="10105" class="Symbol"
      >)</a
      ><a name="10106"
      > </a
      ><a name="10107" class="Symbol"
      >=</a
      ><a name="10108"
      > </a
      ><a name="10109" href="StlcProp.html#8362" class="Function"
      >freeInCtxt</a
      ><a name="10119"
      > </a
      ><a name="10120" href="StlcProp.html#10085" class="Bound"
      >x&#8712;t&#8321;</a
      ><a name="10124"
      > </a
      ><a name="10125" href="StlcProp.html#10096" class="Bound"
      >t&#8321;&#8758;A</a
      ><a name="10129"
      >
</a
      ><a name="10130" href="StlcProp.html#8362" class="Function"
      >freeInCtxt</a
      ><a name="10140"
      > </a
      ><a name="10141" class="Symbol"
      >(</a
      ><a name="10142" href="StlcProp.html#7225" class="InductiveConstructor"
      >app2</a
      ><a name="10146"
      > </a
      ><a name="10147" href="StlcProp.html#10147" class="Bound"
      >x&#8712;t&#8322;</a
      ><a name="10151" class="Symbol"
      >)</a
      ><a name="10152"
      > </a
      ><a name="10153" class="Symbol"
      >(</a
      ><a name="10154" href="Stlc.html#19484" class="InductiveConstructor"
      >app</a
      ><a name="10157"
      > </a
      ><a name="10158" class="Symbol"
      >_</a
      ><a name="10159"
      >    </a
      ><a name="10163" href="StlcProp.html#10163" class="Bound"
      >t&#8322;&#8758;A</a
      ><a name="10167" class="Symbol"
      >)</a
      ><a name="10168"
      > </a
      ><a name="10169" class="Symbol"
      >=</a
      ><a name="10170"
      > </a
      ><a name="10171" href="StlcProp.html#8362" class="Function"
      >freeInCtxt</a
      ><a name="10181"
      > </a
      ><a name="10182" href="StlcProp.html#10147" class="Bound"
      >x&#8712;t&#8322;</a
      ><a name="10186"
      > </a
      ><a name="10187" href="StlcProp.html#10163" class="Bound"
      >t&#8322;&#8758;A</a
      ><a name="10191"
      >
</a
      ><a name="10192" href="StlcProp.html#8362" class="Function"
      >freeInCtxt</a
      ><a name="10202"
      > </a
      ><a name="10203" class="Symbol"
      >(</a
      ><a name="10204" href="StlcProp.html#7279" class="InductiveConstructor"
      >if1</a
      ><a name="10207"
      >  </a
      ><a name="10209" href="StlcProp.html#10209" class="Bound"
      >x&#8712;t&#8321;</a
      ><a name="10213" class="Symbol"
      >)</a
      ><a name="10214"
      > </a
      ><a name="10215" class="Symbol"
      >(</a
      ><a name="10216" href="Stlc.html#19736" class="InductiveConstructor Operator"
      >if</a
      ><a name="10218"
      > </a
      ><a name="10219" href="StlcProp.html#10219" class="Bound"
      >t&#8321;&#8758;A</a
      ><a name="10223"
      > </a
      ><a name="10224" href="Stlc.html#19736" class="InductiveConstructor Operator"
      >then</a
      ><a name="10228"
      > </a
      ><a name="10229" class="Symbol"
      >_</a
      ><a name="10230"
      >    </a
      ><a name="10234" href="Stlc.html#19736" class="InductiveConstructor Operator"
      >else</a
      ><a name="10238"
      > </a
      ><a name="10239" class="Symbol"
      >_</a
      ><a name="10240"
      >   </a
      ><a name="10243" class="Symbol"
      >)</a
      ><a name="10244"
      > </a
      ><a name="10245" class="Symbol"
      >=</a
      ><a name="10246"
      > </a
      ><a name="10247" href="StlcProp.html#8362" class="Function"
      >freeInCtxt</a
      ><a name="10257"
      > </a
      ><a name="10258" href="StlcProp.html#10209" class="Bound"
      >x&#8712;t&#8321;</a
      ><a name="10262"
      > </a
      ><a name="10263" href="StlcProp.html#10219" class="Bound"
      >t&#8321;&#8758;A</a
      ><a name="10267"
      >
</a
      ><a name="10268" href="StlcProp.html#8362" class="Function"
      >freeInCtxt</a
      ><a name="10278"
      > </a
      ><a name="10279" class="Symbol"
      >(</a
      ><a name="10280" href="StlcProp.html#7350" class="InductiveConstructor"
      >if2</a
      ><a name="10283"
      >  </a
      ><a name="10285" href="StlcProp.html#10285" class="Bound"
      >x&#8712;t&#8322;</a
      ><a name="10289" class="Symbol"
      >)</a
      ><a name="10290"
      > </a
      ><a name="10291" class="Symbol"
      >(</a
      ><a name="10292" href="Stlc.html#19736" class="InductiveConstructor Operator"
      >if</a
      ><a name="10294"
      > </a
      ><a name="10295" class="Symbol"
      >_</a
      ><a name="10296"
      >    </a
      ><a name="10300" href="Stlc.html#19736" class="InductiveConstructor Operator"
      >then</a
      ><a name="10304"
      > </a
      ><a name="10305" href="StlcProp.html#10305" class="Bound"
      >t&#8322;&#8758;A</a
      ><a name="10309"
      > </a
      ><a name="10310" href="Stlc.html#19736" class="InductiveConstructor Operator"
      >else</a
      ><a name="10314"
      > </a
      ><a name="10315" class="Symbol"
      >_</a
      ><a name="10316"
      >   </a
      ><a name="10319" class="Symbol"
      >)</a
      ><a name="10320"
      > </a
      ><a name="10321" class="Symbol"
      >=</a
      ><a name="10322"
      > </a
      ><a name="10323" href="StlcProp.html#8362" class="Function"
      >freeInCtxt</a
      ><a name="10333"
      > </a
      ><a name="10334" href="StlcProp.html#10285" class="Bound"
      >x&#8712;t&#8322;</a
      ><a name="10338"
      > </a
      ><a name="10339" href="StlcProp.html#10305" class="Bound"
      >t&#8322;&#8758;A</a
      ><a name="10343"
      >
</a
      ><a name="10344" href="StlcProp.html#8362" class="Function"
      >freeInCtxt</a
      ><a name="10354"
      > </a
      ><a name="10355" class="Symbol"
      >(</a
      ><a name="10356" href="StlcProp.html#7421" class="InductiveConstructor"
      >if3</a
      ><a name="10359"
      >  </a
      ><a name="10361" href="StlcProp.html#10361" class="Bound"
      >x&#8712;t&#8323;</a
      ><a name="10365" class="Symbol"
      >)</a
      ><a name="10366"
      > </a
      ><a name="10367" class="Symbol"
      >(</a
      ><a name="10368" href="Stlc.html#19736" class="InductiveConstructor Operator"
      >if</a
      ><a name="10370"
      > </a
      ><a name="10371" class="Symbol"
      >_</a
      ><a name="10372"
      >    </a
      ><a name="10376" href="Stlc.html#19736" class="InductiveConstructor Operator"
      >then</a
      ><a name="10380"
      > </a
      ><a name="10381" class="Symbol"
      >_</a
      ><a name="10382"
      >    </a
      ><a name="10386" href="Stlc.html#19736" class="InductiveConstructor Operator"
      >else</a
      ><a name="10390"
      > </a
      ><a name="10391" href="StlcProp.html#10391" class="Bound"
      >t&#8323;&#8758;A</a
      ><a name="10395" class="Symbol"
      >)</a
      ><a name="10396"
      > </a
      ><a name="10397" class="Symbol"
      >=</a
      ><a name="10398"
      > </a
      ><a name="10399" href="StlcProp.html#8362" class="Function"
      >freeInCtxt</a
      ><a name="10409"
      > </a
      ><a name="10410" href="StlcProp.html#10361" class="Bound"
      >x&#8712;t&#8323;</a
      ><a name="10414"
      > </a
      ><a name="10415" href="StlcProp.html#10391" class="Bound"
      >t&#8323;&#8758;A</a
      ><a name="10419"
      >
</a
      ><a name="10420" href="StlcProp.html#8362" class="Function"
      >freeInCtxt</a
      ><a name="10430"
      > </a
      ><a name="10431" class="Symbol"
      >{</a
      ><a name="10432" href="StlcProp.html#10432" class="Bound"
      >x</a
      ><a name="10433" class="Symbol"
      >}</a
      ><a name="10434"
      > </a
      ><a name="10435" class="Symbol"
      >(</a
      ><a name="10436" href="StlcProp.html#7110" class="InductiveConstructor"
      >abs</a
      ><a name="10439"
      > </a
      ><a name="10440" class="Symbol"
      >{</a
      ><a name="10441" href="StlcProp.html#10441" class="Bound"
      >y</a
      ><a name="10442" class="Symbol"
      >}</a
      ><a name="10443"
      > </a
      ><a name="10444" href="StlcProp.html#10444" class="Bound"
      >y&#8800;x</a
      ><a name="10447"
      > </a
      ><a name="10448" href="StlcProp.html#10448" class="Bound"
      >x&#8712;t</a
      ><a name="10451" class="Symbol"
      >)</a
      ><a name="10452"
      > </a
      ><a name="10453" class="Symbol"
      >(</a
      ><a name="10454" href="Stlc.html#19368" class="InductiveConstructor"
      >abs</a
      ><a name="10457"
      > </a
      ><a name="10458" href="StlcProp.html#10458" class="Bound"
      >t&#8758;B</a
      ><a name="10461" class="Symbol"
      >)</a
      ><a name="10462"
      >
    </a
      ><a name="10467" class="Keyword"
      >with</a
      ><a name="10471"
      > </a
      ><a name="10472" href="StlcProp.html#8362" class="Function"
      >freeInCtxt</a
      ><a name="10482"
      > </a
      ><a name="10483" href="StlcProp.html#10448" class="Bound"
      >x&#8712;t</a
      ><a name="10486"
      > </a
      ><a name="10487" href="StlcProp.html#10458" class="Bound"
      >t&#8758;B</a
      ><a name="10490"
      >
</a
      ><a name="10491" class="Symbol"
      >...</a
      ><a name="10494"
      > </a
      ><a name="10495" class="Symbol"
      >|</a
      ><a name="10496"
      > </a
      ><a name="10497" href="StlcProp.html#10497" class="Bound"
      >x&#8758;A</a
      ><a name="10500"
      >
    </a
      ><a name="10505" class="Keyword"
      >with</a
      ><a name="10509"
      > </a
      ><a name="10510" href="StlcProp.html#10441" class="Bound"
      >y</a
      ><a name="10511"
      > </a
      ><a name="10512" href="Maps.html#2454" class="Function Operator"
      >&#8799;</a
      ><a name="10513"
      > </a
      ><a name="10514" href="StlcProp.html#10432" class="Bound"
      >x</a
      ><a name="10515"
      >
</a
      ><a name="10516" class="Symbol"
      >...</a
      ><a name="10519"
      > </a
      ><a name="10520" class="Symbol"
      >|</a
      ><a name="10521"
      > </a
      ><a name="10522" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#520" class="InductiveConstructor"
      >yes</a
      ><a name="10525"
      > </a
      ><a name="10526" href="StlcProp.html#10526" class="Bound"
      >y=x</a
      ><a name="10529"
      > </a
      ><a name="10530" class="Symbol"
      >=</a
      ><a name="10531"
      > </a
      ><a name="10532" href="https://agda.github.io/agda-stdlib/Data.Empty.html#348" class="Function"
      >&#8869;-elim</a
      ><a name="10538"
      > </a
      ><a name="10539" class="Symbol"
      >(</a
      ><a name="10540" href="StlcProp.html#10444" class="Bound"
      >y&#8800;x</a
      ><a name="10543"
      > </a
      ><a name="10544" href="StlcProp.html#10526" class="Bound"
      >y=x</a
      ><a name="10547" class="Symbol"
      >)</a
      ><a name="10548"
      >
</a
      ><a name="10549" class="Symbol"
      >...</a
      ><a name="10552"
      > </a
      ><a name="10553" class="Symbol"
      >|</a
      ><a name="10554"
      > </a
      ><a name="10555" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#547" class="InductiveConstructor"
      >no</a
      ><a name="10557"
      >  </a
      ><a name="10559" class="Symbol"
      >_</a
      ><a name="10560"
      >   </a
      ><a name="10563" class="Symbol"
      >=</a
      ><a name="10564"
      > </a
      ><a name="10565" href="StlcProp.html#10497" class="Bound"
      >x&#8758;A</a
      >
</pre><!--{% endraw %}-->

Next, we'll need the fact that any term $$t$$ which is well typed in
the empty context is closed (it has no free variables).

#### Exercise: 2 stars, optional (∅⊢-closed)

<!--{% raw %}--><pre class="Agda">
<a name="10766" class="Keyword"
      >postulate</a
      ><a name="10775"
      >
  </a
      ><a name="10778" href="StlcProp.html#10778" class="Postulate"
      >&#8709;&#8866;-closed</a
      ><a name="10787"
      > </a
      ><a name="10788" class="Symbol"
      >:</a
      ><a name="10789"
      > </a
      ><a name="10790" class="Symbol"
      >&#8704;</a
      ><a name="10791"
      > </a
      ><a name="10792" class="Symbol"
      >{</a
      ><a name="10793" href="StlcProp.html#10793" class="Bound"
      >t</a
      ><a name="10794"
      > </a
      ><a name="10795" href="StlcProp.html#10795" class="Bound"
      >A</a
      ><a name="10796" class="Symbol"
      >}</a
      ><a name="10797"
      > </a
      ><a name="10798" class="Symbol"
      >&#8594;</a
      ><a name="10799"
      > </a
      ><a name="10800" href="Stlc.html#18299" class="Function"
      >&#8709;</a
      ><a name="10801"
      > </a
      ><a name="10802" href="Stlc.html#19231" class="Datatype Operator"
      >&#8866;</a
      ><a name="10803"
      > </a
      ><a name="10804" href="StlcProp.html#10793" class="Bound"
      >t</a
      ><a name="10805"
      > </a
      ><a name="10806" href="Stlc.html#19231" class="Datatype Operator"
      >&#8758;</a
      ><a name="10807"
      > </a
      ><a name="10808" href="StlcProp.html#10795" class="Bound"
      >A</a
      ><a name="10809"
      > </a
      ><a name="10810" class="Symbol"
      >&#8594;</a
      ><a name="10811"
      > </a
      ><a name="10812" href="StlcProp.html#7581" class="Function"
      >Closed</a
      ><a name="10818"
      > </a
      ><a name="10819" href="StlcProp.html#10793" class="Bound"
      >t</a
      >
</pre><!--{% endraw %}-->

<div class="hidden">
<!--{% raw %}--><pre class="Agda">
<a name="10867" href="StlcProp.html#10867" class="Function"
      >&#8709;&#8866;-closed&#8242;</a
      ><a name="10877"
      > </a
      ><a name="10878" class="Symbol"
      >:</a
      ><a name="10879"
      > </a
      ><a name="10880" class="Symbol"
      >&#8704;</a
      ><a name="10881"
      > </a
      ><a name="10882" class="Symbol"
      >{</a
      ><a name="10883" href="StlcProp.html#10883" class="Bound"
      >t</a
      ><a name="10884"
      > </a
      ><a name="10885" href="StlcProp.html#10885" class="Bound"
      >A</a
      ><a name="10886" class="Symbol"
      >}</a
      ><a name="10887"
      > </a
      ><a name="10888" class="Symbol"
      >&#8594;</a
      ><a name="10889"
      > </a
      ><a name="10890" href="Stlc.html#18299" class="Function"
      >&#8709;</a
      ><a name="10891"
      > </a
      ><a name="10892" href="Stlc.html#19231" class="Datatype Operator"
      >&#8866;</a
      ><a name="10893"
      > </a
      ><a name="10894" href="StlcProp.html#10883" class="Bound"
      >t</a
      ><a name="10895"
      > </a
      ><a name="10896" href="Stlc.html#19231" class="Datatype Operator"
      >&#8758;</a
      ><a name="10897"
      > </a
      ><a name="10898" href="StlcProp.html#10885" class="Bound"
      >A</a
      ><a name="10899"
      > </a
      ><a name="10900" class="Symbol"
      >&#8594;</a
      ><a name="10901"
      > </a
      ><a name="10902" href="StlcProp.html#7581" class="Function"
      >Closed</a
      ><a name="10908"
      > </a
      ><a name="10909" href="StlcProp.html#10883" class="Bound"
      >t</a
      ><a name="10910"
      >
</a
      ><a name="10911" href="StlcProp.html#10867" class="Function"
      >&#8709;&#8866;-closed&#8242;</a
      ><a name="10921"
      > </a
      ><a name="10922" class="Symbol"
      >(</a
      ><a name="10923" href="Stlc.html#19275" class="InductiveConstructor"
      >var</a
      ><a name="10926"
      > </a
      ><a name="10927" href="StlcProp.html#10927" class="Bound"
      >x</a
      ><a name="10928"
      > </a
      ><a name="10929" class="Symbol"
      >())</a
      ><a name="10932"
      >
</a
      ><a name="10933" href="StlcProp.html#10867" class="Function"
      >&#8709;&#8866;-closed&#8242;</a
      ><a name="10943"
      > </a
      ><a name="10944" class="Symbol"
      >(</a
      ><a name="10945" href="Stlc.html#19484" class="InductiveConstructor"
      >app</a
      ><a name="10948"
      > </a
      ><a name="10949" href="StlcProp.html#10949" class="Bound"
      >t&#8321;&#8758;A&#8658;B</a
      ><a name="10955"
      > </a
      ><a name="10956" href="StlcProp.html#10956" class="Bound"
      >t&#8322;&#8758;A</a
      ><a name="10960" class="Symbol"
      >)</a
      ><a name="10961"
      > </a
      ><a name="10962" class="Symbol"
      >(</a
      ><a name="10963" href="StlcProp.html#7171" class="InductiveConstructor"
      >app1</a
      ><a name="10967"
      > </a
      ><a name="10968" href="StlcProp.html#10968" class="Bound"
      >x&#8712;t&#8321;</a
      ><a name="10972" class="Symbol"
      >)</a
      ><a name="10973"
      > </a
      ><a name="10974" class="Symbol"
      >=</a
      ><a name="10975"
      > </a
      ><a name="10976" href="StlcProp.html#10867" class="Function"
      >&#8709;&#8866;-closed&#8242;</a
      ><a name="10986"
      > </a
      ><a name="10987" href="StlcProp.html#10949" class="Bound"
      >t&#8321;&#8758;A&#8658;B</a
      ><a name="10993"
      > </a
      ><a name="10994" href="StlcProp.html#10968" class="Bound"
      >x&#8712;t&#8321;</a
      ><a name="10998"
      >
</a
      ><a name="10999" href="StlcProp.html#10867" class="Function"
      >&#8709;&#8866;-closed&#8242;</a
      ><a name="11009"
      > </a
      ><a name="11010" class="Symbol"
      >(</a
      ><a name="11011" href="Stlc.html#19484" class="InductiveConstructor"
      >app</a
      ><a name="11014"
      > </a
      ><a name="11015" href="StlcProp.html#11015" class="Bound"
      >t&#8321;&#8758;A&#8658;B</a
      ><a name="11021"
      > </a
      ><a name="11022" href="StlcProp.html#11022" class="Bound"
      >t&#8322;&#8758;A</a
      ><a name="11026" class="Symbol"
      >)</a
      ><a name="11027"
      > </a
      ><a name="11028" class="Symbol"
      >(</a
      ><a name="11029" href="StlcProp.html#7225" class="InductiveConstructor"
      >app2</a
      ><a name="11033"
      > </a
      ><a name="11034" href="StlcProp.html#11034" class="Bound"
      >x&#8712;t&#8322;</a
      ><a name="11038" class="Symbol"
      >)</a
      ><a name="11039"
      > </a
      ><a name="11040" class="Symbol"
      >=</a
      ><a name="11041"
      > </a
      ><a name="11042" href="StlcProp.html#10867" class="Function"
      >&#8709;&#8866;-closed&#8242;</a
      ><a name="11052"
      > </a
      ><a name="11053" href="StlcProp.html#11022" class="Bound"
      >t&#8322;&#8758;A</a
      ><a name="11057"
      > </a
      ><a name="11058" href="StlcProp.html#11034" class="Bound"
      >x&#8712;t&#8322;</a
      ><a name="11062"
      >
</a
      ><a name="11063" href="StlcProp.html#10867" class="Function"
      >&#8709;&#8866;-closed&#8242;</a
      ><a name="11073"
      > </a
      ><a name="11074" href="Stlc.html#19618" class="InductiveConstructor"
      >true</a
      ><a name="11078"
      >  </a
      ><a name="11080" class="Symbol"
      >()</a
      ><a name="11082"
      >
</a
      ><a name="11083" href="StlcProp.html#10867" class="Function"
      >&#8709;&#8866;-closed&#8242;</a
      ><a name="11093"
      > </a
      ><a name="11094" href="Stlc.html#19677" class="InductiveConstructor"
      >false</a
      ><a name="11099"
      > </a
      ><a name="11100" class="Symbol"
      >()</a
      ><a name="11102"
      >
</a
      ><a name="11103" href="StlcProp.html#10867" class="Function"
      >&#8709;&#8866;-closed&#8242;</a
      ><a name="11113"
      > </a
      ><a name="11114" class="Symbol"
      >(</a
      ><a name="11115" href="Stlc.html#19736" class="InductiveConstructor Operator"
      >if</a
      ><a name="11117"
      > </a
      ><a name="11118" href="StlcProp.html#11118" class="Bound"
      >t&#8321;&#8758;bool</a
      ><a name="11125"
      > </a
      ><a name="11126" href="Stlc.html#19736" class="InductiveConstructor Operator"
      >then</a
      ><a name="11130"
      > </a
      ><a name="11131" href="StlcProp.html#11131" class="Bound"
      >t&#8322;&#8758;A</a
      ><a name="11135"
      > </a
      ><a name="11136" href="Stlc.html#19736" class="InductiveConstructor Operator"
      >else</a
      ><a name="11140"
      > </a
      ><a name="11141" href="StlcProp.html#11141" class="Bound"
      >t&#8323;&#8758;A</a
      ><a name="11145" class="Symbol"
      >)</a
      ><a name="11146"
      > </a
      ><a name="11147" class="Symbol"
      >(</a
      ><a name="11148" href="StlcProp.html#7279" class="InductiveConstructor"
      >if1</a
      ><a name="11151"
      > </a
      ><a name="11152" href="StlcProp.html#11152" class="Bound"
      >x&#8712;t&#8321;</a
      ><a name="11156" class="Symbol"
      >)</a
      ><a name="11157"
      > </a
      ><a name="11158" class="Symbol"
      >=</a
      ><a name="11159"
      > </a
      ><a name="11160" href="StlcProp.html#10867" class="Function"
      >&#8709;&#8866;-closed&#8242;</a
      ><a name="11170"
      > </a
      ><a name="11171" href="StlcProp.html#11118" class="Bound"
      >t&#8321;&#8758;bool</a
      ><a name="11178"
      > </a
      ><a name="11179" href="StlcProp.html#11152" class="Bound"
      >x&#8712;t&#8321;</a
      ><a name="11183"
      >
</a
      ><a name="11184" href="StlcProp.html#10867" class="Function"
      >&#8709;&#8866;-closed&#8242;</a
      ><a name="11194"
      > </a
      ><a name="11195" class="Symbol"
      >(</a
      ><a name="11196" href="Stlc.html#19736" class="InductiveConstructor Operator"
      >if</a
      ><a name="11198"
      > </a
      ><a name="11199" href="StlcProp.html#11199" class="Bound"
      >t&#8321;&#8758;bool</a
      ><a name="11206"
      > </a
      ><a name="11207" href="Stlc.html#19736" class="InductiveConstructor Operator"
      >then</a
      ><a name="11211"
      > </a
      ><a name="11212" href="StlcProp.html#11212" class="Bound"
      >t&#8322;&#8758;A</a
      ><a name="11216"
      > </a
      ><a name="11217" href="Stlc.html#19736" class="InductiveConstructor Operator"
      >else</a
      ><a name="11221"
      > </a
      ><a name="11222" href="StlcProp.html#11222" class="Bound"
      >t&#8323;&#8758;A</a
      ><a name="11226" class="Symbol"
      >)</a
      ><a name="11227"
      > </a
      ><a name="11228" class="Symbol"
      >(</a
      ><a name="11229" href="StlcProp.html#7350" class="InductiveConstructor"
      >if2</a
      ><a name="11232"
      > </a
      ><a name="11233" href="StlcProp.html#11233" class="Bound"
      >x&#8712;t&#8322;</a
      ><a name="11237" class="Symbol"
      >)</a
      ><a name="11238"
      > </a
      ><a name="11239" class="Symbol"
      >=</a
      ><a name="11240"
      > </a
      ><a name="11241" href="StlcProp.html#10867" class="Function"
      >&#8709;&#8866;-closed&#8242;</a
      ><a name="11251"
      > </a
      ><a name="11252" href="StlcProp.html#11212" class="Bound"
      >t&#8322;&#8758;A</a
      ><a name="11256"
      > </a
      ><a name="11257" href="StlcProp.html#11233" class="Bound"
      >x&#8712;t&#8322;</a
      ><a name="11261"
      >
</a
      ><a name="11262" href="StlcProp.html#10867" class="Function"
      >&#8709;&#8866;-closed&#8242;</a
      ><a name="11272"
      > </a
      ><a name="11273" class="Symbol"
      >(</a
      ><a name="11274" href="Stlc.html#19736" class="InductiveConstructor Operator"
      >if</a
      ><a name="11276"
      > </a
      ><a name="11277" href="StlcProp.html#11277" class="Bound"
      >t&#8321;&#8758;bool</a
      ><a name="11284"
      > </a
      ><a name="11285" href="Stlc.html#19736" class="InductiveConstructor Operator"
      >then</a
      ><a name="11289"
      > </a
      ><a name="11290" href="StlcProp.html#11290" class="Bound"
      >t&#8322;&#8758;A</a
      ><a name="11294"
      > </a
      ><a name="11295" href="Stlc.html#19736" class="InductiveConstructor Operator"
      >else</a
      ><a name="11299"
      > </a
      ><a name="11300" href="StlcProp.html#11300" class="Bound"
      >t&#8323;&#8758;A</a
      ><a name="11304" class="Symbol"
      >)</a
      ><a name="11305"
      > </a
      ><a name="11306" class="Symbol"
      >(</a
      ><a name="11307" href="StlcProp.html#7421" class="InductiveConstructor"
      >if3</a
      ><a name="11310"
      > </a
      ><a name="11311" href="StlcProp.html#11311" class="Bound"
      >x&#8712;t&#8323;</a
      ><a name="11315" class="Symbol"
      >)</a
      ><a name="11316"
      > </a
      ><a name="11317" class="Symbol"
      >=</a
      ><a name="11318"
      > </a
      ><a name="11319" href="StlcProp.html#10867" class="Function"
      >&#8709;&#8866;-closed&#8242;</a
      ><a name="11329"
      > </a
      ><a name="11330" href="StlcProp.html#11300" class="Bound"
      >t&#8323;&#8758;A</a
      ><a name="11334"
      > </a
      ><a name="11335" href="StlcProp.html#11311" class="Bound"
      >x&#8712;t&#8323;</a
      ><a name="11339"
      >
</a
      ><a name="11340" href="StlcProp.html#10867" class="Function"
      >&#8709;&#8866;-closed&#8242;</a
      ><a name="11350"
      > </a
      ><a name="11351" class="Symbol"
      >(</a
      ><a name="11352" href="Stlc.html#19368" class="InductiveConstructor"
      >abs</a
      ><a name="11355"
      > </a
      ><a name="11356" class="Symbol"
      >{</a
      ><a name="11357" class="Argument"
      >x</a
      ><a name="11358"
      > </a
      ><a name="11359" class="Symbol"
      >=</a
      ><a name="11360"
      > </a
      ><a name="11361" href="StlcProp.html#11361" class="Bound"
      >x</a
      ><a name="11362" class="Symbol"
      >}</a
      ><a name="11363"
      > </a
      ><a name="11364" href="StlcProp.html#11364" class="Bound"
      >t&#8242;&#8758;A</a
      ><a name="11368" class="Symbol"
      >)</a
      ><a name="11369"
      > </a
      ><a name="11370" class="Symbol"
      >{</a
      ><a name="11371" href="StlcProp.html#11371" class="Bound"
      >y</a
      ><a name="11372" class="Symbol"
      >}</a
      ><a name="11373"
      > </a
      ><a name="11374" class="Symbol"
      >(</a
      ><a name="11375" href="StlcProp.html#7110" class="InductiveConstructor"
      >abs</a
      ><a name="11378"
      > </a
      ><a name="11379" href="StlcProp.html#11379" class="Bound"
      >x&#8800;y</a
      ><a name="11382"
      > </a
      ><a name="11383" href="StlcProp.html#11383" class="Bound"
      >y&#8712;t&#8242;</a
      ><a name="11387" class="Symbol"
      >)</a
      ><a name="11388"
      > </a
      ><a name="11389" class="Keyword"
      >with</a
      ><a name="11393"
      > </a
      ><a name="11394" href="StlcProp.html#8362" class="Function"
      >freeInCtxt</a
      ><a name="11404"
      > </a
      ><a name="11405" href="StlcProp.html#11383" class="Bound"
      >y&#8712;t&#8242;</a
      ><a name="11409"
      > </a
      ><a name="11410" href="StlcProp.html#11364" class="Bound"
      >t&#8242;&#8758;A</a
      ><a name="11414"
      >
</a
      ><a name="11415" href="StlcProp.html#10867" class="Function"
      >&#8709;&#8866;-closed&#8242;</a
      ><a name="11425"
      > </a
      ><a name="11426" class="Symbol"
      >(</a
      ><a name="11427" class="InductiveConstructor"
      >abs</a
      ><a name="11430"
      > </a
      ><a name="11431" class="Symbol"
      >{</a
      ><a name="11432" class="Argument"
      >x</a
      ><a name="11433"
      > </a
      ><a name="11434" class="Symbol"
      >=</a
      ><a name="11435"
      > </a
      ><a name="11436" href="StlcProp.html#11436" class="Bound"
      >x</a
      ><a name="11437" class="Symbol"
      >}</a
      ><a name="11438"
      > </a
      ><a name="11439" href="StlcProp.html#11439" class="Bound"
      >t&#8242;&#8758;A</a
      ><a name="11443" class="Symbol"
      >)</a
      ><a name="11444"
      > </a
      ><a name="11445" class="Symbol"
      >{</a
      ><a name="11446" href="StlcProp.html#11446" class="Bound"
      >y</a
      ><a name="11447" class="Symbol"
      >}</a
      ><a name="11448"
      > </a
      ><a name="11449" class="Symbol"
      >(</a
      ><a name="11450" class="InductiveConstructor"
      >abs</a
      ><a name="11453"
      > </a
      ><a name="11454" href="StlcProp.html#11454" class="Bound"
      >x&#8800;y</a
      ><a name="11457"
      > </a
      ><a name="11458" href="StlcProp.html#11458" class="Bound"
      >y&#8712;t&#8242;</a
      ><a name="11462" class="Symbol"
      >)</a
      ><a name="11463"
      > </a
      ><a name="11464" class="Symbol"
      >|</a
      ><a name="11465"
      > </a
      ><a name="11466" href="StlcProp.html#11466" class="Bound"
      >A</a
      ><a name="11467"
      > </a
      ><a name="11468" href="https://agda.github.io/agda-stdlib/Data.Product.html#509" class="InductiveConstructor Operator"
      >,</a
      ><a name="11469"
      > </a
      ><a name="11470" href="StlcProp.html#11470" class="Bound"
      >y&#8758;A</a
      ><a name="11473"
      > </a
      ><a name="11474" class="Keyword"
      >with</a
      ><a name="11478"
      > </a
      ><a name="11479" href="StlcProp.html#11436" class="Bound"
      >x</a
      ><a name="11480"
      > </a
      ><a name="11481" href="Maps.html#2454" class="Function Operator"
      >&#8799;</a
      ><a name="11482"
      > </a
      ><a name="11483" href="StlcProp.html#11446" class="Bound"
      >y</a
      ><a name="11484"
      >
</a
      ><a name="11485" href="StlcProp.html#10867" class="Function"
      >&#8709;&#8866;-closed&#8242;</a
      ><a name="11495"
      > </a
      ><a name="11496" class="Symbol"
      >(</a
      ><a name="11497" class="InductiveConstructor"
      >abs</a
      ><a name="11500"
      > </a
      ><a name="11501" class="Symbol"
      >{</a
      ><a name="11502" class="Argument"
      >x</a
      ><a name="11503"
      > </a
      ><a name="11504" class="Symbol"
      >=</a
      ><a name="11505"
      > </a
      ><a name="11506" href="StlcProp.html#11506" class="Bound"
      >x</a
      ><a name="11507" class="Symbol"
      >}</a
      ><a name="11508"
      > </a
      ><a name="11509" href="StlcProp.html#11509" class="Bound"
      >t&#8242;&#8758;A</a
      ><a name="11513" class="Symbol"
      >)</a
      ><a name="11514"
      > </a
      ><a name="11515" class="Symbol"
      >{</a
      ><a name="11516" href="StlcProp.html#11516" class="Bound"
      >y</a
      ><a name="11517" class="Symbol"
      >}</a
      ><a name="11518"
      > </a
      ><a name="11519" class="Symbol"
      >(</a
      ><a name="11520" class="InductiveConstructor"
      >abs</a
      ><a name="11523"
      > </a
      ><a name="11524" href="StlcProp.html#11524" class="Bound"
      >x&#8800;y</a
      ><a name="11527"
      > </a
      ><a name="11528" href="StlcProp.html#11528" class="Bound"
      >y&#8712;t&#8242;</a
      ><a name="11532" class="Symbol"
      >)</a
      ><a name="11533"
      > </a
      ><a name="11534" class="Symbol"
      >|</a
      ><a name="11535"
      > </a
      ><a name="11536" href="StlcProp.html#11536" class="Bound"
      >A</a
      ><a name="11537"
      > </a
      ><a name="11538" href="https://agda.github.io/agda-stdlib/Data.Product.html#509" class="InductiveConstructor Operator"
      >,</a
      ><a name="11539"
      > </a
      ><a name="11540" href="StlcProp.html#11540" class="Bound"
      >y&#8758;A</a
      ><a name="11543"
      > </a
      ><a name="11544" class="Symbol"
      >|</a
      ><a name="11545"
      > </a
      ><a name="11546" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#520" class="InductiveConstructor"
      >yes</a
      ><a name="11549"
      > </a
      ><a name="11550" href="StlcProp.html#11550" class="Bound"
      >x=y</a
      ><a name="11553"
      > </a
      ><a name="11554" class="Symbol"
      >=</a
      ><a name="11555"
      > </a
      ><a name="11556" href="StlcProp.html#11524" class="Bound"
      >x&#8800;y</a
      ><a name="11559"
      > </a
      ><a name="11560" href="StlcProp.html#11550" class="Bound"
      >x=y</a
      ><a name="11563"
      >
</a
      ><a name="11564" href="StlcProp.html#10867" class="Function"
      >&#8709;&#8866;-closed&#8242;</a
      ><a name="11574"
      > </a
      ><a name="11575" class="Symbol"
      >(</a
      ><a name="11576" class="InductiveConstructor"
      >abs</a
      ><a name="11579"
      > </a
      ><a name="11580" class="Symbol"
      >{</a
      ><a name="11581" class="Argument"
      >x</a
      ><a name="11582"
      > </a
      ><a name="11583" class="Symbol"
      >=</a
      ><a name="11584"
      > </a
      ><a name="11585" href="StlcProp.html#11585" class="Bound"
      >x</a
      ><a name="11586" class="Symbol"
      >}</a
      ><a name="11587"
      > </a
      ><a name="11588" href="StlcProp.html#11588" class="Bound"
      >t&#8242;&#8758;A</a
      ><a name="11592" class="Symbol"
      >)</a
      ><a name="11593"
      > </a
      ><a name="11594" class="Symbol"
      >{</a
      ><a name="11595" href="StlcProp.html#11595" class="Bound"
      >y</a
      ><a name="11596" class="Symbol"
      >}</a
      ><a name="11597"
      > </a
      ><a name="11598" class="Symbol"
      >(</a
      ><a name="11599" class="InductiveConstructor"
      >abs</a
      ><a name="11602"
      > </a
      ><a name="11603" href="StlcProp.html#11603" class="Bound"
      >x&#8800;y</a
      ><a name="11606"
      > </a
      ><a name="11607" href="StlcProp.html#11607" class="Bound"
      >y&#8712;t&#8242;</a
      ><a name="11611" class="Symbol"
      >)</a
      ><a name="11612"
      > </a
      ><a name="11613" class="Symbol"
      >|</a
      ><a name="11614"
      > </a
      ><a name="11615" href="StlcProp.html#11615" class="Bound"
      >A</a
      ><a name="11616"
      > </a
      ><a name="11617" href="https://agda.github.io/agda-stdlib/Data.Product.html#509" class="InductiveConstructor Operator"
      >,</a
      ><a name="11618"
      > </a
      ><a name="11619" class="Symbol"
      >()</a
      ><a name="11621"
      >  </a
      ><a name="11623" class="Symbol"
      >|</a
      ><a name="11624"
      > </a
      ><a name="11625" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#547" class="InductiveConstructor"
      >no</a
      ><a name="11627"
      >  </a
      ><a name="11629" class="Symbol"
      >_</a
      >
</pre><!--{% endraw %}-->
</div>

Sometimes, when we have a proof $$\Gamma\vdash t : A$$, we will need to
replace $$\Gamma$$ by a different context $$\Gamma'$$.  When is it safe
to do this?  Intuitively, it must at least be the case that
$$\Gamma'$$ assigns the same types as $$\Gamma$$ to all the variables
that appear free in $$t$$. In fact, this is the only condition that
is needed.

<!--{% raw %}--><pre class="Agda">
<a name="12017" href="StlcProp.html#12017" class="Function"
      >replaceCtxt</a
      ><a name="12028"
      > </a
      ><a name="12029" class="Symbol"
      >:</a
      ><a name="12030"
      > </a
      ><a name="12031" class="Symbol"
      >&#8704;</a
      ><a name="12032"
      > </a
      ><a name="12033" class="Symbol"
      >{</a
      ><a name="12034" href="StlcProp.html#12034" class="Bound"
      >&#915;</a
      ><a name="12035"
      > </a
      ><a name="12036" href="StlcProp.html#12036" class="Bound"
      >&#915;&#8242;</a
      ><a name="12038"
      > </a
      ><a name="12039" href="StlcProp.html#12039" class="Bound"
      >t</a
      ><a name="12040"
      > </a
      ><a name="12041" href="StlcProp.html#12041" class="Bound"
      >A</a
      ><a name="12042" class="Symbol"
      >}</a
      ><a name="12043"
      >
            </a
      ><a name="12056" class="Symbol"
      >&#8594;</a
      ><a name="12057"
      > </a
      ><a name="12058" class="Symbol"
      >(&#8704;</a
      ><a name="12060"
      > </a
      ><a name="12061" class="Symbol"
      >{</a
      ><a name="12062" href="StlcProp.html#12062" class="Bound"
      >x</a
      ><a name="12063" class="Symbol"
      >}</a
      ><a name="12064"
      > </a
      ><a name="12065" class="Symbol"
      >&#8594;</a
      ><a name="12066"
      > </a
      ><a name="12067" href="StlcProp.html#12062" class="Bound"
      >x</a
      ><a name="12068"
      > </a
      ><a name="12069" href="StlcProp.html#7047" class="Datatype Operator"
      >FreeIn</a
      ><a name="12075"
      > </a
      ><a name="12076" href="StlcProp.html#12039" class="Bound"
      >t</a
      ><a name="12077"
      > </a
      ><a name="12078" class="Symbol"
      >&#8594;</a
      ><a name="12079"
      > </a
      ><a name="12080" href="StlcProp.html#12034" class="Bound"
      >&#915;</a
      ><a name="12081"
      > </a
      ><a name="12082" href="StlcProp.html#12062" class="Bound"
      >x</a
      ><a name="12083"
      > </a
      ><a name="12084" href="Agda.Builtin.Equality.html#55" class="Datatype Operator"
      >&#8801;</a
      ><a name="12085"
      > </a
      ><a name="12086" href="StlcProp.html#12036" class="Bound"
      >&#915;&#8242;</a
      ><a name="12088"
      > </a
      ><a name="12089" href="StlcProp.html#12062" class="Bound"
      >x</a
      ><a name="12090" class="Symbol"
      >)</a
      ><a name="12091"
      >
            </a
      ><a name="12104" class="Symbol"
      >&#8594;</a
      ><a name="12105"
      > </a
      ><a name="12106" href="StlcProp.html#12034" class="Bound"
      >&#915;</a
      ><a name="12107"
      >  </a
      ><a name="12109" href="Stlc.html#19231" class="Datatype Operator"
      >&#8866;</a
      ><a name="12110"
      > </a
      ><a name="12111" href="StlcProp.html#12039" class="Bound"
      >t</a
      ><a name="12112"
      > </a
      ><a name="12113" href="Stlc.html#19231" class="Datatype Operator"
      >&#8758;</a
      ><a name="12114"
      > </a
      ><a name="12115" href="StlcProp.html#12041" class="Bound"
      >A</a
      ><a name="12116"
      >
            </a
      ><a name="12129" class="Symbol"
      >&#8594;</a
      ><a name="12130"
      > </a
      ><a name="12131" href="StlcProp.html#12036" class="Bound"
      >&#915;&#8242;</a
      ><a name="12133"
      > </a
      ><a name="12134" href="Stlc.html#19231" class="Datatype Operator"
      >&#8866;</a
      ><a name="12135"
      > </a
      ><a name="12136" href="StlcProp.html#12039" class="Bound"
      >t</a
      ><a name="12137"
      > </a
      ><a name="12138" href="Stlc.html#19231" class="Datatype Operator"
      >&#8758;</a
      ><a name="12139"
      > </a
      ><a name="12140" href="StlcProp.html#12041" class="Bound"
      >A</a
      >
</pre><!--{% endraw %}-->

_Proof_: By induction on the derivation of
$$\Gamma \vdash t \in T$$.

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
    $$\Gamma \vdash t_1 : A\to T$$ and $$\Gamma \vdash t_2 : A$$.
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

<!--{% raw %}--><pre class="Agda">
<a name="14445" href="StlcProp.html#12017" class="Function"
      >replaceCtxt</a
      ><a name="14456"
      > </a
      ><a name="14457" href="StlcProp.html#14457" class="Bound"
      >f</a
      ><a name="14458"
      > </a
      ><a name="14459" class="Symbol"
      >(</a
      ><a name="14460" href="Stlc.html#19275" class="InductiveConstructor"
      >var</a
      ><a name="14463"
      > </a
      ><a name="14464" href="StlcProp.html#14464" class="Bound"
      >x</a
      ><a name="14465"
      > </a
      ><a name="14466" href="StlcProp.html#14466" class="Bound"
      >x&#8758;A</a
      ><a name="14469" class="Symbol"
      >)</a
      ><a name="14470"
      > </a
      ><a name="14471" class="Keyword"
      >rewrite</a
      ><a name="14478"
      > </a
      ><a name="14479" href="StlcProp.html#14457" class="Bound"
      >f</a
      ><a name="14480"
      > </a
      ><a name="14481" href="StlcProp.html#7086" class="InductiveConstructor"
      >var</a
      ><a name="14484"
      > </a
      ><a name="14485" class="Symbol"
      >=</a
      ><a name="14486"
      > </a
      ><a name="14487" href="Stlc.html#19275" class="InductiveConstructor"
      >var</a
      ><a name="14490"
      > </a
      ><a name="14491" href="StlcProp.html#14464" class="Bound"
      >x</a
      ><a name="14492"
      > </a
      ><a name="14493" href="StlcProp.html#14466" class="Bound"
      >x&#8758;A</a
      ><a name="14496"
      >
</a
      ><a name="14497" href="StlcProp.html#12017" class="Function"
      >replaceCtxt</a
      ><a name="14508"
      > </a
      ><a name="14509" href="StlcProp.html#14509" class="Bound"
      >f</a
      ><a name="14510"
      > </a
      ><a name="14511" class="Symbol"
      >(</a
      ><a name="14512" href="Stlc.html#19484" class="InductiveConstructor"
      >app</a
      ><a name="14515"
      > </a
      ><a name="14516" href="StlcProp.html#14516" class="Bound"
      >t&#8321;&#8758;A&#8658;B</a
      ><a name="14522"
      > </a
      ><a name="14523" href="StlcProp.html#14523" class="Bound"
      >t&#8322;&#8758;A</a
      ><a name="14527" class="Symbol"
      >)</a
      ><a name="14528"
      >
  </a
      ><a name="14531" class="Symbol"
      >=</a
      ><a name="14532"
      > </a
      ><a name="14533" href="Stlc.html#19484" class="InductiveConstructor"
      >app</a
      ><a name="14536"
      > </a
      ><a name="14537" class="Symbol"
      >(</a
      ><a name="14538" href="StlcProp.html#12017" class="Function"
      >replaceCtxt</a
      ><a name="14549"
      > </a
      ><a name="14550" class="Symbol"
      >(</a
      ><a name="14551" href="StlcProp.html#14509" class="Bound"
      >f</a
      ><a name="14552"
      > </a
      ><a name="14553" href="https://agda.github.io/agda-stdlib/Function.html#713" class="Function Operator"
      >&#8728;</a
      ><a name="14554"
      > </a
      ><a name="14555" href="StlcProp.html#7171" class="InductiveConstructor"
      >app1</a
      ><a name="14559" class="Symbol"
      >)</a
      ><a name="14560"
      > </a
      ><a name="14561" href="StlcProp.html#14516" class="Bound"
      >t&#8321;&#8758;A&#8658;B</a
      ><a name="14567" class="Symbol"
      >)</a
      ><a name="14568"
      > </a
      ><a name="14569" class="Symbol"
      >(</a
      ><a name="14570" href="StlcProp.html#12017" class="Function"
      >replaceCtxt</a
      ><a name="14581"
      > </a
      ><a name="14582" class="Symbol"
      >(</a
      ><a name="14583" href="StlcProp.html#14509" class="Bound"
      >f</a
      ><a name="14584"
      > </a
      ><a name="14585" href="https://agda.github.io/agda-stdlib/Function.html#713" class="Function Operator"
      >&#8728;</a
      ><a name="14586"
      > </a
      ><a name="14587" href="StlcProp.html#7225" class="InductiveConstructor"
      >app2</a
      ><a name="14591" class="Symbol"
      >)</a
      ><a name="14592"
      > </a
      ><a name="14593" href="StlcProp.html#14523" class="Bound"
      >t&#8322;&#8758;A</a
      ><a name="14597" class="Symbol"
      >)</a
      ><a name="14598"
      >
</a
      ><a name="14599" href="StlcProp.html#12017" class="Function"
      >replaceCtxt</a
      ><a name="14610"
      > </a
      ><a name="14611" class="Symbol"
      >{</a
      ><a name="14612" href="StlcProp.html#14612" class="Bound"
      >&#915;</a
      ><a name="14613" class="Symbol"
      >}</a
      ><a name="14614"
      > </a
      ><a name="14615" class="Symbol"
      >{</a
      ><a name="14616" href="StlcProp.html#14616" class="Bound"
      >&#915;&#8242;</a
      ><a name="14618" class="Symbol"
      >}</a
      ><a name="14619"
      > </a
      ><a name="14620" href="StlcProp.html#14620" class="Bound"
      >f</a
      ><a name="14621"
      > </a
      ><a name="14622" class="Symbol"
      >(</a
      ><a name="14623" href="Stlc.html#19368" class="InductiveConstructor"
      >abs</a
      ><a name="14626"
      > </a
      ><a name="14627" class="Symbol"
      >{</a
      ><a name="14628" class="DottedPattern Symbol"
      >.</a
      ><a name="14629" href="StlcProp.html#14612" class="DottedPattern Bound"
      >&#915;</a
      ><a name="14630" class="Symbol"
      >}</a
      ><a name="14631"
      > </a
      ><a name="14632" class="Symbol"
      >{</a
      ><a name="14633" href="StlcProp.html#14633" class="Bound"
      >x</a
      ><a name="14634" class="Symbol"
      >}</a
      ><a name="14635"
      > </a
      ><a name="14636" class="Symbol"
      >{</a
      ><a name="14637" href="StlcProp.html#14637" class="Bound"
      >A</a
      ><a name="14638" class="Symbol"
      >}</a
      ><a name="14639"
      > </a
      ><a name="14640" class="Symbol"
      >{</a
      ><a name="14641" href="StlcProp.html#14641" class="Bound"
      >B</a
      ><a name="14642" class="Symbol"
      >}</a
      ><a name="14643"
      > </a
      ><a name="14644" class="Symbol"
      >{</a
      ><a name="14645" href="StlcProp.html#14645" class="Bound"
      >t&#8242;</a
      ><a name="14647" class="Symbol"
      >}</a
      ><a name="14648"
      > </a
      ><a name="14649" href="StlcProp.html#14649" class="Bound"
      >t&#8242;&#8758;B</a
      ><a name="14653" class="Symbol"
      >)</a
      ><a name="14654"
      >
  </a
      ><a name="14657" class="Symbol"
      >=</a
      ><a name="14658"
      > </a
      ><a name="14659" href="Stlc.html#19368" class="InductiveConstructor"
      >abs</a
      ><a name="14662"
      > </a
      ><a name="14663" class="Symbol"
      >(</a
      ><a name="14664" href="StlcProp.html#12017" class="Function"
      >replaceCtxt</a
      ><a name="14675"
      > </a
      ><a name="14676" href="StlcProp.html#14697" class="Function"
      >f&#8242;</a
      ><a name="14678"
      > </a
      ><a name="14679" href="StlcProp.html#14649" class="Bound"
      >t&#8242;&#8758;B</a
      ><a name="14683" class="Symbol"
      >)</a
      ><a name="14684"
      >
  </a
      ><a name="14687" class="Keyword"
      >where</a
      ><a name="14692"
      >
    </a
      ><a name="14697" href="StlcProp.html#14697" class="Function"
      >f&#8242;</a
      ><a name="14699"
      > </a
      ><a name="14700" class="Symbol"
      >:</a
      ><a name="14701"
      > </a
      ><a name="14702" class="Symbol"
      >&#8704;</a
      ><a name="14703"
      > </a
      ><a name="14704" class="Symbol"
      >{</a
      ><a name="14705" href="StlcProp.html#14705" class="Bound"
      >y</a
      ><a name="14706" class="Symbol"
      >}</a
      ><a name="14707"
      > </a
      ><a name="14708" class="Symbol"
      >&#8594;</a
      ><a name="14709"
      > </a
      ><a name="14710" href="StlcProp.html#14705" class="Bound"
      >y</a
      ><a name="14711"
      > </a
      ><a name="14712" href="StlcProp.html#7047" class="Datatype Operator"
      >FreeIn</a
      ><a name="14718"
      > </a
      ><a name="14719" href="StlcProp.html#14645" class="Bound"
      >t&#8242;</a
      ><a name="14721"
      > </a
      ><a name="14722" class="Symbol"
      >&#8594;</a
      ><a name="14723"
      > </a
      ><a name="14724" class="Symbol"
      >(</a
      ><a name="14725" href="StlcProp.html#14612" class="Bound"
      >&#915;</a
      ><a name="14726"
      > </a
      ><a name="14727" href="Stlc.html#18330" class="Function Operator"
      >,</a
      ><a name="14728"
      > </a
      ><a name="14729" href="StlcProp.html#14633" class="Bound"
      >x</a
      ><a name="14730"
      > </a
      ><a name="14731" href="Stlc.html#18330" class="Function Operator"
      >&#8758;</a
      ><a name="14732"
      > </a
      ><a name="14733" href="StlcProp.html#14637" class="Bound"
      >A</a
      ><a name="14734" class="Symbol"
      >)</a
      ><a name="14735"
      > </a
      ><a name="14736" href="StlcProp.html#14705" class="Bound"
      >y</a
      ><a name="14737"
      > </a
      ><a name="14738" href="Agda.Builtin.Equality.html#55" class="Datatype Operator"
      >&#8801;</a
      ><a name="14739"
      > </a
      ><a name="14740" class="Symbol"
      >(</a
      ><a name="14741" href="StlcProp.html#14616" class="Bound"
      >&#915;&#8242;</a
      ><a name="14743"
      > </a
      ><a name="14744" href="Stlc.html#18330" class="Function Operator"
      >,</a
      ><a name="14745"
      > </a
      ><a name="14746" href="StlcProp.html#14633" class="Bound"
      >x</a
      ><a name="14747"
      > </a
      ><a name="14748" href="Stlc.html#18330" class="Function Operator"
      >&#8758;</a
      ><a name="14749"
      > </a
      ><a name="14750" href="StlcProp.html#14637" class="Bound"
      >A</a
      ><a name="14751" class="Symbol"
      >)</a
      ><a name="14752"
      > </a
      ><a name="14753" href="StlcProp.html#14705" class="Bound"
      >y</a
      ><a name="14754"
      >
    </a
      ><a name="14759" href="StlcProp.html#14697" class="Function"
      >f&#8242;</a
      ><a name="14761"
      > </a
      ><a name="14762" class="Symbol"
      >{</a
      ><a name="14763" href="StlcProp.html#14763" class="Bound"
      >y</a
      ><a name="14764" class="Symbol"
      >}</a
      ><a name="14765"
      > </a
      ><a name="14766" href="StlcProp.html#14766" class="Bound"
      >y&#8712;t&#8242;</a
      ><a name="14770"
      > </a
      ><a name="14771" class="Keyword"
      >with</a
      ><a name="14775"
      > </a
      ><a name="14776" href="StlcProp.html#14633" class="Bound"
      >x</a
      ><a name="14777"
      > </a
      ><a name="14778" href="Maps.html#2454" class="Function Operator"
      >&#8799;</a
      ><a name="14779"
      > </a
      ><a name="14780" href="StlcProp.html#14763" class="Bound"
      >y</a
      ><a name="14781"
      >
    </a
      ><a name="14786" class="Symbol"
      >...</a
      ><a name="14789"
      > </a
      ><a name="14790" class="Symbol"
      >|</a
      ><a name="14791"
      > </a
      ><a name="14792" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#520" class="InductiveConstructor"
      >yes</a
      ><a name="14795"
      > </a
      ><a name="14796" class="Symbol"
      >_</a
      ><a name="14797"
      >   </a
      ><a name="14800" class="Symbol"
      >=</a
      ><a name="14801"
      > </a
      ><a name="14802" href="Agda.Builtin.Equality.html#112" class="InductiveConstructor"
      >refl</a
      ><a name="14806"
      >
    </a
      ><a name="14811" class="Symbol"
      >...</a
      ><a name="14814"
      > </a
      ><a name="14815" class="Symbol"
      >|</a
      ><a name="14816"
      > </a
      ><a name="14817" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#547" class="InductiveConstructor"
      >no</a
      ><a name="14819"
      >  </a
      ><a name="14821" href="StlcProp.html#14821" class="Bound"
      >x&#8800;y</a
      ><a name="14824"
      > </a
      ><a name="14825" class="Symbol"
      >=</a
      ><a name="14826"
      > </a
      ><a name="14827" href="StlcProp.html#14620" class="Bound"
      >f</a
      ><a name="14828"
      > </a
      ><a name="14829" class="Symbol"
      >(</a
      ><a name="14830" href="StlcProp.html#7110" class="InductiveConstructor"
      >abs</a
      ><a name="14833"
      > </a
      ><a name="14834" href="StlcProp.html#14821" class="Bound"
      >x&#8800;y</a
      ><a name="14837"
      > </a
      ><a name="14838" href="StlcProp.html#14766" class="Bound"
      >y&#8712;t&#8242;</a
      ><a name="14842" class="Symbol"
      >)</a
      ><a name="14843"
      >
</a
      ><a name="14844" href="StlcProp.html#12017" class="Function"
      >replaceCtxt</a
      ><a name="14855"
      > </a
      ><a name="14856" class="Symbol"
      >_</a
      ><a name="14857"
      > </a
      ><a name="14858" href="Stlc.html#19618" class="InductiveConstructor"
      >true</a
      ><a name="14862"
      >  </a
      ><a name="14864" class="Symbol"
      >=</a
      ><a name="14865"
      > </a
      ><a name="14866" href="Stlc.html#19618" class="InductiveConstructor"
      >true</a
      ><a name="14870"
      >
</a
      ><a name="14871" href="StlcProp.html#12017" class="Function"
      >replaceCtxt</a
      ><a name="14882"
      > </a
      ><a name="14883" class="Symbol"
      >_</a
      ><a name="14884"
      > </a
      ><a name="14885" href="Stlc.html#19677" class="InductiveConstructor"
      >false</a
      ><a name="14890"
      > </a
      ><a name="14891" class="Symbol"
      >=</a
      ><a name="14892"
      > </a
      ><a name="14893" href="Stlc.html#19677" class="InductiveConstructor"
      >false</a
      ><a name="14898"
      >
</a
      ><a name="14899" href="StlcProp.html#12017" class="Function"
      >replaceCtxt</a
      ><a name="14910"
      > </a
      ><a name="14911" href="StlcProp.html#14911" class="Bound"
      >f</a
      ><a name="14912"
      > </a
      ><a name="14913" class="Symbol"
      >(</a
      ><a name="14914" href="Stlc.html#19736" class="InductiveConstructor Operator"
      >if</a
      ><a name="14916"
      > </a
      ><a name="14917" href="StlcProp.html#14917" class="Bound"
      >t&#8321;&#8758;bool</a
      ><a name="14924"
      > </a
      ><a name="14925" href="Stlc.html#19736" class="InductiveConstructor Operator"
      >then</a
      ><a name="14929"
      > </a
      ><a name="14930" href="StlcProp.html#14930" class="Bound"
      >t&#8322;&#8758;A</a
      ><a name="14934"
      > </a
      ><a name="14935" href="Stlc.html#19736" class="InductiveConstructor Operator"
      >else</a
      ><a name="14939"
      > </a
      ><a name="14940" href="StlcProp.html#14940" class="Bound"
      >t&#8323;&#8758;A</a
      ><a name="14944" class="Symbol"
      >)</a
      ><a name="14945"
      >
  </a
      ><a name="14948" class="Symbol"
      >=</a
      ><a name="14949"
      > </a
      ><a name="14950" href="Stlc.html#19736" class="InductiveConstructor Operator"
      >if</a
      ><a name="14952"
      >   </a
      ><a name="14955" href="StlcProp.html#12017" class="Function"
      >replaceCtxt</a
      ><a name="14966"
      > </a
      ><a name="14967" class="Symbol"
      >(</a
      ><a name="14968" href="StlcProp.html#14911" class="Bound"
      >f</a
      ><a name="14969"
      > </a
      ><a name="14970" href="https://agda.github.io/agda-stdlib/Function.html#713" class="Function Operator"
      >&#8728;</a
      ><a name="14971"
      > </a
      ><a name="14972" href="StlcProp.html#7279" class="InductiveConstructor"
      >if1</a
      ><a name="14975" class="Symbol"
      >)</a
      ><a name="14976"
      > </a
      ><a name="14977" href="StlcProp.html#14917" class="Bound"
      >t&#8321;&#8758;bool</a
      ><a name="14984"
      >
    </a
      ><a name="14989" href="Stlc.html#19736" class="InductiveConstructor Operator"
      >then</a
      ><a name="14993"
      > </a
      ><a name="14994" href="StlcProp.html#12017" class="Function"
      >replaceCtxt</a
      ><a name="15005"
      > </a
      ><a name="15006" class="Symbol"
      >(</a
      ><a name="15007" href="StlcProp.html#14911" class="Bound"
      >f</a
      ><a name="15008"
      > </a
      ><a name="15009" href="https://agda.github.io/agda-stdlib/Function.html#713" class="Function Operator"
      >&#8728;</a
      ><a name="15010"
      > </a
      ><a name="15011" href="StlcProp.html#7350" class="InductiveConstructor"
      >if2</a
      ><a name="15014" class="Symbol"
      >)</a
      ><a name="15015"
      > </a
      ><a name="15016" href="StlcProp.html#14930" class="Bound"
      >t&#8322;&#8758;A</a
      ><a name="15020"
      >
    </a
      ><a name="15025" href="Stlc.html#19736" class="InductiveConstructor Operator"
      >else</a
      ><a name="15029"
      > </a
      ><a name="15030" href="StlcProp.html#12017" class="Function"
      >replaceCtxt</a
      ><a name="15041"
      > </a
      ><a name="15042" class="Symbol"
      >(</a
      ><a name="15043" href="StlcProp.html#14911" class="Bound"
      >f</a
      ><a name="15044"
      > </a
      ><a name="15045" href="https://agda.github.io/agda-stdlib/Function.html#713" class="Function Operator"
      >&#8728;</a
      ><a name="15046"
      > </a
      ><a name="15047" href="StlcProp.html#7421" class="InductiveConstructor"
      >if3</a
      ><a name="15050" class="Symbol"
      >)</a
      ><a name="15051"
      > </a
      ><a name="15052" href="StlcProp.html#14940" class="Bound"
      >t&#8323;&#8758;A</a
      >
</pre><!--{% endraw %}-->

Now we come to the conceptual heart of the proof that reduction
preserves types -- namely, the observation that _substitution_
preserves types.

Formally, the so-called _Substitution Lemma_ says this: Suppose we
have a term $$t$$ with a free variable $$x$$, and suppose we've been
able to assign a type $$T$$ to $$t$$ under the assumption that $$x$$ has
some type $$U$$.  Also, suppose that we have some other term $$v$$ and
that we've shown that $$v$$ has type $$U$$.  Then, since $$v$$ satisfies
the assumption we made about $$x$$ when typing $$t$$, we should be
able to substitute $$v$$ for each of the occurrences of $$x$$ in $$t$$
and obtain a new term that still has type $$T$$.

_Lemma_: If $$\Gamma,x:U \vdash t : T$$ and $$\vdash v : U$$, then
$$\Gamma \vdash [x:=v]t : T$$.

<!--{% raw %}--><pre class="Agda">
<a name="15867" href="StlcProp.html#15867" class="Function"
      >[:=]-preserves-&#8866;</a
      ><a name="15883"
      > </a
      ><a name="15884" class="Symbol"
      >:</a
      ><a name="15885"
      > </a
      ><a name="15886" class="Symbol"
      >&#8704;</a
      ><a name="15887"
      > </a
      ><a name="15888" class="Symbol"
      >{</a
      ><a name="15889" href="StlcProp.html#15889" class="Bound"
      >&#915;</a
      ><a name="15890"
      > </a
      ><a name="15891" href="StlcProp.html#15891" class="Bound"
      >x</a
      ><a name="15892"
      > </a
      ><a name="15893" href="StlcProp.html#15893" class="Bound"
      >A</a
      ><a name="15894"
      > </a
      ><a name="15895" href="StlcProp.html#15895" class="Bound"
      >t</a
      ><a name="15896"
      > </a
      ><a name="15897" href="StlcProp.html#15897" class="Bound"
      >v</a
      ><a name="15898"
      > </a
      ><a name="15899" href="StlcProp.html#15899" class="Bound"
      >B</a
      ><a name="15900" class="Symbol"
      >}</a
      ><a name="15901"
      >
                 </a
      ><a name="15919" class="Symbol"
      >&#8594;</a
      ><a name="15920"
      > </a
      ><a name="15921" href="Stlc.html#18299" class="Function"
      >&#8709;</a
      ><a name="15922"
      > </a
      ><a name="15923" href="Stlc.html#19231" class="Datatype Operator"
      >&#8866;</a
      ><a name="15924"
      > </a
      ><a name="15925" href="StlcProp.html#15897" class="Bound"
      >v</a
      ><a name="15926"
      > </a
      ><a name="15927" href="Stlc.html#19231" class="Datatype Operator"
      >&#8758;</a
      ><a name="15928"
      > </a
      ><a name="15929" href="StlcProp.html#15893" class="Bound"
      >A</a
      ><a name="15930"
      >
                 </a
      ><a name="15948" class="Symbol"
      >&#8594;</a
      ><a name="15949"
      > </a
      ><a name="15950" href="StlcProp.html#15889" class="Bound"
      >&#915;</a
      ><a name="15951"
      > </a
      ><a name="15952" href="Stlc.html#18330" class="Function Operator"
      >,</a
      ><a name="15953"
      > </a
      ><a name="15954" href="StlcProp.html#15891" class="Bound"
      >x</a
      ><a name="15955"
      > </a
      ><a name="15956" href="Stlc.html#18330" class="Function Operator"
      >&#8758;</a
      ><a name="15957"
      > </a
      ><a name="15958" href="StlcProp.html#15893" class="Bound"
      >A</a
      ><a name="15959"
      > </a
      ><a name="15960" href="Stlc.html#19231" class="Datatype Operator"
      >&#8866;</a
      ><a name="15961"
      > </a
      ><a name="15962" href="StlcProp.html#15895" class="Bound"
      >t</a
      ><a name="15963"
      > </a
      ><a name="15964" href="Stlc.html#19231" class="Datatype Operator"
      >&#8758;</a
      ><a name="15965"
      > </a
      ><a name="15966" href="StlcProp.html#15899" class="Bound"
      >B</a
      ><a name="15967"
      >
                 </a
      ><a name="15985" class="Symbol"
      >&#8594;</a
      ><a name="15986"
      > </a
      ><a name="15987" href="StlcProp.html#15889" class="Bound"
      >&#915;</a
      ><a name="15988"
      > </a
      ><a name="15989" href="Stlc.html#18330" class="Function Operator"
      >,</a
      ><a name="15990"
      > </a
      ><a name="15991" href="StlcProp.html#15891" class="Bound"
      >x</a
      ><a name="15992"
      > </a
      ><a name="15993" href="Stlc.html#18330" class="Function Operator"
      >&#8758;</a
      ><a name="15994"
      > </a
      ><a name="15995" href="StlcProp.html#15893" class="Bound"
      >A</a
      ><a name="15996"
      > </a
      ><a name="15997" href="Stlc.html#19231" class="Datatype Operator"
      >&#8866;</a
      ><a name="15998"
      > </a
      ><a name="15999" href="Stlc.html#12300" class="Function Operator"
      >[</a
      ><a name="16000"
      > </a
      ><a name="16001" href="StlcProp.html#15891" class="Bound"
      >x</a
      ><a name="16002"
      > </a
      ><a name="16003" href="Stlc.html#12300" class="Function Operator"
      >:=</a
      ><a name="16005"
      > </a
      ><a name="16006" href="StlcProp.html#15897" class="Bound"
      >v</a
      ><a name="16007"
      > </a
      ><a name="16008" href="Stlc.html#12300" class="Function Operator"
      >]</a
      ><a name="16009"
      > </a
      ><a name="16010" href="StlcProp.html#15895" class="Bound"
      >t</a
      ><a name="16011"
      > </a
      ><a name="16012" href="Stlc.html#19231" class="Datatype Operator"
      >&#8758;</a
      ><a name="16013"
      > </a
      ><a name="16014" href="StlcProp.html#15899" class="Bound"
      >B</a
      >
</pre><!--{% endraw %}-->

One technical subtlety in the statement of the lemma is that
we assign $$v$$ the type $$U$$ in the _empty_ context -- in other
words, we assume $$v$$ is closed.  This assumption considerably
simplifies the $$abs$$ case of the proof (compared to assuming
$$\Gamma \vdash v : U$$, which would be the other reasonable assumption
at this point) because the context invariance lemma then tells us
that $$v$$ has type $$U$$ in any context at all -- we don't have to
worry about free variables in $$v$$ clashing with the variable being
introduced into the context by $$abs$$.

The substitution lemma can be viewed as a kind of "commutation"
property.  Intuitively, it says that substitution and typing can
be done in either order: we can either assign types to the terms
$$t$$ and $$v$$ separately (under suitable contexts) and then combine
them using substitution, or we can substitute first and then
assign a type to $$ $$x:=v$$ t $$ -- the result is the same either
way.

_Proof_: We show, by induction on $$t$$, that for all $$T$$ and
$$\Gamma$$, if $$\Gamma,x:U \vdash t : T$$ and $$\vdash v : U$$, then $$\Gamma
\vdash $$x:=v$$t : T$$.

  - If $$t$$ is a variable there are two cases to consider,
    depending on whether $$t$$ is $$x$$ or some other variable.

      - If $$t = x$$, then from the fact that $$\Gamma, x:U \vdash x :
        T$$ we conclude that $$U = T$$.  We must show that $$$$x:=v$$x =
        v$$ has type $$T$$ under $$\Gamma$$, given the assumption that
        $$v$$ has type $$U = T$$ under the empty context.  This
        follows from context invariance: if a closed term has type
        $$T$$ in the empty context, it has that type in any context.

      - If $$t$$ is some variable $$y$$ that is not equal to $$x$$, then
        we need only note that $$y$$ has the same type under $$\Gamma,
        x:U$$ as under $$\Gamma$$.

  - If $$t$$ is an abstraction $$\lambda y:T_11. t_12$$, then the IH tells us,
    for all $$\Gamma'$$ and $$T'$$, that if $$\Gamma',x:U \vdash t_12 : T'$$
    and $$\vdash v : U$$, then $$\Gamma' \vdash $$x:=v$$t_12 : T'$$.

    The substitution in the conclusion behaves differently
    depending on whether $$x$$ and $$y$$ are the same variable.

    First, suppose $$x = y$$.  Then, by the definition of
    substitution, $$[x:=v]t = t$$, so we just need to show $$\Gamma \vdash
    t : T$$.  But we know $$\Gamma,x:U \vdash t : T$$, and, since $$y$$
    does not appear free in $$\lambda y:T_11. t_12$$, the context invariance
    lemma yields $$\Gamma \vdash t : T$$.

    Second, suppose $$x <> y$$.  We know $$\Gamma,x:U,y:T_11 \vdash t_12 :
    T_12$$ by inversion of the typing relation, from which
    $$\Gamma,y:T_11,x:U \vdash t_12 : T_12$$ follows by the context
    invariance lemma, so the IH applies, giving us $$\Gamma,y:T_11 \vdash
    $$x:=v$$t_12 : T_12$$.  By $$abs$$, $$\Gamma \vdash \lambda y:T_11. $$x:=v$$t_12
    : T_11→T_12$$, and by the definition of substitution (noting
    that $$x <> y$$), $$\Gamma \vdash \lambda y:T_11. $$x:=v$$t_12 : T_11→T_12$$ as
    required.

  - If $$t$$ is an application $$t_1 t_2$$, the result follows
    straightforwardly from the definition of substitution and the
    induction hypotheses.

  - The remaining cases are similar to the application case.

One more technical note: This proof is a rare case where an
induction on terms, rather than typing derivations, yields a
simpler argument.  The reason for this is that the assumption
$$update Gamma x U \vdash t : T$$ is not completely generic, in the
sense that one of the "slots" in the typing relation -- namely the
context -- is not just a variable, and this means that Agda's
native induction tactic does not give us the induction hypothesis
that we want.  It is possible to work around this, but the needed
generalization is a little tricky.  The term $$t$$, on the other
hand, _is_ completely generic.

<!--{% raw %}--><pre class="Agda">
<a name="19925" href="StlcProp.html#15867" class="Function"
      >[:=]-preserves-&#8866;</a
      ><a name="19941"
      > </a
      ><a name="19942" class="Symbol"
      >{</a
      ><a name="19943" href="StlcProp.html#19943" class="Bound"
      >&#915;</a
      ><a name="19944" class="Symbol"
      >}</a
      ><a name="19945"
      > </a
      ><a name="19946" class="Symbol"
      >{</a
      ><a name="19947" href="StlcProp.html#19947" class="Bound"
      >x</a
      ><a name="19948" class="Symbol"
      >}</a
      ><a name="19949"
      > </a
      ><a name="19950" href="StlcProp.html#19950" class="Bound"
      >v&#8758;A</a
      ><a name="19953"
      > </a
      ><a name="19954" class="Symbol"
      >(</a
      ><a name="19955" href="Stlc.html#19275" class="InductiveConstructor"
      >var</a
      ><a name="19958"
      > </a
      ><a name="19959" href="StlcProp.html#19959" class="Bound"
      >y</a
      ><a name="19960"
      > </a
      ><a name="19961" href="StlcProp.html#19961" class="Bound"
      >y&#8712;&#915;</a
      ><a name="19964" class="Symbol"
      >)</a
      ><a name="19965"
      > </a
      ><a name="19966" class="Keyword"
      >with</a
      ><a name="19970"
      > </a
      ><a name="19971" href="StlcProp.html#19947" class="Bound"
      >x</a
      ><a name="19972"
      > </a
      ><a name="19973" href="Maps.html#2454" class="Function Operator"
      >&#8799;</a
      ><a name="19974"
      > </a
      ><a name="19975" href="StlcProp.html#19959" class="Bound"
      >y</a
      ><a name="19976"
      >
</a
      ><a name="19977" class="Symbol"
      >...</a
      ><a name="19980"
      > </a
      ><a name="19981" class="Symbol"
      >|</a
      ><a name="19982"
      > </a
      ><a name="19983" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#520" class="InductiveConstructor"
      >yes</a
      ><a name="19986"
      > </a
      ><a name="19987" href="StlcProp.html#19987" class="Bound"
      >x=y</a
      ><a name="19990"
      > </a
      ><a name="19991" class="Symbol"
      >=</a
      ><a name="19992"
      > </a
      ><a name="19993" class="Symbol"
      >{!!}</a
      ><a name="19997"
      >
</a
      ><a name="19998" class="Symbol"
      >...</a
      ><a name="20001"
      > </a
      ><a name="20002" class="Symbol"
      >|</a
      ><a name="20003"
      > </a
      ><a name="20004" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#547" class="InductiveConstructor"
      >no</a
      ><a name="20006"
      >  </a
      ><a name="20008" href="StlcProp.html#20008" class="Bound"
      >x&#8800;y</a
      ><a name="20011"
      > </a
      ><a name="20012" class="Symbol"
      >=</a
      ><a name="20013"
      > </a
      ><a name="20014" class="Symbol"
      >{!!}</a
      ><a name="20018"
      >
</a
      ><a name="20019" href="StlcProp.html#15867" class="Function"
      >[:=]-preserves-&#8866;</a
      ><a name="20035"
      > </a
      ><a name="20036" href="StlcProp.html#20036" class="Bound"
      >v&#8758;A</a
      ><a name="20039"
      > </a
      ><a name="20040" class="Symbol"
      >(</a
      ><a name="20041" href="Stlc.html#19368" class="InductiveConstructor"
      >abs</a
      ><a name="20044"
      > </a
      ><a name="20045" href="StlcProp.html#20045" class="Bound"
      >t&#8242;&#8758;B</a
      ><a name="20049" class="Symbol"
      >)</a
      ><a name="20050"
      > </a
      ><a name="20051" class="Symbol"
      >=</a
      ><a name="20052"
      > </a
      ><a name="20053" class="Symbol"
      >{!!}</a
      ><a name="20057"
      >
</a
      ><a name="20058" href="StlcProp.html#15867" class="Function"
      >[:=]-preserves-&#8866;</a
      ><a name="20074"
      > </a
      ><a name="20075" href="StlcProp.html#20075" class="Bound"
      >v&#8758;A</a
      ><a name="20078"
      > </a
      ><a name="20079" class="Symbol"
      >(</a
      ><a name="20080" href="Stlc.html#19484" class="InductiveConstructor"
      >app</a
      ><a name="20083"
      > </a
      ><a name="20084" href="StlcProp.html#20084" class="Bound"
      >t&#8321;&#8758;A&#8658;B</a
      ><a name="20090"
      > </a
      ><a name="20091" href="StlcProp.html#20091" class="Bound"
      >t&#8322;&#8758;A</a
      ><a name="20095" class="Symbol"
      >)</a
      ><a name="20096"
      > </a
      ><a name="20097" class="Symbol"
      >=</a
      ><a name="20098"
      >
  </a
      ><a name="20101" href="Stlc.html#19484" class="InductiveConstructor"
      >app</a
      ><a name="20104"
      > </a
      ><a name="20105" class="Symbol"
      >(</a
      ><a name="20106" href="StlcProp.html#15867" class="Function"
      >[:=]-preserves-&#8866;</a
      ><a name="20122"
      > </a
      ><a name="20123" href="StlcProp.html#20075" class="Bound"
      >v&#8758;A</a
      ><a name="20126"
      > </a
      ><a name="20127" href="StlcProp.html#20084" class="Bound"
      >t&#8321;&#8758;A&#8658;B</a
      ><a name="20133" class="Symbol"
      >)</a
      ><a name="20134"
      > </a
      ><a name="20135" class="Symbol"
      >(</a
      ><a name="20136" href="StlcProp.html#15867" class="Function"
      >[:=]-preserves-&#8866;</a
      ><a name="20152"
      > </a
      ><a name="20153" href="StlcProp.html#20075" class="Bound"
      >v&#8758;A</a
      ><a name="20156"
      > </a
      ><a name="20157" href="StlcProp.html#20091" class="Bound"
      >t&#8322;&#8758;A</a
      ><a name="20161" class="Symbol"
      >)</a
      ><a name="20162"
      >
</a
      ><a name="20163" href="StlcProp.html#15867" class="Function"
      >[:=]-preserves-&#8866;</a
      ><a name="20179"
      > </a
      ><a name="20180" href="StlcProp.html#20180" class="Bound"
      >v&#8758;A</a
      ><a name="20183"
      > </a
      ><a name="20184" href="Stlc.html#19618" class="InductiveConstructor"
      >true</a
      ><a name="20188"
      >  </a
      ><a name="20190" class="Symbol"
      >=</a
      ><a name="20191"
      > </a
      ><a name="20192" href="Stlc.html#19618" class="InductiveConstructor"
      >true</a
      ><a name="20196"
      >
</a
      ><a name="20197" href="StlcProp.html#15867" class="Function"
      >[:=]-preserves-&#8866;</a
      ><a name="20213"
      > </a
      ><a name="20214" href="StlcProp.html#20214" class="Bound"
      >v&#8758;A</a
      ><a name="20217"
      > </a
      ><a name="20218" href="Stlc.html#19677" class="InductiveConstructor"
      >false</a
      ><a name="20223"
      > </a
      ><a name="20224" class="Symbol"
      >=</a
      ><a name="20225"
      > </a
      ><a name="20226" href="Stlc.html#19677" class="InductiveConstructor"
      >false</a
      ><a name="20231"
      >
</a
      ><a name="20232" href="StlcProp.html#15867" class="Function"
      >[:=]-preserves-&#8866;</a
      ><a name="20248"
      > </a
      ><a name="20249" href="StlcProp.html#20249" class="Bound"
      >v&#8758;A</a
      ><a name="20252"
      > </a
      ><a name="20253" class="Symbol"
      >(</a
      ><a name="20254" href="Stlc.html#19736" class="InductiveConstructor Operator"
      >if</a
      ><a name="20256"
      > </a
      ><a name="20257" href="StlcProp.html#20257" class="Bound"
      >t&#8321;&#8758;bool</a
      ><a name="20264"
      > </a
      ><a name="20265" href="Stlc.html#19736" class="InductiveConstructor Operator"
      >then</a
      ><a name="20269"
      > </a
      ><a name="20270" href="StlcProp.html#20270" class="Bound"
      >t&#8322;&#8758;B</a
      ><a name="20274"
      > </a
      ><a name="20275" href="Stlc.html#19736" class="InductiveConstructor Operator"
      >else</a
      ><a name="20279"
      > </a
      ><a name="20280" href="StlcProp.html#20280" class="Bound"
      >t&#8323;&#8758;B</a
      ><a name="20284" class="Symbol"
      >)</a
      ><a name="20285"
      > </a
      ><a name="20286" class="Symbol"
      >=</a
      ><a name="20287"
      >
  </a
      ><a name="20290" href="Stlc.html#19736" class="InductiveConstructor Operator"
      >if</a
      ><a name="20292"
      >   </a
      ><a name="20295" href="StlcProp.html#15867" class="Function"
      >[:=]-preserves-&#8866;</a
      ><a name="20311"
      > </a
      ><a name="20312" href="StlcProp.html#20249" class="Bound"
      >v&#8758;A</a
      ><a name="20315"
      > </a
      ><a name="20316" href="StlcProp.html#20257" class="Bound"
      >t&#8321;&#8758;bool</a
      ><a name="20323"
      >
  </a
      ><a name="20326" href="Stlc.html#19736" class="InductiveConstructor Operator"
      >then</a
      ><a name="20330"
      > </a
      ><a name="20331" href="StlcProp.html#15867" class="Function"
      >[:=]-preserves-&#8866;</a
      ><a name="20347"
      > </a
      ><a name="20348" href="StlcProp.html#20249" class="Bound"
      >v&#8758;A</a
      ><a name="20351"
      > </a
      ><a name="20352" href="StlcProp.html#20270" class="Bound"
      >t&#8322;&#8758;B</a
      ><a name="20356"
      >
  </a
      ><a name="20359" href="Stlc.html#19736" class="InductiveConstructor Operator"
      >else</a
      ><a name="20363"
      > </a
      ><a name="20364" href="StlcProp.html#15867" class="Function"
      >[:=]-preserves-&#8866;</a
      ><a name="20380"
      > </a
      ><a name="20381" href="StlcProp.html#20249" class="Bound"
      >v&#8758;A</a
      ><a name="20384"
      > </a
      ><a name="20385" href="StlcProp.html#20280" class="Bound"
      >t&#8323;&#8758;B</a
      >
</pre><!--{% endraw %}-->


### Main Theorem

We now have the tools we need to prove preservation: if a closed
term $$t$$ has type $$T$$ and takes a step to $$t'$$, then $$t'$$
is also a closed term with type $$T$$.  In other words, the small-step
reduction relation preserves types.

Theorem preservation : forall t t' T,
     empty \vdash t : T  →
     t ==> t'  →
     empty \vdash t' : T.

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
      \lambda x:T_11.t_12$$ and $$t_1 t_2$$ steps to $$$$x:=t_2$$t_12$$; the
      desired result now follows from the fact that substitution
      preserves types.

    - If the last rule in the derivation was $$if$$, then $$t = if t_1
      then t_2 else t_3$$, and there are again three cases depending on
      how $$t$$ steps.

    - If $$t$$ steps to $$t_2$$ or $$t_3$$, the result is immediate, since
      $$t_2$$ and $$t_3$$ have the same type as $$t$$.

    - Otherwise, $$t$$ steps by $$Sif$$, and the desired conclusion
      follows directly from the induction hypothesis.

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
      apply substitution_preserves_typing with T_11...
      inversion HT_1...
Qed.

#### Exercise: 2 stars, recommended (subject_expansion_stlc)
An exercise in the $$Stlc$$$$sf/Stlc.html$$ chapter asked about the subject
expansion property for the simple language of arithmetic and
boolean expressions.  Does this property hold for STLC?  That is,
is it always the case that, if $$t ==> t'$$ and $$has_type t' T$$,
then $$empty \vdash t : T$$?  If so, prove it.  If not, give a
counter-example not involving conditionals.

(* FILL IN HERE

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
  (* FILL IN HERE  Admitted.
(** $$$$


## Uniqueness of Types

#### Exercise: 3 stars (types_unique)
Another nice property of the STLC is that types are unique: a
given term (in a given context) has at most one type.
Formalize this statement and prove it.

(* FILL IN HERE
(** $$$$


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
