---
title     : "StlcProp: Properties of STLC"
layout    : page
permalink : /StlcProp
---

<pre class="Agda">{% raw %}
<a name="105" class="Keyword"
      >module</a
      ><a name="111"
      > </a
      ><a name="112" href="StlcProp.html#1" class="Module"
      >StlcProp</a
      ><a name="120"
      > </a
      ><a name="121" class="Keyword"
      >where</a
      >
{% endraw %}</pre>

<div class="hidden">
<pre class="Agda">{% raw %}
<a name="173" class="Keyword"
      >open</a
      ><a name="177"
      > </a
      ><a name="178" class="Keyword"
      >import</a
      ><a name="184"
      > </a
      ><a name="185" href="https://agda.github.io/agda-stdlib/Function.html#1" class="Module"
      >Function</a
      ><a name="193"
      > </a
      ><a name="194" class="Keyword"
      >using</a
      ><a name="199"
      > </a
      ><a name="200" class="Symbol"
      >(</a
      ><a name="201" href="https://agda.github.io/agda-stdlib/Function.html#713" class="Function Operator"
      >_&#8728;_</a
      ><a name="204" class="Symbol"
      >)</a
      ><a name="205"
      >
</a
      ><a name="206" class="Keyword"
      >open</a
      ><a name="210"
      > </a
      ><a name="211" class="Keyword"
      >import</a
      ><a name="217"
      > </a
      ><a name="218" href="https://agda.github.io/agda-stdlib/Data.Empty.html#1" class="Module"
      >Data.Empty</a
      ><a name="228"
      > </a
      ><a name="229" class="Keyword"
      >using</a
      ><a name="234"
      > </a
      ><a name="235" class="Symbol"
      >(</a
      ><a name="236" href="https://agda.github.io/agda-stdlib/Data.Empty.html#243" class="Datatype"
      >&#8869;</a
      ><a name="237" class="Symbol"
      >;</a
      ><a name="238"
      > </a
      ><a name="239" href="https://agda.github.io/agda-stdlib/Data.Empty.html#348" class="Function"
      >&#8869;-elim</a
      ><a name="245" class="Symbol"
      >)</a
      ><a name="246"
      >
</a
      ><a name="247" class="Keyword"
      >open</a
      ><a name="251"
      > </a
      ><a name="252" class="Keyword"
      >import</a
      ><a name="258"
      > </a
      ><a name="259" href="https://agda.github.io/agda-stdlib/Data.Maybe.html#1" class="Module"
      >Data.Maybe</a
      ><a name="269"
      > </a
      ><a name="270" class="Keyword"
      >using</a
      ><a name="275"
      > </a
      ><a name="276" class="Symbol"
      >(</a
      ><a name="277" href="https://agda.github.io/agda-stdlib/Data.Maybe.Base.html#335" class="Datatype"
      >Maybe</a
      ><a name="282" class="Symbol"
      >;</a
      ><a name="283"
      > </a
      ><a name="284" href="https://agda.github.io/agda-stdlib/Data.Maybe.html#1527" class="InductiveConstructor"
      >just</a
      ><a name="288" class="Symbol"
      >;</a
      ><a name="289"
      > </a
      ><a name="290" href="https://agda.github.io/agda-stdlib/Data.Maybe.html#1588" class="InductiveConstructor"
      >nothing</a
      ><a name="297" class="Symbol"
      >)</a
      ><a name="298"
      >
</a
      ><a name="299" class="Keyword"
      >open</a
      ><a name="303"
      > </a
      ><a name="304" class="Keyword"
      >import</a
      ><a name="310"
      > </a
      ><a name="311" href="https://agda.github.io/agda-stdlib/Data.Product.html#1" class="Module"
      >Data.Product</a
      ><a name="323"
      > </a
      ><a name="324" class="Keyword"
      >using</a
      ><a name="329"
      > </a
      ><a name="330" class="Symbol"
      >(</a
      ><a name="331" href="https://agda.github.io/agda-stdlib/Data.Product.html#823" class="Function"
      >&#8707;</a
      ><a name="332" class="Symbol"
      >;</a
      ><a name="333"
      > </a
      ><a name="334" href="https://agda.github.io/agda-stdlib/Data.Product.html#949" class="Function"
      >&#8707;&#8322;</a
      ><a name="336" class="Symbol"
      >;</a
      ><a name="337"
      > </a
      ><a name="338" href="https://agda.github.io/agda-stdlib/Data.Product.html#509" class="InductiveConstructor Operator"
      >_,_</a
      ><a name="341" class="Symbol"
      >;</a
      ><a name="342"
      > </a
      ><a name="343" href="https://agda.github.io/agda-stdlib/Data.Product.html#1621" class="Function Operator"
      >,_</a
      ><a name="345" class="Symbol"
      >)</a
      ><a name="346"
      >
</a
      ><a name="347" class="Keyword"
      >open</a
      ><a name="351"
      > </a
      ><a name="352" class="Keyword"
      >import</a
      ><a name="358"
      > </a
      ><a name="359" href="https://agda.github.io/agda-stdlib/Data.Sum.html#1" class="Module"
      >Data.Sum</a
      ><a name="367"
      > </a
      ><a name="368" class="Keyword"
      >using</a
      ><a name="373"
      > </a
      ><a name="374" class="Symbol"
      >(</a
      ><a name="375" href="https://agda.github.io/agda-stdlib/Data.Sum.html#433" class="Datatype Operator"
      >_&#8846;_</a
      ><a name="378" class="Symbol"
      >;</a
      ><a name="379"
      > </a
      ><a name="380" href="https://agda.github.io/agda-stdlib/Data.Sum.html#489" class="InductiveConstructor"
      >inj&#8321;</a
      ><a name="384" class="Symbol"
      >;</a
      ><a name="385"
      > </a
      ><a name="386" href="https://agda.github.io/agda-stdlib/Data.Sum.html#514" class="InductiveConstructor"
      >inj&#8322;</a
      ><a name="390" class="Symbol"
      >)</a
      ><a name="391"
      >
</a
      ><a name="392" class="Keyword"
      >open</a
      ><a name="396"
      > </a
      ><a name="397" class="Keyword"
      >import</a
      ><a name="403"
      > </a
      ><a name="404" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#1" class="Module"
      >Relation.Nullary</a
      ><a name="420"
      > </a
      ><a name="421" class="Keyword"
      >using</a
      ><a name="426"
      > </a
      ><a name="427" class="Symbol"
      >(</a
      ><a name="428" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#414" class="Function Operator"
      >&#172;_</a
      ><a name="430" class="Symbol"
      >;</a
      ><a name="431"
      > </a
      ><a name="432" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#484" class="Datatype"
      >Dec</a
      ><a name="435" class="Symbol"
      >;</a
      ><a name="436"
      > </a
      ><a name="437" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#520" class="InductiveConstructor"
      >yes</a
      ><a name="440" class="Symbol"
      >;</a
      ><a name="441"
      > </a
      ><a name="442" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#547" class="InductiveConstructor"
      >no</a
      ><a name="444" class="Symbol"
      >)</a
      ><a name="445"
      >
</a
      ><a name="446" class="Keyword"
      >open</a
      ><a name="450"
      > </a
      ><a name="451" class="Keyword"
      >import</a
      ><a name="457"
      > </a
      ><a name="458" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#1" class="Module"
      >Relation.Binary.PropositionalEquality</a
      ><a name="495"
      > </a
      ><a name="496" class="Keyword"
      >using</a
      ><a name="501"
      > </a
      ><a name="502" class="Symbol"
      >(</a
      ><a name="503" href="Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >_&#8801;_</a
      ><a name="506" class="Symbol"
      >;</a
      ><a name="507"
      > </a
      ><a name="508" href="https://agda.github.io/agda-stdlib/Relation.Binary.Core.html#4493" class="Function Operator"
      >_&#8802;_</a
      ><a name="511" class="Symbol"
      >;</a
      ><a name="512"
      > </a
      ><a name="513" href="Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="517" class="Symbol"
      >)</a
      ><a name="518"
      >
</a
      ><a name="519" class="Keyword"
      >open</a
      ><a name="523"
      > </a
      ><a name="524" class="Keyword"
      >import</a
      ><a name="530"
      > </a
      ><a name="531" class="Module"
      >Maps</a
      ><a name="535"
      >
</a
      ><a name="536" class="Keyword"
      >open</a
      ><a name="540"
      > </a
      ><a name="541" class="Keyword"
      >import</a
      ><a name="547"
      > </a
      ><a name="548" href="Stlc.html#1" class="Module"
      >Stlc</a
      >
{% endraw %}</pre>
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

<pre class="Agda">{% raw %}
<a name="1134" href="StlcProp.html#1134" class="Function"
      >CanonicalForms</a
      ><a name="1148"
      > </a
      ><a name="1149" class="Symbol"
      >:</a
      ><a name="1150"
      > </a
      ><a name="1151" href="Stlc.html#5630" class="Datatype"
      >Term</a
      ><a name="1155"
      > </a
      ><a name="1156" class="Symbol"
      >&#8594;</a
      ><a name="1157"
      > </a
      ><a name="1158" href="Stlc.html#5463" class="Datatype"
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
      >
</a
      ><a name="1169" href="StlcProp.html#1134" class="Function"
      >CanonicalForms</a
      ><a name="1183"
      > </a
      ><a name="1184" href="StlcProp.html#1184" class="Bound"
      >t</a
      ><a name="1185"
      > </a
      ><a name="1186" href="Stlc.html#5482" class="InductiveConstructor"
      >bool</a
      ><a name="1190"
      >    </a
      ><a name="1194" class="Symbol"
      >=</a
      ><a name="1195"
      > </a
      ><a name="1196" href="StlcProp.html#1184" class="Bound"
      >t</a
      ><a name="1197"
      > </a
      ><a name="1198" href="Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="1199"
      > </a
      ><a name="1200" href="Stlc.html#5732" class="InductiveConstructor"
      >true</a
      ><a name="1204"
      > </a
      ><a name="1205" href="https://agda.github.io/agda-stdlib/Data.Sum.html#433" class="Datatype Operator"
      >&#8846;</a
      ><a name="1206"
      > </a
      ><a name="1207" href="StlcProp.html#1184" class="Bound"
      >t</a
      ><a name="1208"
      > </a
      ><a name="1209" href="Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="1210"
      > </a
      ><a name="1211" href="Stlc.html#5747" class="InductiveConstructor"
      >false</a
      ><a name="1216"
      >
</a
      ><a name="1217" href="StlcProp.html#1134" class="Function"
      >CanonicalForms</a
      ><a name="1231"
      > </a
      ><a name="1232" href="StlcProp.html#1232" class="Bound"
      >t</a
      ><a name="1233"
      > </a
      ><a name="1234" class="Symbol"
      >(</a
      ><a name="1235" href="StlcProp.html#1235" class="Bound"
      >A</a
      ><a name="1236"
      > </a
      ><a name="1237" href="Stlc.html#5496" class="InductiveConstructor Operator"
      >&#8658;</a
      ><a name="1238"
      > </a
      ><a name="1239" href="StlcProp.html#1239" class="Bound"
      >B</a
      ><a name="1240" class="Symbol"
      >)</a
      ><a name="1241"
      > </a
      ><a name="1242" class="Symbol"
      >=</a
      ><a name="1243"
      > </a
      ><a name="1244" href="https://agda.github.io/agda-stdlib/Data.Product.html#949" class="Function"
      >&#8707;&#8322;</a
      ><a name="1246"
      > </a
      ><a name="1247" class="Symbol"
      >&#955;</a
      ><a name="1248"
      > </a
      ><a name="1249" href="StlcProp.html#1249" class="Bound"
      >x</a
      ><a name="1250"
      > </a
      ><a name="1251" href="StlcProp.html#1251" class="Bound"
      >t&#8242;</a
      ><a name="1253"
      > </a
      ><a name="1254" class="Symbol"
      >&#8594;</a
      ><a name="1255"
      > </a
      ><a name="1256" href="StlcProp.html#1232" class="Bound"
      >t</a
      ><a name="1257"
      > </a
      ><a name="1258" href="Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="1259"
      > </a
      ><a name="1260" href="Stlc.html#5698" class="InductiveConstructor"
      >abs</a
      ><a name="1263"
      > </a
      ><a name="1264" href="StlcProp.html#1249" class="Bound"
      >x</a
      ><a name="1265"
      > </a
      ><a name="1266" href="StlcProp.html#1235" class="Bound"
      >A</a
      ><a name="1267"
      > </a
      ><a name="1268" href="StlcProp.html#1251" class="Bound"
      >t&#8242;</a
      ><a name="1270"
      >

</a
      ><a name="1272" href="StlcProp.html#1272" class="Function"
      >canonicalForms</a
      ><a name="1286"
      > </a
      ><a name="1287" class="Symbol"
      >:</a
      ><a name="1288"
      > </a
      ><a name="1289" class="Symbol"
      >&#8704;</a
      ><a name="1290"
      > </a
      ><a name="1297" class="Symbol"
      >&#8594;</a
      ><a name="1298"
      > </a
      ><a name="1299" href="Stlc.html#18187" class="Function"
      >&#8709;</a
      ><a name="1300"
      > </a
      ><a name="1301" href="Stlc.html#19119" class="Datatype Operator"
      >&#8866;</a
      ><a name="1302"
      > </a
      ><a name="1303" href="StlcProp.html#1292" class="Bound"
      >t</a
      ><a name="1304"
      > </a
      ><a name="1305" href="Stlc.html#19119" class="Datatype Operator"
      >&#8758;</a
      ><a name="1306"
      > </a
      ><a name="1307" href="StlcProp.html#1294" class="Bound"
      >A</a
      ><a name="1308"
      > </a
      ><a name="1309" class="Symbol"
      >&#8594;</a
      ><a name="1310"
      > </a
      ><a name="1311" href="Stlc.html#8969" class="Datatype"
      >Value</a
      ><a name="1316"
      > </a
      ><a name="1317" href="StlcProp.html#1292" class="Bound"
      >t</a
      ><a name="1318"
      > </a
      ><a name="1319" class="Symbol"
      >&#8594;</a
      ><a name="1320"
      > </a
      ><a name="1321" href="StlcProp.html#1134" class="Function"
      >CanonicalForms</a
      ><a name="1335"
      > </a
      ><a name="1336" href="StlcProp.html#1292" class="Bound"
      >t</a
      ><a name="1337"
      > </a
      ><a name="1338" href="StlcProp.html#1294" class="Bound"
      >A</a
      ><a name="1339"
      >
</a
      ><a name="1340" href="StlcProp.html#1272" class="Function"
      >canonicalForms</a
      ><a name="1354"
      > </a
      ><a name="1355" class="Symbol"
      >(</a
      ><a name="1356" href="Stlc.html#19256" class="InductiveConstructor"
      >abs</a
      ><a name="1359"
      > </a
      ><a name="1360" href="StlcProp.html#1360" class="Bound"
      >t&#8242;</a
      ><a name="1362" class="Symbol"
      >)</a
      ><a name="1363"
      > </a
      ><a name="1364" href="Stlc.html#8996" class="InductiveConstructor"
      >abs</a
      ><a name="1367"
      >   </a
      ><a name="1370" class="Symbol"
      >=</a
      ><a name="1371"
      > </a
      ><a name="1372" class="Symbol"
      >_</a
      ><a name="1373"
      > </a
      ><a name="1374" href="https://agda.github.io/agda-stdlib/Data.Product.html#509" class="InductiveConstructor Operator"
      >,</a
      ><a name="1375"
      > </a
      ><a name="1376" class="Symbol"
      >_</a
      ><a name="1377"
      > </a
      ><a name="1378" href="https://agda.github.io/agda-stdlib/Data.Product.html#509" class="InductiveConstructor Operator"
      >,</a
      ><a name="1379"
      > </a
      ><a name="1380" href="Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="1384"
      >
</a
      ><a name="1385" href="StlcProp.html#1272" class="Function"
      >canonicalForms</a
      ><a name="1399"
      > </a
      ><a name="1400" href="Stlc.html#19506" class="InductiveConstructor"
      >true</a
      ><a name="1404"
      >     </a
      ><a name="1409" href="Stlc.html#9044" class="InductiveConstructor"
      >true</a
      ><a name="1413"
      >  </a
      ><a name="1415" class="Symbol"
      >=</a
      ><a name="1416"
      > </a
      ><a name="1417" href="https://agda.github.io/agda-stdlib/Data.Sum.html#489" class="InductiveConstructor"
      >inj&#8321;</a
      ><a name="1421"
      > </a
      ><a name="1422" href="Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="1426"
      >
</a
      ><a name="1427" href="StlcProp.html#1272" class="Function"
      >canonicalForms</a
      ><a name="1441"
      > </a
      ><a name="1442" href="Stlc.html#19565" class="InductiveConstructor"
      >false</a
      ><a name="1447"
      >    </a
      ><a name="1451" href="Stlc.html#9065" class="InductiveConstructor"
      >false</a
      ><a name="1456"
      > </a
      ><a name="1457" class="Symbol"
      >=</a
      ><a name="1458"
      > </a
      ><a name="1459" href="https://agda.github.io/agda-stdlib/Data.Sum.html#514" class="InductiveConstructor"
      >inj&#8322;</a
      ><a name="1463"
      > </a
      ><a name="1464" href="Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      >
{% endraw %}</pre>

## Progress

As before, the _progress_ theorem tells us that closed, well-typed
terms are not stuck: either a well-typed term is a value, or it
can take a reduction step.  The proof is a relatively
straightforward extension of the progress proof we saw in the
[Stlc](Stlc.html) chapter.  We'll give the proof in English first,
then the formal version.

<pre class="Agda">{% raw %}
<a name="1847" href="StlcProp.html#1847" class="Function"
      >progress</a
      ><a name="1855"
      > </a
      ><a name="1856" class="Symbol"
      >:</a
      ><a name="1857"
      > </a
      ><a name="1858" class="Symbol"
      >&#8704;</a
      ><a name="1859"
      > </a
      ><a name="1866" class="Symbol"
      >&#8594;</a
      ><a name="1867"
      > </a
      ><a name="1868" href="Stlc.html#18187" class="Function"
      >&#8709;</a
      ><a name="1869"
      > </a
      ><a name="1870" href="Stlc.html#19119" class="Datatype Operator"
      >&#8866;</a
      ><a name="1871"
      > </a
      ><a name="1872" href="StlcProp.html#1861" class="Bound"
      >t</a
      ><a name="1873"
      > </a
      ><a name="1874" href="Stlc.html#19119" class="Datatype Operator"
      >&#8758;</a
      ><a name="1875"
      > </a
      ><a name="1876" href="StlcProp.html#1863" class="Bound"
      >A</a
      ><a name="1877"
      > </a
      ><a name="1878" class="Symbol"
      >&#8594;</a
      ><a name="1879"
      > </a
      ><a name="1880" href="Stlc.html#8969" class="Datatype"
      >Value</a
      ><a name="1885"
      > </a
      ><a name="1886" href="StlcProp.html#1861" class="Bound"
      >t</a
      ><a name="1887"
      > </a
      ><a name="1888" href="https://agda.github.io/agda-stdlib/Data.Sum.html#433" class="Datatype Operator"
      >&#8846;</a
      ><a name="1889"
      > </a
      ><a name="1890" href="https://agda.github.io/agda-stdlib/Data.Product.html#823" class="Function"
      >&#8707;</a
      ><a name="1891"
      > </a
      ><a name="1892" class="Symbol"
      >&#955;</a
      ><a name="1893"
      > </a
      ><a name="1894" href="StlcProp.html#1894" class="Bound"
      >t&#8242;</a
      ><a name="1896"
      > </a
      ><a name="1897" class="Symbol"
      >&#8594;</a
      ><a name="1898"
      > </a
      ><a name="1899" href="StlcProp.html#1861" class="Bound"
      >t</a
      ><a name="1900"
      > </a
      ><a name="1901" href="Stlc.html#15105" class="Datatype Operator"
      >==&gt;</a
      ><a name="1904"
      > </a
      ><a name="1905" href="StlcProp.html#1894" class="Bound"
      >t&#8242;</a
      >
{% endraw %}</pre>

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

<pre class="Agda">{% raw %}
<a name="3606" href="StlcProp.html#1847" class="Function"
      >progress</a
      ><a name="3614"
      > </a
      ><a name="3615" class="Symbol"
      >(</a
      ><a name="3616" href="Stlc.html#19163" class="InductiveConstructor"
      >var</a
      ><a name="3619"
      > </a
      ><a name="3620" href="StlcProp.html#3620" class="Bound"
      >x</a
      ><a name="3621"
      > </a
      ><a name="3622" class="Symbol"
      >())</a
      ><a name="3625"
      >
</a
      ><a name="3626" href="StlcProp.html#1847" class="Function"
      >progress</a
      ><a name="3634"
      > </a
      ><a name="3635" href="Stlc.html#19506" class="InductiveConstructor"
      >true</a
      ><a name="3639"
      >      </a
      ><a name="3645" class="Symbol"
      >=</a
      ><a name="3646"
      > </a
      ><a name="3647" href="https://agda.github.io/agda-stdlib/Data.Sum.html#489" class="InductiveConstructor"
      >inj&#8321;</a
      ><a name="3651"
      > </a
      ><a name="3652" href="Stlc.html#9044" class="InductiveConstructor"
      >true</a
      ><a name="3656"
      >
</a
      ><a name="3657" href="StlcProp.html#1847" class="Function"
      >progress</a
      ><a name="3665"
      > </a
      ><a name="3666" href="Stlc.html#19565" class="InductiveConstructor"
      >false</a
      ><a name="3671"
      >     </a
      ><a name="3676" class="Symbol"
      >=</a
      ><a name="3677"
      > </a
      ><a name="3678" href="https://agda.github.io/agda-stdlib/Data.Sum.html#489" class="InductiveConstructor"
      >inj&#8321;</a
      ><a name="3682"
      > </a
      ><a name="3683" href="Stlc.html#9065" class="InductiveConstructor"
      >false</a
      ><a name="3688"
      >
</a
      ><a name="3689" href="StlcProp.html#1847" class="Function"
      >progress</a
      ><a name="3697"
      > </a
      ><a name="3698" class="Symbol"
      >(</a
      ><a name="3699" href="Stlc.html#19256" class="InductiveConstructor"
      >abs</a
      ><a name="3702"
      > </a
      ><a name="3703" href="StlcProp.html#3703" class="Bound"
      >t&#8758;A</a
      ><a name="3706" class="Symbol"
      >)</a
      ><a name="3707"
      > </a
      ><a name="3708" class="Symbol"
      >=</a
      ><a name="3709"
      > </a
      ><a name="3710" href="https://agda.github.io/agda-stdlib/Data.Sum.html#489" class="InductiveConstructor"
      >inj&#8321;</a
      ><a name="3714"
      > </a
      ><a name="3715" href="Stlc.html#8996" class="InductiveConstructor"
      >abs</a
      ><a name="3718"
      >
</a
      ><a name="3719" href="StlcProp.html#1847" class="Function"
      >progress</a
      ><a name="3727"
      > </a
      ><a name="3728" class="Symbol"
      >(</a
      ><a name="3729" href="Stlc.html#19372" class="InductiveConstructor"
      >app</a
      ><a name="3732"
      > </a
      ><a name="3733" href="StlcProp.html#3733" class="Bound"
      >t&#8321;&#8758;A&#8658;B</a
      ><a name="3739"
      > </a
      ><a name="3740" href="StlcProp.html#3740" class="Bound"
      >t&#8322;&#8758;B</a
      ><a name="3744" class="Symbol"
      >)</a
      ><a name="3745"
      >
    </a
      ><a name="3750" class="Keyword"
      >with</a
      ><a name="3754"
      > </a
      ><a name="3755" href="StlcProp.html#1847" class="Function"
      >progress</a
      ><a name="3763"
      > </a
      ><a name="3764" href="StlcProp.html#3733" class="Bound"
      >t&#8321;&#8758;A&#8658;B</a
      ><a name="3770"
      >
</a
      ><a name="3771" class="Symbol"
      >...</a
      ><a name="3774"
      > </a
      ><a name="3775" class="Symbol"
      >|</a
      ><a name="3776"
      > </a
      ><a name="3777" href="https://agda.github.io/agda-stdlib/Data.Sum.html#514" class="InductiveConstructor"
      >inj&#8322;</a
      ><a name="3781"
      > </a
      ><a name="3782" class="Symbol"
      >(_</a
      ><a name="3784"
      > </a
      ><a name="3785" href="https://agda.github.io/agda-stdlib/Data.Product.html#509" class="InductiveConstructor Operator"
      >,</a
      ><a name="3786"
      > </a
      ><a name="3787" href="StlcProp.html#3787" class="Bound"
      >t&#8321;&#8658;t&#8321;&#8242;</a
      ><a name="3793" class="Symbol"
      >)</a
      ><a name="3794"
      > </a
      ><a name="3795" class="Symbol"
      >=</a
      ><a name="3796"
      > </a
      ><a name="3797" href="https://agda.github.io/agda-stdlib/Data.Sum.html#514" class="InductiveConstructor"
      >inj&#8322;</a
      ><a name="3801"
      > </a
      ><a name="3802" class="Symbol"
      >(_</a
      ><a name="3804"
      > </a
      ><a name="3805" href="https://agda.github.io/agda-stdlib/Data.Product.html#509" class="InductiveConstructor Operator"
      >,</a
      ><a name="3806"
      > </a
      ><a name="3807" href="Stlc.html#15230" class="InductiveConstructor"
      >app1</a
      ><a name="3811"
      > </a
      ><a name="3812" href="StlcProp.html#3787" class="Bound"
      >t&#8321;&#8658;t&#8321;&#8242;</a
      ><a name="3818" class="Symbol"
      >)</a
      ><a name="3819"
      >
</a
      ><a name="3820" class="Symbol"
      >...</a
      ><a name="3823"
      > </a
      ><a name="3824" class="Symbol"
      >|</a
      ><a name="3825"
      > </a
      ><a name="3826" href="https://agda.github.io/agda-stdlib/Data.Sum.html#489" class="InductiveConstructor"
      >inj&#8321;</a
      ><a name="3830"
      > </a
      ><a name="3831" href="StlcProp.html#3831" class="Bound"
      >v&#8321;</a
      ><a name="3833"
      >
    </a
      ><a name="3838" class="Keyword"
      >with</a
      ><a name="3842"
      > </a
      ><a name="3843" href="StlcProp.html#1847" class="Function"
      >progress</a
      ><a name="3851"
      > </a
      ><a name="3852" href="StlcProp.html#3740" class="Bound"
      >t&#8322;&#8758;B</a
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
      ><a name="3863" href="https://agda.github.io/agda-stdlib/Data.Sum.html#514" class="InductiveConstructor"
      >inj&#8322;</a
      ><a name="3867"
      > </a
      ><a name="3868" class="Symbol"
      >(_</a
      ><a name="3870"
      > </a
      ><a name="3871" href="https://agda.github.io/agda-stdlib/Data.Product.html#509" class="InductiveConstructor Operator"
      >,</a
      ><a name="3872"
      > </a
      ><a name="3873" href="StlcProp.html#3873" class="Bound"
      >t&#8322;&#8658;t&#8322;&#8242;</a
      ><a name="3879" class="Symbol"
      >)</a
      ><a name="3880"
      > </a
      ><a name="3881" class="Symbol"
      >=</a
      ><a name="3882"
      > </a
      ><a name="3883" href="https://agda.github.io/agda-stdlib/Data.Sum.html#514" class="InductiveConstructor"
      >inj&#8322;</a
      ><a name="3887"
      > </a
      ><a name="3888" class="Symbol"
      >(_</a
      ><a name="3890"
      > </a
      ><a name="3891" href="https://agda.github.io/agda-stdlib/Data.Product.html#509" class="InductiveConstructor Operator"
      >,</a
      ><a name="3892"
      > </a
      ><a name="3893" href="Stlc.html#15307" class="InductiveConstructor"
      >app2</a
      ><a name="3897"
      > </a
      ><a name="3898" href="StlcProp.html#3831" class="Bound"
      >v&#8321;</a
      ><a name="3900"
      > </a
      ><a name="3901" href="StlcProp.html#3873" class="Bound"
      >t&#8322;&#8658;t&#8322;&#8242;</a
      ><a name="3907" class="Symbol"
      >)</a
      ><a name="3908"
      >
</a
      ><a name="3909" class="Symbol"
      >...</a
      ><a name="3912"
      > </a
      ><a name="3913" class="Symbol"
      >|</a
      ><a name="3914"
      > </a
      ><a name="3915" href="https://agda.github.io/agda-stdlib/Data.Sum.html#489" class="InductiveConstructor"
      >inj&#8321;</a
      ><a name="3919"
      > </a
      ><a name="3920" href="StlcProp.html#3920" class="Bound"
      >v&#8322;</a
      ><a name="3922"
      >
    </a
      ><a name="3927" class="Keyword"
      >with</a
      ><a name="3931"
      > </a
      ><a name="3932" href="StlcProp.html#1272" class="Function"
      >canonicalForms</a
      ><a name="3946"
      > </a
      ><a name="3947" href="StlcProp.html#3733" class="Bound"
      >t&#8321;&#8758;A&#8658;B</a
      ><a name="3953"
      > </a
      ><a name="3954" href="StlcProp.html#3831" class="Bound"
      >v&#8321;</a
      ><a name="3956"
      >
</a
      ><a name="3957" class="Symbol"
      >...</a
      ><a name="3960"
      > </a
      ><a name="3961" class="Symbol"
      >|</a
      ><a name="3962"
      > </a
      ><a name="3963" class="Symbol"
      >(_</a
      ><a name="3965"
      > </a
      ><a name="3966" href="https://agda.github.io/agda-stdlib/Data.Product.html#509" class="InductiveConstructor Operator"
      >,</a
      ><a name="3967"
      > </a
      ><a name="3968" class="Symbol"
      >_</a
      ><a name="3969"
      > </a
      ><a name="3970" href="https://agda.github.io/agda-stdlib/Data.Product.html#509" class="InductiveConstructor Operator"
      >,</a
      ><a name="3971"
      > </a
      ><a name="3972" href="Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="3976" class="Symbol"
      >)</a
      ><a name="3977"
      > </a
      ><a name="3978" class="Symbol"
      >=</a
      ><a name="3979"
      > </a
      ><a name="3980" href="https://agda.github.io/agda-stdlib/Data.Sum.html#514" class="InductiveConstructor"
      >inj&#8322;</a
      ><a name="3984"
      > </a
      ><a name="3985" class="Symbol"
      >(_</a
      ><a name="3987"
      > </a
      ><a name="3988" href="https://agda.github.io/agda-stdlib/Data.Product.html#509" class="InductiveConstructor Operator"
      >,</a
      ><a name="3989"
      > </a
      ><a name="3990" href="Stlc.html#15139" class="InductiveConstructor"
      >red</a
      ><a name="3993"
      > </a
      ><a name="3994" href="StlcProp.html#3920" class="Bound"
      >v&#8322;</a
      ><a name="3996" class="Symbol"
      >)</a
      ><a name="3997"
      >
</a
      ><a name="3998" href="StlcProp.html#1847" class="Function"
      >progress</a
      ><a name="4006"
      > </a
      ><a name="4007" class="Symbol"
      >(</a
      ><a name="4008" href="Stlc.html#19624" class="InductiveConstructor Operator"
      >if</a
      ><a name="4010"
      > </a
      ><a name="4011" href="StlcProp.html#4011" class="Bound"
      >t&#8321;&#8758;bool</a
      ><a name="4018"
      > </a
      ><a name="4019" href="Stlc.html#19624" class="InductiveConstructor Operator"
      >then</a
      ><a name="4023"
      > </a
      ><a name="4024" href="StlcProp.html#4024" class="Bound"
      >t&#8322;&#8758;A</a
      ><a name="4028"
      > </a
      ><a name="4029" href="Stlc.html#19624" class="InductiveConstructor Operator"
      >else</a
      ><a name="4033"
      > </a
      ><a name="4034" href="StlcProp.html#4034" class="Bound"
      >t&#8323;&#8758;A</a
      ><a name="4038" class="Symbol"
      >)</a
      ><a name="4039"
      >
    </a
      ><a name="4044" class="Keyword"
      >with</a
      ><a name="4048"
      > </a
      ><a name="4049" href="StlcProp.html#1847" class="Function"
      >progress</a
      ><a name="4057"
      > </a
      ><a name="4058" href="StlcProp.html#4011" class="Bound"
      >t&#8321;&#8758;bool</a
      ><a name="4065"
      >
</a
      ><a name="4066" class="Symbol"
      >...</a
      ><a name="4069"
      > </a
      ><a name="4070" class="Symbol"
      >|</a
      ><a name="4071"
      > </a
      ><a name="4072" href="https://agda.github.io/agda-stdlib/Data.Sum.html#514" class="InductiveConstructor"
      >inj&#8322;</a
      ><a name="4076"
      > </a
      ><a name="4077" class="Symbol"
      >(_</a
      ><a name="4079"
      > </a
      ><a name="4080" href="https://agda.github.io/agda-stdlib/Data.Product.html#509" class="InductiveConstructor Operator"
      >,</a
      ><a name="4081"
      > </a
      ><a name="4082" href="StlcProp.html#4082" class="Bound"
      >t&#8321;&#8658;t&#8321;&#8242;</a
      ><a name="4088" class="Symbol"
      >)</a
      ><a name="4089"
      > </a
      ><a name="4090" class="Symbol"
      >=</a
      ><a name="4091"
      > </a
      ><a name="4092" href="https://agda.github.io/agda-stdlib/Data.Sum.html#514" class="InductiveConstructor"
      >inj&#8322;</a
      ><a name="4096"
      > </a
      ><a name="4097" class="Symbol"
      >(_</a
      ><a name="4099"
      > </a
      ><a name="4100" href="https://agda.github.io/agda-stdlib/Data.Product.html#509" class="InductiveConstructor Operator"
      >,</a
      ><a name="4101"
      > </a
      ><a name="4102" href="Stlc.html#15404" class="InductiveConstructor"
      >if</a
      ><a name="4104"
      > </a
      ><a name="4105" href="StlcProp.html#4082" class="Bound"
      >t&#8321;&#8658;t&#8321;&#8242;</a
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
      >v&#8321;</a
      ><a name="4126"
      >
    </a
      ><a name="4131" class="Keyword"
      >with</a
      ><a name="4135"
      > </a
      ><a name="4136" href="StlcProp.html#1272" class="Function"
      >canonicalForms</a
      ><a name="4150"
      > </a
      ><a name="4151" href="StlcProp.html#4011" class="Bound"
      >t&#8321;&#8758;bool</a
      ><a name="4158"
      > </a
      ><a name="4159" href="StlcProp.html#4124" class="Bound"
      >v&#8321;</a
      ><a name="4161"
      >
</a
      ><a name="4162" class="Symbol"
      >...</a
      ><a name="4165"
      > </a
      ><a name="4166" class="Symbol"
      >|</a
      ><a name="4167"
      > </a
      ><a name="4168" href="https://agda.github.io/agda-stdlib/Data.Sum.html#489" class="InductiveConstructor"
      >inj&#8321;</a
      ><a name="4172"
      > </a
      ><a name="4173" href="Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="4177"
      > </a
      ><a name="4178" class="Symbol"
      >=</a
      ><a name="4179"
      > </a
      ><a name="4180" href="https://agda.github.io/agda-stdlib/Data.Sum.html#514" class="InductiveConstructor"
      >inj&#8322;</a
      ><a name="4184"
      > </a
      ><a name="4185" class="Symbol"
      >(_</a
      ><a name="4187"
      > </a
      ><a name="4188" href="https://agda.github.io/agda-stdlib/Data.Product.html#509" class="InductiveConstructor Operator"
      >,</a
      ><a name="4189"
      > </a
      ><a name="4190" href="Stlc.html#15505" class="InductiveConstructor"
      >iftrue</a
      ><a name="4196" class="Symbol"
      >)</a
      ><a name="4197"
      >
</a
      ><a name="4198" class="Symbol"
      >...</a
      ><a name="4201"
      > </a
      ><a name="4202" class="Symbol"
      >|</a
      ><a name="4203"
      > </a
      ><a name="4204" href="https://agda.github.io/agda-stdlib/Data.Sum.html#514" class="InductiveConstructor"
      >inj&#8322;</a
      ><a name="4208"
      > </a
      ><a name="4209" href="Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="4213"
      > </a
      ><a name="4214" class="Symbol"
      >=</a
      ><a name="4215"
      > </a
      ><a name="4216" href="https://agda.github.io/agda-stdlib/Data.Sum.html#514" class="InductiveConstructor"
      >inj&#8322;</a
      ><a name="4220"
      > </a
      ><a name="4221" class="Symbol"
      >(_</a
      ><a name="4223"
      > </a
      ><a name="4224" href="https://agda.github.io/agda-stdlib/Data.Product.html#509" class="InductiveConstructor Operator"
      >,</a
      ><a name="4225"
      > </a
      ><a name="4226" href="Stlc.html#15565" class="InductiveConstructor"
      >iffalse</a
      ><a name="4233" class="Symbol"
      >)</a
      >
{% endraw %}</pre>

#### Exercise: 3 stars, optional (progress_from_term_ind)
Show that progress can also be proved by induction on terms
instead of induction on typing derivations.

<pre class="Agda">{% raw %}
<a name="4423" class="Keyword"
      >postulate</a
      ><a name="4432"
      >
  </a
      ><a name="4435" href="StlcProp.html#4435" class="Postulate"
      >progress&#8242;</a
      ><a name="4444"
      > </a
      ><a name="4445" class="Symbol"
      >:</a
      ><a name="4446"
      > </a
      ><a name="4447" class="Symbol"
      >&#8704;</a
      ><a name="4448"
      > </a
      ><a name="4455" class="Symbol"
      >&#8594;</a
      ><a name="4456"
      > </a
      ><a name="4457" href="Stlc.html#18187" class="Function"
      >&#8709;</a
      ><a name="4458"
      > </a
      ><a name="4459" href="Stlc.html#19119" class="Datatype Operator"
      >&#8866;</a
      ><a name="4460"
      > </a
      ><a name="4461" href="StlcProp.html#4450" class="Bound"
      >t</a
      ><a name="4462"
      > </a
      ><a name="4463" href="Stlc.html#19119" class="Datatype Operator"
      >&#8758;</a
      ><a name="4464"
      > </a
      ><a name="4465" href="StlcProp.html#4452" class="Bound"
      >A</a
      ><a name="4466"
      > </a
      ><a name="4467" class="Symbol"
      >&#8594;</a
      ><a name="4468"
      > </a
      ><a name="4469" href="Stlc.html#8969" class="Datatype"
      >Value</a
      ><a name="4474"
      > </a
      ><a name="4475" href="StlcProp.html#4450" class="Bound"
      >t</a
      ><a name="4476"
      > </a
      ><a name="4477" href="https://agda.github.io/agda-stdlib/Data.Sum.html#433" class="Datatype Operator"
      >&#8846;</a
      ><a name="4478"
      > </a
      ><a name="4479" href="https://agda.github.io/agda-stdlib/Data.Product.html#823" class="Function"
      >&#8707;</a
      ><a name="4480"
      > </a
      ><a name="4481" class="Symbol"
      >&#955;</a
      ><a name="4482"
      > </a
      ><a name="4483" href="StlcProp.html#4483" class="Bound"
      >t&#8242;</a
      ><a name="4485"
      > </a
      ><a name="4486" class="Symbol"
      >&#8594;</a
      ><a name="4487"
      > </a
      ><a name="4488" href="StlcProp.html#4450" class="Bound"
      >t</a
      ><a name="4489"
      > </a
      ><a name="4490" href="Stlc.html#15105" class="Datatype Operator"
      >==&gt;</a
      ><a name="4493"
      > </a
      ><a name="4494" href="StlcProp.html#4483" class="Bound"
      >t&#8242;</a
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

<pre class="Agda">{% raw %}
<a name="6917" class="Keyword"
      >data</a
      ><a name="6921"
      > </a
      ><a name="6922" href="StlcProp.html#6922" class="Datatype Operator"
      >_FreeIn_</a
      ><a name="6930"
      > </a
      ><a name="6931" class="Symbol"
      >(</a
      ><a name="6932" href="StlcProp.html#6932" class="Bound"
      >x</a
      ><a name="6933"
      > </a
      ><a name="6934" class="Symbol"
      >:</a
      ><a name="6935"
      > </a
      ><a name="6936" href="Maps.html#2275" class="Datatype"
      >Id</a
      ><a name="6938" class="Symbol"
      >)</a
      ><a name="6939"
      > </a
      ><a name="6940" class="Symbol"
      >:</a
      ><a name="6941"
      > </a
      ><a name="6942" href="Stlc.html#5630" class="Datatype"
      >Term</a
      ><a name="6946"
      > </a
      ><a name="6947" class="Symbol"
      >&#8594;</a
      ><a name="6948"
      > </a
      ><a name="6949" class="PrimitiveType"
      >Set</a
      ><a name="6952"
      > </a
      ><a name="6953" class="Keyword"
      >where</a
      ><a name="6958"
      >
  </a
      ><a name="6961" href="StlcProp.html#6961" class="InductiveConstructor"
      >var</a
      ><a name="6964"
      >  </a
      ><a name="6966" class="Symbol"
      >:</a
      ><a name="6967"
      > </a
      ><a name="6968" href="StlcProp.html#6932" class="Bound"
      >x</a
      ><a name="6969"
      > </a
      ><a name="6970" href="StlcProp.html#6922" class="Datatype Operator"
      >FreeIn</a
      ><a name="6976"
      > </a
      ><a name="6977" href="Stlc.html#5649" class="InductiveConstructor"
      >var</a
      ><a name="6980"
      > </a
      ><a name="6981" href="StlcProp.html#6932" class="Bound"
      >x</a
      ><a name="6982"
      >
  </a
      ><a name="6985" href="StlcProp.html#6985" class="InductiveConstructor"
      >abs</a
      ><a name="6988"
      >  </a
      ><a name="6990" class="Symbol"
      >:</a
      ><a name="6991"
      > </a
      ><a name="6992" class="Symbol"
      >&#8704;</a
      ><a name="6993"
      > </a
      ><a name="7002" class="Symbol"
      >&#8594;</a
      ><a name="7003"
      > </a
      ><a name="7004" href="StlcProp.html#6995" class="Bound"
      >y</a
      ><a name="7005"
      > </a
      ><a name="7006" href="https://agda.github.io/agda-stdlib/Relation.Binary.Core.html#4493" class="Function Operator"
      >&#8802;</a
      ><a name="7007"
      > </a
      ><a name="7008" href="StlcProp.html#6932" class="Bound"
      >x</a
      ><a name="7009"
      > </a
      ><a name="7010" class="Symbol"
      >&#8594;</a
      ><a name="7011"
      > </a
      ><a name="7012" href="StlcProp.html#6932" class="Bound"
      >x</a
      ><a name="7013"
      > </a
      ><a name="7014" href="StlcProp.html#6922" class="Datatype Operator"
      >FreeIn</a
      ><a name="7020"
      > </a
      ><a name="7021" href="StlcProp.html#6999" class="Bound"
      >t</a
      ><a name="7022"
      > </a
      ><a name="7023" class="Symbol"
      >&#8594;</a
      ><a name="7024"
      > </a
      ><a name="7025" href="StlcProp.html#6932" class="Bound"
      >x</a
      ><a name="7026"
      > </a
      ><a name="7027" href="StlcProp.html#6922" class="Datatype Operator"
      >FreeIn</a
      ><a name="7033"
      > </a
      ><a name="7034" href="Stlc.html#5698" class="InductiveConstructor"
      >abs</a
      ><a name="7037"
      > </a
      ><a name="7038" href="StlcProp.html#6995" class="Bound"
      >y</a
      ><a name="7039"
      > </a
      ><a name="7040" href="StlcProp.html#6997" class="Bound"
      >A</a
      ><a name="7041"
      > </a
      ><a name="7042" href="StlcProp.html#6999" class="Bound"
      >t</a
      ><a name="7043"
      >
  </a
      ><a name="7046" href="StlcProp.html#7046" class="InductiveConstructor"
      >app1</a
      ><a name="7050"
      > </a
      ><a name="7051" class="Symbol"
      >:</a
      ><a name="7052"
      > </a
      ><a name="7053" class="Symbol"
      >&#8704;</a
      ><a name="7054"
      > </a
      ><a name="7063" class="Symbol"
      >&#8594;</a
      ><a name="7064"
      > </a
      ><a name="7065" href="StlcProp.html#6932" class="Bound"
      >x</a
      ><a name="7066"
      > </a
      ><a name="7067" href="StlcProp.html#6922" class="Datatype Operator"
      >FreeIn</a
      ><a name="7073"
      > </a
      ><a name="7074" href="StlcProp.html#7056" class="Bound"
      >t&#8321;</a
      ><a name="7076"
      > </a
      ><a name="7077" class="Symbol"
      >&#8594;</a
      ><a name="7078"
      > </a
      ><a name="7079" href="StlcProp.html#6932" class="Bound"
      >x</a
      ><a name="7080"
      > </a
      ><a name="7081" href="StlcProp.html#6922" class="Datatype Operator"
      >FreeIn</a
      ><a name="7087"
      > </a
      ><a name="7088" href="Stlc.html#5669" class="InductiveConstructor"
      >app</a
      ><a name="7091"
      > </a
      ><a name="7092" href="StlcProp.html#7056" class="Bound"
      >t&#8321;</a
      ><a name="7094"
      > </a
      ><a name="7095" href="StlcProp.html#7059" class="Bound"
      >t&#8322;</a
      ><a name="7097"
      >
  </a
      ><a name="7100" href="StlcProp.html#7100" class="InductiveConstructor"
      >app2</a
      ><a name="7104"
      > </a
      ><a name="7105" class="Symbol"
      >:</a
      ><a name="7106"
      > </a
      ><a name="7107" class="Symbol"
      >&#8704;</a
      ><a name="7108"
      > </a
      ><a name="7117" class="Symbol"
      >&#8594;</a
      ><a name="7118"
      > </a
      ><a name="7119" href="StlcProp.html#6932" class="Bound"
      >x</a
      ><a name="7120"
      > </a
      ><a name="7121" href="StlcProp.html#6922" class="Datatype Operator"
      >FreeIn</a
      ><a name="7127"
      > </a
      ><a name="7128" href="StlcProp.html#7113" class="Bound"
      >t&#8322;</a
      ><a name="7130"
      > </a
      ><a name="7131" class="Symbol"
      >&#8594;</a
      ><a name="7132"
      > </a
      ><a name="7133" href="StlcProp.html#6932" class="Bound"
      >x</a
      ><a name="7134"
      > </a
      ><a name="7135" href="StlcProp.html#6922" class="Datatype Operator"
      >FreeIn</a
      ><a name="7141"
      > </a
      ><a name="7142" href="Stlc.html#5669" class="InductiveConstructor"
      >app</a
      ><a name="7145"
      > </a
      ><a name="7146" href="StlcProp.html#7110" class="Bound"
      >t&#8321;</a
      ><a name="7148"
      > </a
      ><a name="7149" href="StlcProp.html#7113" class="Bound"
      >t&#8322;</a
      ><a name="7151"
      >
  </a
      ><a name="7154" href="StlcProp.html#7154" class="InductiveConstructor"
      >if1</a
      ><a name="7157"
      >  </a
      ><a name="7159" class="Symbol"
      >:</a
      ><a name="7160"
      > </a
      ><a name="7161" class="Symbol"
      >&#8704;</a
      ><a name="7162"
      > </a
      ><a name="7174" class="Symbol"
      >&#8594;</a
      ><a name="7175"
      > </a
      ><a name="7176" href="StlcProp.html#6932" class="Bound"
      >x</a
      ><a name="7177"
      > </a
      ><a name="7178" href="StlcProp.html#6922" class="Datatype Operator"
      >FreeIn</a
      ><a name="7184"
      > </a
      ><a name="7185" href="StlcProp.html#7164" class="Bound"
      >t&#8321;</a
      ><a name="7187"
      > </a
      ><a name="7188" class="Symbol"
      >&#8594;</a
      ><a name="7189"
      > </a
      ><a name="7190" href="StlcProp.html#6932" class="Bound"
      >x</a
      ><a name="7191"
      > </a
      ><a name="7192" href="StlcProp.html#6922" class="Datatype Operator"
      >FreeIn</a
      ><a name="7198"
      > </a
      ><a name="7199" class="Symbol"
      >(</a
      ><a name="7200" href="Stlc.html#5762" class="InductiveConstructor Operator"
      >if</a
      ><a name="7202"
      > </a
      ><a name="7203" href="StlcProp.html#7164" class="Bound"
      >t&#8321;</a
      ><a name="7205"
      > </a
      ><a name="7206" href="Stlc.html#5762" class="InductiveConstructor Operator"
      >then</a
      ><a name="7210"
      > </a
      ><a name="7211" href="StlcProp.html#7167" class="Bound"
      >t&#8322;</a
      ><a name="7213"
      > </a
      ><a name="7214" href="Stlc.html#5762" class="InductiveConstructor Operator"
      >else</a
      ><a name="7218"
      > </a
      ><a name="7219" href="StlcProp.html#7170" class="Bound"
      >t&#8323;</a
      ><a name="7221" class="Symbol"
      >)</a
      ><a name="7222"
      >
  </a
      ><a name="7225" href="StlcProp.html#7225" class="InductiveConstructor"
      >if2</a
      ><a name="7228"
      >  </a
      ><a name="7230" class="Symbol"
      >:</a
      ><a name="7231"
      > </a
      ><a name="7232" class="Symbol"
      >&#8704;</a
      ><a name="7233"
      > </a
      ><a name="7245" class="Symbol"
      >&#8594;</a
      ><a name="7246"
      > </a
      ><a name="7247" href="StlcProp.html#6932" class="Bound"
      >x</a
      ><a name="7248"
      > </a
      ><a name="7249" href="StlcProp.html#6922" class="Datatype Operator"
      >FreeIn</a
      ><a name="7255"
      > </a
      ><a name="7256" href="StlcProp.html#7238" class="Bound"
      >t&#8322;</a
      ><a name="7258"
      > </a
      ><a name="7259" class="Symbol"
      >&#8594;</a
      ><a name="7260"
      > </a
      ><a name="7261" href="StlcProp.html#6932" class="Bound"
      >x</a
      ><a name="7262"
      > </a
      ><a name="7263" href="StlcProp.html#6922" class="Datatype Operator"
      >FreeIn</a
      ><a name="7269"
      > </a
      ><a name="7270" class="Symbol"
      >(</a
      ><a name="7271" href="Stlc.html#5762" class="InductiveConstructor Operator"
      >if</a
      ><a name="7273"
      > </a
      ><a name="7274" href="StlcProp.html#7235" class="Bound"
      >t&#8321;</a
      ><a name="7276"
      > </a
      ><a name="7277" href="Stlc.html#5762" class="InductiveConstructor Operator"
      >then</a
      ><a name="7281"
      > </a
      ><a name="7282" href="StlcProp.html#7238" class="Bound"
      >t&#8322;</a
      ><a name="7284"
      > </a
      ><a name="7285" href="Stlc.html#5762" class="InductiveConstructor Operator"
      >else</a
      ><a name="7289"
      > </a
      ><a name="7290" href="StlcProp.html#7241" class="Bound"
      >t&#8323;</a
      ><a name="7292" class="Symbol"
      >)</a
      ><a name="7293"
      >
  </a
      ><a name="7296" href="StlcProp.html#7296" class="InductiveConstructor"
      >if3</a
      ><a name="7299"
      >  </a
      ><a name="7301" class="Symbol"
      >:</a
      ><a name="7302"
      > </a
      ><a name="7303" class="Symbol"
      >&#8704;</a
      ><a name="7304"
      > </a
      ><a name="7316" class="Symbol"
      >&#8594;</a
      ><a name="7317"
      > </a
      ><a name="7318" href="StlcProp.html#6932" class="Bound"
      >x</a
      ><a name="7319"
      > </a
      ><a name="7320" href="StlcProp.html#6922" class="Datatype Operator"
      >FreeIn</a
      ><a name="7326"
      > </a
      ><a name="7327" href="StlcProp.html#7312" class="Bound"
      >t&#8323;</a
      ><a name="7329"
      > </a
      ><a name="7330" class="Symbol"
      >&#8594;</a
      ><a name="7331"
      > </a
      ><a name="7332" href="StlcProp.html#6932" class="Bound"
      >x</a
      ><a name="7333"
      > </a
      ><a name="7334" href="StlcProp.html#6922" class="Datatype Operator"
      >FreeIn</a
      ><a name="7340"
      > </a
      ><a name="7341" class="Symbol"
      >(</a
      ><a name="7342" href="Stlc.html#5762" class="InductiveConstructor Operator"
      >if</a
      ><a name="7344"
      > </a
      ><a name="7345" href="StlcProp.html#7306" class="Bound"
      >t&#8321;</a
      ><a name="7347"
      > </a
      ><a name="7348" href="Stlc.html#5762" class="InductiveConstructor Operator"
      >then</a
      ><a name="7352"
      > </a
      ><a name="7353" href="StlcProp.html#7309" class="Bound"
      >t&#8322;</a
      ><a name="7355"
      > </a
      ><a name="7356" href="Stlc.html#5762" class="InductiveConstructor Operator"
      >else</a
      ><a name="7360"
      > </a
      ><a name="7361" href="StlcProp.html#7312" class="Bound"
      >t&#8323;</a
      ><a name="7363" class="Symbol"
      >)</a
      >
{% endraw %}</pre>

A term in which no variables appear free is said to be _closed_.

<pre class="Agda">{% raw %}
<a name="7456" href="StlcProp.html#7456" class="Function"
      >Closed</a
      ><a name="7462"
      > </a
      ><a name="7463" class="Symbol"
      >:</a
      ><a name="7464"
      > </a
      ><a name="7465" href="Stlc.html#5630" class="Datatype"
      >Term</a
      ><a name="7469"
      > </a
      ><a name="7470" class="Symbol"
      >&#8594;</a
      ><a name="7471"
      > </a
      ><a name="7472" class="PrimitiveType"
      >Set</a
      ><a name="7475"
      >
</a
      ><a name="7476" href="StlcProp.html#7456" class="Function"
      >Closed</a
      ><a name="7482"
      > </a
      ><a name="7483" href="StlcProp.html#7483" class="Bound"
      >t</a
      ><a name="7484"
      > </a
      ><a name="7485" class="Symbol"
      >=</a
      ><a name="7486"
      > </a
      ><a name="7487" class="Symbol"
      >&#8704;</a
      ><a name="7488"
      > </a
      ><a name="7493" class="Symbol"
      >&#8594;</a
      ><a name="7494"
      > </a
      ><a name="7495" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#414" class="Function Operator"
      >&#172;</a
      ><a name="7496"
      > </a
      ><a name="7497" class="Symbol"
      >(</a
      ><a name="7498" href="StlcProp.html#7490" class="Bound"
      >x</a
      ><a name="7499"
      > </a
      ><a name="7500" href="StlcProp.html#6922" class="Datatype Operator"
      >FreeIn</a
      ><a name="7506"
      > </a
      ><a name="7507" href="StlcProp.html#7483" class="Bound"
      >t</a
      ><a name="7508" class="Symbol"
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
a variable $$x$$ appears free in a term $$t$$, and if we know $$t$$ is
well typed in context $$\Gamma$$, then it must be the case that
$$\Gamma$$ assigns a type to $$x$$.

<pre class="Agda">{% raw %}
<a name="8237" href="StlcProp.html#8237" class="Function"
      >freeInCtxt</a
      ><a name="8247"
      > </a
      ><a name="8248" class="Symbol"
      >:</a
      ><a name="8249"
      > </a
      ><a name="8250" class="Symbol"
      >&#8704;</a
      ><a name="8251"
      > </a
      ><a name="8262" class="Symbol"
      >&#8594;</a
      ><a name="8263"
      > </a
      ><a name="8264" href="StlcProp.html#8253" class="Bound"
      >x</a
      ><a name="8265"
      > </a
      ><a name="8266" href="StlcProp.html#6922" class="Datatype Operator"
      >FreeIn</a
      ><a name="8272"
      > </a
      ><a name="8273" href="StlcProp.html#8255" class="Bound"
      >t</a
      ><a name="8274"
      > </a
      ><a name="8275" class="Symbol"
      >&#8594;</a
      ><a name="8276"
      > </a
      ><a name="8277" href="StlcProp.html#8259" class="Bound"
      >&#915;</a
      ><a name="8278"
      > </a
      ><a name="8279" href="Stlc.html#19119" class="Datatype Operator"
      >&#8866;</a
      ><a name="8280"
      > </a
      ><a name="8281" href="StlcProp.html#8255" class="Bound"
      >t</a
      ><a name="8282"
      > </a
      ><a name="8283" href="Stlc.html#19119" class="Datatype Operator"
      >&#8758;</a
      ><a name="8284"
      > </a
      ><a name="8285" href="StlcProp.html#8257" class="Bound"
      >A</a
      ><a name="8286"
      > </a
      ><a name="8287" class="Symbol"
      >&#8594;</a
      ><a name="8288"
      > </a
      ><a name="8289" href="https://agda.github.io/agda-stdlib/Data.Product.html#823" class="Function"
      >&#8707;</a
      ><a name="8290"
      > </a
      ><a name="8291" class="Symbol"
      >&#955;</a
      ><a name="8292"
      > </a
      ><a name="8293" href="StlcProp.html#8293" class="Bound"
      >B</a
      ><a name="8294"
      > </a
      ><a name="8295" class="Symbol"
      >&#8594;</a
      ><a name="8296"
      > </a
      ><a name="8297" href="StlcProp.html#8259" class="Bound"
      >&#915;</a
      ><a name="8298"
      > </a
      ><a name="8299" href="StlcProp.html#8253" class="Bound"
      >x</a
      ><a name="8300"
      > </a
      ><a name="8301" href="Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="8302"
      > </a
      ><a name="8303" href="https://agda.github.io/agda-stdlib/Data.Maybe.Base.html#373" class="InductiveConstructor"
      >just</a
      ><a name="8307"
      > </a
      ><a name="8308" href="StlcProp.html#8293" class="Bound"
      >B</a
      >
{% endraw %}</pre>

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

<pre class="Agda">{% raw %}
<a name="9904" href="StlcProp.html#8237" class="Function"
      >freeInCtxt</a
      ><a name="9914"
      > </a
      ><a name="9915" href="StlcProp.html#6961" class="InductiveConstructor"
      >var</a
      ><a name="9918"
      > </a
      ><a name="9919" class="Symbol"
      >(</a
      ><a name="9920" href="Stlc.html#19163" class="InductiveConstructor"
      >var</a
      ><a name="9923"
      > </a
      ><a name="9924" class="Symbol"
      >_</a
      ><a name="9925"
      > </a
      ><a name="9926" href="StlcProp.html#9926" class="Bound"
      >x&#8758;A</a
      ><a name="9929" class="Symbol"
      >)</a
      ><a name="9930"
      > </a
      ><a name="9931" class="Symbol"
      >=</a
      ><a name="9932"
      > </a
      ><a name="9933" class="Symbol"
      >(_</a
      ><a name="9935"
      > </a
      ><a name="9936" href="https://agda.github.io/agda-stdlib/Data.Product.html#509" class="InductiveConstructor Operator"
      >,</a
      ><a name="9937"
      > </a
      ><a name="9938" href="StlcProp.html#9926" class="Bound"
      >x&#8758;A</a
      ><a name="9941" class="Symbol"
      >)</a
      ><a name="9942"
      >
</a
      ><a name="9943" href="StlcProp.html#8237" class="Function"
      >freeInCtxt</a
      ><a name="9953"
      > </a
      ><a name="9954" class="Symbol"
      >(</a
      ><a name="9955" href="StlcProp.html#7046" class="InductiveConstructor"
      >app1</a
      ><a name="9959"
      > </a
      ><a name="9960" href="StlcProp.html#9960" class="Bound"
      >x&#8712;t&#8321;</a
      ><a name="9964" class="Symbol"
      >)</a
      ><a name="9965"
      > </a
      ><a name="9966" class="Symbol"
      >(</a
      ><a name="9967" href="Stlc.html#19372" class="InductiveConstructor"
      >app</a
      ><a name="9970"
      > </a
      ><a name="9971" href="StlcProp.html#9971" class="Bound"
      >t&#8321;&#8758;A</a
      ><a name="9975"
      > </a
      ><a name="9976" class="Symbol"
      >_</a
      ><a name="9977"
      >   </a
      ><a name="9980" class="Symbol"
      >)</a
      ><a name="9981"
      > </a
      ><a name="9982" class="Symbol"
      >=</a
      ><a name="9983"
      > </a
      ><a name="9984" href="StlcProp.html#8237" class="Function"
      >freeInCtxt</a
      ><a name="9994"
      > </a
      ><a name="9995" href="StlcProp.html#9960" class="Bound"
      >x&#8712;t&#8321;</a
      ><a name="9999"
      > </a
      ><a name="10000" href="StlcProp.html#9971" class="Bound"
      >t&#8321;&#8758;A</a
      ><a name="10004"
      >
</a
      ><a name="10005" href="StlcProp.html#8237" class="Function"
      >freeInCtxt</a
      ><a name="10015"
      > </a
      ><a name="10016" class="Symbol"
      >(</a
      ><a name="10017" href="StlcProp.html#7100" class="InductiveConstructor"
      >app2</a
      ><a name="10021"
      > </a
      ><a name="10022" href="StlcProp.html#10022" class="Bound"
      >x&#8712;t&#8322;</a
      ><a name="10026" class="Symbol"
      >)</a
      ><a name="10027"
      > </a
      ><a name="10028" class="Symbol"
      >(</a
      ><a name="10029" href="Stlc.html#19372" class="InductiveConstructor"
      >app</a
      ><a name="10032"
      > </a
      ><a name="10033" class="Symbol"
      >_</a
      ><a name="10034"
      >    </a
      ><a name="10038" href="StlcProp.html#10038" class="Bound"
      >t&#8322;&#8758;A</a
      ><a name="10042" class="Symbol"
      >)</a
      ><a name="10043"
      > </a
      ><a name="10044" class="Symbol"
      >=</a
      ><a name="10045"
      > </a
      ><a name="10046" href="StlcProp.html#8237" class="Function"
      >freeInCtxt</a
      ><a name="10056"
      > </a
      ><a name="10057" href="StlcProp.html#10022" class="Bound"
      >x&#8712;t&#8322;</a
      ><a name="10061"
      > </a
      ><a name="10062" href="StlcProp.html#10038" class="Bound"
      >t&#8322;&#8758;A</a
      ><a name="10066"
      >
</a
      ><a name="10067" href="StlcProp.html#8237" class="Function"
      >freeInCtxt</a
      ><a name="10077"
      > </a
      ><a name="10078" class="Symbol"
      >(</a
      ><a name="10079" href="StlcProp.html#7154" class="InductiveConstructor"
      >if1</a
      ><a name="10082"
      >  </a
      ><a name="10084" href="StlcProp.html#10084" class="Bound"
      >x&#8712;t&#8321;</a
      ><a name="10088" class="Symbol"
      >)</a
      ><a name="10089"
      > </a
      ><a name="10090" class="Symbol"
      >(</a
      ><a name="10091" href="Stlc.html#19624" class="InductiveConstructor Operator"
      >if</a
      ><a name="10093"
      > </a
      ><a name="10094" href="StlcProp.html#10094" class="Bound"
      >t&#8321;&#8758;A</a
      ><a name="10098"
      > </a
      ><a name="10099" href="Stlc.html#19624" class="InductiveConstructor Operator"
      >then</a
      ><a name="10103"
      > </a
      ><a name="10104" class="Symbol"
      >_</a
      ><a name="10105"
      >    </a
      ><a name="10109" href="Stlc.html#19624" class="InductiveConstructor Operator"
      >else</a
      ><a name="10113"
      > </a
      ><a name="10114" class="Symbol"
      >_</a
      ><a name="10115"
      >   </a
      ><a name="10118" class="Symbol"
      >)</a
      ><a name="10119"
      > </a
      ><a name="10120" class="Symbol"
      >=</a
      ><a name="10121"
      > </a
      ><a name="10122" href="StlcProp.html#8237" class="Function"
      >freeInCtxt</a
      ><a name="10132"
      > </a
      ><a name="10133" href="StlcProp.html#10084" class="Bound"
      >x&#8712;t&#8321;</a
      ><a name="10137"
      > </a
      ><a name="10138" href="StlcProp.html#10094" class="Bound"
      >t&#8321;&#8758;A</a
      ><a name="10142"
      >
</a
      ><a name="10143" href="StlcProp.html#8237" class="Function"
      >freeInCtxt</a
      ><a name="10153"
      > </a
      ><a name="10154" class="Symbol"
      >(</a
      ><a name="10155" href="StlcProp.html#7225" class="InductiveConstructor"
      >if2</a
      ><a name="10158"
      >  </a
      ><a name="10160" href="StlcProp.html#10160" class="Bound"
      >x&#8712;t&#8322;</a
      ><a name="10164" class="Symbol"
      >)</a
      ><a name="10165"
      > </a
      ><a name="10166" class="Symbol"
      >(</a
      ><a name="10167" href="Stlc.html#19624" class="InductiveConstructor Operator"
      >if</a
      ><a name="10169"
      > </a
      ><a name="10170" class="Symbol"
      >_</a
      ><a name="10171"
      >    </a
      ><a name="10175" href="Stlc.html#19624" class="InductiveConstructor Operator"
      >then</a
      ><a name="10179"
      > </a
      ><a name="10180" href="StlcProp.html#10180" class="Bound"
      >t&#8322;&#8758;A</a
      ><a name="10184"
      > </a
      ><a name="10185" href="Stlc.html#19624" class="InductiveConstructor Operator"
      >else</a
      ><a name="10189"
      > </a
      ><a name="10190" class="Symbol"
      >_</a
      ><a name="10191"
      >   </a
      ><a name="10194" class="Symbol"
      >)</a
      ><a name="10195"
      > </a
      ><a name="10196" class="Symbol"
      >=</a
      ><a name="10197"
      > </a
      ><a name="10198" href="StlcProp.html#8237" class="Function"
      >freeInCtxt</a
      ><a name="10208"
      > </a
      ><a name="10209" href="StlcProp.html#10160" class="Bound"
      >x&#8712;t&#8322;</a
      ><a name="10213"
      > </a
      ><a name="10214" href="StlcProp.html#10180" class="Bound"
      >t&#8322;&#8758;A</a
      ><a name="10218"
      >
</a
      ><a name="10219" href="StlcProp.html#8237" class="Function"
      >freeInCtxt</a
      ><a name="10229"
      > </a
      ><a name="10230" class="Symbol"
      >(</a
      ><a name="10231" href="StlcProp.html#7296" class="InductiveConstructor"
      >if3</a
      ><a name="10234"
      >  </a
      ><a name="10236" href="StlcProp.html#10236" class="Bound"
      >x&#8712;t&#8323;</a
      ><a name="10240" class="Symbol"
      >)</a
      ><a name="10241"
      > </a
      ><a name="10242" class="Symbol"
      >(</a
      ><a name="10243" href="Stlc.html#19624" class="InductiveConstructor Operator"
      >if</a
      ><a name="10245"
      > </a
      ><a name="10246" class="Symbol"
      >_</a
      ><a name="10247"
      >    </a
      ><a name="10251" href="Stlc.html#19624" class="InductiveConstructor Operator"
      >then</a
      ><a name="10255"
      > </a
      ><a name="10256" class="Symbol"
      >_</a
      ><a name="10257"
      >    </a
      ><a name="10261" href="Stlc.html#19624" class="InductiveConstructor Operator"
      >else</a
      ><a name="10265"
      > </a
      ><a name="10266" href="StlcProp.html#10266" class="Bound"
      >t&#8323;&#8758;A</a
      ><a name="10270" class="Symbol"
      >)</a
      ><a name="10271"
      > </a
      ><a name="10272" class="Symbol"
      >=</a
      ><a name="10273"
      > </a
      ><a name="10274" href="StlcProp.html#8237" class="Function"
      >freeInCtxt</a
      ><a name="10284"
      > </a
      ><a name="10285" href="StlcProp.html#10236" class="Bound"
      >x&#8712;t&#8323;</a
      ><a name="10289"
      > </a
      ><a name="10290" href="StlcProp.html#10266" class="Bound"
      >t&#8323;&#8758;A</a
      ><a name="10294"
      >
</a
      ><a name="10295" href="StlcProp.html#8237" class="Function"
      >freeInCtxt</a
      ><a name="10305"
      > </a
      ><a name="10310" class="Symbol"
      >(</a
      ><a name="10311" href="StlcProp.html#6985" class="InductiveConstructor"
      >abs</a
      ><a name="10314"
      > </a
      ><a name="10319" href="StlcProp.html#10319" class="Bound"
      >y&#8800;x</a
      ><a name="10322"
      > </a
      ><a name="10323" href="StlcProp.html#10323" class="Bound"
      >x&#8712;t</a
      ><a name="10326" class="Symbol"
      >)</a
      ><a name="10327"
      > </a
      ><a name="10328" class="Symbol"
      >(</a
      ><a name="10329" href="Stlc.html#19256" class="InductiveConstructor"
      >abs</a
      ><a name="10332"
      > </a
      ><a name="10333" href="StlcProp.html#10333" class="Bound"
      >t&#8758;B</a
      ><a name="10336" class="Symbol"
      >)</a
      ><a name="10337"
      >
    </a
      ><a name="10342" class="Keyword"
      >with</a
      ><a name="10346"
      > </a
      ><a name="10347" href="StlcProp.html#8237" class="Function"
      >freeInCtxt</a
      ><a name="10357"
      > </a
      ><a name="10358" href="StlcProp.html#10323" class="Bound"
      >x&#8712;t</a
      ><a name="10361"
      > </a
      ><a name="10362" href="StlcProp.html#10333" class="Bound"
      >t&#8758;B</a
      ><a name="10365"
      >
</a
      ><a name="10366" class="Symbol"
      >...</a
      ><a name="10369"
      > </a
      ><a name="10370" class="Symbol"
      >|</a
      ><a name="10371"
      > </a
      ><a name="10372" href="StlcProp.html#10372" class="Bound"
      >x&#8758;A</a
      ><a name="10375"
      >
    </a
      ><a name="10380" class="Keyword"
      >with</a
      ><a name="10384"
      > </a
      ><a name="10385" href="StlcProp.html#10316" class="Bound"
      >y</a
      ><a name="10386"
      > </a
      ><a name="10387" href="Maps.html#2329" class="Function Operator"
      >&#8799;</a
      ><a name="10388"
      > </a
      ><a name="10389" href="StlcProp.html#10307" class="Bound"
      >x</a
      ><a name="10390"
      >
</a
      ><a name="10391" class="Symbol"
      >...</a
      ><a name="10394"
      > </a
      ><a name="10395" class="Symbol"
      >|</a
      ><a name="10396"
      > </a
      ><a name="10397" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#520" class="InductiveConstructor"
      >yes</a
      ><a name="10400"
      > </a
      ><a name="10401" href="StlcProp.html#10401" class="Bound"
      >y=x</a
      ><a name="10404"
      > </a
      ><a name="10405" class="Symbol"
      >=</a
      ><a name="10406"
      > </a
      ><a name="10407" href="https://agda.github.io/agda-stdlib/Data.Empty.html#348" class="Function"
      >&#8869;-elim</a
      ><a name="10413"
      > </a
      ><a name="10414" class="Symbol"
      >(</a
      ><a name="10415" href="StlcProp.html#10319" class="Bound"
      >y&#8800;x</a
      ><a name="10418"
      > </a
      ><a name="10419" href="StlcProp.html#10401" class="Bound"
      >y=x</a
      ><a name="10422" class="Symbol"
      >)</a
      ><a name="10423"
      >
</a
      ><a name="10424" class="Symbol"
      >...</a
      ><a name="10427"
      > </a
      ><a name="10428" class="Symbol"
      >|</a
      ><a name="10429"
      > </a
      ><a name="10430" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#547" class="InductiveConstructor"
      >no</a
      ><a name="10432"
      >  </a
      ><a name="10434" class="Symbol"
      >_</a
      ><a name="10435"
      >   </a
      ><a name="10438" class="Symbol"
      >=</a
      ><a name="10439"
      > </a
      ><a name="10440" href="StlcProp.html#10372" class="Bound"
      >x&#8758;A</a
      >
{% endraw %}</pre>

Next, we'll need the fact that any term $$t$$ which is well typed in
the empty context is closed (it has no free variables).

#### Exercise: 2 stars, optional (∅⊢-closed)

<pre class="Agda">{% raw %}
<a name="10641" class="Keyword"
      >postulate</a
      ><a name="10650"
      >
  </a
      ><a name="10653" href="StlcProp.html#10653" class="Postulate"
      >&#8709;&#8866;-closed</a
      ><a name="10662"
      > </a
      ><a name="10663" class="Symbol"
      >:</a
      ><a name="10664"
      > </a
      ><a name="10665" class="Symbol"
      >&#8704;</a
      ><a name="10666"
      > </a
      ><a name="10673" class="Symbol"
      >&#8594;</a
      ><a name="10674"
      > </a
      ><a name="10675" href="Stlc.html#18187" class="Function"
      >&#8709;</a
      ><a name="10676"
      > </a
      ><a name="10677" href="Stlc.html#19119" class="Datatype Operator"
      >&#8866;</a
      ><a name="10678"
      > </a
      ><a name="10679" href="StlcProp.html#10668" class="Bound"
      >t</a
      ><a name="10680"
      > </a
      ><a name="10681" href="Stlc.html#19119" class="Datatype Operator"
      >&#8758;</a
      ><a name="10682"
      > </a
      ><a name="10683" href="StlcProp.html#10670" class="Bound"
      >A</a
      ><a name="10684"
      > </a
      ><a name="10685" class="Symbol"
      >&#8594;</a
      ><a name="10686"
      > </a
      ><a name="10687" href="StlcProp.html#7456" class="Function"
      >Closed</a
      ><a name="10693"
      > </a
      ><a name="10694" href="StlcProp.html#10668" class="Bound"
      >t</a
      >
{% endraw %}</pre>

<div class="hidden">
<pre class="Agda">{% raw %}
<a name="10742" href="StlcProp.html#10742" class="Function"
      >&#8709;&#8866;-closed&#8242;</a
      ><a name="10752"
      > </a
      ><a name="10753" class="Symbol"
      >:</a
      ><a name="10754"
      > </a
      ><a name="10755" class="Symbol"
      >&#8704;</a
      ><a name="10756"
      > </a
      ><a name="10763" class="Symbol"
      >&#8594;</a
      ><a name="10764"
      > </a
      ><a name="10765" href="Stlc.html#18187" class="Function"
      >&#8709;</a
      ><a name="10766"
      > </a
      ><a name="10767" href="Stlc.html#19119" class="Datatype Operator"
      >&#8866;</a
      ><a name="10768"
      > </a
      ><a name="10769" href="StlcProp.html#10758" class="Bound"
      >t</a
      ><a name="10770"
      > </a
      ><a name="10771" href="Stlc.html#19119" class="Datatype Operator"
      >&#8758;</a
      ><a name="10772"
      > </a
      ><a name="10773" href="StlcProp.html#10760" class="Bound"
      >A</a
      ><a name="10774"
      > </a
      ><a name="10775" class="Symbol"
      >&#8594;</a
      ><a name="10776"
      > </a
      ><a name="10777" href="StlcProp.html#7456" class="Function"
      >Closed</a
      ><a name="10783"
      > </a
      ><a name="10784" href="StlcProp.html#10758" class="Bound"
      >t</a
      ><a name="10785"
      >
</a
      ><a name="10786" href="StlcProp.html#10742" class="Function"
      >&#8709;&#8866;-closed&#8242;</a
      ><a name="10796"
      > </a
      ><a name="10797" class="Symbol"
      >(</a
      ><a name="10798" href="Stlc.html#19163" class="InductiveConstructor"
      >var</a
      ><a name="10801"
      > </a
      ><a name="10802" href="StlcProp.html#10802" class="Bound"
      >x</a
      ><a name="10803"
      > </a
      ><a name="10804" class="Symbol"
      >())</a
      ><a name="10807"
      >
</a
      ><a name="10808" href="StlcProp.html#10742" class="Function"
      >&#8709;&#8866;-closed&#8242;</a
      ><a name="10818"
      > </a
      ><a name="10819" class="Symbol"
      >(</a
      ><a name="10820" href="Stlc.html#19372" class="InductiveConstructor"
      >app</a
      ><a name="10823"
      > </a
      ><a name="10824" href="StlcProp.html#10824" class="Bound"
      >t&#8321;&#8758;A&#8658;B</a
      ><a name="10830"
      > </a
      ><a name="10831" href="StlcProp.html#10831" class="Bound"
      >t&#8322;&#8758;A</a
      ><a name="10835" class="Symbol"
      >)</a
      ><a name="10836"
      > </a
      ><a name="10837" class="Symbol"
      >(</a
      ><a name="10838" href="StlcProp.html#7046" class="InductiveConstructor"
      >app1</a
      ><a name="10842"
      > </a
      ><a name="10843" href="StlcProp.html#10843" class="Bound"
      >x&#8712;t&#8321;</a
      ><a name="10847" class="Symbol"
      >)</a
      ><a name="10848"
      > </a
      ><a name="10849" class="Symbol"
      >=</a
      ><a name="10850"
      > </a
      ><a name="10851" href="StlcProp.html#10742" class="Function"
      >&#8709;&#8866;-closed&#8242;</a
      ><a name="10861"
      > </a
      ><a name="10862" href="StlcProp.html#10824" class="Bound"
      >t&#8321;&#8758;A&#8658;B</a
      ><a name="10868"
      > </a
      ><a name="10869" href="StlcProp.html#10843" class="Bound"
      >x&#8712;t&#8321;</a
      ><a name="10873"
      >
</a
      ><a name="10874" href="StlcProp.html#10742" class="Function"
      >&#8709;&#8866;-closed&#8242;</a
      ><a name="10884"
      > </a
      ><a name="10885" class="Symbol"
      >(</a
      ><a name="10886" href="Stlc.html#19372" class="InductiveConstructor"
      >app</a
      ><a name="10889"
      > </a
      ><a name="10890" href="StlcProp.html#10890" class="Bound"
      >t&#8321;&#8758;A&#8658;B</a
      ><a name="10896"
      > </a
      ><a name="10897" href="StlcProp.html#10897" class="Bound"
      >t&#8322;&#8758;A</a
      ><a name="10901" class="Symbol"
      >)</a
      ><a name="10902"
      > </a
      ><a name="10903" class="Symbol"
      >(</a
      ><a name="10904" href="StlcProp.html#7100" class="InductiveConstructor"
      >app2</a
      ><a name="10908"
      > </a
      ><a name="10909" href="StlcProp.html#10909" class="Bound"
      >x&#8712;t&#8322;</a
      ><a name="10913" class="Symbol"
      >)</a
      ><a name="10914"
      > </a
      ><a name="10915" class="Symbol"
      >=</a
      ><a name="10916"
      > </a
      ><a name="10917" href="StlcProp.html#10742" class="Function"
      >&#8709;&#8866;-closed&#8242;</a
      ><a name="10927"
      > </a
      ><a name="10928" href="StlcProp.html#10897" class="Bound"
      >t&#8322;&#8758;A</a
      ><a name="10932"
      > </a
      ><a name="10933" href="StlcProp.html#10909" class="Bound"
      >x&#8712;t&#8322;</a
      ><a name="10937"
      >
</a
      ><a name="10938" href="StlcProp.html#10742" class="Function"
      >&#8709;&#8866;-closed&#8242;</a
      ><a name="10948"
      > </a
      ><a name="10949" href="Stlc.html#19506" class="InductiveConstructor"
      >true</a
      ><a name="10953"
      >  </a
      ><a name="10955" class="Symbol"
      >()</a
      ><a name="10957"
      >
</a
      ><a name="10958" href="StlcProp.html#10742" class="Function"
      >&#8709;&#8866;-closed&#8242;</a
      ><a name="10968"
      > </a
      ><a name="10969" href="Stlc.html#19565" class="InductiveConstructor"
      >false</a
      ><a name="10974"
      > </a
      ><a name="10975" class="Symbol"
      >()</a
      ><a name="10977"
      >
</a
      ><a name="10978" href="StlcProp.html#10742" class="Function"
      >&#8709;&#8866;-closed&#8242;</a
      ><a name="10988"
      > </a
      ><a name="10989" class="Symbol"
      >(</a
      ><a name="10990" href="Stlc.html#19624" class="InductiveConstructor Operator"
      >if</a
      ><a name="10992"
      > </a
      ><a name="10993" href="StlcProp.html#10993" class="Bound"
      >t&#8321;&#8758;bool</a
      ><a name="11000"
      > </a
      ><a name="11001" href="Stlc.html#19624" class="InductiveConstructor Operator"
      >then</a
      ><a name="11005"
      > </a
      ><a name="11006" href="StlcProp.html#11006" class="Bound"
      >t&#8322;&#8758;A</a
      ><a name="11010"
      > </a
      ><a name="11011" href="Stlc.html#19624" class="InductiveConstructor Operator"
      >else</a
      ><a name="11015"
      > </a
      ><a name="11016" href="StlcProp.html#11016" class="Bound"
      >t&#8323;&#8758;A</a
      ><a name="11020" class="Symbol"
      >)</a
      ><a name="11021"
      > </a
      ><a name="11022" class="Symbol"
      >(</a
      ><a name="11023" href="StlcProp.html#7154" class="InductiveConstructor"
      >if1</a
      ><a name="11026"
      > </a
      ><a name="11027" href="StlcProp.html#11027" class="Bound"
      >x&#8712;t&#8321;</a
      ><a name="11031" class="Symbol"
      >)</a
      ><a name="11032"
      > </a
      ><a name="11033" class="Symbol"
      >=</a
      ><a name="11034"
      > </a
      ><a name="11035" href="StlcProp.html#10742" class="Function"
      >&#8709;&#8866;-closed&#8242;</a
      ><a name="11045"
      > </a
      ><a name="11046" href="StlcProp.html#10993" class="Bound"
      >t&#8321;&#8758;bool</a
      ><a name="11053"
      > </a
      ><a name="11054" href="StlcProp.html#11027" class="Bound"
      >x&#8712;t&#8321;</a
      ><a name="11058"
      >
</a
      ><a name="11059" href="StlcProp.html#10742" class="Function"
      >&#8709;&#8866;-closed&#8242;</a
      ><a name="11069"
      > </a
      ><a name="11070" class="Symbol"
      >(</a
      ><a name="11071" href="Stlc.html#19624" class="InductiveConstructor Operator"
      >if</a
      ><a name="11073"
      > </a
      ><a name="11074" href="StlcProp.html#11074" class="Bound"
      >t&#8321;&#8758;bool</a
      ><a name="11081"
      > </a
      ><a name="11082" href="Stlc.html#19624" class="InductiveConstructor Operator"
      >then</a
      ><a name="11086"
      > </a
      ><a name="11087" href="StlcProp.html#11087" class="Bound"
      >t&#8322;&#8758;A</a
      ><a name="11091"
      > </a
      ><a name="11092" href="Stlc.html#19624" class="InductiveConstructor Operator"
      >else</a
      ><a name="11096"
      > </a
      ><a name="11097" href="StlcProp.html#11097" class="Bound"
      >t&#8323;&#8758;A</a
      ><a name="11101" class="Symbol"
      >)</a
      ><a name="11102"
      > </a
      ><a name="11103" class="Symbol"
      >(</a
      ><a name="11104" href="StlcProp.html#7225" class="InductiveConstructor"
      >if2</a
      ><a name="11107"
      > </a
      ><a name="11108" href="StlcProp.html#11108" class="Bound"
      >x&#8712;t&#8322;</a
      ><a name="11112" class="Symbol"
      >)</a
      ><a name="11113"
      > </a
      ><a name="11114" class="Symbol"
      >=</a
      ><a name="11115"
      > </a
      ><a name="11116" href="StlcProp.html#10742" class="Function"
      >&#8709;&#8866;-closed&#8242;</a
      ><a name="11126"
      > </a
      ><a name="11127" href="StlcProp.html#11087" class="Bound"
      >t&#8322;&#8758;A</a
      ><a name="11131"
      > </a
      ><a name="11132" href="StlcProp.html#11108" class="Bound"
      >x&#8712;t&#8322;</a
      ><a name="11136"
      >
</a
      ><a name="11137" href="StlcProp.html#10742" class="Function"
      >&#8709;&#8866;-closed&#8242;</a
      ><a name="11147"
      > </a
      ><a name="11148" class="Symbol"
      >(</a
      ><a name="11149" href="Stlc.html#19624" class="InductiveConstructor Operator"
      >if</a
      ><a name="11151"
      > </a
      ><a name="11152" href="StlcProp.html#11152" class="Bound"
      >t&#8321;&#8758;bool</a
      ><a name="11159"
      > </a
      ><a name="11160" href="Stlc.html#19624" class="InductiveConstructor Operator"
      >then</a
      ><a name="11164"
      > </a
      ><a name="11165" href="StlcProp.html#11165" class="Bound"
      >t&#8322;&#8758;A</a
      ><a name="11169"
      > </a
      ><a name="11170" href="Stlc.html#19624" class="InductiveConstructor Operator"
      >else</a
      ><a name="11174"
      > </a
      ><a name="11175" href="StlcProp.html#11175" class="Bound"
      >t&#8323;&#8758;A</a
      ><a name="11179" class="Symbol"
      >)</a
      ><a name="11180"
      > </a
      ><a name="11181" class="Symbol"
      >(</a
      ><a name="11182" href="StlcProp.html#7296" class="InductiveConstructor"
      >if3</a
      ><a name="11185"
      > </a
      ><a name="11186" href="StlcProp.html#11186" class="Bound"
      >x&#8712;t&#8323;</a
      ><a name="11190" class="Symbol"
      >)</a
      ><a name="11191"
      > </a
      ><a name="11192" class="Symbol"
      >=</a
      ><a name="11193"
      > </a
      ><a name="11194" href="StlcProp.html#10742" class="Function"
      >&#8709;&#8866;-closed&#8242;</a
      ><a name="11204"
      > </a
      ><a name="11205" href="StlcProp.html#11175" class="Bound"
      >t&#8323;&#8758;A</a
      ><a name="11209"
      > </a
      ><a name="11210" href="StlcProp.html#11186" class="Bound"
      >x&#8712;t&#8323;</a
      ><a name="11214"
      >
</a
      ><a name="11215" href="StlcProp.html#10742" class="Function"
      >&#8709;&#8866;-closed&#8242;</a
      ><a name="11225"
      > </a
      ><a name="11226" class="Symbol"
      >(</a
      ><a name="11227" href="Stlc.html#19256" class="InductiveConstructor"
      >abs</a
      ><a name="11230"
      > </a
      ><a name="11231" class="Symbol"
      >{</a
      ><a name="11232" class="Argument"
      >x</a
      ><a name="11233"
      > </a
      ><a name="11234" class="Symbol"
      >=</a
      ><a name="11235"
      > </a
      ><a name="11236" href="StlcProp.html#11236" class="Bound"
      >x</a
      ><a name="11237" class="Symbol"
      >}</a
      ><a name="11238"
      > </a
      ><a name="11239" href="StlcProp.html#11239" class="Bound"
      >t&#8242;&#8758;A</a
      ><a name="11243" class="Symbol"
      >)</a
      ><a name="11244"
      > </a
      ><a name="11249" class="Symbol"
      >(</a
      ><a name="11250" href="StlcProp.html#6985" class="InductiveConstructor"
      >abs</a
      ><a name="11253"
      > </a
      ><a name="11254" href="StlcProp.html#11254" class="Bound"
      >x&#8800;y</a
      ><a name="11257"
      > </a
      ><a name="11258" href="StlcProp.html#11258" class="Bound"
      >y&#8712;t&#8242;</a
      ><a name="11262" class="Symbol"
      >)</a
      ><a name="11263"
      > </a
      ><a name="11264" class="Keyword"
      >with</a
      ><a name="11268"
      > </a
      ><a name="11269" href="StlcProp.html#8237" class="Function"
      >freeInCtxt</a
      ><a name="11279"
      > </a
      ><a name="11280" href="StlcProp.html#11258" class="Bound"
      >y&#8712;t&#8242;</a
      ><a name="11284"
      > </a
      ><a name="11285" href="StlcProp.html#11239" class="Bound"
      >t&#8242;&#8758;A</a
      ><a name="11289"
      >
</a
      ><a name="11290" href="StlcProp.html#10742" class="Function"
      >&#8709;&#8866;-closed&#8242;</a
      ><a name="11300"
      > </a
      ><a name="11301" class="Symbol"
      >(</a
      ><a name="11302" class="InductiveConstructor"
      >abs</a
      ><a name="11305"
      > </a
      ><a name="11306" class="Symbol"
      >{</a
      ><a name="11307" class="Argument"
      >x</a
      ><a name="11308"
      > </a
      ><a name="11309" class="Symbol"
      >=</a
      ><a name="11310"
      > </a
      ><a name="11311" href="StlcProp.html#11311" class="Bound"
      >x</a
      ><a name="11312" class="Symbol"
      >}</a
      ><a name="11313"
      > </a
      ><a name="11314" href="StlcProp.html#11314" class="Bound"
      >t&#8242;&#8758;A</a
      ><a name="11318" class="Symbol"
      >)</a
      ><a name="11319"
      > </a
      ><a name="11324" class="Symbol"
      >(</a
      ><a name="11325" class="InductiveConstructor"
      >abs</a
      ><a name="11328"
      > </a
      ><a name="11329" href="StlcProp.html#11329" class="Bound"
      >x&#8800;y</a
      ><a name="11332"
      > </a
      ><a name="11333" href="StlcProp.html#11333" class="Bound"
      >y&#8712;t&#8242;</a
      ><a name="11337" class="Symbol"
      >)</a
      ><a name="11338"
      > </a
      ><a name="11339" class="Symbol"
      >|</a
      ><a name="11340"
      > </a
      ><a name="11341" href="StlcProp.html#11341" class="Bound"
      >A</a
      ><a name="11342"
      > </a
      ><a name="11343" href="https://agda.github.io/agda-stdlib/Data.Product.html#509" class="InductiveConstructor Operator"
      >,</a
      ><a name="11344"
      > </a
      ><a name="11345" href="StlcProp.html#11345" class="Bound"
      >y&#8758;A</a
      ><a name="11348"
      > </a
      ><a name="11349" class="Keyword"
      >with</a
      ><a name="11353"
      > </a
      ><a name="11354" href="StlcProp.html#11311" class="Bound"
      >x</a
      ><a name="11355"
      > </a
      ><a name="11356" href="Maps.html#2329" class="Function Operator"
      >&#8799;</a
      ><a name="11357"
      > </a
      ><a name="11358" href="StlcProp.html#11321" class="Bound"
      >y</a
      ><a name="11359"
      >
</a
      ><a name="11360" href="StlcProp.html#10742" class="Function"
      >&#8709;&#8866;-closed&#8242;</a
      ><a name="11370"
      > </a
      ><a name="11371" class="Symbol"
      >(</a
      ><a name="11372" class="InductiveConstructor"
      >abs</a
      ><a name="11375"
      > </a
      ><a name="11376" class="Symbol"
      >{</a
      ><a name="11377" class="Argument"
      >x</a
      ><a name="11378"
      > </a
      ><a name="11379" class="Symbol"
      >=</a
      ><a name="11380"
      > </a
      ><a name="11381" href="StlcProp.html#11381" class="Bound"
      >x</a
      ><a name="11382" class="Symbol"
      >}</a
      ><a name="11383"
      > </a
      ><a name="11384" href="StlcProp.html#11384" class="Bound"
      >t&#8242;&#8758;A</a
      ><a name="11388" class="Symbol"
      >)</a
      ><a name="11389"
      > </a
      ><a name="11394" class="Symbol"
      >(</a
      ><a name="11395" class="InductiveConstructor"
      >abs</a
      ><a name="11398"
      > </a
      ><a name="11399" href="StlcProp.html#11399" class="Bound"
      >x&#8800;y</a
      ><a name="11402"
      > </a
      ><a name="11403" href="StlcProp.html#11403" class="Bound"
      >y&#8712;t&#8242;</a
      ><a name="11407" class="Symbol"
      >)</a
      ><a name="11408"
      > </a
      ><a name="11409" class="Symbol"
      >|</a
      ><a name="11410"
      > </a
      ><a name="11411" href="StlcProp.html#11411" class="Bound"
      >A</a
      ><a name="11412"
      > </a
      ><a name="11413" href="https://agda.github.io/agda-stdlib/Data.Product.html#509" class="InductiveConstructor Operator"
      >,</a
      ><a name="11414"
      > </a
      ><a name="11415" href="StlcProp.html#11415" class="Bound"
      >y&#8758;A</a
      ><a name="11418"
      > </a
      ><a name="11419" class="Symbol"
      >|</a
      ><a name="11420"
      > </a
      ><a name="11421" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#520" class="InductiveConstructor"
      >yes</a
      ><a name="11424"
      > </a
      ><a name="11425" href="StlcProp.html#11425" class="Bound"
      >x=y</a
      ><a name="11428"
      > </a
      ><a name="11429" class="Symbol"
      >=</a
      ><a name="11430"
      > </a
      ><a name="11431" href="StlcProp.html#11399" class="Bound"
      >x&#8800;y</a
      ><a name="11434"
      > </a
      ><a name="11435" href="StlcProp.html#11425" class="Bound"
      >x=y</a
      ><a name="11438"
      >
</a
      ><a name="11439" href="StlcProp.html#10742" class="Function"
      >&#8709;&#8866;-closed&#8242;</a
      ><a name="11449"
      > </a
      ><a name="11450" class="Symbol"
      >(</a
      ><a name="11451" class="InductiveConstructor"
      >abs</a
      ><a name="11454"
      > </a
      ><a name="11455" class="Symbol"
      >{</a
      ><a name="11456" class="Argument"
      >x</a
      ><a name="11457"
      > </a
      ><a name="11458" class="Symbol"
      >=</a
      ><a name="11459"
      > </a
      ><a name="11460" href="StlcProp.html#11460" class="Bound"
      >x</a
      ><a name="11461" class="Symbol"
      >}</a
      ><a name="11462"
      > </a
      ><a name="11463" href="StlcProp.html#11463" class="Bound"
      >t&#8242;&#8758;A</a
      ><a name="11467" class="Symbol"
      >)</a
      ><a name="11468"
      > </a
      ><a name="11473" class="Symbol"
      >(</a
      ><a name="11474" class="InductiveConstructor"
      >abs</a
      ><a name="11477"
      > </a
      ><a name="11478" href="StlcProp.html#11478" class="Bound"
      >x&#8800;y</a
      ><a name="11481"
      > </a
      ><a name="11482" href="StlcProp.html#11482" class="Bound"
      >y&#8712;t&#8242;</a
      ><a name="11486" class="Symbol"
      >)</a
      ><a name="11487"
      > </a
      ><a name="11488" class="Symbol"
      >|</a
      ><a name="11489"
      > </a
      ><a name="11490" href="StlcProp.html#11490" class="Bound"
      >A</a
      ><a name="11491"
      > </a
      ><a name="11492" href="https://agda.github.io/agda-stdlib/Data.Product.html#509" class="InductiveConstructor Operator"
      >,</a
      ><a name="11493"
      > </a
      ><a name="11494" class="Symbol"
      >()</a
      ><a name="11496"
      >  </a
      ><a name="11498" class="Symbol"
      >|</a
      ><a name="11499"
      > </a
      ><a name="11500" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#547" class="InductiveConstructor"
      >no</a
      ><a name="11502"
      >  </a
      ><a name="11504" class="Symbol"
      >_</a
      >
{% endraw %}</pre>
</div>

Sometimes, when we have a proof $$\Gamma\vdash t : A$$, we will need to
replace $$\Gamma$$ by a different context $$\Gamma'$$.  When is it safe
to do this?  Intuitively, it must at least be the case that
$$\Gamma'$$ assigns the same types as $$\Gamma$$ to all the variables
that appear free in $$t$$. In fact, this is the only condition that
is needed.

<pre class="Agda">{% raw %}
<a name="11892" href="StlcProp.html#11892" class="Function"
      >replaceCtxt</a
      ><a name="11903"
      > </a
      ><a name="11904" class="Symbol"
      >:</a
      ><a name="11905"
      > </a
      ><a name="11906" class="Symbol"
      >&#8704;</a
      ><a name="11907"
      > </a
      ><a name="11931" class="Symbol"
      >&#8594;</a
      ><a name="11932"
      > </a
      ><a name="11933" class="Symbol"
      >(&#8704;</a
      ><a name="11935"
      > </a
      ><a name="11940" class="Symbol"
      >&#8594;</a
      ><a name="11941"
      > </a
      ><a name="11942" href="StlcProp.html#11937" class="Bound"
      >x</a
      ><a name="11943"
      > </a
      ><a name="11944" href="StlcProp.html#6922" class="Datatype Operator"
      >FreeIn</a
      ><a name="11950"
      > </a
      ><a name="11951" href="StlcProp.html#11914" class="Bound"
      >t</a
      ><a name="11952"
      > </a
      ><a name="11953" class="Symbol"
      >&#8594;</a
      ><a name="11954"
      > </a
      ><a name="11955" href="StlcProp.html#11909" class="Bound"
      >&#915;</a
      ><a name="11956"
      > </a
      ><a name="11957" href="StlcProp.html#11937" class="Bound"
      >x</a
      ><a name="11958"
      > </a
      ><a name="11959" href="Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="11960"
      > </a
      ><a name="11961" href="StlcProp.html#11911" class="Bound"
      >&#915;&#8242;</a
      ><a name="11963"
      > </a
      ><a name="11964" href="StlcProp.html#11937" class="Bound"
      >x</a
      ><a name="11965" class="Symbol"
      >)</a
      ><a name="11966"
      >
            </a
      ><a name="11979" class="Symbol"
      >&#8594;</a
      ><a name="11980"
      > </a
      ><a name="11981" href="StlcProp.html#11909" class="Bound"
      >&#915;</a
      ><a name="11982"
      >  </a
      ><a name="11984" href="Stlc.html#19119" class="Datatype Operator"
      >&#8866;</a
      ><a name="11985"
      > </a
      ><a name="11986" href="StlcProp.html#11914" class="Bound"
      >t</a
      ><a name="11987"
      > </a
      ><a name="11988" href="Stlc.html#19119" class="Datatype Operator"
      >&#8758;</a
      ><a name="11989"
      > </a
      ><a name="11990" href="StlcProp.html#11916" class="Bound"
      >A</a
      ><a name="11991"
      >
            </a
      ><a name="12004" class="Symbol"
      >&#8594;</a
      ><a name="12005"
      > </a
      ><a name="12006" href="StlcProp.html#11911" class="Bound"
      >&#915;&#8242;</a
      ><a name="12008"
      > </a
      ><a name="12009" href="Stlc.html#19119" class="Datatype Operator"
      >&#8866;</a
      ><a name="12010"
      > </a
      ><a name="12011" href="StlcProp.html#11914" class="Bound"
      >t</a
      ><a name="12012"
      > </a
      ><a name="12013" href="Stlc.html#19119" class="Datatype Operator"
      >&#8758;</a
      ><a name="12014"
      > </a
      ><a name="12015" href="StlcProp.html#11916" class="Bound"
      >A</a
      >
{% endraw %}</pre>

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

<pre class="Agda">{% raw %}
<a name="14320" href="StlcProp.html#11892" class="Function"
      >replaceCtxt</a
      ><a name="14331"
      > </a
      ><a name="14332" href="StlcProp.html#14332" class="Bound"
      >f</a
      ><a name="14333"
      > </a
      ><a name="14334" class="Symbol"
      >(</a
      ><a name="14335" href="Stlc.html#19163" class="InductiveConstructor"
      >var</a
      ><a name="14338"
      > </a
      ><a name="14339" href="StlcProp.html#14339" class="Bound"
      >x</a
      ><a name="14340"
      > </a
      ><a name="14341" href="StlcProp.html#14341" class="Bound"
      >x&#8758;A</a
      ><a name="14344" class="Symbol"
      >)</a
      ><a name="14345"
      > </a
      ><a name="14346" class="Keyword"
      >rewrite</a
      ><a name="14353"
      > </a
      ><a name="14354" href="StlcProp.html#14332" class="Bound"
      >f</a
      ><a name="14355"
      > </a
      ><a name="14356" href="StlcProp.html#6961" class="InductiveConstructor"
      >var</a
      ><a name="14359"
      > </a
      ><a name="14360" class="Symbol"
      >=</a
      ><a name="14361"
      > </a
      ><a name="14362" href="Stlc.html#19163" class="InductiveConstructor"
      >var</a
      ><a name="14365"
      > </a
      ><a name="14366" href="StlcProp.html#14339" class="Bound"
      >x</a
      ><a name="14367"
      > </a
      ><a name="14368" href="StlcProp.html#14341" class="Bound"
      >x&#8758;A</a
      ><a name="14371"
      >
</a
      ><a name="14372" href="StlcProp.html#11892" class="Function"
      >replaceCtxt</a
      ><a name="14383"
      > </a
      ><a name="14384" href="StlcProp.html#14384" class="Bound"
      >f</a
      ><a name="14385"
      > </a
      ><a name="14386" class="Symbol"
      >(</a
      ><a name="14387" href="Stlc.html#19372" class="InductiveConstructor"
      >app</a
      ><a name="14390"
      > </a
      ><a name="14391" href="StlcProp.html#14391" class="Bound"
      >t&#8321;&#8758;A&#8658;B</a
      ><a name="14397"
      > </a
      ><a name="14398" href="StlcProp.html#14398" class="Bound"
      >t&#8322;&#8758;A</a
      ><a name="14402" class="Symbol"
      >)</a
      ><a name="14403"
      >
  </a
      ><a name="14406" class="Symbol"
      >=</a
      ><a name="14407"
      > </a
      ><a name="14408" href="Stlc.html#19372" class="InductiveConstructor"
      >app</a
      ><a name="14411"
      > </a
      ><a name="14412" class="Symbol"
      >(</a
      ><a name="14413" href="StlcProp.html#11892" class="Function"
      >replaceCtxt</a
      ><a name="14424"
      > </a
      ><a name="14425" class="Symbol"
      >(</a
      ><a name="14426" href="StlcProp.html#14384" class="Bound"
      >f</a
      ><a name="14427"
      > </a
      ><a name="14428" href="https://agda.github.io/agda-stdlib/Function.html#713" class="Function Operator"
      >&#8728;</a
      ><a name="14429"
      > </a
      ><a name="14430" href="StlcProp.html#7046" class="InductiveConstructor"
      >app1</a
      ><a name="14434" class="Symbol"
      >)</a
      ><a name="14435"
      > </a
      ><a name="14436" href="StlcProp.html#14391" class="Bound"
      >t&#8321;&#8758;A&#8658;B</a
      ><a name="14442" class="Symbol"
      >)</a
      ><a name="14443"
      > </a
      ><a name="14444" class="Symbol"
      >(</a
      ><a name="14445" href="StlcProp.html#11892" class="Function"
      >replaceCtxt</a
      ><a name="14456"
      > </a
      ><a name="14457" class="Symbol"
      >(</a
      ><a name="14458" href="StlcProp.html#14384" class="Bound"
      >f</a
      ><a name="14459"
      > </a
      ><a name="14460" href="https://agda.github.io/agda-stdlib/Function.html#713" class="Function Operator"
      >&#8728;</a
      ><a name="14461"
      > </a
      ><a name="14462" href="StlcProp.html#7100" class="InductiveConstructor"
      >app2</a
      ><a name="14466" class="Symbol"
      >)</a
      ><a name="14467"
      > </a
      ><a name="14468" href="StlcProp.html#14398" class="Bound"
      >t&#8322;&#8758;A</a
      ><a name="14472" class="Symbol"
      >)</a
      ><a name="14473"
      >
</a
      ><a name="14474" href="StlcProp.html#11892" class="Function"
      >replaceCtxt</a
      ><a name="14485"
      > </a
      ><a name="14495" href="StlcProp.html#14495" class="Bound"
      >f</a
      ><a name="14496"
      > </a
      ><a name="14497" class="Symbol"
      >(</a
      ><a name="14498" href="Stlc.html#19256" class="InductiveConstructor"
      >abs</a
      ><a name="14501"
      > </a
      ><a name="14524" href="StlcProp.html#14524" class="Bound"
      >t&#8242;&#8758;B</a
      ><a name="14528" class="Symbol"
      >)</a
      ><a name="14529"
      >
  </a
      ><a name="14532" class="Symbol"
      >=</a
      ><a name="14533"
      > </a
      ><a name="14534" href="Stlc.html#19256" class="InductiveConstructor"
      >abs</a
      ><a name="14537"
      > </a
      ><a name="14538" class="Symbol"
      >(</a
      ><a name="14539" href="StlcProp.html#11892" class="Function"
      >replaceCtxt</a
      ><a name="14550"
      > </a
      ><a name="14551" href="StlcProp.html#14572" class="Function"
      >f&#8242;</a
      ><a name="14553"
      > </a
      ><a name="14554" href="StlcProp.html#14524" class="Bound"
      >t&#8242;&#8758;B</a
      ><a name="14558" class="Symbol"
      >)</a
      ><a name="14559"
      >
  </a
      ><a name="14562" class="Keyword"
      >where</a
      ><a name="14567"
      >
    </a
      ><a name="14572" href="StlcProp.html#14572" class="Function"
      >f&#8242;</a
      ><a name="14574"
      > </a
      ><a name="14575" class="Symbol"
      >:</a
      ><a name="14576"
      > </a
      ><a name="14577" class="Symbol"
      >&#8704;</a
      ><a name="14578"
      > </a
      ><a name="14583" class="Symbol"
      >&#8594;</a
      ><a name="14584"
      > </a
      ><a name="14585" href="StlcProp.html#14580" class="Bound"
      >y</a
      ><a name="14586"
      > </a
      ><a name="14587" href="StlcProp.html#6922" class="Datatype Operator"
      >FreeIn</a
      ><a name="14593"
      > </a
      ><a name="14594" href="StlcProp.html#14520" class="Bound"
      >t&#8242;</a
      ><a name="14596"
      > </a
      ><a name="14597" class="Symbol"
      >&#8594;</a
      ><a name="14598"
      > </a
      ><a name="14599" class="Symbol"
      >(</a
      ><a name="14600" href="StlcProp.html#14487" class="Bound"
      >&#915;</a
      ><a name="14601"
      > </a
      ><a name="14602" href="Stlc.html#18218" class="Function Operator"
      >,</a
      ><a name="14603"
      > </a
      ><a name="14604" href="StlcProp.html#14508" class="Bound"
      >x</a
      ><a name="14605"
      > </a
      ><a name="14606" href="Stlc.html#18218" class="Function Operator"
      >&#8758;</a
      ><a name="14607"
      > </a
      ><a name="14608" href="StlcProp.html#14512" class="Bound"
      >A</a
      ><a name="14609" class="Symbol"
      >)</a
      ><a name="14610"
      > </a
      ><a name="14611" href="StlcProp.html#14580" class="Bound"
      >y</a
      ><a name="14612"
      > </a
      ><a name="14613" href="Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="14614"
      > </a
      ><a name="14615" class="Symbol"
      >(</a
      ><a name="14616" href="StlcProp.html#14491" class="Bound"
      >&#915;&#8242;</a
      ><a name="14618"
      > </a
      ><a name="14619" href="Stlc.html#18218" class="Function Operator"
      >,</a
      ><a name="14620"
      > </a
      ><a name="14621" href="StlcProp.html#14508" class="Bound"
      >x</a
      ><a name="14622"
      > </a
      ><a name="14623" href="Stlc.html#18218" class="Function Operator"
      >&#8758;</a
      ><a name="14624"
      > </a
      ><a name="14625" href="StlcProp.html#14512" class="Bound"
      >A</a
      ><a name="14626" class="Symbol"
      >)</a
      ><a name="14627"
      > </a
      ><a name="14628" href="StlcProp.html#14580" class="Bound"
      >y</a
      ><a name="14629"
      >
    </a
      ><a name="14634" href="StlcProp.html#14572" class="Function"
      >f&#8242;</a
      ><a name="14636"
      > </a
      ><a name="14641" href="StlcProp.html#14641" class="Bound"
      >y&#8712;t&#8242;</a
      ><a name="14645"
      > </a
      ><a name="14646" class="Keyword"
      >with</a
      ><a name="14650"
      > </a
      ><a name="14651" href="StlcProp.html#14508" class="Bound"
      >x</a
      ><a name="14652"
      > </a
      ><a name="14653" href="Maps.html#2329" class="Function Operator"
      >&#8799;</a
      ><a name="14654"
      > </a
      ><a name="14655" href="StlcProp.html#14638" class="Bound"
      >y</a
      ><a name="14656"
      >
    </a
      ><a name="14661" class="Symbol"
      >...</a
      ><a name="14664"
      > </a
      ><a name="14665" class="Symbol"
      >|</a
      ><a name="14666"
      > </a
      ><a name="14667" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#520" class="InductiveConstructor"
      >yes</a
      ><a name="14670"
      > </a
      ><a name="14671" class="Symbol"
      >_</a
      ><a name="14672"
      >   </a
      ><a name="14675" class="Symbol"
      >=</a
      ><a name="14676"
      > </a
      ><a name="14677" href="Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="14681"
      >
    </a
      ><a name="14686" class="Symbol"
      >...</a
      ><a name="14689"
      > </a
      ><a name="14690" class="Symbol"
      >|</a
      ><a name="14691"
      > </a
      ><a name="14692" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#547" class="InductiveConstructor"
      >no</a
      ><a name="14694"
      >  </a
      ><a name="14696" href="StlcProp.html#14696" class="Bound"
      >x&#8800;y</a
      ><a name="14699"
      > </a
      ><a name="14700" class="Symbol"
      >=</a
      ><a name="14701"
      > </a
      ><a name="14702" href="StlcProp.html#14495" class="Bound"
      >f</a
      ><a name="14703"
      > </a
      ><a name="14704" class="Symbol"
      >(</a
      ><a name="14705" href="StlcProp.html#6985" class="InductiveConstructor"
      >abs</a
      ><a name="14708"
      > </a
      ><a name="14709" href="StlcProp.html#14696" class="Bound"
      >x&#8800;y</a
      ><a name="14712"
      > </a
      ><a name="14713" href="StlcProp.html#14641" class="Bound"
      >y&#8712;t&#8242;</a
      ><a name="14717" class="Symbol"
      >)</a
      ><a name="14718"
      >
</a
      ><a name="14719" href="StlcProp.html#11892" class="Function"
      >replaceCtxt</a
      ><a name="14730"
      > </a
      ><a name="14731" class="Symbol"
      >_</a
      ><a name="14732"
      > </a
      ><a name="14733" href="Stlc.html#19506" class="InductiveConstructor"
      >true</a
      ><a name="14737"
      >  </a
      ><a name="14739" class="Symbol"
      >=</a
      ><a name="14740"
      > </a
      ><a name="14741" href="Stlc.html#19506" class="InductiveConstructor"
      >true</a
      ><a name="14745"
      >
</a
      ><a name="14746" href="StlcProp.html#11892" class="Function"
      >replaceCtxt</a
      ><a name="14757"
      > </a
      ><a name="14758" class="Symbol"
      >_</a
      ><a name="14759"
      > </a
      ><a name="14760" href="Stlc.html#19565" class="InductiveConstructor"
      >false</a
      ><a name="14765"
      > </a
      ><a name="14766" class="Symbol"
      >=</a
      ><a name="14767"
      > </a
      ><a name="14768" href="Stlc.html#19565" class="InductiveConstructor"
      >false</a
      ><a name="14773"
      >
</a
      ><a name="14774" href="StlcProp.html#11892" class="Function"
      >replaceCtxt</a
      ><a name="14785"
      > </a
      ><a name="14786" href="StlcProp.html#14786" class="Bound"
      >f</a
      ><a name="14787"
      > </a
      ><a name="14788" class="Symbol"
      >(</a
      ><a name="14789" href="Stlc.html#19624" class="InductiveConstructor Operator"
      >if</a
      ><a name="14791"
      > </a
      ><a name="14792" href="StlcProp.html#14792" class="Bound"
      >t&#8321;&#8758;bool</a
      ><a name="14799"
      > </a
      ><a name="14800" href="Stlc.html#19624" class="InductiveConstructor Operator"
      >then</a
      ><a name="14804"
      > </a
      ><a name="14805" href="StlcProp.html#14805" class="Bound"
      >t&#8322;&#8758;A</a
      ><a name="14809"
      > </a
      ><a name="14810" href="Stlc.html#19624" class="InductiveConstructor Operator"
      >else</a
      ><a name="14814"
      > </a
      ><a name="14815" href="StlcProp.html#14815" class="Bound"
      >t&#8323;&#8758;A</a
      ><a name="14819" class="Symbol"
      >)</a
      ><a name="14820"
      >
  </a
      ><a name="14823" class="Symbol"
      >=</a
      ><a name="14824"
      > </a
      ><a name="14825" href="Stlc.html#19624" class="InductiveConstructor Operator"
      >if</a
      ><a name="14827"
      >   </a
      ><a name="14830" href="StlcProp.html#11892" class="Function"
      >replaceCtxt</a
      ><a name="14841"
      > </a
      ><a name="14842" class="Symbol"
      >(</a
      ><a name="14843" href="StlcProp.html#14786" class="Bound"
      >f</a
      ><a name="14844"
      > </a
      ><a name="14845" href="https://agda.github.io/agda-stdlib/Function.html#713" class="Function Operator"
      >&#8728;</a
      ><a name="14846"
      > </a
      ><a name="14847" href="StlcProp.html#7154" class="InductiveConstructor"
      >if1</a
      ><a name="14850" class="Symbol"
      >)</a
      ><a name="14851"
      > </a
      ><a name="14852" href="StlcProp.html#14792" class="Bound"
      >t&#8321;&#8758;bool</a
      ><a name="14859"
      >
    </a
      ><a name="14864" href="Stlc.html#19624" class="InductiveConstructor Operator"
      >then</a
      ><a name="14868"
      > </a
      ><a name="14869" href="StlcProp.html#11892" class="Function"
      >replaceCtxt</a
      ><a name="14880"
      > </a
      ><a name="14881" class="Symbol"
      >(</a
      ><a name="14882" href="StlcProp.html#14786" class="Bound"
      >f</a
      ><a name="14883"
      > </a
      ><a name="14884" href="https://agda.github.io/agda-stdlib/Function.html#713" class="Function Operator"
      >&#8728;</a
      ><a name="14885"
      > </a
      ><a name="14886" href="StlcProp.html#7225" class="InductiveConstructor"
      >if2</a
      ><a name="14889" class="Symbol"
      >)</a
      ><a name="14890"
      > </a
      ><a name="14891" href="StlcProp.html#14805" class="Bound"
      >t&#8322;&#8758;A</a
      ><a name="14895"
      >
    </a
      ><a name="14900" href="Stlc.html#19624" class="InductiveConstructor Operator"
      >else</a
      ><a name="14904"
      > </a
      ><a name="14905" href="StlcProp.html#11892" class="Function"
      >replaceCtxt</a
      ><a name="14916"
      > </a
      ><a name="14917" class="Symbol"
      >(</a
      ><a name="14918" href="StlcProp.html#14786" class="Bound"
      >f</a
      ><a name="14919"
      > </a
      ><a name="14920" href="https://agda.github.io/agda-stdlib/Function.html#713" class="Function Operator"
      >&#8728;</a
      ><a name="14921"
      > </a
      ><a name="14922" href="StlcProp.html#7296" class="InductiveConstructor"
      >if3</a
      ><a name="14925" class="Symbol"
      >)</a
      ><a name="14926"
      > </a
      ><a name="14927" href="StlcProp.html#14815" class="Bound"
      >t&#8323;&#8758;A</a
      >
{% endraw %}</pre>

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

<pre class="Agda">{% raw %}
<a name="15742" href="StlcProp.html#15742" class="Function"
      >[:=]-preserves-&#8866;</a
      ><a name="15758"
      > </a
      ><a name="15759" class="Symbol"
      >:</a
      ><a name="15760"
      > </a
      ><a name="15761" class="Symbol"
      >&#8704;</a
      ><a name="15762"
      > </a
      ><a name="15794" class="Symbol"
      >&#8594;</a
      ><a name="15795"
      > </a
      ><a name="15796" href="Stlc.html#18187" class="Function"
      >&#8709;</a
      ><a name="15797"
      > </a
      ><a name="15798" href="Stlc.html#19119" class="Datatype Operator"
      >&#8866;</a
      ><a name="15799"
      > </a
      ><a name="15800" href="StlcProp.html#15772" class="Bound"
      >v</a
      ><a name="15801"
      > </a
      ><a name="15802" href="Stlc.html#19119" class="Datatype Operator"
      >&#8758;</a
      ><a name="15803"
      > </a
      ><a name="15804" href="StlcProp.html#15768" class="Bound"
      >A</a
      ><a name="15805"
      >
                 </a
      ><a name="15823" class="Symbol"
      >&#8594;</a
      ><a name="15824"
      > </a
      ><a name="15825" href="StlcProp.html#15764" class="Bound"
      >&#915;</a
      ><a name="15826"
      > </a
      ><a name="15827" href="Stlc.html#18218" class="Function Operator"
      >,</a
      ><a name="15828"
      > </a
      ><a name="15829" href="StlcProp.html#15766" class="Bound"
      >x</a
      ><a name="15830"
      > </a
      ><a name="15831" href="Stlc.html#18218" class="Function Operator"
      >&#8758;</a
      ><a name="15832"
      > </a
      ><a name="15833" href="StlcProp.html#15768" class="Bound"
      >A</a
      ><a name="15834"
      > </a
      ><a name="15835" href="Stlc.html#19119" class="Datatype Operator"
      >&#8866;</a
      ><a name="15836"
      > </a
      ><a name="15837" href="StlcProp.html#15770" class="Bound"
      >t</a
      ><a name="15838"
      > </a
      ><a name="15839" href="Stlc.html#19119" class="Datatype Operator"
      >&#8758;</a
      ><a name="15840"
      > </a
      ><a name="15841" href="StlcProp.html#15774" class="Bound"
      >B</a
      ><a name="15842"
      >
                 </a
      ><a name="15860" class="Symbol"
      >&#8594;</a
      ><a name="15861"
      > </a
      ><a name="15862" href="StlcProp.html#15764" class="Bound"
      >&#915;</a
      ><a name="15863"
      > </a
      ><a name="15864" href="Stlc.html#18218" class="Function Operator"
      >,</a
      ><a name="15865"
      > </a
      ><a name="15866" href="StlcProp.html#15766" class="Bound"
      >x</a
      ><a name="15867"
      > </a
      ><a name="15868" href="Stlc.html#18218" class="Function Operator"
      >&#8758;</a
      ><a name="15869"
      > </a
      ><a name="15870" href="StlcProp.html#15768" class="Bound"
      >A</a
      ><a name="15871"
      > </a
      ><a name="15872" href="Stlc.html#19119" class="Datatype Operator"
      >&#8866;</a
      ><a name="15873"
      > </a
      ><a name="15874" href="Stlc.html#12189" class="Function Operator"
      >[</a
      ><a name="15875"
      > </a
      ><a name="15876" href="StlcProp.html#15766" class="Bound"
      >x</a
      ><a name="15877"
      > </a
      ><a name="15878" href="Stlc.html#12189" class="Function Operator"
      >:=</a
      ><a name="15880"
      > </a
      ><a name="15881" href="StlcProp.html#15772" class="Bound"
      >v</a
      ><a name="15882"
      > </a
      ><a name="15883" href="Stlc.html#12189" class="Function Operator"
      >]</a
      ><a name="15884"
      > </a
      ><a name="15885" href="StlcProp.html#15770" class="Bound"
      >t</a
      ><a name="15886"
      > </a
      ><a name="15887" href="Stlc.html#19119" class="Datatype Operator"
      >&#8758;</a
      ><a name="15888"
      > </a
      ><a name="15889" href="StlcProp.html#15774" class="Bound"
      >B</a
      >
{% endraw %}</pre>

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

<pre class="Agda">{% raw %}
<a name="19800" href="StlcProp.html#15742" class="Function"
      >[:=]-preserves-&#8866;</a
      ><a name="19816"
      > </a
      ><a name="19825" href="StlcProp.html#19825" class="Bound"
      >v&#8758;A</a
      ><a name="19828"
      > </a
      ><a name="19829" class="Symbol"
      >(</a
      ><a name="19830" href="Stlc.html#19163" class="InductiveConstructor"
      >var</a
      ><a name="19833"
      > </a
      ><a name="19834" href="StlcProp.html#19834" class="Bound"
      >y</a
      ><a name="19835"
      > </a
      ><a name="19836" href="StlcProp.html#19836" class="Bound"
      >y&#8712;&#915;</a
      ><a name="19839" class="Symbol"
      >)</a
      ><a name="19840"
      > </a
      ><a name="19841" class="Keyword"
      >with</a
      ><a name="19845"
      > </a
      ><a name="19846" href="StlcProp.html#19822" class="Bound"
      >x</a
      ><a name="19847"
      > </a
      ><a name="19848" href="Maps.html#2329" class="Function Operator"
      >&#8799;</a
      ><a name="19849"
      > </a
      ><a name="19850" href="StlcProp.html#19834" class="Bound"
      >y</a
      ><a name="19851"
      >
</a
      ><a name="19852" class="Symbol"
      >...</a
      ><a name="19855"
      > </a
      ><a name="19856" class="Symbol"
      >|</a
      ><a name="19857"
      > </a
      ><a name="19858" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#520" class="InductiveConstructor"
      >yes</a
      ><a name="19861"
      > </a
      ><a name="19862" href="StlcProp.html#19862" class="Bound"
      >x=y</a
      ><a name="19865"
      > </a
      ><a name="19866" class="Symbol"
      >=</a
      ><a name="19867"
      > </a
      ><a name="19868" class="Symbol"
      >{!!}</a
      ><a name="19872"
      >
</a
      ><a name="19873" class="Symbol"
      >...</a
      ><a name="19876"
      > </a
      ><a name="19877" class="Symbol"
      >|</a
      ><a name="19878"
      > </a
      ><a name="19879" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#547" class="InductiveConstructor"
      >no</a
      ><a name="19881"
      >  </a
      ><a name="19883" href="StlcProp.html#19883" class="Bound"
      >x&#8800;y</a
      ><a name="19886"
      > </a
      ><a name="19887" class="Symbol"
      >=</a
      ><a name="19888"
      > </a
      ><a name="19889" class="Symbol"
      >{!!}</a
      ><a name="19893"
      >
</a
      ><a name="19894" href="StlcProp.html#15742" class="Function"
      >[:=]-preserves-&#8866;</a
      ><a name="19910"
      > </a
      ><a name="19911" href="StlcProp.html#19911" class="Bound"
      >v&#8758;A</a
      ><a name="19914"
      > </a
      ><a name="19915" class="Symbol"
      >(</a
      ><a name="19916" href="Stlc.html#19256" class="InductiveConstructor"
      >abs</a
      ><a name="19919"
      > </a
      ><a name="19920" href="StlcProp.html#19920" class="Bound"
      >t&#8242;&#8758;B</a
      ><a name="19924" class="Symbol"
      >)</a
      ><a name="19925"
      > </a
      ><a name="19926" class="Symbol"
      >=</a
      ><a name="19927"
      > </a
      ><a name="19928" class="Symbol"
      >{!!}</a
      ><a name="19932"
      >
</a
      ><a name="19933" href="StlcProp.html#15742" class="Function"
      >[:=]-preserves-&#8866;</a
      ><a name="19949"
      > </a
      ><a name="19950" href="StlcProp.html#19950" class="Bound"
      >v&#8758;A</a
      ><a name="19953"
      > </a
      ><a name="19954" class="Symbol"
      >(</a
      ><a name="19955" href="Stlc.html#19372" class="InductiveConstructor"
      >app</a
      ><a name="19958"
      > </a
      ><a name="19959" href="StlcProp.html#19959" class="Bound"
      >t&#8321;&#8758;A&#8658;B</a
      ><a name="19965"
      > </a
      ><a name="19966" href="StlcProp.html#19966" class="Bound"
      >t&#8322;&#8758;A</a
      ><a name="19970" class="Symbol"
      >)</a
      ><a name="19971"
      > </a
      ><a name="19972" class="Symbol"
      >=</a
      ><a name="19973"
      >
  </a
      ><a name="19976" href="Stlc.html#19372" class="InductiveConstructor"
      >app</a
      ><a name="19979"
      > </a
      ><a name="19980" class="Symbol"
      >(</a
      ><a name="19981" href="StlcProp.html#15742" class="Function"
      >[:=]-preserves-&#8866;</a
      ><a name="19997"
      > </a
      ><a name="19998" href="StlcProp.html#19950" class="Bound"
      >v&#8758;A</a
      ><a name="20001"
      > </a
      ><a name="20002" href="StlcProp.html#19959" class="Bound"
      >t&#8321;&#8758;A&#8658;B</a
      ><a name="20008" class="Symbol"
      >)</a
      ><a name="20009"
      > </a
      ><a name="20010" class="Symbol"
      >(</a
      ><a name="20011" href="StlcProp.html#15742" class="Function"
      >[:=]-preserves-&#8866;</a
      ><a name="20027"
      > </a
      ><a name="20028" href="StlcProp.html#19950" class="Bound"
      >v&#8758;A</a
      ><a name="20031"
      > </a
      ><a name="20032" href="StlcProp.html#19966" class="Bound"
      >t&#8322;&#8758;A</a
      ><a name="20036" class="Symbol"
      >)</a
      ><a name="20037"
      >
</a
      ><a name="20038" href="StlcProp.html#15742" class="Function"
      >[:=]-preserves-&#8866;</a
      ><a name="20054"
      > </a
      ><a name="20055" href="StlcProp.html#20055" class="Bound"
      >v&#8758;A</a
      ><a name="20058"
      > </a
      ><a name="20059" href="Stlc.html#19506" class="InductiveConstructor"
      >true</a
      ><a name="20063"
      >  </a
      ><a name="20065" class="Symbol"
      >=</a
      ><a name="20066"
      > </a
      ><a name="20067" href="Stlc.html#19506" class="InductiveConstructor"
      >true</a
      ><a name="20071"
      >
</a
      ><a name="20072" href="StlcProp.html#15742" class="Function"
      >[:=]-preserves-&#8866;</a
      ><a name="20088"
      > </a
      ><a name="20089" href="StlcProp.html#20089" class="Bound"
      >v&#8758;A</a
      ><a name="20092"
      > </a
      ><a name="20093" href="Stlc.html#19565" class="InductiveConstructor"
      >false</a
      ><a name="20098"
      > </a
      ><a name="20099" class="Symbol"
      >=</a
      ><a name="20100"
      > </a
      ><a name="20101" href="Stlc.html#19565" class="InductiveConstructor"
      >false</a
      ><a name="20106"
      >
</a
      ><a name="20107" href="StlcProp.html#15742" class="Function"
      >[:=]-preserves-&#8866;</a
      ><a name="20123"
      > </a
      ><a name="20124" href="StlcProp.html#20124" class="Bound"
      >v&#8758;A</a
      ><a name="20127"
      > </a
      ><a name="20128" class="Symbol"
      >(</a
      ><a name="20129" href="Stlc.html#19624" class="InductiveConstructor Operator"
      >if</a
      ><a name="20131"
      > </a
      ><a name="20132" href="StlcProp.html#20132" class="Bound"
      >t&#8321;&#8758;bool</a
      ><a name="20139"
      > </a
      ><a name="20140" href="Stlc.html#19624" class="InductiveConstructor Operator"
      >then</a
      ><a name="20144"
      > </a
      ><a name="20145" href="StlcProp.html#20145" class="Bound"
      >t&#8322;&#8758;B</a
      ><a name="20149"
      > </a
      ><a name="20150" href="Stlc.html#19624" class="InductiveConstructor Operator"
      >else</a
      ><a name="20154"
      > </a
      ><a name="20155" href="StlcProp.html#20155" class="Bound"
      >t&#8323;&#8758;B</a
      ><a name="20159" class="Symbol"
      >)</a
      ><a name="20160"
      > </a
      ><a name="20161" class="Symbol"
      >=</a
      ><a name="20162"
      >
  </a
      ><a name="20165" href="Stlc.html#19624" class="InductiveConstructor Operator"
      >if</a
      ><a name="20167"
      >   </a
      ><a name="20170" href="StlcProp.html#15742" class="Function"
      >[:=]-preserves-&#8866;</a
      ><a name="20186"
      > </a
      ><a name="20187" href="StlcProp.html#20124" class="Bound"
      >v&#8758;A</a
      ><a name="20190"
      > </a
      ><a name="20191" href="StlcProp.html#20132" class="Bound"
      >t&#8321;&#8758;bool</a
      ><a name="20198"
      >
  </a
      ><a name="20201" href="Stlc.html#19624" class="InductiveConstructor Operator"
      >then</a
      ><a name="20205"
      > </a
      ><a name="20206" href="StlcProp.html#15742" class="Function"
      >[:=]-preserves-&#8866;</a
      ><a name="20222"
      > </a
      ><a name="20223" href="StlcProp.html#20124" class="Bound"
      >v&#8758;A</a
      ><a name="20226"
      > </a
      ><a name="20227" href="StlcProp.html#20145" class="Bound"
      >t&#8322;&#8758;B</a
      ><a name="20231"
      >
  </a
      ><a name="20234" href="Stlc.html#19624" class="InductiveConstructor Operator"
      >else</a
      ><a name="20238"
      > </a
      ><a name="20239" href="StlcProp.html#15742" class="Function"
      >[:=]-preserves-&#8866;</a
      ><a name="20255"
      > </a
      ><a name="20256" href="StlcProp.html#20124" class="Bound"
      >v&#8758;A</a
      ><a name="20259"
      > </a
      ><a name="20260" href="StlcProp.html#20155" class="Bound"
      >t&#8323;&#8758;B</a
      >
{% endraw %}</pre>


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
