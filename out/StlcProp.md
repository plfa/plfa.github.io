---
title     : "StlcProp: Properties of STLC"
layout    : page
permalink : /StlcProp
---

<div class="foldable">
<pre class="Agda">{% raw %}
<a name="128" class="Keyword"
      >open</a
      ><a name="132"
      > </a
      ><a name="133" class="Keyword"
      >import</a
      ><a name="139"
      > </a
      ><a name="140" href="https://agda.github.io/agda-stdlib/Function.html#1" class="Module"
      >Function</a
      ><a name="148"
      > </a
      ><a name="149" class="Keyword"
      >using</a
      ><a name="154"
      > </a
      ><a name="155" class="Symbol"
      >(</a
      ><a name="156" href="https://agda.github.io/agda-stdlib/Function.html#713" class="Function Operator"
      >_&#8728;_</a
      ><a name="159" class="Symbol"
      >)</a
      ><a name="160"
      >
</a
      ><a name="161" class="Keyword"
      >open</a
      ><a name="165"
      > </a
      ><a name="166" class="Keyword"
      >import</a
      ><a name="172"
      > </a
      ><a name="173" href="https://agda.github.io/agda-stdlib/Data.Empty.html#1" class="Module"
      >Data.Empty</a
      ><a name="183"
      > </a
      ><a name="184" class="Keyword"
      >using</a
      ><a name="189"
      > </a
      ><a name="190" class="Symbol"
      >(</a
      ><a name="191" href="https://agda.github.io/agda-stdlib/Data.Empty.html#243" class="Datatype"
      >&#8869;</a
      ><a name="192" class="Symbol"
      >;</a
      ><a name="193"
      > </a
      ><a name="194" href="https://agda.github.io/agda-stdlib/Data.Empty.html#348" class="Function"
      >&#8869;-elim</a
      ><a name="200" class="Symbol"
      >)</a
      ><a name="201"
      >
</a
      ><a name="202" class="Keyword"
      >open</a
      ><a name="206"
      > </a
      ><a name="207" class="Keyword"
      >import</a
      ><a name="213"
      > </a
      ><a name="214" href="https://agda.github.io/agda-stdlib/Data.Maybe.html#1" class="Module"
      >Data.Maybe</a
      ><a name="224"
      > </a
      ><a name="225" class="Keyword"
      >using</a
      ><a name="230"
      > </a
      ><a name="231" class="Symbol"
      >(</a
      ><a name="232" href="https://agda.github.io/agda-stdlib/Data.Maybe.Base.html#335" class="Datatype"
      >Maybe</a
      ><a name="237" class="Symbol"
      >;</a
      ><a name="238"
      > </a
      ><a name="239" href="https://agda.github.io/agda-stdlib/Data.Maybe.html#1527" class="InductiveConstructor"
      >just</a
      ><a name="243" class="Symbol"
      >;</a
      ><a name="244"
      > </a
      ><a name="245" href="https://agda.github.io/agda-stdlib/Data.Maybe.html#1588" class="InductiveConstructor"
      >nothing</a
      ><a name="252" class="Symbol"
      >)</a
      ><a name="253"
      >
</a
      ><a name="254" class="Keyword"
      >open</a
      ><a name="258"
      > </a
      ><a name="259" class="Keyword"
      >import</a
      ><a name="265"
      > </a
      ><a name="266" href="https://agda.github.io/agda-stdlib/Data.Product.html#1" class="Module"
      >Data.Product</a
      ><a name="278"
      > </a
      ><a name="279" class="Keyword"
      >using</a
      ><a name="284"
      > </a
      ><a name="285" class="Symbol"
      >(</a
      ><a name="286" href="https://agda.github.io/agda-stdlib/Data.Product.html#823" class="Function"
      >&#8707;</a
      ><a name="287" class="Symbol"
      >;</a
      ><a name="288"
      > </a
      ><a name="289" href="https://agda.github.io/agda-stdlib/Data.Product.html#949" class="Function"
      >&#8707;&#8322;</a
      ><a name="291" class="Symbol"
      >;</a
      ><a name="292"
      > </a
      ><a name="293" href="https://agda.github.io/agda-stdlib/Data.Product.html#509" class="InductiveConstructor Operator"
      >_,_</a
      ><a name="296" class="Symbol"
      >;</a
      ><a name="297"
      > </a
      ><a name="298" href="https://agda.github.io/agda-stdlib/Data.Product.html#1621" class="Function Operator"
      >,_</a
      ><a name="300" class="Symbol"
      >)</a
      ><a name="301"
      >
</a
      ><a name="302" class="Keyword"
      >open</a
      ><a name="306"
      > </a
      ><a name="307" class="Keyword"
      >import</a
      ><a name="313"
      > </a
      ><a name="314" href="https://agda.github.io/agda-stdlib/Data.Sum.html#1" class="Module"
      >Data.Sum</a
      ><a name="322"
      > </a
      ><a name="323" class="Keyword"
      >using</a
      ><a name="328"
      > </a
      ><a name="329" class="Symbol"
      >(</a
      ><a name="330" href="https://agda.github.io/agda-stdlib/Data.Sum.html#433" class="Datatype Operator"
      >_&#8846;_</a
      ><a name="333" class="Symbol"
      >;</a
      ><a name="334"
      > </a
      ><a name="335" href="https://agda.github.io/agda-stdlib/Data.Sum.html#489" class="InductiveConstructor"
      >inj&#8321;</a
      ><a name="339" class="Symbol"
      >;</a
      ><a name="340"
      > </a
      ><a name="341" href="https://agda.github.io/agda-stdlib/Data.Sum.html#514" class="InductiveConstructor"
      >inj&#8322;</a
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
      ><a name="359" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#1" class="Module"
      >Relation.Nullary</a
      ><a name="375"
      > </a
      ><a name="376" class="Keyword"
      >using</a
      ><a name="381"
      > </a
      ><a name="382" class="Symbol"
      >(</a
      ><a name="383" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#414" class="Function Operator"
      >&#172;_</a
      ><a name="385" class="Symbol"
      >;</a
      ><a name="386"
      > </a
      ><a name="387" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#484" class="Datatype"
      >Dec</a
      ><a name="390" class="Symbol"
      >;</a
      ><a name="391"
      > </a
      ><a name="392" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#520" class="InductiveConstructor"
      >yes</a
      ><a name="395" class="Symbol"
      >;</a
      ><a name="396"
      > </a
      ><a name="397" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#547" class="InductiveConstructor"
      >no</a
      ><a name="399" class="Symbol"
      >)</a
      ><a name="400"
      >
</a
      ><a name="401" class="Keyword"
      >open</a
      ><a name="405"
      > </a
      ><a name="406" class="Keyword"
      >import</a
      ><a name="412"
      > </a
      ><a name="413" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#1" class="Module"
      >Relation.Binary.PropositionalEquality</a
      ><a name="450"
      > </a
      ><a name="451" class="Keyword"
      >using</a
      ><a name="456"
      > </a
      ><a name="457" class="Symbol"
      >(</a
      ><a name="458" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >_&#8801;_</a
      ><a name="461" class="Symbol"
      >;</a
      ><a name="462"
      > </a
      ><a name="463" href="https://agda.github.io/agda-stdlib/Relation.Binary.Core.html#4493" class="Function Operator"
      >_&#8802;_</a
      ><a name="466" class="Symbol"
      >;</a
      ><a name="467"
      > </a
      ><a name="468" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="472" class="Symbol"
      >)</a
      ><a name="473"
      >
</a
      ><a name="474" class="Keyword"
      >open</a
      ><a name="478"
      > </a
      ><a name="479" class="Keyword"
      >import</a
      ><a name="485"
      > </a
      ><a name="486" class="Module"
      >Maps</a
      ><a name="490"
      >
</a
      ><a name="491" class="Keyword"
      >open</a
      ><a name="495"
      > </a
      ><a name="496" class="Keyword"
      >import</a
      ><a name="502"
      > </a
      ><a name="503" class="Module"
      >Stlc</a
      >
{% endraw %}</pre>
</div>

In this chapter, we develop the fundamental theory of the Simply
Typed Lambda Calculus---in particular, the type safety
theorem.


## Canonical Forms

As we saw for the simple calculus in the [Stlc]({{ "Stlc" | relative_url }})
chapter, the first step in establishing basic properties of reduction and types
is to identify the possible _canonical forms_ (i.e., well-typed closed values)
belonging to each type.  For $$bool$$, these are the boolean values $$true$$ and
$$false$$.  For arrow types, the canonical forms are lambda-abstractions. 

<pre class="Agda">{% raw %}
<a name="1084" href="StlcProp.html#1084" class="Function"
      >CanonicalForms</a
      ><a name="1098"
      > </a
      ><a name="1099" class="Symbol"
      >:</a
      ><a name="1100"
      > </a
      ><a name="1101" href="Stlc.html#5502" class="Datatype"
      >Term</a
      ><a name="1105"
      > </a
      ><a name="1106" class="Symbol"
      >&#8594;</a
      ><a name="1107"
      > </a
      ><a name="1108" href="Stlc.html#5387" class="Datatype"
      >Type</a
      ><a name="1112"
      > </a
      ><a name="1113" class="Symbol"
      >&#8594;</a
      ><a name="1114"
      > </a
      ><a name="1115" class="PrimitiveType"
      >Set</a
      ><a name="1118"
      >
</a
      ><a name="1119" href="StlcProp.html#1084" class="Function"
      >CanonicalForms</a
      ><a name="1133"
      > </a
      ><a name="1134" href="StlcProp.html#1134" class="Bound"
      >t</a
      ><a name="1135"
      > </a
      ><a name="1136" href="Stlc.html#5406" class="InductiveConstructor"
      >bool</a
      ><a name="1140"
      >    </a
      ><a name="1144" class="Symbol"
      >=</a
      ><a name="1145"
      > </a
      ><a name="1146" href="StlcProp.html#1134" class="Bound"
      >t</a
      ><a name="1147"
      > </a
      ><a name="1148" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="1149"
      > </a
      ><a name="1150" href="Stlc.html#5604" class="InductiveConstructor"
      >true</a
      ><a name="1154"
      > </a
      ><a name="1155" href="https://agda.github.io/agda-stdlib/Data.Sum.html#433" class="Datatype Operator"
      >&#8846;</a
      ><a name="1156"
      > </a
      ><a name="1157" href="StlcProp.html#1134" class="Bound"
      >t</a
      ><a name="1158"
      > </a
      ><a name="1159" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="1160"
      > </a
      ><a name="1161" href="Stlc.html#5619" class="InductiveConstructor"
      >false</a
      ><a name="1166"
      >
</a
      ><a name="1167" href="StlcProp.html#1084" class="Function"
      >CanonicalForms</a
      ><a name="1181"
      > </a
      ><a name="1182" href="StlcProp.html#1182" class="Bound"
      >t</a
      ><a name="1183"
      > </a
      ><a name="1184" class="Symbol"
      >(</a
      ><a name="1185" href="StlcProp.html#1185" class="Bound"
      >A</a
      ><a name="1186"
      > </a
      ><a name="1187" href="Stlc.html#5420" class="InductiveConstructor Operator"
      >&#8658;</a
      ><a name="1188"
      > </a
      ><a name="1189" href="StlcProp.html#1189" class="Bound"
      >B</a
      ><a name="1190" class="Symbol"
      >)</a
      ><a name="1191"
      > </a
      ><a name="1192" class="Symbol"
      >=</a
      ><a name="1193"
      > </a
      ><a name="1194" href="https://agda.github.io/agda-stdlib/Data.Product.html#949" class="Function"
      >&#8707;&#8322;</a
      ><a name="1196"
      > </a
      ><a name="1197" class="Symbol"
      >&#955;</a
      ><a name="1198"
      > </a
      ><a name="1199" href="StlcProp.html#1199" class="Bound"
      >x</a
      ><a name="1200"
      > </a
      ><a name="1201" href="StlcProp.html#1201" class="Bound"
      >t&#8242;</a
      ><a name="1203"
      > </a
      ><a name="1204" class="Symbol"
      >&#8594;</a
      ><a name="1205"
      > </a
      ><a name="1206" href="StlcProp.html#1182" class="Bound"
      >t</a
      ><a name="1207"
      > </a
      ><a name="1208" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="1209"
      > </a
      ><a name="1210" href="Stlc.html#5570" class="InductiveConstructor"
      >abs</a
      ><a name="1213"
      > </a
      ><a name="1214" href="StlcProp.html#1199" class="Bound"
      >x</a
      ><a name="1215"
      > </a
      ><a name="1216" href="StlcProp.html#1185" class="Bound"
      >A</a
      ><a name="1217"
      > </a
      ><a name="1218" href="StlcProp.html#1201" class="Bound"
      >t&#8242;</a
      ><a name="1220"
      >

</a
      ><a name="1222" href="StlcProp.html#1222" class="Function"
      >canonicalForms</a
      ><a name="1236"
      > </a
      ><a name="1237" class="Symbol"
      >:</a
      ><a name="1238"
      > </a
      ><a name="1239" class="Symbol"
      >&#8704;</a
      ><a name="1240"
      > </a
      ><a name="1247" class="Symbol"
      >&#8594;</a
      ><a name="1248"
      > </a
      ><a name="1249" href="Stlc.html#18127" class="Function"
      >&#8709;</a
      ><a name="1250"
      > </a
      ><a name="1251" href="Stlc.html#19059" class="Datatype Operator"
      >&#8866;</a
      ><a name="1252"
      > </a
      ><a name="1253" href="StlcProp.html#1242" class="Bound"
      >t</a
      ><a name="1254"
      > </a
      ><a name="1255" href="Stlc.html#19059" class="Datatype Operator"
      >&#8758;</a
      ><a name="1256"
      > </a
      ><a name="1257" href="StlcProp.html#1244" class="Bound"
      >A</a
      ><a name="1258"
      > </a
      ><a name="1259" class="Symbol"
      >&#8594;</a
      ><a name="1260"
      > </a
      ><a name="1261" href="Stlc.html#8909" class="Datatype"
      >Value</a
      ><a name="1266"
      > </a
      ><a name="1267" href="StlcProp.html#1242" class="Bound"
      >t</a
      ><a name="1268"
      > </a
      ><a name="1269" class="Symbol"
      >&#8594;</a
      ><a name="1270"
      > </a
      ><a name="1271" href="StlcProp.html#1084" class="Function"
      >CanonicalForms</a
      ><a name="1285"
      > </a
      ><a name="1286" href="StlcProp.html#1242" class="Bound"
      >t</a
      ><a name="1287"
      > </a
      ><a name="1288" href="StlcProp.html#1244" class="Bound"
      >A</a
      ><a name="1289"
      >
</a
      ><a name="1290" href="StlcProp.html#1222" class="Function"
      >canonicalForms</a
      ><a name="1304"
      > </a
      ><a name="1305" class="Symbol"
      >(</a
      ><a name="1306" href="Stlc.html#19196" class="InductiveConstructor"
      >abs</a
      ><a name="1309"
      > </a
      ><a name="1310" href="StlcProp.html#1310" class="Bound"
      >t&#8242;</a
      ><a name="1312" class="Symbol"
      >)</a
      ><a name="1313"
      > </a
      ><a name="1314" href="Stlc.html#8936" class="InductiveConstructor"
      >abs</a
      ><a name="1317"
      >   </a
      ><a name="1320" class="Symbol"
      >=</a
      ><a name="1321"
      > </a
      ><a name="1322" class="Symbol"
      >_</a
      ><a name="1323"
      > </a
      ><a name="1324" href="https://agda.github.io/agda-stdlib/Data.Product.html#509" class="InductiveConstructor Operator"
      >,</a
      ><a name="1325"
      > </a
      ><a name="1326" class="Symbol"
      >_</a
      ><a name="1327"
      > </a
      ><a name="1328" href="https://agda.github.io/agda-stdlib/Data.Product.html#509" class="InductiveConstructor Operator"
      >,</a
      ><a name="1329"
      > </a
      ><a name="1330" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="1334"
      >
</a
      ><a name="1335" href="StlcProp.html#1222" class="Function"
      >canonicalForms</a
      ><a name="1349"
      > </a
      ><a name="1350" href="Stlc.html#19446" class="InductiveConstructor"
      >true</a
      ><a name="1354"
      >     </a
      ><a name="1359" href="Stlc.html#8984" class="InductiveConstructor"
      >true</a
      ><a name="1363"
      >  </a
      ><a name="1365" class="Symbol"
      >=</a
      ><a name="1366"
      > </a
      ><a name="1367" href="https://agda.github.io/agda-stdlib/Data.Sum.html#489" class="InductiveConstructor"
      >inj&#8321;</a
      ><a name="1371"
      > </a
      ><a name="1372" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="1376"
      >
</a
      ><a name="1377" href="StlcProp.html#1222" class="Function"
      >canonicalForms</a
      ><a name="1391"
      > </a
      ><a name="1392" href="Stlc.html#19505" class="InductiveConstructor"
      >false</a
      ><a name="1397"
      >    </a
      ><a name="1401" href="Stlc.html#9005" class="InductiveConstructor"
      >false</a
      ><a name="1406"
      > </a
      ><a name="1407" class="Symbol"
      >=</a
      ><a name="1408"
      > </a
      ><a name="1409" href="https://agda.github.io/agda-stdlib/Data.Sum.html#514" class="InductiveConstructor"
      >inj&#8322;</a
      ><a name="1413"
      > </a
      ><a name="1414" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
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
<a name="1815" href="StlcProp.html#1815" class="Function"
      >progress</a
      ><a name="1823"
      > </a
      ><a name="1824" class="Symbol"
      >:</a
      ><a name="1825"
      > </a
      ><a name="1826" class="Symbol"
      >&#8704;</a
      ><a name="1827"
      > </a
      ><a name="1834" class="Symbol"
      >&#8594;</a
      ><a name="1835"
      > </a
      ><a name="1836" href="Stlc.html#18127" class="Function"
      >&#8709;</a
      ><a name="1837"
      > </a
      ><a name="1838" href="Stlc.html#19059" class="Datatype Operator"
      >&#8866;</a
      ><a name="1839"
      > </a
      ><a name="1840" href="StlcProp.html#1829" class="Bound"
      >t</a
      ><a name="1841"
      > </a
      ><a name="1842" href="Stlc.html#19059" class="Datatype Operator"
      >&#8758;</a
      ><a name="1843"
      > </a
      ><a name="1844" href="StlcProp.html#1831" class="Bound"
      >A</a
      ><a name="1845"
      > </a
      ><a name="1846" class="Symbol"
      >&#8594;</a
      ><a name="1847"
      > </a
      ><a name="1848" href="Stlc.html#8909" class="Datatype"
      >Value</a
      ><a name="1853"
      > </a
      ><a name="1854" href="StlcProp.html#1829" class="Bound"
      >t</a
      ><a name="1855"
      > </a
      ><a name="1856" href="https://agda.github.io/agda-stdlib/Data.Sum.html#433" class="Datatype Operator"
      >&#8846;</a
      ><a name="1857"
      > </a
      ><a name="1858" href="https://agda.github.io/agda-stdlib/Data.Product.html#823" class="Function"
      >&#8707;</a
      ><a name="1859"
      > </a
      ><a name="1860" class="Symbol"
      >&#955;</a
      ><a name="1861"
      > </a
      ><a name="1862" href="StlcProp.html#1862" class="Bound"
      >t&#8242;</a
      ><a name="1864"
      > </a
      ><a name="1865" class="Symbol"
      >&#8594;</a
      ><a name="1866"
      > </a
      ><a name="1867" href="StlcProp.html#1829" class="Bound"
      >t</a
      ><a name="1868"
      > </a
      ><a name="1869" href="Stlc.html#15045" class="Datatype Operator"
      >==&gt;</a
      ><a name="1872"
      > </a
      ><a name="1873" href="StlcProp.html#1862" class="Bound"
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
<a name="3574" href="StlcProp.html#1815" class="Function"
      >progress</a
      ><a name="3582"
      > </a
      ><a name="3583" class="Symbol"
      >(</a
      ><a name="3584" href="Stlc.html#19103" class="InductiveConstructor"
      >var</a
      ><a name="3587"
      > </a
      ><a name="3588" href="StlcProp.html#3588" class="Bound"
      >x</a
      ><a name="3589"
      > </a
      ><a name="3590" class="Symbol"
      >())</a
      ><a name="3593"
      >
</a
      ><a name="3594" href="StlcProp.html#1815" class="Function"
      >progress</a
      ><a name="3602"
      > </a
      ><a name="3603" href="Stlc.html#19446" class="InductiveConstructor"
      >true</a
      ><a name="3607"
      >      </a
      ><a name="3613" class="Symbol"
      >=</a
      ><a name="3614"
      > </a
      ><a name="3615" href="https://agda.github.io/agda-stdlib/Data.Sum.html#489" class="InductiveConstructor"
      >inj&#8321;</a
      ><a name="3619"
      > </a
      ><a name="3620" href="Stlc.html#8984" class="InductiveConstructor"
      >true</a
      ><a name="3624"
      >
</a
      ><a name="3625" href="StlcProp.html#1815" class="Function"
      >progress</a
      ><a name="3633"
      > </a
      ><a name="3634" href="Stlc.html#19505" class="InductiveConstructor"
      >false</a
      ><a name="3639"
      >     </a
      ><a name="3644" class="Symbol"
      >=</a
      ><a name="3645"
      > </a
      ><a name="3646" href="https://agda.github.io/agda-stdlib/Data.Sum.html#489" class="InductiveConstructor"
      >inj&#8321;</a
      ><a name="3650"
      > </a
      ><a name="3651" href="Stlc.html#9005" class="InductiveConstructor"
      >false</a
      ><a name="3656"
      >
</a
      ><a name="3657" href="StlcProp.html#1815" class="Function"
      >progress</a
      ><a name="3665"
      > </a
      ><a name="3666" class="Symbol"
      >(</a
      ><a name="3667" href="Stlc.html#19196" class="InductiveConstructor"
      >abs</a
      ><a name="3670"
      > </a
      ><a name="3671" href="StlcProp.html#3671" class="Bound"
      >t&#8758;A</a
      ><a name="3674" class="Symbol"
      >)</a
      ><a name="3675"
      > </a
      ><a name="3676" class="Symbol"
      >=</a
      ><a name="3677"
      > </a
      ><a name="3678" href="https://agda.github.io/agda-stdlib/Data.Sum.html#489" class="InductiveConstructor"
      >inj&#8321;</a
      ><a name="3682"
      > </a
      ><a name="3683" href="Stlc.html#8936" class="InductiveConstructor"
      >abs</a
      ><a name="3686"
      >
</a
      ><a name="3687" href="StlcProp.html#1815" class="Function"
      >progress</a
      ><a name="3695"
      > </a
      ><a name="3696" class="Symbol"
      >(</a
      ><a name="3697" href="Stlc.html#19312" class="InductiveConstructor"
      >app</a
      ><a name="3700"
      > </a
      ><a name="3701" href="StlcProp.html#3701" class="Bound"
      >t&#8321;&#8758;A&#8658;B</a
      ><a name="3707"
      > </a
      ><a name="3708" href="StlcProp.html#3708" class="Bound"
      >t&#8322;&#8758;B</a
      ><a name="3712" class="Symbol"
      >)</a
      ><a name="3713"
      >
    </a
      ><a name="3718" class="Keyword"
      >with</a
      ><a name="3722"
      > </a
      ><a name="3723" href="StlcProp.html#1815" class="Function"
      >progress</a
      ><a name="3731"
      > </a
      ><a name="3732" href="StlcProp.html#3701" class="Bound"
      >t&#8321;&#8758;A&#8658;B</a
      ><a name="3738"
      >
</a
      ><a name="3739" class="Symbol"
      >...</a
      ><a name="3742"
      > </a
      ><a name="3743" class="Symbol"
      >|</a
      ><a name="3744"
      > </a
      ><a name="3745" href="https://agda.github.io/agda-stdlib/Data.Sum.html#514" class="InductiveConstructor"
      >inj&#8322;</a
      ><a name="3749"
      > </a
      ><a name="3750" class="Symbol"
      >(_</a
      ><a name="3752"
      > </a
      ><a name="3753" href="https://agda.github.io/agda-stdlib/Data.Product.html#509" class="InductiveConstructor Operator"
      >,</a
      ><a name="3754"
      > </a
      ><a name="3755" href="StlcProp.html#3755" class="Bound"
      >t&#8321;&#8658;t&#8321;&#8242;</a
      ><a name="3761" class="Symbol"
      >)</a
      ><a name="3762"
      > </a
      ><a name="3763" class="Symbol"
      >=</a
      ><a name="3764"
      > </a
      ><a name="3765" href="https://agda.github.io/agda-stdlib/Data.Sum.html#514" class="InductiveConstructor"
      >inj&#8322;</a
      ><a name="3769"
      > </a
      ><a name="3770" class="Symbol"
      >(_</a
      ><a name="3772"
      > </a
      ><a name="3773" href="https://agda.github.io/agda-stdlib/Data.Product.html#509" class="InductiveConstructor Operator"
      >,</a
      ><a name="3774"
      > </a
      ><a name="3775" href="Stlc.html#15170" class="InductiveConstructor"
      >app1</a
      ><a name="3779"
      > </a
      ><a name="3780" href="StlcProp.html#3755" class="Bound"
      >t&#8321;&#8658;t&#8321;&#8242;</a
      ><a name="3786" class="Symbol"
      >)</a
      ><a name="3787"
      >
</a
      ><a name="3788" class="Symbol"
      >...</a
      ><a name="3791"
      > </a
      ><a name="3792" class="Symbol"
      >|</a
      ><a name="3793"
      > </a
      ><a name="3794" href="https://agda.github.io/agda-stdlib/Data.Sum.html#489" class="InductiveConstructor"
      >inj&#8321;</a
      ><a name="3798"
      > </a
      ><a name="3799" href="StlcProp.html#3799" class="Bound"
      >v&#8321;</a
      ><a name="3801"
      >
    </a
      ><a name="3806" class="Keyword"
      >with</a
      ><a name="3810"
      > </a
      ><a name="3811" href="StlcProp.html#1815" class="Function"
      >progress</a
      ><a name="3819"
      > </a
      ><a name="3820" href="StlcProp.html#3708" class="Bound"
      >t&#8322;&#8758;B</a
      ><a name="3824"
      >
</a
      ><a name="3825" class="Symbol"
      >...</a
      ><a name="3828"
      > </a
      ><a name="3829" class="Symbol"
      >|</a
      ><a name="3830"
      > </a
      ><a name="3831" href="https://agda.github.io/agda-stdlib/Data.Sum.html#514" class="InductiveConstructor"
      >inj&#8322;</a
      ><a name="3835"
      > </a
      ><a name="3836" class="Symbol"
      >(_</a
      ><a name="3838"
      > </a
      ><a name="3839" href="https://agda.github.io/agda-stdlib/Data.Product.html#509" class="InductiveConstructor Operator"
      >,</a
      ><a name="3840"
      > </a
      ><a name="3841" href="StlcProp.html#3841" class="Bound"
      >t&#8322;&#8658;t&#8322;&#8242;</a
      ><a name="3847" class="Symbol"
      >)</a
      ><a name="3848"
      > </a
      ><a name="3849" class="Symbol"
      >=</a
      ><a name="3850"
      > </a
      ><a name="3851" href="https://agda.github.io/agda-stdlib/Data.Sum.html#514" class="InductiveConstructor"
      >inj&#8322;</a
      ><a name="3855"
      > </a
      ><a name="3856" class="Symbol"
      >(_</a
      ><a name="3858"
      > </a
      ><a name="3859" href="https://agda.github.io/agda-stdlib/Data.Product.html#509" class="InductiveConstructor Operator"
      >,</a
      ><a name="3860"
      > </a
      ><a name="3861" href="Stlc.html#15247" class="InductiveConstructor"
      >app2</a
      ><a name="3865"
      > </a
      ><a name="3866" href="StlcProp.html#3799" class="Bound"
      >v&#8321;</a
      ><a name="3868"
      > </a
      ><a name="3869" href="StlcProp.html#3841" class="Bound"
      >t&#8322;&#8658;t&#8322;&#8242;</a
      ><a name="3875" class="Symbol"
      >)</a
      ><a name="3876"
      >
</a
      ><a name="3877" class="Symbol"
      >...</a
      ><a name="3880"
      > </a
      ><a name="3881" class="Symbol"
      >|</a
      ><a name="3882"
      > </a
      ><a name="3883" href="https://agda.github.io/agda-stdlib/Data.Sum.html#489" class="InductiveConstructor"
      >inj&#8321;</a
      ><a name="3887"
      > </a
      ><a name="3888" href="StlcProp.html#3888" class="Bound"
      >v&#8322;</a
      ><a name="3890"
      >
    </a
      ><a name="3895" class="Keyword"
      >with</a
      ><a name="3899"
      > </a
      ><a name="3900" href="StlcProp.html#1222" class="Function"
      >canonicalForms</a
      ><a name="3914"
      > </a
      ><a name="3915" href="StlcProp.html#3701" class="Bound"
      >t&#8321;&#8758;A&#8658;B</a
      ><a name="3921"
      > </a
      ><a name="3922" href="StlcProp.html#3799" class="Bound"
      >v&#8321;</a
      ><a name="3924"
      >
</a
      ><a name="3925" class="Symbol"
      >...</a
      ><a name="3928"
      > </a
      ><a name="3929" class="Symbol"
      >|</a
      ><a name="3930"
      > </a
      ><a name="3931" class="Symbol"
      >(_</a
      ><a name="3933"
      > </a
      ><a name="3934" href="https://agda.github.io/agda-stdlib/Data.Product.html#509" class="InductiveConstructor Operator"
      >,</a
      ><a name="3935"
      > </a
      ><a name="3936" class="Symbol"
      >_</a
      ><a name="3937"
      > </a
      ><a name="3938" href="https://agda.github.io/agda-stdlib/Data.Product.html#509" class="InductiveConstructor Operator"
      >,</a
      ><a name="3939"
      > </a
      ><a name="3940" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="3944" class="Symbol"
      >)</a
      ><a name="3945"
      > </a
      ><a name="3946" class="Symbol"
      >=</a
      ><a name="3947"
      > </a
      ><a name="3948" href="https://agda.github.io/agda-stdlib/Data.Sum.html#514" class="InductiveConstructor"
      >inj&#8322;</a
      ><a name="3952"
      > </a
      ><a name="3953" class="Symbol"
      >(_</a
      ><a name="3955"
      > </a
      ><a name="3956" href="https://agda.github.io/agda-stdlib/Data.Product.html#509" class="InductiveConstructor Operator"
      >,</a
      ><a name="3957"
      > </a
      ><a name="3958" href="Stlc.html#15079" class="InductiveConstructor"
      >red</a
      ><a name="3961"
      > </a
      ><a name="3962" href="StlcProp.html#3888" class="Bound"
      >v&#8322;</a
      ><a name="3964" class="Symbol"
      >)</a
      ><a name="3965"
      >
</a
      ><a name="3966" href="StlcProp.html#1815" class="Function"
      >progress</a
      ><a name="3974"
      > </a
      ><a name="3975" class="Symbol"
      >(</a
      ><a name="3976" href="Stlc.html#19564" class="InductiveConstructor Operator"
      >if</a
      ><a name="3978"
      > </a
      ><a name="3979" href="StlcProp.html#3979" class="Bound"
      >t&#8321;&#8758;bool</a
      ><a name="3986"
      > </a
      ><a name="3987" href="Stlc.html#19564" class="InductiveConstructor Operator"
      >then</a
      ><a name="3991"
      > </a
      ><a name="3992" href="StlcProp.html#3992" class="Bound"
      >t&#8322;&#8758;A</a
      ><a name="3996"
      > </a
      ><a name="3997" href="Stlc.html#19564" class="InductiveConstructor Operator"
      >else</a
      ><a name="4001"
      > </a
      ><a name="4002" href="StlcProp.html#4002" class="Bound"
      >t&#8323;&#8758;A</a
      ><a name="4006" class="Symbol"
      >)</a
      ><a name="4007"
      >
    </a
      ><a name="4012" class="Keyword"
      >with</a
      ><a name="4016"
      > </a
      ><a name="4017" href="StlcProp.html#1815" class="Function"
      >progress</a
      ><a name="4025"
      > </a
      ><a name="4026" href="StlcProp.html#3979" class="Bound"
      >t&#8321;&#8758;bool</a
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
      ><a name="4040" href="https://agda.github.io/agda-stdlib/Data.Sum.html#514" class="InductiveConstructor"
      >inj&#8322;</a
      ><a name="4044"
      > </a
      ><a name="4045" class="Symbol"
      >(_</a
      ><a name="4047"
      > </a
      ><a name="4048" href="https://agda.github.io/agda-stdlib/Data.Product.html#509" class="InductiveConstructor Operator"
      >,</a
      ><a name="4049"
      > </a
      ><a name="4050" href="StlcProp.html#4050" class="Bound"
      >t&#8321;&#8658;t&#8321;&#8242;</a
      ><a name="4056" class="Symbol"
      >)</a
      ><a name="4057"
      > </a
      ><a name="4058" class="Symbol"
      >=</a
      ><a name="4059"
      > </a
      ><a name="4060" href="https://agda.github.io/agda-stdlib/Data.Sum.html#514" class="InductiveConstructor"
      >inj&#8322;</a
      ><a name="4064"
      > </a
      ><a name="4065" class="Symbol"
      >(_</a
      ><a name="4067"
      > </a
      ><a name="4068" href="https://agda.github.io/agda-stdlib/Data.Product.html#509" class="InductiveConstructor Operator"
      >,</a
      ><a name="4069"
      > </a
      ><a name="4070" href="Stlc.html#15344" class="InductiveConstructor"
      >if</a
      ><a name="4072"
      > </a
      ><a name="4073" href="StlcProp.html#4050" class="Bound"
      >t&#8321;&#8658;t&#8321;&#8242;</a
      ><a name="4079" class="Symbol"
      >)</a
      ><a name="4080"
      >
</a
      ><a name="4081" class="Symbol"
      >...</a
      ><a name="4084"
      > </a
      ><a name="4085" class="Symbol"
      >|</a
      ><a name="4086"
      > </a
      ><a name="4087" href="https://agda.github.io/agda-stdlib/Data.Sum.html#489" class="InductiveConstructor"
      >inj&#8321;</a
      ><a name="4091"
      > </a
      ><a name="4092" href="StlcProp.html#4092" class="Bound"
      >v&#8321;</a
      ><a name="4094"
      >
    </a
      ><a name="4099" class="Keyword"
      >with</a
      ><a name="4103"
      > </a
      ><a name="4104" href="StlcProp.html#1222" class="Function"
      >canonicalForms</a
      ><a name="4118"
      > </a
      ><a name="4119" href="StlcProp.html#3979" class="Bound"
      >t&#8321;&#8758;bool</a
      ><a name="4126"
      > </a
      ><a name="4127" href="StlcProp.html#4092" class="Bound"
      >v&#8321;</a
      ><a name="4129"
      >
</a
      ><a name="4130" class="Symbol"
      >...</a
      ><a name="4133"
      > </a
      ><a name="4134" class="Symbol"
      >|</a
      ><a name="4135"
      > </a
      ><a name="4136" href="https://agda.github.io/agda-stdlib/Data.Sum.html#489" class="InductiveConstructor"
      >inj&#8321;</a
      ><a name="4140"
      > </a
      ><a name="4141" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="4145"
      > </a
      ><a name="4146" class="Symbol"
      >=</a
      ><a name="4147"
      > </a
      ><a name="4148" href="https://agda.github.io/agda-stdlib/Data.Sum.html#514" class="InductiveConstructor"
      >inj&#8322;</a
      ><a name="4152"
      > </a
      ><a name="4153" class="Symbol"
      >(_</a
      ><a name="4155"
      > </a
      ><a name="4156" href="https://agda.github.io/agda-stdlib/Data.Product.html#509" class="InductiveConstructor Operator"
      >,</a
      ><a name="4157"
      > </a
      ><a name="4158" href="Stlc.html#15445" class="InductiveConstructor"
      >iftrue</a
      ><a name="4164" class="Symbol"
      >)</a
      ><a name="4165"
      >
</a
      ><a name="4166" class="Symbol"
      >...</a
      ><a name="4169"
      > </a
      ><a name="4170" class="Symbol"
      >|</a
      ><a name="4171"
      > </a
      ><a name="4172" href="https://agda.github.io/agda-stdlib/Data.Sum.html#514" class="InductiveConstructor"
      >inj&#8322;</a
      ><a name="4176"
      > </a
      ><a name="4177" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="4181"
      > </a
      ><a name="4182" class="Symbol"
      >=</a
      ><a name="4183"
      > </a
      ><a name="4184" href="https://agda.github.io/agda-stdlib/Data.Sum.html#514" class="InductiveConstructor"
      >inj&#8322;</a
      ><a name="4188"
      > </a
      ><a name="4189" class="Symbol"
      >(_</a
      ><a name="4191"
      > </a
      ><a name="4192" href="https://agda.github.io/agda-stdlib/Data.Product.html#509" class="InductiveConstructor Operator"
      >,</a
      ><a name="4193"
      > </a
      ><a name="4194" href="Stlc.html#15505" class="InductiveConstructor"
      >iffalse</a
      ><a name="4201" class="Symbol"
      >)</a
      >
{% endraw %}</pre>

#### Exercise: 3 stars, optional (progress_from_term_ind)
Show that progress can also be proved by induction on terms
instead of induction on typing derivations.

<pre class="Agda">{% raw %}
<a name="4391" class="Keyword"
      >postulate</a
      ><a name="4400"
      >
  </a
      ><a name="4403" href="StlcProp.html#4403" class="Postulate"
      >progress&#8242;</a
      ><a name="4412"
      > </a
      ><a name="4413" class="Symbol"
      >:</a
      ><a name="4414"
      > </a
      ><a name="4415" class="Symbol"
      >&#8704;</a
      ><a name="4416"
      > </a
      ><a name="4423" class="Symbol"
      >&#8594;</a
      ><a name="4424"
      > </a
      ><a name="4425" href="Stlc.html#18127" class="Function"
      >&#8709;</a
      ><a name="4426"
      > </a
      ><a name="4427" href="Stlc.html#19059" class="Datatype Operator"
      >&#8866;</a
      ><a name="4428"
      > </a
      ><a name="4429" href="StlcProp.html#4418" class="Bound"
      >t</a
      ><a name="4430"
      > </a
      ><a name="4431" href="Stlc.html#19059" class="Datatype Operator"
      >&#8758;</a
      ><a name="4432"
      > </a
      ><a name="4433" href="StlcProp.html#4420" class="Bound"
      >A</a
      ><a name="4434"
      > </a
      ><a name="4435" class="Symbol"
      >&#8594;</a
      ><a name="4436"
      > </a
      ><a name="4437" href="Stlc.html#8909" class="Datatype"
      >Value</a
      ><a name="4442"
      > </a
      ><a name="4443" href="StlcProp.html#4418" class="Bound"
      >t</a
      ><a name="4444"
      > </a
      ><a name="4445" href="https://agda.github.io/agda-stdlib/Data.Sum.html#433" class="Datatype Operator"
      >&#8846;</a
      ><a name="4446"
      > </a
      ><a name="4447" href="https://agda.github.io/agda-stdlib/Data.Product.html#823" class="Function"
      >&#8707;</a
      ><a name="4448"
      > </a
      ><a name="4449" class="Symbol"
      >&#955;</a
      ><a name="4450"
      > </a
      ><a name="4451" href="StlcProp.html#4451" class="Bound"
      >t&#8242;</a
      ><a name="4453"
      > </a
      ><a name="4454" class="Symbol"
      >&#8594;</a
      ><a name="4455"
      > </a
      ><a name="4456" href="StlcProp.html#4418" class="Bound"
      >t</a
      ><a name="4457"
      > </a
      ><a name="4458" href="Stlc.html#15045" class="Datatype Operator"
      >==&gt;</a
      ><a name="4461"
      > </a
      ><a name="4462" href="StlcProp.html#4451" class="Bound"
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

A variable $$x$$ _appears free in_ a term _t_ if $$t$$ contains some
occurrence of $$x$$ that is not under an abstraction labeled $$x$$.
For example:

  - $$y$$ appears free, but $$x$$ does not, in $$\lambda x : A\to B. x\;y$$
  - both $$x$$ and $$y$$ appear free in $$(\lambda x:A\to B. x\;y) x$$
  - no variables appear free in $$\lambda x:A\to B. \lambda y:A. x\;y$$

Formally:

<pre class="Agda">{% raw %}
<a name="6902" class="Keyword"
      >data</a
      ><a name="6906"
      > </a
      ><a name="6907" href="StlcProp.html#6907" class="Datatype Operator"
      >_FreeIn_</a
      ><a name="6915"
      > </a
      ><a name="6916" class="Symbol"
      >(</a
      ><a name="6917" href="StlcProp.html#6917" class="Bound"
      >x</a
      ><a name="6918"
      > </a
      ><a name="6919" class="Symbol"
      >:</a
      ><a name="6920"
      > </a
      ><a name="6921" href="Maps.html#2243" class="Datatype"
      >Id</a
      ><a name="6923" class="Symbol"
      >)</a
      ><a name="6924"
      > </a
      ><a name="6925" class="Symbol"
      >:</a
      ><a name="6926"
      > </a
      ><a name="6927" href="Stlc.html#5502" class="Datatype"
      >Term</a
      ><a name="6931"
      > </a
      ><a name="6932" class="Symbol"
      >&#8594;</a
      ><a name="6933"
      > </a
      ><a name="6934" class="PrimitiveType"
      >Set</a
      ><a name="6937"
      > </a
      ><a name="6938" class="Keyword"
      >where</a
      ><a name="6943"
      >
  </a
      ><a name="6946" href="StlcProp.html#6946" class="InductiveConstructor"
      >var</a
      ><a name="6949"
      >  </a
      ><a name="6951" class="Symbol"
      >:</a
      ><a name="6952"
      > </a
      ><a name="6953" href="StlcProp.html#6917" class="Bound"
      >x</a
      ><a name="6954"
      > </a
      ><a name="6955" href="StlcProp.html#6907" class="Datatype Operator"
      >FreeIn</a
      ><a name="6961"
      > </a
      ><a name="6962" href="Stlc.html#5521" class="InductiveConstructor"
      >var</a
      ><a name="6965"
      > </a
      ><a name="6966" href="StlcProp.html#6917" class="Bound"
      >x</a
      ><a name="6967"
      >
  </a
      ><a name="6970" href="StlcProp.html#6970" class="InductiveConstructor"
      >abs</a
      ><a name="6973"
      >  </a
      ><a name="6975" class="Symbol"
      >:</a
      ><a name="6976"
      > </a
      ><a name="6977" class="Symbol"
      >&#8704;</a
      ><a name="6978"
      > </a
      ><a name="6987" class="Symbol"
      >&#8594;</a
      ><a name="6988"
      > </a
      ><a name="6989" href="StlcProp.html#6980" class="Bound"
      >y</a
      ><a name="6990"
      > </a
      ><a name="6991" href="https://agda.github.io/agda-stdlib/Relation.Binary.Core.html#4493" class="Function Operator"
      >&#8802;</a
      ><a name="6992"
      > </a
      ><a name="6993" href="StlcProp.html#6917" class="Bound"
      >x</a
      ><a name="6994"
      > </a
      ><a name="6995" class="Symbol"
      >&#8594;</a
      ><a name="6996"
      > </a
      ><a name="6997" href="StlcProp.html#6917" class="Bound"
      >x</a
      ><a name="6998"
      > </a
      ><a name="6999" href="StlcProp.html#6907" class="Datatype Operator"
      >FreeIn</a
      ><a name="7005"
      > </a
      ><a name="7006" href="StlcProp.html#6984" class="Bound"
      >t</a
      ><a name="7007"
      > </a
      ><a name="7008" class="Symbol"
      >&#8594;</a
      ><a name="7009"
      > </a
      ><a name="7010" href="StlcProp.html#6917" class="Bound"
      >x</a
      ><a name="7011"
      > </a
      ><a name="7012" href="StlcProp.html#6907" class="Datatype Operator"
      >FreeIn</a
      ><a name="7018"
      > </a
      ><a name="7019" href="Stlc.html#5570" class="InductiveConstructor"
      >abs</a
      ><a name="7022"
      > </a
      ><a name="7023" href="StlcProp.html#6980" class="Bound"
      >y</a
      ><a name="7024"
      > </a
      ><a name="7025" href="StlcProp.html#6982" class="Bound"
      >A</a
      ><a name="7026"
      > </a
      ><a name="7027" href="StlcProp.html#6984" class="Bound"
      >t</a
      ><a name="7028"
      >
  </a
      ><a name="7031" href="StlcProp.html#7031" class="InductiveConstructor"
      >app1</a
      ><a name="7035"
      > </a
      ><a name="7036" class="Symbol"
      >:</a
      ><a name="7037"
      > </a
      ><a name="7038" class="Symbol"
      >&#8704;</a
      ><a name="7039"
      > </a
      ><a name="7048" class="Symbol"
      >&#8594;</a
      ><a name="7049"
      > </a
      ><a name="7050" href="StlcProp.html#6917" class="Bound"
      >x</a
      ><a name="7051"
      > </a
      ><a name="7052" href="StlcProp.html#6907" class="Datatype Operator"
      >FreeIn</a
      ><a name="7058"
      > </a
      ><a name="7059" href="StlcProp.html#7041" class="Bound"
      >t&#8321;</a
      ><a name="7061"
      > </a
      ><a name="7062" class="Symbol"
      >&#8594;</a
      ><a name="7063"
      > </a
      ><a name="7064" href="StlcProp.html#6917" class="Bound"
      >x</a
      ><a name="7065"
      > </a
      ><a name="7066" href="StlcProp.html#6907" class="Datatype Operator"
      >FreeIn</a
      ><a name="7072"
      > </a
      ><a name="7073" href="Stlc.html#5541" class="InductiveConstructor"
      >app</a
      ><a name="7076"
      > </a
      ><a name="7077" href="StlcProp.html#7041" class="Bound"
      >t&#8321;</a
      ><a name="7079"
      > </a
      ><a name="7080" href="StlcProp.html#7044" class="Bound"
      >t&#8322;</a
      ><a name="7082"
      >
  </a
      ><a name="7085" href="StlcProp.html#7085" class="InductiveConstructor"
      >app2</a
      ><a name="7089"
      > </a
      ><a name="7090" class="Symbol"
      >:</a
      ><a name="7091"
      > </a
      ><a name="7092" class="Symbol"
      >&#8704;</a
      ><a name="7093"
      > </a
      ><a name="7102" class="Symbol"
      >&#8594;</a
      ><a name="7103"
      > </a
      ><a name="7104" href="StlcProp.html#6917" class="Bound"
      >x</a
      ><a name="7105"
      > </a
      ><a name="7106" href="StlcProp.html#6907" class="Datatype Operator"
      >FreeIn</a
      ><a name="7112"
      > </a
      ><a name="7113" href="StlcProp.html#7098" class="Bound"
      >t&#8322;</a
      ><a name="7115"
      > </a
      ><a name="7116" class="Symbol"
      >&#8594;</a
      ><a name="7117"
      > </a
      ><a name="7118" href="StlcProp.html#6917" class="Bound"
      >x</a
      ><a name="7119"
      > </a
      ><a name="7120" href="StlcProp.html#6907" class="Datatype Operator"
      >FreeIn</a
      ><a name="7126"
      > </a
      ><a name="7127" href="Stlc.html#5541" class="InductiveConstructor"
      >app</a
      ><a name="7130"
      > </a
      ><a name="7131" href="StlcProp.html#7095" class="Bound"
      >t&#8321;</a
      ><a name="7133"
      > </a
      ><a name="7134" href="StlcProp.html#7098" class="Bound"
      >t&#8322;</a
      ><a name="7136"
      >
  </a
      ><a name="7139" href="StlcProp.html#7139" class="InductiveConstructor"
      >if1</a
      ><a name="7142"
      >  </a
      ><a name="7144" class="Symbol"
      >:</a
      ><a name="7145"
      > </a
      ><a name="7146" class="Symbol"
      >&#8704;</a
      ><a name="7147"
      > </a
      ><a name="7159" class="Symbol"
      >&#8594;</a
      ><a name="7160"
      > </a
      ><a name="7161" href="StlcProp.html#6917" class="Bound"
      >x</a
      ><a name="7162"
      > </a
      ><a name="7163" href="StlcProp.html#6907" class="Datatype Operator"
      >FreeIn</a
      ><a name="7169"
      > </a
      ><a name="7170" href="StlcProp.html#7149" class="Bound"
      >t&#8321;</a
      ><a name="7172"
      > </a
      ><a name="7173" class="Symbol"
      >&#8594;</a
      ><a name="7174"
      > </a
      ><a name="7175" href="StlcProp.html#6917" class="Bound"
      >x</a
      ><a name="7176"
      > </a
      ><a name="7177" href="StlcProp.html#6907" class="Datatype Operator"
      >FreeIn</a
      ><a name="7183"
      > </a
      ><a name="7184" class="Symbol"
      >(</a
      ><a name="7185" href="Stlc.html#5634" class="InductiveConstructor Operator"
      >if</a
      ><a name="7187"
      > </a
      ><a name="7188" href="StlcProp.html#7149" class="Bound"
      >t&#8321;</a
      ><a name="7190"
      > </a
      ><a name="7191" href="Stlc.html#5634" class="InductiveConstructor Operator"
      >then</a
      ><a name="7195"
      > </a
      ><a name="7196" href="StlcProp.html#7152" class="Bound"
      >t&#8322;</a
      ><a name="7198"
      > </a
      ><a name="7199" href="Stlc.html#5634" class="InductiveConstructor Operator"
      >else</a
      ><a name="7203"
      > </a
      ><a name="7204" href="StlcProp.html#7155" class="Bound"
      >t&#8323;</a
      ><a name="7206" class="Symbol"
      >)</a
      ><a name="7207"
      >
  </a
      ><a name="7210" href="StlcProp.html#7210" class="InductiveConstructor"
      >if2</a
      ><a name="7213"
      >  </a
      ><a name="7215" class="Symbol"
      >:</a
      ><a name="7216"
      > </a
      ><a name="7217" class="Symbol"
      >&#8704;</a
      ><a name="7218"
      > </a
      ><a name="7230" class="Symbol"
      >&#8594;</a
      ><a name="7231"
      > </a
      ><a name="7232" href="StlcProp.html#6917" class="Bound"
      >x</a
      ><a name="7233"
      > </a
      ><a name="7234" href="StlcProp.html#6907" class="Datatype Operator"
      >FreeIn</a
      ><a name="7240"
      > </a
      ><a name="7241" href="StlcProp.html#7223" class="Bound"
      >t&#8322;</a
      ><a name="7243"
      > </a
      ><a name="7244" class="Symbol"
      >&#8594;</a
      ><a name="7245"
      > </a
      ><a name="7246" href="StlcProp.html#6917" class="Bound"
      >x</a
      ><a name="7247"
      > </a
      ><a name="7248" href="StlcProp.html#6907" class="Datatype Operator"
      >FreeIn</a
      ><a name="7254"
      > </a
      ><a name="7255" class="Symbol"
      >(</a
      ><a name="7256" href="Stlc.html#5634" class="InductiveConstructor Operator"
      >if</a
      ><a name="7258"
      > </a
      ><a name="7259" href="StlcProp.html#7220" class="Bound"
      >t&#8321;</a
      ><a name="7261"
      > </a
      ><a name="7262" href="Stlc.html#5634" class="InductiveConstructor Operator"
      >then</a
      ><a name="7266"
      > </a
      ><a name="7267" href="StlcProp.html#7223" class="Bound"
      >t&#8322;</a
      ><a name="7269"
      > </a
      ><a name="7270" href="Stlc.html#5634" class="InductiveConstructor Operator"
      >else</a
      ><a name="7274"
      > </a
      ><a name="7275" href="StlcProp.html#7226" class="Bound"
      >t&#8323;</a
      ><a name="7277" class="Symbol"
      >)</a
      ><a name="7278"
      >
  </a
      ><a name="7281" href="StlcProp.html#7281" class="InductiveConstructor"
      >if3</a
      ><a name="7284"
      >  </a
      ><a name="7286" class="Symbol"
      >:</a
      ><a name="7287"
      > </a
      ><a name="7288" class="Symbol"
      >&#8704;</a
      ><a name="7289"
      > </a
      ><a name="7301" class="Symbol"
      >&#8594;</a
      ><a name="7302"
      > </a
      ><a name="7303" href="StlcProp.html#6917" class="Bound"
      >x</a
      ><a name="7304"
      > </a
      ><a name="7305" href="StlcProp.html#6907" class="Datatype Operator"
      >FreeIn</a
      ><a name="7311"
      > </a
      ><a name="7312" href="StlcProp.html#7297" class="Bound"
      >t&#8323;</a
      ><a name="7314"
      > </a
      ><a name="7315" class="Symbol"
      >&#8594;</a
      ><a name="7316"
      > </a
      ><a name="7317" href="StlcProp.html#6917" class="Bound"
      >x</a
      ><a name="7318"
      > </a
      ><a name="7319" href="StlcProp.html#6907" class="Datatype Operator"
      >FreeIn</a
      ><a name="7325"
      > </a
      ><a name="7326" class="Symbol"
      >(</a
      ><a name="7327" href="Stlc.html#5634" class="InductiveConstructor Operator"
      >if</a
      ><a name="7329"
      > </a
      ><a name="7330" href="StlcProp.html#7291" class="Bound"
      >t&#8321;</a
      ><a name="7332"
      > </a
      ><a name="7333" href="Stlc.html#5634" class="InductiveConstructor Operator"
      >then</a
      ><a name="7337"
      > </a
      ><a name="7338" href="StlcProp.html#7294" class="Bound"
      >t&#8322;</a
      ><a name="7340"
      > </a
      ><a name="7341" href="Stlc.html#5634" class="InductiveConstructor Operator"
      >else</a
      ><a name="7345"
      > </a
      ><a name="7346" href="StlcProp.html#7297" class="Bound"
      >t&#8323;</a
      ><a name="7348" class="Symbol"
      >)</a
      >
{% endraw %}</pre>

A term in which no variables appear free is said to be _closed_.

<pre class="Agda">{% raw %}
<a name="7441" href="StlcProp.html#7441" class="Function"
      >Closed</a
      ><a name="7447"
      > </a
      ><a name="7448" class="Symbol"
      >:</a
      ><a name="7449"
      > </a
      ><a name="7450" href="Stlc.html#5502" class="Datatype"
      >Term</a
      ><a name="7454"
      > </a
      ><a name="7455" class="Symbol"
      >&#8594;</a
      ><a name="7456"
      > </a
      ><a name="7457" class="PrimitiveType"
      >Set</a
      ><a name="7460"
      >
</a
      ><a name="7461" href="StlcProp.html#7441" class="Function"
      >Closed</a
      ><a name="7467"
      > </a
      ><a name="7468" href="StlcProp.html#7468" class="Bound"
      >t</a
      ><a name="7469"
      > </a
      ><a name="7470" class="Symbol"
      >=</a
      ><a name="7471"
      > </a
      ><a name="7472" class="Symbol"
      >&#8704;</a
      ><a name="7473"
      > </a
      ><a name="7478" class="Symbol"
      >&#8594;</a
      ><a name="7479"
      > </a
      ><a name="7480" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#414" class="Function Operator"
      >&#172;</a
      ><a name="7481"
      > </a
      ><a name="7482" class="Symbol"
      >(</a
      ><a name="7483" href="StlcProp.html#7475" class="Bound"
      >x</a
      ><a name="7484"
      > </a
      ><a name="7485" href="StlcProp.html#6907" class="Datatype Operator"
      >FreeIn</a
      ><a name="7491"
      > </a
      ><a name="7492" href="StlcProp.html#7468" class="Bound"
      >t</a
      ><a name="7493" class="Symbol"
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
<a name="8222" href="StlcProp.html#8222" class="Function"
      >freeInCtxt</a
      ><a name="8232"
      > </a
      ><a name="8233" class="Symbol"
      >:</a
      ><a name="8234"
      > </a
      ><a name="8235" class="Symbol"
      >&#8704;</a
      ><a name="8236"
      > </a
      ><a name="8247" class="Symbol"
      >&#8594;</a
      ><a name="8248"
      > </a
      ><a name="8249" href="StlcProp.html#8238" class="Bound"
      >x</a
      ><a name="8250"
      > </a
      ><a name="8251" href="StlcProp.html#6907" class="Datatype Operator"
      >FreeIn</a
      ><a name="8257"
      > </a
      ><a name="8258" href="StlcProp.html#8240" class="Bound"
      >t</a
      ><a name="8259"
      > </a
      ><a name="8260" class="Symbol"
      >&#8594;</a
      ><a name="8261"
      > </a
      ><a name="8262" href="StlcProp.html#8244" class="Bound"
      >&#915;</a
      ><a name="8263"
      > </a
      ><a name="8264" href="Stlc.html#19059" class="Datatype Operator"
      >&#8866;</a
      ><a name="8265"
      > </a
      ><a name="8266" href="StlcProp.html#8240" class="Bound"
      >t</a
      ><a name="8267"
      > </a
      ><a name="8268" href="Stlc.html#19059" class="Datatype Operator"
      >&#8758;</a
      ><a name="8269"
      > </a
      ><a name="8270" href="StlcProp.html#8242" class="Bound"
      >A</a
      ><a name="8271"
      > </a
      ><a name="8272" class="Symbol"
      >&#8594;</a
      ><a name="8273"
      > </a
      ><a name="8274" href="https://agda.github.io/agda-stdlib/Data.Product.html#823" class="Function"
      >&#8707;</a
      ><a name="8275"
      > </a
      ><a name="8276" class="Symbol"
      >&#955;</a
      ><a name="8277"
      > </a
      ><a name="8278" href="StlcProp.html#8278" class="Bound"
      >B</a
      ><a name="8279"
      > </a
      ><a name="8280" class="Symbol"
      >&#8594;</a
      ><a name="8281"
      > </a
      ><a name="8282" href="StlcProp.html#8244" class="Bound"
      >&#915;</a
      ><a name="8283"
      > </a
      ><a name="8284" href="StlcProp.html#8238" class="Bound"
      >x</a
      ><a name="8285"
      > </a
      ><a name="8286" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="8287"
      > </a
      ><a name="8288" href="https://agda.github.io/agda-stdlib/Data.Maybe.Base.html#373" class="InductiveConstructor"
      >just</a
      ><a name="8292"
      > </a
      ><a name="8293" href="StlcProp.html#8278" class="Bound"
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
<a name="9889" href="StlcProp.html#8222" class="Function"
      >freeInCtxt</a
      ><a name="9899"
      > </a
      ><a name="9900" href="StlcProp.html#6946" class="InductiveConstructor"
      >var</a
      ><a name="9903"
      > </a
      ><a name="9904" class="Symbol"
      >(</a
      ><a name="9905" href="Stlc.html#19103" class="InductiveConstructor"
      >var</a
      ><a name="9908"
      > </a
      ><a name="9909" class="Symbol"
      >_</a
      ><a name="9910"
      > </a
      ><a name="9911" href="StlcProp.html#9911" class="Bound"
      >x&#8758;A</a
      ><a name="9914" class="Symbol"
      >)</a
      ><a name="9915"
      > </a
      ><a name="9916" class="Symbol"
      >=</a
      ><a name="9917"
      > </a
      ><a name="9918" class="Symbol"
      >(_</a
      ><a name="9920"
      > </a
      ><a name="9921" href="https://agda.github.io/agda-stdlib/Data.Product.html#509" class="InductiveConstructor Operator"
      >,</a
      ><a name="9922"
      > </a
      ><a name="9923" href="StlcProp.html#9911" class="Bound"
      >x&#8758;A</a
      ><a name="9926" class="Symbol"
      >)</a
      ><a name="9927"
      >
</a
      ><a name="9928" href="StlcProp.html#8222" class="Function"
      >freeInCtxt</a
      ><a name="9938"
      > </a
      ><a name="9939" class="Symbol"
      >(</a
      ><a name="9940" href="StlcProp.html#7031" class="InductiveConstructor"
      >app1</a
      ><a name="9944"
      > </a
      ><a name="9945" href="StlcProp.html#9945" class="Bound"
      >x&#8712;t&#8321;</a
      ><a name="9949" class="Symbol"
      >)</a
      ><a name="9950"
      > </a
      ><a name="9951" class="Symbol"
      >(</a
      ><a name="9952" href="Stlc.html#19312" class="InductiveConstructor"
      >app</a
      ><a name="9955"
      > </a
      ><a name="9956" href="StlcProp.html#9956" class="Bound"
      >t&#8321;&#8758;A</a
      ><a name="9960"
      > </a
      ><a name="9961" class="Symbol"
      >_</a
      ><a name="9962"
      >   </a
      ><a name="9965" class="Symbol"
      >)</a
      ><a name="9966"
      > </a
      ><a name="9967" class="Symbol"
      >=</a
      ><a name="9968"
      > </a
      ><a name="9969" href="StlcProp.html#8222" class="Function"
      >freeInCtxt</a
      ><a name="9979"
      > </a
      ><a name="9980" href="StlcProp.html#9945" class="Bound"
      >x&#8712;t&#8321;</a
      ><a name="9984"
      > </a
      ><a name="9985" href="StlcProp.html#9956" class="Bound"
      >t&#8321;&#8758;A</a
      ><a name="9989"
      >
</a
      ><a name="9990" href="StlcProp.html#8222" class="Function"
      >freeInCtxt</a
      ><a name="10000"
      > </a
      ><a name="10001" class="Symbol"
      >(</a
      ><a name="10002" href="StlcProp.html#7085" class="InductiveConstructor"
      >app2</a
      ><a name="10006"
      > </a
      ><a name="10007" href="StlcProp.html#10007" class="Bound"
      >x&#8712;t&#8322;</a
      ><a name="10011" class="Symbol"
      >)</a
      ><a name="10012"
      > </a
      ><a name="10013" class="Symbol"
      >(</a
      ><a name="10014" href="Stlc.html#19312" class="InductiveConstructor"
      >app</a
      ><a name="10017"
      > </a
      ><a name="10018" class="Symbol"
      >_</a
      ><a name="10019"
      >    </a
      ><a name="10023" href="StlcProp.html#10023" class="Bound"
      >t&#8322;&#8758;A</a
      ><a name="10027" class="Symbol"
      >)</a
      ><a name="10028"
      > </a
      ><a name="10029" class="Symbol"
      >=</a
      ><a name="10030"
      > </a
      ><a name="10031" href="StlcProp.html#8222" class="Function"
      >freeInCtxt</a
      ><a name="10041"
      > </a
      ><a name="10042" href="StlcProp.html#10007" class="Bound"
      >x&#8712;t&#8322;</a
      ><a name="10046"
      > </a
      ><a name="10047" href="StlcProp.html#10023" class="Bound"
      >t&#8322;&#8758;A</a
      ><a name="10051"
      >
</a
      ><a name="10052" href="StlcProp.html#8222" class="Function"
      >freeInCtxt</a
      ><a name="10062"
      > </a
      ><a name="10063" class="Symbol"
      >(</a
      ><a name="10064" href="StlcProp.html#7139" class="InductiveConstructor"
      >if1</a
      ><a name="10067"
      >  </a
      ><a name="10069" href="StlcProp.html#10069" class="Bound"
      >x&#8712;t&#8321;</a
      ><a name="10073" class="Symbol"
      >)</a
      ><a name="10074"
      > </a
      ><a name="10075" class="Symbol"
      >(</a
      ><a name="10076" href="Stlc.html#19564" class="InductiveConstructor Operator"
      >if</a
      ><a name="10078"
      > </a
      ><a name="10079" href="StlcProp.html#10079" class="Bound"
      >t&#8321;&#8758;A</a
      ><a name="10083"
      > </a
      ><a name="10084" href="Stlc.html#19564" class="InductiveConstructor Operator"
      >then</a
      ><a name="10088"
      > </a
      ><a name="10089" class="Symbol"
      >_</a
      ><a name="10090"
      >    </a
      ><a name="10094" href="Stlc.html#19564" class="InductiveConstructor Operator"
      >else</a
      ><a name="10098"
      > </a
      ><a name="10099" class="Symbol"
      >_</a
      ><a name="10100"
      >   </a
      ><a name="10103" class="Symbol"
      >)</a
      ><a name="10104"
      > </a
      ><a name="10105" class="Symbol"
      >=</a
      ><a name="10106"
      > </a
      ><a name="10107" href="StlcProp.html#8222" class="Function"
      >freeInCtxt</a
      ><a name="10117"
      > </a
      ><a name="10118" href="StlcProp.html#10069" class="Bound"
      >x&#8712;t&#8321;</a
      ><a name="10122"
      > </a
      ><a name="10123" href="StlcProp.html#10079" class="Bound"
      >t&#8321;&#8758;A</a
      ><a name="10127"
      >
</a
      ><a name="10128" href="StlcProp.html#8222" class="Function"
      >freeInCtxt</a
      ><a name="10138"
      > </a
      ><a name="10139" class="Symbol"
      >(</a
      ><a name="10140" href="StlcProp.html#7210" class="InductiveConstructor"
      >if2</a
      ><a name="10143"
      >  </a
      ><a name="10145" href="StlcProp.html#10145" class="Bound"
      >x&#8712;t&#8322;</a
      ><a name="10149" class="Symbol"
      >)</a
      ><a name="10150"
      > </a
      ><a name="10151" class="Symbol"
      >(</a
      ><a name="10152" href="Stlc.html#19564" class="InductiveConstructor Operator"
      >if</a
      ><a name="10154"
      > </a
      ><a name="10155" class="Symbol"
      >_</a
      ><a name="10156"
      >    </a
      ><a name="10160" href="Stlc.html#19564" class="InductiveConstructor Operator"
      >then</a
      ><a name="10164"
      > </a
      ><a name="10165" href="StlcProp.html#10165" class="Bound"
      >t&#8322;&#8758;A</a
      ><a name="10169"
      > </a
      ><a name="10170" href="Stlc.html#19564" class="InductiveConstructor Operator"
      >else</a
      ><a name="10174"
      > </a
      ><a name="10175" class="Symbol"
      >_</a
      ><a name="10176"
      >   </a
      ><a name="10179" class="Symbol"
      >)</a
      ><a name="10180"
      > </a
      ><a name="10181" class="Symbol"
      >=</a
      ><a name="10182"
      > </a
      ><a name="10183" href="StlcProp.html#8222" class="Function"
      >freeInCtxt</a
      ><a name="10193"
      > </a
      ><a name="10194" href="StlcProp.html#10145" class="Bound"
      >x&#8712;t&#8322;</a
      ><a name="10198"
      > </a
      ><a name="10199" href="StlcProp.html#10165" class="Bound"
      >t&#8322;&#8758;A</a
      ><a name="10203"
      >
</a
      ><a name="10204" href="StlcProp.html#8222" class="Function"
      >freeInCtxt</a
      ><a name="10214"
      > </a
      ><a name="10215" class="Symbol"
      >(</a
      ><a name="10216" href="StlcProp.html#7281" class="InductiveConstructor"
      >if3</a
      ><a name="10219"
      >  </a
      ><a name="10221" href="StlcProp.html#10221" class="Bound"
      >x&#8712;t&#8323;</a
      ><a name="10225" class="Symbol"
      >)</a
      ><a name="10226"
      > </a
      ><a name="10227" class="Symbol"
      >(</a
      ><a name="10228" href="Stlc.html#19564" class="InductiveConstructor Operator"
      >if</a
      ><a name="10230"
      > </a
      ><a name="10231" class="Symbol"
      >_</a
      ><a name="10232"
      >    </a
      ><a name="10236" href="Stlc.html#19564" class="InductiveConstructor Operator"
      >then</a
      ><a name="10240"
      > </a
      ><a name="10241" class="Symbol"
      >_</a
      ><a name="10242"
      >    </a
      ><a name="10246" href="Stlc.html#19564" class="InductiveConstructor Operator"
      >else</a
      ><a name="10250"
      > </a
      ><a name="10251" href="StlcProp.html#10251" class="Bound"
      >t&#8323;&#8758;A</a
      ><a name="10255" class="Symbol"
      >)</a
      ><a name="10256"
      > </a
      ><a name="10257" class="Symbol"
      >=</a
      ><a name="10258"
      > </a
      ><a name="10259" href="StlcProp.html#8222" class="Function"
      >freeInCtxt</a
      ><a name="10269"
      > </a
      ><a name="10270" href="StlcProp.html#10221" class="Bound"
      >x&#8712;t&#8323;</a
      ><a name="10274"
      > </a
      ><a name="10275" href="StlcProp.html#10251" class="Bound"
      >t&#8323;&#8758;A</a
      ><a name="10279"
      >
</a
      ><a name="10280" href="StlcProp.html#8222" class="Function"
      >freeInCtxt</a
      ><a name="10290"
      > </a
      ><a name="10295" class="Symbol"
      >(</a
      ><a name="10296" href="StlcProp.html#6970" class="InductiveConstructor"
      >abs</a
      ><a name="10299"
      > </a
      ><a name="10304" href="StlcProp.html#10304" class="Bound"
      >y&#8800;x</a
      ><a name="10307"
      > </a
      ><a name="10308" href="StlcProp.html#10308" class="Bound"
      >x&#8712;t</a
      ><a name="10311" class="Symbol"
      >)</a
      ><a name="10312"
      > </a
      ><a name="10313" class="Symbol"
      >(</a
      ><a name="10314" href="Stlc.html#19196" class="InductiveConstructor"
      >abs</a
      ><a name="10317"
      > </a
      ><a name="10318" href="StlcProp.html#10318" class="Bound"
      >t&#8758;B</a
      ><a name="10321" class="Symbol"
      >)</a
      ><a name="10322"
      >
    </a
      ><a name="10327" class="Keyword"
      >with</a
      ><a name="10331"
      > </a
      ><a name="10332" href="StlcProp.html#8222" class="Function"
      >freeInCtxt</a
      ><a name="10342"
      > </a
      ><a name="10343" href="StlcProp.html#10308" class="Bound"
      >x&#8712;t</a
      ><a name="10346"
      > </a
      ><a name="10347" href="StlcProp.html#10318" class="Bound"
      >t&#8758;B</a
      ><a name="10350"
      >
</a
      ><a name="10351" class="Symbol"
      >...</a
      ><a name="10354"
      > </a
      ><a name="10355" class="Symbol"
      >|</a
      ><a name="10356"
      > </a
      ><a name="10357" href="StlcProp.html#10357" class="Bound"
      >x&#8758;A</a
      ><a name="10360"
      >
    </a
      ><a name="10365" class="Keyword"
      >with</a
      ><a name="10369"
      > </a
      ><a name="10370" href="StlcProp.html#10301" class="Bound"
      >y</a
      ><a name="10371"
      > </a
      ><a name="10372" href="Maps.html#2297" class="Function Operator"
      >&#8799;</a
      ><a name="10373"
      > </a
      ><a name="10374" href="StlcProp.html#10292" class="Bound"
      >x</a
      ><a name="10375"
      >
</a
      ><a name="10376" class="Symbol"
      >...</a
      ><a name="10379"
      > </a
      ><a name="10380" class="Symbol"
      >|</a
      ><a name="10381"
      > </a
      ><a name="10382" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#520" class="InductiveConstructor"
      >yes</a
      ><a name="10385"
      > </a
      ><a name="10386" href="StlcProp.html#10386" class="Bound"
      >y=x</a
      ><a name="10389"
      > </a
      ><a name="10390" class="Symbol"
      >=</a
      ><a name="10391"
      > </a
      ><a name="10392" href="https://agda.github.io/agda-stdlib/Data.Empty.html#348" class="Function"
      >&#8869;-elim</a
      ><a name="10398"
      > </a
      ><a name="10399" class="Symbol"
      >(</a
      ><a name="10400" href="StlcProp.html#10304" class="Bound"
      >y&#8800;x</a
      ><a name="10403"
      > </a
      ><a name="10404" href="StlcProp.html#10386" class="Bound"
      >y=x</a
      ><a name="10407" class="Symbol"
      >)</a
      ><a name="10408"
      >
</a
      ><a name="10409" class="Symbol"
      >...</a
      ><a name="10412"
      > </a
      ><a name="10413" class="Symbol"
      >|</a
      ><a name="10414"
      > </a
      ><a name="10415" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#547" class="InductiveConstructor"
      >no</a
      ><a name="10417"
      >  </a
      ><a name="10419" class="Symbol"
      >_</a
      ><a name="10420"
      >   </a
      ><a name="10423" class="Symbol"
      >=</a
      ><a name="10424"
      > </a
      ><a name="10425" href="StlcProp.html#10357" class="Bound"
      >x&#8758;A</a
      >
{% endraw %}</pre>

Next, we'll need the fact that any term $$t$$ which is well typed in
the empty context is closed (it has no free variables).

#### Exercise: 2 stars, optional (∅⊢-closed)

<pre class="Agda">{% raw %}
<a name="10626" class="Keyword"
      >postulate</a
      ><a name="10635"
      >
  </a
      ><a name="10638" href="StlcProp.html#10638" class="Postulate"
      >&#8709;&#8866;-closed</a
      ><a name="10647"
      > </a
      ><a name="10648" class="Symbol"
      >:</a
      ><a name="10649"
      > </a
      ><a name="10650" class="Symbol"
      >&#8704;</a
      ><a name="10651"
      > </a
      ><a name="10658" class="Symbol"
      >&#8594;</a
      ><a name="10659"
      > </a
      ><a name="10660" href="Stlc.html#18127" class="Function"
      >&#8709;</a
      ><a name="10661"
      > </a
      ><a name="10662" href="Stlc.html#19059" class="Datatype Operator"
      >&#8866;</a
      ><a name="10663"
      > </a
      ><a name="10664" href="StlcProp.html#10653" class="Bound"
      >t</a
      ><a name="10665"
      > </a
      ><a name="10666" href="Stlc.html#19059" class="Datatype Operator"
      >&#8758;</a
      ><a name="10667"
      > </a
      ><a name="10668" href="StlcProp.html#10655" class="Bound"
      >A</a
      ><a name="10669"
      > </a
      ><a name="10670" class="Symbol"
      >&#8594;</a
      ><a name="10671"
      > </a
      ><a name="10672" href="StlcProp.html#7441" class="Function"
      >Closed</a
      ><a name="10678"
      > </a
      ><a name="10679" href="StlcProp.html#10653" class="Bound"
      >t</a
      >
{% endraw %}</pre>

<div class="hidden">
<pre class="Agda">{% raw %}
<a name="10727" href="StlcProp.html#10727" class="Function"
      >&#8709;&#8866;-closed&#8242;</a
      ><a name="10737"
      > </a
      ><a name="10738" class="Symbol"
      >:</a
      ><a name="10739"
      > </a
      ><a name="10740" class="Symbol"
      >&#8704;</a
      ><a name="10741"
      > </a
      ><a name="10748" class="Symbol"
      >&#8594;</a
      ><a name="10749"
      > </a
      ><a name="10750" href="Stlc.html#18127" class="Function"
      >&#8709;</a
      ><a name="10751"
      > </a
      ><a name="10752" href="Stlc.html#19059" class="Datatype Operator"
      >&#8866;</a
      ><a name="10753"
      > </a
      ><a name="10754" href="StlcProp.html#10743" class="Bound"
      >t</a
      ><a name="10755"
      > </a
      ><a name="10756" href="Stlc.html#19059" class="Datatype Operator"
      >&#8758;</a
      ><a name="10757"
      > </a
      ><a name="10758" href="StlcProp.html#10745" class="Bound"
      >A</a
      ><a name="10759"
      > </a
      ><a name="10760" class="Symbol"
      >&#8594;</a
      ><a name="10761"
      > </a
      ><a name="10762" href="StlcProp.html#7441" class="Function"
      >Closed</a
      ><a name="10768"
      > </a
      ><a name="10769" href="StlcProp.html#10743" class="Bound"
      >t</a
      ><a name="10770"
      >
</a
      ><a name="10771" href="StlcProp.html#10727" class="Function"
      >&#8709;&#8866;-closed&#8242;</a
      ><a name="10781"
      > </a
      ><a name="10782" class="Symbol"
      >(</a
      ><a name="10783" href="Stlc.html#19103" class="InductiveConstructor"
      >var</a
      ><a name="10786"
      > </a
      ><a name="10787" href="StlcProp.html#10787" class="Bound"
      >x</a
      ><a name="10788"
      > </a
      ><a name="10789" class="Symbol"
      >())</a
      ><a name="10792"
      >
</a
      ><a name="10793" href="StlcProp.html#10727" class="Function"
      >&#8709;&#8866;-closed&#8242;</a
      ><a name="10803"
      > </a
      ><a name="10804" class="Symbol"
      >(</a
      ><a name="10805" href="Stlc.html#19312" class="InductiveConstructor"
      >app</a
      ><a name="10808"
      > </a
      ><a name="10809" href="StlcProp.html#10809" class="Bound"
      >t&#8321;&#8758;A&#8658;B</a
      ><a name="10815"
      > </a
      ><a name="10816" href="StlcProp.html#10816" class="Bound"
      >t&#8322;&#8758;A</a
      ><a name="10820" class="Symbol"
      >)</a
      ><a name="10821"
      > </a
      ><a name="10822" class="Symbol"
      >(</a
      ><a name="10823" href="StlcProp.html#7031" class="InductiveConstructor"
      >app1</a
      ><a name="10827"
      > </a
      ><a name="10828" href="StlcProp.html#10828" class="Bound"
      >x&#8712;t&#8321;</a
      ><a name="10832" class="Symbol"
      >)</a
      ><a name="10833"
      > </a
      ><a name="10834" class="Symbol"
      >=</a
      ><a name="10835"
      > </a
      ><a name="10836" href="StlcProp.html#10727" class="Function"
      >&#8709;&#8866;-closed&#8242;</a
      ><a name="10846"
      > </a
      ><a name="10847" href="StlcProp.html#10809" class="Bound"
      >t&#8321;&#8758;A&#8658;B</a
      ><a name="10853"
      > </a
      ><a name="10854" href="StlcProp.html#10828" class="Bound"
      >x&#8712;t&#8321;</a
      ><a name="10858"
      >
</a
      ><a name="10859" href="StlcProp.html#10727" class="Function"
      >&#8709;&#8866;-closed&#8242;</a
      ><a name="10869"
      > </a
      ><a name="10870" class="Symbol"
      >(</a
      ><a name="10871" href="Stlc.html#19312" class="InductiveConstructor"
      >app</a
      ><a name="10874"
      > </a
      ><a name="10875" href="StlcProp.html#10875" class="Bound"
      >t&#8321;&#8758;A&#8658;B</a
      ><a name="10881"
      > </a
      ><a name="10882" href="StlcProp.html#10882" class="Bound"
      >t&#8322;&#8758;A</a
      ><a name="10886" class="Symbol"
      >)</a
      ><a name="10887"
      > </a
      ><a name="10888" class="Symbol"
      >(</a
      ><a name="10889" href="StlcProp.html#7085" class="InductiveConstructor"
      >app2</a
      ><a name="10893"
      > </a
      ><a name="10894" href="StlcProp.html#10894" class="Bound"
      >x&#8712;t&#8322;</a
      ><a name="10898" class="Symbol"
      >)</a
      ><a name="10899"
      > </a
      ><a name="10900" class="Symbol"
      >=</a
      ><a name="10901"
      > </a
      ><a name="10902" href="StlcProp.html#10727" class="Function"
      >&#8709;&#8866;-closed&#8242;</a
      ><a name="10912"
      > </a
      ><a name="10913" href="StlcProp.html#10882" class="Bound"
      >t&#8322;&#8758;A</a
      ><a name="10917"
      > </a
      ><a name="10918" href="StlcProp.html#10894" class="Bound"
      >x&#8712;t&#8322;</a
      ><a name="10922"
      >
</a
      ><a name="10923" href="StlcProp.html#10727" class="Function"
      >&#8709;&#8866;-closed&#8242;</a
      ><a name="10933"
      > </a
      ><a name="10934" href="Stlc.html#19446" class="InductiveConstructor"
      >true</a
      ><a name="10938"
      >  </a
      ><a name="10940" class="Symbol"
      >()</a
      ><a name="10942"
      >
</a
      ><a name="10943" href="StlcProp.html#10727" class="Function"
      >&#8709;&#8866;-closed&#8242;</a
      ><a name="10953"
      > </a
      ><a name="10954" href="Stlc.html#19505" class="InductiveConstructor"
      >false</a
      ><a name="10959"
      > </a
      ><a name="10960" class="Symbol"
      >()</a
      ><a name="10962"
      >
</a
      ><a name="10963" href="StlcProp.html#10727" class="Function"
      >&#8709;&#8866;-closed&#8242;</a
      ><a name="10973"
      > </a
      ><a name="10974" class="Symbol"
      >(</a
      ><a name="10975" href="Stlc.html#19564" class="InductiveConstructor Operator"
      >if</a
      ><a name="10977"
      > </a
      ><a name="10978" href="StlcProp.html#10978" class="Bound"
      >t&#8321;&#8758;bool</a
      ><a name="10985"
      > </a
      ><a name="10986" href="Stlc.html#19564" class="InductiveConstructor Operator"
      >then</a
      ><a name="10990"
      > </a
      ><a name="10991" href="StlcProp.html#10991" class="Bound"
      >t&#8322;&#8758;A</a
      ><a name="10995"
      > </a
      ><a name="10996" href="Stlc.html#19564" class="InductiveConstructor Operator"
      >else</a
      ><a name="11000"
      > </a
      ><a name="11001" href="StlcProp.html#11001" class="Bound"
      >t&#8323;&#8758;A</a
      ><a name="11005" class="Symbol"
      >)</a
      ><a name="11006"
      > </a
      ><a name="11007" class="Symbol"
      >(</a
      ><a name="11008" href="StlcProp.html#7139" class="InductiveConstructor"
      >if1</a
      ><a name="11011"
      > </a
      ><a name="11012" href="StlcProp.html#11012" class="Bound"
      >x&#8712;t&#8321;</a
      ><a name="11016" class="Symbol"
      >)</a
      ><a name="11017"
      > </a
      ><a name="11018" class="Symbol"
      >=</a
      ><a name="11019"
      > </a
      ><a name="11020" href="StlcProp.html#10727" class="Function"
      >&#8709;&#8866;-closed&#8242;</a
      ><a name="11030"
      > </a
      ><a name="11031" href="StlcProp.html#10978" class="Bound"
      >t&#8321;&#8758;bool</a
      ><a name="11038"
      > </a
      ><a name="11039" href="StlcProp.html#11012" class="Bound"
      >x&#8712;t&#8321;</a
      ><a name="11043"
      >
</a
      ><a name="11044" href="StlcProp.html#10727" class="Function"
      >&#8709;&#8866;-closed&#8242;</a
      ><a name="11054"
      > </a
      ><a name="11055" class="Symbol"
      >(</a
      ><a name="11056" href="Stlc.html#19564" class="InductiveConstructor Operator"
      >if</a
      ><a name="11058"
      > </a
      ><a name="11059" href="StlcProp.html#11059" class="Bound"
      >t&#8321;&#8758;bool</a
      ><a name="11066"
      > </a
      ><a name="11067" href="Stlc.html#19564" class="InductiveConstructor Operator"
      >then</a
      ><a name="11071"
      > </a
      ><a name="11072" href="StlcProp.html#11072" class="Bound"
      >t&#8322;&#8758;A</a
      ><a name="11076"
      > </a
      ><a name="11077" href="Stlc.html#19564" class="InductiveConstructor Operator"
      >else</a
      ><a name="11081"
      > </a
      ><a name="11082" href="StlcProp.html#11082" class="Bound"
      >t&#8323;&#8758;A</a
      ><a name="11086" class="Symbol"
      >)</a
      ><a name="11087"
      > </a
      ><a name="11088" class="Symbol"
      >(</a
      ><a name="11089" href="StlcProp.html#7210" class="InductiveConstructor"
      >if2</a
      ><a name="11092"
      > </a
      ><a name="11093" href="StlcProp.html#11093" class="Bound"
      >x&#8712;t&#8322;</a
      ><a name="11097" class="Symbol"
      >)</a
      ><a name="11098"
      > </a
      ><a name="11099" class="Symbol"
      >=</a
      ><a name="11100"
      > </a
      ><a name="11101" href="StlcProp.html#10727" class="Function"
      >&#8709;&#8866;-closed&#8242;</a
      ><a name="11111"
      > </a
      ><a name="11112" href="StlcProp.html#11072" class="Bound"
      >t&#8322;&#8758;A</a
      ><a name="11116"
      > </a
      ><a name="11117" href="StlcProp.html#11093" class="Bound"
      >x&#8712;t&#8322;</a
      ><a name="11121"
      >
</a
      ><a name="11122" href="StlcProp.html#10727" class="Function"
      >&#8709;&#8866;-closed&#8242;</a
      ><a name="11132"
      > </a
      ><a name="11133" class="Symbol"
      >(</a
      ><a name="11134" href="Stlc.html#19564" class="InductiveConstructor Operator"
      >if</a
      ><a name="11136"
      > </a
      ><a name="11137" href="StlcProp.html#11137" class="Bound"
      >t&#8321;&#8758;bool</a
      ><a name="11144"
      > </a
      ><a name="11145" href="Stlc.html#19564" class="InductiveConstructor Operator"
      >then</a
      ><a name="11149"
      > </a
      ><a name="11150" href="StlcProp.html#11150" class="Bound"
      >t&#8322;&#8758;A</a
      ><a name="11154"
      > </a
      ><a name="11155" href="Stlc.html#19564" class="InductiveConstructor Operator"
      >else</a
      ><a name="11159"
      > </a
      ><a name="11160" href="StlcProp.html#11160" class="Bound"
      >t&#8323;&#8758;A</a
      ><a name="11164" class="Symbol"
      >)</a
      ><a name="11165"
      > </a
      ><a name="11166" class="Symbol"
      >(</a
      ><a name="11167" href="StlcProp.html#7281" class="InductiveConstructor"
      >if3</a
      ><a name="11170"
      > </a
      ><a name="11171" href="StlcProp.html#11171" class="Bound"
      >x&#8712;t&#8323;</a
      ><a name="11175" class="Symbol"
      >)</a
      ><a name="11176"
      > </a
      ><a name="11177" class="Symbol"
      >=</a
      ><a name="11178"
      > </a
      ><a name="11179" href="StlcProp.html#10727" class="Function"
      >&#8709;&#8866;-closed&#8242;</a
      ><a name="11189"
      > </a
      ><a name="11190" href="StlcProp.html#11160" class="Bound"
      >t&#8323;&#8758;A</a
      ><a name="11194"
      > </a
      ><a name="11195" href="StlcProp.html#11171" class="Bound"
      >x&#8712;t&#8323;</a
      ><a name="11199"
      >
</a
      ><a name="11200" href="StlcProp.html#10727" class="Function"
      >&#8709;&#8866;-closed&#8242;</a
      ><a name="11210"
      > </a
      ><a name="11211" class="Symbol"
      >(</a
      ><a name="11212" href="Stlc.html#19196" class="InductiveConstructor"
      >abs</a
      ><a name="11215"
      > </a
      ><a name="11216" class="Symbol"
      >{</a
      ><a name="11217" class="Argument"
      >x</a
      ><a name="11218"
      > </a
      ><a name="11219" class="Symbol"
      >=</a
      ><a name="11220"
      > </a
      ><a name="11221" href="StlcProp.html#11221" class="Bound"
      >x</a
      ><a name="11222" class="Symbol"
      >}</a
      ><a name="11223"
      > </a
      ><a name="11224" href="StlcProp.html#11224" class="Bound"
      >t&#8242;&#8758;A</a
      ><a name="11228" class="Symbol"
      >)</a
      ><a name="11229"
      > </a
      ><a name="11234" class="Symbol"
      >(</a
      ><a name="11235" href="StlcProp.html#6970" class="InductiveConstructor"
      >abs</a
      ><a name="11238"
      > </a
      ><a name="11239" href="StlcProp.html#11239" class="Bound"
      >x&#8800;y</a
      ><a name="11242"
      > </a
      ><a name="11243" href="StlcProp.html#11243" class="Bound"
      >y&#8712;t&#8242;</a
      ><a name="11247" class="Symbol"
      >)</a
      ><a name="11248"
      > </a
      ><a name="11249" class="Keyword"
      >with</a
      ><a name="11253"
      > </a
      ><a name="11254" href="StlcProp.html#8222" class="Function"
      >freeInCtxt</a
      ><a name="11264"
      > </a
      ><a name="11265" href="StlcProp.html#11243" class="Bound"
      >y&#8712;t&#8242;</a
      ><a name="11269"
      > </a
      ><a name="11270" href="StlcProp.html#11224" class="Bound"
      >t&#8242;&#8758;A</a
      ><a name="11274"
      >
</a
      ><a name="11275" href="StlcProp.html#10727" class="Function"
      >&#8709;&#8866;-closed&#8242;</a
      ><a name="11285"
      > </a
      ><a name="11286" class="Symbol"
      >(</a
      ><a name="11287" class="InductiveConstructor"
      >abs</a
      ><a name="11290"
      > </a
      ><a name="11291" class="Symbol"
      >{</a
      ><a name="11292" class="Argument"
      >x</a
      ><a name="11293"
      > </a
      ><a name="11294" class="Symbol"
      >=</a
      ><a name="11295"
      > </a
      ><a name="11296" href="StlcProp.html#11296" class="Bound"
      >x</a
      ><a name="11297" class="Symbol"
      >}</a
      ><a name="11298"
      > </a
      ><a name="11299" href="StlcProp.html#11299" class="Bound"
      >t&#8242;&#8758;A</a
      ><a name="11303" class="Symbol"
      >)</a
      ><a name="11304"
      > </a
      ><a name="11309" class="Symbol"
      >(</a
      ><a name="11310" class="InductiveConstructor"
      >abs</a
      ><a name="11313"
      > </a
      ><a name="11314" href="StlcProp.html#11314" class="Bound"
      >x&#8800;y</a
      ><a name="11317"
      > </a
      ><a name="11318" href="StlcProp.html#11318" class="Bound"
      >y&#8712;t&#8242;</a
      ><a name="11322" class="Symbol"
      >)</a
      ><a name="11323"
      > </a
      ><a name="11324" class="Symbol"
      >|</a
      ><a name="11325"
      > </a
      ><a name="11326" href="StlcProp.html#11326" class="Bound"
      >A</a
      ><a name="11327"
      > </a
      ><a name="11328" href="https://agda.github.io/agda-stdlib/Data.Product.html#509" class="InductiveConstructor Operator"
      >,</a
      ><a name="11329"
      > </a
      ><a name="11330" href="StlcProp.html#11330" class="Bound"
      >y&#8758;A</a
      ><a name="11333"
      > </a
      ><a name="11334" class="Keyword"
      >with</a
      ><a name="11338"
      > </a
      ><a name="11339" href="StlcProp.html#11296" class="Bound"
      >x</a
      ><a name="11340"
      > </a
      ><a name="11341" href="Maps.html#2297" class="Function Operator"
      >&#8799;</a
      ><a name="11342"
      > </a
      ><a name="11343" href="StlcProp.html#11306" class="Bound"
      >y</a
      ><a name="11344"
      >
</a
      ><a name="11345" href="StlcProp.html#10727" class="Function"
      >&#8709;&#8866;-closed&#8242;</a
      ><a name="11355"
      > </a
      ><a name="11356" class="Symbol"
      >(</a
      ><a name="11357" class="InductiveConstructor"
      >abs</a
      ><a name="11360"
      > </a
      ><a name="11361" class="Symbol"
      >{</a
      ><a name="11362" class="Argument"
      >x</a
      ><a name="11363"
      > </a
      ><a name="11364" class="Symbol"
      >=</a
      ><a name="11365"
      > </a
      ><a name="11366" href="StlcProp.html#11366" class="Bound"
      >x</a
      ><a name="11367" class="Symbol"
      >}</a
      ><a name="11368"
      > </a
      ><a name="11369" href="StlcProp.html#11369" class="Bound"
      >t&#8242;&#8758;A</a
      ><a name="11373" class="Symbol"
      >)</a
      ><a name="11374"
      > </a
      ><a name="11379" class="Symbol"
      >(</a
      ><a name="11380" class="InductiveConstructor"
      >abs</a
      ><a name="11383"
      > </a
      ><a name="11384" href="StlcProp.html#11384" class="Bound"
      >x&#8800;y</a
      ><a name="11387"
      > </a
      ><a name="11388" href="StlcProp.html#11388" class="Bound"
      >y&#8712;t&#8242;</a
      ><a name="11392" class="Symbol"
      >)</a
      ><a name="11393"
      > </a
      ><a name="11394" class="Symbol"
      >|</a
      ><a name="11395"
      > </a
      ><a name="11396" href="StlcProp.html#11396" class="Bound"
      >A</a
      ><a name="11397"
      > </a
      ><a name="11398" href="https://agda.github.io/agda-stdlib/Data.Product.html#509" class="InductiveConstructor Operator"
      >,</a
      ><a name="11399"
      > </a
      ><a name="11400" href="StlcProp.html#11400" class="Bound"
      >y&#8758;A</a
      ><a name="11403"
      > </a
      ><a name="11404" class="Symbol"
      >|</a
      ><a name="11405"
      > </a
      ><a name="11406" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#520" class="InductiveConstructor"
      >yes</a
      ><a name="11409"
      > </a
      ><a name="11410" href="StlcProp.html#11410" class="Bound"
      >x=y</a
      ><a name="11413"
      > </a
      ><a name="11414" class="Symbol"
      >=</a
      ><a name="11415"
      > </a
      ><a name="11416" href="StlcProp.html#11384" class="Bound"
      >x&#8800;y</a
      ><a name="11419"
      > </a
      ><a name="11420" href="StlcProp.html#11410" class="Bound"
      >x=y</a
      ><a name="11423"
      >
</a
      ><a name="11424" href="StlcProp.html#10727" class="Function"
      >&#8709;&#8866;-closed&#8242;</a
      ><a name="11434"
      > </a
      ><a name="11435" class="Symbol"
      >(</a
      ><a name="11436" class="InductiveConstructor"
      >abs</a
      ><a name="11439"
      > </a
      ><a name="11440" class="Symbol"
      >{</a
      ><a name="11441" class="Argument"
      >x</a
      ><a name="11442"
      > </a
      ><a name="11443" class="Symbol"
      >=</a
      ><a name="11444"
      > </a
      ><a name="11445" href="StlcProp.html#11445" class="Bound"
      >x</a
      ><a name="11446" class="Symbol"
      >}</a
      ><a name="11447"
      > </a
      ><a name="11448" href="StlcProp.html#11448" class="Bound"
      >t&#8242;&#8758;A</a
      ><a name="11452" class="Symbol"
      >)</a
      ><a name="11453"
      > </a
      ><a name="11458" class="Symbol"
      >(</a
      ><a name="11459" class="InductiveConstructor"
      >abs</a
      ><a name="11462"
      > </a
      ><a name="11463" href="StlcProp.html#11463" class="Bound"
      >x&#8800;y</a
      ><a name="11466"
      > </a
      ><a name="11467" href="StlcProp.html#11467" class="Bound"
      >y&#8712;t&#8242;</a
      ><a name="11471" class="Symbol"
      >)</a
      ><a name="11472"
      > </a
      ><a name="11473" class="Symbol"
      >|</a
      ><a name="11474"
      > </a
      ><a name="11475" href="StlcProp.html#11475" class="Bound"
      >A</a
      ><a name="11476"
      > </a
      ><a name="11477" href="https://agda.github.io/agda-stdlib/Data.Product.html#509" class="InductiveConstructor Operator"
      >,</a
      ><a name="11478"
      > </a
      ><a name="11479" class="Symbol"
      >()</a
      ><a name="11481"
      >  </a
      ><a name="11483" class="Symbol"
      >|</a
      ><a name="11484"
      > </a
      ><a name="11485" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#547" class="InductiveConstructor"
      >no</a
      ><a name="11487"
      >  </a
      ><a name="11489" class="Symbol"
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
<a name="11877" href="StlcProp.html#11877" class="Function"
      >replaceCtxt</a
      ><a name="11888"
      > </a
      ><a name="11889" class="Symbol"
      >:</a
      ><a name="11890"
      > </a
      ><a name="11891" class="Symbol"
      >&#8704;</a
      ><a name="11892"
      > </a
      ><a name="11916" class="Symbol"
      >&#8594;</a
      ><a name="11917"
      > </a
      ><a name="11918" class="Symbol"
      >(&#8704;</a
      ><a name="11920"
      > </a
      ><a name="11925" class="Symbol"
      >&#8594;</a
      ><a name="11926"
      > </a
      ><a name="11927" href="StlcProp.html#11922" class="Bound"
      >x</a
      ><a name="11928"
      > </a
      ><a name="11929" href="StlcProp.html#6907" class="Datatype Operator"
      >FreeIn</a
      ><a name="11935"
      > </a
      ><a name="11936" href="StlcProp.html#11899" class="Bound"
      >t</a
      ><a name="11937"
      > </a
      ><a name="11938" class="Symbol"
      >&#8594;</a
      ><a name="11939"
      > </a
      ><a name="11940" href="StlcProp.html#11894" class="Bound"
      >&#915;</a
      ><a name="11941"
      > </a
      ><a name="11942" href="StlcProp.html#11922" class="Bound"
      >x</a
      ><a name="11943"
      > </a
      ><a name="11944" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="11945"
      > </a
      ><a name="11946" href="StlcProp.html#11896" class="Bound"
      >&#915;&#8242;</a
      ><a name="11948"
      > </a
      ><a name="11949" href="StlcProp.html#11922" class="Bound"
      >x</a
      ><a name="11950" class="Symbol"
      >)</a
      ><a name="11951"
      >
            </a
      ><a name="11964" class="Symbol"
      >&#8594;</a
      ><a name="11965"
      > </a
      ><a name="11966" href="StlcProp.html#11894" class="Bound"
      >&#915;</a
      ><a name="11967"
      >  </a
      ><a name="11969" href="Stlc.html#19059" class="Datatype Operator"
      >&#8866;</a
      ><a name="11970"
      > </a
      ><a name="11971" href="StlcProp.html#11899" class="Bound"
      >t</a
      ><a name="11972"
      > </a
      ><a name="11973" href="Stlc.html#19059" class="Datatype Operator"
      >&#8758;</a
      ><a name="11974"
      > </a
      ><a name="11975" href="StlcProp.html#11901" class="Bound"
      >A</a
      ><a name="11976"
      >
            </a
      ><a name="11989" class="Symbol"
      >&#8594;</a
      ><a name="11990"
      > </a
      ><a name="11991" href="StlcProp.html#11896" class="Bound"
      >&#915;&#8242;</a
      ><a name="11993"
      > </a
      ><a name="11994" href="Stlc.html#19059" class="Datatype Operator"
      >&#8866;</a
      ><a name="11995"
      > </a
      ><a name="11996" href="StlcProp.html#11899" class="Bound"
      >t</a
      ><a name="11997"
      > </a
      ><a name="11998" href="Stlc.html#19059" class="Datatype Operator"
      >&#8758;</a
      ><a name="11999"
      > </a
      ><a name="12000" href="StlcProp.html#11901" class="Bound"
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

<pre class="Agda">{% raw %}
<a name="14301" href="StlcProp.html#11877" class="Function"
      >replaceCtxt</a
      ><a name="14312"
      > </a
      ><a name="14313" href="StlcProp.html#14313" class="Bound"
      >f</a
      ><a name="14314"
      > </a
      ><a name="14315" class="Symbol"
      >(</a
      ><a name="14316" href="Stlc.html#19103" class="InductiveConstructor"
      >var</a
      ><a name="14319"
      > </a
      ><a name="14320" href="StlcProp.html#14320" class="Bound"
      >x</a
      ><a name="14321"
      > </a
      ><a name="14322" href="StlcProp.html#14322" class="Bound"
      >x&#8758;A</a
      ><a name="14325" class="Symbol"
      >)</a
      ><a name="14326"
      > </a
      ><a name="14327" class="Keyword"
      >rewrite</a
      ><a name="14334"
      > </a
      ><a name="14335" href="StlcProp.html#14313" class="Bound"
      >f</a
      ><a name="14336"
      > </a
      ><a name="14337" href="StlcProp.html#6946" class="InductiveConstructor"
      >var</a
      ><a name="14340"
      > </a
      ><a name="14341" class="Symbol"
      >=</a
      ><a name="14342"
      > </a
      ><a name="14343" href="Stlc.html#19103" class="InductiveConstructor"
      >var</a
      ><a name="14346"
      > </a
      ><a name="14347" href="StlcProp.html#14320" class="Bound"
      >x</a
      ><a name="14348"
      > </a
      ><a name="14349" href="StlcProp.html#14322" class="Bound"
      >x&#8758;A</a
      ><a name="14352"
      >
</a
      ><a name="14353" href="StlcProp.html#11877" class="Function"
      >replaceCtxt</a
      ><a name="14364"
      > </a
      ><a name="14365" href="StlcProp.html#14365" class="Bound"
      >f</a
      ><a name="14366"
      > </a
      ><a name="14367" class="Symbol"
      >(</a
      ><a name="14368" href="Stlc.html#19312" class="InductiveConstructor"
      >app</a
      ><a name="14371"
      > </a
      ><a name="14372" href="StlcProp.html#14372" class="Bound"
      >t&#8321;&#8758;A&#8658;B</a
      ><a name="14378"
      > </a
      ><a name="14379" href="StlcProp.html#14379" class="Bound"
      >t&#8322;&#8758;A</a
      ><a name="14383" class="Symbol"
      >)</a
      ><a name="14384"
      >
  </a
      ><a name="14387" class="Symbol"
      >=</a
      ><a name="14388"
      > </a
      ><a name="14389" href="Stlc.html#19312" class="InductiveConstructor"
      >app</a
      ><a name="14392"
      > </a
      ><a name="14393" class="Symbol"
      >(</a
      ><a name="14394" href="StlcProp.html#11877" class="Function"
      >replaceCtxt</a
      ><a name="14405"
      > </a
      ><a name="14406" class="Symbol"
      >(</a
      ><a name="14407" href="StlcProp.html#14365" class="Bound"
      >f</a
      ><a name="14408"
      > </a
      ><a name="14409" href="https://agda.github.io/agda-stdlib/Function.html#713" class="Function Operator"
      >&#8728;</a
      ><a name="14410"
      > </a
      ><a name="14411" href="StlcProp.html#7031" class="InductiveConstructor"
      >app1</a
      ><a name="14415" class="Symbol"
      >)</a
      ><a name="14416"
      > </a
      ><a name="14417" href="StlcProp.html#14372" class="Bound"
      >t&#8321;&#8758;A&#8658;B</a
      ><a name="14423" class="Symbol"
      >)</a
      ><a name="14424"
      > </a
      ><a name="14425" class="Symbol"
      >(</a
      ><a name="14426" href="StlcProp.html#11877" class="Function"
      >replaceCtxt</a
      ><a name="14437"
      > </a
      ><a name="14438" class="Symbol"
      >(</a
      ><a name="14439" href="StlcProp.html#14365" class="Bound"
      >f</a
      ><a name="14440"
      > </a
      ><a name="14441" href="https://agda.github.io/agda-stdlib/Function.html#713" class="Function Operator"
      >&#8728;</a
      ><a name="14442"
      > </a
      ><a name="14443" href="StlcProp.html#7085" class="InductiveConstructor"
      >app2</a
      ><a name="14447" class="Symbol"
      >)</a
      ><a name="14448"
      > </a
      ><a name="14449" href="StlcProp.html#14379" class="Bound"
      >t&#8322;&#8758;A</a
      ><a name="14453" class="Symbol"
      >)</a
      ><a name="14454"
      >
</a
      ><a name="14455" href="StlcProp.html#11877" class="Function"
      >replaceCtxt</a
      ><a name="14466"
      > </a
      ><a name="14476" href="StlcProp.html#14476" class="Bound"
      >f</a
      ><a name="14477"
      > </a
      ><a name="14478" class="Symbol"
      >(</a
      ><a name="14479" href="Stlc.html#19196" class="InductiveConstructor"
      >abs</a
      ><a name="14482"
      > </a
      ><a name="14505" href="StlcProp.html#14505" class="Bound"
      >t&#8242;&#8758;B</a
      ><a name="14509" class="Symbol"
      >)</a
      ><a name="14510"
      >
  </a
      ><a name="14513" class="Symbol"
      >=</a
      ><a name="14514"
      > </a
      ><a name="14515" href="Stlc.html#19196" class="InductiveConstructor"
      >abs</a
      ><a name="14518"
      > </a
      ><a name="14519" class="Symbol"
      >(</a
      ><a name="14520" href="StlcProp.html#11877" class="Function"
      >replaceCtxt</a
      ><a name="14531"
      > </a
      ><a name="14532" href="StlcProp.html#14553" class="Function"
      >f&#8242;</a
      ><a name="14534"
      > </a
      ><a name="14535" href="StlcProp.html#14505" class="Bound"
      >t&#8242;&#8758;B</a
      ><a name="14539" class="Symbol"
      >)</a
      ><a name="14540"
      >
  </a
      ><a name="14543" class="Keyword"
      >where</a
      ><a name="14548"
      >
    </a
      ><a name="14553" href="StlcProp.html#14553" class="Function"
      >f&#8242;</a
      ><a name="14555"
      > </a
      ><a name="14556" class="Symbol"
      >:</a
      ><a name="14557"
      > </a
      ><a name="14558" class="Symbol"
      >&#8704;</a
      ><a name="14559"
      > </a
      ><a name="14564" class="Symbol"
      >&#8594;</a
      ><a name="14565"
      > </a
      ><a name="14566" href="StlcProp.html#14561" class="Bound"
      >y</a
      ><a name="14567"
      > </a
      ><a name="14568" href="StlcProp.html#6907" class="Datatype Operator"
      >FreeIn</a
      ><a name="14574"
      > </a
      ><a name="14575" href="StlcProp.html#14501" class="Bound"
      >t&#8242;</a
      ><a name="14577"
      > </a
      ><a name="14578" class="Symbol"
      >&#8594;</a
      ><a name="14579"
      > </a
      ><a name="14580" class="Symbol"
      >(</a
      ><a name="14581" href="StlcProp.html#14468" class="Bound"
      >&#915;</a
      ><a name="14582"
      > </a
      ><a name="14583" href="Stlc.html#18158" class="Function Operator"
      >,</a
      ><a name="14584"
      > </a
      ><a name="14585" href="StlcProp.html#14489" class="Bound"
      >x</a
      ><a name="14586"
      > </a
      ><a name="14587" href="Stlc.html#18158" class="Function Operator"
      >&#8758;</a
      ><a name="14588"
      > </a
      ><a name="14589" href="StlcProp.html#14493" class="Bound"
      >A</a
      ><a name="14590" class="Symbol"
      >)</a
      ><a name="14591"
      > </a
      ><a name="14592" href="StlcProp.html#14561" class="Bound"
      >y</a
      ><a name="14593"
      > </a
      ><a name="14594" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="14595"
      > </a
      ><a name="14596" class="Symbol"
      >(</a
      ><a name="14597" href="StlcProp.html#14472" class="Bound"
      >&#915;&#8242;</a
      ><a name="14599"
      > </a
      ><a name="14600" href="Stlc.html#18158" class="Function Operator"
      >,</a
      ><a name="14601"
      > </a
      ><a name="14602" href="StlcProp.html#14489" class="Bound"
      >x</a
      ><a name="14603"
      > </a
      ><a name="14604" href="Stlc.html#18158" class="Function Operator"
      >&#8758;</a
      ><a name="14605"
      > </a
      ><a name="14606" href="StlcProp.html#14493" class="Bound"
      >A</a
      ><a name="14607" class="Symbol"
      >)</a
      ><a name="14608"
      > </a
      ><a name="14609" href="StlcProp.html#14561" class="Bound"
      >y</a
      ><a name="14610"
      >
    </a
      ><a name="14615" href="StlcProp.html#14553" class="Function"
      >f&#8242;</a
      ><a name="14617"
      > </a
      ><a name="14622" href="StlcProp.html#14622" class="Bound"
      >y&#8712;t&#8242;</a
      ><a name="14626"
      > </a
      ><a name="14627" class="Keyword"
      >with</a
      ><a name="14631"
      > </a
      ><a name="14632" href="StlcProp.html#14489" class="Bound"
      >x</a
      ><a name="14633"
      > </a
      ><a name="14634" href="Maps.html#2297" class="Function Operator"
      >&#8799;</a
      ><a name="14635"
      > </a
      ><a name="14636" href="StlcProp.html#14619" class="Bound"
      >y</a
      ><a name="14637"
      >
    </a
      ><a name="14642" class="Symbol"
      >...</a
      ><a name="14645"
      > </a
      ><a name="14646" class="Symbol"
      >|</a
      ><a name="14647"
      > </a
      ><a name="14648" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#520" class="InductiveConstructor"
      >yes</a
      ><a name="14651"
      > </a
      ><a name="14652" class="Symbol"
      >_</a
      ><a name="14653"
      >   </a
      ><a name="14656" class="Symbol"
      >=</a
      ><a name="14657"
      > </a
      ><a name="14658" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="14662"
      >
    </a
      ><a name="14667" class="Symbol"
      >...</a
      ><a name="14670"
      > </a
      ><a name="14671" class="Symbol"
      >|</a
      ><a name="14672"
      > </a
      ><a name="14673" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#547" class="InductiveConstructor"
      >no</a
      ><a name="14675"
      >  </a
      ><a name="14677" href="StlcProp.html#14677" class="Bound"
      >x&#8800;y</a
      ><a name="14680"
      > </a
      ><a name="14681" class="Symbol"
      >=</a
      ><a name="14682"
      > </a
      ><a name="14683" href="StlcProp.html#14476" class="Bound"
      >f</a
      ><a name="14684"
      > </a
      ><a name="14685" class="Symbol"
      >(</a
      ><a name="14686" href="StlcProp.html#6970" class="InductiveConstructor"
      >abs</a
      ><a name="14689"
      > </a
      ><a name="14690" href="StlcProp.html#14677" class="Bound"
      >x&#8800;y</a
      ><a name="14693"
      > </a
      ><a name="14694" href="StlcProp.html#14622" class="Bound"
      >y&#8712;t&#8242;</a
      ><a name="14698" class="Symbol"
      >)</a
      ><a name="14699"
      >
</a
      ><a name="14700" href="StlcProp.html#11877" class="Function"
      >replaceCtxt</a
      ><a name="14711"
      > </a
      ><a name="14712" class="Symbol"
      >_</a
      ><a name="14713"
      > </a
      ><a name="14714" href="Stlc.html#19446" class="InductiveConstructor"
      >true</a
      ><a name="14718"
      >  </a
      ><a name="14720" class="Symbol"
      >=</a
      ><a name="14721"
      > </a
      ><a name="14722" href="Stlc.html#19446" class="InductiveConstructor"
      >true</a
      ><a name="14726"
      >
</a
      ><a name="14727" href="StlcProp.html#11877" class="Function"
      >replaceCtxt</a
      ><a name="14738"
      > </a
      ><a name="14739" class="Symbol"
      >_</a
      ><a name="14740"
      > </a
      ><a name="14741" href="Stlc.html#19505" class="InductiveConstructor"
      >false</a
      ><a name="14746"
      > </a
      ><a name="14747" class="Symbol"
      >=</a
      ><a name="14748"
      > </a
      ><a name="14749" href="Stlc.html#19505" class="InductiveConstructor"
      >false</a
      ><a name="14754"
      >
</a
      ><a name="14755" href="StlcProp.html#11877" class="Function"
      >replaceCtxt</a
      ><a name="14766"
      > </a
      ><a name="14767" href="StlcProp.html#14767" class="Bound"
      >f</a
      ><a name="14768"
      > </a
      ><a name="14769" class="Symbol"
      >(</a
      ><a name="14770" href="Stlc.html#19564" class="InductiveConstructor Operator"
      >if</a
      ><a name="14772"
      > </a
      ><a name="14773" href="StlcProp.html#14773" class="Bound"
      >t&#8321;&#8758;bool</a
      ><a name="14780"
      > </a
      ><a name="14781" href="Stlc.html#19564" class="InductiveConstructor Operator"
      >then</a
      ><a name="14785"
      > </a
      ><a name="14786" href="StlcProp.html#14786" class="Bound"
      >t&#8322;&#8758;A</a
      ><a name="14790"
      > </a
      ><a name="14791" href="Stlc.html#19564" class="InductiveConstructor Operator"
      >else</a
      ><a name="14795"
      > </a
      ><a name="14796" href="StlcProp.html#14796" class="Bound"
      >t&#8323;&#8758;A</a
      ><a name="14800" class="Symbol"
      >)</a
      ><a name="14801"
      >
  </a
      ><a name="14804" class="Symbol"
      >=</a
      ><a name="14805"
      > </a
      ><a name="14806" href="Stlc.html#19564" class="InductiveConstructor Operator"
      >if</a
      ><a name="14808"
      >   </a
      ><a name="14811" href="StlcProp.html#11877" class="Function"
      >replaceCtxt</a
      ><a name="14822"
      > </a
      ><a name="14823" class="Symbol"
      >(</a
      ><a name="14824" href="StlcProp.html#14767" class="Bound"
      >f</a
      ><a name="14825"
      > </a
      ><a name="14826" href="https://agda.github.io/agda-stdlib/Function.html#713" class="Function Operator"
      >&#8728;</a
      ><a name="14827"
      > </a
      ><a name="14828" href="StlcProp.html#7139" class="InductiveConstructor"
      >if1</a
      ><a name="14831" class="Symbol"
      >)</a
      ><a name="14832"
      > </a
      ><a name="14833" href="StlcProp.html#14773" class="Bound"
      >t&#8321;&#8758;bool</a
      ><a name="14840"
      >
    </a
      ><a name="14845" href="Stlc.html#19564" class="InductiveConstructor Operator"
      >then</a
      ><a name="14849"
      > </a
      ><a name="14850" href="StlcProp.html#11877" class="Function"
      >replaceCtxt</a
      ><a name="14861"
      > </a
      ><a name="14862" class="Symbol"
      >(</a
      ><a name="14863" href="StlcProp.html#14767" class="Bound"
      >f</a
      ><a name="14864"
      > </a
      ><a name="14865" href="https://agda.github.io/agda-stdlib/Function.html#713" class="Function Operator"
      >&#8728;</a
      ><a name="14866"
      > </a
      ><a name="14867" href="StlcProp.html#7210" class="InductiveConstructor"
      >if2</a
      ><a name="14870" class="Symbol"
      >)</a
      ><a name="14871"
      > </a
      ><a name="14872" href="StlcProp.html#14786" class="Bound"
      >t&#8322;&#8758;A</a
      ><a name="14876"
      >
    </a
      ><a name="14881" href="Stlc.html#19564" class="InductiveConstructor Operator"
      >else</a
      ><a name="14885"
      > </a
      ><a name="14886" href="StlcProp.html#11877" class="Function"
      >replaceCtxt</a
      ><a name="14897"
      > </a
      ><a name="14898" class="Symbol"
      >(</a
      ><a name="14899" href="StlcProp.html#14767" class="Bound"
      >f</a
      ><a name="14900"
      > </a
      ><a name="14901" href="https://agda.github.io/agda-stdlib/Function.html#713" class="Function Operator"
      >&#8728;</a
      ><a name="14902"
      > </a
      ><a name="14903" href="StlcProp.html#7281" class="InductiveConstructor"
      >if3</a
      ><a name="14906" class="Symbol"
      >)</a
      ><a name="14907"
      > </a
      ><a name="14908" href="StlcProp.html#14796" class="Bound"
      >t&#8323;&#8758;A</a
      >
{% endraw %}</pre>

Now we come to the conceptual heart of the proof that reduction
preserves types---namely, the observation that _substitution_
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
<a name="15722" href="StlcProp.html#15722" class="Function"
      >[:=]-preserves-&#8866;</a
      ><a name="15738"
      > </a
      ><a name="15739" class="Symbol"
      >:</a
      ><a name="15740"
      > </a
      ><a name="15741" class="Symbol"
      >&#8704;</a
      ><a name="15742"
      > </a
      ><a name="15774" class="Symbol"
      >&#8594;</a
      ><a name="15775"
      > </a
      ><a name="15776" href="Stlc.html#18127" class="Function"
      >&#8709;</a
      ><a name="15777"
      > </a
      ><a name="15778" href="Stlc.html#19059" class="Datatype Operator"
      >&#8866;</a
      ><a name="15779"
      > </a
      ><a name="15780" href="StlcProp.html#15752" class="Bound"
      >v</a
      ><a name="15781"
      > </a
      ><a name="15782" href="Stlc.html#19059" class="Datatype Operator"
      >&#8758;</a
      ><a name="15783"
      > </a
      ><a name="15784" href="StlcProp.html#15748" class="Bound"
      >A</a
      ><a name="15785"
      >
                 </a
      ><a name="15803" class="Symbol"
      >&#8594;</a
      ><a name="15804"
      > </a
      ><a name="15805" href="StlcProp.html#15744" class="Bound"
      >&#915;</a
      ><a name="15806"
      > </a
      ><a name="15807" href="Stlc.html#18158" class="Function Operator"
      >,</a
      ><a name="15808"
      > </a
      ><a name="15809" href="StlcProp.html#15746" class="Bound"
      >x</a
      ><a name="15810"
      > </a
      ><a name="15811" href="Stlc.html#18158" class="Function Operator"
      >&#8758;</a
      ><a name="15812"
      > </a
      ><a name="15813" href="StlcProp.html#15748" class="Bound"
      >A</a
      ><a name="15814"
      > </a
      ><a name="15815" href="Stlc.html#19059" class="Datatype Operator"
      >&#8866;</a
      ><a name="15816"
      > </a
      ><a name="15817" href="StlcProp.html#15750" class="Bound"
      >t</a
      ><a name="15818"
      > </a
      ><a name="15819" href="Stlc.html#19059" class="Datatype Operator"
      >&#8758;</a
      ><a name="15820"
      > </a
      ><a name="15821" href="StlcProp.html#15754" class="Bound"
      >B</a
      ><a name="15822"
      >
                 </a
      ><a name="15840" class="Symbol"
      >&#8594;</a
      ><a name="15841"
      > </a
      ><a name="15842" href="StlcProp.html#15744" class="Bound"
      >&#915;</a
      ><a name="15843"
      > </a
      ><a name="15844" href="Stlc.html#18158" class="Function Operator"
      >,</a
      ><a name="15845"
      > </a
      ><a name="15846" href="StlcProp.html#15746" class="Bound"
      >x</a
      ><a name="15847"
      > </a
      ><a name="15848" href="Stlc.html#18158" class="Function Operator"
      >&#8758;</a
      ><a name="15849"
      > </a
      ><a name="15850" href="StlcProp.html#15748" class="Bound"
      >A</a
      ><a name="15851"
      > </a
      ><a name="15852" href="Stlc.html#19059" class="Datatype Operator"
      >&#8866;</a
      ><a name="15853"
      > </a
      ><a name="15854" href="Stlc.html#12129" class="Function Operator"
      >[</a
      ><a name="15855"
      > </a
      ><a name="15856" href="StlcProp.html#15746" class="Bound"
      >x</a
      ><a name="15857"
      > </a
      ><a name="15858" href="Stlc.html#12129" class="Function Operator"
      >:=</a
      ><a name="15860"
      > </a
      ><a name="15861" href="StlcProp.html#15752" class="Bound"
      >v</a
      ><a name="15862"
      > </a
      ><a name="15863" href="Stlc.html#12129" class="Function Operator"
      >]</a
      ><a name="15864"
      > </a
      ><a name="15865" href="StlcProp.html#15750" class="Bound"
      >t</a
      ><a name="15866"
      > </a
      ><a name="15867" href="Stlc.html#19059" class="Datatype Operator"
      >&#8758;</a
      ><a name="15868"
      > </a
      ><a name="15869" href="StlcProp.html#15754" class="Bound"
      >B</a
      >
{% endraw %}</pre>

One technical subtlety in the statement of the lemma is that
we assign $$v$$ the type $$U$$ in the _empty_ context---in other
words, we assume $$v$$ is closed.  This assumption considerably
simplifies the $$abs$$ case of the proof (compared to assuming
$$\Gamma \vdash v : U$$, which would be the other reasonable assumption
at this point) because the context invariance lemma then tells us
that $$v$$ has type $$U$$ in any context at all---we don't have to
worry about free variables in $$v$$ clashing with the variable being
introduced into the context by $$abs$$.

The substitution lemma can be viewed as a kind of "commutation"
property.  Intuitively, it says that substitution and typing can
be done in either order: we can either assign types to the terms
$$t$$ and $$v$$ separately (under suitable contexts) and then combine
them using substitution, or we can substitute first and then
assign a type to $$ $$x:=v$$ t $$---the result is the same either
way.

_Proof_: We show, by induction on $$t$$, that for all $$T$$ and
$$\Gamma$$, if $$\Gamma,x:U \vdash t : T$$ and $$\vdash v : U$$, then $$\Gamma
\vdash $$x:=v$$t : T$$.

  - If $$t$$ is a variable there are two cases to consider,
    depending on whether $$t$$ is $$x$$ or some other variable.

      - If $$t = x$$, then from the fact that $$\Gamma, x:U \vdash x :
        T$$ we conclude that $$U = T$$.  We must show that $$[x:=v]x =
        v$$ has type $$T$$ under $$\Gamma$$, given the assumption that
        $$v$$ has type $$U = T$$ under the empty context.  This
        follows from context invariance: if a closed term has type
        $$T$$ in the empty context, it has that type in any context.

      - If $$t$$ is some variable $$y$$ that is not equal to $$x$$, then
        we need only note that $$y$$ has the same type under $$\Gamma,
        x:U$$ as under $$\Gamma$$.

  - If $$t$$ is an abstraction $$\lambda y:t_{11}. t_{12}$$, then the IH tells us,
    for all $$\Gamma'$$ and $$T'$$, that if $$\Gamma',x:U \vdash t_{12}:T'$$
    and $$\vdash v:U$$, then $$\Gamma' \vdash [x:=v]t_{12}:T'$$.

    The substitution in the conclusion behaves differently
    depending on whether $$x$$ and $$y$$ are the same variable.

    First, suppose $$x = y$$.  Then, by the definition of
    substitution, $$[x:=v]t = t$$, so we just need to show $$\Gamma \vdash
    t : T$$.  But we know $$\Gamma,x:U \vdash t : T$$, and, since $$y$$
    does not appear free in $$\lambda y:t_{11}. t_{12}$$, the context invariance
    lemma yields $$\Gamma \vdash t : T$$.

    Second, suppose $$x \neq y$$.  We know $$\Gamma,x:U,y:t_{11} \vdash
    t_{12}:t_{12}$$ by inversion of the typing relation, from which
    $$\Gamma,y:t_{11},x:U \vdash t_{12}:t_{12}$$ follows by the context invariance
    lemma, so the IH applies, giving us $$\Gamma,y:t_{11} \vdash
    [x:=v]t_{12}:t_{12}$$.  By $$abs$$, $$\Gamma \vdash \lambda y:t_{11}.
    [x:=v]t_{12}:t_{11}\to t_{12}$$, and by the definition of substitution (noting
    that $$x \neq y$$), $$\Gamma \vdash \lambda y:t_{11}. [x:=v]t_{12}:t_{11}\to
    t_{12}$$ as required. 

  - If $$t$$ is an application $$t_1 t_2$$, the result follows
    straightforwardly from the definition of substitution and the
    induction hypotheses.

  - The remaining cases are similar to the application case.

One more technical note: This proof is a rare case where an
induction on terms, rather than typing derivations, yields a
simpler argument.  The reason for this is that the assumption
$$update Gamma x U \vdash t : T$$ is not completely generic, in the
sense that one of the "slots" in the typing relation---namely the
context---is not just a variable, and this means that Agda's
native induction tactic does not give us the induction hypothesis
that we want.  It is possible to work around this, but the needed
generalization is a little tricky.  The term $$t$$, on the other
hand, _is_ completely generic.

<pre class="Agda">{% raw %}
<a name="19806" href="StlcProp.html#15722" class="Function"
      >[:=]-preserves-&#8866;</a
      ><a name="19822"
      > </a
      ><a name="19831" href="StlcProp.html#19831" class="Bound"
      >v&#8758;A</a
      ><a name="19834"
      > </a
      ><a name="19835" class="Symbol"
      >(</a
      ><a name="19836" href="Stlc.html#19103" class="InductiveConstructor"
      >var</a
      ><a name="19839"
      > </a
      ><a name="19840" href="StlcProp.html#19840" class="Bound"
      >y</a
      ><a name="19841"
      > </a
      ><a name="19842" href="StlcProp.html#19842" class="Bound"
      >y&#8712;&#915;</a
      ><a name="19845" class="Symbol"
      >)</a
      ><a name="19846"
      > </a
      ><a name="19847" class="Keyword"
      >with</a
      ><a name="19851"
      > </a
      ><a name="19852" href="StlcProp.html#19828" class="Bound"
      >x</a
      ><a name="19853"
      > </a
      ><a name="19854" href="Maps.html#2297" class="Function Operator"
      >&#8799;</a
      ><a name="19855"
      > </a
      ><a name="19856" href="StlcProp.html#19840" class="Bound"
      >y</a
      ><a name="19857"
      >
</a
      ><a name="19858" class="Symbol"
      >...</a
      ><a name="19861"
      > </a
      ><a name="19862" class="Symbol"
      >|</a
      ><a name="19863"
      > </a
      ><a name="19864" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#520" class="InductiveConstructor"
      >yes</a
      ><a name="19867"
      > </a
      ><a name="19868" href="StlcProp.html#19868" class="Bound"
      >x=y</a
      ><a name="19871"
      > </a
      ><a name="19872" class="Symbol"
      >=</a
      ><a name="19873"
      > </a
      ><a name="19874" class="Symbol"
      >{!!}</a
      ><a name="19878"
      >
</a
      ><a name="19879" class="Symbol"
      >...</a
      ><a name="19882"
      > </a
      ><a name="19883" class="Symbol"
      >|</a
      ><a name="19884"
      > </a
      ><a name="19885" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#547" class="InductiveConstructor"
      >no</a
      ><a name="19887"
      >  </a
      ><a name="19889" href="StlcProp.html#19889" class="Bound"
      >x&#8800;y</a
      ><a name="19892"
      > </a
      ><a name="19893" class="Symbol"
      >=</a
      ><a name="19894"
      > </a
      ><a name="19895" class="Symbol"
      >{!!}</a
      ><a name="19899"
      >
</a
      ><a name="19900" href="StlcProp.html#15722" class="Function"
      >[:=]-preserves-&#8866;</a
      ><a name="19916"
      > </a
      ><a name="19917" href="StlcProp.html#19917" class="Bound"
      >v&#8758;A</a
      ><a name="19920"
      > </a
      ><a name="19921" class="Symbol"
      >(</a
      ><a name="19922" href="Stlc.html#19196" class="InductiveConstructor"
      >abs</a
      ><a name="19925"
      > </a
      ><a name="19926" href="StlcProp.html#19926" class="Bound"
      >t&#8242;&#8758;B</a
      ><a name="19930" class="Symbol"
      >)</a
      ><a name="19931"
      > </a
      ><a name="19932" class="Symbol"
      >=</a
      ><a name="19933"
      > </a
      ><a name="19934" class="Symbol"
      >{!!}</a
      ><a name="19938"
      >
</a
      ><a name="19939" href="StlcProp.html#15722" class="Function"
      >[:=]-preserves-&#8866;</a
      ><a name="19955"
      > </a
      ><a name="19956" href="StlcProp.html#19956" class="Bound"
      >v&#8758;A</a
      ><a name="19959"
      > </a
      ><a name="19960" class="Symbol"
      >(</a
      ><a name="19961" href="Stlc.html#19312" class="InductiveConstructor"
      >app</a
      ><a name="19964"
      > </a
      ><a name="19965" href="StlcProp.html#19965" class="Bound"
      >t&#8321;&#8758;A&#8658;B</a
      ><a name="19971"
      > </a
      ><a name="19972" href="StlcProp.html#19972" class="Bound"
      >t&#8322;&#8758;A</a
      ><a name="19976" class="Symbol"
      >)</a
      ><a name="19977"
      > </a
      ><a name="19978" class="Symbol"
      >=</a
      ><a name="19979"
      >
  </a
      ><a name="19982" href="Stlc.html#19312" class="InductiveConstructor"
      >app</a
      ><a name="19985"
      > </a
      ><a name="19986" class="Symbol"
      >(</a
      ><a name="19987" href="StlcProp.html#15722" class="Function"
      >[:=]-preserves-&#8866;</a
      ><a name="20003"
      > </a
      ><a name="20004" href="StlcProp.html#19956" class="Bound"
      >v&#8758;A</a
      ><a name="20007"
      > </a
      ><a name="20008" href="StlcProp.html#19965" class="Bound"
      >t&#8321;&#8758;A&#8658;B</a
      ><a name="20014" class="Symbol"
      >)</a
      ><a name="20015"
      > </a
      ><a name="20016" class="Symbol"
      >(</a
      ><a name="20017" href="StlcProp.html#15722" class="Function"
      >[:=]-preserves-&#8866;</a
      ><a name="20033"
      > </a
      ><a name="20034" href="StlcProp.html#19956" class="Bound"
      >v&#8758;A</a
      ><a name="20037"
      > </a
      ><a name="20038" href="StlcProp.html#19972" class="Bound"
      >t&#8322;&#8758;A</a
      ><a name="20042" class="Symbol"
      >)</a
      ><a name="20043"
      >
</a
      ><a name="20044" href="StlcProp.html#15722" class="Function"
      >[:=]-preserves-&#8866;</a
      ><a name="20060"
      > </a
      ><a name="20061" href="StlcProp.html#20061" class="Bound"
      >v&#8758;A</a
      ><a name="20064"
      > </a
      ><a name="20065" href="Stlc.html#19446" class="InductiveConstructor"
      >true</a
      ><a name="20069"
      >  </a
      ><a name="20071" class="Symbol"
      >=</a
      ><a name="20072"
      > </a
      ><a name="20073" href="Stlc.html#19446" class="InductiveConstructor"
      >true</a
      ><a name="20077"
      >
</a
      ><a name="20078" href="StlcProp.html#15722" class="Function"
      >[:=]-preserves-&#8866;</a
      ><a name="20094"
      > </a
      ><a name="20095" href="StlcProp.html#20095" class="Bound"
      >v&#8758;A</a
      ><a name="20098"
      > </a
      ><a name="20099" href="Stlc.html#19505" class="InductiveConstructor"
      >false</a
      ><a name="20104"
      > </a
      ><a name="20105" class="Symbol"
      >=</a
      ><a name="20106"
      > </a
      ><a name="20107" href="Stlc.html#19505" class="InductiveConstructor"
      >false</a
      ><a name="20112"
      >
</a
      ><a name="20113" href="StlcProp.html#15722" class="Function"
      >[:=]-preserves-&#8866;</a
      ><a name="20129"
      > </a
      ><a name="20130" href="StlcProp.html#20130" class="Bound"
      >v&#8758;A</a
      ><a name="20133"
      > </a
      ><a name="20134" class="Symbol"
      >(</a
      ><a name="20135" href="Stlc.html#19564" class="InductiveConstructor Operator"
      >if</a
      ><a name="20137"
      > </a
      ><a name="20138" href="StlcProp.html#20138" class="Bound"
      >t&#8321;&#8758;bool</a
      ><a name="20145"
      > </a
      ><a name="20146" href="Stlc.html#19564" class="InductiveConstructor Operator"
      >then</a
      ><a name="20150"
      > </a
      ><a name="20151" href="StlcProp.html#20151" class="Bound"
      >t&#8322;&#8758;B</a
      ><a name="20155"
      > </a
      ><a name="20156" href="Stlc.html#19564" class="InductiveConstructor Operator"
      >else</a
      ><a name="20160"
      > </a
      ><a name="20161" href="StlcProp.html#20161" class="Bound"
      >t&#8323;&#8758;B</a
      ><a name="20165" class="Symbol"
      >)</a
      ><a name="20166"
      > </a
      ><a name="20167" class="Symbol"
      >=</a
      ><a name="20168"
      >
  </a
      ><a name="20171" href="Stlc.html#19564" class="InductiveConstructor Operator"
      >if</a
      ><a name="20173"
      >   </a
      ><a name="20176" href="StlcProp.html#15722" class="Function"
      >[:=]-preserves-&#8866;</a
      ><a name="20192"
      > </a
      ><a name="20193" href="StlcProp.html#20130" class="Bound"
      >v&#8758;A</a
      ><a name="20196"
      > </a
      ><a name="20197" href="StlcProp.html#20138" class="Bound"
      >t&#8321;&#8758;bool</a
      ><a name="20204"
      >
  </a
      ><a name="20207" href="Stlc.html#19564" class="InductiveConstructor Operator"
      >then</a
      ><a name="20211"
      > </a
      ><a name="20212" href="StlcProp.html#15722" class="Function"
      >[:=]-preserves-&#8866;</a
      ><a name="20228"
      > </a
      ><a name="20229" href="StlcProp.html#20130" class="Bound"
      >v&#8758;A</a
      ><a name="20232"
      > </a
      ><a name="20233" href="StlcProp.html#20151" class="Bound"
      >t&#8322;&#8758;B</a
      ><a name="20237"
      >
  </a
      ><a name="20240" href="Stlc.html#19564" class="InductiveConstructor Operator"
      >else</a
      ><a name="20244"
      > </a
      ><a name="20245" href="StlcProp.html#15722" class="Function"
      >[:=]-preserves-&#8866;</a
      ><a name="20261"
      > </a
      ><a name="20262" href="StlcProp.html#20130" class="Bound"
      >v&#8758;A</a
      ><a name="20265"
      > </a
      ><a name="20266" href="StlcProp.html#20161" class="Bound"
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
