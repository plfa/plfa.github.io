---
title     : "StlcProp: Properties of STLC"
layout    : page
permalink : /StlcProp
---

#  Properties of STLC

In this chapter, we develop the fundamental theory of the Simply
Typed Lambda Calculus -- in particular, the type safety
theorem.

<div class="foldable">
<pre class="Agda">{% raw %}
<a name="282" class="Keyword"
      >open</a
      ><a name="286"
      > </a
      ><a name="287" class="Keyword"
      >import</a
      ><a name="293"
      > </a
      ><a name="294" href="https://agda.github.io/agda-stdlib/Function.html#1" class="Module"
      >Function</a
      ><a name="302"
      > </a
      ><a name="303" class="Keyword"
      >using</a
      ><a name="308"
      > </a
      ><a name="309" class="Symbol"
      >(</a
      ><a name="310" href="https://agda.github.io/agda-stdlib/Function.html#713" class="Function Operator"
      >_&#8728;_</a
      ><a name="313" class="Symbol"
      >)</a
      ><a name="314"
      >
</a
      ><a name="315" class="Keyword"
      >open</a
      ><a name="319"
      > </a
      ><a name="320" class="Keyword"
      >import</a
      ><a name="326"
      > </a
      ><a name="327" href="https://agda.github.io/agda-stdlib/Data.Empty.html#1" class="Module"
      >Data.Empty</a
      ><a name="337"
      > </a
      ><a name="338" class="Keyword"
      >using</a
      ><a name="343"
      > </a
      ><a name="344" class="Symbol"
      >(</a
      ><a name="345" href="https://agda.github.io/agda-stdlib/Data.Empty.html#243" class="Datatype"
      >&#8869;</a
      ><a name="346" class="Symbol"
      >;</a
      ><a name="347"
      > </a
      ><a name="348" href="https://agda.github.io/agda-stdlib/Data.Empty.html#348" class="Function"
      >&#8869;-elim</a
      ><a name="354" class="Symbol"
      >)</a
      ><a name="355"
      >
</a
      ><a name="356" class="Keyword"
      >open</a
      ><a name="360"
      > </a
      ><a name="361" class="Keyword"
      >import</a
      ><a name="367"
      > </a
      ><a name="368" href="https://agda.github.io/agda-stdlib/Data.Maybe.html#1" class="Module"
      >Data.Maybe</a
      ><a name="378"
      > </a
      ><a name="379" class="Keyword"
      >using</a
      ><a name="384"
      > </a
      ><a name="385" class="Symbol"
      >(</a
      ><a name="386" href="https://agda.github.io/agda-stdlib/Data.Maybe.Base.html#335" class="Datatype"
      >Maybe</a
      ><a name="391" class="Symbol"
      >;</a
      ><a name="392"
      > </a
      ><a name="393" href="https://agda.github.io/agda-stdlib/Data.Maybe.html#1527" class="InductiveConstructor"
      >just</a
      ><a name="397" class="Symbol"
      >;</a
      ><a name="398"
      > </a
      ><a name="399" href="https://agda.github.io/agda-stdlib/Data.Maybe.html#1588" class="InductiveConstructor"
      >nothing</a
      ><a name="406" class="Symbol"
      >)</a
      ><a name="407"
      >
</a
      ><a name="408" class="Keyword"
      >open</a
      ><a name="412"
      > </a
      ><a name="413" class="Keyword"
      >import</a
      ><a name="419"
      > </a
      ><a name="420" href="https://agda.github.io/agda-stdlib/Data.Product.html#1" class="Module"
      >Data.Product</a
      ><a name="432"
      > </a
      ><a name="433" class="Keyword"
      >using</a
      ><a name="438"
      > </a
      ><a name="439" class="Symbol"
      >(</a
      ><a name="440" href="https://agda.github.io/agda-stdlib/Data.Product.html#823" class="Function"
      >&#8707;</a
      ><a name="441" class="Symbol"
      >;</a
      ><a name="442"
      > </a
      ><a name="443" href="https://agda.github.io/agda-stdlib/Data.Product.html#949" class="Function"
      >&#8707;&#8322;</a
      ><a name="445" class="Symbol"
      >;</a
      ><a name="446"
      > </a
      ><a name="447" href="https://agda.github.io/agda-stdlib/Data.Product.html#509" class="InductiveConstructor Operator"
      >_,_</a
      ><a name="450" class="Symbol"
      >;</a
      ><a name="451"
      > </a
      ><a name="452" href="https://agda.github.io/agda-stdlib/Data.Product.html#1621" class="Function Operator"
      >,_</a
      ><a name="454" class="Symbol"
      >)</a
      ><a name="455"
      >
</a
      ><a name="456" class="Keyword"
      >open</a
      ><a name="460"
      > </a
      ><a name="461" class="Keyword"
      >import</a
      ><a name="467"
      > </a
      ><a name="468" href="https://agda.github.io/agda-stdlib/Data.Sum.html#1" class="Module"
      >Data.Sum</a
      ><a name="476"
      > </a
      ><a name="477" class="Keyword"
      >using</a
      ><a name="482"
      > </a
      ><a name="483" class="Symbol"
      >(</a
      ><a name="484" href="https://agda.github.io/agda-stdlib/Data.Sum.html#433" class="Datatype Operator"
      >_&#8846;_</a
      ><a name="487" class="Symbol"
      >;</a
      ><a name="488"
      > </a
      ><a name="489" href="https://agda.github.io/agda-stdlib/Data.Sum.html#489" class="InductiveConstructor"
      >inj&#8321;</a
      ><a name="493" class="Symbol"
      >;</a
      ><a name="494"
      > </a
      ><a name="495" href="https://agda.github.io/agda-stdlib/Data.Sum.html#514" class="InductiveConstructor"
      >inj&#8322;</a
      ><a name="499" class="Symbol"
      >)</a
      ><a name="500"
      >
</a
      ><a name="501" class="Keyword"
      >open</a
      ><a name="505"
      > </a
      ><a name="506" class="Keyword"
      >import</a
      ><a name="512"
      > </a
      ><a name="513" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#1" class="Module"
      >Relation.Nullary</a
      ><a name="529"
      > </a
      ><a name="530" class="Keyword"
      >using</a
      ><a name="535"
      > </a
      ><a name="536" class="Symbol"
      >(</a
      ><a name="537" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#414" class="Function Operator"
      >&#172;_</a
      ><a name="539" class="Symbol"
      >;</a
      ><a name="540"
      > </a
      ><a name="541" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#484" class="Datatype"
      >Dec</a
      ><a name="544" class="Symbol"
      >;</a
      ><a name="545"
      > </a
      ><a name="546" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#520" class="InductiveConstructor"
      >yes</a
      ><a name="549" class="Symbol"
      >;</a
      ><a name="550"
      > </a
      ><a name="551" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#547" class="InductiveConstructor"
      >no</a
      ><a name="553" class="Symbol"
      >)</a
      ><a name="554"
      >
</a
      ><a name="555" class="Keyword"
      >open</a
      ><a name="559"
      > </a
      ><a name="560" class="Keyword"
      >import</a
      ><a name="566"
      > </a
      ><a name="567" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#1" class="Module"
      >Relation.Binary.PropositionalEquality</a
      ><a name="604"
      > </a
      ><a name="605" class="Keyword"
      >using</a
      ><a name="610"
      > </a
      ><a name="611" class="Symbol"
      >(</a
      ><a name="612" href="Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >_&#8801;_</a
      ><a name="615" class="Symbol"
      >;</a
      ><a name="616"
      > </a
      ><a name="617" href="https://agda.github.io/agda-stdlib/Relation.Binary.Core.html#4493" class="Function Operator"
      >_&#8802;_</a
      ><a name="620" class="Symbol"
      >;</a
      ><a name="621"
      > </a
      ><a name="622" href="Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="626" class="Symbol"
      >)</a
      ><a name="627"
      >
</a
      ><a name="628" class="Keyword"
      >open</a
      ><a name="632"
      > </a
      ><a name="633" class="Keyword"
      >import</a
      ><a name="639"
      > </a
      ><a name="640" class="Module"
      >Maps</a
      ><a name="644"
      >
</a
      ><a name="645" class="Keyword"
      >open</a
      ><a name="649"
      > </a
      ><a name="650" class="Keyword"
      >import</a
      ><a name="656"
      > </a
      ><a name="657" class="Module"
      >Stlc</a
      >
{% endraw %}</pre>
</div>

## Canonical Forms

As we saw for the simple calculus in the [Stlc](Stlc.html) chapter, the
first step in establishing basic properties of reduction and types
is to identify the possible _canonical forms_ (i.e., well-typed
closed values) belonging to each type.  For $$bool$$, these are the boolean
values $$true$$ and $$false$$.  For arrow types, the canonical forms
are lambda-abstractions.

<pre class="Agda">{% raw %}
<a name="1088" href="StlcProp.html#1088" class="Function"
      >CanonicalForms</a
      ><a name="1102"
      > </a
      ><a name="1103" class="Symbol"
      >:</a
      ><a name="1104"
      > </a
      ><a name="1105" href="Stlc.html#5543" class="Datatype"
      >Term</a
      ><a name="1109"
      > </a
      ><a name="1110" class="Symbol"
      >&#8594;</a
      ><a name="1111"
      > </a
      ><a name="1112" href="Stlc.html#5428" class="Datatype"
      >Type</a
      ><a name="1116"
      > </a
      ><a name="1117" class="Symbol"
      >&#8594;</a
      ><a name="1118"
      > </a
      ><a name="1119" class="PrimitiveType"
      >Set</a
      ><a name="1122"
      >
</a
      ><a name="1123" href="StlcProp.html#1088" class="Function"
      >CanonicalForms</a
      ><a name="1137"
      > </a
      ><a name="1138" href="StlcProp.html#1138" class="Bound"
      >t</a
      ><a name="1139"
      > </a
      ><a name="1140" href="Stlc.html#5447" class="InductiveConstructor"
      >bool</a
      ><a name="1144"
      >    </a
      ><a name="1148" class="Symbol"
      >=</a
      ><a name="1149"
      > </a
      ><a name="1150" href="StlcProp.html#1138" class="Bound"
      >t</a
      ><a name="1151"
      > </a
      ><a name="1152" href="Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="1153"
      > </a
      ><a name="1154" href="Stlc.html#5645" class="InductiveConstructor"
      >true</a
      ><a name="1158"
      > </a
      ><a name="1159" href="https://agda.github.io/agda-stdlib/Data.Sum.html#433" class="Datatype Operator"
      >&#8846;</a
      ><a name="1160"
      > </a
      ><a name="1161" href="StlcProp.html#1138" class="Bound"
      >t</a
      ><a name="1162"
      > </a
      ><a name="1163" href="Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="1164"
      > </a
      ><a name="1165" href="Stlc.html#5660" class="InductiveConstructor"
      >false</a
      ><a name="1170"
      >
</a
      ><a name="1171" href="StlcProp.html#1088" class="Function"
      >CanonicalForms</a
      ><a name="1185"
      > </a
      ><a name="1186" href="StlcProp.html#1186" class="Bound"
      >t</a
      ><a name="1187"
      > </a
      ><a name="1188" class="Symbol"
      >(</a
      ><a name="1189" href="StlcProp.html#1189" class="Bound"
      >A</a
      ><a name="1190"
      > </a
      ><a name="1191" href="Stlc.html#5461" class="InductiveConstructor Operator"
      >&#8658;</a
      ><a name="1192"
      > </a
      ><a name="1193" href="StlcProp.html#1193" class="Bound"
      >B</a
      ><a name="1194" class="Symbol"
      >)</a
      ><a name="1195"
      > </a
      ><a name="1196" class="Symbol"
      >=</a
      ><a name="1197"
      > </a
      ><a name="1198" href="https://agda.github.io/agda-stdlib/Data.Product.html#949" class="Function"
      >&#8707;&#8322;</a
      ><a name="1200"
      > </a
      ><a name="1201" class="Symbol"
      >&#955;</a
      ><a name="1202"
      > </a
      ><a name="1203" href="StlcProp.html#1203" class="Bound"
      >x</a
      ><a name="1204"
      > </a
      ><a name="1205" href="StlcProp.html#1205" class="Bound"
      >t&#8242;</a
      ><a name="1207"
      > </a
      ><a name="1208" class="Symbol"
      >&#8594;</a
      ><a name="1209"
      > </a
      ><a name="1210" href="StlcProp.html#1186" class="Bound"
      >t</a
      ><a name="1211"
      > </a
      ><a name="1212" href="Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="1213"
      > </a
      ><a name="1214" href="Stlc.html#5611" class="InductiveConstructor"
      >abs</a
      ><a name="1217"
      > </a
      ><a name="1218" href="StlcProp.html#1203" class="Bound"
      >x</a
      ><a name="1219"
      > </a
      ><a name="1220" href="StlcProp.html#1189" class="Bound"
      >A</a
      ><a name="1221"
      > </a
      ><a name="1222" href="StlcProp.html#1205" class="Bound"
      >t&#8242;</a
      ><a name="1224"
      >

</a
      ><a name="1226" href="StlcProp.html#1226" class="Function"
      >canonicalForms</a
      ><a name="1240"
      > </a
      ><a name="1241" class="Symbol"
      >:</a
      ><a name="1242"
      > </a
      ><a name="1243" class="Symbol"
      >&#8704;</a
      ><a name="1244"
      > </a
      ><a name="1251" class="Symbol"
      >&#8594;</a
      ><a name="1252"
      > </a
      ><a name="1253" href="Stlc.html#18168" class="Function"
      >&#8709;</a
      ><a name="1254"
      > </a
      ><a name="1255" href="Stlc.html#19100" class="Datatype Operator"
      >&#8866;</a
      ><a name="1256"
      > </a
      ><a name="1257" href="StlcProp.html#1246" class="Bound"
      >t</a
      ><a name="1258"
      > </a
      ><a name="1259" href="Stlc.html#19100" class="Datatype Operator"
      >&#8758;</a
      ><a name="1260"
      > </a
      ><a name="1261" href="StlcProp.html#1248" class="Bound"
      >A</a
      ><a name="1262"
      > </a
      ><a name="1263" class="Symbol"
      >&#8594;</a
      ><a name="1264"
      > </a
      ><a name="1265" href="Stlc.html#8950" class="Datatype"
      >Value</a
      ><a name="1270"
      > </a
      ><a name="1271" href="StlcProp.html#1246" class="Bound"
      >t</a
      ><a name="1272"
      > </a
      ><a name="1273" class="Symbol"
      >&#8594;</a
      ><a name="1274"
      > </a
      ><a name="1275" href="StlcProp.html#1088" class="Function"
      >CanonicalForms</a
      ><a name="1289"
      > </a
      ><a name="1290" href="StlcProp.html#1246" class="Bound"
      >t</a
      ><a name="1291"
      > </a
      ><a name="1292" href="StlcProp.html#1248" class="Bound"
      >A</a
      ><a name="1293"
      >
</a
      ><a name="1294" href="StlcProp.html#1226" class="Function"
      >canonicalForms</a
      ><a name="1308"
      > </a
      ><a name="1309" class="Symbol"
      >(</a
      ><a name="1310" href="Stlc.html#19237" class="InductiveConstructor"
      >abs</a
      ><a name="1313"
      > </a
      ><a name="1314" href="StlcProp.html#1314" class="Bound"
      >t&#8242;</a
      ><a name="1316" class="Symbol"
      >)</a
      ><a name="1317"
      > </a
      ><a name="1318" href="Stlc.html#8977" class="InductiveConstructor"
      >abs</a
      ><a name="1321"
      >   </a
      ><a name="1324" class="Symbol"
      >=</a
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
      ><a name="1330" class="Symbol"
      >_</a
      ><a name="1331"
      > </a
      ><a name="1332" href="https://agda.github.io/agda-stdlib/Data.Product.html#509" class="InductiveConstructor Operator"
      >,</a
      ><a name="1333"
      > </a
      ><a name="1334" href="Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="1338"
      >
</a
      ><a name="1339" href="StlcProp.html#1226" class="Function"
      >canonicalForms</a
      ><a name="1353"
      > </a
      ><a name="1354" href="Stlc.html#19487" class="InductiveConstructor"
      >true</a
      ><a name="1358"
      >     </a
      ><a name="1363" href="Stlc.html#9025" class="InductiveConstructor"
      >true</a
      ><a name="1367"
      >  </a
      ><a name="1369" class="Symbol"
      >=</a
      ><a name="1370"
      > </a
      ><a name="1371" href="https://agda.github.io/agda-stdlib/Data.Sum.html#489" class="InductiveConstructor"
      >inj&#8321;</a
      ><a name="1375"
      > </a
      ><a name="1376" href="Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="1380"
      >
</a
      ><a name="1381" href="StlcProp.html#1226" class="Function"
      >canonicalForms</a
      ><a name="1395"
      > </a
      ><a name="1396" href="Stlc.html#19546" class="InductiveConstructor"
      >false</a
      ><a name="1401"
      >    </a
      ><a name="1405" href="Stlc.html#9046" class="InductiveConstructor"
      >false</a
      ><a name="1410"
      > </a
      ><a name="1411" class="Symbol"
      >=</a
      ><a name="1412"
      > </a
      ><a name="1413" href="https://agda.github.io/agda-stdlib/Data.Sum.html#514" class="InductiveConstructor"
      >inj&#8322;</a
      ><a name="1417"
      > </a
      ><a name="1418" href="Agda.Builtin.Equality.html#140" class="InductiveConstructor"
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
<a name="1801" href="StlcProp.html#1801" class="Function"
      >progress</a
      ><a name="1809"
      > </a
      ><a name="1810" class="Symbol"
      >:</a
      ><a name="1811"
      > </a
      ><a name="1812" class="Symbol"
      >&#8704;</a
      ><a name="1813"
      > </a
      ><a name="1820" class="Symbol"
      >&#8594;</a
      ><a name="1821"
      > </a
      ><a name="1822" href="Stlc.html#18168" class="Function"
      >&#8709;</a
      ><a name="1823"
      > </a
      ><a name="1824" href="Stlc.html#19100" class="Datatype Operator"
      >&#8866;</a
      ><a name="1825"
      > </a
      ><a name="1826" href="StlcProp.html#1815" class="Bound"
      >t</a
      ><a name="1827"
      > </a
      ><a name="1828" href="Stlc.html#19100" class="Datatype Operator"
      >&#8758;</a
      ><a name="1829"
      > </a
      ><a name="1830" href="StlcProp.html#1817" class="Bound"
      >A</a
      ><a name="1831"
      > </a
      ><a name="1832" class="Symbol"
      >&#8594;</a
      ><a name="1833"
      > </a
      ><a name="1834" href="Stlc.html#8950" class="Datatype"
      >Value</a
      ><a name="1839"
      > </a
      ><a name="1840" href="StlcProp.html#1815" class="Bound"
      >t</a
      ><a name="1841"
      > </a
      ><a name="1842" href="https://agda.github.io/agda-stdlib/Data.Sum.html#433" class="Datatype Operator"
      >&#8846;</a
      ><a name="1843"
      > </a
      ><a name="1844" href="https://agda.github.io/agda-stdlib/Data.Product.html#823" class="Function"
      >&#8707;</a
      ><a name="1845"
      > </a
      ><a name="1846" class="Symbol"
      >&#955;</a
      ><a name="1847"
      > </a
      ><a name="1848" href="StlcProp.html#1848" class="Bound"
      >t&#8242;</a
      ><a name="1850"
      > </a
      ><a name="1851" class="Symbol"
      >&#8594;</a
      ><a name="1852"
      > </a
      ><a name="1853" href="StlcProp.html#1815" class="Bound"
      >t</a
      ><a name="1854"
      > </a
      ><a name="1855" href="Stlc.html#15086" class="Datatype Operator"
      >==&gt;</a
      ><a name="1858"
      > </a
      ><a name="1859" href="StlcProp.html#1848" class="Bound"
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
<a name="3560" href="StlcProp.html#1801" class="Function"
      >progress</a
      ><a name="3568"
      > </a
      ><a name="3569" class="Symbol"
      >(</a
      ><a name="3570" href="Stlc.html#19144" class="InductiveConstructor"
      >var</a
      ><a name="3573"
      > </a
      ><a name="3574" href="StlcProp.html#3574" class="Bound"
      >x</a
      ><a name="3575"
      > </a
      ><a name="3576" class="Symbol"
      >())</a
      ><a name="3579"
      >
</a
      ><a name="3580" href="StlcProp.html#1801" class="Function"
      >progress</a
      ><a name="3588"
      > </a
      ><a name="3589" href="Stlc.html#19487" class="InductiveConstructor"
      >true</a
      ><a name="3593"
      >      </a
      ><a name="3599" class="Symbol"
      >=</a
      ><a name="3600"
      > </a
      ><a name="3601" href="https://agda.github.io/agda-stdlib/Data.Sum.html#489" class="InductiveConstructor"
      >inj&#8321;</a
      ><a name="3605"
      > </a
      ><a name="3606" href="Stlc.html#9025" class="InductiveConstructor"
      >true</a
      ><a name="3610"
      >
</a
      ><a name="3611" href="StlcProp.html#1801" class="Function"
      >progress</a
      ><a name="3619"
      > </a
      ><a name="3620" href="Stlc.html#19546" class="InductiveConstructor"
      >false</a
      ><a name="3625"
      >     </a
      ><a name="3630" class="Symbol"
      >=</a
      ><a name="3631"
      > </a
      ><a name="3632" href="https://agda.github.io/agda-stdlib/Data.Sum.html#489" class="InductiveConstructor"
      >inj&#8321;</a
      ><a name="3636"
      > </a
      ><a name="3637" href="Stlc.html#9046" class="InductiveConstructor"
      >false</a
      ><a name="3642"
      >
</a
      ><a name="3643" href="StlcProp.html#1801" class="Function"
      >progress</a
      ><a name="3651"
      > </a
      ><a name="3652" class="Symbol"
      >(</a
      ><a name="3653" href="Stlc.html#19237" class="InductiveConstructor"
      >abs</a
      ><a name="3656"
      > </a
      ><a name="3657" href="StlcProp.html#3657" class="Bound"
      >t&#8758;A</a
      ><a name="3660" class="Symbol"
      >)</a
      ><a name="3661"
      > </a
      ><a name="3662" class="Symbol"
      >=</a
      ><a name="3663"
      > </a
      ><a name="3664" href="https://agda.github.io/agda-stdlib/Data.Sum.html#489" class="InductiveConstructor"
      >inj&#8321;</a
      ><a name="3668"
      > </a
      ><a name="3669" href="Stlc.html#8977" class="InductiveConstructor"
      >abs</a
      ><a name="3672"
      >
</a
      ><a name="3673" href="StlcProp.html#1801" class="Function"
      >progress</a
      ><a name="3681"
      > </a
      ><a name="3682" class="Symbol"
      >(</a
      ><a name="3683" href="Stlc.html#19353" class="InductiveConstructor"
      >app</a
      ><a name="3686"
      > </a
      ><a name="3687" href="StlcProp.html#3687" class="Bound"
      >t&#8321;&#8758;A&#8658;B</a
      ><a name="3693"
      > </a
      ><a name="3694" href="StlcProp.html#3694" class="Bound"
      >t&#8322;&#8758;B</a
      ><a name="3698" class="Symbol"
      >)</a
      ><a name="3699"
      >
    </a
      ><a name="3704" class="Keyword"
      >with</a
      ><a name="3708"
      > </a
      ><a name="3709" href="StlcProp.html#1801" class="Function"
      >progress</a
      ><a name="3717"
      > </a
      ><a name="3718" href="StlcProp.html#3687" class="Bound"
      >t&#8321;&#8758;A&#8658;B</a
      ><a name="3724"
      >
</a
      ><a name="3725" class="Symbol"
      >...</a
      ><a name="3728"
      > </a
      ><a name="3729" class="Symbol"
      >|</a
      ><a name="3730"
      > </a
      ><a name="3731" href="https://agda.github.io/agda-stdlib/Data.Sum.html#514" class="InductiveConstructor"
      >inj&#8322;</a
      ><a name="3735"
      > </a
      ><a name="3736" class="Symbol"
      >(_</a
      ><a name="3738"
      > </a
      ><a name="3739" href="https://agda.github.io/agda-stdlib/Data.Product.html#509" class="InductiveConstructor Operator"
      >,</a
      ><a name="3740"
      > </a
      ><a name="3741" href="StlcProp.html#3741" class="Bound"
      >t&#8321;&#8658;t&#8321;&#8242;</a
      ><a name="3747" class="Symbol"
      >)</a
      ><a name="3748"
      > </a
      ><a name="3749" class="Symbol"
      >=</a
      ><a name="3750"
      > </a
      ><a name="3751" href="https://agda.github.io/agda-stdlib/Data.Sum.html#514" class="InductiveConstructor"
      >inj&#8322;</a
      ><a name="3755"
      > </a
      ><a name="3756" class="Symbol"
      >(_</a
      ><a name="3758"
      > </a
      ><a name="3759" href="https://agda.github.io/agda-stdlib/Data.Product.html#509" class="InductiveConstructor Operator"
      >,</a
      ><a name="3760"
      > </a
      ><a name="3761" href="Stlc.html#15211" class="InductiveConstructor"
      >app1</a
      ><a name="3765"
      > </a
      ><a name="3766" href="StlcProp.html#3741" class="Bound"
      >t&#8321;&#8658;t&#8321;&#8242;</a
      ><a name="3772" class="Symbol"
      >)</a
      ><a name="3773"
      >
</a
      ><a name="3774" class="Symbol"
      >...</a
      ><a name="3777"
      > </a
      ><a name="3778" class="Symbol"
      >|</a
      ><a name="3779"
      > </a
      ><a name="3780" href="https://agda.github.io/agda-stdlib/Data.Sum.html#489" class="InductiveConstructor"
      >inj&#8321;</a
      ><a name="3784"
      > </a
      ><a name="3785" href="StlcProp.html#3785" class="Bound"
      >v&#8321;</a
      ><a name="3787"
      >
    </a
      ><a name="3792" class="Keyword"
      >with</a
      ><a name="3796"
      > </a
      ><a name="3797" href="StlcProp.html#1801" class="Function"
      >progress</a
      ><a name="3805"
      > </a
      ><a name="3806" href="StlcProp.html#3694" class="Bound"
      >t&#8322;&#8758;B</a
      ><a name="3810"
      >
</a
      ><a name="3811" class="Symbol"
      >...</a
      ><a name="3814"
      > </a
      ><a name="3815" class="Symbol"
      >|</a
      ><a name="3816"
      > </a
      ><a name="3817" href="https://agda.github.io/agda-stdlib/Data.Sum.html#514" class="InductiveConstructor"
      >inj&#8322;</a
      ><a name="3821"
      > </a
      ><a name="3822" class="Symbol"
      >(_</a
      ><a name="3824"
      > </a
      ><a name="3825" href="https://agda.github.io/agda-stdlib/Data.Product.html#509" class="InductiveConstructor Operator"
      >,</a
      ><a name="3826"
      > </a
      ><a name="3827" href="StlcProp.html#3827" class="Bound"
      >t&#8322;&#8658;t&#8322;&#8242;</a
      ><a name="3833" class="Symbol"
      >)</a
      ><a name="3834"
      > </a
      ><a name="3835" class="Symbol"
      >=</a
      ><a name="3836"
      > </a
      ><a name="3837" href="https://agda.github.io/agda-stdlib/Data.Sum.html#514" class="InductiveConstructor"
      >inj&#8322;</a
      ><a name="3841"
      > </a
      ><a name="3842" class="Symbol"
      >(_</a
      ><a name="3844"
      > </a
      ><a name="3845" href="https://agda.github.io/agda-stdlib/Data.Product.html#509" class="InductiveConstructor Operator"
      >,</a
      ><a name="3846"
      > </a
      ><a name="3847" href="Stlc.html#15288" class="InductiveConstructor"
      >app2</a
      ><a name="3851"
      > </a
      ><a name="3852" href="StlcProp.html#3785" class="Bound"
      >v&#8321;</a
      ><a name="3854"
      > </a
      ><a name="3855" href="StlcProp.html#3827" class="Bound"
      >t&#8322;&#8658;t&#8322;&#8242;</a
      ><a name="3861" class="Symbol"
      >)</a
      ><a name="3862"
      >
</a
      ><a name="3863" class="Symbol"
      >...</a
      ><a name="3866"
      > </a
      ><a name="3867" class="Symbol"
      >|</a
      ><a name="3868"
      > </a
      ><a name="3869" href="https://agda.github.io/agda-stdlib/Data.Sum.html#489" class="InductiveConstructor"
      >inj&#8321;</a
      ><a name="3873"
      > </a
      ><a name="3874" href="StlcProp.html#3874" class="Bound"
      >v&#8322;</a
      ><a name="3876"
      >
    </a
      ><a name="3881" class="Keyword"
      >with</a
      ><a name="3885"
      > </a
      ><a name="3886" href="StlcProp.html#1226" class="Function"
      >canonicalForms</a
      ><a name="3900"
      > </a
      ><a name="3901" href="StlcProp.html#3687" class="Bound"
      >t&#8321;&#8758;A&#8658;B</a
      ><a name="3907"
      > </a
      ><a name="3908" href="StlcProp.html#3785" class="Bound"
      >v&#8321;</a
      ><a name="3910"
      >
</a
      ><a name="3911" class="Symbol"
      >...</a
      ><a name="3914"
      > </a
      ><a name="3915" class="Symbol"
      >|</a
      ><a name="3916"
      > </a
      ><a name="3917" class="Symbol"
      >(_</a
      ><a name="3919"
      > </a
      ><a name="3920" href="https://agda.github.io/agda-stdlib/Data.Product.html#509" class="InductiveConstructor Operator"
      >,</a
      ><a name="3921"
      > </a
      ><a name="3922" class="Symbol"
      >_</a
      ><a name="3923"
      > </a
      ><a name="3924" href="https://agda.github.io/agda-stdlib/Data.Product.html#509" class="InductiveConstructor Operator"
      >,</a
      ><a name="3925"
      > </a
      ><a name="3926" href="Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="3930" class="Symbol"
      >)</a
      ><a name="3931"
      > </a
      ><a name="3932" class="Symbol"
      >=</a
      ><a name="3933"
      > </a
      ><a name="3934" href="https://agda.github.io/agda-stdlib/Data.Sum.html#514" class="InductiveConstructor"
      >inj&#8322;</a
      ><a name="3938"
      > </a
      ><a name="3939" class="Symbol"
      >(_</a
      ><a name="3941"
      > </a
      ><a name="3942" href="https://agda.github.io/agda-stdlib/Data.Product.html#509" class="InductiveConstructor Operator"
      >,</a
      ><a name="3943"
      > </a
      ><a name="3944" href="Stlc.html#15120" class="InductiveConstructor"
      >red</a
      ><a name="3947"
      > </a
      ><a name="3948" href="StlcProp.html#3874" class="Bound"
      >v&#8322;</a
      ><a name="3950" class="Symbol"
      >)</a
      ><a name="3951"
      >
</a
      ><a name="3952" href="StlcProp.html#1801" class="Function"
      >progress</a
      ><a name="3960"
      > </a
      ><a name="3961" class="Symbol"
      >(</a
      ><a name="3962" href="Stlc.html#19605" class="InductiveConstructor Operator"
      >if</a
      ><a name="3964"
      > </a
      ><a name="3965" href="StlcProp.html#3965" class="Bound"
      >t&#8321;&#8758;bool</a
      ><a name="3972"
      > </a
      ><a name="3973" href="Stlc.html#19605" class="InductiveConstructor Operator"
      >then</a
      ><a name="3977"
      > </a
      ><a name="3978" href="StlcProp.html#3978" class="Bound"
      >t&#8322;&#8758;A</a
      ><a name="3982"
      > </a
      ><a name="3983" href="Stlc.html#19605" class="InductiveConstructor Operator"
      >else</a
      ><a name="3987"
      > </a
      ><a name="3988" href="StlcProp.html#3988" class="Bound"
      >t&#8323;&#8758;A</a
      ><a name="3992" class="Symbol"
      >)</a
      ><a name="3993"
      >
    </a
      ><a name="3998" class="Keyword"
      >with</a
      ><a name="4002"
      > </a
      ><a name="4003" href="StlcProp.html#1801" class="Function"
      >progress</a
      ><a name="4011"
      > </a
      ><a name="4012" href="StlcProp.html#3965" class="Bound"
      >t&#8321;&#8758;bool</a
      ><a name="4019"
      >
</a
      ><a name="4020" class="Symbol"
      >...</a
      ><a name="4023"
      > </a
      ><a name="4024" class="Symbol"
      >|</a
      ><a name="4025"
      > </a
      ><a name="4026" href="https://agda.github.io/agda-stdlib/Data.Sum.html#514" class="InductiveConstructor"
      >inj&#8322;</a
      ><a name="4030"
      > </a
      ><a name="4031" class="Symbol"
      >(_</a
      ><a name="4033"
      > </a
      ><a name="4034" href="https://agda.github.io/agda-stdlib/Data.Product.html#509" class="InductiveConstructor Operator"
      >,</a
      ><a name="4035"
      > </a
      ><a name="4036" href="StlcProp.html#4036" class="Bound"
      >t&#8321;&#8658;t&#8321;&#8242;</a
      ><a name="4042" class="Symbol"
      >)</a
      ><a name="4043"
      > </a
      ><a name="4044" class="Symbol"
      >=</a
      ><a name="4045"
      > </a
      ><a name="4046" href="https://agda.github.io/agda-stdlib/Data.Sum.html#514" class="InductiveConstructor"
      >inj&#8322;</a
      ><a name="4050"
      > </a
      ><a name="4051" class="Symbol"
      >(_</a
      ><a name="4053"
      > </a
      ><a name="4054" href="https://agda.github.io/agda-stdlib/Data.Product.html#509" class="InductiveConstructor Operator"
      >,</a
      ><a name="4055"
      > </a
      ><a name="4056" href="Stlc.html#15385" class="InductiveConstructor"
      >if</a
      ><a name="4058"
      > </a
      ><a name="4059" href="StlcProp.html#4036" class="Bound"
      >t&#8321;&#8658;t&#8321;&#8242;</a
      ><a name="4065" class="Symbol"
      >)</a
      ><a name="4066"
      >
</a
      ><a name="4067" class="Symbol"
      >...</a
      ><a name="4070"
      > </a
      ><a name="4071" class="Symbol"
      >|</a
      ><a name="4072"
      > </a
      ><a name="4073" href="https://agda.github.io/agda-stdlib/Data.Sum.html#489" class="InductiveConstructor"
      >inj&#8321;</a
      ><a name="4077"
      > </a
      ><a name="4078" href="StlcProp.html#4078" class="Bound"
      >v&#8321;</a
      ><a name="4080"
      >
    </a
      ><a name="4085" class="Keyword"
      >with</a
      ><a name="4089"
      > </a
      ><a name="4090" href="StlcProp.html#1226" class="Function"
      >canonicalForms</a
      ><a name="4104"
      > </a
      ><a name="4105" href="StlcProp.html#3965" class="Bound"
      >t&#8321;&#8758;bool</a
      ><a name="4112"
      > </a
      ><a name="4113" href="StlcProp.html#4078" class="Bound"
      >v&#8321;</a
      ><a name="4115"
      >
</a
      ><a name="4116" class="Symbol"
      >...</a
      ><a name="4119"
      > </a
      ><a name="4120" class="Symbol"
      >|</a
      ><a name="4121"
      > </a
      ><a name="4122" href="https://agda.github.io/agda-stdlib/Data.Sum.html#489" class="InductiveConstructor"
      >inj&#8321;</a
      ><a name="4126"
      > </a
      ><a name="4127" href="Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="4131"
      > </a
      ><a name="4132" class="Symbol"
      >=</a
      ><a name="4133"
      > </a
      ><a name="4134" href="https://agda.github.io/agda-stdlib/Data.Sum.html#514" class="InductiveConstructor"
      >inj&#8322;</a
      ><a name="4138"
      > </a
      ><a name="4139" class="Symbol"
      >(_</a
      ><a name="4141"
      > </a
      ><a name="4142" href="https://agda.github.io/agda-stdlib/Data.Product.html#509" class="InductiveConstructor Operator"
      >,</a
      ><a name="4143"
      > </a
      ><a name="4144" href="Stlc.html#15486" class="InductiveConstructor"
      >iftrue</a
      ><a name="4150" class="Symbol"
      >)</a
      ><a name="4151"
      >
</a
      ><a name="4152" class="Symbol"
      >...</a
      ><a name="4155"
      > </a
      ><a name="4156" class="Symbol"
      >|</a
      ><a name="4157"
      > </a
      ><a name="4158" href="https://agda.github.io/agda-stdlib/Data.Sum.html#514" class="InductiveConstructor"
      >inj&#8322;</a
      ><a name="4162"
      > </a
      ><a name="4163" href="Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="4167"
      > </a
      ><a name="4168" class="Symbol"
      >=</a
      ><a name="4169"
      > </a
      ><a name="4170" href="https://agda.github.io/agda-stdlib/Data.Sum.html#514" class="InductiveConstructor"
      >inj&#8322;</a
      ><a name="4174"
      > </a
      ><a name="4175" class="Symbol"
      >(_</a
      ><a name="4177"
      > </a
      ><a name="4178" href="https://agda.github.io/agda-stdlib/Data.Product.html#509" class="InductiveConstructor Operator"
      >,</a
      ><a name="4179"
      > </a
      ><a name="4180" href="Stlc.html#15546" class="InductiveConstructor"
      >iffalse</a
      ><a name="4187" class="Symbol"
      >)</a
      >
{% endraw %}</pre>

#### Exercise: 3 stars, optional (progress_from_term_ind)
Show that progress can also be proved by induction on terms
instead of induction on typing derivations.

<pre class="Agda">{% raw %}
<a name="4377" class="Keyword"
      >postulate</a
      ><a name="4386"
      >
  </a
      ><a name="4389" href="StlcProp.html#4389" class="Postulate"
      >progress&#8242;</a
      ><a name="4398"
      > </a
      ><a name="4399" class="Symbol"
      >:</a
      ><a name="4400"
      > </a
      ><a name="4401" class="Symbol"
      >&#8704;</a
      ><a name="4402"
      > </a
      ><a name="4409" class="Symbol"
      >&#8594;</a
      ><a name="4410"
      > </a
      ><a name="4411" href="Stlc.html#18168" class="Function"
      >&#8709;</a
      ><a name="4412"
      > </a
      ><a name="4413" href="Stlc.html#19100" class="Datatype Operator"
      >&#8866;</a
      ><a name="4414"
      > </a
      ><a name="4415" href="StlcProp.html#4404" class="Bound"
      >t</a
      ><a name="4416"
      > </a
      ><a name="4417" href="Stlc.html#19100" class="Datatype Operator"
      >&#8758;</a
      ><a name="4418"
      > </a
      ><a name="4419" href="StlcProp.html#4406" class="Bound"
      >A</a
      ><a name="4420"
      > </a
      ><a name="4421" class="Symbol"
      >&#8594;</a
      ><a name="4422"
      > </a
      ><a name="4423" href="Stlc.html#8950" class="Datatype"
      >Value</a
      ><a name="4428"
      > </a
      ><a name="4429" href="StlcProp.html#4404" class="Bound"
      >t</a
      ><a name="4430"
      > </a
      ><a name="4431" href="https://agda.github.io/agda-stdlib/Data.Sum.html#433" class="Datatype Operator"
      >&#8846;</a
      ><a name="4432"
      > </a
      ><a name="4433" href="https://agda.github.io/agda-stdlib/Data.Product.html#823" class="Function"
      >&#8707;</a
      ><a name="4434"
      > </a
      ><a name="4435" class="Symbol"
      >&#955;</a
      ><a name="4436"
      > </a
      ><a name="4437" href="StlcProp.html#4437" class="Bound"
      >t&#8242;</a
      ><a name="4439"
      > </a
      ><a name="4440" class="Symbol"
      >&#8594;</a
      ><a name="4441"
      > </a
      ><a name="4442" href="StlcProp.html#4404" class="Bound"
      >t</a
      ><a name="4443"
      > </a
      ><a name="4444" href="Stlc.html#15086" class="Datatype Operator"
      >==&gt;</a
      ><a name="4447"
      > </a
      ><a name="4448" href="StlcProp.html#4437" class="Bound"
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
<a name="6871" class="Keyword"
      >data</a
      ><a name="6875"
      > </a
      ><a name="6876" href="StlcProp.html#6876" class="Datatype Operator"
      >_FreeIn_</a
      ><a name="6884"
      > </a
      ><a name="6885" class="Symbol"
      >(</a
      ><a name="6886" href="StlcProp.html#6886" class="Bound"
      >x</a
      ><a name="6887"
      > </a
      ><a name="6888" class="Symbol"
      >:</a
      ><a name="6889"
      > </a
      ><a name="6890" href="Maps.html#2275" class="Datatype"
      >Id</a
      ><a name="6892" class="Symbol"
      >)</a
      ><a name="6893"
      > </a
      ><a name="6894" class="Symbol"
      >:</a
      ><a name="6895"
      > </a
      ><a name="6896" href="Stlc.html#5543" class="Datatype"
      >Term</a
      ><a name="6900"
      > </a
      ><a name="6901" class="Symbol"
      >&#8594;</a
      ><a name="6902"
      > </a
      ><a name="6903" class="PrimitiveType"
      >Set</a
      ><a name="6906"
      > </a
      ><a name="6907" class="Keyword"
      >where</a
      ><a name="6912"
      >
  </a
      ><a name="6915" href="StlcProp.html#6915" class="InductiveConstructor"
      >var</a
      ><a name="6918"
      >  </a
      ><a name="6920" class="Symbol"
      >:</a
      ><a name="6921"
      > </a
      ><a name="6922" href="StlcProp.html#6886" class="Bound"
      >x</a
      ><a name="6923"
      > </a
      ><a name="6924" href="StlcProp.html#6876" class="Datatype Operator"
      >FreeIn</a
      ><a name="6930"
      > </a
      ><a name="6931" href="Stlc.html#5562" class="InductiveConstructor"
      >var</a
      ><a name="6934"
      > </a
      ><a name="6935" href="StlcProp.html#6886" class="Bound"
      >x</a
      ><a name="6936"
      >
  </a
      ><a name="6939" href="StlcProp.html#6939" class="InductiveConstructor"
      >abs</a
      ><a name="6942"
      >  </a
      ><a name="6944" class="Symbol"
      >:</a
      ><a name="6945"
      > </a
      ><a name="6946" class="Symbol"
      >&#8704;</a
      ><a name="6947"
      > </a
      ><a name="6956" class="Symbol"
      >&#8594;</a
      ><a name="6957"
      > </a
      ><a name="6958" href="StlcProp.html#6949" class="Bound"
      >y</a
      ><a name="6959"
      > </a
      ><a name="6960" href="https://agda.github.io/agda-stdlib/Relation.Binary.Core.html#4493" class="Function Operator"
      >&#8802;</a
      ><a name="6961"
      > </a
      ><a name="6962" href="StlcProp.html#6886" class="Bound"
      >x</a
      ><a name="6963"
      > </a
      ><a name="6964" class="Symbol"
      >&#8594;</a
      ><a name="6965"
      > </a
      ><a name="6966" href="StlcProp.html#6886" class="Bound"
      >x</a
      ><a name="6967"
      > </a
      ><a name="6968" href="StlcProp.html#6876" class="Datatype Operator"
      >FreeIn</a
      ><a name="6974"
      > </a
      ><a name="6975" href="StlcProp.html#6953" class="Bound"
      >t</a
      ><a name="6976"
      > </a
      ><a name="6977" class="Symbol"
      >&#8594;</a
      ><a name="6978"
      > </a
      ><a name="6979" href="StlcProp.html#6886" class="Bound"
      >x</a
      ><a name="6980"
      > </a
      ><a name="6981" href="StlcProp.html#6876" class="Datatype Operator"
      >FreeIn</a
      ><a name="6987"
      > </a
      ><a name="6988" href="Stlc.html#5611" class="InductiveConstructor"
      >abs</a
      ><a name="6991"
      > </a
      ><a name="6992" href="StlcProp.html#6949" class="Bound"
      >y</a
      ><a name="6993"
      > </a
      ><a name="6994" href="StlcProp.html#6951" class="Bound"
      >A</a
      ><a name="6995"
      > </a
      ><a name="6996" href="StlcProp.html#6953" class="Bound"
      >t</a
      ><a name="6997"
      >
  </a
      ><a name="7000" href="StlcProp.html#7000" class="InductiveConstructor"
      >app1</a
      ><a name="7004"
      > </a
      ><a name="7005" class="Symbol"
      >:</a
      ><a name="7006"
      > </a
      ><a name="7007" class="Symbol"
      >&#8704;</a
      ><a name="7008"
      > </a
      ><a name="7017" class="Symbol"
      >&#8594;</a
      ><a name="7018"
      > </a
      ><a name="7019" href="StlcProp.html#6886" class="Bound"
      >x</a
      ><a name="7020"
      > </a
      ><a name="7021" href="StlcProp.html#6876" class="Datatype Operator"
      >FreeIn</a
      ><a name="7027"
      > </a
      ><a name="7028" href="StlcProp.html#7010" class="Bound"
      >t&#8321;</a
      ><a name="7030"
      > </a
      ><a name="7031" class="Symbol"
      >&#8594;</a
      ><a name="7032"
      > </a
      ><a name="7033" href="StlcProp.html#6886" class="Bound"
      >x</a
      ><a name="7034"
      > </a
      ><a name="7035" href="StlcProp.html#6876" class="Datatype Operator"
      >FreeIn</a
      ><a name="7041"
      > </a
      ><a name="7042" href="Stlc.html#5582" class="InductiveConstructor"
      >app</a
      ><a name="7045"
      > </a
      ><a name="7046" href="StlcProp.html#7010" class="Bound"
      >t&#8321;</a
      ><a name="7048"
      > </a
      ><a name="7049" href="StlcProp.html#7013" class="Bound"
      >t&#8322;</a
      ><a name="7051"
      >
  </a
      ><a name="7054" href="StlcProp.html#7054" class="InductiveConstructor"
      >app2</a
      ><a name="7058"
      > </a
      ><a name="7059" class="Symbol"
      >:</a
      ><a name="7060"
      > </a
      ><a name="7061" class="Symbol"
      >&#8704;</a
      ><a name="7062"
      > </a
      ><a name="7071" class="Symbol"
      >&#8594;</a
      ><a name="7072"
      > </a
      ><a name="7073" href="StlcProp.html#6886" class="Bound"
      >x</a
      ><a name="7074"
      > </a
      ><a name="7075" href="StlcProp.html#6876" class="Datatype Operator"
      >FreeIn</a
      ><a name="7081"
      > </a
      ><a name="7082" href="StlcProp.html#7067" class="Bound"
      >t&#8322;</a
      ><a name="7084"
      > </a
      ><a name="7085" class="Symbol"
      >&#8594;</a
      ><a name="7086"
      > </a
      ><a name="7087" href="StlcProp.html#6886" class="Bound"
      >x</a
      ><a name="7088"
      > </a
      ><a name="7089" href="StlcProp.html#6876" class="Datatype Operator"
      >FreeIn</a
      ><a name="7095"
      > </a
      ><a name="7096" href="Stlc.html#5582" class="InductiveConstructor"
      >app</a
      ><a name="7099"
      > </a
      ><a name="7100" href="StlcProp.html#7064" class="Bound"
      >t&#8321;</a
      ><a name="7102"
      > </a
      ><a name="7103" href="StlcProp.html#7067" class="Bound"
      >t&#8322;</a
      ><a name="7105"
      >
  </a
      ><a name="7108" href="StlcProp.html#7108" class="InductiveConstructor"
      >if1</a
      ><a name="7111"
      >  </a
      ><a name="7113" class="Symbol"
      >:</a
      ><a name="7114"
      > </a
      ><a name="7115" class="Symbol"
      >&#8704;</a
      ><a name="7116"
      > </a
      ><a name="7128" class="Symbol"
      >&#8594;</a
      ><a name="7129"
      > </a
      ><a name="7130" href="StlcProp.html#6886" class="Bound"
      >x</a
      ><a name="7131"
      > </a
      ><a name="7132" href="StlcProp.html#6876" class="Datatype Operator"
      >FreeIn</a
      ><a name="7138"
      > </a
      ><a name="7139" href="StlcProp.html#7118" class="Bound"
      >t&#8321;</a
      ><a name="7141"
      > </a
      ><a name="7142" class="Symbol"
      >&#8594;</a
      ><a name="7143"
      > </a
      ><a name="7144" href="StlcProp.html#6886" class="Bound"
      >x</a
      ><a name="7145"
      > </a
      ><a name="7146" href="StlcProp.html#6876" class="Datatype Operator"
      >FreeIn</a
      ><a name="7152"
      > </a
      ><a name="7153" class="Symbol"
      >(</a
      ><a name="7154" href="Stlc.html#5675" class="InductiveConstructor Operator"
      >if</a
      ><a name="7156"
      > </a
      ><a name="7157" href="StlcProp.html#7118" class="Bound"
      >t&#8321;</a
      ><a name="7159"
      > </a
      ><a name="7160" href="Stlc.html#5675" class="InductiveConstructor Operator"
      >then</a
      ><a name="7164"
      > </a
      ><a name="7165" href="StlcProp.html#7121" class="Bound"
      >t&#8322;</a
      ><a name="7167"
      > </a
      ><a name="7168" href="Stlc.html#5675" class="InductiveConstructor Operator"
      >else</a
      ><a name="7172"
      > </a
      ><a name="7173" href="StlcProp.html#7124" class="Bound"
      >t&#8323;</a
      ><a name="7175" class="Symbol"
      >)</a
      ><a name="7176"
      >
  </a
      ><a name="7179" href="StlcProp.html#7179" class="InductiveConstructor"
      >if2</a
      ><a name="7182"
      >  </a
      ><a name="7184" class="Symbol"
      >:</a
      ><a name="7185"
      > </a
      ><a name="7186" class="Symbol"
      >&#8704;</a
      ><a name="7187"
      > </a
      ><a name="7199" class="Symbol"
      >&#8594;</a
      ><a name="7200"
      > </a
      ><a name="7201" href="StlcProp.html#6886" class="Bound"
      >x</a
      ><a name="7202"
      > </a
      ><a name="7203" href="StlcProp.html#6876" class="Datatype Operator"
      >FreeIn</a
      ><a name="7209"
      > </a
      ><a name="7210" href="StlcProp.html#7192" class="Bound"
      >t&#8322;</a
      ><a name="7212"
      > </a
      ><a name="7213" class="Symbol"
      >&#8594;</a
      ><a name="7214"
      > </a
      ><a name="7215" href="StlcProp.html#6886" class="Bound"
      >x</a
      ><a name="7216"
      > </a
      ><a name="7217" href="StlcProp.html#6876" class="Datatype Operator"
      >FreeIn</a
      ><a name="7223"
      > </a
      ><a name="7224" class="Symbol"
      >(</a
      ><a name="7225" href="Stlc.html#5675" class="InductiveConstructor Operator"
      >if</a
      ><a name="7227"
      > </a
      ><a name="7228" href="StlcProp.html#7189" class="Bound"
      >t&#8321;</a
      ><a name="7230"
      > </a
      ><a name="7231" href="Stlc.html#5675" class="InductiveConstructor Operator"
      >then</a
      ><a name="7235"
      > </a
      ><a name="7236" href="StlcProp.html#7192" class="Bound"
      >t&#8322;</a
      ><a name="7238"
      > </a
      ><a name="7239" href="Stlc.html#5675" class="InductiveConstructor Operator"
      >else</a
      ><a name="7243"
      > </a
      ><a name="7244" href="StlcProp.html#7195" class="Bound"
      >t&#8323;</a
      ><a name="7246" class="Symbol"
      >)</a
      ><a name="7247"
      >
  </a
      ><a name="7250" href="StlcProp.html#7250" class="InductiveConstructor"
      >if3</a
      ><a name="7253"
      >  </a
      ><a name="7255" class="Symbol"
      >:</a
      ><a name="7256"
      > </a
      ><a name="7257" class="Symbol"
      >&#8704;</a
      ><a name="7258"
      > </a
      ><a name="7270" class="Symbol"
      >&#8594;</a
      ><a name="7271"
      > </a
      ><a name="7272" href="StlcProp.html#6886" class="Bound"
      >x</a
      ><a name="7273"
      > </a
      ><a name="7274" href="StlcProp.html#6876" class="Datatype Operator"
      >FreeIn</a
      ><a name="7280"
      > </a
      ><a name="7281" href="StlcProp.html#7266" class="Bound"
      >t&#8323;</a
      ><a name="7283"
      > </a
      ><a name="7284" class="Symbol"
      >&#8594;</a
      ><a name="7285"
      > </a
      ><a name="7286" href="StlcProp.html#6886" class="Bound"
      >x</a
      ><a name="7287"
      > </a
      ><a name="7288" href="StlcProp.html#6876" class="Datatype Operator"
      >FreeIn</a
      ><a name="7294"
      > </a
      ><a name="7295" class="Symbol"
      >(</a
      ><a name="7296" href="Stlc.html#5675" class="InductiveConstructor Operator"
      >if</a
      ><a name="7298"
      > </a
      ><a name="7299" href="StlcProp.html#7260" class="Bound"
      >t&#8321;</a
      ><a name="7301"
      > </a
      ><a name="7302" href="Stlc.html#5675" class="InductiveConstructor Operator"
      >then</a
      ><a name="7306"
      > </a
      ><a name="7307" href="StlcProp.html#7263" class="Bound"
      >t&#8322;</a
      ><a name="7309"
      > </a
      ><a name="7310" href="Stlc.html#5675" class="InductiveConstructor Operator"
      >else</a
      ><a name="7314"
      > </a
      ><a name="7315" href="StlcProp.html#7266" class="Bound"
      >t&#8323;</a
      ><a name="7317" class="Symbol"
      >)</a
      >
{% endraw %}</pre>

A term in which no variables appear free is said to be _closed_.

<pre class="Agda">{% raw %}
<a name="7410" href="StlcProp.html#7410" class="Function"
      >Closed</a
      ><a name="7416"
      > </a
      ><a name="7417" class="Symbol"
      >:</a
      ><a name="7418"
      > </a
      ><a name="7419" href="Stlc.html#5543" class="Datatype"
      >Term</a
      ><a name="7423"
      > </a
      ><a name="7424" class="Symbol"
      >&#8594;</a
      ><a name="7425"
      > </a
      ><a name="7426" class="PrimitiveType"
      >Set</a
      ><a name="7429"
      >
</a
      ><a name="7430" href="StlcProp.html#7410" class="Function"
      >Closed</a
      ><a name="7436"
      > </a
      ><a name="7437" href="StlcProp.html#7437" class="Bound"
      >t</a
      ><a name="7438"
      > </a
      ><a name="7439" class="Symbol"
      >=</a
      ><a name="7440"
      > </a
      ><a name="7441" class="Symbol"
      >&#8704;</a
      ><a name="7442"
      > </a
      ><a name="7447" class="Symbol"
      >&#8594;</a
      ><a name="7448"
      > </a
      ><a name="7449" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#414" class="Function Operator"
      >&#172;</a
      ><a name="7450"
      > </a
      ><a name="7451" class="Symbol"
      >(</a
      ><a name="7452" href="StlcProp.html#7444" class="Bound"
      >x</a
      ><a name="7453"
      > </a
      ><a name="7454" href="StlcProp.html#6876" class="Datatype Operator"
      >FreeIn</a
      ><a name="7460"
      > </a
      ><a name="7461" href="StlcProp.html#7437" class="Bound"
      >t</a
      ><a name="7462" class="Symbol"
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
<a name="8191" href="StlcProp.html#8191" class="Function"
      >freeInCtxt</a
      ><a name="8201"
      > </a
      ><a name="8202" class="Symbol"
      >:</a
      ><a name="8203"
      > </a
      ><a name="8204" class="Symbol"
      >&#8704;</a
      ><a name="8205"
      > </a
      ><a name="8216" class="Symbol"
      >&#8594;</a
      ><a name="8217"
      > </a
      ><a name="8218" href="StlcProp.html#8207" class="Bound"
      >x</a
      ><a name="8219"
      > </a
      ><a name="8220" href="StlcProp.html#6876" class="Datatype Operator"
      >FreeIn</a
      ><a name="8226"
      > </a
      ><a name="8227" href="StlcProp.html#8209" class="Bound"
      >t</a
      ><a name="8228"
      > </a
      ><a name="8229" class="Symbol"
      >&#8594;</a
      ><a name="8230"
      > </a
      ><a name="8231" href="StlcProp.html#8213" class="Bound"
      >&#915;</a
      ><a name="8232"
      > </a
      ><a name="8233" href="Stlc.html#19100" class="Datatype Operator"
      >&#8866;</a
      ><a name="8234"
      > </a
      ><a name="8235" href="StlcProp.html#8209" class="Bound"
      >t</a
      ><a name="8236"
      > </a
      ><a name="8237" href="Stlc.html#19100" class="Datatype Operator"
      >&#8758;</a
      ><a name="8238"
      > </a
      ><a name="8239" href="StlcProp.html#8211" class="Bound"
      >A</a
      ><a name="8240"
      > </a
      ><a name="8241" class="Symbol"
      >&#8594;</a
      ><a name="8242"
      > </a
      ><a name="8243" href="https://agda.github.io/agda-stdlib/Data.Product.html#823" class="Function"
      >&#8707;</a
      ><a name="8244"
      > </a
      ><a name="8245" class="Symbol"
      >&#955;</a
      ><a name="8246"
      > </a
      ><a name="8247" href="StlcProp.html#8247" class="Bound"
      >B</a
      ><a name="8248"
      > </a
      ><a name="8249" class="Symbol"
      >&#8594;</a
      ><a name="8250"
      > </a
      ><a name="8251" href="StlcProp.html#8213" class="Bound"
      >&#915;</a
      ><a name="8252"
      > </a
      ><a name="8253" href="StlcProp.html#8207" class="Bound"
      >x</a
      ><a name="8254"
      > </a
      ><a name="8255" href="Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="8256"
      > </a
      ><a name="8257" href="https://agda.github.io/agda-stdlib/Data.Maybe.Base.html#373" class="InductiveConstructor"
      >just</a
      ><a name="8261"
      > </a
      ><a name="8262" href="StlcProp.html#8247" class="Bound"
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
<a name="9858" href="StlcProp.html#8191" class="Function"
      >freeInCtxt</a
      ><a name="9868"
      > </a
      ><a name="9869" href="StlcProp.html#6915" class="InductiveConstructor"
      >var</a
      ><a name="9872"
      > </a
      ><a name="9873" class="Symbol"
      >(</a
      ><a name="9874" href="Stlc.html#19144" class="InductiveConstructor"
      >var</a
      ><a name="9877"
      > </a
      ><a name="9878" class="Symbol"
      >_</a
      ><a name="9879"
      > </a
      ><a name="9880" href="StlcProp.html#9880" class="Bound"
      >x&#8758;A</a
      ><a name="9883" class="Symbol"
      >)</a
      ><a name="9884"
      > </a
      ><a name="9885" class="Symbol"
      >=</a
      ><a name="9886"
      > </a
      ><a name="9887" class="Symbol"
      >(_</a
      ><a name="9889"
      > </a
      ><a name="9890" href="https://agda.github.io/agda-stdlib/Data.Product.html#509" class="InductiveConstructor Operator"
      >,</a
      ><a name="9891"
      > </a
      ><a name="9892" href="StlcProp.html#9880" class="Bound"
      >x&#8758;A</a
      ><a name="9895" class="Symbol"
      >)</a
      ><a name="9896"
      >
</a
      ><a name="9897" href="StlcProp.html#8191" class="Function"
      >freeInCtxt</a
      ><a name="9907"
      > </a
      ><a name="9908" class="Symbol"
      >(</a
      ><a name="9909" href="StlcProp.html#7000" class="InductiveConstructor"
      >app1</a
      ><a name="9913"
      > </a
      ><a name="9914" href="StlcProp.html#9914" class="Bound"
      >x&#8712;t&#8321;</a
      ><a name="9918" class="Symbol"
      >)</a
      ><a name="9919"
      > </a
      ><a name="9920" class="Symbol"
      >(</a
      ><a name="9921" href="Stlc.html#19353" class="InductiveConstructor"
      >app</a
      ><a name="9924"
      > </a
      ><a name="9925" href="StlcProp.html#9925" class="Bound"
      >t&#8321;&#8758;A</a
      ><a name="9929"
      > </a
      ><a name="9930" class="Symbol"
      >_</a
      ><a name="9931"
      >   </a
      ><a name="9934" class="Symbol"
      >)</a
      ><a name="9935"
      > </a
      ><a name="9936" class="Symbol"
      >=</a
      ><a name="9937"
      > </a
      ><a name="9938" href="StlcProp.html#8191" class="Function"
      >freeInCtxt</a
      ><a name="9948"
      > </a
      ><a name="9949" href="StlcProp.html#9914" class="Bound"
      >x&#8712;t&#8321;</a
      ><a name="9953"
      > </a
      ><a name="9954" href="StlcProp.html#9925" class="Bound"
      >t&#8321;&#8758;A</a
      ><a name="9958"
      >
</a
      ><a name="9959" href="StlcProp.html#8191" class="Function"
      >freeInCtxt</a
      ><a name="9969"
      > </a
      ><a name="9970" class="Symbol"
      >(</a
      ><a name="9971" href="StlcProp.html#7054" class="InductiveConstructor"
      >app2</a
      ><a name="9975"
      > </a
      ><a name="9976" href="StlcProp.html#9976" class="Bound"
      >x&#8712;t&#8322;</a
      ><a name="9980" class="Symbol"
      >)</a
      ><a name="9981"
      > </a
      ><a name="9982" class="Symbol"
      >(</a
      ><a name="9983" href="Stlc.html#19353" class="InductiveConstructor"
      >app</a
      ><a name="9986"
      > </a
      ><a name="9987" class="Symbol"
      >_</a
      ><a name="9988"
      >    </a
      ><a name="9992" href="StlcProp.html#9992" class="Bound"
      >t&#8322;&#8758;A</a
      ><a name="9996" class="Symbol"
      >)</a
      ><a name="9997"
      > </a
      ><a name="9998" class="Symbol"
      >=</a
      ><a name="9999"
      > </a
      ><a name="10000" href="StlcProp.html#8191" class="Function"
      >freeInCtxt</a
      ><a name="10010"
      > </a
      ><a name="10011" href="StlcProp.html#9976" class="Bound"
      >x&#8712;t&#8322;</a
      ><a name="10015"
      > </a
      ><a name="10016" href="StlcProp.html#9992" class="Bound"
      >t&#8322;&#8758;A</a
      ><a name="10020"
      >
</a
      ><a name="10021" href="StlcProp.html#8191" class="Function"
      >freeInCtxt</a
      ><a name="10031"
      > </a
      ><a name="10032" class="Symbol"
      >(</a
      ><a name="10033" href="StlcProp.html#7108" class="InductiveConstructor"
      >if1</a
      ><a name="10036"
      >  </a
      ><a name="10038" href="StlcProp.html#10038" class="Bound"
      >x&#8712;t&#8321;</a
      ><a name="10042" class="Symbol"
      >)</a
      ><a name="10043"
      > </a
      ><a name="10044" class="Symbol"
      >(</a
      ><a name="10045" href="Stlc.html#19605" class="InductiveConstructor Operator"
      >if</a
      ><a name="10047"
      > </a
      ><a name="10048" href="StlcProp.html#10048" class="Bound"
      >t&#8321;&#8758;A</a
      ><a name="10052"
      > </a
      ><a name="10053" href="Stlc.html#19605" class="InductiveConstructor Operator"
      >then</a
      ><a name="10057"
      > </a
      ><a name="10058" class="Symbol"
      >_</a
      ><a name="10059"
      >    </a
      ><a name="10063" href="Stlc.html#19605" class="InductiveConstructor Operator"
      >else</a
      ><a name="10067"
      > </a
      ><a name="10068" class="Symbol"
      >_</a
      ><a name="10069"
      >   </a
      ><a name="10072" class="Symbol"
      >)</a
      ><a name="10073"
      > </a
      ><a name="10074" class="Symbol"
      >=</a
      ><a name="10075"
      > </a
      ><a name="10076" href="StlcProp.html#8191" class="Function"
      >freeInCtxt</a
      ><a name="10086"
      > </a
      ><a name="10087" href="StlcProp.html#10038" class="Bound"
      >x&#8712;t&#8321;</a
      ><a name="10091"
      > </a
      ><a name="10092" href="StlcProp.html#10048" class="Bound"
      >t&#8321;&#8758;A</a
      ><a name="10096"
      >
</a
      ><a name="10097" href="StlcProp.html#8191" class="Function"
      >freeInCtxt</a
      ><a name="10107"
      > </a
      ><a name="10108" class="Symbol"
      >(</a
      ><a name="10109" href="StlcProp.html#7179" class="InductiveConstructor"
      >if2</a
      ><a name="10112"
      >  </a
      ><a name="10114" href="StlcProp.html#10114" class="Bound"
      >x&#8712;t&#8322;</a
      ><a name="10118" class="Symbol"
      >)</a
      ><a name="10119"
      > </a
      ><a name="10120" class="Symbol"
      >(</a
      ><a name="10121" href="Stlc.html#19605" class="InductiveConstructor Operator"
      >if</a
      ><a name="10123"
      > </a
      ><a name="10124" class="Symbol"
      >_</a
      ><a name="10125"
      >    </a
      ><a name="10129" href="Stlc.html#19605" class="InductiveConstructor Operator"
      >then</a
      ><a name="10133"
      > </a
      ><a name="10134" href="StlcProp.html#10134" class="Bound"
      >t&#8322;&#8758;A</a
      ><a name="10138"
      > </a
      ><a name="10139" href="Stlc.html#19605" class="InductiveConstructor Operator"
      >else</a
      ><a name="10143"
      > </a
      ><a name="10144" class="Symbol"
      >_</a
      ><a name="10145"
      >   </a
      ><a name="10148" class="Symbol"
      >)</a
      ><a name="10149"
      > </a
      ><a name="10150" class="Symbol"
      >=</a
      ><a name="10151"
      > </a
      ><a name="10152" href="StlcProp.html#8191" class="Function"
      >freeInCtxt</a
      ><a name="10162"
      > </a
      ><a name="10163" href="StlcProp.html#10114" class="Bound"
      >x&#8712;t&#8322;</a
      ><a name="10167"
      > </a
      ><a name="10168" href="StlcProp.html#10134" class="Bound"
      >t&#8322;&#8758;A</a
      ><a name="10172"
      >
</a
      ><a name="10173" href="StlcProp.html#8191" class="Function"
      >freeInCtxt</a
      ><a name="10183"
      > </a
      ><a name="10184" class="Symbol"
      >(</a
      ><a name="10185" href="StlcProp.html#7250" class="InductiveConstructor"
      >if3</a
      ><a name="10188"
      >  </a
      ><a name="10190" href="StlcProp.html#10190" class="Bound"
      >x&#8712;t&#8323;</a
      ><a name="10194" class="Symbol"
      >)</a
      ><a name="10195"
      > </a
      ><a name="10196" class="Symbol"
      >(</a
      ><a name="10197" href="Stlc.html#19605" class="InductiveConstructor Operator"
      >if</a
      ><a name="10199"
      > </a
      ><a name="10200" class="Symbol"
      >_</a
      ><a name="10201"
      >    </a
      ><a name="10205" href="Stlc.html#19605" class="InductiveConstructor Operator"
      >then</a
      ><a name="10209"
      > </a
      ><a name="10210" class="Symbol"
      >_</a
      ><a name="10211"
      >    </a
      ><a name="10215" href="Stlc.html#19605" class="InductiveConstructor Operator"
      >else</a
      ><a name="10219"
      > </a
      ><a name="10220" href="StlcProp.html#10220" class="Bound"
      >t&#8323;&#8758;A</a
      ><a name="10224" class="Symbol"
      >)</a
      ><a name="10225"
      > </a
      ><a name="10226" class="Symbol"
      >=</a
      ><a name="10227"
      > </a
      ><a name="10228" href="StlcProp.html#8191" class="Function"
      >freeInCtxt</a
      ><a name="10238"
      > </a
      ><a name="10239" href="StlcProp.html#10190" class="Bound"
      >x&#8712;t&#8323;</a
      ><a name="10243"
      > </a
      ><a name="10244" href="StlcProp.html#10220" class="Bound"
      >t&#8323;&#8758;A</a
      ><a name="10248"
      >
</a
      ><a name="10249" href="StlcProp.html#8191" class="Function"
      >freeInCtxt</a
      ><a name="10259"
      > </a
      ><a name="10264" class="Symbol"
      >(</a
      ><a name="10265" href="StlcProp.html#6939" class="InductiveConstructor"
      >abs</a
      ><a name="10268"
      > </a
      ><a name="10273" href="StlcProp.html#10273" class="Bound"
      >y&#8800;x</a
      ><a name="10276"
      > </a
      ><a name="10277" href="StlcProp.html#10277" class="Bound"
      >x&#8712;t</a
      ><a name="10280" class="Symbol"
      >)</a
      ><a name="10281"
      > </a
      ><a name="10282" class="Symbol"
      >(</a
      ><a name="10283" href="Stlc.html#19237" class="InductiveConstructor"
      >abs</a
      ><a name="10286"
      > </a
      ><a name="10287" href="StlcProp.html#10287" class="Bound"
      >t&#8758;B</a
      ><a name="10290" class="Symbol"
      >)</a
      ><a name="10291"
      >
    </a
      ><a name="10296" class="Keyword"
      >with</a
      ><a name="10300"
      > </a
      ><a name="10301" href="StlcProp.html#8191" class="Function"
      >freeInCtxt</a
      ><a name="10311"
      > </a
      ><a name="10312" href="StlcProp.html#10277" class="Bound"
      >x&#8712;t</a
      ><a name="10315"
      > </a
      ><a name="10316" href="StlcProp.html#10287" class="Bound"
      >t&#8758;B</a
      ><a name="10319"
      >
</a
      ><a name="10320" class="Symbol"
      >...</a
      ><a name="10323"
      > </a
      ><a name="10324" class="Symbol"
      >|</a
      ><a name="10325"
      > </a
      ><a name="10326" href="StlcProp.html#10326" class="Bound"
      >x&#8758;A</a
      ><a name="10329"
      >
    </a
      ><a name="10334" class="Keyword"
      >with</a
      ><a name="10338"
      > </a
      ><a name="10339" href="StlcProp.html#10270" class="Bound"
      >y</a
      ><a name="10340"
      > </a
      ><a name="10341" href="Maps.html#2329" class="Function Operator"
      >&#8799;</a
      ><a name="10342"
      > </a
      ><a name="10343" href="StlcProp.html#10261" class="Bound"
      >x</a
      ><a name="10344"
      >
</a
      ><a name="10345" class="Symbol"
      >...</a
      ><a name="10348"
      > </a
      ><a name="10349" class="Symbol"
      >|</a
      ><a name="10350"
      > </a
      ><a name="10351" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#520" class="InductiveConstructor"
      >yes</a
      ><a name="10354"
      > </a
      ><a name="10355" href="StlcProp.html#10355" class="Bound"
      >y=x</a
      ><a name="10358"
      > </a
      ><a name="10359" class="Symbol"
      >=</a
      ><a name="10360"
      > </a
      ><a name="10361" href="https://agda.github.io/agda-stdlib/Data.Empty.html#348" class="Function"
      >&#8869;-elim</a
      ><a name="10367"
      > </a
      ><a name="10368" class="Symbol"
      >(</a
      ><a name="10369" href="StlcProp.html#10273" class="Bound"
      >y&#8800;x</a
      ><a name="10372"
      > </a
      ><a name="10373" href="StlcProp.html#10355" class="Bound"
      >y=x</a
      ><a name="10376" class="Symbol"
      >)</a
      ><a name="10377"
      >
</a
      ><a name="10378" class="Symbol"
      >...</a
      ><a name="10381"
      > </a
      ><a name="10382" class="Symbol"
      >|</a
      ><a name="10383"
      > </a
      ><a name="10384" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#547" class="InductiveConstructor"
      >no</a
      ><a name="10386"
      >  </a
      ><a name="10388" class="Symbol"
      >_</a
      ><a name="10389"
      >   </a
      ><a name="10392" class="Symbol"
      >=</a
      ><a name="10393"
      > </a
      ><a name="10394" href="StlcProp.html#10326" class="Bound"
      >x&#8758;A</a
      >
{% endraw %}</pre>

Next, we'll need the fact that any term $$t$$ which is well typed in
the empty context is closed (it has no free variables).

#### Exercise: 2 stars, optional (∅⊢-closed)

<pre class="Agda">{% raw %}
<a name="10595" class="Keyword"
      >postulate</a
      ><a name="10604"
      >
  </a
      ><a name="10607" href="StlcProp.html#10607" class="Postulate"
      >&#8709;&#8866;-closed</a
      ><a name="10616"
      > </a
      ><a name="10617" class="Symbol"
      >:</a
      ><a name="10618"
      > </a
      ><a name="10619" class="Symbol"
      >&#8704;</a
      ><a name="10620"
      > </a
      ><a name="10627" class="Symbol"
      >&#8594;</a
      ><a name="10628"
      > </a
      ><a name="10629" href="Stlc.html#18168" class="Function"
      >&#8709;</a
      ><a name="10630"
      > </a
      ><a name="10631" href="Stlc.html#19100" class="Datatype Operator"
      >&#8866;</a
      ><a name="10632"
      > </a
      ><a name="10633" href="StlcProp.html#10622" class="Bound"
      >t</a
      ><a name="10634"
      > </a
      ><a name="10635" href="Stlc.html#19100" class="Datatype Operator"
      >&#8758;</a
      ><a name="10636"
      > </a
      ><a name="10637" href="StlcProp.html#10624" class="Bound"
      >A</a
      ><a name="10638"
      > </a
      ><a name="10639" class="Symbol"
      >&#8594;</a
      ><a name="10640"
      > </a
      ><a name="10641" href="StlcProp.html#7410" class="Function"
      >Closed</a
      ><a name="10647"
      > </a
      ><a name="10648" href="StlcProp.html#10622" class="Bound"
      >t</a
      >
{% endraw %}</pre>

<div class="hidden">
<pre class="Agda">{% raw %}
<a name="10696" href="StlcProp.html#10696" class="Function"
      >&#8709;&#8866;-closed&#8242;</a
      ><a name="10706"
      > </a
      ><a name="10707" class="Symbol"
      >:</a
      ><a name="10708"
      > </a
      ><a name="10709" class="Symbol"
      >&#8704;</a
      ><a name="10710"
      > </a
      ><a name="10717" class="Symbol"
      >&#8594;</a
      ><a name="10718"
      > </a
      ><a name="10719" href="Stlc.html#18168" class="Function"
      >&#8709;</a
      ><a name="10720"
      > </a
      ><a name="10721" href="Stlc.html#19100" class="Datatype Operator"
      >&#8866;</a
      ><a name="10722"
      > </a
      ><a name="10723" href="StlcProp.html#10712" class="Bound"
      >t</a
      ><a name="10724"
      > </a
      ><a name="10725" href="Stlc.html#19100" class="Datatype Operator"
      >&#8758;</a
      ><a name="10726"
      > </a
      ><a name="10727" href="StlcProp.html#10714" class="Bound"
      >A</a
      ><a name="10728"
      > </a
      ><a name="10729" class="Symbol"
      >&#8594;</a
      ><a name="10730"
      > </a
      ><a name="10731" href="StlcProp.html#7410" class="Function"
      >Closed</a
      ><a name="10737"
      > </a
      ><a name="10738" href="StlcProp.html#10712" class="Bound"
      >t</a
      ><a name="10739"
      >
</a
      ><a name="10740" href="StlcProp.html#10696" class="Function"
      >&#8709;&#8866;-closed&#8242;</a
      ><a name="10750"
      > </a
      ><a name="10751" class="Symbol"
      >(</a
      ><a name="10752" href="Stlc.html#19144" class="InductiveConstructor"
      >var</a
      ><a name="10755"
      > </a
      ><a name="10756" href="StlcProp.html#10756" class="Bound"
      >x</a
      ><a name="10757"
      > </a
      ><a name="10758" class="Symbol"
      >())</a
      ><a name="10761"
      >
</a
      ><a name="10762" href="StlcProp.html#10696" class="Function"
      >&#8709;&#8866;-closed&#8242;</a
      ><a name="10772"
      > </a
      ><a name="10773" class="Symbol"
      >(</a
      ><a name="10774" href="Stlc.html#19353" class="InductiveConstructor"
      >app</a
      ><a name="10777"
      > </a
      ><a name="10778" href="StlcProp.html#10778" class="Bound"
      >t&#8321;&#8758;A&#8658;B</a
      ><a name="10784"
      > </a
      ><a name="10785" href="StlcProp.html#10785" class="Bound"
      >t&#8322;&#8758;A</a
      ><a name="10789" class="Symbol"
      >)</a
      ><a name="10790"
      > </a
      ><a name="10791" class="Symbol"
      >(</a
      ><a name="10792" href="StlcProp.html#7000" class="InductiveConstructor"
      >app1</a
      ><a name="10796"
      > </a
      ><a name="10797" href="StlcProp.html#10797" class="Bound"
      >x&#8712;t&#8321;</a
      ><a name="10801" class="Symbol"
      >)</a
      ><a name="10802"
      > </a
      ><a name="10803" class="Symbol"
      >=</a
      ><a name="10804"
      > </a
      ><a name="10805" href="StlcProp.html#10696" class="Function"
      >&#8709;&#8866;-closed&#8242;</a
      ><a name="10815"
      > </a
      ><a name="10816" href="StlcProp.html#10778" class="Bound"
      >t&#8321;&#8758;A&#8658;B</a
      ><a name="10822"
      > </a
      ><a name="10823" href="StlcProp.html#10797" class="Bound"
      >x&#8712;t&#8321;</a
      ><a name="10827"
      >
</a
      ><a name="10828" href="StlcProp.html#10696" class="Function"
      >&#8709;&#8866;-closed&#8242;</a
      ><a name="10838"
      > </a
      ><a name="10839" class="Symbol"
      >(</a
      ><a name="10840" href="Stlc.html#19353" class="InductiveConstructor"
      >app</a
      ><a name="10843"
      > </a
      ><a name="10844" href="StlcProp.html#10844" class="Bound"
      >t&#8321;&#8758;A&#8658;B</a
      ><a name="10850"
      > </a
      ><a name="10851" href="StlcProp.html#10851" class="Bound"
      >t&#8322;&#8758;A</a
      ><a name="10855" class="Symbol"
      >)</a
      ><a name="10856"
      > </a
      ><a name="10857" class="Symbol"
      >(</a
      ><a name="10858" href="StlcProp.html#7054" class="InductiveConstructor"
      >app2</a
      ><a name="10862"
      > </a
      ><a name="10863" href="StlcProp.html#10863" class="Bound"
      >x&#8712;t&#8322;</a
      ><a name="10867" class="Symbol"
      >)</a
      ><a name="10868"
      > </a
      ><a name="10869" class="Symbol"
      >=</a
      ><a name="10870"
      > </a
      ><a name="10871" href="StlcProp.html#10696" class="Function"
      >&#8709;&#8866;-closed&#8242;</a
      ><a name="10881"
      > </a
      ><a name="10882" href="StlcProp.html#10851" class="Bound"
      >t&#8322;&#8758;A</a
      ><a name="10886"
      > </a
      ><a name="10887" href="StlcProp.html#10863" class="Bound"
      >x&#8712;t&#8322;</a
      ><a name="10891"
      >
</a
      ><a name="10892" href="StlcProp.html#10696" class="Function"
      >&#8709;&#8866;-closed&#8242;</a
      ><a name="10902"
      > </a
      ><a name="10903" href="Stlc.html#19487" class="InductiveConstructor"
      >true</a
      ><a name="10907"
      >  </a
      ><a name="10909" class="Symbol"
      >()</a
      ><a name="10911"
      >
</a
      ><a name="10912" href="StlcProp.html#10696" class="Function"
      >&#8709;&#8866;-closed&#8242;</a
      ><a name="10922"
      > </a
      ><a name="10923" href="Stlc.html#19546" class="InductiveConstructor"
      >false</a
      ><a name="10928"
      > </a
      ><a name="10929" class="Symbol"
      >()</a
      ><a name="10931"
      >
</a
      ><a name="10932" href="StlcProp.html#10696" class="Function"
      >&#8709;&#8866;-closed&#8242;</a
      ><a name="10942"
      > </a
      ><a name="10943" class="Symbol"
      >(</a
      ><a name="10944" href="Stlc.html#19605" class="InductiveConstructor Operator"
      >if</a
      ><a name="10946"
      > </a
      ><a name="10947" href="StlcProp.html#10947" class="Bound"
      >t&#8321;&#8758;bool</a
      ><a name="10954"
      > </a
      ><a name="10955" href="Stlc.html#19605" class="InductiveConstructor Operator"
      >then</a
      ><a name="10959"
      > </a
      ><a name="10960" href="StlcProp.html#10960" class="Bound"
      >t&#8322;&#8758;A</a
      ><a name="10964"
      > </a
      ><a name="10965" href="Stlc.html#19605" class="InductiveConstructor Operator"
      >else</a
      ><a name="10969"
      > </a
      ><a name="10970" href="StlcProp.html#10970" class="Bound"
      >t&#8323;&#8758;A</a
      ><a name="10974" class="Symbol"
      >)</a
      ><a name="10975"
      > </a
      ><a name="10976" class="Symbol"
      >(</a
      ><a name="10977" href="StlcProp.html#7108" class="InductiveConstructor"
      >if1</a
      ><a name="10980"
      > </a
      ><a name="10981" href="StlcProp.html#10981" class="Bound"
      >x&#8712;t&#8321;</a
      ><a name="10985" class="Symbol"
      >)</a
      ><a name="10986"
      > </a
      ><a name="10987" class="Symbol"
      >=</a
      ><a name="10988"
      > </a
      ><a name="10989" href="StlcProp.html#10696" class="Function"
      >&#8709;&#8866;-closed&#8242;</a
      ><a name="10999"
      > </a
      ><a name="11000" href="StlcProp.html#10947" class="Bound"
      >t&#8321;&#8758;bool</a
      ><a name="11007"
      > </a
      ><a name="11008" href="StlcProp.html#10981" class="Bound"
      >x&#8712;t&#8321;</a
      ><a name="11012"
      >
</a
      ><a name="11013" href="StlcProp.html#10696" class="Function"
      >&#8709;&#8866;-closed&#8242;</a
      ><a name="11023"
      > </a
      ><a name="11024" class="Symbol"
      >(</a
      ><a name="11025" href="Stlc.html#19605" class="InductiveConstructor Operator"
      >if</a
      ><a name="11027"
      > </a
      ><a name="11028" href="StlcProp.html#11028" class="Bound"
      >t&#8321;&#8758;bool</a
      ><a name="11035"
      > </a
      ><a name="11036" href="Stlc.html#19605" class="InductiveConstructor Operator"
      >then</a
      ><a name="11040"
      > </a
      ><a name="11041" href="StlcProp.html#11041" class="Bound"
      >t&#8322;&#8758;A</a
      ><a name="11045"
      > </a
      ><a name="11046" href="Stlc.html#19605" class="InductiveConstructor Operator"
      >else</a
      ><a name="11050"
      > </a
      ><a name="11051" href="StlcProp.html#11051" class="Bound"
      >t&#8323;&#8758;A</a
      ><a name="11055" class="Symbol"
      >)</a
      ><a name="11056"
      > </a
      ><a name="11057" class="Symbol"
      >(</a
      ><a name="11058" href="StlcProp.html#7179" class="InductiveConstructor"
      >if2</a
      ><a name="11061"
      > </a
      ><a name="11062" href="StlcProp.html#11062" class="Bound"
      >x&#8712;t&#8322;</a
      ><a name="11066" class="Symbol"
      >)</a
      ><a name="11067"
      > </a
      ><a name="11068" class="Symbol"
      >=</a
      ><a name="11069"
      > </a
      ><a name="11070" href="StlcProp.html#10696" class="Function"
      >&#8709;&#8866;-closed&#8242;</a
      ><a name="11080"
      > </a
      ><a name="11081" href="StlcProp.html#11041" class="Bound"
      >t&#8322;&#8758;A</a
      ><a name="11085"
      > </a
      ><a name="11086" href="StlcProp.html#11062" class="Bound"
      >x&#8712;t&#8322;</a
      ><a name="11090"
      >
</a
      ><a name="11091" href="StlcProp.html#10696" class="Function"
      >&#8709;&#8866;-closed&#8242;</a
      ><a name="11101"
      > </a
      ><a name="11102" class="Symbol"
      >(</a
      ><a name="11103" href="Stlc.html#19605" class="InductiveConstructor Operator"
      >if</a
      ><a name="11105"
      > </a
      ><a name="11106" href="StlcProp.html#11106" class="Bound"
      >t&#8321;&#8758;bool</a
      ><a name="11113"
      > </a
      ><a name="11114" href="Stlc.html#19605" class="InductiveConstructor Operator"
      >then</a
      ><a name="11118"
      > </a
      ><a name="11119" href="StlcProp.html#11119" class="Bound"
      >t&#8322;&#8758;A</a
      ><a name="11123"
      > </a
      ><a name="11124" href="Stlc.html#19605" class="InductiveConstructor Operator"
      >else</a
      ><a name="11128"
      > </a
      ><a name="11129" href="StlcProp.html#11129" class="Bound"
      >t&#8323;&#8758;A</a
      ><a name="11133" class="Symbol"
      >)</a
      ><a name="11134"
      > </a
      ><a name="11135" class="Symbol"
      >(</a
      ><a name="11136" href="StlcProp.html#7250" class="InductiveConstructor"
      >if3</a
      ><a name="11139"
      > </a
      ><a name="11140" href="StlcProp.html#11140" class="Bound"
      >x&#8712;t&#8323;</a
      ><a name="11144" class="Symbol"
      >)</a
      ><a name="11145"
      > </a
      ><a name="11146" class="Symbol"
      >=</a
      ><a name="11147"
      > </a
      ><a name="11148" href="StlcProp.html#10696" class="Function"
      >&#8709;&#8866;-closed&#8242;</a
      ><a name="11158"
      > </a
      ><a name="11159" href="StlcProp.html#11129" class="Bound"
      >t&#8323;&#8758;A</a
      ><a name="11163"
      > </a
      ><a name="11164" href="StlcProp.html#11140" class="Bound"
      >x&#8712;t&#8323;</a
      ><a name="11168"
      >
</a
      ><a name="11169" href="StlcProp.html#10696" class="Function"
      >&#8709;&#8866;-closed&#8242;</a
      ><a name="11179"
      > </a
      ><a name="11180" class="Symbol"
      >(</a
      ><a name="11181" href="Stlc.html#19237" class="InductiveConstructor"
      >abs</a
      ><a name="11184"
      > </a
      ><a name="11185" class="Symbol"
      >{</a
      ><a name="11186" class="Argument"
      >x</a
      ><a name="11187"
      > </a
      ><a name="11188" class="Symbol"
      >=</a
      ><a name="11189"
      > </a
      ><a name="11190" href="StlcProp.html#11190" class="Bound"
      >x</a
      ><a name="11191" class="Symbol"
      >}</a
      ><a name="11192"
      > </a
      ><a name="11193" href="StlcProp.html#11193" class="Bound"
      >t&#8242;&#8758;A</a
      ><a name="11197" class="Symbol"
      >)</a
      ><a name="11198"
      > </a
      ><a name="11203" class="Symbol"
      >(</a
      ><a name="11204" href="StlcProp.html#6939" class="InductiveConstructor"
      >abs</a
      ><a name="11207"
      > </a
      ><a name="11208" href="StlcProp.html#11208" class="Bound"
      >x&#8800;y</a
      ><a name="11211"
      > </a
      ><a name="11212" href="StlcProp.html#11212" class="Bound"
      >y&#8712;t&#8242;</a
      ><a name="11216" class="Symbol"
      >)</a
      ><a name="11217"
      > </a
      ><a name="11218" class="Keyword"
      >with</a
      ><a name="11222"
      > </a
      ><a name="11223" href="StlcProp.html#8191" class="Function"
      >freeInCtxt</a
      ><a name="11233"
      > </a
      ><a name="11234" href="StlcProp.html#11212" class="Bound"
      >y&#8712;t&#8242;</a
      ><a name="11238"
      > </a
      ><a name="11239" href="StlcProp.html#11193" class="Bound"
      >t&#8242;&#8758;A</a
      ><a name="11243"
      >
</a
      ><a name="11244" href="StlcProp.html#10696" class="Function"
      >&#8709;&#8866;-closed&#8242;</a
      ><a name="11254"
      > </a
      ><a name="11255" class="Symbol"
      >(</a
      ><a name="11256" class="InductiveConstructor"
      >abs</a
      ><a name="11259"
      > </a
      ><a name="11260" class="Symbol"
      >{</a
      ><a name="11261" class="Argument"
      >x</a
      ><a name="11262"
      > </a
      ><a name="11263" class="Symbol"
      >=</a
      ><a name="11264"
      > </a
      ><a name="11265" href="StlcProp.html#11265" class="Bound"
      >x</a
      ><a name="11266" class="Symbol"
      >}</a
      ><a name="11267"
      > </a
      ><a name="11268" href="StlcProp.html#11268" class="Bound"
      >t&#8242;&#8758;A</a
      ><a name="11272" class="Symbol"
      >)</a
      ><a name="11273"
      > </a
      ><a name="11278" class="Symbol"
      >(</a
      ><a name="11279" class="InductiveConstructor"
      >abs</a
      ><a name="11282"
      > </a
      ><a name="11283" href="StlcProp.html#11283" class="Bound"
      >x&#8800;y</a
      ><a name="11286"
      > </a
      ><a name="11287" href="StlcProp.html#11287" class="Bound"
      >y&#8712;t&#8242;</a
      ><a name="11291" class="Symbol"
      >)</a
      ><a name="11292"
      > </a
      ><a name="11293" class="Symbol"
      >|</a
      ><a name="11294"
      > </a
      ><a name="11295" href="StlcProp.html#11295" class="Bound"
      >A</a
      ><a name="11296"
      > </a
      ><a name="11297" href="https://agda.github.io/agda-stdlib/Data.Product.html#509" class="InductiveConstructor Operator"
      >,</a
      ><a name="11298"
      > </a
      ><a name="11299" href="StlcProp.html#11299" class="Bound"
      >y&#8758;A</a
      ><a name="11302"
      > </a
      ><a name="11303" class="Keyword"
      >with</a
      ><a name="11307"
      > </a
      ><a name="11308" href="StlcProp.html#11265" class="Bound"
      >x</a
      ><a name="11309"
      > </a
      ><a name="11310" href="Maps.html#2329" class="Function Operator"
      >&#8799;</a
      ><a name="11311"
      > </a
      ><a name="11312" href="StlcProp.html#11275" class="Bound"
      >y</a
      ><a name="11313"
      >
</a
      ><a name="11314" href="StlcProp.html#10696" class="Function"
      >&#8709;&#8866;-closed&#8242;</a
      ><a name="11324"
      > </a
      ><a name="11325" class="Symbol"
      >(</a
      ><a name="11326" class="InductiveConstructor"
      >abs</a
      ><a name="11329"
      > </a
      ><a name="11330" class="Symbol"
      >{</a
      ><a name="11331" class="Argument"
      >x</a
      ><a name="11332"
      > </a
      ><a name="11333" class="Symbol"
      >=</a
      ><a name="11334"
      > </a
      ><a name="11335" href="StlcProp.html#11335" class="Bound"
      >x</a
      ><a name="11336" class="Symbol"
      >}</a
      ><a name="11337"
      > </a
      ><a name="11338" href="StlcProp.html#11338" class="Bound"
      >t&#8242;&#8758;A</a
      ><a name="11342" class="Symbol"
      >)</a
      ><a name="11343"
      > </a
      ><a name="11348" class="Symbol"
      >(</a
      ><a name="11349" class="InductiveConstructor"
      >abs</a
      ><a name="11352"
      > </a
      ><a name="11353" href="StlcProp.html#11353" class="Bound"
      >x&#8800;y</a
      ><a name="11356"
      > </a
      ><a name="11357" href="StlcProp.html#11357" class="Bound"
      >y&#8712;t&#8242;</a
      ><a name="11361" class="Symbol"
      >)</a
      ><a name="11362"
      > </a
      ><a name="11363" class="Symbol"
      >|</a
      ><a name="11364"
      > </a
      ><a name="11365" href="StlcProp.html#11365" class="Bound"
      >A</a
      ><a name="11366"
      > </a
      ><a name="11367" href="https://agda.github.io/agda-stdlib/Data.Product.html#509" class="InductiveConstructor Operator"
      >,</a
      ><a name="11368"
      > </a
      ><a name="11369" href="StlcProp.html#11369" class="Bound"
      >y&#8758;A</a
      ><a name="11372"
      > </a
      ><a name="11373" class="Symbol"
      >|</a
      ><a name="11374"
      > </a
      ><a name="11375" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#520" class="InductiveConstructor"
      >yes</a
      ><a name="11378"
      > </a
      ><a name="11379" href="StlcProp.html#11379" class="Bound"
      >x=y</a
      ><a name="11382"
      > </a
      ><a name="11383" class="Symbol"
      >=</a
      ><a name="11384"
      > </a
      ><a name="11385" href="StlcProp.html#11353" class="Bound"
      >x&#8800;y</a
      ><a name="11388"
      > </a
      ><a name="11389" href="StlcProp.html#11379" class="Bound"
      >x=y</a
      ><a name="11392"
      >
</a
      ><a name="11393" href="StlcProp.html#10696" class="Function"
      >&#8709;&#8866;-closed&#8242;</a
      ><a name="11403"
      > </a
      ><a name="11404" class="Symbol"
      >(</a
      ><a name="11405" class="InductiveConstructor"
      >abs</a
      ><a name="11408"
      > </a
      ><a name="11409" class="Symbol"
      >{</a
      ><a name="11410" class="Argument"
      >x</a
      ><a name="11411"
      > </a
      ><a name="11412" class="Symbol"
      >=</a
      ><a name="11413"
      > </a
      ><a name="11414" href="StlcProp.html#11414" class="Bound"
      >x</a
      ><a name="11415" class="Symbol"
      >}</a
      ><a name="11416"
      > </a
      ><a name="11417" href="StlcProp.html#11417" class="Bound"
      >t&#8242;&#8758;A</a
      ><a name="11421" class="Symbol"
      >)</a
      ><a name="11422"
      > </a
      ><a name="11427" class="Symbol"
      >(</a
      ><a name="11428" class="InductiveConstructor"
      >abs</a
      ><a name="11431"
      > </a
      ><a name="11432" href="StlcProp.html#11432" class="Bound"
      >x&#8800;y</a
      ><a name="11435"
      > </a
      ><a name="11436" href="StlcProp.html#11436" class="Bound"
      >y&#8712;t&#8242;</a
      ><a name="11440" class="Symbol"
      >)</a
      ><a name="11441"
      > </a
      ><a name="11442" class="Symbol"
      >|</a
      ><a name="11443"
      > </a
      ><a name="11444" href="StlcProp.html#11444" class="Bound"
      >A</a
      ><a name="11445"
      > </a
      ><a name="11446" href="https://agda.github.io/agda-stdlib/Data.Product.html#509" class="InductiveConstructor Operator"
      >,</a
      ><a name="11447"
      > </a
      ><a name="11448" class="Symbol"
      >()</a
      ><a name="11450"
      >  </a
      ><a name="11452" class="Symbol"
      >|</a
      ><a name="11453"
      > </a
      ><a name="11454" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#547" class="InductiveConstructor"
      >no</a
      ><a name="11456"
      >  </a
      ><a name="11458" class="Symbol"
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
<a name="11846" href="StlcProp.html#11846" class="Function"
      >replaceCtxt</a
      ><a name="11857"
      > </a
      ><a name="11858" class="Symbol"
      >:</a
      ><a name="11859"
      > </a
      ><a name="11860" class="Symbol"
      >&#8704;</a
      ><a name="11861"
      > </a
      ><a name="11885" class="Symbol"
      >&#8594;</a
      ><a name="11886"
      > </a
      ><a name="11887" class="Symbol"
      >(&#8704;</a
      ><a name="11889"
      > </a
      ><a name="11894" class="Symbol"
      >&#8594;</a
      ><a name="11895"
      > </a
      ><a name="11896" href="StlcProp.html#11891" class="Bound"
      >x</a
      ><a name="11897"
      > </a
      ><a name="11898" href="StlcProp.html#6876" class="Datatype Operator"
      >FreeIn</a
      ><a name="11904"
      > </a
      ><a name="11905" href="StlcProp.html#11868" class="Bound"
      >t</a
      ><a name="11906"
      > </a
      ><a name="11907" class="Symbol"
      >&#8594;</a
      ><a name="11908"
      > </a
      ><a name="11909" href="StlcProp.html#11863" class="Bound"
      >&#915;</a
      ><a name="11910"
      > </a
      ><a name="11911" href="StlcProp.html#11891" class="Bound"
      >x</a
      ><a name="11912"
      > </a
      ><a name="11913" href="Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="11914"
      > </a
      ><a name="11915" href="StlcProp.html#11865" class="Bound"
      >&#915;&#8242;</a
      ><a name="11917"
      > </a
      ><a name="11918" href="StlcProp.html#11891" class="Bound"
      >x</a
      ><a name="11919" class="Symbol"
      >)</a
      ><a name="11920"
      >
            </a
      ><a name="11933" class="Symbol"
      >&#8594;</a
      ><a name="11934"
      > </a
      ><a name="11935" href="StlcProp.html#11863" class="Bound"
      >&#915;</a
      ><a name="11936"
      >  </a
      ><a name="11938" href="Stlc.html#19100" class="Datatype Operator"
      >&#8866;</a
      ><a name="11939"
      > </a
      ><a name="11940" href="StlcProp.html#11868" class="Bound"
      >t</a
      ><a name="11941"
      > </a
      ><a name="11942" href="Stlc.html#19100" class="Datatype Operator"
      >&#8758;</a
      ><a name="11943"
      > </a
      ><a name="11944" href="StlcProp.html#11870" class="Bound"
      >A</a
      ><a name="11945"
      >
            </a
      ><a name="11958" class="Symbol"
      >&#8594;</a
      ><a name="11959"
      > </a
      ><a name="11960" href="StlcProp.html#11865" class="Bound"
      >&#915;&#8242;</a
      ><a name="11962"
      > </a
      ><a name="11963" href="Stlc.html#19100" class="Datatype Operator"
      >&#8866;</a
      ><a name="11964"
      > </a
      ><a name="11965" href="StlcProp.html#11868" class="Bound"
      >t</a
      ><a name="11966"
      > </a
      ><a name="11967" href="Stlc.html#19100" class="Datatype Operator"
      >&#8758;</a
      ><a name="11968"
      > </a
      ><a name="11969" href="StlcProp.html#11870" class="Bound"
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
<a name="14274" href="StlcProp.html#11846" class="Function"
      >replaceCtxt</a
      ><a name="14285"
      > </a
      ><a name="14286" href="StlcProp.html#14286" class="Bound"
      >f</a
      ><a name="14287"
      > </a
      ><a name="14288" class="Symbol"
      >(</a
      ><a name="14289" href="Stlc.html#19144" class="InductiveConstructor"
      >var</a
      ><a name="14292"
      > </a
      ><a name="14293" href="StlcProp.html#14293" class="Bound"
      >x</a
      ><a name="14294"
      > </a
      ><a name="14295" href="StlcProp.html#14295" class="Bound"
      >x&#8758;A</a
      ><a name="14298" class="Symbol"
      >)</a
      ><a name="14299"
      > </a
      ><a name="14300" class="Keyword"
      >rewrite</a
      ><a name="14307"
      > </a
      ><a name="14308" href="StlcProp.html#14286" class="Bound"
      >f</a
      ><a name="14309"
      > </a
      ><a name="14310" href="StlcProp.html#6915" class="InductiveConstructor"
      >var</a
      ><a name="14313"
      > </a
      ><a name="14314" class="Symbol"
      >=</a
      ><a name="14315"
      > </a
      ><a name="14316" href="Stlc.html#19144" class="InductiveConstructor"
      >var</a
      ><a name="14319"
      > </a
      ><a name="14320" href="StlcProp.html#14293" class="Bound"
      >x</a
      ><a name="14321"
      > </a
      ><a name="14322" href="StlcProp.html#14295" class="Bound"
      >x&#8758;A</a
      ><a name="14325"
      >
</a
      ><a name="14326" href="StlcProp.html#11846" class="Function"
      >replaceCtxt</a
      ><a name="14337"
      > </a
      ><a name="14338" href="StlcProp.html#14338" class="Bound"
      >f</a
      ><a name="14339"
      > </a
      ><a name="14340" class="Symbol"
      >(</a
      ><a name="14341" href="Stlc.html#19353" class="InductiveConstructor"
      >app</a
      ><a name="14344"
      > </a
      ><a name="14345" href="StlcProp.html#14345" class="Bound"
      >t&#8321;&#8758;A&#8658;B</a
      ><a name="14351"
      > </a
      ><a name="14352" href="StlcProp.html#14352" class="Bound"
      >t&#8322;&#8758;A</a
      ><a name="14356" class="Symbol"
      >)</a
      ><a name="14357"
      >
  </a
      ><a name="14360" class="Symbol"
      >=</a
      ><a name="14361"
      > </a
      ><a name="14362" href="Stlc.html#19353" class="InductiveConstructor"
      >app</a
      ><a name="14365"
      > </a
      ><a name="14366" class="Symbol"
      >(</a
      ><a name="14367" href="StlcProp.html#11846" class="Function"
      >replaceCtxt</a
      ><a name="14378"
      > </a
      ><a name="14379" class="Symbol"
      >(</a
      ><a name="14380" href="StlcProp.html#14338" class="Bound"
      >f</a
      ><a name="14381"
      > </a
      ><a name="14382" href="https://agda.github.io/agda-stdlib/Function.html#713" class="Function Operator"
      >&#8728;</a
      ><a name="14383"
      > </a
      ><a name="14384" href="StlcProp.html#7000" class="InductiveConstructor"
      >app1</a
      ><a name="14388" class="Symbol"
      >)</a
      ><a name="14389"
      > </a
      ><a name="14390" href="StlcProp.html#14345" class="Bound"
      >t&#8321;&#8758;A&#8658;B</a
      ><a name="14396" class="Symbol"
      >)</a
      ><a name="14397"
      > </a
      ><a name="14398" class="Symbol"
      >(</a
      ><a name="14399" href="StlcProp.html#11846" class="Function"
      >replaceCtxt</a
      ><a name="14410"
      > </a
      ><a name="14411" class="Symbol"
      >(</a
      ><a name="14412" href="StlcProp.html#14338" class="Bound"
      >f</a
      ><a name="14413"
      > </a
      ><a name="14414" href="https://agda.github.io/agda-stdlib/Function.html#713" class="Function Operator"
      >&#8728;</a
      ><a name="14415"
      > </a
      ><a name="14416" href="StlcProp.html#7054" class="InductiveConstructor"
      >app2</a
      ><a name="14420" class="Symbol"
      >)</a
      ><a name="14421"
      > </a
      ><a name="14422" href="StlcProp.html#14352" class="Bound"
      >t&#8322;&#8758;A</a
      ><a name="14426" class="Symbol"
      >)</a
      ><a name="14427"
      >
</a
      ><a name="14428" href="StlcProp.html#11846" class="Function"
      >replaceCtxt</a
      ><a name="14439"
      > </a
      ><a name="14449" href="StlcProp.html#14449" class="Bound"
      >f</a
      ><a name="14450"
      > </a
      ><a name="14451" class="Symbol"
      >(</a
      ><a name="14452" href="Stlc.html#19237" class="InductiveConstructor"
      >abs</a
      ><a name="14455"
      > </a
      ><a name="14478" href="StlcProp.html#14478" class="Bound"
      >t&#8242;&#8758;B</a
      ><a name="14482" class="Symbol"
      >)</a
      ><a name="14483"
      >
  </a
      ><a name="14486" class="Symbol"
      >=</a
      ><a name="14487"
      > </a
      ><a name="14488" href="Stlc.html#19237" class="InductiveConstructor"
      >abs</a
      ><a name="14491"
      > </a
      ><a name="14492" class="Symbol"
      >(</a
      ><a name="14493" href="StlcProp.html#11846" class="Function"
      >replaceCtxt</a
      ><a name="14504"
      > </a
      ><a name="14505" href="StlcProp.html#14526" class="Function"
      >f&#8242;</a
      ><a name="14507"
      > </a
      ><a name="14508" href="StlcProp.html#14478" class="Bound"
      >t&#8242;&#8758;B</a
      ><a name="14512" class="Symbol"
      >)</a
      ><a name="14513"
      >
  </a
      ><a name="14516" class="Keyword"
      >where</a
      ><a name="14521"
      >
    </a
      ><a name="14526" href="StlcProp.html#14526" class="Function"
      >f&#8242;</a
      ><a name="14528"
      > </a
      ><a name="14529" class="Symbol"
      >:</a
      ><a name="14530"
      > </a
      ><a name="14531" class="Symbol"
      >&#8704;</a
      ><a name="14532"
      > </a
      ><a name="14537" class="Symbol"
      >&#8594;</a
      ><a name="14538"
      > </a
      ><a name="14539" href="StlcProp.html#14534" class="Bound"
      >y</a
      ><a name="14540"
      > </a
      ><a name="14541" href="StlcProp.html#6876" class="Datatype Operator"
      >FreeIn</a
      ><a name="14547"
      > </a
      ><a name="14548" href="StlcProp.html#14474" class="Bound"
      >t&#8242;</a
      ><a name="14550"
      > </a
      ><a name="14551" class="Symbol"
      >&#8594;</a
      ><a name="14552"
      > </a
      ><a name="14553" class="Symbol"
      >(</a
      ><a name="14554" href="StlcProp.html#14441" class="Bound"
      >&#915;</a
      ><a name="14555"
      > </a
      ><a name="14556" href="Stlc.html#18199" class="Function Operator"
      >,</a
      ><a name="14557"
      > </a
      ><a name="14558" href="StlcProp.html#14462" class="Bound"
      >x</a
      ><a name="14559"
      > </a
      ><a name="14560" href="Stlc.html#18199" class="Function Operator"
      >&#8758;</a
      ><a name="14561"
      > </a
      ><a name="14562" href="StlcProp.html#14466" class="Bound"
      >A</a
      ><a name="14563" class="Symbol"
      >)</a
      ><a name="14564"
      > </a
      ><a name="14565" href="StlcProp.html#14534" class="Bound"
      >y</a
      ><a name="14566"
      > </a
      ><a name="14567" href="Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="14568"
      > </a
      ><a name="14569" class="Symbol"
      >(</a
      ><a name="14570" href="StlcProp.html#14445" class="Bound"
      >&#915;&#8242;</a
      ><a name="14572"
      > </a
      ><a name="14573" href="Stlc.html#18199" class="Function Operator"
      >,</a
      ><a name="14574"
      > </a
      ><a name="14575" href="StlcProp.html#14462" class="Bound"
      >x</a
      ><a name="14576"
      > </a
      ><a name="14577" href="Stlc.html#18199" class="Function Operator"
      >&#8758;</a
      ><a name="14578"
      > </a
      ><a name="14579" href="StlcProp.html#14466" class="Bound"
      >A</a
      ><a name="14580" class="Symbol"
      >)</a
      ><a name="14581"
      > </a
      ><a name="14582" href="StlcProp.html#14534" class="Bound"
      >y</a
      ><a name="14583"
      >
    </a
      ><a name="14588" href="StlcProp.html#14526" class="Function"
      >f&#8242;</a
      ><a name="14590"
      > </a
      ><a name="14595" href="StlcProp.html#14595" class="Bound"
      >y&#8712;t&#8242;</a
      ><a name="14599"
      > </a
      ><a name="14600" class="Keyword"
      >with</a
      ><a name="14604"
      > </a
      ><a name="14605" href="StlcProp.html#14462" class="Bound"
      >x</a
      ><a name="14606"
      > </a
      ><a name="14607" href="Maps.html#2329" class="Function Operator"
      >&#8799;</a
      ><a name="14608"
      > </a
      ><a name="14609" href="StlcProp.html#14592" class="Bound"
      >y</a
      ><a name="14610"
      >
    </a
      ><a name="14615" class="Symbol"
      >...</a
      ><a name="14618"
      > </a
      ><a name="14619" class="Symbol"
      >|</a
      ><a name="14620"
      > </a
      ><a name="14621" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#520" class="InductiveConstructor"
      >yes</a
      ><a name="14624"
      > </a
      ><a name="14625" class="Symbol"
      >_</a
      ><a name="14626"
      >   </a
      ><a name="14629" class="Symbol"
      >=</a
      ><a name="14630"
      > </a
      ><a name="14631" href="Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="14635"
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
      >x&#8800;y</a
      ><a name="14653"
      > </a
      ><a name="14654" class="Symbol"
      >=</a
      ><a name="14655"
      > </a
      ><a name="14656" href="StlcProp.html#14449" class="Bound"
      >f</a
      ><a name="14657"
      > </a
      ><a name="14658" class="Symbol"
      >(</a
      ><a name="14659" href="StlcProp.html#6939" class="InductiveConstructor"
      >abs</a
      ><a name="14662"
      > </a
      ><a name="14663" href="StlcProp.html#14650" class="Bound"
      >x&#8800;y</a
      ><a name="14666"
      > </a
      ><a name="14667" href="StlcProp.html#14595" class="Bound"
      >y&#8712;t&#8242;</a
      ><a name="14671" class="Symbol"
      >)</a
      ><a name="14672"
      >
</a
      ><a name="14673" href="StlcProp.html#11846" class="Function"
      >replaceCtxt</a
      ><a name="14684"
      > </a
      ><a name="14685" class="Symbol"
      >_</a
      ><a name="14686"
      > </a
      ><a name="14687" href="Stlc.html#19487" class="InductiveConstructor"
      >true</a
      ><a name="14691"
      >  </a
      ><a name="14693" class="Symbol"
      >=</a
      ><a name="14694"
      > </a
      ><a name="14695" href="Stlc.html#19487" class="InductiveConstructor"
      >true</a
      ><a name="14699"
      >
</a
      ><a name="14700" href="StlcProp.html#11846" class="Function"
      >replaceCtxt</a
      ><a name="14711"
      > </a
      ><a name="14712" class="Symbol"
      >_</a
      ><a name="14713"
      > </a
      ><a name="14714" href="Stlc.html#19546" class="InductiveConstructor"
      >false</a
      ><a name="14719"
      > </a
      ><a name="14720" class="Symbol"
      >=</a
      ><a name="14721"
      > </a
      ><a name="14722" href="Stlc.html#19546" class="InductiveConstructor"
      >false</a
      ><a name="14727"
      >
</a
      ><a name="14728" href="StlcProp.html#11846" class="Function"
      >replaceCtxt</a
      ><a name="14739"
      > </a
      ><a name="14740" href="StlcProp.html#14740" class="Bound"
      >f</a
      ><a name="14741"
      > </a
      ><a name="14742" class="Symbol"
      >(</a
      ><a name="14743" href="Stlc.html#19605" class="InductiveConstructor Operator"
      >if</a
      ><a name="14745"
      > </a
      ><a name="14746" href="StlcProp.html#14746" class="Bound"
      >t&#8321;&#8758;bool</a
      ><a name="14753"
      > </a
      ><a name="14754" href="Stlc.html#19605" class="InductiveConstructor Operator"
      >then</a
      ><a name="14758"
      > </a
      ><a name="14759" href="StlcProp.html#14759" class="Bound"
      >t&#8322;&#8758;A</a
      ><a name="14763"
      > </a
      ><a name="14764" href="Stlc.html#19605" class="InductiveConstructor Operator"
      >else</a
      ><a name="14768"
      > </a
      ><a name="14769" href="StlcProp.html#14769" class="Bound"
      >t&#8323;&#8758;A</a
      ><a name="14773" class="Symbol"
      >)</a
      ><a name="14774"
      >
  </a
      ><a name="14777" class="Symbol"
      >=</a
      ><a name="14778"
      > </a
      ><a name="14779" href="Stlc.html#19605" class="InductiveConstructor Operator"
      >if</a
      ><a name="14781"
      >   </a
      ><a name="14784" href="StlcProp.html#11846" class="Function"
      >replaceCtxt</a
      ><a name="14795"
      > </a
      ><a name="14796" class="Symbol"
      >(</a
      ><a name="14797" href="StlcProp.html#14740" class="Bound"
      >f</a
      ><a name="14798"
      > </a
      ><a name="14799" href="https://agda.github.io/agda-stdlib/Function.html#713" class="Function Operator"
      >&#8728;</a
      ><a name="14800"
      > </a
      ><a name="14801" href="StlcProp.html#7108" class="InductiveConstructor"
      >if1</a
      ><a name="14804" class="Symbol"
      >)</a
      ><a name="14805"
      > </a
      ><a name="14806" href="StlcProp.html#14746" class="Bound"
      >t&#8321;&#8758;bool</a
      ><a name="14813"
      >
    </a
      ><a name="14818" href="Stlc.html#19605" class="InductiveConstructor Operator"
      >then</a
      ><a name="14822"
      > </a
      ><a name="14823" href="StlcProp.html#11846" class="Function"
      >replaceCtxt</a
      ><a name="14834"
      > </a
      ><a name="14835" class="Symbol"
      >(</a
      ><a name="14836" href="StlcProp.html#14740" class="Bound"
      >f</a
      ><a name="14837"
      > </a
      ><a name="14838" href="https://agda.github.io/agda-stdlib/Function.html#713" class="Function Operator"
      >&#8728;</a
      ><a name="14839"
      > </a
      ><a name="14840" href="StlcProp.html#7179" class="InductiveConstructor"
      >if2</a
      ><a name="14843" class="Symbol"
      >)</a
      ><a name="14844"
      > </a
      ><a name="14845" href="StlcProp.html#14759" class="Bound"
      >t&#8322;&#8758;A</a
      ><a name="14849"
      >
    </a
      ><a name="14854" href="Stlc.html#19605" class="InductiveConstructor Operator"
      >else</a
      ><a name="14858"
      > </a
      ><a name="14859" href="StlcProp.html#11846" class="Function"
      >replaceCtxt</a
      ><a name="14870"
      > </a
      ><a name="14871" class="Symbol"
      >(</a
      ><a name="14872" href="StlcProp.html#14740" class="Bound"
      >f</a
      ><a name="14873"
      > </a
      ><a name="14874" href="https://agda.github.io/agda-stdlib/Function.html#713" class="Function Operator"
      >&#8728;</a
      ><a name="14875"
      > </a
      ><a name="14876" href="StlcProp.html#7250" class="InductiveConstructor"
      >if3</a
      ><a name="14879" class="Symbol"
      >)</a
      ><a name="14880"
      > </a
      ><a name="14881" href="StlcProp.html#14769" class="Bound"
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
<a name="15696" href="StlcProp.html#15696" class="Function"
      >[:=]-preserves-&#8866;</a
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
      ><a name="15748" class="Symbol"
      >&#8594;</a
      ><a name="15749"
      > </a
      ><a name="15750" href="Stlc.html#18168" class="Function"
      >&#8709;</a
      ><a name="15751"
      > </a
      ><a name="15752" href="Stlc.html#19100" class="Datatype Operator"
      >&#8866;</a
      ><a name="15753"
      > </a
      ><a name="15754" href="StlcProp.html#15726" class="Bound"
      >v</a
      ><a name="15755"
      > </a
      ><a name="15756" href="Stlc.html#19100" class="Datatype Operator"
      >&#8758;</a
      ><a name="15757"
      > </a
      ><a name="15758" href="StlcProp.html#15722" class="Bound"
      >A</a
      ><a name="15759"
      >
                 </a
      ><a name="15777" class="Symbol"
      >&#8594;</a
      ><a name="15778"
      > </a
      ><a name="15779" href="StlcProp.html#15718" class="Bound"
      >&#915;</a
      ><a name="15780"
      > </a
      ><a name="15781" href="Stlc.html#18199" class="Function Operator"
      >,</a
      ><a name="15782"
      > </a
      ><a name="15783" href="StlcProp.html#15720" class="Bound"
      >x</a
      ><a name="15784"
      > </a
      ><a name="15785" href="Stlc.html#18199" class="Function Operator"
      >&#8758;</a
      ><a name="15786"
      > </a
      ><a name="15787" href="StlcProp.html#15722" class="Bound"
      >A</a
      ><a name="15788"
      > </a
      ><a name="15789" href="Stlc.html#19100" class="Datatype Operator"
      >&#8866;</a
      ><a name="15790"
      > </a
      ><a name="15791" href="StlcProp.html#15724" class="Bound"
      >t</a
      ><a name="15792"
      > </a
      ><a name="15793" href="Stlc.html#19100" class="Datatype Operator"
      >&#8758;</a
      ><a name="15794"
      > </a
      ><a name="15795" href="StlcProp.html#15728" class="Bound"
      >B</a
      ><a name="15796"
      >
                 </a
      ><a name="15814" class="Symbol"
      >&#8594;</a
      ><a name="15815"
      > </a
      ><a name="15816" href="StlcProp.html#15718" class="Bound"
      >&#915;</a
      ><a name="15817"
      > </a
      ><a name="15818" href="Stlc.html#18199" class="Function Operator"
      >,</a
      ><a name="15819"
      > </a
      ><a name="15820" href="StlcProp.html#15720" class="Bound"
      >x</a
      ><a name="15821"
      > </a
      ><a name="15822" href="Stlc.html#18199" class="Function Operator"
      >&#8758;</a
      ><a name="15823"
      > </a
      ><a name="15824" href="StlcProp.html#15722" class="Bound"
      >A</a
      ><a name="15825"
      > </a
      ><a name="15826" href="Stlc.html#19100" class="Datatype Operator"
      >&#8866;</a
      ><a name="15827"
      > </a
      ><a name="15828" href="Stlc.html#12170" class="Function Operator"
      >[</a
      ><a name="15829"
      > </a
      ><a name="15830" href="StlcProp.html#15720" class="Bound"
      >x</a
      ><a name="15831"
      > </a
      ><a name="15832" href="Stlc.html#12170" class="Function Operator"
      >:=</a
      ><a name="15834"
      > </a
      ><a name="15835" href="StlcProp.html#15726" class="Bound"
      >v</a
      ><a name="15836"
      > </a
      ><a name="15837" href="Stlc.html#12170" class="Function Operator"
      >]</a
      ><a name="15838"
      > </a
      ><a name="15839" href="StlcProp.html#15724" class="Bound"
      >t</a
      ><a name="15840"
      > </a
      ><a name="15841" href="Stlc.html#19100" class="Datatype Operator"
      >&#8758;</a
      ><a name="15842"
      > </a
      ><a name="15843" href="StlcProp.html#15728" class="Bound"
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
<a name="19754" href="StlcProp.html#15696" class="Function"
      >[:=]-preserves-&#8866;</a
      ><a name="19770"
      > </a
      ><a name="19779" href="StlcProp.html#19779" class="Bound"
      >v&#8758;A</a
      ><a name="19782"
      > </a
      ><a name="19783" class="Symbol"
      >(</a
      ><a name="19784" href="Stlc.html#19144" class="InductiveConstructor"
      >var</a
      ><a name="19787"
      > </a
      ><a name="19788" href="StlcProp.html#19788" class="Bound"
      >y</a
      ><a name="19789"
      > </a
      ><a name="19790" href="StlcProp.html#19790" class="Bound"
      >y&#8712;&#915;</a
      ><a name="19793" class="Symbol"
      >)</a
      ><a name="19794"
      > </a
      ><a name="19795" class="Keyword"
      >with</a
      ><a name="19799"
      > </a
      ><a name="19800" href="StlcProp.html#19776" class="Bound"
      >x</a
      ><a name="19801"
      > </a
      ><a name="19802" href="Maps.html#2329" class="Function Operator"
      >&#8799;</a
      ><a name="19803"
      > </a
      ><a name="19804" href="StlcProp.html#19788" class="Bound"
      >y</a
      ><a name="19805"
      >
</a
      ><a name="19806" class="Symbol"
      >...</a
      ><a name="19809"
      > </a
      ><a name="19810" class="Symbol"
      >|</a
      ><a name="19811"
      > </a
      ><a name="19812" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#520" class="InductiveConstructor"
      >yes</a
      ><a name="19815"
      > </a
      ><a name="19816" href="StlcProp.html#19816" class="Bound"
      >x=y</a
      ><a name="19819"
      > </a
      ><a name="19820" class="Symbol"
      >=</a
      ><a name="19821"
      > </a
      ><a name="19822" class="Symbol"
      >{!!}</a
      ><a name="19826"
      >
</a
      ><a name="19827" class="Symbol"
      >...</a
      ><a name="19830"
      > </a
      ><a name="19831" class="Symbol"
      >|</a
      ><a name="19832"
      > </a
      ><a name="19833" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#547" class="InductiveConstructor"
      >no</a
      ><a name="19835"
      >  </a
      ><a name="19837" href="StlcProp.html#19837" class="Bound"
      >x&#8800;y</a
      ><a name="19840"
      > </a
      ><a name="19841" class="Symbol"
      >=</a
      ><a name="19842"
      > </a
      ><a name="19843" class="Symbol"
      >{!!}</a
      ><a name="19847"
      >
</a
      ><a name="19848" href="StlcProp.html#15696" class="Function"
      >[:=]-preserves-&#8866;</a
      ><a name="19864"
      > </a
      ><a name="19865" href="StlcProp.html#19865" class="Bound"
      >v&#8758;A</a
      ><a name="19868"
      > </a
      ><a name="19869" class="Symbol"
      >(</a
      ><a name="19870" href="Stlc.html#19237" class="InductiveConstructor"
      >abs</a
      ><a name="19873"
      > </a
      ><a name="19874" href="StlcProp.html#19874" class="Bound"
      >t&#8242;&#8758;B</a
      ><a name="19878" class="Symbol"
      >)</a
      ><a name="19879"
      > </a
      ><a name="19880" class="Symbol"
      >=</a
      ><a name="19881"
      > </a
      ><a name="19882" class="Symbol"
      >{!!}</a
      ><a name="19886"
      >
</a
      ><a name="19887" href="StlcProp.html#15696" class="Function"
      >[:=]-preserves-&#8866;</a
      ><a name="19903"
      > </a
      ><a name="19904" href="StlcProp.html#19904" class="Bound"
      >v&#8758;A</a
      ><a name="19907"
      > </a
      ><a name="19908" class="Symbol"
      >(</a
      ><a name="19909" href="Stlc.html#19353" class="InductiveConstructor"
      >app</a
      ><a name="19912"
      > </a
      ><a name="19913" href="StlcProp.html#19913" class="Bound"
      >t&#8321;&#8758;A&#8658;B</a
      ><a name="19919"
      > </a
      ><a name="19920" href="StlcProp.html#19920" class="Bound"
      >t&#8322;&#8758;A</a
      ><a name="19924" class="Symbol"
      >)</a
      ><a name="19925"
      > </a
      ><a name="19926" class="Symbol"
      >=</a
      ><a name="19927"
      >
  </a
      ><a name="19930" href="Stlc.html#19353" class="InductiveConstructor"
      >app</a
      ><a name="19933"
      > </a
      ><a name="19934" class="Symbol"
      >(</a
      ><a name="19935" href="StlcProp.html#15696" class="Function"
      >[:=]-preserves-&#8866;</a
      ><a name="19951"
      > </a
      ><a name="19952" href="StlcProp.html#19904" class="Bound"
      >v&#8758;A</a
      ><a name="19955"
      > </a
      ><a name="19956" href="StlcProp.html#19913" class="Bound"
      >t&#8321;&#8758;A&#8658;B</a
      ><a name="19962" class="Symbol"
      >)</a
      ><a name="19963"
      > </a
      ><a name="19964" class="Symbol"
      >(</a
      ><a name="19965" href="StlcProp.html#15696" class="Function"
      >[:=]-preserves-&#8866;</a
      ><a name="19981"
      > </a
      ><a name="19982" href="StlcProp.html#19904" class="Bound"
      >v&#8758;A</a
      ><a name="19985"
      > </a
      ><a name="19986" href="StlcProp.html#19920" class="Bound"
      >t&#8322;&#8758;A</a
      ><a name="19990" class="Symbol"
      >)</a
      ><a name="19991"
      >
</a
      ><a name="19992" href="StlcProp.html#15696" class="Function"
      >[:=]-preserves-&#8866;</a
      ><a name="20008"
      > </a
      ><a name="20009" href="StlcProp.html#20009" class="Bound"
      >v&#8758;A</a
      ><a name="20012"
      > </a
      ><a name="20013" href="Stlc.html#19487" class="InductiveConstructor"
      >true</a
      ><a name="20017"
      >  </a
      ><a name="20019" class="Symbol"
      >=</a
      ><a name="20020"
      > </a
      ><a name="20021" href="Stlc.html#19487" class="InductiveConstructor"
      >true</a
      ><a name="20025"
      >
</a
      ><a name="20026" href="StlcProp.html#15696" class="Function"
      >[:=]-preserves-&#8866;</a
      ><a name="20042"
      > </a
      ><a name="20043" href="StlcProp.html#20043" class="Bound"
      >v&#8758;A</a
      ><a name="20046"
      > </a
      ><a name="20047" href="Stlc.html#19546" class="InductiveConstructor"
      >false</a
      ><a name="20052"
      > </a
      ><a name="20053" class="Symbol"
      >=</a
      ><a name="20054"
      > </a
      ><a name="20055" href="Stlc.html#19546" class="InductiveConstructor"
      >false</a
      ><a name="20060"
      >
</a
      ><a name="20061" href="StlcProp.html#15696" class="Function"
      >[:=]-preserves-&#8866;</a
      ><a name="20077"
      > </a
      ><a name="20078" href="StlcProp.html#20078" class="Bound"
      >v&#8758;A</a
      ><a name="20081"
      > </a
      ><a name="20082" class="Symbol"
      >(</a
      ><a name="20083" href="Stlc.html#19605" class="InductiveConstructor Operator"
      >if</a
      ><a name="20085"
      > </a
      ><a name="20086" href="StlcProp.html#20086" class="Bound"
      >t&#8321;&#8758;bool</a
      ><a name="20093"
      > </a
      ><a name="20094" href="Stlc.html#19605" class="InductiveConstructor Operator"
      >then</a
      ><a name="20098"
      > </a
      ><a name="20099" href="StlcProp.html#20099" class="Bound"
      >t&#8322;&#8758;B</a
      ><a name="20103"
      > </a
      ><a name="20104" href="Stlc.html#19605" class="InductiveConstructor Operator"
      >else</a
      ><a name="20108"
      > </a
      ><a name="20109" href="StlcProp.html#20109" class="Bound"
      >t&#8323;&#8758;B</a
      ><a name="20113" class="Symbol"
      >)</a
      ><a name="20114"
      > </a
      ><a name="20115" class="Symbol"
      >=</a
      ><a name="20116"
      >
  </a
      ><a name="20119" href="Stlc.html#19605" class="InductiveConstructor Operator"
      >if</a
      ><a name="20121"
      >   </a
      ><a name="20124" href="StlcProp.html#15696" class="Function"
      >[:=]-preserves-&#8866;</a
      ><a name="20140"
      > </a
      ><a name="20141" href="StlcProp.html#20078" class="Bound"
      >v&#8758;A</a
      ><a name="20144"
      > </a
      ><a name="20145" href="StlcProp.html#20086" class="Bound"
      >t&#8321;&#8758;bool</a
      ><a name="20152"
      >
  </a
      ><a name="20155" href="Stlc.html#19605" class="InductiveConstructor Operator"
      >then</a
      ><a name="20159"
      > </a
      ><a name="20160" href="StlcProp.html#15696" class="Function"
      >[:=]-preserves-&#8866;</a
      ><a name="20176"
      > </a
      ><a name="20177" href="StlcProp.html#20078" class="Bound"
      >v&#8758;A</a
      ><a name="20180"
      > </a
      ><a name="20181" href="StlcProp.html#20099" class="Bound"
      >t&#8322;&#8758;B</a
      ><a name="20185"
      >
  </a
      ><a name="20188" href="Stlc.html#19605" class="InductiveConstructor Operator"
      >else</a
      ><a name="20192"
      > </a
      ><a name="20193" href="StlcProp.html#15696" class="Function"
      >[:=]-preserves-&#8866;</a
      ><a name="20209"
      > </a
      ><a name="20210" href="StlcProp.html#20078" class="Bound"
      >v&#8758;A</a
      ><a name="20213"
      > </a
      ><a name="20214" href="StlcProp.html#20109" class="Bound"
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
