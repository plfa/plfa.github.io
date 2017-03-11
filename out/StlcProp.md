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
      ><a name="458" href="Agda.Builtin.Equality.html#83" class="Datatype Operator"
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
      ><a name="468" href="Agda.Builtin.Equality.html#140" class="InductiveConstructor"
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
<a name="1065" href="StlcProp.html#1065" class="Function"
      >CanonicalForms</a
      ><a name="1079"
      > </a
      ><a name="1080" class="Symbol"
      >:</a
      ><a name="1081"
      > </a
      ><a name="1082" href="Stlc.html#5502" class="Datatype"
      >Term</a
      ><a name="1086"
      > </a
      ><a name="1087" class="Symbol"
      >&#8594;</a
      ><a name="1088"
      > </a
      ><a name="1089" href="Stlc.html#5387" class="Datatype"
      >Type</a
      ><a name="1093"
      > </a
      ><a name="1094" class="Symbol"
      >&#8594;</a
      ><a name="1095"
      > </a
      ><a name="1096" class="PrimitiveType"
      >Set</a
      ><a name="1099"
      >
</a
      ><a name="1100" href="StlcProp.html#1065" class="Function"
      >CanonicalForms</a
      ><a name="1114"
      > </a
      ><a name="1115" href="StlcProp.html#1115" class="Bound"
      >t</a
      ><a name="1116"
      > </a
      ><a name="1117" href="Stlc.html#5406" class="InductiveConstructor"
      >bool</a
      ><a name="1121"
      >    </a
      ><a name="1125" class="Symbol"
      >=</a
      ><a name="1126"
      > </a
      ><a name="1127" href="StlcProp.html#1115" class="Bound"
      >t</a
      ><a name="1128"
      > </a
      ><a name="1129" href="Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="1130"
      > </a
      ><a name="1131" href="Stlc.html#5604" class="InductiveConstructor"
      >true</a
      ><a name="1135"
      > </a
      ><a name="1136" href="https://agda.github.io/agda-stdlib/Data.Sum.html#433" class="Datatype Operator"
      >&#8846;</a
      ><a name="1137"
      > </a
      ><a name="1138" href="StlcProp.html#1115" class="Bound"
      >t</a
      ><a name="1139"
      > </a
      ><a name="1140" href="Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="1141"
      > </a
      ><a name="1142" href="Stlc.html#5619" class="InductiveConstructor"
      >false</a
      ><a name="1147"
      >
</a
      ><a name="1148" href="StlcProp.html#1065" class="Function"
      >CanonicalForms</a
      ><a name="1162"
      > </a
      ><a name="1163" href="StlcProp.html#1163" class="Bound"
      >t</a
      ><a name="1164"
      > </a
      ><a name="1165" class="Symbol"
      >(</a
      ><a name="1166" href="StlcProp.html#1166" class="Bound"
      >A</a
      ><a name="1167"
      > </a
      ><a name="1168" href="Stlc.html#5420" class="InductiveConstructor Operator"
      >&#8658;</a
      ><a name="1169"
      > </a
      ><a name="1170" href="StlcProp.html#1170" class="Bound"
      >B</a
      ><a name="1171" class="Symbol"
      >)</a
      ><a name="1172"
      > </a
      ><a name="1173" class="Symbol"
      >=</a
      ><a name="1174"
      > </a
      ><a name="1175" href="https://agda.github.io/agda-stdlib/Data.Product.html#949" class="Function"
      >&#8707;&#8322;</a
      ><a name="1177"
      > </a
      ><a name="1178" class="Symbol"
      >&#955;</a
      ><a name="1179"
      > </a
      ><a name="1180" href="StlcProp.html#1180" class="Bound"
      >x</a
      ><a name="1181"
      > </a
      ><a name="1182" href="StlcProp.html#1182" class="Bound"
      >t&#8242;</a
      ><a name="1184"
      > </a
      ><a name="1185" class="Symbol"
      >&#8594;</a
      ><a name="1186"
      > </a
      ><a name="1187" href="StlcProp.html#1163" class="Bound"
      >t</a
      ><a name="1188"
      > </a
      ><a name="1189" href="Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="1190"
      > </a
      ><a name="1191" href="Stlc.html#5570" class="InductiveConstructor"
      >abs</a
      ><a name="1194"
      > </a
      ><a name="1195" href="StlcProp.html#1180" class="Bound"
      >x</a
      ><a name="1196"
      > </a
      ><a name="1197" href="StlcProp.html#1166" class="Bound"
      >A</a
      ><a name="1198"
      > </a
      ><a name="1199" href="StlcProp.html#1182" class="Bound"
      >t&#8242;</a
      ><a name="1201"
      >

</a
      ><a name="1203" href="StlcProp.html#1203" class="Function"
      >canonicalForms</a
      ><a name="1217"
      > </a
      ><a name="1218" class="Symbol"
      >:</a
      ><a name="1219"
      > </a
      ><a name="1220" class="Symbol"
      >&#8704;</a
      ><a name="1221"
      > </a
      ><a name="1228" class="Symbol"
      >&#8594;</a
      ><a name="1229"
      > </a
      ><a name="1230" href="Stlc.html#18127" class="Function"
      >&#8709;</a
      ><a name="1231"
      > </a
      ><a name="1232" href="Stlc.html#19059" class="Datatype Operator"
      >&#8866;</a
      ><a name="1233"
      > </a
      ><a name="1234" href="StlcProp.html#1223" class="Bound"
      >t</a
      ><a name="1235"
      > </a
      ><a name="1236" href="Stlc.html#19059" class="Datatype Operator"
      >&#8758;</a
      ><a name="1237"
      > </a
      ><a name="1238" href="StlcProp.html#1225" class="Bound"
      >A</a
      ><a name="1239"
      > </a
      ><a name="1240" class="Symbol"
      >&#8594;</a
      ><a name="1241"
      > </a
      ><a name="1242" href="Stlc.html#8909" class="Datatype"
      >Value</a
      ><a name="1247"
      > </a
      ><a name="1248" href="StlcProp.html#1223" class="Bound"
      >t</a
      ><a name="1249"
      > </a
      ><a name="1250" class="Symbol"
      >&#8594;</a
      ><a name="1251"
      > </a
      ><a name="1252" href="StlcProp.html#1065" class="Function"
      >CanonicalForms</a
      ><a name="1266"
      > </a
      ><a name="1267" href="StlcProp.html#1223" class="Bound"
      >t</a
      ><a name="1268"
      > </a
      ><a name="1269" href="StlcProp.html#1225" class="Bound"
      >A</a
      ><a name="1270"
      >
</a
      ><a name="1271" href="StlcProp.html#1203" class="Function"
      >canonicalForms</a
      ><a name="1285"
      > </a
      ><a name="1286" class="Symbol"
      >(</a
      ><a name="1287" href="Stlc.html#19196" class="InductiveConstructor"
      >abs</a
      ><a name="1290"
      > </a
      ><a name="1291" href="StlcProp.html#1291" class="Bound"
      >t&#8242;</a
      ><a name="1293" class="Symbol"
      >)</a
      ><a name="1294"
      > </a
      ><a name="1295" href="Stlc.html#8936" class="InductiveConstructor"
      >abs</a
      ><a name="1298"
      >   </a
      ><a name="1301" class="Symbol"
      >=</a
      ><a name="1302"
      > </a
      ><a name="1303" class="Symbol"
      >_</a
      ><a name="1304"
      > </a
      ><a name="1305" href="https://agda.github.io/agda-stdlib/Data.Product.html#509" class="InductiveConstructor Operator"
      >,</a
      ><a name="1306"
      > </a
      ><a name="1307" class="Symbol"
      >_</a
      ><a name="1308"
      > </a
      ><a name="1309" href="https://agda.github.io/agda-stdlib/Data.Product.html#509" class="InductiveConstructor Operator"
      >,</a
      ><a name="1310"
      > </a
      ><a name="1311" href="Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="1315"
      >
</a
      ><a name="1316" href="StlcProp.html#1203" class="Function"
      >canonicalForms</a
      ><a name="1330"
      > </a
      ><a name="1331" href="Stlc.html#19446" class="InductiveConstructor"
      >true</a
      ><a name="1335"
      >     </a
      ><a name="1340" href="Stlc.html#8984" class="InductiveConstructor"
      >true</a
      ><a name="1344"
      >  </a
      ><a name="1346" class="Symbol"
      >=</a
      ><a name="1347"
      > </a
      ><a name="1348" href="https://agda.github.io/agda-stdlib/Data.Sum.html#489" class="InductiveConstructor"
      >inj&#8321;</a
      ><a name="1352"
      > </a
      ><a name="1353" href="Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="1357"
      >
</a
      ><a name="1358" href="StlcProp.html#1203" class="Function"
      >canonicalForms</a
      ><a name="1372"
      > </a
      ><a name="1373" href="Stlc.html#19505" class="InductiveConstructor"
      >false</a
      ><a name="1378"
      >    </a
      ><a name="1382" href="Stlc.html#9005" class="InductiveConstructor"
      >false</a
      ><a name="1387"
      > </a
      ><a name="1388" class="Symbol"
      >=</a
      ><a name="1389"
      > </a
      ><a name="1390" href="https://agda.github.io/agda-stdlib/Data.Sum.html#514" class="InductiveConstructor"
      >inj&#8322;</a
      ><a name="1394"
      > </a
      ><a name="1395" href="Agda.Builtin.Equality.html#140" class="InductiveConstructor"
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
<a name="1778" href="StlcProp.html#1778" class="Function"
      >progress</a
      ><a name="1786"
      > </a
      ><a name="1787" class="Symbol"
      >:</a
      ><a name="1788"
      > </a
      ><a name="1789" class="Symbol"
      >&#8704;</a
      ><a name="1790"
      > </a
      ><a name="1797" class="Symbol"
      >&#8594;</a
      ><a name="1798"
      > </a
      ><a name="1799" href="Stlc.html#18127" class="Function"
      >&#8709;</a
      ><a name="1800"
      > </a
      ><a name="1801" href="Stlc.html#19059" class="Datatype Operator"
      >&#8866;</a
      ><a name="1802"
      > </a
      ><a name="1803" href="StlcProp.html#1792" class="Bound"
      >t</a
      ><a name="1804"
      > </a
      ><a name="1805" href="Stlc.html#19059" class="Datatype Operator"
      >&#8758;</a
      ><a name="1806"
      > </a
      ><a name="1807" href="StlcProp.html#1794" class="Bound"
      >A</a
      ><a name="1808"
      > </a
      ><a name="1809" class="Symbol"
      >&#8594;</a
      ><a name="1810"
      > </a
      ><a name="1811" href="Stlc.html#8909" class="Datatype"
      >Value</a
      ><a name="1816"
      > </a
      ><a name="1817" href="StlcProp.html#1792" class="Bound"
      >t</a
      ><a name="1818"
      > </a
      ><a name="1819" href="https://agda.github.io/agda-stdlib/Data.Sum.html#433" class="Datatype Operator"
      >&#8846;</a
      ><a name="1820"
      > </a
      ><a name="1821" href="https://agda.github.io/agda-stdlib/Data.Product.html#823" class="Function"
      >&#8707;</a
      ><a name="1822"
      > </a
      ><a name="1823" class="Symbol"
      >&#955;</a
      ><a name="1824"
      > </a
      ><a name="1825" href="StlcProp.html#1825" class="Bound"
      >t&#8242;</a
      ><a name="1827"
      > </a
      ><a name="1828" class="Symbol"
      >&#8594;</a
      ><a name="1829"
      > </a
      ><a name="1830" href="StlcProp.html#1792" class="Bound"
      >t</a
      ><a name="1831"
      > </a
      ><a name="1832" href="Stlc.html#15045" class="Datatype Operator"
      >==&gt;</a
      ><a name="1835"
      > </a
      ><a name="1836" href="StlcProp.html#1825" class="Bound"
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
<a name="3537" href="StlcProp.html#1778" class="Function"
      >progress</a
      ><a name="3545"
      > </a
      ><a name="3546" class="Symbol"
      >(</a
      ><a name="3547" href="Stlc.html#19103" class="InductiveConstructor"
      >var</a
      ><a name="3550"
      > </a
      ><a name="3551" href="StlcProp.html#3551" class="Bound"
      >x</a
      ><a name="3552"
      > </a
      ><a name="3553" class="Symbol"
      >())</a
      ><a name="3556"
      >
</a
      ><a name="3557" href="StlcProp.html#1778" class="Function"
      >progress</a
      ><a name="3565"
      > </a
      ><a name="3566" href="Stlc.html#19446" class="InductiveConstructor"
      >true</a
      ><a name="3570"
      >      </a
      ><a name="3576" class="Symbol"
      >=</a
      ><a name="3577"
      > </a
      ><a name="3578" href="https://agda.github.io/agda-stdlib/Data.Sum.html#489" class="InductiveConstructor"
      >inj&#8321;</a
      ><a name="3582"
      > </a
      ><a name="3583" href="Stlc.html#8984" class="InductiveConstructor"
      >true</a
      ><a name="3587"
      >
</a
      ><a name="3588" href="StlcProp.html#1778" class="Function"
      >progress</a
      ><a name="3596"
      > </a
      ><a name="3597" href="Stlc.html#19505" class="InductiveConstructor"
      >false</a
      ><a name="3602"
      >     </a
      ><a name="3607" class="Symbol"
      >=</a
      ><a name="3608"
      > </a
      ><a name="3609" href="https://agda.github.io/agda-stdlib/Data.Sum.html#489" class="InductiveConstructor"
      >inj&#8321;</a
      ><a name="3613"
      > </a
      ><a name="3614" href="Stlc.html#9005" class="InductiveConstructor"
      >false</a
      ><a name="3619"
      >
</a
      ><a name="3620" href="StlcProp.html#1778" class="Function"
      >progress</a
      ><a name="3628"
      > </a
      ><a name="3629" class="Symbol"
      >(</a
      ><a name="3630" href="Stlc.html#19196" class="InductiveConstructor"
      >abs</a
      ><a name="3633"
      > </a
      ><a name="3634" href="StlcProp.html#3634" class="Bound"
      >t&#8758;A</a
      ><a name="3637" class="Symbol"
      >)</a
      ><a name="3638"
      > </a
      ><a name="3639" class="Symbol"
      >=</a
      ><a name="3640"
      > </a
      ><a name="3641" href="https://agda.github.io/agda-stdlib/Data.Sum.html#489" class="InductiveConstructor"
      >inj&#8321;</a
      ><a name="3645"
      > </a
      ><a name="3646" href="Stlc.html#8936" class="InductiveConstructor"
      >abs</a
      ><a name="3649"
      >
</a
      ><a name="3650" href="StlcProp.html#1778" class="Function"
      >progress</a
      ><a name="3658"
      > </a
      ><a name="3659" class="Symbol"
      >(</a
      ><a name="3660" href="Stlc.html#19312" class="InductiveConstructor"
      >app</a
      ><a name="3663"
      > </a
      ><a name="3664" href="StlcProp.html#3664" class="Bound"
      >t&#8321;&#8758;A&#8658;B</a
      ><a name="3670"
      > </a
      ><a name="3671" href="StlcProp.html#3671" class="Bound"
      >t&#8322;&#8758;B</a
      ><a name="3675" class="Symbol"
      >)</a
      ><a name="3676"
      >
    </a
      ><a name="3681" class="Keyword"
      >with</a
      ><a name="3685"
      > </a
      ><a name="3686" href="StlcProp.html#1778" class="Function"
      >progress</a
      ><a name="3694"
      > </a
      ><a name="3695" href="StlcProp.html#3664" class="Bound"
      >t&#8321;&#8758;A&#8658;B</a
      ><a name="3701"
      >
</a
      ><a name="3702" class="Symbol"
      >...</a
      ><a name="3705"
      > </a
      ><a name="3706" class="Symbol"
      >|</a
      ><a name="3707"
      > </a
      ><a name="3708" href="https://agda.github.io/agda-stdlib/Data.Sum.html#514" class="InductiveConstructor"
      >inj&#8322;</a
      ><a name="3712"
      > </a
      ><a name="3713" class="Symbol"
      >(_</a
      ><a name="3715"
      > </a
      ><a name="3716" href="https://agda.github.io/agda-stdlib/Data.Product.html#509" class="InductiveConstructor Operator"
      >,</a
      ><a name="3717"
      > </a
      ><a name="3718" href="StlcProp.html#3718" class="Bound"
      >t&#8321;&#8658;t&#8321;&#8242;</a
      ><a name="3724" class="Symbol"
      >)</a
      ><a name="3725"
      > </a
      ><a name="3726" class="Symbol"
      >=</a
      ><a name="3727"
      > </a
      ><a name="3728" href="https://agda.github.io/agda-stdlib/Data.Sum.html#514" class="InductiveConstructor"
      >inj&#8322;</a
      ><a name="3732"
      > </a
      ><a name="3733" class="Symbol"
      >(_</a
      ><a name="3735"
      > </a
      ><a name="3736" href="https://agda.github.io/agda-stdlib/Data.Product.html#509" class="InductiveConstructor Operator"
      >,</a
      ><a name="3737"
      > </a
      ><a name="3738" href="Stlc.html#15170" class="InductiveConstructor"
      >app1</a
      ><a name="3742"
      > </a
      ><a name="3743" href="StlcProp.html#3718" class="Bound"
      >t&#8321;&#8658;t&#8321;&#8242;</a
      ><a name="3749" class="Symbol"
      >)</a
      ><a name="3750"
      >
</a
      ><a name="3751" class="Symbol"
      >...</a
      ><a name="3754"
      > </a
      ><a name="3755" class="Symbol"
      >|</a
      ><a name="3756"
      > </a
      ><a name="3757" href="https://agda.github.io/agda-stdlib/Data.Sum.html#489" class="InductiveConstructor"
      >inj&#8321;</a
      ><a name="3761"
      > </a
      ><a name="3762" href="StlcProp.html#3762" class="Bound"
      >v&#8321;</a
      ><a name="3764"
      >
    </a
      ><a name="3769" class="Keyword"
      >with</a
      ><a name="3773"
      > </a
      ><a name="3774" href="StlcProp.html#1778" class="Function"
      >progress</a
      ><a name="3782"
      > </a
      ><a name="3783" href="StlcProp.html#3671" class="Bound"
      >t&#8322;&#8758;B</a
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
      ><a name="3794" href="https://agda.github.io/agda-stdlib/Data.Sum.html#514" class="InductiveConstructor"
      >inj&#8322;</a
      ><a name="3798"
      > </a
      ><a name="3799" class="Symbol"
      >(_</a
      ><a name="3801"
      > </a
      ><a name="3802" href="https://agda.github.io/agda-stdlib/Data.Product.html#509" class="InductiveConstructor Operator"
      >,</a
      ><a name="3803"
      > </a
      ><a name="3804" href="StlcProp.html#3804" class="Bound"
      >t&#8322;&#8658;t&#8322;&#8242;</a
      ><a name="3810" class="Symbol"
      >)</a
      ><a name="3811"
      > </a
      ><a name="3812" class="Symbol"
      >=</a
      ><a name="3813"
      > </a
      ><a name="3814" href="https://agda.github.io/agda-stdlib/Data.Sum.html#514" class="InductiveConstructor"
      >inj&#8322;</a
      ><a name="3818"
      > </a
      ><a name="3819" class="Symbol"
      >(_</a
      ><a name="3821"
      > </a
      ><a name="3822" href="https://agda.github.io/agda-stdlib/Data.Product.html#509" class="InductiveConstructor Operator"
      >,</a
      ><a name="3823"
      > </a
      ><a name="3824" href="Stlc.html#15247" class="InductiveConstructor"
      >app2</a
      ><a name="3828"
      > </a
      ><a name="3829" href="StlcProp.html#3762" class="Bound"
      >v&#8321;</a
      ><a name="3831"
      > </a
      ><a name="3832" href="StlcProp.html#3804" class="Bound"
      >t&#8322;&#8658;t&#8322;&#8242;</a
      ><a name="3838" class="Symbol"
      >)</a
      ><a name="3839"
      >
</a
      ><a name="3840" class="Symbol"
      >...</a
      ><a name="3843"
      > </a
      ><a name="3844" class="Symbol"
      >|</a
      ><a name="3845"
      > </a
      ><a name="3846" href="https://agda.github.io/agda-stdlib/Data.Sum.html#489" class="InductiveConstructor"
      >inj&#8321;</a
      ><a name="3850"
      > </a
      ><a name="3851" href="StlcProp.html#3851" class="Bound"
      >v&#8322;</a
      ><a name="3853"
      >
    </a
      ><a name="3858" class="Keyword"
      >with</a
      ><a name="3862"
      > </a
      ><a name="3863" href="StlcProp.html#1203" class="Function"
      >canonicalForms</a
      ><a name="3877"
      > </a
      ><a name="3878" href="StlcProp.html#3664" class="Bound"
      >t&#8321;&#8758;A&#8658;B</a
      ><a name="3884"
      > </a
      ><a name="3885" href="StlcProp.html#3762" class="Bound"
      >v&#8321;</a
      ><a name="3887"
      >
</a
      ><a name="3888" class="Symbol"
      >...</a
      ><a name="3891"
      > </a
      ><a name="3892" class="Symbol"
      >|</a
      ><a name="3893"
      > </a
      ><a name="3894" class="Symbol"
      >(_</a
      ><a name="3896"
      > </a
      ><a name="3897" href="https://agda.github.io/agda-stdlib/Data.Product.html#509" class="InductiveConstructor Operator"
      >,</a
      ><a name="3898"
      > </a
      ><a name="3899" class="Symbol"
      >_</a
      ><a name="3900"
      > </a
      ><a name="3901" href="https://agda.github.io/agda-stdlib/Data.Product.html#509" class="InductiveConstructor Operator"
      >,</a
      ><a name="3902"
      > </a
      ><a name="3903" href="Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="3907" class="Symbol"
      >)</a
      ><a name="3908"
      > </a
      ><a name="3909" class="Symbol"
      >=</a
      ><a name="3910"
      > </a
      ><a name="3911" href="https://agda.github.io/agda-stdlib/Data.Sum.html#514" class="InductiveConstructor"
      >inj&#8322;</a
      ><a name="3915"
      > </a
      ><a name="3916" class="Symbol"
      >(_</a
      ><a name="3918"
      > </a
      ><a name="3919" href="https://agda.github.io/agda-stdlib/Data.Product.html#509" class="InductiveConstructor Operator"
      >,</a
      ><a name="3920"
      > </a
      ><a name="3921" href="Stlc.html#15079" class="InductiveConstructor"
      >red</a
      ><a name="3924"
      > </a
      ><a name="3925" href="StlcProp.html#3851" class="Bound"
      >v&#8322;</a
      ><a name="3927" class="Symbol"
      >)</a
      ><a name="3928"
      >
</a
      ><a name="3929" href="StlcProp.html#1778" class="Function"
      >progress</a
      ><a name="3937"
      > </a
      ><a name="3938" class="Symbol"
      >(</a
      ><a name="3939" href="Stlc.html#19564" class="InductiveConstructor Operator"
      >if</a
      ><a name="3941"
      > </a
      ><a name="3942" href="StlcProp.html#3942" class="Bound"
      >t&#8321;&#8758;bool</a
      ><a name="3949"
      > </a
      ><a name="3950" href="Stlc.html#19564" class="InductiveConstructor Operator"
      >then</a
      ><a name="3954"
      > </a
      ><a name="3955" href="StlcProp.html#3955" class="Bound"
      >t&#8322;&#8758;A</a
      ><a name="3959"
      > </a
      ><a name="3960" href="Stlc.html#19564" class="InductiveConstructor Operator"
      >else</a
      ><a name="3964"
      > </a
      ><a name="3965" href="StlcProp.html#3965" class="Bound"
      >t&#8323;&#8758;A</a
      ><a name="3969" class="Symbol"
      >)</a
      ><a name="3970"
      >
    </a
      ><a name="3975" class="Keyword"
      >with</a
      ><a name="3979"
      > </a
      ><a name="3980" href="StlcProp.html#1778" class="Function"
      >progress</a
      ><a name="3988"
      > </a
      ><a name="3989" href="StlcProp.html#3942" class="Bound"
      >t&#8321;&#8758;bool</a
      ><a name="3996"
      >
</a
      ><a name="3997" class="Symbol"
      >...</a
      ><a name="4000"
      > </a
      ><a name="4001" class="Symbol"
      >|</a
      ><a name="4002"
      > </a
      ><a name="4003" href="https://agda.github.io/agda-stdlib/Data.Sum.html#514" class="InductiveConstructor"
      >inj&#8322;</a
      ><a name="4007"
      > </a
      ><a name="4008" class="Symbol"
      >(_</a
      ><a name="4010"
      > </a
      ><a name="4011" href="https://agda.github.io/agda-stdlib/Data.Product.html#509" class="InductiveConstructor Operator"
      >,</a
      ><a name="4012"
      > </a
      ><a name="4013" href="StlcProp.html#4013" class="Bound"
      >t&#8321;&#8658;t&#8321;&#8242;</a
      ><a name="4019" class="Symbol"
      >)</a
      ><a name="4020"
      > </a
      ><a name="4021" class="Symbol"
      >=</a
      ><a name="4022"
      > </a
      ><a name="4023" href="https://agda.github.io/agda-stdlib/Data.Sum.html#514" class="InductiveConstructor"
      >inj&#8322;</a
      ><a name="4027"
      > </a
      ><a name="4028" class="Symbol"
      >(_</a
      ><a name="4030"
      > </a
      ><a name="4031" href="https://agda.github.io/agda-stdlib/Data.Product.html#509" class="InductiveConstructor Operator"
      >,</a
      ><a name="4032"
      > </a
      ><a name="4033" href="Stlc.html#15344" class="InductiveConstructor"
      >if</a
      ><a name="4035"
      > </a
      ><a name="4036" href="StlcProp.html#4013" class="Bound"
      >t&#8321;&#8658;t&#8321;&#8242;</a
      ><a name="4042" class="Symbol"
      >)</a
      ><a name="4043"
      >
</a
      ><a name="4044" class="Symbol"
      >...</a
      ><a name="4047"
      > </a
      ><a name="4048" class="Symbol"
      >|</a
      ><a name="4049"
      > </a
      ><a name="4050" href="https://agda.github.io/agda-stdlib/Data.Sum.html#489" class="InductiveConstructor"
      >inj&#8321;</a
      ><a name="4054"
      > </a
      ><a name="4055" href="StlcProp.html#4055" class="Bound"
      >v&#8321;</a
      ><a name="4057"
      >
    </a
      ><a name="4062" class="Keyword"
      >with</a
      ><a name="4066"
      > </a
      ><a name="4067" href="StlcProp.html#1203" class="Function"
      >canonicalForms</a
      ><a name="4081"
      > </a
      ><a name="4082" href="StlcProp.html#3942" class="Bound"
      >t&#8321;&#8758;bool</a
      ><a name="4089"
      > </a
      ><a name="4090" href="StlcProp.html#4055" class="Bound"
      >v&#8321;</a
      ><a name="4092"
      >
</a
      ><a name="4093" class="Symbol"
      >...</a
      ><a name="4096"
      > </a
      ><a name="4097" class="Symbol"
      >|</a
      ><a name="4098"
      > </a
      ><a name="4099" href="https://agda.github.io/agda-stdlib/Data.Sum.html#489" class="InductiveConstructor"
      >inj&#8321;</a
      ><a name="4103"
      > </a
      ><a name="4104" href="Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="4108"
      > </a
      ><a name="4109" class="Symbol"
      >=</a
      ><a name="4110"
      > </a
      ><a name="4111" href="https://agda.github.io/agda-stdlib/Data.Sum.html#514" class="InductiveConstructor"
      >inj&#8322;</a
      ><a name="4115"
      > </a
      ><a name="4116" class="Symbol"
      >(_</a
      ><a name="4118"
      > </a
      ><a name="4119" href="https://agda.github.io/agda-stdlib/Data.Product.html#509" class="InductiveConstructor Operator"
      >,</a
      ><a name="4120"
      > </a
      ><a name="4121" href="Stlc.html#15445" class="InductiveConstructor"
      >iftrue</a
      ><a name="4127" class="Symbol"
      >)</a
      ><a name="4128"
      >
</a
      ><a name="4129" class="Symbol"
      >...</a
      ><a name="4132"
      > </a
      ><a name="4133" class="Symbol"
      >|</a
      ><a name="4134"
      > </a
      ><a name="4135" href="https://agda.github.io/agda-stdlib/Data.Sum.html#514" class="InductiveConstructor"
      >inj&#8322;</a
      ><a name="4139"
      > </a
      ><a name="4140" href="Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="4144"
      > </a
      ><a name="4145" class="Symbol"
      >=</a
      ><a name="4146"
      > </a
      ><a name="4147" href="https://agda.github.io/agda-stdlib/Data.Sum.html#514" class="InductiveConstructor"
      >inj&#8322;</a
      ><a name="4151"
      > </a
      ><a name="4152" class="Symbol"
      >(_</a
      ><a name="4154"
      > </a
      ><a name="4155" href="https://agda.github.io/agda-stdlib/Data.Product.html#509" class="InductiveConstructor Operator"
      >,</a
      ><a name="4156"
      > </a
      ><a name="4157" href="Stlc.html#15505" class="InductiveConstructor"
      >iffalse</a
      ><a name="4164" class="Symbol"
      >)</a
      >
{% endraw %}</pre>

#### Exercise: 3 stars, optional (progress_from_term_ind)
Show that progress can also be proved by induction on terms
instead of induction on typing derivations.

<pre class="Agda">{% raw %}
<a name="4354" class="Keyword"
      >postulate</a
      ><a name="4363"
      >
  </a
      ><a name="4366" href="StlcProp.html#4366" class="Postulate"
      >progress&#8242;</a
      ><a name="4375"
      > </a
      ><a name="4376" class="Symbol"
      >:</a
      ><a name="4377"
      > </a
      ><a name="4378" class="Symbol"
      >&#8704;</a
      ><a name="4379"
      > </a
      ><a name="4386" class="Symbol"
      >&#8594;</a
      ><a name="4387"
      > </a
      ><a name="4388" href="Stlc.html#18127" class="Function"
      >&#8709;</a
      ><a name="4389"
      > </a
      ><a name="4390" href="Stlc.html#19059" class="Datatype Operator"
      >&#8866;</a
      ><a name="4391"
      > </a
      ><a name="4392" href="StlcProp.html#4381" class="Bound"
      >t</a
      ><a name="4393"
      > </a
      ><a name="4394" href="Stlc.html#19059" class="Datatype Operator"
      >&#8758;</a
      ><a name="4395"
      > </a
      ><a name="4396" href="StlcProp.html#4383" class="Bound"
      >A</a
      ><a name="4397"
      > </a
      ><a name="4398" class="Symbol"
      >&#8594;</a
      ><a name="4399"
      > </a
      ><a name="4400" href="Stlc.html#8909" class="Datatype"
      >Value</a
      ><a name="4405"
      > </a
      ><a name="4406" href="StlcProp.html#4381" class="Bound"
      >t</a
      ><a name="4407"
      > </a
      ><a name="4408" href="https://agda.github.io/agda-stdlib/Data.Sum.html#433" class="Datatype Operator"
      >&#8846;</a
      ><a name="4409"
      > </a
      ><a name="4410" href="https://agda.github.io/agda-stdlib/Data.Product.html#823" class="Function"
      >&#8707;</a
      ><a name="4411"
      > </a
      ><a name="4412" class="Symbol"
      >&#955;</a
      ><a name="4413"
      > </a
      ><a name="4414" href="StlcProp.html#4414" class="Bound"
      >t&#8242;</a
      ><a name="4416"
      > </a
      ><a name="4417" class="Symbol"
      >&#8594;</a
      ><a name="4418"
      > </a
      ><a name="4419" href="StlcProp.html#4381" class="Bound"
      >t</a
      ><a name="4420"
      > </a
      ><a name="4421" href="Stlc.html#15045" class="Datatype Operator"
      >==&gt;</a
      ><a name="4424"
      > </a
      ><a name="4425" href="StlcProp.html#4414" class="Bound"
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
<a name="6848" class="Keyword"
      >data</a
      ><a name="6852"
      > </a
      ><a name="6853" href="StlcProp.html#6853" class="Datatype Operator"
      >_FreeIn_</a
      ><a name="6861"
      > </a
      ><a name="6862" class="Symbol"
      >(</a
      ><a name="6863" href="StlcProp.html#6863" class="Bound"
      >x</a
      ><a name="6864"
      > </a
      ><a name="6865" class="Symbol"
      >:</a
      ><a name="6866"
      > </a
      ><a name="6867" href="Maps.html#2243" class="Datatype"
      >Id</a
      ><a name="6869" class="Symbol"
      >)</a
      ><a name="6870"
      > </a
      ><a name="6871" class="Symbol"
      >:</a
      ><a name="6872"
      > </a
      ><a name="6873" href="Stlc.html#5502" class="Datatype"
      >Term</a
      ><a name="6877"
      > </a
      ><a name="6878" class="Symbol"
      >&#8594;</a
      ><a name="6879"
      > </a
      ><a name="6880" class="PrimitiveType"
      >Set</a
      ><a name="6883"
      > </a
      ><a name="6884" class="Keyword"
      >where</a
      ><a name="6889"
      >
  </a
      ><a name="6892" href="StlcProp.html#6892" class="InductiveConstructor"
      >var</a
      ><a name="6895"
      >  </a
      ><a name="6897" class="Symbol"
      >:</a
      ><a name="6898"
      > </a
      ><a name="6899" href="StlcProp.html#6863" class="Bound"
      >x</a
      ><a name="6900"
      > </a
      ><a name="6901" href="StlcProp.html#6853" class="Datatype Operator"
      >FreeIn</a
      ><a name="6907"
      > </a
      ><a name="6908" href="Stlc.html#5521" class="InductiveConstructor"
      >var</a
      ><a name="6911"
      > </a
      ><a name="6912" href="StlcProp.html#6863" class="Bound"
      >x</a
      ><a name="6913"
      >
  </a
      ><a name="6916" href="StlcProp.html#6916" class="InductiveConstructor"
      >abs</a
      ><a name="6919"
      >  </a
      ><a name="6921" class="Symbol"
      >:</a
      ><a name="6922"
      > </a
      ><a name="6923" class="Symbol"
      >&#8704;</a
      ><a name="6924"
      > </a
      ><a name="6933" class="Symbol"
      >&#8594;</a
      ><a name="6934"
      > </a
      ><a name="6935" href="StlcProp.html#6926" class="Bound"
      >y</a
      ><a name="6936"
      > </a
      ><a name="6937" href="https://agda.github.io/agda-stdlib/Relation.Binary.Core.html#4493" class="Function Operator"
      >&#8802;</a
      ><a name="6938"
      > </a
      ><a name="6939" href="StlcProp.html#6863" class="Bound"
      >x</a
      ><a name="6940"
      > </a
      ><a name="6941" class="Symbol"
      >&#8594;</a
      ><a name="6942"
      > </a
      ><a name="6943" href="StlcProp.html#6863" class="Bound"
      >x</a
      ><a name="6944"
      > </a
      ><a name="6945" href="StlcProp.html#6853" class="Datatype Operator"
      >FreeIn</a
      ><a name="6951"
      > </a
      ><a name="6952" href="StlcProp.html#6930" class="Bound"
      >t</a
      ><a name="6953"
      > </a
      ><a name="6954" class="Symbol"
      >&#8594;</a
      ><a name="6955"
      > </a
      ><a name="6956" href="StlcProp.html#6863" class="Bound"
      >x</a
      ><a name="6957"
      > </a
      ><a name="6958" href="StlcProp.html#6853" class="Datatype Operator"
      >FreeIn</a
      ><a name="6964"
      > </a
      ><a name="6965" href="Stlc.html#5570" class="InductiveConstructor"
      >abs</a
      ><a name="6968"
      > </a
      ><a name="6969" href="StlcProp.html#6926" class="Bound"
      >y</a
      ><a name="6970"
      > </a
      ><a name="6971" href="StlcProp.html#6928" class="Bound"
      >A</a
      ><a name="6972"
      > </a
      ><a name="6973" href="StlcProp.html#6930" class="Bound"
      >t</a
      ><a name="6974"
      >
  </a
      ><a name="6977" href="StlcProp.html#6977" class="InductiveConstructor"
      >app1</a
      ><a name="6981"
      > </a
      ><a name="6982" class="Symbol"
      >:</a
      ><a name="6983"
      > </a
      ><a name="6984" class="Symbol"
      >&#8704;</a
      ><a name="6985"
      > </a
      ><a name="6994" class="Symbol"
      >&#8594;</a
      ><a name="6995"
      > </a
      ><a name="6996" href="StlcProp.html#6863" class="Bound"
      >x</a
      ><a name="6997"
      > </a
      ><a name="6998" href="StlcProp.html#6853" class="Datatype Operator"
      >FreeIn</a
      ><a name="7004"
      > </a
      ><a name="7005" href="StlcProp.html#6987" class="Bound"
      >t&#8321;</a
      ><a name="7007"
      > </a
      ><a name="7008" class="Symbol"
      >&#8594;</a
      ><a name="7009"
      > </a
      ><a name="7010" href="StlcProp.html#6863" class="Bound"
      >x</a
      ><a name="7011"
      > </a
      ><a name="7012" href="StlcProp.html#6853" class="Datatype Operator"
      >FreeIn</a
      ><a name="7018"
      > </a
      ><a name="7019" href="Stlc.html#5541" class="InductiveConstructor"
      >app</a
      ><a name="7022"
      > </a
      ><a name="7023" href="StlcProp.html#6987" class="Bound"
      >t&#8321;</a
      ><a name="7025"
      > </a
      ><a name="7026" href="StlcProp.html#6990" class="Bound"
      >t&#8322;</a
      ><a name="7028"
      >
  </a
      ><a name="7031" href="StlcProp.html#7031" class="InductiveConstructor"
      >app2</a
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
      ><a name="7050" href="StlcProp.html#6863" class="Bound"
      >x</a
      ><a name="7051"
      > </a
      ><a name="7052" href="StlcProp.html#6853" class="Datatype Operator"
      >FreeIn</a
      ><a name="7058"
      > </a
      ><a name="7059" href="StlcProp.html#7044" class="Bound"
      >t&#8322;</a
      ><a name="7061"
      > </a
      ><a name="7062" class="Symbol"
      >&#8594;</a
      ><a name="7063"
      > </a
      ><a name="7064" href="StlcProp.html#6863" class="Bound"
      >x</a
      ><a name="7065"
      > </a
      ><a name="7066" href="StlcProp.html#6853" class="Datatype Operator"
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
      >if1</a
      ><a name="7088"
      >  </a
      ><a name="7090" class="Symbol"
      >:</a
      ><a name="7091"
      > </a
      ><a name="7092" class="Symbol"
      >&#8704;</a
      ><a name="7093"
      > </a
      ><a name="7105" class="Symbol"
      >&#8594;</a
      ><a name="7106"
      > </a
      ><a name="7107" href="StlcProp.html#6863" class="Bound"
      >x</a
      ><a name="7108"
      > </a
      ><a name="7109" href="StlcProp.html#6853" class="Datatype Operator"
      >FreeIn</a
      ><a name="7115"
      > </a
      ><a name="7116" href="StlcProp.html#7095" class="Bound"
      >t&#8321;</a
      ><a name="7118"
      > </a
      ><a name="7119" class="Symbol"
      >&#8594;</a
      ><a name="7120"
      > </a
      ><a name="7121" href="StlcProp.html#6863" class="Bound"
      >x</a
      ><a name="7122"
      > </a
      ><a name="7123" href="StlcProp.html#6853" class="Datatype Operator"
      >FreeIn</a
      ><a name="7129"
      > </a
      ><a name="7130" class="Symbol"
      >(</a
      ><a name="7131" href="Stlc.html#5634" class="InductiveConstructor Operator"
      >if</a
      ><a name="7133"
      > </a
      ><a name="7134" href="StlcProp.html#7095" class="Bound"
      >t&#8321;</a
      ><a name="7136"
      > </a
      ><a name="7137" href="Stlc.html#5634" class="InductiveConstructor Operator"
      >then</a
      ><a name="7141"
      > </a
      ><a name="7142" href="StlcProp.html#7098" class="Bound"
      >t&#8322;</a
      ><a name="7144"
      > </a
      ><a name="7145" href="Stlc.html#5634" class="InductiveConstructor Operator"
      >else</a
      ><a name="7149"
      > </a
      ><a name="7150" href="StlcProp.html#7101" class="Bound"
      >t&#8323;</a
      ><a name="7152" class="Symbol"
      >)</a
      ><a name="7153"
      >
  </a
      ><a name="7156" href="StlcProp.html#7156" class="InductiveConstructor"
      >if2</a
      ><a name="7159"
      >  </a
      ><a name="7161" class="Symbol"
      >:</a
      ><a name="7162"
      > </a
      ><a name="7163" class="Symbol"
      >&#8704;</a
      ><a name="7164"
      > </a
      ><a name="7176" class="Symbol"
      >&#8594;</a
      ><a name="7177"
      > </a
      ><a name="7178" href="StlcProp.html#6863" class="Bound"
      >x</a
      ><a name="7179"
      > </a
      ><a name="7180" href="StlcProp.html#6853" class="Datatype Operator"
      >FreeIn</a
      ><a name="7186"
      > </a
      ><a name="7187" href="StlcProp.html#7169" class="Bound"
      >t&#8322;</a
      ><a name="7189"
      > </a
      ><a name="7190" class="Symbol"
      >&#8594;</a
      ><a name="7191"
      > </a
      ><a name="7192" href="StlcProp.html#6863" class="Bound"
      >x</a
      ><a name="7193"
      > </a
      ><a name="7194" href="StlcProp.html#6853" class="Datatype Operator"
      >FreeIn</a
      ><a name="7200"
      > </a
      ><a name="7201" class="Symbol"
      >(</a
      ><a name="7202" href="Stlc.html#5634" class="InductiveConstructor Operator"
      >if</a
      ><a name="7204"
      > </a
      ><a name="7205" href="StlcProp.html#7166" class="Bound"
      >t&#8321;</a
      ><a name="7207"
      > </a
      ><a name="7208" href="Stlc.html#5634" class="InductiveConstructor Operator"
      >then</a
      ><a name="7212"
      > </a
      ><a name="7213" href="StlcProp.html#7169" class="Bound"
      >t&#8322;</a
      ><a name="7215"
      > </a
      ><a name="7216" href="Stlc.html#5634" class="InductiveConstructor Operator"
      >else</a
      ><a name="7220"
      > </a
      ><a name="7221" href="StlcProp.html#7172" class="Bound"
      >t&#8323;</a
      ><a name="7223" class="Symbol"
      >)</a
      ><a name="7224"
      >
  </a
      ><a name="7227" href="StlcProp.html#7227" class="InductiveConstructor"
      >if3</a
      ><a name="7230"
      >  </a
      ><a name="7232" class="Symbol"
      >:</a
      ><a name="7233"
      > </a
      ><a name="7234" class="Symbol"
      >&#8704;</a
      ><a name="7235"
      > </a
      ><a name="7247" class="Symbol"
      >&#8594;</a
      ><a name="7248"
      > </a
      ><a name="7249" href="StlcProp.html#6863" class="Bound"
      >x</a
      ><a name="7250"
      > </a
      ><a name="7251" href="StlcProp.html#6853" class="Datatype Operator"
      >FreeIn</a
      ><a name="7257"
      > </a
      ><a name="7258" href="StlcProp.html#7243" class="Bound"
      >t&#8323;</a
      ><a name="7260"
      > </a
      ><a name="7261" class="Symbol"
      >&#8594;</a
      ><a name="7262"
      > </a
      ><a name="7263" href="StlcProp.html#6863" class="Bound"
      >x</a
      ><a name="7264"
      > </a
      ><a name="7265" href="StlcProp.html#6853" class="Datatype Operator"
      >FreeIn</a
      ><a name="7271"
      > </a
      ><a name="7272" class="Symbol"
      >(</a
      ><a name="7273" href="Stlc.html#5634" class="InductiveConstructor Operator"
      >if</a
      ><a name="7275"
      > </a
      ><a name="7276" href="StlcProp.html#7237" class="Bound"
      >t&#8321;</a
      ><a name="7278"
      > </a
      ><a name="7279" href="Stlc.html#5634" class="InductiveConstructor Operator"
      >then</a
      ><a name="7283"
      > </a
      ><a name="7284" href="StlcProp.html#7240" class="Bound"
      >t&#8322;</a
      ><a name="7286"
      > </a
      ><a name="7287" href="Stlc.html#5634" class="InductiveConstructor Operator"
      >else</a
      ><a name="7291"
      > </a
      ><a name="7292" href="StlcProp.html#7243" class="Bound"
      >t&#8323;</a
      ><a name="7294" class="Symbol"
      >)</a
      >
{% endraw %}</pre>

A term in which no variables appear free is said to be _closed_.

<pre class="Agda">{% raw %}
<a name="7387" href="StlcProp.html#7387" class="Function"
      >Closed</a
      ><a name="7393"
      > </a
      ><a name="7394" class="Symbol"
      >:</a
      ><a name="7395"
      > </a
      ><a name="7396" href="Stlc.html#5502" class="Datatype"
      >Term</a
      ><a name="7400"
      > </a
      ><a name="7401" class="Symbol"
      >&#8594;</a
      ><a name="7402"
      > </a
      ><a name="7403" class="PrimitiveType"
      >Set</a
      ><a name="7406"
      >
</a
      ><a name="7407" href="StlcProp.html#7387" class="Function"
      >Closed</a
      ><a name="7413"
      > </a
      ><a name="7414" href="StlcProp.html#7414" class="Bound"
      >t</a
      ><a name="7415"
      > </a
      ><a name="7416" class="Symbol"
      >=</a
      ><a name="7417"
      > </a
      ><a name="7418" class="Symbol"
      >&#8704;</a
      ><a name="7419"
      > </a
      ><a name="7424" class="Symbol"
      >&#8594;</a
      ><a name="7425"
      > </a
      ><a name="7426" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#414" class="Function Operator"
      >&#172;</a
      ><a name="7427"
      > </a
      ><a name="7428" class="Symbol"
      >(</a
      ><a name="7429" href="StlcProp.html#7421" class="Bound"
      >x</a
      ><a name="7430"
      > </a
      ><a name="7431" href="StlcProp.html#6853" class="Datatype Operator"
      >FreeIn</a
      ><a name="7437"
      > </a
      ><a name="7438" href="StlcProp.html#7414" class="Bound"
      >t</a
      ><a name="7439" class="Symbol"
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
<a name="8168" href="StlcProp.html#8168" class="Function"
      >freeInCtxt</a
      ><a name="8178"
      > </a
      ><a name="8179" class="Symbol"
      >:</a
      ><a name="8180"
      > </a
      ><a name="8181" class="Symbol"
      >&#8704;</a
      ><a name="8182"
      > </a
      ><a name="8193" class="Symbol"
      >&#8594;</a
      ><a name="8194"
      > </a
      ><a name="8195" href="StlcProp.html#8184" class="Bound"
      >x</a
      ><a name="8196"
      > </a
      ><a name="8197" href="StlcProp.html#6853" class="Datatype Operator"
      >FreeIn</a
      ><a name="8203"
      > </a
      ><a name="8204" href="StlcProp.html#8186" class="Bound"
      >t</a
      ><a name="8205"
      > </a
      ><a name="8206" class="Symbol"
      >&#8594;</a
      ><a name="8207"
      > </a
      ><a name="8208" href="StlcProp.html#8190" class="Bound"
      >&#915;</a
      ><a name="8209"
      > </a
      ><a name="8210" href="Stlc.html#19059" class="Datatype Operator"
      >&#8866;</a
      ><a name="8211"
      > </a
      ><a name="8212" href="StlcProp.html#8186" class="Bound"
      >t</a
      ><a name="8213"
      > </a
      ><a name="8214" href="Stlc.html#19059" class="Datatype Operator"
      >&#8758;</a
      ><a name="8215"
      > </a
      ><a name="8216" href="StlcProp.html#8188" class="Bound"
      >A</a
      ><a name="8217"
      > </a
      ><a name="8218" class="Symbol"
      >&#8594;</a
      ><a name="8219"
      > </a
      ><a name="8220" href="https://agda.github.io/agda-stdlib/Data.Product.html#823" class="Function"
      >&#8707;</a
      ><a name="8221"
      > </a
      ><a name="8222" class="Symbol"
      >&#955;</a
      ><a name="8223"
      > </a
      ><a name="8224" href="StlcProp.html#8224" class="Bound"
      >B</a
      ><a name="8225"
      > </a
      ><a name="8226" class="Symbol"
      >&#8594;</a
      ><a name="8227"
      > </a
      ><a name="8228" href="StlcProp.html#8190" class="Bound"
      >&#915;</a
      ><a name="8229"
      > </a
      ><a name="8230" href="StlcProp.html#8184" class="Bound"
      >x</a
      ><a name="8231"
      > </a
      ><a name="8232" href="Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="8233"
      > </a
      ><a name="8234" href="https://agda.github.io/agda-stdlib/Data.Maybe.Base.html#373" class="InductiveConstructor"
      >just</a
      ><a name="8238"
      > </a
      ><a name="8239" href="StlcProp.html#8224" class="Bound"
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
<a name="9835" href="StlcProp.html#8168" class="Function"
      >freeInCtxt</a
      ><a name="9845"
      > </a
      ><a name="9846" href="StlcProp.html#6892" class="InductiveConstructor"
      >var</a
      ><a name="9849"
      > </a
      ><a name="9850" class="Symbol"
      >(</a
      ><a name="9851" href="Stlc.html#19103" class="InductiveConstructor"
      >var</a
      ><a name="9854"
      > </a
      ><a name="9855" class="Symbol"
      >_</a
      ><a name="9856"
      > </a
      ><a name="9857" href="StlcProp.html#9857" class="Bound"
      >x&#8758;A</a
      ><a name="9860" class="Symbol"
      >)</a
      ><a name="9861"
      > </a
      ><a name="9862" class="Symbol"
      >=</a
      ><a name="9863"
      > </a
      ><a name="9864" class="Symbol"
      >(_</a
      ><a name="9866"
      > </a
      ><a name="9867" href="https://agda.github.io/agda-stdlib/Data.Product.html#509" class="InductiveConstructor Operator"
      >,</a
      ><a name="9868"
      > </a
      ><a name="9869" href="StlcProp.html#9857" class="Bound"
      >x&#8758;A</a
      ><a name="9872" class="Symbol"
      >)</a
      ><a name="9873"
      >
</a
      ><a name="9874" href="StlcProp.html#8168" class="Function"
      >freeInCtxt</a
      ><a name="9884"
      > </a
      ><a name="9885" class="Symbol"
      >(</a
      ><a name="9886" href="StlcProp.html#6977" class="InductiveConstructor"
      >app1</a
      ><a name="9890"
      > </a
      ><a name="9891" href="StlcProp.html#9891" class="Bound"
      >x&#8712;t&#8321;</a
      ><a name="9895" class="Symbol"
      >)</a
      ><a name="9896"
      > </a
      ><a name="9897" class="Symbol"
      >(</a
      ><a name="9898" href="Stlc.html#19312" class="InductiveConstructor"
      >app</a
      ><a name="9901"
      > </a
      ><a name="9902" href="StlcProp.html#9902" class="Bound"
      >t&#8321;&#8758;A</a
      ><a name="9906"
      > </a
      ><a name="9907" class="Symbol"
      >_</a
      ><a name="9908"
      >   </a
      ><a name="9911" class="Symbol"
      >)</a
      ><a name="9912"
      > </a
      ><a name="9913" class="Symbol"
      >=</a
      ><a name="9914"
      > </a
      ><a name="9915" href="StlcProp.html#8168" class="Function"
      >freeInCtxt</a
      ><a name="9925"
      > </a
      ><a name="9926" href="StlcProp.html#9891" class="Bound"
      >x&#8712;t&#8321;</a
      ><a name="9930"
      > </a
      ><a name="9931" href="StlcProp.html#9902" class="Bound"
      >t&#8321;&#8758;A</a
      ><a name="9935"
      >
</a
      ><a name="9936" href="StlcProp.html#8168" class="Function"
      >freeInCtxt</a
      ><a name="9946"
      > </a
      ><a name="9947" class="Symbol"
      >(</a
      ><a name="9948" href="StlcProp.html#7031" class="InductiveConstructor"
      >app2</a
      ><a name="9952"
      > </a
      ><a name="9953" href="StlcProp.html#9953" class="Bound"
      >x&#8712;t&#8322;</a
      ><a name="9957" class="Symbol"
      >)</a
      ><a name="9958"
      > </a
      ><a name="9959" class="Symbol"
      >(</a
      ><a name="9960" href="Stlc.html#19312" class="InductiveConstructor"
      >app</a
      ><a name="9963"
      > </a
      ><a name="9964" class="Symbol"
      >_</a
      ><a name="9965"
      >    </a
      ><a name="9969" href="StlcProp.html#9969" class="Bound"
      >t&#8322;&#8758;A</a
      ><a name="9973" class="Symbol"
      >)</a
      ><a name="9974"
      > </a
      ><a name="9975" class="Symbol"
      >=</a
      ><a name="9976"
      > </a
      ><a name="9977" href="StlcProp.html#8168" class="Function"
      >freeInCtxt</a
      ><a name="9987"
      > </a
      ><a name="9988" href="StlcProp.html#9953" class="Bound"
      >x&#8712;t&#8322;</a
      ><a name="9992"
      > </a
      ><a name="9993" href="StlcProp.html#9969" class="Bound"
      >t&#8322;&#8758;A</a
      ><a name="9997"
      >
</a
      ><a name="9998" href="StlcProp.html#8168" class="Function"
      >freeInCtxt</a
      ><a name="10008"
      > </a
      ><a name="10009" class="Symbol"
      >(</a
      ><a name="10010" href="StlcProp.html#7085" class="InductiveConstructor"
      >if1</a
      ><a name="10013"
      >  </a
      ><a name="10015" href="StlcProp.html#10015" class="Bound"
      >x&#8712;t&#8321;</a
      ><a name="10019" class="Symbol"
      >)</a
      ><a name="10020"
      > </a
      ><a name="10021" class="Symbol"
      >(</a
      ><a name="10022" href="Stlc.html#19564" class="InductiveConstructor Operator"
      >if</a
      ><a name="10024"
      > </a
      ><a name="10025" href="StlcProp.html#10025" class="Bound"
      >t&#8321;&#8758;A</a
      ><a name="10029"
      > </a
      ><a name="10030" href="Stlc.html#19564" class="InductiveConstructor Operator"
      >then</a
      ><a name="10034"
      > </a
      ><a name="10035" class="Symbol"
      >_</a
      ><a name="10036"
      >    </a
      ><a name="10040" href="Stlc.html#19564" class="InductiveConstructor Operator"
      >else</a
      ><a name="10044"
      > </a
      ><a name="10045" class="Symbol"
      >_</a
      ><a name="10046"
      >   </a
      ><a name="10049" class="Symbol"
      >)</a
      ><a name="10050"
      > </a
      ><a name="10051" class="Symbol"
      >=</a
      ><a name="10052"
      > </a
      ><a name="10053" href="StlcProp.html#8168" class="Function"
      >freeInCtxt</a
      ><a name="10063"
      > </a
      ><a name="10064" href="StlcProp.html#10015" class="Bound"
      >x&#8712;t&#8321;</a
      ><a name="10068"
      > </a
      ><a name="10069" href="StlcProp.html#10025" class="Bound"
      >t&#8321;&#8758;A</a
      ><a name="10073"
      >
</a
      ><a name="10074" href="StlcProp.html#8168" class="Function"
      >freeInCtxt</a
      ><a name="10084"
      > </a
      ><a name="10085" class="Symbol"
      >(</a
      ><a name="10086" href="StlcProp.html#7156" class="InductiveConstructor"
      >if2</a
      ><a name="10089"
      >  </a
      ><a name="10091" href="StlcProp.html#10091" class="Bound"
      >x&#8712;t&#8322;</a
      ><a name="10095" class="Symbol"
      >)</a
      ><a name="10096"
      > </a
      ><a name="10097" class="Symbol"
      >(</a
      ><a name="10098" href="Stlc.html#19564" class="InductiveConstructor Operator"
      >if</a
      ><a name="10100"
      > </a
      ><a name="10101" class="Symbol"
      >_</a
      ><a name="10102"
      >    </a
      ><a name="10106" href="Stlc.html#19564" class="InductiveConstructor Operator"
      >then</a
      ><a name="10110"
      > </a
      ><a name="10111" href="StlcProp.html#10111" class="Bound"
      >t&#8322;&#8758;A</a
      ><a name="10115"
      > </a
      ><a name="10116" href="Stlc.html#19564" class="InductiveConstructor Operator"
      >else</a
      ><a name="10120"
      > </a
      ><a name="10121" class="Symbol"
      >_</a
      ><a name="10122"
      >   </a
      ><a name="10125" class="Symbol"
      >)</a
      ><a name="10126"
      > </a
      ><a name="10127" class="Symbol"
      >=</a
      ><a name="10128"
      > </a
      ><a name="10129" href="StlcProp.html#8168" class="Function"
      >freeInCtxt</a
      ><a name="10139"
      > </a
      ><a name="10140" href="StlcProp.html#10091" class="Bound"
      >x&#8712;t&#8322;</a
      ><a name="10144"
      > </a
      ><a name="10145" href="StlcProp.html#10111" class="Bound"
      >t&#8322;&#8758;A</a
      ><a name="10149"
      >
</a
      ><a name="10150" href="StlcProp.html#8168" class="Function"
      >freeInCtxt</a
      ><a name="10160"
      > </a
      ><a name="10161" class="Symbol"
      >(</a
      ><a name="10162" href="StlcProp.html#7227" class="InductiveConstructor"
      >if3</a
      ><a name="10165"
      >  </a
      ><a name="10167" href="StlcProp.html#10167" class="Bound"
      >x&#8712;t&#8323;</a
      ><a name="10171" class="Symbol"
      >)</a
      ><a name="10172"
      > </a
      ><a name="10173" class="Symbol"
      >(</a
      ><a name="10174" href="Stlc.html#19564" class="InductiveConstructor Operator"
      >if</a
      ><a name="10176"
      > </a
      ><a name="10177" class="Symbol"
      >_</a
      ><a name="10178"
      >    </a
      ><a name="10182" href="Stlc.html#19564" class="InductiveConstructor Operator"
      >then</a
      ><a name="10186"
      > </a
      ><a name="10187" class="Symbol"
      >_</a
      ><a name="10188"
      >    </a
      ><a name="10192" href="Stlc.html#19564" class="InductiveConstructor Operator"
      >else</a
      ><a name="10196"
      > </a
      ><a name="10197" href="StlcProp.html#10197" class="Bound"
      >t&#8323;&#8758;A</a
      ><a name="10201" class="Symbol"
      >)</a
      ><a name="10202"
      > </a
      ><a name="10203" class="Symbol"
      >=</a
      ><a name="10204"
      > </a
      ><a name="10205" href="StlcProp.html#8168" class="Function"
      >freeInCtxt</a
      ><a name="10215"
      > </a
      ><a name="10216" href="StlcProp.html#10167" class="Bound"
      >x&#8712;t&#8323;</a
      ><a name="10220"
      > </a
      ><a name="10221" href="StlcProp.html#10197" class="Bound"
      >t&#8323;&#8758;A</a
      ><a name="10225"
      >
</a
      ><a name="10226" href="StlcProp.html#8168" class="Function"
      >freeInCtxt</a
      ><a name="10236"
      > </a
      ><a name="10241" class="Symbol"
      >(</a
      ><a name="10242" href="StlcProp.html#6916" class="InductiveConstructor"
      >abs</a
      ><a name="10245"
      > </a
      ><a name="10250" href="StlcProp.html#10250" class="Bound"
      >y&#8800;x</a
      ><a name="10253"
      > </a
      ><a name="10254" href="StlcProp.html#10254" class="Bound"
      >x&#8712;t</a
      ><a name="10257" class="Symbol"
      >)</a
      ><a name="10258"
      > </a
      ><a name="10259" class="Symbol"
      >(</a
      ><a name="10260" href="Stlc.html#19196" class="InductiveConstructor"
      >abs</a
      ><a name="10263"
      > </a
      ><a name="10264" href="StlcProp.html#10264" class="Bound"
      >t&#8758;B</a
      ><a name="10267" class="Symbol"
      >)</a
      ><a name="10268"
      >
    </a
      ><a name="10273" class="Keyword"
      >with</a
      ><a name="10277"
      > </a
      ><a name="10278" href="StlcProp.html#8168" class="Function"
      >freeInCtxt</a
      ><a name="10288"
      > </a
      ><a name="10289" href="StlcProp.html#10254" class="Bound"
      >x&#8712;t</a
      ><a name="10292"
      > </a
      ><a name="10293" href="StlcProp.html#10264" class="Bound"
      >t&#8758;B</a
      ><a name="10296"
      >
</a
      ><a name="10297" class="Symbol"
      >...</a
      ><a name="10300"
      > </a
      ><a name="10301" class="Symbol"
      >|</a
      ><a name="10302"
      > </a
      ><a name="10303" href="StlcProp.html#10303" class="Bound"
      >x&#8758;A</a
      ><a name="10306"
      >
    </a
      ><a name="10311" class="Keyword"
      >with</a
      ><a name="10315"
      > </a
      ><a name="10316" href="StlcProp.html#10247" class="Bound"
      >y</a
      ><a name="10317"
      > </a
      ><a name="10318" href="Maps.html#2297" class="Function Operator"
      >&#8799;</a
      ><a name="10319"
      > </a
      ><a name="10320" href="StlcProp.html#10238" class="Bound"
      >x</a
      ><a name="10321"
      >
</a
      ><a name="10322" class="Symbol"
      >...</a
      ><a name="10325"
      > </a
      ><a name="10326" class="Symbol"
      >|</a
      ><a name="10327"
      > </a
      ><a name="10328" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#520" class="InductiveConstructor"
      >yes</a
      ><a name="10331"
      > </a
      ><a name="10332" href="StlcProp.html#10332" class="Bound"
      >y=x</a
      ><a name="10335"
      > </a
      ><a name="10336" class="Symbol"
      >=</a
      ><a name="10337"
      > </a
      ><a name="10338" href="https://agda.github.io/agda-stdlib/Data.Empty.html#348" class="Function"
      >&#8869;-elim</a
      ><a name="10344"
      > </a
      ><a name="10345" class="Symbol"
      >(</a
      ><a name="10346" href="StlcProp.html#10250" class="Bound"
      >y&#8800;x</a
      ><a name="10349"
      > </a
      ><a name="10350" href="StlcProp.html#10332" class="Bound"
      >y=x</a
      ><a name="10353" class="Symbol"
      >)</a
      ><a name="10354"
      >
</a
      ><a name="10355" class="Symbol"
      >...</a
      ><a name="10358"
      > </a
      ><a name="10359" class="Symbol"
      >|</a
      ><a name="10360"
      > </a
      ><a name="10361" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#547" class="InductiveConstructor"
      >no</a
      ><a name="10363"
      >  </a
      ><a name="10365" class="Symbol"
      >_</a
      ><a name="10366"
      >   </a
      ><a name="10369" class="Symbol"
      >=</a
      ><a name="10370"
      > </a
      ><a name="10371" href="StlcProp.html#10303" class="Bound"
      >x&#8758;A</a
      >
{% endraw %}</pre>

Next, we'll need the fact that any term $$t$$ which is well typed in
the empty context is closed (it has no free variables).

#### Exercise: 2 stars, optional (∅⊢-closed)

<pre class="Agda">{% raw %}
<a name="10572" class="Keyword"
      >postulate</a
      ><a name="10581"
      >
  </a
      ><a name="10584" href="StlcProp.html#10584" class="Postulate"
      >&#8709;&#8866;-closed</a
      ><a name="10593"
      > </a
      ><a name="10594" class="Symbol"
      >:</a
      ><a name="10595"
      > </a
      ><a name="10596" class="Symbol"
      >&#8704;</a
      ><a name="10597"
      > </a
      ><a name="10604" class="Symbol"
      >&#8594;</a
      ><a name="10605"
      > </a
      ><a name="10606" href="Stlc.html#18127" class="Function"
      >&#8709;</a
      ><a name="10607"
      > </a
      ><a name="10608" href="Stlc.html#19059" class="Datatype Operator"
      >&#8866;</a
      ><a name="10609"
      > </a
      ><a name="10610" href="StlcProp.html#10599" class="Bound"
      >t</a
      ><a name="10611"
      > </a
      ><a name="10612" href="Stlc.html#19059" class="Datatype Operator"
      >&#8758;</a
      ><a name="10613"
      > </a
      ><a name="10614" href="StlcProp.html#10601" class="Bound"
      >A</a
      ><a name="10615"
      > </a
      ><a name="10616" class="Symbol"
      >&#8594;</a
      ><a name="10617"
      > </a
      ><a name="10618" href="StlcProp.html#7387" class="Function"
      >Closed</a
      ><a name="10624"
      > </a
      ><a name="10625" href="StlcProp.html#10599" class="Bound"
      >t</a
      >
{% endraw %}</pre>

<div class="hidden">
<pre class="Agda">{% raw %}
<a name="10673" href="StlcProp.html#10673" class="Function"
      >&#8709;&#8866;-closed&#8242;</a
      ><a name="10683"
      > </a
      ><a name="10684" class="Symbol"
      >:</a
      ><a name="10685"
      > </a
      ><a name="10686" class="Symbol"
      >&#8704;</a
      ><a name="10687"
      > </a
      ><a name="10694" class="Symbol"
      >&#8594;</a
      ><a name="10695"
      > </a
      ><a name="10696" href="Stlc.html#18127" class="Function"
      >&#8709;</a
      ><a name="10697"
      > </a
      ><a name="10698" href="Stlc.html#19059" class="Datatype Operator"
      >&#8866;</a
      ><a name="10699"
      > </a
      ><a name="10700" href="StlcProp.html#10689" class="Bound"
      >t</a
      ><a name="10701"
      > </a
      ><a name="10702" href="Stlc.html#19059" class="Datatype Operator"
      >&#8758;</a
      ><a name="10703"
      > </a
      ><a name="10704" href="StlcProp.html#10691" class="Bound"
      >A</a
      ><a name="10705"
      > </a
      ><a name="10706" class="Symbol"
      >&#8594;</a
      ><a name="10707"
      > </a
      ><a name="10708" href="StlcProp.html#7387" class="Function"
      >Closed</a
      ><a name="10714"
      > </a
      ><a name="10715" href="StlcProp.html#10689" class="Bound"
      >t</a
      ><a name="10716"
      >
</a
      ><a name="10717" href="StlcProp.html#10673" class="Function"
      >&#8709;&#8866;-closed&#8242;</a
      ><a name="10727"
      > </a
      ><a name="10728" class="Symbol"
      >(</a
      ><a name="10729" href="Stlc.html#19103" class="InductiveConstructor"
      >var</a
      ><a name="10732"
      > </a
      ><a name="10733" href="StlcProp.html#10733" class="Bound"
      >x</a
      ><a name="10734"
      > </a
      ><a name="10735" class="Symbol"
      >())</a
      ><a name="10738"
      >
</a
      ><a name="10739" href="StlcProp.html#10673" class="Function"
      >&#8709;&#8866;-closed&#8242;</a
      ><a name="10749"
      > </a
      ><a name="10750" class="Symbol"
      >(</a
      ><a name="10751" href="Stlc.html#19312" class="InductiveConstructor"
      >app</a
      ><a name="10754"
      > </a
      ><a name="10755" href="StlcProp.html#10755" class="Bound"
      >t&#8321;&#8758;A&#8658;B</a
      ><a name="10761"
      > </a
      ><a name="10762" href="StlcProp.html#10762" class="Bound"
      >t&#8322;&#8758;A</a
      ><a name="10766" class="Symbol"
      >)</a
      ><a name="10767"
      > </a
      ><a name="10768" class="Symbol"
      >(</a
      ><a name="10769" href="StlcProp.html#6977" class="InductiveConstructor"
      >app1</a
      ><a name="10773"
      > </a
      ><a name="10774" href="StlcProp.html#10774" class="Bound"
      >x&#8712;t&#8321;</a
      ><a name="10778" class="Symbol"
      >)</a
      ><a name="10779"
      > </a
      ><a name="10780" class="Symbol"
      >=</a
      ><a name="10781"
      > </a
      ><a name="10782" href="StlcProp.html#10673" class="Function"
      >&#8709;&#8866;-closed&#8242;</a
      ><a name="10792"
      > </a
      ><a name="10793" href="StlcProp.html#10755" class="Bound"
      >t&#8321;&#8758;A&#8658;B</a
      ><a name="10799"
      > </a
      ><a name="10800" href="StlcProp.html#10774" class="Bound"
      >x&#8712;t&#8321;</a
      ><a name="10804"
      >
</a
      ><a name="10805" href="StlcProp.html#10673" class="Function"
      >&#8709;&#8866;-closed&#8242;</a
      ><a name="10815"
      > </a
      ><a name="10816" class="Symbol"
      >(</a
      ><a name="10817" href="Stlc.html#19312" class="InductiveConstructor"
      >app</a
      ><a name="10820"
      > </a
      ><a name="10821" href="StlcProp.html#10821" class="Bound"
      >t&#8321;&#8758;A&#8658;B</a
      ><a name="10827"
      > </a
      ><a name="10828" href="StlcProp.html#10828" class="Bound"
      >t&#8322;&#8758;A</a
      ><a name="10832" class="Symbol"
      >)</a
      ><a name="10833"
      > </a
      ><a name="10834" class="Symbol"
      >(</a
      ><a name="10835" href="StlcProp.html#7031" class="InductiveConstructor"
      >app2</a
      ><a name="10839"
      > </a
      ><a name="10840" href="StlcProp.html#10840" class="Bound"
      >x&#8712;t&#8322;</a
      ><a name="10844" class="Symbol"
      >)</a
      ><a name="10845"
      > </a
      ><a name="10846" class="Symbol"
      >=</a
      ><a name="10847"
      > </a
      ><a name="10848" href="StlcProp.html#10673" class="Function"
      >&#8709;&#8866;-closed&#8242;</a
      ><a name="10858"
      > </a
      ><a name="10859" href="StlcProp.html#10828" class="Bound"
      >t&#8322;&#8758;A</a
      ><a name="10863"
      > </a
      ><a name="10864" href="StlcProp.html#10840" class="Bound"
      >x&#8712;t&#8322;</a
      ><a name="10868"
      >
</a
      ><a name="10869" href="StlcProp.html#10673" class="Function"
      >&#8709;&#8866;-closed&#8242;</a
      ><a name="10879"
      > </a
      ><a name="10880" href="Stlc.html#19446" class="InductiveConstructor"
      >true</a
      ><a name="10884"
      >  </a
      ><a name="10886" class="Symbol"
      >()</a
      ><a name="10888"
      >
</a
      ><a name="10889" href="StlcProp.html#10673" class="Function"
      >&#8709;&#8866;-closed&#8242;</a
      ><a name="10899"
      > </a
      ><a name="10900" href="Stlc.html#19505" class="InductiveConstructor"
      >false</a
      ><a name="10905"
      > </a
      ><a name="10906" class="Symbol"
      >()</a
      ><a name="10908"
      >
</a
      ><a name="10909" href="StlcProp.html#10673" class="Function"
      >&#8709;&#8866;-closed&#8242;</a
      ><a name="10919"
      > </a
      ><a name="10920" class="Symbol"
      >(</a
      ><a name="10921" href="Stlc.html#19564" class="InductiveConstructor Operator"
      >if</a
      ><a name="10923"
      > </a
      ><a name="10924" href="StlcProp.html#10924" class="Bound"
      >t&#8321;&#8758;bool</a
      ><a name="10931"
      > </a
      ><a name="10932" href="Stlc.html#19564" class="InductiveConstructor Operator"
      >then</a
      ><a name="10936"
      > </a
      ><a name="10937" href="StlcProp.html#10937" class="Bound"
      >t&#8322;&#8758;A</a
      ><a name="10941"
      > </a
      ><a name="10942" href="Stlc.html#19564" class="InductiveConstructor Operator"
      >else</a
      ><a name="10946"
      > </a
      ><a name="10947" href="StlcProp.html#10947" class="Bound"
      >t&#8323;&#8758;A</a
      ><a name="10951" class="Symbol"
      >)</a
      ><a name="10952"
      > </a
      ><a name="10953" class="Symbol"
      >(</a
      ><a name="10954" href="StlcProp.html#7085" class="InductiveConstructor"
      >if1</a
      ><a name="10957"
      > </a
      ><a name="10958" href="StlcProp.html#10958" class="Bound"
      >x&#8712;t&#8321;</a
      ><a name="10962" class="Symbol"
      >)</a
      ><a name="10963"
      > </a
      ><a name="10964" class="Symbol"
      >=</a
      ><a name="10965"
      > </a
      ><a name="10966" href="StlcProp.html#10673" class="Function"
      >&#8709;&#8866;-closed&#8242;</a
      ><a name="10976"
      > </a
      ><a name="10977" href="StlcProp.html#10924" class="Bound"
      >t&#8321;&#8758;bool</a
      ><a name="10984"
      > </a
      ><a name="10985" href="StlcProp.html#10958" class="Bound"
      >x&#8712;t&#8321;</a
      ><a name="10989"
      >
</a
      ><a name="10990" href="StlcProp.html#10673" class="Function"
      >&#8709;&#8866;-closed&#8242;</a
      ><a name="11000"
      > </a
      ><a name="11001" class="Symbol"
      >(</a
      ><a name="11002" href="Stlc.html#19564" class="InductiveConstructor Operator"
      >if</a
      ><a name="11004"
      > </a
      ><a name="11005" href="StlcProp.html#11005" class="Bound"
      >t&#8321;&#8758;bool</a
      ><a name="11012"
      > </a
      ><a name="11013" href="Stlc.html#19564" class="InductiveConstructor Operator"
      >then</a
      ><a name="11017"
      > </a
      ><a name="11018" href="StlcProp.html#11018" class="Bound"
      >t&#8322;&#8758;A</a
      ><a name="11022"
      > </a
      ><a name="11023" href="Stlc.html#19564" class="InductiveConstructor Operator"
      >else</a
      ><a name="11027"
      > </a
      ><a name="11028" href="StlcProp.html#11028" class="Bound"
      >t&#8323;&#8758;A</a
      ><a name="11032" class="Symbol"
      >)</a
      ><a name="11033"
      > </a
      ><a name="11034" class="Symbol"
      >(</a
      ><a name="11035" href="StlcProp.html#7156" class="InductiveConstructor"
      >if2</a
      ><a name="11038"
      > </a
      ><a name="11039" href="StlcProp.html#11039" class="Bound"
      >x&#8712;t&#8322;</a
      ><a name="11043" class="Symbol"
      >)</a
      ><a name="11044"
      > </a
      ><a name="11045" class="Symbol"
      >=</a
      ><a name="11046"
      > </a
      ><a name="11047" href="StlcProp.html#10673" class="Function"
      >&#8709;&#8866;-closed&#8242;</a
      ><a name="11057"
      > </a
      ><a name="11058" href="StlcProp.html#11018" class="Bound"
      >t&#8322;&#8758;A</a
      ><a name="11062"
      > </a
      ><a name="11063" href="StlcProp.html#11039" class="Bound"
      >x&#8712;t&#8322;</a
      ><a name="11067"
      >
</a
      ><a name="11068" href="StlcProp.html#10673" class="Function"
      >&#8709;&#8866;-closed&#8242;</a
      ><a name="11078"
      > </a
      ><a name="11079" class="Symbol"
      >(</a
      ><a name="11080" href="Stlc.html#19564" class="InductiveConstructor Operator"
      >if</a
      ><a name="11082"
      > </a
      ><a name="11083" href="StlcProp.html#11083" class="Bound"
      >t&#8321;&#8758;bool</a
      ><a name="11090"
      > </a
      ><a name="11091" href="Stlc.html#19564" class="InductiveConstructor Operator"
      >then</a
      ><a name="11095"
      > </a
      ><a name="11096" href="StlcProp.html#11096" class="Bound"
      >t&#8322;&#8758;A</a
      ><a name="11100"
      > </a
      ><a name="11101" href="Stlc.html#19564" class="InductiveConstructor Operator"
      >else</a
      ><a name="11105"
      > </a
      ><a name="11106" href="StlcProp.html#11106" class="Bound"
      >t&#8323;&#8758;A</a
      ><a name="11110" class="Symbol"
      >)</a
      ><a name="11111"
      > </a
      ><a name="11112" class="Symbol"
      >(</a
      ><a name="11113" href="StlcProp.html#7227" class="InductiveConstructor"
      >if3</a
      ><a name="11116"
      > </a
      ><a name="11117" href="StlcProp.html#11117" class="Bound"
      >x&#8712;t&#8323;</a
      ><a name="11121" class="Symbol"
      >)</a
      ><a name="11122"
      > </a
      ><a name="11123" class="Symbol"
      >=</a
      ><a name="11124"
      > </a
      ><a name="11125" href="StlcProp.html#10673" class="Function"
      >&#8709;&#8866;-closed&#8242;</a
      ><a name="11135"
      > </a
      ><a name="11136" href="StlcProp.html#11106" class="Bound"
      >t&#8323;&#8758;A</a
      ><a name="11140"
      > </a
      ><a name="11141" href="StlcProp.html#11117" class="Bound"
      >x&#8712;t&#8323;</a
      ><a name="11145"
      >
</a
      ><a name="11146" href="StlcProp.html#10673" class="Function"
      >&#8709;&#8866;-closed&#8242;</a
      ><a name="11156"
      > </a
      ><a name="11157" class="Symbol"
      >(</a
      ><a name="11158" href="Stlc.html#19196" class="InductiveConstructor"
      >abs</a
      ><a name="11161"
      > </a
      ><a name="11162" class="Symbol"
      >{</a
      ><a name="11163" class="Argument"
      >x</a
      ><a name="11164"
      > </a
      ><a name="11165" class="Symbol"
      >=</a
      ><a name="11166"
      > </a
      ><a name="11167" href="StlcProp.html#11167" class="Bound"
      >x</a
      ><a name="11168" class="Symbol"
      >}</a
      ><a name="11169"
      > </a
      ><a name="11170" href="StlcProp.html#11170" class="Bound"
      >t&#8242;&#8758;A</a
      ><a name="11174" class="Symbol"
      >)</a
      ><a name="11175"
      > </a
      ><a name="11180" class="Symbol"
      >(</a
      ><a name="11181" href="StlcProp.html#6916" class="InductiveConstructor"
      >abs</a
      ><a name="11184"
      > </a
      ><a name="11185" href="StlcProp.html#11185" class="Bound"
      >x&#8800;y</a
      ><a name="11188"
      > </a
      ><a name="11189" href="StlcProp.html#11189" class="Bound"
      >y&#8712;t&#8242;</a
      ><a name="11193" class="Symbol"
      >)</a
      ><a name="11194"
      > </a
      ><a name="11195" class="Keyword"
      >with</a
      ><a name="11199"
      > </a
      ><a name="11200" href="StlcProp.html#8168" class="Function"
      >freeInCtxt</a
      ><a name="11210"
      > </a
      ><a name="11211" href="StlcProp.html#11189" class="Bound"
      >y&#8712;t&#8242;</a
      ><a name="11215"
      > </a
      ><a name="11216" href="StlcProp.html#11170" class="Bound"
      >t&#8242;&#8758;A</a
      ><a name="11220"
      >
</a
      ><a name="11221" href="StlcProp.html#10673" class="Function"
      >&#8709;&#8866;-closed&#8242;</a
      ><a name="11231"
      > </a
      ><a name="11232" class="Symbol"
      >(</a
      ><a name="11233" class="InductiveConstructor"
      >abs</a
      ><a name="11236"
      > </a
      ><a name="11237" class="Symbol"
      >{</a
      ><a name="11238" class="Argument"
      >x</a
      ><a name="11239"
      > </a
      ><a name="11240" class="Symbol"
      >=</a
      ><a name="11241"
      > </a
      ><a name="11242" href="StlcProp.html#11242" class="Bound"
      >x</a
      ><a name="11243" class="Symbol"
      >}</a
      ><a name="11244"
      > </a
      ><a name="11245" href="StlcProp.html#11245" class="Bound"
      >t&#8242;&#8758;A</a
      ><a name="11249" class="Symbol"
      >)</a
      ><a name="11250"
      > </a
      ><a name="11255" class="Symbol"
      >(</a
      ><a name="11256" class="InductiveConstructor"
      >abs</a
      ><a name="11259"
      > </a
      ><a name="11260" href="StlcProp.html#11260" class="Bound"
      >x&#8800;y</a
      ><a name="11263"
      > </a
      ><a name="11264" href="StlcProp.html#11264" class="Bound"
      >y&#8712;t&#8242;</a
      ><a name="11268" class="Symbol"
      >)</a
      ><a name="11269"
      > </a
      ><a name="11270" class="Symbol"
      >|</a
      ><a name="11271"
      > </a
      ><a name="11272" href="StlcProp.html#11272" class="Bound"
      >A</a
      ><a name="11273"
      > </a
      ><a name="11274" href="https://agda.github.io/agda-stdlib/Data.Product.html#509" class="InductiveConstructor Operator"
      >,</a
      ><a name="11275"
      > </a
      ><a name="11276" href="StlcProp.html#11276" class="Bound"
      >y&#8758;A</a
      ><a name="11279"
      > </a
      ><a name="11280" class="Keyword"
      >with</a
      ><a name="11284"
      > </a
      ><a name="11285" href="StlcProp.html#11242" class="Bound"
      >x</a
      ><a name="11286"
      > </a
      ><a name="11287" href="Maps.html#2297" class="Function Operator"
      >&#8799;</a
      ><a name="11288"
      > </a
      ><a name="11289" href="StlcProp.html#11252" class="Bound"
      >y</a
      ><a name="11290"
      >
</a
      ><a name="11291" href="StlcProp.html#10673" class="Function"
      >&#8709;&#8866;-closed&#8242;</a
      ><a name="11301"
      > </a
      ><a name="11302" class="Symbol"
      >(</a
      ><a name="11303" class="InductiveConstructor"
      >abs</a
      ><a name="11306"
      > </a
      ><a name="11307" class="Symbol"
      >{</a
      ><a name="11308" class="Argument"
      >x</a
      ><a name="11309"
      > </a
      ><a name="11310" class="Symbol"
      >=</a
      ><a name="11311"
      > </a
      ><a name="11312" href="StlcProp.html#11312" class="Bound"
      >x</a
      ><a name="11313" class="Symbol"
      >}</a
      ><a name="11314"
      > </a
      ><a name="11315" href="StlcProp.html#11315" class="Bound"
      >t&#8242;&#8758;A</a
      ><a name="11319" class="Symbol"
      >)</a
      ><a name="11320"
      > </a
      ><a name="11325" class="Symbol"
      >(</a
      ><a name="11326" class="InductiveConstructor"
      >abs</a
      ><a name="11329"
      > </a
      ><a name="11330" href="StlcProp.html#11330" class="Bound"
      >x&#8800;y</a
      ><a name="11333"
      > </a
      ><a name="11334" href="StlcProp.html#11334" class="Bound"
      >y&#8712;t&#8242;</a
      ><a name="11338" class="Symbol"
      >)</a
      ><a name="11339"
      > </a
      ><a name="11340" class="Symbol"
      >|</a
      ><a name="11341"
      > </a
      ><a name="11342" href="StlcProp.html#11342" class="Bound"
      >A</a
      ><a name="11343"
      > </a
      ><a name="11344" href="https://agda.github.io/agda-stdlib/Data.Product.html#509" class="InductiveConstructor Operator"
      >,</a
      ><a name="11345"
      > </a
      ><a name="11346" href="StlcProp.html#11346" class="Bound"
      >y&#8758;A</a
      ><a name="11349"
      > </a
      ><a name="11350" class="Symbol"
      >|</a
      ><a name="11351"
      > </a
      ><a name="11352" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#520" class="InductiveConstructor"
      >yes</a
      ><a name="11355"
      > </a
      ><a name="11356" href="StlcProp.html#11356" class="Bound"
      >x=y</a
      ><a name="11359"
      > </a
      ><a name="11360" class="Symbol"
      >=</a
      ><a name="11361"
      > </a
      ><a name="11362" href="StlcProp.html#11330" class="Bound"
      >x&#8800;y</a
      ><a name="11365"
      > </a
      ><a name="11366" href="StlcProp.html#11356" class="Bound"
      >x=y</a
      ><a name="11369"
      >
</a
      ><a name="11370" href="StlcProp.html#10673" class="Function"
      >&#8709;&#8866;-closed&#8242;</a
      ><a name="11380"
      > </a
      ><a name="11381" class="Symbol"
      >(</a
      ><a name="11382" class="InductiveConstructor"
      >abs</a
      ><a name="11385"
      > </a
      ><a name="11386" class="Symbol"
      >{</a
      ><a name="11387" class="Argument"
      >x</a
      ><a name="11388"
      > </a
      ><a name="11389" class="Symbol"
      >=</a
      ><a name="11390"
      > </a
      ><a name="11391" href="StlcProp.html#11391" class="Bound"
      >x</a
      ><a name="11392" class="Symbol"
      >}</a
      ><a name="11393"
      > </a
      ><a name="11394" href="StlcProp.html#11394" class="Bound"
      >t&#8242;&#8758;A</a
      ><a name="11398" class="Symbol"
      >)</a
      ><a name="11399"
      > </a
      ><a name="11404" class="Symbol"
      >(</a
      ><a name="11405" class="InductiveConstructor"
      >abs</a
      ><a name="11408"
      > </a
      ><a name="11409" href="StlcProp.html#11409" class="Bound"
      >x&#8800;y</a
      ><a name="11412"
      > </a
      ><a name="11413" href="StlcProp.html#11413" class="Bound"
      >y&#8712;t&#8242;</a
      ><a name="11417" class="Symbol"
      >)</a
      ><a name="11418"
      > </a
      ><a name="11419" class="Symbol"
      >|</a
      ><a name="11420"
      > </a
      ><a name="11421" href="StlcProp.html#11421" class="Bound"
      >A</a
      ><a name="11422"
      > </a
      ><a name="11423" href="https://agda.github.io/agda-stdlib/Data.Product.html#509" class="InductiveConstructor Operator"
      >,</a
      ><a name="11424"
      > </a
      ><a name="11425" class="Symbol"
      >()</a
      ><a name="11427"
      >  </a
      ><a name="11429" class="Symbol"
      >|</a
      ><a name="11430"
      > </a
      ><a name="11431" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#547" class="InductiveConstructor"
      >no</a
      ><a name="11433"
      >  </a
      ><a name="11435" class="Symbol"
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
<a name="11823" href="StlcProp.html#11823" class="Function"
      >replaceCtxt</a
      ><a name="11834"
      > </a
      ><a name="11835" class="Symbol"
      >:</a
      ><a name="11836"
      > </a
      ><a name="11837" class="Symbol"
      >&#8704;</a
      ><a name="11838"
      > </a
      ><a name="11862" class="Symbol"
      >&#8594;</a
      ><a name="11863"
      > </a
      ><a name="11864" class="Symbol"
      >(&#8704;</a
      ><a name="11866"
      > </a
      ><a name="11871" class="Symbol"
      >&#8594;</a
      ><a name="11872"
      > </a
      ><a name="11873" href="StlcProp.html#11868" class="Bound"
      >x</a
      ><a name="11874"
      > </a
      ><a name="11875" href="StlcProp.html#6853" class="Datatype Operator"
      >FreeIn</a
      ><a name="11881"
      > </a
      ><a name="11882" href="StlcProp.html#11845" class="Bound"
      >t</a
      ><a name="11883"
      > </a
      ><a name="11884" class="Symbol"
      >&#8594;</a
      ><a name="11885"
      > </a
      ><a name="11886" href="StlcProp.html#11840" class="Bound"
      >&#915;</a
      ><a name="11887"
      > </a
      ><a name="11888" href="StlcProp.html#11868" class="Bound"
      >x</a
      ><a name="11889"
      > </a
      ><a name="11890" href="Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="11891"
      > </a
      ><a name="11892" href="StlcProp.html#11842" class="Bound"
      >&#915;&#8242;</a
      ><a name="11894"
      > </a
      ><a name="11895" href="StlcProp.html#11868" class="Bound"
      >x</a
      ><a name="11896" class="Symbol"
      >)</a
      ><a name="11897"
      >
            </a
      ><a name="11910" class="Symbol"
      >&#8594;</a
      ><a name="11911"
      > </a
      ><a name="11912" href="StlcProp.html#11840" class="Bound"
      >&#915;</a
      ><a name="11913"
      >  </a
      ><a name="11915" href="Stlc.html#19059" class="Datatype Operator"
      >&#8866;</a
      ><a name="11916"
      > </a
      ><a name="11917" href="StlcProp.html#11845" class="Bound"
      >t</a
      ><a name="11918"
      > </a
      ><a name="11919" href="Stlc.html#19059" class="Datatype Operator"
      >&#8758;</a
      ><a name="11920"
      > </a
      ><a name="11921" href="StlcProp.html#11847" class="Bound"
      >A</a
      ><a name="11922"
      >
            </a
      ><a name="11935" class="Symbol"
      >&#8594;</a
      ><a name="11936"
      > </a
      ><a name="11937" href="StlcProp.html#11842" class="Bound"
      >&#915;&#8242;</a
      ><a name="11939"
      > </a
      ><a name="11940" href="Stlc.html#19059" class="Datatype Operator"
      >&#8866;</a
      ><a name="11941"
      > </a
      ><a name="11942" href="StlcProp.html#11845" class="Bound"
      >t</a
      ><a name="11943"
      > </a
      ><a name="11944" href="Stlc.html#19059" class="Datatype Operator"
      >&#8758;</a
      ><a name="11945"
      > </a
      ><a name="11946" href="StlcProp.html#11847" class="Bound"
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
<a name="14251" href="StlcProp.html#11823" class="Function"
      >replaceCtxt</a
      ><a name="14262"
      > </a
      ><a name="14263" href="StlcProp.html#14263" class="Bound"
      >f</a
      ><a name="14264"
      > </a
      ><a name="14265" class="Symbol"
      >(</a
      ><a name="14266" href="Stlc.html#19103" class="InductiveConstructor"
      >var</a
      ><a name="14269"
      > </a
      ><a name="14270" href="StlcProp.html#14270" class="Bound"
      >x</a
      ><a name="14271"
      > </a
      ><a name="14272" href="StlcProp.html#14272" class="Bound"
      >x&#8758;A</a
      ><a name="14275" class="Symbol"
      >)</a
      ><a name="14276"
      > </a
      ><a name="14277" class="Keyword"
      >rewrite</a
      ><a name="14284"
      > </a
      ><a name="14285" href="StlcProp.html#14263" class="Bound"
      >f</a
      ><a name="14286"
      > </a
      ><a name="14287" href="StlcProp.html#6892" class="InductiveConstructor"
      >var</a
      ><a name="14290"
      > </a
      ><a name="14291" class="Symbol"
      >=</a
      ><a name="14292"
      > </a
      ><a name="14293" href="Stlc.html#19103" class="InductiveConstructor"
      >var</a
      ><a name="14296"
      > </a
      ><a name="14297" href="StlcProp.html#14270" class="Bound"
      >x</a
      ><a name="14298"
      > </a
      ><a name="14299" href="StlcProp.html#14272" class="Bound"
      >x&#8758;A</a
      ><a name="14302"
      >
</a
      ><a name="14303" href="StlcProp.html#11823" class="Function"
      >replaceCtxt</a
      ><a name="14314"
      > </a
      ><a name="14315" href="StlcProp.html#14315" class="Bound"
      >f</a
      ><a name="14316"
      > </a
      ><a name="14317" class="Symbol"
      >(</a
      ><a name="14318" href="Stlc.html#19312" class="InductiveConstructor"
      >app</a
      ><a name="14321"
      > </a
      ><a name="14322" href="StlcProp.html#14322" class="Bound"
      >t&#8321;&#8758;A&#8658;B</a
      ><a name="14328"
      > </a
      ><a name="14329" href="StlcProp.html#14329" class="Bound"
      >t&#8322;&#8758;A</a
      ><a name="14333" class="Symbol"
      >)</a
      ><a name="14334"
      >
  </a
      ><a name="14337" class="Symbol"
      >=</a
      ><a name="14338"
      > </a
      ><a name="14339" href="Stlc.html#19312" class="InductiveConstructor"
      >app</a
      ><a name="14342"
      > </a
      ><a name="14343" class="Symbol"
      >(</a
      ><a name="14344" href="StlcProp.html#11823" class="Function"
      >replaceCtxt</a
      ><a name="14355"
      > </a
      ><a name="14356" class="Symbol"
      >(</a
      ><a name="14357" href="StlcProp.html#14315" class="Bound"
      >f</a
      ><a name="14358"
      > </a
      ><a name="14359" href="https://agda.github.io/agda-stdlib/Function.html#713" class="Function Operator"
      >&#8728;</a
      ><a name="14360"
      > </a
      ><a name="14361" href="StlcProp.html#6977" class="InductiveConstructor"
      >app1</a
      ><a name="14365" class="Symbol"
      >)</a
      ><a name="14366"
      > </a
      ><a name="14367" href="StlcProp.html#14322" class="Bound"
      >t&#8321;&#8758;A&#8658;B</a
      ><a name="14373" class="Symbol"
      >)</a
      ><a name="14374"
      > </a
      ><a name="14375" class="Symbol"
      >(</a
      ><a name="14376" href="StlcProp.html#11823" class="Function"
      >replaceCtxt</a
      ><a name="14387"
      > </a
      ><a name="14388" class="Symbol"
      >(</a
      ><a name="14389" href="StlcProp.html#14315" class="Bound"
      >f</a
      ><a name="14390"
      > </a
      ><a name="14391" href="https://agda.github.io/agda-stdlib/Function.html#713" class="Function Operator"
      >&#8728;</a
      ><a name="14392"
      > </a
      ><a name="14393" href="StlcProp.html#7031" class="InductiveConstructor"
      >app2</a
      ><a name="14397" class="Symbol"
      >)</a
      ><a name="14398"
      > </a
      ><a name="14399" href="StlcProp.html#14329" class="Bound"
      >t&#8322;&#8758;A</a
      ><a name="14403" class="Symbol"
      >)</a
      ><a name="14404"
      >
</a
      ><a name="14405" href="StlcProp.html#11823" class="Function"
      >replaceCtxt</a
      ><a name="14416"
      > </a
      ><a name="14426" href="StlcProp.html#14426" class="Bound"
      >f</a
      ><a name="14427"
      > </a
      ><a name="14428" class="Symbol"
      >(</a
      ><a name="14429" href="Stlc.html#19196" class="InductiveConstructor"
      >abs</a
      ><a name="14432"
      > </a
      ><a name="14455" href="StlcProp.html#14455" class="Bound"
      >t&#8242;&#8758;B</a
      ><a name="14459" class="Symbol"
      >)</a
      ><a name="14460"
      >
  </a
      ><a name="14463" class="Symbol"
      >=</a
      ><a name="14464"
      > </a
      ><a name="14465" href="Stlc.html#19196" class="InductiveConstructor"
      >abs</a
      ><a name="14468"
      > </a
      ><a name="14469" class="Symbol"
      >(</a
      ><a name="14470" href="StlcProp.html#11823" class="Function"
      >replaceCtxt</a
      ><a name="14481"
      > </a
      ><a name="14482" href="StlcProp.html#14503" class="Function"
      >f&#8242;</a
      ><a name="14484"
      > </a
      ><a name="14485" href="StlcProp.html#14455" class="Bound"
      >t&#8242;&#8758;B</a
      ><a name="14489" class="Symbol"
      >)</a
      ><a name="14490"
      >
  </a
      ><a name="14493" class="Keyword"
      >where</a
      ><a name="14498"
      >
    </a
      ><a name="14503" href="StlcProp.html#14503" class="Function"
      >f&#8242;</a
      ><a name="14505"
      > </a
      ><a name="14506" class="Symbol"
      >:</a
      ><a name="14507"
      > </a
      ><a name="14508" class="Symbol"
      >&#8704;</a
      ><a name="14509"
      > </a
      ><a name="14514" class="Symbol"
      >&#8594;</a
      ><a name="14515"
      > </a
      ><a name="14516" href="StlcProp.html#14511" class="Bound"
      >y</a
      ><a name="14517"
      > </a
      ><a name="14518" href="StlcProp.html#6853" class="Datatype Operator"
      >FreeIn</a
      ><a name="14524"
      > </a
      ><a name="14525" href="StlcProp.html#14451" class="Bound"
      >t&#8242;</a
      ><a name="14527"
      > </a
      ><a name="14528" class="Symbol"
      >&#8594;</a
      ><a name="14529"
      > </a
      ><a name="14530" class="Symbol"
      >(</a
      ><a name="14531" href="StlcProp.html#14418" class="Bound"
      >&#915;</a
      ><a name="14532"
      > </a
      ><a name="14533" href="Stlc.html#18158" class="Function Operator"
      >,</a
      ><a name="14534"
      > </a
      ><a name="14535" href="StlcProp.html#14439" class="Bound"
      >x</a
      ><a name="14536"
      > </a
      ><a name="14537" href="Stlc.html#18158" class="Function Operator"
      >&#8758;</a
      ><a name="14538"
      > </a
      ><a name="14539" href="StlcProp.html#14443" class="Bound"
      >A</a
      ><a name="14540" class="Symbol"
      >)</a
      ><a name="14541"
      > </a
      ><a name="14542" href="StlcProp.html#14511" class="Bound"
      >y</a
      ><a name="14543"
      > </a
      ><a name="14544" href="Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="14545"
      > </a
      ><a name="14546" class="Symbol"
      >(</a
      ><a name="14547" href="StlcProp.html#14422" class="Bound"
      >&#915;&#8242;</a
      ><a name="14549"
      > </a
      ><a name="14550" href="Stlc.html#18158" class="Function Operator"
      >,</a
      ><a name="14551"
      > </a
      ><a name="14552" href="StlcProp.html#14439" class="Bound"
      >x</a
      ><a name="14553"
      > </a
      ><a name="14554" href="Stlc.html#18158" class="Function Operator"
      >&#8758;</a
      ><a name="14555"
      > </a
      ><a name="14556" href="StlcProp.html#14443" class="Bound"
      >A</a
      ><a name="14557" class="Symbol"
      >)</a
      ><a name="14558"
      > </a
      ><a name="14559" href="StlcProp.html#14511" class="Bound"
      >y</a
      ><a name="14560"
      >
    </a
      ><a name="14565" href="StlcProp.html#14503" class="Function"
      >f&#8242;</a
      ><a name="14567"
      > </a
      ><a name="14572" href="StlcProp.html#14572" class="Bound"
      >y&#8712;t&#8242;</a
      ><a name="14576"
      > </a
      ><a name="14577" class="Keyword"
      >with</a
      ><a name="14581"
      > </a
      ><a name="14582" href="StlcProp.html#14439" class="Bound"
      >x</a
      ><a name="14583"
      > </a
      ><a name="14584" href="Maps.html#2297" class="Function Operator"
      >&#8799;</a
      ><a name="14585"
      > </a
      ><a name="14586" href="StlcProp.html#14569" class="Bound"
      >y</a
      ><a name="14587"
      >
    </a
      ><a name="14592" class="Symbol"
      >...</a
      ><a name="14595"
      > </a
      ><a name="14596" class="Symbol"
      >|</a
      ><a name="14597"
      > </a
      ><a name="14598" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#520" class="InductiveConstructor"
      >yes</a
      ><a name="14601"
      > </a
      ><a name="14602" class="Symbol"
      >_</a
      ><a name="14603"
      >   </a
      ><a name="14606" class="Symbol"
      >=</a
      ><a name="14607"
      > </a
      ><a name="14608" href="Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="14612"
      >
    </a
      ><a name="14617" class="Symbol"
      >...</a
      ><a name="14620"
      > </a
      ><a name="14621" class="Symbol"
      >|</a
      ><a name="14622"
      > </a
      ><a name="14623" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#547" class="InductiveConstructor"
      >no</a
      ><a name="14625"
      >  </a
      ><a name="14627" href="StlcProp.html#14627" class="Bound"
      >x&#8800;y</a
      ><a name="14630"
      > </a
      ><a name="14631" class="Symbol"
      >=</a
      ><a name="14632"
      > </a
      ><a name="14633" href="StlcProp.html#14426" class="Bound"
      >f</a
      ><a name="14634"
      > </a
      ><a name="14635" class="Symbol"
      >(</a
      ><a name="14636" href="StlcProp.html#6916" class="InductiveConstructor"
      >abs</a
      ><a name="14639"
      > </a
      ><a name="14640" href="StlcProp.html#14627" class="Bound"
      >x&#8800;y</a
      ><a name="14643"
      > </a
      ><a name="14644" href="StlcProp.html#14572" class="Bound"
      >y&#8712;t&#8242;</a
      ><a name="14648" class="Symbol"
      >)</a
      ><a name="14649"
      >
</a
      ><a name="14650" href="StlcProp.html#11823" class="Function"
      >replaceCtxt</a
      ><a name="14661"
      > </a
      ><a name="14662" class="Symbol"
      >_</a
      ><a name="14663"
      > </a
      ><a name="14664" href="Stlc.html#19446" class="InductiveConstructor"
      >true</a
      ><a name="14668"
      >  </a
      ><a name="14670" class="Symbol"
      >=</a
      ><a name="14671"
      > </a
      ><a name="14672" href="Stlc.html#19446" class="InductiveConstructor"
      >true</a
      ><a name="14676"
      >
</a
      ><a name="14677" href="StlcProp.html#11823" class="Function"
      >replaceCtxt</a
      ><a name="14688"
      > </a
      ><a name="14689" class="Symbol"
      >_</a
      ><a name="14690"
      > </a
      ><a name="14691" href="Stlc.html#19505" class="InductiveConstructor"
      >false</a
      ><a name="14696"
      > </a
      ><a name="14697" class="Symbol"
      >=</a
      ><a name="14698"
      > </a
      ><a name="14699" href="Stlc.html#19505" class="InductiveConstructor"
      >false</a
      ><a name="14704"
      >
</a
      ><a name="14705" href="StlcProp.html#11823" class="Function"
      >replaceCtxt</a
      ><a name="14716"
      > </a
      ><a name="14717" href="StlcProp.html#14717" class="Bound"
      >f</a
      ><a name="14718"
      > </a
      ><a name="14719" class="Symbol"
      >(</a
      ><a name="14720" href="Stlc.html#19564" class="InductiveConstructor Operator"
      >if</a
      ><a name="14722"
      > </a
      ><a name="14723" href="StlcProp.html#14723" class="Bound"
      >t&#8321;&#8758;bool</a
      ><a name="14730"
      > </a
      ><a name="14731" href="Stlc.html#19564" class="InductiveConstructor Operator"
      >then</a
      ><a name="14735"
      > </a
      ><a name="14736" href="StlcProp.html#14736" class="Bound"
      >t&#8322;&#8758;A</a
      ><a name="14740"
      > </a
      ><a name="14741" href="Stlc.html#19564" class="InductiveConstructor Operator"
      >else</a
      ><a name="14745"
      > </a
      ><a name="14746" href="StlcProp.html#14746" class="Bound"
      >t&#8323;&#8758;A</a
      ><a name="14750" class="Symbol"
      >)</a
      ><a name="14751"
      >
  </a
      ><a name="14754" class="Symbol"
      >=</a
      ><a name="14755"
      > </a
      ><a name="14756" href="Stlc.html#19564" class="InductiveConstructor Operator"
      >if</a
      ><a name="14758"
      >   </a
      ><a name="14761" href="StlcProp.html#11823" class="Function"
      >replaceCtxt</a
      ><a name="14772"
      > </a
      ><a name="14773" class="Symbol"
      >(</a
      ><a name="14774" href="StlcProp.html#14717" class="Bound"
      >f</a
      ><a name="14775"
      > </a
      ><a name="14776" href="https://agda.github.io/agda-stdlib/Function.html#713" class="Function Operator"
      >&#8728;</a
      ><a name="14777"
      > </a
      ><a name="14778" href="StlcProp.html#7085" class="InductiveConstructor"
      >if1</a
      ><a name="14781" class="Symbol"
      >)</a
      ><a name="14782"
      > </a
      ><a name="14783" href="StlcProp.html#14723" class="Bound"
      >t&#8321;&#8758;bool</a
      ><a name="14790"
      >
    </a
      ><a name="14795" href="Stlc.html#19564" class="InductiveConstructor Operator"
      >then</a
      ><a name="14799"
      > </a
      ><a name="14800" href="StlcProp.html#11823" class="Function"
      >replaceCtxt</a
      ><a name="14811"
      > </a
      ><a name="14812" class="Symbol"
      >(</a
      ><a name="14813" href="StlcProp.html#14717" class="Bound"
      >f</a
      ><a name="14814"
      > </a
      ><a name="14815" href="https://agda.github.io/agda-stdlib/Function.html#713" class="Function Operator"
      >&#8728;</a
      ><a name="14816"
      > </a
      ><a name="14817" href="StlcProp.html#7156" class="InductiveConstructor"
      >if2</a
      ><a name="14820" class="Symbol"
      >)</a
      ><a name="14821"
      > </a
      ><a name="14822" href="StlcProp.html#14736" class="Bound"
      >t&#8322;&#8758;A</a
      ><a name="14826"
      >
    </a
      ><a name="14831" href="Stlc.html#19564" class="InductiveConstructor Operator"
      >else</a
      ><a name="14835"
      > </a
      ><a name="14836" href="StlcProp.html#11823" class="Function"
      >replaceCtxt</a
      ><a name="14847"
      > </a
      ><a name="14848" class="Symbol"
      >(</a
      ><a name="14849" href="StlcProp.html#14717" class="Bound"
      >f</a
      ><a name="14850"
      > </a
      ><a name="14851" href="https://agda.github.io/agda-stdlib/Function.html#713" class="Function Operator"
      >&#8728;</a
      ><a name="14852"
      > </a
      ><a name="14853" href="StlcProp.html#7227" class="InductiveConstructor"
      >if3</a
      ><a name="14856" class="Symbol"
      >)</a
      ><a name="14857"
      > </a
      ><a name="14858" href="StlcProp.html#14746" class="Bound"
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
<a name="15673" href="StlcProp.html#15673" class="Function"
      >[:=]-preserves-&#8866;</a
      ><a name="15689"
      > </a
      ><a name="15690" class="Symbol"
      >:</a
      ><a name="15691"
      > </a
      ><a name="15692" class="Symbol"
      >&#8704;</a
      ><a name="15693"
      > </a
      ><a name="15725" class="Symbol"
      >&#8594;</a
      ><a name="15726"
      > </a
      ><a name="15727" href="Stlc.html#18127" class="Function"
      >&#8709;</a
      ><a name="15728"
      > </a
      ><a name="15729" href="Stlc.html#19059" class="Datatype Operator"
      >&#8866;</a
      ><a name="15730"
      > </a
      ><a name="15731" href="StlcProp.html#15703" class="Bound"
      >v</a
      ><a name="15732"
      > </a
      ><a name="15733" href="Stlc.html#19059" class="Datatype Operator"
      >&#8758;</a
      ><a name="15734"
      > </a
      ><a name="15735" href="StlcProp.html#15699" class="Bound"
      >A</a
      ><a name="15736"
      >
                 </a
      ><a name="15754" class="Symbol"
      >&#8594;</a
      ><a name="15755"
      > </a
      ><a name="15756" href="StlcProp.html#15695" class="Bound"
      >&#915;</a
      ><a name="15757"
      > </a
      ><a name="15758" href="Stlc.html#18158" class="Function Operator"
      >,</a
      ><a name="15759"
      > </a
      ><a name="15760" href="StlcProp.html#15697" class="Bound"
      >x</a
      ><a name="15761"
      > </a
      ><a name="15762" href="Stlc.html#18158" class="Function Operator"
      >&#8758;</a
      ><a name="15763"
      > </a
      ><a name="15764" href="StlcProp.html#15699" class="Bound"
      >A</a
      ><a name="15765"
      > </a
      ><a name="15766" href="Stlc.html#19059" class="Datatype Operator"
      >&#8866;</a
      ><a name="15767"
      > </a
      ><a name="15768" href="StlcProp.html#15701" class="Bound"
      >t</a
      ><a name="15769"
      > </a
      ><a name="15770" href="Stlc.html#19059" class="Datatype Operator"
      >&#8758;</a
      ><a name="15771"
      > </a
      ><a name="15772" href="StlcProp.html#15705" class="Bound"
      >B</a
      ><a name="15773"
      >
                 </a
      ><a name="15791" class="Symbol"
      >&#8594;</a
      ><a name="15792"
      > </a
      ><a name="15793" href="StlcProp.html#15695" class="Bound"
      >&#915;</a
      ><a name="15794"
      > </a
      ><a name="15795" href="Stlc.html#18158" class="Function Operator"
      >,</a
      ><a name="15796"
      > </a
      ><a name="15797" href="StlcProp.html#15697" class="Bound"
      >x</a
      ><a name="15798"
      > </a
      ><a name="15799" href="Stlc.html#18158" class="Function Operator"
      >&#8758;</a
      ><a name="15800"
      > </a
      ><a name="15801" href="StlcProp.html#15699" class="Bound"
      >A</a
      ><a name="15802"
      > </a
      ><a name="15803" href="Stlc.html#19059" class="Datatype Operator"
      >&#8866;</a
      ><a name="15804"
      > </a
      ><a name="15805" href="Stlc.html#12129" class="Function Operator"
      >[</a
      ><a name="15806"
      > </a
      ><a name="15807" href="StlcProp.html#15697" class="Bound"
      >x</a
      ><a name="15808"
      > </a
      ><a name="15809" href="Stlc.html#12129" class="Function Operator"
      >:=</a
      ><a name="15811"
      > </a
      ><a name="15812" href="StlcProp.html#15703" class="Bound"
      >v</a
      ><a name="15813"
      > </a
      ><a name="15814" href="Stlc.html#12129" class="Function Operator"
      >]</a
      ><a name="15815"
      > </a
      ><a name="15816" href="StlcProp.html#15701" class="Bound"
      >t</a
      ><a name="15817"
      > </a
      ><a name="15818" href="Stlc.html#19059" class="Datatype Operator"
      >&#8758;</a
      ><a name="15819"
      > </a
      ><a name="15820" href="StlcProp.html#15705" class="Bound"
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
<a name="19731" href="StlcProp.html#15673" class="Function"
      >[:=]-preserves-&#8866;</a
      ><a name="19747"
      > </a
      ><a name="19756" href="StlcProp.html#19756" class="Bound"
      >v&#8758;A</a
      ><a name="19759"
      > </a
      ><a name="19760" class="Symbol"
      >(</a
      ><a name="19761" href="Stlc.html#19103" class="InductiveConstructor"
      >var</a
      ><a name="19764"
      > </a
      ><a name="19765" href="StlcProp.html#19765" class="Bound"
      >y</a
      ><a name="19766"
      > </a
      ><a name="19767" href="StlcProp.html#19767" class="Bound"
      >y&#8712;&#915;</a
      ><a name="19770" class="Symbol"
      >)</a
      ><a name="19771"
      > </a
      ><a name="19772" class="Keyword"
      >with</a
      ><a name="19776"
      > </a
      ><a name="19777" href="StlcProp.html#19753" class="Bound"
      >x</a
      ><a name="19778"
      > </a
      ><a name="19779" href="Maps.html#2297" class="Function Operator"
      >&#8799;</a
      ><a name="19780"
      > </a
      ><a name="19781" href="StlcProp.html#19765" class="Bound"
      >y</a
      ><a name="19782"
      >
</a
      ><a name="19783" class="Symbol"
      >...</a
      ><a name="19786"
      > </a
      ><a name="19787" class="Symbol"
      >|</a
      ><a name="19788"
      > </a
      ><a name="19789" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#520" class="InductiveConstructor"
      >yes</a
      ><a name="19792"
      > </a
      ><a name="19793" href="StlcProp.html#19793" class="Bound"
      >x=y</a
      ><a name="19796"
      > </a
      ><a name="19797" class="Symbol"
      >=</a
      ><a name="19798"
      > </a
      ><a name="19799" class="Symbol"
      >{!!}</a
      ><a name="19803"
      >
</a
      ><a name="19804" class="Symbol"
      >...</a
      ><a name="19807"
      > </a
      ><a name="19808" class="Symbol"
      >|</a
      ><a name="19809"
      > </a
      ><a name="19810" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#547" class="InductiveConstructor"
      >no</a
      ><a name="19812"
      >  </a
      ><a name="19814" href="StlcProp.html#19814" class="Bound"
      >x&#8800;y</a
      ><a name="19817"
      > </a
      ><a name="19818" class="Symbol"
      >=</a
      ><a name="19819"
      > </a
      ><a name="19820" class="Symbol"
      >{!!}</a
      ><a name="19824"
      >
</a
      ><a name="19825" href="StlcProp.html#15673" class="Function"
      >[:=]-preserves-&#8866;</a
      ><a name="19841"
      > </a
      ><a name="19842" href="StlcProp.html#19842" class="Bound"
      >v&#8758;A</a
      ><a name="19845"
      > </a
      ><a name="19846" class="Symbol"
      >(</a
      ><a name="19847" href="Stlc.html#19196" class="InductiveConstructor"
      >abs</a
      ><a name="19850"
      > </a
      ><a name="19851" href="StlcProp.html#19851" class="Bound"
      >t&#8242;&#8758;B</a
      ><a name="19855" class="Symbol"
      >)</a
      ><a name="19856"
      > </a
      ><a name="19857" class="Symbol"
      >=</a
      ><a name="19858"
      > </a
      ><a name="19859" class="Symbol"
      >{!!}</a
      ><a name="19863"
      >
</a
      ><a name="19864" href="StlcProp.html#15673" class="Function"
      >[:=]-preserves-&#8866;</a
      ><a name="19880"
      > </a
      ><a name="19881" href="StlcProp.html#19881" class="Bound"
      >v&#8758;A</a
      ><a name="19884"
      > </a
      ><a name="19885" class="Symbol"
      >(</a
      ><a name="19886" href="Stlc.html#19312" class="InductiveConstructor"
      >app</a
      ><a name="19889"
      > </a
      ><a name="19890" href="StlcProp.html#19890" class="Bound"
      >t&#8321;&#8758;A&#8658;B</a
      ><a name="19896"
      > </a
      ><a name="19897" href="StlcProp.html#19897" class="Bound"
      >t&#8322;&#8758;A</a
      ><a name="19901" class="Symbol"
      >)</a
      ><a name="19902"
      > </a
      ><a name="19903" class="Symbol"
      >=</a
      ><a name="19904"
      >
  </a
      ><a name="19907" href="Stlc.html#19312" class="InductiveConstructor"
      >app</a
      ><a name="19910"
      > </a
      ><a name="19911" class="Symbol"
      >(</a
      ><a name="19912" href="StlcProp.html#15673" class="Function"
      >[:=]-preserves-&#8866;</a
      ><a name="19928"
      > </a
      ><a name="19929" href="StlcProp.html#19881" class="Bound"
      >v&#8758;A</a
      ><a name="19932"
      > </a
      ><a name="19933" href="StlcProp.html#19890" class="Bound"
      >t&#8321;&#8758;A&#8658;B</a
      ><a name="19939" class="Symbol"
      >)</a
      ><a name="19940"
      > </a
      ><a name="19941" class="Symbol"
      >(</a
      ><a name="19942" href="StlcProp.html#15673" class="Function"
      >[:=]-preserves-&#8866;</a
      ><a name="19958"
      > </a
      ><a name="19959" href="StlcProp.html#19881" class="Bound"
      >v&#8758;A</a
      ><a name="19962"
      > </a
      ><a name="19963" href="StlcProp.html#19897" class="Bound"
      >t&#8322;&#8758;A</a
      ><a name="19967" class="Symbol"
      >)</a
      ><a name="19968"
      >
</a
      ><a name="19969" href="StlcProp.html#15673" class="Function"
      >[:=]-preserves-&#8866;</a
      ><a name="19985"
      > </a
      ><a name="19986" href="StlcProp.html#19986" class="Bound"
      >v&#8758;A</a
      ><a name="19989"
      > </a
      ><a name="19990" href="Stlc.html#19446" class="InductiveConstructor"
      >true</a
      ><a name="19994"
      >  </a
      ><a name="19996" class="Symbol"
      >=</a
      ><a name="19997"
      > </a
      ><a name="19998" href="Stlc.html#19446" class="InductiveConstructor"
      >true</a
      ><a name="20002"
      >
</a
      ><a name="20003" href="StlcProp.html#15673" class="Function"
      >[:=]-preserves-&#8866;</a
      ><a name="20019"
      > </a
      ><a name="20020" href="StlcProp.html#20020" class="Bound"
      >v&#8758;A</a
      ><a name="20023"
      > </a
      ><a name="20024" href="Stlc.html#19505" class="InductiveConstructor"
      >false</a
      ><a name="20029"
      > </a
      ><a name="20030" class="Symbol"
      >=</a
      ><a name="20031"
      > </a
      ><a name="20032" href="Stlc.html#19505" class="InductiveConstructor"
      >false</a
      ><a name="20037"
      >
</a
      ><a name="20038" href="StlcProp.html#15673" class="Function"
      >[:=]-preserves-&#8866;</a
      ><a name="20054"
      > </a
      ><a name="20055" href="StlcProp.html#20055" class="Bound"
      >v&#8758;A</a
      ><a name="20058"
      > </a
      ><a name="20059" class="Symbol"
      >(</a
      ><a name="20060" href="Stlc.html#19564" class="InductiveConstructor Operator"
      >if</a
      ><a name="20062"
      > </a
      ><a name="20063" href="StlcProp.html#20063" class="Bound"
      >t&#8321;&#8758;bool</a
      ><a name="20070"
      > </a
      ><a name="20071" href="Stlc.html#19564" class="InductiveConstructor Operator"
      >then</a
      ><a name="20075"
      > </a
      ><a name="20076" href="StlcProp.html#20076" class="Bound"
      >t&#8322;&#8758;B</a
      ><a name="20080"
      > </a
      ><a name="20081" href="Stlc.html#19564" class="InductiveConstructor Operator"
      >else</a
      ><a name="20085"
      > </a
      ><a name="20086" href="StlcProp.html#20086" class="Bound"
      >t&#8323;&#8758;B</a
      ><a name="20090" class="Symbol"
      >)</a
      ><a name="20091"
      > </a
      ><a name="20092" class="Symbol"
      >=</a
      ><a name="20093"
      >
  </a
      ><a name="20096" href="Stlc.html#19564" class="InductiveConstructor Operator"
      >if</a
      ><a name="20098"
      >   </a
      ><a name="20101" href="StlcProp.html#15673" class="Function"
      >[:=]-preserves-&#8866;</a
      ><a name="20117"
      > </a
      ><a name="20118" href="StlcProp.html#20055" class="Bound"
      >v&#8758;A</a
      ><a name="20121"
      > </a
      ><a name="20122" href="StlcProp.html#20063" class="Bound"
      >t&#8321;&#8758;bool</a
      ><a name="20129"
      >
  </a
      ><a name="20132" href="Stlc.html#19564" class="InductiveConstructor Operator"
      >then</a
      ><a name="20136"
      > </a
      ><a name="20137" href="StlcProp.html#15673" class="Function"
      >[:=]-preserves-&#8866;</a
      ><a name="20153"
      > </a
      ><a name="20154" href="StlcProp.html#20055" class="Bound"
      >v&#8758;A</a
      ><a name="20157"
      > </a
      ><a name="20158" href="StlcProp.html#20076" class="Bound"
      >t&#8322;&#8758;B</a
      ><a name="20162"
      >
  </a
      ><a name="20165" href="Stlc.html#19564" class="InductiveConstructor Operator"
      >else</a
      ><a name="20169"
      > </a
      ><a name="20170" href="StlcProp.html#15673" class="Function"
      >[:=]-preserves-&#8866;</a
      ><a name="20186"
      > </a
      ><a name="20187" href="StlcProp.html#20055" class="Bound"
      >v&#8758;A</a
      ><a name="20190"
      > </a
      ><a name="20191" href="StlcProp.html#20086" class="Bound"
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
