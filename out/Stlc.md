---
title     : "Stlc: The Simply Typed Lambda-Calculus"
layout    : page
permalink : /Stlc
---

This chapter defines the simply-typed lambda calculus.

## Imports
<pre class="Agda">

<a name="178" class="Keyword"
      >open</a
      ><a name="182"
      > </a
      ><a name="183" class="Keyword"
      >import</a
      ><a name="189"
      > </a
      ><a name="190" class="Module"
      >Maps</a
      ><a name="194"
      > </a
      ><a name="195" class="Keyword"
      >using</a
      ><a name="200"
      > </a
      ><a name="201" class="Symbol"
      >(</a
      ><a name="202" href="Maps.html#2215" class="Datatype"
      >Id</a
      ><a name="204" class="Symbol"
      >;</a
      ><a name="205"
      > </a
      ><a name="206" href="Maps.html#2232" class="InductiveConstructor"
      >id</a
      ><a name="208" class="Symbol"
      >;</a
      ><a name="209"
      > </a
      ><a name="210" href="Maps.html#2558" class="Function Operator"
      >_&#8799;_</a
      ><a name="213" class="Symbol"
      >;</a
      ><a name="214"
      > </a
      ><a name="215" href="Maps.html#11102" class="Function"
      >PartialMap</a
      ><a name="225" class="Symbol"
      >;</a
      ><a name="226"
      > </a
      ><a name="227" class="Keyword"
      >module</a
      ><a name="233"
      > </a
      ><a name="234" href="Maps.html#11191" class="Module"
      >PartialMap</a
      ><a name="244" class="Symbol"
      >)</a
      ><a name="245"
      >
</a
      ><a name="246" class="Keyword"
      >open</a
      ><a name="250"
      > </a
      ><a name="251" href="Maps.html#11191" class="Module"
      >PartialMap</a
      ><a name="261"
      > </a
      ><a name="262" class="Keyword"
      >using</a
      ><a name="267"
      > </a
      ><a name="268" class="Symbol"
      >(</a
      ><a name="269" href="Maps.html#11235" class="Function"
      >&#8709;</a
      ><a name="270" class="Symbol"
      >;</a
      ><a name="271"
      > </a
      ><a name="272" href="Maps.html#11317" class="Function Operator"
      >_,_&#8614;_</a
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
      ><a name="291" href="https://agda.github.io/agda-stdlib/Data.String.html#1" class="Module"
      >Data.String</a
      ><a name="302"
      > </a
      ><a name="303" class="Keyword"
      >using</a
      ><a name="308"
      > </a
      ><a name="309" class="Symbol"
      >(</a
      ><a name="310" href="https://agda.github.io/agda-stdlib/Agda.Builtin.String.html#165" class="Postulate"
      >String</a
      ><a name="316" class="Symbol"
      >)</a
      ><a name="317"
      >
</a
      ><a name="318" class="Keyword"
      >open</a
      ><a name="322"
      > </a
      ><a name="323" class="Keyword"
      >import</a
      ><a name="329"
      > </a
      ><a name="330" href="https://agda.github.io/agda-stdlib/Data.Empty.html#1" class="Module"
      >Data.Empty</a
      ><a name="340"
      > </a
      ><a name="341" class="Keyword"
      >using</a
      ><a name="346"
      > </a
      ><a name="347" class="Symbol"
      >(</a
      ><a name="348" href="https://agda.github.io/agda-stdlib/Data.Empty.html#243" class="Datatype"
      >&#8869;</a
      ><a name="349" class="Symbol"
      >;</a
      ><a name="350"
      > </a
      ><a name="351" href="https://agda.github.io/agda-stdlib/Data.Empty.html#348" class="Function"
      >&#8869;-elim</a
      ><a name="357" class="Symbol"
      >)</a
      ><a name="358"
      >
</a
      ><a name="359" class="Keyword"
      >open</a
      ><a name="363"
      > </a
      ><a name="364" class="Keyword"
      >import</a
      ><a name="370"
      > </a
      ><a name="371" href="https://agda.github.io/agda-stdlib/Data.Maybe.html#1" class="Module"
      >Data.Maybe</a
      ><a name="381"
      > </a
      ><a name="382" class="Keyword"
      >using</a
      ><a name="387"
      > </a
      ><a name="388" class="Symbol"
      >(</a
      ><a name="389" href="https://agda.github.io/agda-stdlib/Data.Maybe.Base.html#335" class="Datatype"
      >Maybe</a
      ><a name="394" class="Symbol"
      >;</a
      ><a name="395"
      > </a
      ><a name="396" href="https://agda.github.io/agda-stdlib/Data.Maybe.html#1527" class="InductiveConstructor"
      >just</a
      ><a name="400" class="Symbol"
      >;</a
      ><a name="401"
      > </a
      ><a name="402" href="https://agda.github.io/agda-stdlib/Data.Maybe.html#1588" class="InductiveConstructor"
      >nothing</a
      ><a name="409" class="Symbol"
      >)</a
      ><a name="410"
      >
</a
      ><a name="411" class="Keyword"
      >open</a
      ><a name="415"
      > </a
      ><a name="416" class="Keyword"
      >import</a
      ><a name="422"
      > </a
      ><a name="423" href="https://agda.github.io/agda-stdlib/Data.Nat.html#1" class="Module"
      >Data.Nat</a
      ><a name="431"
      > </a
      ><a name="432" class="Keyword"
      >using</a
      ><a name="437"
      > </a
      ><a name="438" class="Symbol"
      >(</a
      ><a name="439" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#97" class="Datatype"
      >&#8469;</a
      ><a name="440" class="Symbol"
      >;</a
      ><a name="441"
      > </a
      ><a name="442" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor"
      >suc</a
      ><a name="445" class="Symbol"
      >;</a
      ><a name="446"
      > </a
      ><a name="447" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#115" class="InductiveConstructor"
      >zero</a
      ><a name="451" class="Symbol"
      >;</a
      ><a name="452"
      > </a
      ><a name="453" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator"
      >_+_</a
      ><a name="456" class="Symbol"
      >)</a
      ><a name="457"
      >
</a
      ><a name="458" class="Keyword"
      >open</a
      ><a name="462"
      > </a
      ><a name="463" class="Keyword"
      >import</a
      ><a name="469"
      > </a
      ><a name="470" href="https://agda.github.io/agda-stdlib/Data.Bool.html#1" class="Module"
      >Data.Bool</a
      ><a name="479"
      > </a
      ><a name="480" class="Keyword"
      >using</a
      ><a name="485"
      > </a
      ><a name="486" class="Symbol"
      >(</a
      ><a name="487" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Bool.html#67" class="Datatype"
      >Bool</a
      ><a name="491" class="Symbol"
      >;</a
      ><a name="492"
      > </a
      ><a name="493" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Bool.html#92" class="InductiveConstructor"
      >true</a
      ><a name="497" class="Symbol"
      >;</a
      ><a name="498"
      > </a
      ><a name="499" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Bool.html#86" class="InductiveConstructor"
      >false</a
      ><a name="504" class="Symbol"
      >;</a
      ><a name="505"
      > </a
      ><a name="506" href="https://agda.github.io/agda-stdlib/Data.Bool.Base.html#831" class="Function Operator"
      >if_then_else_</a
      ><a name="519" class="Symbol"
      >)</a
      ><a name="520"
      >
</a
      ><a name="521" class="Keyword"
      >open</a
      ><a name="525"
      > </a
      ><a name="526" class="Keyword"
      >import</a
      ><a name="532"
      > </a
      ><a name="533" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#1" class="Module"
      >Relation.Nullary</a
      ><a name="549"
      > </a
      ><a name="550" class="Keyword"
      >using</a
      ><a name="555"
      > </a
      ><a name="556" class="Symbol"
      >(</a
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
      ><a name="583" href="https://agda.github.io/agda-stdlib/Relation.Nullary.Decidable.html#1" class="Module"
      >Relation.Nullary.Decidable</a
      ><a name="609"
      > </a
      ><a name="610" class="Keyword"
      >using</a
      ><a name="615"
      > </a
      ><a name="616" class="Symbol"
      >(</a
      ><a name="617" href="https://agda.github.io/agda-stdlib/Relation.Nullary.Decidable.html#822" class="Function Operator"
      >&#8970;_&#8971;</a
      ><a name="620" class="Symbol"
      >)</a
      ><a name="621"
      >
</a
      ><a name="622" class="Keyword"
      >open</a
      ><a name="626"
      > </a
      ><a name="627" class="Keyword"
      >import</a
      ><a name="633"
      > </a
      ><a name="634" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#1" class="Module"
      >Relation.Binary.PropositionalEquality</a
      ><a name="671"
      > </a
      ><a name="672" class="Keyword"
      >using</a
      ><a name="677"
      > </a
      ><a name="678" class="Symbol"
      >(</a
      ><a name="679" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >_&#8801;_</a
      ><a name="682" class="Symbol"
      >;</a
      ><a name="683"
      > </a
      ><a name="684" href="https://agda.github.io/agda-stdlib/Relation.Binary.Core.html#4493" class="Function Operator"
      >_&#8802;_</a
      ><a name="687" class="Symbol"
      >;</a
      ><a name="688"
      > </a
      ><a name="689" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="693" class="Symbol"
      >)</a
      ><a name="694"
      >
</a
      ><a name="695" class="Comment"
      >-- open import Relation.Binary.Core using (Rel)</a
      ><a name="742"
      >
</a
      ><a name="743" class="Comment"
      >-- open import Data.Product using (&#8707;; &#8708;; _,_)</a
      ><a name="788"
      >
</a
      ><a name="789" class="Comment"
      >-- open import Function using (_&#8728;_; _$_)</a
      >

</pre>


## Syntax

Syntax of types and terms. All source terms are labeled with $ᵀ$.

<pre class="Agda">

<a name="934" class="Keyword"
      >infixr</a
      ><a name="940"
      > </a
      ><a name="941" class="Number"
      >100</a
      ><a name="944"
      > </a
      ><a name="945" href="Stlc.html#1001" class="InductiveConstructor Operator"
      >_&#8658;_</a
      ><a name="948"
      >
</a
      ><a name="949" class="Keyword"
      >infixl</a
      ><a name="955"
      > </a
      ><a name="956" class="Number"
      >100</a
      ><a name="959"
      > </a
      ><a name="960" href="Stlc.html#1106" class="InductiveConstructor Operator"
      >_&#183;&#7488;_</a
      ><a name="964"
      >

</a
      ><a name="966" class="Keyword"
      >data</a
      ><a name="970"
      > </a
      ><a name="971" href="Stlc.html#971" class="Datatype"
      >Type</a
      ><a name="975"
      > </a
      ><a name="976" class="Symbol"
      >:</a
      ><a name="977"
      > </a
      ><a name="978" class="PrimitiveType"
      >Set</a
      ><a name="981"
      > </a
      ><a name="982" class="Keyword"
      >where</a
      ><a name="987"
      >
  </a
      ><a name="990" href="Stlc.html#990" class="InductiveConstructor"
      >&#120121;</a
      ><a name="991"
      > </a
      ><a name="992" class="Symbol"
      >:</a
      ><a name="993"
      > </a
      ><a name="994" href="Stlc.html#971" class="Datatype"
      >Type</a
      ><a name="998"
      >
  </a
      ><a name="1001" href="Stlc.html#1001" class="InductiveConstructor Operator"
      >_&#8658;_</a
      ><a name="1004"
      > </a
      ><a name="1005" class="Symbol"
      >:</a
      ><a name="1006"
      > </a
      ><a name="1007" href="Stlc.html#971" class="Datatype"
      >Type</a
      ><a name="1011"
      > </a
      ><a name="1012" class="Symbol"
      >&#8594;</a
      ><a name="1013"
      > </a
      ><a name="1014" href="Stlc.html#971" class="Datatype"
      >Type</a
      ><a name="1018"
      > </a
      ><a name="1019" class="Symbol"
      >&#8594;</a
      ><a name="1020"
      > </a
      ><a name="1021" href="Stlc.html#971" class="Datatype"
      >Type</a
      ><a name="1025"
      >

</a
      ><a name="1027" class="Keyword"
      >data</a
      ><a name="1031"
      > </a
      ><a name="1032" href="Stlc.html#1032" class="Datatype"
      >Term</a
      ><a name="1036"
      > </a
      ><a name="1037" class="Symbol"
      >:</a
      ><a name="1038"
      > </a
      ><a name="1039" class="PrimitiveType"
      >Set</a
      ><a name="1042"
      > </a
      ><a name="1043" class="Keyword"
      >where</a
      ><a name="1048"
      >
  </a
      ><a name="1051" href="Stlc.html#1051" class="InductiveConstructor"
      >var&#7488;</a
      ><a name="1055"
      > </a
      ><a name="1056" class="Symbol"
      >:</a
      ><a name="1057"
      > </a
      ><a name="1058" href="Maps.html#2215" class="Datatype"
      >Id</a
      ><a name="1060"
      > </a
      ><a name="1061" class="Symbol"
      >&#8594;</a
      ><a name="1062"
      > </a
      ><a name="1063" href="Stlc.html#1032" class="Datatype"
      >Term</a
      ><a name="1067"
      >
  </a
      ><a name="1070" href="Stlc.html#1070" class="InductiveConstructor Operator"
      >&#955;&#7488;_&#8712;_&#8658;_</a
      ><a name="1077"
      > </a
      ><a name="1078" class="Symbol"
      >:</a
      ><a name="1079"
      > </a
      ><a name="1080" href="Maps.html#2215" class="Datatype"
      >Id</a
      ><a name="1082"
      > </a
      ><a name="1083" class="Symbol"
      >&#8594;</a
      ><a name="1084"
      > </a
      ><a name="1085" href="Stlc.html#971" class="Datatype"
      >Type</a
      ><a name="1089"
      > </a
      ><a name="1090" class="Symbol"
      >&#8594;</a
      ><a name="1091"
      > </a
      ><a name="1092" href="Stlc.html#1032" class="Datatype"
      >Term</a
      ><a name="1096"
      > </a
      ><a name="1097" class="Symbol"
      >&#8594;</a
      ><a name="1098"
      > </a
      ><a name="1099" href="Stlc.html#1032" class="Datatype"
      >Term</a
      ><a name="1103"
      >
  </a
      ><a name="1106" href="Stlc.html#1106" class="InductiveConstructor Operator"
      >_&#183;&#7488;_</a
      ><a name="1110"
      > </a
      ><a name="1111" class="Symbol"
      >:</a
      ><a name="1112"
      > </a
      ><a name="1113" href="Stlc.html#1032" class="Datatype"
      >Term</a
      ><a name="1117"
      > </a
      ><a name="1118" class="Symbol"
      >&#8594;</a
      ><a name="1119"
      > </a
      ><a name="1120" href="Stlc.html#1032" class="Datatype"
      >Term</a
      ><a name="1124"
      > </a
      ><a name="1125" class="Symbol"
      >&#8594;</a
      ><a name="1126"
      > </a
      ><a name="1127" href="Stlc.html#1032" class="Datatype"
      >Term</a
      ><a name="1131"
      >
  </a
      ><a name="1134" href="Stlc.html#1134" class="InductiveConstructor"
      >true&#7488;</a
      ><a name="1139"
      > </a
      ><a name="1140" class="Symbol"
      >:</a
      ><a name="1141"
      > </a
      ><a name="1142" href="Stlc.html#1032" class="Datatype"
      >Term</a
      ><a name="1146"
      >
  </a
      ><a name="1149" href="Stlc.html#1149" class="InductiveConstructor"
      >false&#7488;</a
      ><a name="1155"
      > </a
      ><a name="1156" class="Symbol"
      >:</a
      ><a name="1157"
      > </a
      ><a name="1158" href="Stlc.html#1032" class="Datatype"
      >Term</a
      ><a name="1162"
      >
  </a
      ><a name="1165" href="Stlc.html#1165" class="InductiveConstructor Operator"
      >if&#7488;_then_else_</a
      ><a name="1179"
      > </a
      ><a name="1180" class="Symbol"
      >:</a
      ><a name="1181"
      > </a
      ><a name="1182" href="Stlc.html#1032" class="Datatype"
      >Term</a
      ><a name="1186"
      > </a
      ><a name="1187" class="Symbol"
      >&#8594;</a
      ><a name="1188"
      > </a
      ><a name="1189" href="Stlc.html#1032" class="Datatype"
      >Term</a
      ><a name="1193"
      > </a
      ><a name="1194" class="Symbol"
      >&#8594;</a
      ><a name="1195"
      > </a
      ><a name="1196" href="Stlc.html#1032" class="Datatype"
      >Term</a
      ><a name="1200"
      > </a
      ><a name="1201" class="Symbol"
      >&#8594;</a
      ><a name="1202"
      > </a
      ><a name="1203" href="Stlc.html#1032" class="Datatype"
      >Term</a
      >

</pre>

Some examples.
<pre class="Agda">

<a name="1248" href="Stlc.html#1248" class="Function"
      >f</a
      ><a name="1249"
      > </a
      ><a name="1250" href="Stlc.html#1250" class="Function"
      >x</a
      ><a name="1251"
      > </a
      ><a name="1252" href="Stlc.html#1252" class="Function"
      >y</a
      ><a name="1253"
      > </a
      ><a name="1254" class="Symbol"
      >:</a
      ><a name="1255"
      > </a
      ><a name="1256" href="Maps.html#2215" class="Datatype"
      >Id</a
      ><a name="1258"
      >
</a
      ><a name="1259" href="Stlc.html#1248" class="Function"
      >f</a
      ><a name="1260"
      >  </a
      ><a name="1262" class="Symbol"
      >=</a
      ><a name="1263"
      >  </a
      ><a name="1265" href="Maps.html#2232" class="InductiveConstructor"
      >id</a
      ><a name="1267"
      > </a
      ><a name="1268" class="String"
      >&quot;f&quot;</a
      ><a name="1271"
      >
</a
      ><a name="1272" href="Stlc.html#1250" class="Function"
      >x</a
      ><a name="1273"
      >  </a
      ><a name="1275" class="Symbol"
      >=</a
      ><a name="1276"
      >  </a
      ><a name="1278" href="Maps.html#2232" class="InductiveConstructor"
      >id</a
      ><a name="1280"
      > </a
      ><a name="1281" class="String"
      >&quot;x&quot;</a
      ><a name="1284"
      >
</a
      ><a name="1285" href="Stlc.html#1252" class="Function"
      >y</a
      ><a name="1286"
      >  </a
      ><a name="1288" class="Symbol"
      >=</a
      ><a name="1289"
      >  </a
      ><a name="1291" href="Maps.html#2232" class="InductiveConstructor"
      >id</a
      ><a name="1293"
      > </a
      ><a name="1294" class="String"
      >&quot;y&quot;</a
      ><a name="1297"
      >

</a
      ><a name="1299" href="Stlc.html#1299" class="Function"
      >I[&#120121;]</a
      ><a name="1303"
      > </a
      ><a name="1304" href="Stlc.html#1304" class="Function"
      >I[&#120121;&#8658;&#120121;]</a
      ><a name="1310"
      > </a
      ><a name="1311" href="Stlc.html#1311" class="Function"
      >K[&#120121;][&#120121;]</a
      ><a name="1318"
      > </a
      ><a name="1319" href="Stlc.html#1319" class="Function"
      >not[&#120121;]</a
      ><a name="1325"
      > </a
      ><a name="1326" class="Symbol"
      >:</a
      ><a name="1327"
      > </a
      ><a name="1328" href="Stlc.html#1032" class="Datatype"
      >Term</a
      ><a name="1332"
      > 
</a
      ><a name="1334" href="Stlc.html#1299" class="Function"
      >I[&#120121;]</a
      ><a name="1338"
      >  </a
      ><a name="1340" class="Symbol"
      >=</a
      ><a name="1341"
      >  </a
      ><a name="1343" class="Symbol"
      >(</a
      ><a name="1344" href="Stlc.html#1070" class="InductiveConstructor Operator"
      >&#955;&#7488;</a
      ><a name="1346"
      > </a
      ><a name="1347" href="Stlc.html#1250" class="Function"
      >x</a
      ><a name="1348"
      > </a
      ><a name="1349" href="Stlc.html#1070" class="InductiveConstructor Operator"
      >&#8712;</a
      ><a name="1350"
      > </a
      ><a name="1351" href="Stlc.html#990" class="InductiveConstructor"
      >&#120121;</a
      ><a name="1352"
      > </a
      ><a name="1353" href="Stlc.html#1070" class="InductiveConstructor Operator"
      >&#8658;</a
      ><a name="1354"
      > </a
      ><a name="1355" class="Symbol"
      >(</a
      ><a name="1356" href="Stlc.html#1051" class="InductiveConstructor"
      >var&#7488;</a
      ><a name="1360"
      > </a
      ><a name="1361" href="Stlc.html#1250" class="Function"
      >x</a
      ><a name="1362" class="Symbol"
      >))</a
      ><a name="1364"
      >
</a
      ><a name="1365" href="Stlc.html#1304" class="Function"
      >I[&#120121;&#8658;&#120121;]</a
      ><a name="1371"
      >  </a
      ><a name="1373" class="Symbol"
      >=</a
      ><a name="1374"
      >  </a
      ><a name="1376" class="Symbol"
      >(</a
      ><a name="1377" href="Stlc.html#1070" class="InductiveConstructor Operator"
      >&#955;&#7488;</a
      ><a name="1379"
      > </a
      ><a name="1380" href="Stlc.html#1248" class="Function"
      >f</a
      ><a name="1381"
      > </a
      ><a name="1382" href="Stlc.html#1070" class="InductiveConstructor Operator"
      >&#8712;</a
      ><a name="1383"
      > </a
      ><a name="1384" class="Symbol"
      >(</a
      ><a name="1385" href="Stlc.html#990" class="InductiveConstructor"
      >&#120121;</a
      ><a name="1386"
      > </a
      ><a name="1387" href="Stlc.html#1001" class="InductiveConstructor Operator"
      >&#8658;</a
      ><a name="1388"
      > </a
      ><a name="1389" href="Stlc.html#990" class="InductiveConstructor"
      >&#120121;</a
      ><a name="1390" class="Symbol"
      >)</a
      ><a name="1391"
      > </a
      ><a name="1392" href="Stlc.html#1070" class="InductiveConstructor Operator"
      >&#8658;</a
      ><a name="1393"
      > </a
      ><a name="1394" class="Symbol"
      >(</a
      ><a name="1395" href="Stlc.html#1070" class="InductiveConstructor Operator"
      >&#955;&#7488;</a
      ><a name="1397"
      > </a
      ><a name="1398" href="Stlc.html#1250" class="Function"
      >x</a
      ><a name="1399"
      > </a
      ><a name="1400" href="Stlc.html#1070" class="InductiveConstructor Operator"
      >&#8712;</a
      ><a name="1401"
      > </a
      ><a name="1402" href="Stlc.html#990" class="InductiveConstructor"
      >&#120121;</a
      ><a name="1403"
      > </a
      ><a name="1404" href="Stlc.html#1070" class="InductiveConstructor Operator"
      >&#8658;</a
      ><a name="1405"
      > </a
      ><a name="1406" class="Symbol"
      >((</a
      ><a name="1408" href="Stlc.html#1051" class="InductiveConstructor"
      >var&#7488;</a
      ><a name="1412"
      > </a
      ><a name="1413" href="Stlc.html#1248" class="Function"
      >f</a
      ><a name="1414" class="Symbol"
      >)</a
      ><a name="1415"
      > </a
      ><a name="1416" href="Stlc.html#1106" class="InductiveConstructor Operator"
      >&#183;&#7488;</a
      ><a name="1418"
      > </a
      ><a name="1419" class="Symbol"
      >(</a
      ><a name="1420" href="Stlc.html#1051" class="InductiveConstructor"
      >var&#7488;</a
      ><a name="1424"
      > </a
      ><a name="1425" href="Stlc.html#1250" class="Function"
      >x</a
      ><a name="1426" class="Symbol"
      >))))</a
      ><a name="1430"
      >
</a
      ><a name="1431" href="Stlc.html#1311" class="Function"
      >K[&#120121;][&#120121;]</a
      ><a name="1438"
      >  </a
      ><a name="1440" class="Symbol"
      >=</a
      ><a name="1441"
      >  </a
      ><a name="1443" class="Symbol"
      >(</a
      ><a name="1444" href="Stlc.html#1070" class="InductiveConstructor Operator"
      >&#955;&#7488;</a
      ><a name="1446"
      > </a
      ><a name="1447" href="Stlc.html#1250" class="Function"
      >x</a
      ><a name="1448"
      > </a
      ><a name="1449" href="Stlc.html#1070" class="InductiveConstructor Operator"
      >&#8712;</a
      ><a name="1450"
      > </a
      ><a name="1451" href="Stlc.html#990" class="InductiveConstructor"
      >&#120121;</a
      ><a name="1452"
      > </a
      ><a name="1453" href="Stlc.html#1070" class="InductiveConstructor Operator"
      >&#8658;</a
      ><a name="1454"
      > </a
      ><a name="1455" class="Symbol"
      >(</a
      ><a name="1456" href="Stlc.html#1070" class="InductiveConstructor Operator"
      >&#955;&#7488;</a
      ><a name="1458"
      > </a
      ><a name="1459" href="Stlc.html#1252" class="Function"
      >y</a
      ><a name="1460"
      > </a
      ><a name="1461" href="Stlc.html#1070" class="InductiveConstructor Operator"
      >&#8712;</a
      ><a name="1462"
      > </a
      ><a name="1463" href="Stlc.html#990" class="InductiveConstructor"
      >&#120121;</a
      ><a name="1464"
      > </a
      ><a name="1465" href="Stlc.html#1070" class="InductiveConstructor Operator"
      >&#8658;</a
      ><a name="1466"
      > </a
      ><a name="1467" class="Symbol"
      >(</a
      ><a name="1468" href="Stlc.html#1051" class="InductiveConstructor"
      >var&#7488;</a
      ><a name="1472"
      > </a
      ><a name="1473" href="Stlc.html#1250" class="Function"
      >x</a
      ><a name="1474" class="Symbol"
      >)))</a
      ><a name="1477"
      >
</a
      ><a name="1478" href="Stlc.html#1319" class="Function"
      >not[&#120121;]</a
      ><a name="1484"
      >  </a
      ><a name="1486" class="Symbol"
      >=</a
      ><a name="1487"
      >  </a
      ><a name="1489" class="Symbol"
      >(</a
      ><a name="1490" href="Stlc.html#1070" class="InductiveConstructor Operator"
      >&#955;&#7488;</a
      ><a name="1492"
      > </a
      ><a name="1493" href="Stlc.html#1250" class="Function"
      >x</a
      ><a name="1494"
      > </a
      ><a name="1495" href="Stlc.html#1070" class="InductiveConstructor Operator"
      >&#8712;</a
      ><a name="1496"
      > </a
      ><a name="1497" href="Stlc.html#990" class="InductiveConstructor"
      >&#120121;</a
      ><a name="1498"
      > </a
      ><a name="1499" href="Stlc.html#1070" class="InductiveConstructor Operator"
      >&#8658;</a
      ><a name="1500"
      > </a
      ><a name="1501" class="Symbol"
      >(</a
      ><a name="1502" href="Stlc.html#1165" class="InductiveConstructor Operator"
      >if&#7488;</a
      ><a name="1505"
      > </a
      ><a name="1506" class="Symbol"
      >(</a
      ><a name="1507" href="Stlc.html#1051" class="InductiveConstructor"
      >var&#7488;</a
      ><a name="1511"
      > </a
      ><a name="1512" href="Stlc.html#1250" class="Function"
      >x</a
      ><a name="1513" class="Symbol"
      >)</a
      ><a name="1514"
      > </a
      ><a name="1515" href="Stlc.html#1165" class="InductiveConstructor Operator"
      >then</a
      ><a name="1519"
      > </a
      ><a name="1520" href="Stlc.html#1149" class="InductiveConstructor"
      >false&#7488;</a
      ><a name="1526"
      > </a
      ><a name="1527" href="Stlc.html#1165" class="InductiveConstructor Operator"
      >else</a
      ><a name="1531"
      > </a
      ><a name="1532" href="Stlc.html#1134" class="InductiveConstructor"
      >true&#7488;</a
      ><a name="1537" class="Symbol"
      >))</a
      >

</pre>

## Values

<pre class="Agda">

<a name="1576" class="Keyword"
      >data</a
      ><a name="1580"
      > </a
      ><a name="1581" href="Stlc.html#1581" class="Datatype"
      >value</a
      ><a name="1586"
      > </a
      ><a name="1587" class="Symbol"
      >:</a
      ><a name="1588"
      > </a
      ><a name="1589" href="Stlc.html#1032" class="Datatype"
      >Term</a
      ><a name="1593"
      > </a
      ><a name="1594" class="Symbol"
      >&#8594;</a
      ><a name="1595"
      > </a
      ><a name="1596" class="PrimitiveType"
      >Set</a
      ><a name="1599"
      > </a
      ><a name="1600" class="Keyword"
      >where</a
      ><a name="1605"
      >
  </a
      ><a name="1608" href="Stlc.html#1608" class="InductiveConstructor"
      >value-&#955;&#7488;</a
      ><a name="1616"
      > </a
      ><a name="1617" class="Symbol"
      >:</a
      ><a name="1618"
      > </a
      ><a name="1619" class="Symbol"
      >&#8704;</a
      ><a name="1620"
      > </a
      ><a name="1621" class="Symbol"
      >{</a
      ><a name="1622" href="Stlc.html#1622" class="Bound"
      >x</a
      ><a name="1623"
      > </a
      ><a name="1624" href="Stlc.html#1624" class="Bound"
      >A</a
      ><a name="1625"
      > </a
      ><a name="1626" href="Stlc.html#1626" class="Bound"
      >N</a
      ><a name="1627" class="Symbol"
      >}</a
      ><a name="1628"
      > </a
      ><a name="1629" class="Symbol"
      >&#8594;</a
      ><a name="1630"
      > </a
      ><a name="1631" href="Stlc.html#1581" class="Datatype"
      >value</a
      ><a name="1636"
      > </a
      ><a name="1637" class="Symbol"
      >(</a
      ><a name="1638" href="Stlc.html#1070" class="InductiveConstructor Operator"
      >&#955;&#7488;</a
      ><a name="1640"
      > </a
      ><a name="1641" href="Stlc.html#1622" class="Bound"
      >x</a
      ><a name="1642"
      > </a
      ><a name="1643" href="Stlc.html#1070" class="InductiveConstructor Operator"
      >&#8712;</a
      ><a name="1644"
      > </a
      ><a name="1645" href="Stlc.html#1624" class="Bound"
      >A</a
      ><a name="1646"
      > </a
      ><a name="1647" href="Stlc.html#1070" class="InductiveConstructor Operator"
      >&#8658;</a
      ><a name="1648"
      > </a
      ><a name="1649" href="Stlc.html#1626" class="Bound"
      >N</a
      ><a name="1650" class="Symbol"
      >)</a
      ><a name="1651"
      >
  </a
      ><a name="1654" href="Stlc.html#1654" class="InductiveConstructor"
      >value-true&#7488;</a
      ><a name="1665"
      > </a
      ><a name="1666" class="Symbol"
      >:</a
      ><a name="1667"
      > </a
      ><a name="1668" href="Stlc.html#1581" class="Datatype"
      >value</a
      ><a name="1673"
      > </a
      ><a name="1674" class="Symbol"
      >(</a
      ><a name="1675" href="Stlc.html#1134" class="InductiveConstructor"
      >true&#7488;</a
      ><a name="1680" class="Symbol"
      >)</a
      ><a name="1681"
      >
  </a
      ><a name="1684" href="Stlc.html#1684" class="InductiveConstructor"
      >value-false&#7488;</a
      ><a name="1696"
      > </a
      ><a name="1697" class="Symbol"
      >:</a
      ><a name="1698"
      > </a
      ><a name="1699" href="Stlc.html#1581" class="Datatype"
      >value</a
      ><a name="1704"
      > </a
      ><a name="1705" class="Symbol"
      >(</a
      ><a name="1706" href="Stlc.html#1149" class="InductiveConstructor"
      >false&#7488;</a
      ><a name="1712" class="Symbol"
      >)</a
      >

</pre>

## Substitution

<pre class="Agda">

<a name="1756" href="Stlc.html#1756" class="Function Operator"
      >_[_:=_]</a
      ><a name="1763"
      > </a
      ><a name="1764" class="Symbol"
      >:</a
      ><a name="1765"
      > </a
      ><a name="1766" href="Stlc.html#1032" class="Datatype"
      >Term</a
      ><a name="1770"
      > </a
      ><a name="1771" class="Symbol"
      >&#8594;</a
      ><a name="1772"
      > </a
      ><a name="1773" href="Maps.html#2215" class="Datatype"
      >Id</a
      ><a name="1775"
      > </a
      ><a name="1776" class="Symbol"
      >&#8594;</a
      ><a name="1777"
      > </a
      ><a name="1778" href="Stlc.html#1032" class="Datatype"
      >Term</a
      ><a name="1782"
      > </a
      ><a name="1783" class="Symbol"
      >&#8594;</a
      ><a name="1784"
      > </a
      ><a name="1785" href="Stlc.html#1032" class="Datatype"
      >Term</a
      ><a name="1789"
      >
</a
      ><a name="1790" class="Symbol"
      >(</a
      ><a name="1791" href="Stlc.html#1051" class="InductiveConstructor"
      >var&#7488;</a
      ><a name="1795"
      > </a
      ><a name="1796" href="Stlc.html#1796" class="Bound"
      >x&#8242;</a
      ><a name="1798" class="Symbol"
      >)</a
      ><a name="1799"
      > </a
      ><a name="1800" href="Stlc.html#1756" class="Function Operator"
      >[</a
      ><a name="1801"
      > </a
      ><a name="1802" href="Stlc.html#1802" class="Bound"
      >x</a
      ><a name="1803"
      > </a
      ><a name="1804" href="Stlc.html#1756" class="Function Operator"
      >:=</a
      ><a name="1806"
      > </a
      ><a name="1807" href="Stlc.html#1807" class="Bound"
      >V</a
      ><a name="1808"
      > </a
      ><a name="1809" href="Stlc.html#1756" class="Function Operator"
      >]</a
      ><a name="1810"
      > </a
      ><a name="1811" class="Keyword"
      >with</a
      ><a name="1815"
      > </a
      ><a name="1816" href="Stlc.html#1802" class="Bound"
      >x</a
      ><a name="1817"
      > </a
      ><a name="1818" href="Maps.html#2558" class="Function Operator"
      >&#8799;</a
      ><a name="1819"
      > </a
      ><a name="1820" href="Stlc.html#1796" class="Bound"
      >x&#8242;</a
      ><a name="1822"
      >
</a
      ><a name="1823" class="Symbol"
      >...</a
      ><a name="1826"
      > </a
      ><a name="1827" class="Symbol"
      >|</a
      ><a name="1828"
      > </a
      ><a name="1829" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#520" class="InductiveConstructor"
      >yes</a
      ><a name="1832"
      > </a
      ><a name="1833" class="Symbol"
      >_</a
      ><a name="1834"
      > </a
      ><a name="1835" class="Symbol"
      >=</a
      ><a name="1836"
      > </a
      ><a name="1837" href="Stlc.html#1807" class="Bound"
      >V</a
      ><a name="1838"
      >
</a
      ><a name="1839" class="Symbol"
      >...</a
      ><a name="1842"
      > </a
      ><a name="1843" class="Symbol"
      >|</a
      ><a name="1844"
      > </a
      ><a name="1845" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#547" class="InductiveConstructor"
      >no</a
      ><a name="1847"
      >  </a
      ><a name="1849" class="Symbol"
      >_</a
      ><a name="1850"
      > </a
      ><a name="1851" class="Symbol"
      >=</a
      ><a name="1852"
      > </a
      ><a name="1853" href="Stlc.html#1051" class="InductiveConstructor"
      >var&#7488;</a
      ><a name="1857"
      > </a
      ><a name="1858" href="Stlc.html#1796" class="Bound"
      >x&#8242;</a
      ><a name="1860"
      >
</a
      ><a name="1861" class="Symbol"
      >(</a
      ><a name="1862" href="Stlc.html#1070" class="InductiveConstructor Operator"
      >&#955;&#7488;</a
      ><a name="1864"
      > </a
      ><a name="1865" href="Stlc.html#1865" class="Bound"
      >x&#8242;</a
      ><a name="1867"
      > </a
      ><a name="1868" href="Stlc.html#1070" class="InductiveConstructor Operator"
      >&#8712;</a
      ><a name="1869"
      > </a
      ><a name="1870" href="Stlc.html#1870" class="Bound"
      >A&#8242;</a
      ><a name="1872"
      > </a
      ><a name="1873" href="Stlc.html#1070" class="InductiveConstructor Operator"
      >&#8658;</a
      ><a name="1874"
      > </a
      ><a name="1875" href="Stlc.html#1875" class="Bound"
      >N&#8242;</a
      ><a name="1877" class="Symbol"
      >)</a
      ><a name="1878"
      > </a
      ><a name="1879" href="Stlc.html#1756" class="Function Operator"
      >[</a
      ><a name="1880"
      > </a
      ><a name="1881" href="Stlc.html#1881" class="Bound"
      >x</a
      ><a name="1882"
      > </a
      ><a name="1883" href="Stlc.html#1756" class="Function Operator"
      >:=</a
      ><a name="1885"
      > </a
      ><a name="1886" href="Stlc.html#1886" class="Bound"
      >V</a
      ><a name="1887"
      > </a
      ><a name="1888" href="Stlc.html#1756" class="Function Operator"
      >]</a
      ><a name="1889"
      > </a
      ><a name="1890" class="Keyword"
      >with</a
      ><a name="1894"
      > </a
      ><a name="1895" href="Stlc.html#1881" class="Bound"
      >x</a
      ><a name="1896"
      > </a
      ><a name="1897" href="Maps.html#2558" class="Function Operator"
      >&#8799;</a
      ><a name="1898"
      > </a
      ><a name="1899" href="Stlc.html#1865" class="Bound"
      >x&#8242;</a
      ><a name="1901"
      >
</a
      ><a name="1902" class="Symbol"
      >...</a
      ><a name="1905"
      > </a
      ><a name="1906" class="Symbol"
      >|</a
      ><a name="1907"
      > </a
      ><a name="1908" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#520" class="InductiveConstructor"
      >yes</a
      ><a name="1911"
      > </a
      ><a name="1912" class="Symbol"
      >_</a
      ><a name="1913"
      > </a
      ><a name="1914" class="Symbol"
      >=</a
      ><a name="1915"
      > </a
      ><a name="1916" href="Stlc.html#1070" class="InductiveConstructor Operator"
      >&#955;&#7488;</a
      ><a name="1918"
      > </a
      ><a name="1919" href="Stlc.html#1865" class="Bound"
      >x&#8242;</a
      ><a name="1921"
      > </a
      ><a name="1922" href="Stlc.html#1070" class="InductiveConstructor Operator"
      >&#8712;</a
      ><a name="1923"
      > </a
      ><a name="1924" href="Stlc.html#1870" class="Bound"
      >A&#8242;</a
      ><a name="1926"
      > </a
      ><a name="1927" href="Stlc.html#1070" class="InductiveConstructor Operator"
      >&#8658;</a
      ><a name="1928"
      > </a
      ><a name="1929" href="Stlc.html#1875" class="Bound"
      >N&#8242;</a
      ><a name="1931"
      >
</a
      ><a name="1932" class="Symbol"
      >...</a
      ><a name="1935"
      > </a
      ><a name="1936" class="Symbol"
      >|</a
      ><a name="1937"
      > </a
      ><a name="1938" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#547" class="InductiveConstructor"
      >no</a
      ><a name="1940"
      >  </a
      ><a name="1942" class="Symbol"
      >_</a
      ><a name="1943"
      > </a
      ><a name="1944" class="Symbol"
      >=</a
      ><a name="1945"
      > </a
      ><a name="1946" href="Stlc.html#1070" class="InductiveConstructor Operator"
      >&#955;&#7488;</a
      ><a name="1948"
      > </a
      ><a name="1949" href="Stlc.html#1865" class="Bound"
      >x&#8242;</a
      ><a name="1951"
      > </a
      ><a name="1952" href="Stlc.html#1070" class="InductiveConstructor Operator"
      >&#8712;</a
      ><a name="1953"
      > </a
      ><a name="1954" href="Stlc.html#1870" class="Bound"
      >A&#8242;</a
      ><a name="1956"
      > </a
      ><a name="1957" href="Stlc.html#1070" class="InductiveConstructor Operator"
      >&#8658;</a
      ><a name="1958"
      > </a
      ><a name="1959" class="Symbol"
      >(</a
      ><a name="1960" href="Stlc.html#1875" class="Bound"
      >N&#8242;</a
      ><a name="1962"
      > </a
      ><a name="1963" href="Stlc.html#1756" class="Function Operator"
      >[</a
      ><a name="1964"
      > </a
      ><a name="1965" href="Stlc.html#1881" class="Bound"
      >x</a
      ><a name="1966"
      > </a
      ><a name="1967" href="Stlc.html#1756" class="Function Operator"
      >:=</a
      ><a name="1969"
      > </a
      ><a name="1970" href="Stlc.html#1886" class="Bound"
      >V</a
      ><a name="1971"
      > </a
      ><a name="1972" href="Stlc.html#1756" class="Function Operator"
      >]</a
      ><a name="1973" class="Symbol"
      >)</a
      ><a name="1974"
      >
</a
      ><a name="1975" class="Symbol"
      >(</a
      ><a name="1976" href="Stlc.html#1976" class="Bound"
      >L&#8242;</a
      ><a name="1978"
      > </a
      ><a name="1979" href="Stlc.html#1106" class="InductiveConstructor Operator"
      >&#183;&#7488;</a
      ><a name="1981"
      > </a
      ><a name="1982" href="Stlc.html#1982" class="Bound"
      >M&#8242;</a
      ><a name="1984" class="Symbol"
      >)</a
      ><a name="1985"
      > </a
      ><a name="1986" href="Stlc.html#1756" class="Function Operator"
      >[</a
      ><a name="1987"
      > </a
      ><a name="1988" href="Stlc.html#1988" class="Bound"
      >x</a
      ><a name="1989"
      > </a
      ><a name="1990" href="Stlc.html#1756" class="Function Operator"
      >:=</a
      ><a name="1992"
      > </a
      ><a name="1993" href="Stlc.html#1993" class="Bound"
      >V</a
      ><a name="1994"
      > </a
      ><a name="1995" href="Stlc.html#1756" class="Function Operator"
      >]</a
      ><a name="1996"
      > </a
      ><a name="1997" class="Symbol"
      >=</a
      ><a name="1998"
      >  </a
      ><a name="2000" class="Symbol"
      >(</a
      ><a name="2001" href="Stlc.html#1976" class="Bound"
      >L&#8242;</a
      ><a name="2003"
      > </a
      ><a name="2004" href="Stlc.html#1756" class="Function Operator"
      >[</a
      ><a name="2005"
      > </a
      ><a name="2006" href="Stlc.html#1988" class="Bound"
      >x</a
      ><a name="2007"
      > </a
      ><a name="2008" href="Stlc.html#1756" class="Function Operator"
      >:=</a
      ><a name="2010"
      > </a
      ><a name="2011" href="Stlc.html#1993" class="Bound"
      >V</a
      ><a name="2012"
      > </a
      ><a name="2013" href="Stlc.html#1756" class="Function Operator"
      >]</a
      ><a name="2014" class="Symbol"
      >)</a
      ><a name="2015"
      > </a
      ><a name="2016" href="Stlc.html#1106" class="InductiveConstructor Operator"
      >&#183;&#7488;</a
      ><a name="2018"
      > </a
      ><a name="2019" class="Symbol"
      >(</a
      ><a name="2020" href="Stlc.html#1982" class="Bound"
      >M&#8242;</a
      ><a name="2022"
      > </a
      ><a name="2023" href="Stlc.html#1756" class="Function Operator"
      >[</a
      ><a name="2024"
      > </a
      ><a name="2025" href="Stlc.html#1988" class="Bound"
      >x</a
      ><a name="2026"
      > </a
      ><a name="2027" href="Stlc.html#1756" class="Function Operator"
      >:=</a
      ><a name="2029"
      > </a
      ><a name="2030" href="Stlc.html#1993" class="Bound"
      >V</a
      ><a name="2031"
      > </a
      ><a name="2032" href="Stlc.html#1756" class="Function Operator"
      >]</a
      ><a name="2033" class="Symbol"
      >)</a
      ><a name="2034"
      >
</a
      ><a name="2035" class="Symbol"
      >(</a
      ><a name="2036" href="Stlc.html#1134" class="InductiveConstructor"
      >true&#7488;</a
      ><a name="2041" class="Symbol"
      >)</a
      ><a name="2042"
      > </a
      ><a name="2043" href="Stlc.html#1756" class="Function Operator"
      >[</a
      ><a name="2044"
      > </a
      ><a name="2045" href="Stlc.html#2045" class="Bound"
      >x</a
      ><a name="2046"
      > </a
      ><a name="2047" href="Stlc.html#1756" class="Function Operator"
      >:=</a
      ><a name="2049"
      > </a
      ><a name="2050" href="Stlc.html#2050" class="Bound"
      >V</a
      ><a name="2051"
      > </a
      ><a name="2052" href="Stlc.html#1756" class="Function Operator"
      >]</a
      ><a name="2053"
      > </a
      ><a name="2054" class="Symbol"
      >=</a
      ><a name="2055"
      > </a
      ><a name="2056" href="Stlc.html#1134" class="InductiveConstructor"
      >true&#7488;</a
      ><a name="2061"
      >
</a
      ><a name="2062" class="Symbol"
      >(</a
      ><a name="2063" href="Stlc.html#1149" class="InductiveConstructor"
      >false&#7488;</a
      ><a name="2069" class="Symbol"
      >)</a
      ><a name="2070"
      > </a
      ><a name="2071" href="Stlc.html#1756" class="Function Operator"
      >[</a
      ><a name="2072"
      > </a
      ><a name="2073" href="Stlc.html#2073" class="Bound"
      >x</a
      ><a name="2074"
      > </a
      ><a name="2075" href="Stlc.html#1756" class="Function Operator"
      >:=</a
      ><a name="2077"
      > </a
      ><a name="2078" href="Stlc.html#2078" class="Bound"
      >V</a
      ><a name="2079"
      > </a
      ><a name="2080" href="Stlc.html#1756" class="Function Operator"
      >]</a
      ><a name="2081"
      > </a
      ><a name="2082" class="Symbol"
      >=</a
      ><a name="2083"
      > </a
      ><a name="2084" href="Stlc.html#1149" class="InductiveConstructor"
      >false&#7488;</a
      ><a name="2090"
      >
</a
      ><a name="2091" class="Symbol"
      >(</a
      ><a name="2092" href="Stlc.html#1165" class="InductiveConstructor Operator"
      >if&#7488;</a
      ><a name="2095"
      > </a
      ><a name="2096" href="Stlc.html#2096" class="Bound"
      >L&#8242;</a
      ><a name="2098"
      > </a
      ><a name="2099" href="Stlc.html#1165" class="InductiveConstructor Operator"
      >then</a
      ><a name="2103"
      > </a
      ><a name="2104" href="Stlc.html#2104" class="Bound"
      >M&#8242;</a
      ><a name="2106"
      > </a
      ><a name="2107" href="Stlc.html#1165" class="InductiveConstructor Operator"
      >else</a
      ><a name="2111"
      > </a
      ><a name="2112" href="Stlc.html#2112" class="Bound"
      >N&#8242;</a
      ><a name="2114" class="Symbol"
      >)</a
      ><a name="2115"
      > </a
      ><a name="2116" href="Stlc.html#1756" class="Function Operator"
      >[</a
      ><a name="2117"
      > </a
      ><a name="2118" href="Stlc.html#2118" class="Bound"
      >x</a
      ><a name="2119"
      > </a
      ><a name="2120" href="Stlc.html#1756" class="Function Operator"
      >:=</a
      ><a name="2122"
      > </a
      ><a name="2123" href="Stlc.html#2123" class="Bound"
      >V</a
      ><a name="2124"
      > </a
      ><a name="2125" href="Stlc.html#1756" class="Function Operator"
      >]</a
      ><a name="2126"
      > </a
      ><a name="2127" class="Symbol"
      >=</a
      ><a name="2128"
      > </a
      ><a name="2129" href="Stlc.html#1165" class="InductiveConstructor Operator"
      >if&#7488;</a
      ><a name="2132"
      > </a
      ><a name="2133" class="Symbol"
      >(</a
      ><a name="2134" href="Stlc.html#2096" class="Bound"
      >L&#8242;</a
      ><a name="2136"
      > </a
      ><a name="2137" href="Stlc.html#1756" class="Function Operator"
      >[</a
      ><a name="2138"
      > </a
      ><a name="2139" href="Stlc.html#2118" class="Bound"
      >x</a
      ><a name="2140"
      > </a
      ><a name="2141" href="Stlc.html#1756" class="Function Operator"
      >:=</a
      ><a name="2143"
      > </a
      ><a name="2144" href="Stlc.html#2123" class="Bound"
      >V</a
      ><a name="2145"
      > </a
      ><a name="2146" href="Stlc.html#1756" class="Function Operator"
      >]</a
      ><a name="2147" class="Symbol"
      >)</a
      ><a name="2148"
      > </a
      ><a name="2149" href="Stlc.html#1165" class="InductiveConstructor Operator"
      >then</a
      ><a name="2153"
      > </a
      ><a name="2154" class="Symbol"
      >(</a
      ><a name="2155" href="Stlc.html#2104" class="Bound"
      >M&#8242;</a
      ><a name="2157"
      > </a
      ><a name="2158" href="Stlc.html#1756" class="Function Operator"
      >[</a
      ><a name="2159"
      > </a
      ><a name="2160" href="Stlc.html#2118" class="Bound"
      >x</a
      ><a name="2161"
      > </a
      ><a name="2162" href="Stlc.html#1756" class="Function Operator"
      >:=</a
      ><a name="2164"
      > </a
      ><a name="2165" href="Stlc.html#2123" class="Bound"
      >V</a
      ><a name="2166"
      > </a
      ><a name="2167" href="Stlc.html#1756" class="Function Operator"
      >]</a
      ><a name="2168" class="Symbol"
      >)</a
      ><a name="2169"
      > </a
      ><a name="2170" href="Stlc.html#1165" class="InductiveConstructor Operator"
      >else</a
      ><a name="2174"
      > </a
      ><a name="2175" class="Symbol"
      >(</a
      ><a name="2176" href="Stlc.html#2112" class="Bound"
      >N&#8242;</a
      ><a name="2178"
      > </a
      ><a name="2179" href="Stlc.html#1756" class="Function Operator"
      >[</a
      ><a name="2180"
      > </a
      ><a name="2181" href="Stlc.html#2118" class="Bound"
      >x</a
      ><a name="2182"
      > </a
      ><a name="2183" href="Stlc.html#1756" class="Function Operator"
      >:=</a
      ><a name="2185"
      > </a
      ><a name="2186" href="Stlc.html#2123" class="Bound"
      >V</a
      ><a name="2187"
      > </a
      ><a name="2188" href="Stlc.html#1756" class="Function Operator"
      >]</a
      ><a name="2189" class="Symbol"
      >)</a
      >

</pre>

## Reduction rules

<pre class="Agda">

<a name="2236" class="Keyword"
      >data</a
      ><a name="2240"
      > </a
      ><a name="2241" href="Stlc.html#2241" class="Datatype Operator"
      >_&#10233;_</a
      ><a name="2244"
      > </a
      ><a name="2245" class="Symbol"
      >:</a
      ><a name="2246"
      > </a
      ><a name="2247" href="Stlc.html#1032" class="Datatype"
      >Term</a
      ><a name="2251"
      > </a
      ><a name="2252" class="Symbol"
      >&#8594;</a
      ><a name="2253"
      > </a
      ><a name="2254" href="Stlc.html#1032" class="Datatype"
      >Term</a
      ><a name="2258"
      > </a
      ><a name="2259" class="Symbol"
      >&#8594;</a
      ><a name="2260"
      > </a
      ><a name="2261" class="PrimitiveType"
      >Set</a
      ><a name="2264"
      > </a
      ><a name="2265" class="Keyword"
      >where</a
      ><a name="2270"
      >
  </a
      ><a name="2273" href="Stlc.html#2273" class="InductiveConstructor"
      >&#946;&#8658;</a
      ><a name="2275"
      > </a
      ><a name="2276" class="Symbol"
      >:</a
      ><a name="2277"
      > </a
      ><a name="2278" class="Symbol"
      >&#8704;</a
      ><a name="2279"
      > </a
      ><a name="2280" class="Symbol"
      >{</a
      ><a name="2281" href="Stlc.html#2281" class="Bound"
      >x</a
      ><a name="2282"
      > </a
      ><a name="2283" href="Stlc.html#2283" class="Bound"
      >A</a
      ><a name="2284"
      > </a
      ><a name="2285" href="Stlc.html#2285" class="Bound"
      >N</a
      ><a name="2286"
      > </a
      ><a name="2287" href="Stlc.html#2287" class="Bound"
      >V</a
      ><a name="2288" class="Symbol"
      >}</a
      ><a name="2289"
      > </a
      ><a name="2290" class="Symbol"
      >&#8594;</a
      ><a name="2291"
      > </a
      ><a name="2292" href="Stlc.html#1581" class="Datatype"
      >value</a
      ><a name="2297"
      > </a
      ><a name="2298" href="Stlc.html#2287" class="Bound"
      >V</a
      ><a name="2299"
      > </a
      ><a name="2300" class="Symbol"
      >&#8594;</a
      ><a name="2301"
      >
    </a
      ><a name="2306" class="Symbol"
      >((</a
      ><a name="2308" href="Stlc.html#1070" class="InductiveConstructor Operator"
      >&#955;&#7488;</a
      ><a name="2310"
      > </a
      ><a name="2311" href="Stlc.html#2281" class="Bound"
      >x</a
      ><a name="2312"
      > </a
      ><a name="2313" href="Stlc.html#1070" class="InductiveConstructor Operator"
      >&#8712;</a
      ><a name="2314"
      > </a
      ><a name="2315" href="Stlc.html#2283" class="Bound"
      >A</a
      ><a name="2316"
      > </a
      ><a name="2317" href="Stlc.html#1070" class="InductiveConstructor Operator"
      >&#8658;</a
      ><a name="2318"
      > </a
      ><a name="2319" href="Stlc.html#2285" class="Bound"
      >N</a
      ><a name="2320" class="Symbol"
      >)</a
      ><a name="2321"
      > </a
      ><a name="2322" href="Stlc.html#1106" class="InductiveConstructor Operator"
      >&#183;&#7488;</a
      ><a name="2324"
      > </a
      ><a name="2325" href="Stlc.html#2287" class="Bound"
      >V</a
      ><a name="2326" class="Symbol"
      >)</a
      ><a name="2327"
      > </a
      ><a name="2328" href="Stlc.html#2241" class="Datatype Operator"
      >&#10233;</a
      ><a name="2329"
      > </a
      ><a name="2330" class="Symbol"
      >(</a
      ><a name="2331" href="Stlc.html#2285" class="Bound"
      >N</a
      ><a name="2332"
      > </a
      ><a name="2333" href="Stlc.html#1756" class="Function Operator"
      >[</a
      ><a name="2334"
      > </a
      ><a name="2335" href="Stlc.html#2281" class="Bound"
      >x</a
      ><a name="2336"
      > </a
      ><a name="2337" href="Stlc.html#1756" class="Function Operator"
      >:=</a
      ><a name="2339"
      > </a
      ><a name="2340" href="Stlc.html#2287" class="Bound"
      >V</a
      ><a name="2341"
      > </a
      ><a name="2342" href="Stlc.html#1756" class="Function Operator"
      >]</a
      ><a name="2343" class="Symbol"
      >)</a
      ><a name="2344"
      >
  </a
      ><a name="2347" href="Stlc.html#2347" class="InductiveConstructor"
      >&#947;&#8658;&#8321;</a
      ><a name="2350"
      > </a
      ><a name="2351" class="Symbol"
      >:</a
      ><a name="2352"
      > </a
      ><a name="2353" class="Symbol"
      >&#8704;</a
      ><a name="2354"
      > </a
      ><a name="2355" class="Symbol"
      >{</a
      ><a name="2356" href="Stlc.html#2356" class="Bound"
      >L</a
      ><a name="2357"
      > </a
      ><a name="2358" href="Stlc.html#2358" class="Bound"
      >L'</a
      ><a name="2360"
      > </a
      ><a name="2361" href="Stlc.html#2361" class="Bound"
      >M</a
      ><a name="2362" class="Symbol"
      >}</a
      ><a name="2363"
      > </a
      ><a name="2364" class="Symbol"
      >&#8594;</a
      ><a name="2365"
      >
    </a
      ><a name="2370" href="Stlc.html#2356" class="Bound"
      >L</a
      ><a name="2371"
      > </a
      ><a name="2372" href="Stlc.html#2241" class="Datatype Operator"
      >&#10233;</a
      ><a name="2373"
      > </a
      ><a name="2374" href="Stlc.html#2358" class="Bound"
      >L'</a
      ><a name="2376"
      > </a
      ><a name="2377" class="Symbol"
      >&#8594;</a
      ><a name="2378"
      >
    </a
      ><a name="2383" class="Symbol"
      >(</a
      ><a name="2384" href="Stlc.html#2356" class="Bound"
      >L</a
      ><a name="2385"
      > </a
      ><a name="2386" href="Stlc.html#1106" class="InductiveConstructor Operator"
      >&#183;&#7488;</a
      ><a name="2388"
      > </a
      ><a name="2389" href="Stlc.html#2361" class="Bound"
      >M</a
      ><a name="2390" class="Symbol"
      >)</a
      ><a name="2391"
      > </a
      ><a name="2392" href="Stlc.html#2241" class="Datatype Operator"
      >&#10233;</a
      ><a name="2393"
      > </a
      ><a name="2394" class="Symbol"
      >(</a
      ><a name="2395" href="Stlc.html#2358" class="Bound"
      >L'</a
      ><a name="2397"
      > </a
      ><a name="2398" href="Stlc.html#1106" class="InductiveConstructor Operator"
      >&#183;&#7488;</a
      ><a name="2400"
      > </a
      ><a name="2401" href="Stlc.html#2361" class="Bound"
      >M</a
      ><a name="2402" class="Symbol"
      >)</a
      ><a name="2403"
      >
  </a
      ><a name="2406" href="Stlc.html#2406" class="InductiveConstructor"
      >&#947;&#8658;&#8322;</a
      ><a name="2409"
      > </a
      ><a name="2410" class="Symbol"
      >:</a
      ><a name="2411"
      > </a
      ><a name="2412" class="Symbol"
      >&#8704;</a
      ><a name="2413"
      > </a
      ><a name="2414" class="Symbol"
      >{</a
      ><a name="2415" href="Stlc.html#2415" class="Bound"
      >V</a
      ><a name="2416"
      > </a
      ><a name="2417" href="Stlc.html#2417" class="Bound"
      >M</a
      ><a name="2418"
      > </a
      ><a name="2419" href="Stlc.html#2419" class="Bound"
      >M'</a
      ><a name="2421" class="Symbol"
      >}</a
      ><a name="2422"
      > </a
      ><a name="2423" class="Symbol"
      >&#8594;</a
      ><a name="2424"
      >
    </a
      ><a name="2429" href="Stlc.html#1581" class="Datatype"
      >value</a
      ><a name="2434"
      > </a
      ><a name="2435" href="Stlc.html#2415" class="Bound"
      >V</a
      ><a name="2436"
      > </a
      ><a name="2437" class="Symbol"
      >&#8594;</a
      ><a name="2438"
      >
    </a
      ><a name="2443" href="Stlc.html#2417" class="Bound"
      >M</a
      ><a name="2444"
      > </a
      ><a name="2445" href="Stlc.html#2241" class="Datatype Operator"
      >&#10233;</a
      ><a name="2446"
      > </a
      ><a name="2447" href="Stlc.html#2419" class="Bound"
      >M'</a
      ><a name="2449"
      > </a
      ><a name="2450" class="Symbol"
      >&#8594;</a
      ><a name="2451"
      >
    </a
      ><a name="2456" class="Symbol"
      >(</a
      ><a name="2457" href="Stlc.html#2415" class="Bound"
      >V</a
      ><a name="2458"
      > </a
      ><a name="2459" href="Stlc.html#1106" class="InductiveConstructor Operator"
      >&#183;&#7488;</a
      ><a name="2461"
      > </a
      ><a name="2462" href="Stlc.html#2417" class="Bound"
      >M</a
      ><a name="2463" class="Symbol"
      >)</a
      ><a name="2464"
      > </a
      ><a name="2465" href="Stlc.html#2241" class="Datatype Operator"
      >&#10233;</a
      ><a name="2466"
      > </a
      ><a name="2467" class="Symbol"
      >(</a
      ><a name="2468" href="Stlc.html#2415" class="Bound"
      >V</a
      ><a name="2469"
      > </a
      ><a name="2470" href="Stlc.html#1106" class="InductiveConstructor Operator"
      >&#183;&#7488;</a
      ><a name="2472"
      > </a
      ><a name="2473" href="Stlc.html#2419" class="Bound"
      >M'</a
      ><a name="2475" class="Symbol"
      >)</a
      ><a name="2476"
      >
  </a
      ><a name="2479" href="Stlc.html#2479" class="InductiveConstructor"
      >&#946;&#120121;&#8321;</a
      ><a name="2482"
      > </a
      ><a name="2483" class="Symbol"
      >:</a
      ><a name="2484"
      > </a
      ><a name="2485" class="Symbol"
      >&#8704;</a
      ><a name="2486"
      > </a
      ><a name="2487" class="Symbol"
      >{</a
      ><a name="2488" href="Stlc.html#2488" class="Bound"
      >M</a
      ><a name="2489"
      > </a
      ><a name="2490" href="Stlc.html#2490" class="Bound"
      >N</a
      ><a name="2491" class="Symbol"
      >}</a
      ><a name="2492"
      > </a
      ><a name="2493" class="Symbol"
      >&#8594;</a
      ><a name="2494"
      >
    </a
      ><a name="2499" class="Symbol"
      >(</a
      ><a name="2500" href="Stlc.html#1165" class="InductiveConstructor Operator"
      >if&#7488;</a
      ><a name="2503"
      > </a
      ><a name="2504" href="Stlc.html#1134" class="InductiveConstructor"
      >true&#7488;</a
      ><a name="2509"
      > </a
      ><a name="2510" href="Stlc.html#1165" class="InductiveConstructor Operator"
      >then</a
      ><a name="2514"
      > </a
      ><a name="2515" href="Stlc.html#2488" class="Bound"
      >M</a
      ><a name="2516"
      > </a
      ><a name="2517" href="Stlc.html#1165" class="InductiveConstructor Operator"
      >else</a
      ><a name="2521"
      > </a
      ><a name="2522" href="Stlc.html#2490" class="Bound"
      >N</a
      ><a name="2523" class="Symbol"
      >)</a
      ><a name="2524"
      > </a
      ><a name="2525" href="Stlc.html#2241" class="Datatype Operator"
      >&#10233;</a
      ><a name="2526"
      > </a
      ><a name="2527" href="Stlc.html#2488" class="Bound"
      >M</a
      ><a name="2528"
      >
  </a
      ><a name="2531" href="Stlc.html#2531" class="InductiveConstructor"
      >&#946;&#120121;&#8322;</a
      ><a name="2534"
      > </a
      ><a name="2535" class="Symbol"
      >:</a
      ><a name="2536"
      > </a
      ><a name="2537" class="Symbol"
      >&#8704;</a
      ><a name="2538"
      > </a
      ><a name="2539" class="Symbol"
      >{</a
      ><a name="2540" href="Stlc.html#2540" class="Bound"
      >M</a
      ><a name="2541"
      > </a
      ><a name="2542" href="Stlc.html#2542" class="Bound"
      >N</a
      ><a name="2543" class="Symbol"
      >}</a
      ><a name="2544"
      > </a
      ><a name="2545" class="Symbol"
      >&#8594;</a
      ><a name="2546"
      >
    </a
      ><a name="2551" class="Symbol"
      >(</a
      ><a name="2552" href="Stlc.html#1165" class="InductiveConstructor Operator"
      >if&#7488;</a
      ><a name="2555"
      > </a
      ><a name="2556" href="Stlc.html#1149" class="InductiveConstructor"
      >false&#7488;</a
      ><a name="2562"
      > </a
      ><a name="2563" href="Stlc.html#1165" class="InductiveConstructor Operator"
      >then</a
      ><a name="2567"
      > </a
      ><a name="2568" href="Stlc.html#2540" class="Bound"
      >M</a
      ><a name="2569"
      > </a
      ><a name="2570" href="Stlc.html#1165" class="InductiveConstructor Operator"
      >else</a
      ><a name="2574"
      > </a
      ><a name="2575" href="Stlc.html#2542" class="Bound"
      >N</a
      ><a name="2576" class="Symbol"
      >)</a
      ><a name="2577"
      > </a
      ><a name="2578" href="Stlc.html#2241" class="Datatype Operator"
      >&#10233;</a
      ><a name="2579"
      > </a
      ><a name="2580" href="Stlc.html#2542" class="Bound"
      >N</a
      ><a name="2581"
      >
  </a
      ><a name="2584" href="Stlc.html#2584" class="InductiveConstructor"
      >&#947;&#120121;</a
      ><a name="2586"
      > </a
      ><a name="2587" class="Symbol"
      >:</a
      ><a name="2588"
      > </a
      ><a name="2589" class="Symbol"
      >&#8704;</a
      ><a name="2590"
      > </a
      ><a name="2591" class="Symbol"
      >{</a
      ><a name="2592" href="Stlc.html#2592" class="Bound"
      >L</a
      ><a name="2593"
      > </a
      ><a name="2594" href="Stlc.html#2594" class="Bound"
      >L'</a
      ><a name="2596"
      > </a
      ><a name="2597" href="Stlc.html#2597" class="Bound"
      >M</a
      ><a name="2598"
      > </a
      ><a name="2599" href="Stlc.html#2599" class="Bound"
      >N</a
      ><a name="2600" class="Symbol"
      >}</a
      ><a name="2601"
      > </a
      ><a name="2602" class="Symbol"
      >&#8594;</a
      ><a name="2603"
      >
    </a
      ><a name="2608" href="Stlc.html#2592" class="Bound"
      >L</a
      ><a name="2609"
      > </a
      ><a name="2610" href="Stlc.html#2241" class="Datatype Operator"
      >&#10233;</a
      ><a name="2611"
      > </a
      ><a name="2612" href="Stlc.html#2594" class="Bound"
      >L'</a
      ><a name="2614"
      > </a
      ><a name="2615" class="Symbol"
      >&#8594;</a
      ><a name="2616"
      >    
    </a
      ><a name="2625" class="Symbol"
      >(</a
      ><a name="2626" href="Stlc.html#1165" class="InductiveConstructor Operator"
      >if&#7488;</a
      ><a name="2629"
      > </a
      ><a name="2630" href="Stlc.html#2592" class="Bound"
      >L</a
      ><a name="2631"
      > </a
      ><a name="2632" href="Stlc.html#1165" class="InductiveConstructor Operator"
      >then</a
      ><a name="2636"
      > </a
      ><a name="2637" href="Stlc.html#2597" class="Bound"
      >M</a
      ><a name="2638"
      > </a
      ><a name="2639" href="Stlc.html#1165" class="InductiveConstructor Operator"
      >else</a
      ><a name="2643"
      > </a
      ><a name="2644" href="Stlc.html#2599" class="Bound"
      >N</a
      ><a name="2645" class="Symbol"
      >)</a
      ><a name="2646"
      > </a
      ><a name="2647" href="Stlc.html#2241" class="Datatype Operator"
      >&#10233;</a
      ><a name="2648"
      > </a
      ><a name="2649" class="Symbol"
      >(</a
      ><a name="2650" href="Stlc.html#1165" class="InductiveConstructor Operator"
      >if&#7488;</a
      ><a name="2653"
      > </a
      ><a name="2654" href="Stlc.html#2594" class="Bound"
      >L'</a
      ><a name="2656"
      > </a
      ><a name="2657" href="Stlc.html#1165" class="InductiveConstructor Operator"
      >then</a
      ><a name="2661"
      > </a
      ><a name="2662" href="Stlc.html#2597" class="Bound"
      >M</a
      ><a name="2663"
      > </a
      ><a name="2664" href="Stlc.html#1165" class="InductiveConstructor Operator"
      >else</a
      ><a name="2668"
      > </a
      ><a name="2669" href="Stlc.html#2599" class="Bound"
      >N</a
      ><a name="2670" class="Symbol"
      >)</a
      >

</pre>

## Reflexive and transitive closure of a relation

<pre class="Agda">

<a name="2748" href="Stlc.html#2748" class="Function"
      >Rel</a
      ><a name="2751"
      > </a
      ><a name="2752" class="Symbol"
      >:</a
      ><a name="2753"
      > </a
      ><a name="2754" class="PrimitiveType"
      >Set</a
      ><a name="2757"
      > </a
      ><a name="2758" class="Symbol"
      >&#8594;</a
      ><a name="2759"
      > </a
      ><a name="2760" class="PrimitiveType"
      >Set&#8321;</a
      ><a name="2764"
      >
</a
      ><a name="2765" href="Stlc.html#2748" class="Function"
      >Rel</a
      ><a name="2768"
      > </a
      ><a name="2769" href="Stlc.html#2769" class="Bound"
      >A</a
      ><a name="2770"
      > </a
      ><a name="2771" class="Symbol"
      >=</a
      ><a name="2772"
      > </a
      ><a name="2773" href="Stlc.html#2769" class="Bound"
      >A</a
      ><a name="2774"
      > </a
      ><a name="2775" class="Symbol"
      >&#8594;</a
      ><a name="2776"
      > </a
      ><a name="2777" href="Stlc.html#2769" class="Bound"
      >A</a
      ><a name="2778"
      > </a
      ><a name="2779" class="Symbol"
      >&#8594;</a
      ><a name="2780"
      > </a
      ><a name="2781" class="PrimitiveType"
      >Set</a
      ><a name="2784"
      >

</a
      ><a name="2786" class="Keyword"
      >infixl</a
      ><a name="2792"
      > </a
      ><a name="2793" class="Number"
      >100</a
      ><a name="2796"
      > </a
      ><a name="2797" href="Stlc.html#2918" class="InductiveConstructor Operator"
      >_&gt;&gt;_</a
      ><a name="2801"
      >

</a
      ><a name="2803" class="Keyword"
      >data</a
      ><a name="2807"
      > </a
      ><a name="2808" href="Stlc.html#2808" class="Datatype Operator"
      >_*</a
      ><a name="2810"
      > </a
      ><a name="2811" class="Symbol"
      >{</a
      ><a name="2812" href="Stlc.html#2812" class="Bound"
      >A</a
      ><a name="2813"
      > </a
      ><a name="2814" class="Symbol"
      >:</a
      ><a name="2815"
      > </a
      ><a name="2816" class="PrimitiveType"
      >Set</a
      ><a name="2819" class="Symbol"
      >}</a
      ><a name="2820"
      > </a
      ><a name="2821" class="Symbol"
      >(</a
      ><a name="2822" href="Stlc.html#2822" class="Bound"
      >R</a
      ><a name="2823"
      > </a
      ><a name="2824" class="Symbol"
      >:</a
      ><a name="2825"
      > </a
      ><a name="2826" href="Stlc.html#2748" class="Function"
      >Rel</a
      ><a name="2829"
      > </a
      ><a name="2830" href="Stlc.html#2812" class="Bound"
      >A</a
      ><a name="2831" class="Symbol"
      >)</a
      ><a name="2832"
      > </a
      ><a name="2833" class="Symbol"
      >:</a
      ><a name="2834"
      > </a
      ><a name="2835" href="Stlc.html#2748" class="Function"
      >Rel</a
      ><a name="2838"
      > </a
      ><a name="2839" href="Stlc.html#2812" class="Bound"
      >A</a
      ><a name="2840"
      > </a
      ><a name="2841" class="Keyword"
      >where</a
      ><a name="2846"
      >
  </a
      ><a name="2849" href="Stlc.html#2849" class="InductiveConstructor"
      >&#10216;&#10217;</a
      ><a name="2851"
      > </a
      ><a name="2852" class="Symbol"
      >:</a
      ><a name="2853"
      > </a
      ><a name="2854" class="Symbol"
      >&#8704;</a
      ><a name="2855"
      > </a
      ><a name="2856" class="Symbol"
      >{</a
      ><a name="2857" href="Stlc.html#2857" class="Bound"
      >x</a
      ><a name="2858"
      > </a
      ><a name="2859" class="Symbol"
      >:</a
      ><a name="2860"
      > </a
      ><a name="2861" href="Stlc.html#2812" class="Bound"
      >A</a
      ><a name="2862" class="Symbol"
      >}</a
      ><a name="2863"
      > </a
      ><a name="2864" class="Symbol"
      >&#8594;</a
      ><a name="2865"
      > </a
      ><a name="2866" class="Symbol"
      >(</a
      ><a name="2867" href="Stlc.html#2822" class="Bound"
      >R</a
      ><a name="2868"
      > </a
      ><a name="2869" href="Stlc.html#2808" class="Datatype Operator"
      >*</a
      ><a name="2870" class="Symbol"
      >)</a
      ><a name="2871"
      > </a
      ><a name="2872" href="Stlc.html#2857" class="Bound"
      >x</a
      ><a name="2873"
      > </a
      ><a name="2874" href="Stlc.html#2857" class="Bound"
      >x</a
      ><a name="2875"
      >
  </a
      ><a name="2878" href="Stlc.html#2878" class="InductiveConstructor Operator"
      >&#10216;_&#10217;</a
      ><a name="2881"
      > </a
      ><a name="2882" class="Symbol"
      >:</a
      ><a name="2883"
      > </a
      ><a name="2884" class="Symbol"
      >&#8704;</a
      ><a name="2885"
      > </a
      ><a name="2886" class="Symbol"
      >{</a
      ><a name="2887" href="Stlc.html#2887" class="Bound"
      >x</a
      ><a name="2888"
      > </a
      ><a name="2889" href="Stlc.html#2889" class="Bound"
      >y</a
      ><a name="2890"
      > </a
      ><a name="2891" class="Symbol"
      >:</a
      ><a name="2892"
      > </a
      ><a name="2893" href="Stlc.html#2812" class="Bound"
      >A</a
      ><a name="2894" class="Symbol"
      >}</a
      ><a name="2895"
      > </a
      ><a name="2896" class="Symbol"
      >&#8594;</a
      ><a name="2897"
      > </a
      ><a name="2898" href="Stlc.html#2822" class="Bound"
      >R</a
      ><a name="2899"
      > </a
      ><a name="2900" href="Stlc.html#2887" class="Bound"
      >x</a
      ><a name="2901"
      > </a
      ><a name="2902" href="Stlc.html#2889" class="Bound"
      >y</a
      ><a name="2903"
      > </a
      ><a name="2904" class="Symbol"
      >&#8594;</a
      ><a name="2905"
      > </a
      ><a name="2906" class="Symbol"
      >(</a
      ><a name="2907" href="Stlc.html#2822" class="Bound"
      >R</a
      ><a name="2908"
      > </a
      ><a name="2909" href="Stlc.html#2808" class="Datatype Operator"
      >*</a
      ><a name="2910" class="Symbol"
      >)</a
      ><a name="2911"
      > </a
      ><a name="2912" href="Stlc.html#2887" class="Bound"
      >x</a
      ><a name="2913"
      > </a
      ><a name="2914" href="Stlc.html#2889" class="Bound"
      >y</a
      ><a name="2915"
      >
  </a
      ><a name="2918" href="Stlc.html#2918" class="InductiveConstructor Operator"
      >_&gt;&gt;_</a
      ><a name="2922"
      > </a
      ><a name="2923" class="Symbol"
      >:</a
      ><a name="2924"
      > </a
      ><a name="2925" class="Symbol"
      >&#8704;</a
      ><a name="2926"
      > </a
      ><a name="2927" class="Symbol"
      >{</a
      ><a name="2928" href="Stlc.html#2928" class="Bound"
      >x</a
      ><a name="2929"
      > </a
      ><a name="2930" href="Stlc.html#2930" class="Bound"
      >y</a
      ><a name="2931"
      > </a
      ><a name="2932" href="Stlc.html#2932" class="Bound"
      >z</a
      ><a name="2933"
      > </a
      ><a name="2934" class="Symbol"
      >:</a
      ><a name="2935"
      > </a
      ><a name="2936" href="Stlc.html#2812" class="Bound"
      >A</a
      ><a name="2937" class="Symbol"
      >}</a
      ><a name="2938"
      > </a
      ><a name="2939" class="Symbol"
      >&#8594;</a
      ><a name="2940"
      > </a
      ><a name="2941" class="Symbol"
      >(</a
      ><a name="2942" href="Stlc.html#2822" class="Bound"
      >R</a
      ><a name="2943"
      > </a
      ><a name="2944" href="Stlc.html#2808" class="Datatype Operator"
      >*</a
      ><a name="2945" class="Symbol"
      >)</a
      ><a name="2946"
      > </a
      ><a name="2947" href="Stlc.html#2928" class="Bound"
      >x</a
      ><a name="2948"
      > </a
      ><a name="2949" href="Stlc.html#2930" class="Bound"
      >y</a
      ><a name="2950"
      > </a
      ><a name="2951" class="Symbol"
      >&#8594;</a
      ><a name="2952"
      > </a
      ><a name="2953" class="Symbol"
      >(</a
      ><a name="2954" href="Stlc.html#2822" class="Bound"
      >R</a
      ><a name="2955"
      > </a
      ><a name="2956" href="Stlc.html#2808" class="Datatype Operator"
      >*</a
      ><a name="2957" class="Symbol"
      >)</a
      ><a name="2958"
      > </a
      ><a name="2959" href="Stlc.html#2930" class="Bound"
      >y</a
      ><a name="2960"
      > </a
      ><a name="2961" href="Stlc.html#2932" class="Bound"
      >z</a
      ><a name="2962"
      > </a
      ><a name="2963" class="Symbol"
      >&#8594;</a
      ><a name="2964"
      > </a
      ><a name="2965" class="Symbol"
      >(</a
      ><a name="2966" href="Stlc.html#2822" class="Bound"
      >R</a
      ><a name="2967"
      > </a
      ><a name="2968" href="Stlc.html#2808" class="Datatype Operator"
      >*</a
      ><a name="2969" class="Symbol"
      >)</a
      ><a name="2970"
      > </a
      ><a name="2971" href="Stlc.html#2928" class="Bound"
      >x</a
      ><a name="2972"
      > </a
      ><a name="2973" href="Stlc.html#2932" class="Bound"
      >z</a
      >

</pre>

<pre class="Agda">

<a name="3000" href="Stlc.html#3000" class="Function Operator"
      >_&#10233;*_</a
      ><a name="3004"
      > </a
      ><a name="3005" class="Symbol"
      >:</a
      ><a name="3006"
      > </a
      ><a name="3007" href="Stlc.html#1032" class="Datatype"
      >Term</a
      ><a name="3011"
      > </a
      ><a name="3012" class="Symbol"
      >&#8594;</a
      ><a name="3013"
      > </a
      ><a name="3014" href="Stlc.html#1032" class="Datatype"
      >Term</a
      ><a name="3018"
      > </a
      ><a name="3019" class="Symbol"
      >&#8594;</a
      ><a name="3020"
      > </a
      ><a name="3021" class="PrimitiveType"
      >Set</a
      ><a name="3024"
      >
</a
      ><a name="3025" href="Stlc.html#3000" class="Function Operator"
      >_&#10233;*_</a
      ><a name="3029"
      > </a
      ><a name="3030" class="Symbol"
      >=</a
      ><a name="3031"
      > </a
      ><a name="3032" class="Symbol"
      >(</a
      ><a name="3033" href="Stlc.html#2241" class="Datatype Operator"
      >_&#10233;_</a
      ><a name="3036" class="Symbol"
      >)</a
      ><a name="3037"
      > </a
      ><a name="3038" href="Stlc.html#2808" class="Datatype Operator"
      >*</a
      >

</pre>

Example evaluation.

<pre class="Agda">

<a name="3086" href="Stlc.html#3086" class="Function"
      >example&#8320;</a
      ><a name="3094"
      > </a
      ><a name="3095" class="Symbol"
      >:</a
      ><a name="3096"
      > </a
      ><a name="3097" class="Symbol"
      >(</a
      ><a name="3098" href="Stlc.html#1319" class="Function"
      >not[&#120121;]</a
      ><a name="3104"
      > </a
      ><a name="3105" href="Stlc.html#1106" class="InductiveConstructor Operator"
      >&#183;&#7488;</a
      ><a name="3107"
      > </a
      ><a name="3108" href="Stlc.html#1134" class="InductiveConstructor"
      >true&#7488;</a
      ><a name="3113" class="Symbol"
      >)</a
      ><a name="3114"
      > </a
      ><a name="3115" href="Stlc.html#3000" class="Function Operator"
      >&#10233;*</a
      ><a name="3117"
      > </a
      ><a name="3118" href="Stlc.html#1149" class="InductiveConstructor"
      >false&#7488;</a
      ><a name="3124"
      >
</a
      ><a name="3125" href="Stlc.html#3086" class="Function"
      >example&#8320;</a
      ><a name="3133"
      > </a
      ><a name="3134" class="Symbol"
      >=</a
      ><a name="3135"
      > </a
      ><a name="3136" href="Stlc.html#2878" class="InductiveConstructor Operator"
      >&#10216;</a
      ><a name="3137"
      > </a
      ><a name="3138" href="Stlc.html#3268" class="Function"
      >step&#8320;</a
      ><a name="3143"
      > </a
      ><a name="3144" href="Stlc.html#2878" class="InductiveConstructor Operator"
      >&#10217;</a
      ><a name="3145"
      > </a
      ><a name="3146" href="Stlc.html#2918" class="InductiveConstructor Operator"
      >&gt;&gt;</a
      ><a name="3148"
      > </a
      ><a name="3149" href="Stlc.html#2878" class="InductiveConstructor Operator"
      >&#10216;</a
      ><a name="3150"
      > </a
      ><a name="3151" href="Stlc.html#3311" class="Function"
      >step&#8321;</a
      ><a name="3156"
      > </a
      ><a name="3157" href="Stlc.html#2878" class="InductiveConstructor Operator"
      >&#10217;</a
      ><a name="3158"
      >
  </a
      ><a name="3161" class="Keyword"
      >where</a
      ><a name="3166"
      >
  </a
      ><a name="3169" href="Stlc.html#3169" class="Function"
      >M&#8320;</a
      ><a name="3171"
      > </a
      ><a name="3172" href="Stlc.html#3172" class="Function"
      >M&#8321;</a
      ><a name="3174"
      > </a
      ><a name="3175" href="Stlc.html#3175" class="Function"
      >M&#8322;</a
      ><a name="3177"
      > </a
      ><a name="3178" class="Symbol"
      >:</a
      ><a name="3179"
      > </a
      ><a name="3180" href="Stlc.html#1032" class="Datatype"
      >Term</a
      ><a name="3184"
      >
  </a
      ><a name="3187" href="Stlc.html#3169" class="Function"
      >M&#8320;</a
      ><a name="3189"
      > </a
      ><a name="3190" class="Symbol"
      >=</a
      ><a name="3191"
      > </a
      ><a name="3192" class="Symbol"
      >(</a
      ><a name="3193" href="Stlc.html#1319" class="Function"
      >not[&#120121;]</a
      ><a name="3199"
      > </a
      ><a name="3200" href="Stlc.html#1106" class="InductiveConstructor Operator"
      >&#183;&#7488;</a
      ><a name="3202"
      > </a
      ><a name="3203" href="Stlc.html#1134" class="InductiveConstructor"
      >true&#7488;</a
      ><a name="3208" class="Symbol"
      >)</a
      ><a name="3209"
      >
  </a
      ><a name="3212" href="Stlc.html#3172" class="Function"
      >M&#8321;</a
      ><a name="3214"
      > </a
      ><a name="3215" class="Symbol"
      >=</a
      ><a name="3216"
      > </a
      ><a name="3217" class="Symbol"
      >(</a
      ><a name="3218" href="Stlc.html#1165" class="InductiveConstructor Operator"
      >if&#7488;</a
      ><a name="3221"
      > </a
      ><a name="3222" href="Stlc.html#1134" class="InductiveConstructor"
      >true&#7488;</a
      ><a name="3227"
      > </a
      ><a name="3228" href="Stlc.html#1165" class="InductiveConstructor Operator"
      >then</a
      ><a name="3232"
      > </a
      ><a name="3233" href="Stlc.html#1149" class="InductiveConstructor"
      >false&#7488;</a
      ><a name="3239"
      > </a
      ><a name="3240" href="Stlc.html#1165" class="InductiveConstructor Operator"
      >else</a
      ><a name="3244"
      > </a
      ><a name="3245" href="Stlc.html#1134" class="InductiveConstructor"
      >true&#7488;</a
      ><a name="3250" class="Symbol"
      >)</a
      ><a name="3251"
      >
  </a
      ><a name="3254" href="Stlc.html#3175" class="Function"
      >M&#8322;</a
      ><a name="3256"
      > </a
      ><a name="3257" class="Symbol"
      >=</a
      ><a name="3258"
      > </a
      ><a name="3259" href="Stlc.html#1149" class="InductiveConstructor"
      >false&#7488;</a
      ><a name="3265"
      >
  </a
      ><a name="3268" href="Stlc.html#3268" class="Function"
      >step&#8320;</a
      ><a name="3273"
      > </a
      ><a name="3274" class="Symbol"
      >:</a
      ><a name="3275"
      > </a
      ><a name="3276" href="Stlc.html#3169" class="Function"
      >M&#8320;</a
      ><a name="3278"
      > </a
      ><a name="3279" href="Stlc.html#2241" class="Datatype Operator"
      >&#10233;</a
      ><a name="3280"
      > </a
      ><a name="3281" href="Stlc.html#3172" class="Function"
      >M&#8321;</a
      ><a name="3283"
      >
  </a
      ><a name="3286" href="Stlc.html#3268" class="Function"
      >step&#8320;</a
      ><a name="3291"
      > </a
      ><a name="3292" class="Symbol"
      >=</a
      ><a name="3293"
      > </a
      ><a name="3294" href="Stlc.html#2273" class="InductiveConstructor"
      >&#946;&#8658;</a
      ><a name="3296"
      > </a
      ><a name="3297" href="Stlc.html#1654" class="InductiveConstructor"
      >value-true&#7488;</a
      ><a name="3308"
      >
  </a
      ><a name="3311" href="Stlc.html#3311" class="Function"
      >step&#8321;</a
      ><a name="3316"
      > </a
      ><a name="3317" class="Symbol"
      >:</a
      ><a name="3318"
      > </a
      ><a name="3319" href="Stlc.html#3172" class="Function"
      >M&#8321;</a
      ><a name="3321"
      > </a
      ><a name="3322" href="Stlc.html#2241" class="Datatype Operator"
      >&#10233;</a
      ><a name="3323"
      > </a
      ><a name="3324" href="Stlc.html#3175" class="Function"
      >M&#8322;</a
      ><a name="3326"
      >
  </a
      ><a name="3329" href="Stlc.html#3311" class="Function"
      >step&#8321;</a
      ><a name="3334"
      > </a
      ><a name="3335" class="Symbol"
      >=</a
      ><a name="3336"
      > </a
      ><a name="3337" href="Stlc.html#2479" class="InductiveConstructor"
      >&#946;&#120121;&#8321;</a
      ><a name="3340"
      >

</a
      ><a name="3342" href="Stlc.html#3342" class="Function"
      >example&#8321;</a
      ><a name="3350"
      > </a
      ><a name="3351" class="Symbol"
      >:</a
      ><a name="3352"
      > </a
      ><a name="3353" class="Symbol"
      >(</a
      ><a name="3354" href="Stlc.html#1304" class="Function"
      >I[&#120121;&#8658;&#120121;]</a
      ><a name="3360"
      > </a
      ><a name="3361" href="Stlc.html#1106" class="InductiveConstructor Operator"
      >&#183;&#7488;</a
      ><a name="3363"
      > </a
      ><a name="3364" href="Stlc.html#1299" class="Function"
      >I[&#120121;]</a
      ><a name="3368"
      > </a
      ><a name="3369" href="Stlc.html#1106" class="InductiveConstructor Operator"
      >&#183;&#7488;</a
      ><a name="3371"
      > </a
      ><a name="3372" class="Symbol"
      >(</a
      ><a name="3373" href="Stlc.html#1319" class="Function"
      >not[&#120121;]</a
      ><a name="3379"
      > </a
      ><a name="3380" href="Stlc.html#1106" class="InductiveConstructor Operator"
      >&#183;&#7488;</a
      ><a name="3382"
      > </a
      ><a name="3383" href="Stlc.html#1149" class="InductiveConstructor"
      >false&#7488;</a
      ><a name="3389" class="Symbol"
      >))</a
      ><a name="3391"
      > </a
      ><a name="3392" href="Stlc.html#3000" class="Function Operator"
      >&#10233;*</a
      ><a name="3394"
      > </a
      ><a name="3395" href="Stlc.html#1134" class="InductiveConstructor"
      >true&#7488;</a
      ><a name="3400"
      >
</a
      ><a name="3401" href="Stlc.html#3342" class="Function"
      >example&#8321;</a
      ><a name="3409"
      > </a
      ><a name="3410" class="Symbol"
      >=</a
      ><a name="3411"
      > </a
      ><a name="3412" href="Stlc.html#2878" class="InductiveConstructor Operator"
      >&#10216;</a
      ><a name="3413"
      > </a
      ><a name="3414" href="Stlc.html#3778" class="Function"
      >step&#8320;</a
      ><a name="3419"
      > </a
      ><a name="3420" href="Stlc.html#2878" class="InductiveConstructor Operator"
      >&#10217;</a
      ><a name="3421"
      > </a
      ><a name="3422" href="Stlc.html#2918" class="InductiveConstructor Operator"
      >&gt;&gt;</a
      ><a name="3424"
      > </a
      ><a name="3425" href="Stlc.html#2878" class="InductiveConstructor Operator"
      >&#10216;</a
      ><a name="3426"
      > </a
      ><a name="3427" href="Stlc.html#3824" class="Function"
      >step&#8321;</a
      ><a name="3432"
      > </a
      ><a name="3433" href="Stlc.html#2878" class="InductiveConstructor Operator"
      >&#10217;</a
      ><a name="3434"
      > </a
      ><a name="3435" href="Stlc.html#2918" class="InductiveConstructor Operator"
      >&gt;&gt;</a
      ><a name="3437"
      > </a
      ><a name="3438" href="Stlc.html#2878" class="InductiveConstructor Operator"
      >&#10216;</a
      ><a name="3439"
      > </a
      ><a name="3440" href="Stlc.html#3883" class="Function"
      >step&#8322;</a
      ><a name="3445"
      > </a
      ><a name="3446" href="Stlc.html#2878" class="InductiveConstructor Operator"
      >&#10217;</a
      ><a name="3447"
      > </a
      ><a name="3448" href="Stlc.html#2918" class="InductiveConstructor Operator"
      >&gt;&gt;</a
      ><a name="3450"
      > </a
      ><a name="3451" href="Stlc.html#2878" class="InductiveConstructor Operator"
      >&#10216;</a
      ><a name="3452"
      > </a
      ><a name="3453" href="Stlc.html#3928" class="Function"
      >step&#8323;</a
      ><a name="3458"
      > </a
      ><a name="3459" href="Stlc.html#2878" class="InductiveConstructor Operator"
      >&#10217;</a
      ><a name="3460"
      > </a
      ><a name="3461" href="Stlc.html#2918" class="InductiveConstructor Operator"
      >&gt;&gt;</a
      ><a name="3463"
      > </a
      ><a name="3464" href="Stlc.html#2878" class="InductiveConstructor Operator"
      >&#10216;</a
      ><a name="3465"
      > </a
      ><a name="3466" href="Stlc.html#3980" class="Function"
      >step&#8324;</a
      ><a name="3471"
      > </a
      ><a name="3472" href="Stlc.html#2878" class="InductiveConstructor Operator"
      >&#10217;</a
      ><a name="3473"
      >
  </a
      ><a name="3476" class="Keyword"
      >where</a
      ><a name="3481"
      >
  </a
      ><a name="3484" href="Stlc.html#3484" class="Function"
      >M&#8320;</a
      ><a name="3486"
      > </a
      ><a name="3487" href="Stlc.html#3487" class="Function"
      >M&#8321;</a
      ><a name="3489"
      > </a
      ><a name="3490" href="Stlc.html#3490" class="Function"
      >M&#8322;</a
      ><a name="3492"
      > </a
      ><a name="3493" href="Stlc.html#3493" class="Function"
      >M&#8323;</a
      ><a name="3495"
      > </a
      ><a name="3496" href="Stlc.html#3496" class="Function"
      >M&#8324;</a
      ><a name="3498"
      > </a
      ><a name="3499" href="Stlc.html#3499" class="Function"
      >M&#8325;</a
      ><a name="3501"
      > </a
      ><a name="3502" class="Symbol"
      >:</a
      ><a name="3503"
      > </a
      ><a name="3504" href="Stlc.html#1032" class="Datatype"
      >Term</a
      ><a name="3508"
      >
  </a
      ><a name="3511" href="Stlc.html#3484" class="Function"
      >M&#8320;</a
      ><a name="3513"
      > </a
      ><a name="3514" class="Symbol"
      >=</a
      ><a name="3515"
      > </a
      ><a name="3516" class="Symbol"
      >(</a
      ><a name="3517" href="Stlc.html#1304" class="Function"
      >I[&#120121;&#8658;&#120121;]</a
      ><a name="3523"
      > </a
      ><a name="3524" href="Stlc.html#1106" class="InductiveConstructor Operator"
      >&#183;&#7488;</a
      ><a name="3526"
      > </a
      ><a name="3527" href="Stlc.html#1299" class="Function"
      >I[&#120121;]</a
      ><a name="3531"
      > </a
      ><a name="3532" href="Stlc.html#1106" class="InductiveConstructor Operator"
      >&#183;&#7488;</a
      ><a name="3534"
      > </a
      ><a name="3535" class="Symbol"
      >(</a
      ><a name="3536" href="Stlc.html#1319" class="Function"
      >not[&#120121;]</a
      ><a name="3542"
      > </a
      ><a name="3543" href="Stlc.html#1106" class="InductiveConstructor Operator"
      >&#183;&#7488;</a
      ><a name="3545"
      > </a
      ><a name="3546" href="Stlc.html#1149" class="InductiveConstructor"
      >false&#7488;</a
      ><a name="3552" class="Symbol"
      >))</a
      ><a name="3554"
      >
  </a
      ><a name="3557" href="Stlc.html#3487" class="Function"
      >M&#8321;</a
      ><a name="3559"
      > </a
      ><a name="3560" class="Symbol"
      >=</a
      ><a name="3561"
      > </a
      ><a name="3562" class="Symbol"
      >((</a
      ><a name="3564" href="Stlc.html#1070" class="InductiveConstructor Operator"
      >&#955;&#7488;</a
      ><a name="3566"
      > </a
      ><a name="3567" href="Stlc.html#1250" class="Function"
      >x</a
      ><a name="3568"
      > </a
      ><a name="3569" href="Stlc.html#1070" class="InductiveConstructor Operator"
      >&#8712;</a
      ><a name="3570"
      > </a
      ><a name="3571" href="Stlc.html#990" class="InductiveConstructor"
      >&#120121;</a
      ><a name="3572"
      > </a
      ><a name="3573" href="Stlc.html#1070" class="InductiveConstructor Operator"
      >&#8658;</a
      ><a name="3574"
      > </a
      ><a name="3575" class="Symbol"
      >(</a
      ><a name="3576" href="Stlc.html#1299" class="Function"
      >I[&#120121;]</a
      ><a name="3580"
      > </a
      ><a name="3581" href="Stlc.html#1106" class="InductiveConstructor Operator"
      >&#183;&#7488;</a
      ><a name="3583"
      > </a
      ><a name="3584" href="Stlc.html#1051" class="InductiveConstructor"
      >var&#7488;</a
      ><a name="3588"
      > </a
      ><a name="3589" href="Stlc.html#1250" class="Function"
      >x</a
      ><a name="3590" class="Symbol"
      >))</a
      ><a name="3592"
      > </a
      ><a name="3593" href="Stlc.html#1106" class="InductiveConstructor Operator"
      >&#183;&#7488;</a
      ><a name="3595"
      > </a
      ><a name="3596" class="Symbol"
      >(</a
      ><a name="3597" href="Stlc.html#1319" class="Function"
      >not[&#120121;]</a
      ><a name="3603"
      > </a
      ><a name="3604" href="Stlc.html#1106" class="InductiveConstructor Operator"
      >&#183;&#7488;</a
      ><a name="3606"
      > </a
      ><a name="3607" href="Stlc.html#1149" class="InductiveConstructor"
      >false&#7488;</a
      ><a name="3613" class="Symbol"
      >))</a
      ><a name="3615"
      >
  </a
      ><a name="3618" href="Stlc.html#3490" class="Function"
      >M&#8322;</a
      ><a name="3620"
      > </a
      ><a name="3621" class="Symbol"
      >=</a
      ><a name="3622"
      > </a
      ><a name="3623" class="Symbol"
      >((</a
      ><a name="3625" href="Stlc.html#1070" class="InductiveConstructor Operator"
      >&#955;&#7488;</a
      ><a name="3627"
      > </a
      ><a name="3628" href="Stlc.html#1250" class="Function"
      >x</a
      ><a name="3629"
      > </a
      ><a name="3630" href="Stlc.html#1070" class="InductiveConstructor Operator"
      >&#8712;</a
      ><a name="3631"
      > </a
      ><a name="3632" href="Stlc.html#990" class="InductiveConstructor"
      >&#120121;</a
      ><a name="3633"
      > </a
      ><a name="3634" href="Stlc.html#1070" class="InductiveConstructor Operator"
      >&#8658;</a
      ><a name="3635"
      > </a
      ><a name="3636" class="Symbol"
      >(</a
      ><a name="3637" href="Stlc.html#1299" class="Function"
      >I[&#120121;]</a
      ><a name="3641"
      > </a
      ><a name="3642" href="Stlc.html#1106" class="InductiveConstructor Operator"
      >&#183;&#7488;</a
      ><a name="3644"
      > </a
      ><a name="3645" href="Stlc.html#1051" class="InductiveConstructor"
      >var&#7488;</a
      ><a name="3649"
      > </a
      ><a name="3650" href="Stlc.html#1250" class="Function"
      >x</a
      ><a name="3651" class="Symbol"
      >))</a
      ><a name="3653"
      > </a
      ><a name="3654" href="Stlc.html#1106" class="InductiveConstructor Operator"
      >&#183;&#7488;</a
      ><a name="3656"
      > </a
      ><a name="3657" class="Symbol"
      >(</a
      ><a name="3658" href="Stlc.html#1165" class="InductiveConstructor Operator"
      >if&#7488;</a
      ><a name="3661"
      > </a
      ><a name="3662" href="Stlc.html#1149" class="InductiveConstructor"
      >false&#7488;</a
      ><a name="3668"
      > </a
      ><a name="3669" href="Stlc.html#1165" class="InductiveConstructor Operator"
      >then</a
      ><a name="3673"
      > </a
      ><a name="3674" href="Stlc.html#1149" class="InductiveConstructor"
      >false&#7488;</a
      ><a name="3680"
      > </a
      ><a name="3681" href="Stlc.html#1165" class="InductiveConstructor Operator"
      >else</a
      ><a name="3685"
      > </a
      ><a name="3686" href="Stlc.html#1134" class="InductiveConstructor"
      >true&#7488;</a
      ><a name="3691" class="Symbol"
      >))</a
      ><a name="3693"
      >
  </a
      ><a name="3696" href="Stlc.html#3493" class="Function"
      >M&#8323;</a
      ><a name="3698"
      > </a
      ><a name="3699" class="Symbol"
      >=</a
      ><a name="3700"
      > </a
      ><a name="3701" class="Symbol"
      >((</a
      ><a name="3703" href="Stlc.html#1070" class="InductiveConstructor Operator"
      >&#955;&#7488;</a
      ><a name="3705"
      > </a
      ><a name="3706" href="Stlc.html#1250" class="Function"
      >x</a
      ><a name="3707"
      > </a
      ><a name="3708" href="Stlc.html#1070" class="InductiveConstructor Operator"
      >&#8712;</a
      ><a name="3709"
      > </a
      ><a name="3710" href="Stlc.html#990" class="InductiveConstructor"
      >&#120121;</a
      ><a name="3711"
      > </a
      ><a name="3712" href="Stlc.html#1070" class="InductiveConstructor Operator"
      >&#8658;</a
      ><a name="3713"
      > </a
      ><a name="3714" class="Symbol"
      >(</a
      ><a name="3715" href="Stlc.html#1299" class="Function"
      >I[&#120121;]</a
      ><a name="3719"
      > </a
      ><a name="3720" href="Stlc.html#1106" class="InductiveConstructor Operator"
      >&#183;&#7488;</a
      ><a name="3722"
      > </a
      ><a name="3723" href="Stlc.html#1051" class="InductiveConstructor"
      >var&#7488;</a
      ><a name="3727"
      > </a
      ><a name="3728" href="Stlc.html#1250" class="Function"
      >x</a
      ><a name="3729" class="Symbol"
      >))</a
      ><a name="3731"
      > </a
      ><a name="3732" href="Stlc.html#1106" class="InductiveConstructor Operator"
      >&#183;&#7488;</a
      ><a name="3734"
      > </a
      ><a name="3735" href="Stlc.html#1134" class="InductiveConstructor"
      >true&#7488;</a
      ><a name="3740" class="Symbol"
      >)</a
      ><a name="3741"
      >
  </a
      ><a name="3744" href="Stlc.html#3496" class="Function"
      >M&#8324;</a
      ><a name="3746"
      > </a
      ><a name="3747" class="Symbol"
      >=</a
      ><a name="3748"
      > </a
      ><a name="3749" href="Stlc.html#1299" class="Function"
      >I[&#120121;]</a
      ><a name="3753"
      > </a
      ><a name="3754" href="Stlc.html#1106" class="InductiveConstructor Operator"
      >&#183;&#7488;</a
      ><a name="3756"
      > </a
      ><a name="3757" href="Stlc.html#1134" class="InductiveConstructor"
      >true&#7488;</a
      ><a name="3762"
      >
  </a
      ><a name="3765" href="Stlc.html#3499" class="Function"
      >M&#8325;</a
      ><a name="3767"
      > </a
      ><a name="3768" class="Symbol"
      >=</a
      ><a name="3769"
      > </a
      ><a name="3770" href="Stlc.html#1134" class="InductiveConstructor"
      >true&#7488;</a
      ><a name="3775"
      >
  </a
      ><a name="3778" href="Stlc.html#3778" class="Function"
      >step&#8320;</a
      ><a name="3783"
      > </a
      ><a name="3784" class="Symbol"
      >:</a
      ><a name="3785"
      > </a
      ><a name="3786" href="Stlc.html#3484" class="Function"
      >M&#8320;</a
      ><a name="3788"
      > </a
      ><a name="3789" href="Stlc.html#2241" class="Datatype Operator"
      >&#10233;</a
      ><a name="3790"
      > </a
      ><a name="3791" href="Stlc.html#3487" class="Function"
      >M&#8321;</a
      ><a name="3793"
      >
  </a
      ><a name="3796" href="Stlc.html#3778" class="Function"
      >step&#8320;</a
      ><a name="3801"
      > </a
      ><a name="3802" class="Symbol"
      >=</a
      ><a name="3803"
      > </a
      ><a name="3804" href="Stlc.html#2347" class="InductiveConstructor"
      >&#947;&#8658;&#8321;</a
      ><a name="3807"
      > </a
      ><a name="3808" class="Symbol"
      >(</a
      ><a name="3809" href="Stlc.html#2273" class="InductiveConstructor"
      >&#946;&#8658;</a
      ><a name="3811"
      > </a
      ><a name="3812" href="Stlc.html#1608" class="InductiveConstructor"
      >value-&#955;&#7488;</a
      ><a name="3820" class="Symbol"
      >)</a
      ><a name="3821"
      >
  </a
      ><a name="3824" href="Stlc.html#3824" class="Function"
      >step&#8321;</a
      ><a name="3829"
      > </a
      ><a name="3830" class="Symbol"
      >:</a
      ><a name="3831"
      > </a
      ><a name="3832" href="Stlc.html#3487" class="Function"
      >M&#8321;</a
      ><a name="3834"
      > </a
      ><a name="3835" href="Stlc.html#2241" class="Datatype Operator"
      >&#10233;</a
      ><a name="3836"
      > </a
      ><a name="3837" href="Stlc.html#3490" class="Function"
      >M&#8322;</a
      ><a name="3839"
      >
  </a
      ><a name="3842" href="Stlc.html#3824" class="Function"
      >step&#8321;</a
      ><a name="3847"
      > </a
      ><a name="3848" class="Symbol"
      >=</a
      ><a name="3849"
      > </a
      ><a name="3850" href="Stlc.html#2406" class="InductiveConstructor"
      >&#947;&#8658;&#8322;</a
      ><a name="3853"
      > </a
      ><a name="3854" href="Stlc.html#1608" class="InductiveConstructor"
      >value-&#955;&#7488;</a
      ><a name="3862"
      > </a
      ><a name="3863" class="Symbol"
      >(</a
      ><a name="3864" href="Stlc.html#2273" class="InductiveConstructor"
      >&#946;&#8658;</a
      ><a name="3866"
      > </a
      ><a name="3867" href="Stlc.html#1684" class="InductiveConstructor"
      >value-false&#7488;</a
      ><a name="3879" class="Symbol"
      >)</a
      ><a name="3880"
      >
  </a
      ><a name="3883" href="Stlc.html#3883" class="Function"
      >step&#8322;</a
      ><a name="3888"
      > </a
      ><a name="3889" class="Symbol"
      >:</a
      ><a name="3890"
      > </a
      ><a name="3891" href="Stlc.html#3490" class="Function"
      >M&#8322;</a
      ><a name="3893"
      > </a
      ><a name="3894" href="Stlc.html#2241" class="Datatype Operator"
      >&#10233;</a
      ><a name="3895"
      > </a
      ><a name="3896" href="Stlc.html#3493" class="Function"
      >M&#8323;</a
      ><a name="3898"
      >
  </a
      ><a name="3901" href="Stlc.html#3883" class="Function"
      >step&#8322;</a
      ><a name="3906"
      > </a
      ><a name="3907" class="Symbol"
      >=</a
      ><a name="3908"
      > </a
      ><a name="3909" href="Stlc.html#2406" class="InductiveConstructor"
      >&#947;&#8658;&#8322;</a
      ><a name="3912"
      > </a
      ><a name="3913" href="Stlc.html#1608" class="InductiveConstructor"
      >value-&#955;&#7488;</a
      ><a name="3921"
      > </a
      ><a name="3922" href="Stlc.html#2531" class="InductiveConstructor"
      >&#946;&#120121;&#8322;</a
      ><a name="3925"
      >
  </a
      ><a name="3928" href="Stlc.html#3928" class="Function"
      >step&#8323;</a
      ><a name="3933"
      > </a
      ><a name="3934" class="Symbol"
      >:</a
      ><a name="3935"
      > </a
      ><a name="3936" href="Stlc.html#3493" class="Function"
      >M&#8323;</a
      ><a name="3938"
      > </a
      ><a name="3939" href="Stlc.html#2241" class="Datatype Operator"
      >&#10233;</a
      ><a name="3940"
      > </a
      ><a name="3941" href="Stlc.html#3496" class="Function"
      >M&#8324;</a
      ><a name="3943"
      >
  </a
      ><a name="3946" href="Stlc.html#3928" class="Function"
      >step&#8323;</a
      ><a name="3951"
      > </a
      ><a name="3952" class="Symbol"
      >=</a
      ><a name="3953"
      > </a
      ><a name="3954" href="Stlc.html#2273" class="InductiveConstructor"
      >&#946;&#8658;</a
      ><a name="3956"
      > </a
      ><a name="3957" href="Stlc.html#1654" class="InductiveConstructor"
      >value-true&#7488;</a
      ><a name="3968"
      >         
  </a
      ><a name="3980" href="Stlc.html#3980" class="Function"
      >step&#8324;</a
      ><a name="3985"
      > </a
      ><a name="3986" class="Symbol"
      >:</a
      ><a name="3987"
      > </a
      ><a name="3988" href="Stlc.html#3496" class="Function"
      >M&#8324;</a
      ><a name="3990"
      > </a
      ><a name="3991" href="Stlc.html#2241" class="Datatype Operator"
      >&#10233;</a
      ><a name="3992"
      > </a
      ><a name="3993" href="Stlc.html#3499" class="Function"
      >M&#8325;</a
      ><a name="3995"
      >
  </a
      ><a name="3998" href="Stlc.html#3980" class="Function"
      >step&#8324;</a
      ><a name="4003"
      > </a
      ><a name="4004" class="Symbol"
      >=</a
      ><a name="4005"
      > </a
      ><a name="4006" href="Stlc.html#2273" class="InductiveConstructor"
      >&#946;&#8658;</a
      ><a name="4008"
      > </a
      ><a name="4009" href="Stlc.html#1654" class="InductiveConstructor"
      >value-true&#7488;</a
      >

</pre>

## Type rules

<pre class="Agda">

<a name="4070" href="Stlc.html#4070" class="Function"
      >Context</a
      ><a name="4077"
      > </a
      ><a name="4078" class="Symbol"
      >:</a
      ><a name="4079"
      > </a
      ><a name="4080" class="PrimitiveType"
      >Set</a
      ><a name="4083"
      >
</a
      ><a name="4084" href="Stlc.html#4070" class="Function"
      >Context</a
      ><a name="4091"
      > </a
      ><a name="4092" class="Symbol"
      >=</a
      ><a name="4093"
      > </a
      ><a name="4094" href="Maps.html#11102" class="Function"
      >PartialMap</a
      ><a name="4104"
      > </a
      ><a name="4105" href="Stlc.html#971" class="Datatype"
      >Type</a
      ><a name="4109"
      >

</a
      ><a name="4111" class="Keyword"
      >data</a
      ><a name="4115"
      > </a
      ><a name="4116" href="Stlc.html#4116" class="Datatype Operator"
      >_&#8866;_&#8712;_</a
      ><a name="4121"
      > </a
      ><a name="4122" class="Symbol"
      >:</a
      ><a name="4123"
      > </a
      ><a name="4124" href="Stlc.html#4070" class="Function"
      >Context</a
      ><a name="4131"
      > </a
      ><a name="4132" class="Symbol"
      >&#8594;</a
      ><a name="4133"
      > </a
      ><a name="4134" href="Stlc.html#1032" class="Datatype"
      >Term</a
      ><a name="4138"
      > </a
      ><a name="4139" class="Symbol"
      >&#8594;</a
      ><a name="4140"
      > </a
      ><a name="4141" href="Stlc.html#971" class="Datatype"
      >Type</a
      ><a name="4145"
      > </a
      ><a name="4146" class="Symbol"
      >&#8594;</a
      ><a name="4147"
      > </a
      ><a name="4148" class="PrimitiveType"
      >Set</a
      ><a name="4151"
      > </a
      ><a name="4152" class="Keyword"
      >where</a
      ><a name="4157"
      >
  </a
      ><a name="4160" href="Stlc.html#4160" class="InductiveConstructor"
      >Ax</a
      ><a name="4162"
      > </a
      ><a name="4163" class="Symbol"
      >:</a
      ><a name="4164"
      > </a
      ><a name="4165" class="Symbol"
      >&#8704;</a
      ><a name="4166"
      > </a
      ><a name="4167" class="Symbol"
      >{</a
      ><a name="4168" href="Stlc.html#4168" class="Bound"
      >&#915;</a
      ><a name="4169"
      > </a
      ><a name="4170" href="Stlc.html#4170" class="Bound"
      >x</a
      ><a name="4171"
      > </a
      ><a name="4172" href="Stlc.html#4172" class="Bound"
      >A</a
      ><a name="4173" class="Symbol"
      >}</a
      ><a name="4174"
      > </a
      ><a name="4175" class="Symbol"
      >&#8594;</a
      ><a name="4176"
      >
    </a
      ><a name="4181" href="Stlc.html#4168" class="Bound"
      >&#915;</a
      ><a name="4182"
      > </a
      ><a name="4183" href="Stlc.html#4170" class="Bound"
      >x</a
      ><a name="4184"
      > </a
      ><a name="4185" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="4186"
      > </a
      ><a name="4187" href="https://agda.github.io/agda-stdlib/Data.Maybe.Base.html#373" class="InductiveConstructor"
      >just</a
      ><a name="4191"
      > </a
      ><a name="4192" href="Stlc.html#4172" class="Bound"
      >A</a
      ><a name="4193"
      > </a
      ><a name="4194" class="Symbol"
      >&#8594;</a
      ><a name="4195"
      >
    </a
      ><a name="4200" href="Stlc.html#4168" class="Bound"
      >&#915;</a
      ><a name="4201"
      > </a
      ><a name="4202" href="Stlc.html#4116" class="Datatype Operator"
      >&#8866;</a
      ><a name="4203"
      > </a
      ><a name="4204" href="Stlc.html#1051" class="InductiveConstructor"
      >var&#7488;</a
      ><a name="4208"
      > </a
      ><a name="4209" href="Stlc.html#4170" class="Bound"
      >x</a
      ><a name="4210"
      > </a
      ><a name="4211" href="Stlc.html#4116" class="Datatype Operator"
      >&#8712;</a
      ><a name="4212"
      > </a
      ><a name="4213" href="Stlc.html#4172" class="Bound"
      >A</a
      ><a name="4214"
      >
  </a
      ><a name="4217" href="Stlc.html#4217" class="InductiveConstructor"
      >&#8658;-I</a
      ><a name="4220"
      > </a
      ><a name="4221" class="Symbol"
      >:</a
      ><a name="4222"
      > </a
      ><a name="4223" class="Symbol"
      >&#8704;</a
      ><a name="4224"
      > </a
      ><a name="4225" class="Symbol"
      >{</a
      ><a name="4226" href="Stlc.html#4226" class="Bound"
      >&#915;</a
      ><a name="4227"
      > </a
      ><a name="4228" href="Stlc.html#4228" class="Bound"
      >x</a
      ><a name="4229"
      > </a
      ><a name="4230" href="Stlc.html#4230" class="Bound"
      >N</a
      ><a name="4231"
      > </a
      ><a name="4232" href="Stlc.html#4232" class="Bound"
      >A</a
      ><a name="4233"
      > </a
      ><a name="4234" href="Stlc.html#4234" class="Bound"
      >B</a
      ><a name="4235" class="Symbol"
      >}</a
      ><a name="4236"
      > </a
      ><a name="4237" class="Symbol"
      >&#8594;</a
      ><a name="4238"
      >
    </a
      ><a name="4243" class="Symbol"
      >(</a
      ><a name="4244" href="Stlc.html#4226" class="Bound"
      >&#915;</a
      ><a name="4245"
      > </a
      ><a name="4246" href="Maps.html#11317" class="Function Operator"
      >,</a
      ><a name="4247"
      > </a
      ><a name="4248" href="Stlc.html#4228" class="Bound"
      >x</a
      ><a name="4249"
      > </a
      ><a name="4250" href="Maps.html#11317" class="Function Operator"
      >&#8614;</a
      ><a name="4251"
      > </a
      ><a name="4252" href="Stlc.html#4232" class="Bound"
      >A</a
      ><a name="4253" class="Symbol"
      >)</a
      ><a name="4254"
      > </a
      ><a name="4255" href="Stlc.html#4116" class="Datatype Operator"
      >&#8866;</a
      ><a name="4256"
      > </a
      ><a name="4257" href="Stlc.html#4230" class="Bound"
      >N</a
      ><a name="4258"
      > </a
      ><a name="4259" href="Stlc.html#4116" class="Datatype Operator"
      >&#8712;</a
      ><a name="4260"
      > </a
      ><a name="4261" href="Stlc.html#4234" class="Bound"
      >B</a
      ><a name="4262"
      > </a
      ><a name="4263" class="Symbol"
      >&#8594;</a
      ><a name="4264"
      >
    </a
      ><a name="4269" href="Stlc.html#4226" class="Bound"
      >&#915;</a
      ><a name="4270"
      > </a
      ><a name="4271" href="Stlc.html#4116" class="Datatype Operator"
      >&#8866;</a
      ><a name="4272"
      > </a
      ><a name="4273" class="Symbol"
      >(</a
      ><a name="4274" href="Stlc.html#1070" class="InductiveConstructor Operator"
      >&#955;&#7488;</a
      ><a name="4276"
      > </a
      ><a name="4277" href="Stlc.html#4228" class="Bound"
      >x</a
      ><a name="4278"
      > </a
      ><a name="4279" href="Stlc.html#1070" class="InductiveConstructor Operator"
      >&#8712;</a
      ><a name="4280"
      > </a
      ><a name="4281" href="Stlc.html#4232" class="Bound"
      >A</a
      ><a name="4282"
      > </a
      ><a name="4283" href="Stlc.html#1070" class="InductiveConstructor Operator"
      >&#8658;</a
      ><a name="4284"
      > </a
      ><a name="4285" href="Stlc.html#4230" class="Bound"
      >N</a
      ><a name="4286" class="Symbol"
      >)</a
      ><a name="4287"
      > </a
      ><a name="4288" href="Stlc.html#4116" class="Datatype Operator"
      >&#8712;</a
      ><a name="4289"
      > </a
      ><a name="4290" class="Symbol"
      >(</a
      ><a name="4291" href="Stlc.html#4232" class="Bound"
      >A</a
      ><a name="4292"
      > </a
      ><a name="4293" href="Stlc.html#1001" class="InductiveConstructor Operator"
      >&#8658;</a
      ><a name="4294"
      > </a
      ><a name="4295" href="Stlc.html#4234" class="Bound"
      >B</a
      ><a name="4296" class="Symbol"
      >)</a
      ><a name="4297"
      >
  </a
      ><a name="4300" href="Stlc.html#4300" class="InductiveConstructor"
      >&#8658;-E</a
      ><a name="4303"
      > </a
      ><a name="4304" class="Symbol"
      >:</a
      ><a name="4305"
      > </a
      ><a name="4306" class="Symbol"
      >&#8704;</a
      ><a name="4307"
      > </a
      ><a name="4308" class="Symbol"
      >{</a
      ><a name="4309" href="Stlc.html#4309" class="Bound"
      >&#915;</a
      ><a name="4310"
      > </a
      ><a name="4311" href="Stlc.html#4311" class="Bound"
      >L</a
      ><a name="4312"
      > </a
      ><a name="4313" href="Stlc.html#4313" class="Bound"
      >M</a
      ><a name="4314"
      > </a
      ><a name="4315" href="Stlc.html#4315" class="Bound"
      >A</a
      ><a name="4316"
      > </a
      ><a name="4317" href="Stlc.html#4317" class="Bound"
      >B</a
      ><a name="4318" class="Symbol"
      >}</a
      ><a name="4319"
      > </a
      ><a name="4320" class="Symbol"
      >&#8594;</a
      ><a name="4321"
      >
    </a
      ><a name="4326" href="Stlc.html#4309" class="Bound"
      >&#915;</a
      ><a name="4327"
      > </a
      ><a name="4328" href="Stlc.html#4116" class="Datatype Operator"
      >&#8866;</a
      ><a name="4329"
      > </a
      ><a name="4330" href="Stlc.html#4311" class="Bound"
      >L</a
      ><a name="4331"
      > </a
      ><a name="4332" href="Stlc.html#4116" class="Datatype Operator"
      >&#8712;</a
      ><a name="4333"
      > </a
      ><a name="4334" class="Symbol"
      >(</a
      ><a name="4335" href="Stlc.html#4315" class="Bound"
      >A</a
      ><a name="4336"
      > </a
      ><a name="4337" href="Stlc.html#1001" class="InductiveConstructor Operator"
      >&#8658;</a
      ><a name="4338"
      > </a
      ><a name="4339" href="Stlc.html#4317" class="Bound"
      >B</a
      ><a name="4340" class="Symbol"
      >)</a
      ><a name="4341"
      > </a
      ><a name="4342" class="Symbol"
      >&#8594;</a
      ><a name="4343"
      >
    </a
      ><a name="4348" href="Stlc.html#4309" class="Bound"
      >&#915;</a
      ><a name="4349"
      > </a
      ><a name="4350" href="Stlc.html#4116" class="Datatype Operator"
      >&#8866;</a
      ><a name="4351"
      > </a
      ><a name="4352" href="Stlc.html#4313" class="Bound"
      >M</a
      ><a name="4353"
      > </a
      ><a name="4354" href="Stlc.html#4116" class="Datatype Operator"
      >&#8712;</a
      ><a name="4355"
      > </a
      ><a name="4356" href="Stlc.html#4315" class="Bound"
      >A</a
      ><a name="4357"
      > </a
      ><a name="4358" class="Symbol"
      >&#8594;</a
      ><a name="4359"
      >
    </a
      ><a name="4364" href="Stlc.html#4309" class="Bound"
      >&#915;</a
      ><a name="4365"
      > </a
      ><a name="4366" href="Stlc.html#4116" class="Datatype Operator"
      >&#8866;</a
      ><a name="4367"
      > </a
      ><a name="4368" href="Stlc.html#4311" class="Bound"
      >L</a
      ><a name="4369"
      > </a
      ><a name="4370" href="Stlc.html#1106" class="InductiveConstructor Operator"
      >&#183;&#7488;</a
      ><a name="4372"
      > </a
      ><a name="4373" href="Stlc.html#4313" class="Bound"
      >M</a
      ><a name="4374"
      > </a
      ><a name="4375" href="Stlc.html#4116" class="Datatype Operator"
      >&#8712;</a
      ><a name="4376"
      > </a
      ><a name="4377" href="Stlc.html#4317" class="Bound"
      >B</a
      ><a name="4378"
      >
  </a
      ><a name="4381" href="Stlc.html#4381" class="InductiveConstructor"
      >&#120121;-I&#8321;</a
      ><a name="4385"
      > </a
      ><a name="4386" class="Symbol"
      >:</a
      ><a name="4387"
      > </a
      ><a name="4388" class="Symbol"
      >&#8704;</a
      ><a name="4389"
      > </a
      ><a name="4390" class="Symbol"
      >{</a
      ><a name="4391" href="Stlc.html#4391" class="Bound"
      >&#915;</a
      ><a name="4392" class="Symbol"
      >}</a
      ><a name="4393"
      > </a
      ><a name="4394" class="Symbol"
      >&#8594;</a
      ><a name="4395"
      >
    </a
      ><a name="4400" href="Stlc.html#4391" class="Bound"
      >&#915;</a
      ><a name="4401"
      > </a
      ><a name="4402" href="Stlc.html#4116" class="Datatype Operator"
      >&#8866;</a
      ><a name="4403"
      > </a
      ><a name="4404" href="Stlc.html#1134" class="InductiveConstructor"
      >true&#7488;</a
      ><a name="4409"
      > </a
      ><a name="4410" href="Stlc.html#4116" class="Datatype Operator"
      >&#8712;</a
      ><a name="4411"
      > </a
      ><a name="4412" href="Stlc.html#990" class="InductiveConstructor"
      >&#120121;</a
      ><a name="4413"
      >
  </a
      ><a name="4416" href="Stlc.html#4416" class="InductiveConstructor"
      >&#120121;-I&#8322;</a
      ><a name="4420"
      > </a
      ><a name="4421" class="Symbol"
      >:</a
      ><a name="4422"
      > </a
      ><a name="4423" class="Symbol"
      >&#8704;</a
      ><a name="4424"
      > </a
      ><a name="4425" class="Symbol"
      >{</a
      ><a name="4426" href="Stlc.html#4426" class="Bound"
      >&#915;</a
      ><a name="4427" class="Symbol"
      >}</a
      ><a name="4428"
      > </a
      ><a name="4429" class="Symbol"
      >&#8594;</a
      ><a name="4430"
      >
    </a
      ><a name="4435" href="Stlc.html#4426" class="Bound"
      >&#915;</a
      ><a name="4436"
      > </a
      ><a name="4437" href="Stlc.html#4116" class="Datatype Operator"
      >&#8866;</a
      ><a name="4438"
      > </a
      ><a name="4439" href="Stlc.html#1149" class="InductiveConstructor"
      >false&#7488;</a
      ><a name="4445"
      > </a
      ><a name="4446" href="Stlc.html#4116" class="Datatype Operator"
      >&#8712;</a
      ><a name="4447"
      > </a
      ><a name="4448" href="Stlc.html#990" class="InductiveConstructor"
      >&#120121;</a
      ><a name="4449"
      >
  </a
      ><a name="4452" href="Stlc.html#4452" class="InductiveConstructor"
      >&#120121;-E</a
      ><a name="4455"
      > </a
      ><a name="4456" class="Symbol"
      >:</a
      ><a name="4457"
      > </a
      ><a name="4458" class="Symbol"
      >&#8704;</a
      ><a name="4459"
      > </a
      ><a name="4460" class="Symbol"
      >{</a
      ><a name="4461" href="Stlc.html#4461" class="Bound"
      >&#915;</a
      ><a name="4462"
      > </a
      ><a name="4463" href="Stlc.html#4463" class="Bound"
      >L</a
      ><a name="4464"
      > </a
      ><a name="4465" href="Stlc.html#4465" class="Bound"
      >M</a
      ><a name="4466"
      > </a
      ><a name="4467" href="Stlc.html#4467" class="Bound"
      >N</a
      ><a name="4468"
      > </a
      ><a name="4469" href="Stlc.html#4469" class="Bound"
      >A</a
      ><a name="4470" class="Symbol"
      >}</a
      ><a name="4471"
      > </a
      ><a name="4472" class="Symbol"
      >&#8594;</a
      ><a name="4473"
      >
    </a
      ><a name="4478" href="Stlc.html#4461" class="Bound"
      >&#915;</a
      ><a name="4479"
      > </a
      ><a name="4480" href="Stlc.html#4116" class="Datatype Operator"
      >&#8866;</a
      ><a name="4481"
      > </a
      ><a name="4482" href="Stlc.html#4463" class="Bound"
      >L</a
      ><a name="4483"
      > </a
      ><a name="4484" href="Stlc.html#4116" class="Datatype Operator"
      >&#8712;</a
      ><a name="4485"
      > </a
      ><a name="4486" href="Stlc.html#990" class="InductiveConstructor"
      >&#120121;</a
      ><a name="4487"
      > </a
      ><a name="4488" class="Symbol"
      >&#8594;</a
      ><a name="4489"
      >
    </a
      ><a name="4494" href="Stlc.html#4461" class="Bound"
      >&#915;</a
      ><a name="4495"
      > </a
      ><a name="4496" href="Stlc.html#4116" class="Datatype Operator"
      >&#8866;</a
      ><a name="4497"
      > </a
      ><a name="4498" href="Stlc.html#4465" class="Bound"
      >M</a
      ><a name="4499"
      > </a
      ><a name="4500" href="Stlc.html#4116" class="Datatype Operator"
      >&#8712;</a
      ><a name="4501"
      > </a
      ><a name="4502" href="Stlc.html#4469" class="Bound"
      >A</a
      ><a name="4503"
      > </a
      ><a name="4504" class="Symbol"
      >&#8594;</a
      ><a name="4505"
      >
    </a
      ><a name="4510" href="Stlc.html#4461" class="Bound"
      >&#915;</a
      ><a name="4511"
      > </a
      ><a name="4512" href="Stlc.html#4116" class="Datatype Operator"
      >&#8866;</a
      ><a name="4513"
      > </a
      ><a name="4514" href="Stlc.html#4467" class="Bound"
      >N</a
      ><a name="4515"
      > </a
      ><a name="4516" href="Stlc.html#4116" class="Datatype Operator"
      >&#8712;</a
      ><a name="4517"
      > </a
      ><a name="4518" href="Stlc.html#4469" class="Bound"
      >A</a
      ><a name="4519"
      > </a
      ><a name="4520" class="Symbol"
      >&#8594;</a
      ><a name="4521"
      >
    </a
      ><a name="4526" href="Stlc.html#4461" class="Bound"
      >&#915;</a
      ><a name="4527"
      > </a
      ><a name="4528" href="Stlc.html#4116" class="Datatype Operator"
      >&#8866;</a
      ><a name="4529"
      > </a
      ><a name="4530" class="Symbol"
      >(</a
      ><a name="4531" href="Stlc.html#1165" class="InductiveConstructor Operator"
      >if&#7488;</a
      ><a name="4534"
      > </a
      ><a name="4535" href="Stlc.html#4463" class="Bound"
      >L</a
      ><a name="4536"
      > </a
      ><a name="4537" href="Stlc.html#1165" class="InductiveConstructor Operator"
      >then</a
      ><a name="4541"
      > </a
      ><a name="4542" href="Stlc.html#4465" class="Bound"
      >M</a
      ><a name="4543"
      > </a
      ><a name="4544" href="Stlc.html#1165" class="InductiveConstructor Operator"
      >else</a
      ><a name="4548"
      > </a
      ><a name="4549" href="Stlc.html#4467" class="Bound"
      >N</a
      ><a name="4550" class="Symbol"
      >)</a
      ><a name="4551"
      > </a
      ><a name="4552" href="Stlc.html#4116" class="Datatype Operator"
      >&#8712;</a
      ><a name="4553"
      > </a
      ><a name="4554" href="Stlc.html#4469" class="Bound"
      >A</a
      >

</pre>
