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
      ><a name="215" href="Maps.html#10227" class="Function"
      >PartialMap</a
      ><a name="225" class="Symbol"
      >;</a
      ><a name="226"
      > </a
      ><a name="227" class="Keyword"
      >module</a
      ><a name="233"
      > </a
      ><a name="234" href="Maps.html#10316" class="Module"
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
      ><a name="251" href="Maps.html#10316" class="Module"
      >PartialMap</a
      ><a name="261"
      > </a
      ><a name="262" class="Keyword"
      >using</a
      ><a name="267"
      > </a
      ><a name="268" class="Symbol"
      >(</a
      ><a name="269" href="Maps.html#10360" class="Function"
      >&#8709;</a
      ><a name="270" class="Symbol"
      >;</a
      ><a name="271"
      > </a
      ><a name="272" href="Maps.html#10464" class="Function Operator"
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
      ><a name="351" href="https://agda.github.io/agda-stdlib/Data.Empty.html#360" class="Function"
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
      ><a name="672" class="Symbol"
      >as</a
      ><a name="674"
      > </a
      ><a name="675" class="Module"
      >P</a
      ><a name="676"
      > </a
      ><a name="677" class="Keyword"
      >using</a
      ><a name="682"
      > </a
      ><a name="683" class="Symbol"
      >(</a
      ><a name="684" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >_&#8801;_</a
      ><a name="687" class="Symbol"
      >;</a
      ><a name="688"
      > </a
      ><a name="689" href="https://agda.github.io/agda-stdlib/Relation.Binary.Core.html#4493" class="Function Operator"
      >_&#8802;_</a
      ><a name="692" class="Symbol"
      >;</a
      ><a name="693"
      > </a
      ><a name="694" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="698" class="Symbol"
      >)</a
      ><a name="699"
      >
</a
      ><a name="700" class="Keyword"
      >open</a
      ><a name="704"
      > </a
      ><a name="705" class="Keyword"
      >import</a
      ><a name="711"
      > </a
      ><a name="712" href="https://agda.github.io/agda-stdlib/Relation.Binary.html#1" class="Module"
      >Relation.Binary</a
      ><a name="727"
      > </a
      ><a name="728" class="Keyword"
      >using</a
      ><a name="733"
      > </a
      ><a name="734" class="Symbol"
      >(</a
      ><a name="735" href="https://agda.github.io/agda-stdlib/Relation.Binary.html#1470" class="Record"
      >Preorder</a
      ><a name="743" class="Symbol"
      >)</a
      ><a name="744"
      >
</a
      ><a name="745" class="Keyword"
      >import</a
      ><a name="751"
      > </a
      ><a name="752" href="https://agda.github.io/agda-stdlib/Relation.Binary.PreorderReasoning.html#1" class="Module"
      >Relation.Binary.PreorderReasoning</a
      ><a name="785"
      > </a
      ><a name="786" class="Symbol"
      >as</a
      ><a name="788"
      > </a
      ><a name="789" class="Module"
      >PreorderReasoning</a
      ><a name="806"
      >
</a
      ><a name="807" class="Comment"
      >-- open import Relation.Binary.Core using (Rel)</a
      ><a name="854"
      >
</a
      ><a name="855" class="Comment"
      >-- open import Data.Product using (&#8707;; &#8708;; _,_)</a
      ><a name="900"
      >
</a
      ><a name="901" class="Comment"
      >-- open import Function using (_&#8728;_; _$_)</a
      >

</pre>


## Syntax

Syntax of types and terms. All source terms are labeled with $ᵀ$.

<pre class="Agda">

<a name="1046" class="Keyword"
      >infixr</a
      ><a name="1052"
      > </a
      ><a name="1053" class="Number"
      >100</a
      ><a name="1056"
      > </a
      ><a name="1057" href="Stlc.html#1113" class="InductiveConstructor Operator"
      >_&#8658;_</a
      ><a name="1060"
      >
</a
      ><a name="1061" class="Keyword"
      >infixl</a
      ><a name="1067"
      > </a
      ><a name="1068" class="Number"
      >100</a
      ><a name="1071"
      > </a
      ><a name="1072" href="Stlc.html#1218" class="InductiveConstructor Operator"
      >_&#183;&#7488;_</a
      ><a name="1076"
      >

</a
      ><a name="1078" class="Keyword"
      >data</a
      ><a name="1082"
      > </a
      ><a name="1083" href="Stlc.html#1083" class="Datatype"
      >Type</a
      ><a name="1087"
      > </a
      ><a name="1088" class="Symbol"
      >:</a
      ><a name="1089"
      > </a
      ><a name="1090" class="PrimitiveType"
      >Set</a
      ><a name="1093"
      > </a
      ><a name="1094" class="Keyword"
      >where</a
      ><a name="1099"
      >
  </a
      ><a name="1102" href="Stlc.html#1102" class="InductiveConstructor"
      >&#120121;</a
      ><a name="1103"
      > </a
      ><a name="1104" class="Symbol"
      >:</a
      ><a name="1105"
      > </a
      ><a name="1106" href="Stlc.html#1083" class="Datatype"
      >Type</a
      ><a name="1110"
      >
  </a
      ><a name="1113" href="Stlc.html#1113" class="InductiveConstructor Operator"
      >_&#8658;_</a
      ><a name="1116"
      > </a
      ><a name="1117" class="Symbol"
      >:</a
      ><a name="1118"
      > </a
      ><a name="1119" href="Stlc.html#1083" class="Datatype"
      >Type</a
      ><a name="1123"
      > </a
      ><a name="1124" class="Symbol"
      >&#8594;</a
      ><a name="1125"
      > </a
      ><a name="1126" href="Stlc.html#1083" class="Datatype"
      >Type</a
      ><a name="1130"
      > </a
      ><a name="1131" class="Symbol"
      >&#8594;</a
      ><a name="1132"
      > </a
      ><a name="1133" href="Stlc.html#1083" class="Datatype"
      >Type</a
      ><a name="1137"
      >

</a
      ><a name="1139" class="Keyword"
      >data</a
      ><a name="1143"
      > </a
      ><a name="1144" href="Stlc.html#1144" class="Datatype"
      >Term</a
      ><a name="1148"
      > </a
      ><a name="1149" class="Symbol"
      >:</a
      ><a name="1150"
      > </a
      ><a name="1151" class="PrimitiveType"
      >Set</a
      ><a name="1154"
      > </a
      ><a name="1155" class="Keyword"
      >where</a
      ><a name="1160"
      >
  </a
      ><a name="1163" href="Stlc.html#1163" class="InductiveConstructor"
      >var&#7488;</a
      ><a name="1167"
      > </a
      ><a name="1168" class="Symbol"
      >:</a
      ><a name="1169"
      > </a
      ><a name="1170" href="Maps.html#2215" class="Datatype"
      >Id</a
      ><a name="1172"
      > </a
      ><a name="1173" class="Symbol"
      >&#8594;</a
      ><a name="1174"
      > </a
      ><a name="1175" href="Stlc.html#1144" class="Datatype"
      >Term</a
      ><a name="1179"
      >
  </a
      ><a name="1182" href="Stlc.html#1182" class="InductiveConstructor Operator"
      >&#955;&#7488;_&#8712;_&#8658;_</a
      ><a name="1189"
      > </a
      ><a name="1190" class="Symbol"
      >:</a
      ><a name="1191"
      > </a
      ><a name="1192" href="Maps.html#2215" class="Datatype"
      >Id</a
      ><a name="1194"
      > </a
      ><a name="1195" class="Symbol"
      >&#8594;</a
      ><a name="1196"
      > </a
      ><a name="1197" href="Stlc.html#1083" class="Datatype"
      >Type</a
      ><a name="1201"
      > </a
      ><a name="1202" class="Symbol"
      >&#8594;</a
      ><a name="1203"
      > </a
      ><a name="1204" href="Stlc.html#1144" class="Datatype"
      >Term</a
      ><a name="1208"
      > </a
      ><a name="1209" class="Symbol"
      >&#8594;</a
      ><a name="1210"
      > </a
      ><a name="1211" href="Stlc.html#1144" class="Datatype"
      >Term</a
      ><a name="1215"
      >
  </a
      ><a name="1218" href="Stlc.html#1218" class="InductiveConstructor Operator"
      >_&#183;&#7488;_</a
      ><a name="1222"
      > </a
      ><a name="1223" class="Symbol"
      >:</a
      ><a name="1224"
      > </a
      ><a name="1225" href="Stlc.html#1144" class="Datatype"
      >Term</a
      ><a name="1229"
      > </a
      ><a name="1230" class="Symbol"
      >&#8594;</a
      ><a name="1231"
      > </a
      ><a name="1232" href="Stlc.html#1144" class="Datatype"
      >Term</a
      ><a name="1236"
      > </a
      ><a name="1237" class="Symbol"
      >&#8594;</a
      ><a name="1238"
      > </a
      ><a name="1239" href="Stlc.html#1144" class="Datatype"
      >Term</a
      ><a name="1243"
      >
  </a
      ><a name="1246" href="Stlc.html#1246" class="InductiveConstructor"
      >true&#7488;</a
      ><a name="1251"
      > </a
      ><a name="1252" class="Symbol"
      >:</a
      ><a name="1253"
      > </a
      ><a name="1254" href="Stlc.html#1144" class="Datatype"
      >Term</a
      ><a name="1258"
      >
  </a
      ><a name="1261" href="Stlc.html#1261" class="InductiveConstructor"
      >false&#7488;</a
      ><a name="1267"
      > </a
      ><a name="1268" class="Symbol"
      >:</a
      ><a name="1269"
      > </a
      ><a name="1270" href="Stlc.html#1144" class="Datatype"
      >Term</a
      ><a name="1274"
      >
  </a
      ><a name="1277" href="Stlc.html#1277" class="InductiveConstructor Operator"
      >if&#7488;_then_else_</a
      ><a name="1291"
      > </a
      ><a name="1292" class="Symbol"
      >:</a
      ><a name="1293"
      > </a
      ><a name="1294" href="Stlc.html#1144" class="Datatype"
      >Term</a
      ><a name="1298"
      > </a
      ><a name="1299" class="Symbol"
      >&#8594;</a
      ><a name="1300"
      > </a
      ><a name="1301" href="Stlc.html#1144" class="Datatype"
      >Term</a
      ><a name="1305"
      > </a
      ><a name="1306" class="Symbol"
      >&#8594;</a
      ><a name="1307"
      > </a
      ><a name="1308" href="Stlc.html#1144" class="Datatype"
      >Term</a
      ><a name="1312"
      > </a
      ><a name="1313" class="Symbol"
      >&#8594;</a
      ><a name="1314"
      > </a
      ><a name="1315" href="Stlc.html#1144" class="Datatype"
      >Term</a
      >

</pre>

Some examples.
<pre class="Agda">

<a name="1360" href="Stlc.html#1360" class="Function"
      >f</a
      ><a name="1361"
      > </a
      ><a name="1362" href="Stlc.html#1362" class="Function"
      >x</a
      ><a name="1363"
      > </a
      ><a name="1364" href="Stlc.html#1364" class="Function"
      >y</a
      ><a name="1365"
      > </a
      ><a name="1366" class="Symbol"
      >:</a
      ><a name="1367"
      > </a
      ><a name="1368" href="Maps.html#2215" class="Datatype"
      >Id</a
      ><a name="1370"
      >
</a
      ><a name="1371" href="Stlc.html#1360" class="Function"
      >f</a
      ><a name="1372"
      >  </a
      ><a name="1374" class="Symbol"
      >=</a
      ><a name="1375"
      >  </a
      ><a name="1377" href="Maps.html#2232" class="InductiveConstructor"
      >id</a
      ><a name="1379"
      > </a
      ><a name="1380" class="String"
      >&quot;f&quot;</a
      ><a name="1383"
      >
</a
      ><a name="1384" href="Stlc.html#1362" class="Function"
      >x</a
      ><a name="1385"
      >  </a
      ><a name="1387" class="Symbol"
      >=</a
      ><a name="1388"
      >  </a
      ><a name="1390" href="Maps.html#2232" class="InductiveConstructor"
      >id</a
      ><a name="1392"
      > </a
      ><a name="1393" class="String"
      >&quot;x&quot;</a
      ><a name="1396"
      >
</a
      ><a name="1397" href="Stlc.html#1364" class="Function"
      >y</a
      ><a name="1398"
      >  </a
      ><a name="1400" class="Symbol"
      >=</a
      ><a name="1401"
      >  </a
      ><a name="1403" href="Maps.html#2232" class="InductiveConstructor"
      >id</a
      ><a name="1405"
      > </a
      ><a name="1406" class="String"
      >&quot;y&quot;</a
      ><a name="1409"
      >

</a
      ><a name="1411" href="Stlc.html#1411" class="Function"
      >I[&#120121;]</a
      ><a name="1415"
      > </a
      ><a name="1416" href="Stlc.html#1416" class="Function"
      >I[&#120121;&#8658;&#120121;]</a
      ><a name="1422"
      > </a
      ><a name="1423" href="Stlc.html#1423" class="Function"
      >K[&#120121;][&#120121;]</a
      ><a name="1430"
      > </a
      ><a name="1431" href="Stlc.html#1431" class="Function"
      >not[&#120121;]</a
      ><a name="1437"
      > </a
      ><a name="1438" class="Symbol"
      >:</a
      ><a name="1439"
      > </a
      ><a name="1440" href="Stlc.html#1144" class="Datatype"
      >Term</a
      ><a name="1444"
      > 
</a
      ><a name="1446" href="Stlc.html#1411" class="Function"
      >I[&#120121;]</a
      ><a name="1450"
      >  </a
      ><a name="1452" class="Symbol"
      >=</a
      ><a name="1453"
      >  </a
      ><a name="1455" class="Symbol"
      >(</a
      ><a name="1456" href="Stlc.html#1182" class="InductiveConstructor Operator"
      >&#955;&#7488;</a
      ><a name="1458"
      > </a
      ><a name="1459" href="Stlc.html#1362" class="Function"
      >x</a
      ><a name="1460"
      > </a
      ><a name="1461" href="Stlc.html#1182" class="InductiveConstructor Operator"
      >&#8712;</a
      ><a name="1462"
      > </a
      ><a name="1463" href="Stlc.html#1102" class="InductiveConstructor"
      >&#120121;</a
      ><a name="1464"
      > </a
      ><a name="1465" href="Stlc.html#1182" class="InductiveConstructor Operator"
      >&#8658;</a
      ><a name="1466"
      > </a
      ><a name="1467" class="Symbol"
      >(</a
      ><a name="1468" href="Stlc.html#1163" class="InductiveConstructor"
      >var&#7488;</a
      ><a name="1472"
      > </a
      ><a name="1473" href="Stlc.html#1362" class="Function"
      >x</a
      ><a name="1474" class="Symbol"
      >))</a
      ><a name="1476"
      >
</a
      ><a name="1477" href="Stlc.html#1416" class="Function"
      >I[&#120121;&#8658;&#120121;]</a
      ><a name="1483"
      >  </a
      ><a name="1485" class="Symbol"
      >=</a
      ><a name="1486"
      >  </a
      ><a name="1488" class="Symbol"
      >(</a
      ><a name="1489" href="Stlc.html#1182" class="InductiveConstructor Operator"
      >&#955;&#7488;</a
      ><a name="1491"
      > </a
      ><a name="1492" href="Stlc.html#1360" class="Function"
      >f</a
      ><a name="1493"
      > </a
      ><a name="1494" href="Stlc.html#1182" class="InductiveConstructor Operator"
      >&#8712;</a
      ><a name="1495"
      > </a
      ><a name="1496" class="Symbol"
      >(</a
      ><a name="1497" href="Stlc.html#1102" class="InductiveConstructor"
      >&#120121;</a
      ><a name="1498"
      > </a
      ><a name="1499" href="Stlc.html#1113" class="InductiveConstructor Operator"
      >&#8658;</a
      ><a name="1500"
      > </a
      ><a name="1501" href="Stlc.html#1102" class="InductiveConstructor"
      >&#120121;</a
      ><a name="1502" class="Symbol"
      >)</a
      ><a name="1503"
      > </a
      ><a name="1504" href="Stlc.html#1182" class="InductiveConstructor Operator"
      >&#8658;</a
      ><a name="1505"
      > </a
      ><a name="1506" class="Symbol"
      >(</a
      ><a name="1507" href="Stlc.html#1182" class="InductiveConstructor Operator"
      >&#955;&#7488;</a
      ><a name="1509"
      > </a
      ><a name="1510" href="Stlc.html#1362" class="Function"
      >x</a
      ><a name="1511"
      > </a
      ><a name="1512" href="Stlc.html#1182" class="InductiveConstructor Operator"
      >&#8712;</a
      ><a name="1513"
      > </a
      ><a name="1514" href="Stlc.html#1102" class="InductiveConstructor"
      >&#120121;</a
      ><a name="1515"
      > </a
      ><a name="1516" href="Stlc.html#1182" class="InductiveConstructor Operator"
      >&#8658;</a
      ><a name="1517"
      > </a
      ><a name="1518" class="Symbol"
      >((</a
      ><a name="1520" href="Stlc.html#1163" class="InductiveConstructor"
      >var&#7488;</a
      ><a name="1524"
      > </a
      ><a name="1525" href="Stlc.html#1360" class="Function"
      >f</a
      ><a name="1526" class="Symbol"
      >)</a
      ><a name="1527"
      > </a
      ><a name="1528" href="Stlc.html#1218" class="InductiveConstructor Operator"
      >&#183;&#7488;</a
      ><a name="1530"
      > </a
      ><a name="1531" class="Symbol"
      >(</a
      ><a name="1532" href="Stlc.html#1163" class="InductiveConstructor"
      >var&#7488;</a
      ><a name="1536"
      > </a
      ><a name="1537" href="Stlc.html#1362" class="Function"
      >x</a
      ><a name="1538" class="Symbol"
      >))))</a
      ><a name="1542"
      >
</a
      ><a name="1543" href="Stlc.html#1423" class="Function"
      >K[&#120121;][&#120121;]</a
      ><a name="1550"
      >  </a
      ><a name="1552" class="Symbol"
      >=</a
      ><a name="1553"
      >  </a
      ><a name="1555" class="Symbol"
      >(</a
      ><a name="1556" href="Stlc.html#1182" class="InductiveConstructor Operator"
      >&#955;&#7488;</a
      ><a name="1558"
      > </a
      ><a name="1559" href="Stlc.html#1362" class="Function"
      >x</a
      ><a name="1560"
      > </a
      ><a name="1561" href="Stlc.html#1182" class="InductiveConstructor Operator"
      >&#8712;</a
      ><a name="1562"
      > </a
      ><a name="1563" href="Stlc.html#1102" class="InductiveConstructor"
      >&#120121;</a
      ><a name="1564"
      > </a
      ><a name="1565" href="Stlc.html#1182" class="InductiveConstructor Operator"
      >&#8658;</a
      ><a name="1566"
      > </a
      ><a name="1567" class="Symbol"
      >(</a
      ><a name="1568" href="Stlc.html#1182" class="InductiveConstructor Operator"
      >&#955;&#7488;</a
      ><a name="1570"
      > </a
      ><a name="1571" href="Stlc.html#1364" class="Function"
      >y</a
      ><a name="1572"
      > </a
      ><a name="1573" href="Stlc.html#1182" class="InductiveConstructor Operator"
      >&#8712;</a
      ><a name="1574"
      > </a
      ><a name="1575" href="Stlc.html#1102" class="InductiveConstructor"
      >&#120121;</a
      ><a name="1576"
      > </a
      ><a name="1577" href="Stlc.html#1182" class="InductiveConstructor Operator"
      >&#8658;</a
      ><a name="1578"
      > </a
      ><a name="1579" class="Symbol"
      >(</a
      ><a name="1580" href="Stlc.html#1163" class="InductiveConstructor"
      >var&#7488;</a
      ><a name="1584"
      > </a
      ><a name="1585" href="Stlc.html#1362" class="Function"
      >x</a
      ><a name="1586" class="Symbol"
      >)))</a
      ><a name="1589"
      >
</a
      ><a name="1590" href="Stlc.html#1431" class="Function"
      >not[&#120121;]</a
      ><a name="1596"
      >  </a
      ><a name="1598" class="Symbol"
      >=</a
      ><a name="1599"
      >  </a
      ><a name="1601" class="Symbol"
      >(</a
      ><a name="1602" href="Stlc.html#1182" class="InductiveConstructor Operator"
      >&#955;&#7488;</a
      ><a name="1604"
      > </a
      ><a name="1605" href="Stlc.html#1362" class="Function"
      >x</a
      ><a name="1606"
      > </a
      ><a name="1607" href="Stlc.html#1182" class="InductiveConstructor Operator"
      >&#8712;</a
      ><a name="1608"
      > </a
      ><a name="1609" href="Stlc.html#1102" class="InductiveConstructor"
      >&#120121;</a
      ><a name="1610"
      > </a
      ><a name="1611" href="Stlc.html#1182" class="InductiveConstructor Operator"
      >&#8658;</a
      ><a name="1612"
      > </a
      ><a name="1613" class="Symbol"
      >(</a
      ><a name="1614" href="Stlc.html#1277" class="InductiveConstructor Operator"
      >if&#7488;</a
      ><a name="1617"
      > </a
      ><a name="1618" class="Symbol"
      >(</a
      ><a name="1619" href="Stlc.html#1163" class="InductiveConstructor"
      >var&#7488;</a
      ><a name="1623"
      > </a
      ><a name="1624" href="Stlc.html#1362" class="Function"
      >x</a
      ><a name="1625" class="Symbol"
      >)</a
      ><a name="1626"
      > </a
      ><a name="1627" href="Stlc.html#1277" class="InductiveConstructor Operator"
      >then</a
      ><a name="1631"
      > </a
      ><a name="1632" href="Stlc.html#1261" class="InductiveConstructor"
      >false&#7488;</a
      ><a name="1638"
      > </a
      ><a name="1639" href="Stlc.html#1277" class="InductiveConstructor Operator"
      >else</a
      ><a name="1643"
      > </a
      ><a name="1644" href="Stlc.html#1246" class="InductiveConstructor"
      >true&#7488;</a
      ><a name="1649" class="Symbol"
      >))</a
      >

</pre>

## Values

<pre class="Agda">

<a name="1688" class="Keyword"
      >data</a
      ><a name="1692"
      > </a
      ><a name="1693" href="Stlc.html#1693" class="Datatype"
      >value</a
      ><a name="1698"
      > </a
      ><a name="1699" class="Symbol"
      >:</a
      ><a name="1700"
      > </a
      ><a name="1701" href="Stlc.html#1144" class="Datatype"
      >Term</a
      ><a name="1705"
      > </a
      ><a name="1706" class="Symbol"
      >&#8594;</a
      ><a name="1707"
      > </a
      ><a name="1708" class="PrimitiveType"
      >Set</a
      ><a name="1711"
      > </a
      ><a name="1712" class="Keyword"
      >where</a
      ><a name="1717"
      >
  </a
      ><a name="1720" href="Stlc.html#1720" class="InductiveConstructor"
      >value-&#955;&#7488;</a
      ><a name="1728"
      > </a
      ><a name="1729" class="Symbol"
      >:</a
      ><a name="1730"
      > </a
      ><a name="1731" class="Symbol"
      >&#8704;</a
      ><a name="1732"
      > </a
      ><a name="1733" class="Symbol"
      >{</a
      ><a name="1734" href="Stlc.html#1734" class="Bound"
      >x</a
      ><a name="1735"
      > </a
      ><a name="1736" href="Stlc.html#1736" class="Bound"
      >A</a
      ><a name="1737"
      > </a
      ><a name="1738" href="Stlc.html#1738" class="Bound"
      >N</a
      ><a name="1739" class="Symbol"
      >}</a
      ><a name="1740"
      > </a
      ><a name="1741" class="Symbol"
      >&#8594;</a
      ><a name="1742"
      > </a
      ><a name="1743" href="Stlc.html#1693" class="Datatype"
      >value</a
      ><a name="1748"
      > </a
      ><a name="1749" class="Symbol"
      >(</a
      ><a name="1750" href="Stlc.html#1182" class="InductiveConstructor Operator"
      >&#955;&#7488;</a
      ><a name="1752"
      > </a
      ><a name="1753" href="Stlc.html#1734" class="Bound"
      >x</a
      ><a name="1754"
      > </a
      ><a name="1755" href="Stlc.html#1182" class="InductiveConstructor Operator"
      >&#8712;</a
      ><a name="1756"
      > </a
      ><a name="1757" href="Stlc.html#1736" class="Bound"
      >A</a
      ><a name="1758"
      > </a
      ><a name="1759" href="Stlc.html#1182" class="InductiveConstructor Operator"
      >&#8658;</a
      ><a name="1760"
      > </a
      ><a name="1761" href="Stlc.html#1738" class="Bound"
      >N</a
      ><a name="1762" class="Symbol"
      >)</a
      ><a name="1763"
      >
  </a
      ><a name="1766" href="Stlc.html#1766" class="InductiveConstructor"
      >value-true&#7488;</a
      ><a name="1777"
      > </a
      ><a name="1778" class="Symbol"
      >:</a
      ><a name="1779"
      > </a
      ><a name="1780" href="Stlc.html#1693" class="Datatype"
      >value</a
      ><a name="1785"
      > </a
      ><a name="1786" class="Symbol"
      >(</a
      ><a name="1787" href="Stlc.html#1246" class="InductiveConstructor"
      >true&#7488;</a
      ><a name="1792" class="Symbol"
      >)</a
      ><a name="1793"
      >
  </a
      ><a name="1796" href="Stlc.html#1796" class="InductiveConstructor"
      >value-false&#7488;</a
      ><a name="1808"
      > </a
      ><a name="1809" class="Symbol"
      >:</a
      ><a name="1810"
      > </a
      ><a name="1811" href="Stlc.html#1693" class="Datatype"
      >value</a
      ><a name="1816"
      > </a
      ><a name="1817" class="Symbol"
      >(</a
      ><a name="1818" href="Stlc.html#1261" class="InductiveConstructor"
      >false&#7488;</a
      ><a name="1824" class="Symbol"
      >)</a
      >

</pre>

## Substitution

<pre class="Agda">

<a name="1868" href="Stlc.html#1868" class="Function Operator"
      >_[_:=_]</a
      ><a name="1875"
      > </a
      ><a name="1876" class="Symbol"
      >:</a
      ><a name="1877"
      > </a
      ><a name="1878" href="Stlc.html#1144" class="Datatype"
      >Term</a
      ><a name="1882"
      > </a
      ><a name="1883" class="Symbol"
      >&#8594;</a
      ><a name="1884"
      > </a
      ><a name="1885" href="Maps.html#2215" class="Datatype"
      >Id</a
      ><a name="1887"
      > </a
      ><a name="1888" class="Symbol"
      >&#8594;</a
      ><a name="1889"
      > </a
      ><a name="1890" href="Stlc.html#1144" class="Datatype"
      >Term</a
      ><a name="1894"
      > </a
      ><a name="1895" class="Symbol"
      >&#8594;</a
      ><a name="1896"
      > </a
      ><a name="1897" href="Stlc.html#1144" class="Datatype"
      >Term</a
      ><a name="1901"
      >
</a
      ><a name="1902" class="Symbol"
      >(</a
      ><a name="1903" href="Stlc.html#1163" class="InductiveConstructor"
      >var&#7488;</a
      ><a name="1907"
      > </a
      ><a name="1908" href="Stlc.html#1908" class="Bound"
      >x&#8242;</a
      ><a name="1910" class="Symbol"
      >)</a
      ><a name="1911"
      > </a
      ><a name="1912" href="Stlc.html#1868" class="Function Operator"
      >[</a
      ><a name="1913"
      > </a
      ><a name="1914" href="Stlc.html#1914" class="Bound"
      >x</a
      ><a name="1915"
      > </a
      ><a name="1916" href="Stlc.html#1868" class="Function Operator"
      >:=</a
      ><a name="1918"
      > </a
      ><a name="1919" href="Stlc.html#1919" class="Bound"
      >V</a
      ><a name="1920"
      > </a
      ><a name="1921" href="Stlc.html#1868" class="Function Operator"
      >]</a
      ><a name="1922"
      > </a
      ><a name="1923" class="Keyword"
      >with</a
      ><a name="1927"
      > </a
      ><a name="1928" href="Stlc.html#1914" class="Bound"
      >x</a
      ><a name="1929"
      > </a
      ><a name="1930" href="Maps.html#2558" class="Function Operator"
      >&#8799;</a
      ><a name="1931"
      > </a
      ><a name="1932" href="Stlc.html#1908" class="Bound"
      >x&#8242;</a
      ><a name="1934"
      >
</a
      ><a name="1935" class="Symbol"
      >...</a
      ><a name="1938"
      > </a
      ><a name="1939" class="Symbol"
      >|</a
      ><a name="1940"
      > </a
      ><a name="1941" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#520" class="InductiveConstructor"
      >yes</a
      ><a name="1944"
      > </a
      ><a name="1945" class="Symbol"
      >_</a
      ><a name="1946"
      > </a
      ><a name="1947" class="Symbol"
      >=</a
      ><a name="1948"
      > </a
      ><a name="1949" href="Stlc.html#1919" class="Bound"
      >V</a
      ><a name="1950"
      >
</a
      ><a name="1951" class="Symbol"
      >...</a
      ><a name="1954"
      > </a
      ><a name="1955" class="Symbol"
      >|</a
      ><a name="1956"
      > </a
      ><a name="1957" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#547" class="InductiveConstructor"
      >no</a
      ><a name="1959"
      >  </a
      ><a name="1961" class="Symbol"
      >_</a
      ><a name="1962"
      > </a
      ><a name="1963" class="Symbol"
      >=</a
      ><a name="1964"
      > </a
      ><a name="1965" href="Stlc.html#1163" class="InductiveConstructor"
      >var&#7488;</a
      ><a name="1969"
      > </a
      ><a name="1970" href="Stlc.html#1908" class="Bound"
      >x&#8242;</a
      ><a name="1972"
      >
</a
      ><a name="1973" class="Symbol"
      >(</a
      ><a name="1974" href="Stlc.html#1182" class="InductiveConstructor Operator"
      >&#955;&#7488;</a
      ><a name="1976"
      > </a
      ><a name="1977" href="Stlc.html#1977" class="Bound"
      >x&#8242;</a
      ><a name="1979"
      > </a
      ><a name="1980" href="Stlc.html#1182" class="InductiveConstructor Operator"
      >&#8712;</a
      ><a name="1981"
      > </a
      ><a name="1982" href="Stlc.html#1982" class="Bound"
      >A&#8242;</a
      ><a name="1984"
      > </a
      ><a name="1985" href="Stlc.html#1182" class="InductiveConstructor Operator"
      >&#8658;</a
      ><a name="1986"
      > </a
      ><a name="1987" href="Stlc.html#1987" class="Bound"
      >N&#8242;</a
      ><a name="1989" class="Symbol"
      >)</a
      ><a name="1990"
      > </a
      ><a name="1991" href="Stlc.html#1868" class="Function Operator"
      >[</a
      ><a name="1992"
      > </a
      ><a name="1993" href="Stlc.html#1993" class="Bound"
      >x</a
      ><a name="1994"
      > </a
      ><a name="1995" href="Stlc.html#1868" class="Function Operator"
      >:=</a
      ><a name="1997"
      > </a
      ><a name="1998" href="Stlc.html#1998" class="Bound"
      >V</a
      ><a name="1999"
      > </a
      ><a name="2000" href="Stlc.html#1868" class="Function Operator"
      >]</a
      ><a name="2001"
      > </a
      ><a name="2002" class="Keyword"
      >with</a
      ><a name="2006"
      > </a
      ><a name="2007" href="Stlc.html#1993" class="Bound"
      >x</a
      ><a name="2008"
      > </a
      ><a name="2009" href="Maps.html#2558" class="Function Operator"
      >&#8799;</a
      ><a name="2010"
      > </a
      ><a name="2011" href="Stlc.html#1977" class="Bound"
      >x&#8242;</a
      ><a name="2013"
      >
</a
      ><a name="2014" class="Symbol"
      >...</a
      ><a name="2017"
      > </a
      ><a name="2018" class="Symbol"
      >|</a
      ><a name="2019"
      > </a
      ><a name="2020" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#520" class="InductiveConstructor"
      >yes</a
      ><a name="2023"
      > </a
      ><a name="2024" class="Symbol"
      >_</a
      ><a name="2025"
      > </a
      ><a name="2026" class="Symbol"
      >=</a
      ><a name="2027"
      > </a
      ><a name="2028" href="Stlc.html#1182" class="InductiveConstructor Operator"
      >&#955;&#7488;</a
      ><a name="2030"
      > </a
      ><a name="2031" href="Stlc.html#1977" class="Bound"
      >x&#8242;</a
      ><a name="2033"
      > </a
      ><a name="2034" href="Stlc.html#1182" class="InductiveConstructor Operator"
      >&#8712;</a
      ><a name="2035"
      > </a
      ><a name="2036" href="Stlc.html#1982" class="Bound"
      >A&#8242;</a
      ><a name="2038"
      > </a
      ><a name="2039" href="Stlc.html#1182" class="InductiveConstructor Operator"
      >&#8658;</a
      ><a name="2040"
      > </a
      ><a name="2041" href="Stlc.html#1987" class="Bound"
      >N&#8242;</a
      ><a name="2043"
      >
</a
      ><a name="2044" class="Symbol"
      >...</a
      ><a name="2047"
      > </a
      ><a name="2048" class="Symbol"
      >|</a
      ><a name="2049"
      > </a
      ><a name="2050" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#547" class="InductiveConstructor"
      >no</a
      ><a name="2052"
      >  </a
      ><a name="2054" class="Symbol"
      >_</a
      ><a name="2055"
      > </a
      ><a name="2056" class="Symbol"
      >=</a
      ><a name="2057"
      > </a
      ><a name="2058" href="Stlc.html#1182" class="InductiveConstructor Operator"
      >&#955;&#7488;</a
      ><a name="2060"
      > </a
      ><a name="2061" href="Stlc.html#1977" class="Bound"
      >x&#8242;</a
      ><a name="2063"
      > </a
      ><a name="2064" href="Stlc.html#1182" class="InductiveConstructor Operator"
      >&#8712;</a
      ><a name="2065"
      > </a
      ><a name="2066" href="Stlc.html#1982" class="Bound"
      >A&#8242;</a
      ><a name="2068"
      > </a
      ><a name="2069" href="Stlc.html#1182" class="InductiveConstructor Operator"
      >&#8658;</a
      ><a name="2070"
      > </a
      ><a name="2071" class="Symbol"
      >(</a
      ><a name="2072" href="Stlc.html#1987" class="Bound"
      >N&#8242;</a
      ><a name="2074"
      > </a
      ><a name="2075" href="Stlc.html#1868" class="Function Operator"
      >[</a
      ><a name="2076"
      > </a
      ><a name="2077" href="Stlc.html#1993" class="Bound"
      >x</a
      ><a name="2078"
      > </a
      ><a name="2079" href="Stlc.html#1868" class="Function Operator"
      >:=</a
      ><a name="2081"
      > </a
      ><a name="2082" href="Stlc.html#1998" class="Bound"
      >V</a
      ><a name="2083"
      > </a
      ><a name="2084" href="Stlc.html#1868" class="Function Operator"
      >]</a
      ><a name="2085" class="Symbol"
      >)</a
      ><a name="2086"
      >
</a
      ><a name="2087" class="Symbol"
      >(</a
      ><a name="2088" href="Stlc.html#2088" class="Bound"
      >L&#8242;</a
      ><a name="2090"
      > </a
      ><a name="2091" href="Stlc.html#1218" class="InductiveConstructor Operator"
      >&#183;&#7488;</a
      ><a name="2093"
      > </a
      ><a name="2094" href="Stlc.html#2094" class="Bound"
      >M&#8242;</a
      ><a name="2096" class="Symbol"
      >)</a
      ><a name="2097"
      > </a
      ><a name="2098" href="Stlc.html#1868" class="Function Operator"
      >[</a
      ><a name="2099"
      > </a
      ><a name="2100" href="Stlc.html#2100" class="Bound"
      >x</a
      ><a name="2101"
      > </a
      ><a name="2102" href="Stlc.html#1868" class="Function Operator"
      >:=</a
      ><a name="2104"
      > </a
      ><a name="2105" href="Stlc.html#2105" class="Bound"
      >V</a
      ><a name="2106"
      > </a
      ><a name="2107" href="Stlc.html#1868" class="Function Operator"
      >]</a
      ><a name="2108"
      > </a
      ><a name="2109" class="Symbol"
      >=</a
      ><a name="2110"
      >  </a
      ><a name="2112" class="Symbol"
      >(</a
      ><a name="2113" href="Stlc.html#2088" class="Bound"
      >L&#8242;</a
      ><a name="2115"
      > </a
      ><a name="2116" href="Stlc.html#1868" class="Function Operator"
      >[</a
      ><a name="2117"
      > </a
      ><a name="2118" href="Stlc.html#2100" class="Bound"
      >x</a
      ><a name="2119"
      > </a
      ><a name="2120" href="Stlc.html#1868" class="Function Operator"
      >:=</a
      ><a name="2122"
      > </a
      ><a name="2123" href="Stlc.html#2105" class="Bound"
      >V</a
      ><a name="2124"
      > </a
      ><a name="2125" href="Stlc.html#1868" class="Function Operator"
      >]</a
      ><a name="2126" class="Symbol"
      >)</a
      ><a name="2127"
      > </a
      ><a name="2128" href="Stlc.html#1218" class="InductiveConstructor Operator"
      >&#183;&#7488;</a
      ><a name="2130"
      > </a
      ><a name="2131" class="Symbol"
      >(</a
      ><a name="2132" href="Stlc.html#2094" class="Bound"
      >M&#8242;</a
      ><a name="2134"
      > </a
      ><a name="2135" href="Stlc.html#1868" class="Function Operator"
      >[</a
      ><a name="2136"
      > </a
      ><a name="2137" href="Stlc.html#2100" class="Bound"
      >x</a
      ><a name="2138"
      > </a
      ><a name="2139" href="Stlc.html#1868" class="Function Operator"
      >:=</a
      ><a name="2141"
      > </a
      ><a name="2142" href="Stlc.html#2105" class="Bound"
      >V</a
      ><a name="2143"
      > </a
      ><a name="2144" href="Stlc.html#1868" class="Function Operator"
      >]</a
      ><a name="2145" class="Symbol"
      >)</a
      ><a name="2146"
      >
</a
      ><a name="2147" class="Symbol"
      >(</a
      ><a name="2148" href="Stlc.html#1246" class="InductiveConstructor"
      >true&#7488;</a
      ><a name="2153" class="Symbol"
      >)</a
      ><a name="2154"
      > </a
      ><a name="2155" href="Stlc.html#1868" class="Function Operator"
      >[</a
      ><a name="2156"
      > </a
      ><a name="2157" href="Stlc.html#2157" class="Bound"
      >x</a
      ><a name="2158"
      > </a
      ><a name="2159" href="Stlc.html#1868" class="Function Operator"
      >:=</a
      ><a name="2161"
      > </a
      ><a name="2162" href="Stlc.html#2162" class="Bound"
      >V</a
      ><a name="2163"
      > </a
      ><a name="2164" href="Stlc.html#1868" class="Function Operator"
      >]</a
      ><a name="2165"
      > </a
      ><a name="2166" class="Symbol"
      >=</a
      ><a name="2167"
      > </a
      ><a name="2168" href="Stlc.html#1246" class="InductiveConstructor"
      >true&#7488;</a
      ><a name="2173"
      >
</a
      ><a name="2174" class="Symbol"
      >(</a
      ><a name="2175" href="Stlc.html#1261" class="InductiveConstructor"
      >false&#7488;</a
      ><a name="2181" class="Symbol"
      >)</a
      ><a name="2182"
      > </a
      ><a name="2183" href="Stlc.html#1868" class="Function Operator"
      >[</a
      ><a name="2184"
      > </a
      ><a name="2185" href="Stlc.html#2185" class="Bound"
      >x</a
      ><a name="2186"
      > </a
      ><a name="2187" href="Stlc.html#1868" class="Function Operator"
      >:=</a
      ><a name="2189"
      > </a
      ><a name="2190" href="Stlc.html#2190" class="Bound"
      >V</a
      ><a name="2191"
      > </a
      ><a name="2192" href="Stlc.html#1868" class="Function Operator"
      >]</a
      ><a name="2193"
      > </a
      ><a name="2194" class="Symbol"
      >=</a
      ><a name="2195"
      > </a
      ><a name="2196" href="Stlc.html#1261" class="InductiveConstructor"
      >false&#7488;</a
      ><a name="2202"
      >
</a
      ><a name="2203" class="Symbol"
      >(</a
      ><a name="2204" href="Stlc.html#1277" class="InductiveConstructor Operator"
      >if&#7488;</a
      ><a name="2207"
      > </a
      ><a name="2208" href="Stlc.html#2208" class="Bound"
      >L&#8242;</a
      ><a name="2210"
      > </a
      ><a name="2211" href="Stlc.html#1277" class="InductiveConstructor Operator"
      >then</a
      ><a name="2215"
      > </a
      ><a name="2216" href="Stlc.html#2216" class="Bound"
      >M&#8242;</a
      ><a name="2218"
      > </a
      ><a name="2219" href="Stlc.html#1277" class="InductiveConstructor Operator"
      >else</a
      ><a name="2223"
      > </a
      ><a name="2224" href="Stlc.html#2224" class="Bound"
      >N&#8242;</a
      ><a name="2226" class="Symbol"
      >)</a
      ><a name="2227"
      > </a
      ><a name="2228" href="Stlc.html#1868" class="Function Operator"
      >[</a
      ><a name="2229"
      > </a
      ><a name="2230" href="Stlc.html#2230" class="Bound"
      >x</a
      ><a name="2231"
      > </a
      ><a name="2232" href="Stlc.html#1868" class="Function Operator"
      >:=</a
      ><a name="2234"
      > </a
      ><a name="2235" href="Stlc.html#2235" class="Bound"
      >V</a
      ><a name="2236"
      > </a
      ><a name="2237" href="Stlc.html#1868" class="Function Operator"
      >]</a
      ><a name="2238"
      > </a
      ><a name="2239" class="Symbol"
      >=</a
      ><a name="2240"
      > </a
      ><a name="2241" href="Stlc.html#1277" class="InductiveConstructor Operator"
      >if&#7488;</a
      ><a name="2244"
      > </a
      ><a name="2245" class="Symbol"
      >(</a
      ><a name="2246" href="Stlc.html#2208" class="Bound"
      >L&#8242;</a
      ><a name="2248"
      > </a
      ><a name="2249" href="Stlc.html#1868" class="Function Operator"
      >[</a
      ><a name="2250"
      > </a
      ><a name="2251" href="Stlc.html#2230" class="Bound"
      >x</a
      ><a name="2252"
      > </a
      ><a name="2253" href="Stlc.html#1868" class="Function Operator"
      >:=</a
      ><a name="2255"
      > </a
      ><a name="2256" href="Stlc.html#2235" class="Bound"
      >V</a
      ><a name="2257"
      > </a
      ><a name="2258" href="Stlc.html#1868" class="Function Operator"
      >]</a
      ><a name="2259" class="Symbol"
      >)</a
      ><a name="2260"
      > </a
      ><a name="2261" href="Stlc.html#1277" class="InductiveConstructor Operator"
      >then</a
      ><a name="2265"
      > </a
      ><a name="2266" class="Symbol"
      >(</a
      ><a name="2267" href="Stlc.html#2216" class="Bound"
      >M&#8242;</a
      ><a name="2269"
      > </a
      ><a name="2270" href="Stlc.html#1868" class="Function Operator"
      >[</a
      ><a name="2271"
      > </a
      ><a name="2272" href="Stlc.html#2230" class="Bound"
      >x</a
      ><a name="2273"
      > </a
      ><a name="2274" href="Stlc.html#1868" class="Function Operator"
      >:=</a
      ><a name="2276"
      > </a
      ><a name="2277" href="Stlc.html#2235" class="Bound"
      >V</a
      ><a name="2278"
      > </a
      ><a name="2279" href="Stlc.html#1868" class="Function Operator"
      >]</a
      ><a name="2280" class="Symbol"
      >)</a
      ><a name="2281"
      > </a
      ><a name="2282" href="Stlc.html#1277" class="InductiveConstructor Operator"
      >else</a
      ><a name="2286"
      > </a
      ><a name="2287" class="Symbol"
      >(</a
      ><a name="2288" href="Stlc.html#2224" class="Bound"
      >N&#8242;</a
      ><a name="2290"
      > </a
      ><a name="2291" href="Stlc.html#1868" class="Function Operator"
      >[</a
      ><a name="2292"
      > </a
      ><a name="2293" href="Stlc.html#2230" class="Bound"
      >x</a
      ><a name="2294"
      > </a
      ><a name="2295" href="Stlc.html#1868" class="Function Operator"
      >:=</a
      ><a name="2297"
      > </a
      ><a name="2298" href="Stlc.html#2235" class="Bound"
      >V</a
      ><a name="2299"
      > </a
      ><a name="2300" href="Stlc.html#1868" class="Function Operator"
      >]</a
      ><a name="2301" class="Symbol"
      >)</a
      >

</pre>

## Reduction rules

<pre class="Agda">

<a name="2348" class="Keyword"
      >data</a
      ><a name="2352"
      > </a
      ><a name="2353" href="Stlc.html#2353" class="Datatype Operator"
      >_&#10233;_</a
      ><a name="2356"
      > </a
      ><a name="2357" class="Symbol"
      >:</a
      ><a name="2358"
      > </a
      ><a name="2359" href="Stlc.html#1144" class="Datatype"
      >Term</a
      ><a name="2363"
      > </a
      ><a name="2364" class="Symbol"
      >&#8594;</a
      ><a name="2365"
      > </a
      ><a name="2366" href="Stlc.html#1144" class="Datatype"
      >Term</a
      ><a name="2370"
      > </a
      ><a name="2371" class="Symbol"
      >&#8594;</a
      ><a name="2372"
      > </a
      ><a name="2373" class="PrimitiveType"
      >Set</a
      ><a name="2376"
      > </a
      ><a name="2377" class="Keyword"
      >where</a
      ><a name="2382"
      >
  </a
      ><a name="2385" href="Stlc.html#2385" class="InductiveConstructor"
      >&#946;&#8658;</a
      ><a name="2387"
      > </a
      ><a name="2388" class="Symbol"
      >:</a
      ><a name="2389"
      > </a
      ><a name="2390" class="Symbol"
      >&#8704;</a
      ><a name="2391"
      > </a
      ><a name="2392" class="Symbol"
      >{</a
      ><a name="2393" href="Stlc.html#2393" class="Bound"
      >x</a
      ><a name="2394"
      > </a
      ><a name="2395" href="Stlc.html#2395" class="Bound"
      >A</a
      ><a name="2396"
      > </a
      ><a name="2397" href="Stlc.html#2397" class="Bound"
      >N</a
      ><a name="2398"
      > </a
      ><a name="2399" href="Stlc.html#2399" class="Bound"
      >V</a
      ><a name="2400" class="Symbol"
      >}</a
      ><a name="2401"
      > </a
      ><a name="2402" class="Symbol"
      >&#8594;</a
      ><a name="2403"
      > </a
      ><a name="2404" href="Stlc.html#1693" class="Datatype"
      >value</a
      ><a name="2409"
      > </a
      ><a name="2410" href="Stlc.html#2399" class="Bound"
      >V</a
      ><a name="2411"
      > </a
      ><a name="2412" class="Symbol"
      >&#8594;</a
      ><a name="2413"
      >
    </a
      ><a name="2418" class="Symbol"
      >((</a
      ><a name="2420" href="Stlc.html#1182" class="InductiveConstructor Operator"
      >&#955;&#7488;</a
      ><a name="2422"
      > </a
      ><a name="2423" href="Stlc.html#2393" class="Bound"
      >x</a
      ><a name="2424"
      > </a
      ><a name="2425" href="Stlc.html#1182" class="InductiveConstructor Operator"
      >&#8712;</a
      ><a name="2426"
      > </a
      ><a name="2427" href="Stlc.html#2395" class="Bound"
      >A</a
      ><a name="2428"
      > </a
      ><a name="2429" href="Stlc.html#1182" class="InductiveConstructor Operator"
      >&#8658;</a
      ><a name="2430"
      > </a
      ><a name="2431" href="Stlc.html#2397" class="Bound"
      >N</a
      ><a name="2432" class="Symbol"
      >)</a
      ><a name="2433"
      > </a
      ><a name="2434" href="Stlc.html#1218" class="InductiveConstructor Operator"
      >&#183;&#7488;</a
      ><a name="2436"
      > </a
      ><a name="2437" href="Stlc.html#2399" class="Bound"
      >V</a
      ><a name="2438" class="Symbol"
      >)</a
      ><a name="2439"
      > </a
      ><a name="2440" href="Stlc.html#2353" class="Datatype Operator"
      >&#10233;</a
      ><a name="2441"
      > </a
      ><a name="2442" class="Symbol"
      >(</a
      ><a name="2443" href="Stlc.html#2397" class="Bound"
      >N</a
      ><a name="2444"
      > </a
      ><a name="2445" href="Stlc.html#1868" class="Function Operator"
      >[</a
      ><a name="2446"
      > </a
      ><a name="2447" href="Stlc.html#2393" class="Bound"
      >x</a
      ><a name="2448"
      > </a
      ><a name="2449" href="Stlc.html#1868" class="Function Operator"
      >:=</a
      ><a name="2451"
      > </a
      ><a name="2452" href="Stlc.html#2399" class="Bound"
      >V</a
      ><a name="2453"
      > </a
      ><a name="2454" href="Stlc.html#1868" class="Function Operator"
      >]</a
      ><a name="2455" class="Symbol"
      >)</a
      ><a name="2456"
      >
  </a
      ><a name="2459" href="Stlc.html#2459" class="InductiveConstructor"
      >&#947;&#8658;&#8321;</a
      ><a name="2462"
      > </a
      ><a name="2463" class="Symbol"
      >:</a
      ><a name="2464"
      > </a
      ><a name="2465" class="Symbol"
      >&#8704;</a
      ><a name="2466"
      > </a
      ><a name="2467" class="Symbol"
      >{</a
      ><a name="2468" href="Stlc.html#2468" class="Bound"
      >L</a
      ><a name="2469"
      > </a
      ><a name="2470" href="Stlc.html#2470" class="Bound"
      >L'</a
      ><a name="2472"
      > </a
      ><a name="2473" href="Stlc.html#2473" class="Bound"
      >M</a
      ><a name="2474" class="Symbol"
      >}</a
      ><a name="2475"
      > </a
      ><a name="2476" class="Symbol"
      >&#8594;</a
      ><a name="2477"
      >
    </a
      ><a name="2482" href="Stlc.html#2468" class="Bound"
      >L</a
      ><a name="2483"
      > </a
      ><a name="2484" href="Stlc.html#2353" class="Datatype Operator"
      >&#10233;</a
      ><a name="2485"
      > </a
      ><a name="2486" href="Stlc.html#2470" class="Bound"
      >L'</a
      ><a name="2488"
      > </a
      ><a name="2489" class="Symbol"
      >&#8594;</a
      ><a name="2490"
      >
    </a
      ><a name="2495" class="Symbol"
      >(</a
      ><a name="2496" href="Stlc.html#2468" class="Bound"
      >L</a
      ><a name="2497"
      > </a
      ><a name="2498" href="Stlc.html#1218" class="InductiveConstructor Operator"
      >&#183;&#7488;</a
      ><a name="2500"
      > </a
      ><a name="2501" href="Stlc.html#2473" class="Bound"
      >M</a
      ><a name="2502" class="Symbol"
      >)</a
      ><a name="2503"
      > </a
      ><a name="2504" href="Stlc.html#2353" class="Datatype Operator"
      >&#10233;</a
      ><a name="2505"
      > </a
      ><a name="2506" class="Symbol"
      >(</a
      ><a name="2507" href="Stlc.html#2470" class="Bound"
      >L'</a
      ><a name="2509"
      > </a
      ><a name="2510" href="Stlc.html#1218" class="InductiveConstructor Operator"
      >&#183;&#7488;</a
      ><a name="2512"
      > </a
      ><a name="2513" href="Stlc.html#2473" class="Bound"
      >M</a
      ><a name="2514" class="Symbol"
      >)</a
      ><a name="2515"
      >
  </a
      ><a name="2518" href="Stlc.html#2518" class="InductiveConstructor"
      >&#947;&#8658;&#8322;</a
      ><a name="2521"
      > </a
      ><a name="2522" class="Symbol"
      >:</a
      ><a name="2523"
      > </a
      ><a name="2524" class="Symbol"
      >&#8704;</a
      ><a name="2525"
      > </a
      ><a name="2526" class="Symbol"
      >{</a
      ><a name="2527" href="Stlc.html#2527" class="Bound"
      >V</a
      ><a name="2528"
      > </a
      ><a name="2529" href="Stlc.html#2529" class="Bound"
      >M</a
      ><a name="2530"
      > </a
      ><a name="2531" href="Stlc.html#2531" class="Bound"
      >M'</a
      ><a name="2533" class="Symbol"
      >}</a
      ><a name="2534"
      > </a
      ><a name="2535" class="Symbol"
      >&#8594;</a
      ><a name="2536"
      >
    </a
      ><a name="2541" href="Stlc.html#1693" class="Datatype"
      >value</a
      ><a name="2546"
      > </a
      ><a name="2547" href="Stlc.html#2527" class="Bound"
      >V</a
      ><a name="2548"
      > </a
      ><a name="2549" class="Symbol"
      >&#8594;</a
      ><a name="2550"
      >
    </a
      ><a name="2555" href="Stlc.html#2529" class="Bound"
      >M</a
      ><a name="2556"
      > </a
      ><a name="2557" href="Stlc.html#2353" class="Datatype Operator"
      >&#10233;</a
      ><a name="2558"
      > </a
      ><a name="2559" href="Stlc.html#2531" class="Bound"
      >M'</a
      ><a name="2561"
      > </a
      ><a name="2562" class="Symbol"
      >&#8594;</a
      ><a name="2563"
      >
    </a
      ><a name="2568" class="Symbol"
      >(</a
      ><a name="2569" href="Stlc.html#2527" class="Bound"
      >V</a
      ><a name="2570"
      > </a
      ><a name="2571" href="Stlc.html#1218" class="InductiveConstructor Operator"
      >&#183;&#7488;</a
      ><a name="2573"
      > </a
      ><a name="2574" href="Stlc.html#2529" class="Bound"
      >M</a
      ><a name="2575" class="Symbol"
      >)</a
      ><a name="2576"
      > </a
      ><a name="2577" href="Stlc.html#2353" class="Datatype Operator"
      >&#10233;</a
      ><a name="2578"
      > </a
      ><a name="2579" class="Symbol"
      >(</a
      ><a name="2580" href="Stlc.html#2527" class="Bound"
      >V</a
      ><a name="2581"
      > </a
      ><a name="2582" href="Stlc.html#1218" class="InductiveConstructor Operator"
      >&#183;&#7488;</a
      ><a name="2584"
      > </a
      ><a name="2585" href="Stlc.html#2531" class="Bound"
      >M'</a
      ><a name="2587" class="Symbol"
      >)</a
      ><a name="2588"
      >
  </a
      ><a name="2591" href="Stlc.html#2591" class="InductiveConstructor"
      >&#946;&#120121;&#8321;</a
      ><a name="2594"
      > </a
      ><a name="2595" class="Symbol"
      >:</a
      ><a name="2596"
      > </a
      ><a name="2597" class="Symbol"
      >&#8704;</a
      ><a name="2598"
      > </a
      ><a name="2599" class="Symbol"
      >{</a
      ><a name="2600" href="Stlc.html#2600" class="Bound"
      >M</a
      ><a name="2601"
      > </a
      ><a name="2602" href="Stlc.html#2602" class="Bound"
      >N</a
      ><a name="2603" class="Symbol"
      >}</a
      ><a name="2604"
      > </a
      ><a name="2605" class="Symbol"
      >&#8594;</a
      ><a name="2606"
      >
    </a
      ><a name="2611" class="Symbol"
      >(</a
      ><a name="2612" href="Stlc.html#1277" class="InductiveConstructor Operator"
      >if&#7488;</a
      ><a name="2615"
      > </a
      ><a name="2616" href="Stlc.html#1246" class="InductiveConstructor"
      >true&#7488;</a
      ><a name="2621"
      > </a
      ><a name="2622" href="Stlc.html#1277" class="InductiveConstructor Operator"
      >then</a
      ><a name="2626"
      > </a
      ><a name="2627" href="Stlc.html#2600" class="Bound"
      >M</a
      ><a name="2628"
      > </a
      ><a name="2629" href="Stlc.html#1277" class="InductiveConstructor Operator"
      >else</a
      ><a name="2633"
      > </a
      ><a name="2634" href="Stlc.html#2602" class="Bound"
      >N</a
      ><a name="2635" class="Symbol"
      >)</a
      ><a name="2636"
      > </a
      ><a name="2637" href="Stlc.html#2353" class="Datatype Operator"
      >&#10233;</a
      ><a name="2638"
      > </a
      ><a name="2639" href="Stlc.html#2600" class="Bound"
      >M</a
      ><a name="2640"
      >
  </a
      ><a name="2643" href="Stlc.html#2643" class="InductiveConstructor"
      >&#946;&#120121;&#8322;</a
      ><a name="2646"
      > </a
      ><a name="2647" class="Symbol"
      >:</a
      ><a name="2648"
      > </a
      ><a name="2649" class="Symbol"
      >&#8704;</a
      ><a name="2650"
      > </a
      ><a name="2651" class="Symbol"
      >{</a
      ><a name="2652" href="Stlc.html#2652" class="Bound"
      >M</a
      ><a name="2653"
      > </a
      ><a name="2654" href="Stlc.html#2654" class="Bound"
      >N</a
      ><a name="2655" class="Symbol"
      >}</a
      ><a name="2656"
      > </a
      ><a name="2657" class="Symbol"
      >&#8594;</a
      ><a name="2658"
      >
    </a
      ><a name="2663" class="Symbol"
      >(</a
      ><a name="2664" href="Stlc.html#1277" class="InductiveConstructor Operator"
      >if&#7488;</a
      ><a name="2667"
      > </a
      ><a name="2668" href="Stlc.html#1261" class="InductiveConstructor"
      >false&#7488;</a
      ><a name="2674"
      > </a
      ><a name="2675" href="Stlc.html#1277" class="InductiveConstructor Operator"
      >then</a
      ><a name="2679"
      > </a
      ><a name="2680" href="Stlc.html#2652" class="Bound"
      >M</a
      ><a name="2681"
      > </a
      ><a name="2682" href="Stlc.html#1277" class="InductiveConstructor Operator"
      >else</a
      ><a name="2686"
      > </a
      ><a name="2687" href="Stlc.html#2654" class="Bound"
      >N</a
      ><a name="2688" class="Symbol"
      >)</a
      ><a name="2689"
      > </a
      ><a name="2690" href="Stlc.html#2353" class="Datatype Operator"
      >&#10233;</a
      ><a name="2691"
      > </a
      ><a name="2692" href="Stlc.html#2654" class="Bound"
      >N</a
      ><a name="2693"
      >
  </a
      ><a name="2696" href="Stlc.html#2696" class="InductiveConstructor"
      >&#947;&#120121;</a
      ><a name="2698"
      > </a
      ><a name="2699" class="Symbol"
      >:</a
      ><a name="2700"
      > </a
      ><a name="2701" class="Symbol"
      >&#8704;</a
      ><a name="2702"
      > </a
      ><a name="2703" class="Symbol"
      >{</a
      ><a name="2704" href="Stlc.html#2704" class="Bound"
      >L</a
      ><a name="2705"
      > </a
      ><a name="2706" href="Stlc.html#2706" class="Bound"
      >L'</a
      ><a name="2708"
      > </a
      ><a name="2709" href="Stlc.html#2709" class="Bound"
      >M</a
      ><a name="2710"
      > </a
      ><a name="2711" href="Stlc.html#2711" class="Bound"
      >N</a
      ><a name="2712" class="Symbol"
      >}</a
      ><a name="2713"
      > </a
      ><a name="2714" class="Symbol"
      >&#8594;</a
      ><a name="2715"
      >
    </a
      ><a name="2720" href="Stlc.html#2704" class="Bound"
      >L</a
      ><a name="2721"
      > </a
      ><a name="2722" href="Stlc.html#2353" class="Datatype Operator"
      >&#10233;</a
      ><a name="2723"
      > </a
      ><a name="2724" href="Stlc.html#2706" class="Bound"
      >L'</a
      ><a name="2726"
      > </a
      ><a name="2727" class="Symbol"
      >&#8594;</a
      ><a name="2728"
      >    
    </a
      ><a name="2737" class="Symbol"
      >(</a
      ><a name="2738" href="Stlc.html#1277" class="InductiveConstructor Operator"
      >if&#7488;</a
      ><a name="2741"
      > </a
      ><a name="2742" href="Stlc.html#2704" class="Bound"
      >L</a
      ><a name="2743"
      > </a
      ><a name="2744" href="Stlc.html#1277" class="InductiveConstructor Operator"
      >then</a
      ><a name="2748"
      > </a
      ><a name="2749" href="Stlc.html#2709" class="Bound"
      >M</a
      ><a name="2750"
      > </a
      ><a name="2751" href="Stlc.html#1277" class="InductiveConstructor Operator"
      >else</a
      ><a name="2755"
      > </a
      ><a name="2756" href="Stlc.html#2711" class="Bound"
      >N</a
      ><a name="2757" class="Symbol"
      >)</a
      ><a name="2758"
      > </a
      ><a name="2759" href="Stlc.html#2353" class="Datatype Operator"
      >&#10233;</a
      ><a name="2760"
      > </a
      ><a name="2761" class="Symbol"
      >(</a
      ><a name="2762" href="Stlc.html#1277" class="InductiveConstructor Operator"
      >if&#7488;</a
      ><a name="2765"
      > </a
      ><a name="2766" href="Stlc.html#2706" class="Bound"
      >L'</a
      ><a name="2768"
      > </a
      ><a name="2769" href="Stlc.html#1277" class="InductiveConstructor Operator"
      >then</a
      ><a name="2773"
      > </a
      ><a name="2774" href="Stlc.html#2709" class="Bound"
      >M</a
      ><a name="2775"
      > </a
      ><a name="2776" href="Stlc.html#1277" class="InductiveConstructor Operator"
      >else</a
      ><a name="2780"
      > </a
      ><a name="2781" href="Stlc.html#2711" class="Bound"
      >N</a
      ><a name="2782" class="Symbol"
      >)</a
      >

</pre>

## Reflexive and transitive closure of a relation

<pre class="Agda">

<a name="2860" href="Stlc.html#2860" class="Function"
      >Rel</a
      ><a name="2863"
      > </a
      ><a name="2864" class="Symbol"
      >:</a
      ><a name="2865"
      > </a
      ><a name="2866" class="PrimitiveType"
      >Set</a
      ><a name="2869"
      > </a
      ><a name="2870" class="Symbol"
      >&#8594;</a
      ><a name="2871"
      > </a
      ><a name="2872" class="PrimitiveType"
      >Set&#8321;</a
      ><a name="2876"
      >
</a
      ><a name="2877" href="Stlc.html#2860" class="Function"
      >Rel</a
      ><a name="2880"
      > </a
      ><a name="2881" href="Stlc.html#2881" class="Bound"
      >A</a
      ><a name="2882"
      > </a
      ><a name="2883" class="Symbol"
      >=</a
      ><a name="2884"
      > </a
      ><a name="2885" href="Stlc.html#2881" class="Bound"
      >A</a
      ><a name="2886"
      > </a
      ><a name="2887" class="Symbol"
      >&#8594;</a
      ><a name="2888"
      > </a
      ><a name="2889" href="Stlc.html#2881" class="Bound"
      >A</a
      ><a name="2890"
      > </a
      ><a name="2891" class="Symbol"
      >&#8594;</a
      ><a name="2892"
      > </a
      ><a name="2893" class="PrimitiveType"
      >Set</a
      ><a name="2896"
      >

</a
      ><a name="2898" class="Keyword"
      >infixl</a
      ><a name="2904"
      > </a
      ><a name="2905" class="Number"
      >100</a
      ><a name="2908"
      > </a
      ><a name="2909" href="Stlc.html#3030" class="InductiveConstructor Operator"
      >_&gt;&gt;_</a
      ><a name="2913"
      >

</a
      ><a name="2915" class="Keyword"
      >data</a
      ><a name="2919"
      > </a
      ><a name="2920" href="Stlc.html#2920" class="Datatype Operator"
      >_*</a
      ><a name="2922"
      > </a
      ><a name="2923" class="Symbol"
      >{</a
      ><a name="2924" href="Stlc.html#2924" class="Bound"
      >A</a
      ><a name="2925"
      > </a
      ><a name="2926" class="Symbol"
      >:</a
      ><a name="2927"
      > </a
      ><a name="2928" class="PrimitiveType"
      >Set</a
      ><a name="2931" class="Symbol"
      >}</a
      ><a name="2932"
      > </a
      ><a name="2933" class="Symbol"
      >(</a
      ><a name="2934" href="Stlc.html#2934" class="Bound"
      >R</a
      ><a name="2935"
      > </a
      ><a name="2936" class="Symbol"
      >:</a
      ><a name="2937"
      > </a
      ><a name="2938" href="Stlc.html#2860" class="Function"
      >Rel</a
      ><a name="2941"
      > </a
      ><a name="2942" href="Stlc.html#2924" class="Bound"
      >A</a
      ><a name="2943" class="Symbol"
      >)</a
      ><a name="2944"
      > </a
      ><a name="2945" class="Symbol"
      >:</a
      ><a name="2946"
      > </a
      ><a name="2947" href="Stlc.html#2860" class="Function"
      >Rel</a
      ><a name="2950"
      > </a
      ><a name="2951" href="Stlc.html#2924" class="Bound"
      >A</a
      ><a name="2952"
      > </a
      ><a name="2953" class="Keyword"
      >where</a
      ><a name="2958"
      >
  </a
      ><a name="2961" href="Stlc.html#2961" class="InductiveConstructor"
      >&#10216;&#10217;</a
      ><a name="2963"
      > </a
      ><a name="2964" class="Symbol"
      >:</a
      ><a name="2965"
      > </a
      ><a name="2966" class="Symbol"
      >&#8704;</a
      ><a name="2967"
      > </a
      ><a name="2968" class="Symbol"
      >{</a
      ><a name="2969" href="Stlc.html#2969" class="Bound"
      >x</a
      ><a name="2970"
      > </a
      ><a name="2971" class="Symbol"
      >:</a
      ><a name="2972"
      > </a
      ><a name="2973" href="Stlc.html#2924" class="Bound"
      >A</a
      ><a name="2974" class="Symbol"
      >}</a
      ><a name="2975"
      > </a
      ><a name="2976" class="Symbol"
      >&#8594;</a
      ><a name="2977"
      > </a
      ><a name="2978" class="Symbol"
      >(</a
      ><a name="2979" href="Stlc.html#2934" class="Bound"
      >R</a
      ><a name="2980"
      > </a
      ><a name="2981" href="Stlc.html#2920" class="Datatype Operator"
      >*</a
      ><a name="2982" class="Symbol"
      >)</a
      ><a name="2983"
      > </a
      ><a name="2984" href="Stlc.html#2969" class="Bound"
      >x</a
      ><a name="2985"
      > </a
      ><a name="2986" href="Stlc.html#2969" class="Bound"
      >x</a
      ><a name="2987"
      >
  </a
      ><a name="2990" href="Stlc.html#2990" class="InductiveConstructor Operator"
      >&#10216;_&#10217;</a
      ><a name="2993"
      > </a
      ><a name="2994" class="Symbol"
      >:</a
      ><a name="2995"
      > </a
      ><a name="2996" class="Symbol"
      >&#8704;</a
      ><a name="2997"
      > </a
      ><a name="2998" class="Symbol"
      >{</a
      ><a name="2999" href="Stlc.html#2999" class="Bound"
      >x</a
      ><a name="3000"
      > </a
      ><a name="3001" href="Stlc.html#3001" class="Bound"
      >y</a
      ><a name="3002"
      > </a
      ><a name="3003" class="Symbol"
      >:</a
      ><a name="3004"
      > </a
      ><a name="3005" href="Stlc.html#2924" class="Bound"
      >A</a
      ><a name="3006" class="Symbol"
      >}</a
      ><a name="3007"
      > </a
      ><a name="3008" class="Symbol"
      >&#8594;</a
      ><a name="3009"
      > </a
      ><a name="3010" href="Stlc.html#2934" class="Bound"
      >R</a
      ><a name="3011"
      > </a
      ><a name="3012" href="Stlc.html#2999" class="Bound"
      >x</a
      ><a name="3013"
      > </a
      ><a name="3014" href="Stlc.html#3001" class="Bound"
      >y</a
      ><a name="3015"
      > </a
      ><a name="3016" class="Symbol"
      >&#8594;</a
      ><a name="3017"
      > </a
      ><a name="3018" class="Symbol"
      >(</a
      ><a name="3019" href="Stlc.html#2934" class="Bound"
      >R</a
      ><a name="3020"
      > </a
      ><a name="3021" href="Stlc.html#2920" class="Datatype Operator"
      >*</a
      ><a name="3022" class="Symbol"
      >)</a
      ><a name="3023"
      > </a
      ><a name="3024" href="Stlc.html#2999" class="Bound"
      >x</a
      ><a name="3025"
      > </a
      ><a name="3026" href="Stlc.html#3001" class="Bound"
      >y</a
      ><a name="3027"
      >
  </a
      ><a name="3030" href="Stlc.html#3030" class="InductiveConstructor Operator"
      >_&gt;&gt;_</a
      ><a name="3034"
      > </a
      ><a name="3035" class="Symbol"
      >:</a
      ><a name="3036"
      > </a
      ><a name="3037" class="Symbol"
      >&#8704;</a
      ><a name="3038"
      > </a
      ><a name="3039" class="Symbol"
      >{</a
      ><a name="3040" href="Stlc.html#3040" class="Bound"
      >x</a
      ><a name="3041"
      > </a
      ><a name="3042" href="Stlc.html#3042" class="Bound"
      >y</a
      ><a name="3043"
      > </a
      ><a name="3044" href="Stlc.html#3044" class="Bound"
      >z</a
      ><a name="3045"
      > </a
      ><a name="3046" class="Symbol"
      >:</a
      ><a name="3047"
      > </a
      ><a name="3048" href="Stlc.html#2924" class="Bound"
      >A</a
      ><a name="3049" class="Symbol"
      >}</a
      ><a name="3050"
      > </a
      ><a name="3051" class="Symbol"
      >&#8594;</a
      ><a name="3052"
      > </a
      ><a name="3053" class="Symbol"
      >(</a
      ><a name="3054" href="Stlc.html#2934" class="Bound"
      >R</a
      ><a name="3055"
      > </a
      ><a name="3056" href="Stlc.html#2920" class="Datatype Operator"
      >*</a
      ><a name="3057" class="Symbol"
      >)</a
      ><a name="3058"
      > </a
      ><a name="3059" href="Stlc.html#3040" class="Bound"
      >x</a
      ><a name="3060"
      > </a
      ><a name="3061" href="Stlc.html#3042" class="Bound"
      >y</a
      ><a name="3062"
      > </a
      ><a name="3063" class="Symbol"
      >&#8594;</a
      ><a name="3064"
      > </a
      ><a name="3065" class="Symbol"
      >(</a
      ><a name="3066" href="Stlc.html#2934" class="Bound"
      >R</a
      ><a name="3067"
      > </a
      ><a name="3068" href="Stlc.html#2920" class="Datatype Operator"
      >*</a
      ><a name="3069" class="Symbol"
      >)</a
      ><a name="3070"
      > </a
      ><a name="3071" href="Stlc.html#3042" class="Bound"
      >y</a
      ><a name="3072"
      > </a
      ><a name="3073" href="Stlc.html#3044" class="Bound"
      >z</a
      ><a name="3074"
      > </a
      ><a name="3075" class="Symbol"
      >&#8594;</a
      ><a name="3076"
      > </a
      ><a name="3077" class="Symbol"
      >(</a
      ><a name="3078" href="Stlc.html#2934" class="Bound"
      >R</a
      ><a name="3079"
      > </a
      ><a name="3080" href="Stlc.html#2920" class="Datatype Operator"
      >*</a
      ><a name="3081" class="Symbol"
      >)</a
      ><a name="3082"
      > </a
      ><a name="3083" href="Stlc.html#3040" class="Bound"
      >x</a
      ><a name="3084"
      > </a
      ><a name="3085" href="Stlc.html#3044" class="Bound"
      >z</a
      >

</pre>

<pre class="Agda">

<a name="3112" class="Keyword"
      >infix</a
      ><a name="3117"
      > </a
      ><a name="3118" class="Number"
      >80</a
      ><a name="3120"
      > </a
      ><a name="3121" href="Stlc.html#3127" class="Function Operator"
      >_&#10233;*_</a
      ><a name="3125"
      >

</a
      ><a name="3127" href="Stlc.html#3127" class="Function Operator"
      >_&#10233;*_</a
      ><a name="3131"
      > </a
      ><a name="3132" class="Symbol"
      >:</a
      ><a name="3133"
      > </a
      ><a name="3134" href="Stlc.html#1144" class="Datatype"
      >Term</a
      ><a name="3138"
      > </a
      ><a name="3139" class="Symbol"
      >&#8594;</a
      ><a name="3140"
      > </a
      ><a name="3141" href="Stlc.html#1144" class="Datatype"
      >Term</a
      ><a name="3145"
      > </a
      ><a name="3146" class="Symbol"
      >&#8594;</a
      ><a name="3147"
      > </a
      ><a name="3148" class="PrimitiveType"
      >Set</a
      ><a name="3151"
      >
</a
      ><a name="3152" href="Stlc.html#3127" class="Function Operator"
      >_&#10233;*_</a
      ><a name="3156"
      > </a
      ><a name="3157" class="Symbol"
      >=</a
      ><a name="3158"
      > </a
      ><a name="3159" class="Symbol"
      >(</a
      ><a name="3160" href="Stlc.html#2353" class="Datatype Operator"
      >_&#10233;_</a
      ><a name="3163" class="Symbol"
      >)</a
      ><a name="3164"
      > </a
      ><a name="3165" href="Stlc.html#2920" class="Datatype Operator"
      >*</a
      >

</pre>

<pre class="Agda">

<a name="3192" href="Stlc.html#3192" class="Function"
      >&#10233;*-Preorder</a
      ><a name="3203"
      > </a
      ><a name="3204" class="Symbol"
      >:</a
      ><a name="3205"
      > </a
      ><a name="3206" href="https://agda.github.io/agda-stdlib/Relation.Binary.html#1470" class="Record"
      >Preorder</a
      ><a name="3214"
      > </a
      ><a name="3215" class="Symbol"
      >_</a
      ><a name="3216"
      > </a
      ><a name="3217" class="Symbol"
      >_</a
      ><a name="3218"
      > </a
      ><a name="3219" class="Symbol"
      >_</a
      ><a name="3220"
      >
</a
      ><a name="3221" href="Stlc.html#3192" class="Function"
      >&#10233;*-Preorder</a
      ><a name="3232"
      > </a
      ><a name="3233" class="Symbol"
      >=</a
      ><a name="3234"
      > </a
      ><a name="3235" class="Keyword"
      >record</a
      ><a name="3241"
      >
  </a
      ><a name="3244" class="Symbol"
      >{</a
      ><a name="3245"
      > </a
      ><a name="3246" class="Field"
      >Carrier</a
      ><a name="3253"
      >    </a
      ><a name="3257" class="Symbol"
      >=</a
      ><a name="3258"
      > </a
      ><a name="3259" href="Stlc.html#1144" class="Datatype"
      >Term</a
      ><a name="3263"
      >
  </a
      ><a name="3266" class="Symbol"
      >;</a
      ><a name="3267"
      > </a
      ><a name="3268" class="Field Operator"
      >_&#8776;_</a
      ><a name="3271"
      >        </a
      ><a name="3279" class="Symbol"
      >=</a
      ><a name="3280"
      > </a
      ><a name="3281" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >_&#8801;_</a
      ><a name="3284"
      >
  </a
      ><a name="3287" class="Symbol"
      >;</a
      ><a name="3288"
      > </a
      ><a name="3289" class="Field Operator"
      >_&#8764;_</a
      ><a name="3292"
      >        </a
      ><a name="3300" class="Symbol"
      >=</a
      ><a name="3301"
      > </a
      ><a name="3302" href="Stlc.html#3127" class="Function Operator"
      >_&#10233;*_</a
      ><a name="3306"
      >
  </a
      ><a name="3309" class="Symbol"
      >;</a
      ><a name="3310"
      > </a
      ><a name="3311" class="Field"
      >isPreorder</a
      ><a name="3321"
      > </a
      ><a name="3322" class="Symbol"
      >=</a
      ><a name="3323"
      > </a
      ><a name="3324" class="Keyword"
      >record</a
      ><a name="3330"
      >
    </a
      ><a name="3335" class="Symbol"
      >{</a
      ><a name="3336"
      > </a
      ><a name="3337" class="Field"
      >isEquivalence</a
      ><a name="3350"
      > </a
      ><a name="3351" class="Symbol"
      >=</a
      ><a name="3352"
      > </a
      ><a name="3353" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.Core.html#879" class="Function"
      >P.isEquivalence</a
      ><a name="3368"
      >
    </a
      ><a name="3373" class="Symbol"
      >;</a
      ><a name="3374"
      > </a
      ><a name="3375" class="Field"
      >reflexive</a
      ><a name="3384"
      >     </a
      ><a name="3389" class="Symbol"
      >=</a
      ><a name="3390"
      > </a
      ><a name="3391" class="Symbol"
      >&#955;</a
      ><a name="3392"
      > </a
      ><a name="3393" class="Symbol"
      >{</a
      ><a name="3394" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="3398"
      > </a
      ><a name="3399" class="Symbol"
      >&#8594;</a
      ><a name="3400"
      > </a
      ><a name="3401" href="Stlc.html#2961" class="InductiveConstructor"
      >&#10216;&#10217;</a
      ><a name="3403" class="Symbol"
      >}</a
      ><a name="3404"
      >
    </a
      ><a name="3409" class="Symbol"
      >;</a
      ><a name="3410"
      > </a
      ><a name="3411" class="Field"
      >trans</a
      ><a name="3416"
      >         </a
      ><a name="3425" class="Symbol"
      >=</a
      ><a name="3426"
      > </a
      ><a name="3427" href="Stlc.html#3030" class="InductiveConstructor Operator"
      >_&gt;&gt;_</a
      ><a name="3431"
      >
    </a
      ><a name="3436" class="Symbol"
      >}</a
      ><a name="3437"
      >
  </a
      ><a name="3440" class="Symbol"
      >}</a
      ><a name="3441"
      >

</a
      ><a name="3443" class="Keyword"
      >open</a
      ><a name="3447"
      > </a
      ><a name="3448" href="https://agda.github.io/agda-stdlib/Relation.Binary.PreorderReasoning.html#1" class="Module"
      >PreorderReasoning</a
      ><a name="3465"
      > </a
      ><a name="3466" href="Stlc.html#3192" class="Function"
      >&#10233;*-Preorder</a
      ><a name="3477"
      >
     </a
      ><a name="3483" class="Keyword"
      >using</a
      ><a name="3488"
      > </a
      ><a name="3489" class="Symbol"
      >(</a
      ><a name="3490"
      >begin_</a
      ><a name="3496" class="Symbol"
      >;</a
      ><a name="3497"
      > _&#8718;</a
      ><a name="3500" class="Symbol"
      >)</a
      ><a name="3501"
      > </a
      ><a name="3502" class="Keyword"
      >renaming</a
      ><a name="3510"
      > </a
      ><a name="3511" class="Symbol"
      >(</a
      ><a name="3512"
      >_&#8776;&#10216;_&#10217;_ </a
      ><a name="3519" class="Symbol"
      >to</a
      ><a name="3521"
      > _&#8801;&#10216;_&#10217;_</a
      ><a name="3528" class="Symbol"
      >;</a
      ><a name="3529"
      > _&#8764;&#10216;_&#10217;_ </a
      ><a name="3537" class="Symbol"
      >to</a
      ><a name="3539"
      > _&#10233;*&#10216;_&#10217;_</a
      ><a name="3547" class="Symbol"
      >)</a
      >

</pre>

Example evaluation.

<pre class="Agda">

<a name="3595" href="Stlc.html#3595" class="Function"
      >example&#8320;&#8242;</a
      ><a name="3604"
      > </a
      ><a name="3605" class="Symbol"
      >:</a
      ><a name="3606"
      > </a
      ><a name="3607" href="Stlc.html#1431" class="Function"
      >not[&#120121;]</a
      ><a name="3613"
      > </a
      ><a name="3614" href="Stlc.html#1218" class="InductiveConstructor Operator"
      >&#183;&#7488;</a
      ><a name="3616"
      > </a
      ><a name="3617" href="Stlc.html#1246" class="InductiveConstructor"
      >true&#7488;</a
      ><a name="3622"
      > </a
      ><a name="3623" href="Stlc.html#3127" class="Function Operator"
      >&#10233;*</a
      ><a name="3625"
      > </a
      ><a name="3626" href="Stlc.html#1261" class="InductiveConstructor"
      >false&#7488;</a
      ><a name="3632"
      >
</a
      ><a name="3633" href="Stlc.html#3595" class="Function"
      >example&#8320;&#8242;</a
      ><a name="3642"
      > </a
      ><a name="3643" class="Symbol"
      >=</a
      ><a name="3644"
      >
  </a
      ><a name="3647" href="https://agda.github.io/agda-stdlib/Relation.Binary.PreorderReasoning.html#1154" class="Function Operator"
      >begin</a
      ><a name="3652"
      >
    </a
      ><a name="3657" href="Stlc.html#1431" class="Function"
      >not[&#120121;]</a
      ><a name="3663"
      > </a
      ><a name="3664" href="Stlc.html#1218" class="InductiveConstructor Operator"
      >&#183;&#7488;</a
      ><a name="3666"
      > </a
      ><a name="3667" href="Stlc.html#1246" class="InductiveConstructor"
      >true&#7488;</a
      ><a name="3672"
      >
  </a
      ><a name="3675" href="https://agda.github.io/agda-stdlib/Relation.Binary.PreorderReasoning.html#1220" class="Function Operator"
      >&#10233;*&#10216;</a
      ><a name="3678"
      > </a
      ><a name="3679" href="Stlc.html#2990" class="InductiveConstructor Operator"
      >&#10216;</a
      ><a name="3680"
      > </a
      ><a name="3681" href="Stlc.html#2385" class="InductiveConstructor"
      >&#946;&#8658;</a
      ><a name="3683"
      > </a
      ><a name="3684" href="Stlc.html#1766" class="InductiveConstructor"
      >value-true&#7488;</a
      ><a name="3695"
      > </a
      ><a name="3696" href="Stlc.html#2990" class="InductiveConstructor Operator"
      >&#10217;</a
      ><a name="3697"
      > </a
      ><a name="3698" href="https://agda.github.io/agda-stdlib/Relation.Binary.PreorderReasoning.html#1220" class="Function Operator"
      >&#10217;</a
      ><a name="3699"
      >
    </a
      ><a name="3704" href="Stlc.html#1277" class="InductiveConstructor Operator"
      >if&#7488;</a
      ><a name="3707"
      > </a
      ><a name="3708" href="Stlc.html#1246" class="InductiveConstructor"
      >true&#7488;</a
      ><a name="3713"
      > </a
      ><a name="3714" href="Stlc.html#1277" class="InductiveConstructor Operator"
      >then</a
      ><a name="3718"
      > </a
      ><a name="3719" href="Stlc.html#1261" class="InductiveConstructor"
      >false&#7488;</a
      ><a name="3725"
      > </a
      ><a name="3726" href="Stlc.html#1277" class="InductiveConstructor Operator"
      >else</a
      ><a name="3730"
      > </a
      ><a name="3731" href="Stlc.html#1246" class="InductiveConstructor"
      >true&#7488;</a
      ><a name="3736"
      >
  </a
      ><a name="3739" href="https://agda.github.io/agda-stdlib/Relation.Binary.PreorderReasoning.html#1220" class="Function Operator"
      >&#10233;*&#10216;</a
      ><a name="3742"
      > </a
      ><a name="3743" href="Stlc.html#2990" class="InductiveConstructor Operator"
      >&#10216;</a
      ><a name="3744"
      > </a
      ><a name="3745" href="Stlc.html#2591" class="InductiveConstructor"
      >&#946;&#120121;&#8321;</a
      ><a name="3748"
      > </a
      ><a name="3749" href="Stlc.html#2990" class="InductiveConstructor Operator"
      >&#10217;</a
      ><a name="3750"
      > </a
      ><a name="3751" href="https://agda.github.io/agda-stdlib/Relation.Binary.PreorderReasoning.html#1220" class="Function Operator"
      >&#10217;</a
      ><a name="3752"
      >
    </a
      ><a name="3757" href="Stlc.html#1261" class="InductiveConstructor"
      >false&#7488;</a
      ><a name="3763"
      >
  </a
      ><a name="3766" href="https://agda.github.io/agda-stdlib/Relation.Binary.PreorderReasoning.html#1519" class="Function Operator"
      >&#8718;</a
      ><a name="3767"
      >

</a
      ><a name="3769" href="Stlc.html#3769" class="Function"
      >example&#8320;</a
      ><a name="3777"
      > </a
      ><a name="3778" class="Symbol"
      >:</a
      ><a name="3779"
      > </a
      ><a name="3780" class="Symbol"
      >(</a
      ><a name="3781" href="Stlc.html#1431" class="Function"
      >not[&#120121;]</a
      ><a name="3787"
      > </a
      ><a name="3788" href="Stlc.html#1218" class="InductiveConstructor Operator"
      >&#183;&#7488;</a
      ><a name="3790"
      > </a
      ><a name="3791" href="Stlc.html#1246" class="InductiveConstructor"
      >true&#7488;</a
      ><a name="3796" class="Symbol"
      >)</a
      ><a name="3797"
      > </a
      ><a name="3798" href="Stlc.html#3127" class="Function Operator"
      >&#10233;*</a
      ><a name="3800"
      > </a
      ><a name="3801" href="Stlc.html#1261" class="InductiveConstructor"
      >false&#7488;</a
      ><a name="3807"
      >
</a
      ><a name="3808" href="Stlc.html#3769" class="Function"
      >example&#8320;</a
      ><a name="3816"
      > </a
      ><a name="3817" class="Symbol"
      >=</a
      ><a name="3818"
      > </a
      ><a name="3819" href="Stlc.html#2990" class="InductiveConstructor Operator"
      >&#10216;</a
      ><a name="3820"
      > </a
      ><a name="3821" href="Stlc.html#3951" class="Function"
      >step&#8320;</a
      ><a name="3826"
      > </a
      ><a name="3827" href="Stlc.html#2990" class="InductiveConstructor Operator"
      >&#10217;</a
      ><a name="3828"
      > </a
      ><a name="3829" href="Stlc.html#3030" class="InductiveConstructor Operator"
      >&gt;&gt;</a
      ><a name="3831"
      > </a
      ><a name="3832" href="Stlc.html#2990" class="InductiveConstructor Operator"
      >&#10216;</a
      ><a name="3833"
      > </a
      ><a name="3834" href="Stlc.html#3994" class="Function"
      >step&#8321;</a
      ><a name="3839"
      > </a
      ><a name="3840" href="Stlc.html#2990" class="InductiveConstructor Operator"
      >&#10217;</a
      ><a name="3841"
      >
  </a
      ><a name="3844" class="Keyword"
      >where</a
      ><a name="3849"
      >
  </a
      ><a name="3852" href="Stlc.html#3852" class="Function"
      >M&#8320;</a
      ><a name="3854"
      > </a
      ><a name="3855" href="Stlc.html#3855" class="Function"
      >M&#8321;</a
      ><a name="3857"
      > </a
      ><a name="3858" href="Stlc.html#3858" class="Function"
      >M&#8322;</a
      ><a name="3860"
      > </a
      ><a name="3861" class="Symbol"
      >:</a
      ><a name="3862"
      > </a
      ><a name="3863" href="Stlc.html#1144" class="Datatype"
      >Term</a
      ><a name="3867"
      >
  </a
      ><a name="3870" href="Stlc.html#3852" class="Function"
      >M&#8320;</a
      ><a name="3872"
      > </a
      ><a name="3873" class="Symbol"
      >=</a
      ><a name="3874"
      > </a
      ><a name="3875" class="Symbol"
      >(</a
      ><a name="3876" href="Stlc.html#1431" class="Function"
      >not[&#120121;]</a
      ><a name="3882"
      > </a
      ><a name="3883" href="Stlc.html#1218" class="InductiveConstructor Operator"
      >&#183;&#7488;</a
      ><a name="3885"
      > </a
      ><a name="3886" href="Stlc.html#1246" class="InductiveConstructor"
      >true&#7488;</a
      ><a name="3891" class="Symbol"
      >)</a
      ><a name="3892"
      >
  </a
      ><a name="3895" href="Stlc.html#3855" class="Function"
      >M&#8321;</a
      ><a name="3897"
      > </a
      ><a name="3898" class="Symbol"
      >=</a
      ><a name="3899"
      > </a
      ><a name="3900" class="Symbol"
      >(</a
      ><a name="3901" href="Stlc.html#1277" class="InductiveConstructor Operator"
      >if&#7488;</a
      ><a name="3904"
      > </a
      ><a name="3905" href="Stlc.html#1246" class="InductiveConstructor"
      >true&#7488;</a
      ><a name="3910"
      > </a
      ><a name="3911" href="Stlc.html#1277" class="InductiveConstructor Operator"
      >then</a
      ><a name="3915"
      > </a
      ><a name="3916" href="Stlc.html#1261" class="InductiveConstructor"
      >false&#7488;</a
      ><a name="3922"
      > </a
      ><a name="3923" href="Stlc.html#1277" class="InductiveConstructor Operator"
      >else</a
      ><a name="3927"
      > </a
      ><a name="3928" href="Stlc.html#1246" class="InductiveConstructor"
      >true&#7488;</a
      ><a name="3933" class="Symbol"
      >)</a
      ><a name="3934"
      >
  </a
      ><a name="3937" href="Stlc.html#3858" class="Function"
      >M&#8322;</a
      ><a name="3939"
      > </a
      ><a name="3940" class="Symbol"
      >=</a
      ><a name="3941"
      > </a
      ><a name="3942" href="Stlc.html#1261" class="InductiveConstructor"
      >false&#7488;</a
      ><a name="3948"
      >
  </a
      ><a name="3951" href="Stlc.html#3951" class="Function"
      >step&#8320;</a
      ><a name="3956"
      > </a
      ><a name="3957" class="Symbol"
      >:</a
      ><a name="3958"
      > </a
      ><a name="3959" href="Stlc.html#3852" class="Function"
      >M&#8320;</a
      ><a name="3961"
      > </a
      ><a name="3962" href="Stlc.html#2353" class="Datatype Operator"
      >&#10233;</a
      ><a name="3963"
      > </a
      ><a name="3964" href="Stlc.html#3855" class="Function"
      >M&#8321;</a
      ><a name="3966"
      >
  </a
      ><a name="3969" href="Stlc.html#3951" class="Function"
      >step&#8320;</a
      ><a name="3974"
      > </a
      ><a name="3975" class="Symbol"
      >=</a
      ><a name="3976"
      > </a
      ><a name="3977" href="Stlc.html#2385" class="InductiveConstructor"
      >&#946;&#8658;</a
      ><a name="3979"
      > </a
      ><a name="3980" href="Stlc.html#1766" class="InductiveConstructor"
      >value-true&#7488;</a
      ><a name="3991"
      >
  </a
      ><a name="3994" href="Stlc.html#3994" class="Function"
      >step&#8321;</a
      ><a name="3999"
      > </a
      ><a name="4000" class="Symbol"
      >:</a
      ><a name="4001"
      > </a
      ><a name="4002" href="Stlc.html#3855" class="Function"
      >M&#8321;</a
      ><a name="4004"
      > </a
      ><a name="4005" href="Stlc.html#2353" class="Datatype Operator"
      >&#10233;</a
      ><a name="4006"
      > </a
      ><a name="4007" href="Stlc.html#3858" class="Function"
      >M&#8322;</a
      ><a name="4009"
      >
  </a
      ><a name="4012" href="Stlc.html#3994" class="Function"
      >step&#8321;</a
      ><a name="4017"
      > </a
      ><a name="4018" class="Symbol"
      >=</a
      ><a name="4019"
      > </a
      ><a name="4020" href="Stlc.html#2591" class="InductiveConstructor"
      >&#946;&#120121;&#8321;</a
      ><a name="4023"
      >

</a
      ><a name="4025" href="Stlc.html#4025" class="Function"
      >example&#8321;</a
      ><a name="4033"
      > </a
      ><a name="4034" class="Symbol"
      >:</a
      ><a name="4035"
      > </a
      ><a name="4036" class="Symbol"
      >(</a
      ><a name="4037" href="Stlc.html#1416" class="Function"
      >I[&#120121;&#8658;&#120121;]</a
      ><a name="4043"
      > </a
      ><a name="4044" href="Stlc.html#1218" class="InductiveConstructor Operator"
      >&#183;&#7488;</a
      ><a name="4046"
      > </a
      ><a name="4047" href="Stlc.html#1411" class="Function"
      >I[&#120121;]</a
      ><a name="4051"
      > </a
      ><a name="4052" href="Stlc.html#1218" class="InductiveConstructor Operator"
      >&#183;&#7488;</a
      ><a name="4054"
      > </a
      ><a name="4055" class="Symbol"
      >(</a
      ><a name="4056" href="Stlc.html#1431" class="Function"
      >not[&#120121;]</a
      ><a name="4062"
      > </a
      ><a name="4063" href="Stlc.html#1218" class="InductiveConstructor Operator"
      >&#183;&#7488;</a
      ><a name="4065"
      > </a
      ><a name="4066" href="Stlc.html#1261" class="InductiveConstructor"
      >false&#7488;</a
      ><a name="4072" class="Symbol"
      >))</a
      ><a name="4074"
      > </a
      ><a name="4075" href="Stlc.html#3127" class="Function Operator"
      >&#10233;*</a
      ><a name="4077"
      > </a
      ><a name="4078" href="Stlc.html#1246" class="InductiveConstructor"
      >true&#7488;</a
      ><a name="4083"
      >
</a
      ><a name="4084" href="Stlc.html#4025" class="Function"
      >example&#8321;</a
      ><a name="4092"
      > </a
      ><a name="4093" class="Symbol"
      >=</a
      ><a name="4094"
      > </a
      ><a name="4095" href="Stlc.html#2990" class="InductiveConstructor Operator"
      >&#10216;</a
      ><a name="4096"
      > </a
      ><a name="4097" href="Stlc.html#4461" class="Function"
      >step&#8320;</a
      ><a name="4102"
      > </a
      ><a name="4103" href="Stlc.html#2990" class="InductiveConstructor Operator"
      >&#10217;</a
      ><a name="4104"
      > </a
      ><a name="4105" href="Stlc.html#3030" class="InductiveConstructor Operator"
      >&gt;&gt;</a
      ><a name="4107"
      > </a
      ><a name="4108" href="Stlc.html#2990" class="InductiveConstructor Operator"
      >&#10216;</a
      ><a name="4109"
      > </a
      ><a name="4110" href="Stlc.html#4507" class="Function"
      >step&#8321;</a
      ><a name="4115"
      > </a
      ><a name="4116" href="Stlc.html#2990" class="InductiveConstructor Operator"
      >&#10217;</a
      ><a name="4117"
      > </a
      ><a name="4118" href="Stlc.html#3030" class="InductiveConstructor Operator"
      >&gt;&gt;</a
      ><a name="4120"
      > </a
      ><a name="4121" href="Stlc.html#2990" class="InductiveConstructor Operator"
      >&#10216;</a
      ><a name="4122"
      > </a
      ><a name="4123" href="Stlc.html#4566" class="Function"
      >step&#8322;</a
      ><a name="4128"
      > </a
      ><a name="4129" href="Stlc.html#2990" class="InductiveConstructor Operator"
      >&#10217;</a
      ><a name="4130"
      > </a
      ><a name="4131" href="Stlc.html#3030" class="InductiveConstructor Operator"
      >&gt;&gt;</a
      ><a name="4133"
      > </a
      ><a name="4134" href="Stlc.html#2990" class="InductiveConstructor Operator"
      >&#10216;</a
      ><a name="4135"
      > </a
      ><a name="4136" href="Stlc.html#4611" class="Function"
      >step&#8323;</a
      ><a name="4141"
      > </a
      ><a name="4142" href="Stlc.html#2990" class="InductiveConstructor Operator"
      >&#10217;</a
      ><a name="4143"
      > </a
      ><a name="4144" href="Stlc.html#3030" class="InductiveConstructor Operator"
      >&gt;&gt;</a
      ><a name="4146"
      > </a
      ><a name="4147" href="Stlc.html#2990" class="InductiveConstructor Operator"
      >&#10216;</a
      ><a name="4148"
      > </a
      ><a name="4149" href="Stlc.html#4663" class="Function"
      >step&#8324;</a
      ><a name="4154"
      > </a
      ><a name="4155" href="Stlc.html#2990" class="InductiveConstructor Operator"
      >&#10217;</a
      ><a name="4156"
      >
  </a
      ><a name="4159" class="Keyword"
      >where</a
      ><a name="4164"
      >
  </a
      ><a name="4167" href="Stlc.html#4167" class="Function"
      >M&#8320;</a
      ><a name="4169"
      > </a
      ><a name="4170" href="Stlc.html#4170" class="Function"
      >M&#8321;</a
      ><a name="4172"
      > </a
      ><a name="4173" href="Stlc.html#4173" class="Function"
      >M&#8322;</a
      ><a name="4175"
      > </a
      ><a name="4176" href="Stlc.html#4176" class="Function"
      >M&#8323;</a
      ><a name="4178"
      > </a
      ><a name="4179" href="Stlc.html#4179" class="Function"
      >M&#8324;</a
      ><a name="4181"
      > </a
      ><a name="4182" href="Stlc.html#4182" class="Function"
      >M&#8325;</a
      ><a name="4184"
      > </a
      ><a name="4185" class="Symbol"
      >:</a
      ><a name="4186"
      > </a
      ><a name="4187" href="Stlc.html#1144" class="Datatype"
      >Term</a
      ><a name="4191"
      >
  </a
      ><a name="4194" href="Stlc.html#4167" class="Function"
      >M&#8320;</a
      ><a name="4196"
      > </a
      ><a name="4197" class="Symbol"
      >=</a
      ><a name="4198"
      > </a
      ><a name="4199" class="Symbol"
      >(</a
      ><a name="4200" href="Stlc.html#1416" class="Function"
      >I[&#120121;&#8658;&#120121;]</a
      ><a name="4206"
      > </a
      ><a name="4207" href="Stlc.html#1218" class="InductiveConstructor Operator"
      >&#183;&#7488;</a
      ><a name="4209"
      > </a
      ><a name="4210" href="Stlc.html#1411" class="Function"
      >I[&#120121;]</a
      ><a name="4214"
      > </a
      ><a name="4215" href="Stlc.html#1218" class="InductiveConstructor Operator"
      >&#183;&#7488;</a
      ><a name="4217"
      > </a
      ><a name="4218" class="Symbol"
      >(</a
      ><a name="4219" href="Stlc.html#1431" class="Function"
      >not[&#120121;]</a
      ><a name="4225"
      > </a
      ><a name="4226" href="Stlc.html#1218" class="InductiveConstructor Operator"
      >&#183;&#7488;</a
      ><a name="4228"
      > </a
      ><a name="4229" href="Stlc.html#1261" class="InductiveConstructor"
      >false&#7488;</a
      ><a name="4235" class="Symbol"
      >))</a
      ><a name="4237"
      >
  </a
      ><a name="4240" href="Stlc.html#4170" class="Function"
      >M&#8321;</a
      ><a name="4242"
      > </a
      ><a name="4243" class="Symbol"
      >=</a
      ><a name="4244"
      > </a
      ><a name="4245" class="Symbol"
      >((</a
      ><a name="4247" href="Stlc.html#1182" class="InductiveConstructor Operator"
      >&#955;&#7488;</a
      ><a name="4249"
      > </a
      ><a name="4250" href="Stlc.html#1362" class="Function"
      >x</a
      ><a name="4251"
      > </a
      ><a name="4252" href="Stlc.html#1182" class="InductiveConstructor Operator"
      >&#8712;</a
      ><a name="4253"
      > </a
      ><a name="4254" href="Stlc.html#1102" class="InductiveConstructor"
      >&#120121;</a
      ><a name="4255"
      > </a
      ><a name="4256" href="Stlc.html#1182" class="InductiveConstructor Operator"
      >&#8658;</a
      ><a name="4257"
      > </a
      ><a name="4258" class="Symbol"
      >(</a
      ><a name="4259" href="Stlc.html#1411" class="Function"
      >I[&#120121;]</a
      ><a name="4263"
      > </a
      ><a name="4264" href="Stlc.html#1218" class="InductiveConstructor Operator"
      >&#183;&#7488;</a
      ><a name="4266"
      > </a
      ><a name="4267" href="Stlc.html#1163" class="InductiveConstructor"
      >var&#7488;</a
      ><a name="4271"
      > </a
      ><a name="4272" href="Stlc.html#1362" class="Function"
      >x</a
      ><a name="4273" class="Symbol"
      >))</a
      ><a name="4275"
      > </a
      ><a name="4276" href="Stlc.html#1218" class="InductiveConstructor Operator"
      >&#183;&#7488;</a
      ><a name="4278"
      > </a
      ><a name="4279" class="Symbol"
      >(</a
      ><a name="4280" href="Stlc.html#1431" class="Function"
      >not[&#120121;]</a
      ><a name="4286"
      > </a
      ><a name="4287" href="Stlc.html#1218" class="InductiveConstructor Operator"
      >&#183;&#7488;</a
      ><a name="4289"
      > </a
      ><a name="4290" href="Stlc.html#1261" class="InductiveConstructor"
      >false&#7488;</a
      ><a name="4296" class="Symbol"
      >))</a
      ><a name="4298"
      >
  </a
      ><a name="4301" href="Stlc.html#4173" class="Function"
      >M&#8322;</a
      ><a name="4303"
      > </a
      ><a name="4304" class="Symbol"
      >=</a
      ><a name="4305"
      > </a
      ><a name="4306" class="Symbol"
      >((</a
      ><a name="4308" href="Stlc.html#1182" class="InductiveConstructor Operator"
      >&#955;&#7488;</a
      ><a name="4310"
      > </a
      ><a name="4311" href="Stlc.html#1362" class="Function"
      >x</a
      ><a name="4312"
      > </a
      ><a name="4313" href="Stlc.html#1182" class="InductiveConstructor Operator"
      >&#8712;</a
      ><a name="4314"
      > </a
      ><a name="4315" href="Stlc.html#1102" class="InductiveConstructor"
      >&#120121;</a
      ><a name="4316"
      > </a
      ><a name="4317" href="Stlc.html#1182" class="InductiveConstructor Operator"
      >&#8658;</a
      ><a name="4318"
      > </a
      ><a name="4319" class="Symbol"
      >(</a
      ><a name="4320" href="Stlc.html#1411" class="Function"
      >I[&#120121;]</a
      ><a name="4324"
      > </a
      ><a name="4325" href="Stlc.html#1218" class="InductiveConstructor Operator"
      >&#183;&#7488;</a
      ><a name="4327"
      > </a
      ><a name="4328" href="Stlc.html#1163" class="InductiveConstructor"
      >var&#7488;</a
      ><a name="4332"
      > </a
      ><a name="4333" href="Stlc.html#1362" class="Function"
      >x</a
      ><a name="4334" class="Symbol"
      >))</a
      ><a name="4336"
      > </a
      ><a name="4337" href="Stlc.html#1218" class="InductiveConstructor Operator"
      >&#183;&#7488;</a
      ><a name="4339"
      > </a
      ><a name="4340" class="Symbol"
      >(</a
      ><a name="4341" href="Stlc.html#1277" class="InductiveConstructor Operator"
      >if&#7488;</a
      ><a name="4344"
      > </a
      ><a name="4345" href="Stlc.html#1261" class="InductiveConstructor"
      >false&#7488;</a
      ><a name="4351"
      > </a
      ><a name="4352" href="Stlc.html#1277" class="InductiveConstructor Operator"
      >then</a
      ><a name="4356"
      > </a
      ><a name="4357" href="Stlc.html#1261" class="InductiveConstructor"
      >false&#7488;</a
      ><a name="4363"
      > </a
      ><a name="4364" href="Stlc.html#1277" class="InductiveConstructor Operator"
      >else</a
      ><a name="4368"
      > </a
      ><a name="4369" href="Stlc.html#1246" class="InductiveConstructor"
      >true&#7488;</a
      ><a name="4374" class="Symbol"
      >))</a
      ><a name="4376"
      >
  </a
      ><a name="4379" href="Stlc.html#4176" class="Function"
      >M&#8323;</a
      ><a name="4381"
      > </a
      ><a name="4382" class="Symbol"
      >=</a
      ><a name="4383"
      > </a
      ><a name="4384" class="Symbol"
      >((</a
      ><a name="4386" href="Stlc.html#1182" class="InductiveConstructor Operator"
      >&#955;&#7488;</a
      ><a name="4388"
      > </a
      ><a name="4389" href="Stlc.html#1362" class="Function"
      >x</a
      ><a name="4390"
      > </a
      ><a name="4391" href="Stlc.html#1182" class="InductiveConstructor Operator"
      >&#8712;</a
      ><a name="4392"
      > </a
      ><a name="4393" href="Stlc.html#1102" class="InductiveConstructor"
      >&#120121;</a
      ><a name="4394"
      > </a
      ><a name="4395" href="Stlc.html#1182" class="InductiveConstructor Operator"
      >&#8658;</a
      ><a name="4396"
      > </a
      ><a name="4397" class="Symbol"
      >(</a
      ><a name="4398" href="Stlc.html#1411" class="Function"
      >I[&#120121;]</a
      ><a name="4402"
      > </a
      ><a name="4403" href="Stlc.html#1218" class="InductiveConstructor Operator"
      >&#183;&#7488;</a
      ><a name="4405"
      > </a
      ><a name="4406" href="Stlc.html#1163" class="InductiveConstructor"
      >var&#7488;</a
      ><a name="4410"
      > </a
      ><a name="4411" href="Stlc.html#1362" class="Function"
      >x</a
      ><a name="4412" class="Symbol"
      >))</a
      ><a name="4414"
      > </a
      ><a name="4415" href="Stlc.html#1218" class="InductiveConstructor Operator"
      >&#183;&#7488;</a
      ><a name="4417"
      > </a
      ><a name="4418" href="Stlc.html#1246" class="InductiveConstructor"
      >true&#7488;</a
      ><a name="4423" class="Symbol"
      >)</a
      ><a name="4424"
      >
  </a
      ><a name="4427" href="Stlc.html#4179" class="Function"
      >M&#8324;</a
      ><a name="4429"
      > </a
      ><a name="4430" class="Symbol"
      >=</a
      ><a name="4431"
      > </a
      ><a name="4432" href="Stlc.html#1411" class="Function"
      >I[&#120121;]</a
      ><a name="4436"
      > </a
      ><a name="4437" href="Stlc.html#1218" class="InductiveConstructor Operator"
      >&#183;&#7488;</a
      ><a name="4439"
      > </a
      ><a name="4440" href="Stlc.html#1246" class="InductiveConstructor"
      >true&#7488;</a
      ><a name="4445"
      >
  </a
      ><a name="4448" href="Stlc.html#4182" class="Function"
      >M&#8325;</a
      ><a name="4450"
      > </a
      ><a name="4451" class="Symbol"
      >=</a
      ><a name="4452"
      > </a
      ><a name="4453" href="Stlc.html#1246" class="InductiveConstructor"
      >true&#7488;</a
      ><a name="4458"
      >
  </a
      ><a name="4461" href="Stlc.html#4461" class="Function"
      >step&#8320;</a
      ><a name="4466"
      > </a
      ><a name="4467" class="Symbol"
      >:</a
      ><a name="4468"
      > </a
      ><a name="4469" href="Stlc.html#4167" class="Function"
      >M&#8320;</a
      ><a name="4471"
      > </a
      ><a name="4472" href="Stlc.html#2353" class="Datatype Operator"
      >&#10233;</a
      ><a name="4473"
      > </a
      ><a name="4474" href="Stlc.html#4170" class="Function"
      >M&#8321;</a
      ><a name="4476"
      >
  </a
      ><a name="4479" href="Stlc.html#4461" class="Function"
      >step&#8320;</a
      ><a name="4484"
      > </a
      ><a name="4485" class="Symbol"
      >=</a
      ><a name="4486"
      > </a
      ><a name="4487" href="Stlc.html#2459" class="InductiveConstructor"
      >&#947;&#8658;&#8321;</a
      ><a name="4490"
      > </a
      ><a name="4491" class="Symbol"
      >(</a
      ><a name="4492" href="Stlc.html#2385" class="InductiveConstructor"
      >&#946;&#8658;</a
      ><a name="4494"
      > </a
      ><a name="4495" href="Stlc.html#1720" class="InductiveConstructor"
      >value-&#955;&#7488;</a
      ><a name="4503" class="Symbol"
      >)</a
      ><a name="4504"
      >
  </a
      ><a name="4507" href="Stlc.html#4507" class="Function"
      >step&#8321;</a
      ><a name="4512"
      > </a
      ><a name="4513" class="Symbol"
      >:</a
      ><a name="4514"
      > </a
      ><a name="4515" href="Stlc.html#4170" class="Function"
      >M&#8321;</a
      ><a name="4517"
      > </a
      ><a name="4518" href="Stlc.html#2353" class="Datatype Operator"
      >&#10233;</a
      ><a name="4519"
      > </a
      ><a name="4520" href="Stlc.html#4173" class="Function"
      >M&#8322;</a
      ><a name="4522"
      >
  </a
      ><a name="4525" href="Stlc.html#4507" class="Function"
      >step&#8321;</a
      ><a name="4530"
      > </a
      ><a name="4531" class="Symbol"
      >=</a
      ><a name="4532"
      > </a
      ><a name="4533" href="Stlc.html#2518" class="InductiveConstructor"
      >&#947;&#8658;&#8322;</a
      ><a name="4536"
      > </a
      ><a name="4537" href="Stlc.html#1720" class="InductiveConstructor"
      >value-&#955;&#7488;</a
      ><a name="4545"
      > </a
      ><a name="4546" class="Symbol"
      >(</a
      ><a name="4547" href="Stlc.html#2385" class="InductiveConstructor"
      >&#946;&#8658;</a
      ><a name="4549"
      > </a
      ><a name="4550" href="Stlc.html#1796" class="InductiveConstructor"
      >value-false&#7488;</a
      ><a name="4562" class="Symbol"
      >)</a
      ><a name="4563"
      >
  </a
      ><a name="4566" href="Stlc.html#4566" class="Function"
      >step&#8322;</a
      ><a name="4571"
      > </a
      ><a name="4572" class="Symbol"
      >:</a
      ><a name="4573"
      > </a
      ><a name="4574" href="Stlc.html#4173" class="Function"
      >M&#8322;</a
      ><a name="4576"
      > </a
      ><a name="4577" href="Stlc.html#2353" class="Datatype Operator"
      >&#10233;</a
      ><a name="4578"
      > </a
      ><a name="4579" href="Stlc.html#4176" class="Function"
      >M&#8323;</a
      ><a name="4581"
      >
  </a
      ><a name="4584" href="Stlc.html#4566" class="Function"
      >step&#8322;</a
      ><a name="4589"
      > </a
      ><a name="4590" class="Symbol"
      >=</a
      ><a name="4591"
      > </a
      ><a name="4592" href="Stlc.html#2518" class="InductiveConstructor"
      >&#947;&#8658;&#8322;</a
      ><a name="4595"
      > </a
      ><a name="4596" href="Stlc.html#1720" class="InductiveConstructor"
      >value-&#955;&#7488;</a
      ><a name="4604"
      > </a
      ><a name="4605" href="Stlc.html#2643" class="InductiveConstructor"
      >&#946;&#120121;&#8322;</a
      ><a name="4608"
      >
  </a
      ><a name="4611" href="Stlc.html#4611" class="Function"
      >step&#8323;</a
      ><a name="4616"
      > </a
      ><a name="4617" class="Symbol"
      >:</a
      ><a name="4618"
      > </a
      ><a name="4619" href="Stlc.html#4176" class="Function"
      >M&#8323;</a
      ><a name="4621"
      > </a
      ><a name="4622" href="Stlc.html#2353" class="Datatype Operator"
      >&#10233;</a
      ><a name="4623"
      > </a
      ><a name="4624" href="Stlc.html#4179" class="Function"
      >M&#8324;</a
      ><a name="4626"
      >
  </a
      ><a name="4629" href="Stlc.html#4611" class="Function"
      >step&#8323;</a
      ><a name="4634"
      > </a
      ><a name="4635" class="Symbol"
      >=</a
      ><a name="4636"
      > </a
      ><a name="4637" href="Stlc.html#2385" class="InductiveConstructor"
      >&#946;&#8658;</a
      ><a name="4639"
      > </a
      ><a name="4640" href="Stlc.html#1766" class="InductiveConstructor"
      >value-true&#7488;</a
      ><a name="4651"
      >         
  </a
      ><a name="4663" href="Stlc.html#4663" class="Function"
      >step&#8324;</a
      ><a name="4668"
      > </a
      ><a name="4669" class="Symbol"
      >:</a
      ><a name="4670"
      > </a
      ><a name="4671" href="Stlc.html#4179" class="Function"
      >M&#8324;</a
      ><a name="4673"
      > </a
      ><a name="4674" href="Stlc.html#2353" class="Datatype Operator"
      >&#10233;</a
      ><a name="4675"
      > </a
      ><a name="4676" href="Stlc.html#4182" class="Function"
      >M&#8325;</a
      ><a name="4678"
      >
  </a
      ><a name="4681" href="Stlc.html#4663" class="Function"
      >step&#8324;</a
      ><a name="4686"
      > </a
      ><a name="4687" class="Symbol"
      >=</a
      ><a name="4688"
      > </a
      ><a name="4689" href="Stlc.html#2385" class="InductiveConstructor"
      >&#946;&#8658;</a
      ><a name="4691"
      > </a
      ><a name="4692" href="Stlc.html#1766" class="InductiveConstructor"
      >value-true&#7488;</a
      >

</pre>

## Type rules

<pre class="Agda">

<a name="4753" href="Stlc.html#4753" class="Function"
      >Context</a
      ><a name="4760"
      > </a
      ><a name="4761" class="Symbol"
      >:</a
      ><a name="4762"
      > </a
      ><a name="4763" class="PrimitiveType"
      >Set</a
      ><a name="4766"
      >
</a
      ><a name="4767" href="Stlc.html#4753" class="Function"
      >Context</a
      ><a name="4774"
      > </a
      ><a name="4775" class="Symbol"
      >=</a
      ><a name="4776"
      > </a
      ><a name="4777" href="Maps.html#10227" class="Function"
      >PartialMap</a
      ><a name="4787"
      > </a
      ><a name="4788" href="Stlc.html#1083" class="Datatype"
      >Type</a
      ><a name="4792"
      >

</a
      ><a name="4794" class="Keyword"
      >infix</a
      ><a name="4799"
      > </a
      ><a name="4800" class="Number"
      >50</a
      ><a name="4802"
      > </a
      ><a name="4803" href="Stlc.html#4815" class="Datatype Operator"
      >_&#8866;_&#8712;_</a
      ><a name="4808"
      >

</a
      ><a name="4810" class="Keyword"
      >data</a
      ><a name="4814"
      > </a
      ><a name="4815" href="Stlc.html#4815" class="Datatype Operator"
      >_&#8866;_&#8712;_</a
      ><a name="4820"
      > </a
      ><a name="4821" class="Symbol"
      >:</a
      ><a name="4822"
      > </a
      ><a name="4823" href="Stlc.html#4753" class="Function"
      >Context</a
      ><a name="4830"
      > </a
      ><a name="4831" class="Symbol"
      >&#8594;</a
      ><a name="4832"
      > </a
      ><a name="4833" href="Stlc.html#1144" class="Datatype"
      >Term</a
      ><a name="4837"
      > </a
      ><a name="4838" class="Symbol"
      >&#8594;</a
      ><a name="4839"
      > </a
      ><a name="4840" href="Stlc.html#1083" class="Datatype"
      >Type</a
      ><a name="4844"
      > </a
      ><a name="4845" class="Symbol"
      >&#8594;</a
      ><a name="4846"
      > </a
      ><a name="4847" class="PrimitiveType"
      >Set</a
      ><a name="4850"
      > </a
      ><a name="4851" class="Keyword"
      >where</a
      ><a name="4856"
      >
  </a
      ><a name="4859" href="Stlc.html#4859" class="InductiveConstructor"
      >Ax</a
      ><a name="4861"
      > </a
      ><a name="4862" class="Symbol"
      >:</a
      ><a name="4863"
      > </a
      ><a name="4864" class="Symbol"
      >&#8704;</a
      ><a name="4865"
      > </a
      ><a name="4866" class="Symbol"
      >{</a
      ><a name="4867" href="Stlc.html#4867" class="Bound"
      >&#915;</a
      ><a name="4868"
      > </a
      ><a name="4869" href="Stlc.html#4869" class="Bound"
      >x</a
      ><a name="4870"
      > </a
      ><a name="4871" href="Stlc.html#4871" class="Bound"
      >A</a
      ><a name="4872" class="Symbol"
      >}</a
      ><a name="4873"
      > </a
      ><a name="4874" class="Symbol"
      >&#8594;</a
      ><a name="4875"
      >
    </a
      ><a name="4880" href="Stlc.html#4867" class="Bound"
      >&#915;</a
      ><a name="4881"
      > </a
      ><a name="4882" href="Stlc.html#4869" class="Bound"
      >x</a
      ><a name="4883"
      > </a
      ><a name="4884" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="4885"
      > </a
      ><a name="4886" href="https://agda.github.io/agda-stdlib/Data.Maybe.Base.html#373" class="InductiveConstructor"
      >just</a
      ><a name="4890"
      > </a
      ><a name="4891" href="Stlc.html#4871" class="Bound"
      >A</a
      ><a name="4892"
      > </a
      ><a name="4893" class="Symbol"
      >&#8594;</a
      ><a name="4894"
      >
    </a
      ><a name="4899" href="Stlc.html#4867" class="Bound"
      >&#915;</a
      ><a name="4900"
      > </a
      ><a name="4901" href="Stlc.html#4815" class="Datatype Operator"
      >&#8866;</a
      ><a name="4902"
      > </a
      ><a name="4903" href="Stlc.html#1163" class="InductiveConstructor"
      >var&#7488;</a
      ><a name="4907"
      > </a
      ><a name="4908" href="Stlc.html#4869" class="Bound"
      >x</a
      ><a name="4909"
      > </a
      ><a name="4910" href="Stlc.html#4815" class="Datatype Operator"
      >&#8712;</a
      ><a name="4911"
      > </a
      ><a name="4912" href="Stlc.html#4871" class="Bound"
      >A</a
      ><a name="4913"
      >
  </a
      ><a name="4916" href="Stlc.html#4916" class="InductiveConstructor"
      >&#8658;-I</a
      ><a name="4919"
      > </a
      ><a name="4920" class="Symbol"
      >:</a
      ><a name="4921"
      > </a
      ><a name="4922" class="Symbol"
      >&#8704;</a
      ><a name="4923"
      > </a
      ><a name="4924" class="Symbol"
      >{</a
      ><a name="4925" href="Stlc.html#4925" class="Bound"
      >&#915;</a
      ><a name="4926"
      > </a
      ><a name="4927" href="Stlc.html#4927" class="Bound"
      >x</a
      ><a name="4928"
      > </a
      ><a name="4929" href="Stlc.html#4929" class="Bound"
      >N</a
      ><a name="4930"
      > </a
      ><a name="4931" href="Stlc.html#4931" class="Bound"
      >A</a
      ><a name="4932"
      > </a
      ><a name="4933" href="Stlc.html#4933" class="Bound"
      >B</a
      ><a name="4934" class="Symbol"
      >}</a
      ><a name="4935"
      > </a
      ><a name="4936" class="Symbol"
      >&#8594;</a
      ><a name="4937"
      >
    </a
      ><a name="4942" class="Symbol"
      >(</a
      ><a name="4943" href="Stlc.html#4925" class="Bound"
      >&#915;</a
      ><a name="4944"
      > </a
      ><a name="4945" href="Maps.html#10464" class="Function Operator"
      >,</a
      ><a name="4946"
      > </a
      ><a name="4947" href="Stlc.html#4927" class="Bound"
      >x</a
      ><a name="4948"
      > </a
      ><a name="4949" href="Maps.html#10464" class="Function Operator"
      >&#8614;</a
      ><a name="4950"
      > </a
      ><a name="4951" href="Stlc.html#4931" class="Bound"
      >A</a
      ><a name="4952" class="Symbol"
      >)</a
      ><a name="4953"
      > </a
      ><a name="4954" href="Stlc.html#4815" class="Datatype Operator"
      >&#8866;</a
      ><a name="4955"
      > </a
      ><a name="4956" href="Stlc.html#4929" class="Bound"
      >N</a
      ><a name="4957"
      > </a
      ><a name="4958" href="Stlc.html#4815" class="Datatype Operator"
      >&#8712;</a
      ><a name="4959"
      > </a
      ><a name="4960" href="Stlc.html#4933" class="Bound"
      >B</a
      ><a name="4961"
      > </a
      ><a name="4962" class="Symbol"
      >&#8594;</a
      ><a name="4963"
      >
    </a
      ><a name="4968" href="Stlc.html#4925" class="Bound"
      >&#915;</a
      ><a name="4969"
      > </a
      ><a name="4970" href="Stlc.html#4815" class="Datatype Operator"
      >&#8866;</a
      ><a name="4971"
      > </a
      ><a name="4972" class="Symbol"
      >(</a
      ><a name="4973" href="Stlc.html#1182" class="InductiveConstructor Operator"
      >&#955;&#7488;</a
      ><a name="4975"
      > </a
      ><a name="4976" href="Stlc.html#4927" class="Bound"
      >x</a
      ><a name="4977"
      > </a
      ><a name="4978" href="Stlc.html#1182" class="InductiveConstructor Operator"
      >&#8712;</a
      ><a name="4979"
      > </a
      ><a name="4980" href="Stlc.html#4931" class="Bound"
      >A</a
      ><a name="4981"
      > </a
      ><a name="4982" href="Stlc.html#1182" class="InductiveConstructor Operator"
      >&#8658;</a
      ><a name="4983"
      > </a
      ><a name="4984" href="Stlc.html#4929" class="Bound"
      >N</a
      ><a name="4985" class="Symbol"
      >)</a
      ><a name="4986"
      > </a
      ><a name="4987" href="Stlc.html#4815" class="Datatype Operator"
      >&#8712;</a
      ><a name="4988"
      > </a
      ><a name="4989" class="Symbol"
      >(</a
      ><a name="4990" href="Stlc.html#4931" class="Bound"
      >A</a
      ><a name="4991"
      > </a
      ><a name="4992" href="Stlc.html#1113" class="InductiveConstructor Operator"
      >&#8658;</a
      ><a name="4993"
      > </a
      ><a name="4994" href="Stlc.html#4933" class="Bound"
      >B</a
      ><a name="4995" class="Symbol"
      >)</a
      ><a name="4996"
      >
  </a
      ><a name="4999" href="Stlc.html#4999" class="InductiveConstructor"
      >&#8658;-E</a
      ><a name="5002"
      > </a
      ><a name="5003" class="Symbol"
      >:</a
      ><a name="5004"
      > </a
      ><a name="5005" class="Symbol"
      >&#8704;</a
      ><a name="5006"
      > </a
      ><a name="5007" class="Symbol"
      >{</a
      ><a name="5008" href="Stlc.html#5008" class="Bound"
      >&#915;</a
      ><a name="5009"
      > </a
      ><a name="5010" href="Stlc.html#5010" class="Bound"
      >L</a
      ><a name="5011"
      > </a
      ><a name="5012" href="Stlc.html#5012" class="Bound"
      >M</a
      ><a name="5013"
      > </a
      ><a name="5014" href="Stlc.html#5014" class="Bound"
      >A</a
      ><a name="5015"
      > </a
      ><a name="5016" href="Stlc.html#5016" class="Bound"
      >B</a
      ><a name="5017" class="Symbol"
      >}</a
      ><a name="5018"
      > </a
      ><a name="5019" class="Symbol"
      >&#8594;</a
      ><a name="5020"
      >
    </a
      ><a name="5025" href="Stlc.html#5008" class="Bound"
      >&#915;</a
      ><a name="5026"
      > </a
      ><a name="5027" href="Stlc.html#4815" class="Datatype Operator"
      >&#8866;</a
      ><a name="5028"
      > </a
      ><a name="5029" href="Stlc.html#5010" class="Bound"
      >L</a
      ><a name="5030"
      > </a
      ><a name="5031" href="Stlc.html#4815" class="Datatype Operator"
      >&#8712;</a
      ><a name="5032"
      > </a
      ><a name="5033" class="Symbol"
      >(</a
      ><a name="5034" href="Stlc.html#5014" class="Bound"
      >A</a
      ><a name="5035"
      > </a
      ><a name="5036" href="Stlc.html#1113" class="InductiveConstructor Operator"
      >&#8658;</a
      ><a name="5037"
      > </a
      ><a name="5038" href="Stlc.html#5016" class="Bound"
      >B</a
      ><a name="5039" class="Symbol"
      >)</a
      ><a name="5040"
      > </a
      ><a name="5041" class="Symbol"
      >&#8594;</a
      ><a name="5042"
      >
    </a
      ><a name="5047" href="Stlc.html#5008" class="Bound"
      >&#915;</a
      ><a name="5048"
      > </a
      ><a name="5049" href="Stlc.html#4815" class="Datatype Operator"
      >&#8866;</a
      ><a name="5050"
      > </a
      ><a name="5051" href="Stlc.html#5012" class="Bound"
      >M</a
      ><a name="5052"
      > </a
      ><a name="5053" href="Stlc.html#4815" class="Datatype Operator"
      >&#8712;</a
      ><a name="5054"
      > </a
      ><a name="5055" href="Stlc.html#5014" class="Bound"
      >A</a
      ><a name="5056"
      > </a
      ><a name="5057" class="Symbol"
      >&#8594;</a
      ><a name="5058"
      >
    </a
      ><a name="5063" href="Stlc.html#5008" class="Bound"
      >&#915;</a
      ><a name="5064"
      > </a
      ><a name="5065" href="Stlc.html#4815" class="Datatype Operator"
      >&#8866;</a
      ><a name="5066"
      > </a
      ><a name="5067" href="Stlc.html#5010" class="Bound"
      >L</a
      ><a name="5068"
      > </a
      ><a name="5069" href="Stlc.html#1218" class="InductiveConstructor Operator"
      >&#183;&#7488;</a
      ><a name="5071"
      > </a
      ><a name="5072" href="Stlc.html#5012" class="Bound"
      >M</a
      ><a name="5073"
      > </a
      ><a name="5074" href="Stlc.html#4815" class="Datatype Operator"
      >&#8712;</a
      ><a name="5075"
      > </a
      ><a name="5076" href="Stlc.html#5016" class="Bound"
      >B</a
      ><a name="5077"
      >
  </a
      ><a name="5080" href="Stlc.html#5080" class="InductiveConstructor"
      >&#120121;-I&#8321;</a
      ><a name="5084"
      > </a
      ><a name="5085" class="Symbol"
      >:</a
      ><a name="5086"
      > </a
      ><a name="5087" class="Symbol"
      >&#8704;</a
      ><a name="5088"
      > </a
      ><a name="5089" class="Symbol"
      >{</a
      ><a name="5090" href="Stlc.html#5090" class="Bound"
      >&#915;</a
      ><a name="5091" class="Symbol"
      >}</a
      ><a name="5092"
      > </a
      ><a name="5093" class="Symbol"
      >&#8594;</a
      ><a name="5094"
      >
    </a
      ><a name="5099" href="Stlc.html#5090" class="Bound"
      >&#915;</a
      ><a name="5100"
      > </a
      ><a name="5101" href="Stlc.html#4815" class="Datatype Operator"
      >&#8866;</a
      ><a name="5102"
      > </a
      ><a name="5103" href="Stlc.html#1246" class="InductiveConstructor"
      >true&#7488;</a
      ><a name="5108"
      > </a
      ><a name="5109" href="Stlc.html#4815" class="Datatype Operator"
      >&#8712;</a
      ><a name="5110"
      > </a
      ><a name="5111" href="Stlc.html#1102" class="InductiveConstructor"
      >&#120121;</a
      ><a name="5112"
      >
  </a
      ><a name="5115" href="Stlc.html#5115" class="InductiveConstructor"
      >&#120121;-I&#8322;</a
      ><a name="5119"
      > </a
      ><a name="5120" class="Symbol"
      >:</a
      ><a name="5121"
      > </a
      ><a name="5122" class="Symbol"
      >&#8704;</a
      ><a name="5123"
      > </a
      ><a name="5124" class="Symbol"
      >{</a
      ><a name="5125" href="Stlc.html#5125" class="Bound"
      >&#915;</a
      ><a name="5126" class="Symbol"
      >}</a
      ><a name="5127"
      > </a
      ><a name="5128" class="Symbol"
      >&#8594;</a
      ><a name="5129"
      >
    </a
      ><a name="5134" href="Stlc.html#5125" class="Bound"
      >&#915;</a
      ><a name="5135"
      > </a
      ><a name="5136" href="Stlc.html#4815" class="Datatype Operator"
      >&#8866;</a
      ><a name="5137"
      > </a
      ><a name="5138" href="Stlc.html#1261" class="InductiveConstructor"
      >false&#7488;</a
      ><a name="5144"
      > </a
      ><a name="5145" href="Stlc.html#4815" class="Datatype Operator"
      >&#8712;</a
      ><a name="5146"
      > </a
      ><a name="5147" href="Stlc.html#1102" class="InductiveConstructor"
      >&#120121;</a
      ><a name="5148"
      >
  </a
      ><a name="5151" href="Stlc.html#5151" class="InductiveConstructor"
      >&#120121;-E</a
      ><a name="5154"
      > </a
      ><a name="5155" class="Symbol"
      >:</a
      ><a name="5156"
      > </a
      ><a name="5157" class="Symbol"
      >&#8704;</a
      ><a name="5158"
      > </a
      ><a name="5159" class="Symbol"
      >{</a
      ><a name="5160" href="Stlc.html#5160" class="Bound"
      >&#915;</a
      ><a name="5161"
      > </a
      ><a name="5162" href="Stlc.html#5162" class="Bound"
      >L</a
      ><a name="5163"
      > </a
      ><a name="5164" href="Stlc.html#5164" class="Bound"
      >M</a
      ><a name="5165"
      > </a
      ><a name="5166" href="Stlc.html#5166" class="Bound"
      >N</a
      ><a name="5167"
      > </a
      ><a name="5168" href="Stlc.html#5168" class="Bound"
      >A</a
      ><a name="5169" class="Symbol"
      >}</a
      ><a name="5170"
      > </a
      ><a name="5171" class="Symbol"
      >&#8594;</a
      ><a name="5172"
      >
    </a
      ><a name="5177" href="Stlc.html#5160" class="Bound"
      >&#915;</a
      ><a name="5178"
      > </a
      ><a name="5179" href="Stlc.html#4815" class="Datatype Operator"
      >&#8866;</a
      ><a name="5180"
      > </a
      ><a name="5181" href="Stlc.html#5162" class="Bound"
      >L</a
      ><a name="5182"
      > </a
      ><a name="5183" href="Stlc.html#4815" class="Datatype Operator"
      >&#8712;</a
      ><a name="5184"
      > </a
      ><a name="5185" href="Stlc.html#1102" class="InductiveConstructor"
      >&#120121;</a
      ><a name="5186"
      > </a
      ><a name="5187" class="Symbol"
      >&#8594;</a
      ><a name="5188"
      >
    </a
      ><a name="5193" href="Stlc.html#5160" class="Bound"
      >&#915;</a
      ><a name="5194"
      > </a
      ><a name="5195" href="Stlc.html#4815" class="Datatype Operator"
      >&#8866;</a
      ><a name="5196"
      > </a
      ><a name="5197" href="Stlc.html#5164" class="Bound"
      >M</a
      ><a name="5198"
      > </a
      ><a name="5199" href="Stlc.html#4815" class="Datatype Operator"
      >&#8712;</a
      ><a name="5200"
      > </a
      ><a name="5201" href="Stlc.html#5168" class="Bound"
      >A</a
      ><a name="5202"
      > </a
      ><a name="5203" class="Symbol"
      >&#8594;</a
      ><a name="5204"
      >
    </a
      ><a name="5209" href="Stlc.html#5160" class="Bound"
      >&#915;</a
      ><a name="5210"
      > </a
      ><a name="5211" href="Stlc.html#4815" class="Datatype Operator"
      >&#8866;</a
      ><a name="5212"
      > </a
      ><a name="5213" href="Stlc.html#5166" class="Bound"
      >N</a
      ><a name="5214"
      > </a
      ><a name="5215" href="Stlc.html#4815" class="Datatype Operator"
      >&#8712;</a
      ><a name="5216"
      > </a
      ><a name="5217" href="Stlc.html#5168" class="Bound"
      >A</a
      ><a name="5218"
      > </a
      ><a name="5219" class="Symbol"
      >&#8594;</a
      ><a name="5220"
      >
    </a
      ><a name="5225" href="Stlc.html#5160" class="Bound"
      >&#915;</a
      ><a name="5226"
      > </a
      ><a name="5227" href="Stlc.html#4815" class="Datatype Operator"
      >&#8866;</a
      ><a name="5228"
      > </a
      ><a name="5229" class="Symbol"
      >(</a
      ><a name="5230" href="Stlc.html#1277" class="InductiveConstructor Operator"
      >if&#7488;</a
      ><a name="5233"
      > </a
      ><a name="5234" href="Stlc.html#5162" class="Bound"
      >L</a
      ><a name="5235"
      > </a
      ><a name="5236" href="Stlc.html#1277" class="InductiveConstructor Operator"
      >then</a
      ><a name="5240"
      > </a
      ><a name="5241" href="Stlc.html#5164" class="Bound"
      >M</a
      ><a name="5242"
      > </a
      ><a name="5243" href="Stlc.html#1277" class="InductiveConstructor Operator"
      >else</a
      ><a name="5247"
      > </a
      ><a name="5248" href="Stlc.html#5166" class="Bound"
      >N</a
      ><a name="5249" class="Symbol"
      >)</a
      ><a name="5250"
      > </a
      ><a name="5251" href="Stlc.html#4815" class="Datatype Operator"
      >&#8712;</a
      ><a name="5252"
      > </a
      ><a name="5253" href="Stlc.html#5168" class="Bound"
      >A</a
      >

</pre>
