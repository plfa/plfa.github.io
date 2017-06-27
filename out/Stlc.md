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
      ><a name="700" class="Comment"
      >-- open import Relation.Binary.Core using (Rel)</a
      ><a name="747"
      >
</a
      ><a name="748" class="Comment"
      >-- open import Data.Product using (&#8707;; &#8708;; _,_)</a
      ><a name="793"
      >
</a
      ><a name="794" class="Comment"
      >-- open import Function using (_&#8728;_; _$_)</a
      >

</pre>


## Syntax

Syntax of types and terms. All source terms are labeled with $ᵀ$.

<pre class="Agda">

<a name="939" class="Keyword"
      >infixr</a
      ><a name="945"
      > </a
      ><a name="946" class="Number"
      >100</a
      ><a name="949"
      > </a
      ><a name="950" href="Stlc.html#1006" class="InductiveConstructor Operator"
      >_&#8658;_</a
      ><a name="953"
      >
</a
      ><a name="954" class="Keyword"
      >infixl</a
      ><a name="960"
      > </a
      ><a name="961" class="Number"
      >100</a
      ><a name="964"
      > </a
      ><a name="965" href="Stlc.html#1111" class="InductiveConstructor Operator"
      >_&#183;&#7488;_</a
      ><a name="969"
      >

</a
      ><a name="971" class="Keyword"
      >data</a
      ><a name="975"
      > </a
      ><a name="976" href="Stlc.html#976" class="Datatype"
      >Type</a
      ><a name="980"
      > </a
      ><a name="981" class="Symbol"
      >:</a
      ><a name="982"
      > </a
      ><a name="983" class="PrimitiveType"
      >Set</a
      ><a name="986"
      > </a
      ><a name="987" class="Keyword"
      >where</a
      ><a name="992"
      >
  </a
      ><a name="995" href="Stlc.html#995" class="InductiveConstructor"
      >&#120121;</a
      ><a name="996"
      > </a
      ><a name="997" class="Symbol"
      >:</a
      ><a name="998"
      > </a
      ><a name="999" href="Stlc.html#976" class="Datatype"
      >Type</a
      ><a name="1003"
      >
  </a
      ><a name="1006" href="Stlc.html#1006" class="InductiveConstructor Operator"
      >_&#8658;_</a
      ><a name="1009"
      > </a
      ><a name="1010" class="Symbol"
      >:</a
      ><a name="1011"
      > </a
      ><a name="1012" href="Stlc.html#976" class="Datatype"
      >Type</a
      ><a name="1016"
      > </a
      ><a name="1017" class="Symbol"
      >&#8594;</a
      ><a name="1018"
      > </a
      ><a name="1019" href="Stlc.html#976" class="Datatype"
      >Type</a
      ><a name="1023"
      > </a
      ><a name="1024" class="Symbol"
      >&#8594;</a
      ><a name="1025"
      > </a
      ><a name="1026" href="Stlc.html#976" class="Datatype"
      >Type</a
      ><a name="1030"
      >

</a
      ><a name="1032" class="Keyword"
      >data</a
      ><a name="1036"
      > </a
      ><a name="1037" href="Stlc.html#1037" class="Datatype"
      >Term</a
      ><a name="1041"
      > </a
      ><a name="1042" class="Symbol"
      >:</a
      ><a name="1043"
      > </a
      ><a name="1044" class="PrimitiveType"
      >Set</a
      ><a name="1047"
      > </a
      ><a name="1048" class="Keyword"
      >where</a
      ><a name="1053"
      >
  </a
      ><a name="1056" href="Stlc.html#1056" class="InductiveConstructor"
      >var&#7488;</a
      ><a name="1060"
      > </a
      ><a name="1061" class="Symbol"
      >:</a
      ><a name="1062"
      > </a
      ><a name="1063" href="Maps.html#2215" class="Datatype"
      >Id</a
      ><a name="1065"
      > </a
      ><a name="1066" class="Symbol"
      >&#8594;</a
      ><a name="1067"
      > </a
      ><a name="1068" href="Stlc.html#1037" class="Datatype"
      >Term</a
      ><a name="1072"
      >
  </a
      ><a name="1075" href="Stlc.html#1075" class="InductiveConstructor Operator"
      >&#955;&#7488;_&#8712;_&#8658;_</a
      ><a name="1082"
      > </a
      ><a name="1083" class="Symbol"
      >:</a
      ><a name="1084"
      > </a
      ><a name="1085" href="Maps.html#2215" class="Datatype"
      >Id</a
      ><a name="1087"
      > </a
      ><a name="1088" class="Symbol"
      >&#8594;</a
      ><a name="1089"
      > </a
      ><a name="1090" href="Stlc.html#976" class="Datatype"
      >Type</a
      ><a name="1094"
      > </a
      ><a name="1095" class="Symbol"
      >&#8594;</a
      ><a name="1096"
      > </a
      ><a name="1097" href="Stlc.html#1037" class="Datatype"
      >Term</a
      ><a name="1101"
      > </a
      ><a name="1102" class="Symbol"
      >&#8594;</a
      ><a name="1103"
      > </a
      ><a name="1104" href="Stlc.html#1037" class="Datatype"
      >Term</a
      ><a name="1108"
      >
  </a
      ><a name="1111" href="Stlc.html#1111" class="InductiveConstructor Operator"
      >_&#183;&#7488;_</a
      ><a name="1115"
      > </a
      ><a name="1116" class="Symbol"
      >:</a
      ><a name="1117"
      > </a
      ><a name="1118" href="Stlc.html#1037" class="Datatype"
      >Term</a
      ><a name="1122"
      > </a
      ><a name="1123" class="Symbol"
      >&#8594;</a
      ><a name="1124"
      > </a
      ><a name="1125" href="Stlc.html#1037" class="Datatype"
      >Term</a
      ><a name="1129"
      > </a
      ><a name="1130" class="Symbol"
      >&#8594;</a
      ><a name="1131"
      > </a
      ><a name="1132" href="Stlc.html#1037" class="Datatype"
      >Term</a
      ><a name="1136"
      >
  </a
      ><a name="1139" href="Stlc.html#1139" class="InductiveConstructor"
      >true&#7488;</a
      ><a name="1144"
      > </a
      ><a name="1145" class="Symbol"
      >:</a
      ><a name="1146"
      > </a
      ><a name="1147" href="Stlc.html#1037" class="Datatype"
      >Term</a
      ><a name="1151"
      >
  </a
      ><a name="1154" href="Stlc.html#1154" class="InductiveConstructor"
      >false&#7488;</a
      ><a name="1160"
      > </a
      ><a name="1161" class="Symbol"
      >:</a
      ><a name="1162"
      > </a
      ><a name="1163" href="Stlc.html#1037" class="Datatype"
      >Term</a
      ><a name="1167"
      >
  </a
      ><a name="1170" href="Stlc.html#1170" class="InductiveConstructor Operator"
      >if&#7488;_then_else_</a
      ><a name="1184"
      > </a
      ><a name="1185" class="Symbol"
      >:</a
      ><a name="1186"
      > </a
      ><a name="1187" href="Stlc.html#1037" class="Datatype"
      >Term</a
      ><a name="1191"
      > </a
      ><a name="1192" class="Symbol"
      >&#8594;</a
      ><a name="1193"
      > </a
      ><a name="1194" href="Stlc.html#1037" class="Datatype"
      >Term</a
      ><a name="1198"
      > </a
      ><a name="1199" class="Symbol"
      >&#8594;</a
      ><a name="1200"
      > </a
      ><a name="1201" href="Stlc.html#1037" class="Datatype"
      >Term</a
      ><a name="1205"
      > </a
      ><a name="1206" class="Symbol"
      >&#8594;</a
      ><a name="1207"
      > </a
      ><a name="1208" href="Stlc.html#1037" class="Datatype"
      >Term</a
      >

</pre>

Some examples.
<pre class="Agda">

<a name="1253" href="Stlc.html#1253" class="Function"
      >f</a
      ><a name="1254"
      > </a
      ><a name="1255" href="Stlc.html#1255" class="Function"
      >x</a
      ><a name="1256"
      > </a
      ><a name="1257" href="Stlc.html#1257" class="Function"
      >y</a
      ><a name="1258"
      > </a
      ><a name="1259" class="Symbol"
      >:</a
      ><a name="1260"
      > </a
      ><a name="1261" href="Maps.html#2215" class="Datatype"
      >Id</a
      ><a name="1263"
      >
</a
      ><a name="1264" href="Stlc.html#1253" class="Function"
      >f</a
      ><a name="1265"
      >  </a
      ><a name="1267" class="Symbol"
      >=</a
      ><a name="1268"
      >  </a
      ><a name="1270" href="Maps.html#2232" class="InductiveConstructor"
      >id</a
      ><a name="1272"
      > </a
      ><a name="1273" class="String"
      >&quot;f&quot;</a
      ><a name="1276"
      >
</a
      ><a name="1277" href="Stlc.html#1255" class="Function"
      >x</a
      ><a name="1278"
      >  </a
      ><a name="1280" class="Symbol"
      >=</a
      ><a name="1281"
      >  </a
      ><a name="1283" href="Maps.html#2232" class="InductiveConstructor"
      >id</a
      ><a name="1285"
      > </a
      ><a name="1286" class="String"
      >&quot;x&quot;</a
      ><a name="1289"
      >
</a
      ><a name="1290" href="Stlc.html#1257" class="Function"
      >y</a
      ><a name="1291"
      >  </a
      ><a name="1293" class="Symbol"
      >=</a
      ><a name="1294"
      >  </a
      ><a name="1296" href="Maps.html#2232" class="InductiveConstructor"
      >id</a
      ><a name="1298"
      > </a
      ><a name="1299" class="String"
      >&quot;y&quot;</a
      ><a name="1302"
      >

</a
      ><a name="1304" href="Stlc.html#1304" class="Function"
      >I[&#120121;]</a
      ><a name="1308"
      > </a
      ><a name="1309" href="Stlc.html#1309" class="Function"
      >I[&#120121;&#8658;&#120121;]</a
      ><a name="1315"
      > </a
      ><a name="1316" href="Stlc.html#1316" class="Function"
      >K[&#120121;][&#120121;]</a
      ><a name="1323"
      > </a
      ><a name="1324" href="Stlc.html#1324" class="Function"
      >not[&#120121;]</a
      ><a name="1330"
      > </a
      ><a name="1331" class="Symbol"
      >:</a
      ><a name="1332"
      > </a
      ><a name="1333" href="Stlc.html#1037" class="Datatype"
      >Term</a
      ><a name="1337"
      > 
</a
      ><a name="1339" href="Stlc.html#1304" class="Function"
      >I[&#120121;]</a
      ><a name="1343"
      >  </a
      ><a name="1345" class="Symbol"
      >=</a
      ><a name="1346"
      >  </a
      ><a name="1348" class="Symbol"
      >(</a
      ><a name="1349" href="Stlc.html#1075" class="InductiveConstructor Operator"
      >&#955;&#7488;</a
      ><a name="1351"
      > </a
      ><a name="1352" href="Stlc.html#1255" class="Function"
      >x</a
      ><a name="1353"
      > </a
      ><a name="1354" href="Stlc.html#1075" class="InductiveConstructor Operator"
      >&#8712;</a
      ><a name="1355"
      > </a
      ><a name="1356" href="Stlc.html#995" class="InductiveConstructor"
      >&#120121;</a
      ><a name="1357"
      > </a
      ><a name="1358" href="Stlc.html#1075" class="InductiveConstructor Operator"
      >&#8658;</a
      ><a name="1359"
      > </a
      ><a name="1360" class="Symbol"
      >(</a
      ><a name="1361" href="Stlc.html#1056" class="InductiveConstructor"
      >var&#7488;</a
      ><a name="1365"
      > </a
      ><a name="1366" href="Stlc.html#1255" class="Function"
      >x</a
      ><a name="1367" class="Symbol"
      >))</a
      ><a name="1369"
      >
</a
      ><a name="1370" href="Stlc.html#1309" class="Function"
      >I[&#120121;&#8658;&#120121;]</a
      ><a name="1376"
      >  </a
      ><a name="1378" class="Symbol"
      >=</a
      ><a name="1379"
      >  </a
      ><a name="1381" class="Symbol"
      >(</a
      ><a name="1382" href="Stlc.html#1075" class="InductiveConstructor Operator"
      >&#955;&#7488;</a
      ><a name="1384"
      > </a
      ><a name="1385" href="Stlc.html#1253" class="Function"
      >f</a
      ><a name="1386"
      > </a
      ><a name="1387" href="Stlc.html#1075" class="InductiveConstructor Operator"
      >&#8712;</a
      ><a name="1388"
      > </a
      ><a name="1389" class="Symbol"
      >(</a
      ><a name="1390" href="Stlc.html#995" class="InductiveConstructor"
      >&#120121;</a
      ><a name="1391"
      > </a
      ><a name="1392" href="Stlc.html#1006" class="InductiveConstructor Operator"
      >&#8658;</a
      ><a name="1393"
      > </a
      ><a name="1394" href="Stlc.html#995" class="InductiveConstructor"
      >&#120121;</a
      ><a name="1395" class="Symbol"
      >)</a
      ><a name="1396"
      > </a
      ><a name="1397" href="Stlc.html#1075" class="InductiveConstructor Operator"
      >&#8658;</a
      ><a name="1398"
      > </a
      ><a name="1399" class="Symbol"
      >(</a
      ><a name="1400" href="Stlc.html#1075" class="InductiveConstructor Operator"
      >&#955;&#7488;</a
      ><a name="1402"
      > </a
      ><a name="1403" href="Stlc.html#1255" class="Function"
      >x</a
      ><a name="1404"
      > </a
      ><a name="1405" href="Stlc.html#1075" class="InductiveConstructor Operator"
      >&#8712;</a
      ><a name="1406"
      > </a
      ><a name="1407" href="Stlc.html#995" class="InductiveConstructor"
      >&#120121;</a
      ><a name="1408"
      > </a
      ><a name="1409" href="Stlc.html#1075" class="InductiveConstructor Operator"
      >&#8658;</a
      ><a name="1410"
      > </a
      ><a name="1411" class="Symbol"
      >((</a
      ><a name="1413" href="Stlc.html#1056" class="InductiveConstructor"
      >var&#7488;</a
      ><a name="1417"
      > </a
      ><a name="1418" href="Stlc.html#1253" class="Function"
      >f</a
      ><a name="1419" class="Symbol"
      >)</a
      ><a name="1420"
      > </a
      ><a name="1421" href="Stlc.html#1111" class="InductiveConstructor Operator"
      >&#183;&#7488;</a
      ><a name="1423"
      > </a
      ><a name="1424" class="Symbol"
      >(</a
      ><a name="1425" href="Stlc.html#1056" class="InductiveConstructor"
      >var&#7488;</a
      ><a name="1429"
      > </a
      ><a name="1430" href="Stlc.html#1255" class="Function"
      >x</a
      ><a name="1431" class="Symbol"
      >))))</a
      ><a name="1435"
      >
</a
      ><a name="1436" href="Stlc.html#1316" class="Function"
      >K[&#120121;][&#120121;]</a
      ><a name="1443"
      >  </a
      ><a name="1445" class="Symbol"
      >=</a
      ><a name="1446"
      >  </a
      ><a name="1448" class="Symbol"
      >(</a
      ><a name="1449" href="Stlc.html#1075" class="InductiveConstructor Operator"
      >&#955;&#7488;</a
      ><a name="1451"
      > </a
      ><a name="1452" href="Stlc.html#1255" class="Function"
      >x</a
      ><a name="1453"
      > </a
      ><a name="1454" href="Stlc.html#1075" class="InductiveConstructor Operator"
      >&#8712;</a
      ><a name="1455"
      > </a
      ><a name="1456" href="Stlc.html#995" class="InductiveConstructor"
      >&#120121;</a
      ><a name="1457"
      > </a
      ><a name="1458" href="Stlc.html#1075" class="InductiveConstructor Operator"
      >&#8658;</a
      ><a name="1459"
      > </a
      ><a name="1460" class="Symbol"
      >(</a
      ><a name="1461" href="Stlc.html#1075" class="InductiveConstructor Operator"
      >&#955;&#7488;</a
      ><a name="1463"
      > </a
      ><a name="1464" href="Stlc.html#1257" class="Function"
      >y</a
      ><a name="1465"
      > </a
      ><a name="1466" href="Stlc.html#1075" class="InductiveConstructor Operator"
      >&#8712;</a
      ><a name="1467"
      > </a
      ><a name="1468" href="Stlc.html#995" class="InductiveConstructor"
      >&#120121;</a
      ><a name="1469"
      > </a
      ><a name="1470" href="Stlc.html#1075" class="InductiveConstructor Operator"
      >&#8658;</a
      ><a name="1471"
      > </a
      ><a name="1472" class="Symbol"
      >(</a
      ><a name="1473" href="Stlc.html#1056" class="InductiveConstructor"
      >var&#7488;</a
      ><a name="1477"
      > </a
      ><a name="1478" href="Stlc.html#1255" class="Function"
      >x</a
      ><a name="1479" class="Symbol"
      >)))</a
      ><a name="1482"
      >
</a
      ><a name="1483" href="Stlc.html#1324" class="Function"
      >not[&#120121;]</a
      ><a name="1489"
      >  </a
      ><a name="1491" class="Symbol"
      >=</a
      ><a name="1492"
      >  </a
      ><a name="1494" class="Symbol"
      >(</a
      ><a name="1495" href="Stlc.html#1075" class="InductiveConstructor Operator"
      >&#955;&#7488;</a
      ><a name="1497"
      > </a
      ><a name="1498" href="Stlc.html#1255" class="Function"
      >x</a
      ><a name="1499"
      > </a
      ><a name="1500" href="Stlc.html#1075" class="InductiveConstructor Operator"
      >&#8712;</a
      ><a name="1501"
      > </a
      ><a name="1502" href="Stlc.html#995" class="InductiveConstructor"
      >&#120121;</a
      ><a name="1503"
      > </a
      ><a name="1504" href="Stlc.html#1075" class="InductiveConstructor Operator"
      >&#8658;</a
      ><a name="1505"
      > </a
      ><a name="1506" class="Symbol"
      >(</a
      ><a name="1507" href="Stlc.html#1170" class="InductiveConstructor Operator"
      >if&#7488;</a
      ><a name="1510"
      > </a
      ><a name="1511" class="Symbol"
      >(</a
      ><a name="1512" href="Stlc.html#1056" class="InductiveConstructor"
      >var&#7488;</a
      ><a name="1516"
      > </a
      ><a name="1517" href="Stlc.html#1255" class="Function"
      >x</a
      ><a name="1518" class="Symbol"
      >)</a
      ><a name="1519"
      > </a
      ><a name="1520" href="Stlc.html#1170" class="InductiveConstructor Operator"
      >then</a
      ><a name="1524"
      > </a
      ><a name="1525" href="Stlc.html#1154" class="InductiveConstructor"
      >false&#7488;</a
      ><a name="1531"
      > </a
      ><a name="1532" href="Stlc.html#1170" class="InductiveConstructor Operator"
      >else</a
      ><a name="1536"
      > </a
      ><a name="1537" href="Stlc.html#1139" class="InductiveConstructor"
      >true&#7488;</a
      ><a name="1542" class="Symbol"
      >))</a
      >

</pre>

## Values

<pre class="Agda">

<a name="1581" class="Keyword"
      >data</a
      ><a name="1585"
      > </a
      ><a name="1586" href="Stlc.html#1586" class="Datatype"
      >value</a
      ><a name="1591"
      > </a
      ><a name="1592" class="Symbol"
      >:</a
      ><a name="1593"
      > </a
      ><a name="1594" href="Stlc.html#1037" class="Datatype"
      >Term</a
      ><a name="1598"
      > </a
      ><a name="1599" class="Symbol"
      >&#8594;</a
      ><a name="1600"
      > </a
      ><a name="1601" class="PrimitiveType"
      >Set</a
      ><a name="1604"
      > </a
      ><a name="1605" class="Keyword"
      >where</a
      ><a name="1610"
      >
  </a
      ><a name="1613" href="Stlc.html#1613" class="InductiveConstructor"
      >value-&#955;&#7488;</a
      ><a name="1621"
      > </a
      ><a name="1622" class="Symbol"
      >:</a
      ><a name="1623"
      > </a
      ><a name="1624" class="Symbol"
      >&#8704;</a
      ><a name="1625"
      > </a
      ><a name="1626" class="Symbol"
      >{</a
      ><a name="1627" href="Stlc.html#1627" class="Bound"
      >x</a
      ><a name="1628"
      > </a
      ><a name="1629" href="Stlc.html#1629" class="Bound"
      >A</a
      ><a name="1630"
      > </a
      ><a name="1631" href="Stlc.html#1631" class="Bound"
      >N</a
      ><a name="1632" class="Symbol"
      >}</a
      ><a name="1633"
      > </a
      ><a name="1634" class="Symbol"
      >&#8594;</a
      ><a name="1635"
      > </a
      ><a name="1636" href="Stlc.html#1586" class="Datatype"
      >value</a
      ><a name="1641"
      > </a
      ><a name="1642" class="Symbol"
      >(</a
      ><a name="1643" href="Stlc.html#1075" class="InductiveConstructor Operator"
      >&#955;&#7488;</a
      ><a name="1645"
      > </a
      ><a name="1646" href="Stlc.html#1627" class="Bound"
      >x</a
      ><a name="1647"
      > </a
      ><a name="1648" href="Stlc.html#1075" class="InductiveConstructor Operator"
      >&#8712;</a
      ><a name="1649"
      > </a
      ><a name="1650" href="Stlc.html#1629" class="Bound"
      >A</a
      ><a name="1651"
      > </a
      ><a name="1652" href="Stlc.html#1075" class="InductiveConstructor Operator"
      >&#8658;</a
      ><a name="1653"
      > </a
      ><a name="1654" href="Stlc.html#1631" class="Bound"
      >N</a
      ><a name="1655" class="Symbol"
      >)</a
      ><a name="1656"
      >
  </a
      ><a name="1659" href="Stlc.html#1659" class="InductiveConstructor"
      >value-true&#7488;</a
      ><a name="1670"
      > </a
      ><a name="1671" class="Symbol"
      >:</a
      ><a name="1672"
      > </a
      ><a name="1673" href="Stlc.html#1586" class="Datatype"
      >value</a
      ><a name="1678"
      > </a
      ><a name="1679" class="Symbol"
      >(</a
      ><a name="1680" href="Stlc.html#1139" class="InductiveConstructor"
      >true&#7488;</a
      ><a name="1685" class="Symbol"
      >)</a
      ><a name="1686"
      >
  </a
      ><a name="1689" href="Stlc.html#1689" class="InductiveConstructor"
      >value-false&#7488;</a
      ><a name="1701"
      > </a
      ><a name="1702" class="Symbol"
      >:</a
      ><a name="1703"
      > </a
      ><a name="1704" href="Stlc.html#1586" class="Datatype"
      >value</a
      ><a name="1709"
      > </a
      ><a name="1710" class="Symbol"
      >(</a
      ><a name="1711" href="Stlc.html#1154" class="InductiveConstructor"
      >false&#7488;</a
      ><a name="1717" class="Symbol"
      >)</a
      >

</pre>

## Substitution

<pre class="Agda">

<a name="1761" href="Stlc.html#1761" class="Function Operator"
      >_[_:=_]</a
      ><a name="1768"
      > </a
      ><a name="1769" class="Symbol"
      >:</a
      ><a name="1770"
      > </a
      ><a name="1771" href="Stlc.html#1037" class="Datatype"
      >Term</a
      ><a name="1775"
      > </a
      ><a name="1776" class="Symbol"
      >&#8594;</a
      ><a name="1777"
      > </a
      ><a name="1778" href="Maps.html#2215" class="Datatype"
      >Id</a
      ><a name="1780"
      > </a
      ><a name="1781" class="Symbol"
      >&#8594;</a
      ><a name="1782"
      > </a
      ><a name="1783" href="Stlc.html#1037" class="Datatype"
      >Term</a
      ><a name="1787"
      > </a
      ><a name="1788" class="Symbol"
      >&#8594;</a
      ><a name="1789"
      > </a
      ><a name="1790" href="Stlc.html#1037" class="Datatype"
      >Term</a
      ><a name="1794"
      >
</a
      ><a name="1795" class="Symbol"
      >(</a
      ><a name="1796" href="Stlc.html#1056" class="InductiveConstructor"
      >var&#7488;</a
      ><a name="1800"
      > </a
      ><a name="1801" href="Stlc.html#1801" class="Bound"
      >x&#8242;</a
      ><a name="1803" class="Symbol"
      >)</a
      ><a name="1804"
      > </a
      ><a name="1805" href="Stlc.html#1761" class="Function Operator"
      >[</a
      ><a name="1806"
      > </a
      ><a name="1807" href="Stlc.html#1807" class="Bound"
      >x</a
      ><a name="1808"
      > </a
      ><a name="1809" href="Stlc.html#1761" class="Function Operator"
      >:=</a
      ><a name="1811"
      > </a
      ><a name="1812" href="Stlc.html#1812" class="Bound"
      >V</a
      ><a name="1813"
      > </a
      ><a name="1814" href="Stlc.html#1761" class="Function Operator"
      >]</a
      ><a name="1815"
      > </a
      ><a name="1816" class="Keyword"
      >with</a
      ><a name="1820"
      > </a
      ><a name="1821" href="Stlc.html#1807" class="Bound"
      >x</a
      ><a name="1822"
      > </a
      ><a name="1823" href="Maps.html#2558" class="Function Operator"
      >&#8799;</a
      ><a name="1824"
      > </a
      ><a name="1825" href="Stlc.html#1801" class="Bound"
      >x&#8242;</a
      ><a name="1827"
      >
</a
      ><a name="1828" class="Symbol"
      >...</a
      ><a name="1831"
      > </a
      ><a name="1832" class="Symbol"
      >|</a
      ><a name="1833"
      > </a
      ><a name="1834" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#520" class="InductiveConstructor"
      >yes</a
      ><a name="1837"
      > </a
      ><a name="1838" class="Symbol"
      >_</a
      ><a name="1839"
      > </a
      ><a name="1840" class="Symbol"
      >=</a
      ><a name="1841"
      > </a
      ><a name="1842" href="Stlc.html#1812" class="Bound"
      >V</a
      ><a name="1843"
      >
</a
      ><a name="1844" class="Symbol"
      >...</a
      ><a name="1847"
      > </a
      ><a name="1848" class="Symbol"
      >|</a
      ><a name="1849"
      > </a
      ><a name="1850" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#547" class="InductiveConstructor"
      >no</a
      ><a name="1852"
      >  </a
      ><a name="1854" class="Symbol"
      >_</a
      ><a name="1855"
      > </a
      ><a name="1856" class="Symbol"
      >=</a
      ><a name="1857"
      > </a
      ><a name="1858" href="Stlc.html#1056" class="InductiveConstructor"
      >var&#7488;</a
      ><a name="1862"
      > </a
      ><a name="1863" href="Stlc.html#1801" class="Bound"
      >x&#8242;</a
      ><a name="1865"
      >
</a
      ><a name="1866" class="Symbol"
      >(</a
      ><a name="1867" href="Stlc.html#1075" class="InductiveConstructor Operator"
      >&#955;&#7488;</a
      ><a name="1869"
      > </a
      ><a name="1870" href="Stlc.html#1870" class="Bound"
      >x&#8242;</a
      ><a name="1872"
      > </a
      ><a name="1873" href="Stlc.html#1075" class="InductiveConstructor Operator"
      >&#8712;</a
      ><a name="1874"
      > </a
      ><a name="1875" href="Stlc.html#1875" class="Bound"
      >A&#8242;</a
      ><a name="1877"
      > </a
      ><a name="1878" href="Stlc.html#1075" class="InductiveConstructor Operator"
      >&#8658;</a
      ><a name="1879"
      > </a
      ><a name="1880" href="Stlc.html#1880" class="Bound"
      >N&#8242;</a
      ><a name="1882" class="Symbol"
      >)</a
      ><a name="1883"
      > </a
      ><a name="1884" href="Stlc.html#1761" class="Function Operator"
      >[</a
      ><a name="1885"
      > </a
      ><a name="1886" href="Stlc.html#1886" class="Bound"
      >x</a
      ><a name="1887"
      > </a
      ><a name="1888" href="Stlc.html#1761" class="Function Operator"
      >:=</a
      ><a name="1890"
      > </a
      ><a name="1891" href="Stlc.html#1891" class="Bound"
      >V</a
      ><a name="1892"
      > </a
      ><a name="1893" href="Stlc.html#1761" class="Function Operator"
      >]</a
      ><a name="1894"
      > </a
      ><a name="1895" class="Keyword"
      >with</a
      ><a name="1899"
      > </a
      ><a name="1900" href="Stlc.html#1886" class="Bound"
      >x</a
      ><a name="1901"
      > </a
      ><a name="1902" href="Maps.html#2558" class="Function Operator"
      >&#8799;</a
      ><a name="1903"
      > </a
      ><a name="1904" href="Stlc.html#1870" class="Bound"
      >x&#8242;</a
      ><a name="1906"
      >
</a
      ><a name="1907" class="Symbol"
      >...</a
      ><a name="1910"
      > </a
      ><a name="1911" class="Symbol"
      >|</a
      ><a name="1912"
      > </a
      ><a name="1913" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#520" class="InductiveConstructor"
      >yes</a
      ><a name="1916"
      > </a
      ><a name="1917" class="Symbol"
      >_</a
      ><a name="1918"
      > </a
      ><a name="1919" class="Symbol"
      >=</a
      ><a name="1920"
      > </a
      ><a name="1921" href="Stlc.html#1075" class="InductiveConstructor Operator"
      >&#955;&#7488;</a
      ><a name="1923"
      > </a
      ><a name="1924" href="Stlc.html#1870" class="Bound"
      >x&#8242;</a
      ><a name="1926"
      > </a
      ><a name="1927" href="Stlc.html#1075" class="InductiveConstructor Operator"
      >&#8712;</a
      ><a name="1928"
      > </a
      ><a name="1929" href="Stlc.html#1875" class="Bound"
      >A&#8242;</a
      ><a name="1931"
      > </a
      ><a name="1932" href="Stlc.html#1075" class="InductiveConstructor Operator"
      >&#8658;</a
      ><a name="1933"
      > </a
      ><a name="1934" href="Stlc.html#1880" class="Bound"
      >N&#8242;</a
      ><a name="1936"
      >
</a
      ><a name="1937" class="Symbol"
      >...</a
      ><a name="1940"
      > </a
      ><a name="1941" class="Symbol"
      >|</a
      ><a name="1942"
      > </a
      ><a name="1943" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#547" class="InductiveConstructor"
      >no</a
      ><a name="1945"
      >  </a
      ><a name="1947" class="Symbol"
      >_</a
      ><a name="1948"
      > </a
      ><a name="1949" class="Symbol"
      >=</a
      ><a name="1950"
      > </a
      ><a name="1951" href="Stlc.html#1075" class="InductiveConstructor Operator"
      >&#955;&#7488;</a
      ><a name="1953"
      > </a
      ><a name="1954" href="Stlc.html#1870" class="Bound"
      >x&#8242;</a
      ><a name="1956"
      > </a
      ><a name="1957" href="Stlc.html#1075" class="InductiveConstructor Operator"
      >&#8712;</a
      ><a name="1958"
      > </a
      ><a name="1959" href="Stlc.html#1875" class="Bound"
      >A&#8242;</a
      ><a name="1961"
      > </a
      ><a name="1962" href="Stlc.html#1075" class="InductiveConstructor Operator"
      >&#8658;</a
      ><a name="1963"
      > </a
      ><a name="1964" class="Symbol"
      >(</a
      ><a name="1965" href="Stlc.html#1880" class="Bound"
      >N&#8242;</a
      ><a name="1967"
      > </a
      ><a name="1968" href="Stlc.html#1761" class="Function Operator"
      >[</a
      ><a name="1969"
      > </a
      ><a name="1970" href="Stlc.html#1886" class="Bound"
      >x</a
      ><a name="1971"
      > </a
      ><a name="1972" href="Stlc.html#1761" class="Function Operator"
      >:=</a
      ><a name="1974"
      > </a
      ><a name="1975" href="Stlc.html#1891" class="Bound"
      >V</a
      ><a name="1976"
      > </a
      ><a name="1977" href="Stlc.html#1761" class="Function Operator"
      >]</a
      ><a name="1978" class="Symbol"
      >)</a
      ><a name="1979"
      >
</a
      ><a name="1980" class="Symbol"
      >(</a
      ><a name="1981" href="Stlc.html#1981" class="Bound"
      >L&#8242;</a
      ><a name="1983"
      > </a
      ><a name="1984" href="Stlc.html#1111" class="InductiveConstructor Operator"
      >&#183;&#7488;</a
      ><a name="1986"
      > </a
      ><a name="1987" href="Stlc.html#1987" class="Bound"
      >M&#8242;</a
      ><a name="1989" class="Symbol"
      >)</a
      ><a name="1990"
      > </a
      ><a name="1991" href="Stlc.html#1761" class="Function Operator"
      >[</a
      ><a name="1992"
      > </a
      ><a name="1993" href="Stlc.html#1993" class="Bound"
      >x</a
      ><a name="1994"
      > </a
      ><a name="1995" href="Stlc.html#1761" class="Function Operator"
      >:=</a
      ><a name="1997"
      > </a
      ><a name="1998" href="Stlc.html#1998" class="Bound"
      >V</a
      ><a name="1999"
      > </a
      ><a name="2000" href="Stlc.html#1761" class="Function Operator"
      >]</a
      ><a name="2001"
      > </a
      ><a name="2002" class="Symbol"
      >=</a
      ><a name="2003"
      >  </a
      ><a name="2005" class="Symbol"
      >(</a
      ><a name="2006" href="Stlc.html#1981" class="Bound"
      >L&#8242;</a
      ><a name="2008"
      > </a
      ><a name="2009" href="Stlc.html#1761" class="Function Operator"
      >[</a
      ><a name="2010"
      > </a
      ><a name="2011" href="Stlc.html#1993" class="Bound"
      >x</a
      ><a name="2012"
      > </a
      ><a name="2013" href="Stlc.html#1761" class="Function Operator"
      >:=</a
      ><a name="2015"
      > </a
      ><a name="2016" href="Stlc.html#1998" class="Bound"
      >V</a
      ><a name="2017"
      > </a
      ><a name="2018" href="Stlc.html#1761" class="Function Operator"
      >]</a
      ><a name="2019" class="Symbol"
      >)</a
      ><a name="2020"
      > </a
      ><a name="2021" href="Stlc.html#1111" class="InductiveConstructor Operator"
      >&#183;&#7488;</a
      ><a name="2023"
      > </a
      ><a name="2024" class="Symbol"
      >(</a
      ><a name="2025" href="Stlc.html#1987" class="Bound"
      >M&#8242;</a
      ><a name="2027"
      > </a
      ><a name="2028" href="Stlc.html#1761" class="Function Operator"
      >[</a
      ><a name="2029"
      > </a
      ><a name="2030" href="Stlc.html#1993" class="Bound"
      >x</a
      ><a name="2031"
      > </a
      ><a name="2032" href="Stlc.html#1761" class="Function Operator"
      >:=</a
      ><a name="2034"
      > </a
      ><a name="2035" href="Stlc.html#1998" class="Bound"
      >V</a
      ><a name="2036"
      > </a
      ><a name="2037" href="Stlc.html#1761" class="Function Operator"
      >]</a
      ><a name="2038" class="Symbol"
      >)</a
      ><a name="2039"
      >
</a
      ><a name="2040" class="Symbol"
      >(</a
      ><a name="2041" href="Stlc.html#1139" class="InductiveConstructor"
      >true&#7488;</a
      ><a name="2046" class="Symbol"
      >)</a
      ><a name="2047"
      > </a
      ><a name="2048" href="Stlc.html#1761" class="Function Operator"
      >[</a
      ><a name="2049"
      > </a
      ><a name="2050" href="Stlc.html#2050" class="Bound"
      >x</a
      ><a name="2051"
      > </a
      ><a name="2052" href="Stlc.html#1761" class="Function Operator"
      >:=</a
      ><a name="2054"
      > </a
      ><a name="2055" href="Stlc.html#2055" class="Bound"
      >V</a
      ><a name="2056"
      > </a
      ><a name="2057" href="Stlc.html#1761" class="Function Operator"
      >]</a
      ><a name="2058"
      > </a
      ><a name="2059" class="Symbol"
      >=</a
      ><a name="2060"
      > </a
      ><a name="2061" href="Stlc.html#1139" class="InductiveConstructor"
      >true&#7488;</a
      ><a name="2066"
      >
</a
      ><a name="2067" class="Symbol"
      >(</a
      ><a name="2068" href="Stlc.html#1154" class="InductiveConstructor"
      >false&#7488;</a
      ><a name="2074" class="Symbol"
      >)</a
      ><a name="2075"
      > </a
      ><a name="2076" href="Stlc.html#1761" class="Function Operator"
      >[</a
      ><a name="2077"
      > </a
      ><a name="2078" href="Stlc.html#2078" class="Bound"
      >x</a
      ><a name="2079"
      > </a
      ><a name="2080" href="Stlc.html#1761" class="Function Operator"
      >:=</a
      ><a name="2082"
      > </a
      ><a name="2083" href="Stlc.html#2083" class="Bound"
      >V</a
      ><a name="2084"
      > </a
      ><a name="2085" href="Stlc.html#1761" class="Function Operator"
      >]</a
      ><a name="2086"
      > </a
      ><a name="2087" class="Symbol"
      >=</a
      ><a name="2088"
      > </a
      ><a name="2089" href="Stlc.html#1154" class="InductiveConstructor"
      >false&#7488;</a
      ><a name="2095"
      >
</a
      ><a name="2096" class="Symbol"
      >(</a
      ><a name="2097" href="Stlc.html#1170" class="InductiveConstructor Operator"
      >if&#7488;</a
      ><a name="2100"
      > </a
      ><a name="2101" href="Stlc.html#2101" class="Bound"
      >L&#8242;</a
      ><a name="2103"
      > </a
      ><a name="2104" href="Stlc.html#1170" class="InductiveConstructor Operator"
      >then</a
      ><a name="2108"
      > </a
      ><a name="2109" href="Stlc.html#2109" class="Bound"
      >M&#8242;</a
      ><a name="2111"
      > </a
      ><a name="2112" href="Stlc.html#1170" class="InductiveConstructor Operator"
      >else</a
      ><a name="2116"
      > </a
      ><a name="2117" href="Stlc.html#2117" class="Bound"
      >N&#8242;</a
      ><a name="2119" class="Symbol"
      >)</a
      ><a name="2120"
      > </a
      ><a name="2121" href="Stlc.html#1761" class="Function Operator"
      >[</a
      ><a name="2122"
      > </a
      ><a name="2123" href="Stlc.html#2123" class="Bound"
      >x</a
      ><a name="2124"
      > </a
      ><a name="2125" href="Stlc.html#1761" class="Function Operator"
      >:=</a
      ><a name="2127"
      > </a
      ><a name="2128" href="Stlc.html#2128" class="Bound"
      >V</a
      ><a name="2129"
      > </a
      ><a name="2130" href="Stlc.html#1761" class="Function Operator"
      >]</a
      ><a name="2131"
      > </a
      ><a name="2132" class="Symbol"
      >=</a
      ><a name="2133"
      > </a
      ><a name="2134" href="Stlc.html#1170" class="InductiveConstructor Operator"
      >if&#7488;</a
      ><a name="2137"
      > </a
      ><a name="2138" class="Symbol"
      >(</a
      ><a name="2139" href="Stlc.html#2101" class="Bound"
      >L&#8242;</a
      ><a name="2141"
      > </a
      ><a name="2142" href="Stlc.html#1761" class="Function Operator"
      >[</a
      ><a name="2143"
      > </a
      ><a name="2144" href="Stlc.html#2123" class="Bound"
      >x</a
      ><a name="2145"
      > </a
      ><a name="2146" href="Stlc.html#1761" class="Function Operator"
      >:=</a
      ><a name="2148"
      > </a
      ><a name="2149" href="Stlc.html#2128" class="Bound"
      >V</a
      ><a name="2150"
      > </a
      ><a name="2151" href="Stlc.html#1761" class="Function Operator"
      >]</a
      ><a name="2152" class="Symbol"
      >)</a
      ><a name="2153"
      > </a
      ><a name="2154" href="Stlc.html#1170" class="InductiveConstructor Operator"
      >then</a
      ><a name="2158"
      > </a
      ><a name="2159" class="Symbol"
      >(</a
      ><a name="2160" href="Stlc.html#2109" class="Bound"
      >M&#8242;</a
      ><a name="2162"
      > </a
      ><a name="2163" href="Stlc.html#1761" class="Function Operator"
      >[</a
      ><a name="2164"
      > </a
      ><a name="2165" href="Stlc.html#2123" class="Bound"
      >x</a
      ><a name="2166"
      > </a
      ><a name="2167" href="Stlc.html#1761" class="Function Operator"
      >:=</a
      ><a name="2169"
      > </a
      ><a name="2170" href="Stlc.html#2128" class="Bound"
      >V</a
      ><a name="2171"
      > </a
      ><a name="2172" href="Stlc.html#1761" class="Function Operator"
      >]</a
      ><a name="2173" class="Symbol"
      >)</a
      ><a name="2174"
      > </a
      ><a name="2175" href="Stlc.html#1170" class="InductiveConstructor Operator"
      >else</a
      ><a name="2179"
      > </a
      ><a name="2180" class="Symbol"
      >(</a
      ><a name="2181" href="Stlc.html#2117" class="Bound"
      >N&#8242;</a
      ><a name="2183"
      > </a
      ><a name="2184" href="Stlc.html#1761" class="Function Operator"
      >[</a
      ><a name="2185"
      > </a
      ><a name="2186" href="Stlc.html#2123" class="Bound"
      >x</a
      ><a name="2187"
      > </a
      ><a name="2188" href="Stlc.html#1761" class="Function Operator"
      >:=</a
      ><a name="2190"
      > </a
      ><a name="2191" href="Stlc.html#2128" class="Bound"
      >V</a
      ><a name="2192"
      > </a
      ><a name="2193" href="Stlc.html#1761" class="Function Operator"
      >]</a
      ><a name="2194" class="Symbol"
      >)</a
      >

</pre>

## Reduction rules

<pre class="Agda">

<a name="2241" class="Keyword"
      >data</a
      ><a name="2245"
      > </a
      ><a name="2246" href="Stlc.html#2246" class="Datatype Operator"
      >_&#10233;_</a
      ><a name="2249"
      > </a
      ><a name="2250" class="Symbol"
      >:</a
      ><a name="2251"
      > </a
      ><a name="2252" href="Stlc.html#1037" class="Datatype"
      >Term</a
      ><a name="2256"
      > </a
      ><a name="2257" class="Symbol"
      >&#8594;</a
      ><a name="2258"
      > </a
      ><a name="2259" href="Stlc.html#1037" class="Datatype"
      >Term</a
      ><a name="2263"
      > </a
      ><a name="2264" class="Symbol"
      >&#8594;</a
      ><a name="2265"
      > </a
      ><a name="2266" class="PrimitiveType"
      >Set</a
      ><a name="2269"
      > </a
      ><a name="2270" class="Keyword"
      >where</a
      ><a name="2275"
      >
  </a
      ><a name="2278" href="Stlc.html#2278" class="InductiveConstructor"
      >&#946;&#8658;</a
      ><a name="2280"
      > </a
      ><a name="2281" class="Symbol"
      >:</a
      ><a name="2282"
      > </a
      ><a name="2283" class="Symbol"
      >&#8704;</a
      ><a name="2284"
      > </a
      ><a name="2285" class="Symbol"
      >{</a
      ><a name="2286" href="Stlc.html#2286" class="Bound"
      >x</a
      ><a name="2287"
      > </a
      ><a name="2288" href="Stlc.html#2288" class="Bound"
      >A</a
      ><a name="2289"
      > </a
      ><a name="2290" href="Stlc.html#2290" class="Bound"
      >N</a
      ><a name="2291"
      > </a
      ><a name="2292" href="Stlc.html#2292" class="Bound"
      >V</a
      ><a name="2293" class="Symbol"
      >}</a
      ><a name="2294"
      > </a
      ><a name="2295" class="Symbol"
      >&#8594;</a
      ><a name="2296"
      > </a
      ><a name="2297" href="Stlc.html#1586" class="Datatype"
      >value</a
      ><a name="2302"
      > </a
      ><a name="2303" href="Stlc.html#2292" class="Bound"
      >V</a
      ><a name="2304"
      > </a
      ><a name="2305" class="Symbol"
      >&#8594;</a
      ><a name="2306"
      >
    </a
      ><a name="2311" class="Symbol"
      >((</a
      ><a name="2313" href="Stlc.html#1075" class="InductiveConstructor Operator"
      >&#955;&#7488;</a
      ><a name="2315"
      > </a
      ><a name="2316" href="Stlc.html#2286" class="Bound"
      >x</a
      ><a name="2317"
      > </a
      ><a name="2318" href="Stlc.html#1075" class="InductiveConstructor Operator"
      >&#8712;</a
      ><a name="2319"
      > </a
      ><a name="2320" href="Stlc.html#2288" class="Bound"
      >A</a
      ><a name="2321"
      > </a
      ><a name="2322" href="Stlc.html#1075" class="InductiveConstructor Operator"
      >&#8658;</a
      ><a name="2323"
      > </a
      ><a name="2324" href="Stlc.html#2290" class="Bound"
      >N</a
      ><a name="2325" class="Symbol"
      >)</a
      ><a name="2326"
      > </a
      ><a name="2327" href="Stlc.html#1111" class="InductiveConstructor Operator"
      >&#183;&#7488;</a
      ><a name="2329"
      > </a
      ><a name="2330" href="Stlc.html#2292" class="Bound"
      >V</a
      ><a name="2331" class="Symbol"
      >)</a
      ><a name="2332"
      > </a
      ><a name="2333" href="Stlc.html#2246" class="Datatype Operator"
      >&#10233;</a
      ><a name="2334"
      > </a
      ><a name="2335" class="Symbol"
      >(</a
      ><a name="2336" href="Stlc.html#2290" class="Bound"
      >N</a
      ><a name="2337"
      > </a
      ><a name="2338" href="Stlc.html#1761" class="Function Operator"
      >[</a
      ><a name="2339"
      > </a
      ><a name="2340" href="Stlc.html#2286" class="Bound"
      >x</a
      ><a name="2341"
      > </a
      ><a name="2342" href="Stlc.html#1761" class="Function Operator"
      >:=</a
      ><a name="2344"
      > </a
      ><a name="2345" href="Stlc.html#2292" class="Bound"
      >V</a
      ><a name="2346"
      > </a
      ><a name="2347" href="Stlc.html#1761" class="Function Operator"
      >]</a
      ><a name="2348" class="Symbol"
      >)</a
      ><a name="2349"
      >
  </a
      ><a name="2352" href="Stlc.html#2352" class="InductiveConstructor"
      >&#947;&#8658;&#8321;</a
      ><a name="2355"
      > </a
      ><a name="2356" class="Symbol"
      >:</a
      ><a name="2357"
      > </a
      ><a name="2358" class="Symbol"
      >&#8704;</a
      ><a name="2359"
      > </a
      ><a name="2360" class="Symbol"
      >{</a
      ><a name="2361" href="Stlc.html#2361" class="Bound"
      >L</a
      ><a name="2362"
      > </a
      ><a name="2363" href="Stlc.html#2363" class="Bound"
      >L'</a
      ><a name="2365"
      > </a
      ><a name="2366" href="Stlc.html#2366" class="Bound"
      >M</a
      ><a name="2367" class="Symbol"
      >}</a
      ><a name="2368"
      > </a
      ><a name="2369" class="Symbol"
      >&#8594;</a
      ><a name="2370"
      >
    </a
      ><a name="2375" href="Stlc.html#2361" class="Bound"
      >L</a
      ><a name="2376"
      > </a
      ><a name="2377" href="Stlc.html#2246" class="Datatype Operator"
      >&#10233;</a
      ><a name="2378"
      > </a
      ><a name="2379" href="Stlc.html#2363" class="Bound"
      >L'</a
      ><a name="2381"
      > </a
      ><a name="2382" class="Symbol"
      >&#8594;</a
      ><a name="2383"
      >
    </a
      ><a name="2388" class="Symbol"
      >(</a
      ><a name="2389" href="Stlc.html#2361" class="Bound"
      >L</a
      ><a name="2390"
      > </a
      ><a name="2391" href="Stlc.html#1111" class="InductiveConstructor Operator"
      >&#183;&#7488;</a
      ><a name="2393"
      > </a
      ><a name="2394" href="Stlc.html#2366" class="Bound"
      >M</a
      ><a name="2395" class="Symbol"
      >)</a
      ><a name="2396"
      > </a
      ><a name="2397" href="Stlc.html#2246" class="Datatype Operator"
      >&#10233;</a
      ><a name="2398"
      > </a
      ><a name="2399" class="Symbol"
      >(</a
      ><a name="2400" href="Stlc.html#2363" class="Bound"
      >L'</a
      ><a name="2402"
      > </a
      ><a name="2403" href="Stlc.html#1111" class="InductiveConstructor Operator"
      >&#183;&#7488;</a
      ><a name="2405"
      > </a
      ><a name="2406" href="Stlc.html#2366" class="Bound"
      >M</a
      ><a name="2407" class="Symbol"
      >)</a
      ><a name="2408"
      >
  </a
      ><a name="2411" href="Stlc.html#2411" class="InductiveConstructor"
      >&#947;&#8658;&#8322;</a
      ><a name="2414"
      > </a
      ><a name="2415" class="Symbol"
      >:</a
      ><a name="2416"
      > </a
      ><a name="2417" class="Symbol"
      >&#8704;</a
      ><a name="2418"
      > </a
      ><a name="2419" class="Symbol"
      >{</a
      ><a name="2420" href="Stlc.html#2420" class="Bound"
      >V</a
      ><a name="2421"
      > </a
      ><a name="2422" href="Stlc.html#2422" class="Bound"
      >M</a
      ><a name="2423"
      > </a
      ><a name="2424" href="Stlc.html#2424" class="Bound"
      >M'</a
      ><a name="2426" class="Symbol"
      >}</a
      ><a name="2427"
      > </a
      ><a name="2428" class="Symbol"
      >&#8594;</a
      ><a name="2429"
      >
    </a
      ><a name="2434" href="Stlc.html#1586" class="Datatype"
      >value</a
      ><a name="2439"
      > </a
      ><a name="2440" href="Stlc.html#2420" class="Bound"
      >V</a
      ><a name="2441"
      > </a
      ><a name="2442" class="Symbol"
      >&#8594;</a
      ><a name="2443"
      >
    </a
      ><a name="2448" href="Stlc.html#2422" class="Bound"
      >M</a
      ><a name="2449"
      > </a
      ><a name="2450" href="Stlc.html#2246" class="Datatype Operator"
      >&#10233;</a
      ><a name="2451"
      > </a
      ><a name="2452" href="Stlc.html#2424" class="Bound"
      >M'</a
      ><a name="2454"
      > </a
      ><a name="2455" class="Symbol"
      >&#8594;</a
      ><a name="2456"
      >
    </a
      ><a name="2461" class="Symbol"
      >(</a
      ><a name="2462" href="Stlc.html#2420" class="Bound"
      >V</a
      ><a name="2463"
      > </a
      ><a name="2464" href="Stlc.html#1111" class="InductiveConstructor Operator"
      >&#183;&#7488;</a
      ><a name="2466"
      > </a
      ><a name="2467" href="Stlc.html#2422" class="Bound"
      >M</a
      ><a name="2468" class="Symbol"
      >)</a
      ><a name="2469"
      > </a
      ><a name="2470" href="Stlc.html#2246" class="Datatype Operator"
      >&#10233;</a
      ><a name="2471"
      > </a
      ><a name="2472" class="Symbol"
      >(</a
      ><a name="2473" href="Stlc.html#2420" class="Bound"
      >V</a
      ><a name="2474"
      > </a
      ><a name="2475" href="Stlc.html#1111" class="InductiveConstructor Operator"
      >&#183;&#7488;</a
      ><a name="2477"
      > </a
      ><a name="2478" href="Stlc.html#2424" class="Bound"
      >M'</a
      ><a name="2480" class="Symbol"
      >)</a
      ><a name="2481"
      >
  </a
      ><a name="2484" href="Stlc.html#2484" class="InductiveConstructor"
      >&#946;&#120121;&#8321;</a
      ><a name="2487"
      > </a
      ><a name="2488" class="Symbol"
      >:</a
      ><a name="2489"
      > </a
      ><a name="2490" class="Symbol"
      >&#8704;</a
      ><a name="2491"
      > </a
      ><a name="2492" class="Symbol"
      >{</a
      ><a name="2493" href="Stlc.html#2493" class="Bound"
      >M</a
      ><a name="2494"
      > </a
      ><a name="2495" href="Stlc.html#2495" class="Bound"
      >N</a
      ><a name="2496" class="Symbol"
      >}</a
      ><a name="2497"
      > </a
      ><a name="2498" class="Symbol"
      >&#8594;</a
      ><a name="2499"
      >
    </a
      ><a name="2504" class="Symbol"
      >(</a
      ><a name="2505" href="Stlc.html#1170" class="InductiveConstructor Operator"
      >if&#7488;</a
      ><a name="2508"
      > </a
      ><a name="2509" href="Stlc.html#1139" class="InductiveConstructor"
      >true&#7488;</a
      ><a name="2514"
      > </a
      ><a name="2515" href="Stlc.html#1170" class="InductiveConstructor Operator"
      >then</a
      ><a name="2519"
      > </a
      ><a name="2520" href="Stlc.html#2493" class="Bound"
      >M</a
      ><a name="2521"
      > </a
      ><a name="2522" href="Stlc.html#1170" class="InductiveConstructor Operator"
      >else</a
      ><a name="2526"
      > </a
      ><a name="2527" href="Stlc.html#2495" class="Bound"
      >N</a
      ><a name="2528" class="Symbol"
      >)</a
      ><a name="2529"
      > </a
      ><a name="2530" href="Stlc.html#2246" class="Datatype Operator"
      >&#10233;</a
      ><a name="2531"
      > </a
      ><a name="2532" href="Stlc.html#2493" class="Bound"
      >M</a
      ><a name="2533"
      >
  </a
      ><a name="2536" href="Stlc.html#2536" class="InductiveConstructor"
      >&#946;&#120121;&#8322;</a
      ><a name="2539"
      > </a
      ><a name="2540" class="Symbol"
      >:</a
      ><a name="2541"
      > </a
      ><a name="2542" class="Symbol"
      >&#8704;</a
      ><a name="2543"
      > </a
      ><a name="2544" class="Symbol"
      >{</a
      ><a name="2545" href="Stlc.html#2545" class="Bound"
      >M</a
      ><a name="2546"
      > </a
      ><a name="2547" href="Stlc.html#2547" class="Bound"
      >N</a
      ><a name="2548" class="Symbol"
      >}</a
      ><a name="2549"
      > </a
      ><a name="2550" class="Symbol"
      >&#8594;</a
      ><a name="2551"
      >
    </a
      ><a name="2556" class="Symbol"
      >(</a
      ><a name="2557" href="Stlc.html#1170" class="InductiveConstructor Operator"
      >if&#7488;</a
      ><a name="2560"
      > </a
      ><a name="2561" href="Stlc.html#1154" class="InductiveConstructor"
      >false&#7488;</a
      ><a name="2567"
      > </a
      ><a name="2568" href="Stlc.html#1170" class="InductiveConstructor Operator"
      >then</a
      ><a name="2572"
      > </a
      ><a name="2573" href="Stlc.html#2545" class="Bound"
      >M</a
      ><a name="2574"
      > </a
      ><a name="2575" href="Stlc.html#1170" class="InductiveConstructor Operator"
      >else</a
      ><a name="2579"
      > </a
      ><a name="2580" href="Stlc.html#2547" class="Bound"
      >N</a
      ><a name="2581" class="Symbol"
      >)</a
      ><a name="2582"
      > </a
      ><a name="2583" href="Stlc.html#2246" class="Datatype Operator"
      >&#10233;</a
      ><a name="2584"
      > </a
      ><a name="2585" href="Stlc.html#2547" class="Bound"
      >N</a
      ><a name="2586"
      >
  </a
      ><a name="2589" href="Stlc.html#2589" class="InductiveConstructor"
      >&#947;&#120121;</a
      ><a name="2591"
      > </a
      ><a name="2592" class="Symbol"
      >:</a
      ><a name="2593"
      > </a
      ><a name="2594" class="Symbol"
      >&#8704;</a
      ><a name="2595"
      > </a
      ><a name="2596" class="Symbol"
      >{</a
      ><a name="2597" href="Stlc.html#2597" class="Bound"
      >L</a
      ><a name="2598"
      > </a
      ><a name="2599" href="Stlc.html#2599" class="Bound"
      >L'</a
      ><a name="2601"
      > </a
      ><a name="2602" href="Stlc.html#2602" class="Bound"
      >M</a
      ><a name="2603"
      > </a
      ><a name="2604" href="Stlc.html#2604" class="Bound"
      >N</a
      ><a name="2605" class="Symbol"
      >}</a
      ><a name="2606"
      > </a
      ><a name="2607" class="Symbol"
      >&#8594;</a
      ><a name="2608"
      >
    </a
      ><a name="2613" href="Stlc.html#2597" class="Bound"
      >L</a
      ><a name="2614"
      > </a
      ><a name="2615" href="Stlc.html#2246" class="Datatype Operator"
      >&#10233;</a
      ><a name="2616"
      > </a
      ><a name="2617" href="Stlc.html#2599" class="Bound"
      >L'</a
      ><a name="2619"
      > </a
      ><a name="2620" class="Symbol"
      >&#8594;</a
      ><a name="2621"
      >    
    </a
      ><a name="2630" class="Symbol"
      >(</a
      ><a name="2631" href="Stlc.html#1170" class="InductiveConstructor Operator"
      >if&#7488;</a
      ><a name="2634"
      > </a
      ><a name="2635" href="Stlc.html#2597" class="Bound"
      >L</a
      ><a name="2636"
      > </a
      ><a name="2637" href="Stlc.html#1170" class="InductiveConstructor Operator"
      >then</a
      ><a name="2641"
      > </a
      ><a name="2642" href="Stlc.html#2602" class="Bound"
      >M</a
      ><a name="2643"
      > </a
      ><a name="2644" href="Stlc.html#1170" class="InductiveConstructor Operator"
      >else</a
      ><a name="2648"
      > </a
      ><a name="2649" href="Stlc.html#2604" class="Bound"
      >N</a
      ><a name="2650" class="Symbol"
      >)</a
      ><a name="2651"
      > </a
      ><a name="2652" href="Stlc.html#2246" class="Datatype Operator"
      >&#10233;</a
      ><a name="2653"
      > </a
      ><a name="2654" class="Symbol"
      >(</a
      ><a name="2655" href="Stlc.html#1170" class="InductiveConstructor Operator"
      >if&#7488;</a
      ><a name="2658"
      > </a
      ><a name="2659" href="Stlc.html#2599" class="Bound"
      >L'</a
      ><a name="2661"
      > </a
      ><a name="2662" href="Stlc.html#1170" class="InductiveConstructor Operator"
      >then</a
      ><a name="2666"
      > </a
      ><a name="2667" href="Stlc.html#2602" class="Bound"
      >M</a
      ><a name="2668"
      > </a
      ><a name="2669" href="Stlc.html#1170" class="InductiveConstructor Operator"
      >else</a
      ><a name="2673"
      > </a
      ><a name="2674" href="Stlc.html#2604" class="Bound"
      >N</a
      ><a name="2675" class="Symbol"
      >)</a
      >

</pre>

## Reflexive and transitive closure of a relation

<pre class="Agda">

<a name="2753" href="Stlc.html#2753" class="Function"
      >Rel</a
      ><a name="2756"
      > </a
      ><a name="2757" class="Symbol"
      >:</a
      ><a name="2758"
      > </a
      ><a name="2759" class="PrimitiveType"
      >Set</a
      ><a name="2762"
      > </a
      ><a name="2763" class="Symbol"
      >&#8594;</a
      ><a name="2764"
      > </a
      ><a name="2765" class="PrimitiveType"
      >Set&#8321;</a
      ><a name="2769"
      >
</a
      ><a name="2770" href="Stlc.html#2753" class="Function"
      >Rel</a
      ><a name="2773"
      > </a
      ><a name="2774" href="Stlc.html#2774" class="Bound"
      >A</a
      ><a name="2775"
      > </a
      ><a name="2776" class="Symbol"
      >=</a
      ><a name="2777"
      > </a
      ><a name="2778" href="Stlc.html#2774" class="Bound"
      >A</a
      ><a name="2779"
      > </a
      ><a name="2780" class="Symbol"
      >&#8594;</a
      ><a name="2781"
      > </a
      ><a name="2782" href="Stlc.html#2774" class="Bound"
      >A</a
      ><a name="2783"
      > </a
      ><a name="2784" class="Symbol"
      >&#8594;</a
      ><a name="2785"
      > </a
      ><a name="2786" class="PrimitiveType"
      >Set</a
      ><a name="2789"
      >

</a
      ><a name="2791" class="Keyword"
      >infixl</a
      ><a name="2797"
      > </a
      ><a name="2798" class="Number"
      >100</a
      ><a name="2801"
      > </a
      ><a name="2802" href="Stlc.html#2923" class="InductiveConstructor Operator"
      >_&gt;&gt;_</a
      ><a name="2806"
      >

</a
      ><a name="2808" class="Keyword"
      >data</a
      ><a name="2812"
      > </a
      ><a name="2813" href="Stlc.html#2813" class="Datatype Operator"
      >_*</a
      ><a name="2815"
      > </a
      ><a name="2816" class="Symbol"
      >{</a
      ><a name="2817" href="Stlc.html#2817" class="Bound"
      >A</a
      ><a name="2818"
      > </a
      ><a name="2819" class="Symbol"
      >:</a
      ><a name="2820"
      > </a
      ><a name="2821" class="PrimitiveType"
      >Set</a
      ><a name="2824" class="Symbol"
      >}</a
      ><a name="2825"
      > </a
      ><a name="2826" class="Symbol"
      >(</a
      ><a name="2827" href="Stlc.html#2827" class="Bound"
      >R</a
      ><a name="2828"
      > </a
      ><a name="2829" class="Symbol"
      >:</a
      ><a name="2830"
      > </a
      ><a name="2831" href="Stlc.html#2753" class="Function"
      >Rel</a
      ><a name="2834"
      > </a
      ><a name="2835" href="Stlc.html#2817" class="Bound"
      >A</a
      ><a name="2836" class="Symbol"
      >)</a
      ><a name="2837"
      > </a
      ><a name="2838" class="Symbol"
      >:</a
      ><a name="2839"
      > </a
      ><a name="2840" href="Stlc.html#2753" class="Function"
      >Rel</a
      ><a name="2843"
      > </a
      ><a name="2844" href="Stlc.html#2817" class="Bound"
      >A</a
      ><a name="2845"
      > </a
      ><a name="2846" class="Keyword"
      >where</a
      ><a name="2851"
      >
  </a
      ><a name="2854" href="Stlc.html#2854" class="InductiveConstructor"
      >&#10216;&#10217;</a
      ><a name="2856"
      > </a
      ><a name="2857" class="Symbol"
      >:</a
      ><a name="2858"
      > </a
      ><a name="2859" class="Symbol"
      >&#8704;</a
      ><a name="2860"
      > </a
      ><a name="2861" class="Symbol"
      >{</a
      ><a name="2862" href="Stlc.html#2862" class="Bound"
      >x</a
      ><a name="2863"
      > </a
      ><a name="2864" class="Symbol"
      >:</a
      ><a name="2865"
      > </a
      ><a name="2866" href="Stlc.html#2817" class="Bound"
      >A</a
      ><a name="2867" class="Symbol"
      >}</a
      ><a name="2868"
      > </a
      ><a name="2869" class="Symbol"
      >&#8594;</a
      ><a name="2870"
      > </a
      ><a name="2871" class="Symbol"
      >(</a
      ><a name="2872" href="Stlc.html#2827" class="Bound"
      >R</a
      ><a name="2873"
      > </a
      ><a name="2874" href="Stlc.html#2813" class="Datatype Operator"
      >*</a
      ><a name="2875" class="Symbol"
      >)</a
      ><a name="2876"
      > </a
      ><a name="2877" href="Stlc.html#2862" class="Bound"
      >x</a
      ><a name="2878"
      > </a
      ><a name="2879" href="Stlc.html#2862" class="Bound"
      >x</a
      ><a name="2880"
      >
  </a
      ><a name="2883" href="Stlc.html#2883" class="InductiveConstructor Operator"
      >&#10216;_&#10217;</a
      ><a name="2886"
      > </a
      ><a name="2887" class="Symbol"
      >:</a
      ><a name="2888"
      > </a
      ><a name="2889" class="Symbol"
      >&#8704;</a
      ><a name="2890"
      > </a
      ><a name="2891" class="Symbol"
      >{</a
      ><a name="2892" href="Stlc.html#2892" class="Bound"
      >x</a
      ><a name="2893"
      > </a
      ><a name="2894" href="Stlc.html#2894" class="Bound"
      >y</a
      ><a name="2895"
      > </a
      ><a name="2896" class="Symbol"
      >:</a
      ><a name="2897"
      > </a
      ><a name="2898" href="Stlc.html#2817" class="Bound"
      >A</a
      ><a name="2899" class="Symbol"
      >}</a
      ><a name="2900"
      > </a
      ><a name="2901" class="Symbol"
      >&#8594;</a
      ><a name="2902"
      > </a
      ><a name="2903" href="Stlc.html#2827" class="Bound"
      >R</a
      ><a name="2904"
      > </a
      ><a name="2905" href="Stlc.html#2892" class="Bound"
      >x</a
      ><a name="2906"
      > </a
      ><a name="2907" href="Stlc.html#2894" class="Bound"
      >y</a
      ><a name="2908"
      > </a
      ><a name="2909" class="Symbol"
      >&#8594;</a
      ><a name="2910"
      > </a
      ><a name="2911" class="Symbol"
      >(</a
      ><a name="2912" href="Stlc.html#2827" class="Bound"
      >R</a
      ><a name="2913"
      > </a
      ><a name="2914" href="Stlc.html#2813" class="Datatype Operator"
      >*</a
      ><a name="2915" class="Symbol"
      >)</a
      ><a name="2916"
      > </a
      ><a name="2917" href="Stlc.html#2892" class="Bound"
      >x</a
      ><a name="2918"
      > </a
      ><a name="2919" href="Stlc.html#2894" class="Bound"
      >y</a
      ><a name="2920"
      >
  </a
      ><a name="2923" href="Stlc.html#2923" class="InductiveConstructor Operator"
      >_&gt;&gt;_</a
      ><a name="2927"
      > </a
      ><a name="2928" class="Symbol"
      >:</a
      ><a name="2929"
      > </a
      ><a name="2930" class="Symbol"
      >&#8704;</a
      ><a name="2931"
      > </a
      ><a name="2932" class="Symbol"
      >{</a
      ><a name="2933" href="Stlc.html#2933" class="Bound"
      >x</a
      ><a name="2934"
      > </a
      ><a name="2935" href="Stlc.html#2935" class="Bound"
      >y</a
      ><a name="2936"
      > </a
      ><a name="2937" href="Stlc.html#2937" class="Bound"
      >z</a
      ><a name="2938"
      > </a
      ><a name="2939" class="Symbol"
      >:</a
      ><a name="2940"
      > </a
      ><a name="2941" href="Stlc.html#2817" class="Bound"
      >A</a
      ><a name="2942" class="Symbol"
      >}</a
      ><a name="2943"
      > </a
      ><a name="2944" class="Symbol"
      >&#8594;</a
      ><a name="2945"
      > </a
      ><a name="2946" class="Symbol"
      >(</a
      ><a name="2947" href="Stlc.html#2827" class="Bound"
      >R</a
      ><a name="2948"
      > </a
      ><a name="2949" href="Stlc.html#2813" class="Datatype Operator"
      >*</a
      ><a name="2950" class="Symbol"
      >)</a
      ><a name="2951"
      > </a
      ><a name="2952" href="Stlc.html#2933" class="Bound"
      >x</a
      ><a name="2953"
      > </a
      ><a name="2954" href="Stlc.html#2935" class="Bound"
      >y</a
      ><a name="2955"
      > </a
      ><a name="2956" class="Symbol"
      >&#8594;</a
      ><a name="2957"
      > </a
      ><a name="2958" class="Symbol"
      >(</a
      ><a name="2959" href="Stlc.html#2827" class="Bound"
      >R</a
      ><a name="2960"
      > </a
      ><a name="2961" href="Stlc.html#2813" class="Datatype Operator"
      >*</a
      ><a name="2962" class="Symbol"
      >)</a
      ><a name="2963"
      > </a
      ><a name="2964" href="Stlc.html#2935" class="Bound"
      >y</a
      ><a name="2965"
      > </a
      ><a name="2966" href="Stlc.html#2937" class="Bound"
      >z</a
      ><a name="2967"
      > </a
      ><a name="2968" class="Symbol"
      >&#8594;</a
      ><a name="2969"
      > </a
      ><a name="2970" class="Symbol"
      >(</a
      ><a name="2971" href="Stlc.html#2827" class="Bound"
      >R</a
      ><a name="2972"
      > </a
      ><a name="2973" href="Stlc.html#2813" class="Datatype Operator"
      >*</a
      ><a name="2974" class="Symbol"
      >)</a
      ><a name="2975"
      > </a
      ><a name="2976" href="Stlc.html#2933" class="Bound"
      >x</a
      ><a name="2977"
      > </a
      ><a name="2978" href="Stlc.html#2937" class="Bound"
      >z</a
      >

</pre>

<pre class="Agda">

<a name="3005" class="Keyword"
      >infix</a
      ><a name="3010"
      > </a
      ><a name="3011" class="Number"
      >80</a
      ><a name="3013"
      > </a
      ><a name="3014" href="Stlc.html#3020" class="Function Operator"
      >_&#10233;*_</a
      ><a name="3018"
      >

</a
      ><a name="3020" href="Stlc.html#3020" class="Function Operator"
      >_&#10233;*_</a
      ><a name="3024"
      > </a
      ><a name="3025" class="Symbol"
      >:</a
      ><a name="3026"
      > </a
      ><a name="3027" href="Stlc.html#1037" class="Datatype"
      >Term</a
      ><a name="3031"
      > </a
      ><a name="3032" class="Symbol"
      >&#8594;</a
      ><a name="3033"
      > </a
      ><a name="3034" href="Stlc.html#1037" class="Datatype"
      >Term</a
      ><a name="3038"
      > </a
      ><a name="3039" class="Symbol"
      >&#8594;</a
      ><a name="3040"
      > </a
      ><a name="3041" class="PrimitiveType"
      >Set</a
      ><a name="3044"
      >
</a
      ><a name="3045" href="Stlc.html#3020" class="Function Operator"
      >_&#10233;*_</a
      ><a name="3049"
      > </a
      ><a name="3050" class="Symbol"
      >=</a
      ><a name="3051"
      > </a
      ><a name="3052" class="Symbol"
      >(</a
      ><a name="3053" href="Stlc.html#2246" class="Datatype Operator"
      >_&#10233;_</a
      ><a name="3056" class="Symbol"
      >)</a
      ><a name="3057"
      > </a
      ><a name="3058" href="Stlc.html#2813" class="Datatype Operator"
      >*</a
      >

</pre>

<pre class="Agda">

<a name="3085" class="Keyword"
      >open</a
      ><a name="3089"
      > </a
      ><a name="3090" class="Keyword"
      >import</a
      ><a name="3096"
      > </a
      ><a name="3097" href="https://agda.github.io/agda-stdlib/Relation.Binary.html#1" class="Module"
      >Relation.Binary</a
      ><a name="3112"
      > </a
      ><a name="3113" class="Keyword"
      >using</a
      ><a name="3118"
      > </a
      ><a name="3119" class="Symbol"
      >(</a
      ><a name="3120" href="https://agda.github.io/agda-stdlib/Relation.Binary.html#1470" class="Record"
      >Preorder</a
      ><a name="3128" class="Symbol"
      >)</a
      ><a name="3129"
      >

</a
      ><a name="3131" href="Stlc.html#3131" class="Function"
      >&#10233;*-Preorder</a
      ><a name="3142"
      > </a
      ><a name="3143" class="Symbol"
      >:</a
      ><a name="3144"
      > </a
      ><a name="3145" href="https://agda.github.io/agda-stdlib/Relation.Binary.html#1470" class="Record"
      >Preorder</a
      ><a name="3153"
      > </a
      ><a name="3154" class="Symbol"
      >_</a
      ><a name="3155"
      > </a
      ><a name="3156" class="Symbol"
      >_</a
      ><a name="3157"
      > </a
      ><a name="3158" class="Symbol"
      >_</a
      ><a name="3159"
      >
</a
      ><a name="3160" href="Stlc.html#3131" class="Function"
      >&#10233;*-Preorder</a
      ><a name="3171"
      > </a
      ><a name="3172" class="Symbol"
      >=</a
      ><a name="3173"
      > </a
      ><a name="3174" class="Keyword"
      >record</a
      ><a name="3180"
      >
  </a
      ><a name="3183" class="Symbol"
      >{</a
      ><a name="3184"
      > </a
      ><a name="3185" class="Field"
      >Carrier</a
      ><a name="3192"
      >    </a
      ><a name="3196" class="Symbol"
      >=</a
      ><a name="3197"
      > </a
      ><a name="3198" href="Stlc.html#1037" class="Datatype"
      >Term</a
      ><a name="3202"
      >
  </a
      ><a name="3205" class="Symbol"
      >;</a
      ><a name="3206"
      > </a
      ><a name="3207" class="Field Operator"
      >_&#8776;_</a
      ><a name="3210"
      >        </a
      ><a name="3218" class="Symbol"
      >=</a
      ><a name="3219"
      > </a
      ><a name="3220" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >_&#8801;_</a
      ><a name="3223"
      >
  </a
      ><a name="3226" class="Symbol"
      >;</a
      ><a name="3227"
      > </a
      ><a name="3228" class="Field Operator"
      >_&#8764;_</a
      ><a name="3231"
      >        </a
      ><a name="3239" class="Symbol"
      >=</a
      ><a name="3240"
      > </a
      ><a name="3241" href="Stlc.html#3020" class="Function Operator"
      >_&#10233;*_</a
      ><a name="3245"
      >
  </a
      ><a name="3248" class="Symbol"
      >;</a
      ><a name="3249"
      > </a
      ><a name="3250" class="Field"
      >isPreorder</a
      ><a name="3260"
      > </a
      ><a name="3261" class="Symbol"
      >=</a
      ><a name="3262"
      > </a
      ><a name="3263" class="Keyword"
      >record</a
      ><a name="3269"
      >
    </a
      ><a name="3274" class="Symbol"
      >{</a
      ><a name="3275"
      > </a
      ><a name="3276" class="Field"
      >isEquivalence</a
      ><a name="3289"
      > </a
      ><a name="3290" class="Symbol"
      >=</a
      ><a name="3291"
      > </a
      ><a name="3292" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.Core.html#879" class="Function"
      >P.isEquivalence</a
      ><a name="3307"
      >
    </a
      ><a name="3312" class="Symbol"
      >;</a
      ><a name="3313"
      > </a
      ><a name="3314" class="Field"
      >reflexive</a
      ><a name="3323"
      >     </a
      ><a name="3328" class="Symbol"
      >=</a
      ><a name="3329"
      > </a
      ><a name="3330" class="Symbol"
      >&#955;</a
      ><a name="3331"
      > </a
      ><a name="3332" class="Symbol"
      >{</a
      ><a name="3333" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="3337"
      > </a
      ><a name="3338" class="Symbol"
      >&#8594;</a
      ><a name="3339"
      > </a
      ><a name="3340" href="Stlc.html#2854" class="InductiveConstructor"
      >&#10216;&#10217;</a
      ><a name="3342" class="Symbol"
      >}</a
      ><a name="3343"
      >
    </a
      ><a name="3348" class="Symbol"
      >;</a
      ><a name="3349"
      > </a
      ><a name="3350" class="Field"
      >trans</a
      ><a name="3355"
      >         </a
      ><a name="3364" class="Symbol"
      >=</a
      ><a name="3365"
      > </a
      ><a name="3366" href="Stlc.html#2923" class="InductiveConstructor Operator"
      >_&gt;&gt;_</a
      ><a name="3370"
      >
    </a
      ><a name="3375" class="Symbol"
      >}</a
      ><a name="3376"
      >
  </a
      ><a name="3379" class="Symbol"
      >}</a
      ><a name="3380"
      >

</a
      ><a name="3382" class="Keyword"
      >open</a
      ><a name="3386"
      > </a
      ><a name="3387" class="Keyword"
      >import</a
      ><a name="3393"
      > </a
      ><a name="3394" href="https://agda.github.io/agda-stdlib/Relation.Binary.PreorderReasoning.html#1" class="Module"
      >Relation.Binary.PreorderReasoning</a
      ><a name="3427"
      > </a
      ><a name="3428" href="Stlc.html#3131" class="Function"
      >&#10233;*-Preorder</a
      ><a name="3439"
      >
     </a
      ><a name="3445" class="Keyword"
      >using</a
      ><a name="3450"
      > </a
      ><a name="3451" class="Symbol"
      >(</a
      ><a name="3452"
      >begin_</a
      ><a name="3458" class="Symbol"
      >;</a
      ><a name="3459"
      > _&#8718;</a
      ><a name="3462" class="Symbol"
      >)</a
      ><a name="3463"
      > </a
      ><a name="3464" class="Keyword"
      >renaming</a
      ><a name="3472"
      > </a
      ><a name="3473" class="Symbol"
      >(</a
      ><a name="3474"
      >_&#8776;&#10216;_&#10217;_ </a
      ><a name="3481" class="Symbol"
      >to</a
      ><a name="3483"
      > _&#8801;&#10216;_&#10217;_</a
      ><a name="3490" class="Symbol"
      >;</a
      ><a name="3491"
      > _&#8764;&#10216;_&#10217;_ </a
      ><a name="3499" class="Symbol"
      >to</a
      ><a name="3501"
      > _&#10233;*&#10216;_&#10217;_</a
      ><a name="3509" class="Symbol"
      >)</a
      >

</pre>

Example evaluation.

<pre class="Agda">

<a name="3557" href="Stlc.html#3557" class="Function"
      >example&#8320;&#8242;</a
      ><a name="3566"
      > </a
      ><a name="3567" class="Symbol"
      >:</a
      ><a name="3568"
      > </a
      ><a name="3569" href="Stlc.html#1324" class="Function"
      >not[&#120121;]</a
      ><a name="3575"
      > </a
      ><a name="3576" href="Stlc.html#1111" class="InductiveConstructor Operator"
      >&#183;&#7488;</a
      ><a name="3578"
      > </a
      ><a name="3579" href="Stlc.html#1139" class="InductiveConstructor"
      >true&#7488;</a
      ><a name="3584"
      > </a
      ><a name="3585" href="Stlc.html#3020" class="Function Operator"
      >&#10233;*</a
      ><a name="3587"
      > </a
      ><a name="3588" href="Stlc.html#1154" class="InductiveConstructor"
      >false&#7488;</a
      ><a name="3594"
      >
</a
      ><a name="3595" href="Stlc.html#3557" class="Function"
      >example&#8320;&#8242;</a
      ><a name="3604"
      > </a
      ><a name="3605" class="Symbol"
      >=</a
      ><a name="3606"
      >
  </a
      ><a name="3609" href="https://agda.github.io/agda-stdlib/Relation.Binary.PreorderReasoning.html#1154" class="Function Operator"
      >begin</a
      ><a name="3614"
      >
    </a
      ><a name="3619" href="Stlc.html#1324" class="Function"
      >not[&#120121;]</a
      ><a name="3625"
      > </a
      ><a name="3626" href="Stlc.html#1111" class="InductiveConstructor Operator"
      >&#183;&#7488;</a
      ><a name="3628"
      > </a
      ><a name="3629" href="Stlc.html#1139" class="InductiveConstructor"
      >true&#7488;</a
      ><a name="3634"
      >
  </a
      ><a name="3637" href="https://agda.github.io/agda-stdlib/Relation.Binary.PreorderReasoning.html#1220" class="Function Operator"
      >&#10233;*&#10216;</a
      ><a name="3640"
      > </a
      ><a name="3641" href="Stlc.html#2883" class="InductiveConstructor Operator"
      >&#10216;</a
      ><a name="3642"
      > </a
      ><a name="3643" href="Stlc.html#2278" class="InductiveConstructor"
      >&#946;&#8658;</a
      ><a name="3645"
      > </a
      ><a name="3646" href="Stlc.html#1659" class="InductiveConstructor"
      >value-true&#7488;</a
      ><a name="3657"
      > </a
      ><a name="3658" href="Stlc.html#2883" class="InductiveConstructor Operator"
      >&#10217;</a
      ><a name="3659"
      > </a
      ><a name="3660" href="https://agda.github.io/agda-stdlib/Relation.Binary.PreorderReasoning.html#1220" class="Function Operator"
      >&#10217;</a
      ><a name="3661"
      >
    </a
      ><a name="3666" href="Stlc.html#1170" class="InductiveConstructor Operator"
      >if&#7488;</a
      ><a name="3669"
      > </a
      ><a name="3670" href="Stlc.html#1139" class="InductiveConstructor"
      >true&#7488;</a
      ><a name="3675"
      > </a
      ><a name="3676" href="Stlc.html#1170" class="InductiveConstructor Operator"
      >then</a
      ><a name="3680"
      > </a
      ><a name="3681" href="Stlc.html#1154" class="InductiveConstructor"
      >false&#7488;</a
      ><a name="3687"
      > </a
      ><a name="3688" href="Stlc.html#1170" class="InductiveConstructor Operator"
      >else</a
      ><a name="3692"
      > </a
      ><a name="3693" href="Stlc.html#1139" class="InductiveConstructor"
      >true&#7488;</a
      ><a name="3698"
      >
  </a
      ><a name="3701" href="https://agda.github.io/agda-stdlib/Relation.Binary.PreorderReasoning.html#1220" class="Function Operator"
      >&#10233;*&#10216;</a
      ><a name="3704"
      > </a
      ><a name="3705" href="Stlc.html#2883" class="InductiveConstructor Operator"
      >&#10216;</a
      ><a name="3706"
      > </a
      ><a name="3707" href="Stlc.html#2484" class="InductiveConstructor"
      >&#946;&#120121;&#8321;</a
      ><a name="3710"
      > </a
      ><a name="3711" href="Stlc.html#2883" class="InductiveConstructor Operator"
      >&#10217;</a
      ><a name="3712"
      > </a
      ><a name="3713" href="https://agda.github.io/agda-stdlib/Relation.Binary.PreorderReasoning.html#1220" class="Function Operator"
      >&#10217;</a
      ><a name="3714"
      >
    </a
      ><a name="3719" href="Stlc.html#1154" class="InductiveConstructor"
      >false&#7488;</a
      ><a name="3725"
      >
  </a
      ><a name="3728" href="https://agda.github.io/agda-stdlib/Relation.Binary.PreorderReasoning.html#1519" class="Function Operator"
      >&#8718;</a
      ><a name="3729"
      >

</a
      ><a name="3731" href="Stlc.html#3731" class="Function"
      >example&#8320;</a
      ><a name="3739"
      > </a
      ><a name="3740" class="Symbol"
      >:</a
      ><a name="3741"
      > </a
      ><a name="3742" class="Symbol"
      >(</a
      ><a name="3743" href="Stlc.html#1324" class="Function"
      >not[&#120121;]</a
      ><a name="3749"
      > </a
      ><a name="3750" href="Stlc.html#1111" class="InductiveConstructor Operator"
      >&#183;&#7488;</a
      ><a name="3752"
      > </a
      ><a name="3753" href="Stlc.html#1139" class="InductiveConstructor"
      >true&#7488;</a
      ><a name="3758" class="Symbol"
      >)</a
      ><a name="3759"
      > </a
      ><a name="3760" href="Stlc.html#3020" class="Function Operator"
      >&#10233;*</a
      ><a name="3762"
      > </a
      ><a name="3763" href="Stlc.html#1154" class="InductiveConstructor"
      >false&#7488;</a
      ><a name="3769"
      >
</a
      ><a name="3770" href="Stlc.html#3731" class="Function"
      >example&#8320;</a
      ><a name="3778"
      > </a
      ><a name="3779" class="Symbol"
      >=</a
      ><a name="3780"
      > </a
      ><a name="3781" href="Stlc.html#2883" class="InductiveConstructor Operator"
      >&#10216;</a
      ><a name="3782"
      > </a
      ><a name="3783" href="Stlc.html#3913" class="Function"
      >step&#8320;</a
      ><a name="3788"
      > </a
      ><a name="3789" href="Stlc.html#2883" class="InductiveConstructor Operator"
      >&#10217;</a
      ><a name="3790"
      > </a
      ><a name="3791" href="Stlc.html#2923" class="InductiveConstructor Operator"
      >&gt;&gt;</a
      ><a name="3793"
      > </a
      ><a name="3794" href="Stlc.html#2883" class="InductiveConstructor Operator"
      >&#10216;</a
      ><a name="3795"
      > </a
      ><a name="3796" href="Stlc.html#3956" class="Function"
      >step&#8321;</a
      ><a name="3801"
      > </a
      ><a name="3802" href="Stlc.html#2883" class="InductiveConstructor Operator"
      >&#10217;</a
      ><a name="3803"
      >
  </a
      ><a name="3806" class="Keyword"
      >where</a
      ><a name="3811"
      >
  </a
      ><a name="3814" href="Stlc.html#3814" class="Function"
      >M&#8320;</a
      ><a name="3816"
      > </a
      ><a name="3817" href="Stlc.html#3817" class="Function"
      >M&#8321;</a
      ><a name="3819"
      > </a
      ><a name="3820" href="Stlc.html#3820" class="Function"
      >M&#8322;</a
      ><a name="3822"
      > </a
      ><a name="3823" class="Symbol"
      >:</a
      ><a name="3824"
      > </a
      ><a name="3825" href="Stlc.html#1037" class="Datatype"
      >Term</a
      ><a name="3829"
      >
  </a
      ><a name="3832" href="Stlc.html#3814" class="Function"
      >M&#8320;</a
      ><a name="3834"
      > </a
      ><a name="3835" class="Symbol"
      >=</a
      ><a name="3836"
      > </a
      ><a name="3837" class="Symbol"
      >(</a
      ><a name="3838" href="Stlc.html#1324" class="Function"
      >not[&#120121;]</a
      ><a name="3844"
      > </a
      ><a name="3845" href="Stlc.html#1111" class="InductiveConstructor Operator"
      >&#183;&#7488;</a
      ><a name="3847"
      > </a
      ><a name="3848" href="Stlc.html#1139" class="InductiveConstructor"
      >true&#7488;</a
      ><a name="3853" class="Symbol"
      >)</a
      ><a name="3854"
      >
  </a
      ><a name="3857" href="Stlc.html#3817" class="Function"
      >M&#8321;</a
      ><a name="3859"
      > </a
      ><a name="3860" class="Symbol"
      >=</a
      ><a name="3861"
      > </a
      ><a name="3862" class="Symbol"
      >(</a
      ><a name="3863" href="Stlc.html#1170" class="InductiveConstructor Operator"
      >if&#7488;</a
      ><a name="3866"
      > </a
      ><a name="3867" href="Stlc.html#1139" class="InductiveConstructor"
      >true&#7488;</a
      ><a name="3872"
      > </a
      ><a name="3873" href="Stlc.html#1170" class="InductiveConstructor Operator"
      >then</a
      ><a name="3877"
      > </a
      ><a name="3878" href="Stlc.html#1154" class="InductiveConstructor"
      >false&#7488;</a
      ><a name="3884"
      > </a
      ><a name="3885" href="Stlc.html#1170" class="InductiveConstructor Operator"
      >else</a
      ><a name="3889"
      > </a
      ><a name="3890" href="Stlc.html#1139" class="InductiveConstructor"
      >true&#7488;</a
      ><a name="3895" class="Symbol"
      >)</a
      ><a name="3896"
      >
  </a
      ><a name="3899" href="Stlc.html#3820" class="Function"
      >M&#8322;</a
      ><a name="3901"
      > </a
      ><a name="3902" class="Symbol"
      >=</a
      ><a name="3903"
      > </a
      ><a name="3904" href="Stlc.html#1154" class="InductiveConstructor"
      >false&#7488;</a
      ><a name="3910"
      >
  </a
      ><a name="3913" href="Stlc.html#3913" class="Function"
      >step&#8320;</a
      ><a name="3918"
      > </a
      ><a name="3919" class="Symbol"
      >:</a
      ><a name="3920"
      > </a
      ><a name="3921" href="Stlc.html#3814" class="Function"
      >M&#8320;</a
      ><a name="3923"
      > </a
      ><a name="3924" href="Stlc.html#2246" class="Datatype Operator"
      >&#10233;</a
      ><a name="3925"
      > </a
      ><a name="3926" href="Stlc.html#3817" class="Function"
      >M&#8321;</a
      ><a name="3928"
      >
  </a
      ><a name="3931" href="Stlc.html#3913" class="Function"
      >step&#8320;</a
      ><a name="3936"
      > </a
      ><a name="3937" class="Symbol"
      >=</a
      ><a name="3938"
      > </a
      ><a name="3939" href="Stlc.html#2278" class="InductiveConstructor"
      >&#946;&#8658;</a
      ><a name="3941"
      > </a
      ><a name="3942" href="Stlc.html#1659" class="InductiveConstructor"
      >value-true&#7488;</a
      ><a name="3953"
      >
  </a
      ><a name="3956" href="Stlc.html#3956" class="Function"
      >step&#8321;</a
      ><a name="3961"
      > </a
      ><a name="3962" class="Symbol"
      >:</a
      ><a name="3963"
      > </a
      ><a name="3964" href="Stlc.html#3817" class="Function"
      >M&#8321;</a
      ><a name="3966"
      > </a
      ><a name="3967" href="Stlc.html#2246" class="Datatype Operator"
      >&#10233;</a
      ><a name="3968"
      > </a
      ><a name="3969" href="Stlc.html#3820" class="Function"
      >M&#8322;</a
      ><a name="3971"
      >
  </a
      ><a name="3974" href="Stlc.html#3956" class="Function"
      >step&#8321;</a
      ><a name="3979"
      > </a
      ><a name="3980" class="Symbol"
      >=</a
      ><a name="3981"
      > </a
      ><a name="3982" href="Stlc.html#2484" class="InductiveConstructor"
      >&#946;&#120121;&#8321;</a
      ><a name="3985"
      >

</a
      ><a name="3987" href="Stlc.html#3987" class="Function"
      >example&#8321;</a
      ><a name="3995"
      > </a
      ><a name="3996" class="Symbol"
      >:</a
      ><a name="3997"
      > </a
      ><a name="3998" class="Symbol"
      >(</a
      ><a name="3999" href="Stlc.html#1309" class="Function"
      >I[&#120121;&#8658;&#120121;]</a
      ><a name="4005"
      > </a
      ><a name="4006" href="Stlc.html#1111" class="InductiveConstructor Operator"
      >&#183;&#7488;</a
      ><a name="4008"
      > </a
      ><a name="4009" href="Stlc.html#1304" class="Function"
      >I[&#120121;]</a
      ><a name="4013"
      > </a
      ><a name="4014" href="Stlc.html#1111" class="InductiveConstructor Operator"
      >&#183;&#7488;</a
      ><a name="4016"
      > </a
      ><a name="4017" class="Symbol"
      >(</a
      ><a name="4018" href="Stlc.html#1324" class="Function"
      >not[&#120121;]</a
      ><a name="4024"
      > </a
      ><a name="4025" href="Stlc.html#1111" class="InductiveConstructor Operator"
      >&#183;&#7488;</a
      ><a name="4027"
      > </a
      ><a name="4028" href="Stlc.html#1154" class="InductiveConstructor"
      >false&#7488;</a
      ><a name="4034" class="Symbol"
      >))</a
      ><a name="4036"
      > </a
      ><a name="4037" href="Stlc.html#3020" class="Function Operator"
      >&#10233;*</a
      ><a name="4039"
      > </a
      ><a name="4040" href="Stlc.html#1139" class="InductiveConstructor"
      >true&#7488;</a
      ><a name="4045"
      >
</a
      ><a name="4046" href="Stlc.html#3987" class="Function"
      >example&#8321;</a
      ><a name="4054"
      > </a
      ><a name="4055" class="Symbol"
      >=</a
      ><a name="4056"
      > </a
      ><a name="4057" href="Stlc.html#2883" class="InductiveConstructor Operator"
      >&#10216;</a
      ><a name="4058"
      > </a
      ><a name="4059" href="Stlc.html#4423" class="Function"
      >step&#8320;</a
      ><a name="4064"
      > </a
      ><a name="4065" href="Stlc.html#2883" class="InductiveConstructor Operator"
      >&#10217;</a
      ><a name="4066"
      > </a
      ><a name="4067" href="Stlc.html#2923" class="InductiveConstructor Operator"
      >&gt;&gt;</a
      ><a name="4069"
      > </a
      ><a name="4070" href="Stlc.html#2883" class="InductiveConstructor Operator"
      >&#10216;</a
      ><a name="4071"
      > </a
      ><a name="4072" href="Stlc.html#4469" class="Function"
      >step&#8321;</a
      ><a name="4077"
      > </a
      ><a name="4078" href="Stlc.html#2883" class="InductiveConstructor Operator"
      >&#10217;</a
      ><a name="4079"
      > </a
      ><a name="4080" href="Stlc.html#2923" class="InductiveConstructor Operator"
      >&gt;&gt;</a
      ><a name="4082"
      > </a
      ><a name="4083" href="Stlc.html#2883" class="InductiveConstructor Operator"
      >&#10216;</a
      ><a name="4084"
      > </a
      ><a name="4085" href="Stlc.html#4528" class="Function"
      >step&#8322;</a
      ><a name="4090"
      > </a
      ><a name="4091" href="Stlc.html#2883" class="InductiveConstructor Operator"
      >&#10217;</a
      ><a name="4092"
      > </a
      ><a name="4093" href="Stlc.html#2923" class="InductiveConstructor Operator"
      >&gt;&gt;</a
      ><a name="4095"
      > </a
      ><a name="4096" href="Stlc.html#2883" class="InductiveConstructor Operator"
      >&#10216;</a
      ><a name="4097"
      > </a
      ><a name="4098" href="Stlc.html#4573" class="Function"
      >step&#8323;</a
      ><a name="4103"
      > </a
      ><a name="4104" href="Stlc.html#2883" class="InductiveConstructor Operator"
      >&#10217;</a
      ><a name="4105"
      > </a
      ><a name="4106" href="Stlc.html#2923" class="InductiveConstructor Operator"
      >&gt;&gt;</a
      ><a name="4108"
      > </a
      ><a name="4109" href="Stlc.html#2883" class="InductiveConstructor Operator"
      >&#10216;</a
      ><a name="4110"
      > </a
      ><a name="4111" href="Stlc.html#4625" class="Function"
      >step&#8324;</a
      ><a name="4116"
      > </a
      ><a name="4117" href="Stlc.html#2883" class="InductiveConstructor Operator"
      >&#10217;</a
      ><a name="4118"
      >
  </a
      ><a name="4121" class="Keyword"
      >where</a
      ><a name="4126"
      >
  </a
      ><a name="4129" href="Stlc.html#4129" class="Function"
      >M&#8320;</a
      ><a name="4131"
      > </a
      ><a name="4132" href="Stlc.html#4132" class="Function"
      >M&#8321;</a
      ><a name="4134"
      > </a
      ><a name="4135" href="Stlc.html#4135" class="Function"
      >M&#8322;</a
      ><a name="4137"
      > </a
      ><a name="4138" href="Stlc.html#4138" class="Function"
      >M&#8323;</a
      ><a name="4140"
      > </a
      ><a name="4141" href="Stlc.html#4141" class="Function"
      >M&#8324;</a
      ><a name="4143"
      > </a
      ><a name="4144" href="Stlc.html#4144" class="Function"
      >M&#8325;</a
      ><a name="4146"
      > </a
      ><a name="4147" class="Symbol"
      >:</a
      ><a name="4148"
      > </a
      ><a name="4149" href="Stlc.html#1037" class="Datatype"
      >Term</a
      ><a name="4153"
      >
  </a
      ><a name="4156" href="Stlc.html#4129" class="Function"
      >M&#8320;</a
      ><a name="4158"
      > </a
      ><a name="4159" class="Symbol"
      >=</a
      ><a name="4160"
      > </a
      ><a name="4161" class="Symbol"
      >(</a
      ><a name="4162" href="Stlc.html#1309" class="Function"
      >I[&#120121;&#8658;&#120121;]</a
      ><a name="4168"
      > </a
      ><a name="4169" href="Stlc.html#1111" class="InductiveConstructor Operator"
      >&#183;&#7488;</a
      ><a name="4171"
      > </a
      ><a name="4172" href="Stlc.html#1304" class="Function"
      >I[&#120121;]</a
      ><a name="4176"
      > </a
      ><a name="4177" href="Stlc.html#1111" class="InductiveConstructor Operator"
      >&#183;&#7488;</a
      ><a name="4179"
      > </a
      ><a name="4180" class="Symbol"
      >(</a
      ><a name="4181" href="Stlc.html#1324" class="Function"
      >not[&#120121;]</a
      ><a name="4187"
      > </a
      ><a name="4188" href="Stlc.html#1111" class="InductiveConstructor Operator"
      >&#183;&#7488;</a
      ><a name="4190"
      > </a
      ><a name="4191" href="Stlc.html#1154" class="InductiveConstructor"
      >false&#7488;</a
      ><a name="4197" class="Symbol"
      >))</a
      ><a name="4199"
      >
  </a
      ><a name="4202" href="Stlc.html#4132" class="Function"
      >M&#8321;</a
      ><a name="4204"
      > </a
      ><a name="4205" class="Symbol"
      >=</a
      ><a name="4206"
      > </a
      ><a name="4207" class="Symbol"
      >((</a
      ><a name="4209" href="Stlc.html#1075" class="InductiveConstructor Operator"
      >&#955;&#7488;</a
      ><a name="4211"
      > </a
      ><a name="4212" href="Stlc.html#1255" class="Function"
      >x</a
      ><a name="4213"
      > </a
      ><a name="4214" href="Stlc.html#1075" class="InductiveConstructor Operator"
      >&#8712;</a
      ><a name="4215"
      > </a
      ><a name="4216" href="Stlc.html#995" class="InductiveConstructor"
      >&#120121;</a
      ><a name="4217"
      > </a
      ><a name="4218" href="Stlc.html#1075" class="InductiveConstructor Operator"
      >&#8658;</a
      ><a name="4219"
      > </a
      ><a name="4220" class="Symbol"
      >(</a
      ><a name="4221" href="Stlc.html#1304" class="Function"
      >I[&#120121;]</a
      ><a name="4225"
      > </a
      ><a name="4226" href="Stlc.html#1111" class="InductiveConstructor Operator"
      >&#183;&#7488;</a
      ><a name="4228"
      > </a
      ><a name="4229" href="Stlc.html#1056" class="InductiveConstructor"
      >var&#7488;</a
      ><a name="4233"
      > </a
      ><a name="4234" href="Stlc.html#1255" class="Function"
      >x</a
      ><a name="4235" class="Symbol"
      >))</a
      ><a name="4237"
      > </a
      ><a name="4238" href="Stlc.html#1111" class="InductiveConstructor Operator"
      >&#183;&#7488;</a
      ><a name="4240"
      > </a
      ><a name="4241" class="Symbol"
      >(</a
      ><a name="4242" href="Stlc.html#1324" class="Function"
      >not[&#120121;]</a
      ><a name="4248"
      > </a
      ><a name="4249" href="Stlc.html#1111" class="InductiveConstructor Operator"
      >&#183;&#7488;</a
      ><a name="4251"
      > </a
      ><a name="4252" href="Stlc.html#1154" class="InductiveConstructor"
      >false&#7488;</a
      ><a name="4258" class="Symbol"
      >))</a
      ><a name="4260"
      >
  </a
      ><a name="4263" href="Stlc.html#4135" class="Function"
      >M&#8322;</a
      ><a name="4265"
      > </a
      ><a name="4266" class="Symbol"
      >=</a
      ><a name="4267"
      > </a
      ><a name="4268" class="Symbol"
      >((</a
      ><a name="4270" href="Stlc.html#1075" class="InductiveConstructor Operator"
      >&#955;&#7488;</a
      ><a name="4272"
      > </a
      ><a name="4273" href="Stlc.html#1255" class="Function"
      >x</a
      ><a name="4274"
      > </a
      ><a name="4275" href="Stlc.html#1075" class="InductiveConstructor Operator"
      >&#8712;</a
      ><a name="4276"
      > </a
      ><a name="4277" href="Stlc.html#995" class="InductiveConstructor"
      >&#120121;</a
      ><a name="4278"
      > </a
      ><a name="4279" href="Stlc.html#1075" class="InductiveConstructor Operator"
      >&#8658;</a
      ><a name="4280"
      > </a
      ><a name="4281" class="Symbol"
      >(</a
      ><a name="4282" href="Stlc.html#1304" class="Function"
      >I[&#120121;]</a
      ><a name="4286"
      > </a
      ><a name="4287" href="Stlc.html#1111" class="InductiveConstructor Operator"
      >&#183;&#7488;</a
      ><a name="4289"
      > </a
      ><a name="4290" href="Stlc.html#1056" class="InductiveConstructor"
      >var&#7488;</a
      ><a name="4294"
      > </a
      ><a name="4295" href="Stlc.html#1255" class="Function"
      >x</a
      ><a name="4296" class="Symbol"
      >))</a
      ><a name="4298"
      > </a
      ><a name="4299" href="Stlc.html#1111" class="InductiveConstructor Operator"
      >&#183;&#7488;</a
      ><a name="4301"
      > </a
      ><a name="4302" class="Symbol"
      >(</a
      ><a name="4303" href="Stlc.html#1170" class="InductiveConstructor Operator"
      >if&#7488;</a
      ><a name="4306"
      > </a
      ><a name="4307" href="Stlc.html#1154" class="InductiveConstructor"
      >false&#7488;</a
      ><a name="4313"
      > </a
      ><a name="4314" href="Stlc.html#1170" class="InductiveConstructor Operator"
      >then</a
      ><a name="4318"
      > </a
      ><a name="4319" href="Stlc.html#1154" class="InductiveConstructor"
      >false&#7488;</a
      ><a name="4325"
      > </a
      ><a name="4326" href="Stlc.html#1170" class="InductiveConstructor Operator"
      >else</a
      ><a name="4330"
      > </a
      ><a name="4331" href="Stlc.html#1139" class="InductiveConstructor"
      >true&#7488;</a
      ><a name="4336" class="Symbol"
      >))</a
      ><a name="4338"
      >
  </a
      ><a name="4341" href="Stlc.html#4138" class="Function"
      >M&#8323;</a
      ><a name="4343"
      > </a
      ><a name="4344" class="Symbol"
      >=</a
      ><a name="4345"
      > </a
      ><a name="4346" class="Symbol"
      >((</a
      ><a name="4348" href="Stlc.html#1075" class="InductiveConstructor Operator"
      >&#955;&#7488;</a
      ><a name="4350"
      > </a
      ><a name="4351" href="Stlc.html#1255" class="Function"
      >x</a
      ><a name="4352"
      > </a
      ><a name="4353" href="Stlc.html#1075" class="InductiveConstructor Operator"
      >&#8712;</a
      ><a name="4354"
      > </a
      ><a name="4355" href="Stlc.html#995" class="InductiveConstructor"
      >&#120121;</a
      ><a name="4356"
      > </a
      ><a name="4357" href="Stlc.html#1075" class="InductiveConstructor Operator"
      >&#8658;</a
      ><a name="4358"
      > </a
      ><a name="4359" class="Symbol"
      >(</a
      ><a name="4360" href="Stlc.html#1304" class="Function"
      >I[&#120121;]</a
      ><a name="4364"
      > </a
      ><a name="4365" href="Stlc.html#1111" class="InductiveConstructor Operator"
      >&#183;&#7488;</a
      ><a name="4367"
      > </a
      ><a name="4368" href="Stlc.html#1056" class="InductiveConstructor"
      >var&#7488;</a
      ><a name="4372"
      > </a
      ><a name="4373" href="Stlc.html#1255" class="Function"
      >x</a
      ><a name="4374" class="Symbol"
      >))</a
      ><a name="4376"
      > </a
      ><a name="4377" href="Stlc.html#1111" class="InductiveConstructor Operator"
      >&#183;&#7488;</a
      ><a name="4379"
      > </a
      ><a name="4380" href="Stlc.html#1139" class="InductiveConstructor"
      >true&#7488;</a
      ><a name="4385" class="Symbol"
      >)</a
      ><a name="4386"
      >
  </a
      ><a name="4389" href="Stlc.html#4141" class="Function"
      >M&#8324;</a
      ><a name="4391"
      > </a
      ><a name="4392" class="Symbol"
      >=</a
      ><a name="4393"
      > </a
      ><a name="4394" href="Stlc.html#1304" class="Function"
      >I[&#120121;]</a
      ><a name="4398"
      > </a
      ><a name="4399" href="Stlc.html#1111" class="InductiveConstructor Operator"
      >&#183;&#7488;</a
      ><a name="4401"
      > </a
      ><a name="4402" href="Stlc.html#1139" class="InductiveConstructor"
      >true&#7488;</a
      ><a name="4407"
      >
  </a
      ><a name="4410" href="Stlc.html#4144" class="Function"
      >M&#8325;</a
      ><a name="4412"
      > </a
      ><a name="4413" class="Symbol"
      >=</a
      ><a name="4414"
      > </a
      ><a name="4415" href="Stlc.html#1139" class="InductiveConstructor"
      >true&#7488;</a
      ><a name="4420"
      >
  </a
      ><a name="4423" href="Stlc.html#4423" class="Function"
      >step&#8320;</a
      ><a name="4428"
      > </a
      ><a name="4429" class="Symbol"
      >:</a
      ><a name="4430"
      > </a
      ><a name="4431" href="Stlc.html#4129" class="Function"
      >M&#8320;</a
      ><a name="4433"
      > </a
      ><a name="4434" href="Stlc.html#2246" class="Datatype Operator"
      >&#10233;</a
      ><a name="4435"
      > </a
      ><a name="4436" href="Stlc.html#4132" class="Function"
      >M&#8321;</a
      ><a name="4438"
      >
  </a
      ><a name="4441" href="Stlc.html#4423" class="Function"
      >step&#8320;</a
      ><a name="4446"
      > </a
      ><a name="4447" class="Symbol"
      >=</a
      ><a name="4448"
      > </a
      ><a name="4449" href="Stlc.html#2352" class="InductiveConstructor"
      >&#947;&#8658;&#8321;</a
      ><a name="4452"
      > </a
      ><a name="4453" class="Symbol"
      >(</a
      ><a name="4454" href="Stlc.html#2278" class="InductiveConstructor"
      >&#946;&#8658;</a
      ><a name="4456"
      > </a
      ><a name="4457" href="Stlc.html#1613" class="InductiveConstructor"
      >value-&#955;&#7488;</a
      ><a name="4465" class="Symbol"
      >)</a
      ><a name="4466"
      >
  </a
      ><a name="4469" href="Stlc.html#4469" class="Function"
      >step&#8321;</a
      ><a name="4474"
      > </a
      ><a name="4475" class="Symbol"
      >:</a
      ><a name="4476"
      > </a
      ><a name="4477" href="Stlc.html#4132" class="Function"
      >M&#8321;</a
      ><a name="4479"
      > </a
      ><a name="4480" href="Stlc.html#2246" class="Datatype Operator"
      >&#10233;</a
      ><a name="4481"
      > </a
      ><a name="4482" href="Stlc.html#4135" class="Function"
      >M&#8322;</a
      ><a name="4484"
      >
  </a
      ><a name="4487" href="Stlc.html#4469" class="Function"
      >step&#8321;</a
      ><a name="4492"
      > </a
      ><a name="4493" class="Symbol"
      >=</a
      ><a name="4494"
      > </a
      ><a name="4495" href="Stlc.html#2411" class="InductiveConstructor"
      >&#947;&#8658;&#8322;</a
      ><a name="4498"
      > </a
      ><a name="4499" href="Stlc.html#1613" class="InductiveConstructor"
      >value-&#955;&#7488;</a
      ><a name="4507"
      > </a
      ><a name="4508" class="Symbol"
      >(</a
      ><a name="4509" href="Stlc.html#2278" class="InductiveConstructor"
      >&#946;&#8658;</a
      ><a name="4511"
      > </a
      ><a name="4512" href="Stlc.html#1689" class="InductiveConstructor"
      >value-false&#7488;</a
      ><a name="4524" class="Symbol"
      >)</a
      ><a name="4525"
      >
  </a
      ><a name="4528" href="Stlc.html#4528" class="Function"
      >step&#8322;</a
      ><a name="4533"
      > </a
      ><a name="4534" class="Symbol"
      >:</a
      ><a name="4535"
      > </a
      ><a name="4536" href="Stlc.html#4135" class="Function"
      >M&#8322;</a
      ><a name="4538"
      > </a
      ><a name="4539" href="Stlc.html#2246" class="Datatype Operator"
      >&#10233;</a
      ><a name="4540"
      > </a
      ><a name="4541" href="Stlc.html#4138" class="Function"
      >M&#8323;</a
      ><a name="4543"
      >
  </a
      ><a name="4546" href="Stlc.html#4528" class="Function"
      >step&#8322;</a
      ><a name="4551"
      > </a
      ><a name="4552" class="Symbol"
      >=</a
      ><a name="4553"
      > </a
      ><a name="4554" href="Stlc.html#2411" class="InductiveConstructor"
      >&#947;&#8658;&#8322;</a
      ><a name="4557"
      > </a
      ><a name="4558" href="Stlc.html#1613" class="InductiveConstructor"
      >value-&#955;&#7488;</a
      ><a name="4566"
      > </a
      ><a name="4567" href="Stlc.html#2536" class="InductiveConstructor"
      >&#946;&#120121;&#8322;</a
      ><a name="4570"
      >
  </a
      ><a name="4573" href="Stlc.html#4573" class="Function"
      >step&#8323;</a
      ><a name="4578"
      > </a
      ><a name="4579" class="Symbol"
      >:</a
      ><a name="4580"
      > </a
      ><a name="4581" href="Stlc.html#4138" class="Function"
      >M&#8323;</a
      ><a name="4583"
      > </a
      ><a name="4584" href="Stlc.html#2246" class="Datatype Operator"
      >&#10233;</a
      ><a name="4585"
      > </a
      ><a name="4586" href="Stlc.html#4141" class="Function"
      >M&#8324;</a
      ><a name="4588"
      >
  </a
      ><a name="4591" href="Stlc.html#4573" class="Function"
      >step&#8323;</a
      ><a name="4596"
      > </a
      ><a name="4597" class="Symbol"
      >=</a
      ><a name="4598"
      > </a
      ><a name="4599" href="Stlc.html#2278" class="InductiveConstructor"
      >&#946;&#8658;</a
      ><a name="4601"
      > </a
      ><a name="4602" href="Stlc.html#1659" class="InductiveConstructor"
      >value-true&#7488;</a
      ><a name="4613"
      >         
  </a
      ><a name="4625" href="Stlc.html#4625" class="Function"
      >step&#8324;</a
      ><a name="4630"
      > </a
      ><a name="4631" class="Symbol"
      >:</a
      ><a name="4632"
      > </a
      ><a name="4633" href="Stlc.html#4141" class="Function"
      >M&#8324;</a
      ><a name="4635"
      > </a
      ><a name="4636" href="Stlc.html#2246" class="Datatype Operator"
      >&#10233;</a
      ><a name="4637"
      > </a
      ><a name="4638" href="Stlc.html#4144" class="Function"
      >M&#8325;</a
      ><a name="4640"
      >
  </a
      ><a name="4643" href="Stlc.html#4625" class="Function"
      >step&#8324;</a
      ><a name="4648"
      > </a
      ><a name="4649" class="Symbol"
      >=</a
      ><a name="4650"
      > </a
      ><a name="4651" href="Stlc.html#2278" class="InductiveConstructor"
      >&#946;&#8658;</a
      ><a name="4653"
      > </a
      ><a name="4654" href="Stlc.html#1659" class="InductiveConstructor"
      >value-true&#7488;</a
      >

</pre>

## Type rules

<pre class="Agda">

<a name="4715" href="Stlc.html#4715" class="Function"
      >Context</a
      ><a name="4722"
      > </a
      ><a name="4723" class="Symbol"
      >:</a
      ><a name="4724"
      > </a
      ><a name="4725" class="PrimitiveType"
      >Set</a
      ><a name="4728"
      >
</a
      ><a name="4729" href="Stlc.html#4715" class="Function"
      >Context</a
      ><a name="4736"
      > </a
      ><a name="4737" class="Symbol"
      >=</a
      ><a name="4738"
      > </a
      ><a name="4739" href="Maps.html#10227" class="Function"
      >PartialMap</a
      ><a name="4749"
      > </a
      ><a name="4750" href="Stlc.html#976" class="Datatype"
      >Type</a
      ><a name="4754"
      >

</a
      ><a name="4756" class="Keyword"
      >infix</a
      ><a name="4761"
      > </a
      ><a name="4762" class="Number"
      >50</a
      ><a name="4764"
      > </a
      ><a name="4765" href="Stlc.html#4777" class="Datatype Operator"
      >_&#8866;_&#8712;_</a
      ><a name="4770"
      >

</a
      ><a name="4772" class="Keyword"
      >data</a
      ><a name="4776"
      > </a
      ><a name="4777" href="Stlc.html#4777" class="Datatype Operator"
      >_&#8866;_&#8712;_</a
      ><a name="4782"
      > </a
      ><a name="4783" class="Symbol"
      >:</a
      ><a name="4784"
      > </a
      ><a name="4785" href="Stlc.html#4715" class="Function"
      >Context</a
      ><a name="4792"
      > </a
      ><a name="4793" class="Symbol"
      >&#8594;</a
      ><a name="4794"
      > </a
      ><a name="4795" href="Stlc.html#1037" class="Datatype"
      >Term</a
      ><a name="4799"
      > </a
      ><a name="4800" class="Symbol"
      >&#8594;</a
      ><a name="4801"
      > </a
      ><a name="4802" href="Stlc.html#976" class="Datatype"
      >Type</a
      ><a name="4806"
      > </a
      ><a name="4807" class="Symbol"
      >&#8594;</a
      ><a name="4808"
      > </a
      ><a name="4809" class="PrimitiveType"
      >Set</a
      ><a name="4812"
      > </a
      ><a name="4813" class="Keyword"
      >where</a
      ><a name="4818"
      >
  </a
      ><a name="4821" href="Stlc.html#4821" class="InductiveConstructor"
      >Ax</a
      ><a name="4823"
      > </a
      ><a name="4824" class="Symbol"
      >:</a
      ><a name="4825"
      > </a
      ><a name="4826" class="Symbol"
      >&#8704;</a
      ><a name="4827"
      > </a
      ><a name="4828" class="Symbol"
      >{</a
      ><a name="4829" href="Stlc.html#4829" class="Bound"
      >&#915;</a
      ><a name="4830"
      > </a
      ><a name="4831" href="Stlc.html#4831" class="Bound"
      >x</a
      ><a name="4832"
      > </a
      ><a name="4833" href="Stlc.html#4833" class="Bound"
      >A</a
      ><a name="4834" class="Symbol"
      >}</a
      ><a name="4835"
      > </a
      ><a name="4836" class="Symbol"
      >&#8594;</a
      ><a name="4837"
      >
    </a
      ><a name="4842" href="Stlc.html#4829" class="Bound"
      >&#915;</a
      ><a name="4843"
      > </a
      ><a name="4844" href="Stlc.html#4831" class="Bound"
      >x</a
      ><a name="4845"
      > </a
      ><a name="4846" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="4847"
      > </a
      ><a name="4848" href="https://agda.github.io/agda-stdlib/Data.Maybe.Base.html#373" class="InductiveConstructor"
      >just</a
      ><a name="4852"
      > </a
      ><a name="4853" href="Stlc.html#4833" class="Bound"
      >A</a
      ><a name="4854"
      > </a
      ><a name="4855" class="Symbol"
      >&#8594;</a
      ><a name="4856"
      >
    </a
      ><a name="4861" href="Stlc.html#4829" class="Bound"
      >&#915;</a
      ><a name="4862"
      > </a
      ><a name="4863" href="Stlc.html#4777" class="Datatype Operator"
      >&#8866;</a
      ><a name="4864"
      > </a
      ><a name="4865" href="Stlc.html#1056" class="InductiveConstructor"
      >var&#7488;</a
      ><a name="4869"
      > </a
      ><a name="4870" href="Stlc.html#4831" class="Bound"
      >x</a
      ><a name="4871"
      > </a
      ><a name="4872" href="Stlc.html#4777" class="Datatype Operator"
      >&#8712;</a
      ><a name="4873"
      > </a
      ><a name="4874" href="Stlc.html#4833" class="Bound"
      >A</a
      ><a name="4875"
      >
  </a
      ><a name="4878" href="Stlc.html#4878" class="InductiveConstructor"
      >&#8658;-I</a
      ><a name="4881"
      > </a
      ><a name="4882" class="Symbol"
      >:</a
      ><a name="4883"
      > </a
      ><a name="4884" class="Symbol"
      >&#8704;</a
      ><a name="4885"
      > </a
      ><a name="4886" class="Symbol"
      >{</a
      ><a name="4887" href="Stlc.html#4887" class="Bound"
      >&#915;</a
      ><a name="4888"
      > </a
      ><a name="4889" href="Stlc.html#4889" class="Bound"
      >x</a
      ><a name="4890"
      > </a
      ><a name="4891" href="Stlc.html#4891" class="Bound"
      >N</a
      ><a name="4892"
      > </a
      ><a name="4893" href="Stlc.html#4893" class="Bound"
      >A</a
      ><a name="4894"
      > </a
      ><a name="4895" href="Stlc.html#4895" class="Bound"
      >B</a
      ><a name="4896" class="Symbol"
      >}</a
      ><a name="4897"
      > </a
      ><a name="4898" class="Symbol"
      >&#8594;</a
      ><a name="4899"
      >
    </a
      ><a name="4904" class="Symbol"
      >(</a
      ><a name="4905" href="Stlc.html#4887" class="Bound"
      >&#915;</a
      ><a name="4906"
      > </a
      ><a name="4907" href="Maps.html#10464" class="Function Operator"
      >,</a
      ><a name="4908"
      > </a
      ><a name="4909" href="Stlc.html#4889" class="Bound"
      >x</a
      ><a name="4910"
      > </a
      ><a name="4911" href="Maps.html#10464" class="Function Operator"
      >&#8614;</a
      ><a name="4912"
      > </a
      ><a name="4913" href="Stlc.html#4893" class="Bound"
      >A</a
      ><a name="4914" class="Symbol"
      >)</a
      ><a name="4915"
      > </a
      ><a name="4916" href="Stlc.html#4777" class="Datatype Operator"
      >&#8866;</a
      ><a name="4917"
      > </a
      ><a name="4918" href="Stlc.html#4891" class="Bound"
      >N</a
      ><a name="4919"
      > </a
      ><a name="4920" href="Stlc.html#4777" class="Datatype Operator"
      >&#8712;</a
      ><a name="4921"
      > </a
      ><a name="4922" href="Stlc.html#4895" class="Bound"
      >B</a
      ><a name="4923"
      > </a
      ><a name="4924" class="Symbol"
      >&#8594;</a
      ><a name="4925"
      >
    </a
      ><a name="4930" href="Stlc.html#4887" class="Bound"
      >&#915;</a
      ><a name="4931"
      > </a
      ><a name="4932" href="Stlc.html#4777" class="Datatype Operator"
      >&#8866;</a
      ><a name="4933"
      > </a
      ><a name="4934" class="Symbol"
      >(</a
      ><a name="4935" href="Stlc.html#1075" class="InductiveConstructor Operator"
      >&#955;&#7488;</a
      ><a name="4937"
      > </a
      ><a name="4938" href="Stlc.html#4889" class="Bound"
      >x</a
      ><a name="4939"
      > </a
      ><a name="4940" href="Stlc.html#1075" class="InductiveConstructor Operator"
      >&#8712;</a
      ><a name="4941"
      > </a
      ><a name="4942" href="Stlc.html#4893" class="Bound"
      >A</a
      ><a name="4943"
      > </a
      ><a name="4944" href="Stlc.html#1075" class="InductiveConstructor Operator"
      >&#8658;</a
      ><a name="4945"
      > </a
      ><a name="4946" href="Stlc.html#4891" class="Bound"
      >N</a
      ><a name="4947" class="Symbol"
      >)</a
      ><a name="4948"
      > </a
      ><a name="4949" href="Stlc.html#4777" class="Datatype Operator"
      >&#8712;</a
      ><a name="4950"
      > </a
      ><a name="4951" class="Symbol"
      >(</a
      ><a name="4952" href="Stlc.html#4893" class="Bound"
      >A</a
      ><a name="4953"
      > </a
      ><a name="4954" href="Stlc.html#1006" class="InductiveConstructor Operator"
      >&#8658;</a
      ><a name="4955"
      > </a
      ><a name="4956" href="Stlc.html#4895" class="Bound"
      >B</a
      ><a name="4957" class="Symbol"
      >)</a
      ><a name="4958"
      >
  </a
      ><a name="4961" href="Stlc.html#4961" class="InductiveConstructor"
      >&#8658;-E</a
      ><a name="4964"
      > </a
      ><a name="4965" class="Symbol"
      >:</a
      ><a name="4966"
      > </a
      ><a name="4967" class="Symbol"
      >&#8704;</a
      ><a name="4968"
      > </a
      ><a name="4969" class="Symbol"
      >{</a
      ><a name="4970" href="Stlc.html#4970" class="Bound"
      >&#915;</a
      ><a name="4971"
      > </a
      ><a name="4972" href="Stlc.html#4972" class="Bound"
      >L</a
      ><a name="4973"
      > </a
      ><a name="4974" href="Stlc.html#4974" class="Bound"
      >M</a
      ><a name="4975"
      > </a
      ><a name="4976" href="Stlc.html#4976" class="Bound"
      >A</a
      ><a name="4977"
      > </a
      ><a name="4978" href="Stlc.html#4978" class="Bound"
      >B</a
      ><a name="4979" class="Symbol"
      >}</a
      ><a name="4980"
      > </a
      ><a name="4981" class="Symbol"
      >&#8594;</a
      ><a name="4982"
      >
    </a
      ><a name="4987" href="Stlc.html#4970" class="Bound"
      >&#915;</a
      ><a name="4988"
      > </a
      ><a name="4989" href="Stlc.html#4777" class="Datatype Operator"
      >&#8866;</a
      ><a name="4990"
      > </a
      ><a name="4991" href="Stlc.html#4972" class="Bound"
      >L</a
      ><a name="4992"
      > </a
      ><a name="4993" href="Stlc.html#4777" class="Datatype Operator"
      >&#8712;</a
      ><a name="4994"
      > </a
      ><a name="4995" class="Symbol"
      >(</a
      ><a name="4996" href="Stlc.html#4976" class="Bound"
      >A</a
      ><a name="4997"
      > </a
      ><a name="4998" href="Stlc.html#1006" class="InductiveConstructor Operator"
      >&#8658;</a
      ><a name="4999"
      > </a
      ><a name="5000" href="Stlc.html#4978" class="Bound"
      >B</a
      ><a name="5001" class="Symbol"
      >)</a
      ><a name="5002"
      > </a
      ><a name="5003" class="Symbol"
      >&#8594;</a
      ><a name="5004"
      >
    </a
      ><a name="5009" href="Stlc.html#4970" class="Bound"
      >&#915;</a
      ><a name="5010"
      > </a
      ><a name="5011" href="Stlc.html#4777" class="Datatype Operator"
      >&#8866;</a
      ><a name="5012"
      > </a
      ><a name="5013" href="Stlc.html#4974" class="Bound"
      >M</a
      ><a name="5014"
      > </a
      ><a name="5015" href="Stlc.html#4777" class="Datatype Operator"
      >&#8712;</a
      ><a name="5016"
      > </a
      ><a name="5017" href="Stlc.html#4976" class="Bound"
      >A</a
      ><a name="5018"
      > </a
      ><a name="5019" class="Symbol"
      >&#8594;</a
      ><a name="5020"
      >
    </a
      ><a name="5025" href="Stlc.html#4970" class="Bound"
      >&#915;</a
      ><a name="5026"
      > </a
      ><a name="5027" href="Stlc.html#4777" class="Datatype Operator"
      >&#8866;</a
      ><a name="5028"
      > </a
      ><a name="5029" href="Stlc.html#4972" class="Bound"
      >L</a
      ><a name="5030"
      > </a
      ><a name="5031" href="Stlc.html#1111" class="InductiveConstructor Operator"
      >&#183;&#7488;</a
      ><a name="5033"
      > </a
      ><a name="5034" href="Stlc.html#4974" class="Bound"
      >M</a
      ><a name="5035"
      > </a
      ><a name="5036" href="Stlc.html#4777" class="Datatype Operator"
      >&#8712;</a
      ><a name="5037"
      > </a
      ><a name="5038" href="Stlc.html#4978" class="Bound"
      >B</a
      ><a name="5039"
      >
  </a
      ><a name="5042" href="Stlc.html#5042" class="InductiveConstructor"
      >&#120121;-I&#8321;</a
      ><a name="5046"
      > </a
      ><a name="5047" class="Symbol"
      >:</a
      ><a name="5048"
      > </a
      ><a name="5049" class="Symbol"
      >&#8704;</a
      ><a name="5050"
      > </a
      ><a name="5051" class="Symbol"
      >{</a
      ><a name="5052" href="Stlc.html#5052" class="Bound"
      >&#915;</a
      ><a name="5053" class="Symbol"
      >}</a
      ><a name="5054"
      > </a
      ><a name="5055" class="Symbol"
      >&#8594;</a
      ><a name="5056"
      >
    </a
      ><a name="5061" href="Stlc.html#5052" class="Bound"
      >&#915;</a
      ><a name="5062"
      > </a
      ><a name="5063" href="Stlc.html#4777" class="Datatype Operator"
      >&#8866;</a
      ><a name="5064"
      > </a
      ><a name="5065" href="Stlc.html#1139" class="InductiveConstructor"
      >true&#7488;</a
      ><a name="5070"
      > </a
      ><a name="5071" href="Stlc.html#4777" class="Datatype Operator"
      >&#8712;</a
      ><a name="5072"
      > </a
      ><a name="5073" href="Stlc.html#995" class="InductiveConstructor"
      >&#120121;</a
      ><a name="5074"
      >
  </a
      ><a name="5077" href="Stlc.html#5077" class="InductiveConstructor"
      >&#120121;-I&#8322;</a
      ><a name="5081"
      > </a
      ><a name="5082" class="Symbol"
      >:</a
      ><a name="5083"
      > </a
      ><a name="5084" class="Symbol"
      >&#8704;</a
      ><a name="5085"
      > </a
      ><a name="5086" class="Symbol"
      >{</a
      ><a name="5087" href="Stlc.html#5087" class="Bound"
      >&#915;</a
      ><a name="5088" class="Symbol"
      >}</a
      ><a name="5089"
      > </a
      ><a name="5090" class="Symbol"
      >&#8594;</a
      ><a name="5091"
      >
    </a
      ><a name="5096" href="Stlc.html#5087" class="Bound"
      >&#915;</a
      ><a name="5097"
      > </a
      ><a name="5098" href="Stlc.html#4777" class="Datatype Operator"
      >&#8866;</a
      ><a name="5099"
      > </a
      ><a name="5100" href="Stlc.html#1154" class="InductiveConstructor"
      >false&#7488;</a
      ><a name="5106"
      > </a
      ><a name="5107" href="Stlc.html#4777" class="Datatype Operator"
      >&#8712;</a
      ><a name="5108"
      > </a
      ><a name="5109" href="Stlc.html#995" class="InductiveConstructor"
      >&#120121;</a
      ><a name="5110"
      >
  </a
      ><a name="5113" href="Stlc.html#5113" class="InductiveConstructor"
      >&#120121;-E</a
      ><a name="5116"
      > </a
      ><a name="5117" class="Symbol"
      >:</a
      ><a name="5118"
      > </a
      ><a name="5119" class="Symbol"
      >&#8704;</a
      ><a name="5120"
      > </a
      ><a name="5121" class="Symbol"
      >{</a
      ><a name="5122" href="Stlc.html#5122" class="Bound"
      >&#915;</a
      ><a name="5123"
      > </a
      ><a name="5124" href="Stlc.html#5124" class="Bound"
      >L</a
      ><a name="5125"
      > </a
      ><a name="5126" href="Stlc.html#5126" class="Bound"
      >M</a
      ><a name="5127"
      > </a
      ><a name="5128" href="Stlc.html#5128" class="Bound"
      >N</a
      ><a name="5129"
      > </a
      ><a name="5130" href="Stlc.html#5130" class="Bound"
      >A</a
      ><a name="5131" class="Symbol"
      >}</a
      ><a name="5132"
      > </a
      ><a name="5133" class="Symbol"
      >&#8594;</a
      ><a name="5134"
      >
    </a
      ><a name="5139" href="Stlc.html#5122" class="Bound"
      >&#915;</a
      ><a name="5140"
      > </a
      ><a name="5141" href="Stlc.html#4777" class="Datatype Operator"
      >&#8866;</a
      ><a name="5142"
      > </a
      ><a name="5143" href="Stlc.html#5124" class="Bound"
      >L</a
      ><a name="5144"
      > </a
      ><a name="5145" href="Stlc.html#4777" class="Datatype Operator"
      >&#8712;</a
      ><a name="5146"
      > </a
      ><a name="5147" href="Stlc.html#995" class="InductiveConstructor"
      >&#120121;</a
      ><a name="5148"
      > </a
      ><a name="5149" class="Symbol"
      >&#8594;</a
      ><a name="5150"
      >
    </a
      ><a name="5155" href="Stlc.html#5122" class="Bound"
      >&#915;</a
      ><a name="5156"
      > </a
      ><a name="5157" href="Stlc.html#4777" class="Datatype Operator"
      >&#8866;</a
      ><a name="5158"
      > </a
      ><a name="5159" href="Stlc.html#5126" class="Bound"
      >M</a
      ><a name="5160"
      > </a
      ><a name="5161" href="Stlc.html#4777" class="Datatype Operator"
      >&#8712;</a
      ><a name="5162"
      > </a
      ><a name="5163" href="Stlc.html#5130" class="Bound"
      >A</a
      ><a name="5164"
      > </a
      ><a name="5165" class="Symbol"
      >&#8594;</a
      ><a name="5166"
      >
    </a
      ><a name="5171" href="Stlc.html#5122" class="Bound"
      >&#915;</a
      ><a name="5172"
      > </a
      ><a name="5173" href="Stlc.html#4777" class="Datatype Operator"
      >&#8866;</a
      ><a name="5174"
      > </a
      ><a name="5175" href="Stlc.html#5128" class="Bound"
      >N</a
      ><a name="5176"
      > </a
      ><a name="5177" href="Stlc.html#4777" class="Datatype Operator"
      >&#8712;</a
      ><a name="5178"
      > </a
      ><a name="5179" href="Stlc.html#5130" class="Bound"
      >A</a
      ><a name="5180"
      > </a
      ><a name="5181" class="Symbol"
      >&#8594;</a
      ><a name="5182"
      >
    </a
      ><a name="5187" href="Stlc.html#5122" class="Bound"
      >&#915;</a
      ><a name="5188"
      > </a
      ><a name="5189" href="Stlc.html#4777" class="Datatype Operator"
      >&#8866;</a
      ><a name="5190"
      > </a
      ><a name="5191" class="Symbol"
      >(</a
      ><a name="5192" href="Stlc.html#1170" class="InductiveConstructor Operator"
      >if&#7488;</a
      ><a name="5195"
      > </a
      ><a name="5196" href="Stlc.html#5124" class="Bound"
      >L</a
      ><a name="5197"
      > </a
      ><a name="5198" href="Stlc.html#1170" class="InductiveConstructor Operator"
      >then</a
      ><a name="5202"
      > </a
      ><a name="5203" href="Stlc.html#5126" class="Bound"
      >M</a
      ><a name="5204"
      > </a
      ><a name="5205" href="Stlc.html#1170" class="InductiveConstructor Operator"
      >else</a
      ><a name="5209"
      > </a
      ><a name="5210" href="Stlc.html#5128" class="Bound"
      >N</a
      ><a name="5211" class="Symbol"
      >)</a
      ><a name="5212"
      > </a
      ><a name="5213" href="Stlc.html#4777" class="Datatype Operator"
      >&#8712;</a
      ><a name="5214"
      > </a
      ><a name="5215" href="Stlc.html#5130" class="Bound"
      >A</a
      >

</pre>
