---
title     : "Stlc: The Simply Typed Lambda-Calculus"
layout    : page
permalink : /Stlc
---

This chapter defines the simply-typed lambda calculus.

## Imports

<pre class="Agda">

<a name="179" class="Keyword"
      >open</a
      ><a name="183"
      > </a
      ><a name="184" class="Keyword"
      >import</a
      ><a name="190"
      > </a
      ><a name="191" class="Module"
      >Maps</a
      ><a name="195"
      > </a
      ><a name="196" class="Keyword"
      >using</a
      ><a name="201"
      > </a
      ><a name="202" class="Symbol"
      >(</a
      ><a name="203" href="Maps.html#2171" class="Datatype"
      >Id</a
      ><a name="205" class="Symbol"
      >;</a
      ><a name="206"
      > </a
      ><a name="207" href="Maps.html#2188" class="InductiveConstructor"
      >id</a
      ><a name="209" class="Symbol"
      >;</a
      ><a name="210"
      > </a
      ><a name="211" href="Maps.html#2509" class="Function Operator"
      >_&#8799;_</a
      ><a name="214" class="Symbol"
      >;</a
      ><a name="215"
      > </a
      ><a name="216" href="Maps.html#10132" class="Function"
      >PartialMap</a
      ><a name="226" class="Symbol"
      >;</a
      ><a name="227"
      > </a
      ><a name="228" class="Keyword"
      >module</a
      ><a name="234"
      > </a
      ><a name="235" href="Maps.html#10221" class="Module"
      >PartialMap</a
      ><a name="245" class="Symbol"
      >)</a
      ><a name="246"
      >
</a
      ><a name="247" class="Keyword"
      >open</a
      ><a name="251"
      > </a
      ><a name="252" href="Maps.html#10221" class="Module"
      >PartialMap</a
      ><a name="262"
      > </a
      ><a name="263" class="Keyword"
      >using</a
      ><a name="268"
      > </a
      ><a name="269" class="Symbol"
      >(</a
      ><a name="270" href="Maps.html#10265" class="Function"
      >&#8709;</a
      ><a name="271" class="Symbol"
      >)</a
      ><a name="272"
      > </a
      ><a name="273" class="Keyword"
      >renaming</a
      ><a name="281"
      > </a
      ><a name="282" class="Symbol"
      >(</a
      ><a name="283" href="Maps.html#10368" class="Function Operator"
      >_,_&#8614;_</a
      ><a name="288"
      > </a
      ><a name="289" class="Symbol"
      >to</a
      ><a name="291"
      > </a
      ><a name="292" href="Maps.html#10368" class="Function Operator"
      >_,_&#8758;_</a
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
      ><a name="311" href="https://agda.github.io/agda-stdlib/Data.Nat.html#1" class="Module"
      >Data.Nat</a
      ><a name="319"
      > </a
      ><a name="320" class="Keyword"
      >using</a
      ><a name="325"
      > </a
      ><a name="326" class="Symbol"
      >(</a
      ><a name="327" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#97" class="Datatype"
      >&#8469;</a
      ><a name="328" class="Symbol"
      >)</a
      ><a name="329"
      >
</a
      ><a name="330" class="Keyword"
      >open</a
      ><a name="334"
      > </a
      ><a name="335" class="Keyword"
      >import</a
      ><a name="341"
      > </a
      ><a name="342" href="https://agda.github.io/agda-stdlib/Data.Maybe.html#1" class="Module"
      >Data.Maybe</a
      ><a name="352"
      > </a
      ><a name="353" class="Keyword"
      >using</a
      ><a name="358"
      > </a
      ><a name="359" class="Symbol"
      >(</a
      ><a name="360" href="https://agda.github.io/agda-stdlib/Data.Maybe.Base.html#335" class="Datatype"
      >Maybe</a
      ><a name="365" class="Symbol"
      >;</a
      ><a name="366"
      > </a
      ><a name="367" href="https://agda.github.io/agda-stdlib/Data.Maybe.html#1527" class="InductiveConstructor"
      >just</a
      ><a name="371" class="Symbol"
      >;</a
      ><a name="372"
      > </a
      ><a name="373" href="https://agda.github.io/agda-stdlib/Data.Maybe.html#1588" class="InductiveConstructor"
      >nothing</a
      ><a name="380" class="Symbol"
      >)</a
      ><a name="381"
      >
</a
      ><a name="382" class="Keyword"
      >open</a
      ><a name="386"
      > </a
      ><a name="387" class="Keyword"
      >import</a
      ><a name="393"
      > </a
      ><a name="394" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#1" class="Module"
      >Relation.Nullary</a
      ><a name="410"
      > </a
      ><a name="411" class="Keyword"
      >using</a
      ><a name="416"
      > </a
      ><a name="417" class="Symbol"
      >(</a
      ><a name="418" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#484" class="Datatype"
      >Dec</a
      ><a name="421" class="Symbol"
      >;</a
      ><a name="422"
      > </a
      ><a name="423" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#520" class="InductiveConstructor"
      >yes</a
      ><a name="426" class="Symbol"
      >;</a
      ><a name="427"
      > </a
      ><a name="428" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#547" class="InductiveConstructor"
      >no</a
      ><a name="430" class="Symbol"
      >)</a
      ><a name="431"
      >
</a
      ><a name="432" class="Keyword"
      >open</a
      ><a name="436"
      > </a
      ><a name="437" class="Keyword"
      >import</a
      ><a name="443"
      > </a
      ><a name="444" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#1" class="Module"
      >Relation.Binary.PropositionalEquality</a
      ><a name="481"
      > </a
      ><a name="482" class="Keyword"
      >using</a
      ><a name="487"
      > </a
      ><a name="488" class="Symbol"
      >(</a
      ><a name="489" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >_&#8801;_</a
      ><a name="492" class="Symbol"
      >;</a
      ><a name="493"
      > </a
      ><a name="494" href="https://agda.github.io/agda-stdlib/Relation.Binary.Core.html#4493" class="Function Operator"
      >_&#8802;_</a
      ><a name="497" class="Symbol"
      >;</a
      ><a name="498"
      > </a
      ><a name="499" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="503" class="Symbol"
      >)</a
      >

</pre>


## Syntax

Syntax of types and terms.

<pre class="Agda">

<a name="570" class="Keyword"
      >infixr</a
      ><a name="576"
      > </a
      ><a name="577" class="Number"
      >20</a
      ><a name="579"
      > </a
      ><a name="580" href="Stlc.html#620" class="InductiveConstructor Operator"
      >_&#8658;_</a
      ><a name="583"
      >

</a
      ><a name="585" class="Keyword"
      >data</a
      ><a name="589"
      > </a
      ><a name="590" href="Stlc.html#590" class="Datatype"
      >Type</a
      ><a name="594"
      > </a
      ><a name="595" class="Symbol"
      >:</a
      ><a name="596"
      > </a
      ><a name="597" class="PrimitiveType"
      >Set</a
      ><a name="600"
      > </a
      ><a name="601" class="Keyword"
      >where</a
      ><a name="606"
      >
  </a
      ><a name="609" href="Stlc.html#609" class="InductiveConstructor"
      >&#120121;</a
      ><a name="610"
      > </a
      ><a name="611" class="Symbol"
      >:</a
      ><a name="612"
      > </a
      ><a name="613" href="Stlc.html#590" class="Datatype"
      >Type</a
      ><a name="617"
      >
  </a
      ><a name="620" href="Stlc.html#620" class="InductiveConstructor Operator"
      >_&#8658;_</a
      ><a name="623"
      > </a
      ><a name="624" class="Symbol"
      >:</a
      ><a name="625"
      > </a
      ><a name="626" href="Stlc.html#590" class="Datatype"
      >Type</a
      ><a name="630"
      > </a
      ><a name="631" class="Symbol"
      >&#8594;</a
      ><a name="632"
      > </a
      ><a name="633" href="Stlc.html#590" class="Datatype"
      >Type</a
      ><a name="637"
      > </a
      ><a name="638" class="Symbol"
      >&#8594;</a
      ><a name="639"
      > </a
      ><a name="640" href="Stlc.html#590" class="Datatype"
      >Type</a
      ><a name="644"
      >

</a
      ><a name="646" class="Keyword"
      >infixl</a
      ><a name="652"
      > </a
      ><a name="653" class="Number"
      >20</a
      ><a name="655"
      > </a
      ><a name="656" href="Stlc.html#779" class="InductiveConstructor Operator"
      >_&#183;_</a
      ><a name="659"
      >
</a
      ><a name="660" class="Keyword"
      >infix</a
      ><a name="665"
      >  </a
      ><a name="667" class="Number"
      >15</a
      ><a name="669"
      > </a
      ><a name="670" href="Stlc.html#743" class="InductiveConstructor Operator"
      >&#955;[_&#8758;_]_</a
      ><a name="677"
      >
</a
      ><a name="678" class="Keyword"
      >infix</a
      ><a name="683"
      >  </a
      ><a name="685" class="Number"
      >15</a
      ><a name="687"
      > </a
      ><a name="688" href="Stlc.html#835" class="InductiveConstructor Operator"
      >if_then_else_</a
      ><a name="701"
      >

</a
      ><a name="703" class="Keyword"
      >data</a
      ><a name="707"
      > </a
      ><a name="708" href="Stlc.html#708" class="Datatype"
      >Term</a
      ><a name="712"
      > </a
      ><a name="713" class="Symbol"
      >:</a
      ><a name="714"
      > </a
      ><a name="715" class="PrimitiveType"
      >Set</a
      ><a name="718"
      > </a
      ><a name="719" class="Keyword"
      >where</a
      ><a name="724"
      >
  </a
      ><a name="727" href="Stlc.html#727" class="InductiveConstructor"
      >`</a
      ><a name="728"
      > </a
      ><a name="729" class="Symbol"
      >:</a
      ><a name="730"
      > </a
      ><a name="731" href="Maps.html#2171" class="Datatype"
      >Id</a
      ><a name="733"
      > </a
      ><a name="734" class="Symbol"
      >&#8594;</a
      ><a name="735"
      > </a
      ><a name="736" href="Stlc.html#708" class="Datatype"
      >Term</a
      ><a name="740"
      >
  </a
      ><a name="743" href="Stlc.html#743" class="InductiveConstructor Operator"
      >&#955;[_&#8758;_]_</a
      ><a name="750"
      > </a
      ><a name="751" class="Symbol"
      >:</a
      ><a name="752"
      > </a
      ><a name="753" href="Maps.html#2171" class="Datatype"
      >Id</a
      ><a name="755"
      > </a
      ><a name="756" class="Symbol"
      >&#8594;</a
      ><a name="757"
      > </a
      ><a name="758" href="Stlc.html#590" class="Datatype"
      >Type</a
      ><a name="762"
      > </a
      ><a name="763" class="Symbol"
      >&#8594;</a
      ><a name="764"
      > </a
      ><a name="765" href="Stlc.html#708" class="Datatype"
      >Term</a
      ><a name="769"
      > </a
      ><a name="770" class="Symbol"
      >&#8594;</a
      ><a name="771"
      > </a
      ><a name="772" href="Stlc.html#708" class="Datatype"
      >Term</a
      ><a name="776"
      >
  </a
      ><a name="779" href="Stlc.html#779" class="InductiveConstructor Operator"
      >_&#183;_</a
      ><a name="782"
      > </a
      ><a name="783" class="Symbol"
      >:</a
      ><a name="784"
      > </a
      ><a name="785" href="Stlc.html#708" class="Datatype"
      >Term</a
      ><a name="789"
      > </a
      ><a name="790" class="Symbol"
      >&#8594;</a
      ><a name="791"
      > </a
      ><a name="792" href="Stlc.html#708" class="Datatype"
      >Term</a
      ><a name="796"
      > </a
      ><a name="797" class="Symbol"
      >&#8594;</a
      ><a name="798"
      > </a
      ><a name="799" href="Stlc.html#708" class="Datatype"
      >Term</a
      ><a name="803"
      >
  </a
      ><a name="806" href="Stlc.html#806" class="InductiveConstructor"
      >true</a
      ><a name="810"
      > </a
      ><a name="811" class="Symbol"
      >:</a
      ><a name="812"
      > </a
      ><a name="813" href="Stlc.html#708" class="Datatype"
      >Term</a
      ><a name="817"
      >
  </a
      ><a name="820" href="Stlc.html#820" class="InductiveConstructor"
      >false</a
      ><a name="825"
      > </a
      ><a name="826" class="Symbol"
      >:</a
      ><a name="827"
      > </a
      ><a name="828" href="Stlc.html#708" class="Datatype"
      >Term</a
      ><a name="832"
      >
  </a
      ><a name="835" href="Stlc.html#835" class="InductiveConstructor Operator"
      >if_then_else_</a
      ><a name="848"
      > </a
      ><a name="849" class="Symbol"
      >:</a
      ><a name="850"
      > </a
      ><a name="851" href="Stlc.html#708" class="Datatype"
      >Term</a
      ><a name="855"
      > </a
      ><a name="856" class="Symbol"
      >&#8594;</a
      ><a name="857"
      > </a
      ><a name="858" href="Stlc.html#708" class="Datatype"
      >Term</a
      ><a name="862"
      > </a
      ><a name="863" class="Symbol"
      >&#8594;</a
      ><a name="864"
      > </a
      ><a name="865" href="Stlc.html#708" class="Datatype"
      >Term</a
      ><a name="869"
      > </a
      ><a name="870" class="Symbol"
      >&#8594;</a
      ><a name="871"
      > </a
      ><a name="872" href="Stlc.html#708" class="Datatype"
      >Term</a
      >

</pre>

Example terms.
<pre class="Agda">

<a name="917" href="Stlc.html#917" class="Function"
      >f</a
      ><a name="918"
      > </a
      ><a name="919" href="Stlc.html#919" class="Function"
      >x</a
      ><a name="920"
      > </a
      ><a name="921" class="Symbol"
      >:</a
      ><a name="922"
      > </a
      ><a name="923" href="Maps.html#2171" class="Datatype"
      >Id</a
      ><a name="925"
      >
</a
      ><a name="926" href="Stlc.html#917" class="Function"
      >f</a
      ><a name="927"
      >  </a
      ><a name="929" class="Symbol"
      >=</a
      ><a name="930"
      >  </a
      ><a name="932" href="Maps.html#2188" class="InductiveConstructor"
      >id</a
      ><a name="934"
      > </a
      ><a name="935" class="Number"
      >0</a
      ><a name="936"
      >
</a
      ><a name="937" href="Stlc.html#919" class="Function"
      >x</a
      ><a name="938"
      >  </a
      ><a name="940" class="Symbol"
      >=</a
      ><a name="941"
      >  </a
      ><a name="943" href="Maps.html#2188" class="InductiveConstructor"
      >id</a
      ><a name="945"
      > </a
      ><a name="946" class="Number"
      >1</a
      ><a name="947"
      >

</a
      ><a name="949" href="Stlc.html#949" class="Function"
      >not</a
      ><a name="952"
      > </a
      ><a name="953" href="Stlc.html#953" class="Function"
      >two</a
      ><a name="956"
      > </a
      ><a name="957" class="Symbol"
      >:</a
      ><a name="958"
      > </a
      ><a name="959" href="Stlc.html#708" class="Datatype"
      >Term</a
      ><a name="963"
      > 
</a
      ><a name="965" href="Stlc.html#949" class="Function"
      >not</a
      ><a name="968"
      > </a
      ><a name="969" class="Symbol"
      >=</a
      ><a name="970"
      >  </a
      ><a name="972" href="Stlc.html#743" class="InductiveConstructor Operator"
      >&#955;[</a
      ><a name="974"
      > </a
      ><a name="975" href="Stlc.html#919" class="Function"
      >x</a
      ><a name="976"
      > </a
      ><a name="977" href="Stlc.html#743" class="InductiveConstructor Operator"
      >&#8758;</a
      ><a name="978"
      > </a
      ><a name="979" href="Stlc.html#609" class="InductiveConstructor"
      >&#120121;</a
      ><a name="980"
      > </a
      ><a name="981" href="Stlc.html#743" class="InductiveConstructor Operator"
      >]</a
      ><a name="982"
      > </a
      ><a name="983" class="Symbol"
      >(</a
      ><a name="984" href="Stlc.html#835" class="InductiveConstructor Operator"
      >if</a
      ><a name="986"
      > </a
      ><a name="987" href="Stlc.html#727" class="InductiveConstructor"
      >`</a
      ><a name="988"
      > </a
      ><a name="989" href="Stlc.html#919" class="Function"
      >x</a
      ><a name="990"
      > </a
      ><a name="991" href="Stlc.html#835" class="InductiveConstructor Operator"
      >then</a
      ><a name="995"
      > </a
      ><a name="996" href="Stlc.html#820" class="InductiveConstructor"
      >false</a
      ><a name="1001"
      > </a
      ><a name="1002" href="Stlc.html#835" class="InductiveConstructor Operator"
      >else</a
      ><a name="1006"
      > </a
      ><a name="1007" href="Stlc.html#806" class="InductiveConstructor"
      >true</a
      ><a name="1011" class="Symbol"
      >)</a
      ><a name="1012"
      >
</a
      ><a name="1013" href="Stlc.html#953" class="Function"
      >two</a
      ><a name="1016"
      > </a
      ><a name="1017" class="Symbol"
      >=</a
      ><a name="1018"
      >  </a
      ><a name="1020" href="Stlc.html#743" class="InductiveConstructor Operator"
      >&#955;[</a
      ><a name="1022"
      > </a
      ><a name="1023" href="Stlc.html#917" class="Function"
      >f</a
      ><a name="1024"
      > </a
      ><a name="1025" href="Stlc.html#743" class="InductiveConstructor Operator"
      >&#8758;</a
      ><a name="1026"
      > </a
      ><a name="1027" href="Stlc.html#609" class="InductiveConstructor"
      >&#120121;</a
      ><a name="1028"
      > </a
      ><a name="1029" href="Stlc.html#620" class="InductiveConstructor Operator"
      >&#8658;</a
      ><a name="1030"
      > </a
      ><a name="1031" href="Stlc.html#609" class="InductiveConstructor"
      >&#120121;</a
      ><a name="1032"
      > </a
      ><a name="1033" href="Stlc.html#743" class="InductiveConstructor Operator"
      >]</a
      ><a name="1034"
      > </a
      ><a name="1035" href="Stlc.html#743" class="InductiveConstructor Operator"
      >&#955;[</a
      ><a name="1037"
      > </a
      ><a name="1038" href="Stlc.html#919" class="Function"
      >x</a
      ><a name="1039"
      > </a
      ><a name="1040" href="Stlc.html#743" class="InductiveConstructor Operator"
      >&#8758;</a
      ><a name="1041"
      > </a
      ><a name="1042" href="Stlc.html#609" class="InductiveConstructor"
      >&#120121;</a
      ><a name="1043"
      > </a
      ><a name="1044" href="Stlc.html#743" class="InductiveConstructor Operator"
      >]</a
      ><a name="1045"
      > </a
      ><a name="1046" href="Stlc.html#727" class="InductiveConstructor"
      >`</a
      ><a name="1047"
      > </a
      ><a name="1048" href="Stlc.html#917" class="Function"
      >f</a
      ><a name="1049"
      > </a
      ><a name="1050" href="Stlc.html#779" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="1051"
      > </a
      ><a name="1052" class="Symbol"
      >(</a
      ><a name="1053" href="Stlc.html#727" class="InductiveConstructor"
      >`</a
      ><a name="1054"
      > </a
      ><a name="1055" href="Stlc.html#917" class="Function"
      >f</a
      ><a name="1056"
      > </a
      ><a name="1057" href="Stlc.html#779" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="1058"
      > </a
      ><a name="1059" href="Stlc.html#727" class="InductiveConstructor"
      >`</a
      ><a name="1060"
      > </a
      ><a name="1061" href="Stlc.html#919" class="Function"
      >x</a
      ><a name="1062" class="Symbol"
      >)</a
      >

</pre>

## Values

<pre class="Agda">

<a name="1100" class="Keyword"
      >data</a
      ><a name="1104"
      > </a
      ><a name="1105" href="Stlc.html#1105" class="Datatype"
      >Value</a
      ><a name="1110"
      > </a
      ><a name="1111" class="Symbol"
      >:</a
      ><a name="1112"
      > </a
      ><a name="1113" href="Stlc.html#708" class="Datatype"
      >Term</a
      ><a name="1117"
      > </a
      ><a name="1118" class="Symbol"
      >&#8594;</a
      ><a name="1119"
      > </a
      ><a name="1120" class="PrimitiveType"
      >Set</a
      ><a name="1123"
      > </a
      ><a name="1124" class="Keyword"
      >where</a
      ><a name="1129"
      >
  </a
      ><a name="1132" href="Stlc.html#1132" class="InductiveConstructor"
      >value-&#955;</a
      ><a name="1139"
      >     </a
      ><a name="1144" class="Symbol"
      >:</a
      ><a name="1145"
      > </a
      ><a name="1146" class="Symbol"
      >&#8704;</a
      ><a name="1147"
      > </a
      ><a name="1148" class="Symbol"
      >{</a
      ><a name="1149" href="Stlc.html#1149" class="Bound"
      >x</a
      ><a name="1150"
      > </a
      ><a name="1151" href="Stlc.html#1151" class="Bound"
      >A</a
      ><a name="1152"
      > </a
      ><a name="1153" href="Stlc.html#1153" class="Bound"
      >N</a
      ><a name="1154" class="Symbol"
      >}</a
      ><a name="1155"
      > </a
      ><a name="1156" class="Symbol"
      >&#8594;</a
      ><a name="1157"
      > </a
      ><a name="1158" href="Stlc.html#1105" class="Datatype"
      >Value</a
      ><a name="1163"
      > </a
      ><a name="1164" class="Symbol"
      >(</a
      ><a name="1165" href="Stlc.html#743" class="InductiveConstructor Operator"
      >&#955;[</a
      ><a name="1167"
      > </a
      ><a name="1168" href="Stlc.html#1149" class="Bound"
      >x</a
      ><a name="1169"
      > </a
      ><a name="1170" href="Stlc.html#743" class="InductiveConstructor Operator"
      >&#8758;</a
      ><a name="1171"
      > </a
      ><a name="1172" href="Stlc.html#1151" class="Bound"
      >A</a
      ><a name="1173"
      > </a
      ><a name="1174" href="Stlc.html#743" class="InductiveConstructor Operator"
      >]</a
      ><a name="1175"
      > </a
      ><a name="1176" href="Stlc.html#1153" class="Bound"
      >N</a
      ><a name="1177" class="Symbol"
      >)</a
      ><a name="1178"
      >
  </a
      ><a name="1181" href="Stlc.html#1181" class="InductiveConstructor"
      >value-true</a
      ><a name="1191"
      >  </a
      ><a name="1193" class="Symbol"
      >:</a
      ><a name="1194"
      > </a
      ><a name="1195" href="Stlc.html#1105" class="Datatype"
      >Value</a
      ><a name="1200"
      > </a
      ><a name="1201" href="Stlc.html#806" class="InductiveConstructor"
      >true</a
      ><a name="1205"
      >
  </a
      ><a name="1208" href="Stlc.html#1208" class="InductiveConstructor"
      >value-false</a
      ><a name="1219"
      > </a
      ><a name="1220" class="Symbol"
      >:</a
      ><a name="1221"
      > </a
      ><a name="1222" href="Stlc.html#1105" class="Datatype"
      >Value</a
      ><a name="1227"
      > </a
      ><a name="1228" href="Stlc.html#820" class="InductiveConstructor"
      >false</a
      >

</pre>

## Substitution

<pre class="Agda">

<a name="1276" href="Stlc.html#1276" class="Function Operator"
      >_[_:=_]</a
      ><a name="1283"
      > </a
      ><a name="1284" class="Symbol"
      >:</a
      ><a name="1285"
      > </a
      ><a name="1286" href="Stlc.html#708" class="Datatype"
      >Term</a
      ><a name="1290"
      > </a
      ><a name="1291" class="Symbol"
      >&#8594;</a
      ><a name="1292"
      > </a
      ><a name="1293" href="Maps.html#2171" class="Datatype"
      >Id</a
      ><a name="1295"
      > </a
      ><a name="1296" class="Symbol"
      >&#8594;</a
      ><a name="1297"
      > </a
      ><a name="1298" href="Stlc.html#708" class="Datatype"
      >Term</a
      ><a name="1302"
      > </a
      ><a name="1303" class="Symbol"
      >&#8594;</a
      ><a name="1304"
      > </a
      ><a name="1305" href="Stlc.html#708" class="Datatype"
      >Term</a
      ><a name="1309"
      >
</a
      ><a name="1310" class="Symbol"
      >(</a
      ><a name="1311" href="Stlc.html#727" class="InductiveConstructor"
      >`</a
      ><a name="1312"
      > </a
      ><a name="1313" href="Stlc.html#1313" class="Bound"
      >x&#8242;</a
      ><a name="1315" class="Symbol"
      >)</a
      ><a name="1316"
      > </a
      ><a name="1317" href="Stlc.html#1276" class="Function Operator"
      >[</a
      ><a name="1318"
      > </a
      ><a name="1319" href="Stlc.html#1319" class="Bound"
      >x</a
      ><a name="1320"
      > </a
      ><a name="1321" href="Stlc.html#1276" class="Function Operator"
      >:=</a
      ><a name="1323"
      > </a
      ><a name="1324" href="Stlc.html#1324" class="Bound"
      >V</a
      ><a name="1325"
      > </a
      ><a name="1326" href="Stlc.html#1276" class="Function Operator"
      >]</a
      ><a name="1327"
      > </a
      ><a name="1328" class="Keyword"
      >with</a
      ><a name="1332"
      > </a
      ><a name="1333" href="Stlc.html#1319" class="Bound"
      >x</a
      ><a name="1334"
      > </a
      ><a name="1335" href="Maps.html#2509" class="Function Operator"
      >&#8799;</a
      ><a name="1336"
      > </a
      ><a name="1337" href="Stlc.html#1313" class="Bound"
      >x&#8242;</a
      ><a name="1339"
      >
</a
      ><a name="1340" class="Symbol"
      >...</a
      ><a name="1343"
      > </a
      ><a name="1344" class="Symbol"
      >|</a
      ><a name="1345"
      > </a
      ><a name="1346" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#520" class="InductiveConstructor"
      >yes</a
      ><a name="1349"
      > </a
      ><a name="1350" class="Symbol"
      >_</a
      ><a name="1351"
      > </a
      ><a name="1352" class="Symbol"
      >=</a
      ><a name="1353"
      > </a
      ><a name="1354" href="Stlc.html#1324" class="Bound"
      >V</a
      ><a name="1355"
      >
</a
      ><a name="1356" class="Symbol"
      >...</a
      ><a name="1359"
      > </a
      ><a name="1360" class="Symbol"
      >|</a
      ><a name="1361"
      > </a
      ><a name="1362" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#547" class="InductiveConstructor"
      >no</a
      ><a name="1364"
      >  </a
      ><a name="1366" class="Symbol"
      >_</a
      ><a name="1367"
      > </a
      ><a name="1368" class="Symbol"
      >=</a
      ><a name="1369"
      > </a
      ><a name="1370" href="Stlc.html#727" class="InductiveConstructor"
      >`</a
      ><a name="1371"
      > </a
      ><a name="1372" href="Stlc.html#1313" class="Bound"
      >x&#8242;</a
      ><a name="1374"
      >
</a
      ><a name="1375" class="Symbol"
      >(</a
      ><a name="1376" href="Stlc.html#743" class="InductiveConstructor Operator"
      >&#955;[</a
      ><a name="1378"
      > </a
      ><a name="1379" href="Stlc.html#1379" class="Bound"
      >x&#8242;</a
      ><a name="1381"
      > </a
      ><a name="1382" href="Stlc.html#743" class="InductiveConstructor Operator"
      >&#8758;</a
      ><a name="1383"
      > </a
      ><a name="1384" href="Stlc.html#1384" class="Bound"
      >A&#8242;</a
      ><a name="1386"
      > </a
      ><a name="1387" href="Stlc.html#743" class="InductiveConstructor Operator"
      >]</a
      ><a name="1388"
      > </a
      ><a name="1389" href="Stlc.html#1389" class="Bound"
      >N&#8242;</a
      ><a name="1391" class="Symbol"
      >)</a
      ><a name="1392"
      > </a
      ><a name="1393" href="Stlc.html#1276" class="Function Operator"
      >[</a
      ><a name="1394"
      > </a
      ><a name="1395" href="Stlc.html#1395" class="Bound"
      >x</a
      ><a name="1396"
      > </a
      ><a name="1397" href="Stlc.html#1276" class="Function Operator"
      >:=</a
      ><a name="1399"
      > </a
      ><a name="1400" href="Stlc.html#1400" class="Bound"
      >V</a
      ><a name="1401"
      > </a
      ><a name="1402" href="Stlc.html#1276" class="Function Operator"
      >]</a
      ><a name="1403"
      > </a
      ><a name="1404" class="Keyword"
      >with</a
      ><a name="1408"
      > </a
      ><a name="1409" href="Stlc.html#1395" class="Bound"
      >x</a
      ><a name="1410"
      > </a
      ><a name="1411" href="Maps.html#2509" class="Function Operator"
      >&#8799;</a
      ><a name="1412"
      > </a
      ><a name="1413" href="Stlc.html#1379" class="Bound"
      >x&#8242;</a
      ><a name="1415"
      >
</a
      ><a name="1416" class="Symbol"
      >...</a
      ><a name="1419"
      > </a
      ><a name="1420" class="Symbol"
      >|</a
      ><a name="1421"
      > </a
      ><a name="1422" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#520" class="InductiveConstructor"
      >yes</a
      ><a name="1425"
      > </a
      ><a name="1426" class="Symbol"
      >_</a
      ><a name="1427"
      > </a
      ><a name="1428" class="Symbol"
      >=</a
      ><a name="1429"
      > </a
      ><a name="1430" href="Stlc.html#743" class="InductiveConstructor Operator"
      >&#955;[</a
      ><a name="1432"
      > </a
      ><a name="1433" href="Stlc.html#1379" class="Bound"
      >x&#8242;</a
      ><a name="1435"
      > </a
      ><a name="1436" href="Stlc.html#743" class="InductiveConstructor Operator"
      >&#8758;</a
      ><a name="1437"
      > </a
      ><a name="1438" href="Stlc.html#1384" class="Bound"
      >A&#8242;</a
      ><a name="1440"
      > </a
      ><a name="1441" href="Stlc.html#743" class="InductiveConstructor Operator"
      >]</a
      ><a name="1442"
      > </a
      ><a name="1443" href="Stlc.html#1389" class="Bound"
      >N&#8242;</a
      ><a name="1445"
      >
</a
      ><a name="1446" class="Symbol"
      >...</a
      ><a name="1449"
      > </a
      ><a name="1450" class="Symbol"
      >|</a
      ><a name="1451"
      > </a
      ><a name="1452" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#547" class="InductiveConstructor"
      >no</a
      ><a name="1454"
      >  </a
      ><a name="1456" class="Symbol"
      >_</a
      ><a name="1457"
      > </a
      ><a name="1458" class="Symbol"
      >=</a
      ><a name="1459"
      > </a
      ><a name="1460" href="Stlc.html#743" class="InductiveConstructor Operator"
      >&#955;[</a
      ><a name="1462"
      > </a
      ><a name="1463" href="Stlc.html#1379" class="Bound"
      >x&#8242;</a
      ><a name="1465"
      > </a
      ><a name="1466" href="Stlc.html#743" class="InductiveConstructor Operator"
      >&#8758;</a
      ><a name="1467"
      > </a
      ><a name="1468" href="Stlc.html#1384" class="Bound"
      >A&#8242;</a
      ><a name="1470"
      > </a
      ><a name="1471" href="Stlc.html#743" class="InductiveConstructor Operator"
      >]</a
      ><a name="1472"
      > </a
      ><a name="1473" class="Symbol"
      >(</a
      ><a name="1474" href="Stlc.html#1389" class="Bound"
      >N&#8242;</a
      ><a name="1476"
      > </a
      ><a name="1477" href="Stlc.html#1276" class="Function Operator"
      >[</a
      ><a name="1478"
      > </a
      ><a name="1479" href="Stlc.html#1395" class="Bound"
      >x</a
      ><a name="1480"
      > </a
      ><a name="1481" href="Stlc.html#1276" class="Function Operator"
      >:=</a
      ><a name="1483"
      > </a
      ><a name="1484" href="Stlc.html#1400" class="Bound"
      >V</a
      ><a name="1485"
      > </a
      ><a name="1486" href="Stlc.html#1276" class="Function Operator"
      >]</a
      ><a name="1487" class="Symbol"
      >)</a
      ><a name="1488"
      >
</a
      ><a name="1489" class="Symbol"
      >(</a
      ><a name="1490" href="Stlc.html#1490" class="Bound"
      >L&#8242;</a
      ><a name="1492"
      > </a
      ><a name="1493" href="Stlc.html#779" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="1494"
      > </a
      ><a name="1495" href="Stlc.html#1495" class="Bound"
      >M&#8242;</a
      ><a name="1497" class="Symbol"
      >)</a
      ><a name="1498"
      > </a
      ><a name="1499" href="Stlc.html#1276" class="Function Operator"
      >[</a
      ><a name="1500"
      > </a
      ><a name="1501" href="Stlc.html#1501" class="Bound"
      >x</a
      ><a name="1502"
      > </a
      ><a name="1503" href="Stlc.html#1276" class="Function Operator"
      >:=</a
      ><a name="1505"
      > </a
      ><a name="1506" href="Stlc.html#1506" class="Bound"
      >V</a
      ><a name="1507"
      > </a
      ><a name="1508" href="Stlc.html#1276" class="Function Operator"
      >]</a
      ><a name="1509"
      > </a
      ><a name="1510" class="Symbol"
      >=</a
      ><a name="1511"
      >  </a
      ><a name="1513" class="Symbol"
      >(</a
      ><a name="1514" href="Stlc.html#1490" class="Bound"
      >L&#8242;</a
      ><a name="1516"
      > </a
      ><a name="1517" href="Stlc.html#1276" class="Function Operator"
      >[</a
      ><a name="1518"
      > </a
      ><a name="1519" href="Stlc.html#1501" class="Bound"
      >x</a
      ><a name="1520"
      > </a
      ><a name="1521" href="Stlc.html#1276" class="Function Operator"
      >:=</a
      ><a name="1523"
      > </a
      ><a name="1524" href="Stlc.html#1506" class="Bound"
      >V</a
      ><a name="1525"
      > </a
      ><a name="1526" href="Stlc.html#1276" class="Function Operator"
      >]</a
      ><a name="1527" class="Symbol"
      >)</a
      ><a name="1528"
      > </a
      ><a name="1529" href="Stlc.html#779" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="1530"
      > </a
      ><a name="1531" class="Symbol"
      >(</a
      ><a name="1532" href="Stlc.html#1495" class="Bound"
      >M&#8242;</a
      ><a name="1534"
      > </a
      ><a name="1535" href="Stlc.html#1276" class="Function Operator"
      >[</a
      ><a name="1536"
      > </a
      ><a name="1537" href="Stlc.html#1501" class="Bound"
      >x</a
      ><a name="1538"
      > </a
      ><a name="1539" href="Stlc.html#1276" class="Function Operator"
      >:=</a
      ><a name="1541"
      > </a
      ><a name="1542" href="Stlc.html#1506" class="Bound"
      >V</a
      ><a name="1543"
      > </a
      ><a name="1544" href="Stlc.html#1276" class="Function Operator"
      >]</a
      ><a name="1545" class="Symbol"
      >)</a
      ><a name="1546"
      >
</a
      ><a name="1547" class="Symbol"
      >(</a
      ><a name="1548" href="Stlc.html#806" class="InductiveConstructor"
      >true</a
      ><a name="1552" class="Symbol"
      >)</a
      ><a name="1553"
      > </a
      ><a name="1554" href="Stlc.html#1276" class="Function Operator"
      >[</a
      ><a name="1555"
      > </a
      ><a name="1556" href="Stlc.html#1556" class="Bound"
      >x</a
      ><a name="1557"
      > </a
      ><a name="1558" href="Stlc.html#1276" class="Function Operator"
      >:=</a
      ><a name="1560"
      > </a
      ><a name="1561" href="Stlc.html#1561" class="Bound"
      >V</a
      ><a name="1562"
      > </a
      ><a name="1563" href="Stlc.html#1276" class="Function Operator"
      >]</a
      ><a name="1564"
      > </a
      ><a name="1565" class="Symbol"
      >=</a
      ><a name="1566"
      > </a
      ><a name="1567" href="Stlc.html#806" class="InductiveConstructor"
      >true</a
      ><a name="1571"
      >
</a
      ><a name="1572" class="Symbol"
      >(</a
      ><a name="1573" href="Stlc.html#820" class="InductiveConstructor"
      >false</a
      ><a name="1578" class="Symbol"
      >)</a
      ><a name="1579"
      > </a
      ><a name="1580" href="Stlc.html#1276" class="Function Operator"
      >[</a
      ><a name="1581"
      > </a
      ><a name="1582" href="Stlc.html#1582" class="Bound"
      >x</a
      ><a name="1583"
      > </a
      ><a name="1584" href="Stlc.html#1276" class="Function Operator"
      >:=</a
      ><a name="1586"
      > </a
      ><a name="1587" href="Stlc.html#1587" class="Bound"
      >V</a
      ><a name="1588"
      > </a
      ><a name="1589" href="Stlc.html#1276" class="Function Operator"
      >]</a
      ><a name="1590"
      > </a
      ><a name="1591" class="Symbol"
      >=</a
      ><a name="1592"
      > </a
      ><a name="1593" href="Stlc.html#820" class="InductiveConstructor"
      >false</a
      ><a name="1598"
      >
</a
      ><a name="1599" class="Symbol"
      >(</a
      ><a name="1600" href="Stlc.html#835" class="InductiveConstructor Operator"
      >if</a
      ><a name="1602"
      > </a
      ><a name="1603" href="Stlc.html#1603" class="Bound"
      >L&#8242;</a
      ><a name="1605"
      > </a
      ><a name="1606" href="Stlc.html#835" class="InductiveConstructor Operator"
      >then</a
      ><a name="1610"
      > </a
      ><a name="1611" href="Stlc.html#1611" class="Bound"
      >M&#8242;</a
      ><a name="1613"
      > </a
      ><a name="1614" href="Stlc.html#835" class="InductiveConstructor Operator"
      >else</a
      ><a name="1618"
      > </a
      ><a name="1619" href="Stlc.html#1619" class="Bound"
      >N&#8242;</a
      ><a name="1621" class="Symbol"
      >)</a
      ><a name="1622"
      > </a
      ><a name="1623" href="Stlc.html#1276" class="Function Operator"
      >[</a
      ><a name="1624"
      > </a
      ><a name="1625" href="Stlc.html#1625" class="Bound"
      >x</a
      ><a name="1626"
      > </a
      ><a name="1627" href="Stlc.html#1276" class="Function Operator"
      >:=</a
      ><a name="1629"
      > </a
      ><a name="1630" href="Stlc.html#1630" class="Bound"
      >V</a
      ><a name="1631"
      > </a
      ><a name="1632" href="Stlc.html#1276" class="Function Operator"
      >]</a
      ><a name="1633"
      > </a
      ><a name="1634" class="Symbol"
      >=</a
      ><a name="1635"
      > </a
      ><a name="1636" href="Stlc.html#835" class="InductiveConstructor Operator"
      >if</a
      ><a name="1638"
      > </a
      ><a name="1639" class="Symbol"
      >(</a
      ><a name="1640" href="Stlc.html#1603" class="Bound"
      >L&#8242;</a
      ><a name="1642"
      > </a
      ><a name="1643" href="Stlc.html#1276" class="Function Operator"
      >[</a
      ><a name="1644"
      > </a
      ><a name="1645" href="Stlc.html#1625" class="Bound"
      >x</a
      ><a name="1646"
      > </a
      ><a name="1647" href="Stlc.html#1276" class="Function Operator"
      >:=</a
      ><a name="1649"
      > </a
      ><a name="1650" href="Stlc.html#1630" class="Bound"
      >V</a
      ><a name="1651"
      > </a
      ><a name="1652" href="Stlc.html#1276" class="Function Operator"
      >]</a
      ><a name="1653" class="Symbol"
      >)</a
      ><a name="1654"
      > </a
      ><a name="1655" href="Stlc.html#835" class="InductiveConstructor Operator"
      >then</a
      ><a name="1659"
      > </a
      ><a name="1660" class="Symbol"
      >(</a
      ><a name="1661" href="Stlc.html#1611" class="Bound"
      >M&#8242;</a
      ><a name="1663"
      > </a
      ><a name="1664" href="Stlc.html#1276" class="Function Operator"
      >[</a
      ><a name="1665"
      > </a
      ><a name="1666" href="Stlc.html#1625" class="Bound"
      >x</a
      ><a name="1667"
      > </a
      ><a name="1668" href="Stlc.html#1276" class="Function Operator"
      >:=</a
      ><a name="1670"
      > </a
      ><a name="1671" href="Stlc.html#1630" class="Bound"
      >V</a
      ><a name="1672"
      > </a
      ><a name="1673" href="Stlc.html#1276" class="Function Operator"
      >]</a
      ><a name="1674" class="Symbol"
      >)</a
      ><a name="1675"
      > </a
      ><a name="1676" href="Stlc.html#835" class="InductiveConstructor Operator"
      >else</a
      ><a name="1680"
      > </a
      ><a name="1681" class="Symbol"
      >(</a
      ><a name="1682" href="Stlc.html#1619" class="Bound"
      >N&#8242;</a
      ><a name="1684"
      > </a
      ><a name="1685" href="Stlc.html#1276" class="Function Operator"
      >[</a
      ><a name="1686"
      > </a
      ><a name="1687" href="Stlc.html#1625" class="Bound"
      >x</a
      ><a name="1688"
      > </a
      ><a name="1689" href="Stlc.html#1276" class="Function Operator"
      >:=</a
      ><a name="1691"
      > </a
      ><a name="1692" href="Stlc.html#1630" class="Bound"
      >V</a
      ><a name="1693"
      > </a
      ><a name="1694" href="Stlc.html#1276" class="Function Operator"
      >]</a
      ><a name="1695" class="Symbol"
      >)</a
      >

</pre>

## Reduction rules

<pre class="Agda">

<a name="1742" class="Keyword"
      >infix</a
      ><a name="1747"
      > </a
      ><a name="1748" class="Number"
      >10</a
      ><a name="1750"
      > </a
      ><a name="1751" href="Stlc.html#1762" class="Datatype Operator"
      >_&#10233;_</a
      ><a name="1754"
      > 

</a
      ><a name="1757" class="Keyword"
      >data</a
      ><a name="1761"
      > </a
      ><a name="1762" href="Stlc.html#1762" class="Datatype Operator"
      >_&#10233;_</a
      ><a name="1765"
      > </a
      ><a name="1766" class="Symbol"
      >:</a
      ><a name="1767"
      > </a
      ><a name="1768" href="Stlc.html#708" class="Datatype"
      >Term</a
      ><a name="1772"
      > </a
      ><a name="1773" class="Symbol"
      >&#8594;</a
      ><a name="1774"
      > </a
      ><a name="1775" href="Stlc.html#708" class="Datatype"
      >Term</a
      ><a name="1779"
      > </a
      ><a name="1780" class="Symbol"
      >&#8594;</a
      ><a name="1781"
      > </a
      ><a name="1782" class="PrimitiveType"
      >Set</a
      ><a name="1785"
      > </a
      ><a name="1786" class="Keyword"
      >where</a
      ><a name="1791"
      >
  </a
      ><a name="1794" href="Stlc.html#1794" class="InductiveConstructor"
      >&#946;&#955;&#183;</a
      ><a name="1797"
      > </a
      ><a name="1798" class="Symbol"
      >:</a
      ><a name="1799"
      > </a
      ><a name="1800" class="Symbol"
      >&#8704;</a
      ><a name="1801"
      > </a
      ><a name="1802" class="Symbol"
      >{</a
      ><a name="1803" href="Stlc.html#1803" class="Bound"
      >x</a
      ><a name="1804"
      > </a
      ><a name="1805" href="Stlc.html#1805" class="Bound"
      >A</a
      ><a name="1806"
      > </a
      ><a name="1807" href="Stlc.html#1807" class="Bound"
      >N</a
      ><a name="1808"
      > </a
      ><a name="1809" href="Stlc.html#1809" class="Bound"
      >V</a
      ><a name="1810" class="Symbol"
      >}</a
      ><a name="1811"
      > </a
      ><a name="1812" class="Symbol"
      >&#8594;</a
      ><a name="1813"
      > </a
      ><a name="1814" href="Stlc.html#1105" class="Datatype"
      >Value</a
      ><a name="1819"
      > </a
      ><a name="1820" href="Stlc.html#1809" class="Bound"
      >V</a
      ><a name="1821"
      > </a
      ><a name="1822" class="Symbol"
      >&#8594;</a
      ><a name="1823"
      >
    </a
      ><a name="1828" class="Symbol"
      >(</a
      ><a name="1829" href="Stlc.html#743" class="InductiveConstructor Operator"
      >&#955;[</a
      ><a name="1831"
      > </a
      ><a name="1832" href="Stlc.html#1803" class="Bound"
      >x</a
      ><a name="1833"
      > </a
      ><a name="1834" href="Stlc.html#743" class="InductiveConstructor Operator"
      >&#8758;</a
      ><a name="1835"
      > </a
      ><a name="1836" href="Stlc.html#1805" class="Bound"
      >A</a
      ><a name="1837"
      > </a
      ><a name="1838" href="Stlc.html#743" class="InductiveConstructor Operator"
      >]</a
      ><a name="1839"
      > </a
      ><a name="1840" href="Stlc.html#1807" class="Bound"
      >N</a
      ><a name="1841" class="Symbol"
      >)</a
      ><a name="1842"
      > </a
      ><a name="1843" href="Stlc.html#779" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="1844"
      > </a
      ><a name="1845" href="Stlc.html#1809" class="Bound"
      >V</a
      ><a name="1846"
      > </a
      ><a name="1847" href="Stlc.html#1762" class="Datatype Operator"
      >&#10233;</a
      ><a name="1848"
      > </a
      ><a name="1849" href="Stlc.html#1807" class="Bound"
      >N</a
      ><a name="1850"
      > </a
      ><a name="1851" href="Stlc.html#1276" class="Function Operator"
      >[</a
      ><a name="1852"
      > </a
      ><a name="1853" href="Stlc.html#1803" class="Bound"
      >x</a
      ><a name="1854"
      > </a
      ><a name="1855" href="Stlc.html#1276" class="Function Operator"
      >:=</a
      ><a name="1857"
      > </a
      ><a name="1858" href="Stlc.html#1809" class="Bound"
      >V</a
      ><a name="1859"
      > </a
      ><a name="1860" href="Stlc.html#1276" class="Function Operator"
      >]</a
      ><a name="1861"
      >
  </a
      ><a name="1864" href="Stlc.html#1864" class="InductiveConstructor"
      >&#958;&#183;&#8321;</a
      ><a name="1867"
      > </a
      ><a name="1868" class="Symbol"
      >:</a
      ><a name="1869"
      > </a
      ><a name="1870" class="Symbol"
      >&#8704;</a
      ><a name="1871"
      > </a
      ><a name="1872" class="Symbol"
      >{</a
      ><a name="1873" href="Stlc.html#1873" class="Bound"
      >L</a
      ><a name="1874"
      > </a
      ><a name="1875" href="Stlc.html#1875" class="Bound"
      >L&#8242;</a
      ><a name="1877"
      > </a
      ><a name="1878" href="Stlc.html#1878" class="Bound"
      >M</a
      ><a name="1879" class="Symbol"
      >}</a
      ><a name="1880"
      > </a
      ><a name="1881" class="Symbol"
      >&#8594;</a
      ><a name="1882"
      >
    </a
      ><a name="1887" href="Stlc.html#1873" class="Bound"
      >L</a
      ><a name="1888"
      > </a
      ><a name="1889" href="Stlc.html#1762" class="Datatype Operator"
      >&#10233;</a
      ><a name="1890"
      > </a
      ><a name="1891" href="Stlc.html#1875" class="Bound"
      >L&#8242;</a
      ><a name="1893"
      > </a
      ><a name="1894" class="Symbol"
      >&#8594;</a
      ><a name="1895"
      >
    </a
      ><a name="1900" href="Stlc.html#1873" class="Bound"
      >L</a
      ><a name="1901"
      > </a
      ><a name="1902" href="Stlc.html#779" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="1903"
      > </a
      ><a name="1904" href="Stlc.html#1878" class="Bound"
      >M</a
      ><a name="1905"
      > </a
      ><a name="1906" href="Stlc.html#1762" class="Datatype Operator"
      >&#10233;</a
      ><a name="1907"
      > </a
      ><a name="1908" href="Stlc.html#1875" class="Bound"
      >L&#8242;</a
      ><a name="1910"
      > </a
      ><a name="1911" href="Stlc.html#779" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="1912"
      > </a
      ><a name="1913" href="Stlc.html#1878" class="Bound"
      >M</a
      ><a name="1914"
      >
  </a
      ><a name="1917" href="Stlc.html#1917" class="InductiveConstructor"
      >&#958;&#183;&#8322;</a
      ><a name="1920"
      > </a
      ><a name="1921" class="Symbol"
      >:</a
      ><a name="1922"
      > </a
      ><a name="1923" class="Symbol"
      >&#8704;</a
      ><a name="1924"
      > </a
      ><a name="1925" class="Symbol"
      >{</a
      ><a name="1926" href="Stlc.html#1926" class="Bound"
      >V</a
      ><a name="1927"
      > </a
      ><a name="1928" href="Stlc.html#1928" class="Bound"
      >M</a
      ><a name="1929"
      > </a
      ><a name="1930" href="Stlc.html#1930" class="Bound"
      >M&#8242;</a
      ><a name="1932" class="Symbol"
      >}</a
      ><a name="1933"
      > </a
      ><a name="1934" class="Symbol"
      >&#8594;</a
      ><a name="1935"
      >
    </a
      ><a name="1940" href="Stlc.html#1105" class="Datatype"
      >Value</a
      ><a name="1945"
      > </a
      ><a name="1946" href="Stlc.html#1926" class="Bound"
      >V</a
      ><a name="1947"
      > </a
      ><a name="1948" class="Symbol"
      >&#8594;</a
      ><a name="1949"
      >
    </a
      ><a name="1954" href="Stlc.html#1928" class="Bound"
      >M</a
      ><a name="1955"
      > </a
      ><a name="1956" href="Stlc.html#1762" class="Datatype Operator"
      >&#10233;</a
      ><a name="1957"
      > </a
      ><a name="1958" href="Stlc.html#1930" class="Bound"
      >M&#8242;</a
      ><a name="1960"
      > </a
      ><a name="1961" class="Symbol"
      >&#8594;</a
      ><a name="1962"
      >
    </a
      ><a name="1967" href="Stlc.html#1926" class="Bound"
      >V</a
      ><a name="1968"
      > </a
      ><a name="1969" href="Stlc.html#779" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="1970"
      > </a
      ><a name="1971" href="Stlc.html#1928" class="Bound"
      >M</a
      ><a name="1972"
      > </a
      ><a name="1973" href="Stlc.html#1762" class="Datatype Operator"
      >&#10233;</a
      ><a name="1974"
      > </a
      ><a name="1975" href="Stlc.html#1926" class="Bound"
      >V</a
      ><a name="1976"
      > </a
      ><a name="1977" href="Stlc.html#779" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="1978"
      > </a
      ><a name="1979" href="Stlc.html#1930" class="Bound"
      >M&#8242;</a
      ><a name="1981"
      >
  </a
      ><a name="1984" href="Stlc.html#1984" class="InductiveConstructor"
      >&#946;if-true</a
      ><a name="1992"
      > </a
      ><a name="1993" class="Symbol"
      >:</a
      ><a name="1994"
      > </a
      ><a name="1995" class="Symbol"
      >&#8704;</a
      ><a name="1996"
      > </a
      ><a name="1997" class="Symbol"
      >{</a
      ><a name="1998" href="Stlc.html#1998" class="Bound"
      >M</a
      ><a name="1999"
      > </a
      ><a name="2000" href="Stlc.html#2000" class="Bound"
      >N</a
      ><a name="2001" class="Symbol"
      >}</a
      ><a name="2002"
      > </a
      ><a name="2003" class="Symbol"
      >&#8594;</a
      ><a name="2004"
      >
    </a
      ><a name="2009" href="Stlc.html#835" class="InductiveConstructor Operator"
      >if</a
      ><a name="2011"
      > </a
      ><a name="2012" href="Stlc.html#806" class="InductiveConstructor"
      >true</a
      ><a name="2016"
      > </a
      ><a name="2017" href="Stlc.html#835" class="InductiveConstructor Operator"
      >then</a
      ><a name="2021"
      > </a
      ><a name="2022" href="Stlc.html#1998" class="Bound"
      >M</a
      ><a name="2023"
      > </a
      ><a name="2024" href="Stlc.html#835" class="InductiveConstructor Operator"
      >else</a
      ><a name="2028"
      > </a
      ><a name="2029" href="Stlc.html#2000" class="Bound"
      >N</a
      ><a name="2030"
      > </a
      ><a name="2031" href="Stlc.html#1762" class="Datatype Operator"
      >&#10233;</a
      ><a name="2032"
      > </a
      ><a name="2033" href="Stlc.html#1998" class="Bound"
      >M</a
      ><a name="2034"
      >
  </a
      ><a name="2037" href="Stlc.html#2037" class="InductiveConstructor"
      >&#946;if-false</a
      ><a name="2046"
      > </a
      ><a name="2047" class="Symbol"
      >:</a
      ><a name="2048"
      > </a
      ><a name="2049" class="Symbol"
      >&#8704;</a
      ><a name="2050"
      > </a
      ><a name="2051" class="Symbol"
      >{</a
      ><a name="2052" href="Stlc.html#2052" class="Bound"
      >M</a
      ><a name="2053"
      > </a
      ><a name="2054" href="Stlc.html#2054" class="Bound"
      >N</a
      ><a name="2055" class="Symbol"
      >}</a
      ><a name="2056"
      > </a
      ><a name="2057" class="Symbol"
      >&#8594;</a
      ><a name="2058"
      >
    </a
      ><a name="2063" href="Stlc.html#835" class="InductiveConstructor Operator"
      >if</a
      ><a name="2065"
      > </a
      ><a name="2066" href="Stlc.html#820" class="InductiveConstructor"
      >false</a
      ><a name="2071"
      > </a
      ><a name="2072" href="Stlc.html#835" class="InductiveConstructor Operator"
      >then</a
      ><a name="2076"
      > </a
      ><a name="2077" href="Stlc.html#2052" class="Bound"
      >M</a
      ><a name="2078"
      > </a
      ><a name="2079" href="Stlc.html#835" class="InductiveConstructor Operator"
      >else</a
      ><a name="2083"
      > </a
      ><a name="2084" href="Stlc.html#2054" class="Bound"
      >N</a
      ><a name="2085"
      > </a
      ><a name="2086" href="Stlc.html#1762" class="Datatype Operator"
      >&#10233;</a
      ><a name="2087"
      > </a
      ><a name="2088" href="Stlc.html#2054" class="Bound"
      >N</a
      ><a name="2089"
      >
  </a
      ><a name="2092" href="Stlc.html#2092" class="InductiveConstructor"
      >&#958;if</a
      ><a name="2095"
      > </a
      ><a name="2096" class="Symbol"
      >:</a
      ><a name="2097"
      > </a
      ><a name="2098" class="Symbol"
      >&#8704;</a
      ><a name="2099"
      > </a
      ><a name="2100" class="Symbol"
      >{</a
      ><a name="2101" href="Stlc.html#2101" class="Bound"
      >L</a
      ><a name="2102"
      > </a
      ><a name="2103" href="Stlc.html#2103" class="Bound"
      >L&#8242;</a
      ><a name="2105"
      > </a
      ><a name="2106" href="Stlc.html#2106" class="Bound"
      >M</a
      ><a name="2107"
      > </a
      ><a name="2108" href="Stlc.html#2108" class="Bound"
      >N</a
      ><a name="2109" class="Symbol"
      >}</a
      ><a name="2110"
      > </a
      ><a name="2111" class="Symbol"
      >&#8594;</a
      ><a name="2112"
      >
    </a
      ><a name="2117" href="Stlc.html#2101" class="Bound"
      >L</a
      ><a name="2118"
      > </a
      ><a name="2119" href="Stlc.html#1762" class="Datatype Operator"
      >&#10233;</a
      ><a name="2120"
      > </a
      ><a name="2121" href="Stlc.html#2103" class="Bound"
      >L&#8242;</a
      ><a name="2123"
      > </a
      ><a name="2124" class="Symbol"
      >&#8594;</a
      ><a name="2125"
      >    
    </a
      ><a name="2134" href="Stlc.html#835" class="InductiveConstructor Operator"
      >if</a
      ><a name="2136"
      > </a
      ><a name="2137" href="Stlc.html#2101" class="Bound"
      >L</a
      ><a name="2138"
      > </a
      ><a name="2139" href="Stlc.html#835" class="InductiveConstructor Operator"
      >then</a
      ><a name="2143"
      > </a
      ><a name="2144" href="Stlc.html#2106" class="Bound"
      >M</a
      ><a name="2145"
      > </a
      ><a name="2146" href="Stlc.html#835" class="InductiveConstructor Operator"
      >else</a
      ><a name="2150"
      > </a
      ><a name="2151" href="Stlc.html#2108" class="Bound"
      >N</a
      ><a name="2152"
      > </a
      ><a name="2153" href="Stlc.html#1762" class="Datatype Operator"
      >&#10233;</a
      ><a name="2154"
      > </a
      ><a name="2155" href="Stlc.html#835" class="InductiveConstructor Operator"
      >if</a
      ><a name="2157"
      > </a
      ><a name="2158" href="Stlc.html#2103" class="Bound"
      >L&#8242;</a
      ><a name="2160"
      > </a
      ><a name="2161" href="Stlc.html#835" class="InductiveConstructor Operator"
      >then</a
      ><a name="2165"
      > </a
      ><a name="2166" href="Stlc.html#2106" class="Bound"
      >M</a
      ><a name="2167"
      > </a
      ><a name="2168" href="Stlc.html#835" class="InductiveConstructor Operator"
      >else</a
      ><a name="2172"
      > </a
      ><a name="2173" href="Stlc.html#2108" class="Bound"
      >N</a
      >

</pre>

## Reflexive and transitive closure


<pre class="Agda">

<a name="2238" class="Keyword"
      >infix</a
      ><a name="2243"
      > </a
      ><a name="2244" class="Number"
      >10</a
      ><a name="2246"
      > </a
      ><a name="2247" href="Stlc.html#2287" class="Datatype Operator"
      >_&#10233;*_</a
      ><a name="2251"
      > 
</a
      ><a name="2253" class="Keyword"
      >infixr</a
      ><a name="2259"
      > </a
      ><a name="2260" class="Number"
      >2</a
      ><a name="2261"
      > </a
      ><a name="2262" href="Stlc.html#2340" class="InductiveConstructor Operator"
      >_&#10233;&#10216;_&#10217;_</a
      ><a name="2268"
      >
</a
      ><a name="2269" class="Keyword"
      >infix</a
      ><a name="2274"
      >  </a
      ><a name="2276" class="Number"
      >3</a
      ><a name="2277"
      > </a
      ><a name="2278" href="Stlc.html#2320" class="InductiveConstructor Operator"
      >_&#8718;</a
      ><a name="2280"
      >

</a
      ><a name="2282" class="Keyword"
      >data</a
      ><a name="2286"
      > </a
      ><a name="2287" href="Stlc.html#2287" class="Datatype Operator"
      >_&#10233;*_</a
      ><a name="2291"
      > </a
      ><a name="2292" class="Symbol"
      >:</a
      ><a name="2293"
      > </a
      ><a name="2294" href="Stlc.html#708" class="Datatype"
      >Term</a
      ><a name="2298"
      > </a
      ><a name="2299" class="Symbol"
      >&#8594;</a
      ><a name="2300"
      > </a
      ><a name="2301" href="Stlc.html#708" class="Datatype"
      >Term</a
      ><a name="2305"
      > </a
      ><a name="2306" class="Symbol"
      >&#8594;</a
      ><a name="2307"
      > </a
      ><a name="2308" class="PrimitiveType"
      >Set</a
      ><a name="2311"
      > </a
      ><a name="2312" class="Keyword"
      >where</a
      ><a name="2317"
      >
  </a
      ><a name="2320" href="Stlc.html#2320" class="InductiveConstructor Operator"
      >_&#8718;</a
      ><a name="2322"
      > </a
      ><a name="2323" class="Symbol"
      >:</a
      ><a name="2324"
      > </a
      ><a name="2325" class="Symbol"
      >&#8704;</a
      ><a name="2326"
      > </a
      ><a name="2327" href="Stlc.html#2327" class="Bound"
      >M</a
      ><a name="2328"
      > </a
      ><a name="2329" class="Symbol"
      >&#8594;</a
      ><a name="2330"
      > </a
      ><a name="2331" href="Stlc.html#2327" class="Bound"
      >M</a
      ><a name="2332"
      > </a
      ><a name="2333" href="Stlc.html#2287" class="Datatype Operator"
      >&#10233;*</a
      ><a name="2335"
      > </a
      ><a name="2336" href="Stlc.html#2327" class="Bound"
      >M</a
      ><a name="2337"
      >
  </a
      ><a name="2340" href="Stlc.html#2340" class="InductiveConstructor Operator"
      >_&#10233;&#10216;_&#10217;_</a
      ><a name="2346"
      > </a
      ><a name="2347" class="Symbol"
      >:</a
      ><a name="2348"
      > </a
      ><a name="2349" class="Symbol"
      >&#8704;</a
      ><a name="2350"
      > </a
      ><a name="2351" href="Stlc.html#2351" class="Bound"
      >L</a
      ><a name="2352"
      > </a
      ><a name="2353" class="Symbol"
      >{</a
      ><a name="2354" href="Stlc.html#2354" class="Bound"
      >M</a
      ><a name="2355"
      > </a
      ><a name="2356" href="Stlc.html#2356" class="Bound"
      >N</a
      ><a name="2357" class="Symbol"
      >}</a
      ><a name="2358"
      > </a
      ><a name="2359" class="Symbol"
      >&#8594;</a
      ><a name="2360"
      > </a
      ><a name="2361" href="Stlc.html#2351" class="Bound"
      >L</a
      ><a name="2362"
      > </a
      ><a name="2363" href="Stlc.html#1762" class="Datatype Operator"
      >&#10233;</a
      ><a name="2364"
      > </a
      ><a name="2365" href="Stlc.html#2354" class="Bound"
      >M</a
      ><a name="2366"
      > </a
      ><a name="2367" class="Symbol"
      >&#8594;</a
      ><a name="2368"
      > </a
      ><a name="2369" href="Stlc.html#2354" class="Bound"
      >M</a
      ><a name="2370"
      > </a
      ><a name="2371" href="Stlc.html#2287" class="Datatype Operator"
      >&#10233;*</a
      ><a name="2373"
      > </a
      ><a name="2374" href="Stlc.html#2356" class="Bound"
      >N</a
      ><a name="2375"
      > </a
      ><a name="2376" class="Symbol"
      >&#8594;</a
      ><a name="2377"
      > </a
      ><a name="2378" href="Stlc.html#2351" class="Bound"
      >L</a
      ><a name="2379"
      > </a
      ><a name="2380" href="Stlc.html#2287" class="Datatype Operator"
      >&#10233;*</a
      ><a name="2382"
      > </a
      ><a name="2383" href="Stlc.html#2356" class="Bound"
      >N</a
      ><a name="2384"
      >  

</a
      ><a name="2388" href="Stlc.html#2388" class="Function"
      >reduction&#8321;</a
      ><a name="2398"
      > </a
      ><a name="2399" class="Symbol"
      >:</a
      ><a name="2400"
      > </a
      ><a name="2401" href="Stlc.html#949" class="Function"
      >not</a
      ><a name="2404"
      > </a
      ><a name="2405" href="Stlc.html#779" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="2406"
      > </a
      ><a name="2407" href="Stlc.html#806" class="InductiveConstructor"
      >true</a
      ><a name="2411"
      > </a
      ><a name="2412" href="Stlc.html#2287" class="Datatype Operator"
      >&#10233;*</a
      ><a name="2414"
      > </a
      ><a name="2415" href="Stlc.html#820" class="InductiveConstructor"
      >false</a
      ><a name="2420"
      >
</a
      ><a name="2421" href="Stlc.html#2388" class="Function"
      >reduction&#8321;</a
      ><a name="2431"
      > </a
      ><a name="2432" class="Symbol"
      >=</a
      ><a name="2433"
      >
    </a
      ><a name="2438" href="Stlc.html#949" class="Function"
      >not</a
      ><a name="2441"
      > </a
      ><a name="2442" href="Stlc.html#779" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="2443"
      > </a
      ><a name="2444" href="Stlc.html#806" class="InductiveConstructor"
      >true</a
      ><a name="2448"
      >
  </a
      ><a name="2451" href="Stlc.html#2340" class="InductiveConstructor Operator"
      >&#10233;&#10216;</a
      ><a name="2453"
      > </a
      ><a name="2454" href="Stlc.html#1794" class="InductiveConstructor"
      >&#946;&#955;&#183;</a
      ><a name="2457"
      > </a
      ><a name="2458" href="Stlc.html#1181" class="InductiveConstructor"
      >value-true</a
      ><a name="2468"
      > </a
      ><a name="2469" href="Stlc.html#2340" class="InductiveConstructor Operator"
      >&#10217;</a
      ><a name="2470"
      >
    </a
      ><a name="2475" href="Stlc.html#835" class="InductiveConstructor Operator"
      >if</a
      ><a name="2477"
      > </a
      ><a name="2478" href="Stlc.html#806" class="InductiveConstructor"
      >true</a
      ><a name="2482"
      > </a
      ><a name="2483" href="Stlc.html#835" class="InductiveConstructor Operator"
      >then</a
      ><a name="2487"
      > </a
      ><a name="2488" href="Stlc.html#820" class="InductiveConstructor"
      >false</a
      ><a name="2493"
      > </a
      ><a name="2494" href="Stlc.html#835" class="InductiveConstructor Operator"
      >else</a
      ><a name="2498"
      > </a
      ><a name="2499" href="Stlc.html#806" class="InductiveConstructor"
      >true</a
      ><a name="2503"
      >
  </a
      ><a name="2506" href="Stlc.html#2340" class="InductiveConstructor Operator"
      >&#10233;&#10216;</a
      ><a name="2508"
      > </a
      ><a name="2509" href="Stlc.html#1984" class="InductiveConstructor"
      >&#946;if-true</a
      ><a name="2517"
      > </a
      ><a name="2518" href="Stlc.html#2340" class="InductiveConstructor Operator"
      >&#10217;</a
      ><a name="2519"
      >
    </a
      ><a name="2524" href="Stlc.html#820" class="InductiveConstructor"
      >false</a
      ><a name="2529"
      >
  </a
      ><a name="2532" href="Stlc.html#2320" class="InductiveConstructor Operator"
      >&#8718;</a
      ><a name="2533"
      >

</a
      ><a name="2535" href="Stlc.html#2535" class="Function"
      >reduction&#8322;</a
      ><a name="2545"
      > </a
      ><a name="2546" class="Symbol"
      >:</a
      ><a name="2547"
      > </a
      ><a name="2548" href="Stlc.html#953" class="Function"
      >two</a
      ><a name="2551"
      > </a
      ><a name="2552" href="Stlc.html#779" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="2553"
      > </a
      ><a name="2554" href="Stlc.html#949" class="Function"
      >not</a
      ><a name="2557"
      > </a
      ><a name="2558" href="Stlc.html#779" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="2559"
      > </a
      ><a name="2560" href="Stlc.html#806" class="InductiveConstructor"
      >true</a
      ><a name="2564"
      > </a
      ><a name="2565" href="Stlc.html#2287" class="Datatype Operator"
      >&#10233;*</a
      ><a name="2567"
      > </a
      ><a name="2568" href="Stlc.html#806" class="InductiveConstructor"
      >true</a
      ><a name="2572"
      >
</a
      ><a name="2573" href="Stlc.html#2535" class="Function"
      >reduction&#8322;</a
      ><a name="2583"
      > </a
      ><a name="2584" class="Symbol"
      >=</a
      ><a name="2585"
      >
    </a
      ><a name="2590" href="Stlc.html#953" class="Function"
      >two</a
      ><a name="2593"
      > </a
      ><a name="2594" href="Stlc.html#779" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="2595"
      > </a
      ><a name="2596" href="Stlc.html#949" class="Function"
      >not</a
      ><a name="2599"
      > </a
      ><a name="2600" href="Stlc.html#779" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="2601"
      > </a
      ><a name="2602" href="Stlc.html#806" class="InductiveConstructor"
      >true</a
      ><a name="2606"
      >
  </a
      ><a name="2609" href="Stlc.html#2340" class="InductiveConstructor Operator"
      >&#10233;&#10216;</a
      ><a name="2611"
      > </a
      ><a name="2612" href="Stlc.html#1864" class="InductiveConstructor"
      >&#958;&#183;&#8321;</a
      ><a name="2615"
      > </a
      ><a name="2616" class="Symbol"
      >(</a
      ><a name="2617" href="Stlc.html#1794" class="InductiveConstructor"
      >&#946;&#955;&#183;</a
      ><a name="2620"
      > </a
      ><a name="2621" href="Stlc.html#1132" class="InductiveConstructor"
      >value-&#955;</a
      ><a name="2628" class="Symbol"
      >)</a
      ><a name="2629"
      > </a
      ><a name="2630" href="Stlc.html#2340" class="InductiveConstructor Operator"
      >&#10217;</a
      ><a name="2631"
      >
    </a
      ><a name="2636" class="Symbol"
      >(</a
      ><a name="2637" href="Stlc.html#743" class="InductiveConstructor Operator"
      >&#955;[</a
      ><a name="2639"
      > </a
      ><a name="2640" href="Stlc.html#919" class="Function"
      >x</a
      ><a name="2641"
      > </a
      ><a name="2642" href="Stlc.html#743" class="InductiveConstructor Operator"
      >&#8758;</a
      ><a name="2643"
      > </a
      ><a name="2644" href="Stlc.html#609" class="InductiveConstructor"
      >&#120121;</a
      ><a name="2645"
      > </a
      ><a name="2646" href="Stlc.html#743" class="InductiveConstructor Operator"
      >]</a
      ><a name="2647"
      > </a
      ><a name="2648" href="Stlc.html#949" class="Function"
      >not</a
      ><a name="2651"
      > </a
      ><a name="2652" href="Stlc.html#779" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="2653"
      > </a
      ><a name="2654" class="Symbol"
      >(</a
      ><a name="2655" href="Stlc.html#949" class="Function"
      >not</a
      ><a name="2658"
      > </a
      ><a name="2659" href="Stlc.html#779" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="2660"
      > </a
      ><a name="2661" href="Stlc.html#727" class="InductiveConstructor"
      >`</a
      ><a name="2662"
      > </a
      ><a name="2663" href="Stlc.html#919" class="Function"
      >x</a
      ><a name="2664" class="Symbol"
      >))</a
      ><a name="2666"
      > </a
      ><a name="2667" href="Stlc.html#779" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="2668"
      > </a
      ><a name="2669" href="Stlc.html#806" class="InductiveConstructor"
      >true</a
      ><a name="2673"
      >
  </a
      ><a name="2676" href="Stlc.html#2340" class="InductiveConstructor Operator"
      >&#10233;&#10216;</a
      ><a name="2678"
      > </a
      ><a name="2679" href="Stlc.html#1794" class="InductiveConstructor"
      >&#946;&#955;&#183;</a
      ><a name="2682"
      > </a
      ><a name="2683" href="Stlc.html#1181" class="InductiveConstructor"
      >value-true</a
      ><a name="2693"
      > </a
      ><a name="2694" href="Stlc.html#2340" class="InductiveConstructor Operator"
      >&#10217;</a
      ><a name="2695"
      >
    </a
      ><a name="2700" href="Stlc.html#949" class="Function"
      >not</a
      ><a name="2703"
      > </a
      ><a name="2704" href="Stlc.html#779" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="2705"
      > </a
      ><a name="2706" class="Symbol"
      >(</a
      ><a name="2707" href="Stlc.html#949" class="Function"
      >not</a
      ><a name="2710"
      > </a
      ><a name="2711" href="Stlc.html#779" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="2712"
      > </a
      ><a name="2713" href="Stlc.html#806" class="InductiveConstructor"
      >true</a
      ><a name="2717" class="Symbol"
      >)</a
      ><a name="2718"
      >
  </a
      ><a name="2721" href="Stlc.html#2340" class="InductiveConstructor Operator"
      >&#10233;&#10216;</a
      ><a name="2723"
      > </a
      ><a name="2724" href="Stlc.html#1917" class="InductiveConstructor"
      >&#958;&#183;&#8322;</a
      ><a name="2727"
      > </a
      ><a name="2728" href="Stlc.html#1132" class="InductiveConstructor"
      >value-&#955;</a
      ><a name="2735"
      > </a
      ><a name="2736" class="Symbol"
      >(</a
      ><a name="2737" href="Stlc.html#1794" class="InductiveConstructor"
      >&#946;&#955;&#183;</a
      ><a name="2740"
      > </a
      ><a name="2741" href="Stlc.html#1181" class="InductiveConstructor"
      >value-true</a
      ><a name="2751" class="Symbol"
      >)</a
      ><a name="2752"
      > </a
      ><a name="2753" href="Stlc.html#2340" class="InductiveConstructor Operator"
      >&#10217;</a
      ><a name="2754"
      >
    </a
      ><a name="2759" href="Stlc.html#949" class="Function"
      >not</a
      ><a name="2762"
      > </a
      ><a name="2763" href="Stlc.html#779" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="2764"
      > </a
      ><a name="2765" class="Symbol"
      >(</a
      ><a name="2766" href="Stlc.html#835" class="InductiveConstructor Operator"
      >if</a
      ><a name="2768"
      > </a
      ><a name="2769" href="Stlc.html#806" class="InductiveConstructor"
      >true</a
      ><a name="2773"
      > </a
      ><a name="2774" href="Stlc.html#835" class="InductiveConstructor Operator"
      >then</a
      ><a name="2778"
      > </a
      ><a name="2779" href="Stlc.html#820" class="InductiveConstructor"
      >false</a
      ><a name="2784"
      > </a
      ><a name="2785" href="Stlc.html#835" class="InductiveConstructor Operator"
      >else</a
      ><a name="2789"
      > </a
      ><a name="2790" href="Stlc.html#806" class="InductiveConstructor"
      >true</a
      ><a name="2794" class="Symbol"
      >)</a
      ><a name="2795"
      >
  </a
      ><a name="2798" href="Stlc.html#2340" class="InductiveConstructor Operator"
      >&#10233;&#10216;</a
      ><a name="2800"
      > </a
      ><a name="2801" href="Stlc.html#1917" class="InductiveConstructor"
      >&#958;&#183;&#8322;</a
      ><a name="2804"
      > </a
      ><a name="2805" href="Stlc.html#1132" class="InductiveConstructor"
      >value-&#955;</a
      ><a name="2812"
      > </a
      ><a name="2813" href="Stlc.html#1984" class="InductiveConstructor"
      >&#946;if-true</a
      ><a name="2821"
      >  </a
      ><a name="2823" href="Stlc.html#2340" class="InductiveConstructor Operator"
      >&#10217;</a
      ><a name="2824"
      >
    </a
      ><a name="2829" href="Stlc.html#949" class="Function"
      >not</a
      ><a name="2832"
      > </a
      ><a name="2833" href="Stlc.html#779" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="2834"
      > </a
      ><a name="2835" href="Stlc.html#820" class="InductiveConstructor"
      >false</a
      ><a name="2840"
      >
  </a
      ><a name="2843" href="Stlc.html#2340" class="InductiveConstructor Operator"
      >&#10233;&#10216;</a
      ><a name="2845"
      > </a
      ><a name="2846" href="Stlc.html#1794" class="InductiveConstructor"
      >&#946;&#955;&#183;</a
      ><a name="2849"
      > </a
      ><a name="2850" href="Stlc.html#1208" class="InductiveConstructor"
      >value-false</a
      ><a name="2861"
      > </a
      ><a name="2862" href="Stlc.html#2340" class="InductiveConstructor Operator"
      >&#10217;</a
      ><a name="2863"
      >
    </a
      ><a name="2868" href="Stlc.html#835" class="InductiveConstructor Operator"
      >if</a
      ><a name="2870"
      > </a
      ><a name="2871" href="Stlc.html#820" class="InductiveConstructor"
      >false</a
      ><a name="2876"
      > </a
      ><a name="2877" href="Stlc.html#835" class="InductiveConstructor Operator"
      >then</a
      ><a name="2881"
      > </a
      ><a name="2882" href="Stlc.html#820" class="InductiveConstructor"
      >false</a
      ><a name="2887"
      > </a
      ><a name="2888" href="Stlc.html#835" class="InductiveConstructor Operator"
      >else</a
      ><a name="2892"
      > </a
      ><a name="2893" href="Stlc.html#806" class="InductiveConstructor"
      >true</a
      ><a name="2897"
      >
  </a
      ><a name="2900" href="Stlc.html#2340" class="InductiveConstructor Operator"
      >&#10233;&#10216;</a
      ><a name="2902"
      > </a
      ><a name="2903" href="Stlc.html#2037" class="InductiveConstructor"
      >&#946;if-false</a
      ><a name="2912"
      > </a
      ><a name="2913" href="Stlc.html#2340" class="InductiveConstructor Operator"
      >&#10217;</a
      ><a name="2914"
      >
    </a
      ><a name="2919" href="Stlc.html#806" class="InductiveConstructor"
      >true</a
      ><a name="2923"
      >
  </a
      ><a name="2926" href="Stlc.html#2320" class="InductiveConstructor Operator"
      >&#8718;</a
      >

</pre>

Much of the above, though not all, can be filled in using C-c C-r and C-c C-s.



## Type rules

<pre class="Agda">

<a name="3050" href="Stlc.html#3050" class="Function"
      >Context</a
      ><a name="3057"
      > </a
      ><a name="3058" class="Symbol"
      >:</a
      ><a name="3059"
      > </a
      ><a name="3060" class="PrimitiveType"
      >Set</a
      ><a name="3063"
      >
</a
      ><a name="3064" href="Stlc.html#3050" class="Function"
      >Context</a
      ><a name="3071"
      > </a
      ><a name="3072" class="Symbol"
      >=</a
      ><a name="3073"
      > </a
      ><a name="3074" href="Maps.html#10132" class="Function"
      >PartialMap</a
      ><a name="3084"
      > </a
      ><a name="3085" href="Stlc.html#590" class="Datatype"
      >Type</a
      ><a name="3089"
      >

</a
      ><a name="3091" class="Keyword"
      >infix</a
      ><a name="3096"
      > </a
      ><a name="3097" class="Number"
      >10</a
      ><a name="3099"
      > </a
      ><a name="3100" href="Stlc.html#3112" class="Datatype Operator"
      >_&#8866;_&#8758;_</a
      ><a name="3105"
      >

</a
      ><a name="3107" class="Keyword"
      >data</a
      ><a name="3111"
      > </a
      ><a name="3112" href="Stlc.html#3112" class="Datatype Operator"
      >_&#8866;_&#8758;_</a
      ><a name="3117"
      > </a
      ><a name="3118" class="Symbol"
      >:</a
      ><a name="3119"
      > </a
      ><a name="3120" href="Stlc.html#3050" class="Function"
      >Context</a
      ><a name="3127"
      > </a
      ><a name="3128" class="Symbol"
      >&#8594;</a
      ><a name="3129"
      > </a
      ><a name="3130" href="Stlc.html#708" class="Datatype"
      >Term</a
      ><a name="3134"
      > </a
      ><a name="3135" class="Symbol"
      >&#8594;</a
      ><a name="3136"
      > </a
      ><a name="3137" href="Stlc.html#590" class="Datatype"
      >Type</a
      ><a name="3141"
      > </a
      ><a name="3142" class="Symbol"
      >&#8594;</a
      ><a name="3143"
      > </a
      ><a name="3144" class="PrimitiveType"
      >Set</a
      ><a name="3147"
      > </a
      ><a name="3148" class="Keyword"
      >where</a
      ><a name="3153"
      >
  </a
      ><a name="3156" href="Stlc.html#3156" class="InductiveConstructor"
      >Ax</a
      ><a name="3158"
      > </a
      ><a name="3159" class="Symbol"
      >:</a
      ><a name="3160"
      > </a
      ><a name="3161" class="Symbol"
      >&#8704;</a
      ><a name="3162"
      > </a
      ><a name="3163" class="Symbol"
      >{</a
      ><a name="3164" href="Stlc.html#3164" class="Bound"
      >&#915;</a
      ><a name="3165"
      > </a
      ><a name="3166" href="Stlc.html#3166" class="Bound"
      >x</a
      ><a name="3167"
      > </a
      ><a name="3168" href="Stlc.html#3168" class="Bound"
      >A</a
      ><a name="3169" class="Symbol"
      >}</a
      ><a name="3170"
      > </a
      ><a name="3171" class="Symbol"
      >&#8594;</a
      ><a name="3172"
      >
    </a
      ><a name="3177" href="Stlc.html#3164" class="Bound"
      >&#915;</a
      ><a name="3178"
      > </a
      ><a name="3179" href="Stlc.html#3166" class="Bound"
      >x</a
      ><a name="3180"
      > </a
      ><a name="3181" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="3182"
      > </a
      ><a name="3183" href="https://agda.github.io/agda-stdlib/Data.Maybe.Base.html#373" class="InductiveConstructor"
      >just</a
      ><a name="3187"
      > </a
      ><a name="3188" href="Stlc.html#3168" class="Bound"
      >A</a
      ><a name="3189"
      > </a
      ><a name="3190" class="Symbol"
      >&#8594;</a
      ><a name="3191"
      >
    </a
      ><a name="3196" href="Stlc.html#3164" class="Bound"
      >&#915;</a
      ><a name="3197"
      > </a
      ><a name="3198" href="Stlc.html#3112" class="Datatype Operator"
      >&#8866;</a
      ><a name="3199"
      > </a
      ><a name="3200" href="Stlc.html#727" class="InductiveConstructor"
      >`</a
      ><a name="3201"
      > </a
      ><a name="3202" href="Stlc.html#3166" class="Bound"
      >x</a
      ><a name="3203"
      > </a
      ><a name="3204" href="Stlc.html#3112" class="Datatype Operator"
      >&#8758;</a
      ><a name="3205"
      > </a
      ><a name="3206" href="Stlc.html#3168" class="Bound"
      >A</a
      ><a name="3207"
      >
  </a
      ><a name="3210" href="Stlc.html#3210" class="InductiveConstructor"
      >&#8658;-I</a
      ><a name="3213"
      > </a
      ><a name="3214" class="Symbol"
      >:</a
      ><a name="3215"
      > </a
      ><a name="3216" class="Symbol"
      >&#8704;</a
      ><a name="3217"
      > </a
      ><a name="3218" class="Symbol"
      >{</a
      ><a name="3219" href="Stlc.html#3219" class="Bound"
      >&#915;</a
      ><a name="3220"
      > </a
      ><a name="3221" href="Stlc.html#3221" class="Bound"
      >x</a
      ><a name="3222"
      > </a
      ><a name="3223" href="Stlc.html#3223" class="Bound"
      >N</a
      ><a name="3224"
      > </a
      ><a name="3225" href="Stlc.html#3225" class="Bound"
      >A</a
      ><a name="3226"
      > </a
      ><a name="3227" href="Stlc.html#3227" class="Bound"
      >B</a
      ><a name="3228" class="Symbol"
      >}</a
      ><a name="3229"
      > </a
      ><a name="3230" class="Symbol"
      >&#8594;</a
      ><a name="3231"
      >
    </a
      ><a name="3236" href="Stlc.html#3219" class="Bound"
      >&#915;</a
      ><a name="3237"
      > </a
      ><a name="3238" href="Maps.html#10368" class="Function Operator"
      >,</a
      ><a name="3239"
      > </a
      ><a name="3240" href="Stlc.html#3221" class="Bound"
      >x</a
      ><a name="3241"
      > </a
      ><a name="3242" href="Maps.html#10368" class="Function Operator"
      >&#8758;</a
      ><a name="3243"
      > </a
      ><a name="3244" href="Stlc.html#3225" class="Bound"
      >A</a
      ><a name="3245"
      > </a
      ><a name="3246" href="Stlc.html#3112" class="Datatype Operator"
      >&#8866;</a
      ><a name="3247"
      > </a
      ><a name="3248" href="Stlc.html#3223" class="Bound"
      >N</a
      ><a name="3249"
      > </a
      ><a name="3250" href="Stlc.html#3112" class="Datatype Operator"
      >&#8758;</a
      ><a name="3251"
      > </a
      ><a name="3252" href="Stlc.html#3227" class="Bound"
      >B</a
      ><a name="3253"
      > </a
      ><a name="3254" class="Symbol"
      >&#8594;</a
      ><a name="3255"
      >
    </a
      ><a name="3260" href="Stlc.html#3219" class="Bound"
      >&#915;</a
      ><a name="3261"
      > </a
      ><a name="3262" href="Stlc.html#3112" class="Datatype Operator"
      >&#8866;</a
      ><a name="3263"
      > </a
      ><a name="3264" href="Stlc.html#743" class="InductiveConstructor Operator"
      >&#955;[</a
      ><a name="3266"
      > </a
      ><a name="3267" href="Stlc.html#3221" class="Bound"
      >x</a
      ><a name="3268"
      > </a
      ><a name="3269" href="Stlc.html#743" class="InductiveConstructor Operator"
      >&#8758;</a
      ><a name="3270"
      > </a
      ><a name="3271" href="Stlc.html#3225" class="Bound"
      >A</a
      ><a name="3272"
      > </a
      ><a name="3273" href="Stlc.html#743" class="InductiveConstructor Operator"
      >]</a
      ><a name="3274"
      > </a
      ><a name="3275" href="Stlc.html#3223" class="Bound"
      >N</a
      ><a name="3276"
      > </a
      ><a name="3277" href="Stlc.html#3112" class="Datatype Operator"
      >&#8758;</a
      ><a name="3278"
      > </a
      ><a name="3279" href="Stlc.html#3225" class="Bound"
      >A</a
      ><a name="3280"
      > </a
      ><a name="3281" href="Stlc.html#620" class="InductiveConstructor Operator"
      >&#8658;</a
      ><a name="3282"
      > </a
      ><a name="3283" href="Stlc.html#3227" class="Bound"
      >B</a
      ><a name="3284"
      >
  </a
      ><a name="3287" href="Stlc.html#3287" class="InductiveConstructor"
      >&#8658;-E</a
      ><a name="3290"
      > </a
      ><a name="3291" class="Symbol"
      >:</a
      ><a name="3292"
      > </a
      ><a name="3293" class="Symbol"
      >&#8704;</a
      ><a name="3294"
      > </a
      ><a name="3295" class="Symbol"
      >{</a
      ><a name="3296" href="Stlc.html#3296" class="Bound"
      >&#915;</a
      ><a name="3297"
      > </a
      ><a name="3298" href="Stlc.html#3298" class="Bound"
      >L</a
      ><a name="3299"
      > </a
      ><a name="3300" href="Stlc.html#3300" class="Bound"
      >M</a
      ><a name="3301"
      > </a
      ><a name="3302" href="Stlc.html#3302" class="Bound"
      >A</a
      ><a name="3303"
      > </a
      ><a name="3304" href="Stlc.html#3304" class="Bound"
      >B</a
      ><a name="3305" class="Symbol"
      >}</a
      ><a name="3306"
      > </a
      ><a name="3307" class="Symbol"
      >&#8594;</a
      ><a name="3308"
      >
    </a
      ><a name="3313" href="Stlc.html#3296" class="Bound"
      >&#915;</a
      ><a name="3314"
      > </a
      ><a name="3315" href="Stlc.html#3112" class="Datatype Operator"
      >&#8866;</a
      ><a name="3316"
      > </a
      ><a name="3317" href="Stlc.html#3298" class="Bound"
      >L</a
      ><a name="3318"
      > </a
      ><a name="3319" href="Stlc.html#3112" class="Datatype Operator"
      >&#8758;</a
      ><a name="3320"
      > </a
      ><a name="3321" href="Stlc.html#3302" class="Bound"
      >A</a
      ><a name="3322"
      > </a
      ><a name="3323" href="Stlc.html#620" class="InductiveConstructor Operator"
      >&#8658;</a
      ><a name="3324"
      > </a
      ><a name="3325" href="Stlc.html#3304" class="Bound"
      >B</a
      ><a name="3326"
      > </a
      ><a name="3327" class="Symbol"
      >&#8594;</a
      ><a name="3328"
      >
    </a
      ><a name="3333" href="Stlc.html#3296" class="Bound"
      >&#915;</a
      ><a name="3334"
      > </a
      ><a name="3335" href="Stlc.html#3112" class="Datatype Operator"
      >&#8866;</a
      ><a name="3336"
      > </a
      ><a name="3337" href="Stlc.html#3300" class="Bound"
      >M</a
      ><a name="3338"
      > </a
      ><a name="3339" href="Stlc.html#3112" class="Datatype Operator"
      >&#8758;</a
      ><a name="3340"
      > </a
      ><a name="3341" href="Stlc.html#3302" class="Bound"
      >A</a
      ><a name="3342"
      > </a
      ><a name="3343" class="Symbol"
      >&#8594;</a
      ><a name="3344"
      >
    </a
      ><a name="3349" href="Stlc.html#3296" class="Bound"
      >&#915;</a
      ><a name="3350"
      > </a
      ><a name="3351" href="Stlc.html#3112" class="Datatype Operator"
      >&#8866;</a
      ><a name="3352"
      > </a
      ><a name="3353" href="Stlc.html#3298" class="Bound"
      >L</a
      ><a name="3354"
      > </a
      ><a name="3355" href="Stlc.html#779" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="3356"
      > </a
      ><a name="3357" href="Stlc.html#3300" class="Bound"
      >M</a
      ><a name="3358"
      > </a
      ><a name="3359" href="Stlc.html#3112" class="Datatype Operator"
      >&#8758;</a
      ><a name="3360"
      > </a
      ><a name="3361" href="Stlc.html#3304" class="Bound"
      >B</a
      ><a name="3362"
      >
  </a
      ><a name="3365" href="Stlc.html#3365" class="InductiveConstructor"
      >&#120121;-I&#8321;</a
      ><a name="3369"
      > </a
      ><a name="3370" class="Symbol"
      >:</a
      ><a name="3371"
      > </a
      ><a name="3372" class="Symbol"
      >&#8704;</a
      ><a name="3373"
      > </a
      ><a name="3374" class="Symbol"
      >{</a
      ><a name="3375" href="Stlc.html#3375" class="Bound"
      >&#915;</a
      ><a name="3376" class="Symbol"
      >}</a
      ><a name="3377"
      > </a
      ><a name="3378" class="Symbol"
      >&#8594;</a
      ><a name="3379"
      >
    </a
      ><a name="3384" href="Stlc.html#3375" class="Bound"
      >&#915;</a
      ><a name="3385"
      > </a
      ><a name="3386" href="Stlc.html#3112" class="Datatype Operator"
      >&#8866;</a
      ><a name="3387"
      > </a
      ><a name="3388" href="Stlc.html#806" class="InductiveConstructor"
      >true</a
      ><a name="3392"
      > </a
      ><a name="3393" href="Stlc.html#3112" class="Datatype Operator"
      >&#8758;</a
      ><a name="3394"
      > </a
      ><a name="3395" href="Stlc.html#609" class="InductiveConstructor"
      >&#120121;</a
      ><a name="3396"
      >
  </a
      ><a name="3399" href="Stlc.html#3399" class="InductiveConstructor"
      >&#120121;-I&#8322;</a
      ><a name="3403"
      > </a
      ><a name="3404" class="Symbol"
      >:</a
      ><a name="3405"
      > </a
      ><a name="3406" class="Symbol"
      >&#8704;</a
      ><a name="3407"
      > </a
      ><a name="3408" class="Symbol"
      >{</a
      ><a name="3409" href="Stlc.html#3409" class="Bound"
      >&#915;</a
      ><a name="3410" class="Symbol"
      >}</a
      ><a name="3411"
      > </a
      ><a name="3412" class="Symbol"
      >&#8594;</a
      ><a name="3413"
      >
    </a
      ><a name="3418" href="Stlc.html#3409" class="Bound"
      >&#915;</a
      ><a name="3419"
      > </a
      ><a name="3420" href="Stlc.html#3112" class="Datatype Operator"
      >&#8866;</a
      ><a name="3421"
      > </a
      ><a name="3422" href="Stlc.html#820" class="InductiveConstructor"
      >false</a
      ><a name="3427"
      > </a
      ><a name="3428" href="Stlc.html#3112" class="Datatype Operator"
      >&#8758;</a
      ><a name="3429"
      > </a
      ><a name="3430" href="Stlc.html#609" class="InductiveConstructor"
      >&#120121;</a
      ><a name="3431"
      >
  </a
      ><a name="3434" href="Stlc.html#3434" class="InductiveConstructor"
      >&#120121;-E</a
      ><a name="3437"
      > </a
      ><a name="3438" class="Symbol"
      >:</a
      ><a name="3439"
      > </a
      ><a name="3440" class="Symbol"
      >&#8704;</a
      ><a name="3441"
      > </a
      ><a name="3442" class="Symbol"
      >{</a
      ><a name="3443" href="Stlc.html#3443" class="Bound"
      >&#915;</a
      ><a name="3444"
      > </a
      ><a name="3445" href="Stlc.html#3445" class="Bound"
      >L</a
      ><a name="3446"
      > </a
      ><a name="3447" href="Stlc.html#3447" class="Bound"
      >M</a
      ><a name="3448"
      > </a
      ><a name="3449" href="Stlc.html#3449" class="Bound"
      >N</a
      ><a name="3450"
      > </a
      ><a name="3451" href="Stlc.html#3451" class="Bound"
      >A</a
      ><a name="3452" class="Symbol"
      >}</a
      ><a name="3453"
      > </a
      ><a name="3454" class="Symbol"
      >&#8594;</a
      ><a name="3455"
      >
    </a
      ><a name="3460" href="Stlc.html#3443" class="Bound"
      >&#915;</a
      ><a name="3461"
      > </a
      ><a name="3462" href="Stlc.html#3112" class="Datatype Operator"
      >&#8866;</a
      ><a name="3463"
      > </a
      ><a name="3464" href="Stlc.html#3445" class="Bound"
      >L</a
      ><a name="3465"
      > </a
      ><a name="3466" href="Stlc.html#3112" class="Datatype Operator"
      >&#8758;</a
      ><a name="3467"
      > </a
      ><a name="3468" href="Stlc.html#609" class="InductiveConstructor"
      >&#120121;</a
      ><a name="3469"
      > </a
      ><a name="3470" class="Symbol"
      >&#8594;</a
      ><a name="3471"
      >
    </a
      ><a name="3476" href="Stlc.html#3443" class="Bound"
      >&#915;</a
      ><a name="3477"
      > </a
      ><a name="3478" href="Stlc.html#3112" class="Datatype Operator"
      >&#8866;</a
      ><a name="3479"
      > </a
      ><a name="3480" href="Stlc.html#3447" class="Bound"
      >M</a
      ><a name="3481"
      > </a
      ><a name="3482" href="Stlc.html#3112" class="Datatype Operator"
      >&#8758;</a
      ><a name="3483"
      > </a
      ><a name="3484" href="Stlc.html#3451" class="Bound"
      >A</a
      ><a name="3485"
      > </a
      ><a name="3486" class="Symbol"
      >&#8594;</a
      ><a name="3487"
      >
    </a
      ><a name="3492" href="Stlc.html#3443" class="Bound"
      >&#915;</a
      ><a name="3493"
      > </a
      ><a name="3494" href="Stlc.html#3112" class="Datatype Operator"
      >&#8866;</a
      ><a name="3495"
      > </a
      ><a name="3496" href="Stlc.html#3449" class="Bound"
      >N</a
      ><a name="3497"
      > </a
      ><a name="3498" href="Stlc.html#3112" class="Datatype Operator"
      >&#8758;</a
      ><a name="3499"
      > </a
      ><a name="3500" href="Stlc.html#3451" class="Bound"
      >A</a
      ><a name="3501"
      > </a
      ><a name="3502" class="Symbol"
      >&#8594;</a
      ><a name="3503"
      >
    </a
      ><a name="3508" href="Stlc.html#3443" class="Bound"
      >&#915;</a
      ><a name="3509"
      > </a
      ><a name="3510" href="Stlc.html#3112" class="Datatype Operator"
      >&#8866;</a
      ><a name="3511"
      > </a
      ><a name="3512" href="Stlc.html#835" class="InductiveConstructor Operator"
      >if</a
      ><a name="3514"
      > </a
      ><a name="3515" href="Stlc.html#3445" class="Bound"
      >L</a
      ><a name="3516"
      > </a
      ><a name="3517" href="Stlc.html#835" class="InductiveConstructor Operator"
      >then</a
      ><a name="3521"
      > </a
      ><a name="3522" href="Stlc.html#3447" class="Bound"
      >M</a
      ><a name="3523"
      > </a
      ><a name="3524" href="Stlc.html#835" class="InductiveConstructor Operator"
      >else</a
      ><a name="3528"
      > </a
      ><a name="3529" href="Stlc.html#3449" class="Bound"
      >N</a
      ><a name="3530"
      > </a
      ><a name="3531" href="Stlc.html#3112" class="Datatype Operator"
      >&#8758;</a
      ><a name="3532"
      > </a
      ><a name="3533" href="Stlc.html#3451" class="Bound"
      >A</a
      >

</pre>

## Example type derivations

<pre class="Agda">

<a name="3593" href="Stlc.html#3593" class="Function"
      >typing&#8321;</a
      ><a name="3600"
      > </a
      ><a name="3601" class="Symbol"
      >:</a
      ><a name="3602"
      > </a
      ><a name="3603" href="Maps.html#10265" class="Function"
      >&#8709;</a
      ><a name="3604"
      > </a
      ><a name="3605" href="Stlc.html#3112" class="Datatype Operator"
      >&#8866;</a
      ><a name="3606"
      > </a
      ><a name="3607" href="Stlc.html#949" class="Function"
      >not</a
      ><a name="3610"
      > </a
      ><a name="3611" href="Stlc.html#3112" class="Datatype Operator"
      >&#8758;</a
      ><a name="3612"
      > </a
      ><a name="3613" href="Stlc.html#609" class="InductiveConstructor"
      >&#120121;</a
      ><a name="3614"
      > </a
      ><a name="3615" href="Stlc.html#620" class="InductiveConstructor Operator"
      >&#8658;</a
      ><a name="3616"
      > </a
      ><a name="3617" href="Stlc.html#609" class="InductiveConstructor"
      >&#120121;</a
      ><a name="3618"
      >
</a
      ><a name="3619" href="Stlc.html#3593" class="Function"
      >typing&#8321;</a
      ><a name="3626"
      > </a
      ><a name="3627" class="Symbol"
      >=</a
      ><a name="3628"
      > </a
      ><a name="3629" href="Stlc.html#3210" class="InductiveConstructor"
      >&#8658;-I</a
      ><a name="3632"
      > </a
      ><a name="3633" class="Symbol"
      >(</a
      ><a name="3634" href="Stlc.html#3434" class="InductiveConstructor"
      >&#120121;-E</a
      ><a name="3637"
      > </a
      ><a name="3638" class="Symbol"
      >(</a
      ><a name="3639" href="Stlc.html#3156" class="InductiveConstructor"
      >Ax</a
      ><a name="3641"
      > </a
      ><a name="3642" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="3646" class="Symbol"
      >)</a
      ><a name="3647"
      > </a
      ><a name="3648" href="Stlc.html#3399" class="InductiveConstructor"
      >&#120121;-I&#8322;</a
      ><a name="3652"
      > </a
      ><a name="3653" href="Stlc.html#3365" class="InductiveConstructor"
      >&#120121;-I&#8321;</a
      ><a name="3657" class="Symbol"
      >)</a
      ><a name="3658"
      >

</a
      ><a name="3660" href="Stlc.html#3660" class="Function"
      >typing&#8322;</a
      ><a name="3667"
      > </a
      ><a name="3668" class="Symbol"
      >:</a
      ><a name="3669"
      > </a
      ><a name="3670" href="Maps.html#10265" class="Function"
      >&#8709;</a
      ><a name="3671"
      > </a
      ><a name="3672" href="Stlc.html#3112" class="Datatype Operator"
      >&#8866;</a
      ><a name="3673"
      > </a
      ><a name="3674" href="Stlc.html#953" class="Function"
      >two</a
      ><a name="3677"
      > </a
      ><a name="3678" href="Stlc.html#3112" class="Datatype Operator"
      >&#8758;</a
      ><a name="3679"
      > </a
      ><a name="3680" class="Symbol"
      >(</a
      ><a name="3681" href="Stlc.html#609" class="InductiveConstructor"
      >&#120121;</a
      ><a name="3682"
      > </a
      ><a name="3683" href="Stlc.html#620" class="InductiveConstructor Operator"
      >&#8658;</a
      ><a name="3684"
      > </a
      ><a name="3685" href="Stlc.html#609" class="InductiveConstructor"
      >&#120121;</a
      ><a name="3686" class="Symbol"
      >)</a
      ><a name="3687"
      > </a
      ><a name="3688" href="Stlc.html#620" class="InductiveConstructor Operator"
      >&#8658;</a
      ><a name="3689"
      > </a
      ><a name="3690" href="Stlc.html#609" class="InductiveConstructor"
      >&#120121;</a
      ><a name="3691"
      > </a
      ><a name="3692" href="Stlc.html#620" class="InductiveConstructor Operator"
      >&#8658;</a
      ><a name="3693"
      > </a
      ><a name="3694" href="Stlc.html#609" class="InductiveConstructor"
      >&#120121;</a
      ><a name="3695"
      >
</a
      ><a name="3696" href="Stlc.html#3660" class="Function"
      >typing&#8322;</a
      ><a name="3703"
      > </a
      ><a name="3704" class="Symbol"
      >=</a
      ><a name="3705"
      > </a
      ><a name="3706" href="Stlc.html#3210" class="InductiveConstructor"
      >&#8658;-I</a
      ><a name="3709"
      > </a
      ><a name="3710" class="Symbol"
      >(</a
      ><a name="3711" href="Stlc.html#3210" class="InductiveConstructor"
      >&#8658;-I</a
      ><a name="3714"
      > </a
      ><a name="3715" class="Symbol"
      >(</a
      ><a name="3716" href="Stlc.html#3287" class="InductiveConstructor"
      >&#8658;-E</a
      ><a name="3719"
      > </a
      ><a name="3720" class="Symbol"
      >(</a
      ><a name="3721" href="Stlc.html#3156" class="InductiveConstructor"
      >Ax</a
      ><a name="3723"
      > </a
      ><a name="3724" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="3728" class="Symbol"
      >)</a
      ><a name="3729"
      > </a
      ><a name="3730" class="Symbol"
      >(</a
      ><a name="3731" href="Stlc.html#3287" class="InductiveConstructor"
      >&#8658;-E</a
      ><a name="3734"
      > </a
      ><a name="3735" class="Symbol"
      >(</a
      ><a name="3736" href="Stlc.html#3156" class="InductiveConstructor"
      >Ax</a
      ><a name="3738"
      > </a
      ><a name="3739" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="3743" class="Symbol"
      >)</a
      ><a name="3744"
      > </a
      ><a name="3745" class="Symbol"
      >(</a
      ><a name="3746" href="Stlc.html#3156" class="InductiveConstructor"
      >Ax</a
      ><a name="3748"
      > </a
      ><a name="3749" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="3753" class="Symbol"
      >))))</a
      >

</pre>

Construction of a type derivation is best done interactively.
We start with the declaration:

    typing₁ : ∅ ⊢ not ∶ 𝔹 ⇒ 𝔹
    typing₁ = ?

Typing C-l causes Agda to create a hole and tell us its expected type.

    typing₁ = { }0
    ?0 : ∅ ⊢ not ∶ 𝔹 ⇒ 𝔹

Now we fill in the hole by typing C-c C-r. Agda observes that
the outermost term in `not` in a `λ`, which is typed using `⇒-I`. The
`⇒-I` rule in turn takes one argument, which Agda leaves as a hole.

    typing₁ = ⇒-I { }0
    ?0 : ∅ , x ∶ 𝔹 ⊢ if ` x then false else true ∶ 𝔹

Again we fill in the hole by typing C-c C-r. Agda observes that the
outermost term is now `if_then_else_`, which is typed using `𝔹-E`. The
`𝔹-E` rule in turn takes three arguments, which Agda leaves as holes.

    typing₁ = ⇒-I (𝔹-E { }0 { }1 { }2)
    ?0 : ∅ , x ∶ 𝔹 ⊢ ` x ∶
    ?1 : ∅ , x ∶ 𝔹 ⊢ false ∶ 𝔹
    ?2 : ∅ , x ∶ 𝔹 ⊢ true ∶ 𝔹

Again we fill in the three holes by typing C-c C-r in each. Agda observes
that `\` x`, `false`, and `true` are typed using `Ax`, `𝔹-I₂`, and
`𝔹-I₁` respectively. The `Ax` rule in turn takes an argument, to show
that `(∅ , x ∶ 𝔹) x = just 𝔹`, which can in turn be specified with a
hole. After filling in all holes, the term is as above.

The entire process can be automated using Agsy, invoked with C-c C-a.


