---
title     : "Stlc: The Simply Typed Lambda-Calculus"
layout    : page
permalink : /Stlc
---

This chapter defines the simply-typed lambda calculus.

## Imports

<pre class="Agda">{% raw %}
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
{% endraw %}</pre>


## Syntax

Syntax of types and terms.

<pre class="Agda">{% raw %}
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
      ><a name="656" href="Stlc.html#781" class="InductiveConstructor Operator"
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
      ><a name="670" href="Stlc.html#745" class="InductiveConstructor Operator"
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
      ><a name="688" href="Stlc.html#837" class="InductiveConstructor Operator"
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
      >var</a
      ><a name="730"
      > </a
      ><a name="731" class="Symbol"
      >:</a
      ><a name="732"
      > </a
      ><a name="733" href="Maps.html#2171" class="Datatype"
      >Id</a
      ><a name="735"
      > </a
      ><a name="736" class="Symbol"
      >&#8594;</a
      ><a name="737"
      > </a
      ><a name="738" href="Stlc.html#708" class="Datatype"
      >Term</a
      ><a name="742"
      >
  </a
      ><a name="745" href="Stlc.html#745" class="InductiveConstructor Operator"
      >&#955;[_&#8758;_]_</a
      ><a name="752"
      > </a
      ><a name="753" class="Symbol"
      >:</a
      ><a name="754"
      > </a
      ><a name="755" href="Maps.html#2171" class="Datatype"
      >Id</a
      ><a name="757"
      > </a
      ><a name="758" class="Symbol"
      >&#8594;</a
      ><a name="759"
      > </a
      ><a name="760" href="Stlc.html#590" class="Datatype"
      >Type</a
      ><a name="764"
      > </a
      ><a name="765" class="Symbol"
      >&#8594;</a
      ><a name="766"
      > </a
      ><a name="767" href="Stlc.html#708" class="Datatype"
      >Term</a
      ><a name="771"
      > </a
      ><a name="772" class="Symbol"
      >&#8594;</a
      ><a name="773"
      > </a
      ><a name="774" href="Stlc.html#708" class="Datatype"
      >Term</a
      ><a name="778"
      >
  </a
      ><a name="781" href="Stlc.html#781" class="InductiveConstructor Operator"
      >_&#183;_</a
      ><a name="784"
      > </a
      ><a name="785" class="Symbol"
      >:</a
      ><a name="786"
      > </a
      ><a name="787" href="Stlc.html#708" class="Datatype"
      >Term</a
      ><a name="791"
      > </a
      ><a name="792" class="Symbol"
      >&#8594;</a
      ><a name="793"
      > </a
      ><a name="794" href="Stlc.html#708" class="Datatype"
      >Term</a
      ><a name="798"
      > </a
      ><a name="799" class="Symbol"
      >&#8594;</a
      ><a name="800"
      > </a
      ><a name="801" href="Stlc.html#708" class="Datatype"
      >Term</a
      ><a name="805"
      >
  </a
      ><a name="808" href="Stlc.html#808" class="InductiveConstructor"
      >true</a
      ><a name="812"
      > </a
      ><a name="813" class="Symbol"
      >:</a
      ><a name="814"
      > </a
      ><a name="815" href="Stlc.html#708" class="Datatype"
      >Term</a
      ><a name="819"
      >
  </a
      ><a name="822" href="Stlc.html#822" class="InductiveConstructor"
      >false</a
      ><a name="827"
      > </a
      ><a name="828" class="Symbol"
      >:</a
      ><a name="829"
      > </a
      ><a name="830" href="Stlc.html#708" class="Datatype"
      >Term</a
      ><a name="834"
      >
  </a
      ><a name="837" href="Stlc.html#837" class="InductiveConstructor Operator"
      >if_then_else_</a
      ><a name="850"
      > </a
      ><a name="851" class="Symbol"
      >:</a
      ><a name="852"
      > </a
      ><a name="853" href="Stlc.html#708" class="Datatype"
      >Term</a
      ><a name="857"
      > </a
      ><a name="858" class="Symbol"
      >&#8594;</a
      ><a name="859"
      > </a
      ><a name="860" href="Stlc.html#708" class="Datatype"
      >Term</a
      ><a name="864"
      > </a
      ><a name="865" class="Symbol"
      >&#8594;</a
      ><a name="866"
      > </a
      ><a name="867" href="Stlc.html#708" class="Datatype"
      >Term</a
      ><a name="871"
      > </a
      ><a name="872" class="Symbol"
      >&#8594;</a
      ><a name="873"
      > </a
      ><a name="874" href="Stlc.html#708" class="Datatype"
      >Term</a
      >
{% endraw %}</pre>

Example terms.
<pre class="Agda">{% raw %}
<a name="919" href="Stlc.html#919" class="Function"
      >f</a
      ><a name="920"
      > </a
      ><a name="921" href="Stlc.html#921" class="Function"
      >x</a
      ><a name="922"
      > </a
      ><a name="923" class="Symbol"
      >:</a
      ><a name="924"
      > </a
      ><a name="925" href="Maps.html#2171" class="Datatype"
      >Id</a
      ><a name="927"
      >
</a
      ><a name="928" href="Stlc.html#919" class="Function"
      >f</a
      ><a name="929"
      >  </a
      ><a name="931" class="Symbol"
      >=</a
      ><a name="932"
      >  </a
      ><a name="934" href="Maps.html#2188" class="InductiveConstructor"
      >id</a
      ><a name="936"
      > </a
      ><a name="937" class="Number"
      >0</a
      ><a name="938"
      >
</a
      ><a name="939" href="Stlc.html#921" class="Function"
      >x</a
      ><a name="940"
      >  </a
      ><a name="942" class="Symbol"
      >=</a
      ><a name="943"
      >  </a
      ><a name="945" href="Maps.html#2188" class="InductiveConstructor"
      >id</a
      ><a name="947"
      > </a
      ><a name="948" class="Number"
      >1</a
      ><a name="949"
      >

</a
      ><a name="951" href="Stlc.html#951" class="Function"
      >not</a
      ><a name="954"
      > </a
      ><a name="955" href="Stlc.html#955" class="Function"
      >two</a
      ><a name="958"
      > </a
      ><a name="959" class="Symbol"
      >:</a
      ><a name="960"
      > </a
      ><a name="961" href="Stlc.html#708" class="Datatype"
      >Term</a
      ><a name="965"
      > 
</a
      ><a name="967" href="Stlc.html#951" class="Function"
      >not</a
      ><a name="970"
      > </a
      ><a name="971" class="Symbol"
      >=</a
      ><a name="972"
      >  </a
      ><a name="974" href="Stlc.html#745" class="InductiveConstructor Operator"
      >&#955;[</a
      ><a name="976"
      > </a
      ><a name="977" href="Stlc.html#921" class="Function"
      >x</a
      ><a name="978"
      > </a
      ><a name="979" href="Stlc.html#745" class="InductiveConstructor Operator"
      >&#8758;</a
      ><a name="980"
      > </a
      ><a name="981" href="Stlc.html#609" class="InductiveConstructor"
      >&#120121;</a
      ><a name="982"
      > </a
      ><a name="983" href="Stlc.html#745" class="InductiveConstructor Operator"
      >]</a
      ><a name="984"
      > </a
      ><a name="985" class="Symbol"
      >(</a
      ><a name="986" href="Stlc.html#837" class="InductiveConstructor Operator"
      >if</a
      ><a name="988"
      > </a
      ><a name="989" href="Stlc.html#727" class="InductiveConstructor"
      >var</a
      ><a name="992"
      > </a
      ><a name="993" href="Stlc.html#921" class="Function"
      >x</a
      ><a name="994"
      > </a
      ><a name="995" href="Stlc.html#837" class="InductiveConstructor Operator"
      >then</a
      ><a name="999"
      > </a
      ><a name="1000" href="Stlc.html#822" class="InductiveConstructor"
      >false</a
      ><a name="1005"
      > </a
      ><a name="1006" href="Stlc.html#837" class="InductiveConstructor Operator"
      >else</a
      ><a name="1010"
      > </a
      ><a name="1011" href="Stlc.html#808" class="InductiveConstructor"
      >true</a
      ><a name="1015" class="Symbol"
      >)</a
      ><a name="1016"
      >
</a
      ><a name="1017" href="Stlc.html#955" class="Function"
      >two</a
      ><a name="1020"
      > </a
      ><a name="1021" class="Symbol"
      >=</a
      ><a name="1022"
      >  </a
      ><a name="1024" href="Stlc.html#745" class="InductiveConstructor Operator"
      >&#955;[</a
      ><a name="1026"
      > </a
      ><a name="1027" href="Stlc.html#919" class="Function"
      >f</a
      ><a name="1028"
      > </a
      ><a name="1029" href="Stlc.html#745" class="InductiveConstructor Operator"
      >&#8758;</a
      ><a name="1030"
      > </a
      ><a name="1031" href="Stlc.html#609" class="InductiveConstructor"
      >&#120121;</a
      ><a name="1032"
      > </a
      ><a name="1033" href="Stlc.html#620" class="InductiveConstructor Operator"
      >&#8658;</a
      ><a name="1034"
      > </a
      ><a name="1035" href="Stlc.html#609" class="InductiveConstructor"
      >&#120121;</a
      ><a name="1036"
      > </a
      ><a name="1037" href="Stlc.html#745" class="InductiveConstructor Operator"
      >]</a
      ><a name="1038"
      > </a
      ><a name="1039" href="Stlc.html#745" class="InductiveConstructor Operator"
      >&#955;[</a
      ><a name="1041"
      > </a
      ><a name="1042" href="Stlc.html#921" class="Function"
      >x</a
      ><a name="1043"
      > </a
      ><a name="1044" href="Stlc.html#745" class="InductiveConstructor Operator"
      >&#8758;</a
      ><a name="1045"
      > </a
      ><a name="1046" href="Stlc.html#609" class="InductiveConstructor"
      >&#120121;</a
      ><a name="1047"
      > </a
      ><a name="1048" href="Stlc.html#745" class="InductiveConstructor Operator"
      >]</a
      ><a name="1049"
      > </a
      ><a name="1050" href="Stlc.html#727" class="InductiveConstructor"
      >var</a
      ><a name="1053"
      > </a
      ><a name="1054" href="Stlc.html#919" class="Function"
      >f</a
      ><a name="1055"
      > </a
      ><a name="1056" href="Stlc.html#781" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="1057"
      > </a
      ><a name="1058" class="Symbol"
      >(</a
      ><a name="1059" href="Stlc.html#727" class="InductiveConstructor"
      >var</a
      ><a name="1062"
      > </a
      ><a name="1063" href="Stlc.html#919" class="Function"
      >f</a
      ><a name="1064"
      > </a
      ><a name="1065" href="Stlc.html#781" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="1066"
      > </a
      ><a name="1067" href="Stlc.html#727" class="InductiveConstructor"
      >var</a
      ><a name="1070"
      > </a
      ><a name="1071" href="Stlc.html#921" class="Function"
      >x</a
      ><a name="1072" class="Symbol"
      >)</a
      >
{% endraw %}</pre>

## Values

<pre class="Agda">{% raw %}
<a name="1110" class="Keyword"
      >data</a
      ><a name="1114"
      > </a
      ><a name="1115" href="Stlc.html#1115" class="Datatype"
      >Value</a
      ><a name="1120"
      > </a
      ><a name="1121" class="Symbol"
      >:</a
      ><a name="1122"
      > </a
      ><a name="1123" href="Stlc.html#708" class="Datatype"
      >Term</a
      ><a name="1127"
      > </a
      ><a name="1128" class="Symbol"
      >&#8594;</a
      ><a name="1129"
      > </a
      ><a name="1130" class="PrimitiveType"
      >Set</a
      ><a name="1133"
      > </a
      ><a name="1134" class="Keyword"
      >where</a
      ><a name="1139"
      >
  </a
      ><a name="1142" href="Stlc.html#1142" class="InductiveConstructor"
      >value-&#955;</a
      ><a name="1149"
      >     </a
      ><a name="1154" class="Symbol"
      >:</a
      ><a name="1155"
      > </a
      ><a name="1156" class="Symbol"
      >&#8704;</a
      ><a name="1157"
      > </a
      ><a name="1158" class="Symbol"
      >{</a
      ><a name="1159" href="Stlc.html#1159" class="Bound"
      >x</a
      ><a name="1160"
      > </a
      ><a name="1161" href="Stlc.html#1161" class="Bound"
      >A</a
      ><a name="1162"
      > </a
      ><a name="1163" href="Stlc.html#1163" class="Bound"
      >N</a
      ><a name="1164" class="Symbol"
      >}</a
      ><a name="1165"
      > </a
      ><a name="1166" class="Symbol"
      >&#8594;</a
      ><a name="1167"
      > </a
      ><a name="1168" href="Stlc.html#1115" class="Datatype"
      >Value</a
      ><a name="1173"
      > </a
      ><a name="1174" class="Symbol"
      >(</a
      ><a name="1175" href="Stlc.html#745" class="InductiveConstructor Operator"
      >&#955;[</a
      ><a name="1177"
      > </a
      ><a name="1178" href="Stlc.html#1159" class="Bound"
      >x</a
      ><a name="1179"
      > </a
      ><a name="1180" href="Stlc.html#745" class="InductiveConstructor Operator"
      >&#8758;</a
      ><a name="1181"
      > </a
      ><a name="1182" href="Stlc.html#1161" class="Bound"
      >A</a
      ><a name="1183"
      > </a
      ><a name="1184" href="Stlc.html#745" class="InductiveConstructor Operator"
      >]</a
      ><a name="1185"
      > </a
      ><a name="1186" href="Stlc.html#1163" class="Bound"
      >N</a
      ><a name="1187" class="Symbol"
      >)</a
      ><a name="1188"
      >
  </a
      ><a name="1191" href="Stlc.html#1191" class="InductiveConstructor"
      >value-true</a
      ><a name="1201"
      >  </a
      ><a name="1203" class="Symbol"
      >:</a
      ><a name="1204"
      > </a
      ><a name="1205" href="Stlc.html#1115" class="Datatype"
      >Value</a
      ><a name="1210"
      > </a
      ><a name="1211" href="Stlc.html#808" class="InductiveConstructor"
      >true</a
      ><a name="1215"
      >
  </a
      ><a name="1218" href="Stlc.html#1218" class="InductiveConstructor"
      >value-false</a
      ><a name="1229"
      > </a
      ><a name="1230" class="Symbol"
      >:</a
      ><a name="1231"
      > </a
      ><a name="1232" href="Stlc.html#1115" class="Datatype"
      >Value</a
      ><a name="1237"
      > </a
      ><a name="1238" href="Stlc.html#822" class="InductiveConstructor"
      >false</a
      >
{% endraw %}</pre>

## Substitution

<pre class="Agda">{% raw %}
<a name="1286" href="Stlc.html#1286" class="Function Operator"
      >_[_&#8758;=_]</a
      ><a name="1293"
      > </a
      ><a name="1294" class="Symbol"
      >:</a
      ><a name="1295"
      > </a
      ><a name="1296" href="Stlc.html#708" class="Datatype"
      >Term</a
      ><a name="1300"
      > </a
      ><a name="1301" class="Symbol"
      >&#8594;</a
      ><a name="1302"
      > </a
      ><a name="1303" href="Maps.html#2171" class="Datatype"
      >Id</a
      ><a name="1305"
      > </a
      ><a name="1306" class="Symbol"
      >&#8594;</a
      ><a name="1307"
      > </a
      ><a name="1308" href="Stlc.html#708" class="Datatype"
      >Term</a
      ><a name="1312"
      > </a
      ><a name="1313" class="Symbol"
      >&#8594;</a
      ><a name="1314"
      > </a
      ><a name="1315" href="Stlc.html#708" class="Datatype"
      >Term</a
      ><a name="1319"
      >
</a
      ><a name="1320" class="Symbol"
      >(</a
      ><a name="1321" href="Stlc.html#727" class="InductiveConstructor"
      >var</a
      ><a name="1324"
      > </a
      ><a name="1325" href="Stlc.html#1325" class="Bound"
      >x&#8242;</a
      ><a name="1327" class="Symbol"
      >)</a
      ><a name="1328"
      > </a
      ><a name="1329" href="Stlc.html#1286" class="Function Operator"
      >[</a
      ><a name="1330"
      > </a
      ><a name="1331" href="Stlc.html#1331" class="Bound"
      >x</a
      ><a name="1332"
      > </a
      ><a name="1333" href="Stlc.html#1286" class="Function Operator"
      >&#8758;=</a
      ><a name="1335"
      > </a
      ><a name="1336" href="Stlc.html#1336" class="Bound"
      >V</a
      ><a name="1337"
      > </a
      ><a name="1338" href="Stlc.html#1286" class="Function Operator"
      >]</a
      ><a name="1339"
      > </a
      ><a name="1340" class="Keyword"
      >with</a
      ><a name="1344"
      > </a
      ><a name="1345" href="Stlc.html#1331" class="Bound"
      >x</a
      ><a name="1346"
      > </a
      ><a name="1347" href="Maps.html#2509" class="Function Operator"
      >&#8799;</a
      ><a name="1348"
      > </a
      ><a name="1349" href="Stlc.html#1325" class="Bound"
      >x&#8242;</a
      ><a name="1351"
      >
</a
      ><a name="1352" class="Symbol"
      >...</a
      ><a name="1355"
      > </a
      ><a name="1356" class="Symbol"
      >|</a
      ><a name="1357"
      > </a
      ><a name="1358" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#520" class="InductiveConstructor"
      >yes</a
      ><a name="1361"
      > </a
      ><a name="1362" class="Symbol"
      >_</a
      ><a name="1363"
      > </a
      ><a name="1364" class="Symbol"
      >=</a
      ><a name="1365"
      > </a
      ><a name="1366" href="Stlc.html#1336" class="Bound"
      >V</a
      ><a name="1367"
      >
</a
      ><a name="1368" class="Symbol"
      >...</a
      ><a name="1371"
      > </a
      ><a name="1372" class="Symbol"
      >|</a
      ><a name="1373"
      > </a
      ><a name="1374" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#547" class="InductiveConstructor"
      >no</a
      ><a name="1376"
      >  </a
      ><a name="1378" class="Symbol"
      >_</a
      ><a name="1379"
      > </a
      ><a name="1380" class="Symbol"
      >=</a
      ><a name="1381"
      > </a
      ><a name="1382" href="Stlc.html#727" class="InductiveConstructor"
      >var</a
      ><a name="1385"
      > </a
      ><a name="1386" href="Stlc.html#1325" class="Bound"
      >x&#8242;</a
      ><a name="1388"
      >
</a
      ><a name="1389" class="Symbol"
      >(</a
      ><a name="1390" href="Stlc.html#745" class="InductiveConstructor Operator"
      >&#955;[</a
      ><a name="1392"
      > </a
      ><a name="1393" href="Stlc.html#1393" class="Bound"
      >x&#8242;</a
      ><a name="1395"
      > </a
      ><a name="1396" href="Stlc.html#745" class="InductiveConstructor Operator"
      >&#8758;</a
      ><a name="1397"
      > </a
      ><a name="1398" href="Stlc.html#1398" class="Bound"
      >A&#8242;</a
      ><a name="1400"
      > </a
      ><a name="1401" href="Stlc.html#745" class="InductiveConstructor Operator"
      >]</a
      ><a name="1402"
      > </a
      ><a name="1403" href="Stlc.html#1403" class="Bound"
      >N&#8242;</a
      ><a name="1405" class="Symbol"
      >)</a
      ><a name="1406"
      > </a
      ><a name="1407" href="Stlc.html#1286" class="Function Operator"
      >[</a
      ><a name="1408"
      > </a
      ><a name="1409" href="Stlc.html#1409" class="Bound"
      >x</a
      ><a name="1410"
      > </a
      ><a name="1411" href="Stlc.html#1286" class="Function Operator"
      >&#8758;=</a
      ><a name="1413"
      > </a
      ><a name="1414" href="Stlc.html#1414" class="Bound"
      >V</a
      ><a name="1415"
      > </a
      ><a name="1416" href="Stlc.html#1286" class="Function Operator"
      >]</a
      ><a name="1417"
      > </a
      ><a name="1418" class="Keyword"
      >with</a
      ><a name="1422"
      > </a
      ><a name="1423" href="Stlc.html#1409" class="Bound"
      >x</a
      ><a name="1424"
      > </a
      ><a name="1425" href="Maps.html#2509" class="Function Operator"
      >&#8799;</a
      ><a name="1426"
      > </a
      ><a name="1427" href="Stlc.html#1393" class="Bound"
      >x&#8242;</a
      ><a name="1429"
      >
</a
      ><a name="1430" class="Symbol"
      >...</a
      ><a name="1433"
      > </a
      ><a name="1434" class="Symbol"
      >|</a
      ><a name="1435"
      > </a
      ><a name="1436" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#520" class="InductiveConstructor"
      >yes</a
      ><a name="1439"
      > </a
      ><a name="1440" class="Symbol"
      >_</a
      ><a name="1441"
      > </a
      ><a name="1442" class="Symbol"
      >=</a
      ><a name="1443"
      > </a
      ><a name="1444" href="Stlc.html#745" class="InductiveConstructor Operator"
      >&#955;[</a
      ><a name="1446"
      > </a
      ><a name="1447" href="Stlc.html#1393" class="Bound"
      >x&#8242;</a
      ><a name="1449"
      > </a
      ><a name="1450" href="Stlc.html#745" class="InductiveConstructor Operator"
      >&#8758;</a
      ><a name="1451"
      > </a
      ><a name="1452" href="Stlc.html#1398" class="Bound"
      >A&#8242;</a
      ><a name="1454"
      > </a
      ><a name="1455" href="Stlc.html#745" class="InductiveConstructor Operator"
      >]</a
      ><a name="1456"
      > </a
      ><a name="1457" href="Stlc.html#1403" class="Bound"
      >N&#8242;</a
      ><a name="1459"
      >
</a
      ><a name="1460" class="Symbol"
      >...</a
      ><a name="1463"
      > </a
      ><a name="1464" class="Symbol"
      >|</a
      ><a name="1465"
      > </a
      ><a name="1466" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#547" class="InductiveConstructor"
      >no</a
      ><a name="1468"
      >  </a
      ><a name="1470" class="Symbol"
      >_</a
      ><a name="1471"
      > </a
      ><a name="1472" class="Symbol"
      >=</a
      ><a name="1473"
      > </a
      ><a name="1474" href="Stlc.html#745" class="InductiveConstructor Operator"
      >&#955;[</a
      ><a name="1476"
      > </a
      ><a name="1477" href="Stlc.html#1393" class="Bound"
      >x&#8242;</a
      ><a name="1479"
      > </a
      ><a name="1480" href="Stlc.html#745" class="InductiveConstructor Operator"
      >&#8758;</a
      ><a name="1481"
      > </a
      ><a name="1482" href="Stlc.html#1398" class="Bound"
      >A&#8242;</a
      ><a name="1484"
      > </a
      ><a name="1485" href="Stlc.html#745" class="InductiveConstructor Operator"
      >]</a
      ><a name="1486"
      > </a
      ><a name="1487" class="Symbol"
      >(</a
      ><a name="1488" href="Stlc.html#1403" class="Bound"
      >N&#8242;</a
      ><a name="1490"
      > </a
      ><a name="1491" href="Stlc.html#1286" class="Function Operator"
      >[</a
      ><a name="1492"
      > </a
      ><a name="1493" href="Stlc.html#1409" class="Bound"
      >x</a
      ><a name="1494"
      > </a
      ><a name="1495" href="Stlc.html#1286" class="Function Operator"
      >&#8758;=</a
      ><a name="1497"
      > </a
      ><a name="1498" href="Stlc.html#1414" class="Bound"
      >V</a
      ><a name="1499"
      > </a
      ><a name="1500" href="Stlc.html#1286" class="Function Operator"
      >]</a
      ><a name="1501" class="Symbol"
      >)</a
      ><a name="1502"
      >
</a
      ><a name="1503" class="Symbol"
      >(</a
      ><a name="1504" href="Stlc.html#1504" class="Bound"
      >L&#8242;</a
      ><a name="1506"
      > </a
      ><a name="1507" href="Stlc.html#781" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="1508"
      > </a
      ><a name="1509" href="Stlc.html#1509" class="Bound"
      >M&#8242;</a
      ><a name="1511" class="Symbol"
      >)</a
      ><a name="1512"
      > </a
      ><a name="1513" href="Stlc.html#1286" class="Function Operator"
      >[</a
      ><a name="1514"
      > </a
      ><a name="1515" href="Stlc.html#1515" class="Bound"
      >x</a
      ><a name="1516"
      > </a
      ><a name="1517" href="Stlc.html#1286" class="Function Operator"
      >&#8758;=</a
      ><a name="1519"
      > </a
      ><a name="1520" href="Stlc.html#1520" class="Bound"
      >V</a
      ><a name="1521"
      > </a
      ><a name="1522" href="Stlc.html#1286" class="Function Operator"
      >]</a
      ><a name="1523"
      > </a
      ><a name="1524" class="Symbol"
      >=</a
      ><a name="1525"
      >  </a
      ><a name="1527" class="Symbol"
      >(</a
      ><a name="1528" href="Stlc.html#1504" class="Bound"
      >L&#8242;</a
      ><a name="1530"
      > </a
      ><a name="1531" href="Stlc.html#1286" class="Function Operator"
      >[</a
      ><a name="1532"
      > </a
      ><a name="1533" href="Stlc.html#1515" class="Bound"
      >x</a
      ><a name="1534"
      > </a
      ><a name="1535" href="Stlc.html#1286" class="Function Operator"
      >&#8758;=</a
      ><a name="1537"
      > </a
      ><a name="1538" href="Stlc.html#1520" class="Bound"
      >V</a
      ><a name="1539"
      > </a
      ><a name="1540" href="Stlc.html#1286" class="Function Operator"
      >]</a
      ><a name="1541" class="Symbol"
      >)</a
      ><a name="1542"
      > </a
      ><a name="1543" href="Stlc.html#781" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="1544"
      > </a
      ><a name="1545" class="Symbol"
      >(</a
      ><a name="1546" href="Stlc.html#1509" class="Bound"
      >M&#8242;</a
      ><a name="1548"
      > </a
      ><a name="1549" href="Stlc.html#1286" class="Function Operator"
      >[</a
      ><a name="1550"
      > </a
      ><a name="1551" href="Stlc.html#1515" class="Bound"
      >x</a
      ><a name="1552"
      > </a
      ><a name="1553" href="Stlc.html#1286" class="Function Operator"
      >&#8758;=</a
      ><a name="1555"
      > </a
      ><a name="1556" href="Stlc.html#1520" class="Bound"
      >V</a
      ><a name="1557"
      > </a
      ><a name="1558" href="Stlc.html#1286" class="Function Operator"
      >]</a
      ><a name="1559" class="Symbol"
      >)</a
      ><a name="1560"
      >
</a
      ><a name="1561" class="Symbol"
      >(</a
      ><a name="1562" href="Stlc.html#808" class="InductiveConstructor"
      >true</a
      ><a name="1566" class="Symbol"
      >)</a
      ><a name="1567"
      > </a
      ><a name="1568" href="Stlc.html#1286" class="Function Operator"
      >[</a
      ><a name="1569"
      > </a
      ><a name="1570" href="Stlc.html#1570" class="Bound"
      >x</a
      ><a name="1571"
      > </a
      ><a name="1572" href="Stlc.html#1286" class="Function Operator"
      >&#8758;=</a
      ><a name="1574"
      > </a
      ><a name="1575" href="Stlc.html#1575" class="Bound"
      >V</a
      ><a name="1576"
      > </a
      ><a name="1577" href="Stlc.html#1286" class="Function Operator"
      >]</a
      ><a name="1578"
      > </a
      ><a name="1579" class="Symbol"
      >=</a
      ><a name="1580"
      > </a
      ><a name="1581" href="Stlc.html#808" class="InductiveConstructor"
      >true</a
      ><a name="1585"
      >
</a
      ><a name="1586" class="Symbol"
      >(</a
      ><a name="1587" href="Stlc.html#822" class="InductiveConstructor"
      >false</a
      ><a name="1592" class="Symbol"
      >)</a
      ><a name="1593"
      > </a
      ><a name="1594" href="Stlc.html#1286" class="Function Operator"
      >[</a
      ><a name="1595"
      > </a
      ><a name="1596" href="Stlc.html#1596" class="Bound"
      >x</a
      ><a name="1597"
      > </a
      ><a name="1598" href="Stlc.html#1286" class="Function Operator"
      >&#8758;=</a
      ><a name="1600"
      > </a
      ><a name="1601" href="Stlc.html#1601" class="Bound"
      >V</a
      ><a name="1602"
      > </a
      ><a name="1603" href="Stlc.html#1286" class="Function Operator"
      >]</a
      ><a name="1604"
      > </a
      ><a name="1605" class="Symbol"
      >=</a
      ><a name="1606"
      > </a
      ><a name="1607" href="Stlc.html#822" class="InductiveConstructor"
      >false</a
      ><a name="1612"
      >
</a
      ><a name="1613" class="Symbol"
      >(</a
      ><a name="1614" href="Stlc.html#837" class="InductiveConstructor Operator"
      >if</a
      ><a name="1616"
      > </a
      ><a name="1617" href="Stlc.html#1617" class="Bound"
      >L&#8242;</a
      ><a name="1619"
      > </a
      ><a name="1620" href="Stlc.html#837" class="InductiveConstructor Operator"
      >then</a
      ><a name="1624"
      > </a
      ><a name="1625" href="Stlc.html#1625" class="Bound"
      >M&#8242;</a
      ><a name="1627"
      > </a
      ><a name="1628" href="Stlc.html#837" class="InductiveConstructor Operator"
      >else</a
      ><a name="1632"
      > </a
      ><a name="1633" href="Stlc.html#1633" class="Bound"
      >N&#8242;</a
      ><a name="1635" class="Symbol"
      >)</a
      ><a name="1636"
      > </a
      ><a name="1637" href="Stlc.html#1286" class="Function Operator"
      >[</a
      ><a name="1638"
      > </a
      ><a name="1639" href="Stlc.html#1639" class="Bound"
      >x</a
      ><a name="1640"
      > </a
      ><a name="1641" href="Stlc.html#1286" class="Function Operator"
      >&#8758;=</a
      ><a name="1643"
      > </a
      ><a name="1644" href="Stlc.html#1644" class="Bound"
      >V</a
      ><a name="1645"
      > </a
      ><a name="1646" href="Stlc.html#1286" class="Function Operator"
      >]</a
      ><a name="1647"
      > </a
      ><a name="1648" class="Symbol"
      >=</a
      ><a name="1649"
      > </a
      ><a name="1650" href="Stlc.html#837" class="InductiveConstructor Operator"
      >if</a
      ><a name="1652"
      > </a
      ><a name="1653" class="Symbol"
      >(</a
      ><a name="1654" href="Stlc.html#1617" class="Bound"
      >L&#8242;</a
      ><a name="1656"
      > </a
      ><a name="1657" href="Stlc.html#1286" class="Function Operator"
      >[</a
      ><a name="1658"
      > </a
      ><a name="1659" href="Stlc.html#1639" class="Bound"
      >x</a
      ><a name="1660"
      > </a
      ><a name="1661" href="Stlc.html#1286" class="Function Operator"
      >&#8758;=</a
      ><a name="1663"
      > </a
      ><a name="1664" href="Stlc.html#1644" class="Bound"
      >V</a
      ><a name="1665"
      > </a
      ><a name="1666" href="Stlc.html#1286" class="Function Operator"
      >]</a
      ><a name="1667" class="Symbol"
      >)</a
      ><a name="1668"
      > </a
      ><a name="1669" href="Stlc.html#837" class="InductiveConstructor Operator"
      >then</a
      ><a name="1673"
      > </a
      ><a name="1674" class="Symbol"
      >(</a
      ><a name="1675" href="Stlc.html#1625" class="Bound"
      >M&#8242;</a
      ><a name="1677"
      > </a
      ><a name="1678" href="Stlc.html#1286" class="Function Operator"
      >[</a
      ><a name="1679"
      > </a
      ><a name="1680" href="Stlc.html#1639" class="Bound"
      >x</a
      ><a name="1681"
      > </a
      ><a name="1682" href="Stlc.html#1286" class="Function Operator"
      >&#8758;=</a
      ><a name="1684"
      > </a
      ><a name="1685" href="Stlc.html#1644" class="Bound"
      >V</a
      ><a name="1686"
      > </a
      ><a name="1687" href="Stlc.html#1286" class="Function Operator"
      >]</a
      ><a name="1688" class="Symbol"
      >)</a
      ><a name="1689"
      > </a
      ><a name="1690" href="Stlc.html#837" class="InductiveConstructor Operator"
      >else</a
      ><a name="1694"
      > </a
      ><a name="1695" class="Symbol"
      >(</a
      ><a name="1696" href="Stlc.html#1633" class="Bound"
      >N&#8242;</a
      ><a name="1698"
      > </a
      ><a name="1699" href="Stlc.html#1286" class="Function Operator"
      >[</a
      ><a name="1700"
      > </a
      ><a name="1701" href="Stlc.html#1639" class="Bound"
      >x</a
      ><a name="1702"
      > </a
      ><a name="1703" href="Stlc.html#1286" class="Function Operator"
      >&#8758;=</a
      ><a name="1705"
      > </a
      ><a name="1706" href="Stlc.html#1644" class="Bound"
      >V</a
      ><a name="1707"
      > </a
      ><a name="1708" href="Stlc.html#1286" class="Function Operator"
      >]</a
      ><a name="1709" class="Symbol"
      >)</a
      >
{% endraw %}</pre>

## Reduction rules

<pre class="Agda">{% raw %}
<a name="1756" class="Keyword"
      >infix</a
      ><a name="1761"
      > </a
      ><a name="1762" class="Number"
      >10</a
      ><a name="1764"
      > </a
      ><a name="1765" href="Stlc.html#1776" class="Datatype Operator"
      >_&#10233;_</a
      ><a name="1768"
      > 

</a
      ><a name="1771" class="Keyword"
      >data</a
      ><a name="1775"
      > </a
      ><a name="1776" href="Stlc.html#1776" class="Datatype Operator"
      >_&#10233;_</a
      ><a name="1779"
      > </a
      ><a name="1780" class="Symbol"
      >:</a
      ><a name="1781"
      > </a
      ><a name="1782" href="Stlc.html#708" class="Datatype"
      >Term</a
      ><a name="1786"
      > </a
      ><a name="1787" class="Symbol"
      >&#8594;</a
      ><a name="1788"
      > </a
      ><a name="1789" href="Stlc.html#708" class="Datatype"
      >Term</a
      ><a name="1793"
      > </a
      ><a name="1794" class="Symbol"
      >&#8594;</a
      ><a name="1795"
      > </a
      ><a name="1796" class="PrimitiveType"
      >Set</a
      ><a name="1799"
      > </a
      ><a name="1800" class="Keyword"
      >where</a
      ><a name="1805"
      >
  </a
      ><a name="1808" href="Stlc.html#1808" class="InductiveConstructor"
      >&#946;&#8658;</a
      ><a name="1810"
      > </a
      ><a name="1811" class="Symbol"
      >:</a
      ><a name="1812"
      > </a
      ><a name="1813" class="Symbol"
      >&#8704;</a
      ><a name="1814"
      > </a
      ><a name="1815" class="Symbol"
      >{</a
      ><a name="1816" href="Stlc.html#1816" class="Bound"
      >x</a
      ><a name="1817"
      > </a
      ><a name="1818" href="Stlc.html#1818" class="Bound"
      >A</a
      ><a name="1819"
      > </a
      ><a name="1820" href="Stlc.html#1820" class="Bound"
      >N</a
      ><a name="1821"
      > </a
      ><a name="1822" href="Stlc.html#1822" class="Bound"
      >V</a
      ><a name="1823" class="Symbol"
      >}</a
      ><a name="1824"
      > </a
      ><a name="1825" class="Symbol"
      >&#8594;</a
      ><a name="1826"
      > </a
      ><a name="1827" href="Stlc.html#1115" class="Datatype"
      >Value</a
      ><a name="1832"
      > </a
      ><a name="1833" href="Stlc.html#1822" class="Bound"
      >V</a
      ><a name="1834"
      > </a
      ><a name="1835" class="Symbol"
      >&#8594;</a
      ><a name="1836"
      >
    </a
      ><a name="1841" class="Symbol"
      >(</a
      ><a name="1842" href="Stlc.html#745" class="InductiveConstructor Operator"
      >&#955;[</a
      ><a name="1844"
      > </a
      ><a name="1845" href="Stlc.html#1816" class="Bound"
      >x</a
      ><a name="1846"
      > </a
      ><a name="1847" href="Stlc.html#745" class="InductiveConstructor Operator"
      >&#8758;</a
      ><a name="1848"
      > </a
      ><a name="1849" href="Stlc.html#1818" class="Bound"
      >A</a
      ><a name="1850"
      > </a
      ><a name="1851" href="Stlc.html#745" class="InductiveConstructor Operator"
      >]</a
      ><a name="1852"
      > </a
      ><a name="1853" href="Stlc.html#1820" class="Bound"
      >N</a
      ><a name="1854" class="Symbol"
      >)</a
      ><a name="1855"
      > </a
      ><a name="1856" href="Stlc.html#781" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="1857"
      > </a
      ><a name="1858" href="Stlc.html#1822" class="Bound"
      >V</a
      ><a name="1859"
      > </a
      ><a name="1860" href="Stlc.html#1776" class="Datatype Operator"
      >&#10233;</a
      ><a name="1861"
      > </a
      ><a name="1862" href="Stlc.html#1820" class="Bound"
      >N</a
      ><a name="1863"
      > </a
      ><a name="1864" href="Stlc.html#1286" class="Function Operator"
      >[</a
      ><a name="1865"
      > </a
      ><a name="1866" href="Stlc.html#1816" class="Bound"
      >x</a
      ><a name="1867"
      > </a
      ><a name="1868" href="Stlc.html#1286" class="Function Operator"
      >&#8758;=</a
      ><a name="1870"
      > </a
      ><a name="1871" href="Stlc.html#1822" class="Bound"
      >V</a
      ><a name="1872"
      > </a
      ><a name="1873" href="Stlc.html#1286" class="Function Operator"
      >]</a
      ><a name="1874"
      >
  </a
      ><a name="1877" href="Stlc.html#1877" class="InductiveConstructor"
      >&#947;&#8658;&#8321;</a
      ><a name="1880"
      > </a
      ><a name="1881" class="Symbol"
      >:</a
      ><a name="1882"
      > </a
      ><a name="1883" class="Symbol"
      >&#8704;</a
      ><a name="1884"
      > </a
      ><a name="1885" class="Symbol"
      >{</a
      ><a name="1886" href="Stlc.html#1886" class="Bound"
      >L</a
      ><a name="1887"
      > </a
      ><a name="1888" href="Stlc.html#1888" class="Bound"
      >L'</a
      ><a name="1890"
      > </a
      ><a name="1891" href="Stlc.html#1891" class="Bound"
      >M</a
      ><a name="1892" class="Symbol"
      >}</a
      ><a name="1893"
      > </a
      ><a name="1894" class="Symbol"
      >&#8594;</a
      ><a name="1895"
      >
    </a
      ><a name="1900" href="Stlc.html#1886" class="Bound"
      >L</a
      ><a name="1901"
      > </a
      ><a name="1902" href="Stlc.html#1776" class="Datatype Operator"
      >&#10233;</a
      ><a name="1903"
      > </a
      ><a name="1904" href="Stlc.html#1888" class="Bound"
      >L'</a
      ><a name="1906"
      > </a
      ><a name="1907" class="Symbol"
      >&#8594;</a
      ><a name="1908"
      >
    </a
      ><a name="1913" href="Stlc.html#1886" class="Bound"
      >L</a
      ><a name="1914"
      > </a
      ><a name="1915" href="Stlc.html#781" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="1916"
      > </a
      ><a name="1917" href="Stlc.html#1891" class="Bound"
      >M</a
      ><a name="1918"
      > </a
      ><a name="1919" href="Stlc.html#1776" class="Datatype Operator"
      >&#10233;</a
      ><a name="1920"
      > </a
      ><a name="1921" href="Stlc.html#1888" class="Bound"
      >L'</a
      ><a name="1923"
      > </a
      ><a name="1924" href="Stlc.html#781" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="1925"
      > </a
      ><a name="1926" href="Stlc.html#1891" class="Bound"
      >M</a
      ><a name="1927"
      >
  </a
      ><a name="1930" href="Stlc.html#1930" class="InductiveConstructor"
      >&#947;&#8658;&#8322;</a
      ><a name="1933"
      > </a
      ><a name="1934" class="Symbol"
      >:</a
      ><a name="1935"
      > </a
      ><a name="1936" class="Symbol"
      >&#8704;</a
      ><a name="1937"
      > </a
      ><a name="1938" class="Symbol"
      >{</a
      ><a name="1939" href="Stlc.html#1939" class="Bound"
      >V</a
      ><a name="1940"
      > </a
      ><a name="1941" href="Stlc.html#1941" class="Bound"
      >M</a
      ><a name="1942"
      > </a
      ><a name="1943" href="Stlc.html#1943" class="Bound"
      >M'</a
      ><a name="1945" class="Symbol"
      >}</a
      ><a name="1946"
      > </a
      ><a name="1947" class="Symbol"
      >&#8594;</a
      ><a name="1948"
      >
    </a
      ><a name="1953" href="Stlc.html#1115" class="Datatype"
      >Value</a
      ><a name="1958"
      > </a
      ><a name="1959" href="Stlc.html#1939" class="Bound"
      >V</a
      ><a name="1960"
      > </a
      ><a name="1961" class="Symbol"
      >&#8594;</a
      ><a name="1962"
      >
    </a
      ><a name="1967" href="Stlc.html#1941" class="Bound"
      >M</a
      ><a name="1968"
      > </a
      ><a name="1969" href="Stlc.html#1776" class="Datatype Operator"
      >&#10233;</a
      ><a name="1970"
      > </a
      ><a name="1971" href="Stlc.html#1943" class="Bound"
      >M'</a
      ><a name="1973"
      > </a
      ><a name="1974" class="Symbol"
      >&#8594;</a
      ><a name="1975"
      >
    </a
      ><a name="1980" href="Stlc.html#1939" class="Bound"
      >V</a
      ><a name="1981"
      > </a
      ><a name="1982" href="Stlc.html#781" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="1983"
      > </a
      ><a name="1984" href="Stlc.html#1941" class="Bound"
      >M</a
      ><a name="1985"
      > </a
      ><a name="1986" href="Stlc.html#1776" class="Datatype Operator"
      >&#10233;</a
      ><a name="1987"
      > </a
      ><a name="1988" href="Stlc.html#1939" class="Bound"
      >V</a
      ><a name="1989"
      > </a
      ><a name="1990" href="Stlc.html#781" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="1991"
      > </a
      ><a name="1992" href="Stlc.html#1943" class="Bound"
      >M'</a
      ><a name="1994"
      >
  </a
      ><a name="1997" href="Stlc.html#1997" class="InductiveConstructor"
      >&#946;&#120121;&#8321;</a
      ><a name="2000"
      > </a
      ><a name="2001" class="Symbol"
      >:</a
      ><a name="2002"
      > </a
      ><a name="2003" class="Symbol"
      >&#8704;</a
      ><a name="2004"
      > </a
      ><a name="2005" class="Symbol"
      >{</a
      ><a name="2006" href="Stlc.html#2006" class="Bound"
      >M</a
      ><a name="2007"
      > </a
      ><a name="2008" href="Stlc.html#2008" class="Bound"
      >N</a
      ><a name="2009" class="Symbol"
      >}</a
      ><a name="2010"
      > </a
      ><a name="2011" class="Symbol"
      >&#8594;</a
      ><a name="2012"
      >
    </a
      ><a name="2017" href="Stlc.html#837" class="InductiveConstructor Operator"
      >if</a
      ><a name="2019"
      > </a
      ><a name="2020" href="Stlc.html#808" class="InductiveConstructor"
      >true</a
      ><a name="2024"
      > </a
      ><a name="2025" href="Stlc.html#837" class="InductiveConstructor Operator"
      >then</a
      ><a name="2029"
      > </a
      ><a name="2030" href="Stlc.html#2006" class="Bound"
      >M</a
      ><a name="2031"
      > </a
      ><a name="2032" href="Stlc.html#837" class="InductiveConstructor Operator"
      >else</a
      ><a name="2036"
      > </a
      ><a name="2037" href="Stlc.html#2008" class="Bound"
      >N</a
      ><a name="2038"
      > </a
      ><a name="2039" href="Stlc.html#1776" class="Datatype Operator"
      >&#10233;</a
      ><a name="2040"
      > </a
      ><a name="2041" href="Stlc.html#2006" class="Bound"
      >M</a
      ><a name="2042"
      >
  </a
      ><a name="2045" href="Stlc.html#2045" class="InductiveConstructor"
      >&#946;&#120121;&#8322;</a
      ><a name="2048"
      > </a
      ><a name="2049" class="Symbol"
      >:</a
      ><a name="2050"
      > </a
      ><a name="2051" class="Symbol"
      >&#8704;</a
      ><a name="2052"
      > </a
      ><a name="2053" class="Symbol"
      >{</a
      ><a name="2054" href="Stlc.html#2054" class="Bound"
      >M</a
      ><a name="2055"
      > </a
      ><a name="2056" href="Stlc.html#2056" class="Bound"
      >N</a
      ><a name="2057" class="Symbol"
      >}</a
      ><a name="2058"
      > </a
      ><a name="2059" class="Symbol"
      >&#8594;</a
      ><a name="2060"
      >
    </a
      ><a name="2065" href="Stlc.html#837" class="InductiveConstructor Operator"
      >if</a
      ><a name="2067"
      > </a
      ><a name="2068" href="Stlc.html#822" class="InductiveConstructor"
      >false</a
      ><a name="2073"
      > </a
      ><a name="2074" href="Stlc.html#837" class="InductiveConstructor Operator"
      >then</a
      ><a name="2078"
      > </a
      ><a name="2079" href="Stlc.html#2054" class="Bound"
      >M</a
      ><a name="2080"
      > </a
      ><a name="2081" href="Stlc.html#837" class="InductiveConstructor Operator"
      >else</a
      ><a name="2085"
      > </a
      ><a name="2086" href="Stlc.html#2056" class="Bound"
      >N</a
      ><a name="2087"
      > </a
      ><a name="2088" href="Stlc.html#1776" class="Datatype Operator"
      >&#10233;</a
      ><a name="2089"
      > </a
      ><a name="2090" href="Stlc.html#2056" class="Bound"
      >N</a
      ><a name="2091"
      >
  </a
      ><a name="2094" href="Stlc.html#2094" class="InductiveConstructor"
      >&#947;&#120121;</a
      ><a name="2096"
      > </a
      ><a name="2097" class="Symbol"
      >:</a
      ><a name="2098"
      > </a
      ><a name="2099" class="Symbol"
      >&#8704;</a
      ><a name="2100"
      > </a
      ><a name="2101" class="Symbol"
      >{</a
      ><a name="2102" href="Stlc.html#2102" class="Bound"
      >L</a
      ><a name="2103"
      > </a
      ><a name="2104" href="Stlc.html#2104" class="Bound"
      >L'</a
      ><a name="2106"
      > </a
      ><a name="2107" href="Stlc.html#2107" class="Bound"
      >M</a
      ><a name="2108"
      > </a
      ><a name="2109" href="Stlc.html#2109" class="Bound"
      >N</a
      ><a name="2110" class="Symbol"
      >}</a
      ><a name="2111"
      > </a
      ><a name="2112" class="Symbol"
      >&#8594;</a
      ><a name="2113"
      >
    </a
      ><a name="2118" href="Stlc.html#2102" class="Bound"
      >L</a
      ><a name="2119"
      > </a
      ><a name="2120" href="Stlc.html#1776" class="Datatype Operator"
      >&#10233;</a
      ><a name="2121"
      > </a
      ><a name="2122" href="Stlc.html#2104" class="Bound"
      >L'</a
      ><a name="2124"
      > </a
      ><a name="2125" class="Symbol"
      >&#8594;</a
      ><a name="2126"
      >    
    </a
      ><a name="2135" href="Stlc.html#837" class="InductiveConstructor Operator"
      >if</a
      ><a name="2137"
      > </a
      ><a name="2138" href="Stlc.html#2102" class="Bound"
      >L</a
      ><a name="2139"
      > </a
      ><a name="2140" href="Stlc.html#837" class="InductiveConstructor Operator"
      >then</a
      ><a name="2144"
      > </a
      ><a name="2145" href="Stlc.html#2107" class="Bound"
      >M</a
      ><a name="2146"
      > </a
      ><a name="2147" href="Stlc.html#837" class="InductiveConstructor Operator"
      >else</a
      ><a name="2151"
      > </a
      ><a name="2152" href="Stlc.html#2109" class="Bound"
      >N</a
      ><a name="2153"
      > </a
      ><a name="2154" href="Stlc.html#1776" class="Datatype Operator"
      >&#10233;</a
      ><a name="2155"
      > </a
      ><a name="2156" href="Stlc.html#837" class="InductiveConstructor Operator"
      >if</a
      ><a name="2158"
      > </a
      ><a name="2159" href="Stlc.html#2104" class="Bound"
      >L'</a
      ><a name="2161"
      > </a
      ><a name="2162" href="Stlc.html#837" class="InductiveConstructor Operator"
      >then</a
      ><a name="2166"
      > </a
      ><a name="2167" href="Stlc.html#2107" class="Bound"
      >M</a
      ><a name="2168"
      > </a
      ><a name="2169" href="Stlc.html#837" class="InductiveConstructor Operator"
      >else</a
      ><a name="2173"
      > </a
      ><a name="2174" href="Stlc.html#2109" class="Bound"
      >N</a
      >
{% endraw %}</pre>

## Reflexive and transitive closure


<pre class="Agda">{% raw %}
<a name="2239" class="Keyword"
      >infix</a
      ><a name="2244"
      > </a
      ><a name="2245" class="Number"
      >10</a
      ><a name="2247"
      > </a
      ><a name="2248" href="Stlc.html#2288" class="Datatype Operator"
      >_&#10233;*_</a
      ><a name="2252"
      > 
</a
      ><a name="2254" class="Keyword"
      >infixr</a
      ><a name="2260"
      > </a
      ><a name="2261" class="Number"
      >2</a
      ><a name="2262"
      > </a
      ><a name="2263" href="Stlc.html#2341" class="InductiveConstructor Operator"
      >_&#10233;&#10216;_&#10217;_</a
      ><a name="2269"
      >
</a
      ><a name="2270" class="Keyword"
      >infix</a
      ><a name="2275"
      >  </a
      ><a name="2277" class="Number"
      >3</a
      ><a name="2278"
      > </a
      ><a name="2279" href="Stlc.html#2321" class="InductiveConstructor Operator"
      >_&#8718;</a
      ><a name="2281"
      >

</a
      ><a name="2283" class="Keyword"
      >data</a
      ><a name="2287"
      > </a
      ><a name="2288" href="Stlc.html#2288" class="Datatype Operator"
      >_&#10233;*_</a
      ><a name="2292"
      > </a
      ><a name="2293" class="Symbol"
      >:</a
      ><a name="2294"
      > </a
      ><a name="2295" href="Stlc.html#708" class="Datatype"
      >Term</a
      ><a name="2299"
      > </a
      ><a name="2300" class="Symbol"
      >&#8594;</a
      ><a name="2301"
      > </a
      ><a name="2302" href="Stlc.html#708" class="Datatype"
      >Term</a
      ><a name="2306"
      > </a
      ><a name="2307" class="Symbol"
      >&#8594;</a
      ><a name="2308"
      > </a
      ><a name="2309" class="PrimitiveType"
      >Set</a
      ><a name="2312"
      > </a
      ><a name="2313" class="Keyword"
      >where</a
      ><a name="2318"
      >
  </a
      ><a name="2321" href="Stlc.html#2321" class="InductiveConstructor Operator"
      >_&#8718;</a
      ><a name="2323"
      > </a
      ><a name="2324" class="Symbol"
      >:</a
      ><a name="2325"
      > </a
      ><a name="2326" class="Symbol"
      >&#8704;</a
      ><a name="2327"
      > </a
      ><a name="2328" href="Stlc.html#2328" class="Bound"
      >M</a
      ><a name="2329"
      > </a
      ><a name="2330" class="Symbol"
      >&#8594;</a
      ><a name="2331"
      > </a
      ><a name="2332" href="Stlc.html#2328" class="Bound"
      >M</a
      ><a name="2333"
      > </a
      ><a name="2334" href="Stlc.html#2288" class="Datatype Operator"
      >&#10233;*</a
      ><a name="2336"
      > </a
      ><a name="2337" href="Stlc.html#2328" class="Bound"
      >M</a
      ><a name="2338"
      >
  </a
      ><a name="2341" href="Stlc.html#2341" class="InductiveConstructor Operator"
      >_&#10233;&#10216;_&#10217;_</a
      ><a name="2347"
      > </a
      ><a name="2348" class="Symbol"
      >:</a
      ><a name="2349"
      > </a
      ><a name="2350" class="Symbol"
      >&#8704;</a
      ><a name="2351"
      > </a
      ><a name="2352" href="Stlc.html#2352" class="Bound"
      >L</a
      ><a name="2353"
      > </a
      ><a name="2354" class="Symbol"
      >{</a
      ><a name="2355" href="Stlc.html#2355" class="Bound"
      >M</a
      ><a name="2356"
      > </a
      ><a name="2357" href="Stlc.html#2357" class="Bound"
      >N</a
      ><a name="2358" class="Symbol"
      >}</a
      ><a name="2359"
      > </a
      ><a name="2360" class="Symbol"
      >&#8594;</a
      ><a name="2361"
      > </a
      ><a name="2362" href="Stlc.html#2352" class="Bound"
      >L</a
      ><a name="2363"
      > </a
      ><a name="2364" href="Stlc.html#1776" class="Datatype Operator"
      >&#10233;</a
      ><a name="2365"
      > </a
      ><a name="2366" href="Stlc.html#2355" class="Bound"
      >M</a
      ><a name="2367"
      > </a
      ><a name="2368" class="Symbol"
      >&#8594;</a
      ><a name="2369"
      > </a
      ><a name="2370" href="Stlc.html#2355" class="Bound"
      >M</a
      ><a name="2371"
      > </a
      ><a name="2372" href="Stlc.html#2288" class="Datatype Operator"
      >&#10233;*</a
      ><a name="2374"
      > </a
      ><a name="2375" href="Stlc.html#2357" class="Bound"
      >N</a
      ><a name="2376"
      > </a
      ><a name="2377" class="Symbol"
      >&#8594;</a
      ><a name="2378"
      > </a
      ><a name="2379" href="Stlc.html#2352" class="Bound"
      >L</a
      ><a name="2380"
      > </a
      ><a name="2381" href="Stlc.html#2288" class="Datatype Operator"
      >&#10233;*</a
      ><a name="2383"
      > </a
      ><a name="2384" href="Stlc.html#2357" class="Bound"
      >N</a
      ><a name="2385"
      >  

</a
      ><a name="2389" href="Stlc.html#2389" class="Function"
      >reduction&#8321;</a
      ><a name="2399"
      > </a
      ><a name="2400" class="Symbol"
      >:</a
      ><a name="2401"
      > </a
      ><a name="2402" href="Stlc.html#951" class="Function"
      >not</a
      ><a name="2405"
      > </a
      ><a name="2406" href="Stlc.html#781" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="2407"
      > </a
      ><a name="2408" href="Stlc.html#808" class="InductiveConstructor"
      >true</a
      ><a name="2412"
      > </a
      ><a name="2413" href="Stlc.html#2288" class="Datatype Operator"
      >&#10233;*</a
      ><a name="2415"
      > </a
      ><a name="2416" href="Stlc.html#822" class="InductiveConstructor"
      >false</a
      ><a name="2421"
      >
</a
      ><a name="2422" href="Stlc.html#2389" class="Function"
      >reduction&#8321;</a
      ><a name="2432"
      > </a
      ><a name="2433" class="Symbol"
      >=</a
      ><a name="2434"
      >
    </a
      ><a name="2439" href="Stlc.html#951" class="Function"
      >not</a
      ><a name="2442"
      > </a
      ><a name="2443" href="Stlc.html#781" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="2444"
      > </a
      ><a name="2445" href="Stlc.html#808" class="InductiveConstructor"
      >true</a
      ><a name="2449"
      >
  </a
      ><a name="2452" href="Stlc.html#2341" class="InductiveConstructor Operator"
      >&#10233;&#10216;</a
      ><a name="2454"
      > </a
      ><a name="2455" href="Stlc.html#1808" class="InductiveConstructor"
      >&#946;&#8658;</a
      ><a name="2457"
      > </a
      ><a name="2458" href="Stlc.html#1191" class="InductiveConstructor"
      >value-true</a
      ><a name="2468"
      > </a
      ><a name="2469" href="Stlc.html#2341" class="InductiveConstructor Operator"
      >&#10217;</a
      ><a name="2470"
      >
    </a
      ><a name="2475" href="Stlc.html#837" class="InductiveConstructor Operator"
      >if</a
      ><a name="2477"
      > </a
      ><a name="2478" href="Stlc.html#808" class="InductiveConstructor"
      >true</a
      ><a name="2482"
      > </a
      ><a name="2483" href="Stlc.html#837" class="InductiveConstructor Operator"
      >then</a
      ><a name="2487"
      > </a
      ><a name="2488" href="Stlc.html#822" class="InductiveConstructor"
      >false</a
      ><a name="2493"
      > </a
      ><a name="2494" href="Stlc.html#837" class="InductiveConstructor Operator"
      >else</a
      ><a name="2498"
      > </a
      ><a name="2499" href="Stlc.html#808" class="InductiveConstructor"
      >true</a
      ><a name="2503"
      >
  </a
      ><a name="2506" href="Stlc.html#2341" class="InductiveConstructor Operator"
      >&#10233;&#10216;</a
      ><a name="2508"
      > </a
      ><a name="2509" href="Stlc.html#1997" class="InductiveConstructor"
      >&#946;&#120121;&#8321;</a
      ><a name="2512"
      > </a
      ><a name="2513" href="Stlc.html#2341" class="InductiveConstructor Operator"
      >&#10217;</a
      ><a name="2514"
      >
    </a
      ><a name="2519" href="Stlc.html#822" class="InductiveConstructor"
      >false</a
      ><a name="2524"
      >
  </a
      ><a name="2527" href="Stlc.html#2321" class="InductiveConstructor Operator"
      >&#8718;</a
      ><a name="2528"
      >

</a
      ><a name="2530" href="Stlc.html#2530" class="Function"
      >reduction&#8322;</a
      ><a name="2540"
      > </a
      ><a name="2541" class="Symbol"
      >:</a
      ><a name="2542"
      > </a
      ><a name="2543" href="Stlc.html#955" class="Function"
      >two</a
      ><a name="2546"
      > </a
      ><a name="2547" href="Stlc.html#781" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="2548"
      > </a
      ><a name="2549" href="Stlc.html#951" class="Function"
      >not</a
      ><a name="2552"
      > </a
      ><a name="2553" href="Stlc.html#781" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="2554"
      > </a
      ><a name="2555" href="Stlc.html#808" class="InductiveConstructor"
      >true</a
      ><a name="2559"
      > </a
      ><a name="2560" href="Stlc.html#2288" class="Datatype Operator"
      >&#10233;*</a
      ><a name="2562"
      > </a
      ><a name="2563" href="Stlc.html#808" class="InductiveConstructor"
      >true</a
      ><a name="2567"
      >
</a
      ><a name="2568" href="Stlc.html#2530" class="Function"
      >reduction&#8322;</a
      ><a name="2578"
      > </a
      ><a name="2579" class="Symbol"
      >=</a
      ><a name="2580"
      >
    </a
      ><a name="2585" href="Stlc.html#955" class="Function"
      >two</a
      ><a name="2588"
      > </a
      ><a name="2589" href="Stlc.html#781" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="2590"
      > </a
      ><a name="2591" href="Stlc.html#951" class="Function"
      >not</a
      ><a name="2594"
      > </a
      ><a name="2595" href="Stlc.html#781" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="2596"
      > </a
      ><a name="2597" href="Stlc.html#808" class="InductiveConstructor"
      >true</a
      ><a name="2601"
      >
  </a
      ><a name="2604" href="Stlc.html#2341" class="InductiveConstructor Operator"
      >&#10233;&#10216;</a
      ><a name="2606"
      > </a
      ><a name="2607" href="Stlc.html#1877" class="InductiveConstructor"
      >&#947;&#8658;&#8321;</a
      ><a name="2610"
      > </a
      ><a name="2611" class="Symbol"
      >(</a
      ><a name="2612" href="Stlc.html#1808" class="InductiveConstructor"
      >&#946;&#8658;</a
      ><a name="2614"
      > </a
      ><a name="2615" href="Stlc.html#1142" class="InductiveConstructor"
      >value-&#955;</a
      ><a name="2622" class="Symbol"
      >)</a
      ><a name="2623"
      > </a
      ><a name="2624" href="Stlc.html#2341" class="InductiveConstructor Operator"
      >&#10217;</a
      ><a name="2625"
      >
    </a
      ><a name="2630" class="Symbol"
      >(</a
      ><a name="2631" href="Stlc.html#745" class="InductiveConstructor Operator"
      >&#955;[</a
      ><a name="2633"
      > </a
      ><a name="2634" href="Stlc.html#921" class="Function"
      >x</a
      ><a name="2635"
      > </a
      ><a name="2636" href="Stlc.html#745" class="InductiveConstructor Operator"
      >&#8758;</a
      ><a name="2637"
      > </a
      ><a name="2638" href="Stlc.html#609" class="InductiveConstructor"
      >&#120121;</a
      ><a name="2639"
      > </a
      ><a name="2640" href="Stlc.html#745" class="InductiveConstructor Operator"
      >]</a
      ><a name="2641"
      > </a
      ><a name="2642" href="Stlc.html#951" class="Function"
      >not</a
      ><a name="2645"
      > </a
      ><a name="2646" href="Stlc.html#781" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="2647"
      > </a
      ><a name="2648" class="Symbol"
      >(</a
      ><a name="2649" href="Stlc.html#951" class="Function"
      >not</a
      ><a name="2652"
      > </a
      ><a name="2653" href="Stlc.html#781" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="2654"
      > </a
      ><a name="2655" href="Stlc.html#727" class="InductiveConstructor"
      >var</a
      ><a name="2658"
      > </a
      ><a name="2659" href="Stlc.html#921" class="Function"
      >x</a
      ><a name="2660" class="Symbol"
      >))</a
      ><a name="2662"
      > </a
      ><a name="2663" href="Stlc.html#781" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="2664"
      > </a
      ><a name="2665" href="Stlc.html#808" class="InductiveConstructor"
      >true</a
      ><a name="2669"
      >
  </a
      ><a name="2672" href="Stlc.html#2341" class="InductiveConstructor Operator"
      >&#10233;&#10216;</a
      ><a name="2674"
      > </a
      ><a name="2675" href="Stlc.html#1808" class="InductiveConstructor"
      >&#946;&#8658;</a
      ><a name="2677"
      > </a
      ><a name="2678" href="Stlc.html#1191" class="InductiveConstructor"
      >value-true</a
      ><a name="2688"
      > </a
      ><a name="2689" href="Stlc.html#2341" class="InductiveConstructor Operator"
      >&#10217;</a
      ><a name="2690"
      >
    </a
      ><a name="2695" href="Stlc.html#951" class="Function"
      >not</a
      ><a name="2698"
      > </a
      ><a name="2699" href="Stlc.html#781" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="2700"
      > </a
      ><a name="2701" class="Symbol"
      >(</a
      ><a name="2702" href="Stlc.html#951" class="Function"
      >not</a
      ><a name="2705"
      > </a
      ><a name="2706" href="Stlc.html#781" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="2707"
      > </a
      ><a name="2708" href="Stlc.html#808" class="InductiveConstructor"
      >true</a
      ><a name="2712" class="Symbol"
      >)</a
      ><a name="2713"
      >
  </a
      ><a name="2716" href="Stlc.html#2341" class="InductiveConstructor Operator"
      >&#10233;&#10216;</a
      ><a name="2718"
      > </a
      ><a name="2719" href="Stlc.html#1930" class="InductiveConstructor"
      >&#947;&#8658;&#8322;</a
      ><a name="2722"
      > </a
      ><a name="2723" href="Stlc.html#1142" class="InductiveConstructor"
      >value-&#955;</a
      ><a name="2730"
      > </a
      ><a name="2731" class="Symbol"
      >(</a
      ><a name="2732" href="Stlc.html#1808" class="InductiveConstructor"
      >&#946;&#8658;</a
      ><a name="2734"
      > </a
      ><a name="2735" href="Stlc.html#1191" class="InductiveConstructor"
      >value-true</a
      ><a name="2745" class="Symbol"
      >)</a
      ><a name="2746"
      > </a
      ><a name="2747" href="Stlc.html#2341" class="InductiveConstructor Operator"
      >&#10217;</a
      ><a name="2748"
      >
    </a
      ><a name="2753" href="Stlc.html#951" class="Function"
      >not</a
      ><a name="2756"
      > </a
      ><a name="2757" href="Stlc.html#781" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="2758"
      > </a
      ><a name="2759" class="Symbol"
      >(</a
      ><a name="2760" href="Stlc.html#837" class="InductiveConstructor Operator"
      >if</a
      ><a name="2762"
      > </a
      ><a name="2763" href="Stlc.html#808" class="InductiveConstructor"
      >true</a
      ><a name="2767"
      > </a
      ><a name="2768" href="Stlc.html#837" class="InductiveConstructor Operator"
      >then</a
      ><a name="2772"
      > </a
      ><a name="2773" href="Stlc.html#822" class="InductiveConstructor"
      >false</a
      ><a name="2778"
      > </a
      ><a name="2779" href="Stlc.html#837" class="InductiveConstructor Operator"
      >else</a
      ><a name="2783"
      > </a
      ><a name="2784" href="Stlc.html#808" class="InductiveConstructor"
      >true</a
      ><a name="2788" class="Symbol"
      >)</a
      ><a name="2789"
      >
  </a
      ><a name="2792" href="Stlc.html#2341" class="InductiveConstructor Operator"
      >&#10233;&#10216;</a
      ><a name="2794"
      > </a
      ><a name="2795" href="Stlc.html#1930" class="InductiveConstructor"
      >&#947;&#8658;&#8322;</a
      ><a name="2798"
      > </a
      ><a name="2799" href="Stlc.html#1142" class="InductiveConstructor"
      >value-&#955;</a
      ><a name="2806"
      > </a
      ><a name="2807" href="Stlc.html#1997" class="InductiveConstructor"
      >&#946;&#120121;&#8321;</a
      ><a name="2810"
      >  </a
      ><a name="2812" href="Stlc.html#2341" class="InductiveConstructor Operator"
      >&#10217;</a
      ><a name="2813"
      >
    </a
      ><a name="2818" href="Stlc.html#951" class="Function"
      >not</a
      ><a name="2821"
      > </a
      ><a name="2822" href="Stlc.html#781" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="2823"
      > </a
      ><a name="2824" href="Stlc.html#822" class="InductiveConstructor"
      >false</a
      ><a name="2829"
      >
  </a
      ><a name="2832" href="Stlc.html#2341" class="InductiveConstructor Operator"
      >&#10233;&#10216;</a
      ><a name="2834"
      > </a
      ><a name="2835" href="Stlc.html#1808" class="InductiveConstructor"
      >&#946;&#8658;</a
      ><a name="2837"
      > </a
      ><a name="2838" href="Stlc.html#1218" class="InductiveConstructor"
      >value-false</a
      ><a name="2849"
      > </a
      ><a name="2850" href="Stlc.html#2341" class="InductiveConstructor Operator"
      >&#10217;</a
      ><a name="2851"
      >
    </a
      ><a name="2856" href="Stlc.html#837" class="InductiveConstructor Operator"
      >if</a
      ><a name="2858"
      > </a
      ><a name="2859" href="Stlc.html#822" class="InductiveConstructor"
      >false</a
      ><a name="2864"
      > </a
      ><a name="2865" href="Stlc.html#837" class="InductiveConstructor Operator"
      >then</a
      ><a name="2869"
      > </a
      ><a name="2870" href="Stlc.html#822" class="InductiveConstructor"
      >false</a
      ><a name="2875"
      > </a
      ><a name="2876" href="Stlc.html#837" class="InductiveConstructor Operator"
      >else</a
      ><a name="2880"
      > </a
      ><a name="2881" href="Stlc.html#808" class="InductiveConstructor"
      >true</a
      ><a name="2885"
      >
  </a
      ><a name="2888" href="Stlc.html#2341" class="InductiveConstructor Operator"
      >&#10233;&#10216;</a
      ><a name="2890"
      > </a
      ><a name="2891" href="Stlc.html#2045" class="InductiveConstructor"
      >&#946;&#120121;&#8322;</a
      ><a name="2894"
      > </a
      ><a name="2895" href="Stlc.html#2341" class="InductiveConstructor Operator"
      >&#10217;</a
      ><a name="2896"
      >
    </a
      ><a name="2901" href="Stlc.html#808" class="InductiveConstructor"
      >true</a
      ><a name="2905"
      >
  </a
      ><a name="2908" href="Stlc.html#2321" class="InductiveConstructor Operator"
      >&#8718;</a
      >
{% endraw %}</pre>

Much of the above, though not all, can be filled in using C-c C-r and C-c C-s.



## Type rules

<pre class="Agda">{% raw %}
<a name="3032" href="Stlc.html#3032" class="Function"
      >Context</a
      ><a name="3039"
      > </a
      ><a name="3040" class="Symbol"
      >:</a
      ><a name="3041"
      > </a
      ><a name="3042" class="PrimitiveType"
      >Set</a
      ><a name="3045"
      >
</a
      ><a name="3046" href="Stlc.html#3032" class="Function"
      >Context</a
      ><a name="3053"
      > </a
      ><a name="3054" class="Symbol"
      >=</a
      ><a name="3055"
      > </a
      ><a name="3056" href="Maps.html#10132" class="Function"
      >PartialMap</a
      ><a name="3066"
      > </a
      ><a name="3067" href="Stlc.html#590" class="Datatype"
      >Type</a
      ><a name="3071"
      >

</a
      ><a name="3073" class="Keyword"
      >infix</a
      ><a name="3078"
      > </a
      ><a name="3079" class="Number"
      >10</a
      ><a name="3081"
      > </a
      ><a name="3082" href="Stlc.html#3094" class="Datatype Operator"
      >_&#8866;_&#8758;_</a
      ><a name="3087"
      >

</a
      ><a name="3089" class="Keyword"
      >data</a
      ><a name="3093"
      > </a
      ><a name="3094" href="Stlc.html#3094" class="Datatype Operator"
      >_&#8866;_&#8758;_</a
      ><a name="3099"
      > </a
      ><a name="3100" class="Symbol"
      >:</a
      ><a name="3101"
      > </a
      ><a name="3102" href="Stlc.html#3032" class="Function"
      >Context</a
      ><a name="3109"
      > </a
      ><a name="3110" class="Symbol"
      >&#8594;</a
      ><a name="3111"
      > </a
      ><a name="3112" href="Stlc.html#708" class="Datatype"
      >Term</a
      ><a name="3116"
      > </a
      ><a name="3117" class="Symbol"
      >&#8594;</a
      ><a name="3118"
      > </a
      ><a name="3119" href="Stlc.html#590" class="Datatype"
      >Type</a
      ><a name="3123"
      > </a
      ><a name="3124" class="Symbol"
      >&#8594;</a
      ><a name="3125"
      > </a
      ><a name="3126" class="PrimitiveType"
      >Set</a
      ><a name="3129"
      > </a
      ><a name="3130" class="Keyword"
      >where</a
      ><a name="3135"
      >
  </a
      ><a name="3138" href="Stlc.html#3138" class="InductiveConstructor"
      >Ax</a
      ><a name="3140"
      > </a
      ><a name="3141" class="Symbol"
      >:</a
      ><a name="3142"
      > </a
      ><a name="3143" class="Symbol"
      >&#8704;</a
      ><a name="3144"
      > </a
      ><a name="3145" class="Symbol"
      >{</a
      ><a name="3146" href="Stlc.html#3146" class="Bound"
      >&#915;</a
      ><a name="3147"
      > </a
      ><a name="3148" href="Stlc.html#3148" class="Bound"
      >x</a
      ><a name="3149"
      > </a
      ><a name="3150" href="Stlc.html#3150" class="Bound"
      >A</a
      ><a name="3151" class="Symbol"
      >}</a
      ><a name="3152"
      > </a
      ><a name="3153" class="Symbol"
      >&#8594;</a
      ><a name="3154"
      >
    </a
      ><a name="3159" href="Stlc.html#3146" class="Bound"
      >&#915;</a
      ><a name="3160"
      > </a
      ><a name="3161" href="Stlc.html#3148" class="Bound"
      >x</a
      ><a name="3162"
      > </a
      ><a name="3163" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="3164"
      > </a
      ><a name="3165" href="https://agda.github.io/agda-stdlib/Data.Maybe.Base.html#373" class="InductiveConstructor"
      >just</a
      ><a name="3169"
      > </a
      ><a name="3170" href="Stlc.html#3150" class="Bound"
      >A</a
      ><a name="3171"
      > </a
      ><a name="3172" class="Symbol"
      >&#8594;</a
      ><a name="3173"
      >
    </a
      ><a name="3178" href="Stlc.html#3146" class="Bound"
      >&#915;</a
      ><a name="3179"
      > </a
      ><a name="3180" href="Stlc.html#3094" class="Datatype Operator"
      >&#8866;</a
      ><a name="3181"
      > </a
      ><a name="3182" href="Stlc.html#727" class="InductiveConstructor"
      >var</a
      ><a name="3185"
      > </a
      ><a name="3186" href="Stlc.html#3148" class="Bound"
      >x</a
      ><a name="3187"
      > </a
      ><a name="3188" href="Stlc.html#3094" class="Datatype Operator"
      >&#8758;</a
      ><a name="3189"
      > </a
      ><a name="3190" href="Stlc.html#3150" class="Bound"
      >A</a
      ><a name="3191"
      >
  </a
      ><a name="3194" href="Stlc.html#3194" class="InductiveConstructor"
      >&#8658;-I</a
      ><a name="3197"
      > </a
      ><a name="3198" class="Symbol"
      >:</a
      ><a name="3199"
      > </a
      ><a name="3200" class="Symbol"
      >&#8704;</a
      ><a name="3201"
      > </a
      ><a name="3202" class="Symbol"
      >{</a
      ><a name="3203" href="Stlc.html#3203" class="Bound"
      >&#915;</a
      ><a name="3204"
      > </a
      ><a name="3205" href="Stlc.html#3205" class="Bound"
      >x</a
      ><a name="3206"
      > </a
      ><a name="3207" href="Stlc.html#3207" class="Bound"
      >N</a
      ><a name="3208"
      > </a
      ><a name="3209" href="Stlc.html#3209" class="Bound"
      >A</a
      ><a name="3210"
      > </a
      ><a name="3211" href="Stlc.html#3211" class="Bound"
      >B</a
      ><a name="3212" class="Symbol"
      >}</a
      ><a name="3213"
      > </a
      ><a name="3214" class="Symbol"
      >&#8594;</a
      ><a name="3215"
      >
    </a
      ><a name="3220" href="Stlc.html#3203" class="Bound"
      >&#915;</a
      ><a name="3221"
      > </a
      ><a name="3222" href="Maps.html#10368" class="Function Operator"
      >,</a
      ><a name="3223"
      > </a
      ><a name="3224" href="Stlc.html#3205" class="Bound"
      >x</a
      ><a name="3225"
      > </a
      ><a name="3226" href="Maps.html#10368" class="Function Operator"
      >&#8758;</a
      ><a name="3227"
      > </a
      ><a name="3228" href="Stlc.html#3209" class="Bound"
      >A</a
      ><a name="3229"
      > </a
      ><a name="3230" href="Stlc.html#3094" class="Datatype Operator"
      >&#8866;</a
      ><a name="3231"
      > </a
      ><a name="3232" href="Stlc.html#3207" class="Bound"
      >N</a
      ><a name="3233"
      > </a
      ><a name="3234" href="Stlc.html#3094" class="Datatype Operator"
      >&#8758;</a
      ><a name="3235"
      > </a
      ><a name="3236" href="Stlc.html#3211" class="Bound"
      >B</a
      ><a name="3237"
      > </a
      ><a name="3238" class="Symbol"
      >&#8594;</a
      ><a name="3239"
      >
    </a
      ><a name="3244" href="Stlc.html#3203" class="Bound"
      >&#915;</a
      ><a name="3245"
      > </a
      ><a name="3246" href="Stlc.html#3094" class="Datatype Operator"
      >&#8866;</a
      ><a name="3247"
      > </a
      ><a name="3248" href="Stlc.html#745" class="InductiveConstructor Operator"
      >&#955;[</a
      ><a name="3250"
      > </a
      ><a name="3251" href="Stlc.html#3205" class="Bound"
      >x</a
      ><a name="3252"
      > </a
      ><a name="3253" href="Stlc.html#745" class="InductiveConstructor Operator"
      >&#8758;</a
      ><a name="3254"
      > </a
      ><a name="3255" href="Stlc.html#3209" class="Bound"
      >A</a
      ><a name="3256"
      > </a
      ><a name="3257" href="Stlc.html#745" class="InductiveConstructor Operator"
      >]</a
      ><a name="3258"
      > </a
      ><a name="3259" href="Stlc.html#3207" class="Bound"
      >N</a
      ><a name="3260"
      > </a
      ><a name="3261" href="Stlc.html#3094" class="Datatype Operator"
      >&#8758;</a
      ><a name="3262"
      > </a
      ><a name="3263" href="Stlc.html#3209" class="Bound"
      >A</a
      ><a name="3264"
      > </a
      ><a name="3265" href="Stlc.html#620" class="InductiveConstructor Operator"
      >&#8658;</a
      ><a name="3266"
      > </a
      ><a name="3267" href="Stlc.html#3211" class="Bound"
      >B</a
      ><a name="3268"
      >
  </a
      ><a name="3271" href="Stlc.html#3271" class="InductiveConstructor"
      >&#8658;-E</a
      ><a name="3274"
      > </a
      ><a name="3275" class="Symbol"
      >:</a
      ><a name="3276"
      > </a
      ><a name="3277" class="Symbol"
      >&#8704;</a
      ><a name="3278"
      > </a
      ><a name="3279" class="Symbol"
      >{</a
      ><a name="3280" href="Stlc.html#3280" class="Bound"
      >&#915;</a
      ><a name="3281"
      > </a
      ><a name="3282" href="Stlc.html#3282" class="Bound"
      >L</a
      ><a name="3283"
      > </a
      ><a name="3284" href="Stlc.html#3284" class="Bound"
      >M</a
      ><a name="3285"
      > </a
      ><a name="3286" href="Stlc.html#3286" class="Bound"
      >A</a
      ><a name="3287"
      > </a
      ><a name="3288" href="Stlc.html#3288" class="Bound"
      >B</a
      ><a name="3289" class="Symbol"
      >}</a
      ><a name="3290"
      > </a
      ><a name="3291" class="Symbol"
      >&#8594;</a
      ><a name="3292"
      >
    </a
      ><a name="3297" href="Stlc.html#3280" class="Bound"
      >&#915;</a
      ><a name="3298"
      > </a
      ><a name="3299" href="Stlc.html#3094" class="Datatype Operator"
      >&#8866;</a
      ><a name="3300"
      > </a
      ><a name="3301" href="Stlc.html#3282" class="Bound"
      >L</a
      ><a name="3302"
      > </a
      ><a name="3303" href="Stlc.html#3094" class="Datatype Operator"
      >&#8758;</a
      ><a name="3304"
      > </a
      ><a name="3305" href="Stlc.html#3286" class="Bound"
      >A</a
      ><a name="3306"
      > </a
      ><a name="3307" href="Stlc.html#620" class="InductiveConstructor Operator"
      >&#8658;</a
      ><a name="3308"
      > </a
      ><a name="3309" href="Stlc.html#3288" class="Bound"
      >B</a
      ><a name="3310"
      > </a
      ><a name="3311" class="Symbol"
      >&#8594;</a
      ><a name="3312"
      >
    </a
      ><a name="3317" href="Stlc.html#3280" class="Bound"
      >&#915;</a
      ><a name="3318"
      > </a
      ><a name="3319" href="Stlc.html#3094" class="Datatype Operator"
      >&#8866;</a
      ><a name="3320"
      > </a
      ><a name="3321" href="Stlc.html#3284" class="Bound"
      >M</a
      ><a name="3322"
      > </a
      ><a name="3323" href="Stlc.html#3094" class="Datatype Operator"
      >&#8758;</a
      ><a name="3324"
      > </a
      ><a name="3325" href="Stlc.html#3286" class="Bound"
      >A</a
      ><a name="3326"
      > </a
      ><a name="3327" class="Symbol"
      >&#8594;</a
      ><a name="3328"
      >
    </a
      ><a name="3333" href="Stlc.html#3280" class="Bound"
      >&#915;</a
      ><a name="3334"
      > </a
      ><a name="3335" href="Stlc.html#3094" class="Datatype Operator"
      >&#8866;</a
      ><a name="3336"
      > </a
      ><a name="3337" href="Stlc.html#3282" class="Bound"
      >L</a
      ><a name="3338"
      > </a
      ><a name="3339" href="Stlc.html#781" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="3340"
      > </a
      ><a name="3341" href="Stlc.html#3284" class="Bound"
      >M</a
      ><a name="3342"
      > </a
      ><a name="3343" href="Stlc.html#3094" class="Datatype Operator"
      >&#8758;</a
      ><a name="3344"
      > </a
      ><a name="3345" href="Stlc.html#3288" class="Bound"
      >B</a
      ><a name="3346"
      >
  </a
      ><a name="3349" href="Stlc.html#3349" class="InductiveConstructor"
      >&#120121;-I&#8321;</a
      ><a name="3353"
      > </a
      ><a name="3354" class="Symbol"
      >:</a
      ><a name="3355"
      > </a
      ><a name="3356" class="Symbol"
      >&#8704;</a
      ><a name="3357"
      > </a
      ><a name="3358" class="Symbol"
      >{</a
      ><a name="3359" href="Stlc.html#3359" class="Bound"
      >&#915;</a
      ><a name="3360" class="Symbol"
      >}</a
      ><a name="3361"
      > </a
      ><a name="3362" class="Symbol"
      >&#8594;</a
      ><a name="3363"
      >
    </a
      ><a name="3368" href="Stlc.html#3359" class="Bound"
      >&#915;</a
      ><a name="3369"
      > </a
      ><a name="3370" href="Stlc.html#3094" class="Datatype Operator"
      >&#8866;</a
      ><a name="3371"
      > </a
      ><a name="3372" href="Stlc.html#808" class="InductiveConstructor"
      >true</a
      ><a name="3376"
      > </a
      ><a name="3377" href="Stlc.html#3094" class="Datatype Operator"
      >&#8758;</a
      ><a name="3378"
      > </a
      ><a name="3379" href="Stlc.html#609" class="InductiveConstructor"
      >&#120121;</a
      ><a name="3380"
      >
  </a
      ><a name="3383" href="Stlc.html#3383" class="InductiveConstructor"
      >&#120121;-I&#8322;</a
      ><a name="3387"
      > </a
      ><a name="3388" class="Symbol"
      >:</a
      ><a name="3389"
      > </a
      ><a name="3390" class="Symbol"
      >&#8704;</a
      ><a name="3391"
      > </a
      ><a name="3392" class="Symbol"
      >{</a
      ><a name="3393" href="Stlc.html#3393" class="Bound"
      >&#915;</a
      ><a name="3394" class="Symbol"
      >}</a
      ><a name="3395"
      > </a
      ><a name="3396" class="Symbol"
      >&#8594;</a
      ><a name="3397"
      >
    </a
      ><a name="3402" href="Stlc.html#3393" class="Bound"
      >&#915;</a
      ><a name="3403"
      > </a
      ><a name="3404" href="Stlc.html#3094" class="Datatype Operator"
      >&#8866;</a
      ><a name="3405"
      > </a
      ><a name="3406" href="Stlc.html#822" class="InductiveConstructor"
      >false</a
      ><a name="3411"
      > </a
      ><a name="3412" href="Stlc.html#3094" class="Datatype Operator"
      >&#8758;</a
      ><a name="3413"
      > </a
      ><a name="3414" href="Stlc.html#609" class="InductiveConstructor"
      >&#120121;</a
      ><a name="3415"
      >
  </a
      ><a name="3418" href="Stlc.html#3418" class="InductiveConstructor"
      >&#120121;-E</a
      ><a name="3421"
      > </a
      ><a name="3422" class="Symbol"
      >:</a
      ><a name="3423"
      > </a
      ><a name="3424" class="Symbol"
      >&#8704;</a
      ><a name="3425"
      > </a
      ><a name="3426" class="Symbol"
      >{</a
      ><a name="3427" href="Stlc.html#3427" class="Bound"
      >&#915;</a
      ><a name="3428"
      > </a
      ><a name="3429" href="Stlc.html#3429" class="Bound"
      >L</a
      ><a name="3430"
      > </a
      ><a name="3431" href="Stlc.html#3431" class="Bound"
      >M</a
      ><a name="3432"
      > </a
      ><a name="3433" href="Stlc.html#3433" class="Bound"
      >N</a
      ><a name="3434"
      > </a
      ><a name="3435" href="Stlc.html#3435" class="Bound"
      >A</a
      ><a name="3436" class="Symbol"
      >}</a
      ><a name="3437"
      > </a
      ><a name="3438" class="Symbol"
      >&#8594;</a
      ><a name="3439"
      >
    </a
      ><a name="3444" href="Stlc.html#3427" class="Bound"
      >&#915;</a
      ><a name="3445"
      > </a
      ><a name="3446" href="Stlc.html#3094" class="Datatype Operator"
      >&#8866;</a
      ><a name="3447"
      > </a
      ><a name="3448" href="Stlc.html#3429" class="Bound"
      >L</a
      ><a name="3449"
      > </a
      ><a name="3450" href="Stlc.html#3094" class="Datatype Operator"
      >&#8758;</a
      ><a name="3451"
      > </a
      ><a name="3452" href="Stlc.html#609" class="InductiveConstructor"
      >&#120121;</a
      ><a name="3453"
      > </a
      ><a name="3454" class="Symbol"
      >&#8594;</a
      ><a name="3455"
      >
    </a
      ><a name="3460" href="Stlc.html#3427" class="Bound"
      >&#915;</a
      ><a name="3461"
      > </a
      ><a name="3462" href="Stlc.html#3094" class="Datatype Operator"
      >&#8866;</a
      ><a name="3463"
      > </a
      ><a name="3464" href="Stlc.html#3431" class="Bound"
      >M</a
      ><a name="3465"
      > </a
      ><a name="3466" href="Stlc.html#3094" class="Datatype Operator"
      >&#8758;</a
      ><a name="3467"
      > </a
      ><a name="3468" href="Stlc.html#3435" class="Bound"
      >A</a
      ><a name="3469"
      > </a
      ><a name="3470" class="Symbol"
      >&#8594;</a
      ><a name="3471"
      >
    </a
      ><a name="3476" href="Stlc.html#3427" class="Bound"
      >&#915;</a
      ><a name="3477"
      > </a
      ><a name="3478" href="Stlc.html#3094" class="Datatype Operator"
      >&#8866;</a
      ><a name="3479"
      > </a
      ><a name="3480" href="Stlc.html#3433" class="Bound"
      >N</a
      ><a name="3481"
      > </a
      ><a name="3482" href="Stlc.html#3094" class="Datatype Operator"
      >&#8758;</a
      ><a name="3483"
      > </a
      ><a name="3484" href="Stlc.html#3435" class="Bound"
      >A</a
      ><a name="3485"
      > </a
      ><a name="3486" class="Symbol"
      >&#8594;</a
      ><a name="3487"
      >
    </a
      ><a name="3492" href="Stlc.html#3427" class="Bound"
      >&#915;</a
      ><a name="3493"
      > </a
      ><a name="3494" href="Stlc.html#3094" class="Datatype Operator"
      >&#8866;</a
      ><a name="3495"
      > </a
      ><a name="3496" href="Stlc.html#837" class="InductiveConstructor Operator"
      >if</a
      ><a name="3498"
      > </a
      ><a name="3499" href="Stlc.html#3429" class="Bound"
      >L</a
      ><a name="3500"
      > </a
      ><a name="3501" href="Stlc.html#837" class="InductiveConstructor Operator"
      >then</a
      ><a name="3505"
      > </a
      ><a name="3506" href="Stlc.html#3431" class="Bound"
      >M</a
      ><a name="3507"
      > </a
      ><a name="3508" href="Stlc.html#837" class="InductiveConstructor Operator"
      >else</a
      ><a name="3512"
      > </a
      ><a name="3513" href="Stlc.html#3433" class="Bound"
      >N</a
      ><a name="3514"
      > </a
      ><a name="3515" href="Stlc.html#3094" class="Datatype Operator"
      >&#8758;</a
      ><a name="3516"
      > </a
      ><a name="3517" href="Stlc.html#3435" class="Bound"
      >A</a
      >
{% endraw %}</pre>

## Example type derivations

<pre class="Agda">{% raw %}
<a name="3577" href="Stlc.html#3577" class="Function"
      >typing&#8321;</a
      ><a name="3584"
      > </a
      ><a name="3585" class="Symbol"
      >:</a
      ><a name="3586"
      > </a
      ><a name="3587" href="Maps.html#10265" class="Function"
      >&#8709;</a
      ><a name="3588"
      > </a
      ><a name="3589" href="Stlc.html#3094" class="Datatype Operator"
      >&#8866;</a
      ><a name="3590"
      > </a
      ><a name="3591" href="Stlc.html#951" class="Function"
      >not</a
      ><a name="3594"
      > </a
      ><a name="3595" href="Stlc.html#3094" class="Datatype Operator"
      >&#8758;</a
      ><a name="3596"
      > </a
      ><a name="3597" href="Stlc.html#609" class="InductiveConstructor"
      >&#120121;</a
      ><a name="3598"
      > </a
      ><a name="3599" href="Stlc.html#620" class="InductiveConstructor Operator"
      >&#8658;</a
      ><a name="3600"
      > </a
      ><a name="3601" href="Stlc.html#609" class="InductiveConstructor"
      >&#120121;</a
      ><a name="3602"
      >
</a
      ><a name="3603" href="Stlc.html#3577" class="Function"
      >typing&#8321;</a
      ><a name="3610"
      > </a
      ><a name="3611" class="Symbol"
      >=</a
      ><a name="3612"
      > </a
      ><a name="3613" href="Stlc.html#3194" class="InductiveConstructor"
      >&#8658;-I</a
      ><a name="3616"
      > </a
      ><a name="3617" class="Symbol"
      >(</a
      ><a name="3618" href="Stlc.html#3418" class="InductiveConstructor"
      >&#120121;-E</a
      ><a name="3621"
      > </a
      ><a name="3622" class="Symbol"
      >(</a
      ><a name="3623" href="Stlc.html#3138" class="InductiveConstructor"
      >Ax</a
      ><a name="3625"
      > </a
      ><a name="3626" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="3630" class="Symbol"
      >)</a
      ><a name="3631"
      > </a
      ><a name="3632" href="Stlc.html#3383" class="InductiveConstructor"
      >&#120121;-I&#8322;</a
      ><a name="3636"
      > </a
      ><a name="3637" href="Stlc.html#3349" class="InductiveConstructor"
      >&#120121;-I&#8321;</a
      ><a name="3641" class="Symbol"
      >)</a
      ><a name="3642"
      >

</a
      ><a name="3644" href="Stlc.html#3644" class="Function"
      >typing&#8322;</a
      ><a name="3651"
      > </a
      ><a name="3652" class="Symbol"
      >:</a
      ><a name="3653"
      > </a
      ><a name="3654" href="Maps.html#10265" class="Function"
      >&#8709;</a
      ><a name="3655"
      > </a
      ><a name="3656" href="Stlc.html#3094" class="Datatype Operator"
      >&#8866;</a
      ><a name="3657"
      > </a
      ><a name="3658" href="Stlc.html#955" class="Function"
      >two</a
      ><a name="3661"
      > </a
      ><a name="3662" href="Stlc.html#3094" class="Datatype Operator"
      >&#8758;</a
      ><a name="3663"
      > </a
      ><a name="3664" class="Symbol"
      >(</a
      ><a name="3665" href="Stlc.html#609" class="InductiveConstructor"
      >&#120121;</a
      ><a name="3666"
      > </a
      ><a name="3667" href="Stlc.html#620" class="InductiveConstructor Operator"
      >&#8658;</a
      ><a name="3668"
      > </a
      ><a name="3669" href="Stlc.html#609" class="InductiveConstructor"
      >&#120121;</a
      ><a name="3670" class="Symbol"
      >)</a
      ><a name="3671"
      > </a
      ><a name="3672" href="Stlc.html#620" class="InductiveConstructor Operator"
      >&#8658;</a
      ><a name="3673"
      > </a
      ><a name="3674" href="Stlc.html#609" class="InductiveConstructor"
      >&#120121;</a
      ><a name="3675"
      > </a
      ><a name="3676" href="Stlc.html#620" class="InductiveConstructor Operator"
      >&#8658;</a
      ><a name="3677"
      > </a
      ><a name="3678" href="Stlc.html#609" class="InductiveConstructor"
      >&#120121;</a
      ><a name="3679"
      >
</a
      ><a name="3680" href="Stlc.html#3644" class="Function"
      >typing&#8322;</a
      ><a name="3687"
      > </a
      ><a name="3688" class="Symbol"
      >=</a
      ><a name="3689"
      > </a
      ><a name="3690" href="Stlc.html#3194" class="InductiveConstructor"
      >&#8658;-I</a
      ><a name="3693"
      > </a
      ><a name="3694" class="Symbol"
      >(</a
      ><a name="3695" href="Stlc.html#3194" class="InductiveConstructor"
      >&#8658;-I</a
      ><a name="3698"
      > </a
      ><a name="3699" class="Symbol"
      >(</a
      ><a name="3700" href="Stlc.html#3271" class="InductiveConstructor"
      >&#8658;-E</a
      ><a name="3703"
      > </a
      ><a name="3704" class="Symbol"
      >(</a
      ><a name="3705" href="Stlc.html#3138" class="InductiveConstructor"
      >Ax</a
      ><a name="3707"
      > </a
      ><a name="3708" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="3712" class="Symbol"
      >)</a
      ><a name="3713"
      > </a
      ><a name="3714" class="Symbol"
      >(</a
      ><a name="3715" href="Stlc.html#3271" class="InductiveConstructor"
      >&#8658;-E</a
      ><a name="3718"
      > </a
      ><a name="3719" class="Symbol"
      >(</a
      ><a name="3720" href="Stlc.html#3138" class="InductiveConstructor"
      >Ax</a
      ><a name="3722"
      > </a
      ><a name="3723" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="3727" class="Symbol"
      >)</a
      ><a name="3728"
      > </a
      ><a name="3729" class="Symbol"
      >(</a
      ><a name="3730" href="Stlc.html#3138" class="InductiveConstructor"
      >Ax</a
      ><a name="3732"
      > </a
      ><a name="3733" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="3737" class="Symbol"
      >))))</a
      >
{% endraw %}</pre>

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
    ?0 : ∅ , x ∶ 𝔹 ⊢ if var x then false else true ∶ 𝔹

Again we fill in the hole by typing C-c C-r. Agda observes that the
outermost term is now `if_then_else_`, which is typed using `𝔹-E`. The
`𝔹-E` rule in turn takes three arguments, which Agda leaves as holes.

    typing₁ = ⇒-I (𝔹-E { }0 { }1 { }2)
    ?0 : ∅ , x ∶ 𝔹 ⊢ var x ∶
    ?1 : ∅ , x ∶ 𝔹 ⊢ false ∶ 𝔹
    ?2 : ∅ , x ∶ 𝔹 ⊢ true ∶ 𝔹

Again we fill in the three holes by typing C-c C-r in each. Agda observes
that `var x`, `false`, and `true` are typed using `Ax`, `𝔹-I₂`, and
`𝔹-I₁` respectively. The `Ax` rule in turn takes an argument, to show
that `(∅ , x ∶ 𝔹) x = just 𝔹`, which can in turn be specified with a
hole. After filling in all holes, the term is as above.

The entire process can be automated using Agsy, invoked with C-c C-a.


