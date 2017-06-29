---
title     : "Stlc: The Simply Typed Lambda-Calculus"
layout    : page
permalink : /Stlc
---

This chapter defines the simply-typed lambda calculus.

## Imports
<pre class="Agda">{% raw %}
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
      ><a name="215" href="Maps.html#10226" class="Function"
      >PartialMap</a
      ><a name="225" class="Symbol"
      >;</a
      ><a name="226"
      > </a
      ><a name="227" class="Keyword"
      >module</a
      ><a name="233"
      > </a
      ><a name="234" href="Maps.html#10315" class="Module"
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
      ><a name="251" href="Maps.html#10315" class="Module"
      >PartialMap</a
      ><a name="261"
      > </a
      ><a name="262" class="Keyword"
      >using</a
      ><a name="267"
      > </a
      ><a name="268" class="Symbol"
      >(</a
      ><a name="269" href="Maps.html#10359" class="Function"
      >&#8709;</a
      ><a name="270" class="Symbol"
      >)</a
      ><a name="271"
      > </a
      ><a name="272" class="Keyword"
      >renaming</a
      ><a name="280"
      > </a
      ><a name="281" class="Symbol"
      >(</a
      ><a name="282" href="Maps.html#10462" class="Function Operator"
      >_,_&#8614;_</a
      ><a name="287"
      > </a
      ><a name="288" class="Symbol"
      >to</a
      ><a name="290"
      > </a
      ><a name="291" href="Maps.html#10462" class="Function Operator"
      >_,_&#8758;_</a
      ><a name="296" class="Symbol"
      >)</a
      ><a name="297"
      >
</a
      ><a name="298" class="Keyword"
      >open</a
      ><a name="302"
      > </a
      ><a name="303" class="Keyword"
      >import</a
      ><a name="309"
      > </a
      ><a name="310" href="https://agda.github.io/agda-stdlib/Data.String.html#1" class="Module"
      >Data.String</a
      ><a name="321"
      > </a
      ><a name="322" class="Keyword"
      >using</a
      ><a name="327"
      > </a
      ><a name="328" class="Symbol"
      >(</a
      ><a name="329" href="https://agda.github.io/agda-stdlib/Agda.Builtin.String.html#165" class="Postulate"
      >String</a
      ><a name="335" class="Symbol"
      >)</a
      ><a name="336"
      >
</a
      ><a name="337" class="Keyword"
      >open</a
      ><a name="341"
      > </a
      ><a name="342" class="Keyword"
      >import</a
      ><a name="348"
      > </a
      ><a name="349" href="https://agda.github.io/agda-stdlib/Data.Maybe.html#1" class="Module"
      >Data.Maybe</a
      ><a name="359"
      > </a
      ><a name="360" class="Keyword"
      >using</a
      ><a name="365"
      > </a
      ><a name="366" class="Symbol"
      >(</a
      ><a name="367" href="https://agda.github.io/agda-stdlib/Data.Maybe.Base.html#335" class="Datatype"
      >Maybe</a
      ><a name="372" class="Symbol"
      >;</a
      ><a name="373"
      > </a
      ><a name="374" href="https://agda.github.io/agda-stdlib/Data.Maybe.html#1527" class="InductiveConstructor"
      >just</a
      ><a name="378" class="Symbol"
      >;</a
      ><a name="379"
      > </a
      ><a name="380" href="https://agda.github.io/agda-stdlib/Data.Maybe.html#1588" class="InductiveConstructor"
      >nothing</a
      ><a name="387" class="Symbol"
      >)</a
      ><a name="388"
      >
</a
      ><a name="389" class="Keyword"
      >open</a
      ><a name="393"
      > </a
      ><a name="394" class="Keyword"
      >import</a
      ><a name="400"
      > </a
      ><a name="401" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#1" class="Module"
      >Relation.Nullary</a
      ><a name="417"
      > </a
      ><a name="418" class="Keyword"
      >using</a
      ><a name="423"
      > </a
      ><a name="424" class="Symbol"
      >(</a
      ><a name="425" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#484" class="Datatype"
      >Dec</a
      ><a name="428" class="Symbol"
      >;</a
      ><a name="429"
      > </a
      ><a name="430" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#520" class="InductiveConstructor"
      >yes</a
      ><a name="433" class="Symbol"
      >;</a
      ><a name="434"
      > </a
      ><a name="435" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#547" class="InductiveConstructor"
      >no</a
      ><a name="437" class="Symbol"
      >)</a
      ><a name="438"
      >
</a
      ><a name="439" class="Keyword"
      >open</a
      ><a name="443"
      > </a
      ><a name="444" class="Keyword"
      >import</a
      ><a name="450"
      > </a
      ><a name="451" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#1" class="Module"
      >Relation.Binary.PropositionalEquality</a
      ><a name="488"
      > </a
      ><a name="489" class="Keyword"
      >using</a
      ><a name="494"
      > </a
      ><a name="495" class="Symbol"
      >(</a
      ><a name="496" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >_&#8801;_</a
      ><a name="499" class="Symbol"
      >;</a
      ><a name="500"
      > </a
      ><a name="501" href="https://agda.github.io/agda-stdlib/Relation.Binary.Core.html#4493" class="Function Operator"
      >_&#8802;_</a
      ><a name="504" class="Symbol"
      >;</a
      ><a name="505"
      > </a
      ><a name="506" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="510" class="Symbol"
      >)</a
      >
{% endraw %}</pre>


## Syntax

Syntax of types and terms.

<pre class="Agda">{% raw %}
<a name="577" class="Keyword"
      >infixr</a
      ><a name="583"
      > </a
      ><a name="584" class="Number"
      >20</a
      ><a name="586"
      > </a
      ><a name="587" href="Stlc.html#627" class="InductiveConstructor Operator"
      >_&#8658;_</a
      ><a name="590"
      >

</a
      ><a name="592" class="Keyword"
      >data</a
      ><a name="596"
      > </a
      ><a name="597" href="Stlc.html#597" class="Datatype"
      >Type</a
      ><a name="601"
      > </a
      ><a name="602" class="Symbol"
      >:</a
      ><a name="603"
      > </a
      ><a name="604" class="PrimitiveType"
      >Set</a
      ><a name="607"
      > </a
      ><a name="608" class="Keyword"
      >where</a
      ><a name="613"
      >
  </a
      ><a name="616" href="Stlc.html#616" class="InductiveConstructor"
      >&#120121;</a
      ><a name="617"
      > </a
      ><a name="618" class="Symbol"
      >:</a
      ><a name="619"
      > </a
      ><a name="620" href="Stlc.html#597" class="Datatype"
      >Type</a
      ><a name="624"
      >
  </a
      ><a name="627" href="Stlc.html#627" class="InductiveConstructor Operator"
      >_&#8658;_</a
      ><a name="630"
      > </a
      ><a name="631" class="Symbol"
      >:</a
      ><a name="632"
      > </a
      ><a name="633" href="Stlc.html#597" class="Datatype"
      >Type</a
      ><a name="637"
      > </a
      ><a name="638" class="Symbol"
      >&#8594;</a
      ><a name="639"
      > </a
      ><a name="640" href="Stlc.html#597" class="Datatype"
      >Type</a
      ><a name="644"
      > </a
      ><a name="645" class="Symbol"
      >&#8594;</a
      ><a name="646"
      > </a
      ><a name="647" href="Stlc.html#597" class="Datatype"
      >Type</a
      ><a name="651"
      >

</a
      ><a name="653" class="Keyword"
      >infixl</a
      ><a name="659"
      > </a
      ><a name="660" class="Number"
      >20</a
      ><a name="662"
      > </a
      ><a name="663" href="Stlc.html#788" class="InductiveConstructor Operator"
      >_&#183;_</a
      ><a name="666"
      >
</a
      ><a name="667" class="Keyword"
      >infix</a
      ><a name="672"
      >  </a
      ><a name="674" class="Number"
      >15</a
      ><a name="676"
      > </a
      ><a name="677" href="Stlc.html#752" class="InductiveConstructor Operator"
      >&#955;[_&#8758;_]_</a
      ><a name="684"
      >
</a
      ><a name="685" class="Keyword"
      >infix</a
      ><a name="690"
      >  </a
      ><a name="692" class="Number"
      >15</a
      ><a name="694"
      > </a
      ><a name="695" href="Stlc.html#844" class="InductiveConstructor Operator"
      >if_then_else_</a
      ><a name="708"
      >

</a
      ><a name="710" class="Keyword"
      >data</a
      ><a name="714"
      > </a
      ><a name="715" href="Stlc.html#715" class="Datatype"
      >Term</a
      ><a name="719"
      > </a
      ><a name="720" class="Symbol"
      >:</a
      ><a name="721"
      > </a
      ><a name="722" class="PrimitiveType"
      >Set</a
      ><a name="725"
      > </a
      ><a name="726" class="Keyword"
      >where</a
      ><a name="731"
      >
  </a
      ><a name="734" href="Stlc.html#734" class="InductiveConstructor"
      >var</a
      ><a name="737"
      > </a
      ><a name="738" class="Symbol"
      >:</a
      ><a name="739"
      > </a
      ><a name="740" href="Maps.html#2215" class="Datatype"
      >Id</a
      ><a name="742"
      > </a
      ><a name="743" class="Symbol"
      >&#8594;</a
      ><a name="744"
      > </a
      ><a name="745" href="Stlc.html#715" class="Datatype"
      >Term</a
      ><a name="749"
      >
  </a
      ><a name="752" href="Stlc.html#752" class="InductiveConstructor Operator"
      >&#955;[_&#8758;_]_</a
      ><a name="759"
      > </a
      ><a name="760" class="Symbol"
      >:</a
      ><a name="761"
      > </a
      ><a name="762" href="Maps.html#2215" class="Datatype"
      >Id</a
      ><a name="764"
      > </a
      ><a name="765" class="Symbol"
      >&#8594;</a
      ><a name="766"
      > </a
      ><a name="767" href="Stlc.html#597" class="Datatype"
      >Type</a
      ><a name="771"
      > </a
      ><a name="772" class="Symbol"
      >&#8594;</a
      ><a name="773"
      > </a
      ><a name="774" href="Stlc.html#715" class="Datatype"
      >Term</a
      ><a name="778"
      > </a
      ><a name="779" class="Symbol"
      >&#8594;</a
      ><a name="780"
      > </a
      ><a name="781" href="Stlc.html#715" class="Datatype"
      >Term</a
      ><a name="785"
      >
  </a
      ><a name="788" href="Stlc.html#788" class="InductiveConstructor Operator"
      >_&#183;_</a
      ><a name="791"
      > </a
      ><a name="792" class="Symbol"
      >:</a
      ><a name="793"
      > </a
      ><a name="794" href="Stlc.html#715" class="Datatype"
      >Term</a
      ><a name="798"
      > </a
      ><a name="799" class="Symbol"
      >&#8594;</a
      ><a name="800"
      > </a
      ><a name="801" href="Stlc.html#715" class="Datatype"
      >Term</a
      ><a name="805"
      > </a
      ><a name="806" class="Symbol"
      >&#8594;</a
      ><a name="807"
      > </a
      ><a name="808" href="Stlc.html#715" class="Datatype"
      >Term</a
      ><a name="812"
      >
  </a
      ><a name="815" href="Stlc.html#815" class="InductiveConstructor"
      >true</a
      ><a name="819"
      > </a
      ><a name="820" class="Symbol"
      >:</a
      ><a name="821"
      > </a
      ><a name="822" href="Stlc.html#715" class="Datatype"
      >Term</a
      ><a name="826"
      >
  </a
      ><a name="829" href="Stlc.html#829" class="InductiveConstructor"
      >false</a
      ><a name="834"
      > </a
      ><a name="835" class="Symbol"
      >:</a
      ><a name="836"
      > </a
      ><a name="837" href="Stlc.html#715" class="Datatype"
      >Term</a
      ><a name="841"
      >
  </a
      ><a name="844" href="Stlc.html#844" class="InductiveConstructor Operator"
      >if_then_else_</a
      ><a name="857"
      > </a
      ><a name="858" class="Symbol"
      >:</a
      ><a name="859"
      > </a
      ><a name="860" href="Stlc.html#715" class="Datatype"
      >Term</a
      ><a name="864"
      > </a
      ><a name="865" class="Symbol"
      >&#8594;</a
      ><a name="866"
      > </a
      ><a name="867" href="Stlc.html#715" class="Datatype"
      >Term</a
      ><a name="871"
      > </a
      ><a name="872" class="Symbol"
      >&#8594;</a
      ><a name="873"
      > </a
      ><a name="874" href="Stlc.html#715" class="Datatype"
      >Term</a
      ><a name="878"
      > </a
      ><a name="879" class="Symbol"
      >&#8594;</a
      ><a name="880"
      > </a
      ><a name="881" href="Stlc.html#715" class="Datatype"
      >Term</a
      >
{% endraw %}</pre>

Example terms.
<pre class="Agda">{% raw %}
<a name="926" href="Stlc.html#926" class="Function"
      >f</a
      ><a name="927"
      > </a
      ><a name="928" href="Stlc.html#928" class="Function"
      >x</a
      ><a name="929"
      > </a
      ><a name="930" class="Symbol"
      >:</a
      ><a name="931"
      > </a
      ><a name="932" href="Maps.html#2215" class="Datatype"
      >Id</a
      ><a name="934"
      >
</a
      ><a name="935" href="Stlc.html#926" class="Function"
      >f</a
      ><a name="936"
      >  </a
      ><a name="938" class="Symbol"
      >=</a
      ><a name="939"
      >  </a
      ><a name="941" href="Maps.html#2232" class="InductiveConstructor"
      >id</a
      ><a name="943"
      > </a
      ><a name="944" class="String"
      >&quot;f&quot;</a
      ><a name="947"
      >
</a
      ><a name="948" href="Stlc.html#928" class="Function"
      >x</a
      ><a name="949"
      >  </a
      ><a name="951" class="Symbol"
      >=</a
      ><a name="952"
      >  </a
      ><a name="954" href="Maps.html#2232" class="InductiveConstructor"
      >id</a
      ><a name="956"
      > </a
      ><a name="957" class="String"
      >&quot;x&quot;</a
      ><a name="960"
      >

</a
      ><a name="962" href="Stlc.html#962" class="Function"
      >not</a
      ><a name="965"
      > </a
      ><a name="966" href="Stlc.html#966" class="Function"
      >two</a
      ><a name="969"
      > </a
      ><a name="970" class="Symbol"
      >:</a
      ><a name="971"
      > </a
      ><a name="972" href="Stlc.html#715" class="Datatype"
      >Term</a
      ><a name="976"
      > 
</a
      ><a name="978" href="Stlc.html#962" class="Function"
      >not</a
      ><a name="981"
      > </a
      ><a name="982" class="Symbol"
      >=</a
      ><a name="983"
      >  </a
      ><a name="985" href="Stlc.html#752" class="InductiveConstructor Operator"
      >&#955;[</a
      ><a name="987"
      > </a
      ><a name="988" href="Stlc.html#928" class="Function"
      >x</a
      ><a name="989"
      > </a
      ><a name="990" href="Stlc.html#752" class="InductiveConstructor Operator"
      >&#8758;</a
      ><a name="991"
      > </a
      ><a name="992" href="Stlc.html#616" class="InductiveConstructor"
      >&#120121;</a
      ><a name="993"
      > </a
      ><a name="994" href="Stlc.html#752" class="InductiveConstructor Operator"
      >]</a
      ><a name="995"
      > </a
      ><a name="996" class="Symbol"
      >(</a
      ><a name="997" href="Stlc.html#844" class="InductiveConstructor Operator"
      >if</a
      ><a name="999"
      > </a
      ><a name="1000" href="Stlc.html#734" class="InductiveConstructor"
      >var</a
      ><a name="1003"
      > </a
      ><a name="1004" href="Stlc.html#928" class="Function"
      >x</a
      ><a name="1005"
      > </a
      ><a name="1006" href="Stlc.html#844" class="InductiveConstructor Operator"
      >then</a
      ><a name="1010"
      > </a
      ><a name="1011" href="Stlc.html#829" class="InductiveConstructor"
      >false</a
      ><a name="1016"
      > </a
      ><a name="1017" href="Stlc.html#844" class="InductiveConstructor Operator"
      >else</a
      ><a name="1021"
      > </a
      ><a name="1022" href="Stlc.html#815" class="InductiveConstructor"
      >true</a
      ><a name="1026" class="Symbol"
      >)</a
      ><a name="1027"
      >
</a
      ><a name="1028" href="Stlc.html#966" class="Function"
      >two</a
      ><a name="1031"
      > </a
      ><a name="1032" class="Symbol"
      >=</a
      ><a name="1033"
      >  </a
      ><a name="1035" href="Stlc.html#752" class="InductiveConstructor Operator"
      >&#955;[</a
      ><a name="1037"
      > </a
      ><a name="1038" href="Stlc.html#926" class="Function"
      >f</a
      ><a name="1039"
      > </a
      ><a name="1040" href="Stlc.html#752" class="InductiveConstructor Operator"
      >&#8758;</a
      ><a name="1041"
      > </a
      ><a name="1042" href="Stlc.html#616" class="InductiveConstructor"
      >&#120121;</a
      ><a name="1043"
      > </a
      ><a name="1044" href="Stlc.html#627" class="InductiveConstructor Operator"
      >&#8658;</a
      ><a name="1045"
      > </a
      ><a name="1046" href="Stlc.html#616" class="InductiveConstructor"
      >&#120121;</a
      ><a name="1047"
      > </a
      ><a name="1048" href="Stlc.html#752" class="InductiveConstructor Operator"
      >]</a
      ><a name="1049"
      > </a
      ><a name="1050" href="Stlc.html#752" class="InductiveConstructor Operator"
      >&#955;[</a
      ><a name="1052"
      > </a
      ><a name="1053" href="Stlc.html#928" class="Function"
      >x</a
      ><a name="1054"
      > </a
      ><a name="1055" href="Stlc.html#752" class="InductiveConstructor Operator"
      >&#8758;</a
      ><a name="1056"
      > </a
      ><a name="1057" href="Stlc.html#616" class="InductiveConstructor"
      >&#120121;</a
      ><a name="1058"
      > </a
      ><a name="1059" href="Stlc.html#752" class="InductiveConstructor Operator"
      >]</a
      ><a name="1060"
      > </a
      ><a name="1061" href="Stlc.html#734" class="InductiveConstructor"
      >var</a
      ><a name="1064"
      > </a
      ><a name="1065" href="Stlc.html#926" class="Function"
      >f</a
      ><a name="1066"
      > </a
      ><a name="1067" href="Stlc.html#788" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="1068"
      > </a
      ><a name="1069" class="Symbol"
      >(</a
      ><a name="1070" href="Stlc.html#734" class="InductiveConstructor"
      >var</a
      ><a name="1073"
      > </a
      ><a name="1074" href="Stlc.html#926" class="Function"
      >f</a
      ><a name="1075"
      > </a
      ><a name="1076" href="Stlc.html#788" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="1077"
      > </a
      ><a name="1078" href="Stlc.html#734" class="InductiveConstructor"
      >var</a
      ><a name="1081"
      > </a
      ><a name="1082" href="Stlc.html#928" class="Function"
      >x</a
      ><a name="1083" class="Symbol"
      >)</a
      >
{% endraw %}</pre>

## Values

<pre class="Agda">{% raw %}
<a name="1121" class="Keyword"
      >data</a
      ><a name="1125"
      > </a
      ><a name="1126" href="Stlc.html#1126" class="Datatype"
      >Value</a
      ><a name="1131"
      > </a
      ><a name="1132" class="Symbol"
      >:</a
      ><a name="1133"
      > </a
      ><a name="1134" href="Stlc.html#715" class="Datatype"
      >Term</a
      ><a name="1138"
      > </a
      ><a name="1139" class="Symbol"
      >&#8594;</a
      ><a name="1140"
      > </a
      ><a name="1141" class="PrimitiveType"
      >Set</a
      ><a name="1144"
      > </a
      ><a name="1145" class="Keyword"
      >where</a
      ><a name="1150"
      >
  </a
      ><a name="1153" href="Stlc.html#1153" class="InductiveConstructor"
      >value-&#955;</a
      ><a name="1160"
      >     </a
      ><a name="1165" class="Symbol"
      >:</a
      ><a name="1166"
      > </a
      ><a name="1167" class="Symbol"
      >&#8704;</a
      ><a name="1168"
      > </a
      ><a name="1169" class="Symbol"
      >{</a
      ><a name="1170" href="Stlc.html#1170" class="Bound"
      >x</a
      ><a name="1171"
      > </a
      ><a name="1172" href="Stlc.html#1172" class="Bound"
      >A</a
      ><a name="1173"
      > </a
      ><a name="1174" href="Stlc.html#1174" class="Bound"
      >N</a
      ><a name="1175" class="Symbol"
      >}</a
      ><a name="1176"
      > </a
      ><a name="1177" class="Symbol"
      >&#8594;</a
      ><a name="1178"
      > </a
      ><a name="1179" href="Stlc.html#1126" class="Datatype"
      >Value</a
      ><a name="1184"
      > </a
      ><a name="1185" class="Symbol"
      >(</a
      ><a name="1186" href="Stlc.html#752" class="InductiveConstructor Operator"
      >&#955;[</a
      ><a name="1188"
      > </a
      ><a name="1189" href="Stlc.html#1170" class="Bound"
      >x</a
      ><a name="1190"
      > </a
      ><a name="1191" href="Stlc.html#752" class="InductiveConstructor Operator"
      >&#8758;</a
      ><a name="1192"
      > </a
      ><a name="1193" href="Stlc.html#1172" class="Bound"
      >A</a
      ><a name="1194"
      > </a
      ><a name="1195" href="Stlc.html#752" class="InductiveConstructor Operator"
      >]</a
      ><a name="1196"
      > </a
      ><a name="1197" href="Stlc.html#1174" class="Bound"
      >N</a
      ><a name="1198" class="Symbol"
      >)</a
      ><a name="1199"
      >
  </a
      ><a name="1202" href="Stlc.html#1202" class="InductiveConstructor"
      >value-true</a
      ><a name="1212"
      >  </a
      ><a name="1214" class="Symbol"
      >:</a
      ><a name="1215"
      > </a
      ><a name="1216" href="Stlc.html#1126" class="Datatype"
      >Value</a
      ><a name="1221"
      > </a
      ><a name="1222" href="Stlc.html#815" class="InductiveConstructor"
      >true</a
      ><a name="1226"
      >
  </a
      ><a name="1229" href="Stlc.html#1229" class="InductiveConstructor"
      >value-false</a
      ><a name="1240"
      > </a
      ><a name="1241" class="Symbol"
      >:</a
      ><a name="1242"
      > </a
      ><a name="1243" href="Stlc.html#1126" class="Datatype"
      >Value</a
      ><a name="1248"
      > </a
      ><a name="1249" href="Stlc.html#829" class="InductiveConstructor"
      >false</a
      >
{% endraw %}</pre>

## Substitution

<pre class="Agda">{% raw %}
<a name="1297" href="Stlc.html#1297" class="Function Operator"
      >_[_&#8758;=_]</a
      ><a name="1304"
      > </a
      ><a name="1305" class="Symbol"
      >:</a
      ><a name="1306"
      > </a
      ><a name="1307" href="Stlc.html#715" class="Datatype"
      >Term</a
      ><a name="1311"
      > </a
      ><a name="1312" class="Symbol"
      >&#8594;</a
      ><a name="1313"
      > </a
      ><a name="1314" href="Maps.html#2215" class="Datatype"
      >Id</a
      ><a name="1316"
      > </a
      ><a name="1317" class="Symbol"
      >&#8594;</a
      ><a name="1318"
      > </a
      ><a name="1319" href="Stlc.html#715" class="Datatype"
      >Term</a
      ><a name="1323"
      > </a
      ><a name="1324" class="Symbol"
      >&#8594;</a
      ><a name="1325"
      > </a
      ><a name="1326" href="Stlc.html#715" class="Datatype"
      >Term</a
      ><a name="1330"
      >
</a
      ><a name="1331" class="Symbol"
      >(</a
      ><a name="1332" href="Stlc.html#734" class="InductiveConstructor"
      >var</a
      ><a name="1335"
      > </a
      ><a name="1336" href="Stlc.html#1336" class="Bound"
      >x&#8242;</a
      ><a name="1338" class="Symbol"
      >)</a
      ><a name="1339"
      > </a
      ><a name="1340" href="Stlc.html#1297" class="Function Operator"
      >[</a
      ><a name="1341"
      > </a
      ><a name="1342" href="Stlc.html#1342" class="Bound"
      >x</a
      ><a name="1343"
      > </a
      ><a name="1344" href="Stlc.html#1297" class="Function Operator"
      >&#8758;=</a
      ><a name="1346"
      > </a
      ><a name="1347" href="Stlc.html#1347" class="Bound"
      >V</a
      ><a name="1348"
      > </a
      ><a name="1349" href="Stlc.html#1297" class="Function Operator"
      >]</a
      ><a name="1350"
      > </a
      ><a name="1351" class="Keyword"
      >with</a
      ><a name="1355"
      > </a
      ><a name="1356" href="Stlc.html#1342" class="Bound"
      >x</a
      ><a name="1357"
      > </a
      ><a name="1358" href="Maps.html#2558" class="Function Operator"
      >&#8799;</a
      ><a name="1359"
      > </a
      ><a name="1360" href="Stlc.html#1336" class="Bound"
      >x&#8242;</a
      ><a name="1362"
      >
</a
      ><a name="1363" class="Symbol"
      >...</a
      ><a name="1366"
      > </a
      ><a name="1367" class="Symbol"
      >|</a
      ><a name="1368"
      > </a
      ><a name="1369" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#520" class="InductiveConstructor"
      >yes</a
      ><a name="1372"
      > </a
      ><a name="1373" class="Symbol"
      >_</a
      ><a name="1374"
      > </a
      ><a name="1375" class="Symbol"
      >=</a
      ><a name="1376"
      > </a
      ><a name="1377" href="Stlc.html#1347" class="Bound"
      >V</a
      ><a name="1378"
      >
</a
      ><a name="1379" class="Symbol"
      >...</a
      ><a name="1382"
      > </a
      ><a name="1383" class="Symbol"
      >|</a
      ><a name="1384"
      > </a
      ><a name="1385" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#547" class="InductiveConstructor"
      >no</a
      ><a name="1387"
      >  </a
      ><a name="1389" class="Symbol"
      >_</a
      ><a name="1390"
      > </a
      ><a name="1391" class="Symbol"
      >=</a
      ><a name="1392"
      > </a
      ><a name="1393" href="Stlc.html#734" class="InductiveConstructor"
      >var</a
      ><a name="1396"
      > </a
      ><a name="1397" href="Stlc.html#1336" class="Bound"
      >x&#8242;</a
      ><a name="1399"
      >
</a
      ><a name="1400" class="Symbol"
      >(</a
      ><a name="1401" href="Stlc.html#752" class="InductiveConstructor Operator"
      >&#955;[</a
      ><a name="1403"
      > </a
      ><a name="1404" href="Stlc.html#1404" class="Bound"
      >x&#8242;</a
      ><a name="1406"
      > </a
      ><a name="1407" href="Stlc.html#752" class="InductiveConstructor Operator"
      >&#8758;</a
      ><a name="1408"
      > </a
      ><a name="1409" href="Stlc.html#1409" class="Bound"
      >A&#8242;</a
      ><a name="1411"
      > </a
      ><a name="1412" href="Stlc.html#752" class="InductiveConstructor Operator"
      >]</a
      ><a name="1413"
      > </a
      ><a name="1414" href="Stlc.html#1414" class="Bound"
      >N&#8242;</a
      ><a name="1416" class="Symbol"
      >)</a
      ><a name="1417"
      > </a
      ><a name="1418" href="Stlc.html#1297" class="Function Operator"
      >[</a
      ><a name="1419"
      > </a
      ><a name="1420" href="Stlc.html#1420" class="Bound"
      >x</a
      ><a name="1421"
      > </a
      ><a name="1422" href="Stlc.html#1297" class="Function Operator"
      >&#8758;=</a
      ><a name="1424"
      > </a
      ><a name="1425" href="Stlc.html#1425" class="Bound"
      >V</a
      ><a name="1426"
      > </a
      ><a name="1427" href="Stlc.html#1297" class="Function Operator"
      >]</a
      ><a name="1428"
      > </a
      ><a name="1429" class="Keyword"
      >with</a
      ><a name="1433"
      > </a
      ><a name="1434" href="Stlc.html#1420" class="Bound"
      >x</a
      ><a name="1435"
      > </a
      ><a name="1436" href="Maps.html#2558" class="Function Operator"
      >&#8799;</a
      ><a name="1437"
      > </a
      ><a name="1438" href="Stlc.html#1404" class="Bound"
      >x&#8242;</a
      ><a name="1440"
      >
</a
      ><a name="1441" class="Symbol"
      >...</a
      ><a name="1444"
      > </a
      ><a name="1445" class="Symbol"
      >|</a
      ><a name="1446"
      > </a
      ><a name="1447" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#520" class="InductiveConstructor"
      >yes</a
      ><a name="1450"
      > </a
      ><a name="1451" class="Symbol"
      >_</a
      ><a name="1452"
      > </a
      ><a name="1453" class="Symbol"
      >=</a
      ><a name="1454"
      > </a
      ><a name="1455" href="Stlc.html#752" class="InductiveConstructor Operator"
      >&#955;[</a
      ><a name="1457"
      > </a
      ><a name="1458" href="Stlc.html#1404" class="Bound"
      >x&#8242;</a
      ><a name="1460"
      > </a
      ><a name="1461" href="Stlc.html#752" class="InductiveConstructor Operator"
      >&#8758;</a
      ><a name="1462"
      > </a
      ><a name="1463" href="Stlc.html#1409" class="Bound"
      >A&#8242;</a
      ><a name="1465"
      > </a
      ><a name="1466" href="Stlc.html#752" class="InductiveConstructor Operator"
      >]</a
      ><a name="1467"
      > </a
      ><a name="1468" href="Stlc.html#1414" class="Bound"
      >N&#8242;</a
      ><a name="1470"
      >
</a
      ><a name="1471" class="Symbol"
      >...</a
      ><a name="1474"
      > </a
      ><a name="1475" class="Symbol"
      >|</a
      ><a name="1476"
      > </a
      ><a name="1477" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#547" class="InductiveConstructor"
      >no</a
      ><a name="1479"
      >  </a
      ><a name="1481" class="Symbol"
      >_</a
      ><a name="1482"
      > </a
      ><a name="1483" class="Symbol"
      >=</a
      ><a name="1484"
      > </a
      ><a name="1485" href="Stlc.html#752" class="InductiveConstructor Operator"
      >&#955;[</a
      ><a name="1487"
      > </a
      ><a name="1488" href="Stlc.html#1404" class="Bound"
      >x&#8242;</a
      ><a name="1490"
      > </a
      ><a name="1491" href="Stlc.html#752" class="InductiveConstructor Operator"
      >&#8758;</a
      ><a name="1492"
      > </a
      ><a name="1493" href="Stlc.html#1409" class="Bound"
      >A&#8242;</a
      ><a name="1495"
      > </a
      ><a name="1496" href="Stlc.html#752" class="InductiveConstructor Operator"
      >]</a
      ><a name="1497"
      > </a
      ><a name="1498" class="Symbol"
      >(</a
      ><a name="1499" href="Stlc.html#1414" class="Bound"
      >N&#8242;</a
      ><a name="1501"
      > </a
      ><a name="1502" href="Stlc.html#1297" class="Function Operator"
      >[</a
      ><a name="1503"
      > </a
      ><a name="1504" href="Stlc.html#1420" class="Bound"
      >x</a
      ><a name="1505"
      > </a
      ><a name="1506" href="Stlc.html#1297" class="Function Operator"
      >&#8758;=</a
      ><a name="1508"
      > </a
      ><a name="1509" href="Stlc.html#1425" class="Bound"
      >V</a
      ><a name="1510"
      > </a
      ><a name="1511" href="Stlc.html#1297" class="Function Operator"
      >]</a
      ><a name="1512" class="Symbol"
      >)</a
      ><a name="1513"
      >
</a
      ><a name="1514" class="Symbol"
      >(</a
      ><a name="1515" href="Stlc.html#1515" class="Bound"
      >L&#8242;</a
      ><a name="1517"
      > </a
      ><a name="1518" href="Stlc.html#788" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="1519"
      > </a
      ><a name="1520" href="Stlc.html#1520" class="Bound"
      >M&#8242;</a
      ><a name="1522" class="Symbol"
      >)</a
      ><a name="1523"
      > </a
      ><a name="1524" href="Stlc.html#1297" class="Function Operator"
      >[</a
      ><a name="1525"
      > </a
      ><a name="1526" href="Stlc.html#1526" class="Bound"
      >x</a
      ><a name="1527"
      > </a
      ><a name="1528" href="Stlc.html#1297" class="Function Operator"
      >&#8758;=</a
      ><a name="1530"
      > </a
      ><a name="1531" href="Stlc.html#1531" class="Bound"
      >V</a
      ><a name="1532"
      > </a
      ><a name="1533" href="Stlc.html#1297" class="Function Operator"
      >]</a
      ><a name="1534"
      > </a
      ><a name="1535" class="Symbol"
      >=</a
      ><a name="1536"
      >  </a
      ><a name="1538" class="Symbol"
      >(</a
      ><a name="1539" href="Stlc.html#1515" class="Bound"
      >L&#8242;</a
      ><a name="1541"
      > </a
      ><a name="1542" href="Stlc.html#1297" class="Function Operator"
      >[</a
      ><a name="1543"
      > </a
      ><a name="1544" href="Stlc.html#1526" class="Bound"
      >x</a
      ><a name="1545"
      > </a
      ><a name="1546" href="Stlc.html#1297" class="Function Operator"
      >&#8758;=</a
      ><a name="1548"
      > </a
      ><a name="1549" href="Stlc.html#1531" class="Bound"
      >V</a
      ><a name="1550"
      > </a
      ><a name="1551" href="Stlc.html#1297" class="Function Operator"
      >]</a
      ><a name="1552" class="Symbol"
      >)</a
      ><a name="1553"
      > </a
      ><a name="1554" href="Stlc.html#788" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="1555"
      > </a
      ><a name="1556" class="Symbol"
      >(</a
      ><a name="1557" href="Stlc.html#1520" class="Bound"
      >M&#8242;</a
      ><a name="1559"
      > </a
      ><a name="1560" href="Stlc.html#1297" class="Function Operator"
      >[</a
      ><a name="1561"
      > </a
      ><a name="1562" href="Stlc.html#1526" class="Bound"
      >x</a
      ><a name="1563"
      > </a
      ><a name="1564" href="Stlc.html#1297" class="Function Operator"
      >&#8758;=</a
      ><a name="1566"
      > </a
      ><a name="1567" href="Stlc.html#1531" class="Bound"
      >V</a
      ><a name="1568"
      > </a
      ><a name="1569" href="Stlc.html#1297" class="Function Operator"
      >]</a
      ><a name="1570" class="Symbol"
      >)</a
      ><a name="1571"
      >
</a
      ><a name="1572" class="Symbol"
      >(</a
      ><a name="1573" href="Stlc.html#815" class="InductiveConstructor"
      >true</a
      ><a name="1577" class="Symbol"
      >)</a
      ><a name="1578"
      > </a
      ><a name="1579" href="Stlc.html#1297" class="Function Operator"
      >[</a
      ><a name="1580"
      > </a
      ><a name="1581" href="Stlc.html#1581" class="Bound"
      >x</a
      ><a name="1582"
      > </a
      ><a name="1583" href="Stlc.html#1297" class="Function Operator"
      >&#8758;=</a
      ><a name="1585"
      > </a
      ><a name="1586" href="Stlc.html#1586" class="Bound"
      >V</a
      ><a name="1587"
      > </a
      ><a name="1588" href="Stlc.html#1297" class="Function Operator"
      >]</a
      ><a name="1589"
      > </a
      ><a name="1590" class="Symbol"
      >=</a
      ><a name="1591"
      > </a
      ><a name="1592" href="Stlc.html#815" class="InductiveConstructor"
      >true</a
      ><a name="1596"
      >
</a
      ><a name="1597" class="Symbol"
      >(</a
      ><a name="1598" href="Stlc.html#829" class="InductiveConstructor"
      >false</a
      ><a name="1603" class="Symbol"
      >)</a
      ><a name="1604"
      > </a
      ><a name="1605" href="Stlc.html#1297" class="Function Operator"
      >[</a
      ><a name="1606"
      > </a
      ><a name="1607" href="Stlc.html#1607" class="Bound"
      >x</a
      ><a name="1608"
      > </a
      ><a name="1609" href="Stlc.html#1297" class="Function Operator"
      >&#8758;=</a
      ><a name="1611"
      > </a
      ><a name="1612" href="Stlc.html#1612" class="Bound"
      >V</a
      ><a name="1613"
      > </a
      ><a name="1614" href="Stlc.html#1297" class="Function Operator"
      >]</a
      ><a name="1615"
      > </a
      ><a name="1616" class="Symbol"
      >=</a
      ><a name="1617"
      > </a
      ><a name="1618" href="Stlc.html#829" class="InductiveConstructor"
      >false</a
      ><a name="1623"
      >
</a
      ><a name="1624" class="Symbol"
      >(</a
      ><a name="1625" href="Stlc.html#844" class="InductiveConstructor Operator"
      >if</a
      ><a name="1627"
      > </a
      ><a name="1628" href="Stlc.html#1628" class="Bound"
      >L&#8242;</a
      ><a name="1630"
      > </a
      ><a name="1631" href="Stlc.html#844" class="InductiveConstructor Operator"
      >then</a
      ><a name="1635"
      > </a
      ><a name="1636" href="Stlc.html#1636" class="Bound"
      >M&#8242;</a
      ><a name="1638"
      > </a
      ><a name="1639" href="Stlc.html#844" class="InductiveConstructor Operator"
      >else</a
      ><a name="1643"
      > </a
      ><a name="1644" href="Stlc.html#1644" class="Bound"
      >N&#8242;</a
      ><a name="1646" class="Symbol"
      >)</a
      ><a name="1647"
      > </a
      ><a name="1648" href="Stlc.html#1297" class="Function Operator"
      >[</a
      ><a name="1649"
      > </a
      ><a name="1650" href="Stlc.html#1650" class="Bound"
      >x</a
      ><a name="1651"
      > </a
      ><a name="1652" href="Stlc.html#1297" class="Function Operator"
      >&#8758;=</a
      ><a name="1654"
      > </a
      ><a name="1655" href="Stlc.html#1655" class="Bound"
      >V</a
      ><a name="1656"
      > </a
      ><a name="1657" href="Stlc.html#1297" class="Function Operator"
      >]</a
      ><a name="1658"
      > </a
      ><a name="1659" class="Symbol"
      >=</a
      ><a name="1660"
      > </a
      ><a name="1661" href="Stlc.html#844" class="InductiveConstructor Operator"
      >if</a
      ><a name="1663"
      > </a
      ><a name="1664" class="Symbol"
      >(</a
      ><a name="1665" href="Stlc.html#1628" class="Bound"
      >L&#8242;</a
      ><a name="1667"
      > </a
      ><a name="1668" href="Stlc.html#1297" class="Function Operator"
      >[</a
      ><a name="1669"
      > </a
      ><a name="1670" href="Stlc.html#1650" class="Bound"
      >x</a
      ><a name="1671"
      > </a
      ><a name="1672" href="Stlc.html#1297" class="Function Operator"
      >&#8758;=</a
      ><a name="1674"
      > </a
      ><a name="1675" href="Stlc.html#1655" class="Bound"
      >V</a
      ><a name="1676"
      > </a
      ><a name="1677" href="Stlc.html#1297" class="Function Operator"
      >]</a
      ><a name="1678" class="Symbol"
      >)</a
      ><a name="1679"
      > </a
      ><a name="1680" href="Stlc.html#844" class="InductiveConstructor Operator"
      >then</a
      ><a name="1684"
      > </a
      ><a name="1685" class="Symbol"
      >(</a
      ><a name="1686" href="Stlc.html#1636" class="Bound"
      >M&#8242;</a
      ><a name="1688"
      > </a
      ><a name="1689" href="Stlc.html#1297" class="Function Operator"
      >[</a
      ><a name="1690"
      > </a
      ><a name="1691" href="Stlc.html#1650" class="Bound"
      >x</a
      ><a name="1692"
      > </a
      ><a name="1693" href="Stlc.html#1297" class="Function Operator"
      >&#8758;=</a
      ><a name="1695"
      > </a
      ><a name="1696" href="Stlc.html#1655" class="Bound"
      >V</a
      ><a name="1697"
      > </a
      ><a name="1698" href="Stlc.html#1297" class="Function Operator"
      >]</a
      ><a name="1699" class="Symbol"
      >)</a
      ><a name="1700"
      > </a
      ><a name="1701" href="Stlc.html#844" class="InductiveConstructor Operator"
      >else</a
      ><a name="1705"
      > </a
      ><a name="1706" class="Symbol"
      >(</a
      ><a name="1707" href="Stlc.html#1644" class="Bound"
      >N&#8242;</a
      ><a name="1709"
      > </a
      ><a name="1710" href="Stlc.html#1297" class="Function Operator"
      >[</a
      ><a name="1711"
      > </a
      ><a name="1712" href="Stlc.html#1650" class="Bound"
      >x</a
      ><a name="1713"
      > </a
      ><a name="1714" href="Stlc.html#1297" class="Function Operator"
      >&#8758;=</a
      ><a name="1716"
      > </a
      ><a name="1717" href="Stlc.html#1655" class="Bound"
      >V</a
      ><a name="1718"
      > </a
      ><a name="1719" href="Stlc.html#1297" class="Function Operator"
      >]</a
      ><a name="1720" class="Symbol"
      >)</a
      >
{% endraw %}</pre>

## Reduction rules

<pre class="Agda">{% raw %}
<a name="1767" class="Keyword"
      >infix</a
      ><a name="1772"
      > </a
      ><a name="1773" class="Number"
      >10</a
      ><a name="1775"
      > </a
      ><a name="1776" href="Stlc.html#1787" class="Datatype Operator"
      >_&#10233;_</a
      ><a name="1779"
      > 

</a
      ><a name="1782" class="Keyword"
      >data</a
      ><a name="1786"
      > </a
      ><a name="1787" href="Stlc.html#1787" class="Datatype Operator"
      >_&#10233;_</a
      ><a name="1790"
      > </a
      ><a name="1791" class="Symbol"
      >:</a
      ><a name="1792"
      > </a
      ><a name="1793" href="Stlc.html#715" class="Datatype"
      >Term</a
      ><a name="1797"
      > </a
      ><a name="1798" class="Symbol"
      >&#8594;</a
      ><a name="1799"
      > </a
      ><a name="1800" href="Stlc.html#715" class="Datatype"
      >Term</a
      ><a name="1804"
      > </a
      ><a name="1805" class="Symbol"
      >&#8594;</a
      ><a name="1806"
      > </a
      ><a name="1807" class="PrimitiveType"
      >Set</a
      ><a name="1810"
      > </a
      ><a name="1811" class="Keyword"
      >where</a
      ><a name="1816"
      >
  </a
      ><a name="1819" href="Stlc.html#1819" class="InductiveConstructor"
      >&#946;&#8658;</a
      ><a name="1821"
      > </a
      ><a name="1822" class="Symbol"
      >:</a
      ><a name="1823"
      > </a
      ><a name="1824" class="Symbol"
      >&#8704;</a
      ><a name="1825"
      > </a
      ><a name="1826" class="Symbol"
      >{</a
      ><a name="1827" href="Stlc.html#1827" class="Bound"
      >x</a
      ><a name="1828"
      > </a
      ><a name="1829" href="Stlc.html#1829" class="Bound"
      >A</a
      ><a name="1830"
      > </a
      ><a name="1831" href="Stlc.html#1831" class="Bound"
      >N</a
      ><a name="1832"
      > </a
      ><a name="1833" href="Stlc.html#1833" class="Bound"
      >V</a
      ><a name="1834" class="Symbol"
      >}</a
      ><a name="1835"
      > </a
      ><a name="1836" class="Symbol"
      >&#8594;</a
      ><a name="1837"
      > </a
      ><a name="1838" href="Stlc.html#1126" class="Datatype"
      >Value</a
      ><a name="1843"
      > </a
      ><a name="1844" href="Stlc.html#1833" class="Bound"
      >V</a
      ><a name="1845"
      > </a
      ><a name="1846" class="Symbol"
      >&#8594;</a
      ><a name="1847"
      >
    </a
      ><a name="1852" class="Symbol"
      >(</a
      ><a name="1853" href="Stlc.html#752" class="InductiveConstructor Operator"
      >&#955;[</a
      ><a name="1855"
      > </a
      ><a name="1856" href="Stlc.html#1827" class="Bound"
      >x</a
      ><a name="1857"
      > </a
      ><a name="1858" href="Stlc.html#752" class="InductiveConstructor Operator"
      >&#8758;</a
      ><a name="1859"
      > </a
      ><a name="1860" href="Stlc.html#1829" class="Bound"
      >A</a
      ><a name="1861"
      > </a
      ><a name="1862" href="Stlc.html#752" class="InductiveConstructor Operator"
      >]</a
      ><a name="1863"
      > </a
      ><a name="1864" href="Stlc.html#1831" class="Bound"
      >N</a
      ><a name="1865" class="Symbol"
      >)</a
      ><a name="1866"
      > </a
      ><a name="1867" href="Stlc.html#788" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="1868"
      > </a
      ><a name="1869" href="Stlc.html#1833" class="Bound"
      >V</a
      ><a name="1870"
      > </a
      ><a name="1871" href="Stlc.html#1787" class="Datatype Operator"
      >&#10233;</a
      ><a name="1872"
      > </a
      ><a name="1873" href="Stlc.html#1831" class="Bound"
      >N</a
      ><a name="1874"
      > </a
      ><a name="1875" href="Stlc.html#1297" class="Function Operator"
      >[</a
      ><a name="1876"
      > </a
      ><a name="1877" href="Stlc.html#1827" class="Bound"
      >x</a
      ><a name="1878"
      > </a
      ><a name="1879" href="Stlc.html#1297" class="Function Operator"
      >&#8758;=</a
      ><a name="1881"
      > </a
      ><a name="1882" href="Stlc.html#1833" class="Bound"
      >V</a
      ><a name="1883"
      > </a
      ><a name="1884" href="Stlc.html#1297" class="Function Operator"
      >]</a
      ><a name="1885"
      >
  </a
      ><a name="1888" href="Stlc.html#1888" class="InductiveConstructor"
      >&#947;&#8658;&#8321;</a
      ><a name="1891"
      > </a
      ><a name="1892" class="Symbol"
      >:</a
      ><a name="1893"
      > </a
      ><a name="1894" class="Symbol"
      >&#8704;</a
      ><a name="1895"
      > </a
      ><a name="1896" class="Symbol"
      >{</a
      ><a name="1897" href="Stlc.html#1897" class="Bound"
      >L</a
      ><a name="1898"
      > </a
      ><a name="1899" href="Stlc.html#1899" class="Bound"
      >L'</a
      ><a name="1901"
      > </a
      ><a name="1902" href="Stlc.html#1902" class="Bound"
      >M</a
      ><a name="1903" class="Symbol"
      >}</a
      ><a name="1904"
      > </a
      ><a name="1905" class="Symbol"
      >&#8594;</a
      ><a name="1906"
      >
    </a
      ><a name="1911" href="Stlc.html#1897" class="Bound"
      >L</a
      ><a name="1912"
      > </a
      ><a name="1913" href="Stlc.html#1787" class="Datatype Operator"
      >&#10233;</a
      ><a name="1914"
      > </a
      ><a name="1915" href="Stlc.html#1899" class="Bound"
      >L'</a
      ><a name="1917"
      > </a
      ><a name="1918" class="Symbol"
      >&#8594;</a
      ><a name="1919"
      >
    </a
      ><a name="1924" href="Stlc.html#1897" class="Bound"
      >L</a
      ><a name="1925"
      > </a
      ><a name="1926" href="Stlc.html#788" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="1927"
      > </a
      ><a name="1928" href="Stlc.html#1902" class="Bound"
      >M</a
      ><a name="1929"
      > </a
      ><a name="1930" href="Stlc.html#1787" class="Datatype Operator"
      >&#10233;</a
      ><a name="1931"
      > </a
      ><a name="1932" href="Stlc.html#1899" class="Bound"
      >L'</a
      ><a name="1934"
      > </a
      ><a name="1935" href="Stlc.html#788" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="1936"
      > </a
      ><a name="1937" href="Stlc.html#1902" class="Bound"
      >M</a
      ><a name="1938"
      >
  </a
      ><a name="1941" href="Stlc.html#1941" class="InductiveConstructor"
      >&#947;&#8658;&#8322;</a
      ><a name="1944"
      > </a
      ><a name="1945" class="Symbol"
      >:</a
      ><a name="1946"
      > </a
      ><a name="1947" class="Symbol"
      >&#8704;</a
      ><a name="1948"
      > </a
      ><a name="1949" class="Symbol"
      >{</a
      ><a name="1950" href="Stlc.html#1950" class="Bound"
      >V</a
      ><a name="1951"
      > </a
      ><a name="1952" href="Stlc.html#1952" class="Bound"
      >M</a
      ><a name="1953"
      > </a
      ><a name="1954" href="Stlc.html#1954" class="Bound"
      >M'</a
      ><a name="1956" class="Symbol"
      >}</a
      ><a name="1957"
      > </a
      ><a name="1958" class="Symbol"
      >&#8594;</a
      ><a name="1959"
      >
    </a
      ><a name="1964" href="Stlc.html#1126" class="Datatype"
      >Value</a
      ><a name="1969"
      > </a
      ><a name="1970" href="Stlc.html#1950" class="Bound"
      >V</a
      ><a name="1971"
      > </a
      ><a name="1972" class="Symbol"
      >&#8594;</a
      ><a name="1973"
      >
    </a
      ><a name="1978" href="Stlc.html#1952" class="Bound"
      >M</a
      ><a name="1979"
      > </a
      ><a name="1980" href="Stlc.html#1787" class="Datatype Operator"
      >&#10233;</a
      ><a name="1981"
      > </a
      ><a name="1982" href="Stlc.html#1954" class="Bound"
      >M'</a
      ><a name="1984"
      > </a
      ><a name="1985" class="Symbol"
      >&#8594;</a
      ><a name="1986"
      >
    </a
      ><a name="1991" href="Stlc.html#1950" class="Bound"
      >V</a
      ><a name="1992"
      > </a
      ><a name="1993" href="Stlc.html#788" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="1994"
      > </a
      ><a name="1995" href="Stlc.html#1952" class="Bound"
      >M</a
      ><a name="1996"
      > </a
      ><a name="1997" href="Stlc.html#1787" class="Datatype Operator"
      >&#10233;</a
      ><a name="1998"
      > </a
      ><a name="1999" href="Stlc.html#1950" class="Bound"
      >V</a
      ><a name="2000"
      > </a
      ><a name="2001" href="Stlc.html#788" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="2002"
      > </a
      ><a name="2003" href="Stlc.html#1954" class="Bound"
      >M'</a
      ><a name="2005"
      >
  </a
      ><a name="2008" href="Stlc.html#2008" class="InductiveConstructor"
      >&#946;&#120121;&#8321;</a
      ><a name="2011"
      > </a
      ><a name="2012" class="Symbol"
      >:</a
      ><a name="2013"
      > </a
      ><a name="2014" class="Symbol"
      >&#8704;</a
      ><a name="2015"
      > </a
      ><a name="2016" class="Symbol"
      >{</a
      ><a name="2017" href="Stlc.html#2017" class="Bound"
      >M</a
      ><a name="2018"
      > </a
      ><a name="2019" href="Stlc.html#2019" class="Bound"
      >N</a
      ><a name="2020" class="Symbol"
      >}</a
      ><a name="2021"
      > </a
      ><a name="2022" class="Symbol"
      >&#8594;</a
      ><a name="2023"
      >
    </a
      ><a name="2028" href="Stlc.html#844" class="InductiveConstructor Operator"
      >if</a
      ><a name="2030"
      > </a
      ><a name="2031" href="Stlc.html#815" class="InductiveConstructor"
      >true</a
      ><a name="2035"
      > </a
      ><a name="2036" href="Stlc.html#844" class="InductiveConstructor Operator"
      >then</a
      ><a name="2040"
      > </a
      ><a name="2041" href="Stlc.html#2017" class="Bound"
      >M</a
      ><a name="2042"
      > </a
      ><a name="2043" href="Stlc.html#844" class="InductiveConstructor Operator"
      >else</a
      ><a name="2047"
      > </a
      ><a name="2048" href="Stlc.html#2019" class="Bound"
      >N</a
      ><a name="2049"
      > </a
      ><a name="2050" href="Stlc.html#1787" class="Datatype Operator"
      >&#10233;</a
      ><a name="2051"
      > </a
      ><a name="2052" href="Stlc.html#2017" class="Bound"
      >M</a
      ><a name="2053"
      >
  </a
      ><a name="2056" href="Stlc.html#2056" class="InductiveConstructor"
      >&#946;&#120121;&#8322;</a
      ><a name="2059"
      > </a
      ><a name="2060" class="Symbol"
      >:</a
      ><a name="2061"
      > </a
      ><a name="2062" class="Symbol"
      >&#8704;</a
      ><a name="2063"
      > </a
      ><a name="2064" class="Symbol"
      >{</a
      ><a name="2065" href="Stlc.html#2065" class="Bound"
      >M</a
      ><a name="2066"
      > </a
      ><a name="2067" href="Stlc.html#2067" class="Bound"
      >N</a
      ><a name="2068" class="Symbol"
      >}</a
      ><a name="2069"
      > </a
      ><a name="2070" class="Symbol"
      >&#8594;</a
      ><a name="2071"
      >
    </a
      ><a name="2076" href="Stlc.html#844" class="InductiveConstructor Operator"
      >if</a
      ><a name="2078"
      > </a
      ><a name="2079" href="Stlc.html#829" class="InductiveConstructor"
      >false</a
      ><a name="2084"
      > </a
      ><a name="2085" href="Stlc.html#844" class="InductiveConstructor Operator"
      >then</a
      ><a name="2089"
      > </a
      ><a name="2090" href="Stlc.html#2065" class="Bound"
      >M</a
      ><a name="2091"
      > </a
      ><a name="2092" href="Stlc.html#844" class="InductiveConstructor Operator"
      >else</a
      ><a name="2096"
      > </a
      ><a name="2097" href="Stlc.html#2067" class="Bound"
      >N</a
      ><a name="2098"
      > </a
      ><a name="2099" href="Stlc.html#1787" class="Datatype Operator"
      >&#10233;</a
      ><a name="2100"
      > </a
      ><a name="2101" href="Stlc.html#2067" class="Bound"
      >N</a
      ><a name="2102"
      >
  </a
      ><a name="2105" href="Stlc.html#2105" class="InductiveConstructor"
      >&#947;&#120121;</a
      ><a name="2107"
      > </a
      ><a name="2108" class="Symbol"
      >:</a
      ><a name="2109"
      > </a
      ><a name="2110" class="Symbol"
      >&#8704;</a
      ><a name="2111"
      > </a
      ><a name="2112" class="Symbol"
      >{</a
      ><a name="2113" href="Stlc.html#2113" class="Bound"
      >L</a
      ><a name="2114"
      > </a
      ><a name="2115" href="Stlc.html#2115" class="Bound"
      >L'</a
      ><a name="2117"
      > </a
      ><a name="2118" href="Stlc.html#2118" class="Bound"
      >M</a
      ><a name="2119"
      > </a
      ><a name="2120" href="Stlc.html#2120" class="Bound"
      >N</a
      ><a name="2121" class="Symbol"
      >}</a
      ><a name="2122"
      > </a
      ><a name="2123" class="Symbol"
      >&#8594;</a
      ><a name="2124"
      >
    </a
      ><a name="2129" href="Stlc.html#2113" class="Bound"
      >L</a
      ><a name="2130"
      > </a
      ><a name="2131" href="Stlc.html#1787" class="Datatype Operator"
      >&#10233;</a
      ><a name="2132"
      > </a
      ><a name="2133" href="Stlc.html#2115" class="Bound"
      >L'</a
      ><a name="2135"
      > </a
      ><a name="2136" class="Symbol"
      >&#8594;</a
      ><a name="2137"
      >    
    </a
      ><a name="2146" href="Stlc.html#844" class="InductiveConstructor Operator"
      >if</a
      ><a name="2148"
      > </a
      ><a name="2149" href="Stlc.html#2113" class="Bound"
      >L</a
      ><a name="2150"
      > </a
      ><a name="2151" href="Stlc.html#844" class="InductiveConstructor Operator"
      >then</a
      ><a name="2155"
      > </a
      ><a name="2156" href="Stlc.html#2118" class="Bound"
      >M</a
      ><a name="2157"
      > </a
      ><a name="2158" href="Stlc.html#844" class="InductiveConstructor Operator"
      >else</a
      ><a name="2162"
      > </a
      ><a name="2163" href="Stlc.html#2120" class="Bound"
      >N</a
      ><a name="2164"
      > </a
      ><a name="2165" href="Stlc.html#1787" class="Datatype Operator"
      >&#10233;</a
      ><a name="2166"
      > </a
      ><a name="2167" href="Stlc.html#844" class="InductiveConstructor Operator"
      >if</a
      ><a name="2169"
      > </a
      ><a name="2170" href="Stlc.html#2115" class="Bound"
      >L'</a
      ><a name="2172"
      > </a
      ><a name="2173" href="Stlc.html#844" class="InductiveConstructor Operator"
      >then</a
      ><a name="2177"
      > </a
      ><a name="2178" href="Stlc.html#2118" class="Bound"
      >M</a
      ><a name="2179"
      > </a
      ><a name="2180" href="Stlc.html#844" class="InductiveConstructor Operator"
      >else</a
      ><a name="2184"
      > </a
      ><a name="2185" href="Stlc.html#2120" class="Bound"
      >N</a
      >
{% endraw %}</pre>

## Reflexive and transitive closure

<pre class="Agda">{% raw %}
<a name="2249" href="Stlc.html#2249" class="Function"
      >Rel</a
      ><a name="2252"
      > </a
      ><a name="2253" class="Symbol"
      >:</a
      ><a name="2254"
      > </a
      ><a name="2255" class="PrimitiveType"
      >Set</a
      ><a name="2258"
      > </a
      ><a name="2259" class="Symbol"
      >&#8594;</a
      ><a name="2260"
      > </a
      ><a name="2261" class="PrimitiveType"
      >Set&#8321;</a
      ><a name="2265"
      >
</a
      ><a name="2266" href="Stlc.html#2249" class="Function"
      >Rel</a
      ><a name="2269"
      > </a
      ><a name="2270" href="Stlc.html#2270" class="Bound"
      >A</a
      ><a name="2271"
      > </a
      ><a name="2272" class="Symbol"
      >=</a
      ><a name="2273"
      > </a
      ><a name="2274" href="Stlc.html#2270" class="Bound"
      >A</a
      ><a name="2275"
      > </a
      ><a name="2276" class="Symbol"
      >&#8594;</a
      ><a name="2277"
      > </a
      ><a name="2278" href="Stlc.html#2270" class="Bound"
      >A</a
      ><a name="2279"
      > </a
      ><a name="2280" class="Symbol"
      >&#8594;</a
      ><a name="2281"
      > </a
      ><a name="2282" class="PrimitiveType"
      >Set</a
      ><a name="2285"
      >

</a
      ><a name="2287" class="Keyword"
      >infixl</a
      ><a name="2293"
      > </a
      ><a name="2294" class="Number"
      >10</a
      ><a name="2296"
      > </a
      ><a name="2297" href="Stlc.html#2418" class="InductiveConstructor Operator"
      >_&gt;&gt;_</a
      ><a name="2301"
      >

</a
      ><a name="2303" class="Keyword"
      >data</a
      ><a name="2307"
      > </a
      ><a name="2308" href="Stlc.html#2308" class="Datatype Operator"
      >_*</a
      ><a name="2310"
      > </a
      ><a name="2311" class="Symbol"
      >{</a
      ><a name="2312" href="Stlc.html#2312" class="Bound"
      >A</a
      ><a name="2313"
      > </a
      ><a name="2314" class="Symbol"
      >:</a
      ><a name="2315"
      > </a
      ><a name="2316" class="PrimitiveType"
      >Set</a
      ><a name="2319" class="Symbol"
      >}</a
      ><a name="2320"
      > </a
      ><a name="2321" class="Symbol"
      >(</a
      ><a name="2322" href="Stlc.html#2322" class="Bound"
      >R</a
      ><a name="2323"
      > </a
      ><a name="2324" class="Symbol"
      >:</a
      ><a name="2325"
      > </a
      ><a name="2326" href="Stlc.html#2249" class="Function"
      >Rel</a
      ><a name="2329"
      > </a
      ><a name="2330" href="Stlc.html#2312" class="Bound"
      >A</a
      ><a name="2331" class="Symbol"
      >)</a
      ><a name="2332"
      > </a
      ><a name="2333" class="Symbol"
      >:</a
      ><a name="2334"
      > </a
      ><a name="2335" href="Stlc.html#2249" class="Function"
      >Rel</a
      ><a name="2338"
      > </a
      ><a name="2339" href="Stlc.html#2312" class="Bound"
      >A</a
      ><a name="2340"
      > </a
      ><a name="2341" class="Keyword"
      >where</a
      ><a name="2346"
      >
  </a
      ><a name="2349" href="Stlc.html#2349" class="InductiveConstructor"
      >&#10216;&#10217;</a
      ><a name="2351"
      > </a
      ><a name="2352" class="Symbol"
      >:</a
      ><a name="2353"
      > </a
      ><a name="2354" class="Symbol"
      >&#8704;</a
      ><a name="2355"
      > </a
      ><a name="2356" class="Symbol"
      >{</a
      ><a name="2357" href="Stlc.html#2357" class="Bound"
      >x</a
      ><a name="2358"
      > </a
      ><a name="2359" class="Symbol"
      >:</a
      ><a name="2360"
      > </a
      ><a name="2361" href="Stlc.html#2312" class="Bound"
      >A</a
      ><a name="2362" class="Symbol"
      >}</a
      ><a name="2363"
      > </a
      ><a name="2364" class="Symbol"
      >&#8594;</a
      ><a name="2365"
      > </a
      ><a name="2366" class="Symbol"
      >(</a
      ><a name="2367" href="Stlc.html#2322" class="Bound"
      >R</a
      ><a name="2368"
      > </a
      ><a name="2369" href="Stlc.html#2308" class="Datatype Operator"
      >*</a
      ><a name="2370" class="Symbol"
      >)</a
      ><a name="2371"
      > </a
      ><a name="2372" href="Stlc.html#2357" class="Bound"
      >x</a
      ><a name="2373"
      > </a
      ><a name="2374" href="Stlc.html#2357" class="Bound"
      >x</a
      ><a name="2375"
      >
  </a
      ><a name="2378" href="Stlc.html#2378" class="InductiveConstructor Operator"
      >&#10216;_&#10217;</a
      ><a name="2381"
      > </a
      ><a name="2382" class="Symbol"
      >:</a
      ><a name="2383"
      > </a
      ><a name="2384" class="Symbol"
      >&#8704;</a
      ><a name="2385"
      > </a
      ><a name="2386" class="Symbol"
      >{</a
      ><a name="2387" href="Stlc.html#2387" class="Bound"
      >x</a
      ><a name="2388"
      > </a
      ><a name="2389" href="Stlc.html#2389" class="Bound"
      >y</a
      ><a name="2390"
      > </a
      ><a name="2391" class="Symbol"
      >:</a
      ><a name="2392"
      > </a
      ><a name="2393" href="Stlc.html#2312" class="Bound"
      >A</a
      ><a name="2394" class="Symbol"
      >}</a
      ><a name="2395"
      > </a
      ><a name="2396" class="Symbol"
      >&#8594;</a
      ><a name="2397"
      > </a
      ><a name="2398" href="Stlc.html#2322" class="Bound"
      >R</a
      ><a name="2399"
      > </a
      ><a name="2400" href="Stlc.html#2387" class="Bound"
      >x</a
      ><a name="2401"
      > </a
      ><a name="2402" href="Stlc.html#2389" class="Bound"
      >y</a
      ><a name="2403"
      > </a
      ><a name="2404" class="Symbol"
      >&#8594;</a
      ><a name="2405"
      > </a
      ><a name="2406" class="Symbol"
      >(</a
      ><a name="2407" href="Stlc.html#2322" class="Bound"
      >R</a
      ><a name="2408"
      > </a
      ><a name="2409" href="Stlc.html#2308" class="Datatype Operator"
      >*</a
      ><a name="2410" class="Symbol"
      >)</a
      ><a name="2411"
      > </a
      ><a name="2412" href="Stlc.html#2387" class="Bound"
      >x</a
      ><a name="2413"
      > </a
      ><a name="2414" href="Stlc.html#2389" class="Bound"
      >y</a
      ><a name="2415"
      >
  </a
      ><a name="2418" href="Stlc.html#2418" class="InductiveConstructor Operator"
      >_&gt;&gt;_</a
      ><a name="2422"
      > </a
      ><a name="2423" class="Symbol"
      >:</a
      ><a name="2424"
      > </a
      ><a name="2425" class="Symbol"
      >&#8704;</a
      ><a name="2426"
      > </a
      ><a name="2427" class="Symbol"
      >{</a
      ><a name="2428" href="Stlc.html#2428" class="Bound"
      >x</a
      ><a name="2429"
      > </a
      ><a name="2430" href="Stlc.html#2430" class="Bound"
      >y</a
      ><a name="2431"
      > </a
      ><a name="2432" href="Stlc.html#2432" class="Bound"
      >z</a
      ><a name="2433"
      > </a
      ><a name="2434" class="Symbol"
      >:</a
      ><a name="2435"
      > </a
      ><a name="2436" href="Stlc.html#2312" class="Bound"
      >A</a
      ><a name="2437" class="Symbol"
      >}</a
      ><a name="2438"
      > </a
      ><a name="2439" class="Symbol"
      >&#8594;</a
      ><a name="2440"
      > </a
      ><a name="2441" class="Symbol"
      >(</a
      ><a name="2442" href="Stlc.html#2322" class="Bound"
      >R</a
      ><a name="2443"
      > </a
      ><a name="2444" href="Stlc.html#2308" class="Datatype Operator"
      >*</a
      ><a name="2445" class="Symbol"
      >)</a
      ><a name="2446"
      > </a
      ><a name="2447" href="Stlc.html#2428" class="Bound"
      >x</a
      ><a name="2448"
      > </a
      ><a name="2449" href="Stlc.html#2430" class="Bound"
      >y</a
      ><a name="2450"
      > </a
      ><a name="2451" class="Symbol"
      >&#8594;</a
      ><a name="2452"
      > </a
      ><a name="2453" class="Symbol"
      >(</a
      ><a name="2454" href="Stlc.html#2322" class="Bound"
      >R</a
      ><a name="2455"
      > </a
      ><a name="2456" href="Stlc.html#2308" class="Datatype Operator"
      >*</a
      ><a name="2457" class="Symbol"
      >)</a
      ><a name="2458"
      > </a
      ><a name="2459" href="Stlc.html#2430" class="Bound"
      >y</a
      ><a name="2460"
      > </a
      ><a name="2461" href="Stlc.html#2432" class="Bound"
      >z</a
      ><a name="2462"
      > </a
      ><a name="2463" class="Symbol"
      >&#8594;</a
      ><a name="2464"
      > </a
      ><a name="2465" class="Symbol"
      >(</a
      ><a name="2466" href="Stlc.html#2322" class="Bound"
      >R</a
      ><a name="2467"
      > </a
      ><a name="2468" href="Stlc.html#2308" class="Datatype Operator"
      >*</a
      ><a name="2469" class="Symbol"
      >)</a
      ><a name="2470"
      > </a
      ><a name="2471" href="Stlc.html#2428" class="Bound"
      >x</a
      ><a name="2472"
      > </a
      ><a name="2473" href="Stlc.html#2432" class="Bound"
      >z</a
      ><a name="2474"
      >

</a
      ><a name="2476" class="Keyword"
      >infix</a
      ><a name="2481"
      > </a
      ><a name="2482" class="Number"
      >10</a
      ><a name="2484"
      > </a
      ><a name="2485" href="Stlc.html#2491" class="Function Operator"
      >_&#10233;*_</a
      ><a name="2489"
      >

</a
      ><a name="2491" href="Stlc.html#2491" class="Function Operator"
      >_&#10233;*_</a
      ><a name="2495"
      > </a
      ><a name="2496" class="Symbol"
      >:</a
      ><a name="2497"
      > </a
      ><a name="2498" href="Stlc.html#2249" class="Function"
      >Rel</a
      ><a name="2501"
      > </a
      ><a name="2502" href="Stlc.html#715" class="Datatype"
      >Term</a
      ><a name="2506"
      >
</a
      ><a name="2507" href="Stlc.html#2491" class="Function Operator"
      >_&#10233;*_</a
      ><a name="2511"
      > </a
      ><a name="2512" class="Symbol"
      >=</a
      ><a name="2513"
      > </a
      ><a name="2514" class="Symbol"
      >(</a
      ><a name="2515" href="Stlc.html#1787" class="Datatype Operator"
      >_&#10233;_</a
      ><a name="2518" class="Symbol"
      >)</a
      ><a name="2519"
      > </a
      ><a name="2520" href="Stlc.html#2308" class="Datatype Operator"
      >*</a
      >
{% endraw %}</pre>

## Notation for setting out reductions

<pre class="Agda">{% raw %}
<a name="2587" class="Keyword"
      >infixr</a
      ><a name="2593"
      > </a
      ><a name="2594" class="Number"
      >2</a
      ><a name="2595"
      > </a
      ><a name="2596" href="Stlc.html#2616" class="Function Operator"
      >_&#10233;&#10216;_&#10217;_</a
      ><a name="2602"
      >
</a
      ><a name="2603" class="Keyword"
      >infix</a
      ><a name="2608"
      >  </a
      ><a name="2610" class="Number"
      >3</a
      ><a name="2611"
      > </a
      ><a name="2612" href="Stlc.html#2698" class="Function Operator"
      >_&#8718;</a
      ><a name="2614"
      >

</a
      ><a name="2616" href="Stlc.html#2616" class="Function Operator"
      >_&#10233;&#10216;_&#10217;_</a
      ><a name="2622"
      > </a
      ><a name="2623" class="Symbol"
      >:</a
      ><a name="2624"
      > </a
      ><a name="2625" class="Symbol"
      >&#8704;</a
      ><a name="2626"
      > </a
      ><a name="2627" href="Stlc.html#2627" class="Bound"
      >L</a
      ><a name="2628"
      > </a
      ><a name="2629" class="Symbol"
      >{</a
      ><a name="2630" href="Stlc.html#2630" class="Bound"
      >M</a
      ><a name="2631"
      > </a
      ><a name="2632" href="Stlc.html#2632" class="Bound"
      >N</a
      ><a name="2633" class="Symbol"
      >}</a
      ><a name="2634"
      > </a
      ><a name="2635" class="Symbol"
      >&#8594;</a
      ><a name="2636"
      > </a
      ><a name="2637" href="Stlc.html#2627" class="Bound"
      >L</a
      ><a name="2638"
      > </a
      ><a name="2639" href="Stlc.html#1787" class="Datatype Operator"
      >&#10233;</a
      ><a name="2640"
      > </a
      ><a name="2641" href="Stlc.html#2630" class="Bound"
      >M</a
      ><a name="2642"
      > </a
      ><a name="2643" class="Symbol"
      >&#8594;</a
      ><a name="2644"
      > </a
      ><a name="2645" href="Stlc.html#2630" class="Bound"
      >M</a
      ><a name="2646"
      > </a
      ><a name="2647" href="Stlc.html#2491" class="Function Operator"
      >&#10233;*</a
      ><a name="2649"
      > </a
      ><a name="2650" href="Stlc.html#2632" class="Bound"
      >N</a
      ><a name="2651"
      > </a
      ><a name="2652" class="Symbol"
      >&#8594;</a
      ><a name="2653"
      > </a
      ><a name="2654" href="Stlc.html#2627" class="Bound"
      >L</a
      ><a name="2655"
      > </a
      ><a name="2656" href="Stlc.html#2491" class="Function Operator"
      >&#10233;*</a
      ><a name="2658"
      > </a
      ><a name="2659" href="Stlc.html#2632" class="Bound"
      >N</a
      ><a name="2660"
      >
</a
      ><a name="2661" href="Stlc.html#2661" class="Bound"
      >L</a
      ><a name="2662"
      > </a
      ><a name="2663" href="Stlc.html#2616" class="Function Operator"
      >&#10233;&#10216;</a
      ><a name="2665"
      > </a
      ><a name="2666" href="Stlc.html#2666" class="Bound"
      >L&#10233;M</a
      ><a name="2669"
      > </a
      ><a name="2670" href="Stlc.html#2616" class="Function Operator"
      >&#10217;</a
      ><a name="2671"
      > </a
      ><a name="2672" href="Stlc.html#2672" class="Bound"
      >M&#10233;*N</a
      ><a name="2676"
      >  </a
      ><a name="2678" class="Symbol"
      >=</a
      ><a name="2679"
      >  </a
      ><a name="2681" href="Stlc.html#2378" class="InductiveConstructor Operator"
      >&#10216;</a
      ><a name="2682"
      > </a
      ><a name="2683" href="Stlc.html#2666" class="Bound"
      >L&#10233;M</a
      ><a name="2686"
      > </a
      ><a name="2687" href="Stlc.html#2378" class="InductiveConstructor Operator"
      >&#10217;</a
      ><a name="2688"
      > </a
      ><a name="2689" href="Stlc.html#2418" class="InductiveConstructor Operator"
      >&gt;&gt;</a
      ><a name="2691"
      > </a
      ><a name="2692" href="Stlc.html#2672" class="Bound"
      >M&#10233;*N</a
      ><a name="2696"
      >

</a
      ><a name="2698" href="Stlc.html#2698" class="Function Operator"
      >_&#8718;</a
      ><a name="2700"
      > </a
      ><a name="2701" class="Symbol"
      >:</a
      ><a name="2702"
      > </a
      ><a name="2703" class="Symbol"
      >&#8704;</a
      ><a name="2704"
      > </a
      ><a name="2705" href="Stlc.html#2705" class="Bound"
      >M</a
      ><a name="2706"
      > </a
      ><a name="2707" class="Symbol"
      >&#8594;</a
      ><a name="2708"
      > </a
      ><a name="2709" href="Stlc.html#2705" class="Bound"
      >M</a
      ><a name="2710"
      > </a
      ><a name="2711" href="Stlc.html#2491" class="Function Operator"
      >&#10233;*</a
      ><a name="2713"
      > </a
      ><a name="2714" href="Stlc.html#2705" class="Bound"
      >M</a
      ><a name="2715"
      >
</a
      ><a name="2716" href="Stlc.html#2716" class="Bound"
      >M</a
      ><a name="2717"
      > </a
      ><a name="2718" href="Stlc.html#2698" class="Function Operator"
      >&#8718;</a
      ><a name="2719"
      >  </a
      ><a name="2721" class="Symbol"
      >=</a
      ><a name="2722"
      >  </a
      ><a name="2724" href="Stlc.html#2349" class="InductiveConstructor"
      >&#10216;&#10217;</a
      >
{% endraw %}</pre>

## Example reduction derivations

<pre class="Agda">{% raw %}
<a name="2786" href="Stlc.html#2786" class="Function"
      >reduction&#8321;</a
      ><a name="2796"
      > </a
      ><a name="2797" class="Symbol"
      >:</a
      ><a name="2798"
      > </a
      ><a name="2799" href="Stlc.html#962" class="Function"
      >not</a
      ><a name="2802"
      > </a
      ><a name="2803" href="Stlc.html#788" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="2804"
      > </a
      ><a name="2805" href="Stlc.html#815" class="InductiveConstructor"
      >true</a
      ><a name="2809"
      > </a
      ><a name="2810" href="Stlc.html#2491" class="Function Operator"
      >&#10233;*</a
      ><a name="2812"
      > </a
      ><a name="2813" href="Stlc.html#829" class="InductiveConstructor"
      >false</a
      ><a name="2818"
      >
</a
      ><a name="2819" href="Stlc.html#2786" class="Function"
      >reduction&#8321;</a
      ><a name="2829"
      > </a
      ><a name="2830" class="Symbol"
      >=</a
      ><a name="2831"
      >
    </a
      ><a name="2836" href="Stlc.html#962" class="Function"
      >not</a
      ><a name="2839"
      > </a
      ><a name="2840" href="Stlc.html#788" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="2841"
      > </a
      ><a name="2842" href="Stlc.html#815" class="InductiveConstructor"
      >true</a
      ><a name="2846"
      >
  </a
      ><a name="2849" href="Stlc.html#2616" class="Function Operator"
      >&#10233;&#10216;</a
      ><a name="2851"
      > </a
      ><a name="2852" href="Stlc.html#1819" class="InductiveConstructor"
      >&#946;&#8658;</a
      ><a name="2854"
      > </a
      ><a name="2855" href="Stlc.html#1202" class="InductiveConstructor"
      >value-true</a
      ><a name="2865"
      > </a
      ><a name="2866" href="Stlc.html#2616" class="Function Operator"
      >&#10217;</a
      ><a name="2867"
      >
    </a
      ><a name="2872" href="Stlc.html#844" class="InductiveConstructor Operator"
      >if</a
      ><a name="2874"
      > </a
      ><a name="2875" href="Stlc.html#815" class="InductiveConstructor"
      >true</a
      ><a name="2879"
      > </a
      ><a name="2880" href="Stlc.html#844" class="InductiveConstructor Operator"
      >then</a
      ><a name="2884"
      > </a
      ><a name="2885" href="Stlc.html#829" class="InductiveConstructor"
      >false</a
      ><a name="2890"
      > </a
      ><a name="2891" href="Stlc.html#844" class="InductiveConstructor Operator"
      >else</a
      ><a name="2895"
      > </a
      ><a name="2896" href="Stlc.html#815" class="InductiveConstructor"
      >true</a
      ><a name="2900"
      >
  </a
      ><a name="2903" href="Stlc.html#2616" class="Function Operator"
      >&#10233;&#10216;</a
      ><a name="2905"
      > </a
      ><a name="2906" href="Stlc.html#2008" class="InductiveConstructor"
      >&#946;&#120121;&#8321;</a
      ><a name="2909"
      > </a
      ><a name="2910" href="Stlc.html#2616" class="Function Operator"
      >&#10217;</a
      ><a name="2911"
      >
    </a
      ><a name="2916" href="Stlc.html#829" class="InductiveConstructor"
      >false</a
      ><a name="2921"
      >
  </a
      ><a name="2924" href="Stlc.html#2698" class="Function Operator"
      >&#8718;</a
      ><a name="2925"
      >

</a
      ><a name="2927" href="Stlc.html#2927" class="Function"
      >reduction&#8322;</a
      ><a name="2937"
      > </a
      ><a name="2938" class="Symbol"
      >:</a
      ><a name="2939"
      > </a
      ><a name="2940" href="Stlc.html#966" class="Function"
      >two</a
      ><a name="2943"
      > </a
      ><a name="2944" href="Stlc.html#788" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="2945"
      > </a
      ><a name="2946" href="Stlc.html#962" class="Function"
      >not</a
      ><a name="2949"
      > </a
      ><a name="2950" href="Stlc.html#788" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="2951"
      > </a
      ><a name="2952" href="Stlc.html#815" class="InductiveConstructor"
      >true</a
      ><a name="2956"
      > </a
      ><a name="2957" href="Stlc.html#2491" class="Function Operator"
      >&#10233;*</a
      ><a name="2959"
      > </a
      ><a name="2960" href="Stlc.html#815" class="InductiveConstructor"
      >true</a
      ><a name="2964"
      >
</a
      ><a name="2965" href="Stlc.html#2927" class="Function"
      >reduction&#8322;</a
      ><a name="2975"
      > </a
      ><a name="2976" class="Symbol"
      >=</a
      ><a name="2977"
      >
    </a
      ><a name="2982" href="Stlc.html#966" class="Function"
      >two</a
      ><a name="2985"
      > </a
      ><a name="2986" href="Stlc.html#788" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="2987"
      > </a
      ><a name="2988" href="Stlc.html#962" class="Function"
      >not</a
      ><a name="2991"
      > </a
      ><a name="2992" href="Stlc.html#788" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="2993"
      > </a
      ><a name="2994" href="Stlc.html#815" class="InductiveConstructor"
      >true</a
      ><a name="2998"
      >
  </a
      ><a name="3001" href="Stlc.html#2616" class="Function Operator"
      >&#10233;&#10216;</a
      ><a name="3003"
      > </a
      ><a name="3004" href="Stlc.html#1888" class="InductiveConstructor"
      >&#947;&#8658;&#8321;</a
      ><a name="3007"
      > </a
      ><a name="3008" class="Symbol"
      >(</a
      ><a name="3009" href="Stlc.html#1819" class="InductiveConstructor"
      >&#946;&#8658;</a
      ><a name="3011"
      > </a
      ><a name="3012" href="Stlc.html#1153" class="InductiveConstructor"
      >value-&#955;</a
      ><a name="3019" class="Symbol"
      >)</a
      ><a name="3020"
      > </a
      ><a name="3021" href="Stlc.html#2616" class="Function Operator"
      >&#10217;</a
      ><a name="3022"
      >
    </a
      ><a name="3027" class="Symbol"
      >(</a
      ><a name="3028" href="Stlc.html#752" class="InductiveConstructor Operator"
      >&#955;[</a
      ><a name="3030"
      > </a
      ><a name="3031" href="Stlc.html#928" class="Function"
      >x</a
      ><a name="3032"
      > </a
      ><a name="3033" href="Stlc.html#752" class="InductiveConstructor Operator"
      >&#8758;</a
      ><a name="3034"
      > </a
      ><a name="3035" href="Stlc.html#616" class="InductiveConstructor"
      >&#120121;</a
      ><a name="3036"
      > </a
      ><a name="3037" href="Stlc.html#752" class="InductiveConstructor Operator"
      >]</a
      ><a name="3038"
      > </a
      ><a name="3039" href="Stlc.html#962" class="Function"
      >not</a
      ><a name="3042"
      > </a
      ><a name="3043" href="Stlc.html#788" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="3044"
      > </a
      ><a name="3045" class="Symbol"
      >(</a
      ><a name="3046" href="Stlc.html#962" class="Function"
      >not</a
      ><a name="3049"
      > </a
      ><a name="3050" href="Stlc.html#788" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="3051"
      > </a
      ><a name="3052" href="Stlc.html#734" class="InductiveConstructor"
      >var</a
      ><a name="3055"
      > </a
      ><a name="3056" href="Stlc.html#928" class="Function"
      >x</a
      ><a name="3057" class="Symbol"
      >))</a
      ><a name="3059"
      > </a
      ><a name="3060" href="Stlc.html#788" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="3061"
      > </a
      ><a name="3062" href="Stlc.html#815" class="InductiveConstructor"
      >true</a
      ><a name="3066"
      >
  </a
      ><a name="3069" href="Stlc.html#2616" class="Function Operator"
      >&#10233;&#10216;</a
      ><a name="3071"
      > </a
      ><a name="3072" href="Stlc.html#1819" class="InductiveConstructor"
      >&#946;&#8658;</a
      ><a name="3074"
      > </a
      ><a name="3075" href="Stlc.html#1202" class="InductiveConstructor"
      >value-true</a
      ><a name="3085"
      > </a
      ><a name="3086" href="Stlc.html#2616" class="Function Operator"
      >&#10217;</a
      ><a name="3087"
      >
    </a
      ><a name="3092" href="Stlc.html#962" class="Function"
      >not</a
      ><a name="3095"
      > </a
      ><a name="3096" href="Stlc.html#788" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="3097"
      > </a
      ><a name="3098" class="Symbol"
      >(</a
      ><a name="3099" href="Stlc.html#962" class="Function"
      >not</a
      ><a name="3102"
      > </a
      ><a name="3103" href="Stlc.html#788" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="3104"
      > </a
      ><a name="3105" href="Stlc.html#815" class="InductiveConstructor"
      >true</a
      ><a name="3109" class="Symbol"
      >)</a
      ><a name="3110"
      >
  </a
      ><a name="3113" href="Stlc.html#2616" class="Function Operator"
      >&#10233;&#10216;</a
      ><a name="3115"
      > </a
      ><a name="3116" href="Stlc.html#1941" class="InductiveConstructor"
      >&#947;&#8658;&#8322;</a
      ><a name="3119"
      > </a
      ><a name="3120" href="Stlc.html#1153" class="InductiveConstructor"
      >value-&#955;</a
      ><a name="3127"
      > </a
      ><a name="3128" class="Symbol"
      >(</a
      ><a name="3129" href="Stlc.html#1819" class="InductiveConstructor"
      >&#946;&#8658;</a
      ><a name="3131"
      > </a
      ><a name="3132" href="Stlc.html#1202" class="InductiveConstructor"
      >value-true</a
      ><a name="3142" class="Symbol"
      >)</a
      ><a name="3143"
      > </a
      ><a name="3144" href="Stlc.html#2616" class="Function Operator"
      >&#10217;</a
      ><a name="3145"
      >
    </a
      ><a name="3150" href="Stlc.html#962" class="Function"
      >not</a
      ><a name="3153"
      > </a
      ><a name="3154" href="Stlc.html#788" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="3155"
      > </a
      ><a name="3156" class="Symbol"
      >(</a
      ><a name="3157" href="Stlc.html#844" class="InductiveConstructor Operator"
      >if</a
      ><a name="3159"
      > </a
      ><a name="3160" href="Stlc.html#815" class="InductiveConstructor"
      >true</a
      ><a name="3164"
      > </a
      ><a name="3165" href="Stlc.html#844" class="InductiveConstructor Operator"
      >then</a
      ><a name="3169"
      > </a
      ><a name="3170" href="Stlc.html#829" class="InductiveConstructor"
      >false</a
      ><a name="3175"
      > </a
      ><a name="3176" href="Stlc.html#844" class="InductiveConstructor Operator"
      >else</a
      ><a name="3180"
      > </a
      ><a name="3181" href="Stlc.html#815" class="InductiveConstructor"
      >true</a
      ><a name="3185" class="Symbol"
      >)</a
      ><a name="3186"
      >
  </a
      ><a name="3189" href="Stlc.html#2616" class="Function Operator"
      >&#10233;&#10216;</a
      ><a name="3191"
      > </a
      ><a name="3192" href="Stlc.html#1941" class="InductiveConstructor"
      >&#947;&#8658;&#8322;</a
      ><a name="3195"
      > </a
      ><a name="3196" href="Stlc.html#1153" class="InductiveConstructor"
      >value-&#955;</a
      ><a name="3203"
      > </a
      ><a name="3204" href="Stlc.html#2008" class="InductiveConstructor"
      >&#946;&#120121;&#8321;</a
      ><a name="3207"
      > </a
      ><a name="3208" href="Stlc.html#2616" class="Function Operator"
      >&#10217;</a
      ><a name="3209"
      >
    </a
      ><a name="3214" href="Stlc.html#962" class="Function"
      >not</a
      ><a name="3217"
      > </a
      ><a name="3218" href="Stlc.html#788" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="3219"
      > </a
      ><a name="3220" href="Stlc.html#829" class="InductiveConstructor"
      >false</a
      ><a name="3225"
      >
  </a
      ><a name="3228" href="Stlc.html#2616" class="Function Operator"
      >&#10233;&#10216;</a
      ><a name="3230"
      > </a
      ><a name="3231" href="Stlc.html#1819" class="InductiveConstructor"
      >&#946;&#8658;</a
      ><a name="3233"
      > </a
      ><a name="3234" href="Stlc.html#1229" class="InductiveConstructor"
      >value-false</a
      ><a name="3245"
      > </a
      ><a name="3246" href="Stlc.html#2616" class="Function Operator"
      >&#10217;</a
      ><a name="3247"
      >
    </a
      ><a name="3252" href="Stlc.html#844" class="InductiveConstructor Operator"
      >if</a
      ><a name="3254"
      > </a
      ><a name="3255" href="Stlc.html#829" class="InductiveConstructor"
      >false</a
      ><a name="3260"
      > </a
      ><a name="3261" href="Stlc.html#844" class="InductiveConstructor Operator"
      >then</a
      ><a name="3265"
      > </a
      ><a name="3266" href="Stlc.html#829" class="InductiveConstructor"
      >false</a
      ><a name="3271"
      > </a
      ><a name="3272" href="Stlc.html#844" class="InductiveConstructor Operator"
      >else</a
      ><a name="3276"
      > </a
      ><a name="3277" href="Stlc.html#815" class="InductiveConstructor"
      >true</a
      ><a name="3281"
      >
  </a
      ><a name="3284" href="Stlc.html#2616" class="Function Operator"
      >&#10233;&#10216;</a
      ><a name="3286"
      > </a
      ><a name="3287" href="Stlc.html#2056" class="InductiveConstructor"
      >&#946;&#120121;&#8322;</a
      ><a name="3290"
      > </a
      ><a name="3291" href="Stlc.html#2616" class="Function Operator"
      >&#10217;</a
      ><a name="3292"
      >
    </a
      ><a name="3297" href="Stlc.html#815" class="InductiveConstructor"
      >true</a
      ><a name="3301"
      >
  </a
      ><a name="3304" href="Stlc.html#2698" class="Function Operator"
      >&#8718;</a
      >
{% endraw %}</pre>

## Type rules

<pre class="Agda">{% raw %}
<a name="3346" href="Stlc.html#3346" class="Function"
      >Context</a
      ><a name="3353"
      > </a
      ><a name="3354" class="Symbol"
      >:</a
      ><a name="3355"
      > </a
      ><a name="3356" class="PrimitiveType"
      >Set</a
      ><a name="3359"
      >
</a
      ><a name="3360" href="Stlc.html#3346" class="Function"
      >Context</a
      ><a name="3367"
      > </a
      ><a name="3368" class="Symbol"
      >=</a
      ><a name="3369"
      > </a
      ><a name="3370" href="Maps.html#10226" class="Function"
      >PartialMap</a
      ><a name="3380"
      > </a
      ><a name="3381" href="Stlc.html#597" class="Datatype"
      >Type</a
      ><a name="3385"
      >

</a
      ><a name="3387" class="Keyword"
      >infix</a
      ><a name="3392"
      > </a
      ><a name="3393" class="Number"
      >10</a
      ><a name="3395"
      > </a
      ><a name="3396" href="Stlc.html#3408" class="Datatype Operator"
      >_&#8866;_&#8758;_</a
      ><a name="3401"
      >

</a
      ><a name="3403" class="Keyword"
      >data</a
      ><a name="3407"
      > </a
      ><a name="3408" href="Stlc.html#3408" class="Datatype Operator"
      >_&#8866;_&#8758;_</a
      ><a name="3413"
      > </a
      ><a name="3414" class="Symbol"
      >:</a
      ><a name="3415"
      > </a
      ><a name="3416" href="Stlc.html#3346" class="Function"
      >Context</a
      ><a name="3423"
      > </a
      ><a name="3424" class="Symbol"
      >&#8594;</a
      ><a name="3425"
      > </a
      ><a name="3426" href="Stlc.html#715" class="Datatype"
      >Term</a
      ><a name="3430"
      > </a
      ><a name="3431" class="Symbol"
      >&#8594;</a
      ><a name="3432"
      > </a
      ><a name="3433" href="Stlc.html#597" class="Datatype"
      >Type</a
      ><a name="3437"
      > </a
      ><a name="3438" class="Symbol"
      >&#8594;</a
      ><a name="3439"
      > </a
      ><a name="3440" class="PrimitiveType"
      >Set</a
      ><a name="3443"
      > </a
      ><a name="3444" class="Keyword"
      >where</a
      ><a name="3449"
      >
  </a
      ><a name="3452" href="Stlc.html#3452" class="InductiveConstructor"
      >Ax</a
      ><a name="3454"
      > </a
      ><a name="3455" class="Symbol"
      >:</a
      ><a name="3456"
      > </a
      ><a name="3457" class="Symbol"
      >&#8704;</a
      ><a name="3458"
      > </a
      ><a name="3459" class="Symbol"
      >{</a
      ><a name="3460" href="Stlc.html#3460" class="Bound"
      >&#915;</a
      ><a name="3461"
      > </a
      ><a name="3462" href="Stlc.html#3462" class="Bound"
      >x</a
      ><a name="3463"
      > </a
      ><a name="3464" href="Stlc.html#3464" class="Bound"
      >A</a
      ><a name="3465" class="Symbol"
      >}</a
      ><a name="3466"
      > </a
      ><a name="3467" class="Symbol"
      >&#8594;</a
      ><a name="3468"
      >
    </a
      ><a name="3473" href="Stlc.html#3460" class="Bound"
      >&#915;</a
      ><a name="3474"
      > </a
      ><a name="3475" href="Stlc.html#3462" class="Bound"
      >x</a
      ><a name="3476"
      > </a
      ><a name="3477" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="3478"
      > </a
      ><a name="3479" href="https://agda.github.io/agda-stdlib/Data.Maybe.Base.html#373" class="InductiveConstructor"
      >just</a
      ><a name="3483"
      > </a
      ><a name="3484" href="Stlc.html#3464" class="Bound"
      >A</a
      ><a name="3485"
      > </a
      ><a name="3486" class="Symbol"
      >&#8594;</a
      ><a name="3487"
      >
    </a
      ><a name="3492" href="Stlc.html#3460" class="Bound"
      >&#915;</a
      ><a name="3493"
      > </a
      ><a name="3494" href="Stlc.html#3408" class="Datatype Operator"
      >&#8866;</a
      ><a name="3495"
      > </a
      ><a name="3496" href="Stlc.html#734" class="InductiveConstructor"
      >var</a
      ><a name="3499"
      > </a
      ><a name="3500" href="Stlc.html#3462" class="Bound"
      >x</a
      ><a name="3501"
      > </a
      ><a name="3502" href="Stlc.html#3408" class="Datatype Operator"
      >&#8758;</a
      ><a name="3503"
      > </a
      ><a name="3504" href="Stlc.html#3464" class="Bound"
      >A</a
      ><a name="3505"
      >
  </a
      ><a name="3508" href="Stlc.html#3508" class="InductiveConstructor"
      >&#8658;-I</a
      ><a name="3511"
      > </a
      ><a name="3512" class="Symbol"
      >:</a
      ><a name="3513"
      > </a
      ><a name="3514" class="Symbol"
      >&#8704;</a
      ><a name="3515"
      > </a
      ><a name="3516" class="Symbol"
      >{</a
      ><a name="3517" href="Stlc.html#3517" class="Bound"
      >&#915;</a
      ><a name="3518"
      > </a
      ><a name="3519" href="Stlc.html#3519" class="Bound"
      >x</a
      ><a name="3520"
      > </a
      ><a name="3521" href="Stlc.html#3521" class="Bound"
      >N</a
      ><a name="3522"
      > </a
      ><a name="3523" href="Stlc.html#3523" class="Bound"
      >A</a
      ><a name="3524"
      > </a
      ><a name="3525" href="Stlc.html#3525" class="Bound"
      >B</a
      ><a name="3526" class="Symbol"
      >}</a
      ><a name="3527"
      > </a
      ><a name="3528" class="Symbol"
      >&#8594;</a
      ><a name="3529"
      >
    </a
      ><a name="3534" href="Stlc.html#3517" class="Bound"
      >&#915;</a
      ><a name="3535"
      > </a
      ><a name="3536" href="Maps.html#10462" class="Function Operator"
      >,</a
      ><a name="3537"
      > </a
      ><a name="3538" href="Stlc.html#3519" class="Bound"
      >x</a
      ><a name="3539"
      > </a
      ><a name="3540" href="Maps.html#10462" class="Function Operator"
      >&#8758;</a
      ><a name="3541"
      > </a
      ><a name="3542" href="Stlc.html#3523" class="Bound"
      >A</a
      ><a name="3543"
      > </a
      ><a name="3544" href="Stlc.html#3408" class="Datatype Operator"
      >&#8866;</a
      ><a name="3545"
      > </a
      ><a name="3546" href="Stlc.html#3521" class="Bound"
      >N</a
      ><a name="3547"
      > </a
      ><a name="3548" href="Stlc.html#3408" class="Datatype Operator"
      >&#8758;</a
      ><a name="3549"
      > </a
      ><a name="3550" href="Stlc.html#3525" class="Bound"
      >B</a
      ><a name="3551"
      > </a
      ><a name="3552" class="Symbol"
      >&#8594;</a
      ><a name="3553"
      >
    </a
      ><a name="3558" href="Stlc.html#3517" class="Bound"
      >&#915;</a
      ><a name="3559"
      > </a
      ><a name="3560" href="Stlc.html#3408" class="Datatype Operator"
      >&#8866;</a
      ><a name="3561"
      > </a
      ><a name="3562" href="Stlc.html#752" class="InductiveConstructor Operator"
      >&#955;[</a
      ><a name="3564"
      > </a
      ><a name="3565" href="Stlc.html#3519" class="Bound"
      >x</a
      ><a name="3566"
      > </a
      ><a name="3567" href="Stlc.html#752" class="InductiveConstructor Operator"
      >&#8758;</a
      ><a name="3568"
      > </a
      ><a name="3569" href="Stlc.html#3523" class="Bound"
      >A</a
      ><a name="3570"
      > </a
      ><a name="3571" href="Stlc.html#752" class="InductiveConstructor Operator"
      >]</a
      ><a name="3572"
      > </a
      ><a name="3573" href="Stlc.html#3521" class="Bound"
      >N</a
      ><a name="3574"
      > </a
      ><a name="3575" href="Stlc.html#3408" class="Datatype Operator"
      >&#8758;</a
      ><a name="3576"
      > </a
      ><a name="3577" href="Stlc.html#3523" class="Bound"
      >A</a
      ><a name="3578"
      > </a
      ><a name="3579" href="Stlc.html#627" class="InductiveConstructor Operator"
      >&#8658;</a
      ><a name="3580"
      > </a
      ><a name="3581" href="Stlc.html#3525" class="Bound"
      >B</a
      ><a name="3582"
      >
  </a
      ><a name="3585" href="Stlc.html#3585" class="InductiveConstructor"
      >&#8658;-E</a
      ><a name="3588"
      > </a
      ><a name="3589" class="Symbol"
      >:</a
      ><a name="3590"
      > </a
      ><a name="3591" class="Symbol"
      >&#8704;</a
      ><a name="3592"
      > </a
      ><a name="3593" class="Symbol"
      >{</a
      ><a name="3594" href="Stlc.html#3594" class="Bound"
      >&#915;</a
      ><a name="3595"
      > </a
      ><a name="3596" href="Stlc.html#3596" class="Bound"
      >L</a
      ><a name="3597"
      > </a
      ><a name="3598" href="Stlc.html#3598" class="Bound"
      >M</a
      ><a name="3599"
      > </a
      ><a name="3600" href="Stlc.html#3600" class="Bound"
      >A</a
      ><a name="3601"
      > </a
      ><a name="3602" href="Stlc.html#3602" class="Bound"
      >B</a
      ><a name="3603" class="Symbol"
      >}</a
      ><a name="3604"
      > </a
      ><a name="3605" class="Symbol"
      >&#8594;</a
      ><a name="3606"
      >
    </a
      ><a name="3611" href="Stlc.html#3594" class="Bound"
      >&#915;</a
      ><a name="3612"
      > </a
      ><a name="3613" href="Stlc.html#3408" class="Datatype Operator"
      >&#8866;</a
      ><a name="3614"
      > </a
      ><a name="3615" href="Stlc.html#3596" class="Bound"
      >L</a
      ><a name="3616"
      > </a
      ><a name="3617" href="Stlc.html#3408" class="Datatype Operator"
      >&#8758;</a
      ><a name="3618"
      > </a
      ><a name="3619" href="Stlc.html#3600" class="Bound"
      >A</a
      ><a name="3620"
      > </a
      ><a name="3621" href="Stlc.html#627" class="InductiveConstructor Operator"
      >&#8658;</a
      ><a name="3622"
      > </a
      ><a name="3623" href="Stlc.html#3602" class="Bound"
      >B</a
      ><a name="3624"
      > </a
      ><a name="3625" class="Symbol"
      >&#8594;</a
      ><a name="3626"
      >
    </a
      ><a name="3631" href="Stlc.html#3594" class="Bound"
      >&#915;</a
      ><a name="3632"
      > </a
      ><a name="3633" href="Stlc.html#3408" class="Datatype Operator"
      >&#8866;</a
      ><a name="3634"
      > </a
      ><a name="3635" href="Stlc.html#3598" class="Bound"
      >M</a
      ><a name="3636"
      > </a
      ><a name="3637" href="Stlc.html#3408" class="Datatype Operator"
      >&#8758;</a
      ><a name="3638"
      > </a
      ><a name="3639" href="Stlc.html#3600" class="Bound"
      >A</a
      ><a name="3640"
      > </a
      ><a name="3641" class="Symbol"
      >&#8594;</a
      ><a name="3642"
      >
    </a
      ><a name="3647" href="Stlc.html#3594" class="Bound"
      >&#915;</a
      ><a name="3648"
      > </a
      ><a name="3649" href="Stlc.html#3408" class="Datatype Operator"
      >&#8866;</a
      ><a name="3650"
      > </a
      ><a name="3651" href="Stlc.html#3596" class="Bound"
      >L</a
      ><a name="3652"
      > </a
      ><a name="3653" href="Stlc.html#788" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="3654"
      > </a
      ><a name="3655" href="Stlc.html#3598" class="Bound"
      >M</a
      ><a name="3656"
      > </a
      ><a name="3657" href="Stlc.html#3408" class="Datatype Operator"
      >&#8758;</a
      ><a name="3658"
      > </a
      ><a name="3659" href="Stlc.html#3602" class="Bound"
      >B</a
      ><a name="3660"
      >
  </a
      ><a name="3663" href="Stlc.html#3663" class="InductiveConstructor"
      >&#120121;-I&#8321;</a
      ><a name="3667"
      > </a
      ><a name="3668" class="Symbol"
      >:</a
      ><a name="3669"
      > </a
      ><a name="3670" class="Symbol"
      >&#8704;</a
      ><a name="3671"
      > </a
      ><a name="3672" class="Symbol"
      >{</a
      ><a name="3673" href="Stlc.html#3673" class="Bound"
      >&#915;</a
      ><a name="3674" class="Symbol"
      >}</a
      ><a name="3675"
      > </a
      ><a name="3676" class="Symbol"
      >&#8594;</a
      ><a name="3677"
      >
    </a
      ><a name="3682" href="Stlc.html#3673" class="Bound"
      >&#915;</a
      ><a name="3683"
      > </a
      ><a name="3684" href="Stlc.html#3408" class="Datatype Operator"
      >&#8866;</a
      ><a name="3685"
      > </a
      ><a name="3686" href="Stlc.html#815" class="InductiveConstructor"
      >true</a
      ><a name="3690"
      > </a
      ><a name="3691" href="Stlc.html#3408" class="Datatype Operator"
      >&#8758;</a
      ><a name="3692"
      > </a
      ><a name="3693" href="Stlc.html#616" class="InductiveConstructor"
      >&#120121;</a
      ><a name="3694"
      >
  </a
      ><a name="3697" href="Stlc.html#3697" class="InductiveConstructor"
      >&#120121;-I&#8322;</a
      ><a name="3701"
      > </a
      ><a name="3702" class="Symbol"
      >:</a
      ><a name="3703"
      > </a
      ><a name="3704" class="Symbol"
      >&#8704;</a
      ><a name="3705"
      > </a
      ><a name="3706" class="Symbol"
      >{</a
      ><a name="3707" href="Stlc.html#3707" class="Bound"
      >&#915;</a
      ><a name="3708" class="Symbol"
      >}</a
      ><a name="3709"
      > </a
      ><a name="3710" class="Symbol"
      >&#8594;</a
      ><a name="3711"
      >
    </a
      ><a name="3716" href="Stlc.html#3707" class="Bound"
      >&#915;</a
      ><a name="3717"
      > </a
      ><a name="3718" href="Stlc.html#3408" class="Datatype Operator"
      >&#8866;</a
      ><a name="3719"
      > </a
      ><a name="3720" href="Stlc.html#829" class="InductiveConstructor"
      >false</a
      ><a name="3725"
      > </a
      ><a name="3726" href="Stlc.html#3408" class="Datatype Operator"
      >&#8758;</a
      ><a name="3727"
      > </a
      ><a name="3728" href="Stlc.html#616" class="InductiveConstructor"
      >&#120121;</a
      ><a name="3729"
      >
  </a
      ><a name="3732" href="Stlc.html#3732" class="InductiveConstructor"
      >&#120121;-E</a
      ><a name="3735"
      > </a
      ><a name="3736" class="Symbol"
      >:</a
      ><a name="3737"
      > </a
      ><a name="3738" class="Symbol"
      >&#8704;</a
      ><a name="3739"
      > </a
      ><a name="3740" class="Symbol"
      >{</a
      ><a name="3741" href="Stlc.html#3741" class="Bound"
      >&#915;</a
      ><a name="3742"
      > </a
      ><a name="3743" href="Stlc.html#3743" class="Bound"
      >L</a
      ><a name="3744"
      > </a
      ><a name="3745" href="Stlc.html#3745" class="Bound"
      >M</a
      ><a name="3746"
      > </a
      ><a name="3747" href="Stlc.html#3747" class="Bound"
      >N</a
      ><a name="3748"
      > </a
      ><a name="3749" href="Stlc.html#3749" class="Bound"
      >A</a
      ><a name="3750" class="Symbol"
      >}</a
      ><a name="3751"
      > </a
      ><a name="3752" class="Symbol"
      >&#8594;</a
      ><a name="3753"
      >
    </a
      ><a name="3758" href="Stlc.html#3741" class="Bound"
      >&#915;</a
      ><a name="3759"
      > </a
      ><a name="3760" href="Stlc.html#3408" class="Datatype Operator"
      >&#8866;</a
      ><a name="3761"
      > </a
      ><a name="3762" href="Stlc.html#3743" class="Bound"
      >L</a
      ><a name="3763"
      > </a
      ><a name="3764" href="Stlc.html#3408" class="Datatype Operator"
      >&#8758;</a
      ><a name="3765"
      > </a
      ><a name="3766" href="Stlc.html#616" class="InductiveConstructor"
      >&#120121;</a
      ><a name="3767"
      > </a
      ><a name="3768" class="Symbol"
      >&#8594;</a
      ><a name="3769"
      >
    </a
      ><a name="3774" href="Stlc.html#3741" class="Bound"
      >&#915;</a
      ><a name="3775"
      > </a
      ><a name="3776" href="Stlc.html#3408" class="Datatype Operator"
      >&#8866;</a
      ><a name="3777"
      > </a
      ><a name="3778" href="Stlc.html#3745" class="Bound"
      >M</a
      ><a name="3779"
      > </a
      ><a name="3780" href="Stlc.html#3408" class="Datatype Operator"
      >&#8758;</a
      ><a name="3781"
      > </a
      ><a name="3782" href="Stlc.html#3749" class="Bound"
      >A</a
      ><a name="3783"
      > </a
      ><a name="3784" class="Symbol"
      >&#8594;</a
      ><a name="3785"
      >
    </a
      ><a name="3790" href="Stlc.html#3741" class="Bound"
      >&#915;</a
      ><a name="3791"
      > </a
      ><a name="3792" href="Stlc.html#3408" class="Datatype Operator"
      >&#8866;</a
      ><a name="3793"
      > </a
      ><a name="3794" href="Stlc.html#3747" class="Bound"
      >N</a
      ><a name="3795"
      > </a
      ><a name="3796" href="Stlc.html#3408" class="Datatype Operator"
      >&#8758;</a
      ><a name="3797"
      > </a
      ><a name="3798" href="Stlc.html#3749" class="Bound"
      >A</a
      ><a name="3799"
      > </a
      ><a name="3800" class="Symbol"
      >&#8594;</a
      ><a name="3801"
      >
    </a
      ><a name="3806" href="Stlc.html#3741" class="Bound"
      >&#915;</a
      ><a name="3807"
      > </a
      ><a name="3808" href="Stlc.html#3408" class="Datatype Operator"
      >&#8866;</a
      ><a name="3809"
      > </a
      ><a name="3810" href="Stlc.html#844" class="InductiveConstructor Operator"
      >if</a
      ><a name="3812"
      > </a
      ><a name="3813" href="Stlc.html#3743" class="Bound"
      >L</a
      ><a name="3814"
      > </a
      ><a name="3815" href="Stlc.html#844" class="InductiveConstructor Operator"
      >then</a
      ><a name="3819"
      > </a
      ><a name="3820" href="Stlc.html#3745" class="Bound"
      >M</a
      ><a name="3821"
      > </a
      ><a name="3822" href="Stlc.html#844" class="InductiveConstructor Operator"
      >else</a
      ><a name="3826"
      > </a
      ><a name="3827" href="Stlc.html#3747" class="Bound"
      >N</a
      ><a name="3828"
      > </a
      ><a name="3829" href="Stlc.html#3408" class="Datatype Operator"
      >&#8758;</a
      ><a name="3830"
      > </a
      ><a name="3831" href="Stlc.html#3749" class="Bound"
      >A</a
      >
{% endraw %}</pre>

## Example type derivations

<pre class="Agda">{% raw %}
<a name="3891" href="Stlc.html#3891" class="Function"
      >typing&#8321;</a
      ><a name="3898"
      > </a
      ><a name="3899" class="Symbol"
      >:</a
      ><a name="3900"
      > </a
      ><a name="3901" href="Maps.html#10359" class="Function"
      >&#8709;</a
      ><a name="3902"
      > </a
      ><a name="3903" href="Stlc.html#3408" class="Datatype Operator"
      >&#8866;</a
      ><a name="3904"
      > </a
      ><a name="3905" href="Stlc.html#962" class="Function"
      >not</a
      ><a name="3908"
      > </a
      ><a name="3909" href="Stlc.html#3408" class="Datatype Operator"
      >&#8758;</a
      ><a name="3910"
      > </a
      ><a name="3911" href="Stlc.html#616" class="InductiveConstructor"
      >&#120121;</a
      ><a name="3912"
      > </a
      ><a name="3913" href="Stlc.html#627" class="InductiveConstructor Operator"
      >&#8658;</a
      ><a name="3914"
      > </a
      ><a name="3915" href="Stlc.html#616" class="InductiveConstructor"
      >&#120121;</a
      ><a name="3916"
      >
</a
      ><a name="3917" href="Stlc.html#3891" class="Function"
      >typing&#8321;</a
      ><a name="3924"
      > </a
      ><a name="3925" class="Symbol"
      >=</a
      ><a name="3926"
      > </a
      ><a name="3927" href="Stlc.html#3508" class="InductiveConstructor"
      >&#8658;-I</a
      ><a name="3930"
      > </a
      ><a name="3931" class="Symbol"
      >(</a
      ><a name="3932" href="Stlc.html#3732" class="InductiveConstructor"
      >&#120121;-E</a
      ><a name="3935"
      > </a
      ><a name="3936" class="Symbol"
      >(</a
      ><a name="3937" href="Stlc.html#3452" class="InductiveConstructor"
      >Ax</a
      ><a name="3939"
      > </a
      ><a name="3940" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="3944" class="Symbol"
      >)</a
      ><a name="3945"
      > </a
      ><a name="3946" href="Stlc.html#3697" class="InductiveConstructor"
      >&#120121;-I&#8322;</a
      ><a name="3950"
      > </a
      ><a name="3951" href="Stlc.html#3663" class="InductiveConstructor"
      >&#120121;-I&#8321;</a
      ><a name="3955" class="Symbol"
      >)</a
      ><a name="3956"
      >

</a
      ><a name="3958" href="Stlc.html#3958" class="Function"
      >typing&#8322;</a
      ><a name="3965"
      > </a
      ><a name="3966" class="Symbol"
      >:</a
      ><a name="3967"
      > </a
      ><a name="3968" href="Maps.html#10359" class="Function"
      >&#8709;</a
      ><a name="3969"
      > </a
      ><a name="3970" href="Stlc.html#3408" class="Datatype Operator"
      >&#8866;</a
      ><a name="3971"
      > </a
      ><a name="3972" href="Stlc.html#966" class="Function"
      >two</a
      ><a name="3975"
      > </a
      ><a name="3976" href="Stlc.html#3408" class="Datatype Operator"
      >&#8758;</a
      ><a name="3977"
      > </a
      ><a name="3978" class="Symbol"
      >(</a
      ><a name="3979" href="Stlc.html#616" class="InductiveConstructor"
      >&#120121;</a
      ><a name="3980"
      > </a
      ><a name="3981" href="Stlc.html#627" class="InductiveConstructor Operator"
      >&#8658;</a
      ><a name="3982"
      > </a
      ><a name="3983" href="Stlc.html#616" class="InductiveConstructor"
      >&#120121;</a
      ><a name="3984" class="Symbol"
      >)</a
      ><a name="3985"
      > </a
      ><a name="3986" href="Stlc.html#627" class="InductiveConstructor Operator"
      >&#8658;</a
      ><a name="3987"
      > </a
      ><a name="3988" href="Stlc.html#616" class="InductiveConstructor"
      >&#120121;</a
      ><a name="3989"
      > </a
      ><a name="3990" href="Stlc.html#627" class="InductiveConstructor Operator"
      >&#8658;</a
      ><a name="3991"
      > </a
      ><a name="3992" href="Stlc.html#616" class="InductiveConstructor"
      >&#120121;</a
      ><a name="3993"
      >
</a
      ><a name="3994" href="Stlc.html#3958" class="Function"
      >typing&#8322;</a
      ><a name="4001"
      > </a
      ><a name="4002" class="Symbol"
      >=</a
      ><a name="4003"
      > </a
      ><a name="4004" href="Stlc.html#3508" class="InductiveConstructor"
      >&#8658;-I</a
      ><a name="4007"
      > </a
      ><a name="4008" class="Symbol"
      >(</a
      ><a name="4009" href="Stlc.html#3508" class="InductiveConstructor"
      >&#8658;-I</a
      ><a name="4012"
      > </a
      ><a name="4013" class="Symbol"
      >(</a
      ><a name="4014" href="Stlc.html#3585" class="InductiveConstructor"
      >&#8658;-E</a
      ><a name="4017"
      > </a
      ><a name="4018" class="Symbol"
      >(</a
      ><a name="4019" href="Stlc.html#3452" class="InductiveConstructor"
      >Ax</a
      ><a name="4021"
      > </a
      ><a name="4022" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="4026" class="Symbol"
      >)</a
      ><a name="4027"
      > </a
      ><a name="4028" class="Symbol"
      >(</a
      ><a name="4029" href="Stlc.html#3585" class="InductiveConstructor"
      >&#8658;-E</a
      ><a name="4032"
      > </a
      ><a name="4033" class="Symbol"
      >(</a
      ><a name="4034" href="Stlc.html#3452" class="InductiveConstructor"
      >Ax</a
      ><a name="4036"
      > </a
      ><a name="4037" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="4041" class="Symbol"
      >)</a
      ><a name="4042"
      > </a
      ><a name="4043" class="Symbol"
      >(</a
      ><a name="4044" href="Stlc.html#3452" class="InductiveConstructor"
      >Ax</a
      ><a name="4046"
      > </a
      ><a name="4047" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="4051" class="Symbol"
      >))))</a
      >
{% endraw %}</pre>

Construction of a type derivation is best done interactively.
We start with the declaration:

    typing₁ : ∅ ⊢ not ∶ 𝔹 ⇒ 𝔹
    typing₁ = ?

Typing C-L (control L) causes Agda to create a hole and tell us its
expected type.

    typing₁ = { }0
    ?0 : ∅ ⊢ not ∶ 𝔹 ⇒ 𝔹

Now we fill in the hole by typing C-R (control R). Agda observes that
the outermost term in `not` in a `λ`, which is typed using `⇒-I`. The
`⇒-I` rule in turn takes one argument, which Agda leaves as a hole.

    typing₁ = ⇒-I { }0
    ?0 : ∅ , x ∶ 𝔹 ⊢ if var x then false else true ∶ 𝔹

Again we fill in the hole by typing C-R. Agda observes that the
outermost term is now `if_then_else_`, which is typed using `𝔹-E`. The
`𝔹-E` rule in turn takes three arguments, which Agda leaves as holes.

    typing₁ = ⇒-I (𝔹-E { }0 { }1 { }2)
    ?0 : ∅ , x ∶ 𝔹 ⊢ var x ∶
    ?1 : ∅ , x ∶ 𝔹 ⊢ false ∶ 𝔹
    ?2 : ∅ , x ∶ 𝔹 ⊢ true ∶ 𝔹

Again we fill in the three holes by typing C-R in each. Agda observes
that `var x`, `false`, and `true` are typed using `Ax`, `𝔹-I₂`, and
`𝔹-I₁` respectively. The `Ax` rule in turn takes an argument, to show
that `(∅ , x ∶ 𝔹) x = just 𝔹`, which can in turn be specified with a
hole. After filling in all holes, the term is as above.


