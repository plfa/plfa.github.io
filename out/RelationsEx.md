---
title     : "Relations Exercises"
layout    : page
permalink : /RelationsEx
---

## Imports

<pre class="Agda">{% raw %}
<a name="111" class="Keyword"
      >open</a
      ><a name="115"
      > </a
      ><a name="116" class="Keyword"
      >import</a
      ><a name="122"
      > </a
      ><a name="123" class="Module"
      >Naturals</a
      ><a name="131"
      > </a
      ><a name="132" class="Keyword"
      >using</a
      ><a name="137"
      > </a
      ><a name="138" class="Symbol"
      >(</a
      ><a name="139" href="Naturals.html#1064" class="Datatype"
      >&#8469;</a
      ><a name="140" class="Symbol"
      >;</a
      ><a name="141"
      > </a
      ><a name="142" href="Naturals.html#1080" class="InductiveConstructor"
      >zero</a
      ><a name="146" class="Symbol"
      >;</a
      ><a name="147"
      > </a
      ><a name="148" href="Naturals.html#1091" class="InductiveConstructor"
      >suc</a
      ><a name="151" class="Symbol"
      >;</a
      ><a name="152"
      > </a
      ><a name="153" href="Naturals.html#9439" class="Primitive Operator"
      >_+_</a
      ><a name="156" class="Symbol"
      >;</a
      ><a name="157"
      > </a
      ><a name="158" href="Naturals.html#12016" class="Primitive Operator"
      >_*_</a
      ><a name="161" class="Symbol"
      >;</a
      ><a name="162"
      > </a
      ><a name="163" href="Naturals.html#13851" class="Primitive Operator"
      >_&#8760;_</a
      ><a name="166" class="Symbol"
      >)</a
      ><a name="167"
      >
</a
      ><a name="168" class="Keyword"
      >open</a
      ><a name="172"
      > </a
      ><a name="173" class="Keyword"
      >import</a
      ><a name="179"
      > </a
      ><a name="180" class="Module"
      >Relations</a
      ><a name="189"
      > </a
      ><a name="190" class="Keyword"
      >using</a
      ><a name="195"
      > </a
      ><a name="196" class="Symbol"
      >(</a
      ><a name="197" href="Relations.html#1114" class="Datatype Operator"
      >_&#8804;_</a
      ><a name="200" class="Symbol"
      >;</a
      ><a name="201"
      > </a
      ><a name="202" href="Relations.html#15375" class="Datatype Operator"
      >_&lt;_</a
      ><a name="205" class="Symbol"
      >;</a
      ><a name="206"
      > </a
      ><a name="207" href="Relations.html#16129" class="Datatype"
      >Trichotomy</a
      ><a name="217" class="Symbol"
      >;</a
      ><a name="218"
      > </a
      ><a name="219" href="Relations.html#17213" class="Datatype"
      >even</a
      ><a name="223" class="Symbol"
      >;</a
      ><a name="224"
      > </a
      ><a name="225" href="Relations.html#17311" class="Datatype"
      >odd</a
      ><a name="228" class="Symbol"
      >)</a
      ><a name="229"
      >
</a
      ><a name="230" class="Keyword"
      >open</a
      ><a name="234"
      > </a
      ><a name="235" class="Keyword"
      >import</a
      ><a name="241"
      > </a
      ><a name="242" class="Module"
      >Properties</a
      ><a name="252"
      > </a
      ><a name="253" class="Keyword"
      >using</a
      ><a name="258"
      > </a
      ><a name="259" class="Symbol"
      >(</a
      ><a name="260" href="Properties.html#17070" class="Function"
      >+-comm</a
      ><a name="266" class="Symbol"
      >;</a
      ><a name="267"
      > </a
      ><a name="268" href="Properties.html#16853" class="Function"
      >+-identity</a
      ><a name="278" class="Symbol"
      >;</a
      ><a name="279"
      > </a
      ><a name="280" href="Properties.html#16962" class="Function"
      >+-suc</a
      ><a name="285" class="Symbol"
      >)</a
      ><a name="286"
      >
</a
      ><a name="287" class="Keyword"
      >open</a
      ><a name="291"
      > </a
      ><a name="292" class="Keyword"
      >import</a
      ><a name="298"
      > </a
      ><a name="299" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#1" class="Module"
      >Relation.Binary.PropositionalEquality</a
      ><a name="336"
      > </a
      ><a name="337" class="Keyword"
      >using</a
      ><a name="342"
      > </a
      ><a name="343" class="Symbol"
      >(</a
      ><a name="344" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >_&#8801;_</a
      ><a name="347" class="Symbol"
      >;</a
      ><a name="348"
      > </a
      ><a name="349" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="353" class="Symbol"
      >;</a
      ><a name="354"
      > </a
      ><a name="355" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.Core.html#565" class="Function"
      >sym</a
      ><a name="358" class="Symbol"
      >)</a
      ><a name="359"
      >
</a
      ><a name="360" class="Keyword"
      >open</a
      ><a name="364"
      > </a
      ><a name="365" class="Keyword"
      >import</a
      ><a name="371"
      > </a
      ><a name="372" href="https://agda.github.io/agda-stdlib/Data.Product.html#1" class="Module"
      >Data.Product</a
      ><a name="384"
      > </a
      ><a name="385" class="Keyword"
      >using</a
      ><a name="390"
      > </a
      ><a name="391" class="Symbol"
      >(</a
      ><a name="392" href="https://agda.github.io/agda-stdlib/Data.Product.html#823" class="Function"
      >&#8707;</a
      ><a name="393" class="Symbol"
      >;</a
      ><a name="394"
      > </a
      ><a name="395" href="https://agda.github.io/agda-stdlib/Data.Product.html#509" class="InductiveConstructor Operator"
      >_,_</a
      ><a name="398" class="Symbol"
      >)</a
      ><a name="399"
      >
</a
      ><a name="400" class="Keyword"
      >open</a
      ><a name="404"
      > </a
      ><a name="405" href="Relations.html#16129" class="Module"
      >Trichotomy</a
      ><a name="415"
      >
</a
      ><a name="416" class="Keyword"
      >open</a
      ><a name="420"
      > </a
      ><a name="421" href="Relations.html#15375" class="Module Operator"
      >_&lt;_</a
      ><a name="424"
      >
</a
      ><a name="425" class="Keyword"
      >open</a
      ><a name="429"
      > </a
      ><a name="430" href="Relations.html#1114" class="Module Operator"
      >_&#8804;_</a
      ><a name="433"
      >
</a
      ><a name="434" class="Keyword"
      >open</a
      ><a name="438"
      > </a
      ><a name="439" href="Relations.html#17213" class="Module"
      >even</a
      ><a name="443"
      >
</a
      ><a name="444" class="Keyword"
      >open</a
      ><a name="448"
      > </a
      ><a name="449" href="Relations.html#17311" class="Module"
      >odd</a
      >
{% endraw %}</pre>

*Trichotomy*

<pre class="Agda">{% raw %}
<a name="492" href="RelationsEx.html#492" class="Function"
      >trichotomy</a
      ><a name="502"
      > </a
      ><a name="503" class="Symbol"
      >:</a
      ><a name="504"
      > </a
      ><a name="505" class="Symbol"
      >&#8704;</a
      ><a name="506"
      > </a
      ><a name="507" class="Symbol"
      >(</a
      ><a name="508" href="RelationsEx.html#508" class="Bound"
      >m</a
      ><a name="509"
      > </a
      ><a name="510" href="RelationsEx.html#510" class="Bound"
      >n</a
      ><a name="511"
      > </a
      ><a name="512" class="Symbol"
      >:</a
      ><a name="513"
      > </a
      ><a name="514" href="Naturals.html#1064" class="Datatype"
      >&#8469;</a
      ><a name="515" class="Symbol"
      >)</a
      ><a name="516"
      > </a
      ><a name="517" class="Symbol"
      >&#8594;</a
      ><a name="518"
      > </a
      ><a name="519" href="Relations.html#16129" class="Datatype"
      >Trichotomy</a
      ><a name="529"
      > </a
      ><a name="530" href="RelationsEx.html#508" class="Bound"
      >m</a
      ><a name="531"
      > </a
      ><a name="532" href="RelationsEx.html#510" class="Bound"
      >n</a
      ><a name="533"
      >
</a
      ><a name="534" href="RelationsEx.html#492" class="Function"
      >trichotomy</a
      ><a name="544"
      > </a
      ><a name="545" href="Naturals.html#1080" class="InductiveConstructor"
      >zero</a
      ><a name="549"
      > </a
      ><a name="550" href="Naturals.html#1080" class="InductiveConstructor"
      >zero</a
      ><a name="554"
      > </a
      ><a name="555" class="Symbol"
      >=</a
      ><a name="556"
      > </a
      ><a name="557" href="Relations.html#16208" class="InductiveConstructor"
      >same</a
      ><a name="561"
      > </a
      ><a name="562" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="566"
      >
</a
      ><a name="567" href="RelationsEx.html#492" class="Function"
      >trichotomy</a
      ><a name="577"
      > </a
      ><a name="578" href="Naturals.html#1080" class="InductiveConstructor"
      >zero</a
      ><a name="582"
      > </a
      ><a name="583" class="Symbol"
      >(</a
      ><a name="584" href="Naturals.html#1091" class="InductiveConstructor"
      >suc</a
      ><a name="587"
      > </a
      ><a name="588" href="RelationsEx.html#588" class="Bound"
      >n</a
      ><a name="589" class="Symbol"
      >)</a
      ><a name="590"
      > </a
      ><a name="591" class="Symbol"
      >=</a
      ><a name="592"
      > </a
      ><a name="593" href="Relations.html#16162" class="InductiveConstructor"
      >less</a
      ><a name="597"
      > </a
      ><a name="598" href="Relations.html#15401" class="InductiveConstructor"
      >z&lt;s</a
      ><a name="601"
      >
</a
      ><a name="602" href="RelationsEx.html#492" class="Function"
      >trichotomy</a
      ><a name="612"
      > </a
      ><a name="613" class="Symbol"
      >(</a
      ><a name="614" href="Naturals.html#1091" class="InductiveConstructor"
      >suc</a
      ><a name="617"
      > </a
      ><a name="618" href="RelationsEx.html#618" class="Bound"
      >m</a
      ><a name="619" class="Symbol"
      >)</a
      ><a name="620"
      > </a
      ><a name="621" href="Naturals.html#1080" class="InductiveConstructor"
      >zero</a
      ><a name="625"
      > </a
      ><a name="626" class="Symbol"
      >=</a
      ><a name="627"
      > </a
      ><a name="628" href="Relations.html#16254" class="InductiveConstructor"
      >more</a
      ><a name="632"
      > </a
      ><a name="633" href="Relations.html#15401" class="InductiveConstructor"
      >z&lt;s</a
      ><a name="636"
      >
</a
      ><a name="637" href="RelationsEx.html#492" class="Function"
      >trichotomy</a
      ><a name="647"
      > </a
      ><a name="648" class="Symbol"
      >(</a
      ><a name="649" href="Naturals.html#1091" class="InductiveConstructor"
      >suc</a
      ><a name="652"
      > </a
      ><a name="653" href="RelationsEx.html#653" class="Bound"
      >m</a
      ><a name="654" class="Symbol"
      >)</a
      ><a name="655"
      > </a
      ><a name="656" class="Symbol"
      >(</a
      ><a name="657" href="Naturals.html#1091" class="InductiveConstructor"
      >suc</a
      ><a name="660"
      > </a
      ><a name="661" href="RelationsEx.html#661" class="Bound"
      >n</a
      ><a name="662" class="Symbol"
      >)</a
      ><a name="663"
      > </a
      ><a name="664" class="Keyword"
      >with</a
      ><a name="668"
      > </a
      ><a name="669" href="RelationsEx.html#492" class="Function"
      >trichotomy</a
      ><a name="679"
      > </a
      ><a name="680" href="RelationsEx.html#653" class="Bound"
      >m</a
      ><a name="681"
      > </a
      ><a name="682" href="RelationsEx.html#661" class="Bound"
      >n</a
      ><a name="683"
      >
</a
      ><a name="684" class="Symbol"
      >...</a
      ><a name="687"
      > </a
      ><a name="688" class="Symbol"
      >|</a
      ><a name="689"
      > </a
      ><a name="690" href="Relations.html#16162" class="InductiveConstructor"
      >less</a
      ><a name="694"
      > </a
      ><a name="695" href="RelationsEx.html#695" class="Bound"
      >m&lt;n</a
      ><a name="698"
      > </a
      ><a name="699" class="Symbol"
      >=</a
      ><a name="700"
      > </a
      ><a name="701" href="Relations.html#16162" class="InductiveConstructor"
      >less</a
      ><a name="705"
      > </a
      ><a name="706" class="Symbol"
      >(</a
      ><a name="707" href="Relations.html#15434" class="InductiveConstructor"
      >s&lt;s</a
      ><a name="710"
      > </a
      ><a name="711" href="RelationsEx.html#695" class="Bound"
      >m&lt;n</a
      ><a name="714" class="Symbol"
      >)</a
      ><a name="715"
      >
</a
      ><a name="716" class="Symbol"
      >...</a
      ><a name="719"
      > </a
      ><a name="720" class="Symbol"
      >|</a
      ><a name="721"
      > </a
      ><a name="722" href="Relations.html#16208" class="InductiveConstructor"
      >same</a
      ><a name="726"
      > </a
      ><a name="727" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="731"
      > </a
      ><a name="732" class="Symbol"
      >=</a
      ><a name="733"
      > </a
      ><a name="734" href="Relations.html#16208" class="InductiveConstructor"
      >same</a
      ><a name="738"
      > </a
      ><a name="739" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="743"
      >
</a
      ><a name="744" class="Symbol"
      >...</a
      ><a name="747"
      > </a
      ><a name="748" class="Symbol"
      >|</a
      ><a name="749"
      > </a
      ><a name="750" href="Relations.html#16254" class="InductiveConstructor"
      >more</a
      ><a name="754"
      > </a
      ><a name="755" href="RelationsEx.html#755" class="Bound"
      >n&lt;m</a
      ><a name="758"
      > </a
      ><a name="759" class="Symbol"
      >=</a
      ><a name="760"
      > </a
      ><a name="761" href="Relations.html#16254" class="InductiveConstructor"
      >more</a
      ><a name="765"
      > </a
      ><a name="766" class="Symbol"
      >(</a
      ><a name="767" href="Relations.html#15434" class="InductiveConstructor"
      >s&lt;s</a
      ><a name="770"
      > </a
      ><a name="771" href="RelationsEx.html#755" class="Bound"
      >n&lt;m</a
      ><a name="774" class="Symbol"
      >)</a
      >
{% endraw %}</pre>

*Relate strict comparison to comparison*

<pre class="Agda">{% raw %}
<a name="843" href="RelationsEx.html#843" class="Function"
      >&lt;-implies-&#8804;</a
      ><a name="854"
      > </a
      ><a name="855" class="Symbol"
      >:</a
      ><a name="856"
      > </a
      ><a name="857" class="Symbol"
      >&#8704;</a
      ><a name="858"
      > </a
      ><a name="859" class="Symbol"
      >{</a
      ><a name="860" href="RelationsEx.html#860" class="Bound"
      >m</a
      ><a name="861"
      > </a
      ><a name="862" href="RelationsEx.html#862" class="Bound"
      >n</a
      ><a name="863"
      > </a
      ><a name="864" class="Symbol"
      >:</a
      ><a name="865"
      > </a
      ><a name="866" href="Naturals.html#1064" class="Datatype"
      >&#8469;</a
      ><a name="867" class="Symbol"
      >}</a
      ><a name="868"
      > </a
      ><a name="869" class="Symbol"
      >&#8594;</a
      ><a name="870"
      > </a
      ><a name="871" href="RelationsEx.html#860" class="Bound"
      >m</a
      ><a name="872"
      > </a
      ><a name="873" href="Relations.html#15375" class="Datatype Operator"
      >&lt;</a
      ><a name="874"
      > </a
      ><a name="875" href="RelationsEx.html#862" class="Bound"
      >n</a
      ><a name="876"
      > </a
      ><a name="877" class="Symbol"
      >&#8594;</a
      ><a name="878"
      > </a
      ><a name="879" href="Naturals.html#1091" class="InductiveConstructor"
      >suc</a
      ><a name="882"
      > </a
      ><a name="883" href="RelationsEx.html#860" class="Bound"
      >m</a
      ><a name="884"
      > </a
      ><a name="885" href="Relations.html#1114" class="Datatype Operator"
      >&#8804;</a
      ><a name="886"
      > </a
      ><a name="887" href="RelationsEx.html#862" class="Bound"
      >n</a
      ><a name="888"
      >
</a
      ><a name="889" href="RelationsEx.html#843" class="Function"
      >&lt;-implies-&#8804;</a
      ><a name="900"
      > </a
      ><a name="901" href="Relations.html#15401" class="InductiveConstructor"
      >z&lt;s</a
      ><a name="904"
      > </a
      ><a name="905" class="Symbol"
      >=</a
      ><a name="906"
      > </a
      ><a name="907" href="Relations.html#1169" class="InductiveConstructor"
      >s&#8804;s</a
      ><a name="910"
      > </a
      ><a name="911" href="Relations.html#1140" class="InductiveConstructor"
      >z&#8804;n</a
      ><a name="914"
      >
</a
      ><a name="915" href="RelationsEx.html#843" class="Function"
      >&lt;-implies-&#8804;</a
      ><a name="926"
      > </a
      ><a name="927" class="Symbol"
      >(</a
      ><a name="928" href="Relations.html#15434" class="InductiveConstructor"
      >s&lt;s</a
      ><a name="931"
      > </a
      ><a name="932" href="RelationsEx.html#932" class="Bound"
      >m&lt;n</a
      ><a name="935" class="Symbol"
      >)</a
      ><a name="936"
      > </a
      ><a name="937" class="Symbol"
      >=</a
      ><a name="938"
      > </a
      ><a name="939" href="Relations.html#1169" class="InductiveConstructor"
      >s&#8804;s</a
      ><a name="942"
      > </a
      ><a name="943" class="Symbol"
      >(</a
      ><a name="944" href="RelationsEx.html#843" class="Function"
      >&lt;-implies-&#8804;</a
      ><a name="955"
      > </a
      ><a name="956" href="RelationsEx.html#932" class="Bound"
      >m&lt;n</a
      ><a name="959" class="Symbol"
      >)</a
      ><a name="960"
      >

</a
      ><a name="962" href="RelationsEx.html#962" class="Function"
      >&#8804;-implies-&lt;</a
      ><a name="973"
      > </a
      ><a name="974" class="Symbol"
      >:</a
      ><a name="975"
      > </a
      ><a name="976" class="Symbol"
      >&#8704;</a
      ><a name="977"
      > </a
      ><a name="978" class="Symbol"
      >{</a
      ><a name="979" href="RelationsEx.html#979" class="Bound"
      >m</a
      ><a name="980"
      > </a
      ><a name="981" href="RelationsEx.html#981" class="Bound"
      >n</a
      ><a name="982"
      > </a
      ><a name="983" class="Symbol"
      >:</a
      ><a name="984"
      > </a
      ><a name="985" href="Naturals.html#1064" class="Datatype"
      >&#8469;</a
      ><a name="986" class="Symbol"
      >}</a
      ><a name="987"
      > </a
      ><a name="988" class="Symbol"
      >&#8594;</a
      ><a name="989"
      > </a
      ><a name="990" href="Naturals.html#1091" class="InductiveConstructor"
      >suc</a
      ><a name="993"
      > </a
      ><a name="994" href="RelationsEx.html#979" class="Bound"
      >m</a
      ><a name="995"
      > </a
      ><a name="996" href="Relations.html#1114" class="Datatype Operator"
      >&#8804;</a
      ><a name="997"
      > </a
      ><a name="998" href="RelationsEx.html#981" class="Bound"
      >n</a
      ><a name="999"
      > </a
      ><a name="1000" class="Symbol"
      >&#8594;</a
      ><a name="1001"
      > </a
      ><a name="1002" href="RelationsEx.html#979" class="Bound"
      >m</a
      ><a name="1003"
      > </a
      ><a name="1004" href="Relations.html#15375" class="Datatype Operator"
      >&lt;</a
      ><a name="1005"
      > </a
      ><a name="1006" href="RelationsEx.html#981" class="Bound"
      >n</a
      ><a name="1007"
      >
</a
      ><a name="1008" href="RelationsEx.html#962" class="Function"
      >&#8804;-implies-&lt;</a
      ><a name="1019"
      > </a
      ><a name="1020" class="Symbol"
      >(</a
      ><a name="1021" href="Relations.html#1169" class="InductiveConstructor"
      >s&#8804;s</a
      ><a name="1024"
      > </a
      ><a name="1025" href="Relations.html#1140" class="InductiveConstructor"
      >z&#8804;n</a
      ><a name="1028" class="Symbol"
      >)</a
      ><a name="1029"
      > </a
      ><a name="1030" class="Symbol"
      >=</a
      ><a name="1031"
      > </a
      ><a name="1032" href="Relations.html#15401" class="InductiveConstructor"
      >z&lt;s</a
      ><a name="1035"
      >
</a
      ><a name="1036" href="RelationsEx.html#962" class="Function"
      >&#8804;-implies-&lt;</a
      ><a name="1047"
      > </a
      ><a name="1048" class="Symbol"
      >(</a
      ><a name="1049" href="Relations.html#1169" class="InductiveConstructor"
      >s&#8804;s</a
      ><a name="1052"
      > </a
      ><a name="1053" class="Symbol"
      >(</a
      ><a name="1054" href="Relations.html#1169" class="InductiveConstructor"
      >s&#8804;s</a
      ><a name="1057"
      > </a
      ><a name="1058" href="RelationsEx.html#1058" class="Bound"
      >m&#8804;n</a
      ><a name="1061" class="Symbol"
      >))</a
      ><a name="1063"
      > </a
      ><a name="1064" class="Symbol"
      >=</a
      ><a name="1065"
      > </a
      ><a name="1066" href="Relations.html#15434" class="InductiveConstructor"
      >s&lt;s</a
      ><a name="1069"
      > </a
      ><a name="1070" class="Symbol"
      >(</a
      ><a name="1071" href="RelationsEx.html#962" class="Function"
      >&#8804;-implies-&lt;</a
      ><a name="1082"
      > </a
      ><a name="1083" class="Symbol"
      >(</a
      ><a name="1084" href="Relations.html#1169" class="InductiveConstructor"
      >s&#8804;s</a
      ><a name="1087"
      > </a
      ><a name="1088" href="RelationsEx.html#1058" class="Bound"
      >m&#8804;n</a
      ><a name="1091" class="Symbol"
      >))</a
      >
{% endraw %}</pre>

*Even and odd*

<pre class="Agda">{% raw %}
<a name="1135" href="RelationsEx.html#1135" class="Function"
      >+-evev</a
      ><a name="1141"
      > </a
      ><a name="1142" class="Symbol"
      >:</a
      ><a name="1143"
      > </a
      ><a name="1144" class="Symbol"
      >&#8704;</a
      ><a name="1145"
      > </a
      ><a name="1146" class="Symbol"
      >{</a
      ><a name="1147" href="RelationsEx.html#1147" class="Bound"
      >m</a
      ><a name="1148"
      > </a
      ><a name="1149" href="RelationsEx.html#1149" class="Bound"
      >n</a
      ><a name="1150"
      > </a
      ><a name="1151" class="Symbol"
      >:</a
      ><a name="1152"
      > </a
      ><a name="1153" href="Naturals.html#1064" class="Datatype"
      >&#8469;</a
      ><a name="1154" class="Symbol"
      >}</a
      ><a name="1155"
      > </a
      ><a name="1156" class="Symbol"
      >&#8594;</a
      ><a name="1157"
      > </a
      ><a name="1158" href="Relations.html#17213" class="Datatype"
      >even</a
      ><a name="1162"
      > </a
      ><a name="1163" href="RelationsEx.html#1147" class="Bound"
      >m</a
      ><a name="1164"
      > </a
      ><a name="1165" class="Symbol"
      >&#8594;</a
      ><a name="1166"
      > </a
      ><a name="1167" href="Relations.html#17213" class="Datatype"
      >even</a
      ><a name="1171"
      > </a
      ><a name="1172" href="RelationsEx.html#1149" class="Bound"
      >n</a
      ><a name="1173"
      > </a
      ><a name="1174" class="Symbol"
      >&#8594;</a
      ><a name="1175"
      > </a
      ><a name="1176" href="Relations.html#17213" class="Datatype"
      >even</a
      ><a name="1180"
      > </a
      ><a name="1181" class="Symbol"
      >(</a
      ><a name="1182" href="RelationsEx.html#1147" class="Bound"
      >m</a
      ><a name="1183"
      > </a
      ><a name="1184" href="Naturals.html#9439" class="Primitive Operator"
      >+</a
      ><a name="1185"
      > </a
      ><a name="1186" href="RelationsEx.html#1149" class="Bound"
      >n</a
      ><a name="1187" class="Symbol"
      >)</a
      ><a name="1188"
      >
</a
      ><a name="1189" href="RelationsEx.html#1135" class="Function"
      >+-evev</a
      ><a name="1195"
      > </a
      ><a name="1196" href="Relations.html#17238" class="InductiveConstructor"
      >ev-zero</a
      ><a name="1203"
      > </a
      ><a name="1204" href="RelationsEx.html#1204" class="Bound"
      >evn</a
      ><a name="1207"
      > </a
      ><a name="1208" class="Symbol"
      >=</a
      ><a name="1209"
      > </a
      ><a name="1210" href="RelationsEx.html#1204" class="Bound"
      >evn</a
      ><a name="1213"
      >
</a
      ><a name="1214" href="RelationsEx.html#1135" class="Function"
      >+-evev</a
      ><a name="1220"
      > </a
      ><a name="1221" class="Symbol"
      >(</a
      ><a name="1222" href="Relations.html#17262" class="InductiveConstructor"
      >ev-suc</a
      ><a name="1228"
      > </a
      ><a name="1229" class="Symbol"
      >(</a
      ><a name="1230" href="Relations.html#17335" class="InductiveConstructor"
      >od-suc</a
      ><a name="1236"
      > </a
      ><a name="1237" href="RelationsEx.html#1237" class="Bound"
      >evm</a
      ><a name="1240" class="Symbol"
      >))</a
      ><a name="1242"
      > </a
      ><a name="1243" href="RelationsEx.html#1243" class="Bound"
      >evn</a
      ><a name="1246"
      > </a
      ><a name="1247" class="Symbol"
      >=</a
      ><a name="1248"
      > </a
      ><a name="1249" href="Relations.html#17262" class="InductiveConstructor"
      >ev-suc</a
      ><a name="1255"
      > </a
      ><a name="1256" class="Symbol"
      >(</a
      ><a name="1257" href="Relations.html#17335" class="InductiveConstructor"
      >od-suc</a
      ><a name="1263"
      > </a
      ><a name="1264" class="Symbol"
      >(</a
      ><a name="1265" href="RelationsEx.html#1135" class="Function"
      >+-evev</a
      ><a name="1271"
      > </a
      ><a name="1272" href="RelationsEx.html#1237" class="Bound"
      >evm</a
      ><a name="1275"
      > </a
      ><a name="1276" href="RelationsEx.html#1243" class="Bound"
      >evn</a
      ><a name="1279" class="Symbol"
      >))</a
      ><a name="1281"
      >

</a
      ><a name="1283" href="RelationsEx.html#1283" class="Function"
      >+-evod</a
      ><a name="1289"
      > </a
      ><a name="1290" class="Symbol"
      >:</a
      ><a name="1291"
      > </a
      ><a name="1292" class="Symbol"
      >&#8704;</a
      ><a name="1293"
      > </a
      ><a name="1294" class="Symbol"
      >{</a
      ><a name="1295" href="RelationsEx.html#1295" class="Bound"
      >m</a
      ><a name="1296"
      > </a
      ><a name="1297" href="RelationsEx.html#1297" class="Bound"
      >n</a
      ><a name="1298"
      > </a
      ><a name="1299" class="Symbol"
      >:</a
      ><a name="1300"
      > </a
      ><a name="1301" href="Naturals.html#1064" class="Datatype"
      >&#8469;</a
      ><a name="1302" class="Symbol"
      >}</a
      ><a name="1303"
      > </a
      ><a name="1304" class="Symbol"
      >&#8594;</a
      ><a name="1305"
      > </a
      ><a name="1306" href="Relations.html#17213" class="Datatype"
      >even</a
      ><a name="1310"
      > </a
      ><a name="1311" href="RelationsEx.html#1295" class="Bound"
      >m</a
      ><a name="1312"
      > </a
      ><a name="1313" class="Symbol"
      >&#8594;</a
      ><a name="1314"
      > </a
      ><a name="1315" href="Relations.html#17311" class="Datatype"
      >odd</a
      ><a name="1318"
      > </a
      ><a name="1319" href="RelationsEx.html#1297" class="Bound"
      >n</a
      ><a name="1320"
      > </a
      ><a name="1321" class="Symbol"
      >&#8594;</a
      ><a name="1322"
      > </a
      ><a name="1323" href="Relations.html#17311" class="Datatype"
      >odd</a
      ><a name="1326"
      > </a
      ><a name="1327" class="Symbol"
      >(</a
      ><a name="1328" href="RelationsEx.html#1295" class="Bound"
      >m</a
      ><a name="1329"
      > </a
      ><a name="1330" href="Naturals.html#9439" class="Primitive Operator"
      >+</a
      ><a name="1331"
      > </a
      ><a name="1332" href="RelationsEx.html#1297" class="Bound"
      >n</a
      ><a name="1333" class="Symbol"
      >)</a
      ><a name="1334"
      >
</a
      ><a name="1335" href="RelationsEx.html#1283" class="Function"
      >+-evod</a
      ><a name="1341"
      > </a
      ><a name="1342" href="Relations.html#17238" class="InductiveConstructor"
      >ev-zero</a
      ><a name="1349"
      > </a
      ><a name="1350" href="RelationsEx.html#1350" class="Bound"
      >odn</a
      ><a name="1353"
      > </a
      ><a name="1354" class="Symbol"
      >=</a
      ><a name="1355"
      > </a
      ><a name="1356" href="RelationsEx.html#1350" class="Bound"
      >odn</a
      ><a name="1359"
      >
</a
      ><a name="1360" href="RelationsEx.html#1283" class="Function"
      >+-evod</a
      ><a name="1366"
      > </a
      ><a name="1367" class="Symbol"
      >(</a
      ><a name="1368" href="Relations.html#17262" class="InductiveConstructor"
      >ev-suc</a
      ><a name="1374"
      > </a
      ><a name="1375" class="Symbol"
      >(</a
      ><a name="1376" href="Relations.html#17335" class="InductiveConstructor"
      >od-suc</a
      ><a name="1382"
      > </a
      ><a name="1383" href="RelationsEx.html#1383" class="Bound"
      >evm</a
      ><a name="1386" class="Symbol"
      >))</a
      ><a name="1388"
      > </a
      ><a name="1389" href="RelationsEx.html#1389" class="Bound"
      >odn</a
      ><a name="1392"
      > </a
      ><a name="1393" class="Symbol"
      >=</a
      ><a name="1394"
      > </a
      ><a name="1395" href="Relations.html#17335" class="InductiveConstructor"
      >od-suc</a
      ><a name="1401"
      > </a
      ><a name="1402" class="Symbol"
      >(</a
      ><a name="1403" href="Relations.html#17262" class="InductiveConstructor"
      >ev-suc</a
      ><a name="1409"
      > </a
      ><a name="1410" class="Symbol"
      >(</a
      ><a name="1411" href="RelationsEx.html#1283" class="Function"
      >+-evod</a
      ><a name="1417"
      > </a
      ><a name="1418" href="RelationsEx.html#1383" class="Bound"
      >evm</a
      ><a name="1421"
      > </a
      ><a name="1422" href="RelationsEx.html#1389" class="Bound"
      >odn</a
      ><a name="1425" class="Symbol"
      >))</a
      ><a name="1427"
      >

</a
      ><a name="1429" href="RelationsEx.html#1429" class="Function"
      >+-odev</a
      ><a name="1435"
      > </a
      ><a name="1436" class="Symbol"
      >:</a
      ><a name="1437"
      > </a
      ><a name="1438" class="Symbol"
      >&#8704;</a
      ><a name="1439"
      > </a
      ><a name="1440" class="Symbol"
      >{</a
      ><a name="1441" href="RelationsEx.html#1441" class="Bound"
      >m</a
      ><a name="1442"
      > </a
      ><a name="1443" href="RelationsEx.html#1443" class="Bound"
      >n</a
      ><a name="1444"
      > </a
      ><a name="1445" class="Symbol"
      >:</a
      ><a name="1446"
      > </a
      ><a name="1447" href="Naturals.html#1064" class="Datatype"
      >&#8469;</a
      ><a name="1448" class="Symbol"
      >}</a
      ><a name="1449"
      > </a
      ><a name="1450" class="Symbol"
      >&#8594;</a
      ><a name="1451"
      > </a
      ><a name="1452" href="Relations.html#17311" class="Datatype"
      >odd</a
      ><a name="1455"
      > </a
      ><a name="1456" href="RelationsEx.html#1441" class="Bound"
      >m</a
      ><a name="1457"
      > </a
      ><a name="1458" class="Symbol"
      >&#8594;</a
      ><a name="1459"
      > </a
      ><a name="1460" href="Relations.html#17213" class="Datatype"
      >even</a
      ><a name="1464"
      > </a
      ><a name="1465" href="RelationsEx.html#1443" class="Bound"
      >n</a
      ><a name="1466"
      > </a
      ><a name="1467" class="Symbol"
      >&#8594;</a
      ><a name="1468"
      > </a
      ><a name="1469" href="Relations.html#17311" class="Datatype"
      >odd</a
      ><a name="1472"
      > </a
      ><a name="1473" class="Symbol"
      >(</a
      ><a name="1474" href="RelationsEx.html#1441" class="Bound"
      >m</a
      ><a name="1475"
      > </a
      ><a name="1476" href="Naturals.html#9439" class="Primitive Operator"
      >+</a
      ><a name="1477"
      > </a
      ><a name="1478" href="RelationsEx.html#1443" class="Bound"
      >n</a
      ><a name="1479" class="Symbol"
      >)</a
      ><a name="1480"
      >
</a
      ><a name="1481" href="RelationsEx.html#1429" class="Function"
      >+-odev</a
      ><a name="1487"
      > </a
      ><a name="1488" class="Symbol"
      >(</a
      ><a name="1489" href="Relations.html#17335" class="InductiveConstructor"
      >od-suc</a
      ><a name="1495"
      > </a
      ><a name="1496" href="RelationsEx.html#1496" class="Bound"
      >evm</a
      ><a name="1499" class="Symbol"
      >)</a
      ><a name="1500"
      > </a
      ><a name="1501" href="RelationsEx.html#1501" class="Bound"
      >evn</a
      ><a name="1504"
      > </a
      ><a name="1505" class="Symbol"
      >=</a
      ><a name="1506"
      > </a
      ><a name="1507" href="Relations.html#17335" class="InductiveConstructor"
      >od-suc</a
      ><a name="1513"
      > </a
      ><a name="1514" class="Symbol"
      >(</a
      ><a name="1515" href="RelationsEx.html#1135" class="Function"
      >+-evev</a
      ><a name="1521"
      > </a
      ><a name="1522" href="RelationsEx.html#1496" class="Bound"
      >evm</a
      ><a name="1525"
      > </a
      ><a name="1526" href="RelationsEx.html#1501" class="Bound"
      >evn</a
      ><a name="1529" class="Symbol"
      >)</a
      ><a name="1530"
      >

</a
      ><a name="1532" href="RelationsEx.html#1532" class="Function"
      >+-odod</a
      ><a name="1538"
      > </a
      ><a name="1539" class="Symbol"
      >:</a
      ><a name="1540"
      > </a
      ><a name="1541" class="Symbol"
      >&#8704;</a
      ><a name="1542"
      > </a
      ><a name="1543" class="Symbol"
      >{</a
      ><a name="1544" href="RelationsEx.html#1544" class="Bound"
      >m</a
      ><a name="1545"
      > </a
      ><a name="1546" href="RelationsEx.html#1546" class="Bound"
      >n</a
      ><a name="1547"
      > </a
      ><a name="1548" class="Symbol"
      >:</a
      ><a name="1549"
      > </a
      ><a name="1550" href="Naturals.html#1064" class="Datatype"
      >&#8469;</a
      ><a name="1551" class="Symbol"
      >}</a
      ><a name="1552"
      > </a
      ><a name="1553" class="Symbol"
      >&#8594;</a
      ><a name="1554"
      > </a
      ><a name="1555" href="Relations.html#17311" class="Datatype"
      >odd</a
      ><a name="1558"
      > </a
      ><a name="1559" href="RelationsEx.html#1544" class="Bound"
      >m</a
      ><a name="1560"
      > </a
      ><a name="1561" class="Symbol"
      >&#8594;</a
      ><a name="1562"
      > </a
      ><a name="1563" href="Relations.html#17311" class="Datatype"
      >odd</a
      ><a name="1566"
      > </a
      ><a name="1567" href="RelationsEx.html#1546" class="Bound"
      >n</a
      ><a name="1568"
      > </a
      ><a name="1569" class="Symbol"
      >&#8594;</a
      ><a name="1570"
      > </a
      ><a name="1571" href="Relations.html#17213" class="Datatype"
      >even</a
      ><a name="1575"
      > </a
      ><a name="1576" class="Symbol"
      >(</a
      ><a name="1577" href="RelationsEx.html#1544" class="Bound"
      >m</a
      ><a name="1578"
      > </a
      ><a name="1579" href="Naturals.html#9439" class="Primitive Operator"
      >+</a
      ><a name="1580"
      > </a
      ><a name="1581" href="RelationsEx.html#1546" class="Bound"
      >n</a
      ><a name="1582" class="Symbol"
      >)</a
      ><a name="1583"
      >
</a
      ><a name="1584" href="RelationsEx.html#1532" class="Function"
      >+-odod</a
      ><a name="1590"
      > </a
      ><a name="1591" class="Symbol"
      >(</a
      ><a name="1592" href="Relations.html#17335" class="InductiveConstructor"
      >od-suc</a
      ><a name="1598"
      > </a
      ><a name="1599" href="RelationsEx.html#1599" class="Bound"
      >evm</a
      ><a name="1602" class="Symbol"
      >)</a
      ><a name="1603"
      > </a
      ><a name="1604" href="RelationsEx.html#1604" class="Bound"
      >odn</a
      ><a name="1607"
      > </a
      ><a name="1608" class="Symbol"
      >=</a
      ><a name="1609"
      > </a
      ><a name="1610" href="Relations.html#17262" class="InductiveConstructor"
      >ev-suc</a
      ><a name="1616"
      > </a
      ><a name="1617" class="Symbol"
      >(</a
      ><a name="1618" href="RelationsEx.html#1283" class="Function"
      >+-evod</a
      ><a name="1624"
      > </a
      ><a name="1625" href="RelationsEx.html#1599" class="Bound"
      >evm</a
      ><a name="1628"
      > </a
      ><a name="1629" href="RelationsEx.html#1604" class="Bound"
      >odn</a
      ><a name="1632" class="Symbol"
      >)</a
      >
{% endraw %}</pre>

<pre class="Agda">{% raw %}
<a name="1659" href="RelationsEx.html#1659" class="Function"
      >+-lemma</a
      ><a name="1666"
      > </a
      ><a name="1667" class="Symbol"
      >:</a
      ><a name="1668"
      > </a
      ><a name="1669" class="Symbol"
      >&#8704;</a
      ><a name="1670"
      > </a
      ><a name="1671" class="Symbol"
      >(</a
      ><a name="1672" href="RelationsEx.html#1672" class="Bound"
      >m</a
      ><a name="1673"
      > </a
      ><a name="1674" class="Symbol"
      >:</a
      ><a name="1675"
      > </a
      ><a name="1676" href="Naturals.html#1064" class="Datatype"
      >&#8469;</a
      ><a name="1677" class="Symbol"
      >)</a
      ><a name="1678"
      > </a
      ><a name="1679" class="Symbol"
      >&#8594;</a
      ><a name="1680"
      > </a
      ><a name="1681" href="Naturals.html#1091" class="InductiveConstructor"
      >suc</a
      ><a name="1684"
      > </a
      ><a name="1685" class="Symbol"
      >(</a
      ><a name="1686" href="Naturals.html#1091" class="InductiveConstructor"
      >suc</a
      ><a name="1689"
      > </a
      ><a name="1690" class="Symbol"
      >(</a
      ><a name="1691" href="RelationsEx.html#1672" class="Bound"
      >m</a
      ><a name="1692"
      > </a
      ><a name="1693" href="Naturals.html#9439" class="Primitive Operator"
      >+</a
      ><a name="1694"
      > </a
      ><a name="1695" class="Symbol"
      >(</a
      ><a name="1696" href="RelationsEx.html#1672" class="Bound"
      >m</a
      ><a name="1697"
      > </a
      ><a name="1698" href="Naturals.html#9439" class="Primitive Operator"
      >+</a
      ><a name="1699"
      > </a
      ><a name="1700" class="Number"
      >0</a
      ><a name="1701" class="Symbol"
      >)))</a
      ><a name="1704"
      > </a
      ><a name="1705" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="1706"
      > </a
      ><a name="1707" href="Naturals.html#1091" class="InductiveConstructor"
      >suc</a
      ><a name="1710"
      > </a
      ><a name="1711" href="RelationsEx.html#1672" class="Bound"
      >m</a
      ><a name="1712"
      > </a
      ><a name="1713" href="Naturals.html#9439" class="Primitive Operator"
      >+</a
      ><a name="1714"
      > </a
      ><a name="1715" class="Symbol"
      >(</a
      ><a name="1716" href="Naturals.html#1091" class="InductiveConstructor"
      >suc</a
      ><a name="1719"
      > </a
      ><a name="1720" href="RelationsEx.html#1672" class="Bound"
      >m</a
      ><a name="1721"
      > </a
      ><a name="1722" href="Naturals.html#9439" class="Primitive Operator"
      >+</a
      ><a name="1723"
      > </a
      ><a name="1724" class="Number"
      >0</a
      ><a name="1725" class="Symbol"
      >)</a
      ><a name="1726"
      >
</a
      ><a name="1727" href="RelationsEx.html#1659" class="Function"
      >+-lemma</a
      ><a name="1734"
      > </a
      ><a name="1735" href="RelationsEx.html#1735" class="Bound"
      >m</a
      ><a name="1736"
      > </a
      ><a name="1737" class="Keyword"
      >rewrite</a
      ><a name="1744"
      > </a
      ><a name="1745" href="Properties.html#16853" class="Function"
      >+-identity</a
      ><a name="1755"
      > </a
      ><a name="1756" href="RelationsEx.html#1735" class="Bound"
      >m</a
      ><a name="1757"
      > </a
      ><a name="1758" class="Symbol"
      >|</a
      ><a name="1759"
      > </a
      ><a name="1760" href="Properties.html#16962" class="Function"
      >+-suc</a
      ><a name="1765"
      > </a
      ><a name="1766" href="RelationsEx.html#1735" class="Bound"
      >m</a
      ><a name="1767"
      > </a
      ><a name="1768" href="RelationsEx.html#1735" class="Bound"
      >m</a
      ><a name="1769"
      > </a
      ><a name="1770" class="Symbol"
      >=</a
      ><a name="1771"
      > </a
      ><a name="1772" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="1776"
      >

</a
      ><a name="1778" href="RelationsEx.html#1778" class="Function"
      >+-lemma&#8242;</a
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
      ><a name="1791" class="Symbol"
      >(</a
      ><a name="1792" href="RelationsEx.html#1792" class="Bound"
      >m</a
      ><a name="1793"
      > </a
      ><a name="1794" class="Symbol"
      >:</a
      ><a name="1795"
      > </a
      ><a name="1796" href="Naturals.html#1064" class="Datatype"
      >&#8469;</a
      ><a name="1797" class="Symbol"
      >)</a
      ><a name="1798"
      > </a
      ><a name="1799" class="Symbol"
      >&#8594;</a
      ><a name="1800"
      > </a
      ><a name="1801" href="Naturals.html#1091" class="InductiveConstructor"
      >suc</a
      ><a name="1804"
      > </a
      ><a name="1805" class="Symbol"
      >(</a
      ><a name="1806" href="Naturals.html#1091" class="InductiveConstructor"
      >suc</a
      ><a name="1809"
      > </a
      ><a name="1810" class="Symbol"
      >(</a
      ><a name="1811" href="RelationsEx.html#1792" class="Bound"
      >m</a
      ><a name="1812"
      > </a
      ><a name="1813" href="Naturals.html#9439" class="Primitive Operator"
      >+</a
      ><a name="1814"
      > </a
      ><a name="1815" class="Symbol"
      >(</a
      ><a name="1816" href="RelationsEx.html#1792" class="Bound"
      >m</a
      ><a name="1817"
      > </a
      ><a name="1818" href="Naturals.html#9439" class="Primitive Operator"
      >+</a
      ><a name="1819"
      > </a
      ><a name="1820" class="Number"
      >0</a
      ><a name="1821" class="Symbol"
      >)))</a
      ><a name="1824"
      > </a
      ><a name="1825" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="1826"
      > </a
      ><a name="1827" href="Naturals.html#1091" class="InductiveConstructor"
      >suc</a
      ><a name="1830"
      > </a
      ><a name="1831" href="RelationsEx.html#1792" class="Bound"
      >m</a
      ><a name="1832"
      > </a
      ><a name="1833" href="Naturals.html#9439" class="Primitive Operator"
      >+</a
      ><a name="1834"
      > </a
      ><a name="1835" class="Symbol"
      >(</a
      ><a name="1836" href="Naturals.html#1091" class="InductiveConstructor"
      >suc</a
      ><a name="1839"
      > </a
      ><a name="1840" href="RelationsEx.html#1792" class="Bound"
      >m</a
      ><a name="1841"
      > </a
      ><a name="1842" href="Naturals.html#9439" class="Primitive Operator"
      >+</a
      ><a name="1843"
      > </a
      ><a name="1844" class="Number"
      >0</a
      ><a name="1845" class="Symbol"
      >)</a
      ><a name="1846"
      >
</a
      ><a name="1847" href="RelationsEx.html#1778" class="Function"
      >+-lemma&#8242;</a
      ><a name="1855"
      > </a
      ><a name="1856" href="RelationsEx.html#1856" class="Bound"
      >m</a
      ><a name="1857"
      > </a
      ><a name="1858" class="Keyword"
      >rewrite</a
      ><a name="1865"
      > </a
      ><a name="1866" href="Properties.html#16962" class="Function"
      >+-suc</a
      ><a name="1871"
      > </a
      ><a name="1872" href="RelationsEx.html#1856" class="Bound"
      >m</a
      ><a name="1873"
      > </a
      ><a name="1874" class="Symbol"
      >(</a
      ><a name="1875" href="RelationsEx.html#1856" class="Bound"
      >m</a
      ><a name="1876"
      > </a
      ><a name="1877" href="Naturals.html#9439" class="Primitive Operator"
      >+</a
      ><a name="1878"
      > </a
      ><a name="1879" class="Number"
      >0</a
      ><a name="1880" class="Symbol"
      >)</a
      ><a name="1881"
      > </a
      ><a name="1882" class="Symbol"
      >=</a
      ><a name="1883"
      > </a
      ><a name="1884" class="Symbol"
      >{!!}</a
      ><a name="1888"
      >

</a
      ><a name="1890" class="Keyword"
      >mutual</a
      ><a name="1896"
      >
  </a
      ><a name="1899" href="RelationsEx.html#1899" class="Function"
      >is-even</a
      ><a name="1906"
      > </a
      ><a name="1907" class="Symbol"
      >:</a
      ><a name="1908"
      > </a
      ><a name="1909" class="Symbol"
      >&#8704;</a
      ><a name="1910"
      > </a
      ><a name="1911" class="Symbol"
      >(</a
      ><a name="1912" href="RelationsEx.html#1912" class="Bound"
      >n</a
      ><a name="1913"
      > </a
      ><a name="1914" class="Symbol"
      >:</a
      ><a name="1915"
      > </a
      ><a name="1916" href="Naturals.html#1064" class="Datatype"
      >&#8469;</a
      ><a name="1917" class="Symbol"
      >)</a
      ><a name="1918"
      > </a
      ><a name="1919" class="Symbol"
      >&#8594;</a
      ><a name="1920"
      > </a
      ><a name="1921" href="Relations.html#17213" class="Datatype"
      >even</a
      ><a name="1925"
      > </a
      ><a name="1926" href="RelationsEx.html#1912" class="Bound"
      >n</a
      ><a name="1927"
      > </a
      ><a name="1928" class="Symbol"
      >&#8594;</a
      ><a name="1929"
      > </a
      ><a name="1930" href="https://agda.github.io/agda-stdlib/Data.Product.html#823" class="Function"
      >&#8707;</a
      ><a name="1931" class="Symbol"
      >(&#955;</a
      ><a name="1933"
      > </a
      ><a name="1934" class="Symbol"
      >(</a
      ><a name="1935" href="RelationsEx.html#1935" class="Bound"
      >m</a
      ><a name="1936"
      > </a
      ><a name="1937" class="Symbol"
      >:</a
      ><a name="1938"
      > </a
      ><a name="1939" href="Naturals.html#1064" class="Datatype"
      >&#8469;</a
      ><a name="1940" class="Symbol"
      >)</a
      ><a name="1941"
      > </a
      ><a name="1942" class="Symbol"
      >&#8594;</a
      ><a name="1943"
      > </a
      ><a name="1944" href="RelationsEx.html#1912" class="Bound"
      >n</a
      ><a name="1945"
      > </a
      ><a name="1946" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="1947"
      > </a
      ><a name="1948" class="Number"
      >2</a
      ><a name="1949"
      > </a
      ><a name="1950" href="Naturals.html#12016" class="Primitive Operator"
      >*</a
      ><a name="1951"
      > </a
      ><a name="1952" href="RelationsEx.html#1935" class="Bound"
      >m</a
      ><a name="1953" class="Symbol"
      >)</a
      ><a name="1954"
      >
  </a
      ><a name="1957" href="RelationsEx.html#1899" class="Function"
      >is-even</a
      ><a name="1964"
      > </a
      ><a name="1965" href="Naturals.html#1080" class="InductiveConstructor"
      >zero</a
      ><a name="1969"
      > </a
      ><a name="1970" href="Relations.html#17238" class="InductiveConstructor"
      >ev-zero</a
      ><a name="1977"
      > </a
      ><a name="1978" class="Symbol"
      >=</a
      ><a name="1979"
      >  </a
      ><a name="1981" href="Naturals.html#1080" class="InductiveConstructor"
      >zero</a
      ><a name="1985"
      > </a
      ><a name="1986" href="https://agda.github.io/agda-stdlib/Data.Product.html#509" class="InductiveConstructor Operator"
      >,</a
      ><a name="1987"
      > </a
      ><a name="1988" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="1992"
      >
  </a
      ><a name="1995" href="RelationsEx.html#1899" class="Function"
      >is-even</a
      ><a name="2002"
      > </a
      ><a name="2003" class="Symbol"
      >(</a
      ><a name="2004" href="Naturals.html#1091" class="InductiveConstructor"
      >suc</a
      ><a name="2007"
      > </a
      ><a name="2008" href="RelationsEx.html#2008" class="Bound"
      >n</a
      ><a name="2009" class="Symbol"
      >)</a
      ><a name="2010"
      > </a
      ><a name="2011" class="Symbol"
      >(</a
      ><a name="2012" href="Relations.html#17262" class="InductiveConstructor"
      >ev-suc</a
      ><a name="2018"
      > </a
      ><a name="2019" href="RelationsEx.html#2019" class="Bound"
      >odn</a
      ><a name="2022" class="Symbol"
      >)</a
      ><a name="2023"
      > </a
      ><a name="2024" class="Keyword"
      >with</a
      ><a name="2028"
      > </a
      ><a name="2029" href="RelationsEx.html#2108" class="Function"
      >is-odd</a
      ><a name="2035"
      > </a
      ><a name="2036" href="RelationsEx.html#2008" class="Bound"
      >n</a
      ><a name="2037"
      > </a
      ><a name="2038" href="RelationsEx.html#2019" class="Bound"
      >odn</a
      ><a name="2041"
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
      ><a name="2050" href="RelationsEx.html#2050" class="Bound"
      >m</a
      ><a name="2051"
      > </a
      ><a name="2052" href="https://agda.github.io/agda-stdlib/Data.Product.html#509" class="InductiveConstructor Operator"
      >,</a
      ><a name="2053"
      > </a
      ><a name="2054" href="RelationsEx.html#2054" class="Bound"
      >n&#8801;1+2*m</a
      ><a name="2061"
      > </a
      ><a name="2062" class="Keyword"
      >rewrite</a
      ><a name="2069"
      > </a
      ><a name="2070" href="RelationsEx.html#2054" class="Bound"
      >n&#8801;1+2*m</a
      ><a name="2077"
      > </a
      ><a name="2078" class="Symbol"
      >|</a
      ><a name="2079"
      > </a
      ><a name="2080" href="RelationsEx.html#1659" class="Function"
      >+-lemma</a
      ><a name="2087"
      > </a
      ><a name="2088" href="RelationsEx.html#2050" class="Bound"
      >m</a
      ><a name="2089"
      > </a
      ><a name="2090" class="Symbol"
      >=</a
      ><a name="2091"
      > </a
      ><a name="2092" href="Naturals.html#1091" class="InductiveConstructor"
      >suc</a
      ><a name="2095"
      > </a
      ><a name="2096" href="RelationsEx.html#2050" class="Bound"
      >m</a
      ><a name="2097"
      > </a
      ><a name="2098" href="https://agda.github.io/agda-stdlib/Data.Product.html#509" class="InductiveConstructor Operator"
      >,</a
      ><a name="2099"
      > </a
      ><a name="2100" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="2104"
      >

  </a
      ><a name="2108" href="RelationsEx.html#2108" class="Function"
      >is-odd</a
      ><a name="2114"
      > </a
      ><a name="2115" class="Symbol"
      >:</a
      ><a name="2116"
      > </a
      ><a name="2117" class="Symbol"
      >&#8704;</a
      ><a name="2118"
      > </a
      ><a name="2119" class="Symbol"
      >(</a
      ><a name="2120" href="RelationsEx.html#2120" class="Bound"
      >n</a
      ><a name="2121"
      > </a
      ><a name="2122" class="Symbol"
      >:</a
      ><a name="2123"
      > </a
      ><a name="2124" href="Naturals.html#1064" class="Datatype"
      >&#8469;</a
      ><a name="2125" class="Symbol"
      >)</a
      ><a name="2126"
      > </a
      ><a name="2127" class="Symbol"
      >&#8594;</a
      ><a name="2128"
      > </a
      ><a name="2129" href="Relations.html#17311" class="Datatype"
      >odd</a
      ><a name="2132"
      > </a
      ><a name="2133" href="RelationsEx.html#2120" class="Bound"
      >n</a
      ><a name="2134"
      > </a
      ><a name="2135" class="Symbol"
      >&#8594;</a
      ><a name="2136"
      > </a
      ><a name="2137" href="https://agda.github.io/agda-stdlib/Data.Product.html#823" class="Function"
      >&#8707;</a
      ><a name="2138" class="Symbol"
      >(&#955;</a
      ><a name="2140"
      > </a
      ><a name="2141" class="Symbol"
      >(</a
      ><a name="2142" href="RelationsEx.html#2142" class="Bound"
      >m</a
      ><a name="2143"
      > </a
      ><a name="2144" class="Symbol"
      >:</a
      ><a name="2145"
      > </a
      ><a name="2146" href="Naturals.html#1064" class="Datatype"
      >&#8469;</a
      ><a name="2147" class="Symbol"
      >)</a
      ><a name="2148"
      > </a
      ><a name="2149" class="Symbol"
      >&#8594;</a
      ><a name="2150"
      > </a
      ><a name="2151" href="RelationsEx.html#2120" class="Bound"
      >n</a
      ><a name="2152"
      > </a
      ><a name="2153" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="2154"
      > </a
      ><a name="2155" class="Number"
      >1</a
      ><a name="2156"
      > </a
      ><a name="2157" href="Naturals.html#9439" class="Primitive Operator"
      >+</a
      ><a name="2158"
      > </a
      ><a name="2159" class="Number"
      >2</a
      ><a name="2160"
      > </a
      ><a name="2161" href="Naturals.html#12016" class="Primitive Operator"
      >*</a
      ><a name="2162"
      > </a
      ><a name="2163" href="RelationsEx.html#2142" class="Bound"
      >m</a
      ><a name="2164" class="Symbol"
      >)</a
      ><a name="2165"
      >
  </a
      ><a name="2168" href="RelationsEx.html#2108" class="Function"
      >is-odd</a
      ><a name="2174"
      > </a
      ><a name="2175" class="Symbol"
      >(</a
      ><a name="2176" href="Naturals.html#1091" class="InductiveConstructor"
      >suc</a
      ><a name="2179"
      > </a
      ><a name="2180" href="RelationsEx.html#2180" class="Bound"
      >n</a
      ><a name="2181" class="Symbol"
      >)</a
      ><a name="2182"
      > </a
      ><a name="2183" class="Symbol"
      >(</a
      ><a name="2184" href="Relations.html#17335" class="InductiveConstructor"
      >od-suc</a
      ><a name="2190"
      > </a
      ><a name="2191" href="RelationsEx.html#2191" class="Bound"
      >evn</a
      ><a name="2194" class="Symbol"
      >)</a
      ><a name="2195"
      > </a
      ><a name="2196" class="Keyword"
      >with</a
      ><a name="2200"
      > </a
      ><a name="2201" href="RelationsEx.html#1899" class="Function"
      >is-even</a
      ><a name="2208"
      > </a
      ><a name="2209" href="RelationsEx.html#2180" class="Bound"
      >n</a
      ><a name="2210"
      > </a
      ><a name="2211" href="RelationsEx.html#2191" class="Bound"
      >evn</a
      ><a name="2214"
      >
  </a
      ><a name="2217" class="Symbol"
      >...</a
      ><a name="2220"
      > </a
      ><a name="2221" class="Symbol"
      >|</a
      ><a name="2222"
      > </a
      ><a name="2223" href="RelationsEx.html#2223" class="Bound"
      >m</a
      ><a name="2224"
      > </a
      ><a name="2225" href="https://agda.github.io/agda-stdlib/Data.Product.html#509" class="InductiveConstructor Operator"
      >,</a
      ><a name="2226"
      > </a
      ><a name="2227" href="RelationsEx.html#2227" class="Bound"
      >n&#8801;2*m</a
      ><a name="2232"
      > </a
      ><a name="2233" class="Keyword"
      >rewrite</a
      ><a name="2240"
      > </a
      ><a name="2241" href="RelationsEx.html#2227" class="Bound"
      >n&#8801;2*m</a
      ><a name="2246"
      > </a
      ><a name="2247" class="Symbol"
      >=</a
      ><a name="2248"
      > </a
      ><a name="2249" href="RelationsEx.html#2223" class="Bound"
      >m</a
      ><a name="2250"
      > </a
      ><a name="2251" href="https://agda.github.io/agda-stdlib/Data.Product.html#509" class="InductiveConstructor Operator"
      >,</a
      ><a name="2252"
      > </a
      ><a name="2253" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      >
{% endraw %}</pre>

    
