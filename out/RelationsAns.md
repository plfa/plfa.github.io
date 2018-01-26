---
title     : "Relations Answers"
layout    : page
permalink : /RelationsAns
---

## Imports

<pre class="Agda">{% raw %}
<a name="110" class="Keyword"
      >open</a
      ><a name="114"
      > </a
      ><a name="115" class="Keyword"
      >import</a
      ><a name="121"
      > </a
      ><a name="122" class="Module"
      >Naturals</a
      ><a name="130"
      > </a
      ><a name="131" class="Keyword"
      >using</a
      ><a name="136"
      > </a
      ><a name="137" class="Symbol"
      >(</a
      ><a name="138" href="Naturals.html#1064" class="Datatype"
      >&#8469;</a
      ><a name="139" class="Symbol"
      >;</a
      ><a name="140"
      > </a
      ><a name="141" href="Naturals.html#1080" class="InductiveConstructor"
      >zero</a
      ><a name="145" class="Symbol"
      >;</a
      ><a name="146"
      > </a
      ><a name="147" href="Naturals.html#1091" class="InductiveConstructor"
      >suc</a
      ><a name="150" class="Symbol"
      >;</a
      ><a name="151"
      > </a
      ><a name="152" href="Naturals.html#9439" class="Primitive Operator"
      >_+_</a
      ><a name="155" class="Symbol"
      >;</a
      ><a name="156"
      > </a
      ><a name="157" href="Naturals.html#12016" class="Primitive Operator"
      >_*_</a
      ><a name="160" class="Symbol"
      >;</a
      ><a name="161"
      > </a
      ><a name="162" href="Naturals.html#13851" class="Primitive Operator"
      >_&#8760;_</a
      ><a name="165" class="Symbol"
      >)</a
      ><a name="166"
      >
</a
      ><a name="167" class="Keyword"
      >open</a
      ><a name="171"
      > </a
      ><a name="172" class="Keyword"
      >import</a
      ><a name="178"
      > </a
      ><a name="179" class="Module"
      >Relations</a
      ><a name="188"
      > </a
      ><a name="189" class="Keyword"
      >using</a
      ><a name="194"
      > </a
      ><a name="195" class="Symbol"
      >(</a
      ><a name="196" href="Relations.html#1114" class="Datatype Operator"
      >_&#8804;_</a
      ><a name="199" class="Symbol"
      >;</a
      ><a name="200"
      > </a
      ><a name="201" href="Relations.html#15375" class="Datatype Operator"
      >_&lt;_</a
      ><a name="204" class="Symbol"
      >;</a
      ><a name="205"
      > </a
      ><a name="206" href="Relations.html#16129" class="Datatype"
      >Trichotomy</a
      ><a name="216" class="Symbol"
      >;</a
      ><a name="217"
      > </a
      ><a name="218" href="Relations.html#17213" class="Datatype"
      >even</a
      ><a name="222" class="Symbol"
      >;</a
      ><a name="223"
      > </a
      ><a name="224" href="Relations.html#17311" class="Datatype"
      >odd</a
      ><a name="227" class="Symbol"
      >)</a
      ><a name="228"
      >
</a
      ><a name="229" class="Keyword"
      >open</a
      ><a name="233"
      > </a
      ><a name="234" class="Keyword"
      >import</a
      ><a name="240"
      > </a
      ><a name="241" class="Module"
      >Properties</a
      ><a name="251"
      > </a
      ><a name="252" class="Keyword"
      >using</a
      ><a name="257"
      > </a
      ><a name="258" class="Symbol"
      >(</a
      ><a name="259" href="Properties.html#17070" class="Function"
      >+-comm</a
      ><a name="265" class="Symbol"
      >;</a
      ><a name="266"
      > </a
      ><a name="267" href="Properties.html#16853" class="Function"
      >+-identity</a
      ><a name="277" class="Symbol"
      >;</a
      ><a name="278"
      > </a
      ><a name="279" href="Properties.html#16962" class="Function"
      >+-suc</a
      ><a name="284" class="Symbol"
      >)</a
      ><a name="285"
      >
</a
      ><a name="286" class="Keyword"
      >open</a
      ><a name="290"
      > </a
      ><a name="291" class="Keyword"
      >import</a
      ><a name="297"
      > </a
      ><a name="298" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#1" class="Module"
      >Relation.Binary.PropositionalEquality</a
      ><a name="335"
      > </a
      ><a name="336" class="Keyword"
      >using</a
      ><a name="341"
      > </a
      ><a name="342" class="Symbol"
      >(</a
      ><a name="343" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >_&#8801;_</a
      ><a name="346" class="Symbol"
      >;</a
      ><a name="347"
      > </a
      ><a name="348" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="352" class="Symbol"
      >;</a
      ><a name="353"
      > </a
      ><a name="354" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.Core.html#565" class="Function"
      >sym</a
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
      ><a name="371" href="https://agda.github.io/agda-stdlib/Data.Product.html#1" class="Module"
      >Data.Product</a
      ><a name="383"
      > </a
      ><a name="384" class="Keyword"
      >using</a
      ><a name="389"
      > </a
      ><a name="390" class="Symbol"
      >(</a
      ><a name="391" href="https://agda.github.io/agda-stdlib/Data.Product.html#823" class="Function"
      >&#8707;</a
      ><a name="392" class="Symbol"
      >;</a
      ><a name="393"
      > </a
      ><a name="394" href="https://agda.github.io/agda-stdlib/Data.Product.html#509" class="InductiveConstructor Operator"
      >_,_</a
      ><a name="397" class="Symbol"
      >)</a
      ><a name="398"
      >
</a
      ><a name="399" class="Keyword"
      >open</a
      ><a name="403"
      > </a
      ><a name="404" href="Relations.html#16129" class="Module"
      >Trichotomy</a
      ><a name="414"
      >
</a
      ><a name="415" class="Keyword"
      >open</a
      ><a name="419"
      > </a
      ><a name="420" href="Relations.html#15375" class="Module Operator"
      >_&lt;_</a
      ><a name="423"
      >
</a
      ><a name="424" class="Keyword"
      >open</a
      ><a name="428"
      > </a
      ><a name="429" href="Relations.html#1114" class="Module Operator"
      >_&#8804;_</a
      ><a name="432"
      >
</a
      ><a name="433" class="Keyword"
      >open</a
      ><a name="437"
      > </a
      ><a name="438" href="Relations.html#17213" class="Module"
      >even</a
      ><a name="442"
      >
</a
      ><a name="443" class="Keyword"
      >open</a
      ><a name="447"
      > </a
      ><a name="448" href="Relations.html#17311" class="Module"
      >odd</a
      >
{% endraw %}</pre>

*Trichotomy*

<pre class="Agda">{% raw %}
<a name="491" href="RelationsAns.html#491" class="Function"
      >trichotomy</a
      ><a name="501"
      > </a
      ><a name="502" class="Symbol"
      >:</a
      ><a name="503"
      > </a
      ><a name="504" class="Symbol"
      >&#8704;</a
      ><a name="505"
      > </a
      ><a name="506" class="Symbol"
      >(</a
      ><a name="507" href="RelationsAns.html#507" class="Bound"
      >m</a
      ><a name="508"
      > </a
      ><a name="509" href="RelationsAns.html#509" class="Bound"
      >n</a
      ><a name="510"
      > </a
      ><a name="511" class="Symbol"
      >:</a
      ><a name="512"
      > </a
      ><a name="513" href="Naturals.html#1064" class="Datatype"
      >&#8469;</a
      ><a name="514" class="Symbol"
      >)</a
      ><a name="515"
      > </a
      ><a name="516" class="Symbol"
      >&#8594;</a
      ><a name="517"
      > </a
      ><a name="518" href="Relations.html#16129" class="Datatype"
      >Trichotomy</a
      ><a name="528"
      > </a
      ><a name="529" href="RelationsAns.html#507" class="Bound"
      >m</a
      ><a name="530"
      > </a
      ><a name="531" href="RelationsAns.html#509" class="Bound"
      >n</a
      ><a name="532"
      >
</a
      ><a name="533" href="RelationsAns.html#491" class="Function"
      >trichotomy</a
      ><a name="543"
      > </a
      ><a name="544" href="Naturals.html#1080" class="InductiveConstructor"
      >zero</a
      ><a name="548"
      > </a
      ><a name="549" href="Naturals.html#1080" class="InductiveConstructor"
      >zero</a
      ><a name="553"
      > </a
      ><a name="554" class="Symbol"
      >=</a
      ><a name="555"
      > </a
      ><a name="556" href="Relations.html#16208" class="InductiveConstructor"
      >same</a
      ><a name="560"
      > </a
      ><a name="561" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="565"
      >
</a
      ><a name="566" href="RelationsAns.html#491" class="Function"
      >trichotomy</a
      ><a name="576"
      > </a
      ><a name="577" href="Naturals.html#1080" class="InductiveConstructor"
      >zero</a
      ><a name="581"
      > </a
      ><a name="582" class="Symbol"
      >(</a
      ><a name="583" href="Naturals.html#1091" class="InductiveConstructor"
      >suc</a
      ><a name="586"
      > </a
      ><a name="587" href="RelationsAns.html#587" class="Bound"
      >n</a
      ><a name="588" class="Symbol"
      >)</a
      ><a name="589"
      > </a
      ><a name="590" class="Symbol"
      >=</a
      ><a name="591"
      > </a
      ><a name="592" href="Relations.html#16162" class="InductiveConstructor"
      >less</a
      ><a name="596"
      > </a
      ><a name="597" href="Relations.html#15401" class="InductiveConstructor"
      >z&lt;s</a
      ><a name="600"
      >
</a
      ><a name="601" href="RelationsAns.html#491" class="Function"
      >trichotomy</a
      ><a name="611"
      > </a
      ><a name="612" class="Symbol"
      >(</a
      ><a name="613" href="Naturals.html#1091" class="InductiveConstructor"
      >suc</a
      ><a name="616"
      > </a
      ><a name="617" href="RelationsAns.html#617" class="Bound"
      >m</a
      ><a name="618" class="Symbol"
      >)</a
      ><a name="619"
      > </a
      ><a name="620" href="Naturals.html#1080" class="InductiveConstructor"
      >zero</a
      ><a name="624"
      > </a
      ><a name="625" class="Symbol"
      >=</a
      ><a name="626"
      > </a
      ><a name="627" href="Relations.html#16254" class="InductiveConstructor"
      >more</a
      ><a name="631"
      > </a
      ><a name="632" href="Relations.html#15401" class="InductiveConstructor"
      >z&lt;s</a
      ><a name="635"
      >
</a
      ><a name="636" href="RelationsAns.html#491" class="Function"
      >trichotomy</a
      ><a name="646"
      > </a
      ><a name="647" class="Symbol"
      >(</a
      ><a name="648" href="Naturals.html#1091" class="InductiveConstructor"
      >suc</a
      ><a name="651"
      > </a
      ><a name="652" href="RelationsAns.html#652" class="Bound"
      >m</a
      ><a name="653" class="Symbol"
      >)</a
      ><a name="654"
      > </a
      ><a name="655" class="Symbol"
      >(</a
      ><a name="656" href="Naturals.html#1091" class="InductiveConstructor"
      >suc</a
      ><a name="659"
      > </a
      ><a name="660" href="RelationsAns.html#660" class="Bound"
      >n</a
      ><a name="661" class="Symbol"
      >)</a
      ><a name="662"
      > </a
      ><a name="663" class="Keyword"
      >with</a
      ><a name="667"
      > </a
      ><a name="668" href="RelationsAns.html#491" class="Function"
      >trichotomy</a
      ><a name="678"
      > </a
      ><a name="679" href="RelationsAns.html#652" class="Bound"
      >m</a
      ><a name="680"
      > </a
      ><a name="681" href="RelationsAns.html#660" class="Bound"
      >n</a
      ><a name="682"
      >
</a
      ><a name="683" class="Symbol"
      >...</a
      ><a name="686"
      > </a
      ><a name="687" class="Symbol"
      >|</a
      ><a name="688"
      > </a
      ><a name="689" href="Relations.html#16162" class="InductiveConstructor"
      >less</a
      ><a name="693"
      > </a
      ><a name="694" href="RelationsAns.html#694" class="Bound"
      >m&lt;n</a
      ><a name="697"
      > </a
      ><a name="698" class="Symbol"
      >=</a
      ><a name="699"
      > </a
      ><a name="700" href="Relations.html#16162" class="InductiveConstructor"
      >less</a
      ><a name="704"
      > </a
      ><a name="705" class="Symbol"
      >(</a
      ><a name="706" href="Relations.html#15434" class="InductiveConstructor"
      >s&lt;s</a
      ><a name="709"
      > </a
      ><a name="710" href="RelationsAns.html#694" class="Bound"
      >m&lt;n</a
      ><a name="713" class="Symbol"
      >)</a
      ><a name="714"
      >
</a
      ><a name="715" class="Symbol"
      >...</a
      ><a name="718"
      > </a
      ><a name="719" class="Symbol"
      >|</a
      ><a name="720"
      > </a
      ><a name="721" href="Relations.html#16208" class="InductiveConstructor"
      >same</a
      ><a name="725"
      > </a
      ><a name="726" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="730"
      > </a
      ><a name="731" class="Symbol"
      >=</a
      ><a name="732"
      > </a
      ><a name="733" href="Relations.html#16208" class="InductiveConstructor"
      >same</a
      ><a name="737"
      > </a
      ><a name="738" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="742"
      >
</a
      ><a name="743" class="Symbol"
      >...</a
      ><a name="746"
      > </a
      ><a name="747" class="Symbol"
      >|</a
      ><a name="748"
      > </a
      ><a name="749" href="Relations.html#16254" class="InductiveConstructor"
      >more</a
      ><a name="753"
      > </a
      ><a name="754" href="RelationsAns.html#754" class="Bound"
      >n&lt;m</a
      ><a name="757"
      > </a
      ><a name="758" class="Symbol"
      >=</a
      ><a name="759"
      > </a
      ><a name="760" href="Relations.html#16254" class="InductiveConstructor"
      >more</a
      ><a name="764"
      > </a
      ><a name="765" class="Symbol"
      >(</a
      ><a name="766" href="Relations.html#15434" class="InductiveConstructor"
      >s&lt;s</a
      ><a name="769"
      > </a
      ><a name="770" href="RelationsAns.html#754" class="Bound"
      >n&lt;m</a
      ><a name="773" class="Symbol"
      >)</a
      >
{% endraw %}</pre>

*Relate strict comparison to comparison*

<pre class="Agda">{% raw %}
<a name="842" href="RelationsAns.html#842" class="Function"
      >&lt;-implies-&#8804;</a
      ><a name="853"
      > </a
      ><a name="854" class="Symbol"
      >:</a
      ><a name="855"
      > </a
      ><a name="856" class="Symbol"
      >&#8704;</a
      ><a name="857"
      > </a
      ><a name="858" class="Symbol"
      >{</a
      ><a name="859" href="RelationsAns.html#859" class="Bound"
      >m</a
      ><a name="860"
      > </a
      ><a name="861" href="RelationsAns.html#861" class="Bound"
      >n</a
      ><a name="862"
      > </a
      ><a name="863" class="Symbol"
      >:</a
      ><a name="864"
      > </a
      ><a name="865" href="Naturals.html#1064" class="Datatype"
      >&#8469;</a
      ><a name="866" class="Symbol"
      >}</a
      ><a name="867"
      > </a
      ><a name="868" class="Symbol"
      >&#8594;</a
      ><a name="869"
      > </a
      ><a name="870" href="RelationsAns.html#859" class="Bound"
      >m</a
      ><a name="871"
      > </a
      ><a name="872" href="Relations.html#15375" class="Datatype Operator"
      >&lt;</a
      ><a name="873"
      > </a
      ><a name="874" href="RelationsAns.html#861" class="Bound"
      >n</a
      ><a name="875"
      > </a
      ><a name="876" class="Symbol"
      >&#8594;</a
      ><a name="877"
      > </a
      ><a name="878" href="Naturals.html#1091" class="InductiveConstructor"
      >suc</a
      ><a name="881"
      > </a
      ><a name="882" href="RelationsAns.html#859" class="Bound"
      >m</a
      ><a name="883"
      > </a
      ><a name="884" href="Relations.html#1114" class="Datatype Operator"
      >&#8804;</a
      ><a name="885"
      > </a
      ><a name="886" href="RelationsAns.html#861" class="Bound"
      >n</a
      ><a name="887"
      >
</a
      ><a name="888" href="RelationsAns.html#842" class="Function"
      >&lt;-implies-&#8804;</a
      ><a name="899"
      > </a
      ><a name="900" href="Relations.html#15401" class="InductiveConstructor"
      >z&lt;s</a
      ><a name="903"
      > </a
      ><a name="904" class="Symbol"
      >=</a
      ><a name="905"
      > </a
      ><a name="906" href="Relations.html#1169" class="InductiveConstructor"
      >s&#8804;s</a
      ><a name="909"
      > </a
      ><a name="910" href="Relations.html#1140" class="InductiveConstructor"
      >z&#8804;n</a
      ><a name="913"
      >
</a
      ><a name="914" href="RelationsAns.html#842" class="Function"
      >&lt;-implies-&#8804;</a
      ><a name="925"
      > </a
      ><a name="926" class="Symbol"
      >(</a
      ><a name="927" href="Relations.html#15434" class="InductiveConstructor"
      >s&lt;s</a
      ><a name="930"
      > </a
      ><a name="931" href="RelationsAns.html#931" class="Bound"
      >m&lt;n</a
      ><a name="934" class="Symbol"
      >)</a
      ><a name="935"
      > </a
      ><a name="936" class="Symbol"
      >=</a
      ><a name="937"
      > </a
      ><a name="938" href="Relations.html#1169" class="InductiveConstructor"
      >s&#8804;s</a
      ><a name="941"
      > </a
      ><a name="942" class="Symbol"
      >(</a
      ><a name="943" href="RelationsAns.html#842" class="Function"
      >&lt;-implies-&#8804;</a
      ><a name="954"
      > </a
      ><a name="955" href="RelationsAns.html#931" class="Bound"
      >m&lt;n</a
      ><a name="958" class="Symbol"
      >)</a
      ><a name="959"
      >

</a
      ><a name="961" href="RelationsAns.html#961" class="Function"
      >&#8804;-implies-&lt;</a
      ><a name="972"
      > </a
      ><a name="973" class="Symbol"
      >:</a
      ><a name="974"
      > </a
      ><a name="975" class="Symbol"
      >&#8704;</a
      ><a name="976"
      > </a
      ><a name="977" class="Symbol"
      >{</a
      ><a name="978" href="RelationsAns.html#978" class="Bound"
      >m</a
      ><a name="979"
      > </a
      ><a name="980" href="RelationsAns.html#980" class="Bound"
      >n</a
      ><a name="981"
      > </a
      ><a name="982" class="Symbol"
      >:</a
      ><a name="983"
      > </a
      ><a name="984" href="Naturals.html#1064" class="Datatype"
      >&#8469;</a
      ><a name="985" class="Symbol"
      >}</a
      ><a name="986"
      > </a
      ><a name="987" class="Symbol"
      >&#8594;</a
      ><a name="988"
      > </a
      ><a name="989" href="Naturals.html#1091" class="InductiveConstructor"
      >suc</a
      ><a name="992"
      > </a
      ><a name="993" href="RelationsAns.html#978" class="Bound"
      >m</a
      ><a name="994"
      > </a
      ><a name="995" href="Relations.html#1114" class="Datatype Operator"
      >&#8804;</a
      ><a name="996"
      > </a
      ><a name="997" href="RelationsAns.html#980" class="Bound"
      >n</a
      ><a name="998"
      > </a
      ><a name="999" class="Symbol"
      >&#8594;</a
      ><a name="1000"
      > </a
      ><a name="1001" href="RelationsAns.html#978" class="Bound"
      >m</a
      ><a name="1002"
      > </a
      ><a name="1003" href="Relations.html#15375" class="Datatype Operator"
      >&lt;</a
      ><a name="1004"
      > </a
      ><a name="1005" href="RelationsAns.html#980" class="Bound"
      >n</a
      ><a name="1006"
      >
</a
      ><a name="1007" href="RelationsAns.html#961" class="Function"
      >&#8804;-implies-&lt;</a
      ><a name="1018"
      > </a
      ><a name="1019" class="Symbol"
      >(</a
      ><a name="1020" href="Relations.html#1169" class="InductiveConstructor"
      >s&#8804;s</a
      ><a name="1023"
      > </a
      ><a name="1024" href="Relations.html#1140" class="InductiveConstructor"
      >z&#8804;n</a
      ><a name="1027" class="Symbol"
      >)</a
      ><a name="1028"
      > </a
      ><a name="1029" class="Symbol"
      >=</a
      ><a name="1030"
      > </a
      ><a name="1031" href="Relations.html#15401" class="InductiveConstructor"
      >z&lt;s</a
      ><a name="1034"
      >
</a
      ><a name="1035" href="RelationsAns.html#961" class="Function"
      >&#8804;-implies-&lt;</a
      ><a name="1046"
      > </a
      ><a name="1047" class="Symbol"
      >(</a
      ><a name="1048" href="Relations.html#1169" class="InductiveConstructor"
      >s&#8804;s</a
      ><a name="1051"
      > </a
      ><a name="1052" class="Symbol"
      >(</a
      ><a name="1053" href="Relations.html#1169" class="InductiveConstructor"
      >s&#8804;s</a
      ><a name="1056"
      > </a
      ><a name="1057" href="RelationsAns.html#1057" class="Bound"
      >m&#8804;n</a
      ><a name="1060" class="Symbol"
      >))</a
      ><a name="1062"
      > </a
      ><a name="1063" class="Symbol"
      >=</a
      ><a name="1064"
      > </a
      ><a name="1065" href="Relations.html#15434" class="InductiveConstructor"
      >s&lt;s</a
      ><a name="1068"
      > </a
      ><a name="1069" class="Symbol"
      >(</a
      ><a name="1070" href="RelationsAns.html#961" class="Function"
      >&#8804;-implies-&lt;</a
      ><a name="1081"
      > </a
      ><a name="1082" class="Symbol"
      >(</a
      ><a name="1083" href="Relations.html#1169" class="InductiveConstructor"
      >s&#8804;s</a
      ><a name="1086"
      > </a
      ><a name="1087" href="RelationsAns.html#1057" class="Bound"
      >m&#8804;n</a
      ><a name="1090" class="Symbol"
      >))</a
      >
{% endraw %}</pre>

*Even and odd*

<pre class="Agda">{% raw %}
<a name="1134" href="RelationsAns.html#1134" class="Function"
      >+-evev</a
      ><a name="1140"
      > </a
      ><a name="1141" class="Symbol"
      >:</a
      ><a name="1142"
      > </a
      ><a name="1143" class="Symbol"
      >&#8704;</a
      ><a name="1144"
      > </a
      ><a name="1145" class="Symbol"
      >{</a
      ><a name="1146" href="RelationsAns.html#1146" class="Bound"
      >m</a
      ><a name="1147"
      > </a
      ><a name="1148" href="RelationsAns.html#1148" class="Bound"
      >n</a
      ><a name="1149"
      > </a
      ><a name="1150" class="Symbol"
      >:</a
      ><a name="1151"
      > </a
      ><a name="1152" href="Naturals.html#1064" class="Datatype"
      >&#8469;</a
      ><a name="1153" class="Symbol"
      >}</a
      ><a name="1154"
      > </a
      ><a name="1155" class="Symbol"
      >&#8594;</a
      ><a name="1156"
      > </a
      ><a name="1157" href="Relations.html#17213" class="Datatype"
      >even</a
      ><a name="1161"
      > </a
      ><a name="1162" href="RelationsAns.html#1146" class="Bound"
      >m</a
      ><a name="1163"
      > </a
      ><a name="1164" class="Symbol"
      >&#8594;</a
      ><a name="1165"
      > </a
      ><a name="1166" href="Relations.html#17213" class="Datatype"
      >even</a
      ><a name="1170"
      > </a
      ><a name="1171" href="RelationsAns.html#1148" class="Bound"
      >n</a
      ><a name="1172"
      > </a
      ><a name="1173" class="Symbol"
      >&#8594;</a
      ><a name="1174"
      > </a
      ><a name="1175" href="Relations.html#17213" class="Datatype"
      >even</a
      ><a name="1179"
      > </a
      ><a name="1180" class="Symbol"
      >(</a
      ><a name="1181" href="RelationsAns.html#1146" class="Bound"
      >m</a
      ><a name="1182"
      > </a
      ><a name="1183" href="Naturals.html#9439" class="Primitive Operator"
      >+</a
      ><a name="1184"
      > </a
      ><a name="1185" href="RelationsAns.html#1148" class="Bound"
      >n</a
      ><a name="1186" class="Symbol"
      >)</a
      ><a name="1187"
      >
</a
      ><a name="1188" href="RelationsAns.html#1134" class="Function"
      >+-evev</a
      ><a name="1194"
      > </a
      ><a name="1195" href="Relations.html#17238" class="InductiveConstructor"
      >ev-zero</a
      ><a name="1202"
      > </a
      ><a name="1203" href="RelationsAns.html#1203" class="Bound"
      >evn</a
      ><a name="1206"
      > </a
      ><a name="1207" class="Symbol"
      >=</a
      ><a name="1208"
      > </a
      ><a name="1209" href="RelationsAns.html#1203" class="Bound"
      >evn</a
      ><a name="1212"
      >
</a
      ><a name="1213" href="RelationsAns.html#1134" class="Function"
      >+-evev</a
      ><a name="1219"
      > </a
      ><a name="1220" class="Symbol"
      >(</a
      ><a name="1221" href="Relations.html#17262" class="InductiveConstructor"
      >ev-suc</a
      ><a name="1227"
      > </a
      ><a name="1228" class="Symbol"
      >(</a
      ><a name="1229" href="Relations.html#17335" class="InductiveConstructor"
      >od-suc</a
      ><a name="1235"
      > </a
      ><a name="1236" href="RelationsAns.html#1236" class="Bound"
      >evm</a
      ><a name="1239" class="Symbol"
      >))</a
      ><a name="1241"
      > </a
      ><a name="1242" href="RelationsAns.html#1242" class="Bound"
      >evn</a
      ><a name="1245"
      > </a
      ><a name="1246" class="Symbol"
      >=</a
      ><a name="1247"
      > </a
      ><a name="1248" href="Relations.html#17262" class="InductiveConstructor"
      >ev-suc</a
      ><a name="1254"
      > </a
      ><a name="1255" class="Symbol"
      >(</a
      ><a name="1256" href="Relations.html#17335" class="InductiveConstructor"
      >od-suc</a
      ><a name="1262"
      > </a
      ><a name="1263" class="Symbol"
      >(</a
      ><a name="1264" href="RelationsAns.html#1134" class="Function"
      >+-evev</a
      ><a name="1270"
      > </a
      ><a name="1271" href="RelationsAns.html#1236" class="Bound"
      >evm</a
      ><a name="1274"
      > </a
      ><a name="1275" href="RelationsAns.html#1242" class="Bound"
      >evn</a
      ><a name="1278" class="Symbol"
      >))</a
      ><a name="1280"
      >

</a
      ><a name="1282" href="RelationsAns.html#1282" class="Function"
      >+-evod</a
      ><a name="1288"
      > </a
      ><a name="1289" class="Symbol"
      >:</a
      ><a name="1290"
      > </a
      ><a name="1291" class="Symbol"
      >&#8704;</a
      ><a name="1292"
      > </a
      ><a name="1293" class="Symbol"
      >{</a
      ><a name="1294" href="RelationsAns.html#1294" class="Bound"
      >m</a
      ><a name="1295"
      > </a
      ><a name="1296" href="RelationsAns.html#1296" class="Bound"
      >n</a
      ><a name="1297"
      > </a
      ><a name="1298" class="Symbol"
      >:</a
      ><a name="1299"
      > </a
      ><a name="1300" href="Naturals.html#1064" class="Datatype"
      >&#8469;</a
      ><a name="1301" class="Symbol"
      >}</a
      ><a name="1302"
      > </a
      ><a name="1303" class="Symbol"
      >&#8594;</a
      ><a name="1304"
      > </a
      ><a name="1305" href="Relations.html#17213" class="Datatype"
      >even</a
      ><a name="1309"
      > </a
      ><a name="1310" href="RelationsAns.html#1294" class="Bound"
      >m</a
      ><a name="1311"
      > </a
      ><a name="1312" class="Symbol"
      >&#8594;</a
      ><a name="1313"
      > </a
      ><a name="1314" href="Relations.html#17311" class="Datatype"
      >odd</a
      ><a name="1317"
      > </a
      ><a name="1318" href="RelationsAns.html#1296" class="Bound"
      >n</a
      ><a name="1319"
      > </a
      ><a name="1320" class="Symbol"
      >&#8594;</a
      ><a name="1321"
      > </a
      ><a name="1322" href="Relations.html#17311" class="Datatype"
      >odd</a
      ><a name="1325"
      > </a
      ><a name="1326" class="Symbol"
      >(</a
      ><a name="1327" href="RelationsAns.html#1294" class="Bound"
      >m</a
      ><a name="1328"
      > </a
      ><a name="1329" href="Naturals.html#9439" class="Primitive Operator"
      >+</a
      ><a name="1330"
      > </a
      ><a name="1331" href="RelationsAns.html#1296" class="Bound"
      >n</a
      ><a name="1332" class="Symbol"
      >)</a
      ><a name="1333"
      >
</a
      ><a name="1334" href="RelationsAns.html#1282" class="Function"
      >+-evod</a
      ><a name="1340"
      > </a
      ><a name="1341" href="Relations.html#17238" class="InductiveConstructor"
      >ev-zero</a
      ><a name="1348"
      > </a
      ><a name="1349" href="RelationsAns.html#1349" class="Bound"
      >odn</a
      ><a name="1352"
      > </a
      ><a name="1353" class="Symbol"
      >=</a
      ><a name="1354"
      > </a
      ><a name="1355" href="RelationsAns.html#1349" class="Bound"
      >odn</a
      ><a name="1358"
      >
</a
      ><a name="1359" href="RelationsAns.html#1282" class="Function"
      >+-evod</a
      ><a name="1365"
      > </a
      ><a name="1366" class="Symbol"
      >(</a
      ><a name="1367" href="Relations.html#17262" class="InductiveConstructor"
      >ev-suc</a
      ><a name="1373"
      > </a
      ><a name="1374" class="Symbol"
      >(</a
      ><a name="1375" href="Relations.html#17335" class="InductiveConstructor"
      >od-suc</a
      ><a name="1381"
      > </a
      ><a name="1382" href="RelationsAns.html#1382" class="Bound"
      >evm</a
      ><a name="1385" class="Symbol"
      >))</a
      ><a name="1387"
      > </a
      ><a name="1388" href="RelationsAns.html#1388" class="Bound"
      >odn</a
      ><a name="1391"
      > </a
      ><a name="1392" class="Symbol"
      >=</a
      ><a name="1393"
      > </a
      ><a name="1394" href="Relations.html#17335" class="InductiveConstructor"
      >od-suc</a
      ><a name="1400"
      > </a
      ><a name="1401" class="Symbol"
      >(</a
      ><a name="1402" href="Relations.html#17262" class="InductiveConstructor"
      >ev-suc</a
      ><a name="1408"
      > </a
      ><a name="1409" class="Symbol"
      >(</a
      ><a name="1410" href="RelationsAns.html#1282" class="Function"
      >+-evod</a
      ><a name="1416"
      > </a
      ><a name="1417" href="RelationsAns.html#1382" class="Bound"
      >evm</a
      ><a name="1420"
      > </a
      ><a name="1421" href="RelationsAns.html#1388" class="Bound"
      >odn</a
      ><a name="1424" class="Symbol"
      >))</a
      ><a name="1426"
      >

</a
      ><a name="1428" href="RelationsAns.html#1428" class="Function"
      >+-odev</a
      ><a name="1434"
      > </a
      ><a name="1435" class="Symbol"
      >:</a
      ><a name="1436"
      > </a
      ><a name="1437" class="Symbol"
      >&#8704;</a
      ><a name="1438"
      > </a
      ><a name="1439" class="Symbol"
      >{</a
      ><a name="1440" href="RelationsAns.html#1440" class="Bound"
      >m</a
      ><a name="1441"
      > </a
      ><a name="1442" href="RelationsAns.html#1442" class="Bound"
      >n</a
      ><a name="1443"
      > </a
      ><a name="1444" class="Symbol"
      >:</a
      ><a name="1445"
      > </a
      ><a name="1446" href="Naturals.html#1064" class="Datatype"
      >&#8469;</a
      ><a name="1447" class="Symbol"
      >}</a
      ><a name="1448"
      > </a
      ><a name="1449" class="Symbol"
      >&#8594;</a
      ><a name="1450"
      > </a
      ><a name="1451" href="Relations.html#17311" class="Datatype"
      >odd</a
      ><a name="1454"
      > </a
      ><a name="1455" href="RelationsAns.html#1440" class="Bound"
      >m</a
      ><a name="1456"
      > </a
      ><a name="1457" class="Symbol"
      >&#8594;</a
      ><a name="1458"
      > </a
      ><a name="1459" href="Relations.html#17213" class="Datatype"
      >even</a
      ><a name="1463"
      > </a
      ><a name="1464" href="RelationsAns.html#1442" class="Bound"
      >n</a
      ><a name="1465"
      > </a
      ><a name="1466" class="Symbol"
      >&#8594;</a
      ><a name="1467"
      > </a
      ><a name="1468" href="Relations.html#17311" class="Datatype"
      >odd</a
      ><a name="1471"
      > </a
      ><a name="1472" class="Symbol"
      >(</a
      ><a name="1473" href="RelationsAns.html#1440" class="Bound"
      >m</a
      ><a name="1474"
      > </a
      ><a name="1475" href="Naturals.html#9439" class="Primitive Operator"
      >+</a
      ><a name="1476"
      > </a
      ><a name="1477" href="RelationsAns.html#1442" class="Bound"
      >n</a
      ><a name="1478" class="Symbol"
      >)</a
      ><a name="1479"
      >
</a
      ><a name="1480" href="RelationsAns.html#1428" class="Function"
      >+-odev</a
      ><a name="1486"
      > </a
      ><a name="1487" class="Symbol"
      >(</a
      ><a name="1488" href="Relations.html#17335" class="InductiveConstructor"
      >od-suc</a
      ><a name="1494"
      > </a
      ><a name="1495" href="RelationsAns.html#1495" class="Bound"
      >evm</a
      ><a name="1498" class="Symbol"
      >)</a
      ><a name="1499"
      > </a
      ><a name="1500" href="RelationsAns.html#1500" class="Bound"
      >evn</a
      ><a name="1503"
      > </a
      ><a name="1504" class="Symbol"
      >=</a
      ><a name="1505"
      > </a
      ><a name="1506" href="Relations.html#17335" class="InductiveConstructor"
      >od-suc</a
      ><a name="1512"
      > </a
      ><a name="1513" class="Symbol"
      >(</a
      ><a name="1514" href="RelationsAns.html#1134" class="Function"
      >+-evev</a
      ><a name="1520"
      > </a
      ><a name="1521" href="RelationsAns.html#1495" class="Bound"
      >evm</a
      ><a name="1524"
      > </a
      ><a name="1525" href="RelationsAns.html#1500" class="Bound"
      >evn</a
      ><a name="1528" class="Symbol"
      >)</a
      ><a name="1529"
      >

</a
      ><a name="1531" href="RelationsAns.html#1531" class="Function"
      >+-odod</a
      ><a name="1537"
      > </a
      ><a name="1538" class="Symbol"
      >:</a
      ><a name="1539"
      > </a
      ><a name="1540" class="Symbol"
      >&#8704;</a
      ><a name="1541"
      > </a
      ><a name="1542" class="Symbol"
      >{</a
      ><a name="1543" href="RelationsAns.html#1543" class="Bound"
      >m</a
      ><a name="1544"
      > </a
      ><a name="1545" href="RelationsAns.html#1545" class="Bound"
      >n</a
      ><a name="1546"
      > </a
      ><a name="1547" class="Symbol"
      >:</a
      ><a name="1548"
      > </a
      ><a name="1549" href="Naturals.html#1064" class="Datatype"
      >&#8469;</a
      ><a name="1550" class="Symbol"
      >}</a
      ><a name="1551"
      > </a
      ><a name="1552" class="Symbol"
      >&#8594;</a
      ><a name="1553"
      > </a
      ><a name="1554" href="Relations.html#17311" class="Datatype"
      >odd</a
      ><a name="1557"
      > </a
      ><a name="1558" href="RelationsAns.html#1543" class="Bound"
      >m</a
      ><a name="1559"
      > </a
      ><a name="1560" class="Symbol"
      >&#8594;</a
      ><a name="1561"
      > </a
      ><a name="1562" href="Relations.html#17311" class="Datatype"
      >odd</a
      ><a name="1565"
      > </a
      ><a name="1566" href="RelationsAns.html#1545" class="Bound"
      >n</a
      ><a name="1567"
      > </a
      ><a name="1568" class="Symbol"
      >&#8594;</a
      ><a name="1569"
      > </a
      ><a name="1570" href="Relations.html#17213" class="Datatype"
      >even</a
      ><a name="1574"
      > </a
      ><a name="1575" class="Symbol"
      >(</a
      ><a name="1576" href="RelationsAns.html#1543" class="Bound"
      >m</a
      ><a name="1577"
      > </a
      ><a name="1578" href="Naturals.html#9439" class="Primitive Operator"
      >+</a
      ><a name="1579"
      > </a
      ><a name="1580" href="RelationsAns.html#1545" class="Bound"
      >n</a
      ><a name="1581" class="Symbol"
      >)</a
      ><a name="1582"
      >
</a
      ><a name="1583" href="RelationsAns.html#1531" class="Function"
      >+-odod</a
      ><a name="1589"
      > </a
      ><a name="1590" class="Symbol"
      >(</a
      ><a name="1591" href="Relations.html#17335" class="InductiveConstructor"
      >od-suc</a
      ><a name="1597"
      > </a
      ><a name="1598" href="RelationsAns.html#1598" class="Bound"
      >evm</a
      ><a name="1601" class="Symbol"
      >)</a
      ><a name="1602"
      > </a
      ><a name="1603" href="RelationsAns.html#1603" class="Bound"
      >odn</a
      ><a name="1606"
      > </a
      ><a name="1607" class="Symbol"
      >=</a
      ><a name="1608"
      > </a
      ><a name="1609" href="Relations.html#17262" class="InductiveConstructor"
      >ev-suc</a
      ><a name="1615"
      > </a
      ><a name="1616" class="Symbol"
      >(</a
      ><a name="1617" href="RelationsAns.html#1282" class="Function"
      >+-evod</a
      ><a name="1623"
      > </a
      ><a name="1624" href="RelationsAns.html#1598" class="Bound"
      >evm</a
      ><a name="1627"
      > </a
      ><a name="1628" href="RelationsAns.html#1603" class="Bound"
      >odn</a
      ><a name="1631" class="Symbol"
      >)</a
      >
{% endraw %}</pre>

<pre class="Agda">{% raw %}
<a name="1658" href="RelationsAns.html#1658" class="Function"
      >+-lemma</a
      ><a name="1665"
      > </a
      ><a name="1666" class="Symbol"
      >:</a
      ><a name="1667"
      > </a
      ><a name="1668" class="Symbol"
      >&#8704;</a
      ><a name="1669"
      > </a
      ><a name="1670" class="Symbol"
      >(</a
      ><a name="1671" href="RelationsAns.html#1671" class="Bound"
      >m</a
      ><a name="1672"
      > </a
      ><a name="1673" class="Symbol"
      >:</a
      ><a name="1674"
      > </a
      ><a name="1675" href="Naturals.html#1064" class="Datatype"
      >&#8469;</a
      ><a name="1676" class="Symbol"
      >)</a
      ><a name="1677"
      > </a
      ><a name="1678" class="Symbol"
      >&#8594;</a
      ><a name="1679"
      > </a
      ><a name="1680" href="Naturals.html#1091" class="InductiveConstructor"
      >suc</a
      ><a name="1683"
      > </a
      ><a name="1684" class="Symbol"
      >(</a
      ><a name="1685" href="Naturals.html#1091" class="InductiveConstructor"
      >suc</a
      ><a name="1688"
      > </a
      ><a name="1689" class="Symbol"
      >(</a
      ><a name="1690" href="RelationsAns.html#1671" class="Bound"
      >m</a
      ><a name="1691"
      > </a
      ><a name="1692" href="Naturals.html#9439" class="Primitive Operator"
      >+</a
      ><a name="1693"
      > </a
      ><a name="1694" class="Symbol"
      >(</a
      ><a name="1695" href="RelationsAns.html#1671" class="Bound"
      >m</a
      ><a name="1696"
      > </a
      ><a name="1697" href="Naturals.html#9439" class="Primitive Operator"
      >+</a
      ><a name="1698"
      > </a
      ><a name="1699" class="Number"
      >0</a
      ><a name="1700" class="Symbol"
      >)))</a
      ><a name="1703"
      > </a
      ><a name="1704" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="1705"
      > </a
      ><a name="1706" href="Naturals.html#1091" class="InductiveConstructor"
      >suc</a
      ><a name="1709"
      > </a
      ><a name="1710" href="RelationsAns.html#1671" class="Bound"
      >m</a
      ><a name="1711"
      > </a
      ><a name="1712" href="Naturals.html#9439" class="Primitive Operator"
      >+</a
      ><a name="1713"
      > </a
      ><a name="1714" class="Symbol"
      >(</a
      ><a name="1715" href="Naturals.html#1091" class="InductiveConstructor"
      >suc</a
      ><a name="1718"
      > </a
      ><a name="1719" href="RelationsAns.html#1671" class="Bound"
      >m</a
      ><a name="1720"
      > </a
      ><a name="1721" href="Naturals.html#9439" class="Primitive Operator"
      >+</a
      ><a name="1722"
      > </a
      ><a name="1723" class="Number"
      >0</a
      ><a name="1724" class="Symbol"
      >)</a
      ><a name="1725"
      >
</a
      ><a name="1726" href="RelationsAns.html#1658" class="Function"
      >+-lemma</a
      ><a name="1733"
      > </a
      ><a name="1734" href="RelationsAns.html#1734" class="Bound"
      >m</a
      ><a name="1735"
      > </a
      ><a name="1736" class="Keyword"
      >rewrite</a
      ><a name="1743"
      > </a
      ><a name="1744" href="Properties.html#16853" class="Function"
      >+-identity</a
      ><a name="1754"
      > </a
      ><a name="1755" href="RelationsAns.html#1734" class="Bound"
      >m</a
      ><a name="1756"
      > </a
      ><a name="1757" class="Symbol"
      >|</a
      ><a name="1758"
      > </a
      ><a name="1759" href="Properties.html#16962" class="Function"
      >+-suc</a
      ><a name="1764"
      > </a
      ><a name="1765" href="RelationsAns.html#1734" class="Bound"
      >m</a
      ><a name="1766"
      > </a
      ><a name="1767" href="RelationsAns.html#1734" class="Bound"
      >m</a
      ><a name="1768"
      > </a
      ><a name="1769" class="Symbol"
      >=</a
      ><a name="1770"
      > </a
      ><a name="1771" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="1775"
      >

</a
      ><a name="1777" href="RelationsAns.html#1777" class="Function"
      >+-lemma&#8242;</a
      ><a name="1785"
      > </a
      ><a name="1786" class="Symbol"
      >:</a
      ><a name="1787"
      > </a
      ><a name="1788" class="Symbol"
      >&#8704;</a
      ><a name="1789"
      > </a
      ><a name="1790" class="Symbol"
      >(</a
      ><a name="1791" href="RelationsAns.html#1791" class="Bound"
      >m</a
      ><a name="1792"
      > </a
      ><a name="1793" class="Symbol"
      >:</a
      ><a name="1794"
      > </a
      ><a name="1795" href="Naturals.html#1064" class="Datatype"
      >&#8469;</a
      ><a name="1796" class="Symbol"
      >)</a
      ><a name="1797"
      > </a
      ><a name="1798" class="Symbol"
      >&#8594;</a
      ><a name="1799"
      > </a
      ><a name="1800" href="Naturals.html#1091" class="InductiveConstructor"
      >suc</a
      ><a name="1803"
      > </a
      ><a name="1804" class="Symbol"
      >(</a
      ><a name="1805" href="Naturals.html#1091" class="InductiveConstructor"
      >suc</a
      ><a name="1808"
      > </a
      ><a name="1809" class="Symbol"
      >(</a
      ><a name="1810" href="RelationsAns.html#1791" class="Bound"
      >m</a
      ><a name="1811"
      > </a
      ><a name="1812" href="Naturals.html#9439" class="Primitive Operator"
      >+</a
      ><a name="1813"
      > </a
      ><a name="1814" class="Symbol"
      >(</a
      ><a name="1815" href="RelationsAns.html#1791" class="Bound"
      >m</a
      ><a name="1816"
      > </a
      ><a name="1817" href="Naturals.html#9439" class="Primitive Operator"
      >+</a
      ><a name="1818"
      > </a
      ><a name="1819" class="Number"
      >0</a
      ><a name="1820" class="Symbol"
      >)))</a
      ><a name="1823"
      > </a
      ><a name="1824" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="1825"
      > </a
      ><a name="1826" href="Naturals.html#1091" class="InductiveConstructor"
      >suc</a
      ><a name="1829"
      > </a
      ><a name="1830" href="RelationsAns.html#1791" class="Bound"
      >m</a
      ><a name="1831"
      > </a
      ><a name="1832" href="Naturals.html#9439" class="Primitive Operator"
      >+</a
      ><a name="1833"
      > </a
      ><a name="1834" class="Symbol"
      >(</a
      ><a name="1835" href="Naturals.html#1091" class="InductiveConstructor"
      >suc</a
      ><a name="1838"
      > </a
      ><a name="1839" href="RelationsAns.html#1791" class="Bound"
      >m</a
      ><a name="1840"
      > </a
      ><a name="1841" href="Naturals.html#9439" class="Primitive Operator"
      >+</a
      ><a name="1842"
      > </a
      ><a name="1843" class="Number"
      >0</a
      ><a name="1844" class="Symbol"
      >)</a
      ><a name="1845"
      >
</a
      ><a name="1846" href="RelationsAns.html#1777" class="Function"
      >+-lemma&#8242;</a
      ><a name="1854"
      > </a
      ><a name="1855" href="RelationsAns.html#1855" class="Bound"
      >m</a
      ><a name="1856"
      > </a
      ><a name="1857" class="Keyword"
      >rewrite</a
      ><a name="1864"
      > </a
      ><a name="1865" href="Properties.html#16962" class="Function"
      >+-suc</a
      ><a name="1870"
      > </a
      ><a name="1871" href="RelationsAns.html#1855" class="Bound"
      >m</a
      ><a name="1872"
      > </a
      ><a name="1873" class="Symbol"
      >(</a
      ><a name="1874" href="RelationsAns.html#1855" class="Bound"
      >m</a
      ><a name="1875"
      > </a
      ><a name="1876" href="Naturals.html#9439" class="Primitive Operator"
      >+</a
      ><a name="1877"
      > </a
      ><a name="1878" class="Number"
      >0</a
      ><a name="1879" class="Symbol"
      >)</a
      ><a name="1880"
      > </a
      ><a name="1881" class="Symbol"
      >=</a
      ><a name="1882"
      > </a
      ><a name="1883" class="Symbol"
      >{!!}</a
      ><a name="1887"
      >

</a
      ><a name="1889" class="Keyword"
      >mutual</a
      ><a name="1895"
      >
  </a
      ><a name="1898" href="RelationsAns.html#1898" class="Function"
      >is-even</a
      ><a name="1905"
      > </a
      ><a name="1906" class="Symbol"
      >:</a
      ><a name="1907"
      > </a
      ><a name="1908" class="Symbol"
      >&#8704;</a
      ><a name="1909"
      > </a
      ><a name="1910" class="Symbol"
      >(</a
      ><a name="1911" href="RelationsAns.html#1911" class="Bound"
      >n</a
      ><a name="1912"
      > </a
      ><a name="1913" class="Symbol"
      >:</a
      ><a name="1914"
      > </a
      ><a name="1915" href="Naturals.html#1064" class="Datatype"
      >&#8469;</a
      ><a name="1916" class="Symbol"
      >)</a
      ><a name="1917"
      > </a
      ><a name="1918" class="Symbol"
      >&#8594;</a
      ><a name="1919"
      > </a
      ><a name="1920" href="Relations.html#17213" class="Datatype"
      >even</a
      ><a name="1924"
      > </a
      ><a name="1925" href="RelationsAns.html#1911" class="Bound"
      >n</a
      ><a name="1926"
      > </a
      ><a name="1927" class="Symbol"
      >&#8594;</a
      ><a name="1928"
      > </a
      ><a name="1929" href="https://agda.github.io/agda-stdlib/Data.Product.html#823" class="Function"
      >&#8707;</a
      ><a name="1930" class="Symbol"
      >(&#955;</a
      ><a name="1932"
      > </a
      ><a name="1933" class="Symbol"
      >(</a
      ><a name="1934" href="RelationsAns.html#1934" class="Bound"
      >m</a
      ><a name="1935"
      > </a
      ><a name="1936" class="Symbol"
      >:</a
      ><a name="1937"
      > </a
      ><a name="1938" href="Naturals.html#1064" class="Datatype"
      >&#8469;</a
      ><a name="1939" class="Symbol"
      >)</a
      ><a name="1940"
      > </a
      ><a name="1941" class="Symbol"
      >&#8594;</a
      ><a name="1942"
      > </a
      ><a name="1943" href="RelationsAns.html#1911" class="Bound"
      >n</a
      ><a name="1944"
      > </a
      ><a name="1945" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="1946"
      > </a
      ><a name="1947" class="Number"
      >2</a
      ><a name="1948"
      > </a
      ><a name="1949" href="Naturals.html#12016" class="Primitive Operator"
      >*</a
      ><a name="1950"
      > </a
      ><a name="1951" href="RelationsAns.html#1934" class="Bound"
      >m</a
      ><a name="1952" class="Symbol"
      >)</a
      ><a name="1953"
      >
  </a
      ><a name="1956" href="RelationsAns.html#1898" class="Function"
      >is-even</a
      ><a name="1963"
      > </a
      ><a name="1964" href="Naturals.html#1080" class="InductiveConstructor"
      >zero</a
      ><a name="1968"
      > </a
      ><a name="1969" href="Relations.html#17238" class="InductiveConstructor"
      >ev-zero</a
      ><a name="1976"
      > </a
      ><a name="1977" class="Symbol"
      >=</a
      ><a name="1978"
      >  </a
      ><a name="1980" href="Naturals.html#1080" class="InductiveConstructor"
      >zero</a
      ><a name="1984"
      > </a
      ><a name="1985" href="https://agda.github.io/agda-stdlib/Data.Product.html#509" class="InductiveConstructor Operator"
      >,</a
      ><a name="1986"
      > </a
      ><a name="1987" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="1991"
      >
  </a
      ><a name="1994" href="RelationsAns.html#1898" class="Function"
      >is-even</a
      ><a name="2001"
      > </a
      ><a name="2002" class="Symbol"
      >(</a
      ><a name="2003" href="Naturals.html#1091" class="InductiveConstructor"
      >suc</a
      ><a name="2006"
      > </a
      ><a name="2007" href="RelationsAns.html#2007" class="Bound"
      >n</a
      ><a name="2008" class="Symbol"
      >)</a
      ><a name="2009"
      > </a
      ><a name="2010" class="Symbol"
      >(</a
      ><a name="2011" href="Relations.html#17262" class="InductiveConstructor"
      >ev-suc</a
      ><a name="2017"
      > </a
      ><a name="2018" href="RelationsAns.html#2018" class="Bound"
      >odn</a
      ><a name="2021" class="Symbol"
      >)</a
      ><a name="2022"
      > </a
      ><a name="2023" class="Keyword"
      >with</a
      ><a name="2027"
      > </a
      ><a name="2028" href="RelationsAns.html#2107" class="Function"
      >is-odd</a
      ><a name="2034"
      > </a
      ><a name="2035" href="RelationsAns.html#2007" class="Bound"
      >n</a
      ><a name="2036"
      > </a
      ><a name="2037" href="RelationsAns.html#2018" class="Bound"
      >odn</a
      ><a name="2040"
      >
  </a
      ><a name="2043" class="Symbol"
      >...</a
      ><a name="2046"
      > </a
      ><a name="2047" class="Symbol"
      >|</a
      ><a name="2048"
      > </a
      ><a name="2049" href="RelationsAns.html#2049" class="Bound"
      >m</a
      ><a name="2050"
      > </a
      ><a name="2051" href="https://agda.github.io/agda-stdlib/Data.Product.html#509" class="InductiveConstructor Operator"
      >,</a
      ><a name="2052"
      > </a
      ><a name="2053" href="RelationsAns.html#2053" class="Bound"
      >n&#8801;1+2*m</a
      ><a name="2060"
      > </a
      ><a name="2061" class="Keyword"
      >rewrite</a
      ><a name="2068"
      > </a
      ><a name="2069" href="RelationsAns.html#2053" class="Bound"
      >n&#8801;1+2*m</a
      ><a name="2076"
      > </a
      ><a name="2077" class="Symbol"
      >|</a
      ><a name="2078"
      > </a
      ><a name="2079" href="RelationsAns.html#1658" class="Function"
      >+-lemma</a
      ><a name="2086"
      > </a
      ><a name="2087" href="RelationsAns.html#2049" class="Bound"
      >m</a
      ><a name="2088"
      > </a
      ><a name="2089" class="Symbol"
      >=</a
      ><a name="2090"
      > </a
      ><a name="2091" href="Naturals.html#1091" class="InductiveConstructor"
      >suc</a
      ><a name="2094"
      > </a
      ><a name="2095" href="RelationsAns.html#2049" class="Bound"
      >m</a
      ><a name="2096"
      > </a
      ><a name="2097" href="https://agda.github.io/agda-stdlib/Data.Product.html#509" class="InductiveConstructor Operator"
      >,</a
      ><a name="2098"
      > </a
      ><a name="2099" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="2103"
      >

  </a
      ><a name="2107" href="RelationsAns.html#2107" class="Function"
      >is-odd</a
      ><a name="2113"
      > </a
      ><a name="2114" class="Symbol"
      >:</a
      ><a name="2115"
      > </a
      ><a name="2116" class="Symbol"
      >&#8704;</a
      ><a name="2117"
      > </a
      ><a name="2118" class="Symbol"
      >(</a
      ><a name="2119" href="RelationsAns.html#2119" class="Bound"
      >n</a
      ><a name="2120"
      > </a
      ><a name="2121" class="Symbol"
      >:</a
      ><a name="2122"
      > </a
      ><a name="2123" href="Naturals.html#1064" class="Datatype"
      >&#8469;</a
      ><a name="2124" class="Symbol"
      >)</a
      ><a name="2125"
      > </a
      ><a name="2126" class="Symbol"
      >&#8594;</a
      ><a name="2127"
      > </a
      ><a name="2128" href="Relations.html#17311" class="Datatype"
      >odd</a
      ><a name="2131"
      > </a
      ><a name="2132" href="RelationsAns.html#2119" class="Bound"
      >n</a
      ><a name="2133"
      > </a
      ><a name="2134" class="Symbol"
      >&#8594;</a
      ><a name="2135"
      > </a
      ><a name="2136" href="https://agda.github.io/agda-stdlib/Data.Product.html#823" class="Function"
      >&#8707;</a
      ><a name="2137" class="Symbol"
      >(&#955;</a
      ><a name="2139"
      > </a
      ><a name="2140" class="Symbol"
      >(</a
      ><a name="2141" href="RelationsAns.html#2141" class="Bound"
      >m</a
      ><a name="2142"
      > </a
      ><a name="2143" class="Symbol"
      >:</a
      ><a name="2144"
      > </a
      ><a name="2145" href="Naturals.html#1064" class="Datatype"
      >&#8469;</a
      ><a name="2146" class="Symbol"
      >)</a
      ><a name="2147"
      > </a
      ><a name="2148" class="Symbol"
      >&#8594;</a
      ><a name="2149"
      > </a
      ><a name="2150" href="RelationsAns.html#2119" class="Bound"
      >n</a
      ><a name="2151"
      > </a
      ><a name="2152" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="2153"
      > </a
      ><a name="2154" class="Number"
      >1</a
      ><a name="2155"
      > </a
      ><a name="2156" href="Naturals.html#9439" class="Primitive Operator"
      >+</a
      ><a name="2157"
      > </a
      ><a name="2158" class="Number"
      >2</a
      ><a name="2159"
      > </a
      ><a name="2160" href="Naturals.html#12016" class="Primitive Operator"
      >*</a
      ><a name="2161"
      > </a
      ><a name="2162" href="RelationsAns.html#2141" class="Bound"
      >m</a
      ><a name="2163" class="Symbol"
      >)</a
      ><a name="2164"
      >
  </a
      ><a name="2167" href="RelationsAns.html#2107" class="Function"
      >is-odd</a
      ><a name="2173"
      > </a
      ><a name="2174" class="Symbol"
      >(</a
      ><a name="2175" href="Naturals.html#1091" class="InductiveConstructor"
      >suc</a
      ><a name="2178"
      > </a
      ><a name="2179" href="RelationsAns.html#2179" class="Bound"
      >n</a
      ><a name="2180" class="Symbol"
      >)</a
      ><a name="2181"
      > </a
      ><a name="2182" class="Symbol"
      >(</a
      ><a name="2183" href="Relations.html#17335" class="InductiveConstructor"
      >od-suc</a
      ><a name="2189"
      > </a
      ><a name="2190" href="RelationsAns.html#2190" class="Bound"
      >evn</a
      ><a name="2193" class="Symbol"
      >)</a
      ><a name="2194"
      > </a
      ><a name="2195" class="Keyword"
      >with</a
      ><a name="2199"
      > </a
      ><a name="2200" href="RelationsAns.html#1898" class="Function"
      >is-even</a
      ><a name="2207"
      > </a
      ><a name="2208" href="RelationsAns.html#2179" class="Bound"
      >n</a
      ><a name="2209"
      > </a
      ><a name="2210" href="RelationsAns.html#2190" class="Bound"
      >evn</a
      ><a name="2213"
      >
  </a
      ><a name="2216" class="Symbol"
      >...</a
      ><a name="2219"
      > </a
      ><a name="2220" class="Symbol"
      >|</a
      ><a name="2221"
      > </a
      ><a name="2222" href="RelationsAns.html#2222" class="Bound"
      >m</a
      ><a name="2223"
      > </a
      ><a name="2224" href="https://agda.github.io/agda-stdlib/Data.Product.html#509" class="InductiveConstructor Operator"
      >,</a
      ><a name="2225"
      > </a
      ><a name="2226" href="RelationsAns.html#2226" class="Bound"
      >n&#8801;2*m</a
      ><a name="2231"
      > </a
      ><a name="2232" class="Keyword"
      >rewrite</a
      ><a name="2239"
      > </a
      ><a name="2240" href="RelationsAns.html#2226" class="Bound"
      >n&#8801;2*m</a
      ><a name="2245"
      > </a
      ><a name="2246" class="Symbol"
      >=</a
      ><a name="2247"
      > </a
      ><a name="2248" href="RelationsAns.html#2222" class="Bound"
      >m</a
      ><a name="2249"
      > </a
      ><a name="2250" href="https://agda.github.io/agda-stdlib/Data.Product.html#509" class="InductiveConstructor Operator"
      >,</a
      ><a name="2251"
      > </a
      ><a name="2252" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      >
{% endraw %}</pre>

    
