---
title     : "Properties Exercises"
layout    : page
permalink : /PropertiesEx
---

<pre class="Agda">{% raw %}
<a name="101" class="Keyword"
      >open</a
      ><a name="105"
      > </a
      ><a name="106" class="Keyword"
      >import</a
      ><a name="112"
      > </a
      ><a name="113" class="Module"
      >Naturals</a
      ><a name="121"
      > </a
      ><a name="122" class="Keyword"
      >using</a
      ><a name="127"
      > </a
      ><a name="128" class="Symbol"
      >(</a
      ><a name="129" href="Naturals.html#1064" class="Datatype"
      >&#8469;</a
      ><a name="130" class="Symbol"
      >;</a
      ><a name="131"
      > </a
      ><a name="132" href="Naturals.html#1091" class="InductiveConstructor"
      >suc</a
      ><a name="135" class="Symbol"
      >;</a
      ><a name="136"
      > </a
      ><a name="137" href="Naturals.html#1080" class="InductiveConstructor"
      >zero</a
      ><a name="141" class="Symbol"
      >;</a
      ><a name="142"
      > </a
      ><a name="143" href="Naturals.html#9439" class="Primitive Operator"
      >_+_</a
      ><a name="146" class="Symbol"
      >;</a
      ><a name="147"
      > </a
      ><a name="148" href="Naturals.html#12016" class="Primitive Operator"
      >_*_</a
      ><a name="151" class="Symbol"
      >;</a
      ><a name="152"
      > </a
      ><a name="153" href="Naturals.html#13851" class="Primitive Operator"
      >_&#8760;_</a
      ><a name="156" class="Symbol"
      >)</a
      ><a name="157"
      >
</a
      ><a name="158" class="Keyword"
      >open</a
      ><a name="162"
      > </a
      ><a name="163" class="Keyword"
      >import</a
      ><a name="169"
      > </a
      ><a name="170" class="Module"
      >Properties</a
      ><a name="180"
      > </a
      ><a name="181" class="Keyword"
      >using</a
      ><a name="186"
      > </a
      ><a name="187" class="Symbol"
      >(</a
      ><a name="188" href="Properties.html#7291" class="Function"
      >+-assoc</a
      ><a name="195" class="Symbol"
      >;</a
      ><a name="196"
      > </a
      ><a name="197" href="Properties.html#17070" class="Function"
      >+-comm</a
      ><a name="203" class="Symbol"
      >)</a
      ><a name="204"
      >
</a
      ><a name="205" class="Keyword"
      >open</a
      ><a name="209"
      > </a
      ><a name="210" class="Keyword"
      >import</a
      ><a name="216"
      > </a
      ><a name="217" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#1" class="Module"
      >Relation.Binary.PropositionalEquality</a
      ><a name="254"
      > </a
      ><a name="255" class="Keyword"
      >using</a
      ><a name="260"
      > </a
      ><a name="261" class="Symbol"
      >(</a
      ><a name="262" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >_&#8801;_</a
      ><a name="265" class="Symbol"
      >;</a
      ><a name="266"
      > </a
      ><a name="267" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="271" class="Symbol"
      >;</a
      ><a name="272"
      > </a
      ><a name="273" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.Core.html#565" class="Function"
      >sym</a
      ><a name="276" class="Symbol"
      >)</a
      >
{% endraw %}</pre>

*Swapping terms*

<pre class="Agda">{% raw %}
<a name="322" href="PropertiesEx.html#322" class="Function"
      >+-swap</a
      ><a name="328"
      > </a
      ><a name="329" class="Symbol"
      >:</a
      ><a name="330"
      > </a
      ><a name="331" class="Symbol"
      >&#8704;</a
      ><a name="332"
      > </a
      ><a name="333" class="Symbol"
      >(</a
      ><a name="334" href="PropertiesEx.html#334" class="Bound"
      >m</a
      ><a name="335"
      > </a
      ><a name="336" href="PropertiesEx.html#336" class="Bound"
      >n</a
      ><a name="337"
      > </a
      ><a name="338" href="PropertiesEx.html#338" class="Bound"
      >p</a
      ><a name="339"
      > </a
      ><a name="340" class="Symbol"
      >:</a
      ><a name="341"
      > </a
      ><a name="342" href="Naturals.html#1064" class="Datatype"
      >&#8469;</a
      ><a name="343" class="Symbol"
      >)</a
      ><a name="344"
      > </a
      ><a name="345" class="Symbol"
      >&#8594;</a
      ><a name="346"
      > </a
      ><a name="347" href="PropertiesEx.html#334" class="Bound"
      >m</a
      ><a name="348"
      > </a
      ><a name="349" href="Naturals.html#9439" class="Primitive Operator"
      >+</a
      ><a name="350"
      > </a
      ><a name="351" class="Symbol"
      >(</a
      ><a name="352" href="PropertiesEx.html#336" class="Bound"
      >n</a
      ><a name="353"
      > </a
      ><a name="354" href="Naturals.html#9439" class="Primitive Operator"
      >+</a
      ><a name="355"
      > </a
      ><a name="356" href="PropertiesEx.html#338" class="Bound"
      >p</a
      ><a name="357" class="Symbol"
      >)</a
      ><a name="358"
      > </a
      ><a name="359" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="360"
      > </a
      ><a name="361" href="PropertiesEx.html#336" class="Bound"
      >n</a
      ><a name="362"
      > </a
      ><a name="363" href="Naturals.html#9439" class="Primitive Operator"
      >+</a
      ><a name="364"
      > </a
      ><a name="365" class="Symbol"
      >(</a
      ><a name="366" href="PropertiesEx.html#334" class="Bound"
      >m</a
      ><a name="367"
      > </a
      ><a name="368" href="Naturals.html#9439" class="Primitive Operator"
      >+</a
      ><a name="369"
      > </a
      ><a name="370" href="PropertiesEx.html#338" class="Bound"
      >p</a
      ><a name="371" class="Symbol"
      >)</a
      ><a name="372"
      >
</a
      ><a name="373" href="PropertiesEx.html#322" class="Function"
      >+-swap</a
      ><a name="379"
      > </a
      ><a name="380" href="PropertiesEx.html#380" class="Bound"
      >m</a
      ><a name="381"
      > </a
      ><a name="382" href="PropertiesEx.html#382" class="Bound"
      >n</a
      ><a name="383"
      > </a
      ><a name="384" href="PropertiesEx.html#384" class="Bound"
      >p</a
      ><a name="385"
      > </a
      ><a name="386" class="Keyword"
      >rewrite</a
      ><a name="393"
      > </a
      ><a name="394" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.Core.html#565" class="Function"
      >sym</a
      ><a name="397"
      > </a
      ><a name="398" class="Symbol"
      >(</a
      ><a name="399" href="Properties.html#7291" class="Function"
      >+-assoc</a
      ><a name="406"
      > </a
      ><a name="407" href="PropertiesEx.html#380" class="Bound"
      >m</a
      ><a name="408"
      > </a
      ><a name="409" href="PropertiesEx.html#382" class="Bound"
      >n</a
      ><a name="410"
      > </a
      ><a name="411" href="PropertiesEx.html#384" class="Bound"
      >p</a
      ><a name="412" class="Symbol"
      >)</a
      ><a name="413"
      > </a
      ><a name="414" class="Symbol"
      >|</a
      ><a name="415"
      > </a
      ><a name="416" href="Properties.html#17070" class="Function"
      >+-comm</a
      ><a name="422"
      > </a
      ><a name="423" href="PropertiesEx.html#380" class="Bound"
      >m</a
      ><a name="424"
      > </a
      ><a name="425" href="PropertiesEx.html#382" class="Bound"
      >n</a
      ><a name="426"
      > </a
      ><a name="427" class="Symbol"
      >|</a
      ><a name="428"
      > </a
      ><a name="429" href="Properties.html#7291" class="Function"
      >+-assoc</a
      ><a name="436"
      > </a
      ><a name="437" href="PropertiesEx.html#382" class="Bound"
      >n</a
      ><a name="438"
      > </a
      ><a name="439" href="PropertiesEx.html#380" class="Bound"
      >m</a
      ><a name="440"
      > </a
      ><a name="441" href="PropertiesEx.html#384" class="Bound"
      >p</a
      ><a name="442"
      > </a
      ><a name="443" class="Symbol"
      >=</a
      ><a name="444"
      > </a
      ><a name="445" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      >
{% endraw %}</pre>

*Multiplication distributes over addition*

<pre class="Agda">{% raw %}
<a name="519" href="PropertiesEx.html#519" class="Function"
      >*-distrib-+</a
      ><a name="530"
      > </a
      ><a name="531" class="Symbol"
      >:</a
      ><a name="532"
      > </a
      ><a name="533" class="Symbol"
      >&#8704;</a
      ><a name="534"
      > </a
      ><a name="535" class="Symbol"
      >(</a
      ><a name="536" href="PropertiesEx.html#536" class="Bound"
      >m</a
      ><a name="537"
      > </a
      ><a name="538" href="PropertiesEx.html#538" class="Bound"
      >n</a
      ><a name="539"
      > </a
      ><a name="540" href="PropertiesEx.html#540" class="Bound"
      >p</a
      ><a name="541"
      > </a
      ><a name="542" class="Symbol"
      >:</a
      ><a name="543"
      > </a
      ><a name="544" href="Naturals.html#1064" class="Datatype"
      >&#8469;</a
      ><a name="545" class="Symbol"
      >)</a
      ><a name="546"
      > </a
      ><a name="547" class="Symbol"
      >&#8594;</a
      ><a name="548"
      > </a
      ><a name="549" class="Symbol"
      >(</a
      ><a name="550" href="PropertiesEx.html#536" class="Bound"
      >m</a
      ><a name="551"
      > </a
      ><a name="552" href="Naturals.html#9439" class="Primitive Operator"
      >+</a
      ><a name="553"
      > </a
      ><a name="554" href="PropertiesEx.html#538" class="Bound"
      >n</a
      ><a name="555" class="Symbol"
      >)</a
      ><a name="556"
      > </a
      ><a name="557" href="Naturals.html#12016" class="Primitive Operator"
      >*</a
      ><a name="558"
      > </a
      ><a name="559" href="PropertiesEx.html#540" class="Bound"
      >p</a
      ><a name="560"
      > </a
      ><a name="561" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="562"
      > </a
      ><a name="563" href="PropertiesEx.html#536" class="Bound"
      >m</a
      ><a name="564"
      > </a
      ><a name="565" href="Naturals.html#12016" class="Primitive Operator"
      >*</a
      ><a name="566"
      > </a
      ><a name="567" href="PropertiesEx.html#540" class="Bound"
      >p</a
      ><a name="568"
      > </a
      ><a name="569" href="Naturals.html#9439" class="Primitive Operator"
      >+</a
      ><a name="570"
      > </a
      ><a name="571" href="PropertiesEx.html#538" class="Bound"
      >n</a
      ><a name="572"
      > </a
      ><a name="573" href="Naturals.html#12016" class="Primitive Operator"
      >*</a
      ><a name="574"
      > </a
      ><a name="575" href="PropertiesEx.html#540" class="Bound"
      >p</a
      ><a name="576"
      >
</a
      ><a name="577" href="PropertiesEx.html#519" class="Function"
      >*-distrib-+</a
      ><a name="588"
      > </a
      ><a name="589" href="Naturals.html#1080" class="InductiveConstructor"
      >zero</a
      ><a name="593"
      > </a
      ><a name="594" href="PropertiesEx.html#594" class="Bound"
      >n</a
      ><a name="595"
      > </a
      ><a name="596" href="PropertiesEx.html#596" class="Bound"
      >p</a
      ><a name="597"
      > </a
      ><a name="598" class="Symbol"
      >=</a
      ><a name="599"
      > </a
      ><a name="600" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="604"
      >
</a
      ><a name="605" href="PropertiesEx.html#519" class="Function"
      >*-distrib-+</a
      ><a name="616"
      > </a
      ><a name="617" class="Symbol"
      >(</a
      ><a name="618" href="Naturals.html#1091" class="InductiveConstructor"
      >suc</a
      ><a name="621"
      > </a
      ><a name="622" href="PropertiesEx.html#622" class="Bound"
      >m</a
      ><a name="623" class="Symbol"
      >)</a
      ><a name="624"
      > </a
      ><a name="625" href="PropertiesEx.html#625" class="Bound"
      >n</a
      ><a name="626"
      > </a
      ><a name="627" href="PropertiesEx.html#627" class="Bound"
      >p</a
      ><a name="628"
      > </a
      ><a name="629" class="Keyword"
      >rewrite</a
      ><a name="636"
      > </a
      ><a name="637" href="PropertiesEx.html#519" class="Function"
      >*-distrib-+</a
      ><a name="648"
      > </a
      ><a name="649" href="PropertiesEx.html#622" class="Bound"
      >m</a
      ><a name="650"
      > </a
      ><a name="651" href="PropertiesEx.html#625" class="Bound"
      >n</a
      ><a name="652"
      > </a
      ><a name="653" href="PropertiesEx.html#627" class="Bound"
      >p</a
      ><a name="654"
      > </a
      ><a name="655" class="Symbol"
      >|</a
      ><a name="656"
      > </a
      ><a name="657" href="Properties.html#7291" class="Function"
      >+-assoc</a
      ><a name="664"
      > </a
      ><a name="665" href="PropertiesEx.html#627" class="Bound"
      >p</a
      ><a name="666"
      > </a
      ><a name="667" class="Symbol"
      >(</a
      ><a name="668" href="PropertiesEx.html#622" class="Bound"
      >m</a
      ><a name="669"
      > </a
      ><a name="670" href="Naturals.html#12016" class="Primitive Operator"
      >*</a
      ><a name="671"
      > </a
      ><a name="672" href="PropertiesEx.html#627" class="Bound"
      >p</a
      ><a name="673" class="Symbol"
      >)</a
      ><a name="674"
      > </a
      ><a name="675" class="Symbol"
      >(</a
      ><a name="676" href="PropertiesEx.html#625" class="Bound"
      >n</a
      ><a name="677"
      > </a
      ><a name="678" href="Naturals.html#12016" class="Primitive Operator"
      >*</a
      ><a name="679"
      > </a
      ><a name="680" href="PropertiesEx.html#627" class="Bound"
      >p</a
      ><a name="681" class="Symbol"
      >)</a
      ><a name="682"
      > </a
      ><a name="683" class="Symbol"
      >=</a
      ><a name="684"
      > </a
      ><a name="685" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      >
{% endraw %}</pre>

*Multiplication is associative*

<pre class="Agda">{% raw %}
<a name="748" href="PropertiesEx.html#748" class="Function"
      >*-assoc</a
      ><a name="755"
      > </a
      ><a name="756" class="Symbol"
      >:</a
      ><a name="757"
      > </a
      ><a name="758" class="Symbol"
      >&#8704;</a
      ><a name="759"
      > </a
      ><a name="760" class="Symbol"
      >(</a
      ><a name="761" href="PropertiesEx.html#761" class="Bound"
      >m</a
      ><a name="762"
      > </a
      ><a name="763" href="PropertiesEx.html#763" class="Bound"
      >n</a
      ><a name="764"
      > </a
      ><a name="765" href="PropertiesEx.html#765" class="Bound"
      >p</a
      ><a name="766"
      > </a
      ><a name="767" class="Symbol"
      >:</a
      ><a name="768"
      > </a
      ><a name="769" href="Naturals.html#1064" class="Datatype"
      >&#8469;</a
      ><a name="770" class="Symbol"
      >)</a
      ><a name="771"
      > </a
      ><a name="772" class="Symbol"
      >&#8594;</a
      ><a name="773"
      > </a
      ><a name="774" class="Symbol"
      >(</a
      ><a name="775" href="PropertiesEx.html#761" class="Bound"
      >m</a
      ><a name="776"
      > </a
      ><a name="777" href="Naturals.html#12016" class="Primitive Operator"
      >*</a
      ><a name="778"
      > </a
      ><a name="779" href="PropertiesEx.html#763" class="Bound"
      >n</a
      ><a name="780" class="Symbol"
      >)</a
      ><a name="781"
      > </a
      ><a name="782" href="Naturals.html#12016" class="Primitive Operator"
      >*</a
      ><a name="783"
      > </a
      ><a name="784" href="PropertiesEx.html#765" class="Bound"
      >p</a
      ><a name="785"
      > </a
      ><a name="786" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="787"
      > </a
      ><a name="788" href="PropertiesEx.html#761" class="Bound"
      >m</a
      ><a name="789"
      > </a
      ><a name="790" href="Naturals.html#12016" class="Primitive Operator"
      >*</a
      ><a name="791"
      > </a
      ><a name="792" class="Symbol"
      >(</a
      ><a name="793" href="PropertiesEx.html#763" class="Bound"
      >n</a
      ><a name="794"
      > </a
      ><a name="795" href="Naturals.html#12016" class="Primitive Operator"
      >*</a
      ><a name="796"
      > </a
      ><a name="797" href="PropertiesEx.html#765" class="Bound"
      >p</a
      ><a name="798" class="Symbol"
      >)</a
      ><a name="799"
      >
</a
      ><a name="800" href="PropertiesEx.html#748" class="Function"
      >*-assoc</a
      ><a name="807"
      > </a
      ><a name="808" href="Naturals.html#1080" class="InductiveConstructor"
      >zero</a
      ><a name="812"
      > </a
      ><a name="813" href="PropertiesEx.html#813" class="Bound"
      >n</a
      ><a name="814"
      > </a
      ><a name="815" href="PropertiesEx.html#815" class="Bound"
      >p</a
      ><a name="816"
      > </a
      ><a name="817" class="Symbol"
      >=</a
      ><a name="818"
      > </a
      ><a name="819" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="823"
      >
</a
      ><a name="824" href="PropertiesEx.html#748" class="Function"
      >*-assoc</a
      ><a name="831"
      > </a
      ><a name="832" class="Symbol"
      >(</a
      ><a name="833" href="Naturals.html#1091" class="InductiveConstructor"
      >suc</a
      ><a name="836"
      > </a
      ><a name="837" href="PropertiesEx.html#837" class="Bound"
      >m</a
      ><a name="838" class="Symbol"
      >)</a
      ><a name="839"
      > </a
      ><a name="840" href="PropertiesEx.html#840" class="Bound"
      >n</a
      ><a name="841"
      > </a
      ><a name="842" href="PropertiesEx.html#842" class="Bound"
      >p</a
      ><a name="843"
      > </a
      ><a name="844" class="Keyword"
      >rewrite</a
      ><a name="851"
      > </a
      ><a name="852" href="PropertiesEx.html#519" class="Function"
      >*-distrib-+</a
      ><a name="863"
      > </a
      ><a name="864" href="PropertiesEx.html#840" class="Bound"
      >n</a
      ><a name="865"
      > </a
      ><a name="866" class="Symbol"
      >(</a
      ><a name="867" href="PropertiesEx.html#837" class="Bound"
      >m</a
      ><a name="868"
      > </a
      ><a name="869" href="Naturals.html#12016" class="Primitive Operator"
      >*</a
      ><a name="870"
      > </a
      ><a name="871" href="PropertiesEx.html#840" class="Bound"
      >n</a
      ><a name="872" class="Symbol"
      >)</a
      ><a name="873"
      > </a
      ><a name="874" href="PropertiesEx.html#842" class="Bound"
      >p</a
      ><a name="875"
      > </a
      ><a name="876" class="Symbol"
      >|</a
      ><a name="877"
      > </a
      ><a name="878" href="PropertiesEx.html#748" class="Function"
      >*-assoc</a
      ><a name="885"
      > </a
      ><a name="886" href="PropertiesEx.html#837" class="Bound"
      >m</a
      ><a name="887"
      > </a
      ><a name="888" href="PropertiesEx.html#840" class="Bound"
      >n</a
      ><a name="889"
      > </a
      ><a name="890" href="PropertiesEx.html#842" class="Bound"
      >p</a
      ><a name="891"
      > </a
      ><a name="892" class="Symbol"
      >=</a
      ><a name="893"
      > </a
      ><a name="894" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      >
{% endraw %}</pre>

*Multiplications is commutative*

<pre class="Agda">{% raw %}
<a name="958" href="PropertiesEx.html#958" class="Function"
      >*-zero</a
      ><a name="964"
      > </a
      ><a name="965" class="Symbol"
      >:</a
      ><a name="966"
      > </a
      ><a name="967" class="Symbol"
      >&#8704;</a
      ><a name="968"
      > </a
      ><a name="969" class="Symbol"
      >(</a
      ><a name="970" href="PropertiesEx.html#970" class="Bound"
      >n</a
      ><a name="971"
      > </a
      ><a name="972" class="Symbol"
      >:</a
      ><a name="973"
      > </a
      ><a name="974" href="Naturals.html#1064" class="Datatype"
      >&#8469;</a
      ><a name="975" class="Symbol"
      >)</a
      ><a name="976"
      > </a
      ><a name="977" class="Symbol"
      >&#8594;</a
      ><a name="978"
      > </a
      ><a name="979" href="PropertiesEx.html#970" class="Bound"
      >n</a
      ><a name="980"
      > </a
      ><a name="981" href="Naturals.html#12016" class="Primitive Operator"
      >*</a
      ><a name="982"
      > </a
      ><a name="983" href="Naturals.html#1080" class="InductiveConstructor"
      >zero</a
      ><a name="987"
      > </a
      ><a name="988" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="989"
      > </a
      ><a name="990" href="Naturals.html#1080" class="InductiveConstructor"
      >zero</a
      ><a name="994"
      >
</a
      ><a name="995" href="PropertiesEx.html#958" class="Function"
      >*-zero</a
      ><a name="1001"
      > </a
      ><a name="1002" href="Naturals.html#1080" class="InductiveConstructor"
      >zero</a
      ><a name="1006"
      > </a
      ><a name="1007" class="Symbol"
      >=</a
      ><a name="1008"
      > </a
      ><a name="1009" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="1013"
      >
</a
      ><a name="1014" href="PropertiesEx.html#958" class="Function"
      >*-zero</a
      ><a name="1020"
      > </a
      ><a name="1021" class="Symbol"
      >(</a
      ><a name="1022" href="Naturals.html#1091" class="InductiveConstructor"
      >suc</a
      ><a name="1025"
      > </a
      ><a name="1026" href="PropertiesEx.html#1026" class="Bound"
      >n</a
      ><a name="1027" class="Symbol"
      >)</a
      ><a name="1028"
      > </a
      ><a name="1029" class="Keyword"
      >rewrite</a
      ><a name="1036"
      > </a
      ><a name="1037" href="PropertiesEx.html#958" class="Function"
      >*-zero</a
      ><a name="1043"
      > </a
      ><a name="1044" href="PropertiesEx.html#1026" class="Bound"
      >n</a
      ><a name="1045"
      > </a
      ><a name="1046" class="Symbol"
      >=</a
      ><a name="1047"
      > </a
      ><a name="1048" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="1052"
      >

</a
      ><a name="1054" href="PropertiesEx.html#1054" class="Function"
      >+-*-suc</a
      ><a name="1061"
      > </a
      ><a name="1062" class="Symbol"
      >:</a
      ><a name="1063"
      > </a
      ><a name="1064" class="Symbol"
      >&#8704;</a
      ><a name="1065"
      > </a
      ><a name="1066" class="Symbol"
      >(</a
      ><a name="1067" href="PropertiesEx.html#1067" class="Bound"
      >m</a
      ><a name="1068"
      > </a
      ><a name="1069" href="PropertiesEx.html#1069" class="Bound"
      >n</a
      ><a name="1070"
      > </a
      ><a name="1071" class="Symbol"
      >:</a
      ><a name="1072"
      > </a
      ><a name="1073" href="Naturals.html#1064" class="Datatype"
      >&#8469;</a
      ><a name="1074" class="Symbol"
      >)</a
      ><a name="1075"
      > </a
      ><a name="1076" class="Symbol"
      >&#8594;</a
      ><a name="1077"
      > </a
      ><a name="1078" href="PropertiesEx.html#1069" class="Bound"
      >n</a
      ><a name="1079"
      > </a
      ><a name="1080" href="Naturals.html#12016" class="Primitive Operator"
      >*</a
      ><a name="1081"
      > </a
      ><a name="1082" href="Naturals.html#1091" class="InductiveConstructor"
      >suc</a
      ><a name="1085"
      > </a
      ><a name="1086" href="PropertiesEx.html#1067" class="Bound"
      >m</a
      ><a name="1087"
      > </a
      ><a name="1088" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="1089"
      > </a
      ><a name="1090" href="PropertiesEx.html#1069" class="Bound"
      >n</a
      ><a name="1091"
      > </a
      ><a name="1092" href="Naturals.html#9439" class="Primitive Operator"
      >+</a
      ><a name="1093"
      > </a
      ><a name="1094" href="PropertiesEx.html#1069" class="Bound"
      >n</a
      ><a name="1095"
      > </a
      ><a name="1096" href="Naturals.html#12016" class="Primitive Operator"
      >*</a
      ><a name="1097"
      > </a
      ><a name="1098" href="PropertiesEx.html#1067" class="Bound"
      >m</a
      ><a name="1099"
      >
</a
      ><a name="1100" href="PropertiesEx.html#1054" class="Function"
      >+-*-suc</a
      ><a name="1107"
      > </a
      ><a name="1108" href="PropertiesEx.html#1108" class="Bound"
      >m</a
      ><a name="1109"
      > </a
      ><a name="1110" href="Naturals.html#1080" class="InductiveConstructor"
      >zero</a
      ><a name="1114"
      > </a
      ><a name="1115" class="Symbol"
      >=</a
      ><a name="1116"
      > </a
      ><a name="1117" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="1121"
      >
</a
      ><a name="1122" href="PropertiesEx.html#1054" class="Function"
      >+-*-suc</a
      ><a name="1129"
      > </a
      ><a name="1130" href="PropertiesEx.html#1130" class="Bound"
      >m</a
      ><a name="1131"
      > </a
      ><a name="1132" class="Symbol"
      >(</a
      ><a name="1133" href="Naturals.html#1091" class="InductiveConstructor"
      >suc</a
      ><a name="1136"
      > </a
      ><a name="1137" href="PropertiesEx.html#1137" class="Bound"
      >n</a
      ><a name="1138" class="Symbol"
      >)</a
      ><a name="1139"
      > </a
      ><a name="1140" class="Keyword"
      >rewrite</a
      ><a name="1147"
      > </a
      ><a name="1148" href="PropertiesEx.html#1054" class="Function"
      >+-*-suc</a
      ><a name="1155"
      > </a
      ><a name="1156" href="PropertiesEx.html#1130" class="Bound"
      >m</a
      ><a name="1157"
      > </a
      ><a name="1158" href="PropertiesEx.html#1137" class="Bound"
      >n</a
      ><a name="1159"
      > </a
      ><a name="1160" class="Symbol"
      >|</a
      ><a name="1161"
      > </a
      ><a name="1162" href="PropertiesEx.html#322" class="Function"
      >+-swap</a
      ><a name="1168"
      > </a
      ><a name="1169" href="PropertiesEx.html#1130" class="Bound"
      >m</a
      ><a name="1170"
      > </a
      ><a name="1171" href="PropertiesEx.html#1137" class="Bound"
      >n</a
      ><a name="1172"
      > </a
      ><a name="1173" class="Symbol"
      >(</a
      ><a name="1174" href="PropertiesEx.html#1137" class="Bound"
      >n</a
      ><a name="1175"
      > </a
      ><a name="1176" href="Naturals.html#12016" class="Primitive Operator"
      >*</a
      ><a name="1177"
      > </a
      ><a name="1178" href="PropertiesEx.html#1130" class="Bound"
      >m</a
      ><a name="1179" class="Symbol"
      >)</a
      ><a name="1180"
      > </a
      ><a name="1181" class="Symbol"
      >=</a
      ><a name="1182"
      > </a
      ><a name="1183" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="1187"
      >

</a
      ><a name="1189" href="PropertiesEx.html#1189" class="Function"
      >*-comm</a
      ><a name="1195"
      > </a
      ><a name="1196" class="Symbol"
      >:</a
      ><a name="1197"
      > </a
      ><a name="1198" class="Symbol"
      >&#8704;</a
      ><a name="1199"
      > </a
      ><a name="1200" class="Symbol"
      >(</a
      ><a name="1201" href="PropertiesEx.html#1201" class="Bound"
      >m</a
      ><a name="1202"
      > </a
      ><a name="1203" href="PropertiesEx.html#1203" class="Bound"
      >n</a
      ><a name="1204"
      > </a
      ><a name="1205" class="Symbol"
      >:</a
      ><a name="1206"
      > </a
      ><a name="1207" href="Naturals.html#1064" class="Datatype"
      >&#8469;</a
      ><a name="1208" class="Symbol"
      >)</a
      ><a name="1209"
      > </a
      ><a name="1210" class="Symbol"
      >&#8594;</a
      ><a name="1211"
      > </a
      ><a name="1212" href="PropertiesEx.html#1201" class="Bound"
      >m</a
      ><a name="1213"
      > </a
      ><a name="1214" href="Naturals.html#12016" class="Primitive Operator"
      >*</a
      ><a name="1215"
      > </a
      ><a name="1216" href="PropertiesEx.html#1203" class="Bound"
      >n</a
      ><a name="1217"
      > </a
      ><a name="1218" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="1219"
      > </a
      ><a name="1220" href="PropertiesEx.html#1203" class="Bound"
      >n</a
      ><a name="1221"
      > </a
      ><a name="1222" href="Naturals.html#12016" class="Primitive Operator"
      >*</a
      ><a name="1223"
      > </a
      ><a name="1224" href="PropertiesEx.html#1201" class="Bound"
      >m</a
      ><a name="1225"
      >
</a
      ><a name="1226" href="PropertiesEx.html#1189" class="Function"
      >*-comm</a
      ><a name="1232"
      > </a
      ><a name="1233" href="Naturals.html#1080" class="InductiveConstructor"
      >zero</a
      ><a name="1237"
      > </a
      ><a name="1238" href="PropertiesEx.html#1238" class="Bound"
      >n</a
      ><a name="1239"
      > </a
      ><a name="1240" class="Keyword"
      >rewrite</a
      ><a name="1247"
      > </a
      ><a name="1248" href="PropertiesEx.html#958" class="Function"
      >*-zero</a
      ><a name="1254"
      > </a
      ><a name="1255" href="PropertiesEx.html#1238" class="Bound"
      >n</a
      ><a name="1256"
      > </a
      ><a name="1257" class="Symbol"
      >=</a
      ><a name="1258"
      > </a
      ><a name="1259" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="1263"
      >
</a
      ><a name="1264" href="PropertiesEx.html#1189" class="Function"
      >*-comm</a
      ><a name="1270"
      > </a
      ><a name="1271" class="Symbol"
      >(</a
      ><a name="1272" href="Naturals.html#1091" class="InductiveConstructor"
      >suc</a
      ><a name="1275"
      > </a
      ><a name="1276" href="PropertiesEx.html#1276" class="Bound"
      >m</a
      ><a name="1277" class="Symbol"
      >)</a
      ><a name="1278"
      > </a
      ><a name="1279" href="PropertiesEx.html#1279" class="Bound"
      >n</a
      ><a name="1280"
      > </a
      ><a name="1281" class="Keyword"
      >rewrite</a
      ><a name="1288"
      > </a
      ><a name="1289" href="PropertiesEx.html#1054" class="Function"
      >+-*-suc</a
      ><a name="1296"
      > </a
      ><a name="1297" href="PropertiesEx.html#1276" class="Bound"
      >m</a
      ><a name="1298"
      > </a
      ><a name="1299" href="PropertiesEx.html#1279" class="Bound"
      >n</a
      ><a name="1300"
      > </a
      ><a name="1301" class="Symbol"
      >|</a
      ><a name="1302"
      > </a
      ><a name="1303" href="PropertiesEx.html#1189" class="Function"
      >*-comm</a
      ><a name="1309"
      > </a
      ><a name="1310" href="PropertiesEx.html#1276" class="Bound"
      >m</a
      ><a name="1311"
      > </a
      ><a name="1312" href="PropertiesEx.html#1279" class="Bound"
      >n</a
      ><a name="1313"
      > </a
      ><a name="1314" class="Symbol"
      >=</a
      ><a name="1315"
      > </a
      ><a name="1316" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      >
{% endraw %}</pre>

*Monus from zero*

<pre class="Agda">{% raw %}
<a name="1365" href="PropertiesEx.html#1365" class="Function"
      >0&#8760;n&#8801;0</a
      ><a name="1370"
      > </a
      ><a name="1371" class="Symbol"
      >:</a
      ><a name="1372"
      > </a
      ><a name="1373" class="Symbol"
      >&#8704;</a
      ><a name="1374"
      > </a
      ><a name="1375" class="Symbol"
      >(</a
      ><a name="1376" href="PropertiesEx.html#1376" class="Bound"
      >n</a
      ><a name="1377"
      > </a
      ><a name="1378" class="Symbol"
      >:</a
      ><a name="1379"
      > </a
      ><a name="1380" href="Naturals.html#1064" class="Datatype"
      >&#8469;</a
      ><a name="1381" class="Symbol"
      >)</a
      ><a name="1382"
      > </a
      ><a name="1383" class="Symbol"
      >&#8594;</a
      ><a name="1384"
      > </a
      ><a name="1385" href="Naturals.html#1080" class="InductiveConstructor"
      >zero</a
      ><a name="1389"
      > </a
      ><a name="1390" href="Naturals.html#13851" class="Primitive Operator"
      >&#8760;</a
      ><a name="1391"
      > </a
      ><a name="1392" href="PropertiesEx.html#1376" class="Bound"
      >n</a
      ><a name="1393"
      > </a
      ><a name="1394" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="1395"
      > </a
      ><a name="1396" href="Naturals.html#1080" class="InductiveConstructor"
      >zero</a
      ><a name="1400"
      >
</a
      ><a name="1401" href="PropertiesEx.html#1365" class="Function"
      >0&#8760;n&#8801;0</a
      ><a name="1406"
      > </a
      ><a name="1407" href="Naturals.html#1080" class="InductiveConstructor"
      >zero</a
      ><a name="1411"
      > </a
      ><a name="1412" class="Symbol"
      >=</a
      ><a name="1413"
      > </a
      ><a name="1414" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="1418"
      >
</a
      ><a name="1419" href="PropertiesEx.html#1365" class="Function"
      >0&#8760;n&#8801;0</a
      ><a name="1424"
      > </a
      ><a name="1425" class="Symbol"
      >(</a
      ><a name="1426" href="Naturals.html#1091" class="InductiveConstructor"
      >suc</a
      ><a name="1429"
      > </a
      ><a name="1430" href="PropertiesEx.html#1430" class="Bound"
      >n</a
      ><a name="1431" class="Symbol"
      >)</a
      ><a name="1432"
      > </a
      ><a name="1433" class="Symbol"
      >=</a
      ><a name="1434"
      > </a
      ><a name="1435" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      >
{% endraw %}</pre>

The proof does not require induction.

*Associativity of monus with addition*

<pre class="Agda">{% raw %}
<a name="1544" href="PropertiesEx.html#1544" class="Function"
      >&#8760;-+-assoc</a
      ><a name="1553"
      > </a
      ><a name="1554" class="Symbol"
      >:</a
      ><a name="1555"
      > </a
      ><a name="1556" class="Symbol"
      >&#8704;</a
      ><a name="1557"
      > </a
      ><a name="1558" class="Symbol"
      >(</a
      ><a name="1559" href="PropertiesEx.html#1559" class="Bound"
      >m</a
      ><a name="1560"
      > </a
      ><a name="1561" href="PropertiesEx.html#1561" class="Bound"
      >n</a
      ><a name="1562"
      > </a
      ><a name="1563" href="PropertiesEx.html#1563" class="Bound"
      >p</a
      ><a name="1564"
      > </a
      ><a name="1565" class="Symbol"
      >:</a
      ><a name="1566"
      > </a
      ><a name="1567" href="Naturals.html#1064" class="Datatype"
      >&#8469;</a
      ><a name="1568" class="Symbol"
      >)</a
      ><a name="1569"
      > </a
      ><a name="1570" class="Symbol"
      >&#8594;</a
      ><a name="1571"
      > </a
      ><a name="1572" class="Symbol"
      >(</a
      ><a name="1573" href="PropertiesEx.html#1559" class="Bound"
      >m</a
      ><a name="1574"
      > </a
      ><a name="1575" href="Naturals.html#13851" class="Primitive Operator"
      >&#8760;</a
      ><a name="1576"
      > </a
      ><a name="1577" href="PropertiesEx.html#1561" class="Bound"
      >n</a
      ><a name="1578" class="Symbol"
      >)</a
      ><a name="1579"
      > </a
      ><a name="1580" href="Naturals.html#13851" class="Primitive Operator"
      >&#8760;</a
      ><a name="1581"
      > </a
      ><a name="1582" href="PropertiesEx.html#1563" class="Bound"
      >p</a
      ><a name="1583"
      > </a
      ><a name="1584" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="1585"
      > </a
      ><a name="1586" href="PropertiesEx.html#1559" class="Bound"
      >m</a
      ><a name="1587"
      > </a
      ><a name="1588" href="Naturals.html#13851" class="Primitive Operator"
      >&#8760;</a
      ><a name="1589"
      > </a
      ><a name="1590" class="Symbol"
      >(</a
      ><a name="1591" href="PropertiesEx.html#1561" class="Bound"
      >n</a
      ><a name="1592"
      > </a
      ><a name="1593" href="Naturals.html#9439" class="Primitive Operator"
      >+</a
      ><a name="1594"
      > </a
      ><a name="1595" href="PropertiesEx.html#1563" class="Bound"
      >p</a
      ><a name="1596" class="Symbol"
      >)</a
      ><a name="1597"
      >
</a
      ><a name="1598" href="PropertiesEx.html#1544" class="Function"
      >&#8760;-+-assoc</a
      ><a name="1607"
      > </a
      ><a name="1608" href="PropertiesEx.html#1608" class="Bound"
      >m</a
      ><a name="1609"
      > </a
      ><a name="1610" href="Naturals.html#1080" class="InductiveConstructor"
      >zero</a
      ><a name="1614"
      > </a
      ><a name="1615" href="PropertiesEx.html#1615" class="Bound"
      >p</a
      ><a name="1616"
      > </a
      ><a name="1617" class="Symbol"
      >=</a
      ><a name="1618"
      > </a
      ><a name="1619" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="1623"
      >
</a
      ><a name="1624" href="PropertiesEx.html#1544" class="Function"
      >&#8760;-+-assoc</a
      ><a name="1633"
      > </a
      ><a name="1634" href="Naturals.html#1080" class="InductiveConstructor"
      >zero</a
      ><a name="1638"
      > </a
      ><a name="1639" class="Symbol"
      >(</a
      ><a name="1640" href="Naturals.html#1091" class="InductiveConstructor"
      >suc</a
      ><a name="1643"
      > </a
      ><a name="1644" href="PropertiesEx.html#1644" class="Bound"
      >n</a
      ><a name="1645" class="Symbol"
      >)</a
      ><a name="1646"
      > </a
      ><a name="1647" href="PropertiesEx.html#1647" class="Bound"
      >p</a
      ><a name="1648"
      > </a
      ><a name="1649" class="Keyword"
      >rewrite</a
      ><a name="1656"
      > </a
      ><a name="1657" href="PropertiesEx.html#1365" class="Function"
      >0&#8760;n&#8801;0</a
      ><a name="1662"
      > </a
      ><a name="1663" href="PropertiesEx.html#1647" class="Bound"
      >p</a
      ><a name="1664"
      > </a
      ><a name="1665" class="Symbol"
      >=</a
      ><a name="1666"
      > </a
      ><a name="1667" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="1671"
      >
</a
      ><a name="1672" href="PropertiesEx.html#1544" class="Function"
      >&#8760;-+-assoc</a
      ><a name="1681"
      > </a
      ><a name="1682" class="Symbol"
      >(</a
      ><a name="1683" href="Naturals.html#1091" class="InductiveConstructor"
      >suc</a
      ><a name="1686"
      > </a
      ><a name="1687" href="PropertiesEx.html#1687" class="Bound"
      >m</a
      ><a name="1688" class="Symbol"
      >)</a
      ><a name="1689"
      > </a
      ><a name="1690" class="Symbol"
      >(</a
      ><a name="1691" href="Naturals.html#1091" class="InductiveConstructor"
      >suc</a
      ><a name="1694"
      > </a
      ><a name="1695" href="PropertiesEx.html#1695" class="Bound"
      >n</a
      ><a name="1696" class="Symbol"
      >)</a
      ><a name="1697"
      > </a
      ><a name="1698" href="PropertiesEx.html#1698" class="Bound"
      >p</a
      ><a name="1699"
      > </a
      ><a name="1700" class="Keyword"
      >rewrite</a
      ><a name="1707"
      > </a
      ><a name="1708" href="PropertiesEx.html#1544" class="Function"
      >&#8760;-+-assoc</a
      ><a name="1717"
      > </a
      ><a name="1718" href="PropertiesEx.html#1687" class="Bound"
      >m</a
      ><a name="1719"
      > </a
      ><a name="1720" href="PropertiesEx.html#1695" class="Bound"
      >n</a
      ><a name="1721"
      > </a
      ><a name="1722" href="PropertiesEx.html#1698" class="Bound"
      >p</a
      ><a name="1723"
      > </a
      ><a name="1724" class="Symbol"
      >=</a
      ><a name="1725"
      > </a
      ><a name="1726" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      >
{% endraw %}</pre>


