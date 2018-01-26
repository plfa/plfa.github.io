---
title     : "Properties Answers"
layout    : page
permalink : /PropertiesAns
---

<pre class="Agda">{% raw %}
<a name="100" class="Keyword"
      >open</a
      ><a name="104"
      > </a
      ><a name="105" class="Keyword"
      >import</a
      ><a name="111"
      > </a
      ><a name="112" class="Module"
      >Naturals</a
      ><a name="120"
      > </a
      ><a name="121" class="Keyword"
      >using</a
      ><a name="126"
      > </a
      ><a name="127" class="Symbol"
      >(</a
      ><a name="128" href="Naturals.html#1064" class="Datatype"
      >&#8469;</a
      ><a name="129" class="Symbol"
      >;</a
      ><a name="130"
      > </a
      ><a name="131" href="Naturals.html#1091" class="InductiveConstructor"
      >suc</a
      ><a name="134" class="Symbol"
      >;</a
      ><a name="135"
      > </a
      ><a name="136" href="Naturals.html#1080" class="InductiveConstructor"
      >zero</a
      ><a name="140" class="Symbol"
      >;</a
      ><a name="141"
      > </a
      ><a name="142" href="Naturals.html#9439" class="Primitive Operator"
      >_+_</a
      ><a name="145" class="Symbol"
      >;</a
      ><a name="146"
      > </a
      ><a name="147" href="Naturals.html#12016" class="Primitive Operator"
      >_*_</a
      ><a name="150" class="Symbol"
      >;</a
      ><a name="151"
      > </a
      ><a name="152" href="Naturals.html#13851" class="Primitive Operator"
      >_&#8760;_</a
      ><a name="155" class="Symbol"
      >)</a
      ><a name="156"
      >
</a
      ><a name="157" class="Keyword"
      >open</a
      ><a name="161"
      > </a
      ><a name="162" class="Keyword"
      >import</a
      ><a name="168"
      > </a
      ><a name="169" class="Module"
      >Properties</a
      ><a name="179"
      > </a
      ><a name="180" class="Keyword"
      >using</a
      ><a name="185"
      > </a
      ><a name="186" class="Symbol"
      >(</a
      ><a name="187" href="Properties.html#7291" class="Function"
      >+-assoc</a
      ><a name="194" class="Symbol"
      >;</a
      ><a name="195"
      > </a
      ><a name="196" href="Properties.html#17070" class="Function"
      >+-comm</a
      ><a name="202" class="Symbol"
      >)</a
      ><a name="203"
      >
</a
      ><a name="204" class="Keyword"
      >open</a
      ><a name="208"
      > </a
      ><a name="209" class="Keyword"
      >import</a
      ><a name="215"
      > </a
      ><a name="216" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#1" class="Module"
      >Relation.Binary.PropositionalEquality</a
      ><a name="253"
      > </a
      ><a name="254" class="Keyword"
      >using</a
      ><a name="259"
      > </a
      ><a name="260" class="Symbol"
      >(</a
      ><a name="261" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >_&#8801;_</a
      ><a name="264" class="Symbol"
      >;</a
      ><a name="265"
      > </a
      ><a name="266" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="270" class="Symbol"
      >;</a
      ><a name="271"
      > </a
      ><a name="272" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.Core.html#565" class="Function"
      >sym</a
      ><a name="275" class="Symbol"
      >)</a
      >
{% endraw %}</pre>

*Swapping terms*

<pre class="Agda">{% raw %}
<a name="321" href="PropertiesAns.html#321" class="Function"
      >+-swap</a
      ><a name="327"
      > </a
      ><a name="328" class="Symbol"
      >:</a
      ><a name="329"
      > </a
      ><a name="330" class="Symbol"
      >&#8704;</a
      ><a name="331"
      > </a
      ><a name="332" class="Symbol"
      >(</a
      ><a name="333" href="PropertiesAns.html#333" class="Bound"
      >m</a
      ><a name="334"
      > </a
      ><a name="335" href="PropertiesAns.html#335" class="Bound"
      >n</a
      ><a name="336"
      > </a
      ><a name="337" href="PropertiesAns.html#337" class="Bound"
      >p</a
      ><a name="338"
      > </a
      ><a name="339" class="Symbol"
      >:</a
      ><a name="340"
      > </a
      ><a name="341" href="Naturals.html#1064" class="Datatype"
      >&#8469;</a
      ><a name="342" class="Symbol"
      >)</a
      ><a name="343"
      > </a
      ><a name="344" class="Symbol"
      >&#8594;</a
      ><a name="345"
      > </a
      ><a name="346" href="PropertiesAns.html#333" class="Bound"
      >m</a
      ><a name="347"
      > </a
      ><a name="348" href="Naturals.html#9439" class="Primitive Operator"
      >+</a
      ><a name="349"
      > </a
      ><a name="350" class="Symbol"
      >(</a
      ><a name="351" href="PropertiesAns.html#335" class="Bound"
      >n</a
      ><a name="352"
      > </a
      ><a name="353" href="Naturals.html#9439" class="Primitive Operator"
      >+</a
      ><a name="354"
      > </a
      ><a name="355" href="PropertiesAns.html#337" class="Bound"
      >p</a
      ><a name="356" class="Symbol"
      >)</a
      ><a name="357"
      > </a
      ><a name="358" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="359"
      > </a
      ><a name="360" href="PropertiesAns.html#335" class="Bound"
      >n</a
      ><a name="361"
      > </a
      ><a name="362" href="Naturals.html#9439" class="Primitive Operator"
      >+</a
      ><a name="363"
      > </a
      ><a name="364" class="Symbol"
      >(</a
      ><a name="365" href="PropertiesAns.html#333" class="Bound"
      >m</a
      ><a name="366"
      > </a
      ><a name="367" href="Naturals.html#9439" class="Primitive Operator"
      >+</a
      ><a name="368"
      > </a
      ><a name="369" href="PropertiesAns.html#337" class="Bound"
      >p</a
      ><a name="370" class="Symbol"
      >)</a
      ><a name="371"
      >
</a
      ><a name="372" href="PropertiesAns.html#321" class="Function"
      >+-swap</a
      ><a name="378"
      > </a
      ><a name="379" href="PropertiesAns.html#379" class="Bound"
      >m</a
      ><a name="380"
      > </a
      ><a name="381" href="PropertiesAns.html#381" class="Bound"
      >n</a
      ><a name="382"
      > </a
      ><a name="383" href="PropertiesAns.html#383" class="Bound"
      >p</a
      ><a name="384"
      > </a
      ><a name="385" class="Keyword"
      >rewrite</a
      ><a name="392"
      > </a
      ><a name="393" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.Core.html#565" class="Function"
      >sym</a
      ><a name="396"
      > </a
      ><a name="397" class="Symbol"
      >(</a
      ><a name="398" href="Properties.html#7291" class="Function"
      >+-assoc</a
      ><a name="405"
      > </a
      ><a name="406" href="PropertiesAns.html#379" class="Bound"
      >m</a
      ><a name="407"
      > </a
      ><a name="408" href="PropertiesAns.html#381" class="Bound"
      >n</a
      ><a name="409"
      > </a
      ><a name="410" href="PropertiesAns.html#383" class="Bound"
      >p</a
      ><a name="411" class="Symbol"
      >)</a
      ><a name="412"
      > </a
      ><a name="413" class="Symbol"
      >|</a
      ><a name="414"
      > </a
      ><a name="415" href="Properties.html#17070" class="Function"
      >+-comm</a
      ><a name="421"
      > </a
      ><a name="422" href="PropertiesAns.html#379" class="Bound"
      >m</a
      ><a name="423"
      > </a
      ><a name="424" href="PropertiesAns.html#381" class="Bound"
      >n</a
      ><a name="425"
      > </a
      ><a name="426" class="Symbol"
      >|</a
      ><a name="427"
      > </a
      ><a name="428" href="Properties.html#7291" class="Function"
      >+-assoc</a
      ><a name="435"
      > </a
      ><a name="436" href="PropertiesAns.html#381" class="Bound"
      >n</a
      ><a name="437"
      > </a
      ><a name="438" href="PropertiesAns.html#379" class="Bound"
      >m</a
      ><a name="439"
      > </a
      ><a name="440" href="PropertiesAns.html#383" class="Bound"
      >p</a
      ><a name="441"
      > </a
      ><a name="442" class="Symbol"
      >=</a
      ><a name="443"
      > </a
      ><a name="444" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      >
{% endraw %}</pre>

*Multiplication distributes over addition*

<pre class="Agda">{% raw %}
<a name="518" href="PropertiesAns.html#518" class="Function"
      >*-distrib-+</a
      ><a name="529"
      > </a
      ><a name="530" class="Symbol"
      >:</a
      ><a name="531"
      > </a
      ><a name="532" class="Symbol"
      >&#8704;</a
      ><a name="533"
      > </a
      ><a name="534" class="Symbol"
      >(</a
      ><a name="535" href="PropertiesAns.html#535" class="Bound"
      >m</a
      ><a name="536"
      > </a
      ><a name="537" href="PropertiesAns.html#537" class="Bound"
      >n</a
      ><a name="538"
      > </a
      ><a name="539" href="PropertiesAns.html#539" class="Bound"
      >p</a
      ><a name="540"
      > </a
      ><a name="541" class="Symbol"
      >:</a
      ><a name="542"
      > </a
      ><a name="543" href="Naturals.html#1064" class="Datatype"
      >&#8469;</a
      ><a name="544" class="Symbol"
      >)</a
      ><a name="545"
      > </a
      ><a name="546" class="Symbol"
      >&#8594;</a
      ><a name="547"
      > </a
      ><a name="548" class="Symbol"
      >(</a
      ><a name="549" href="PropertiesAns.html#535" class="Bound"
      >m</a
      ><a name="550"
      > </a
      ><a name="551" href="Naturals.html#9439" class="Primitive Operator"
      >+</a
      ><a name="552"
      > </a
      ><a name="553" href="PropertiesAns.html#537" class="Bound"
      >n</a
      ><a name="554" class="Symbol"
      >)</a
      ><a name="555"
      > </a
      ><a name="556" href="Naturals.html#12016" class="Primitive Operator"
      >*</a
      ><a name="557"
      > </a
      ><a name="558" href="PropertiesAns.html#539" class="Bound"
      >p</a
      ><a name="559"
      > </a
      ><a name="560" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="561"
      > </a
      ><a name="562" href="PropertiesAns.html#535" class="Bound"
      >m</a
      ><a name="563"
      > </a
      ><a name="564" href="Naturals.html#12016" class="Primitive Operator"
      >*</a
      ><a name="565"
      > </a
      ><a name="566" href="PropertiesAns.html#539" class="Bound"
      >p</a
      ><a name="567"
      > </a
      ><a name="568" href="Naturals.html#9439" class="Primitive Operator"
      >+</a
      ><a name="569"
      > </a
      ><a name="570" href="PropertiesAns.html#537" class="Bound"
      >n</a
      ><a name="571"
      > </a
      ><a name="572" href="Naturals.html#12016" class="Primitive Operator"
      >*</a
      ><a name="573"
      > </a
      ><a name="574" href="PropertiesAns.html#539" class="Bound"
      >p</a
      ><a name="575"
      >
</a
      ><a name="576" href="PropertiesAns.html#518" class="Function"
      >*-distrib-+</a
      ><a name="587"
      > </a
      ><a name="588" href="Naturals.html#1080" class="InductiveConstructor"
      >zero</a
      ><a name="592"
      > </a
      ><a name="593" href="PropertiesAns.html#593" class="Bound"
      >n</a
      ><a name="594"
      > </a
      ><a name="595" href="PropertiesAns.html#595" class="Bound"
      >p</a
      ><a name="596"
      > </a
      ><a name="597" class="Symbol"
      >=</a
      ><a name="598"
      > </a
      ><a name="599" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="603"
      >
</a
      ><a name="604" href="PropertiesAns.html#518" class="Function"
      >*-distrib-+</a
      ><a name="615"
      > </a
      ><a name="616" class="Symbol"
      >(</a
      ><a name="617" href="Naturals.html#1091" class="InductiveConstructor"
      >suc</a
      ><a name="620"
      > </a
      ><a name="621" href="PropertiesAns.html#621" class="Bound"
      >m</a
      ><a name="622" class="Symbol"
      >)</a
      ><a name="623"
      > </a
      ><a name="624" href="PropertiesAns.html#624" class="Bound"
      >n</a
      ><a name="625"
      > </a
      ><a name="626" href="PropertiesAns.html#626" class="Bound"
      >p</a
      ><a name="627"
      > </a
      ><a name="628" class="Keyword"
      >rewrite</a
      ><a name="635"
      > </a
      ><a name="636" href="PropertiesAns.html#518" class="Function"
      >*-distrib-+</a
      ><a name="647"
      > </a
      ><a name="648" href="PropertiesAns.html#621" class="Bound"
      >m</a
      ><a name="649"
      > </a
      ><a name="650" href="PropertiesAns.html#624" class="Bound"
      >n</a
      ><a name="651"
      > </a
      ><a name="652" href="PropertiesAns.html#626" class="Bound"
      >p</a
      ><a name="653"
      > </a
      ><a name="654" class="Symbol"
      >|</a
      ><a name="655"
      > </a
      ><a name="656" href="Properties.html#7291" class="Function"
      >+-assoc</a
      ><a name="663"
      > </a
      ><a name="664" href="PropertiesAns.html#626" class="Bound"
      >p</a
      ><a name="665"
      > </a
      ><a name="666" class="Symbol"
      >(</a
      ><a name="667" href="PropertiesAns.html#621" class="Bound"
      >m</a
      ><a name="668"
      > </a
      ><a name="669" href="Naturals.html#12016" class="Primitive Operator"
      >*</a
      ><a name="670"
      > </a
      ><a name="671" href="PropertiesAns.html#626" class="Bound"
      >p</a
      ><a name="672" class="Symbol"
      >)</a
      ><a name="673"
      > </a
      ><a name="674" class="Symbol"
      >(</a
      ><a name="675" href="PropertiesAns.html#624" class="Bound"
      >n</a
      ><a name="676"
      > </a
      ><a name="677" href="Naturals.html#12016" class="Primitive Operator"
      >*</a
      ><a name="678"
      > </a
      ><a name="679" href="PropertiesAns.html#626" class="Bound"
      >p</a
      ><a name="680" class="Symbol"
      >)</a
      ><a name="681"
      > </a
      ><a name="682" class="Symbol"
      >=</a
      ><a name="683"
      > </a
      ><a name="684" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      >
{% endraw %}</pre>

*Multiplication is associative*

<pre class="Agda">{% raw %}
<a name="747" href="PropertiesAns.html#747" class="Function"
      >*-assoc</a
      ><a name="754"
      > </a
      ><a name="755" class="Symbol"
      >:</a
      ><a name="756"
      > </a
      ><a name="757" class="Symbol"
      >&#8704;</a
      ><a name="758"
      > </a
      ><a name="759" class="Symbol"
      >(</a
      ><a name="760" href="PropertiesAns.html#760" class="Bound"
      >m</a
      ><a name="761"
      > </a
      ><a name="762" href="PropertiesAns.html#762" class="Bound"
      >n</a
      ><a name="763"
      > </a
      ><a name="764" href="PropertiesAns.html#764" class="Bound"
      >p</a
      ><a name="765"
      > </a
      ><a name="766" class="Symbol"
      >:</a
      ><a name="767"
      > </a
      ><a name="768" href="Naturals.html#1064" class="Datatype"
      >&#8469;</a
      ><a name="769" class="Symbol"
      >)</a
      ><a name="770"
      > </a
      ><a name="771" class="Symbol"
      >&#8594;</a
      ><a name="772"
      > </a
      ><a name="773" class="Symbol"
      >(</a
      ><a name="774" href="PropertiesAns.html#760" class="Bound"
      >m</a
      ><a name="775"
      > </a
      ><a name="776" href="Naturals.html#12016" class="Primitive Operator"
      >*</a
      ><a name="777"
      > </a
      ><a name="778" href="PropertiesAns.html#762" class="Bound"
      >n</a
      ><a name="779" class="Symbol"
      >)</a
      ><a name="780"
      > </a
      ><a name="781" href="Naturals.html#12016" class="Primitive Operator"
      >*</a
      ><a name="782"
      > </a
      ><a name="783" href="PropertiesAns.html#764" class="Bound"
      >p</a
      ><a name="784"
      > </a
      ><a name="785" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="786"
      > </a
      ><a name="787" href="PropertiesAns.html#760" class="Bound"
      >m</a
      ><a name="788"
      > </a
      ><a name="789" href="Naturals.html#12016" class="Primitive Operator"
      >*</a
      ><a name="790"
      > </a
      ><a name="791" class="Symbol"
      >(</a
      ><a name="792" href="PropertiesAns.html#762" class="Bound"
      >n</a
      ><a name="793"
      > </a
      ><a name="794" href="Naturals.html#12016" class="Primitive Operator"
      >*</a
      ><a name="795"
      > </a
      ><a name="796" href="PropertiesAns.html#764" class="Bound"
      >p</a
      ><a name="797" class="Symbol"
      >)</a
      ><a name="798"
      >
</a
      ><a name="799" href="PropertiesAns.html#747" class="Function"
      >*-assoc</a
      ><a name="806"
      > </a
      ><a name="807" href="Naturals.html#1080" class="InductiveConstructor"
      >zero</a
      ><a name="811"
      > </a
      ><a name="812" href="PropertiesAns.html#812" class="Bound"
      >n</a
      ><a name="813"
      > </a
      ><a name="814" href="PropertiesAns.html#814" class="Bound"
      >p</a
      ><a name="815"
      > </a
      ><a name="816" class="Symbol"
      >=</a
      ><a name="817"
      > </a
      ><a name="818" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="822"
      >
</a
      ><a name="823" href="PropertiesAns.html#747" class="Function"
      >*-assoc</a
      ><a name="830"
      > </a
      ><a name="831" class="Symbol"
      >(</a
      ><a name="832" href="Naturals.html#1091" class="InductiveConstructor"
      >suc</a
      ><a name="835"
      > </a
      ><a name="836" href="PropertiesAns.html#836" class="Bound"
      >m</a
      ><a name="837" class="Symbol"
      >)</a
      ><a name="838"
      > </a
      ><a name="839" href="PropertiesAns.html#839" class="Bound"
      >n</a
      ><a name="840"
      > </a
      ><a name="841" href="PropertiesAns.html#841" class="Bound"
      >p</a
      ><a name="842"
      > </a
      ><a name="843" class="Keyword"
      >rewrite</a
      ><a name="850"
      > </a
      ><a name="851" href="PropertiesAns.html#518" class="Function"
      >*-distrib-+</a
      ><a name="862"
      > </a
      ><a name="863" href="PropertiesAns.html#839" class="Bound"
      >n</a
      ><a name="864"
      > </a
      ><a name="865" class="Symbol"
      >(</a
      ><a name="866" href="PropertiesAns.html#836" class="Bound"
      >m</a
      ><a name="867"
      > </a
      ><a name="868" href="Naturals.html#12016" class="Primitive Operator"
      >*</a
      ><a name="869"
      > </a
      ><a name="870" href="PropertiesAns.html#839" class="Bound"
      >n</a
      ><a name="871" class="Symbol"
      >)</a
      ><a name="872"
      > </a
      ><a name="873" href="PropertiesAns.html#841" class="Bound"
      >p</a
      ><a name="874"
      > </a
      ><a name="875" class="Symbol"
      >|</a
      ><a name="876"
      > </a
      ><a name="877" href="PropertiesAns.html#747" class="Function"
      >*-assoc</a
      ><a name="884"
      > </a
      ><a name="885" href="PropertiesAns.html#836" class="Bound"
      >m</a
      ><a name="886"
      > </a
      ><a name="887" href="PropertiesAns.html#839" class="Bound"
      >n</a
      ><a name="888"
      > </a
      ><a name="889" href="PropertiesAns.html#841" class="Bound"
      >p</a
      ><a name="890"
      > </a
      ><a name="891" class="Symbol"
      >=</a
      ><a name="892"
      > </a
      ><a name="893" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      >
{% endraw %}</pre>

*Multiplications is commutative*

<pre class="Agda">{% raw %}
<a name="957" href="PropertiesAns.html#957" class="Function"
      >*-zero</a
      ><a name="963"
      > </a
      ><a name="964" class="Symbol"
      >:</a
      ><a name="965"
      > </a
      ><a name="966" class="Symbol"
      >&#8704;</a
      ><a name="967"
      > </a
      ><a name="968" class="Symbol"
      >(</a
      ><a name="969" href="PropertiesAns.html#969" class="Bound"
      >n</a
      ><a name="970"
      > </a
      ><a name="971" class="Symbol"
      >:</a
      ><a name="972"
      > </a
      ><a name="973" href="Naturals.html#1064" class="Datatype"
      >&#8469;</a
      ><a name="974" class="Symbol"
      >)</a
      ><a name="975"
      > </a
      ><a name="976" class="Symbol"
      >&#8594;</a
      ><a name="977"
      > </a
      ><a name="978" href="PropertiesAns.html#969" class="Bound"
      >n</a
      ><a name="979"
      > </a
      ><a name="980" href="Naturals.html#12016" class="Primitive Operator"
      >*</a
      ><a name="981"
      > </a
      ><a name="982" href="Naturals.html#1080" class="InductiveConstructor"
      >zero</a
      ><a name="986"
      > </a
      ><a name="987" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="988"
      > </a
      ><a name="989" href="Naturals.html#1080" class="InductiveConstructor"
      >zero</a
      ><a name="993"
      >
</a
      ><a name="994" href="PropertiesAns.html#957" class="Function"
      >*-zero</a
      ><a name="1000"
      > </a
      ><a name="1001" href="Naturals.html#1080" class="InductiveConstructor"
      >zero</a
      ><a name="1005"
      > </a
      ><a name="1006" class="Symbol"
      >=</a
      ><a name="1007"
      > </a
      ><a name="1008" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="1012"
      >
</a
      ><a name="1013" href="PropertiesAns.html#957" class="Function"
      >*-zero</a
      ><a name="1019"
      > </a
      ><a name="1020" class="Symbol"
      >(</a
      ><a name="1021" href="Naturals.html#1091" class="InductiveConstructor"
      >suc</a
      ><a name="1024"
      > </a
      ><a name="1025" href="PropertiesAns.html#1025" class="Bound"
      >n</a
      ><a name="1026" class="Symbol"
      >)</a
      ><a name="1027"
      > </a
      ><a name="1028" class="Keyword"
      >rewrite</a
      ><a name="1035"
      > </a
      ><a name="1036" href="PropertiesAns.html#957" class="Function"
      >*-zero</a
      ><a name="1042"
      > </a
      ><a name="1043" href="PropertiesAns.html#1025" class="Bound"
      >n</a
      ><a name="1044"
      > </a
      ><a name="1045" class="Symbol"
      >=</a
      ><a name="1046"
      > </a
      ><a name="1047" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="1051"
      >

</a
      ><a name="1053" href="PropertiesAns.html#1053" class="Function"
      >+-*-suc</a
      ><a name="1060"
      > </a
      ><a name="1061" class="Symbol"
      >:</a
      ><a name="1062"
      > </a
      ><a name="1063" class="Symbol"
      >&#8704;</a
      ><a name="1064"
      > </a
      ><a name="1065" class="Symbol"
      >(</a
      ><a name="1066" href="PropertiesAns.html#1066" class="Bound"
      >m</a
      ><a name="1067"
      > </a
      ><a name="1068" href="PropertiesAns.html#1068" class="Bound"
      >n</a
      ><a name="1069"
      > </a
      ><a name="1070" class="Symbol"
      >:</a
      ><a name="1071"
      > </a
      ><a name="1072" href="Naturals.html#1064" class="Datatype"
      >&#8469;</a
      ><a name="1073" class="Symbol"
      >)</a
      ><a name="1074"
      > </a
      ><a name="1075" class="Symbol"
      >&#8594;</a
      ><a name="1076"
      > </a
      ><a name="1077" href="PropertiesAns.html#1068" class="Bound"
      >n</a
      ><a name="1078"
      > </a
      ><a name="1079" href="Naturals.html#12016" class="Primitive Operator"
      >*</a
      ><a name="1080"
      > </a
      ><a name="1081" href="Naturals.html#1091" class="InductiveConstructor"
      >suc</a
      ><a name="1084"
      > </a
      ><a name="1085" href="PropertiesAns.html#1066" class="Bound"
      >m</a
      ><a name="1086"
      > </a
      ><a name="1087" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="1088"
      > </a
      ><a name="1089" href="PropertiesAns.html#1068" class="Bound"
      >n</a
      ><a name="1090"
      > </a
      ><a name="1091" href="Naturals.html#9439" class="Primitive Operator"
      >+</a
      ><a name="1092"
      > </a
      ><a name="1093" href="PropertiesAns.html#1068" class="Bound"
      >n</a
      ><a name="1094"
      > </a
      ><a name="1095" href="Naturals.html#12016" class="Primitive Operator"
      >*</a
      ><a name="1096"
      > </a
      ><a name="1097" href="PropertiesAns.html#1066" class="Bound"
      >m</a
      ><a name="1098"
      >
</a
      ><a name="1099" href="PropertiesAns.html#1053" class="Function"
      >+-*-suc</a
      ><a name="1106"
      > </a
      ><a name="1107" href="PropertiesAns.html#1107" class="Bound"
      >m</a
      ><a name="1108"
      > </a
      ><a name="1109" href="Naturals.html#1080" class="InductiveConstructor"
      >zero</a
      ><a name="1113"
      > </a
      ><a name="1114" class="Symbol"
      >=</a
      ><a name="1115"
      > </a
      ><a name="1116" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="1120"
      >
</a
      ><a name="1121" href="PropertiesAns.html#1053" class="Function"
      >+-*-suc</a
      ><a name="1128"
      > </a
      ><a name="1129" href="PropertiesAns.html#1129" class="Bound"
      >m</a
      ><a name="1130"
      > </a
      ><a name="1131" class="Symbol"
      >(</a
      ><a name="1132" href="Naturals.html#1091" class="InductiveConstructor"
      >suc</a
      ><a name="1135"
      > </a
      ><a name="1136" href="PropertiesAns.html#1136" class="Bound"
      >n</a
      ><a name="1137" class="Symbol"
      >)</a
      ><a name="1138"
      > </a
      ><a name="1139" class="Keyword"
      >rewrite</a
      ><a name="1146"
      > </a
      ><a name="1147" href="PropertiesAns.html#1053" class="Function"
      >+-*-suc</a
      ><a name="1154"
      > </a
      ><a name="1155" href="PropertiesAns.html#1129" class="Bound"
      >m</a
      ><a name="1156"
      > </a
      ><a name="1157" href="PropertiesAns.html#1136" class="Bound"
      >n</a
      ><a name="1158"
      > </a
      ><a name="1159" class="Symbol"
      >|</a
      ><a name="1160"
      > </a
      ><a name="1161" href="PropertiesAns.html#321" class="Function"
      >+-swap</a
      ><a name="1167"
      > </a
      ><a name="1168" href="PropertiesAns.html#1129" class="Bound"
      >m</a
      ><a name="1169"
      > </a
      ><a name="1170" href="PropertiesAns.html#1136" class="Bound"
      >n</a
      ><a name="1171"
      > </a
      ><a name="1172" class="Symbol"
      >(</a
      ><a name="1173" href="PropertiesAns.html#1136" class="Bound"
      >n</a
      ><a name="1174"
      > </a
      ><a name="1175" href="Naturals.html#12016" class="Primitive Operator"
      >*</a
      ><a name="1176"
      > </a
      ><a name="1177" href="PropertiesAns.html#1129" class="Bound"
      >m</a
      ><a name="1178" class="Symbol"
      >)</a
      ><a name="1179"
      > </a
      ><a name="1180" class="Symbol"
      >=</a
      ><a name="1181"
      > </a
      ><a name="1182" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="1186"
      >

</a
      ><a name="1188" href="PropertiesAns.html#1188" class="Function"
      >*-comm</a
      ><a name="1194"
      > </a
      ><a name="1195" class="Symbol"
      >:</a
      ><a name="1196"
      > </a
      ><a name="1197" class="Symbol"
      >&#8704;</a
      ><a name="1198"
      > </a
      ><a name="1199" class="Symbol"
      >(</a
      ><a name="1200" href="PropertiesAns.html#1200" class="Bound"
      >m</a
      ><a name="1201"
      > </a
      ><a name="1202" href="PropertiesAns.html#1202" class="Bound"
      >n</a
      ><a name="1203"
      > </a
      ><a name="1204" class="Symbol"
      >:</a
      ><a name="1205"
      > </a
      ><a name="1206" href="Naturals.html#1064" class="Datatype"
      >&#8469;</a
      ><a name="1207" class="Symbol"
      >)</a
      ><a name="1208"
      > </a
      ><a name="1209" class="Symbol"
      >&#8594;</a
      ><a name="1210"
      > </a
      ><a name="1211" href="PropertiesAns.html#1200" class="Bound"
      >m</a
      ><a name="1212"
      > </a
      ><a name="1213" href="Naturals.html#12016" class="Primitive Operator"
      >*</a
      ><a name="1214"
      > </a
      ><a name="1215" href="PropertiesAns.html#1202" class="Bound"
      >n</a
      ><a name="1216"
      > </a
      ><a name="1217" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="1218"
      > </a
      ><a name="1219" href="PropertiesAns.html#1202" class="Bound"
      >n</a
      ><a name="1220"
      > </a
      ><a name="1221" href="Naturals.html#12016" class="Primitive Operator"
      >*</a
      ><a name="1222"
      > </a
      ><a name="1223" href="PropertiesAns.html#1200" class="Bound"
      >m</a
      ><a name="1224"
      >
</a
      ><a name="1225" href="PropertiesAns.html#1188" class="Function"
      >*-comm</a
      ><a name="1231"
      > </a
      ><a name="1232" href="Naturals.html#1080" class="InductiveConstructor"
      >zero</a
      ><a name="1236"
      > </a
      ><a name="1237" href="PropertiesAns.html#1237" class="Bound"
      >n</a
      ><a name="1238"
      > </a
      ><a name="1239" class="Keyword"
      >rewrite</a
      ><a name="1246"
      > </a
      ><a name="1247" href="PropertiesAns.html#957" class="Function"
      >*-zero</a
      ><a name="1253"
      > </a
      ><a name="1254" href="PropertiesAns.html#1237" class="Bound"
      >n</a
      ><a name="1255"
      > </a
      ><a name="1256" class="Symbol"
      >=</a
      ><a name="1257"
      > </a
      ><a name="1258" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="1262"
      >
</a
      ><a name="1263" href="PropertiesAns.html#1188" class="Function"
      >*-comm</a
      ><a name="1269"
      > </a
      ><a name="1270" class="Symbol"
      >(</a
      ><a name="1271" href="Naturals.html#1091" class="InductiveConstructor"
      >suc</a
      ><a name="1274"
      > </a
      ><a name="1275" href="PropertiesAns.html#1275" class="Bound"
      >m</a
      ><a name="1276" class="Symbol"
      >)</a
      ><a name="1277"
      > </a
      ><a name="1278" href="PropertiesAns.html#1278" class="Bound"
      >n</a
      ><a name="1279"
      > </a
      ><a name="1280" class="Keyword"
      >rewrite</a
      ><a name="1287"
      > </a
      ><a name="1288" href="PropertiesAns.html#1053" class="Function"
      >+-*-suc</a
      ><a name="1295"
      > </a
      ><a name="1296" href="PropertiesAns.html#1275" class="Bound"
      >m</a
      ><a name="1297"
      > </a
      ><a name="1298" href="PropertiesAns.html#1278" class="Bound"
      >n</a
      ><a name="1299"
      > </a
      ><a name="1300" class="Symbol"
      >|</a
      ><a name="1301"
      > </a
      ><a name="1302" href="PropertiesAns.html#1188" class="Function"
      >*-comm</a
      ><a name="1308"
      > </a
      ><a name="1309" href="PropertiesAns.html#1275" class="Bound"
      >m</a
      ><a name="1310"
      > </a
      ><a name="1311" href="PropertiesAns.html#1278" class="Bound"
      >n</a
      ><a name="1312"
      > </a
      ><a name="1313" class="Symbol"
      >=</a
      ><a name="1314"
      > </a
      ><a name="1315" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      >
{% endraw %}</pre>

*Monus from zero*

<pre class="Agda">{% raw %}
<a name="1364" href="PropertiesAns.html#1364" class="Function"
      >0&#8760;n&#8801;0</a
      ><a name="1369"
      > </a
      ><a name="1370" class="Symbol"
      >:</a
      ><a name="1371"
      > </a
      ><a name="1372" class="Symbol"
      >&#8704;</a
      ><a name="1373"
      > </a
      ><a name="1374" class="Symbol"
      >(</a
      ><a name="1375" href="PropertiesAns.html#1375" class="Bound"
      >n</a
      ><a name="1376"
      > </a
      ><a name="1377" class="Symbol"
      >:</a
      ><a name="1378"
      > </a
      ><a name="1379" href="Naturals.html#1064" class="Datatype"
      >&#8469;</a
      ><a name="1380" class="Symbol"
      >)</a
      ><a name="1381"
      > </a
      ><a name="1382" class="Symbol"
      >&#8594;</a
      ><a name="1383"
      > </a
      ><a name="1384" href="Naturals.html#1080" class="InductiveConstructor"
      >zero</a
      ><a name="1388"
      > </a
      ><a name="1389" href="Naturals.html#13851" class="Primitive Operator"
      >&#8760;</a
      ><a name="1390"
      > </a
      ><a name="1391" href="PropertiesAns.html#1375" class="Bound"
      >n</a
      ><a name="1392"
      > </a
      ><a name="1393" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="1394"
      > </a
      ><a name="1395" href="Naturals.html#1080" class="InductiveConstructor"
      >zero</a
      ><a name="1399"
      >
</a
      ><a name="1400" href="PropertiesAns.html#1364" class="Function"
      >0&#8760;n&#8801;0</a
      ><a name="1405"
      > </a
      ><a name="1406" href="Naturals.html#1080" class="InductiveConstructor"
      >zero</a
      ><a name="1410"
      > </a
      ><a name="1411" class="Symbol"
      >=</a
      ><a name="1412"
      > </a
      ><a name="1413" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="1417"
      >
</a
      ><a name="1418" href="PropertiesAns.html#1364" class="Function"
      >0&#8760;n&#8801;0</a
      ><a name="1423"
      > </a
      ><a name="1424" class="Symbol"
      >(</a
      ><a name="1425" href="Naturals.html#1091" class="InductiveConstructor"
      >suc</a
      ><a name="1428"
      > </a
      ><a name="1429" href="PropertiesAns.html#1429" class="Bound"
      >n</a
      ><a name="1430" class="Symbol"
      >)</a
      ><a name="1431"
      > </a
      ><a name="1432" class="Symbol"
      >=</a
      ><a name="1433"
      > </a
      ><a name="1434" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      >
{% endraw %}</pre>

The proof does not require induction.

*Associativity of monus with addition*

<pre class="Agda">{% raw %}
<a name="1543" href="PropertiesAns.html#1543" class="Function"
      >&#8760;-+-assoc</a
      ><a name="1552"
      > </a
      ><a name="1553" class="Symbol"
      >:</a
      ><a name="1554"
      > </a
      ><a name="1555" class="Symbol"
      >&#8704;</a
      ><a name="1556"
      > </a
      ><a name="1557" class="Symbol"
      >(</a
      ><a name="1558" href="PropertiesAns.html#1558" class="Bound"
      >m</a
      ><a name="1559"
      > </a
      ><a name="1560" href="PropertiesAns.html#1560" class="Bound"
      >n</a
      ><a name="1561"
      > </a
      ><a name="1562" href="PropertiesAns.html#1562" class="Bound"
      >p</a
      ><a name="1563"
      > </a
      ><a name="1564" class="Symbol"
      >:</a
      ><a name="1565"
      > </a
      ><a name="1566" href="Naturals.html#1064" class="Datatype"
      >&#8469;</a
      ><a name="1567" class="Symbol"
      >)</a
      ><a name="1568"
      > </a
      ><a name="1569" class="Symbol"
      >&#8594;</a
      ><a name="1570"
      > </a
      ><a name="1571" class="Symbol"
      >(</a
      ><a name="1572" href="PropertiesAns.html#1558" class="Bound"
      >m</a
      ><a name="1573"
      > </a
      ><a name="1574" href="Naturals.html#13851" class="Primitive Operator"
      >&#8760;</a
      ><a name="1575"
      > </a
      ><a name="1576" href="PropertiesAns.html#1560" class="Bound"
      >n</a
      ><a name="1577" class="Symbol"
      >)</a
      ><a name="1578"
      > </a
      ><a name="1579" href="Naturals.html#13851" class="Primitive Operator"
      >&#8760;</a
      ><a name="1580"
      > </a
      ><a name="1581" href="PropertiesAns.html#1562" class="Bound"
      >p</a
      ><a name="1582"
      > </a
      ><a name="1583" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="1584"
      > </a
      ><a name="1585" href="PropertiesAns.html#1558" class="Bound"
      >m</a
      ><a name="1586"
      > </a
      ><a name="1587" href="Naturals.html#13851" class="Primitive Operator"
      >&#8760;</a
      ><a name="1588"
      > </a
      ><a name="1589" class="Symbol"
      >(</a
      ><a name="1590" href="PropertiesAns.html#1560" class="Bound"
      >n</a
      ><a name="1591"
      > </a
      ><a name="1592" href="Naturals.html#9439" class="Primitive Operator"
      >+</a
      ><a name="1593"
      > </a
      ><a name="1594" href="PropertiesAns.html#1562" class="Bound"
      >p</a
      ><a name="1595" class="Symbol"
      >)</a
      ><a name="1596"
      >
</a
      ><a name="1597" href="PropertiesAns.html#1543" class="Function"
      >&#8760;-+-assoc</a
      ><a name="1606"
      > </a
      ><a name="1607" href="PropertiesAns.html#1607" class="Bound"
      >m</a
      ><a name="1608"
      > </a
      ><a name="1609" href="Naturals.html#1080" class="InductiveConstructor"
      >zero</a
      ><a name="1613"
      > </a
      ><a name="1614" href="PropertiesAns.html#1614" class="Bound"
      >p</a
      ><a name="1615"
      > </a
      ><a name="1616" class="Symbol"
      >=</a
      ><a name="1617"
      > </a
      ><a name="1618" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="1622"
      >
</a
      ><a name="1623" href="PropertiesAns.html#1543" class="Function"
      >&#8760;-+-assoc</a
      ><a name="1632"
      > </a
      ><a name="1633" href="Naturals.html#1080" class="InductiveConstructor"
      >zero</a
      ><a name="1637"
      > </a
      ><a name="1638" class="Symbol"
      >(</a
      ><a name="1639" href="Naturals.html#1091" class="InductiveConstructor"
      >suc</a
      ><a name="1642"
      > </a
      ><a name="1643" href="PropertiesAns.html#1643" class="Bound"
      >n</a
      ><a name="1644" class="Symbol"
      >)</a
      ><a name="1645"
      > </a
      ><a name="1646" href="PropertiesAns.html#1646" class="Bound"
      >p</a
      ><a name="1647"
      > </a
      ><a name="1648" class="Keyword"
      >rewrite</a
      ><a name="1655"
      > </a
      ><a name="1656" href="PropertiesAns.html#1364" class="Function"
      >0&#8760;n&#8801;0</a
      ><a name="1661"
      > </a
      ><a name="1662" href="PropertiesAns.html#1646" class="Bound"
      >p</a
      ><a name="1663"
      > </a
      ><a name="1664" class="Symbol"
      >=</a
      ><a name="1665"
      > </a
      ><a name="1666" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="1670"
      >
</a
      ><a name="1671" href="PropertiesAns.html#1543" class="Function"
      >&#8760;-+-assoc</a
      ><a name="1680"
      > </a
      ><a name="1681" class="Symbol"
      >(</a
      ><a name="1682" href="Naturals.html#1091" class="InductiveConstructor"
      >suc</a
      ><a name="1685"
      > </a
      ><a name="1686" href="PropertiesAns.html#1686" class="Bound"
      >m</a
      ><a name="1687" class="Symbol"
      >)</a
      ><a name="1688"
      > </a
      ><a name="1689" class="Symbol"
      >(</a
      ><a name="1690" href="Naturals.html#1091" class="InductiveConstructor"
      >suc</a
      ><a name="1693"
      > </a
      ><a name="1694" href="PropertiesAns.html#1694" class="Bound"
      >n</a
      ><a name="1695" class="Symbol"
      >)</a
      ><a name="1696"
      > </a
      ><a name="1697" href="PropertiesAns.html#1697" class="Bound"
      >p</a
      ><a name="1698"
      > </a
      ><a name="1699" class="Keyword"
      >rewrite</a
      ><a name="1706"
      > </a
      ><a name="1707" href="PropertiesAns.html#1543" class="Function"
      >&#8760;-+-assoc</a
      ><a name="1716"
      > </a
      ><a name="1717" href="PropertiesAns.html#1686" class="Bound"
      >m</a
      ><a name="1718"
      > </a
      ><a name="1719" href="PropertiesAns.html#1694" class="Bound"
      >n</a
      ><a name="1720"
      > </a
      ><a name="1721" href="PropertiesAns.html#1697" class="Bound"
      >p</a
      ><a name="1722"
      > </a
      ><a name="1723" class="Symbol"
      >=</a
      ><a name="1724"
      > </a
      ><a name="1725" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      >
{% endraw %}</pre>


