
---
title     : "Basics: Functional Programming in Agda"
layout    : page
permalink : /Basics
---

<pre class="Agda">{% raw %}
<a name="114" class="Keyword"
      >open</a
      ><a name="118"
      > </a
      ><a name="119" class="Keyword"
      >import</a
      ><a name="125"
      > </a
      ><a name="126" href="https://agda.github.io/agda-stdlib/Data.Empty.html#1" class="Module"
      >Data.Empty</a
      ><a name="136"
      >       </a
      ><a name="143" class="Keyword"
      >using</a
      ><a name="148"
      > </a
      ><a name="149" class="Symbol"
      >(</a
      ><a name="150" href="https://agda.github.io/agda-stdlib/Data.Empty.html#243" class="Datatype"
      >&#8869;</a
      ><a name="151" class="Symbol"
      >;</a
      ><a name="152"
      > </a
      ><a name="153" href="https://agda.github.io/agda-stdlib/Data.Empty.html#348" class="Function"
      >&#8869;-elim</a
      ><a name="159" class="Symbol"
      >)</a
      ><a name="160"
      >
</a
      ><a name="161" class="Keyword"
      >open</a
      ><a name="165"
      > </a
      ><a name="166" class="Keyword"
      >import</a
      ><a name="172"
      > </a
      ><a name="173" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#1" class="Module"
      >Relation.Nullary</a
      ><a name="189"
      > </a
      ><a name="190" class="Keyword"
      >using</a
      ><a name="195"
      > </a
      ><a name="196" class="Symbol"
      >(</a
      ><a name="197" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#414" class="Function Operator"
      >&#172;_</a
      ><a name="199" class="Symbol"
      >;</a
      ><a name="200"
      > </a
      ><a name="201" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#484" class="Datatype"
      >Dec</a
      ><a name="204" class="Symbol"
      >;</a
      ><a name="205"
      > </a
      ><a name="206" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#520" class="InductiveConstructor"
      >yes</a
      ><a name="209" class="Symbol"
      >;</a
      ><a name="210"
      > </a
      ><a name="211" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#547" class="InductiveConstructor"
      >no</a
      ><a name="213" class="Symbol"
      >)</a
      ><a name="214"
      >
</a
      ><a name="215" class="Keyword"
      >open</a
      ><a name="219"
      > </a
      ><a name="220" class="Keyword"
      >import</a
      ><a name="226"
      > </a
      ><a name="227" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#1" class="Module"
      >Relation.Binary.PropositionalEquality</a
      ><a name="264"
      >
                             </a
      ><a name="294" class="Keyword"
      >using</a
      ><a name="299"
      > </a
      ><a name="300" class="Symbol"
      >(</a
      ><a name="301" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >_&#8801;_</a
      ><a name="304" class="Symbol"
      >;</a
      ><a name="305"
      > </a
      ><a name="306" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="310" class="Symbol"
      >;</a
      ><a name="311"
      > </a
      ><a name="312" href="https://agda.github.io/agda-stdlib/Relation.Binary.Core.html#4493" class="Function Operator"
      >_&#8802;_</a
      ><a name="315" class="Symbol"
      >;</a
      ><a name="316"
      > </a
      ><a name="317" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.Core.html#632" class="Function"
      >trans</a
      ><a name="322" class="Symbol"
      >;</a
      ><a name="323"
      > </a
      ><a name="324" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.Core.html#565" class="Function"
      >sym</a
      ><a name="327" class="Symbol"
      >)</a
      >
{% endraw %}</pre>

# Natural numbers

<pre class="Agda">{% raw %}
<a name="373" class="Keyword"
      >data</a
      ><a name="377"
      > </a
      ><a name="378" href="Basics0.html#378" class="Datatype"
      >&#8469;</a
      ><a name="379"
      > </a
      ><a name="380" class="Symbol"
      >:</a
      ><a name="381"
      > </a
      ><a name="382" class="PrimitiveType"
      >Set</a
      ><a name="385"
      > </a
      ><a name="386" class="Keyword"
      >where</a
      ><a name="391"
      >
  </a
      ><a name="394" href="Basics0.html#394" class="InductiveConstructor"
      >zero</a
      ><a name="398"
      > </a
      ><a name="399" class="Symbol"
      >:</a
      ><a name="400"
      > </a
      ><a name="401" href="Basics0.html#378" class="Datatype"
      >&#8469;</a
      ><a name="402"
      >
  </a
      ><a name="405" href="Basics0.html#405" class="InductiveConstructor"
      >suc</a
      ><a name="408"
      > </a
      ><a name="409" class="Symbol"
      >:</a
      ><a name="410"
      > </a
      ><a name="411" href="Basics0.html#378" class="Datatype"
      >&#8469;</a
      ><a name="412"
      > </a
      ><a name="413" class="Symbol"
      >&#8594;</a
      ><a name="414"
      > </a
      ><a name="415" href="Basics0.html#378" class="Datatype"
      >&#8469;</a
      ><a name="416"
      >
</a
      ><a name="417" class="Symbol"
      >{-#</a
      ><a name="420"
      > </a
      ><a name="421" class="Keyword"
      >BUILTIN</a
      ><a name="428"
      > NATURAL </a
      ><a name="437" href="Basics0.html#378" class="Datatype"
      >&#8469;</a
      ><a name="438"
      > </a
      ><a name="439" class="Symbol"
      >#-}</a
      >
{% endraw %}</pre>

<pre class="Agda">{% raw %}
<a name="468" href="Basics0.html#468" class="Function"
      >congruent</a
      ><a name="477"
      > </a
      ><a name="478" class="Symbol"
      >:</a
      ><a name="479"
      > </a
      ><a name="480" class="Symbol"
      >&#8704;</a
      ><a name="481"
      > </a
      ><a name="482" class="Symbol"
      >{</a
      ><a name="483" href="Basics0.html#483" class="Bound"
      >m</a
      ><a name="484"
      > </a
      ><a name="485" href="Basics0.html#485" class="Bound"
      >n</a
      ><a name="486" class="Symbol"
      >}</a
      ><a name="487"
      > </a
      ><a name="488" class="Symbol"
      >&#8594;</a
      ><a name="489"
      > </a
      ><a name="490" href="Basics0.html#483" class="Bound"
      >m</a
      ><a name="491"
      > </a
      ><a name="492" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="493"
      > </a
      ><a name="494" href="Basics0.html#485" class="Bound"
      >n</a
      ><a name="495"
      > </a
      ><a name="496" class="Symbol"
      >&#8594;</a
      ><a name="497"
      > </a
      ><a name="498" href="Basics0.html#405" class="InductiveConstructor"
      >suc</a
      ><a name="501"
      > </a
      ><a name="502" href="Basics0.html#483" class="Bound"
      >m</a
      ><a name="503"
      > </a
      ><a name="504" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="505"
      > </a
      ><a name="506" href="Basics0.html#405" class="InductiveConstructor"
      >suc</a
      ><a name="509"
      > </a
      ><a name="510" href="Basics0.html#485" class="Bound"
      >n</a
      ><a name="511"
      >
</a
      ><a name="512" href="Basics0.html#468" class="Function"
      >congruent</a
      ><a name="521"
      > </a
      ><a name="522" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="526"
      > </a
      ><a name="527" class="Symbol"
      >=</a
      ><a name="528"
      > </a
      ><a name="529" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="533"
      >

</a
      ><a name="535" href="Basics0.html#535" class="Function"
      >injective</a
      ><a name="544"
      > </a
      ><a name="545" class="Symbol"
      >:</a
      ><a name="546"
      > </a
      ><a name="547" class="Symbol"
      >&#8704;</a
      ><a name="548"
      > </a
      ><a name="549" class="Symbol"
      >{</a
      ><a name="550" href="Basics0.html#550" class="Bound"
      >m</a
      ><a name="551"
      > </a
      ><a name="552" href="Basics0.html#552" class="Bound"
      >n</a
      ><a name="553" class="Symbol"
      >}</a
      ><a name="554"
      > </a
      ><a name="555" class="Symbol"
      >&#8594;</a
      ><a name="556"
      > </a
      ><a name="557" href="Basics0.html#405" class="InductiveConstructor"
      >suc</a
      ><a name="560"
      > </a
      ><a name="561" href="Basics0.html#550" class="Bound"
      >m</a
      ><a name="562"
      > </a
      ><a name="563" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="564"
      > </a
      ><a name="565" href="Basics0.html#405" class="InductiveConstructor"
      >suc</a
      ><a name="568"
      > </a
      ><a name="569" href="Basics0.html#552" class="Bound"
      >n</a
      ><a name="570"
      > </a
      ><a name="571" class="Symbol"
      >&#8594;</a
      ><a name="572"
      > </a
      ><a name="573" href="Basics0.html#550" class="Bound"
      >m</a
      ><a name="574"
      > </a
      ><a name="575" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="576"
      > </a
      ><a name="577" href="Basics0.html#552" class="Bound"
      >n</a
      ><a name="578"
      >
</a
      ><a name="579" href="Basics0.html#535" class="Function"
      >injective</a
      ><a name="588"
      > </a
      ><a name="589" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="593"
      > </a
      ><a name="594" class="Symbol"
      >=</a
      ><a name="595"
      > </a
      ><a name="596" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="600"
      >

</a
      ><a name="602" href="Basics0.html#602" class="Function"
      >distinct</a
      ><a name="610"
      > </a
      ><a name="611" class="Symbol"
      >:</a
      ><a name="612"
      > </a
      ><a name="613" class="Symbol"
      >&#8704;</a
      ><a name="614"
      > </a
      ><a name="615" class="Symbol"
      >{</a
      ><a name="616" href="Basics0.html#616" class="Bound"
      >m</a
      ><a name="617" class="Symbol"
      >}</a
      ><a name="618"
      > </a
      ><a name="619" class="Symbol"
      >&#8594;</a
      ><a name="620"
      > </a
      ><a name="621" href="Basics0.html#394" class="InductiveConstructor"
      >zero</a
      ><a name="625"
      > </a
      ><a name="626" href="https://agda.github.io/agda-stdlib/Relation.Binary.Core.html#4493" class="Function Operator"
      >&#8802;</a
      ><a name="627"
      > </a
      ><a name="628" href="Basics0.html#405" class="InductiveConstructor"
      >suc</a
      ><a name="631"
      > </a
      ><a name="632" href="Basics0.html#616" class="Bound"
      >m</a
      ><a name="633"
      >
</a
      ><a name="634" href="Basics0.html#602" class="Function"
      >distinct</a
      ><a name="642"
      > </a
      ><a name="643" class="Symbol"
      >()</a
      >
{% endraw %}</pre>

<pre class="Agda">{% raw %}
<a name="671" href="Basics0.html#671" class="Function Operator"
      >_&#8799;_</a
      ><a name="674"
      > </a
      ><a name="675" class="Symbol"
      >:</a
      ><a name="676"
      > </a
      ><a name="677" class="Symbol"
      >&#8704;</a
      ><a name="678"
      > </a
      ><a name="679" class="Symbol"
      >(</a
      ><a name="680" href="Basics0.html#680" class="Bound"
      >m</a
      ><a name="681"
      > </a
      ><a name="682" href="Basics0.html#682" class="Bound"
      >n</a
      ><a name="683"
      > </a
      ><a name="684" class="Symbol"
      >:</a
      ><a name="685"
      > </a
      ><a name="686" href="Basics0.html#378" class="Datatype"
      >&#8469;</a
      ><a name="687" class="Symbol"
      >)</a
      ><a name="688"
      > </a
      ><a name="689" class="Symbol"
      >&#8594;</a
      ><a name="690"
      > </a
      ><a name="691" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#484" class="Datatype"
      >Dec</a
      ><a name="694"
      > </a
      ><a name="695" class="Symbol"
      >(</a
      ><a name="696" href="Basics0.html#680" class="Bound"
      >m</a
      ><a name="697"
      > </a
      ><a name="698" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="699"
      > </a
      ><a name="700" href="Basics0.html#682" class="Bound"
      >n</a
      ><a name="701" class="Symbol"
      >)</a
      ><a name="702"
      >
</a
      ><a name="703" href="Basics0.html#394" class="InductiveConstructor"
      >zero</a
      ><a name="707"
      > </a
      ><a name="708" href="Basics0.html#671" class="Function Operator"
      >&#8799;</a
      ><a name="709"
      > </a
      ><a name="710" href="Basics0.html#394" class="InductiveConstructor"
      >zero</a
      ><a name="714"
      > </a
      ><a name="715" class="Symbol"
      >=</a
      ><a name="716"
      >  </a
      ><a name="718" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#520" class="InductiveConstructor"
      >yes</a
      ><a name="721"
      > </a
      ><a name="722" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="726"
      >
</a
      ><a name="727" href="Basics0.html#394" class="InductiveConstructor"
      >zero</a
      ><a name="731"
      > </a
      ><a name="732" href="Basics0.html#671" class="Function Operator"
      >&#8799;</a
      ><a name="733"
      > </a
      ><a name="734" href="Basics0.html#405" class="InductiveConstructor"
      >suc</a
      ><a name="737"
      > </a
      ><a name="738" href="Basics0.html#738" class="Bound"
      >n</a
      ><a name="739"
      > </a
      ><a name="740" class="Symbol"
      >=</a
      ><a name="741"
      >  </a
      ><a name="743" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#547" class="InductiveConstructor"
      >no</a
      ><a name="745"
      > </a
      ><a name="746" class="Symbol"
      >(&#955;())</a
      ><a name="751"
      > 
</a
      ><a name="753" href="Basics0.html#405" class="InductiveConstructor"
      >suc</a
      ><a name="756"
      > </a
      ><a name="757" href="Basics0.html#757" class="Bound"
      >m</a
      ><a name="758"
      > </a
      ><a name="759" href="Basics0.html#671" class="Function Operator"
      >&#8799;</a
      ><a name="760"
      > </a
      ><a name="761" href="Basics0.html#394" class="InductiveConstructor"
      >zero</a
      ><a name="765"
      > </a
      ><a name="766" class="Symbol"
      >=</a
      ><a name="767"
      >  </a
      ><a name="769" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#547" class="InductiveConstructor"
      >no</a
      ><a name="771"
      > </a
      ><a name="772" class="Symbol"
      >(&#955;())</a
      ><a name="777"
      >
</a
      ><a name="778" href="Basics0.html#405" class="InductiveConstructor"
      >suc</a
      ><a name="781"
      > </a
      ><a name="782" href="Basics0.html#782" class="Bound"
      >m</a
      ><a name="783"
      > </a
      ><a name="784" href="Basics0.html#671" class="Function Operator"
      >&#8799;</a
      ><a name="785"
      > </a
      ><a name="786" href="Basics0.html#405" class="InductiveConstructor"
      >suc</a
      ><a name="789"
      > </a
      ><a name="790" href="Basics0.html#790" class="Bound"
      >n</a
      ><a name="791"
      > </a
      ><a name="792" class="Keyword"
      >with</a
      ><a name="796"
      > </a
      ><a name="797" href="Basics0.html#782" class="Bound"
      >m</a
      ><a name="798"
      > </a
      ><a name="799" href="Basics0.html#671" class="Function Operator"
      >&#8799;</a
      ><a name="800"
      > </a
      ><a name="801" href="Basics0.html#790" class="Bound"
      >n</a
      ><a name="802"
      >
</a
      ><a name="803" class="Symbol"
      >...</a
      ><a name="806"
      > </a
      ><a name="807" class="Symbol"
      >|</a
      ><a name="808"
      > </a
      ><a name="809" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#520" class="InductiveConstructor"
      >yes</a
      ><a name="812"
      > </a
      ><a name="813" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="817"
      > </a
      ><a name="818" class="Symbol"
      >=</a
      ><a name="819"
      >  </a
      ><a name="821" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#520" class="InductiveConstructor"
      >yes</a
      ><a name="824"
      > </a
      ><a name="825" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="829"
      >
</a
      ><a name="830" class="Symbol"
      >...</a
      ><a name="833"
      > </a
      ><a name="834" class="Symbol"
      >|</a
      ><a name="835"
      > </a
      ><a name="836" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#547" class="InductiveConstructor"
      >no</a
      ><a name="838"
      > </a
      ><a name="839" href="Basics0.html#839" class="Bound"
      >p</a
      ><a name="840"
      > </a
      ><a name="841" class="Symbol"
      >=</a
      ><a name="842"
      >  </a
      ><a name="844" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#547" class="InductiveConstructor"
      >no</a
      ><a name="846"
      > </a
      ><a name="847" class="Symbol"
      >(&#955;</a
      ><a name="849"
      > </a
      ><a name="850" href="Basics0.html#850" class="Bound"
      >r</a
      ><a name="851"
      > </a
      ><a name="852" class="Symbol"
      >&#8594;</a
      ><a name="853"
      > </a
      ><a name="854" href="Basics0.html#839" class="Bound"
      >p</a
      ><a name="855"
      > </a
      ><a name="856" class="Symbol"
      >(</a
      ><a name="857" href="Basics0.html#535" class="Function"
      >injective</a
      ><a name="866"
      > </a
      ><a name="867" href="Basics0.html#850" class="Bound"
      >r</a
      ><a name="868" class="Symbol"
      >))</a
      >
{% endraw %}</pre>

# Addition and its properties

<pre class="Agda">{% raw %}
<a name="927" href="Basics0.html#927" class="Function Operator"
      >_+_</a
      ><a name="930"
      > </a
      ><a name="931" class="Symbol"
      >:</a
      ><a name="932"
      > </a
      ><a name="933" href="Basics0.html#378" class="Datatype"
      >&#8469;</a
      ><a name="934"
      > </a
      ><a name="935" class="Symbol"
      >&#8594;</a
      ><a name="936"
      > </a
      ><a name="937" href="Basics0.html#378" class="Datatype"
      >&#8469;</a
      ><a name="938"
      > </a
      ><a name="939" class="Symbol"
      >&#8594;</a
      ><a name="940"
      > </a
      ><a name="941" href="Basics0.html#378" class="Datatype"
      >&#8469;</a
      ><a name="942"
      >
</a
      ><a name="943" href="Basics0.html#394" class="InductiveConstructor"
      >zero</a
      ><a name="947"
      > </a
      ><a name="948" href="Basics0.html#927" class="Function Operator"
      >+</a
      ><a name="949"
      > </a
      ><a name="950" href="Basics0.html#950" class="Bound"
      >n</a
      ><a name="951"
      > </a
      ><a name="952" class="Symbol"
      >=</a
      ><a name="953"
      > </a
      ><a name="954" href="Basics0.html#950" class="Bound"
      >n</a
      ><a name="955"
      >
</a
      ><a name="956" href="Basics0.html#405" class="InductiveConstructor"
      >suc</a
      ><a name="959"
      > </a
      ><a name="960" href="Basics0.html#960" class="Bound"
      >m</a
      ><a name="961"
      > </a
      ><a name="962" href="Basics0.html#927" class="Function Operator"
      >+</a
      ><a name="963"
      > </a
      ><a name="964" href="Basics0.html#964" class="Bound"
      >n</a
      ><a name="965"
      > </a
      ><a name="966" class="Symbol"
      >=</a
      ><a name="967"
      > </a
      ><a name="968" href="Basics0.html#405" class="InductiveConstructor"
      >suc</a
      ><a name="971"
      > </a
      ><a name="972" class="Symbol"
      >(</a
      ><a name="973" href="Basics0.html#960" class="Bound"
      >m</a
      ><a name="974"
      > </a
      ><a name="975" href="Basics0.html#927" class="Function Operator"
      >+</a
      ><a name="976"
      > </a
      ><a name="977" href="Basics0.html#964" class="Bound"
      >n</a
      ><a name="978" class="Symbol"
      >)</a
      >
{% endraw %}</pre>

<pre class="Agda">{% raw %}
<a name="1005" href="Basics0.html#1005" class="Function"
      >+-assoc</a
      ><a name="1012"
      > </a
      ><a name="1013" class="Symbol"
      >:</a
      ><a name="1014"
      > </a
      ><a name="1015" class="Symbol"
      >&#8704;</a
      ><a name="1016"
      > </a
      ><a name="1017" href="Basics0.html#1017" class="Bound"
      >m</a
      ><a name="1018"
      > </a
      ><a name="1019" href="Basics0.html#1019" class="Bound"
      >n</a
      ><a name="1020"
      > </a
      ><a name="1021" href="Basics0.html#1021" class="Bound"
      >p</a
      ><a name="1022"
      > </a
      ><a name="1023" class="Symbol"
      >&#8594;</a
      ><a name="1024"
      > </a
      ><a name="1025" class="Symbol"
      >(</a
      ><a name="1026" href="Basics0.html#1017" class="Bound"
      >m</a
      ><a name="1027"
      > </a
      ><a name="1028" href="Basics0.html#927" class="Function Operator"
      >+</a
      ><a name="1029"
      > </a
      ><a name="1030" href="Basics0.html#1019" class="Bound"
      >n</a
      ><a name="1031" class="Symbol"
      >)</a
      ><a name="1032"
      > </a
      ><a name="1033" href="Basics0.html#927" class="Function Operator"
      >+</a
      ><a name="1034"
      > </a
      ><a name="1035" href="Basics0.html#1021" class="Bound"
      >p</a
      ><a name="1036"
      > </a
      ><a name="1037" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="1038"
      > </a
      ><a name="1039" href="Basics0.html#1017" class="Bound"
      >m</a
      ><a name="1040"
      > </a
      ><a name="1041" href="Basics0.html#927" class="Function Operator"
      >+</a
      ><a name="1042"
      > </a
      ><a name="1043" class="Symbol"
      >(</a
      ><a name="1044" href="Basics0.html#1019" class="Bound"
      >n</a
      ><a name="1045"
      > </a
      ><a name="1046" href="Basics0.html#927" class="Function Operator"
      >+</a
      ><a name="1047"
      > </a
      ><a name="1048" href="Basics0.html#1021" class="Bound"
      >p</a
      ><a name="1049" class="Symbol"
      >)</a
      ><a name="1050"
      >
</a
      ><a name="1051" href="Basics0.html#1005" class="Function"
      >+-assoc</a
      ><a name="1058"
      > </a
      ><a name="1059" href="Basics0.html#394" class="InductiveConstructor"
      >zero</a
      ><a name="1063"
      > </a
      ><a name="1064" href="Basics0.html#1064" class="Bound"
      >n</a
      ><a name="1065"
      > </a
      ><a name="1066" href="Basics0.html#1066" class="Bound"
      >p</a
      ><a name="1067"
      > </a
      ><a name="1068" class="Symbol"
      >=</a
      ><a name="1069"
      > </a
      ><a name="1070" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="1074"
      >
</a
      ><a name="1075" href="Basics0.html#1005" class="Function"
      >+-assoc</a
      ><a name="1082"
      > </a
      ><a name="1083" class="Symbol"
      >(</a
      ><a name="1084" href="Basics0.html#405" class="InductiveConstructor"
      >suc</a
      ><a name="1087"
      > </a
      ><a name="1088" href="Basics0.html#1088" class="Bound"
      >m</a
      ><a name="1089" class="Symbol"
      >)</a
      ><a name="1090"
      > </a
      ><a name="1091" href="Basics0.html#1091" class="Bound"
      >n</a
      ><a name="1092"
      > </a
      ><a name="1093" href="Basics0.html#1093" class="Bound"
      >p</a
      ><a name="1094"
      > </a
      ><a name="1095" class="Keyword"
      >rewrite</a
      ><a name="1102"
      > </a
      ><a name="1103" href="Basics0.html#1005" class="Function"
      >+-assoc</a
      ><a name="1110"
      > </a
      ><a name="1111" href="Basics0.html#1088" class="Bound"
      >m</a
      ><a name="1112"
      > </a
      ><a name="1113" href="Basics0.html#1091" class="Bound"
      >n</a
      ><a name="1114"
      > </a
      ><a name="1115" href="Basics0.html#1093" class="Bound"
      >p</a
      ><a name="1116"
      > </a
      ><a name="1117" class="Symbol"
      >=</a
      ><a name="1118"
      > </a
      ><a name="1119" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="1123"
      >

</a
      ><a name="1125" href="Basics0.html#1125" class="Function"
      >+-zero</a
      ><a name="1131"
      > </a
      ><a name="1132" class="Symbol"
      >:</a
      ><a name="1133"
      > </a
      ><a name="1134" class="Symbol"
      >&#8704;</a
      ><a name="1135"
      > </a
      ><a name="1136" href="Basics0.html#1136" class="Bound"
      >m</a
      ><a name="1137"
      > </a
      ><a name="1138" class="Symbol"
      >&#8594;</a
      ><a name="1139"
      > </a
      ><a name="1140" href="Basics0.html#1136" class="Bound"
      >m</a
      ><a name="1141"
      > </a
      ><a name="1142" href="Basics0.html#927" class="Function Operator"
      >+</a
      ><a name="1143"
      > </a
      ><a name="1144" href="Basics0.html#394" class="InductiveConstructor"
      >zero</a
      ><a name="1148"
      > </a
      ><a name="1149" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="1150"
      > </a
      ><a name="1151" href="Basics0.html#1136" class="Bound"
      >m</a
      ><a name="1152"
      >
</a
      ><a name="1153" href="Basics0.html#1125" class="Function"
      >+-zero</a
      ><a name="1159"
      > </a
      ><a name="1160" href="Basics0.html#394" class="InductiveConstructor"
      >zero</a
      ><a name="1164"
      > </a
      ><a name="1165" class="Symbol"
      >=</a
      ><a name="1166"
      > </a
      ><a name="1167" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="1171"
      >
</a
      ><a name="1172" href="Basics0.html#1125" class="Function"
      >+-zero</a
      ><a name="1178"
      > </a
      ><a name="1179" class="Symbol"
      >(</a
      ><a name="1180" href="Basics0.html#405" class="InductiveConstructor"
      >suc</a
      ><a name="1183"
      > </a
      ><a name="1184" href="Basics0.html#1184" class="Bound"
      >m</a
      ><a name="1185" class="Symbol"
      >)</a
      ><a name="1186"
      > </a
      ><a name="1187" class="Keyword"
      >rewrite</a
      ><a name="1194"
      > </a
      ><a name="1195" href="Basics0.html#1125" class="Function"
      >+-zero</a
      ><a name="1201"
      > </a
      ><a name="1202" href="Basics0.html#1184" class="Bound"
      >m</a
      ><a name="1203"
      > </a
      ><a name="1204" class="Symbol"
      >=</a
      ><a name="1205"
      > </a
      ><a name="1206" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="1210"
      >

</a
      ><a name="1212" href="Basics0.html#1212" class="Function"
      >+-suc</a
      ><a name="1217"
      > </a
      ><a name="1218" class="Symbol"
      >:</a
      ><a name="1219"
      > </a
      ><a name="1220" class="Symbol"
      >&#8704;</a
      ><a name="1221"
      > </a
      ><a name="1222" href="Basics0.html#1222" class="Bound"
      >m</a
      ><a name="1223"
      > </a
      ><a name="1224" href="Basics0.html#1224" class="Bound"
      >n</a
      ><a name="1225"
      > </a
      ><a name="1226" class="Symbol"
      >&#8594;</a
      ><a name="1227"
      > </a
      ><a name="1228" href="Basics0.html#1222" class="Bound"
      >m</a
      ><a name="1229"
      > </a
      ><a name="1230" href="Basics0.html#927" class="Function Operator"
      >+</a
      ><a name="1231"
      > </a
      ><a name="1232" class="Symbol"
      >(</a
      ><a name="1233" href="Basics0.html#405" class="InductiveConstructor"
      >suc</a
      ><a name="1236"
      > </a
      ><a name="1237" href="Basics0.html#1224" class="Bound"
      >n</a
      ><a name="1238" class="Symbol"
      >)</a
      ><a name="1239"
      > </a
      ><a name="1240" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="1241"
      > </a
      ><a name="1242" href="Basics0.html#405" class="InductiveConstructor"
      >suc</a
      ><a name="1245"
      > </a
      ><a name="1246" class="Symbol"
      >(</a
      ><a name="1247" href="Basics0.html#1222" class="Bound"
      >m</a
      ><a name="1248"
      > </a
      ><a name="1249" href="Basics0.html#927" class="Function Operator"
      >+</a
      ><a name="1250"
      > </a
      ><a name="1251" href="Basics0.html#1224" class="Bound"
      >n</a
      ><a name="1252" class="Symbol"
      >)</a
      ><a name="1253"
      >
</a
      ><a name="1254" href="Basics0.html#1212" class="Function"
      >+-suc</a
      ><a name="1259"
      > </a
      ><a name="1260" href="Basics0.html#394" class="InductiveConstructor"
      >zero</a
      ><a name="1264"
      > </a
      ><a name="1265" href="Basics0.html#1265" class="Bound"
      >n</a
      ><a name="1266"
      > </a
      ><a name="1267" class="Symbol"
      >=</a
      ><a name="1268"
      > </a
      ><a name="1269" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="1273"
      >
</a
      ><a name="1274" href="Basics0.html#1212" class="Function"
      >+-suc</a
      ><a name="1279"
      > </a
      ><a name="1280" class="Symbol"
      >(</a
      ><a name="1281" href="Basics0.html#405" class="InductiveConstructor"
      >suc</a
      ><a name="1284"
      > </a
      ><a name="1285" href="Basics0.html#1285" class="Bound"
      >m</a
      ><a name="1286" class="Symbol"
      >)</a
      ><a name="1287"
      > </a
      ><a name="1288" href="Basics0.html#1288" class="Bound"
      >n</a
      ><a name="1289"
      > </a
      ><a name="1290" class="Keyword"
      >rewrite</a
      ><a name="1297"
      > </a
      ><a name="1298" href="Basics0.html#1212" class="Function"
      >+-suc</a
      ><a name="1303"
      > </a
      ><a name="1304" href="Basics0.html#1285" class="Bound"
      >m</a
      ><a name="1305"
      > </a
      ><a name="1306" href="Basics0.html#1288" class="Bound"
      >n</a
      ><a name="1307"
      > </a
      ><a name="1308" class="Symbol"
      >=</a
      ><a name="1309"
      > </a
      ><a name="1310" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="1314"
      >

</a
      ><a name="1316" href="Basics0.html#1316" class="Function"
      >+-comm</a
      ><a name="1322"
      > </a
      ><a name="1323" class="Symbol"
      >:</a
      ><a name="1324"
      > </a
      ><a name="1325" class="Symbol"
      >&#8704;</a
      ><a name="1326"
      > </a
      ><a name="1327" href="Basics0.html#1327" class="Bound"
      >m</a
      ><a name="1328"
      > </a
      ><a name="1329" href="Basics0.html#1329" class="Bound"
      >n</a
      ><a name="1330"
      > </a
      ><a name="1331" class="Symbol"
      >&#8594;</a
      ><a name="1332"
      > </a
      ><a name="1333" href="Basics0.html#1327" class="Bound"
      >m</a
      ><a name="1334"
      > </a
      ><a name="1335" href="Basics0.html#927" class="Function Operator"
      >+</a
      ><a name="1336"
      > </a
      ><a name="1337" href="Basics0.html#1329" class="Bound"
      >n</a
      ><a name="1338"
      > </a
      ><a name="1339" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="1340"
      > </a
      ><a name="1341" href="Basics0.html#1329" class="Bound"
      >n</a
      ><a name="1342"
      > </a
      ><a name="1343" href="Basics0.html#927" class="Function Operator"
      >+</a
      ><a name="1344"
      > </a
      ><a name="1345" href="Basics0.html#1327" class="Bound"
      >m</a
      ><a name="1346"
      >
</a
      ><a name="1347" href="Basics0.html#1316" class="Function"
      >+-comm</a
      ><a name="1353"
      > </a
      ><a name="1354" href="Basics0.html#1354" class="Bound"
      >m</a
      ><a name="1355"
      > </a
      ><a name="1356" href="Basics0.html#394" class="InductiveConstructor"
      >zero</a
      ><a name="1360"
      > </a
      ><a name="1361" class="Symbol"
      >=</a
      ><a name="1362"
      >  </a
      ><a name="1364" href="Basics0.html#1125" class="Function"
      >+-zero</a
      ><a name="1370"
      > </a
      ><a name="1371" href="Basics0.html#1354" class="Bound"
      >m</a
      ><a name="1372"
      >
</a
      ><a name="1373" href="Basics0.html#1316" class="Function"
      >+-comm</a
      ><a name="1379"
      > </a
      ><a name="1380" href="Basics0.html#1380" class="Bound"
      >m</a
      ><a name="1381"
      > </a
      ><a name="1382" class="Symbol"
      >(</a
      ><a name="1383" href="Basics0.html#405" class="InductiveConstructor"
      >suc</a
      ><a name="1386"
      > </a
      ><a name="1387" href="Basics0.html#1387" class="Bound"
      >n</a
      ><a name="1388" class="Symbol"
      >)</a
      ><a name="1389"
      > </a
      ><a name="1390" class="Keyword"
      >rewrite</a
      ><a name="1397"
      > </a
      ><a name="1398" href="Basics0.html#1212" class="Function"
      >+-suc</a
      ><a name="1403"
      > </a
      ><a name="1404" href="Basics0.html#1380" class="Bound"
      >m</a
      ><a name="1405"
      > </a
      ><a name="1406" href="Basics0.html#1387" class="Bound"
      >n</a
      ><a name="1407"
      > </a
      ><a name="1408" class="Symbol"
      >|</a
      ><a name="1409"
      > </a
      ><a name="1410" href="Basics0.html#1316" class="Function"
      >+-comm</a
      ><a name="1416"
      > </a
      ><a name="1417" href="Basics0.html#1380" class="Bound"
      >m</a
      ><a name="1418"
      > </a
      ><a name="1419" href="Basics0.html#1387" class="Bound"
      >n</a
      ><a name="1420"
      > </a
      ><a name="1421" class="Symbol"
      >=</a
      ><a name="1422"
      > </a
      ><a name="1423" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      >
{% endraw %}</pre>

# Equality and decidable equality for naturals




# Showing `double` injective

<pre class="Agda">{% raw %}
<a name="1534" href="Basics0.html#1534" class="Function"
      >double</a
      ><a name="1540"
      > </a
      ><a name="1541" class="Symbol"
      >:</a
      ><a name="1542"
      > </a
      ><a name="1543" href="Basics0.html#378" class="Datatype"
      >&#8469;</a
      ><a name="1544"
      > </a
      ><a name="1545" class="Symbol"
      >&#8594;</a
      ><a name="1546"
      > </a
      ><a name="1547" href="Basics0.html#378" class="Datatype"
      >&#8469;</a
      ><a name="1548"
      >
</a
      ><a name="1549" href="Basics0.html#1534" class="Function"
      >double</a
      ><a name="1555"
      > </a
      ><a name="1556" href="Basics0.html#394" class="InductiveConstructor"
      >zero</a
      ><a name="1560"
      >  </a
      ><a name="1562" class="Symbol"
      >=</a
      ><a name="1563"
      >  </a
      ><a name="1565" href="Basics0.html#394" class="InductiveConstructor"
      >zero</a
      ><a name="1569"
      >
</a
      ><a name="1570" href="Basics0.html#1534" class="Function"
      >double</a
      ><a name="1576"
      > </a
      ><a name="1577" class="Symbol"
      >(</a
      ><a name="1578" href="Basics0.html#405" class="InductiveConstructor"
      >suc</a
      ><a name="1581"
      > </a
      ><a name="1582" href="Basics0.html#1582" class="Bound"
      >n</a
      ><a name="1583" class="Symbol"
      >)</a
      ><a name="1584"
      >  </a
      ><a name="1586" class="Symbol"
      >=</a
      ><a name="1587"
      >  </a
      ><a name="1589" href="Basics0.html#405" class="InductiveConstructor"
      >suc</a
      ><a name="1592"
      > </a
      ><a name="1593" class="Symbol"
      >(</a
      ><a name="1594" href="Basics0.html#405" class="InductiveConstructor"
      >suc</a
      ><a name="1597"
      > </a
      ><a name="1598" class="Symbol"
      >(</a
      ><a name="1599" href="Basics0.html#1534" class="Function"
      >double</a
      ><a name="1605"
      > </a
      ><a name="1606" href="Basics0.html#1582" class="Bound"
      >n</a
      ><a name="1607" class="Symbol"
      >))</a
      >
{% endraw %}</pre>

<pre class="Agda">{% raw %}
<a name="1635" href="Basics0.html#1635" class="Function"
      >double-injective</a
      ><a name="1651"
      > </a
      ><a name="1652" class="Symbol"
      >:</a
      ><a name="1653"
      > </a
      ><a name="1654" class="Symbol"
      >&#8704;</a
      ><a name="1655"
      > </a
      ><a name="1656" href="Basics0.html#1656" class="Bound"
      >m</a
      ><a name="1657"
      > </a
      ><a name="1658" href="Basics0.html#1658" class="Bound"
      >n</a
      ><a name="1659"
      > </a
      ><a name="1660" class="Symbol"
      >&#8594;</a
      ><a name="1661"
      > </a
      ><a name="1662" href="Basics0.html#1534" class="Function"
      >double</a
      ><a name="1668"
      > </a
      ><a name="1669" href="Basics0.html#1656" class="Bound"
      >m</a
      ><a name="1670"
      > </a
      ><a name="1671" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="1672"
      > </a
      ><a name="1673" href="Basics0.html#1534" class="Function"
      >double</a
      ><a name="1679"
      > </a
      ><a name="1680" href="Basics0.html#1658" class="Bound"
      >n</a
      ><a name="1681"
      > </a
      ><a name="1682" class="Symbol"
      >&#8594;</a
      ><a name="1683"
      > </a
      ><a name="1684" href="Basics0.html#1656" class="Bound"
      >m</a
      ><a name="1685"
      > </a
      ><a name="1686" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="1687"
      > </a
      ><a name="1688" href="Basics0.html#1658" class="Bound"
      >n</a
      ><a name="1689"
      >
</a
      ><a name="1690" href="Basics0.html#1635" class="Function"
      >double-injective</a
      ><a name="1706"
      > </a
      ><a name="1707" href="Basics0.html#394" class="InductiveConstructor"
      >zero</a
      ><a name="1711"
      > </a
      ><a name="1712" href="Basics0.html#394" class="InductiveConstructor"
      >zero</a
      ><a name="1716"
      > </a
      ><a name="1717" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="1721"
      > </a
      ><a name="1722" class="Symbol"
      >=</a
      ><a name="1723"
      > </a
      ><a name="1724" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="1728"
      >
</a
      ><a name="1729" href="Basics0.html#1635" class="Function"
      >double-injective</a
      ><a name="1745"
      > </a
      ><a name="1746" href="Basics0.html#394" class="InductiveConstructor"
      >zero</a
      ><a name="1750"
      > </a
      ><a name="1751" class="Symbol"
      >(</a
      ><a name="1752" href="Basics0.html#405" class="InductiveConstructor"
      >suc</a
      ><a name="1755"
      > </a
      ><a name="1756" href="Basics0.html#1756" class="Bound"
      >n</a
      ><a name="1757" class="Symbol"
      >)</a
      ><a name="1758"
      > </a
      ><a name="1759" class="Symbol"
      >()</a
      ><a name="1761"
      >
</a
      ><a name="1762" href="Basics0.html#1635" class="Function"
      >double-injective</a
      ><a name="1778"
      > </a
      ><a name="1779" class="Symbol"
      >(</a
      ><a name="1780" href="Basics0.html#405" class="InductiveConstructor"
      >suc</a
      ><a name="1783"
      > </a
      ><a name="1784" href="Basics0.html#1784" class="Bound"
      >m</a
      ><a name="1785" class="Symbol"
      >)</a
      ><a name="1786"
      > </a
      ><a name="1787" href="Basics0.html#394" class="InductiveConstructor"
      >zero</a
      ><a name="1791"
      > </a
      ><a name="1792" class="Symbol"
      >()</a
      ><a name="1794"
      >
</a
      ><a name="1795" href="Basics0.html#1635" class="Function"
      >double-injective</a
      ><a name="1811"
      > </a
      ><a name="1812" class="Symbol"
      >(</a
      ><a name="1813" href="Basics0.html#405" class="InductiveConstructor"
      >suc</a
      ><a name="1816"
      > </a
      ><a name="1817" href="Basics0.html#1817" class="Bound"
      >m</a
      ><a name="1818" class="Symbol"
      >)</a
      ><a name="1819"
      > </a
      ><a name="1820" class="Symbol"
      >(</a
      ><a name="1821" href="Basics0.html#405" class="InductiveConstructor"
      >suc</a
      ><a name="1824"
      > </a
      ><a name="1825" href="Basics0.html#1825" class="Bound"
      >n</a
      ><a name="1826" class="Symbol"
      >)</a
      ><a name="1827"
      > </a
      ><a name="1828" href="Basics0.html#1828" class="Bound"
      >r</a
      ><a name="1829"
      > </a
      ><a name="1830" class="Symbol"
      >=</a
      ><a name="1831"
      >
   </a
      ><a name="1835" href="Basics0.html#468" class="Function"
      >congruent</a
      ><a name="1844"
      > </a
      ><a name="1845" class="Symbol"
      >(</a
      ><a name="1846" href="Basics0.html#1635" class="Function"
      >double-injective</a
      ><a name="1862"
      > </a
      ><a name="1863" href="Basics0.html#1817" class="Bound"
      >m</a
      ><a name="1864"
      > </a
      ><a name="1865" href="Basics0.html#1825" class="Bound"
      >n</a
      ><a name="1866"
      > </a
      ><a name="1867" class="Symbol"
      >(</a
      ><a name="1868" href="Basics0.html#535" class="Function"
      >injective</a
      ><a name="1877"
      > </a
      ><a name="1878" class="Symbol"
      >(</a
      ><a name="1879" href="Basics0.html#535" class="Function"
      >injective</a
      ><a name="1888"
      > </a
      ><a name="1889" href="Basics0.html#1828" class="Bound"
      >r</a
      ><a name="1890" class="Symbol"
      >)))</a
      >
{% endraw %}</pre>

In Coq, the inductive proof for `double-injective`
is sensitive to how one inducts on `m` and `n`. In Agda, that aspect
is straightforward. However, Agda requires helper functions for
injection and congruence which are not required in Coq.

I can remove the use of `congruent` by rewriting with its argument.
Is there an easy way to remove the two uses of `injective`?
