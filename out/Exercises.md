---
title     : "Exercises: Exercises"
layout    : page
permalink : /Exercises
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
      ><a name="122" href="https://agda.github.io/agda-stdlib/Data.Nat.html#1" class="Module"
      >Data.Nat</a
      ><a name="130"
      > </a
      ><a name="131" class="Keyword"
      >using</a
      ><a name="136"
      > </a
      ><a name="137" class="Symbol"
      >(</a
      ><a name="138" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#97" class="Datatype"
      >&#8469;</a
      ><a name="139" class="Symbol"
      >;</a
      ><a name="140"
      > </a
      ><a name="141" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor"
      >suc</a
      ><a name="144" class="Symbol"
      >;</a
      ><a name="145"
      > </a
      ><a name="146" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#115" class="InductiveConstructor"
      >zero</a
      ><a name="150" class="Symbol"
      >;</a
      ><a name="151"
      > </a
      ><a name="152" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator"
      >_+_</a
      ><a name="155" class="Symbol"
      >;</a
      ><a name="156"
      > </a
      ><a name="157" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#433" class="Primitive Operator"
      >_*_</a
      ><a name="160" class="Symbol"
      >)</a
      ><a name="161"
      >
</a
      ><a name="162" class="Keyword"
      >open</a
      ><a name="166"
      > </a
      ><a name="167" class="Keyword"
      >import</a
      ><a name="173"
      > </a
      ><a name="174" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#1" class="Module"
      >Relation.Binary.PropositionalEquality</a
      ><a name="211"
      > </a
      ><a name="212" class="Keyword"
      >using</a
      ><a name="217"
      > </a
      ><a name="218" class="Symbol"
      >(</a
      ><a name="219" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >_&#8801;_</a
      ><a name="222" class="Symbol"
      >;</a
      ><a name="223"
      > </a
      ><a name="224" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="228" class="Symbol"
      >;</a
      ><a name="229"
      > </a
      ><a name="230" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.Core.html#565" class="Function"
      >sym</a
      ><a name="233" class="Symbol"
      >)</a
      >
{% endraw %}</pre>

## Exercises

<pre class="Agda">{% raw %}
<a name="274" href="Exercises.html#274" class="Function Operator"
      >_&#8760;_</a
      ><a name="277"
      > </a
      ><a name="278" class="Symbol"
      >:</a
      ><a name="279"
      > </a
      ><a name="280" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#97" class="Datatype"
      >&#8469;</a
      ><a name="281"
      > </a
      ><a name="282" class="Symbol"
      >&#8594;</a
      ><a name="283"
      > </a
      ><a name="284" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#97" class="Datatype"
      >&#8469;</a
      ><a name="285"
      > </a
      ><a name="286" class="Symbol"
      >&#8594;</a
      ><a name="287"
      > </a
      ><a name="288" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#97" class="Datatype"
      >&#8469;</a
      ><a name="289"
      >
</a
      ><a name="290" href="Exercises.html#290" class="Bound"
      >m</a
      ><a name="291"
      >       </a
      ><a name="298" href="Exercises.html#274" class="Function Operator"
      >&#8760;</a
      ><a name="299"
      > </a
      ><a name="300" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#115" class="InductiveConstructor"
      >zero</a
      ><a name="304"
      >     </a
      ><a name="309" class="Symbol"
      >=</a
      ><a name="310"
      >  </a
      ><a name="312" href="Exercises.html#290" class="Bound"
      >m</a
      ><a name="313"
      >         </a
      ><a name="322" class="Comment"
      >-- (vii)</a
      ><a name="330"
      >
</a
      ><a name="331" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#115" class="InductiveConstructor"
      >zero</a
      ><a name="335"
      >    </a
      ><a name="339" href="Exercises.html#274" class="Function Operator"
      >&#8760;</a
      ><a name="340"
      > </a
      ><a name="341" class="Symbol"
      >(</a
      ><a name="342" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor"
      >suc</a
      ><a name="345"
      > </a
      ><a name="346" href="Exercises.html#346" class="Bound"
      >n</a
      ><a name="347" class="Symbol"
      >)</a
      ><a name="348"
      >  </a
      ><a name="350" class="Symbol"
      >=</a
      ><a name="351"
      >  </a
      ><a name="353" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#115" class="InductiveConstructor"
      >zero</a
      ><a name="357"
      >      </a
      ><a name="363" class="Comment"
      >-- (viii)</a
      ><a name="372"
      >
</a
      ><a name="373" class="Symbol"
      >(</a
      ><a name="374" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor"
      >suc</a
      ><a name="377"
      > </a
      ><a name="378" href="Exercises.html#378" class="Bound"
      >m</a
      ><a name="379" class="Symbol"
      >)</a
      ><a name="380"
      > </a
      ><a name="381" href="Exercises.html#274" class="Function Operator"
      >&#8760;</a
      ><a name="382"
      > </a
      ><a name="383" class="Symbol"
      >(</a
      ><a name="384" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor"
      >suc</a
      ><a name="387"
      > </a
      ><a name="388" href="Exercises.html#388" class="Bound"
      >n</a
      ><a name="389" class="Symbol"
      >)</a
      ><a name="390"
      >  </a
      ><a name="392" class="Symbol"
      >=</a
      ><a name="393"
      >  </a
      ><a name="395" href="Exercises.html#378" class="Bound"
      >m</a
      ><a name="396"
      > </a
      ><a name="397" href="Exercises.html#274" class="Function Operator"
      >&#8760;</a
      ><a name="398"
      > </a
      ><a name="399" href="Exercises.html#388" class="Bound"
      >n</a
      ><a name="400"
      >     </a
      ><a name="405" class="Comment"
      >-- (ix)</a
      ><a name="412"
      >

</a
      ><a name="414" class="Keyword"
      >infixl</a
      ><a name="420"
      > </a
      ><a name="421" class="Number"
      >6</a
      ><a name="422"
      > </a
      ><a name="423" href="Exercises.html#274" class="Function Operator"
      >_&#8760;_</a
      ><a name="426"
      >

</a
      ><a name="428" href="Exercises.html#428" class="Function"
      >assoc+</a
      ><a name="434"
      > </a
      ><a name="435" class="Symbol"
      >:</a
      ><a name="436"
      > </a
      ><a name="437" class="Symbol"
      >&#8704;</a
      ><a name="438"
      > </a
      ><a name="439" class="Symbol"
      >(</a
      ><a name="440" href="Exercises.html#440" class="Bound"
      >m</a
      ><a name="441"
      > </a
      ><a name="442" href="Exercises.html#442" class="Bound"
      >n</a
      ><a name="443"
      > </a
      ><a name="444" href="Exercises.html#444" class="Bound"
      >p</a
      ><a name="445"
      > </a
      ><a name="446" class="Symbol"
      >:</a
      ><a name="447"
      > </a
      ><a name="448" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#97" class="Datatype"
      >&#8469;</a
      ><a name="449" class="Symbol"
      >)</a
      ><a name="450"
      > </a
      ><a name="451" class="Symbol"
      >&#8594;</a
      ><a name="452"
      > </a
      ><a name="453" class="Symbol"
      >(</a
      ><a name="454" href="Exercises.html#440" class="Bound"
      >m</a
      ><a name="455"
      > </a
      ><a name="456" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator"
      >+</a
      ><a name="457"
      > </a
      ><a name="458" href="Exercises.html#442" class="Bound"
      >n</a
      ><a name="459" class="Symbol"
      >)</a
      ><a name="460"
      > </a
      ><a name="461" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator"
      >+</a
      ><a name="462"
      > </a
      ><a name="463" href="Exercises.html#444" class="Bound"
      >p</a
      ><a name="464"
      > </a
      ><a name="465" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="466"
      > </a
      ><a name="467" href="Exercises.html#440" class="Bound"
      >m</a
      ><a name="468"
      > </a
      ><a name="469" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator"
      >+</a
      ><a name="470"
      > </a
      ><a name="471" class="Symbol"
      >(</a
      ><a name="472" href="Exercises.html#442" class="Bound"
      >n</a
      ><a name="473"
      > </a
      ><a name="474" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator"
      >+</a
      ><a name="475"
      > </a
      ><a name="476" href="Exercises.html#444" class="Bound"
      >p</a
      ><a name="477" class="Symbol"
      >)</a
      ><a name="478"
      >
</a
      ><a name="479" href="Exercises.html#428" class="Function"
      >assoc+</a
      ><a name="485"
      > </a
      ><a name="486" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#115" class="InductiveConstructor"
      >zero</a
      ><a name="490"
      > </a
      ><a name="491" href="Exercises.html#491" class="Bound"
      >n</a
      ><a name="492"
      > </a
      ><a name="493" href="Exercises.html#493" class="Bound"
      >p</a
      ><a name="494"
      > </a
      ><a name="495" class="Symbol"
      >=</a
      ><a name="496"
      > </a
      ><a name="497" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="501"
      >
</a
      ><a name="502" href="Exercises.html#428" class="Function"
      >assoc+</a
      ><a name="508"
      > </a
      ><a name="509" class="Symbol"
      >(</a
      ><a name="510" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor"
      >suc</a
      ><a name="513"
      > </a
      ><a name="514" href="Exercises.html#514" class="Bound"
      >m</a
      ><a name="515" class="Symbol"
      >)</a
      ><a name="516"
      > </a
      ><a name="517" href="Exercises.html#517" class="Bound"
      >n</a
      ><a name="518"
      > </a
      ><a name="519" href="Exercises.html#519" class="Bound"
      >p</a
      ><a name="520"
      > </a
      ><a name="521" class="Keyword"
      >rewrite</a
      ><a name="528"
      > </a
      ><a name="529" href="Exercises.html#428" class="Function"
      >assoc+</a
      ><a name="535"
      > </a
      ><a name="536" href="Exercises.html#514" class="Bound"
      >m</a
      ><a name="537"
      > </a
      ><a name="538" href="Exercises.html#517" class="Bound"
      >n</a
      ><a name="539"
      > </a
      ><a name="540" href="Exercises.html#519" class="Bound"
      >p</a
      ><a name="541"
      > </a
      ><a name="542" class="Symbol"
      >=</a
      ><a name="543"
      > </a
      ><a name="544" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="548"
      >

</a
      ><a name="550" href="Exercises.html#550" class="Function"
      >com+zero</a
      ><a name="558"
      > </a
      ><a name="559" class="Symbol"
      >:</a
      ><a name="560"
      > </a
      ><a name="561" class="Symbol"
      >&#8704;</a
      ><a name="562"
      > </a
      ><a name="563" class="Symbol"
      >(</a
      ><a name="564" href="Exercises.html#564" class="Bound"
      >n</a
      ><a name="565"
      > </a
      ><a name="566" class="Symbol"
      >:</a
      ><a name="567"
      > </a
      ><a name="568" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#97" class="Datatype"
      >&#8469;</a
      ><a name="569" class="Symbol"
      >)</a
      ><a name="570"
      > </a
      ><a name="571" class="Symbol"
      >&#8594;</a
      ><a name="572"
      > </a
      ><a name="573" href="Exercises.html#564" class="Bound"
      >n</a
      ><a name="574"
      > </a
      ><a name="575" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator"
      >+</a
      ><a name="576"
      > </a
      ><a name="577" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#115" class="InductiveConstructor"
      >zero</a
      ><a name="581"
      > </a
      ><a name="582" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="583"
      > </a
      ><a name="584" href="Exercises.html#564" class="Bound"
      >n</a
      ><a name="585"
      >
</a
      ><a name="586" href="Exercises.html#550" class="Function"
      >com+zero</a
      ><a name="594"
      > </a
      ><a name="595" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#115" class="InductiveConstructor"
      >zero</a
      ><a name="599"
      > </a
      ><a name="600" class="Symbol"
      >=</a
      ><a name="601"
      > </a
      ><a name="602" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="606"
      >
</a
      ><a name="607" href="Exercises.html#550" class="Function"
      >com+zero</a
      ><a name="615"
      > </a
      ><a name="616" class="Symbol"
      >(</a
      ><a name="617" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor"
      >suc</a
      ><a name="620"
      > </a
      ><a name="621" href="Exercises.html#621" class="Bound"
      >n</a
      ><a name="622" class="Symbol"
      >)</a
      ><a name="623"
      > </a
      ><a name="624" class="Keyword"
      >rewrite</a
      ><a name="631"
      > </a
      ><a name="632" href="Exercises.html#550" class="Function"
      >com+zero</a
      ><a name="640"
      > </a
      ><a name="641" href="Exercises.html#621" class="Bound"
      >n</a
      ><a name="642"
      > </a
      ><a name="643" class="Symbol"
      >=</a
      ><a name="644"
      > </a
      ><a name="645" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="649"
      >

</a
      ><a name="651" href="Exercises.html#651" class="Function"
      >com+suc</a
      ><a name="658"
      > </a
      ><a name="659" class="Symbol"
      >:</a
      ><a name="660"
      > </a
      ><a name="661" class="Symbol"
      >&#8704;</a
      ><a name="662"
      > </a
      ><a name="663" class="Symbol"
      >(</a
      ><a name="664" href="Exercises.html#664" class="Bound"
      >m</a
      ><a name="665"
      > </a
      ><a name="666" href="Exercises.html#666" class="Bound"
      >n</a
      ><a name="667"
      > </a
      ><a name="668" class="Symbol"
      >:</a
      ><a name="669"
      > </a
      ><a name="670" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#97" class="Datatype"
      >&#8469;</a
      ><a name="671" class="Symbol"
      >)</a
      ><a name="672"
      > </a
      ><a name="673" class="Symbol"
      >&#8594;</a
      ><a name="674"
      > </a
      ><a name="675" href="Exercises.html#666" class="Bound"
      >n</a
      ><a name="676"
      > </a
      ><a name="677" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator"
      >+</a
      ><a name="678"
      > </a
      ><a name="679" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor"
      >suc</a
      ><a name="682"
      > </a
      ><a name="683" href="Exercises.html#664" class="Bound"
      >m</a
      ><a name="684"
      > </a
      ><a name="685" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="686"
      > </a
      ><a name="687" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor"
      >suc</a
      ><a name="690"
      > </a
      ><a name="691" class="Symbol"
      >(</a
      ><a name="692" href="Exercises.html#666" class="Bound"
      >n</a
      ><a name="693"
      > </a
      ><a name="694" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator"
      >+</a
      ><a name="695"
      > </a
      ><a name="696" href="Exercises.html#664" class="Bound"
      >m</a
      ><a name="697" class="Symbol"
      >)</a
      ><a name="698"
      >
</a
      ><a name="699" href="Exercises.html#651" class="Function"
      >com+suc</a
      ><a name="706"
      > </a
      ><a name="707" href="Exercises.html#707" class="Bound"
      >m</a
      ><a name="708"
      > </a
      ><a name="709" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#115" class="InductiveConstructor"
      >zero</a
      ><a name="713"
      > </a
      ><a name="714" class="Symbol"
      >=</a
      ><a name="715"
      > </a
      ><a name="716" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="720"
      >
</a
      ><a name="721" href="Exercises.html#651" class="Function"
      >com+suc</a
      ><a name="728"
      > </a
      ><a name="729" href="Exercises.html#729" class="Bound"
      >m</a
      ><a name="730"
      > </a
      ><a name="731" class="Symbol"
      >(</a
      ><a name="732" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor"
      >suc</a
      ><a name="735"
      > </a
      ><a name="736" href="Exercises.html#736" class="Bound"
      >n</a
      ><a name="737" class="Symbol"
      >)</a
      ><a name="738"
      > </a
      ><a name="739" class="Keyword"
      >rewrite</a
      ><a name="746"
      > </a
      ><a name="747" href="Exercises.html#651" class="Function"
      >com+suc</a
      ><a name="754"
      > </a
      ><a name="755" href="Exercises.html#729" class="Bound"
      >m</a
      ><a name="756"
      > </a
      ><a name="757" href="Exercises.html#736" class="Bound"
      >n</a
      ><a name="758"
      > </a
      ><a name="759" class="Symbol"
      >=</a
      ><a name="760"
      > </a
      ><a name="761" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="765"
      >

</a
      ><a name="767" href="Exercises.html#767" class="Function"
      >com+</a
      ><a name="771"
      > </a
      ><a name="772" class="Symbol"
      >:</a
      ><a name="773"
      > </a
      ><a name="774" class="Symbol"
      >&#8704;</a
      ><a name="775"
      > </a
      ><a name="776" class="Symbol"
      >(</a
      ><a name="777" href="Exercises.html#777" class="Bound"
      >m</a
      ><a name="778"
      > </a
      ><a name="779" href="Exercises.html#779" class="Bound"
      >n</a
      ><a name="780"
      > </a
      ><a name="781" class="Symbol"
      >:</a
      ><a name="782"
      > </a
      ><a name="783" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#97" class="Datatype"
      >&#8469;</a
      ><a name="784" class="Symbol"
      >)</a
      ><a name="785"
      > </a
      ><a name="786" class="Symbol"
      >&#8594;</a
      ><a name="787"
      > </a
      ><a name="788" href="Exercises.html#777" class="Bound"
      >m</a
      ><a name="789"
      > </a
      ><a name="790" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator"
      >+</a
      ><a name="791"
      > </a
      ><a name="792" href="Exercises.html#779" class="Bound"
      >n</a
      ><a name="793"
      > </a
      ><a name="794" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="795"
      > </a
      ><a name="796" href="Exercises.html#779" class="Bound"
      >n</a
      ><a name="797"
      > </a
      ><a name="798" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator"
      >+</a
      ><a name="799"
      > </a
      ><a name="800" href="Exercises.html#777" class="Bound"
      >m</a
      ><a name="801"
      >
</a
      ><a name="802" href="Exercises.html#767" class="Function"
      >com+</a
      ><a name="806"
      > </a
      ><a name="807" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#115" class="InductiveConstructor"
      >zero</a
      ><a name="811"
      > </a
      ><a name="812" href="Exercises.html#812" class="Bound"
      >n</a
      ><a name="813"
      > </a
      ><a name="814" class="Keyword"
      >rewrite</a
      ><a name="821"
      > </a
      ><a name="822" href="Exercises.html#550" class="Function"
      >com+zero</a
      ><a name="830"
      > </a
      ><a name="831" href="Exercises.html#812" class="Bound"
      >n</a
      ><a name="832"
      > </a
      ><a name="833" class="Symbol"
      >=</a
      ><a name="834"
      > </a
      ><a name="835" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="839"
      >
</a
      ><a name="840" href="Exercises.html#767" class="Function"
      >com+</a
      ><a name="844"
      > </a
      ><a name="845" class="Symbol"
      >(</a
      ><a name="846" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor"
      >suc</a
      ><a name="849"
      > </a
      ><a name="850" href="Exercises.html#850" class="Bound"
      >m</a
      ><a name="851" class="Symbol"
      >)</a
      ><a name="852"
      > </a
      ><a name="853" href="Exercises.html#853" class="Bound"
      >n</a
      ><a name="854"
      > </a
      ><a name="855" class="Keyword"
      >rewrite</a
      ><a name="862"
      > </a
      ><a name="863" href="Exercises.html#651" class="Function"
      >com+suc</a
      ><a name="870"
      > </a
      ><a name="871" href="Exercises.html#850" class="Bound"
      >m</a
      ><a name="872"
      > </a
      ><a name="873" href="Exercises.html#853" class="Bound"
      >n</a
      ><a name="874"
      > </a
      ><a name="875" class="Symbol"
      >|</a
      ><a name="876"
      > </a
      ><a name="877" href="Exercises.html#767" class="Function"
      >com+</a
      ><a name="881"
      > </a
      ><a name="882" href="Exercises.html#850" class="Bound"
      >m</a
      ><a name="883"
      > </a
      ><a name="884" href="Exercises.html#853" class="Bound"
      >n</a
      ><a name="885"
      > </a
      ><a name="886" class="Symbol"
      >=</a
      ><a name="887"
      > </a
      ><a name="888" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="892"
      >

</a
      ><a name="894" href="Exercises.html#894" class="Function"
      >dist*+</a
      ><a name="900"
      > </a
      ><a name="901" class="Symbol"
      >:</a
      ><a name="902"
      > </a
      ><a name="903" class="Symbol"
      >&#8704;</a
      ><a name="904"
      > </a
      ><a name="905" class="Symbol"
      >(</a
      ><a name="906" href="Exercises.html#906" class="Bound"
      >m</a
      ><a name="907"
      > </a
      ><a name="908" href="Exercises.html#908" class="Bound"
      >n</a
      ><a name="909"
      > </a
      ><a name="910" href="Exercises.html#910" class="Bound"
      >p</a
      ><a name="911"
      > </a
      ><a name="912" class="Symbol"
      >:</a
      ><a name="913"
      > </a
      ><a name="914" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#97" class="Datatype"
      >&#8469;</a
      ><a name="915" class="Symbol"
      >)</a
      ><a name="916"
      > </a
      ><a name="917" class="Symbol"
      >&#8594;</a
      ><a name="918"
      > </a
      ><a name="919" class="Symbol"
      >(</a
      ><a name="920" href="Exercises.html#906" class="Bound"
      >m</a
      ><a name="921"
      > </a
      ><a name="922" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator"
      >+</a
      ><a name="923"
      > </a
      ><a name="924" href="Exercises.html#908" class="Bound"
      >n</a
      ><a name="925" class="Symbol"
      >)</a
      ><a name="926"
      > </a
      ><a name="927" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#433" class="Primitive Operator"
      >*</a
      ><a name="928"
      > </a
      ><a name="929" href="Exercises.html#910" class="Bound"
      >p</a
      ><a name="930"
      > </a
      ><a name="931" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="932"
      > </a
      ><a name="933" href="Exercises.html#906" class="Bound"
      >m</a
      ><a name="934"
      > </a
      ><a name="935" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#433" class="Primitive Operator"
      >*</a
      ><a name="936"
      > </a
      ><a name="937" href="Exercises.html#910" class="Bound"
      >p</a
      ><a name="938"
      > </a
      ><a name="939" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator"
      >+</a
      ><a name="940"
      > </a
      ><a name="941" href="Exercises.html#908" class="Bound"
      >n</a
      ><a name="942"
      > </a
      ><a name="943" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#433" class="Primitive Operator"
      >*</a
      ><a name="944"
      > </a
      ><a name="945" href="Exercises.html#910" class="Bound"
      >p</a
      ><a name="946"
      >
</a
      ><a name="947" href="Exercises.html#894" class="Function"
      >dist*+</a
      ><a name="953"
      > </a
      ><a name="954" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#115" class="InductiveConstructor"
      >zero</a
      ><a name="958"
      > </a
      ><a name="959" href="Exercises.html#959" class="Bound"
      >n</a
      ><a name="960"
      > </a
      ><a name="961" href="Exercises.html#961" class="Bound"
      >p</a
      ><a name="962"
      > </a
      ><a name="963" class="Symbol"
      >=</a
      ><a name="964"
      > </a
      ><a name="965" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="969"
      >
</a
      ><a name="970" href="Exercises.html#894" class="Function"
      >dist*+</a
      ><a name="976"
      > </a
      ><a name="977" class="Symbol"
      >(</a
      ><a name="978" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor"
      >suc</a
      ><a name="981"
      > </a
      ><a name="982" href="Exercises.html#982" class="Bound"
      >m</a
      ><a name="983" class="Symbol"
      >)</a
      ><a name="984"
      > </a
      ><a name="985" href="Exercises.html#985" class="Bound"
      >n</a
      ><a name="986"
      > </a
      ><a name="987" href="Exercises.html#987" class="Bound"
      >p</a
      ><a name="988"
      > </a
      ><a name="989" class="Keyword"
      >rewrite</a
      ><a name="996"
      > </a
      ><a name="997" href="Exercises.html#894" class="Function"
      >dist*+</a
      ><a name="1003"
      > </a
      ><a name="1004" href="Exercises.html#982" class="Bound"
      >m</a
      ><a name="1005"
      > </a
      ><a name="1006" href="Exercises.html#985" class="Bound"
      >n</a
      ><a name="1007"
      > </a
      ><a name="1008" href="Exercises.html#987" class="Bound"
      >p</a
      ><a name="1009"
      > </a
      ><a name="1010" class="Symbol"
      >|</a
      ><a name="1011"
      > </a
      ><a name="1012" href="Exercises.html#428" class="Function"
      >assoc+</a
      ><a name="1018"
      > </a
      ><a name="1019" href="Exercises.html#987" class="Bound"
      >p</a
      ><a name="1020"
      > </a
      ><a name="1021" class="Symbol"
      >(</a
      ><a name="1022" href="Exercises.html#982" class="Bound"
      >m</a
      ><a name="1023"
      > </a
      ><a name="1024" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#433" class="Primitive Operator"
      >*</a
      ><a name="1025"
      > </a
      ><a name="1026" href="Exercises.html#987" class="Bound"
      >p</a
      ><a name="1027" class="Symbol"
      >)</a
      ><a name="1028"
      > </a
      ><a name="1029" class="Symbol"
      >(</a
      ><a name="1030" href="Exercises.html#985" class="Bound"
      >n</a
      ><a name="1031"
      > </a
      ><a name="1032" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#433" class="Primitive Operator"
      >*</a
      ><a name="1033"
      > </a
      ><a name="1034" href="Exercises.html#987" class="Bound"
      >p</a
      ><a name="1035" class="Symbol"
      >)</a
      ><a name="1036"
      > </a
      ><a name="1037" class="Symbol"
      >=</a
      ><a name="1038"
      > </a
      ><a name="1039" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="1043"
      >

</a
      ><a name="1045" href="Exercises.html#1045" class="Function"
      >assoc*</a
      ><a name="1051"
      > </a
      ><a name="1052" class="Symbol"
      >:</a
      ><a name="1053"
      > </a
      ><a name="1054" class="Symbol"
      >&#8704;</a
      ><a name="1055"
      > </a
      ><a name="1056" class="Symbol"
      >(</a
      ><a name="1057" href="Exercises.html#1057" class="Bound"
      >m</a
      ><a name="1058"
      > </a
      ><a name="1059" href="Exercises.html#1059" class="Bound"
      >n</a
      ><a name="1060"
      > </a
      ><a name="1061" href="Exercises.html#1061" class="Bound"
      >p</a
      ><a name="1062"
      > </a
      ><a name="1063" class="Symbol"
      >:</a
      ><a name="1064"
      > </a
      ><a name="1065" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#97" class="Datatype"
      >&#8469;</a
      ><a name="1066" class="Symbol"
      >)</a
      ><a name="1067"
      > </a
      ><a name="1068" class="Symbol"
      >&#8594;</a
      ><a name="1069"
      > </a
      ><a name="1070" class="Symbol"
      >(</a
      ><a name="1071" href="Exercises.html#1057" class="Bound"
      >m</a
      ><a name="1072"
      > </a
      ><a name="1073" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#433" class="Primitive Operator"
      >*</a
      ><a name="1074"
      > </a
      ><a name="1075" href="Exercises.html#1059" class="Bound"
      >n</a
      ><a name="1076" class="Symbol"
      >)</a
      ><a name="1077"
      > </a
      ><a name="1078" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#433" class="Primitive Operator"
      >*</a
      ><a name="1079"
      > </a
      ><a name="1080" href="Exercises.html#1061" class="Bound"
      >p</a
      ><a name="1081"
      > </a
      ><a name="1082" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="1083"
      > </a
      ><a name="1084" href="Exercises.html#1057" class="Bound"
      >m</a
      ><a name="1085"
      > </a
      ><a name="1086" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#433" class="Primitive Operator"
      >*</a
      ><a name="1087"
      > </a
      ><a name="1088" class="Symbol"
      >(</a
      ><a name="1089" href="Exercises.html#1059" class="Bound"
      >n</a
      ><a name="1090"
      > </a
      ><a name="1091" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#433" class="Primitive Operator"
      >*</a
      ><a name="1092"
      > </a
      ><a name="1093" href="Exercises.html#1061" class="Bound"
      >p</a
      ><a name="1094" class="Symbol"
      >)</a
      ><a name="1095"
      >
</a
      ><a name="1096" href="Exercises.html#1045" class="Function"
      >assoc*</a
      ><a name="1102"
      > </a
      ><a name="1103" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#115" class="InductiveConstructor"
      >zero</a
      ><a name="1107"
      > </a
      ><a name="1108" href="Exercises.html#1108" class="Bound"
      >n</a
      ><a name="1109"
      > </a
      ><a name="1110" href="Exercises.html#1110" class="Bound"
      >p</a
      ><a name="1111"
      > </a
      ><a name="1112" class="Symbol"
      >=</a
      ><a name="1113"
      > </a
      ><a name="1114" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="1118"
      >
</a
      ><a name="1119" href="Exercises.html#1045" class="Function"
      >assoc*</a
      ><a name="1125"
      > </a
      ><a name="1126" class="Symbol"
      >(</a
      ><a name="1127" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor"
      >suc</a
      ><a name="1130"
      > </a
      ><a name="1131" href="Exercises.html#1131" class="Bound"
      >m</a
      ><a name="1132" class="Symbol"
      >)</a
      ><a name="1133"
      > </a
      ><a name="1134" href="Exercises.html#1134" class="Bound"
      >n</a
      ><a name="1135"
      > </a
      ><a name="1136" href="Exercises.html#1136" class="Bound"
      >p</a
      ><a name="1137"
      > </a
      ><a name="1138" class="Keyword"
      >rewrite</a
      ><a name="1145"
      > </a
      ><a name="1146" href="Exercises.html#894" class="Function"
      >dist*+</a
      ><a name="1152"
      > </a
      ><a name="1153" href="Exercises.html#1134" class="Bound"
      >n</a
      ><a name="1154"
      > </a
      ><a name="1155" class="Symbol"
      >(</a
      ><a name="1156" href="Exercises.html#1131" class="Bound"
      >m</a
      ><a name="1157"
      > </a
      ><a name="1158" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#433" class="Primitive Operator"
      >*</a
      ><a name="1159"
      > </a
      ><a name="1160" href="Exercises.html#1134" class="Bound"
      >n</a
      ><a name="1161" class="Symbol"
      >)</a
      ><a name="1162"
      > </a
      ><a name="1163" href="Exercises.html#1136" class="Bound"
      >p</a
      ><a name="1164"
      > </a
      ><a name="1165" class="Symbol"
      >|</a
      ><a name="1166"
      > </a
      ><a name="1167" href="Exercises.html#1045" class="Function"
      >assoc*</a
      ><a name="1173"
      > </a
      ><a name="1174" href="Exercises.html#1131" class="Bound"
      >m</a
      ><a name="1175"
      > </a
      ><a name="1176" href="Exercises.html#1134" class="Bound"
      >n</a
      ><a name="1177"
      > </a
      ><a name="1178" href="Exercises.html#1136" class="Bound"
      >p</a
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
      ><a name="1188" href="Exercises.html#1188" class="Function"
      >com*zero</a
      ><a name="1196"
      > </a
      ><a name="1197" class="Symbol"
      >:</a
      ><a name="1198"
      > </a
      ><a name="1199" class="Symbol"
      >&#8704;</a
      ><a name="1200"
      > </a
      ><a name="1201" class="Symbol"
      >(</a
      ><a name="1202" href="Exercises.html#1202" class="Bound"
      >n</a
      ><a name="1203"
      > </a
      ><a name="1204" class="Symbol"
      >:</a
      ><a name="1205"
      > </a
      ><a name="1206" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#97" class="Datatype"
      >&#8469;</a
      ><a name="1207" class="Symbol"
      >)</a
      ><a name="1208"
      > </a
      ><a name="1209" class="Symbol"
      >&#8594;</a
      ><a name="1210"
      > </a
      ><a name="1211" href="Exercises.html#1202" class="Bound"
      >n</a
      ><a name="1212"
      > </a
      ><a name="1213" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#433" class="Primitive Operator"
      >*</a
      ><a name="1214"
      > </a
      ><a name="1215" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#115" class="InductiveConstructor"
      >zero</a
      ><a name="1219"
      > </a
      ><a name="1220" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="1221"
      > </a
      ><a name="1222" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#115" class="InductiveConstructor"
      >zero</a
      ><a name="1226"
      >
</a
      ><a name="1227" href="Exercises.html#1188" class="Function"
      >com*zero</a
      ><a name="1235"
      > </a
      ><a name="1236" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#115" class="InductiveConstructor"
      >zero</a
      ><a name="1240"
      > </a
      ><a name="1241" class="Symbol"
      >=</a
      ><a name="1242"
      > </a
      ><a name="1243" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="1247"
      >
</a
      ><a name="1248" href="Exercises.html#1188" class="Function"
      >com*zero</a
      ><a name="1256"
      > </a
      ><a name="1257" class="Symbol"
      >(</a
      ><a name="1258" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor"
      >suc</a
      ><a name="1261"
      > </a
      ><a name="1262" href="Exercises.html#1262" class="Bound"
      >n</a
      ><a name="1263" class="Symbol"
      >)</a
      ><a name="1264"
      > </a
      ><a name="1265" class="Keyword"
      >rewrite</a
      ><a name="1272"
      > </a
      ><a name="1273" href="Exercises.html#1188" class="Function"
      >com*zero</a
      ><a name="1281"
      > </a
      ><a name="1282" href="Exercises.html#1262" class="Bound"
      >n</a
      ><a name="1283"
      > </a
      ><a name="1284" class="Symbol"
      >=</a
      ><a name="1285"
      > </a
      ><a name="1286" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="1290"
      >

</a
      ><a name="1292" href="Exercises.html#1292" class="Function"
      >swap+</a
      ><a name="1297"
      > </a
      ><a name="1298" class="Symbol"
      >:</a
      ><a name="1299"
      > </a
      ><a name="1300" class="Symbol"
      >&#8704;</a
      ><a name="1301"
      > </a
      ><a name="1302" class="Symbol"
      >(</a
      ><a name="1303" href="Exercises.html#1303" class="Bound"
      >m</a
      ><a name="1304"
      > </a
      ><a name="1305" href="Exercises.html#1305" class="Bound"
      >n</a
      ><a name="1306"
      > </a
      ><a name="1307" href="Exercises.html#1307" class="Bound"
      >p</a
      ><a name="1308"
      > </a
      ><a name="1309" class="Symbol"
      >:</a
      ><a name="1310"
      > </a
      ><a name="1311" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#97" class="Datatype"
      >&#8469;</a
      ><a name="1312" class="Symbol"
      >)</a
      ><a name="1313"
      > </a
      ><a name="1314" class="Symbol"
      >&#8594;</a
      ><a name="1315"
      > </a
      ><a name="1316" href="Exercises.html#1303" class="Bound"
      >m</a
      ><a name="1317"
      > </a
      ><a name="1318" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator"
      >+</a
      ><a name="1319"
      > </a
      ><a name="1320" class="Symbol"
      >(</a
      ><a name="1321" href="Exercises.html#1305" class="Bound"
      >n</a
      ><a name="1322"
      > </a
      ><a name="1323" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator"
      >+</a
      ><a name="1324"
      > </a
      ><a name="1325" href="Exercises.html#1307" class="Bound"
      >p</a
      ><a name="1326" class="Symbol"
      >)</a
      ><a name="1327"
      > </a
      ><a name="1328" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="1329"
      > </a
      ><a name="1330" href="Exercises.html#1305" class="Bound"
      >n</a
      ><a name="1331"
      > </a
      ><a name="1332" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator"
      >+</a
      ><a name="1333"
      > </a
      ><a name="1334" class="Symbol"
      >(</a
      ><a name="1335" href="Exercises.html#1303" class="Bound"
      >m</a
      ><a name="1336"
      > </a
      ><a name="1337" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator"
      >+</a
      ><a name="1338"
      > </a
      ><a name="1339" href="Exercises.html#1307" class="Bound"
      >p</a
      ><a name="1340" class="Symbol"
      >)</a
      ><a name="1341"
      >
</a
      ><a name="1342" href="Exercises.html#1292" class="Function"
      >swap+</a
      ><a name="1347"
      > </a
      ><a name="1348" href="Exercises.html#1348" class="Bound"
      >m</a
      ><a name="1349"
      > </a
      ><a name="1350" href="Exercises.html#1350" class="Bound"
      >n</a
      ><a name="1351"
      > </a
      ><a name="1352" href="Exercises.html#1352" class="Bound"
      >p</a
      ><a name="1353"
      > </a
      ><a name="1354" class="Keyword"
      >rewrite</a
      ><a name="1361"
      > </a
      ><a name="1362" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.Core.html#565" class="Function"
      >sym</a
      ><a name="1365"
      > </a
      ><a name="1366" class="Symbol"
      >(</a
      ><a name="1367" href="Exercises.html#428" class="Function"
      >assoc+</a
      ><a name="1373"
      > </a
      ><a name="1374" href="Exercises.html#1348" class="Bound"
      >m</a
      ><a name="1375"
      > </a
      ><a name="1376" href="Exercises.html#1350" class="Bound"
      >n</a
      ><a name="1377"
      > </a
      ><a name="1378" href="Exercises.html#1352" class="Bound"
      >p</a
      ><a name="1379" class="Symbol"
      >)</a
      ><a name="1380"
      > </a
      ><a name="1381" class="Symbol"
      >|</a
      ><a name="1382"
      > </a
      ><a name="1383" href="Exercises.html#767" class="Function"
      >com+</a
      ><a name="1387"
      > </a
      ><a name="1388" href="Exercises.html#1348" class="Bound"
      >m</a
      ><a name="1389"
      > </a
      ><a name="1390" href="Exercises.html#1350" class="Bound"
      >n</a
      ><a name="1391"
      > </a
      ><a name="1392" class="Symbol"
      >|</a
      ><a name="1393"
      > </a
      ><a name="1394" href="Exercises.html#428" class="Function"
      >assoc+</a
      ><a name="1400"
      > </a
      ><a name="1401" href="Exercises.html#1350" class="Bound"
      >n</a
      ><a name="1402"
      > </a
      ><a name="1403" href="Exercises.html#1348" class="Bound"
      >m</a
      ><a name="1404"
      > </a
      ><a name="1405" href="Exercises.html#1352" class="Bound"
      >p</a
      ><a name="1406"
      > </a
      ><a name="1407" class="Symbol"
      >=</a
      ><a name="1408"
      > </a
      ><a name="1409" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="1413"
      >

</a
      ><a name="1415" href="Exercises.html#1415" class="Function"
      >com*suc</a
      ><a name="1422"
      > </a
      ><a name="1423" class="Symbol"
      >:</a
      ><a name="1424"
      > </a
      ><a name="1425" class="Symbol"
      >&#8704;</a
      ><a name="1426"
      > </a
      ><a name="1427" class="Symbol"
      >(</a
      ><a name="1428" href="Exercises.html#1428" class="Bound"
      >m</a
      ><a name="1429"
      > </a
      ><a name="1430" href="Exercises.html#1430" class="Bound"
      >n</a
      ><a name="1431"
      > </a
      ><a name="1432" class="Symbol"
      >:</a
      ><a name="1433"
      > </a
      ><a name="1434" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#97" class="Datatype"
      >&#8469;</a
      ><a name="1435" class="Symbol"
      >)</a
      ><a name="1436"
      > </a
      ><a name="1437" class="Symbol"
      >&#8594;</a
      ><a name="1438"
      > </a
      ><a name="1439" href="Exercises.html#1430" class="Bound"
      >n</a
      ><a name="1440"
      > </a
      ><a name="1441" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#433" class="Primitive Operator"
      >*</a
      ><a name="1442"
      > </a
      ><a name="1443" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor"
      >suc</a
      ><a name="1446"
      > </a
      ><a name="1447" href="Exercises.html#1428" class="Bound"
      >m</a
      ><a name="1448"
      > </a
      ><a name="1449" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="1450"
      > </a
      ><a name="1451" href="Exercises.html#1430" class="Bound"
      >n</a
      ><a name="1452"
      > </a
      ><a name="1453" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator"
      >+</a
      ><a name="1454"
      > </a
      ><a name="1455" href="Exercises.html#1430" class="Bound"
      >n</a
      ><a name="1456"
      > </a
      ><a name="1457" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#433" class="Primitive Operator"
      >*</a
      ><a name="1458"
      > </a
      ><a name="1459" href="Exercises.html#1428" class="Bound"
      >m</a
      ><a name="1460"
      >
</a
      ><a name="1461" href="Exercises.html#1415" class="Function"
      >com*suc</a
      ><a name="1468"
      > </a
      ><a name="1469" href="Exercises.html#1469" class="Bound"
      >m</a
      ><a name="1470"
      > </a
      ><a name="1471" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#115" class="InductiveConstructor"
      >zero</a
      ><a name="1475"
      > </a
      ><a name="1476" class="Symbol"
      >=</a
      ><a name="1477"
      > </a
      ><a name="1478" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="1482"
      >
</a
      ><a name="1483" href="Exercises.html#1415" class="Function"
      >com*suc</a
      ><a name="1490"
      > </a
      ><a name="1491" href="Exercises.html#1491" class="Bound"
      >m</a
      ><a name="1492"
      > </a
      ><a name="1493" class="Symbol"
      >(</a
      ><a name="1494" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor"
      >suc</a
      ><a name="1497"
      > </a
      ><a name="1498" href="Exercises.html#1498" class="Bound"
      >n</a
      ><a name="1499" class="Symbol"
      >)</a
      ><a name="1500"
      > </a
      ><a name="1501" class="Keyword"
      >rewrite</a
      ><a name="1508"
      > </a
      ><a name="1509" href="Exercises.html#1415" class="Function"
      >com*suc</a
      ><a name="1516"
      > </a
      ><a name="1517" href="Exercises.html#1491" class="Bound"
      >m</a
      ><a name="1518"
      > </a
      ><a name="1519" href="Exercises.html#1498" class="Bound"
      >n</a
      ><a name="1520"
      > </a
      ><a name="1521" class="Symbol"
      >|</a
      ><a name="1522"
      > </a
      ><a name="1523" href="Exercises.html#1292" class="Function"
      >swap+</a
      ><a name="1528"
      > </a
      ><a name="1529" href="Exercises.html#1491" class="Bound"
      >m</a
      ><a name="1530"
      > </a
      ><a name="1531" href="Exercises.html#1498" class="Bound"
      >n</a
      ><a name="1532"
      > </a
      ><a name="1533" class="Symbol"
      >(</a
      ><a name="1534" href="Exercises.html#1498" class="Bound"
      >n</a
      ><a name="1535"
      > </a
      ><a name="1536" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#433" class="Primitive Operator"
      >*</a
      ><a name="1537"
      > </a
      ><a name="1538" href="Exercises.html#1491" class="Bound"
      >m</a
      ><a name="1539" class="Symbol"
      >)</a
      ><a name="1540"
      > </a
      ><a name="1541" class="Symbol"
      >=</a
      ><a name="1542"
      > </a
      ><a name="1543" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="1547"
      >

</a
      ><a name="1549" href="Exercises.html#1549" class="Function"
      >com*</a
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
      ><a name="1559" href="Exercises.html#1559" class="Bound"
      >m</a
      ><a name="1560"
      > </a
      ><a name="1561" href="Exercises.html#1561" class="Bound"
      >n</a
      ><a name="1562"
      > </a
      ><a name="1563" class="Symbol"
      >:</a
      ><a name="1564"
      > </a
      ><a name="1565" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#97" class="Datatype"
      >&#8469;</a
      ><a name="1566" class="Symbol"
      >)</a
      ><a name="1567"
      > </a
      ><a name="1568" class="Symbol"
      >&#8594;</a
      ><a name="1569"
      > </a
      ><a name="1570" href="Exercises.html#1559" class="Bound"
      >m</a
      ><a name="1571"
      > </a
      ><a name="1572" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#433" class="Primitive Operator"
      >*</a
      ><a name="1573"
      > </a
      ><a name="1574" href="Exercises.html#1561" class="Bound"
      >n</a
      ><a name="1575"
      > </a
      ><a name="1576" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="1577"
      > </a
      ><a name="1578" href="Exercises.html#1561" class="Bound"
      >n</a
      ><a name="1579"
      > </a
      ><a name="1580" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#433" class="Primitive Operator"
      >*</a
      ><a name="1581"
      > </a
      ><a name="1582" href="Exercises.html#1559" class="Bound"
      >m</a
      ><a name="1583"
      >
</a
      ><a name="1584" href="Exercises.html#1549" class="Function"
      >com*</a
      ><a name="1588"
      > </a
      ><a name="1589" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#115" class="InductiveConstructor"
      >zero</a
      ><a name="1593"
      > </a
      ><a name="1594" href="Exercises.html#1594" class="Bound"
      >n</a
      ><a name="1595"
      > </a
      ><a name="1596" class="Keyword"
      >rewrite</a
      ><a name="1603"
      > </a
      ><a name="1604" href="Exercises.html#1188" class="Function"
      >com*zero</a
      ><a name="1612"
      > </a
      ><a name="1613" href="Exercises.html#1594" class="Bound"
      >n</a
      ><a name="1614"
      > </a
      ><a name="1615" class="Symbol"
      >=</a
      ><a name="1616"
      > </a
      ><a name="1617" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="1621"
      >
</a
      ><a name="1622" href="Exercises.html#1549" class="Function"
      >com*</a
      ><a name="1626"
      > </a
      ><a name="1627" class="Symbol"
      >(</a
      ><a name="1628" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor"
      >suc</a
      ><a name="1631"
      > </a
      ><a name="1632" href="Exercises.html#1632" class="Bound"
      >m</a
      ><a name="1633" class="Symbol"
      >)</a
      ><a name="1634"
      > </a
      ><a name="1635" href="Exercises.html#1635" class="Bound"
      >n</a
      ><a name="1636"
      > </a
      ><a name="1637" class="Keyword"
      >rewrite</a
      ><a name="1644"
      > </a
      ><a name="1645" href="Exercises.html#1415" class="Function"
      >com*suc</a
      ><a name="1652"
      > </a
      ><a name="1653" href="Exercises.html#1632" class="Bound"
      >m</a
      ><a name="1654"
      > </a
      ><a name="1655" href="Exercises.html#1635" class="Bound"
      >n</a
      ><a name="1656"
      > </a
      ><a name="1657" class="Symbol"
      >|</a
      ><a name="1658"
      > </a
      ><a name="1659" href="Exercises.html#1549" class="Function"
      >com*</a
      ><a name="1663"
      > </a
      ><a name="1664" href="Exercises.html#1632" class="Bound"
      >m</a
      ><a name="1665"
      > </a
      ><a name="1666" href="Exercises.html#1635" class="Bound"
      >n</a
      ><a name="1667"
      > </a
      ><a name="1668" class="Symbol"
      >=</a
      ><a name="1669"
      > </a
      ><a name="1670" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="1674"
      >

</a
      ><a name="1676" href="Exercises.html#1676" class="Function"
      >zero&#8760;</a
      ><a name="1681"
      > </a
      ><a name="1682" class="Symbol"
      >:</a
      ><a name="1683"
      > </a
      ><a name="1684" class="Symbol"
      >&#8704;</a
      ><a name="1685"
      > </a
      ><a name="1686" class="Symbol"
      >(</a
      ><a name="1687" href="Exercises.html#1687" class="Bound"
      >n</a
      ><a name="1688"
      > </a
      ><a name="1689" class="Symbol"
      >:</a
      ><a name="1690"
      > </a
      ><a name="1691" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#97" class="Datatype"
      >&#8469;</a
      ><a name="1692" class="Symbol"
      >)</a
      ><a name="1693"
      > </a
      ><a name="1694" class="Symbol"
      >&#8594;</a
      ><a name="1695"
      > </a
      ><a name="1696" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#115" class="InductiveConstructor"
      >zero</a
      ><a name="1700"
      > </a
      ><a name="1701" href="Exercises.html#274" class="Function Operator"
      >&#8760;</a
      ><a name="1702"
      > </a
      ><a name="1703" href="Exercises.html#1687" class="Bound"
      >n</a
      ><a name="1704"
      > </a
      ><a name="1705" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="1706"
      > </a
      ><a name="1707" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#115" class="InductiveConstructor"
      >zero</a
      ><a name="1711"
      >
</a
      ><a name="1712" href="Exercises.html#1676" class="Function"
      >zero&#8760;</a
      ><a name="1717"
      > </a
      ><a name="1718" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#115" class="InductiveConstructor"
      >zero</a
      ><a name="1722"
      > </a
      ><a name="1723" class="Symbol"
      >=</a
      ><a name="1724"
      > </a
      ><a name="1725" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="1729"
      >
</a
      ><a name="1730" href="Exercises.html#1676" class="Function"
      >zero&#8760;</a
      ><a name="1735"
      > </a
      ><a name="1736" class="Symbol"
      >(</a
      ><a name="1737" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor"
      >suc</a
      ><a name="1740"
      > </a
      ><a name="1741" href="Exercises.html#1741" class="Bound"
      >n</a
      ><a name="1742" class="Symbol"
      >)</a
      ><a name="1743"
      > </a
      ><a name="1744" class="Symbol"
      >=</a
      ><a name="1745"
      > </a
      ><a name="1746" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="1750"
      >

</a
      ><a name="1752" href="Exercises.html#1752" class="Function"
      >assoc&#8760;</a
      ><a name="1758"
      > </a
      ><a name="1759" class="Symbol"
      >:</a
      ><a name="1760"
      > </a
      ><a name="1761" class="Symbol"
      >&#8704;</a
      ><a name="1762"
      > </a
      ><a name="1763" class="Symbol"
      >(</a
      ><a name="1764" href="Exercises.html#1764" class="Bound"
      >m</a
      ><a name="1765"
      > </a
      ><a name="1766" href="Exercises.html#1766" class="Bound"
      >n</a
      ><a name="1767"
      > </a
      ><a name="1768" href="Exercises.html#1768" class="Bound"
      >p</a
      ><a name="1769"
      > </a
      ><a name="1770" class="Symbol"
      >:</a
      ><a name="1771"
      > </a
      ><a name="1772" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#97" class="Datatype"
      >&#8469;</a
      ><a name="1773" class="Symbol"
      >)</a
      ><a name="1774"
      > </a
      ><a name="1775" class="Symbol"
      >&#8594;</a
      ><a name="1776"
      > </a
      ><a name="1777" class="Symbol"
      >(</a
      ><a name="1778" href="Exercises.html#1764" class="Bound"
      >m</a
      ><a name="1779"
      > </a
      ><a name="1780" href="Exercises.html#274" class="Function Operator"
      >&#8760;</a
      ><a name="1781"
      > </a
      ><a name="1782" href="Exercises.html#1766" class="Bound"
      >n</a
      ><a name="1783" class="Symbol"
      >)</a
      ><a name="1784"
      > </a
      ><a name="1785" href="Exercises.html#274" class="Function Operator"
      >&#8760;</a
      ><a name="1786"
      > </a
      ><a name="1787" href="Exercises.html#1768" class="Bound"
      >p</a
      ><a name="1788"
      > </a
      ><a name="1789" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="1790"
      > </a
      ><a name="1791" href="Exercises.html#1764" class="Bound"
      >m</a
      ><a name="1792"
      > </a
      ><a name="1793" href="Exercises.html#274" class="Function Operator"
      >&#8760;</a
      ><a name="1794"
      > </a
      ><a name="1795" class="Symbol"
      >(</a
      ><a name="1796" href="Exercises.html#1766" class="Bound"
      >n</a
      ><a name="1797"
      > </a
      ><a name="1798" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator"
      >+</a
      ><a name="1799"
      > </a
      ><a name="1800" href="Exercises.html#1768" class="Bound"
      >p</a
      ><a name="1801" class="Symbol"
      >)</a
      ><a name="1802"
      >
</a
      ><a name="1803" href="Exercises.html#1752" class="Function"
      >assoc&#8760;</a
      ><a name="1809"
      > </a
      ><a name="1810" href="Exercises.html#1810" class="Bound"
      >m</a
      ><a name="1811"
      > </a
      ><a name="1812" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#115" class="InductiveConstructor"
      >zero</a
      ><a name="1816"
      > </a
      ><a name="1817" href="Exercises.html#1817" class="Bound"
      >p</a
      ><a name="1818"
      > </a
      ><a name="1819" class="Symbol"
      >=</a
      ><a name="1820"
      > </a
      ><a name="1821" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="1825"
      >
</a
      ><a name="1826" href="Exercises.html#1752" class="Function"
      >assoc&#8760;</a
      ><a name="1832"
      > </a
      ><a name="1833" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#115" class="InductiveConstructor"
      >zero</a
      ><a name="1837"
      > </a
      ><a name="1838" class="Symbol"
      >(</a
      ><a name="1839" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor"
      >suc</a
      ><a name="1842"
      > </a
      ><a name="1843" href="Exercises.html#1843" class="Bound"
      >n</a
      ><a name="1844" class="Symbol"
      >)</a
      ><a name="1845"
      > </a
      ><a name="1846" href="Exercises.html#1846" class="Bound"
      >p</a
      ><a name="1847"
      > </a
      ><a name="1848" class="Keyword"
      >rewrite</a
      ><a name="1855"
      > </a
      ><a name="1856" href="Exercises.html#1676" class="Function"
      >zero&#8760;</a
      ><a name="1861"
      > </a
      ><a name="1862" href="Exercises.html#1846" class="Bound"
      >p</a
      ><a name="1863"
      > </a
      ><a name="1864" class="Symbol"
      >=</a
      ><a name="1865"
      > </a
      ><a name="1866" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="1870"
      >
</a
      ><a name="1871" href="Exercises.html#1752" class="Function"
      >assoc&#8760;</a
      ><a name="1877"
      > </a
      ><a name="1878" class="Symbol"
      >(</a
      ><a name="1879" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor"
      >suc</a
      ><a name="1882"
      > </a
      ><a name="1883" href="Exercises.html#1883" class="Bound"
      >m</a
      ><a name="1884" class="Symbol"
      >)</a
      ><a name="1885"
      > </a
      ><a name="1886" class="Symbol"
      >(</a
      ><a name="1887" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor"
      >suc</a
      ><a name="1890"
      > </a
      ><a name="1891" href="Exercises.html#1891" class="Bound"
      >n</a
      ><a name="1892" class="Symbol"
      >)</a
      ><a name="1893"
      > </a
      ><a name="1894" href="Exercises.html#1894" class="Bound"
      >p</a
      ><a name="1895"
      > </a
      ><a name="1896" class="Keyword"
      >rewrite</a
      ><a name="1903"
      > </a
      ><a name="1904" href="Exercises.html#1752" class="Function"
      >assoc&#8760;</a
      ><a name="1910"
      > </a
      ><a name="1911" href="Exercises.html#1883" class="Bound"
      >m</a
      ><a name="1912"
      > </a
      ><a name="1913" href="Exercises.html#1891" class="Bound"
      >n</a
      ><a name="1914"
      > </a
      ><a name="1915" href="Exercises.html#1894" class="Bound"
      >p</a
      ><a name="1916"
      > </a
      ><a name="1917" class="Symbol"
      >=</a
      ><a name="1918"
      > </a
      ><a name="1919" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      >
{% endraw %}</pre>


