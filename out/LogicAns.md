---
title     : "Logic Answers"
layout    : page
permalink : /LogicAns
---

<pre class="Agda">{% raw %}
<a name="90" class="Keyword"
      >open</a
      ><a name="94"
      > </a
      ><a name="95" class="Keyword"
      >import</a
      ><a name="101"
      > </a
      ><a name="102" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#1" class="Module"
      >Relation.Binary.PropositionalEquality</a
      ><a name="139"
      > </a
      ><a name="140" class="Keyword"
      >using</a
      ><a name="145"
      > </a
      ><a name="146" class="Symbol"
      >(</a
      ><a name="147" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >_&#8801;_</a
      ><a name="150" class="Symbol"
      >;</a
      ><a name="151"
      > </a
      ><a name="152" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="156" class="Symbol"
      >;</a
      ><a name="157"
      > </a
      ><a name="158" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.Core.html#565" class="Function"
      >sym</a
      ><a name="161" class="Symbol"
      >)</a
      ><a name="162"
      >
</a
      ><a name="163" class="Keyword"
      >open</a
      ><a name="167"
      > </a
      ><a name="168" class="Keyword"
      >import</a
      ><a name="174"
      > </a
      ><a name="175" class="Module"
      >Logic</a
      >
{% endraw %}</pre>

<pre class="Agda">{% raw %}
<a name="206" href="LogicAns.html#206" class="Function"
      >ex1</a
      ><a name="209"
      > </a
      ><a name="210" class="Symbol"
      >:</a
      ><a name="211"
      > </a
      ><a name="212" href="Logic.html#35748" class="Function"
      >&#172;&#172;-elim</a
      ><a name="219"
      > </a
      ><a name="220" class="Symbol"
      >&#8594;</a
      ><a name="221"
      > </a
      ><a name="222" href="Logic.html#35756" class="Function"
      >excluded-middle</a
      ><a name="237"
      >
</a
      ><a name="238" href="LogicAns.html#206" class="Function"
      >ex1</a
      ><a name="241"
      > </a
      ><a name="242" href="LogicAns.html#242" class="Bound"
      >h</a
      ><a name="243"
      > </a
      ><a name="244" class="Symbol"
      >=</a
      ><a name="245"
      > </a
      ><a name="246" href="LogicAns.html#242" class="Bound"
      >h</a
      ><a name="247"
      > </a
      ><a name="248" href="Logic.html#33236" class="Function"
      >excluded-middle-irrefutable</a
      ><a name="275"
      >

</a
      ><a name="277" href="LogicAns.html#277" class="Function"
      >ex2</a
      ><a name="280"
      > </a
      ><a name="281" class="Symbol"
      >:</a
      ><a name="282"
      > </a
      ><a name="283" href="Logic.html#35756" class="Function"
      >excluded-middle</a
      ><a name="298"
      > </a
      ><a name="299" class="Symbol"
      >&#8594;</a
      ><a name="300"
      > </a
      ><a name="301" href="Logic.html#35779" class="Function"
      >implication</a
      ><a name="312"
      >
</a
      ><a name="313" href="LogicAns.html#277" class="Function"
      >ex2</a
      ><a name="316"
      > </a
      ><a name="317" href="LogicAns.html#317" class="Bound"
      >em</a
      ><a name="319"
      > </a
      ><a name="320" href="LogicAns.html#320" class="Bound"
      >f</a
      ><a name="321"
      > </a
      ><a name="322" class="Keyword"
      >with</a
      ><a name="326"
      > </a
      ><a name="327" href="LogicAns.html#317" class="Bound"
      >em</a
      ><a name="329"
      >
</a
      ><a name="330" class="Symbol"
      >...</a
      ><a name="333"
      > </a
      ><a name="334" class="Symbol"
      >|</a
      ><a name="335"
      > </a
      ><a name="336" href="Logic.html#14686" class="InductiveConstructor"
      >inj&#8321;</a
      ><a name="340"
      > </a
      ><a name="341" href="LogicAns.html#341" class="Bound"
      >a</a
      ><a name="342"
      > </a
      ><a name="343" class="Symbol"
      >=</a
      ><a name="344"
      > </a
      ><a name="345" href="Logic.html#14722" class="InductiveConstructor"
      >inj&#8322;</a
      ><a name="349"
      > </a
      ><a name="350" class="Symbol"
      >(</a
      ><a name="351" href="LogicAns.html#320" class="Bound"
      >f</a
      ><a name="352"
      > </a
      ><a name="353" href="LogicAns.html#341" class="Bound"
      >a</a
      ><a name="354" class="Symbol"
      >)</a
      ><a name="355"
      >
</a
      ><a name="356" class="Symbol"
      >...</a
      ><a name="359"
      > </a
      ><a name="360" class="Symbol"
      >|</a
      ><a name="361"
      > </a
      ><a name="362" href="Logic.html#14722" class="InductiveConstructor"
      >inj&#8322;</a
      ><a name="366"
      > </a
      ><a name="367" href="LogicAns.html#367" class="Bound"
      >&#172;a</a
      ><a name="369"
      > </a
      ><a name="370" class="Symbol"
      >=</a
      ><a name="371"
      > </a
      ><a name="372" href="Logic.html#14686" class="InductiveConstructor"
      >inj&#8321;</a
      ><a name="376"
      > </a
      ><a name="377" href="LogicAns.html#367" class="Bound"
      >&#172;a</a
      ><a name="379"
      >

</a
      ><a name="381" href="LogicAns.html#381" class="Function"
      >ex3</a
      ><a name="384"
      > </a
      ><a name="385" class="Symbol"
      >:</a
      ><a name="386"
      > </a
      ><a name="387" href="Logic.html#35756" class="Function"
      >excluded-middle</a
      ><a name="402"
      > </a
      ><a name="403" class="Symbol"
      >&#8594;</a
      ><a name="404"
      > </a
      ><a name="405" href="Logic.html#35772" class="Function"
      >peirce</a
      ><a name="411"
      >
</a
      ><a name="412" href="LogicAns.html#381" class="Function"
      >ex3</a
      ><a name="415"
      > </a
      ><a name="416" href="LogicAns.html#416" class="Bound"
      >em</a
      ><a name="418"
      > </a
      ><a name="419" href="LogicAns.html#419" class="Bound"
      >k</a
      ><a name="420"
      > </a
      ><a name="421" class="Keyword"
      >with</a
      ><a name="425"
      > </a
      ><a name="426" href="LogicAns.html#416" class="Bound"
      >em</a
      ><a name="428"
      >
</a
      ><a name="429" class="Symbol"
      >...</a
      ><a name="432"
      > </a
      ><a name="433" class="Symbol"
      >|</a
      ><a name="434"
      > </a
      ><a name="435" href="Logic.html#14686" class="InductiveConstructor"
      >inj&#8321;</a
      ><a name="439"
      > </a
      ><a name="440" href="LogicAns.html#440" class="Bound"
      >a</a
      ><a name="441"
      > </a
      ><a name="442" class="Symbol"
      >=</a
      ><a name="443"
      > </a
      ><a name="444" href="LogicAns.html#440" class="Bound"
      >a</a
      ><a name="445"
      >
</a
      ><a name="446" class="Symbol"
      >...</a
      ><a name="449"
      > </a
      ><a name="450" class="Symbol"
      >|</a
      ><a name="451"
      > </a
      ><a name="452" href="Logic.html#14722" class="InductiveConstructor"
      >inj&#8322;</a
      ><a name="456"
      > </a
      ><a name="457" href="LogicAns.html#457" class="Bound"
      >&#172;a</a
      ><a name="459"
      > </a
      ><a name="460" class="Symbol"
      >=</a
      ><a name="461"
      > </a
      ><a name="462" href="LogicAns.html#419" class="Bound"
      >k</a
      ><a name="463"
      > </a
      ><a name="464" class="Symbol"
      >(&#955;</a
      ><a name="466"
      > </a
      ><a name="467" href="LogicAns.html#467" class="Bound"
      >a</a
      ><a name="468"
      > </a
      ><a name="469" class="Symbol"
      >&#8594;</a
      ><a name="470"
      > </a
      ><a name="471" href="Logic.html#19890" class="Function"
      >&#8869;-elim</a
      ><a name="477"
      > </a
      ><a name="478" class="Symbol"
      >(</a
      ><a name="479" href="LogicAns.html#457" class="Bound"
      >&#172;a</a
      ><a name="481"
      > </a
      ><a name="482" href="LogicAns.html#467" class="Bound"
      >a</a
      ><a name="483" class="Symbol"
      >))</a
      ><a name="485"
      >

</a
      ><a name="487" href="LogicAns.html#487" class="Function"
      >ex4</a
      ><a name="490"
      > </a
      ><a name="491" class="Symbol"
      >:</a
      ><a name="492"
      > </a
      ><a name="493" href="Logic.html#36029" class="Function"
      >de-morgan&#8242;</a
      ><a name="503"
      > </a
      ><a name="504" class="Symbol"
      >&#8594;</a
      ><a name="505"
      > </a
      ><a name="506" href="Logic.html#35748" class="Function"
      >&#172;&#172;-elim</a
      ><a name="513"
      >
</a
      ><a name="514" href="LogicAns.html#487" class="Function"
      >ex4</a
      ><a name="517"
      > </a
      ><a name="518" href="LogicAns.html#518" class="Bound"
      >dem</a
      ><a name="521"
      > </a
      ><a name="522" href="LogicAns.html#522" class="Bound"
      >&#172;&#172;a</a
      ><a name="525"
      > </a
      ><a name="526" class="Symbol"
      >=</a
      ><a name="527"
      > </a
      ><a name="528" href="Logic.html#7507" class="Function"
      >fst</a
      ><a name="531"
      > </a
      ><a name="532" class="Symbol"
      >(</a
      ><a name="533" href="LogicAns.html#518" class="Bound"
      >dem</a
      ><a name="536"
      > </a
      ><a name="537" class="Symbol"
      >(</a
      ><a name="538" href="LogicAns.html#559" class="Function"
      >obvs</a
      ><a name="542"
      > </a
      ><a name="543" href="LogicAns.html#522" class="Bound"
      >&#172;&#172;a</a
      ><a name="546" class="Symbol"
      >))</a
      ><a name="548"
      >
  </a
      ><a name="551" class="Keyword"
      >where</a
      ><a name="556"
      >
  </a
      ><a name="559" href="LogicAns.html#559" class="Function"
      >obvs</a
      ><a name="563"
      > </a
      ><a name="564" class="Symbol"
      >:</a
      ><a name="565"
      > </a
      ><a name="566" class="Symbol"
      >&#8704;</a
      ><a name="567"
      > </a
      ><a name="568" class="Symbol"
      >{</a
      ><a name="569" href="LogicAns.html#569" class="Bound"
      >A</a
      ><a name="570"
      > </a
      ><a name="571" class="Symbol"
      >:</a
      ><a name="572"
      > </a
      ><a name="573" class="PrimitiveType"
      >Set</a
      ><a name="576" class="Symbol"
      >}</a
      ><a name="577"
      > </a
      ><a name="578" class="Symbol"
      >&#8594;</a
      ><a name="579"
      > </a
      ><a name="580" href="Logic.html#29825" class="Function Operator"
      >&#172;</a
      ><a name="581"
      > </a
      ><a name="582" href="Logic.html#29825" class="Function Operator"
      >&#172;</a
      ><a name="583"
      > </a
      ><a name="584" href="LogicAns.html#569" class="Bound"
      >A</a
      ><a name="585"
      > </a
      ><a name="586" class="Symbol"
      >&#8594;</a
      ><a name="587"
      > </a
      ><a name="588" href="Logic.html#29825" class="Function Operator"
      >&#172;</a
      ><a name="589"
      > </a
      ><a name="590" class="Symbol"
      >(</a
      ><a name="591" href="Logic.html#29825" class="Function Operator"
      >&#172;</a
      ><a name="592"
      > </a
      ><a name="593" href="LogicAns.html#569" class="Bound"
      >A</a
      ><a name="594"
      > </a
      ><a name="595" href="Logic.html#14656" class="Datatype Operator"
      >&#8846;</a
      ><a name="596"
      > </a
      ><a name="597" href="Logic.html#29825" class="Function Operator"
      >&#172;</a
      ><a name="598"
      > </a
      ><a name="599" href="Logic.html#12590" class="Datatype"
      >&#8868;</a
      ><a name="600" class="Symbol"
      >)</a
      ><a name="601"
      >
  </a
      ><a name="604" href="LogicAns.html#559" class="Function"
      >obvs</a
      ><a name="608"
      > </a
      ><a name="609" href="LogicAns.html#609" class="Bound"
      >&#172;&#172;a</a
      ><a name="612"
      > </a
      ><a name="613" class="Symbol"
      >(</a
      ><a name="614" href="Logic.html#14686" class="InductiveConstructor"
      >inj&#8321;</a
      ><a name="618"
      > </a
      ><a name="619" href="LogicAns.html#619" class="Bound"
      >&#172;a</a
      ><a name="621" class="Symbol"
      >)</a
      ><a name="622"
      > </a
      ><a name="623" class="Symbol"
      >=</a
      ><a name="624"
      > </a
      ><a name="625" href="LogicAns.html#609" class="Bound"
      >&#172;&#172;a</a
      ><a name="628"
      > </a
      ><a name="629" href="LogicAns.html#619" class="Bound"
      >&#172;a</a
      ><a name="631"
      >
  </a
      ><a name="634" href="LogicAns.html#559" class="Function"
      >obvs</a
      ><a name="638"
      > </a
      ><a name="639" href="LogicAns.html#639" class="Bound"
      >&#172;&#172;a</a
      ><a name="642"
      > </a
      ><a name="643" class="Symbol"
      >(</a
      ><a name="644" href="Logic.html#14722" class="InductiveConstructor"
      >inj&#8322;</a
      ><a name="648"
      > </a
      ><a name="649" href="LogicAns.html#649" class="Bound"
      >&#172;&#8868;</a
      ><a name="651" class="Symbol"
      >)</a
      ><a name="652"
      > </a
      ><a name="653" class="Symbol"
      >=</a
      ><a name="654"
      > </a
      ><a name="655" href="LogicAns.html#649" class="Bound"
      >&#172;&#8868;</a
      ><a name="657"
      > </a
      ><a name="658" href="Logic.html#12606" class="InductiveConstructor"
      >tt</a
      ><a name="660"
      >

</a
      ><a name="662" href="LogicAns.html#662" class="Function"
      >help&#8242;</a
      ><a name="667"
      > </a
      ><a name="668" class="Symbol"
      >:</a
      ><a name="669"
      > </a
      ><a name="670" href="Logic.html#35756" class="Function"
      >excluded-middle</a
      ><a name="685"
      > </a
      ><a name="686" class="Symbol"
      >&#8594;</a
      ><a name="687"
      > </a
      ><a name="688" class="Symbol"
      >&#8704;</a
      ><a name="689"
      > </a
      ><a name="690" class="Symbol"
      >{</a
      ><a name="691" href="LogicAns.html#691" class="Bound"
      >A</a
      ><a name="692"
      > </a
      ><a name="693" href="LogicAns.html#693" class="Bound"
      >B</a
      ><a name="694"
      > </a
      ><a name="695" class="Symbol"
      >:</a
      ><a name="696"
      > </a
      ><a name="697" class="PrimitiveType"
      >Set</a
      ><a name="700" class="Symbol"
      >}</a
      ><a name="701"
      > </a
      ><a name="702" class="Symbol"
      >&#8594;</a
      ><a name="703"
      > </a
      ><a name="704" href="Logic.html#29825" class="Function Operator"
      >&#172;</a
      ><a name="705"
      > </a
      ><a name="706" class="Symbol"
      >(</a
      ><a name="707" href="LogicAns.html#691" class="Bound"
      >A</a
      ><a name="708"
      > </a
      ><a name="709" href="Logic.html#7202" class="Datatype Operator"
      >&#215;</a
      ><a name="710"
      > </a
      ><a name="711" href="LogicAns.html#693" class="Bound"
      >B</a
      ><a name="712" class="Symbol"
      >)</a
      ><a name="713"
      > </a
      ><a name="714" class="Symbol"
      >&#8594;</a
      ><a name="715"
      > </a
      ><a name="716" href="Logic.html#29825" class="Function Operator"
      >&#172;</a
      ><a name="717"
      > </a
      ><a name="718" href="LogicAns.html#691" class="Bound"
      >A</a
      ><a name="719"
      > </a
      ><a name="720" href="Logic.html#14656" class="Datatype Operator"
      >&#8846;</a
      ><a name="721"
      > </a
      ><a name="722" href="Logic.html#29825" class="Function Operator"
      >&#172;</a
      ><a name="723"
      > </a
      ><a name="724" href="LogicAns.html#693" class="Bound"
      >B</a
      ><a name="725"
      >
</a
      ><a name="726" href="LogicAns.html#662" class="Function"
      >help&#8242;</a
      ><a name="731"
      > </a
      ><a name="732" href="LogicAns.html#732" class="Bound"
      >em</a
      ><a name="734"
      > </a
      ><a name="735" href="LogicAns.html#735" class="Bound"
      >&#172;a&#215;b</a
      ><a name="739"
      > </a
      ><a name="740" class="Keyword"
      >with</a
      ><a name="744"
      > </a
      ><a name="745" href="LogicAns.html#732" class="Bound"
      >em</a
      ><a name="747"
      > </a
      ><a name="748" class="Symbol"
      >|</a
      ><a name="749"
      > </a
      ><a name="750" href="LogicAns.html#732" class="Bound"
      >em</a
      ><a name="752"
      >
</a
      ><a name="753" class="Symbol"
      >...</a
      ><a name="756"
      > </a
      ><a name="757" class="Symbol"
      >|</a
      ><a name="758"
      > </a
      ><a name="759" href="Logic.html#14686" class="InductiveConstructor"
      >inj&#8321;</a
      ><a name="763"
      > </a
      ><a name="764" href="LogicAns.html#764" class="Bound"
      >a</a
      ><a name="765"
      > </a
      ><a name="766" class="Symbol"
      >|</a
      ><a name="767"
      > </a
      ><a name="768" href="Logic.html#14686" class="InductiveConstructor"
      >inj&#8321;</a
      ><a name="772"
      > </a
      ><a name="773" href="LogicAns.html#773" class="Bound"
      >b</a
      ><a name="774"
      > </a
      ><a name="775" class="Symbol"
      >=</a
      ><a name="776"
      > </a
      ><a name="777" href="Logic.html#19890" class="Function"
      >&#8869;-elim</a
      ><a name="783"
      > </a
      ><a name="784" class="Symbol"
      >(</a
      ><a name="785" href="LogicAns.html#735" class="Bound"
      >&#172;a&#215;b</a
      ><a name="789"
      > </a
      ><a name="790" class="Symbol"
      >(</a
      ><a name="791" href="LogicAns.html#764" class="Bound"
      >a</a
      ><a name="792"
      > </a
      ><a name="793" href="Logic.html#7232" class="InductiveConstructor Operator"
      >,</a
      ><a name="794"
      > </a
      ><a name="795" href="LogicAns.html#773" class="Bound"
      >b</a
      ><a name="796" class="Symbol"
      >))</a
      ><a name="798"
      >
</a
      ><a name="799" class="Symbol"
      >...</a
      ><a name="802"
      > </a
      ><a name="803" class="Symbol"
      >|</a
      ><a name="804"
      > </a
      ><a name="805" href="Logic.html#14686" class="InductiveConstructor"
      >inj&#8321;</a
      ><a name="809"
      > </a
      ><a name="810" href="LogicAns.html#810" class="Bound"
      >a</a
      ><a name="811"
      > </a
      ><a name="812" class="Symbol"
      >|</a
      ><a name="813"
      > </a
      ><a name="814" href="Logic.html#14722" class="InductiveConstructor"
      >inj&#8322;</a
      ><a name="818"
      > </a
      ><a name="819" href="LogicAns.html#819" class="Bound"
      >&#172;b</a
      ><a name="821"
      > </a
      ><a name="822" class="Symbol"
      >=</a
      ><a name="823"
      > </a
      ><a name="824" href="Logic.html#14722" class="InductiveConstructor"
      >inj&#8322;</a
      ><a name="828"
      > </a
      ><a name="829" href="LogicAns.html#819" class="Bound"
      >&#172;b</a
      ><a name="831"
      >
</a
      ><a name="832" class="Symbol"
      >...</a
      ><a name="835"
      > </a
      ><a name="836" class="Symbol"
      >|</a
      ><a name="837"
      > </a
      ><a name="838" href="Logic.html#14722" class="InductiveConstructor"
      >inj&#8322;</a
      ><a name="842"
      > </a
      ><a name="843" href="LogicAns.html#843" class="Bound"
      >&#172;a</a
      ><a name="845"
      > </a
      ><a name="846" class="Symbol"
      >|</a
      ><a name="847"
      > </a
      ><a name="848" href="Logic.html#14686" class="InductiveConstructor"
      >inj&#8321;</a
      ><a name="852"
      > </a
      ><a name="853" href="LogicAns.html#853" class="Bound"
      >b</a
      ><a name="854"
      > </a
      ><a name="855" class="Symbol"
      >=</a
      ><a name="856"
      > </a
      ><a name="857" href="Logic.html#14686" class="InductiveConstructor"
      >inj&#8321;</a
      ><a name="861"
      > </a
      ><a name="862" href="LogicAns.html#843" class="Bound"
      >&#172;a</a
      ><a name="864"
      >
</a
      ><a name="865" class="Symbol"
      >...</a
      ><a name="868"
      > </a
      ><a name="869" class="Symbol"
      >|</a
      ><a name="870"
      > </a
      ><a name="871" href="Logic.html#14722" class="InductiveConstructor"
      >inj&#8322;</a
      ><a name="875"
      > </a
      ><a name="876" href="LogicAns.html#876" class="Bound"
      >&#172;a</a
      ><a name="878"
      > </a
      ><a name="879" class="Symbol"
      >|</a
      ><a name="880"
      > </a
      ><a name="881" href="Logic.html#14722" class="InductiveConstructor"
      >inj&#8322;</a
      ><a name="885"
      > </a
      ><a name="886" href="LogicAns.html#886" class="Bound"
      >&#172;b</a
      ><a name="888"
      > </a
      ><a name="889" class="Symbol"
      >=</a
      ><a name="890"
      > </a
      ><a name="891" href="Logic.html#14686" class="InductiveConstructor"
      >inj&#8321;</a
      ><a name="895"
      > </a
      ><a name="896" href="LogicAns.html#876" class="Bound"
      >&#172;a</a
      ><a name="898"
      >

</a
      ><a name="900" href="LogicAns.html#900" class="Function"
      >&#8868;&#8869;-iso</a
      ><a name="906"
      > </a
      ><a name="907" class="Symbol"
      >:</a
      ><a name="908"
      > </a
      ><a name="909" class="Symbol"
      >(</a
      ><a name="910" href="Logic.html#29825" class="Function Operator"
      >&#172;</a
      ><a name="911"
      > </a
      ><a name="912" href="Logic.html#19450" class="Datatype"
      >&#8869;</a
      ><a name="913" class="Symbol"
      >)</a
      ><a name="914"
      > </a
      ><a name="915" href="Logic.html#1478" class="Record Operator"
      >&#8771;</a
      ><a name="916"
      > </a
      ><a name="917" href="Logic.html#12590" class="Datatype"
      >&#8868;</a
      ><a name="918"
      >
</a
      ><a name="919" href="LogicAns.html#900" class="Function"
      >&#8868;&#8869;-iso</a
      ><a name="925"
      > </a
      ><a name="926" class="Symbol"
      >=</a
      ><a name="927"
      >
  </a
      ><a name="930" class="Keyword"
      >record</a
      ><a name="936"
      >
    </a
      ><a name="941" class="Symbol"
      >{</a
      ><a name="942"
      > </a
      ><a name="943" class="Field"
      >to</a
      ><a name="945"
      >   </a
      ><a name="948" class="Symbol"
      >=</a
      ><a name="949"
      >  </a
      ><a name="951" class="Symbol"
      >&#955;</a
      ><a name="952"
      > </a
      ><a name="953" href="LogicAns.html#953" class="Bound"
      >_</a
      ><a name="954"
      > </a
      ><a name="955" class="Symbol"
      >&#8594;</a
      ><a name="956"
      > </a
      ><a name="957" href="Logic.html#12606" class="InductiveConstructor"
      >tt</a
      ><a name="959"
      >
    </a
      ><a name="964" class="Symbol"
      >;</a
      ><a name="965"
      > </a
      ><a name="966" class="Field"
      >fro</a
      ><a name="969"
      >  </a
      ><a name="971" class="Symbol"
      >=</a
      ><a name="972"
      >  </a
      ><a name="974" class="Symbol"
      >&#955;</a
      ><a name="975"
      > </a
      ><a name="976" href="LogicAns.html#976" class="Bound"
      >_</a
      ><a name="977"
      > </a
      ><a name="978" href="LogicAns.html#978" class="Bound"
      >ff</a
      ><a name="980"
      > </a
      ><a name="981" class="Symbol"
      >&#8594;</a
      ><a name="982"
      > </a
      ><a name="983" href="LogicAns.html#978" class="Bound"
      >ff</a
      ><a name="985"
      >
    </a
      ><a name="990" class="Symbol"
      >;</a
      ><a name="991"
      > </a
      ><a name="992" class="Field"
      >inv&#737;</a
      ><a name="996"
      > </a
      ><a name="997" class="Symbol"
      >=</a
      ><a name="998"
      >  </a
      ><a name="1000" class="Symbol"
      >&#955;</a
      ><a name="1001"
      > </a
      ><a name="1002" href="LogicAns.html#1002" class="Bound"
      >_</a
      ><a name="1003"
      > </a
      ><a name="1004" class="Symbol"
      >&#8594;</a
      ><a name="1005"
      > </a
      ><a name="1006" href="Logic.html#24738" class="Postulate"
      >extensionality</a
      ><a name="1020"
      > </a
      ><a name="1021" class="Symbol"
      >(&#955;</a
      ><a name="1023"
      > </a
      ><a name="1024" class="Symbol"
      >())</a
      ><a name="1027"
      >
    </a
      ><a name="1032" class="Symbol"
      >;</a
      ><a name="1033"
      > </a
      ><a name="1034" class="Field"
      >inv&#691;</a
      ><a name="1038"
      > </a
      ><a name="1039" class="Symbol"
      >=</a
      ><a name="1040"
      >  </a
      ><a name="1042" class="Symbol"
      >&#955;</a
      ><a name="1043"
      > </a
      ><a name="1044" class="Symbol"
      >{</a
      ><a name="1045"
      > </a
      ><a name="1046" href="Logic.html#12606" class="InductiveConstructor"
      >tt</a
      ><a name="1048"
      > </a
      ><a name="1049" class="Symbol"
      >&#8594;</a
      ><a name="1050"
      > </a
      ><a name="1051" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="1055"
      > </a
      ><a name="1056" class="Symbol"
      >}</a
      ><a name="1057"
      >
    </a
      ><a name="1062" class="Symbol"
      >}</a
      >
{% endraw %}</pre>
