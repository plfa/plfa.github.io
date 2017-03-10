---
title         : "Stlc: The Simply Typed Lambda-Calculus"
layout        : default
hide-implicit : false
extra-script : [agda-extra-script.html]
extra-style  : [agda-extra-style.html]
permalink     : "sf/Stlc.html"
---

<!--{% raw %}--><pre class="Agda">
<a name="236" class="Keyword"
      >module</a
      ><a name="242"
      > </a
      ><a name="243" href="Stlc.html#1" class="Module"
      >Stlc</a
      ><a name="247"
      > </a
      ><a name="248" class="Keyword"
      >where</a
      >
</pre><!--{% endraw %}-->

<div class="hidden">
<!--{% raw %}--><pre class="Agda">
<a name="300" class="Keyword"
      >open</a
      ><a name="304"
      > </a
      ><a name="305" class="Keyword"
      >import</a
      ><a name="311"
      > </a
      ><a name="312" class="Module"
      >Maps</a
      ><a name="316"
      > </a
      ><a name="317" class="Keyword"
      >using</a
      ><a name="322"
      > </a
      ><a name="323" class="Symbol"
      >(</a
      ><a name="324" href="Maps.html#2400" class="Datatype"
      >Id</a
      ><a name="326" class="Symbol"
      >;</a
      ><a name="327"
      > </a
      ><a name="328" href="Maps.html#2417" class="InductiveConstructor"
      >id</a
      ><a name="330" class="Symbol"
      >;</a
      ><a name="331"
      > </a
      ><a name="332" href="Maps.html#2454" class="Function Operator"
      >_&#8799;_</a
      ><a name="335" class="Symbol"
      >;</a
      ><a name="336"
      > </a
      ><a name="337" href="Maps.html#9519" class="Function"
      >PartialMap</a
      ><a name="347" class="Symbol"
      >;</a
      ><a name="348"
      > </a
      ><a name="349" class="Keyword"
      >module</a
      ><a name="355"
      > </a
      ><a name="356" href="Maps.html#9608" class="Module"
      >PartialMap</a
      ><a name="366" class="Symbol"
      >)</a
      ><a name="367"
      >
</a
      ><a name="368" class="Keyword"
      >open</a
      ><a name="372"
      > </a
      ><a name="373" class="Keyword"
      >import</a
      ><a name="379"
      > </a
      ><a name="380" href="https://agda.github.io/agda-stdlib/Data.Empty.html#1" class="Module"
      >Data.Empty</a
      ><a name="390"
      > </a
      ><a name="391" class="Keyword"
      >using</a
      ><a name="396"
      > </a
      ><a name="397" class="Symbol"
      >(</a
      ><a name="398" href="https://agda.github.io/agda-stdlib/Data.Empty.html#243" class="Datatype"
      >&#8869;</a
      ><a name="399" class="Symbol"
      >;</a
      ><a name="400"
      > </a
      ><a name="401" href="https://agda.github.io/agda-stdlib/Data.Empty.html#348" class="Function"
      >&#8869;-elim</a
      ><a name="407" class="Symbol"
      >)</a
      ><a name="408"
      >
</a
      ><a name="409" class="Keyword"
      >open</a
      ><a name="413"
      > </a
      ><a name="414" class="Keyword"
      >import</a
      ><a name="420"
      > </a
      ><a name="421" href="https://agda.github.io/agda-stdlib/Data.Maybe.html#1" class="Module"
      >Data.Maybe</a
      ><a name="431"
      > </a
      ><a name="432" class="Keyword"
      >using</a
      ><a name="437"
      > </a
      ><a name="438" class="Symbol"
      >(</a
      ><a name="439" href="https://agda.github.io/agda-stdlib/Data.Maybe.Base.html#335" class="Datatype"
      >Maybe</a
      ><a name="444" class="Symbol"
      >;</a
      ><a name="445"
      > </a
      ><a name="446" href="https://agda.github.io/agda-stdlib/Data.Maybe.html#1527" class="InductiveConstructor"
      >just</a
      ><a name="450" class="Symbol"
      >;</a
      ><a name="451"
      > </a
      ><a name="452" href="https://agda.github.io/agda-stdlib/Data.Maybe.html#1588" class="InductiveConstructor"
      >nothing</a
      ><a name="459" class="Symbol"
      >)</a
      ><a name="460"
      >
</a
      ><a name="461" class="Keyword"
      >open</a
      ><a name="465"
      > </a
      ><a name="466" class="Keyword"
      >import</a
      ><a name="472"
      > </a
      ><a name="473" href="https://agda.github.io/agda-stdlib/Data.Nat.html#1" class="Module"
      >Data.Nat</a
      ><a name="481"
      > </a
      ><a name="482" class="Keyword"
      >using</a
      ><a name="487"
      > </a
      ><a name="488" class="Symbol"
      >(</a
      ><a name="489" href="Agda.Builtin.Nat.html#69" class="Datatype"
      >&#8469;</a
      ><a name="490" class="Symbol"
      >;</a
      ><a name="491"
      > </a
      ><a name="492" href="Agda.Builtin.Nat.html#100" class="InductiveConstructor"
      >suc</a
      ><a name="495" class="Symbol"
      >;</a
      ><a name="496"
      > </a
      ><a name="497" href="Agda.Builtin.Nat.html#87" class="InductiveConstructor"
      >zero</a
      ><a name="501" class="Symbol"
      >;</a
      ><a name="502"
      > </a
      ><a name="503" href="Agda.Builtin.Nat.html#202" class="Primitive Operator"
      >_+_</a
      ><a name="506" class="Symbol"
      >)</a
      ><a name="507"
      >
</a
      ><a name="508" class="Keyword"
      >open</a
      ><a name="512"
      > </a
      ><a name="513" class="Keyword"
      >import</a
      ><a name="519"
      > </a
      ><a name="520" href="https://agda.github.io/agda-stdlib/Data.Product.html#1" class="Module"
      >Data.Product</a
      ><a name="532"
      > </a
      ><a name="533" class="Keyword"
      >using</a
      ><a name="538"
      > </a
      ><a name="539" class="Symbol"
      >(</a
      ><a name="540" href="https://agda.github.io/agda-stdlib/Data.Product.html#823" class="Function"
      >&#8707;</a
      ><a name="541" class="Symbol"
      >;</a
      ><a name="542"
      > </a
      ><a name="543" href="https://agda.github.io/agda-stdlib/Data.Product.html#884" class="Function"
      >&#8708;</a
      ><a name="544" class="Symbol"
      >;</a
      ><a name="545"
      > </a
      ><a name="546" href="https://agda.github.io/agda-stdlib/Data.Product.html#509" class="InductiveConstructor Operator"
      >_,_</a
      ><a name="549" class="Symbol"
      >)</a
      ><a name="550"
      >
</a
      ><a name="551" class="Keyword"
      >open</a
      ><a name="555"
      > </a
      ><a name="556" class="Keyword"
      >import</a
      ><a name="562"
      > </a
      ><a name="563" href="https://agda.github.io/agda-stdlib/Function.html#1" class="Module"
      >Function</a
      ><a name="571"
      > </a
      ><a name="572" class="Keyword"
      >using</a
      ><a name="577"
      > </a
      ><a name="578" class="Symbol"
      >(</a
      ><a name="579" href="https://agda.github.io/agda-stdlib/Function.html#713" class="Function Operator"
      >_&#8728;_</a
      ><a name="582" class="Symbol"
      >;</a
      ><a name="583"
      > </a
      ><a name="584" href="https://agda.github.io/agda-stdlib/Function.html#1835" class="Function Operator"
      >_$_</a
      ><a name="587" class="Symbol"
      >)</a
      ><a name="588"
      >
</a
      ><a name="589" class="Keyword"
      >open</a
      ><a name="593"
      > </a
      ><a name="594" class="Keyword"
      >import</a
      ><a name="600"
      > </a
      ><a name="601" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#1" class="Module"
      >Relation.Nullary</a
      ><a name="617"
      > </a
      ><a name="618" class="Keyword"
      >using</a
      ><a name="623"
      > </a
      ><a name="624" class="Symbol"
      >(</a
      ><a name="625" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#484" class="Datatype"
      >Dec</a
      ><a name="628" class="Symbol"
      >;</a
      ><a name="629"
      > </a
      ><a name="630" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#520" class="InductiveConstructor"
      >yes</a
      ><a name="633" class="Symbol"
      >;</a
      ><a name="634"
      > </a
      ><a name="635" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#547" class="InductiveConstructor"
      >no</a
      ><a name="637" class="Symbol"
      >)</a
      ><a name="638"
      >
</a
      ><a name="639" class="Keyword"
      >open</a
      ><a name="643"
      > </a
      ><a name="644" class="Keyword"
      >import</a
      ><a name="650"
      > </a
      ><a name="651" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#1" class="Module"
      >Relation.Binary.PropositionalEquality</a
      ><a name="688"
      > </a
      ><a name="689" class="Keyword"
      >using</a
      ><a name="694"
      > </a
      ><a name="695" class="Symbol"
      >(</a
      ><a name="696" href="Agda.Builtin.Equality.html#55" class="Datatype Operator"
      >_&#8801;_</a
      ><a name="699" class="Symbol"
      >;</a
      ><a name="700"
      > </a
      ><a name="701" href="https://agda.github.io/agda-stdlib/Relation.Binary.Core.html#4493" class="Function Operator"
      >_&#8802;_</a
      ><a name="704" class="Symbol"
      >;</a
      ><a name="705"
      > </a
      ><a name="706" href="Agda.Builtin.Equality.html#112" class="InductiveConstructor"
      >refl</a
      ><a name="710" class="Symbol"
      >)</a
      >
</pre><!--{% endraw %}-->
</div>

# The Simply Typed Lambda-Calculus

The simply typed lambda-calculus (STLC) is a tiny core
calculus embodying the key concept of _functional abstraction_,
which shows up in pretty much every real-world programming
language in some form (functions, procedures, methods, etc.).

We will follow exactly the same pattern as in the previous chapter
when formalizing this calculus (syntax, small-step semantics,
typing rules) and its main properties (progress and preservation).
The new technical challenges arise from the mechanisms of
_variable binding_ and _substitution_.  It which will take some
work to deal with these.


## Overview

The STLC is built on some collection of _base types_:
booleans, numbers, strings, etc.  The exact choice of base types
doesn't matter much---the construction of the language and its
theoretical properties work out the same no matter what we
choose---so for the sake of brevity let's take just $$bool$$ for
the moment.  At the end of the chapter we'll see how to add more
base types, and in later chapters we'll enrich the pure STLC with
other useful constructs like pairs, records, subtyping, and
mutable state.

Starting from boolean constants and conditionals, we add three
things:

  - variables
  - function abstractions
  - application

This gives us the following collection of abstract syntax
constructors (written out first in informal BNF notation---we'll
formalize it below).

$$
  \begin{array}{rll}
    \text{Terms}\;s,t,u
    ::=  & x & \text{variable} \\
    \mid & \lambda x : A . t & \text{abstraction} \\
    \mid & s\;t & \text{application} \\
    \mid & true & \text{constant true} \\
    \mid & false & \text{constant false} \\
    \mid & \text{if }s\text{ then }t\text{ else }u & \text{conditional}
  \end{array}
$$

In a lambda abstraction $$\lambda x : A . t$$, the variable $$x$$ is called the
_parameter_ to the function; the term $$t$$ is its _body_.  The annotation $$:A$$
specifies the type of arguments that the function can be applied to.

Some examples:

  - The identity function for booleans:

    $$\lambda x:bool. x$$.
  - The identity function for booleans, applied to the boolean $$true$$:

    $$(\lambda x:bool. x)\;true$$.
  - The boolean "not" function:

    $$\lambda x:bool. \text{if }x\text{ then }false\text{ else }true$$.
  - The constant function that takes every (boolean) argument to $$true$$:

    $$\lambda x:bool. true$$.
  - A two-argument function that takes two booleans and returns the
    first one:

    $$\lambda x:bool. \lambda y:bool. x$$.

    As in Agda, a two-argument function is really a
    one-argument function whose body is also a one-argument function.
  - A two-argument function that takes two booleans and returns the
    first one, applied to the booleans $$false$$ and $$true$$:

    $$(\lambda x:bool. \lambda y:bool. x)\;false\;true$$.

    As in Agda, application associates to the left---i.e., this
    expression is parsed as

    $$((\lambda x:bool. \lambda y:bool. x)\;false)\;true$$.

  - A higher-order function that takes a _function_ $$f$$ (from booleans
    to booleans) as an argument, applies $$f$$ to $$true$$, and applies
    $$f$$ again to the result:

    $$\lambda f:bool\rightarrow bool. f\;(f\;true)$$.

  - The same higher-order function, applied to the constantly $$false$$
    function:

    $$(\lambda f:bool\rightarrow bool. f\;(f\;true))\;(\lambda x:bool. false)$$.

As the last several examples show, the STLC is a language of
_higher-order_ functions: we can write down functions that take
other functions as arguments and/or return other functions as
results.

The STLC doesn't provide any primitive syntax for defining _named_
functions---all functions are "anonymous."  We'll see in chapter
`MoreStlc` that it is easy to add named functions to what we've
got---indeed, the fundamental naming and binding mechanisms are
exactly the same.

The _types_ of the STLC include $$bool$$, which classifies the
boolean constants $$true$$ and $$false$$ as well as more complex
computations that yield booleans, plus _arrow types_ that classify
functions.

$$
    \text{Types}\;A,B ::= bool \mid A \rightarrow B
$$

For example:

  - $$\lambda x:bool. false$$ has type $$bool\rightarrow bool$$;
  - $$\lambda x:bool. x$$ has type $$bool\rightarrow bool$$;
  - $$(\lambda x:bool. x)\;true$$ has type $$bool$$;
  - $$\lambda x:bool. \lambda y:bool. x$$ has type
    $$bool\rightarrow bool\rightarrow bool$$
    (i.e., $$bool\rightarrow (bool\rightarrow bool)$$)
  - $$(\lambda x:bool. \lambda y:bool. x)\;false$$ has type $$bool\rightarrow bool$$
  - $$(\lambda x:bool. \lambda y:bool. x)\;false\;true$$ has type $$bool$$

## Syntax

We begin by formalizing the syntax of the STLC.
Unfortunately, $$\rightarrow$$ is already used for Agda's function type,
so we will STLC's function type as `_⇒_`.


### Types

<!--{% raw %}--><pre class="Agda">
<a name="5583" class="Keyword"
      >data</a
      ><a name="5587"
      > </a
      ><a name="5588" href="Stlc.html#5588" class="Datatype"
      >Type</a
      ><a name="5592"
      > </a
      ><a name="5593" class="Symbol"
      >:</a
      ><a name="5594"
      > </a
      ><a name="5595" class="PrimitiveType"
      >Set</a
      ><a name="5598"
      > </a
      ><a name="5599" class="Keyword"
      >where</a
      ><a name="5604"
      >
  </a
      ><a name="5607" href="Stlc.html#5607" class="InductiveConstructor"
      >bool</a
      ><a name="5611"
      > </a
      ><a name="5612" class="Symbol"
      >:</a
      ><a name="5613"
      > </a
      ><a name="5614" href="Stlc.html#5588" class="Datatype"
      >Type</a
      ><a name="5618"
      >
  </a
      ><a name="5621" href="Stlc.html#5621" class="InductiveConstructor Operator"
      >_&#8658;_</a
      ><a name="5624"
      >  </a
      ><a name="5626" class="Symbol"
      >:</a
      ><a name="5627"
      > </a
      ><a name="5628" href="Stlc.html#5588" class="Datatype"
      >Type</a
      ><a name="5632"
      > </a
      ><a name="5633" class="Symbol"
      >&#8594;</a
      ><a name="5634"
      > </a
      ><a name="5635" href="Stlc.html#5588" class="Datatype"
      >Type</a
      ><a name="5639"
      > </a
      ><a name="5640" class="Symbol"
      >&#8594;</a
      ><a name="5641"
      > </a
      ><a name="5642" href="Stlc.html#5588" class="Datatype"
      >Type</a
      >
</pre><!--{% endraw %}-->

<div class="hidden">
<!--{% raw %}--><pre class="Agda">
<a name="5693" class="Keyword"
      >infixr</a
      ><a name="5699"
      > </a
      ><a name="5700" class="Number"
      >5</a
      >
</pre><!--{% endraw %}-->
</div>


### Terms

<!--{% raw %}--><pre class="Agda">
<a name="5750" class="Keyword"
      >data</a
      ><a name="5754"
      > </a
      ><a name="5755" href="Stlc.html#5755" class="Datatype"
      >Term</a
      ><a name="5759"
      > </a
      ><a name="5760" class="Symbol"
      >:</a
      ><a name="5761"
      > </a
      ><a name="5762" class="PrimitiveType"
      >Set</a
      ><a name="5765"
      > </a
      ><a name="5766" class="Keyword"
      >where</a
      ><a name="5771"
      >
  </a
      ><a name="5774" href="Stlc.html#5774" class="InductiveConstructor"
      >var</a
      ><a name="5777"
      >   </a
      ><a name="5780" class="Symbol"
      >:</a
      ><a name="5781"
      > </a
      ><a name="5782" href="Maps.html#2400" class="Datatype"
      >Id</a
      ><a name="5784"
      > </a
      ><a name="5785" class="Symbol"
      >&#8594;</a
      ><a name="5786"
      > </a
      ><a name="5787" href="Stlc.html#5755" class="Datatype"
      >Term</a
      ><a name="5791"
      >
  </a
      ><a name="5794" href="Stlc.html#5794" class="InductiveConstructor"
      >app</a
      ><a name="5797"
      >   </a
      ><a name="5800" class="Symbol"
      >:</a
      ><a name="5801"
      > </a
      ><a name="5802" href="Stlc.html#5755" class="Datatype"
      >Term</a
      ><a name="5806"
      > </a
      ><a name="5807" class="Symbol"
      >&#8594;</a
      ><a name="5808"
      > </a
      ><a name="5809" href="Stlc.html#5755" class="Datatype"
      >Term</a
      ><a name="5813"
      > </a
      ><a name="5814" class="Symbol"
      >&#8594;</a
      ><a name="5815"
      > </a
      ><a name="5816" href="Stlc.html#5755" class="Datatype"
      >Term</a
      ><a name="5820"
      >
  </a
      ><a name="5823" href="Stlc.html#5823" class="InductiveConstructor"
      >abs</a
      ><a name="5826"
      >   </a
      ><a name="5829" class="Symbol"
      >:</a
      ><a name="5830"
      > </a
      ><a name="5831" href="Maps.html#2400" class="Datatype"
      >Id</a
      ><a name="5833"
      > </a
      ><a name="5834" class="Symbol"
      >&#8594;</a
      ><a name="5835"
      > </a
      ><a name="5836" href="Stlc.html#5588" class="Datatype"
      >Type</a
      ><a name="5840"
      > </a
      ><a name="5841" class="Symbol"
      >&#8594;</a
      ><a name="5842"
      > </a
      ><a name="5843" href="Stlc.html#5755" class="Datatype"
      >Term</a
      ><a name="5847"
      > </a
      ><a name="5848" class="Symbol"
      >&#8594;</a
      ><a name="5849"
      > </a
      ><a name="5850" href="Stlc.html#5755" class="Datatype"
      >Term</a
      ><a name="5854"
      >
  </a
      ><a name="5857" href="Stlc.html#5857" class="InductiveConstructor"
      >true</a
      ><a name="5861"
      >  </a
      ><a name="5863" class="Symbol"
      >:</a
      ><a name="5864"
      > </a
      ><a name="5865" href="Stlc.html#5755" class="Datatype"
      >Term</a
      ><a name="5869"
      >
  </a
      ><a name="5872" href="Stlc.html#5872" class="InductiveConstructor"
      >false</a
      ><a name="5877"
      > </a
      ><a name="5878" class="Symbol"
      >:</a
      ><a name="5879"
      > </a
      ><a name="5880" href="Stlc.html#5755" class="Datatype"
      >Term</a
      ><a name="5884"
      >
  </a
      ><a name="5887" href="Stlc.html#5887" class="InductiveConstructor Operator"
      >if_then_else_</a
      ><a name="5900"
      > </a
      ><a name="5901" class="Symbol"
      >:</a
      ><a name="5902"
      > </a
      ><a name="5903" href="Stlc.html#5755" class="Datatype"
      >Term</a
      ><a name="5907"
      > </a
      ><a name="5908" class="Symbol"
      >&#8594;</a
      ><a name="5909"
      > </a
      ><a name="5910" href="Stlc.html#5755" class="Datatype"
      >Term</a
      ><a name="5914"
      > </a
      ><a name="5915" class="Symbol"
      >&#8594;</a
      ><a name="5916"
      > </a
      ><a name="5917" href="Stlc.html#5755" class="Datatype"
      >Term</a
      ><a name="5921"
      > </a
      ><a name="5922" class="Symbol"
      >&#8594;</a
      ><a name="5923"
      > </a
      ><a name="5924" href="Stlc.html#5755" class="Datatype"
      >Term</a
      >
</pre><!--{% endraw %}-->

<div class="hidden">
<!--{% raw %}--><pre class="Agda">
<a name="5975" class="Keyword"
      >infixr</a
      ><a name="5981"
      > </a
      ><a name="5982" class="Number"
      >8</a
      >
</pre><!--{% endraw %}-->
</div>

Note that an abstraction $$\lambda x:A.t$$ (formally, `abs x A t`) is
always annotated with the type $$A$$ of its parameter, in contrast
to Agda (and other functional languages like ML, Haskell, etc.),
which use _type inference_ to fill in missing annotations.  We're
not considering type inference here.

Some examples...

<!--{% raw %}--><pre class="Agda">
<a name="6354" href="Stlc.html#6354" class="Function"
      >x</a
      ><a name="6355"
      > </a
      ><a name="6356" class="Symbol"
      >=</a
      ><a name="6357"
      > </a
      ><a name="6358" href="Maps.html#2417" class="InductiveConstructor"
      >id</a
      ><a name="6360"
      > </a
      ><a name="6361" class="Number"
      >0</a
      ><a name="6362"
      >
</a
      ><a name="6363" href="Stlc.html#6363" class="Function"
      >y</a
      ><a name="6364"
      > </a
      ><a name="6365" class="Symbol"
      >=</a
      ><a name="6366"
      > </a
      ><a name="6367" href="Maps.html#2417" class="InductiveConstructor"
      >id</a
      ><a name="6369"
      > </a
      ><a name="6370" class="Number"
      >1</a
      ><a name="6371"
      >
</a
      ><a name="6372" href="Stlc.html#6372" class="Function"
      >z</a
      ><a name="6373"
      > </a
      ><a name="6374" class="Symbol"
      >=</a
      ><a name="6375"
      > </a
      ><a name="6376" href="Maps.html#2417" class="InductiveConstructor"
      >id</a
      ><a name="6378"
      > </a
      ><a name="6379" class="Number"
      >2</a
      >
</pre><!--{% endraw %}-->

<div class="hidden">
<!--{% raw %}--><pre class="Agda">
<a name="6427" class="Symbol"
      >{-#</a
      ><a name="6430"
      > </a
      ><a name="6431" class="Keyword"
      >DISPLAY</a
      ><a name="6438"
      > </a
      ><a name="6439" href="Agda.Builtin.Nat.html#87" class="InductiveConstructor"
      >zero</a
      ><a name="6443"
      > = </a
      ><a name="6446" href="Stlc.html#6354" class="Function"
      >x</a
      ><a name="6447"
      > </a
      ><a name="6448" class="Symbol"
      >#-}</a
      ><a name="6451"
      >
</a
      ><a name="6452" class="Symbol"
      >{-#</a
      ><a name="6455"
      > </a
      ><a name="6456" class="Keyword"
      >DISPLAY</a
      ><a name="6463"
      > </a
      ><a name="6464" href="Agda.Builtin.Nat.html#100" class="InductiveConstructor"
      >suc</a
      ><a name="6467"
      > </a
      ><a name="6468" href="Agda.Builtin.Nat.html#87" class="InductiveConstructor"
      >zero</a
      ><a name="6472"
      > = </a
      ><a name="6475" href="Stlc.html#6363" class="Function"
      >y</a
      ><a name="6476"
      > </a
      ><a name="6477" class="Symbol"
      >#-}</a
      ><a name="6480"
      >
</a
      ><a name="6481" class="Symbol"
      >{-#</a
      ><a name="6484"
      > </a
      ><a name="6485" class="Keyword"
      >DISPLAY</a
      ><a name="6492"
      > </a
      ><a name="6493" href="Agda.Builtin.Nat.html#100" class="InductiveConstructor"
      >suc</a
      ><a name="6496"
      > (</a
      ><a name="6498" href="Agda.Builtin.Nat.html#100" class="InductiveConstructor"
      >suc</a
      ><a name="6501"
      > </a
      ><a name="6502" href="Agda.Builtin.Nat.html#87" class="InductiveConstructor"
      >zero</a
      ><a name="6506"
      >) = </a
      ><a name="6510" href="Stlc.html#6372" class="Function"
      >z</a
      ><a name="6511"
      > </a
      ><a name="6512" class="Symbol"
      >#-}</a
      >
</pre><!--{% endraw %}-->
</div>

$$\text{idB} = \lambda x:bool. x$$.

<!--{% raw %}--><pre class="Agda">
<a name="6585" href="Stlc.html#6585" class="Function"
      >idB</a
      ><a name="6588"
      > </a
      ><a name="6589" class="Symbol"
      >=</a
      ><a name="6590"
      > </a
      ><a name="6591" class="Symbol"
      >(</a
      ><a name="6592" href="Stlc.html#5823" class="InductiveConstructor"
      >abs</a
      ><a name="6595"
      > </a
      ><a name="6596" href="Stlc.html#6354" class="Function"
      >x</a
      ><a name="6597"
      > </a
      ><a name="6598" href="Stlc.html#5607" class="InductiveConstructor"
      >bool</a
      ><a name="6602"
      > </a
      ><a name="6603" class="Symbol"
      >(</a
      ><a name="6604" href="Stlc.html#5774" class="InductiveConstructor"
      >var</a
      ><a name="6607"
      > </a
      ><a name="6608" href="Stlc.html#6354" class="Function"
      >x</a
      ><a name="6609" class="Symbol"
      >))</a
      >
</pre><!--{% endraw %}-->

$$\text{idBB} = \lambda x:bool\rightarrow bool. x$$.

<!--{% raw %}--><pre class="Agda">
<a name="6691" href="Stlc.html#6691" class="Function"
      >idBB</a
      ><a name="6695"
      > </a
      ><a name="6696" class="Symbol"
      >=</a
      ><a name="6697"
      > </a
      ><a name="6698" class="Symbol"
      >(</a
      ><a name="6699" href="Stlc.html#5823" class="InductiveConstructor"
      >abs</a
      ><a name="6702"
      > </a
      ><a name="6703" href="Stlc.html#6354" class="Function"
      >x</a
      ><a name="6704"
      > </a
      ><a name="6705" class="Symbol"
      >(</a
      ><a name="6706" href="Stlc.html#5607" class="InductiveConstructor"
      >bool</a
      ><a name="6710"
      > </a
      ><a name="6711" href="Stlc.html#5621" class="InductiveConstructor Operator"
      >&#8658;</a
      ><a name="6712"
      > </a
      ><a name="6713" href="Stlc.html#5607" class="InductiveConstructor"
      >bool</a
      ><a name="6717" class="Symbol"
      >)</a
      ><a name="6718"
      > </a
      ><a name="6719" class="Symbol"
      >(</a
      ><a name="6720" href="Stlc.html#5774" class="InductiveConstructor"
      >var</a
      ><a name="6723"
      > </a
      ><a name="6724" href="Stlc.html#6354" class="Function"
      >x</a
      ><a name="6725" class="Symbol"
      >))</a
      >
</pre><!--{% endraw %}-->

$$\text{idBBBB} = \lambda x:(bool\rightarrow bool)\rightarrow (bool\rightarrow bool). x$$.

<!--{% raw %}--><pre class="Agda">
<a name="6845" href="Stlc.html#6845" class="Function"
      >idBBBB</a
      ><a name="6851"
      > </a
      ><a name="6852" class="Symbol"
      >=</a
      ><a name="6853"
      > </a
      ><a name="6854" class="Symbol"
      >(</a
      ><a name="6855" href="Stlc.html#5823" class="InductiveConstructor"
      >abs</a
      ><a name="6858"
      > </a
      ><a name="6859" href="Stlc.html#6354" class="Function"
      >x</a
      ><a name="6860"
      > </a
      ><a name="6861" class="Symbol"
      >((</a
      ><a name="6863" href="Stlc.html#5607" class="InductiveConstructor"
      >bool</a
      ><a name="6867"
      > </a
      ><a name="6868" href="Stlc.html#5621" class="InductiveConstructor Operator"
      >&#8658;</a
      ><a name="6869"
      > </a
      ><a name="6870" href="Stlc.html#5607" class="InductiveConstructor"
      >bool</a
      ><a name="6874" class="Symbol"
      >)</a
      ><a name="6875"
      > </a
      ><a name="6876" href="Stlc.html#5621" class="InductiveConstructor Operator"
      >&#8658;</a
      ><a name="6877"
      > </a
      ><a name="6878" class="Symbol"
      >(</a
      ><a name="6879" href="Stlc.html#5607" class="InductiveConstructor"
      >bool</a
      ><a name="6883"
      > </a
      ><a name="6884" href="Stlc.html#5621" class="InductiveConstructor Operator"
      >&#8658;</a
      ><a name="6885"
      > </a
      ><a name="6886" href="Stlc.html#5607" class="InductiveConstructor"
      >bool</a
      ><a name="6890" class="Symbol"
      >))</a
      ><a name="6892"
      > </a
      ><a name="6893" class="Symbol"
      >(</a
      ><a name="6894" href="Stlc.html#5774" class="InductiveConstructor"
      >var</a
      ><a name="6897"
      > </a
      ><a name="6898" href="Stlc.html#6354" class="Function"
      >x</a
      ><a name="6899" class="Symbol"
      >))</a
      >
</pre><!--{% endraw %}-->

$$\text{k} = \lambda x:bool. \lambda y:bool. x$$.

<!--{% raw %}--><pre class="Agda">
<a name="6978" href="Stlc.html#6978" class="Function"
      >k</a
      ><a name="6979"
      > </a
      ><a name="6980" class="Symbol"
      >=</a
      ><a name="6981"
      > </a
      ><a name="6982" class="Symbol"
      >(</a
      ><a name="6983" href="Stlc.html#5823" class="InductiveConstructor"
      >abs</a
      ><a name="6986"
      > </a
      ><a name="6987" href="Stlc.html#6354" class="Function"
      >x</a
      ><a name="6988"
      > </a
      ><a name="6989" href="Stlc.html#5607" class="InductiveConstructor"
      >bool</a
      ><a name="6993"
      > </a
      ><a name="6994" class="Symbol"
      >(</a
      ><a name="6995" href="Stlc.html#5823" class="InductiveConstructor"
      >abs</a
      ><a name="6998"
      > </a
      ><a name="6999" href="Stlc.html#6363" class="Function"
      >y</a
      ><a name="7000"
      > </a
      ><a name="7001" href="Stlc.html#5607" class="InductiveConstructor"
      >bool</a
      ><a name="7005"
      > </a
      ><a name="7006" class="Symbol"
      >(</a
      ><a name="7007" href="Stlc.html#5774" class="InductiveConstructor"
      >var</a
      ><a name="7010"
      > </a
      ><a name="7011" href="Stlc.html#6354" class="Function"
      >x</a
      ><a name="7012" class="Symbol"
      >)))</a
      >
</pre><!--{% endraw %}-->

$$\text{notB} = \lambda x:bool. \text{if }x\text{ then }false\text{ else }true$$.

<!--{% raw %}--><pre class="Agda">
<a name="7124" href="Stlc.html#7124" class="Function"
      >notB</a
      ><a name="7128"
      > </a
      ><a name="7129" class="Symbol"
      >=</a
      ><a name="7130"
      > </a
      ><a name="7131" class="Symbol"
      >(</a
      ><a name="7132" href="Stlc.html#5823" class="InductiveConstructor"
      >abs</a
      ><a name="7135"
      > </a
      ><a name="7136" href="Stlc.html#6354" class="Function"
      >x</a
      ><a name="7137"
      > </a
      ><a name="7138" href="Stlc.html#5607" class="InductiveConstructor"
      >bool</a
      ><a name="7142"
      > </a
      ><a name="7143" class="Symbol"
      >(</a
      ><a name="7144" href="Stlc.html#5887" class="InductiveConstructor Operator"
      >if</a
      ><a name="7146"
      > </a
      ><a name="7147" class="Symbol"
      >(</a
      ><a name="7148" href="Stlc.html#5774" class="InductiveConstructor"
      >var</a
      ><a name="7151"
      > </a
      ><a name="7152" href="Stlc.html#6354" class="Function"
      >x</a
      ><a name="7153" class="Symbol"
      >)</a
      ><a name="7154"
      > </a
      ><a name="7155" href="Stlc.html#5887" class="InductiveConstructor Operator"
      >then</a
      ><a name="7159"
      > </a
      ><a name="7160" href="Stlc.html#5872" class="InductiveConstructor"
      >false</a
      ><a name="7165"
      > </a
      ><a name="7166" href="Stlc.html#5887" class="InductiveConstructor Operator"
      >else</a
      ><a name="7170"
      > </a
      ><a name="7171" href="Stlc.html#5857" class="InductiveConstructor"
      >true</a
      ><a name="7175" class="Symbol"
      >))</a
      >
</pre><!--{% endraw %}-->

<div class="hidden">
<!--{% raw %}--><pre class="Agda">
<a name="7224" class="Symbol"
      >{-#</a
      ><a name="7227"
      > </a
      ><a name="7228" class="Keyword"
      >DISPLAY</a
      ><a name="7235"
      > </a
      ><a name="7236" href="Stlc.html#5823" class="InductiveConstructor"
      >abs</a
      ><a name="7239"
      > 0 </a
      ><a name="7242" href="Stlc.html#5607" class="InductiveConstructor"
      >bool</a
      ><a name="7246"
      > (</a
      ><a name="7248" href="Stlc.html#5774" class="InductiveConstructor"
      >var</a
      ><a name="7251"
      > 0) = </a
      ><a name="7257" href="Stlc.html#6585" class="Function"
      >idB</a
      ><a name="7260"
      > </a
      ><a name="7261" class="Symbol"
      >#-}</a
      ><a name="7264"
      >
</a
      ><a name="7265" class="Symbol"
      >{-#</a
      ><a name="7268"
      > </a
      ><a name="7269" class="Keyword"
      >DISPLAY</a
      ><a name="7276"
      > </a
      ><a name="7277" href="Stlc.html#5823" class="InductiveConstructor"
      >abs</a
      ><a name="7280"
      > 0 (</a
      ><a name="7284" href="Stlc.html#5607" class="InductiveConstructor"
      >bool</a
      ><a name="7288"
      > </a
      ><a name="7289" href="Stlc.html#5621" class="InductiveConstructor Operator"
      >&#8658;</a
      ><a name="7290"
      > </a
      ><a name="7291" href="Stlc.html#5607" class="InductiveConstructor"
      >bool</a
      ><a name="7295"
      >) (</a
      ><a name="7298" href="Stlc.html#5774" class="InductiveConstructor"
      >var</a
      ><a name="7301"
      > 0) = </a
      ><a name="7307" href="Stlc.html#6691" class="Function"
      >idBB</a
      ><a name="7311"
      > </a
      ><a name="7312" class="Symbol"
      >#-}</a
      ><a name="7315"
      >
</a
      ><a name="7316" class="Symbol"
      >{-#</a
      ><a name="7319"
      > </a
      ><a name="7320" class="Keyword"
      >DISPLAY</a
      ><a name="7327"
      > </a
      ><a name="7328" href="Stlc.html#5823" class="InductiveConstructor"
      >abs</a
      ><a name="7331"
      > 0 ((</a
      ><a name="7336" href="Stlc.html#5607" class="InductiveConstructor"
      >bool</a
      ><a name="7340"
      > </a
      ><a name="7341" href="Stlc.html#5621" class="InductiveConstructor Operator"
      >&#8658;</a
      ><a name="7342"
      > </a
      ><a name="7343" href="Stlc.html#5607" class="InductiveConstructor"
      >bool</a
      ><a name="7347"
      >) </a
      ><a name="7349" href="Stlc.html#5621" class="InductiveConstructor Operator"
      >&#8658;</a
      ><a name="7350"
      > (</a
      ><a name="7352" href="Stlc.html#5607" class="InductiveConstructor"
      >bool</a
      ><a name="7356"
      > </a
      ><a name="7357" href="Stlc.html#5621" class="InductiveConstructor Operator"
      >&#8658;</a
      ><a name="7358"
      > </a
      ><a name="7359" href="Stlc.html#5607" class="InductiveConstructor"
      >bool</a
      ><a name="7363"
      >)) (</a
      ><a name="7367" href="Stlc.html#5774" class="InductiveConstructor"
      >var</a
      ><a name="7370"
      > 0) = </a
      ><a name="7376" href="Stlc.html#6845" class="Function"
      >idBBBB</a
      ><a name="7382"
      > </a
      ><a name="7383" class="Symbol"
      >#-}</a
      ><a name="7386"
      >
</a
      ><a name="7387" class="Symbol"
      >{-#</a
      ><a name="7390"
      > </a
      ><a name="7391" class="Keyword"
      >DISPLAY</a
      ><a name="7398"
      > </a
      ><a name="7399" href="Stlc.html#5823" class="InductiveConstructor"
      >abs</a
      ><a name="7402"
      > 0 </a
      ><a name="7405" href="Stlc.html#5607" class="InductiveConstructor"
      >bool</a
      ><a name="7409"
      > (</a
      ><a name="7411" href="Stlc.html#5823" class="InductiveConstructor"
      >abs</a
      ><a name="7414"
      > </a
      ><a name="7415" href="Stlc.html#7415" class="Bound"
      >y</a
      ><a name="7416"
      > </a
      ><a name="7417" href="Stlc.html#5607" class="InductiveConstructor"
      >bool</a
      ><a name="7421"
      > (</a
      ><a name="7423" href="Stlc.html#5774" class="InductiveConstructor"
      >var</a
      ><a name="7426"
      > 0)) = </a
      ><a name="7433" href="Stlc.html#6978" class="Function"
      >k</a
      ><a name="7434"
      > </a
      ><a name="7435" class="Symbol"
      >#-}</a
      ><a name="7438"
      >
</a
      ><a name="7439" class="Symbol"
      >{-#</a
      ><a name="7442"
      > </a
      ><a name="7443" class="Keyword"
      >DISPLAY</a
      ><a name="7450"
      > </a
      ><a name="7451" href="Stlc.html#5823" class="InductiveConstructor"
      >abs</a
      ><a name="7454"
      > 0 </a
      ><a name="7457" href="Stlc.html#5607" class="InductiveConstructor"
      >bool</a
      ><a name="7461"
      > (</a
      ><a name="7463" href="Stlc.html#5887" class="InductiveConstructor Operator"
      >if</a
      ><a name="7465"
      > (</a
      ><a name="7467" href="Stlc.html#5774" class="InductiveConstructor"
      >var</a
      ><a name="7470"
      > 0) </a
      ><a name="7474" href="Stlc.html#5887" class="InductiveConstructor Operator"
      >then</a
      ><a name="7478"
      > </a
      ><a name="7479" href="Stlc.html#5872" class="InductiveConstructor"
      >false</a
      ><a name="7484"
      > </a
      ><a name="7485" href="Stlc.html#5887" class="InductiveConstructor Operator"
      >else</a
      ><a name="7489"
      > </a
      ><a name="7490" href="Stlc.html#5857" class="InductiveConstructor"
      >true</a
      ><a name="7494"
      >) = </a
      ><a name="7498" href="Stlc.html#7124" class="Function"
      >notB</a
      ><a name="7502"
      > </a
      ><a name="7503" class="Symbol"
      >#-}</a
      >
</pre><!--{% endraw %}-->
</div>

## Operational Semantics

To define the small-step semantics of STLC terms, we begin,
as always, by defining the set of values.  Next, we define the
critical notions of _free variables_ and _substitution_, which are
used in the reduction rule for application expressions.  And
finally we give the small-step relation itself.

### Values

To define the values of the STLC, we have a few cases to consider.

First, for the boolean part of the language, the situation is
clear: $$true$$ and $$false$$ are the only values.  An $$\text{if}$$
expression is never a value.

Second, an application is clearly not a value: It represents a
function being invoked on some argument, which clearly still has
work left to do.

Third, for abstractions, we have a choice:

  - We can say that $$\lambda x:A. t$$ is a value only when $$t$$ is a
    value---i.e., only if the function's body has been
    reduced (as much as it can be without knowing what argument it
    is going to be applied to).

  - Or we can say that $$\lambda x:A. t$$ is always a value, no matter
    whether $$t$$ is one or not---in other words, we can say that
    reduction stops at abstractions.

Agda makes the first choice---for example,

<!--{% raw %}--><pre class="Agda">
<a name="8741" href="Stlc.html#8741" class="Function Operator"
      >test_normalizeUnderLambda</a
      ><a name="8766"
      > </a
      ><a name="8767" class="Symbol"
      >:</a
      ><a name="8768"
      > </a
      ><a name="8769" class="Symbol"
      >(&#955;</a
      ><a name="8771"
      > </a
      ><a name="8772" class="Symbol"
      >(</a
      ><a name="8773" href="Stlc.html#8773" class="Bound"
      >x</a
      ><a name="8774"
      > </a
      ><a name="8775" class="Symbol"
      >:</a
      ><a name="8776"
      > </a
      ><a name="8777" href="Agda.Builtin.Nat.html#69" class="Datatype"
      >&#8469;</a
      ><a name="8778" class="Symbol"
      >)</a
      ><a name="8779"
      > </a
      ><a name="8780" class="Symbol"
      >&#8594;</a
      ><a name="8781"
      > </a
      ><a name="8782" class="Number"
      >3</a
      ><a name="8783"
      > </a
      ><a name="8784" href="Agda.Builtin.Nat.html#202" class="Primitive Operator"
      >+</a
      ><a name="8785"
      > </a
      ><a name="8786" class="Number"
      >4</a
      ><a name="8787" class="Symbol"
      >)</a
      ><a name="8788"
      > </a
      ><a name="8789" href="Agda.Builtin.Equality.html#55" class="Datatype Operator"
      >&#8801;</a
      ><a name="8790"
      > </a
      ><a name="8791" class="Symbol"
      >(&#955;</a
      ><a name="8793"
      > </a
      ><a name="8794" class="Symbol"
      >(</a
      ><a name="8795" href="Stlc.html#8795" class="Bound"
      >x</a
      ><a name="8796"
      > </a
      ><a name="8797" class="Symbol"
      >:</a
      ><a name="8798"
      > </a
      ><a name="8799" href="Agda.Builtin.Nat.html#69" class="Datatype"
      >&#8469;</a
      ><a name="8800" class="Symbol"
      >)</a
      ><a name="8801"
      > </a
      ><a name="8802" class="Symbol"
      >&#8594;</a
      ><a name="8803"
      > </a
      ><a name="8804" class="Number"
      >7</a
      ><a name="8805" class="Symbol"
      >)</a
      ><a name="8806"
      >
</a
      ><a name="8807" href="Stlc.html#8741" class="Function Operator"
      >test_normalizeUnderLambda</a
      ><a name="8832"
      > </a
      ><a name="8833" class="Symbol"
      >=</a
      ><a name="8834"
      > </a
      ><a name="8835" href="Agda.Builtin.Equality.html#112" class="InductiveConstructor"
      >refl</a
      >
</pre><!--{% endraw %}-->

Most real-world functional programming languages make the second
choice---reduction of a function's body only begins when the
function is actually applied to an argument.  We also make the
second choice here.

<!--{% raw %}--><pre class="Agda">
<a name="9075" class="Keyword"
      >data</a
      ><a name="9079"
      > </a
      ><a name="9080" href="Stlc.html#9080" class="Datatype"
      >Value</a
      ><a name="9085"
      > </a
      ><a name="9086" class="Symbol"
      >:</a
      ><a name="9087"
      > </a
      ><a name="9088" href="Stlc.html#5755" class="Datatype"
      >Term</a
      ><a name="9092"
      > </a
      ><a name="9093" class="Symbol"
      >&#8594;</a
      ><a name="9094"
      > </a
      ><a name="9095" class="PrimitiveType"
      >Set</a
      ><a name="9098"
      > </a
      ><a name="9099" class="Keyword"
      >where</a
      ><a name="9104"
      >
  </a
      ><a name="9107" href="Stlc.html#9107" class="InductiveConstructor"
      >abs</a
      ><a name="9110"
      >   </a
      ><a name="9113" class="Symbol"
      >:</a
      ><a name="9114"
      > </a
      ><a name="9115" class="Symbol"
      >&#8704;</a
      ><a name="9116"
      > </a
      ><a name="9117" class="Symbol"
      >{</a
      ><a name="9118" href="Stlc.html#9118" class="Bound"
      >x</a
      ><a name="9119"
      > </a
      ><a name="9120" href="Stlc.html#9120" class="Bound"
      >A</a
      ><a name="9121"
      > </a
      ><a name="9122" href="Stlc.html#9122" class="Bound"
      >t</a
      ><a name="9123" class="Symbol"
      >}</a
      ><a name="9124"
      >
        </a
      ><a name="9133" class="Symbol"
      >&#8594;</a
      ><a name="9134"
      > </a
      ><a name="9135" href="Stlc.html#9080" class="Datatype"
      >Value</a
      ><a name="9140"
      > </a
      ><a name="9141" class="Symbol"
      >(</a
      ><a name="9142" href="Stlc.html#5823" class="InductiveConstructor"
      >abs</a
      ><a name="9145"
      > </a
      ><a name="9146" href="Stlc.html#9118" class="Bound"
      >x</a
      ><a name="9147"
      > </a
      ><a name="9148" href="Stlc.html#9120" class="Bound"
      >A</a
      ><a name="9149"
      > </a
      ><a name="9150" href="Stlc.html#9122" class="Bound"
      >t</a
      ><a name="9151" class="Symbol"
      >)</a
      ><a name="9152"
      >
  </a
      ><a name="9155" href="Stlc.html#9155" class="InductiveConstructor"
      >true</a
      ><a name="9159"
      >  </a
      ><a name="9161" class="Symbol"
      >:</a
      ><a name="9162"
      > </a
      ><a name="9163" href="Stlc.html#9080" class="Datatype"
      >Value</a
      ><a name="9168"
      > </a
      ><a name="9169" href="Stlc.html#5857" class="InductiveConstructor"
      >true</a
      ><a name="9173"
      >
  </a
      ><a name="9176" href="Stlc.html#9176" class="InductiveConstructor"
      >false</a
      ><a name="9181"
      > </a
      ><a name="9182" class="Symbol"
      >:</a
      ><a name="9183"
      > </a
      ><a name="9184" href="Stlc.html#9080" class="Datatype"
      >Value</a
      ><a name="9189"
      > </a
      ><a name="9190" href="Stlc.html#5872" class="InductiveConstructor"
      >false</a
      >
</pre><!--{% endraw %}-->

Finally, we must consider what constitutes a _complete_ program.

Intuitively, a "complete program" must not refer to any undefined
variables.  We'll see shortly how to define the _free_ variables
in a STLC term.  A complete program is _closed_---that is, it
contains no free variables.

Having made the choice not to reduce under abstractions, we don't
need to worry about whether variables are values, since we'll
always be reducing programs "from the outside in," and that means
the small-step relation will always be working with closed terms.


### Substitution

Now we come to the heart of the STLC: the operation of
substituting one term for a variable in another term.  This
operation is used below to define the operational semantics of
function application, where we will need to substitute the
argument term for the function parameter in the function's body.
For example, we reduce

$$(\lambda x:bool. \text{if }x\text{ then }true\text{ else }x)\;false$$

to

$$\text{if }false\text{ then }true\text{ else }false$$

by substituting $$false$$ for the parameter $$x$$ in the body of the
function.

In general, we need to be able to substitute some given term $$s$$
for occurrences of some variable $$x$$ in another term $$t$$.  In
informal discussions, this is usually written $$[x:=s]t$$ and
pronounced "substitute $$x$$ with $$s$$ in $$t$$."

Here are some examples:

  - $$[x:=true](\text{if }x\text{ then }x\text{ else }false)$$
     yields $$\text{if }true\text{ then }true\text{ else }false$$

  - $$[x:=true]x$$
    yields $$true$$

  - $$[x:=true](\text{if }x\text{ then }x\text{ else }y)$$
    yields $$\text{if }true\text{ then }true\text{ else }y$$

  - $$[x:=true]y$$
    yields $$y$$

  - $$[x:=true]false$$
    yields $$false$$ (vacuous substitution)

  - $$[x:=true](\lambda y:bool. \text{if }y\text{ then }x\text{ else }false)$$
    yields $$\lambda y:bool. \text{if }y\text{ then }true\text{ else }false$$

  - $$[x:=true](\lambda y:bool. x)$$
    yields $$\lambda y:bool. true$$

  - $$[x:=true](\lambda y:bool. y)$$
    yields $$\lambda y:bool. y$$

  - $$[x:=true](\lambda x:bool. x)$$
    yields $$\lambda x:bool. x$$

The last example is very important: substituting $$x$$ with $$true$$ in
$$\lambda x:bool. x$$ does _not_ yield $$\lambda x:bool. true$$!  The reason for
this is that the $$x$$ in the body of $$\lambda x:bool. x$$ is _bound_ by the
abstraction: it is a new, local name that just happens to be
spelled the same as some global name $$x$$.

Here is the definition, informally...

$$
  \begin{aligned}
    &[x:=s]x                &&= s \\
    &[x:=s]y                &&= y \;\{\text{if }x\neq y\} \\
    &[x:=s](\lambda x:A. t) &&= \lambda x:A. t \\
    &[x:=s](\lambda y:A. t) &&= \lambda y:A. [x:=s]t \;\{\text{if }x\neq y\} \\
    &[x:=s](t1\;t2)         &&= ([x:=s]t1) ([x:=s]t2) \\
    &[x:=s]true             &&= true \\
    &[x:=s]false            &&= false \\
    &[x:=s](\text{if }t1\text{ then }t2\text{ else }t3) &&=
       \text{if }[x:=s]t1\text{ then }[x:=s]t2\text{ else }[x:=s]t3
  \end{aligned}
$$

... and formally:

<!--{% raw %}--><pre class="Agda">
<a name="12300" href="Stlc.html#12300" class="Function Operator"
      >[_:=_]_</a
      ><a name="12307"
      > </a
      ><a name="12308" class="Symbol"
      >:</a
      ><a name="12309"
      > </a
      ><a name="12310" href="Maps.html#2400" class="Datatype"
      >Id</a
      ><a name="12312"
      > </a
      ><a name="12313" class="Symbol"
      >-&gt;</a
      ><a name="12315"
      > </a
      ><a name="12316" href="Stlc.html#5755" class="Datatype"
      >Term</a
      ><a name="12320"
      > </a
      ><a name="12321" class="Symbol"
      >-&gt;</a
      ><a name="12323"
      > </a
      ><a name="12324" href="Stlc.html#5755" class="Datatype"
      >Term</a
      ><a name="12328"
      > </a
      ><a name="12329" class="Symbol"
      >-&gt;</a
      ><a name="12331"
      > </a
      ><a name="12332" href="Stlc.html#5755" class="Datatype"
      >Term</a
      ><a name="12336"
      >
</a
      ><a name="12337" href="Stlc.html#12300" class="Function Operator"
      >[</a
      ><a name="12338"
      > </a
      ><a name="12339" href="Stlc.html#12339" class="Bound"
      >x</a
      ><a name="12340"
      > </a
      ><a name="12341" href="Stlc.html#12300" class="Function Operator"
      >:=</a
      ><a name="12343"
      > </a
      ><a name="12344" href="Stlc.html#12344" class="Bound"
      >v</a
      ><a name="12345"
      > </a
      ><a name="12346" href="Stlc.html#12300" class="Function Operator"
      >]</a
      ><a name="12347"
      > </a
      ><a name="12348" class="Symbol"
      >(</a
      ><a name="12349" href="Stlc.html#5774" class="InductiveConstructor"
      >var</a
      ><a name="12352"
      > </a
      ><a name="12353" href="Stlc.html#12353" class="Bound"
      >y</a
      ><a name="12354" class="Symbol"
      >)</a
      ><a name="12355"
      > </a
      ><a name="12356" class="Keyword"
      >with</a
      ><a name="12360"
      > </a
      ><a name="12361" href="Stlc.html#12339" class="Bound"
      >x</a
      ><a name="12362"
      > </a
      ><a name="12363" href="Maps.html#2454" class="Function Operator"
      >&#8799;</a
      ><a name="12364"
      > </a
      ><a name="12365" href="Stlc.html#12353" class="Bound"
      >y</a
      ><a name="12366"
      >
</a
      ><a name="12367" class="Symbol"
      >...</a
      ><a name="12370"
      > </a
      ><a name="12371" class="Symbol"
      >|</a
      ><a name="12372"
      > </a
      ><a name="12373" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#520" class="InductiveConstructor"
      >yes</a
      ><a name="12376"
      > </a
      ><a name="12377" href="Stlc.html#12377" class="Bound"
      >x=y</a
      ><a name="12380"
      > </a
      ><a name="12381" class="Symbol"
      >=</a
      ><a name="12382"
      > </a
      ><a name="12383" href="Stlc.html#12344" class="Bound"
      >v</a
      ><a name="12384"
      >
</a
      ><a name="12385" class="Symbol"
      >...</a
      ><a name="12388"
      > </a
      ><a name="12389" class="Symbol"
      >|</a
      ><a name="12390"
      > </a
      ><a name="12391" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#547" class="InductiveConstructor"
      >no</a
      ><a name="12393"
      >  </a
      ><a name="12395" href="Stlc.html#12395" class="Bound"
      >x&#8800;y</a
      ><a name="12398"
      > </a
      ><a name="12399" class="Symbol"
      >=</a
      ><a name="12400"
      > </a
      ><a name="12401" href="Stlc.html#5774" class="InductiveConstructor"
      >var</a
      ><a name="12404"
      > </a
      ><a name="12405" href="Stlc.html#12353" class="Bound"
      >y</a
      ><a name="12406"
      >
</a
      ><a name="12407" href="Stlc.html#12300" class="Function Operator"
      >[</a
      ><a name="12408"
      > </a
      ><a name="12409" href="Stlc.html#12409" class="Bound"
      >x</a
      ><a name="12410"
      > </a
      ><a name="12411" href="Stlc.html#12300" class="Function Operator"
      >:=</a
      ><a name="12413"
      > </a
      ><a name="12414" href="Stlc.html#12414" class="Bound"
      >v</a
      ><a name="12415"
      > </a
      ><a name="12416" href="Stlc.html#12300" class="Function Operator"
      >]</a
      ><a name="12417"
      > </a
      ><a name="12418" class="Symbol"
      >(</a
      ><a name="12419" href="Stlc.html#5794" class="InductiveConstructor"
      >app</a
      ><a name="12422"
      > </a
      ><a name="12423" href="Stlc.html#12423" class="Bound"
      >s</a
      ><a name="12424"
      > </a
      ><a name="12425" href="Stlc.html#12425" class="Bound"
      >t</a
      ><a name="12426" class="Symbol"
      >)</a
      ><a name="12427"
      > </a
      ><a name="12428" class="Symbol"
      >=</a
      ><a name="12429"
      > </a
      ><a name="12430" href="Stlc.html#5794" class="InductiveConstructor"
      >app</a
      ><a name="12433"
      > </a
      ><a name="12434" class="Symbol"
      >(</a
      ><a name="12435" href="Stlc.html#12300" class="Function Operator"
      >[</a
      ><a name="12436"
      > </a
      ><a name="12437" href="Stlc.html#12409" class="Bound"
      >x</a
      ><a name="12438"
      > </a
      ><a name="12439" href="Stlc.html#12300" class="Function Operator"
      >:=</a
      ><a name="12441"
      > </a
      ><a name="12442" href="Stlc.html#12414" class="Bound"
      >v</a
      ><a name="12443"
      > </a
      ><a name="12444" href="Stlc.html#12300" class="Function Operator"
      >]</a
      ><a name="12445"
      > </a
      ><a name="12446" href="Stlc.html#12423" class="Bound"
      >s</a
      ><a name="12447" class="Symbol"
      >)</a
      ><a name="12448"
      > </a
      ><a name="12449" class="Symbol"
      >(</a
      ><a name="12450" href="Stlc.html#12300" class="Function Operator"
      >[</a
      ><a name="12451"
      > </a
      ><a name="12452" href="Stlc.html#12409" class="Bound"
      >x</a
      ><a name="12453"
      > </a
      ><a name="12454" href="Stlc.html#12300" class="Function Operator"
      >:=</a
      ><a name="12456"
      > </a
      ><a name="12457" href="Stlc.html#12414" class="Bound"
      >v</a
      ><a name="12458"
      > </a
      ><a name="12459" href="Stlc.html#12300" class="Function Operator"
      >]</a
      ><a name="12460"
      > </a
      ><a name="12461" href="Stlc.html#12425" class="Bound"
      >t</a
      ><a name="12462" class="Symbol"
      >)</a
      ><a name="12463"
      >
</a
      ><a name="12464" href="Stlc.html#12300" class="Function Operator"
      >[</a
      ><a name="12465"
      > </a
      ><a name="12466" href="Stlc.html#12466" class="Bound"
      >x</a
      ><a name="12467"
      > </a
      ><a name="12468" href="Stlc.html#12300" class="Function Operator"
      >:=</a
      ><a name="12470"
      > </a
      ><a name="12471" href="Stlc.html#12471" class="Bound"
      >v</a
      ><a name="12472"
      > </a
      ><a name="12473" href="Stlc.html#12300" class="Function Operator"
      >]</a
      ><a name="12474"
      > </a
      ><a name="12475" class="Symbol"
      >(</a
      ><a name="12476" href="Stlc.html#5823" class="InductiveConstructor"
      >abs</a
      ><a name="12479"
      > </a
      ><a name="12480" href="Stlc.html#12480" class="Bound"
      >y</a
      ><a name="12481"
      > </a
      ><a name="12482" href="Stlc.html#12482" class="Bound"
      >A</a
      ><a name="12483"
      > </a
      ><a name="12484" href="Stlc.html#12484" class="Bound"
      >t</a
      ><a name="12485" class="Symbol"
      >)</a
      ><a name="12486"
      > </a
      ><a name="12487" class="Keyword"
      >with</a
      ><a name="12491"
      > </a
      ><a name="12492" href="Stlc.html#12466" class="Bound"
      >x</a
      ><a name="12493"
      > </a
      ><a name="12494" href="Maps.html#2454" class="Function Operator"
      >&#8799;</a
      ><a name="12495"
      > </a
      ><a name="12496" href="Stlc.html#12480" class="Bound"
      >y</a
      ><a name="12497"
      >
</a
      ><a name="12498" class="Symbol"
      >...</a
      ><a name="12501"
      > </a
      ><a name="12502" class="Symbol"
      >|</a
      ><a name="12503"
      > </a
      ><a name="12504" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#520" class="InductiveConstructor"
      >yes</a
      ><a name="12507"
      > </a
      ><a name="12508" href="Stlc.html#12508" class="Bound"
      >x=y</a
      ><a name="12511"
      > </a
      ><a name="12512" class="Symbol"
      >=</a
      ><a name="12513"
      > </a
      ><a name="12514" href="Stlc.html#5823" class="InductiveConstructor"
      >abs</a
      ><a name="12517"
      > </a
      ><a name="12518" href="Stlc.html#12480" class="Bound"
      >y</a
      ><a name="12519"
      > </a
      ><a name="12520" href="Stlc.html#12482" class="Bound"
      >A</a
      ><a name="12521"
      > </a
      ><a name="12522" href="Stlc.html#12484" class="Bound"
      >t</a
      ><a name="12523"
      >
</a
      ><a name="12524" class="Symbol"
      >...</a
      ><a name="12527"
      > </a
      ><a name="12528" class="Symbol"
      >|</a
      ><a name="12529"
      > </a
      ><a name="12530" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#547" class="InductiveConstructor"
      >no</a
      ><a name="12532"
      >  </a
      ><a name="12534" href="Stlc.html#12534" class="Bound"
      >x&#8800;y</a
      ><a name="12537"
      > </a
      ><a name="12538" class="Symbol"
      >=</a
      ><a name="12539"
      > </a
      ><a name="12540" href="Stlc.html#5823" class="InductiveConstructor"
      >abs</a
      ><a name="12543"
      > </a
      ><a name="12544" href="Stlc.html#12480" class="Bound"
      >y</a
      ><a name="12545"
      > </a
      ><a name="12546" href="Stlc.html#12482" class="Bound"
      >A</a
      ><a name="12547"
      > </a
      ><a name="12548" class="Symbol"
      >(</a
      ><a name="12549" href="Stlc.html#12300" class="Function Operator"
      >[</a
      ><a name="12550"
      > </a
      ><a name="12551" href="Stlc.html#12466" class="Bound"
      >x</a
      ><a name="12552"
      > </a
      ><a name="12553" href="Stlc.html#12300" class="Function Operator"
      >:=</a
      ><a name="12555"
      > </a
      ><a name="12556" href="Stlc.html#12471" class="Bound"
      >v</a
      ><a name="12557"
      > </a
      ><a name="12558" href="Stlc.html#12300" class="Function Operator"
      >]</a
      ><a name="12559"
      > </a
      ><a name="12560" href="Stlc.html#12484" class="Bound"
      >t</a
      ><a name="12561" class="Symbol"
      >)</a
      ><a name="12562"
      >
</a
      ><a name="12563" href="Stlc.html#12300" class="Function Operator"
      >[</a
      ><a name="12564"
      > </a
      ><a name="12565" href="Stlc.html#12565" class="Bound"
      >x</a
      ><a name="12566"
      > </a
      ><a name="12567" href="Stlc.html#12300" class="Function Operator"
      >:=</a
      ><a name="12569"
      > </a
      ><a name="12570" href="Stlc.html#12570" class="Bound"
      >v</a
      ><a name="12571"
      > </a
      ><a name="12572" href="Stlc.html#12300" class="Function Operator"
      >]</a
      ><a name="12573"
      > </a
      ><a name="12574" href="Stlc.html#5857" class="InductiveConstructor"
      >true</a
      ><a name="12578"
      >  </a
      ><a name="12580" class="Symbol"
      >=</a
      ><a name="12581"
      > </a
      ><a name="12582" href="Stlc.html#5857" class="InductiveConstructor"
      >true</a
      ><a name="12586"
      >
</a
      ><a name="12587" href="Stlc.html#12300" class="Function Operator"
      >[</a
      ><a name="12588"
      > </a
      ><a name="12589" href="Stlc.html#12589" class="Bound"
      >x</a
      ><a name="12590"
      > </a
      ><a name="12591" href="Stlc.html#12300" class="Function Operator"
      >:=</a
      ><a name="12593"
      > </a
      ><a name="12594" href="Stlc.html#12594" class="Bound"
      >v</a
      ><a name="12595"
      > </a
      ><a name="12596" href="Stlc.html#12300" class="Function Operator"
      >]</a
      ><a name="12597"
      > </a
      ><a name="12598" href="Stlc.html#5872" class="InductiveConstructor"
      >false</a
      ><a name="12603"
      > </a
      ><a name="12604" class="Symbol"
      >=</a
      ><a name="12605"
      > </a
      ><a name="12606" href="Stlc.html#5872" class="InductiveConstructor"
      >false</a
      ><a name="12611"
      >
</a
      ><a name="12612" href="Stlc.html#12300" class="Function Operator"
      >[</a
      ><a name="12613"
      > </a
      ><a name="12614" href="Stlc.html#12614" class="Bound"
      >x</a
      ><a name="12615"
      > </a
      ><a name="12616" href="Stlc.html#12300" class="Function Operator"
      >:=</a
      ><a name="12618"
      > </a
      ><a name="12619" href="Stlc.html#12619" class="Bound"
      >v</a
      ><a name="12620"
      > </a
      ><a name="12621" href="Stlc.html#12300" class="Function Operator"
      >]</a
      ><a name="12622"
      > </a
      ><a name="12623" class="Symbol"
      >(</a
      ><a name="12624" href="Stlc.html#5887" class="InductiveConstructor Operator"
      >if</a
      ><a name="12626"
      > </a
      ><a name="12627" href="Stlc.html#12627" class="Bound"
      >s</a
      ><a name="12628"
      > </a
      ><a name="12629" href="Stlc.html#5887" class="InductiveConstructor Operator"
      >then</a
      ><a name="12633"
      > </a
      ><a name="12634" href="Stlc.html#12634" class="Bound"
      >t</a
      ><a name="12635"
      > </a
      ><a name="12636" href="Stlc.html#5887" class="InductiveConstructor Operator"
      >else</a
      ><a name="12640"
      > </a
      ><a name="12641" href="Stlc.html#12641" class="Bound"
      >u</a
      ><a name="12642" class="Symbol"
      >)</a
      ><a name="12643"
      > </a
      ><a name="12644" class="Symbol"
      >=</a
      ><a name="12645"
      >
  </a
      ><a name="12648" href="Stlc.html#5887" class="InductiveConstructor Operator"
      >if</a
      ><a name="12650"
      > </a
      ><a name="12651" href="Stlc.html#12300" class="Function Operator"
      >[</a
      ><a name="12652"
      > </a
      ><a name="12653" href="Stlc.html#12614" class="Bound"
      >x</a
      ><a name="12654"
      > </a
      ><a name="12655" href="Stlc.html#12300" class="Function Operator"
      >:=</a
      ><a name="12657"
      > </a
      ><a name="12658" href="Stlc.html#12619" class="Bound"
      >v</a
      ><a name="12659"
      > </a
      ><a name="12660" href="Stlc.html#12300" class="Function Operator"
      >]</a
      ><a name="12661"
      > </a
      ><a name="12662" href="Stlc.html#12627" class="Bound"
      >s</a
      ><a name="12663"
      > </a
      ><a name="12664" href="Stlc.html#5887" class="InductiveConstructor Operator"
      >then</a
      ><a name="12668"
      > </a
      ><a name="12669" href="Stlc.html#12300" class="Function Operator"
      >[</a
      ><a name="12670"
      > </a
      ><a name="12671" href="Stlc.html#12614" class="Bound"
      >x</a
      ><a name="12672"
      > </a
      ><a name="12673" href="Stlc.html#12300" class="Function Operator"
      >:=</a
      ><a name="12675"
      > </a
      ><a name="12676" href="Stlc.html#12619" class="Bound"
      >v</a
      ><a name="12677"
      > </a
      ><a name="12678" href="Stlc.html#12300" class="Function Operator"
      >]</a
      ><a name="12679"
      > </a
      ><a name="12680" href="Stlc.html#12634" class="Bound"
      >t</a
      ><a name="12681"
      > </a
      ><a name="12682" href="Stlc.html#5887" class="InductiveConstructor Operator"
      >else</a
      ><a name="12686"
      >  </a
      ><a name="12688" href="Stlc.html#12300" class="Function Operator"
      >[</a
      ><a name="12689"
      > </a
      ><a name="12690" href="Stlc.html#12614" class="Bound"
      >x</a
      ><a name="12691"
      > </a
      ><a name="12692" href="Stlc.html#12300" class="Function Operator"
      >:=</a
      ><a name="12694"
      > </a
      ><a name="12695" href="Stlc.html#12619" class="Bound"
      >v</a
      ><a name="12696"
      > </a
      ><a name="12697" href="Stlc.html#12300" class="Function Operator"
      >]</a
      ><a name="12698"
      > </a
      ><a name="12699" href="Stlc.html#12641" class="Bound"
      >u</a
      >
</pre><!--{% endraw %}-->

<div class="hidden">
<!--{% raw %}--><pre class="Agda">
<a name="12747" class="Keyword"
      >infix</a
      ><a name="12752"
      > </a
      ><a name="12753" class="Number"
      >9</a
      >
</pre><!--{% endraw %}-->
</div>

_Technical note_: Substitution becomes trickier to define if we
consider the case where $$s$$, the term being substituted for a
variable in some other term, may itself contain free variables.
Since we are only interested here in defining the small-step relation
on closed terms (i.e., terms like $$\lambda x:bool. x$$ that include
binders for all of the variables they mention), we can avoid this
extra complexity here, but it must be dealt with when formalizing
richer languages.


#### Exercise: 3 stars (subst-correct)
The definition that we gave above defines substitution as a _function_.
Suppose, instead, we wanted to define substitution as an inductive _relation_.
We've begun the definition by providing the `data` header and
one of the constructors; your job is to fill in the rest of the constructors
and prove that the relation you've defined coincides with the function given
above.
<!--{% raw %}--><pre class="Agda">
<a name="13691" class="Keyword"
      >data</a
      ><a name="13695"
      > </a
      ><a name="13696" href="Stlc.html#13696" class="Datatype Operator"
      >[_:=_]_==&gt;_</a
      ><a name="13707"
      > </a
      ><a name="13708" class="Symbol"
      >(</a
      ><a name="13709" href="Stlc.html#13709" class="Bound"
      >x</a
      ><a name="13710"
      > </a
      ><a name="13711" class="Symbol"
      >:</a
      ><a name="13712"
      > </a
      ><a name="13713" href="Maps.html#2400" class="Datatype"
      >Id</a
      ><a name="13715" class="Symbol"
      >)</a
      ><a name="13716"
      > </a
      ><a name="13717" class="Symbol"
      >(</a
      ><a name="13718" href="Stlc.html#13718" class="Bound"
      >s</a
      ><a name="13719"
      > </a
      ><a name="13720" class="Symbol"
      >:</a
      ><a name="13721"
      > </a
      ><a name="13722" href="Stlc.html#5755" class="Datatype"
      >Term</a
      ><a name="13726" class="Symbol"
      >)</a
      ><a name="13727"
      > </a
      ><a name="13728" class="Symbol"
      >:</a
      ><a name="13729"
      > </a
      ><a name="13730" href="Stlc.html#5755" class="Datatype"
      >Term</a
      ><a name="13734"
      > </a
      ><a name="13735" class="Symbol"
      >-&gt;</a
      ><a name="13737"
      > </a
      ><a name="13738" href="Stlc.html#5755" class="Datatype"
      >Term</a
      ><a name="13742"
      > </a
      ><a name="13743" class="Symbol"
      >-&gt;</a
      ><a name="13745"
      > </a
      ><a name="13746" class="PrimitiveType"
      >Set</a
      ><a name="13749"
      > </a
      ><a name="13750" class="Keyword"
      >where</a
      ><a name="13755"
      >
  </a
      ><a name="13758" href="Stlc.html#13758" class="InductiveConstructor"
      >var1</a
      ><a name="13762"
      > </a
      ><a name="13763" class="Symbol"
      >:</a
      ><a name="13764"
      > </a
      ><a name="13765" href="Stlc.html#13696" class="Datatype Operator"
      >[</a
      ><a name="13766"
      > </a
      ><a name="13767" href="Stlc.html#13709" class="Bound"
      >x</a
      ><a name="13768"
      > </a
      ><a name="13769" href="Stlc.html#13696" class="Datatype Operator"
      >:=</a
      ><a name="13771"
      > </a
      ><a name="13772" href="Stlc.html#13718" class="Bound"
      >s</a
      ><a name="13773"
      > </a
      ><a name="13774" href="Stlc.html#13696" class="Datatype Operator"
      >]</a
      ><a name="13775"
      > </a
      ><a name="13776" class="Symbol"
      >(</a
      ><a name="13777" href="Stlc.html#5774" class="InductiveConstructor"
      >var</a
      ><a name="13780"
      > </a
      ><a name="13781" href="Stlc.html#13709" class="Bound"
      >x</a
      ><a name="13782" class="Symbol"
      >)</a
      ><a name="13783"
      > </a
      ><a name="13784" href="Stlc.html#13696" class="Datatype Operator"
      >==&gt;</a
      ><a name="13787"
      > </a
      ><a name="13788" href="Stlc.html#13718" class="Bound"
      >s</a
      ><a name="13789"
      >
  </a
      ><a name="13792" class="Comment"
      >{- FILL IN HERE -}</a
      >
</pre><!--{% endraw %}-->

<!--{% raw %}--><pre class="Agda">
<a name="13836" class="Keyword"
      >postulate</a
      ><a name="13845"
      >
  </a
      ><a name="13848" href="Stlc.html#13848" class="Postulate"
      >subst-correct</a
      ><a name="13861"
      > </a
      ><a name="13862" class="Symbol"
      >:</a
      ><a name="13863"
      > </a
      ><a name="13864" class="Symbol"
      >&#8704;</a
      ><a name="13865"
      > </a
      ><a name="13866" href="Stlc.html#13866" class="Bound"
      >s</a
      ><a name="13867"
      > </a
      ><a name="13868" href="Stlc.html#13868" class="Bound"
      >x</a
      ><a name="13869"
      > </a
      ><a name="13870" href="Stlc.html#13870" class="Bound"
      >t</a
      ><a name="13871"
      > </a
      ><a name="13872" href="Stlc.html#13872" class="Bound"
      >t'</a
      ><a name="13874"
      >
                </a
      ><a name="13891" class="Symbol"
      >&#8594;</a
      ><a name="13892"
      > </a
      ><a name="13893" href="Stlc.html#12300" class="Function Operator"
      >[</a
      ><a name="13894"
      > </a
      ><a name="13895" href="Stlc.html#13868" class="Bound"
      >x</a
      ><a name="13896"
      > </a
      ><a name="13897" href="Stlc.html#12300" class="Function Operator"
      >:=</a
      ><a name="13899"
      > </a
      ><a name="13900" href="Stlc.html#13866" class="Bound"
      >s</a
      ><a name="13901"
      > </a
      ><a name="13902" href="Stlc.html#12300" class="Function Operator"
      >]</a
      ><a name="13903"
      > </a
      ><a name="13904" href="Stlc.html#13870" class="Bound"
      >t</a
      ><a name="13905"
      > </a
      ><a name="13906" href="Agda.Builtin.Equality.html#55" class="Datatype Operator"
      >&#8801;</a
      ><a name="13907"
      > </a
      ><a name="13908" href="Stlc.html#13872" class="Bound"
      >t'</a
      ><a name="13910"
      >
                </a
      ><a name="13927" class="Symbol"
      >&#8594;</a
      ><a name="13928"
      > </a
      ><a name="13929" href="Stlc.html#13696" class="Datatype Operator"
      >[</a
      ><a name="13930"
      > </a
      ><a name="13931" href="Stlc.html#13868" class="Bound"
      >x</a
      ><a name="13932"
      > </a
      ><a name="13933" href="Stlc.html#13696" class="Datatype Operator"
      >:=</a
      ><a name="13935"
      > </a
      ><a name="13936" href="Stlc.html#13866" class="Bound"
      >s</a
      ><a name="13937"
      > </a
      ><a name="13938" href="Stlc.html#13696" class="Datatype Operator"
      >]</a
      ><a name="13939"
      > </a
      ><a name="13940" href="Stlc.html#13870" class="Bound"
      >t</a
      ><a name="13941"
      > </a
      ><a name="13942" href="Stlc.html#13696" class="Datatype Operator"
      >==&gt;</a
      ><a name="13945"
      > </a
      ><a name="13946" href="Stlc.html#13872" class="Bound"
      >t'</a
      >
</pre><!--{% endraw %}-->


### Reduction

The small-step reduction relation for STLC now follows the
same pattern as the ones we have seen before.  Intuitively, to
reduce a function application, we first reduce its left-hand
side (the function) until it becomes an abstraction; then we
reduce its right-hand side (the argument) until it is also a
value; and finally we substitute the argument for the bound
variable in the body of the abstraction.  This last rule, written
informally as

$$
(\lambda x : A . t) v \Longrightarrow [x:=v]t
$$

is traditionally called "beta-reduction".

$$
\begin{array}{cl}
  \frac{value(v)}{(\lambda x : A . t) v \Longrightarrow [x:=v]t}&(red)\\\\
  \frac{s \Longrightarrow s'}{s\;t \Longrightarrow s'\;t}&(app1)\\\\
  \frac{value(v)\quad t \Longrightarrow t'}{v\;t \Longrightarrow v\;t'}&(app2)
\end{array}
$$

... plus the usual rules for booleans:

$$
\begin{array}{cl}
  \frac{}{(\text{if }true\text{ then }t_1\text{ else }t_2) \Longrightarrow t_1}&(iftrue)\\\\
  \frac{}{(\text{if }false\text{ then }t_1\text{ else }t_2) \Longrightarrow t_2}&(iffalse)\\\\
  \frac{s \Longrightarrow s'}{\text{if }s\text{ then }t_1\text{ else }t_2
    \Longrightarrow \text{if }s\text{ then }t_1\text{ else }t_2}&(if)
\end{array}
$$

Formally:

<!--{% raw %}--><pre class="Agda">
<a name="15212" class="Keyword"
      >data</a
      ><a name="15216"
      > </a
      ><a name="15217" href="Stlc.html#15217" class="Datatype Operator"
      >_==&gt;_</a
      ><a name="15222"
      > </a
      ><a name="15223" class="Symbol"
      >:</a
      ><a name="15224"
      > </a
      ><a name="15225" href="Stlc.html#5755" class="Datatype"
      >Term</a
      ><a name="15229"
      > </a
      ><a name="15230" class="Symbol"
      >&#8594;</a
      ><a name="15231"
      > </a
      ><a name="15232" href="Stlc.html#5755" class="Datatype"
      >Term</a
      ><a name="15236"
      > </a
      ><a name="15237" class="Symbol"
      >&#8594;</a
      ><a name="15238"
      > </a
      ><a name="15239" class="PrimitiveType"
      >Set</a
      ><a name="15242"
      > </a
      ><a name="15243" class="Keyword"
      >where</a
      ><a name="15248"
      >
  </a
      ><a name="15251" href="Stlc.html#15251" class="InductiveConstructor"
      >red</a
      ><a name="15254"
      >     </a
      ><a name="15259" class="Symbol"
      >:</a
      ><a name="15260"
      > </a
      ><a name="15261" class="Symbol"
      >&#8704;</a
      ><a name="15262"
      > </a
      ><a name="15263" class="Symbol"
      >{</a
      ><a name="15264" href="Stlc.html#15264" class="Bound"
      >x</a
      ><a name="15265"
      > </a
      ><a name="15266" href="Stlc.html#15266" class="Bound"
      >A</a
      ><a name="15267"
      > </a
      ><a name="15268" href="Stlc.html#15268" class="Bound"
      >s</a
      ><a name="15269"
      > </a
      ><a name="15270" href="Stlc.html#15270" class="Bound"
      >t</a
      ><a name="15271" class="Symbol"
      >}</a
      ><a name="15272"
      >
          </a
      ><a name="15283" class="Symbol"
      >&#8594;</a
      ><a name="15284"
      > </a
      ><a name="15285" href="Stlc.html#9080" class="Datatype"
      >Value</a
      ><a name="15290"
      > </a
      ><a name="15291" href="Stlc.html#15270" class="Bound"
      >t</a
      ><a name="15292"
      >
          </a
      ><a name="15303" class="Symbol"
      >&#8594;</a
      ><a name="15304"
      > </a
      ><a name="15305" href="Stlc.html#5794" class="InductiveConstructor"
      >app</a
      ><a name="15308"
      > </a
      ><a name="15309" class="Symbol"
      >(</a
      ><a name="15310" href="Stlc.html#5823" class="InductiveConstructor"
      >abs</a
      ><a name="15313"
      > </a
      ><a name="15314" href="Stlc.html#15264" class="Bound"
      >x</a
      ><a name="15315"
      > </a
      ><a name="15316" href="Stlc.html#15266" class="Bound"
      >A</a
      ><a name="15317"
      > </a
      ><a name="15318" href="Stlc.html#15268" class="Bound"
      >s</a
      ><a name="15319" class="Symbol"
      >)</a
      ><a name="15320"
      > </a
      ><a name="15321" href="Stlc.html#15270" class="Bound"
      >t</a
      ><a name="15322"
      > </a
      ><a name="15323" href="Stlc.html#15217" class="Datatype Operator"
      >==&gt;</a
      ><a name="15326"
      > </a
      ><a name="15327" href="Stlc.html#12300" class="Function Operator"
      >[</a
      ><a name="15328"
      > </a
      ><a name="15329" href="Stlc.html#15264" class="Bound"
      >x</a
      ><a name="15330"
      > </a
      ><a name="15331" href="Stlc.html#12300" class="Function Operator"
      >:=</a
      ><a name="15333"
      > </a
      ><a name="15334" href="Stlc.html#15270" class="Bound"
      >t</a
      ><a name="15335"
      > </a
      ><a name="15336" href="Stlc.html#12300" class="Function Operator"
      >]</a
      ><a name="15337"
      > </a
      ><a name="15338" href="Stlc.html#15268" class="Bound"
      >s</a
      ><a name="15339"
      >
  </a
      ><a name="15342" href="Stlc.html#15342" class="InductiveConstructor"
      >app1</a
      ><a name="15346"
      >    </a
      ><a name="15350" class="Symbol"
      >:</a
      ><a name="15351"
      > </a
      ><a name="15352" class="Symbol"
      >&#8704;</a
      ><a name="15353"
      > </a
      ><a name="15354" class="Symbol"
      >{</a
      ><a name="15355" href="Stlc.html#15355" class="Bound"
      >s</a
      ><a name="15356"
      > </a
      ><a name="15357" href="Stlc.html#15357" class="Bound"
      >s'</a
      ><a name="15359"
      > </a
      ><a name="15360" href="Stlc.html#15360" class="Bound"
      >t</a
      ><a name="15361" class="Symbol"
      >}</a
      ><a name="15362"
      >
          </a
      ><a name="15373" class="Symbol"
      >&#8594;</a
      ><a name="15374"
      > </a
      ><a name="15375" href="Stlc.html#15355" class="Bound"
      >s</a
      ><a name="15376"
      > </a
      ><a name="15377" href="Stlc.html#15217" class="Datatype Operator"
      >==&gt;</a
      ><a name="15380"
      > </a
      ><a name="15381" href="Stlc.html#15357" class="Bound"
      >s'</a
      ><a name="15383"
      >
          </a
      ><a name="15394" class="Symbol"
      >&#8594;</a
      ><a name="15395"
      > </a
      ><a name="15396" href="Stlc.html#5794" class="InductiveConstructor"
      >app</a
      ><a name="15399"
      > </a
      ><a name="15400" href="Stlc.html#15355" class="Bound"
      >s</a
      ><a name="15401"
      > </a
      ><a name="15402" href="Stlc.html#15360" class="Bound"
      >t</a
      ><a name="15403"
      > </a
      ><a name="15404" href="Stlc.html#15217" class="Datatype Operator"
      >==&gt;</a
      ><a name="15407"
      > </a
      ><a name="15408" href="Stlc.html#5794" class="InductiveConstructor"
      >app</a
      ><a name="15411"
      > </a
      ><a name="15412" href="Stlc.html#15357" class="Bound"
      >s'</a
      ><a name="15414"
      > </a
      ><a name="15415" href="Stlc.html#15360" class="Bound"
      >t</a
      ><a name="15416"
      >
  </a
      ><a name="15419" href="Stlc.html#15419" class="InductiveConstructor"
      >app2</a
      ><a name="15423"
      >    </a
      ><a name="15427" class="Symbol"
      >:</a
      ><a name="15428"
      > </a
      ><a name="15429" class="Symbol"
      >&#8704;</a
      ><a name="15430"
      > </a
      ><a name="15431" class="Symbol"
      >{</a
      ><a name="15432" href="Stlc.html#15432" class="Bound"
      >s</a
      ><a name="15433"
      > </a
      ><a name="15434" href="Stlc.html#15434" class="Bound"
      >t</a
      ><a name="15435"
      > </a
      ><a name="15436" href="Stlc.html#15436" class="Bound"
      >t'</a
      ><a name="15438" class="Symbol"
      >}</a
      ><a name="15439"
      >
          </a
      ><a name="15450" class="Symbol"
      >&#8594;</a
      ><a name="15451"
      > </a
      ><a name="15452" href="Stlc.html#9080" class="Datatype"
      >Value</a
      ><a name="15457"
      > </a
      ><a name="15458" href="Stlc.html#15432" class="Bound"
      >s</a
      ><a name="15459"
      >
          </a
      ><a name="15470" class="Symbol"
      >&#8594;</a
      ><a name="15471"
      > </a
      ><a name="15472" href="Stlc.html#15434" class="Bound"
      >t</a
      ><a name="15473"
      > </a
      ><a name="15474" href="Stlc.html#15217" class="Datatype Operator"
      >==&gt;</a
      ><a name="15477"
      > </a
      ><a name="15478" href="Stlc.html#15436" class="Bound"
      >t'</a
      ><a name="15480"
      >
          </a
      ><a name="15491" class="Symbol"
      >&#8594;</a
      ><a name="15492"
      > </a
      ><a name="15493" href="Stlc.html#5794" class="InductiveConstructor"
      >app</a
      ><a name="15496"
      > </a
      ><a name="15497" href="Stlc.html#15432" class="Bound"
      >s</a
      ><a name="15498"
      > </a
      ><a name="15499" href="Stlc.html#15434" class="Bound"
      >t</a
      ><a name="15500"
      > </a
      ><a name="15501" href="Stlc.html#15217" class="Datatype Operator"
      >==&gt;</a
      ><a name="15504"
      > </a
      ><a name="15505" href="Stlc.html#5794" class="InductiveConstructor"
      >app</a
      ><a name="15508"
      > </a
      ><a name="15509" href="Stlc.html#15432" class="Bound"
      >s</a
      ><a name="15510"
      > </a
      ><a name="15511" href="Stlc.html#15436" class="Bound"
      >t'</a
      ><a name="15513"
      >
  </a
      ><a name="15516" href="Stlc.html#15516" class="InductiveConstructor"
      >if</a
      ><a name="15518"
      >      </a
      ><a name="15524" class="Symbol"
      >:</a
      ><a name="15525"
      > </a
      ><a name="15526" class="Symbol"
      >&#8704;</a
      ><a name="15527"
      > </a
      ><a name="15528" class="Symbol"
      >{</a
      ><a name="15529" href="Stlc.html#15529" class="Bound"
      >s</a
      ><a name="15530"
      > </a
      ><a name="15531" href="Stlc.html#15531" class="Bound"
      >s'</a
      ><a name="15533"
      > </a
      ><a name="15534" href="Stlc.html#15534" class="Bound"
      >t</a
      ><a name="15535"
      > </a
      ><a name="15536" href="Stlc.html#15536" class="Bound"
      >u</a
      ><a name="15537" class="Symbol"
      >}</a
      ><a name="15538"
      >
          </a
      ><a name="15549" class="Symbol"
      >&#8594;</a
      ><a name="15550"
      > </a
      ><a name="15551" href="Stlc.html#15529" class="Bound"
      >s</a
      ><a name="15552"
      > </a
      ><a name="15553" href="Stlc.html#15217" class="Datatype Operator"
      >==&gt;</a
      ><a name="15556"
      > </a
      ><a name="15557" href="Stlc.html#15531" class="Bound"
      >s'</a
      ><a name="15559"
      >
          </a
      ><a name="15570" class="Symbol"
      >&#8594;</a
      ><a name="15571"
      > </a
      ><a name="15572" href="Stlc.html#5887" class="InductiveConstructor Operator"
      >if</a
      ><a name="15574"
      > </a
      ><a name="15575" href="Stlc.html#15529" class="Bound"
      >s</a
      ><a name="15576"
      > </a
      ><a name="15577" href="Stlc.html#5887" class="InductiveConstructor Operator"
      >then</a
      ><a name="15581"
      > </a
      ><a name="15582" href="Stlc.html#15534" class="Bound"
      >t</a
      ><a name="15583"
      > </a
      ><a name="15584" href="Stlc.html#5887" class="InductiveConstructor Operator"
      >else</a
      ><a name="15588"
      > </a
      ><a name="15589" href="Stlc.html#15536" class="Bound"
      >u</a
      ><a name="15590"
      > </a
      ><a name="15591" href="Stlc.html#15217" class="Datatype Operator"
      >==&gt;</a
      ><a name="15594"
      > </a
      ><a name="15595" href="Stlc.html#5887" class="InductiveConstructor Operator"
      >if</a
      ><a name="15597"
      > </a
      ><a name="15598" href="Stlc.html#15531" class="Bound"
      >s'</a
      ><a name="15600"
      > </a
      ><a name="15601" href="Stlc.html#5887" class="InductiveConstructor Operator"
      >then</a
      ><a name="15605"
      > </a
      ><a name="15606" href="Stlc.html#15534" class="Bound"
      >t</a
      ><a name="15607"
      > </a
      ><a name="15608" href="Stlc.html#5887" class="InductiveConstructor Operator"
      >else</a
      ><a name="15612"
      > </a
      ><a name="15613" href="Stlc.html#15536" class="Bound"
      >u</a
      ><a name="15614"
      >
  </a
      ><a name="15617" href="Stlc.html#15617" class="InductiveConstructor"
      >iftrue</a
      ><a name="15623"
      >  </a
      ><a name="15625" class="Symbol"
      >:</a
      ><a name="15626"
      > </a
      ><a name="15627" class="Symbol"
      >&#8704;</a
      ><a name="15628"
      > </a
      ><a name="15629" class="Symbol"
      >{</a
      ><a name="15630" href="Stlc.html#15630" class="Bound"
      >s</a
      ><a name="15631"
      > </a
      ><a name="15632" href="Stlc.html#15632" class="Bound"
      >t</a
      ><a name="15633" class="Symbol"
      >}</a
      ><a name="15634"
      >
          </a
      ><a name="15645" class="Symbol"
      >&#8594;</a
      ><a name="15646"
      > </a
      ><a name="15647" href="Stlc.html#5887" class="InductiveConstructor Operator"
      >if</a
      ><a name="15649"
      > </a
      ><a name="15650" href="Stlc.html#5857" class="InductiveConstructor"
      >true</a
      ><a name="15654"
      > </a
      ><a name="15655" href="Stlc.html#5887" class="InductiveConstructor Operator"
      >then</a
      ><a name="15659"
      > </a
      ><a name="15660" href="Stlc.html#15630" class="Bound"
      >s</a
      ><a name="15661"
      > </a
      ><a name="15662" href="Stlc.html#5887" class="InductiveConstructor Operator"
      >else</a
      ><a name="15666"
      > </a
      ><a name="15667" href="Stlc.html#15632" class="Bound"
      >t</a
      ><a name="15668"
      > </a
      ><a name="15669" href="Stlc.html#15217" class="Datatype Operator"
      >==&gt;</a
      ><a name="15672"
      > </a
      ><a name="15673" href="Stlc.html#15630" class="Bound"
      >s</a
      ><a name="15674"
      >
  </a
      ><a name="15677" href="Stlc.html#15677" class="InductiveConstructor"
      >iffalse</a
      ><a name="15684"
      > </a
      ><a name="15685" class="Symbol"
      >:</a
      ><a name="15686"
      > </a
      ><a name="15687" class="Symbol"
      >&#8704;</a
      ><a name="15688"
      > </a
      ><a name="15689" class="Symbol"
      >{</a
      ><a name="15690" href="Stlc.html#15690" class="Bound"
      >s</a
      ><a name="15691"
      > </a
      ><a name="15692" href="Stlc.html#15692" class="Bound"
      >t</a
      ><a name="15693" class="Symbol"
      >}</a
      ><a name="15694"
      >
          </a
      ><a name="15705" class="Symbol"
      >&#8594;</a
      ><a name="15706"
      > </a
      ><a name="15707" href="Stlc.html#5887" class="InductiveConstructor Operator"
      >if</a
      ><a name="15709"
      > </a
      ><a name="15710" href="Stlc.html#5872" class="InductiveConstructor"
      >false</a
      ><a name="15715"
      > </a
      ><a name="15716" href="Stlc.html#5887" class="InductiveConstructor Operator"
      >then</a
      ><a name="15720"
      > </a
      ><a name="15721" href="Stlc.html#15690" class="Bound"
      >s</a
      ><a name="15722"
      > </a
      ><a name="15723" href="Stlc.html#5887" class="InductiveConstructor Operator"
      >else</a
      ><a name="15727"
      > </a
      ><a name="15728" href="Stlc.html#15692" class="Bound"
      >t</a
      ><a name="15729"
      > </a
      ><a name="15730" href="Stlc.html#15217" class="Datatype Operator"
      >==&gt;</a
      ><a name="15733"
      > </a
      ><a name="15734" href="Stlc.html#15692" class="Bound"
      >t</a
      >
</pre><!--{% endraw %}-->

<div class="hidden">
<!--{% raw %}--><pre class="Agda">
<a name="15782" class="Keyword"
      >infix</a
      ><a name="15787"
      > </a
      ><a name="15788" class="Number"
      >1</a
      >
</pre><!--{% endraw %}-->
</div>

<!--{% raw %}--><pre class="Agda">
<a name="15828" class="Keyword"
      >data</a
      ><a name="15832"
      > </a
      ><a name="15833" href="Stlc.html#15833" class="Datatype"
      >Multi</a
      ><a name="15838"
      > </a
      ><a name="15839" class="Symbol"
      >(</a
      ><a name="15840" href="Stlc.html#15840" class="Bound"
      >R</a
      ><a name="15841"
      > </a
      ><a name="15842" class="Symbol"
      >:</a
      ><a name="15843"
      > </a
      ><a name="15844" href="Stlc.html#5755" class="Datatype"
      >Term</a
      ><a name="15848"
      > </a
      ><a name="15849" class="Symbol"
      >&#8594;</a
      ><a name="15850"
      > </a
      ><a name="15851" href="Stlc.html#5755" class="Datatype"
      >Term</a
      ><a name="15855"
      > </a
      ><a name="15856" class="Symbol"
      >&#8594;</a
      ><a name="15857"
      > </a
      ><a name="15858" class="PrimitiveType"
      >Set</a
      ><a name="15861" class="Symbol"
      >)</a
      ><a name="15862"
      > </a
      ><a name="15863" class="Symbol"
      >:</a
      ><a name="15864"
      > </a
      ><a name="15865" href="Stlc.html#5755" class="Datatype"
      >Term</a
      ><a name="15869"
      > </a
      ><a name="15870" class="Symbol"
      >&#8594;</a
      ><a name="15871"
      > </a
      ><a name="15872" href="Stlc.html#5755" class="Datatype"
      >Term</a
      ><a name="15876"
      > </a
      ><a name="15877" class="Symbol"
      >&#8594;</a
      ><a name="15878"
      > </a
      ><a name="15879" class="PrimitiveType"
      >Set</a
      ><a name="15882"
      > </a
      ><a name="15883" class="Keyword"
      >where</a
      ><a name="15888"
      >
  </a
      ><a name="15891" href="Stlc.html#15891" class="InductiveConstructor"
      >refl</a
      ><a name="15895"
      > </a
      ><a name="15896" class="Symbol"
      >:</a
      ><a name="15897"
      > </a
      ><a name="15898" class="Symbol"
      >&#8704;</a
      ><a name="15899"
      > </a
      ><a name="15900" class="Symbol"
      >{</a
      ><a name="15901" href="Stlc.html#15901" class="Bound"
      >x</a
      ><a name="15902" class="Symbol"
      >}</a
      ><a name="15903"
      > </a
      ><a name="15904" class="Symbol"
      >-&gt;</a
      ><a name="15906"
      > </a
      ><a name="15907" href="Stlc.html#15833" class="Datatype"
      >Multi</a
      ><a name="15912"
      > </a
      ><a name="15913" href="Stlc.html#15840" class="Bound"
      >R</a
      ><a name="15914"
      > </a
      ><a name="15915" href="Stlc.html#15901" class="Bound"
      >x</a
      ><a name="15916"
      > </a
      ><a name="15917" href="Stlc.html#15901" class="Bound"
      >x</a
      ><a name="15918"
      >
  </a
      ><a name="15921" href="Stlc.html#15921" class="InductiveConstructor"
      >step</a
      ><a name="15925"
      > </a
      ><a name="15926" class="Symbol"
      >:</a
      ><a name="15927"
      > </a
      ><a name="15928" class="Symbol"
      >&#8704;</a
      ><a name="15929"
      > </a
      ><a name="15930" class="Symbol"
      >{</a
      ><a name="15931" href="Stlc.html#15931" class="Bound"
      >x</a
      ><a name="15932"
      > </a
      ><a name="15933" href="Stlc.html#15933" class="Bound"
      >y</a
      ><a name="15934"
      > </a
      ><a name="15935" href="Stlc.html#15935" class="Bound"
      >z</a
      ><a name="15936" class="Symbol"
      >}</a
      ><a name="15937"
      > </a
      ><a name="15938" class="Symbol"
      >-&gt;</a
      ><a name="15940"
      > </a
      ><a name="15941" href="Stlc.html#15840" class="Bound"
      >R</a
      ><a name="15942"
      > </a
      ><a name="15943" href="Stlc.html#15931" class="Bound"
      >x</a
      ><a name="15944"
      > </a
      ><a name="15945" href="Stlc.html#15933" class="Bound"
      >y</a
      ><a name="15946"
      > </a
      ><a name="15947" class="Symbol"
      >-&gt;</a
      ><a name="15949"
      > </a
      ><a name="15950" href="Stlc.html#15833" class="Datatype"
      >Multi</a
      ><a name="15955"
      > </a
      ><a name="15956" href="Stlc.html#15840" class="Bound"
      >R</a
      ><a name="15957"
      > </a
      ><a name="15958" href="Stlc.html#15933" class="Bound"
      >y</a
      ><a name="15959"
      > </a
      ><a name="15960" href="Stlc.html#15935" class="Bound"
      >z</a
      ><a name="15961"
      > </a
      ><a name="15962" class="Symbol"
      >-&gt;</a
      ><a name="15964"
      > </a
      ><a name="15965" href="Stlc.html#15833" class="Datatype"
      >Multi</a
      ><a name="15970"
      > </a
      ><a name="15971" href="Stlc.html#15840" class="Bound"
      >R</a
      ><a name="15972"
      > </a
      ><a name="15973" href="Stlc.html#15931" class="Bound"
      >x</a
      ><a name="15974"
      > </a
      ><a name="15975" href="Stlc.html#15935" class="Bound"
      >z</a
      >
</pre><!--{% endraw %}-->

<!--{% raw %}--><pre class="Agda">
<a name="16002" href="Stlc.html#16002" class="Function Operator"
      >_==&gt;*_</a
      ><a name="16008"
      > </a
      ><a name="16009" class="Symbol"
      >:</a
      ><a name="16010"
      > </a
      ><a name="16011" href="Stlc.html#5755" class="Datatype"
      >Term</a
      ><a name="16015"
      > </a
      ><a name="16016" class="Symbol"
      >&#8594;</a
      ><a name="16017"
      > </a
      ><a name="16018" href="Stlc.html#5755" class="Datatype"
      >Term</a
      ><a name="16022"
      > </a
      ><a name="16023" class="Symbol"
      >&#8594;</a
      ><a name="16024"
      > </a
      ><a name="16025" class="PrimitiveType"
      >Set</a
      ><a name="16028"
      >
</a
      ><a name="16029" href="Stlc.html#16002" class="Function Operator"
      >_==&gt;*_</a
      ><a name="16035"
      > </a
      ><a name="16036" class="Symbol"
      >=</a
      ><a name="16037"
      > </a
      ><a name="16038" href="Stlc.html#15833" class="Datatype"
      >Multi</a
      ><a name="16043"
      > </a
      ><a name="16044" href="Stlc.html#15217" class="Datatype Operator"
      >_==&gt;_</a
      >
</pre><!--{% endraw %}-->

<div class="hidden">
<!--{% raw %}--><pre class="Agda">
<a name="16096" class="Symbol"
      >{-#</a
      ><a name="16099"
      > </a
      ><a name="16100" class="Keyword"
      >DISPLAY</a
      ><a name="16107"
      > </a
      ><a name="16108" href="Stlc.html#15833" class="Datatype"
      >Multi</a
      ><a name="16113"
      > </a
      ><a name="16114" href="Stlc.html#16114" class="Bound Operator"
      >_==&gt;_</a
      ><a name="16119"
      > = </a
      ><a name="16122" href="Stlc.html#16002" class="Function Operator"
      >_==&gt;*_</a
      ><a name="16128"
      > </a
      ><a name="16129" class="Symbol"
      >#-}</a
      >
</pre><!--{% endraw %}-->
</div>

### Examples

Example:

$$((\lambda x:bool\rightarrow bool. x) (\lambda x:bool. x)) \Longrightarrow^* (\lambda x:bool. x)$$.

<!--{% raw %}--><pre class="Agda">
<a name="16291" href="Stlc.html#16291" class="Function"
      >step-example1</a
      ><a name="16304"
      > </a
      ><a name="16305" class="Symbol"
      >:</a
      ><a name="16306"
      > </a
      ><a name="16307" class="Symbol"
      >(</a
      ><a name="16308" href="Stlc.html#5794" class="InductiveConstructor"
      >app</a
      ><a name="16311"
      > </a
      ><a name="16312" href="Stlc.html#6691" class="Function"
      >idBB</a
      ><a name="16316"
      > </a
      ><a name="16317" href="Stlc.html#6585" class="Function"
      >idB</a
      ><a name="16320" class="Symbol"
      >)</a
      ><a name="16321"
      > </a
      ><a name="16322" href="Stlc.html#16002" class="Function Operator"
      >==&gt;*</a
      ><a name="16326"
      > </a
      ><a name="16327" href="Stlc.html#6585" class="Function"
      >idB</a
      ><a name="16330"
      >
</a
      ><a name="16331" href="Stlc.html#16291" class="Function"
      >step-example1</a
      ><a name="16344"
      > </a
      ><a name="16345" class="Symbol"
      >=</a
      ><a name="16346"
      > </a
      ><a name="16347" href="Stlc.html#15921" class="InductiveConstructor"
      >step</a
      ><a name="16351"
      > </a
      ><a name="16352" class="Symbol"
      >(</a
      ><a name="16353" href="Stlc.html#15251" class="InductiveConstructor"
      >red</a
      ><a name="16356"
      > </a
      ><a name="16357" href="Stlc.html#9107" class="InductiveConstructor"
      >abs</a
      ><a name="16360" class="Symbol"
      >)</a
      ><a name="16361"
      >
              </a
      ><a name="16376" href="https://agda.github.io/agda-stdlib/Function.html#1835" class="Function Operator"
      >$</a
      ><a name="16377"
      > </a
      ><a name="16378" href="Stlc.html#15891" class="InductiveConstructor"
      >refl</a
      >
</pre><!--{% endraw %}-->

Example:

$$(\lambda x:bool\rightarrow bool. x) \;((\lambda x:bool\rightarrow bool. x)\;(\lambda x:bool. x))) \Longrightarrow^* (\lambda x:bool. x)$$.

<!--{% raw %}--><pre class="Agda">
<a name="16560" href="Stlc.html#16560" class="Function"
      >step-example2</a
      ><a name="16573"
      > </a
      ><a name="16574" class="Symbol"
      >:</a
      ><a name="16575"
      > </a
      ><a name="16576" class="Symbol"
      >(</a
      ><a name="16577" href="Stlc.html#5794" class="InductiveConstructor"
      >app</a
      ><a name="16580"
      > </a
      ><a name="16581" href="Stlc.html#6691" class="Function"
      >idBB</a
      ><a name="16585"
      > </a
      ><a name="16586" class="Symbol"
      >(</a
      ><a name="16587" href="Stlc.html#5794" class="InductiveConstructor"
      >app</a
      ><a name="16590"
      > </a
      ><a name="16591" href="Stlc.html#6691" class="Function"
      >idBB</a
      ><a name="16595"
      > </a
      ><a name="16596" href="Stlc.html#6585" class="Function"
      >idB</a
      ><a name="16599" class="Symbol"
      >))</a
      ><a name="16601"
      > </a
      ><a name="16602" href="Stlc.html#16002" class="Function Operator"
      >==&gt;*</a
      ><a name="16606"
      > </a
      ><a name="16607" href="Stlc.html#6585" class="Function"
      >idB</a
      ><a name="16610"
      >
</a
      ><a name="16611" href="Stlc.html#16560" class="Function"
      >step-example2</a
      ><a name="16624"
      > </a
      ><a name="16625" class="Symbol"
      >=</a
      ><a name="16626"
      > </a
      ><a name="16627" href="Stlc.html#15921" class="InductiveConstructor"
      >step</a
      ><a name="16631"
      > </a
      ><a name="16632" class="Symbol"
      >(</a
      ><a name="16633" href="Stlc.html#15419" class="InductiveConstructor"
      >app2</a
      ><a name="16637"
      > </a
      ><a name="16638" href="Stlc.html#9107" class="InductiveConstructor"
      >abs</a
      ><a name="16641"
      > </a
      ><a name="16642" class="Symbol"
      >(</a
      ><a name="16643" href="Stlc.html#15251" class="InductiveConstructor"
      >red</a
      ><a name="16646"
      > </a
      ><a name="16647" href="Stlc.html#9107" class="InductiveConstructor"
      >abs</a
      ><a name="16650" class="Symbol"
      >))</a
      ><a name="16652"
      >
              </a
      ><a name="16667" href="https://agda.github.io/agda-stdlib/Function.html#1835" class="Function Operator"
      >$</a
      ><a name="16668"
      > </a
      ><a name="16669" href="Stlc.html#15921" class="InductiveConstructor"
      >step</a
      ><a name="16673"
      > </a
      ><a name="16674" class="Symbol"
      >(</a
      ><a name="16675" href="Stlc.html#15251" class="InductiveConstructor"
      >red</a
      ><a name="16678"
      > </a
      ><a name="16679" href="Stlc.html#9107" class="InductiveConstructor"
      >abs</a
      ><a name="16682" class="Symbol"
      >)</a
      ><a name="16683"
      >
              </a
      ><a name="16698" href="https://agda.github.io/agda-stdlib/Function.html#1835" class="Function Operator"
      >$</a
      ><a name="16699"
      > </a
      ><a name="16700" href="Stlc.html#15891" class="InductiveConstructor"
      >refl</a
      >
</pre><!--{% endraw %}-->

Example:

$$((\lambda x:bool\rightarrow bool. x)\;(\lambda x:bool. \text{if }x\text{ then }false\text{ else }true))\;true\Longrightarrow^* false$$.

<!--{% raw %}--><pre class="Agda">
<a name="16879" href="Stlc.html#16879" class="Function"
      >step-example3</a
      ><a name="16892"
      > </a
      ><a name="16893" class="Symbol"
      >:</a
      ><a name="16894"
      > </a
      ><a name="16895" class="Symbol"
      >(</a
      ><a name="16896" href="Stlc.html#5794" class="InductiveConstructor"
      >app</a
      ><a name="16899"
      > </a
      ><a name="16900" class="Symbol"
      >(</a
      ><a name="16901" href="Stlc.html#5794" class="InductiveConstructor"
      >app</a
      ><a name="16904"
      > </a
      ><a name="16905" href="Stlc.html#6691" class="Function"
      >idBB</a
      ><a name="16909"
      > </a
      ><a name="16910" href="Stlc.html#7124" class="Function"
      >notB</a
      ><a name="16914" class="Symbol"
      >)</a
      ><a name="16915"
      > </a
      ><a name="16916" href="Stlc.html#5857" class="InductiveConstructor"
      >true</a
      ><a name="16920" class="Symbol"
      >)</a
      ><a name="16921"
      > </a
      ><a name="16922" href="Stlc.html#16002" class="Function Operator"
      >==&gt;*</a
      ><a name="16926"
      > </a
      ><a name="16927" href="Stlc.html#5872" class="InductiveConstructor"
      >false</a
      ><a name="16932"
      >
</a
      ><a name="16933" href="Stlc.html#16879" class="Function"
      >step-example3</a
      ><a name="16946"
      > </a
      ><a name="16947" class="Symbol"
      >=</a
      ><a name="16948"
      > </a
      ><a name="16949" href="Stlc.html#15921" class="InductiveConstructor"
      >step</a
      ><a name="16953"
      > </a
      ><a name="16954" class="Symbol"
      >(</a
      ><a name="16955" href="Stlc.html#15342" class="InductiveConstructor"
      >app1</a
      ><a name="16959"
      > </a
      ><a name="16960" class="Symbol"
      >(</a
      ><a name="16961" href="Stlc.html#15251" class="InductiveConstructor"
      >red</a
      ><a name="16964"
      > </a
      ><a name="16965" href="Stlc.html#9107" class="InductiveConstructor"
      >abs</a
      ><a name="16968" class="Symbol"
      >))</a
      ><a name="16970"
      >
              </a
      ><a name="16985" href="https://agda.github.io/agda-stdlib/Function.html#1835" class="Function Operator"
      >$</a
      ><a name="16986"
      > </a
      ><a name="16987" href="Stlc.html#15921" class="InductiveConstructor"
      >step</a
      ><a name="16991"
      > </a
      ><a name="16992" class="Symbol"
      >(</a
      ><a name="16993" href="Stlc.html#15251" class="InductiveConstructor"
      >red</a
      ><a name="16996"
      > </a
      ><a name="16997" href="Stlc.html#9155" class="InductiveConstructor"
      >true</a
      ><a name="17001" class="Symbol"
      >)</a
      ><a name="17002"
      >
              </a
      ><a name="17017" href="https://agda.github.io/agda-stdlib/Function.html#1835" class="Function Operator"
      >$</a
      ><a name="17018"
      > </a
      ><a name="17019" href="Stlc.html#15921" class="InductiveConstructor"
      >step</a
      ><a name="17023"
      > </a
      ><a name="17024" href="Stlc.html#15617" class="InductiveConstructor"
      >iftrue</a
      ><a name="17030"
      >
              </a
      ><a name="17045" href="https://agda.github.io/agda-stdlib/Function.html#1835" class="Function Operator"
      >$</a
      ><a name="17046"
      > </a
      ><a name="17047" href="Stlc.html#15891" class="InductiveConstructor"
      >refl</a
      >
</pre><!--{% endraw %}-->

Example:

$$((\lambda x:bool\rightarrow bool. x)\;((\lambda x:bool. \text{if }x\text{ then }false\text{ else }true)\;true))\Longrightarrow^* false$$.

<!--{% raw %}--><pre class="Agda">
<a name="17228" href="Stlc.html#17228" class="Function"
      >step-example4</a
      ><a name="17241"
      > </a
      ><a name="17242" class="Symbol"
      >:</a
      ><a name="17243"
      > </a
      ><a name="17244" class="Symbol"
      >(</a
      ><a name="17245" href="Stlc.html#5794" class="InductiveConstructor"
      >app</a
      ><a name="17248"
      > </a
      ><a name="17249" href="Stlc.html#6691" class="Function"
      >idBB</a
      ><a name="17253"
      > </a
      ><a name="17254" class="Symbol"
      >(</a
      ><a name="17255" href="Stlc.html#5794" class="InductiveConstructor"
      >app</a
      ><a name="17258"
      > </a
      ><a name="17259" href="Stlc.html#7124" class="Function"
      >notB</a
      ><a name="17263"
      > </a
      ><a name="17264" href="Stlc.html#5857" class="InductiveConstructor"
      >true</a
      ><a name="17268" class="Symbol"
      >))</a
      ><a name="17270"
      > </a
      ><a name="17271" href="Stlc.html#16002" class="Function Operator"
      >==&gt;*</a
      ><a name="17275"
      > </a
      ><a name="17276" href="Stlc.html#5872" class="InductiveConstructor"
      >false</a
      ><a name="17281"
      >
</a
      ><a name="17282" href="Stlc.html#17228" class="Function"
      >step-example4</a
      ><a name="17295"
      > </a
      ><a name="17296" class="Symbol"
      >=</a
      ><a name="17297"
      > </a
      ><a name="17298" href="Stlc.html#15921" class="InductiveConstructor"
      >step</a
      ><a name="17302"
      > </a
      ><a name="17303" class="Symbol"
      >(</a
      ><a name="17304" href="Stlc.html#15419" class="InductiveConstructor"
      >app2</a
      ><a name="17308"
      > </a
      ><a name="17309" href="Stlc.html#9107" class="InductiveConstructor"
      >abs</a
      ><a name="17312"
      > </a
      ><a name="17313" class="Symbol"
      >(</a
      ><a name="17314" href="Stlc.html#15251" class="InductiveConstructor"
      >red</a
      ><a name="17317"
      > </a
      ><a name="17318" href="Stlc.html#9155" class="InductiveConstructor"
      >true</a
      ><a name="17322" class="Symbol"
      >))</a
      ><a name="17324"
      >
              </a
      ><a name="17339" href="https://agda.github.io/agda-stdlib/Function.html#1835" class="Function Operator"
      >$</a
      ><a name="17340"
      > </a
      ><a name="17341" href="Stlc.html#15921" class="InductiveConstructor"
      >step</a
      ><a name="17345"
      > </a
      ><a name="17346" class="Symbol"
      >(</a
      ><a name="17347" href="Stlc.html#15419" class="InductiveConstructor"
      >app2</a
      ><a name="17351"
      > </a
      ><a name="17352" href="Stlc.html#9107" class="InductiveConstructor"
      >abs</a
      ><a name="17355"
      > </a
      ><a name="17356" href="Stlc.html#15617" class="InductiveConstructor"
      >iftrue</a
      ><a name="17362" class="Symbol"
      >)</a
      ><a name="17363"
      >
              </a
      ><a name="17378" href="https://agda.github.io/agda-stdlib/Function.html#1835" class="Function Operator"
      >$</a
      ><a name="17379"
      > </a
      ><a name="17380" href="Stlc.html#15921" class="InductiveConstructor"
      >step</a
      ><a name="17384"
      > </a
      ><a name="17385" class="Symbol"
      >(</a
      ><a name="17386" href="Stlc.html#15251" class="InductiveConstructor"
      >red</a
      ><a name="17389"
      > </a
      ><a name="17390" href="Stlc.html#9176" class="InductiveConstructor"
      >false</a
      ><a name="17395" class="Symbol"
      >)</a
      ><a name="17396"
      >
              </a
      ><a name="17411" href="https://agda.github.io/agda-stdlib/Function.html#1835" class="Function Operator"
      >$</a
      ><a name="17412"
      > </a
      ><a name="17413" href="Stlc.html#15891" class="InductiveConstructor"
      >refl</a
      >
</pre><!--{% endraw %}-->

#### Exercise: 2 stars (step-example5)

<!--{% raw %}--><pre class="Agda">
<a name="17483" class="Keyword"
      >postulate</a
      ><a name="17492"
      >
  </a
      ><a name="17495" href="Stlc.html#17495" class="Postulate"
      >step-example5</a
      ><a name="17508"
      > </a
      ><a name="17509" class="Symbol"
      >:</a
      ><a name="17510"
      > </a
      ><a name="17511" class="Symbol"
      >(</a
      ><a name="17512" href="Stlc.html#5794" class="InductiveConstructor"
      >app</a
      ><a name="17515"
      > </a
      ><a name="17516" class="Symbol"
      >(</a
      ><a name="17517" href="Stlc.html#5794" class="InductiveConstructor"
      >app</a
      ><a name="17520"
      > </a
      ><a name="17521" href="Stlc.html#6845" class="Function"
      >idBBBB</a
      ><a name="17527"
      > </a
      ><a name="17528" href="Stlc.html#6691" class="Function"
      >idBB</a
      ><a name="17532" class="Symbol"
      >)</a
      ><a name="17533"
      > </a
      ><a name="17534" href="Stlc.html#6585" class="Function"
      >idB</a
      ><a name="17537" class="Symbol"
      >)</a
      ><a name="17538"
      > </a
      ><a name="17539" href="Stlc.html#16002" class="Function Operator"
      >==&gt;*</a
      ><a name="17543"
      > </a
      ><a name="17544" href="Stlc.html#6585" class="Function"
      >idB</a
      >
</pre><!--{% endraw %}-->

## Typing

Next we consider the typing relation of the STLC.

### Contexts

_Question_: What is the type of the term "$$x\;y$$"?

_Answer_: It depends on the types of $$x$$ and $$y$$!

I.e., in order to assign a type to a term, we need to know
what assumptions we should make about the types of its free
variables.

This leads us to a three-place _typing judgment_, informally
written $$\Gamma\vdash t : A$$, where $$\Gamma$$ is a
"typing context"---a mapping from variables to their types.

Informally, we'll write $$\Gamma , x:A$$ for "extend the partial function
$$\Gamma$$ to also map $$x$$ to $$A$$."  Formally, we use the function `_,_∶_`
(or "update") to add a binding to a context.

<!--{% raw %}--><pre class="Agda">
<a name="18264" href="Stlc.html#18264" class="Function"
      >Ctxt</a
      ><a name="18268"
      > </a
      ><a name="18269" class="Symbol"
      >:</a
      ><a name="18270"
      > </a
      ><a name="18271" class="PrimitiveType"
      >Set</a
      ><a name="18274"
      >
</a
      ><a name="18275" href="Stlc.html#18264" class="Function"
      >Ctxt</a
      ><a name="18279"
      > </a
      ><a name="18280" class="Symbol"
      >=</a
      ><a name="18281"
      > </a
      ><a name="18282" href="Maps.html#9519" class="Function"
      >PartialMap</a
      ><a name="18292"
      > </a
      ><a name="18293" href="Stlc.html#5588" class="Datatype"
      >Type</a
      ><a name="18297"
      >

</a
      ><a name="18299" href="Stlc.html#18299" class="Function"
      >&#8709;</a
      ><a name="18300"
      > </a
      ><a name="18301" class="Symbol"
      >:</a
      ><a name="18302"
      > </a
      ><a name="18303" href="Stlc.html#18264" class="Function"
      >Ctxt</a
      ><a name="18307"
      >
</a
      ><a name="18308" href="Stlc.html#18299" class="Function"
      >&#8709;</a
      ><a name="18309"
      > </a
      ><a name="18310" class="Symbol"
      >=</a
      ><a name="18311"
      > </a
      ><a name="18312" href="Maps.html#9652" class="Function"
      >PartialMap.empty</a
      ><a name="18328"
      >

</a
      ><a name="18330" href="Stlc.html#18330" class="Function Operator"
      >_,_&#8758;_</a
      ><a name="18335"
      > </a
      ><a name="18336" class="Symbol"
      >:</a
      ><a name="18337"
      > </a
      ><a name="18338" href="Stlc.html#18264" class="Function"
      >Ctxt</a
      ><a name="18342"
      > </a
      ><a name="18343" class="Symbol"
      >-&gt;</a
      ><a name="18345"
      > </a
      ><a name="18346" href="Maps.html#2400" class="Datatype"
      >Id</a
      ><a name="18348"
      > </a
      ><a name="18349" class="Symbol"
      >-&gt;</a
      ><a name="18351"
      > </a
      ><a name="18352" href="Stlc.html#5588" class="Datatype"
      >Type</a
      ><a name="18356"
      > </a
      ><a name="18357" class="Symbol"
      >-&gt;</a
      ><a name="18359"
      > </a
      ><a name="18360" href="Stlc.html#18264" class="Function"
      >Ctxt</a
      ><a name="18364"
      >
</a
      ><a name="18365" href="Stlc.html#18330" class="Function Operator"
      >_,_&#8758;_</a
      ><a name="18370"
      > </a
      ><a name="18371" class="Symbol"
      >=</a
      ><a name="18372"
      > </a
      ><a name="18373" href="Maps.html#9741" class="Function"
      >PartialMap.update</a
      >
</pre><!--{% endraw %}-->

<div class="hidden">
<!--{% raw %}--><pre class="Agda">
<a name="18437" class="Keyword"
      >infixl</a
      ><a name="18443"
      > </a
      ><a name="18444" class="Number"
      >3</a
      >
</pre><!--{% endraw %}-->
</div>


### Typing Relation

$$
  \begin{array}{cl}
  \frac{\Gamma\;x = A}{\Gamma\vdash{x:A}}&(var)\\\\
  \frac{\Gamma,x:A\vdash t:B}{\Gamma\vdash (\lambda x:A.t) : A\rightarrow B}&(abs)\\\\
  \frac{\Gamma\vdash s:A\rightarrow B\quad\Gamma\vdash t:A}{\Gamma\vdash (s\;t) : B}&(app)\\\\
  \frac{}{\Gamma\vdash true : bool}&(true)\\\\
  \frac{}{\Gamma\vdash false : bool}&(true)\\\\
  \frac{\Gamma\vdash s:bool \quad \Gamma\vdash t1:A \quad \Gamma\vdash t2:A}{\Gamma\vdash\text{if }s\text{ then }t1\text{ else }t2 : A}&(if)
  \end{array}
$$

We can read the three-place relation $$\Gamma\vdash (t : A)$$ as:
"to the term $$t$$ we can assign the type $$A$$ using as types for
the free variables of $$t$$ the ones specified in the context
$$\Gamma$$."

<!--{% raw %}--><pre class="Agda">
<a name="19226" class="Keyword"
      >data</a
      ><a name="19230"
      > </a
      ><a name="19231" href="Stlc.html#19231" class="Datatype Operator"
      >_&#8866;_&#8758;_</a
      ><a name="19236"
      > </a
      ><a name="19237" class="Symbol"
      >:</a
      ><a name="19238"
      > </a
      ><a name="19239" href="Stlc.html#18264" class="Function"
      >Ctxt</a
      ><a name="19243"
      > </a
      ><a name="19244" class="Symbol"
      >-&gt;</a
      ><a name="19246"
      > </a
      ><a name="19247" href="Stlc.html#5755" class="Datatype"
      >Term</a
      ><a name="19251"
      > </a
      ><a name="19252" class="Symbol"
      >-&gt;</a
      ><a name="19254"
      > </a
      ><a name="19255" href="Stlc.html#5588" class="Datatype"
      >Type</a
      ><a name="19259"
      > </a
      ><a name="19260" class="Symbol"
      >-&gt;</a
      ><a name="19262"
      > </a
      ><a name="19263" class="PrimitiveType"
      >Set</a
      ><a name="19266"
      > </a
      ><a name="19267" class="Keyword"
      >where</a
      ><a name="19272"
      >
  </a
      ><a name="19275" href="Stlc.html#19275" class="InductiveConstructor"
      >var</a
      ><a name="19278"
      >           </a
      ><a name="19289" class="Symbol"
      >:</a
      ><a name="19290"
      > </a
      ><a name="19291" class="Symbol"
      >&#8704;</a
      ><a name="19292"
      > </a
      ><a name="19293" class="Symbol"
      >{</a
      ><a name="19294" href="Stlc.html#19294" class="Bound"
      >&#915;</a
      ><a name="19295" class="Symbol"
      >}</a
      ><a name="19296"
      > </a
      ><a name="19297" href="Stlc.html#19297" class="Bound"
      >x</a
      ><a name="19298"
      > </a
      ><a name="19299" class="Symbol"
      >{</a
      ><a name="19300" href="Stlc.html#19300" class="Bound"
      >A</a
      ><a name="19301" class="Symbol"
      >}</a
      ><a name="19302"
      >
                </a
      ><a name="19319" class="Symbol"
      >&#8594;</a
      ><a name="19320"
      > </a
      ><a name="19321" href="Stlc.html#19294" class="Bound"
      >&#915;</a
      ><a name="19322"
      > </a
      ><a name="19323" href="Stlc.html#19297" class="Bound"
      >x</a
      ><a name="19324"
      > </a
      ><a name="19325" href="Agda.Builtin.Equality.html#55" class="Datatype Operator"
      >&#8801;</a
      ><a name="19326"
      > </a
      ><a name="19327" href="https://agda.github.io/agda-stdlib/Data.Maybe.Base.html#373" class="InductiveConstructor"
      >just</a
      ><a name="19331"
      > </a
      ><a name="19332" href="Stlc.html#19300" class="Bound"
      >A</a
      ><a name="19333"
      >
                </a
      ><a name="19350" class="Symbol"
      >&#8594;</a
      ><a name="19351"
      > </a
      ><a name="19352" href="Stlc.html#19294" class="Bound"
      >&#915;</a
      ><a name="19353"
      > </a
      ><a name="19354" href="Stlc.html#19231" class="Datatype Operator"
      >&#8866;</a
      ><a name="19355"
      > </a
      ><a name="19356" href="Stlc.html#5774" class="InductiveConstructor"
      >var</a
      ><a name="19359"
      > </a
      ><a name="19360" href="Stlc.html#19297" class="Bound"
      >x</a
      ><a name="19361"
      > </a
      ><a name="19362" href="Stlc.html#19231" class="Datatype Operator"
      >&#8758;</a
      ><a name="19363"
      > </a
      ><a name="19364" href="Stlc.html#19300" class="Bound"
      >A</a
      ><a name="19365"
      >
  </a
      ><a name="19368" href="Stlc.html#19368" class="InductiveConstructor"
      >abs</a
      ><a name="19371"
      >           </a
      ><a name="19382" class="Symbol"
      >:</a
      ><a name="19383"
      > </a
      ><a name="19384" class="Symbol"
      >&#8704;</a
      ><a name="19385"
      > </a
      ><a name="19386" class="Symbol"
      >{</a
      ><a name="19387" href="Stlc.html#19387" class="Bound"
      >&#915;</a
      ><a name="19388" class="Symbol"
      >}</a
      ><a name="19389"
      > </a
      ><a name="19390" class="Symbol"
      >{</a
      ><a name="19391" href="Stlc.html#19391" class="Bound"
      >x</a
      ><a name="19392" class="Symbol"
      >}</a
      ><a name="19393"
      > </a
      ><a name="19394" class="Symbol"
      >{</a
      ><a name="19395" href="Stlc.html#19395" class="Bound"
      >A</a
      ><a name="19396" class="Symbol"
      >}</a
      ><a name="19397"
      > </a
      ><a name="19398" class="Symbol"
      >{</a
      ><a name="19399" href="Stlc.html#19399" class="Bound"
      >B</a
      ><a name="19400" class="Symbol"
      >}</a
      ><a name="19401"
      > </a
      ><a name="19402" class="Symbol"
      >{</a
      ><a name="19403" href="Stlc.html#19403" class="Bound"
      >s</a
      ><a name="19404" class="Symbol"
      >}</a
      ><a name="19405"
      >
                </a
      ><a name="19422" class="Symbol"
      >&#8594;</a
      ><a name="19423"
      > </a
      ><a name="19424" href="Stlc.html#19387" class="Bound"
      >&#915;</a
      ><a name="19425"
      > </a
      ><a name="19426" href="Stlc.html#18330" class="Function Operator"
      >,</a
      ><a name="19427"
      > </a
      ><a name="19428" href="Stlc.html#19391" class="Bound"
      >x</a
      ><a name="19429"
      > </a
      ><a name="19430" href="Stlc.html#18330" class="Function Operator"
      >&#8758;</a
      ><a name="19431"
      > </a
      ><a name="19432" href="Stlc.html#19395" class="Bound"
      >A</a
      ><a name="19433"
      > </a
      ><a name="19434" href="Stlc.html#19231" class="Datatype Operator"
      >&#8866;</a
      ><a name="19435"
      > </a
      ><a name="19436" href="Stlc.html#19403" class="Bound"
      >s</a
      ><a name="19437"
      > </a
      ><a name="19438" href="Stlc.html#19231" class="Datatype Operator"
      >&#8758;</a
      ><a name="19439"
      > </a
      ><a name="19440" href="Stlc.html#19399" class="Bound"
      >B</a
      ><a name="19441"
      >
                </a
      ><a name="19458" class="Symbol"
      >&#8594;</a
      ><a name="19459"
      > </a
      ><a name="19460" href="Stlc.html#19387" class="Bound"
      >&#915;</a
      ><a name="19461"
      > </a
      ><a name="19462" href="Stlc.html#19231" class="Datatype Operator"
      >&#8866;</a
      ><a name="19463"
      > </a
      ><a name="19464" href="Stlc.html#5823" class="InductiveConstructor"
      >abs</a
      ><a name="19467"
      > </a
      ><a name="19468" href="Stlc.html#19391" class="Bound"
      >x</a
      ><a name="19469"
      > </a
      ><a name="19470" href="Stlc.html#19395" class="Bound"
      >A</a
      ><a name="19471"
      > </a
      ><a name="19472" href="Stlc.html#19403" class="Bound"
      >s</a
      ><a name="19473"
      > </a
      ><a name="19474" href="Stlc.html#19231" class="Datatype Operator"
      >&#8758;</a
      ><a name="19475"
      > </a
      ><a name="19476" href="Stlc.html#19395" class="Bound"
      >A</a
      ><a name="19477"
      > </a
      ><a name="19478" href="Stlc.html#5621" class="InductiveConstructor Operator"
      >&#8658;</a
      ><a name="19479"
      > </a
      ><a name="19480" href="Stlc.html#19399" class="Bound"
      >B</a
      ><a name="19481"
      >
  </a
      ><a name="19484" href="Stlc.html#19484" class="InductiveConstructor"
      >app</a
      ><a name="19487"
      >           </a
      ><a name="19498" class="Symbol"
      >:</a
      ><a name="19499"
      > </a
      ><a name="19500" class="Symbol"
      >&#8704;</a
      ><a name="19501"
      > </a
      ><a name="19502" class="Symbol"
      >{</a
      ><a name="19503" href="Stlc.html#19503" class="Bound"
      >&#915;</a
      ><a name="19504" class="Symbol"
      >}</a
      ><a name="19505"
      > </a
      ><a name="19506" class="Symbol"
      >{</a
      ><a name="19507" href="Stlc.html#19507" class="Bound"
      >A</a
      ><a name="19508" class="Symbol"
      >}</a
      ><a name="19509"
      > </a
      ><a name="19510" class="Symbol"
      >{</a
      ><a name="19511" href="Stlc.html#19511" class="Bound"
      >B</a
      ><a name="19512" class="Symbol"
      >}</a
      ><a name="19513"
      > </a
      ><a name="19514" class="Symbol"
      >{</a
      ><a name="19515" href="Stlc.html#19515" class="Bound"
      >s</a
      ><a name="19516" class="Symbol"
      >}</a
      ><a name="19517"
      > </a
      ><a name="19518" class="Symbol"
      >{</a
      ><a name="19519" href="Stlc.html#19519" class="Bound"
      >t</a
      ><a name="19520" class="Symbol"
      >}</a
      ><a name="19521"
      >
                </a
      ><a name="19538" class="Symbol"
      >&#8594;</a
      ><a name="19539"
      > </a
      ><a name="19540" href="Stlc.html#19503" class="Bound"
      >&#915;</a
      ><a name="19541"
      > </a
      ><a name="19542" href="Stlc.html#19231" class="Datatype Operator"
      >&#8866;</a
      ><a name="19543"
      > </a
      ><a name="19544" href="Stlc.html#19515" class="Bound"
      >s</a
      ><a name="19545"
      > </a
      ><a name="19546" href="Stlc.html#19231" class="Datatype Operator"
      >&#8758;</a
      ><a name="19547"
      > </a
      ><a name="19548" href="Stlc.html#19507" class="Bound"
      >A</a
      ><a name="19549"
      > </a
      ><a name="19550" href="Stlc.html#5621" class="InductiveConstructor Operator"
      >&#8658;</a
      ><a name="19551"
      > </a
      ><a name="19552" href="Stlc.html#19511" class="Bound"
      >B</a
      ><a name="19553"
      >
                </a
      ><a name="19570" class="Symbol"
      >&#8594;</a
      ><a name="19571"
      > </a
      ><a name="19572" href="Stlc.html#19503" class="Bound"
      >&#915;</a
      ><a name="19573"
      > </a
      ><a name="19574" href="Stlc.html#19231" class="Datatype Operator"
      >&#8866;</a
      ><a name="19575"
      > </a
      ><a name="19576" href="Stlc.html#19519" class="Bound"
      >t</a
      ><a name="19577"
      > </a
      ><a name="19578" href="Stlc.html#19231" class="Datatype Operator"
      >&#8758;</a
      ><a name="19579"
      > </a
      ><a name="19580" href="Stlc.html#19507" class="Bound"
      >A</a
      ><a name="19581"
      >
                </a
      ><a name="19598" class="Symbol"
      >&#8594;</a
      ><a name="19599"
      > </a
      ><a name="19600" href="Stlc.html#19503" class="Bound"
      >&#915;</a
      ><a name="19601"
      > </a
      ><a name="19602" href="Stlc.html#19231" class="Datatype Operator"
      >&#8866;</a
      ><a name="19603"
      > </a
      ><a name="19604" href="Stlc.html#5794" class="InductiveConstructor"
      >app</a
      ><a name="19607"
      > </a
      ><a name="19608" href="Stlc.html#19515" class="Bound"
      >s</a
      ><a name="19609"
      > </a
      ><a name="19610" href="Stlc.html#19519" class="Bound"
      >t</a
      ><a name="19611"
      > </a
      ><a name="19612" href="Stlc.html#19231" class="Datatype Operator"
      >&#8758;</a
      ><a name="19613"
      > </a
      ><a name="19614" href="Stlc.html#19511" class="Bound"
      >B</a
      ><a name="19615"
      >
  </a
      ><a name="19618" href="Stlc.html#19618" class="InductiveConstructor"
      >true</a
      ><a name="19622"
      >          </a
      ><a name="19632" class="Symbol"
      >:</a
      ><a name="19633"
      > </a
      ><a name="19634" class="Symbol"
      >&#8704;</a
      ><a name="19635"
      > </a
      ><a name="19636" class="Symbol"
      >{</a
      ><a name="19637" href="Stlc.html#19637" class="Bound"
      >&#915;</a
      ><a name="19638" class="Symbol"
      >}</a
      ><a name="19639"
      >
                </a
      ><a name="19656" class="Symbol"
      >&#8594;</a
      ><a name="19657"
      > </a
      ><a name="19658" href="Stlc.html#19637" class="Bound"
      >&#915;</a
      ><a name="19659"
      > </a
      ><a name="19660" href="Stlc.html#19231" class="Datatype Operator"
      >&#8866;</a
      ><a name="19661"
      > </a
      ><a name="19662" href="Stlc.html#5857" class="InductiveConstructor"
      >true</a
      ><a name="19666"
      >  </a
      ><a name="19668" href="Stlc.html#19231" class="Datatype Operator"
      >&#8758;</a
      ><a name="19669"
      > </a
      ><a name="19670" href="Stlc.html#5607" class="InductiveConstructor"
      >bool</a
      ><a name="19674"
      >
  </a
      ><a name="19677" href="Stlc.html#19677" class="InductiveConstructor"
      >false</a
      ><a name="19682"
      >         </a
      ><a name="19691" class="Symbol"
      >:</a
      ><a name="19692"
      > </a
      ><a name="19693" class="Symbol"
      >&#8704;</a
      ><a name="19694"
      > </a
      ><a name="19695" class="Symbol"
      >{</a
      ><a name="19696" href="Stlc.html#19696" class="Bound"
      >&#915;</a
      ><a name="19697" class="Symbol"
      >}</a
      ><a name="19698"
      >
                </a
      ><a name="19715" class="Symbol"
      >&#8594;</a
      ><a name="19716"
      > </a
      ><a name="19717" href="Stlc.html#19696" class="Bound"
      >&#915;</a
      ><a name="19718"
      > </a
      ><a name="19719" href="Stlc.html#19231" class="Datatype Operator"
      >&#8866;</a
      ><a name="19720"
      > </a
      ><a name="19721" href="Stlc.html#5872" class="InductiveConstructor"
      >false</a
      ><a name="19726"
      > </a
      ><a name="19727" href="Stlc.html#19231" class="Datatype Operator"
      >&#8758;</a
      ><a name="19728"
      > </a
      ><a name="19729" href="Stlc.html#5607" class="InductiveConstructor"
      >bool</a
      ><a name="19733"
      >
  </a
      ><a name="19736" href="Stlc.html#19736" class="InductiveConstructor Operator"
      >if_then_else_</a
      ><a name="19749"
      > </a
      ><a name="19750" class="Symbol"
      >:</a
      ><a name="19751"
      > </a
      ><a name="19752" class="Symbol"
      >&#8704;</a
      ><a name="19753"
      > </a
      ><a name="19754" class="Symbol"
      >{</a
      ><a name="19755" href="Stlc.html#19755" class="Bound"
      >&#915;</a
      ><a name="19756" class="Symbol"
      >}</a
      ><a name="19757"
      > </a
      ><a name="19758" class="Symbol"
      >{</a
      ><a name="19759" href="Stlc.html#19759" class="Bound"
      >s</a
      ><a name="19760" class="Symbol"
      >}</a
      ><a name="19761"
      > </a
      ><a name="19762" class="Symbol"
      >{</a
      ><a name="19763" href="Stlc.html#19763" class="Bound"
      >t</a
      ><a name="19764" class="Symbol"
      >}</a
      ><a name="19765"
      > </a
      ><a name="19766" class="Symbol"
      >{</a
      ><a name="19767" href="Stlc.html#19767" class="Bound"
      >u</a
      ><a name="19768" class="Symbol"
      >}</a
      ><a name="19769"
      > </a
      ><a name="19770" class="Symbol"
      >{</a
      ><a name="19771" href="Stlc.html#19771" class="Bound"
      >A</a
      ><a name="19772" class="Symbol"
      >}</a
      ><a name="19773"
      >
                </a
      ><a name="19790" class="Symbol"
      >&#8594;</a
      ><a name="19791"
      > </a
      ><a name="19792" href="Stlc.html#19755" class="Bound"
      >&#915;</a
      ><a name="19793"
      > </a
      ><a name="19794" href="Stlc.html#19231" class="Datatype Operator"
      >&#8866;</a
      ><a name="19795"
      > </a
      ><a name="19796" href="Stlc.html#19759" class="Bound"
      >s</a
      ><a name="19797"
      > </a
      ><a name="19798" href="Stlc.html#19231" class="Datatype Operator"
      >&#8758;</a
      ><a name="19799"
      > </a
      ><a name="19800" href="Stlc.html#5607" class="InductiveConstructor"
      >bool</a
      ><a name="19804"
      >
                </a
      ><a name="19821" class="Symbol"
      >&#8594;</a
      ><a name="19822"
      > </a
      ><a name="19823" href="Stlc.html#19755" class="Bound"
      >&#915;</a
      ><a name="19824"
      > </a
      ><a name="19825" href="Stlc.html#19231" class="Datatype Operator"
      >&#8866;</a
      ><a name="19826"
      > </a
      ><a name="19827" href="Stlc.html#19763" class="Bound"
      >t</a
      ><a name="19828"
      > </a
      ><a name="19829" href="Stlc.html#19231" class="Datatype Operator"
      >&#8758;</a
      ><a name="19830"
      > </a
      ><a name="19831" href="Stlc.html#19771" class="Bound"
      >A</a
      ><a name="19832"
      >
                </a
      ><a name="19849" class="Symbol"
      >&#8594;</a
      ><a name="19850"
      > </a
      ><a name="19851" href="Stlc.html#19755" class="Bound"
      >&#915;</a
      ><a name="19852"
      > </a
      ><a name="19853" href="Stlc.html#19231" class="Datatype Operator"
      >&#8866;</a
      ><a name="19854"
      > </a
      ><a name="19855" href="Stlc.html#19767" class="Bound"
      >u</a
      ><a name="19856"
      > </a
      ><a name="19857" href="Stlc.html#19231" class="Datatype Operator"
      >&#8758;</a
      ><a name="19858"
      > </a
      ><a name="19859" href="Stlc.html#19771" class="Bound"
      >A</a
      ><a name="19860"
      >
                </a
      ><a name="19877" class="Symbol"
      >&#8594;</a
      ><a name="19878"
      > </a
      ><a name="19879" href="Stlc.html#19755" class="Bound"
      >&#915;</a
      ><a name="19880"
      > </a
      ><a name="19881" href="Stlc.html#19231" class="Datatype Operator"
      >&#8866;</a
      ><a name="19882"
      > </a
      ><a name="19883" href="Stlc.html#5887" class="InductiveConstructor Operator"
      >if</a
      ><a name="19885"
      > </a
      ><a name="19886" href="Stlc.html#19759" class="Bound"
      >s</a
      ><a name="19887"
      > </a
      ><a name="19888" href="Stlc.html#5887" class="InductiveConstructor Operator"
      >then</a
      ><a name="19892"
      > </a
      ><a name="19893" href="Stlc.html#19763" class="Bound"
      >t</a
      ><a name="19894"
      > </a
      ><a name="19895" href="Stlc.html#5887" class="InductiveConstructor Operator"
      >else</a
      ><a name="19899"
      > </a
      ><a name="19900" href="Stlc.html#19767" class="Bound"
      >u</a
      ><a name="19901"
      > </a
      ><a name="19902" href="Stlc.html#19231" class="Datatype Operator"
      >&#8758;</a
      ><a name="19903"
      > </a
      ><a name="19904" href="Stlc.html#19771" class="Bound"
      >A</a
      >
</pre><!--{% endraw %}-->

<div class="hidden">
<!--{% raw %}--><pre class="Agda">
<a name="19952" class="Keyword"
      >infix</a
      ><a name="19957"
      > </a
      ><a name="19958" class="Number"
      >1</a
      >
</pre><!--{% endraw %}-->
</div>


### Examples

<!--{% raw %}--><pre class="Agda">
<a name="20013" href="Stlc.html#20013" class="Function"
      >typing-example1</a
      ><a name="20028"
      > </a
      ><a name="20029" class="Symbol"
      >:</a
      ><a name="20030"
      > </a
      ><a name="20031" href="Stlc.html#18299" class="Function"
      >&#8709;</a
      ><a name="20032"
      > </a
      ><a name="20033" href="Stlc.html#19231" class="Datatype Operator"
      >&#8866;</a
      ><a name="20034"
      > </a
      ><a name="20035" href="Stlc.html#6585" class="Function"
      >idB</a
      ><a name="20038"
      > </a
      ><a name="20039" href="Stlc.html#19231" class="Datatype Operator"
      >&#8758;</a
      ><a name="20040"
      > </a
      ><a name="20041" href="Stlc.html#5607" class="InductiveConstructor"
      >bool</a
      ><a name="20045"
      > </a
      ><a name="20046" href="Stlc.html#5621" class="InductiveConstructor Operator"
      >&#8658;</a
      ><a name="20047"
      > </a
      ><a name="20048" href="Stlc.html#5607" class="InductiveConstructor"
      >bool</a
      ><a name="20052"
      >
</a
      ><a name="20053" href="Stlc.html#20013" class="Function"
      >typing-example1</a
      ><a name="20068"
      > </a
      ><a name="20069" class="Symbol"
      >=</a
      ><a name="20070"
      > </a
      ><a name="20071" href="Stlc.html#19368" class="InductiveConstructor"
      >abs</a
      ><a name="20074"
      > </a
      ><a name="20075" class="Symbol"
      >(</a
      ><a name="20076" href="Stlc.html#19275" class="InductiveConstructor"
      >var</a
      ><a name="20079"
      > </a
      ><a name="20080" href="Stlc.html#6354" class="Function"
      >x</a
      ><a name="20081"
      > </a
      ><a name="20082" href="Agda.Builtin.Equality.html#112" class="InductiveConstructor"
      >refl</a
      ><a name="20086" class="Symbol"
      >)</a
      >
</pre><!--{% endraw %}-->

Another example:

$$\varnothing\vdash \lambda x:A. \lambda y:A\rightarrow A. y\;(y\;x) : A\rightarrow (A\rightarrow A)\rightarrow A$$.

<!--{% raw %}--><pre class="Agda">
<a name="20249" href="Stlc.html#20249" class="Function"
      >typing-example2</a
      ><a name="20264"
      > </a
      ><a name="20265" class="Symbol"
      >:</a
      ><a name="20266"
      > </a
      ><a name="20267" href="Stlc.html#18299" class="Function"
      >&#8709;</a
      ><a name="20268"
      > </a
      ><a name="20269" href="Stlc.html#19231" class="Datatype Operator"
      >&#8866;</a
      ><a name="20270"
      >
  </a
      ><a name="20273" class="Symbol"
      >(</a
      ><a name="20274" href="Stlc.html#5823" class="InductiveConstructor"
      >abs</a
      ><a name="20277"
      > </a
      ><a name="20278" href="Stlc.html#6354" class="Function"
      >x</a
      ><a name="20279"
      > </a
      ><a name="20280" href="Stlc.html#5607" class="InductiveConstructor"
      >bool</a
      ><a name="20284"
      >
    </a
      ><a name="20289" class="Symbol"
      >(</a
      ><a name="20290" href="Stlc.html#5823" class="InductiveConstructor"
      >abs</a
      ><a name="20293"
      > </a
      ><a name="20294" href="Stlc.html#6363" class="Function"
      >y</a
      ><a name="20295"
      > </a
      ><a name="20296" class="Symbol"
      >(</a
      ><a name="20297" href="Stlc.html#5607" class="InductiveConstructor"
      >bool</a
      ><a name="20301"
      > </a
      ><a name="20302" href="Stlc.html#5621" class="InductiveConstructor Operator"
      >&#8658;</a
      ><a name="20303"
      > </a
      ><a name="20304" href="Stlc.html#5607" class="InductiveConstructor"
      >bool</a
      ><a name="20308" class="Symbol"
      >)</a
      ><a name="20309"
      >
      </a
      ><a name="20316" class="Symbol"
      >(</a
      ><a name="20317" href="Stlc.html#5794" class="InductiveConstructor"
      >app</a
      ><a name="20320"
      > </a
      ><a name="20321" class="Symbol"
      >(</a
      ><a name="20322" href="Stlc.html#5774" class="InductiveConstructor"
      >var</a
      ><a name="20325"
      > </a
      ><a name="20326" href="Stlc.html#6363" class="Function"
      >y</a
      ><a name="20327" class="Symbol"
      >)</a
      ><a name="20328"
      >
        </a
      ><a name="20337" class="Symbol"
      >(</a
      ><a name="20338" href="Stlc.html#5794" class="InductiveConstructor"
      >app</a
      ><a name="20341"
      > </a
      ><a name="20342" class="Symbol"
      >(</a
      ><a name="20343" href="Stlc.html#5774" class="InductiveConstructor"
      >var</a
      ><a name="20346"
      > </a
      ><a name="20347" href="Stlc.html#6363" class="Function"
      >y</a
      ><a name="20348" class="Symbol"
      >)</a
      ><a name="20349"
      > </a
      ><a name="20350" class="Symbol"
      >(</a
      ><a name="20351" href="Stlc.html#5774" class="InductiveConstructor"
      >var</a
      ><a name="20354"
      > </a
      ><a name="20355" href="Stlc.html#6354" class="Function"
      >x</a
      ><a name="20356" class="Symbol"
      >)))))</a
      ><a name="20361"
      >
  </a
      ><a name="20364" href="Stlc.html#19231" class="Datatype Operator"
      >&#8758;</a
      ><a name="20365"
      > </a
      ><a name="20366" class="Symbol"
      >(</a
      ><a name="20367" href="Stlc.html#5607" class="InductiveConstructor"
      >bool</a
      ><a name="20371"
      > </a
      ><a name="20372" href="Stlc.html#5621" class="InductiveConstructor Operator"
      >&#8658;</a
      ><a name="20373"
      > </a
      ><a name="20374" class="Symbol"
      >(</a
      ><a name="20375" href="Stlc.html#5607" class="InductiveConstructor"
      >bool</a
      ><a name="20379"
      > </a
      ><a name="20380" href="Stlc.html#5621" class="InductiveConstructor Operator"
      >&#8658;</a
      ><a name="20381"
      > </a
      ><a name="20382" href="Stlc.html#5607" class="InductiveConstructor"
      >bool</a
      ><a name="20386" class="Symbol"
      >)</a
      ><a name="20387"
      > </a
      ><a name="20388" href="Stlc.html#5621" class="InductiveConstructor Operator"
      >&#8658;</a
      ><a name="20389"
      > </a
      ><a name="20390" href="Stlc.html#5607" class="InductiveConstructor"
      >bool</a
      ><a name="20394" class="Symbol"
      >)</a
      ><a name="20395"
      >
</a
      ><a name="20396" href="Stlc.html#20249" class="Function"
      >typing-example2</a
      ><a name="20411"
      > </a
      ><a name="20412" class="Symbol"
      >=</a
      ><a name="20413"
      >
  </a
      ><a name="20416" class="Symbol"
      >(</a
      ><a name="20417" href="Stlc.html#19368" class="InductiveConstructor"
      >abs</a
      ><a name="20420"
      >
    </a
      ><a name="20425" class="Symbol"
      >(</a
      ><a name="20426" href="Stlc.html#19368" class="InductiveConstructor"
      >abs</a
      ><a name="20429"
      >
      </a
      ><a name="20436" class="Symbol"
      >(</a
      ><a name="20437" href="Stlc.html#19484" class="InductiveConstructor"
      >app</a
      ><a name="20440"
      > </a
      ><a name="20441" class="Symbol"
      >(</a
      ><a name="20442" href="Stlc.html#19275" class="InductiveConstructor"
      >var</a
      ><a name="20445"
      > </a
      ><a name="20446" href="Stlc.html#6363" class="Function"
      >y</a
      ><a name="20447"
      > </a
      ><a name="20448" href="Agda.Builtin.Equality.html#112" class="InductiveConstructor"
      >refl</a
      ><a name="20452" class="Symbol"
      >)</a
      ><a name="20453"
      >
        </a
      ><a name="20462" class="Symbol"
      >(</a
      ><a name="20463" href="Stlc.html#19484" class="InductiveConstructor"
      >app</a
      ><a name="20466"
      > </a
      ><a name="20467" class="Symbol"
      >(</a
      ><a name="20468" href="Stlc.html#19275" class="InductiveConstructor"
      >var</a
      ><a name="20471"
      > </a
      ><a name="20472" href="Stlc.html#6363" class="Function"
      >y</a
      ><a name="20473"
      > </a
      ><a name="20474" href="Agda.Builtin.Equality.html#112" class="InductiveConstructor"
      >refl</a
      ><a name="20478" class="Symbol"
      >)</a
      ><a name="20479"
      > </a
      ><a name="20480" class="Symbol"
      >(</a
      ><a name="20481" href="Stlc.html#19275" class="InductiveConstructor"
      >var</a
      ><a name="20484"
      > </a
      ><a name="20485" href="Stlc.html#6354" class="Function"
      >x</a
      ><a name="20486"
      > </a
      ><a name="20487" href="Agda.Builtin.Equality.html#112" class="InductiveConstructor"
      >refl</a
      ><a name="20491" class="Symbol"
      >)</a
      ><a name="20492"
      > </a
      ><a name="20493" class="Symbol"
      >))))</a
      >
</pre><!--{% endraw %}-->

#### Exercise: 2 stars (typing-example3)
Formally prove the following typing derivation holds:

$$\exists A, \varnothing\vdash \lambda x:bool\rightarrow B. \lambda y:bool\rightarrow bool. \lambda z:bool. y\;(x\;z) : A$$.

<!--{% raw %}--><pre class="Agda">
<a name="20745" class="Keyword"
      >postulate</a
      ><a name="20754"
      >
  </a
      ><a name="20757" href="Stlc.html#20757" class="Postulate"
      >typing-example3</a
      ><a name="20772"
      > </a
      ><a name="20773" class="Symbol"
      >:</a
      ><a name="20774"
      > </a
      ><a name="20775" href="https://agda.github.io/agda-stdlib/Data.Product.html#823" class="Function"
      >&#8707;</a
      ><a name="20776"
      > </a
      ><a name="20777" class="Symbol"
      >&#955;</a
      ><a name="20778"
      > </a
      ><a name="20779" href="Stlc.html#20779" class="Bound"
      >A</a
      ><a name="20780"
      > </a
      ><a name="20781" class="Symbol"
      >&#8594;</a
      ><a name="20782"
      > </a
      ><a name="20783" href="Stlc.html#18299" class="Function"
      >&#8709;</a
      ><a name="20784"
      > </a
      ><a name="20785" href="Stlc.html#19231" class="Datatype Operator"
      >&#8866;</a
      ><a name="20786"
      >
    </a
      ><a name="20791" class="Symbol"
      >(</a
      ><a name="20792" href="Stlc.html#5823" class="InductiveConstructor"
      >abs</a
      ><a name="20795"
      > </a
      ><a name="20796" href="Stlc.html#6354" class="Function"
      >x</a
      ><a name="20797"
      > </a
      ><a name="20798" class="Symbol"
      >(</a
      ><a name="20799" href="Stlc.html#5607" class="InductiveConstructor"
      >bool</a
      ><a name="20803"
      > </a
      ><a name="20804" href="Stlc.html#5621" class="InductiveConstructor Operator"
      >&#8658;</a
      ><a name="20805"
      > </a
      ><a name="20806" href="Stlc.html#5607" class="InductiveConstructor"
      >bool</a
      ><a name="20810" class="Symbol"
      >)</a
      ><a name="20811"
      >
      </a
      ><a name="20818" class="Symbol"
      >(</a
      ><a name="20819" href="Stlc.html#5823" class="InductiveConstructor"
      >abs</a
      ><a name="20822"
      > </a
      ><a name="20823" href="Stlc.html#6363" class="Function"
      >y</a
      ><a name="20824"
      > </a
      ><a name="20825" class="Symbol"
      >(</a
      ><a name="20826" href="Stlc.html#5607" class="InductiveConstructor"
      >bool</a
      ><a name="20830"
      > </a
      ><a name="20831" href="Stlc.html#5621" class="InductiveConstructor Operator"
      >&#8658;</a
      ><a name="20832"
      > </a
      ><a name="20833" href="Stlc.html#5607" class="InductiveConstructor"
      >bool</a
      ><a name="20837" class="Symbol"
      >)</a
      ><a name="20838"
      >
        </a
      ><a name="20847" class="Symbol"
      >(</a
      ><a name="20848" href="Stlc.html#5823" class="InductiveConstructor"
      >abs</a
      ><a name="20851"
      > </a
      ><a name="20852" href="Stlc.html#6372" class="Function"
      >z</a
      ><a name="20853"
      > </a
      ><a name="20854" href="Stlc.html#5607" class="InductiveConstructor"
      >bool</a
      ><a name="20858"
      >
          </a
      ><a name="20869" class="Symbol"
      >(</a
      ><a name="20870" href="Stlc.html#5794" class="InductiveConstructor"
      >app</a
      ><a name="20873"
      > </a
      ><a name="20874" class="Symbol"
      >(</a
      ><a name="20875" href="Stlc.html#5774" class="InductiveConstructor"
      >var</a
      ><a name="20878"
      > </a
      ><a name="20879" href="Stlc.html#6363" class="Function"
      >y</a
      ><a name="20880" class="Symbol"
      >)</a
      ><a name="20881"
      > </a
      ><a name="20882" class="Symbol"
      >(</a
      ><a name="20883" href="Stlc.html#5794" class="InductiveConstructor"
      >app</a
      ><a name="20886"
      > </a
      ><a name="20887" class="Symbol"
      >(</a
      ><a name="20888" href="Stlc.html#5774" class="InductiveConstructor"
      >var</a
      ><a name="20891"
      > </a
      ><a name="20892" href="Stlc.html#6354" class="Function"
      >x</a
      ><a name="20893" class="Symbol"
      >)</a
      ><a name="20894"
      > </a
      ><a name="20895" class="Symbol"
      >(</a
      ><a name="20896" href="Stlc.html#5774" class="InductiveConstructor"
      >var</a
      ><a name="20899"
      > </a
      ><a name="20900" href="Stlc.html#6372" class="Function"
      >z</a
      ><a name="20901" class="Symbol"
      >))))))</a
      ><a name="20907"
      > </a
      ><a name="20908" href="Stlc.html#19231" class="Datatype Operator"
      >&#8758;</a
      ><a name="20909"
      > </a
      ><a name="20910" href="Stlc.html#20779" class="Bound"
      >A</a
      >
</pre><!--{% endraw %}-->

We can also show that terms are _not_ typable.  For example, let's
formally check that there is no typing derivation assigning a type
to the term $$\lambda x:bool. \lambda y:bool. x\;y$$---i.e.,


$$\nexists A, \varnothing\vdash \lambda x:bool. \lambda y:bool. x\;y : A$$.

<!--{% raw %}--><pre class="Agda">
<a name="21211" class="Keyword"
      >postulate</a
      ><a name="21220"
      >
  </a
      ><a name="21223" href="Stlc.html#21223" class="Postulate"
      >typing-nonexample1</a
      ><a name="21241"
      > </a
      ><a name="21242" class="Symbol"
      >:</a
      ><a name="21243"
      > </a
      ><a name="21244" href="https://agda.github.io/agda-stdlib/Data.Product.html#884" class="Function"
      >&#8708;</a
      ><a name="21245"
      > </a
      ><a name="21246" class="Symbol"
      >&#955;</a
      ><a name="21247"
      > </a
      ><a name="21248" href="Stlc.html#21248" class="Bound"
      >A</a
      ><a name="21249"
      > </a
      ><a name="21250" class="Symbol"
      >&#8594;</a
      ><a name="21251"
      > </a
      ><a name="21252" href="Stlc.html#18299" class="Function"
      >&#8709;</a
      ><a name="21253"
      > </a
      ><a name="21254" href="Stlc.html#19231" class="Datatype Operator"
      >&#8866;</a
      ><a name="21255"
      >
    </a
      ><a name="21260" class="Symbol"
      >(</a
      ><a name="21261" href="Stlc.html#5823" class="InductiveConstructor"
      >abs</a
      ><a name="21264"
      > </a
      ><a name="21265" href="Stlc.html#6354" class="Function"
      >x</a
      ><a name="21266"
      > </a
      ><a name="21267" href="Stlc.html#5607" class="InductiveConstructor"
      >bool</a
      ><a name="21271"
      >
      </a
      ><a name="21278" class="Symbol"
      >(</a
      ><a name="21279" href="Stlc.html#5823" class="InductiveConstructor"
      >abs</a
      ><a name="21282"
      > </a
      ><a name="21283" href="Stlc.html#6363" class="Function"
      >y</a
      ><a name="21284"
      > </a
      ><a name="21285" href="Stlc.html#5607" class="InductiveConstructor"
      >bool</a
      ><a name="21289"
      >
        </a
      ><a name="21298" class="Symbol"
      >(</a
      ><a name="21299" href="Stlc.html#5794" class="InductiveConstructor"
      >app</a
      ><a name="21302"
      > </a
      ><a name="21303" class="Symbol"
      >(</a
      ><a name="21304" href="Stlc.html#5774" class="InductiveConstructor"
      >var</a
      ><a name="21307"
      > </a
      ><a name="21308" href="Stlc.html#6354" class="Function"
      >x</a
      ><a name="21309" class="Symbol"
      >)</a
      ><a name="21310"
      > </a
      ><a name="21311" class="Symbol"
      >(</a
      ><a name="21312" href="Stlc.html#5774" class="InductiveConstructor"
      >var</a
      ><a name="21315"
      > </a
      ><a name="21316" href="Stlc.html#6363" class="Function"
      >y</a
      ><a name="21317" class="Symbol"
      >))))</a
      ><a name="21321"
      > </a
      ><a name="21322" href="Stlc.html#19231" class="Datatype Operator"
      >&#8758;</a
      ><a name="21323"
      > </a
      ><a name="21324" href="Stlc.html#21248" class="Bound"
      >A</a
      >
</pre><!--{% endraw %}-->

#### Exercise: 3 stars, optional (typing-nonexample2)
Another nonexample:

$$\nexists A, \exists B, \varnothing\vdash \lambda x:A. x\;x : B$$.

<!--{% raw %}--><pre class="Agda">
<a name="21495" class="Keyword"
      >postulate</a
      ><a name="21504"
      >
  </a
      ><a name="21507" href="Stlc.html#21507" class="Postulate"
      >typing-nonexample2</a
      ><a name="21525"
      > </a
      ><a name="21526" class="Symbol"
      >:</a
      ><a name="21527"
      > </a
      ><a name="21528" href="https://agda.github.io/agda-stdlib/Data.Product.html#884" class="Function"
      >&#8708;</a
      ><a name="21529"
      > </a
      ><a name="21530" class="Symbol"
      >&#955;</a
      ><a name="21531"
      > </a
      ><a name="21532" href="Stlc.html#21532" class="Bound"
      >A</a
      ><a name="21533"
      > </a
      ><a name="21534" class="Symbol"
      >&#8594;</a
      ><a name="21535"
      > </a
      ><a name="21536" href="https://agda.github.io/agda-stdlib/Data.Product.html#823" class="Function"
      >&#8707;</a
      ><a name="21537"
      > </a
      ><a name="21538" class="Symbol"
      >&#955;</a
      ><a name="21539"
      > </a
      ><a name="21540" href="Stlc.html#21540" class="Bound"
      >B</a
      ><a name="21541"
      > </a
      ><a name="21542" class="Symbol"
      >&#8594;</a
      ><a name="21543"
      > </a
      ><a name="21544" href="Stlc.html#18299" class="Function"
      >&#8709;</a
      ><a name="21545"
      > </a
      ><a name="21546" href="Stlc.html#19231" class="Datatype Operator"
      >&#8866;</a
      ><a name="21547"
      >
    </a
      ><a name="21552" class="Symbol"
      >(</a
      ><a name="21553" href="Stlc.html#5823" class="InductiveConstructor"
      >abs</a
      ><a name="21556"
      > </a
      ><a name="21557" href="Stlc.html#6354" class="Function"
      >x</a
      ><a name="21558"
      > </a
      ><a name="21559" href="Stlc.html#21540" class="Bound"
      >B</a
      ><a name="21560"
      > </a
      ><a name="21561" class="Symbol"
      >(</a
      ><a name="21562" href="Stlc.html#5794" class="InductiveConstructor"
      >app</a
      ><a name="21565"
      > </a
      ><a name="21566" class="Symbol"
      >(</a
      ><a name="21567" href="Stlc.html#5774" class="InductiveConstructor"
      >var</a
      ><a name="21570"
      > </a
      ><a name="21571" href="Stlc.html#6354" class="Function"
      >x</a
      ><a name="21572" class="Symbol"
      >)</a
      ><a name="21573"
      > </a
      ><a name="21574" class="Symbol"
      >(</a
      ><a name="21575" href="Stlc.html#5774" class="InductiveConstructor"
      >var</a
      ><a name="21578"
      > </a
      ><a name="21579" href="Stlc.html#6354" class="Function"
      >x</a
      ><a name="21580" class="Symbol"
      >)))</a
      ><a name="21583"
      > </a
      ><a name="21584" href="Stlc.html#19231" class="Datatype Operator"
      >&#8758;</a
      ><a name="21585"
      > </a
      ><a name="21586" href="Stlc.html#21532" class="Bound"
      >A</a
      >
</pre><!--{% endraw %}-->
