---
title     : "Stlc: The Simply Typed Lambda-Calculus"
layout    : page
permalink : /Stlc
---

<div class="foldable">
<pre class="Agda">{% raw %}
<a name="134" class="Keyword"
      >open</a
      ><a name="138"
      > </a
      ><a name="139" class="Keyword"
      >import</a
      ><a name="145"
      > </a
      ><a name="146" class="Module"
      >Maps</a
      ><a name="150"
      > </a
      ><a name="151" class="Keyword"
      >using</a
      ><a name="156"
      > </a
      ><a name="157" class="Symbol"
      >(</a
      ><a name="158" href="Maps.html#2290" class="Datatype"
      >Id</a
      ><a name="160" class="Symbol"
      >;</a
      ><a name="161"
      > </a
      ><a name="162" href="Maps.html#2307" class="InductiveConstructor"
      >id</a
      ><a name="164" class="Symbol"
      >;</a
      ><a name="165"
      > </a
      ><a name="166" href="Maps.html#2344" class="Function Operator"
      >_&#8799;_</a
      ><a name="169" class="Symbol"
      >;</a
      ><a name="170"
      > </a
      ><a name="171" href="Maps.html#9409" class="Function"
      >PartialMap</a
      ><a name="181" class="Symbol"
      >;</a
      ><a name="182"
      > </a
      ><a name="183" class="Keyword"
      >module</a
      ><a name="189"
      > </a
      ><a name="190" href="Maps.html#9498" class="Module"
      >PartialMap</a
      ><a name="200" class="Symbol"
      >)</a
      ><a name="201"
      >
</a
      ><a name="202" class="Keyword"
      >open</a
      ><a name="206"
      > </a
      ><a name="207" class="Keyword"
      >import</a
      ><a name="213"
      > </a
      ><a name="214" href="https://agda.github.io/agda-stdlib/Data.Empty.html#1" class="Module"
      >Data.Empty</a
      ><a name="224"
      > </a
      ><a name="225" class="Keyword"
      >using</a
      ><a name="230"
      > </a
      ><a name="231" class="Symbol"
      >(</a
      ><a name="232" href="https://agda.github.io/agda-stdlib/Data.Empty.html#243" class="Datatype"
      >&#8869;</a
      ><a name="233" class="Symbol"
      >;</a
      ><a name="234"
      > </a
      ><a name="235" href="https://agda.github.io/agda-stdlib/Data.Empty.html#360" class="Function"
      >&#8869;-elim</a
      ><a name="241" class="Symbol"
      >)</a
      ><a name="242"
      >
</a
      ><a name="243" class="Keyword"
      >open</a
      ><a name="247"
      > </a
      ><a name="248" class="Keyword"
      >import</a
      ><a name="254"
      > </a
      ><a name="255" href="https://agda.github.io/agda-stdlib/Data.Maybe.html#1" class="Module"
      >Data.Maybe</a
      ><a name="265"
      > </a
      ><a name="266" class="Keyword"
      >using</a
      ><a name="271"
      > </a
      ><a name="272" class="Symbol"
      >(</a
      ><a name="273" href="https://agda.github.io/agda-stdlib/Data.Maybe.Base.html#335" class="Datatype"
      >Maybe</a
      ><a name="278" class="Symbol"
      >;</a
      ><a name="279"
      > </a
      ><a name="280" href="https://agda.github.io/agda-stdlib/Data.Maybe.html#1527" class="InductiveConstructor"
      >just</a
      ><a name="284" class="Symbol"
      >;</a
      ><a name="285"
      > </a
      ><a name="286" href="https://agda.github.io/agda-stdlib/Data.Maybe.html#1588" class="InductiveConstructor"
      >nothing</a
      ><a name="293" class="Symbol"
      >)</a
      ><a name="294"
      >
</a
      ><a name="295" class="Keyword"
      >open</a
      ><a name="299"
      > </a
      ><a name="300" class="Keyword"
      >import</a
      ><a name="306"
      > </a
      ><a name="307" href="https://agda.github.io/agda-stdlib/Data.Nat.html#1" class="Module"
      >Data.Nat</a
      ><a name="315"
      > </a
      ><a name="316" class="Keyword"
      >using</a
      ><a name="321"
      > </a
      ><a name="322" class="Symbol"
      >(</a
      ><a name="323" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#97" class="Datatype"
      >&#8469;</a
      ><a name="324" class="Symbol"
      >;</a
      ><a name="325"
      > </a
      ><a name="326" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor"
      >suc</a
      ><a name="329" class="Symbol"
      >;</a
      ><a name="330"
      > </a
      ><a name="331" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#115" class="InductiveConstructor"
      >zero</a
      ><a name="335" class="Symbol"
      >;</a
      ><a name="336"
      > </a
      ><a name="337" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator"
      >_+_</a
      ><a name="340" class="Symbol"
      >)</a
      ><a name="341"
      >
</a
      ><a name="342" class="Keyword"
      >open</a
      ><a name="346"
      > </a
      ><a name="347" class="Keyword"
      >import</a
      ><a name="353"
      > </a
      ><a name="354" href="https://agda.github.io/agda-stdlib/Data.Product.html#1" class="Module"
      >Data.Product</a
      ><a name="366"
      > </a
      ><a name="367" class="Keyword"
      >using</a
      ><a name="372"
      > </a
      ><a name="373" class="Symbol"
      >(</a
      ><a name="374" href="https://agda.github.io/agda-stdlib/Data.Product.html#823" class="Function"
      >&#8707;</a
      ><a name="375" class="Symbol"
      >;</a
      ><a name="376"
      > </a
      ><a name="377" href="https://agda.github.io/agda-stdlib/Data.Product.html#884" class="Function"
      >&#8708;</a
      ><a name="378" class="Symbol"
      >;</a
      ><a name="379"
      > </a
      ><a name="380" href="https://agda.github.io/agda-stdlib/Data.Product.html#509" class="InductiveConstructor Operator"
      >_,_</a
      ><a name="383" class="Symbol"
      >)</a
      ><a name="384"
      >
</a
      ><a name="385" class="Keyword"
      >open</a
      ><a name="389"
      > </a
      ><a name="390" class="Keyword"
      >import</a
      ><a name="396"
      > </a
      ><a name="397" href="https://agda.github.io/agda-stdlib/Function.html#1" class="Module"
      >Function</a
      ><a name="405"
      > </a
      ><a name="406" class="Keyword"
      >using</a
      ><a name="411"
      > </a
      ><a name="412" class="Symbol"
      >(</a
      ><a name="413" href="https://agda.github.io/agda-stdlib/Function.html#713" class="Function Operator"
      >_&#8728;_</a
      ><a name="416" class="Symbol"
      >;</a
      ><a name="417"
      > </a
      ><a name="418" href="https://agda.github.io/agda-stdlib/Function.html#1835" class="Function Operator"
      >_$_</a
      ><a name="421" class="Symbol"
      >)</a
      ><a name="422"
      >
</a
      ><a name="423" class="Keyword"
      >open</a
      ><a name="427"
      > </a
      ><a name="428" class="Keyword"
      >import</a
      ><a name="434"
      > </a
      ><a name="435" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#1" class="Module"
      >Relation.Nullary</a
      ><a name="451"
      > </a
      ><a name="452" class="Keyword"
      >using</a
      ><a name="457"
      > </a
      ><a name="458" class="Symbol"
      >(</a
      ><a name="459" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#484" class="Datatype"
      >Dec</a
      ><a name="462" class="Symbol"
      >;</a
      ><a name="463"
      > </a
      ><a name="464" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#520" class="InductiveConstructor"
      >yes</a
      ><a name="467" class="Symbol"
      >;</a
      ><a name="468"
      > </a
      ><a name="469" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#547" class="InductiveConstructor"
      >no</a
      ><a name="471" class="Symbol"
      >)</a
      ><a name="472"
      >
</a
      ><a name="473" class="Keyword"
      >open</a
      ><a name="477"
      > </a
      ><a name="478" class="Keyword"
      >import</a
      ><a name="484"
      > </a
      ><a name="485" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#1" class="Module"
      >Relation.Binary.PropositionalEquality</a
      ><a name="522"
      > </a
      ><a name="523" class="Keyword"
      >using</a
      ><a name="528"
      > </a
      ><a name="529" class="Symbol"
      >(</a
      ><a name="530" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >_&#8801;_</a
      ><a name="533" class="Symbol"
      >;</a
      ><a name="534"
      > </a
      ><a name="535" href="https://agda.github.io/agda-stdlib/Relation.Binary.Core.html#4493" class="Function Operator"
      >_&#8802;_</a
      ><a name="538" class="Symbol"
      >;</a
      ><a name="539"
      > </a
      ><a name="540" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="544" class="Symbol"
      >)</a
      >
{% endraw %}</pre>
</div>


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

<pre class="Agda">{% raw %}
<a name="5382" class="Keyword"
      >data</a
      ><a name="5386"
      > </a
      ><a name="5387" href="Stlc.html#5387" class="Datatype"
      >Type</a
      ><a name="5391"
      > </a
      ><a name="5392" class="Symbol"
      >:</a
      ><a name="5393"
      > </a
      ><a name="5394" class="PrimitiveType"
      >Set</a
      ><a name="5397"
      > </a
      ><a name="5398" class="Keyword"
      >where</a
      ><a name="5403"
      >
  </a
      ><a name="5406" href="Stlc.html#5406" class="InductiveConstructor"
      >bool</a
      ><a name="5410"
      > </a
      ><a name="5411" class="Symbol"
      >:</a
      ><a name="5412"
      > </a
      ><a name="5413" href="Stlc.html#5387" class="Datatype"
      >Type</a
      ><a name="5417"
      >
  </a
      ><a name="5420" href="Stlc.html#5420" class="InductiveConstructor Operator"
      >_&#8658;_</a
      ><a name="5423"
      >  </a
      ><a name="5425" class="Symbol"
      >:</a
      ><a name="5426"
      > </a
      ><a name="5427" href="Stlc.html#5387" class="Datatype"
      >Type</a
      ><a name="5431"
      > </a
      ><a name="5432" class="Symbol"
      >&#8594;</a
      ><a name="5433"
      > </a
      ><a name="5434" href="Stlc.html#5387" class="Datatype"
      >Type</a
      ><a name="5438"
      > </a
      ><a name="5439" class="Symbol"
      >&#8594;</a
      ><a name="5440"
      > </a
      ><a name="5441" href="Stlc.html#5387" class="Datatype"
      >Type</a
      ><a name="5445"
      >

</a
      ><a name="5447" class="Keyword"
      >infixr</a
      ><a name="5453"
      > </a
      ><a name="5454" class="Number"
      >5</a
      ><a name="5455"
      > </a
      ><a name="5456" href="Stlc.html#5420" class="InductiveConstructor Operator"
      >_&#8658;_</a
      >
{% endraw %}</pre>


### Terms

<pre class="Agda">{% raw %}
<a name="5497" class="Keyword"
      >data</a
      ><a name="5501"
      > </a
      ><a name="5502" href="Stlc.html#5502" class="Datatype"
      >Term</a
      ><a name="5506"
      > </a
      ><a name="5507" class="Symbol"
      >:</a
      ><a name="5508"
      > </a
      ><a name="5509" class="PrimitiveType"
      >Set</a
      ><a name="5512"
      > </a
      ><a name="5513" class="Keyword"
      >where</a
      ><a name="5518"
      >
  </a
      ><a name="5521" href="Stlc.html#5521" class="InductiveConstructor"
      >var</a
      ><a name="5524"
      >   </a
      ><a name="5527" class="Symbol"
      >:</a
      ><a name="5528"
      > </a
      ><a name="5529" href="Maps.html#2290" class="Datatype"
      >Id</a
      ><a name="5531"
      > </a
      ><a name="5532" class="Symbol"
      >&#8594;</a
      ><a name="5533"
      > </a
      ><a name="5534" href="Stlc.html#5502" class="Datatype"
      >Term</a
      ><a name="5538"
      >
  </a
      ><a name="5541" href="Stlc.html#5541" class="InductiveConstructor"
      >app</a
      ><a name="5544"
      >   </a
      ><a name="5547" class="Symbol"
      >:</a
      ><a name="5548"
      > </a
      ><a name="5549" href="Stlc.html#5502" class="Datatype"
      >Term</a
      ><a name="5553"
      > </a
      ><a name="5554" class="Symbol"
      >&#8594;</a
      ><a name="5555"
      > </a
      ><a name="5556" href="Stlc.html#5502" class="Datatype"
      >Term</a
      ><a name="5560"
      > </a
      ><a name="5561" class="Symbol"
      >&#8594;</a
      ><a name="5562"
      > </a
      ><a name="5563" href="Stlc.html#5502" class="Datatype"
      >Term</a
      ><a name="5567"
      >
  </a
      ><a name="5570" href="Stlc.html#5570" class="InductiveConstructor"
      >abs</a
      ><a name="5573"
      >   </a
      ><a name="5576" class="Symbol"
      >:</a
      ><a name="5577"
      > </a
      ><a name="5578" href="Maps.html#2290" class="Datatype"
      >Id</a
      ><a name="5580"
      > </a
      ><a name="5581" class="Symbol"
      >&#8594;</a
      ><a name="5582"
      > </a
      ><a name="5583" href="Stlc.html#5387" class="Datatype"
      >Type</a
      ><a name="5587"
      > </a
      ><a name="5588" class="Symbol"
      >&#8594;</a
      ><a name="5589"
      > </a
      ><a name="5590" href="Stlc.html#5502" class="Datatype"
      >Term</a
      ><a name="5594"
      > </a
      ><a name="5595" class="Symbol"
      >&#8594;</a
      ><a name="5596"
      > </a
      ><a name="5597" href="Stlc.html#5502" class="Datatype"
      >Term</a
      ><a name="5601"
      >
  </a
      ><a name="5604" href="Stlc.html#5604" class="InductiveConstructor"
      >true</a
      ><a name="5608"
      >  </a
      ><a name="5610" class="Symbol"
      >:</a
      ><a name="5611"
      > </a
      ><a name="5612" href="Stlc.html#5502" class="Datatype"
      >Term</a
      ><a name="5616"
      >
  </a
      ><a name="5619" href="Stlc.html#5619" class="InductiveConstructor"
      >false</a
      ><a name="5624"
      > </a
      ><a name="5625" class="Symbol"
      >:</a
      ><a name="5626"
      > </a
      ><a name="5627" href="Stlc.html#5502" class="Datatype"
      >Term</a
      ><a name="5631"
      >
  </a
      ><a name="5634" href="Stlc.html#5634" class="InductiveConstructor Operator"
      >if_then_else_</a
      ><a name="5647"
      > </a
      ><a name="5648" class="Symbol"
      >:</a
      ><a name="5649"
      > </a
      ><a name="5650" href="Stlc.html#5502" class="Datatype"
      >Term</a
      ><a name="5654"
      > </a
      ><a name="5655" class="Symbol"
      >&#8594;</a
      ><a name="5656"
      > </a
      ><a name="5657" href="Stlc.html#5502" class="Datatype"
      >Term</a
      ><a name="5661"
      > </a
      ><a name="5662" class="Symbol"
      >&#8594;</a
      ><a name="5663"
      > </a
      ><a name="5664" href="Stlc.html#5502" class="Datatype"
      >Term</a
      ><a name="5668"
      > </a
      ><a name="5669" class="Symbol"
      >&#8594;</a
      ><a name="5670"
      > </a
      ><a name="5671" href="Stlc.html#5502" class="Datatype"
      >Term</a
      >
{% endraw %}</pre>

<div class="hidden">
<pre class="Agda">{% raw %}
<a name="5722" class="Keyword"
      >infixr</a
      ><a name="5728"
      > </a
      ><a name="5729" class="Number"
      >8</a
      ><a name="5730"
      > </a
      ><a name="5731" href="Stlc.html#19564" class="InductiveConstructor Operator"
      >if_then_else_</a
      >
{% endraw %}</pre>
</div>

Note that an abstraction $$\lambda x:A.t$$ (formally, `abs x A t`) is
always annotated with the type $$A$$ of its parameter, in contrast
to Agda (and other functional languages like ML, Haskell, etc.),
which use _type inference_ to fill in missing annotations.  We're
not considering type inference here.

We introduce $$x, y, z$$ as names for variables.  The pragmas ensure
that $$id 0, id 1, id 2$$ display as $$x, y, z$$.

<pre class="Agda">{% raw %}
<a name="6203" href="Stlc.html#6203" class="Function"
      >x</a
      ><a name="6204"
      > </a
      ><a name="6205" class="Symbol"
      >=</a
      ><a name="6206"
      > </a
      ><a name="6207" href="Maps.html#2307" class="InductiveConstructor"
      >id</a
      ><a name="6209"
      > </a
      ><a name="6210" class="Number"
      >0</a
      ><a name="6211"
      >
</a
      ><a name="6212" href="Stlc.html#6212" class="Function"
      >y</a
      ><a name="6213"
      > </a
      ><a name="6214" class="Symbol"
      >=</a
      ><a name="6215"
      > </a
      ><a name="6216" href="Maps.html#2307" class="InductiveConstructor"
      >id</a
      ><a name="6218"
      > </a
      ><a name="6219" class="Number"
      >1</a
      ><a name="6220"
      >
</a
      ><a name="6221" href="Stlc.html#6221" class="Function"
      >z</a
      ><a name="6222"
      > </a
      ><a name="6223" class="Symbol"
      >=</a
      ><a name="6224"
      > </a
      ><a name="6225" href="Maps.html#2307" class="InductiveConstructor"
      >id</a
      ><a name="6227"
      > </a
      ><a name="6228" class="Number"
      >2</a
      ><a name="6229"
      >

</a
      ><a name="6231" class="Symbol"
      >{-#</a
      ><a name="6234"
      > </a
      ><a name="6235" class="Keyword"
      >DISPLAY</a
      ><a name="6242"
      > </a
      ><a name="6243" href="Maps.html#2307" class="InductiveConstructor"
      >id</a
      ><a name="6245"
      > </a
      ><a name="6246" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#115" class="InductiveConstructor"
      >zero</a
      ><a name="6250"
      > = </a
      ><a name="6253" href="Stlc.html#6203" class="Function"
      >x</a
      ><a name="6254"
      > </a
      ><a name="6255" class="Symbol"
      >#-}</a
      ><a name="6258"
      >
</a
      ><a name="6259" class="Symbol"
      >{-#</a
      ><a name="6262"
      > </a
      ><a name="6263" class="Keyword"
      >DISPLAY</a
      ><a name="6270"
      > </a
      ><a name="6271" href="Maps.html#2307" class="InductiveConstructor"
      >id</a
      ><a name="6273"
      > (</a
      ><a name="6275" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor"
      >suc</a
      ><a name="6278"
      > </a
      ><a name="6279" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#115" class="InductiveConstructor"
      >zero</a
      ><a name="6283"
      >) = </a
      ><a name="6287" href="Stlc.html#6212" class="Function"
      >y</a
      ><a name="6288"
      > </a
      ><a name="6289" class="Symbol"
      >#-}</a
      ><a name="6292"
      >
</a
      ><a name="6293" class="Symbol"
      >{-#</a
      ><a name="6296"
      > </a
      ><a name="6297" class="Keyword"
      >DISPLAY</a
      ><a name="6304"
      > </a
      ><a name="6305" href="Maps.html#2307" class="InductiveConstructor"
      >id</a
      ><a name="6307"
      > (</a
      ><a name="6309" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor"
      >suc</a
      ><a name="6312"
      > (</a
      ><a name="6314" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor"
      >suc</a
      ><a name="6317"
      > </a
      ><a name="6318" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#115" class="InductiveConstructor"
      >zero</a
      ><a name="6322"
      >)) = </a
      ><a name="6327" href="Stlc.html#6221" class="Function"
      >z</a
      ><a name="6328"
      > </a
      ><a name="6329" class="Symbol"
      >#-}</a
      >
{% endraw %}</pre>

Some examples...

$$\text{idB} = \lambda x:bool. x$$.

<pre class="Agda">{% raw %}
<a name="6413" href="Stlc.html#6413" class="Function"
      >idB</a
      ><a name="6416"
      > </a
      ><a name="6417" class="Symbol"
      >=</a
      ><a name="6418"
      > </a
      ><a name="6419" class="Symbol"
      >(</a
      ><a name="6420" href="Stlc.html#5570" class="InductiveConstructor"
      >abs</a
      ><a name="6423"
      > </a
      ><a name="6424" href="Stlc.html#6203" class="Function"
      >x</a
      ><a name="6425"
      > </a
      ><a name="6426" href="Stlc.html#5406" class="InductiveConstructor"
      >bool</a
      ><a name="6430"
      > </a
      ><a name="6431" class="Symbol"
      >(</a
      ><a name="6432" href="Stlc.html#5521" class="InductiveConstructor"
      >var</a
      ><a name="6435"
      > </a
      ><a name="6436" href="Stlc.html#6203" class="Function"
      >x</a
      ><a name="6437" class="Symbol"
      >))</a
      >
{% endraw %}</pre>

$$\text{idBB} = \lambda x:bool\rightarrow bool. x$$.

<pre class="Agda">{% raw %}
<a name="6519" href="Stlc.html#6519" class="Function"
      >idBB</a
      ><a name="6523"
      > </a
      ><a name="6524" class="Symbol"
      >=</a
      ><a name="6525"
      > </a
      ><a name="6526" class="Symbol"
      >(</a
      ><a name="6527" href="Stlc.html#5570" class="InductiveConstructor"
      >abs</a
      ><a name="6530"
      > </a
      ><a name="6531" href="Stlc.html#6203" class="Function"
      >x</a
      ><a name="6532"
      > </a
      ><a name="6533" class="Symbol"
      >(</a
      ><a name="6534" href="Stlc.html#5406" class="InductiveConstructor"
      >bool</a
      ><a name="6538"
      > </a
      ><a name="6539" href="Stlc.html#5420" class="InductiveConstructor Operator"
      >&#8658;</a
      ><a name="6540"
      > </a
      ><a name="6541" href="Stlc.html#5406" class="InductiveConstructor"
      >bool</a
      ><a name="6545" class="Symbol"
      >)</a
      ><a name="6546"
      > </a
      ><a name="6547" class="Symbol"
      >(</a
      ><a name="6548" href="Stlc.html#5521" class="InductiveConstructor"
      >var</a
      ><a name="6551"
      > </a
      ><a name="6552" href="Stlc.html#6203" class="Function"
      >x</a
      ><a name="6553" class="Symbol"
      >))</a
      >
{% endraw %}</pre>

$$\text{idBBBB} = \lambda x:(bool\rightarrow bool)\rightarrow (bool\rightarrow bool). x$$.

<pre class="Agda">{% raw %}
<a name="6673" href="Stlc.html#6673" class="Function"
      >idBBBB</a
      ><a name="6679"
      > </a
      ><a name="6680" class="Symbol"
      >=</a
      ><a name="6681"
      > </a
      ><a name="6682" class="Symbol"
      >(</a
      ><a name="6683" href="Stlc.html#5570" class="InductiveConstructor"
      >abs</a
      ><a name="6686"
      > </a
      ><a name="6687" href="Stlc.html#6203" class="Function"
      >x</a
      ><a name="6688"
      > </a
      ><a name="6689" class="Symbol"
      >((</a
      ><a name="6691" href="Stlc.html#5406" class="InductiveConstructor"
      >bool</a
      ><a name="6695"
      > </a
      ><a name="6696" href="Stlc.html#5420" class="InductiveConstructor Operator"
      >&#8658;</a
      ><a name="6697"
      > </a
      ><a name="6698" href="Stlc.html#5406" class="InductiveConstructor"
      >bool</a
      ><a name="6702" class="Symbol"
      >)</a
      ><a name="6703"
      > </a
      ><a name="6704" href="Stlc.html#5420" class="InductiveConstructor Operator"
      >&#8658;</a
      ><a name="6705"
      > </a
      ><a name="6706" class="Symbol"
      >(</a
      ><a name="6707" href="Stlc.html#5406" class="InductiveConstructor"
      >bool</a
      ><a name="6711"
      > </a
      ><a name="6712" href="Stlc.html#5420" class="InductiveConstructor Operator"
      >&#8658;</a
      ><a name="6713"
      > </a
      ><a name="6714" href="Stlc.html#5406" class="InductiveConstructor"
      >bool</a
      ><a name="6718" class="Symbol"
      >))</a
      ><a name="6720"
      > </a
      ><a name="6721" class="Symbol"
      >(</a
      ><a name="6722" href="Stlc.html#5521" class="InductiveConstructor"
      >var</a
      ><a name="6725"
      > </a
      ><a name="6726" href="Stlc.html#6203" class="Function"
      >x</a
      ><a name="6727" class="Symbol"
      >))</a
      >
{% endraw %}</pre>

$$\text{k} = \lambda x:bool. \lambda y:bool. x$$.

<pre class="Agda">{% raw %}
<a name="6806" href="Stlc.html#6806" class="Function"
      >k</a
      ><a name="6807"
      > </a
      ><a name="6808" class="Symbol"
      >=</a
      ><a name="6809"
      > </a
      ><a name="6810" class="Symbol"
      >(</a
      ><a name="6811" href="Stlc.html#5570" class="InductiveConstructor"
      >abs</a
      ><a name="6814"
      > </a
      ><a name="6815" href="Stlc.html#6203" class="Function"
      >x</a
      ><a name="6816"
      > </a
      ><a name="6817" href="Stlc.html#5406" class="InductiveConstructor"
      >bool</a
      ><a name="6821"
      > </a
      ><a name="6822" class="Symbol"
      >(</a
      ><a name="6823" href="Stlc.html#5570" class="InductiveConstructor"
      >abs</a
      ><a name="6826"
      > </a
      ><a name="6827" href="Stlc.html#6212" class="Function"
      >y</a
      ><a name="6828"
      > </a
      ><a name="6829" href="Stlc.html#5406" class="InductiveConstructor"
      >bool</a
      ><a name="6833"
      > </a
      ><a name="6834" class="Symbol"
      >(</a
      ><a name="6835" href="Stlc.html#5521" class="InductiveConstructor"
      >var</a
      ><a name="6838"
      > </a
      ><a name="6839" href="Stlc.html#6203" class="Function"
      >x</a
      ><a name="6840" class="Symbol"
      >)))</a
      >
{% endraw %}</pre>

$$\text{notB} = \lambda x:bool. \text{if }x\text{ then }false\text{ else }true$$.

<pre class="Agda">{% raw %}
<a name="6952" href="Stlc.html#6952" class="Function"
      >notB</a
      ><a name="6956"
      > </a
      ><a name="6957" class="Symbol"
      >=</a
      ><a name="6958"
      > </a
      ><a name="6959" class="Symbol"
      >(</a
      ><a name="6960" href="Stlc.html#5570" class="InductiveConstructor"
      >abs</a
      ><a name="6963"
      > </a
      ><a name="6964" href="Stlc.html#6203" class="Function"
      >x</a
      ><a name="6965"
      > </a
      ><a name="6966" href="Stlc.html#5406" class="InductiveConstructor"
      >bool</a
      ><a name="6970"
      > </a
      ><a name="6971" class="Symbol"
      >(</a
      ><a name="6972" href="Stlc.html#5634" class="InductiveConstructor Operator"
      >if</a
      ><a name="6974"
      > </a
      ><a name="6975" class="Symbol"
      >(</a
      ><a name="6976" href="Stlc.html#5521" class="InductiveConstructor"
      >var</a
      ><a name="6979"
      > </a
      ><a name="6980" href="Stlc.html#6203" class="Function"
      >x</a
      ><a name="6981" class="Symbol"
      >)</a
      ><a name="6982"
      > </a
      ><a name="6983" href="Stlc.html#5634" class="InductiveConstructor Operator"
      >then</a
      ><a name="6987"
      > </a
      ><a name="6988" href="Stlc.html#5619" class="InductiveConstructor"
      >false</a
      ><a name="6993"
      > </a
      ><a name="6994" href="Stlc.html#5634" class="InductiveConstructor Operator"
      >else</a
      ><a name="6998"
      > </a
      ><a name="6999" href="Stlc.html#5604" class="InductiveConstructor"
      >true</a
      ><a name="7003" class="Symbol"
      >))</a
      >
{% endraw %}</pre>

<div class="hidden">
<pre class="Agda">{% raw %}
<a name="7052" class="Symbol"
      >{-#</a
      ><a name="7055"
      > </a
      ><a name="7056" class="Keyword"
      >DISPLAY</a
      ><a name="7063"
      > </a
      ><a name="7064" href="Stlc.html#5570" class="InductiveConstructor"
      >abs</a
      ><a name="7067"
      > 0 </a
      ><a name="7070" href="Stlc.html#5406" class="InductiveConstructor"
      >bool</a
      ><a name="7074"
      > (</a
      ><a name="7076" href="Stlc.html#5521" class="InductiveConstructor"
      >var</a
      ><a name="7079"
      > 0) = </a
      ><a name="7085" href="Stlc.html#6413" class="Function"
      >idB</a
      ><a name="7088"
      > </a
      ><a name="7089" class="Symbol"
      >#-}</a
      ><a name="7092"
      >
</a
      ><a name="7093" class="Symbol"
      >{-#</a
      ><a name="7096"
      > </a
      ><a name="7097" class="Keyword"
      >DISPLAY</a
      ><a name="7104"
      > </a
      ><a name="7105" href="Stlc.html#5570" class="InductiveConstructor"
      >abs</a
      ><a name="7108"
      > 0 (</a
      ><a name="7112" href="Stlc.html#5406" class="InductiveConstructor"
      >bool</a
      ><a name="7116"
      > </a
      ><a name="7117" href="Stlc.html#5420" class="InductiveConstructor Operator"
      >&#8658;</a
      ><a name="7118"
      > </a
      ><a name="7119" href="Stlc.html#5406" class="InductiveConstructor"
      >bool</a
      ><a name="7123"
      >) (</a
      ><a name="7126" href="Stlc.html#5521" class="InductiveConstructor"
      >var</a
      ><a name="7129"
      > 0) = </a
      ><a name="7135" href="Stlc.html#6519" class="Function"
      >idBB</a
      ><a name="7139"
      > </a
      ><a name="7140" class="Symbol"
      >#-}</a
      ><a name="7143"
      >
</a
      ><a name="7144" class="Symbol"
      >{-#</a
      ><a name="7147"
      > </a
      ><a name="7148" class="Keyword"
      >DISPLAY</a
      ><a name="7155"
      > </a
      ><a name="7156" href="Stlc.html#5570" class="InductiveConstructor"
      >abs</a
      ><a name="7159"
      > 0 ((</a
      ><a name="7164" href="Stlc.html#5406" class="InductiveConstructor"
      >bool</a
      ><a name="7168"
      > </a
      ><a name="7169" href="Stlc.html#5420" class="InductiveConstructor Operator"
      >&#8658;</a
      ><a name="7170"
      > </a
      ><a name="7171" href="Stlc.html#5406" class="InductiveConstructor"
      >bool</a
      ><a name="7175"
      >) </a
      ><a name="7177" href="Stlc.html#5420" class="InductiveConstructor Operator"
      >&#8658;</a
      ><a name="7178"
      > (</a
      ><a name="7180" href="Stlc.html#5406" class="InductiveConstructor"
      >bool</a
      ><a name="7184"
      > </a
      ><a name="7185" href="Stlc.html#5420" class="InductiveConstructor Operator"
      >&#8658;</a
      ><a name="7186"
      > </a
      ><a name="7187" href="Stlc.html#5406" class="InductiveConstructor"
      >bool</a
      ><a name="7191"
      >)) (</a
      ><a name="7195" href="Stlc.html#5521" class="InductiveConstructor"
      >var</a
      ><a name="7198"
      > 0) = </a
      ><a name="7204" href="Stlc.html#6673" class="Function"
      >idBBBB</a
      ><a name="7210"
      > </a
      ><a name="7211" class="Symbol"
      >#-}</a
      ><a name="7214"
      >
</a
      ><a name="7215" class="Symbol"
      >{-#</a
      ><a name="7218"
      > </a
      ><a name="7219" class="Keyword"
      >DISPLAY</a
      ><a name="7226"
      > </a
      ><a name="7227" href="Stlc.html#5570" class="InductiveConstructor"
      >abs</a
      ><a name="7230"
      > 0 </a
      ><a name="7233" href="Stlc.html#5406" class="InductiveConstructor"
      >bool</a
      ><a name="7237"
      > (</a
      ><a name="7239" href="Stlc.html#5570" class="InductiveConstructor"
      >abs</a
      ><a name="7242"
      > </a
      ><a name="7243" href="Stlc.html#7243" class="Bound"
      >y</a
      ><a name="7244"
      > </a
      ><a name="7245" href="Stlc.html#5406" class="InductiveConstructor"
      >bool</a
      ><a name="7249"
      > (</a
      ><a name="7251" href="Stlc.html#5521" class="InductiveConstructor"
      >var</a
      ><a name="7254"
      > 0)) = </a
      ><a name="7261" href="Stlc.html#6806" class="Function"
      >k</a
      ><a name="7262"
      > </a
      ><a name="7263" class="Symbol"
      >#-}</a
      ><a name="7266"
      >
</a
      ><a name="7267" class="Symbol"
      >{-#</a
      ><a name="7270"
      > </a
      ><a name="7271" class="Keyword"
      >DISPLAY</a
      ><a name="7278"
      > </a
      ><a name="7279" href="Stlc.html#5570" class="InductiveConstructor"
      >abs</a
      ><a name="7282"
      > 0 </a
      ><a name="7285" href="Stlc.html#5406" class="InductiveConstructor"
      >bool</a
      ><a name="7289"
      > (</a
      ><a name="7291" href="Stlc.html#5634" class="InductiveConstructor Operator"
      >if</a
      ><a name="7293"
      > (</a
      ><a name="7295" href="Stlc.html#5521" class="InductiveConstructor"
      >var</a
      ><a name="7298"
      > 0) </a
      ><a name="7302" href="Stlc.html#5634" class="InductiveConstructor Operator"
      >then</a
      ><a name="7306"
      > </a
      ><a name="7307" href="Stlc.html#5619" class="InductiveConstructor"
      >false</a
      ><a name="7312"
      > </a
      ><a name="7313" href="Stlc.html#5634" class="InductiveConstructor Operator"
      >else</a
      ><a name="7317"
      > </a
      ><a name="7318" href="Stlc.html#5604" class="InductiveConstructor"
      >true</a
      ><a name="7322"
      >) = </a
      ><a name="7326" href="Stlc.html#6952" class="Function"
      >notB</a
      ><a name="7330"
      > </a
      ><a name="7331" class="Symbol"
      >#-}</a
      >
{% endraw %}</pre>
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

<pre class="Agda">{% raw %}
<a name="8570" href="Stlc.html#8570" class="Function Operator"
      >test_normalizeUnderLambda</a
      ><a name="8595"
      > </a
      ><a name="8596" class="Symbol"
      >:</a
      ><a name="8597"
      > </a
      ><a name="8598" class="Symbol"
      >(&#955;</a
      ><a name="8600"
      > </a
      ><a name="8601" class="Symbol"
      >(</a
      ><a name="8602" href="Stlc.html#8602" class="Bound"
      >x</a
      ><a name="8603"
      > </a
      ><a name="8604" class="Symbol"
      >:</a
      ><a name="8605"
      > </a
      ><a name="8606" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#97" class="Datatype"
      >&#8469;</a
      ><a name="8607" class="Symbol"
      >)</a
      ><a name="8608"
      > </a
      ><a name="8609" class="Symbol"
      >&#8594;</a
      ><a name="8610"
      > </a
      ><a name="8611" class="Number"
      >3</a
      ><a name="8612"
      > </a
      ><a name="8613" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator"
      >+</a
      ><a name="8614"
      > </a
      ><a name="8615" class="Number"
      >4</a
      ><a name="8616" class="Symbol"
      >)</a
      ><a name="8617"
      > </a
      ><a name="8618" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="8619"
      > </a
      ><a name="8620" class="Symbol"
      >(&#955;</a
      ><a name="8622"
      > </a
      ><a name="8623" class="Symbol"
      >(</a
      ><a name="8624" href="Stlc.html#8624" class="Bound"
      >x</a
      ><a name="8625"
      > </a
      ><a name="8626" class="Symbol"
      >:</a
      ><a name="8627"
      > </a
      ><a name="8628" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#97" class="Datatype"
      >&#8469;</a
      ><a name="8629" class="Symbol"
      >)</a
      ><a name="8630"
      > </a
      ><a name="8631" class="Symbol"
      >&#8594;</a
      ><a name="8632"
      > </a
      ><a name="8633" class="Number"
      >7</a
      ><a name="8634" class="Symbol"
      >)</a
      ><a name="8635"
      >
</a
      ><a name="8636" href="Stlc.html#8570" class="Function Operator"
      >test_normalizeUnderLambda</a
      ><a name="8661"
      > </a
      ><a name="8662" class="Symbol"
      >=</a
      ><a name="8663"
      > </a
      ><a name="8664" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      >
{% endraw %}</pre>

Most real-world functional programming languages make the second
choice---reduction of a function's body only begins when the
function is actually applied to an argument.  We also make the
second choice here.

<pre class="Agda">{% raw %}
<a name="8904" class="Keyword"
      >data</a
      ><a name="8908"
      > </a
      ><a name="8909" href="Stlc.html#8909" class="Datatype"
      >Value</a
      ><a name="8914"
      > </a
      ><a name="8915" class="Symbol"
      >:</a
      ><a name="8916"
      > </a
      ><a name="8917" href="Stlc.html#5502" class="Datatype"
      >Term</a
      ><a name="8921"
      > </a
      ><a name="8922" class="Symbol"
      >&#8594;</a
      ><a name="8923"
      > </a
      ><a name="8924" class="PrimitiveType"
      >Set</a
      ><a name="8927"
      > </a
      ><a name="8928" class="Keyword"
      >where</a
      ><a name="8933"
      >
  </a
      ><a name="8936" href="Stlc.html#8936" class="InductiveConstructor"
      >abs</a
      ><a name="8939"
      >   </a
      ><a name="8942" class="Symbol"
      >:</a
      ><a name="8943"
      > </a
      ><a name="8944" class="Symbol"
      >&#8704;</a
      ><a name="8945"
      > </a
      ><a name="8946" class="Symbol"
      >{</a
      ><a name="8947" href="Stlc.html#8947" class="Bound"
      >x</a
      ><a name="8948"
      > </a
      ><a name="8949" href="Stlc.html#8949" class="Bound"
      >A</a
      ><a name="8950"
      > </a
      ><a name="8951" href="Stlc.html#8951" class="Bound"
      >t</a
      ><a name="8952" class="Symbol"
      >}</a
      ><a name="8953"
      >
        </a
      ><a name="8962" class="Symbol"
      >&#8594;</a
      ><a name="8963"
      > </a
      ><a name="8964" href="Stlc.html#8909" class="Datatype"
      >Value</a
      ><a name="8969"
      > </a
      ><a name="8970" class="Symbol"
      >(</a
      ><a name="8971" href="Stlc.html#5570" class="InductiveConstructor"
      >abs</a
      ><a name="8974"
      > </a
      ><a name="8975" href="Stlc.html#8947" class="Bound"
      >x</a
      ><a name="8976"
      > </a
      ><a name="8977" href="Stlc.html#8949" class="Bound"
      >A</a
      ><a name="8978"
      > </a
      ><a name="8979" href="Stlc.html#8951" class="Bound"
      >t</a
      ><a name="8980" class="Symbol"
      >)</a
      ><a name="8981"
      >
  </a
      ><a name="8984" href="Stlc.html#8984" class="InductiveConstructor"
      >true</a
      ><a name="8988"
      >  </a
      ><a name="8990" class="Symbol"
      >:</a
      ><a name="8991"
      > </a
      ><a name="8992" href="Stlc.html#8909" class="Datatype"
      >Value</a
      ><a name="8997"
      > </a
      ><a name="8998" href="Stlc.html#5604" class="InductiveConstructor"
      >true</a
      ><a name="9002"
      >
  </a
      ><a name="9005" href="Stlc.html#9005" class="InductiveConstructor"
      >false</a
      ><a name="9010"
      > </a
      ><a name="9011" class="Symbol"
      >:</a
      ><a name="9012"
      > </a
      ><a name="9013" href="Stlc.html#8909" class="Datatype"
      >Value</a
      ><a name="9018"
      > </a
      ><a name="9019" href="Stlc.html#5619" class="InductiveConstructor"
      >false</a
      >
{% endraw %}</pre>

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

<pre class="Agda">{% raw %}
<a name="12129" href="Stlc.html#12129" class="Function Operator"
      >[_:=_]_</a
      ><a name="12136"
      > </a
      ><a name="12137" class="Symbol"
      >:</a
      ><a name="12138"
      > </a
      ><a name="12139" href="Maps.html#2290" class="Datatype"
      >Id</a
      ><a name="12141"
      > </a
      ><a name="12142" class="Symbol"
      >-&gt;</a
      ><a name="12144"
      > </a
      ><a name="12145" href="Stlc.html#5502" class="Datatype"
      >Term</a
      ><a name="12149"
      > </a
      ><a name="12150" class="Symbol"
      >-&gt;</a
      ><a name="12152"
      > </a
      ><a name="12153" href="Stlc.html#5502" class="Datatype"
      >Term</a
      ><a name="12157"
      > </a
      ><a name="12158" class="Symbol"
      >-&gt;</a
      ><a name="12160"
      > </a
      ><a name="12161" href="Stlc.html#5502" class="Datatype"
      >Term</a
      ><a name="12165"
      >
</a
      ><a name="12166" href="Stlc.html#12129" class="Function Operator"
      >[</a
      ><a name="12167"
      > </a
      ><a name="12168" href="Stlc.html#12168" class="Bound"
      >x</a
      ><a name="12169"
      > </a
      ><a name="12170" href="Stlc.html#12129" class="Function Operator"
      >:=</a
      ><a name="12172"
      > </a
      ><a name="12173" href="Stlc.html#12173" class="Bound"
      >v</a
      ><a name="12174"
      > </a
      ><a name="12175" href="Stlc.html#12129" class="Function Operator"
      >]</a
      ><a name="12176"
      > </a
      ><a name="12177" class="Symbol"
      >(</a
      ><a name="12178" href="Stlc.html#5521" class="InductiveConstructor"
      >var</a
      ><a name="12181"
      > </a
      ><a name="12182" href="Stlc.html#12182" class="Bound"
      >y</a
      ><a name="12183" class="Symbol"
      >)</a
      ><a name="12184"
      > </a
      ><a name="12185" class="Keyword"
      >with</a
      ><a name="12189"
      > </a
      ><a name="12190" href="Stlc.html#12168" class="Bound"
      >x</a
      ><a name="12191"
      > </a
      ><a name="12192" href="Maps.html#2344" class="Function Operator"
      >&#8799;</a
      ><a name="12193"
      > </a
      ><a name="12194" href="Stlc.html#12182" class="Bound"
      >y</a
      ><a name="12195"
      >
</a
      ><a name="12196" class="Symbol"
      >...</a
      ><a name="12199"
      > </a
      ><a name="12200" class="Symbol"
      >|</a
      ><a name="12201"
      > </a
      ><a name="12202" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#520" class="InductiveConstructor"
      >yes</a
      ><a name="12205"
      > </a
      ><a name="12206" href="Stlc.html#12206" class="Bound"
      >x=y</a
      ><a name="12209"
      > </a
      ><a name="12210" class="Symbol"
      >=</a
      ><a name="12211"
      > </a
      ><a name="12212" href="Stlc.html#12173" class="Bound"
      >v</a
      ><a name="12213"
      >
</a
      ><a name="12214" class="Symbol"
      >...</a
      ><a name="12217"
      > </a
      ><a name="12218" class="Symbol"
      >|</a
      ><a name="12219"
      > </a
      ><a name="12220" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#547" class="InductiveConstructor"
      >no</a
      ><a name="12222"
      >  </a
      ><a name="12224" href="Stlc.html#12224" class="Bound"
      >x&#8800;y</a
      ><a name="12227"
      > </a
      ><a name="12228" class="Symbol"
      >=</a
      ><a name="12229"
      > </a
      ><a name="12230" href="Stlc.html#5521" class="InductiveConstructor"
      >var</a
      ><a name="12233"
      > </a
      ><a name="12234" href="Stlc.html#12182" class="Bound"
      >y</a
      ><a name="12235"
      >
</a
      ><a name="12236" href="Stlc.html#12129" class="Function Operator"
      >[</a
      ><a name="12237"
      > </a
      ><a name="12238" href="Stlc.html#12238" class="Bound"
      >x</a
      ><a name="12239"
      > </a
      ><a name="12240" href="Stlc.html#12129" class="Function Operator"
      >:=</a
      ><a name="12242"
      > </a
      ><a name="12243" href="Stlc.html#12243" class="Bound"
      >v</a
      ><a name="12244"
      > </a
      ><a name="12245" href="Stlc.html#12129" class="Function Operator"
      >]</a
      ><a name="12246"
      > </a
      ><a name="12247" class="Symbol"
      >(</a
      ><a name="12248" href="Stlc.html#5541" class="InductiveConstructor"
      >app</a
      ><a name="12251"
      > </a
      ><a name="12252" href="Stlc.html#12252" class="Bound"
      >s</a
      ><a name="12253"
      > </a
      ><a name="12254" href="Stlc.html#12254" class="Bound"
      >t</a
      ><a name="12255" class="Symbol"
      >)</a
      ><a name="12256"
      > </a
      ><a name="12257" class="Symbol"
      >=</a
      ><a name="12258"
      > </a
      ><a name="12259" href="Stlc.html#5541" class="InductiveConstructor"
      >app</a
      ><a name="12262"
      > </a
      ><a name="12263" class="Symbol"
      >(</a
      ><a name="12264" href="Stlc.html#12129" class="Function Operator"
      >[</a
      ><a name="12265"
      > </a
      ><a name="12266" href="Stlc.html#12238" class="Bound"
      >x</a
      ><a name="12267"
      > </a
      ><a name="12268" href="Stlc.html#12129" class="Function Operator"
      >:=</a
      ><a name="12270"
      > </a
      ><a name="12271" href="Stlc.html#12243" class="Bound"
      >v</a
      ><a name="12272"
      > </a
      ><a name="12273" href="Stlc.html#12129" class="Function Operator"
      >]</a
      ><a name="12274"
      > </a
      ><a name="12275" href="Stlc.html#12252" class="Bound"
      >s</a
      ><a name="12276" class="Symbol"
      >)</a
      ><a name="12277"
      > </a
      ><a name="12278" class="Symbol"
      >(</a
      ><a name="12279" href="Stlc.html#12129" class="Function Operator"
      >[</a
      ><a name="12280"
      > </a
      ><a name="12281" href="Stlc.html#12238" class="Bound"
      >x</a
      ><a name="12282"
      > </a
      ><a name="12283" href="Stlc.html#12129" class="Function Operator"
      >:=</a
      ><a name="12285"
      > </a
      ><a name="12286" href="Stlc.html#12243" class="Bound"
      >v</a
      ><a name="12287"
      > </a
      ><a name="12288" href="Stlc.html#12129" class="Function Operator"
      >]</a
      ><a name="12289"
      > </a
      ><a name="12290" href="Stlc.html#12254" class="Bound"
      >t</a
      ><a name="12291" class="Symbol"
      >)</a
      ><a name="12292"
      >
</a
      ><a name="12293" href="Stlc.html#12129" class="Function Operator"
      >[</a
      ><a name="12294"
      > </a
      ><a name="12295" href="Stlc.html#12295" class="Bound"
      >x</a
      ><a name="12296"
      > </a
      ><a name="12297" href="Stlc.html#12129" class="Function Operator"
      >:=</a
      ><a name="12299"
      > </a
      ><a name="12300" href="Stlc.html#12300" class="Bound"
      >v</a
      ><a name="12301"
      > </a
      ><a name="12302" href="Stlc.html#12129" class="Function Operator"
      >]</a
      ><a name="12303"
      > </a
      ><a name="12304" class="Symbol"
      >(</a
      ><a name="12305" href="Stlc.html#5570" class="InductiveConstructor"
      >abs</a
      ><a name="12308"
      > </a
      ><a name="12309" href="Stlc.html#12309" class="Bound"
      >y</a
      ><a name="12310"
      > </a
      ><a name="12311" href="Stlc.html#12311" class="Bound"
      >A</a
      ><a name="12312"
      > </a
      ><a name="12313" href="Stlc.html#12313" class="Bound"
      >t</a
      ><a name="12314" class="Symbol"
      >)</a
      ><a name="12315"
      > </a
      ><a name="12316" class="Keyword"
      >with</a
      ><a name="12320"
      > </a
      ><a name="12321" href="Stlc.html#12295" class="Bound"
      >x</a
      ><a name="12322"
      > </a
      ><a name="12323" href="Maps.html#2344" class="Function Operator"
      >&#8799;</a
      ><a name="12324"
      > </a
      ><a name="12325" href="Stlc.html#12309" class="Bound"
      >y</a
      ><a name="12326"
      >
</a
      ><a name="12327" class="Symbol"
      >...</a
      ><a name="12330"
      > </a
      ><a name="12331" class="Symbol"
      >|</a
      ><a name="12332"
      > </a
      ><a name="12333" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#520" class="InductiveConstructor"
      >yes</a
      ><a name="12336"
      > </a
      ><a name="12337" href="Stlc.html#12337" class="Bound"
      >x=y</a
      ><a name="12340"
      > </a
      ><a name="12341" class="Symbol"
      >=</a
      ><a name="12342"
      > </a
      ><a name="12343" href="Stlc.html#5570" class="InductiveConstructor"
      >abs</a
      ><a name="12346"
      > </a
      ><a name="12347" href="Stlc.html#12309" class="Bound"
      >y</a
      ><a name="12348"
      > </a
      ><a name="12349" href="Stlc.html#12311" class="Bound"
      >A</a
      ><a name="12350"
      > </a
      ><a name="12351" href="Stlc.html#12313" class="Bound"
      >t</a
      ><a name="12352"
      >
</a
      ><a name="12353" class="Symbol"
      >...</a
      ><a name="12356"
      > </a
      ><a name="12357" class="Symbol"
      >|</a
      ><a name="12358"
      > </a
      ><a name="12359" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#547" class="InductiveConstructor"
      >no</a
      ><a name="12361"
      >  </a
      ><a name="12363" href="Stlc.html#12363" class="Bound"
      >x&#8800;y</a
      ><a name="12366"
      > </a
      ><a name="12367" class="Symbol"
      >=</a
      ><a name="12368"
      > </a
      ><a name="12369" href="Stlc.html#5570" class="InductiveConstructor"
      >abs</a
      ><a name="12372"
      > </a
      ><a name="12373" href="Stlc.html#12309" class="Bound"
      >y</a
      ><a name="12374"
      > </a
      ><a name="12375" href="Stlc.html#12311" class="Bound"
      >A</a
      ><a name="12376"
      > </a
      ><a name="12377" class="Symbol"
      >(</a
      ><a name="12378" href="Stlc.html#12129" class="Function Operator"
      >[</a
      ><a name="12379"
      > </a
      ><a name="12380" href="Stlc.html#12295" class="Bound"
      >x</a
      ><a name="12381"
      > </a
      ><a name="12382" href="Stlc.html#12129" class="Function Operator"
      >:=</a
      ><a name="12384"
      > </a
      ><a name="12385" href="Stlc.html#12300" class="Bound"
      >v</a
      ><a name="12386"
      > </a
      ><a name="12387" href="Stlc.html#12129" class="Function Operator"
      >]</a
      ><a name="12388"
      > </a
      ><a name="12389" href="Stlc.html#12313" class="Bound"
      >t</a
      ><a name="12390" class="Symbol"
      >)</a
      ><a name="12391"
      >
</a
      ><a name="12392" href="Stlc.html#12129" class="Function Operator"
      >[</a
      ><a name="12393"
      > </a
      ><a name="12394" href="Stlc.html#12394" class="Bound"
      >x</a
      ><a name="12395"
      > </a
      ><a name="12396" href="Stlc.html#12129" class="Function Operator"
      >:=</a
      ><a name="12398"
      > </a
      ><a name="12399" href="Stlc.html#12399" class="Bound"
      >v</a
      ><a name="12400"
      > </a
      ><a name="12401" href="Stlc.html#12129" class="Function Operator"
      >]</a
      ><a name="12402"
      > </a
      ><a name="12403" href="Stlc.html#5604" class="InductiveConstructor"
      >true</a
      ><a name="12407"
      >  </a
      ><a name="12409" class="Symbol"
      >=</a
      ><a name="12410"
      > </a
      ><a name="12411" href="Stlc.html#5604" class="InductiveConstructor"
      >true</a
      ><a name="12415"
      >
</a
      ><a name="12416" href="Stlc.html#12129" class="Function Operator"
      >[</a
      ><a name="12417"
      > </a
      ><a name="12418" href="Stlc.html#12418" class="Bound"
      >x</a
      ><a name="12419"
      > </a
      ><a name="12420" href="Stlc.html#12129" class="Function Operator"
      >:=</a
      ><a name="12422"
      > </a
      ><a name="12423" href="Stlc.html#12423" class="Bound"
      >v</a
      ><a name="12424"
      > </a
      ><a name="12425" href="Stlc.html#12129" class="Function Operator"
      >]</a
      ><a name="12426"
      > </a
      ><a name="12427" href="Stlc.html#5619" class="InductiveConstructor"
      >false</a
      ><a name="12432"
      > </a
      ><a name="12433" class="Symbol"
      >=</a
      ><a name="12434"
      > </a
      ><a name="12435" href="Stlc.html#5619" class="InductiveConstructor"
      >false</a
      ><a name="12440"
      >
</a
      ><a name="12441" href="Stlc.html#12129" class="Function Operator"
      >[</a
      ><a name="12442"
      > </a
      ><a name="12443" href="Stlc.html#12443" class="Bound"
      >x</a
      ><a name="12444"
      > </a
      ><a name="12445" href="Stlc.html#12129" class="Function Operator"
      >:=</a
      ><a name="12447"
      > </a
      ><a name="12448" href="Stlc.html#12448" class="Bound"
      >v</a
      ><a name="12449"
      > </a
      ><a name="12450" href="Stlc.html#12129" class="Function Operator"
      >]</a
      ><a name="12451"
      > </a
      ><a name="12452" class="Symbol"
      >(</a
      ><a name="12453" href="Stlc.html#5634" class="InductiveConstructor Operator"
      >if</a
      ><a name="12455"
      > </a
      ><a name="12456" href="Stlc.html#12456" class="Bound"
      >s</a
      ><a name="12457"
      > </a
      ><a name="12458" href="Stlc.html#5634" class="InductiveConstructor Operator"
      >then</a
      ><a name="12462"
      > </a
      ><a name="12463" href="Stlc.html#12463" class="Bound"
      >t</a
      ><a name="12464"
      > </a
      ><a name="12465" href="Stlc.html#5634" class="InductiveConstructor Operator"
      >else</a
      ><a name="12469"
      > </a
      ><a name="12470" href="Stlc.html#12470" class="Bound"
      >u</a
      ><a name="12471" class="Symbol"
      >)</a
      ><a name="12472"
      > </a
      ><a name="12473" class="Symbol"
      >=</a
      ><a name="12474"
      >
  </a
      ><a name="12477" href="Stlc.html#5634" class="InductiveConstructor Operator"
      >if</a
      ><a name="12479"
      > </a
      ><a name="12480" href="Stlc.html#12129" class="Function Operator"
      >[</a
      ><a name="12481"
      > </a
      ><a name="12482" href="Stlc.html#12443" class="Bound"
      >x</a
      ><a name="12483"
      > </a
      ><a name="12484" href="Stlc.html#12129" class="Function Operator"
      >:=</a
      ><a name="12486"
      > </a
      ><a name="12487" href="Stlc.html#12448" class="Bound"
      >v</a
      ><a name="12488"
      > </a
      ><a name="12489" href="Stlc.html#12129" class="Function Operator"
      >]</a
      ><a name="12490"
      > </a
      ><a name="12491" href="Stlc.html#12456" class="Bound"
      >s</a
      ><a name="12492"
      > </a
      ><a name="12493" href="Stlc.html#5634" class="InductiveConstructor Operator"
      >then</a
      ><a name="12497"
      > </a
      ><a name="12498" href="Stlc.html#12129" class="Function Operator"
      >[</a
      ><a name="12499"
      > </a
      ><a name="12500" href="Stlc.html#12443" class="Bound"
      >x</a
      ><a name="12501"
      > </a
      ><a name="12502" href="Stlc.html#12129" class="Function Operator"
      >:=</a
      ><a name="12504"
      > </a
      ><a name="12505" href="Stlc.html#12448" class="Bound"
      >v</a
      ><a name="12506"
      > </a
      ><a name="12507" href="Stlc.html#12129" class="Function Operator"
      >]</a
      ><a name="12508"
      > </a
      ><a name="12509" href="Stlc.html#12463" class="Bound"
      >t</a
      ><a name="12510"
      > </a
      ><a name="12511" href="Stlc.html#5634" class="InductiveConstructor Operator"
      >else</a
      ><a name="12515"
      >  </a
      ><a name="12517" href="Stlc.html#12129" class="Function Operator"
      >[</a
      ><a name="12518"
      > </a
      ><a name="12519" href="Stlc.html#12443" class="Bound"
      >x</a
      ><a name="12520"
      > </a
      ><a name="12521" href="Stlc.html#12129" class="Function Operator"
      >:=</a
      ><a name="12523"
      > </a
      ><a name="12524" href="Stlc.html#12448" class="Bound"
      >v</a
      ><a name="12525"
      > </a
      ><a name="12526" href="Stlc.html#12129" class="Function Operator"
      >]</a
      ><a name="12527"
      > </a
      ><a name="12528" href="Stlc.html#12470" class="Bound"
      >u</a
      >
{% endraw %}</pre>

<div class="hidden">
<pre class="Agda">{% raw %}
<a name="12576" class="Keyword"
      >infix</a
      ><a name="12581"
      > </a
      ><a name="12582" class="Number"
      >9</a
      ><a name="12583"
      > </a
      ><a name="12584" href="Stlc.html#12129" class="Function Operator"
      >[_:=_]_</a
      >
{% endraw %}</pre>
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
<pre class="Agda">{% raw %}
<a name="13520" class="Keyword"
      >data</a
      ><a name="13524"
      > </a
      ><a name="13525" href="Stlc.html#13525" class="Datatype Operator"
      >[_:=_]_==&gt;_</a
      ><a name="13536"
      > </a
      ><a name="13537" class="Symbol"
      >(</a
      ><a name="13538" href="Stlc.html#13538" class="Bound"
      >x</a
      ><a name="13539"
      > </a
      ><a name="13540" class="Symbol"
      >:</a
      ><a name="13541"
      > </a
      ><a name="13542" href="Maps.html#2290" class="Datatype"
      >Id</a
      ><a name="13544" class="Symbol"
      >)</a
      ><a name="13545"
      > </a
      ><a name="13546" class="Symbol"
      >(</a
      ><a name="13547" href="Stlc.html#13547" class="Bound"
      >s</a
      ><a name="13548"
      > </a
      ><a name="13549" class="Symbol"
      >:</a
      ><a name="13550"
      > </a
      ><a name="13551" href="Stlc.html#5502" class="Datatype"
      >Term</a
      ><a name="13555" class="Symbol"
      >)</a
      ><a name="13556"
      > </a
      ><a name="13557" class="Symbol"
      >:</a
      ><a name="13558"
      > </a
      ><a name="13559" href="Stlc.html#5502" class="Datatype"
      >Term</a
      ><a name="13563"
      > </a
      ><a name="13564" class="Symbol"
      >-&gt;</a
      ><a name="13566"
      > </a
      ><a name="13567" href="Stlc.html#5502" class="Datatype"
      >Term</a
      ><a name="13571"
      > </a
      ><a name="13572" class="Symbol"
      >-&gt;</a
      ><a name="13574"
      > </a
      ><a name="13575" class="PrimitiveType"
      >Set</a
      ><a name="13578"
      > </a
      ><a name="13579" class="Keyword"
      >where</a
      ><a name="13584"
      >
  </a
      ><a name="13587" href="Stlc.html#13587" class="InductiveConstructor"
      >var1</a
      ><a name="13591"
      > </a
      ><a name="13592" class="Symbol"
      >:</a
      ><a name="13593"
      > </a
      ><a name="13594" href="Stlc.html#13525" class="Datatype Operator"
      >[</a
      ><a name="13595"
      > </a
      ><a name="13596" href="Stlc.html#13538" class="Bound"
      >x</a
      ><a name="13597"
      > </a
      ><a name="13598" href="Stlc.html#13525" class="Datatype Operator"
      >:=</a
      ><a name="13600"
      > </a
      ><a name="13601" href="Stlc.html#13547" class="Bound"
      >s</a
      ><a name="13602"
      > </a
      ><a name="13603" href="Stlc.html#13525" class="Datatype Operator"
      >]</a
      ><a name="13604"
      > </a
      ><a name="13605" class="Symbol"
      >(</a
      ><a name="13606" href="Stlc.html#5521" class="InductiveConstructor"
      >var</a
      ><a name="13609"
      > </a
      ><a name="13610" href="Stlc.html#13538" class="Bound"
      >x</a
      ><a name="13611" class="Symbol"
      >)</a
      ><a name="13612"
      > </a
      ><a name="13613" href="Stlc.html#13525" class="Datatype Operator"
      >==&gt;</a
      ><a name="13616"
      > </a
      ><a name="13617" href="Stlc.html#13547" class="Bound"
      >s</a
      ><a name="13618"
      >
  </a
      ><a name="13621" class="Comment"
      >{- FILL IN HERE -}</a
      >
{% endraw %}</pre>

<pre class="Agda">{% raw %}
<a name="13665" class="Keyword"
      >postulate</a
      ><a name="13674"
      >
  </a
      ><a name="13677" href="Stlc.html#13677" class="Postulate"
      >subst-correct</a
      ><a name="13690"
      > </a
      ><a name="13691" class="Symbol"
      >:</a
      ><a name="13692"
      > </a
      ><a name="13693" class="Symbol"
      >&#8704;</a
      ><a name="13694"
      > </a
      ><a name="13695" href="Stlc.html#13695" class="Bound"
      >s</a
      ><a name="13696"
      > </a
      ><a name="13697" href="Stlc.html#13697" class="Bound"
      >x</a
      ><a name="13698"
      > </a
      ><a name="13699" href="Stlc.html#13699" class="Bound"
      >t</a
      ><a name="13700"
      > </a
      ><a name="13701" href="Stlc.html#13701" class="Bound"
      >t'</a
      ><a name="13703"
      >
                </a
      ><a name="13720" class="Symbol"
      >&#8594;</a
      ><a name="13721"
      > </a
      ><a name="13722" href="Stlc.html#12129" class="Function Operator"
      >[</a
      ><a name="13723"
      > </a
      ><a name="13724" href="Stlc.html#13697" class="Bound"
      >x</a
      ><a name="13725"
      > </a
      ><a name="13726" href="Stlc.html#12129" class="Function Operator"
      >:=</a
      ><a name="13728"
      > </a
      ><a name="13729" href="Stlc.html#13695" class="Bound"
      >s</a
      ><a name="13730"
      > </a
      ><a name="13731" href="Stlc.html#12129" class="Function Operator"
      >]</a
      ><a name="13732"
      > </a
      ><a name="13733" href="Stlc.html#13699" class="Bound"
      >t</a
      ><a name="13734"
      > </a
      ><a name="13735" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="13736"
      > </a
      ><a name="13737" href="Stlc.html#13701" class="Bound"
      >t'</a
      ><a name="13739"
      >
                </a
      ><a name="13756" class="Symbol"
      >&#8594;</a
      ><a name="13757"
      > </a
      ><a name="13758" href="Stlc.html#13525" class="Datatype Operator"
      >[</a
      ><a name="13759"
      > </a
      ><a name="13760" href="Stlc.html#13697" class="Bound"
      >x</a
      ><a name="13761"
      > </a
      ><a name="13762" href="Stlc.html#13525" class="Datatype Operator"
      >:=</a
      ><a name="13764"
      > </a
      ><a name="13765" href="Stlc.html#13695" class="Bound"
      >s</a
      ><a name="13766"
      > </a
      ><a name="13767" href="Stlc.html#13525" class="Datatype Operator"
      >]</a
      ><a name="13768"
      > </a
      ><a name="13769" href="Stlc.html#13699" class="Bound"
      >t</a
      ><a name="13770"
      > </a
      ><a name="13771" href="Stlc.html#13525" class="Datatype Operator"
      >==&gt;</a
      ><a name="13774"
      > </a
      ><a name="13775" href="Stlc.html#13701" class="Bound"
      >t'</a
      >
{% endraw %}</pre>

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

<pre class="Agda">{% raw %}
<a name="15040" class="Keyword"
      >data</a
      ><a name="15044"
      > </a
      ><a name="15045" href="Stlc.html#15045" class="Datatype Operator"
      >_==&gt;_</a
      ><a name="15050"
      > </a
      ><a name="15051" class="Symbol"
      >:</a
      ><a name="15052"
      > </a
      ><a name="15053" href="Stlc.html#5502" class="Datatype"
      >Term</a
      ><a name="15057"
      > </a
      ><a name="15058" class="Symbol"
      >&#8594;</a
      ><a name="15059"
      > </a
      ><a name="15060" href="Stlc.html#5502" class="Datatype"
      >Term</a
      ><a name="15064"
      > </a
      ><a name="15065" class="Symbol"
      >&#8594;</a
      ><a name="15066"
      > </a
      ><a name="15067" class="PrimitiveType"
      >Set</a
      ><a name="15070"
      > </a
      ><a name="15071" class="Keyword"
      >where</a
      ><a name="15076"
      >
  </a
      ><a name="15079" href="Stlc.html#15079" class="InductiveConstructor"
      >red</a
      ><a name="15082"
      >     </a
      ><a name="15087" class="Symbol"
      >:</a
      ><a name="15088"
      > </a
      ><a name="15089" class="Symbol"
      >&#8704;</a
      ><a name="15090"
      > </a
      ><a name="15091" class="Symbol"
      >{</a
      ><a name="15092" href="Stlc.html#15092" class="Bound"
      >x</a
      ><a name="15093"
      > </a
      ><a name="15094" href="Stlc.html#15094" class="Bound"
      >A</a
      ><a name="15095"
      > </a
      ><a name="15096" href="Stlc.html#15096" class="Bound"
      >s</a
      ><a name="15097"
      > </a
      ><a name="15098" href="Stlc.html#15098" class="Bound"
      >t</a
      ><a name="15099" class="Symbol"
      >}</a
      ><a name="15100"
      >
          </a
      ><a name="15111" class="Symbol"
      >&#8594;</a
      ><a name="15112"
      > </a
      ><a name="15113" href="Stlc.html#8909" class="Datatype"
      >Value</a
      ><a name="15118"
      > </a
      ><a name="15119" href="Stlc.html#15098" class="Bound"
      >t</a
      ><a name="15120"
      >
          </a
      ><a name="15131" class="Symbol"
      >&#8594;</a
      ><a name="15132"
      > </a
      ><a name="15133" href="Stlc.html#5541" class="InductiveConstructor"
      >app</a
      ><a name="15136"
      > </a
      ><a name="15137" class="Symbol"
      >(</a
      ><a name="15138" href="Stlc.html#5570" class="InductiveConstructor"
      >abs</a
      ><a name="15141"
      > </a
      ><a name="15142" href="Stlc.html#15092" class="Bound"
      >x</a
      ><a name="15143"
      > </a
      ><a name="15144" href="Stlc.html#15094" class="Bound"
      >A</a
      ><a name="15145"
      > </a
      ><a name="15146" href="Stlc.html#15096" class="Bound"
      >s</a
      ><a name="15147" class="Symbol"
      >)</a
      ><a name="15148"
      > </a
      ><a name="15149" href="Stlc.html#15098" class="Bound"
      >t</a
      ><a name="15150"
      > </a
      ><a name="15151" href="Stlc.html#15045" class="Datatype Operator"
      >==&gt;</a
      ><a name="15154"
      > </a
      ><a name="15155" href="Stlc.html#12129" class="Function Operator"
      >[</a
      ><a name="15156"
      > </a
      ><a name="15157" href="Stlc.html#15092" class="Bound"
      >x</a
      ><a name="15158"
      > </a
      ><a name="15159" href="Stlc.html#12129" class="Function Operator"
      >:=</a
      ><a name="15161"
      > </a
      ><a name="15162" href="Stlc.html#15098" class="Bound"
      >t</a
      ><a name="15163"
      > </a
      ><a name="15164" href="Stlc.html#12129" class="Function Operator"
      >]</a
      ><a name="15165"
      > </a
      ><a name="15166" href="Stlc.html#15096" class="Bound"
      >s</a
      ><a name="15167"
      >
  </a
      ><a name="15170" href="Stlc.html#15170" class="InductiveConstructor"
      >app1</a
      ><a name="15174"
      >    </a
      ><a name="15178" class="Symbol"
      >:</a
      ><a name="15179"
      > </a
      ><a name="15180" class="Symbol"
      >&#8704;</a
      ><a name="15181"
      > </a
      ><a name="15182" class="Symbol"
      >{</a
      ><a name="15183" href="Stlc.html#15183" class="Bound"
      >s</a
      ><a name="15184"
      > </a
      ><a name="15185" href="Stlc.html#15185" class="Bound"
      >s'</a
      ><a name="15187"
      > </a
      ><a name="15188" href="Stlc.html#15188" class="Bound"
      >t</a
      ><a name="15189" class="Symbol"
      >}</a
      ><a name="15190"
      >
          </a
      ><a name="15201" class="Symbol"
      >&#8594;</a
      ><a name="15202"
      > </a
      ><a name="15203" href="Stlc.html#15183" class="Bound"
      >s</a
      ><a name="15204"
      > </a
      ><a name="15205" href="Stlc.html#15045" class="Datatype Operator"
      >==&gt;</a
      ><a name="15208"
      > </a
      ><a name="15209" href="Stlc.html#15185" class="Bound"
      >s'</a
      ><a name="15211"
      >
          </a
      ><a name="15222" class="Symbol"
      >&#8594;</a
      ><a name="15223"
      > </a
      ><a name="15224" href="Stlc.html#5541" class="InductiveConstructor"
      >app</a
      ><a name="15227"
      > </a
      ><a name="15228" href="Stlc.html#15183" class="Bound"
      >s</a
      ><a name="15229"
      > </a
      ><a name="15230" href="Stlc.html#15188" class="Bound"
      >t</a
      ><a name="15231"
      > </a
      ><a name="15232" href="Stlc.html#15045" class="Datatype Operator"
      >==&gt;</a
      ><a name="15235"
      > </a
      ><a name="15236" href="Stlc.html#5541" class="InductiveConstructor"
      >app</a
      ><a name="15239"
      > </a
      ><a name="15240" href="Stlc.html#15185" class="Bound"
      >s'</a
      ><a name="15242"
      > </a
      ><a name="15243" href="Stlc.html#15188" class="Bound"
      >t</a
      ><a name="15244"
      >
  </a
      ><a name="15247" href="Stlc.html#15247" class="InductiveConstructor"
      >app2</a
      ><a name="15251"
      >    </a
      ><a name="15255" class="Symbol"
      >:</a
      ><a name="15256"
      > </a
      ><a name="15257" class="Symbol"
      >&#8704;</a
      ><a name="15258"
      > </a
      ><a name="15259" class="Symbol"
      >{</a
      ><a name="15260" href="Stlc.html#15260" class="Bound"
      >s</a
      ><a name="15261"
      > </a
      ><a name="15262" href="Stlc.html#15262" class="Bound"
      >t</a
      ><a name="15263"
      > </a
      ><a name="15264" href="Stlc.html#15264" class="Bound"
      >t'</a
      ><a name="15266" class="Symbol"
      >}</a
      ><a name="15267"
      >
          </a
      ><a name="15278" class="Symbol"
      >&#8594;</a
      ><a name="15279"
      > </a
      ><a name="15280" href="Stlc.html#8909" class="Datatype"
      >Value</a
      ><a name="15285"
      > </a
      ><a name="15286" href="Stlc.html#15260" class="Bound"
      >s</a
      ><a name="15287"
      >
          </a
      ><a name="15298" class="Symbol"
      >&#8594;</a
      ><a name="15299"
      > </a
      ><a name="15300" href="Stlc.html#15262" class="Bound"
      >t</a
      ><a name="15301"
      > </a
      ><a name="15302" href="Stlc.html#15045" class="Datatype Operator"
      >==&gt;</a
      ><a name="15305"
      > </a
      ><a name="15306" href="Stlc.html#15264" class="Bound"
      >t'</a
      ><a name="15308"
      >
          </a
      ><a name="15319" class="Symbol"
      >&#8594;</a
      ><a name="15320"
      > </a
      ><a name="15321" href="Stlc.html#5541" class="InductiveConstructor"
      >app</a
      ><a name="15324"
      > </a
      ><a name="15325" href="Stlc.html#15260" class="Bound"
      >s</a
      ><a name="15326"
      > </a
      ><a name="15327" href="Stlc.html#15262" class="Bound"
      >t</a
      ><a name="15328"
      > </a
      ><a name="15329" href="Stlc.html#15045" class="Datatype Operator"
      >==&gt;</a
      ><a name="15332"
      > </a
      ><a name="15333" href="Stlc.html#5541" class="InductiveConstructor"
      >app</a
      ><a name="15336"
      > </a
      ><a name="15337" href="Stlc.html#15260" class="Bound"
      >s</a
      ><a name="15338"
      > </a
      ><a name="15339" href="Stlc.html#15264" class="Bound"
      >t'</a
      ><a name="15341"
      >
  </a
      ><a name="15344" href="Stlc.html#15344" class="InductiveConstructor"
      >if</a
      ><a name="15346"
      >      </a
      ><a name="15352" class="Symbol"
      >:</a
      ><a name="15353"
      > </a
      ><a name="15354" class="Symbol"
      >&#8704;</a
      ><a name="15355"
      > </a
      ><a name="15356" class="Symbol"
      >{</a
      ><a name="15357" href="Stlc.html#15357" class="Bound"
      >s</a
      ><a name="15358"
      > </a
      ><a name="15359" href="Stlc.html#15359" class="Bound"
      >s'</a
      ><a name="15361"
      > </a
      ><a name="15362" href="Stlc.html#15362" class="Bound"
      >t</a
      ><a name="15363"
      > </a
      ><a name="15364" href="Stlc.html#15364" class="Bound"
      >u</a
      ><a name="15365" class="Symbol"
      >}</a
      ><a name="15366"
      >
          </a
      ><a name="15377" class="Symbol"
      >&#8594;</a
      ><a name="15378"
      > </a
      ><a name="15379" href="Stlc.html#15357" class="Bound"
      >s</a
      ><a name="15380"
      > </a
      ><a name="15381" href="Stlc.html#15045" class="Datatype Operator"
      >==&gt;</a
      ><a name="15384"
      > </a
      ><a name="15385" href="Stlc.html#15359" class="Bound"
      >s'</a
      ><a name="15387"
      >
          </a
      ><a name="15398" class="Symbol"
      >&#8594;</a
      ><a name="15399"
      > </a
      ><a name="15400" href="Stlc.html#5634" class="InductiveConstructor Operator"
      >if</a
      ><a name="15402"
      > </a
      ><a name="15403" href="Stlc.html#15357" class="Bound"
      >s</a
      ><a name="15404"
      > </a
      ><a name="15405" href="Stlc.html#5634" class="InductiveConstructor Operator"
      >then</a
      ><a name="15409"
      > </a
      ><a name="15410" href="Stlc.html#15362" class="Bound"
      >t</a
      ><a name="15411"
      > </a
      ><a name="15412" href="Stlc.html#5634" class="InductiveConstructor Operator"
      >else</a
      ><a name="15416"
      > </a
      ><a name="15417" href="Stlc.html#15364" class="Bound"
      >u</a
      ><a name="15418"
      > </a
      ><a name="15419" href="Stlc.html#15045" class="Datatype Operator"
      >==&gt;</a
      ><a name="15422"
      > </a
      ><a name="15423" href="Stlc.html#5634" class="InductiveConstructor Operator"
      >if</a
      ><a name="15425"
      > </a
      ><a name="15426" href="Stlc.html#15359" class="Bound"
      >s'</a
      ><a name="15428"
      > </a
      ><a name="15429" href="Stlc.html#5634" class="InductiveConstructor Operator"
      >then</a
      ><a name="15433"
      > </a
      ><a name="15434" href="Stlc.html#15362" class="Bound"
      >t</a
      ><a name="15435"
      > </a
      ><a name="15436" href="Stlc.html#5634" class="InductiveConstructor Operator"
      >else</a
      ><a name="15440"
      > </a
      ><a name="15441" href="Stlc.html#15364" class="Bound"
      >u</a
      ><a name="15442"
      >
  </a
      ><a name="15445" href="Stlc.html#15445" class="InductiveConstructor"
      >iftrue</a
      ><a name="15451"
      >  </a
      ><a name="15453" class="Symbol"
      >:</a
      ><a name="15454"
      > </a
      ><a name="15455" class="Symbol"
      >&#8704;</a
      ><a name="15456"
      > </a
      ><a name="15457" class="Symbol"
      >{</a
      ><a name="15458" href="Stlc.html#15458" class="Bound"
      >s</a
      ><a name="15459"
      > </a
      ><a name="15460" href="Stlc.html#15460" class="Bound"
      >t</a
      ><a name="15461" class="Symbol"
      >}</a
      ><a name="15462"
      >
          </a
      ><a name="15473" class="Symbol"
      >&#8594;</a
      ><a name="15474"
      > </a
      ><a name="15475" href="Stlc.html#5634" class="InductiveConstructor Operator"
      >if</a
      ><a name="15477"
      > </a
      ><a name="15478" href="Stlc.html#5604" class="InductiveConstructor"
      >true</a
      ><a name="15482"
      > </a
      ><a name="15483" href="Stlc.html#5634" class="InductiveConstructor Operator"
      >then</a
      ><a name="15487"
      > </a
      ><a name="15488" href="Stlc.html#15458" class="Bound"
      >s</a
      ><a name="15489"
      > </a
      ><a name="15490" href="Stlc.html#5634" class="InductiveConstructor Operator"
      >else</a
      ><a name="15494"
      > </a
      ><a name="15495" href="Stlc.html#15460" class="Bound"
      >t</a
      ><a name="15496"
      > </a
      ><a name="15497" href="Stlc.html#15045" class="Datatype Operator"
      >==&gt;</a
      ><a name="15500"
      > </a
      ><a name="15501" href="Stlc.html#15458" class="Bound"
      >s</a
      ><a name="15502"
      >
  </a
      ><a name="15505" href="Stlc.html#15505" class="InductiveConstructor"
      >iffalse</a
      ><a name="15512"
      > </a
      ><a name="15513" class="Symbol"
      >:</a
      ><a name="15514"
      > </a
      ><a name="15515" class="Symbol"
      >&#8704;</a
      ><a name="15516"
      > </a
      ><a name="15517" class="Symbol"
      >{</a
      ><a name="15518" href="Stlc.html#15518" class="Bound"
      >s</a
      ><a name="15519"
      > </a
      ><a name="15520" href="Stlc.html#15520" class="Bound"
      >t</a
      ><a name="15521" class="Symbol"
      >}</a
      ><a name="15522"
      >
          </a
      ><a name="15533" class="Symbol"
      >&#8594;</a
      ><a name="15534"
      > </a
      ><a name="15535" href="Stlc.html#5634" class="InductiveConstructor Operator"
      >if</a
      ><a name="15537"
      > </a
      ><a name="15538" href="Stlc.html#5619" class="InductiveConstructor"
      >false</a
      ><a name="15543"
      > </a
      ><a name="15544" href="Stlc.html#5634" class="InductiveConstructor Operator"
      >then</a
      ><a name="15548"
      > </a
      ><a name="15549" href="Stlc.html#15518" class="Bound"
      >s</a
      ><a name="15550"
      > </a
      ><a name="15551" href="Stlc.html#5634" class="InductiveConstructor Operator"
      >else</a
      ><a name="15555"
      > </a
      ><a name="15556" href="Stlc.html#15520" class="Bound"
      >t</a
      ><a name="15557"
      > </a
      ><a name="15558" href="Stlc.html#15045" class="Datatype Operator"
      >==&gt;</a
      ><a name="15561"
      > </a
      ><a name="15562" href="Stlc.html#15520" class="Bound"
      >t</a
      >
{% endraw %}</pre>

<div class="hidden">
<pre class="Agda">{% raw %}
<a name="15610" class="Keyword"
      >infix</a
      ><a name="15615"
      > </a
      ><a name="15616" class="Number"
      >1</a
      ><a name="15617"
      > </a
      ><a name="15618" href="Stlc.html#15045" class="Datatype Operator"
      >_==&gt;_</a
      >
{% endraw %}</pre>
</div>

<pre class="Agda">{% raw %}
<a name="15656" class="Keyword"
      >data</a
      ><a name="15660"
      > </a
      ><a name="15661" href="Stlc.html#15661" class="Datatype"
      >Multi</a
      ><a name="15666"
      > </a
      ><a name="15667" class="Symbol"
      >(</a
      ><a name="15668" href="Stlc.html#15668" class="Bound"
      >R</a
      ><a name="15669"
      > </a
      ><a name="15670" class="Symbol"
      >:</a
      ><a name="15671"
      > </a
      ><a name="15672" href="Stlc.html#5502" class="Datatype"
      >Term</a
      ><a name="15676"
      > </a
      ><a name="15677" class="Symbol"
      >&#8594;</a
      ><a name="15678"
      > </a
      ><a name="15679" href="Stlc.html#5502" class="Datatype"
      >Term</a
      ><a name="15683"
      > </a
      ><a name="15684" class="Symbol"
      >&#8594;</a
      ><a name="15685"
      > </a
      ><a name="15686" class="PrimitiveType"
      >Set</a
      ><a name="15689" class="Symbol"
      >)</a
      ><a name="15690"
      > </a
      ><a name="15691" class="Symbol"
      >:</a
      ><a name="15692"
      > </a
      ><a name="15693" href="Stlc.html#5502" class="Datatype"
      >Term</a
      ><a name="15697"
      > </a
      ><a name="15698" class="Symbol"
      >&#8594;</a
      ><a name="15699"
      > </a
      ><a name="15700" href="Stlc.html#5502" class="Datatype"
      >Term</a
      ><a name="15704"
      > </a
      ><a name="15705" class="Symbol"
      >&#8594;</a
      ><a name="15706"
      > </a
      ><a name="15707" class="PrimitiveType"
      >Set</a
      ><a name="15710"
      > </a
      ><a name="15711" class="Keyword"
      >where</a
      ><a name="15716"
      >
  </a
      ><a name="15719" href="Stlc.html#15719" class="InductiveConstructor"
      >refl</a
      ><a name="15723"
      > </a
      ><a name="15724" class="Symbol"
      >:</a
      ><a name="15725"
      > </a
      ><a name="15726" class="Symbol"
      >&#8704;</a
      ><a name="15727"
      > </a
      ><a name="15728" class="Symbol"
      >{</a
      ><a name="15729" href="Stlc.html#15729" class="Bound"
      >x</a
      ><a name="15730" class="Symbol"
      >}</a
      ><a name="15731"
      > </a
      ><a name="15732" class="Symbol"
      >-&gt;</a
      ><a name="15734"
      > </a
      ><a name="15735" href="Stlc.html#15661" class="Datatype"
      >Multi</a
      ><a name="15740"
      > </a
      ><a name="15741" href="Stlc.html#15668" class="Bound"
      >R</a
      ><a name="15742"
      > </a
      ><a name="15743" href="Stlc.html#15729" class="Bound"
      >x</a
      ><a name="15744"
      > </a
      ><a name="15745" href="Stlc.html#15729" class="Bound"
      >x</a
      ><a name="15746"
      >
  </a
      ><a name="15749" href="Stlc.html#15749" class="InductiveConstructor"
      >step</a
      ><a name="15753"
      > </a
      ><a name="15754" class="Symbol"
      >:</a
      ><a name="15755"
      > </a
      ><a name="15756" class="Symbol"
      >&#8704;</a
      ><a name="15757"
      > </a
      ><a name="15758" class="Symbol"
      >{</a
      ><a name="15759" href="Stlc.html#15759" class="Bound"
      >x</a
      ><a name="15760"
      > </a
      ><a name="15761" href="Stlc.html#15761" class="Bound"
      >y</a
      ><a name="15762"
      > </a
      ><a name="15763" href="Stlc.html#15763" class="Bound"
      >z</a
      ><a name="15764" class="Symbol"
      >}</a
      ><a name="15765"
      > </a
      ><a name="15766" class="Symbol"
      >-&gt;</a
      ><a name="15768"
      > </a
      ><a name="15769" href="Stlc.html#15668" class="Bound"
      >R</a
      ><a name="15770"
      > </a
      ><a name="15771" href="Stlc.html#15759" class="Bound"
      >x</a
      ><a name="15772"
      > </a
      ><a name="15773" href="Stlc.html#15761" class="Bound"
      >y</a
      ><a name="15774"
      > </a
      ><a name="15775" class="Symbol"
      >-&gt;</a
      ><a name="15777"
      > </a
      ><a name="15778" href="Stlc.html#15661" class="Datatype"
      >Multi</a
      ><a name="15783"
      > </a
      ><a name="15784" href="Stlc.html#15668" class="Bound"
      >R</a
      ><a name="15785"
      > </a
      ><a name="15786" href="Stlc.html#15761" class="Bound"
      >y</a
      ><a name="15787"
      > </a
      ><a name="15788" href="Stlc.html#15763" class="Bound"
      >z</a
      ><a name="15789"
      > </a
      ><a name="15790" class="Symbol"
      >-&gt;</a
      ><a name="15792"
      > </a
      ><a name="15793" href="Stlc.html#15661" class="Datatype"
      >Multi</a
      ><a name="15798"
      > </a
      ><a name="15799" href="Stlc.html#15668" class="Bound"
      >R</a
      ><a name="15800"
      > </a
      ><a name="15801" href="Stlc.html#15759" class="Bound"
      >x</a
      ><a name="15802"
      > </a
      ><a name="15803" href="Stlc.html#15763" class="Bound"
      >z</a
      >
{% endraw %}</pre>

<pre class="Agda">{% raw %}
<a name="15830" href="Stlc.html#15830" class="Function Operator"
      >_==&gt;*_</a
      ><a name="15836"
      > </a
      ><a name="15837" class="Symbol"
      >:</a
      ><a name="15838"
      > </a
      ><a name="15839" href="Stlc.html#5502" class="Datatype"
      >Term</a
      ><a name="15843"
      > </a
      ><a name="15844" class="Symbol"
      >&#8594;</a
      ><a name="15845"
      > </a
      ><a name="15846" href="Stlc.html#5502" class="Datatype"
      >Term</a
      ><a name="15850"
      > </a
      ><a name="15851" class="Symbol"
      >&#8594;</a
      ><a name="15852"
      > </a
      ><a name="15853" class="PrimitiveType"
      >Set</a
      ><a name="15856"
      >
</a
      ><a name="15857" href="Stlc.html#15830" class="Function Operator"
      >_==&gt;*_</a
      ><a name="15863"
      > </a
      ><a name="15864" class="Symbol"
      >=</a
      ><a name="15865"
      > </a
      ><a name="15866" href="Stlc.html#15661" class="Datatype"
      >Multi</a
      ><a name="15871"
      > </a
      ><a name="15872" href="Stlc.html#15045" class="Datatype Operator"
      >_==&gt;_</a
      >
{% endraw %}</pre>

<div class="hidden">
<pre class="Agda">{% raw %}
<a name="15924" class="Symbol"
      >{-#</a
      ><a name="15927"
      > </a
      ><a name="15928" class="Keyword"
      >DISPLAY</a
      ><a name="15935"
      > </a
      ><a name="15936" href="Stlc.html#15661" class="Datatype"
      >Multi</a
      ><a name="15941"
      > </a
      ><a name="15942" href="Stlc.html#15942" class="Bound Operator"
      >_==&gt;_</a
      ><a name="15947"
      > = </a
      ><a name="15950" href="Stlc.html#15830" class="Function Operator"
      >_==&gt;*_</a
      ><a name="15956"
      > </a
      ><a name="15957" class="Symbol"
      >#-}</a
      >
{% endraw %}</pre>
</div>

### Examples

Example:

$$((\lambda x:bool\rightarrow bool. x) (\lambda x:bool. x)) \Longrightarrow^* (\lambda x:bool. x)$$.

<pre class="Agda">{% raw %}
<a name="16119" href="Stlc.html#16119" class="Function"
      >step-example1</a
      ><a name="16132"
      > </a
      ><a name="16133" class="Symbol"
      >:</a
      ><a name="16134"
      > </a
      ><a name="16135" class="Symbol"
      >(</a
      ><a name="16136" href="Stlc.html#5541" class="InductiveConstructor"
      >app</a
      ><a name="16139"
      > </a
      ><a name="16140" href="Stlc.html#6519" class="Function"
      >idBB</a
      ><a name="16144"
      > </a
      ><a name="16145" href="Stlc.html#6413" class="Function"
      >idB</a
      ><a name="16148" class="Symbol"
      >)</a
      ><a name="16149"
      > </a
      ><a name="16150" href="Stlc.html#15830" class="Function Operator"
      >==&gt;*</a
      ><a name="16154"
      > </a
      ><a name="16155" href="Stlc.html#6413" class="Function"
      >idB</a
      ><a name="16158"
      >
</a
      ><a name="16159" href="Stlc.html#16119" class="Function"
      >step-example1</a
      ><a name="16172"
      > </a
      ><a name="16173" class="Symbol"
      >=</a
      ><a name="16174"
      > </a
      ><a name="16175" href="Stlc.html#15749" class="InductiveConstructor"
      >step</a
      ><a name="16179"
      > </a
      ><a name="16180" class="Symbol"
      >(</a
      ><a name="16181" href="Stlc.html#15079" class="InductiveConstructor"
      >red</a
      ><a name="16184"
      > </a
      ><a name="16185" href="Stlc.html#8936" class="InductiveConstructor"
      >abs</a
      ><a name="16188" class="Symbol"
      >)</a
      ><a name="16189"
      >
              </a
      ><a name="16204" href="https://agda.github.io/agda-stdlib/Function.html#1835" class="Function Operator"
      >$</a
      ><a name="16205"
      > </a
      ><a name="16206" href="Stlc.html#15719" class="InductiveConstructor"
      >refl</a
      >
{% endraw %}</pre>

Example:

$$(\lambda x:bool\rightarrow bool. x) \;((\lambda x:bool\rightarrow bool. x)\;(\lambda x:bool. x))) \Longrightarrow^* (\lambda x:bool. x)$$.

<pre class="Agda">{% raw %}
<a name="16388" href="Stlc.html#16388" class="Function"
      >step-example2</a
      ><a name="16401"
      > </a
      ><a name="16402" class="Symbol"
      >:</a
      ><a name="16403"
      > </a
      ><a name="16404" class="Symbol"
      >(</a
      ><a name="16405" href="Stlc.html#5541" class="InductiveConstructor"
      >app</a
      ><a name="16408"
      > </a
      ><a name="16409" href="Stlc.html#6519" class="Function"
      >idBB</a
      ><a name="16413"
      > </a
      ><a name="16414" class="Symbol"
      >(</a
      ><a name="16415" href="Stlc.html#5541" class="InductiveConstructor"
      >app</a
      ><a name="16418"
      > </a
      ><a name="16419" href="Stlc.html#6519" class="Function"
      >idBB</a
      ><a name="16423"
      > </a
      ><a name="16424" href="Stlc.html#6413" class="Function"
      >idB</a
      ><a name="16427" class="Symbol"
      >))</a
      ><a name="16429"
      > </a
      ><a name="16430" href="Stlc.html#15830" class="Function Operator"
      >==&gt;*</a
      ><a name="16434"
      > </a
      ><a name="16435" href="Stlc.html#6413" class="Function"
      >idB</a
      ><a name="16438"
      >
</a
      ><a name="16439" href="Stlc.html#16388" class="Function"
      >step-example2</a
      ><a name="16452"
      > </a
      ><a name="16453" class="Symbol"
      >=</a
      ><a name="16454"
      > </a
      ><a name="16455" href="Stlc.html#15749" class="InductiveConstructor"
      >step</a
      ><a name="16459"
      > </a
      ><a name="16460" class="Symbol"
      >(</a
      ><a name="16461" href="Stlc.html#15247" class="InductiveConstructor"
      >app2</a
      ><a name="16465"
      > </a
      ><a name="16466" href="Stlc.html#8936" class="InductiveConstructor"
      >abs</a
      ><a name="16469"
      > </a
      ><a name="16470" class="Symbol"
      >(</a
      ><a name="16471" href="Stlc.html#15079" class="InductiveConstructor"
      >red</a
      ><a name="16474"
      > </a
      ><a name="16475" href="Stlc.html#8936" class="InductiveConstructor"
      >abs</a
      ><a name="16478" class="Symbol"
      >))</a
      ><a name="16480"
      >
              </a
      ><a name="16495" href="https://agda.github.io/agda-stdlib/Function.html#1835" class="Function Operator"
      >$</a
      ><a name="16496"
      > </a
      ><a name="16497" href="Stlc.html#15749" class="InductiveConstructor"
      >step</a
      ><a name="16501"
      > </a
      ><a name="16502" class="Symbol"
      >(</a
      ><a name="16503" href="Stlc.html#15079" class="InductiveConstructor"
      >red</a
      ><a name="16506"
      > </a
      ><a name="16507" href="Stlc.html#8936" class="InductiveConstructor"
      >abs</a
      ><a name="16510" class="Symbol"
      >)</a
      ><a name="16511"
      >
              </a
      ><a name="16526" href="https://agda.github.io/agda-stdlib/Function.html#1835" class="Function Operator"
      >$</a
      ><a name="16527"
      > </a
      ><a name="16528" href="Stlc.html#15719" class="InductiveConstructor"
      >refl</a
      >
{% endraw %}</pre>

Example:

$$((\lambda x:bool\rightarrow bool. x)\;(\lambda x:bool. \text{if }x\text{ then }false\text{ else }true))\;true\Longrightarrow^* false$$.

<pre class="Agda">{% raw %}
<a name="16707" href="Stlc.html#16707" class="Function"
      >step-example3</a
      ><a name="16720"
      > </a
      ><a name="16721" class="Symbol"
      >:</a
      ><a name="16722"
      > </a
      ><a name="16723" class="Symbol"
      >(</a
      ><a name="16724" href="Stlc.html#5541" class="InductiveConstructor"
      >app</a
      ><a name="16727"
      > </a
      ><a name="16728" class="Symbol"
      >(</a
      ><a name="16729" href="Stlc.html#5541" class="InductiveConstructor"
      >app</a
      ><a name="16732"
      > </a
      ><a name="16733" href="Stlc.html#6519" class="Function"
      >idBB</a
      ><a name="16737"
      > </a
      ><a name="16738" href="Stlc.html#6952" class="Function"
      >notB</a
      ><a name="16742" class="Symbol"
      >)</a
      ><a name="16743"
      > </a
      ><a name="16744" href="Stlc.html#5604" class="InductiveConstructor"
      >true</a
      ><a name="16748" class="Symbol"
      >)</a
      ><a name="16749"
      > </a
      ><a name="16750" href="Stlc.html#15830" class="Function Operator"
      >==&gt;*</a
      ><a name="16754"
      > </a
      ><a name="16755" href="Stlc.html#5619" class="InductiveConstructor"
      >false</a
      ><a name="16760"
      >
</a
      ><a name="16761" href="Stlc.html#16707" class="Function"
      >step-example3</a
      ><a name="16774"
      > </a
      ><a name="16775" class="Symbol"
      >=</a
      ><a name="16776"
      > </a
      ><a name="16777" href="Stlc.html#15749" class="InductiveConstructor"
      >step</a
      ><a name="16781"
      > </a
      ><a name="16782" class="Symbol"
      >(</a
      ><a name="16783" href="Stlc.html#15170" class="InductiveConstructor"
      >app1</a
      ><a name="16787"
      > </a
      ><a name="16788" class="Symbol"
      >(</a
      ><a name="16789" href="Stlc.html#15079" class="InductiveConstructor"
      >red</a
      ><a name="16792"
      > </a
      ><a name="16793" href="Stlc.html#8936" class="InductiveConstructor"
      >abs</a
      ><a name="16796" class="Symbol"
      >))</a
      ><a name="16798"
      >
              </a
      ><a name="16813" href="https://agda.github.io/agda-stdlib/Function.html#1835" class="Function Operator"
      >$</a
      ><a name="16814"
      > </a
      ><a name="16815" href="Stlc.html#15749" class="InductiveConstructor"
      >step</a
      ><a name="16819"
      > </a
      ><a name="16820" class="Symbol"
      >(</a
      ><a name="16821" href="Stlc.html#15079" class="InductiveConstructor"
      >red</a
      ><a name="16824"
      > </a
      ><a name="16825" href="Stlc.html#8984" class="InductiveConstructor"
      >true</a
      ><a name="16829" class="Symbol"
      >)</a
      ><a name="16830"
      >
              </a
      ><a name="16845" href="https://agda.github.io/agda-stdlib/Function.html#1835" class="Function Operator"
      >$</a
      ><a name="16846"
      > </a
      ><a name="16847" href="Stlc.html#15749" class="InductiveConstructor"
      >step</a
      ><a name="16851"
      > </a
      ><a name="16852" href="Stlc.html#15445" class="InductiveConstructor"
      >iftrue</a
      ><a name="16858"
      >
              </a
      ><a name="16873" href="https://agda.github.io/agda-stdlib/Function.html#1835" class="Function Operator"
      >$</a
      ><a name="16874"
      > </a
      ><a name="16875" href="Stlc.html#15719" class="InductiveConstructor"
      >refl</a
      >
{% endraw %}</pre>

Example:

$$((\lambda x:bool\rightarrow bool. x)\;((\lambda x:bool. \text{if }x\text{ then }false\text{ else }true)\;true))\Longrightarrow^* false$$.

<pre class="Agda">{% raw %}
<a name="17056" href="Stlc.html#17056" class="Function"
      >step-example4</a
      ><a name="17069"
      > </a
      ><a name="17070" class="Symbol"
      >:</a
      ><a name="17071"
      > </a
      ><a name="17072" class="Symbol"
      >(</a
      ><a name="17073" href="Stlc.html#5541" class="InductiveConstructor"
      >app</a
      ><a name="17076"
      > </a
      ><a name="17077" href="Stlc.html#6519" class="Function"
      >idBB</a
      ><a name="17081"
      > </a
      ><a name="17082" class="Symbol"
      >(</a
      ><a name="17083" href="Stlc.html#5541" class="InductiveConstructor"
      >app</a
      ><a name="17086"
      > </a
      ><a name="17087" href="Stlc.html#6952" class="Function"
      >notB</a
      ><a name="17091"
      > </a
      ><a name="17092" href="Stlc.html#5604" class="InductiveConstructor"
      >true</a
      ><a name="17096" class="Symbol"
      >))</a
      ><a name="17098"
      > </a
      ><a name="17099" href="Stlc.html#15830" class="Function Operator"
      >==&gt;*</a
      ><a name="17103"
      > </a
      ><a name="17104" href="Stlc.html#5619" class="InductiveConstructor"
      >false</a
      ><a name="17109"
      >
</a
      ><a name="17110" href="Stlc.html#17056" class="Function"
      >step-example4</a
      ><a name="17123"
      > </a
      ><a name="17124" class="Symbol"
      >=</a
      ><a name="17125"
      > </a
      ><a name="17126" href="Stlc.html#15749" class="InductiveConstructor"
      >step</a
      ><a name="17130"
      > </a
      ><a name="17131" class="Symbol"
      >(</a
      ><a name="17132" href="Stlc.html#15247" class="InductiveConstructor"
      >app2</a
      ><a name="17136"
      > </a
      ><a name="17137" href="Stlc.html#8936" class="InductiveConstructor"
      >abs</a
      ><a name="17140"
      > </a
      ><a name="17141" class="Symbol"
      >(</a
      ><a name="17142" href="Stlc.html#15079" class="InductiveConstructor"
      >red</a
      ><a name="17145"
      > </a
      ><a name="17146" href="Stlc.html#8984" class="InductiveConstructor"
      >true</a
      ><a name="17150" class="Symbol"
      >))</a
      ><a name="17152"
      >
              </a
      ><a name="17167" href="https://agda.github.io/agda-stdlib/Function.html#1835" class="Function Operator"
      >$</a
      ><a name="17168"
      > </a
      ><a name="17169" href="Stlc.html#15749" class="InductiveConstructor"
      >step</a
      ><a name="17173"
      > </a
      ><a name="17174" class="Symbol"
      >(</a
      ><a name="17175" href="Stlc.html#15247" class="InductiveConstructor"
      >app2</a
      ><a name="17179"
      > </a
      ><a name="17180" href="Stlc.html#8936" class="InductiveConstructor"
      >abs</a
      ><a name="17183"
      > </a
      ><a name="17184" href="Stlc.html#15445" class="InductiveConstructor"
      >iftrue</a
      ><a name="17190" class="Symbol"
      >)</a
      ><a name="17191"
      >
              </a
      ><a name="17206" href="https://agda.github.io/agda-stdlib/Function.html#1835" class="Function Operator"
      >$</a
      ><a name="17207"
      > </a
      ><a name="17208" href="Stlc.html#15749" class="InductiveConstructor"
      >step</a
      ><a name="17212"
      > </a
      ><a name="17213" class="Symbol"
      >(</a
      ><a name="17214" href="Stlc.html#15079" class="InductiveConstructor"
      >red</a
      ><a name="17217"
      > </a
      ><a name="17218" href="Stlc.html#9005" class="InductiveConstructor"
      >false</a
      ><a name="17223" class="Symbol"
      >)</a
      ><a name="17224"
      >
              </a
      ><a name="17239" href="https://agda.github.io/agda-stdlib/Function.html#1835" class="Function Operator"
      >$</a
      ><a name="17240"
      > </a
      ><a name="17241" href="Stlc.html#15719" class="InductiveConstructor"
      >refl</a
      >
{% endraw %}</pre>

#### Exercise: 2 stars (step-example5)

<pre class="Agda">{% raw %}
<a name="17311" class="Keyword"
      >postulate</a
      ><a name="17320"
      >
  </a
      ><a name="17323" href="Stlc.html#17323" class="Postulate"
      >step-example5</a
      ><a name="17336"
      > </a
      ><a name="17337" class="Symbol"
      >:</a
      ><a name="17338"
      > </a
      ><a name="17339" class="Symbol"
      >(</a
      ><a name="17340" href="Stlc.html#5541" class="InductiveConstructor"
      >app</a
      ><a name="17343"
      > </a
      ><a name="17344" class="Symbol"
      >(</a
      ><a name="17345" href="Stlc.html#5541" class="InductiveConstructor"
      >app</a
      ><a name="17348"
      > </a
      ><a name="17349" href="Stlc.html#6673" class="Function"
      >idBBBB</a
      ><a name="17355"
      > </a
      ><a name="17356" href="Stlc.html#6519" class="Function"
      >idBB</a
      ><a name="17360" class="Symbol"
      >)</a
      ><a name="17361"
      > </a
      ><a name="17362" href="Stlc.html#6413" class="Function"
      >idB</a
      ><a name="17365" class="Symbol"
      >)</a
      ><a name="17366"
      > </a
      ><a name="17367" href="Stlc.html#15830" class="Function Operator"
      >==&gt;*</a
      ><a name="17371"
      > </a
      ><a name="17372" href="Stlc.html#6413" class="Function"
      >idB</a
      >
{% endraw %}</pre>

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

<pre class="Agda">{% raw %}
<a name="18092" href="Stlc.html#18092" class="Function"
      >Ctxt</a
      ><a name="18096"
      > </a
      ><a name="18097" class="Symbol"
      >:</a
      ><a name="18098"
      > </a
      ><a name="18099" class="PrimitiveType"
      >Set</a
      ><a name="18102"
      >
</a
      ><a name="18103" href="Stlc.html#18092" class="Function"
      >Ctxt</a
      ><a name="18107"
      > </a
      ><a name="18108" class="Symbol"
      >=</a
      ><a name="18109"
      > </a
      ><a name="18110" href="Maps.html#9409" class="Function"
      >PartialMap</a
      ><a name="18120"
      > </a
      ><a name="18121" href="Stlc.html#5387" class="Datatype"
      >Type</a
      ><a name="18125"
      >

</a
      ><a name="18127" href="Stlc.html#18127" class="Function"
      >&#8709;</a
      ><a name="18128"
      > </a
      ><a name="18129" class="Symbol"
      >:</a
      ><a name="18130"
      > </a
      ><a name="18131" href="Stlc.html#18092" class="Function"
      >Ctxt</a
      ><a name="18135"
      >
</a
      ><a name="18136" href="Stlc.html#18127" class="Function"
      >&#8709;</a
      ><a name="18137"
      > </a
      ><a name="18138" class="Symbol"
      >=</a
      ><a name="18139"
      > </a
      ><a name="18140" href="Maps.html#9542" class="Function"
      >PartialMap.empty</a
      ><a name="18156"
      >

</a
      ><a name="18158" href="Stlc.html#18158" class="Function Operator"
      >_,_&#8758;_</a
      ><a name="18163"
      > </a
      ><a name="18164" class="Symbol"
      >:</a
      ><a name="18165"
      > </a
      ><a name="18166" href="Stlc.html#18092" class="Function"
      >Ctxt</a
      ><a name="18170"
      > </a
      ><a name="18171" class="Symbol"
      >-&gt;</a
      ><a name="18173"
      > </a
      ><a name="18174" href="Maps.html#2290" class="Datatype"
      >Id</a
      ><a name="18176"
      > </a
      ><a name="18177" class="Symbol"
      >-&gt;</a
      ><a name="18179"
      > </a
      ><a name="18180" href="Stlc.html#5387" class="Datatype"
      >Type</a
      ><a name="18184"
      > </a
      ><a name="18185" class="Symbol"
      >-&gt;</a
      ><a name="18187"
      > </a
      ><a name="18188" href="Stlc.html#18092" class="Function"
      >Ctxt</a
      ><a name="18192"
      >
</a
      ><a name="18193" href="Stlc.html#18158" class="Function Operator"
      >_,_&#8758;_</a
      ><a name="18198"
      > </a
      ><a name="18199" class="Symbol"
      >=</a
      ><a name="18200"
      > </a
      ><a name="18201" href="Maps.html#9631" class="Function"
      >PartialMap.update</a
      >
{% endraw %}</pre>

<div class="hidden">
<pre class="Agda">{% raw %}
<a name="18265" class="Keyword"
      >infixl</a
      ><a name="18271"
      > </a
      ><a name="18272" class="Number"
      >3</a
      ><a name="18273"
      > </a
      ><a name="18274" href="Stlc.html#18158" class="Function Operator"
      >_,_&#8758;_</a
      >
{% endraw %}</pre>
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

<pre class="Agda">{% raw %}
<a name="19054" class="Keyword"
      >data</a
      ><a name="19058"
      > </a
      ><a name="19059" href="Stlc.html#19059" class="Datatype Operator"
      >_&#8866;_&#8758;_</a
      ><a name="19064"
      > </a
      ><a name="19065" class="Symbol"
      >:</a
      ><a name="19066"
      > </a
      ><a name="19067" href="Stlc.html#18092" class="Function"
      >Ctxt</a
      ><a name="19071"
      > </a
      ><a name="19072" class="Symbol"
      >-&gt;</a
      ><a name="19074"
      > </a
      ><a name="19075" href="Stlc.html#5502" class="Datatype"
      >Term</a
      ><a name="19079"
      > </a
      ><a name="19080" class="Symbol"
      >-&gt;</a
      ><a name="19082"
      > </a
      ><a name="19083" href="Stlc.html#5387" class="Datatype"
      >Type</a
      ><a name="19087"
      > </a
      ><a name="19088" class="Symbol"
      >-&gt;</a
      ><a name="19090"
      > </a
      ><a name="19091" class="PrimitiveType"
      >Set</a
      ><a name="19094"
      > </a
      ><a name="19095" class="Keyword"
      >where</a
      ><a name="19100"
      >
  </a
      ><a name="19103" href="Stlc.html#19103" class="InductiveConstructor"
      >var</a
      ><a name="19106"
      >           </a
      ><a name="19117" class="Symbol"
      >:</a
      ><a name="19118"
      > </a
      ><a name="19119" class="Symbol"
      >&#8704;</a
      ><a name="19120"
      > </a
      ><a name="19121" class="Symbol"
      >{</a
      ><a name="19122" href="Stlc.html#19122" class="Bound"
      >&#915;</a
      ><a name="19123" class="Symbol"
      >}</a
      ><a name="19124"
      > </a
      ><a name="19125" href="Stlc.html#19125" class="Bound"
      >x</a
      ><a name="19126"
      > </a
      ><a name="19127" class="Symbol"
      >{</a
      ><a name="19128" href="Stlc.html#19128" class="Bound"
      >A</a
      ><a name="19129" class="Symbol"
      >}</a
      ><a name="19130"
      >
                </a
      ><a name="19147" class="Symbol"
      >&#8594;</a
      ><a name="19148"
      > </a
      ><a name="19149" href="Stlc.html#19122" class="Bound"
      >&#915;</a
      ><a name="19150"
      > </a
      ><a name="19151" href="Stlc.html#19125" class="Bound"
      >x</a
      ><a name="19152"
      > </a
      ><a name="19153" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="19154"
      > </a
      ><a name="19155" href="https://agda.github.io/agda-stdlib/Data.Maybe.Base.html#373" class="InductiveConstructor"
      >just</a
      ><a name="19159"
      > </a
      ><a name="19160" href="Stlc.html#19128" class="Bound"
      >A</a
      ><a name="19161"
      >
                </a
      ><a name="19178" class="Symbol"
      >&#8594;</a
      ><a name="19179"
      > </a
      ><a name="19180" href="Stlc.html#19122" class="Bound"
      >&#915;</a
      ><a name="19181"
      > </a
      ><a name="19182" href="Stlc.html#19059" class="Datatype Operator"
      >&#8866;</a
      ><a name="19183"
      > </a
      ><a name="19184" href="Stlc.html#5521" class="InductiveConstructor"
      >var</a
      ><a name="19187"
      > </a
      ><a name="19188" href="Stlc.html#19125" class="Bound"
      >x</a
      ><a name="19189"
      > </a
      ><a name="19190" href="Stlc.html#19059" class="Datatype Operator"
      >&#8758;</a
      ><a name="19191"
      > </a
      ><a name="19192" href="Stlc.html#19128" class="Bound"
      >A</a
      ><a name="19193"
      >
  </a
      ><a name="19196" href="Stlc.html#19196" class="InductiveConstructor"
      >abs</a
      ><a name="19199"
      >           </a
      ><a name="19210" class="Symbol"
      >:</a
      ><a name="19211"
      > </a
      ><a name="19212" class="Symbol"
      >&#8704;</a
      ><a name="19213"
      > </a
      ><a name="19214" class="Symbol"
      >{</a
      ><a name="19215" href="Stlc.html#19215" class="Bound"
      >&#915;</a
      ><a name="19216" class="Symbol"
      >}</a
      ><a name="19217"
      > </a
      ><a name="19218" class="Symbol"
      >{</a
      ><a name="19219" href="Stlc.html#19219" class="Bound"
      >x</a
      ><a name="19220" class="Symbol"
      >}</a
      ><a name="19221"
      > </a
      ><a name="19222" class="Symbol"
      >{</a
      ><a name="19223" href="Stlc.html#19223" class="Bound"
      >A</a
      ><a name="19224" class="Symbol"
      >}</a
      ><a name="19225"
      > </a
      ><a name="19226" class="Symbol"
      >{</a
      ><a name="19227" href="Stlc.html#19227" class="Bound"
      >B</a
      ><a name="19228" class="Symbol"
      >}</a
      ><a name="19229"
      > </a
      ><a name="19230" class="Symbol"
      >{</a
      ><a name="19231" href="Stlc.html#19231" class="Bound"
      >s</a
      ><a name="19232" class="Symbol"
      >}</a
      ><a name="19233"
      >
                </a
      ><a name="19250" class="Symbol"
      >&#8594;</a
      ><a name="19251"
      > </a
      ><a name="19252" href="Stlc.html#19215" class="Bound"
      >&#915;</a
      ><a name="19253"
      > </a
      ><a name="19254" href="Stlc.html#18158" class="Function Operator"
      >,</a
      ><a name="19255"
      > </a
      ><a name="19256" href="Stlc.html#19219" class="Bound"
      >x</a
      ><a name="19257"
      > </a
      ><a name="19258" href="Stlc.html#18158" class="Function Operator"
      >&#8758;</a
      ><a name="19259"
      > </a
      ><a name="19260" href="Stlc.html#19223" class="Bound"
      >A</a
      ><a name="19261"
      > </a
      ><a name="19262" href="Stlc.html#19059" class="Datatype Operator"
      >&#8866;</a
      ><a name="19263"
      > </a
      ><a name="19264" href="Stlc.html#19231" class="Bound"
      >s</a
      ><a name="19265"
      > </a
      ><a name="19266" href="Stlc.html#19059" class="Datatype Operator"
      >&#8758;</a
      ><a name="19267"
      > </a
      ><a name="19268" href="Stlc.html#19227" class="Bound"
      >B</a
      ><a name="19269"
      >
                </a
      ><a name="19286" class="Symbol"
      >&#8594;</a
      ><a name="19287"
      > </a
      ><a name="19288" href="Stlc.html#19215" class="Bound"
      >&#915;</a
      ><a name="19289"
      > </a
      ><a name="19290" href="Stlc.html#19059" class="Datatype Operator"
      >&#8866;</a
      ><a name="19291"
      > </a
      ><a name="19292" href="Stlc.html#5570" class="InductiveConstructor"
      >abs</a
      ><a name="19295"
      > </a
      ><a name="19296" href="Stlc.html#19219" class="Bound"
      >x</a
      ><a name="19297"
      > </a
      ><a name="19298" href="Stlc.html#19223" class="Bound"
      >A</a
      ><a name="19299"
      > </a
      ><a name="19300" href="Stlc.html#19231" class="Bound"
      >s</a
      ><a name="19301"
      > </a
      ><a name="19302" href="Stlc.html#19059" class="Datatype Operator"
      >&#8758;</a
      ><a name="19303"
      > </a
      ><a name="19304" href="Stlc.html#19223" class="Bound"
      >A</a
      ><a name="19305"
      > </a
      ><a name="19306" href="Stlc.html#5420" class="InductiveConstructor Operator"
      >&#8658;</a
      ><a name="19307"
      > </a
      ><a name="19308" href="Stlc.html#19227" class="Bound"
      >B</a
      ><a name="19309"
      >
  </a
      ><a name="19312" href="Stlc.html#19312" class="InductiveConstructor"
      >app</a
      ><a name="19315"
      >           </a
      ><a name="19326" class="Symbol"
      >:</a
      ><a name="19327"
      > </a
      ><a name="19328" class="Symbol"
      >&#8704;</a
      ><a name="19329"
      > </a
      ><a name="19330" class="Symbol"
      >{</a
      ><a name="19331" href="Stlc.html#19331" class="Bound"
      >&#915;</a
      ><a name="19332" class="Symbol"
      >}</a
      ><a name="19333"
      > </a
      ><a name="19334" class="Symbol"
      >{</a
      ><a name="19335" href="Stlc.html#19335" class="Bound"
      >A</a
      ><a name="19336" class="Symbol"
      >}</a
      ><a name="19337"
      > </a
      ><a name="19338" class="Symbol"
      >{</a
      ><a name="19339" href="Stlc.html#19339" class="Bound"
      >B</a
      ><a name="19340" class="Symbol"
      >}</a
      ><a name="19341"
      > </a
      ><a name="19342" class="Symbol"
      >{</a
      ><a name="19343" href="Stlc.html#19343" class="Bound"
      >s</a
      ><a name="19344" class="Symbol"
      >}</a
      ><a name="19345"
      > </a
      ><a name="19346" class="Symbol"
      >{</a
      ><a name="19347" href="Stlc.html#19347" class="Bound"
      >t</a
      ><a name="19348" class="Symbol"
      >}</a
      ><a name="19349"
      >
                </a
      ><a name="19366" class="Symbol"
      >&#8594;</a
      ><a name="19367"
      > </a
      ><a name="19368" href="Stlc.html#19331" class="Bound"
      >&#915;</a
      ><a name="19369"
      > </a
      ><a name="19370" href="Stlc.html#19059" class="Datatype Operator"
      >&#8866;</a
      ><a name="19371"
      > </a
      ><a name="19372" href="Stlc.html#19343" class="Bound"
      >s</a
      ><a name="19373"
      > </a
      ><a name="19374" href="Stlc.html#19059" class="Datatype Operator"
      >&#8758;</a
      ><a name="19375"
      > </a
      ><a name="19376" href="Stlc.html#19335" class="Bound"
      >A</a
      ><a name="19377"
      > </a
      ><a name="19378" href="Stlc.html#5420" class="InductiveConstructor Operator"
      >&#8658;</a
      ><a name="19379"
      > </a
      ><a name="19380" href="Stlc.html#19339" class="Bound"
      >B</a
      ><a name="19381"
      >
                </a
      ><a name="19398" class="Symbol"
      >&#8594;</a
      ><a name="19399"
      > </a
      ><a name="19400" href="Stlc.html#19331" class="Bound"
      >&#915;</a
      ><a name="19401"
      > </a
      ><a name="19402" href="Stlc.html#19059" class="Datatype Operator"
      >&#8866;</a
      ><a name="19403"
      > </a
      ><a name="19404" href="Stlc.html#19347" class="Bound"
      >t</a
      ><a name="19405"
      > </a
      ><a name="19406" href="Stlc.html#19059" class="Datatype Operator"
      >&#8758;</a
      ><a name="19407"
      > </a
      ><a name="19408" href="Stlc.html#19335" class="Bound"
      >A</a
      ><a name="19409"
      >
                </a
      ><a name="19426" class="Symbol"
      >&#8594;</a
      ><a name="19427"
      > </a
      ><a name="19428" href="Stlc.html#19331" class="Bound"
      >&#915;</a
      ><a name="19429"
      > </a
      ><a name="19430" href="Stlc.html#19059" class="Datatype Operator"
      >&#8866;</a
      ><a name="19431"
      > </a
      ><a name="19432" href="Stlc.html#5541" class="InductiveConstructor"
      >app</a
      ><a name="19435"
      > </a
      ><a name="19436" href="Stlc.html#19343" class="Bound"
      >s</a
      ><a name="19437"
      > </a
      ><a name="19438" href="Stlc.html#19347" class="Bound"
      >t</a
      ><a name="19439"
      > </a
      ><a name="19440" href="Stlc.html#19059" class="Datatype Operator"
      >&#8758;</a
      ><a name="19441"
      > </a
      ><a name="19442" href="Stlc.html#19339" class="Bound"
      >B</a
      ><a name="19443"
      >
  </a
      ><a name="19446" href="Stlc.html#19446" class="InductiveConstructor"
      >true</a
      ><a name="19450"
      >          </a
      ><a name="19460" class="Symbol"
      >:</a
      ><a name="19461"
      > </a
      ><a name="19462" class="Symbol"
      >&#8704;</a
      ><a name="19463"
      > </a
      ><a name="19464" class="Symbol"
      >{</a
      ><a name="19465" href="Stlc.html#19465" class="Bound"
      >&#915;</a
      ><a name="19466" class="Symbol"
      >}</a
      ><a name="19467"
      >
                </a
      ><a name="19484" class="Symbol"
      >&#8594;</a
      ><a name="19485"
      > </a
      ><a name="19486" href="Stlc.html#19465" class="Bound"
      >&#915;</a
      ><a name="19487"
      > </a
      ><a name="19488" href="Stlc.html#19059" class="Datatype Operator"
      >&#8866;</a
      ><a name="19489"
      > </a
      ><a name="19490" href="Stlc.html#5604" class="InductiveConstructor"
      >true</a
      ><a name="19494"
      >  </a
      ><a name="19496" href="Stlc.html#19059" class="Datatype Operator"
      >&#8758;</a
      ><a name="19497"
      > </a
      ><a name="19498" href="Stlc.html#5406" class="InductiveConstructor"
      >bool</a
      ><a name="19502"
      >
  </a
      ><a name="19505" href="Stlc.html#19505" class="InductiveConstructor"
      >false</a
      ><a name="19510"
      >         </a
      ><a name="19519" class="Symbol"
      >:</a
      ><a name="19520"
      > </a
      ><a name="19521" class="Symbol"
      >&#8704;</a
      ><a name="19522"
      > </a
      ><a name="19523" class="Symbol"
      >{</a
      ><a name="19524" href="Stlc.html#19524" class="Bound"
      >&#915;</a
      ><a name="19525" class="Symbol"
      >}</a
      ><a name="19526"
      >
                </a
      ><a name="19543" class="Symbol"
      >&#8594;</a
      ><a name="19544"
      > </a
      ><a name="19545" href="Stlc.html#19524" class="Bound"
      >&#915;</a
      ><a name="19546"
      > </a
      ><a name="19547" href="Stlc.html#19059" class="Datatype Operator"
      >&#8866;</a
      ><a name="19548"
      > </a
      ><a name="19549" href="Stlc.html#5619" class="InductiveConstructor"
      >false</a
      ><a name="19554"
      > </a
      ><a name="19555" href="Stlc.html#19059" class="Datatype Operator"
      >&#8758;</a
      ><a name="19556"
      > </a
      ><a name="19557" href="Stlc.html#5406" class="InductiveConstructor"
      >bool</a
      ><a name="19561"
      >
  </a
      ><a name="19564" href="Stlc.html#19564" class="InductiveConstructor Operator"
      >if_then_else_</a
      ><a name="19577"
      > </a
      ><a name="19578" class="Symbol"
      >:</a
      ><a name="19579"
      > </a
      ><a name="19580" class="Symbol"
      >&#8704;</a
      ><a name="19581"
      > </a
      ><a name="19582" class="Symbol"
      >{</a
      ><a name="19583" href="Stlc.html#19583" class="Bound"
      >&#915;</a
      ><a name="19584" class="Symbol"
      >}</a
      ><a name="19585"
      > </a
      ><a name="19586" class="Symbol"
      >{</a
      ><a name="19587" href="Stlc.html#19587" class="Bound"
      >s</a
      ><a name="19588" class="Symbol"
      >}</a
      ><a name="19589"
      > </a
      ><a name="19590" class="Symbol"
      >{</a
      ><a name="19591" href="Stlc.html#19591" class="Bound"
      >t</a
      ><a name="19592" class="Symbol"
      >}</a
      ><a name="19593"
      > </a
      ><a name="19594" class="Symbol"
      >{</a
      ><a name="19595" href="Stlc.html#19595" class="Bound"
      >u</a
      ><a name="19596" class="Symbol"
      >}</a
      ><a name="19597"
      > </a
      ><a name="19598" class="Symbol"
      >{</a
      ><a name="19599" href="Stlc.html#19599" class="Bound"
      >A</a
      ><a name="19600" class="Symbol"
      >}</a
      ><a name="19601"
      >
                </a
      ><a name="19618" class="Symbol"
      >&#8594;</a
      ><a name="19619"
      > </a
      ><a name="19620" href="Stlc.html#19583" class="Bound"
      >&#915;</a
      ><a name="19621"
      > </a
      ><a name="19622" href="Stlc.html#19059" class="Datatype Operator"
      >&#8866;</a
      ><a name="19623"
      > </a
      ><a name="19624" href="Stlc.html#19587" class="Bound"
      >s</a
      ><a name="19625"
      > </a
      ><a name="19626" href="Stlc.html#19059" class="Datatype Operator"
      >&#8758;</a
      ><a name="19627"
      > </a
      ><a name="19628" href="Stlc.html#5406" class="InductiveConstructor"
      >bool</a
      ><a name="19632"
      >
                </a
      ><a name="19649" class="Symbol"
      >&#8594;</a
      ><a name="19650"
      > </a
      ><a name="19651" href="Stlc.html#19583" class="Bound"
      >&#915;</a
      ><a name="19652"
      > </a
      ><a name="19653" href="Stlc.html#19059" class="Datatype Operator"
      >&#8866;</a
      ><a name="19654"
      > </a
      ><a name="19655" href="Stlc.html#19591" class="Bound"
      >t</a
      ><a name="19656"
      > </a
      ><a name="19657" href="Stlc.html#19059" class="Datatype Operator"
      >&#8758;</a
      ><a name="19658"
      > </a
      ><a name="19659" href="Stlc.html#19599" class="Bound"
      >A</a
      ><a name="19660"
      >
                </a
      ><a name="19677" class="Symbol"
      >&#8594;</a
      ><a name="19678"
      > </a
      ><a name="19679" href="Stlc.html#19583" class="Bound"
      >&#915;</a
      ><a name="19680"
      > </a
      ><a name="19681" href="Stlc.html#19059" class="Datatype Operator"
      >&#8866;</a
      ><a name="19682"
      > </a
      ><a name="19683" href="Stlc.html#19595" class="Bound"
      >u</a
      ><a name="19684"
      > </a
      ><a name="19685" href="Stlc.html#19059" class="Datatype Operator"
      >&#8758;</a
      ><a name="19686"
      > </a
      ><a name="19687" href="Stlc.html#19599" class="Bound"
      >A</a
      ><a name="19688"
      >
                </a
      ><a name="19705" class="Symbol"
      >&#8594;</a
      ><a name="19706"
      > </a
      ><a name="19707" href="Stlc.html#19583" class="Bound"
      >&#915;</a
      ><a name="19708"
      > </a
      ><a name="19709" href="Stlc.html#19059" class="Datatype Operator"
      >&#8866;</a
      ><a name="19710"
      > </a
      ><a name="19711" href="Stlc.html#5634" class="InductiveConstructor Operator"
      >if</a
      ><a name="19713"
      > </a
      ><a name="19714" href="Stlc.html#19587" class="Bound"
      >s</a
      ><a name="19715"
      > </a
      ><a name="19716" href="Stlc.html#5634" class="InductiveConstructor Operator"
      >then</a
      ><a name="19720"
      > </a
      ><a name="19721" href="Stlc.html#19591" class="Bound"
      >t</a
      ><a name="19722"
      > </a
      ><a name="19723" href="Stlc.html#5634" class="InductiveConstructor Operator"
      >else</a
      ><a name="19727"
      > </a
      ><a name="19728" href="Stlc.html#19595" class="Bound"
      >u</a
      ><a name="19729"
      > </a
      ><a name="19730" href="Stlc.html#19059" class="Datatype Operator"
      >&#8758;</a
      ><a name="19731"
      > </a
      ><a name="19732" href="Stlc.html#19599" class="Bound"
      >A</a
      >
{% endraw %}</pre>

<div class="hidden">
<pre class="Agda">{% raw %}
<a name="19780" class="Keyword"
      >infix</a
      ><a name="19785"
      > </a
      ><a name="19786" class="Number"
      >1</a
      ><a name="19787"
      > </a
      ><a name="19788" href="Stlc.html#19059" class="Datatype Operator"
      >_&#8866;_&#8758;_</a
      >
{% endraw %}</pre>
</div>


### Examples

<pre class="Agda">{% raw %}
<a name="19841" href="Stlc.html#19841" class="Function"
      >typing-example1</a
      ><a name="19856"
      > </a
      ><a name="19857" class="Symbol"
      >:</a
      ><a name="19858"
      > </a
      ><a name="19859" href="Stlc.html#18127" class="Function"
      >&#8709;</a
      ><a name="19860"
      > </a
      ><a name="19861" href="Stlc.html#19059" class="Datatype Operator"
      >&#8866;</a
      ><a name="19862"
      > </a
      ><a name="19863" href="Stlc.html#6413" class="Function"
      >idB</a
      ><a name="19866"
      > </a
      ><a name="19867" href="Stlc.html#19059" class="Datatype Operator"
      >&#8758;</a
      ><a name="19868"
      > </a
      ><a name="19869" href="Stlc.html#5406" class="InductiveConstructor"
      >bool</a
      ><a name="19873"
      > </a
      ><a name="19874" href="Stlc.html#5420" class="InductiveConstructor Operator"
      >&#8658;</a
      ><a name="19875"
      > </a
      ><a name="19876" href="Stlc.html#5406" class="InductiveConstructor"
      >bool</a
      ><a name="19880"
      >
</a
      ><a name="19881" href="Stlc.html#19841" class="Function"
      >typing-example1</a
      ><a name="19896"
      > </a
      ><a name="19897" class="Symbol"
      >=</a
      ><a name="19898"
      > </a
      ><a name="19899" href="Stlc.html#19196" class="InductiveConstructor"
      >abs</a
      ><a name="19902"
      > </a
      ><a name="19903" class="Symbol"
      >(</a
      ><a name="19904" href="Stlc.html#19103" class="InductiveConstructor"
      >var</a
      ><a name="19907"
      > </a
      ><a name="19908" href="Stlc.html#6203" class="Function"
      >x</a
      ><a name="19909"
      > </a
      ><a name="19910" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="19914" class="Symbol"
      >)</a
      >
{% endraw %}</pre>

Another example:

$$\varnothing\vdash \lambda x:A. \lambda y:A\rightarrow A. y\;(y\;x) : A\rightarrow (A\rightarrow A)\rightarrow A$$.

<pre class="Agda">{% raw %}
<a name="20077" href="Stlc.html#20077" class="Function"
      >typing-example2</a
      ><a name="20092"
      > </a
      ><a name="20093" class="Symbol"
      >:</a
      ><a name="20094"
      > </a
      ><a name="20095" href="Stlc.html#18127" class="Function"
      >&#8709;</a
      ><a name="20096"
      > </a
      ><a name="20097" href="Stlc.html#19059" class="Datatype Operator"
      >&#8866;</a
      ><a name="20098"
      >
  </a
      ><a name="20101" class="Symbol"
      >(</a
      ><a name="20102" href="Stlc.html#5570" class="InductiveConstructor"
      >abs</a
      ><a name="20105"
      > </a
      ><a name="20106" href="Stlc.html#6203" class="Function"
      >x</a
      ><a name="20107"
      > </a
      ><a name="20108" href="Stlc.html#5406" class="InductiveConstructor"
      >bool</a
      ><a name="20112"
      >
    </a
      ><a name="20117" class="Symbol"
      >(</a
      ><a name="20118" href="Stlc.html#5570" class="InductiveConstructor"
      >abs</a
      ><a name="20121"
      > </a
      ><a name="20122" href="Stlc.html#6212" class="Function"
      >y</a
      ><a name="20123"
      > </a
      ><a name="20124" class="Symbol"
      >(</a
      ><a name="20125" href="Stlc.html#5406" class="InductiveConstructor"
      >bool</a
      ><a name="20129"
      > </a
      ><a name="20130" href="Stlc.html#5420" class="InductiveConstructor Operator"
      >&#8658;</a
      ><a name="20131"
      > </a
      ><a name="20132" href="Stlc.html#5406" class="InductiveConstructor"
      >bool</a
      ><a name="20136" class="Symbol"
      >)</a
      ><a name="20137"
      >
      </a
      ><a name="20144" class="Symbol"
      >(</a
      ><a name="20145" href="Stlc.html#5541" class="InductiveConstructor"
      >app</a
      ><a name="20148"
      > </a
      ><a name="20149" class="Symbol"
      >(</a
      ><a name="20150" href="Stlc.html#5521" class="InductiveConstructor"
      >var</a
      ><a name="20153"
      > </a
      ><a name="20154" href="Stlc.html#6212" class="Function"
      >y</a
      ><a name="20155" class="Symbol"
      >)</a
      ><a name="20156"
      >
        </a
      ><a name="20165" class="Symbol"
      >(</a
      ><a name="20166" href="Stlc.html#5541" class="InductiveConstructor"
      >app</a
      ><a name="20169"
      > </a
      ><a name="20170" class="Symbol"
      >(</a
      ><a name="20171" href="Stlc.html#5521" class="InductiveConstructor"
      >var</a
      ><a name="20174"
      > </a
      ><a name="20175" href="Stlc.html#6212" class="Function"
      >y</a
      ><a name="20176" class="Symbol"
      >)</a
      ><a name="20177"
      > </a
      ><a name="20178" class="Symbol"
      >(</a
      ><a name="20179" href="Stlc.html#5521" class="InductiveConstructor"
      >var</a
      ><a name="20182"
      > </a
      ><a name="20183" href="Stlc.html#6203" class="Function"
      >x</a
      ><a name="20184" class="Symbol"
      >)))))</a
      ><a name="20189"
      >
  </a
      ><a name="20192" href="Stlc.html#19059" class="Datatype Operator"
      >&#8758;</a
      ><a name="20193"
      > </a
      ><a name="20194" class="Symbol"
      >(</a
      ><a name="20195" href="Stlc.html#5406" class="InductiveConstructor"
      >bool</a
      ><a name="20199"
      > </a
      ><a name="20200" href="Stlc.html#5420" class="InductiveConstructor Operator"
      >&#8658;</a
      ><a name="20201"
      > </a
      ><a name="20202" class="Symbol"
      >(</a
      ><a name="20203" href="Stlc.html#5406" class="InductiveConstructor"
      >bool</a
      ><a name="20207"
      > </a
      ><a name="20208" href="Stlc.html#5420" class="InductiveConstructor Operator"
      >&#8658;</a
      ><a name="20209"
      > </a
      ><a name="20210" href="Stlc.html#5406" class="InductiveConstructor"
      >bool</a
      ><a name="20214" class="Symbol"
      >)</a
      ><a name="20215"
      > </a
      ><a name="20216" href="Stlc.html#5420" class="InductiveConstructor Operator"
      >&#8658;</a
      ><a name="20217"
      > </a
      ><a name="20218" href="Stlc.html#5406" class="InductiveConstructor"
      >bool</a
      ><a name="20222" class="Symbol"
      >)</a
      ><a name="20223"
      >
</a
      ><a name="20224" href="Stlc.html#20077" class="Function"
      >typing-example2</a
      ><a name="20239"
      > </a
      ><a name="20240" class="Symbol"
      >=</a
      ><a name="20241"
      >
  </a
      ><a name="20244" class="Symbol"
      >(</a
      ><a name="20245" href="Stlc.html#19196" class="InductiveConstructor"
      >abs</a
      ><a name="20248"
      >
    </a
      ><a name="20253" class="Symbol"
      >(</a
      ><a name="20254" href="Stlc.html#19196" class="InductiveConstructor"
      >abs</a
      ><a name="20257"
      >
      </a
      ><a name="20264" class="Symbol"
      >(</a
      ><a name="20265" href="Stlc.html#19312" class="InductiveConstructor"
      >app</a
      ><a name="20268"
      > </a
      ><a name="20269" class="Symbol"
      >(</a
      ><a name="20270" href="Stlc.html#19103" class="InductiveConstructor"
      >var</a
      ><a name="20273"
      > </a
      ><a name="20274" href="Stlc.html#6212" class="Function"
      >y</a
      ><a name="20275"
      > </a
      ><a name="20276" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="20280" class="Symbol"
      >)</a
      ><a name="20281"
      >
        </a
      ><a name="20290" class="Symbol"
      >(</a
      ><a name="20291" href="Stlc.html#19312" class="InductiveConstructor"
      >app</a
      ><a name="20294"
      > </a
      ><a name="20295" class="Symbol"
      >(</a
      ><a name="20296" href="Stlc.html#19103" class="InductiveConstructor"
      >var</a
      ><a name="20299"
      > </a
      ><a name="20300" href="Stlc.html#6212" class="Function"
      >y</a
      ><a name="20301"
      > </a
      ><a name="20302" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="20306" class="Symbol"
      >)</a
      ><a name="20307"
      > </a
      ><a name="20308" class="Symbol"
      >(</a
      ><a name="20309" href="Stlc.html#19103" class="InductiveConstructor"
      >var</a
      ><a name="20312"
      > </a
      ><a name="20313" href="Stlc.html#6203" class="Function"
      >x</a
      ><a name="20314"
      > </a
      ><a name="20315" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="20319" class="Symbol"
      >)</a
      ><a name="20320"
      > </a
      ><a name="20321" class="Symbol"
      >))))</a
      >
{% endraw %}</pre>

#### Exercise: 2 stars (typing-example3)
Formally prove the following typing derivation holds:

$$\exists A, \varnothing\vdash \lambda x:bool\rightarrow B. \lambda y:bool\rightarrow bool. \lambda z:bool. y\;(x\;z) : A$$.

<pre class="Agda">{% raw %}
<a name="20573" class="Keyword"
      >postulate</a
      ><a name="20582"
      >
  </a
      ><a name="20585" href="Stlc.html#20585" class="Postulate"
      >typing-example3</a
      ><a name="20600"
      > </a
      ><a name="20601" class="Symbol"
      >:</a
      ><a name="20602"
      > </a
      ><a name="20603" href="https://agda.github.io/agda-stdlib/Data.Product.html#823" class="Function"
      >&#8707;</a
      ><a name="20604"
      > </a
      ><a name="20605" class="Symbol"
      >&#955;</a
      ><a name="20606"
      > </a
      ><a name="20607" href="Stlc.html#20607" class="Bound"
      >A</a
      ><a name="20608"
      > </a
      ><a name="20609" class="Symbol"
      >&#8594;</a
      ><a name="20610"
      > </a
      ><a name="20611" href="Stlc.html#18127" class="Function"
      >&#8709;</a
      ><a name="20612"
      > </a
      ><a name="20613" href="Stlc.html#19059" class="Datatype Operator"
      >&#8866;</a
      ><a name="20614"
      >
    </a
      ><a name="20619" class="Symbol"
      >(</a
      ><a name="20620" href="Stlc.html#5570" class="InductiveConstructor"
      >abs</a
      ><a name="20623"
      > </a
      ><a name="20624" href="Stlc.html#6203" class="Function"
      >x</a
      ><a name="20625"
      > </a
      ><a name="20626" class="Symbol"
      >(</a
      ><a name="20627" href="Stlc.html#5406" class="InductiveConstructor"
      >bool</a
      ><a name="20631"
      > </a
      ><a name="20632" href="Stlc.html#5420" class="InductiveConstructor Operator"
      >&#8658;</a
      ><a name="20633"
      > </a
      ><a name="20634" href="Stlc.html#5406" class="InductiveConstructor"
      >bool</a
      ><a name="20638" class="Symbol"
      >)</a
      ><a name="20639"
      >
      </a
      ><a name="20646" class="Symbol"
      >(</a
      ><a name="20647" href="Stlc.html#5570" class="InductiveConstructor"
      >abs</a
      ><a name="20650"
      > </a
      ><a name="20651" href="Stlc.html#6212" class="Function"
      >y</a
      ><a name="20652"
      > </a
      ><a name="20653" class="Symbol"
      >(</a
      ><a name="20654" href="Stlc.html#5406" class="InductiveConstructor"
      >bool</a
      ><a name="20658"
      > </a
      ><a name="20659" href="Stlc.html#5420" class="InductiveConstructor Operator"
      >&#8658;</a
      ><a name="20660"
      > </a
      ><a name="20661" href="Stlc.html#5406" class="InductiveConstructor"
      >bool</a
      ><a name="20665" class="Symbol"
      >)</a
      ><a name="20666"
      >
        </a
      ><a name="20675" class="Symbol"
      >(</a
      ><a name="20676" href="Stlc.html#5570" class="InductiveConstructor"
      >abs</a
      ><a name="20679"
      > </a
      ><a name="20680" href="Stlc.html#6221" class="Function"
      >z</a
      ><a name="20681"
      > </a
      ><a name="20682" href="Stlc.html#5406" class="InductiveConstructor"
      >bool</a
      ><a name="20686"
      >
          </a
      ><a name="20697" class="Symbol"
      >(</a
      ><a name="20698" href="Stlc.html#5541" class="InductiveConstructor"
      >app</a
      ><a name="20701"
      > </a
      ><a name="20702" class="Symbol"
      >(</a
      ><a name="20703" href="Stlc.html#5521" class="InductiveConstructor"
      >var</a
      ><a name="20706"
      > </a
      ><a name="20707" href="Stlc.html#6212" class="Function"
      >y</a
      ><a name="20708" class="Symbol"
      >)</a
      ><a name="20709"
      > </a
      ><a name="20710" class="Symbol"
      >(</a
      ><a name="20711" href="Stlc.html#5541" class="InductiveConstructor"
      >app</a
      ><a name="20714"
      > </a
      ><a name="20715" class="Symbol"
      >(</a
      ><a name="20716" href="Stlc.html#5521" class="InductiveConstructor"
      >var</a
      ><a name="20719"
      > </a
      ><a name="20720" href="Stlc.html#6203" class="Function"
      >x</a
      ><a name="20721" class="Symbol"
      >)</a
      ><a name="20722"
      > </a
      ><a name="20723" class="Symbol"
      >(</a
      ><a name="20724" href="Stlc.html#5521" class="InductiveConstructor"
      >var</a
      ><a name="20727"
      > </a
      ><a name="20728" href="Stlc.html#6221" class="Function"
      >z</a
      ><a name="20729" class="Symbol"
      >))))))</a
      ><a name="20735"
      > </a
      ><a name="20736" href="Stlc.html#19059" class="Datatype Operator"
      >&#8758;</a
      ><a name="20737"
      > </a
      ><a name="20738" href="Stlc.html#20607" class="Bound"
      >A</a
      >
{% endraw %}</pre>

We can also show that terms are _not_ typable.  For example, let's
formally check that there is no typing derivation assigning a type
to the term $$\lambda x:bool. \lambda y:bool. x\;y$$---i.e.,


$$\nexists A, \varnothing\vdash \lambda x:bool. \lambda y:bool. x\;y : A$$.

<pre class="Agda">{% raw %}
<a name="21039" class="Keyword"
      >postulate</a
      ><a name="21048"
      >
  </a
      ><a name="21051" href="Stlc.html#21051" class="Postulate"
      >typing-nonexample1</a
      ><a name="21069"
      > </a
      ><a name="21070" class="Symbol"
      >:</a
      ><a name="21071"
      > </a
      ><a name="21072" href="https://agda.github.io/agda-stdlib/Data.Product.html#884" class="Function"
      >&#8708;</a
      ><a name="21073"
      > </a
      ><a name="21074" class="Symbol"
      >&#955;</a
      ><a name="21075"
      > </a
      ><a name="21076" href="Stlc.html#21076" class="Bound"
      >A</a
      ><a name="21077"
      > </a
      ><a name="21078" class="Symbol"
      >&#8594;</a
      ><a name="21079"
      > </a
      ><a name="21080" href="Stlc.html#18127" class="Function"
      >&#8709;</a
      ><a name="21081"
      > </a
      ><a name="21082" href="Stlc.html#19059" class="Datatype Operator"
      >&#8866;</a
      ><a name="21083"
      >
    </a
      ><a name="21088" class="Symbol"
      >(</a
      ><a name="21089" href="Stlc.html#5570" class="InductiveConstructor"
      >abs</a
      ><a name="21092"
      > </a
      ><a name="21093" href="Stlc.html#6203" class="Function"
      >x</a
      ><a name="21094"
      > </a
      ><a name="21095" href="Stlc.html#5406" class="InductiveConstructor"
      >bool</a
      ><a name="21099"
      >
      </a
      ><a name="21106" class="Symbol"
      >(</a
      ><a name="21107" href="Stlc.html#5570" class="InductiveConstructor"
      >abs</a
      ><a name="21110"
      > </a
      ><a name="21111" href="Stlc.html#6212" class="Function"
      >y</a
      ><a name="21112"
      > </a
      ><a name="21113" href="Stlc.html#5406" class="InductiveConstructor"
      >bool</a
      ><a name="21117"
      >
        </a
      ><a name="21126" class="Symbol"
      >(</a
      ><a name="21127" href="Stlc.html#5541" class="InductiveConstructor"
      >app</a
      ><a name="21130"
      > </a
      ><a name="21131" class="Symbol"
      >(</a
      ><a name="21132" href="Stlc.html#5521" class="InductiveConstructor"
      >var</a
      ><a name="21135"
      > </a
      ><a name="21136" href="Stlc.html#6203" class="Function"
      >x</a
      ><a name="21137" class="Symbol"
      >)</a
      ><a name="21138"
      > </a
      ><a name="21139" class="Symbol"
      >(</a
      ><a name="21140" href="Stlc.html#5521" class="InductiveConstructor"
      >var</a
      ><a name="21143"
      > </a
      ><a name="21144" href="Stlc.html#6212" class="Function"
      >y</a
      ><a name="21145" class="Symbol"
      >))))</a
      ><a name="21149"
      > </a
      ><a name="21150" href="Stlc.html#19059" class="Datatype Operator"
      >&#8758;</a
      ><a name="21151"
      > </a
      ><a name="21152" href="Stlc.html#21076" class="Bound"
      >A</a
      >
{% endraw %}</pre>

#### Exercise: 3 stars, optional (typing-nonexample2)
Another nonexample:

$$\nexists A, \exists B, \varnothing\vdash \lambda x:A. x\;x : B$$.

<pre class="Agda">{% raw %}
<a name="21323" class="Keyword"
      >postulate</a
      ><a name="21332"
      >
  </a
      ><a name="21335" href="Stlc.html#21335" class="Postulate"
      >typing-nonexample2</a
      ><a name="21353"
      > </a
      ><a name="21354" class="Symbol"
      >:</a
      ><a name="21355"
      > </a
      ><a name="21356" href="https://agda.github.io/agda-stdlib/Data.Product.html#884" class="Function"
      >&#8708;</a
      ><a name="21357"
      > </a
      ><a name="21358" class="Symbol"
      >&#955;</a
      ><a name="21359"
      > </a
      ><a name="21360" href="Stlc.html#21360" class="Bound"
      >A</a
      ><a name="21361"
      > </a
      ><a name="21362" class="Symbol"
      >&#8594;</a
      ><a name="21363"
      > </a
      ><a name="21364" href="https://agda.github.io/agda-stdlib/Data.Product.html#823" class="Function"
      >&#8707;</a
      ><a name="21365"
      > </a
      ><a name="21366" class="Symbol"
      >&#955;</a
      ><a name="21367"
      > </a
      ><a name="21368" href="Stlc.html#21368" class="Bound"
      >B</a
      ><a name="21369"
      > </a
      ><a name="21370" class="Symbol"
      >&#8594;</a
      ><a name="21371"
      > </a
      ><a name="21372" href="Stlc.html#18127" class="Function"
      >&#8709;</a
      ><a name="21373"
      > </a
      ><a name="21374" href="Stlc.html#19059" class="Datatype Operator"
      >&#8866;</a
      ><a name="21375"
      >
    </a
      ><a name="21380" class="Symbol"
      >(</a
      ><a name="21381" href="Stlc.html#5570" class="InductiveConstructor"
      >abs</a
      ><a name="21384"
      > </a
      ><a name="21385" href="Stlc.html#6203" class="Function"
      >x</a
      ><a name="21386"
      > </a
      ><a name="21387" href="Stlc.html#21368" class="Bound"
      >B</a
      ><a name="21388"
      > </a
      ><a name="21389" class="Symbol"
      >(</a
      ><a name="21390" href="Stlc.html#5541" class="InductiveConstructor"
      >app</a
      ><a name="21393"
      > </a
      ><a name="21394" class="Symbol"
      >(</a
      ><a name="21395" href="Stlc.html#5521" class="InductiveConstructor"
      >var</a
      ><a name="21398"
      > </a
      ><a name="21399" href="Stlc.html#6203" class="Function"
      >x</a
      ><a name="21400" class="Symbol"
      >)</a
      ><a name="21401"
      > </a
      ><a name="21402" class="Symbol"
      >(</a
      ><a name="21403" href="Stlc.html#5521" class="InductiveConstructor"
      >var</a
      ><a name="21406"
      > </a
      ><a name="21407" href="Stlc.html#6203" class="Function"
      >x</a
      ><a name="21408" class="Symbol"
      >)))</a
      ><a name="21411"
      > </a
      ><a name="21412" href="Stlc.html#19059" class="Datatype Operator"
      >&#8758;</a
      ><a name="21413"
      > </a
      ><a name="21414" href="Stlc.html#21360" class="Bound"
      >A</a
      >
{% endraw %}</pre>
