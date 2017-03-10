---
title     : "Stlc: The Simply Typed Lambda-Calculus"
layout    : page
permalink : /Stlc
---

<pre class="Agda">{% raw %}
<a name="111" class="Keyword"
      >module</a
      ><a name="117"
      > </a
      ><a name="118" href="Stlc.html#1" class="Module"
      >Stlc</a
      ><a name="122"
      > </a
      ><a name="123" class="Keyword"
      >where</a
      >
{% endraw %}</pre>

<div class="hidden">
<pre class="Agda">{% raw %}
<a name="175" class="Keyword"
      >open</a
      ><a name="179"
      > </a
      ><a name="180" class="Keyword"
      >import</a
      ><a name="186"
      > </a
      ><a name="187" class="Module"
      >Maps</a
      ><a name="191"
      > </a
      ><a name="192" class="Keyword"
      >using</a
      ><a name="197"
      > </a
      ><a name="198" class="Symbol"
      >(</a
      ><a name="199" href="Maps.html#2275" class="Datatype"
      >Id</a
      ><a name="201" class="Symbol"
      >;</a
      ><a name="202"
      > </a
      ><a name="203" href="Maps.html#2292" class="InductiveConstructor"
      >id</a
      ><a name="205" class="Symbol"
      >;</a
      ><a name="206"
      > </a
      ><a name="207" href="Maps.html#2329" class="Function Operator"
      >_&#8799;_</a
      ><a name="210" class="Symbol"
      >;</a
      ><a name="211"
      > </a
      ><a name="212" href="Maps.html#9394" class="Function"
      >PartialMap</a
      ><a name="222" class="Symbol"
      >;</a
      ><a name="223"
      > </a
      ><a name="224" class="Keyword"
      >module</a
      ><a name="230"
      > </a
      ><a name="231" href="Maps.html#9483" class="Module"
      >PartialMap</a
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
      ><a name="255" href="https://agda.github.io/agda-stdlib/Data.Empty.html#1" class="Module"
      >Data.Empty</a
      ><a name="265"
      > </a
      ><a name="266" class="Keyword"
      >using</a
      ><a name="271"
      > </a
      ><a name="272" class="Symbol"
      >(</a
      ><a name="273" href="https://agda.github.io/agda-stdlib/Data.Empty.html#243" class="Datatype"
      >&#8869;</a
      ><a name="274" class="Symbol"
      >;</a
      ><a name="275"
      > </a
      ><a name="276" href="https://agda.github.io/agda-stdlib/Data.Empty.html#348" class="Function"
      >&#8869;-elim</a
      ><a name="282" class="Symbol"
      >)</a
      ><a name="283"
      >
</a
      ><a name="284" class="Keyword"
      >open</a
      ><a name="288"
      > </a
      ><a name="289" class="Keyword"
      >import</a
      ><a name="295"
      > </a
      ><a name="296" href="https://agda.github.io/agda-stdlib/Data.Maybe.html#1" class="Module"
      >Data.Maybe</a
      ><a name="306"
      > </a
      ><a name="307" class="Keyword"
      >using</a
      ><a name="312"
      > </a
      ><a name="313" class="Symbol"
      >(</a
      ><a name="314" href="https://agda.github.io/agda-stdlib/Data.Maybe.Base.html#335" class="Datatype"
      >Maybe</a
      ><a name="319" class="Symbol"
      >;</a
      ><a name="320"
      > </a
      ><a name="321" href="https://agda.github.io/agda-stdlib/Data.Maybe.html#1527" class="InductiveConstructor"
      >just</a
      ><a name="325" class="Symbol"
      >;</a
      ><a name="326"
      > </a
      ><a name="327" href="https://agda.github.io/agda-stdlib/Data.Maybe.html#1588" class="InductiveConstructor"
      >nothing</a
      ><a name="334" class="Symbol"
      >)</a
      ><a name="335"
      >
</a
      ><a name="336" class="Keyword"
      >open</a
      ><a name="340"
      > </a
      ><a name="341" class="Keyword"
      >import</a
      ><a name="347"
      > </a
      ><a name="348" href="https://agda.github.io/agda-stdlib/Data.Nat.html#1" class="Module"
      >Data.Nat</a
      ><a name="356"
      > </a
      ><a name="357" class="Keyword"
      >using</a
      ><a name="362"
      > </a
      ><a name="363" class="Symbol"
      >(</a
      ><a name="364" href="Agda.Builtin.Nat.html#97" class="Datatype"
      >&#8469;</a
      ><a name="365" class="Symbol"
      >;</a
      ><a name="366"
      > </a
      ><a name="367" href="Agda.Builtin.Nat.html#128" class="InductiveConstructor"
      >suc</a
      ><a name="370" class="Symbol"
      >;</a
      ><a name="371"
      > </a
      ><a name="372" href="Agda.Builtin.Nat.html#115" class="InductiveConstructor"
      >zero</a
      ><a name="376" class="Symbol"
      >;</a
      ><a name="377"
      > </a
      ><a name="378" href="Agda.Builtin.Nat.html#230" class="Primitive Operator"
      >_+_</a
      ><a name="381" class="Symbol"
      >)</a
      ><a name="382"
      >
</a
      ><a name="383" class="Keyword"
      >open</a
      ><a name="387"
      > </a
      ><a name="388" class="Keyword"
      >import</a
      ><a name="394"
      > </a
      ><a name="395" href="https://agda.github.io/agda-stdlib/Data.Product.html#1" class="Module"
      >Data.Product</a
      ><a name="407"
      > </a
      ><a name="408" class="Keyword"
      >using</a
      ><a name="413"
      > </a
      ><a name="414" class="Symbol"
      >(</a
      ><a name="415" href="https://agda.github.io/agda-stdlib/Data.Product.html#823" class="Function"
      >&#8707;</a
      ><a name="416" class="Symbol"
      >;</a
      ><a name="417"
      > </a
      ><a name="418" href="https://agda.github.io/agda-stdlib/Data.Product.html#884" class="Function"
      >&#8708;</a
      ><a name="419" class="Symbol"
      >;</a
      ><a name="420"
      > </a
      ><a name="421" href="https://agda.github.io/agda-stdlib/Data.Product.html#509" class="InductiveConstructor Operator"
      >_,_</a
      ><a name="424" class="Symbol"
      >)</a
      ><a name="425"
      >
</a
      ><a name="426" class="Keyword"
      >open</a
      ><a name="430"
      > </a
      ><a name="431" class="Keyword"
      >import</a
      ><a name="437"
      > </a
      ><a name="438" href="https://agda.github.io/agda-stdlib/Function.html#1" class="Module"
      >Function</a
      ><a name="446"
      > </a
      ><a name="447" class="Keyword"
      >using</a
      ><a name="452"
      > </a
      ><a name="453" class="Symbol"
      >(</a
      ><a name="454" href="https://agda.github.io/agda-stdlib/Function.html#713" class="Function Operator"
      >_&#8728;_</a
      ><a name="457" class="Symbol"
      >;</a
      ><a name="458"
      > </a
      ><a name="459" href="https://agda.github.io/agda-stdlib/Function.html#1835" class="Function Operator"
      >_$_</a
      ><a name="462" class="Symbol"
      >)</a
      ><a name="463"
      >
</a
      ><a name="464" class="Keyword"
      >open</a
      ><a name="468"
      > </a
      ><a name="469" class="Keyword"
      >import</a
      ><a name="475"
      > </a
      ><a name="476" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#1" class="Module"
      >Relation.Nullary</a
      ><a name="492"
      > </a
      ><a name="493" class="Keyword"
      >using</a
      ><a name="498"
      > </a
      ><a name="499" class="Symbol"
      >(</a
      ><a name="500" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#484" class="Datatype"
      >Dec</a
      ><a name="503" class="Symbol"
      >;</a
      ><a name="504"
      > </a
      ><a name="505" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#520" class="InductiveConstructor"
      >yes</a
      ><a name="508" class="Symbol"
      >;</a
      ><a name="509"
      > </a
      ><a name="510" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#547" class="InductiveConstructor"
      >no</a
      ><a name="512" class="Symbol"
      >)</a
      ><a name="513"
      >
</a
      ><a name="514" class="Keyword"
      >open</a
      ><a name="518"
      > </a
      ><a name="519" class="Keyword"
      >import</a
      ><a name="525"
      > </a
      ><a name="526" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#1" class="Module"
      >Relation.Binary.PropositionalEquality</a
      ><a name="563"
      > </a
      ><a name="564" class="Keyword"
      >using</a
      ><a name="569"
      > </a
      ><a name="570" class="Symbol"
      >(</a
      ><a name="571" href="Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >_&#8801;_</a
      ><a name="574" class="Symbol"
      >;</a
      ><a name="575"
      > </a
      ><a name="576" href="https://agda.github.io/agda-stdlib/Relation.Binary.Core.html#4493" class="Function Operator"
      >_&#8802;_</a
      ><a name="579" class="Symbol"
      >;</a
      ><a name="580"
      > </a
      ><a name="581" href="Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="585" class="Symbol"
      >)</a
      >
{% endraw %}</pre>
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

<pre class="Agda">{% raw %}
<a name="5458" class="Keyword"
      >data</a
      ><a name="5462"
      > </a
      ><a name="5463" href="Stlc.html#5463" class="Datatype"
      >Type</a
      ><a name="5467"
      > </a
      ><a name="5468" class="Symbol"
      >:</a
      ><a name="5469"
      > </a
      ><a name="5470" class="PrimitiveType"
      >Set</a
      ><a name="5473"
      > </a
      ><a name="5474" class="Keyword"
      >where</a
      ><a name="5479"
      >
  </a
      ><a name="5482" href="Stlc.html#5482" class="InductiveConstructor"
      >bool</a
      ><a name="5486"
      > </a
      ><a name="5487" class="Symbol"
      >:</a
      ><a name="5488"
      > </a
      ><a name="5489" href="Stlc.html#5463" class="Datatype"
      >Type</a
      ><a name="5493"
      >
  </a
      ><a name="5496" href="Stlc.html#5496" class="InductiveConstructor Operator"
      >_&#8658;_</a
      ><a name="5499"
      >  </a
      ><a name="5501" class="Symbol"
      >:</a
      ><a name="5502"
      > </a
      ><a name="5503" href="Stlc.html#5463" class="Datatype"
      >Type</a
      ><a name="5507"
      > </a
      ><a name="5508" class="Symbol"
      >&#8594;</a
      ><a name="5509"
      > </a
      ><a name="5510" href="Stlc.html#5463" class="Datatype"
      >Type</a
      ><a name="5514"
      > </a
      ><a name="5515" class="Symbol"
      >&#8594;</a
      ><a name="5516"
      > </a
      ><a name="5517" href="Stlc.html#5463" class="Datatype"
      >Type</a
      >
{% endraw %}</pre>

<div class="hidden">
<pre class="Agda">{% raw %}
<a name="5568" class="Keyword"
      >infixr</a
      ><a name="5574"
      > </a
      ><a name="5575" class="Number"
      >5</a
      ><a name="5576"
      > </a
      ><a name="5577" href="Stlc.html#5496" class="InductiveConstructor Operator"
      >_&#8658;_</a
      >
{% endraw %}</pre>
</div>


### Terms

<pre class="Agda">{% raw %}
<a name="5625" class="Keyword"
      >data</a
      ><a name="5629"
      > </a
      ><a name="5630" href="Stlc.html#5630" class="Datatype"
      >Term</a
      ><a name="5634"
      > </a
      ><a name="5635" class="Symbol"
      >:</a
      ><a name="5636"
      > </a
      ><a name="5637" class="PrimitiveType"
      >Set</a
      ><a name="5640"
      > </a
      ><a name="5641" class="Keyword"
      >where</a
      ><a name="5646"
      >
  </a
      ><a name="5649" href="Stlc.html#5649" class="InductiveConstructor"
      >var</a
      ><a name="5652"
      >   </a
      ><a name="5655" class="Symbol"
      >:</a
      ><a name="5656"
      > </a
      ><a name="5657" href="Maps.html#2275" class="Datatype"
      >Id</a
      ><a name="5659"
      > </a
      ><a name="5660" class="Symbol"
      >&#8594;</a
      ><a name="5661"
      > </a
      ><a name="5662" href="Stlc.html#5630" class="Datatype"
      >Term</a
      ><a name="5666"
      >
  </a
      ><a name="5669" href="Stlc.html#5669" class="InductiveConstructor"
      >app</a
      ><a name="5672"
      >   </a
      ><a name="5675" class="Symbol"
      >:</a
      ><a name="5676"
      > </a
      ><a name="5677" href="Stlc.html#5630" class="Datatype"
      >Term</a
      ><a name="5681"
      > </a
      ><a name="5682" class="Symbol"
      >&#8594;</a
      ><a name="5683"
      > </a
      ><a name="5684" href="Stlc.html#5630" class="Datatype"
      >Term</a
      ><a name="5688"
      > </a
      ><a name="5689" class="Symbol"
      >&#8594;</a
      ><a name="5690"
      > </a
      ><a name="5691" href="Stlc.html#5630" class="Datatype"
      >Term</a
      ><a name="5695"
      >
  </a
      ><a name="5698" href="Stlc.html#5698" class="InductiveConstructor"
      >abs</a
      ><a name="5701"
      >   </a
      ><a name="5704" class="Symbol"
      >:</a
      ><a name="5705"
      > </a
      ><a name="5706" href="Maps.html#2275" class="Datatype"
      >Id</a
      ><a name="5708"
      > </a
      ><a name="5709" class="Symbol"
      >&#8594;</a
      ><a name="5710"
      > </a
      ><a name="5711" href="Stlc.html#5463" class="Datatype"
      >Type</a
      ><a name="5715"
      > </a
      ><a name="5716" class="Symbol"
      >&#8594;</a
      ><a name="5717"
      > </a
      ><a name="5718" href="Stlc.html#5630" class="Datatype"
      >Term</a
      ><a name="5722"
      > </a
      ><a name="5723" class="Symbol"
      >&#8594;</a
      ><a name="5724"
      > </a
      ><a name="5725" href="Stlc.html#5630" class="Datatype"
      >Term</a
      ><a name="5729"
      >
  </a
      ><a name="5732" href="Stlc.html#5732" class="InductiveConstructor"
      >true</a
      ><a name="5736"
      >  </a
      ><a name="5738" class="Symbol"
      >:</a
      ><a name="5739"
      > </a
      ><a name="5740" href="Stlc.html#5630" class="Datatype"
      >Term</a
      ><a name="5744"
      >
  </a
      ><a name="5747" href="Stlc.html#5747" class="InductiveConstructor"
      >false</a
      ><a name="5752"
      > </a
      ><a name="5753" class="Symbol"
      >:</a
      ><a name="5754"
      > </a
      ><a name="5755" href="Stlc.html#5630" class="Datatype"
      >Term</a
      ><a name="5759"
      >
  </a
      ><a name="5762" href="Stlc.html#5762" class="InductiveConstructor Operator"
      >if_then_else_</a
      ><a name="5775"
      > </a
      ><a name="5776" class="Symbol"
      >:</a
      ><a name="5777"
      > </a
      ><a name="5778" href="Stlc.html#5630" class="Datatype"
      >Term</a
      ><a name="5782"
      > </a
      ><a name="5783" class="Symbol"
      >&#8594;</a
      ><a name="5784"
      > </a
      ><a name="5785" href="Stlc.html#5630" class="Datatype"
      >Term</a
      ><a name="5789"
      > </a
      ><a name="5790" class="Symbol"
      >&#8594;</a
      ><a name="5791"
      > </a
      ><a name="5792" href="Stlc.html#5630" class="Datatype"
      >Term</a
      ><a name="5796"
      > </a
      ><a name="5797" class="Symbol"
      >&#8594;</a
      ><a name="5798"
      > </a
      ><a name="5799" href="Stlc.html#5630" class="Datatype"
      >Term</a
      >
{% endraw %}</pre>

<div class="hidden">
<pre class="Agda">{% raw %}
<a name="5850" class="Keyword"
      >infixr</a
      ><a name="5856"
      > </a
      ><a name="5857" class="Number"
      >8</a
      ><a name="5858"
      > </a
      ><a name="5859" href="Stlc.html#19624" class="InductiveConstructor Operator"
      >if_then_else_</a
      >
{% endraw %}</pre>
</div>

Note that an abstraction $$\lambda x:A.t$$ (formally, `abs x A t`) is
always annotated with the type $$A$$ of its parameter, in contrast
to Agda (and other functional languages like ML, Haskell, etc.),
which use _type inference_ to fill in missing annotations.  We're
not considering type inference here.

Some examples...

<pre class="Agda">{% raw %}
<a name="6229" href="Stlc.html#6229" class="Function"
      >x</a
      ><a name="6230"
      > </a
      ><a name="6231" class="Symbol"
      >=</a
      ><a name="6232"
      > </a
      ><a name="6233" href="Maps.html#2292" class="InductiveConstructor"
      >id</a
      ><a name="6235"
      > </a
      ><a name="6236" class="Number"
      >0</a
      ><a name="6237"
      >
</a
      ><a name="6238" href="Stlc.html#6238" class="Function"
      >y</a
      ><a name="6239"
      > </a
      ><a name="6240" class="Symbol"
      >=</a
      ><a name="6241"
      > </a
      ><a name="6242" href="Maps.html#2292" class="InductiveConstructor"
      >id</a
      ><a name="6244"
      > </a
      ><a name="6245" class="Number"
      >1</a
      ><a name="6246"
      >
</a
      ><a name="6247" href="Stlc.html#6247" class="Function"
      >z</a
      ><a name="6248"
      > </a
      ><a name="6249" class="Symbol"
      >=</a
      ><a name="6250"
      > </a
      ><a name="6251" href="Maps.html#2292" class="InductiveConstructor"
      >id</a
      ><a name="6253"
      > </a
      ><a name="6254" class="Number"
      >2</a
      >
{% endraw %}</pre>

<div class="hidden">
<pre class="Agda">{% raw %}
<a name="6302" class="Symbol"
      >{-#</a
      ><a name="6305"
      > </a
      ><a name="6306" class="Keyword"
      >DISPLAY</a
      ><a name="6313"
      > </a
      ><a name="6314" href="Maps.html#2292" class="InductiveConstructor"
      >id</a
      ><a name="6316"
      > </a
      ><a name="6317" href="Agda.Builtin.Nat.html#115" class="InductiveConstructor"
      >zero</a
      ><a name="6321"
      > = </a
      ><a name="6324" href="Stlc.html#6229" class="Function"
      >x</a
      ><a name="6325"
      > </a
      ><a name="6326" class="Symbol"
      >#-}</a
      ><a name="6329"
      >
</a
      ><a name="6330" class="Symbol"
      >{-#</a
      ><a name="6333"
      > </a
      ><a name="6334" class="Keyword"
      >DISPLAY</a
      ><a name="6341"
      > </a
      ><a name="6342" href="Maps.html#2292" class="InductiveConstructor"
      >id</a
      ><a name="6344"
      > (</a
      ><a name="6346" href="Agda.Builtin.Nat.html#128" class="InductiveConstructor"
      >suc</a
      ><a name="6349"
      > </a
      ><a name="6350" href="Agda.Builtin.Nat.html#115" class="InductiveConstructor"
      >zero</a
      ><a name="6354"
      >) = </a
      ><a name="6358" href="Stlc.html#6238" class="Function"
      >y</a
      ><a name="6359"
      > </a
      ><a name="6360" class="Symbol"
      >#-}</a
      ><a name="6363"
      >
</a
      ><a name="6364" class="Symbol"
      >{-#</a
      ><a name="6367"
      > </a
      ><a name="6368" class="Keyword"
      >DISPLAY</a
      ><a name="6375"
      > </a
      ><a name="6376" href="Maps.html#2292" class="InductiveConstructor"
      >id</a
      ><a name="6378"
      > (</a
      ><a name="6380" href="Agda.Builtin.Nat.html#128" class="InductiveConstructor"
      >suc</a
      ><a name="6383"
      > (</a
      ><a name="6385" href="Agda.Builtin.Nat.html#128" class="InductiveConstructor"
      >suc</a
      ><a name="6388"
      > </a
      ><a name="6389" href="Agda.Builtin.Nat.html#115" class="InductiveConstructor"
      >zero</a
      ><a name="6393"
      >)) = </a
      ><a name="6398" href="Stlc.html#6247" class="Function"
      >z</a
      ><a name="6399"
      > </a
      ><a name="6400" class="Symbol"
      >#-}</a
      >
{% endraw %}</pre>
</div>

$$\text{idB} = \lambda x:bool. x$$.

<pre class="Agda">{% raw %}
<a name="6473" href="Stlc.html#6473" class="Function"
      >idB</a
      ><a name="6476"
      > </a
      ><a name="6477" class="Symbol"
      >=</a
      ><a name="6478"
      > </a
      ><a name="6479" class="Symbol"
      >(</a
      ><a name="6480" href="Stlc.html#5698" class="InductiveConstructor"
      >abs</a
      ><a name="6483"
      > </a
      ><a name="6484" href="Stlc.html#6229" class="Function"
      >x</a
      ><a name="6485"
      > </a
      ><a name="6486" href="Stlc.html#5482" class="InductiveConstructor"
      >bool</a
      ><a name="6490"
      > </a
      ><a name="6491" class="Symbol"
      >(</a
      ><a name="6492" href="Stlc.html#5649" class="InductiveConstructor"
      >var</a
      ><a name="6495"
      > </a
      ><a name="6496" href="Stlc.html#6229" class="Function"
      >x</a
      ><a name="6497" class="Symbol"
      >))</a
      >
{% endraw %}</pre>

$$\text{idBB} = \lambda x:bool\rightarrow bool. x$$.

<pre class="Agda">{% raw %}
<a name="6579" href="Stlc.html#6579" class="Function"
      >idBB</a
      ><a name="6583"
      > </a
      ><a name="6584" class="Symbol"
      >=</a
      ><a name="6585"
      > </a
      ><a name="6586" class="Symbol"
      >(</a
      ><a name="6587" href="Stlc.html#5698" class="InductiveConstructor"
      >abs</a
      ><a name="6590"
      > </a
      ><a name="6591" href="Stlc.html#6229" class="Function"
      >x</a
      ><a name="6592"
      > </a
      ><a name="6593" class="Symbol"
      >(</a
      ><a name="6594" href="Stlc.html#5482" class="InductiveConstructor"
      >bool</a
      ><a name="6598"
      > </a
      ><a name="6599" href="Stlc.html#5496" class="InductiveConstructor Operator"
      >&#8658;</a
      ><a name="6600"
      > </a
      ><a name="6601" href="Stlc.html#5482" class="InductiveConstructor"
      >bool</a
      ><a name="6605" class="Symbol"
      >)</a
      ><a name="6606"
      > </a
      ><a name="6607" class="Symbol"
      >(</a
      ><a name="6608" href="Stlc.html#5649" class="InductiveConstructor"
      >var</a
      ><a name="6611"
      > </a
      ><a name="6612" href="Stlc.html#6229" class="Function"
      >x</a
      ><a name="6613" class="Symbol"
      >))</a
      >
{% endraw %}</pre>

$$\text{idBBBB} = \lambda x:(bool\rightarrow bool)\rightarrow (bool\rightarrow bool). x$$.

<pre class="Agda">{% raw %}
<a name="6733" href="Stlc.html#6733" class="Function"
      >idBBBB</a
      ><a name="6739"
      > </a
      ><a name="6740" class="Symbol"
      >=</a
      ><a name="6741"
      > </a
      ><a name="6742" class="Symbol"
      >(</a
      ><a name="6743" href="Stlc.html#5698" class="InductiveConstructor"
      >abs</a
      ><a name="6746"
      > </a
      ><a name="6747" href="Stlc.html#6229" class="Function"
      >x</a
      ><a name="6748"
      > </a
      ><a name="6749" class="Symbol"
      >((</a
      ><a name="6751" href="Stlc.html#5482" class="InductiveConstructor"
      >bool</a
      ><a name="6755"
      > </a
      ><a name="6756" href="Stlc.html#5496" class="InductiveConstructor Operator"
      >&#8658;</a
      ><a name="6757"
      > </a
      ><a name="6758" href="Stlc.html#5482" class="InductiveConstructor"
      >bool</a
      ><a name="6762" class="Symbol"
      >)</a
      ><a name="6763"
      > </a
      ><a name="6764" href="Stlc.html#5496" class="InductiveConstructor Operator"
      >&#8658;</a
      ><a name="6765"
      > </a
      ><a name="6766" class="Symbol"
      >(</a
      ><a name="6767" href="Stlc.html#5482" class="InductiveConstructor"
      >bool</a
      ><a name="6771"
      > </a
      ><a name="6772" href="Stlc.html#5496" class="InductiveConstructor Operator"
      >&#8658;</a
      ><a name="6773"
      > </a
      ><a name="6774" href="Stlc.html#5482" class="InductiveConstructor"
      >bool</a
      ><a name="6778" class="Symbol"
      >))</a
      ><a name="6780"
      > </a
      ><a name="6781" class="Symbol"
      >(</a
      ><a name="6782" href="Stlc.html#5649" class="InductiveConstructor"
      >var</a
      ><a name="6785"
      > </a
      ><a name="6786" href="Stlc.html#6229" class="Function"
      >x</a
      ><a name="6787" class="Symbol"
      >))</a
      >
{% endraw %}</pre>

$$\text{k} = \lambda x:bool. \lambda y:bool. x$$.

<pre class="Agda">{% raw %}
<a name="6866" href="Stlc.html#6866" class="Function"
      >k</a
      ><a name="6867"
      > </a
      ><a name="6868" class="Symbol"
      >=</a
      ><a name="6869"
      > </a
      ><a name="6870" class="Symbol"
      >(</a
      ><a name="6871" href="Stlc.html#5698" class="InductiveConstructor"
      >abs</a
      ><a name="6874"
      > </a
      ><a name="6875" href="Stlc.html#6229" class="Function"
      >x</a
      ><a name="6876"
      > </a
      ><a name="6877" href="Stlc.html#5482" class="InductiveConstructor"
      >bool</a
      ><a name="6881"
      > </a
      ><a name="6882" class="Symbol"
      >(</a
      ><a name="6883" href="Stlc.html#5698" class="InductiveConstructor"
      >abs</a
      ><a name="6886"
      > </a
      ><a name="6887" href="Stlc.html#6238" class="Function"
      >y</a
      ><a name="6888"
      > </a
      ><a name="6889" href="Stlc.html#5482" class="InductiveConstructor"
      >bool</a
      ><a name="6893"
      > </a
      ><a name="6894" class="Symbol"
      >(</a
      ><a name="6895" href="Stlc.html#5649" class="InductiveConstructor"
      >var</a
      ><a name="6898"
      > </a
      ><a name="6899" href="Stlc.html#6229" class="Function"
      >x</a
      ><a name="6900" class="Symbol"
      >)))</a
      >
{% endraw %}</pre>

$$\text{notB} = \lambda x:bool. \text{if }x\text{ then }false\text{ else }true$$.

<pre class="Agda">{% raw %}
<a name="7012" href="Stlc.html#7012" class="Function"
      >notB</a
      ><a name="7016"
      > </a
      ><a name="7017" class="Symbol"
      >=</a
      ><a name="7018"
      > </a
      ><a name="7019" class="Symbol"
      >(</a
      ><a name="7020" href="Stlc.html#5698" class="InductiveConstructor"
      >abs</a
      ><a name="7023"
      > </a
      ><a name="7024" href="Stlc.html#6229" class="Function"
      >x</a
      ><a name="7025"
      > </a
      ><a name="7026" href="Stlc.html#5482" class="InductiveConstructor"
      >bool</a
      ><a name="7030"
      > </a
      ><a name="7031" class="Symbol"
      >(</a
      ><a name="7032" href="Stlc.html#5762" class="InductiveConstructor Operator"
      >if</a
      ><a name="7034"
      > </a
      ><a name="7035" class="Symbol"
      >(</a
      ><a name="7036" href="Stlc.html#5649" class="InductiveConstructor"
      >var</a
      ><a name="7039"
      > </a
      ><a name="7040" href="Stlc.html#6229" class="Function"
      >x</a
      ><a name="7041" class="Symbol"
      >)</a
      ><a name="7042"
      > </a
      ><a name="7043" href="Stlc.html#5762" class="InductiveConstructor Operator"
      >then</a
      ><a name="7047"
      > </a
      ><a name="7048" href="Stlc.html#5747" class="InductiveConstructor"
      >false</a
      ><a name="7053"
      > </a
      ><a name="7054" href="Stlc.html#5762" class="InductiveConstructor Operator"
      >else</a
      ><a name="7058"
      > </a
      ><a name="7059" href="Stlc.html#5732" class="InductiveConstructor"
      >true</a
      ><a name="7063" class="Symbol"
      >))</a
      >
{% endraw %}</pre>

<div class="hidden">
<pre class="Agda">{% raw %}
<a name="7112" class="Symbol"
      >{-#</a
      ><a name="7115"
      > </a
      ><a name="7116" class="Keyword"
      >DISPLAY</a
      ><a name="7123"
      > </a
      ><a name="7124" href="Stlc.html#5698" class="InductiveConstructor"
      >abs</a
      ><a name="7127"
      > 0 </a
      ><a name="7130" href="Stlc.html#5482" class="InductiveConstructor"
      >bool</a
      ><a name="7134"
      > (</a
      ><a name="7136" href="Stlc.html#5649" class="InductiveConstructor"
      >var</a
      ><a name="7139"
      > 0) = </a
      ><a name="7145" href="Stlc.html#6473" class="Function"
      >idB</a
      ><a name="7148"
      > </a
      ><a name="7149" class="Symbol"
      >#-}</a
      ><a name="7152"
      >
</a
      ><a name="7153" class="Symbol"
      >{-#</a
      ><a name="7156"
      > </a
      ><a name="7157" class="Keyword"
      >DISPLAY</a
      ><a name="7164"
      > </a
      ><a name="7165" href="Stlc.html#5698" class="InductiveConstructor"
      >abs</a
      ><a name="7168"
      > 0 (</a
      ><a name="7172" href="Stlc.html#5482" class="InductiveConstructor"
      >bool</a
      ><a name="7176"
      > </a
      ><a name="7177" href="Stlc.html#5496" class="InductiveConstructor Operator"
      >&#8658;</a
      ><a name="7178"
      > </a
      ><a name="7179" href="Stlc.html#5482" class="InductiveConstructor"
      >bool</a
      ><a name="7183"
      >) (</a
      ><a name="7186" href="Stlc.html#5649" class="InductiveConstructor"
      >var</a
      ><a name="7189"
      > 0) = </a
      ><a name="7195" href="Stlc.html#6579" class="Function"
      >idBB</a
      ><a name="7199"
      > </a
      ><a name="7200" class="Symbol"
      >#-}</a
      ><a name="7203"
      >
</a
      ><a name="7204" class="Symbol"
      >{-#</a
      ><a name="7207"
      > </a
      ><a name="7208" class="Keyword"
      >DISPLAY</a
      ><a name="7215"
      > </a
      ><a name="7216" href="Stlc.html#5698" class="InductiveConstructor"
      >abs</a
      ><a name="7219"
      > 0 ((</a
      ><a name="7224" href="Stlc.html#5482" class="InductiveConstructor"
      >bool</a
      ><a name="7228"
      > </a
      ><a name="7229" href="Stlc.html#5496" class="InductiveConstructor Operator"
      >&#8658;</a
      ><a name="7230"
      > </a
      ><a name="7231" href="Stlc.html#5482" class="InductiveConstructor"
      >bool</a
      ><a name="7235"
      >) </a
      ><a name="7237" href="Stlc.html#5496" class="InductiveConstructor Operator"
      >&#8658;</a
      ><a name="7238"
      > (</a
      ><a name="7240" href="Stlc.html#5482" class="InductiveConstructor"
      >bool</a
      ><a name="7244"
      > </a
      ><a name="7245" href="Stlc.html#5496" class="InductiveConstructor Operator"
      >&#8658;</a
      ><a name="7246"
      > </a
      ><a name="7247" href="Stlc.html#5482" class="InductiveConstructor"
      >bool</a
      ><a name="7251"
      >)) (</a
      ><a name="7255" href="Stlc.html#5649" class="InductiveConstructor"
      >var</a
      ><a name="7258"
      > 0) = </a
      ><a name="7264" href="Stlc.html#6733" class="Function"
      >idBBBB</a
      ><a name="7270"
      > </a
      ><a name="7271" class="Symbol"
      >#-}</a
      ><a name="7274"
      >
</a
      ><a name="7275" class="Symbol"
      >{-#</a
      ><a name="7278"
      > </a
      ><a name="7279" class="Keyword"
      >DISPLAY</a
      ><a name="7286"
      > </a
      ><a name="7287" href="Stlc.html#5698" class="InductiveConstructor"
      >abs</a
      ><a name="7290"
      > 0 </a
      ><a name="7293" href="Stlc.html#5482" class="InductiveConstructor"
      >bool</a
      ><a name="7297"
      > (</a
      ><a name="7299" href="Stlc.html#5698" class="InductiveConstructor"
      >abs</a
      ><a name="7302"
      > </a
      ><a name="7303" href="Stlc.html#7303" class="Bound"
      >y</a
      ><a name="7304"
      > </a
      ><a name="7305" href="Stlc.html#5482" class="InductiveConstructor"
      >bool</a
      ><a name="7309"
      > (</a
      ><a name="7311" href="Stlc.html#5649" class="InductiveConstructor"
      >var</a
      ><a name="7314"
      > 0)) = </a
      ><a name="7321" href="Stlc.html#6866" class="Function"
      >k</a
      ><a name="7322"
      > </a
      ><a name="7323" class="Symbol"
      >#-}</a
      ><a name="7326"
      >
</a
      ><a name="7327" class="Symbol"
      >{-#</a
      ><a name="7330"
      > </a
      ><a name="7331" class="Keyword"
      >DISPLAY</a
      ><a name="7338"
      > </a
      ><a name="7339" href="Stlc.html#5698" class="InductiveConstructor"
      >abs</a
      ><a name="7342"
      > 0 </a
      ><a name="7345" href="Stlc.html#5482" class="InductiveConstructor"
      >bool</a
      ><a name="7349"
      > (</a
      ><a name="7351" href="Stlc.html#5762" class="InductiveConstructor Operator"
      >if</a
      ><a name="7353"
      > (</a
      ><a name="7355" href="Stlc.html#5649" class="InductiveConstructor"
      >var</a
      ><a name="7358"
      > 0) </a
      ><a name="7362" href="Stlc.html#5762" class="InductiveConstructor Operator"
      >then</a
      ><a name="7366"
      > </a
      ><a name="7367" href="Stlc.html#5747" class="InductiveConstructor"
      >false</a
      ><a name="7372"
      > </a
      ><a name="7373" href="Stlc.html#5762" class="InductiveConstructor Operator"
      >else</a
      ><a name="7377"
      > </a
      ><a name="7378" href="Stlc.html#5732" class="InductiveConstructor"
      >true</a
      ><a name="7382"
      >) = </a
      ><a name="7386" href="Stlc.html#7012" class="Function"
      >notB</a
      ><a name="7390"
      > </a
      ><a name="7391" class="Symbol"
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
<a name="8630" href="Stlc.html#8630" class="Function Operator"
      >test_normalizeUnderLambda</a
      ><a name="8655"
      > </a
      ><a name="8656" class="Symbol"
      >:</a
      ><a name="8657"
      > </a
      ><a name="8658" class="Symbol"
      >(&#955;</a
      ><a name="8660"
      > </a
      ><a name="8661" class="Symbol"
      >(</a
      ><a name="8662" href="Stlc.html#8662" class="Bound"
      >x</a
      ><a name="8663"
      > </a
      ><a name="8664" class="Symbol"
      >:</a
      ><a name="8665"
      > </a
      ><a name="8666" href="Agda.Builtin.Nat.html#97" class="Datatype"
      >&#8469;</a
      ><a name="8667" class="Symbol"
      >)</a
      ><a name="8668"
      > </a
      ><a name="8669" class="Symbol"
      >&#8594;</a
      ><a name="8670"
      > </a
      ><a name="8671" class="Number"
      >3</a
      ><a name="8672"
      > </a
      ><a name="8673" href="Agda.Builtin.Nat.html#230" class="Primitive Operator"
      >+</a
      ><a name="8674"
      > </a
      ><a name="8675" class="Number"
      >4</a
      ><a name="8676" class="Symbol"
      >)</a
      ><a name="8677"
      > </a
      ><a name="8678" href="Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="8679"
      > </a
      ><a name="8680" class="Symbol"
      >(&#955;</a
      ><a name="8682"
      > </a
      ><a name="8683" class="Symbol"
      >(</a
      ><a name="8684" href="Stlc.html#8684" class="Bound"
      >x</a
      ><a name="8685"
      > </a
      ><a name="8686" class="Symbol"
      >:</a
      ><a name="8687"
      > </a
      ><a name="8688" href="Agda.Builtin.Nat.html#97" class="Datatype"
      >&#8469;</a
      ><a name="8689" class="Symbol"
      >)</a
      ><a name="8690"
      > </a
      ><a name="8691" class="Symbol"
      >&#8594;</a
      ><a name="8692"
      > </a
      ><a name="8693" class="Number"
      >7</a
      ><a name="8694" class="Symbol"
      >)</a
      ><a name="8695"
      >
</a
      ><a name="8696" href="Stlc.html#8630" class="Function Operator"
      >test_normalizeUnderLambda</a
      ><a name="8721"
      > </a
      ><a name="8722" class="Symbol"
      >=</a
      ><a name="8723"
      > </a
      ><a name="8724" href="Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      >
{% endraw %}</pre>

Most real-world functional programming languages make the second
choice---reduction of a function's body only begins when the
function is actually applied to an argument.  We also make the
second choice here.

<pre class="Agda">{% raw %}
<a name="8964" class="Keyword"
      >data</a
      ><a name="8968"
      > </a
      ><a name="8969" href="Stlc.html#8969" class="Datatype"
      >Value</a
      ><a name="8974"
      > </a
      ><a name="8975" class="Symbol"
      >:</a
      ><a name="8976"
      > </a
      ><a name="8977" href="Stlc.html#5630" class="Datatype"
      >Term</a
      ><a name="8981"
      > </a
      ><a name="8982" class="Symbol"
      >&#8594;</a
      ><a name="8983"
      > </a
      ><a name="8984" class="PrimitiveType"
      >Set</a
      ><a name="8987"
      > </a
      ><a name="8988" class="Keyword"
      >where</a
      ><a name="8993"
      >
  </a
      ><a name="8996" href="Stlc.html#8996" class="InductiveConstructor"
      >abs</a
      ><a name="8999"
      >   </a
      ><a name="9002" class="Symbol"
      >:</a
      ><a name="9003"
      > </a
      ><a name="9004" class="Symbol"
      >&#8704;</a
      ><a name="9005"
      > </a
      ><a name="9022" class="Symbol"
      >&#8594;</a
      ><a name="9023"
      > </a
      ><a name="9024" href="Stlc.html#8969" class="Datatype"
      >Value</a
      ><a name="9029"
      > </a
      ><a name="9030" class="Symbol"
      >(</a
      ><a name="9031" href="Stlc.html#5698" class="InductiveConstructor"
      >abs</a
      ><a name="9034"
      > </a
      ><a name="9035" href="Stlc.html#9007" class="Bound"
      >x</a
      ><a name="9036"
      > </a
      ><a name="9037" href="Stlc.html#9009" class="Bound"
      >A</a
      ><a name="9038"
      > </a
      ><a name="9039" href="Stlc.html#9011" class="Bound"
      >t</a
      ><a name="9040" class="Symbol"
      >)</a
      ><a name="9041"
      >
  </a
      ><a name="9044" href="Stlc.html#9044" class="InductiveConstructor"
      >true</a
      ><a name="9048"
      >  </a
      ><a name="9050" class="Symbol"
      >:</a
      ><a name="9051"
      > </a
      ><a name="9052" href="Stlc.html#8969" class="Datatype"
      >Value</a
      ><a name="9057"
      > </a
      ><a name="9058" href="Stlc.html#5732" class="InductiveConstructor"
      >true</a
      ><a name="9062"
      >
  </a
      ><a name="9065" href="Stlc.html#9065" class="InductiveConstructor"
      >false</a
      ><a name="9070"
      > </a
      ><a name="9071" class="Symbol"
      >:</a
      ><a name="9072"
      > </a
      ><a name="9073" href="Stlc.html#8969" class="Datatype"
      >Value</a
      ><a name="9078"
      > </a
      ><a name="9079" href="Stlc.html#5747" class="InductiveConstructor"
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
<a name="12189" href="Stlc.html#12189" class="Function Operator"
      >[_:=_]_</a
      ><a name="12196"
      > </a
      ><a name="12197" class="Symbol"
      >:</a
      ><a name="12198"
      > </a
      ><a name="12199" href="Maps.html#2275" class="Datatype"
      >Id</a
      ><a name="12201"
      > </a
      ><a name="12202" class="Symbol"
      >-&gt;</a
      ><a name="12204"
      > </a
      ><a name="12205" href="Stlc.html#5630" class="Datatype"
      >Term</a
      ><a name="12209"
      > </a
      ><a name="12210" class="Symbol"
      >-&gt;</a
      ><a name="12212"
      > </a
      ><a name="12213" href="Stlc.html#5630" class="Datatype"
      >Term</a
      ><a name="12217"
      > </a
      ><a name="12218" class="Symbol"
      >-&gt;</a
      ><a name="12220"
      > </a
      ><a name="12221" href="Stlc.html#5630" class="Datatype"
      >Term</a
      ><a name="12225"
      >
</a
      ><a name="12226" href="Stlc.html#12189" class="Function Operator"
      >[</a
      ><a name="12227"
      > </a
      ><a name="12228" href="Stlc.html#12228" class="Bound"
      >x</a
      ><a name="12229"
      > </a
      ><a name="12230" href="Stlc.html#12189" class="Function Operator"
      >:=</a
      ><a name="12232"
      > </a
      ><a name="12233" href="Stlc.html#12233" class="Bound"
      >v</a
      ><a name="12234"
      > </a
      ><a name="12235" href="Stlc.html#12189" class="Function Operator"
      >]</a
      ><a name="12236"
      > </a
      ><a name="12237" class="Symbol"
      >(</a
      ><a name="12238" href="Stlc.html#5649" class="InductiveConstructor"
      >var</a
      ><a name="12241"
      > </a
      ><a name="12242" href="Stlc.html#12242" class="Bound"
      >y</a
      ><a name="12243" class="Symbol"
      >)</a
      ><a name="12244"
      > </a
      ><a name="12245" class="Keyword"
      >with</a
      ><a name="12249"
      > </a
      ><a name="12250" href="Stlc.html#12228" class="Bound"
      >x</a
      ><a name="12251"
      > </a
      ><a name="12252" href="Maps.html#2329" class="Function Operator"
      >&#8799;</a
      ><a name="12253"
      > </a
      ><a name="12254" href="Stlc.html#12242" class="Bound"
      >y</a
      ><a name="12255"
      >
</a
      ><a name="12256" class="Symbol"
      >...</a
      ><a name="12259"
      > </a
      ><a name="12260" class="Symbol"
      >|</a
      ><a name="12261"
      > </a
      ><a name="12262" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#520" class="InductiveConstructor"
      >yes</a
      ><a name="12265"
      > </a
      ><a name="12266" href="Stlc.html#12266" class="Bound"
      >x=y</a
      ><a name="12269"
      > </a
      ><a name="12270" class="Symbol"
      >=</a
      ><a name="12271"
      > </a
      ><a name="12272" href="Stlc.html#12233" class="Bound"
      >v</a
      ><a name="12273"
      >
</a
      ><a name="12274" class="Symbol"
      >...</a
      ><a name="12277"
      > </a
      ><a name="12278" class="Symbol"
      >|</a
      ><a name="12279"
      > </a
      ><a name="12280" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#547" class="InductiveConstructor"
      >no</a
      ><a name="12282"
      >  </a
      ><a name="12284" href="Stlc.html#12284" class="Bound"
      >x&#8800;y</a
      ><a name="12287"
      > </a
      ><a name="12288" class="Symbol"
      >=</a
      ><a name="12289"
      > </a
      ><a name="12290" href="Stlc.html#5649" class="InductiveConstructor"
      >var</a
      ><a name="12293"
      > </a
      ><a name="12294" href="Stlc.html#12242" class="Bound"
      >y</a
      ><a name="12295"
      >
</a
      ><a name="12296" href="Stlc.html#12189" class="Function Operator"
      >[</a
      ><a name="12297"
      > </a
      ><a name="12298" href="Stlc.html#12298" class="Bound"
      >x</a
      ><a name="12299"
      > </a
      ><a name="12300" href="Stlc.html#12189" class="Function Operator"
      >:=</a
      ><a name="12302"
      > </a
      ><a name="12303" href="Stlc.html#12303" class="Bound"
      >v</a
      ><a name="12304"
      > </a
      ><a name="12305" href="Stlc.html#12189" class="Function Operator"
      >]</a
      ><a name="12306"
      > </a
      ><a name="12307" class="Symbol"
      >(</a
      ><a name="12308" href="Stlc.html#5669" class="InductiveConstructor"
      >app</a
      ><a name="12311"
      > </a
      ><a name="12312" href="Stlc.html#12312" class="Bound"
      >s</a
      ><a name="12313"
      > </a
      ><a name="12314" href="Stlc.html#12314" class="Bound"
      >t</a
      ><a name="12315" class="Symbol"
      >)</a
      ><a name="12316"
      > </a
      ><a name="12317" class="Symbol"
      >=</a
      ><a name="12318"
      > </a
      ><a name="12319" href="Stlc.html#5669" class="InductiveConstructor"
      >app</a
      ><a name="12322"
      > </a
      ><a name="12323" class="Symbol"
      >(</a
      ><a name="12324" href="Stlc.html#12189" class="Function Operator"
      >[</a
      ><a name="12325"
      > </a
      ><a name="12326" href="Stlc.html#12298" class="Bound"
      >x</a
      ><a name="12327"
      > </a
      ><a name="12328" href="Stlc.html#12189" class="Function Operator"
      >:=</a
      ><a name="12330"
      > </a
      ><a name="12331" href="Stlc.html#12303" class="Bound"
      >v</a
      ><a name="12332"
      > </a
      ><a name="12333" href="Stlc.html#12189" class="Function Operator"
      >]</a
      ><a name="12334"
      > </a
      ><a name="12335" href="Stlc.html#12312" class="Bound"
      >s</a
      ><a name="12336" class="Symbol"
      >)</a
      ><a name="12337"
      > </a
      ><a name="12338" class="Symbol"
      >(</a
      ><a name="12339" href="Stlc.html#12189" class="Function Operator"
      >[</a
      ><a name="12340"
      > </a
      ><a name="12341" href="Stlc.html#12298" class="Bound"
      >x</a
      ><a name="12342"
      > </a
      ><a name="12343" href="Stlc.html#12189" class="Function Operator"
      >:=</a
      ><a name="12345"
      > </a
      ><a name="12346" href="Stlc.html#12303" class="Bound"
      >v</a
      ><a name="12347"
      > </a
      ><a name="12348" href="Stlc.html#12189" class="Function Operator"
      >]</a
      ><a name="12349"
      > </a
      ><a name="12350" href="Stlc.html#12314" class="Bound"
      >t</a
      ><a name="12351" class="Symbol"
      >)</a
      ><a name="12352"
      >
</a
      ><a name="12353" href="Stlc.html#12189" class="Function Operator"
      >[</a
      ><a name="12354"
      > </a
      ><a name="12355" href="Stlc.html#12355" class="Bound"
      >x</a
      ><a name="12356"
      > </a
      ><a name="12357" href="Stlc.html#12189" class="Function Operator"
      >:=</a
      ><a name="12359"
      > </a
      ><a name="12360" href="Stlc.html#12360" class="Bound"
      >v</a
      ><a name="12361"
      > </a
      ><a name="12362" href="Stlc.html#12189" class="Function Operator"
      >]</a
      ><a name="12363"
      > </a
      ><a name="12364" class="Symbol"
      >(</a
      ><a name="12365" href="Stlc.html#5698" class="InductiveConstructor"
      >abs</a
      ><a name="12368"
      > </a
      ><a name="12369" href="Stlc.html#12369" class="Bound"
      >y</a
      ><a name="12370"
      > </a
      ><a name="12371" href="Stlc.html#12371" class="Bound"
      >A</a
      ><a name="12372"
      > </a
      ><a name="12373" href="Stlc.html#12373" class="Bound"
      >t</a
      ><a name="12374" class="Symbol"
      >)</a
      ><a name="12375"
      > </a
      ><a name="12376" class="Keyword"
      >with</a
      ><a name="12380"
      > </a
      ><a name="12381" href="Stlc.html#12355" class="Bound"
      >x</a
      ><a name="12382"
      > </a
      ><a name="12383" href="Maps.html#2329" class="Function Operator"
      >&#8799;</a
      ><a name="12384"
      > </a
      ><a name="12385" href="Stlc.html#12369" class="Bound"
      >y</a
      ><a name="12386"
      >
</a
      ><a name="12387" class="Symbol"
      >...</a
      ><a name="12390"
      > </a
      ><a name="12391" class="Symbol"
      >|</a
      ><a name="12392"
      > </a
      ><a name="12393" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#520" class="InductiveConstructor"
      >yes</a
      ><a name="12396"
      > </a
      ><a name="12397" href="Stlc.html#12397" class="Bound"
      >x=y</a
      ><a name="12400"
      > </a
      ><a name="12401" class="Symbol"
      >=</a
      ><a name="12402"
      > </a
      ><a name="12403" href="Stlc.html#5698" class="InductiveConstructor"
      >abs</a
      ><a name="12406"
      > </a
      ><a name="12407" href="Stlc.html#12369" class="Bound"
      >y</a
      ><a name="12408"
      > </a
      ><a name="12409" href="Stlc.html#12371" class="Bound"
      >A</a
      ><a name="12410"
      > </a
      ><a name="12411" href="Stlc.html#12373" class="Bound"
      >t</a
      ><a name="12412"
      >
</a
      ><a name="12413" class="Symbol"
      >...</a
      ><a name="12416"
      > </a
      ><a name="12417" class="Symbol"
      >|</a
      ><a name="12418"
      > </a
      ><a name="12419" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#547" class="InductiveConstructor"
      >no</a
      ><a name="12421"
      >  </a
      ><a name="12423" href="Stlc.html#12423" class="Bound"
      >x&#8800;y</a
      ><a name="12426"
      > </a
      ><a name="12427" class="Symbol"
      >=</a
      ><a name="12428"
      > </a
      ><a name="12429" href="Stlc.html#5698" class="InductiveConstructor"
      >abs</a
      ><a name="12432"
      > </a
      ><a name="12433" href="Stlc.html#12369" class="Bound"
      >y</a
      ><a name="12434"
      > </a
      ><a name="12435" href="Stlc.html#12371" class="Bound"
      >A</a
      ><a name="12436"
      > </a
      ><a name="12437" class="Symbol"
      >(</a
      ><a name="12438" href="Stlc.html#12189" class="Function Operator"
      >[</a
      ><a name="12439"
      > </a
      ><a name="12440" href="Stlc.html#12355" class="Bound"
      >x</a
      ><a name="12441"
      > </a
      ><a name="12442" href="Stlc.html#12189" class="Function Operator"
      >:=</a
      ><a name="12444"
      > </a
      ><a name="12445" href="Stlc.html#12360" class="Bound"
      >v</a
      ><a name="12446"
      > </a
      ><a name="12447" href="Stlc.html#12189" class="Function Operator"
      >]</a
      ><a name="12448"
      > </a
      ><a name="12449" href="Stlc.html#12373" class="Bound"
      >t</a
      ><a name="12450" class="Symbol"
      >)</a
      ><a name="12451"
      >
</a
      ><a name="12452" href="Stlc.html#12189" class="Function Operator"
      >[</a
      ><a name="12453"
      > </a
      ><a name="12454" href="Stlc.html#12454" class="Bound"
      >x</a
      ><a name="12455"
      > </a
      ><a name="12456" href="Stlc.html#12189" class="Function Operator"
      >:=</a
      ><a name="12458"
      > </a
      ><a name="12459" href="Stlc.html#12459" class="Bound"
      >v</a
      ><a name="12460"
      > </a
      ><a name="12461" href="Stlc.html#12189" class="Function Operator"
      >]</a
      ><a name="12462"
      > </a
      ><a name="12463" href="Stlc.html#5732" class="InductiveConstructor"
      >true</a
      ><a name="12467"
      >  </a
      ><a name="12469" class="Symbol"
      >=</a
      ><a name="12470"
      > </a
      ><a name="12471" href="Stlc.html#5732" class="InductiveConstructor"
      >true</a
      ><a name="12475"
      >
</a
      ><a name="12476" href="Stlc.html#12189" class="Function Operator"
      >[</a
      ><a name="12477"
      > </a
      ><a name="12478" href="Stlc.html#12478" class="Bound"
      >x</a
      ><a name="12479"
      > </a
      ><a name="12480" href="Stlc.html#12189" class="Function Operator"
      >:=</a
      ><a name="12482"
      > </a
      ><a name="12483" href="Stlc.html#12483" class="Bound"
      >v</a
      ><a name="12484"
      > </a
      ><a name="12485" href="Stlc.html#12189" class="Function Operator"
      >]</a
      ><a name="12486"
      > </a
      ><a name="12487" href="Stlc.html#5747" class="InductiveConstructor"
      >false</a
      ><a name="12492"
      > </a
      ><a name="12493" class="Symbol"
      >=</a
      ><a name="12494"
      > </a
      ><a name="12495" href="Stlc.html#5747" class="InductiveConstructor"
      >false</a
      ><a name="12500"
      >
</a
      ><a name="12501" href="Stlc.html#12189" class="Function Operator"
      >[</a
      ><a name="12502"
      > </a
      ><a name="12503" href="Stlc.html#12503" class="Bound"
      >x</a
      ><a name="12504"
      > </a
      ><a name="12505" href="Stlc.html#12189" class="Function Operator"
      >:=</a
      ><a name="12507"
      > </a
      ><a name="12508" href="Stlc.html#12508" class="Bound"
      >v</a
      ><a name="12509"
      > </a
      ><a name="12510" href="Stlc.html#12189" class="Function Operator"
      >]</a
      ><a name="12511"
      > </a
      ><a name="12512" class="Symbol"
      >(</a
      ><a name="12513" href="Stlc.html#5762" class="InductiveConstructor Operator"
      >if</a
      ><a name="12515"
      > </a
      ><a name="12516" href="Stlc.html#12516" class="Bound"
      >s</a
      ><a name="12517"
      > </a
      ><a name="12518" href="Stlc.html#5762" class="InductiveConstructor Operator"
      >then</a
      ><a name="12522"
      > </a
      ><a name="12523" href="Stlc.html#12523" class="Bound"
      >t</a
      ><a name="12524"
      > </a
      ><a name="12525" href="Stlc.html#5762" class="InductiveConstructor Operator"
      >else</a
      ><a name="12529"
      > </a
      ><a name="12530" href="Stlc.html#12530" class="Bound"
      >u</a
      ><a name="12531" class="Symbol"
      >)</a
      ><a name="12532"
      > </a
      ><a name="12533" class="Symbol"
      >=</a
      ><a name="12534"
      >
  </a
      ><a name="12537" href="Stlc.html#5762" class="InductiveConstructor Operator"
      >if</a
      ><a name="12539"
      > </a
      ><a name="12540" href="Stlc.html#12189" class="Function Operator"
      >[</a
      ><a name="12541"
      > </a
      ><a name="12542" href="Stlc.html#12503" class="Bound"
      >x</a
      ><a name="12543"
      > </a
      ><a name="12544" href="Stlc.html#12189" class="Function Operator"
      >:=</a
      ><a name="12546"
      > </a
      ><a name="12547" href="Stlc.html#12508" class="Bound"
      >v</a
      ><a name="12548"
      > </a
      ><a name="12549" href="Stlc.html#12189" class="Function Operator"
      >]</a
      ><a name="12550"
      > </a
      ><a name="12551" href="Stlc.html#12516" class="Bound"
      >s</a
      ><a name="12552"
      > </a
      ><a name="12553" href="Stlc.html#5762" class="InductiveConstructor Operator"
      >then</a
      ><a name="12557"
      > </a
      ><a name="12558" href="Stlc.html#12189" class="Function Operator"
      >[</a
      ><a name="12559"
      > </a
      ><a name="12560" href="Stlc.html#12503" class="Bound"
      >x</a
      ><a name="12561"
      > </a
      ><a name="12562" href="Stlc.html#12189" class="Function Operator"
      >:=</a
      ><a name="12564"
      > </a
      ><a name="12565" href="Stlc.html#12508" class="Bound"
      >v</a
      ><a name="12566"
      > </a
      ><a name="12567" href="Stlc.html#12189" class="Function Operator"
      >]</a
      ><a name="12568"
      > </a
      ><a name="12569" href="Stlc.html#12523" class="Bound"
      >t</a
      ><a name="12570"
      > </a
      ><a name="12571" href="Stlc.html#5762" class="InductiveConstructor Operator"
      >else</a
      ><a name="12575"
      >  </a
      ><a name="12577" href="Stlc.html#12189" class="Function Operator"
      >[</a
      ><a name="12578"
      > </a
      ><a name="12579" href="Stlc.html#12503" class="Bound"
      >x</a
      ><a name="12580"
      > </a
      ><a name="12581" href="Stlc.html#12189" class="Function Operator"
      >:=</a
      ><a name="12583"
      > </a
      ><a name="12584" href="Stlc.html#12508" class="Bound"
      >v</a
      ><a name="12585"
      > </a
      ><a name="12586" href="Stlc.html#12189" class="Function Operator"
      >]</a
      ><a name="12587"
      > </a
      ><a name="12588" href="Stlc.html#12530" class="Bound"
      >u</a
      >
{% endraw %}</pre>

<div class="hidden">
<pre class="Agda">{% raw %}
<a name="12636" class="Keyword"
      >infix</a
      ><a name="12641"
      > </a
      ><a name="12642" class="Number"
      >9</a
      ><a name="12643"
      > </a
      ><a name="12644" href="Stlc.html#12189" class="Function Operator"
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
<a name="13580" class="Keyword"
      >data</a
      ><a name="13584"
      > </a
      ><a name="13585" href="Stlc.html#13585" class="Datatype Operator"
      >[_:=_]_==&gt;_</a
      ><a name="13596"
      > </a
      ><a name="13597" class="Symbol"
      >(</a
      ><a name="13598" href="Stlc.html#13598" class="Bound"
      >x</a
      ><a name="13599"
      > </a
      ><a name="13600" class="Symbol"
      >:</a
      ><a name="13601"
      > </a
      ><a name="13602" href="Maps.html#2275" class="Datatype"
      >Id</a
      ><a name="13604" class="Symbol"
      >)</a
      ><a name="13605"
      > </a
      ><a name="13606" class="Symbol"
      >(</a
      ><a name="13607" href="Stlc.html#13607" class="Bound"
      >s</a
      ><a name="13608"
      > </a
      ><a name="13609" class="Symbol"
      >:</a
      ><a name="13610"
      > </a
      ><a name="13611" href="Stlc.html#5630" class="Datatype"
      >Term</a
      ><a name="13615" class="Symbol"
      >)</a
      ><a name="13616"
      > </a
      ><a name="13617" class="Symbol"
      >:</a
      ><a name="13618"
      > </a
      ><a name="13619" href="Stlc.html#5630" class="Datatype"
      >Term</a
      ><a name="13623"
      > </a
      ><a name="13624" class="Symbol"
      >-&gt;</a
      ><a name="13626"
      > </a
      ><a name="13627" href="Stlc.html#5630" class="Datatype"
      >Term</a
      ><a name="13631"
      > </a
      ><a name="13632" class="Symbol"
      >-&gt;</a
      ><a name="13634"
      > </a
      ><a name="13635" class="PrimitiveType"
      >Set</a
      ><a name="13638"
      > </a
      ><a name="13639" class="Keyword"
      >where</a
      ><a name="13644"
      >
  </a
      ><a name="13647" href="Stlc.html#13647" class="InductiveConstructor"
      >var1</a
      ><a name="13651"
      > </a
      ><a name="13652" class="Symbol"
      >:</a
      ><a name="13653"
      > </a
      ><a name="13654" href="Stlc.html#13585" class="Datatype Operator"
      >[</a
      ><a name="13655"
      > </a
      ><a name="13656" href="Stlc.html#13598" class="Bound"
      >x</a
      ><a name="13657"
      > </a
      ><a name="13658" href="Stlc.html#13585" class="Datatype Operator"
      >:=</a
      ><a name="13660"
      > </a
      ><a name="13661" href="Stlc.html#13607" class="Bound"
      >s</a
      ><a name="13662"
      > </a
      ><a name="13663" href="Stlc.html#13585" class="Datatype Operator"
      >]</a
      ><a name="13664"
      > </a
      ><a name="13665" class="Symbol"
      >(</a
      ><a name="13666" href="Stlc.html#5649" class="InductiveConstructor"
      >var</a
      ><a name="13669"
      > </a
      ><a name="13670" href="Stlc.html#13598" class="Bound"
      >x</a
      ><a name="13671" class="Symbol"
      >)</a
      ><a name="13672"
      > </a
      ><a name="13673" href="Stlc.html#13585" class="Datatype Operator"
      >==&gt;</a
      ><a name="13676"
      > </a
      ><a name="13677" href="Stlc.html#13607" class="Bound"
      >s</a
      ><a name="13678"
      >
  </a
      ><a name="13681" class="Comment"
      >{- FILL IN HERE -}</a
      >
{% endraw %}</pre>

<pre class="Agda">{% raw %}
<a name="13725" class="Keyword"
      >postulate</a
      ><a name="13734"
      >
  </a
      ><a name="13737" href="Stlc.html#13737" class="Postulate"
      >subst-correct</a
      ><a name="13750"
      > </a
      ><a name="13751" class="Symbol"
      >:</a
      ><a name="13752"
      > </a
      ><a name="13753" class="Symbol"
      >&#8704;</a
      ><a name="13754"
      > </a
      ><a name="13755" href="Stlc.html#13755" class="Bound"
      >s</a
      ><a name="13756"
      > </a
      ><a name="13757" href="Stlc.html#13757" class="Bound"
      >x</a
      ><a name="13758"
      > </a
      ><a name="13759" href="Stlc.html#13759" class="Bound"
      >t</a
      ><a name="13760"
      > </a
      ><a name="13761" href="Stlc.html#13761" class="Bound"
      >t'</a
      ><a name="13763"
      >
                </a
      ><a name="13780" class="Symbol"
      >&#8594;</a
      ><a name="13781"
      > </a
      ><a name="13782" href="Stlc.html#12189" class="Function Operator"
      >[</a
      ><a name="13783"
      > </a
      ><a name="13784" href="Stlc.html#13757" class="Bound"
      >x</a
      ><a name="13785"
      > </a
      ><a name="13786" href="Stlc.html#12189" class="Function Operator"
      >:=</a
      ><a name="13788"
      > </a
      ><a name="13789" href="Stlc.html#13755" class="Bound"
      >s</a
      ><a name="13790"
      > </a
      ><a name="13791" href="Stlc.html#12189" class="Function Operator"
      >]</a
      ><a name="13792"
      > </a
      ><a name="13793" href="Stlc.html#13759" class="Bound"
      >t</a
      ><a name="13794"
      > </a
      ><a name="13795" href="Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="13796"
      > </a
      ><a name="13797" href="Stlc.html#13761" class="Bound"
      >t'</a
      ><a name="13799"
      >
                </a
      ><a name="13816" class="Symbol"
      >&#8594;</a
      ><a name="13817"
      > </a
      ><a name="13818" href="Stlc.html#13585" class="Datatype Operator"
      >[</a
      ><a name="13819"
      > </a
      ><a name="13820" href="Stlc.html#13757" class="Bound"
      >x</a
      ><a name="13821"
      > </a
      ><a name="13822" href="Stlc.html#13585" class="Datatype Operator"
      >:=</a
      ><a name="13824"
      > </a
      ><a name="13825" href="Stlc.html#13755" class="Bound"
      >s</a
      ><a name="13826"
      > </a
      ><a name="13827" href="Stlc.html#13585" class="Datatype Operator"
      >]</a
      ><a name="13828"
      > </a
      ><a name="13829" href="Stlc.html#13759" class="Bound"
      >t</a
      ><a name="13830"
      > </a
      ><a name="13831" href="Stlc.html#13585" class="Datatype Operator"
      >==&gt;</a
      ><a name="13834"
      > </a
      ><a name="13835" href="Stlc.html#13761" class="Bound"
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
<a name="15100" class="Keyword"
      >data</a
      ><a name="15104"
      > </a
      ><a name="15105" href="Stlc.html#15105" class="Datatype Operator"
      >_==&gt;_</a
      ><a name="15110"
      > </a
      ><a name="15111" class="Symbol"
      >:</a
      ><a name="15112"
      > </a
      ><a name="15113" href="Stlc.html#5630" class="Datatype"
      >Term</a
      ><a name="15117"
      > </a
      ><a name="15118" class="Symbol"
      >&#8594;</a
      ><a name="15119"
      > </a
      ><a name="15120" href="Stlc.html#5630" class="Datatype"
      >Term</a
      ><a name="15124"
      > </a
      ><a name="15125" class="Symbol"
      >&#8594;</a
      ><a name="15126"
      > </a
      ><a name="15127" class="PrimitiveType"
      >Set</a
      ><a name="15130"
      > </a
      ><a name="15131" class="Keyword"
      >where</a
      ><a name="15136"
      >
  </a
      ><a name="15139" href="Stlc.html#15139" class="InductiveConstructor"
      >red</a
      ><a name="15142"
      >     </a
      ><a name="15147" class="Symbol"
      >:</a
      ><a name="15148"
      > </a
      ><a name="15149" class="Symbol"
      >&#8704;</a
      ><a name="15150"
      > </a
      ><a name="15171" class="Symbol"
      >&#8594;</a
      ><a name="15172"
      > </a
      ><a name="15173" href="Stlc.html#8969" class="Datatype"
      >Value</a
      ><a name="15178"
      > </a
      ><a name="15179" href="Stlc.html#15158" class="Bound"
      >t</a
      ><a name="15180"
      >
          </a
      ><a name="15191" class="Symbol"
      >&#8594;</a
      ><a name="15192"
      > </a
      ><a name="15193" href="Stlc.html#5669" class="InductiveConstructor"
      >app</a
      ><a name="15196"
      > </a
      ><a name="15197" class="Symbol"
      >(</a
      ><a name="15198" href="Stlc.html#5698" class="InductiveConstructor"
      >abs</a
      ><a name="15201"
      > </a
      ><a name="15202" href="Stlc.html#15152" class="Bound"
      >x</a
      ><a name="15203"
      > </a
      ><a name="15204" href="Stlc.html#15154" class="Bound"
      >A</a
      ><a name="15205"
      > </a
      ><a name="15206" href="Stlc.html#15156" class="Bound"
      >s</a
      ><a name="15207" class="Symbol"
      >)</a
      ><a name="15208"
      > </a
      ><a name="15209" href="Stlc.html#15158" class="Bound"
      >t</a
      ><a name="15210"
      > </a
      ><a name="15211" href="Stlc.html#15105" class="Datatype Operator"
      >==&gt;</a
      ><a name="15214"
      > </a
      ><a name="15215" href="Stlc.html#12189" class="Function Operator"
      >[</a
      ><a name="15216"
      > </a
      ><a name="15217" href="Stlc.html#15152" class="Bound"
      >x</a
      ><a name="15218"
      > </a
      ><a name="15219" href="Stlc.html#12189" class="Function Operator"
      >:=</a
      ><a name="15221"
      > </a
      ><a name="15222" href="Stlc.html#15158" class="Bound"
      >t</a
      ><a name="15223"
      > </a
      ><a name="15224" href="Stlc.html#12189" class="Function Operator"
      >]</a
      ><a name="15225"
      > </a
      ><a name="15226" href="Stlc.html#15156" class="Bound"
      >s</a
      ><a name="15227"
      >
  </a
      ><a name="15230" href="Stlc.html#15230" class="InductiveConstructor"
      >app1</a
      ><a name="15234"
      >    </a
      ><a name="15238" class="Symbol"
      >:</a
      ><a name="15239"
      > </a
      ><a name="15240" class="Symbol"
      >&#8704;</a
      ><a name="15241"
      > </a
      ><a name="15261" class="Symbol"
      >&#8594;</a
      ><a name="15262"
      > </a
      ><a name="15263" href="Stlc.html#15243" class="Bound"
      >s</a
      ><a name="15264"
      > </a
      ><a name="15265" href="Stlc.html#15105" class="Datatype Operator"
      >==&gt;</a
      ><a name="15268"
      > </a
      ><a name="15269" href="Stlc.html#15245" class="Bound"
      >s'</a
      ><a name="15271"
      >
          </a
      ><a name="15282" class="Symbol"
      >&#8594;</a
      ><a name="15283"
      > </a
      ><a name="15284" href="Stlc.html#5669" class="InductiveConstructor"
      >app</a
      ><a name="15287"
      > </a
      ><a name="15288" href="Stlc.html#15243" class="Bound"
      >s</a
      ><a name="15289"
      > </a
      ><a name="15290" href="Stlc.html#15248" class="Bound"
      >t</a
      ><a name="15291"
      > </a
      ><a name="15292" href="Stlc.html#15105" class="Datatype Operator"
      >==&gt;</a
      ><a name="15295"
      > </a
      ><a name="15296" href="Stlc.html#5669" class="InductiveConstructor"
      >app</a
      ><a name="15299"
      > </a
      ><a name="15300" href="Stlc.html#15245" class="Bound"
      >s'</a
      ><a name="15302"
      > </a
      ><a name="15303" href="Stlc.html#15248" class="Bound"
      >t</a
      ><a name="15304"
      >
  </a
      ><a name="15307" href="Stlc.html#15307" class="InductiveConstructor"
      >app2</a
      ><a name="15311"
      >    </a
      ><a name="15315" class="Symbol"
      >:</a
      ><a name="15316"
      > </a
      ><a name="15317" class="Symbol"
      >&#8704;</a
      ><a name="15318"
      > </a
      ><a name="15338" class="Symbol"
      >&#8594;</a
      ><a name="15339"
      > </a
      ><a name="15340" href="Stlc.html#8969" class="Datatype"
      >Value</a
      ><a name="15345"
      > </a
      ><a name="15346" href="Stlc.html#15320" class="Bound"
      >s</a
      ><a name="15347"
      >
          </a
      ><a name="15358" class="Symbol"
      >&#8594;</a
      ><a name="15359"
      > </a
      ><a name="15360" href="Stlc.html#15322" class="Bound"
      >t</a
      ><a name="15361"
      > </a
      ><a name="15362" href="Stlc.html#15105" class="Datatype Operator"
      >==&gt;</a
      ><a name="15365"
      > </a
      ><a name="15366" href="Stlc.html#15324" class="Bound"
      >t'</a
      ><a name="15368"
      >
          </a
      ><a name="15379" class="Symbol"
      >&#8594;</a
      ><a name="15380"
      > </a
      ><a name="15381" href="Stlc.html#5669" class="InductiveConstructor"
      >app</a
      ><a name="15384"
      > </a
      ><a name="15385" href="Stlc.html#15320" class="Bound"
      >s</a
      ><a name="15386"
      > </a
      ><a name="15387" href="Stlc.html#15322" class="Bound"
      >t</a
      ><a name="15388"
      > </a
      ><a name="15389" href="Stlc.html#15105" class="Datatype Operator"
      >==&gt;</a
      ><a name="15392"
      > </a
      ><a name="15393" href="Stlc.html#5669" class="InductiveConstructor"
      >app</a
      ><a name="15396"
      > </a
      ><a name="15397" href="Stlc.html#15320" class="Bound"
      >s</a
      ><a name="15398"
      > </a
      ><a name="15399" href="Stlc.html#15324" class="Bound"
      >t'</a
      ><a name="15401"
      >
  </a
      ><a name="15404" href="Stlc.html#15404" class="InductiveConstructor"
      >if</a
      ><a name="15406"
      >      </a
      ><a name="15412" class="Symbol"
      >:</a
      ><a name="15413"
      > </a
      ><a name="15414" class="Symbol"
      >&#8704;</a
      ><a name="15415"
      > </a
      ><a name="15437" class="Symbol"
      >&#8594;</a
      ><a name="15438"
      > </a
      ><a name="15439" href="Stlc.html#15417" class="Bound"
      >s</a
      ><a name="15440"
      > </a
      ><a name="15441" href="Stlc.html#15105" class="Datatype Operator"
      >==&gt;</a
      ><a name="15444"
      > </a
      ><a name="15445" href="Stlc.html#15419" class="Bound"
      >s'</a
      ><a name="15447"
      >
          </a
      ><a name="15458" class="Symbol"
      >&#8594;</a
      ><a name="15459"
      > </a
      ><a name="15460" href="Stlc.html#5762" class="InductiveConstructor Operator"
      >if</a
      ><a name="15462"
      > </a
      ><a name="15463" href="Stlc.html#15417" class="Bound"
      >s</a
      ><a name="15464"
      > </a
      ><a name="15465" href="Stlc.html#5762" class="InductiveConstructor Operator"
      >then</a
      ><a name="15469"
      > </a
      ><a name="15470" href="Stlc.html#15422" class="Bound"
      >t</a
      ><a name="15471"
      > </a
      ><a name="15472" href="Stlc.html#5762" class="InductiveConstructor Operator"
      >else</a
      ><a name="15476"
      > </a
      ><a name="15477" href="Stlc.html#15424" class="Bound"
      >u</a
      ><a name="15478"
      > </a
      ><a name="15479" href="Stlc.html#15105" class="Datatype Operator"
      >==&gt;</a
      ><a name="15482"
      > </a
      ><a name="15483" href="Stlc.html#5762" class="InductiveConstructor Operator"
      >if</a
      ><a name="15485"
      > </a
      ><a name="15486" href="Stlc.html#15419" class="Bound"
      >s'</a
      ><a name="15488"
      > </a
      ><a name="15489" href="Stlc.html#5762" class="InductiveConstructor Operator"
      >then</a
      ><a name="15493"
      > </a
      ><a name="15494" href="Stlc.html#15422" class="Bound"
      >t</a
      ><a name="15495"
      > </a
      ><a name="15496" href="Stlc.html#5762" class="InductiveConstructor Operator"
      >else</a
      ><a name="15500"
      > </a
      ><a name="15501" href="Stlc.html#15424" class="Bound"
      >u</a
      ><a name="15502"
      >
  </a
      ><a name="15505" href="Stlc.html#15505" class="InductiveConstructor"
      >iftrue</a
      ><a name="15511"
      >  </a
      ><a name="15513" class="Symbol"
      >:</a
      ><a name="15514"
      > </a
      ><a name="15515" class="Symbol"
      >&#8704;</a
      ><a name="15516"
      > </a
      ><a name="15533" class="Symbol"
      >&#8594;</a
      ><a name="15534"
      > </a
      ><a name="15535" href="Stlc.html#5762" class="InductiveConstructor Operator"
      >if</a
      ><a name="15537"
      > </a
      ><a name="15538" href="Stlc.html#5732" class="InductiveConstructor"
      >true</a
      ><a name="15542"
      > </a
      ><a name="15543" href="Stlc.html#5762" class="InductiveConstructor Operator"
      >then</a
      ><a name="15547"
      > </a
      ><a name="15548" href="Stlc.html#15518" class="Bound"
      >s</a
      ><a name="15549"
      > </a
      ><a name="15550" href="Stlc.html#5762" class="InductiveConstructor Operator"
      >else</a
      ><a name="15554"
      > </a
      ><a name="15555" href="Stlc.html#15520" class="Bound"
      >t</a
      ><a name="15556"
      > </a
      ><a name="15557" href="Stlc.html#15105" class="Datatype Operator"
      >==&gt;</a
      ><a name="15560"
      > </a
      ><a name="15561" href="Stlc.html#15518" class="Bound"
      >s</a
      ><a name="15562"
      >
  </a
      ><a name="15565" href="Stlc.html#15565" class="InductiveConstructor"
      >iffalse</a
      ><a name="15572"
      > </a
      ><a name="15573" class="Symbol"
      >:</a
      ><a name="15574"
      > </a
      ><a name="15575" class="Symbol"
      >&#8704;</a
      ><a name="15576"
      > </a
      ><a name="15593" class="Symbol"
      >&#8594;</a
      ><a name="15594"
      > </a
      ><a name="15595" href="Stlc.html#5762" class="InductiveConstructor Operator"
      >if</a
      ><a name="15597"
      > </a
      ><a name="15598" href="Stlc.html#5747" class="InductiveConstructor"
      >false</a
      ><a name="15603"
      > </a
      ><a name="15604" href="Stlc.html#5762" class="InductiveConstructor Operator"
      >then</a
      ><a name="15608"
      > </a
      ><a name="15609" href="Stlc.html#15578" class="Bound"
      >s</a
      ><a name="15610"
      > </a
      ><a name="15611" href="Stlc.html#5762" class="InductiveConstructor Operator"
      >else</a
      ><a name="15615"
      > </a
      ><a name="15616" href="Stlc.html#15580" class="Bound"
      >t</a
      ><a name="15617"
      > </a
      ><a name="15618" href="Stlc.html#15105" class="Datatype Operator"
      >==&gt;</a
      ><a name="15621"
      > </a
      ><a name="15622" href="Stlc.html#15580" class="Bound"
      >t</a
      >
{% endraw %}</pre>

<div class="hidden">
<pre class="Agda">{% raw %}
<a name="15670" class="Keyword"
      >infix</a
      ><a name="15675"
      > </a
      ><a name="15676" class="Number"
      >1</a
      ><a name="15677"
      > </a
      ><a name="15678" href="Stlc.html#15105" class="Datatype Operator"
      >_==&gt;_</a
      >
{% endraw %}</pre>
</div>

<pre class="Agda">{% raw %}
<a name="15716" class="Keyword"
      >data</a
      ><a name="15720"
      > </a
      ><a name="15721" href="Stlc.html#15721" class="Datatype"
      >Multi</a
      ><a name="15726"
      > </a
      ><a name="15727" class="Symbol"
      >(</a
      ><a name="15728" href="Stlc.html#15728" class="Bound"
      >R</a
      ><a name="15729"
      > </a
      ><a name="15730" class="Symbol"
      >:</a
      ><a name="15731"
      > </a
      ><a name="15732" href="Stlc.html#5630" class="Datatype"
      >Term</a
      ><a name="15736"
      > </a
      ><a name="15737" class="Symbol"
      >&#8594;</a
      ><a name="15738"
      > </a
      ><a name="15739" href="Stlc.html#5630" class="Datatype"
      >Term</a
      ><a name="15743"
      > </a
      ><a name="15744" class="Symbol"
      >&#8594;</a
      ><a name="15745"
      > </a
      ><a name="15746" class="PrimitiveType"
      >Set</a
      ><a name="15749" class="Symbol"
      >)</a
      ><a name="15750"
      > </a
      ><a name="15751" class="Symbol"
      >:</a
      ><a name="15752"
      > </a
      ><a name="15753" href="Stlc.html#5630" class="Datatype"
      >Term</a
      ><a name="15757"
      > </a
      ><a name="15758" class="Symbol"
      >&#8594;</a
      ><a name="15759"
      > </a
      ><a name="15760" href="Stlc.html#5630" class="Datatype"
      >Term</a
      ><a name="15764"
      > </a
      ><a name="15765" class="Symbol"
      >&#8594;</a
      ><a name="15766"
      > </a
      ><a name="15767" class="PrimitiveType"
      >Set</a
      ><a name="15770"
      > </a
      ><a name="15771" class="Keyword"
      >where</a
      ><a name="15776"
      >
  </a
      ><a name="15779" href="Stlc.html#15779" class="InductiveConstructor"
      >refl</a
      ><a name="15783"
      > </a
      ><a name="15784" class="Symbol"
      >:</a
      ><a name="15785"
      > </a
      ><a name="15786" class="Symbol"
      >&#8704;</a
      ><a name="15787"
      > </a
      ><a name="15792" class="Symbol"
      >-&gt;</a
      ><a name="15794"
      > </a
      ><a name="15795" href="Stlc.html#15721" class="Datatype"
      >Multi</a
      ><a name="15800"
      > </a
      ><a name="15801" href="Stlc.html#15728" class="Bound"
      >R</a
      ><a name="15802"
      > </a
      ><a name="15803" href="Stlc.html#15789" class="Bound"
      >x</a
      ><a name="15804"
      > </a
      ><a name="15805" href="Stlc.html#15789" class="Bound"
      >x</a
      ><a name="15806"
      >
  </a
      ><a name="15809" href="Stlc.html#15809" class="InductiveConstructor"
      >step</a
      ><a name="15813"
      > </a
      ><a name="15814" class="Symbol"
      >:</a
      ><a name="15815"
      > </a
      ><a name="15816" class="Symbol"
      >&#8704;</a
      ><a name="15817"
      > </a
      ><a name="15826" class="Symbol"
      >-&gt;</a
      ><a name="15828"
      > </a
      ><a name="15829" href="Stlc.html#15728" class="Bound"
      >R</a
      ><a name="15830"
      > </a
      ><a name="15831" href="Stlc.html#15819" class="Bound"
      >x</a
      ><a name="15832"
      > </a
      ><a name="15833" href="Stlc.html#15821" class="Bound"
      >y</a
      ><a name="15834"
      > </a
      ><a name="15835" class="Symbol"
      >-&gt;</a
      ><a name="15837"
      > </a
      ><a name="15838" href="Stlc.html#15721" class="Datatype"
      >Multi</a
      ><a name="15843"
      > </a
      ><a name="15844" href="Stlc.html#15728" class="Bound"
      >R</a
      ><a name="15845"
      > </a
      ><a name="15846" href="Stlc.html#15821" class="Bound"
      >y</a
      ><a name="15847"
      > </a
      ><a name="15848" href="Stlc.html#15823" class="Bound"
      >z</a
      ><a name="15849"
      > </a
      ><a name="15850" class="Symbol"
      >-&gt;</a
      ><a name="15852"
      > </a
      ><a name="15853" href="Stlc.html#15721" class="Datatype"
      >Multi</a
      ><a name="15858"
      > </a
      ><a name="15859" href="Stlc.html#15728" class="Bound"
      >R</a
      ><a name="15860"
      > </a
      ><a name="15861" href="Stlc.html#15819" class="Bound"
      >x</a
      ><a name="15862"
      > </a
      ><a name="15863" href="Stlc.html#15823" class="Bound"
      >z</a
      >
{% endraw %}</pre>

<pre class="Agda">{% raw %}
<a name="15890" href="Stlc.html#15890" class="Function Operator"
      >_==&gt;*_</a
      ><a name="15896"
      > </a
      ><a name="15897" class="Symbol"
      >:</a
      ><a name="15898"
      > </a
      ><a name="15899" href="Stlc.html#5630" class="Datatype"
      >Term</a
      ><a name="15903"
      > </a
      ><a name="15904" class="Symbol"
      >&#8594;</a
      ><a name="15905"
      > </a
      ><a name="15906" href="Stlc.html#5630" class="Datatype"
      >Term</a
      ><a name="15910"
      > </a
      ><a name="15911" class="Symbol"
      >&#8594;</a
      ><a name="15912"
      > </a
      ><a name="15913" class="PrimitiveType"
      >Set</a
      ><a name="15916"
      >
</a
      ><a name="15917" href="Stlc.html#15890" class="Function Operator"
      >_==&gt;*_</a
      ><a name="15923"
      > </a
      ><a name="15924" class="Symbol"
      >=</a
      ><a name="15925"
      > </a
      ><a name="15926" href="Stlc.html#15721" class="Datatype"
      >Multi</a
      ><a name="15931"
      > </a
      ><a name="15932" href="Stlc.html#15105" class="Datatype Operator"
      >_==&gt;_</a
      >
{% endraw %}</pre>

<div class="hidden">
<pre class="Agda">{% raw %}
<a name="15984" class="Symbol"
      >{-#</a
      ><a name="15987"
      > </a
      ><a name="15988" class="Keyword"
      >DISPLAY</a
      ><a name="15995"
      > </a
      ><a name="15996" href="Stlc.html#15721" class="Datatype"
      >Multi</a
      ><a name="16001"
      > </a
      ><a name="16002" href="Stlc.html#16002" class="Bound Operator"
      >_==&gt;_</a
      ><a name="16007"
      > = </a
      ><a name="16010" href="Stlc.html#15890" class="Function Operator"
      >_==&gt;*_</a
      ><a name="16016"
      > </a
      ><a name="16017" class="Symbol"
      >#-}</a
      >
{% endraw %}</pre>
</div>

### Examples

Example:

$$((\lambda x:bool\rightarrow bool. x) (\lambda x:bool. x)) \Longrightarrow^* (\lambda x:bool. x)$$.

<pre class="Agda">{% raw %}
<a name="16179" href="Stlc.html#16179" class="Function"
      >step-example1</a
      ><a name="16192"
      > </a
      ><a name="16193" class="Symbol"
      >:</a
      ><a name="16194"
      > </a
      ><a name="16195" class="Symbol"
      >(</a
      ><a name="16196" href="Stlc.html#5669" class="InductiveConstructor"
      >app</a
      ><a name="16199"
      > </a
      ><a name="16200" href="Stlc.html#6579" class="Function"
      >idBB</a
      ><a name="16204"
      > </a
      ><a name="16205" href="Stlc.html#6473" class="Function"
      >idB</a
      ><a name="16208" class="Symbol"
      >)</a
      ><a name="16209"
      > </a
      ><a name="16210" href="Stlc.html#15890" class="Function Operator"
      >==&gt;*</a
      ><a name="16214"
      > </a
      ><a name="16215" href="Stlc.html#6473" class="Function"
      >idB</a
      ><a name="16218"
      >
</a
      ><a name="16219" href="Stlc.html#16179" class="Function"
      >step-example1</a
      ><a name="16232"
      > </a
      ><a name="16233" class="Symbol"
      >=</a
      ><a name="16234"
      > </a
      ><a name="16235" href="Stlc.html#15809" class="InductiveConstructor"
      >step</a
      ><a name="16239"
      > </a
      ><a name="16240" class="Symbol"
      >(</a
      ><a name="16241" href="Stlc.html#15139" class="InductiveConstructor"
      >red</a
      ><a name="16244"
      > </a
      ><a name="16245" href="Stlc.html#8996" class="InductiveConstructor"
      >abs</a
      ><a name="16248" class="Symbol"
      >)</a
      ><a name="16249"
      >
              </a
      ><a name="16264" href="https://agda.github.io/agda-stdlib/Function.html#1835" class="Function Operator"
      >$</a
      ><a name="16265"
      > </a
      ><a name="16266" href="Stlc.html#15779" class="InductiveConstructor"
      >refl</a
      >
{% endraw %}</pre>

Example:

$$(\lambda x:bool\rightarrow bool. x) \;((\lambda x:bool\rightarrow bool. x)\;(\lambda x:bool. x))) \Longrightarrow^* (\lambda x:bool. x)$$.

<pre class="Agda">{% raw %}
<a name="16448" href="Stlc.html#16448" class="Function"
      >step-example2</a
      ><a name="16461"
      > </a
      ><a name="16462" class="Symbol"
      >:</a
      ><a name="16463"
      > </a
      ><a name="16464" class="Symbol"
      >(</a
      ><a name="16465" href="Stlc.html#5669" class="InductiveConstructor"
      >app</a
      ><a name="16468"
      > </a
      ><a name="16469" href="Stlc.html#6579" class="Function"
      >idBB</a
      ><a name="16473"
      > </a
      ><a name="16474" class="Symbol"
      >(</a
      ><a name="16475" href="Stlc.html#5669" class="InductiveConstructor"
      >app</a
      ><a name="16478"
      > </a
      ><a name="16479" href="Stlc.html#6579" class="Function"
      >idBB</a
      ><a name="16483"
      > </a
      ><a name="16484" href="Stlc.html#6473" class="Function"
      >idB</a
      ><a name="16487" class="Symbol"
      >))</a
      ><a name="16489"
      > </a
      ><a name="16490" href="Stlc.html#15890" class="Function Operator"
      >==&gt;*</a
      ><a name="16494"
      > </a
      ><a name="16495" href="Stlc.html#6473" class="Function"
      >idB</a
      ><a name="16498"
      >
</a
      ><a name="16499" href="Stlc.html#16448" class="Function"
      >step-example2</a
      ><a name="16512"
      > </a
      ><a name="16513" class="Symbol"
      >=</a
      ><a name="16514"
      > </a
      ><a name="16515" href="Stlc.html#15809" class="InductiveConstructor"
      >step</a
      ><a name="16519"
      > </a
      ><a name="16520" class="Symbol"
      >(</a
      ><a name="16521" href="Stlc.html#15307" class="InductiveConstructor"
      >app2</a
      ><a name="16525"
      > </a
      ><a name="16526" href="Stlc.html#8996" class="InductiveConstructor"
      >abs</a
      ><a name="16529"
      > </a
      ><a name="16530" class="Symbol"
      >(</a
      ><a name="16531" href="Stlc.html#15139" class="InductiveConstructor"
      >red</a
      ><a name="16534"
      > </a
      ><a name="16535" href="Stlc.html#8996" class="InductiveConstructor"
      >abs</a
      ><a name="16538" class="Symbol"
      >))</a
      ><a name="16540"
      >
              </a
      ><a name="16555" href="https://agda.github.io/agda-stdlib/Function.html#1835" class="Function Operator"
      >$</a
      ><a name="16556"
      > </a
      ><a name="16557" href="Stlc.html#15809" class="InductiveConstructor"
      >step</a
      ><a name="16561"
      > </a
      ><a name="16562" class="Symbol"
      >(</a
      ><a name="16563" href="Stlc.html#15139" class="InductiveConstructor"
      >red</a
      ><a name="16566"
      > </a
      ><a name="16567" href="Stlc.html#8996" class="InductiveConstructor"
      >abs</a
      ><a name="16570" class="Symbol"
      >)</a
      ><a name="16571"
      >
              </a
      ><a name="16586" href="https://agda.github.io/agda-stdlib/Function.html#1835" class="Function Operator"
      >$</a
      ><a name="16587"
      > </a
      ><a name="16588" href="Stlc.html#15779" class="InductiveConstructor"
      >refl</a
      >
{% endraw %}</pre>

Example:

$$((\lambda x:bool\rightarrow bool. x)\;(\lambda x:bool. \text{if }x\text{ then }false\text{ else }true))\;true\Longrightarrow^* false$$.

<pre class="Agda">{% raw %}
<a name="16767" href="Stlc.html#16767" class="Function"
      >step-example3</a
      ><a name="16780"
      > </a
      ><a name="16781" class="Symbol"
      >:</a
      ><a name="16782"
      > </a
      ><a name="16783" class="Symbol"
      >(</a
      ><a name="16784" href="Stlc.html#5669" class="InductiveConstructor"
      >app</a
      ><a name="16787"
      > </a
      ><a name="16788" class="Symbol"
      >(</a
      ><a name="16789" href="Stlc.html#5669" class="InductiveConstructor"
      >app</a
      ><a name="16792"
      > </a
      ><a name="16793" href="Stlc.html#6579" class="Function"
      >idBB</a
      ><a name="16797"
      > </a
      ><a name="16798" href="Stlc.html#7012" class="Function"
      >notB</a
      ><a name="16802" class="Symbol"
      >)</a
      ><a name="16803"
      > </a
      ><a name="16804" href="Stlc.html#5732" class="InductiveConstructor"
      >true</a
      ><a name="16808" class="Symbol"
      >)</a
      ><a name="16809"
      > </a
      ><a name="16810" href="Stlc.html#15890" class="Function Operator"
      >==&gt;*</a
      ><a name="16814"
      > </a
      ><a name="16815" href="Stlc.html#5747" class="InductiveConstructor"
      >false</a
      ><a name="16820"
      >
</a
      ><a name="16821" href="Stlc.html#16767" class="Function"
      >step-example3</a
      ><a name="16834"
      > </a
      ><a name="16835" class="Symbol"
      >=</a
      ><a name="16836"
      > </a
      ><a name="16837" href="Stlc.html#15809" class="InductiveConstructor"
      >step</a
      ><a name="16841"
      > </a
      ><a name="16842" class="Symbol"
      >(</a
      ><a name="16843" href="Stlc.html#15230" class="InductiveConstructor"
      >app1</a
      ><a name="16847"
      > </a
      ><a name="16848" class="Symbol"
      >(</a
      ><a name="16849" href="Stlc.html#15139" class="InductiveConstructor"
      >red</a
      ><a name="16852"
      > </a
      ><a name="16853" href="Stlc.html#8996" class="InductiveConstructor"
      >abs</a
      ><a name="16856" class="Symbol"
      >))</a
      ><a name="16858"
      >
              </a
      ><a name="16873" href="https://agda.github.io/agda-stdlib/Function.html#1835" class="Function Operator"
      >$</a
      ><a name="16874"
      > </a
      ><a name="16875" href="Stlc.html#15809" class="InductiveConstructor"
      >step</a
      ><a name="16879"
      > </a
      ><a name="16880" class="Symbol"
      >(</a
      ><a name="16881" href="Stlc.html#15139" class="InductiveConstructor"
      >red</a
      ><a name="16884"
      > </a
      ><a name="16885" href="Stlc.html#9044" class="InductiveConstructor"
      >true</a
      ><a name="16889" class="Symbol"
      >)</a
      ><a name="16890"
      >
              </a
      ><a name="16905" href="https://agda.github.io/agda-stdlib/Function.html#1835" class="Function Operator"
      >$</a
      ><a name="16906"
      > </a
      ><a name="16907" href="Stlc.html#15809" class="InductiveConstructor"
      >step</a
      ><a name="16911"
      > </a
      ><a name="16912" href="Stlc.html#15505" class="InductiveConstructor"
      >iftrue</a
      ><a name="16918"
      >
              </a
      ><a name="16933" href="https://agda.github.io/agda-stdlib/Function.html#1835" class="Function Operator"
      >$</a
      ><a name="16934"
      > </a
      ><a name="16935" href="Stlc.html#15779" class="InductiveConstructor"
      >refl</a
      >
{% endraw %}</pre>

Example:

$$((\lambda x:bool\rightarrow bool. x)\;((\lambda x:bool. \text{if }x\text{ then }false\text{ else }true)\;true))\Longrightarrow^* false$$.

<pre class="Agda">{% raw %}
<a name="17116" href="Stlc.html#17116" class="Function"
      >step-example4</a
      ><a name="17129"
      > </a
      ><a name="17130" class="Symbol"
      >:</a
      ><a name="17131"
      > </a
      ><a name="17132" class="Symbol"
      >(</a
      ><a name="17133" href="Stlc.html#5669" class="InductiveConstructor"
      >app</a
      ><a name="17136"
      > </a
      ><a name="17137" href="Stlc.html#6579" class="Function"
      >idBB</a
      ><a name="17141"
      > </a
      ><a name="17142" class="Symbol"
      >(</a
      ><a name="17143" href="Stlc.html#5669" class="InductiveConstructor"
      >app</a
      ><a name="17146"
      > </a
      ><a name="17147" href="Stlc.html#7012" class="Function"
      >notB</a
      ><a name="17151"
      > </a
      ><a name="17152" href="Stlc.html#5732" class="InductiveConstructor"
      >true</a
      ><a name="17156" class="Symbol"
      >))</a
      ><a name="17158"
      > </a
      ><a name="17159" href="Stlc.html#15890" class="Function Operator"
      >==&gt;*</a
      ><a name="17163"
      > </a
      ><a name="17164" href="Stlc.html#5747" class="InductiveConstructor"
      >false</a
      ><a name="17169"
      >
</a
      ><a name="17170" href="Stlc.html#17116" class="Function"
      >step-example4</a
      ><a name="17183"
      > </a
      ><a name="17184" class="Symbol"
      >=</a
      ><a name="17185"
      > </a
      ><a name="17186" href="Stlc.html#15809" class="InductiveConstructor"
      >step</a
      ><a name="17190"
      > </a
      ><a name="17191" class="Symbol"
      >(</a
      ><a name="17192" href="Stlc.html#15307" class="InductiveConstructor"
      >app2</a
      ><a name="17196"
      > </a
      ><a name="17197" href="Stlc.html#8996" class="InductiveConstructor"
      >abs</a
      ><a name="17200"
      > </a
      ><a name="17201" class="Symbol"
      >(</a
      ><a name="17202" href="Stlc.html#15139" class="InductiveConstructor"
      >red</a
      ><a name="17205"
      > </a
      ><a name="17206" href="Stlc.html#9044" class="InductiveConstructor"
      >true</a
      ><a name="17210" class="Symbol"
      >))</a
      ><a name="17212"
      >
              </a
      ><a name="17227" href="https://agda.github.io/agda-stdlib/Function.html#1835" class="Function Operator"
      >$</a
      ><a name="17228"
      > </a
      ><a name="17229" href="Stlc.html#15809" class="InductiveConstructor"
      >step</a
      ><a name="17233"
      > </a
      ><a name="17234" class="Symbol"
      >(</a
      ><a name="17235" href="Stlc.html#15307" class="InductiveConstructor"
      >app2</a
      ><a name="17239"
      > </a
      ><a name="17240" href="Stlc.html#8996" class="InductiveConstructor"
      >abs</a
      ><a name="17243"
      > </a
      ><a name="17244" href="Stlc.html#15505" class="InductiveConstructor"
      >iftrue</a
      ><a name="17250" class="Symbol"
      >)</a
      ><a name="17251"
      >
              </a
      ><a name="17266" href="https://agda.github.io/agda-stdlib/Function.html#1835" class="Function Operator"
      >$</a
      ><a name="17267"
      > </a
      ><a name="17268" href="Stlc.html#15809" class="InductiveConstructor"
      >step</a
      ><a name="17272"
      > </a
      ><a name="17273" class="Symbol"
      >(</a
      ><a name="17274" href="Stlc.html#15139" class="InductiveConstructor"
      >red</a
      ><a name="17277"
      > </a
      ><a name="17278" href="Stlc.html#9065" class="InductiveConstructor"
      >false</a
      ><a name="17283" class="Symbol"
      >)</a
      ><a name="17284"
      >
              </a
      ><a name="17299" href="https://agda.github.io/agda-stdlib/Function.html#1835" class="Function Operator"
      >$</a
      ><a name="17300"
      > </a
      ><a name="17301" href="Stlc.html#15779" class="InductiveConstructor"
      >refl</a
      >
{% endraw %}</pre>

#### Exercise: 2 stars (step-example5)

<pre class="Agda">{% raw %}
<a name="17371" class="Keyword"
      >postulate</a
      ><a name="17380"
      >
  </a
      ><a name="17383" href="Stlc.html#17383" class="Postulate"
      >step-example5</a
      ><a name="17396"
      > </a
      ><a name="17397" class="Symbol"
      >:</a
      ><a name="17398"
      > </a
      ><a name="17399" class="Symbol"
      >(</a
      ><a name="17400" href="Stlc.html#5669" class="InductiveConstructor"
      >app</a
      ><a name="17403"
      > </a
      ><a name="17404" class="Symbol"
      >(</a
      ><a name="17405" href="Stlc.html#5669" class="InductiveConstructor"
      >app</a
      ><a name="17408"
      > </a
      ><a name="17409" href="Stlc.html#6733" class="Function"
      >idBBBB</a
      ><a name="17415"
      > </a
      ><a name="17416" href="Stlc.html#6579" class="Function"
      >idBB</a
      ><a name="17420" class="Symbol"
      >)</a
      ><a name="17421"
      > </a
      ><a name="17422" href="Stlc.html#6473" class="Function"
      >idB</a
      ><a name="17425" class="Symbol"
      >)</a
      ><a name="17426"
      > </a
      ><a name="17427" href="Stlc.html#15890" class="Function Operator"
      >==&gt;*</a
      ><a name="17431"
      > </a
      ><a name="17432" href="Stlc.html#6473" class="Function"
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
<a name="18152" href="Stlc.html#18152" class="Function"
      >Ctxt</a
      ><a name="18156"
      > </a
      ><a name="18157" class="Symbol"
      >:</a
      ><a name="18158"
      > </a
      ><a name="18159" class="PrimitiveType"
      >Set</a
      ><a name="18162"
      >
</a
      ><a name="18163" href="Stlc.html#18152" class="Function"
      >Ctxt</a
      ><a name="18167"
      > </a
      ><a name="18168" class="Symbol"
      >=</a
      ><a name="18169"
      > </a
      ><a name="18170" href="Maps.html#9394" class="Function"
      >PartialMap</a
      ><a name="18180"
      > </a
      ><a name="18181" href="Stlc.html#5463" class="Datatype"
      >Type</a
      ><a name="18185"
      >

</a
      ><a name="18187" href="Stlc.html#18187" class="Function"
      >&#8709;</a
      ><a name="18188"
      > </a
      ><a name="18189" class="Symbol"
      >:</a
      ><a name="18190"
      > </a
      ><a name="18191" href="Stlc.html#18152" class="Function"
      >Ctxt</a
      ><a name="18195"
      >
</a
      ><a name="18196" href="Stlc.html#18187" class="Function"
      >&#8709;</a
      ><a name="18197"
      > </a
      ><a name="18198" class="Symbol"
      >=</a
      ><a name="18199"
      > </a
      ><a name="18200" href="Maps.html#9527" class="Function"
      >PartialMap.empty</a
      ><a name="18216"
      >

</a
      ><a name="18218" href="Stlc.html#18218" class="Function Operator"
      >_,_&#8758;_</a
      ><a name="18223"
      > </a
      ><a name="18224" class="Symbol"
      >:</a
      ><a name="18225"
      > </a
      ><a name="18226" href="Stlc.html#18152" class="Function"
      >Ctxt</a
      ><a name="18230"
      > </a
      ><a name="18231" class="Symbol"
      >-&gt;</a
      ><a name="18233"
      > </a
      ><a name="18234" href="Maps.html#2275" class="Datatype"
      >Id</a
      ><a name="18236"
      > </a
      ><a name="18237" class="Symbol"
      >-&gt;</a
      ><a name="18239"
      > </a
      ><a name="18240" href="Stlc.html#5463" class="Datatype"
      >Type</a
      ><a name="18244"
      > </a
      ><a name="18245" class="Symbol"
      >-&gt;</a
      ><a name="18247"
      > </a
      ><a name="18248" href="Stlc.html#18152" class="Function"
      >Ctxt</a
      ><a name="18252"
      >
</a
      ><a name="18253" href="Stlc.html#18218" class="Function Operator"
      >_,_&#8758;_</a
      ><a name="18258"
      > </a
      ><a name="18259" class="Symbol"
      >=</a
      ><a name="18260"
      > </a
      ><a name="18261" href="Maps.html#9616" class="Function"
      >PartialMap.update</a
      >
{% endraw %}</pre>

<div class="hidden">
<pre class="Agda">{% raw %}
<a name="18325" class="Keyword"
      >infixl</a
      ><a name="18331"
      > </a
      ><a name="18332" class="Number"
      >3</a
      ><a name="18333"
      > </a
      ><a name="18334" href="Stlc.html#18218" class="Function Operator"
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
<a name="19114" class="Keyword"
      >data</a
      ><a name="19118"
      > </a
      ><a name="19119" href="Stlc.html#19119" class="Datatype Operator"
      >_&#8866;_&#8758;_</a
      ><a name="19124"
      > </a
      ><a name="19125" class="Symbol"
      >:</a
      ><a name="19126"
      > </a
      ><a name="19127" href="Stlc.html#18152" class="Function"
      >Ctxt</a
      ><a name="19131"
      > </a
      ><a name="19132" class="Symbol"
      >-&gt;</a
      ><a name="19134"
      > </a
      ><a name="19135" href="Stlc.html#5630" class="Datatype"
      >Term</a
      ><a name="19139"
      > </a
      ><a name="19140" class="Symbol"
      >-&gt;</a
      ><a name="19142"
      > </a
      ><a name="19143" href="Stlc.html#5463" class="Datatype"
      >Type</a
      ><a name="19147"
      > </a
      ><a name="19148" class="Symbol"
      >-&gt;</a
      ><a name="19150"
      > </a
      ><a name="19151" class="PrimitiveType"
      >Set</a
      ><a name="19154"
      > </a
      ><a name="19155" class="Keyword"
      >where</a
      ><a name="19160"
      >
  </a
      ><a name="19163" href="Stlc.html#19163" class="InductiveConstructor"
      >var</a
      ><a name="19166"
      >           </a
      ><a name="19177" class="Symbol"
      >:</a
      ><a name="19178"
      > </a
      ><a name="19179" class="Symbol"
      >&#8704;</a
      ><a name="19180"
      > </a
      ><a name="19185" href="Stlc.html#19185" class="Bound"
      >x</a
      ><a name="19186"
      > </a
      ><a name="19207" class="Symbol"
      >&#8594;</a
      ><a name="19208"
      > </a
      ><a name="19209" href="Stlc.html#19182" class="Bound"
      >&#915;</a
      ><a name="19210"
      > </a
      ><a name="19211" href="Stlc.html#19185" class="Bound"
      >x</a
      ><a name="19212"
      > </a
      ><a name="19213" href="Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="19214"
      > </a
      ><a name="19215" href="https://agda.github.io/agda-stdlib/Data.Maybe.Base.html#373" class="InductiveConstructor"
      >just</a
      ><a name="19219"
      > </a
      ><a name="19220" href="Stlc.html#19188" class="Bound"
      >A</a
      ><a name="19221"
      >
                </a
      ><a name="19238" class="Symbol"
      >&#8594;</a
      ><a name="19239"
      > </a
      ><a name="19240" href="Stlc.html#19182" class="Bound"
      >&#915;</a
      ><a name="19241"
      > </a
      ><a name="19242" href="Stlc.html#19119" class="Datatype Operator"
      >&#8866;</a
      ><a name="19243"
      > </a
      ><a name="19244" href="Stlc.html#5649" class="InductiveConstructor"
      >var</a
      ><a name="19247"
      > </a
      ><a name="19248" href="Stlc.html#19185" class="Bound"
      >x</a
      ><a name="19249"
      > </a
      ><a name="19250" href="Stlc.html#19119" class="Datatype Operator"
      >&#8758;</a
      ><a name="19251"
      > </a
      ><a name="19252" href="Stlc.html#19188" class="Bound"
      >A</a
      ><a name="19253"
      >
  </a
      ><a name="19256" href="Stlc.html#19256" class="InductiveConstructor"
      >abs</a
      ><a name="19259"
      >           </a
      ><a name="19270" class="Symbol"
      >:</a
      ><a name="19271"
      > </a
      ><a name="19272" class="Symbol"
      >&#8704;</a
      ><a name="19273"
      > </a
      ><a name="19310" class="Symbol"
      >&#8594;</a
      ><a name="19311"
      > </a
      ><a name="19312" href="Stlc.html#19275" class="Bound"
      >&#915;</a
      ><a name="19313"
      > </a
      ><a name="19314" href="Stlc.html#18218" class="Function Operator"
      >,</a
      ><a name="19315"
      > </a
      ><a name="19316" href="Stlc.html#19279" class="Bound"
      >x</a
      ><a name="19317"
      > </a
      ><a name="19318" href="Stlc.html#18218" class="Function Operator"
      >&#8758;</a
      ><a name="19319"
      > </a
      ><a name="19320" href="Stlc.html#19283" class="Bound"
      >A</a
      ><a name="19321"
      > </a
      ><a name="19322" href="Stlc.html#19119" class="Datatype Operator"
      >&#8866;</a
      ><a name="19323"
      > </a
      ><a name="19324" href="Stlc.html#19291" class="Bound"
      >s</a
      ><a name="19325"
      > </a
      ><a name="19326" href="Stlc.html#19119" class="Datatype Operator"
      >&#8758;</a
      ><a name="19327"
      > </a
      ><a name="19328" href="Stlc.html#19287" class="Bound"
      >B</a
      ><a name="19329"
      >
                </a
      ><a name="19346" class="Symbol"
      >&#8594;</a
      ><a name="19347"
      > </a
      ><a name="19348" href="Stlc.html#19275" class="Bound"
      >&#915;</a
      ><a name="19349"
      > </a
      ><a name="19350" href="Stlc.html#19119" class="Datatype Operator"
      >&#8866;</a
      ><a name="19351"
      > </a
      ><a name="19352" href="Stlc.html#5698" class="InductiveConstructor"
      >abs</a
      ><a name="19355"
      > </a
      ><a name="19356" href="Stlc.html#19279" class="Bound"
      >x</a
      ><a name="19357"
      > </a
      ><a name="19358" href="Stlc.html#19283" class="Bound"
      >A</a
      ><a name="19359"
      > </a
      ><a name="19360" href="Stlc.html#19291" class="Bound"
      >s</a
      ><a name="19361"
      > </a
      ><a name="19362" href="Stlc.html#19119" class="Datatype Operator"
      >&#8758;</a
      ><a name="19363"
      > </a
      ><a name="19364" href="Stlc.html#19283" class="Bound"
      >A</a
      ><a name="19365"
      > </a
      ><a name="19366" href="Stlc.html#5496" class="InductiveConstructor Operator"
      >&#8658;</a
      ><a name="19367"
      > </a
      ><a name="19368" href="Stlc.html#19287" class="Bound"
      >B</a
      ><a name="19369"
      >
  </a
      ><a name="19372" href="Stlc.html#19372" class="InductiveConstructor"
      >app</a
      ><a name="19375"
      >           </a
      ><a name="19386" class="Symbol"
      >:</a
      ><a name="19387"
      > </a
      ><a name="19388" class="Symbol"
      >&#8704;</a
      ><a name="19389"
      > </a
      ><a name="19426" class="Symbol"
      >&#8594;</a
      ><a name="19427"
      > </a
      ><a name="19428" href="Stlc.html#19391" class="Bound"
      >&#915;</a
      ><a name="19429"
      > </a
      ><a name="19430" href="Stlc.html#19119" class="Datatype Operator"
      >&#8866;</a
      ><a name="19431"
      > </a
      ><a name="19432" href="Stlc.html#19403" class="Bound"
      >s</a
      ><a name="19433"
      > </a
      ><a name="19434" href="Stlc.html#19119" class="Datatype Operator"
      >&#8758;</a
      ><a name="19435"
      > </a
      ><a name="19436" href="Stlc.html#19395" class="Bound"
      >A</a
      ><a name="19437"
      > </a
      ><a name="19438" href="Stlc.html#5496" class="InductiveConstructor Operator"
      >&#8658;</a
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
      ><a name="19460" href="Stlc.html#19391" class="Bound"
      >&#915;</a
      ><a name="19461"
      > </a
      ><a name="19462" href="Stlc.html#19119" class="Datatype Operator"
      >&#8866;</a
      ><a name="19463"
      > </a
      ><a name="19464" href="Stlc.html#19407" class="Bound"
      >t</a
      ><a name="19465"
      > </a
      ><a name="19466" href="Stlc.html#19119" class="Datatype Operator"
      >&#8758;</a
      ><a name="19467"
      > </a
      ><a name="19468" href="Stlc.html#19395" class="Bound"
      >A</a
      ><a name="19469"
      >
                </a
      ><a name="19486" class="Symbol"
      >&#8594;</a
      ><a name="19487"
      > </a
      ><a name="19488" href="Stlc.html#19391" class="Bound"
      >&#915;</a
      ><a name="19489"
      > </a
      ><a name="19490" href="Stlc.html#19119" class="Datatype Operator"
      >&#8866;</a
      ><a name="19491"
      > </a
      ><a name="19492" href="Stlc.html#5669" class="InductiveConstructor"
      >app</a
      ><a name="19495"
      > </a
      ><a name="19496" href="Stlc.html#19403" class="Bound"
      >s</a
      ><a name="19497"
      > </a
      ><a name="19498" href="Stlc.html#19407" class="Bound"
      >t</a
      ><a name="19499"
      > </a
      ><a name="19500" href="Stlc.html#19119" class="Datatype Operator"
      >&#8758;</a
      ><a name="19501"
      > </a
      ><a name="19502" href="Stlc.html#19399" class="Bound"
      >B</a
      ><a name="19503"
      >
  </a
      ><a name="19506" href="Stlc.html#19506" class="InductiveConstructor"
      >true</a
      ><a name="19510"
      >          </a
      ><a name="19520" class="Symbol"
      >:</a
      ><a name="19521"
      > </a
      ><a name="19522" class="Symbol"
      >&#8704;</a
      ><a name="19523"
      > </a
      ><a name="19544" class="Symbol"
      >&#8594;</a
      ><a name="19545"
      > </a
      ><a name="19546" href="Stlc.html#19525" class="Bound"
      >&#915;</a
      ><a name="19547"
      > </a
      ><a name="19548" href="Stlc.html#19119" class="Datatype Operator"
      >&#8866;</a
      ><a name="19549"
      > </a
      ><a name="19550" href="Stlc.html#5732" class="InductiveConstructor"
      >true</a
      ><a name="19554"
      >  </a
      ><a name="19556" href="Stlc.html#19119" class="Datatype Operator"
      >&#8758;</a
      ><a name="19557"
      > </a
      ><a name="19558" href="Stlc.html#5482" class="InductiveConstructor"
      >bool</a
      ><a name="19562"
      >
  </a
      ><a name="19565" href="Stlc.html#19565" class="InductiveConstructor"
      >false</a
      ><a name="19570"
      >         </a
      ><a name="19579" class="Symbol"
      >:</a
      ><a name="19580"
      > </a
      ><a name="19581" class="Symbol"
      >&#8704;</a
      ><a name="19582"
      > </a
      ><a name="19603" class="Symbol"
      >&#8594;</a
      ><a name="19604"
      > </a
      ><a name="19605" href="Stlc.html#19584" class="Bound"
      >&#915;</a
      ><a name="19606"
      > </a
      ><a name="19607" href="Stlc.html#19119" class="Datatype Operator"
      >&#8866;</a
      ><a name="19608"
      > </a
      ><a name="19609" href="Stlc.html#5747" class="InductiveConstructor"
      >false</a
      ><a name="19614"
      > </a
      ><a name="19615" href="Stlc.html#19119" class="Datatype Operator"
      >&#8758;</a
      ><a name="19616"
      > </a
      ><a name="19617" href="Stlc.html#5482" class="InductiveConstructor"
      >bool</a
      ><a name="19621"
      >
  </a
      ><a name="19624" href="Stlc.html#19624" class="InductiveConstructor Operator"
      >if_then_else_</a
      ><a name="19637"
      > </a
      ><a name="19638" class="Symbol"
      >:</a
      ><a name="19639"
      > </a
      ><a name="19640" class="Symbol"
      >&#8704;</a
      ><a name="19641"
      > </a
      ><a name="19678" class="Symbol"
      >&#8594;</a
      ><a name="19679"
      > </a
      ><a name="19680" href="Stlc.html#19643" class="Bound"
      >&#915;</a
      ><a name="19681"
      > </a
      ><a name="19682" href="Stlc.html#19119" class="Datatype Operator"
      >&#8866;</a
      ><a name="19683"
      > </a
      ><a name="19684" href="Stlc.html#19647" class="Bound"
      >s</a
      ><a name="19685"
      > </a
      ><a name="19686" href="Stlc.html#19119" class="Datatype Operator"
      >&#8758;</a
      ><a name="19687"
      > </a
      ><a name="19688" href="Stlc.html#5482" class="InductiveConstructor"
      >bool</a
      ><a name="19692"
      >
                </a
      ><a name="19709" class="Symbol"
      >&#8594;</a
      ><a name="19710"
      > </a
      ><a name="19711" href="Stlc.html#19643" class="Bound"
      >&#915;</a
      ><a name="19712"
      > </a
      ><a name="19713" href="Stlc.html#19119" class="Datatype Operator"
      >&#8866;</a
      ><a name="19714"
      > </a
      ><a name="19715" href="Stlc.html#19651" class="Bound"
      >t</a
      ><a name="19716"
      > </a
      ><a name="19717" href="Stlc.html#19119" class="Datatype Operator"
      >&#8758;</a
      ><a name="19718"
      > </a
      ><a name="19719" href="Stlc.html#19659" class="Bound"
      >A</a
      ><a name="19720"
      >
                </a
      ><a name="19737" class="Symbol"
      >&#8594;</a
      ><a name="19738"
      > </a
      ><a name="19739" href="Stlc.html#19643" class="Bound"
      >&#915;</a
      ><a name="19740"
      > </a
      ><a name="19741" href="Stlc.html#19119" class="Datatype Operator"
      >&#8866;</a
      ><a name="19742"
      > </a
      ><a name="19743" href="Stlc.html#19655" class="Bound"
      >u</a
      ><a name="19744"
      > </a
      ><a name="19745" href="Stlc.html#19119" class="Datatype Operator"
      >&#8758;</a
      ><a name="19746"
      > </a
      ><a name="19747" href="Stlc.html#19659" class="Bound"
      >A</a
      ><a name="19748"
      >
                </a
      ><a name="19765" class="Symbol"
      >&#8594;</a
      ><a name="19766"
      > </a
      ><a name="19767" href="Stlc.html#19643" class="Bound"
      >&#915;</a
      ><a name="19768"
      > </a
      ><a name="19769" href="Stlc.html#19119" class="Datatype Operator"
      >&#8866;</a
      ><a name="19770"
      > </a
      ><a name="19771" href="Stlc.html#5762" class="InductiveConstructor Operator"
      >if</a
      ><a name="19773"
      > </a
      ><a name="19774" href="Stlc.html#19647" class="Bound"
      >s</a
      ><a name="19775"
      > </a
      ><a name="19776" href="Stlc.html#5762" class="InductiveConstructor Operator"
      >then</a
      ><a name="19780"
      > </a
      ><a name="19781" href="Stlc.html#19651" class="Bound"
      >t</a
      ><a name="19782"
      > </a
      ><a name="19783" href="Stlc.html#5762" class="InductiveConstructor Operator"
      >else</a
      ><a name="19787"
      > </a
      ><a name="19788" href="Stlc.html#19655" class="Bound"
      >u</a
      ><a name="19789"
      > </a
      ><a name="19790" href="Stlc.html#19119" class="Datatype Operator"
      >&#8758;</a
      ><a name="19791"
      > </a
      ><a name="19792" href="Stlc.html#19659" class="Bound"
      >A</a
      >
{% endraw %}</pre>

<div class="hidden">
<pre class="Agda">{% raw %}
<a name="19840" class="Keyword"
      >infix</a
      ><a name="19845"
      > </a
      ><a name="19846" class="Number"
      >1</a
      ><a name="19847"
      > </a
      ><a name="19848" href="Stlc.html#19119" class="Datatype Operator"
      >_&#8866;_&#8758;_</a
      >
{% endraw %}</pre>
</div>


### Examples

<pre class="Agda">{% raw %}
<a name="19901" href="Stlc.html#19901" class="Function"
      >typing-example1</a
      ><a name="19916"
      > </a
      ><a name="19917" class="Symbol"
      >:</a
      ><a name="19918"
      > </a
      ><a name="19919" href="Stlc.html#18187" class="Function"
      >&#8709;</a
      ><a name="19920"
      > </a
      ><a name="19921" href="Stlc.html#19119" class="Datatype Operator"
      >&#8866;</a
      ><a name="19922"
      > </a
      ><a name="19923" href="Stlc.html#6473" class="Function"
      >idB</a
      ><a name="19926"
      > </a
      ><a name="19927" href="Stlc.html#19119" class="Datatype Operator"
      >&#8758;</a
      ><a name="19928"
      > </a
      ><a name="19929" href="Stlc.html#5482" class="InductiveConstructor"
      >bool</a
      ><a name="19933"
      > </a
      ><a name="19934" href="Stlc.html#5496" class="InductiveConstructor Operator"
      >&#8658;</a
      ><a name="19935"
      > </a
      ><a name="19936" href="Stlc.html#5482" class="InductiveConstructor"
      >bool</a
      ><a name="19940"
      >
</a
      ><a name="19941" href="Stlc.html#19901" class="Function"
      >typing-example1</a
      ><a name="19956"
      > </a
      ><a name="19957" class="Symbol"
      >=</a
      ><a name="19958"
      > </a
      ><a name="19959" href="Stlc.html#19256" class="InductiveConstructor"
      >abs</a
      ><a name="19962"
      > </a
      ><a name="19963" class="Symbol"
      >(</a
      ><a name="19964" href="Stlc.html#19163" class="InductiveConstructor"
      >var</a
      ><a name="19967"
      > </a
      ><a name="19968" href="Stlc.html#6229" class="Function"
      >x</a
      ><a name="19969"
      > </a
      ><a name="19970" href="Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="19974" class="Symbol"
      >)</a
      >
{% endraw %}</pre>

Another example:

$$\varnothing\vdash \lambda x:A. \lambda y:A\rightarrow A. y\;(y\;x) : A\rightarrow (A\rightarrow A)\rightarrow A$$.

<pre class="Agda">{% raw %}
<a name="20137" href="Stlc.html#20137" class="Function"
      >typing-example2</a
      ><a name="20152"
      > </a
      ><a name="20153" class="Symbol"
      >:</a
      ><a name="20154"
      > </a
      ><a name="20155" href="Stlc.html#18187" class="Function"
      >&#8709;</a
      ><a name="20156"
      > </a
      ><a name="20157" href="Stlc.html#19119" class="Datatype Operator"
      >&#8866;</a
      ><a name="20158"
      >
  </a
      ><a name="20161" class="Symbol"
      >(</a
      ><a name="20162" href="Stlc.html#5698" class="InductiveConstructor"
      >abs</a
      ><a name="20165"
      > </a
      ><a name="20166" href="Stlc.html#6229" class="Function"
      >x</a
      ><a name="20167"
      > </a
      ><a name="20168" href="Stlc.html#5482" class="InductiveConstructor"
      >bool</a
      ><a name="20172"
      >
    </a
      ><a name="20177" class="Symbol"
      >(</a
      ><a name="20178" href="Stlc.html#5698" class="InductiveConstructor"
      >abs</a
      ><a name="20181"
      > </a
      ><a name="20182" href="Stlc.html#6238" class="Function"
      >y</a
      ><a name="20183"
      > </a
      ><a name="20184" class="Symbol"
      >(</a
      ><a name="20185" href="Stlc.html#5482" class="InductiveConstructor"
      >bool</a
      ><a name="20189"
      > </a
      ><a name="20190" href="Stlc.html#5496" class="InductiveConstructor Operator"
      >&#8658;</a
      ><a name="20191"
      > </a
      ><a name="20192" href="Stlc.html#5482" class="InductiveConstructor"
      >bool</a
      ><a name="20196" class="Symbol"
      >)</a
      ><a name="20197"
      >
      </a
      ><a name="20204" class="Symbol"
      >(</a
      ><a name="20205" href="Stlc.html#5669" class="InductiveConstructor"
      >app</a
      ><a name="20208"
      > </a
      ><a name="20209" class="Symbol"
      >(</a
      ><a name="20210" href="Stlc.html#5649" class="InductiveConstructor"
      >var</a
      ><a name="20213"
      > </a
      ><a name="20214" href="Stlc.html#6238" class="Function"
      >y</a
      ><a name="20215" class="Symbol"
      >)</a
      ><a name="20216"
      >
        </a
      ><a name="20225" class="Symbol"
      >(</a
      ><a name="20226" href="Stlc.html#5669" class="InductiveConstructor"
      >app</a
      ><a name="20229"
      > </a
      ><a name="20230" class="Symbol"
      >(</a
      ><a name="20231" href="Stlc.html#5649" class="InductiveConstructor"
      >var</a
      ><a name="20234"
      > </a
      ><a name="20235" href="Stlc.html#6238" class="Function"
      >y</a
      ><a name="20236" class="Symbol"
      >)</a
      ><a name="20237"
      > </a
      ><a name="20238" class="Symbol"
      >(</a
      ><a name="20239" href="Stlc.html#5649" class="InductiveConstructor"
      >var</a
      ><a name="20242"
      > </a
      ><a name="20243" href="Stlc.html#6229" class="Function"
      >x</a
      ><a name="20244" class="Symbol"
      >)))))</a
      ><a name="20249"
      >
  </a
      ><a name="20252" href="Stlc.html#19119" class="Datatype Operator"
      >&#8758;</a
      ><a name="20253"
      > </a
      ><a name="20254" class="Symbol"
      >(</a
      ><a name="20255" href="Stlc.html#5482" class="InductiveConstructor"
      >bool</a
      ><a name="20259"
      > </a
      ><a name="20260" href="Stlc.html#5496" class="InductiveConstructor Operator"
      >&#8658;</a
      ><a name="20261"
      > </a
      ><a name="20262" class="Symbol"
      >(</a
      ><a name="20263" href="Stlc.html#5482" class="InductiveConstructor"
      >bool</a
      ><a name="20267"
      > </a
      ><a name="20268" href="Stlc.html#5496" class="InductiveConstructor Operator"
      >&#8658;</a
      ><a name="20269"
      > </a
      ><a name="20270" href="Stlc.html#5482" class="InductiveConstructor"
      >bool</a
      ><a name="20274" class="Symbol"
      >)</a
      ><a name="20275"
      > </a
      ><a name="20276" href="Stlc.html#5496" class="InductiveConstructor Operator"
      >&#8658;</a
      ><a name="20277"
      > </a
      ><a name="20278" href="Stlc.html#5482" class="InductiveConstructor"
      >bool</a
      ><a name="20282" class="Symbol"
      >)</a
      ><a name="20283"
      >
</a
      ><a name="20284" href="Stlc.html#20137" class="Function"
      >typing-example2</a
      ><a name="20299"
      > </a
      ><a name="20300" class="Symbol"
      >=</a
      ><a name="20301"
      >
  </a
      ><a name="20304" class="Symbol"
      >(</a
      ><a name="20305" href="Stlc.html#19256" class="InductiveConstructor"
      >abs</a
      ><a name="20308"
      >
    </a
      ><a name="20313" class="Symbol"
      >(</a
      ><a name="20314" href="Stlc.html#19256" class="InductiveConstructor"
      >abs</a
      ><a name="20317"
      >
      </a
      ><a name="20324" class="Symbol"
      >(</a
      ><a name="20325" href="Stlc.html#19372" class="InductiveConstructor"
      >app</a
      ><a name="20328"
      > </a
      ><a name="20329" class="Symbol"
      >(</a
      ><a name="20330" href="Stlc.html#19163" class="InductiveConstructor"
      >var</a
      ><a name="20333"
      > </a
      ><a name="20334" href="Stlc.html#6238" class="Function"
      >y</a
      ><a name="20335"
      > </a
      ><a name="20336" href="Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="20340" class="Symbol"
      >)</a
      ><a name="20341"
      >
        </a
      ><a name="20350" class="Symbol"
      >(</a
      ><a name="20351" href="Stlc.html#19372" class="InductiveConstructor"
      >app</a
      ><a name="20354"
      > </a
      ><a name="20355" class="Symbol"
      >(</a
      ><a name="20356" href="Stlc.html#19163" class="InductiveConstructor"
      >var</a
      ><a name="20359"
      > </a
      ><a name="20360" href="Stlc.html#6238" class="Function"
      >y</a
      ><a name="20361"
      > </a
      ><a name="20362" href="Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="20366" class="Symbol"
      >)</a
      ><a name="20367"
      > </a
      ><a name="20368" class="Symbol"
      >(</a
      ><a name="20369" href="Stlc.html#19163" class="InductiveConstructor"
      >var</a
      ><a name="20372"
      > </a
      ><a name="20373" href="Stlc.html#6229" class="Function"
      >x</a
      ><a name="20374"
      > </a
      ><a name="20375" href="Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="20379" class="Symbol"
      >)</a
      ><a name="20380"
      > </a
      ><a name="20381" class="Symbol"
      >))))</a
      >
{% endraw %}</pre>

#### Exercise: 2 stars (typing-example3)
Formally prove the following typing derivation holds:

$$\exists A, \varnothing\vdash \lambda x:bool\rightarrow B. \lambda y:bool\rightarrow bool. \lambda z:bool. y\;(x\;z) : A$$.

<pre class="Agda">{% raw %}
<a name="20633" class="Keyword"
      >postulate</a
      ><a name="20642"
      >
  </a
      ><a name="20645" href="Stlc.html#20645" class="Postulate"
      >typing-example3</a
      ><a name="20660"
      > </a
      ><a name="20661" class="Symbol"
      >:</a
      ><a name="20662"
      > </a
      ><a name="20663" href="https://agda.github.io/agda-stdlib/Data.Product.html#823" class="Function"
      >&#8707;</a
      ><a name="20664"
      > </a
      ><a name="20665" class="Symbol"
      >&#955;</a
      ><a name="20666"
      > </a
      ><a name="20667" href="Stlc.html#20667" class="Bound"
      >A</a
      ><a name="20668"
      > </a
      ><a name="20669" class="Symbol"
      >&#8594;</a
      ><a name="20670"
      > </a
      ><a name="20671" href="Stlc.html#18187" class="Function"
      >&#8709;</a
      ><a name="20672"
      > </a
      ><a name="20673" href="Stlc.html#19119" class="Datatype Operator"
      >&#8866;</a
      ><a name="20674"
      >
    </a
      ><a name="20679" class="Symbol"
      >(</a
      ><a name="20680" href="Stlc.html#5698" class="InductiveConstructor"
      >abs</a
      ><a name="20683"
      > </a
      ><a name="20684" href="Stlc.html#6229" class="Function"
      >x</a
      ><a name="20685"
      > </a
      ><a name="20686" class="Symbol"
      >(</a
      ><a name="20687" href="Stlc.html#5482" class="InductiveConstructor"
      >bool</a
      ><a name="20691"
      > </a
      ><a name="20692" href="Stlc.html#5496" class="InductiveConstructor Operator"
      >&#8658;</a
      ><a name="20693"
      > </a
      ><a name="20694" href="Stlc.html#5482" class="InductiveConstructor"
      >bool</a
      ><a name="20698" class="Symbol"
      >)</a
      ><a name="20699"
      >
      </a
      ><a name="20706" class="Symbol"
      >(</a
      ><a name="20707" href="Stlc.html#5698" class="InductiveConstructor"
      >abs</a
      ><a name="20710"
      > </a
      ><a name="20711" href="Stlc.html#6238" class="Function"
      >y</a
      ><a name="20712"
      > </a
      ><a name="20713" class="Symbol"
      >(</a
      ><a name="20714" href="Stlc.html#5482" class="InductiveConstructor"
      >bool</a
      ><a name="20718"
      > </a
      ><a name="20719" href="Stlc.html#5496" class="InductiveConstructor Operator"
      >&#8658;</a
      ><a name="20720"
      > </a
      ><a name="20721" href="Stlc.html#5482" class="InductiveConstructor"
      >bool</a
      ><a name="20725" class="Symbol"
      >)</a
      ><a name="20726"
      >
        </a
      ><a name="20735" class="Symbol"
      >(</a
      ><a name="20736" href="Stlc.html#5698" class="InductiveConstructor"
      >abs</a
      ><a name="20739"
      > </a
      ><a name="20740" href="Stlc.html#6247" class="Function"
      >z</a
      ><a name="20741"
      > </a
      ><a name="20742" href="Stlc.html#5482" class="InductiveConstructor"
      >bool</a
      ><a name="20746"
      >
          </a
      ><a name="20757" class="Symbol"
      >(</a
      ><a name="20758" href="Stlc.html#5669" class="InductiveConstructor"
      >app</a
      ><a name="20761"
      > </a
      ><a name="20762" class="Symbol"
      >(</a
      ><a name="20763" href="Stlc.html#5649" class="InductiveConstructor"
      >var</a
      ><a name="20766"
      > </a
      ><a name="20767" href="Stlc.html#6238" class="Function"
      >y</a
      ><a name="20768" class="Symbol"
      >)</a
      ><a name="20769"
      > </a
      ><a name="20770" class="Symbol"
      >(</a
      ><a name="20771" href="Stlc.html#5669" class="InductiveConstructor"
      >app</a
      ><a name="20774"
      > </a
      ><a name="20775" class="Symbol"
      >(</a
      ><a name="20776" href="Stlc.html#5649" class="InductiveConstructor"
      >var</a
      ><a name="20779"
      > </a
      ><a name="20780" href="Stlc.html#6229" class="Function"
      >x</a
      ><a name="20781" class="Symbol"
      >)</a
      ><a name="20782"
      > </a
      ><a name="20783" class="Symbol"
      >(</a
      ><a name="20784" href="Stlc.html#5649" class="InductiveConstructor"
      >var</a
      ><a name="20787"
      > </a
      ><a name="20788" href="Stlc.html#6247" class="Function"
      >z</a
      ><a name="20789" class="Symbol"
      >))))))</a
      ><a name="20795"
      > </a
      ><a name="20796" href="Stlc.html#19119" class="Datatype Operator"
      >&#8758;</a
      ><a name="20797"
      > </a
      ><a name="20798" href="Stlc.html#20667" class="Bound"
      >A</a
      >
{% endraw %}</pre>

We can also show that terms are _not_ typable.  For example, let's
formally check that there is no typing derivation assigning a type
to the term $$\lambda x:bool. \lambda y:bool. x\;y$$---i.e.,


$$\nexists A, \varnothing\vdash \lambda x:bool. \lambda y:bool. x\;y : A$$.

<pre class="Agda">{% raw %}
<a name="21099" class="Keyword"
      >postulate</a
      ><a name="21108"
      >
  </a
      ><a name="21111" href="Stlc.html#21111" class="Postulate"
      >typing-nonexample1</a
      ><a name="21129"
      > </a
      ><a name="21130" class="Symbol"
      >:</a
      ><a name="21131"
      > </a
      ><a name="21132" href="https://agda.github.io/agda-stdlib/Data.Product.html#884" class="Function"
      >&#8708;</a
      ><a name="21133"
      > </a
      ><a name="21134" class="Symbol"
      >&#955;</a
      ><a name="21135"
      > </a
      ><a name="21136" href="Stlc.html#21136" class="Bound"
      >A</a
      ><a name="21137"
      > </a
      ><a name="21138" class="Symbol"
      >&#8594;</a
      ><a name="21139"
      > </a
      ><a name="21140" href="Stlc.html#18187" class="Function"
      >&#8709;</a
      ><a name="21141"
      > </a
      ><a name="21142" href="Stlc.html#19119" class="Datatype Operator"
      >&#8866;</a
      ><a name="21143"
      >
    </a
      ><a name="21148" class="Symbol"
      >(</a
      ><a name="21149" href="Stlc.html#5698" class="InductiveConstructor"
      >abs</a
      ><a name="21152"
      > </a
      ><a name="21153" href="Stlc.html#6229" class="Function"
      >x</a
      ><a name="21154"
      > </a
      ><a name="21155" href="Stlc.html#5482" class="InductiveConstructor"
      >bool</a
      ><a name="21159"
      >
      </a
      ><a name="21166" class="Symbol"
      >(</a
      ><a name="21167" href="Stlc.html#5698" class="InductiveConstructor"
      >abs</a
      ><a name="21170"
      > </a
      ><a name="21171" href="Stlc.html#6238" class="Function"
      >y</a
      ><a name="21172"
      > </a
      ><a name="21173" href="Stlc.html#5482" class="InductiveConstructor"
      >bool</a
      ><a name="21177"
      >
        </a
      ><a name="21186" class="Symbol"
      >(</a
      ><a name="21187" href="Stlc.html#5669" class="InductiveConstructor"
      >app</a
      ><a name="21190"
      > </a
      ><a name="21191" class="Symbol"
      >(</a
      ><a name="21192" href="Stlc.html#5649" class="InductiveConstructor"
      >var</a
      ><a name="21195"
      > </a
      ><a name="21196" href="Stlc.html#6229" class="Function"
      >x</a
      ><a name="21197" class="Symbol"
      >)</a
      ><a name="21198"
      > </a
      ><a name="21199" class="Symbol"
      >(</a
      ><a name="21200" href="Stlc.html#5649" class="InductiveConstructor"
      >var</a
      ><a name="21203"
      > </a
      ><a name="21204" href="Stlc.html#6238" class="Function"
      >y</a
      ><a name="21205" class="Symbol"
      >))))</a
      ><a name="21209"
      > </a
      ><a name="21210" href="Stlc.html#19119" class="Datatype Operator"
      >&#8758;</a
      ><a name="21211"
      > </a
      ><a name="21212" href="Stlc.html#21136" class="Bound"
      >A</a
      >
{% endraw %}</pre>

#### Exercise: 3 stars, optional (typing-nonexample2)
Another nonexample:

$$\nexists A, \exists B, \varnothing\vdash \lambda x:A. x\;x : B$$.

<pre class="Agda">{% raw %}
<a name="21383" class="Keyword"
      >postulate</a
      ><a name="21392"
      >
  </a
      ><a name="21395" href="Stlc.html#21395" class="Postulate"
      >typing-nonexample2</a
      ><a name="21413"
      > </a
      ><a name="21414" class="Symbol"
      >:</a
      ><a name="21415"
      > </a
      ><a name="21416" href="https://agda.github.io/agda-stdlib/Data.Product.html#884" class="Function"
      >&#8708;</a
      ><a name="21417"
      > </a
      ><a name="21418" class="Symbol"
      >&#955;</a
      ><a name="21419"
      > </a
      ><a name="21420" href="Stlc.html#21420" class="Bound"
      >A</a
      ><a name="21421"
      > </a
      ><a name="21422" class="Symbol"
      >&#8594;</a
      ><a name="21423"
      > </a
      ><a name="21424" href="https://agda.github.io/agda-stdlib/Data.Product.html#823" class="Function"
      >&#8707;</a
      ><a name="21425"
      > </a
      ><a name="21426" class="Symbol"
      >&#955;</a
      ><a name="21427"
      > </a
      ><a name="21428" href="Stlc.html#21428" class="Bound"
      >B</a
      ><a name="21429"
      > </a
      ><a name="21430" class="Symbol"
      >&#8594;</a
      ><a name="21431"
      > </a
      ><a name="21432" href="Stlc.html#18187" class="Function"
      >&#8709;</a
      ><a name="21433"
      > </a
      ><a name="21434" href="Stlc.html#19119" class="Datatype Operator"
      >&#8866;</a
      ><a name="21435"
      >
    </a
      ><a name="21440" class="Symbol"
      >(</a
      ><a name="21441" href="Stlc.html#5698" class="InductiveConstructor"
      >abs</a
      ><a name="21444"
      > </a
      ><a name="21445" href="Stlc.html#6229" class="Function"
      >x</a
      ><a name="21446"
      > </a
      ><a name="21447" href="Stlc.html#21428" class="Bound"
      >B</a
      ><a name="21448"
      > </a
      ><a name="21449" class="Symbol"
      >(</a
      ><a name="21450" href="Stlc.html#5669" class="InductiveConstructor"
      >app</a
      ><a name="21453"
      > </a
      ><a name="21454" class="Symbol"
      >(</a
      ><a name="21455" href="Stlc.html#5649" class="InductiveConstructor"
      >var</a
      ><a name="21458"
      > </a
      ><a name="21459" href="Stlc.html#6229" class="Function"
      >x</a
      ><a name="21460" class="Symbol"
      >)</a
      ><a name="21461"
      > </a
      ><a name="21462" class="Symbol"
      >(</a
      ><a name="21463" href="Stlc.html#5649" class="InductiveConstructor"
      >var</a
      ><a name="21466"
      > </a
      ><a name="21467" href="Stlc.html#6229" class="Function"
      >x</a
      ><a name="21468" class="Symbol"
      >)))</a
      ><a name="21471"
      > </a
      ><a name="21472" href="Stlc.html#19119" class="Datatype Operator"
      >&#8758;</a
      ><a name="21473"
      > </a
      ><a name="21474" href="Stlc.html#21420" class="Bound"
      >A</a
      >
{% endraw %}</pre>
