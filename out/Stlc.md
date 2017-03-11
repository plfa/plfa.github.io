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
      ><a name="158" href="Maps.html#2275" class="Datatype"
      >Id</a
      ><a name="160" class="Symbol"
      >;</a
      ><a name="161"
      > </a
      ><a name="162" href="Maps.html#2292" class="InductiveConstructor"
      >id</a
      ><a name="164" class="Symbol"
      >;</a
      ><a name="165"
      > </a
      ><a name="166" href="Maps.html#2329" class="Function Operator"
      >_&#8799;_</a
      ><a name="169" class="Symbol"
      >;</a
      ><a name="170"
      > </a
      ><a name="171" href="Maps.html#9394" class="Function"
      >PartialMap</a
      ><a name="181" class="Symbol"
      >;</a
      ><a name="182"
      > </a
      ><a name="183" class="Keyword"
      >module</a
      ><a name="189"
      > </a
      ><a name="190" href="Maps.html#9483" class="Module"
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
      ><a name="235" href="https://agda.github.io/agda-stdlib/Data.Empty.html#348" class="Function"
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
      ><a name="323" href="Agda.Builtin.Nat.html#97" class="Datatype"
      >&#8469;</a
      ><a name="324" class="Symbol"
      >;</a
      ><a name="325"
      > </a
      ><a name="326" href="Agda.Builtin.Nat.html#128" class="InductiveConstructor"
      >suc</a
      ><a name="329" class="Symbol"
      >;</a
      ><a name="330"
      > </a
      ><a name="331" href="Agda.Builtin.Nat.html#115" class="InductiveConstructor"
      >zero</a
      ><a name="335" class="Symbol"
      >;</a
      ><a name="336"
      > </a
      ><a name="337" href="Agda.Builtin.Nat.html#230" class="Primitive Operator"
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
      ><a name="530" href="Agda.Builtin.Equality.html#83" class="Datatype Operator"
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
      ><a name="540" href="Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="544" class="Symbol"
      >)</a
      >
{% endraw %}</pre>
</div>

# Stlc: The Simply Typed Lambda-Calculus

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
<a name="5423" class="Keyword"
      >data</a
      ><a name="5427"
      > </a
      ><a name="5428" href="Stlc.html#5428" class="Datatype"
      >Type</a
      ><a name="5432"
      > </a
      ><a name="5433" class="Symbol"
      >:</a
      ><a name="5434"
      > </a
      ><a name="5435" class="PrimitiveType"
      >Set</a
      ><a name="5438"
      > </a
      ><a name="5439" class="Keyword"
      >where</a
      ><a name="5444"
      >
  </a
      ><a name="5447" href="Stlc.html#5447" class="InductiveConstructor"
      >bool</a
      ><a name="5451"
      > </a
      ><a name="5452" class="Symbol"
      >:</a
      ><a name="5453"
      > </a
      ><a name="5454" href="Stlc.html#5428" class="Datatype"
      >Type</a
      ><a name="5458"
      >
  </a
      ><a name="5461" href="Stlc.html#5461" class="InductiveConstructor Operator"
      >_&#8658;_</a
      ><a name="5464"
      >  </a
      ><a name="5466" class="Symbol"
      >:</a
      ><a name="5467"
      > </a
      ><a name="5468" href="Stlc.html#5428" class="Datatype"
      >Type</a
      ><a name="5472"
      > </a
      ><a name="5473" class="Symbol"
      >&#8594;</a
      ><a name="5474"
      > </a
      ><a name="5475" href="Stlc.html#5428" class="Datatype"
      >Type</a
      ><a name="5479"
      > </a
      ><a name="5480" class="Symbol"
      >&#8594;</a
      ><a name="5481"
      > </a
      ><a name="5482" href="Stlc.html#5428" class="Datatype"
      >Type</a
      ><a name="5486"
      >

</a
      ><a name="5488" class="Keyword"
      >infixr</a
      ><a name="5494"
      > </a
      ><a name="5495" class="Number"
      >5</a
      ><a name="5496"
      > </a
      ><a name="5497" href="Stlc.html#5461" class="InductiveConstructor Operator"
      >_&#8658;_</a
      >
{% endraw %}</pre>


### Terms

<pre class="Agda">{% raw %}
<a name="5538" class="Keyword"
      >data</a
      ><a name="5542"
      > </a
      ><a name="5543" href="Stlc.html#5543" class="Datatype"
      >Term</a
      ><a name="5547"
      > </a
      ><a name="5548" class="Symbol"
      >:</a
      ><a name="5549"
      > </a
      ><a name="5550" class="PrimitiveType"
      >Set</a
      ><a name="5553"
      > </a
      ><a name="5554" class="Keyword"
      >where</a
      ><a name="5559"
      >
  </a
      ><a name="5562" href="Stlc.html#5562" class="InductiveConstructor"
      >var</a
      ><a name="5565"
      >   </a
      ><a name="5568" class="Symbol"
      >:</a
      ><a name="5569"
      > </a
      ><a name="5570" href="Maps.html#2275" class="Datatype"
      >Id</a
      ><a name="5572"
      > </a
      ><a name="5573" class="Symbol"
      >&#8594;</a
      ><a name="5574"
      > </a
      ><a name="5575" href="Stlc.html#5543" class="Datatype"
      >Term</a
      ><a name="5579"
      >
  </a
      ><a name="5582" href="Stlc.html#5582" class="InductiveConstructor"
      >app</a
      ><a name="5585"
      >   </a
      ><a name="5588" class="Symbol"
      >:</a
      ><a name="5589"
      > </a
      ><a name="5590" href="Stlc.html#5543" class="Datatype"
      >Term</a
      ><a name="5594"
      > </a
      ><a name="5595" class="Symbol"
      >&#8594;</a
      ><a name="5596"
      > </a
      ><a name="5597" href="Stlc.html#5543" class="Datatype"
      >Term</a
      ><a name="5601"
      > </a
      ><a name="5602" class="Symbol"
      >&#8594;</a
      ><a name="5603"
      > </a
      ><a name="5604" href="Stlc.html#5543" class="Datatype"
      >Term</a
      ><a name="5608"
      >
  </a
      ><a name="5611" href="Stlc.html#5611" class="InductiveConstructor"
      >abs</a
      ><a name="5614"
      >   </a
      ><a name="5617" class="Symbol"
      >:</a
      ><a name="5618"
      > </a
      ><a name="5619" href="Maps.html#2275" class="Datatype"
      >Id</a
      ><a name="5621"
      > </a
      ><a name="5622" class="Symbol"
      >&#8594;</a
      ><a name="5623"
      > </a
      ><a name="5624" href="Stlc.html#5428" class="Datatype"
      >Type</a
      ><a name="5628"
      > </a
      ><a name="5629" class="Symbol"
      >&#8594;</a
      ><a name="5630"
      > </a
      ><a name="5631" href="Stlc.html#5543" class="Datatype"
      >Term</a
      ><a name="5635"
      > </a
      ><a name="5636" class="Symbol"
      >&#8594;</a
      ><a name="5637"
      > </a
      ><a name="5638" href="Stlc.html#5543" class="Datatype"
      >Term</a
      ><a name="5642"
      >
  </a
      ><a name="5645" href="Stlc.html#5645" class="InductiveConstructor"
      >true</a
      ><a name="5649"
      >  </a
      ><a name="5651" class="Symbol"
      >:</a
      ><a name="5652"
      > </a
      ><a name="5653" href="Stlc.html#5543" class="Datatype"
      >Term</a
      ><a name="5657"
      >
  </a
      ><a name="5660" href="Stlc.html#5660" class="InductiveConstructor"
      >false</a
      ><a name="5665"
      > </a
      ><a name="5666" class="Symbol"
      >:</a
      ><a name="5667"
      > </a
      ><a name="5668" href="Stlc.html#5543" class="Datatype"
      >Term</a
      ><a name="5672"
      >
  </a
      ><a name="5675" href="Stlc.html#5675" class="InductiveConstructor Operator"
      >if_then_else_</a
      ><a name="5688"
      > </a
      ><a name="5689" class="Symbol"
      >:</a
      ><a name="5690"
      > </a
      ><a name="5691" href="Stlc.html#5543" class="Datatype"
      >Term</a
      ><a name="5695"
      > </a
      ><a name="5696" class="Symbol"
      >&#8594;</a
      ><a name="5697"
      > </a
      ><a name="5698" href="Stlc.html#5543" class="Datatype"
      >Term</a
      ><a name="5702"
      > </a
      ><a name="5703" class="Symbol"
      >&#8594;</a
      ><a name="5704"
      > </a
      ><a name="5705" href="Stlc.html#5543" class="Datatype"
      >Term</a
      ><a name="5709"
      > </a
      ><a name="5710" class="Symbol"
      >&#8594;</a
      ><a name="5711"
      > </a
      ><a name="5712" href="Stlc.html#5543" class="Datatype"
      >Term</a
      >
{% endraw %}</pre>

<div class="hidden">
<pre class="Agda">{% raw %}
<a name="5763" class="Keyword"
      >infixr</a
      ><a name="5769"
      > </a
      ><a name="5770" class="Number"
      >8</a
      ><a name="5771"
      > </a
      ><a name="5772" href="Stlc.html#19605" class="InductiveConstructor Operator"
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
<a name="6244" href="Stlc.html#6244" class="Function"
      >x</a
      ><a name="6245"
      > </a
      ><a name="6246" class="Symbol"
      >=</a
      ><a name="6247"
      > </a
      ><a name="6248" href="Maps.html#2292" class="InductiveConstructor"
      >id</a
      ><a name="6250"
      > </a
      ><a name="6251" class="Number"
      >0</a
      ><a name="6252"
      >
</a
      ><a name="6253" href="Stlc.html#6253" class="Function"
      >y</a
      ><a name="6254"
      > </a
      ><a name="6255" class="Symbol"
      >=</a
      ><a name="6256"
      > </a
      ><a name="6257" href="Maps.html#2292" class="InductiveConstructor"
      >id</a
      ><a name="6259"
      > </a
      ><a name="6260" class="Number"
      >1</a
      ><a name="6261"
      >
</a
      ><a name="6262" href="Stlc.html#6262" class="Function"
      >z</a
      ><a name="6263"
      > </a
      ><a name="6264" class="Symbol"
      >=</a
      ><a name="6265"
      > </a
      ><a name="6266" href="Maps.html#2292" class="InductiveConstructor"
      >id</a
      ><a name="6268"
      > </a
      ><a name="6269" class="Number"
      >2</a
      ><a name="6270"
      >

</a
      ><a name="6272" class="Symbol"
      >{-#</a
      ><a name="6275"
      > </a
      ><a name="6276" class="Keyword"
      >DISPLAY</a
      ><a name="6283"
      > </a
      ><a name="6284" href="Maps.html#2292" class="InductiveConstructor"
      >id</a
      ><a name="6286"
      > </a
      ><a name="6287" href="Agda.Builtin.Nat.html#115" class="InductiveConstructor"
      >zero</a
      ><a name="6291"
      > = </a
      ><a name="6294" href="Stlc.html#6244" class="Function"
      >x</a
      ><a name="6295"
      > </a
      ><a name="6296" class="Symbol"
      >#-}</a
      ><a name="6299"
      >
</a
      ><a name="6300" class="Symbol"
      >{-#</a
      ><a name="6303"
      > </a
      ><a name="6304" class="Keyword"
      >DISPLAY</a
      ><a name="6311"
      > </a
      ><a name="6312" href="Maps.html#2292" class="InductiveConstructor"
      >id</a
      ><a name="6314"
      > (</a
      ><a name="6316" href="Agda.Builtin.Nat.html#128" class="InductiveConstructor"
      >suc</a
      ><a name="6319"
      > </a
      ><a name="6320" href="Agda.Builtin.Nat.html#115" class="InductiveConstructor"
      >zero</a
      ><a name="6324"
      >) = </a
      ><a name="6328" href="Stlc.html#6253" class="Function"
      >y</a
      ><a name="6329"
      > </a
      ><a name="6330" class="Symbol"
      >#-}</a
      ><a name="6333"
      >
</a
      ><a name="6334" class="Symbol"
      >{-#</a
      ><a name="6337"
      > </a
      ><a name="6338" class="Keyword"
      >DISPLAY</a
      ><a name="6345"
      > </a
      ><a name="6346" href="Maps.html#2292" class="InductiveConstructor"
      >id</a
      ><a name="6348"
      > (</a
      ><a name="6350" href="Agda.Builtin.Nat.html#128" class="InductiveConstructor"
      >suc</a
      ><a name="6353"
      > (</a
      ><a name="6355" href="Agda.Builtin.Nat.html#128" class="InductiveConstructor"
      >suc</a
      ><a name="6358"
      > </a
      ><a name="6359" href="Agda.Builtin.Nat.html#115" class="InductiveConstructor"
      >zero</a
      ><a name="6363"
      >)) = </a
      ><a name="6368" href="Stlc.html#6262" class="Function"
      >z</a
      ><a name="6369"
      > </a
      ><a name="6370" class="Symbol"
      >#-}</a
      >
{% endraw %}</pre>

Some examples...

$$\text{idB} = \lambda x:bool. x$$.

<pre class="Agda">{% raw %}
<a name="6454" href="Stlc.html#6454" class="Function"
      >idB</a
      ><a name="6457"
      > </a
      ><a name="6458" class="Symbol"
      >=</a
      ><a name="6459"
      > </a
      ><a name="6460" class="Symbol"
      >(</a
      ><a name="6461" href="Stlc.html#5611" class="InductiveConstructor"
      >abs</a
      ><a name="6464"
      > </a
      ><a name="6465" href="Stlc.html#6244" class="Function"
      >x</a
      ><a name="6466"
      > </a
      ><a name="6467" href="Stlc.html#5447" class="InductiveConstructor"
      >bool</a
      ><a name="6471"
      > </a
      ><a name="6472" class="Symbol"
      >(</a
      ><a name="6473" href="Stlc.html#5562" class="InductiveConstructor"
      >var</a
      ><a name="6476"
      > </a
      ><a name="6477" href="Stlc.html#6244" class="Function"
      >x</a
      ><a name="6478" class="Symbol"
      >))</a
      >
{% endraw %}</pre>

$$\text{idBB} = \lambda x:bool\rightarrow bool. x$$.

<pre class="Agda">{% raw %}
<a name="6560" href="Stlc.html#6560" class="Function"
      >idBB</a
      ><a name="6564"
      > </a
      ><a name="6565" class="Symbol"
      >=</a
      ><a name="6566"
      > </a
      ><a name="6567" class="Symbol"
      >(</a
      ><a name="6568" href="Stlc.html#5611" class="InductiveConstructor"
      >abs</a
      ><a name="6571"
      > </a
      ><a name="6572" href="Stlc.html#6244" class="Function"
      >x</a
      ><a name="6573"
      > </a
      ><a name="6574" class="Symbol"
      >(</a
      ><a name="6575" href="Stlc.html#5447" class="InductiveConstructor"
      >bool</a
      ><a name="6579"
      > </a
      ><a name="6580" href="Stlc.html#5461" class="InductiveConstructor Operator"
      >&#8658;</a
      ><a name="6581"
      > </a
      ><a name="6582" href="Stlc.html#5447" class="InductiveConstructor"
      >bool</a
      ><a name="6586" class="Symbol"
      >)</a
      ><a name="6587"
      > </a
      ><a name="6588" class="Symbol"
      >(</a
      ><a name="6589" href="Stlc.html#5562" class="InductiveConstructor"
      >var</a
      ><a name="6592"
      > </a
      ><a name="6593" href="Stlc.html#6244" class="Function"
      >x</a
      ><a name="6594" class="Symbol"
      >))</a
      >
{% endraw %}</pre>

$$\text{idBBBB} = \lambda x:(bool\rightarrow bool)\rightarrow (bool\rightarrow bool). x$$.

<pre class="Agda">{% raw %}
<a name="6714" href="Stlc.html#6714" class="Function"
      >idBBBB</a
      ><a name="6720"
      > </a
      ><a name="6721" class="Symbol"
      >=</a
      ><a name="6722"
      > </a
      ><a name="6723" class="Symbol"
      >(</a
      ><a name="6724" href="Stlc.html#5611" class="InductiveConstructor"
      >abs</a
      ><a name="6727"
      > </a
      ><a name="6728" href="Stlc.html#6244" class="Function"
      >x</a
      ><a name="6729"
      > </a
      ><a name="6730" class="Symbol"
      >((</a
      ><a name="6732" href="Stlc.html#5447" class="InductiveConstructor"
      >bool</a
      ><a name="6736"
      > </a
      ><a name="6737" href="Stlc.html#5461" class="InductiveConstructor Operator"
      >&#8658;</a
      ><a name="6738"
      > </a
      ><a name="6739" href="Stlc.html#5447" class="InductiveConstructor"
      >bool</a
      ><a name="6743" class="Symbol"
      >)</a
      ><a name="6744"
      > </a
      ><a name="6745" href="Stlc.html#5461" class="InductiveConstructor Operator"
      >&#8658;</a
      ><a name="6746"
      > </a
      ><a name="6747" class="Symbol"
      >(</a
      ><a name="6748" href="Stlc.html#5447" class="InductiveConstructor"
      >bool</a
      ><a name="6752"
      > </a
      ><a name="6753" href="Stlc.html#5461" class="InductiveConstructor Operator"
      >&#8658;</a
      ><a name="6754"
      > </a
      ><a name="6755" href="Stlc.html#5447" class="InductiveConstructor"
      >bool</a
      ><a name="6759" class="Symbol"
      >))</a
      ><a name="6761"
      > </a
      ><a name="6762" class="Symbol"
      >(</a
      ><a name="6763" href="Stlc.html#5562" class="InductiveConstructor"
      >var</a
      ><a name="6766"
      > </a
      ><a name="6767" href="Stlc.html#6244" class="Function"
      >x</a
      ><a name="6768" class="Symbol"
      >))</a
      >
{% endraw %}</pre>

$$\text{k} = \lambda x:bool. \lambda y:bool. x$$.

<pre class="Agda">{% raw %}
<a name="6847" href="Stlc.html#6847" class="Function"
      >k</a
      ><a name="6848"
      > </a
      ><a name="6849" class="Symbol"
      >=</a
      ><a name="6850"
      > </a
      ><a name="6851" class="Symbol"
      >(</a
      ><a name="6852" href="Stlc.html#5611" class="InductiveConstructor"
      >abs</a
      ><a name="6855"
      > </a
      ><a name="6856" href="Stlc.html#6244" class="Function"
      >x</a
      ><a name="6857"
      > </a
      ><a name="6858" href="Stlc.html#5447" class="InductiveConstructor"
      >bool</a
      ><a name="6862"
      > </a
      ><a name="6863" class="Symbol"
      >(</a
      ><a name="6864" href="Stlc.html#5611" class="InductiveConstructor"
      >abs</a
      ><a name="6867"
      > </a
      ><a name="6868" href="Stlc.html#6253" class="Function"
      >y</a
      ><a name="6869"
      > </a
      ><a name="6870" href="Stlc.html#5447" class="InductiveConstructor"
      >bool</a
      ><a name="6874"
      > </a
      ><a name="6875" class="Symbol"
      >(</a
      ><a name="6876" href="Stlc.html#5562" class="InductiveConstructor"
      >var</a
      ><a name="6879"
      > </a
      ><a name="6880" href="Stlc.html#6244" class="Function"
      >x</a
      ><a name="6881" class="Symbol"
      >)))</a
      >
{% endraw %}</pre>

$$\text{notB} = \lambda x:bool. \text{if }x\text{ then }false\text{ else }true$$.

<pre class="Agda">{% raw %}
<a name="6993" href="Stlc.html#6993" class="Function"
      >notB</a
      ><a name="6997"
      > </a
      ><a name="6998" class="Symbol"
      >=</a
      ><a name="6999"
      > </a
      ><a name="7000" class="Symbol"
      >(</a
      ><a name="7001" href="Stlc.html#5611" class="InductiveConstructor"
      >abs</a
      ><a name="7004"
      > </a
      ><a name="7005" href="Stlc.html#6244" class="Function"
      >x</a
      ><a name="7006"
      > </a
      ><a name="7007" href="Stlc.html#5447" class="InductiveConstructor"
      >bool</a
      ><a name="7011"
      > </a
      ><a name="7012" class="Symbol"
      >(</a
      ><a name="7013" href="Stlc.html#5675" class="InductiveConstructor Operator"
      >if</a
      ><a name="7015"
      > </a
      ><a name="7016" class="Symbol"
      >(</a
      ><a name="7017" href="Stlc.html#5562" class="InductiveConstructor"
      >var</a
      ><a name="7020"
      > </a
      ><a name="7021" href="Stlc.html#6244" class="Function"
      >x</a
      ><a name="7022" class="Symbol"
      >)</a
      ><a name="7023"
      > </a
      ><a name="7024" href="Stlc.html#5675" class="InductiveConstructor Operator"
      >then</a
      ><a name="7028"
      > </a
      ><a name="7029" href="Stlc.html#5660" class="InductiveConstructor"
      >false</a
      ><a name="7034"
      > </a
      ><a name="7035" href="Stlc.html#5675" class="InductiveConstructor Operator"
      >else</a
      ><a name="7039"
      > </a
      ><a name="7040" href="Stlc.html#5645" class="InductiveConstructor"
      >true</a
      ><a name="7044" class="Symbol"
      >))</a
      >
{% endraw %}</pre>

<div class="hidden">
<pre class="Agda">{% raw %}
<a name="7093" class="Symbol"
      >{-#</a
      ><a name="7096"
      > </a
      ><a name="7097" class="Keyword"
      >DISPLAY</a
      ><a name="7104"
      > </a
      ><a name="7105" href="Stlc.html#5611" class="InductiveConstructor"
      >abs</a
      ><a name="7108"
      > 0 </a
      ><a name="7111" href="Stlc.html#5447" class="InductiveConstructor"
      >bool</a
      ><a name="7115"
      > (</a
      ><a name="7117" href="Stlc.html#5562" class="InductiveConstructor"
      >var</a
      ><a name="7120"
      > 0) = </a
      ><a name="7126" href="Stlc.html#6454" class="Function"
      >idB</a
      ><a name="7129"
      > </a
      ><a name="7130" class="Symbol"
      >#-}</a
      ><a name="7133"
      >
</a
      ><a name="7134" class="Symbol"
      >{-#</a
      ><a name="7137"
      > </a
      ><a name="7138" class="Keyword"
      >DISPLAY</a
      ><a name="7145"
      > </a
      ><a name="7146" href="Stlc.html#5611" class="InductiveConstructor"
      >abs</a
      ><a name="7149"
      > 0 (</a
      ><a name="7153" href="Stlc.html#5447" class="InductiveConstructor"
      >bool</a
      ><a name="7157"
      > </a
      ><a name="7158" href="Stlc.html#5461" class="InductiveConstructor Operator"
      >&#8658;</a
      ><a name="7159"
      > </a
      ><a name="7160" href="Stlc.html#5447" class="InductiveConstructor"
      >bool</a
      ><a name="7164"
      >) (</a
      ><a name="7167" href="Stlc.html#5562" class="InductiveConstructor"
      >var</a
      ><a name="7170"
      > 0) = </a
      ><a name="7176" href="Stlc.html#6560" class="Function"
      >idBB</a
      ><a name="7180"
      > </a
      ><a name="7181" class="Symbol"
      >#-}</a
      ><a name="7184"
      >
</a
      ><a name="7185" class="Symbol"
      >{-#</a
      ><a name="7188"
      > </a
      ><a name="7189" class="Keyword"
      >DISPLAY</a
      ><a name="7196"
      > </a
      ><a name="7197" href="Stlc.html#5611" class="InductiveConstructor"
      >abs</a
      ><a name="7200"
      > 0 ((</a
      ><a name="7205" href="Stlc.html#5447" class="InductiveConstructor"
      >bool</a
      ><a name="7209"
      > </a
      ><a name="7210" href="Stlc.html#5461" class="InductiveConstructor Operator"
      >&#8658;</a
      ><a name="7211"
      > </a
      ><a name="7212" href="Stlc.html#5447" class="InductiveConstructor"
      >bool</a
      ><a name="7216"
      >) </a
      ><a name="7218" href="Stlc.html#5461" class="InductiveConstructor Operator"
      >&#8658;</a
      ><a name="7219"
      > (</a
      ><a name="7221" href="Stlc.html#5447" class="InductiveConstructor"
      >bool</a
      ><a name="7225"
      > </a
      ><a name="7226" href="Stlc.html#5461" class="InductiveConstructor Operator"
      >&#8658;</a
      ><a name="7227"
      > </a
      ><a name="7228" href="Stlc.html#5447" class="InductiveConstructor"
      >bool</a
      ><a name="7232"
      >)) (</a
      ><a name="7236" href="Stlc.html#5562" class="InductiveConstructor"
      >var</a
      ><a name="7239"
      > 0) = </a
      ><a name="7245" href="Stlc.html#6714" class="Function"
      >idBBBB</a
      ><a name="7251"
      > </a
      ><a name="7252" class="Symbol"
      >#-}</a
      ><a name="7255"
      >
</a
      ><a name="7256" class="Symbol"
      >{-#</a
      ><a name="7259"
      > </a
      ><a name="7260" class="Keyword"
      >DISPLAY</a
      ><a name="7267"
      > </a
      ><a name="7268" href="Stlc.html#5611" class="InductiveConstructor"
      >abs</a
      ><a name="7271"
      > 0 </a
      ><a name="7274" href="Stlc.html#5447" class="InductiveConstructor"
      >bool</a
      ><a name="7278"
      > (</a
      ><a name="7280" href="Stlc.html#5611" class="InductiveConstructor"
      >abs</a
      ><a name="7283"
      > </a
      ><a name="7284" href="Stlc.html#7284" class="Bound"
      >y</a
      ><a name="7285"
      > </a
      ><a name="7286" href="Stlc.html#5447" class="InductiveConstructor"
      >bool</a
      ><a name="7290"
      > (</a
      ><a name="7292" href="Stlc.html#5562" class="InductiveConstructor"
      >var</a
      ><a name="7295"
      > 0)) = </a
      ><a name="7302" href="Stlc.html#6847" class="Function"
      >k</a
      ><a name="7303"
      > </a
      ><a name="7304" class="Symbol"
      >#-}</a
      ><a name="7307"
      >
</a
      ><a name="7308" class="Symbol"
      >{-#</a
      ><a name="7311"
      > </a
      ><a name="7312" class="Keyword"
      >DISPLAY</a
      ><a name="7319"
      > </a
      ><a name="7320" href="Stlc.html#5611" class="InductiveConstructor"
      >abs</a
      ><a name="7323"
      > 0 </a
      ><a name="7326" href="Stlc.html#5447" class="InductiveConstructor"
      >bool</a
      ><a name="7330"
      > (</a
      ><a name="7332" href="Stlc.html#5675" class="InductiveConstructor Operator"
      >if</a
      ><a name="7334"
      > (</a
      ><a name="7336" href="Stlc.html#5562" class="InductiveConstructor"
      >var</a
      ><a name="7339"
      > 0) </a
      ><a name="7343" href="Stlc.html#5675" class="InductiveConstructor Operator"
      >then</a
      ><a name="7347"
      > </a
      ><a name="7348" href="Stlc.html#5660" class="InductiveConstructor"
      >false</a
      ><a name="7353"
      > </a
      ><a name="7354" href="Stlc.html#5675" class="InductiveConstructor Operator"
      >else</a
      ><a name="7358"
      > </a
      ><a name="7359" href="Stlc.html#5645" class="InductiveConstructor"
      >true</a
      ><a name="7363"
      >) = </a
      ><a name="7367" href="Stlc.html#6993" class="Function"
      >notB</a
      ><a name="7371"
      > </a
      ><a name="7372" class="Symbol"
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
<a name="8611" href="Stlc.html#8611" class="Function Operator"
      >test_normalizeUnderLambda</a
      ><a name="8636"
      > </a
      ><a name="8637" class="Symbol"
      >:</a
      ><a name="8638"
      > </a
      ><a name="8639" class="Symbol"
      >(&#955;</a
      ><a name="8641"
      > </a
      ><a name="8642" class="Symbol"
      >(</a
      ><a name="8643" href="Stlc.html#8643" class="Bound"
      >x</a
      ><a name="8644"
      > </a
      ><a name="8645" class="Symbol"
      >:</a
      ><a name="8646"
      > </a
      ><a name="8647" href="Agda.Builtin.Nat.html#97" class="Datatype"
      >&#8469;</a
      ><a name="8648" class="Symbol"
      >)</a
      ><a name="8649"
      > </a
      ><a name="8650" class="Symbol"
      >&#8594;</a
      ><a name="8651"
      > </a
      ><a name="8652" class="Number"
      >3</a
      ><a name="8653"
      > </a
      ><a name="8654" href="Agda.Builtin.Nat.html#230" class="Primitive Operator"
      >+</a
      ><a name="8655"
      > </a
      ><a name="8656" class="Number"
      >4</a
      ><a name="8657" class="Symbol"
      >)</a
      ><a name="8658"
      > </a
      ><a name="8659" href="Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="8660"
      > </a
      ><a name="8661" class="Symbol"
      >(&#955;</a
      ><a name="8663"
      > </a
      ><a name="8664" class="Symbol"
      >(</a
      ><a name="8665" href="Stlc.html#8665" class="Bound"
      >x</a
      ><a name="8666"
      > </a
      ><a name="8667" class="Symbol"
      >:</a
      ><a name="8668"
      > </a
      ><a name="8669" href="Agda.Builtin.Nat.html#97" class="Datatype"
      >&#8469;</a
      ><a name="8670" class="Symbol"
      >)</a
      ><a name="8671"
      > </a
      ><a name="8672" class="Symbol"
      >&#8594;</a
      ><a name="8673"
      > </a
      ><a name="8674" class="Number"
      >7</a
      ><a name="8675" class="Symbol"
      >)</a
      ><a name="8676"
      >
</a
      ><a name="8677" href="Stlc.html#8611" class="Function Operator"
      >test_normalizeUnderLambda</a
      ><a name="8702"
      > </a
      ><a name="8703" class="Symbol"
      >=</a
      ><a name="8704"
      > </a
      ><a name="8705" href="Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      >
{% endraw %}</pre>

Most real-world functional programming languages make the second
choice---reduction of a function's body only begins when the
function is actually applied to an argument.  We also make the
second choice here.

<pre class="Agda">{% raw %}
<a name="8945" class="Keyword"
      >data</a
      ><a name="8949"
      > </a
      ><a name="8950" href="Stlc.html#8950" class="Datatype"
      >Value</a
      ><a name="8955"
      > </a
      ><a name="8956" class="Symbol"
      >:</a
      ><a name="8957"
      > </a
      ><a name="8958" href="Stlc.html#5543" class="Datatype"
      >Term</a
      ><a name="8962"
      > </a
      ><a name="8963" class="Symbol"
      >&#8594;</a
      ><a name="8964"
      > </a
      ><a name="8965" class="PrimitiveType"
      >Set</a
      ><a name="8968"
      > </a
      ><a name="8969" class="Keyword"
      >where</a
      ><a name="8974"
      >
  </a
      ><a name="8977" href="Stlc.html#8977" class="InductiveConstructor"
      >abs</a
      ><a name="8980"
      >   </a
      ><a name="8983" class="Symbol"
      >:</a
      ><a name="8984"
      > </a
      ><a name="8985" class="Symbol"
      >&#8704;</a
      ><a name="8986"
      > </a
      ><a name="9003" class="Symbol"
      >&#8594;</a
      ><a name="9004"
      > </a
      ><a name="9005" href="Stlc.html#8950" class="Datatype"
      >Value</a
      ><a name="9010"
      > </a
      ><a name="9011" class="Symbol"
      >(</a
      ><a name="9012" href="Stlc.html#5611" class="InductiveConstructor"
      >abs</a
      ><a name="9015"
      > </a
      ><a name="9016" href="Stlc.html#8988" class="Bound"
      >x</a
      ><a name="9017"
      > </a
      ><a name="9018" href="Stlc.html#8990" class="Bound"
      >A</a
      ><a name="9019"
      > </a
      ><a name="9020" href="Stlc.html#8992" class="Bound"
      >t</a
      ><a name="9021" class="Symbol"
      >)</a
      ><a name="9022"
      >
  </a
      ><a name="9025" href="Stlc.html#9025" class="InductiveConstructor"
      >true</a
      ><a name="9029"
      >  </a
      ><a name="9031" class="Symbol"
      >:</a
      ><a name="9032"
      > </a
      ><a name="9033" href="Stlc.html#8950" class="Datatype"
      >Value</a
      ><a name="9038"
      > </a
      ><a name="9039" href="Stlc.html#5645" class="InductiveConstructor"
      >true</a
      ><a name="9043"
      >
  </a
      ><a name="9046" href="Stlc.html#9046" class="InductiveConstructor"
      >false</a
      ><a name="9051"
      > </a
      ><a name="9052" class="Symbol"
      >:</a
      ><a name="9053"
      > </a
      ><a name="9054" href="Stlc.html#8950" class="Datatype"
      >Value</a
      ><a name="9059"
      > </a
      ><a name="9060" href="Stlc.html#5660" class="InductiveConstructor"
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
<a name="12170" href="Stlc.html#12170" class="Function Operator"
      >[_:=_]_</a
      ><a name="12177"
      > </a
      ><a name="12178" class="Symbol"
      >:</a
      ><a name="12179"
      > </a
      ><a name="12180" href="Maps.html#2275" class="Datatype"
      >Id</a
      ><a name="12182"
      > </a
      ><a name="12183" class="Symbol"
      >-&gt;</a
      ><a name="12185"
      > </a
      ><a name="12186" href="Stlc.html#5543" class="Datatype"
      >Term</a
      ><a name="12190"
      > </a
      ><a name="12191" class="Symbol"
      >-&gt;</a
      ><a name="12193"
      > </a
      ><a name="12194" href="Stlc.html#5543" class="Datatype"
      >Term</a
      ><a name="12198"
      > </a
      ><a name="12199" class="Symbol"
      >-&gt;</a
      ><a name="12201"
      > </a
      ><a name="12202" href="Stlc.html#5543" class="Datatype"
      >Term</a
      ><a name="12206"
      >
</a
      ><a name="12207" href="Stlc.html#12170" class="Function Operator"
      >[</a
      ><a name="12208"
      > </a
      ><a name="12209" href="Stlc.html#12209" class="Bound"
      >x</a
      ><a name="12210"
      > </a
      ><a name="12211" href="Stlc.html#12170" class="Function Operator"
      >:=</a
      ><a name="12213"
      > </a
      ><a name="12214" href="Stlc.html#12214" class="Bound"
      >v</a
      ><a name="12215"
      > </a
      ><a name="12216" href="Stlc.html#12170" class="Function Operator"
      >]</a
      ><a name="12217"
      > </a
      ><a name="12218" class="Symbol"
      >(</a
      ><a name="12219" href="Stlc.html#5562" class="InductiveConstructor"
      >var</a
      ><a name="12222"
      > </a
      ><a name="12223" href="Stlc.html#12223" class="Bound"
      >y</a
      ><a name="12224" class="Symbol"
      >)</a
      ><a name="12225"
      > </a
      ><a name="12226" class="Keyword"
      >with</a
      ><a name="12230"
      > </a
      ><a name="12231" href="Stlc.html#12209" class="Bound"
      >x</a
      ><a name="12232"
      > </a
      ><a name="12233" href="Maps.html#2329" class="Function Operator"
      >&#8799;</a
      ><a name="12234"
      > </a
      ><a name="12235" href="Stlc.html#12223" class="Bound"
      >y</a
      ><a name="12236"
      >
</a
      ><a name="12237" class="Symbol"
      >...</a
      ><a name="12240"
      > </a
      ><a name="12241" class="Symbol"
      >|</a
      ><a name="12242"
      > </a
      ><a name="12243" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#520" class="InductiveConstructor"
      >yes</a
      ><a name="12246"
      > </a
      ><a name="12247" href="Stlc.html#12247" class="Bound"
      >x=y</a
      ><a name="12250"
      > </a
      ><a name="12251" class="Symbol"
      >=</a
      ><a name="12252"
      > </a
      ><a name="12253" href="Stlc.html#12214" class="Bound"
      >v</a
      ><a name="12254"
      >
</a
      ><a name="12255" class="Symbol"
      >...</a
      ><a name="12258"
      > </a
      ><a name="12259" class="Symbol"
      >|</a
      ><a name="12260"
      > </a
      ><a name="12261" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#547" class="InductiveConstructor"
      >no</a
      ><a name="12263"
      >  </a
      ><a name="12265" href="Stlc.html#12265" class="Bound"
      >x&#8800;y</a
      ><a name="12268"
      > </a
      ><a name="12269" class="Symbol"
      >=</a
      ><a name="12270"
      > </a
      ><a name="12271" href="Stlc.html#5562" class="InductiveConstructor"
      >var</a
      ><a name="12274"
      > </a
      ><a name="12275" href="Stlc.html#12223" class="Bound"
      >y</a
      ><a name="12276"
      >
</a
      ><a name="12277" href="Stlc.html#12170" class="Function Operator"
      >[</a
      ><a name="12278"
      > </a
      ><a name="12279" href="Stlc.html#12279" class="Bound"
      >x</a
      ><a name="12280"
      > </a
      ><a name="12281" href="Stlc.html#12170" class="Function Operator"
      >:=</a
      ><a name="12283"
      > </a
      ><a name="12284" href="Stlc.html#12284" class="Bound"
      >v</a
      ><a name="12285"
      > </a
      ><a name="12286" href="Stlc.html#12170" class="Function Operator"
      >]</a
      ><a name="12287"
      > </a
      ><a name="12288" class="Symbol"
      >(</a
      ><a name="12289" href="Stlc.html#5582" class="InductiveConstructor"
      >app</a
      ><a name="12292"
      > </a
      ><a name="12293" href="Stlc.html#12293" class="Bound"
      >s</a
      ><a name="12294"
      > </a
      ><a name="12295" href="Stlc.html#12295" class="Bound"
      >t</a
      ><a name="12296" class="Symbol"
      >)</a
      ><a name="12297"
      > </a
      ><a name="12298" class="Symbol"
      >=</a
      ><a name="12299"
      > </a
      ><a name="12300" href="Stlc.html#5582" class="InductiveConstructor"
      >app</a
      ><a name="12303"
      > </a
      ><a name="12304" class="Symbol"
      >(</a
      ><a name="12305" href="Stlc.html#12170" class="Function Operator"
      >[</a
      ><a name="12306"
      > </a
      ><a name="12307" href="Stlc.html#12279" class="Bound"
      >x</a
      ><a name="12308"
      > </a
      ><a name="12309" href="Stlc.html#12170" class="Function Operator"
      >:=</a
      ><a name="12311"
      > </a
      ><a name="12312" href="Stlc.html#12284" class="Bound"
      >v</a
      ><a name="12313"
      > </a
      ><a name="12314" href="Stlc.html#12170" class="Function Operator"
      >]</a
      ><a name="12315"
      > </a
      ><a name="12316" href="Stlc.html#12293" class="Bound"
      >s</a
      ><a name="12317" class="Symbol"
      >)</a
      ><a name="12318"
      > </a
      ><a name="12319" class="Symbol"
      >(</a
      ><a name="12320" href="Stlc.html#12170" class="Function Operator"
      >[</a
      ><a name="12321"
      > </a
      ><a name="12322" href="Stlc.html#12279" class="Bound"
      >x</a
      ><a name="12323"
      > </a
      ><a name="12324" href="Stlc.html#12170" class="Function Operator"
      >:=</a
      ><a name="12326"
      > </a
      ><a name="12327" href="Stlc.html#12284" class="Bound"
      >v</a
      ><a name="12328"
      > </a
      ><a name="12329" href="Stlc.html#12170" class="Function Operator"
      >]</a
      ><a name="12330"
      > </a
      ><a name="12331" href="Stlc.html#12295" class="Bound"
      >t</a
      ><a name="12332" class="Symbol"
      >)</a
      ><a name="12333"
      >
</a
      ><a name="12334" href="Stlc.html#12170" class="Function Operator"
      >[</a
      ><a name="12335"
      > </a
      ><a name="12336" href="Stlc.html#12336" class="Bound"
      >x</a
      ><a name="12337"
      > </a
      ><a name="12338" href="Stlc.html#12170" class="Function Operator"
      >:=</a
      ><a name="12340"
      > </a
      ><a name="12341" href="Stlc.html#12341" class="Bound"
      >v</a
      ><a name="12342"
      > </a
      ><a name="12343" href="Stlc.html#12170" class="Function Operator"
      >]</a
      ><a name="12344"
      > </a
      ><a name="12345" class="Symbol"
      >(</a
      ><a name="12346" href="Stlc.html#5611" class="InductiveConstructor"
      >abs</a
      ><a name="12349"
      > </a
      ><a name="12350" href="Stlc.html#12350" class="Bound"
      >y</a
      ><a name="12351"
      > </a
      ><a name="12352" href="Stlc.html#12352" class="Bound"
      >A</a
      ><a name="12353"
      > </a
      ><a name="12354" href="Stlc.html#12354" class="Bound"
      >t</a
      ><a name="12355" class="Symbol"
      >)</a
      ><a name="12356"
      > </a
      ><a name="12357" class="Keyword"
      >with</a
      ><a name="12361"
      > </a
      ><a name="12362" href="Stlc.html#12336" class="Bound"
      >x</a
      ><a name="12363"
      > </a
      ><a name="12364" href="Maps.html#2329" class="Function Operator"
      >&#8799;</a
      ><a name="12365"
      > </a
      ><a name="12366" href="Stlc.html#12350" class="Bound"
      >y</a
      ><a name="12367"
      >
</a
      ><a name="12368" class="Symbol"
      >...</a
      ><a name="12371"
      > </a
      ><a name="12372" class="Symbol"
      >|</a
      ><a name="12373"
      > </a
      ><a name="12374" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#520" class="InductiveConstructor"
      >yes</a
      ><a name="12377"
      > </a
      ><a name="12378" href="Stlc.html#12378" class="Bound"
      >x=y</a
      ><a name="12381"
      > </a
      ><a name="12382" class="Symbol"
      >=</a
      ><a name="12383"
      > </a
      ><a name="12384" href="Stlc.html#5611" class="InductiveConstructor"
      >abs</a
      ><a name="12387"
      > </a
      ><a name="12388" href="Stlc.html#12350" class="Bound"
      >y</a
      ><a name="12389"
      > </a
      ><a name="12390" href="Stlc.html#12352" class="Bound"
      >A</a
      ><a name="12391"
      > </a
      ><a name="12392" href="Stlc.html#12354" class="Bound"
      >t</a
      ><a name="12393"
      >
</a
      ><a name="12394" class="Symbol"
      >...</a
      ><a name="12397"
      > </a
      ><a name="12398" class="Symbol"
      >|</a
      ><a name="12399"
      > </a
      ><a name="12400" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#547" class="InductiveConstructor"
      >no</a
      ><a name="12402"
      >  </a
      ><a name="12404" href="Stlc.html#12404" class="Bound"
      >x&#8800;y</a
      ><a name="12407"
      > </a
      ><a name="12408" class="Symbol"
      >=</a
      ><a name="12409"
      > </a
      ><a name="12410" href="Stlc.html#5611" class="InductiveConstructor"
      >abs</a
      ><a name="12413"
      > </a
      ><a name="12414" href="Stlc.html#12350" class="Bound"
      >y</a
      ><a name="12415"
      > </a
      ><a name="12416" href="Stlc.html#12352" class="Bound"
      >A</a
      ><a name="12417"
      > </a
      ><a name="12418" class="Symbol"
      >(</a
      ><a name="12419" href="Stlc.html#12170" class="Function Operator"
      >[</a
      ><a name="12420"
      > </a
      ><a name="12421" href="Stlc.html#12336" class="Bound"
      >x</a
      ><a name="12422"
      > </a
      ><a name="12423" href="Stlc.html#12170" class="Function Operator"
      >:=</a
      ><a name="12425"
      > </a
      ><a name="12426" href="Stlc.html#12341" class="Bound"
      >v</a
      ><a name="12427"
      > </a
      ><a name="12428" href="Stlc.html#12170" class="Function Operator"
      >]</a
      ><a name="12429"
      > </a
      ><a name="12430" href="Stlc.html#12354" class="Bound"
      >t</a
      ><a name="12431" class="Symbol"
      >)</a
      ><a name="12432"
      >
</a
      ><a name="12433" href="Stlc.html#12170" class="Function Operator"
      >[</a
      ><a name="12434"
      > </a
      ><a name="12435" href="Stlc.html#12435" class="Bound"
      >x</a
      ><a name="12436"
      > </a
      ><a name="12437" href="Stlc.html#12170" class="Function Operator"
      >:=</a
      ><a name="12439"
      > </a
      ><a name="12440" href="Stlc.html#12440" class="Bound"
      >v</a
      ><a name="12441"
      > </a
      ><a name="12442" href="Stlc.html#12170" class="Function Operator"
      >]</a
      ><a name="12443"
      > </a
      ><a name="12444" href="Stlc.html#5645" class="InductiveConstructor"
      >true</a
      ><a name="12448"
      >  </a
      ><a name="12450" class="Symbol"
      >=</a
      ><a name="12451"
      > </a
      ><a name="12452" href="Stlc.html#5645" class="InductiveConstructor"
      >true</a
      ><a name="12456"
      >
</a
      ><a name="12457" href="Stlc.html#12170" class="Function Operator"
      >[</a
      ><a name="12458"
      > </a
      ><a name="12459" href="Stlc.html#12459" class="Bound"
      >x</a
      ><a name="12460"
      > </a
      ><a name="12461" href="Stlc.html#12170" class="Function Operator"
      >:=</a
      ><a name="12463"
      > </a
      ><a name="12464" href="Stlc.html#12464" class="Bound"
      >v</a
      ><a name="12465"
      > </a
      ><a name="12466" href="Stlc.html#12170" class="Function Operator"
      >]</a
      ><a name="12467"
      > </a
      ><a name="12468" href="Stlc.html#5660" class="InductiveConstructor"
      >false</a
      ><a name="12473"
      > </a
      ><a name="12474" class="Symbol"
      >=</a
      ><a name="12475"
      > </a
      ><a name="12476" href="Stlc.html#5660" class="InductiveConstructor"
      >false</a
      ><a name="12481"
      >
</a
      ><a name="12482" href="Stlc.html#12170" class="Function Operator"
      >[</a
      ><a name="12483"
      > </a
      ><a name="12484" href="Stlc.html#12484" class="Bound"
      >x</a
      ><a name="12485"
      > </a
      ><a name="12486" href="Stlc.html#12170" class="Function Operator"
      >:=</a
      ><a name="12488"
      > </a
      ><a name="12489" href="Stlc.html#12489" class="Bound"
      >v</a
      ><a name="12490"
      > </a
      ><a name="12491" href="Stlc.html#12170" class="Function Operator"
      >]</a
      ><a name="12492"
      > </a
      ><a name="12493" class="Symbol"
      >(</a
      ><a name="12494" href="Stlc.html#5675" class="InductiveConstructor Operator"
      >if</a
      ><a name="12496"
      > </a
      ><a name="12497" href="Stlc.html#12497" class="Bound"
      >s</a
      ><a name="12498"
      > </a
      ><a name="12499" href="Stlc.html#5675" class="InductiveConstructor Operator"
      >then</a
      ><a name="12503"
      > </a
      ><a name="12504" href="Stlc.html#12504" class="Bound"
      >t</a
      ><a name="12505"
      > </a
      ><a name="12506" href="Stlc.html#5675" class="InductiveConstructor Operator"
      >else</a
      ><a name="12510"
      > </a
      ><a name="12511" href="Stlc.html#12511" class="Bound"
      >u</a
      ><a name="12512" class="Symbol"
      >)</a
      ><a name="12513"
      > </a
      ><a name="12514" class="Symbol"
      >=</a
      ><a name="12515"
      >
  </a
      ><a name="12518" href="Stlc.html#5675" class="InductiveConstructor Operator"
      >if</a
      ><a name="12520"
      > </a
      ><a name="12521" href="Stlc.html#12170" class="Function Operator"
      >[</a
      ><a name="12522"
      > </a
      ><a name="12523" href="Stlc.html#12484" class="Bound"
      >x</a
      ><a name="12524"
      > </a
      ><a name="12525" href="Stlc.html#12170" class="Function Operator"
      >:=</a
      ><a name="12527"
      > </a
      ><a name="12528" href="Stlc.html#12489" class="Bound"
      >v</a
      ><a name="12529"
      > </a
      ><a name="12530" href="Stlc.html#12170" class="Function Operator"
      >]</a
      ><a name="12531"
      > </a
      ><a name="12532" href="Stlc.html#12497" class="Bound"
      >s</a
      ><a name="12533"
      > </a
      ><a name="12534" href="Stlc.html#5675" class="InductiveConstructor Operator"
      >then</a
      ><a name="12538"
      > </a
      ><a name="12539" href="Stlc.html#12170" class="Function Operator"
      >[</a
      ><a name="12540"
      > </a
      ><a name="12541" href="Stlc.html#12484" class="Bound"
      >x</a
      ><a name="12542"
      > </a
      ><a name="12543" href="Stlc.html#12170" class="Function Operator"
      >:=</a
      ><a name="12545"
      > </a
      ><a name="12546" href="Stlc.html#12489" class="Bound"
      >v</a
      ><a name="12547"
      > </a
      ><a name="12548" href="Stlc.html#12170" class="Function Operator"
      >]</a
      ><a name="12549"
      > </a
      ><a name="12550" href="Stlc.html#12504" class="Bound"
      >t</a
      ><a name="12551"
      > </a
      ><a name="12552" href="Stlc.html#5675" class="InductiveConstructor Operator"
      >else</a
      ><a name="12556"
      >  </a
      ><a name="12558" href="Stlc.html#12170" class="Function Operator"
      >[</a
      ><a name="12559"
      > </a
      ><a name="12560" href="Stlc.html#12484" class="Bound"
      >x</a
      ><a name="12561"
      > </a
      ><a name="12562" href="Stlc.html#12170" class="Function Operator"
      >:=</a
      ><a name="12564"
      > </a
      ><a name="12565" href="Stlc.html#12489" class="Bound"
      >v</a
      ><a name="12566"
      > </a
      ><a name="12567" href="Stlc.html#12170" class="Function Operator"
      >]</a
      ><a name="12568"
      > </a
      ><a name="12569" href="Stlc.html#12511" class="Bound"
      >u</a
      >
{% endraw %}</pre>

<div class="hidden">
<pre class="Agda">{% raw %}
<a name="12617" class="Keyword"
      >infix</a
      ><a name="12622"
      > </a
      ><a name="12623" class="Number"
      >9</a
      ><a name="12624"
      > </a
      ><a name="12625" href="Stlc.html#12170" class="Function Operator"
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
<a name="13561" class="Keyword"
      >data</a
      ><a name="13565"
      > </a
      ><a name="13566" href="Stlc.html#13566" class="Datatype Operator"
      >[_:=_]_==&gt;_</a
      ><a name="13577"
      > </a
      ><a name="13578" class="Symbol"
      >(</a
      ><a name="13579" href="Stlc.html#13579" class="Bound"
      >x</a
      ><a name="13580"
      > </a
      ><a name="13581" class="Symbol"
      >:</a
      ><a name="13582"
      > </a
      ><a name="13583" href="Maps.html#2275" class="Datatype"
      >Id</a
      ><a name="13585" class="Symbol"
      >)</a
      ><a name="13586"
      > </a
      ><a name="13587" class="Symbol"
      >(</a
      ><a name="13588" href="Stlc.html#13588" class="Bound"
      >s</a
      ><a name="13589"
      > </a
      ><a name="13590" class="Symbol"
      >:</a
      ><a name="13591"
      > </a
      ><a name="13592" href="Stlc.html#5543" class="Datatype"
      >Term</a
      ><a name="13596" class="Symbol"
      >)</a
      ><a name="13597"
      > </a
      ><a name="13598" class="Symbol"
      >:</a
      ><a name="13599"
      > </a
      ><a name="13600" href="Stlc.html#5543" class="Datatype"
      >Term</a
      ><a name="13604"
      > </a
      ><a name="13605" class="Symbol"
      >-&gt;</a
      ><a name="13607"
      > </a
      ><a name="13608" href="Stlc.html#5543" class="Datatype"
      >Term</a
      ><a name="13612"
      > </a
      ><a name="13613" class="Symbol"
      >-&gt;</a
      ><a name="13615"
      > </a
      ><a name="13616" class="PrimitiveType"
      >Set</a
      ><a name="13619"
      > </a
      ><a name="13620" class="Keyword"
      >where</a
      ><a name="13625"
      >
  </a
      ><a name="13628" href="Stlc.html#13628" class="InductiveConstructor"
      >var1</a
      ><a name="13632"
      > </a
      ><a name="13633" class="Symbol"
      >:</a
      ><a name="13634"
      > </a
      ><a name="13635" href="Stlc.html#13566" class="Datatype Operator"
      >[</a
      ><a name="13636"
      > </a
      ><a name="13637" href="Stlc.html#13579" class="Bound"
      >x</a
      ><a name="13638"
      > </a
      ><a name="13639" href="Stlc.html#13566" class="Datatype Operator"
      >:=</a
      ><a name="13641"
      > </a
      ><a name="13642" href="Stlc.html#13588" class="Bound"
      >s</a
      ><a name="13643"
      > </a
      ><a name="13644" href="Stlc.html#13566" class="Datatype Operator"
      >]</a
      ><a name="13645"
      > </a
      ><a name="13646" class="Symbol"
      >(</a
      ><a name="13647" href="Stlc.html#5562" class="InductiveConstructor"
      >var</a
      ><a name="13650"
      > </a
      ><a name="13651" href="Stlc.html#13579" class="Bound"
      >x</a
      ><a name="13652" class="Symbol"
      >)</a
      ><a name="13653"
      > </a
      ><a name="13654" href="Stlc.html#13566" class="Datatype Operator"
      >==&gt;</a
      ><a name="13657"
      > </a
      ><a name="13658" href="Stlc.html#13588" class="Bound"
      >s</a
      ><a name="13659"
      >
  </a
      ><a name="13662" class="Comment"
      >{- FILL IN HERE -}</a
      >
{% endraw %}</pre>

<pre class="Agda">{% raw %}
<a name="13706" class="Keyword"
      >postulate</a
      ><a name="13715"
      >
  </a
      ><a name="13718" href="Stlc.html#13718" class="Postulate"
      >subst-correct</a
      ><a name="13731"
      > </a
      ><a name="13732" class="Symbol"
      >:</a
      ><a name="13733"
      > </a
      ><a name="13734" class="Symbol"
      >&#8704;</a
      ><a name="13735"
      > </a
      ><a name="13736" href="Stlc.html#13736" class="Bound"
      >s</a
      ><a name="13737"
      > </a
      ><a name="13738" href="Stlc.html#13738" class="Bound"
      >x</a
      ><a name="13739"
      > </a
      ><a name="13740" href="Stlc.html#13740" class="Bound"
      >t</a
      ><a name="13741"
      > </a
      ><a name="13742" href="Stlc.html#13742" class="Bound"
      >t'</a
      ><a name="13744"
      >
                </a
      ><a name="13761" class="Symbol"
      >&#8594;</a
      ><a name="13762"
      > </a
      ><a name="13763" href="Stlc.html#12170" class="Function Operator"
      >[</a
      ><a name="13764"
      > </a
      ><a name="13765" href="Stlc.html#13738" class="Bound"
      >x</a
      ><a name="13766"
      > </a
      ><a name="13767" href="Stlc.html#12170" class="Function Operator"
      >:=</a
      ><a name="13769"
      > </a
      ><a name="13770" href="Stlc.html#13736" class="Bound"
      >s</a
      ><a name="13771"
      > </a
      ><a name="13772" href="Stlc.html#12170" class="Function Operator"
      >]</a
      ><a name="13773"
      > </a
      ><a name="13774" href="Stlc.html#13740" class="Bound"
      >t</a
      ><a name="13775"
      > </a
      ><a name="13776" href="Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="13777"
      > </a
      ><a name="13778" href="Stlc.html#13742" class="Bound"
      >t'</a
      ><a name="13780"
      >
                </a
      ><a name="13797" class="Symbol"
      >&#8594;</a
      ><a name="13798"
      > </a
      ><a name="13799" href="Stlc.html#13566" class="Datatype Operator"
      >[</a
      ><a name="13800"
      > </a
      ><a name="13801" href="Stlc.html#13738" class="Bound"
      >x</a
      ><a name="13802"
      > </a
      ><a name="13803" href="Stlc.html#13566" class="Datatype Operator"
      >:=</a
      ><a name="13805"
      > </a
      ><a name="13806" href="Stlc.html#13736" class="Bound"
      >s</a
      ><a name="13807"
      > </a
      ><a name="13808" href="Stlc.html#13566" class="Datatype Operator"
      >]</a
      ><a name="13809"
      > </a
      ><a name="13810" href="Stlc.html#13740" class="Bound"
      >t</a
      ><a name="13811"
      > </a
      ><a name="13812" href="Stlc.html#13566" class="Datatype Operator"
      >==&gt;</a
      ><a name="13815"
      > </a
      ><a name="13816" href="Stlc.html#13742" class="Bound"
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
<a name="15081" class="Keyword"
      >data</a
      ><a name="15085"
      > </a
      ><a name="15086" href="Stlc.html#15086" class="Datatype Operator"
      >_==&gt;_</a
      ><a name="15091"
      > </a
      ><a name="15092" class="Symbol"
      >:</a
      ><a name="15093"
      > </a
      ><a name="15094" href="Stlc.html#5543" class="Datatype"
      >Term</a
      ><a name="15098"
      > </a
      ><a name="15099" class="Symbol"
      >&#8594;</a
      ><a name="15100"
      > </a
      ><a name="15101" href="Stlc.html#5543" class="Datatype"
      >Term</a
      ><a name="15105"
      > </a
      ><a name="15106" class="Symbol"
      >&#8594;</a
      ><a name="15107"
      > </a
      ><a name="15108" class="PrimitiveType"
      >Set</a
      ><a name="15111"
      > </a
      ><a name="15112" class="Keyword"
      >where</a
      ><a name="15117"
      >
  </a
      ><a name="15120" href="Stlc.html#15120" class="InductiveConstructor"
      >red</a
      ><a name="15123"
      >     </a
      ><a name="15128" class="Symbol"
      >:</a
      ><a name="15129"
      > </a
      ><a name="15130" class="Symbol"
      >&#8704;</a
      ><a name="15131"
      > </a
      ><a name="15152" class="Symbol"
      >&#8594;</a
      ><a name="15153"
      > </a
      ><a name="15154" href="Stlc.html#8950" class="Datatype"
      >Value</a
      ><a name="15159"
      > </a
      ><a name="15160" href="Stlc.html#15139" class="Bound"
      >t</a
      ><a name="15161"
      >
          </a
      ><a name="15172" class="Symbol"
      >&#8594;</a
      ><a name="15173"
      > </a
      ><a name="15174" href="Stlc.html#5582" class="InductiveConstructor"
      >app</a
      ><a name="15177"
      > </a
      ><a name="15178" class="Symbol"
      >(</a
      ><a name="15179" href="Stlc.html#5611" class="InductiveConstructor"
      >abs</a
      ><a name="15182"
      > </a
      ><a name="15183" href="Stlc.html#15133" class="Bound"
      >x</a
      ><a name="15184"
      > </a
      ><a name="15185" href="Stlc.html#15135" class="Bound"
      >A</a
      ><a name="15186"
      > </a
      ><a name="15187" href="Stlc.html#15137" class="Bound"
      >s</a
      ><a name="15188" class="Symbol"
      >)</a
      ><a name="15189"
      > </a
      ><a name="15190" href="Stlc.html#15139" class="Bound"
      >t</a
      ><a name="15191"
      > </a
      ><a name="15192" href="Stlc.html#15086" class="Datatype Operator"
      >==&gt;</a
      ><a name="15195"
      > </a
      ><a name="15196" href="Stlc.html#12170" class="Function Operator"
      >[</a
      ><a name="15197"
      > </a
      ><a name="15198" href="Stlc.html#15133" class="Bound"
      >x</a
      ><a name="15199"
      > </a
      ><a name="15200" href="Stlc.html#12170" class="Function Operator"
      >:=</a
      ><a name="15202"
      > </a
      ><a name="15203" href="Stlc.html#15139" class="Bound"
      >t</a
      ><a name="15204"
      > </a
      ><a name="15205" href="Stlc.html#12170" class="Function Operator"
      >]</a
      ><a name="15206"
      > </a
      ><a name="15207" href="Stlc.html#15137" class="Bound"
      >s</a
      ><a name="15208"
      >
  </a
      ><a name="15211" href="Stlc.html#15211" class="InductiveConstructor"
      >app1</a
      ><a name="15215"
      >    </a
      ><a name="15219" class="Symbol"
      >:</a
      ><a name="15220"
      > </a
      ><a name="15221" class="Symbol"
      >&#8704;</a
      ><a name="15222"
      > </a
      ><a name="15242" class="Symbol"
      >&#8594;</a
      ><a name="15243"
      > </a
      ><a name="15244" href="Stlc.html#15224" class="Bound"
      >s</a
      ><a name="15245"
      > </a
      ><a name="15246" href="Stlc.html#15086" class="Datatype Operator"
      >==&gt;</a
      ><a name="15249"
      > </a
      ><a name="15250" href="Stlc.html#15226" class="Bound"
      >s'</a
      ><a name="15252"
      >
          </a
      ><a name="15263" class="Symbol"
      >&#8594;</a
      ><a name="15264"
      > </a
      ><a name="15265" href="Stlc.html#5582" class="InductiveConstructor"
      >app</a
      ><a name="15268"
      > </a
      ><a name="15269" href="Stlc.html#15224" class="Bound"
      >s</a
      ><a name="15270"
      > </a
      ><a name="15271" href="Stlc.html#15229" class="Bound"
      >t</a
      ><a name="15272"
      > </a
      ><a name="15273" href="Stlc.html#15086" class="Datatype Operator"
      >==&gt;</a
      ><a name="15276"
      > </a
      ><a name="15277" href="Stlc.html#5582" class="InductiveConstructor"
      >app</a
      ><a name="15280"
      > </a
      ><a name="15281" href="Stlc.html#15226" class="Bound"
      >s'</a
      ><a name="15283"
      > </a
      ><a name="15284" href="Stlc.html#15229" class="Bound"
      >t</a
      ><a name="15285"
      >
  </a
      ><a name="15288" href="Stlc.html#15288" class="InductiveConstructor"
      >app2</a
      ><a name="15292"
      >    </a
      ><a name="15296" class="Symbol"
      >:</a
      ><a name="15297"
      > </a
      ><a name="15298" class="Symbol"
      >&#8704;</a
      ><a name="15299"
      > </a
      ><a name="15319" class="Symbol"
      >&#8594;</a
      ><a name="15320"
      > </a
      ><a name="15321" href="Stlc.html#8950" class="Datatype"
      >Value</a
      ><a name="15326"
      > </a
      ><a name="15327" href="Stlc.html#15301" class="Bound"
      >s</a
      ><a name="15328"
      >
          </a
      ><a name="15339" class="Symbol"
      >&#8594;</a
      ><a name="15340"
      > </a
      ><a name="15341" href="Stlc.html#15303" class="Bound"
      >t</a
      ><a name="15342"
      > </a
      ><a name="15343" href="Stlc.html#15086" class="Datatype Operator"
      >==&gt;</a
      ><a name="15346"
      > </a
      ><a name="15347" href="Stlc.html#15305" class="Bound"
      >t'</a
      ><a name="15349"
      >
          </a
      ><a name="15360" class="Symbol"
      >&#8594;</a
      ><a name="15361"
      > </a
      ><a name="15362" href="Stlc.html#5582" class="InductiveConstructor"
      >app</a
      ><a name="15365"
      > </a
      ><a name="15366" href="Stlc.html#15301" class="Bound"
      >s</a
      ><a name="15367"
      > </a
      ><a name="15368" href="Stlc.html#15303" class="Bound"
      >t</a
      ><a name="15369"
      > </a
      ><a name="15370" href="Stlc.html#15086" class="Datatype Operator"
      >==&gt;</a
      ><a name="15373"
      > </a
      ><a name="15374" href="Stlc.html#5582" class="InductiveConstructor"
      >app</a
      ><a name="15377"
      > </a
      ><a name="15378" href="Stlc.html#15301" class="Bound"
      >s</a
      ><a name="15379"
      > </a
      ><a name="15380" href="Stlc.html#15305" class="Bound"
      >t'</a
      ><a name="15382"
      >
  </a
      ><a name="15385" href="Stlc.html#15385" class="InductiveConstructor"
      >if</a
      ><a name="15387"
      >      </a
      ><a name="15393" class="Symbol"
      >:</a
      ><a name="15394"
      > </a
      ><a name="15395" class="Symbol"
      >&#8704;</a
      ><a name="15396"
      > </a
      ><a name="15418" class="Symbol"
      >&#8594;</a
      ><a name="15419"
      > </a
      ><a name="15420" href="Stlc.html#15398" class="Bound"
      >s</a
      ><a name="15421"
      > </a
      ><a name="15422" href="Stlc.html#15086" class="Datatype Operator"
      >==&gt;</a
      ><a name="15425"
      > </a
      ><a name="15426" href="Stlc.html#15400" class="Bound"
      >s'</a
      ><a name="15428"
      >
          </a
      ><a name="15439" class="Symbol"
      >&#8594;</a
      ><a name="15440"
      > </a
      ><a name="15441" href="Stlc.html#5675" class="InductiveConstructor Operator"
      >if</a
      ><a name="15443"
      > </a
      ><a name="15444" href="Stlc.html#15398" class="Bound"
      >s</a
      ><a name="15445"
      > </a
      ><a name="15446" href="Stlc.html#5675" class="InductiveConstructor Operator"
      >then</a
      ><a name="15450"
      > </a
      ><a name="15451" href="Stlc.html#15403" class="Bound"
      >t</a
      ><a name="15452"
      > </a
      ><a name="15453" href="Stlc.html#5675" class="InductiveConstructor Operator"
      >else</a
      ><a name="15457"
      > </a
      ><a name="15458" href="Stlc.html#15405" class="Bound"
      >u</a
      ><a name="15459"
      > </a
      ><a name="15460" href="Stlc.html#15086" class="Datatype Operator"
      >==&gt;</a
      ><a name="15463"
      > </a
      ><a name="15464" href="Stlc.html#5675" class="InductiveConstructor Operator"
      >if</a
      ><a name="15466"
      > </a
      ><a name="15467" href="Stlc.html#15400" class="Bound"
      >s'</a
      ><a name="15469"
      > </a
      ><a name="15470" href="Stlc.html#5675" class="InductiveConstructor Operator"
      >then</a
      ><a name="15474"
      > </a
      ><a name="15475" href="Stlc.html#15403" class="Bound"
      >t</a
      ><a name="15476"
      > </a
      ><a name="15477" href="Stlc.html#5675" class="InductiveConstructor Operator"
      >else</a
      ><a name="15481"
      > </a
      ><a name="15482" href="Stlc.html#15405" class="Bound"
      >u</a
      ><a name="15483"
      >
  </a
      ><a name="15486" href="Stlc.html#15486" class="InductiveConstructor"
      >iftrue</a
      ><a name="15492"
      >  </a
      ><a name="15494" class="Symbol"
      >:</a
      ><a name="15495"
      > </a
      ><a name="15496" class="Symbol"
      >&#8704;</a
      ><a name="15497"
      > </a
      ><a name="15514" class="Symbol"
      >&#8594;</a
      ><a name="15515"
      > </a
      ><a name="15516" href="Stlc.html#5675" class="InductiveConstructor Operator"
      >if</a
      ><a name="15518"
      > </a
      ><a name="15519" href="Stlc.html#5645" class="InductiveConstructor"
      >true</a
      ><a name="15523"
      > </a
      ><a name="15524" href="Stlc.html#5675" class="InductiveConstructor Operator"
      >then</a
      ><a name="15528"
      > </a
      ><a name="15529" href="Stlc.html#15499" class="Bound"
      >s</a
      ><a name="15530"
      > </a
      ><a name="15531" href="Stlc.html#5675" class="InductiveConstructor Operator"
      >else</a
      ><a name="15535"
      > </a
      ><a name="15536" href="Stlc.html#15501" class="Bound"
      >t</a
      ><a name="15537"
      > </a
      ><a name="15538" href="Stlc.html#15086" class="Datatype Operator"
      >==&gt;</a
      ><a name="15541"
      > </a
      ><a name="15542" href="Stlc.html#15499" class="Bound"
      >s</a
      ><a name="15543"
      >
  </a
      ><a name="15546" href="Stlc.html#15546" class="InductiveConstructor"
      >iffalse</a
      ><a name="15553"
      > </a
      ><a name="15554" class="Symbol"
      >:</a
      ><a name="15555"
      > </a
      ><a name="15556" class="Symbol"
      >&#8704;</a
      ><a name="15557"
      > </a
      ><a name="15574" class="Symbol"
      >&#8594;</a
      ><a name="15575"
      > </a
      ><a name="15576" href="Stlc.html#5675" class="InductiveConstructor Operator"
      >if</a
      ><a name="15578"
      > </a
      ><a name="15579" href="Stlc.html#5660" class="InductiveConstructor"
      >false</a
      ><a name="15584"
      > </a
      ><a name="15585" href="Stlc.html#5675" class="InductiveConstructor Operator"
      >then</a
      ><a name="15589"
      > </a
      ><a name="15590" href="Stlc.html#15559" class="Bound"
      >s</a
      ><a name="15591"
      > </a
      ><a name="15592" href="Stlc.html#5675" class="InductiveConstructor Operator"
      >else</a
      ><a name="15596"
      > </a
      ><a name="15597" href="Stlc.html#15561" class="Bound"
      >t</a
      ><a name="15598"
      > </a
      ><a name="15599" href="Stlc.html#15086" class="Datatype Operator"
      >==&gt;</a
      ><a name="15602"
      > </a
      ><a name="15603" href="Stlc.html#15561" class="Bound"
      >t</a
      >
{% endraw %}</pre>

<div class="hidden">
<pre class="Agda">{% raw %}
<a name="15651" class="Keyword"
      >infix</a
      ><a name="15656"
      > </a
      ><a name="15657" class="Number"
      >1</a
      ><a name="15658"
      > </a
      ><a name="15659" href="Stlc.html#15086" class="Datatype Operator"
      >_==&gt;_</a
      >
{% endraw %}</pre>
</div>

<pre class="Agda">{% raw %}
<a name="15697" class="Keyword"
      >data</a
      ><a name="15701"
      > </a
      ><a name="15702" href="Stlc.html#15702" class="Datatype"
      >Multi</a
      ><a name="15707"
      > </a
      ><a name="15708" class="Symbol"
      >(</a
      ><a name="15709" href="Stlc.html#15709" class="Bound"
      >R</a
      ><a name="15710"
      > </a
      ><a name="15711" class="Symbol"
      >:</a
      ><a name="15712"
      > </a
      ><a name="15713" href="Stlc.html#5543" class="Datatype"
      >Term</a
      ><a name="15717"
      > </a
      ><a name="15718" class="Symbol"
      >&#8594;</a
      ><a name="15719"
      > </a
      ><a name="15720" href="Stlc.html#5543" class="Datatype"
      >Term</a
      ><a name="15724"
      > </a
      ><a name="15725" class="Symbol"
      >&#8594;</a
      ><a name="15726"
      > </a
      ><a name="15727" class="PrimitiveType"
      >Set</a
      ><a name="15730" class="Symbol"
      >)</a
      ><a name="15731"
      > </a
      ><a name="15732" class="Symbol"
      >:</a
      ><a name="15733"
      > </a
      ><a name="15734" href="Stlc.html#5543" class="Datatype"
      >Term</a
      ><a name="15738"
      > </a
      ><a name="15739" class="Symbol"
      >&#8594;</a
      ><a name="15740"
      > </a
      ><a name="15741" href="Stlc.html#5543" class="Datatype"
      >Term</a
      ><a name="15745"
      > </a
      ><a name="15746" class="Symbol"
      >&#8594;</a
      ><a name="15747"
      > </a
      ><a name="15748" class="PrimitiveType"
      >Set</a
      ><a name="15751"
      > </a
      ><a name="15752" class="Keyword"
      >where</a
      ><a name="15757"
      >
  </a
      ><a name="15760" href="Stlc.html#15760" class="InductiveConstructor"
      >refl</a
      ><a name="15764"
      > </a
      ><a name="15765" class="Symbol"
      >:</a
      ><a name="15766"
      > </a
      ><a name="15767" class="Symbol"
      >&#8704;</a
      ><a name="15768"
      > </a
      ><a name="15773" class="Symbol"
      >-&gt;</a
      ><a name="15775"
      > </a
      ><a name="15776" href="Stlc.html#15702" class="Datatype"
      >Multi</a
      ><a name="15781"
      > </a
      ><a name="15782" href="Stlc.html#15709" class="Bound"
      >R</a
      ><a name="15783"
      > </a
      ><a name="15784" href="Stlc.html#15770" class="Bound"
      >x</a
      ><a name="15785"
      > </a
      ><a name="15786" href="Stlc.html#15770" class="Bound"
      >x</a
      ><a name="15787"
      >
  </a
      ><a name="15790" href="Stlc.html#15790" class="InductiveConstructor"
      >step</a
      ><a name="15794"
      > </a
      ><a name="15795" class="Symbol"
      >:</a
      ><a name="15796"
      > </a
      ><a name="15797" class="Symbol"
      >&#8704;</a
      ><a name="15798"
      > </a
      ><a name="15807" class="Symbol"
      >-&gt;</a
      ><a name="15809"
      > </a
      ><a name="15810" href="Stlc.html#15709" class="Bound"
      >R</a
      ><a name="15811"
      > </a
      ><a name="15812" href="Stlc.html#15800" class="Bound"
      >x</a
      ><a name="15813"
      > </a
      ><a name="15814" href="Stlc.html#15802" class="Bound"
      >y</a
      ><a name="15815"
      > </a
      ><a name="15816" class="Symbol"
      >-&gt;</a
      ><a name="15818"
      > </a
      ><a name="15819" href="Stlc.html#15702" class="Datatype"
      >Multi</a
      ><a name="15824"
      > </a
      ><a name="15825" href="Stlc.html#15709" class="Bound"
      >R</a
      ><a name="15826"
      > </a
      ><a name="15827" href="Stlc.html#15802" class="Bound"
      >y</a
      ><a name="15828"
      > </a
      ><a name="15829" href="Stlc.html#15804" class="Bound"
      >z</a
      ><a name="15830"
      > </a
      ><a name="15831" class="Symbol"
      >-&gt;</a
      ><a name="15833"
      > </a
      ><a name="15834" href="Stlc.html#15702" class="Datatype"
      >Multi</a
      ><a name="15839"
      > </a
      ><a name="15840" href="Stlc.html#15709" class="Bound"
      >R</a
      ><a name="15841"
      > </a
      ><a name="15842" href="Stlc.html#15800" class="Bound"
      >x</a
      ><a name="15843"
      > </a
      ><a name="15844" href="Stlc.html#15804" class="Bound"
      >z</a
      >
{% endraw %}</pre>

<pre class="Agda">{% raw %}
<a name="15871" href="Stlc.html#15871" class="Function Operator"
      >_==&gt;*_</a
      ><a name="15877"
      > </a
      ><a name="15878" class="Symbol"
      >:</a
      ><a name="15879"
      > </a
      ><a name="15880" href="Stlc.html#5543" class="Datatype"
      >Term</a
      ><a name="15884"
      > </a
      ><a name="15885" class="Symbol"
      >&#8594;</a
      ><a name="15886"
      > </a
      ><a name="15887" href="Stlc.html#5543" class="Datatype"
      >Term</a
      ><a name="15891"
      > </a
      ><a name="15892" class="Symbol"
      >&#8594;</a
      ><a name="15893"
      > </a
      ><a name="15894" class="PrimitiveType"
      >Set</a
      ><a name="15897"
      >
</a
      ><a name="15898" href="Stlc.html#15871" class="Function Operator"
      >_==&gt;*_</a
      ><a name="15904"
      > </a
      ><a name="15905" class="Symbol"
      >=</a
      ><a name="15906"
      > </a
      ><a name="15907" href="Stlc.html#15702" class="Datatype"
      >Multi</a
      ><a name="15912"
      > </a
      ><a name="15913" href="Stlc.html#15086" class="Datatype Operator"
      >_==&gt;_</a
      >
{% endraw %}</pre>

<div class="hidden">
<pre class="Agda">{% raw %}
<a name="15965" class="Symbol"
      >{-#</a
      ><a name="15968"
      > </a
      ><a name="15969" class="Keyword"
      >DISPLAY</a
      ><a name="15976"
      > </a
      ><a name="15977" href="Stlc.html#15702" class="Datatype"
      >Multi</a
      ><a name="15982"
      > </a
      ><a name="15983" href="Stlc.html#15983" class="Bound Operator"
      >_==&gt;_</a
      ><a name="15988"
      > = </a
      ><a name="15991" href="Stlc.html#15871" class="Function Operator"
      >_==&gt;*_</a
      ><a name="15997"
      > </a
      ><a name="15998" class="Symbol"
      >#-}</a
      >
{% endraw %}</pre>
</div>

### Examples

Example:

$$((\lambda x:bool\rightarrow bool. x) (\lambda x:bool. x)) \Longrightarrow^* (\lambda x:bool. x)$$.

<pre class="Agda">{% raw %}
<a name="16160" href="Stlc.html#16160" class="Function"
      >step-example1</a
      ><a name="16173"
      > </a
      ><a name="16174" class="Symbol"
      >:</a
      ><a name="16175"
      > </a
      ><a name="16176" class="Symbol"
      >(</a
      ><a name="16177" href="Stlc.html#5582" class="InductiveConstructor"
      >app</a
      ><a name="16180"
      > </a
      ><a name="16181" href="Stlc.html#6560" class="Function"
      >idBB</a
      ><a name="16185"
      > </a
      ><a name="16186" href="Stlc.html#6454" class="Function"
      >idB</a
      ><a name="16189" class="Symbol"
      >)</a
      ><a name="16190"
      > </a
      ><a name="16191" href="Stlc.html#15871" class="Function Operator"
      >==&gt;*</a
      ><a name="16195"
      > </a
      ><a name="16196" href="Stlc.html#6454" class="Function"
      >idB</a
      ><a name="16199"
      >
</a
      ><a name="16200" href="Stlc.html#16160" class="Function"
      >step-example1</a
      ><a name="16213"
      > </a
      ><a name="16214" class="Symbol"
      >=</a
      ><a name="16215"
      > </a
      ><a name="16216" href="Stlc.html#15790" class="InductiveConstructor"
      >step</a
      ><a name="16220"
      > </a
      ><a name="16221" class="Symbol"
      >(</a
      ><a name="16222" href="Stlc.html#15120" class="InductiveConstructor"
      >red</a
      ><a name="16225"
      > </a
      ><a name="16226" href="Stlc.html#8977" class="InductiveConstructor"
      >abs</a
      ><a name="16229" class="Symbol"
      >)</a
      ><a name="16230"
      >
              </a
      ><a name="16245" href="https://agda.github.io/agda-stdlib/Function.html#1835" class="Function Operator"
      >$</a
      ><a name="16246"
      > </a
      ><a name="16247" href="Stlc.html#15760" class="InductiveConstructor"
      >refl</a
      >
{% endraw %}</pre>

Example:

$$(\lambda x:bool\rightarrow bool. x) \;((\lambda x:bool\rightarrow bool. x)\;(\lambda x:bool. x))) \Longrightarrow^* (\lambda x:bool. x)$$.

<pre class="Agda">{% raw %}
<a name="16429" href="Stlc.html#16429" class="Function"
      >step-example2</a
      ><a name="16442"
      > </a
      ><a name="16443" class="Symbol"
      >:</a
      ><a name="16444"
      > </a
      ><a name="16445" class="Symbol"
      >(</a
      ><a name="16446" href="Stlc.html#5582" class="InductiveConstructor"
      >app</a
      ><a name="16449"
      > </a
      ><a name="16450" href="Stlc.html#6560" class="Function"
      >idBB</a
      ><a name="16454"
      > </a
      ><a name="16455" class="Symbol"
      >(</a
      ><a name="16456" href="Stlc.html#5582" class="InductiveConstructor"
      >app</a
      ><a name="16459"
      > </a
      ><a name="16460" href="Stlc.html#6560" class="Function"
      >idBB</a
      ><a name="16464"
      > </a
      ><a name="16465" href="Stlc.html#6454" class="Function"
      >idB</a
      ><a name="16468" class="Symbol"
      >))</a
      ><a name="16470"
      > </a
      ><a name="16471" href="Stlc.html#15871" class="Function Operator"
      >==&gt;*</a
      ><a name="16475"
      > </a
      ><a name="16476" href="Stlc.html#6454" class="Function"
      >idB</a
      ><a name="16479"
      >
</a
      ><a name="16480" href="Stlc.html#16429" class="Function"
      >step-example2</a
      ><a name="16493"
      > </a
      ><a name="16494" class="Symbol"
      >=</a
      ><a name="16495"
      > </a
      ><a name="16496" href="Stlc.html#15790" class="InductiveConstructor"
      >step</a
      ><a name="16500"
      > </a
      ><a name="16501" class="Symbol"
      >(</a
      ><a name="16502" href="Stlc.html#15288" class="InductiveConstructor"
      >app2</a
      ><a name="16506"
      > </a
      ><a name="16507" href="Stlc.html#8977" class="InductiveConstructor"
      >abs</a
      ><a name="16510"
      > </a
      ><a name="16511" class="Symbol"
      >(</a
      ><a name="16512" href="Stlc.html#15120" class="InductiveConstructor"
      >red</a
      ><a name="16515"
      > </a
      ><a name="16516" href="Stlc.html#8977" class="InductiveConstructor"
      >abs</a
      ><a name="16519" class="Symbol"
      >))</a
      ><a name="16521"
      >
              </a
      ><a name="16536" href="https://agda.github.io/agda-stdlib/Function.html#1835" class="Function Operator"
      >$</a
      ><a name="16537"
      > </a
      ><a name="16538" href="Stlc.html#15790" class="InductiveConstructor"
      >step</a
      ><a name="16542"
      > </a
      ><a name="16543" class="Symbol"
      >(</a
      ><a name="16544" href="Stlc.html#15120" class="InductiveConstructor"
      >red</a
      ><a name="16547"
      > </a
      ><a name="16548" href="Stlc.html#8977" class="InductiveConstructor"
      >abs</a
      ><a name="16551" class="Symbol"
      >)</a
      ><a name="16552"
      >
              </a
      ><a name="16567" href="https://agda.github.io/agda-stdlib/Function.html#1835" class="Function Operator"
      >$</a
      ><a name="16568"
      > </a
      ><a name="16569" href="Stlc.html#15760" class="InductiveConstructor"
      >refl</a
      >
{% endraw %}</pre>

Example:

$$((\lambda x:bool\rightarrow bool. x)\;(\lambda x:bool. \text{if }x\text{ then }false\text{ else }true))\;true\Longrightarrow^* false$$.

<pre class="Agda">{% raw %}
<a name="16748" href="Stlc.html#16748" class="Function"
      >step-example3</a
      ><a name="16761"
      > </a
      ><a name="16762" class="Symbol"
      >:</a
      ><a name="16763"
      > </a
      ><a name="16764" class="Symbol"
      >(</a
      ><a name="16765" href="Stlc.html#5582" class="InductiveConstructor"
      >app</a
      ><a name="16768"
      > </a
      ><a name="16769" class="Symbol"
      >(</a
      ><a name="16770" href="Stlc.html#5582" class="InductiveConstructor"
      >app</a
      ><a name="16773"
      > </a
      ><a name="16774" href="Stlc.html#6560" class="Function"
      >idBB</a
      ><a name="16778"
      > </a
      ><a name="16779" href="Stlc.html#6993" class="Function"
      >notB</a
      ><a name="16783" class="Symbol"
      >)</a
      ><a name="16784"
      > </a
      ><a name="16785" href="Stlc.html#5645" class="InductiveConstructor"
      >true</a
      ><a name="16789" class="Symbol"
      >)</a
      ><a name="16790"
      > </a
      ><a name="16791" href="Stlc.html#15871" class="Function Operator"
      >==&gt;*</a
      ><a name="16795"
      > </a
      ><a name="16796" href="Stlc.html#5660" class="InductiveConstructor"
      >false</a
      ><a name="16801"
      >
</a
      ><a name="16802" href="Stlc.html#16748" class="Function"
      >step-example3</a
      ><a name="16815"
      > </a
      ><a name="16816" class="Symbol"
      >=</a
      ><a name="16817"
      > </a
      ><a name="16818" href="Stlc.html#15790" class="InductiveConstructor"
      >step</a
      ><a name="16822"
      > </a
      ><a name="16823" class="Symbol"
      >(</a
      ><a name="16824" href="Stlc.html#15211" class="InductiveConstructor"
      >app1</a
      ><a name="16828"
      > </a
      ><a name="16829" class="Symbol"
      >(</a
      ><a name="16830" href="Stlc.html#15120" class="InductiveConstructor"
      >red</a
      ><a name="16833"
      > </a
      ><a name="16834" href="Stlc.html#8977" class="InductiveConstructor"
      >abs</a
      ><a name="16837" class="Symbol"
      >))</a
      ><a name="16839"
      >
              </a
      ><a name="16854" href="https://agda.github.io/agda-stdlib/Function.html#1835" class="Function Operator"
      >$</a
      ><a name="16855"
      > </a
      ><a name="16856" href="Stlc.html#15790" class="InductiveConstructor"
      >step</a
      ><a name="16860"
      > </a
      ><a name="16861" class="Symbol"
      >(</a
      ><a name="16862" href="Stlc.html#15120" class="InductiveConstructor"
      >red</a
      ><a name="16865"
      > </a
      ><a name="16866" href="Stlc.html#9025" class="InductiveConstructor"
      >true</a
      ><a name="16870" class="Symbol"
      >)</a
      ><a name="16871"
      >
              </a
      ><a name="16886" href="https://agda.github.io/agda-stdlib/Function.html#1835" class="Function Operator"
      >$</a
      ><a name="16887"
      > </a
      ><a name="16888" href="Stlc.html#15790" class="InductiveConstructor"
      >step</a
      ><a name="16892"
      > </a
      ><a name="16893" href="Stlc.html#15486" class="InductiveConstructor"
      >iftrue</a
      ><a name="16899"
      >
              </a
      ><a name="16914" href="https://agda.github.io/agda-stdlib/Function.html#1835" class="Function Operator"
      >$</a
      ><a name="16915"
      > </a
      ><a name="16916" href="Stlc.html#15760" class="InductiveConstructor"
      >refl</a
      >
{% endraw %}</pre>

Example:

$$((\lambda x:bool\rightarrow bool. x)\;((\lambda x:bool. \text{if }x\text{ then }false\text{ else }true)\;true))\Longrightarrow^* false$$.

<pre class="Agda">{% raw %}
<a name="17097" href="Stlc.html#17097" class="Function"
      >step-example4</a
      ><a name="17110"
      > </a
      ><a name="17111" class="Symbol"
      >:</a
      ><a name="17112"
      > </a
      ><a name="17113" class="Symbol"
      >(</a
      ><a name="17114" href="Stlc.html#5582" class="InductiveConstructor"
      >app</a
      ><a name="17117"
      > </a
      ><a name="17118" href="Stlc.html#6560" class="Function"
      >idBB</a
      ><a name="17122"
      > </a
      ><a name="17123" class="Symbol"
      >(</a
      ><a name="17124" href="Stlc.html#5582" class="InductiveConstructor"
      >app</a
      ><a name="17127"
      > </a
      ><a name="17128" href="Stlc.html#6993" class="Function"
      >notB</a
      ><a name="17132"
      > </a
      ><a name="17133" href="Stlc.html#5645" class="InductiveConstructor"
      >true</a
      ><a name="17137" class="Symbol"
      >))</a
      ><a name="17139"
      > </a
      ><a name="17140" href="Stlc.html#15871" class="Function Operator"
      >==&gt;*</a
      ><a name="17144"
      > </a
      ><a name="17145" href="Stlc.html#5660" class="InductiveConstructor"
      >false</a
      ><a name="17150"
      >
</a
      ><a name="17151" href="Stlc.html#17097" class="Function"
      >step-example4</a
      ><a name="17164"
      > </a
      ><a name="17165" class="Symbol"
      >=</a
      ><a name="17166"
      > </a
      ><a name="17167" href="Stlc.html#15790" class="InductiveConstructor"
      >step</a
      ><a name="17171"
      > </a
      ><a name="17172" class="Symbol"
      >(</a
      ><a name="17173" href="Stlc.html#15288" class="InductiveConstructor"
      >app2</a
      ><a name="17177"
      > </a
      ><a name="17178" href="Stlc.html#8977" class="InductiveConstructor"
      >abs</a
      ><a name="17181"
      > </a
      ><a name="17182" class="Symbol"
      >(</a
      ><a name="17183" href="Stlc.html#15120" class="InductiveConstructor"
      >red</a
      ><a name="17186"
      > </a
      ><a name="17187" href="Stlc.html#9025" class="InductiveConstructor"
      >true</a
      ><a name="17191" class="Symbol"
      >))</a
      ><a name="17193"
      >
              </a
      ><a name="17208" href="https://agda.github.io/agda-stdlib/Function.html#1835" class="Function Operator"
      >$</a
      ><a name="17209"
      > </a
      ><a name="17210" href="Stlc.html#15790" class="InductiveConstructor"
      >step</a
      ><a name="17214"
      > </a
      ><a name="17215" class="Symbol"
      >(</a
      ><a name="17216" href="Stlc.html#15288" class="InductiveConstructor"
      >app2</a
      ><a name="17220"
      > </a
      ><a name="17221" href="Stlc.html#8977" class="InductiveConstructor"
      >abs</a
      ><a name="17224"
      > </a
      ><a name="17225" href="Stlc.html#15486" class="InductiveConstructor"
      >iftrue</a
      ><a name="17231" class="Symbol"
      >)</a
      ><a name="17232"
      >
              </a
      ><a name="17247" href="https://agda.github.io/agda-stdlib/Function.html#1835" class="Function Operator"
      >$</a
      ><a name="17248"
      > </a
      ><a name="17249" href="Stlc.html#15790" class="InductiveConstructor"
      >step</a
      ><a name="17253"
      > </a
      ><a name="17254" class="Symbol"
      >(</a
      ><a name="17255" href="Stlc.html#15120" class="InductiveConstructor"
      >red</a
      ><a name="17258"
      > </a
      ><a name="17259" href="Stlc.html#9046" class="InductiveConstructor"
      >false</a
      ><a name="17264" class="Symbol"
      >)</a
      ><a name="17265"
      >
              </a
      ><a name="17280" href="https://agda.github.io/agda-stdlib/Function.html#1835" class="Function Operator"
      >$</a
      ><a name="17281"
      > </a
      ><a name="17282" href="Stlc.html#15760" class="InductiveConstructor"
      >refl</a
      >
{% endraw %}</pre>

#### Exercise: 2 stars (step-example5)

<pre class="Agda">{% raw %}
<a name="17352" class="Keyword"
      >postulate</a
      ><a name="17361"
      >
  </a
      ><a name="17364" href="Stlc.html#17364" class="Postulate"
      >step-example5</a
      ><a name="17377"
      > </a
      ><a name="17378" class="Symbol"
      >:</a
      ><a name="17379"
      > </a
      ><a name="17380" class="Symbol"
      >(</a
      ><a name="17381" href="Stlc.html#5582" class="InductiveConstructor"
      >app</a
      ><a name="17384"
      > </a
      ><a name="17385" class="Symbol"
      >(</a
      ><a name="17386" href="Stlc.html#5582" class="InductiveConstructor"
      >app</a
      ><a name="17389"
      > </a
      ><a name="17390" href="Stlc.html#6714" class="Function"
      >idBBBB</a
      ><a name="17396"
      > </a
      ><a name="17397" href="Stlc.html#6560" class="Function"
      >idBB</a
      ><a name="17401" class="Symbol"
      >)</a
      ><a name="17402"
      > </a
      ><a name="17403" href="Stlc.html#6454" class="Function"
      >idB</a
      ><a name="17406" class="Symbol"
      >)</a
      ><a name="17407"
      > </a
      ><a name="17408" href="Stlc.html#15871" class="Function Operator"
      >==&gt;*</a
      ><a name="17412"
      > </a
      ><a name="17413" href="Stlc.html#6454" class="Function"
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
<a name="18133" href="Stlc.html#18133" class="Function"
      >Ctxt</a
      ><a name="18137"
      > </a
      ><a name="18138" class="Symbol"
      >:</a
      ><a name="18139"
      > </a
      ><a name="18140" class="PrimitiveType"
      >Set</a
      ><a name="18143"
      >
</a
      ><a name="18144" href="Stlc.html#18133" class="Function"
      >Ctxt</a
      ><a name="18148"
      > </a
      ><a name="18149" class="Symbol"
      >=</a
      ><a name="18150"
      > </a
      ><a name="18151" href="Maps.html#9394" class="Function"
      >PartialMap</a
      ><a name="18161"
      > </a
      ><a name="18162" href="Stlc.html#5428" class="Datatype"
      >Type</a
      ><a name="18166"
      >

</a
      ><a name="18168" href="Stlc.html#18168" class="Function"
      >&#8709;</a
      ><a name="18169"
      > </a
      ><a name="18170" class="Symbol"
      >:</a
      ><a name="18171"
      > </a
      ><a name="18172" href="Stlc.html#18133" class="Function"
      >Ctxt</a
      ><a name="18176"
      >
</a
      ><a name="18177" href="Stlc.html#18168" class="Function"
      >&#8709;</a
      ><a name="18178"
      > </a
      ><a name="18179" class="Symbol"
      >=</a
      ><a name="18180"
      > </a
      ><a name="18181" href="Maps.html#9527" class="Function"
      >PartialMap.empty</a
      ><a name="18197"
      >

</a
      ><a name="18199" href="Stlc.html#18199" class="Function Operator"
      >_,_&#8758;_</a
      ><a name="18204"
      > </a
      ><a name="18205" class="Symbol"
      >:</a
      ><a name="18206"
      > </a
      ><a name="18207" href="Stlc.html#18133" class="Function"
      >Ctxt</a
      ><a name="18211"
      > </a
      ><a name="18212" class="Symbol"
      >-&gt;</a
      ><a name="18214"
      > </a
      ><a name="18215" href="Maps.html#2275" class="Datatype"
      >Id</a
      ><a name="18217"
      > </a
      ><a name="18218" class="Symbol"
      >-&gt;</a
      ><a name="18220"
      > </a
      ><a name="18221" href="Stlc.html#5428" class="Datatype"
      >Type</a
      ><a name="18225"
      > </a
      ><a name="18226" class="Symbol"
      >-&gt;</a
      ><a name="18228"
      > </a
      ><a name="18229" href="Stlc.html#18133" class="Function"
      >Ctxt</a
      ><a name="18233"
      >
</a
      ><a name="18234" href="Stlc.html#18199" class="Function Operator"
      >_,_&#8758;_</a
      ><a name="18239"
      > </a
      ><a name="18240" class="Symbol"
      >=</a
      ><a name="18241"
      > </a
      ><a name="18242" href="Maps.html#9616" class="Function"
      >PartialMap.update</a
      >
{% endraw %}</pre>

<div class="hidden">
<pre class="Agda">{% raw %}
<a name="18306" class="Keyword"
      >infixl</a
      ><a name="18312"
      > </a
      ><a name="18313" class="Number"
      >3</a
      ><a name="18314"
      > </a
      ><a name="18315" href="Stlc.html#18199" class="Function Operator"
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
<a name="19095" class="Keyword"
      >data</a
      ><a name="19099"
      > </a
      ><a name="19100" href="Stlc.html#19100" class="Datatype Operator"
      >_&#8866;_&#8758;_</a
      ><a name="19105"
      > </a
      ><a name="19106" class="Symbol"
      >:</a
      ><a name="19107"
      > </a
      ><a name="19108" href="Stlc.html#18133" class="Function"
      >Ctxt</a
      ><a name="19112"
      > </a
      ><a name="19113" class="Symbol"
      >-&gt;</a
      ><a name="19115"
      > </a
      ><a name="19116" href="Stlc.html#5543" class="Datatype"
      >Term</a
      ><a name="19120"
      > </a
      ><a name="19121" class="Symbol"
      >-&gt;</a
      ><a name="19123"
      > </a
      ><a name="19124" href="Stlc.html#5428" class="Datatype"
      >Type</a
      ><a name="19128"
      > </a
      ><a name="19129" class="Symbol"
      >-&gt;</a
      ><a name="19131"
      > </a
      ><a name="19132" class="PrimitiveType"
      >Set</a
      ><a name="19135"
      > </a
      ><a name="19136" class="Keyword"
      >where</a
      ><a name="19141"
      >
  </a
      ><a name="19144" href="Stlc.html#19144" class="InductiveConstructor"
      >var</a
      ><a name="19147"
      >           </a
      ><a name="19158" class="Symbol"
      >:</a
      ><a name="19159"
      > </a
      ><a name="19160" class="Symbol"
      >&#8704;</a
      ><a name="19161"
      > </a
      ><a name="19166" href="Stlc.html#19166" class="Bound"
      >x</a
      ><a name="19167"
      > </a
      ><a name="19188" class="Symbol"
      >&#8594;</a
      ><a name="19189"
      > </a
      ><a name="19190" href="Stlc.html#19163" class="Bound"
      >&#915;</a
      ><a name="19191"
      > </a
      ><a name="19192" href="Stlc.html#19166" class="Bound"
      >x</a
      ><a name="19193"
      > </a
      ><a name="19194" href="Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="19195"
      > </a
      ><a name="19196" href="https://agda.github.io/agda-stdlib/Data.Maybe.Base.html#373" class="InductiveConstructor"
      >just</a
      ><a name="19200"
      > </a
      ><a name="19201" href="Stlc.html#19169" class="Bound"
      >A</a
      ><a name="19202"
      >
                </a
      ><a name="19219" class="Symbol"
      >&#8594;</a
      ><a name="19220"
      > </a
      ><a name="19221" href="Stlc.html#19163" class="Bound"
      >&#915;</a
      ><a name="19222"
      > </a
      ><a name="19223" href="Stlc.html#19100" class="Datatype Operator"
      >&#8866;</a
      ><a name="19224"
      > </a
      ><a name="19225" href="Stlc.html#5562" class="InductiveConstructor"
      >var</a
      ><a name="19228"
      > </a
      ><a name="19229" href="Stlc.html#19166" class="Bound"
      >x</a
      ><a name="19230"
      > </a
      ><a name="19231" href="Stlc.html#19100" class="Datatype Operator"
      >&#8758;</a
      ><a name="19232"
      > </a
      ><a name="19233" href="Stlc.html#19169" class="Bound"
      >A</a
      ><a name="19234"
      >
  </a
      ><a name="19237" href="Stlc.html#19237" class="InductiveConstructor"
      >abs</a
      ><a name="19240"
      >           </a
      ><a name="19251" class="Symbol"
      >:</a
      ><a name="19252"
      > </a
      ><a name="19253" class="Symbol"
      >&#8704;</a
      ><a name="19254"
      > </a
      ><a name="19291" class="Symbol"
      >&#8594;</a
      ><a name="19292"
      > </a
      ><a name="19293" href="Stlc.html#19256" class="Bound"
      >&#915;</a
      ><a name="19294"
      > </a
      ><a name="19295" href="Stlc.html#18199" class="Function Operator"
      >,</a
      ><a name="19296"
      > </a
      ><a name="19297" href="Stlc.html#19260" class="Bound"
      >x</a
      ><a name="19298"
      > </a
      ><a name="19299" href="Stlc.html#18199" class="Function Operator"
      >&#8758;</a
      ><a name="19300"
      > </a
      ><a name="19301" href="Stlc.html#19264" class="Bound"
      >A</a
      ><a name="19302"
      > </a
      ><a name="19303" href="Stlc.html#19100" class="Datatype Operator"
      >&#8866;</a
      ><a name="19304"
      > </a
      ><a name="19305" href="Stlc.html#19272" class="Bound"
      >s</a
      ><a name="19306"
      > </a
      ><a name="19307" href="Stlc.html#19100" class="Datatype Operator"
      >&#8758;</a
      ><a name="19308"
      > </a
      ><a name="19309" href="Stlc.html#19268" class="Bound"
      >B</a
      ><a name="19310"
      >
                </a
      ><a name="19327" class="Symbol"
      >&#8594;</a
      ><a name="19328"
      > </a
      ><a name="19329" href="Stlc.html#19256" class="Bound"
      >&#915;</a
      ><a name="19330"
      > </a
      ><a name="19331" href="Stlc.html#19100" class="Datatype Operator"
      >&#8866;</a
      ><a name="19332"
      > </a
      ><a name="19333" href="Stlc.html#5611" class="InductiveConstructor"
      >abs</a
      ><a name="19336"
      > </a
      ><a name="19337" href="Stlc.html#19260" class="Bound"
      >x</a
      ><a name="19338"
      > </a
      ><a name="19339" href="Stlc.html#19264" class="Bound"
      >A</a
      ><a name="19340"
      > </a
      ><a name="19341" href="Stlc.html#19272" class="Bound"
      >s</a
      ><a name="19342"
      > </a
      ><a name="19343" href="Stlc.html#19100" class="Datatype Operator"
      >&#8758;</a
      ><a name="19344"
      > </a
      ><a name="19345" href="Stlc.html#19264" class="Bound"
      >A</a
      ><a name="19346"
      > </a
      ><a name="19347" href="Stlc.html#5461" class="InductiveConstructor Operator"
      >&#8658;</a
      ><a name="19348"
      > </a
      ><a name="19349" href="Stlc.html#19268" class="Bound"
      >B</a
      ><a name="19350"
      >
  </a
      ><a name="19353" href="Stlc.html#19353" class="InductiveConstructor"
      >app</a
      ><a name="19356"
      >           </a
      ><a name="19367" class="Symbol"
      >:</a
      ><a name="19368"
      > </a
      ><a name="19369" class="Symbol"
      >&#8704;</a
      ><a name="19370"
      > </a
      ><a name="19407" class="Symbol"
      >&#8594;</a
      ><a name="19408"
      > </a
      ><a name="19409" href="Stlc.html#19372" class="Bound"
      >&#915;</a
      ><a name="19410"
      > </a
      ><a name="19411" href="Stlc.html#19100" class="Datatype Operator"
      >&#8866;</a
      ><a name="19412"
      > </a
      ><a name="19413" href="Stlc.html#19384" class="Bound"
      >s</a
      ><a name="19414"
      > </a
      ><a name="19415" href="Stlc.html#19100" class="Datatype Operator"
      >&#8758;</a
      ><a name="19416"
      > </a
      ><a name="19417" href="Stlc.html#19376" class="Bound"
      >A</a
      ><a name="19418"
      > </a
      ><a name="19419" href="Stlc.html#5461" class="InductiveConstructor Operator"
      >&#8658;</a
      ><a name="19420"
      > </a
      ><a name="19421" href="Stlc.html#19380" class="Bound"
      >B</a
      ><a name="19422"
      >
                </a
      ><a name="19439" class="Symbol"
      >&#8594;</a
      ><a name="19440"
      > </a
      ><a name="19441" href="Stlc.html#19372" class="Bound"
      >&#915;</a
      ><a name="19442"
      > </a
      ><a name="19443" href="Stlc.html#19100" class="Datatype Operator"
      >&#8866;</a
      ><a name="19444"
      > </a
      ><a name="19445" href="Stlc.html#19388" class="Bound"
      >t</a
      ><a name="19446"
      > </a
      ><a name="19447" href="Stlc.html#19100" class="Datatype Operator"
      >&#8758;</a
      ><a name="19448"
      > </a
      ><a name="19449" href="Stlc.html#19376" class="Bound"
      >A</a
      ><a name="19450"
      >
                </a
      ><a name="19467" class="Symbol"
      >&#8594;</a
      ><a name="19468"
      > </a
      ><a name="19469" href="Stlc.html#19372" class="Bound"
      >&#915;</a
      ><a name="19470"
      > </a
      ><a name="19471" href="Stlc.html#19100" class="Datatype Operator"
      >&#8866;</a
      ><a name="19472"
      > </a
      ><a name="19473" href="Stlc.html#5582" class="InductiveConstructor"
      >app</a
      ><a name="19476"
      > </a
      ><a name="19477" href="Stlc.html#19384" class="Bound"
      >s</a
      ><a name="19478"
      > </a
      ><a name="19479" href="Stlc.html#19388" class="Bound"
      >t</a
      ><a name="19480"
      > </a
      ><a name="19481" href="Stlc.html#19100" class="Datatype Operator"
      >&#8758;</a
      ><a name="19482"
      > </a
      ><a name="19483" href="Stlc.html#19380" class="Bound"
      >B</a
      ><a name="19484"
      >
  </a
      ><a name="19487" href="Stlc.html#19487" class="InductiveConstructor"
      >true</a
      ><a name="19491"
      >          </a
      ><a name="19501" class="Symbol"
      >:</a
      ><a name="19502"
      > </a
      ><a name="19503" class="Symbol"
      >&#8704;</a
      ><a name="19504"
      > </a
      ><a name="19525" class="Symbol"
      >&#8594;</a
      ><a name="19526"
      > </a
      ><a name="19527" href="Stlc.html#19506" class="Bound"
      >&#915;</a
      ><a name="19528"
      > </a
      ><a name="19529" href="Stlc.html#19100" class="Datatype Operator"
      >&#8866;</a
      ><a name="19530"
      > </a
      ><a name="19531" href="Stlc.html#5645" class="InductiveConstructor"
      >true</a
      ><a name="19535"
      >  </a
      ><a name="19537" href="Stlc.html#19100" class="Datatype Operator"
      >&#8758;</a
      ><a name="19538"
      > </a
      ><a name="19539" href="Stlc.html#5447" class="InductiveConstructor"
      >bool</a
      ><a name="19543"
      >
  </a
      ><a name="19546" href="Stlc.html#19546" class="InductiveConstructor"
      >false</a
      ><a name="19551"
      >         </a
      ><a name="19560" class="Symbol"
      >:</a
      ><a name="19561"
      > </a
      ><a name="19562" class="Symbol"
      >&#8704;</a
      ><a name="19563"
      > </a
      ><a name="19584" class="Symbol"
      >&#8594;</a
      ><a name="19585"
      > </a
      ><a name="19586" href="Stlc.html#19565" class="Bound"
      >&#915;</a
      ><a name="19587"
      > </a
      ><a name="19588" href="Stlc.html#19100" class="Datatype Operator"
      >&#8866;</a
      ><a name="19589"
      > </a
      ><a name="19590" href="Stlc.html#5660" class="InductiveConstructor"
      >false</a
      ><a name="19595"
      > </a
      ><a name="19596" href="Stlc.html#19100" class="Datatype Operator"
      >&#8758;</a
      ><a name="19597"
      > </a
      ><a name="19598" href="Stlc.html#5447" class="InductiveConstructor"
      >bool</a
      ><a name="19602"
      >
  </a
      ><a name="19605" href="Stlc.html#19605" class="InductiveConstructor Operator"
      >if_then_else_</a
      ><a name="19618"
      > </a
      ><a name="19619" class="Symbol"
      >:</a
      ><a name="19620"
      > </a
      ><a name="19621" class="Symbol"
      >&#8704;</a
      ><a name="19622"
      > </a
      ><a name="19659" class="Symbol"
      >&#8594;</a
      ><a name="19660"
      > </a
      ><a name="19661" href="Stlc.html#19624" class="Bound"
      >&#915;</a
      ><a name="19662"
      > </a
      ><a name="19663" href="Stlc.html#19100" class="Datatype Operator"
      >&#8866;</a
      ><a name="19664"
      > </a
      ><a name="19665" href="Stlc.html#19628" class="Bound"
      >s</a
      ><a name="19666"
      > </a
      ><a name="19667" href="Stlc.html#19100" class="Datatype Operator"
      >&#8758;</a
      ><a name="19668"
      > </a
      ><a name="19669" href="Stlc.html#5447" class="InductiveConstructor"
      >bool</a
      ><a name="19673"
      >
                </a
      ><a name="19690" class="Symbol"
      >&#8594;</a
      ><a name="19691"
      > </a
      ><a name="19692" href="Stlc.html#19624" class="Bound"
      >&#915;</a
      ><a name="19693"
      > </a
      ><a name="19694" href="Stlc.html#19100" class="Datatype Operator"
      >&#8866;</a
      ><a name="19695"
      > </a
      ><a name="19696" href="Stlc.html#19632" class="Bound"
      >t</a
      ><a name="19697"
      > </a
      ><a name="19698" href="Stlc.html#19100" class="Datatype Operator"
      >&#8758;</a
      ><a name="19699"
      > </a
      ><a name="19700" href="Stlc.html#19640" class="Bound"
      >A</a
      ><a name="19701"
      >
                </a
      ><a name="19718" class="Symbol"
      >&#8594;</a
      ><a name="19719"
      > </a
      ><a name="19720" href="Stlc.html#19624" class="Bound"
      >&#915;</a
      ><a name="19721"
      > </a
      ><a name="19722" href="Stlc.html#19100" class="Datatype Operator"
      >&#8866;</a
      ><a name="19723"
      > </a
      ><a name="19724" href="Stlc.html#19636" class="Bound"
      >u</a
      ><a name="19725"
      > </a
      ><a name="19726" href="Stlc.html#19100" class="Datatype Operator"
      >&#8758;</a
      ><a name="19727"
      > </a
      ><a name="19728" href="Stlc.html#19640" class="Bound"
      >A</a
      ><a name="19729"
      >
                </a
      ><a name="19746" class="Symbol"
      >&#8594;</a
      ><a name="19747"
      > </a
      ><a name="19748" href="Stlc.html#19624" class="Bound"
      >&#915;</a
      ><a name="19749"
      > </a
      ><a name="19750" href="Stlc.html#19100" class="Datatype Operator"
      >&#8866;</a
      ><a name="19751"
      > </a
      ><a name="19752" href="Stlc.html#5675" class="InductiveConstructor Operator"
      >if</a
      ><a name="19754"
      > </a
      ><a name="19755" href="Stlc.html#19628" class="Bound"
      >s</a
      ><a name="19756"
      > </a
      ><a name="19757" href="Stlc.html#5675" class="InductiveConstructor Operator"
      >then</a
      ><a name="19761"
      > </a
      ><a name="19762" href="Stlc.html#19632" class="Bound"
      >t</a
      ><a name="19763"
      > </a
      ><a name="19764" href="Stlc.html#5675" class="InductiveConstructor Operator"
      >else</a
      ><a name="19768"
      > </a
      ><a name="19769" href="Stlc.html#19636" class="Bound"
      >u</a
      ><a name="19770"
      > </a
      ><a name="19771" href="Stlc.html#19100" class="Datatype Operator"
      >&#8758;</a
      ><a name="19772"
      > </a
      ><a name="19773" href="Stlc.html#19640" class="Bound"
      >A</a
      >
{% endraw %}</pre>

<div class="hidden">
<pre class="Agda">{% raw %}
<a name="19821" class="Keyword"
      >infix</a
      ><a name="19826"
      > </a
      ><a name="19827" class="Number"
      >1</a
      ><a name="19828"
      > </a
      ><a name="19829" href="Stlc.html#19100" class="Datatype Operator"
      >_&#8866;_&#8758;_</a
      >
{% endraw %}</pre>
</div>


### Examples

<pre class="Agda">{% raw %}
<a name="19882" href="Stlc.html#19882" class="Function"
      >typing-example1</a
      ><a name="19897"
      > </a
      ><a name="19898" class="Symbol"
      >:</a
      ><a name="19899"
      > </a
      ><a name="19900" href="Stlc.html#18168" class="Function"
      >&#8709;</a
      ><a name="19901"
      > </a
      ><a name="19902" href="Stlc.html#19100" class="Datatype Operator"
      >&#8866;</a
      ><a name="19903"
      > </a
      ><a name="19904" href="Stlc.html#6454" class="Function"
      >idB</a
      ><a name="19907"
      > </a
      ><a name="19908" href="Stlc.html#19100" class="Datatype Operator"
      >&#8758;</a
      ><a name="19909"
      > </a
      ><a name="19910" href="Stlc.html#5447" class="InductiveConstructor"
      >bool</a
      ><a name="19914"
      > </a
      ><a name="19915" href="Stlc.html#5461" class="InductiveConstructor Operator"
      >&#8658;</a
      ><a name="19916"
      > </a
      ><a name="19917" href="Stlc.html#5447" class="InductiveConstructor"
      >bool</a
      ><a name="19921"
      >
</a
      ><a name="19922" href="Stlc.html#19882" class="Function"
      >typing-example1</a
      ><a name="19937"
      > </a
      ><a name="19938" class="Symbol"
      >=</a
      ><a name="19939"
      > </a
      ><a name="19940" href="Stlc.html#19237" class="InductiveConstructor"
      >abs</a
      ><a name="19943"
      > </a
      ><a name="19944" class="Symbol"
      >(</a
      ><a name="19945" href="Stlc.html#19144" class="InductiveConstructor"
      >var</a
      ><a name="19948"
      > </a
      ><a name="19949" href="Stlc.html#6244" class="Function"
      >x</a
      ><a name="19950"
      > </a
      ><a name="19951" href="Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="19955" class="Symbol"
      >)</a
      >
{% endraw %}</pre>

Another example:

$$\varnothing\vdash \lambda x:A. \lambda y:A\rightarrow A. y\;(y\;x) : A\rightarrow (A\rightarrow A)\rightarrow A$$.

<pre class="Agda">{% raw %}
<a name="20118" href="Stlc.html#20118" class="Function"
      >typing-example2</a
      ><a name="20133"
      > </a
      ><a name="20134" class="Symbol"
      >:</a
      ><a name="20135"
      > </a
      ><a name="20136" href="Stlc.html#18168" class="Function"
      >&#8709;</a
      ><a name="20137"
      > </a
      ><a name="20138" href="Stlc.html#19100" class="Datatype Operator"
      >&#8866;</a
      ><a name="20139"
      >
  </a
      ><a name="20142" class="Symbol"
      >(</a
      ><a name="20143" href="Stlc.html#5611" class="InductiveConstructor"
      >abs</a
      ><a name="20146"
      > </a
      ><a name="20147" href="Stlc.html#6244" class="Function"
      >x</a
      ><a name="20148"
      > </a
      ><a name="20149" href="Stlc.html#5447" class="InductiveConstructor"
      >bool</a
      ><a name="20153"
      >
    </a
      ><a name="20158" class="Symbol"
      >(</a
      ><a name="20159" href="Stlc.html#5611" class="InductiveConstructor"
      >abs</a
      ><a name="20162"
      > </a
      ><a name="20163" href="Stlc.html#6253" class="Function"
      >y</a
      ><a name="20164"
      > </a
      ><a name="20165" class="Symbol"
      >(</a
      ><a name="20166" href="Stlc.html#5447" class="InductiveConstructor"
      >bool</a
      ><a name="20170"
      > </a
      ><a name="20171" href="Stlc.html#5461" class="InductiveConstructor Operator"
      >&#8658;</a
      ><a name="20172"
      > </a
      ><a name="20173" href="Stlc.html#5447" class="InductiveConstructor"
      >bool</a
      ><a name="20177" class="Symbol"
      >)</a
      ><a name="20178"
      >
      </a
      ><a name="20185" class="Symbol"
      >(</a
      ><a name="20186" href="Stlc.html#5582" class="InductiveConstructor"
      >app</a
      ><a name="20189"
      > </a
      ><a name="20190" class="Symbol"
      >(</a
      ><a name="20191" href="Stlc.html#5562" class="InductiveConstructor"
      >var</a
      ><a name="20194"
      > </a
      ><a name="20195" href="Stlc.html#6253" class="Function"
      >y</a
      ><a name="20196" class="Symbol"
      >)</a
      ><a name="20197"
      >
        </a
      ><a name="20206" class="Symbol"
      >(</a
      ><a name="20207" href="Stlc.html#5582" class="InductiveConstructor"
      >app</a
      ><a name="20210"
      > </a
      ><a name="20211" class="Symbol"
      >(</a
      ><a name="20212" href="Stlc.html#5562" class="InductiveConstructor"
      >var</a
      ><a name="20215"
      > </a
      ><a name="20216" href="Stlc.html#6253" class="Function"
      >y</a
      ><a name="20217" class="Symbol"
      >)</a
      ><a name="20218"
      > </a
      ><a name="20219" class="Symbol"
      >(</a
      ><a name="20220" href="Stlc.html#5562" class="InductiveConstructor"
      >var</a
      ><a name="20223"
      > </a
      ><a name="20224" href="Stlc.html#6244" class="Function"
      >x</a
      ><a name="20225" class="Symbol"
      >)))))</a
      ><a name="20230"
      >
  </a
      ><a name="20233" href="Stlc.html#19100" class="Datatype Operator"
      >&#8758;</a
      ><a name="20234"
      > </a
      ><a name="20235" class="Symbol"
      >(</a
      ><a name="20236" href="Stlc.html#5447" class="InductiveConstructor"
      >bool</a
      ><a name="20240"
      > </a
      ><a name="20241" href="Stlc.html#5461" class="InductiveConstructor Operator"
      >&#8658;</a
      ><a name="20242"
      > </a
      ><a name="20243" class="Symbol"
      >(</a
      ><a name="20244" href="Stlc.html#5447" class="InductiveConstructor"
      >bool</a
      ><a name="20248"
      > </a
      ><a name="20249" href="Stlc.html#5461" class="InductiveConstructor Operator"
      >&#8658;</a
      ><a name="20250"
      > </a
      ><a name="20251" href="Stlc.html#5447" class="InductiveConstructor"
      >bool</a
      ><a name="20255" class="Symbol"
      >)</a
      ><a name="20256"
      > </a
      ><a name="20257" href="Stlc.html#5461" class="InductiveConstructor Operator"
      >&#8658;</a
      ><a name="20258"
      > </a
      ><a name="20259" href="Stlc.html#5447" class="InductiveConstructor"
      >bool</a
      ><a name="20263" class="Symbol"
      >)</a
      ><a name="20264"
      >
</a
      ><a name="20265" href="Stlc.html#20118" class="Function"
      >typing-example2</a
      ><a name="20280"
      > </a
      ><a name="20281" class="Symbol"
      >=</a
      ><a name="20282"
      >
  </a
      ><a name="20285" class="Symbol"
      >(</a
      ><a name="20286" href="Stlc.html#19237" class="InductiveConstructor"
      >abs</a
      ><a name="20289"
      >
    </a
      ><a name="20294" class="Symbol"
      >(</a
      ><a name="20295" href="Stlc.html#19237" class="InductiveConstructor"
      >abs</a
      ><a name="20298"
      >
      </a
      ><a name="20305" class="Symbol"
      >(</a
      ><a name="20306" href="Stlc.html#19353" class="InductiveConstructor"
      >app</a
      ><a name="20309"
      > </a
      ><a name="20310" class="Symbol"
      >(</a
      ><a name="20311" href="Stlc.html#19144" class="InductiveConstructor"
      >var</a
      ><a name="20314"
      > </a
      ><a name="20315" href="Stlc.html#6253" class="Function"
      >y</a
      ><a name="20316"
      > </a
      ><a name="20317" href="Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="20321" class="Symbol"
      >)</a
      ><a name="20322"
      >
        </a
      ><a name="20331" class="Symbol"
      >(</a
      ><a name="20332" href="Stlc.html#19353" class="InductiveConstructor"
      >app</a
      ><a name="20335"
      > </a
      ><a name="20336" class="Symbol"
      >(</a
      ><a name="20337" href="Stlc.html#19144" class="InductiveConstructor"
      >var</a
      ><a name="20340"
      > </a
      ><a name="20341" href="Stlc.html#6253" class="Function"
      >y</a
      ><a name="20342"
      > </a
      ><a name="20343" href="Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="20347" class="Symbol"
      >)</a
      ><a name="20348"
      > </a
      ><a name="20349" class="Symbol"
      >(</a
      ><a name="20350" href="Stlc.html#19144" class="InductiveConstructor"
      >var</a
      ><a name="20353"
      > </a
      ><a name="20354" href="Stlc.html#6244" class="Function"
      >x</a
      ><a name="20355"
      > </a
      ><a name="20356" href="Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="20360" class="Symbol"
      >)</a
      ><a name="20361"
      > </a
      ><a name="20362" class="Symbol"
      >))))</a
      >
{% endraw %}</pre>

#### Exercise: 2 stars (typing-example3)
Formally prove the following typing derivation holds:

$$\exists A, \varnothing\vdash \lambda x:bool\rightarrow B. \lambda y:bool\rightarrow bool. \lambda z:bool. y\;(x\;z) : A$$.

<pre class="Agda">{% raw %}
<a name="20614" class="Keyword"
      >postulate</a
      ><a name="20623"
      >
  </a
      ><a name="20626" href="Stlc.html#20626" class="Postulate"
      >typing-example3</a
      ><a name="20641"
      > </a
      ><a name="20642" class="Symbol"
      >:</a
      ><a name="20643"
      > </a
      ><a name="20644" href="https://agda.github.io/agda-stdlib/Data.Product.html#823" class="Function"
      >&#8707;</a
      ><a name="20645"
      > </a
      ><a name="20646" class="Symbol"
      >&#955;</a
      ><a name="20647"
      > </a
      ><a name="20648" href="Stlc.html#20648" class="Bound"
      >A</a
      ><a name="20649"
      > </a
      ><a name="20650" class="Symbol"
      >&#8594;</a
      ><a name="20651"
      > </a
      ><a name="20652" href="Stlc.html#18168" class="Function"
      >&#8709;</a
      ><a name="20653"
      > </a
      ><a name="20654" href="Stlc.html#19100" class="Datatype Operator"
      >&#8866;</a
      ><a name="20655"
      >
    </a
      ><a name="20660" class="Symbol"
      >(</a
      ><a name="20661" href="Stlc.html#5611" class="InductiveConstructor"
      >abs</a
      ><a name="20664"
      > </a
      ><a name="20665" href="Stlc.html#6244" class="Function"
      >x</a
      ><a name="20666"
      > </a
      ><a name="20667" class="Symbol"
      >(</a
      ><a name="20668" href="Stlc.html#5447" class="InductiveConstructor"
      >bool</a
      ><a name="20672"
      > </a
      ><a name="20673" href="Stlc.html#5461" class="InductiveConstructor Operator"
      >&#8658;</a
      ><a name="20674"
      > </a
      ><a name="20675" href="Stlc.html#5447" class="InductiveConstructor"
      >bool</a
      ><a name="20679" class="Symbol"
      >)</a
      ><a name="20680"
      >
      </a
      ><a name="20687" class="Symbol"
      >(</a
      ><a name="20688" href="Stlc.html#5611" class="InductiveConstructor"
      >abs</a
      ><a name="20691"
      > </a
      ><a name="20692" href="Stlc.html#6253" class="Function"
      >y</a
      ><a name="20693"
      > </a
      ><a name="20694" class="Symbol"
      >(</a
      ><a name="20695" href="Stlc.html#5447" class="InductiveConstructor"
      >bool</a
      ><a name="20699"
      > </a
      ><a name="20700" href="Stlc.html#5461" class="InductiveConstructor Operator"
      >&#8658;</a
      ><a name="20701"
      > </a
      ><a name="20702" href="Stlc.html#5447" class="InductiveConstructor"
      >bool</a
      ><a name="20706" class="Symbol"
      >)</a
      ><a name="20707"
      >
        </a
      ><a name="20716" class="Symbol"
      >(</a
      ><a name="20717" href="Stlc.html#5611" class="InductiveConstructor"
      >abs</a
      ><a name="20720"
      > </a
      ><a name="20721" href="Stlc.html#6262" class="Function"
      >z</a
      ><a name="20722"
      > </a
      ><a name="20723" href="Stlc.html#5447" class="InductiveConstructor"
      >bool</a
      ><a name="20727"
      >
          </a
      ><a name="20738" class="Symbol"
      >(</a
      ><a name="20739" href="Stlc.html#5582" class="InductiveConstructor"
      >app</a
      ><a name="20742"
      > </a
      ><a name="20743" class="Symbol"
      >(</a
      ><a name="20744" href="Stlc.html#5562" class="InductiveConstructor"
      >var</a
      ><a name="20747"
      > </a
      ><a name="20748" href="Stlc.html#6253" class="Function"
      >y</a
      ><a name="20749" class="Symbol"
      >)</a
      ><a name="20750"
      > </a
      ><a name="20751" class="Symbol"
      >(</a
      ><a name="20752" href="Stlc.html#5582" class="InductiveConstructor"
      >app</a
      ><a name="20755"
      > </a
      ><a name="20756" class="Symbol"
      >(</a
      ><a name="20757" href="Stlc.html#5562" class="InductiveConstructor"
      >var</a
      ><a name="20760"
      > </a
      ><a name="20761" href="Stlc.html#6244" class="Function"
      >x</a
      ><a name="20762" class="Symbol"
      >)</a
      ><a name="20763"
      > </a
      ><a name="20764" class="Symbol"
      >(</a
      ><a name="20765" href="Stlc.html#5562" class="InductiveConstructor"
      >var</a
      ><a name="20768"
      > </a
      ><a name="20769" href="Stlc.html#6262" class="Function"
      >z</a
      ><a name="20770" class="Symbol"
      >))))))</a
      ><a name="20776"
      > </a
      ><a name="20777" href="Stlc.html#19100" class="Datatype Operator"
      >&#8758;</a
      ><a name="20778"
      > </a
      ><a name="20779" href="Stlc.html#20648" class="Bound"
      >A</a
      >
{% endraw %}</pre>

We can also show that terms are _not_ typable.  For example, let's
formally check that there is no typing derivation assigning a type
to the term $$\lambda x:bool. \lambda y:bool. x\;y$$---i.e.,


$$\nexists A, \varnothing\vdash \lambda x:bool. \lambda y:bool. x\;y : A$$.

<pre class="Agda">{% raw %}
<a name="21080" class="Keyword"
      >postulate</a
      ><a name="21089"
      >
  </a
      ><a name="21092" href="Stlc.html#21092" class="Postulate"
      >typing-nonexample1</a
      ><a name="21110"
      > </a
      ><a name="21111" class="Symbol"
      >:</a
      ><a name="21112"
      > </a
      ><a name="21113" href="https://agda.github.io/agda-stdlib/Data.Product.html#884" class="Function"
      >&#8708;</a
      ><a name="21114"
      > </a
      ><a name="21115" class="Symbol"
      >&#955;</a
      ><a name="21116"
      > </a
      ><a name="21117" href="Stlc.html#21117" class="Bound"
      >A</a
      ><a name="21118"
      > </a
      ><a name="21119" class="Symbol"
      >&#8594;</a
      ><a name="21120"
      > </a
      ><a name="21121" href="Stlc.html#18168" class="Function"
      >&#8709;</a
      ><a name="21122"
      > </a
      ><a name="21123" href="Stlc.html#19100" class="Datatype Operator"
      >&#8866;</a
      ><a name="21124"
      >
    </a
      ><a name="21129" class="Symbol"
      >(</a
      ><a name="21130" href="Stlc.html#5611" class="InductiveConstructor"
      >abs</a
      ><a name="21133"
      > </a
      ><a name="21134" href="Stlc.html#6244" class="Function"
      >x</a
      ><a name="21135"
      > </a
      ><a name="21136" href="Stlc.html#5447" class="InductiveConstructor"
      >bool</a
      ><a name="21140"
      >
      </a
      ><a name="21147" class="Symbol"
      >(</a
      ><a name="21148" href="Stlc.html#5611" class="InductiveConstructor"
      >abs</a
      ><a name="21151"
      > </a
      ><a name="21152" href="Stlc.html#6253" class="Function"
      >y</a
      ><a name="21153"
      > </a
      ><a name="21154" href="Stlc.html#5447" class="InductiveConstructor"
      >bool</a
      ><a name="21158"
      >
        </a
      ><a name="21167" class="Symbol"
      >(</a
      ><a name="21168" href="Stlc.html#5582" class="InductiveConstructor"
      >app</a
      ><a name="21171"
      > </a
      ><a name="21172" class="Symbol"
      >(</a
      ><a name="21173" href="Stlc.html#5562" class="InductiveConstructor"
      >var</a
      ><a name="21176"
      > </a
      ><a name="21177" href="Stlc.html#6244" class="Function"
      >x</a
      ><a name="21178" class="Symbol"
      >)</a
      ><a name="21179"
      > </a
      ><a name="21180" class="Symbol"
      >(</a
      ><a name="21181" href="Stlc.html#5562" class="InductiveConstructor"
      >var</a
      ><a name="21184"
      > </a
      ><a name="21185" href="Stlc.html#6253" class="Function"
      >y</a
      ><a name="21186" class="Symbol"
      >))))</a
      ><a name="21190"
      > </a
      ><a name="21191" href="Stlc.html#19100" class="Datatype Operator"
      >&#8758;</a
      ><a name="21192"
      > </a
      ><a name="21193" href="Stlc.html#21117" class="Bound"
      >A</a
      >
{% endraw %}</pre>

#### Exercise: 3 stars, optional (typing-nonexample2)
Another nonexample:

$$\nexists A, \exists B, \varnothing\vdash \lambda x:A. x\;x : B$$.

<pre class="Agda">{% raw %}
<a name="21364" class="Keyword"
      >postulate</a
      ><a name="21373"
      >
  </a
      ><a name="21376" href="Stlc.html#21376" class="Postulate"
      >typing-nonexample2</a
      ><a name="21394"
      > </a
      ><a name="21395" class="Symbol"
      >:</a
      ><a name="21396"
      > </a
      ><a name="21397" href="https://agda.github.io/agda-stdlib/Data.Product.html#884" class="Function"
      >&#8708;</a
      ><a name="21398"
      > </a
      ><a name="21399" class="Symbol"
      >&#955;</a
      ><a name="21400"
      > </a
      ><a name="21401" href="Stlc.html#21401" class="Bound"
      >A</a
      ><a name="21402"
      > </a
      ><a name="21403" class="Symbol"
      >&#8594;</a
      ><a name="21404"
      > </a
      ><a name="21405" href="https://agda.github.io/agda-stdlib/Data.Product.html#823" class="Function"
      >&#8707;</a
      ><a name="21406"
      > </a
      ><a name="21407" class="Symbol"
      >&#955;</a
      ><a name="21408"
      > </a
      ><a name="21409" href="Stlc.html#21409" class="Bound"
      >B</a
      ><a name="21410"
      > </a
      ><a name="21411" class="Symbol"
      >&#8594;</a
      ><a name="21412"
      > </a
      ><a name="21413" href="Stlc.html#18168" class="Function"
      >&#8709;</a
      ><a name="21414"
      > </a
      ><a name="21415" href="Stlc.html#19100" class="Datatype Operator"
      >&#8866;</a
      ><a name="21416"
      >
    </a
      ><a name="21421" class="Symbol"
      >(</a
      ><a name="21422" href="Stlc.html#5611" class="InductiveConstructor"
      >abs</a
      ><a name="21425"
      > </a
      ><a name="21426" href="Stlc.html#6244" class="Function"
      >x</a
      ><a name="21427"
      > </a
      ><a name="21428" href="Stlc.html#21409" class="Bound"
      >B</a
      ><a name="21429"
      > </a
      ><a name="21430" class="Symbol"
      >(</a
      ><a name="21431" href="Stlc.html#5582" class="InductiveConstructor"
      >app</a
      ><a name="21434"
      > </a
      ><a name="21435" class="Symbol"
      >(</a
      ><a name="21436" href="Stlc.html#5562" class="InductiveConstructor"
      >var</a
      ><a name="21439"
      > </a
      ><a name="21440" href="Stlc.html#6244" class="Function"
      >x</a
      ><a name="21441" class="Symbol"
      >)</a
      ><a name="21442"
      > </a
      ><a name="21443" class="Symbol"
      >(</a
      ><a name="21444" href="Stlc.html#5562" class="InductiveConstructor"
      >var</a
      ><a name="21447"
      > </a
      ><a name="21448" href="Stlc.html#6244" class="Function"
      >x</a
      ><a name="21449" class="Symbol"
      >)))</a
      ><a name="21452"
      > </a
      ><a name="21453" href="Stlc.html#19100" class="Datatype Operator"
      >&#8758;</a
      ><a name="21454"
      > </a
      ><a name="21455" href="Stlc.html#21401" class="Bound"
      >A</a
      >
{% endraw %}</pre>
