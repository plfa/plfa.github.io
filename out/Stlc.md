---
title     : "Stlc: The Simply Typed Lambda-Calculus"
layout    : page
permalink : /Stlc
---

The _lambda-calculus_, first published by the logician Alonzo Church in
1932, is a core calculus with only three syntactic constructs:
variables, abstraction, and application.  It embodies the concept of
_functional abstraction_, which shows up in almost every programming
language in some form (as functions, procedures, or methods).
The _simply-typed lambda calculus_ (or STLC) is a variant of the
lambda calculus published by Church in 1940.  It has just the three
constructs above for function types, plus whatever else is required
for base types. Church had a minimal base type with no operations;
we will be slightly more pragmatic and choose booleans as our base type.

This chapter formalises the STLC (syntax, small-step semantics, and typing rules),
and the next chapter reviews its main properties (progress and preservation).
The new technical challenges arise from the mechanisms of
_variable binding_ and _substitution_.

<!--
We've already seen how to formalize a language with
variables ([Imp]({{ "Imp" | relative_url }})).
There, however, the variables were all global.
In the STLC, we need to handle the variables that name the
parameters to functions, and these are _bound_ variables.
Moreover, instead of just looking up variables in a global store,
we'll need to reduce function applications by _substituting_
arguments for parameters in function bodies.
-->

We choose booleans as our base type for simplicity.  At the end of the
chapter we'll see how to add numbers as a base type, and in later
chapters we'll enrich STLC with useful constructs like pairs, sums,
lists, records, subtyping, and mutable state.

## Imports

<pre class="Agda">{% raw %}
<a name="1756" class="Keyword"
      >open</a
      ><a name="1760"
      > </a
      ><a name="1761" class="Keyword"
      >import</a
      ><a name="1767"
      > </a
      ><a name="1768" class="Module"
      >Maps</a
      ><a name="1772"
      > </a
      ><a name="1773" class="Keyword"
      >using</a
      ><a name="1778"
      > </a
      ><a name="1779" class="Symbol"
      >(</a
      ><a name="1780" href="Maps.html#2171" class="Datatype"
      >Id</a
      ><a name="1782" class="Symbol"
      >;</a
      ><a name="1783"
      > </a
      ><a name="1784" href="Maps.html#2188" class="InductiveConstructor"
      >id</a
      ><a name="1786" class="Symbol"
      >;</a
      ><a name="1787"
      > </a
      ><a name="1788" href="Maps.html#2509" class="Function Operator"
      >_&#8799;_</a
      ><a name="1791" class="Symbol"
      >;</a
      ><a name="1792"
      > </a
      ><a name="1793" href="Maps.html#10132" class="Function"
      >PartialMap</a
      ><a name="1803" class="Symbol"
      >;</a
      ><a name="1804"
      > </a
      ><a name="1805" class="Keyword"
      >module</a
      ><a name="1811"
      > </a
      ><a name="1812" href="Maps.html#10221" class="Module"
      >PartialMap</a
      ><a name="1822" class="Symbol"
      >)</a
      ><a name="1823"
      >
</a
      ><a name="1824" class="Keyword"
      >open</a
      ><a name="1828"
      > </a
      ><a name="1829" href="Maps.html#10221" class="Module"
      >PartialMap</a
      ><a name="1839"
      > </a
      ><a name="1840" class="Keyword"
      >using</a
      ><a name="1845"
      > </a
      ><a name="1846" class="Symbol"
      >(</a
      ><a name="1847" href="Maps.html#10265" class="Function"
      >&#8709;</a
      ><a name="1848" class="Symbol"
      >;</a
      ><a name="1849"
      > </a
      ><a name="1850" href="Maps.html#11919" class="Function"
      >just-injective</a
      ><a name="1864" class="Symbol"
      >)</a
      ><a name="1865"
      > </a
      ><a name="1866" class="Keyword"
      >renaming</a
      ><a name="1874"
      > </a
      ><a name="1875" class="Symbol"
      >(</a
      ><a name="1876" href="Maps.html#10368" class="Function Operator"
      >_,_&#8614;_</a
      ><a name="1881"
      > </a
      ><a name="1882" class="Symbol"
      >to</a
      ><a name="1884"
      > </a
      ><a name="1885" href="Maps.html#10368" class="Function Operator"
      >_,_&#8758;_</a
      ><a name="1890" class="Symbol"
      >)</a
      ><a name="1891"
      >
</a
      ><a name="1892" class="Keyword"
      >open</a
      ><a name="1896"
      > </a
      ><a name="1897" class="Keyword"
      >import</a
      ><a name="1903"
      > </a
      ><a name="1904" href="https://agda.github.io/agda-stdlib/Data.Nat.html#1" class="Module"
      >Data.Nat</a
      ><a name="1912"
      > </a
      ><a name="1913" class="Keyword"
      >using</a
      ><a name="1918"
      > </a
      ><a name="1919" class="Symbol"
      >(</a
      ><a name="1920" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#97" class="Datatype"
      >&#8469;</a
      ><a name="1921" class="Symbol"
      >)</a
      ><a name="1922"
      >
</a
      ><a name="1923" class="Keyword"
      >open</a
      ><a name="1927"
      > </a
      ><a name="1928" class="Keyword"
      >import</a
      ><a name="1934"
      > </a
      ><a name="1935" href="https://agda.github.io/agda-stdlib/Data.Maybe.html#1" class="Module"
      >Data.Maybe</a
      ><a name="1945"
      > </a
      ><a name="1946" class="Keyword"
      >using</a
      ><a name="1951"
      > </a
      ><a name="1952" class="Symbol"
      >(</a
      ><a name="1953" href="https://agda.github.io/agda-stdlib/Data.Maybe.Base.html#335" class="Datatype"
      >Maybe</a
      ><a name="1958" class="Symbol"
      >;</a
      ><a name="1959"
      > </a
      ><a name="1960" href="https://agda.github.io/agda-stdlib/Data.Maybe.html#1527" class="InductiveConstructor"
      >just</a
      ><a name="1964" class="Symbol"
      >;</a
      ><a name="1965"
      > </a
      ><a name="1966" href="https://agda.github.io/agda-stdlib/Data.Maybe.html#1588" class="InductiveConstructor"
      >nothing</a
      ><a name="1973" class="Symbol"
      >)</a
      ><a name="1974"
      >
</a
      ><a name="1975" class="Keyword"
      >open</a
      ><a name="1979"
      > </a
      ><a name="1980" class="Keyword"
      >import</a
      ><a name="1986"
      > </a
      ><a name="1987" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#1" class="Module"
      >Relation.Nullary</a
      ><a name="2003"
      > </a
      ><a name="2004" class="Keyword"
      >using</a
      ><a name="2009"
      > </a
      ><a name="2010" class="Symbol"
      >(</a
      ><a name="2011" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#484" class="Datatype"
      >Dec</a
      ><a name="2014" class="Symbol"
      >;</a
      ><a name="2015"
      > </a
      ><a name="2016" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#520" class="InductiveConstructor"
      >yes</a
      ><a name="2019" class="Symbol"
      >;</a
      ><a name="2020"
      > </a
      ><a name="2021" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#547" class="InductiveConstructor"
      >no</a
      ><a name="2023" class="Symbol"
      >;</a
      ><a name="2024"
      > </a
      ><a name="2025" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#414" class="Function Operator"
      >&#172;_</a
      ><a name="2027" class="Symbol"
      >)</a
      ><a name="2028"
      >
</a
      ><a name="2029" class="Keyword"
      >open</a
      ><a name="2033"
      > </a
      ><a name="2034" class="Keyword"
      >import</a
      ><a name="2040"
      > </a
      ><a name="2041" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#1" class="Module"
      >Relation.Binary.PropositionalEquality</a
      ><a name="2078"
      > </a
      ><a name="2079" class="Keyword"
      >using</a
      ><a name="2084"
      > </a
      ><a name="2085" class="Symbol"
      >(</a
      ><a name="2086" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >_&#8801;_</a
      ><a name="2089" class="Symbol"
      >;</a
      ><a name="2090"
      > </a
      ><a name="2091" href="https://agda.github.io/agda-stdlib/Relation.Binary.Core.html#4493" class="Function Operator"
      >_&#8802;_</a
      ><a name="2094" class="Symbol"
      >;</a
      ><a name="2095"
      > </a
      ><a name="2096" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="2100" class="Symbol"
      >)</a
      >
{% endraw %}</pre>

## Syntax

We have just two types.

  * Functions, `A ⇒ B`
  * Booleans, `𝔹`

We require some form of base type, because otherwise the set of types
would be empty. Church used a trivial base type `o` with no operations.
For us, it is more convenient to use booleans. Later we will consider
numbers as a base type.

Here is the syntax of types in BNF.

    A, B, C  ::=  A ⇒ B | 𝔹

And here it is formalised in Agda.

<pre class="Agda">{% raw %}
<a name="2544" class="Keyword"
      >infixr</a
      ><a name="2550"
      > </a
      ><a name="2551" class="Number"
      >20</a
      ><a name="2553"
      > </a
      ><a name="2554" href="Stlc.html#2583" class="InductiveConstructor Operator"
      >_&#8658;_</a
      ><a name="2557"
      >

</a
      ><a name="2559" class="Keyword"
      >data</a
      ><a name="2563"
      > </a
      ><a name="2564" href="Stlc.html#2564" class="Datatype"
      >Type</a
      ><a name="2568"
      > </a
      ><a name="2569" class="Symbol"
      >:</a
      ><a name="2570"
      > </a
      ><a name="2571" class="PrimitiveType"
      >Set</a
      ><a name="2574"
      > </a
      ><a name="2575" class="Keyword"
      >where</a
      ><a name="2580"
      >
  </a
      ><a name="2583" href="Stlc.html#2583" class="InductiveConstructor Operator"
      >_&#8658;_</a
      ><a name="2586"
      > </a
      ><a name="2587" class="Symbol"
      >:</a
      ><a name="2588"
      > </a
      ><a name="2589" href="Stlc.html#2564" class="Datatype"
      >Type</a
      ><a name="2593"
      > </a
      ><a name="2594" class="Symbol"
      >&#8594;</a
      ><a name="2595"
      > </a
      ><a name="2596" href="Stlc.html#2564" class="Datatype"
      >Type</a
      ><a name="2600"
      > </a
      ><a name="2601" class="Symbol"
      >&#8594;</a
      ><a name="2602"
      > </a
      ><a name="2603" href="Stlc.html#2564" class="Datatype"
      >Type</a
      ><a name="2607"
      >
  </a
      ><a name="2610" href="Stlc.html#2610" class="InductiveConstructor"
      >&#120121;</a
      ><a name="2611"
      > </a
      ><a name="2612" class="Symbol"
      >:</a
      ><a name="2613"
      > </a
      ><a name="2614" href="Stlc.html#2564" class="Datatype"
      >Type</a
      >
{% endraw %}</pre>

Terms have six constructs. Three are for the core lambda calculus:

  * Variables, `` ` x ``
  * Abstractions, `λ[ x ∶ A ] N`
  * Applications, `L · M`

and three are for the base type, booleans:

  * True, `true`
  * False, `false`
  * Conditions, `if L then M else N`

Abstraction is also called lambda abstraction, and is the construct
from which the calculus takes its name. 

With the exception of variables, each term form either constructs
a value of a given type (abstractions yield functions, true and
false yield booleans) or deconstructs it (applications use functions,
conditionals use booleans). We will see this again when we come
to the rules for assigning types to terms, where constructors
correspond to introduction rules and deconstructors to eliminators.

Here is the syntax of terms in BNF.

    L, M, N  ::=  ` x | λ[ x ∶ A ] N | L · M | true | false | if L then M else N

And here it is formalised in Agda.

<pre class="Agda">{% raw %}
<a name="3575" class="Keyword"
      >infixl</a
      ><a name="3581"
      > </a
      ><a name="3582" class="Number"
      >20</a
      ><a name="3584"
      > </a
      ><a name="3585" href="Stlc.html#3708" class="InductiveConstructor Operator"
      >_&#183;_</a
      ><a name="3588"
      >
</a
      ><a name="3589" class="Keyword"
      >infix</a
      ><a name="3594"
      >  </a
      ><a name="3596" class="Number"
      >15</a
      ><a name="3598"
      > </a
      ><a name="3599" href="Stlc.html#3672" class="InductiveConstructor Operator"
      >&#955;[_&#8758;_]_</a
      ><a name="3606"
      >
</a
      ><a name="3607" class="Keyword"
      >infix</a
      ><a name="3612"
      >  </a
      ><a name="3614" class="Number"
      >15</a
      ><a name="3616"
      > </a
      ><a name="3617" href="Stlc.html#3764" class="InductiveConstructor Operator"
      >if_then_else_</a
      ><a name="3630"
      >

</a
      ><a name="3632" class="Keyword"
      >data</a
      ><a name="3636"
      > </a
      ><a name="3637" href="Stlc.html#3637" class="Datatype"
      >Term</a
      ><a name="3641"
      > </a
      ><a name="3642" class="Symbol"
      >:</a
      ><a name="3643"
      > </a
      ><a name="3644" class="PrimitiveType"
      >Set</a
      ><a name="3647"
      > </a
      ><a name="3648" class="Keyword"
      >where</a
      ><a name="3653"
      >
  </a
      ><a name="3656" href="Stlc.html#3656" class="InductiveConstructor"
      >`</a
      ><a name="3657"
      > </a
      ><a name="3658" class="Symbol"
      >:</a
      ><a name="3659"
      > </a
      ><a name="3660" href="Maps.html#2171" class="Datatype"
      >Id</a
      ><a name="3662"
      > </a
      ><a name="3663" class="Symbol"
      >&#8594;</a
      ><a name="3664"
      > </a
      ><a name="3665" href="Stlc.html#3637" class="Datatype"
      >Term</a
      ><a name="3669"
      >
  </a
      ><a name="3672" href="Stlc.html#3672" class="InductiveConstructor Operator"
      >&#955;[_&#8758;_]_</a
      ><a name="3679"
      > </a
      ><a name="3680" class="Symbol"
      >:</a
      ><a name="3681"
      > </a
      ><a name="3682" href="Maps.html#2171" class="Datatype"
      >Id</a
      ><a name="3684"
      > </a
      ><a name="3685" class="Symbol"
      >&#8594;</a
      ><a name="3686"
      > </a
      ><a name="3687" href="Stlc.html#2564" class="Datatype"
      >Type</a
      ><a name="3691"
      > </a
      ><a name="3692" class="Symbol"
      >&#8594;</a
      ><a name="3693"
      > </a
      ><a name="3694" href="Stlc.html#3637" class="Datatype"
      >Term</a
      ><a name="3698"
      > </a
      ><a name="3699" class="Symbol"
      >&#8594;</a
      ><a name="3700"
      > </a
      ><a name="3701" href="Stlc.html#3637" class="Datatype"
      >Term</a
      ><a name="3705"
      >
  </a
      ><a name="3708" href="Stlc.html#3708" class="InductiveConstructor Operator"
      >_&#183;_</a
      ><a name="3711"
      > </a
      ><a name="3712" class="Symbol"
      >:</a
      ><a name="3713"
      > </a
      ><a name="3714" href="Stlc.html#3637" class="Datatype"
      >Term</a
      ><a name="3718"
      > </a
      ><a name="3719" class="Symbol"
      >&#8594;</a
      ><a name="3720"
      > </a
      ><a name="3721" href="Stlc.html#3637" class="Datatype"
      >Term</a
      ><a name="3725"
      > </a
      ><a name="3726" class="Symbol"
      >&#8594;</a
      ><a name="3727"
      > </a
      ><a name="3728" href="Stlc.html#3637" class="Datatype"
      >Term</a
      ><a name="3732"
      >
  </a
      ><a name="3735" href="Stlc.html#3735" class="InductiveConstructor"
      >true</a
      ><a name="3739"
      > </a
      ><a name="3740" class="Symbol"
      >:</a
      ><a name="3741"
      > </a
      ><a name="3742" href="Stlc.html#3637" class="Datatype"
      >Term</a
      ><a name="3746"
      >
  </a
      ><a name="3749" href="Stlc.html#3749" class="InductiveConstructor"
      >false</a
      ><a name="3754"
      > </a
      ><a name="3755" class="Symbol"
      >:</a
      ><a name="3756"
      > </a
      ><a name="3757" href="Stlc.html#3637" class="Datatype"
      >Term</a
      ><a name="3761"
      >
  </a
      ><a name="3764" href="Stlc.html#3764" class="InductiveConstructor Operator"
      >if_then_else_</a
      ><a name="3777"
      > </a
      ><a name="3778" class="Symbol"
      >:</a
      ><a name="3779"
      > </a
      ><a name="3780" href="Stlc.html#3637" class="Datatype"
      >Term</a
      ><a name="3784"
      > </a
      ><a name="3785" class="Symbol"
      >&#8594;</a
      ><a name="3786"
      > </a
      ><a name="3787" href="Stlc.html#3637" class="Datatype"
      >Term</a
      ><a name="3791"
      > </a
      ><a name="3792" class="Symbol"
      >&#8594;</a
      ><a name="3793"
      > </a
      ><a name="3794" href="Stlc.html#3637" class="Datatype"
      >Term</a
      ><a name="3798"
      > </a
      ><a name="3799" class="Symbol"
      >&#8594;</a
      ><a name="3800"
      > </a
      ><a name="3801" href="Stlc.html#3637" class="Datatype"
      >Term</a
      >
{% endraw %}</pre>

#### Special characters

We use the following special characters

    ⇒  U+21D2: RIGHTWARDS DOUBLE ARROW (\=>)
    `  U+0060: GRAVE ACCENT 
    λ  U+03BB:  GREEK SMALL LETTER LAMBDA (\Gl or \lambda)
    ∶  U+2236:  RATIO (\:)
    ·  U+00B7: MIDDLE DOT (\cdot)

Note that ∶ (U+2236 RATIO) is not the same as : (U+003A COLON).
Colon is reserved in Agda for declaring types. Everywhere that we
declare a type in the object language rather than Agda we use
ratio in place of colon.

Using ratio for this purpose is arguably a bad idea, because one must use context
rather than appearance to distinguish it from colon. Arguably, it might be
better to use a different symbol, such as `∈` or `::`.  We reserve `∈`
for use later to indicate that a variable appears free in a term, and
eschew `::` because we consider it too ugly.


#### Formal vs informal

In informal presentation of formal semantics, one uses choice of
variable name to disambiguate and writes `x` rather than `` ` x ``
for a term that is a variable. Agda requires we distinguish.
Often researchers use `var x` rather than `` ` x ``, but we chose
the latter since it is closer to the informal notation `x`.

Similarly, informal presentation often use the notations `A → B` for
functions, `λ x . N` for abstractions, and `L M` for applications.  We
cannot use these, because they overlap with the notation used by Agda.
In `λ[ x ∶ A ] N`, recall that Agda treats square brackets `[]` as
ordinary symbols, while round parentheses `()` and curly braces `{}`
have special meaning.  We would use `L @ M` for application, but
`@` has a reserved meaning in Agda.


#### Examples

Here are a couple of example terms, `not` of type
`𝔹 ⇒ 𝔹`, which complements its argument, and `two` of type
`(𝔹 ⇒ 𝔹) ⇒ 𝔹 ⇒ 𝔹` which takes a function and a boolean
and applies the function to the boolean twice.

<pre class="Agda">{% raw %}
<a name="5677" href="Stlc.html#5677" class="Function"
      >f</a
      ><a name="5678"
      > </a
      ><a name="5679" href="Stlc.html#5679" class="Function"
      >x</a
      ><a name="5680"
      > </a
      ><a name="5681" href="Stlc.html#5681" class="Function"
      >y</a
      ><a name="5682"
      > </a
      ><a name="5683" class="Symbol"
      >:</a
      ><a name="5684"
      > </a
      ><a name="5685" href="Maps.html#2171" class="Datatype"
      >Id</a
      ><a name="5687"
      >
</a
      ><a name="5688" href="Stlc.html#5677" class="Function"
      >f</a
      ><a name="5689"
      >  </a
      ><a name="5691" class="Symbol"
      >=</a
      ><a name="5692"
      >  </a
      ><a name="5694" href="Maps.html#2188" class="InductiveConstructor"
      >id</a
      ><a name="5696"
      > </a
      ><a name="5697" class="Number"
      >0</a
      ><a name="5698"
      >
</a
      ><a name="5699" href="Stlc.html#5679" class="Function"
      >x</a
      ><a name="5700"
      >  </a
      ><a name="5702" class="Symbol"
      >=</a
      ><a name="5703"
      >  </a
      ><a name="5705" href="Maps.html#2188" class="InductiveConstructor"
      >id</a
      ><a name="5707"
      > </a
      ><a name="5708" class="Number"
      >1</a
      ><a name="5709"
      >
</a
      ><a name="5710" href="Stlc.html#5681" class="Function"
      >y</a
      ><a name="5711"
      >  </a
      ><a name="5713" class="Symbol"
      >=</a
      ><a name="5714"
      >  </a
      ><a name="5716" href="Maps.html#2188" class="InductiveConstructor"
      >id</a
      ><a name="5718"
      > </a
      ><a name="5719" class="Number"
      >2</a
      ><a name="5720"
      >

</a
      ><a name="5722" href="Stlc.html#5722" class="Function"
      >not</a
      ><a name="5725"
      > </a
      ><a name="5726" href="Stlc.html#5726" class="Function"
      >two</a
      ><a name="5729"
      > </a
      ><a name="5730" class="Symbol"
      >:</a
      ><a name="5731"
      > </a
      ><a name="5732" href="Stlc.html#3637" class="Datatype"
      >Term</a
      ><a name="5736"
      > 
</a
      ><a name="5738" href="Stlc.html#5722" class="Function"
      >not</a
      ><a name="5741"
      > </a
      ><a name="5742" class="Symbol"
      >=</a
      ><a name="5743"
      >  </a
      ><a name="5745" href="Stlc.html#3672" class="InductiveConstructor Operator"
      >&#955;[</a
      ><a name="5747"
      > </a
      ><a name="5748" href="Stlc.html#5679" class="Function"
      >x</a
      ><a name="5749"
      > </a
      ><a name="5750" href="Stlc.html#3672" class="InductiveConstructor Operator"
      >&#8758;</a
      ><a name="5751"
      > </a
      ><a name="5752" href="Stlc.html#2610" class="InductiveConstructor"
      >&#120121;</a
      ><a name="5753"
      > </a
      ><a name="5754" href="Stlc.html#3672" class="InductiveConstructor Operator"
      >]</a
      ><a name="5755"
      > </a
      ><a name="5756" class="Symbol"
      >(</a
      ><a name="5757" href="Stlc.html#3764" class="InductiveConstructor Operator"
      >if</a
      ><a name="5759"
      > </a
      ><a name="5760" href="Stlc.html#3656" class="InductiveConstructor"
      >`</a
      ><a name="5761"
      > </a
      ><a name="5762" href="Stlc.html#5679" class="Function"
      >x</a
      ><a name="5763"
      > </a
      ><a name="5764" href="Stlc.html#3764" class="InductiveConstructor Operator"
      >then</a
      ><a name="5768"
      > </a
      ><a name="5769" href="Stlc.html#3749" class="InductiveConstructor"
      >false</a
      ><a name="5774"
      > </a
      ><a name="5775" href="Stlc.html#3764" class="InductiveConstructor Operator"
      >else</a
      ><a name="5779"
      > </a
      ><a name="5780" href="Stlc.html#3735" class="InductiveConstructor"
      >true</a
      ><a name="5784" class="Symbol"
      >)</a
      ><a name="5785"
      >
</a
      ><a name="5786" href="Stlc.html#5726" class="Function"
      >two</a
      ><a name="5789"
      > </a
      ><a name="5790" class="Symbol"
      >=</a
      ><a name="5791"
      >  </a
      ><a name="5793" href="Stlc.html#3672" class="InductiveConstructor Operator"
      >&#955;[</a
      ><a name="5795"
      > </a
      ><a name="5796" href="Stlc.html#5677" class="Function"
      >f</a
      ><a name="5797"
      > </a
      ><a name="5798" href="Stlc.html#3672" class="InductiveConstructor Operator"
      >&#8758;</a
      ><a name="5799"
      > </a
      ><a name="5800" href="Stlc.html#2610" class="InductiveConstructor"
      >&#120121;</a
      ><a name="5801"
      > </a
      ><a name="5802" href="Stlc.html#2583" class="InductiveConstructor Operator"
      >&#8658;</a
      ><a name="5803"
      > </a
      ><a name="5804" href="Stlc.html#2610" class="InductiveConstructor"
      >&#120121;</a
      ><a name="5805"
      > </a
      ><a name="5806" href="Stlc.html#3672" class="InductiveConstructor Operator"
      >]</a
      ><a name="5807"
      > </a
      ><a name="5808" href="Stlc.html#3672" class="InductiveConstructor Operator"
      >&#955;[</a
      ><a name="5810"
      > </a
      ><a name="5811" href="Stlc.html#5679" class="Function"
      >x</a
      ><a name="5812"
      > </a
      ><a name="5813" href="Stlc.html#3672" class="InductiveConstructor Operator"
      >&#8758;</a
      ><a name="5814"
      > </a
      ><a name="5815" href="Stlc.html#2610" class="InductiveConstructor"
      >&#120121;</a
      ><a name="5816"
      > </a
      ><a name="5817" href="Stlc.html#3672" class="InductiveConstructor Operator"
      >]</a
      ><a name="5818"
      > </a
      ><a name="5819" href="Stlc.html#3656" class="InductiveConstructor"
      >`</a
      ><a name="5820"
      > </a
      ><a name="5821" href="Stlc.html#5677" class="Function"
      >f</a
      ><a name="5822"
      > </a
      ><a name="5823" href="Stlc.html#3708" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="5824"
      > </a
      ><a name="5825" class="Symbol"
      >(</a
      ><a name="5826" href="Stlc.html#3656" class="InductiveConstructor"
      >`</a
      ><a name="5827"
      > </a
      ><a name="5828" href="Stlc.html#5677" class="Function"
      >f</a
      ><a name="5829"
      > </a
      ><a name="5830" href="Stlc.html#3708" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="5831"
      > </a
      ><a name="5832" href="Stlc.html#3656" class="InductiveConstructor"
      >`</a
      ><a name="5833"
      > </a
      ><a name="5834" href="Stlc.html#5679" class="Function"
      >x</a
      ><a name="5835" class="Symbol"
      >)</a
      >
{% endraw %}</pre>


#### Bound and free variables

In an abstraction `λ[ x ∶ A ] N` we call `x` the _bound_ variable
and `N` the _body_ of the abstraction.  One of the most important
aspects of lambda calculus is that names of bound variables are
irrelevant.  Thus the five terms

* `` λ[ f ∶ 𝔹 ⇒ 𝔹 ] λ[ x ∶ 𝔹 ] ` f · (` f · ` x) ``
* `` λ[ g ∶ 𝔹 ⇒ 𝔹 ] λ[ y ∶ 𝔹 ] ` g · (` g · ` y) ``
* `` λ[ fred ∶ 𝔹 ⇒ 𝔹 ] λ[ xander ∶ 𝔹 ] ` fred · (` fred · ` xander) ``
* `` λ[ 👿 ∶ 𝔹 ⇒ 𝔹 ] λ[ 😄 ∶ 𝔹 ] ` 👿 · (` 👿 · ` 😄) ``  
* `` λ[ x ∶ 𝔹 ⇒ 𝔹 ] λ[ f ∶ 𝔹 ] ` x · (` x · ` f) ``

are all considered equivalent.  This equivalence relation
is sometimes called _alpha renaming_.

As we descend from a term into its subterms, variables
that are bound may become free.  Consider the following terms.

* `` λ[ f ∶ 𝔹 ⇒ 𝔹 ] λ[ x ∶ 𝔹 ] ` f · (` f · ` x) ``
  Both variable `f` and `x` are bound.

* `` λ[ x ∶ 𝔹 ] ` f · (` f · ` x) ``
  has `x` as a bound variable but `f` as a free variable.  

* `` ` f · (` f · ` x) ``
  has both `f` and `x` as free variables.

We say that a term with no free variables is _closed_; otherwise it is
_open_.  Of the three terms above, the first is closed and the other
two are open.  A formal definition of bound and free variables will be
given in the next chapter.

Different occurrences of a variable may be bound and free.
In the term 

    (λ[ x ∶ 𝔹 ] ` x) · ` x

the inner occurrence of `x` is bound while the outer occurrence is free.
Note that by alpha renaming, the term above is equivalent to

    (λ[ y ∶ 𝔹 ] ` y) · ` x

in which `y` is bound and `x` is free.  A common convention, called the
Barendregt convention, is to use alpha renaming to ensure that the bound
variables in a term are distinct from the free variables, which can
avoid confusions that may arise if bound and free variables have the
same names.


#### Precedence

As in Agda, functions of two or more arguments are represented via
currying. This is made more convenient by declaring `_⇒_` to
associate to the right and `_·_` to associate to the left.
Thus,

* `(𝔹 ⇒ 𝔹) ⇒ 𝔹 ⇒ 𝔹` abbreviates `(𝔹 ⇒ 𝔹) ⇒ (𝔹 ⇒ 𝔹)`
* `two · not · true` abbreviates `(two · not) · true`.

We choose the binding strength for abstractions and conditionals
to be weaker than application. For instance,

* `` λ[ f ∶ 𝔹 ⇒ 𝔹 ] λ[ x ∶ 𝔹 ] ` f · (` f · ` x) ``
  - abbreviates `` (λ[ f ∶ 𝔹 ⇒ 𝔹 ] (λ[ x ∶ 𝔹 ] (` f · (` f · ` x)))) ``
  - and not `` (λ[ f ∶ 𝔹 ⇒ 𝔹 ] (λ[ x ∶ 𝔹 ] ` f)) · (` f · ` x) ``.

<pre class="Agda">{% raw %}
<a name="8302" href="Stlc.html#8302" class="Function"
      >ex&#8321;</a
      ><a name="8305"
      > </a
      ><a name="8306" class="Symbol"
      >:</a
      ><a name="8307"
      > </a
      ><a name="8308" class="Symbol"
      >(</a
      ><a name="8309" href="Stlc.html#2610" class="InductiveConstructor"
      >&#120121;</a
      ><a name="8310"
      > </a
      ><a name="8311" href="Stlc.html#2583" class="InductiveConstructor Operator"
      >&#8658;</a
      ><a name="8312"
      > </a
      ><a name="8313" href="Stlc.html#2610" class="InductiveConstructor"
      >&#120121;</a
      ><a name="8314" class="Symbol"
      >)</a
      ><a name="8315"
      > </a
      ><a name="8316" href="Stlc.html#2583" class="InductiveConstructor Operator"
      >&#8658;</a
      ><a name="8317"
      > </a
      ><a name="8318" href="Stlc.html#2610" class="InductiveConstructor"
      >&#120121;</a
      ><a name="8319"
      > </a
      ><a name="8320" href="Stlc.html#2583" class="InductiveConstructor Operator"
      >&#8658;</a
      ><a name="8321"
      > </a
      ><a name="8322" href="Stlc.html#2610" class="InductiveConstructor"
      >&#120121;</a
      ><a name="8323"
      > </a
      ><a name="8324" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="8325"
      > </a
      ><a name="8326" class="Symbol"
      >(</a
      ><a name="8327" href="Stlc.html#2610" class="InductiveConstructor"
      >&#120121;</a
      ><a name="8328"
      > </a
      ><a name="8329" href="Stlc.html#2583" class="InductiveConstructor Operator"
      >&#8658;</a
      ><a name="8330"
      > </a
      ><a name="8331" href="Stlc.html#2610" class="InductiveConstructor"
      >&#120121;</a
      ><a name="8332" class="Symbol"
      >)</a
      ><a name="8333"
      > </a
      ><a name="8334" href="Stlc.html#2583" class="InductiveConstructor Operator"
      >&#8658;</a
      ><a name="8335"
      > </a
      ><a name="8336" class="Symbol"
      >(</a
      ><a name="8337" href="Stlc.html#2610" class="InductiveConstructor"
      >&#120121;</a
      ><a name="8338"
      > </a
      ><a name="8339" href="Stlc.html#2583" class="InductiveConstructor Operator"
      >&#8658;</a
      ><a name="8340"
      > </a
      ><a name="8341" href="Stlc.html#2610" class="InductiveConstructor"
      >&#120121;</a
      ><a name="8342" class="Symbol"
      >)</a
      ><a name="8343"
      >
</a
      ><a name="8344" href="Stlc.html#8302" class="Function"
      >ex&#8321;</a
      ><a name="8347"
      > </a
      ><a name="8348" class="Symbol"
      >=</a
      ><a name="8349"
      > </a
      ><a name="8350" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="8354"
      >

</a
      ><a name="8356" href="Stlc.html#8356" class="Function"
      >ex&#8322;</a
      ><a name="8359"
      > </a
      ><a name="8360" class="Symbol"
      >:</a
      ><a name="8361"
      > </a
      ><a name="8362" href="Stlc.html#5726" class="Function"
      >two</a
      ><a name="8365"
      > </a
      ><a name="8366" href="Stlc.html#3708" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="8367"
      > </a
      ><a name="8368" href="Stlc.html#5722" class="Function"
      >not</a
      ><a name="8371"
      > </a
      ><a name="8372" href="Stlc.html#3708" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="8373"
      > </a
      ><a name="8374" href="Stlc.html#3735" class="InductiveConstructor"
      >true</a
      ><a name="8378"
      > </a
      ><a name="8379" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="8380"
      > </a
      ><a name="8381" class="Symbol"
      >(</a
      ><a name="8382" href="Stlc.html#5726" class="Function"
      >two</a
      ><a name="8385"
      > </a
      ><a name="8386" href="Stlc.html#3708" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="8387"
      > </a
      ><a name="8388" href="Stlc.html#5722" class="Function"
      >not</a
      ><a name="8391" class="Symbol"
      >)</a
      ><a name="8392"
      > </a
      ><a name="8393" href="Stlc.html#3708" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="8394"
      > </a
      ><a name="8395" href="Stlc.html#3735" class="InductiveConstructor"
      >true</a
      ><a name="8399"
      >
</a
      ><a name="8400" href="Stlc.html#8356" class="Function"
      >ex&#8322;</a
      ><a name="8403"
      > </a
      ><a name="8404" class="Symbol"
      >=</a
      ><a name="8405"
      > </a
      ><a name="8406" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="8410"
      >

</a
      ><a name="8412" href="Stlc.html#8412" class="Function"
      >ex&#8323;</a
      ><a name="8415"
      > </a
      ><a name="8416" class="Symbol"
      >:</a
      ><a name="8417"
      > </a
      ><a name="8418" href="Stlc.html#3672" class="InductiveConstructor Operator"
      >&#955;[</a
      ><a name="8420"
      > </a
      ><a name="8421" href="Stlc.html#5677" class="Function"
      >f</a
      ><a name="8422"
      > </a
      ><a name="8423" href="Stlc.html#3672" class="InductiveConstructor Operator"
      >&#8758;</a
      ><a name="8424"
      > </a
      ><a name="8425" href="Stlc.html#2610" class="InductiveConstructor"
      >&#120121;</a
      ><a name="8426"
      > </a
      ><a name="8427" href="Stlc.html#2583" class="InductiveConstructor Operator"
      >&#8658;</a
      ><a name="8428"
      > </a
      ><a name="8429" href="Stlc.html#2610" class="InductiveConstructor"
      >&#120121;</a
      ><a name="8430"
      > </a
      ><a name="8431" href="Stlc.html#3672" class="InductiveConstructor Operator"
      >]</a
      ><a name="8432"
      > </a
      ><a name="8433" href="Stlc.html#3672" class="InductiveConstructor Operator"
      >&#955;[</a
      ><a name="8435"
      > </a
      ><a name="8436" href="Stlc.html#5679" class="Function"
      >x</a
      ><a name="8437"
      > </a
      ><a name="8438" href="Stlc.html#3672" class="InductiveConstructor Operator"
      >&#8758;</a
      ><a name="8439"
      > </a
      ><a name="8440" href="Stlc.html#2610" class="InductiveConstructor"
      >&#120121;</a
      ><a name="8441"
      > </a
      ><a name="8442" href="Stlc.html#3672" class="InductiveConstructor Operator"
      >]</a
      ><a name="8443"
      > </a
      ><a name="8444" href="Stlc.html#3656" class="InductiveConstructor"
      >`</a
      ><a name="8445"
      > </a
      ><a name="8446" href="Stlc.html#5677" class="Function"
      >f</a
      ><a name="8447"
      > </a
      ><a name="8448" href="Stlc.html#3708" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="8449"
      > </a
      ><a name="8450" class="Symbol"
      >(</a
      ><a name="8451" href="Stlc.html#3656" class="InductiveConstructor"
      >`</a
      ><a name="8452"
      > </a
      ><a name="8453" href="Stlc.html#5677" class="Function"
      >f</a
      ><a name="8454"
      > </a
      ><a name="8455" href="Stlc.html#3708" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="8456"
      > </a
      ><a name="8457" href="Stlc.html#3656" class="InductiveConstructor"
      >`</a
      ><a name="8458"
      > </a
      ><a name="8459" href="Stlc.html#5679" class="Function"
      >x</a
      ><a name="8460" class="Symbol"
      >)</a
      ><a name="8461"
      >
      </a
      ><a name="8468" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="8469"
      > </a
      ><a name="8470" class="Symbol"
      >(</a
      ><a name="8471" href="Stlc.html#3672" class="InductiveConstructor Operator"
      >&#955;[</a
      ><a name="8473"
      > </a
      ><a name="8474" href="Stlc.html#5677" class="Function"
      >f</a
      ><a name="8475"
      > </a
      ><a name="8476" href="Stlc.html#3672" class="InductiveConstructor Operator"
      >&#8758;</a
      ><a name="8477"
      > </a
      ><a name="8478" href="Stlc.html#2610" class="InductiveConstructor"
      >&#120121;</a
      ><a name="8479"
      > </a
      ><a name="8480" href="Stlc.html#2583" class="InductiveConstructor Operator"
      >&#8658;</a
      ><a name="8481"
      > </a
      ><a name="8482" href="Stlc.html#2610" class="InductiveConstructor"
      >&#120121;</a
      ><a name="8483"
      > </a
      ><a name="8484" href="Stlc.html#3672" class="InductiveConstructor Operator"
      >]</a
      ><a name="8485"
      > </a
      ><a name="8486" class="Symbol"
      >(</a
      ><a name="8487" href="Stlc.html#3672" class="InductiveConstructor Operator"
      >&#955;[</a
      ><a name="8489"
      > </a
      ><a name="8490" href="Stlc.html#5679" class="Function"
      >x</a
      ><a name="8491"
      > </a
      ><a name="8492" href="Stlc.html#3672" class="InductiveConstructor Operator"
      >&#8758;</a
      ><a name="8493"
      > </a
      ><a name="8494" href="Stlc.html#2610" class="InductiveConstructor"
      >&#120121;</a
      ><a name="8495"
      > </a
      ><a name="8496" href="Stlc.html#3672" class="InductiveConstructor Operator"
      >]</a
      ><a name="8497"
      > </a
      ><a name="8498" class="Symbol"
      >(</a
      ><a name="8499" href="Stlc.html#3656" class="InductiveConstructor"
      >`</a
      ><a name="8500"
      > </a
      ><a name="8501" href="Stlc.html#5677" class="Function"
      >f</a
      ><a name="8502"
      > </a
      ><a name="8503" href="Stlc.html#3708" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="8504"
      > </a
      ><a name="8505" class="Symbol"
      >(</a
      ><a name="8506" href="Stlc.html#3656" class="InductiveConstructor"
      >`</a
      ><a name="8507"
      > </a
      ><a name="8508" href="Stlc.html#5677" class="Function"
      >f</a
      ><a name="8509"
      > </a
      ><a name="8510" href="Stlc.html#3708" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="8511"
      > </a
      ><a name="8512" href="Stlc.html#3656" class="InductiveConstructor"
      >`</a
      ><a name="8513"
      > </a
      ><a name="8514" href="Stlc.html#5679" class="Function"
      >x</a
      ><a name="8515" class="Symbol"
      >))))</a
      ><a name="8519"
      >
</a
      ><a name="8520" href="Stlc.html#8412" class="Function"
      >ex&#8323;</a
      ><a name="8523"
      > </a
      ><a name="8524" class="Symbol"
      >=</a
      ><a name="8525"
      > </a
      ><a name="8526" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      >
{% endraw %}</pre>

#### Quiz

* What is the type of the following term?

    λ[ f ∶ 𝔹 ⇒ 𝔹 ] ` f · (` f  · true)

  1. `𝔹 ⇒ (𝔹 ⇒ 𝔹)`
  2. `(𝔹 ⇒ 𝔹) ⇒ 𝔹`
  3. `𝔹 ⇒ 𝔹 ⇒ 𝔹`
  4. `𝔹 ⇒ 𝔹`
  5. `𝔹`

  Give more than one answer if appropriate.

* What is the type of the following term?

    (λ[ f ∶ 𝔹 ⇒ 𝔹 ] ` f · (` f  · true)) · not

  1. `𝔹 ⇒ (𝔹 ⇒ 𝔹)`
  2. `(𝔹 ⇒ 𝔹) ⇒ 𝔹`
  3. `𝔹 ⇒ 𝔹 ⇒ 𝔹`
  4. `𝔹 ⇒ 𝔹`
  5. `𝔹`

  Give more than one answer if appropriate.

## Values

We only consider reduction of _closed_ terms,
those that contain no free variables.  We consider
a precise definition of free variables in
[StlcProp]({{ "StlcProp" | relative_url }}).

A term is a value if it is fully reduced.
For booleans, the situation is clear, `true` and
`false` are values, while conditionals are not.
For functions, applications are not values, because
we expect them to further reduce, and variables are
not values, because we focus on closed terms.
Following convention, we treat all abstractions
as values.

The predicate `Value M` holds if term `M` is a value.

<pre class="Agda">{% raw %}
<a name="9587" class="Keyword"
      >data</a
      ><a name="9591"
      > </a
      ><a name="9592" href="Stlc.html#9592" class="Datatype"
      >Value</a
      ><a name="9597"
      > </a
      ><a name="9598" class="Symbol"
      >:</a
      ><a name="9599"
      > </a
      ><a name="9600" href="Stlc.html#3637" class="Datatype"
      >Term</a
      ><a name="9604"
      > </a
      ><a name="9605" class="Symbol"
      >&#8594;</a
      ><a name="9606"
      > </a
      ><a name="9607" class="PrimitiveType"
      >Set</a
      ><a name="9610"
      > </a
      ><a name="9611" class="Keyword"
      >where</a
      ><a name="9616"
      >
  </a
      ><a name="9619" href="Stlc.html#9619" class="InductiveConstructor"
      >value-&#955;</a
      ><a name="9626"
      >     </a
      ><a name="9631" class="Symbol"
      >:</a
      ><a name="9632"
      > </a
      ><a name="9633" class="Symbol"
      >&#8704;</a
      ><a name="9634"
      > </a
      ><a name="9635" class="Symbol"
      >{</a
      ><a name="9636" href="Stlc.html#9636" class="Bound"
      >x</a
      ><a name="9637"
      > </a
      ><a name="9638" href="Stlc.html#9638" class="Bound"
      >A</a
      ><a name="9639"
      > </a
      ><a name="9640" href="Stlc.html#9640" class="Bound"
      >N</a
      ><a name="9641" class="Symbol"
      >}</a
      ><a name="9642"
      > </a
      ><a name="9643" class="Symbol"
      >&#8594;</a
      ><a name="9644"
      > </a
      ><a name="9645" href="Stlc.html#9592" class="Datatype"
      >Value</a
      ><a name="9650"
      > </a
      ><a name="9651" class="Symbol"
      >(</a
      ><a name="9652" href="Stlc.html#3672" class="InductiveConstructor Operator"
      >&#955;[</a
      ><a name="9654"
      > </a
      ><a name="9655" href="Stlc.html#9636" class="Bound"
      >x</a
      ><a name="9656"
      > </a
      ><a name="9657" href="Stlc.html#3672" class="InductiveConstructor Operator"
      >&#8758;</a
      ><a name="9658"
      > </a
      ><a name="9659" href="Stlc.html#9638" class="Bound"
      >A</a
      ><a name="9660"
      > </a
      ><a name="9661" href="Stlc.html#3672" class="InductiveConstructor Operator"
      >]</a
      ><a name="9662"
      > </a
      ><a name="9663" href="Stlc.html#9640" class="Bound"
      >N</a
      ><a name="9664" class="Symbol"
      >)</a
      ><a name="9665"
      >
  </a
      ><a name="9668" href="Stlc.html#9668" class="InductiveConstructor"
      >value-true</a
      ><a name="9678"
      >  </a
      ><a name="9680" class="Symbol"
      >:</a
      ><a name="9681"
      > </a
      ><a name="9682" href="Stlc.html#9592" class="Datatype"
      >Value</a
      ><a name="9687"
      > </a
      ><a name="9688" href="Stlc.html#3735" class="InductiveConstructor"
      >true</a
      ><a name="9692"
      >
  </a
      ><a name="9695" href="Stlc.html#9695" class="InductiveConstructor"
      >value-false</a
      ><a name="9706"
      > </a
      ><a name="9707" class="Symbol"
      >:</a
      ><a name="9708"
      > </a
      ><a name="9709" href="Stlc.html#9592" class="Datatype"
      >Value</a
      ><a name="9714"
      > </a
      ><a name="9715" href="Stlc.html#3749" class="InductiveConstructor"
      >false</a
      >
{% endraw %}</pre>

We let `V` and `W` range over values.


#### Formal vs informal

In informal presentations of formal semantics, using
`V` as the name of a metavariable is sufficient to
indicate that it is a value. In Agda, we must explicitly
invoke the `Value` predicate.

#### Other approaches

An alternative is not to focus on closed terms,
to treat variables as values, and to treat
`λ[ x ∶ A ] N` as a value only if `N` is a value.
Indeed, this is how Agda normalises terms.
Formalising this approach requires a more sophisticated
definition of substitution, which permits substituting
closed terms for values.

## Substitution

The heart of lambda calculus is the operation of
substituting one term for a variable in another term.
Substitution plays a key role in defining the
operational semantics of function application.
For instance, we have

      (λ[ f ∶ 𝔹 ⇒ 𝔹 ] `f · (`f · true)) · not
    ⟹
      not · (not · true)

where we substitute `false` for `` `x `` in the body
of the function abstraction.

We write substitution as `N [ x := V ]`, meaning
substitute term `V` for free occurrences of variable `x` in term `V`,
or, more compactly, substitute `V` for `x` in `N`.
Substitution works if `V` is any closed term;
it need not be a value, but we use `V` since we
always substitute values.

Here are some examples.

* `` ` f [ f := not ] `` yields `` not ``
* `` true [ f := not ] `` yields `` true ``
* `` (` f · true) [ f := not ] `` yields `` not · true ``
* `` (` f · (` f · true)) [ f := not ] `` yields `` not · (not · true) ``
* `` (λ[ x ∶ 𝔹 ] ` f · (` f · ` x)) [ f := not ] `` yields `` λ[ x ∶ 𝔹 ] not · (not · ` x) ``
* `` (λ[ y ∶ 𝔹 ] ` y) [ x := true ] `` yields `` λ[ y ∶ 𝔹 ] ` y ``
* `` (λ[ x ∶ 𝔹 ] ` x) [ x := true ] `` yields `` λ[ x ∶ 𝔹 ] ` x ``

The last example is important: substituting `true` for `x` in
`` (λ[ x ∶ 𝔹 ] ` x) `` does _not_ yield `` (λ[ x ∶ 𝔹 ] true) ``.
The reason for this is that `x` in the body of `` (λ[ x ∶ 𝔹 ] ` x) ``
is _bound_ by the abstraction.  An important feature of abstraction
is that the choice of bound names is irrelevant: both
`` (λ[ x ∶ 𝔹 ] ` x) `` and `` (λ[ y ∶ 𝔹 ] ` y) `` stand for the
identity function.  The way to think of this is that `x` within
the body of the abstraction stands for a _different_ variable than
`x` outside the abstraction, they both just happen to have the same
name.

Here is the formal definition in Agda.

<pre class="Agda">{% raw %}
<a name="12136" href="Stlc.html#12136" class="Function Operator"
      >_[_:=_]</a
      ><a name="12143"
      > </a
      ><a name="12144" class="Symbol"
      >:</a
      ><a name="12145"
      > </a
      ><a name="12146" href="Stlc.html#3637" class="Datatype"
      >Term</a
      ><a name="12150"
      > </a
      ><a name="12151" class="Symbol"
      >&#8594;</a
      ><a name="12152"
      > </a
      ><a name="12153" href="Maps.html#2171" class="Datatype"
      >Id</a
      ><a name="12155"
      > </a
      ><a name="12156" class="Symbol"
      >&#8594;</a
      ><a name="12157"
      > </a
      ><a name="12158" href="Stlc.html#3637" class="Datatype"
      >Term</a
      ><a name="12162"
      > </a
      ><a name="12163" class="Symbol"
      >&#8594;</a
      ><a name="12164"
      > </a
      ><a name="12165" href="Stlc.html#3637" class="Datatype"
      >Term</a
      ><a name="12169"
      >
</a
      ><a name="12170" class="Symbol"
      >(</a
      ><a name="12171" href="Stlc.html#3656" class="InductiveConstructor"
      >`</a
      ><a name="12172"
      > </a
      ><a name="12173" href="Stlc.html#12173" class="Bound"
      >x&#8242;</a
      ><a name="12175" class="Symbol"
      >)</a
      ><a name="12176"
      > </a
      ><a name="12177" href="Stlc.html#12136" class="Function Operator"
      >[</a
      ><a name="12178"
      > </a
      ><a name="12179" href="Stlc.html#12179" class="Bound"
      >x</a
      ><a name="12180"
      > </a
      ><a name="12181" href="Stlc.html#12136" class="Function Operator"
      >:=</a
      ><a name="12183"
      > </a
      ><a name="12184" href="Stlc.html#12184" class="Bound"
      >V</a
      ><a name="12185"
      > </a
      ><a name="12186" href="Stlc.html#12136" class="Function Operator"
      >]</a
      ><a name="12187"
      > </a
      ><a name="12188" class="Keyword"
      >with</a
      ><a name="12192"
      > </a
      ><a name="12193" href="Stlc.html#12179" class="Bound"
      >x</a
      ><a name="12194"
      > </a
      ><a name="12195" href="Maps.html#2509" class="Function Operator"
      >&#8799;</a
      ><a name="12196"
      > </a
      ><a name="12197" href="Stlc.html#12173" class="Bound"
      >x&#8242;</a
      ><a name="12199"
      >
</a
      ><a name="12200" class="Symbol"
      >...</a
      ><a name="12203"
      > </a
      ><a name="12204" class="Symbol"
      >|</a
      ><a name="12205"
      > </a
      ><a name="12206" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#520" class="InductiveConstructor"
      >yes</a
      ><a name="12209"
      > </a
      ><a name="12210" class="Symbol"
      >_</a
      ><a name="12211"
      > </a
      ><a name="12212" class="Symbol"
      >=</a
      ><a name="12213"
      > </a
      ><a name="12214" href="Stlc.html#12184" class="Bound"
      >V</a
      ><a name="12215"
      >
</a
      ><a name="12216" class="Symbol"
      >...</a
      ><a name="12219"
      > </a
      ><a name="12220" class="Symbol"
      >|</a
      ><a name="12221"
      > </a
      ><a name="12222" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#547" class="InductiveConstructor"
      >no</a
      ><a name="12224"
      >  </a
      ><a name="12226" class="Symbol"
      >_</a
      ><a name="12227"
      > </a
      ><a name="12228" class="Symbol"
      >=</a
      ><a name="12229"
      > </a
      ><a name="12230" href="Stlc.html#3656" class="InductiveConstructor"
      >`</a
      ><a name="12231"
      > </a
      ><a name="12232" href="Stlc.html#12173" class="Bound"
      >x&#8242;</a
      ><a name="12234"
      >
</a
      ><a name="12235" class="Symbol"
      >(</a
      ><a name="12236" href="Stlc.html#3672" class="InductiveConstructor Operator"
      >&#955;[</a
      ><a name="12238"
      > </a
      ><a name="12239" href="Stlc.html#12239" class="Bound"
      >x&#8242;</a
      ><a name="12241"
      > </a
      ><a name="12242" href="Stlc.html#3672" class="InductiveConstructor Operator"
      >&#8758;</a
      ><a name="12243"
      > </a
      ><a name="12244" href="Stlc.html#12244" class="Bound"
      >A&#8242;</a
      ><a name="12246"
      > </a
      ><a name="12247" href="Stlc.html#3672" class="InductiveConstructor Operator"
      >]</a
      ><a name="12248"
      > </a
      ><a name="12249" href="Stlc.html#12249" class="Bound"
      >N&#8242;</a
      ><a name="12251" class="Symbol"
      >)</a
      ><a name="12252"
      > </a
      ><a name="12253" href="Stlc.html#12136" class="Function Operator"
      >[</a
      ><a name="12254"
      > </a
      ><a name="12255" href="Stlc.html#12255" class="Bound"
      >x</a
      ><a name="12256"
      > </a
      ><a name="12257" href="Stlc.html#12136" class="Function Operator"
      >:=</a
      ><a name="12259"
      > </a
      ><a name="12260" href="Stlc.html#12260" class="Bound"
      >V</a
      ><a name="12261"
      > </a
      ><a name="12262" href="Stlc.html#12136" class="Function Operator"
      >]</a
      ><a name="12263"
      > </a
      ><a name="12264" class="Keyword"
      >with</a
      ><a name="12268"
      > </a
      ><a name="12269" href="Stlc.html#12255" class="Bound"
      >x</a
      ><a name="12270"
      > </a
      ><a name="12271" href="Maps.html#2509" class="Function Operator"
      >&#8799;</a
      ><a name="12272"
      > </a
      ><a name="12273" href="Stlc.html#12239" class="Bound"
      >x&#8242;</a
      ><a name="12275"
      >
</a
      ><a name="12276" class="Symbol"
      >...</a
      ><a name="12279"
      > </a
      ><a name="12280" class="Symbol"
      >|</a
      ><a name="12281"
      > </a
      ><a name="12282" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#520" class="InductiveConstructor"
      >yes</a
      ><a name="12285"
      > </a
      ><a name="12286" class="Symbol"
      >_</a
      ><a name="12287"
      > </a
      ><a name="12288" class="Symbol"
      >=</a
      ><a name="12289"
      > </a
      ><a name="12290" href="Stlc.html#3672" class="InductiveConstructor Operator"
      >&#955;[</a
      ><a name="12292"
      > </a
      ><a name="12293" href="Stlc.html#12239" class="Bound"
      >x&#8242;</a
      ><a name="12295"
      > </a
      ><a name="12296" href="Stlc.html#3672" class="InductiveConstructor Operator"
      >&#8758;</a
      ><a name="12297"
      > </a
      ><a name="12298" href="Stlc.html#12244" class="Bound"
      >A&#8242;</a
      ><a name="12300"
      > </a
      ><a name="12301" href="Stlc.html#3672" class="InductiveConstructor Operator"
      >]</a
      ><a name="12302"
      > </a
      ><a name="12303" href="Stlc.html#12249" class="Bound"
      >N&#8242;</a
      ><a name="12305"
      >
</a
      ><a name="12306" class="Symbol"
      >...</a
      ><a name="12309"
      > </a
      ><a name="12310" class="Symbol"
      >|</a
      ><a name="12311"
      > </a
      ><a name="12312" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#547" class="InductiveConstructor"
      >no</a
      ><a name="12314"
      >  </a
      ><a name="12316" class="Symbol"
      >_</a
      ><a name="12317"
      > </a
      ><a name="12318" class="Symbol"
      >=</a
      ><a name="12319"
      > </a
      ><a name="12320" href="Stlc.html#3672" class="InductiveConstructor Operator"
      >&#955;[</a
      ><a name="12322"
      > </a
      ><a name="12323" href="Stlc.html#12239" class="Bound"
      >x&#8242;</a
      ><a name="12325"
      > </a
      ><a name="12326" href="Stlc.html#3672" class="InductiveConstructor Operator"
      >&#8758;</a
      ><a name="12327"
      > </a
      ><a name="12328" href="Stlc.html#12244" class="Bound"
      >A&#8242;</a
      ><a name="12330"
      > </a
      ><a name="12331" href="Stlc.html#3672" class="InductiveConstructor Operator"
      >]</a
      ><a name="12332"
      > </a
      ><a name="12333" class="Symbol"
      >(</a
      ><a name="12334" href="Stlc.html#12249" class="Bound"
      >N&#8242;</a
      ><a name="12336"
      > </a
      ><a name="12337" href="Stlc.html#12136" class="Function Operator"
      >[</a
      ><a name="12338"
      > </a
      ><a name="12339" href="Stlc.html#12255" class="Bound"
      >x</a
      ><a name="12340"
      > </a
      ><a name="12341" href="Stlc.html#12136" class="Function Operator"
      >:=</a
      ><a name="12343"
      > </a
      ><a name="12344" href="Stlc.html#12260" class="Bound"
      >V</a
      ><a name="12345"
      > </a
      ><a name="12346" href="Stlc.html#12136" class="Function Operator"
      >]</a
      ><a name="12347" class="Symbol"
      >)</a
      ><a name="12348"
      >
</a
      ><a name="12349" class="Symbol"
      >(</a
      ><a name="12350" href="Stlc.html#12350" class="Bound"
      >L&#8242;</a
      ><a name="12352"
      > </a
      ><a name="12353" href="Stlc.html#3708" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="12354"
      > </a
      ><a name="12355" href="Stlc.html#12355" class="Bound"
      >M&#8242;</a
      ><a name="12357" class="Symbol"
      >)</a
      ><a name="12358"
      > </a
      ><a name="12359" href="Stlc.html#12136" class="Function Operator"
      >[</a
      ><a name="12360"
      > </a
      ><a name="12361" href="Stlc.html#12361" class="Bound"
      >x</a
      ><a name="12362"
      > </a
      ><a name="12363" href="Stlc.html#12136" class="Function Operator"
      >:=</a
      ><a name="12365"
      > </a
      ><a name="12366" href="Stlc.html#12366" class="Bound"
      >V</a
      ><a name="12367"
      > </a
      ><a name="12368" href="Stlc.html#12136" class="Function Operator"
      >]</a
      ><a name="12369"
      > </a
      ><a name="12370" class="Symbol"
      >=</a
      ><a name="12371"
      >  </a
      ><a name="12373" class="Symbol"
      >(</a
      ><a name="12374" href="Stlc.html#12350" class="Bound"
      >L&#8242;</a
      ><a name="12376"
      > </a
      ><a name="12377" href="Stlc.html#12136" class="Function Operator"
      >[</a
      ><a name="12378"
      > </a
      ><a name="12379" href="Stlc.html#12361" class="Bound"
      >x</a
      ><a name="12380"
      > </a
      ><a name="12381" href="Stlc.html#12136" class="Function Operator"
      >:=</a
      ><a name="12383"
      > </a
      ><a name="12384" href="Stlc.html#12366" class="Bound"
      >V</a
      ><a name="12385"
      > </a
      ><a name="12386" href="Stlc.html#12136" class="Function Operator"
      >]</a
      ><a name="12387" class="Symbol"
      >)</a
      ><a name="12388"
      > </a
      ><a name="12389" href="Stlc.html#3708" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="12390"
      > </a
      ><a name="12391" class="Symbol"
      >(</a
      ><a name="12392" href="Stlc.html#12355" class="Bound"
      >M&#8242;</a
      ><a name="12394"
      > </a
      ><a name="12395" href="Stlc.html#12136" class="Function Operator"
      >[</a
      ><a name="12396"
      > </a
      ><a name="12397" href="Stlc.html#12361" class="Bound"
      >x</a
      ><a name="12398"
      > </a
      ><a name="12399" href="Stlc.html#12136" class="Function Operator"
      >:=</a
      ><a name="12401"
      > </a
      ><a name="12402" href="Stlc.html#12366" class="Bound"
      >V</a
      ><a name="12403"
      > </a
      ><a name="12404" href="Stlc.html#12136" class="Function Operator"
      >]</a
      ><a name="12405" class="Symbol"
      >)</a
      ><a name="12406"
      >
</a
      ><a name="12407" class="Symbol"
      >(</a
      ><a name="12408" href="Stlc.html#3735" class="InductiveConstructor"
      >true</a
      ><a name="12412" class="Symbol"
      >)</a
      ><a name="12413"
      > </a
      ><a name="12414" href="Stlc.html#12136" class="Function Operator"
      >[</a
      ><a name="12415"
      > </a
      ><a name="12416" href="Stlc.html#12416" class="Bound"
      >x</a
      ><a name="12417"
      > </a
      ><a name="12418" href="Stlc.html#12136" class="Function Operator"
      >:=</a
      ><a name="12420"
      > </a
      ><a name="12421" href="Stlc.html#12421" class="Bound"
      >V</a
      ><a name="12422"
      > </a
      ><a name="12423" href="Stlc.html#12136" class="Function Operator"
      >]</a
      ><a name="12424"
      > </a
      ><a name="12425" class="Symbol"
      >=</a
      ><a name="12426"
      > </a
      ><a name="12427" href="Stlc.html#3735" class="InductiveConstructor"
      >true</a
      ><a name="12431"
      >
</a
      ><a name="12432" class="Symbol"
      >(</a
      ><a name="12433" href="Stlc.html#3749" class="InductiveConstructor"
      >false</a
      ><a name="12438" class="Symbol"
      >)</a
      ><a name="12439"
      > </a
      ><a name="12440" href="Stlc.html#12136" class="Function Operator"
      >[</a
      ><a name="12441"
      > </a
      ><a name="12442" href="Stlc.html#12442" class="Bound"
      >x</a
      ><a name="12443"
      > </a
      ><a name="12444" href="Stlc.html#12136" class="Function Operator"
      >:=</a
      ><a name="12446"
      > </a
      ><a name="12447" href="Stlc.html#12447" class="Bound"
      >V</a
      ><a name="12448"
      > </a
      ><a name="12449" href="Stlc.html#12136" class="Function Operator"
      >]</a
      ><a name="12450"
      > </a
      ><a name="12451" class="Symbol"
      >=</a
      ><a name="12452"
      > </a
      ><a name="12453" href="Stlc.html#3749" class="InductiveConstructor"
      >false</a
      ><a name="12458"
      >
</a
      ><a name="12459" class="Symbol"
      >(</a
      ><a name="12460" href="Stlc.html#3764" class="InductiveConstructor Operator"
      >if</a
      ><a name="12462"
      > </a
      ><a name="12463" href="Stlc.html#12463" class="Bound"
      >L&#8242;</a
      ><a name="12465"
      > </a
      ><a name="12466" href="Stlc.html#3764" class="InductiveConstructor Operator"
      >then</a
      ><a name="12470"
      > </a
      ><a name="12471" href="Stlc.html#12471" class="Bound"
      >M&#8242;</a
      ><a name="12473"
      > </a
      ><a name="12474" href="Stlc.html#3764" class="InductiveConstructor Operator"
      >else</a
      ><a name="12478"
      > </a
      ><a name="12479" href="Stlc.html#12479" class="Bound"
      >N&#8242;</a
      ><a name="12481" class="Symbol"
      >)</a
      ><a name="12482"
      > </a
      ><a name="12483" href="Stlc.html#12136" class="Function Operator"
      >[</a
      ><a name="12484"
      > </a
      ><a name="12485" href="Stlc.html#12485" class="Bound"
      >x</a
      ><a name="12486"
      > </a
      ><a name="12487" href="Stlc.html#12136" class="Function Operator"
      >:=</a
      ><a name="12489"
      > </a
      ><a name="12490" href="Stlc.html#12490" class="Bound"
      >V</a
      ><a name="12491"
      > </a
      ><a name="12492" href="Stlc.html#12136" class="Function Operator"
      >]</a
      ><a name="12493"
      > </a
      ><a name="12494" class="Symbol"
      >=</a
      ><a name="12495"
      >
  </a
      ><a name="12498" href="Stlc.html#3764" class="InductiveConstructor Operator"
      >if</a
      ><a name="12500"
      > </a
      ><a name="12501" class="Symbol"
      >(</a
      ><a name="12502" href="Stlc.html#12463" class="Bound"
      >L&#8242;</a
      ><a name="12504"
      > </a
      ><a name="12505" href="Stlc.html#12136" class="Function Operator"
      >[</a
      ><a name="12506"
      > </a
      ><a name="12507" href="Stlc.html#12485" class="Bound"
      >x</a
      ><a name="12508"
      > </a
      ><a name="12509" href="Stlc.html#12136" class="Function Operator"
      >:=</a
      ><a name="12511"
      > </a
      ><a name="12512" href="Stlc.html#12490" class="Bound"
      >V</a
      ><a name="12513"
      > </a
      ><a name="12514" href="Stlc.html#12136" class="Function Operator"
      >]</a
      ><a name="12515" class="Symbol"
      >)</a
      ><a name="12516"
      > </a
      ><a name="12517" href="Stlc.html#3764" class="InductiveConstructor Operator"
      >then</a
      ><a name="12521"
      > </a
      ><a name="12522" class="Symbol"
      >(</a
      ><a name="12523" href="Stlc.html#12471" class="Bound"
      >M&#8242;</a
      ><a name="12525"
      > </a
      ><a name="12526" href="Stlc.html#12136" class="Function Operator"
      >[</a
      ><a name="12527"
      > </a
      ><a name="12528" href="Stlc.html#12485" class="Bound"
      >x</a
      ><a name="12529"
      > </a
      ><a name="12530" href="Stlc.html#12136" class="Function Operator"
      >:=</a
      ><a name="12532"
      > </a
      ><a name="12533" href="Stlc.html#12490" class="Bound"
      >V</a
      ><a name="12534"
      > </a
      ><a name="12535" href="Stlc.html#12136" class="Function Operator"
      >]</a
      ><a name="12536" class="Symbol"
      >)</a
      ><a name="12537"
      > </a
      ><a name="12538" href="Stlc.html#3764" class="InductiveConstructor Operator"
      >else</a
      ><a name="12542"
      > </a
      ><a name="12543" class="Symbol"
      >(</a
      ><a name="12544" href="Stlc.html#12479" class="Bound"
      >N&#8242;</a
      ><a name="12546"
      > </a
      ><a name="12547" href="Stlc.html#12136" class="Function Operator"
      >[</a
      ><a name="12548"
      > </a
      ><a name="12549" href="Stlc.html#12485" class="Bound"
      >x</a
      ><a name="12550"
      > </a
      ><a name="12551" href="Stlc.html#12136" class="Function Operator"
      >:=</a
      ><a name="12553"
      > </a
      ><a name="12554" href="Stlc.html#12490" class="Bound"
      >V</a
      ><a name="12555"
      > </a
      ><a name="12556" href="Stlc.html#12136" class="Function Operator"
      >]</a
      ><a name="12557" class="Symbol"
      >)</a
      >
{% endraw %}</pre>

The two key cases are variables and abstraction.

* For variables, we compare `x`, the variable we are substituting for,
with `x′`, the variable in the term. If they are the same,
we yield `V`, otherwise we yield `x′` unchanged.

* For abstractions, we compare `x`, the variable we are substituting for,
with `x′`, the variable bound in the abstraction. If they are the same,
we yield abstraction unchanged, otherwise we subsititute inside the body.

In all other cases, we push substitution recursively into
the subterms.

#### Special characters

    ′  U+2032: PRIME (\')

Note that ′ (U+2032: PRIME) is not the same as ' (U+0027: APOSTROPHE).


#### Examples

Here is confirmation that the examples above are correct.

<pre class="Agda">{% raw %}
<a name="13307" href="Stlc.html#13307" class="Function"
      >ex&#8321;&#8321;</a
      ><a name="13311"
      > </a
      ><a name="13312" class="Symbol"
      >:</a
      ><a name="13313"
      > </a
      ><a name="13314" href="Stlc.html#3656" class="InductiveConstructor"
      >`</a
      ><a name="13315"
      > </a
      ><a name="13316" href="Stlc.html#5677" class="Function"
      >f</a
      ><a name="13317"
      > </a
      ><a name="13318" href="Stlc.html#12136" class="Function Operator"
      >[</a
      ><a name="13319"
      > </a
      ><a name="13320" href="Stlc.html#5677" class="Function"
      >f</a
      ><a name="13321"
      > </a
      ><a name="13322" href="Stlc.html#12136" class="Function Operator"
      >:=</a
      ><a name="13324"
      > </a
      ><a name="13325" href="Stlc.html#5722" class="Function"
      >not</a
      ><a name="13328"
      > </a
      ><a name="13329" href="Stlc.html#12136" class="Function Operator"
      >]</a
      ><a name="13330"
      > </a
      ><a name="13331" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="13332"
      >  </a
      ><a name="13334" href="Stlc.html#5722" class="Function"
      >not</a
      ><a name="13337"
      >
</a
      ><a name="13338" href="Stlc.html#13307" class="Function"
      >ex&#8321;&#8321;</a
      ><a name="13342"
      > </a
      ><a name="13343" class="Symbol"
      >=</a
      ><a name="13344"
      > </a
      ><a name="13345" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="13349"
      >

</a
      ><a name="13351" href="Stlc.html#13351" class="Function"
      >ex&#8321;&#8322;</a
      ><a name="13355"
      > </a
      ><a name="13356" class="Symbol"
      >:</a
      ><a name="13357"
      > </a
      ><a name="13358" href="Stlc.html#3735" class="InductiveConstructor"
      >true</a
      ><a name="13362"
      > </a
      ><a name="13363" href="Stlc.html#12136" class="Function Operator"
      >[</a
      ><a name="13364"
      > </a
      ><a name="13365" href="Stlc.html#5677" class="Function"
      >f</a
      ><a name="13366"
      > </a
      ><a name="13367" href="Stlc.html#12136" class="Function Operator"
      >:=</a
      ><a name="13369"
      > </a
      ><a name="13370" href="Stlc.html#5722" class="Function"
      >not</a
      ><a name="13373"
      > </a
      ><a name="13374" href="Stlc.html#12136" class="Function Operator"
      >]</a
      ><a name="13375"
      > </a
      ><a name="13376" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="13377"
      > </a
      ><a name="13378" href="Stlc.html#3735" class="InductiveConstructor"
      >true</a
      ><a name="13382"
      >
</a
      ><a name="13383" href="Stlc.html#13351" class="Function"
      >ex&#8321;&#8322;</a
      ><a name="13387"
      > </a
      ><a name="13388" class="Symbol"
      >=</a
      ><a name="13389"
      > </a
      ><a name="13390" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="13394"
      >

</a
      ><a name="13396" href="Stlc.html#13396" class="Function"
      >ex&#8321;&#8323;</a
      ><a name="13400"
      > </a
      ><a name="13401" class="Symbol"
      >:</a
      ><a name="13402"
      > </a
      ><a name="13403" class="Symbol"
      >(</a
      ><a name="13404" href="Stlc.html#3656" class="InductiveConstructor"
      >`</a
      ><a name="13405"
      > </a
      ><a name="13406" href="Stlc.html#5677" class="Function"
      >f</a
      ><a name="13407"
      > </a
      ><a name="13408" href="Stlc.html#3708" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="13409"
      > </a
      ><a name="13410" href="Stlc.html#3735" class="InductiveConstructor"
      >true</a
      ><a name="13414" class="Symbol"
      >)</a
      ><a name="13415"
      > </a
      ><a name="13416" href="Stlc.html#12136" class="Function Operator"
      >[</a
      ><a name="13417"
      > </a
      ><a name="13418" href="Stlc.html#5677" class="Function"
      >f</a
      ><a name="13419"
      > </a
      ><a name="13420" href="Stlc.html#12136" class="Function Operator"
      >:=</a
      ><a name="13422"
      > </a
      ><a name="13423" href="Stlc.html#5722" class="Function"
      >not</a
      ><a name="13426"
      > </a
      ><a name="13427" href="Stlc.html#12136" class="Function Operator"
      >]</a
      ><a name="13428"
      > </a
      ><a name="13429" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="13430"
      > </a
      ><a name="13431" href="Stlc.html#5722" class="Function"
      >not</a
      ><a name="13434"
      > </a
      ><a name="13435" href="Stlc.html#3708" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="13436"
      > </a
      ><a name="13437" href="Stlc.html#3735" class="InductiveConstructor"
      >true</a
      ><a name="13441"
      >
</a
      ><a name="13442" href="Stlc.html#13396" class="Function"
      >ex&#8321;&#8323;</a
      ><a name="13446"
      > </a
      ><a name="13447" class="Symbol"
      >=</a
      ><a name="13448"
      > </a
      ><a name="13449" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="13453"
      >

</a
      ><a name="13455" href="Stlc.html#13455" class="Function"
      >ex&#8321;&#8324;</a
      ><a name="13459"
      > </a
      ><a name="13460" class="Symbol"
      >:</a
      ><a name="13461"
      > </a
      ><a name="13462" class="Symbol"
      >(</a
      ><a name="13463" href="Stlc.html#3656" class="InductiveConstructor"
      >`</a
      ><a name="13464"
      > </a
      ><a name="13465" href="Stlc.html#5677" class="Function"
      >f</a
      ><a name="13466"
      > </a
      ><a name="13467" href="Stlc.html#3708" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="13468"
      > </a
      ><a name="13469" class="Symbol"
      >(</a
      ><a name="13470" href="Stlc.html#3656" class="InductiveConstructor"
      >`</a
      ><a name="13471"
      > </a
      ><a name="13472" href="Stlc.html#5677" class="Function"
      >f</a
      ><a name="13473"
      > </a
      ><a name="13474" href="Stlc.html#3708" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="13475"
      > </a
      ><a name="13476" href="Stlc.html#3735" class="InductiveConstructor"
      >true</a
      ><a name="13480" class="Symbol"
      >))</a
      ><a name="13482"
      > </a
      ><a name="13483" href="Stlc.html#12136" class="Function Operator"
      >[</a
      ><a name="13484"
      > </a
      ><a name="13485" href="Stlc.html#5677" class="Function"
      >f</a
      ><a name="13486"
      > </a
      ><a name="13487" href="Stlc.html#12136" class="Function Operator"
      >:=</a
      ><a name="13489"
      > </a
      ><a name="13490" href="Stlc.html#5722" class="Function"
      >not</a
      ><a name="13493"
      > </a
      ><a name="13494" href="Stlc.html#12136" class="Function Operator"
      >]</a
      ><a name="13495"
      > </a
      ><a name="13496" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="13497"
      > </a
      ><a name="13498" href="Stlc.html#5722" class="Function"
      >not</a
      ><a name="13501"
      > </a
      ><a name="13502" href="Stlc.html#3708" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="13503"
      > </a
      ><a name="13504" class="Symbol"
      >(</a
      ><a name="13505" href="Stlc.html#5722" class="Function"
      >not</a
      ><a name="13508"
      > </a
      ><a name="13509" href="Stlc.html#3708" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="13510"
      > </a
      ><a name="13511" href="Stlc.html#3735" class="InductiveConstructor"
      >true</a
      ><a name="13515" class="Symbol"
      >)</a
      ><a name="13516"
      >
</a
      ><a name="13517" href="Stlc.html#13455" class="Function"
      >ex&#8321;&#8324;</a
      ><a name="13521"
      > </a
      ><a name="13522" class="Symbol"
      >=</a
      ><a name="13523"
      > </a
      ><a name="13524" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="13528"
      >

</a
      ><a name="13530" href="Stlc.html#13530" class="Function"
      >ex&#8321;&#8325;</a
      ><a name="13534"
      > </a
      ><a name="13535" class="Symbol"
      >:</a
      ><a name="13536"
      > </a
      ><a name="13537" class="Symbol"
      >(</a
      ><a name="13538" href="Stlc.html#3672" class="InductiveConstructor Operator"
      >&#955;[</a
      ><a name="13540"
      > </a
      ><a name="13541" href="Stlc.html#5679" class="Function"
      >x</a
      ><a name="13542"
      > </a
      ><a name="13543" href="Stlc.html#3672" class="InductiveConstructor Operator"
      >&#8758;</a
      ><a name="13544"
      > </a
      ><a name="13545" href="Stlc.html#2610" class="InductiveConstructor"
      >&#120121;</a
      ><a name="13546"
      > </a
      ><a name="13547" href="Stlc.html#3672" class="InductiveConstructor Operator"
      >]</a
      ><a name="13548"
      > </a
      ><a name="13549" href="Stlc.html#3656" class="InductiveConstructor"
      >`</a
      ><a name="13550"
      > </a
      ><a name="13551" href="Stlc.html#5677" class="Function"
      >f</a
      ><a name="13552"
      > </a
      ><a name="13553" href="Stlc.html#3708" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="13554"
      > </a
      ><a name="13555" class="Symbol"
      >(</a
      ><a name="13556" href="Stlc.html#3656" class="InductiveConstructor"
      >`</a
      ><a name="13557"
      > </a
      ><a name="13558" href="Stlc.html#5677" class="Function"
      >f</a
      ><a name="13559"
      > </a
      ><a name="13560" href="Stlc.html#3708" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="13561"
      > </a
      ><a name="13562" href="Stlc.html#3656" class="InductiveConstructor"
      >`</a
      ><a name="13563"
      > </a
      ><a name="13564" href="Stlc.html#5679" class="Function"
      >x</a
      ><a name="13565" class="Symbol"
      >))</a
      ><a name="13567"
      > </a
      ><a name="13568" href="Stlc.html#12136" class="Function Operator"
      >[</a
      ><a name="13569"
      > </a
      ><a name="13570" href="Stlc.html#5677" class="Function"
      >f</a
      ><a name="13571"
      > </a
      ><a name="13572" href="Stlc.html#12136" class="Function Operator"
      >:=</a
      ><a name="13574"
      > </a
      ><a name="13575" href="Stlc.html#5722" class="Function"
      >not</a
      ><a name="13578"
      > </a
      ><a name="13579" href="Stlc.html#12136" class="Function Operator"
      >]</a
      ><a name="13580"
      > </a
      ><a name="13581" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="13582"
      > </a
      ><a name="13583" href="Stlc.html#3672" class="InductiveConstructor Operator"
      >&#955;[</a
      ><a name="13585"
      > </a
      ><a name="13586" href="Stlc.html#5679" class="Function"
      >x</a
      ><a name="13587"
      > </a
      ><a name="13588" href="Stlc.html#3672" class="InductiveConstructor Operator"
      >&#8758;</a
      ><a name="13589"
      > </a
      ><a name="13590" href="Stlc.html#2610" class="InductiveConstructor"
      >&#120121;</a
      ><a name="13591"
      > </a
      ><a name="13592" href="Stlc.html#3672" class="InductiveConstructor Operator"
      >]</a
      ><a name="13593"
      > </a
      ><a name="13594" href="Stlc.html#5722" class="Function"
      >not</a
      ><a name="13597"
      > </a
      ><a name="13598" href="Stlc.html#3708" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="13599"
      > </a
      ><a name="13600" class="Symbol"
      >(</a
      ><a name="13601" href="Stlc.html#5722" class="Function"
      >not</a
      ><a name="13604"
      > </a
      ><a name="13605" href="Stlc.html#3708" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="13606"
      > </a
      ><a name="13607" href="Stlc.html#3656" class="InductiveConstructor"
      >`</a
      ><a name="13608"
      > </a
      ><a name="13609" href="Stlc.html#5679" class="Function"
      >x</a
      ><a name="13610" class="Symbol"
      >)</a
      ><a name="13611"
      >
</a
      ><a name="13612" href="Stlc.html#13530" class="Function"
      >ex&#8321;&#8325;</a
      ><a name="13616"
      > </a
      ><a name="13617" class="Symbol"
      >=</a
      ><a name="13618"
      > </a
      ><a name="13619" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="13623"
      >

</a
      ><a name="13625" href="Stlc.html#13625" class="Function"
      >ex&#8321;&#8326;</a
      ><a name="13629"
      > </a
      ><a name="13630" class="Symbol"
      >:</a
      ><a name="13631"
      > </a
      ><a name="13632" class="Symbol"
      >(</a
      ><a name="13633" href="Stlc.html#3672" class="InductiveConstructor Operator"
      >&#955;[</a
      ><a name="13635"
      > </a
      ><a name="13636" href="Stlc.html#5681" class="Function"
      >y</a
      ><a name="13637"
      > </a
      ><a name="13638" href="Stlc.html#3672" class="InductiveConstructor Operator"
      >&#8758;</a
      ><a name="13639"
      > </a
      ><a name="13640" href="Stlc.html#2610" class="InductiveConstructor"
      >&#120121;</a
      ><a name="13641"
      > </a
      ><a name="13642" href="Stlc.html#3672" class="InductiveConstructor Operator"
      >]</a
      ><a name="13643"
      > </a
      ><a name="13644" href="Stlc.html#3656" class="InductiveConstructor"
      >`</a
      ><a name="13645"
      > </a
      ><a name="13646" href="Stlc.html#5681" class="Function"
      >y</a
      ><a name="13647" class="Symbol"
      >)</a
      ><a name="13648"
      > </a
      ><a name="13649" href="Stlc.html#12136" class="Function Operator"
      >[</a
      ><a name="13650"
      > </a
      ><a name="13651" href="Stlc.html#5679" class="Function"
      >x</a
      ><a name="13652"
      > </a
      ><a name="13653" href="Stlc.html#12136" class="Function Operator"
      >:=</a
      ><a name="13655"
      > </a
      ><a name="13656" href="Stlc.html#3735" class="InductiveConstructor"
      >true</a
      ><a name="13660"
      > </a
      ><a name="13661" href="Stlc.html#12136" class="Function Operator"
      >]</a
      ><a name="13662"
      > </a
      ><a name="13663" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="13664"
      > </a
      ><a name="13665" href="Stlc.html#3672" class="InductiveConstructor Operator"
      >&#955;[</a
      ><a name="13667"
      > </a
      ><a name="13668" href="Stlc.html#5681" class="Function"
      >y</a
      ><a name="13669"
      > </a
      ><a name="13670" href="Stlc.html#3672" class="InductiveConstructor Operator"
      >&#8758;</a
      ><a name="13671"
      > </a
      ><a name="13672" href="Stlc.html#2610" class="InductiveConstructor"
      >&#120121;</a
      ><a name="13673"
      > </a
      ><a name="13674" href="Stlc.html#3672" class="InductiveConstructor Operator"
      >]</a
      ><a name="13675"
      > </a
      ><a name="13676" href="Stlc.html#3656" class="InductiveConstructor"
      >`</a
      ><a name="13677"
      > </a
      ><a name="13678" href="Stlc.html#5681" class="Function"
      >y</a
      ><a name="13679"
      >
</a
      ><a name="13680" href="Stlc.html#13625" class="Function"
      >ex&#8321;&#8326;</a
      ><a name="13684"
      > </a
      ><a name="13685" class="Symbol"
      >=</a
      ><a name="13686"
      > </a
      ><a name="13687" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="13691"
      >

</a
      ><a name="13693" href="Stlc.html#13693" class="Function"
      >ex&#8321;&#8327;</a
      ><a name="13697"
      > </a
      ><a name="13698" class="Symbol"
      >:</a
      ><a name="13699"
      > </a
      ><a name="13700" class="Symbol"
      >(</a
      ><a name="13701" href="Stlc.html#3672" class="InductiveConstructor Operator"
      >&#955;[</a
      ><a name="13703"
      > </a
      ><a name="13704" href="Stlc.html#5679" class="Function"
      >x</a
      ><a name="13705"
      > </a
      ><a name="13706" href="Stlc.html#3672" class="InductiveConstructor Operator"
      >&#8758;</a
      ><a name="13707"
      > </a
      ><a name="13708" href="Stlc.html#2610" class="InductiveConstructor"
      >&#120121;</a
      ><a name="13709"
      > </a
      ><a name="13710" href="Stlc.html#3672" class="InductiveConstructor Operator"
      >]</a
      ><a name="13711"
      > </a
      ><a name="13712" href="Stlc.html#3656" class="InductiveConstructor"
      >`</a
      ><a name="13713"
      > </a
      ><a name="13714" href="Stlc.html#5679" class="Function"
      >x</a
      ><a name="13715" class="Symbol"
      >)</a
      ><a name="13716"
      > </a
      ><a name="13717" href="Stlc.html#12136" class="Function Operator"
      >[</a
      ><a name="13718"
      > </a
      ><a name="13719" href="Stlc.html#5679" class="Function"
      >x</a
      ><a name="13720"
      > </a
      ><a name="13721" href="Stlc.html#12136" class="Function Operator"
      >:=</a
      ><a name="13723"
      > </a
      ><a name="13724" href="Stlc.html#3735" class="InductiveConstructor"
      >true</a
      ><a name="13728"
      > </a
      ><a name="13729" href="Stlc.html#12136" class="Function Operator"
      >]</a
      ><a name="13730"
      > </a
      ><a name="13731" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="13732"
      > </a
      ><a name="13733" href="Stlc.html#3672" class="InductiveConstructor Operator"
      >&#955;[</a
      ><a name="13735"
      > </a
      ><a name="13736" href="Stlc.html#5679" class="Function"
      >x</a
      ><a name="13737"
      > </a
      ><a name="13738" href="Stlc.html#3672" class="InductiveConstructor Operator"
      >&#8758;</a
      ><a name="13739"
      > </a
      ><a name="13740" href="Stlc.html#2610" class="InductiveConstructor"
      >&#120121;</a
      ><a name="13741"
      > </a
      ><a name="13742" href="Stlc.html#3672" class="InductiveConstructor Operator"
      >]</a
      ><a name="13743"
      > </a
      ><a name="13744" href="Stlc.html#3656" class="InductiveConstructor"
      >`</a
      ><a name="13745"
      > </a
      ><a name="13746" href="Stlc.html#5679" class="Function"
      >x</a
      ><a name="13747"
      >
</a
      ><a name="13748" href="Stlc.html#13693" class="Function"
      >ex&#8321;&#8327;</a
      ><a name="13752"
      > </a
      ><a name="13753" class="Symbol"
      >=</a
      ><a name="13754"
      > </a
      ><a name="13755" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      >
{% endraw %}</pre>

#### Quiz

What is the result of the following substitution?

    (λ[ y ∶ 𝔹 ] ` x · (λ[ x ∶ 𝔹 ] ` x)) [ x := true ]

1. `` (λ[ y ∶ 𝔹 ] ` x · (λ[ x ∶ 𝔹 ] ` x)) ``
2. `` (λ[ y ∶ 𝔹 ] ` x · (λ[ x ∶ 𝔹 ] true)) ``
3. `` (λ[ y ∶ 𝔹 ] true · (λ[ x ∶ 𝔹 ] ` x)) ``
4. `` (λ[ y ∶ 𝔹 ] true · (λ[ x ∶ 𝔹 ] ` true)) ``


## Reduction

We give the reduction rules for call-by-value lambda calculus.  To
reduce an application, first we reduce the left-hand side until it
becomes a value (which must be an abstraction); then we reduce the
right-hand side until it becomes a value; and finally we substitute
the argument for the variable in the abstraction.  To reduce a
conditional, we first reduce the condition until it becomes a value;
if the condition is true the conditional reduces to the first
branch and if false it reduces to the second branch.a

In an informal presentation of the formal semantics, 
the rules for reduction are written as follows.

    L ⟹ L′
    --------------- ξ·₁
    L · M ⟹ L′ · M

    Value V
    M ⟹ M′
    --------------- ξ·₂
    V · M ⟹ V · M′

    Value V
    --------------------------------- βλ·
    (λ[ x ∶ A ] N) · V ⟹ N [ x := V ]

    L ⟹ L′
    ----------------------------------------- ξif
    if L then M else N ⟹ if L′ then M else N

    -------------------------- βif-true
    if true then M else N ⟹ M

    --------------------------- βif-false
    if false then M else N ⟹ N

As we will show later, the rules are deterministic, in that
at most one rule applies to every term.  As we will also show
later, for every well-typed term either a reduction applies
or it is a value.

The rules break into two sorts. Compatibility rules
direct us to reduce some part of a term.
We give them names starting with the Greek letter xi, `ξ`.
Once a term is sufficiently
reduced, it will consist of a constructor and
a deconstructor, in our case `λ` and `·`, or
`if` and `true`, or `if` and `false`.
We give them names starting with the Greek letter beta, `β`,
and indeed such rules are traditionally called beta rules.

Here are the above rules formalised in Agda.

<pre class="Agda">{% raw %}
<a name="15869" class="Keyword"
      >infix</a
      ><a name="15874"
      > </a
      ><a name="15875" class="Number"
      >10</a
      ><a name="15877"
      > </a
      ><a name="15878" href="Stlc.html#15889" class="Datatype Operator"
      >_&#10233;_</a
      ><a name="15881"
      > 

</a
      ><a name="15884" class="Keyword"
      >data</a
      ><a name="15888"
      > </a
      ><a name="15889" href="Stlc.html#15889" class="Datatype Operator"
      >_&#10233;_</a
      ><a name="15892"
      > </a
      ><a name="15893" class="Symbol"
      >:</a
      ><a name="15894"
      > </a
      ><a name="15895" href="Stlc.html#3637" class="Datatype"
      >Term</a
      ><a name="15899"
      > </a
      ><a name="15900" class="Symbol"
      >&#8594;</a
      ><a name="15901"
      > </a
      ><a name="15902" href="Stlc.html#3637" class="Datatype"
      >Term</a
      ><a name="15906"
      > </a
      ><a name="15907" class="Symbol"
      >&#8594;</a
      ><a name="15908"
      > </a
      ><a name="15909" class="PrimitiveType"
      >Set</a
      ><a name="15912"
      > </a
      ><a name="15913" class="Keyword"
      >where</a
      ><a name="15918"
      >
  </a
      ><a name="15921" href="Stlc.html#15921" class="InductiveConstructor"
      >&#958;&#183;&#8321;</a
      ><a name="15924"
      > </a
      ><a name="15925" class="Symbol"
      >:</a
      ><a name="15926"
      > </a
      ><a name="15927" class="Symbol"
      >&#8704;</a
      ><a name="15928"
      > </a
      ><a name="15929" class="Symbol"
      >{</a
      ><a name="15930" href="Stlc.html#15930" class="Bound"
      >L</a
      ><a name="15931"
      > </a
      ><a name="15932" href="Stlc.html#15932" class="Bound"
      >L&#8242;</a
      ><a name="15934"
      > </a
      ><a name="15935" href="Stlc.html#15935" class="Bound"
      >M</a
      ><a name="15936" class="Symbol"
      >}</a
      ><a name="15937"
      > </a
      ><a name="15938" class="Symbol"
      >&#8594;</a
      ><a name="15939"
      >
    </a
      ><a name="15944" href="Stlc.html#15930" class="Bound"
      >L</a
      ><a name="15945"
      > </a
      ><a name="15946" href="Stlc.html#15889" class="Datatype Operator"
      >&#10233;</a
      ><a name="15947"
      > </a
      ><a name="15948" href="Stlc.html#15932" class="Bound"
      >L&#8242;</a
      ><a name="15950"
      > </a
      ><a name="15951" class="Symbol"
      >&#8594;</a
      ><a name="15952"
      >
    </a
      ><a name="15957" href="Stlc.html#15930" class="Bound"
      >L</a
      ><a name="15958"
      > </a
      ><a name="15959" href="Stlc.html#3708" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="15960"
      > </a
      ><a name="15961" href="Stlc.html#15935" class="Bound"
      >M</a
      ><a name="15962"
      > </a
      ><a name="15963" href="Stlc.html#15889" class="Datatype Operator"
      >&#10233;</a
      ><a name="15964"
      > </a
      ><a name="15965" href="Stlc.html#15932" class="Bound"
      >L&#8242;</a
      ><a name="15967"
      > </a
      ><a name="15968" href="Stlc.html#3708" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="15969"
      > </a
      ><a name="15970" href="Stlc.html#15935" class="Bound"
      >M</a
      ><a name="15971"
      >
  </a
      ><a name="15974" href="Stlc.html#15974" class="InductiveConstructor"
      >&#958;&#183;&#8322;</a
      ><a name="15977"
      > </a
      ><a name="15978" class="Symbol"
      >:</a
      ><a name="15979"
      > </a
      ><a name="15980" class="Symbol"
      >&#8704;</a
      ><a name="15981"
      > </a
      ><a name="15982" class="Symbol"
      >{</a
      ><a name="15983" href="Stlc.html#15983" class="Bound"
      >V</a
      ><a name="15984"
      > </a
      ><a name="15985" href="Stlc.html#15985" class="Bound"
      >M</a
      ><a name="15986"
      > </a
      ><a name="15987" href="Stlc.html#15987" class="Bound"
      >M&#8242;</a
      ><a name="15989" class="Symbol"
      >}</a
      ><a name="15990"
      > </a
      ><a name="15991" class="Symbol"
      >&#8594;</a
      ><a name="15992"
      >
    </a
      ><a name="15997" href="Stlc.html#9592" class="Datatype"
      >Value</a
      ><a name="16002"
      > </a
      ><a name="16003" href="Stlc.html#15983" class="Bound"
      >V</a
      ><a name="16004"
      > </a
      ><a name="16005" class="Symbol"
      >&#8594;</a
      ><a name="16006"
      >
    </a
      ><a name="16011" href="Stlc.html#15985" class="Bound"
      >M</a
      ><a name="16012"
      > </a
      ><a name="16013" href="Stlc.html#15889" class="Datatype Operator"
      >&#10233;</a
      ><a name="16014"
      > </a
      ><a name="16015" href="Stlc.html#15987" class="Bound"
      >M&#8242;</a
      ><a name="16017"
      > </a
      ><a name="16018" class="Symbol"
      >&#8594;</a
      ><a name="16019"
      >
    </a
      ><a name="16024" href="Stlc.html#15983" class="Bound"
      >V</a
      ><a name="16025"
      > </a
      ><a name="16026" href="Stlc.html#3708" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="16027"
      > </a
      ><a name="16028" href="Stlc.html#15985" class="Bound"
      >M</a
      ><a name="16029"
      > </a
      ><a name="16030" href="Stlc.html#15889" class="Datatype Operator"
      >&#10233;</a
      ><a name="16031"
      > </a
      ><a name="16032" href="Stlc.html#15983" class="Bound"
      >V</a
      ><a name="16033"
      > </a
      ><a name="16034" href="Stlc.html#3708" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="16035"
      > </a
      ><a name="16036" href="Stlc.html#15987" class="Bound"
      >M&#8242;</a
      ><a name="16038"
      >
  </a
      ><a name="16041" href="Stlc.html#16041" class="InductiveConstructor"
      >&#946;&#955;&#183;</a
      ><a name="16044"
      > </a
      ><a name="16045" class="Symbol"
      >:</a
      ><a name="16046"
      > </a
      ><a name="16047" class="Symbol"
      >&#8704;</a
      ><a name="16048"
      > </a
      ><a name="16049" class="Symbol"
      >{</a
      ><a name="16050" href="Stlc.html#16050" class="Bound"
      >x</a
      ><a name="16051"
      > </a
      ><a name="16052" href="Stlc.html#16052" class="Bound"
      >A</a
      ><a name="16053"
      > </a
      ><a name="16054" href="Stlc.html#16054" class="Bound"
      >N</a
      ><a name="16055"
      > </a
      ><a name="16056" href="Stlc.html#16056" class="Bound"
      >V</a
      ><a name="16057" class="Symbol"
      >}</a
      ><a name="16058"
      > </a
      ><a name="16059" class="Symbol"
      >&#8594;</a
      ><a name="16060"
      > </a
      ><a name="16061" href="Stlc.html#9592" class="Datatype"
      >Value</a
      ><a name="16066"
      > </a
      ><a name="16067" href="Stlc.html#16056" class="Bound"
      >V</a
      ><a name="16068"
      > </a
      ><a name="16069" class="Symbol"
      >&#8594;</a
      ><a name="16070"
      >
    </a
      ><a name="16075" class="Symbol"
      >(</a
      ><a name="16076" href="Stlc.html#3672" class="InductiveConstructor Operator"
      >&#955;[</a
      ><a name="16078"
      > </a
      ><a name="16079" href="Stlc.html#16050" class="Bound"
      >x</a
      ><a name="16080"
      > </a
      ><a name="16081" href="Stlc.html#3672" class="InductiveConstructor Operator"
      >&#8758;</a
      ><a name="16082"
      > </a
      ><a name="16083" href="Stlc.html#16052" class="Bound"
      >A</a
      ><a name="16084"
      > </a
      ><a name="16085" href="Stlc.html#3672" class="InductiveConstructor Operator"
      >]</a
      ><a name="16086"
      > </a
      ><a name="16087" href="Stlc.html#16054" class="Bound"
      >N</a
      ><a name="16088" class="Symbol"
      >)</a
      ><a name="16089"
      > </a
      ><a name="16090" href="Stlc.html#3708" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="16091"
      > </a
      ><a name="16092" href="Stlc.html#16056" class="Bound"
      >V</a
      ><a name="16093"
      > </a
      ><a name="16094" href="Stlc.html#15889" class="Datatype Operator"
      >&#10233;</a
      ><a name="16095"
      > </a
      ><a name="16096" href="Stlc.html#16054" class="Bound"
      >N</a
      ><a name="16097"
      > </a
      ><a name="16098" href="Stlc.html#12136" class="Function Operator"
      >[</a
      ><a name="16099"
      > </a
      ><a name="16100" href="Stlc.html#16050" class="Bound"
      >x</a
      ><a name="16101"
      > </a
      ><a name="16102" href="Stlc.html#12136" class="Function Operator"
      >:=</a
      ><a name="16104"
      > </a
      ><a name="16105" href="Stlc.html#16056" class="Bound"
      >V</a
      ><a name="16106"
      > </a
      ><a name="16107" href="Stlc.html#12136" class="Function Operator"
      >]</a
      ><a name="16108"
      >
  </a
      ><a name="16111" href="Stlc.html#16111" class="InductiveConstructor"
      >&#958;if</a
      ><a name="16114"
      > </a
      ><a name="16115" class="Symbol"
      >:</a
      ><a name="16116"
      > </a
      ><a name="16117" class="Symbol"
      >&#8704;</a
      ><a name="16118"
      > </a
      ><a name="16119" class="Symbol"
      >{</a
      ><a name="16120" href="Stlc.html#16120" class="Bound"
      >L</a
      ><a name="16121"
      > </a
      ><a name="16122" href="Stlc.html#16122" class="Bound"
      >L&#8242;</a
      ><a name="16124"
      > </a
      ><a name="16125" href="Stlc.html#16125" class="Bound"
      >M</a
      ><a name="16126"
      > </a
      ><a name="16127" href="Stlc.html#16127" class="Bound"
      >N</a
      ><a name="16128" class="Symbol"
      >}</a
      ><a name="16129"
      > </a
      ><a name="16130" class="Symbol"
      >&#8594;</a
      ><a name="16131"
      >
    </a
      ><a name="16136" href="Stlc.html#16120" class="Bound"
      >L</a
      ><a name="16137"
      > </a
      ><a name="16138" href="Stlc.html#15889" class="Datatype Operator"
      >&#10233;</a
      ><a name="16139"
      > </a
      ><a name="16140" href="Stlc.html#16122" class="Bound"
      >L&#8242;</a
      ><a name="16142"
      > </a
      ><a name="16143" class="Symbol"
      >&#8594;</a
      ><a name="16144"
      >    
    </a
      ><a name="16153" href="Stlc.html#3764" class="InductiveConstructor Operator"
      >if</a
      ><a name="16155"
      > </a
      ><a name="16156" href="Stlc.html#16120" class="Bound"
      >L</a
      ><a name="16157"
      > </a
      ><a name="16158" href="Stlc.html#3764" class="InductiveConstructor Operator"
      >then</a
      ><a name="16162"
      > </a
      ><a name="16163" href="Stlc.html#16125" class="Bound"
      >M</a
      ><a name="16164"
      > </a
      ><a name="16165" href="Stlc.html#3764" class="InductiveConstructor Operator"
      >else</a
      ><a name="16169"
      > </a
      ><a name="16170" href="Stlc.html#16127" class="Bound"
      >N</a
      ><a name="16171"
      > </a
      ><a name="16172" href="Stlc.html#15889" class="Datatype Operator"
      >&#10233;</a
      ><a name="16173"
      > </a
      ><a name="16174" href="Stlc.html#3764" class="InductiveConstructor Operator"
      >if</a
      ><a name="16176"
      > </a
      ><a name="16177" href="Stlc.html#16122" class="Bound"
      >L&#8242;</a
      ><a name="16179"
      > </a
      ><a name="16180" href="Stlc.html#3764" class="InductiveConstructor Operator"
      >then</a
      ><a name="16184"
      > </a
      ><a name="16185" href="Stlc.html#16125" class="Bound"
      >M</a
      ><a name="16186"
      > </a
      ><a name="16187" href="Stlc.html#3764" class="InductiveConstructor Operator"
      >else</a
      ><a name="16191"
      > </a
      ><a name="16192" href="Stlc.html#16127" class="Bound"
      >N</a
      ><a name="16193"
      >
  </a
      ><a name="16196" href="Stlc.html#16196" class="InductiveConstructor"
      >&#946;if-true</a
      ><a name="16204"
      > </a
      ><a name="16205" class="Symbol"
      >:</a
      ><a name="16206"
      > </a
      ><a name="16207" class="Symbol"
      >&#8704;</a
      ><a name="16208"
      > </a
      ><a name="16209" class="Symbol"
      >{</a
      ><a name="16210" href="Stlc.html#16210" class="Bound"
      >M</a
      ><a name="16211"
      > </a
      ><a name="16212" href="Stlc.html#16212" class="Bound"
      >N</a
      ><a name="16213" class="Symbol"
      >}</a
      ><a name="16214"
      > </a
      ><a name="16215" class="Symbol"
      >&#8594;</a
      ><a name="16216"
      >
    </a
      ><a name="16221" href="Stlc.html#3764" class="InductiveConstructor Operator"
      >if</a
      ><a name="16223"
      > </a
      ><a name="16224" href="Stlc.html#3735" class="InductiveConstructor"
      >true</a
      ><a name="16228"
      > </a
      ><a name="16229" href="Stlc.html#3764" class="InductiveConstructor Operator"
      >then</a
      ><a name="16233"
      > </a
      ><a name="16234" href="Stlc.html#16210" class="Bound"
      >M</a
      ><a name="16235"
      > </a
      ><a name="16236" href="Stlc.html#3764" class="InductiveConstructor Operator"
      >else</a
      ><a name="16240"
      > </a
      ><a name="16241" href="Stlc.html#16212" class="Bound"
      >N</a
      ><a name="16242"
      > </a
      ><a name="16243" href="Stlc.html#15889" class="Datatype Operator"
      >&#10233;</a
      ><a name="16244"
      > </a
      ><a name="16245" href="Stlc.html#16210" class="Bound"
      >M</a
      ><a name="16246"
      >
  </a
      ><a name="16249" href="Stlc.html#16249" class="InductiveConstructor"
      >&#946;if-false</a
      ><a name="16258"
      > </a
      ><a name="16259" class="Symbol"
      >:</a
      ><a name="16260"
      > </a
      ><a name="16261" class="Symbol"
      >&#8704;</a
      ><a name="16262"
      > </a
      ><a name="16263" class="Symbol"
      >{</a
      ><a name="16264" href="Stlc.html#16264" class="Bound"
      >M</a
      ><a name="16265"
      > </a
      ><a name="16266" href="Stlc.html#16266" class="Bound"
      >N</a
      ><a name="16267" class="Symbol"
      >}</a
      ><a name="16268"
      > </a
      ><a name="16269" class="Symbol"
      >&#8594;</a
      ><a name="16270"
      >
    </a
      ><a name="16275" href="Stlc.html#3764" class="InductiveConstructor Operator"
      >if</a
      ><a name="16277"
      > </a
      ><a name="16278" href="Stlc.html#3749" class="InductiveConstructor"
      >false</a
      ><a name="16283"
      > </a
      ><a name="16284" href="Stlc.html#3764" class="InductiveConstructor Operator"
      >then</a
      ><a name="16288"
      > </a
      ><a name="16289" href="Stlc.html#16264" class="Bound"
      >M</a
      ><a name="16290"
      > </a
      ><a name="16291" href="Stlc.html#3764" class="InductiveConstructor Operator"
      >else</a
      ><a name="16295"
      > </a
      ><a name="16296" href="Stlc.html#16266" class="Bound"
      >N</a
      ><a name="16297"
      > </a
      ><a name="16298" href="Stlc.html#15889" class="Datatype Operator"
      >&#10233;</a
      ><a name="16299"
      > </a
      ><a name="16300" href="Stlc.html#16266" class="Bound"
      >N</a
      >
{% endraw %}</pre>

#### Special characters

We use the following special characters

    ⟹  U+27F9: LONG RIGHTWARDS DOUBLE ARROW (\r6)
    ξ  U+03BE: GREEK SMALL LETTER XI (\Gx or \xi)
    β  U+03B2: GREEK SMALL LETTER BETA (\Gb or \beta)

#### Quiz

What does the following term step to?

    (λ[ x ∶ 𝔹 ⇒ 𝔹 ] ` x) · (λ [ x ∶ 𝔹 ] ` x)  ⟹  ???

1.  `` (λ [ x ∶ 𝔹 ] ` x) ``
2.  `` (λ[ x ∶ 𝔹 ⇒ 𝔹 ] ` x) ``
3.  `` (λ[ x ∶ 𝔹 ⇒ 𝔹 ] ` x) · (λ [ x ∶ 𝔹 ] ` x) ``

What does the following term step to?

    (λ[ x ∶ 𝔹 ⇒ 𝔹 ] ` x) · ((λ[ x ∶ 𝔹 ⇒ 𝔹 ] ` x) (λ [ x ∶ 𝔹 ] ` x))  ⟹  ???

1.  `` (λ [ x ∶ 𝔹 ] ` x) ``
2.  `` (λ[ x ∶ 𝔹 ⇒ 𝔹 ] ` x) ``
3.  `` (λ[ x ∶ 𝔹 ⇒ 𝔹 ] ` x) · (λ [ x ∶ 𝔹 ] ` x) ``

What does the following term step to?  (Where `not` is as defined above.)

    not · true  ⟹  ???

1.  `` if ` x then false else true ``
2.  `` if true then false else true ``
3.  `` true ``
4.  `` false ``

What does the following term step to?  (Where `two` and `not` are as defined above.)

    two · not · true  ⟹  ???

1.  `` not · (not · true) ``
2.  `` (λ[ x ∶ 𝔹 ] not · (not · ` x)) · true ``
4.  `` true ``
5.  `` false ``

## Reflexive and transitive closure

A single step is only part of the story. In general, we wish to repeatedly
step a closed term until it reduces to a value.  We do this by defining
the reflexive and transitive closure `⟹*` of the step function `⟹`.
In an informal presentation of the formal semantics, the rules
are written as follows.

    ------- done
    M ⟹* M

    L ⟹ M
    M ⟹* N
    ------- step
    L ⟹* N

Here it is formalised in Agda.

<pre class="Agda">{% raw %}
<a name="17874" class="Keyword"
      >infix</a
      ><a name="17879"
      > </a
      ><a name="17880" class="Number"
      >10</a
      ><a name="17882"
      > </a
      ><a name="17883" href="Stlc.html#17923" class="Datatype Operator"
      >_&#10233;*_</a
      ><a name="17887"
      > 
</a
      ><a name="17889" class="Keyword"
      >infixr</a
      ><a name="17895"
      > </a
      ><a name="17896" class="Number"
      >2</a
      ><a name="17897"
      > </a
      ><a name="17898" href="Stlc.html#17976" class="InductiveConstructor Operator"
      >_&#10233;&#10216;_&#10217;_</a
      ><a name="17904"
      >
</a
      ><a name="17905" class="Keyword"
      >infix</a
      ><a name="17910"
      >  </a
      ><a name="17912" class="Number"
      >3</a
      ><a name="17913"
      > </a
      ><a name="17914" href="Stlc.html#17956" class="InductiveConstructor Operator"
      >_&#8718;</a
      ><a name="17916"
      >

</a
      ><a name="17918" class="Keyword"
      >data</a
      ><a name="17922"
      > </a
      ><a name="17923" href="Stlc.html#17923" class="Datatype Operator"
      >_&#10233;*_</a
      ><a name="17927"
      > </a
      ><a name="17928" class="Symbol"
      >:</a
      ><a name="17929"
      > </a
      ><a name="17930" href="Stlc.html#3637" class="Datatype"
      >Term</a
      ><a name="17934"
      > </a
      ><a name="17935" class="Symbol"
      >&#8594;</a
      ><a name="17936"
      > </a
      ><a name="17937" href="Stlc.html#3637" class="Datatype"
      >Term</a
      ><a name="17941"
      > </a
      ><a name="17942" class="Symbol"
      >&#8594;</a
      ><a name="17943"
      > </a
      ><a name="17944" class="PrimitiveType"
      >Set</a
      ><a name="17947"
      > </a
      ><a name="17948" class="Keyword"
      >where</a
      ><a name="17953"
      >
  </a
      ><a name="17956" href="Stlc.html#17956" class="InductiveConstructor Operator"
      >_&#8718;</a
      ><a name="17958"
      > </a
      ><a name="17959" class="Symbol"
      >:</a
      ><a name="17960"
      > </a
      ><a name="17961" class="Symbol"
      >&#8704;</a
      ><a name="17962"
      > </a
      ><a name="17963" href="Stlc.html#17963" class="Bound"
      >M</a
      ><a name="17964"
      > </a
      ><a name="17965" class="Symbol"
      >&#8594;</a
      ><a name="17966"
      > </a
      ><a name="17967" href="Stlc.html#17963" class="Bound"
      >M</a
      ><a name="17968"
      > </a
      ><a name="17969" href="Stlc.html#17923" class="Datatype Operator"
      >&#10233;*</a
      ><a name="17971"
      > </a
      ><a name="17972" href="Stlc.html#17963" class="Bound"
      >M</a
      ><a name="17973"
      >
  </a
      ><a name="17976" href="Stlc.html#17976" class="InductiveConstructor Operator"
      >_&#10233;&#10216;_&#10217;_</a
      ><a name="17982"
      > </a
      ><a name="17983" class="Symbol"
      >:</a
      ><a name="17984"
      > </a
      ><a name="17985" class="Symbol"
      >&#8704;</a
      ><a name="17986"
      > </a
      ><a name="17987" href="Stlc.html#17987" class="Bound"
      >L</a
      ><a name="17988"
      > </a
      ><a name="17989" class="Symbol"
      >{</a
      ><a name="17990" href="Stlc.html#17990" class="Bound"
      >M</a
      ><a name="17991"
      > </a
      ><a name="17992" href="Stlc.html#17992" class="Bound"
      >N</a
      ><a name="17993" class="Symbol"
      >}</a
      ><a name="17994"
      > </a
      ><a name="17995" class="Symbol"
      >&#8594;</a
      ><a name="17996"
      > </a
      ><a name="17997" href="Stlc.html#17987" class="Bound"
      >L</a
      ><a name="17998"
      > </a
      ><a name="17999" href="Stlc.html#15889" class="Datatype Operator"
      >&#10233;</a
      ><a name="18000"
      > </a
      ><a name="18001" href="Stlc.html#17990" class="Bound"
      >M</a
      ><a name="18002"
      > </a
      ><a name="18003" class="Symbol"
      >&#8594;</a
      ><a name="18004"
      > </a
      ><a name="18005" href="Stlc.html#17990" class="Bound"
      >M</a
      ><a name="18006"
      > </a
      ><a name="18007" href="Stlc.html#17923" class="Datatype Operator"
      >&#10233;*</a
      ><a name="18009"
      > </a
      ><a name="18010" href="Stlc.html#17992" class="Bound"
      >N</a
      ><a name="18011"
      > </a
      ><a name="18012" class="Symbol"
      >&#8594;</a
      ><a name="18013"
      > </a
      ><a name="18014" href="Stlc.html#17987" class="Bound"
      >L</a
      ><a name="18015"
      > </a
      ><a name="18016" href="Stlc.html#17923" class="Datatype Operator"
      >&#10233;*</a
      ><a name="18018"
      > </a
      ><a name="18019" href="Stlc.html#17992" class="Bound"
      >N</a
      >
{% endraw %}</pre>

We can read this as follows.

* From term `M`, we can take no steps, giving `M ∎` of type `M ⟹* M`.

* From term `L` we can take a single step `L⟹M` of type `L ⟹ M`
  followed by zero or more steps `M⟹*N` of type `M ⟹* N`,
  giving `L ⟨ L⟹M ⟩ M⟹*N` of type `L ⟹* N`.

The names of the two clauses in the definition of reflexive
and transitive closure have been chosen to allow us to lay
out example reductions in an appealing way.

<pre class="Agda">{% raw %}
<a name="18480" href="Stlc.html#18480" class="Function"
      >reduction&#8321;</a
      ><a name="18490"
      > </a
      ><a name="18491" class="Symbol"
      >:</a
      ><a name="18492"
      > </a
      ><a name="18493" href="Stlc.html#5722" class="Function"
      >not</a
      ><a name="18496"
      > </a
      ><a name="18497" href="Stlc.html#3708" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="18498"
      > </a
      ><a name="18499" href="Stlc.html#3735" class="InductiveConstructor"
      >true</a
      ><a name="18503"
      > </a
      ><a name="18504" href="Stlc.html#17923" class="Datatype Operator"
      >&#10233;*</a
      ><a name="18506"
      > </a
      ><a name="18507" href="Stlc.html#3749" class="InductiveConstructor"
      >false</a
      ><a name="18512"
      >
</a
      ><a name="18513" href="Stlc.html#18480" class="Function"
      >reduction&#8321;</a
      ><a name="18523"
      > </a
      ><a name="18524" class="Symbol"
      >=</a
      ><a name="18525"
      >
    </a
      ><a name="18530" href="Stlc.html#5722" class="Function"
      >not</a
      ><a name="18533"
      > </a
      ><a name="18534" href="Stlc.html#3708" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="18535"
      > </a
      ><a name="18536" href="Stlc.html#3735" class="InductiveConstructor"
      >true</a
      ><a name="18540"
      >
  </a
      ><a name="18543" href="Stlc.html#17976" class="InductiveConstructor Operator"
      >&#10233;&#10216;</a
      ><a name="18545"
      > </a
      ><a name="18546" href="Stlc.html#16041" class="InductiveConstructor"
      >&#946;&#955;&#183;</a
      ><a name="18549"
      > </a
      ><a name="18550" href="Stlc.html#9668" class="InductiveConstructor"
      >value-true</a
      ><a name="18560"
      > </a
      ><a name="18561" href="Stlc.html#17976" class="InductiveConstructor Operator"
      >&#10217;</a
      ><a name="18562"
      >
    </a
      ><a name="18567" href="Stlc.html#3764" class="InductiveConstructor Operator"
      >if</a
      ><a name="18569"
      > </a
      ><a name="18570" href="Stlc.html#3735" class="InductiveConstructor"
      >true</a
      ><a name="18574"
      > </a
      ><a name="18575" href="Stlc.html#3764" class="InductiveConstructor Operator"
      >then</a
      ><a name="18579"
      > </a
      ><a name="18580" href="Stlc.html#3749" class="InductiveConstructor"
      >false</a
      ><a name="18585"
      > </a
      ><a name="18586" href="Stlc.html#3764" class="InductiveConstructor Operator"
      >else</a
      ><a name="18590"
      > </a
      ><a name="18591" href="Stlc.html#3735" class="InductiveConstructor"
      >true</a
      ><a name="18595"
      >
  </a
      ><a name="18598" href="Stlc.html#17976" class="InductiveConstructor Operator"
      >&#10233;&#10216;</a
      ><a name="18600"
      > </a
      ><a name="18601" href="Stlc.html#16196" class="InductiveConstructor"
      >&#946;if-true</a
      ><a name="18609"
      > </a
      ><a name="18610" href="Stlc.html#17976" class="InductiveConstructor Operator"
      >&#10217;</a
      ><a name="18611"
      >
    </a
      ><a name="18616" href="Stlc.html#3749" class="InductiveConstructor"
      >false</a
      ><a name="18621"
      >
  </a
      ><a name="18624" href="Stlc.html#17956" class="InductiveConstructor Operator"
      >&#8718;</a
      ><a name="18625"
      >

</a
      ><a name="18627" href="Stlc.html#18627" class="Function"
      >reduction&#8322;</a
      ><a name="18637"
      > </a
      ><a name="18638" class="Symbol"
      >:</a
      ><a name="18639"
      > </a
      ><a name="18640" href="Stlc.html#5726" class="Function"
      >two</a
      ><a name="18643"
      > </a
      ><a name="18644" href="Stlc.html#3708" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="18645"
      > </a
      ><a name="18646" href="Stlc.html#5722" class="Function"
      >not</a
      ><a name="18649"
      > </a
      ><a name="18650" href="Stlc.html#3708" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="18651"
      > </a
      ><a name="18652" href="Stlc.html#3735" class="InductiveConstructor"
      >true</a
      ><a name="18656"
      > </a
      ><a name="18657" href="Stlc.html#17923" class="Datatype Operator"
      >&#10233;*</a
      ><a name="18659"
      > </a
      ><a name="18660" href="Stlc.html#3735" class="InductiveConstructor"
      >true</a
      ><a name="18664"
      >
</a
      ><a name="18665" href="Stlc.html#18627" class="Function"
      >reduction&#8322;</a
      ><a name="18675"
      > </a
      ><a name="18676" class="Symbol"
      >=</a
      ><a name="18677"
      >
    </a
      ><a name="18682" href="Stlc.html#5726" class="Function"
      >two</a
      ><a name="18685"
      > </a
      ><a name="18686" href="Stlc.html#3708" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="18687"
      > </a
      ><a name="18688" href="Stlc.html#5722" class="Function"
      >not</a
      ><a name="18691"
      > </a
      ><a name="18692" href="Stlc.html#3708" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="18693"
      > </a
      ><a name="18694" href="Stlc.html#3735" class="InductiveConstructor"
      >true</a
      ><a name="18698"
      >
  </a
      ><a name="18701" href="Stlc.html#17976" class="InductiveConstructor Operator"
      >&#10233;&#10216;</a
      ><a name="18703"
      > </a
      ><a name="18704" href="Stlc.html#15921" class="InductiveConstructor"
      >&#958;&#183;&#8321;</a
      ><a name="18707"
      > </a
      ><a name="18708" class="Symbol"
      >(</a
      ><a name="18709" href="Stlc.html#16041" class="InductiveConstructor"
      >&#946;&#955;&#183;</a
      ><a name="18712"
      > </a
      ><a name="18713" href="Stlc.html#9619" class="InductiveConstructor"
      >value-&#955;</a
      ><a name="18720" class="Symbol"
      >)</a
      ><a name="18721"
      > </a
      ><a name="18722" href="Stlc.html#17976" class="InductiveConstructor Operator"
      >&#10217;</a
      ><a name="18723"
      >
    </a
      ><a name="18728" class="Symbol"
      >(</a
      ><a name="18729" href="Stlc.html#3672" class="InductiveConstructor Operator"
      >&#955;[</a
      ><a name="18731"
      > </a
      ><a name="18732" href="Stlc.html#5679" class="Function"
      >x</a
      ><a name="18733"
      > </a
      ><a name="18734" href="Stlc.html#3672" class="InductiveConstructor Operator"
      >&#8758;</a
      ><a name="18735"
      > </a
      ><a name="18736" href="Stlc.html#2610" class="InductiveConstructor"
      >&#120121;</a
      ><a name="18737"
      > </a
      ><a name="18738" href="Stlc.html#3672" class="InductiveConstructor Operator"
      >]</a
      ><a name="18739"
      > </a
      ><a name="18740" href="Stlc.html#5722" class="Function"
      >not</a
      ><a name="18743"
      > </a
      ><a name="18744" href="Stlc.html#3708" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="18745"
      > </a
      ><a name="18746" class="Symbol"
      >(</a
      ><a name="18747" href="Stlc.html#5722" class="Function"
      >not</a
      ><a name="18750"
      > </a
      ><a name="18751" href="Stlc.html#3708" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="18752"
      > </a
      ><a name="18753" href="Stlc.html#3656" class="InductiveConstructor"
      >`</a
      ><a name="18754"
      > </a
      ><a name="18755" href="Stlc.html#5679" class="Function"
      >x</a
      ><a name="18756" class="Symbol"
      >))</a
      ><a name="18758"
      > </a
      ><a name="18759" href="Stlc.html#3708" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="18760"
      > </a
      ><a name="18761" href="Stlc.html#3735" class="InductiveConstructor"
      >true</a
      ><a name="18765"
      >
  </a
      ><a name="18768" href="Stlc.html#17976" class="InductiveConstructor Operator"
      >&#10233;&#10216;</a
      ><a name="18770"
      > </a
      ><a name="18771" href="Stlc.html#16041" class="InductiveConstructor"
      >&#946;&#955;&#183;</a
      ><a name="18774"
      > </a
      ><a name="18775" href="Stlc.html#9668" class="InductiveConstructor"
      >value-true</a
      ><a name="18785"
      > </a
      ><a name="18786" href="Stlc.html#17976" class="InductiveConstructor Operator"
      >&#10217;</a
      ><a name="18787"
      >
    </a
      ><a name="18792" href="Stlc.html#5722" class="Function"
      >not</a
      ><a name="18795"
      > </a
      ><a name="18796" href="Stlc.html#3708" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="18797"
      > </a
      ><a name="18798" class="Symbol"
      >(</a
      ><a name="18799" href="Stlc.html#5722" class="Function"
      >not</a
      ><a name="18802"
      > </a
      ><a name="18803" href="Stlc.html#3708" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="18804"
      > </a
      ><a name="18805" href="Stlc.html#3735" class="InductiveConstructor"
      >true</a
      ><a name="18809" class="Symbol"
      >)</a
      ><a name="18810"
      >
  </a
      ><a name="18813" href="Stlc.html#17976" class="InductiveConstructor Operator"
      >&#10233;&#10216;</a
      ><a name="18815"
      > </a
      ><a name="18816" href="Stlc.html#15974" class="InductiveConstructor"
      >&#958;&#183;&#8322;</a
      ><a name="18819"
      > </a
      ><a name="18820" href="Stlc.html#9619" class="InductiveConstructor"
      >value-&#955;</a
      ><a name="18827"
      > </a
      ><a name="18828" class="Symbol"
      >(</a
      ><a name="18829" href="Stlc.html#16041" class="InductiveConstructor"
      >&#946;&#955;&#183;</a
      ><a name="18832"
      > </a
      ><a name="18833" href="Stlc.html#9668" class="InductiveConstructor"
      >value-true</a
      ><a name="18843" class="Symbol"
      >)</a
      ><a name="18844"
      > </a
      ><a name="18845" href="Stlc.html#17976" class="InductiveConstructor Operator"
      >&#10217;</a
      ><a name="18846"
      >
    </a
      ><a name="18851" href="Stlc.html#5722" class="Function"
      >not</a
      ><a name="18854"
      > </a
      ><a name="18855" href="Stlc.html#3708" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="18856"
      > </a
      ><a name="18857" class="Symbol"
      >(</a
      ><a name="18858" href="Stlc.html#3764" class="InductiveConstructor Operator"
      >if</a
      ><a name="18860"
      > </a
      ><a name="18861" href="Stlc.html#3735" class="InductiveConstructor"
      >true</a
      ><a name="18865"
      > </a
      ><a name="18866" href="Stlc.html#3764" class="InductiveConstructor Operator"
      >then</a
      ><a name="18870"
      > </a
      ><a name="18871" href="Stlc.html#3749" class="InductiveConstructor"
      >false</a
      ><a name="18876"
      > </a
      ><a name="18877" href="Stlc.html#3764" class="InductiveConstructor Operator"
      >else</a
      ><a name="18881"
      > </a
      ><a name="18882" href="Stlc.html#3735" class="InductiveConstructor"
      >true</a
      ><a name="18886" class="Symbol"
      >)</a
      ><a name="18887"
      >
  </a
      ><a name="18890" href="Stlc.html#17976" class="InductiveConstructor Operator"
      >&#10233;&#10216;</a
      ><a name="18892"
      > </a
      ><a name="18893" href="Stlc.html#15974" class="InductiveConstructor"
      >&#958;&#183;&#8322;</a
      ><a name="18896"
      > </a
      ><a name="18897" href="Stlc.html#9619" class="InductiveConstructor"
      >value-&#955;</a
      ><a name="18904"
      > </a
      ><a name="18905" href="Stlc.html#16196" class="InductiveConstructor"
      >&#946;if-true</a
      ><a name="18913"
      >  </a
      ><a name="18915" href="Stlc.html#17976" class="InductiveConstructor Operator"
      >&#10217;</a
      ><a name="18916"
      >
    </a
      ><a name="18921" href="Stlc.html#5722" class="Function"
      >not</a
      ><a name="18924"
      > </a
      ><a name="18925" href="Stlc.html#3708" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="18926"
      > </a
      ><a name="18927" href="Stlc.html#3749" class="InductiveConstructor"
      >false</a
      ><a name="18932"
      >
  </a
      ><a name="18935" href="Stlc.html#17976" class="InductiveConstructor Operator"
      >&#10233;&#10216;</a
      ><a name="18937"
      > </a
      ><a name="18938" href="Stlc.html#16041" class="InductiveConstructor"
      >&#946;&#955;&#183;</a
      ><a name="18941"
      > </a
      ><a name="18942" href="Stlc.html#9695" class="InductiveConstructor"
      >value-false</a
      ><a name="18953"
      > </a
      ><a name="18954" href="Stlc.html#17976" class="InductiveConstructor Operator"
      >&#10217;</a
      ><a name="18955"
      >
    </a
      ><a name="18960" href="Stlc.html#3764" class="InductiveConstructor Operator"
      >if</a
      ><a name="18962"
      > </a
      ><a name="18963" href="Stlc.html#3749" class="InductiveConstructor"
      >false</a
      ><a name="18968"
      > </a
      ><a name="18969" href="Stlc.html#3764" class="InductiveConstructor Operator"
      >then</a
      ><a name="18973"
      > </a
      ><a name="18974" href="Stlc.html#3749" class="InductiveConstructor"
      >false</a
      ><a name="18979"
      > </a
      ><a name="18980" href="Stlc.html#3764" class="InductiveConstructor Operator"
      >else</a
      ><a name="18984"
      > </a
      ><a name="18985" href="Stlc.html#3735" class="InductiveConstructor"
      >true</a
      ><a name="18989"
      >
  </a
      ><a name="18992" href="Stlc.html#17976" class="InductiveConstructor Operator"
      >&#10233;&#10216;</a
      ><a name="18994"
      > </a
      ><a name="18995" href="Stlc.html#16249" class="InductiveConstructor"
      >&#946;if-false</a
      ><a name="19004"
      > </a
      ><a name="19005" href="Stlc.html#17976" class="InductiveConstructor Operator"
      >&#10217;</a
      ><a name="19006"
      >
    </a
      ><a name="19011" href="Stlc.html#3735" class="InductiveConstructor"
      >true</a
      ><a name="19015"
      >
  </a
      ><a name="19018" href="Stlc.html#17956" class="InductiveConstructor Operator"
      >&#8718;</a
      >
{% endraw %}</pre>

<!--
Much of the above, though not all, can be filled in using C-c C-r and C-c C-s.
-->

#### Special characters

We use the following special characters

    ∎  U+220E: END OF PROOF (\qed)
    ⟨  U+27E8: MATHEMATICAL LEFT ANGLE BRACKET (\<)
    ⟩  U+27E9: MATHEMATICAL RIGHT ANGLE BRACKET (\>)

## Typing

While reduction considers only closed terms, typing must
consider terms with free variables.  To type a term,
we must first type its subterms, and in particular in the
body of an abstraction its bound variable may appear free.

In general, we use typing _judgements_ of the form

    Γ ⊢ M ∶ A

which asserts in type environment `Γ` that term `M` has type `A`.
Environment `Γ` provides types for all the free variables in `M`.

Here are three examples. 

* `` ∅ , f ∶ 𝔹 ⇒ 𝔹 , x ∶ 𝔹 ⊢ ` f · (` f · ` x) ∶  𝔹 ``
* `` ∅ , f ∶ 𝔹 ⇒ 𝔹 ⊢ (λ[ x ∶ 𝔹 ] ` f · (` f · ` x)) ∶  𝔹 ⇒ 𝔹 ``
* `` ∅ ⊢ (λ[ f ∶ 𝔹 ⇒ 𝔹 ] λ[ x ∶ 𝔹 ] ` f · (` f · ` x)) ∶  (𝔹 ⇒ 𝔹) ⇒ 𝔹 ⇒ 𝔹 ``

Environments are partial maps from identifiers to types, built using `∅`
for the empty map, and `Γ , x ∶ A` for the map that extends
environment `Γ` by mapping variable `x` to type `A`.

In an informal presentation of the formal semantics, 
the rules for typing are written as follows.

    Γ x ≡ A
    ----------- Ax
    Γ ⊢ ` x ∶ A

    Γ , x ∶ A ⊢ N ∶ B
    ------------------------ ⇒-I
    Γ ⊢ λ[ x ∶ A ] N ∶ A ⇒ B

    Γ ⊢ L ∶ A ⇒ B
    Γ ⊢ M ∶ A
    -------------- ⇒-E
    Γ ⊢ L · M ∶ B

    ------------- 𝔹-I₁
    Γ ⊢ true ∶ 𝔹

    -------------- 𝔹-I₂
    Γ ⊢ false ∶ 𝔹

    Γ ⊢ L : 𝔹
    Γ ⊢ M ∶ A
    Γ ⊢ N ∶ A
    -------------------------- 𝔹-E
    Γ ⊢ if L then M else N ∶ A

As we will show later, the rules are deterministic, in that
at most one rule applies to every term. 

The proof rules come in pairs, with rules to introduce and to
eliminate each connective, labeled `-I` and `-E`, respectively. As we
read the rules from top to bottom, introduction and elimination rules
do what they say on the tin: the first _introduces_ a formula for the
connective, which appears in the conclusion but not in the premises;
while the second _eliminates_ a formula for the connective, which appears in
a premise but not in the conclusion. An introduction rule describes
how to construct a value of the type (abstractions yield functions,
true and false yield booleans), while an elimination rule describes
how to deconstruct a value of the given type (applications use
functions, conditionals use booleans).

Here are the above rules formalised in Agda.

<pre class="Agda">{% raw %}
<a name="21564" href="Stlc.html#21564" class="Function"
      >Context</a
      ><a name="21571"
      > </a
      ><a name="21572" class="Symbol"
      >:</a
      ><a name="21573"
      > </a
      ><a name="21574" class="PrimitiveType"
      >Set</a
      ><a name="21577"
      >
</a
      ><a name="21578" href="Stlc.html#21564" class="Function"
      >Context</a
      ><a name="21585"
      > </a
      ><a name="21586" class="Symbol"
      >=</a
      ><a name="21587"
      > </a
      ><a name="21588" href="Maps.html#10132" class="Function"
      >PartialMap</a
      ><a name="21598"
      > </a
      ><a name="21599" href="Stlc.html#2564" class="Datatype"
      >Type</a
      ><a name="21603"
      >

</a
      ><a name="21605" class="Keyword"
      >infix</a
      ><a name="21610"
      > </a
      ><a name="21611" class="Number"
      >10</a
      ><a name="21613"
      > </a
      ><a name="21614" href="Stlc.html#21626" class="Datatype Operator"
      >_&#8866;_&#8758;_</a
      ><a name="21619"
      >

</a
      ><a name="21621" class="Keyword"
      >data</a
      ><a name="21625"
      > </a
      ><a name="21626" href="Stlc.html#21626" class="Datatype Operator"
      >_&#8866;_&#8758;_</a
      ><a name="21631"
      > </a
      ><a name="21632" class="Symbol"
      >:</a
      ><a name="21633"
      > </a
      ><a name="21634" href="Stlc.html#21564" class="Function"
      >Context</a
      ><a name="21641"
      > </a
      ><a name="21642" class="Symbol"
      >&#8594;</a
      ><a name="21643"
      > </a
      ><a name="21644" href="Stlc.html#3637" class="Datatype"
      >Term</a
      ><a name="21648"
      > </a
      ><a name="21649" class="Symbol"
      >&#8594;</a
      ><a name="21650"
      > </a
      ><a name="21651" href="Stlc.html#2564" class="Datatype"
      >Type</a
      ><a name="21655"
      > </a
      ><a name="21656" class="Symbol"
      >&#8594;</a
      ><a name="21657"
      > </a
      ><a name="21658" class="PrimitiveType"
      >Set</a
      ><a name="21661"
      > </a
      ><a name="21662" class="Keyword"
      >where</a
      ><a name="21667"
      >
  </a
      ><a name="21670" href="Stlc.html#21670" class="InductiveConstructor"
      >Ax</a
      ><a name="21672"
      > </a
      ><a name="21673" class="Symbol"
      >:</a
      ><a name="21674"
      > </a
      ><a name="21675" class="Symbol"
      >&#8704;</a
      ><a name="21676"
      > </a
      ><a name="21677" class="Symbol"
      >{</a
      ><a name="21678" href="Stlc.html#21678" class="Bound"
      >&#915;</a
      ><a name="21679"
      > </a
      ><a name="21680" href="Stlc.html#21680" class="Bound"
      >x</a
      ><a name="21681"
      > </a
      ><a name="21682" href="Stlc.html#21682" class="Bound"
      >A</a
      ><a name="21683" class="Symbol"
      >}</a
      ><a name="21684"
      > </a
      ><a name="21685" class="Symbol"
      >&#8594;</a
      ><a name="21686"
      >
    </a
      ><a name="21691" href="Stlc.html#21678" class="Bound"
      >&#915;</a
      ><a name="21692"
      > </a
      ><a name="21693" href="Stlc.html#21680" class="Bound"
      >x</a
      ><a name="21694"
      > </a
      ><a name="21695" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="21696"
      > </a
      ><a name="21697" href="https://agda.github.io/agda-stdlib/Data.Maybe.Base.html#373" class="InductiveConstructor"
      >just</a
      ><a name="21701"
      > </a
      ><a name="21702" href="Stlc.html#21682" class="Bound"
      >A</a
      ><a name="21703"
      > </a
      ><a name="21704" class="Symbol"
      >&#8594;</a
      ><a name="21705"
      >
    </a
      ><a name="21710" href="Stlc.html#21678" class="Bound"
      >&#915;</a
      ><a name="21711"
      > </a
      ><a name="21712" href="Stlc.html#21626" class="Datatype Operator"
      >&#8866;</a
      ><a name="21713"
      > </a
      ><a name="21714" href="Stlc.html#3656" class="InductiveConstructor"
      >`</a
      ><a name="21715"
      > </a
      ><a name="21716" href="Stlc.html#21680" class="Bound"
      >x</a
      ><a name="21717"
      > </a
      ><a name="21718" href="Stlc.html#21626" class="Datatype Operator"
      >&#8758;</a
      ><a name="21719"
      > </a
      ><a name="21720" href="Stlc.html#21682" class="Bound"
      >A</a
      ><a name="21721"
      >
  </a
      ><a name="21724" href="Stlc.html#21724" class="InductiveConstructor"
      >&#8658;-I</a
      ><a name="21727"
      > </a
      ><a name="21728" class="Symbol"
      >:</a
      ><a name="21729"
      > </a
      ><a name="21730" class="Symbol"
      >&#8704;</a
      ><a name="21731"
      > </a
      ><a name="21732" class="Symbol"
      >{</a
      ><a name="21733" href="Stlc.html#21733" class="Bound"
      >&#915;</a
      ><a name="21734"
      > </a
      ><a name="21735" href="Stlc.html#21735" class="Bound"
      >x</a
      ><a name="21736"
      > </a
      ><a name="21737" href="Stlc.html#21737" class="Bound"
      >N</a
      ><a name="21738"
      > </a
      ><a name="21739" href="Stlc.html#21739" class="Bound"
      >A</a
      ><a name="21740"
      > </a
      ><a name="21741" href="Stlc.html#21741" class="Bound"
      >B</a
      ><a name="21742" class="Symbol"
      >}</a
      ><a name="21743"
      > </a
      ><a name="21744" class="Symbol"
      >&#8594;</a
      ><a name="21745"
      >
    </a
      ><a name="21750" href="Stlc.html#21733" class="Bound"
      >&#915;</a
      ><a name="21751"
      > </a
      ><a name="21752" href="Maps.html#10368" class="Function Operator"
      >,</a
      ><a name="21753"
      > </a
      ><a name="21754" href="Stlc.html#21735" class="Bound"
      >x</a
      ><a name="21755"
      > </a
      ><a name="21756" href="Maps.html#10368" class="Function Operator"
      >&#8758;</a
      ><a name="21757"
      > </a
      ><a name="21758" href="Stlc.html#21739" class="Bound"
      >A</a
      ><a name="21759"
      > </a
      ><a name="21760" href="Stlc.html#21626" class="Datatype Operator"
      >&#8866;</a
      ><a name="21761"
      > </a
      ><a name="21762" href="Stlc.html#21737" class="Bound"
      >N</a
      ><a name="21763"
      > </a
      ><a name="21764" href="Stlc.html#21626" class="Datatype Operator"
      >&#8758;</a
      ><a name="21765"
      > </a
      ><a name="21766" href="Stlc.html#21741" class="Bound"
      >B</a
      ><a name="21767"
      > </a
      ><a name="21768" class="Symbol"
      >&#8594;</a
      ><a name="21769"
      >
    </a
      ><a name="21774" href="Stlc.html#21733" class="Bound"
      >&#915;</a
      ><a name="21775"
      > </a
      ><a name="21776" href="Stlc.html#21626" class="Datatype Operator"
      >&#8866;</a
      ><a name="21777"
      > </a
      ><a name="21778" href="Stlc.html#3672" class="InductiveConstructor Operator"
      >&#955;[</a
      ><a name="21780"
      > </a
      ><a name="21781" href="Stlc.html#21735" class="Bound"
      >x</a
      ><a name="21782"
      > </a
      ><a name="21783" href="Stlc.html#3672" class="InductiveConstructor Operator"
      >&#8758;</a
      ><a name="21784"
      > </a
      ><a name="21785" href="Stlc.html#21739" class="Bound"
      >A</a
      ><a name="21786"
      > </a
      ><a name="21787" href="Stlc.html#3672" class="InductiveConstructor Operator"
      >]</a
      ><a name="21788"
      > </a
      ><a name="21789" href="Stlc.html#21737" class="Bound"
      >N</a
      ><a name="21790"
      > </a
      ><a name="21791" href="Stlc.html#21626" class="Datatype Operator"
      >&#8758;</a
      ><a name="21792"
      > </a
      ><a name="21793" href="Stlc.html#21739" class="Bound"
      >A</a
      ><a name="21794"
      > </a
      ><a name="21795" href="Stlc.html#2583" class="InductiveConstructor Operator"
      >&#8658;</a
      ><a name="21796"
      > </a
      ><a name="21797" href="Stlc.html#21741" class="Bound"
      >B</a
      ><a name="21798"
      >
  </a
      ><a name="21801" href="Stlc.html#21801" class="InductiveConstructor"
      >&#8658;-E</a
      ><a name="21804"
      > </a
      ><a name="21805" class="Symbol"
      >:</a
      ><a name="21806"
      > </a
      ><a name="21807" class="Symbol"
      >&#8704;</a
      ><a name="21808"
      > </a
      ><a name="21809" class="Symbol"
      >{</a
      ><a name="21810" href="Stlc.html#21810" class="Bound"
      >&#915;</a
      ><a name="21811"
      > </a
      ><a name="21812" href="Stlc.html#21812" class="Bound"
      >L</a
      ><a name="21813"
      > </a
      ><a name="21814" href="Stlc.html#21814" class="Bound"
      >M</a
      ><a name="21815"
      > </a
      ><a name="21816" href="Stlc.html#21816" class="Bound"
      >A</a
      ><a name="21817"
      > </a
      ><a name="21818" href="Stlc.html#21818" class="Bound"
      >B</a
      ><a name="21819" class="Symbol"
      >}</a
      ><a name="21820"
      > </a
      ><a name="21821" class="Symbol"
      >&#8594;</a
      ><a name="21822"
      >
    </a
      ><a name="21827" href="Stlc.html#21810" class="Bound"
      >&#915;</a
      ><a name="21828"
      > </a
      ><a name="21829" href="Stlc.html#21626" class="Datatype Operator"
      >&#8866;</a
      ><a name="21830"
      > </a
      ><a name="21831" href="Stlc.html#21812" class="Bound"
      >L</a
      ><a name="21832"
      > </a
      ><a name="21833" href="Stlc.html#21626" class="Datatype Operator"
      >&#8758;</a
      ><a name="21834"
      > </a
      ><a name="21835" href="Stlc.html#21816" class="Bound"
      >A</a
      ><a name="21836"
      > </a
      ><a name="21837" href="Stlc.html#2583" class="InductiveConstructor Operator"
      >&#8658;</a
      ><a name="21838"
      > </a
      ><a name="21839" href="Stlc.html#21818" class="Bound"
      >B</a
      ><a name="21840"
      > </a
      ><a name="21841" class="Symbol"
      >&#8594;</a
      ><a name="21842"
      >
    </a
      ><a name="21847" href="Stlc.html#21810" class="Bound"
      >&#915;</a
      ><a name="21848"
      > </a
      ><a name="21849" href="Stlc.html#21626" class="Datatype Operator"
      >&#8866;</a
      ><a name="21850"
      > </a
      ><a name="21851" href="Stlc.html#21814" class="Bound"
      >M</a
      ><a name="21852"
      > </a
      ><a name="21853" href="Stlc.html#21626" class="Datatype Operator"
      >&#8758;</a
      ><a name="21854"
      > </a
      ><a name="21855" href="Stlc.html#21816" class="Bound"
      >A</a
      ><a name="21856"
      > </a
      ><a name="21857" class="Symbol"
      >&#8594;</a
      ><a name="21858"
      >
    </a
      ><a name="21863" href="Stlc.html#21810" class="Bound"
      >&#915;</a
      ><a name="21864"
      > </a
      ><a name="21865" href="Stlc.html#21626" class="Datatype Operator"
      >&#8866;</a
      ><a name="21866"
      > </a
      ><a name="21867" href="Stlc.html#21812" class="Bound"
      >L</a
      ><a name="21868"
      > </a
      ><a name="21869" href="Stlc.html#3708" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="21870"
      > </a
      ><a name="21871" href="Stlc.html#21814" class="Bound"
      >M</a
      ><a name="21872"
      > </a
      ><a name="21873" href="Stlc.html#21626" class="Datatype Operator"
      >&#8758;</a
      ><a name="21874"
      > </a
      ><a name="21875" href="Stlc.html#21818" class="Bound"
      >B</a
      ><a name="21876"
      >
  </a
      ><a name="21879" href="Stlc.html#21879" class="InductiveConstructor"
      >&#120121;-I&#8321;</a
      ><a name="21883"
      > </a
      ><a name="21884" class="Symbol"
      >:</a
      ><a name="21885"
      > </a
      ><a name="21886" class="Symbol"
      >&#8704;</a
      ><a name="21887"
      > </a
      ><a name="21888" class="Symbol"
      >{</a
      ><a name="21889" href="Stlc.html#21889" class="Bound"
      >&#915;</a
      ><a name="21890" class="Symbol"
      >}</a
      ><a name="21891"
      > </a
      ><a name="21892" class="Symbol"
      >&#8594;</a
      ><a name="21893"
      >
    </a
      ><a name="21898" href="Stlc.html#21889" class="Bound"
      >&#915;</a
      ><a name="21899"
      > </a
      ><a name="21900" href="Stlc.html#21626" class="Datatype Operator"
      >&#8866;</a
      ><a name="21901"
      > </a
      ><a name="21902" href="Stlc.html#3735" class="InductiveConstructor"
      >true</a
      ><a name="21906"
      > </a
      ><a name="21907" href="Stlc.html#21626" class="Datatype Operator"
      >&#8758;</a
      ><a name="21908"
      > </a
      ><a name="21909" href="Stlc.html#2610" class="InductiveConstructor"
      >&#120121;</a
      ><a name="21910"
      >
  </a
      ><a name="21913" href="Stlc.html#21913" class="InductiveConstructor"
      >&#120121;-I&#8322;</a
      ><a name="21917"
      > </a
      ><a name="21918" class="Symbol"
      >:</a
      ><a name="21919"
      > </a
      ><a name="21920" class="Symbol"
      >&#8704;</a
      ><a name="21921"
      > </a
      ><a name="21922" class="Symbol"
      >{</a
      ><a name="21923" href="Stlc.html#21923" class="Bound"
      >&#915;</a
      ><a name="21924" class="Symbol"
      >}</a
      ><a name="21925"
      > </a
      ><a name="21926" class="Symbol"
      >&#8594;</a
      ><a name="21927"
      >
    </a
      ><a name="21932" href="Stlc.html#21923" class="Bound"
      >&#915;</a
      ><a name="21933"
      > </a
      ><a name="21934" href="Stlc.html#21626" class="Datatype Operator"
      >&#8866;</a
      ><a name="21935"
      > </a
      ><a name="21936" href="Stlc.html#3749" class="InductiveConstructor"
      >false</a
      ><a name="21941"
      > </a
      ><a name="21942" href="Stlc.html#21626" class="Datatype Operator"
      >&#8758;</a
      ><a name="21943"
      > </a
      ><a name="21944" href="Stlc.html#2610" class="InductiveConstructor"
      >&#120121;</a
      ><a name="21945"
      >
  </a
      ><a name="21948" href="Stlc.html#21948" class="InductiveConstructor"
      >&#120121;-E</a
      ><a name="21951"
      > </a
      ><a name="21952" class="Symbol"
      >:</a
      ><a name="21953"
      > </a
      ><a name="21954" class="Symbol"
      >&#8704;</a
      ><a name="21955"
      > </a
      ><a name="21956" class="Symbol"
      >{</a
      ><a name="21957" href="Stlc.html#21957" class="Bound"
      >&#915;</a
      ><a name="21958"
      > </a
      ><a name="21959" href="Stlc.html#21959" class="Bound"
      >L</a
      ><a name="21960"
      > </a
      ><a name="21961" href="Stlc.html#21961" class="Bound"
      >M</a
      ><a name="21962"
      > </a
      ><a name="21963" href="Stlc.html#21963" class="Bound"
      >N</a
      ><a name="21964"
      > </a
      ><a name="21965" href="Stlc.html#21965" class="Bound"
      >A</a
      ><a name="21966" class="Symbol"
      >}</a
      ><a name="21967"
      > </a
      ><a name="21968" class="Symbol"
      >&#8594;</a
      ><a name="21969"
      >
    </a
      ><a name="21974" href="Stlc.html#21957" class="Bound"
      >&#915;</a
      ><a name="21975"
      > </a
      ><a name="21976" href="Stlc.html#21626" class="Datatype Operator"
      >&#8866;</a
      ><a name="21977"
      > </a
      ><a name="21978" href="Stlc.html#21959" class="Bound"
      >L</a
      ><a name="21979"
      > </a
      ><a name="21980" href="Stlc.html#21626" class="Datatype Operator"
      >&#8758;</a
      ><a name="21981"
      > </a
      ><a name="21982" href="Stlc.html#2610" class="InductiveConstructor"
      >&#120121;</a
      ><a name="21983"
      > </a
      ><a name="21984" class="Symbol"
      >&#8594;</a
      ><a name="21985"
      >
    </a
      ><a name="21990" href="Stlc.html#21957" class="Bound"
      >&#915;</a
      ><a name="21991"
      > </a
      ><a name="21992" href="Stlc.html#21626" class="Datatype Operator"
      >&#8866;</a
      ><a name="21993"
      > </a
      ><a name="21994" href="Stlc.html#21961" class="Bound"
      >M</a
      ><a name="21995"
      > </a
      ><a name="21996" href="Stlc.html#21626" class="Datatype Operator"
      >&#8758;</a
      ><a name="21997"
      > </a
      ><a name="21998" href="Stlc.html#21965" class="Bound"
      >A</a
      ><a name="21999"
      > </a
      ><a name="22000" class="Symbol"
      >&#8594;</a
      ><a name="22001"
      >
    </a
      ><a name="22006" href="Stlc.html#21957" class="Bound"
      >&#915;</a
      ><a name="22007"
      > </a
      ><a name="22008" href="Stlc.html#21626" class="Datatype Operator"
      >&#8866;</a
      ><a name="22009"
      > </a
      ><a name="22010" href="Stlc.html#21963" class="Bound"
      >N</a
      ><a name="22011"
      > </a
      ><a name="22012" href="Stlc.html#21626" class="Datatype Operator"
      >&#8758;</a
      ><a name="22013"
      > </a
      ><a name="22014" href="Stlc.html#21965" class="Bound"
      >A</a
      ><a name="22015"
      > </a
      ><a name="22016" class="Symbol"
      >&#8594;</a
      ><a name="22017"
      >
    </a
      ><a name="22022" href="Stlc.html#21957" class="Bound"
      >&#915;</a
      ><a name="22023"
      > </a
      ><a name="22024" href="Stlc.html#21626" class="Datatype Operator"
      >&#8866;</a
      ><a name="22025"
      > </a
      ><a name="22026" href="Stlc.html#3764" class="InductiveConstructor Operator"
      >if</a
      ><a name="22028"
      > </a
      ><a name="22029" href="Stlc.html#21959" class="Bound"
      >L</a
      ><a name="22030"
      > </a
      ><a name="22031" href="Stlc.html#3764" class="InductiveConstructor Operator"
      >then</a
      ><a name="22035"
      > </a
      ><a name="22036" href="Stlc.html#21961" class="Bound"
      >M</a
      ><a name="22037"
      > </a
      ><a name="22038" href="Stlc.html#3764" class="InductiveConstructor Operator"
      >else</a
      ><a name="22042"
      > </a
      ><a name="22043" href="Stlc.html#21963" class="Bound"
      >N</a
      ><a name="22044"
      > </a
      ><a name="22045" href="Stlc.html#21626" class="Datatype Operator"
      >&#8758;</a
      ><a name="22046"
      > </a
      ><a name="22047" href="Stlc.html#21965" class="Bound"
      >A</a
      >
{% endraw %}</pre>

#### Example type derivations

Here are a couple of typing examples.  First, here is how
they would be written in an informal description of the
formal semantics.

Derivation of `not`:

    ------------ Ax    ------------- 𝔹-I₂    ------------- 𝔹-I₁
    Γ₀ ⊢ ` x ∶ 𝔹       Γ₀ ⊢ false ∶ 𝔹         Γ₀ ⊢ true ∶ 𝔹
    ------------------------------------------------------ 𝔹-E
    Γ₀ ⊢ if ` x then false else true ∶ 𝔹
    --------------------------------------------------- ⇒-I
    ∅ ⊢ λ[ x ∶ 𝔹 ] if ` x then false else true ∶ 𝔹 ⇒ 𝔹

where `Γ₀ = ∅ , x ∶ 𝔹`.

Derivation of `two`:

                            ----------------- Ax     ------------ Ax
                            Γ₂ ⊢ ` f ∶ 𝔹 ⇒ 𝔹         Γ₂ ⊢ ` x ∶ 𝔹
    ----------------- Ax    ------------------------------------- ⇒-E
    Γ₂ ⊢ ` f ∶ 𝔹 ⇒ 𝔹        Γ₂ ⊢ ` f · ` x ∶ 𝔹
    -------------------------------------------  ⇒-E
    Γ₂ ⊢ ` f · (` f · ` x) ∶ 𝔹
    ------------------------------------------ ⇒-I
    Γ₁ ⊢ λ[ x ∶ 𝔹 ] ` f · (` f · ` x) ∶ 𝔹 ⇒ 𝔹
    ---------------------------------------------------------- ⇒-I
    ∅ ⊢ λ[ f ∶ 𝔹 ⇒ 𝔹 ] λ[ x ∶ 𝔹 ] ` f · (` f · ` x) ∶ 𝔹 ⇒ 𝔹

where `Γ₁ = ∅ , f ∶ 𝔹 ⇒ 𝔹` and `Γ₂ = ∅ , f ∶ 𝔹 ⇒ 𝔹 , x ∶ 𝔹`.

Here are the above derivations formalised in Agda.

<pre class="Agda">{% raw %}
<a name="23330" href="Stlc.html#23330" class="Function"
      >typing&#8321;</a
      ><a name="23337"
      > </a
      ><a name="23338" class="Symbol"
      >:</a
      ><a name="23339"
      > </a
      ><a name="23340" href="Maps.html#10265" class="Function"
      >&#8709;</a
      ><a name="23341"
      > </a
      ><a name="23342" href="Stlc.html#21626" class="Datatype Operator"
      >&#8866;</a
      ><a name="23343"
      > </a
      ><a name="23344" href="Stlc.html#5722" class="Function"
      >not</a
      ><a name="23347"
      > </a
      ><a name="23348" href="Stlc.html#21626" class="Datatype Operator"
      >&#8758;</a
      ><a name="23349"
      > </a
      ><a name="23350" href="Stlc.html#2610" class="InductiveConstructor"
      >&#120121;</a
      ><a name="23351"
      > </a
      ><a name="23352" href="Stlc.html#2583" class="InductiveConstructor Operator"
      >&#8658;</a
      ><a name="23353"
      > </a
      ><a name="23354" href="Stlc.html#2610" class="InductiveConstructor"
      >&#120121;</a
      ><a name="23355"
      >
</a
      ><a name="23356" href="Stlc.html#23330" class="Function"
      >typing&#8321;</a
      ><a name="23363"
      > </a
      ><a name="23364" class="Symbol"
      >=</a
      ><a name="23365"
      > </a
      ><a name="23366" href="Stlc.html#21724" class="InductiveConstructor"
      >&#8658;-I</a
      ><a name="23369"
      > </a
      ><a name="23370" class="Symbol"
      >(</a
      ><a name="23371" href="Stlc.html#21948" class="InductiveConstructor"
      >&#120121;-E</a
      ><a name="23374"
      > </a
      ><a name="23375" class="Symbol"
      >(</a
      ><a name="23376" href="Stlc.html#21670" class="InductiveConstructor"
      >Ax</a
      ><a name="23378"
      > </a
      ><a name="23379" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="23383" class="Symbol"
      >)</a
      ><a name="23384"
      > </a
      ><a name="23385" href="Stlc.html#21913" class="InductiveConstructor"
      >&#120121;-I&#8322;</a
      ><a name="23389"
      > </a
      ><a name="23390" href="Stlc.html#21879" class="InductiveConstructor"
      >&#120121;-I&#8321;</a
      ><a name="23394" class="Symbol"
      >)</a
      ><a name="23395"
      >

</a
      ><a name="23397" href="Stlc.html#23397" class="Function"
      >typing&#8322;</a
      ><a name="23404"
      > </a
      ><a name="23405" class="Symbol"
      >:</a
      ><a name="23406"
      > </a
      ><a name="23407" href="Maps.html#10265" class="Function"
      >&#8709;</a
      ><a name="23408"
      > </a
      ><a name="23409" href="Stlc.html#21626" class="Datatype Operator"
      >&#8866;</a
      ><a name="23410"
      > </a
      ><a name="23411" href="Stlc.html#5726" class="Function"
      >two</a
      ><a name="23414"
      > </a
      ><a name="23415" href="Stlc.html#21626" class="Datatype Operator"
      >&#8758;</a
      ><a name="23416"
      > </a
      ><a name="23417" class="Symbol"
      >(</a
      ><a name="23418" href="Stlc.html#2610" class="InductiveConstructor"
      >&#120121;</a
      ><a name="23419"
      > </a
      ><a name="23420" href="Stlc.html#2583" class="InductiveConstructor Operator"
      >&#8658;</a
      ><a name="23421"
      > </a
      ><a name="23422" href="Stlc.html#2610" class="InductiveConstructor"
      >&#120121;</a
      ><a name="23423" class="Symbol"
      >)</a
      ><a name="23424"
      > </a
      ><a name="23425" href="Stlc.html#2583" class="InductiveConstructor Operator"
      >&#8658;</a
      ><a name="23426"
      > </a
      ><a name="23427" href="Stlc.html#2610" class="InductiveConstructor"
      >&#120121;</a
      ><a name="23428"
      > </a
      ><a name="23429" href="Stlc.html#2583" class="InductiveConstructor Operator"
      >&#8658;</a
      ><a name="23430"
      > </a
      ><a name="23431" href="Stlc.html#2610" class="InductiveConstructor"
      >&#120121;</a
      ><a name="23432"
      >
</a
      ><a name="23433" href="Stlc.html#23397" class="Function"
      >typing&#8322;</a
      ><a name="23440"
      > </a
      ><a name="23441" class="Symbol"
      >=</a
      ><a name="23442"
      > </a
      ><a name="23443" href="Stlc.html#21724" class="InductiveConstructor"
      >&#8658;-I</a
      ><a name="23446"
      > </a
      ><a name="23447" class="Symbol"
      >(</a
      ><a name="23448" href="Stlc.html#21724" class="InductiveConstructor"
      >&#8658;-I</a
      ><a name="23451"
      > </a
      ><a name="23452" class="Symbol"
      >(</a
      ><a name="23453" href="Stlc.html#21801" class="InductiveConstructor"
      >&#8658;-E</a
      ><a name="23456"
      > </a
      ><a name="23457" class="Symbol"
      >(</a
      ><a name="23458" href="Stlc.html#21670" class="InductiveConstructor"
      >Ax</a
      ><a name="23460"
      > </a
      ><a name="23461" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="23465" class="Symbol"
      >)</a
      ><a name="23466"
      > </a
      ><a name="23467" class="Symbol"
      >(</a
      ><a name="23468" href="Stlc.html#21801" class="InductiveConstructor"
      >&#8658;-E</a
      ><a name="23471"
      > </a
      ><a name="23472" class="Symbol"
      >(</a
      ><a name="23473" href="Stlc.html#21670" class="InductiveConstructor"
      >Ax</a
      ><a name="23475"
      > </a
      ><a name="23476" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="23480" class="Symbol"
      >)</a
      ><a name="23481"
      > </a
      ><a name="23482" class="Symbol"
      >(</a
      ><a name="23483" href="Stlc.html#21670" class="InductiveConstructor"
      >Ax</a
      ><a name="23485"
      > </a
      ><a name="23486" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="23490" class="Symbol"
      >))))</a
      >
{% endraw %}</pre>

#### Interaction with Agda

Construction of a type derivation is best done interactively.
Start with the declaration:

    typing₁ : ∅ ⊢ not ∶ 𝔹 ⇒ 𝔹
    typing₁ = ?

Typing C-l causes Agda to create a hole and tell us its expected type.

    typing₁ = { }0
    ?0 : ∅ ⊢ not ∶ 𝔹 ⇒ 𝔹

Now we fill in the hole by typing C-c C-r. Agda observes that
the outermost term in `not` in a `λ`, which is typed using `⇒-I`. The
`⇒-I` rule in turn takes one argument, which Agda leaves as a hole.

    typing₁ = ⇒-I { }0
    ?0 : ∅ , x ∶ 𝔹 ⊢ if ` x then false else true ∶ 𝔹

Again we fill in the hole by typing C-c C-r. Agda observes that the
outermost term is now `if_then_else_`, which is typed using `𝔹-E`. The
`𝔹-E` rule in turn takes three arguments, which Agda leaves as holes.

    typing₁ = ⇒-I (𝔹-E { }0 { }1 { }2)
    ?0 : ∅ , x ∶ 𝔹 ⊢ ` x ∶
    ?1 : ∅ , x ∶ 𝔹 ⊢ false ∶ 𝔹
    ?2 : ∅ , x ∶ 𝔹 ⊢ true ∶ 𝔹

Again we fill in the three holes by typing C-c C-r in each. Agda observes
that `` ` x ``, `false`, and `true` are typed using `Ax`, `𝔹-I₂`, and
`𝔹-I₁` respectively. The `Ax` rule in turn takes an argument, to show
that `(∅ , x ∶ 𝔹) x = just 𝔹`, which can in turn be specified with a
hole. After filling in all holes, the term is as above.

The entire process can be automated using Agsy, invoked with C-c C-a.

#### Non-examples

We can also show that terms are _not_ typeable.  For example, here is
a formal proof that it is not possible to type the term `` true ·
false ``.  In other words, no type `A` is the type of this term.  It
cannot be typed, because doing so requires that the first term in the
application is both a boolean and a function.

<pre class="Agda">{% raw %}
<a name="25171" href="Stlc.html#25171" class="Function"
      >notyping&#8322;</a
      ><a name="25180"
      > </a
      ><a name="25181" class="Symbol"
      >:</a
      ><a name="25182"
      > </a
      ><a name="25183" class="Symbol"
      >&#8704;</a
      ><a name="25184"
      > </a
      ><a name="25185" class="Symbol"
      >{</a
      ><a name="25186" href="Stlc.html#25186" class="Bound"
      >A</a
      ><a name="25187" class="Symbol"
      >}</a
      ><a name="25188"
      > </a
      ><a name="25189" class="Symbol"
      >&#8594;</a
      ><a name="25190"
      > </a
      ><a name="25191" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#414" class="Function Operator"
      >&#172;</a
      ><a name="25192"
      > </a
      ><a name="25193" class="Symbol"
      >(</a
      ><a name="25194" href="Maps.html#10265" class="Function"
      >&#8709;</a
      ><a name="25195"
      > </a
      ><a name="25196" href="Stlc.html#21626" class="Datatype Operator"
      >&#8866;</a
      ><a name="25197"
      > </a
      ><a name="25198" href="Stlc.html#3735" class="InductiveConstructor"
      >true</a
      ><a name="25202"
      > </a
      ><a name="25203" href="Stlc.html#3708" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="25204"
      > </a
      ><a name="25205" href="Stlc.html#3749" class="InductiveConstructor"
      >false</a
      ><a name="25210"
      > </a
      ><a name="25211" href="Stlc.html#21626" class="Datatype Operator"
      >&#8758;</a
      ><a name="25212"
      > </a
      ><a name="25213" href="Stlc.html#25186" class="Bound"
      >A</a
      ><a name="25214" class="Symbol"
      >)</a
      ><a name="25215"
      >
</a
      ><a name="25216" href="Stlc.html#25171" class="Function"
      >notyping&#8322;</a
      ><a name="25225"
      > </a
      ><a name="25226" class="Symbol"
      >(</a
      ><a name="25227" href="Stlc.html#21801" class="InductiveConstructor"
      >&#8658;-E</a
      ><a name="25230"
      > </a
      ><a name="25231" class="Symbol"
      >()</a
      ><a name="25233"
      > </a
      ><a name="25234" class="Symbol"
      >_)</a
      >
{% endraw %}</pre>

As a second example, here is a formal proof that it is not possible to
type `` λ[ x ∶ 𝔹 ] λ[ y ∶ 𝔹 ] ` x · ` y `` It cannot be typed, because
doing so requires `x` to be both boolean and a function.

<pre class="Agda">{% raw %}
<a name="25462" href="Stlc.html#25462" class="Function"
      >contradiction</a
      ><a name="25475"
      > </a
      ><a name="25476" class="Symbol"
      >:</a
      ><a name="25477"
      > </a
      ><a name="25478" class="Symbol"
      >&#8704;</a
      ><a name="25479"
      > </a
      ><a name="25480" class="Symbol"
      >{</a
      ><a name="25481" href="Stlc.html#25481" class="Bound"
      >A</a
      ><a name="25482"
      > </a
      ><a name="25483" href="Stlc.html#25483" class="Bound"
      >B</a
      ><a name="25484" class="Symbol"
      >}</a
      ><a name="25485"
      > </a
      ><a name="25486" class="Symbol"
      >&#8594;</a
      ><a name="25487"
      > </a
      ><a name="25488" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#414" class="Function Operator"
      >&#172;</a
      ><a name="25489"
      > </a
      ><a name="25490" class="Symbol"
      >(</a
      ><a name="25491" href="Stlc.html#2610" class="InductiveConstructor"
      >&#120121;</a
      ><a name="25492"
      > </a
      ><a name="25493" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="25494"
      > </a
      ><a name="25495" href="Stlc.html#25481" class="Bound"
      >A</a
      ><a name="25496"
      > </a
      ><a name="25497" href="Stlc.html#2583" class="InductiveConstructor Operator"
      >&#8658;</a
      ><a name="25498"
      > </a
      ><a name="25499" href="Stlc.html#25483" class="Bound"
      >B</a
      ><a name="25500" class="Symbol"
      >)</a
      ><a name="25501"
      >
</a
      ><a name="25502" href="Stlc.html#25462" class="Function"
      >contradiction</a
      ><a name="25515"
      > </a
      ><a name="25516" class="Symbol"
      >()</a
      ><a name="25518"
      >

</a
      ><a name="25520" href="Stlc.html#25520" class="Function"
      >notyping&#8321;</a
      ><a name="25529"
      > </a
      ><a name="25530" class="Symbol"
      >:</a
      ><a name="25531"
      > </a
      ><a name="25532" class="Symbol"
      >&#8704;</a
      ><a name="25533"
      > </a
      ><a name="25534" class="Symbol"
      >{</a
      ><a name="25535" href="Stlc.html#25535" class="Bound"
      >A</a
      ><a name="25536" class="Symbol"
      >}</a
      ><a name="25537"
      > </a
      ><a name="25538" class="Symbol"
      >&#8594;</a
      ><a name="25539"
      > </a
      ><a name="25540" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#414" class="Function Operator"
      >&#172;</a
      ><a name="25541"
      > </a
      ><a name="25542" class="Symbol"
      >(</a
      ><a name="25543" href="Maps.html#10265" class="Function"
      >&#8709;</a
      ><a name="25544"
      > </a
      ><a name="25545" href="Stlc.html#21626" class="Datatype Operator"
      >&#8866;</a
      ><a name="25546"
      > </a
      ><a name="25547" href="Stlc.html#3672" class="InductiveConstructor Operator"
      >&#955;[</a
      ><a name="25549"
      > </a
      ><a name="25550" href="Stlc.html#5679" class="Function"
      >x</a
      ><a name="25551"
      > </a
      ><a name="25552" href="Stlc.html#3672" class="InductiveConstructor Operator"
      >&#8758;</a
      ><a name="25553"
      > </a
      ><a name="25554" href="Stlc.html#2610" class="InductiveConstructor"
      >&#120121;</a
      ><a name="25555"
      > </a
      ><a name="25556" href="Stlc.html#3672" class="InductiveConstructor Operator"
      >]</a
      ><a name="25557"
      > </a
      ><a name="25558" href="Stlc.html#3672" class="InductiveConstructor Operator"
      >&#955;[</a
      ><a name="25560"
      > </a
      ><a name="25561" href="Stlc.html#5681" class="Function"
      >y</a
      ><a name="25562"
      > </a
      ><a name="25563" href="Stlc.html#3672" class="InductiveConstructor Operator"
      >&#8758;</a
      ><a name="25564"
      > </a
      ><a name="25565" href="Stlc.html#2610" class="InductiveConstructor"
      >&#120121;</a
      ><a name="25566"
      > </a
      ><a name="25567" href="Stlc.html#3672" class="InductiveConstructor Operator"
      >]</a
      ><a name="25568"
      > </a
      ><a name="25569" href="Stlc.html#3656" class="InductiveConstructor"
      >`</a
      ><a name="25570"
      > </a
      ><a name="25571" href="Stlc.html#5679" class="Function"
      >x</a
      ><a name="25572"
      > </a
      ><a name="25573" href="Stlc.html#3708" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="25574"
      > </a
      ><a name="25575" href="Stlc.html#3656" class="InductiveConstructor"
      >`</a
      ><a name="25576"
      > </a
      ><a name="25577" href="Stlc.html#5681" class="Function"
      >y</a
      ><a name="25578"
      > </a
      ><a name="25579" href="Stlc.html#21626" class="Datatype Operator"
      >&#8758;</a
      ><a name="25580"
      > </a
      ><a name="25581" href="Stlc.html#25535" class="Bound"
      >A</a
      ><a name="25582" class="Symbol"
      >)</a
      ><a name="25583"
      >
</a
      ><a name="25584" href="Stlc.html#25520" class="Function"
      >notyping&#8321;</a
      ><a name="25593"
      > </a
      ><a name="25594" class="Symbol"
      >(</a
      ><a name="25595" href="Stlc.html#21724" class="InductiveConstructor"
      >&#8658;-I</a
      ><a name="25598"
      > </a
      ><a name="25599" class="Symbol"
      >(</a
      ><a name="25600" href="Stlc.html#21724" class="InductiveConstructor"
      >&#8658;-I</a
      ><a name="25603"
      > </a
      ><a name="25604" class="Symbol"
      >(</a
      ><a name="25605" href="Stlc.html#21801" class="InductiveConstructor"
      >&#8658;-E</a
      ><a name="25608"
      > </a
      ><a name="25609" class="Symbol"
      >(</a
      ><a name="25610" href="Stlc.html#21670" class="InductiveConstructor"
      >Ax</a
      ><a name="25612"
      > </a
      ><a name="25613" href="Stlc.html#25613" class="Bound"
      >&#915;x</a
      ><a name="25615" class="Symbol"
      >)</a
      ><a name="25616"
      > </a
      ><a name="25617" class="Symbol"
      >_)))</a
      ><a name="25621"
      > </a
      ><a name="25622" class="Symbol"
      >=</a
      ><a name="25623"
      >  </a
      ><a name="25625" href="Stlc.html#25462" class="Function"
      >contradiction</a
      ><a name="25638"
      > </a
      ><a name="25639" class="Symbol"
      >(</a
      ><a name="25640" href="Maps.html#11919" class="Function"
      >just-injective</a
      ><a name="25654"
      > </a
      ><a name="25655" href="Stlc.html#25613" class="Bound"
      >&#915;x</a
      ><a name="25657" class="Symbol"
      >)</a
      >
{% endraw %}</pre>


#### Quiz

For each of the following, given a type `A` for which it is derivable,
or explain why there is no such `A`.

1. `` ∅ , y ∶ A ⊢ λ[ x ∶ 𝔹 ] ` x ∶ 𝔹 ⇒ 𝔹 ``
2. `` ∅ ⊢ λ[ y ∶ 𝔹 ⇒ 𝔹 ] λ[ x ∶ 𝔹 ] ` y · ` x ∶ A ``
3. `` ∅ ⊢ λ[ y ∶ 𝔹 ⇒ 𝔹 ] λ[ x ∶ 𝔹 ] ` x · ` y ∶ A ``
4. `` ∅ , x ∶ A ⊢ λ[ y : 𝔹 ⇒ 𝔹 ] `y · `x : A ``

For each of the following, give type `A`, `B`, and `C` for which it is derivable,
or explain why there are no such types.

1. `` ∅ ⊢ λ[ y ∶ 𝔹 ⇒ 𝔹 ⇒ 𝔹 ] λ[ x ∶ 𝔹 ] ` y · ` x ∶ A ``
2. `` ∅ , x ∶ A ⊢ x · x ∶ B ``
3. `` ∅ , x ∶ A , y ∶ B ⊢ λ[ z ∶ C ] ` x · (` y · ` z) ∶ D ``



