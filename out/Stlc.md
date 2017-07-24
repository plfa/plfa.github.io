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
* `` λ[ 😈 ∶ 𝔹 ⇒ 𝔹 ] λ[ 😄 ∶ 𝔹 ] ` 😈 · (` 😈 · ` 😄) ``  
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

#### Special characters

    😈  U+1F608: SMILING FACE WITH HORNS
    😄  U+1F604: SMILING FACE WITH OPEN MOUTH AND SMILING EYES

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
<a name="8429" href="Stlc.html#8429" class="Function"
      >ex&#8321;</a
      ><a name="8432"
      > </a
      ><a name="8433" class="Symbol"
      >:</a
      ><a name="8434"
      > </a
      ><a name="8435" class="Symbol"
      >(</a
      ><a name="8436" href="Stlc.html#2610" class="InductiveConstructor"
      >&#120121;</a
      ><a name="8437"
      > </a
      ><a name="8438" href="Stlc.html#2583" class="InductiveConstructor Operator"
      >&#8658;</a
      ><a name="8439"
      > </a
      ><a name="8440" href="Stlc.html#2610" class="InductiveConstructor"
      >&#120121;</a
      ><a name="8441" class="Symbol"
      >)</a
      ><a name="8442"
      > </a
      ><a name="8443" href="Stlc.html#2583" class="InductiveConstructor Operator"
      >&#8658;</a
      ><a name="8444"
      > </a
      ><a name="8445" href="Stlc.html#2610" class="InductiveConstructor"
      >&#120121;</a
      ><a name="8446"
      > </a
      ><a name="8447" href="Stlc.html#2583" class="InductiveConstructor Operator"
      >&#8658;</a
      ><a name="8448"
      > </a
      ><a name="8449" href="Stlc.html#2610" class="InductiveConstructor"
      >&#120121;</a
      ><a name="8450"
      > </a
      ><a name="8451" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="8452"
      > </a
      ><a name="8453" class="Symbol"
      >(</a
      ><a name="8454" href="Stlc.html#2610" class="InductiveConstructor"
      >&#120121;</a
      ><a name="8455"
      > </a
      ><a name="8456" href="Stlc.html#2583" class="InductiveConstructor Operator"
      >&#8658;</a
      ><a name="8457"
      > </a
      ><a name="8458" href="Stlc.html#2610" class="InductiveConstructor"
      >&#120121;</a
      ><a name="8459" class="Symbol"
      >)</a
      ><a name="8460"
      > </a
      ><a name="8461" href="Stlc.html#2583" class="InductiveConstructor Operator"
      >&#8658;</a
      ><a name="8462"
      > </a
      ><a name="8463" class="Symbol"
      >(</a
      ><a name="8464" href="Stlc.html#2610" class="InductiveConstructor"
      >&#120121;</a
      ><a name="8465"
      > </a
      ><a name="8466" href="Stlc.html#2583" class="InductiveConstructor Operator"
      >&#8658;</a
      ><a name="8467"
      > </a
      ><a name="8468" href="Stlc.html#2610" class="InductiveConstructor"
      >&#120121;</a
      ><a name="8469" class="Symbol"
      >)</a
      ><a name="8470"
      >
</a
      ><a name="8471" href="Stlc.html#8429" class="Function"
      >ex&#8321;</a
      ><a name="8474"
      > </a
      ><a name="8475" class="Symbol"
      >=</a
      ><a name="8476"
      > </a
      ><a name="8477" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="8481"
      >

</a
      ><a name="8483" href="Stlc.html#8483" class="Function"
      >ex&#8322;</a
      ><a name="8486"
      > </a
      ><a name="8487" class="Symbol"
      >:</a
      ><a name="8488"
      > </a
      ><a name="8489" href="Stlc.html#5726" class="Function"
      >two</a
      ><a name="8492"
      > </a
      ><a name="8493" href="Stlc.html#3708" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="8494"
      > </a
      ><a name="8495" href="Stlc.html#5722" class="Function"
      >not</a
      ><a name="8498"
      > </a
      ><a name="8499" href="Stlc.html#3708" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="8500"
      > </a
      ><a name="8501" href="Stlc.html#3735" class="InductiveConstructor"
      >true</a
      ><a name="8505"
      > </a
      ><a name="8506" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="8507"
      > </a
      ><a name="8508" class="Symbol"
      >(</a
      ><a name="8509" href="Stlc.html#5726" class="Function"
      >two</a
      ><a name="8512"
      > </a
      ><a name="8513" href="Stlc.html#3708" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="8514"
      > </a
      ><a name="8515" href="Stlc.html#5722" class="Function"
      >not</a
      ><a name="8518" class="Symbol"
      >)</a
      ><a name="8519"
      > </a
      ><a name="8520" href="Stlc.html#3708" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="8521"
      > </a
      ><a name="8522" href="Stlc.html#3735" class="InductiveConstructor"
      >true</a
      ><a name="8526"
      >
</a
      ><a name="8527" href="Stlc.html#8483" class="Function"
      >ex&#8322;</a
      ><a name="8530"
      > </a
      ><a name="8531" class="Symbol"
      >=</a
      ><a name="8532"
      > </a
      ><a name="8533" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="8537"
      >

</a
      ><a name="8539" href="Stlc.html#8539" class="Function"
      >ex&#8323;</a
      ><a name="8542"
      > </a
      ><a name="8543" class="Symbol"
      >:</a
      ><a name="8544"
      > </a
      ><a name="8545" href="Stlc.html#3672" class="InductiveConstructor Operator"
      >&#955;[</a
      ><a name="8547"
      > </a
      ><a name="8548" href="Stlc.html#5677" class="Function"
      >f</a
      ><a name="8549"
      > </a
      ><a name="8550" href="Stlc.html#3672" class="InductiveConstructor Operator"
      >&#8758;</a
      ><a name="8551"
      > </a
      ><a name="8552" href="Stlc.html#2610" class="InductiveConstructor"
      >&#120121;</a
      ><a name="8553"
      > </a
      ><a name="8554" href="Stlc.html#2583" class="InductiveConstructor Operator"
      >&#8658;</a
      ><a name="8555"
      > </a
      ><a name="8556" href="Stlc.html#2610" class="InductiveConstructor"
      >&#120121;</a
      ><a name="8557"
      > </a
      ><a name="8558" href="Stlc.html#3672" class="InductiveConstructor Operator"
      >]</a
      ><a name="8559"
      > </a
      ><a name="8560" href="Stlc.html#3672" class="InductiveConstructor Operator"
      >&#955;[</a
      ><a name="8562"
      > </a
      ><a name="8563" href="Stlc.html#5679" class="Function"
      >x</a
      ><a name="8564"
      > </a
      ><a name="8565" href="Stlc.html#3672" class="InductiveConstructor Operator"
      >&#8758;</a
      ><a name="8566"
      > </a
      ><a name="8567" href="Stlc.html#2610" class="InductiveConstructor"
      >&#120121;</a
      ><a name="8568"
      > </a
      ><a name="8569" href="Stlc.html#3672" class="InductiveConstructor Operator"
      >]</a
      ><a name="8570"
      > </a
      ><a name="8571" href="Stlc.html#3656" class="InductiveConstructor"
      >`</a
      ><a name="8572"
      > </a
      ><a name="8573" href="Stlc.html#5677" class="Function"
      >f</a
      ><a name="8574"
      > </a
      ><a name="8575" href="Stlc.html#3708" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="8576"
      > </a
      ><a name="8577" class="Symbol"
      >(</a
      ><a name="8578" href="Stlc.html#3656" class="InductiveConstructor"
      >`</a
      ><a name="8579"
      > </a
      ><a name="8580" href="Stlc.html#5677" class="Function"
      >f</a
      ><a name="8581"
      > </a
      ><a name="8582" href="Stlc.html#3708" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="8583"
      > </a
      ><a name="8584" href="Stlc.html#3656" class="InductiveConstructor"
      >`</a
      ><a name="8585"
      > </a
      ><a name="8586" href="Stlc.html#5679" class="Function"
      >x</a
      ><a name="8587" class="Symbol"
      >)</a
      ><a name="8588"
      >
      </a
      ><a name="8595" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="8596"
      > </a
      ><a name="8597" class="Symbol"
      >(</a
      ><a name="8598" href="Stlc.html#3672" class="InductiveConstructor Operator"
      >&#955;[</a
      ><a name="8600"
      > </a
      ><a name="8601" href="Stlc.html#5677" class="Function"
      >f</a
      ><a name="8602"
      > </a
      ><a name="8603" href="Stlc.html#3672" class="InductiveConstructor Operator"
      >&#8758;</a
      ><a name="8604"
      > </a
      ><a name="8605" href="Stlc.html#2610" class="InductiveConstructor"
      >&#120121;</a
      ><a name="8606"
      > </a
      ><a name="8607" href="Stlc.html#2583" class="InductiveConstructor Operator"
      >&#8658;</a
      ><a name="8608"
      > </a
      ><a name="8609" href="Stlc.html#2610" class="InductiveConstructor"
      >&#120121;</a
      ><a name="8610"
      > </a
      ><a name="8611" href="Stlc.html#3672" class="InductiveConstructor Operator"
      >]</a
      ><a name="8612"
      > </a
      ><a name="8613" class="Symbol"
      >(</a
      ><a name="8614" href="Stlc.html#3672" class="InductiveConstructor Operator"
      >&#955;[</a
      ><a name="8616"
      > </a
      ><a name="8617" href="Stlc.html#5679" class="Function"
      >x</a
      ><a name="8618"
      > </a
      ><a name="8619" href="Stlc.html#3672" class="InductiveConstructor Operator"
      >&#8758;</a
      ><a name="8620"
      > </a
      ><a name="8621" href="Stlc.html#2610" class="InductiveConstructor"
      >&#120121;</a
      ><a name="8622"
      > </a
      ><a name="8623" href="Stlc.html#3672" class="InductiveConstructor Operator"
      >]</a
      ><a name="8624"
      > </a
      ><a name="8625" class="Symbol"
      >(</a
      ><a name="8626" href="Stlc.html#3656" class="InductiveConstructor"
      >`</a
      ><a name="8627"
      > </a
      ><a name="8628" href="Stlc.html#5677" class="Function"
      >f</a
      ><a name="8629"
      > </a
      ><a name="8630" href="Stlc.html#3708" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="8631"
      > </a
      ><a name="8632" class="Symbol"
      >(</a
      ><a name="8633" href="Stlc.html#3656" class="InductiveConstructor"
      >`</a
      ><a name="8634"
      > </a
      ><a name="8635" href="Stlc.html#5677" class="Function"
      >f</a
      ><a name="8636"
      > </a
      ><a name="8637" href="Stlc.html#3708" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="8638"
      > </a
      ><a name="8639" href="Stlc.html#3656" class="InductiveConstructor"
      >`</a
      ><a name="8640"
      > </a
      ><a name="8641" href="Stlc.html#5679" class="Function"
      >x</a
      ><a name="8642" class="Symbol"
      >))))</a
      ><a name="8646"
      >
</a
      ><a name="8647" href="Stlc.html#8539" class="Function"
      >ex&#8323;</a
      ><a name="8650"
      > </a
      ><a name="8651" class="Symbol"
      >=</a
      ><a name="8652"
      > </a
      ><a name="8653" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
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
<a name="9714" class="Keyword"
      >data</a
      ><a name="9718"
      > </a
      ><a name="9719" href="Stlc.html#9719" class="Datatype"
      >Value</a
      ><a name="9724"
      > </a
      ><a name="9725" class="Symbol"
      >:</a
      ><a name="9726"
      > </a
      ><a name="9727" href="Stlc.html#3637" class="Datatype"
      >Term</a
      ><a name="9731"
      > </a
      ><a name="9732" class="Symbol"
      >&#8594;</a
      ><a name="9733"
      > </a
      ><a name="9734" class="PrimitiveType"
      >Set</a
      ><a name="9737"
      > </a
      ><a name="9738" class="Keyword"
      >where</a
      ><a name="9743"
      >
  </a
      ><a name="9746" href="Stlc.html#9746" class="InductiveConstructor"
      >value-&#955;</a
      ><a name="9753"
      >     </a
      ><a name="9758" class="Symbol"
      >:</a
      ><a name="9759"
      > </a
      ><a name="9760" class="Symbol"
      >&#8704;</a
      ><a name="9761"
      > </a
      ><a name="9762" class="Symbol"
      >{</a
      ><a name="9763" href="Stlc.html#9763" class="Bound"
      >x</a
      ><a name="9764"
      > </a
      ><a name="9765" href="Stlc.html#9765" class="Bound"
      >A</a
      ><a name="9766"
      > </a
      ><a name="9767" href="Stlc.html#9767" class="Bound"
      >N</a
      ><a name="9768" class="Symbol"
      >}</a
      ><a name="9769"
      > </a
      ><a name="9770" class="Symbol"
      >&#8594;</a
      ><a name="9771"
      > </a
      ><a name="9772" href="Stlc.html#9719" class="Datatype"
      >Value</a
      ><a name="9777"
      > </a
      ><a name="9778" class="Symbol"
      >(</a
      ><a name="9779" href="Stlc.html#3672" class="InductiveConstructor Operator"
      >&#955;[</a
      ><a name="9781"
      > </a
      ><a name="9782" href="Stlc.html#9763" class="Bound"
      >x</a
      ><a name="9783"
      > </a
      ><a name="9784" href="Stlc.html#3672" class="InductiveConstructor Operator"
      >&#8758;</a
      ><a name="9785"
      > </a
      ><a name="9786" href="Stlc.html#9765" class="Bound"
      >A</a
      ><a name="9787"
      > </a
      ><a name="9788" href="Stlc.html#3672" class="InductiveConstructor Operator"
      >]</a
      ><a name="9789"
      > </a
      ><a name="9790" href="Stlc.html#9767" class="Bound"
      >N</a
      ><a name="9791" class="Symbol"
      >)</a
      ><a name="9792"
      >
  </a
      ><a name="9795" href="Stlc.html#9795" class="InductiveConstructor"
      >value-true</a
      ><a name="9805"
      >  </a
      ><a name="9807" class="Symbol"
      >:</a
      ><a name="9808"
      > </a
      ><a name="9809" href="Stlc.html#9719" class="Datatype"
      >Value</a
      ><a name="9814"
      > </a
      ><a name="9815" href="Stlc.html#3735" class="InductiveConstructor"
      >true</a
      ><a name="9819"
      >
  </a
      ><a name="9822" href="Stlc.html#9822" class="InductiveConstructor"
      >value-false</a
      ><a name="9833"
      > </a
      ><a name="9834" class="Symbol"
      >:</a
      ><a name="9835"
      > </a
      ><a name="9836" href="Stlc.html#9719" class="Datatype"
      >Value</a
      ><a name="9841"
      > </a
      ><a name="9842" href="Stlc.html#3749" class="InductiveConstructor"
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
<a name="12263" href="Stlc.html#12263" class="Function Operator"
      >_[_:=_]</a
      ><a name="12270"
      > </a
      ><a name="12271" class="Symbol"
      >:</a
      ><a name="12272"
      > </a
      ><a name="12273" href="Stlc.html#3637" class="Datatype"
      >Term</a
      ><a name="12277"
      > </a
      ><a name="12278" class="Symbol"
      >&#8594;</a
      ><a name="12279"
      > </a
      ><a name="12280" href="Maps.html#2171" class="Datatype"
      >Id</a
      ><a name="12282"
      > </a
      ><a name="12283" class="Symbol"
      >&#8594;</a
      ><a name="12284"
      > </a
      ><a name="12285" href="Stlc.html#3637" class="Datatype"
      >Term</a
      ><a name="12289"
      > </a
      ><a name="12290" class="Symbol"
      >&#8594;</a
      ><a name="12291"
      > </a
      ><a name="12292" href="Stlc.html#3637" class="Datatype"
      >Term</a
      ><a name="12296"
      >
</a
      ><a name="12297" class="Symbol"
      >(</a
      ><a name="12298" href="Stlc.html#3656" class="InductiveConstructor"
      >`</a
      ><a name="12299"
      > </a
      ><a name="12300" href="Stlc.html#12300" class="Bound"
      >x&#8242;</a
      ><a name="12302" class="Symbol"
      >)</a
      ><a name="12303"
      > </a
      ><a name="12304" href="Stlc.html#12263" class="Function Operator"
      >[</a
      ><a name="12305"
      > </a
      ><a name="12306" href="Stlc.html#12306" class="Bound"
      >x</a
      ><a name="12307"
      > </a
      ><a name="12308" href="Stlc.html#12263" class="Function Operator"
      >:=</a
      ><a name="12310"
      > </a
      ><a name="12311" href="Stlc.html#12311" class="Bound"
      >V</a
      ><a name="12312"
      > </a
      ><a name="12313" href="Stlc.html#12263" class="Function Operator"
      >]</a
      ><a name="12314"
      > </a
      ><a name="12315" class="Keyword"
      >with</a
      ><a name="12319"
      > </a
      ><a name="12320" href="Stlc.html#12306" class="Bound"
      >x</a
      ><a name="12321"
      > </a
      ><a name="12322" href="Maps.html#2509" class="Function Operator"
      >&#8799;</a
      ><a name="12323"
      > </a
      ><a name="12324" href="Stlc.html#12300" class="Bound"
      >x&#8242;</a
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
      ><a name="12337" class="Symbol"
      >_</a
      ><a name="12338"
      > </a
      ><a name="12339" class="Symbol"
      >=</a
      ><a name="12340"
      > </a
      ><a name="12341" href="Stlc.html#12311" class="Bound"
      >V</a
      ><a name="12342"
      >
</a
      ><a name="12343" class="Symbol"
      >...</a
      ><a name="12346"
      > </a
      ><a name="12347" class="Symbol"
      >|</a
      ><a name="12348"
      > </a
      ><a name="12349" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#547" class="InductiveConstructor"
      >no</a
      ><a name="12351"
      >  </a
      ><a name="12353" class="Symbol"
      >_</a
      ><a name="12354"
      > </a
      ><a name="12355" class="Symbol"
      >=</a
      ><a name="12356"
      > </a
      ><a name="12357" href="Stlc.html#3656" class="InductiveConstructor"
      >`</a
      ><a name="12358"
      > </a
      ><a name="12359" href="Stlc.html#12300" class="Bound"
      >x&#8242;</a
      ><a name="12361"
      >
</a
      ><a name="12362" class="Symbol"
      >(</a
      ><a name="12363" href="Stlc.html#3672" class="InductiveConstructor Operator"
      >&#955;[</a
      ><a name="12365"
      > </a
      ><a name="12366" href="Stlc.html#12366" class="Bound"
      >x&#8242;</a
      ><a name="12368"
      > </a
      ><a name="12369" href="Stlc.html#3672" class="InductiveConstructor Operator"
      >&#8758;</a
      ><a name="12370"
      > </a
      ><a name="12371" href="Stlc.html#12371" class="Bound"
      >A&#8242;</a
      ><a name="12373"
      > </a
      ><a name="12374" href="Stlc.html#3672" class="InductiveConstructor Operator"
      >]</a
      ><a name="12375"
      > </a
      ><a name="12376" href="Stlc.html#12376" class="Bound"
      >N&#8242;</a
      ><a name="12378" class="Symbol"
      >)</a
      ><a name="12379"
      > </a
      ><a name="12380" href="Stlc.html#12263" class="Function Operator"
      >[</a
      ><a name="12381"
      > </a
      ><a name="12382" href="Stlc.html#12382" class="Bound"
      >x</a
      ><a name="12383"
      > </a
      ><a name="12384" href="Stlc.html#12263" class="Function Operator"
      >:=</a
      ><a name="12386"
      > </a
      ><a name="12387" href="Stlc.html#12387" class="Bound"
      >V</a
      ><a name="12388"
      > </a
      ><a name="12389" href="Stlc.html#12263" class="Function Operator"
      >]</a
      ><a name="12390"
      > </a
      ><a name="12391" class="Keyword"
      >with</a
      ><a name="12395"
      > </a
      ><a name="12396" href="Stlc.html#12382" class="Bound"
      >x</a
      ><a name="12397"
      > </a
      ><a name="12398" href="Maps.html#2509" class="Function Operator"
      >&#8799;</a
      ><a name="12399"
      > </a
      ><a name="12400" href="Stlc.html#12366" class="Bound"
      >x&#8242;</a
      ><a name="12402"
      >
</a
      ><a name="12403" class="Symbol"
      >...</a
      ><a name="12406"
      > </a
      ><a name="12407" class="Symbol"
      >|</a
      ><a name="12408"
      > </a
      ><a name="12409" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#520" class="InductiveConstructor"
      >yes</a
      ><a name="12412"
      > </a
      ><a name="12413" class="Symbol"
      >_</a
      ><a name="12414"
      > </a
      ><a name="12415" class="Symbol"
      >=</a
      ><a name="12416"
      > </a
      ><a name="12417" href="Stlc.html#3672" class="InductiveConstructor Operator"
      >&#955;[</a
      ><a name="12419"
      > </a
      ><a name="12420" href="Stlc.html#12366" class="Bound"
      >x&#8242;</a
      ><a name="12422"
      > </a
      ><a name="12423" href="Stlc.html#3672" class="InductiveConstructor Operator"
      >&#8758;</a
      ><a name="12424"
      > </a
      ><a name="12425" href="Stlc.html#12371" class="Bound"
      >A&#8242;</a
      ><a name="12427"
      > </a
      ><a name="12428" href="Stlc.html#3672" class="InductiveConstructor Operator"
      >]</a
      ><a name="12429"
      > </a
      ><a name="12430" href="Stlc.html#12376" class="Bound"
      >N&#8242;</a
      ><a name="12432"
      >
</a
      ><a name="12433" class="Symbol"
      >...</a
      ><a name="12436"
      > </a
      ><a name="12437" class="Symbol"
      >|</a
      ><a name="12438"
      > </a
      ><a name="12439" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#547" class="InductiveConstructor"
      >no</a
      ><a name="12441"
      >  </a
      ><a name="12443" class="Symbol"
      >_</a
      ><a name="12444"
      > </a
      ><a name="12445" class="Symbol"
      >=</a
      ><a name="12446"
      > </a
      ><a name="12447" href="Stlc.html#3672" class="InductiveConstructor Operator"
      >&#955;[</a
      ><a name="12449"
      > </a
      ><a name="12450" href="Stlc.html#12366" class="Bound"
      >x&#8242;</a
      ><a name="12452"
      > </a
      ><a name="12453" href="Stlc.html#3672" class="InductiveConstructor Operator"
      >&#8758;</a
      ><a name="12454"
      > </a
      ><a name="12455" href="Stlc.html#12371" class="Bound"
      >A&#8242;</a
      ><a name="12457"
      > </a
      ><a name="12458" href="Stlc.html#3672" class="InductiveConstructor Operator"
      >]</a
      ><a name="12459"
      > </a
      ><a name="12460" class="Symbol"
      >(</a
      ><a name="12461" href="Stlc.html#12376" class="Bound"
      >N&#8242;</a
      ><a name="12463"
      > </a
      ><a name="12464" href="Stlc.html#12263" class="Function Operator"
      >[</a
      ><a name="12465"
      > </a
      ><a name="12466" href="Stlc.html#12382" class="Bound"
      >x</a
      ><a name="12467"
      > </a
      ><a name="12468" href="Stlc.html#12263" class="Function Operator"
      >:=</a
      ><a name="12470"
      > </a
      ><a name="12471" href="Stlc.html#12387" class="Bound"
      >V</a
      ><a name="12472"
      > </a
      ><a name="12473" href="Stlc.html#12263" class="Function Operator"
      >]</a
      ><a name="12474" class="Symbol"
      >)</a
      ><a name="12475"
      >
</a
      ><a name="12476" class="Symbol"
      >(</a
      ><a name="12477" href="Stlc.html#12477" class="Bound"
      >L&#8242;</a
      ><a name="12479"
      > </a
      ><a name="12480" href="Stlc.html#3708" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="12481"
      > </a
      ><a name="12482" href="Stlc.html#12482" class="Bound"
      >M&#8242;</a
      ><a name="12484" class="Symbol"
      >)</a
      ><a name="12485"
      > </a
      ><a name="12486" href="Stlc.html#12263" class="Function Operator"
      >[</a
      ><a name="12487"
      > </a
      ><a name="12488" href="Stlc.html#12488" class="Bound"
      >x</a
      ><a name="12489"
      > </a
      ><a name="12490" href="Stlc.html#12263" class="Function Operator"
      >:=</a
      ><a name="12492"
      > </a
      ><a name="12493" href="Stlc.html#12493" class="Bound"
      >V</a
      ><a name="12494"
      > </a
      ><a name="12495" href="Stlc.html#12263" class="Function Operator"
      >]</a
      ><a name="12496"
      > </a
      ><a name="12497" class="Symbol"
      >=</a
      ><a name="12498"
      >  </a
      ><a name="12500" class="Symbol"
      >(</a
      ><a name="12501" href="Stlc.html#12477" class="Bound"
      >L&#8242;</a
      ><a name="12503"
      > </a
      ><a name="12504" href="Stlc.html#12263" class="Function Operator"
      >[</a
      ><a name="12505"
      > </a
      ><a name="12506" href="Stlc.html#12488" class="Bound"
      >x</a
      ><a name="12507"
      > </a
      ><a name="12508" href="Stlc.html#12263" class="Function Operator"
      >:=</a
      ><a name="12510"
      > </a
      ><a name="12511" href="Stlc.html#12493" class="Bound"
      >V</a
      ><a name="12512"
      > </a
      ><a name="12513" href="Stlc.html#12263" class="Function Operator"
      >]</a
      ><a name="12514" class="Symbol"
      >)</a
      ><a name="12515"
      > </a
      ><a name="12516" href="Stlc.html#3708" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="12517"
      > </a
      ><a name="12518" class="Symbol"
      >(</a
      ><a name="12519" href="Stlc.html#12482" class="Bound"
      >M&#8242;</a
      ><a name="12521"
      > </a
      ><a name="12522" href="Stlc.html#12263" class="Function Operator"
      >[</a
      ><a name="12523"
      > </a
      ><a name="12524" href="Stlc.html#12488" class="Bound"
      >x</a
      ><a name="12525"
      > </a
      ><a name="12526" href="Stlc.html#12263" class="Function Operator"
      >:=</a
      ><a name="12528"
      > </a
      ><a name="12529" href="Stlc.html#12493" class="Bound"
      >V</a
      ><a name="12530"
      > </a
      ><a name="12531" href="Stlc.html#12263" class="Function Operator"
      >]</a
      ><a name="12532" class="Symbol"
      >)</a
      ><a name="12533"
      >
</a
      ><a name="12534" class="Symbol"
      >(</a
      ><a name="12535" href="Stlc.html#3735" class="InductiveConstructor"
      >true</a
      ><a name="12539" class="Symbol"
      >)</a
      ><a name="12540"
      > </a
      ><a name="12541" href="Stlc.html#12263" class="Function Operator"
      >[</a
      ><a name="12542"
      > </a
      ><a name="12543" href="Stlc.html#12543" class="Bound"
      >x</a
      ><a name="12544"
      > </a
      ><a name="12545" href="Stlc.html#12263" class="Function Operator"
      >:=</a
      ><a name="12547"
      > </a
      ><a name="12548" href="Stlc.html#12548" class="Bound"
      >V</a
      ><a name="12549"
      > </a
      ><a name="12550" href="Stlc.html#12263" class="Function Operator"
      >]</a
      ><a name="12551"
      > </a
      ><a name="12552" class="Symbol"
      >=</a
      ><a name="12553"
      > </a
      ><a name="12554" href="Stlc.html#3735" class="InductiveConstructor"
      >true</a
      ><a name="12558"
      >
</a
      ><a name="12559" class="Symbol"
      >(</a
      ><a name="12560" href="Stlc.html#3749" class="InductiveConstructor"
      >false</a
      ><a name="12565" class="Symbol"
      >)</a
      ><a name="12566"
      > </a
      ><a name="12567" href="Stlc.html#12263" class="Function Operator"
      >[</a
      ><a name="12568"
      > </a
      ><a name="12569" href="Stlc.html#12569" class="Bound"
      >x</a
      ><a name="12570"
      > </a
      ><a name="12571" href="Stlc.html#12263" class="Function Operator"
      >:=</a
      ><a name="12573"
      > </a
      ><a name="12574" href="Stlc.html#12574" class="Bound"
      >V</a
      ><a name="12575"
      > </a
      ><a name="12576" href="Stlc.html#12263" class="Function Operator"
      >]</a
      ><a name="12577"
      > </a
      ><a name="12578" class="Symbol"
      >=</a
      ><a name="12579"
      > </a
      ><a name="12580" href="Stlc.html#3749" class="InductiveConstructor"
      >false</a
      ><a name="12585"
      >
</a
      ><a name="12586" class="Symbol"
      >(</a
      ><a name="12587" href="Stlc.html#3764" class="InductiveConstructor Operator"
      >if</a
      ><a name="12589"
      > </a
      ><a name="12590" href="Stlc.html#12590" class="Bound"
      >L&#8242;</a
      ><a name="12592"
      > </a
      ><a name="12593" href="Stlc.html#3764" class="InductiveConstructor Operator"
      >then</a
      ><a name="12597"
      > </a
      ><a name="12598" href="Stlc.html#12598" class="Bound"
      >M&#8242;</a
      ><a name="12600"
      > </a
      ><a name="12601" href="Stlc.html#3764" class="InductiveConstructor Operator"
      >else</a
      ><a name="12605"
      > </a
      ><a name="12606" href="Stlc.html#12606" class="Bound"
      >N&#8242;</a
      ><a name="12608" class="Symbol"
      >)</a
      ><a name="12609"
      > </a
      ><a name="12610" href="Stlc.html#12263" class="Function Operator"
      >[</a
      ><a name="12611"
      > </a
      ><a name="12612" href="Stlc.html#12612" class="Bound"
      >x</a
      ><a name="12613"
      > </a
      ><a name="12614" href="Stlc.html#12263" class="Function Operator"
      >:=</a
      ><a name="12616"
      > </a
      ><a name="12617" href="Stlc.html#12617" class="Bound"
      >V</a
      ><a name="12618"
      > </a
      ><a name="12619" href="Stlc.html#12263" class="Function Operator"
      >]</a
      ><a name="12620"
      > </a
      ><a name="12621" class="Symbol"
      >=</a
      ><a name="12622"
      >
  </a
      ><a name="12625" href="Stlc.html#3764" class="InductiveConstructor Operator"
      >if</a
      ><a name="12627"
      > </a
      ><a name="12628" class="Symbol"
      >(</a
      ><a name="12629" href="Stlc.html#12590" class="Bound"
      >L&#8242;</a
      ><a name="12631"
      > </a
      ><a name="12632" href="Stlc.html#12263" class="Function Operator"
      >[</a
      ><a name="12633"
      > </a
      ><a name="12634" href="Stlc.html#12612" class="Bound"
      >x</a
      ><a name="12635"
      > </a
      ><a name="12636" href="Stlc.html#12263" class="Function Operator"
      >:=</a
      ><a name="12638"
      > </a
      ><a name="12639" href="Stlc.html#12617" class="Bound"
      >V</a
      ><a name="12640"
      > </a
      ><a name="12641" href="Stlc.html#12263" class="Function Operator"
      >]</a
      ><a name="12642" class="Symbol"
      >)</a
      ><a name="12643"
      > </a
      ><a name="12644" href="Stlc.html#3764" class="InductiveConstructor Operator"
      >then</a
      ><a name="12648"
      > </a
      ><a name="12649" class="Symbol"
      >(</a
      ><a name="12650" href="Stlc.html#12598" class="Bound"
      >M&#8242;</a
      ><a name="12652"
      > </a
      ><a name="12653" href="Stlc.html#12263" class="Function Operator"
      >[</a
      ><a name="12654"
      > </a
      ><a name="12655" href="Stlc.html#12612" class="Bound"
      >x</a
      ><a name="12656"
      > </a
      ><a name="12657" href="Stlc.html#12263" class="Function Operator"
      >:=</a
      ><a name="12659"
      > </a
      ><a name="12660" href="Stlc.html#12617" class="Bound"
      >V</a
      ><a name="12661"
      > </a
      ><a name="12662" href="Stlc.html#12263" class="Function Operator"
      >]</a
      ><a name="12663" class="Symbol"
      >)</a
      ><a name="12664"
      > </a
      ><a name="12665" href="Stlc.html#3764" class="InductiveConstructor Operator"
      >else</a
      ><a name="12669"
      > </a
      ><a name="12670" class="Symbol"
      >(</a
      ><a name="12671" href="Stlc.html#12606" class="Bound"
      >N&#8242;</a
      ><a name="12673"
      > </a
      ><a name="12674" href="Stlc.html#12263" class="Function Operator"
      >[</a
      ><a name="12675"
      > </a
      ><a name="12676" href="Stlc.html#12612" class="Bound"
      >x</a
      ><a name="12677"
      > </a
      ><a name="12678" href="Stlc.html#12263" class="Function Operator"
      >:=</a
      ><a name="12680"
      > </a
      ><a name="12681" href="Stlc.html#12617" class="Bound"
      >V</a
      ><a name="12682"
      > </a
      ><a name="12683" href="Stlc.html#12263" class="Function Operator"
      >]</a
      ><a name="12684" class="Symbol"
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
<a name="13434" href="Stlc.html#13434" class="Function"
      >ex&#8321;&#8321;</a
      ><a name="13438"
      > </a
      ><a name="13439" class="Symbol"
      >:</a
      ><a name="13440"
      > </a
      ><a name="13441" href="Stlc.html#3656" class="InductiveConstructor"
      >`</a
      ><a name="13442"
      > </a
      ><a name="13443" href="Stlc.html#5677" class="Function"
      >f</a
      ><a name="13444"
      > </a
      ><a name="13445" href="Stlc.html#12263" class="Function Operator"
      >[</a
      ><a name="13446"
      > </a
      ><a name="13447" href="Stlc.html#5677" class="Function"
      >f</a
      ><a name="13448"
      > </a
      ><a name="13449" href="Stlc.html#12263" class="Function Operator"
      >:=</a
      ><a name="13451"
      > </a
      ><a name="13452" href="Stlc.html#5722" class="Function"
      >not</a
      ><a name="13455"
      > </a
      ><a name="13456" href="Stlc.html#12263" class="Function Operator"
      >]</a
      ><a name="13457"
      > </a
      ><a name="13458" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="13459"
      >  </a
      ><a name="13461" href="Stlc.html#5722" class="Function"
      >not</a
      ><a name="13464"
      >
</a
      ><a name="13465" href="Stlc.html#13434" class="Function"
      >ex&#8321;&#8321;</a
      ><a name="13469"
      > </a
      ><a name="13470" class="Symbol"
      >=</a
      ><a name="13471"
      > </a
      ><a name="13472" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="13476"
      >

</a
      ><a name="13478" href="Stlc.html#13478" class="Function"
      >ex&#8321;&#8322;</a
      ><a name="13482"
      > </a
      ><a name="13483" class="Symbol"
      >:</a
      ><a name="13484"
      > </a
      ><a name="13485" href="Stlc.html#3735" class="InductiveConstructor"
      >true</a
      ><a name="13489"
      > </a
      ><a name="13490" href="Stlc.html#12263" class="Function Operator"
      >[</a
      ><a name="13491"
      > </a
      ><a name="13492" href="Stlc.html#5677" class="Function"
      >f</a
      ><a name="13493"
      > </a
      ><a name="13494" href="Stlc.html#12263" class="Function Operator"
      >:=</a
      ><a name="13496"
      > </a
      ><a name="13497" href="Stlc.html#5722" class="Function"
      >not</a
      ><a name="13500"
      > </a
      ><a name="13501" href="Stlc.html#12263" class="Function Operator"
      >]</a
      ><a name="13502"
      > </a
      ><a name="13503" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="13504"
      > </a
      ><a name="13505" href="Stlc.html#3735" class="InductiveConstructor"
      >true</a
      ><a name="13509"
      >
</a
      ><a name="13510" href="Stlc.html#13478" class="Function"
      >ex&#8321;&#8322;</a
      ><a name="13514"
      > </a
      ><a name="13515" class="Symbol"
      >=</a
      ><a name="13516"
      > </a
      ><a name="13517" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="13521"
      >

</a
      ><a name="13523" href="Stlc.html#13523" class="Function"
      >ex&#8321;&#8323;</a
      ><a name="13527"
      > </a
      ><a name="13528" class="Symbol"
      >:</a
      ><a name="13529"
      > </a
      ><a name="13530" class="Symbol"
      >(</a
      ><a name="13531" href="Stlc.html#3656" class="InductiveConstructor"
      >`</a
      ><a name="13532"
      > </a
      ><a name="13533" href="Stlc.html#5677" class="Function"
      >f</a
      ><a name="13534"
      > </a
      ><a name="13535" href="Stlc.html#3708" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="13536"
      > </a
      ><a name="13537" href="Stlc.html#3735" class="InductiveConstructor"
      >true</a
      ><a name="13541" class="Symbol"
      >)</a
      ><a name="13542"
      > </a
      ><a name="13543" href="Stlc.html#12263" class="Function Operator"
      >[</a
      ><a name="13544"
      > </a
      ><a name="13545" href="Stlc.html#5677" class="Function"
      >f</a
      ><a name="13546"
      > </a
      ><a name="13547" href="Stlc.html#12263" class="Function Operator"
      >:=</a
      ><a name="13549"
      > </a
      ><a name="13550" href="Stlc.html#5722" class="Function"
      >not</a
      ><a name="13553"
      > </a
      ><a name="13554" href="Stlc.html#12263" class="Function Operator"
      >]</a
      ><a name="13555"
      > </a
      ><a name="13556" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="13557"
      > </a
      ><a name="13558" href="Stlc.html#5722" class="Function"
      >not</a
      ><a name="13561"
      > </a
      ><a name="13562" href="Stlc.html#3708" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="13563"
      > </a
      ><a name="13564" href="Stlc.html#3735" class="InductiveConstructor"
      >true</a
      ><a name="13568"
      >
</a
      ><a name="13569" href="Stlc.html#13523" class="Function"
      >ex&#8321;&#8323;</a
      ><a name="13573"
      > </a
      ><a name="13574" class="Symbol"
      >=</a
      ><a name="13575"
      > </a
      ><a name="13576" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="13580"
      >

</a
      ><a name="13582" href="Stlc.html#13582" class="Function"
      >ex&#8321;&#8324;</a
      ><a name="13586"
      > </a
      ><a name="13587" class="Symbol"
      >:</a
      ><a name="13588"
      > </a
      ><a name="13589" class="Symbol"
      >(</a
      ><a name="13590" href="Stlc.html#3656" class="InductiveConstructor"
      >`</a
      ><a name="13591"
      > </a
      ><a name="13592" href="Stlc.html#5677" class="Function"
      >f</a
      ><a name="13593"
      > </a
      ><a name="13594" href="Stlc.html#3708" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="13595"
      > </a
      ><a name="13596" class="Symbol"
      >(</a
      ><a name="13597" href="Stlc.html#3656" class="InductiveConstructor"
      >`</a
      ><a name="13598"
      > </a
      ><a name="13599" href="Stlc.html#5677" class="Function"
      >f</a
      ><a name="13600"
      > </a
      ><a name="13601" href="Stlc.html#3708" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="13602"
      > </a
      ><a name="13603" href="Stlc.html#3735" class="InductiveConstructor"
      >true</a
      ><a name="13607" class="Symbol"
      >))</a
      ><a name="13609"
      > </a
      ><a name="13610" href="Stlc.html#12263" class="Function Operator"
      >[</a
      ><a name="13611"
      > </a
      ><a name="13612" href="Stlc.html#5677" class="Function"
      >f</a
      ><a name="13613"
      > </a
      ><a name="13614" href="Stlc.html#12263" class="Function Operator"
      >:=</a
      ><a name="13616"
      > </a
      ><a name="13617" href="Stlc.html#5722" class="Function"
      >not</a
      ><a name="13620"
      > </a
      ><a name="13621" href="Stlc.html#12263" class="Function Operator"
      >]</a
      ><a name="13622"
      > </a
      ><a name="13623" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="13624"
      > </a
      ><a name="13625" href="Stlc.html#5722" class="Function"
      >not</a
      ><a name="13628"
      > </a
      ><a name="13629" href="Stlc.html#3708" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="13630"
      > </a
      ><a name="13631" class="Symbol"
      >(</a
      ><a name="13632" href="Stlc.html#5722" class="Function"
      >not</a
      ><a name="13635"
      > </a
      ><a name="13636" href="Stlc.html#3708" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="13637"
      > </a
      ><a name="13638" href="Stlc.html#3735" class="InductiveConstructor"
      >true</a
      ><a name="13642" class="Symbol"
      >)</a
      ><a name="13643"
      >
</a
      ><a name="13644" href="Stlc.html#13582" class="Function"
      >ex&#8321;&#8324;</a
      ><a name="13648"
      > </a
      ><a name="13649" class="Symbol"
      >=</a
      ><a name="13650"
      > </a
      ><a name="13651" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="13655"
      >

</a
      ><a name="13657" href="Stlc.html#13657" class="Function"
      >ex&#8321;&#8325;</a
      ><a name="13661"
      > </a
      ><a name="13662" class="Symbol"
      >:</a
      ><a name="13663"
      > </a
      ><a name="13664" class="Symbol"
      >(</a
      ><a name="13665" href="Stlc.html#3672" class="InductiveConstructor Operator"
      >&#955;[</a
      ><a name="13667"
      > </a
      ><a name="13668" href="Stlc.html#5679" class="Function"
      >x</a
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
      ><a name="13678" href="Stlc.html#5677" class="Function"
      >f</a
      ><a name="13679"
      > </a
      ><a name="13680" href="Stlc.html#3708" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="13681"
      > </a
      ><a name="13682" class="Symbol"
      >(</a
      ><a name="13683" href="Stlc.html#3656" class="InductiveConstructor"
      >`</a
      ><a name="13684"
      > </a
      ><a name="13685" href="Stlc.html#5677" class="Function"
      >f</a
      ><a name="13686"
      > </a
      ><a name="13687" href="Stlc.html#3708" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="13688"
      > </a
      ><a name="13689" href="Stlc.html#3656" class="InductiveConstructor"
      >`</a
      ><a name="13690"
      > </a
      ><a name="13691" href="Stlc.html#5679" class="Function"
      >x</a
      ><a name="13692" class="Symbol"
      >))</a
      ><a name="13694"
      > </a
      ><a name="13695" href="Stlc.html#12263" class="Function Operator"
      >[</a
      ><a name="13696"
      > </a
      ><a name="13697" href="Stlc.html#5677" class="Function"
      >f</a
      ><a name="13698"
      > </a
      ><a name="13699" href="Stlc.html#12263" class="Function Operator"
      >:=</a
      ><a name="13701"
      > </a
      ><a name="13702" href="Stlc.html#5722" class="Function"
      >not</a
      ><a name="13705"
      > </a
      ><a name="13706" href="Stlc.html#12263" class="Function Operator"
      >]</a
      ><a name="13707"
      > </a
      ><a name="13708" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="13709"
      > </a
      ><a name="13710" href="Stlc.html#3672" class="InductiveConstructor Operator"
      >&#955;[</a
      ><a name="13712"
      > </a
      ><a name="13713" href="Stlc.html#5679" class="Function"
      >x</a
      ><a name="13714"
      > </a
      ><a name="13715" href="Stlc.html#3672" class="InductiveConstructor Operator"
      >&#8758;</a
      ><a name="13716"
      > </a
      ><a name="13717" href="Stlc.html#2610" class="InductiveConstructor"
      >&#120121;</a
      ><a name="13718"
      > </a
      ><a name="13719" href="Stlc.html#3672" class="InductiveConstructor Operator"
      >]</a
      ><a name="13720"
      > </a
      ><a name="13721" href="Stlc.html#5722" class="Function"
      >not</a
      ><a name="13724"
      > </a
      ><a name="13725" href="Stlc.html#3708" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="13726"
      > </a
      ><a name="13727" class="Symbol"
      >(</a
      ><a name="13728" href="Stlc.html#5722" class="Function"
      >not</a
      ><a name="13731"
      > </a
      ><a name="13732" href="Stlc.html#3708" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="13733"
      > </a
      ><a name="13734" href="Stlc.html#3656" class="InductiveConstructor"
      >`</a
      ><a name="13735"
      > </a
      ><a name="13736" href="Stlc.html#5679" class="Function"
      >x</a
      ><a name="13737" class="Symbol"
      >)</a
      ><a name="13738"
      >
</a
      ><a name="13739" href="Stlc.html#13657" class="Function"
      >ex&#8321;&#8325;</a
      ><a name="13743"
      > </a
      ><a name="13744" class="Symbol"
      >=</a
      ><a name="13745"
      > </a
      ><a name="13746" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="13750"
      >

</a
      ><a name="13752" href="Stlc.html#13752" class="Function"
      >ex&#8321;&#8326;</a
      ><a name="13756"
      > </a
      ><a name="13757" class="Symbol"
      >:</a
      ><a name="13758"
      > </a
      ><a name="13759" class="Symbol"
      >(</a
      ><a name="13760" href="Stlc.html#3672" class="InductiveConstructor Operator"
      >&#955;[</a
      ><a name="13762"
      > </a
      ><a name="13763" href="Stlc.html#5681" class="Function"
      >y</a
      ><a name="13764"
      > </a
      ><a name="13765" href="Stlc.html#3672" class="InductiveConstructor Operator"
      >&#8758;</a
      ><a name="13766"
      > </a
      ><a name="13767" href="Stlc.html#2610" class="InductiveConstructor"
      >&#120121;</a
      ><a name="13768"
      > </a
      ><a name="13769" href="Stlc.html#3672" class="InductiveConstructor Operator"
      >]</a
      ><a name="13770"
      > </a
      ><a name="13771" href="Stlc.html#3656" class="InductiveConstructor"
      >`</a
      ><a name="13772"
      > </a
      ><a name="13773" href="Stlc.html#5681" class="Function"
      >y</a
      ><a name="13774" class="Symbol"
      >)</a
      ><a name="13775"
      > </a
      ><a name="13776" href="Stlc.html#12263" class="Function Operator"
      >[</a
      ><a name="13777"
      > </a
      ><a name="13778" href="Stlc.html#5679" class="Function"
      >x</a
      ><a name="13779"
      > </a
      ><a name="13780" href="Stlc.html#12263" class="Function Operator"
      >:=</a
      ><a name="13782"
      > </a
      ><a name="13783" href="Stlc.html#3735" class="InductiveConstructor"
      >true</a
      ><a name="13787"
      > </a
      ><a name="13788" href="Stlc.html#12263" class="Function Operator"
      >]</a
      ><a name="13789"
      > </a
      ><a name="13790" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="13791"
      > </a
      ><a name="13792" href="Stlc.html#3672" class="InductiveConstructor Operator"
      >&#955;[</a
      ><a name="13794"
      > </a
      ><a name="13795" href="Stlc.html#5681" class="Function"
      >y</a
      ><a name="13796"
      > </a
      ><a name="13797" href="Stlc.html#3672" class="InductiveConstructor Operator"
      >&#8758;</a
      ><a name="13798"
      > </a
      ><a name="13799" href="Stlc.html#2610" class="InductiveConstructor"
      >&#120121;</a
      ><a name="13800"
      > </a
      ><a name="13801" href="Stlc.html#3672" class="InductiveConstructor Operator"
      >]</a
      ><a name="13802"
      > </a
      ><a name="13803" href="Stlc.html#3656" class="InductiveConstructor"
      >`</a
      ><a name="13804"
      > </a
      ><a name="13805" href="Stlc.html#5681" class="Function"
      >y</a
      ><a name="13806"
      >
</a
      ><a name="13807" href="Stlc.html#13752" class="Function"
      >ex&#8321;&#8326;</a
      ><a name="13811"
      > </a
      ><a name="13812" class="Symbol"
      >=</a
      ><a name="13813"
      > </a
      ><a name="13814" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="13818"
      >

</a
      ><a name="13820" href="Stlc.html#13820" class="Function"
      >ex&#8321;&#8327;</a
      ><a name="13824"
      > </a
      ><a name="13825" class="Symbol"
      >:</a
      ><a name="13826"
      > </a
      ><a name="13827" class="Symbol"
      >(</a
      ><a name="13828" href="Stlc.html#3672" class="InductiveConstructor Operator"
      >&#955;[</a
      ><a name="13830"
      > </a
      ><a name="13831" href="Stlc.html#5679" class="Function"
      >x</a
      ><a name="13832"
      > </a
      ><a name="13833" href="Stlc.html#3672" class="InductiveConstructor Operator"
      >&#8758;</a
      ><a name="13834"
      > </a
      ><a name="13835" href="Stlc.html#2610" class="InductiveConstructor"
      >&#120121;</a
      ><a name="13836"
      > </a
      ><a name="13837" href="Stlc.html#3672" class="InductiveConstructor Operator"
      >]</a
      ><a name="13838"
      > </a
      ><a name="13839" href="Stlc.html#3656" class="InductiveConstructor"
      >`</a
      ><a name="13840"
      > </a
      ><a name="13841" href="Stlc.html#5679" class="Function"
      >x</a
      ><a name="13842" class="Symbol"
      >)</a
      ><a name="13843"
      > </a
      ><a name="13844" href="Stlc.html#12263" class="Function Operator"
      >[</a
      ><a name="13845"
      > </a
      ><a name="13846" href="Stlc.html#5679" class="Function"
      >x</a
      ><a name="13847"
      > </a
      ><a name="13848" href="Stlc.html#12263" class="Function Operator"
      >:=</a
      ><a name="13850"
      > </a
      ><a name="13851" href="Stlc.html#3735" class="InductiveConstructor"
      >true</a
      ><a name="13855"
      > </a
      ><a name="13856" href="Stlc.html#12263" class="Function Operator"
      >]</a
      ><a name="13857"
      > </a
      ><a name="13858" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="13859"
      > </a
      ><a name="13860" href="Stlc.html#3672" class="InductiveConstructor Operator"
      >&#955;[</a
      ><a name="13862"
      > </a
      ><a name="13863" href="Stlc.html#5679" class="Function"
      >x</a
      ><a name="13864"
      > </a
      ><a name="13865" href="Stlc.html#3672" class="InductiveConstructor Operator"
      >&#8758;</a
      ><a name="13866"
      > </a
      ><a name="13867" href="Stlc.html#2610" class="InductiveConstructor"
      >&#120121;</a
      ><a name="13868"
      > </a
      ><a name="13869" href="Stlc.html#3672" class="InductiveConstructor Operator"
      >]</a
      ><a name="13870"
      > </a
      ><a name="13871" href="Stlc.html#3656" class="InductiveConstructor"
      >`</a
      ><a name="13872"
      > </a
      ><a name="13873" href="Stlc.html#5679" class="Function"
      >x</a
      ><a name="13874"
      >
</a
      ><a name="13875" href="Stlc.html#13820" class="Function"
      >ex&#8321;&#8327;</a
      ><a name="13879"
      > </a
      ><a name="13880" class="Symbol"
      >=</a
      ><a name="13881"
      > </a
      ><a name="13882" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
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
<a name="15996" class="Keyword"
      >infix</a
      ><a name="16001"
      > </a
      ><a name="16002" class="Number"
      >10</a
      ><a name="16004"
      > </a
      ><a name="16005" href="Stlc.html#16016" class="Datatype Operator"
      >_&#10233;_</a
      ><a name="16008"
      > 

</a
      ><a name="16011" class="Keyword"
      >data</a
      ><a name="16015"
      > </a
      ><a name="16016" href="Stlc.html#16016" class="Datatype Operator"
      >_&#10233;_</a
      ><a name="16019"
      > </a
      ><a name="16020" class="Symbol"
      >:</a
      ><a name="16021"
      > </a
      ><a name="16022" href="Stlc.html#3637" class="Datatype"
      >Term</a
      ><a name="16026"
      > </a
      ><a name="16027" class="Symbol"
      >&#8594;</a
      ><a name="16028"
      > </a
      ><a name="16029" href="Stlc.html#3637" class="Datatype"
      >Term</a
      ><a name="16033"
      > </a
      ><a name="16034" class="Symbol"
      >&#8594;</a
      ><a name="16035"
      > </a
      ><a name="16036" class="PrimitiveType"
      >Set</a
      ><a name="16039"
      > </a
      ><a name="16040" class="Keyword"
      >where</a
      ><a name="16045"
      >
  </a
      ><a name="16048" href="Stlc.html#16048" class="InductiveConstructor"
      >&#958;&#183;&#8321;</a
      ><a name="16051"
      > </a
      ><a name="16052" class="Symbol"
      >:</a
      ><a name="16053"
      > </a
      ><a name="16054" class="Symbol"
      >&#8704;</a
      ><a name="16055"
      > </a
      ><a name="16056" class="Symbol"
      >{</a
      ><a name="16057" href="Stlc.html#16057" class="Bound"
      >L</a
      ><a name="16058"
      > </a
      ><a name="16059" href="Stlc.html#16059" class="Bound"
      >L&#8242;</a
      ><a name="16061"
      > </a
      ><a name="16062" href="Stlc.html#16062" class="Bound"
      >M</a
      ><a name="16063" class="Symbol"
      >}</a
      ><a name="16064"
      > </a
      ><a name="16065" class="Symbol"
      >&#8594;</a
      ><a name="16066"
      >
    </a
      ><a name="16071" href="Stlc.html#16057" class="Bound"
      >L</a
      ><a name="16072"
      > </a
      ><a name="16073" href="Stlc.html#16016" class="Datatype Operator"
      >&#10233;</a
      ><a name="16074"
      > </a
      ><a name="16075" href="Stlc.html#16059" class="Bound"
      >L&#8242;</a
      ><a name="16077"
      > </a
      ><a name="16078" class="Symbol"
      >&#8594;</a
      ><a name="16079"
      >
    </a
      ><a name="16084" href="Stlc.html#16057" class="Bound"
      >L</a
      ><a name="16085"
      > </a
      ><a name="16086" href="Stlc.html#3708" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="16087"
      > </a
      ><a name="16088" href="Stlc.html#16062" class="Bound"
      >M</a
      ><a name="16089"
      > </a
      ><a name="16090" href="Stlc.html#16016" class="Datatype Operator"
      >&#10233;</a
      ><a name="16091"
      > </a
      ><a name="16092" href="Stlc.html#16059" class="Bound"
      >L&#8242;</a
      ><a name="16094"
      > </a
      ><a name="16095" href="Stlc.html#3708" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="16096"
      > </a
      ><a name="16097" href="Stlc.html#16062" class="Bound"
      >M</a
      ><a name="16098"
      >
  </a
      ><a name="16101" href="Stlc.html#16101" class="InductiveConstructor"
      >&#958;&#183;&#8322;</a
      ><a name="16104"
      > </a
      ><a name="16105" class="Symbol"
      >:</a
      ><a name="16106"
      > </a
      ><a name="16107" class="Symbol"
      >&#8704;</a
      ><a name="16108"
      > </a
      ><a name="16109" class="Symbol"
      >{</a
      ><a name="16110" href="Stlc.html#16110" class="Bound"
      >V</a
      ><a name="16111"
      > </a
      ><a name="16112" href="Stlc.html#16112" class="Bound"
      >M</a
      ><a name="16113"
      > </a
      ><a name="16114" href="Stlc.html#16114" class="Bound"
      >M&#8242;</a
      ><a name="16116" class="Symbol"
      >}</a
      ><a name="16117"
      > </a
      ><a name="16118" class="Symbol"
      >&#8594;</a
      ><a name="16119"
      >
    </a
      ><a name="16124" href="Stlc.html#9719" class="Datatype"
      >Value</a
      ><a name="16129"
      > </a
      ><a name="16130" href="Stlc.html#16110" class="Bound"
      >V</a
      ><a name="16131"
      > </a
      ><a name="16132" class="Symbol"
      >&#8594;</a
      ><a name="16133"
      >
    </a
      ><a name="16138" href="Stlc.html#16112" class="Bound"
      >M</a
      ><a name="16139"
      > </a
      ><a name="16140" href="Stlc.html#16016" class="Datatype Operator"
      >&#10233;</a
      ><a name="16141"
      > </a
      ><a name="16142" href="Stlc.html#16114" class="Bound"
      >M&#8242;</a
      ><a name="16144"
      > </a
      ><a name="16145" class="Symbol"
      >&#8594;</a
      ><a name="16146"
      >
    </a
      ><a name="16151" href="Stlc.html#16110" class="Bound"
      >V</a
      ><a name="16152"
      > </a
      ><a name="16153" href="Stlc.html#3708" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="16154"
      > </a
      ><a name="16155" href="Stlc.html#16112" class="Bound"
      >M</a
      ><a name="16156"
      > </a
      ><a name="16157" href="Stlc.html#16016" class="Datatype Operator"
      >&#10233;</a
      ><a name="16158"
      > </a
      ><a name="16159" href="Stlc.html#16110" class="Bound"
      >V</a
      ><a name="16160"
      > </a
      ><a name="16161" href="Stlc.html#3708" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="16162"
      > </a
      ><a name="16163" href="Stlc.html#16114" class="Bound"
      >M&#8242;</a
      ><a name="16165"
      >
  </a
      ><a name="16168" href="Stlc.html#16168" class="InductiveConstructor"
      >&#946;&#955;&#183;</a
      ><a name="16171"
      > </a
      ><a name="16172" class="Symbol"
      >:</a
      ><a name="16173"
      > </a
      ><a name="16174" class="Symbol"
      >&#8704;</a
      ><a name="16175"
      > </a
      ><a name="16176" class="Symbol"
      >{</a
      ><a name="16177" href="Stlc.html#16177" class="Bound"
      >x</a
      ><a name="16178"
      > </a
      ><a name="16179" href="Stlc.html#16179" class="Bound"
      >A</a
      ><a name="16180"
      > </a
      ><a name="16181" href="Stlc.html#16181" class="Bound"
      >N</a
      ><a name="16182"
      > </a
      ><a name="16183" href="Stlc.html#16183" class="Bound"
      >V</a
      ><a name="16184" class="Symbol"
      >}</a
      ><a name="16185"
      > </a
      ><a name="16186" class="Symbol"
      >&#8594;</a
      ><a name="16187"
      > </a
      ><a name="16188" href="Stlc.html#9719" class="Datatype"
      >Value</a
      ><a name="16193"
      > </a
      ><a name="16194" href="Stlc.html#16183" class="Bound"
      >V</a
      ><a name="16195"
      > </a
      ><a name="16196" class="Symbol"
      >&#8594;</a
      ><a name="16197"
      >
    </a
      ><a name="16202" class="Symbol"
      >(</a
      ><a name="16203" href="Stlc.html#3672" class="InductiveConstructor Operator"
      >&#955;[</a
      ><a name="16205"
      > </a
      ><a name="16206" href="Stlc.html#16177" class="Bound"
      >x</a
      ><a name="16207"
      > </a
      ><a name="16208" href="Stlc.html#3672" class="InductiveConstructor Operator"
      >&#8758;</a
      ><a name="16209"
      > </a
      ><a name="16210" href="Stlc.html#16179" class="Bound"
      >A</a
      ><a name="16211"
      > </a
      ><a name="16212" href="Stlc.html#3672" class="InductiveConstructor Operator"
      >]</a
      ><a name="16213"
      > </a
      ><a name="16214" href="Stlc.html#16181" class="Bound"
      >N</a
      ><a name="16215" class="Symbol"
      >)</a
      ><a name="16216"
      > </a
      ><a name="16217" href="Stlc.html#3708" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="16218"
      > </a
      ><a name="16219" href="Stlc.html#16183" class="Bound"
      >V</a
      ><a name="16220"
      > </a
      ><a name="16221" href="Stlc.html#16016" class="Datatype Operator"
      >&#10233;</a
      ><a name="16222"
      > </a
      ><a name="16223" href="Stlc.html#16181" class="Bound"
      >N</a
      ><a name="16224"
      > </a
      ><a name="16225" href="Stlc.html#12263" class="Function Operator"
      >[</a
      ><a name="16226"
      > </a
      ><a name="16227" href="Stlc.html#16177" class="Bound"
      >x</a
      ><a name="16228"
      > </a
      ><a name="16229" href="Stlc.html#12263" class="Function Operator"
      >:=</a
      ><a name="16231"
      > </a
      ><a name="16232" href="Stlc.html#16183" class="Bound"
      >V</a
      ><a name="16233"
      > </a
      ><a name="16234" href="Stlc.html#12263" class="Function Operator"
      >]</a
      ><a name="16235"
      >
  </a
      ><a name="16238" href="Stlc.html#16238" class="InductiveConstructor"
      >&#958;if</a
      ><a name="16241"
      > </a
      ><a name="16242" class="Symbol"
      >:</a
      ><a name="16243"
      > </a
      ><a name="16244" class="Symbol"
      >&#8704;</a
      ><a name="16245"
      > </a
      ><a name="16246" class="Symbol"
      >{</a
      ><a name="16247" href="Stlc.html#16247" class="Bound"
      >L</a
      ><a name="16248"
      > </a
      ><a name="16249" href="Stlc.html#16249" class="Bound"
      >L&#8242;</a
      ><a name="16251"
      > </a
      ><a name="16252" href="Stlc.html#16252" class="Bound"
      >M</a
      ><a name="16253"
      > </a
      ><a name="16254" href="Stlc.html#16254" class="Bound"
      >N</a
      ><a name="16255" class="Symbol"
      >}</a
      ><a name="16256"
      > </a
      ><a name="16257" class="Symbol"
      >&#8594;</a
      ><a name="16258"
      >
    </a
      ><a name="16263" href="Stlc.html#16247" class="Bound"
      >L</a
      ><a name="16264"
      > </a
      ><a name="16265" href="Stlc.html#16016" class="Datatype Operator"
      >&#10233;</a
      ><a name="16266"
      > </a
      ><a name="16267" href="Stlc.html#16249" class="Bound"
      >L&#8242;</a
      ><a name="16269"
      > </a
      ><a name="16270" class="Symbol"
      >&#8594;</a
      ><a name="16271"
      >    
    </a
      ><a name="16280" href="Stlc.html#3764" class="InductiveConstructor Operator"
      >if</a
      ><a name="16282"
      > </a
      ><a name="16283" href="Stlc.html#16247" class="Bound"
      >L</a
      ><a name="16284"
      > </a
      ><a name="16285" href="Stlc.html#3764" class="InductiveConstructor Operator"
      >then</a
      ><a name="16289"
      > </a
      ><a name="16290" href="Stlc.html#16252" class="Bound"
      >M</a
      ><a name="16291"
      > </a
      ><a name="16292" href="Stlc.html#3764" class="InductiveConstructor Operator"
      >else</a
      ><a name="16296"
      > </a
      ><a name="16297" href="Stlc.html#16254" class="Bound"
      >N</a
      ><a name="16298"
      > </a
      ><a name="16299" href="Stlc.html#16016" class="Datatype Operator"
      >&#10233;</a
      ><a name="16300"
      > </a
      ><a name="16301" href="Stlc.html#3764" class="InductiveConstructor Operator"
      >if</a
      ><a name="16303"
      > </a
      ><a name="16304" href="Stlc.html#16249" class="Bound"
      >L&#8242;</a
      ><a name="16306"
      > </a
      ><a name="16307" href="Stlc.html#3764" class="InductiveConstructor Operator"
      >then</a
      ><a name="16311"
      > </a
      ><a name="16312" href="Stlc.html#16252" class="Bound"
      >M</a
      ><a name="16313"
      > </a
      ><a name="16314" href="Stlc.html#3764" class="InductiveConstructor Operator"
      >else</a
      ><a name="16318"
      > </a
      ><a name="16319" href="Stlc.html#16254" class="Bound"
      >N</a
      ><a name="16320"
      >
  </a
      ><a name="16323" href="Stlc.html#16323" class="InductiveConstructor"
      >&#946;if-true</a
      ><a name="16331"
      > </a
      ><a name="16332" class="Symbol"
      >:</a
      ><a name="16333"
      > </a
      ><a name="16334" class="Symbol"
      >&#8704;</a
      ><a name="16335"
      > </a
      ><a name="16336" class="Symbol"
      >{</a
      ><a name="16337" href="Stlc.html#16337" class="Bound"
      >M</a
      ><a name="16338"
      > </a
      ><a name="16339" href="Stlc.html#16339" class="Bound"
      >N</a
      ><a name="16340" class="Symbol"
      >}</a
      ><a name="16341"
      > </a
      ><a name="16342" class="Symbol"
      >&#8594;</a
      ><a name="16343"
      >
    </a
      ><a name="16348" href="Stlc.html#3764" class="InductiveConstructor Operator"
      >if</a
      ><a name="16350"
      > </a
      ><a name="16351" href="Stlc.html#3735" class="InductiveConstructor"
      >true</a
      ><a name="16355"
      > </a
      ><a name="16356" href="Stlc.html#3764" class="InductiveConstructor Operator"
      >then</a
      ><a name="16360"
      > </a
      ><a name="16361" href="Stlc.html#16337" class="Bound"
      >M</a
      ><a name="16362"
      > </a
      ><a name="16363" href="Stlc.html#3764" class="InductiveConstructor Operator"
      >else</a
      ><a name="16367"
      > </a
      ><a name="16368" href="Stlc.html#16339" class="Bound"
      >N</a
      ><a name="16369"
      > </a
      ><a name="16370" href="Stlc.html#16016" class="Datatype Operator"
      >&#10233;</a
      ><a name="16371"
      > </a
      ><a name="16372" href="Stlc.html#16337" class="Bound"
      >M</a
      ><a name="16373"
      >
  </a
      ><a name="16376" href="Stlc.html#16376" class="InductiveConstructor"
      >&#946;if-false</a
      ><a name="16385"
      > </a
      ><a name="16386" class="Symbol"
      >:</a
      ><a name="16387"
      > </a
      ><a name="16388" class="Symbol"
      >&#8704;</a
      ><a name="16389"
      > </a
      ><a name="16390" class="Symbol"
      >{</a
      ><a name="16391" href="Stlc.html#16391" class="Bound"
      >M</a
      ><a name="16392"
      > </a
      ><a name="16393" href="Stlc.html#16393" class="Bound"
      >N</a
      ><a name="16394" class="Symbol"
      >}</a
      ><a name="16395"
      > </a
      ><a name="16396" class="Symbol"
      >&#8594;</a
      ><a name="16397"
      >
    </a
      ><a name="16402" href="Stlc.html#3764" class="InductiveConstructor Operator"
      >if</a
      ><a name="16404"
      > </a
      ><a name="16405" href="Stlc.html#3749" class="InductiveConstructor"
      >false</a
      ><a name="16410"
      > </a
      ><a name="16411" href="Stlc.html#3764" class="InductiveConstructor Operator"
      >then</a
      ><a name="16415"
      > </a
      ><a name="16416" href="Stlc.html#16391" class="Bound"
      >M</a
      ><a name="16417"
      > </a
      ><a name="16418" href="Stlc.html#3764" class="InductiveConstructor Operator"
      >else</a
      ><a name="16422"
      > </a
      ><a name="16423" href="Stlc.html#16393" class="Bound"
      >N</a
      ><a name="16424"
      > </a
      ><a name="16425" href="Stlc.html#16016" class="Datatype Operator"
      >&#10233;</a
      ><a name="16426"
      > </a
      ><a name="16427" href="Stlc.html#16393" class="Bound"
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
<a name="18001" class="Keyword"
      >infix</a
      ><a name="18006"
      > </a
      ><a name="18007" class="Number"
      >10</a
      ><a name="18009"
      > </a
      ><a name="18010" href="Stlc.html#18050" class="Datatype Operator"
      >_&#10233;*_</a
      ><a name="18014"
      > 
</a
      ><a name="18016" class="Keyword"
      >infixr</a
      ><a name="18022"
      > </a
      ><a name="18023" class="Number"
      >2</a
      ><a name="18024"
      > </a
      ><a name="18025" href="Stlc.html#18103" class="InductiveConstructor Operator"
      >_&#10233;&#10216;_&#10217;_</a
      ><a name="18031"
      >
</a
      ><a name="18032" class="Keyword"
      >infix</a
      ><a name="18037"
      >  </a
      ><a name="18039" class="Number"
      >3</a
      ><a name="18040"
      > </a
      ><a name="18041" href="Stlc.html#18083" class="InductiveConstructor Operator"
      >_&#8718;</a
      ><a name="18043"
      >

</a
      ><a name="18045" class="Keyword"
      >data</a
      ><a name="18049"
      > </a
      ><a name="18050" href="Stlc.html#18050" class="Datatype Operator"
      >_&#10233;*_</a
      ><a name="18054"
      > </a
      ><a name="18055" class="Symbol"
      >:</a
      ><a name="18056"
      > </a
      ><a name="18057" href="Stlc.html#3637" class="Datatype"
      >Term</a
      ><a name="18061"
      > </a
      ><a name="18062" class="Symbol"
      >&#8594;</a
      ><a name="18063"
      > </a
      ><a name="18064" href="Stlc.html#3637" class="Datatype"
      >Term</a
      ><a name="18068"
      > </a
      ><a name="18069" class="Symbol"
      >&#8594;</a
      ><a name="18070"
      > </a
      ><a name="18071" class="PrimitiveType"
      >Set</a
      ><a name="18074"
      > </a
      ><a name="18075" class="Keyword"
      >where</a
      ><a name="18080"
      >
  </a
      ><a name="18083" href="Stlc.html#18083" class="InductiveConstructor Operator"
      >_&#8718;</a
      ><a name="18085"
      > </a
      ><a name="18086" class="Symbol"
      >:</a
      ><a name="18087"
      > </a
      ><a name="18088" class="Symbol"
      >&#8704;</a
      ><a name="18089"
      > </a
      ><a name="18090" href="Stlc.html#18090" class="Bound"
      >M</a
      ><a name="18091"
      > </a
      ><a name="18092" class="Symbol"
      >&#8594;</a
      ><a name="18093"
      > </a
      ><a name="18094" href="Stlc.html#18090" class="Bound"
      >M</a
      ><a name="18095"
      > </a
      ><a name="18096" href="Stlc.html#18050" class="Datatype Operator"
      >&#10233;*</a
      ><a name="18098"
      > </a
      ><a name="18099" href="Stlc.html#18090" class="Bound"
      >M</a
      ><a name="18100"
      >
  </a
      ><a name="18103" href="Stlc.html#18103" class="InductiveConstructor Operator"
      >_&#10233;&#10216;_&#10217;_</a
      ><a name="18109"
      > </a
      ><a name="18110" class="Symbol"
      >:</a
      ><a name="18111"
      > </a
      ><a name="18112" class="Symbol"
      >&#8704;</a
      ><a name="18113"
      > </a
      ><a name="18114" href="Stlc.html#18114" class="Bound"
      >L</a
      ><a name="18115"
      > </a
      ><a name="18116" class="Symbol"
      >{</a
      ><a name="18117" href="Stlc.html#18117" class="Bound"
      >M</a
      ><a name="18118"
      > </a
      ><a name="18119" href="Stlc.html#18119" class="Bound"
      >N</a
      ><a name="18120" class="Symbol"
      >}</a
      ><a name="18121"
      > </a
      ><a name="18122" class="Symbol"
      >&#8594;</a
      ><a name="18123"
      > </a
      ><a name="18124" href="Stlc.html#18114" class="Bound"
      >L</a
      ><a name="18125"
      > </a
      ><a name="18126" href="Stlc.html#16016" class="Datatype Operator"
      >&#10233;</a
      ><a name="18127"
      > </a
      ><a name="18128" href="Stlc.html#18117" class="Bound"
      >M</a
      ><a name="18129"
      > </a
      ><a name="18130" class="Symbol"
      >&#8594;</a
      ><a name="18131"
      > </a
      ><a name="18132" href="Stlc.html#18117" class="Bound"
      >M</a
      ><a name="18133"
      > </a
      ><a name="18134" href="Stlc.html#18050" class="Datatype Operator"
      >&#10233;*</a
      ><a name="18136"
      > </a
      ><a name="18137" href="Stlc.html#18119" class="Bound"
      >N</a
      ><a name="18138"
      > </a
      ><a name="18139" class="Symbol"
      >&#8594;</a
      ><a name="18140"
      > </a
      ><a name="18141" href="Stlc.html#18114" class="Bound"
      >L</a
      ><a name="18142"
      > </a
      ><a name="18143" href="Stlc.html#18050" class="Datatype Operator"
      >&#10233;*</a
      ><a name="18145"
      > </a
      ><a name="18146" href="Stlc.html#18119" class="Bound"
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
<a name="18607" href="Stlc.html#18607" class="Function"
      >reduction&#8321;</a
      ><a name="18617"
      > </a
      ><a name="18618" class="Symbol"
      >:</a
      ><a name="18619"
      > </a
      ><a name="18620" href="Stlc.html#5722" class="Function"
      >not</a
      ><a name="18623"
      > </a
      ><a name="18624" href="Stlc.html#3708" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="18625"
      > </a
      ><a name="18626" href="Stlc.html#3735" class="InductiveConstructor"
      >true</a
      ><a name="18630"
      > </a
      ><a name="18631" href="Stlc.html#18050" class="Datatype Operator"
      >&#10233;*</a
      ><a name="18633"
      > </a
      ><a name="18634" href="Stlc.html#3749" class="InductiveConstructor"
      >false</a
      ><a name="18639"
      >
</a
      ><a name="18640" href="Stlc.html#18607" class="Function"
      >reduction&#8321;</a
      ><a name="18650"
      > </a
      ><a name="18651" class="Symbol"
      >=</a
      ><a name="18652"
      >
    </a
      ><a name="18657" href="Stlc.html#5722" class="Function"
      >not</a
      ><a name="18660"
      > </a
      ><a name="18661" href="Stlc.html#3708" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="18662"
      > </a
      ><a name="18663" href="Stlc.html#3735" class="InductiveConstructor"
      >true</a
      ><a name="18667"
      >
  </a
      ><a name="18670" href="Stlc.html#18103" class="InductiveConstructor Operator"
      >&#10233;&#10216;</a
      ><a name="18672"
      > </a
      ><a name="18673" href="Stlc.html#16168" class="InductiveConstructor"
      >&#946;&#955;&#183;</a
      ><a name="18676"
      > </a
      ><a name="18677" href="Stlc.html#9795" class="InductiveConstructor"
      >value-true</a
      ><a name="18687"
      > </a
      ><a name="18688" href="Stlc.html#18103" class="InductiveConstructor Operator"
      >&#10217;</a
      ><a name="18689"
      >
    </a
      ><a name="18694" href="Stlc.html#3764" class="InductiveConstructor Operator"
      >if</a
      ><a name="18696"
      > </a
      ><a name="18697" href="Stlc.html#3735" class="InductiveConstructor"
      >true</a
      ><a name="18701"
      > </a
      ><a name="18702" href="Stlc.html#3764" class="InductiveConstructor Operator"
      >then</a
      ><a name="18706"
      > </a
      ><a name="18707" href="Stlc.html#3749" class="InductiveConstructor"
      >false</a
      ><a name="18712"
      > </a
      ><a name="18713" href="Stlc.html#3764" class="InductiveConstructor Operator"
      >else</a
      ><a name="18717"
      > </a
      ><a name="18718" href="Stlc.html#3735" class="InductiveConstructor"
      >true</a
      ><a name="18722"
      >
  </a
      ><a name="18725" href="Stlc.html#18103" class="InductiveConstructor Operator"
      >&#10233;&#10216;</a
      ><a name="18727"
      > </a
      ><a name="18728" href="Stlc.html#16323" class="InductiveConstructor"
      >&#946;if-true</a
      ><a name="18736"
      > </a
      ><a name="18737" href="Stlc.html#18103" class="InductiveConstructor Operator"
      >&#10217;</a
      ><a name="18738"
      >
    </a
      ><a name="18743" href="Stlc.html#3749" class="InductiveConstructor"
      >false</a
      ><a name="18748"
      >
  </a
      ><a name="18751" href="Stlc.html#18083" class="InductiveConstructor Operator"
      >&#8718;</a
      ><a name="18752"
      >

</a
      ><a name="18754" href="Stlc.html#18754" class="Function"
      >reduction&#8322;</a
      ><a name="18764"
      > </a
      ><a name="18765" class="Symbol"
      >:</a
      ><a name="18766"
      > </a
      ><a name="18767" href="Stlc.html#5726" class="Function"
      >two</a
      ><a name="18770"
      > </a
      ><a name="18771" href="Stlc.html#3708" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="18772"
      > </a
      ><a name="18773" href="Stlc.html#5722" class="Function"
      >not</a
      ><a name="18776"
      > </a
      ><a name="18777" href="Stlc.html#3708" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="18778"
      > </a
      ><a name="18779" href="Stlc.html#3735" class="InductiveConstructor"
      >true</a
      ><a name="18783"
      > </a
      ><a name="18784" href="Stlc.html#18050" class="Datatype Operator"
      >&#10233;*</a
      ><a name="18786"
      > </a
      ><a name="18787" href="Stlc.html#3735" class="InductiveConstructor"
      >true</a
      ><a name="18791"
      >
</a
      ><a name="18792" href="Stlc.html#18754" class="Function"
      >reduction&#8322;</a
      ><a name="18802"
      > </a
      ><a name="18803" class="Symbol"
      >=</a
      ><a name="18804"
      >
    </a
      ><a name="18809" href="Stlc.html#5726" class="Function"
      >two</a
      ><a name="18812"
      > </a
      ><a name="18813" href="Stlc.html#3708" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="18814"
      > </a
      ><a name="18815" href="Stlc.html#5722" class="Function"
      >not</a
      ><a name="18818"
      > </a
      ><a name="18819" href="Stlc.html#3708" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="18820"
      > </a
      ><a name="18821" href="Stlc.html#3735" class="InductiveConstructor"
      >true</a
      ><a name="18825"
      >
  </a
      ><a name="18828" href="Stlc.html#18103" class="InductiveConstructor Operator"
      >&#10233;&#10216;</a
      ><a name="18830"
      > </a
      ><a name="18831" href="Stlc.html#16048" class="InductiveConstructor"
      >&#958;&#183;&#8321;</a
      ><a name="18834"
      > </a
      ><a name="18835" class="Symbol"
      >(</a
      ><a name="18836" href="Stlc.html#16168" class="InductiveConstructor"
      >&#946;&#955;&#183;</a
      ><a name="18839"
      > </a
      ><a name="18840" href="Stlc.html#9746" class="InductiveConstructor"
      >value-&#955;</a
      ><a name="18847" class="Symbol"
      >)</a
      ><a name="18848"
      > </a
      ><a name="18849" href="Stlc.html#18103" class="InductiveConstructor Operator"
      >&#10217;</a
      ><a name="18850"
      >
    </a
      ><a name="18855" class="Symbol"
      >(</a
      ><a name="18856" href="Stlc.html#3672" class="InductiveConstructor Operator"
      >&#955;[</a
      ><a name="18858"
      > </a
      ><a name="18859" href="Stlc.html#5679" class="Function"
      >x</a
      ><a name="18860"
      > </a
      ><a name="18861" href="Stlc.html#3672" class="InductiveConstructor Operator"
      >&#8758;</a
      ><a name="18862"
      > </a
      ><a name="18863" href="Stlc.html#2610" class="InductiveConstructor"
      >&#120121;</a
      ><a name="18864"
      > </a
      ><a name="18865" href="Stlc.html#3672" class="InductiveConstructor Operator"
      >]</a
      ><a name="18866"
      > </a
      ><a name="18867" href="Stlc.html#5722" class="Function"
      >not</a
      ><a name="18870"
      > </a
      ><a name="18871" href="Stlc.html#3708" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="18872"
      > </a
      ><a name="18873" class="Symbol"
      >(</a
      ><a name="18874" href="Stlc.html#5722" class="Function"
      >not</a
      ><a name="18877"
      > </a
      ><a name="18878" href="Stlc.html#3708" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="18879"
      > </a
      ><a name="18880" href="Stlc.html#3656" class="InductiveConstructor"
      >`</a
      ><a name="18881"
      > </a
      ><a name="18882" href="Stlc.html#5679" class="Function"
      >x</a
      ><a name="18883" class="Symbol"
      >))</a
      ><a name="18885"
      > </a
      ><a name="18886" href="Stlc.html#3708" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="18887"
      > </a
      ><a name="18888" href="Stlc.html#3735" class="InductiveConstructor"
      >true</a
      ><a name="18892"
      >
  </a
      ><a name="18895" href="Stlc.html#18103" class="InductiveConstructor Operator"
      >&#10233;&#10216;</a
      ><a name="18897"
      > </a
      ><a name="18898" href="Stlc.html#16168" class="InductiveConstructor"
      >&#946;&#955;&#183;</a
      ><a name="18901"
      > </a
      ><a name="18902" href="Stlc.html#9795" class="InductiveConstructor"
      >value-true</a
      ><a name="18912"
      > </a
      ><a name="18913" href="Stlc.html#18103" class="InductiveConstructor Operator"
      >&#10217;</a
      ><a name="18914"
      >
    </a
      ><a name="18919" href="Stlc.html#5722" class="Function"
      >not</a
      ><a name="18922"
      > </a
      ><a name="18923" href="Stlc.html#3708" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="18924"
      > </a
      ><a name="18925" class="Symbol"
      >(</a
      ><a name="18926" href="Stlc.html#5722" class="Function"
      >not</a
      ><a name="18929"
      > </a
      ><a name="18930" href="Stlc.html#3708" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="18931"
      > </a
      ><a name="18932" href="Stlc.html#3735" class="InductiveConstructor"
      >true</a
      ><a name="18936" class="Symbol"
      >)</a
      ><a name="18937"
      >
  </a
      ><a name="18940" href="Stlc.html#18103" class="InductiveConstructor Operator"
      >&#10233;&#10216;</a
      ><a name="18942"
      > </a
      ><a name="18943" href="Stlc.html#16101" class="InductiveConstructor"
      >&#958;&#183;&#8322;</a
      ><a name="18946"
      > </a
      ><a name="18947" href="Stlc.html#9746" class="InductiveConstructor"
      >value-&#955;</a
      ><a name="18954"
      > </a
      ><a name="18955" class="Symbol"
      >(</a
      ><a name="18956" href="Stlc.html#16168" class="InductiveConstructor"
      >&#946;&#955;&#183;</a
      ><a name="18959"
      > </a
      ><a name="18960" href="Stlc.html#9795" class="InductiveConstructor"
      >value-true</a
      ><a name="18970" class="Symbol"
      >)</a
      ><a name="18971"
      > </a
      ><a name="18972" href="Stlc.html#18103" class="InductiveConstructor Operator"
      >&#10217;</a
      ><a name="18973"
      >
    </a
      ><a name="18978" href="Stlc.html#5722" class="Function"
      >not</a
      ><a name="18981"
      > </a
      ><a name="18982" href="Stlc.html#3708" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="18983"
      > </a
      ><a name="18984" class="Symbol"
      >(</a
      ><a name="18985" href="Stlc.html#3764" class="InductiveConstructor Operator"
      >if</a
      ><a name="18987"
      > </a
      ><a name="18988" href="Stlc.html#3735" class="InductiveConstructor"
      >true</a
      ><a name="18992"
      > </a
      ><a name="18993" href="Stlc.html#3764" class="InductiveConstructor Operator"
      >then</a
      ><a name="18997"
      > </a
      ><a name="18998" href="Stlc.html#3749" class="InductiveConstructor"
      >false</a
      ><a name="19003"
      > </a
      ><a name="19004" href="Stlc.html#3764" class="InductiveConstructor Operator"
      >else</a
      ><a name="19008"
      > </a
      ><a name="19009" href="Stlc.html#3735" class="InductiveConstructor"
      >true</a
      ><a name="19013" class="Symbol"
      >)</a
      ><a name="19014"
      >
  </a
      ><a name="19017" href="Stlc.html#18103" class="InductiveConstructor Operator"
      >&#10233;&#10216;</a
      ><a name="19019"
      > </a
      ><a name="19020" href="Stlc.html#16101" class="InductiveConstructor"
      >&#958;&#183;&#8322;</a
      ><a name="19023"
      > </a
      ><a name="19024" href="Stlc.html#9746" class="InductiveConstructor"
      >value-&#955;</a
      ><a name="19031"
      > </a
      ><a name="19032" href="Stlc.html#16323" class="InductiveConstructor"
      >&#946;if-true</a
      ><a name="19040"
      >  </a
      ><a name="19042" href="Stlc.html#18103" class="InductiveConstructor Operator"
      >&#10217;</a
      ><a name="19043"
      >
    </a
      ><a name="19048" href="Stlc.html#5722" class="Function"
      >not</a
      ><a name="19051"
      > </a
      ><a name="19052" href="Stlc.html#3708" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="19053"
      > </a
      ><a name="19054" href="Stlc.html#3749" class="InductiveConstructor"
      >false</a
      ><a name="19059"
      >
  </a
      ><a name="19062" href="Stlc.html#18103" class="InductiveConstructor Operator"
      >&#10233;&#10216;</a
      ><a name="19064"
      > </a
      ><a name="19065" href="Stlc.html#16168" class="InductiveConstructor"
      >&#946;&#955;&#183;</a
      ><a name="19068"
      > </a
      ><a name="19069" href="Stlc.html#9822" class="InductiveConstructor"
      >value-false</a
      ><a name="19080"
      > </a
      ><a name="19081" href="Stlc.html#18103" class="InductiveConstructor Operator"
      >&#10217;</a
      ><a name="19082"
      >
    </a
      ><a name="19087" href="Stlc.html#3764" class="InductiveConstructor Operator"
      >if</a
      ><a name="19089"
      > </a
      ><a name="19090" href="Stlc.html#3749" class="InductiveConstructor"
      >false</a
      ><a name="19095"
      > </a
      ><a name="19096" href="Stlc.html#3764" class="InductiveConstructor Operator"
      >then</a
      ><a name="19100"
      > </a
      ><a name="19101" href="Stlc.html#3749" class="InductiveConstructor"
      >false</a
      ><a name="19106"
      > </a
      ><a name="19107" href="Stlc.html#3764" class="InductiveConstructor Operator"
      >else</a
      ><a name="19111"
      > </a
      ><a name="19112" href="Stlc.html#3735" class="InductiveConstructor"
      >true</a
      ><a name="19116"
      >
  </a
      ><a name="19119" href="Stlc.html#18103" class="InductiveConstructor Operator"
      >&#10233;&#10216;</a
      ><a name="19121"
      > </a
      ><a name="19122" href="Stlc.html#16376" class="InductiveConstructor"
      >&#946;if-false</a
      ><a name="19131"
      > </a
      ><a name="19132" href="Stlc.html#18103" class="InductiveConstructor Operator"
      >&#10217;</a
      ><a name="19133"
      >
    </a
      ><a name="19138" href="Stlc.html#3735" class="InductiveConstructor"
      >true</a
      ><a name="19142"
      >
  </a
      ><a name="19145" href="Stlc.html#18083" class="InductiveConstructor Operator"
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
<a name="21691" href="Stlc.html#21691" class="Function"
      >Context</a
      ><a name="21698"
      > </a
      ><a name="21699" class="Symbol"
      >:</a
      ><a name="21700"
      > </a
      ><a name="21701" class="PrimitiveType"
      >Set</a
      ><a name="21704"
      >
</a
      ><a name="21705" href="Stlc.html#21691" class="Function"
      >Context</a
      ><a name="21712"
      > </a
      ><a name="21713" class="Symbol"
      >=</a
      ><a name="21714"
      > </a
      ><a name="21715" href="Maps.html#10132" class="Function"
      >PartialMap</a
      ><a name="21725"
      > </a
      ><a name="21726" href="Stlc.html#2564" class="Datatype"
      >Type</a
      ><a name="21730"
      >

</a
      ><a name="21732" class="Keyword"
      >infix</a
      ><a name="21737"
      > </a
      ><a name="21738" class="Number"
      >10</a
      ><a name="21740"
      > </a
      ><a name="21741" href="Stlc.html#21753" class="Datatype Operator"
      >_&#8866;_&#8758;_</a
      ><a name="21746"
      >

</a
      ><a name="21748" class="Keyword"
      >data</a
      ><a name="21752"
      > </a
      ><a name="21753" href="Stlc.html#21753" class="Datatype Operator"
      >_&#8866;_&#8758;_</a
      ><a name="21758"
      > </a
      ><a name="21759" class="Symbol"
      >:</a
      ><a name="21760"
      > </a
      ><a name="21761" href="Stlc.html#21691" class="Function"
      >Context</a
      ><a name="21768"
      > </a
      ><a name="21769" class="Symbol"
      >&#8594;</a
      ><a name="21770"
      > </a
      ><a name="21771" href="Stlc.html#3637" class="Datatype"
      >Term</a
      ><a name="21775"
      > </a
      ><a name="21776" class="Symbol"
      >&#8594;</a
      ><a name="21777"
      > </a
      ><a name="21778" href="Stlc.html#2564" class="Datatype"
      >Type</a
      ><a name="21782"
      > </a
      ><a name="21783" class="Symbol"
      >&#8594;</a
      ><a name="21784"
      > </a
      ><a name="21785" class="PrimitiveType"
      >Set</a
      ><a name="21788"
      > </a
      ><a name="21789" class="Keyword"
      >where</a
      ><a name="21794"
      >
  </a
      ><a name="21797" href="Stlc.html#21797" class="InductiveConstructor"
      >Ax</a
      ><a name="21799"
      > </a
      ><a name="21800" class="Symbol"
      >:</a
      ><a name="21801"
      > </a
      ><a name="21802" class="Symbol"
      >&#8704;</a
      ><a name="21803"
      > </a
      ><a name="21804" class="Symbol"
      >{</a
      ><a name="21805" href="Stlc.html#21805" class="Bound"
      >&#915;</a
      ><a name="21806"
      > </a
      ><a name="21807" href="Stlc.html#21807" class="Bound"
      >x</a
      ><a name="21808"
      > </a
      ><a name="21809" href="Stlc.html#21809" class="Bound"
      >A</a
      ><a name="21810" class="Symbol"
      >}</a
      ><a name="21811"
      > </a
      ><a name="21812" class="Symbol"
      >&#8594;</a
      ><a name="21813"
      >
    </a
      ><a name="21818" href="Stlc.html#21805" class="Bound"
      >&#915;</a
      ><a name="21819"
      > </a
      ><a name="21820" href="Stlc.html#21807" class="Bound"
      >x</a
      ><a name="21821"
      > </a
      ><a name="21822" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="21823"
      > </a
      ><a name="21824" href="https://agda.github.io/agda-stdlib/Data.Maybe.Base.html#373" class="InductiveConstructor"
      >just</a
      ><a name="21828"
      > </a
      ><a name="21829" href="Stlc.html#21809" class="Bound"
      >A</a
      ><a name="21830"
      > </a
      ><a name="21831" class="Symbol"
      >&#8594;</a
      ><a name="21832"
      >
    </a
      ><a name="21837" href="Stlc.html#21805" class="Bound"
      >&#915;</a
      ><a name="21838"
      > </a
      ><a name="21839" href="Stlc.html#21753" class="Datatype Operator"
      >&#8866;</a
      ><a name="21840"
      > </a
      ><a name="21841" href="Stlc.html#3656" class="InductiveConstructor"
      >`</a
      ><a name="21842"
      > </a
      ><a name="21843" href="Stlc.html#21807" class="Bound"
      >x</a
      ><a name="21844"
      > </a
      ><a name="21845" href="Stlc.html#21753" class="Datatype Operator"
      >&#8758;</a
      ><a name="21846"
      > </a
      ><a name="21847" href="Stlc.html#21809" class="Bound"
      >A</a
      ><a name="21848"
      >
  </a
      ><a name="21851" href="Stlc.html#21851" class="InductiveConstructor"
      >&#8658;-I</a
      ><a name="21854"
      > </a
      ><a name="21855" class="Symbol"
      >:</a
      ><a name="21856"
      > </a
      ><a name="21857" class="Symbol"
      >&#8704;</a
      ><a name="21858"
      > </a
      ><a name="21859" class="Symbol"
      >{</a
      ><a name="21860" href="Stlc.html#21860" class="Bound"
      >&#915;</a
      ><a name="21861"
      > </a
      ><a name="21862" href="Stlc.html#21862" class="Bound"
      >x</a
      ><a name="21863"
      > </a
      ><a name="21864" href="Stlc.html#21864" class="Bound"
      >N</a
      ><a name="21865"
      > </a
      ><a name="21866" href="Stlc.html#21866" class="Bound"
      >A</a
      ><a name="21867"
      > </a
      ><a name="21868" href="Stlc.html#21868" class="Bound"
      >B</a
      ><a name="21869" class="Symbol"
      >}</a
      ><a name="21870"
      > </a
      ><a name="21871" class="Symbol"
      >&#8594;</a
      ><a name="21872"
      >
    </a
      ><a name="21877" href="Stlc.html#21860" class="Bound"
      >&#915;</a
      ><a name="21878"
      > </a
      ><a name="21879" href="Maps.html#10368" class="Function Operator"
      >,</a
      ><a name="21880"
      > </a
      ><a name="21881" href="Stlc.html#21862" class="Bound"
      >x</a
      ><a name="21882"
      > </a
      ><a name="21883" href="Maps.html#10368" class="Function Operator"
      >&#8758;</a
      ><a name="21884"
      > </a
      ><a name="21885" href="Stlc.html#21866" class="Bound"
      >A</a
      ><a name="21886"
      > </a
      ><a name="21887" href="Stlc.html#21753" class="Datatype Operator"
      >&#8866;</a
      ><a name="21888"
      > </a
      ><a name="21889" href="Stlc.html#21864" class="Bound"
      >N</a
      ><a name="21890"
      > </a
      ><a name="21891" href="Stlc.html#21753" class="Datatype Operator"
      >&#8758;</a
      ><a name="21892"
      > </a
      ><a name="21893" href="Stlc.html#21868" class="Bound"
      >B</a
      ><a name="21894"
      > </a
      ><a name="21895" class="Symbol"
      >&#8594;</a
      ><a name="21896"
      >
    </a
      ><a name="21901" href="Stlc.html#21860" class="Bound"
      >&#915;</a
      ><a name="21902"
      > </a
      ><a name="21903" href="Stlc.html#21753" class="Datatype Operator"
      >&#8866;</a
      ><a name="21904"
      > </a
      ><a name="21905" href="Stlc.html#3672" class="InductiveConstructor Operator"
      >&#955;[</a
      ><a name="21907"
      > </a
      ><a name="21908" href="Stlc.html#21862" class="Bound"
      >x</a
      ><a name="21909"
      > </a
      ><a name="21910" href="Stlc.html#3672" class="InductiveConstructor Operator"
      >&#8758;</a
      ><a name="21911"
      > </a
      ><a name="21912" href="Stlc.html#21866" class="Bound"
      >A</a
      ><a name="21913"
      > </a
      ><a name="21914" href="Stlc.html#3672" class="InductiveConstructor Operator"
      >]</a
      ><a name="21915"
      > </a
      ><a name="21916" href="Stlc.html#21864" class="Bound"
      >N</a
      ><a name="21917"
      > </a
      ><a name="21918" href="Stlc.html#21753" class="Datatype Operator"
      >&#8758;</a
      ><a name="21919"
      > </a
      ><a name="21920" href="Stlc.html#21866" class="Bound"
      >A</a
      ><a name="21921"
      > </a
      ><a name="21922" href="Stlc.html#2583" class="InductiveConstructor Operator"
      >&#8658;</a
      ><a name="21923"
      > </a
      ><a name="21924" href="Stlc.html#21868" class="Bound"
      >B</a
      ><a name="21925"
      >
  </a
      ><a name="21928" href="Stlc.html#21928" class="InductiveConstructor"
      >&#8658;-E</a
      ><a name="21931"
      > </a
      ><a name="21932" class="Symbol"
      >:</a
      ><a name="21933"
      > </a
      ><a name="21934" class="Symbol"
      >&#8704;</a
      ><a name="21935"
      > </a
      ><a name="21936" class="Symbol"
      >{</a
      ><a name="21937" href="Stlc.html#21937" class="Bound"
      >&#915;</a
      ><a name="21938"
      > </a
      ><a name="21939" href="Stlc.html#21939" class="Bound"
      >L</a
      ><a name="21940"
      > </a
      ><a name="21941" href="Stlc.html#21941" class="Bound"
      >M</a
      ><a name="21942"
      > </a
      ><a name="21943" href="Stlc.html#21943" class="Bound"
      >A</a
      ><a name="21944"
      > </a
      ><a name="21945" href="Stlc.html#21945" class="Bound"
      >B</a
      ><a name="21946" class="Symbol"
      >}</a
      ><a name="21947"
      > </a
      ><a name="21948" class="Symbol"
      >&#8594;</a
      ><a name="21949"
      >
    </a
      ><a name="21954" href="Stlc.html#21937" class="Bound"
      >&#915;</a
      ><a name="21955"
      > </a
      ><a name="21956" href="Stlc.html#21753" class="Datatype Operator"
      >&#8866;</a
      ><a name="21957"
      > </a
      ><a name="21958" href="Stlc.html#21939" class="Bound"
      >L</a
      ><a name="21959"
      > </a
      ><a name="21960" href="Stlc.html#21753" class="Datatype Operator"
      >&#8758;</a
      ><a name="21961"
      > </a
      ><a name="21962" href="Stlc.html#21943" class="Bound"
      >A</a
      ><a name="21963"
      > </a
      ><a name="21964" href="Stlc.html#2583" class="InductiveConstructor Operator"
      >&#8658;</a
      ><a name="21965"
      > </a
      ><a name="21966" href="Stlc.html#21945" class="Bound"
      >B</a
      ><a name="21967"
      > </a
      ><a name="21968" class="Symbol"
      >&#8594;</a
      ><a name="21969"
      >
    </a
      ><a name="21974" href="Stlc.html#21937" class="Bound"
      >&#915;</a
      ><a name="21975"
      > </a
      ><a name="21976" href="Stlc.html#21753" class="Datatype Operator"
      >&#8866;</a
      ><a name="21977"
      > </a
      ><a name="21978" href="Stlc.html#21941" class="Bound"
      >M</a
      ><a name="21979"
      > </a
      ><a name="21980" href="Stlc.html#21753" class="Datatype Operator"
      >&#8758;</a
      ><a name="21981"
      > </a
      ><a name="21982" href="Stlc.html#21943" class="Bound"
      >A</a
      ><a name="21983"
      > </a
      ><a name="21984" class="Symbol"
      >&#8594;</a
      ><a name="21985"
      >
    </a
      ><a name="21990" href="Stlc.html#21937" class="Bound"
      >&#915;</a
      ><a name="21991"
      > </a
      ><a name="21992" href="Stlc.html#21753" class="Datatype Operator"
      >&#8866;</a
      ><a name="21993"
      > </a
      ><a name="21994" href="Stlc.html#21939" class="Bound"
      >L</a
      ><a name="21995"
      > </a
      ><a name="21996" href="Stlc.html#3708" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="21997"
      > </a
      ><a name="21998" href="Stlc.html#21941" class="Bound"
      >M</a
      ><a name="21999"
      > </a
      ><a name="22000" href="Stlc.html#21753" class="Datatype Operator"
      >&#8758;</a
      ><a name="22001"
      > </a
      ><a name="22002" href="Stlc.html#21945" class="Bound"
      >B</a
      ><a name="22003"
      >
  </a
      ><a name="22006" href="Stlc.html#22006" class="InductiveConstructor"
      >&#120121;-I&#8321;</a
      ><a name="22010"
      > </a
      ><a name="22011" class="Symbol"
      >:</a
      ><a name="22012"
      > </a
      ><a name="22013" class="Symbol"
      >&#8704;</a
      ><a name="22014"
      > </a
      ><a name="22015" class="Symbol"
      >{</a
      ><a name="22016" href="Stlc.html#22016" class="Bound"
      >&#915;</a
      ><a name="22017" class="Symbol"
      >}</a
      ><a name="22018"
      > </a
      ><a name="22019" class="Symbol"
      >&#8594;</a
      ><a name="22020"
      >
    </a
      ><a name="22025" href="Stlc.html#22016" class="Bound"
      >&#915;</a
      ><a name="22026"
      > </a
      ><a name="22027" href="Stlc.html#21753" class="Datatype Operator"
      >&#8866;</a
      ><a name="22028"
      > </a
      ><a name="22029" href="Stlc.html#3735" class="InductiveConstructor"
      >true</a
      ><a name="22033"
      > </a
      ><a name="22034" href="Stlc.html#21753" class="Datatype Operator"
      >&#8758;</a
      ><a name="22035"
      > </a
      ><a name="22036" href="Stlc.html#2610" class="InductiveConstructor"
      >&#120121;</a
      ><a name="22037"
      >
  </a
      ><a name="22040" href="Stlc.html#22040" class="InductiveConstructor"
      >&#120121;-I&#8322;</a
      ><a name="22044"
      > </a
      ><a name="22045" class="Symbol"
      >:</a
      ><a name="22046"
      > </a
      ><a name="22047" class="Symbol"
      >&#8704;</a
      ><a name="22048"
      > </a
      ><a name="22049" class="Symbol"
      >{</a
      ><a name="22050" href="Stlc.html#22050" class="Bound"
      >&#915;</a
      ><a name="22051" class="Symbol"
      >}</a
      ><a name="22052"
      > </a
      ><a name="22053" class="Symbol"
      >&#8594;</a
      ><a name="22054"
      >
    </a
      ><a name="22059" href="Stlc.html#22050" class="Bound"
      >&#915;</a
      ><a name="22060"
      > </a
      ><a name="22061" href="Stlc.html#21753" class="Datatype Operator"
      >&#8866;</a
      ><a name="22062"
      > </a
      ><a name="22063" href="Stlc.html#3749" class="InductiveConstructor"
      >false</a
      ><a name="22068"
      > </a
      ><a name="22069" href="Stlc.html#21753" class="Datatype Operator"
      >&#8758;</a
      ><a name="22070"
      > </a
      ><a name="22071" href="Stlc.html#2610" class="InductiveConstructor"
      >&#120121;</a
      ><a name="22072"
      >
  </a
      ><a name="22075" href="Stlc.html#22075" class="InductiveConstructor"
      >&#120121;-E</a
      ><a name="22078"
      > </a
      ><a name="22079" class="Symbol"
      >:</a
      ><a name="22080"
      > </a
      ><a name="22081" class="Symbol"
      >&#8704;</a
      ><a name="22082"
      > </a
      ><a name="22083" class="Symbol"
      >{</a
      ><a name="22084" href="Stlc.html#22084" class="Bound"
      >&#915;</a
      ><a name="22085"
      > </a
      ><a name="22086" href="Stlc.html#22086" class="Bound"
      >L</a
      ><a name="22087"
      > </a
      ><a name="22088" href="Stlc.html#22088" class="Bound"
      >M</a
      ><a name="22089"
      > </a
      ><a name="22090" href="Stlc.html#22090" class="Bound"
      >N</a
      ><a name="22091"
      > </a
      ><a name="22092" href="Stlc.html#22092" class="Bound"
      >A</a
      ><a name="22093" class="Symbol"
      >}</a
      ><a name="22094"
      > </a
      ><a name="22095" class="Symbol"
      >&#8594;</a
      ><a name="22096"
      >
    </a
      ><a name="22101" href="Stlc.html#22084" class="Bound"
      >&#915;</a
      ><a name="22102"
      > </a
      ><a name="22103" href="Stlc.html#21753" class="Datatype Operator"
      >&#8866;</a
      ><a name="22104"
      > </a
      ><a name="22105" href="Stlc.html#22086" class="Bound"
      >L</a
      ><a name="22106"
      > </a
      ><a name="22107" href="Stlc.html#21753" class="Datatype Operator"
      >&#8758;</a
      ><a name="22108"
      > </a
      ><a name="22109" href="Stlc.html#2610" class="InductiveConstructor"
      >&#120121;</a
      ><a name="22110"
      > </a
      ><a name="22111" class="Symbol"
      >&#8594;</a
      ><a name="22112"
      >
    </a
      ><a name="22117" href="Stlc.html#22084" class="Bound"
      >&#915;</a
      ><a name="22118"
      > </a
      ><a name="22119" href="Stlc.html#21753" class="Datatype Operator"
      >&#8866;</a
      ><a name="22120"
      > </a
      ><a name="22121" href="Stlc.html#22088" class="Bound"
      >M</a
      ><a name="22122"
      > </a
      ><a name="22123" href="Stlc.html#21753" class="Datatype Operator"
      >&#8758;</a
      ><a name="22124"
      > </a
      ><a name="22125" href="Stlc.html#22092" class="Bound"
      >A</a
      ><a name="22126"
      > </a
      ><a name="22127" class="Symbol"
      >&#8594;</a
      ><a name="22128"
      >
    </a
      ><a name="22133" href="Stlc.html#22084" class="Bound"
      >&#915;</a
      ><a name="22134"
      > </a
      ><a name="22135" href="Stlc.html#21753" class="Datatype Operator"
      >&#8866;</a
      ><a name="22136"
      > </a
      ><a name="22137" href="Stlc.html#22090" class="Bound"
      >N</a
      ><a name="22138"
      > </a
      ><a name="22139" href="Stlc.html#21753" class="Datatype Operator"
      >&#8758;</a
      ><a name="22140"
      > </a
      ><a name="22141" href="Stlc.html#22092" class="Bound"
      >A</a
      ><a name="22142"
      > </a
      ><a name="22143" class="Symbol"
      >&#8594;</a
      ><a name="22144"
      >
    </a
      ><a name="22149" href="Stlc.html#22084" class="Bound"
      >&#915;</a
      ><a name="22150"
      > </a
      ><a name="22151" href="Stlc.html#21753" class="Datatype Operator"
      >&#8866;</a
      ><a name="22152"
      > </a
      ><a name="22153" href="Stlc.html#3764" class="InductiveConstructor Operator"
      >if</a
      ><a name="22155"
      > </a
      ><a name="22156" href="Stlc.html#22086" class="Bound"
      >L</a
      ><a name="22157"
      > </a
      ><a name="22158" href="Stlc.html#3764" class="InductiveConstructor Operator"
      >then</a
      ><a name="22162"
      > </a
      ><a name="22163" href="Stlc.html#22088" class="Bound"
      >M</a
      ><a name="22164"
      > </a
      ><a name="22165" href="Stlc.html#3764" class="InductiveConstructor Operator"
      >else</a
      ><a name="22169"
      > </a
      ><a name="22170" href="Stlc.html#22090" class="Bound"
      >N</a
      ><a name="22171"
      > </a
      ><a name="22172" href="Stlc.html#21753" class="Datatype Operator"
      >&#8758;</a
      ><a name="22173"
      > </a
      ><a name="22174" href="Stlc.html#22092" class="Bound"
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
<a name="23457" href="Stlc.html#23457" class="Function"
      >typing&#8321;</a
      ><a name="23464"
      > </a
      ><a name="23465" class="Symbol"
      >:</a
      ><a name="23466"
      > </a
      ><a name="23467" href="Maps.html#10265" class="Function"
      >&#8709;</a
      ><a name="23468"
      > </a
      ><a name="23469" href="Stlc.html#21753" class="Datatype Operator"
      >&#8866;</a
      ><a name="23470"
      > </a
      ><a name="23471" href="Stlc.html#5722" class="Function"
      >not</a
      ><a name="23474"
      > </a
      ><a name="23475" href="Stlc.html#21753" class="Datatype Operator"
      >&#8758;</a
      ><a name="23476"
      > </a
      ><a name="23477" href="Stlc.html#2610" class="InductiveConstructor"
      >&#120121;</a
      ><a name="23478"
      > </a
      ><a name="23479" href="Stlc.html#2583" class="InductiveConstructor Operator"
      >&#8658;</a
      ><a name="23480"
      > </a
      ><a name="23481" href="Stlc.html#2610" class="InductiveConstructor"
      >&#120121;</a
      ><a name="23482"
      >
</a
      ><a name="23483" href="Stlc.html#23457" class="Function"
      >typing&#8321;</a
      ><a name="23490"
      > </a
      ><a name="23491" class="Symbol"
      >=</a
      ><a name="23492"
      > </a
      ><a name="23493" href="Stlc.html#21851" class="InductiveConstructor"
      >&#8658;-I</a
      ><a name="23496"
      > </a
      ><a name="23497" class="Symbol"
      >(</a
      ><a name="23498" href="Stlc.html#22075" class="InductiveConstructor"
      >&#120121;-E</a
      ><a name="23501"
      > </a
      ><a name="23502" class="Symbol"
      >(</a
      ><a name="23503" href="Stlc.html#21797" class="InductiveConstructor"
      >Ax</a
      ><a name="23505"
      > </a
      ><a name="23506" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="23510" class="Symbol"
      >)</a
      ><a name="23511"
      > </a
      ><a name="23512" href="Stlc.html#22040" class="InductiveConstructor"
      >&#120121;-I&#8322;</a
      ><a name="23516"
      > </a
      ><a name="23517" href="Stlc.html#22006" class="InductiveConstructor"
      >&#120121;-I&#8321;</a
      ><a name="23521" class="Symbol"
      >)</a
      ><a name="23522"
      >

</a
      ><a name="23524" href="Stlc.html#23524" class="Function"
      >typing&#8322;</a
      ><a name="23531"
      > </a
      ><a name="23532" class="Symbol"
      >:</a
      ><a name="23533"
      > </a
      ><a name="23534" href="Maps.html#10265" class="Function"
      >&#8709;</a
      ><a name="23535"
      > </a
      ><a name="23536" href="Stlc.html#21753" class="Datatype Operator"
      >&#8866;</a
      ><a name="23537"
      > </a
      ><a name="23538" href="Stlc.html#5726" class="Function"
      >two</a
      ><a name="23541"
      > </a
      ><a name="23542" href="Stlc.html#21753" class="Datatype Operator"
      >&#8758;</a
      ><a name="23543"
      > </a
      ><a name="23544" class="Symbol"
      >(</a
      ><a name="23545" href="Stlc.html#2610" class="InductiveConstructor"
      >&#120121;</a
      ><a name="23546"
      > </a
      ><a name="23547" href="Stlc.html#2583" class="InductiveConstructor Operator"
      >&#8658;</a
      ><a name="23548"
      > </a
      ><a name="23549" href="Stlc.html#2610" class="InductiveConstructor"
      >&#120121;</a
      ><a name="23550" class="Symbol"
      >)</a
      ><a name="23551"
      > </a
      ><a name="23552" href="Stlc.html#2583" class="InductiveConstructor Operator"
      >&#8658;</a
      ><a name="23553"
      > </a
      ><a name="23554" href="Stlc.html#2610" class="InductiveConstructor"
      >&#120121;</a
      ><a name="23555"
      > </a
      ><a name="23556" href="Stlc.html#2583" class="InductiveConstructor Operator"
      >&#8658;</a
      ><a name="23557"
      > </a
      ><a name="23558" href="Stlc.html#2610" class="InductiveConstructor"
      >&#120121;</a
      ><a name="23559"
      >
</a
      ><a name="23560" href="Stlc.html#23524" class="Function"
      >typing&#8322;</a
      ><a name="23567"
      > </a
      ><a name="23568" class="Symbol"
      >=</a
      ><a name="23569"
      > </a
      ><a name="23570" href="Stlc.html#21851" class="InductiveConstructor"
      >&#8658;-I</a
      ><a name="23573"
      > </a
      ><a name="23574" class="Symbol"
      >(</a
      ><a name="23575" href="Stlc.html#21851" class="InductiveConstructor"
      >&#8658;-I</a
      ><a name="23578"
      > </a
      ><a name="23579" class="Symbol"
      >(</a
      ><a name="23580" href="Stlc.html#21928" class="InductiveConstructor"
      >&#8658;-E</a
      ><a name="23583"
      > </a
      ><a name="23584" class="Symbol"
      >(</a
      ><a name="23585" href="Stlc.html#21797" class="InductiveConstructor"
      >Ax</a
      ><a name="23587"
      > </a
      ><a name="23588" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="23592" class="Symbol"
      >)</a
      ><a name="23593"
      > </a
      ><a name="23594" class="Symbol"
      >(</a
      ><a name="23595" href="Stlc.html#21928" class="InductiveConstructor"
      >&#8658;-E</a
      ><a name="23598"
      > </a
      ><a name="23599" class="Symbol"
      >(</a
      ><a name="23600" href="Stlc.html#21797" class="InductiveConstructor"
      >Ax</a
      ><a name="23602"
      > </a
      ><a name="23603" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="23607" class="Symbol"
      >)</a
      ><a name="23608"
      > </a
      ><a name="23609" class="Symbol"
      >(</a
      ><a name="23610" href="Stlc.html#21797" class="InductiveConstructor"
      >Ax</a
      ><a name="23612"
      > </a
      ><a name="23613" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="23617" class="Symbol"
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
<a name="25298" href="Stlc.html#25298" class="Function"
      >notyping&#8322;</a
      ><a name="25307"
      > </a
      ><a name="25308" class="Symbol"
      >:</a
      ><a name="25309"
      > </a
      ><a name="25310" class="Symbol"
      >&#8704;</a
      ><a name="25311"
      > </a
      ><a name="25312" class="Symbol"
      >{</a
      ><a name="25313" href="Stlc.html#25313" class="Bound"
      >A</a
      ><a name="25314" class="Symbol"
      >}</a
      ><a name="25315"
      > </a
      ><a name="25316" class="Symbol"
      >&#8594;</a
      ><a name="25317"
      > </a
      ><a name="25318" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#414" class="Function Operator"
      >&#172;</a
      ><a name="25319"
      > </a
      ><a name="25320" class="Symbol"
      >(</a
      ><a name="25321" href="Maps.html#10265" class="Function"
      >&#8709;</a
      ><a name="25322"
      > </a
      ><a name="25323" href="Stlc.html#21753" class="Datatype Operator"
      >&#8866;</a
      ><a name="25324"
      > </a
      ><a name="25325" href="Stlc.html#3735" class="InductiveConstructor"
      >true</a
      ><a name="25329"
      > </a
      ><a name="25330" href="Stlc.html#3708" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="25331"
      > </a
      ><a name="25332" href="Stlc.html#3749" class="InductiveConstructor"
      >false</a
      ><a name="25337"
      > </a
      ><a name="25338" href="Stlc.html#21753" class="Datatype Operator"
      >&#8758;</a
      ><a name="25339"
      > </a
      ><a name="25340" href="Stlc.html#25313" class="Bound"
      >A</a
      ><a name="25341" class="Symbol"
      >)</a
      ><a name="25342"
      >
</a
      ><a name="25343" href="Stlc.html#25298" class="Function"
      >notyping&#8322;</a
      ><a name="25352"
      > </a
      ><a name="25353" class="Symbol"
      >(</a
      ><a name="25354" href="Stlc.html#21928" class="InductiveConstructor"
      >&#8658;-E</a
      ><a name="25357"
      > </a
      ><a name="25358" class="Symbol"
      >()</a
      ><a name="25360"
      > </a
      ><a name="25361" class="Symbol"
      >_)</a
      >
{% endraw %}</pre>

As a second example, here is a formal proof that it is not possible to
type `` λ[ x ∶ 𝔹 ] λ[ y ∶ 𝔹 ] ` x · ` y `` It cannot be typed, because
doing so requires `x` to be both boolean and a function.

<pre class="Agda">{% raw %}
<a name="25589" href="Stlc.html#25589" class="Function"
      >contradiction</a
      ><a name="25602"
      > </a
      ><a name="25603" class="Symbol"
      >:</a
      ><a name="25604"
      > </a
      ><a name="25605" class="Symbol"
      >&#8704;</a
      ><a name="25606"
      > </a
      ><a name="25607" class="Symbol"
      >{</a
      ><a name="25608" href="Stlc.html#25608" class="Bound"
      >A</a
      ><a name="25609"
      > </a
      ><a name="25610" href="Stlc.html#25610" class="Bound"
      >B</a
      ><a name="25611" class="Symbol"
      >}</a
      ><a name="25612"
      > </a
      ><a name="25613" class="Symbol"
      >&#8594;</a
      ><a name="25614"
      > </a
      ><a name="25615" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#414" class="Function Operator"
      >&#172;</a
      ><a name="25616"
      > </a
      ><a name="25617" class="Symbol"
      >(</a
      ><a name="25618" href="Stlc.html#2610" class="InductiveConstructor"
      >&#120121;</a
      ><a name="25619"
      > </a
      ><a name="25620" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="25621"
      > </a
      ><a name="25622" href="Stlc.html#25608" class="Bound"
      >A</a
      ><a name="25623"
      > </a
      ><a name="25624" href="Stlc.html#2583" class="InductiveConstructor Operator"
      >&#8658;</a
      ><a name="25625"
      > </a
      ><a name="25626" href="Stlc.html#25610" class="Bound"
      >B</a
      ><a name="25627" class="Symbol"
      >)</a
      ><a name="25628"
      >
</a
      ><a name="25629" href="Stlc.html#25589" class="Function"
      >contradiction</a
      ><a name="25642"
      > </a
      ><a name="25643" class="Symbol"
      >()</a
      ><a name="25645"
      >

</a
      ><a name="25647" href="Stlc.html#25647" class="Function"
      >notyping&#8321;</a
      ><a name="25656"
      > </a
      ><a name="25657" class="Symbol"
      >:</a
      ><a name="25658"
      > </a
      ><a name="25659" class="Symbol"
      >&#8704;</a
      ><a name="25660"
      > </a
      ><a name="25661" class="Symbol"
      >{</a
      ><a name="25662" href="Stlc.html#25662" class="Bound"
      >A</a
      ><a name="25663" class="Symbol"
      >}</a
      ><a name="25664"
      > </a
      ><a name="25665" class="Symbol"
      >&#8594;</a
      ><a name="25666"
      > </a
      ><a name="25667" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#414" class="Function Operator"
      >&#172;</a
      ><a name="25668"
      > </a
      ><a name="25669" class="Symbol"
      >(</a
      ><a name="25670" href="Maps.html#10265" class="Function"
      >&#8709;</a
      ><a name="25671"
      > </a
      ><a name="25672" href="Stlc.html#21753" class="Datatype Operator"
      >&#8866;</a
      ><a name="25673"
      > </a
      ><a name="25674" href="Stlc.html#3672" class="InductiveConstructor Operator"
      >&#955;[</a
      ><a name="25676"
      > </a
      ><a name="25677" href="Stlc.html#5679" class="Function"
      >x</a
      ><a name="25678"
      > </a
      ><a name="25679" href="Stlc.html#3672" class="InductiveConstructor Operator"
      >&#8758;</a
      ><a name="25680"
      > </a
      ><a name="25681" href="Stlc.html#2610" class="InductiveConstructor"
      >&#120121;</a
      ><a name="25682"
      > </a
      ><a name="25683" href="Stlc.html#3672" class="InductiveConstructor Operator"
      >]</a
      ><a name="25684"
      > </a
      ><a name="25685" href="Stlc.html#3672" class="InductiveConstructor Operator"
      >&#955;[</a
      ><a name="25687"
      > </a
      ><a name="25688" href="Stlc.html#5681" class="Function"
      >y</a
      ><a name="25689"
      > </a
      ><a name="25690" href="Stlc.html#3672" class="InductiveConstructor Operator"
      >&#8758;</a
      ><a name="25691"
      > </a
      ><a name="25692" href="Stlc.html#2610" class="InductiveConstructor"
      >&#120121;</a
      ><a name="25693"
      > </a
      ><a name="25694" href="Stlc.html#3672" class="InductiveConstructor Operator"
      >]</a
      ><a name="25695"
      > </a
      ><a name="25696" href="Stlc.html#3656" class="InductiveConstructor"
      >`</a
      ><a name="25697"
      > </a
      ><a name="25698" href="Stlc.html#5679" class="Function"
      >x</a
      ><a name="25699"
      > </a
      ><a name="25700" href="Stlc.html#3708" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="25701"
      > </a
      ><a name="25702" href="Stlc.html#3656" class="InductiveConstructor"
      >`</a
      ><a name="25703"
      > </a
      ><a name="25704" href="Stlc.html#5681" class="Function"
      >y</a
      ><a name="25705"
      > </a
      ><a name="25706" href="Stlc.html#21753" class="Datatype Operator"
      >&#8758;</a
      ><a name="25707"
      > </a
      ><a name="25708" href="Stlc.html#25662" class="Bound"
      >A</a
      ><a name="25709" class="Symbol"
      >)</a
      ><a name="25710"
      >
</a
      ><a name="25711" href="Stlc.html#25647" class="Function"
      >notyping&#8321;</a
      ><a name="25720"
      > </a
      ><a name="25721" class="Symbol"
      >(</a
      ><a name="25722" href="Stlc.html#21851" class="InductiveConstructor"
      >&#8658;-I</a
      ><a name="25725"
      > </a
      ><a name="25726" class="Symbol"
      >(</a
      ><a name="25727" href="Stlc.html#21851" class="InductiveConstructor"
      >&#8658;-I</a
      ><a name="25730"
      > </a
      ><a name="25731" class="Symbol"
      >(</a
      ><a name="25732" href="Stlc.html#21928" class="InductiveConstructor"
      >&#8658;-E</a
      ><a name="25735"
      > </a
      ><a name="25736" class="Symbol"
      >(</a
      ><a name="25737" href="Stlc.html#21797" class="InductiveConstructor"
      >Ax</a
      ><a name="25739"
      > </a
      ><a name="25740" href="Stlc.html#25740" class="Bound"
      >&#915;x</a
      ><a name="25742" class="Symbol"
      >)</a
      ><a name="25743"
      > </a
      ><a name="25744" class="Symbol"
      >_)))</a
      ><a name="25748"
      > </a
      ><a name="25749" class="Symbol"
      >=</a
      ><a name="25750"
      >  </a
      ><a name="25752" href="Stlc.html#25589" class="Function"
      >contradiction</a
      ><a name="25765"
      > </a
      ><a name="25766" class="Symbol"
      >(</a
      ><a name="25767" href="Maps.html#11919" class="Function"
      >just-injective</a
      ><a name="25781"
      > </a
      ><a name="25782" href="Stlc.html#25740" class="Bound"
      >&#915;x</a
      ><a name="25784" class="Symbol"
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



