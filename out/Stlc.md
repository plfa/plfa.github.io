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

<pre class="Agda">

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

</pre>

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

<pre class="Agda">

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

</pre>

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

<pre class="Agda">

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

</pre>

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

<pre class="Agda">

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

</pre>


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

<pre class="Agda">

<a name="8432" href="Stlc.html#8432" class="Function"
      >ex&#8321;</a
      ><a name="8435"
      > </a
      ><a name="8436" class="Symbol"
      >:</a
      ><a name="8437"
      > </a
      ><a name="8438" class="Symbol"
      >(</a
      ><a name="8439" href="Stlc.html#2610" class="InductiveConstructor"
      >&#120121;</a
      ><a name="8440"
      > </a
      ><a name="8441" href="Stlc.html#2583" class="InductiveConstructor Operator"
      >&#8658;</a
      ><a name="8442"
      > </a
      ><a name="8443" href="Stlc.html#2610" class="InductiveConstructor"
      >&#120121;</a
      ><a name="8444" class="Symbol"
      >)</a
      ><a name="8445"
      > </a
      ><a name="8446" href="Stlc.html#2583" class="InductiveConstructor Operator"
      >&#8658;</a
      ><a name="8447"
      > </a
      ><a name="8448" href="Stlc.html#2610" class="InductiveConstructor"
      >&#120121;</a
      ><a name="8449"
      > </a
      ><a name="8450" href="Stlc.html#2583" class="InductiveConstructor Operator"
      >&#8658;</a
      ><a name="8451"
      > </a
      ><a name="8452" href="Stlc.html#2610" class="InductiveConstructor"
      >&#120121;</a
      ><a name="8453"
      > </a
      ><a name="8454" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="8455"
      > </a
      ><a name="8456" class="Symbol"
      >(</a
      ><a name="8457" href="Stlc.html#2610" class="InductiveConstructor"
      >&#120121;</a
      ><a name="8458"
      > </a
      ><a name="8459" href="Stlc.html#2583" class="InductiveConstructor Operator"
      >&#8658;</a
      ><a name="8460"
      > </a
      ><a name="8461" href="Stlc.html#2610" class="InductiveConstructor"
      >&#120121;</a
      ><a name="8462" class="Symbol"
      >)</a
      ><a name="8463"
      > </a
      ><a name="8464" href="Stlc.html#2583" class="InductiveConstructor Operator"
      >&#8658;</a
      ><a name="8465"
      > </a
      ><a name="8466" class="Symbol"
      >(</a
      ><a name="8467" href="Stlc.html#2610" class="InductiveConstructor"
      >&#120121;</a
      ><a name="8468"
      > </a
      ><a name="8469" href="Stlc.html#2583" class="InductiveConstructor Operator"
      >&#8658;</a
      ><a name="8470"
      > </a
      ><a name="8471" href="Stlc.html#2610" class="InductiveConstructor"
      >&#120121;</a
      ><a name="8472" class="Symbol"
      >)</a
      ><a name="8473"
      >
</a
      ><a name="8474" href="Stlc.html#8432" class="Function"
      >ex&#8321;</a
      ><a name="8477"
      > </a
      ><a name="8478" class="Symbol"
      >=</a
      ><a name="8479"
      > </a
      ><a name="8480" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="8484"
      >

</a
      ><a name="8486" href="Stlc.html#8486" class="Function"
      >ex&#8322;</a
      ><a name="8489"
      > </a
      ><a name="8490" class="Symbol"
      >:</a
      ><a name="8491"
      > </a
      ><a name="8492" href="Stlc.html#5726" class="Function"
      >two</a
      ><a name="8495"
      > </a
      ><a name="8496" href="Stlc.html#3708" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="8497"
      > </a
      ><a name="8498" href="Stlc.html#5722" class="Function"
      >not</a
      ><a name="8501"
      > </a
      ><a name="8502" href="Stlc.html#3708" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="8503"
      > </a
      ><a name="8504" href="Stlc.html#3735" class="InductiveConstructor"
      >true</a
      ><a name="8508"
      > </a
      ><a name="8509" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="8510"
      > </a
      ><a name="8511" class="Symbol"
      >(</a
      ><a name="8512" href="Stlc.html#5726" class="Function"
      >two</a
      ><a name="8515"
      > </a
      ><a name="8516" href="Stlc.html#3708" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="8517"
      > </a
      ><a name="8518" href="Stlc.html#5722" class="Function"
      >not</a
      ><a name="8521" class="Symbol"
      >)</a
      ><a name="8522"
      > </a
      ><a name="8523" href="Stlc.html#3708" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="8524"
      > </a
      ><a name="8525" href="Stlc.html#3735" class="InductiveConstructor"
      >true</a
      ><a name="8529"
      >
</a
      ><a name="8530" href="Stlc.html#8486" class="Function"
      >ex&#8322;</a
      ><a name="8533"
      > </a
      ><a name="8534" class="Symbol"
      >=</a
      ><a name="8535"
      > </a
      ><a name="8536" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="8540"
      >

</a
      ><a name="8542" href="Stlc.html#8542" class="Function"
      >ex&#8323;</a
      ><a name="8545"
      > </a
      ><a name="8546" class="Symbol"
      >:</a
      ><a name="8547"
      > </a
      ><a name="8548" href="Stlc.html#3672" class="InductiveConstructor Operator"
      >&#955;[</a
      ><a name="8550"
      > </a
      ><a name="8551" href="Stlc.html#5677" class="Function"
      >f</a
      ><a name="8552"
      > </a
      ><a name="8553" href="Stlc.html#3672" class="InductiveConstructor Operator"
      >&#8758;</a
      ><a name="8554"
      > </a
      ><a name="8555" href="Stlc.html#2610" class="InductiveConstructor"
      >&#120121;</a
      ><a name="8556"
      > </a
      ><a name="8557" href="Stlc.html#2583" class="InductiveConstructor Operator"
      >&#8658;</a
      ><a name="8558"
      > </a
      ><a name="8559" href="Stlc.html#2610" class="InductiveConstructor"
      >&#120121;</a
      ><a name="8560"
      > </a
      ><a name="8561" href="Stlc.html#3672" class="InductiveConstructor Operator"
      >]</a
      ><a name="8562"
      > </a
      ><a name="8563" href="Stlc.html#3672" class="InductiveConstructor Operator"
      >&#955;[</a
      ><a name="8565"
      > </a
      ><a name="8566" href="Stlc.html#5679" class="Function"
      >x</a
      ><a name="8567"
      > </a
      ><a name="8568" href="Stlc.html#3672" class="InductiveConstructor Operator"
      >&#8758;</a
      ><a name="8569"
      > </a
      ><a name="8570" href="Stlc.html#2610" class="InductiveConstructor"
      >&#120121;</a
      ><a name="8571"
      > </a
      ><a name="8572" href="Stlc.html#3672" class="InductiveConstructor Operator"
      >]</a
      ><a name="8573"
      > </a
      ><a name="8574" href="Stlc.html#3656" class="InductiveConstructor"
      >`</a
      ><a name="8575"
      > </a
      ><a name="8576" href="Stlc.html#5677" class="Function"
      >f</a
      ><a name="8577"
      > </a
      ><a name="8578" href="Stlc.html#3708" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="8579"
      > </a
      ><a name="8580" class="Symbol"
      >(</a
      ><a name="8581" href="Stlc.html#3656" class="InductiveConstructor"
      >`</a
      ><a name="8582"
      > </a
      ><a name="8583" href="Stlc.html#5677" class="Function"
      >f</a
      ><a name="8584"
      > </a
      ><a name="8585" href="Stlc.html#3708" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="8586"
      > </a
      ><a name="8587" href="Stlc.html#3656" class="InductiveConstructor"
      >`</a
      ><a name="8588"
      > </a
      ><a name="8589" href="Stlc.html#5679" class="Function"
      >x</a
      ><a name="8590" class="Symbol"
      >)</a
      ><a name="8591"
      >
      </a
      ><a name="8598" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="8599"
      > </a
      ><a name="8600" class="Symbol"
      >(</a
      ><a name="8601" href="Stlc.html#3672" class="InductiveConstructor Operator"
      >&#955;[</a
      ><a name="8603"
      > </a
      ><a name="8604" href="Stlc.html#5677" class="Function"
      >f</a
      ><a name="8605"
      > </a
      ><a name="8606" href="Stlc.html#3672" class="InductiveConstructor Operator"
      >&#8758;</a
      ><a name="8607"
      > </a
      ><a name="8608" href="Stlc.html#2610" class="InductiveConstructor"
      >&#120121;</a
      ><a name="8609"
      > </a
      ><a name="8610" href="Stlc.html#2583" class="InductiveConstructor Operator"
      >&#8658;</a
      ><a name="8611"
      > </a
      ><a name="8612" href="Stlc.html#2610" class="InductiveConstructor"
      >&#120121;</a
      ><a name="8613"
      > </a
      ><a name="8614" href="Stlc.html#3672" class="InductiveConstructor Operator"
      >]</a
      ><a name="8615"
      > </a
      ><a name="8616" class="Symbol"
      >(</a
      ><a name="8617" href="Stlc.html#3672" class="InductiveConstructor Operator"
      >&#955;[</a
      ><a name="8619"
      > </a
      ><a name="8620" href="Stlc.html#5679" class="Function"
      >x</a
      ><a name="8621"
      > </a
      ><a name="8622" href="Stlc.html#3672" class="InductiveConstructor Operator"
      >&#8758;</a
      ><a name="8623"
      > </a
      ><a name="8624" href="Stlc.html#2610" class="InductiveConstructor"
      >&#120121;</a
      ><a name="8625"
      > </a
      ><a name="8626" href="Stlc.html#3672" class="InductiveConstructor Operator"
      >]</a
      ><a name="8627"
      > </a
      ><a name="8628" class="Symbol"
      >(</a
      ><a name="8629" href="Stlc.html#3656" class="InductiveConstructor"
      >`</a
      ><a name="8630"
      > </a
      ><a name="8631" href="Stlc.html#5677" class="Function"
      >f</a
      ><a name="8632"
      > </a
      ><a name="8633" href="Stlc.html#3708" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="8634"
      > </a
      ><a name="8635" class="Symbol"
      >(</a
      ><a name="8636" href="Stlc.html#3656" class="InductiveConstructor"
      >`</a
      ><a name="8637"
      > </a
      ><a name="8638" href="Stlc.html#5677" class="Function"
      >f</a
      ><a name="8639"
      > </a
      ><a name="8640" href="Stlc.html#3708" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="8641"
      > </a
      ><a name="8642" href="Stlc.html#3656" class="InductiveConstructor"
      >`</a
      ><a name="8643"
      > </a
      ><a name="8644" href="Stlc.html#5679" class="Function"
      >x</a
      ><a name="8645" class="Symbol"
      >))))</a
      ><a name="8649"
      >
</a
      ><a name="8650" href="Stlc.html#8542" class="Function"
      >ex&#8323;</a
      ><a name="8653"
      > </a
      ><a name="8654" class="Symbol"
      >=</a
      ><a name="8655"
      > </a
      ><a name="8656" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      >

</pre>

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

<pre class="Agda">

<a name="9717" class="Keyword"
      >data</a
      ><a name="9721"
      > </a
      ><a name="9722" href="Stlc.html#9722" class="Datatype"
      >Value</a
      ><a name="9727"
      > </a
      ><a name="9728" class="Symbol"
      >:</a
      ><a name="9729"
      > </a
      ><a name="9730" href="Stlc.html#3637" class="Datatype"
      >Term</a
      ><a name="9734"
      > </a
      ><a name="9735" class="Symbol"
      >&#8594;</a
      ><a name="9736"
      > </a
      ><a name="9737" class="PrimitiveType"
      >Set</a
      ><a name="9740"
      > </a
      ><a name="9741" class="Keyword"
      >where</a
      ><a name="9746"
      >
  </a
      ><a name="9749" href="Stlc.html#9749" class="InductiveConstructor"
      >value-&#955;</a
      ><a name="9756"
      >     </a
      ><a name="9761" class="Symbol"
      >:</a
      ><a name="9762"
      > </a
      ><a name="9763" class="Symbol"
      >&#8704;</a
      ><a name="9764"
      > </a
      ><a name="9765" class="Symbol"
      >{</a
      ><a name="9766" href="Stlc.html#9766" class="Bound"
      >x</a
      ><a name="9767"
      > </a
      ><a name="9768" href="Stlc.html#9768" class="Bound"
      >A</a
      ><a name="9769"
      > </a
      ><a name="9770" href="Stlc.html#9770" class="Bound"
      >N</a
      ><a name="9771" class="Symbol"
      >}</a
      ><a name="9772"
      > </a
      ><a name="9773" class="Symbol"
      >&#8594;</a
      ><a name="9774"
      > </a
      ><a name="9775" href="Stlc.html#9722" class="Datatype"
      >Value</a
      ><a name="9780"
      > </a
      ><a name="9781" class="Symbol"
      >(</a
      ><a name="9782" href="Stlc.html#3672" class="InductiveConstructor Operator"
      >&#955;[</a
      ><a name="9784"
      > </a
      ><a name="9785" href="Stlc.html#9766" class="Bound"
      >x</a
      ><a name="9786"
      > </a
      ><a name="9787" href="Stlc.html#3672" class="InductiveConstructor Operator"
      >&#8758;</a
      ><a name="9788"
      > </a
      ><a name="9789" href="Stlc.html#9768" class="Bound"
      >A</a
      ><a name="9790"
      > </a
      ><a name="9791" href="Stlc.html#3672" class="InductiveConstructor Operator"
      >]</a
      ><a name="9792"
      > </a
      ><a name="9793" href="Stlc.html#9770" class="Bound"
      >N</a
      ><a name="9794" class="Symbol"
      >)</a
      ><a name="9795"
      >
  </a
      ><a name="9798" href="Stlc.html#9798" class="InductiveConstructor"
      >value-true</a
      ><a name="9808"
      >  </a
      ><a name="9810" class="Symbol"
      >:</a
      ><a name="9811"
      > </a
      ><a name="9812" href="Stlc.html#9722" class="Datatype"
      >Value</a
      ><a name="9817"
      > </a
      ><a name="9818" href="Stlc.html#3735" class="InductiveConstructor"
      >true</a
      ><a name="9822"
      >
  </a
      ><a name="9825" href="Stlc.html#9825" class="InductiveConstructor"
      >value-false</a
      ><a name="9836"
      > </a
      ><a name="9837" class="Symbol"
      >:</a
      ><a name="9838"
      > </a
      ><a name="9839" href="Stlc.html#9722" class="Datatype"
      >Value</a
      ><a name="9844"
      > </a
      ><a name="9845" href="Stlc.html#3749" class="InductiveConstructor"
      >false</a
      >

</pre>

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

<pre class="Agda">

<a name="12266" href="Stlc.html#12266" class="Function Operator"
      >_[_:=_]</a
      ><a name="12273"
      > </a
      ><a name="12274" class="Symbol"
      >:</a
      ><a name="12275"
      > </a
      ><a name="12276" href="Stlc.html#3637" class="Datatype"
      >Term</a
      ><a name="12280"
      > </a
      ><a name="12281" class="Symbol"
      >&#8594;</a
      ><a name="12282"
      > </a
      ><a name="12283" href="Maps.html#2171" class="Datatype"
      >Id</a
      ><a name="12285"
      > </a
      ><a name="12286" class="Symbol"
      >&#8594;</a
      ><a name="12287"
      > </a
      ><a name="12288" href="Stlc.html#3637" class="Datatype"
      >Term</a
      ><a name="12292"
      > </a
      ><a name="12293" class="Symbol"
      >&#8594;</a
      ><a name="12294"
      > </a
      ><a name="12295" href="Stlc.html#3637" class="Datatype"
      >Term</a
      ><a name="12299"
      >
</a
      ><a name="12300" class="Symbol"
      >(</a
      ><a name="12301" href="Stlc.html#3656" class="InductiveConstructor"
      >`</a
      ><a name="12302"
      > </a
      ><a name="12303" href="Stlc.html#12303" class="Bound"
      >x&#8242;</a
      ><a name="12305" class="Symbol"
      >)</a
      ><a name="12306"
      > </a
      ><a name="12307" href="Stlc.html#12266" class="Function Operator"
      >[</a
      ><a name="12308"
      > </a
      ><a name="12309" href="Stlc.html#12309" class="Bound"
      >x</a
      ><a name="12310"
      > </a
      ><a name="12311" href="Stlc.html#12266" class="Function Operator"
      >:=</a
      ><a name="12313"
      > </a
      ><a name="12314" href="Stlc.html#12314" class="Bound"
      >V</a
      ><a name="12315"
      > </a
      ><a name="12316" href="Stlc.html#12266" class="Function Operator"
      >]</a
      ><a name="12317"
      > </a
      ><a name="12318" class="Keyword"
      >with</a
      ><a name="12322"
      > </a
      ><a name="12323" href="Stlc.html#12309" class="Bound"
      >x</a
      ><a name="12324"
      > </a
      ><a name="12325" href="Maps.html#2509" class="Function Operator"
      >&#8799;</a
      ><a name="12326"
      > </a
      ><a name="12327" href="Stlc.html#12303" class="Bound"
      >x&#8242;</a
      ><a name="12329"
      >
</a
      ><a name="12330" class="Symbol"
      >...</a
      ><a name="12333"
      > </a
      ><a name="12334" class="Symbol"
      >|</a
      ><a name="12335"
      > </a
      ><a name="12336" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#520" class="InductiveConstructor"
      >yes</a
      ><a name="12339"
      > </a
      ><a name="12340" class="Symbol"
      >_</a
      ><a name="12341"
      > </a
      ><a name="12342" class="Symbol"
      >=</a
      ><a name="12343"
      > </a
      ><a name="12344" href="Stlc.html#12314" class="Bound"
      >V</a
      ><a name="12345"
      >
</a
      ><a name="12346" class="Symbol"
      >...</a
      ><a name="12349"
      > </a
      ><a name="12350" class="Symbol"
      >|</a
      ><a name="12351"
      > </a
      ><a name="12352" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#547" class="InductiveConstructor"
      >no</a
      ><a name="12354"
      >  </a
      ><a name="12356" class="Symbol"
      >_</a
      ><a name="12357"
      > </a
      ><a name="12358" class="Symbol"
      >=</a
      ><a name="12359"
      > </a
      ><a name="12360" href="Stlc.html#3656" class="InductiveConstructor"
      >`</a
      ><a name="12361"
      > </a
      ><a name="12362" href="Stlc.html#12303" class="Bound"
      >x&#8242;</a
      ><a name="12364"
      >
</a
      ><a name="12365" class="Symbol"
      >(</a
      ><a name="12366" href="Stlc.html#3672" class="InductiveConstructor Operator"
      >&#955;[</a
      ><a name="12368"
      > </a
      ><a name="12369" href="Stlc.html#12369" class="Bound"
      >x&#8242;</a
      ><a name="12371"
      > </a
      ><a name="12372" href="Stlc.html#3672" class="InductiveConstructor Operator"
      >&#8758;</a
      ><a name="12373"
      > </a
      ><a name="12374" href="Stlc.html#12374" class="Bound"
      >A&#8242;</a
      ><a name="12376"
      > </a
      ><a name="12377" href="Stlc.html#3672" class="InductiveConstructor Operator"
      >]</a
      ><a name="12378"
      > </a
      ><a name="12379" href="Stlc.html#12379" class="Bound"
      >N&#8242;</a
      ><a name="12381" class="Symbol"
      >)</a
      ><a name="12382"
      > </a
      ><a name="12383" href="Stlc.html#12266" class="Function Operator"
      >[</a
      ><a name="12384"
      > </a
      ><a name="12385" href="Stlc.html#12385" class="Bound"
      >x</a
      ><a name="12386"
      > </a
      ><a name="12387" href="Stlc.html#12266" class="Function Operator"
      >:=</a
      ><a name="12389"
      > </a
      ><a name="12390" href="Stlc.html#12390" class="Bound"
      >V</a
      ><a name="12391"
      > </a
      ><a name="12392" href="Stlc.html#12266" class="Function Operator"
      >]</a
      ><a name="12393"
      > </a
      ><a name="12394" class="Keyword"
      >with</a
      ><a name="12398"
      > </a
      ><a name="12399" href="Stlc.html#12385" class="Bound"
      >x</a
      ><a name="12400"
      > </a
      ><a name="12401" href="Maps.html#2509" class="Function Operator"
      >&#8799;</a
      ><a name="12402"
      > </a
      ><a name="12403" href="Stlc.html#12369" class="Bound"
      >x&#8242;</a
      ><a name="12405"
      >
</a
      ><a name="12406" class="Symbol"
      >...</a
      ><a name="12409"
      > </a
      ><a name="12410" class="Symbol"
      >|</a
      ><a name="12411"
      > </a
      ><a name="12412" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#520" class="InductiveConstructor"
      >yes</a
      ><a name="12415"
      > </a
      ><a name="12416" class="Symbol"
      >_</a
      ><a name="12417"
      > </a
      ><a name="12418" class="Symbol"
      >=</a
      ><a name="12419"
      > </a
      ><a name="12420" href="Stlc.html#3672" class="InductiveConstructor Operator"
      >&#955;[</a
      ><a name="12422"
      > </a
      ><a name="12423" href="Stlc.html#12369" class="Bound"
      >x&#8242;</a
      ><a name="12425"
      > </a
      ><a name="12426" href="Stlc.html#3672" class="InductiveConstructor Operator"
      >&#8758;</a
      ><a name="12427"
      > </a
      ><a name="12428" href="Stlc.html#12374" class="Bound"
      >A&#8242;</a
      ><a name="12430"
      > </a
      ><a name="12431" href="Stlc.html#3672" class="InductiveConstructor Operator"
      >]</a
      ><a name="12432"
      > </a
      ><a name="12433" href="Stlc.html#12379" class="Bound"
      >N&#8242;</a
      ><a name="12435"
      >
</a
      ><a name="12436" class="Symbol"
      >...</a
      ><a name="12439"
      > </a
      ><a name="12440" class="Symbol"
      >|</a
      ><a name="12441"
      > </a
      ><a name="12442" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#547" class="InductiveConstructor"
      >no</a
      ><a name="12444"
      >  </a
      ><a name="12446" class="Symbol"
      >_</a
      ><a name="12447"
      > </a
      ><a name="12448" class="Symbol"
      >=</a
      ><a name="12449"
      > </a
      ><a name="12450" href="Stlc.html#3672" class="InductiveConstructor Operator"
      >&#955;[</a
      ><a name="12452"
      > </a
      ><a name="12453" href="Stlc.html#12369" class="Bound"
      >x&#8242;</a
      ><a name="12455"
      > </a
      ><a name="12456" href="Stlc.html#3672" class="InductiveConstructor Operator"
      >&#8758;</a
      ><a name="12457"
      > </a
      ><a name="12458" href="Stlc.html#12374" class="Bound"
      >A&#8242;</a
      ><a name="12460"
      > </a
      ><a name="12461" href="Stlc.html#3672" class="InductiveConstructor Operator"
      >]</a
      ><a name="12462"
      > </a
      ><a name="12463" class="Symbol"
      >(</a
      ><a name="12464" href="Stlc.html#12379" class="Bound"
      >N&#8242;</a
      ><a name="12466"
      > </a
      ><a name="12467" href="Stlc.html#12266" class="Function Operator"
      >[</a
      ><a name="12468"
      > </a
      ><a name="12469" href="Stlc.html#12385" class="Bound"
      >x</a
      ><a name="12470"
      > </a
      ><a name="12471" href="Stlc.html#12266" class="Function Operator"
      >:=</a
      ><a name="12473"
      > </a
      ><a name="12474" href="Stlc.html#12390" class="Bound"
      >V</a
      ><a name="12475"
      > </a
      ><a name="12476" href="Stlc.html#12266" class="Function Operator"
      >]</a
      ><a name="12477" class="Symbol"
      >)</a
      ><a name="12478"
      >
</a
      ><a name="12479" class="Symbol"
      >(</a
      ><a name="12480" href="Stlc.html#12480" class="Bound"
      >L&#8242;</a
      ><a name="12482"
      > </a
      ><a name="12483" href="Stlc.html#3708" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="12484"
      > </a
      ><a name="12485" href="Stlc.html#12485" class="Bound"
      >M&#8242;</a
      ><a name="12487" class="Symbol"
      >)</a
      ><a name="12488"
      > </a
      ><a name="12489" href="Stlc.html#12266" class="Function Operator"
      >[</a
      ><a name="12490"
      > </a
      ><a name="12491" href="Stlc.html#12491" class="Bound"
      >x</a
      ><a name="12492"
      > </a
      ><a name="12493" href="Stlc.html#12266" class="Function Operator"
      >:=</a
      ><a name="12495"
      > </a
      ><a name="12496" href="Stlc.html#12496" class="Bound"
      >V</a
      ><a name="12497"
      > </a
      ><a name="12498" href="Stlc.html#12266" class="Function Operator"
      >]</a
      ><a name="12499"
      > </a
      ><a name="12500" class="Symbol"
      >=</a
      ><a name="12501"
      >  </a
      ><a name="12503" class="Symbol"
      >(</a
      ><a name="12504" href="Stlc.html#12480" class="Bound"
      >L&#8242;</a
      ><a name="12506"
      > </a
      ><a name="12507" href="Stlc.html#12266" class="Function Operator"
      >[</a
      ><a name="12508"
      > </a
      ><a name="12509" href="Stlc.html#12491" class="Bound"
      >x</a
      ><a name="12510"
      > </a
      ><a name="12511" href="Stlc.html#12266" class="Function Operator"
      >:=</a
      ><a name="12513"
      > </a
      ><a name="12514" href="Stlc.html#12496" class="Bound"
      >V</a
      ><a name="12515"
      > </a
      ><a name="12516" href="Stlc.html#12266" class="Function Operator"
      >]</a
      ><a name="12517" class="Symbol"
      >)</a
      ><a name="12518"
      > </a
      ><a name="12519" href="Stlc.html#3708" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="12520"
      > </a
      ><a name="12521" class="Symbol"
      >(</a
      ><a name="12522" href="Stlc.html#12485" class="Bound"
      >M&#8242;</a
      ><a name="12524"
      > </a
      ><a name="12525" href="Stlc.html#12266" class="Function Operator"
      >[</a
      ><a name="12526"
      > </a
      ><a name="12527" href="Stlc.html#12491" class="Bound"
      >x</a
      ><a name="12528"
      > </a
      ><a name="12529" href="Stlc.html#12266" class="Function Operator"
      >:=</a
      ><a name="12531"
      > </a
      ><a name="12532" href="Stlc.html#12496" class="Bound"
      >V</a
      ><a name="12533"
      > </a
      ><a name="12534" href="Stlc.html#12266" class="Function Operator"
      >]</a
      ><a name="12535" class="Symbol"
      >)</a
      ><a name="12536"
      >
</a
      ><a name="12537" class="Symbol"
      >(</a
      ><a name="12538" href="Stlc.html#3735" class="InductiveConstructor"
      >true</a
      ><a name="12542" class="Symbol"
      >)</a
      ><a name="12543"
      > </a
      ><a name="12544" href="Stlc.html#12266" class="Function Operator"
      >[</a
      ><a name="12545"
      > </a
      ><a name="12546" href="Stlc.html#12546" class="Bound"
      >x</a
      ><a name="12547"
      > </a
      ><a name="12548" href="Stlc.html#12266" class="Function Operator"
      >:=</a
      ><a name="12550"
      > </a
      ><a name="12551" href="Stlc.html#12551" class="Bound"
      >V</a
      ><a name="12552"
      > </a
      ><a name="12553" href="Stlc.html#12266" class="Function Operator"
      >]</a
      ><a name="12554"
      > </a
      ><a name="12555" class="Symbol"
      >=</a
      ><a name="12556"
      > </a
      ><a name="12557" href="Stlc.html#3735" class="InductiveConstructor"
      >true</a
      ><a name="12561"
      >
</a
      ><a name="12562" class="Symbol"
      >(</a
      ><a name="12563" href="Stlc.html#3749" class="InductiveConstructor"
      >false</a
      ><a name="12568" class="Symbol"
      >)</a
      ><a name="12569"
      > </a
      ><a name="12570" href="Stlc.html#12266" class="Function Operator"
      >[</a
      ><a name="12571"
      > </a
      ><a name="12572" href="Stlc.html#12572" class="Bound"
      >x</a
      ><a name="12573"
      > </a
      ><a name="12574" href="Stlc.html#12266" class="Function Operator"
      >:=</a
      ><a name="12576"
      > </a
      ><a name="12577" href="Stlc.html#12577" class="Bound"
      >V</a
      ><a name="12578"
      > </a
      ><a name="12579" href="Stlc.html#12266" class="Function Operator"
      >]</a
      ><a name="12580"
      > </a
      ><a name="12581" class="Symbol"
      >=</a
      ><a name="12582"
      > </a
      ><a name="12583" href="Stlc.html#3749" class="InductiveConstructor"
      >false</a
      ><a name="12588"
      >
</a
      ><a name="12589" class="Symbol"
      >(</a
      ><a name="12590" href="Stlc.html#3764" class="InductiveConstructor Operator"
      >if</a
      ><a name="12592"
      > </a
      ><a name="12593" href="Stlc.html#12593" class="Bound"
      >L&#8242;</a
      ><a name="12595"
      > </a
      ><a name="12596" href="Stlc.html#3764" class="InductiveConstructor Operator"
      >then</a
      ><a name="12600"
      > </a
      ><a name="12601" href="Stlc.html#12601" class="Bound"
      >M&#8242;</a
      ><a name="12603"
      > </a
      ><a name="12604" href="Stlc.html#3764" class="InductiveConstructor Operator"
      >else</a
      ><a name="12608"
      > </a
      ><a name="12609" href="Stlc.html#12609" class="Bound"
      >N&#8242;</a
      ><a name="12611" class="Symbol"
      >)</a
      ><a name="12612"
      > </a
      ><a name="12613" href="Stlc.html#12266" class="Function Operator"
      >[</a
      ><a name="12614"
      > </a
      ><a name="12615" href="Stlc.html#12615" class="Bound"
      >x</a
      ><a name="12616"
      > </a
      ><a name="12617" href="Stlc.html#12266" class="Function Operator"
      >:=</a
      ><a name="12619"
      > </a
      ><a name="12620" href="Stlc.html#12620" class="Bound"
      >V</a
      ><a name="12621"
      > </a
      ><a name="12622" href="Stlc.html#12266" class="Function Operator"
      >]</a
      ><a name="12623"
      > </a
      ><a name="12624" class="Symbol"
      >=</a
      ><a name="12625"
      >
  </a
      ><a name="12628" href="Stlc.html#3764" class="InductiveConstructor Operator"
      >if</a
      ><a name="12630"
      > </a
      ><a name="12631" class="Symbol"
      >(</a
      ><a name="12632" href="Stlc.html#12593" class="Bound"
      >L&#8242;</a
      ><a name="12634"
      > </a
      ><a name="12635" href="Stlc.html#12266" class="Function Operator"
      >[</a
      ><a name="12636"
      > </a
      ><a name="12637" href="Stlc.html#12615" class="Bound"
      >x</a
      ><a name="12638"
      > </a
      ><a name="12639" href="Stlc.html#12266" class="Function Operator"
      >:=</a
      ><a name="12641"
      > </a
      ><a name="12642" href="Stlc.html#12620" class="Bound"
      >V</a
      ><a name="12643"
      > </a
      ><a name="12644" href="Stlc.html#12266" class="Function Operator"
      >]</a
      ><a name="12645" class="Symbol"
      >)</a
      ><a name="12646"
      > </a
      ><a name="12647" href="Stlc.html#3764" class="InductiveConstructor Operator"
      >then</a
      ><a name="12651"
      > </a
      ><a name="12652" class="Symbol"
      >(</a
      ><a name="12653" href="Stlc.html#12601" class="Bound"
      >M&#8242;</a
      ><a name="12655"
      > </a
      ><a name="12656" href="Stlc.html#12266" class="Function Operator"
      >[</a
      ><a name="12657"
      > </a
      ><a name="12658" href="Stlc.html#12615" class="Bound"
      >x</a
      ><a name="12659"
      > </a
      ><a name="12660" href="Stlc.html#12266" class="Function Operator"
      >:=</a
      ><a name="12662"
      > </a
      ><a name="12663" href="Stlc.html#12620" class="Bound"
      >V</a
      ><a name="12664"
      > </a
      ><a name="12665" href="Stlc.html#12266" class="Function Operator"
      >]</a
      ><a name="12666" class="Symbol"
      >)</a
      ><a name="12667"
      > </a
      ><a name="12668" href="Stlc.html#3764" class="InductiveConstructor Operator"
      >else</a
      ><a name="12672"
      > </a
      ><a name="12673" class="Symbol"
      >(</a
      ><a name="12674" href="Stlc.html#12609" class="Bound"
      >N&#8242;</a
      ><a name="12676"
      > </a
      ><a name="12677" href="Stlc.html#12266" class="Function Operator"
      >[</a
      ><a name="12678"
      > </a
      ><a name="12679" href="Stlc.html#12615" class="Bound"
      >x</a
      ><a name="12680"
      > </a
      ><a name="12681" href="Stlc.html#12266" class="Function Operator"
      >:=</a
      ><a name="12683"
      > </a
      ><a name="12684" href="Stlc.html#12620" class="Bound"
      >V</a
      ><a name="12685"
      > </a
      ><a name="12686" href="Stlc.html#12266" class="Function Operator"
      >]</a
      ><a name="12687" class="Symbol"
      >)</a
      >

</pre>

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

<pre class="Agda">

<a name="13437" href="Stlc.html#13437" class="Function"
      >ex&#8321;&#8321;</a
      ><a name="13441"
      > </a
      ><a name="13442" class="Symbol"
      >:</a
      ><a name="13443"
      > </a
      ><a name="13444" href="Stlc.html#3656" class="InductiveConstructor"
      >`</a
      ><a name="13445"
      > </a
      ><a name="13446" href="Stlc.html#5677" class="Function"
      >f</a
      ><a name="13447"
      > </a
      ><a name="13448" href="Stlc.html#12266" class="Function Operator"
      >[</a
      ><a name="13449"
      > </a
      ><a name="13450" href="Stlc.html#5677" class="Function"
      >f</a
      ><a name="13451"
      > </a
      ><a name="13452" href="Stlc.html#12266" class="Function Operator"
      >:=</a
      ><a name="13454"
      > </a
      ><a name="13455" href="Stlc.html#5722" class="Function"
      >not</a
      ><a name="13458"
      > </a
      ><a name="13459" href="Stlc.html#12266" class="Function Operator"
      >]</a
      ><a name="13460"
      > </a
      ><a name="13461" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="13462"
      >  </a
      ><a name="13464" href="Stlc.html#5722" class="Function"
      >not</a
      ><a name="13467"
      >
</a
      ><a name="13468" href="Stlc.html#13437" class="Function"
      >ex&#8321;&#8321;</a
      ><a name="13472"
      > </a
      ><a name="13473" class="Symbol"
      >=</a
      ><a name="13474"
      > </a
      ><a name="13475" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="13479"
      >

</a
      ><a name="13481" href="Stlc.html#13481" class="Function"
      >ex&#8321;&#8322;</a
      ><a name="13485"
      > </a
      ><a name="13486" class="Symbol"
      >:</a
      ><a name="13487"
      > </a
      ><a name="13488" href="Stlc.html#3735" class="InductiveConstructor"
      >true</a
      ><a name="13492"
      > </a
      ><a name="13493" href="Stlc.html#12266" class="Function Operator"
      >[</a
      ><a name="13494"
      > </a
      ><a name="13495" href="Stlc.html#5677" class="Function"
      >f</a
      ><a name="13496"
      > </a
      ><a name="13497" href="Stlc.html#12266" class="Function Operator"
      >:=</a
      ><a name="13499"
      > </a
      ><a name="13500" href="Stlc.html#5722" class="Function"
      >not</a
      ><a name="13503"
      > </a
      ><a name="13504" href="Stlc.html#12266" class="Function Operator"
      >]</a
      ><a name="13505"
      > </a
      ><a name="13506" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="13507"
      > </a
      ><a name="13508" href="Stlc.html#3735" class="InductiveConstructor"
      >true</a
      ><a name="13512"
      >
</a
      ><a name="13513" href="Stlc.html#13481" class="Function"
      >ex&#8321;&#8322;</a
      ><a name="13517"
      > </a
      ><a name="13518" class="Symbol"
      >=</a
      ><a name="13519"
      > </a
      ><a name="13520" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="13524"
      >

</a
      ><a name="13526" href="Stlc.html#13526" class="Function"
      >ex&#8321;&#8323;</a
      ><a name="13530"
      > </a
      ><a name="13531" class="Symbol"
      >:</a
      ><a name="13532"
      > </a
      ><a name="13533" class="Symbol"
      >(</a
      ><a name="13534" href="Stlc.html#3656" class="InductiveConstructor"
      >`</a
      ><a name="13535"
      > </a
      ><a name="13536" href="Stlc.html#5677" class="Function"
      >f</a
      ><a name="13537"
      > </a
      ><a name="13538" href="Stlc.html#3708" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="13539"
      > </a
      ><a name="13540" href="Stlc.html#3735" class="InductiveConstructor"
      >true</a
      ><a name="13544" class="Symbol"
      >)</a
      ><a name="13545"
      > </a
      ><a name="13546" href="Stlc.html#12266" class="Function Operator"
      >[</a
      ><a name="13547"
      > </a
      ><a name="13548" href="Stlc.html#5677" class="Function"
      >f</a
      ><a name="13549"
      > </a
      ><a name="13550" href="Stlc.html#12266" class="Function Operator"
      >:=</a
      ><a name="13552"
      > </a
      ><a name="13553" href="Stlc.html#5722" class="Function"
      >not</a
      ><a name="13556"
      > </a
      ><a name="13557" href="Stlc.html#12266" class="Function Operator"
      >]</a
      ><a name="13558"
      > </a
      ><a name="13559" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="13560"
      > </a
      ><a name="13561" href="Stlc.html#5722" class="Function"
      >not</a
      ><a name="13564"
      > </a
      ><a name="13565" href="Stlc.html#3708" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="13566"
      > </a
      ><a name="13567" href="Stlc.html#3735" class="InductiveConstructor"
      >true</a
      ><a name="13571"
      >
</a
      ><a name="13572" href="Stlc.html#13526" class="Function"
      >ex&#8321;&#8323;</a
      ><a name="13576"
      > </a
      ><a name="13577" class="Symbol"
      >=</a
      ><a name="13578"
      > </a
      ><a name="13579" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="13583"
      >

</a
      ><a name="13585" href="Stlc.html#13585" class="Function"
      >ex&#8321;&#8324;</a
      ><a name="13589"
      > </a
      ><a name="13590" class="Symbol"
      >:</a
      ><a name="13591"
      > </a
      ><a name="13592" class="Symbol"
      >(</a
      ><a name="13593" href="Stlc.html#3656" class="InductiveConstructor"
      >`</a
      ><a name="13594"
      > </a
      ><a name="13595" href="Stlc.html#5677" class="Function"
      >f</a
      ><a name="13596"
      > </a
      ><a name="13597" href="Stlc.html#3708" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="13598"
      > </a
      ><a name="13599" class="Symbol"
      >(</a
      ><a name="13600" href="Stlc.html#3656" class="InductiveConstructor"
      >`</a
      ><a name="13601"
      > </a
      ><a name="13602" href="Stlc.html#5677" class="Function"
      >f</a
      ><a name="13603"
      > </a
      ><a name="13604" href="Stlc.html#3708" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="13605"
      > </a
      ><a name="13606" href="Stlc.html#3735" class="InductiveConstructor"
      >true</a
      ><a name="13610" class="Symbol"
      >))</a
      ><a name="13612"
      > </a
      ><a name="13613" href="Stlc.html#12266" class="Function Operator"
      >[</a
      ><a name="13614"
      > </a
      ><a name="13615" href="Stlc.html#5677" class="Function"
      >f</a
      ><a name="13616"
      > </a
      ><a name="13617" href="Stlc.html#12266" class="Function Operator"
      >:=</a
      ><a name="13619"
      > </a
      ><a name="13620" href="Stlc.html#5722" class="Function"
      >not</a
      ><a name="13623"
      > </a
      ><a name="13624" href="Stlc.html#12266" class="Function Operator"
      >]</a
      ><a name="13625"
      > </a
      ><a name="13626" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="13627"
      > </a
      ><a name="13628" href="Stlc.html#5722" class="Function"
      >not</a
      ><a name="13631"
      > </a
      ><a name="13632" href="Stlc.html#3708" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="13633"
      > </a
      ><a name="13634" class="Symbol"
      >(</a
      ><a name="13635" href="Stlc.html#5722" class="Function"
      >not</a
      ><a name="13638"
      > </a
      ><a name="13639" href="Stlc.html#3708" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="13640"
      > </a
      ><a name="13641" href="Stlc.html#3735" class="InductiveConstructor"
      >true</a
      ><a name="13645" class="Symbol"
      >)</a
      ><a name="13646"
      >
</a
      ><a name="13647" href="Stlc.html#13585" class="Function"
      >ex&#8321;&#8324;</a
      ><a name="13651"
      > </a
      ><a name="13652" class="Symbol"
      >=</a
      ><a name="13653"
      > </a
      ><a name="13654" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="13658"
      >

</a
      ><a name="13660" href="Stlc.html#13660" class="Function"
      >ex&#8321;&#8325;</a
      ><a name="13664"
      > </a
      ><a name="13665" class="Symbol"
      >:</a
      ><a name="13666"
      > </a
      ><a name="13667" class="Symbol"
      >(</a
      ><a name="13668" href="Stlc.html#3672" class="InductiveConstructor Operator"
      >&#955;[</a
      ><a name="13670"
      > </a
      ><a name="13671" href="Stlc.html#5679" class="Function"
      >x</a
      ><a name="13672"
      > </a
      ><a name="13673" href="Stlc.html#3672" class="InductiveConstructor Operator"
      >&#8758;</a
      ><a name="13674"
      > </a
      ><a name="13675" href="Stlc.html#2610" class="InductiveConstructor"
      >&#120121;</a
      ><a name="13676"
      > </a
      ><a name="13677" href="Stlc.html#3672" class="InductiveConstructor Operator"
      >]</a
      ><a name="13678"
      > </a
      ><a name="13679" href="Stlc.html#3656" class="InductiveConstructor"
      >`</a
      ><a name="13680"
      > </a
      ><a name="13681" href="Stlc.html#5677" class="Function"
      >f</a
      ><a name="13682"
      > </a
      ><a name="13683" href="Stlc.html#3708" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="13684"
      > </a
      ><a name="13685" class="Symbol"
      >(</a
      ><a name="13686" href="Stlc.html#3656" class="InductiveConstructor"
      >`</a
      ><a name="13687"
      > </a
      ><a name="13688" href="Stlc.html#5677" class="Function"
      >f</a
      ><a name="13689"
      > </a
      ><a name="13690" href="Stlc.html#3708" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="13691"
      > </a
      ><a name="13692" href="Stlc.html#3656" class="InductiveConstructor"
      >`</a
      ><a name="13693"
      > </a
      ><a name="13694" href="Stlc.html#5679" class="Function"
      >x</a
      ><a name="13695" class="Symbol"
      >))</a
      ><a name="13697"
      > </a
      ><a name="13698" href="Stlc.html#12266" class="Function Operator"
      >[</a
      ><a name="13699"
      > </a
      ><a name="13700" href="Stlc.html#5677" class="Function"
      >f</a
      ><a name="13701"
      > </a
      ><a name="13702" href="Stlc.html#12266" class="Function Operator"
      >:=</a
      ><a name="13704"
      > </a
      ><a name="13705" href="Stlc.html#5722" class="Function"
      >not</a
      ><a name="13708"
      > </a
      ><a name="13709" href="Stlc.html#12266" class="Function Operator"
      >]</a
      ><a name="13710"
      > </a
      ><a name="13711" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="13712"
      > </a
      ><a name="13713" href="Stlc.html#3672" class="InductiveConstructor Operator"
      >&#955;[</a
      ><a name="13715"
      > </a
      ><a name="13716" href="Stlc.html#5679" class="Function"
      >x</a
      ><a name="13717"
      > </a
      ><a name="13718" href="Stlc.html#3672" class="InductiveConstructor Operator"
      >&#8758;</a
      ><a name="13719"
      > </a
      ><a name="13720" href="Stlc.html#2610" class="InductiveConstructor"
      >&#120121;</a
      ><a name="13721"
      > </a
      ><a name="13722" href="Stlc.html#3672" class="InductiveConstructor Operator"
      >]</a
      ><a name="13723"
      > </a
      ><a name="13724" href="Stlc.html#5722" class="Function"
      >not</a
      ><a name="13727"
      > </a
      ><a name="13728" href="Stlc.html#3708" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="13729"
      > </a
      ><a name="13730" class="Symbol"
      >(</a
      ><a name="13731" href="Stlc.html#5722" class="Function"
      >not</a
      ><a name="13734"
      > </a
      ><a name="13735" href="Stlc.html#3708" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="13736"
      > </a
      ><a name="13737" href="Stlc.html#3656" class="InductiveConstructor"
      >`</a
      ><a name="13738"
      > </a
      ><a name="13739" href="Stlc.html#5679" class="Function"
      >x</a
      ><a name="13740" class="Symbol"
      >)</a
      ><a name="13741"
      >
</a
      ><a name="13742" href="Stlc.html#13660" class="Function"
      >ex&#8321;&#8325;</a
      ><a name="13746"
      > </a
      ><a name="13747" class="Symbol"
      >=</a
      ><a name="13748"
      > </a
      ><a name="13749" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="13753"
      >

</a
      ><a name="13755" href="Stlc.html#13755" class="Function"
      >ex&#8321;&#8326;</a
      ><a name="13759"
      > </a
      ><a name="13760" class="Symbol"
      >:</a
      ><a name="13761"
      > </a
      ><a name="13762" class="Symbol"
      >(</a
      ><a name="13763" href="Stlc.html#3672" class="InductiveConstructor Operator"
      >&#955;[</a
      ><a name="13765"
      > </a
      ><a name="13766" href="Stlc.html#5681" class="Function"
      >y</a
      ><a name="13767"
      > </a
      ><a name="13768" href="Stlc.html#3672" class="InductiveConstructor Operator"
      >&#8758;</a
      ><a name="13769"
      > </a
      ><a name="13770" href="Stlc.html#2610" class="InductiveConstructor"
      >&#120121;</a
      ><a name="13771"
      > </a
      ><a name="13772" href="Stlc.html#3672" class="InductiveConstructor Operator"
      >]</a
      ><a name="13773"
      > </a
      ><a name="13774" href="Stlc.html#3656" class="InductiveConstructor"
      >`</a
      ><a name="13775"
      > </a
      ><a name="13776" href="Stlc.html#5681" class="Function"
      >y</a
      ><a name="13777" class="Symbol"
      >)</a
      ><a name="13778"
      > </a
      ><a name="13779" href="Stlc.html#12266" class="Function Operator"
      >[</a
      ><a name="13780"
      > </a
      ><a name="13781" href="Stlc.html#5679" class="Function"
      >x</a
      ><a name="13782"
      > </a
      ><a name="13783" href="Stlc.html#12266" class="Function Operator"
      >:=</a
      ><a name="13785"
      > </a
      ><a name="13786" href="Stlc.html#3735" class="InductiveConstructor"
      >true</a
      ><a name="13790"
      > </a
      ><a name="13791" href="Stlc.html#12266" class="Function Operator"
      >]</a
      ><a name="13792"
      > </a
      ><a name="13793" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="13794"
      > </a
      ><a name="13795" href="Stlc.html#3672" class="InductiveConstructor Operator"
      >&#955;[</a
      ><a name="13797"
      > </a
      ><a name="13798" href="Stlc.html#5681" class="Function"
      >y</a
      ><a name="13799"
      > </a
      ><a name="13800" href="Stlc.html#3672" class="InductiveConstructor Operator"
      >&#8758;</a
      ><a name="13801"
      > </a
      ><a name="13802" href="Stlc.html#2610" class="InductiveConstructor"
      >&#120121;</a
      ><a name="13803"
      > </a
      ><a name="13804" href="Stlc.html#3672" class="InductiveConstructor Operator"
      >]</a
      ><a name="13805"
      > </a
      ><a name="13806" href="Stlc.html#3656" class="InductiveConstructor"
      >`</a
      ><a name="13807"
      > </a
      ><a name="13808" href="Stlc.html#5681" class="Function"
      >y</a
      ><a name="13809"
      >
</a
      ><a name="13810" href="Stlc.html#13755" class="Function"
      >ex&#8321;&#8326;</a
      ><a name="13814"
      > </a
      ><a name="13815" class="Symbol"
      >=</a
      ><a name="13816"
      > </a
      ><a name="13817" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="13821"
      >

</a
      ><a name="13823" href="Stlc.html#13823" class="Function"
      >ex&#8321;&#8327;</a
      ><a name="13827"
      > </a
      ><a name="13828" class="Symbol"
      >:</a
      ><a name="13829"
      > </a
      ><a name="13830" class="Symbol"
      >(</a
      ><a name="13831" href="Stlc.html#3672" class="InductiveConstructor Operator"
      >&#955;[</a
      ><a name="13833"
      > </a
      ><a name="13834" href="Stlc.html#5679" class="Function"
      >x</a
      ><a name="13835"
      > </a
      ><a name="13836" href="Stlc.html#3672" class="InductiveConstructor Operator"
      >&#8758;</a
      ><a name="13837"
      > </a
      ><a name="13838" href="Stlc.html#2610" class="InductiveConstructor"
      >&#120121;</a
      ><a name="13839"
      > </a
      ><a name="13840" href="Stlc.html#3672" class="InductiveConstructor Operator"
      >]</a
      ><a name="13841"
      > </a
      ><a name="13842" href="Stlc.html#3656" class="InductiveConstructor"
      >`</a
      ><a name="13843"
      > </a
      ><a name="13844" href="Stlc.html#5679" class="Function"
      >x</a
      ><a name="13845" class="Symbol"
      >)</a
      ><a name="13846"
      > </a
      ><a name="13847" href="Stlc.html#12266" class="Function Operator"
      >[</a
      ><a name="13848"
      > </a
      ><a name="13849" href="Stlc.html#5679" class="Function"
      >x</a
      ><a name="13850"
      > </a
      ><a name="13851" href="Stlc.html#12266" class="Function Operator"
      >:=</a
      ><a name="13853"
      > </a
      ><a name="13854" href="Stlc.html#3735" class="InductiveConstructor"
      >true</a
      ><a name="13858"
      > </a
      ><a name="13859" href="Stlc.html#12266" class="Function Operator"
      >]</a
      ><a name="13860"
      > </a
      ><a name="13861" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="13862"
      > </a
      ><a name="13863" href="Stlc.html#3672" class="InductiveConstructor Operator"
      >&#955;[</a
      ><a name="13865"
      > </a
      ><a name="13866" href="Stlc.html#5679" class="Function"
      >x</a
      ><a name="13867"
      > </a
      ><a name="13868" href="Stlc.html#3672" class="InductiveConstructor Operator"
      >&#8758;</a
      ><a name="13869"
      > </a
      ><a name="13870" href="Stlc.html#2610" class="InductiveConstructor"
      >&#120121;</a
      ><a name="13871"
      > </a
      ><a name="13872" href="Stlc.html#3672" class="InductiveConstructor Operator"
      >]</a
      ><a name="13873"
      > </a
      ><a name="13874" href="Stlc.html#3656" class="InductiveConstructor"
      >`</a
      ><a name="13875"
      > </a
      ><a name="13876" href="Stlc.html#5679" class="Function"
      >x</a
      ><a name="13877"
      >
</a
      ><a name="13878" href="Stlc.html#13823" class="Function"
      >ex&#8321;&#8327;</a
      ><a name="13882"
      > </a
      ><a name="13883" class="Symbol"
      >=</a
      ><a name="13884"
      > </a
      ><a name="13885" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      >

</pre>

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

<pre class="Agda">

<a name="15999" class="Keyword"
      >infix</a
      ><a name="16004"
      > </a
      ><a name="16005" class="Number"
      >10</a
      ><a name="16007"
      > </a
      ><a name="16008" href="Stlc.html#16019" class="Datatype Operator"
      >_&#10233;_</a
      ><a name="16011"
      > 

</a
      ><a name="16014" class="Keyword"
      >data</a
      ><a name="16018"
      > </a
      ><a name="16019" href="Stlc.html#16019" class="Datatype Operator"
      >_&#10233;_</a
      ><a name="16022"
      > </a
      ><a name="16023" class="Symbol"
      >:</a
      ><a name="16024"
      > </a
      ><a name="16025" href="Stlc.html#3637" class="Datatype"
      >Term</a
      ><a name="16029"
      > </a
      ><a name="16030" class="Symbol"
      >&#8594;</a
      ><a name="16031"
      > </a
      ><a name="16032" href="Stlc.html#3637" class="Datatype"
      >Term</a
      ><a name="16036"
      > </a
      ><a name="16037" class="Symbol"
      >&#8594;</a
      ><a name="16038"
      > </a
      ><a name="16039" class="PrimitiveType"
      >Set</a
      ><a name="16042"
      > </a
      ><a name="16043" class="Keyword"
      >where</a
      ><a name="16048"
      >
  </a
      ><a name="16051" href="Stlc.html#16051" class="InductiveConstructor"
      >&#958;&#183;&#8321;</a
      ><a name="16054"
      > </a
      ><a name="16055" class="Symbol"
      >:</a
      ><a name="16056"
      > </a
      ><a name="16057" class="Symbol"
      >&#8704;</a
      ><a name="16058"
      > </a
      ><a name="16059" class="Symbol"
      >{</a
      ><a name="16060" href="Stlc.html#16060" class="Bound"
      >L</a
      ><a name="16061"
      > </a
      ><a name="16062" href="Stlc.html#16062" class="Bound"
      >L&#8242;</a
      ><a name="16064"
      > </a
      ><a name="16065" href="Stlc.html#16065" class="Bound"
      >M</a
      ><a name="16066" class="Symbol"
      >}</a
      ><a name="16067"
      > </a
      ><a name="16068" class="Symbol"
      >&#8594;</a
      ><a name="16069"
      >
    </a
      ><a name="16074" href="Stlc.html#16060" class="Bound"
      >L</a
      ><a name="16075"
      > </a
      ><a name="16076" href="Stlc.html#16019" class="Datatype Operator"
      >&#10233;</a
      ><a name="16077"
      > </a
      ><a name="16078" href="Stlc.html#16062" class="Bound"
      >L&#8242;</a
      ><a name="16080"
      > </a
      ><a name="16081" class="Symbol"
      >&#8594;</a
      ><a name="16082"
      >
    </a
      ><a name="16087" href="Stlc.html#16060" class="Bound"
      >L</a
      ><a name="16088"
      > </a
      ><a name="16089" href="Stlc.html#3708" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="16090"
      > </a
      ><a name="16091" href="Stlc.html#16065" class="Bound"
      >M</a
      ><a name="16092"
      > </a
      ><a name="16093" href="Stlc.html#16019" class="Datatype Operator"
      >&#10233;</a
      ><a name="16094"
      > </a
      ><a name="16095" href="Stlc.html#16062" class="Bound"
      >L&#8242;</a
      ><a name="16097"
      > </a
      ><a name="16098" href="Stlc.html#3708" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="16099"
      > </a
      ><a name="16100" href="Stlc.html#16065" class="Bound"
      >M</a
      ><a name="16101"
      >
  </a
      ><a name="16104" href="Stlc.html#16104" class="InductiveConstructor"
      >&#958;&#183;&#8322;</a
      ><a name="16107"
      > </a
      ><a name="16108" class="Symbol"
      >:</a
      ><a name="16109"
      > </a
      ><a name="16110" class="Symbol"
      >&#8704;</a
      ><a name="16111"
      > </a
      ><a name="16112" class="Symbol"
      >{</a
      ><a name="16113" href="Stlc.html#16113" class="Bound"
      >V</a
      ><a name="16114"
      > </a
      ><a name="16115" href="Stlc.html#16115" class="Bound"
      >M</a
      ><a name="16116"
      > </a
      ><a name="16117" href="Stlc.html#16117" class="Bound"
      >M&#8242;</a
      ><a name="16119" class="Symbol"
      >}</a
      ><a name="16120"
      > </a
      ><a name="16121" class="Symbol"
      >&#8594;</a
      ><a name="16122"
      >
    </a
      ><a name="16127" href="Stlc.html#9722" class="Datatype"
      >Value</a
      ><a name="16132"
      > </a
      ><a name="16133" href="Stlc.html#16113" class="Bound"
      >V</a
      ><a name="16134"
      > </a
      ><a name="16135" class="Symbol"
      >&#8594;</a
      ><a name="16136"
      >
    </a
      ><a name="16141" href="Stlc.html#16115" class="Bound"
      >M</a
      ><a name="16142"
      > </a
      ><a name="16143" href="Stlc.html#16019" class="Datatype Operator"
      >&#10233;</a
      ><a name="16144"
      > </a
      ><a name="16145" href="Stlc.html#16117" class="Bound"
      >M&#8242;</a
      ><a name="16147"
      > </a
      ><a name="16148" class="Symbol"
      >&#8594;</a
      ><a name="16149"
      >
    </a
      ><a name="16154" href="Stlc.html#16113" class="Bound"
      >V</a
      ><a name="16155"
      > </a
      ><a name="16156" href="Stlc.html#3708" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="16157"
      > </a
      ><a name="16158" href="Stlc.html#16115" class="Bound"
      >M</a
      ><a name="16159"
      > </a
      ><a name="16160" href="Stlc.html#16019" class="Datatype Operator"
      >&#10233;</a
      ><a name="16161"
      > </a
      ><a name="16162" href="Stlc.html#16113" class="Bound"
      >V</a
      ><a name="16163"
      > </a
      ><a name="16164" href="Stlc.html#3708" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="16165"
      > </a
      ><a name="16166" href="Stlc.html#16117" class="Bound"
      >M&#8242;</a
      ><a name="16168"
      >
  </a
      ><a name="16171" href="Stlc.html#16171" class="InductiveConstructor"
      >&#946;&#955;&#183;</a
      ><a name="16174"
      > </a
      ><a name="16175" class="Symbol"
      >:</a
      ><a name="16176"
      > </a
      ><a name="16177" class="Symbol"
      >&#8704;</a
      ><a name="16178"
      > </a
      ><a name="16179" class="Symbol"
      >{</a
      ><a name="16180" href="Stlc.html#16180" class="Bound"
      >x</a
      ><a name="16181"
      > </a
      ><a name="16182" href="Stlc.html#16182" class="Bound"
      >A</a
      ><a name="16183"
      > </a
      ><a name="16184" href="Stlc.html#16184" class="Bound"
      >N</a
      ><a name="16185"
      > </a
      ><a name="16186" href="Stlc.html#16186" class="Bound"
      >V</a
      ><a name="16187" class="Symbol"
      >}</a
      ><a name="16188"
      > </a
      ><a name="16189" class="Symbol"
      >&#8594;</a
      ><a name="16190"
      > </a
      ><a name="16191" href="Stlc.html#9722" class="Datatype"
      >Value</a
      ><a name="16196"
      > </a
      ><a name="16197" href="Stlc.html#16186" class="Bound"
      >V</a
      ><a name="16198"
      > </a
      ><a name="16199" class="Symbol"
      >&#8594;</a
      ><a name="16200"
      >
    </a
      ><a name="16205" class="Symbol"
      >(</a
      ><a name="16206" href="Stlc.html#3672" class="InductiveConstructor Operator"
      >&#955;[</a
      ><a name="16208"
      > </a
      ><a name="16209" href="Stlc.html#16180" class="Bound"
      >x</a
      ><a name="16210"
      > </a
      ><a name="16211" href="Stlc.html#3672" class="InductiveConstructor Operator"
      >&#8758;</a
      ><a name="16212"
      > </a
      ><a name="16213" href="Stlc.html#16182" class="Bound"
      >A</a
      ><a name="16214"
      > </a
      ><a name="16215" href="Stlc.html#3672" class="InductiveConstructor Operator"
      >]</a
      ><a name="16216"
      > </a
      ><a name="16217" href="Stlc.html#16184" class="Bound"
      >N</a
      ><a name="16218" class="Symbol"
      >)</a
      ><a name="16219"
      > </a
      ><a name="16220" href="Stlc.html#3708" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="16221"
      > </a
      ><a name="16222" href="Stlc.html#16186" class="Bound"
      >V</a
      ><a name="16223"
      > </a
      ><a name="16224" href="Stlc.html#16019" class="Datatype Operator"
      >&#10233;</a
      ><a name="16225"
      > </a
      ><a name="16226" href="Stlc.html#16184" class="Bound"
      >N</a
      ><a name="16227"
      > </a
      ><a name="16228" href="Stlc.html#12266" class="Function Operator"
      >[</a
      ><a name="16229"
      > </a
      ><a name="16230" href="Stlc.html#16180" class="Bound"
      >x</a
      ><a name="16231"
      > </a
      ><a name="16232" href="Stlc.html#12266" class="Function Operator"
      >:=</a
      ><a name="16234"
      > </a
      ><a name="16235" href="Stlc.html#16186" class="Bound"
      >V</a
      ><a name="16236"
      > </a
      ><a name="16237" href="Stlc.html#12266" class="Function Operator"
      >]</a
      ><a name="16238"
      >
  </a
      ><a name="16241" href="Stlc.html#16241" class="InductiveConstructor"
      >&#958;if</a
      ><a name="16244"
      > </a
      ><a name="16245" class="Symbol"
      >:</a
      ><a name="16246"
      > </a
      ><a name="16247" class="Symbol"
      >&#8704;</a
      ><a name="16248"
      > </a
      ><a name="16249" class="Symbol"
      >{</a
      ><a name="16250" href="Stlc.html#16250" class="Bound"
      >L</a
      ><a name="16251"
      > </a
      ><a name="16252" href="Stlc.html#16252" class="Bound"
      >L&#8242;</a
      ><a name="16254"
      > </a
      ><a name="16255" href="Stlc.html#16255" class="Bound"
      >M</a
      ><a name="16256"
      > </a
      ><a name="16257" href="Stlc.html#16257" class="Bound"
      >N</a
      ><a name="16258" class="Symbol"
      >}</a
      ><a name="16259"
      > </a
      ><a name="16260" class="Symbol"
      >&#8594;</a
      ><a name="16261"
      >
    </a
      ><a name="16266" href="Stlc.html#16250" class="Bound"
      >L</a
      ><a name="16267"
      > </a
      ><a name="16268" href="Stlc.html#16019" class="Datatype Operator"
      >&#10233;</a
      ><a name="16269"
      > </a
      ><a name="16270" href="Stlc.html#16252" class="Bound"
      >L&#8242;</a
      ><a name="16272"
      > </a
      ><a name="16273" class="Symbol"
      >&#8594;</a
      ><a name="16274"
      >    
    </a
      ><a name="16283" href="Stlc.html#3764" class="InductiveConstructor Operator"
      >if</a
      ><a name="16285"
      > </a
      ><a name="16286" href="Stlc.html#16250" class="Bound"
      >L</a
      ><a name="16287"
      > </a
      ><a name="16288" href="Stlc.html#3764" class="InductiveConstructor Operator"
      >then</a
      ><a name="16292"
      > </a
      ><a name="16293" href="Stlc.html#16255" class="Bound"
      >M</a
      ><a name="16294"
      > </a
      ><a name="16295" href="Stlc.html#3764" class="InductiveConstructor Operator"
      >else</a
      ><a name="16299"
      > </a
      ><a name="16300" href="Stlc.html#16257" class="Bound"
      >N</a
      ><a name="16301"
      > </a
      ><a name="16302" href="Stlc.html#16019" class="Datatype Operator"
      >&#10233;</a
      ><a name="16303"
      > </a
      ><a name="16304" href="Stlc.html#3764" class="InductiveConstructor Operator"
      >if</a
      ><a name="16306"
      > </a
      ><a name="16307" href="Stlc.html#16252" class="Bound"
      >L&#8242;</a
      ><a name="16309"
      > </a
      ><a name="16310" href="Stlc.html#3764" class="InductiveConstructor Operator"
      >then</a
      ><a name="16314"
      > </a
      ><a name="16315" href="Stlc.html#16255" class="Bound"
      >M</a
      ><a name="16316"
      > </a
      ><a name="16317" href="Stlc.html#3764" class="InductiveConstructor Operator"
      >else</a
      ><a name="16321"
      > </a
      ><a name="16322" href="Stlc.html#16257" class="Bound"
      >N</a
      ><a name="16323"
      >
  </a
      ><a name="16326" href="Stlc.html#16326" class="InductiveConstructor"
      >&#946;if-true</a
      ><a name="16334"
      > </a
      ><a name="16335" class="Symbol"
      >:</a
      ><a name="16336"
      > </a
      ><a name="16337" class="Symbol"
      >&#8704;</a
      ><a name="16338"
      > </a
      ><a name="16339" class="Symbol"
      >{</a
      ><a name="16340" href="Stlc.html#16340" class="Bound"
      >M</a
      ><a name="16341"
      > </a
      ><a name="16342" href="Stlc.html#16342" class="Bound"
      >N</a
      ><a name="16343" class="Symbol"
      >}</a
      ><a name="16344"
      > </a
      ><a name="16345" class="Symbol"
      >&#8594;</a
      ><a name="16346"
      >
    </a
      ><a name="16351" href="Stlc.html#3764" class="InductiveConstructor Operator"
      >if</a
      ><a name="16353"
      > </a
      ><a name="16354" href="Stlc.html#3735" class="InductiveConstructor"
      >true</a
      ><a name="16358"
      > </a
      ><a name="16359" href="Stlc.html#3764" class="InductiveConstructor Operator"
      >then</a
      ><a name="16363"
      > </a
      ><a name="16364" href="Stlc.html#16340" class="Bound"
      >M</a
      ><a name="16365"
      > </a
      ><a name="16366" href="Stlc.html#3764" class="InductiveConstructor Operator"
      >else</a
      ><a name="16370"
      > </a
      ><a name="16371" href="Stlc.html#16342" class="Bound"
      >N</a
      ><a name="16372"
      > </a
      ><a name="16373" href="Stlc.html#16019" class="Datatype Operator"
      >&#10233;</a
      ><a name="16374"
      > </a
      ><a name="16375" href="Stlc.html#16340" class="Bound"
      >M</a
      ><a name="16376"
      >
  </a
      ><a name="16379" href="Stlc.html#16379" class="InductiveConstructor"
      >&#946;if-false</a
      ><a name="16388"
      > </a
      ><a name="16389" class="Symbol"
      >:</a
      ><a name="16390"
      > </a
      ><a name="16391" class="Symbol"
      >&#8704;</a
      ><a name="16392"
      > </a
      ><a name="16393" class="Symbol"
      >{</a
      ><a name="16394" href="Stlc.html#16394" class="Bound"
      >M</a
      ><a name="16395"
      > </a
      ><a name="16396" href="Stlc.html#16396" class="Bound"
      >N</a
      ><a name="16397" class="Symbol"
      >}</a
      ><a name="16398"
      > </a
      ><a name="16399" class="Symbol"
      >&#8594;</a
      ><a name="16400"
      >
    </a
      ><a name="16405" href="Stlc.html#3764" class="InductiveConstructor Operator"
      >if</a
      ><a name="16407"
      > </a
      ><a name="16408" href="Stlc.html#3749" class="InductiveConstructor"
      >false</a
      ><a name="16413"
      > </a
      ><a name="16414" href="Stlc.html#3764" class="InductiveConstructor Operator"
      >then</a
      ><a name="16418"
      > </a
      ><a name="16419" href="Stlc.html#16394" class="Bound"
      >M</a
      ><a name="16420"
      > </a
      ><a name="16421" href="Stlc.html#3764" class="InductiveConstructor Operator"
      >else</a
      ><a name="16425"
      > </a
      ><a name="16426" href="Stlc.html#16396" class="Bound"
      >N</a
      ><a name="16427"
      > </a
      ><a name="16428" href="Stlc.html#16019" class="Datatype Operator"
      >&#10233;</a
      ><a name="16429"
      > </a
      ><a name="16430" href="Stlc.html#16396" class="Bound"
      >N</a
      >

</pre>

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

<pre class="Agda">

<a name="18004" class="Keyword"
      >infix</a
      ><a name="18009"
      > </a
      ><a name="18010" class="Number"
      >10</a
      ><a name="18012"
      > </a
      ><a name="18013" href="Stlc.html#18053" class="Datatype Operator"
      >_&#10233;*_</a
      ><a name="18017"
      > 
</a
      ><a name="18019" class="Keyword"
      >infixr</a
      ><a name="18025"
      > </a
      ><a name="18026" class="Number"
      >2</a
      ><a name="18027"
      > </a
      ><a name="18028" href="Stlc.html#18106" class="InductiveConstructor Operator"
      >_&#10233;&#10216;_&#10217;_</a
      ><a name="18034"
      >
</a
      ><a name="18035" class="Keyword"
      >infix</a
      ><a name="18040"
      >  </a
      ><a name="18042" class="Number"
      >3</a
      ><a name="18043"
      > </a
      ><a name="18044" href="Stlc.html#18086" class="InductiveConstructor Operator"
      >_&#8718;</a
      ><a name="18046"
      >

</a
      ><a name="18048" class="Keyword"
      >data</a
      ><a name="18052"
      > </a
      ><a name="18053" href="Stlc.html#18053" class="Datatype Operator"
      >_&#10233;*_</a
      ><a name="18057"
      > </a
      ><a name="18058" class="Symbol"
      >:</a
      ><a name="18059"
      > </a
      ><a name="18060" href="Stlc.html#3637" class="Datatype"
      >Term</a
      ><a name="18064"
      > </a
      ><a name="18065" class="Symbol"
      >&#8594;</a
      ><a name="18066"
      > </a
      ><a name="18067" href="Stlc.html#3637" class="Datatype"
      >Term</a
      ><a name="18071"
      > </a
      ><a name="18072" class="Symbol"
      >&#8594;</a
      ><a name="18073"
      > </a
      ><a name="18074" class="PrimitiveType"
      >Set</a
      ><a name="18077"
      > </a
      ><a name="18078" class="Keyword"
      >where</a
      ><a name="18083"
      >
  </a
      ><a name="18086" href="Stlc.html#18086" class="InductiveConstructor Operator"
      >_&#8718;</a
      ><a name="18088"
      > </a
      ><a name="18089" class="Symbol"
      >:</a
      ><a name="18090"
      > </a
      ><a name="18091" class="Symbol"
      >&#8704;</a
      ><a name="18092"
      > </a
      ><a name="18093" href="Stlc.html#18093" class="Bound"
      >M</a
      ><a name="18094"
      > </a
      ><a name="18095" class="Symbol"
      >&#8594;</a
      ><a name="18096"
      > </a
      ><a name="18097" href="Stlc.html#18093" class="Bound"
      >M</a
      ><a name="18098"
      > </a
      ><a name="18099" href="Stlc.html#18053" class="Datatype Operator"
      >&#10233;*</a
      ><a name="18101"
      > </a
      ><a name="18102" href="Stlc.html#18093" class="Bound"
      >M</a
      ><a name="18103"
      >
  </a
      ><a name="18106" href="Stlc.html#18106" class="InductiveConstructor Operator"
      >_&#10233;&#10216;_&#10217;_</a
      ><a name="18112"
      > </a
      ><a name="18113" class="Symbol"
      >:</a
      ><a name="18114"
      > </a
      ><a name="18115" class="Symbol"
      >&#8704;</a
      ><a name="18116"
      > </a
      ><a name="18117" href="Stlc.html#18117" class="Bound"
      >L</a
      ><a name="18118"
      > </a
      ><a name="18119" class="Symbol"
      >{</a
      ><a name="18120" href="Stlc.html#18120" class="Bound"
      >M</a
      ><a name="18121"
      > </a
      ><a name="18122" href="Stlc.html#18122" class="Bound"
      >N</a
      ><a name="18123" class="Symbol"
      >}</a
      ><a name="18124"
      > </a
      ><a name="18125" class="Symbol"
      >&#8594;</a
      ><a name="18126"
      > </a
      ><a name="18127" href="Stlc.html#18117" class="Bound"
      >L</a
      ><a name="18128"
      > </a
      ><a name="18129" href="Stlc.html#16019" class="Datatype Operator"
      >&#10233;</a
      ><a name="18130"
      > </a
      ><a name="18131" href="Stlc.html#18120" class="Bound"
      >M</a
      ><a name="18132"
      > </a
      ><a name="18133" class="Symbol"
      >&#8594;</a
      ><a name="18134"
      > </a
      ><a name="18135" href="Stlc.html#18120" class="Bound"
      >M</a
      ><a name="18136"
      > </a
      ><a name="18137" href="Stlc.html#18053" class="Datatype Operator"
      >&#10233;*</a
      ><a name="18139"
      > </a
      ><a name="18140" href="Stlc.html#18122" class="Bound"
      >N</a
      ><a name="18141"
      > </a
      ><a name="18142" class="Symbol"
      >&#8594;</a
      ><a name="18143"
      > </a
      ><a name="18144" href="Stlc.html#18117" class="Bound"
      >L</a
      ><a name="18145"
      > </a
      ><a name="18146" href="Stlc.html#18053" class="Datatype Operator"
      >&#10233;*</a
      ><a name="18148"
      > </a
      ><a name="18149" href="Stlc.html#18122" class="Bound"
      >N</a
      >

</pre>

We can read this as follows.

* From term `M`, we can take no steps, giving `M ∎` of type `M ⟹* M`.

* From term `L` we can take a single step `L⟹M` of type `L ⟹ M`
  followed by zero or more steps `M⟹*N` of type `M ⟹* N`,
  giving `L ⟨ L⟹M ⟩ M⟹*N` of type `L ⟹* N`.

The names of the two clauses in the definition of reflexive
and transitive closure have been chosen to allow us to lay
out example reductions in an appealing way.

<pre class="Agda">

<a name="18610" href="Stlc.html#18610" class="Function"
      >reduction&#8321;</a
      ><a name="18620"
      > </a
      ><a name="18621" class="Symbol"
      >:</a
      ><a name="18622"
      > </a
      ><a name="18623" href="Stlc.html#5722" class="Function"
      >not</a
      ><a name="18626"
      > </a
      ><a name="18627" href="Stlc.html#3708" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="18628"
      > </a
      ><a name="18629" href="Stlc.html#3735" class="InductiveConstructor"
      >true</a
      ><a name="18633"
      > </a
      ><a name="18634" href="Stlc.html#18053" class="Datatype Operator"
      >&#10233;*</a
      ><a name="18636"
      > </a
      ><a name="18637" href="Stlc.html#3749" class="InductiveConstructor"
      >false</a
      ><a name="18642"
      >
</a
      ><a name="18643" href="Stlc.html#18610" class="Function"
      >reduction&#8321;</a
      ><a name="18653"
      > </a
      ><a name="18654" class="Symbol"
      >=</a
      ><a name="18655"
      >
    </a
      ><a name="18660" href="Stlc.html#5722" class="Function"
      >not</a
      ><a name="18663"
      > </a
      ><a name="18664" href="Stlc.html#3708" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="18665"
      > </a
      ><a name="18666" href="Stlc.html#3735" class="InductiveConstructor"
      >true</a
      ><a name="18670"
      >
  </a
      ><a name="18673" href="Stlc.html#18106" class="InductiveConstructor Operator"
      >&#10233;&#10216;</a
      ><a name="18675"
      > </a
      ><a name="18676" href="Stlc.html#16171" class="InductiveConstructor"
      >&#946;&#955;&#183;</a
      ><a name="18679"
      > </a
      ><a name="18680" href="Stlc.html#9798" class="InductiveConstructor"
      >value-true</a
      ><a name="18690"
      > </a
      ><a name="18691" href="Stlc.html#18106" class="InductiveConstructor Operator"
      >&#10217;</a
      ><a name="18692"
      >
    </a
      ><a name="18697" href="Stlc.html#3764" class="InductiveConstructor Operator"
      >if</a
      ><a name="18699"
      > </a
      ><a name="18700" href="Stlc.html#3735" class="InductiveConstructor"
      >true</a
      ><a name="18704"
      > </a
      ><a name="18705" href="Stlc.html#3764" class="InductiveConstructor Operator"
      >then</a
      ><a name="18709"
      > </a
      ><a name="18710" href="Stlc.html#3749" class="InductiveConstructor"
      >false</a
      ><a name="18715"
      > </a
      ><a name="18716" href="Stlc.html#3764" class="InductiveConstructor Operator"
      >else</a
      ><a name="18720"
      > </a
      ><a name="18721" href="Stlc.html#3735" class="InductiveConstructor"
      >true</a
      ><a name="18725"
      >
  </a
      ><a name="18728" href="Stlc.html#18106" class="InductiveConstructor Operator"
      >&#10233;&#10216;</a
      ><a name="18730"
      > </a
      ><a name="18731" href="Stlc.html#16326" class="InductiveConstructor"
      >&#946;if-true</a
      ><a name="18739"
      > </a
      ><a name="18740" href="Stlc.html#18106" class="InductiveConstructor Operator"
      >&#10217;</a
      ><a name="18741"
      >
    </a
      ><a name="18746" href="Stlc.html#3749" class="InductiveConstructor"
      >false</a
      ><a name="18751"
      >
  </a
      ><a name="18754" href="Stlc.html#18086" class="InductiveConstructor Operator"
      >&#8718;</a
      ><a name="18755"
      >

</a
      ><a name="18757" href="Stlc.html#18757" class="Function"
      >reduction&#8322;</a
      ><a name="18767"
      > </a
      ><a name="18768" class="Symbol"
      >:</a
      ><a name="18769"
      > </a
      ><a name="18770" href="Stlc.html#5726" class="Function"
      >two</a
      ><a name="18773"
      > </a
      ><a name="18774" href="Stlc.html#3708" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="18775"
      > </a
      ><a name="18776" href="Stlc.html#5722" class="Function"
      >not</a
      ><a name="18779"
      > </a
      ><a name="18780" href="Stlc.html#3708" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="18781"
      > </a
      ><a name="18782" href="Stlc.html#3735" class="InductiveConstructor"
      >true</a
      ><a name="18786"
      > </a
      ><a name="18787" href="Stlc.html#18053" class="Datatype Operator"
      >&#10233;*</a
      ><a name="18789"
      > </a
      ><a name="18790" href="Stlc.html#3735" class="InductiveConstructor"
      >true</a
      ><a name="18794"
      >
</a
      ><a name="18795" href="Stlc.html#18757" class="Function"
      >reduction&#8322;</a
      ><a name="18805"
      > </a
      ><a name="18806" class="Symbol"
      >=</a
      ><a name="18807"
      >
    </a
      ><a name="18812" href="Stlc.html#5726" class="Function"
      >two</a
      ><a name="18815"
      > </a
      ><a name="18816" href="Stlc.html#3708" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="18817"
      > </a
      ><a name="18818" href="Stlc.html#5722" class="Function"
      >not</a
      ><a name="18821"
      > </a
      ><a name="18822" href="Stlc.html#3708" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="18823"
      > </a
      ><a name="18824" href="Stlc.html#3735" class="InductiveConstructor"
      >true</a
      ><a name="18828"
      >
  </a
      ><a name="18831" href="Stlc.html#18106" class="InductiveConstructor Operator"
      >&#10233;&#10216;</a
      ><a name="18833"
      > </a
      ><a name="18834" href="Stlc.html#16051" class="InductiveConstructor"
      >&#958;&#183;&#8321;</a
      ><a name="18837"
      > </a
      ><a name="18838" class="Symbol"
      >(</a
      ><a name="18839" href="Stlc.html#16171" class="InductiveConstructor"
      >&#946;&#955;&#183;</a
      ><a name="18842"
      > </a
      ><a name="18843" href="Stlc.html#9749" class="InductiveConstructor"
      >value-&#955;</a
      ><a name="18850" class="Symbol"
      >)</a
      ><a name="18851"
      > </a
      ><a name="18852" href="Stlc.html#18106" class="InductiveConstructor Operator"
      >&#10217;</a
      ><a name="18853"
      >
    </a
      ><a name="18858" class="Symbol"
      >(</a
      ><a name="18859" href="Stlc.html#3672" class="InductiveConstructor Operator"
      >&#955;[</a
      ><a name="18861"
      > </a
      ><a name="18862" href="Stlc.html#5679" class="Function"
      >x</a
      ><a name="18863"
      > </a
      ><a name="18864" href="Stlc.html#3672" class="InductiveConstructor Operator"
      >&#8758;</a
      ><a name="18865"
      > </a
      ><a name="18866" href="Stlc.html#2610" class="InductiveConstructor"
      >&#120121;</a
      ><a name="18867"
      > </a
      ><a name="18868" href="Stlc.html#3672" class="InductiveConstructor Operator"
      >]</a
      ><a name="18869"
      > </a
      ><a name="18870" href="Stlc.html#5722" class="Function"
      >not</a
      ><a name="18873"
      > </a
      ><a name="18874" href="Stlc.html#3708" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="18875"
      > </a
      ><a name="18876" class="Symbol"
      >(</a
      ><a name="18877" href="Stlc.html#5722" class="Function"
      >not</a
      ><a name="18880"
      > </a
      ><a name="18881" href="Stlc.html#3708" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="18882"
      > </a
      ><a name="18883" href="Stlc.html#3656" class="InductiveConstructor"
      >`</a
      ><a name="18884"
      > </a
      ><a name="18885" href="Stlc.html#5679" class="Function"
      >x</a
      ><a name="18886" class="Symbol"
      >))</a
      ><a name="18888"
      > </a
      ><a name="18889" href="Stlc.html#3708" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="18890"
      > </a
      ><a name="18891" href="Stlc.html#3735" class="InductiveConstructor"
      >true</a
      ><a name="18895"
      >
  </a
      ><a name="18898" href="Stlc.html#18106" class="InductiveConstructor Operator"
      >&#10233;&#10216;</a
      ><a name="18900"
      > </a
      ><a name="18901" href="Stlc.html#16171" class="InductiveConstructor"
      >&#946;&#955;&#183;</a
      ><a name="18904"
      > </a
      ><a name="18905" href="Stlc.html#9798" class="InductiveConstructor"
      >value-true</a
      ><a name="18915"
      > </a
      ><a name="18916" href="Stlc.html#18106" class="InductiveConstructor Operator"
      >&#10217;</a
      ><a name="18917"
      >
    </a
      ><a name="18922" href="Stlc.html#5722" class="Function"
      >not</a
      ><a name="18925"
      > </a
      ><a name="18926" href="Stlc.html#3708" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="18927"
      > </a
      ><a name="18928" class="Symbol"
      >(</a
      ><a name="18929" href="Stlc.html#5722" class="Function"
      >not</a
      ><a name="18932"
      > </a
      ><a name="18933" href="Stlc.html#3708" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="18934"
      > </a
      ><a name="18935" href="Stlc.html#3735" class="InductiveConstructor"
      >true</a
      ><a name="18939" class="Symbol"
      >)</a
      ><a name="18940"
      >
  </a
      ><a name="18943" href="Stlc.html#18106" class="InductiveConstructor Operator"
      >&#10233;&#10216;</a
      ><a name="18945"
      > </a
      ><a name="18946" href="Stlc.html#16104" class="InductiveConstructor"
      >&#958;&#183;&#8322;</a
      ><a name="18949"
      > </a
      ><a name="18950" href="Stlc.html#9749" class="InductiveConstructor"
      >value-&#955;</a
      ><a name="18957"
      > </a
      ><a name="18958" class="Symbol"
      >(</a
      ><a name="18959" href="Stlc.html#16171" class="InductiveConstructor"
      >&#946;&#955;&#183;</a
      ><a name="18962"
      > </a
      ><a name="18963" href="Stlc.html#9798" class="InductiveConstructor"
      >value-true</a
      ><a name="18973" class="Symbol"
      >)</a
      ><a name="18974"
      > </a
      ><a name="18975" href="Stlc.html#18106" class="InductiveConstructor Operator"
      >&#10217;</a
      ><a name="18976"
      >
    </a
      ><a name="18981" href="Stlc.html#5722" class="Function"
      >not</a
      ><a name="18984"
      > </a
      ><a name="18985" href="Stlc.html#3708" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="18986"
      > </a
      ><a name="18987" class="Symbol"
      >(</a
      ><a name="18988" href="Stlc.html#3764" class="InductiveConstructor Operator"
      >if</a
      ><a name="18990"
      > </a
      ><a name="18991" href="Stlc.html#3735" class="InductiveConstructor"
      >true</a
      ><a name="18995"
      > </a
      ><a name="18996" href="Stlc.html#3764" class="InductiveConstructor Operator"
      >then</a
      ><a name="19000"
      > </a
      ><a name="19001" href="Stlc.html#3749" class="InductiveConstructor"
      >false</a
      ><a name="19006"
      > </a
      ><a name="19007" href="Stlc.html#3764" class="InductiveConstructor Operator"
      >else</a
      ><a name="19011"
      > </a
      ><a name="19012" href="Stlc.html#3735" class="InductiveConstructor"
      >true</a
      ><a name="19016" class="Symbol"
      >)</a
      ><a name="19017"
      >
  </a
      ><a name="19020" href="Stlc.html#18106" class="InductiveConstructor Operator"
      >&#10233;&#10216;</a
      ><a name="19022"
      > </a
      ><a name="19023" href="Stlc.html#16104" class="InductiveConstructor"
      >&#958;&#183;&#8322;</a
      ><a name="19026"
      > </a
      ><a name="19027" href="Stlc.html#9749" class="InductiveConstructor"
      >value-&#955;</a
      ><a name="19034"
      > </a
      ><a name="19035" href="Stlc.html#16326" class="InductiveConstructor"
      >&#946;if-true</a
      ><a name="19043"
      >  </a
      ><a name="19045" href="Stlc.html#18106" class="InductiveConstructor Operator"
      >&#10217;</a
      ><a name="19046"
      >
    </a
      ><a name="19051" href="Stlc.html#5722" class="Function"
      >not</a
      ><a name="19054"
      > </a
      ><a name="19055" href="Stlc.html#3708" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="19056"
      > </a
      ><a name="19057" href="Stlc.html#3749" class="InductiveConstructor"
      >false</a
      ><a name="19062"
      >
  </a
      ><a name="19065" href="Stlc.html#18106" class="InductiveConstructor Operator"
      >&#10233;&#10216;</a
      ><a name="19067"
      > </a
      ><a name="19068" href="Stlc.html#16171" class="InductiveConstructor"
      >&#946;&#955;&#183;</a
      ><a name="19071"
      > </a
      ><a name="19072" href="Stlc.html#9825" class="InductiveConstructor"
      >value-false</a
      ><a name="19083"
      > </a
      ><a name="19084" href="Stlc.html#18106" class="InductiveConstructor Operator"
      >&#10217;</a
      ><a name="19085"
      >
    </a
      ><a name="19090" href="Stlc.html#3764" class="InductiveConstructor Operator"
      >if</a
      ><a name="19092"
      > </a
      ><a name="19093" href="Stlc.html#3749" class="InductiveConstructor"
      >false</a
      ><a name="19098"
      > </a
      ><a name="19099" href="Stlc.html#3764" class="InductiveConstructor Operator"
      >then</a
      ><a name="19103"
      > </a
      ><a name="19104" href="Stlc.html#3749" class="InductiveConstructor"
      >false</a
      ><a name="19109"
      > </a
      ><a name="19110" href="Stlc.html#3764" class="InductiveConstructor Operator"
      >else</a
      ><a name="19114"
      > </a
      ><a name="19115" href="Stlc.html#3735" class="InductiveConstructor"
      >true</a
      ><a name="19119"
      >
  </a
      ><a name="19122" href="Stlc.html#18106" class="InductiveConstructor Operator"
      >&#10233;&#10216;</a
      ><a name="19124"
      > </a
      ><a name="19125" href="Stlc.html#16379" class="InductiveConstructor"
      >&#946;if-false</a
      ><a name="19134"
      > </a
      ><a name="19135" href="Stlc.html#18106" class="InductiveConstructor Operator"
      >&#10217;</a
      ><a name="19136"
      >
    </a
      ><a name="19141" href="Stlc.html#3735" class="InductiveConstructor"
      >true</a
      ><a name="19145"
      >
  </a
      ><a name="19148" href="Stlc.html#18086" class="InductiveConstructor Operator"
      >&#8718;</a
      >

</pre>

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

<pre class="Agda">

<a name="21694" href="Stlc.html#21694" class="Function"
      >Context</a
      ><a name="21701"
      > </a
      ><a name="21702" class="Symbol"
      >:</a
      ><a name="21703"
      > </a
      ><a name="21704" class="PrimitiveType"
      >Set</a
      ><a name="21707"
      >
</a
      ><a name="21708" href="Stlc.html#21694" class="Function"
      >Context</a
      ><a name="21715"
      > </a
      ><a name="21716" class="Symbol"
      >=</a
      ><a name="21717"
      > </a
      ><a name="21718" href="Maps.html#10132" class="Function"
      >PartialMap</a
      ><a name="21728"
      > </a
      ><a name="21729" href="Stlc.html#2564" class="Datatype"
      >Type</a
      ><a name="21733"
      >

</a
      ><a name="21735" class="Keyword"
      >infix</a
      ><a name="21740"
      > </a
      ><a name="21741" class="Number"
      >10</a
      ><a name="21743"
      > </a
      ><a name="21744" href="Stlc.html#21756" class="Datatype Operator"
      >_&#8866;_&#8758;_</a
      ><a name="21749"
      >

</a
      ><a name="21751" class="Keyword"
      >data</a
      ><a name="21755"
      > </a
      ><a name="21756" href="Stlc.html#21756" class="Datatype Operator"
      >_&#8866;_&#8758;_</a
      ><a name="21761"
      > </a
      ><a name="21762" class="Symbol"
      >:</a
      ><a name="21763"
      > </a
      ><a name="21764" href="Stlc.html#21694" class="Function"
      >Context</a
      ><a name="21771"
      > </a
      ><a name="21772" class="Symbol"
      >&#8594;</a
      ><a name="21773"
      > </a
      ><a name="21774" href="Stlc.html#3637" class="Datatype"
      >Term</a
      ><a name="21778"
      > </a
      ><a name="21779" class="Symbol"
      >&#8594;</a
      ><a name="21780"
      > </a
      ><a name="21781" href="Stlc.html#2564" class="Datatype"
      >Type</a
      ><a name="21785"
      > </a
      ><a name="21786" class="Symbol"
      >&#8594;</a
      ><a name="21787"
      > </a
      ><a name="21788" class="PrimitiveType"
      >Set</a
      ><a name="21791"
      > </a
      ><a name="21792" class="Keyword"
      >where</a
      ><a name="21797"
      >
  </a
      ><a name="21800" href="Stlc.html#21800" class="InductiveConstructor"
      >Ax</a
      ><a name="21802"
      > </a
      ><a name="21803" class="Symbol"
      >:</a
      ><a name="21804"
      > </a
      ><a name="21805" class="Symbol"
      >&#8704;</a
      ><a name="21806"
      > </a
      ><a name="21807" class="Symbol"
      >{</a
      ><a name="21808" href="Stlc.html#21808" class="Bound"
      >&#915;</a
      ><a name="21809"
      > </a
      ><a name="21810" href="Stlc.html#21810" class="Bound"
      >x</a
      ><a name="21811"
      > </a
      ><a name="21812" href="Stlc.html#21812" class="Bound"
      >A</a
      ><a name="21813" class="Symbol"
      >}</a
      ><a name="21814"
      > </a
      ><a name="21815" class="Symbol"
      >&#8594;</a
      ><a name="21816"
      >
    </a
      ><a name="21821" href="Stlc.html#21808" class="Bound"
      >&#915;</a
      ><a name="21822"
      > </a
      ><a name="21823" href="Stlc.html#21810" class="Bound"
      >x</a
      ><a name="21824"
      > </a
      ><a name="21825" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="21826"
      > </a
      ><a name="21827" href="https://agda.github.io/agda-stdlib/Data.Maybe.Base.html#373" class="InductiveConstructor"
      >just</a
      ><a name="21831"
      > </a
      ><a name="21832" href="Stlc.html#21812" class="Bound"
      >A</a
      ><a name="21833"
      > </a
      ><a name="21834" class="Symbol"
      >&#8594;</a
      ><a name="21835"
      >
    </a
      ><a name="21840" href="Stlc.html#21808" class="Bound"
      >&#915;</a
      ><a name="21841"
      > </a
      ><a name="21842" href="Stlc.html#21756" class="Datatype Operator"
      >&#8866;</a
      ><a name="21843"
      > </a
      ><a name="21844" href="Stlc.html#3656" class="InductiveConstructor"
      >`</a
      ><a name="21845"
      > </a
      ><a name="21846" href="Stlc.html#21810" class="Bound"
      >x</a
      ><a name="21847"
      > </a
      ><a name="21848" href="Stlc.html#21756" class="Datatype Operator"
      >&#8758;</a
      ><a name="21849"
      > </a
      ><a name="21850" href="Stlc.html#21812" class="Bound"
      >A</a
      ><a name="21851"
      >
  </a
      ><a name="21854" href="Stlc.html#21854" class="InductiveConstructor"
      >&#8658;-I</a
      ><a name="21857"
      > </a
      ><a name="21858" class="Symbol"
      >:</a
      ><a name="21859"
      > </a
      ><a name="21860" class="Symbol"
      >&#8704;</a
      ><a name="21861"
      > </a
      ><a name="21862" class="Symbol"
      >{</a
      ><a name="21863" href="Stlc.html#21863" class="Bound"
      >&#915;</a
      ><a name="21864"
      > </a
      ><a name="21865" href="Stlc.html#21865" class="Bound"
      >x</a
      ><a name="21866"
      > </a
      ><a name="21867" href="Stlc.html#21867" class="Bound"
      >N</a
      ><a name="21868"
      > </a
      ><a name="21869" href="Stlc.html#21869" class="Bound"
      >A</a
      ><a name="21870"
      > </a
      ><a name="21871" href="Stlc.html#21871" class="Bound"
      >B</a
      ><a name="21872" class="Symbol"
      >}</a
      ><a name="21873"
      > </a
      ><a name="21874" class="Symbol"
      >&#8594;</a
      ><a name="21875"
      >
    </a
      ><a name="21880" href="Stlc.html#21863" class="Bound"
      >&#915;</a
      ><a name="21881"
      > </a
      ><a name="21882" href="Maps.html#10368" class="Function Operator"
      >,</a
      ><a name="21883"
      > </a
      ><a name="21884" href="Stlc.html#21865" class="Bound"
      >x</a
      ><a name="21885"
      > </a
      ><a name="21886" href="Maps.html#10368" class="Function Operator"
      >&#8758;</a
      ><a name="21887"
      > </a
      ><a name="21888" href="Stlc.html#21869" class="Bound"
      >A</a
      ><a name="21889"
      > </a
      ><a name="21890" href="Stlc.html#21756" class="Datatype Operator"
      >&#8866;</a
      ><a name="21891"
      > </a
      ><a name="21892" href="Stlc.html#21867" class="Bound"
      >N</a
      ><a name="21893"
      > </a
      ><a name="21894" href="Stlc.html#21756" class="Datatype Operator"
      >&#8758;</a
      ><a name="21895"
      > </a
      ><a name="21896" href="Stlc.html#21871" class="Bound"
      >B</a
      ><a name="21897"
      > </a
      ><a name="21898" class="Symbol"
      >&#8594;</a
      ><a name="21899"
      >
    </a
      ><a name="21904" href="Stlc.html#21863" class="Bound"
      >&#915;</a
      ><a name="21905"
      > </a
      ><a name="21906" href="Stlc.html#21756" class="Datatype Operator"
      >&#8866;</a
      ><a name="21907"
      > </a
      ><a name="21908" href="Stlc.html#3672" class="InductiveConstructor Operator"
      >&#955;[</a
      ><a name="21910"
      > </a
      ><a name="21911" href="Stlc.html#21865" class="Bound"
      >x</a
      ><a name="21912"
      > </a
      ><a name="21913" href="Stlc.html#3672" class="InductiveConstructor Operator"
      >&#8758;</a
      ><a name="21914"
      > </a
      ><a name="21915" href="Stlc.html#21869" class="Bound"
      >A</a
      ><a name="21916"
      > </a
      ><a name="21917" href="Stlc.html#3672" class="InductiveConstructor Operator"
      >]</a
      ><a name="21918"
      > </a
      ><a name="21919" href="Stlc.html#21867" class="Bound"
      >N</a
      ><a name="21920"
      > </a
      ><a name="21921" href="Stlc.html#21756" class="Datatype Operator"
      >&#8758;</a
      ><a name="21922"
      > </a
      ><a name="21923" href="Stlc.html#21869" class="Bound"
      >A</a
      ><a name="21924"
      > </a
      ><a name="21925" href="Stlc.html#2583" class="InductiveConstructor Operator"
      >&#8658;</a
      ><a name="21926"
      > </a
      ><a name="21927" href="Stlc.html#21871" class="Bound"
      >B</a
      ><a name="21928"
      >
  </a
      ><a name="21931" href="Stlc.html#21931" class="InductiveConstructor"
      >&#8658;-E</a
      ><a name="21934"
      > </a
      ><a name="21935" class="Symbol"
      >:</a
      ><a name="21936"
      > </a
      ><a name="21937" class="Symbol"
      >&#8704;</a
      ><a name="21938"
      > </a
      ><a name="21939" class="Symbol"
      >{</a
      ><a name="21940" href="Stlc.html#21940" class="Bound"
      >&#915;</a
      ><a name="21941"
      > </a
      ><a name="21942" href="Stlc.html#21942" class="Bound"
      >L</a
      ><a name="21943"
      > </a
      ><a name="21944" href="Stlc.html#21944" class="Bound"
      >M</a
      ><a name="21945"
      > </a
      ><a name="21946" href="Stlc.html#21946" class="Bound"
      >A</a
      ><a name="21947"
      > </a
      ><a name="21948" href="Stlc.html#21948" class="Bound"
      >B</a
      ><a name="21949" class="Symbol"
      >}</a
      ><a name="21950"
      > </a
      ><a name="21951" class="Symbol"
      >&#8594;</a
      ><a name="21952"
      >
    </a
      ><a name="21957" href="Stlc.html#21940" class="Bound"
      >&#915;</a
      ><a name="21958"
      > </a
      ><a name="21959" href="Stlc.html#21756" class="Datatype Operator"
      >&#8866;</a
      ><a name="21960"
      > </a
      ><a name="21961" href="Stlc.html#21942" class="Bound"
      >L</a
      ><a name="21962"
      > </a
      ><a name="21963" href="Stlc.html#21756" class="Datatype Operator"
      >&#8758;</a
      ><a name="21964"
      > </a
      ><a name="21965" href="Stlc.html#21946" class="Bound"
      >A</a
      ><a name="21966"
      > </a
      ><a name="21967" href="Stlc.html#2583" class="InductiveConstructor Operator"
      >&#8658;</a
      ><a name="21968"
      > </a
      ><a name="21969" href="Stlc.html#21948" class="Bound"
      >B</a
      ><a name="21970"
      > </a
      ><a name="21971" class="Symbol"
      >&#8594;</a
      ><a name="21972"
      >
    </a
      ><a name="21977" href="Stlc.html#21940" class="Bound"
      >&#915;</a
      ><a name="21978"
      > </a
      ><a name="21979" href="Stlc.html#21756" class="Datatype Operator"
      >&#8866;</a
      ><a name="21980"
      > </a
      ><a name="21981" href="Stlc.html#21944" class="Bound"
      >M</a
      ><a name="21982"
      > </a
      ><a name="21983" href="Stlc.html#21756" class="Datatype Operator"
      >&#8758;</a
      ><a name="21984"
      > </a
      ><a name="21985" href="Stlc.html#21946" class="Bound"
      >A</a
      ><a name="21986"
      > </a
      ><a name="21987" class="Symbol"
      >&#8594;</a
      ><a name="21988"
      >
    </a
      ><a name="21993" href="Stlc.html#21940" class="Bound"
      >&#915;</a
      ><a name="21994"
      > </a
      ><a name="21995" href="Stlc.html#21756" class="Datatype Operator"
      >&#8866;</a
      ><a name="21996"
      > </a
      ><a name="21997" href="Stlc.html#21942" class="Bound"
      >L</a
      ><a name="21998"
      > </a
      ><a name="21999" href="Stlc.html#3708" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="22000"
      > </a
      ><a name="22001" href="Stlc.html#21944" class="Bound"
      >M</a
      ><a name="22002"
      > </a
      ><a name="22003" href="Stlc.html#21756" class="Datatype Operator"
      >&#8758;</a
      ><a name="22004"
      > </a
      ><a name="22005" href="Stlc.html#21948" class="Bound"
      >B</a
      ><a name="22006"
      >
  </a
      ><a name="22009" href="Stlc.html#22009" class="InductiveConstructor"
      >&#120121;-I&#8321;</a
      ><a name="22013"
      > </a
      ><a name="22014" class="Symbol"
      >:</a
      ><a name="22015"
      > </a
      ><a name="22016" class="Symbol"
      >&#8704;</a
      ><a name="22017"
      > </a
      ><a name="22018" class="Symbol"
      >{</a
      ><a name="22019" href="Stlc.html#22019" class="Bound"
      >&#915;</a
      ><a name="22020" class="Symbol"
      >}</a
      ><a name="22021"
      > </a
      ><a name="22022" class="Symbol"
      >&#8594;</a
      ><a name="22023"
      >
    </a
      ><a name="22028" href="Stlc.html#22019" class="Bound"
      >&#915;</a
      ><a name="22029"
      > </a
      ><a name="22030" href="Stlc.html#21756" class="Datatype Operator"
      >&#8866;</a
      ><a name="22031"
      > </a
      ><a name="22032" href="Stlc.html#3735" class="InductiveConstructor"
      >true</a
      ><a name="22036"
      > </a
      ><a name="22037" href="Stlc.html#21756" class="Datatype Operator"
      >&#8758;</a
      ><a name="22038"
      > </a
      ><a name="22039" href="Stlc.html#2610" class="InductiveConstructor"
      >&#120121;</a
      ><a name="22040"
      >
  </a
      ><a name="22043" href="Stlc.html#22043" class="InductiveConstructor"
      >&#120121;-I&#8322;</a
      ><a name="22047"
      > </a
      ><a name="22048" class="Symbol"
      >:</a
      ><a name="22049"
      > </a
      ><a name="22050" class="Symbol"
      >&#8704;</a
      ><a name="22051"
      > </a
      ><a name="22052" class="Symbol"
      >{</a
      ><a name="22053" href="Stlc.html#22053" class="Bound"
      >&#915;</a
      ><a name="22054" class="Symbol"
      >}</a
      ><a name="22055"
      > </a
      ><a name="22056" class="Symbol"
      >&#8594;</a
      ><a name="22057"
      >
    </a
      ><a name="22062" href="Stlc.html#22053" class="Bound"
      >&#915;</a
      ><a name="22063"
      > </a
      ><a name="22064" href="Stlc.html#21756" class="Datatype Operator"
      >&#8866;</a
      ><a name="22065"
      > </a
      ><a name="22066" href="Stlc.html#3749" class="InductiveConstructor"
      >false</a
      ><a name="22071"
      > </a
      ><a name="22072" href="Stlc.html#21756" class="Datatype Operator"
      >&#8758;</a
      ><a name="22073"
      > </a
      ><a name="22074" href="Stlc.html#2610" class="InductiveConstructor"
      >&#120121;</a
      ><a name="22075"
      >
  </a
      ><a name="22078" href="Stlc.html#22078" class="InductiveConstructor"
      >&#120121;-E</a
      ><a name="22081"
      > </a
      ><a name="22082" class="Symbol"
      >:</a
      ><a name="22083"
      > </a
      ><a name="22084" class="Symbol"
      >&#8704;</a
      ><a name="22085"
      > </a
      ><a name="22086" class="Symbol"
      >{</a
      ><a name="22087" href="Stlc.html#22087" class="Bound"
      >&#915;</a
      ><a name="22088"
      > </a
      ><a name="22089" href="Stlc.html#22089" class="Bound"
      >L</a
      ><a name="22090"
      > </a
      ><a name="22091" href="Stlc.html#22091" class="Bound"
      >M</a
      ><a name="22092"
      > </a
      ><a name="22093" href="Stlc.html#22093" class="Bound"
      >N</a
      ><a name="22094"
      > </a
      ><a name="22095" href="Stlc.html#22095" class="Bound"
      >A</a
      ><a name="22096" class="Symbol"
      >}</a
      ><a name="22097"
      > </a
      ><a name="22098" class="Symbol"
      >&#8594;</a
      ><a name="22099"
      >
    </a
      ><a name="22104" href="Stlc.html#22087" class="Bound"
      >&#915;</a
      ><a name="22105"
      > </a
      ><a name="22106" href="Stlc.html#21756" class="Datatype Operator"
      >&#8866;</a
      ><a name="22107"
      > </a
      ><a name="22108" href="Stlc.html#22089" class="Bound"
      >L</a
      ><a name="22109"
      > </a
      ><a name="22110" href="Stlc.html#21756" class="Datatype Operator"
      >&#8758;</a
      ><a name="22111"
      > </a
      ><a name="22112" href="Stlc.html#2610" class="InductiveConstructor"
      >&#120121;</a
      ><a name="22113"
      > </a
      ><a name="22114" class="Symbol"
      >&#8594;</a
      ><a name="22115"
      >
    </a
      ><a name="22120" href="Stlc.html#22087" class="Bound"
      >&#915;</a
      ><a name="22121"
      > </a
      ><a name="22122" href="Stlc.html#21756" class="Datatype Operator"
      >&#8866;</a
      ><a name="22123"
      > </a
      ><a name="22124" href="Stlc.html#22091" class="Bound"
      >M</a
      ><a name="22125"
      > </a
      ><a name="22126" href="Stlc.html#21756" class="Datatype Operator"
      >&#8758;</a
      ><a name="22127"
      > </a
      ><a name="22128" href="Stlc.html#22095" class="Bound"
      >A</a
      ><a name="22129"
      > </a
      ><a name="22130" class="Symbol"
      >&#8594;</a
      ><a name="22131"
      >
    </a
      ><a name="22136" href="Stlc.html#22087" class="Bound"
      >&#915;</a
      ><a name="22137"
      > </a
      ><a name="22138" href="Stlc.html#21756" class="Datatype Operator"
      >&#8866;</a
      ><a name="22139"
      > </a
      ><a name="22140" href="Stlc.html#22093" class="Bound"
      >N</a
      ><a name="22141"
      > </a
      ><a name="22142" href="Stlc.html#21756" class="Datatype Operator"
      >&#8758;</a
      ><a name="22143"
      > </a
      ><a name="22144" href="Stlc.html#22095" class="Bound"
      >A</a
      ><a name="22145"
      > </a
      ><a name="22146" class="Symbol"
      >&#8594;</a
      ><a name="22147"
      >
    </a
      ><a name="22152" href="Stlc.html#22087" class="Bound"
      >&#915;</a
      ><a name="22153"
      > </a
      ><a name="22154" href="Stlc.html#21756" class="Datatype Operator"
      >&#8866;</a
      ><a name="22155"
      > </a
      ><a name="22156" href="Stlc.html#3764" class="InductiveConstructor Operator"
      >if</a
      ><a name="22158"
      > </a
      ><a name="22159" href="Stlc.html#22089" class="Bound"
      >L</a
      ><a name="22160"
      > </a
      ><a name="22161" href="Stlc.html#3764" class="InductiveConstructor Operator"
      >then</a
      ><a name="22165"
      > </a
      ><a name="22166" href="Stlc.html#22091" class="Bound"
      >M</a
      ><a name="22167"
      > </a
      ><a name="22168" href="Stlc.html#3764" class="InductiveConstructor Operator"
      >else</a
      ><a name="22172"
      > </a
      ><a name="22173" href="Stlc.html#22093" class="Bound"
      >N</a
      ><a name="22174"
      > </a
      ><a name="22175" href="Stlc.html#21756" class="Datatype Operator"
      >&#8758;</a
      ><a name="22176"
      > </a
      ><a name="22177" href="Stlc.html#22095" class="Bound"
      >A</a
      >

</pre>

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

<pre class="Agda">

<a name="23460" href="Stlc.html#23460" class="Function"
      >typing&#8321;</a
      ><a name="23467"
      > </a
      ><a name="23468" class="Symbol"
      >:</a
      ><a name="23469"
      > </a
      ><a name="23470" href="Maps.html#10265" class="Function"
      >&#8709;</a
      ><a name="23471"
      > </a
      ><a name="23472" href="Stlc.html#21756" class="Datatype Operator"
      >&#8866;</a
      ><a name="23473"
      > </a
      ><a name="23474" href="Stlc.html#5722" class="Function"
      >not</a
      ><a name="23477"
      > </a
      ><a name="23478" href="Stlc.html#21756" class="Datatype Operator"
      >&#8758;</a
      ><a name="23479"
      > </a
      ><a name="23480" href="Stlc.html#2610" class="InductiveConstructor"
      >&#120121;</a
      ><a name="23481"
      > </a
      ><a name="23482" href="Stlc.html#2583" class="InductiveConstructor Operator"
      >&#8658;</a
      ><a name="23483"
      > </a
      ><a name="23484" href="Stlc.html#2610" class="InductiveConstructor"
      >&#120121;</a
      ><a name="23485"
      >
</a
      ><a name="23486" href="Stlc.html#23460" class="Function"
      >typing&#8321;</a
      ><a name="23493"
      > </a
      ><a name="23494" class="Symbol"
      >=</a
      ><a name="23495"
      > </a
      ><a name="23496" href="Stlc.html#21854" class="InductiveConstructor"
      >&#8658;-I</a
      ><a name="23499"
      > </a
      ><a name="23500" class="Symbol"
      >(</a
      ><a name="23501" href="Stlc.html#22078" class="InductiveConstructor"
      >&#120121;-E</a
      ><a name="23504"
      > </a
      ><a name="23505" class="Symbol"
      >(</a
      ><a name="23506" href="Stlc.html#21800" class="InductiveConstructor"
      >Ax</a
      ><a name="23508"
      > </a
      ><a name="23509" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="23513" class="Symbol"
      >)</a
      ><a name="23514"
      > </a
      ><a name="23515" href="Stlc.html#22043" class="InductiveConstructor"
      >&#120121;-I&#8322;</a
      ><a name="23519"
      > </a
      ><a name="23520" href="Stlc.html#22009" class="InductiveConstructor"
      >&#120121;-I&#8321;</a
      ><a name="23524" class="Symbol"
      >)</a
      ><a name="23525"
      >

</a
      ><a name="23527" href="Stlc.html#23527" class="Function"
      >typing&#8322;</a
      ><a name="23534"
      > </a
      ><a name="23535" class="Symbol"
      >:</a
      ><a name="23536"
      > </a
      ><a name="23537" href="Maps.html#10265" class="Function"
      >&#8709;</a
      ><a name="23538"
      > </a
      ><a name="23539" href="Stlc.html#21756" class="Datatype Operator"
      >&#8866;</a
      ><a name="23540"
      > </a
      ><a name="23541" href="Stlc.html#5726" class="Function"
      >two</a
      ><a name="23544"
      > </a
      ><a name="23545" href="Stlc.html#21756" class="Datatype Operator"
      >&#8758;</a
      ><a name="23546"
      > </a
      ><a name="23547" class="Symbol"
      >(</a
      ><a name="23548" href="Stlc.html#2610" class="InductiveConstructor"
      >&#120121;</a
      ><a name="23549"
      > </a
      ><a name="23550" href="Stlc.html#2583" class="InductiveConstructor Operator"
      >&#8658;</a
      ><a name="23551"
      > </a
      ><a name="23552" href="Stlc.html#2610" class="InductiveConstructor"
      >&#120121;</a
      ><a name="23553" class="Symbol"
      >)</a
      ><a name="23554"
      > </a
      ><a name="23555" href="Stlc.html#2583" class="InductiveConstructor Operator"
      >&#8658;</a
      ><a name="23556"
      > </a
      ><a name="23557" href="Stlc.html#2610" class="InductiveConstructor"
      >&#120121;</a
      ><a name="23558"
      > </a
      ><a name="23559" href="Stlc.html#2583" class="InductiveConstructor Operator"
      >&#8658;</a
      ><a name="23560"
      > </a
      ><a name="23561" href="Stlc.html#2610" class="InductiveConstructor"
      >&#120121;</a
      ><a name="23562"
      >
</a
      ><a name="23563" href="Stlc.html#23527" class="Function"
      >typing&#8322;</a
      ><a name="23570"
      > </a
      ><a name="23571" class="Symbol"
      >=</a
      ><a name="23572"
      > </a
      ><a name="23573" href="Stlc.html#21854" class="InductiveConstructor"
      >&#8658;-I</a
      ><a name="23576"
      > </a
      ><a name="23577" class="Symbol"
      >(</a
      ><a name="23578" href="Stlc.html#21854" class="InductiveConstructor"
      >&#8658;-I</a
      ><a name="23581"
      > </a
      ><a name="23582" class="Symbol"
      >(</a
      ><a name="23583" href="Stlc.html#21931" class="InductiveConstructor"
      >&#8658;-E</a
      ><a name="23586"
      > </a
      ><a name="23587" class="Symbol"
      >(</a
      ><a name="23588" href="Stlc.html#21800" class="InductiveConstructor"
      >Ax</a
      ><a name="23590"
      > </a
      ><a name="23591" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="23595" class="Symbol"
      >)</a
      ><a name="23596"
      > </a
      ><a name="23597" class="Symbol"
      >(</a
      ><a name="23598" href="Stlc.html#21931" class="InductiveConstructor"
      >&#8658;-E</a
      ><a name="23601"
      > </a
      ><a name="23602" class="Symbol"
      >(</a
      ><a name="23603" href="Stlc.html#21800" class="InductiveConstructor"
      >Ax</a
      ><a name="23605"
      > </a
      ><a name="23606" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="23610" class="Symbol"
      >)</a
      ><a name="23611"
      > </a
      ><a name="23612" class="Symbol"
      >(</a
      ><a name="23613" href="Stlc.html#21800" class="InductiveConstructor"
      >Ax</a
      ><a name="23615"
      > </a
      ><a name="23616" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="23620" class="Symbol"
      >))))</a
      >

</pre>

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

<pre class="Agda">

<a name="25301" href="Stlc.html#25301" class="Function"
      >notyping&#8322;</a
      ><a name="25310"
      > </a
      ><a name="25311" class="Symbol"
      >:</a
      ><a name="25312"
      > </a
      ><a name="25313" class="Symbol"
      >&#8704;</a
      ><a name="25314"
      > </a
      ><a name="25315" class="Symbol"
      >{</a
      ><a name="25316" href="Stlc.html#25316" class="Bound"
      >A</a
      ><a name="25317" class="Symbol"
      >}</a
      ><a name="25318"
      > </a
      ><a name="25319" class="Symbol"
      >&#8594;</a
      ><a name="25320"
      > </a
      ><a name="25321" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#414" class="Function Operator"
      >&#172;</a
      ><a name="25322"
      > </a
      ><a name="25323" class="Symbol"
      >(</a
      ><a name="25324" href="Maps.html#10265" class="Function"
      >&#8709;</a
      ><a name="25325"
      > </a
      ><a name="25326" href="Stlc.html#21756" class="Datatype Operator"
      >&#8866;</a
      ><a name="25327"
      > </a
      ><a name="25328" href="Stlc.html#3735" class="InductiveConstructor"
      >true</a
      ><a name="25332"
      > </a
      ><a name="25333" href="Stlc.html#3708" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="25334"
      > </a
      ><a name="25335" href="Stlc.html#3749" class="InductiveConstructor"
      >false</a
      ><a name="25340"
      > </a
      ><a name="25341" href="Stlc.html#21756" class="Datatype Operator"
      >&#8758;</a
      ><a name="25342"
      > </a
      ><a name="25343" href="Stlc.html#25316" class="Bound"
      >A</a
      ><a name="25344" class="Symbol"
      >)</a
      ><a name="25345"
      >
</a
      ><a name="25346" href="Stlc.html#25301" class="Function"
      >notyping&#8322;</a
      ><a name="25355"
      > </a
      ><a name="25356" class="Symbol"
      >(</a
      ><a name="25357" href="Stlc.html#21931" class="InductiveConstructor"
      >&#8658;-E</a
      ><a name="25360"
      > </a
      ><a name="25361" class="Symbol"
      >()</a
      ><a name="25363"
      > </a
      ><a name="25364" class="Symbol"
      >_)</a
      >

</pre>

As a second example, here is a formal proof that it is not possible to
type `` λ[ x ∶ 𝔹 ] λ[ y ∶ 𝔹 ] ` x · ` y `` It cannot be typed, because
doing so requires `x` to be both boolean and a function.

<pre class="Agda">

<a name="25592" href="Stlc.html#25592" class="Function"
      >contradiction</a
      ><a name="25605"
      > </a
      ><a name="25606" class="Symbol"
      >:</a
      ><a name="25607"
      > </a
      ><a name="25608" class="Symbol"
      >&#8704;</a
      ><a name="25609"
      > </a
      ><a name="25610" class="Symbol"
      >{</a
      ><a name="25611" href="Stlc.html#25611" class="Bound"
      >A</a
      ><a name="25612"
      > </a
      ><a name="25613" href="Stlc.html#25613" class="Bound"
      >B</a
      ><a name="25614" class="Symbol"
      >}</a
      ><a name="25615"
      > </a
      ><a name="25616" class="Symbol"
      >&#8594;</a
      ><a name="25617"
      > </a
      ><a name="25618" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#414" class="Function Operator"
      >&#172;</a
      ><a name="25619"
      > </a
      ><a name="25620" class="Symbol"
      >(</a
      ><a name="25621" href="Stlc.html#2610" class="InductiveConstructor"
      >&#120121;</a
      ><a name="25622"
      > </a
      ><a name="25623" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="25624"
      > </a
      ><a name="25625" href="Stlc.html#25611" class="Bound"
      >A</a
      ><a name="25626"
      > </a
      ><a name="25627" href="Stlc.html#2583" class="InductiveConstructor Operator"
      >&#8658;</a
      ><a name="25628"
      > </a
      ><a name="25629" href="Stlc.html#25613" class="Bound"
      >B</a
      ><a name="25630" class="Symbol"
      >)</a
      ><a name="25631"
      >
</a
      ><a name="25632" href="Stlc.html#25592" class="Function"
      >contradiction</a
      ><a name="25645"
      > </a
      ><a name="25646" class="Symbol"
      >()</a
      ><a name="25648"
      >

</a
      ><a name="25650" href="Stlc.html#25650" class="Function"
      >notyping&#8321;</a
      ><a name="25659"
      > </a
      ><a name="25660" class="Symbol"
      >:</a
      ><a name="25661"
      > </a
      ><a name="25662" class="Symbol"
      >&#8704;</a
      ><a name="25663"
      > </a
      ><a name="25664" class="Symbol"
      >{</a
      ><a name="25665" href="Stlc.html#25665" class="Bound"
      >A</a
      ><a name="25666" class="Symbol"
      >}</a
      ><a name="25667"
      > </a
      ><a name="25668" class="Symbol"
      >&#8594;</a
      ><a name="25669"
      > </a
      ><a name="25670" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#414" class="Function Operator"
      >&#172;</a
      ><a name="25671"
      > </a
      ><a name="25672" class="Symbol"
      >(</a
      ><a name="25673" href="Maps.html#10265" class="Function"
      >&#8709;</a
      ><a name="25674"
      > </a
      ><a name="25675" href="Stlc.html#21756" class="Datatype Operator"
      >&#8866;</a
      ><a name="25676"
      > </a
      ><a name="25677" href="Stlc.html#3672" class="InductiveConstructor Operator"
      >&#955;[</a
      ><a name="25679"
      > </a
      ><a name="25680" href="Stlc.html#5679" class="Function"
      >x</a
      ><a name="25681"
      > </a
      ><a name="25682" href="Stlc.html#3672" class="InductiveConstructor Operator"
      >&#8758;</a
      ><a name="25683"
      > </a
      ><a name="25684" href="Stlc.html#2610" class="InductiveConstructor"
      >&#120121;</a
      ><a name="25685"
      > </a
      ><a name="25686" href="Stlc.html#3672" class="InductiveConstructor Operator"
      >]</a
      ><a name="25687"
      > </a
      ><a name="25688" href="Stlc.html#3672" class="InductiveConstructor Operator"
      >&#955;[</a
      ><a name="25690"
      > </a
      ><a name="25691" href="Stlc.html#5681" class="Function"
      >y</a
      ><a name="25692"
      > </a
      ><a name="25693" href="Stlc.html#3672" class="InductiveConstructor Operator"
      >&#8758;</a
      ><a name="25694"
      > </a
      ><a name="25695" href="Stlc.html#2610" class="InductiveConstructor"
      >&#120121;</a
      ><a name="25696"
      > </a
      ><a name="25697" href="Stlc.html#3672" class="InductiveConstructor Operator"
      >]</a
      ><a name="25698"
      > </a
      ><a name="25699" href="Stlc.html#3656" class="InductiveConstructor"
      >`</a
      ><a name="25700"
      > </a
      ><a name="25701" href="Stlc.html#5679" class="Function"
      >x</a
      ><a name="25702"
      > </a
      ><a name="25703" href="Stlc.html#3708" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="25704"
      > </a
      ><a name="25705" href="Stlc.html#3656" class="InductiveConstructor"
      >`</a
      ><a name="25706"
      > </a
      ><a name="25707" href="Stlc.html#5681" class="Function"
      >y</a
      ><a name="25708"
      > </a
      ><a name="25709" href="Stlc.html#21756" class="Datatype Operator"
      >&#8758;</a
      ><a name="25710"
      > </a
      ><a name="25711" href="Stlc.html#25665" class="Bound"
      >A</a
      ><a name="25712" class="Symbol"
      >)</a
      ><a name="25713"
      >
</a
      ><a name="25714" href="Stlc.html#25650" class="Function"
      >notyping&#8321;</a
      ><a name="25723"
      > </a
      ><a name="25724" class="Symbol"
      >(</a
      ><a name="25725" href="Stlc.html#21854" class="InductiveConstructor"
      >&#8658;-I</a
      ><a name="25728"
      > </a
      ><a name="25729" class="Symbol"
      >(</a
      ><a name="25730" href="Stlc.html#21854" class="InductiveConstructor"
      >&#8658;-I</a
      ><a name="25733"
      > </a
      ><a name="25734" class="Symbol"
      >(</a
      ><a name="25735" href="Stlc.html#21931" class="InductiveConstructor"
      >&#8658;-E</a
      ><a name="25738"
      > </a
      ><a name="25739" class="Symbol"
      >(</a
      ><a name="25740" href="Stlc.html#21800" class="InductiveConstructor"
      >Ax</a
      ><a name="25742"
      > </a
      ><a name="25743" href="Stlc.html#25743" class="Bound"
      >&#915;x</a
      ><a name="25745" class="Symbol"
      >)</a
      ><a name="25746"
      > </a
      ><a name="25747" class="Symbol"
      >_)))</a
      ><a name="25751"
      > </a
      ><a name="25752" class="Symbol"
      >=</a
      ><a name="25753"
      >  </a
      ><a name="25755" href="Stlc.html#25592" class="Function"
      >contradiction</a
      ><a name="25768"
      > </a
      ><a name="25769" class="Symbol"
      >(</a
      ><a name="25770" href="Maps.html#11919" class="Function"
      >just-injective</a
      ><a name="25784"
      > </a
      ><a name="25785" href="Stlc.html#25743" class="Bound"
      >&#915;x</a
      ><a name="25787" class="Symbol"
      >)</a
      >

</pre>


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



