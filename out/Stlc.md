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

<a name="5678" href="Stlc.html#5678" class="Function"
      >f</a
      ><a name="5679"
      > </a
      ><a name="5680" href="Stlc.html#5680" class="Function"
      >x</a
      ><a name="5681"
      > </a
      ><a name="5682" href="Stlc.html#5682" class="Function"
      >y</a
      ><a name="5683"
      > </a
      ><a name="5684" class="Symbol"
      >:</a
      ><a name="5685"
      > </a
      ><a name="5686" href="Maps.html#2171" class="Datatype"
      >Id</a
      ><a name="5688"
      >
</a
      ><a name="5689" href="Stlc.html#5678" class="Function"
      >f</a
      ><a name="5690"
      >  </a
      ><a name="5692" class="Symbol"
      >=</a
      ><a name="5693"
      >  </a
      ><a name="5695" href="Maps.html#2188" class="InductiveConstructor"
      >id</a
      ><a name="5697"
      > </a
      ><a name="5698" class="Number"
      >0</a
      ><a name="5699"
      >
</a
      ><a name="5700" href="Stlc.html#5680" class="Function"
      >x</a
      ><a name="5701"
      >  </a
      ><a name="5703" class="Symbol"
      >=</a
      ><a name="5704"
      >  </a
      ><a name="5706" href="Maps.html#2188" class="InductiveConstructor"
      >id</a
      ><a name="5708"
      > </a
      ><a name="5709" class="Number"
      >1</a
      ><a name="5710"
      >
</a
      ><a name="5711" href="Stlc.html#5682" class="Function"
      >y</a
      ><a name="5712"
      >  </a
      ><a name="5714" class="Symbol"
      >=</a
      ><a name="5715"
      >  </a
      ><a name="5717" href="Maps.html#2188" class="InductiveConstructor"
      >id</a
      ><a name="5719"
      > </a
      ><a name="5720" class="Number"
      >2</a
      ><a name="5721"
      >

</a
      ><a name="5723" href="Stlc.html#5723" class="Function"
      >not</a
      ><a name="5726"
      > </a
      ><a name="5727" href="Stlc.html#5727" class="Function"
      >two</a
      ><a name="5730"
      > </a
      ><a name="5731" class="Symbol"
      >:</a
      ><a name="5732"
      > </a
      ><a name="5733" href="Stlc.html#3637" class="Datatype"
      >Term</a
      ><a name="5737"
      > 
</a
      ><a name="5739" href="Stlc.html#5723" class="Function"
      >not</a
      ><a name="5742"
      > </a
      ><a name="5743" class="Symbol"
      >=</a
      ><a name="5744"
      >  </a
      ><a name="5746" href="Stlc.html#3672" class="InductiveConstructor Operator"
      >&#955;[</a
      ><a name="5748"
      > </a
      ><a name="5749" href="Stlc.html#5680" class="Function"
      >x</a
      ><a name="5750"
      > </a
      ><a name="5751" href="Stlc.html#3672" class="InductiveConstructor Operator"
      >&#8758;</a
      ><a name="5752"
      > </a
      ><a name="5753" href="Stlc.html#2610" class="InductiveConstructor"
      >&#120121;</a
      ><a name="5754"
      > </a
      ><a name="5755" href="Stlc.html#3672" class="InductiveConstructor Operator"
      >]</a
      ><a name="5756"
      > </a
      ><a name="5757" class="Symbol"
      >(</a
      ><a name="5758" href="Stlc.html#3764" class="InductiveConstructor Operator"
      >if</a
      ><a name="5760"
      > </a
      ><a name="5761" href="Stlc.html#3656" class="InductiveConstructor"
      >`</a
      ><a name="5762"
      > </a
      ><a name="5763" href="Stlc.html#5680" class="Function"
      >x</a
      ><a name="5764"
      > </a
      ><a name="5765" href="Stlc.html#3764" class="InductiveConstructor Operator"
      >then</a
      ><a name="5769"
      > </a
      ><a name="5770" href="Stlc.html#3749" class="InductiveConstructor"
      >false</a
      ><a name="5775"
      > </a
      ><a name="5776" href="Stlc.html#3764" class="InductiveConstructor Operator"
      >else</a
      ><a name="5780"
      > </a
      ><a name="5781" href="Stlc.html#3735" class="InductiveConstructor"
      >true</a
      ><a name="5785" class="Symbol"
      >)</a
      ><a name="5786"
      >
</a
      ><a name="5787" href="Stlc.html#5727" class="Function"
      >two</a
      ><a name="5790"
      > </a
      ><a name="5791" class="Symbol"
      >=</a
      ><a name="5792"
      >  </a
      ><a name="5794" href="Stlc.html#3672" class="InductiveConstructor Operator"
      >&#955;[</a
      ><a name="5796"
      > </a
      ><a name="5797" href="Stlc.html#5678" class="Function"
      >f</a
      ><a name="5798"
      > </a
      ><a name="5799" href="Stlc.html#3672" class="InductiveConstructor Operator"
      >&#8758;</a
      ><a name="5800"
      > </a
      ><a name="5801" href="Stlc.html#2610" class="InductiveConstructor"
      >&#120121;</a
      ><a name="5802"
      > </a
      ><a name="5803" href="Stlc.html#2583" class="InductiveConstructor Operator"
      >&#8658;</a
      ><a name="5804"
      > </a
      ><a name="5805" href="Stlc.html#2610" class="InductiveConstructor"
      >&#120121;</a
      ><a name="5806"
      > </a
      ><a name="5807" href="Stlc.html#3672" class="InductiveConstructor Operator"
      >]</a
      ><a name="5808"
      > </a
      ><a name="5809" href="Stlc.html#3672" class="InductiveConstructor Operator"
      >&#955;[</a
      ><a name="5811"
      > </a
      ><a name="5812" href="Stlc.html#5680" class="Function"
      >x</a
      ><a name="5813"
      > </a
      ><a name="5814" href="Stlc.html#3672" class="InductiveConstructor Operator"
      >&#8758;</a
      ><a name="5815"
      > </a
      ><a name="5816" href="Stlc.html#2610" class="InductiveConstructor"
      >&#120121;</a
      ><a name="5817"
      > </a
      ><a name="5818" href="Stlc.html#3672" class="InductiveConstructor Operator"
      >]</a
      ><a name="5819"
      > </a
      ><a name="5820" href="Stlc.html#3656" class="InductiveConstructor"
      >`</a
      ><a name="5821"
      > </a
      ><a name="5822" href="Stlc.html#5678" class="Function"
      >f</a
      ><a name="5823"
      > </a
      ><a name="5824" href="Stlc.html#3708" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="5825"
      > </a
      ><a name="5826" class="Symbol"
      >(</a
      ><a name="5827" href="Stlc.html#3656" class="InductiveConstructor"
      >`</a
      ><a name="5828"
      > </a
      ><a name="5829" href="Stlc.html#5678" class="Function"
      >f</a
      ><a name="5830"
      > </a
      ><a name="5831" href="Stlc.html#3708" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="5832"
      > </a
      ><a name="5833" href="Stlc.html#3656" class="InductiveConstructor"
      >`</a
      ><a name="5834"
      > </a
      ><a name="5835" href="Stlc.html#5680" class="Function"
      >x</a
      ><a name="5836" class="Symbol"
      >)</a
      >

</pre>


#### Bound and free variables

In an abstraction `λ[ x ∶ A ] N` we call `x` the _bound_ variable
and `N` the _body_ of the abstraction.  One of the most important
aspects of lambda calculus is that names of bound variables are
irrelevant.  Thus the four terms

* `` λ[ f ∶ 𝔹 ⇒ 𝔹 ] λ[ x ∶ 𝔹 ] ` f · (` f · ` x) ``
* `` λ[ g ∶ 𝔹 ⇒ 𝔹 ] λ[ y ∶ 𝔹 ] ` g · (` g · ` y) ``
* `` λ[ fred ∶ 𝔹 ⇒ 𝔹 ] λ[ xander ∶ 𝔹 ] ` fred · (` fred · ` xander) ``
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

* `` λ[ f ∶ 𝔹 ⇒ 𝔹 ] λ[ x ∶ 𝔹 ] ` f · (` f · ` x) `` abbreviates
  `` (λ[ f ∶ 𝔹 ⇒ 𝔹 ] (λ[ x ∶ 𝔹 ] (` f · (` f · ` x)))) `` and not
  `` (λ[ f ∶ 𝔹 ⇒ 𝔹 ] (λ[ x ∶ 𝔹 ] ` f)) · (` f · ` x) ``.

<pre class="Agda">

<a name="8245" href="Stlc.html#8245" class="Function"
      >ex&#8321;</a
      ><a name="8248"
      > </a
      ><a name="8249" class="Symbol"
      >:</a
      ><a name="8250"
      > </a
      ><a name="8251" class="Symbol"
      >(</a
      ><a name="8252" href="Stlc.html#2610" class="InductiveConstructor"
      >&#120121;</a
      ><a name="8253"
      > </a
      ><a name="8254" href="Stlc.html#2583" class="InductiveConstructor Operator"
      >&#8658;</a
      ><a name="8255"
      > </a
      ><a name="8256" href="Stlc.html#2610" class="InductiveConstructor"
      >&#120121;</a
      ><a name="8257" class="Symbol"
      >)</a
      ><a name="8258"
      > </a
      ><a name="8259" href="Stlc.html#2583" class="InductiveConstructor Operator"
      >&#8658;</a
      ><a name="8260"
      > </a
      ><a name="8261" href="Stlc.html#2610" class="InductiveConstructor"
      >&#120121;</a
      ><a name="8262"
      > </a
      ><a name="8263" href="Stlc.html#2583" class="InductiveConstructor Operator"
      >&#8658;</a
      ><a name="8264"
      > </a
      ><a name="8265" href="Stlc.html#2610" class="InductiveConstructor"
      >&#120121;</a
      ><a name="8266"
      > </a
      ><a name="8267" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="8268"
      > </a
      ><a name="8269" class="Symbol"
      >(</a
      ><a name="8270" href="Stlc.html#2610" class="InductiveConstructor"
      >&#120121;</a
      ><a name="8271"
      > </a
      ><a name="8272" href="Stlc.html#2583" class="InductiveConstructor Operator"
      >&#8658;</a
      ><a name="8273"
      > </a
      ><a name="8274" href="Stlc.html#2610" class="InductiveConstructor"
      >&#120121;</a
      ><a name="8275" class="Symbol"
      >)</a
      ><a name="8276"
      > </a
      ><a name="8277" href="Stlc.html#2583" class="InductiveConstructor Operator"
      >&#8658;</a
      ><a name="8278"
      > </a
      ><a name="8279" class="Symbol"
      >(</a
      ><a name="8280" href="Stlc.html#2610" class="InductiveConstructor"
      >&#120121;</a
      ><a name="8281"
      > </a
      ><a name="8282" href="Stlc.html#2583" class="InductiveConstructor Operator"
      >&#8658;</a
      ><a name="8283"
      > </a
      ><a name="8284" href="Stlc.html#2610" class="InductiveConstructor"
      >&#120121;</a
      ><a name="8285" class="Symbol"
      >)</a
      ><a name="8286"
      >
</a
      ><a name="8287" href="Stlc.html#8245" class="Function"
      >ex&#8321;</a
      ><a name="8290"
      > </a
      ><a name="8291" class="Symbol"
      >=</a
      ><a name="8292"
      > </a
      ><a name="8293" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="8297"
      >

</a
      ><a name="8299" href="Stlc.html#8299" class="Function"
      >ex&#8322;</a
      ><a name="8302"
      > </a
      ><a name="8303" class="Symbol"
      >:</a
      ><a name="8304"
      > </a
      ><a name="8305" href="Stlc.html#5727" class="Function"
      >two</a
      ><a name="8308"
      > </a
      ><a name="8309" href="Stlc.html#3708" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="8310"
      > </a
      ><a name="8311" href="Stlc.html#5723" class="Function"
      >not</a
      ><a name="8314"
      > </a
      ><a name="8315" href="Stlc.html#3708" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="8316"
      > </a
      ><a name="8317" href="Stlc.html#3735" class="InductiveConstructor"
      >true</a
      ><a name="8321"
      > </a
      ><a name="8322" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="8323"
      > </a
      ><a name="8324" class="Symbol"
      >(</a
      ><a name="8325" href="Stlc.html#5727" class="Function"
      >two</a
      ><a name="8328"
      > </a
      ><a name="8329" href="Stlc.html#3708" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="8330"
      > </a
      ><a name="8331" href="Stlc.html#5723" class="Function"
      >not</a
      ><a name="8334" class="Symbol"
      >)</a
      ><a name="8335"
      > </a
      ><a name="8336" href="Stlc.html#3708" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="8337"
      > </a
      ><a name="8338" href="Stlc.html#3735" class="InductiveConstructor"
      >true</a
      ><a name="8342"
      >
</a
      ><a name="8343" href="Stlc.html#8299" class="Function"
      >ex&#8322;</a
      ><a name="8346"
      > </a
      ><a name="8347" class="Symbol"
      >=</a
      ><a name="8348"
      > </a
      ><a name="8349" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="8353"
      >

</a
      ><a name="8355" href="Stlc.html#8355" class="Function"
      >ex&#8323;</a
      ><a name="8358"
      > </a
      ><a name="8359" class="Symbol"
      >:</a
      ><a name="8360"
      > </a
      ><a name="8361" href="Stlc.html#3672" class="InductiveConstructor Operator"
      >&#955;[</a
      ><a name="8363"
      > </a
      ><a name="8364" href="Stlc.html#5678" class="Function"
      >f</a
      ><a name="8365"
      > </a
      ><a name="8366" href="Stlc.html#3672" class="InductiveConstructor Operator"
      >&#8758;</a
      ><a name="8367"
      > </a
      ><a name="8368" href="Stlc.html#2610" class="InductiveConstructor"
      >&#120121;</a
      ><a name="8369"
      > </a
      ><a name="8370" href="Stlc.html#2583" class="InductiveConstructor Operator"
      >&#8658;</a
      ><a name="8371"
      > </a
      ><a name="8372" href="Stlc.html#2610" class="InductiveConstructor"
      >&#120121;</a
      ><a name="8373"
      > </a
      ><a name="8374" href="Stlc.html#3672" class="InductiveConstructor Operator"
      >]</a
      ><a name="8375"
      > </a
      ><a name="8376" href="Stlc.html#3672" class="InductiveConstructor Operator"
      >&#955;[</a
      ><a name="8378"
      > </a
      ><a name="8379" href="Stlc.html#5680" class="Function"
      >x</a
      ><a name="8380"
      > </a
      ><a name="8381" href="Stlc.html#3672" class="InductiveConstructor Operator"
      >&#8758;</a
      ><a name="8382"
      > </a
      ><a name="8383" href="Stlc.html#2610" class="InductiveConstructor"
      >&#120121;</a
      ><a name="8384"
      > </a
      ><a name="8385" href="Stlc.html#3672" class="InductiveConstructor Operator"
      >]</a
      ><a name="8386"
      > </a
      ><a name="8387" href="Stlc.html#3656" class="InductiveConstructor"
      >`</a
      ><a name="8388"
      > </a
      ><a name="8389" href="Stlc.html#5678" class="Function"
      >f</a
      ><a name="8390"
      > </a
      ><a name="8391" href="Stlc.html#3708" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="8392"
      > </a
      ><a name="8393" class="Symbol"
      >(</a
      ><a name="8394" href="Stlc.html#3656" class="InductiveConstructor"
      >`</a
      ><a name="8395"
      > </a
      ><a name="8396" href="Stlc.html#5678" class="Function"
      >f</a
      ><a name="8397"
      > </a
      ><a name="8398" href="Stlc.html#3708" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="8399"
      > </a
      ><a name="8400" href="Stlc.html#3656" class="InductiveConstructor"
      >`</a
      ><a name="8401"
      > </a
      ><a name="8402" href="Stlc.html#5680" class="Function"
      >x</a
      ><a name="8403" class="Symbol"
      >)</a
      ><a name="8404"
      >
      </a
      ><a name="8411" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="8412"
      > </a
      ><a name="8413" class="Symbol"
      >(</a
      ><a name="8414" href="Stlc.html#3672" class="InductiveConstructor Operator"
      >&#955;[</a
      ><a name="8416"
      > </a
      ><a name="8417" href="Stlc.html#5678" class="Function"
      >f</a
      ><a name="8418"
      > </a
      ><a name="8419" href="Stlc.html#3672" class="InductiveConstructor Operator"
      >&#8758;</a
      ><a name="8420"
      > </a
      ><a name="8421" href="Stlc.html#2610" class="InductiveConstructor"
      >&#120121;</a
      ><a name="8422"
      > </a
      ><a name="8423" href="Stlc.html#2583" class="InductiveConstructor Operator"
      >&#8658;</a
      ><a name="8424"
      > </a
      ><a name="8425" href="Stlc.html#2610" class="InductiveConstructor"
      >&#120121;</a
      ><a name="8426"
      > </a
      ><a name="8427" href="Stlc.html#3672" class="InductiveConstructor Operator"
      >]</a
      ><a name="8428"
      > </a
      ><a name="8429" class="Symbol"
      >(</a
      ><a name="8430" href="Stlc.html#3672" class="InductiveConstructor Operator"
      >&#955;[</a
      ><a name="8432"
      > </a
      ><a name="8433" href="Stlc.html#5680" class="Function"
      >x</a
      ><a name="8434"
      > </a
      ><a name="8435" href="Stlc.html#3672" class="InductiveConstructor Operator"
      >&#8758;</a
      ><a name="8436"
      > </a
      ><a name="8437" href="Stlc.html#2610" class="InductiveConstructor"
      >&#120121;</a
      ><a name="8438"
      > </a
      ><a name="8439" href="Stlc.html#3672" class="InductiveConstructor Operator"
      >]</a
      ><a name="8440"
      > </a
      ><a name="8441" class="Symbol"
      >(</a
      ><a name="8442" href="Stlc.html#3656" class="InductiveConstructor"
      >`</a
      ><a name="8443"
      > </a
      ><a name="8444" href="Stlc.html#5678" class="Function"
      >f</a
      ><a name="8445"
      > </a
      ><a name="8446" href="Stlc.html#3708" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="8447"
      > </a
      ><a name="8448" class="Symbol"
      >(</a
      ><a name="8449" href="Stlc.html#3656" class="InductiveConstructor"
      >`</a
      ><a name="8450"
      > </a
      ><a name="8451" href="Stlc.html#5678" class="Function"
      >f</a
      ><a name="8452"
      > </a
      ><a name="8453" href="Stlc.html#3708" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="8454"
      > </a
      ><a name="8455" href="Stlc.html#3656" class="InductiveConstructor"
      >`</a
      ><a name="8456"
      > </a
      ><a name="8457" href="Stlc.html#5680" class="Function"
      >x</a
      ><a name="8458" class="Symbol"
      >))))</a
      ><a name="8462"
      >
</a
      ><a name="8463" href="Stlc.html#8355" class="Function"
      >ex&#8323;</a
      ><a name="8466"
      > </a
      ><a name="8467" class="Symbol"
      >=</a
      ><a name="8468"
      > </a
      ><a name="8469" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
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

<a name="9530" class="Keyword"
      >data</a
      ><a name="9534"
      > </a
      ><a name="9535" href="Stlc.html#9535" class="Datatype"
      >Value</a
      ><a name="9540"
      > </a
      ><a name="9541" class="Symbol"
      >:</a
      ><a name="9542"
      > </a
      ><a name="9543" href="Stlc.html#3637" class="Datatype"
      >Term</a
      ><a name="9547"
      > </a
      ><a name="9548" class="Symbol"
      >&#8594;</a
      ><a name="9549"
      > </a
      ><a name="9550" class="PrimitiveType"
      >Set</a
      ><a name="9553"
      > </a
      ><a name="9554" class="Keyword"
      >where</a
      ><a name="9559"
      >
  </a
      ><a name="9562" href="Stlc.html#9562" class="InductiveConstructor"
      >value-&#955;</a
      ><a name="9569"
      >     </a
      ><a name="9574" class="Symbol"
      >:</a
      ><a name="9575"
      > </a
      ><a name="9576" class="Symbol"
      >&#8704;</a
      ><a name="9577"
      > </a
      ><a name="9578" class="Symbol"
      >{</a
      ><a name="9579" href="Stlc.html#9579" class="Bound"
      >x</a
      ><a name="9580"
      > </a
      ><a name="9581" href="Stlc.html#9581" class="Bound"
      >A</a
      ><a name="9582"
      > </a
      ><a name="9583" href="Stlc.html#9583" class="Bound"
      >N</a
      ><a name="9584" class="Symbol"
      >}</a
      ><a name="9585"
      > </a
      ><a name="9586" class="Symbol"
      >&#8594;</a
      ><a name="9587"
      > </a
      ><a name="9588" href="Stlc.html#9535" class="Datatype"
      >Value</a
      ><a name="9593"
      > </a
      ><a name="9594" class="Symbol"
      >(</a
      ><a name="9595" href="Stlc.html#3672" class="InductiveConstructor Operator"
      >&#955;[</a
      ><a name="9597"
      > </a
      ><a name="9598" href="Stlc.html#9579" class="Bound"
      >x</a
      ><a name="9599"
      > </a
      ><a name="9600" href="Stlc.html#3672" class="InductiveConstructor Operator"
      >&#8758;</a
      ><a name="9601"
      > </a
      ><a name="9602" href="Stlc.html#9581" class="Bound"
      >A</a
      ><a name="9603"
      > </a
      ><a name="9604" href="Stlc.html#3672" class="InductiveConstructor Operator"
      >]</a
      ><a name="9605"
      > </a
      ><a name="9606" href="Stlc.html#9583" class="Bound"
      >N</a
      ><a name="9607" class="Symbol"
      >)</a
      ><a name="9608"
      >
  </a
      ><a name="9611" href="Stlc.html#9611" class="InductiveConstructor"
      >value-true</a
      ><a name="9621"
      >  </a
      ><a name="9623" class="Symbol"
      >:</a
      ><a name="9624"
      > </a
      ><a name="9625" href="Stlc.html#9535" class="Datatype"
      >Value</a
      ><a name="9630"
      > </a
      ><a name="9631" href="Stlc.html#3735" class="InductiveConstructor"
      >true</a
      ><a name="9635"
      >
  </a
      ><a name="9638" href="Stlc.html#9638" class="InductiveConstructor"
      >value-false</a
      ><a name="9649"
      > </a
      ><a name="9650" class="Symbol"
      >:</a
      ><a name="9651"
      > </a
      ><a name="9652" href="Stlc.html#9535" class="Datatype"
      >Value</a
      ><a name="9657"
      > </a
      ><a name="9658" href="Stlc.html#3749" class="InductiveConstructor"
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

<a name="12079" href="Stlc.html#12079" class="Function Operator"
      >_[_:=_]</a
      ><a name="12086"
      > </a
      ><a name="12087" class="Symbol"
      >:</a
      ><a name="12088"
      > </a
      ><a name="12089" href="Stlc.html#3637" class="Datatype"
      >Term</a
      ><a name="12093"
      > </a
      ><a name="12094" class="Symbol"
      >&#8594;</a
      ><a name="12095"
      > </a
      ><a name="12096" href="Maps.html#2171" class="Datatype"
      >Id</a
      ><a name="12098"
      > </a
      ><a name="12099" class="Symbol"
      >&#8594;</a
      ><a name="12100"
      > </a
      ><a name="12101" href="Stlc.html#3637" class="Datatype"
      >Term</a
      ><a name="12105"
      > </a
      ><a name="12106" class="Symbol"
      >&#8594;</a
      ><a name="12107"
      > </a
      ><a name="12108" href="Stlc.html#3637" class="Datatype"
      >Term</a
      ><a name="12112"
      >
</a
      ><a name="12113" class="Symbol"
      >(</a
      ><a name="12114" href="Stlc.html#3656" class="InductiveConstructor"
      >`</a
      ><a name="12115"
      > </a
      ><a name="12116" href="Stlc.html#12116" class="Bound"
      >x&#8242;</a
      ><a name="12118" class="Symbol"
      >)</a
      ><a name="12119"
      > </a
      ><a name="12120" href="Stlc.html#12079" class="Function Operator"
      >[</a
      ><a name="12121"
      > </a
      ><a name="12122" href="Stlc.html#12122" class="Bound"
      >x</a
      ><a name="12123"
      > </a
      ><a name="12124" href="Stlc.html#12079" class="Function Operator"
      >:=</a
      ><a name="12126"
      > </a
      ><a name="12127" href="Stlc.html#12127" class="Bound"
      >V</a
      ><a name="12128"
      > </a
      ><a name="12129" href="Stlc.html#12079" class="Function Operator"
      >]</a
      ><a name="12130"
      > </a
      ><a name="12131" class="Keyword"
      >with</a
      ><a name="12135"
      > </a
      ><a name="12136" href="Stlc.html#12122" class="Bound"
      >x</a
      ><a name="12137"
      > </a
      ><a name="12138" href="Maps.html#2509" class="Function Operator"
      >&#8799;</a
      ><a name="12139"
      > </a
      ><a name="12140" href="Stlc.html#12116" class="Bound"
      >x&#8242;</a
      ><a name="12142"
      >
</a
      ><a name="12143" class="Symbol"
      >...</a
      ><a name="12146"
      > </a
      ><a name="12147" class="Symbol"
      >|</a
      ><a name="12148"
      > </a
      ><a name="12149" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#520" class="InductiveConstructor"
      >yes</a
      ><a name="12152"
      > </a
      ><a name="12153" class="Symbol"
      >_</a
      ><a name="12154"
      > </a
      ><a name="12155" class="Symbol"
      >=</a
      ><a name="12156"
      > </a
      ><a name="12157" href="Stlc.html#12127" class="Bound"
      >V</a
      ><a name="12158"
      >
</a
      ><a name="12159" class="Symbol"
      >...</a
      ><a name="12162"
      > </a
      ><a name="12163" class="Symbol"
      >|</a
      ><a name="12164"
      > </a
      ><a name="12165" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#547" class="InductiveConstructor"
      >no</a
      ><a name="12167"
      >  </a
      ><a name="12169" class="Symbol"
      >_</a
      ><a name="12170"
      > </a
      ><a name="12171" class="Symbol"
      >=</a
      ><a name="12172"
      > </a
      ><a name="12173" href="Stlc.html#3656" class="InductiveConstructor"
      >`</a
      ><a name="12174"
      > </a
      ><a name="12175" href="Stlc.html#12116" class="Bound"
      >x&#8242;</a
      ><a name="12177"
      >
</a
      ><a name="12178" class="Symbol"
      >(</a
      ><a name="12179" href="Stlc.html#3672" class="InductiveConstructor Operator"
      >&#955;[</a
      ><a name="12181"
      > </a
      ><a name="12182" href="Stlc.html#12182" class="Bound"
      >x&#8242;</a
      ><a name="12184"
      > </a
      ><a name="12185" href="Stlc.html#3672" class="InductiveConstructor Operator"
      >&#8758;</a
      ><a name="12186"
      > </a
      ><a name="12187" href="Stlc.html#12187" class="Bound"
      >A&#8242;</a
      ><a name="12189"
      > </a
      ><a name="12190" href="Stlc.html#3672" class="InductiveConstructor Operator"
      >]</a
      ><a name="12191"
      > </a
      ><a name="12192" href="Stlc.html#12192" class="Bound"
      >N&#8242;</a
      ><a name="12194" class="Symbol"
      >)</a
      ><a name="12195"
      > </a
      ><a name="12196" href="Stlc.html#12079" class="Function Operator"
      >[</a
      ><a name="12197"
      > </a
      ><a name="12198" href="Stlc.html#12198" class="Bound"
      >x</a
      ><a name="12199"
      > </a
      ><a name="12200" href="Stlc.html#12079" class="Function Operator"
      >:=</a
      ><a name="12202"
      > </a
      ><a name="12203" href="Stlc.html#12203" class="Bound"
      >V</a
      ><a name="12204"
      > </a
      ><a name="12205" href="Stlc.html#12079" class="Function Operator"
      >]</a
      ><a name="12206"
      > </a
      ><a name="12207" class="Keyword"
      >with</a
      ><a name="12211"
      > </a
      ><a name="12212" href="Stlc.html#12198" class="Bound"
      >x</a
      ><a name="12213"
      > </a
      ><a name="12214" href="Maps.html#2509" class="Function Operator"
      >&#8799;</a
      ><a name="12215"
      > </a
      ><a name="12216" href="Stlc.html#12182" class="Bound"
      >x&#8242;</a
      ><a name="12218"
      >
</a
      ><a name="12219" class="Symbol"
      >...</a
      ><a name="12222"
      > </a
      ><a name="12223" class="Symbol"
      >|</a
      ><a name="12224"
      > </a
      ><a name="12225" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#520" class="InductiveConstructor"
      >yes</a
      ><a name="12228"
      > </a
      ><a name="12229" class="Symbol"
      >_</a
      ><a name="12230"
      > </a
      ><a name="12231" class="Symbol"
      >=</a
      ><a name="12232"
      > </a
      ><a name="12233" href="Stlc.html#3672" class="InductiveConstructor Operator"
      >&#955;[</a
      ><a name="12235"
      > </a
      ><a name="12236" href="Stlc.html#12182" class="Bound"
      >x&#8242;</a
      ><a name="12238"
      > </a
      ><a name="12239" href="Stlc.html#3672" class="InductiveConstructor Operator"
      >&#8758;</a
      ><a name="12240"
      > </a
      ><a name="12241" href="Stlc.html#12187" class="Bound"
      >A&#8242;</a
      ><a name="12243"
      > </a
      ><a name="12244" href="Stlc.html#3672" class="InductiveConstructor Operator"
      >]</a
      ><a name="12245"
      > </a
      ><a name="12246" href="Stlc.html#12192" class="Bound"
      >N&#8242;</a
      ><a name="12248"
      >
</a
      ><a name="12249" class="Symbol"
      >...</a
      ><a name="12252"
      > </a
      ><a name="12253" class="Symbol"
      >|</a
      ><a name="12254"
      > </a
      ><a name="12255" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#547" class="InductiveConstructor"
      >no</a
      ><a name="12257"
      >  </a
      ><a name="12259" class="Symbol"
      >_</a
      ><a name="12260"
      > </a
      ><a name="12261" class="Symbol"
      >=</a
      ><a name="12262"
      > </a
      ><a name="12263" href="Stlc.html#3672" class="InductiveConstructor Operator"
      >&#955;[</a
      ><a name="12265"
      > </a
      ><a name="12266" href="Stlc.html#12182" class="Bound"
      >x&#8242;</a
      ><a name="12268"
      > </a
      ><a name="12269" href="Stlc.html#3672" class="InductiveConstructor Operator"
      >&#8758;</a
      ><a name="12270"
      > </a
      ><a name="12271" href="Stlc.html#12187" class="Bound"
      >A&#8242;</a
      ><a name="12273"
      > </a
      ><a name="12274" href="Stlc.html#3672" class="InductiveConstructor Operator"
      >]</a
      ><a name="12275"
      > </a
      ><a name="12276" class="Symbol"
      >(</a
      ><a name="12277" href="Stlc.html#12192" class="Bound"
      >N&#8242;</a
      ><a name="12279"
      > </a
      ><a name="12280" href="Stlc.html#12079" class="Function Operator"
      >[</a
      ><a name="12281"
      > </a
      ><a name="12282" href="Stlc.html#12198" class="Bound"
      >x</a
      ><a name="12283"
      > </a
      ><a name="12284" href="Stlc.html#12079" class="Function Operator"
      >:=</a
      ><a name="12286"
      > </a
      ><a name="12287" href="Stlc.html#12203" class="Bound"
      >V</a
      ><a name="12288"
      > </a
      ><a name="12289" href="Stlc.html#12079" class="Function Operator"
      >]</a
      ><a name="12290" class="Symbol"
      >)</a
      ><a name="12291"
      >
</a
      ><a name="12292" class="Symbol"
      >(</a
      ><a name="12293" href="Stlc.html#12293" class="Bound"
      >L&#8242;</a
      ><a name="12295"
      > </a
      ><a name="12296" href="Stlc.html#3708" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="12297"
      > </a
      ><a name="12298" href="Stlc.html#12298" class="Bound"
      >M&#8242;</a
      ><a name="12300" class="Symbol"
      >)</a
      ><a name="12301"
      > </a
      ><a name="12302" href="Stlc.html#12079" class="Function Operator"
      >[</a
      ><a name="12303"
      > </a
      ><a name="12304" href="Stlc.html#12304" class="Bound"
      >x</a
      ><a name="12305"
      > </a
      ><a name="12306" href="Stlc.html#12079" class="Function Operator"
      >:=</a
      ><a name="12308"
      > </a
      ><a name="12309" href="Stlc.html#12309" class="Bound"
      >V</a
      ><a name="12310"
      > </a
      ><a name="12311" href="Stlc.html#12079" class="Function Operator"
      >]</a
      ><a name="12312"
      > </a
      ><a name="12313" class="Symbol"
      >=</a
      ><a name="12314"
      >  </a
      ><a name="12316" class="Symbol"
      >(</a
      ><a name="12317" href="Stlc.html#12293" class="Bound"
      >L&#8242;</a
      ><a name="12319"
      > </a
      ><a name="12320" href="Stlc.html#12079" class="Function Operator"
      >[</a
      ><a name="12321"
      > </a
      ><a name="12322" href="Stlc.html#12304" class="Bound"
      >x</a
      ><a name="12323"
      > </a
      ><a name="12324" href="Stlc.html#12079" class="Function Operator"
      >:=</a
      ><a name="12326"
      > </a
      ><a name="12327" href="Stlc.html#12309" class="Bound"
      >V</a
      ><a name="12328"
      > </a
      ><a name="12329" href="Stlc.html#12079" class="Function Operator"
      >]</a
      ><a name="12330" class="Symbol"
      >)</a
      ><a name="12331"
      > </a
      ><a name="12332" href="Stlc.html#3708" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="12333"
      > </a
      ><a name="12334" class="Symbol"
      >(</a
      ><a name="12335" href="Stlc.html#12298" class="Bound"
      >M&#8242;</a
      ><a name="12337"
      > </a
      ><a name="12338" href="Stlc.html#12079" class="Function Operator"
      >[</a
      ><a name="12339"
      > </a
      ><a name="12340" href="Stlc.html#12304" class="Bound"
      >x</a
      ><a name="12341"
      > </a
      ><a name="12342" href="Stlc.html#12079" class="Function Operator"
      >:=</a
      ><a name="12344"
      > </a
      ><a name="12345" href="Stlc.html#12309" class="Bound"
      >V</a
      ><a name="12346"
      > </a
      ><a name="12347" href="Stlc.html#12079" class="Function Operator"
      >]</a
      ><a name="12348" class="Symbol"
      >)</a
      ><a name="12349"
      >
</a
      ><a name="12350" class="Symbol"
      >(</a
      ><a name="12351" href="Stlc.html#3735" class="InductiveConstructor"
      >true</a
      ><a name="12355" class="Symbol"
      >)</a
      ><a name="12356"
      > </a
      ><a name="12357" href="Stlc.html#12079" class="Function Operator"
      >[</a
      ><a name="12358"
      > </a
      ><a name="12359" href="Stlc.html#12359" class="Bound"
      >x</a
      ><a name="12360"
      > </a
      ><a name="12361" href="Stlc.html#12079" class="Function Operator"
      >:=</a
      ><a name="12363"
      > </a
      ><a name="12364" href="Stlc.html#12364" class="Bound"
      >V</a
      ><a name="12365"
      > </a
      ><a name="12366" href="Stlc.html#12079" class="Function Operator"
      >]</a
      ><a name="12367"
      > </a
      ><a name="12368" class="Symbol"
      >=</a
      ><a name="12369"
      > </a
      ><a name="12370" href="Stlc.html#3735" class="InductiveConstructor"
      >true</a
      ><a name="12374"
      >
</a
      ><a name="12375" class="Symbol"
      >(</a
      ><a name="12376" href="Stlc.html#3749" class="InductiveConstructor"
      >false</a
      ><a name="12381" class="Symbol"
      >)</a
      ><a name="12382"
      > </a
      ><a name="12383" href="Stlc.html#12079" class="Function Operator"
      >[</a
      ><a name="12384"
      > </a
      ><a name="12385" href="Stlc.html#12385" class="Bound"
      >x</a
      ><a name="12386"
      > </a
      ><a name="12387" href="Stlc.html#12079" class="Function Operator"
      >:=</a
      ><a name="12389"
      > </a
      ><a name="12390" href="Stlc.html#12390" class="Bound"
      >V</a
      ><a name="12391"
      > </a
      ><a name="12392" href="Stlc.html#12079" class="Function Operator"
      >]</a
      ><a name="12393"
      > </a
      ><a name="12394" class="Symbol"
      >=</a
      ><a name="12395"
      > </a
      ><a name="12396" href="Stlc.html#3749" class="InductiveConstructor"
      >false</a
      ><a name="12401"
      >
</a
      ><a name="12402" class="Symbol"
      >(</a
      ><a name="12403" href="Stlc.html#3764" class="InductiveConstructor Operator"
      >if</a
      ><a name="12405"
      > </a
      ><a name="12406" href="Stlc.html#12406" class="Bound"
      >L&#8242;</a
      ><a name="12408"
      > </a
      ><a name="12409" href="Stlc.html#3764" class="InductiveConstructor Operator"
      >then</a
      ><a name="12413"
      > </a
      ><a name="12414" href="Stlc.html#12414" class="Bound"
      >M&#8242;</a
      ><a name="12416"
      > </a
      ><a name="12417" href="Stlc.html#3764" class="InductiveConstructor Operator"
      >else</a
      ><a name="12421"
      > </a
      ><a name="12422" href="Stlc.html#12422" class="Bound"
      >N&#8242;</a
      ><a name="12424" class="Symbol"
      >)</a
      ><a name="12425"
      > </a
      ><a name="12426" href="Stlc.html#12079" class="Function Operator"
      >[</a
      ><a name="12427"
      > </a
      ><a name="12428" href="Stlc.html#12428" class="Bound"
      >x</a
      ><a name="12429"
      > </a
      ><a name="12430" href="Stlc.html#12079" class="Function Operator"
      >:=</a
      ><a name="12432"
      > </a
      ><a name="12433" href="Stlc.html#12433" class="Bound"
      >V</a
      ><a name="12434"
      > </a
      ><a name="12435" href="Stlc.html#12079" class="Function Operator"
      >]</a
      ><a name="12436"
      > </a
      ><a name="12437" class="Symbol"
      >=</a
      ><a name="12438"
      >
  </a
      ><a name="12441" href="Stlc.html#3764" class="InductiveConstructor Operator"
      >if</a
      ><a name="12443"
      > </a
      ><a name="12444" class="Symbol"
      >(</a
      ><a name="12445" href="Stlc.html#12406" class="Bound"
      >L&#8242;</a
      ><a name="12447"
      > </a
      ><a name="12448" href="Stlc.html#12079" class="Function Operator"
      >[</a
      ><a name="12449"
      > </a
      ><a name="12450" href="Stlc.html#12428" class="Bound"
      >x</a
      ><a name="12451"
      > </a
      ><a name="12452" href="Stlc.html#12079" class="Function Operator"
      >:=</a
      ><a name="12454"
      > </a
      ><a name="12455" href="Stlc.html#12433" class="Bound"
      >V</a
      ><a name="12456"
      > </a
      ><a name="12457" href="Stlc.html#12079" class="Function Operator"
      >]</a
      ><a name="12458" class="Symbol"
      >)</a
      ><a name="12459"
      > </a
      ><a name="12460" href="Stlc.html#3764" class="InductiveConstructor Operator"
      >then</a
      ><a name="12464"
      > </a
      ><a name="12465" class="Symbol"
      >(</a
      ><a name="12466" href="Stlc.html#12414" class="Bound"
      >M&#8242;</a
      ><a name="12468"
      > </a
      ><a name="12469" href="Stlc.html#12079" class="Function Operator"
      >[</a
      ><a name="12470"
      > </a
      ><a name="12471" href="Stlc.html#12428" class="Bound"
      >x</a
      ><a name="12472"
      > </a
      ><a name="12473" href="Stlc.html#12079" class="Function Operator"
      >:=</a
      ><a name="12475"
      > </a
      ><a name="12476" href="Stlc.html#12433" class="Bound"
      >V</a
      ><a name="12477"
      > </a
      ><a name="12478" href="Stlc.html#12079" class="Function Operator"
      >]</a
      ><a name="12479" class="Symbol"
      >)</a
      ><a name="12480"
      > </a
      ><a name="12481" href="Stlc.html#3764" class="InductiveConstructor Operator"
      >else</a
      ><a name="12485"
      > </a
      ><a name="12486" class="Symbol"
      >(</a
      ><a name="12487" href="Stlc.html#12422" class="Bound"
      >N&#8242;</a
      ><a name="12489"
      > </a
      ><a name="12490" href="Stlc.html#12079" class="Function Operator"
      >[</a
      ><a name="12491"
      > </a
      ><a name="12492" href="Stlc.html#12428" class="Bound"
      >x</a
      ><a name="12493"
      > </a
      ><a name="12494" href="Stlc.html#12079" class="Function Operator"
      >:=</a
      ><a name="12496"
      > </a
      ><a name="12497" href="Stlc.html#12433" class="Bound"
      >V</a
      ><a name="12498"
      > </a
      ><a name="12499" href="Stlc.html#12079" class="Function Operator"
      >]</a
      ><a name="12500" class="Symbol"
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

<a name="13250" href="Stlc.html#13250" class="Function"
      >ex&#8321;&#8321;</a
      ><a name="13254"
      > </a
      ><a name="13255" class="Symbol"
      >:</a
      ><a name="13256"
      > </a
      ><a name="13257" href="Stlc.html#3656" class="InductiveConstructor"
      >`</a
      ><a name="13258"
      > </a
      ><a name="13259" href="Stlc.html#5678" class="Function"
      >f</a
      ><a name="13260"
      > </a
      ><a name="13261" href="Stlc.html#12079" class="Function Operator"
      >[</a
      ><a name="13262"
      > </a
      ><a name="13263" href="Stlc.html#5678" class="Function"
      >f</a
      ><a name="13264"
      > </a
      ><a name="13265" href="Stlc.html#12079" class="Function Operator"
      >:=</a
      ><a name="13267"
      > </a
      ><a name="13268" href="Stlc.html#5723" class="Function"
      >not</a
      ><a name="13271"
      > </a
      ><a name="13272" href="Stlc.html#12079" class="Function Operator"
      >]</a
      ><a name="13273"
      > </a
      ><a name="13274" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="13275"
      >  </a
      ><a name="13277" href="Stlc.html#5723" class="Function"
      >not</a
      ><a name="13280"
      >
</a
      ><a name="13281" href="Stlc.html#13250" class="Function"
      >ex&#8321;&#8321;</a
      ><a name="13285"
      > </a
      ><a name="13286" class="Symbol"
      >=</a
      ><a name="13287"
      > </a
      ><a name="13288" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="13292"
      >

</a
      ><a name="13294" href="Stlc.html#13294" class="Function"
      >ex&#8321;&#8322;</a
      ><a name="13298"
      > </a
      ><a name="13299" class="Symbol"
      >:</a
      ><a name="13300"
      > </a
      ><a name="13301" href="Stlc.html#3735" class="InductiveConstructor"
      >true</a
      ><a name="13305"
      > </a
      ><a name="13306" href="Stlc.html#12079" class="Function Operator"
      >[</a
      ><a name="13307"
      > </a
      ><a name="13308" href="Stlc.html#5678" class="Function"
      >f</a
      ><a name="13309"
      > </a
      ><a name="13310" href="Stlc.html#12079" class="Function Operator"
      >:=</a
      ><a name="13312"
      > </a
      ><a name="13313" href="Stlc.html#5723" class="Function"
      >not</a
      ><a name="13316"
      > </a
      ><a name="13317" href="Stlc.html#12079" class="Function Operator"
      >]</a
      ><a name="13318"
      > </a
      ><a name="13319" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="13320"
      > </a
      ><a name="13321" href="Stlc.html#3735" class="InductiveConstructor"
      >true</a
      ><a name="13325"
      >
</a
      ><a name="13326" href="Stlc.html#13294" class="Function"
      >ex&#8321;&#8322;</a
      ><a name="13330"
      > </a
      ><a name="13331" class="Symbol"
      >=</a
      ><a name="13332"
      > </a
      ><a name="13333" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="13337"
      >

</a
      ><a name="13339" href="Stlc.html#13339" class="Function"
      >ex&#8321;&#8323;</a
      ><a name="13343"
      > </a
      ><a name="13344" class="Symbol"
      >:</a
      ><a name="13345"
      > </a
      ><a name="13346" class="Symbol"
      >(</a
      ><a name="13347" href="Stlc.html#3656" class="InductiveConstructor"
      >`</a
      ><a name="13348"
      > </a
      ><a name="13349" href="Stlc.html#5678" class="Function"
      >f</a
      ><a name="13350"
      > </a
      ><a name="13351" href="Stlc.html#3708" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="13352"
      > </a
      ><a name="13353" href="Stlc.html#3735" class="InductiveConstructor"
      >true</a
      ><a name="13357" class="Symbol"
      >)</a
      ><a name="13358"
      > </a
      ><a name="13359" href="Stlc.html#12079" class="Function Operator"
      >[</a
      ><a name="13360"
      > </a
      ><a name="13361" href="Stlc.html#5678" class="Function"
      >f</a
      ><a name="13362"
      > </a
      ><a name="13363" href="Stlc.html#12079" class="Function Operator"
      >:=</a
      ><a name="13365"
      > </a
      ><a name="13366" href="Stlc.html#5723" class="Function"
      >not</a
      ><a name="13369"
      > </a
      ><a name="13370" href="Stlc.html#12079" class="Function Operator"
      >]</a
      ><a name="13371"
      > </a
      ><a name="13372" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="13373"
      > </a
      ><a name="13374" href="Stlc.html#5723" class="Function"
      >not</a
      ><a name="13377"
      > </a
      ><a name="13378" href="Stlc.html#3708" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="13379"
      > </a
      ><a name="13380" href="Stlc.html#3735" class="InductiveConstructor"
      >true</a
      ><a name="13384"
      >
</a
      ><a name="13385" href="Stlc.html#13339" class="Function"
      >ex&#8321;&#8323;</a
      ><a name="13389"
      > </a
      ><a name="13390" class="Symbol"
      >=</a
      ><a name="13391"
      > </a
      ><a name="13392" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="13396"
      >

</a
      ><a name="13398" href="Stlc.html#13398" class="Function"
      >ex&#8321;&#8324;</a
      ><a name="13402"
      > </a
      ><a name="13403" class="Symbol"
      >:</a
      ><a name="13404"
      > </a
      ><a name="13405" class="Symbol"
      >(</a
      ><a name="13406" href="Stlc.html#3656" class="InductiveConstructor"
      >`</a
      ><a name="13407"
      > </a
      ><a name="13408" href="Stlc.html#5678" class="Function"
      >f</a
      ><a name="13409"
      > </a
      ><a name="13410" href="Stlc.html#3708" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="13411"
      > </a
      ><a name="13412" class="Symbol"
      >(</a
      ><a name="13413" href="Stlc.html#3656" class="InductiveConstructor"
      >`</a
      ><a name="13414"
      > </a
      ><a name="13415" href="Stlc.html#5678" class="Function"
      >f</a
      ><a name="13416"
      > </a
      ><a name="13417" href="Stlc.html#3708" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="13418"
      > </a
      ><a name="13419" href="Stlc.html#3735" class="InductiveConstructor"
      >true</a
      ><a name="13423" class="Symbol"
      >))</a
      ><a name="13425"
      > </a
      ><a name="13426" href="Stlc.html#12079" class="Function Operator"
      >[</a
      ><a name="13427"
      > </a
      ><a name="13428" href="Stlc.html#5678" class="Function"
      >f</a
      ><a name="13429"
      > </a
      ><a name="13430" href="Stlc.html#12079" class="Function Operator"
      >:=</a
      ><a name="13432"
      > </a
      ><a name="13433" href="Stlc.html#5723" class="Function"
      >not</a
      ><a name="13436"
      > </a
      ><a name="13437" href="Stlc.html#12079" class="Function Operator"
      >]</a
      ><a name="13438"
      > </a
      ><a name="13439" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="13440"
      > </a
      ><a name="13441" href="Stlc.html#5723" class="Function"
      >not</a
      ><a name="13444"
      > </a
      ><a name="13445" href="Stlc.html#3708" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="13446"
      > </a
      ><a name="13447" class="Symbol"
      >(</a
      ><a name="13448" href="Stlc.html#5723" class="Function"
      >not</a
      ><a name="13451"
      > </a
      ><a name="13452" href="Stlc.html#3708" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="13453"
      > </a
      ><a name="13454" href="Stlc.html#3735" class="InductiveConstructor"
      >true</a
      ><a name="13458" class="Symbol"
      >)</a
      ><a name="13459"
      >
</a
      ><a name="13460" href="Stlc.html#13398" class="Function"
      >ex&#8321;&#8324;</a
      ><a name="13464"
      > </a
      ><a name="13465" class="Symbol"
      >=</a
      ><a name="13466"
      > </a
      ><a name="13467" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="13471"
      >

</a
      ><a name="13473" href="Stlc.html#13473" class="Function"
      >ex&#8321;&#8325;</a
      ><a name="13477"
      > </a
      ><a name="13478" class="Symbol"
      >:</a
      ><a name="13479"
      > </a
      ><a name="13480" class="Symbol"
      >(</a
      ><a name="13481" href="Stlc.html#3672" class="InductiveConstructor Operator"
      >&#955;[</a
      ><a name="13483"
      > </a
      ><a name="13484" href="Stlc.html#5680" class="Function"
      >x</a
      ><a name="13485"
      > </a
      ><a name="13486" href="Stlc.html#3672" class="InductiveConstructor Operator"
      >&#8758;</a
      ><a name="13487"
      > </a
      ><a name="13488" href="Stlc.html#2610" class="InductiveConstructor"
      >&#120121;</a
      ><a name="13489"
      > </a
      ><a name="13490" href="Stlc.html#3672" class="InductiveConstructor Operator"
      >]</a
      ><a name="13491"
      > </a
      ><a name="13492" href="Stlc.html#3656" class="InductiveConstructor"
      >`</a
      ><a name="13493"
      > </a
      ><a name="13494" href="Stlc.html#5678" class="Function"
      >f</a
      ><a name="13495"
      > </a
      ><a name="13496" href="Stlc.html#3708" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="13497"
      > </a
      ><a name="13498" class="Symbol"
      >(</a
      ><a name="13499" href="Stlc.html#3656" class="InductiveConstructor"
      >`</a
      ><a name="13500"
      > </a
      ><a name="13501" href="Stlc.html#5678" class="Function"
      >f</a
      ><a name="13502"
      > </a
      ><a name="13503" href="Stlc.html#3708" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="13504"
      > </a
      ><a name="13505" href="Stlc.html#3656" class="InductiveConstructor"
      >`</a
      ><a name="13506"
      > </a
      ><a name="13507" href="Stlc.html#5680" class="Function"
      >x</a
      ><a name="13508" class="Symbol"
      >))</a
      ><a name="13510"
      > </a
      ><a name="13511" href="Stlc.html#12079" class="Function Operator"
      >[</a
      ><a name="13512"
      > </a
      ><a name="13513" href="Stlc.html#5678" class="Function"
      >f</a
      ><a name="13514"
      > </a
      ><a name="13515" href="Stlc.html#12079" class="Function Operator"
      >:=</a
      ><a name="13517"
      > </a
      ><a name="13518" href="Stlc.html#5723" class="Function"
      >not</a
      ><a name="13521"
      > </a
      ><a name="13522" href="Stlc.html#12079" class="Function Operator"
      >]</a
      ><a name="13523"
      > </a
      ><a name="13524" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="13525"
      > </a
      ><a name="13526" href="Stlc.html#3672" class="InductiveConstructor Operator"
      >&#955;[</a
      ><a name="13528"
      > </a
      ><a name="13529" href="Stlc.html#5680" class="Function"
      >x</a
      ><a name="13530"
      > </a
      ><a name="13531" href="Stlc.html#3672" class="InductiveConstructor Operator"
      >&#8758;</a
      ><a name="13532"
      > </a
      ><a name="13533" href="Stlc.html#2610" class="InductiveConstructor"
      >&#120121;</a
      ><a name="13534"
      > </a
      ><a name="13535" href="Stlc.html#3672" class="InductiveConstructor Operator"
      >]</a
      ><a name="13536"
      > </a
      ><a name="13537" href="Stlc.html#5723" class="Function"
      >not</a
      ><a name="13540"
      > </a
      ><a name="13541" href="Stlc.html#3708" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="13542"
      > </a
      ><a name="13543" class="Symbol"
      >(</a
      ><a name="13544" href="Stlc.html#5723" class="Function"
      >not</a
      ><a name="13547"
      > </a
      ><a name="13548" href="Stlc.html#3708" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="13549"
      > </a
      ><a name="13550" href="Stlc.html#3656" class="InductiveConstructor"
      >`</a
      ><a name="13551"
      > </a
      ><a name="13552" href="Stlc.html#5680" class="Function"
      >x</a
      ><a name="13553" class="Symbol"
      >)</a
      ><a name="13554"
      >
</a
      ><a name="13555" href="Stlc.html#13473" class="Function"
      >ex&#8321;&#8325;</a
      ><a name="13559"
      > </a
      ><a name="13560" class="Symbol"
      >=</a
      ><a name="13561"
      > </a
      ><a name="13562" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="13566"
      >

</a
      ><a name="13568" href="Stlc.html#13568" class="Function"
      >ex&#8321;&#8326;</a
      ><a name="13572"
      > </a
      ><a name="13573" class="Symbol"
      >:</a
      ><a name="13574"
      > </a
      ><a name="13575" class="Symbol"
      >(</a
      ><a name="13576" href="Stlc.html#3672" class="InductiveConstructor Operator"
      >&#955;[</a
      ><a name="13578"
      > </a
      ><a name="13579" href="Stlc.html#5682" class="Function"
      >y</a
      ><a name="13580"
      > </a
      ><a name="13581" href="Stlc.html#3672" class="InductiveConstructor Operator"
      >&#8758;</a
      ><a name="13582"
      > </a
      ><a name="13583" href="Stlc.html#2610" class="InductiveConstructor"
      >&#120121;</a
      ><a name="13584"
      > </a
      ><a name="13585" href="Stlc.html#3672" class="InductiveConstructor Operator"
      >]</a
      ><a name="13586"
      > </a
      ><a name="13587" href="Stlc.html#3656" class="InductiveConstructor"
      >`</a
      ><a name="13588"
      > </a
      ><a name="13589" href="Stlc.html#5682" class="Function"
      >y</a
      ><a name="13590" class="Symbol"
      >)</a
      ><a name="13591"
      > </a
      ><a name="13592" href="Stlc.html#12079" class="Function Operator"
      >[</a
      ><a name="13593"
      > </a
      ><a name="13594" href="Stlc.html#5680" class="Function"
      >x</a
      ><a name="13595"
      > </a
      ><a name="13596" href="Stlc.html#12079" class="Function Operator"
      >:=</a
      ><a name="13598"
      > </a
      ><a name="13599" href="Stlc.html#3735" class="InductiveConstructor"
      >true</a
      ><a name="13603"
      > </a
      ><a name="13604" href="Stlc.html#12079" class="Function Operator"
      >]</a
      ><a name="13605"
      > </a
      ><a name="13606" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="13607"
      > </a
      ><a name="13608" href="Stlc.html#3672" class="InductiveConstructor Operator"
      >&#955;[</a
      ><a name="13610"
      > </a
      ><a name="13611" href="Stlc.html#5682" class="Function"
      >y</a
      ><a name="13612"
      > </a
      ><a name="13613" href="Stlc.html#3672" class="InductiveConstructor Operator"
      >&#8758;</a
      ><a name="13614"
      > </a
      ><a name="13615" href="Stlc.html#2610" class="InductiveConstructor"
      >&#120121;</a
      ><a name="13616"
      > </a
      ><a name="13617" href="Stlc.html#3672" class="InductiveConstructor Operator"
      >]</a
      ><a name="13618"
      > </a
      ><a name="13619" href="Stlc.html#3656" class="InductiveConstructor"
      >`</a
      ><a name="13620"
      > </a
      ><a name="13621" href="Stlc.html#5682" class="Function"
      >y</a
      ><a name="13622"
      >
</a
      ><a name="13623" href="Stlc.html#13568" class="Function"
      >ex&#8321;&#8326;</a
      ><a name="13627"
      > </a
      ><a name="13628" class="Symbol"
      >=</a
      ><a name="13629"
      > </a
      ><a name="13630" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="13634"
      >

</a
      ><a name="13636" href="Stlc.html#13636" class="Function"
      >ex&#8321;&#8327;</a
      ><a name="13640"
      > </a
      ><a name="13641" class="Symbol"
      >:</a
      ><a name="13642"
      > </a
      ><a name="13643" class="Symbol"
      >(</a
      ><a name="13644" href="Stlc.html#3672" class="InductiveConstructor Operator"
      >&#955;[</a
      ><a name="13646"
      > </a
      ><a name="13647" href="Stlc.html#5680" class="Function"
      >x</a
      ><a name="13648"
      > </a
      ><a name="13649" href="Stlc.html#3672" class="InductiveConstructor Operator"
      >&#8758;</a
      ><a name="13650"
      > </a
      ><a name="13651" href="Stlc.html#2610" class="InductiveConstructor"
      >&#120121;</a
      ><a name="13652"
      > </a
      ><a name="13653" href="Stlc.html#3672" class="InductiveConstructor Operator"
      >]</a
      ><a name="13654"
      > </a
      ><a name="13655" href="Stlc.html#3656" class="InductiveConstructor"
      >`</a
      ><a name="13656"
      > </a
      ><a name="13657" href="Stlc.html#5680" class="Function"
      >x</a
      ><a name="13658" class="Symbol"
      >)</a
      ><a name="13659"
      > </a
      ><a name="13660" href="Stlc.html#12079" class="Function Operator"
      >[</a
      ><a name="13661"
      > </a
      ><a name="13662" href="Stlc.html#5680" class="Function"
      >x</a
      ><a name="13663"
      > </a
      ><a name="13664" href="Stlc.html#12079" class="Function Operator"
      >:=</a
      ><a name="13666"
      > </a
      ><a name="13667" href="Stlc.html#3735" class="InductiveConstructor"
      >true</a
      ><a name="13671"
      > </a
      ><a name="13672" href="Stlc.html#12079" class="Function Operator"
      >]</a
      ><a name="13673"
      > </a
      ><a name="13674" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="13675"
      > </a
      ><a name="13676" href="Stlc.html#3672" class="InductiveConstructor Operator"
      >&#955;[</a
      ><a name="13678"
      > </a
      ><a name="13679" href="Stlc.html#5680" class="Function"
      >x</a
      ><a name="13680"
      > </a
      ><a name="13681" href="Stlc.html#3672" class="InductiveConstructor Operator"
      >&#8758;</a
      ><a name="13682"
      > </a
      ><a name="13683" href="Stlc.html#2610" class="InductiveConstructor"
      >&#120121;</a
      ><a name="13684"
      > </a
      ><a name="13685" href="Stlc.html#3672" class="InductiveConstructor Operator"
      >]</a
      ><a name="13686"
      > </a
      ><a name="13687" href="Stlc.html#3656" class="InductiveConstructor"
      >`</a
      ><a name="13688"
      > </a
      ><a name="13689" href="Stlc.html#5680" class="Function"
      >x</a
      ><a name="13690"
      >
</a
      ><a name="13691" href="Stlc.html#13636" class="Function"
      >ex&#8321;&#8327;</a
      ><a name="13695"
      > </a
      ><a name="13696" class="Symbol"
      >=</a
      ><a name="13697"
      > </a
      ><a name="13698" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
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

<a name="15812" class="Keyword"
      >infix</a
      ><a name="15817"
      > </a
      ><a name="15818" class="Number"
      >10</a
      ><a name="15820"
      > </a
      ><a name="15821" href="Stlc.html#15832" class="Datatype Operator"
      >_&#10233;_</a
      ><a name="15824"
      > 

</a
      ><a name="15827" class="Keyword"
      >data</a
      ><a name="15831"
      > </a
      ><a name="15832" href="Stlc.html#15832" class="Datatype Operator"
      >_&#10233;_</a
      ><a name="15835"
      > </a
      ><a name="15836" class="Symbol"
      >:</a
      ><a name="15837"
      > </a
      ><a name="15838" href="Stlc.html#3637" class="Datatype"
      >Term</a
      ><a name="15842"
      > </a
      ><a name="15843" class="Symbol"
      >&#8594;</a
      ><a name="15844"
      > </a
      ><a name="15845" href="Stlc.html#3637" class="Datatype"
      >Term</a
      ><a name="15849"
      > </a
      ><a name="15850" class="Symbol"
      >&#8594;</a
      ><a name="15851"
      > </a
      ><a name="15852" class="PrimitiveType"
      >Set</a
      ><a name="15855"
      > </a
      ><a name="15856" class="Keyword"
      >where</a
      ><a name="15861"
      >
  </a
      ><a name="15864" href="Stlc.html#15864" class="InductiveConstructor"
      >&#958;&#183;&#8321;</a
      ><a name="15867"
      > </a
      ><a name="15868" class="Symbol"
      >:</a
      ><a name="15869"
      > </a
      ><a name="15870" class="Symbol"
      >&#8704;</a
      ><a name="15871"
      > </a
      ><a name="15872" class="Symbol"
      >{</a
      ><a name="15873" href="Stlc.html#15873" class="Bound"
      >L</a
      ><a name="15874"
      > </a
      ><a name="15875" href="Stlc.html#15875" class="Bound"
      >L&#8242;</a
      ><a name="15877"
      > </a
      ><a name="15878" href="Stlc.html#15878" class="Bound"
      >M</a
      ><a name="15879" class="Symbol"
      >}</a
      ><a name="15880"
      > </a
      ><a name="15881" class="Symbol"
      >&#8594;</a
      ><a name="15882"
      >
    </a
      ><a name="15887" href="Stlc.html#15873" class="Bound"
      >L</a
      ><a name="15888"
      > </a
      ><a name="15889" href="Stlc.html#15832" class="Datatype Operator"
      >&#10233;</a
      ><a name="15890"
      > </a
      ><a name="15891" href="Stlc.html#15875" class="Bound"
      >L&#8242;</a
      ><a name="15893"
      > </a
      ><a name="15894" class="Symbol"
      >&#8594;</a
      ><a name="15895"
      >
    </a
      ><a name="15900" href="Stlc.html#15873" class="Bound"
      >L</a
      ><a name="15901"
      > </a
      ><a name="15902" href="Stlc.html#3708" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="15903"
      > </a
      ><a name="15904" href="Stlc.html#15878" class="Bound"
      >M</a
      ><a name="15905"
      > </a
      ><a name="15906" href="Stlc.html#15832" class="Datatype Operator"
      >&#10233;</a
      ><a name="15907"
      > </a
      ><a name="15908" href="Stlc.html#15875" class="Bound"
      >L&#8242;</a
      ><a name="15910"
      > </a
      ><a name="15911" href="Stlc.html#3708" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="15912"
      > </a
      ><a name="15913" href="Stlc.html#15878" class="Bound"
      >M</a
      ><a name="15914"
      >
  </a
      ><a name="15917" href="Stlc.html#15917" class="InductiveConstructor"
      >&#958;&#183;&#8322;</a
      ><a name="15920"
      > </a
      ><a name="15921" class="Symbol"
      >:</a
      ><a name="15922"
      > </a
      ><a name="15923" class="Symbol"
      >&#8704;</a
      ><a name="15924"
      > </a
      ><a name="15925" class="Symbol"
      >{</a
      ><a name="15926" href="Stlc.html#15926" class="Bound"
      >V</a
      ><a name="15927"
      > </a
      ><a name="15928" href="Stlc.html#15928" class="Bound"
      >M</a
      ><a name="15929"
      > </a
      ><a name="15930" href="Stlc.html#15930" class="Bound"
      >M&#8242;</a
      ><a name="15932" class="Symbol"
      >}</a
      ><a name="15933"
      > </a
      ><a name="15934" class="Symbol"
      >&#8594;</a
      ><a name="15935"
      >
    </a
      ><a name="15940" href="Stlc.html#9535" class="Datatype"
      >Value</a
      ><a name="15945"
      > </a
      ><a name="15946" href="Stlc.html#15926" class="Bound"
      >V</a
      ><a name="15947"
      > </a
      ><a name="15948" class="Symbol"
      >&#8594;</a
      ><a name="15949"
      >
    </a
      ><a name="15954" href="Stlc.html#15928" class="Bound"
      >M</a
      ><a name="15955"
      > </a
      ><a name="15956" href="Stlc.html#15832" class="Datatype Operator"
      >&#10233;</a
      ><a name="15957"
      > </a
      ><a name="15958" href="Stlc.html#15930" class="Bound"
      >M&#8242;</a
      ><a name="15960"
      > </a
      ><a name="15961" class="Symbol"
      >&#8594;</a
      ><a name="15962"
      >
    </a
      ><a name="15967" href="Stlc.html#15926" class="Bound"
      >V</a
      ><a name="15968"
      > </a
      ><a name="15969" href="Stlc.html#3708" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="15970"
      > </a
      ><a name="15971" href="Stlc.html#15928" class="Bound"
      >M</a
      ><a name="15972"
      > </a
      ><a name="15973" href="Stlc.html#15832" class="Datatype Operator"
      >&#10233;</a
      ><a name="15974"
      > </a
      ><a name="15975" href="Stlc.html#15926" class="Bound"
      >V</a
      ><a name="15976"
      > </a
      ><a name="15977" href="Stlc.html#3708" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="15978"
      > </a
      ><a name="15979" href="Stlc.html#15930" class="Bound"
      >M&#8242;</a
      ><a name="15981"
      >
  </a
      ><a name="15984" href="Stlc.html#15984" class="InductiveConstructor"
      >&#946;&#955;&#183;</a
      ><a name="15987"
      > </a
      ><a name="15988" class="Symbol"
      >:</a
      ><a name="15989"
      > </a
      ><a name="15990" class="Symbol"
      >&#8704;</a
      ><a name="15991"
      > </a
      ><a name="15992" class="Symbol"
      >{</a
      ><a name="15993" href="Stlc.html#15993" class="Bound"
      >x</a
      ><a name="15994"
      > </a
      ><a name="15995" href="Stlc.html#15995" class="Bound"
      >A</a
      ><a name="15996"
      > </a
      ><a name="15997" href="Stlc.html#15997" class="Bound"
      >N</a
      ><a name="15998"
      > </a
      ><a name="15999" href="Stlc.html#15999" class="Bound"
      >V</a
      ><a name="16000" class="Symbol"
      >}</a
      ><a name="16001"
      > </a
      ><a name="16002" class="Symbol"
      >&#8594;</a
      ><a name="16003"
      > </a
      ><a name="16004" href="Stlc.html#9535" class="Datatype"
      >Value</a
      ><a name="16009"
      > </a
      ><a name="16010" href="Stlc.html#15999" class="Bound"
      >V</a
      ><a name="16011"
      > </a
      ><a name="16012" class="Symbol"
      >&#8594;</a
      ><a name="16013"
      >
    </a
      ><a name="16018" class="Symbol"
      >(</a
      ><a name="16019" href="Stlc.html#3672" class="InductiveConstructor Operator"
      >&#955;[</a
      ><a name="16021"
      > </a
      ><a name="16022" href="Stlc.html#15993" class="Bound"
      >x</a
      ><a name="16023"
      > </a
      ><a name="16024" href="Stlc.html#3672" class="InductiveConstructor Operator"
      >&#8758;</a
      ><a name="16025"
      > </a
      ><a name="16026" href="Stlc.html#15995" class="Bound"
      >A</a
      ><a name="16027"
      > </a
      ><a name="16028" href="Stlc.html#3672" class="InductiveConstructor Operator"
      >]</a
      ><a name="16029"
      > </a
      ><a name="16030" href="Stlc.html#15997" class="Bound"
      >N</a
      ><a name="16031" class="Symbol"
      >)</a
      ><a name="16032"
      > </a
      ><a name="16033" href="Stlc.html#3708" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="16034"
      > </a
      ><a name="16035" href="Stlc.html#15999" class="Bound"
      >V</a
      ><a name="16036"
      > </a
      ><a name="16037" href="Stlc.html#15832" class="Datatype Operator"
      >&#10233;</a
      ><a name="16038"
      > </a
      ><a name="16039" href="Stlc.html#15997" class="Bound"
      >N</a
      ><a name="16040"
      > </a
      ><a name="16041" href="Stlc.html#12079" class="Function Operator"
      >[</a
      ><a name="16042"
      > </a
      ><a name="16043" href="Stlc.html#15993" class="Bound"
      >x</a
      ><a name="16044"
      > </a
      ><a name="16045" href="Stlc.html#12079" class="Function Operator"
      >:=</a
      ><a name="16047"
      > </a
      ><a name="16048" href="Stlc.html#15999" class="Bound"
      >V</a
      ><a name="16049"
      > </a
      ><a name="16050" href="Stlc.html#12079" class="Function Operator"
      >]</a
      ><a name="16051"
      >
  </a
      ><a name="16054" href="Stlc.html#16054" class="InductiveConstructor"
      >&#958;if</a
      ><a name="16057"
      > </a
      ><a name="16058" class="Symbol"
      >:</a
      ><a name="16059"
      > </a
      ><a name="16060" class="Symbol"
      >&#8704;</a
      ><a name="16061"
      > </a
      ><a name="16062" class="Symbol"
      >{</a
      ><a name="16063" href="Stlc.html#16063" class="Bound"
      >L</a
      ><a name="16064"
      > </a
      ><a name="16065" href="Stlc.html#16065" class="Bound"
      >L&#8242;</a
      ><a name="16067"
      > </a
      ><a name="16068" href="Stlc.html#16068" class="Bound"
      >M</a
      ><a name="16069"
      > </a
      ><a name="16070" href="Stlc.html#16070" class="Bound"
      >N</a
      ><a name="16071" class="Symbol"
      >}</a
      ><a name="16072"
      > </a
      ><a name="16073" class="Symbol"
      >&#8594;</a
      ><a name="16074"
      >
    </a
      ><a name="16079" href="Stlc.html#16063" class="Bound"
      >L</a
      ><a name="16080"
      > </a
      ><a name="16081" href="Stlc.html#15832" class="Datatype Operator"
      >&#10233;</a
      ><a name="16082"
      > </a
      ><a name="16083" href="Stlc.html#16065" class="Bound"
      >L&#8242;</a
      ><a name="16085"
      > </a
      ><a name="16086" class="Symbol"
      >&#8594;</a
      ><a name="16087"
      >    
    </a
      ><a name="16096" href="Stlc.html#3764" class="InductiveConstructor Operator"
      >if</a
      ><a name="16098"
      > </a
      ><a name="16099" href="Stlc.html#16063" class="Bound"
      >L</a
      ><a name="16100"
      > </a
      ><a name="16101" href="Stlc.html#3764" class="InductiveConstructor Operator"
      >then</a
      ><a name="16105"
      > </a
      ><a name="16106" href="Stlc.html#16068" class="Bound"
      >M</a
      ><a name="16107"
      > </a
      ><a name="16108" href="Stlc.html#3764" class="InductiveConstructor Operator"
      >else</a
      ><a name="16112"
      > </a
      ><a name="16113" href="Stlc.html#16070" class="Bound"
      >N</a
      ><a name="16114"
      > </a
      ><a name="16115" href="Stlc.html#15832" class="Datatype Operator"
      >&#10233;</a
      ><a name="16116"
      > </a
      ><a name="16117" href="Stlc.html#3764" class="InductiveConstructor Operator"
      >if</a
      ><a name="16119"
      > </a
      ><a name="16120" href="Stlc.html#16065" class="Bound"
      >L&#8242;</a
      ><a name="16122"
      > </a
      ><a name="16123" href="Stlc.html#3764" class="InductiveConstructor Operator"
      >then</a
      ><a name="16127"
      > </a
      ><a name="16128" href="Stlc.html#16068" class="Bound"
      >M</a
      ><a name="16129"
      > </a
      ><a name="16130" href="Stlc.html#3764" class="InductiveConstructor Operator"
      >else</a
      ><a name="16134"
      > </a
      ><a name="16135" href="Stlc.html#16070" class="Bound"
      >N</a
      ><a name="16136"
      >
  </a
      ><a name="16139" href="Stlc.html#16139" class="InductiveConstructor"
      >&#946;if-true</a
      ><a name="16147"
      > </a
      ><a name="16148" class="Symbol"
      >:</a
      ><a name="16149"
      > </a
      ><a name="16150" class="Symbol"
      >&#8704;</a
      ><a name="16151"
      > </a
      ><a name="16152" class="Symbol"
      >{</a
      ><a name="16153" href="Stlc.html#16153" class="Bound"
      >M</a
      ><a name="16154"
      > </a
      ><a name="16155" href="Stlc.html#16155" class="Bound"
      >N</a
      ><a name="16156" class="Symbol"
      >}</a
      ><a name="16157"
      > </a
      ><a name="16158" class="Symbol"
      >&#8594;</a
      ><a name="16159"
      >
    </a
      ><a name="16164" href="Stlc.html#3764" class="InductiveConstructor Operator"
      >if</a
      ><a name="16166"
      > </a
      ><a name="16167" href="Stlc.html#3735" class="InductiveConstructor"
      >true</a
      ><a name="16171"
      > </a
      ><a name="16172" href="Stlc.html#3764" class="InductiveConstructor Operator"
      >then</a
      ><a name="16176"
      > </a
      ><a name="16177" href="Stlc.html#16153" class="Bound"
      >M</a
      ><a name="16178"
      > </a
      ><a name="16179" href="Stlc.html#3764" class="InductiveConstructor Operator"
      >else</a
      ><a name="16183"
      > </a
      ><a name="16184" href="Stlc.html#16155" class="Bound"
      >N</a
      ><a name="16185"
      > </a
      ><a name="16186" href="Stlc.html#15832" class="Datatype Operator"
      >&#10233;</a
      ><a name="16187"
      > </a
      ><a name="16188" href="Stlc.html#16153" class="Bound"
      >M</a
      ><a name="16189"
      >
  </a
      ><a name="16192" href="Stlc.html#16192" class="InductiveConstructor"
      >&#946;if-false</a
      ><a name="16201"
      > </a
      ><a name="16202" class="Symbol"
      >:</a
      ><a name="16203"
      > </a
      ><a name="16204" class="Symbol"
      >&#8704;</a
      ><a name="16205"
      > </a
      ><a name="16206" class="Symbol"
      >{</a
      ><a name="16207" href="Stlc.html#16207" class="Bound"
      >M</a
      ><a name="16208"
      > </a
      ><a name="16209" href="Stlc.html#16209" class="Bound"
      >N</a
      ><a name="16210" class="Symbol"
      >}</a
      ><a name="16211"
      > </a
      ><a name="16212" class="Symbol"
      >&#8594;</a
      ><a name="16213"
      >
    </a
      ><a name="16218" href="Stlc.html#3764" class="InductiveConstructor Operator"
      >if</a
      ><a name="16220"
      > </a
      ><a name="16221" href="Stlc.html#3749" class="InductiveConstructor"
      >false</a
      ><a name="16226"
      > </a
      ><a name="16227" href="Stlc.html#3764" class="InductiveConstructor Operator"
      >then</a
      ><a name="16231"
      > </a
      ><a name="16232" href="Stlc.html#16207" class="Bound"
      >M</a
      ><a name="16233"
      > </a
      ><a name="16234" href="Stlc.html#3764" class="InductiveConstructor Operator"
      >else</a
      ><a name="16238"
      > </a
      ><a name="16239" href="Stlc.html#16209" class="Bound"
      >N</a
      ><a name="16240"
      > </a
      ><a name="16241" href="Stlc.html#15832" class="Datatype Operator"
      >&#10233;</a
      ><a name="16242"
      > </a
      ><a name="16243" href="Stlc.html#16209" class="Bound"
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

<a name="17817" class="Keyword"
      >infix</a
      ><a name="17822"
      > </a
      ><a name="17823" class="Number"
      >10</a
      ><a name="17825"
      > </a
      ><a name="17826" href="Stlc.html#17866" class="Datatype Operator"
      >_&#10233;*_</a
      ><a name="17830"
      > 
</a
      ><a name="17832" class="Keyword"
      >infixr</a
      ><a name="17838"
      > </a
      ><a name="17839" class="Number"
      >2</a
      ><a name="17840"
      > </a
      ><a name="17841" href="Stlc.html#17919" class="InductiveConstructor Operator"
      >_&#10233;&#10216;_&#10217;_</a
      ><a name="17847"
      >
</a
      ><a name="17848" class="Keyword"
      >infix</a
      ><a name="17853"
      >  </a
      ><a name="17855" class="Number"
      >3</a
      ><a name="17856"
      > </a
      ><a name="17857" href="Stlc.html#17899" class="InductiveConstructor Operator"
      >_&#8718;</a
      ><a name="17859"
      >

</a
      ><a name="17861" class="Keyword"
      >data</a
      ><a name="17865"
      > </a
      ><a name="17866" href="Stlc.html#17866" class="Datatype Operator"
      >_&#10233;*_</a
      ><a name="17870"
      > </a
      ><a name="17871" class="Symbol"
      >:</a
      ><a name="17872"
      > </a
      ><a name="17873" href="Stlc.html#3637" class="Datatype"
      >Term</a
      ><a name="17877"
      > </a
      ><a name="17878" class="Symbol"
      >&#8594;</a
      ><a name="17879"
      > </a
      ><a name="17880" href="Stlc.html#3637" class="Datatype"
      >Term</a
      ><a name="17884"
      > </a
      ><a name="17885" class="Symbol"
      >&#8594;</a
      ><a name="17886"
      > </a
      ><a name="17887" class="PrimitiveType"
      >Set</a
      ><a name="17890"
      > </a
      ><a name="17891" class="Keyword"
      >where</a
      ><a name="17896"
      >
  </a
      ><a name="17899" href="Stlc.html#17899" class="InductiveConstructor Operator"
      >_&#8718;</a
      ><a name="17901"
      > </a
      ><a name="17902" class="Symbol"
      >:</a
      ><a name="17903"
      > </a
      ><a name="17904" class="Symbol"
      >&#8704;</a
      ><a name="17905"
      > </a
      ><a name="17906" href="Stlc.html#17906" class="Bound"
      >M</a
      ><a name="17907"
      > </a
      ><a name="17908" class="Symbol"
      >&#8594;</a
      ><a name="17909"
      > </a
      ><a name="17910" href="Stlc.html#17906" class="Bound"
      >M</a
      ><a name="17911"
      > </a
      ><a name="17912" href="Stlc.html#17866" class="Datatype Operator"
      >&#10233;*</a
      ><a name="17914"
      > </a
      ><a name="17915" href="Stlc.html#17906" class="Bound"
      >M</a
      ><a name="17916"
      >
  </a
      ><a name="17919" href="Stlc.html#17919" class="InductiveConstructor Operator"
      >_&#10233;&#10216;_&#10217;_</a
      ><a name="17925"
      > </a
      ><a name="17926" class="Symbol"
      >:</a
      ><a name="17927"
      > </a
      ><a name="17928" class="Symbol"
      >&#8704;</a
      ><a name="17929"
      > </a
      ><a name="17930" href="Stlc.html#17930" class="Bound"
      >L</a
      ><a name="17931"
      > </a
      ><a name="17932" class="Symbol"
      >{</a
      ><a name="17933" href="Stlc.html#17933" class="Bound"
      >M</a
      ><a name="17934"
      > </a
      ><a name="17935" href="Stlc.html#17935" class="Bound"
      >N</a
      ><a name="17936" class="Symbol"
      >}</a
      ><a name="17937"
      > </a
      ><a name="17938" class="Symbol"
      >&#8594;</a
      ><a name="17939"
      > </a
      ><a name="17940" href="Stlc.html#17930" class="Bound"
      >L</a
      ><a name="17941"
      > </a
      ><a name="17942" href="Stlc.html#15832" class="Datatype Operator"
      >&#10233;</a
      ><a name="17943"
      > </a
      ><a name="17944" href="Stlc.html#17933" class="Bound"
      >M</a
      ><a name="17945"
      > </a
      ><a name="17946" class="Symbol"
      >&#8594;</a
      ><a name="17947"
      > </a
      ><a name="17948" href="Stlc.html#17933" class="Bound"
      >M</a
      ><a name="17949"
      > </a
      ><a name="17950" href="Stlc.html#17866" class="Datatype Operator"
      >&#10233;*</a
      ><a name="17952"
      > </a
      ><a name="17953" href="Stlc.html#17935" class="Bound"
      >N</a
      ><a name="17954"
      > </a
      ><a name="17955" class="Symbol"
      >&#8594;</a
      ><a name="17956"
      > </a
      ><a name="17957" href="Stlc.html#17930" class="Bound"
      >L</a
      ><a name="17958"
      > </a
      ><a name="17959" href="Stlc.html#17866" class="Datatype Operator"
      >&#10233;*</a
      ><a name="17961"
      > </a
      ><a name="17962" href="Stlc.html#17935" class="Bound"
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

<a name="18423" href="Stlc.html#18423" class="Function"
      >reduction&#8321;</a
      ><a name="18433"
      > </a
      ><a name="18434" class="Symbol"
      >:</a
      ><a name="18435"
      > </a
      ><a name="18436" href="Stlc.html#5723" class="Function"
      >not</a
      ><a name="18439"
      > </a
      ><a name="18440" href="Stlc.html#3708" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="18441"
      > </a
      ><a name="18442" href="Stlc.html#3735" class="InductiveConstructor"
      >true</a
      ><a name="18446"
      > </a
      ><a name="18447" href="Stlc.html#17866" class="Datatype Operator"
      >&#10233;*</a
      ><a name="18449"
      > </a
      ><a name="18450" href="Stlc.html#3749" class="InductiveConstructor"
      >false</a
      ><a name="18455"
      >
</a
      ><a name="18456" href="Stlc.html#18423" class="Function"
      >reduction&#8321;</a
      ><a name="18466"
      > </a
      ><a name="18467" class="Symbol"
      >=</a
      ><a name="18468"
      >
    </a
      ><a name="18473" href="Stlc.html#5723" class="Function"
      >not</a
      ><a name="18476"
      > </a
      ><a name="18477" href="Stlc.html#3708" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="18478"
      > </a
      ><a name="18479" href="Stlc.html#3735" class="InductiveConstructor"
      >true</a
      ><a name="18483"
      >
  </a
      ><a name="18486" href="Stlc.html#17919" class="InductiveConstructor Operator"
      >&#10233;&#10216;</a
      ><a name="18488"
      > </a
      ><a name="18489" href="Stlc.html#15984" class="InductiveConstructor"
      >&#946;&#955;&#183;</a
      ><a name="18492"
      > </a
      ><a name="18493" href="Stlc.html#9611" class="InductiveConstructor"
      >value-true</a
      ><a name="18503"
      > </a
      ><a name="18504" href="Stlc.html#17919" class="InductiveConstructor Operator"
      >&#10217;</a
      ><a name="18505"
      >
    </a
      ><a name="18510" href="Stlc.html#3764" class="InductiveConstructor Operator"
      >if</a
      ><a name="18512"
      > </a
      ><a name="18513" href="Stlc.html#3735" class="InductiveConstructor"
      >true</a
      ><a name="18517"
      > </a
      ><a name="18518" href="Stlc.html#3764" class="InductiveConstructor Operator"
      >then</a
      ><a name="18522"
      > </a
      ><a name="18523" href="Stlc.html#3749" class="InductiveConstructor"
      >false</a
      ><a name="18528"
      > </a
      ><a name="18529" href="Stlc.html#3764" class="InductiveConstructor Operator"
      >else</a
      ><a name="18533"
      > </a
      ><a name="18534" href="Stlc.html#3735" class="InductiveConstructor"
      >true</a
      ><a name="18538"
      >
  </a
      ><a name="18541" href="Stlc.html#17919" class="InductiveConstructor Operator"
      >&#10233;&#10216;</a
      ><a name="18543"
      > </a
      ><a name="18544" href="Stlc.html#16139" class="InductiveConstructor"
      >&#946;if-true</a
      ><a name="18552"
      > </a
      ><a name="18553" href="Stlc.html#17919" class="InductiveConstructor Operator"
      >&#10217;</a
      ><a name="18554"
      >
    </a
      ><a name="18559" href="Stlc.html#3749" class="InductiveConstructor"
      >false</a
      ><a name="18564"
      >
  </a
      ><a name="18567" href="Stlc.html#17899" class="InductiveConstructor Operator"
      >&#8718;</a
      ><a name="18568"
      >

</a
      ><a name="18570" href="Stlc.html#18570" class="Function"
      >reduction&#8322;</a
      ><a name="18580"
      > </a
      ><a name="18581" class="Symbol"
      >:</a
      ><a name="18582"
      > </a
      ><a name="18583" href="Stlc.html#5727" class="Function"
      >two</a
      ><a name="18586"
      > </a
      ><a name="18587" href="Stlc.html#3708" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="18588"
      > </a
      ><a name="18589" href="Stlc.html#5723" class="Function"
      >not</a
      ><a name="18592"
      > </a
      ><a name="18593" href="Stlc.html#3708" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="18594"
      > </a
      ><a name="18595" href="Stlc.html#3735" class="InductiveConstructor"
      >true</a
      ><a name="18599"
      > </a
      ><a name="18600" href="Stlc.html#17866" class="Datatype Operator"
      >&#10233;*</a
      ><a name="18602"
      > </a
      ><a name="18603" href="Stlc.html#3735" class="InductiveConstructor"
      >true</a
      ><a name="18607"
      >
</a
      ><a name="18608" href="Stlc.html#18570" class="Function"
      >reduction&#8322;</a
      ><a name="18618"
      > </a
      ><a name="18619" class="Symbol"
      >=</a
      ><a name="18620"
      >
    </a
      ><a name="18625" href="Stlc.html#5727" class="Function"
      >two</a
      ><a name="18628"
      > </a
      ><a name="18629" href="Stlc.html#3708" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="18630"
      > </a
      ><a name="18631" href="Stlc.html#5723" class="Function"
      >not</a
      ><a name="18634"
      > </a
      ><a name="18635" href="Stlc.html#3708" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="18636"
      > </a
      ><a name="18637" href="Stlc.html#3735" class="InductiveConstructor"
      >true</a
      ><a name="18641"
      >
  </a
      ><a name="18644" href="Stlc.html#17919" class="InductiveConstructor Operator"
      >&#10233;&#10216;</a
      ><a name="18646"
      > </a
      ><a name="18647" href="Stlc.html#15864" class="InductiveConstructor"
      >&#958;&#183;&#8321;</a
      ><a name="18650"
      > </a
      ><a name="18651" class="Symbol"
      >(</a
      ><a name="18652" href="Stlc.html#15984" class="InductiveConstructor"
      >&#946;&#955;&#183;</a
      ><a name="18655"
      > </a
      ><a name="18656" href="Stlc.html#9562" class="InductiveConstructor"
      >value-&#955;</a
      ><a name="18663" class="Symbol"
      >)</a
      ><a name="18664"
      > </a
      ><a name="18665" href="Stlc.html#17919" class="InductiveConstructor Operator"
      >&#10217;</a
      ><a name="18666"
      >
    </a
      ><a name="18671" class="Symbol"
      >(</a
      ><a name="18672" href="Stlc.html#3672" class="InductiveConstructor Operator"
      >&#955;[</a
      ><a name="18674"
      > </a
      ><a name="18675" href="Stlc.html#5680" class="Function"
      >x</a
      ><a name="18676"
      > </a
      ><a name="18677" href="Stlc.html#3672" class="InductiveConstructor Operator"
      >&#8758;</a
      ><a name="18678"
      > </a
      ><a name="18679" href="Stlc.html#2610" class="InductiveConstructor"
      >&#120121;</a
      ><a name="18680"
      > </a
      ><a name="18681" href="Stlc.html#3672" class="InductiveConstructor Operator"
      >]</a
      ><a name="18682"
      > </a
      ><a name="18683" href="Stlc.html#5723" class="Function"
      >not</a
      ><a name="18686"
      > </a
      ><a name="18687" href="Stlc.html#3708" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="18688"
      > </a
      ><a name="18689" class="Symbol"
      >(</a
      ><a name="18690" href="Stlc.html#5723" class="Function"
      >not</a
      ><a name="18693"
      > </a
      ><a name="18694" href="Stlc.html#3708" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="18695"
      > </a
      ><a name="18696" href="Stlc.html#3656" class="InductiveConstructor"
      >`</a
      ><a name="18697"
      > </a
      ><a name="18698" href="Stlc.html#5680" class="Function"
      >x</a
      ><a name="18699" class="Symbol"
      >))</a
      ><a name="18701"
      > </a
      ><a name="18702" href="Stlc.html#3708" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="18703"
      > </a
      ><a name="18704" href="Stlc.html#3735" class="InductiveConstructor"
      >true</a
      ><a name="18708"
      >
  </a
      ><a name="18711" href="Stlc.html#17919" class="InductiveConstructor Operator"
      >&#10233;&#10216;</a
      ><a name="18713"
      > </a
      ><a name="18714" href="Stlc.html#15984" class="InductiveConstructor"
      >&#946;&#955;&#183;</a
      ><a name="18717"
      > </a
      ><a name="18718" href="Stlc.html#9611" class="InductiveConstructor"
      >value-true</a
      ><a name="18728"
      > </a
      ><a name="18729" href="Stlc.html#17919" class="InductiveConstructor Operator"
      >&#10217;</a
      ><a name="18730"
      >
    </a
      ><a name="18735" href="Stlc.html#5723" class="Function"
      >not</a
      ><a name="18738"
      > </a
      ><a name="18739" href="Stlc.html#3708" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="18740"
      > </a
      ><a name="18741" class="Symbol"
      >(</a
      ><a name="18742" href="Stlc.html#5723" class="Function"
      >not</a
      ><a name="18745"
      > </a
      ><a name="18746" href="Stlc.html#3708" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="18747"
      > </a
      ><a name="18748" href="Stlc.html#3735" class="InductiveConstructor"
      >true</a
      ><a name="18752" class="Symbol"
      >)</a
      ><a name="18753"
      >
  </a
      ><a name="18756" href="Stlc.html#17919" class="InductiveConstructor Operator"
      >&#10233;&#10216;</a
      ><a name="18758"
      > </a
      ><a name="18759" href="Stlc.html#15917" class="InductiveConstructor"
      >&#958;&#183;&#8322;</a
      ><a name="18762"
      > </a
      ><a name="18763" href="Stlc.html#9562" class="InductiveConstructor"
      >value-&#955;</a
      ><a name="18770"
      > </a
      ><a name="18771" class="Symbol"
      >(</a
      ><a name="18772" href="Stlc.html#15984" class="InductiveConstructor"
      >&#946;&#955;&#183;</a
      ><a name="18775"
      > </a
      ><a name="18776" href="Stlc.html#9611" class="InductiveConstructor"
      >value-true</a
      ><a name="18786" class="Symbol"
      >)</a
      ><a name="18787"
      > </a
      ><a name="18788" href="Stlc.html#17919" class="InductiveConstructor Operator"
      >&#10217;</a
      ><a name="18789"
      >
    </a
      ><a name="18794" href="Stlc.html#5723" class="Function"
      >not</a
      ><a name="18797"
      > </a
      ><a name="18798" href="Stlc.html#3708" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="18799"
      > </a
      ><a name="18800" class="Symbol"
      >(</a
      ><a name="18801" href="Stlc.html#3764" class="InductiveConstructor Operator"
      >if</a
      ><a name="18803"
      > </a
      ><a name="18804" href="Stlc.html#3735" class="InductiveConstructor"
      >true</a
      ><a name="18808"
      > </a
      ><a name="18809" href="Stlc.html#3764" class="InductiveConstructor Operator"
      >then</a
      ><a name="18813"
      > </a
      ><a name="18814" href="Stlc.html#3749" class="InductiveConstructor"
      >false</a
      ><a name="18819"
      > </a
      ><a name="18820" href="Stlc.html#3764" class="InductiveConstructor Operator"
      >else</a
      ><a name="18824"
      > </a
      ><a name="18825" href="Stlc.html#3735" class="InductiveConstructor"
      >true</a
      ><a name="18829" class="Symbol"
      >)</a
      ><a name="18830"
      >
  </a
      ><a name="18833" href="Stlc.html#17919" class="InductiveConstructor Operator"
      >&#10233;&#10216;</a
      ><a name="18835"
      > </a
      ><a name="18836" href="Stlc.html#15917" class="InductiveConstructor"
      >&#958;&#183;&#8322;</a
      ><a name="18839"
      > </a
      ><a name="18840" href="Stlc.html#9562" class="InductiveConstructor"
      >value-&#955;</a
      ><a name="18847"
      > </a
      ><a name="18848" href="Stlc.html#16139" class="InductiveConstructor"
      >&#946;if-true</a
      ><a name="18856"
      >  </a
      ><a name="18858" href="Stlc.html#17919" class="InductiveConstructor Operator"
      >&#10217;</a
      ><a name="18859"
      >
    </a
      ><a name="18864" href="Stlc.html#5723" class="Function"
      >not</a
      ><a name="18867"
      > </a
      ><a name="18868" href="Stlc.html#3708" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="18869"
      > </a
      ><a name="18870" href="Stlc.html#3749" class="InductiveConstructor"
      >false</a
      ><a name="18875"
      >
  </a
      ><a name="18878" href="Stlc.html#17919" class="InductiveConstructor Operator"
      >&#10233;&#10216;</a
      ><a name="18880"
      > </a
      ><a name="18881" href="Stlc.html#15984" class="InductiveConstructor"
      >&#946;&#955;&#183;</a
      ><a name="18884"
      > </a
      ><a name="18885" href="Stlc.html#9638" class="InductiveConstructor"
      >value-false</a
      ><a name="18896"
      > </a
      ><a name="18897" href="Stlc.html#17919" class="InductiveConstructor Operator"
      >&#10217;</a
      ><a name="18898"
      >
    </a
      ><a name="18903" href="Stlc.html#3764" class="InductiveConstructor Operator"
      >if</a
      ><a name="18905"
      > </a
      ><a name="18906" href="Stlc.html#3749" class="InductiveConstructor"
      >false</a
      ><a name="18911"
      > </a
      ><a name="18912" href="Stlc.html#3764" class="InductiveConstructor Operator"
      >then</a
      ><a name="18916"
      > </a
      ><a name="18917" href="Stlc.html#3749" class="InductiveConstructor"
      >false</a
      ><a name="18922"
      > </a
      ><a name="18923" href="Stlc.html#3764" class="InductiveConstructor Operator"
      >else</a
      ><a name="18927"
      > </a
      ><a name="18928" href="Stlc.html#3735" class="InductiveConstructor"
      >true</a
      ><a name="18932"
      >
  </a
      ><a name="18935" href="Stlc.html#17919" class="InductiveConstructor Operator"
      >&#10233;&#10216;</a
      ><a name="18937"
      > </a
      ><a name="18938" href="Stlc.html#16192" class="InductiveConstructor"
      >&#946;if-false</a
      ><a name="18947"
      > </a
      ><a name="18948" href="Stlc.html#17919" class="InductiveConstructor Operator"
      >&#10217;</a
      ><a name="18949"
      >
    </a
      ><a name="18954" href="Stlc.html#3735" class="InductiveConstructor"
      >true</a
      ><a name="18958"
      >
  </a
      ><a name="18961" href="Stlc.html#17899" class="InductiveConstructor Operator"
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

<a name="21507" href="Stlc.html#21507" class="Function"
      >Context</a
      ><a name="21514"
      > </a
      ><a name="21515" class="Symbol"
      >:</a
      ><a name="21516"
      > </a
      ><a name="21517" class="PrimitiveType"
      >Set</a
      ><a name="21520"
      >
</a
      ><a name="21521" href="Stlc.html#21507" class="Function"
      >Context</a
      ><a name="21528"
      > </a
      ><a name="21529" class="Symbol"
      >=</a
      ><a name="21530"
      > </a
      ><a name="21531" href="Maps.html#10132" class="Function"
      >PartialMap</a
      ><a name="21541"
      > </a
      ><a name="21542" href="Stlc.html#2564" class="Datatype"
      >Type</a
      ><a name="21546"
      >

</a
      ><a name="21548" class="Keyword"
      >infix</a
      ><a name="21553"
      > </a
      ><a name="21554" class="Number"
      >10</a
      ><a name="21556"
      > </a
      ><a name="21557" href="Stlc.html#21569" class="Datatype Operator"
      >_&#8866;_&#8758;_</a
      ><a name="21562"
      >

</a
      ><a name="21564" class="Keyword"
      >data</a
      ><a name="21568"
      > </a
      ><a name="21569" href="Stlc.html#21569" class="Datatype Operator"
      >_&#8866;_&#8758;_</a
      ><a name="21574"
      > </a
      ><a name="21575" class="Symbol"
      >:</a
      ><a name="21576"
      > </a
      ><a name="21577" href="Stlc.html#21507" class="Function"
      >Context</a
      ><a name="21584"
      > </a
      ><a name="21585" class="Symbol"
      >&#8594;</a
      ><a name="21586"
      > </a
      ><a name="21587" href="Stlc.html#3637" class="Datatype"
      >Term</a
      ><a name="21591"
      > </a
      ><a name="21592" class="Symbol"
      >&#8594;</a
      ><a name="21593"
      > </a
      ><a name="21594" href="Stlc.html#2564" class="Datatype"
      >Type</a
      ><a name="21598"
      > </a
      ><a name="21599" class="Symbol"
      >&#8594;</a
      ><a name="21600"
      > </a
      ><a name="21601" class="PrimitiveType"
      >Set</a
      ><a name="21604"
      > </a
      ><a name="21605" class="Keyword"
      >where</a
      ><a name="21610"
      >
  </a
      ><a name="21613" href="Stlc.html#21613" class="InductiveConstructor"
      >Ax</a
      ><a name="21615"
      > </a
      ><a name="21616" class="Symbol"
      >:</a
      ><a name="21617"
      > </a
      ><a name="21618" class="Symbol"
      >&#8704;</a
      ><a name="21619"
      > </a
      ><a name="21620" class="Symbol"
      >{</a
      ><a name="21621" href="Stlc.html#21621" class="Bound"
      >&#915;</a
      ><a name="21622"
      > </a
      ><a name="21623" href="Stlc.html#21623" class="Bound"
      >x</a
      ><a name="21624"
      > </a
      ><a name="21625" href="Stlc.html#21625" class="Bound"
      >A</a
      ><a name="21626" class="Symbol"
      >}</a
      ><a name="21627"
      > </a
      ><a name="21628" class="Symbol"
      >&#8594;</a
      ><a name="21629"
      >
    </a
      ><a name="21634" href="Stlc.html#21621" class="Bound"
      >&#915;</a
      ><a name="21635"
      > </a
      ><a name="21636" href="Stlc.html#21623" class="Bound"
      >x</a
      ><a name="21637"
      > </a
      ><a name="21638" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="21639"
      > </a
      ><a name="21640" href="https://agda.github.io/agda-stdlib/Data.Maybe.Base.html#373" class="InductiveConstructor"
      >just</a
      ><a name="21644"
      > </a
      ><a name="21645" href="Stlc.html#21625" class="Bound"
      >A</a
      ><a name="21646"
      > </a
      ><a name="21647" class="Symbol"
      >&#8594;</a
      ><a name="21648"
      >
    </a
      ><a name="21653" href="Stlc.html#21621" class="Bound"
      >&#915;</a
      ><a name="21654"
      > </a
      ><a name="21655" href="Stlc.html#21569" class="Datatype Operator"
      >&#8866;</a
      ><a name="21656"
      > </a
      ><a name="21657" href="Stlc.html#3656" class="InductiveConstructor"
      >`</a
      ><a name="21658"
      > </a
      ><a name="21659" href="Stlc.html#21623" class="Bound"
      >x</a
      ><a name="21660"
      > </a
      ><a name="21661" href="Stlc.html#21569" class="Datatype Operator"
      >&#8758;</a
      ><a name="21662"
      > </a
      ><a name="21663" href="Stlc.html#21625" class="Bound"
      >A</a
      ><a name="21664"
      >
  </a
      ><a name="21667" href="Stlc.html#21667" class="InductiveConstructor"
      >&#8658;-I</a
      ><a name="21670"
      > </a
      ><a name="21671" class="Symbol"
      >:</a
      ><a name="21672"
      > </a
      ><a name="21673" class="Symbol"
      >&#8704;</a
      ><a name="21674"
      > </a
      ><a name="21675" class="Symbol"
      >{</a
      ><a name="21676" href="Stlc.html#21676" class="Bound"
      >&#915;</a
      ><a name="21677"
      > </a
      ><a name="21678" href="Stlc.html#21678" class="Bound"
      >x</a
      ><a name="21679"
      > </a
      ><a name="21680" href="Stlc.html#21680" class="Bound"
      >N</a
      ><a name="21681"
      > </a
      ><a name="21682" href="Stlc.html#21682" class="Bound"
      >A</a
      ><a name="21683"
      > </a
      ><a name="21684" href="Stlc.html#21684" class="Bound"
      >B</a
      ><a name="21685" class="Symbol"
      >}</a
      ><a name="21686"
      > </a
      ><a name="21687" class="Symbol"
      >&#8594;</a
      ><a name="21688"
      >
    </a
      ><a name="21693" href="Stlc.html#21676" class="Bound"
      >&#915;</a
      ><a name="21694"
      > </a
      ><a name="21695" href="Maps.html#10368" class="Function Operator"
      >,</a
      ><a name="21696"
      > </a
      ><a name="21697" href="Stlc.html#21678" class="Bound"
      >x</a
      ><a name="21698"
      > </a
      ><a name="21699" href="Maps.html#10368" class="Function Operator"
      >&#8758;</a
      ><a name="21700"
      > </a
      ><a name="21701" href="Stlc.html#21682" class="Bound"
      >A</a
      ><a name="21702"
      > </a
      ><a name="21703" href="Stlc.html#21569" class="Datatype Operator"
      >&#8866;</a
      ><a name="21704"
      > </a
      ><a name="21705" href="Stlc.html#21680" class="Bound"
      >N</a
      ><a name="21706"
      > </a
      ><a name="21707" href="Stlc.html#21569" class="Datatype Operator"
      >&#8758;</a
      ><a name="21708"
      > </a
      ><a name="21709" href="Stlc.html#21684" class="Bound"
      >B</a
      ><a name="21710"
      > </a
      ><a name="21711" class="Symbol"
      >&#8594;</a
      ><a name="21712"
      >
    </a
      ><a name="21717" href="Stlc.html#21676" class="Bound"
      >&#915;</a
      ><a name="21718"
      > </a
      ><a name="21719" href="Stlc.html#21569" class="Datatype Operator"
      >&#8866;</a
      ><a name="21720"
      > </a
      ><a name="21721" href="Stlc.html#3672" class="InductiveConstructor Operator"
      >&#955;[</a
      ><a name="21723"
      > </a
      ><a name="21724" href="Stlc.html#21678" class="Bound"
      >x</a
      ><a name="21725"
      > </a
      ><a name="21726" href="Stlc.html#3672" class="InductiveConstructor Operator"
      >&#8758;</a
      ><a name="21727"
      > </a
      ><a name="21728" href="Stlc.html#21682" class="Bound"
      >A</a
      ><a name="21729"
      > </a
      ><a name="21730" href="Stlc.html#3672" class="InductiveConstructor Operator"
      >]</a
      ><a name="21731"
      > </a
      ><a name="21732" href="Stlc.html#21680" class="Bound"
      >N</a
      ><a name="21733"
      > </a
      ><a name="21734" href="Stlc.html#21569" class="Datatype Operator"
      >&#8758;</a
      ><a name="21735"
      > </a
      ><a name="21736" href="Stlc.html#21682" class="Bound"
      >A</a
      ><a name="21737"
      > </a
      ><a name="21738" href="Stlc.html#2583" class="InductiveConstructor Operator"
      >&#8658;</a
      ><a name="21739"
      > </a
      ><a name="21740" href="Stlc.html#21684" class="Bound"
      >B</a
      ><a name="21741"
      >
  </a
      ><a name="21744" href="Stlc.html#21744" class="InductiveConstructor"
      >&#8658;-E</a
      ><a name="21747"
      > </a
      ><a name="21748" class="Symbol"
      >:</a
      ><a name="21749"
      > </a
      ><a name="21750" class="Symbol"
      >&#8704;</a
      ><a name="21751"
      > </a
      ><a name="21752" class="Symbol"
      >{</a
      ><a name="21753" href="Stlc.html#21753" class="Bound"
      >&#915;</a
      ><a name="21754"
      > </a
      ><a name="21755" href="Stlc.html#21755" class="Bound"
      >L</a
      ><a name="21756"
      > </a
      ><a name="21757" href="Stlc.html#21757" class="Bound"
      >M</a
      ><a name="21758"
      > </a
      ><a name="21759" href="Stlc.html#21759" class="Bound"
      >A</a
      ><a name="21760"
      > </a
      ><a name="21761" href="Stlc.html#21761" class="Bound"
      >B</a
      ><a name="21762" class="Symbol"
      >}</a
      ><a name="21763"
      > </a
      ><a name="21764" class="Symbol"
      >&#8594;</a
      ><a name="21765"
      >
    </a
      ><a name="21770" href="Stlc.html#21753" class="Bound"
      >&#915;</a
      ><a name="21771"
      > </a
      ><a name="21772" href="Stlc.html#21569" class="Datatype Operator"
      >&#8866;</a
      ><a name="21773"
      > </a
      ><a name="21774" href="Stlc.html#21755" class="Bound"
      >L</a
      ><a name="21775"
      > </a
      ><a name="21776" href="Stlc.html#21569" class="Datatype Operator"
      >&#8758;</a
      ><a name="21777"
      > </a
      ><a name="21778" href="Stlc.html#21759" class="Bound"
      >A</a
      ><a name="21779"
      > </a
      ><a name="21780" href="Stlc.html#2583" class="InductiveConstructor Operator"
      >&#8658;</a
      ><a name="21781"
      > </a
      ><a name="21782" href="Stlc.html#21761" class="Bound"
      >B</a
      ><a name="21783"
      > </a
      ><a name="21784" class="Symbol"
      >&#8594;</a
      ><a name="21785"
      >
    </a
      ><a name="21790" href="Stlc.html#21753" class="Bound"
      >&#915;</a
      ><a name="21791"
      > </a
      ><a name="21792" href="Stlc.html#21569" class="Datatype Operator"
      >&#8866;</a
      ><a name="21793"
      > </a
      ><a name="21794" href="Stlc.html#21757" class="Bound"
      >M</a
      ><a name="21795"
      > </a
      ><a name="21796" href="Stlc.html#21569" class="Datatype Operator"
      >&#8758;</a
      ><a name="21797"
      > </a
      ><a name="21798" href="Stlc.html#21759" class="Bound"
      >A</a
      ><a name="21799"
      > </a
      ><a name="21800" class="Symbol"
      >&#8594;</a
      ><a name="21801"
      >
    </a
      ><a name="21806" href="Stlc.html#21753" class="Bound"
      >&#915;</a
      ><a name="21807"
      > </a
      ><a name="21808" href="Stlc.html#21569" class="Datatype Operator"
      >&#8866;</a
      ><a name="21809"
      > </a
      ><a name="21810" href="Stlc.html#21755" class="Bound"
      >L</a
      ><a name="21811"
      > </a
      ><a name="21812" href="Stlc.html#3708" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="21813"
      > </a
      ><a name="21814" href="Stlc.html#21757" class="Bound"
      >M</a
      ><a name="21815"
      > </a
      ><a name="21816" href="Stlc.html#21569" class="Datatype Operator"
      >&#8758;</a
      ><a name="21817"
      > </a
      ><a name="21818" href="Stlc.html#21761" class="Bound"
      >B</a
      ><a name="21819"
      >
  </a
      ><a name="21822" href="Stlc.html#21822" class="InductiveConstructor"
      >&#120121;-I&#8321;</a
      ><a name="21826"
      > </a
      ><a name="21827" class="Symbol"
      >:</a
      ><a name="21828"
      > </a
      ><a name="21829" class="Symbol"
      >&#8704;</a
      ><a name="21830"
      > </a
      ><a name="21831" class="Symbol"
      >{</a
      ><a name="21832" href="Stlc.html#21832" class="Bound"
      >&#915;</a
      ><a name="21833" class="Symbol"
      >}</a
      ><a name="21834"
      > </a
      ><a name="21835" class="Symbol"
      >&#8594;</a
      ><a name="21836"
      >
    </a
      ><a name="21841" href="Stlc.html#21832" class="Bound"
      >&#915;</a
      ><a name="21842"
      > </a
      ><a name="21843" href="Stlc.html#21569" class="Datatype Operator"
      >&#8866;</a
      ><a name="21844"
      > </a
      ><a name="21845" href="Stlc.html#3735" class="InductiveConstructor"
      >true</a
      ><a name="21849"
      > </a
      ><a name="21850" href="Stlc.html#21569" class="Datatype Operator"
      >&#8758;</a
      ><a name="21851"
      > </a
      ><a name="21852" href="Stlc.html#2610" class="InductiveConstructor"
      >&#120121;</a
      ><a name="21853"
      >
  </a
      ><a name="21856" href="Stlc.html#21856" class="InductiveConstructor"
      >&#120121;-I&#8322;</a
      ><a name="21860"
      > </a
      ><a name="21861" class="Symbol"
      >:</a
      ><a name="21862"
      > </a
      ><a name="21863" class="Symbol"
      >&#8704;</a
      ><a name="21864"
      > </a
      ><a name="21865" class="Symbol"
      >{</a
      ><a name="21866" href="Stlc.html#21866" class="Bound"
      >&#915;</a
      ><a name="21867" class="Symbol"
      >}</a
      ><a name="21868"
      > </a
      ><a name="21869" class="Symbol"
      >&#8594;</a
      ><a name="21870"
      >
    </a
      ><a name="21875" href="Stlc.html#21866" class="Bound"
      >&#915;</a
      ><a name="21876"
      > </a
      ><a name="21877" href="Stlc.html#21569" class="Datatype Operator"
      >&#8866;</a
      ><a name="21878"
      > </a
      ><a name="21879" href="Stlc.html#3749" class="InductiveConstructor"
      >false</a
      ><a name="21884"
      > </a
      ><a name="21885" href="Stlc.html#21569" class="Datatype Operator"
      >&#8758;</a
      ><a name="21886"
      > </a
      ><a name="21887" href="Stlc.html#2610" class="InductiveConstructor"
      >&#120121;</a
      ><a name="21888"
      >
  </a
      ><a name="21891" href="Stlc.html#21891" class="InductiveConstructor"
      >&#120121;-E</a
      ><a name="21894"
      > </a
      ><a name="21895" class="Symbol"
      >:</a
      ><a name="21896"
      > </a
      ><a name="21897" class="Symbol"
      >&#8704;</a
      ><a name="21898"
      > </a
      ><a name="21899" class="Symbol"
      >{</a
      ><a name="21900" href="Stlc.html#21900" class="Bound"
      >&#915;</a
      ><a name="21901"
      > </a
      ><a name="21902" href="Stlc.html#21902" class="Bound"
      >L</a
      ><a name="21903"
      > </a
      ><a name="21904" href="Stlc.html#21904" class="Bound"
      >M</a
      ><a name="21905"
      > </a
      ><a name="21906" href="Stlc.html#21906" class="Bound"
      >N</a
      ><a name="21907"
      > </a
      ><a name="21908" href="Stlc.html#21908" class="Bound"
      >A</a
      ><a name="21909" class="Symbol"
      >}</a
      ><a name="21910"
      > </a
      ><a name="21911" class="Symbol"
      >&#8594;</a
      ><a name="21912"
      >
    </a
      ><a name="21917" href="Stlc.html#21900" class="Bound"
      >&#915;</a
      ><a name="21918"
      > </a
      ><a name="21919" href="Stlc.html#21569" class="Datatype Operator"
      >&#8866;</a
      ><a name="21920"
      > </a
      ><a name="21921" href="Stlc.html#21902" class="Bound"
      >L</a
      ><a name="21922"
      > </a
      ><a name="21923" href="Stlc.html#21569" class="Datatype Operator"
      >&#8758;</a
      ><a name="21924"
      > </a
      ><a name="21925" href="Stlc.html#2610" class="InductiveConstructor"
      >&#120121;</a
      ><a name="21926"
      > </a
      ><a name="21927" class="Symbol"
      >&#8594;</a
      ><a name="21928"
      >
    </a
      ><a name="21933" href="Stlc.html#21900" class="Bound"
      >&#915;</a
      ><a name="21934"
      > </a
      ><a name="21935" href="Stlc.html#21569" class="Datatype Operator"
      >&#8866;</a
      ><a name="21936"
      > </a
      ><a name="21937" href="Stlc.html#21904" class="Bound"
      >M</a
      ><a name="21938"
      > </a
      ><a name="21939" href="Stlc.html#21569" class="Datatype Operator"
      >&#8758;</a
      ><a name="21940"
      > </a
      ><a name="21941" href="Stlc.html#21908" class="Bound"
      >A</a
      ><a name="21942"
      > </a
      ><a name="21943" class="Symbol"
      >&#8594;</a
      ><a name="21944"
      >
    </a
      ><a name="21949" href="Stlc.html#21900" class="Bound"
      >&#915;</a
      ><a name="21950"
      > </a
      ><a name="21951" href="Stlc.html#21569" class="Datatype Operator"
      >&#8866;</a
      ><a name="21952"
      > </a
      ><a name="21953" href="Stlc.html#21906" class="Bound"
      >N</a
      ><a name="21954"
      > </a
      ><a name="21955" href="Stlc.html#21569" class="Datatype Operator"
      >&#8758;</a
      ><a name="21956"
      > </a
      ><a name="21957" href="Stlc.html#21908" class="Bound"
      >A</a
      ><a name="21958"
      > </a
      ><a name="21959" class="Symbol"
      >&#8594;</a
      ><a name="21960"
      >
    </a
      ><a name="21965" href="Stlc.html#21900" class="Bound"
      >&#915;</a
      ><a name="21966"
      > </a
      ><a name="21967" href="Stlc.html#21569" class="Datatype Operator"
      >&#8866;</a
      ><a name="21968"
      > </a
      ><a name="21969" href="Stlc.html#3764" class="InductiveConstructor Operator"
      >if</a
      ><a name="21971"
      > </a
      ><a name="21972" href="Stlc.html#21902" class="Bound"
      >L</a
      ><a name="21973"
      > </a
      ><a name="21974" href="Stlc.html#3764" class="InductiveConstructor Operator"
      >then</a
      ><a name="21978"
      > </a
      ><a name="21979" href="Stlc.html#21904" class="Bound"
      >M</a
      ><a name="21980"
      > </a
      ><a name="21981" href="Stlc.html#3764" class="InductiveConstructor Operator"
      >else</a
      ><a name="21985"
      > </a
      ><a name="21986" href="Stlc.html#21906" class="Bound"
      >N</a
      ><a name="21987"
      > </a
      ><a name="21988" href="Stlc.html#21569" class="Datatype Operator"
      >&#8758;</a
      ><a name="21989"
      > </a
      ><a name="21990" href="Stlc.html#21908" class="Bound"
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

<a name="23273" href="Stlc.html#23273" class="Function"
      >typing&#8321;</a
      ><a name="23280"
      > </a
      ><a name="23281" class="Symbol"
      >:</a
      ><a name="23282"
      > </a
      ><a name="23283" href="Maps.html#10265" class="Function"
      >&#8709;</a
      ><a name="23284"
      > </a
      ><a name="23285" href="Stlc.html#21569" class="Datatype Operator"
      >&#8866;</a
      ><a name="23286"
      > </a
      ><a name="23287" href="Stlc.html#5723" class="Function"
      >not</a
      ><a name="23290"
      > </a
      ><a name="23291" href="Stlc.html#21569" class="Datatype Operator"
      >&#8758;</a
      ><a name="23292"
      > </a
      ><a name="23293" href="Stlc.html#2610" class="InductiveConstructor"
      >&#120121;</a
      ><a name="23294"
      > </a
      ><a name="23295" href="Stlc.html#2583" class="InductiveConstructor Operator"
      >&#8658;</a
      ><a name="23296"
      > </a
      ><a name="23297" href="Stlc.html#2610" class="InductiveConstructor"
      >&#120121;</a
      ><a name="23298"
      >
</a
      ><a name="23299" href="Stlc.html#23273" class="Function"
      >typing&#8321;</a
      ><a name="23306"
      > </a
      ><a name="23307" class="Symbol"
      >=</a
      ><a name="23308"
      > </a
      ><a name="23309" href="Stlc.html#21667" class="InductiveConstructor"
      >&#8658;-I</a
      ><a name="23312"
      > </a
      ><a name="23313" class="Symbol"
      >(</a
      ><a name="23314" href="Stlc.html#21891" class="InductiveConstructor"
      >&#120121;-E</a
      ><a name="23317"
      > </a
      ><a name="23318" class="Symbol"
      >(</a
      ><a name="23319" href="Stlc.html#21613" class="InductiveConstructor"
      >Ax</a
      ><a name="23321"
      > </a
      ><a name="23322" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="23326" class="Symbol"
      >)</a
      ><a name="23327"
      > </a
      ><a name="23328" href="Stlc.html#21856" class="InductiveConstructor"
      >&#120121;-I&#8322;</a
      ><a name="23332"
      > </a
      ><a name="23333" href="Stlc.html#21822" class="InductiveConstructor"
      >&#120121;-I&#8321;</a
      ><a name="23337" class="Symbol"
      >)</a
      ><a name="23338"
      >

</a
      ><a name="23340" href="Stlc.html#23340" class="Function"
      >typing&#8322;</a
      ><a name="23347"
      > </a
      ><a name="23348" class="Symbol"
      >:</a
      ><a name="23349"
      > </a
      ><a name="23350" href="Maps.html#10265" class="Function"
      >&#8709;</a
      ><a name="23351"
      > </a
      ><a name="23352" href="Stlc.html#21569" class="Datatype Operator"
      >&#8866;</a
      ><a name="23353"
      > </a
      ><a name="23354" href="Stlc.html#5727" class="Function"
      >two</a
      ><a name="23357"
      > </a
      ><a name="23358" href="Stlc.html#21569" class="Datatype Operator"
      >&#8758;</a
      ><a name="23359"
      > </a
      ><a name="23360" class="Symbol"
      >(</a
      ><a name="23361" href="Stlc.html#2610" class="InductiveConstructor"
      >&#120121;</a
      ><a name="23362"
      > </a
      ><a name="23363" href="Stlc.html#2583" class="InductiveConstructor Operator"
      >&#8658;</a
      ><a name="23364"
      > </a
      ><a name="23365" href="Stlc.html#2610" class="InductiveConstructor"
      >&#120121;</a
      ><a name="23366" class="Symbol"
      >)</a
      ><a name="23367"
      > </a
      ><a name="23368" href="Stlc.html#2583" class="InductiveConstructor Operator"
      >&#8658;</a
      ><a name="23369"
      > </a
      ><a name="23370" href="Stlc.html#2610" class="InductiveConstructor"
      >&#120121;</a
      ><a name="23371"
      > </a
      ><a name="23372" href="Stlc.html#2583" class="InductiveConstructor Operator"
      >&#8658;</a
      ><a name="23373"
      > </a
      ><a name="23374" href="Stlc.html#2610" class="InductiveConstructor"
      >&#120121;</a
      ><a name="23375"
      >
</a
      ><a name="23376" href="Stlc.html#23340" class="Function"
      >typing&#8322;</a
      ><a name="23383"
      > </a
      ><a name="23384" class="Symbol"
      >=</a
      ><a name="23385"
      > </a
      ><a name="23386" href="Stlc.html#21667" class="InductiveConstructor"
      >&#8658;-I</a
      ><a name="23389"
      > </a
      ><a name="23390" class="Symbol"
      >(</a
      ><a name="23391" href="Stlc.html#21667" class="InductiveConstructor"
      >&#8658;-I</a
      ><a name="23394"
      > </a
      ><a name="23395" class="Symbol"
      >(</a
      ><a name="23396" href="Stlc.html#21744" class="InductiveConstructor"
      >&#8658;-E</a
      ><a name="23399"
      > </a
      ><a name="23400" class="Symbol"
      >(</a
      ><a name="23401" href="Stlc.html#21613" class="InductiveConstructor"
      >Ax</a
      ><a name="23403"
      > </a
      ><a name="23404" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="23408" class="Symbol"
      >)</a
      ><a name="23409"
      > </a
      ><a name="23410" class="Symbol"
      >(</a
      ><a name="23411" href="Stlc.html#21744" class="InductiveConstructor"
      >&#8658;-E</a
      ><a name="23414"
      > </a
      ><a name="23415" class="Symbol"
      >(</a
      ><a name="23416" href="Stlc.html#21613" class="InductiveConstructor"
      >Ax</a
      ><a name="23418"
      > </a
      ><a name="23419" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="23423" class="Symbol"
      >)</a
      ><a name="23424"
      > </a
      ><a name="23425" class="Symbol"
      >(</a
      ><a name="23426" href="Stlc.html#21613" class="InductiveConstructor"
      >Ax</a
      ><a name="23428"
      > </a
      ><a name="23429" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="23433" class="Symbol"
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

<a name="25114" href="Stlc.html#25114" class="Function"
      >notyping&#8322;</a
      ><a name="25123"
      > </a
      ><a name="25124" class="Symbol"
      >:</a
      ><a name="25125"
      > </a
      ><a name="25126" class="Symbol"
      >&#8704;</a
      ><a name="25127"
      > </a
      ><a name="25128" class="Symbol"
      >{</a
      ><a name="25129" href="Stlc.html#25129" class="Bound"
      >A</a
      ><a name="25130" class="Symbol"
      >}</a
      ><a name="25131"
      > </a
      ><a name="25132" class="Symbol"
      >&#8594;</a
      ><a name="25133"
      > </a
      ><a name="25134" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#414" class="Function Operator"
      >&#172;</a
      ><a name="25135"
      > </a
      ><a name="25136" class="Symbol"
      >(</a
      ><a name="25137" href="Maps.html#10265" class="Function"
      >&#8709;</a
      ><a name="25138"
      > </a
      ><a name="25139" href="Stlc.html#21569" class="Datatype Operator"
      >&#8866;</a
      ><a name="25140"
      > </a
      ><a name="25141" href="Stlc.html#3735" class="InductiveConstructor"
      >true</a
      ><a name="25145"
      > </a
      ><a name="25146" href="Stlc.html#3708" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="25147"
      > </a
      ><a name="25148" href="Stlc.html#3749" class="InductiveConstructor"
      >false</a
      ><a name="25153"
      > </a
      ><a name="25154" href="Stlc.html#21569" class="Datatype Operator"
      >&#8758;</a
      ><a name="25155"
      > </a
      ><a name="25156" href="Stlc.html#25129" class="Bound"
      >A</a
      ><a name="25157" class="Symbol"
      >)</a
      ><a name="25158"
      >
</a
      ><a name="25159" href="Stlc.html#25114" class="Function"
      >notyping&#8322;</a
      ><a name="25168"
      > </a
      ><a name="25169" class="Symbol"
      >(</a
      ><a name="25170" href="Stlc.html#21744" class="InductiveConstructor"
      >&#8658;-E</a
      ><a name="25173"
      > </a
      ><a name="25174" class="Symbol"
      >()</a
      ><a name="25176"
      > </a
      ><a name="25177" class="Symbol"
      >_)</a
      >

</pre>

As a second example, here is a formal proof that it is not possible to
type `` λ[ x ∶ 𝔹 ] λ[ y ∶ 𝔹 ] ` x · ` y `` It cannot be typed, because
doing so requires `x` to be both boolean and a function.

<pre class="Agda">

<a name="25405" href="Stlc.html#25405" class="Function"
      >contradiction</a
      ><a name="25418"
      > </a
      ><a name="25419" class="Symbol"
      >:</a
      ><a name="25420"
      > </a
      ><a name="25421" class="Symbol"
      >&#8704;</a
      ><a name="25422"
      > </a
      ><a name="25423" class="Symbol"
      >{</a
      ><a name="25424" href="Stlc.html#25424" class="Bound"
      >A</a
      ><a name="25425"
      > </a
      ><a name="25426" href="Stlc.html#25426" class="Bound"
      >B</a
      ><a name="25427" class="Symbol"
      >}</a
      ><a name="25428"
      > </a
      ><a name="25429" class="Symbol"
      >&#8594;</a
      ><a name="25430"
      > </a
      ><a name="25431" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#414" class="Function Operator"
      >&#172;</a
      ><a name="25432"
      > </a
      ><a name="25433" class="Symbol"
      >(</a
      ><a name="25434" href="Stlc.html#2610" class="InductiveConstructor"
      >&#120121;</a
      ><a name="25435"
      > </a
      ><a name="25436" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="25437"
      > </a
      ><a name="25438" href="Stlc.html#25424" class="Bound"
      >A</a
      ><a name="25439"
      > </a
      ><a name="25440" href="Stlc.html#2583" class="InductiveConstructor Operator"
      >&#8658;</a
      ><a name="25441"
      > </a
      ><a name="25442" href="Stlc.html#25426" class="Bound"
      >B</a
      ><a name="25443" class="Symbol"
      >)</a
      ><a name="25444"
      >
</a
      ><a name="25445" href="Stlc.html#25405" class="Function"
      >contradiction</a
      ><a name="25458"
      > </a
      ><a name="25459" class="Symbol"
      >()</a
      ><a name="25461"
      >

</a
      ><a name="25463" href="Stlc.html#25463" class="Function"
      >notyping&#8321;</a
      ><a name="25472"
      > </a
      ><a name="25473" class="Symbol"
      >:</a
      ><a name="25474"
      > </a
      ><a name="25475" class="Symbol"
      >&#8704;</a
      ><a name="25476"
      > </a
      ><a name="25477" class="Symbol"
      >{</a
      ><a name="25478" href="Stlc.html#25478" class="Bound"
      >A</a
      ><a name="25479" class="Symbol"
      >}</a
      ><a name="25480"
      > </a
      ><a name="25481" class="Symbol"
      >&#8594;</a
      ><a name="25482"
      > </a
      ><a name="25483" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#414" class="Function Operator"
      >&#172;</a
      ><a name="25484"
      > </a
      ><a name="25485" class="Symbol"
      >(</a
      ><a name="25486" href="Maps.html#10265" class="Function"
      >&#8709;</a
      ><a name="25487"
      > </a
      ><a name="25488" href="Stlc.html#21569" class="Datatype Operator"
      >&#8866;</a
      ><a name="25489"
      > </a
      ><a name="25490" href="Stlc.html#3672" class="InductiveConstructor Operator"
      >&#955;[</a
      ><a name="25492"
      > </a
      ><a name="25493" href="Stlc.html#5680" class="Function"
      >x</a
      ><a name="25494"
      > </a
      ><a name="25495" href="Stlc.html#3672" class="InductiveConstructor Operator"
      >&#8758;</a
      ><a name="25496"
      > </a
      ><a name="25497" href="Stlc.html#2610" class="InductiveConstructor"
      >&#120121;</a
      ><a name="25498"
      > </a
      ><a name="25499" href="Stlc.html#3672" class="InductiveConstructor Operator"
      >]</a
      ><a name="25500"
      > </a
      ><a name="25501" href="Stlc.html#3672" class="InductiveConstructor Operator"
      >&#955;[</a
      ><a name="25503"
      > </a
      ><a name="25504" href="Stlc.html#5682" class="Function"
      >y</a
      ><a name="25505"
      > </a
      ><a name="25506" href="Stlc.html#3672" class="InductiveConstructor Operator"
      >&#8758;</a
      ><a name="25507"
      > </a
      ><a name="25508" href="Stlc.html#2610" class="InductiveConstructor"
      >&#120121;</a
      ><a name="25509"
      > </a
      ><a name="25510" href="Stlc.html#3672" class="InductiveConstructor Operator"
      >]</a
      ><a name="25511"
      > </a
      ><a name="25512" href="Stlc.html#3656" class="InductiveConstructor"
      >`</a
      ><a name="25513"
      > </a
      ><a name="25514" href="Stlc.html#5680" class="Function"
      >x</a
      ><a name="25515"
      > </a
      ><a name="25516" href="Stlc.html#3708" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="25517"
      > </a
      ><a name="25518" href="Stlc.html#3656" class="InductiveConstructor"
      >`</a
      ><a name="25519"
      > </a
      ><a name="25520" href="Stlc.html#5682" class="Function"
      >y</a
      ><a name="25521"
      > </a
      ><a name="25522" href="Stlc.html#21569" class="Datatype Operator"
      >&#8758;</a
      ><a name="25523"
      > </a
      ><a name="25524" href="Stlc.html#25478" class="Bound"
      >A</a
      ><a name="25525" class="Symbol"
      >)</a
      ><a name="25526"
      >
</a
      ><a name="25527" href="Stlc.html#25463" class="Function"
      >notyping&#8321;</a
      ><a name="25536"
      > </a
      ><a name="25537" class="Symbol"
      >(</a
      ><a name="25538" href="Stlc.html#21667" class="InductiveConstructor"
      >&#8658;-I</a
      ><a name="25541"
      > </a
      ><a name="25542" class="Symbol"
      >(</a
      ><a name="25543" href="Stlc.html#21667" class="InductiveConstructor"
      >&#8658;-I</a
      ><a name="25546"
      > </a
      ><a name="25547" class="Symbol"
      >(</a
      ><a name="25548" href="Stlc.html#21744" class="InductiveConstructor"
      >&#8658;-E</a
      ><a name="25551"
      > </a
      ><a name="25552" class="Symbol"
      >(</a
      ><a name="25553" href="Stlc.html#21613" class="InductiveConstructor"
      >Ax</a
      ><a name="25555"
      > </a
      ><a name="25556" href="Stlc.html#25556" class="Bound"
      >&#915;x</a
      ><a name="25558" class="Symbol"
      >)</a
      ><a name="25559"
      > </a
      ><a name="25560" class="Symbol"
      >_)))</a
      ><a name="25564"
      > </a
      ><a name="25565" class="Symbol"
      >=</a
      ><a name="25566"
      >  </a
      ><a name="25568" href="Stlc.html#25405" class="Function"
      >contradiction</a
      ><a name="25581"
      > </a
      ><a name="25582" class="Symbol"
      >(</a
      ><a name="25583" href="Maps.html#11919" class="Function"
      >just-injective</a
      ><a name="25597"
      > </a
      ><a name="25598" href="Stlc.html#25556" class="Bound"
      >&#915;x</a
      ><a name="25600" class="Symbol"
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



