---
title     : "Stlc: The Simply Typed Lambda-Calculus"
layout    : page
permalink : /Stlc
---

The _lambda-calculus_, first published by the logician Alonzo Church in
1932, is a core calculus with only three syntactic constructs:
variables, abstraction, and application.  It embodies the concept of
_functional abstraction_, which shows up in almsot every programming
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

We've already seen how to formalize a language with
variables ([Imp]({{ "Imp" | relative_url }})).
There, however, the variables were all global.
In the STLC, we need to handle the variables that name the
parameters to functions, and these are _bound_ variables.
Moreover, instead of just looking up variables in a global store,
we'll need to reduce function applications by _substituting_
arguments for parameters in function bodies.

We choose booleans as our base type for simplicity.  At the end of the
chapter we'll see how to add numbers as a base type, and in later
chapters we'll enrich STLC with useful constructs like pairs, sums,
lists, records, subtyping, and mutable state.

## Imports

<pre class="Agda">

<a name="1747" class="Keyword"
      >open</a
      ><a name="1751"
      > </a
      ><a name="1752" class="Keyword"
      >import</a
      ><a name="1758"
      > </a
      ><a name="1759" class="Module"
      >Maps</a
      ><a name="1763"
      > </a
      ><a name="1764" class="Keyword"
      >using</a
      ><a name="1769"
      > </a
      ><a name="1770" class="Symbol"
      >(</a
      ><a name="1771" href="Maps.html#2171" class="Datatype"
      >Id</a
      ><a name="1773" class="Symbol"
      >;</a
      ><a name="1774"
      > </a
      ><a name="1775" href="Maps.html#2188" class="InductiveConstructor"
      >id</a
      ><a name="1777" class="Symbol"
      >;</a
      ><a name="1778"
      > </a
      ><a name="1779" href="Maps.html#2509" class="Function Operator"
      >_&#8799;_</a
      ><a name="1782" class="Symbol"
      >;</a
      ><a name="1783"
      > </a
      ><a name="1784" href="Maps.html#10132" class="Function"
      >PartialMap</a
      ><a name="1794" class="Symbol"
      >;</a
      ><a name="1795"
      > </a
      ><a name="1796" class="Keyword"
      >module</a
      ><a name="1802"
      > </a
      ><a name="1803" href="Maps.html#10221" class="Module"
      >PartialMap</a
      ><a name="1813" class="Symbol"
      >)</a
      ><a name="1814"
      >
</a
      ><a name="1815" class="Keyword"
      >open</a
      ><a name="1819"
      > </a
      ><a name="1820" href="Maps.html#10221" class="Module"
      >PartialMap</a
      ><a name="1830"
      > </a
      ><a name="1831" class="Keyword"
      >using</a
      ><a name="1836"
      > </a
      ><a name="1837" class="Symbol"
      >(</a
      ><a name="1838" href="Maps.html#10265" class="Function"
      >&#8709;</a
      ><a name="1839" class="Symbol"
      >)</a
      ><a name="1840"
      > </a
      ><a name="1841" class="Keyword"
      >renaming</a
      ><a name="1849"
      > </a
      ><a name="1850" class="Symbol"
      >(</a
      ><a name="1851" href="Maps.html#10368" class="Function Operator"
      >_,_&#8614;_</a
      ><a name="1856"
      > </a
      ><a name="1857" class="Symbol"
      >to</a
      ><a name="1859"
      > </a
      ><a name="1860" href="Maps.html#10368" class="Function Operator"
      >_,_&#8758;_</a
      ><a name="1865" class="Symbol"
      >)</a
      ><a name="1866"
      >
</a
      ><a name="1867" class="Keyword"
      >open</a
      ><a name="1871"
      > </a
      ><a name="1872" class="Keyword"
      >import</a
      ><a name="1878"
      > </a
      ><a name="1879" href="https://agda.github.io/agda-stdlib/Data.Nat.html#1" class="Module"
      >Data.Nat</a
      ><a name="1887"
      > </a
      ><a name="1888" class="Keyword"
      >using</a
      ><a name="1893"
      > </a
      ><a name="1894" class="Symbol"
      >(</a
      ><a name="1895" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#97" class="Datatype"
      >&#8469;</a
      ><a name="1896" class="Symbol"
      >)</a
      ><a name="1897"
      >
</a
      ><a name="1898" class="Keyword"
      >open</a
      ><a name="1902"
      > </a
      ><a name="1903" class="Keyword"
      >import</a
      ><a name="1909"
      > </a
      ><a name="1910" href="https://agda.github.io/agda-stdlib/Data.Maybe.html#1" class="Module"
      >Data.Maybe</a
      ><a name="1920"
      > </a
      ><a name="1921" class="Keyword"
      >using</a
      ><a name="1926"
      > </a
      ><a name="1927" class="Symbol"
      >(</a
      ><a name="1928" href="https://agda.github.io/agda-stdlib/Data.Maybe.Base.html#335" class="Datatype"
      >Maybe</a
      ><a name="1933" class="Symbol"
      >;</a
      ><a name="1934"
      > </a
      ><a name="1935" href="https://agda.github.io/agda-stdlib/Data.Maybe.html#1527" class="InductiveConstructor"
      >just</a
      ><a name="1939" class="Symbol"
      >;</a
      ><a name="1940"
      > </a
      ><a name="1941" href="https://agda.github.io/agda-stdlib/Data.Maybe.html#1588" class="InductiveConstructor"
      >nothing</a
      ><a name="1948" class="Symbol"
      >)</a
      ><a name="1949"
      >
</a
      ><a name="1950" class="Keyword"
      >open</a
      ><a name="1954"
      > </a
      ><a name="1955" class="Keyword"
      >import</a
      ><a name="1961"
      > </a
      ><a name="1962" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#1" class="Module"
      >Relation.Nullary</a
      ><a name="1978"
      > </a
      ><a name="1979" class="Keyword"
      >using</a
      ><a name="1984"
      > </a
      ><a name="1985" class="Symbol"
      >(</a
      ><a name="1986" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#484" class="Datatype"
      >Dec</a
      ><a name="1989" class="Symbol"
      >;</a
      ><a name="1990"
      > </a
      ><a name="1991" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#520" class="InductiveConstructor"
      >yes</a
      ><a name="1994" class="Symbol"
      >;</a
      ><a name="1995"
      > </a
      ><a name="1996" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#547" class="InductiveConstructor"
      >no</a
      ><a name="1998" class="Symbol"
      >)</a
      ><a name="1999"
      >
</a
      ><a name="2000" class="Keyword"
      >open</a
      ><a name="2004"
      > </a
      ><a name="2005" class="Keyword"
      >import</a
      ><a name="2011"
      > </a
      ><a name="2012" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#1" class="Module"
      >Relation.Binary.PropositionalEquality</a
      ><a name="2049"
      > </a
      ><a name="2050" class="Keyword"
      >using</a
      ><a name="2055"
      > </a
      ><a name="2056" class="Symbol"
      >(</a
      ><a name="2057" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >_&#8801;_</a
      ><a name="2060" class="Symbol"
      >;</a
      ><a name="2061"
      > </a
      ><a name="2062" href="https://agda.github.io/agda-stdlib/Relation.Binary.Core.html#4493" class="Function Operator"
      >_&#8802;_</a
      ><a name="2065" class="Symbol"
      >;</a
      ><a name="2066"
      > </a
      ><a name="2067" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="2071" class="Symbol"
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

<a name="2515" class="Keyword"
      >infixr</a
      ><a name="2521"
      > </a
      ><a name="2522" class="Number"
      >20</a
      ><a name="2524"
      > </a
      ><a name="2525" href="Stlc.html#2554" class="InductiveConstructor Operator"
      >_&#8658;_</a
      ><a name="2528"
      >

</a
      ><a name="2530" class="Keyword"
      >data</a
      ><a name="2534"
      > </a
      ><a name="2535" href="Stlc.html#2535" class="Datatype"
      >Type</a
      ><a name="2539"
      > </a
      ><a name="2540" class="Symbol"
      >:</a
      ><a name="2541"
      > </a
      ><a name="2542" class="PrimitiveType"
      >Set</a
      ><a name="2545"
      > </a
      ><a name="2546" class="Keyword"
      >where</a
      ><a name="2551"
      >
  </a
      ><a name="2554" href="Stlc.html#2554" class="InductiveConstructor Operator"
      >_&#8658;_</a
      ><a name="2557"
      > </a
      ><a name="2558" class="Symbol"
      >:</a
      ><a name="2559"
      > </a
      ><a name="2560" href="Stlc.html#2535" class="Datatype"
      >Type</a
      ><a name="2564"
      > </a
      ><a name="2565" class="Symbol"
      >&#8594;</a
      ><a name="2566"
      > </a
      ><a name="2567" href="Stlc.html#2535" class="Datatype"
      >Type</a
      ><a name="2571"
      > </a
      ><a name="2572" class="Symbol"
      >&#8594;</a
      ><a name="2573"
      > </a
      ><a name="2574" href="Stlc.html#2535" class="Datatype"
      >Type</a
      ><a name="2578"
      >
  </a
      ><a name="2581" href="Stlc.html#2581" class="InductiveConstructor"
      >&#120121;</a
      ><a name="2582"
      > </a
      ><a name="2583" class="Symbol"
      >:</a
      ><a name="2584"
      > </a
      ><a name="2585" href="Stlc.html#2535" class="Datatype"
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

With the exception of variables, each construct either constructs
a value of a given type (abstractions yield functions, true and
false yield booleans) or deconstructs it (applications use functions,
conditionals use booleans). We will see this again when we come
to the rules for assigning types to terms, where constructors
correspond to introduction rules and deconstructors to eliminators.

Here is the syntax of terms in BNF.

    L, M, N  ::=  ` x | λ[ x ∶ A ] N | L · M | true | false | if L then M else N

And here it is formalised in Agda.

<pre class="Agda">

<a name="3546" class="Keyword"
      >infixl</a
      ><a name="3552"
      > </a
      ><a name="3553" class="Number"
      >20</a
      ><a name="3555"
      > </a
      ><a name="3556" href="Stlc.html#3679" class="InductiveConstructor Operator"
      >_&#183;_</a
      ><a name="3559"
      >
</a
      ><a name="3560" class="Keyword"
      >infix</a
      ><a name="3565"
      >  </a
      ><a name="3567" class="Number"
      >15</a
      ><a name="3569"
      > </a
      ><a name="3570" href="Stlc.html#3643" class="InductiveConstructor Operator"
      >&#955;[_&#8758;_]_</a
      ><a name="3577"
      >
</a
      ><a name="3578" class="Keyword"
      >infix</a
      ><a name="3583"
      >  </a
      ><a name="3585" class="Number"
      >15</a
      ><a name="3587"
      > </a
      ><a name="3588" href="Stlc.html#3735" class="InductiveConstructor Operator"
      >if_then_else_</a
      ><a name="3601"
      >

</a
      ><a name="3603" class="Keyword"
      >data</a
      ><a name="3607"
      > </a
      ><a name="3608" href="Stlc.html#3608" class="Datatype"
      >Term</a
      ><a name="3612"
      > </a
      ><a name="3613" class="Symbol"
      >:</a
      ><a name="3614"
      > </a
      ><a name="3615" class="PrimitiveType"
      >Set</a
      ><a name="3618"
      > </a
      ><a name="3619" class="Keyword"
      >where</a
      ><a name="3624"
      >
  </a
      ><a name="3627" href="Stlc.html#3627" class="InductiveConstructor"
      >`</a
      ><a name="3628"
      > </a
      ><a name="3629" class="Symbol"
      >:</a
      ><a name="3630"
      > </a
      ><a name="3631" href="Maps.html#2171" class="Datatype"
      >Id</a
      ><a name="3633"
      > </a
      ><a name="3634" class="Symbol"
      >&#8594;</a
      ><a name="3635"
      > </a
      ><a name="3636" href="Stlc.html#3608" class="Datatype"
      >Term</a
      ><a name="3640"
      >
  </a
      ><a name="3643" href="Stlc.html#3643" class="InductiveConstructor Operator"
      >&#955;[_&#8758;_]_</a
      ><a name="3650"
      > </a
      ><a name="3651" class="Symbol"
      >:</a
      ><a name="3652"
      > </a
      ><a name="3653" href="Maps.html#2171" class="Datatype"
      >Id</a
      ><a name="3655"
      > </a
      ><a name="3656" class="Symbol"
      >&#8594;</a
      ><a name="3657"
      > </a
      ><a name="3658" href="Stlc.html#2535" class="Datatype"
      >Type</a
      ><a name="3662"
      > </a
      ><a name="3663" class="Symbol"
      >&#8594;</a
      ><a name="3664"
      > </a
      ><a name="3665" href="Stlc.html#3608" class="Datatype"
      >Term</a
      ><a name="3669"
      > </a
      ><a name="3670" class="Symbol"
      >&#8594;</a
      ><a name="3671"
      > </a
      ><a name="3672" href="Stlc.html#3608" class="Datatype"
      >Term</a
      ><a name="3676"
      >
  </a
      ><a name="3679" href="Stlc.html#3679" class="InductiveConstructor Operator"
      >_&#183;_</a
      ><a name="3682"
      > </a
      ><a name="3683" class="Symbol"
      >:</a
      ><a name="3684"
      > </a
      ><a name="3685" href="Stlc.html#3608" class="Datatype"
      >Term</a
      ><a name="3689"
      > </a
      ><a name="3690" class="Symbol"
      >&#8594;</a
      ><a name="3691"
      > </a
      ><a name="3692" href="Stlc.html#3608" class="Datatype"
      >Term</a
      ><a name="3696"
      > </a
      ><a name="3697" class="Symbol"
      >&#8594;</a
      ><a name="3698"
      > </a
      ><a name="3699" href="Stlc.html#3608" class="Datatype"
      >Term</a
      ><a name="3703"
      >
  </a
      ><a name="3706" href="Stlc.html#3706" class="InductiveConstructor"
      >true</a
      ><a name="3710"
      > </a
      ><a name="3711" class="Symbol"
      >:</a
      ><a name="3712"
      > </a
      ><a name="3713" href="Stlc.html#3608" class="Datatype"
      >Term</a
      ><a name="3717"
      >
  </a
      ><a name="3720" href="Stlc.html#3720" class="InductiveConstructor"
      >false</a
      ><a name="3725"
      > </a
      ><a name="3726" class="Symbol"
      >:</a
      ><a name="3727"
      > </a
      ><a name="3728" href="Stlc.html#3608" class="Datatype"
      >Term</a
      ><a name="3732"
      >
  </a
      ><a name="3735" href="Stlc.html#3735" class="InductiveConstructor Operator"
      >if_then_else_</a
      ><a name="3748"
      > </a
      ><a name="3749" class="Symbol"
      >:</a
      ><a name="3750"
      > </a
      ><a name="3751" href="Stlc.html#3608" class="Datatype"
      >Term</a
      ><a name="3755"
      > </a
      ><a name="3756" class="Symbol"
      >&#8594;</a
      ><a name="3757"
      > </a
      ><a name="3758" href="Stlc.html#3608" class="Datatype"
      >Term</a
      ><a name="3762"
      > </a
      ><a name="3763" class="Symbol"
      >&#8594;</a
      ><a name="3764"
      > </a
      ><a name="3765" href="Stlc.html#3608" class="Datatype"
      >Term</a
      ><a name="3769"
      > </a
      ><a name="3770" class="Symbol"
      >&#8594;</a
      ><a name="3771"
      > </a
      ><a name="3772" href="Stlc.html#3608" class="Datatype"
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

<a name="5639" href="Stlc.html#5639" class="Function"
      >f</a
      ><a name="5640"
      > </a
      ><a name="5641" href="Stlc.html#5641" class="Function"
      >x</a
      ><a name="5642"
      > </a
      ><a name="5643" href="Stlc.html#5643" class="Function"
      >y</a
      ><a name="5644"
      > </a
      ><a name="5645" class="Symbol"
      >:</a
      ><a name="5646"
      > </a
      ><a name="5647" href="Maps.html#2171" class="Datatype"
      >Id</a
      ><a name="5649"
      >
</a
      ><a name="5650" href="Stlc.html#5639" class="Function"
      >f</a
      ><a name="5651"
      >  </a
      ><a name="5653" class="Symbol"
      >=</a
      ><a name="5654"
      >  </a
      ><a name="5656" href="Maps.html#2188" class="InductiveConstructor"
      >id</a
      ><a name="5658"
      > </a
      ><a name="5659" class="Number"
      >0</a
      ><a name="5660"
      >
</a
      ><a name="5661" href="Stlc.html#5641" class="Function"
      >x</a
      ><a name="5662"
      >  </a
      ><a name="5664" class="Symbol"
      >=</a
      ><a name="5665"
      >  </a
      ><a name="5667" href="Maps.html#2188" class="InductiveConstructor"
      >id</a
      ><a name="5669"
      > </a
      ><a name="5670" class="Number"
      >1</a
      ><a name="5671"
      >
</a
      ><a name="5672" href="Stlc.html#5643" class="Function"
      >y</a
      ><a name="5673"
      >  </a
      ><a name="5675" class="Symbol"
      >=</a
      ><a name="5676"
      >  </a
      ><a name="5678" href="Maps.html#2188" class="InductiveConstructor"
      >id</a
      ><a name="5680"
      > </a
      ><a name="5681" class="Number"
      >2</a
      ><a name="5682"
      >

</a
      ><a name="5684" href="Stlc.html#5684" class="Function"
      >not</a
      ><a name="5687"
      > </a
      ><a name="5688" href="Stlc.html#5688" class="Function"
      >two</a
      ><a name="5691"
      > </a
      ><a name="5692" class="Symbol"
      >:</a
      ><a name="5693"
      > </a
      ><a name="5694" href="Stlc.html#3608" class="Datatype"
      >Term</a
      ><a name="5698"
      > 
</a
      ><a name="5700" href="Stlc.html#5684" class="Function"
      >not</a
      ><a name="5703"
      > </a
      ><a name="5704" class="Symbol"
      >=</a
      ><a name="5705"
      >  </a
      ><a name="5707" href="Stlc.html#3643" class="InductiveConstructor Operator"
      >&#955;[</a
      ><a name="5709"
      > </a
      ><a name="5710" href="Stlc.html#5641" class="Function"
      >x</a
      ><a name="5711"
      > </a
      ><a name="5712" href="Stlc.html#3643" class="InductiveConstructor Operator"
      >&#8758;</a
      ><a name="5713"
      > </a
      ><a name="5714" href="Stlc.html#2581" class="InductiveConstructor"
      >&#120121;</a
      ><a name="5715"
      > </a
      ><a name="5716" href="Stlc.html#3643" class="InductiveConstructor Operator"
      >]</a
      ><a name="5717"
      > </a
      ><a name="5718" class="Symbol"
      >(</a
      ><a name="5719" href="Stlc.html#3735" class="InductiveConstructor Operator"
      >if</a
      ><a name="5721"
      > </a
      ><a name="5722" href="Stlc.html#3627" class="InductiveConstructor"
      >`</a
      ><a name="5723"
      > </a
      ><a name="5724" href="Stlc.html#5641" class="Function"
      >x</a
      ><a name="5725"
      > </a
      ><a name="5726" href="Stlc.html#3735" class="InductiveConstructor Operator"
      >then</a
      ><a name="5730"
      > </a
      ><a name="5731" href="Stlc.html#3720" class="InductiveConstructor"
      >false</a
      ><a name="5736"
      > </a
      ><a name="5737" href="Stlc.html#3735" class="InductiveConstructor Operator"
      >else</a
      ><a name="5741"
      > </a
      ><a name="5742" href="Stlc.html#3706" class="InductiveConstructor"
      >true</a
      ><a name="5746" class="Symbol"
      >)</a
      ><a name="5747"
      >
</a
      ><a name="5748" href="Stlc.html#5688" class="Function"
      >two</a
      ><a name="5751"
      > </a
      ><a name="5752" class="Symbol"
      >=</a
      ><a name="5753"
      >  </a
      ><a name="5755" href="Stlc.html#3643" class="InductiveConstructor Operator"
      >&#955;[</a
      ><a name="5757"
      > </a
      ><a name="5758" href="Stlc.html#5639" class="Function"
      >f</a
      ><a name="5759"
      > </a
      ><a name="5760" href="Stlc.html#3643" class="InductiveConstructor Operator"
      >&#8758;</a
      ><a name="5761"
      > </a
      ><a name="5762" href="Stlc.html#2581" class="InductiveConstructor"
      >&#120121;</a
      ><a name="5763"
      > </a
      ><a name="5764" href="Stlc.html#2554" class="InductiveConstructor Operator"
      >&#8658;</a
      ><a name="5765"
      > </a
      ><a name="5766" href="Stlc.html#2581" class="InductiveConstructor"
      >&#120121;</a
      ><a name="5767"
      > </a
      ><a name="5768" href="Stlc.html#3643" class="InductiveConstructor Operator"
      >]</a
      ><a name="5769"
      > </a
      ><a name="5770" href="Stlc.html#3643" class="InductiveConstructor Operator"
      >&#955;[</a
      ><a name="5772"
      > </a
      ><a name="5773" href="Stlc.html#5641" class="Function"
      >x</a
      ><a name="5774"
      > </a
      ><a name="5775" href="Stlc.html#3643" class="InductiveConstructor Operator"
      >&#8758;</a
      ><a name="5776"
      > </a
      ><a name="5777" href="Stlc.html#2581" class="InductiveConstructor"
      >&#120121;</a
      ><a name="5778"
      > </a
      ><a name="5779" href="Stlc.html#3643" class="InductiveConstructor Operator"
      >]</a
      ><a name="5780"
      > </a
      ><a name="5781" href="Stlc.html#3627" class="InductiveConstructor"
      >`</a
      ><a name="5782"
      > </a
      ><a name="5783" href="Stlc.html#5639" class="Function"
      >f</a
      ><a name="5784"
      > </a
      ><a name="5785" href="Stlc.html#3679" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="5786"
      > </a
      ><a name="5787" class="Symbol"
      >(</a
      ><a name="5788" href="Stlc.html#3627" class="InductiveConstructor"
      >`</a
      ><a name="5789"
      > </a
      ><a name="5790" href="Stlc.html#5639" class="Function"
      >f</a
      ><a name="5791"
      > </a
      ><a name="5792" href="Stlc.html#3679" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="5793"
      > </a
      ><a name="5794" href="Stlc.html#3627" class="InductiveConstructor"
      >`</a
      ><a name="5795"
      > </a
      ><a name="5796" href="Stlc.html#5641" class="Function"
      >x</a
      ><a name="5797" class="Symbol"
      >)</a
      >

</pre>


#### Bound and free variables

In an abstraction `λ[ x ∶ A ] N` we call `x` the _bound_ variable
and `N` the _body_ of the abstraction.  One of the most important
aspects of lambda calculus is that names of bound variables are
irrelevant.  Thus the two terms

    λ[ f ∶ 𝔹 ⇒ 𝔹 ] λ[ x ∶ 𝔹 ] ` f · (` f · ` x)

and

    λ[ g ∶ 𝔹 ⇒ 𝔹 ] λ[ y ∶ 𝔹 ] ` g · (` g · ` y)

and 

    λ[ fred ∶ 𝔹 ⇒ 𝔹 ] λ[ xander ∶ 𝔹 ] ` fred · (` fred · ` xander)

and even

    λ[ x ∶ 𝔹 ⇒ 𝔹 ] λ[ f ∶ 𝔹 ] ` x · (` x · ` f)

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

> `(𝔹 ⇒ 𝔹) ⇒ 𝔹 ⇒ 𝔹` abbreviates `(𝔹 ⇒ 𝔹) ⇒ (𝔹 ⇒ 𝔹)`,

and similarly,

> `two · not · true` abbreviates `(two · not) · true`.

We choose the binding strength for abstractions and conditionals
to be weaker than application. For instance,

> `` λ[ f ∶ 𝔹 ⇒ 𝔹 ] λ[ x ∶ 𝔹 ] ` f · (` f · ` x) `` abbreviates
> `` (λ[ f ∶ 𝔹 ⇒ 𝔹 ] (λ[ x ∶ 𝔹 ] (` f · (` f · ` x)))) `` and not
> `` (λ[ f ∶ 𝔹 ⇒ 𝔹 ] (λ[ x ∶ 𝔹 ] ` f)) · (` f · ` x) ``.

<pre class="Agda">

<a name="8231" href="Stlc.html#8231" class="Function"
      >ex&#8321;</a
      ><a name="8234"
      > </a
      ><a name="8235" class="Symbol"
      >:</a
      ><a name="8236"
      > </a
      ><a name="8237" class="Symbol"
      >(</a
      ><a name="8238" href="Stlc.html#2581" class="InductiveConstructor"
      >&#120121;</a
      ><a name="8239"
      > </a
      ><a name="8240" href="Stlc.html#2554" class="InductiveConstructor Operator"
      >&#8658;</a
      ><a name="8241"
      > </a
      ><a name="8242" href="Stlc.html#2581" class="InductiveConstructor"
      >&#120121;</a
      ><a name="8243" class="Symbol"
      >)</a
      ><a name="8244"
      > </a
      ><a name="8245" href="Stlc.html#2554" class="InductiveConstructor Operator"
      >&#8658;</a
      ><a name="8246"
      > </a
      ><a name="8247" href="Stlc.html#2581" class="InductiveConstructor"
      >&#120121;</a
      ><a name="8248"
      > </a
      ><a name="8249" href="Stlc.html#2554" class="InductiveConstructor Operator"
      >&#8658;</a
      ><a name="8250"
      > </a
      ><a name="8251" href="Stlc.html#2581" class="InductiveConstructor"
      >&#120121;</a
      ><a name="8252"
      > </a
      ><a name="8253" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="8254"
      > </a
      ><a name="8255" class="Symbol"
      >(</a
      ><a name="8256" href="Stlc.html#2581" class="InductiveConstructor"
      >&#120121;</a
      ><a name="8257"
      > </a
      ><a name="8258" href="Stlc.html#2554" class="InductiveConstructor Operator"
      >&#8658;</a
      ><a name="8259"
      > </a
      ><a name="8260" href="Stlc.html#2581" class="InductiveConstructor"
      >&#120121;</a
      ><a name="8261" class="Symbol"
      >)</a
      ><a name="8262"
      > </a
      ><a name="8263" href="Stlc.html#2554" class="InductiveConstructor Operator"
      >&#8658;</a
      ><a name="8264"
      > </a
      ><a name="8265" class="Symbol"
      >(</a
      ><a name="8266" href="Stlc.html#2581" class="InductiveConstructor"
      >&#120121;</a
      ><a name="8267"
      > </a
      ><a name="8268" href="Stlc.html#2554" class="InductiveConstructor Operator"
      >&#8658;</a
      ><a name="8269"
      > </a
      ><a name="8270" href="Stlc.html#2581" class="InductiveConstructor"
      >&#120121;</a
      ><a name="8271" class="Symbol"
      >)</a
      ><a name="8272"
      >
</a
      ><a name="8273" href="Stlc.html#8231" class="Function"
      >ex&#8321;</a
      ><a name="8276"
      > </a
      ><a name="8277" class="Symbol"
      >=</a
      ><a name="8278"
      > </a
      ><a name="8279" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="8283"
      >

</a
      ><a name="8285" href="Stlc.html#8285" class="Function"
      >ex&#8322;</a
      ><a name="8288"
      > </a
      ><a name="8289" class="Symbol"
      >:</a
      ><a name="8290"
      > </a
      ><a name="8291" href="Stlc.html#5688" class="Function"
      >two</a
      ><a name="8294"
      > </a
      ><a name="8295" href="Stlc.html#3679" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="8296"
      > </a
      ><a name="8297" href="Stlc.html#5684" class="Function"
      >not</a
      ><a name="8300"
      > </a
      ><a name="8301" href="Stlc.html#3679" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="8302"
      > </a
      ><a name="8303" href="Stlc.html#3706" class="InductiveConstructor"
      >true</a
      ><a name="8307"
      > </a
      ><a name="8308" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="8309"
      > </a
      ><a name="8310" class="Symbol"
      >(</a
      ><a name="8311" href="Stlc.html#5688" class="Function"
      >two</a
      ><a name="8314"
      > </a
      ><a name="8315" href="Stlc.html#3679" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="8316"
      > </a
      ><a name="8317" href="Stlc.html#5684" class="Function"
      >not</a
      ><a name="8320" class="Symbol"
      >)</a
      ><a name="8321"
      > </a
      ><a name="8322" href="Stlc.html#3679" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="8323"
      > </a
      ><a name="8324" href="Stlc.html#3706" class="InductiveConstructor"
      >true</a
      ><a name="8328"
      >
</a
      ><a name="8329" href="Stlc.html#8285" class="Function"
      >ex&#8322;</a
      ><a name="8332"
      > </a
      ><a name="8333" class="Symbol"
      >=</a
      ><a name="8334"
      > </a
      ><a name="8335" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="8339"
      >

</a
      ><a name="8341" href="Stlc.html#8341" class="Function"
      >ex&#8323;</a
      ><a name="8344"
      > </a
      ><a name="8345" class="Symbol"
      >:</a
      ><a name="8346"
      > </a
      ><a name="8347" href="Stlc.html#3643" class="InductiveConstructor Operator"
      >&#955;[</a
      ><a name="8349"
      > </a
      ><a name="8350" href="Stlc.html#5639" class="Function"
      >f</a
      ><a name="8351"
      > </a
      ><a name="8352" href="Stlc.html#3643" class="InductiveConstructor Operator"
      >&#8758;</a
      ><a name="8353"
      > </a
      ><a name="8354" href="Stlc.html#2581" class="InductiveConstructor"
      >&#120121;</a
      ><a name="8355"
      > </a
      ><a name="8356" href="Stlc.html#2554" class="InductiveConstructor Operator"
      >&#8658;</a
      ><a name="8357"
      > </a
      ><a name="8358" href="Stlc.html#2581" class="InductiveConstructor"
      >&#120121;</a
      ><a name="8359"
      > </a
      ><a name="8360" href="Stlc.html#3643" class="InductiveConstructor Operator"
      >]</a
      ><a name="8361"
      > </a
      ><a name="8362" href="Stlc.html#3643" class="InductiveConstructor Operator"
      >&#955;[</a
      ><a name="8364"
      > </a
      ><a name="8365" href="Stlc.html#5641" class="Function"
      >x</a
      ><a name="8366"
      > </a
      ><a name="8367" href="Stlc.html#3643" class="InductiveConstructor Operator"
      >&#8758;</a
      ><a name="8368"
      > </a
      ><a name="8369" href="Stlc.html#2581" class="InductiveConstructor"
      >&#120121;</a
      ><a name="8370"
      > </a
      ><a name="8371" href="Stlc.html#3643" class="InductiveConstructor Operator"
      >]</a
      ><a name="8372"
      > </a
      ><a name="8373" href="Stlc.html#3627" class="InductiveConstructor"
      >`</a
      ><a name="8374"
      > </a
      ><a name="8375" href="Stlc.html#5639" class="Function"
      >f</a
      ><a name="8376"
      > </a
      ><a name="8377" href="Stlc.html#3679" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="8378"
      > </a
      ><a name="8379" class="Symbol"
      >(</a
      ><a name="8380" href="Stlc.html#3627" class="InductiveConstructor"
      >`</a
      ><a name="8381"
      > </a
      ><a name="8382" href="Stlc.html#5639" class="Function"
      >f</a
      ><a name="8383"
      > </a
      ><a name="8384" href="Stlc.html#3679" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="8385"
      > </a
      ><a name="8386" href="Stlc.html#3627" class="InductiveConstructor"
      >`</a
      ><a name="8387"
      > </a
      ><a name="8388" href="Stlc.html#5641" class="Function"
      >x</a
      ><a name="8389" class="Symbol"
      >)</a
      ><a name="8390"
      >
      </a
      ><a name="8397" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="8398"
      > </a
      ><a name="8399" class="Symbol"
      >(</a
      ><a name="8400" href="Stlc.html#3643" class="InductiveConstructor Operator"
      >&#955;[</a
      ><a name="8402"
      > </a
      ><a name="8403" href="Stlc.html#5639" class="Function"
      >f</a
      ><a name="8404"
      > </a
      ><a name="8405" href="Stlc.html#3643" class="InductiveConstructor Operator"
      >&#8758;</a
      ><a name="8406"
      > </a
      ><a name="8407" href="Stlc.html#2581" class="InductiveConstructor"
      >&#120121;</a
      ><a name="8408"
      > </a
      ><a name="8409" href="Stlc.html#2554" class="InductiveConstructor Operator"
      >&#8658;</a
      ><a name="8410"
      > </a
      ><a name="8411" href="Stlc.html#2581" class="InductiveConstructor"
      >&#120121;</a
      ><a name="8412"
      > </a
      ><a name="8413" href="Stlc.html#3643" class="InductiveConstructor Operator"
      >]</a
      ><a name="8414"
      > </a
      ><a name="8415" class="Symbol"
      >(</a
      ><a name="8416" href="Stlc.html#3643" class="InductiveConstructor Operator"
      >&#955;[</a
      ><a name="8418"
      > </a
      ><a name="8419" href="Stlc.html#5641" class="Function"
      >x</a
      ><a name="8420"
      > </a
      ><a name="8421" href="Stlc.html#3643" class="InductiveConstructor Operator"
      >&#8758;</a
      ><a name="8422"
      > </a
      ><a name="8423" href="Stlc.html#2581" class="InductiveConstructor"
      >&#120121;</a
      ><a name="8424"
      > </a
      ><a name="8425" href="Stlc.html#3643" class="InductiveConstructor Operator"
      >]</a
      ><a name="8426"
      > </a
      ><a name="8427" class="Symbol"
      >(</a
      ><a name="8428" href="Stlc.html#3627" class="InductiveConstructor"
      >`</a
      ><a name="8429"
      > </a
      ><a name="8430" href="Stlc.html#5639" class="Function"
      >f</a
      ><a name="8431"
      > </a
      ><a name="8432" href="Stlc.html#3679" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="8433"
      > </a
      ><a name="8434" class="Symbol"
      >(</a
      ><a name="8435" href="Stlc.html#3627" class="InductiveConstructor"
      >`</a
      ><a name="8436"
      > </a
      ><a name="8437" href="Stlc.html#5639" class="Function"
      >f</a
      ><a name="8438"
      > </a
      ><a name="8439" href="Stlc.html#3679" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="8440"
      > </a
      ><a name="8441" href="Stlc.html#3627" class="InductiveConstructor"
      >`</a
      ><a name="8442"
      > </a
      ><a name="8443" href="Stlc.html#5641" class="Function"
      >x</a
      ><a name="8444" class="Symbol"
      >))))</a
      ><a name="8448"
      >
</a
      ><a name="8449" href="Stlc.html#8341" class="Function"
      >ex&#8323;</a
      ><a name="8452"
      > </a
      ><a name="8453" class="Symbol"
      >=</a
      ><a name="8454"
      > </a
      ><a name="8455" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
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

<a name="9516" class="Keyword"
      >data</a
      ><a name="9520"
      > </a
      ><a name="9521" href="Stlc.html#9521" class="Datatype"
      >Value</a
      ><a name="9526"
      > </a
      ><a name="9527" class="Symbol"
      >:</a
      ><a name="9528"
      > </a
      ><a name="9529" href="Stlc.html#3608" class="Datatype"
      >Term</a
      ><a name="9533"
      > </a
      ><a name="9534" class="Symbol"
      >&#8594;</a
      ><a name="9535"
      > </a
      ><a name="9536" class="PrimitiveType"
      >Set</a
      ><a name="9539"
      > </a
      ><a name="9540" class="Keyword"
      >where</a
      ><a name="9545"
      >
  </a
      ><a name="9548" href="Stlc.html#9548" class="InductiveConstructor"
      >value-&#955;</a
      ><a name="9555"
      >     </a
      ><a name="9560" class="Symbol"
      >:</a
      ><a name="9561"
      > </a
      ><a name="9562" class="Symbol"
      >&#8704;</a
      ><a name="9563"
      > </a
      ><a name="9564" class="Symbol"
      >{</a
      ><a name="9565" href="Stlc.html#9565" class="Bound"
      >x</a
      ><a name="9566"
      > </a
      ><a name="9567" href="Stlc.html#9567" class="Bound"
      >A</a
      ><a name="9568"
      > </a
      ><a name="9569" href="Stlc.html#9569" class="Bound"
      >N</a
      ><a name="9570" class="Symbol"
      >}</a
      ><a name="9571"
      > </a
      ><a name="9572" class="Symbol"
      >&#8594;</a
      ><a name="9573"
      > </a
      ><a name="9574" href="Stlc.html#9521" class="Datatype"
      >Value</a
      ><a name="9579"
      > </a
      ><a name="9580" class="Symbol"
      >(</a
      ><a name="9581" href="Stlc.html#3643" class="InductiveConstructor Operator"
      >&#955;[</a
      ><a name="9583"
      > </a
      ><a name="9584" href="Stlc.html#9565" class="Bound"
      >x</a
      ><a name="9585"
      > </a
      ><a name="9586" href="Stlc.html#3643" class="InductiveConstructor Operator"
      >&#8758;</a
      ><a name="9587"
      > </a
      ><a name="9588" href="Stlc.html#9567" class="Bound"
      >A</a
      ><a name="9589"
      > </a
      ><a name="9590" href="Stlc.html#3643" class="InductiveConstructor Operator"
      >]</a
      ><a name="9591"
      > </a
      ><a name="9592" href="Stlc.html#9569" class="Bound"
      >N</a
      ><a name="9593" class="Symbol"
      >)</a
      ><a name="9594"
      >
  </a
      ><a name="9597" href="Stlc.html#9597" class="InductiveConstructor"
      >value-true</a
      ><a name="9607"
      >  </a
      ><a name="9609" class="Symbol"
      >:</a
      ><a name="9610"
      > </a
      ><a name="9611" href="Stlc.html#9521" class="Datatype"
      >Value</a
      ><a name="9616"
      > </a
      ><a name="9617" href="Stlc.html#3706" class="InductiveConstructor"
      >true</a
      ><a name="9621"
      >
  </a
      ><a name="9624" href="Stlc.html#9624" class="InductiveConstructor"
      >value-false</a
      ><a name="9635"
      > </a
      ><a name="9636" class="Symbol"
      >:</a
      ><a name="9637"
      > </a
      ><a name="9638" href="Stlc.html#9521" class="Datatype"
      >Value</a
      ><a name="9643"
      > </a
      ><a name="9644" href="Stlc.html#3720" class="InductiveConstructor"
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

<a name="12065" href="Stlc.html#12065" class="Function Operator"
      >_[_:=_]</a
      ><a name="12072"
      > </a
      ><a name="12073" class="Symbol"
      >:</a
      ><a name="12074"
      > </a
      ><a name="12075" href="Stlc.html#3608" class="Datatype"
      >Term</a
      ><a name="12079"
      > </a
      ><a name="12080" class="Symbol"
      >&#8594;</a
      ><a name="12081"
      > </a
      ><a name="12082" href="Maps.html#2171" class="Datatype"
      >Id</a
      ><a name="12084"
      > </a
      ><a name="12085" class="Symbol"
      >&#8594;</a
      ><a name="12086"
      > </a
      ><a name="12087" href="Stlc.html#3608" class="Datatype"
      >Term</a
      ><a name="12091"
      > </a
      ><a name="12092" class="Symbol"
      >&#8594;</a
      ><a name="12093"
      > </a
      ><a name="12094" href="Stlc.html#3608" class="Datatype"
      >Term</a
      ><a name="12098"
      >
</a
      ><a name="12099" class="Symbol"
      >(</a
      ><a name="12100" href="Stlc.html#3627" class="InductiveConstructor"
      >`</a
      ><a name="12101"
      > </a
      ><a name="12102" href="Stlc.html#12102" class="Bound"
      >x&#8242;</a
      ><a name="12104" class="Symbol"
      >)</a
      ><a name="12105"
      > </a
      ><a name="12106" href="Stlc.html#12065" class="Function Operator"
      >[</a
      ><a name="12107"
      > </a
      ><a name="12108" href="Stlc.html#12108" class="Bound"
      >x</a
      ><a name="12109"
      > </a
      ><a name="12110" href="Stlc.html#12065" class="Function Operator"
      >:=</a
      ><a name="12112"
      > </a
      ><a name="12113" href="Stlc.html#12113" class="Bound"
      >V</a
      ><a name="12114"
      > </a
      ><a name="12115" href="Stlc.html#12065" class="Function Operator"
      >]</a
      ><a name="12116"
      > </a
      ><a name="12117" class="Keyword"
      >with</a
      ><a name="12121"
      > </a
      ><a name="12122" href="Stlc.html#12108" class="Bound"
      >x</a
      ><a name="12123"
      > </a
      ><a name="12124" href="Maps.html#2509" class="Function Operator"
      >&#8799;</a
      ><a name="12125"
      > </a
      ><a name="12126" href="Stlc.html#12102" class="Bound"
      >x&#8242;</a
      ><a name="12128"
      >
</a
      ><a name="12129" class="Symbol"
      >...</a
      ><a name="12132"
      > </a
      ><a name="12133" class="Symbol"
      >|</a
      ><a name="12134"
      > </a
      ><a name="12135" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#520" class="InductiveConstructor"
      >yes</a
      ><a name="12138"
      > </a
      ><a name="12139" class="Symbol"
      >_</a
      ><a name="12140"
      > </a
      ><a name="12141" class="Symbol"
      >=</a
      ><a name="12142"
      > </a
      ><a name="12143" href="Stlc.html#12113" class="Bound"
      >V</a
      ><a name="12144"
      >
</a
      ><a name="12145" class="Symbol"
      >...</a
      ><a name="12148"
      > </a
      ><a name="12149" class="Symbol"
      >|</a
      ><a name="12150"
      > </a
      ><a name="12151" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#547" class="InductiveConstructor"
      >no</a
      ><a name="12153"
      >  </a
      ><a name="12155" class="Symbol"
      >_</a
      ><a name="12156"
      > </a
      ><a name="12157" class="Symbol"
      >=</a
      ><a name="12158"
      > </a
      ><a name="12159" href="Stlc.html#3627" class="InductiveConstructor"
      >`</a
      ><a name="12160"
      > </a
      ><a name="12161" href="Stlc.html#12102" class="Bound"
      >x&#8242;</a
      ><a name="12163"
      >
</a
      ><a name="12164" class="Symbol"
      >(</a
      ><a name="12165" href="Stlc.html#3643" class="InductiveConstructor Operator"
      >&#955;[</a
      ><a name="12167"
      > </a
      ><a name="12168" href="Stlc.html#12168" class="Bound"
      >x&#8242;</a
      ><a name="12170"
      > </a
      ><a name="12171" href="Stlc.html#3643" class="InductiveConstructor Operator"
      >&#8758;</a
      ><a name="12172"
      > </a
      ><a name="12173" href="Stlc.html#12173" class="Bound"
      >A&#8242;</a
      ><a name="12175"
      > </a
      ><a name="12176" href="Stlc.html#3643" class="InductiveConstructor Operator"
      >]</a
      ><a name="12177"
      > </a
      ><a name="12178" href="Stlc.html#12178" class="Bound"
      >N&#8242;</a
      ><a name="12180" class="Symbol"
      >)</a
      ><a name="12181"
      > </a
      ><a name="12182" href="Stlc.html#12065" class="Function Operator"
      >[</a
      ><a name="12183"
      > </a
      ><a name="12184" href="Stlc.html#12184" class="Bound"
      >x</a
      ><a name="12185"
      > </a
      ><a name="12186" href="Stlc.html#12065" class="Function Operator"
      >:=</a
      ><a name="12188"
      > </a
      ><a name="12189" href="Stlc.html#12189" class="Bound"
      >V</a
      ><a name="12190"
      > </a
      ><a name="12191" href="Stlc.html#12065" class="Function Operator"
      >]</a
      ><a name="12192"
      > </a
      ><a name="12193" class="Keyword"
      >with</a
      ><a name="12197"
      > </a
      ><a name="12198" href="Stlc.html#12184" class="Bound"
      >x</a
      ><a name="12199"
      > </a
      ><a name="12200" href="Maps.html#2509" class="Function Operator"
      >&#8799;</a
      ><a name="12201"
      > </a
      ><a name="12202" href="Stlc.html#12168" class="Bound"
      >x&#8242;</a
      ><a name="12204"
      >
</a
      ><a name="12205" class="Symbol"
      >...</a
      ><a name="12208"
      > </a
      ><a name="12209" class="Symbol"
      >|</a
      ><a name="12210"
      > </a
      ><a name="12211" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#520" class="InductiveConstructor"
      >yes</a
      ><a name="12214"
      > </a
      ><a name="12215" class="Symbol"
      >_</a
      ><a name="12216"
      > </a
      ><a name="12217" class="Symbol"
      >=</a
      ><a name="12218"
      > </a
      ><a name="12219" href="Stlc.html#3643" class="InductiveConstructor Operator"
      >&#955;[</a
      ><a name="12221"
      > </a
      ><a name="12222" href="Stlc.html#12168" class="Bound"
      >x&#8242;</a
      ><a name="12224"
      > </a
      ><a name="12225" href="Stlc.html#3643" class="InductiveConstructor Operator"
      >&#8758;</a
      ><a name="12226"
      > </a
      ><a name="12227" href="Stlc.html#12173" class="Bound"
      >A&#8242;</a
      ><a name="12229"
      > </a
      ><a name="12230" href="Stlc.html#3643" class="InductiveConstructor Operator"
      >]</a
      ><a name="12231"
      > </a
      ><a name="12232" href="Stlc.html#12178" class="Bound"
      >N&#8242;</a
      ><a name="12234"
      >
</a
      ><a name="12235" class="Symbol"
      >...</a
      ><a name="12238"
      > </a
      ><a name="12239" class="Symbol"
      >|</a
      ><a name="12240"
      > </a
      ><a name="12241" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#547" class="InductiveConstructor"
      >no</a
      ><a name="12243"
      >  </a
      ><a name="12245" class="Symbol"
      >_</a
      ><a name="12246"
      > </a
      ><a name="12247" class="Symbol"
      >=</a
      ><a name="12248"
      > </a
      ><a name="12249" href="Stlc.html#3643" class="InductiveConstructor Operator"
      >&#955;[</a
      ><a name="12251"
      > </a
      ><a name="12252" href="Stlc.html#12168" class="Bound"
      >x&#8242;</a
      ><a name="12254"
      > </a
      ><a name="12255" href="Stlc.html#3643" class="InductiveConstructor Operator"
      >&#8758;</a
      ><a name="12256"
      > </a
      ><a name="12257" href="Stlc.html#12173" class="Bound"
      >A&#8242;</a
      ><a name="12259"
      > </a
      ><a name="12260" href="Stlc.html#3643" class="InductiveConstructor Operator"
      >]</a
      ><a name="12261"
      > </a
      ><a name="12262" class="Symbol"
      >(</a
      ><a name="12263" href="Stlc.html#12178" class="Bound"
      >N&#8242;</a
      ><a name="12265"
      > </a
      ><a name="12266" href="Stlc.html#12065" class="Function Operator"
      >[</a
      ><a name="12267"
      > </a
      ><a name="12268" href="Stlc.html#12184" class="Bound"
      >x</a
      ><a name="12269"
      > </a
      ><a name="12270" href="Stlc.html#12065" class="Function Operator"
      >:=</a
      ><a name="12272"
      > </a
      ><a name="12273" href="Stlc.html#12189" class="Bound"
      >V</a
      ><a name="12274"
      > </a
      ><a name="12275" href="Stlc.html#12065" class="Function Operator"
      >]</a
      ><a name="12276" class="Symbol"
      >)</a
      ><a name="12277"
      >
</a
      ><a name="12278" class="Symbol"
      >(</a
      ><a name="12279" href="Stlc.html#12279" class="Bound"
      >L&#8242;</a
      ><a name="12281"
      > </a
      ><a name="12282" href="Stlc.html#3679" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="12283"
      > </a
      ><a name="12284" href="Stlc.html#12284" class="Bound"
      >M&#8242;</a
      ><a name="12286" class="Symbol"
      >)</a
      ><a name="12287"
      > </a
      ><a name="12288" href="Stlc.html#12065" class="Function Operator"
      >[</a
      ><a name="12289"
      > </a
      ><a name="12290" href="Stlc.html#12290" class="Bound"
      >x</a
      ><a name="12291"
      > </a
      ><a name="12292" href="Stlc.html#12065" class="Function Operator"
      >:=</a
      ><a name="12294"
      > </a
      ><a name="12295" href="Stlc.html#12295" class="Bound"
      >V</a
      ><a name="12296"
      > </a
      ><a name="12297" href="Stlc.html#12065" class="Function Operator"
      >]</a
      ><a name="12298"
      > </a
      ><a name="12299" class="Symbol"
      >=</a
      ><a name="12300"
      >  </a
      ><a name="12302" class="Symbol"
      >(</a
      ><a name="12303" href="Stlc.html#12279" class="Bound"
      >L&#8242;</a
      ><a name="12305"
      > </a
      ><a name="12306" href="Stlc.html#12065" class="Function Operator"
      >[</a
      ><a name="12307"
      > </a
      ><a name="12308" href="Stlc.html#12290" class="Bound"
      >x</a
      ><a name="12309"
      > </a
      ><a name="12310" href="Stlc.html#12065" class="Function Operator"
      >:=</a
      ><a name="12312"
      > </a
      ><a name="12313" href="Stlc.html#12295" class="Bound"
      >V</a
      ><a name="12314"
      > </a
      ><a name="12315" href="Stlc.html#12065" class="Function Operator"
      >]</a
      ><a name="12316" class="Symbol"
      >)</a
      ><a name="12317"
      > </a
      ><a name="12318" href="Stlc.html#3679" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="12319"
      > </a
      ><a name="12320" class="Symbol"
      >(</a
      ><a name="12321" href="Stlc.html#12284" class="Bound"
      >M&#8242;</a
      ><a name="12323"
      > </a
      ><a name="12324" href="Stlc.html#12065" class="Function Operator"
      >[</a
      ><a name="12325"
      > </a
      ><a name="12326" href="Stlc.html#12290" class="Bound"
      >x</a
      ><a name="12327"
      > </a
      ><a name="12328" href="Stlc.html#12065" class="Function Operator"
      >:=</a
      ><a name="12330"
      > </a
      ><a name="12331" href="Stlc.html#12295" class="Bound"
      >V</a
      ><a name="12332"
      > </a
      ><a name="12333" href="Stlc.html#12065" class="Function Operator"
      >]</a
      ><a name="12334" class="Symbol"
      >)</a
      ><a name="12335"
      >
</a
      ><a name="12336" class="Symbol"
      >(</a
      ><a name="12337" href="Stlc.html#3706" class="InductiveConstructor"
      >true</a
      ><a name="12341" class="Symbol"
      >)</a
      ><a name="12342"
      > </a
      ><a name="12343" href="Stlc.html#12065" class="Function Operator"
      >[</a
      ><a name="12344"
      > </a
      ><a name="12345" href="Stlc.html#12345" class="Bound"
      >x</a
      ><a name="12346"
      > </a
      ><a name="12347" href="Stlc.html#12065" class="Function Operator"
      >:=</a
      ><a name="12349"
      > </a
      ><a name="12350" href="Stlc.html#12350" class="Bound"
      >V</a
      ><a name="12351"
      > </a
      ><a name="12352" href="Stlc.html#12065" class="Function Operator"
      >]</a
      ><a name="12353"
      > </a
      ><a name="12354" class="Symbol"
      >=</a
      ><a name="12355"
      > </a
      ><a name="12356" href="Stlc.html#3706" class="InductiveConstructor"
      >true</a
      ><a name="12360"
      >
</a
      ><a name="12361" class="Symbol"
      >(</a
      ><a name="12362" href="Stlc.html#3720" class="InductiveConstructor"
      >false</a
      ><a name="12367" class="Symbol"
      >)</a
      ><a name="12368"
      > </a
      ><a name="12369" href="Stlc.html#12065" class="Function Operator"
      >[</a
      ><a name="12370"
      > </a
      ><a name="12371" href="Stlc.html#12371" class="Bound"
      >x</a
      ><a name="12372"
      > </a
      ><a name="12373" href="Stlc.html#12065" class="Function Operator"
      >:=</a
      ><a name="12375"
      > </a
      ><a name="12376" href="Stlc.html#12376" class="Bound"
      >V</a
      ><a name="12377"
      > </a
      ><a name="12378" href="Stlc.html#12065" class="Function Operator"
      >]</a
      ><a name="12379"
      > </a
      ><a name="12380" class="Symbol"
      >=</a
      ><a name="12381"
      > </a
      ><a name="12382" href="Stlc.html#3720" class="InductiveConstructor"
      >false</a
      ><a name="12387"
      >
</a
      ><a name="12388" class="Symbol"
      >(</a
      ><a name="12389" href="Stlc.html#3735" class="InductiveConstructor Operator"
      >if</a
      ><a name="12391"
      > </a
      ><a name="12392" href="Stlc.html#12392" class="Bound"
      >L&#8242;</a
      ><a name="12394"
      > </a
      ><a name="12395" href="Stlc.html#3735" class="InductiveConstructor Operator"
      >then</a
      ><a name="12399"
      > </a
      ><a name="12400" href="Stlc.html#12400" class="Bound"
      >M&#8242;</a
      ><a name="12402"
      > </a
      ><a name="12403" href="Stlc.html#3735" class="InductiveConstructor Operator"
      >else</a
      ><a name="12407"
      > </a
      ><a name="12408" href="Stlc.html#12408" class="Bound"
      >N&#8242;</a
      ><a name="12410" class="Symbol"
      >)</a
      ><a name="12411"
      > </a
      ><a name="12412" href="Stlc.html#12065" class="Function Operator"
      >[</a
      ><a name="12413"
      > </a
      ><a name="12414" href="Stlc.html#12414" class="Bound"
      >x</a
      ><a name="12415"
      > </a
      ><a name="12416" href="Stlc.html#12065" class="Function Operator"
      >:=</a
      ><a name="12418"
      > </a
      ><a name="12419" href="Stlc.html#12419" class="Bound"
      >V</a
      ><a name="12420"
      > </a
      ><a name="12421" href="Stlc.html#12065" class="Function Operator"
      >]</a
      ><a name="12422"
      > </a
      ><a name="12423" class="Symbol"
      >=</a
      ><a name="12424"
      >
  </a
      ><a name="12427" href="Stlc.html#3735" class="InductiveConstructor Operator"
      >if</a
      ><a name="12429"
      > </a
      ><a name="12430" class="Symbol"
      >(</a
      ><a name="12431" href="Stlc.html#12392" class="Bound"
      >L&#8242;</a
      ><a name="12433"
      > </a
      ><a name="12434" href="Stlc.html#12065" class="Function Operator"
      >[</a
      ><a name="12435"
      > </a
      ><a name="12436" href="Stlc.html#12414" class="Bound"
      >x</a
      ><a name="12437"
      > </a
      ><a name="12438" href="Stlc.html#12065" class="Function Operator"
      >:=</a
      ><a name="12440"
      > </a
      ><a name="12441" href="Stlc.html#12419" class="Bound"
      >V</a
      ><a name="12442"
      > </a
      ><a name="12443" href="Stlc.html#12065" class="Function Operator"
      >]</a
      ><a name="12444" class="Symbol"
      >)</a
      ><a name="12445"
      > </a
      ><a name="12446" href="Stlc.html#3735" class="InductiveConstructor Operator"
      >then</a
      ><a name="12450"
      > </a
      ><a name="12451" class="Symbol"
      >(</a
      ><a name="12452" href="Stlc.html#12400" class="Bound"
      >M&#8242;</a
      ><a name="12454"
      > </a
      ><a name="12455" href="Stlc.html#12065" class="Function Operator"
      >[</a
      ><a name="12456"
      > </a
      ><a name="12457" href="Stlc.html#12414" class="Bound"
      >x</a
      ><a name="12458"
      > </a
      ><a name="12459" href="Stlc.html#12065" class="Function Operator"
      >:=</a
      ><a name="12461"
      > </a
      ><a name="12462" href="Stlc.html#12419" class="Bound"
      >V</a
      ><a name="12463"
      > </a
      ><a name="12464" href="Stlc.html#12065" class="Function Operator"
      >]</a
      ><a name="12465" class="Symbol"
      >)</a
      ><a name="12466"
      > </a
      ><a name="12467" href="Stlc.html#3735" class="InductiveConstructor Operator"
      >else</a
      ><a name="12471"
      > </a
      ><a name="12472" class="Symbol"
      >(</a
      ><a name="12473" href="Stlc.html#12408" class="Bound"
      >N&#8242;</a
      ><a name="12475"
      > </a
      ><a name="12476" href="Stlc.html#12065" class="Function Operator"
      >[</a
      ><a name="12477"
      > </a
      ><a name="12478" href="Stlc.html#12414" class="Bound"
      >x</a
      ><a name="12479"
      > </a
      ><a name="12480" href="Stlc.html#12065" class="Function Operator"
      >:=</a
      ><a name="12482"
      > </a
      ><a name="12483" href="Stlc.html#12419" class="Bound"
      >V</a
      ><a name="12484"
      > </a
      ><a name="12485" href="Stlc.html#12065" class="Function Operator"
      >]</a
      ><a name="12486" class="Symbol"
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

<a name="13236" href="Stlc.html#13236" class="Function"
      >ex&#8321;&#8321;</a
      ><a name="13240"
      > </a
      ><a name="13241" class="Symbol"
      >:</a
      ><a name="13242"
      > </a
      ><a name="13243" href="Stlc.html#3627" class="InductiveConstructor"
      >`</a
      ><a name="13244"
      > </a
      ><a name="13245" href="Stlc.html#5639" class="Function"
      >f</a
      ><a name="13246"
      > </a
      ><a name="13247" href="Stlc.html#12065" class="Function Operator"
      >[</a
      ><a name="13248"
      > </a
      ><a name="13249" href="Stlc.html#5639" class="Function"
      >f</a
      ><a name="13250"
      > </a
      ><a name="13251" href="Stlc.html#12065" class="Function Operator"
      >:=</a
      ><a name="13253"
      > </a
      ><a name="13254" href="Stlc.html#5684" class="Function"
      >not</a
      ><a name="13257"
      > </a
      ><a name="13258" href="Stlc.html#12065" class="Function Operator"
      >]</a
      ><a name="13259"
      > </a
      ><a name="13260" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="13261"
      >  </a
      ><a name="13263" href="Stlc.html#5684" class="Function"
      >not</a
      ><a name="13266"
      >
</a
      ><a name="13267" href="Stlc.html#13236" class="Function"
      >ex&#8321;&#8321;</a
      ><a name="13271"
      > </a
      ><a name="13272" class="Symbol"
      >=</a
      ><a name="13273"
      > </a
      ><a name="13274" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="13278"
      >

</a
      ><a name="13280" href="Stlc.html#13280" class="Function"
      >ex&#8321;&#8322;</a
      ><a name="13284"
      > </a
      ><a name="13285" class="Symbol"
      >:</a
      ><a name="13286"
      > </a
      ><a name="13287" href="Stlc.html#3706" class="InductiveConstructor"
      >true</a
      ><a name="13291"
      > </a
      ><a name="13292" href="Stlc.html#12065" class="Function Operator"
      >[</a
      ><a name="13293"
      > </a
      ><a name="13294" href="Stlc.html#5639" class="Function"
      >f</a
      ><a name="13295"
      > </a
      ><a name="13296" href="Stlc.html#12065" class="Function Operator"
      >:=</a
      ><a name="13298"
      > </a
      ><a name="13299" href="Stlc.html#5684" class="Function"
      >not</a
      ><a name="13302"
      > </a
      ><a name="13303" href="Stlc.html#12065" class="Function Operator"
      >]</a
      ><a name="13304"
      > </a
      ><a name="13305" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="13306"
      > </a
      ><a name="13307" href="Stlc.html#3706" class="InductiveConstructor"
      >true</a
      ><a name="13311"
      >
</a
      ><a name="13312" href="Stlc.html#13280" class="Function"
      >ex&#8321;&#8322;</a
      ><a name="13316"
      > </a
      ><a name="13317" class="Symbol"
      >=</a
      ><a name="13318"
      > </a
      ><a name="13319" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="13323"
      >

</a
      ><a name="13325" href="Stlc.html#13325" class="Function"
      >ex&#8321;&#8323;</a
      ><a name="13329"
      > </a
      ><a name="13330" class="Symbol"
      >:</a
      ><a name="13331"
      > </a
      ><a name="13332" class="Symbol"
      >(</a
      ><a name="13333" href="Stlc.html#3627" class="InductiveConstructor"
      >`</a
      ><a name="13334"
      > </a
      ><a name="13335" href="Stlc.html#5639" class="Function"
      >f</a
      ><a name="13336"
      > </a
      ><a name="13337" href="Stlc.html#3679" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="13338"
      > </a
      ><a name="13339" href="Stlc.html#3706" class="InductiveConstructor"
      >true</a
      ><a name="13343" class="Symbol"
      >)</a
      ><a name="13344"
      > </a
      ><a name="13345" href="Stlc.html#12065" class="Function Operator"
      >[</a
      ><a name="13346"
      > </a
      ><a name="13347" href="Stlc.html#5639" class="Function"
      >f</a
      ><a name="13348"
      > </a
      ><a name="13349" href="Stlc.html#12065" class="Function Operator"
      >:=</a
      ><a name="13351"
      > </a
      ><a name="13352" href="Stlc.html#5684" class="Function"
      >not</a
      ><a name="13355"
      > </a
      ><a name="13356" href="Stlc.html#12065" class="Function Operator"
      >]</a
      ><a name="13357"
      > </a
      ><a name="13358" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="13359"
      > </a
      ><a name="13360" href="Stlc.html#5684" class="Function"
      >not</a
      ><a name="13363"
      > </a
      ><a name="13364" href="Stlc.html#3679" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="13365"
      > </a
      ><a name="13366" href="Stlc.html#3706" class="InductiveConstructor"
      >true</a
      ><a name="13370"
      >
</a
      ><a name="13371" href="Stlc.html#13325" class="Function"
      >ex&#8321;&#8323;</a
      ><a name="13375"
      > </a
      ><a name="13376" class="Symbol"
      >=</a
      ><a name="13377"
      > </a
      ><a name="13378" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="13382"
      >

</a
      ><a name="13384" href="Stlc.html#13384" class="Function"
      >ex&#8321;&#8324;</a
      ><a name="13388"
      > </a
      ><a name="13389" class="Symbol"
      >:</a
      ><a name="13390"
      > </a
      ><a name="13391" class="Symbol"
      >(</a
      ><a name="13392" href="Stlc.html#3627" class="InductiveConstructor"
      >`</a
      ><a name="13393"
      > </a
      ><a name="13394" href="Stlc.html#5639" class="Function"
      >f</a
      ><a name="13395"
      > </a
      ><a name="13396" href="Stlc.html#3679" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="13397"
      > </a
      ><a name="13398" class="Symbol"
      >(</a
      ><a name="13399" href="Stlc.html#3627" class="InductiveConstructor"
      >`</a
      ><a name="13400"
      > </a
      ><a name="13401" href="Stlc.html#5639" class="Function"
      >f</a
      ><a name="13402"
      > </a
      ><a name="13403" href="Stlc.html#3679" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="13404"
      > </a
      ><a name="13405" href="Stlc.html#3706" class="InductiveConstructor"
      >true</a
      ><a name="13409" class="Symbol"
      >))</a
      ><a name="13411"
      > </a
      ><a name="13412" href="Stlc.html#12065" class="Function Operator"
      >[</a
      ><a name="13413"
      > </a
      ><a name="13414" href="Stlc.html#5639" class="Function"
      >f</a
      ><a name="13415"
      > </a
      ><a name="13416" href="Stlc.html#12065" class="Function Operator"
      >:=</a
      ><a name="13418"
      > </a
      ><a name="13419" href="Stlc.html#5684" class="Function"
      >not</a
      ><a name="13422"
      > </a
      ><a name="13423" href="Stlc.html#12065" class="Function Operator"
      >]</a
      ><a name="13424"
      > </a
      ><a name="13425" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="13426"
      > </a
      ><a name="13427" href="Stlc.html#5684" class="Function"
      >not</a
      ><a name="13430"
      > </a
      ><a name="13431" href="Stlc.html#3679" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="13432"
      > </a
      ><a name="13433" class="Symbol"
      >(</a
      ><a name="13434" href="Stlc.html#5684" class="Function"
      >not</a
      ><a name="13437"
      > </a
      ><a name="13438" href="Stlc.html#3679" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="13439"
      > </a
      ><a name="13440" href="Stlc.html#3706" class="InductiveConstructor"
      >true</a
      ><a name="13444" class="Symbol"
      >)</a
      ><a name="13445"
      >
</a
      ><a name="13446" href="Stlc.html#13384" class="Function"
      >ex&#8321;&#8324;</a
      ><a name="13450"
      > </a
      ><a name="13451" class="Symbol"
      >=</a
      ><a name="13452"
      > </a
      ><a name="13453" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="13457"
      >

</a
      ><a name="13459" href="Stlc.html#13459" class="Function"
      >ex&#8321;&#8325;</a
      ><a name="13463"
      > </a
      ><a name="13464" class="Symbol"
      >:</a
      ><a name="13465"
      > </a
      ><a name="13466" class="Symbol"
      >(</a
      ><a name="13467" href="Stlc.html#3643" class="InductiveConstructor Operator"
      >&#955;[</a
      ><a name="13469"
      > </a
      ><a name="13470" href="Stlc.html#5641" class="Function"
      >x</a
      ><a name="13471"
      > </a
      ><a name="13472" href="Stlc.html#3643" class="InductiveConstructor Operator"
      >&#8758;</a
      ><a name="13473"
      > </a
      ><a name="13474" href="Stlc.html#2581" class="InductiveConstructor"
      >&#120121;</a
      ><a name="13475"
      > </a
      ><a name="13476" href="Stlc.html#3643" class="InductiveConstructor Operator"
      >]</a
      ><a name="13477"
      > </a
      ><a name="13478" href="Stlc.html#3627" class="InductiveConstructor"
      >`</a
      ><a name="13479"
      > </a
      ><a name="13480" href="Stlc.html#5639" class="Function"
      >f</a
      ><a name="13481"
      > </a
      ><a name="13482" href="Stlc.html#3679" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="13483"
      > </a
      ><a name="13484" class="Symbol"
      >(</a
      ><a name="13485" href="Stlc.html#3627" class="InductiveConstructor"
      >`</a
      ><a name="13486"
      > </a
      ><a name="13487" href="Stlc.html#5639" class="Function"
      >f</a
      ><a name="13488"
      > </a
      ><a name="13489" href="Stlc.html#3679" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="13490"
      > </a
      ><a name="13491" href="Stlc.html#3627" class="InductiveConstructor"
      >`</a
      ><a name="13492"
      > </a
      ><a name="13493" href="Stlc.html#5641" class="Function"
      >x</a
      ><a name="13494" class="Symbol"
      >))</a
      ><a name="13496"
      > </a
      ><a name="13497" href="Stlc.html#12065" class="Function Operator"
      >[</a
      ><a name="13498"
      > </a
      ><a name="13499" href="Stlc.html#5639" class="Function"
      >f</a
      ><a name="13500"
      > </a
      ><a name="13501" href="Stlc.html#12065" class="Function Operator"
      >:=</a
      ><a name="13503"
      > </a
      ><a name="13504" href="Stlc.html#5684" class="Function"
      >not</a
      ><a name="13507"
      > </a
      ><a name="13508" href="Stlc.html#12065" class="Function Operator"
      >]</a
      ><a name="13509"
      > </a
      ><a name="13510" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="13511"
      > </a
      ><a name="13512" href="Stlc.html#3643" class="InductiveConstructor Operator"
      >&#955;[</a
      ><a name="13514"
      > </a
      ><a name="13515" href="Stlc.html#5641" class="Function"
      >x</a
      ><a name="13516"
      > </a
      ><a name="13517" href="Stlc.html#3643" class="InductiveConstructor Operator"
      >&#8758;</a
      ><a name="13518"
      > </a
      ><a name="13519" href="Stlc.html#2581" class="InductiveConstructor"
      >&#120121;</a
      ><a name="13520"
      > </a
      ><a name="13521" href="Stlc.html#3643" class="InductiveConstructor Operator"
      >]</a
      ><a name="13522"
      > </a
      ><a name="13523" href="Stlc.html#5684" class="Function"
      >not</a
      ><a name="13526"
      > </a
      ><a name="13527" href="Stlc.html#3679" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="13528"
      > </a
      ><a name="13529" class="Symbol"
      >(</a
      ><a name="13530" href="Stlc.html#5684" class="Function"
      >not</a
      ><a name="13533"
      > </a
      ><a name="13534" href="Stlc.html#3679" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="13535"
      > </a
      ><a name="13536" href="Stlc.html#3627" class="InductiveConstructor"
      >`</a
      ><a name="13537"
      > </a
      ><a name="13538" href="Stlc.html#5641" class="Function"
      >x</a
      ><a name="13539" class="Symbol"
      >)</a
      ><a name="13540"
      >
</a
      ><a name="13541" href="Stlc.html#13459" class="Function"
      >ex&#8321;&#8325;</a
      ><a name="13545"
      > </a
      ><a name="13546" class="Symbol"
      >=</a
      ><a name="13547"
      > </a
      ><a name="13548" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="13552"
      >

</a
      ><a name="13554" href="Stlc.html#13554" class="Function"
      >ex&#8321;&#8326;</a
      ><a name="13558"
      > </a
      ><a name="13559" class="Symbol"
      >:</a
      ><a name="13560"
      > </a
      ><a name="13561" class="Symbol"
      >(</a
      ><a name="13562" href="Stlc.html#3643" class="InductiveConstructor Operator"
      >&#955;[</a
      ><a name="13564"
      > </a
      ><a name="13565" href="Stlc.html#5643" class="Function"
      >y</a
      ><a name="13566"
      > </a
      ><a name="13567" href="Stlc.html#3643" class="InductiveConstructor Operator"
      >&#8758;</a
      ><a name="13568"
      > </a
      ><a name="13569" href="Stlc.html#2581" class="InductiveConstructor"
      >&#120121;</a
      ><a name="13570"
      > </a
      ><a name="13571" href="Stlc.html#3643" class="InductiveConstructor Operator"
      >]</a
      ><a name="13572"
      > </a
      ><a name="13573" href="Stlc.html#3627" class="InductiveConstructor"
      >`</a
      ><a name="13574"
      > </a
      ><a name="13575" href="Stlc.html#5643" class="Function"
      >y</a
      ><a name="13576" class="Symbol"
      >)</a
      ><a name="13577"
      > </a
      ><a name="13578" href="Stlc.html#12065" class="Function Operator"
      >[</a
      ><a name="13579"
      > </a
      ><a name="13580" href="Stlc.html#5641" class="Function"
      >x</a
      ><a name="13581"
      > </a
      ><a name="13582" href="Stlc.html#12065" class="Function Operator"
      >:=</a
      ><a name="13584"
      > </a
      ><a name="13585" href="Stlc.html#3706" class="InductiveConstructor"
      >true</a
      ><a name="13589"
      > </a
      ><a name="13590" href="Stlc.html#12065" class="Function Operator"
      >]</a
      ><a name="13591"
      > </a
      ><a name="13592" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="13593"
      > </a
      ><a name="13594" href="Stlc.html#3643" class="InductiveConstructor Operator"
      >&#955;[</a
      ><a name="13596"
      > </a
      ><a name="13597" href="Stlc.html#5643" class="Function"
      >y</a
      ><a name="13598"
      > </a
      ><a name="13599" href="Stlc.html#3643" class="InductiveConstructor Operator"
      >&#8758;</a
      ><a name="13600"
      > </a
      ><a name="13601" href="Stlc.html#2581" class="InductiveConstructor"
      >&#120121;</a
      ><a name="13602"
      > </a
      ><a name="13603" href="Stlc.html#3643" class="InductiveConstructor Operator"
      >]</a
      ><a name="13604"
      > </a
      ><a name="13605" href="Stlc.html#3627" class="InductiveConstructor"
      >`</a
      ><a name="13606"
      > </a
      ><a name="13607" href="Stlc.html#5643" class="Function"
      >y</a
      ><a name="13608"
      >
</a
      ><a name="13609" href="Stlc.html#13554" class="Function"
      >ex&#8321;&#8326;</a
      ><a name="13613"
      > </a
      ><a name="13614" class="Symbol"
      >=</a
      ><a name="13615"
      > </a
      ><a name="13616" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="13620"
      >

</a
      ><a name="13622" href="Stlc.html#13622" class="Function"
      >ex&#8321;&#8327;</a
      ><a name="13626"
      > </a
      ><a name="13627" class="Symbol"
      >:</a
      ><a name="13628"
      > </a
      ><a name="13629" class="Symbol"
      >(</a
      ><a name="13630" href="Stlc.html#3643" class="InductiveConstructor Operator"
      >&#955;[</a
      ><a name="13632"
      > </a
      ><a name="13633" href="Stlc.html#5641" class="Function"
      >x</a
      ><a name="13634"
      > </a
      ><a name="13635" href="Stlc.html#3643" class="InductiveConstructor Operator"
      >&#8758;</a
      ><a name="13636"
      > </a
      ><a name="13637" href="Stlc.html#2581" class="InductiveConstructor"
      >&#120121;</a
      ><a name="13638"
      > </a
      ><a name="13639" href="Stlc.html#3643" class="InductiveConstructor Operator"
      >]</a
      ><a name="13640"
      > </a
      ><a name="13641" href="Stlc.html#3627" class="InductiveConstructor"
      >`</a
      ><a name="13642"
      > </a
      ><a name="13643" href="Stlc.html#5641" class="Function"
      >x</a
      ><a name="13644" class="Symbol"
      >)</a
      ><a name="13645"
      > </a
      ><a name="13646" href="Stlc.html#12065" class="Function Operator"
      >[</a
      ><a name="13647"
      > </a
      ><a name="13648" href="Stlc.html#5641" class="Function"
      >x</a
      ><a name="13649"
      > </a
      ><a name="13650" href="Stlc.html#12065" class="Function Operator"
      >:=</a
      ><a name="13652"
      > </a
      ><a name="13653" href="Stlc.html#3706" class="InductiveConstructor"
      >true</a
      ><a name="13657"
      > </a
      ><a name="13658" href="Stlc.html#12065" class="Function Operator"
      >]</a
      ><a name="13659"
      > </a
      ><a name="13660" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="13661"
      > </a
      ><a name="13662" href="Stlc.html#3643" class="InductiveConstructor Operator"
      >&#955;[</a
      ><a name="13664"
      > </a
      ><a name="13665" href="Stlc.html#5641" class="Function"
      >x</a
      ><a name="13666"
      > </a
      ><a name="13667" href="Stlc.html#3643" class="InductiveConstructor Operator"
      >&#8758;</a
      ><a name="13668"
      > </a
      ><a name="13669" href="Stlc.html#2581" class="InductiveConstructor"
      >&#120121;</a
      ><a name="13670"
      > </a
      ><a name="13671" href="Stlc.html#3643" class="InductiveConstructor Operator"
      >]</a
      ><a name="13672"
      > </a
      ><a name="13673" href="Stlc.html#3627" class="InductiveConstructor"
      >`</a
      ><a name="13674"
      > </a
      ><a name="13675" href="Stlc.html#5641" class="Function"
      >x</a
      ><a name="13676"
      >
</a
      ><a name="13677" href="Stlc.html#13622" class="Function"
      >ex&#8321;&#8327;</a
      ><a name="13681"
      > </a
      ><a name="13682" class="Symbol"
      >=</a
      ><a name="13683"
      > </a
      ><a name="13684" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
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

In an informal presentation of the formal semantics, the rules
are written as follows.

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

<pre class="Agda">

<a name="15737" class="Keyword"
      >infix</a
      ><a name="15742"
      > </a
      ><a name="15743" class="Number"
      >10</a
      ><a name="15745"
      > </a
      ><a name="15746" href="Stlc.html#15757" class="Datatype Operator"
      >_&#10233;_</a
      ><a name="15749"
      > 

</a
      ><a name="15752" class="Keyword"
      >data</a
      ><a name="15756"
      > </a
      ><a name="15757" href="Stlc.html#15757" class="Datatype Operator"
      >_&#10233;_</a
      ><a name="15760"
      > </a
      ><a name="15761" class="Symbol"
      >:</a
      ><a name="15762"
      > </a
      ><a name="15763" href="Stlc.html#3608" class="Datatype"
      >Term</a
      ><a name="15767"
      > </a
      ><a name="15768" class="Symbol"
      >&#8594;</a
      ><a name="15769"
      > </a
      ><a name="15770" href="Stlc.html#3608" class="Datatype"
      >Term</a
      ><a name="15774"
      > </a
      ><a name="15775" class="Symbol"
      >&#8594;</a
      ><a name="15776"
      > </a
      ><a name="15777" class="PrimitiveType"
      >Set</a
      ><a name="15780"
      > </a
      ><a name="15781" class="Keyword"
      >where</a
      ><a name="15786"
      >
  </a
      ><a name="15789" href="Stlc.html#15789" class="InductiveConstructor"
      >&#958;&#183;&#8321;</a
      ><a name="15792"
      > </a
      ><a name="15793" class="Symbol"
      >:</a
      ><a name="15794"
      > </a
      ><a name="15795" class="Symbol"
      >&#8704;</a
      ><a name="15796"
      > </a
      ><a name="15797" class="Symbol"
      >{</a
      ><a name="15798" href="Stlc.html#15798" class="Bound"
      >L</a
      ><a name="15799"
      > </a
      ><a name="15800" href="Stlc.html#15800" class="Bound"
      >L&#8242;</a
      ><a name="15802"
      > </a
      ><a name="15803" href="Stlc.html#15803" class="Bound"
      >M</a
      ><a name="15804" class="Symbol"
      >}</a
      ><a name="15805"
      > </a
      ><a name="15806" class="Symbol"
      >&#8594;</a
      ><a name="15807"
      >
    </a
      ><a name="15812" href="Stlc.html#15798" class="Bound"
      >L</a
      ><a name="15813"
      > </a
      ><a name="15814" href="Stlc.html#15757" class="Datatype Operator"
      >&#10233;</a
      ><a name="15815"
      > </a
      ><a name="15816" href="Stlc.html#15800" class="Bound"
      >L&#8242;</a
      ><a name="15818"
      > </a
      ><a name="15819" class="Symbol"
      >&#8594;</a
      ><a name="15820"
      >
    </a
      ><a name="15825" href="Stlc.html#15798" class="Bound"
      >L</a
      ><a name="15826"
      > </a
      ><a name="15827" href="Stlc.html#3679" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="15828"
      > </a
      ><a name="15829" href="Stlc.html#15803" class="Bound"
      >M</a
      ><a name="15830"
      > </a
      ><a name="15831" href="Stlc.html#15757" class="Datatype Operator"
      >&#10233;</a
      ><a name="15832"
      > </a
      ><a name="15833" href="Stlc.html#15800" class="Bound"
      >L&#8242;</a
      ><a name="15835"
      > </a
      ><a name="15836" href="Stlc.html#3679" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="15837"
      > </a
      ><a name="15838" href="Stlc.html#15803" class="Bound"
      >M</a
      ><a name="15839"
      >
  </a
      ><a name="15842" href="Stlc.html#15842" class="InductiveConstructor"
      >&#958;&#183;&#8322;</a
      ><a name="15845"
      > </a
      ><a name="15846" class="Symbol"
      >:</a
      ><a name="15847"
      > </a
      ><a name="15848" class="Symbol"
      >&#8704;</a
      ><a name="15849"
      > </a
      ><a name="15850" class="Symbol"
      >{</a
      ><a name="15851" href="Stlc.html#15851" class="Bound"
      >V</a
      ><a name="15852"
      > </a
      ><a name="15853" href="Stlc.html#15853" class="Bound"
      >M</a
      ><a name="15854"
      > </a
      ><a name="15855" href="Stlc.html#15855" class="Bound"
      >M&#8242;</a
      ><a name="15857" class="Symbol"
      >}</a
      ><a name="15858"
      > </a
      ><a name="15859" class="Symbol"
      >&#8594;</a
      ><a name="15860"
      >
    </a
      ><a name="15865" href="Stlc.html#9521" class="Datatype"
      >Value</a
      ><a name="15870"
      > </a
      ><a name="15871" href="Stlc.html#15851" class="Bound"
      >V</a
      ><a name="15872"
      > </a
      ><a name="15873" class="Symbol"
      >&#8594;</a
      ><a name="15874"
      >
    </a
      ><a name="15879" href="Stlc.html#15853" class="Bound"
      >M</a
      ><a name="15880"
      > </a
      ><a name="15881" href="Stlc.html#15757" class="Datatype Operator"
      >&#10233;</a
      ><a name="15882"
      > </a
      ><a name="15883" href="Stlc.html#15855" class="Bound"
      >M&#8242;</a
      ><a name="15885"
      > </a
      ><a name="15886" class="Symbol"
      >&#8594;</a
      ><a name="15887"
      >
    </a
      ><a name="15892" href="Stlc.html#15851" class="Bound"
      >V</a
      ><a name="15893"
      > </a
      ><a name="15894" href="Stlc.html#3679" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="15895"
      > </a
      ><a name="15896" href="Stlc.html#15853" class="Bound"
      >M</a
      ><a name="15897"
      > </a
      ><a name="15898" href="Stlc.html#15757" class="Datatype Operator"
      >&#10233;</a
      ><a name="15899"
      > </a
      ><a name="15900" href="Stlc.html#15851" class="Bound"
      >V</a
      ><a name="15901"
      > </a
      ><a name="15902" href="Stlc.html#3679" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="15903"
      > </a
      ><a name="15904" href="Stlc.html#15855" class="Bound"
      >M&#8242;</a
      ><a name="15906"
      >
  </a
      ><a name="15909" href="Stlc.html#15909" class="InductiveConstructor"
      >&#946;&#955;&#183;</a
      ><a name="15912"
      > </a
      ><a name="15913" class="Symbol"
      >:</a
      ><a name="15914"
      > </a
      ><a name="15915" class="Symbol"
      >&#8704;</a
      ><a name="15916"
      > </a
      ><a name="15917" class="Symbol"
      >{</a
      ><a name="15918" href="Stlc.html#15918" class="Bound"
      >x</a
      ><a name="15919"
      > </a
      ><a name="15920" href="Stlc.html#15920" class="Bound"
      >A</a
      ><a name="15921"
      > </a
      ><a name="15922" href="Stlc.html#15922" class="Bound"
      >N</a
      ><a name="15923"
      > </a
      ><a name="15924" href="Stlc.html#15924" class="Bound"
      >V</a
      ><a name="15925" class="Symbol"
      >}</a
      ><a name="15926"
      > </a
      ><a name="15927" class="Symbol"
      >&#8594;</a
      ><a name="15928"
      > </a
      ><a name="15929" href="Stlc.html#9521" class="Datatype"
      >Value</a
      ><a name="15934"
      > </a
      ><a name="15935" href="Stlc.html#15924" class="Bound"
      >V</a
      ><a name="15936"
      > </a
      ><a name="15937" class="Symbol"
      >&#8594;</a
      ><a name="15938"
      >
    </a
      ><a name="15943" class="Symbol"
      >(</a
      ><a name="15944" href="Stlc.html#3643" class="InductiveConstructor Operator"
      >&#955;[</a
      ><a name="15946"
      > </a
      ><a name="15947" href="Stlc.html#15918" class="Bound"
      >x</a
      ><a name="15948"
      > </a
      ><a name="15949" href="Stlc.html#3643" class="InductiveConstructor Operator"
      >&#8758;</a
      ><a name="15950"
      > </a
      ><a name="15951" href="Stlc.html#15920" class="Bound"
      >A</a
      ><a name="15952"
      > </a
      ><a name="15953" href="Stlc.html#3643" class="InductiveConstructor Operator"
      >]</a
      ><a name="15954"
      > </a
      ><a name="15955" href="Stlc.html#15922" class="Bound"
      >N</a
      ><a name="15956" class="Symbol"
      >)</a
      ><a name="15957"
      > </a
      ><a name="15958" href="Stlc.html#3679" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="15959"
      > </a
      ><a name="15960" href="Stlc.html#15924" class="Bound"
      >V</a
      ><a name="15961"
      > </a
      ><a name="15962" href="Stlc.html#15757" class="Datatype Operator"
      >&#10233;</a
      ><a name="15963"
      > </a
      ><a name="15964" href="Stlc.html#15922" class="Bound"
      >N</a
      ><a name="15965"
      > </a
      ><a name="15966" href="Stlc.html#12065" class="Function Operator"
      >[</a
      ><a name="15967"
      > </a
      ><a name="15968" href="Stlc.html#15918" class="Bound"
      >x</a
      ><a name="15969"
      > </a
      ><a name="15970" href="Stlc.html#12065" class="Function Operator"
      >:=</a
      ><a name="15972"
      > </a
      ><a name="15973" href="Stlc.html#15924" class="Bound"
      >V</a
      ><a name="15974"
      > </a
      ><a name="15975" href="Stlc.html#12065" class="Function Operator"
      >]</a
      ><a name="15976"
      >
  </a
      ><a name="15979" href="Stlc.html#15979" class="InductiveConstructor"
      >&#958;if</a
      ><a name="15982"
      > </a
      ><a name="15983" class="Symbol"
      >:</a
      ><a name="15984"
      > </a
      ><a name="15985" class="Symbol"
      >&#8704;</a
      ><a name="15986"
      > </a
      ><a name="15987" class="Symbol"
      >{</a
      ><a name="15988" href="Stlc.html#15988" class="Bound"
      >L</a
      ><a name="15989"
      > </a
      ><a name="15990" href="Stlc.html#15990" class="Bound"
      >L&#8242;</a
      ><a name="15992"
      > </a
      ><a name="15993" href="Stlc.html#15993" class="Bound"
      >M</a
      ><a name="15994"
      > </a
      ><a name="15995" href="Stlc.html#15995" class="Bound"
      >N</a
      ><a name="15996" class="Symbol"
      >}</a
      ><a name="15997"
      > </a
      ><a name="15998" class="Symbol"
      >&#8594;</a
      ><a name="15999"
      >
    </a
      ><a name="16004" href="Stlc.html#15988" class="Bound"
      >L</a
      ><a name="16005"
      > </a
      ><a name="16006" href="Stlc.html#15757" class="Datatype Operator"
      >&#10233;</a
      ><a name="16007"
      > </a
      ><a name="16008" href="Stlc.html#15990" class="Bound"
      >L&#8242;</a
      ><a name="16010"
      > </a
      ><a name="16011" class="Symbol"
      >&#8594;</a
      ><a name="16012"
      >    
    </a
      ><a name="16021" href="Stlc.html#3735" class="InductiveConstructor Operator"
      >if</a
      ><a name="16023"
      > </a
      ><a name="16024" href="Stlc.html#15988" class="Bound"
      >L</a
      ><a name="16025"
      > </a
      ><a name="16026" href="Stlc.html#3735" class="InductiveConstructor Operator"
      >then</a
      ><a name="16030"
      > </a
      ><a name="16031" href="Stlc.html#15993" class="Bound"
      >M</a
      ><a name="16032"
      > </a
      ><a name="16033" href="Stlc.html#3735" class="InductiveConstructor Operator"
      >else</a
      ><a name="16037"
      > </a
      ><a name="16038" href="Stlc.html#15995" class="Bound"
      >N</a
      ><a name="16039"
      > </a
      ><a name="16040" href="Stlc.html#15757" class="Datatype Operator"
      >&#10233;</a
      ><a name="16041"
      > </a
      ><a name="16042" href="Stlc.html#3735" class="InductiveConstructor Operator"
      >if</a
      ><a name="16044"
      > </a
      ><a name="16045" href="Stlc.html#15990" class="Bound"
      >L&#8242;</a
      ><a name="16047"
      > </a
      ><a name="16048" href="Stlc.html#3735" class="InductiveConstructor Operator"
      >then</a
      ><a name="16052"
      > </a
      ><a name="16053" href="Stlc.html#15993" class="Bound"
      >M</a
      ><a name="16054"
      > </a
      ><a name="16055" href="Stlc.html#3735" class="InductiveConstructor Operator"
      >else</a
      ><a name="16059"
      > </a
      ><a name="16060" href="Stlc.html#15995" class="Bound"
      >N</a
      ><a name="16061"
      >
  </a
      ><a name="16064" href="Stlc.html#16064" class="InductiveConstructor"
      >&#946;if-true</a
      ><a name="16072"
      > </a
      ><a name="16073" class="Symbol"
      >:</a
      ><a name="16074"
      > </a
      ><a name="16075" class="Symbol"
      >&#8704;</a
      ><a name="16076"
      > </a
      ><a name="16077" class="Symbol"
      >{</a
      ><a name="16078" href="Stlc.html#16078" class="Bound"
      >M</a
      ><a name="16079"
      > </a
      ><a name="16080" href="Stlc.html#16080" class="Bound"
      >N</a
      ><a name="16081" class="Symbol"
      >}</a
      ><a name="16082"
      > </a
      ><a name="16083" class="Symbol"
      >&#8594;</a
      ><a name="16084"
      >
    </a
      ><a name="16089" href="Stlc.html#3735" class="InductiveConstructor Operator"
      >if</a
      ><a name="16091"
      > </a
      ><a name="16092" href="Stlc.html#3706" class="InductiveConstructor"
      >true</a
      ><a name="16096"
      > </a
      ><a name="16097" href="Stlc.html#3735" class="InductiveConstructor Operator"
      >then</a
      ><a name="16101"
      > </a
      ><a name="16102" href="Stlc.html#16078" class="Bound"
      >M</a
      ><a name="16103"
      > </a
      ><a name="16104" href="Stlc.html#3735" class="InductiveConstructor Operator"
      >else</a
      ><a name="16108"
      > </a
      ><a name="16109" href="Stlc.html#16080" class="Bound"
      >N</a
      ><a name="16110"
      > </a
      ><a name="16111" href="Stlc.html#15757" class="Datatype Operator"
      >&#10233;</a
      ><a name="16112"
      > </a
      ><a name="16113" href="Stlc.html#16078" class="Bound"
      >M</a
      ><a name="16114"
      >
  </a
      ><a name="16117" href="Stlc.html#16117" class="InductiveConstructor"
      >&#946;if-false</a
      ><a name="16126"
      > </a
      ><a name="16127" class="Symbol"
      >:</a
      ><a name="16128"
      > </a
      ><a name="16129" class="Symbol"
      >&#8704;</a
      ><a name="16130"
      > </a
      ><a name="16131" class="Symbol"
      >{</a
      ><a name="16132" href="Stlc.html#16132" class="Bound"
      >M</a
      ><a name="16133"
      > </a
      ><a name="16134" href="Stlc.html#16134" class="Bound"
      >N</a
      ><a name="16135" class="Symbol"
      >}</a
      ><a name="16136"
      > </a
      ><a name="16137" class="Symbol"
      >&#8594;</a
      ><a name="16138"
      >
    </a
      ><a name="16143" href="Stlc.html#3735" class="InductiveConstructor Operator"
      >if</a
      ><a name="16145"
      > </a
      ><a name="16146" href="Stlc.html#3720" class="InductiveConstructor"
      >false</a
      ><a name="16151"
      > </a
      ><a name="16152" href="Stlc.html#3735" class="InductiveConstructor Operator"
      >then</a
      ><a name="16156"
      > </a
      ><a name="16157" href="Stlc.html#16132" class="Bound"
      >M</a
      ><a name="16158"
      > </a
      ><a name="16159" href="Stlc.html#3735" class="InductiveConstructor Operator"
      >else</a
      ><a name="16163"
      > </a
      ><a name="16164" href="Stlc.html#16134" class="Bound"
      >N</a
      ><a name="16165"
      > </a
      ><a name="16166" href="Stlc.html#15757" class="Datatype Operator"
      >&#10233;</a
      ><a name="16167"
      > </a
      ><a name="16168" href="Stlc.html#16134" class="Bound"
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

<a name="17736" class="Keyword"
      >infix</a
      ><a name="17741"
      > </a
      ><a name="17742" class="Number"
      >10</a
      ><a name="17744"
      > </a
      ><a name="17745" href="Stlc.html#17785" class="Datatype Operator"
      >_&#10233;*_</a
      ><a name="17749"
      > 
</a
      ><a name="17751" class="Keyword"
      >infixr</a
      ><a name="17757"
      > </a
      ><a name="17758" class="Number"
      >2</a
      ><a name="17759"
      > </a
      ><a name="17760" href="Stlc.html#17838" class="InductiveConstructor Operator"
      >_&#10233;&#10216;_&#10217;_</a
      ><a name="17766"
      >
</a
      ><a name="17767" class="Keyword"
      >infix</a
      ><a name="17772"
      >  </a
      ><a name="17774" class="Number"
      >3</a
      ><a name="17775"
      > </a
      ><a name="17776" href="Stlc.html#17818" class="InductiveConstructor Operator"
      >_&#8718;</a
      ><a name="17778"
      >

</a
      ><a name="17780" class="Keyword"
      >data</a
      ><a name="17784"
      > </a
      ><a name="17785" href="Stlc.html#17785" class="Datatype Operator"
      >_&#10233;*_</a
      ><a name="17789"
      > </a
      ><a name="17790" class="Symbol"
      >:</a
      ><a name="17791"
      > </a
      ><a name="17792" href="Stlc.html#3608" class="Datatype"
      >Term</a
      ><a name="17796"
      > </a
      ><a name="17797" class="Symbol"
      >&#8594;</a
      ><a name="17798"
      > </a
      ><a name="17799" href="Stlc.html#3608" class="Datatype"
      >Term</a
      ><a name="17803"
      > </a
      ><a name="17804" class="Symbol"
      >&#8594;</a
      ><a name="17805"
      > </a
      ><a name="17806" class="PrimitiveType"
      >Set</a
      ><a name="17809"
      > </a
      ><a name="17810" class="Keyword"
      >where</a
      ><a name="17815"
      >
  </a
      ><a name="17818" href="Stlc.html#17818" class="InductiveConstructor Operator"
      >_&#8718;</a
      ><a name="17820"
      > </a
      ><a name="17821" class="Symbol"
      >:</a
      ><a name="17822"
      > </a
      ><a name="17823" class="Symbol"
      >&#8704;</a
      ><a name="17824"
      > </a
      ><a name="17825" href="Stlc.html#17825" class="Bound"
      >M</a
      ><a name="17826"
      > </a
      ><a name="17827" class="Symbol"
      >&#8594;</a
      ><a name="17828"
      > </a
      ><a name="17829" href="Stlc.html#17825" class="Bound"
      >M</a
      ><a name="17830"
      > </a
      ><a name="17831" href="Stlc.html#17785" class="Datatype Operator"
      >&#10233;*</a
      ><a name="17833"
      > </a
      ><a name="17834" href="Stlc.html#17825" class="Bound"
      >M</a
      ><a name="17835"
      >
  </a
      ><a name="17838" href="Stlc.html#17838" class="InductiveConstructor Operator"
      >_&#10233;&#10216;_&#10217;_</a
      ><a name="17844"
      > </a
      ><a name="17845" class="Symbol"
      >:</a
      ><a name="17846"
      > </a
      ><a name="17847" class="Symbol"
      >&#8704;</a
      ><a name="17848"
      > </a
      ><a name="17849" href="Stlc.html#17849" class="Bound"
      >L</a
      ><a name="17850"
      > </a
      ><a name="17851" class="Symbol"
      >{</a
      ><a name="17852" href="Stlc.html#17852" class="Bound"
      >M</a
      ><a name="17853"
      > </a
      ><a name="17854" href="Stlc.html#17854" class="Bound"
      >N</a
      ><a name="17855" class="Symbol"
      >}</a
      ><a name="17856"
      > </a
      ><a name="17857" class="Symbol"
      >&#8594;</a
      ><a name="17858"
      > </a
      ><a name="17859" href="Stlc.html#17849" class="Bound"
      >L</a
      ><a name="17860"
      > </a
      ><a name="17861" href="Stlc.html#15757" class="Datatype Operator"
      >&#10233;</a
      ><a name="17862"
      > </a
      ><a name="17863" href="Stlc.html#17852" class="Bound"
      >M</a
      ><a name="17864"
      > </a
      ><a name="17865" class="Symbol"
      >&#8594;</a
      ><a name="17866"
      > </a
      ><a name="17867" href="Stlc.html#17852" class="Bound"
      >M</a
      ><a name="17868"
      > </a
      ><a name="17869" href="Stlc.html#17785" class="Datatype Operator"
      >&#10233;*</a
      ><a name="17871"
      > </a
      ><a name="17872" href="Stlc.html#17854" class="Bound"
      >N</a
      ><a name="17873"
      > </a
      ><a name="17874" class="Symbol"
      >&#8594;</a
      ><a name="17875"
      > </a
      ><a name="17876" href="Stlc.html#17849" class="Bound"
      >L</a
      ><a name="17877"
      > </a
      ><a name="17878" href="Stlc.html#17785" class="Datatype Operator"
      >&#10233;*</a
      ><a name="17880"
      > </a
      ><a name="17881" href="Stlc.html#17854" class="Bound"
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

<a name="18342" href="Stlc.html#18342" class="Function"
      >reduction&#8321;</a
      ><a name="18352"
      > </a
      ><a name="18353" class="Symbol"
      >:</a
      ><a name="18354"
      > </a
      ><a name="18355" href="Stlc.html#5684" class="Function"
      >not</a
      ><a name="18358"
      > </a
      ><a name="18359" href="Stlc.html#3679" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="18360"
      > </a
      ><a name="18361" href="Stlc.html#3706" class="InductiveConstructor"
      >true</a
      ><a name="18365"
      > </a
      ><a name="18366" href="Stlc.html#17785" class="Datatype Operator"
      >&#10233;*</a
      ><a name="18368"
      > </a
      ><a name="18369" href="Stlc.html#3720" class="InductiveConstructor"
      >false</a
      ><a name="18374"
      >
</a
      ><a name="18375" href="Stlc.html#18342" class="Function"
      >reduction&#8321;</a
      ><a name="18385"
      > </a
      ><a name="18386" class="Symbol"
      >=</a
      ><a name="18387"
      >
    </a
      ><a name="18392" href="Stlc.html#5684" class="Function"
      >not</a
      ><a name="18395"
      > </a
      ><a name="18396" href="Stlc.html#3679" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="18397"
      > </a
      ><a name="18398" href="Stlc.html#3706" class="InductiveConstructor"
      >true</a
      ><a name="18402"
      >
  </a
      ><a name="18405" href="Stlc.html#17838" class="InductiveConstructor Operator"
      >&#10233;&#10216;</a
      ><a name="18407"
      > </a
      ><a name="18408" href="Stlc.html#15909" class="InductiveConstructor"
      >&#946;&#955;&#183;</a
      ><a name="18411"
      > </a
      ><a name="18412" href="Stlc.html#9597" class="InductiveConstructor"
      >value-true</a
      ><a name="18422"
      > </a
      ><a name="18423" href="Stlc.html#17838" class="InductiveConstructor Operator"
      >&#10217;</a
      ><a name="18424"
      >
    </a
      ><a name="18429" href="Stlc.html#3735" class="InductiveConstructor Operator"
      >if</a
      ><a name="18431"
      > </a
      ><a name="18432" href="Stlc.html#3706" class="InductiveConstructor"
      >true</a
      ><a name="18436"
      > </a
      ><a name="18437" href="Stlc.html#3735" class="InductiveConstructor Operator"
      >then</a
      ><a name="18441"
      > </a
      ><a name="18442" href="Stlc.html#3720" class="InductiveConstructor"
      >false</a
      ><a name="18447"
      > </a
      ><a name="18448" href="Stlc.html#3735" class="InductiveConstructor Operator"
      >else</a
      ><a name="18452"
      > </a
      ><a name="18453" href="Stlc.html#3706" class="InductiveConstructor"
      >true</a
      ><a name="18457"
      >
  </a
      ><a name="18460" href="Stlc.html#17838" class="InductiveConstructor Operator"
      >&#10233;&#10216;</a
      ><a name="18462"
      > </a
      ><a name="18463" href="Stlc.html#16064" class="InductiveConstructor"
      >&#946;if-true</a
      ><a name="18471"
      > </a
      ><a name="18472" href="Stlc.html#17838" class="InductiveConstructor Operator"
      >&#10217;</a
      ><a name="18473"
      >
    </a
      ><a name="18478" href="Stlc.html#3720" class="InductiveConstructor"
      >false</a
      ><a name="18483"
      >
  </a
      ><a name="18486" href="Stlc.html#17818" class="InductiveConstructor Operator"
      >&#8718;</a
      ><a name="18487"
      >

</a
      ><a name="18489" href="Stlc.html#18489" class="Function"
      >reduction&#8322;</a
      ><a name="18499"
      > </a
      ><a name="18500" class="Symbol"
      >:</a
      ><a name="18501"
      > </a
      ><a name="18502" href="Stlc.html#5688" class="Function"
      >two</a
      ><a name="18505"
      > </a
      ><a name="18506" href="Stlc.html#3679" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="18507"
      > </a
      ><a name="18508" href="Stlc.html#5684" class="Function"
      >not</a
      ><a name="18511"
      > </a
      ><a name="18512" href="Stlc.html#3679" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="18513"
      > </a
      ><a name="18514" href="Stlc.html#3706" class="InductiveConstructor"
      >true</a
      ><a name="18518"
      > </a
      ><a name="18519" href="Stlc.html#17785" class="Datatype Operator"
      >&#10233;*</a
      ><a name="18521"
      > </a
      ><a name="18522" href="Stlc.html#3706" class="InductiveConstructor"
      >true</a
      ><a name="18526"
      >
</a
      ><a name="18527" href="Stlc.html#18489" class="Function"
      >reduction&#8322;</a
      ><a name="18537"
      > </a
      ><a name="18538" class="Symbol"
      >=</a
      ><a name="18539"
      >
    </a
      ><a name="18544" href="Stlc.html#5688" class="Function"
      >two</a
      ><a name="18547"
      > </a
      ><a name="18548" href="Stlc.html#3679" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="18549"
      > </a
      ><a name="18550" href="Stlc.html#5684" class="Function"
      >not</a
      ><a name="18553"
      > </a
      ><a name="18554" href="Stlc.html#3679" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="18555"
      > </a
      ><a name="18556" href="Stlc.html#3706" class="InductiveConstructor"
      >true</a
      ><a name="18560"
      >
  </a
      ><a name="18563" href="Stlc.html#17838" class="InductiveConstructor Operator"
      >&#10233;&#10216;</a
      ><a name="18565"
      > </a
      ><a name="18566" href="Stlc.html#15789" class="InductiveConstructor"
      >&#958;&#183;&#8321;</a
      ><a name="18569"
      > </a
      ><a name="18570" class="Symbol"
      >(</a
      ><a name="18571" href="Stlc.html#15909" class="InductiveConstructor"
      >&#946;&#955;&#183;</a
      ><a name="18574"
      > </a
      ><a name="18575" href="Stlc.html#9548" class="InductiveConstructor"
      >value-&#955;</a
      ><a name="18582" class="Symbol"
      >)</a
      ><a name="18583"
      > </a
      ><a name="18584" href="Stlc.html#17838" class="InductiveConstructor Operator"
      >&#10217;</a
      ><a name="18585"
      >
    </a
      ><a name="18590" class="Symbol"
      >(</a
      ><a name="18591" href="Stlc.html#3643" class="InductiveConstructor Operator"
      >&#955;[</a
      ><a name="18593"
      > </a
      ><a name="18594" href="Stlc.html#5641" class="Function"
      >x</a
      ><a name="18595"
      > </a
      ><a name="18596" href="Stlc.html#3643" class="InductiveConstructor Operator"
      >&#8758;</a
      ><a name="18597"
      > </a
      ><a name="18598" href="Stlc.html#2581" class="InductiveConstructor"
      >&#120121;</a
      ><a name="18599"
      > </a
      ><a name="18600" href="Stlc.html#3643" class="InductiveConstructor Operator"
      >]</a
      ><a name="18601"
      > </a
      ><a name="18602" href="Stlc.html#5684" class="Function"
      >not</a
      ><a name="18605"
      > </a
      ><a name="18606" href="Stlc.html#3679" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="18607"
      > </a
      ><a name="18608" class="Symbol"
      >(</a
      ><a name="18609" href="Stlc.html#5684" class="Function"
      >not</a
      ><a name="18612"
      > </a
      ><a name="18613" href="Stlc.html#3679" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="18614"
      > </a
      ><a name="18615" href="Stlc.html#3627" class="InductiveConstructor"
      >`</a
      ><a name="18616"
      > </a
      ><a name="18617" href="Stlc.html#5641" class="Function"
      >x</a
      ><a name="18618" class="Symbol"
      >))</a
      ><a name="18620"
      > </a
      ><a name="18621" href="Stlc.html#3679" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="18622"
      > </a
      ><a name="18623" href="Stlc.html#3706" class="InductiveConstructor"
      >true</a
      ><a name="18627"
      >
  </a
      ><a name="18630" href="Stlc.html#17838" class="InductiveConstructor Operator"
      >&#10233;&#10216;</a
      ><a name="18632"
      > </a
      ><a name="18633" href="Stlc.html#15909" class="InductiveConstructor"
      >&#946;&#955;&#183;</a
      ><a name="18636"
      > </a
      ><a name="18637" href="Stlc.html#9597" class="InductiveConstructor"
      >value-true</a
      ><a name="18647"
      > </a
      ><a name="18648" href="Stlc.html#17838" class="InductiveConstructor Operator"
      >&#10217;</a
      ><a name="18649"
      >
    </a
      ><a name="18654" href="Stlc.html#5684" class="Function"
      >not</a
      ><a name="18657"
      > </a
      ><a name="18658" href="Stlc.html#3679" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="18659"
      > </a
      ><a name="18660" class="Symbol"
      >(</a
      ><a name="18661" href="Stlc.html#5684" class="Function"
      >not</a
      ><a name="18664"
      > </a
      ><a name="18665" href="Stlc.html#3679" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="18666"
      > </a
      ><a name="18667" href="Stlc.html#3706" class="InductiveConstructor"
      >true</a
      ><a name="18671" class="Symbol"
      >)</a
      ><a name="18672"
      >
  </a
      ><a name="18675" href="Stlc.html#17838" class="InductiveConstructor Operator"
      >&#10233;&#10216;</a
      ><a name="18677"
      > </a
      ><a name="18678" href="Stlc.html#15842" class="InductiveConstructor"
      >&#958;&#183;&#8322;</a
      ><a name="18681"
      > </a
      ><a name="18682" href="Stlc.html#9548" class="InductiveConstructor"
      >value-&#955;</a
      ><a name="18689"
      > </a
      ><a name="18690" class="Symbol"
      >(</a
      ><a name="18691" href="Stlc.html#15909" class="InductiveConstructor"
      >&#946;&#955;&#183;</a
      ><a name="18694"
      > </a
      ><a name="18695" href="Stlc.html#9597" class="InductiveConstructor"
      >value-true</a
      ><a name="18705" class="Symbol"
      >)</a
      ><a name="18706"
      > </a
      ><a name="18707" href="Stlc.html#17838" class="InductiveConstructor Operator"
      >&#10217;</a
      ><a name="18708"
      >
    </a
      ><a name="18713" href="Stlc.html#5684" class="Function"
      >not</a
      ><a name="18716"
      > </a
      ><a name="18717" href="Stlc.html#3679" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="18718"
      > </a
      ><a name="18719" class="Symbol"
      >(</a
      ><a name="18720" href="Stlc.html#3735" class="InductiveConstructor Operator"
      >if</a
      ><a name="18722"
      > </a
      ><a name="18723" href="Stlc.html#3706" class="InductiveConstructor"
      >true</a
      ><a name="18727"
      > </a
      ><a name="18728" href="Stlc.html#3735" class="InductiveConstructor Operator"
      >then</a
      ><a name="18732"
      > </a
      ><a name="18733" href="Stlc.html#3720" class="InductiveConstructor"
      >false</a
      ><a name="18738"
      > </a
      ><a name="18739" href="Stlc.html#3735" class="InductiveConstructor Operator"
      >else</a
      ><a name="18743"
      > </a
      ><a name="18744" href="Stlc.html#3706" class="InductiveConstructor"
      >true</a
      ><a name="18748" class="Symbol"
      >)</a
      ><a name="18749"
      >
  </a
      ><a name="18752" href="Stlc.html#17838" class="InductiveConstructor Operator"
      >&#10233;&#10216;</a
      ><a name="18754"
      > </a
      ><a name="18755" href="Stlc.html#15842" class="InductiveConstructor"
      >&#958;&#183;&#8322;</a
      ><a name="18758"
      > </a
      ><a name="18759" href="Stlc.html#9548" class="InductiveConstructor"
      >value-&#955;</a
      ><a name="18766"
      > </a
      ><a name="18767" href="Stlc.html#16064" class="InductiveConstructor"
      >&#946;if-true</a
      ><a name="18775"
      >  </a
      ><a name="18777" href="Stlc.html#17838" class="InductiveConstructor Operator"
      >&#10217;</a
      ><a name="18778"
      >
    </a
      ><a name="18783" href="Stlc.html#5684" class="Function"
      >not</a
      ><a name="18786"
      > </a
      ><a name="18787" href="Stlc.html#3679" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="18788"
      > </a
      ><a name="18789" href="Stlc.html#3720" class="InductiveConstructor"
      >false</a
      ><a name="18794"
      >
  </a
      ><a name="18797" href="Stlc.html#17838" class="InductiveConstructor Operator"
      >&#10233;&#10216;</a
      ><a name="18799"
      > </a
      ><a name="18800" href="Stlc.html#15909" class="InductiveConstructor"
      >&#946;&#955;&#183;</a
      ><a name="18803"
      > </a
      ><a name="18804" href="Stlc.html#9624" class="InductiveConstructor"
      >value-false</a
      ><a name="18815"
      > </a
      ><a name="18816" href="Stlc.html#17838" class="InductiveConstructor Operator"
      >&#10217;</a
      ><a name="18817"
      >
    </a
      ><a name="18822" href="Stlc.html#3735" class="InductiveConstructor Operator"
      >if</a
      ><a name="18824"
      > </a
      ><a name="18825" href="Stlc.html#3720" class="InductiveConstructor"
      >false</a
      ><a name="18830"
      > </a
      ><a name="18831" href="Stlc.html#3735" class="InductiveConstructor Operator"
      >then</a
      ><a name="18835"
      > </a
      ><a name="18836" href="Stlc.html#3720" class="InductiveConstructor"
      >false</a
      ><a name="18841"
      > </a
      ><a name="18842" href="Stlc.html#3735" class="InductiveConstructor Operator"
      >else</a
      ><a name="18846"
      > </a
      ><a name="18847" href="Stlc.html#3706" class="InductiveConstructor"
      >true</a
      ><a name="18851"
      >
  </a
      ><a name="18854" href="Stlc.html#17838" class="InductiveConstructor Operator"
      >&#10233;&#10216;</a
      ><a name="18856"
      > </a
      ><a name="18857" href="Stlc.html#16117" class="InductiveConstructor"
      >&#946;if-false</a
      ><a name="18866"
      > </a
      ><a name="18867" href="Stlc.html#17838" class="InductiveConstructor Operator"
      >&#10217;</a
      ><a name="18868"
      >
    </a
      ><a name="18873" href="Stlc.html#3706" class="InductiveConstructor"
      >true</a
      ><a name="18877"
      >
  </a
      ><a name="18880" href="Stlc.html#17818" class="InductiveConstructor Operator"
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
Here `Γ` provides types for all the free variables in `M`.

Here are three examples. 

* `` ∅ ⊢ (λ[ f ∶ 𝔹 ⇒ 𝔹 ] λ[ x ∶ 𝔹 ] ` f · (` f · ` x)) ∶  (𝔹 ⇒ 𝔹) ⇒ 𝔹 ⇒ 𝔹 ``

* `` ∅ , f ∶ 𝔹 ⇒ 𝔹 ⊢ (λ[ x ∶ 𝔹 ] ` f · (` f · ` x)) ∶  𝔹 ⇒ 𝔹 ``

* `` ∅ , f ∶ 𝔹 ⇒ 𝔹 , x ∶ 𝔹 ⊢ ` f · (` f · ` x) ∶  𝔹 ``

Environments are maps from free variables to types, built using `∅`
for the empty map, and `Γ , x ∶ A` for the map that extends
environment `Γ` by mapping variable `x` to type `A`.


<pre class="Agda">

<a name="20044" href="Stlc.html#20044" class="Function"
      >Context</a
      ><a name="20051"
      > </a
      ><a name="20052" class="Symbol"
      >:</a
      ><a name="20053"
      > </a
      ><a name="20054" class="PrimitiveType"
      >Set</a
      ><a name="20057"
      >
</a
      ><a name="20058" href="Stlc.html#20044" class="Function"
      >Context</a
      ><a name="20065"
      > </a
      ><a name="20066" class="Symbol"
      >=</a
      ><a name="20067"
      > </a
      ><a name="20068" href="Maps.html#10132" class="Function"
      >PartialMap</a
      ><a name="20078"
      > </a
      ><a name="20079" href="Stlc.html#2535" class="Datatype"
      >Type</a
      ><a name="20083"
      >

</a
      ><a name="20085" class="Keyword"
      >infix</a
      ><a name="20090"
      > </a
      ><a name="20091" class="Number"
      >10</a
      ><a name="20093"
      > </a
      ><a name="20094" href="Stlc.html#20106" class="Datatype Operator"
      >_&#8866;_&#8758;_</a
      ><a name="20099"
      >

</a
      ><a name="20101" class="Keyword"
      >data</a
      ><a name="20105"
      > </a
      ><a name="20106" href="Stlc.html#20106" class="Datatype Operator"
      >_&#8866;_&#8758;_</a
      ><a name="20111"
      > </a
      ><a name="20112" class="Symbol"
      >:</a
      ><a name="20113"
      > </a
      ><a name="20114" href="Stlc.html#20044" class="Function"
      >Context</a
      ><a name="20121"
      > </a
      ><a name="20122" class="Symbol"
      >&#8594;</a
      ><a name="20123"
      > </a
      ><a name="20124" href="Stlc.html#3608" class="Datatype"
      >Term</a
      ><a name="20128"
      > </a
      ><a name="20129" class="Symbol"
      >&#8594;</a
      ><a name="20130"
      > </a
      ><a name="20131" href="Stlc.html#2535" class="Datatype"
      >Type</a
      ><a name="20135"
      > </a
      ><a name="20136" class="Symbol"
      >&#8594;</a
      ><a name="20137"
      > </a
      ><a name="20138" class="PrimitiveType"
      >Set</a
      ><a name="20141"
      > </a
      ><a name="20142" class="Keyword"
      >where</a
      ><a name="20147"
      >
  </a
      ><a name="20150" href="Stlc.html#20150" class="InductiveConstructor"
      >Ax</a
      ><a name="20152"
      > </a
      ><a name="20153" class="Symbol"
      >:</a
      ><a name="20154"
      > </a
      ><a name="20155" class="Symbol"
      >&#8704;</a
      ><a name="20156"
      > </a
      ><a name="20157" class="Symbol"
      >{</a
      ><a name="20158" href="Stlc.html#20158" class="Bound"
      >&#915;</a
      ><a name="20159"
      > </a
      ><a name="20160" href="Stlc.html#20160" class="Bound"
      >x</a
      ><a name="20161"
      > </a
      ><a name="20162" href="Stlc.html#20162" class="Bound"
      >A</a
      ><a name="20163" class="Symbol"
      >}</a
      ><a name="20164"
      > </a
      ><a name="20165" class="Symbol"
      >&#8594;</a
      ><a name="20166"
      >
    </a
      ><a name="20171" href="Stlc.html#20158" class="Bound"
      >&#915;</a
      ><a name="20172"
      > </a
      ><a name="20173" href="Stlc.html#20160" class="Bound"
      >x</a
      ><a name="20174"
      > </a
      ><a name="20175" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="20176"
      > </a
      ><a name="20177" href="https://agda.github.io/agda-stdlib/Data.Maybe.Base.html#373" class="InductiveConstructor"
      >just</a
      ><a name="20181"
      > </a
      ><a name="20182" href="Stlc.html#20162" class="Bound"
      >A</a
      ><a name="20183"
      > </a
      ><a name="20184" class="Symbol"
      >&#8594;</a
      ><a name="20185"
      >
    </a
      ><a name="20190" href="Stlc.html#20158" class="Bound"
      >&#915;</a
      ><a name="20191"
      > </a
      ><a name="20192" href="Stlc.html#20106" class="Datatype Operator"
      >&#8866;</a
      ><a name="20193"
      > </a
      ><a name="20194" href="Stlc.html#3627" class="InductiveConstructor"
      >`</a
      ><a name="20195"
      > </a
      ><a name="20196" href="Stlc.html#20160" class="Bound"
      >x</a
      ><a name="20197"
      > </a
      ><a name="20198" href="Stlc.html#20106" class="Datatype Operator"
      >&#8758;</a
      ><a name="20199"
      > </a
      ><a name="20200" href="Stlc.html#20162" class="Bound"
      >A</a
      ><a name="20201"
      >
  </a
      ><a name="20204" href="Stlc.html#20204" class="InductiveConstructor"
      >&#8658;-I</a
      ><a name="20207"
      > </a
      ><a name="20208" class="Symbol"
      >:</a
      ><a name="20209"
      > </a
      ><a name="20210" class="Symbol"
      >&#8704;</a
      ><a name="20211"
      > </a
      ><a name="20212" class="Symbol"
      >{</a
      ><a name="20213" href="Stlc.html#20213" class="Bound"
      >&#915;</a
      ><a name="20214"
      > </a
      ><a name="20215" href="Stlc.html#20215" class="Bound"
      >x</a
      ><a name="20216"
      > </a
      ><a name="20217" href="Stlc.html#20217" class="Bound"
      >N</a
      ><a name="20218"
      > </a
      ><a name="20219" href="Stlc.html#20219" class="Bound"
      >A</a
      ><a name="20220"
      > </a
      ><a name="20221" href="Stlc.html#20221" class="Bound"
      >B</a
      ><a name="20222" class="Symbol"
      >}</a
      ><a name="20223"
      > </a
      ><a name="20224" class="Symbol"
      >&#8594;</a
      ><a name="20225"
      >
    </a
      ><a name="20230" href="Stlc.html#20213" class="Bound"
      >&#915;</a
      ><a name="20231"
      > </a
      ><a name="20232" href="Maps.html#10368" class="Function Operator"
      >,</a
      ><a name="20233"
      > </a
      ><a name="20234" href="Stlc.html#20215" class="Bound"
      >x</a
      ><a name="20235"
      > </a
      ><a name="20236" href="Maps.html#10368" class="Function Operator"
      >&#8758;</a
      ><a name="20237"
      > </a
      ><a name="20238" href="Stlc.html#20219" class="Bound"
      >A</a
      ><a name="20239"
      > </a
      ><a name="20240" href="Stlc.html#20106" class="Datatype Operator"
      >&#8866;</a
      ><a name="20241"
      > </a
      ><a name="20242" href="Stlc.html#20217" class="Bound"
      >N</a
      ><a name="20243"
      > </a
      ><a name="20244" href="Stlc.html#20106" class="Datatype Operator"
      >&#8758;</a
      ><a name="20245"
      > </a
      ><a name="20246" href="Stlc.html#20221" class="Bound"
      >B</a
      ><a name="20247"
      > </a
      ><a name="20248" class="Symbol"
      >&#8594;</a
      ><a name="20249"
      >
    </a
      ><a name="20254" href="Stlc.html#20213" class="Bound"
      >&#915;</a
      ><a name="20255"
      > </a
      ><a name="20256" href="Stlc.html#20106" class="Datatype Operator"
      >&#8866;</a
      ><a name="20257"
      > </a
      ><a name="20258" href="Stlc.html#3643" class="InductiveConstructor Operator"
      >&#955;[</a
      ><a name="20260"
      > </a
      ><a name="20261" href="Stlc.html#20215" class="Bound"
      >x</a
      ><a name="20262"
      > </a
      ><a name="20263" href="Stlc.html#3643" class="InductiveConstructor Operator"
      >&#8758;</a
      ><a name="20264"
      > </a
      ><a name="20265" href="Stlc.html#20219" class="Bound"
      >A</a
      ><a name="20266"
      > </a
      ><a name="20267" href="Stlc.html#3643" class="InductiveConstructor Operator"
      >]</a
      ><a name="20268"
      > </a
      ><a name="20269" href="Stlc.html#20217" class="Bound"
      >N</a
      ><a name="20270"
      > </a
      ><a name="20271" href="Stlc.html#20106" class="Datatype Operator"
      >&#8758;</a
      ><a name="20272"
      > </a
      ><a name="20273" href="Stlc.html#20219" class="Bound"
      >A</a
      ><a name="20274"
      > </a
      ><a name="20275" href="Stlc.html#2554" class="InductiveConstructor Operator"
      >&#8658;</a
      ><a name="20276"
      > </a
      ><a name="20277" href="Stlc.html#20221" class="Bound"
      >B</a
      ><a name="20278"
      >
  </a
      ><a name="20281" href="Stlc.html#20281" class="InductiveConstructor"
      >&#8658;-E</a
      ><a name="20284"
      > </a
      ><a name="20285" class="Symbol"
      >:</a
      ><a name="20286"
      > </a
      ><a name="20287" class="Symbol"
      >&#8704;</a
      ><a name="20288"
      > </a
      ><a name="20289" class="Symbol"
      >{</a
      ><a name="20290" href="Stlc.html#20290" class="Bound"
      >&#915;</a
      ><a name="20291"
      > </a
      ><a name="20292" href="Stlc.html#20292" class="Bound"
      >L</a
      ><a name="20293"
      > </a
      ><a name="20294" href="Stlc.html#20294" class="Bound"
      >M</a
      ><a name="20295"
      > </a
      ><a name="20296" href="Stlc.html#20296" class="Bound"
      >A</a
      ><a name="20297"
      > </a
      ><a name="20298" href="Stlc.html#20298" class="Bound"
      >B</a
      ><a name="20299" class="Symbol"
      >}</a
      ><a name="20300"
      > </a
      ><a name="20301" class="Symbol"
      >&#8594;</a
      ><a name="20302"
      >
    </a
      ><a name="20307" href="Stlc.html#20290" class="Bound"
      >&#915;</a
      ><a name="20308"
      > </a
      ><a name="20309" href="Stlc.html#20106" class="Datatype Operator"
      >&#8866;</a
      ><a name="20310"
      > </a
      ><a name="20311" href="Stlc.html#20292" class="Bound"
      >L</a
      ><a name="20312"
      > </a
      ><a name="20313" href="Stlc.html#20106" class="Datatype Operator"
      >&#8758;</a
      ><a name="20314"
      > </a
      ><a name="20315" href="Stlc.html#20296" class="Bound"
      >A</a
      ><a name="20316"
      > </a
      ><a name="20317" href="Stlc.html#2554" class="InductiveConstructor Operator"
      >&#8658;</a
      ><a name="20318"
      > </a
      ><a name="20319" href="Stlc.html#20298" class="Bound"
      >B</a
      ><a name="20320"
      > </a
      ><a name="20321" class="Symbol"
      >&#8594;</a
      ><a name="20322"
      >
    </a
      ><a name="20327" href="Stlc.html#20290" class="Bound"
      >&#915;</a
      ><a name="20328"
      > </a
      ><a name="20329" href="Stlc.html#20106" class="Datatype Operator"
      >&#8866;</a
      ><a name="20330"
      > </a
      ><a name="20331" href="Stlc.html#20294" class="Bound"
      >M</a
      ><a name="20332"
      > </a
      ><a name="20333" href="Stlc.html#20106" class="Datatype Operator"
      >&#8758;</a
      ><a name="20334"
      > </a
      ><a name="20335" href="Stlc.html#20296" class="Bound"
      >A</a
      ><a name="20336"
      > </a
      ><a name="20337" class="Symbol"
      >&#8594;</a
      ><a name="20338"
      >
    </a
      ><a name="20343" href="Stlc.html#20290" class="Bound"
      >&#915;</a
      ><a name="20344"
      > </a
      ><a name="20345" href="Stlc.html#20106" class="Datatype Operator"
      >&#8866;</a
      ><a name="20346"
      > </a
      ><a name="20347" href="Stlc.html#20292" class="Bound"
      >L</a
      ><a name="20348"
      > </a
      ><a name="20349" href="Stlc.html#3679" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="20350"
      > </a
      ><a name="20351" href="Stlc.html#20294" class="Bound"
      >M</a
      ><a name="20352"
      > </a
      ><a name="20353" href="Stlc.html#20106" class="Datatype Operator"
      >&#8758;</a
      ><a name="20354"
      > </a
      ><a name="20355" href="Stlc.html#20298" class="Bound"
      >B</a
      ><a name="20356"
      >
  </a
      ><a name="20359" href="Stlc.html#20359" class="InductiveConstructor"
      >&#120121;-I&#8321;</a
      ><a name="20363"
      > </a
      ><a name="20364" class="Symbol"
      >:</a
      ><a name="20365"
      > </a
      ><a name="20366" class="Symbol"
      >&#8704;</a
      ><a name="20367"
      > </a
      ><a name="20368" class="Symbol"
      >{</a
      ><a name="20369" href="Stlc.html#20369" class="Bound"
      >&#915;</a
      ><a name="20370" class="Symbol"
      >}</a
      ><a name="20371"
      > </a
      ><a name="20372" class="Symbol"
      >&#8594;</a
      ><a name="20373"
      >
    </a
      ><a name="20378" href="Stlc.html#20369" class="Bound"
      >&#915;</a
      ><a name="20379"
      > </a
      ><a name="20380" href="Stlc.html#20106" class="Datatype Operator"
      >&#8866;</a
      ><a name="20381"
      > </a
      ><a name="20382" href="Stlc.html#3706" class="InductiveConstructor"
      >true</a
      ><a name="20386"
      > </a
      ><a name="20387" href="Stlc.html#20106" class="Datatype Operator"
      >&#8758;</a
      ><a name="20388"
      > </a
      ><a name="20389" href="Stlc.html#2581" class="InductiveConstructor"
      >&#120121;</a
      ><a name="20390"
      >
  </a
      ><a name="20393" href="Stlc.html#20393" class="InductiveConstructor"
      >&#120121;-I&#8322;</a
      ><a name="20397"
      > </a
      ><a name="20398" class="Symbol"
      >:</a
      ><a name="20399"
      > </a
      ><a name="20400" class="Symbol"
      >&#8704;</a
      ><a name="20401"
      > </a
      ><a name="20402" class="Symbol"
      >{</a
      ><a name="20403" href="Stlc.html#20403" class="Bound"
      >&#915;</a
      ><a name="20404" class="Symbol"
      >}</a
      ><a name="20405"
      > </a
      ><a name="20406" class="Symbol"
      >&#8594;</a
      ><a name="20407"
      >
    </a
      ><a name="20412" href="Stlc.html#20403" class="Bound"
      >&#915;</a
      ><a name="20413"
      > </a
      ><a name="20414" href="Stlc.html#20106" class="Datatype Operator"
      >&#8866;</a
      ><a name="20415"
      > </a
      ><a name="20416" href="Stlc.html#3720" class="InductiveConstructor"
      >false</a
      ><a name="20421"
      > </a
      ><a name="20422" href="Stlc.html#20106" class="Datatype Operator"
      >&#8758;</a
      ><a name="20423"
      > </a
      ><a name="20424" href="Stlc.html#2581" class="InductiveConstructor"
      >&#120121;</a
      ><a name="20425"
      >
  </a
      ><a name="20428" href="Stlc.html#20428" class="InductiveConstructor"
      >&#120121;-E</a
      ><a name="20431"
      > </a
      ><a name="20432" class="Symbol"
      >:</a
      ><a name="20433"
      > </a
      ><a name="20434" class="Symbol"
      >&#8704;</a
      ><a name="20435"
      > </a
      ><a name="20436" class="Symbol"
      >{</a
      ><a name="20437" href="Stlc.html#20437" class="Bound"
      >&#915;</a
      ><a name="20438"
      > </a
      ><a name="20439" href="Stlc.html#20439" class="Bound"
      >L</a
      ><a name="20440"
      > </a
      ><a name="20441" href="Stlc.html#20441" class="Bound"
      >M</a
      ><a name="20442"
      > </a
      ><a name="20443" href="Stlc.html#20443" class="Bound"
      >N</a
      ><a name="20444"
      > </a
      ><a name="20445" href="Stlc.html#20445" class="Bound"
      >A</a
      ><a name="20446" class="Symbol"
      >}</a
      ><a name="20447"
      > </a
      ><a name="20448" class="Symbol"
      >&#8594;</a
      ><a name="20449"
      >
    </a
      ><a name="20454" href="Stlc.html#20437" class="Bound"
      >&#915;</a
      ><a name="20455"
      > </a
      ><a name="20456" href="Stlc.html#20106" class="Datatype Operator"
      >&#8866;</a
      ><a name="20457"
      > </a
      ><a name="20458" href="Stlc.html#20439" class="Bound"
      >L</a
      ><a name="20459"
      > </a
      ><a name="20460" href="Stlc.html#20106" class="Datatype Operator"
      >&#8758;</a
      ><a name="20461"
      > </a
      ><a name="20462" href="Stlc.html#2581" class="InductiveConstructor"
      >&#120121;</a
      ><a name="20463"
      > </a
      ><a name="20464" class="Symbol"
      >&#8594;</a
      ><a name="20465"
      >
    </a
      ><a name="20470" href="Stlc.html#20437" class="Bound"
      >&#915;</a
      ><a name="20471"
      > </a
      ><a name="20472" href="Stlc.html#20106" class="Datatype Operator"
      >&#8866;</a
      ><a name="20473"
      > </a
      ><a name="20474" href="Stlc.html#20441" class="Bound"
      >M</a
      ><a name="20475"
      > </a
      ><a name="20476" href="Stlc.html#20106" class="Datatype Operator"
      >&#8758;</a
      ><a name="20477"
      > </a
      ><a name="20478" href="Stlc.html#20445" class="Bound"
      >A</a
      ><a name="20479"
      > </a
      ><a name="20480" class="Symbol"
      >&#8594;</a
      ><a name="20481"
      >
    </a
      ><a name="20486" href="Stlc.html#20437" class="Bound"
      >&#915;</a
      ><a name="20487"
      > </a
      ><a name="20488" href="Stlc.html#20106" class="Datatype Operator"
      >&#8866;</a
      ><a name="20489"
      > </a
      ><a name="20490" href="Stlc.html#20443" class="Bound"
      >N</a
      ><a name="20491"
      > </a
      ><a name="20492" href="Stlc.html#20106" class="Datatype Operator"
      >&#8758;</a
      ><a name="20493"
      > </a
      ><a name="20494" href="Stlc.html#20445" class="Bound"
      >A</a
      ><a name="20495"
      > </a
      ><a name="20496" class="Symbol"
      >&#8594;</a
      ><a name="20497"
      >
    </a
      ><a name="20502" href="Stlc.html#20437" class="Bound"
      >&#915;</a
      ><a name="20503"
      > </a
      ><a name="20504" href="Stlc.html#20106" class="Datatype Operator"
      >&#8866;</a
      ><a name="20505"
      > </a
      ><a name="20506" href="Stlc.html#3735" class="InductiveConstructor Operator"
      >if</a
      ><a name="20508"
      > </a
      ><a name="20509" href="Stlc.html#20439" class="Bound"
      >L</a
      ><a name="20510"
      > </a
      ><a name="20511" href="Stlc.html#3735" class="InductiveConstructor Operator"
      >then</a
      ><a name="20515"
      > </a
      ><a name="20516" href="Stlc.html#20441" class="Bound"
      >M</a
      ><a name="20517"
      > </a
      ><a name="20518" href="Stlc.html#3735" class="InductiveConstructor Operator"
      >else</a
      ><a name="20522"
      > </a
      ><a name="20523" href="Stlc.html#20443" class="Bound"
      >N</a
      ><a name="20524"
      > </a
      ><a name="20525" href="Stlc.html#20106" class="Datatype Operator"
      >&#8758;</a
      ><a name="20526"
      > </a
      ><a name="20527" href="Stlc.html#20445" class="Bound"
      >A</a
      >

</pre>

## Example type derivations

<pre class="Agda">

<a name="20587" href="Stlc.html#20587" class="Function"
      >typing&#8321;</a
      ><a name="20594"
      > </a
      ><a name="20595" class="Symbol"
      >:</a
      ><a name="20596"
      > </a
      ><a name="20597" href="Maps.html#10265" class="Function"
      >&#8709;</a
      ><a name="20598"
      > </a
      ><a name="20599" href="Stlc.html#20106" class="Datatype Operator"
      >&#8866;</a
      ><a name="20600"
      > </a
      ><a name="20601" href="Stlc.html#5684" class="Function"
      >not</a
      ><a name="20604"
      > </a
      ><a name="20605" href="Stlc.html#20106" class="Datatype Operator"
      >&#8758;</a
      ><a name="20606"
      > </a
      ><a name="20607" href="Stlc.html#2581" class="InductiveConstructor"
      >&#120121;</a
      ><a name="20608"
      > </a
      ><a name="20609" href="Stlc.html#2554" class="InductiveConstructor Operator"
      >&#8658;</a
      ><a name="20610"
      > </a
      ><a name="20611" href="Stlc.html#2581" class="InductiveConstructor"
      >&#120121;</a
      ><a name="20612"
      >
</a
      ><a name="20613" href="Stlc.html#20587" class="Function"
      >typing&#8321;</a
      ><a name="20620"
      > </a
      ><a name="20621" class="Symbol"
      >=</a
      ><a name="20622"
      > </a
      ><a name="20623" href="Stlc.html#20204" class="InductiveConstructor"
      >&#8658;-I</a
      ><a name="20626"
      > </a
      ><a name="20627" class="Symbol"
      >(</a
      ><a name="20628" href="Stlc.html#20428" class="InductiveConstructor"
      >&#120121;-E</a
      ><a name="20631"
      > </a
      ><a name="20632" class="Symbol"
      >(</a
      ><a name="20633" href="Stlc.html#20150" class="InductiveConstructor"
      >Ax</a
      ><a name="20635"
      > </a
      ><a name="20636" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="20640" class="Symbol"
      >)</a
      ><a name="20641"
      > </a
      ><a name="20642" href="Stlc.html#20393" class="InductiveConstructor"
      >&#120121;-I&#8322;</a
      ><a name="20646"
      > </a
      ><a name="20647" href="Stlc.html#20359" class="InductiveConstructor"
      >&#120121;-I&#8321;</a
      ><a name="20651" class="Symbol"
      >)</a
      ><a name="20652"
      >

</a
      ><a name="20654" href="Stlc.html#20654" class="Function"
      >typing&#8322;</a
      ><a name="20661"
      > </a
      ><a name="20662" class="Symbol"
      >:</a
      ><a name="20663"
      > </a
      ><a name="20664" href="Maps.html#10265" class="Function"
      >&#8709;</a
      ><a name="20665"
      > </a
      ><a name="20666" href="Stlc.html#20106" class="Datatype Operator"
      >&#8866;</a
      ><a name="20667"
      > </a
      ><a name="20668" href="Stlc.html#5688" class="Function"
      >two</a
      ><a name="20671"
      > </a
      ><a name="20672" href="Stlc.html#20106" class="Datatype Operator"
      >&#8758;</a
      ><a name="20673"
      > </a
      ><a name="20674" class="Symbol"
      >(</a
      ><a name="20675" href="Stlc.html#2581" class="InductiveConstructor"
      >&#120121;</a
      ><a name="20676"
      > </a
      ><a name="20677" href="Stlc.html#2554" class="InductiveConstructor Operator"
      >&#8658;</a
      ><a name="20678"
      > </a
      ><a name="20679" href="Stlc.html#2581" class="InductiveConstructor"
      >&#120121;</a
      ><a name="20680" class="Symbol"
      >)</a
      ><a name="20681"
      > </a
      ><a name="20682" href="Stlc.html#2554" class="InductiveConstructor Operator"
      >&#8658;</a
      ><a name="20683"
      > </a
      ><a name="20684" href="Stlc.html#2581" class="InductiveConstructor"
      >&#120121;</a
      ><a name="20685"
      > </a
      ><a name="20686" href="Stlc.html#2554" class="InductiveConstructor Operator"
      >&#8658;</a
      ><a name="20687"
      > </a
      ><a name="20688" href="Stlc.html#2581" class="InductiveConstructor"
      >&#120121;</a
      ><a name="20689"
      >
</a
      ><a name="20690" href="Stlc.html#20654" class="Function"
      >typing&#8322;</a
      ><a name="20697"
      > </a
      ><a name="20698" class="Symbol"
      >=</a
      ><a name="20699"
      > </a
      ><a name="20700" href="Stlc.html#20204" class="InductiveConstructor"
      >&#8658;-I</a
      ><a name="20703"
      > </a
      ><a name="20704" class="Symbol"
      >(</a
      ><a name="20705" href="Stlc.html#20204" class="InductiveConstructor"
      >&#8658;-I</a
      ><a name="20708"
      > </a
      ><a name="20709" class="Symbol"
      >(</a
      ><a name="20710" href="Stlc.html#20281" class="InductiveConstructor"
      >&#8658;-E</a
      ><a name="20713"
      > </a
      ><a name="20714" class="Symbol"
      >(</a
      ><a name="20715" href="Stlc.html#20150" class="InductiveConstructor"
      >Ax</a
      ><a name="20717"
      > </a
      ><a name="20718" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="20722" class="Symbol"
      >)</a
      ><a name="20723"
      > </a
      ><a name="20724" class="Symbol"
      >(</a
      ><a name="20725" href="Stlc.html#20281" class="InductiveConstructor"
      >&#8658;-E</a
      ><a name="20728"
      > </a
      ><a name="20729" class="Symbol"
      >(</a
      ><a name="20730" href="Stlc.html#20150" class="InductiveConstructor"
      >Ax</a
      ><a name="20732"
      > </a
      ><a name="20733" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="20737" class="Symbol"
      >)</a
      ><a name="20738"
      > </a
      ><a name="20739" class="Symbol"
      >(</a
      ><a name="20740" href="Stlc.html#20150" class="InductiveConstructor"
      >Ax</a
      ><a name="20742"
      > </a
      ><a name="20743" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="20747" class="Symbol"
      >))))</a
      >

</pre>

Construction of a type derivation is best done interactively.
We start with the declaration:

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


