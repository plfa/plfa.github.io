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

<a name="5649" href="Stlc.html#5649" class="Function"
      >f</a
      ><a name="5650"
      > </a
      ><a name="5651" href="Stlc.html#5651" class="Function"
      >x</a
      ><a name="5652"
      > </a
      ><a name="5653" href="Stlc.html#5653" class="Function"
      >y</a
      ><a name="5654"
      > </a
      ><a name="5655" class="Symbol"
      >:</a
      ><a name="5656"
      > </a
      ><a name="5657" href="Maps.html#2171" class="Datatype"
      >Id</a
      ><a name="5659"
      >
</a
      ><a name="5660" href="Stlc.html#5649" class="Function"
      >f</a
      ><a name="5661"
      >  </a
      ><a name="5663" class="Symbol"
      >=</a
      ><a name="5664"
      >  </a
      ><a name="5666" href="Maps.html#2188" class="InductiveConstructor"
      >id</a
      ><a name="5668"
      > </a
      ><a name="5669" class="Number"
      >0</a
      ><a name="5670"
      >
</a
      ><a name="5671" href="Stlc.html#5651" class="Function"
      >x</a
      ><a name="5672"
      >  </a
      ><a name="5674" class="Symbol"
      >=</a
      ><a name="5675"
      >  </a
      ><a name="5677" href="Maps.html#2188" class="InductiveConstructor"
      >id</a
      ><a name="5679"
      > </a
      ><a name="5680" class="Number"
      >1</a
      ><a name="5681"
      >
</a
      ><a name="5682" href="Stlc.html#5653" class="Function"
      >y</a
      ><a name="5683"
      >  </a
      ><a name="5685" class="Symbol"
      >=</a
      ><a name="5686"
      >  </a
      ><a name="5688" href="Maps.html#2188" class="InductiveConstructor"
      >id</a
      ><a name="5690"
      > </a
      ><a name="5691" class="Number"
      >2</a
      ><a name="5692"
      >

</a
      ><a name="5694" href="Stlc.html#5694" class="Function"
      >not</a
      ><a name="5697"
      > </a
      ><a name="5698" href="Stlc.html#5698" class="Function"
      >two</a
      ><a name="5701"
      > </a
      ><a name="5702" class="Symbol"
      >:</a
      ><a name="5703"
      > </a
      ><a name="5704" href="Stlc.html#3608" class="Datatype"
      >Term</a
      ><a name="5708"
      > 
</a
      ><a name="5710" href="Stlc.html#5694" class="Function"
      >not</a
      ><a name="5713"
      > </a
      ><a name="5714" class="Symbol"
      >=</a
      ><a name="5715"
      >  </a
      ><a name="5717" href="Stlc.html#3643" class="InductiveConstructor Operator"
      >&#955;[</a
      ><a name="5719"
      > </a
      ><a name="5720" href="Stlc.html#5651" class="Function"
      >x</a
      ><a name="5721"
      > </a
      ><a name="5722" href="Stlc.html#3643" class="InductiveConstructor Operator"
      >&#8758;</a
      ><a name="5723"
      > </a
      ><a name="5724" href="Stlc.html#2581" class="InductiveConstructor"
      >&#120121;</a
      ><a name="5725"
      > </a
      ><a name="5726" href="Stlc.html#3643" class="InductiveConstructor Operator"
      >]</a
      ><a name="5727"
      > </a
      ><a name="5728" class="Symbol"
      >(</a
      ><a name="5729" href="Stlc.html#3735" class="InductiveConstructor Operator"
      >if</a
      ><a name="5731"
      > </a
      ><a name="5732" href="Stlc.html#3627" class="InductiveConstructor"
      >`</a
      ><a name="5733"
      > </a
      ><a name="5734" href="Stlc.html#5651" class="Function"
      >x</a
      ><a name="5735"
      > </a
      ><a name="5736" href="Stlc.html#3735" class="InductiveConstructor Operator"
      >then</a
      ><a name="5740"
      > </a
      ><a name="5741" href="Stlc.html#3720" class="InductiveConstructor"
      >false</a
      ><a name="5746"
      > </a
      ><a name="5747" href="Stlc.html#3735" class="InductiveConstructor Operator"
      >else</a
      ><a name="5751"
      > </a
      ><a name="5752" href="Stlc.html#3706" class="InductiveConstructor"
      >true</a
      ><a name="5756" class="Symbol"
      >)</a
      ><a name="5757"
      >
</a
      ><a name="5758" href="Stlc.html#5698" class="Function"
      >two</a
      ><a name="5761"
      > </a
      ><a name="5762" class="Symbol"
      >=</a
      ><a name="5763"
      >  </a
      ><a name="5765" href="Stlc.html#3643" class="InductiveConstructor Operator"
      >&#955;[</a
      ><a name="5767"
      > </a
      ><a name="5768" href="Stlc.html#5649" class="Function"
      >f</a
      ><a name="5769"
      > </a
      ><a name="5770" href="Stlc.html#3643" class="InductiveConstructor Operator"
      >&#8758;</a
      ><a name="5771"
      > </a
      ><a name="5772" href="Stlc.html#2581" class="InductiveConstructor"
      >&#120121;</a
      ><a name="5773"
      > </a
      ><a name="5774" href="Stlc.html#2554" class="InductiveConstructor Operator"
      >&#8658;</a
      ><a name="5775"
      > </a
      ><a name="5776" href="Stlc.html#2581" class="InductiveConstructor"
      >&#120121;</a
      ><a name="5777"
      > </a
      ><a name="5778" href="Stlc.html#3643" class="InductiveConstructor Operator"
      >]</a
      ><a name="5779"
      > </a
      ><a name="5780" href="Stlc.html#3643" class="InductiveConstructor Operator"
      >&#955;[</a
      ><a name="5782"
      > </a
      ><a name="5783" href="Stlc.html#5651" class="Function"
      >x</a
      ><a name="5784"
      > </a
      ><a name="5785" href="Stlc.html#3643" class="InductiveConstructor Operator"
      >&#8758;</a
      ><a name="5786"
      > </a
      ><a name="5787" href="Stlc.html#2581" class="InductiveConstructor"
      >&#120121;</a
      ><a name="5788"
      > </a
      ><a name="5789" href="Stlc.html#3643" class="InductiveConstructor Operator"
      >]</a
      ><a name="5790"
      > </a
      ><a name="5791" href="Stlc.html#3627" class="InductiveConstructor"
      >`</a
      ><a name="5792"
      > </a
      ><a name="5793" href="Stlc.html#5649" class="Function"
      >f</a
      ><a name="5794"
      > </a
      ><a name="5795" href="Stlc.html#3679" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="5796"
      > </a
      ><a name="5797" class="Symbol"
      >(</a
      ><a name="5798" href="Stlc.html#3627" class="InductiveConstructor"
      >`</a
      ><a name="5799"
      > </a
      ><a name="5800" href="Stlc.html#5649" class="Function"
      >f</a
      ><a name="5801"
      > </a
      ><a name="5802" href="Stlc.html#3679" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="5803"
      > </a
      ><a name="5804" href="Stlc.html#3627" class="InductiveConstructor"
      >`</a
      ><a name="5805"
      > </a
      ><a name="5806" href="Stlc.html#5651" class="Function"
      >x</a
      ><a name="5807" class="Symbol"
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

* `(𝔹 ⇒ 𝔹) ⇒ 𝔹 ⇒ 𝔹` abbreviates `(𝔹 ⇒ 𝔹) ⇒ (𝔹 ⇒ 𝔹)`
* `two · not · true` abbreviates `(two · not) · true`.

We choose the binding strength for abstractions and conditionals
to be weaker than application. For instance,

* `` λ[ f ∶ 𝔹 ⇒ 𝔹 ] λ[ x ∶ 𝔹 ] ` f · (` f · ` x) `` abbreviates
  `` (λ[ f ∶ 𝔹 ⇒ 𝔹 ] (λ[ x ∶ 𝔹 ] (` f · (` f · ` x)))) `` and not
  `` (λ[ f ∶ 𝔹 ⇒ 𝔹 ] (λ[ x ∶ 𝔹 ] ` f)) · (` f · ` x) ``.

<pre class="Agda">

<a name="8223" href="Stlc.html#8223" class="Function"
      >ex&#8321;</a
      ><a name="8226"
      > </a
      ><a name="8227" class="Symbol"
      >:</a
      ><a name="8228"
      > </a
      ><a name="8229" class="Symbol"
      >(</a
      ><a name="8230" href="Stlc.html#2581" class="InductiveConstructor"
      >&#120121;</a
      ><a name="8231"
      > </a
      ><a name="8232" href="Stlc.html#2554" class="InductiveConstructor Operator"
      >&#8658;</a
      ><a name="8233"
      > </a
      ><a name="8234" href="Stlc.html#2581" class="InductiveConstructor"
      >&#120121;</a
      ><a name="8235" class="Symbol"
      >)</a
      ><a name="8236"
      > </a
      ><a name="8237" href="Stlc.html#2554" class="InductiveConstructor Operator"
      >&#8658;</a
      ><a name="8238"
      > </a
      ><a name="8239" href="Stlc.html#2581" class="InductiveConstructor"
      >&#120121;</a
      ><a name="8240"
      > </a
      ><a name="8241" href="Stlc.html#2554" class="InductiveConstructor Operator"
      >&#8658;</a
      ><a name="8242"
      > </a
      ><a name="8243" href="Stlc.html#2581" class="InductiveConstructor"
      >&#120121;</a
      ><a name="8244"
      > </a
      ><a name="8245" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="8246"
      > </a
      ><a name="8247" class="Symbol"
      >(</a
      ><a name="8248" href="Stlc.html#2581" class="InductiveConstructor"
      >&#120121;</a
      ><a name="8249"
      > </a
      ><a name="8250" href="Stlc.html#2554" class="InductiveConstructor Operator"
      >&#8658;</a
      ><a name="8251"
      > </a
      ><a name="8252" href="Stlc.html#2581" class="InductiveConstructor"
      >&#120121;</a
      ><a name="8253" class="Symbol"
      >)</a
      ><a name="8254"
      > </a
      ><a name="8255" href="Stlc.html#2554" class="InductiveConstructor Operator"
      >&#8658;</a
      ><a name="8256"
      > </a
      ><a name="8257" class="Symbol"
      >(</a
      ><a name="8258" href="Stlc.html#2581" class="InductiveConstructor"
      >&#120121;</a
      ><a name="8259"
      > </a
      ><a name="8260" href="Stlc.html#2554" class="InductiveConstructor Operator"
      >&#8658;</a
      ><a name="8261"
      > </a
      ><a name="8262" href="Stlc.html#2581" class="InductiveConstructor"
      >&#120121;</a
      ><a name="8263" class="Symbol"
      >)</a
      ><a name="8264"
      >
</a
      ><a name="8265" href="Stlc.html#8223" class="Function"
      >ex&#8321;</a
      ><a name="8268"
      > </a
      ><a name="8269" class="Symbol"
      >=</a
      ><a name="8270"
      > </a
      ><a name="8271" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="8275"
      >

</a
      ><a name="8277" href="Stlc.html#8277" class="Function"
      >ex&#8322;</a
      ><a name="8280"
      > </a
      ><a name="8281" class="Symbol"
      >:</a
      ><a name="8282"
      > </a
      ><a name="8283" href="Stlc.html#5698" class="Function"
      >two</a
      ><a name="8286"
      > </a
      ><a name="8287" href="Stlc.html#3679" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="8288"
      > </a
      ><a name="8289" href="Stlc.html#5694" class="Function"
      >not</a
      ><a name="8292"
      > </a
      ><a name="8293" href="Stlc.html#3679" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="8294"
      > </a
      ><a name="8295" href="Stlc.html#3706" class="InductiveConstructor"
      >true</a
      ><a name="8299"
      > </a
      ><a name="8300" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="8301"
      > </a
      ><a name="8302" class="Symbol"
      >(</a
      ><a name="8303" href="Stlc.html#5698" class="Function"
      >two</a
      ><a name="8306"
      > </a
      ><a name="8307" href="Stlc.html#3679" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="8308"
      > </a
      ><a name="8309" href="Stlc.html#5694" class="Function"
      >not</a
      ><a name="8312" class="Symbol"
      >)</a
      ><a name="8313"
      > </a
      ><a name="8314" href="Stlc.html#3679" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="8315"
      > </a
      ><a name="8316" href="Stlc.html#3706" class="InductiveConstructor"
      >true</a
      ><a name="8320"
      >
</a
      ><a name="8321" href="Stlc.html#8277" class="Function"
      >ex&#8322;</a
      ><a name="8324"
      > </a
      ><a name="8325" class="Symbol"
      >=</a
      ><a name="8326"
      > </a
      ><a name="8327" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="8331"
      >

</a
      ><a name="8333" href="Stlc.html#8333" class="Function"
      >ex&#8323;</a
      ><a name="8336"
      > </a
      ><a name="8337" class="Symbol"
      >:</a
      ><a name="8338"
      > </a
      ><a name="8339" href="Stlc.html#3643" class="InductiveConstructor Operator"
      >&#955;[</a
      ><a name="8341"
      > </a
      ><a name="8342" href="Stlc.html#5649" class="Function"
      >f</a
      ><a name="8343"
      > </a
      ><a name="8344" href="Stlc.html#3643" class="InductiveConstructor Operator"
      >&#8758;</a
      ><a name="8345"
      > </a
      ><a name="8346" href="Stlc.html#2581" class="InductiveConstructor"
      >&#120121;</a
      ><a name="8347"
      > </a
      ><a name="8348" href="Stlc.html#2554" class="InductiveConstructor Operator"
      >&#8658;</a
      ><a name="8349"
      > </a
      ><a name="8350" href="Stlc.html#2581" class="InductiveConstructor"
      >&#120121;</a
      ><a name="8351"
      > </a
      ><a name="8352" href="Stlc.html#3643" class="InductiveConstructor Operator"
      >]</a
      ><a name="8353"
      > </a
      ><a name="8354" href="Stlc.html#3643" class="InductiveConstructor Operator"
      >&#955;[</a
      ><a name="8356"
      > </a
      ><a name="8357" href="Stlc.html#5651" class="Function"
      >x</a
      ><a name="8358"
      > </a
      ><a name="8359" href="Stlc.html#3643" class="InductiveConstructor Operator"
      >&#8758;</a
      ><a name="8360"
      > </a
      ><a name="8361" href="Stlc.html#2581" class="InductiveConstructor"
      >&#120121;</a
      ><a name="8362"
      > </a
      ><a name="8363" href="Stlc.html#3643" class="InductiveConstructor Operator"
      >]</a
      ><a name="8364"
      > </a
      ><a name="8365" href="Stlc.html#3627" class="InductiveConstructor"
      >`</a
      ><a name="8366"
      > </a
      ><a name="8367" href="Stlc.html#5649" class="Function"
      >f</a
      ><a name="8368"
      > </a
      ><a name="8369" href="Stlc.html#3679" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="8370"
      > </a
      ><a name="8371" class="Symbol"
      >(</a
      ><a name="8372" href="Stlc.html#3627" class="InductiveConstructor"
      >`</a
      ><a name="8373"
      > </a
      ><a name="8374" href="Stlc.html#5649" class="Function"
      >f</a
      ><a name="8375"
      > </a
      ><a name="8376" href="Stlc.html#3679" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="8377"
      > </a
      ><a name="8378" href="Stlc.html#3627" class="InductiveConstructor"
      >`</a
      ><a name="8379"
      > </a
      ><a name="8380" href="Stlc.html#5651" class="Function"
      >x</a
      ><a name="8381" class="Symbol"
      >)</a
      ><a name="8382"
      >
      </a
      ><a name="8389" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="8390"
      > </a
      ><a name="8391" class="Symbol"
      >(</a
      ><a name="8392" href="Stlc.html#3643" class="InductiveConstructor Operator"
      >&#955;[</a
      ><a name="8394"
      > </a
      ><a name="8395" href="Stlc.html#5649" class="Function"
      >f</a
      ><a name="8396"
      > </a
      ><a name="8397" href="Stlc.html#3643" class="InductiveConstructor Operator"
      >&#8758;</a
      ><a name="8398"
      > </a
      ><a name="8399" href="Stlc.html#2581" class="InductiveConstructor"
      >&#120121;</a
      ><a name="8400"
      > </a
      ><a name="8401" href="Stlc.html#2554" class="InductiveConstructor Operator"
      >&#8658;</a
      ><a name="8402"
      > </a
      ><a name="8403" href="Stlc.html#2581" class="InductiveConstructor"
      >&#120121;</a
      ><a name="8404"
      > </a
      ><a name="8405" href="Stlc.html#3643" class="InductiveConstructor Operator"
      >]</a
      ><a name="8406"
      > </a
      ><a name="8407" class="Symbol"
      >(</a
      ><a name="8408" href="Stlc.html#3643" class="InductiveConstructor Operator"
      >&#955;[</a
      ><a name="8410"
      > </a
      ><a name="8411" href="Stlc.html#5651" class="Function"
      >x</a
      ><a name="8412"
      > </a
      ><a name="8413" href="Stlc.html#3643" class="InductiveConstructor Operator"
      >&#8758;</a
      ><a name="8414"
      > </a
      ><a name="8415" href="Stlc.html#2581" class="InductiveConstructor"
      >&#120121;</a
      ><a name="8416"
      > </a
      ><a name="8417" href="Stlc.html#3643" class="InductiveConstructor Operator"
      >]</a
      ><a name="8418"
      > </a
      ><a name="8419" class="Symbol"
      >(</a
      ><a name="8420" href="Stlc.html#3627" class="InductiveConstructor"
      >`</a
      ><a name="8421"
      > </a
      ><a name="8422" href="Stlc.html#5649" class="Function"
      >f</a
      ><a name="8423"
      > </a
      ><a name="8424" href="Stlc.html#3679" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="8425"
      > </a
      ><a name="8426" class="Symbol"
      >(</a
      ><a name="8427" href="Stlc.html#3627" class="InductiveConstructor"
      >`</a
      ><a name="8428"
      > </a
      ><a name="8429" href="Stlc.html#5649" class="Function"
      >f</a
      ><a name="8430"
      > </a
      ><a name="8431" href="Stlc.html#3679" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="8432"
      > </a
      ><a name="8433" href="Stlc.html#3627" class="InductiveConstructor"
      >`</a
      ><a name="8434"
      > </a
      ><a name="8435" href="Stlc.html#5651" class="Function"
      >x</a
      ><a name="8436" class="Symbol"
      >))))</a
      ><a name="8440"
      >
</a
      ><a name="8441" href="Stlc.html#8333" class="Function"
      >ex&#8323;</a
      ><a name="8444"
      > </a
      ><a name="8445" class="Symbol"
      >=</a
      ><a name="8446"
      > </a
      ><a name="8447" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
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

<a name="9508" class="Keyword"
      >data</a
      ><a name="9512"
      > </a
      ><a name="9513" href="Stlc.html#9513" class="Datatype"
      >Value</a
      ><a name="9518"
      > </a
      ><a name="9519" class="Symbol"
      >:</a
      ><a name="9520"
      > </a
      ><a name="9521" href="Stlc.html#3608" class="Datatype"
      >Term</a
      ><a name="9525"
      > </a
      ><a name="9526" class="Symbol"
      >&#8594;</a
      ><a name="9527"
      > </a
      ><a name="9528" class="PrimitiveType"
      >Set</a
      ><a name="9531"
      > </a
      ><a name="9532" class="Keyword"
      >where</a
      ><a name="9537"
      >
  </a
      ><a name="9540" href="Stlc.html#9540" class="InductiveConstructor"
      >value-&#955;</a
      ><a name="9547"
      >     </a
      ><a name="9552" class="Symbol"
      >:</a
      ><a name="9553"
      > </a
      ><a name="9554" class="Symbol"
      >&#8704;</a
      ><a name="9555"
      > </a
      ><a name="9556" class="Symbol"
      >{</a
      ><a name="9557" href="Stlc.html#9557" class="Bound"
      >x</a
      ><a name="9558"
      > </a
      ><a name="9559" href="Stlc.html#9559" class="Bound"
      >A</a
      ><a name="9560"
      > </a
      ><a name="9561" href="Stlc.html#9561" class="Bound"
      >N</a
      ><a name="9562" class="Symbol"
      >}</a
      ><a name="9563"
      > </a
      ><a name="9564" class="Symbol"
      >&#8594;</a
      ><a name="9565"
      > </a
      ><a name="9566" href="Stlc.html#9513" class="Datatype"
      >Value</a
      ><a name="9571"
      > </a
      ><a name="9572" class="Symbol"
      >(</a
      ><a name="9573" href="Stlc.html#3643" class="InductiveConstructor Operator"
      >&#955;[</a
      ><a name="9575"
      > </a
      ><a name="9576" href="Stlc.html#9557" class="Bound"
      >x</a
      ><a name="9577"
      > </a
      ><a name="9578" href="Stlc.html#3643" class="InductiveConstructor Operator"
      >&#8758;</a
      ><a name="9579"
      > </a
      ><a name="9580" href="Stlc.html#9559" class="Bound"
      >A</a
      ><a name="9581"
      > </a
      ><a name="9582" href="Stlc.html#3643" class="InductiveConstructor Operator"
      >]</a
      ><a name="9583"
      > </a
      ><a name="9584" href="Stlc.html#9561" class="Bound"
      >N</a
      ><a name="9585" class="Symbol"
      >)</a
      ><a name="9586"
      >
  </a
      ><a name="9589" href="Stlc.html#9589" class="InductiveConstructor"
      >value-true</a
      ><a name="9599"
      >  </a
      ><a name="9601" class="Symbol"
      >:</a
      ><a name="9602"
      > </a
      ><a name="9603" href="Stlc.html#9513" class="Datatype"
      >Value</a
      ><a name="9608"
      > </a
      ><a name="9609" href="Stlc.html#3706" class="InductiveConstructor"
      >true</a
      ><a name="9613"
      >
  </a
      ><a name="9616" href="Stlc.html#9616" class="InductiveConstructor"
      >value-false</a
      ><a name="9627"
      > </a
      ><a name="9628" class="Symbol"
      >:</a
      ><a name="9629"
      > </a
      ><a name="9630" href="Stlc.html#9513" class="Datatype"
      >Value</a
      ><a name="9635"
      > </a
      ><a name="9636" href="Stlc.html#3720" class="InductiveConstructor"
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

<a name="12057" href="Stlc.html#12057" class="Function Operator"
      >_[_:=_]</a
      ><a name="12064"
      > </a
      ><a name="12065" class="Symbol"
      >:</a
      ><a name="12066"
      > </a
      ><a name="12067" href="Stlc.html#3608" class="Datatype"
      >Term</a
      ><a name="12071"
      > </a
      ><a name="12072" class="Symbol"
      >&#8594;</a
      ><a name="12073"
      > </a
      ><a name="12074" href="Maps.html#2171" class="Datatype"
      >Id</a
      ><a name="12076"
      > </a
      ><a name="12077" class="Symbol"
      >&#8594;</a
      ><a name="12078"
      > </a
      ><a name="12079" href="Stlc.html#3608" class="Datatype"
      >Term</a
      ><a name="12083"
      > </a
      ><a name="12084" class="Symbol"
      >&#8594;</a
      ><a name="12085"
      > </a
      ><a name="12086" href="Stlc.html#3608" class="Datatype"
      >Term</a
      ><a name="12090"
      >
</a
      ><a name="12091" class="Symbol"
      >(</a
      ><a name="12092" href="Stlc.html#3627" class="InductiveConstructor"
      >`</a
      ><a name="12093"
      > </a
      ><a name="12094" href="Stlc.html#12094" class="Bound"
      >x&#8242;</a
      ><a name="12096" class="Symbol"
      >)</a
      ><a name="12097"
      > </a
      ><a name="12098" href="Stlc.html#12057" class="Function Operator"
      >[</a
      ><a name="12099"
      > </a
      ><a name="12100" href="Stlc.html#12100" class="Bound"
      >x</a
      ><a name="12101"
      > </a
      ><a name="12102" href="Stlc.html#12057" class="Function Operator"
      >:=</a
      ><a name="12104"
      > </a
      ><a name="12105" href="Stlc.html#12105" class="Bound"
      >V</a
      ><a name="12106"
      > </a
      ><a name="12107" href="Stlc.html#12057" class="Function Operator"
      >]</a
      ><a name="12108"
      > </a
      ><a name="12109" class="Keyword"
      >with</a
      ><a name="12113"
      > </a
      ><a name="12114" href="Stlc.html#12100" class="Bound"
      >x</a
      ><a name="12115"
      > </a
      ><a name="12116" href="Maps.html#2509" class="Function Operator"
      >&#8799;</a
      ><a name="12117"
      > </a
      ><a name="12118" href="Stlc.html#12094" class="Bound"
      >x&#8242;</a
      ><a name="12120"
      >
</a
      ><a name="12121" class="Symbol"
      >...</a
      ><a name="12124"
      > </a
      ><a name="12125" class="Symbol"
      >|</a
      ><a name="12126"
      > </a
      ><a name="12127" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#520" class="InductiveConstructor"
      >yes</a
      ><a name="12130"
      > </a
      ><a name="12131" class="Symbol"
      >_</a
      ><a name="12132"
      > </a
      ><a name="12133" class="Symbol"
      >=</a
      ><a name="12134"
      > </a
      ><a name="12135" href="Stlc.html#12105" class="Bound"
      >V</a
      ><a name="12136"
      >
</a
      ><a name="12137" class="Symbol"
      >...</a
      ><a name="12140"
      > </a
      ><a name="12141" class="Symbol"
      >|</a
      ><a name="12142"
      > </a
      ><a name="12143" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#547" class="InductiveConstructor"
      >no</a
      ><a name="12145"
      >  </a
      ><a name="12147" class="Symbol"
      >_</a
      ><a name="12148"
      > </a
      ><a name="12149" class="Symbol"
      >=</a
      ><a name="12150"
      > </a
      ><a name="12151" href="Stlc.html#3627" class="InductiveConstructor"
      >`</a
      ><a name="12152"
      > </a
      ><a name="12153" href="Stlc.html#12094" class="Bound"
      >x&#8242;</a
      ><a name="12155"
      >
</a
      ><a name="12156" class="Symbol"
      >(</a
      ><a name="12157" href="Stlc.html#3643" class="InductiveConstructor Operator"
      >&#955;[</a
      ><a name="12159"
      > </a
      ><a name="12160" href="Stlc.html#12160" class="Bound"
      >x&#8242;</a
      ><a name="12162"
      > </a
      ><a name="12163" href="Stlc.html#3643" class="InductiveConstructor Operator"
      >&#8758;</a
      ><a name="12164"
      > </a
      ><a name="12165" href="Stlc.html#12165" class="Bound"
      >A&#8242;</a
      ><a name="12167"
      > </a
      ><a name="12168" href="Stlc.html#3643" class="InductiveConstructor Operator"
      >]</a
      ><a name="12169"
      > </a
      ><a name="12170" href="Stlc.html#12170" class="Bound"
      >N&#8242;</a
      ><a name="12172" class="Symbol"
      >)</a
      ><a name="12173"
      > </a
      ><a name="12174" href="Stlc.html#12057" class="Function Operator"
      >[</a
      ><a name="12175"
      > </a
      ><a name="12176" href="Stlc.html#12176" class="Bound"
      >x</a
      ><a name="12177"
      > </a
      ><a name="12178" href="Stlc.html#12057" class="Function Operator"
      >:=</a
      ><a name="12180"
      > </a
      ><a name="12181" href="Stlc.html#12181" class="Bound"
      >V</a
      ><a name="12182"
      > </a
      ><a name="12183" href="Stlc.html#12057" class="Function Operator"
      >]</a
      ><a name="12184"
      > </a
      ><a name="12185" class="Keyword"
      >with</a
      ><a name="12189"
      > </a
      ><a name="12190" href="Stlc.html#12176" class="Bound"
      >x</a
      ><a name="12191"
      > </a
      ><a name="12192" href="Maps.html#2509" class="Function Operator"
      >&#8799;</a
      ><a name="12193"
      > </a
      ><a name="12194" href="Stlc.html#12160" class="Bound"
      >x&#8242;</a
      ><a name="12196"
      >
</a
      ><a name="12197" class="Symbol"
      >...</a
      ><a name="12200"
      > </a
      ><a name="12201" class="Symbol"
      >|</a
      ><a name="12202"
      > </a
      ><a name="12203" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#520" class="InductiveConstructor"
      >yes</a
      ><a name="12206"
      > </a
      ><a name="12207" class="Symbol"
      >_</a
      ><a name="12208"
      > </a
      ><a name="12209" class="Symbol"
      >=</a
      ><a name="12210"
      > </a
      ><a name="12211" href="Stlc.html#3643" class="InductiveConstructor Operator"
      >&#955;[</a
      ><a name="12213"
      > </a
      ><a name="12214" href="Stlc.html#12160" class="Bound"
      >x&#8242;</a
      ><a name="12216"
      > </a
      ><a name="12217" href="Stlc.html#3643" class="InductiveConstructor Operator"
      >&#8758;</a
      ><a name="12218"
      > </a
      ><a name="12219" href="Stlc.html#12165" class="Bound"
      >A&#8242;</a
      ><a name="12221"
      > </a
      ><a name="12222" href="Stlc.html#3643" class="InductiveConstructor Operator"
      >]</a
      ><a name="12223"
      > </a
      ><a name="12224" href="Stlc.html#12170" class="Bound"
      >N&#8242;</a
      ><a name="12226"
      >
</a
      ><a name="12227" class="Symbol"
      >...</a
      ><a name="12230"
      > </a
      ><a name="12231" class="Symbol"
      >|</a
      ><a name="12232"
      > </a
      ><a name="12233" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#547" class="InductiveConstructor"
      >no</a
      ><a name="12235"
      >  </a
      ><a name="12237" class="Symbol"
      >_</a
      ><a name="12238"
      > </a
      ><a name="12239" class="Symbol"
      >=</a
      ><a name="12240"
      > </a
      ><a name="12241" href="Stlc.html#3643" class="InductiveConstructor Operator"
      >&#955;[</a
      ><a name="12243"
      > </a
      ><a name="12244" href="Stlc.html#12160" class="Bound"
      >x&#8242;</a
      ><a name="12246"
      > </a
      ><a name="12247" href="Stlc.html#3643" class="InductiveConstructor Operator"
      >&#8758;</a
      ><a name="12248"
      > </a
      ><a name="12249" href="Stlc.html#12165" class="Bound"
      >A&#8242;</a
      ><a name="12251"
      > </a
      ><a name="12252" href="Stlc.html#3643" class="InductiveConstructor Operator"
      >]</a
      ><a name="12253"
      > </a
      ><a name="12254" class="Symbol"
      >(</a
      ><a name="12255" href="Stlc.html#12170" class="Bound"
      >N&#8242;</a
      ><a name="12257"
      > </a
      ><a name="12258" href="Stlc.html#12057" class="Function Operator"
      >[</a
      ><a name="12259"
      > </a
      ><a name="12260" href="Stlc.html#12176" class="Bound"
      >x</a
      ><a name="12261"
      > </a
      ><a name="12262" href="Stlc.html#12057" class="Function Operator"
      >:=</a
      ><a name="12264"
      > </a
      ><a name="12265" href="Stlc.html#12181" class="Bound"
      >V</a
      ><a name="12266"
      > </a
      ><a name="12267" href="Stlc.html#12057" class="Function Operator"
      >]</a
      ><a name="12268" class="Symbol"
      >)</a
      ><a name="12269"
      >
</a
      ><a name="12270" class="Symbol"
      >(</a
      ><a name="12271" href="Stlc.html#12271" class="Bound"
      >L&#8242;</a
      ><a name="12273"
      > </a
      ><a name="12274" href="Stlc.html#3679" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="12275"
      > </a
      ><a name="12276" href="Stlc.html#12276" class="Bound"
      >M&#8242;</a
      ><a name="12278" class="Symbol"
      >)</a
      ><a name="12279"
      > </a
      ><a name="12280" href="Stlc.html#12057" class="Function Operator"
      >[</a
      ><a name="12281"
      > </a
      ><a name="12282" href="Stlc.html#12282" class="Bound"
      >x</a
      ><a name="12283"
      > </a
      ><a name="12284" href="Stlc.html#12057" class="Function Operator"
      >:=</a
      ><a name="12286"
      > </a
      ><a name="12287" href="Stlc.html#12287" class="Bound"
      >V</a
      ><a name="12288"
      > </a
      ><a name="12289" href="Stlc.html#12057" class="Function Operator"
      >]</a
      ><a name="12290"
      > </a
      ><a name="12291" class="Symbol"
      >=</a
      ><a name="12292"
      >  </a
      ><a name="12294" class="Symbol"
      >(</a
      ><a name="12295" href="Stlc.html#12271" class="Bound"
      >L&#8242;</a
      ><a name="12297"
      > </a
      ><a name="12298" href="Stlc.html#12057" class="Function Operator"
      >[</a
      ><a name="12299"
      > </a
      ><a name="12300" href="Stlc.html#12282" class="Bound"
      >x</a
      ><a name="12301"
      > </a
      ><a name="12302" href="Stlc.html#12057" class="Function Operator"
      >:=</a
      ><a name="12304"
      > </a
      ><a name="12305" href="Stlc.html#12287" class="Bound"
      >V</a
      ><a name="12306"
      > </a
      ><a name="12307" href="Stlc.html#12057" class="Function Operator"
      >]</a
      ><a name="12308" class="Symbol"
      >)</a
      ><a name="12309"
      > </a
      ><a name="12310" href="Stlc.html#3679" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="12311"
      > </a
      ><a name="12312" class="Symbol"
      >(</a
      ><a name="12313" href="Stlc.html#12276" class="Bound"
      >M&#8242;</a
      ><a name="12315"
      > </a
      ><a name="12316" href="Stlc.html#12057" class="Function Operator"
      >[</a
      ><a name="12317"
      > </a
      ><a name="12318" href="Stlc.html#12282" class="Bound"
      >x</a
      ><a name="12319"
      > </a
      ><a name="12320" href="Stlc.html#12057" class="Function Operator"
      >:=</a
      ><a name="12322"
      > </a
      ><a name="12323" href="Stlc.html#12287" class="Bound"
      >V</a
      ><a name="12324"
      > </a
      ><a name="12325" href="Stlc.html#12057" class="Function Operator"
      >]</a
      ><a name="12326" class="Symbol"
      >)</a
      ><a name="12327"
      >
</a
      ><a name="12328" class="Symbol"
      >(</a
      ><a name="12329" href="Stlc.html#3706" class="InductiveConstructor"
      >true</a
      ><a name="12333" class="Symbol"
      >)</a
      ><a name="12334"
      > </a
      ><a name="12335" href="Stlc.html#12057" class="Function Operator"
      >[</a
      ><a name="12336"
      > </a
      ><a name="12337" href="Stlc.html#12337" class="Bound"
      >x</a
      ><a name="12338"
      > </a
      ><a name="12339" href="Stlc.html#12057" class="Function Operator"
      >:=</a
      ><a name="12341"
      > </a
      ><a name="12342" href="Stlc.html#12342" class="Bound"
      >V</a
      ><a name="12343"
      > </a
      ><a name="12344" href="Stlc.html#12057" class="Function Operator"
      >]</a
      ><a name="12345"
      > </a
      ><a name="12346" class="Symbol"
      >=</a
      ><a name="12347"
      > </a
      ><a name="12348" href="Stlc.html#3706" class="InductiveConstructor"
      >true</a
      ><a name="12352"
      >
</a
      ><a name="12353" class="Symbol"
      >(</a
      ><a name="12354" href="Stlc.html#3720" class="InductiveConstructor"
      >false</a
      ><a name="12359" class="Symbol"
      >)</a
      ><a name="12360"
      > </a
      ><a name="12361" href="Stlc.html#12057" class="Function Operator"
      >[</a
      ><a name="12362"
      > </a
      ><a name="12363" href="Stlc.html#12363" class="Bound"
      >x</a
      ><a name="12364"
      > </a
      ><a name="12365" href="Stlc.html#12057" class="Function Operator"
      >:=</a
      ><a name="12367"
      > </a
      ><a name="12368" href="Stlc.html#12368" class="Bound"
      >V</a
      ><a name="12369"
      > </a
      ><a name="12370" href="Stlc.html#12057" class="Function Operator"
      >]</a
      ><a name="12371"
      > </a
      ><a name="12372" class="Symbol"
      >=</a
      ><a name="12373"
      > </a
      ><a name="12374" href="Stlc.html#3720" class="InductiveConstructor"
      >false</a
      ><a name="12379"
      >
</a
      ><a name="12380" class="Symbol"
      >(</a
      ><a name="12381" href="Stlc.html#3735" class="InductiveConstructor Operator"
      >if</a
      ><a name="12383"
      > </a
      ><a name="12384" href="Stlc.html#12384" class="Bound"
      >L&#8242;</a
      ><a name="12386"
      > </a
      ><a name="12387" href="Stlc.html#3735" class="InductiveConstructor Operator"
      >then</a
      ><a name="12391"
      > </a
      ><a name="12392" href="Stlc.html#12392" class="Bound"
      >M&#8242;</a
      ><a name="12394"
      > </a
      ><a name="12395" href="Stlc.html#3735" class="InductiveConstructor Operator"
      >else</a
      ><a name="12399"
      > </a
      ><a name="12400" href="Stlc.html#12400" class="Bound"
      >N&#8242;</a
      ><a name="12402" class="Symbol"
      >)</a
      ><a name="12403"
      > </a
      ><a name="12404" href="Stlc.html#12057" class="Function Operator"
      >[</a
      ><a name="12405"
      > </a
      ><a name="12406" href="Stlc.html#12406" class="Bound"
      >x</a
      ><a name="12407"
      > </a
      ><a name="12408" href="Stlc.html#12057" class="Function Operator"
      >:=</a
      ><a name="12410"
      > </a
      ><a name="12411" href="Stlc.html#12411" class="Bound"
      >V</a
      ><a name="12412"
      > </a
      ><a name="12413" href="Stlc.html#12057" class="Function Operator"
      >]</a
      ><a name="12414"
      > </a
      ><a name="12415" class="Symbol"
      >=</a
      ><a name="12416"
      >
  </a
      ><a name="12419" href="Stlc.html#3735" class="InductiveConstructor Operator"
      >if</a
      ><a name="12421"
      > </a
      ><a name="12422" class="Symbol"
      >(</a
      ><a name="12423" href="Stlc.html#12384" class="Bound"
      >L&#8242;</a
      ><a name="12425"
      > </a
      ><a name="12426" href="Stlc.html#12057" class="Function Operator"
      >[</a
      ><a name="12427"
      > </a
      ><a name="12428" href="Stlc.html#12406" class="Bound"
      >x</a
      ><a name="12429"
      > </a
      ><a name="12430" href="Stlc.html#12057" class="Function Operator"
      >:=</a
      ><a name="12432"
      > </a
      ><a name="12433" href="Stlc.html#12411" class="Bound"
      >V</a
      ><a name="12434"
      > </a
      ><a name="12435" href="Stlc.html#12057" class="Function Operator"
      >]</a
      ><a name="12436" class="Symbol"
      >)</a
      ><a name="12437"
      > </a
      ><a name="12438" href="Stlc.html#3735" class="InductiveConstructor Operator"
      >then</a
      ><a name="12442"
      > </a
      ><a name="12443" class="Symbol"
      >(</a
      ><a name="12444" href="Stlc.html#12392" class="Bound"
      >M&#8242;</a
      ><a name="12446"
      > </a
      ><a name="12447" href="Stlc.html#12057" class="Function Operator"
      >[</a
      ><a name="12448"
      > </a
      ><a name="12449" href="Stlc.html#12406" class="Bound"
      >x</a
      ><a name="12450"
      > </a
      ><a name="12451" href="Stlc.html#12057" class="Function Operator"
      >:=</a
      ><a name="12453"
      > </a
      ><a name="12454" href="Stlc.html#12411" class="Bound"
      >V</a
      ><a name="12455"
      > </a
      ><a name="12456" href="Stlc.html#12057" class="Function Operator"
      >]</a
      ><a name="12457" class="Symbol"
      >)</a
      ><a name="12458"
      > </a
      ><a name="12459" href="Stlc.html#3735" class="InductiveConstructor Operator"
      >else</a
      ><a name="12463"
      > </a
      ><a name="12464" class="Symbol"
      >(</a
      ><a name="12465" href="Stlc.html#12400" class="Bound"
      >N&#8242;</a
      ><a name="12467"
      > </a
      ><a name="12468" href="Stlc.html#12057" class="Function Operator"
      >[</a
      ><a name="12469"
      > </a
      ><a name="12470" href="Stlc.html#12406" class="Bound"
      >x</a
      ><a name="12471"
      > </a
      ><a name="12472" href="Stlc.html#12057" class="Function Operator"
      >:=</a
      ><a name="12474"
      > </a
      ><a name="12475" href="Stlc.html#12411" class="Bound"
      >V</a
      ><a name="12476"
      > </a
      ><a name="12477" href="Stlc.html#12057" class="Function Operator"
      >]</a
      ><a name="12478" class="Symbol"
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

<a name="13228" href="Stlc.html#13228" class="Function"
      >ex&#8321;&#8321;</a
      ><a name="13232"
      > </a
      ><a name="13233" class="Symbol"
      >:</a
      ><a name="13234"
      > </a
      ><a name="13235" href="Stlc.html#3627" class="InductiveConstructor"
      >`</a
      ><a name="13236"
      > </a
      ><a name="13237" href="Stlc.html#5649" class="Function"
      >f</a
      ><a name="13238"
      > </a
      ><a name="13239" href="Stlc.html#12057" class="Function Operator"
      >[</a
      ><a name="13240"
      > </a
      ><a name="13241" href="Stlc.html#5649" class="Function"
      >f</a
      ><a name="13242"
      > </a
      ><a name="13243" href="Stlc.html#12057" class="Function Operator"
      >:=</a
      ><a name="13245"
      > </a
      ><a name="13246" href="Stlc.html#5694" class="Function"
      >not</a
      ><a name="13249"
      > </a
      ><a name="13250" href="Stlc.html#12057" class="Function Operator"
      >]</a
      ><a name="13251"
      > </a
      ><a name="13252" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="13253"
      >  </a
      ><a name="13255" href="Stlc.html#5694" class="Function"
      >not</a
      ><a name="13258"
      >
</a
      ><a name="13259" href="Stlc.html#13228" class="Function"
      >ex&#8321;&#8321;</a
      ><a name="13263"
      > </a
      ><a name="13264" class="Symbol"
      >=</a
      ><a name="13265"
      > </a
      ><a name="13266" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="13270"
      >

</a
      ><a name="13272" href="Stlc.html#13272" class="Function"
      >ex&#8321;&#8322;</a
      ><a name="13276"
      > </a
      ><a name="13277" class="Symbol"
      >:</a
      ><a name="13278"
      > </a
      ><a name="13279" href="Stlc.html#3706" class="InductiveConstructor"
      >true</a
      ><a name="13283"
      > </a
      ><a name="13284" href="Stlc.html#12057" class="Function Operator"
      >[</a
      ><a name="13285"
      > </a
      ><a name="13286" href="Stlc.html#5649" class="Function"
      >f</a
      ><a name="13287"
      > </a
      ><a name="13288" href="Stlc.html#12057" class="Function Operator"
      >:=</a
      ><a name="13290"
      > </a
      ><a name="13291" href="Stlc.html#5694" class="Function"
      >not</a
      ><a name="13294"
      > </a
      ><a name="13295" href="Stlc.html#12057" class="Function Operator"
      >]</a
      ><a name="13296"
      > </a
      ><a name="13297" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="13298"
      > </a
      ><a name="13299" href="Stlc.html#3706" class="InductiveConstructor"
      >true</a
      ><a name="13303"
      >
</a
      ><a name="13304" href="Stlc.html#13272" class="Function"
      >ex&#8321;&#8322;</a
      ><a name="13308"
      > </a
      ><a name="13309" class="Symbol"
      >=</a
      ><a name="13310"
      > </a
      ><a name="13311" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="13315"
      >

</a
      ><a name="13317" href="Stlc.html#13317" class="Function"
      >ex&#8321;&#8323;</a
      ><a name="13321"
      > </a
      ><a name="13322" class="Symbol"
      >:</a
      ><a name="13323"
      > </a
      ><a name="13324" class="Symbol"
      >(</a
      ><a name="13325" href="Stlc.html#3627" class="InductiveConstructor"
      >`</a
      ><a name="13326"
      > </a
      ><a name="13327" href="Stlc.html#5649" class="Function"
      >f</a
      ><a name="13328"
      > </a
      ><a name="13329" href="Stlc.html#3679" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="13330"
      > </a
      ><a name="13331" href="Stlc.html#3706" class="InductiveConstructor"
      >true</a
      ><a name="13335" class="Symbol"
      >)</a
      ><a name="13336"
      > </a
      ><a name="13337" href="Stlc.html#12057" class="Function Operator"
      >[</a
      ><a name="13338"
      > </a
      ><a name="13339" href="Stlc.html#5649" class="Function"
      >f</a
      ><a name="13340"
      > </a
      ><a name="13341" href="Stlc.html#12057" class="Function Operator"
      >:=</a
      ><a name="13343"
      > </a
      ><a name="13344" href="Stlc.html#5694" class="Function"
      >not</a
      ><a name="13347"
      > </a
      ><a name="13348" href="Stlc.html#12057" class="Function Operator"
      >]</a
      ><a name="13349"
      > </a
      ><a name="13350" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="13351"
      > </a
      ><a name="13352" href="Stlc.html#5694" class="Function"
      >not</a
      ><a name="13355"
      > </a
      ><a name="13356" href="Stlc.html#3679" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="13357"
      > </a
      ><a name="13358" href="Stlc.html#3706" class="InductiveConstructor"
      >true</a
      ><a name="13362"
      >
</a
      ><a name="13363" href="Stlc.html#13317" class="Function"
      >ex&#8321;&#8323;</a
      ><a name="13367"
      > </a
      ><a name="13368" class="Symbol"
      >=</a
      ><a name="13369"
      > </a
      ><a name="13370" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="13374"
      >

</a
      ><a name="13376" href="Stlc.html#13376" class="Function"
      >ex&#8321;&#8324;</a
      ><a name="13380"
      > </a
      ><a name="13381" class="Symbol"
      >:</a
      ><a name="13382"
      > </a
      ><a name="13383" class="Symbol"
      >(</a
      ><a name="13384" href="Stlc.html#3627" class="InductiveConstructor"
      >`</a
      ><a name="13385"
      > </a
      ><a name="13386" href="Stlc.html#5649" class="Function"
      >f</a
      ><a name="13387"
      > </a
      ><a name="13388" href="Stlc.html#3679" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="13389"
      > </a
      ><a name="13390" class="Symbol"
      >(</a
      ><a name="13391" href="Stlc.html#3627" class="InductiveConstructor"
      >`</a
      ><a name="13392"
      > </a
      ><a name="13393" href="Stlc.html#5649" class="Function"
      >f</a
      ><a name="13394"
      > </a
      ><a name="13395" href="Stlc.html#3679" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="13396"
      > </a
      ><a name="13397" href="Stlc.html#3706" class="InductiveConstructor"
      >true</a
      ><a name="13401" class="Symbol"
      >))</a
      ><a name="13403"
      > </a
      ><a name="13404" href="Stlc.html#12057" class="Function Operator"
      >[</a
      ><a name="13405"
      > </a
      ><a name="13406" href="Stlc.html#5649" class="Function"
      >f</a
      ><a name="13407"
      > </a
      ><a name="13408" href="Stlc.html#12057" class="Function Operator"
      >:=</a
      ><a name="13410"
      > </a
      ><a name="13411" href="Stlc.html#5694" class="Function"
      >not</a
      ><a name="13414"
      > </a
      ><a name="13415" href="Stlc.html#12057" class="Function Operator"
      >]</a
      ><a name="13416"
      > </a
      ><a name="13417" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="13418"
      > </a
      ><a name="13419" href="Stlc.html#5694" class="Function"
      >not</a
      ><a name="13422"
      > </a
      ><a name="13423" href="Stlc.html#3679" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="13424"
      > </a
      ><a name="13425" class="Symbol"
      >(</a
      ><a name="13426" href="Stlc.html#5694" class="Function"
      >not</a
      ><a name="13429"
      > </a
      ><a name="13430" href="Stlc.html#3679" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="13431"
      > </a
      ><a name="13432" href="Stlc.html#3706" class="InductiveConstructor"
      >true</a
      ><a name="13436" class="Symbol"
      >)</a
      ><a name="13437"
      >
</a
      ><a name="13438" href="Stlc.html#13376" class="Function"
      >ex&#8321;&#8324;</a
      ><a name="13442"
      > </a
      ><a name="13443" class="Symbol"
      >=</a
      ><a name="13444"
      > </a
      ><a name="13445" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="13449"
      >

</a
      ><a name="13451" href="Stlc.html#13451" class="Function"
      >ex&#8321;&#8325;</a
      ><a name="13455"
      > </a
      ><a name="13456" class="Symbol"
      >:</a
      ><a name="13457"
      > </a
      ><a name="13458" class="Symbol"
      >(</a
      ><a name="13459" href="Stlc.html#3643" class="InductiveConstructor Operator"
      >&#955;[</a
      ><a name="13461"
      > </a
      ><a name="13462" href="Stlc.html#5651" class="Function"
      >x</a
      ><a name="13463"
      > </a
      ><a name="13464" href="Stlc.html#3643" class="InductiveConstructor Operator"
      >&#8758;</a
      ><a name="13465"
      > </a
      ><a name="13466" href="Stlc.html#2581" class="InductiveConstructor"
      >&#120121;</a
      ><a name="13467"
      > </a
      ><a name="13468" href="Stlc.html#3643" class="InductiveConstructor Operator"
      >]</a
      ><a name="13469"
      > </a
      ><a name="13470" href="Stlc.html#3627" class="InductiveConstructor"
      >`</a
      ><a name="13471"
      > </a
      ><a name="13472" href="Stlc.html#5649" class="Function"
      >f</a
      ><a name="13473"
      > </a
      ><a name="13474" href="Stlc.html#3679" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="13475"
      > </a
      ><a name="13476" class="Symbol"
      >(</a
      ><a name="13477" href="Stlc.html#3627" class="InductiveConstructor"
      >`</a
      ><a name="13478"
      > </a
      ><a name="13479" href="Stlc.html#5649" class="Function"
      >f</a
      ><a name="13480"
      > </a
      ><a name="13481" href="Stlc.html#3679" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="13482"
      > </a
      ><a name="13483" href="Stlc.html#3627" class="InductiveConstructor"
      >`</a
      ><a name="13484"
      > </a
      ><a name="13485" href="Stlc.html#5651" class="Function"
      >x</a
      ><a name="13486" class="Symbol"
      >))</a
      ><a name="13488"
      > </a
      ><a name="13489" href="Stlc.html#12057" class="Function Operator"
      >[</a
      ><a name="13490"
      > </a
      ><a name="13491" href="Stlc.html#5649" class="Function"
      >f</a
      ><a name="13492"
      > </a
      ><a name="13493" href="Stlc.html#12057" class="Function Operator"
      >:=</a
      ><a name="13495"
      > </a
      ><a name="13496" href="Stlc.html#5694" class="Function"
      >not</a
      ><a name="13499"
      > </a
      ><a name="13500" href="Stlc.html#12057" class="Function Operator"
      >]</a
      ><a name="13501"
      > </a
      ><a name="13502" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="13503"
      > </a
      ><a name="13504" href="Stlc.html#3643" class="InductiveConstructor Operator"
      >&#955;[</a
      ><a name="13506"
      > </a
      ><a name="13507" href="Stlc.html#5651" class="Function"
      >x</a
      ><a name="13508"
      > </a
      ><a name="13509" href="Stlc.html#3643" class="InductiveConstructor Operator"
      >&#8758;</a
      ><a name="13510"
      > </a
      ><a name="13511" href="Stlc.html#2581" class="InductiveConstructor"
      >&#120121;</a
      ><a name="13512"
      > </a
      ><a name="13513" href="Stlc.html#3643" class="InductiveConstructor Operator"
      >]</a
      ><a name="13514"
      > </a
      ><a name="13515" href="Stlc.html#5694" class="Function"
      >not</a
      ><a name="13518"
      > </a
      ><a name="13519" href="Stlc.html#3679" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="13520"
      > </a
      ><a name="13521" class="Symbol"
      >(</a
      ><a name="13522" href="Stlc.html#5694" class="Function"
      >not</a
      ><a name="13525"
      > </a
      ><a name="13526" href="Stlc.html#3679" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="13527"
      > </a
      ><a name="13528" href="Stlc.html#3627" class="InductiveConstructor"
      >`</a
      ><a name="13529"
      > </a
      ><a name="13530" href="Stlc.html#5651" class="Function"
      >x</a
      ><a name="13531" class="Symbol"
      >)</a
      ><a name="13532"
      >
</a
      ><a name="13533" href="Stlc.html#13451" class="Function"
      >ex&#8321;&#8325;</a
      ><a name="13537"
      > </a
      ><a name="13538" class="Symbol"
      >=</a
      ><a name="13539"
      > </a
      ><a name="13540" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="13544"
      >

</a
      ><a name="13546" href="Stlc.html#13546" class="Function"
      >ex&#8321;&#8326;</a
      ><a name="13550"
      > </a
      ><a name="13551" class="Symbol"
      >:</a
      ><a name="13552"
      > </a
      ><a name="13553" class="Symbol"
      >(</a
      ><a name="13554" href="Stlc.html#3643" class="InductiveConstructor Operator"
      >&#955;[</a
      ><a name="13556"
      > </a
      ><a name="13557" href="Stlc.html#5653" class="Function"
      >y</a
      ><a name="13558"
      > </a
      ><a name="13559" href="Stlc.html#3643" class="InductiveConstructor Operator"
      >&#8758;</a
      ><a name="13560"
      > </a
      ><a name="13561" href="Stlc.html#2581" class="InductiveConstructor"
      >&#120121;</a
      ><a name="13562"
      > </a
      ><a name="13563" href="Stlc.html#3643" class="InductiveConstructor Operator"
      >]</a
      ><a name="13564"
      > </a
      ><a name="13565" href="Stlc.html#3627" class="InductiveConstructor"
      >`</a
      ><a name="13566"
      > </a
      ><a name="13567" href="Stlc.html#5653" class="Function"
      >y</a
      ><a name="13568" class="Symbol"
      >)</a
      ><a name="13569"
      > </a
      ><a name="13570" href="Stlc.html#12057" class="Function Operator"
      >[</a
      ><a name="13571"
      > </a
      ><a name="13572" href="Stlc.html#5651" class="Function"
      >x</a
      ><a name="13573"
      > </a
      ><a name="13574" href="Stlc.html#12057" class="Function Operator"
      >:=</a
      ><a name="13576"
      > </a
      ><a name="13577" href="Stlc.html#3706" class="InductiveConstructor"
      >true</a
      ><a name="13581"
      > </a
      ><a name="13582" href="Stlc.html#12057" class="Function Operator"
      >]</a
      ><a name="13583"
      > </a
      ><a name="13584" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="13585"
      > </a
      ><a name="13586" href="Stlc.html#3643" class="InductiveConstructor Operator"
      >&#955;[</a
      ><a name="13588"
      > </a
      ><a name="13589" href="Stlc.html#5653" class="Function"
      >y</a
      ><a name="13590"
      > </a
      ><a name="13591" href="Stlc.html#3643" class="InductiveConstructor Operator"
      >&#8758;</a
      ><a name="13592"
      > </a
      ><a name="13593" href="Stlc.html#2581" class="InductiveConstructor"
      >&#120121;</a
      ><a name="13594"
      > </a
      ><a name="13595" href="Stlc.html#3643" class="InductiveConstructor Operator"
      >]</a
      ><a name="13596"
      > </a
      ><a name="13597" href="Stlc.html#3627" class="InductiveConstructor"
      >`</a
      ><a name="13598"
      > </a
      ><a name="13599" href="Stlc.html#5653" class="Function"
      >y</a
      ><a name="13600"
      >
</a
      ><a name="13601" href="Stlc.html#13546" class="Function"
      >ex&#8321;&#8326;</a
      ><a name="13605"
      > </a
      ><a name="13606" class="Symbol"
      >=</a
      ><a name="13607"
      > </a
      ><a name="13608" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="13612"
      >

</a
      ><a name="13614" href="Stlc.html#13614" class="Function"
      >ex&#8321;&#8327;</a
      ><a name="13618"
      > </a
      ><a name="13619" class="Symbol"
      >:</a
      ><a name="13620"
      > </a
      ><a name="13621" class="Symbol"
      >(</a
      ><a name="13622" href="Stlc.html#3643" class="InductiveConstructor Operator"
      >&#955;[</a
      ><a name="13624"
      > </a
      ><a name="13625" href="Stlc.html#5651" class="Function"
      >x</a
      ><a name="13626"
      > </a
      ><a name="13627" href="Stlc.html#3643" class="InductiveConstructor Operator"
      >&#8758;</a
      ><a name="13628"
      > </a
      ><a name="13629" href="Stlc.html#2581" class="InductiveConstructor"
      >&#120121;</a
      ><a name="13630"
      > </a
      ><a name="13631" href="Stlc.html#3643" class="InductiveConstructor Operator"
      >]</a
      ><a name="13632"
      > </a
      ><a name="13633" href="Stlc.html#3627" class="InductiveConstructor"
      >`</a
      ><a name="13634"
      > </a
      ><a name="13635" href="Stlc.html#5651" class="Function"
      >x</a
      ><a name="13636" class="Symbol"
      >)</a
      ><a name="13637"
      > </a
      ><a name="13638" href="Stlc.html#12057" class="Function Operator"
      >[</a
      ><a name="13639"
      > </a
      ><a name="13640" href="Stlc.html#5651" class="Function"
      >x</a
      ><a name="13641"
      > </a
      ><a name="13642" href="Stlc.html#12057" class="Function Operator"
      >:=</a
      ><a name="13644"
      > </a
      ><a name="13645" href="Stlc.html#3706" class="InductiveConstructor"
      >true</a
      ><a name="13649"
      > </a
      ><a name="13650" href="Stlc.html#12057" class="Function Operator"
      >]</a
      ><a name="13651"
      > </a
      ><a name="13652" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="13653"
      > </a
      ><a name="13654" href="Stlc.html#3643" class="InductiveConstructor Operator"
      >&#955;[</a
      ><a name="13656"
      > </a
      ><a name="13657" href="Stlc.html#5651" class="Function"
      >x</a
      ><a name="13658"
      > </a
      ><a name="13659" href="Stlc.html#3643" class="InductiveConstructor Operator"
      >&#8758;</a
      ><a name="13660"
      > </a
      ><a name="13661" href="Stlc.html#2581" class="InductiveConstructor"
      >&#120121;</a
      ><a name="13662"
      > </a
      ><a name="13663" href="Stlc.html#3643" class="InductiveConstructor Operator"
      >]</a
      ><a name="13664"
      > </a
      ><a name="13665" href="Stlc.html#3627" class="InductiveConstructor"
      >`</a
      ><a name="13666"
      > </a
      ><a name="13667" href="Stlc.html#5651" class="Function"
      >x</a
      ><a name="13668"
      >
</a
      ><a name="13669" href="Stlc.html#13614" class="Function"
      >ex&#8321;&#8327;</a
      ><a name="13673"
      > </a
      ><a name="13674" class="Symbol"
      >=</a
      ><a name="13675"
      > </a
      ><a name="13676" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
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

<a name="15729" class="Keyword"
      >infix</a
      ><a name="15734"
      > </a
      ><a name="15735" class="Number"
      >10</a
      ><a name="15737"
      > </a
      ><a name="15738" href="Stlc.html#15749" class="Datatype Operator"
      >_&#10233;_</a
      ><a name="15741"
      > 

</a
      ><a name="15744" class="Keyword"
      >data</a
      ><a name="15748"
      > </a
      ><a name="15749" href="Stlc.html#15749" class="Datatype Operator"
      >_&#10233;_</a
      ><a name="15752"
      > </a
      ><a name="15753" class="Symbol"
      >:</a
      ><a name="15754"
      > </a
      ><a name="15755" href="Stlc.html#3608" class="Datatype"
      >Term</a
      ><a name="15759"
      > </a
      ><a name="15760" class="Symbol"
      >&#8594;</a
      ><a name="15761"
      > </a
      ><a name="15762" href="Stlc.html#3608" class="Datatype"
      >Term</a
      ><a name="15766"
      > </a
      ><a name="15767" class="Symbol"
      >&#8594;</a
      ><a name="15768"
      > </a
      ><a name="15769" class="PrimitiveType"
      >Set</a
      ><a name="15772"
      > </a
      ><a name="15773" class="Keyword"
      >where</a
      ><a name="15778"
      >
  </a
      ><a name="15781" href="Stlc.html#15781" class="InductiveConstructor"
      >&#958;&#183;&#8321;</a
      ><a name="15784"
      > </a
      ><a name="15785" class="Symbol"
      >:</a
      ><a name="15786"
      > </a
      ><a name="15787" class="Symbol"
      >&#8704;</a
      ><a name="15788"
      > </a
      ><a name="15789" class="Symbol"
      >{</a
      ><a name="15790" href="Stlc.html#15790" class="Bound"
      >L</a
      ><a name="15791"
      > </a
      ><a name="15792" href="Stlc.html#15792" class="Bound"
      >L&#8242;</a
      ><a name="15794"
      > </a
      ><a name="15795" href="Stlc.html#15795" class="Bound"
      >M</a
      ><a name="15796" class="Symbol"
      >}</a
      ><a name="15797"
      > </a
      ><a name="15798" class="Symbol"
      >&#8594;</a
      ><a name="15799"
      >
    </a
      ><a name="15804" href="Stlc.html#15790" class="Bound"
      >L</a
      ><a name="15805"
      > </a
      ><a name="15806" href="Stlc.html#15749" class="Datatype Operator"
      >&#10233;</a
      ><a name="15807"
      > </a
      ><a name="15808" href="Stlc.html#15792" class="Bound"
      >L&#8242;</a
      ><a name="15810"
      > </a
      ><a name="15811" class="Symbol"
      >&#8594;</a
      ><a name="15812"
      >
    </a
      ><a name="15817" href="Stlc.html#15790" class="Bound"
      >L</a
      ><a name="15818"
      > </a
      ><a name="15819" href="Stlc.html#3679" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="15820"
      > </a
      ><a name="15821" href="Stlc.html#15795" class="Bound"
      >M</a
      ><a name="15822"
      > </a
      ><a name="15823" href="Stlc.html#15749" class="Datatype Operator"
      >&#10233;</a
      ><a name="15824"
      > </a
      ><a name="15825" href="Stlc.html#15792" class="Bound"
      >L&#8242;</a
      ><a name="15827"
      > </a
      ><a name="15828" href="Stlc.html#3679" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="15829"
      > </a
      ><a name="15830" href="Stlc.html#15795" class="Bound"
      >M</a
      ><a name="15831"
      >
  </a
      ><a name="15834" href="Stlc.html#15834" class="InductiveConstructor"
      >&#958;&#183;&#8322;</a
      ><a name="15837"
      > </a
      ><a name="15838" class="Symbol"
      >:</a
      ><a name="15839"
      > </a
      ><a name="15840" class="Symbol"
      >&#8704;</a
      ><a name="15841"
      > </a
      ><a name="15842" class="Symbol"
      >{</a
      ><a name="15843" href="Stlc.html#15843" class="Bound"
      >V</a
      ><a name="15844"
      > </a
      ><a name="15845" href="Stlc.html#15845" class="Bound"
      >M</a
      ><a name="15846"
      > </a
      ><a name="15847" href="Stlc.html#15847" class="Bound"
      >M&#8242;</a
      ><a name="15849" class="Symbol"
      >}</a
      ><a name="15850"
      > </a
      ><a name="15851" class="Symbol"
      >&#8594;</a
      ><a name="15852"
      >
    </a
      ><a name="15857" href="Stlc.html#9513" class="Datatype"
      >Value</a
      ><a name="15862"
      > </a
      ><a name="15863" href="Stlc.html#15843" class="Bound"
      >V</a
      ><a name="15864"
      > </a
      ><a name="15865" class="Symbol"
      >&#8594;</a
      ><a name="15866"
      >
    </a
      ><a name="15871" href="Stlc.html#15845" class="Bound"
      >M</a
      ><a name="15872"
      > </a
      ><a name="15873" href="Stlc.html#15749" class="Datatype Operator"
      >&#10233;</a
      ><a name="15874"
      > </a
      ><a name="15875" href="Stlc.html#15847" class="Bound"
      >M&#8242;</a
      ><a name="15877"
      > </a
      ><a name="15878" class="Symbol"
      >&#8594;</a
      ><a name="15879"
      >
    </a
      ><a name="15884" href="Stlc.html#15843" class="Bound"
      >V</a
      ><a name="15885"
      > </a
      ><a name="15886" href="Stlc.html#3679" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="15887"
      > </a
      ><a name="15888" href="Stlc.html#15845" class="Bound"
      >M</a
      ><a name="15889"
      > </a
      ><a name="15890" href="Stlc.html#15749" class="Datatype Operator"
      >&#10233;</a
      ><a name="15891"
      > </a
      ><a name="15892" href="Stlc.html#15843" class="Bound"
      >V</a
      ><a name="15893"
      > </a
      ><a name="15894" href="Stlc.html#3679" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="15895"
      > </a
      ><a name="15896" href="Stlc.html#15847" class="Bound"
      >M&#8242;</a
      ><a name="15898"
      >
  </a
      ><a name="15901" href="Stlc.html#15901" class="InductiveConstructor"
      >&#946;&#955;&#183;</a
      ><a name="15904"
      > </a
      ><a name="15905" class="Symbol"
      >:</a
      ><a name="15906"
      > </a
      ><a name="15907" class="Symbol"
      >&#8704;</a
      ><a name="15908"
      > </a
      ><a name="15909" class="Symbol"
      >{</a
      ><a name="15910" href="Stlc.html#15910" class="Bound"
      >x</a
      ><a name="15911"
      > </a
      ><a name="15912" href="Stlc.html#15912" class="Bound"
      >A</a
      ><a name="15913"
      > </a
      ><a name="15914" href="Stlc.html#15914" class="Bound"
      >N</a
      ><a name="15915"
      > </a
      ><a name="15916" href="Stlc.html#15916" class="Bound"
      >V</a
      ><a name="15917" class="Symbol"
      >}</a
      ><a name="15918"
      > </a
      ><a name="15919" class="Symbol"
      >&#8594;</a
      ><a name="15920"
      > </a
      ><a name="15921" href="Stlc.html#9513" class="Datatype"
      >Value</a
      ><a name="15926"
      > </a
      ><a name="15927" href="Stlc.html#15916" class="Bound"
      >V</a
      ><a name="15928"
      > </a
      ><a name="15929" class="Symbol"
      >&#8594;</a
      ><a name="15930"
      >
    </a
      ><a name="15935" class="Symbol"
      >(</a
      ><a name="15936" href="Stlc.html#3643" class="InductiveConstructor Operator"
      >&#955;[</a
      ><a name="15938"
      > </a
      ><a name="15939" href="Stlc.html#15910" class="Bound"
      >x</a
      ><a name="15940"
      > </a
      ><a name="15941" href="Stlc.html#3643" class="InductiveConstructor Operator"
      >&#8758;</a
      ><a name="15942"
      > </a
      ><a name="15943" href="Stlc.html#15912" class="Bound"
      >A</a
      ><a name="15944"
      > </a
      ><a name="15945" href="Stlc.html#3643" class="InductiveConstructor Operator"
      >]</a
      ><a name="15946"
      > </a
      ><a name="15947" href="Stlc.html#15914" class="Bound"
      >N</a
      ><a name="15948" class="Symbol"
      >)</a
      ><a name="15949"
      > </a
      ><a name="15950" href="Stlc.html#3679" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="15951"
      > </a
      ><a name="15952" href="Stlc.html#15916" class="Bound"
      >V</a
      ><a name="15953"
      > </a
      ><a name="15954" href="Stlc.html#15749" class="Datatype Operator"
      >&#10233;</a
      ><a name="15955"
      > </a
      ><a name="15956" href="Stlc.html#15914" class="Bound"
      >N</a
      ><a name="15957"
      > </a
      ><a name="15958" href="Stlc.html#12057" class="Function Operator"
      >[</a
      ><a name="15959"
      > </a
      ><a name="15960" href="Stlc.html#15910" class="Bound"
      >x</a
      ><a name="15961"
      > </a
      ><a name="15962" href="Stlc.html#12057" class="Function Operator"
      >:=</a
      ><a name="15964"
      > </a
      ><a name="15965" href="Stlc.html#15916" class="Bound"
      >V</a
      ><a name="15966"
      > </a
      ><a name="15967" href="Stlc.html#12057" class="Function Operator"
      >]</a
      ><a name="15968"
      >
  </a
      ><a name="15971" href="Stlc.html#15971" class="InductiveConstructor"
      >&#958;if</a
      ><a name="15974"
      > </a
      ><a name="15975" class="Symbol"
      >:</a
      ><a name="15976"
      > </a
      ><a name="15977" class="Symbol"
      >&#8704;</a
      ><a name="15978"
      > </a
      ><a name="15979" class="Symbol"
      >{</a
      ><a name="15980" href="Stlc.html#15980" class="Bound"
      >L</a
      ><a name="15981"
      > </a
      ><a name="15982" href="Stlc.html#15982" class="Bound"
      >L&#8242;</a
      ><a name="15984"
      > </a
      ><a name="15985" href="Stlc.html#15985" class="Bound"
      >M</a
      ><a name="15986"
      > </a
      ><a name="15987" href="Stlc.html#15987" class="Bound"
      >N</a
      ><a name="15988" class="Symbol"
      >}</a
      ><a name="15989"
      > </a
      ><a name="15990" class="Symbol"
      >&#8594;</a
      ><a name="15991"
      >
    </a
      ><a name="15996" href="Stlc.html#15980" class="Bound"
      >L</a
      ><a name="15997"
      > </a
      ><a name="15998" href="Stlc.html#15749" class="Datatype Operator"
      >&#10233;</a
      ><a name="15999"
      > </a
      ><a name="16000" href="Stlc.html#15982" class="Bound"
      >L&#8242;</a
      ><a name="16002"
      > </a
      ><a name="16003" class="Symbol"
      >&#8594;</a
      ><a name="16004"
      >    
    </a
      ><a name="16013" href="Stlc.html#3735" class="InductiveConstructor Operator"
      >if</a
      ><a name="16015"
      > </a
      ><a name="16016" href="Stlc.html#15980" class="Bound"
      >L</a
      ><a name="16017"
      > </a
      ><a name="16018" href="Stlc.html#3735" class="InductiveConstructor Operator"
      >then</a
      ><a name="16022"
      > </a
      ><a name="16023" href="Stlc.html#15985" class="Bound"
      >M</a
      ><a name="16024"
      > </a
      ><a name="16025" href="Stlc.html#3735" class="InductiveConstructor Operator"
      >else</a
      ><a name="16029"
      > </a
      ><a name="16030" href="Stlc.html#15987" class="Bound"
      >N</a
      ><a name="16031"
      > </a
      ><a name="16032" href="Stlc.html#15749" class="Datatype Operator"
      >&#10233;</a
      ><a name="16033"
      > </a
      ><a name="16034" href="Stlc.html#3735" class="InductiveConstructor Operator"
      >if</a
      ><a name="16036"
      > </a
      ><a name="16037" href="Stlc.html#15982" class="Bound"
      >L&#8242;</a
      ><a name="16039"
      > </a
      ><a name="16040" href="Stlc.html#3735" class="InductiveConstructor Operator"
      >then</a
      ><a name="16044"
      > </a
      ><a name="16045" href="Stlc.html#15985" class="Bound"
      >M</a
      ><a name="16046"
      > </a
      ><a name="16047" href="Stlc.html#3735" class="InductiveConstructor Operator"
      >else</a
      ><a name="16051"
      > </a
      ><a name="16052" href="Stlc.html#15987" class="Bound"
      >N</a
      ><a name="16053"
      >
  </a
      ><a name="16056" href="Stlc.html#16056" class="InductiveConstructor"
      >&#946;if-true</a
      ><a name="16064"
      > </a
      ><a name="16065" class="Symbol"
      >:</a
      ><a name="16066"
      > </a
      ><a name="16067" class="Symbol"
      >&#8704;</a
      ><a name="16068"
      > </a
      ><a name="16069" class="Symbol"
      >{</a
      ><a name="16070" href="Stlc.html#16070" class="Bound"
      >M</a
      ><a name="16071"
      > </a
      ><a name="16072" href="Stlc.html#16072" class="Bound"
      >N</a
      ><a name="16073" class="Symbol"
      >}</a
      ><a name="16074"
      > </a
      ><a name="16075" class="Symbol"
      >&#8594;</a
      ><a name="16076"
      >
    </a
      ><a name="16081" href="Stlc.html#3735" class="InductiveConstructor Operator"
      >if</a
      ><a name="16083"
      > </a
      ><a name="16084" href="Stlc.html#3706" class="InductiveConstructor"
      >true</a
      ><a name="16088"
      > </a
      ><a name="16089" href="Stlc.html#3735" class="InductiveConstructor Operator"
      >then</a
      ><a name="16093"
      > </a
      ><a name="16094" href="Stlc.html#16070" class="Bound"
      >M</a
      ><a name="16095"
      > </a
      ><a name="16096" href="Stlc.html#3735" class="InductiveConstructor Operator"
      >else</a
      ><a name="16100"
      > </a
      ><a name="16101" href="Stlc.html#16072" class="Bound"
      >N</a
      ><a name="16102"
      > </a
      ><a name="16103" href="Stlc.html#15749" class="Datatype Operator"
      >&#10233;</a
      ><a name="16104"
      > </a
      ><a name="16105" href="Stlc.html#16070" class="Bound"
      >M</a
      ><a name="16106"
      >
  </a
      ><a name="16109" href="Stlc.html#16109" class="InductiveConstructor"
      >&#946;if-false</a
      ><a name="16118"
      > </a
      ><a name="16119" class="Symbol"
      >:</a
      ><a name="16120"
      > </a
      ><a name="16121" class="Symbol"
      >&#8704;</a
      ><a name="16122"
      > </a
      ><a name="16123" class="Symbol"
      >{</a
      ><a name="16124" href="Stlc.html#16124" class="Bound"
      >M</a
      ><a name="16125"
      > </a
      ><a name="16126" href="Stlc.html#16126" class="Bound"
      >N</a
      ><a name="16127" class="Symbol"
      >}</a
      ><a name="16128"
      > </a
      ><a name="16129" class="Symbol"
      >&#8594;</a
      ><a name="16130"
      >
    </a
      ><a name="16135" href="Stlc.html#3735" class="InductiveConstructor Operator"
      >if</a
      ><a name="16137"
      > </a
      ><a name="16138" href="Stlc.html#3720" class="InductiveConstructor"
      >false</a
      ><a name="16143"
      > </a
      ><a name="16144" href="Stlc.html#3735" class="InductiveConstructor Operator"
      >then</a
      ><a name="16148"
      > </a
      ><a name="16149" href="Stlc.html#16124" class="Bound"
      >M</a
      ><a name="16150"
      > </a
      ><a name="16151" href="Stlc.html#3735" class="InductiveConstructor Operator"
      >else</a
      ><a name="16155"
      > </a
      ><a name="16156" href="Stlc.html#16126" class="Bound"
      >N</a
      ><a name="16157"
      > </a
      ><a name="16158" href="Stlc.html#15749" class="Datatype Operator"
      >&#10233;</a
      ><a name="16159"
      > </a
      ><a name="16160" href="Stlc.html#16126" class="Bound"
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

<a name="17734" class="Keyword"
      >infix</a
      ><a name="17739"
      > </a
      ><a name="17740" class="Number"
      >10</a
      ><a name="17742"
      > </a
      ><a name="17743" href="Stlc.html#17783" class="Datatype Operator"
      >_&#10233;*_</a
      ><a name="17747"
      > 
</a
      ><a name="17749" class="Keyword"
      >infixr</a
      ><a name="17755"
      > </a
      ><a name="17756" class="Number"
      >2</a
      ><a name="17757"
      > </a
      ><a name="17758" href="Stlc.html#17836" class="InductiveConstructor Operator"
      >_&#10233;&#10216;_&#10217;_</a
      ><a name="17764"
      >
</a
      ><a name="17765" class="Keyword"
      >infix</a
      ><a name="17770"
      >  </a
      ><a name="17772" class="Number"
      >3</a
      ><a name="17773"
      > </a
      ><a name="17774" href="Stlc.html#17816" class="InductiveConstructor Operator"
      >_&#8718;</a
      ><a name="17776"
      >

</a
      ><a name="17778" class="Keyword"
      >data</a
      ><a name="17782"
      > </a
      ><a name="17783" href="Stlc.html#17783" class="Datatype Operator"
      >_&#10233;*_</a
      ><a name="17787"
      > </a
      ><a name="17788" class="Symbol"
      >:</a
      ><a name="17789"
      > </a
      ><a name="17790" href="Stlc.html#3608" class="Datatype"
      >Term</a
      ><a name="17794"
      > </a
      ><a name="17795" class="Symbol"
      >&#8594;</a
      ><a name="17796"
      > </a
      ><a name="17797" href="Stlc.html#3608" class="Datatype"
      >Term</a
      ><a name="17801"
      > </a
      ><a name="17802" class="Symbol"
      >&#8594;</a
      ><a name="17803"
      > </a
      ><a name="17804" class="PrimitiveType"
      >Set</a
      ><a name="17807"
      > </a
      ><a name="17808" class="Keyword"
      >where</a
      ><a name="17813"
      >
  </a
      ><a name="17816" href="Stlc.html#17816" class="InductiveConstructor Operator"
      >_&#8718;</a
      ><a name="17818"
      > </a
      ><a name="17819" class="Symbol"
      >:</a
      ><a name="17820"
      > </a
      ><a name="17821" class="Symbol"
      >&#8704;</a
      ><a name="17822"
      > </a
      ><a name="17823" href="Stlc.html#17823" class="Bound"
      >M</a
      ><a name="17824"
      > </a
      ><a name="17825" class="Symbol"
      >&#8594;</a
      ><a name="17826"
      > </a
      ><a name="17827" href="Stlc.html#17823" class="Bound"
      >M</a
      ><a name="17828"
      > </a
      ><a name="17829" href="Stlc.html#17783" class="Datatype Operator"
      >&#10233;*</a
      ><a name="17831"
      > </a
      ><a name="17832" href="Stlc.html#17823" class="Bound"
      >M</a
      ><a name="17833"
      >
  </a
      ><a name="17836" href="Stlc.html#17836" class="InductiveConstructor Operator"
      >_&#10233;&#10216;_&#10217;_</a
      ><a name="17842"
      > </a
      ><a name="17843" class="Symbol"
      >:</a
      ><a name="17844"
      > </a
      ><a name="17845" class="Symbol"
      >&#8704;</a
      ><a name="17846"
      > </a
      ><a name="17847" href="Stlc.html#17847" class="Bound"
      >L</a
      ><a name="17848"
      > </a
      ><a name="17849" class="Symbol"
      >{</a
      ><a name="17850" href="Stlc.html#17850" class="Bound"
      >M</a
      ><a name="17851"
      > </a
      ><a name="17852" href="Stlc.html#17852" class="Bound"
      >N</a
      ><a name="17853" class="Symbol"
      >}</a
      ><a name="17854"
      > </a
      ><a name="17855" class="Symbol"
      >&#8594;</a
      ><a name="17856"
      > </a
      ><a name="17857" href="Stlc.html#17847" class="Bound"
      >L</a
      ><a name="17858"
      > </a
      ><a name="17859" href="Stlc.html#15749" class="Datatype Operator"
      >&#10233;</a
      ><a name="17860"
      > </a
      ><a name="17861" href="Stlc.html#17850" class="Bound"
      >M</a
      ><a name="17862"
      > </a
      ><a name="17863" class="Symbol"
      >&#8594;</a
      ><a name="17864"
      > </a
      ><a name="17865" href="Stlc.html#17850" class="Bound"
      >M</a
      ><a name="17866"
      > </a
      ><a name="17867" href="Stlc.html#17783" class="Datatype Operator"
      >&#10233;*</a
      ><a name="17869"
      > </a
      ><a name="17870" href="Stlc.html#17852" class="Bound"
      >N</a
      ><a name="17871"
      > </a
      ><a name="17872" class="Symbol"
      >&#8594;</a
      ><a name="17873"
      > </a
      ><a name="17874" href="Stlc.html#17847" class="Bound"
      >L</a
      ><a name="17875"
      > </a
      ><a name="17876" href="Stlc.html#17783" class="Datatype Operator"
      >&#10233;*</a
      ><a name="17878"
      > </a
      ><a name="17879" href="Stlc.html#17852" class="Bound"
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

<a name="18340" href="Stlc.html#18340" class="Function"
      >reduction&#8321;</a
      ><a name="18350"
      > </a
      ><a name="18351" class="Symbol"
      >:</a
      ><a name="18352"
      > </a
      ><a name="18353" href="Stlc.html#5694" class="Function"
      >not</a
      ><a name="18356"
      > </a
      ><a name="18357" href="Stlc.html#3679" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="18358"
      > </a
      ><a name="18359" href="Stlc.html#3706" class="InductiveConstructor"
      >true</a
      ><a name="18363"
      > </a
      ><a name="18364" href="Stlc.html#17783" class="Datatype Operator"
      >&#10233;*</a
      ><a name="18366"
      > </a
      ><a name="18367" href="Stlc.html#3720" class="InductiveConstructor"
      >false</a
      ><a name="18372"
      >
</a
      ><a name="18373" href="Stlc.html#18340" class="Function"
      >reduction&#8321;</a
      ><a name="18383"
      > </a
      ><a name="18384" class="Symbol"
      >=</a
      ><a name="18385"
      >
    </a
      ><a name="18390" href="Stlc.html#5694" class="Function"
      >not</a
      ><a name="18393"
      > </a
      ><a name="18394" href="Stlc.html#3679" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="18395"
      > </a
      ><a name="18396" href="Stlc.html#3706" class="InductiveConstructor"
      >true</a
      ><a name="18400"
      >
  </a
      ><a name="18403" href="Stlc.html#17836" class="InductiveConstructor Operator"
      >&#10233;&#10216;</a
      ><a name="18405"
      > </a
      ><a name="18406" href="Stlc.html#15901" class="InductiveConstructor"
      >&#946;&#955;&#183;</a
      ><a name="18409"
      > </a
      ><a name="18410" href="Stlc.html#9589" class="InductiveConstructor"
      >value-true</a
      ><a name="18420"
      > </a
      ><a name="18421" href="Stlc.html#17836" class="InductiveConstructor Operator"
      >&#10217;</a
      ><a name="18422"
      >
    </a
      ><a name="18427" href="Stlc.html#3735" class="InductiveConstructor Operator"
      >if</a
      ><a name="18429"
      > </a
      ><a name="18430" href="Stlc.html#3706" class="InductiveConstructor"
      >true</a
      ><a name="18434"
      > </a
      ><a name="18435" href="Stlc.html#3735" class="InductiveConstructor Operator"
      >then</a
      ><a name="18439"
      > </a
      ><a name="18440" href="Stlc.html#3720" class="InductiveConstructor"
      >false</a
      ><a name="18445"
      > </a
      ><a name="18446" href="Stlc.html#3735" class="InductiveConstructor Operator"
      >else</a
      ><a name="18450"
      > </a
      ><a name="18451" href="Stlc.html#3706" class="InductiveConstructor"
      >true</a
      ><a name="18455"
      >
  </a
      ><a name="18458" href="Stlc.html#17836" class="InductiveConstructor Operator"
      >&#10233;&#10216;</a
      ><a name="18460"
      > </a
      ><a name="18461" href="Stlc.html#16056" class="InductiveConstructor"
      >&#946;if-true</a
      ><a name="18469"
      > </a
      ><a name="18470" href="Stlc.html#17836" class="InductiveConstructor Operator"
      >&#10217;</a
      ><a name="18471"
      >
    </a
      ><a name="18476" href="Stlc.html#3720" class="InductiveConstructor"
      >false</a
      ><a name="18481"
      >
  </a
      ><a name="18484" href="Stlc.html#17816" class="InductiveConstructor Operator"
      >&#8718;</a
      ><a name="18485"
      >

</a
      ><a name="18487" href="Stlc.html#18487" class="Function"
      >reduction&#8322;</a
      ><a name="18497"
      > </a
      ><a name="18498" class="Symbol"
      >:</a
      ><a name="18499"
      > </a
      ><a name="18500" href="Stlc.html#5698" class="Function"
      >two</a
      ><a name="18503"
      > </a
      ><a name="18504" href="Stlc.html#3679" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="18505"
      > </a
      ><a name="18506" href="Stlc.html#5694" class="Function"
      >not</a
      ><a name="18509"
      > </a
      ><a name="18510" href="Stlc.html#3679" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="18511"
      > </a
      ><a name="18512" href="Stlc.html#3706" class="InductiveConstructor"
      >true</a
      ><a name="18516"
      > </a
      ><a name="18517" href="Stlc.html#17783" class="Datatype Operator"
      >&#10233;*</a
      ><a name="18519"
      > </a
      ><a name="18520" href="Stlc.html#3706" class="InductiveConstructor"
      >true</a
      ><a name="18524"
      >
</a
      ><a name="18525" href="Stlc.html#18487" class="Function"
      >reduction&#8322;</a
      ><a name="18535"
      > </a
      ><a name="18536" class="Symbol"
      >=</a
      ><a name="18537"
      >
    </a
      ><a name="18542" href="Stlc.html#5698" class="Function"
      >two</a
      ><a name="18545"
      > </a
      ><a name="18546" href="Stlc.html#3679" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="18547"
      > </a
      ><a name="18548" href="Stlc.html#5694" class="Function"
      >not</a
      ><a name="18551"
      > </a
      ><a name="18552" href="Stlc.html#3679" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="18553"
      > </a
      ><a name="18554" href="Stlc.html#3706" class="InductiveConstructor"
      >true</a
      ><a name="18558"
      >
  </a
      ><a name="18561" href="Stlc.html#17836" class="InductiveConstructor Operator"
      >&#10233;&#10216;</a
      ><a name="18563"
      > </a
      ><a name="18564" href="Stlc.html#15781" class="InductiveConstructor"
      >&#958;&#183;&#8321;</a
      ><a name="18567"
      > </a
      ><a name="18568" class="Symbol"
      >(</a
      ><a name="18569" href="Stlc.html#15901" class="InductiveConstructor"
      >&#946;&#955;&#183;</a
      ><a name="18572"
      > </a
      ><a name="18573" href="Stlc.html#9540" class="InductiveConstructor"
      >value-&#955;</a
      ><a name="18580" class="Symbol"
      >)</a
      ><a name="18581"
      > </a
      ><a name="18582" href="Stlc.html#17836" class="InductiveConstructor Operator"
      >&#10217;</a
      ><a name="18583"
      >
    </a
      ><a name="18588" class="Symbol"
      >(</a
      ><a name="18589" href="Stlc.html#3643" class="InductiveConstructor Operator"
      >&#955;[</a
      ><a name="18591"
      > </a
      ><a name="18592" href="Stlc.html#5651" class="Function"
      >x</a
      ><a name="18593"
      > </a
      ><a name="18594" href="Stlc.html#3643" class="InductiveConstructor Operator"
      >&#8758;</a
      ><a name="18595"
      > </a
      ><a name="18596" href="Stlc.html#2581" class="InductiveConstructor"
      >&#120121;</a
      ><a name="18597"
      > </a
      ><a name="18598" href="Stlc.html#3643" class="InductiveConstructor Operator"
      >]</a
      ><a name="18599"
      > </a
      ><a name="18600" href="Stlc.html#5694" class="Function"
      >not</a
      ><a name="18603"
      > </a
      ><a name="18604" href="Stlc.html#3679" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="18605"
      > </a
      ><a name="18606" class="Symbol"
      >(</a
      ><a name="18607" href="Stlc.html#5694" class="Function"
      >not</a
      ><a name="18610"
      > </a
      ><a name="18611" href="Stlc.html#3679" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="18612"
      > </a
      ><a name="18613" href="Stlc.html#3627" class="InductiveConstructor"
      >`</a
      ><a name="18614"
      > </a
      ><a name="18615" href="Stlc.html#5651" class="Function"
      >x</a
      ><a name="18616" class="Symbol"
      >))</a
      ><a name="18618"
      > </a
      ><a name="18619" href="Stlc.html#3679" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="18620"
      > </a
      ><a name="18621" href="Stlc.html#3706" class="InductiveConstructor"
      >true</a
      ><a name="18625"
      >
  </a
      ><a name="18628" href="Stlc.html#17836" class="InductiveConstructor Operator"
      >&#10233;&#10216;</a
      ><a name="18630"
      > </a
      ><a name="18631" href="Stlc.html#15901" class="InductiveConstructor"
      >&#946;&#955;&#183;</a
      ><a name="18634"
      > </a
      ><a name="18635" href="Stlc.html#9589" class="InductiveConstructor"
      >value-true</a
      ><a name="18645"
      > </a
      ><a name="18646" href="Stlc.html#17836" class="InductiveConstructor Operator"
      >&#10217;</a
      ><a name="18647"
      >
    </a
      ><a name="18652" href="Stlc.html#5694" class="Function"
      >not</a
      ><a name="18655"
      > </a
      ><a name="18656" href="Stlc.html#3679" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="18657"
      > </a
      ><a name="18658" class="Symbol"
      >(</a
      ><a name="18659" href="Stlc.html#5694" class="Function"
      >not</a
      ><a name="18662"
      > </a
      ><a name="18663" href="Stlc.html#3679" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="18664"
      > </a
      ><a name="18665" href="Stlc.html#3706" class="InductiveConstructor"
      >true</a
      ><a name="18669" class="Symbol"
      >)</a
      ><a name="18670"
      >
  </a
      ><a name="18673" href="Stlc.html#17836" class="InductiveConstructor Operator"
      >&#10233;&#10216;</a
      ><a name="18675"
      > </a
      ><a name="18676" href="Stlc.html#15834" class="InductiveConstructor"
      >&#958;&#183;&#8322;</a
      ><a name="18679"
      > </a
      ><a name="18680" href="Stlc.html#9540" class="InductiveConstructor"
      >value-&#955;</a
      ><a name="18687"
      > </a
      ><a name="18688" class="Symbol"
      >(</a
      ><a name="18689" href="Stlc.html#15901" class="InductiveConstructor"
      >&#946;&#955;&#183;</a
      ><a name="18692"
      > </a
      ><a name="18693" href="Stlc.html#9589" class="InductiveConstructor"
      >value-true</a
      ><a name="18703" class="Symbol"
      >)</a
      ><a name="18704"
      > </a
      ><a name="18705" href="Stlc.html#17836" class="InductiveConstructor Operator"
      >&#10217;</a
      ><a name="18706"
      >
    </a
      ><a name="18711" href="Stlc.html#5694" class="Function"
      >not</a
      ><a name="18714"
      > </a
      ><a name="18715" href="Stlc.html#3679" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="18716"
      > </a
      ><a name="18717" class="Symbol"
      >(</a
      ><a name="18718" href="Stlc.html#3735" class="InductiveConstructor Operator"
      >if</a
      ><a name="18720"
      > </a
      ><a name="18721" href="Stlc.html#3706" class="InductiveConstructor"
      >true</a
      ><a name="18725"
      > </a
      ><a name="18726" href="Stlc.html#3735" class="InductiveConstructor Operator"
      >then</a
      ><a name="18730"
      > </a
      ><a name="18731" href="Stlc.html#3720" class="InductiveConstructor"
      >false</a
      ><a name="18736"
      > </a
      ><a name="18737" href="Stlc.html#3735" class="InductiveConstructor Operator"
      >else</a
      ><a name="18741"
      > </a
      ><a name="18742" href="Stlc.html#3706" class="InductiveConstructor"
      >true</a
      ><a name="18746" class="Symbol"
      >)</a
      ><a name="18747"
      >
  </a
      ><a name="18750" href="Stlc.html#17836" class="InductiveConstructor Operator"
      >&#10233;&#10216;</a
      ><a name="18752"
      > </a
      ><a name="18753" href="Stlc.html#15834" class="InductiveConstructor"
      >&#958;&#183;&#8322;</a
      ><a name="18756"
      > </a
      ><a name="18757" href="Stlc.html#9540" class="InductiveConstructor"
      >value-&#955;</a
      ><a name="18764"
      > </a
      ><a name="18765" href="Stlc.html#16056" class="InductiveConstructor"
      >&#946;if-true</a
      ><a name="18773"
      >  </a
      ><a name="18775" href="Stlc.html#17836" class="InductiveConstructor Operator"
      >&#10217;</a
      ><a name="18776"
      >
    </a
      ><a name="18781" href="Stlc.html#5694" class="Function"
      >not</a
      ><a name="18784"
      > </a
      ><a name="18785" href="Stlc.html#3679" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="18786"
      > </a
      ><a name="18787" href="Stlc.html#3720" class="InductiveConstructor"
      >false</a
      ><a name="18792"
      >
  </a
      ><a name="18795" href="Stlc.html#17836" class="InductiveConstructor Operator"
      >&#10233;&#10216;</a
      ><a name="18797"
      > </a
      ><a name="18798" href="Stlc.html#15901" class="InductiveConstructor"
      >&#946;&#955;&#183;</a
      ><a name="18801"
      > </a
      ><a name="18802" href="Stlc.html#9616" class="InductiveConstructor"
      >value-false</a
      ><a name="18813"
      > </a
      ><a name="18814" href="Stlc.html#17836" class="InductiveConstructor Operator"
      >&#10217;</a
      ><a name="18815"
      >
    </a
      ><a name="18820" href="Stlc.html#3735" class="InductiveConstructor Operator"
      >if</a
      ><a name="18822"
      > </a
      ><a name="18823" href="Stlc.html#3720" class="InductiveConstructor"
      >false</a
      ><a name="18828"
      > </a
      ><a name="18829" href="Stlc.html#3735" class="InductiveConstructor Operator"
      >then</a
      ><a name="18833"
      > </a
      ><a name="18834" href="Stlc.html#3720" class="InductiveConstructor"
      >false</a
      ><a name="18839"
      > </a
      ><a name="18840" href="Stlc.html#3735" class="InductiveConstructor Operator"
      >else</a
      ><a name="18844"
      > </a
      ><a name="18845" href="Stlc.html#3706" class="InductiveConstructor"
      >true</a
      ><a name="18849"
      >
  </a
      ><a name="18852" href="Stlc.html#17836" class="InductiveConstructor Operator"
      >&#10233;&#10216;</a
      ><a name="18854"
      > </a
      ><a name="18855" href="Stlc.html#16109" class="InductiveConstructor"
      >&#946;if-false</a
      ><a name="18864"
      > </a
      ><a name="18865" href="Stlc.html#17836" class="InductiveConstructor Operator"
      >&#10217;</a
      ><a name="18866"
      >
    </a
      ><a name="18871" href="Stlc.html#3706" class="InductiveConstructor"
      >true</a
      ><a name="18875"
      >
  </a
      ><a name="18878" href="Stlc.html#17816" class="InductiveConstructor Operator"
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

<a name="20042" href="Stlc.html#20042" class="Function"
      >Context</a
      ><a name="20049"
      > </a
      ><a name="20050" class="Symbol"
      >:</a
      ><a name="20051"
      > </a
      ><a name="20052" class="PrimitiveType"
      >Set</a
      ><a name="20055"
      >
</a
      ><a name="20056" href="Stlc.html#20042" class="Function"
      >Context</a
      ><a name="20063"
      > </a
      ><a name="20064" class="Symbol"
      >=</a
      ><a name="20065"
      > </a
      ><a name="20066" href="Maps.html#10132" class="Function"
      >PartialMap</a
      ><a name="20076"
      > </a
      ><a name="20077" href="Stlc.html#2535" class="Datatype"
      >Type</a
      ><a name="20081"
      >

</a
      ><a name="20083" class="Keyword"
      >infix</a
      ><a name="20088"
      > </a
      ><a name="20089" class="Number"
      >10</a
      ><a name="20091"
      > </a
      ><a name="20092" href="Stlc.html#20104" class="Datatype Operator"
      >_&#8866;_&#8758;_</a
      ><a name="20097"
      >

</a
      ><a name="20099" class="Keyword"
      >data</a
      ><a name="20103"
      > </a
      ><a name="20104" href="Stlc.html#20104" class="Datatype Operator"
      >_&#8866;_&#8758;_</a
      ><a name="20109"
      > </a
      ><a name="20110" class="Symbol"
      >:</a
      ><a name="20111"
      > </a
      ><a name="20112" href="Stlc.html#20042" class="Function"
      >Context</a
      ><a name="20119"
      > </a
      ><a name="20120" class="Symbol"
      >&#8594;</a
      ><a name="20121"
      > </a
      ><a name="20122" href="Stlc.html#3608" class="Datatype"
      >Term</a
      ><a name="20126"
      > </a
      ><a name="20127" class="Symbol"
      >&#8594;</a
      ><a name="20128"
      > </a
      ><a name="20129" href="Stlc.html#2535" class="Datatype"
      >Type</a
      ><a name="20133"
      > </a
      ><a name="20134" class="Symbol"
      >&#8594;</a
      ><a name="20135"
      > </a
      ><a name="20136" class="PrimitiveType"
      >Set</a
      ><a name="20139"
      > </a
      ><a name="20140" class="Keyword"
      >where</a
      ><a name="20145"
      >
  </a
      ><a name="20148" href="Stlc.html#20148" class="InductiveConstructor"
      >Ax</a
      ><a name="20150"
      > </a
      ><a name="20151" class="Symbol"
      >:</a
      ><a name="20152"
      > </a
      ><a name="20153" class="Symbol"
      >&#8704;</a
      ><a name="20154"
      > </a
      ><a name="20155" class="Symbol"
      >{</a
      ><a name="20156" href="Stlc.html#20156" class="Bound"
      >&#915;</a
      ><a name="20157"
      > </a
      ><a name="20158" href="Stlc.html#20158" class="Bound"
      >x</a
      ><a name="20159"
      > </a
      ><a name="20160" href="Stlc.html#20160" class="Bound"
      >A</a
      ><a name="20161" class="Symbol"
      >}</a
      ><a name="20162"
      > </a
      ><a name="20163" class="Symbol"
      >&#8594;</a
      ><a name="20164"
      >
    </a
      ><a name="20169" href="Stlc.html#20156" class="Bound"
      >&#915;</a
      ><a name="20170"
      > </a
      ><a name="20171" href="Stlc.html#20158" class="Bound"
      >x</a
      ><a name="20172"
      > </a
      ><a name="20173" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="20174"
      > </a
      ><a name="20175" href="https://agda.github.io/agda-stdlib/Data.Maybe.Base.html#373" class="InductiveConstructor"
      >just</a
      ><a name="20179"
      > </a
      ><a name="20180" href="Stlc.html#20160" class="Bound"
      >A</a
      ><a name="20181"
      > </a
      ><a name="20182" class="Symbol"
      >&#8594;</a
      ><a name="20183"
      >
    </a
      ><a name="20188" href="Stlc.html#20156" class="Bound"
      >&#915;</a
      ><a name="20189"
      > </a
      ><a name="20190" href="Stlc.html#20104" class="Datatype Operator"
      >&#8866;</a
      ><a name="20191"
      > </a
      ><a name="20192" href="Stlc.html#3627" class="InductiveConstructor"
      >`</a
      ><a name="20193"
      > </a
      ><a name="20194" href="Stlc.html#20158" class="Bound"
      >x</a
      ><a name="20195"
      > </a
      ><a name="20196" href="Stlc.html#20104" class="Datatype Operator"
      >&#8758;</a
      ><a name="20197"
      > </a
      ><a name="20198" href="Stlc.html#20160" class="Bound"
      >A</a
      ><a name="20199"
      >
  </a
      ><a name="20202" href="Stlc.html#20202" class="InductiveConstructor"
      >&#8658;-I</a
      ><a name="20205"
      > </a
      ><a name="20206" class="Symbol"
      >:</a
      ><a name="20207"
      > </a
      ><a name="20208" class="Symbol"
      >&#8704;</a
      ><a name="20209"
      > </a
      ><a name="20210" class="Symbol"
      >{</a
      ><a name="20211" href="Stlc.html#20211" class="Bound"
      >&#915;</a
      ><a name="20212"
      > </a
      ><a name="20213" href="Stlc.html#20213" class="Bound"
      >x</a
      ><a name="20214"
      > </a
      ><a name="20215" href="Stlc.html#20215" class="Bound"
      >N</a
      ><a name="20216"
      > </a
      ><a name="20217" href="Stlc.html#20217" class="Bound"
      >A</a
      ><a name="20218"
      > </a
      ><a name="20219" href="Stlc.html#20219" class="Bound"
      >B</a
      ><a name="20220" class="Symbol"
      >}</a
      ><a name="20221"
      > </a
      ><a name="20222" class="Symbol"
      >&#8594;</a
      ><a name="20223"
      >
    </a
      ><a name="20228" href="Stlc.html#20211" class="Bound"
      >&#915;</a
      ><a name="20229"
      > </a
      ><a name="20230" href="Maps.html#10368" class="Function Operator"
      >,</a
      ><a name="20231"
      > </a
      ><a name="20232" href="Stlc.html#20213" class="Bound"
      >x</a
      ><a name="20233"
      > </a
      ><a name="20234" href="Maps.html#10368" class="Function Operator"
      >&#8758;</a
      ><a name="20235"
      > </a
      ><a name="20236" href="Stlc.html#20217" class="Bound"
      >A</a
      ><a name="20237"
      > </a
      ><a name="20238" href="Stlc.html#20104" class="Datatype Operator"
      >&#8866;</a
      ><a name="20239"
      > </a
      ><a name="20240" href="Stlc.html#20215" class="Bound"
      >N</a
      ><a name="20241"
      > </a
      ><a name="20242" href="Stlc.html#20104" class="Datatype Operator"
      >&#8758;</a
      ><a name="20243"
      > </a
      ><a name="20244" href="Stlc.html#20219" class="Bound"
      >B</a
      ><a name="20245"
      > </a
      ><a name="20246" class="Symbol"
      >&#8594;</a
      ><a name="20247"
      >
    </a
      ><a name="20252" href="Stlc.html#20211" class="Bound"
      >&#915;</a
      ><a name="20253"
      > </a
      ><a name="20254" href="Stlc.html#20104" class="Datatype Operator"
      >&#8866;</a
      ><a name="20255"
      > </a
      ><a name="20256" href="Stlc.html#3643" class="InductiveConstructor Operator"
      >&#955;[</a
      ><a name="20258"
      > </a
      ><a name="20259" href="Stlc.html#20213" class="Bound"
      >x</a
      ><a name="20260"
      > </a
      ><a name="20261" href="Stlc.html#3643" class="InductiveConstructor Operator"
      >&#8758;</a
      ><a name="20262"
      > </a
      ><a name="20263" href="Stlc.html#20217" class="Bound"
      >A</a
      ><a name="20264"
      > </a
      ><a name="20265" href="Stlc.html#3643" class="InductiveConstructor Operator"
      >]</a
      ><a name="20266"
      > </a
      ><a name="20267" href="Stlc.html#20215" class="Bound"
      >N</a
      ><a name="20268"
      > </a
      ><a name="20269" href="Stlc.html#20104" class="Datatype Operator"
      >&#8758;</a
      ><a name="20270"
      > </a
      ><a name="20271" href="Stlc.html#20217" class="Bound"
      >A</a
      ><a name="20272"
      > </a
      ><a name="20273" href="Stlc.html#2554" class="InductiveConstructor Operator"
      >&#8658;</a
      ><a name="20274"
      > </a
      ><a name="20275" href="Stlc.html#20219" class="Bound"
      >B</a
      ><a name="20276"
      >
  </a
      ><a name="20279" href="Stlc.html#20279" class="InductiveConstructor"
      >&#8658;-E</a
      ><a name="20282"
      > </a
      ><a name="20283" class="Symbol"
      >:</a
      ><a name="20284"
      > </a
      ><a name="20285" class="Symbol"
      >&#8704;</a
      ><a name="20286"
      > </a
      ><a name="20287" class="Symbol"
      >{</a
      ><a name="20288" href="Stlc.html#20288" class="Bound"
      >&#915;</a
      ><a name="20289"
      > </a
      ><a name="20290" href="Stlc.html#20290" class="Bound"
      >L</a
      ><a name="20291"
      > </a
      ><a name="20292" href="Stlc.html#20292" class="Bound"
      >M</a
      ><a name="20293"
      > </a
      ><a name="20294" href="Stlc.html#20294" class="Bound"
      >A</a
      ><a name="20295"
      > </a
      ><a name="20296" href="Stlc.html#20296" class="Bound"
      >B</a
      ><a name="20297" class="Symbol"
      >}</a
      ><a name="20298"
      > </a
      ><a name="20299" class="Symbol"
      >&#8594;</a
      ><a name="20300"
      >
    </a
      ><a name="20305" href="Stlc.html#20288" class="Bound"
      >&#915;</a
      ><a name="20306"
      > </a
      ><a name="20307" href="Stlc.html#20104" class="Datatype Operator"
      >&#8866;</a
      ><a name="20308"
      > </a
      ><a name="20309" href="Stlc.html#20290" class="Bound"
      >L</a
      ><a name="20310"
      > </a
      ><a name="20311" href="Stlc.html#20104" class="Datatype Operator"
      >&#8758;</a
      ><a name="20312"
      > </a
      ><a name="20313" href="Stlc.html#20294" class="Bound"
      >A</a
      ><a name="20314"
      > </a
      ><a name="20315" href="Stlc.html#2554" class="InductiveConstructor Operator"
      >&#8658;</a
      ><a name="20316"
      > </a
      ><a name="20317" href="Stlc.html#20296" class="Bound"
      >B</a
      ><a name="20318"
      > </a
      ><a name="20319" class="Symbol"
      >&#8594;</a
      ><a name="20320"
      >
    </a
      ><a name="20325" href="Stlc.html#20288" class="Bound"
      >&#915;</a
      ><a name="20326"
      > </a
      ><a name="20327" href="Stlc.html#20104" class="Datatype Operator"
      >&#8866;</a
      ><a name="20328"
      > </a
      ><a name="20329" href="Stlc.html#20292" class="Bound"
      >M</a
      ><a name="20330"
      > </a
      ><a name="20331" href="Stlc.html#20104" class="Datatype Operator"
      >&#8758;</a
      ><a name="20332"
      > </a
      ><a name="20333" href="Stlc.html#20294" class="Bound"
      >A</a
      ><a name="20334"
      > </a
      ><a name="20335" class="Symbol"
      >&#8594;</a
      ><a name="20336"
      >
    </a
      ><a name="20341" href="Stlc.html#20288" class="Bound"
      >&#915;</a
      ><a name="20342"
      > </a
      ><a name="20343" href="Stlc.html#20104" class="Datatype Operator"
      >&#8866;</a
      ><a name="20344"
      > </a
      ><a name="20345" href="Stlc.html#20290" class="Bound"
      >L</a
      ><a name="20346"
      > </a
      ><a name="20347" href="Stlc.html#3679" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="20348"
      > </a
      ><a name="20349" href="Stlc.html#20292" class="Bound"
      >M</a
      ><a name="20350"
      > </a
      ><a name="20351" href="Stlc.html#20104" class="Datatype Operator"
      >&#8758;</a
      ><a name="20352"
      > </a
      ><a name="20353" href="Stlc.html#20296" class="Bound"
      >B</a
      ><a name="20354"
      >
  </a
      ><a name="20357" href="Stlc.html#20357" class="InductiveConstructor"
      >&#120121;-I&#8321;</a
      ><a name="20361"
      > </a
      ><a name="20362" class="Symbol"
      >:</a
      ><a name="20363"
      > </a
      ><a name="20364" class="Symbol"
      >&#8704;</a
      ><a name="20365"
      > </a
      ><a name="20366" class="Symbol"
      >{</a
      ><a name="20367" href="Stlc.html#20367" class="Bound"
      >&#915;</a
      ><a name="20368" class="Symbol"
      >}</a
      ><a name="20369"
      > </a
      ><a name="20370" class="Symbol"
      >&#8594;</a
      ><a name="20371"
      >
    </a
      ><a name="20376" href="Stlc.html#20367" class="Bound"
      >&#915;</a
      ><a name="20377"
      > </a
      ><a name="20378" href="Stlc.html#20104" class="Datatype Operator"
      >&#8866;</a
      ><a name="20379"
      > </a
      ><a name="20380" href="Stlc.html#3706" class="InductiveConstructor"
      >true</a
      ><a name="20384"
      > </a
      ><a name="20385" href="Stlc.html#20104" class="Datatype Operator"
      >&#8758;</a
      ><a name="20386"
      > </a
      ><a name="20387" href="Stlc.html#2581" class="InductiveConstructor"
      >&#120121;</a
      ><a name="20388"
      >
  </a
      ><a name="20391" href="Stlc.html#20391" class="InductiveConstructor"
      >&#120121;-I&#8322;</a
      ><a name="20395"
      > </a
      ><a name="20396" class="Symbol"
      >:</a
      ><a name="20397"
      > </a
      ><a name="20398" class="Symbol"
      >&#8704;</a
      ><a name="20399"
      > </a
      ><a name="20400" class="Symbol"
      >{</a
      ><a name="20401" href="Stlc.html#20401" class="Bound"
      >&#915;</a
      ><a name="20402" class="Symbol"
      >}</a
      ><a name="20403"
      > </a
      ><a name="20404" class="Symbol"
      >&#8594;</a
      ><a name="20405"
      >
    </a
      ><a name="20410" href="Stlc.html#20401" class="Bound"
      >&#915;</a
      ><a name="20411"
      > </a
      ><a name="20412" href="Stlc.html#20104" class="Datatype Operator"
      >&#8866;</a
      ><a name="20413"
      > </a
      ><a name="20414" href="Stlc.html#3720" class="InductiveConstructor"
      >false</a
      ><a name="20419"
      > </a
      ><a name="20420" href="Stlc.html#20104" class="Datatype Operator"
      >&#8758;</a
      ><a name="20421"
      > </a
      ><a name="20422" href="Stlc.html#2581" class="InductiveConstructor"
      >&#120121;</a
      ><a name="20423"
      >
  </a
      ><a name="20426" href="Stlc.html#20426" class="InductiveConstructor"
      >&#120121;-E</a
      ><a name="20429"
      > </a
      ><a name="20430" class="Symbol"
      >:</a
      ><a name="20431"
      > </a
      ><a name="20432" class="Symbol"
      >&#8704;</a
      ><a name="20433"
      > </a
      ><a name="20434" class="Symbol"
      >{</a
      ><a name="20435" href="Stlc.html#20435" class="Bound"
      >&#915;</a
      ><a name="20436"
      > </a
      ><a name="20437" href="Stlc.html#20437" class="Bound"
      >L</a
      ><a name="20438"
      > </a
      ><a name="20439" href="Stlc.html#20439" class="Bound"
      >M</a
      ><a name="20440"
      > </a
      ><a name="20441" href="Stlc.html#20441" class="Bound"
      >N</a
      ><a name="20442"
      > </a
      ><a name="20443" href="Stlc.html#20443" class="Bound"
      >A</a
      ><a name="20444" class="Symbol"
      >}</a
      ><a name="20445"
      > </a
      ><a name="20446" class="Symbol"
      >&#8594;</a
      ><a name="20447"
      >
    </a
      ><a name="20452" href="Stlc.html#20435" class="Bound"
      >&#915;</a
      ><a name="20453"
      > </a
      ><a name="20454" href="Stlc.html#20104" class="Datatype Operator"
      >&#8866;</a
      ><a name="20455"
      > </a
      ><a name="20456" href="Stlc.html#20437" class="Bound"
      >L</a
      ><a name="20457"
      > </a
      ><a name="20458" href="Stlc.html#20104" class="Datatype Operator"
      >&#8758;</a
      ><a name="20459"
      > </a
      ><a name="20460" href="Stlc.html#2581" class="InductiveConstructor"
      >&#120121;</a
      ><a name="20461"
      > </a
      ><a name="20462" class="Symbol"
      >&#8594;</a
      ><a name="20463"
      >
    </a
      ><a name="20468" href="Stlc.html#20435" class="Bound"
      >&#915;</a
      ><a name="20469"
      > </a
      ><a name="20470" href="Stlc.html#20104" class="Datatype Operator"
      >&#8866;</a
      ><a name="20471"
      > </a
      ><a name="20472" href="Stlc.html#20439" class="Bound"
      >M</a
      ><a name="20473"
      > </a
      ><a name="20474" href="Stlc.html#20104" class="Datatype Operator"
      >&#8758;</a
      ><a name="20475"
      > </a
      ><a name="20476" href="Stlc.html#20443" class="Bound"
      >A</a
      ><a name="20477"
      > </a
      ><a name="20478" class="Symbol"
      >&#8594;</a
      ><a name="20479"
      >
    </a
      ><a name="20484" href="Stlc.html#20435" class="Bound"
      >&#915;</a
      ><a name="20485"
      > </a
      ><a name="20486" href="Stlc.html#20104" class="Datatype Operator"
      >&#8866;</a
      ><a name="20487"
      > </a
      ><a name="20488" href="Stlc.html#20441" class="Bound"
      >N</a
      ><a name="20489"
      > </a
      ><a name="20490" href="Stlc.html#20104" class="Datatype Operator"
      >&#8758;</a
      ><a name="20491"
      > </a
      ><a name="20492" href="Stlc.html#20443" class="Bound"
      >A</a
      ><a name="20493"
      > </a
      ><a name="20494" class="Symbol"
      >&#8594;</a
      ><a name="20495"
      >
    </a
      ><a name="20500" href="Stlc.html#20435" class="Bound"
      >&#915;</a
      ><a name="20501"
      > </a
      ><a name="20502" href="Stlc.html#20104" class="Datatype Operator"
      >&#8866;</a
      ><a name="20503"
      > </a
      ><a name="20504" href="Stlc.html#3735" class="InductiveConstructor Operator"
      >if</a
      ><a name="20506"
      > </a
      ><a name="20507" href="Stlc.html#20437" class="Bound"
      >L</a
      ><a name="20508"
      > </a
      ><a name="20509" href="Stlc.html#3735" class="InductiveConstructor Operator"
      >then</a
      ><a name="20513"
      > </a
      ><a name="20514" href="Stlc.html#20439" class="Bound"
      >M</a
      ><a name="20515"
      > </a
      ><a name="20516" href="Stlc.html#3735" class="InductiveConstructor Operator"
      >else</a
      ><a name="20520"
      > </a
      ><a name="20521" href="Stlc.html#20441" class="Bound"
      >N</a
      ><a name="20522"
      > </a
      ><a name="20523" href="Stlc.html#20104" class="Datatype Operator"
      >&#8758;</a
      ><a name="20524"
      > </a
      ><a name="20525" href="Stlc.html#20443" class="Bound"
      >A</a
      >

</pre>

## Example type derivations

<pre class="Agda">

<a name="20585" href="Stlc.html#20585" class="Function"
      >typing&#8321;</a
      ><a name="20592"
      > </a
      ><a name="20593" class="Symbol"
      >:</a
      ><a name="20594"
      > </a
      ><a name="20595" href="Maps.html#10265" class="Function"
      >&#8709;</a
      ><a name="20596"
      > </a
      ><a name="20597" href="Stlc.html#20104" class="Datatype Operator"
      >&#8866;</a
      ><a name="20598"
      > </a
      ><a name="20599" href="Stlc.html#5694" class="Function"
      >not</a
      ><a name="20602"
      > </a
      ><a name="20603" href="Stlc.html#20104" class="Datatype Operator"
      >&#8758;</a
      ><a name="20604"
      > </a
      ><a name="20605" href="Stlc.html#2581" class="InductiveConstructor"
      >&#120121;</a
      ><a name="20606"
      > </a
      ><a name="20607" href="Stlc.html#2554" class="InductiveConstructor Operator"
      >&#8658;</a
      ><a name="20608"
      > </a
      ><a name="20609" href="Stlc.html#2581" class="InductiveConstructor"
      >&#120121;</a
      ><a name="20610"
      >
</a
      ><a name="20611" href="Stlc.html#20585" class="Function"
      >typing&#8321;</a
      ><a name="20618"
      > </a
      ><a name="20619" class="Symbol"
      >=</a
      ><a name="20620"
      > </a
      ><a name="20621" href="Stlc.html#20202" class="InductiveConstructor"
      >&#8658;-I</a
      ><a name="20624"
      > </a
      ><a name="20625" class="Symbol"
      >(</a
      ><a name="20626" href="Stlc.html#20426" class="InductiveConstructor"
      >&#120121;-E</a
      ><a name="20629"
      > </a
      ><a name="20630" class="Symbol"
      >(</a
      ><a name="20631" href="Stlc.html#20148" class="InductiveConstructor"
      >Ax</a
      ><a name="20633"
      > </a
      ><a name="20634" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="20638" class="Symbol"
      >)</a
      ><a name="20639"
      > </a
      ><a name="20640" href="Stlc.html#20391" class="InductiveConstructor"
      >&#120121;-I&#8322;</a
      ><a name="20644"
      > </a
      ><a name="20645" href="Stlc.html#20357" class="InductiveConstructor"
      >&#120121;-I&#8321;</a
      ><a name="20649" class="Symbol"
      >)</a
      ><a name="20650"
      >

</a
      ><a name="20652" href="Stlc.html#20652" class="Function"
      >typing&#8322;</a
      ><a name="20659"
      > </a
      ><a name="20660" class="Symbol"
      >:</a
      ><a name="20661"
      > </a
      ><a name="20662" href="Maps.html#10265" class="Function"
      >&#8709;</a
      ><a name="20663"
      > </a
      ><a name="20664" href="Stlc.html#20104" class="Datatype Operator"
      >&#8866;</a
      ><a name="20665"
      > </a
      ><a name="20666" href="Stlc.html#5698" class="Function"
      >two</a
      ><a name="20669"
      > </a
      ><a name="20670" href="Stlc.html#20104" class="Datatype Operator"
      >&#8758;</a
      ><a name="20671"
      > </a
      ><a name="20672" class="Symbol"
      >(</a
      ><a name="20673" href="Stlc.html#2581" class="InductiveConstructor"
      >&#120121;</a
      ><a name="20674"
      > </a
      ><a name="20675" href="Stlc.html#2554" class="InductiveConstructor Operator"
      >&#8658;</a
      ><a name="20676"
      > </a
      ><a name="20677" href="Stlc.html#2581" class="InductiveConstructor"
      >&#120121;</a
      ><a name="20678" class="Symbol"
      >)</a
      ><a name="20679"
      > </a
      ><a name="20680" href="Stlc.html#2554" class="InductiveConstructor Operator"
      >&#8658;</a
      ><a name="20681"
      > </a
      ><a name="20682" href="Stlc.html#2581" class="InductiveConstructor"
      >&#120121;</a
      ><a name="20683"
      > </a
      ><a name="20684" href="Stlc.html#2554" class="InductiveConstructor Operator"
      >&#8658;</a
      ><a name="20685"
      > </a
      ><a name="20686" href="Stlc.html#2581" class="InductiveConstructor"
      >&#120121;</a
      ><a name="20687"
      >
</a
      ><a name="20688" href="Stlc.html#20652" class="Function"
      >typing&#8322;</a
      ><a name="20695"
      > </a
      ><a name="20696" class="Symbol"
      >=</a
      ><a name="20697"
      > </a
      ><a name="20698" href="Stlc.html#20202" class="InductiveConstructor"
      >&#8658;-I</a
      ><a name="20701"
      > </a
      ><a name="20702" class="Symbol"
      >(</a
      ><a name="20703" href="Stlc.html#20202" class="InductiveConstructor"
      >&#8658;-I</a
      ><a name="20706"
      > </a
      ><a name="20707" class="Symbol"
      >(</a
      ><a name="20708" href="Stlc.html#20279" class="InductiveConstructor"
      >&#8658;-E</a
      ><a name="20711"
      > </a
      ><a name="20712" class="Symbol"
      >(</a
      ><a name="20713" href="Stlc.html#20148" class="InductiveConstructor"
      >Ax</a
      ><a name="20715"
      > </a
      ><a name="20716" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="20720" class="Symbol"
      >)</a
      ><a name="20721"
      > </a
      ><a name="20722" class="Symbol"
      >(</a
      ><a name="20723" href="Stlc.html#20279" class="InductiveConstructor"
      >&#8658;-E</a
      ><a name="20726"
      > </a
      ><a name="20727" class="Symbol"
      >(</a
      ><a name="20728" href="Stlc.html#20148" class="InductiveConstructor"
      >Ax</a
      ><a name="20730"
      > </a
      ><a name="20731" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="20735" class="Symbol"
      >)</a
      ><a name="20736"
      > </a
      ><a name="20737" class="Symbol"
      >(</a
      ><a name="20738" href="Stlc.html#20148" class="InductiveConstructor"
      >Ax</a
      ><a name="20740"
      > </a
      ><a name="20741" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="20745" class="Symbol"
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


