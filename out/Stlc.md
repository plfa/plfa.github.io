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
      >;</a
      ><a name="1840"
      > </a
      ><a name="1841" href="Maps.html#11919" class="Function"
      >just-injective</a
      ><a name="1855" class="Symbol"
      >)</a
      ><a name="1856"
      > </a
      ><a name="1857" class="Keyword"
      >renaming</a
      ><a name="1865"
      > </a
      ><a name="1866" class="Symbol"
      >(</a
      ><a name="1867" href="Maps.html#10368" class="Function Operator"
      >_,_&#8614;_</a
      ><a name="1872"
      > </a
      ><a name="1873" class="Symbol"
      >to</a
      ><a name="1875"
      > </a
      ><a name="1876" href="Maps.html#10368" class="Function Operator"
      >_,_&#8758;_</a
      ><a name="1881" class="Symbol"
      >)</a
      ><a name="1882"
      >
</a
      ><a name="1883" class="Keyword"
      >open</a
      ><a name="1887"
      > </a
      ><a name="1888" class="Keyword"
      >import</a
      ><a name="1894"
      > </a
      ><a name="1895" href="https://agda.github.io/agda-stdlib/Data.Nat.html#1" class="Module"
      >Data.Nat</a
      ><a name="1903"
      > </a
      ><a name="1904" class="Keyword"
      >using</a
      ><a name="1909"
      > </a
      ><a name="1910" class="Symbol"
      >(</a
      ><a name="1911" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#97" class="Datatype"
      >&#8469;</a
      ><a name="1912" class="Symbol"
      >)</a
      ><a name="1913"
      >
</a
      ><a name="1914" class="Keyword"
      >open</a
      ><a name="1918"
      > </a
      ><a name="1919" class="Keyword"
      >import</a
      ><a name="1925"
      > </a
      ><a name="1926" href="https://agda.github.io/agda-stdlib/Data.Maybe.html#1" class="Module"
      >Data.Maybe</a
      ><a name="1936"
      > </a
      ><a name="1937" class="Keyword"
      >using</a
      ><a name="1942"
      > </a
      ><a name="1943" class="Symbol"
      >(</a
      ><a name="1944" href="https://agda.github.io/agda-stdlib/Data.Maybe.Base.html#335" class="Datatype"
      >Maybe</a
      ><a name="1949" class="Symbol"
      >;</a
      ><a name="1950"
      > </a
      ><a name="1951" href="https://agda.github.io/agda-stdlib/Data.Maybe.html#1527" class="InductiveConstructor"
      >just</a
      ><a name="1955" class="Symbol"
      >;</a
      ><a name="1956"
      > </a
      ><a name="1957" href="https://agda.github.io/agda-stdlib/Data.Maybe.html#1588" class="InductiveConstructor"
      >nothing</a
      ><a name="1964" class="Symbol"
      >)</a
      ><a name="1965"
      >
</a
      ><a name="1966" class="Keyword"
      >open</a
      ><a name="1970"
      > </a
      ><a name="1971" class="Keyword"
      >import</a
      ><a name="1977"
      > </a
      ><a name="1978" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#1" class="Module"
      >Relation.Nullary</a
      ><a name="1994"
      > </a
      ><a name="1995" class="Keyword"
      >using</a
      ><a name="2000"
      > </a
      ><a name="2001" class="Symbol"
      >(</a
      ><a name="2002" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#484" class="Datatype"
      >Dec</a
      ><a name="2005" class="Symbol"
      >;</a
      ><a name="2006"
      > </a
      ><a name="2007" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#520" class="InductiveConstructor"
      >yes</a
      ><a name="2010" class="Symbol"
      >;</a
      ><a name="2011"
      > </a
      ><a name="2012" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#547" class="InductiveConstructor"
      >no</a
      ><a name="2014" class="Symbol"
      >;</a
      ><a name="2015"
      > </a
      ><a name="2016" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#414" class="Function Operator"
      >&#172;_</a
      ><a name="2018" class="Symbol"
      >)</a
      ><a name="2019"
      >
</a
      ><a name="2020" class="Keyword"
      >open</a
      ><a name="2024"
      > </a
      ><a name="2025" class="Keyword"
      >import</a
      ><a name="2031"
      > </a
      ><a name="2032" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#1" class="Module"
      >Relation.Binary.PropositionalEquality</a
      ><a name="2069"
      > </a
      ><a name="2070" class="Keyword"
      >using</a
      ><a name="2075"
      > </a
      ><a name="2076" class="Symbol"
      >(</a
      ><a name="2077" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >_&#8801;_</a
      ><a name="2080" class="Symbol"
      >;</a
      ><a name="2081"
      > </a
      ><a name="2082" href="https://agda.github.io/agda-stdlib/Relation.Binary.Core.html#4493" class="Function Operator"
      >_&#8802;_</a
      ><a name="2085" class="Symbol"
      >;</a
      ><a name="2086"
      > </a
      ><a name="2087" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="2091" class="Symbol"
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

<a name="2535" class="Keyword"
      >infixr</a
      ><a name="2541"
      > </a
      ><a name="2542" class="Number"
      >20</a
      ><a name="2544"
      > </a
      ><a name="2545" href="Stlc.html#2574" class="InductiveConstructor Operator"
      >_&#8658;_</a
      ><a name="2548"
      >

</a
      ><a name="2550" class="Keyword"
      >data</a
      ><a name="2554"
      > </a
      ><a name="2555" href="Stlc.html#2555" class="Datatype"
      >Type</a
      ><a name="2559"
      > </a
      ><a name="2560" class="Symbol"
      >:</a
      ><a name="2561"
      > </a
      ><a name="2562" class="PrimitiveType"
      >Set</a
      ><a name="2565"
      > </a
      ><a name="2566" class="Keyword"
      >where</a
      ><a name="2571"
      >
  </a
      ><a name="2574" href="Stlc.html#2574" class="InductiveConstructor Operator"
      >_&#8658;_</a
      ><a name="2577"
      > </a
      ><a name="2578" class="Symbol"
      >:</a
      ><a name="2579"
      > </a
      ><a name="2580" href="Stlc.html#2555" class="Datatype"
      >Type</a
      ><a name="2584"
      > </a
      ><a name="2585" class="Symbol"
      >&#8594;</a
      ><a name="2586"
      > </a
      ><a name="2587" href="Stlc.html#2555" class="Datatype"
      >Type</a
      ><a name="2591"
      > </a
      ><a name="2592" class="Symbol"
      >&#8594;</a
      ><a name="2593"
      > </a
      ><a name="2594" href="Stlc.html#2555" class="Datatype"
      >Type</a
      ><a name="2598"
      >
  </a
      ><a name="2601" href="Stlc.html#2601" class="InductiveConstructor"
      >&#120121;</a
      ><a name="2602"
      > </a
      ><a name="2603" class="Symbol"
      >:</a
      ><a name="2604"
      > </a
      ><a name="2605" href="Stlc.html#2555" class="Datatype"
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

<a name="3566" class="Keyword"
      >infixl</a
      ><a name="3572"
      > </a
      ><a name="3573" class="Number"
      >20</a
      ><a name="3575"
      > </a
      ><a name="3576" href="Stlc.html#3699" class="InductiveConstructor Operator"
      >_&#183;_</a
      ><a name="3579"
      >
</a
      ><a name="3580" class="Keyword"
      >infix</a
      ><a name="3585"
      >  </a
      ><a name="3587" class="Number"
      >15</a
      ><a name="3589"
      > </a
      ><a name="3590" href="Stlc.html#3663" class="InductiveConstructor Operator"
      >&#955;[_&#8758;_]_</a
      ><a name="3597"
      >
</a
      ><a name="3598" class="Keyword"
      >infix</a
      ><a name="3603"
      >  </a
      ><a name="3605" class="Number"
      >15</a
      ><a name="3607"
      > </a
      ><a name="3608" href="Stlc.html#3755" class="InductiveConstructor Operator"
      >if_then_else_</a
      ><a name="3621"
      >

</a
      ><a name="3623" class="Keyword"
      >data</a
      ><a name="3627"
      > </a
      ><a name="3628" href="Stlc.html#3628" class="Datatype"
      >Term</a
      ><a name="3632"
      > </a
      ><a name="3633" class="Symbol"
      >:</a
      ><a name="3634"
      > </a
      ><a name="3635" class="PrimitiveType"
      >Set</a
      ><a name="3638"
      > </a
      ><a name="3639" class="Keyword"
      >where</a
      ><a name="3644"
      >
  </a
      ><a name="3647" href="Stlc.html#3647" class="InductiveConstructor"
      >`</a
      ><a name="3648"
      > </a
      ><a name="3649" class="Symbol"
      >:</a
      ><a name="3650"
      > </a
      ><a name="3651" href="Maps.html#2171" class="Datatype"
      >Id</a
      ><a name="3653"
      > </a
      ><a name="3654" class="Symbol"
      >&#8594;</a
      ><a name="3655"
      > </a
      ><a name="3656" href="Stlc.html#3628" class="Datatype"
      >Term</a
      ><a name="3660"
      >
  </a
      ><a name="3663" href="Stlc.html#3663" class="InductiveConstructor Operator"
      >&#955;[_&#8758;_]_</a
      ><a name="3670"
      > </a
      ><a name="3671" class="Symbol"
      >:</a
      ><a name="3672"
      > </a
      ><a name="3673" href="Maps.html#2171" class="Datatype"
      >Id</a
      ><a name="3675"
      > </a
      ><a name="3676" class="Symbol"
      >&#8594;</a
      ><a name="3677"
      > </a
      ><a name="3678" href="Stlc.html#2555" class="Datatype"
      >Type</a
      ><a name="3682"
      > </a
      ><a name="3683" class="Symbol"
      >&#8594;</a
      ><a name="3684"
      > </a
      ><a name="3685" href="Stlc.html#3628" class="Datatype"
      >Term</a
      ><a name="3689"
      > </a
      ><a name="3690" class="Symbol"
      >&#8594;</a
      ><a name="3691"
      > </a
      ><a name="3692" href="Stlc.html#3628" class="Datatype"
      >Term</a
      ><a name="3696"
      >
  </a
      ><a name="3699" href="Stlc.html#3699" class="InductiveConstructor Operator"
      >_&#183;_</a
      ><a name="3702"
      > </a
      ><a name="3703" class="Symbol"
      >:</a
      ><a name="3704"
      > </a
      ><a name="3705" href="Stlc.html#3628" class="Datatype"
      >Term</a
      ><a name="3709"
      > </a
      ><a name="3710" class="Symbol"
      >&#8594;</a
      ><a name="3711"
      > </a
      ><a name="3712" href="Stlc.html#3628" class="Datatype"
      >Term</a
      ><a name="3716"
      > </a
      ><a name="3717" class="Symbol"
      >&#8594;</a
      ><a name="3718"
      > </a
      ><a name="3719" href="Stlc.html#3628" class="Datatype"
      >Term</a
      ><a name="3723"
      >
  </a
      ><a name="3726" href="Stlc.html#3726" class="InductiveConstructor"
      >true</a
      ><a name="3730"
      > </a
      ><a name="3731" class="Symbol"
      >:</a
      ><a name="3732"
      > </a
      ><a name="3733" href="Stlc.html#3628" class="Datatype"
      >Term</a
      ><a name="3737"
      >
  </a
      ><a name="3740" href="Stlc.html#3740" class="InductiveConstructor"
      >false</a
      ><a name="3745"
      > </a
      ><a name="3746" class="Symbol"
      >:</a
      ><a name="3747"
      > </a
      ><a name="3748" href="Stlc.html#3628" class="Datatype"
      >Term</a
      ><a name="3752"
      >
  </a
      ><a name="3755" href="Stlc.html#3755" class="InductiveConstructor Operator"
      >if_then_else_</a
      ><a name="3768"
      > </a
      ><a name="3769" class="Symbol"
      >:</a
      ><a name="3770"
      > </a
      ><a name="3771" href="Stlc.html#3628" class="Datatype"
      >Term</a
      ><a name="3775"
      > </a
      ><a name="3776" class="Symbol"
      >&#8594;</a
      ><a name="3777"
      > </a
      ><a name="3778" href="Stlc.html#3628" class="Datatype"
      >Term</a
      ><a name="3782"
      > </a
      ><a name="3783" class="Symbol"
      >&#8594;</a
      ><a name="3784"
      > </a
      ><a name="3785" href="Stlc.html#3628" class="Datatype"
      >Term</a
      ><a name="3789"
      > </a
      ><a name="3790" class="Symbol"
      >&#8594;</a
      ><a name="3791"
      > </a
      ><a name="3792" href="Stlc.html#3628" class="Datatype"
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

<a name="5669" href="Stlc.html#5669" class="Function"
      >f</a
      ><a name="5670"
      > </a
      ><a name="5671" href="Stlc.html#5671" class="Function"
      >x</a
      ><a name="5672"
      > </a
      ><a name="5673" href="Stlc.html#5673" class="Function"
      >y</a
      ><a name="5674"
      > </a
      ><a name="5675" class="Symbol"
      >:</a
      ><a name="5676"
      > </a
      ><a name="5677" href="Maps.html#2171" class="Datatype"
      >Id</a
      ><a name="5679"
      >
</a
      ><a name="5680" href="Stlc.html#5669" class="Function"
      >f</a
      ><a name="5681"
      >  </a
      ><a name="5683" class="Symbol"
      >=</a
      ><a name="5684"
      >  </a
      ><a name="5686" href="Maps.html#2188" class="InductiveConstructor"
      >id</a
      ><a name="5688"
      > </a
      ><a name="5689" class="Number"
      >0</a
      ><a name="5690"
      >
</a
      ><a name="5691" href="Stlc.html#5671" class="Function"
      >x</a
      ><a name="5692"
      >  </a
      ><a name="5694" class="Symbol"
      >=</a
      ><a name="5695"
      >  </a
      ><a name="5697" href="Maps.html#2188" class="InductiveConstructor"
      >id</a
      ><a name="5699"
      > </a
      ><a name="5700" class="Number"
      >1</a
      ><a name="5701"
      >
</a
      ><a name="5702" href="Stlc.html#5673" class="Function"
      >y</a
      ><a name="5703"
      >  </a
      ><a name="5705" class="Symbol"
      >=</a
      ><a name="5706"
      >  </a
      ><a name="5708" href="Maps.html#2188" class="InductiveConstructor"
      >id</a
      ><a name="5710"
      > </a
      ><a name="5711" class="Number"
      >2</a
      ><a name="5712"
      >

</a
      ><a name="5714" href="Stlc.html#5714" class="Function"
      >not</a
      ><a name="5717"
      > </a
      ><a name="5718" href="Stlc.html#5718" class="Function"
      >two</a
      ><a name="5721"
      > </a
      ><a name="5722" class="Symbol"
      >:</a
      ><a name="5723"
      > </a
      ><a name="5724" href="Stlc.html#3628" class="Datatype"
      >Term</a
      ><a name="5728"
      > 
</a
      ><a name="5730" href="Stlc.html#5714" class="Function"
      >not</a
      ><a name="5733"
      > </a
      ><a name="5734" class="Symbol"
      >=</a
      ><a name="5735"
      >  </a
      ><a name="5737" href="Stlc.html#3663" class="InductiveConstructor Operator"
      >&#955;[</a
      ><a name="5739"
      > </a
      ><a name="5740" href="Stlc.html#5671" class="Function"
      >x</a
      ><a name="5741"
      > </a
      ><a name="5742" href="Stlc.html#3663" class="InductiveConstructor Operator"
      >&#8758;</a
      ><a name="5743"
      > </a
      ><a name="5744" href="Stlc.html#2601" class="InductiveConstructor"
      >&#120121;</a
      ><a name="5745"
      > </a
      ><a name="5746" href="Stlc.html#3663" class="InductiveConstructor Operator"
      >]</a
      ><a name="5747"
      > </a
      ><a name="5748" class="Symbol"
      >(</a
      ><a name="5749" href="Stlc.html#3755" class="InductiveConstructor Operator"
      >if</a
      ><a name="5751"
      > </a
      ><a name="5752" href="Stlc.html#3647" class="InductiveConstructor"
      >`</a
      ><a name="5753"
      > </a
      ><a name="5754" href="Stlc.html#5671" class="Function"
      >x</a
      ><a name="5755"
      > </a
      ><a name="5756" href="Stlc.html#3755" class="InductiveConstructor Operator"
      >then</a
      ><a name="5760"
      > </a
      ><a name="5761" href="Stlc.html#3740" class="InductiveConstructor"
      >false</a
      ><a name="5766"
      > </a
      ><a name="5767" href="Stlc.html#3755" class="InductiveConstructor Operator"
      >else</a
      ><a name="5771"
      > </a
      ><a name="5772" href="Stlc.html#3726" class="InductiveConstructor"
      >true</a
      ><a name="5776" class="Symbol"
      >)</a
      ><a name="5777"
      >
</a
      ><a name="5778" href="Stlc.html#5718" class="Function"
      >two</a
      ><a name="5781"
      > </a
      ><a name="5782" class="Symbol"
      >=</a
      ><a name="5783"
      >  </a
      ><a name="5785" href="Stlc.html#3663" class="InductiveConstructor Operator"
      >&#955;[</a
      ><a name="5787"
      > </a
      ><a name="5788" href="Stlc.html#5669" class="Function"
      >f</a
      ><a name="5789"
      > </a
      ><a name="5790" href="Stlc.html#3663" class="InductiveConstructor Operator"
      >&#8758;</a
      ><a name="5791"
      > </a
      ><a name="5792" href="Stlc.html#2601" class="InductiveConstructor"
      >&#120121;</a
      ><a name="5793"
      > </a
      ><a name="5794" href="Stlc.html#2574" class="InductiveConstructor Operator"
      >&#8658;</a
      ><a name="5795"
      > </a
      ><a name="5796" href="Stlc.html#2601" class="InductiveConstructor"
      >&#120121;</a
      ><a name="5797"
      > </a
      ><a name="5798" href="Stlc.html#3663" class="InductiveConstructor Operator"
      >]</a
      ><a name="5799"
      > </a
      ><a name="5800" href="Stlc.html#3663" class="InductiveConstructor Operator"
      >&#955;[</a
      ><a name="5802"
      > </a
      ><a name="5803" href="Stlc.html#5671" class="Function"
      >x</a
      ><a name="5804"
      > </a
      ><a name="5805" href="Stlc.html#3663" class="InductiveConstructor Operator"
      >&#8758;</a
      ><a name="5806"
      > </a
      ><a name="5807" href="Stlc.html#2601" class="InductiveConstructor"
      >&#120121;</a
      ><a name="5808"
      > </a
      ><a name="5809" href="Stlc.html#3663" class="InductiveConstructor Operator"
      >]</a
      ><a name="5810"
      > </a
      ><a name="5811" href="Stlc.html#3647" class="InductiveConstructor"
      >`</a
      ><a name="5812"
      > </a
      ><a name="5813" href="Stlc.html#5669" class="Function"
      >f</a
      ><a name="5814"
      > </a
      ><a name="5815" href="Stlc.html#3699" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="5816"
      > </a
      ><a name="5817" class="Symbol"
      >(</a
      ><a name="5818" href="Stlc.html#3647" class="InductiveConstructor"
      >`</a
      ><a name="5819"
      > </a
      ><a name="5820" href="Stlc.html#5669" class="Function"
      >f</a
      ><a name="5821"
      > </a
      ><a name="5822" href="Stlc.html#3699" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="5823"
      > </a
      ><a name="5824" href="Stlc.html#3647" class="InductiveConstructor"
      >`</a
      ><a name="5825"
      > </a
      ><a name="5826" href="Stlc.html#5671" class="Function"
      >x</a
      ><a name="5827" class="Symbol"
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

<a name="8236" href="Stlc.html#8236" class="Function"
      >ex&#8321;</a
      ><a name="8239"
      > </a
      ><a name="8240" class="Symbol"
      >:</a
      ><a name="8241"
      > </a
      ><a name="8242" class="Symbol"
      >(</a
      ><a name="8243" href="Stlc.html#2601" class="InductiveConstructor"
      >&#120121;</a
      ><a name="8244"
      > </a
      ><a name="8245" href="Stlc.html#2574" class="InductiveConstructor Operator"
      >&#8658;</a
      ><a name="8246"
      > </a
      ><a name="8247" href="Stlc.html#2601" class="InductiveConstructor"
      >&#120121;</a
      ><a name="8248" class="Symbol"
      >)</a
      ><a name="8249"
      > </a
      ><a name="8250" href="Stlc.html#2574" class="InductiveConstructor Operator"
      >&#8658;</a
      ><a name="8251"
      > </a
      ><a name="8252" href="Stlc.html#2601" class="InductiveConstructor"
      >&#120121;</a
      ><a name="8253"
      > </a
      ><a name="8254" href="Stlc.html#2574" class="InductiveConstructor Operator"
      >&#8658;</a
      ><a name="8255"
      > </a
      ><a name="8256" href="Stlc.html#2601" class="InductiveConstructor"
      >&#120121;</a
      ><a name="8257"
      > </a
      ><a name="8258" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="8259"
      > </a
      ><a name="8260" class="Symbol"
      >(</a
      ><a name="8261" href="Stlc.html#2601" class="InductiveConstructor"
      >&#120121;</a
      ><a name="8262"
      > </a
      ><a name="8263" href="Stlc.html#2574" class="InductiveConstructor Operator"
      >&#8658;</a
      ><a name="8264"
      > </a
      ><a name="8265" href="Stlc.html#2601" class="InductiveConstructor"
      >&#120121;</a
      ><a name="8266" class="Symbol"
      >)</a
      ><a name="8267"
      > </a
      ><a name="8268" href="Stlc.html#2574" class="InductiveConstructor Operator"
      >&#8658;</a
      ><a name="8269"
      > </a
      ><a name="8270" class="Symbol"
      >(</a
      ><a name="8271" href="Stlc.html#2601" class="InductiveConstructor"
      >&#120121;</a
      ><a name="8272"
      > </a
      ><a name="8273" href="Stlc.html#2574" class="InductiveConstructor Operator"
      >&#8658;</a
      ><a name="8274"
      > </a
      ><a name="8275" href="Stlc.html#2601" class="InductiveConstructor"
      >&#120121;</a
      ><a name="8276" class="Symbol"
      >)</a
      ><a name="8277"
      >
</a
      ><a name="8278" href="Stlc.html#8236" class="Function"
      >ex&#8321;</a
      ><a name="8281"
      > </a
      ><a name="8282" class="Symbol"
      >=</a
      ><a name="8283"
      > </a
      ><a name="8284" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="8288"
      >

</a
      ><a name="8290" href="Stlc.html#8290" class="Function"
      >ex&#8322;</a
      ><a name="8293"
      > </a
      ><a name="8294" class="Symbol"
      >:</a
      ><a name="8295"
      > </a
      ><a name="8296" href="Stlc.html#5718" class="Function"
      >two</a
      ><a name="8299"
      > </a
      ><a name="8300" href="Stlc.html#3699" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="8301"
      > </a
      ><a name="8302" href="Stlc.html#5714" class="Function"
      >not</a
      ><a name="8305"
      > </a
      ><a name="8306" href="Stlc.html#3699" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="8307"
      > </a
      ><a name="8308" href="Stlc.html#3726" class="InductiveConstructor"
      >true</a
      ><a name="8312"
      > </a
      ><a name="8313" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="8314"
      > </a
      ><a name="8315" class="Symbol"
      >(</a
      ><a name="8316" href="Stlc.html#5718" class="Function"
      >two</a
      ><a name="8319"
      > </a
      ><a name="8320" href="Stlc.html#3699" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="8321"
      > </a
      ><a name="8322" href="Stlc.html#5714" class="Function"
      >not</a
      ><a name="8325" class="Symbol"
      >)</a
      ><a name="8326"
      > </a
      ><a name="8327" href="Stlc.html#3699" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="8328"
      > </a
      ><a name="8329" href="Stlc.html#3726" class="InductiveConstructor"
      >true</a
      ><a name="8333"
      >
</a
      ><a name="8334" href="Stlc.html#8290" class="Function"
      >ex&#8322;</a
      ><a name="8337"
      > </a
      ><a name="8338" class="Symbol"
      >=</a
      ><a name="8339"
      > </a
      ><a name="8340" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="8344"
      >

</a
      ><a name="8346" href="Stlc.html#8346" class="Function"
      >ex&#8323;</a
      ><a name="8349"
      > </a
      ><a name="8350" class="Symbol"
      >:</a
      ><a name="8351"
      > </a
      ><a name="8352" href="Stlc.html#3663" class="InductiveConstructor Operator"
      >&#955;[</a
      ><a name="8354"
      > </a
      ><a name="8355" href="Stlc.html#5669" class="Function"
      >f</a
      ><a name="8356"
      > </a
      ><a name="8357" href="Stlc.html#3663" class="InductiveConstructor Operator"
      >&#8758;</a
      ><a name="8358"
      > </a
      ><a name="8359" href="Stlc.html#2601" class="InductiveConstructor"
      >&#120121;</a
      ><a name="8360"
      > </a
      ><a name="8361" href="Stlc.html#2574" class="InductiveConstructor Operator"
      >&#8658;</a
      ><a name="8362"
      > </a
      ><a name="8363" href="Stlc.html#2601" class="InductiveConstructor"
      >&#120121;</a
      ><a name="8364"
      > </a
      ><a name="8365" href="Stlc.html#3663" class="InductiveConstructor Operator"
      >]</a
      ><a name="8366"
      > </a
      ><a name="8367" href="Stlc.html#3663" class="InductiveConstructor Operator"
      >&#955;[</a
      ><a name="8369"
      > </a
      ><a name="8370" href="Stlc.html#5671" class="Function"
      >x</a
      ><a name="8371"
      > </a
      ><a name="8372" href="Stlc.html#3663" class="InductiveConstructor Operator"
      >&#8758;</a
      ><a name="8373"
      > </a
      ><a name="8374" href="Stlc.html#2601" class="InductiveConstructor"
      >&#120121;</a
      ><a name="8375"
      > </a
      ><a name="8376" href="Stlc.html#3663" class="InductiveConstructor Operator"
      >]</a
      ><a name="8377"
      > </a
      ><a name="8378" href="Stlc.html#3647" class="InductiveConstructor"
      >`</a
      ><a name="8379"
      > </a
      ><a name="8380" href="Stlc.html#5669" class="Function"
      >f</a
      ><a name="8381"
      > </a
      ><a name="8382" href="Stlc.html#3699" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="8383"
      > </a
      ><a name="8384" class="Symbol"
      >(</a
      ><a name="8385" href="Stlc.html#3647" class="InductiveConstructor"
      >`</a
      ><a name="8386"
      > </a
      ><a name="8387" href="Stlc.html#5669" class="Function"
      >f</a
      ><a name="8388"
      > </a
      ><a name="8389" href="Stlc.html#3699" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="8390"
      > </a
      ><a name="8391" href="Stlc.html#3647" class="InductiveConstructor"
      >`</a
      ><a name="8392"
      > </a
      ><a name="8393" href="Stlc.html#5671" class="Function"
      >x</a
      ><a name="8394" class="Symbol"
      >)</a
      ><a name="8395"
      >
      </a
      ><a name="8402" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="8403"
      > </a
      ><a name="8404" class="Symbol"
      >(</a
      ><a name="8405" href="Stlc.html#3663" class="InductiveConstructor Operator"
      >&#955;[</a
      ><a name="8407"
      > </a
      ><a name="8408" href="Stlc.html#5669" class="Function"
      >f</a
      ><a name="8409"
      > </a
      ><a name="8410" href="Stlc.html#3663" class="InductiveConstructor Operator"
      >&#8758;</a
      ><a name="8411"
      > </a
      ><a name="8412" href="Stlc.html#2601" class="InductiveConstructor"
      >&#120121;</a
      ><a name="8413"
      > </a
      ><a name="8414" href="Stlc.html#2574" class="InductiveConstructor Operator"
      >&#8658;</a
      ><a name="8415"
      > </a
      ><a name="8416" href="Stlc.html#2601" class="InductiveConstructor"
      >&#120121;</a
      ><a name="8417"
      > </a
      ><a name="8418" href="Stlc.html#3663" class="InductiveConstructor Operator"
      >]</a
      ><a name="8419"
      > </a
      ><a name="8420" class="Symbol"
      >(</a
      ><a name="8421" href="Stlc.html#3663" class="InductiveConstructor Operator"
      >&#955;[</a
      ><a name="8423"
      > </a
      ><a name="8424" href="Stlc.html#5671" class="Function"
      >x</a
      ><a name="8425"
      > </a
      ><a name="8426" href="Stlc.html#3663" class="InductiveConstructor Operator"
      >&#8758;</a
      ><a name="8427"
      > </a
      ><a name="8428" href="Stlc.html#2601" class="InductiveConstructor"
      >&#120121;</a
      ><a name="8429"
      > </a
      ><a name="8430" href="Stlc.html#3663" class="InductiveConstructor Operator"
      >]</a
      ><a name="8431"
      > </a
      ><a name="8432" class="Symbol"
      >(</a
      ><a name="8433" href="Stlc.html#3647" class="InductiveConstructor"
      >`</a
      ><a name="8434"
      > </a
      ><a name="8435" href="Stlc.html#5669" class="Function"
      >f</a
      ><a name="8436"
      > </a
      ><a name="8437" href="Stlc.html#3699" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="8438"
      > </a
      ><a name="8439" class="Symbol"
      >(</a
      ><a name="8440" href="Stlc.html#3647" class="InductiveConstructor"
      >`</a
      ><a name="8441"
      > </a
      ><a name="8442" href="Stlc.html#5669" class="Function"
      >f</a
      ><a name="8443"
      > </a
      ><a name="8444" href="Stlc.html#3699" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="8445"
      > </a
      ><a name="8446" href="Stlc.html#3647" class="InductiveConstructor"
      >`</a
      ><a name="8447"
      > </a
      ><a name="8448" href="Stlc.html#5671" class="Function"
      >x</a
      ><a name="8449" class="Symbol"
      >))))</a
      ><a name="8453"
      >
</a
      ><a name="8454" href="Stlc.html#8346" class="Function"
      >ex&#8323;</a
      ><a name="8457"
      > </a
      ><a name="8458" class="Symbol"
      >=</a
      ><a name="8459"
      > </a
      ><a name="8460" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
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

<a name="9521" class="Keyword"
      >data</a
      ><a name="9525"
      > </a
      ><a name="9526" href="Stlc.html#9526" class="Datatype"
      >Value</a
      ><a name="9531"
      > </a
      ><a name="9532" class="Symbol"
      >:</a
      ><a name="9533"
      > </a
      ><a name="9534" href="Stlc.html#3628" class="Datatype"
      >Term</a
      ><a name="9538"
      > </a
      ><a name="9539" class="Symbol"
      >&#8594;</a
      ><a name="9540"
      > </a
      ><a name="9541" class="PrimitiveType"
      >Set</a
      ><a name="9544"
      > </a
      ><a name="9545" class="Keyword"
      >where</a
      ><a name="9550"
      >
  </a
      ><a name="9553" href="Stlc.html#9553" class="InductiveConstructor"
      >value-&#955;</a
      ><a name="9560"
      >     </a
      ><a name="9565" class="Symbol"
      >:</a
      ><a name="9566"
      > </a
      ><a name="9567" class="Symbol"
      >&#8704;</a
      ><a name="9568"
      > </a
      ><a name="9569" class="Symbol"
      >{</a
      ><a name="9570" href="Stlc.html#9570" class="Bound"
      >x</a
      ><a name="9571"
      > </a
      ><a name="9572" href="Stlc.html#9572" class="Bound"
      >A</a
      ><a name="9573"
      > </a
      ><a name="9574" href="Stlc.html#9574" class="Bound"
      >N</a
      ><a name="9575" class="Symbol"
      >}</a
      ><a name="9576"
      > </a
      ><a name="9577" class="Symbol"
      >&#8594;</a
      ><a name="9578"
      > </a
      ><a name="9579" href="Stlc.html#9526" class="Datatype"
      >Value</a
      ><a name="9584"
      > </a
      ><a name="9585" class="Symbol"
      >(</a
      ><a name="9586" href="Stlc.html#3663" class="InductiveConstructor Operator"
      >&#955;[</a
      ><a name="9588"
      > </a
      ><a name="9589" href="Stlc.html#9570" class="Bound"
      >x</a
      ><a name="9590"
      > </a
      ><a name="9591" href="Stlc.html#3663" class="InductiveConstructor Operator"
      >&#8758;</a
      ><a name="9592"
      > </a
      ><a name="9593" href="Stlc.html#9572" class="Bound"
      >A</a
      ><a name="9594"
      > </a
      ><a name="9595" href="Stlc.html#3663" class="InductiveConstructor Operator"
      >]</a
      ><a name="9596"
      > </a
      ><a name="9597" href="Stlc.html#9574" class="Bound"
      >N</a
      ><a name="9598" class="Symbol"
      >)</a
      ><a name="9599"
      >
  </a
      ><a name="9602" href="Stlc.html#9602" class="InductiveConstructor"
      >value-true</a
      ><a name="9612"
      >  </a
      ><a name="9614" class="Symbol"
      >:</a
      ><a name="9615"
      > </a
      ><a name="9616" href="Stlc.html#9526" class="Datatype"
      >Value</a
      ><a name="9621"
      > </a
      ><a name="9622" href="Stlc.html#3726" class="InductiveConstructor"
      >true</a
      ><a name="9626"
      >
  </a
      ><a name="9629" href="Stlc.html#9629" class="InductiveConstructor"
      >value-false</a
      ><a name="9640"
      > </a
      ><a name="9641" class="Symbol"
      >:</a
      ><a name="9642"
      > </a
      ><a name="9643" href="Stlc.html#9526" class="Datatype"
      >Value</a
      ><a name="9648"
      > </a
      ><a name="9649" href="Stlc.html#3740" class="InductiveConstructor"
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

<a name="12070" href="Stlc.html#12070" class="Function Operator"
      >_[_:=_]</a
      ><a name="12077"
      > </a
      ><a name="12078" class="Symbol"
      >:</a
      ><a name="12079"
      > </a
      ><a name="12080" href="Stlc.html#3628" class="Datatype"
      >Term</a
      ><a name="12084"
      > </a
      ><a name="12085" class="Symbol"
      >&#8594;</a
      ><a name="12086"
      > </a
      ><a name="12087" href="Maps.html#2171" class="Datatype"
      >Id</a
      ><a name="12089"
      > </a
      ><a name="12090" class="Symbol"
      >&#8594;</a
      ><a name="12091"
      > </a
      ><a name="12092" href="Stlc.html#3628" class="Datatype"
      >Term</a
      ><a name="12096"
      > </a
      ><a name="12097" class="Symbol"
      >&#8594;</a
      ><a name="12098"
      > </a
      ><a name="12099" href="Stlc.html#3628" class="Datatype"
      >Term</a
      ><a name="12103"
      >
</a
      ><a name="12104" class="Symbol"
      >(</a
      ><a name="12105" href="Stlc.html#3647" class="InductiveConstructor"
      >`</a
      ><a name="12106"
      > </a
      ><a name="12107" href="Stlc.html#12107" class="Bound"
      >x&#8242;</a
      ><a name="12109" class="Symbol"
      >)</a
      ><a name="12110"
      > </a
      ><a name="12111" href="Stlc.html#12070" class="Function Operator"
      >[</a
      ><a name="12112"
      > </a
      ><a name="12113" href="Stlc.html#12113" class="Bound"
      >x</a
      ><a name="12114"
      > </a
      ><a name="12115" href="Stlc.html#12070" class="Function Operator"
      >:=</a
      ><a name="12117"
      > </a
      ><a name="12118" href="Stlc.html#12118" class="Bound"
      >V</a
      ><a name="12119"
      > </a
      ><a name="12120" href="Stlc.html#12070" class="Function Operator"
      >]</a
      ><a name="12121"
      > </a
      ><a name="12122" class="Keyword"
      >with</a
      ><a name="12126"
      > </a
      ><a name="12127" href="Stlc.html#12113" class="Bound"
      >x</a
      ><a name="12128"
      > </a
      ><a name="12129" href="Maps.html#2509" class="Function Operator"
      >&#8799;</a
      ><a name="12130"
      > </a
      ><a name="12131" href="Stlc.html#12107" class="Bound"
      >x&#8242;</a
      ><a name="12133"
      >
</a
      ><a name="12134" class="Symbol"
      >...</a
      ><a name="12137"
      > </a
      ><a name="12138" class="Symbol"
      >|</a
      ><a name="12139"
      > </a
      ><a name="12140" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#520" class="InductiveConstructor"
      >yes</a
      ><a name="12143"
      > </a
      ><a name="12144" class="Symbol"
      >_</a
      ><a name="12145"
      > </a
      ><a name="12146" class="Symbol"
      >=</a
      ><a name="12147"
      > </a
      ><a name="12148" href="Stlc.html#12118" class="Bound"
      >V</a
      ><a name="12149"
      >
</a
      ><a name="12150" class="Symbol"
      >...</a
      ><a name="12153"
      > </a
      ><a name="12154" class="Symbol"
      >|</a
      ><a name="12155"
      > </a
      ><a name="12156" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#547" class="InductiveConstructor"
      >no</a
      ><a name="12158"
      >  </a
      ><a name="12160" class="Symbol"
      >_</a
      ><a name="12161"
      > </a
      ><a name="12162" class="Symbol"
      >=</a
      ><a name="12163"
      > </a
      ><a name="12164" href="Stlc.html#3647" class="InductiveConstructor"
      >`</a
      ><a name="12165"
      > </a
      ><a name="12166" href="Stlc.html#12107" class="Bound"
      >x&#8242;</a
      ><a name="12168"
      >
</a
      ><a name="12169" class="Symbol"
      >(</a
      ><a name="12170" href="Stlc.html#3663" class="InductiveConstructor Operator"
      >&#955;[</a
      ><a name="12172"
      > </a
      ><a name="12173" href="Stlc.html#12173" class="Bound"
      >x&#8242;</a
      ><a name="12175"
      > </a
      ><a name="12176" href="Stlc.html#3663" class="InductiveConstructor Operator"
      >&#8758;</a
      ><a name="12177"
      > </a
      ><a name="12178" href="Stlc.html#12178" class="Bound"
      >A&#8242;</a
      ><a name="12180"
      > </a
      ><a name="12181" href="Stlc.html#3663" class="InductiveConstructor Operator"
      >]</a
      ><a name="12182"
      > </a
      ><a name="12183" href="Stlc.html#12183" class="Bound"
      >N&#8242;</a
      ><a name="12185" class="Symbol"
      >)</a
      ><a name="12186"
      > </a
      ><a name="12187" href="Stlc.html#12070" class="Function Operator"
      >[</a
      ><a name="12188"
      > </a
      ><a name="12189" href="Stlc.html#12189" class="Bound"
      >x</a
      ><a name="12190"
      > </a
      ><a name="12191" href="Stlc.html#12070" class="Function Operator"
      >:=</a
      ><a name="12193"
      > </a
      ><a name="12194" href="Stlc.html#12194" class="Bound"
      >V</a
      ><a name="12195"
      > </a
      ><a name="12196" href="Stlc.html#12070" class="Function Operator"
      >]</a
      ><a name="12197"
      > </a
      ><a name="12198" class="Keyword"
      >with</a
      ><a name="12202"
      > </a
      ><a name="12203" href="Stlc.html#12189" class="Bound"
      >x</a
      ><a name="12204"
      > </a
      ><a name="12205" href="Maps.html#2509" class="Function Operator"
      >&#8799;</a
      ><a name="12206"
      > </a
      ><a name="12207" href="Stlc.html#12173" class="Bound"
      >x&#8242;</a
      ><a name="12209"
      >
</a
      ><a name="12210" class="Symbol"
      >...</a
      ><a name="12213"
      > </a
      ><a name="12214" class="Symbol"
      >|</a
      ><a name="12215"
      > </a
      ><a name="12216" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#520" class="InductiveConstructor"
      >yes</a
      ><a name="12219"
      > </a
      ><a name="12220" class="Symbol"
      >_</a
      ><a name="12221"
      > </a
      ><a name="12222" class="Symbol"
      >=</a
      ><a name="12223"
      > </a
      ><a name="12224" href="Stlc.html#3663" class="InductiveConstructor Operator"
      >&#955;[</a
      ><a name="12226"
      > </a
      ><a name="12227" href="Stlc.html#12173" class="Bound"
      >x&#8242;</a
      ><a name="12229"
      > </a
      ><a name="12230" href="Stlc.html#3663" class="InductiveConstructor Operator"
      >&#8758;</a
      ><a name="12231"
      > </a
      ><a name="12232" href="Stlc.html#12178" class="Bound"
      >A&#8242;</a
      ><a name="12234"
      > </a
      ><a name="12235" href="Stlc.html#3663" class="InductiveConstructor Operator"
      >]</a
      ><a name="12236"
      > </a
      ><a name="12237" href="Stlc.html#12183" class="Bound"
      >N&#8242;</a
      ><a name="12239"
      >
</a
      ><a name="12240" class="Symbol"
      >...</a
      ><a name="12243"
      > </a
      ><a name="12244" class="Symbol"
      >|</a
      ><a name="12245"
      > </a
      ><a name="12246" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#547" class="InductiveConstructor"
      >no</a
      ><a name="12248"
      >  </a
      ><a name="12250" class="Symbol"
      >_</a
      ><a name="12251"
      > </a
      ><a name="12252" class="Symbol"
      >=</a
      ><a name="12253"
      > </a
      ><a name="12254" href="Stlc.html#3663" class="InductiveConstructor Operator"
      >&#955;[</a
      ><a name="12256"
      > </a
      ><a name="12257" href="Stlc.html#12173" class="Bound"
      >x&#8242;</a
      ><a name="12259"
      > </a
      ><a name="12260" href="Stlc.html#3663" class="InductiveConstructor Operator"
      >&#8758;</a
      ><a name="12261"
      > </a
      ><a name="12262" href="Stlc.html#12178" class="Bound"
      >A&#8242;</a
      ><a name="12264"
      > </a
      ><a name="12265" href="Stlc.html#3663" class="InductiveConstructor Operator"
      >]</a
      ><a name="12266"
      > </a
      ><a name="12267" class="Symbol"
      >(</a
      ><a name="12268" href="Stlc.html#12183" class="Bound"
      >N&#8242;</a
      ><a name="12270"
      > </a
      ><a name="12271" href="Stlc.html#12070" class="Function Operator"
      >[</a
      ><a name="12272"
      > </a
      ><a name="12273" href="Stlc.html#12189" class="Bound"
      >x</a
      ><a name="12274"
      > </a
      ><a name="12275" href="Stlc.html#12070" class="Function Operator"
      >:=</a
      ><a name="12277"
      > </a
      ><a name="12278" href="Stlc.html#12194" class="Bound"
      >V</a
      ><a name="12279"
      > </a
      ><a name="12280" href="Stlc.html#12070" class="Function Operator"
      >]</a
      ><a name="12281" class="Symbol"
      >)</a
      ><a name="12282"
      >
</a
      ><a name="12283" class="Symbol"
      >(</a
      ><a name="12284" href="Stlc.html#12284" class="Bound"
      >L&#8242;</a
      ><a name="12286"
      > </a
      ><a name="12287" href="Stlc.html#3699" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="12288"
      > </a
      ><a name="12289" href="Stlc.html#12289" class="Bound"
      >M&#8242;</a
      ><a name="12291" class="Symbol"
      >)</a
      ><a name="12292"
      > </a
      ><a name="12293" href="Stlc.html#12070" class="Function Operator"
      >[</a
      ><a name="12294"
      > </a
      ><a name="12295" href="Stlc.html#12295" class="Bound"
      >x</a
      ><a name="12296"
      > </a
      ><a name="12297" href="Stlc.html#12070" class="Function Operator"
      >:=</a
      ><a name="12299"
      > </a
      ><a name="12300" href="Stlc.html#12300" class="Bound"
      >V</a
      ><a name="12301"
      > </a
      ><a name="12302" href="Stlc.html#12070" class="Function Operator"
      >]</a
      ><a name="12303"
      > </a
      ><a name="12304" class="Symbol"
      >=</a
      ><a name="12305"
      >  </a
      ><a name="12307" class="Symbol"
      >(</a
      ><a name="12308" href="Stlc.html#12284" class="Bound"
      >L&#8242;</a
      ><a name="12310"
      > </a
      ><a name="12311" href="Stlc.html#12070" class="Function Operator"
      >[</a
      ><a name="12312"
      > </a
      ><a name="12313" href="Stlc.html#12295" class="Bound"
      >x</a
      ><a name="12314"
      > </a
      ><a name="12315" href="Stlc.html#12070" class="Function Operator"
      >:=</a
      ><a name="12317"
      > </a
      ><a name="12318" href="Stlc.html#12300" class="Bound"
      >V</a
      ><a name="12319"
      > </a
      ><a name="12320" href="Stlc.html#12070" class="Function Operator"
      >]</a
      ><a name="12321" class="Symbol"
      >)</a
      ><a name="12322"
      > </a
      ><a name="12323" href="Stlc.html#3699" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="12324"
      > </a
      ><a name="12325" class="Symbol"
      >(</a
      ><a name="12326" href="Stlc.html#12289" class="Bound"
      >M&#8242;</a
      ><a name="12328"
      > </a
      ><a name="12329" href="Stlc.html#12070" class="Function Operator"
      >[</a
      ><a name="12330"
      > </a
      ><a name="12331" href="Stlc.html#12295" class="Bound"
      >x</a
      ><a name="12332"
      > </a
      ><a name="12333" href="Stlc.html#12070" class="Function Operator"
      >:=</a
      ><a name="12335"
      > </a
      ><a name="12336" href="Stlc.html#12300" class="Bound"
      >V</a
      ><a name="12337"
      > </a
      ><a name="12338" href="Stlc.html#12070" class="Function Operator"
      >]</a
      ><a name="12339" class="Symbol"
      >)</a
      ><a name="12340"
      >
</a
      ><a name="12341" class="Symbol"
      >(</a
      ><a name="12342" href="Stlc.html#3726" class="InductiveConstructor"
      >true</a
      ><a name="12346" class="Symbol"
      >)</a
      ><a name="12347"
      > </a
      ><a name="12348" href="Stlc.html#12070" class="Function Operator"
      >[</a
      ><a name="12349"
      > </a
      ><a name="12350" href="Stlc.html#12350" class="Bound"
      >x</a
      ><a name="12351"
      > </a
      ><a name="12352" href="Stlc.html#12070" class="Function Operator"
      >:=</a
      ><a name="12354"
      > </a
      ><a name="12355" href="Stlc.html#12355" class="Bound"
      >V</a
      ><a name="12356"
      > </a
      ><a name="12357" href="Stlc.html#12070" class="Function Operator"
      >]</a
      ><a name="12358"
      > </a
      ><a name="12359" class="Symbol"
      >=</a
      ><a name="12360"
      > </a
      ><a name="12361" href="Stlc.html#3726" class="InductiveConstructor"
      >true</a
      ><a name="12365"
      >
</a
      ><a name="12366" class="Symbol"
      >(</a
      ><a name="12367" href="Stlc.html#3740" class="InductiveConstructor"
      >false</a
      ><a name="12372" class="Symbol"
      >)</a
      ><a name="12373"
      > </a
      ><a name="12374" href="Stlc.html#12070" class="Function Operator"
      >[</a
      ><a name="12375"
      > </a
      ><a name="12376" href="Stlc.html#12376" class="Bound"
      >x</a
      ><a name="12377"
      > </a
      ><a name="12378" href="Stlc.html#12070" class="Function Operator"
      >:=</a
      ><a name="12380"
      > </a
      ><a name="12381" href="Stlc.html#12381" class="Bound"
      >V</a
      ><a name="12382"
      > </a
      ><a name="12383" href="Stlc.html#12070" class="Function Operator"
      >]</a
      ><a name="12384"
      > </a
      ><a name="12385" class="Symbol"
      >=</a
      ><a name="12386"
      > </a
      ><a name="12387" href="Stlc.html#3740" class="InductiveConstructor"
      >false</a
      ><a name="12392"
      >
</a
      ><a name="12393" class="Symbol"
      >(</a
      ><a name="12394" href="Stlc.html#3755" class="InductiveConstructor Operator"
      >if</a
      ><a name="12396"
      > </a
      ><a name="12397" href="Stlc.html#12397" class="Bound"
      >L&#8242;</a
      ><a name="12399"
      > </a
      ><a name="12400" href="Stlc.html#3755" class="InductiveConstructor Operator"
      >then</a
      ><a name="12404"
      > </a
      ><a name="12405" href="Stlc.html#12405" class="Bound"
      >M&#8242;</a
      ><a name="12407"
      > </a
      ><a name="12408" href="Stlc.html#3755" class="InductiveConstructor Operator"
      >else</a
      ><a name="12412"
      > </a
      ><a name="12413" href="Stlc.html#12413" class="Bound"
      >N&#8242;</a
      ><a name="12415" class="Symbol"
      >)</a
      ><a name="12416"
      > </a
      ><a name="12417" href="Stlc.html#12070" class="Function Operator"
      >[</a
      ><a name="12418"
      > </a
      ><a name="12419" href="Stlc.html#12419" class="Bound"
      >x</a
      ><a name="12420"
      > </a
      ><a name="12421" href="Stlc.html#12070" class="Function Operator"
      >:=</a
      ><a name="12423"
      > </a
      ><a name="12424" href="Stlc.html#12424" class="Bound"
      >V</a
      ><a name="12425"
      > </a
      ><a name="12426" href="Stlc.html#12070" class="Function Operator"
      >]</a
      ><a name="12427"
      > </a
      ><a name="12428" class="Symbol"
      >=</a
      ><a name="12429"
      >
  </a
      ><a name="12432" href="Stlc.html#3755" class="InductiveConstructor Operator"
      >if</a
      ><a name="12434"
      > </a
      ><a name="12435" class="Symbol"
      >(</a
      ><a name="12436" href="Stlc.html#12397" class="Bound"
      >L&#8242;</a
      ><a name="12438"
      > </a
      ><a name="12439" href="Stlc.html#12070" class="Function Operator"
      >[</a
      ><a name="12440"
      > </a
      ><a name="12441" href="Stlc.html#12419" class="Bound"
      >x</a
      ><a name="12442"
      > </a
      ><a name="12443" href="Stlc.html#12070" class="Function Operator"
      >:=</a
      ><a name="12445"
      > </a
      ><a name="12446" href="Stlc.html#12424" class="Bound"
      >V</a
      ><a name="12447"
      > </a
      ><a name="12448" href="Stlc.html#12070" class="Function Operator"
      >]</a
      ><a name="12449" class="Symbol"
      >)</a
      ><a name="12450"
      > </a
      ><a name="12451" href="Stlc.html#3755" class="InductiveConstructor Operator"
      >then</a
      ><a name="12455"
      > </a
      ><a name="12456" class="Symbol"
      >(</a
      ><a name="12457" href="Stlc.html#12405" class="Bound"
      >M&#8242;</a
      ><a name="12459"
      > </a
      ><a name="12460" href="Stlc.html#12070" class="Function Operator"
      >[</a
      ><a name="12461"
      > </a
      ><a name="12462" href="Stlc.html#12419" class="Bound"
      >x</a
      ><a name="12463"
      > </a
      ><a name="12464" href="Stlc.html#12070" class="Function Operator"
      >:=</a
      ><a name="12466"
      > </a
      ><a name="12467" href="Stlc.html#12424" class="Bound"
      >V</a
      ><a name="12468"
      > </a
      ><a name="12469" href="Stlc.html#12070" class="Function Operator"
      >]</a
      ><a name="12470" class="Symbol"
      >)</a
      ><a name="12471"
      > </a
      ><a name="12472" href="Stlc.html#3755" class="InductiveConstructor Operator"
      >else</a
      ><a name="12476"
      > </a
      ><a name="12477" class="Symbol"
      >(</a
      ><a name="12478" href="Stlc.html#12413" class="Bound"
      >N&#8242;</a
      ><a name="12480"
      > </a
      ><a name="12481" href="Stlc.html#12070" class="Function Operator"
      >[</a
      ><a name="12482"
      > </a
      ><a name="12483" href="Stlc.html#12419" class="Bound"
      >x</a
      ><a name="12484"
      > </a
      ><a name="12485" href="Stlc.html#12070" class="Function Operator"
      >:=</a
      ><a name="12487"
      > </a
      ><a name="12488" href="Stlc.html#12424" class="Bound"
      >V</a
      ><a name="12489"
      > </a
      ><a name="12490" href="Stlc.html#12070" class="Function Operator"
      >]</a
      ><a name="12491" class="Symbol"
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

<a name="13241" href="Stlc.html#13241" class="Function"
      >ex&#8321;&#8321;</a
      ><a name="13245"
      > </a
      ><a name="13246" class="Symbol"
      >:</a
      ><a name="13247"
      > </a
      ><a name="13248" href="Stlc.html#3647" class="InductiveConstructor"
      >`</a
      ><a name="13249"
      > </a
      ><a name="13250" href="Stlc.html#5669" class="Function"
      >f</a
      ><a name="13251"
      > </a
      ><a name="13252" href="Stlc.html#12070" class="Function Operator"
      >[</a
      ><a name="13253"
      > </a
      ><a name="13254" href="Stlc.html#5669" class="Function"
      >f</a
      ><a name="13255"
      > </a
      ><a name="13256" href="Stlc.html#12070" class="Function Operator"
      >:=</a
      ><a name="13258"
      > </a
      ><a name="13259" href="Stlc.html#5714" class="Function"
      >not</a
      ><a name="13262"
      > </a
      ><a name="13263" href="Stlc.html#12070" class="Function Operator"
      >]</a
      ><a name="13264"
      > </a
      ><a name="13265" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="13266"
      >  </a
      ><a name="13268" href="Stlc.html#5714" class="Function"
      >not</a
      ><a name="13271"
      >
</a
      ><a name="13272" href="Stlc.html#13241" class="Function"
      >ex&#8321;&#8321;</a
      ><a name="13276"
      > </a
      ><a name="13277" class="Symbol"
      >=</a
      ><a name="13278"
      > </a
      ><a name="13279" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="13283"
      >

</a
      ><a name="13285" href="Stlc.html#13285" class="Function"
      >ex&#8321;&#8322;</a
      ><a name="13289"
      > </a
      ><a name="13290" class="Symbol"
      >:</a
      ><a name="13291"
      > </a
      ><a name="13292" href="Stlc.html#3726" class="InductiveConstructor"
      >true</a
      ><a name="13296"
      > </a
      ><a name="13297" href="Stlc.html#12070" class="Function Operator"
      >[</a
      ><a name="13298"
      > </a
      ><a name="13299" href="Stlc.html#5669" class="Function"
      >f</a
      ><a name="13300"
      > </a
      ><a name="13301" href="Stlc.html#12070" class="Function Operator"
      >:=</a
      ><a name="13303"
      > </a
      ><a name="13304" href="Stlc.html#5714" class="Function"
      >not</a
      ><a name="13307"
      > </a
      ><a name="13308" href="Stlc.html#12070" class="Function Operator"
      >]</a
      ><a name="13309"
      > </a
      ><a name="13310" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="13311"
      > </a
      ><a name="13312" href="Stlc.html#3726" class="InductiveConstructor"
      >true</a
      ><a name="13316"
      >
</a
      ><a name="13317" href="Stlc.html#13285" class="Function"
      >ex&#8321;&#8322;</a
      ><a name="13321"
      > </a
      ><a name="13322" class="Symbol"
      >=</a
      ><a name="13323"
      > </a
      ><a name="13324" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="13328"
      >

</a
      ><a name="13330" href="Stlc.html#13330" class="Function"
      >ex&#8321;&#8323;</a
      ><a name="13334"
      > </a
      ><a name="13335" class="Symbol"
      >:</a
      ><a name="13336"
      > </a
      ><a name="13337" class="Symbol"
      >(</a
      ><a name="13338" href="Stlc.html#3647" class="InductiveConstructor"
      >`</a
      ><a name="13339"
      > </a
      ><a name="13340" href="Stlc.html#5669" class="Function"
      >f</a
      ><a name="13341"
      > </a
      ><a name="13342" href="Stlc.html#3699" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="13343"
      > </a
      ><a name="13344" href="Stlc.html#3726" class="InductiveConstructor"
      >true</a
      ><a name="13348" class="Symbol"
      >)</a
      ><a name="13349"
      > </a
      ><a name="13350" href="Stlc.html#12070" class="Function Operator"
      >[</a
      ><a name="13351"
      > </a
      ><a name="13352" href="Stlc.html#5669" class="Function"
      >f</a
      ><a name="13353"
      > </a
      ><a name="13354" href="Stlc.html#12070" class="Function Operator"
      >:=</a
      ><a name="13356"
      > </a
      ><a name="13357" href="Stlc.html#5714" class="Function"
      >not</a
      ><a name="13360"
      > </a
      ><a name="13361" href="Stlc.html#12070" class="Function Operator"
      >]</a
      ><a name="13362"
      > </a
      ><a name="13363" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="13364"
      > </a
      ><a name="13365" href="Stlc.html#5714" class="Function"
      >not</a
      ><a name="13368"
      > </a
      ><a name="13369" href="Stlc.html#3699" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="13370"
      > </a
      ><a name="13371" href="Stlc.html#3726" class="InductiveConstructor"
      >true</a
      ><a name="13375"
      >
</a
      ><a name="13376" href="Stlc.html#13330" class="Function"
      >ex&#8321;&#8323;</a
      ><a name="13380"
      > </a
      ><a name="13381" class="Symbol"
      >=</a
      ><a name="13382"
      > </a
      ><a name="13383" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="13387"
      >

</a
      ><a name="13389" href="Stlc.html#13389" class="Function"
      >ex&#8321;&#8324;</a
      ><a name="13393"
      > </a
      ><a name="13394" class="Symbol"
      >:</a
      ><a name="13395"
      > </a
      ><a name="13396" class="Symbol"
      >(</a
      ><a name="13397" href="Stlc.html#3647" class="InductiveConstructor"
      >`</a
      ><a name="13398"
      > </a
      ><a name="13399" href="Stlc.html#5669" class="Function"
      >f</a
      ><a name="13400"
      > </a
      ><a name="13401" href="Stlc.html#3699" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="13402"
      > </a
      ><a name="13403" class="Symbol"
      >(</a
      ><a name="13404" href="Stlc.html#3647" class="InductiveConstructor"
      >`</a
      ><a name="13405"
      > </a
      ><a name="13406" href="Stlc.html#5669" class="Function"
      >f</a
      ><a name="13407"
      > </a
      ><a name="13408" href="Stlc.html#3699" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="13409"
      > </a
      ><a name="13410" href="Stlc.html#3726" class="InductiveConstructor"
      >true</a
      ><a name="13414" class="Symbol"
      >))</a
      ><a name="13416"
      > </a
      ><a name="13417" href="Stlc.html#12070" class="Function Operator"
      >[</a
      ><a name="13418"
      > </a
      ><a name="13419" href="Stlc.html#5669" class="Function"
      >f</a
      ><a name="13420"
      > </a
      ><a name="13421" href="Stlc.html#12070" class="Function Operator"
      >:=</a
      ><a name="13423"
      > </a
      ><a name="13424" href="Stlc.html#5714" class="Function"
      >not</a
      ><a name="13427"
      > </a
      ><a name="13428" href="Stlc.html#12070" class="Function Operator"
      >]</a
      ><a name="13429"
      > </a
      ><a name="13430" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="13431"
      > </a
      ><a name="13432" href="Stlc.html#5714" class="Function"
      >not</a
      ><a name="13435"
      > </a
      ><a name="13436" href="Stlc.html#3699" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="13437"
      > </a
      ><a name="13438" class="Symbol"
      >(</a
      ><a name="13439" href="Stlc.html#5714" class="Function"
      >not</a
      ><a name="13442"
      > </a
      ><a name="13443" href="Stlc.html#3699" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="13444"
      > </a
      ><a name="13445" href="Stlc.html#3726" class="InductiveConstructor"
      >true</a
      ><a name="13449" class="Symbol"
      >)</a
      ><a name="13450"
      >
</a
      ><a name="13451" href="Stlc.html#13389" class="Function"
      >ex&#8321;&#8324;</a
      ><a name="13455"
      > </a
      ><a name="13456" class="Symbol"
      >=</a
      ><a name="13457"
      > </a
      ><a name="13458" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="13462"
      >

</a
      ><a name="13464" href="Stlc.html#13464" class="Function"
      >ex&#8321;&#8325;</a
      ><a name="13468"
      > </a
      ><a name="13469" class="Symbol"
      >:</a
      ><a name="13470"
      > </a
      ><a name="13471" class="Symbol"
      >(</a
      ><a name="13472" href="Stlc.html#3663" class="InductiveConstructor Operator"
      >&#955;[</a
      ><a name="13474"
      > </a
      ><a name="13475" href="Stlc.html#5671" class="Function"
      >x</a
      ><a name="13476"
      > </a
      ><a name="13477" href="Stlc.html#3663" class="InductiveConstructor Operator"
      >&#8758;</a
      ><a name="13478"
      > </a
      ><a name="13479" href="Stlc.html#2601" class="InductiveConstructor"
      >&#120121;</a
      ><a name="13480"
      > </a
      ><a name="13481" href="Stlc.html#3663" class="InductiveConstructor Operator"
      >]</a
      ><a name="13482"
      > </a
      ><a name="13483" href="Stlc.html#3647" class="InductiveConstructor"
      >`</a
      ><a name="13484"
      > </a
      ><a name="13485" href="Stlc.html#5669" class="Function"
      >f</a
      ><a name="13486"
      > </a
      ><a name="13487" href="Stlc.html#3699" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="13488"
      > </a
      ><a name="13489" class="Symbol"
      >(</a
      ><a name="13490" href="Stlc.html#3647" class="InductiveConstructor"
      >`</a
      ><a name="13491"
      > </a
      ><a name="13492" href="Stlc.html#5669" class="Function"
      >f</a
      ><a name="13493"
      > </a
      ><a name="13494" href="Stlc.html#3699" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="13495"
      > </a
      ><a name="13496" href="Stlc.html#3647" class="InductiveConstructor"
      >`</a
      ><a name="13497"
      > </a
      ><a name="13498" href="Stlc.html#5671" class="Function"
      >x</a
      ><a name="13499" class="Symbol"
      >))</a
      ><a name="13501"
      > </a
      ><a name="13502" href="Stlc.html#12070" class="Function Operator"
      >[</a
      ><a name="13503"
      > </a
      ><a name="13504" href="Stlc.html#5669" class="Function"
      >f</a
      ><a name="13505"
      > </a
      ><a name="13506" href="Stlc.html#12070" class="Function Operator"
      >:=</a
      ><a name="13508"
      > </a
      ><a name="13509" href="Stlc.html#5714" class="Function"
      >not</a
      ><a name="13512"
      > </a
      ><a name="13513" href="Stlc.html#12070" class="Function Operator"
      >]</a
      ><a name="13514"
      > </a
      ><a name="13515" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="13516"
      > </a
      ><a name="13517" href="Stlc.html#3663" class="InductiveConstructor Operator"
      >&#955;[</a
      ><a name="13519"
      > </a
      ><a name="13520" href="Stlc.html#5671" class="Function"
      >x</a
      ><a name="13521"
      > </a
      ><a name="13522" href="Stlc.html#3663" class="InductiveConstructor Operator"
      >&#8758;</a
      ><a name="13523"
      > </a
      ><a name="13524" href="Stlc.html#2601" class="InductiveConstructor"
      >&#120121;</a
      ><a name="13525"
      > </a
      ><a name="13526" href="Stlc.html#3663" class="InductiveConstructor Operator"
      >]</a
      ><a name="13527"
      > </a
      ><a name="13528" href="Stlc.html#5714" class="Function"
      >not</a
      ><a name="13531"
      > </a
      ><a name="13532" href="Stlc.html#3699" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="13533"
      > </a
      ><a name="13534" class="Symbol"
      >(</a
      ><a name="13535" href="Stlc.html#5714" class="Function"
      >not</a
      ><a name="13538"
      > </a
      ><a name="13539" href="Stlc.html#3699" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="13540"
      > </a
      ><a name="13541" href="Stlc.html#3647" class="InductiveConstructor"
      >`</a
      ><a name="13542"
      > </a
      ><a name="13543" href="Stlc.html#5671" class="Function"
      >x</a
      ><a name="13544" class="Symbol"
      >)</a
      ><a name="13545"
      >
</a
      ><a name="13546" href="Stlc.html#13464" class="Function"
      >ex&#8321;&#8325;</a
      ><a name="13550"
      > </a
      ><a name="13551" class="Symbol"
      >=</a
      ><a name="13552"
      > </a
      ><a name="13553" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="13557"
      >

</a
      ><a name="13559" href="Stlc.html#13559" class="Function"
      >ex&#8321;&#8326;</a
      ><a name="13563"
      > </a
      ><a name="13564" class="Symbol"
      >:</a
      ><a name="13565"
      > </a
      ><a name="13566" class="Symbol"
      >(</a
      ><a name="13567" href="Stlc.html#3663" class="InductiveConstructor Operator"
      >&#955;[</a
      ><a name="13569"
      > </a
      ><a name="13570" href="Stlc.html#5673" class="Function"
      >y</a
      ><a name="13571"
      > </a
      ><a name="13572" href="Stlc.html#3663" class="InductiveConstructor Operator"
      >&#8758;</a
      ><a name="13573"
      > </a
      ><a name="13574" href="Stlc.html#2601" class="InductiveConstructor"
      >&#120121;</a
      ><a name="13575"
      > </a
      ><a name="13576" href="Stlc.html#3663" class="InductiveConstructor Operator"
      >]</a
      ><a name="13577"
      > </a
      ><a name="13578" href="Stlc.html#3647" class="InductiveConstructor"
      >`</a
      ><a name="13579"
      > </a
      ><a name="13580" href="Stlc.html#5673" class="Function"
      >y</a
      ><a name="13581" class="Symbol"
      >)</a
      ><a name="13582"
      > </a
      ><a name="13583" href="Stlc.html#12070" class="Function Operator"
      >[</a
      ><a name="13584"
      > </a
      ><a name="13585" href="Stlc.html#5671" class="Function"
      >x</a
      ><a name="13586"
      > </a
      ><a name="13587" href="Stlc.html#12070" class="Function Operator"
      >:=</a
      ><a name="13589"
      > </a
      ><a name="13590" href="Stlc.html#3726" class="InductiveConstructor"
      >true</a
      ><a name="13594"
      > </a
      ><a name="13595" href="Stlc.html#12070" class="Function Operator"
      >]</a
      ><a name="13596"
      > </a
      ><a name="13597" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="13598"
      > </a
      ><a name="13599" href="Stlc.html#3663" class="InductiveConstructor Operator"
      >&#955;[</a
      ><a name="13601"
      > </a
      ><a name="13602" href="Stlc.html#5673" class="Function"
      >y</a
      ><a name="13603"
      > </a
      ><a name="13604" href="Stlc.html#3663" class="InductiveConstructor Operator"
      >&#8758;</a
      ><a name="13605"
      > </a
      ><a name="13606" href="Stlc.html#2601" class="InductiveConstructor"
      >&#120121;</a
      ><a name="13607"
      > </a
      ><a name="13608" href="Stlc.html#3663" class="InductiveConstructor Operator"
      >]</a
      ><a name="13609"
      > </a
      ><a name="13610" href="Stlc.html#3647" class="InductiveConstructor"
      >`</a
      ><a name="13611"
      > </a
      ><a name="13612" href="Stlc.html#5673" class="Function"
      >y</a
      ><a name="13613"
      >
</a
      ><a name="13614" href="Stlc.html#13559" class="Function"
      >ex&#8321;&#8326;</a
      ><a name="13618"
      > </a
      ><a name="13619" class="Symbol"
      >=</a
      ><a name="13620"
      > </a
      ><a name="13621" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="13625"
      >

</a
      ><a name="13627" href="Stlc.html#13627" class="Function"
      >ex&#8321;&#8327;</a
      ><a name="13631"
      > </a
      ><a name="13632" class="Symbol"
      >:</a
      ><a name="13633"
      > </a
      ><a name="13634" class="Symbol"
      >(</a
      ><a name="13635" href="Stlc.html#3663" class="InductiveConstructor Operator"
      >&#955;[</a
      ><a name="13637"
      > </a
      ><a name="13638" href="Stlc.html#5671" class="Function"
      >x</a
      ><a name="13639"
      > </a
      ><a name="13640" href="Stlc.html#3663" class="InductiveConstructor Operator"
      >&#8758;</a
      ><a name="13641"
      > </a
      ><a name="13642" href="Stlc.html#2601" class="InductiveConstructor"
      >&#120121;</a
      ><a name="13643"
      > </a
      ><a name="13644" href="Stlc.html#3663" class="InductiveConstructor Operator"
      >]</a
      ><a name="13645"
      > </a
      ><a name="13646" href="Stlc.html#3647" class="InductiveConstructor"
      >`</a
      ><a name="13647"
      > </a
      ><a name="13648" href="Stlc.html#5671" class="Function"
      >x</a
      ><a name="13649" class="Symbol"
      >)</a
      ><a name="13650"
      > </a
      ><a name="13651" href="Stlc.html#12070" class="Function Operator"
      >[</a
      ><a name="13652"
      > </a
      ><a name="13653" href="Stlc.html#5671" class="Function"
      >x</a
      ><a name="13654"
      > </a
      ><a name="13655" href="Stlc.html#12070" class="Function Operator"
      >:=</a
      ><a name="13657"
      > </a
      ><a name="13658" href="Stlc.html#3726" class="InductiveConstructor"
      >true</a
      ><a name="13662"
      > </a
      ><a name="13663" href="Stlc.html#12070" class="Function Operator"
      >]</a
      ><a name="13664"
      > </a
      ><a name="13665" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="13666"
      > </a
      ><a name="13667" href="Stlc.html#3663" class="InductiveConstructor Operator"
      >&#955;[</a
      ><a name="13669"
      > </a
      ><a name="13670" href="Stlc.html#5671" class="Function"
      >x</a
      ><a name="13671"
      > </a
      ><a name="13672" href="Stlc.html#3663" class="InductiveConstructor Operator"
      >&#8758;</a
      ><a name="13673"
      > </a
      ><a name="13674" href="Stlc.html#2601" class="InductiveConstructor"
      >&#120121;</a
      ><a name="13675"
      > </a
      ><a name="13676" href="Stlc.html#3663" class="InductiveConstructor Operator"
      >]</a
      ><a name="13677"
      > </a
      ><a name="13678" href="Stlc.html#3647" class="InductiveConstructor"
      >`</a
      ><a name="13679"
      > </a
      ><a name="13680" href="Stlc.html#5671" class="Function"
      >x</a
      ><a name="13681"
      >
</a
      ><a name="13682" href="Stlc.html#13627" class="Function"
      >ex&#8321;&#8327;</a
      ><a name="13686"
      > </a
      ><a name="13687" class="Symbol"
      >=</a
      ><a name="13688"
      > </a
      ><a name="13689" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
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

<a name="15803" class="Keyword"
      >infix</a
      ><a name="15808"
      > </a
      ><a name="15809" class="Number"
      >10</a
      ><a name="15811"
      > </a
      ><a name="15812" href="Stlc.html#15823" class="Datatype Operator"
      >_&#10233;_</a
      ><a name="15815"
      > 

</a
      ><a name="15818" class="Keyword"
      >data</a
      ><a name="15822"
      > </a
      ><a name="15823" href="Stlc.html#15823" class="Datatype Operator"
      >_&#10233;_</a
      ><a name="15826"
      > </a
      ><a name="15827" class="Symbol"
      >:</a
      ><a name="15828"
      > </a
      ><a name="15829" href="Stlc.html#3628" class="Datatype"
      >Term</a
      ><a name="15833"
      > </a
      ><a name="15834" class="Symbol"
      >&#8594;</a
      ><a name="15835"
      > </a
      ><a name="15836" href="Stlc.html#3628" class="Datatype"
      >Term</a
      ><a name="15840"
      > </a
      ><a name="15841" class="Symbol"
      >&#8594;</a
      ><a name="15842"
      > </a
      ><a name="15843" class="PrimitiveType"
      >Set</a
      ><a name="15846"
      > </a
      ><a name="15847" class="Keyword"
      >where</a
      ><a name="15852"
      >
  </a
      ><a name="15855" href="Stlc.html#15855" class="InductiveConstructor"
      >&#958;&#183;&#8321;</a
      ><a name="15858"
      > </a
      ><a name="15859" class="Symbol"
      >:</a
      ><a name="15860"
      > </a
      ><a name="15861" class="Symbol"
      >&#8704;</a
      ><a name="15862"
      > </a
      ><a name="15863" class="Symbol"
      >{</a
      ><a name="15864" href="Stlc.html#15864" class="Bound"
      >L</a
      ><a name="15865"
      > </a
      ><a name="15866" href="Stlc.html#15866" class="Bound"
      >L&#8242;</a
      ><a name="15868"
      > </a
      ><a name="15869" href="Stlc.html#15869" class="Bound"
      >M</a
      ><a name="15870" class="Symbol"
      >}</a
      ><a name="15871"
      > </a
      ><a name="15872" class="Symbol"
      >&#8594;</a
      ><a name="15873"
      >
    </a
      ><a name="15878" href="Stlc.html#15864" class="Bound"
      >L</a
      ><a name="15879"
      > </a
      ><a name="15880" href="Stlc.html#15823" class="Datatype Operator"
      >&#10233;</a
      ><a name="15881"
      > </a
      ><a name="15882" href="Stlc.html#15866" class="Bound"
      >L&#8242;</a
      ><a name="15884"
      > </a
      ><a name="15885" class="Symbol"
      >&#8594;</a
      ><a name="15886"
      >
    </a
      ><a name="15891" href="Stlc.html#15864" class="Bound"
      >L</a
      ><a name="15892"
      > </a
      ><a name="15893" href="Stlc.html#3699" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="15894"
      > </a
      ><a name="15895" href="Stlc.html#15869" class="Bound"
      >M</a
      ><a name="15896"
      > </a
      ><a name="15897" href="Stlc.html#15823" class="Datatype Operator"
      >&#10233;</a
      ><a name="15898"
      > </a
      ><a name="15899" href="Stlc.html#15866" class="Bound"
      >L&#8242;</a
      ><a name="15901"
      > </a
      ><a name="15902" href="Stlc.html#3699" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="15903"
      > </a
      ><a name="15904" href="Stlc.html#15869" class="Bound"
      >M</a
      ><a name="15905"
      >
  </a
      ><a name="15908" href="Stlc.html#15908" class="InductiveConstructor"
      >&#958;&#183;&#8322;</a
      ><a name="15911"
      > </a
      ><a name="15912" class="Symbol"
      >:</a
      ><a name="15913"
      > </a
      ><a name="15914" class="Symbol"
      >&#8704;</a
      ><a name="15915"
      > </a
      ><a name="15916" class="Symbol"
      >{</a
      ><a name="15917" href="Stlc.html#15917" class="Bound"
      >V</a
      ><a name="15918"
      > </a
      ><a name="15919" href="Stlc.html#15919" class="Bound"
      >M</a
      ><a name="15920"
      > </a
      ><a name="15921" href="Stlc.html#15921" class="Bound"
      >M&#8242;</a
      ><a name="15923" class="Symbol"
      >}</a
      ><a name="15924"
      > </a
      ><a name="15925" class="Symbol"
      >&#8594;</a
      ><a name="15926"
      >
    </a
      ><a name="15931" href="Stlc.html#9526" class="Datatype"
      >Value</a
      ><a name="15936"
      > </a
      ><a name="15937" href="Stlc.html#15917" class="Bound"
      >V</a
      ><a name="15938"
      > </a
      ><a name="15939" class="Symbol"
      >&#8594;</a
      ><a name="15940"
      >
    </a
      ><a name="15945" href="Stlc.html#15919" class="Bound"
      >M</a
      ><a name="15946"
      > </a
      ><a name="15947" href="Stlc.html#15823" class="Datatype Operator"
      >&#10233;</a
      ><a name="15948"
      > </a
      ><a name="15949" href="Stlc.html#15921" class="Bound"
      >M&#8242;</a
      ><a name="15951"
      > </a
      ><a name="15952" class="Symbol"
      >&#8594;</a
      ><a name="15953"
      >
    </a
      ><a name="15958" href="Stlc.html#15917" class="Bound"
      >V</a
      ><a name="15959"
      > </a
      ><a name="15960" href="Stlc.html#3699" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="15961"
      > </a
      ><a name="15962" href="Stlc.html#15919" class="Bound"
      >M</a
      ><a name="15963"
      > </a
      ><a name="15964" href="Stlc.html#15823" class="Datatype Operator"
      >&#10233;</a
      ><a name="15965"
      > </a
      ><a name="15966" href="Stlc.html#15917" class="Bound"
      >V</a
      ><a name="15967"
      > </a
      ><a name="15968" href="Stlc.html#3699" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="15969"
      > </a
      ><a name="15970" href="Stlc.html#15921" class="Bound"
      >M&#8242;</a
      ><a name="15972"
      >
  </a
      ><a name="15975" href="Stlc.html#15975" class="InductiveConstructor"
      >&#946;&#955;&#183;</a
      ><a name="15978"
      > </a
      ><a name="15979" class="Symbol"
      >:</a
      ><a name="15980"
      > </a
      ><a name="15981" class="Symbol"
      >&#8704;</a
      ><a name="15982"
      > </a
      ><a name="15983" class="Symbol"
      >{</a
      ><a name="15984" href="Stlc.html#15984" class="Bound"
      >x</a
      ><a name="15985"
      > </a
      ><a name="15986" href="Stlc.html#15986" class="Bound"
      >A</a
      ><a name="15987"
      > </a
      ><a name="15988" href="Stlc.html#15988" class="Bound"
      >N</a
      ><a name="15989"
      > </a
      ><a name="15990" href="Stlc.html#15990" class="Bound"
      >V</a
      ><a name="15991" class="Symbol"
      >}</a
      ><a name="15992"
      > </a
      ><a name="15993" class="Symbol"
      >&#8594;</a
      ><a name="15994"
      > </a
      ><a name="15995" href="Stlc.html#9526" class="Datatype"
      >Value</a
      ><a name="16000"
      > </a
      ><a name="16001" href="Stlc.html#15990" class="Bound"
      >V</a
      ><a name="16002"
      > </a
      ><a name="16003" class="Symbol"
      >&#8594;</a
      ><a name="16004"
      >
    </a
      ><a name="16009" class="Symbol"
      >(</a
      ><a name="16010" href="Stlc.html#3663" class="InductiveConstructor Operator"
      >&#955;[</a
      ><a name="16012"
      > </a
      ><a name="16013" href="Stlc.html#15984" class="Bound"
      >x</a
      ><a name="16014"
      > </a
      ><a name="16015" href="Stlc.html#3663" class="InductiveConstructor Operator"
      >&#8758;</a
      ><a name="16016"
      > </a
      ><a name="16017" href="Stlc.html#15986" class="Bound"
      >A</a
      ><a name="16018"
      > </a
      ><a name="16019" href="Stlc.html#3663" class="InductiveConstructor Operator"
      >]</a
      ><a name="16020"
      > </a
      ><a name="16021" href="Stlc.html#15988" class="Bound"
      >N</a
      ><a name="16022" class="Symbol"
      >)</a
      ><a name="16023"
      > </a
      ><a name="16024" href="Stlc.html#3699" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="16025"
      > </a
      ><a name="16026" href="Stlc.html#15990" class="Bound"
      >V</a
      ><a name="16027"
      > </a
      ><a name="16028" href="Stlc.html#15823" class="Datatype Operator"
      >&#10233;</a
      ><a name="16029"
      > </a
      ><a name="16030" href="Stlc.html#15988" class="Bound"
      >N</a
      ><a name="16031"
      > </a
      ><a name="16032" href="Stlc.html#12070" class="Function Operator"
      >[</a
      ><a name="16033"
      > </a
      ><a name="16034" href="Stlc.html#15984" class="Bound"
      >x</a
      ><a name="16035"
      > </a
      ><a name="16036" href="Stlc.html#12070" class="Function Operator"
      >:=</a
      ><a name="16038"
      > </a
      ><a name="16039" href="Stlc.html#15990" class="Bound"
      >V</a
      ><a name="16040"
      > </a
      ><a name="16041" href="Stlc.html#12070" class="Function Operator"
      >]</a
      ><a name="16042"
      >
  </a
      ><a name="16045" href="Stlc.html#16045" class="InductiveConstructor"
      >&#958;if</a
      ><a name="16048"
      > </a
      ><a name="16049" class="Symbol"
      >:</a
      ><a name="16050"
      > </a
      ><a name="16051" class="Symbol"
      >&#8704;</a
      ><a name="16052"
      > </a
      ><a name="16053" class="Symbol"
      >{</a
      ><a name="16054" href="Stlc.html#16054" class="Bound"
      >L</a
      ><a name="16055"
      > </a
      ><a name="16056" href="Stlc.html#16056" class="Bound"
      >L&#8242;</a
      ><a name="16058"
      > </a
      ><a name="16059" href="Stlc.html#16059" class="Bound"
      >M</a
      ><a name="16060"
      > </a
      ><a name="16061" href="Stlc.html#16061" class="Bound"
      >N</a
      ><a name="16062" class="Symbol"
      >}</a
      ><a name="16063"
      > </a
      ><a name="16064" class="Symbol"
      >&#8594;</a
      ><a name="16065"
      >
    </a
      ><a name="16070" href="Stlc.html#16054" class="Bound"
      >L</a
      ><a name="16071"
      > </a
      ><a name="16072" href="Stlc.html#15823" class="Datatype Operator"
      >&#10233;</a
      ><a name="16073"
      > </a
      ><a name="16074" href="Stlc.html#16056" class="Bound"
      >L&#8242;</a
      ><a name="16076"
      > </a
      ><a name="16077" class="Symbol"
      >&#8594;</a
      ><a name="16078"
      >    
    </a
      ><a name="16087" href="Stlc.html#3755" class="InductiveConstructor Operator"
      >if</a
      ><a name="16089"
      > </a
      ><a name="16090" href="Stlc.html#16054" class="Bound"
      >L</a
      ><a name="16091"
      > </a
      ><a name="16092" href="Stlc.html#3755" class="InductiveConstructor Operator"
      >then</a
      ><a name="16096"
      > </a
      ><a name="16097" href="Stlc.html#16059" class="Bound"
      >M</a
      ><a name="16098"
      > </a
      ><a name="16099" href="Stlc.html#3755" class="InductiveConstructor Operator"
      >else</a
      ><a name="16103"
      > </a
      ><a name="16104" href="Stlc.html#16061" class="Bound"
      >N</a
      ><a name="16105"
      > </a
      ><a name="16106" href="Stlc.html#15823" class="Datatype Operator"
      >&#10233;</a
      ><a name="16107"
      > </a
      ><a name="16108" href="Stlc.html#3755" class="InductiveConstructor Operator"
      >if</a
      ><a name="16110"
      > </a
      ><a name="16111" href="Stlc.html#16056" class="Bound"
      >L&#8242;</a
      ><a name="16113"
      > </a
      ><a name="16114" href="Stlc.html#3755" class="InductiveConstructor Operator"
      >then</a
      ><a name="16118"
      > </a
      ><a name="16119" href="Stlc.html#16059" class="Bound"
      >M</a
      ><a name="16120"
      > </a
      ><a name="16121" href="Stlc.html#3755" class="InductiveConstructor Operator"
      >else</a
      ><a name="16125"
      > </a
      ><a name="16126" href="Stlc.html#16061" class="Bound"
      >N</a
      ><a name="16127"
      >
  </a
      ><a name="16130" href="Stlc.html#16130" class="InductiveConstructor"
      >&#946;if-true</a
      ><a name="16138"
      > </a
      ><a name="16139" class="Symbol"
      >:</a
      ><a name="16140"
      > </a
      ><a name="16141" class="Symbol"
      >&#8704;</a
      ><a name="16142"
      > </a
      ><a name="16143" class="Symbol"
      >{</a
      ><a name="16144" href="Stlc.html#16144" class="Bound"
      >M</a
      ><a name="16145"
      > </a
      ><a name="16146" href="Stlc.html#16146" class="Bound"
      >N</a
      ><a name="16147" class="Symbol"
      >}</a
      ><a name="16148"
      > </a
      ><a name="16149" class="Symbol"
      >&#8594;</a
      ><a name="16150"
      >
    </a
      ><a name="16155" href="Stlc.html#3755" class="InductiveConstructor Operator"
      >if</a
      ><a name="16157"
      > </a
      ><a name="16158" href="Stlc.html#3726" class="InductiveConstructor"
      >true</a
      ><a name="16162"
      > </a
      ><a name="16163" href="Stlc.html#3755" class="InductiveConstructor Operator"
      >then</a
      ><a name="16167"
      > </a
      ><a name="16168" href="Stlc.html#16144" class="Bound"
      >M</a
      ><a name="16169"
      > </a
      ><a name="16170" href="Stlc.html#3755" class="InductiveConstructor Operator"
      >else</a
      ><a name="16174"
      > </a
      ><a name="16175" href="Stlc.html#16146" class="Bound"
      >N</a
      ><a name="16176"
      > </a
      ><a name="16177" href="Stlc.html#15823" class="Datatype Operator"
      >&#10233;</a
      ><a name="16178"
      > </a
      ><a name="16179" href="Stlc.html#16144" class="Bound"
      >M</a
      ><a name="16180"
      >
  </a
      ><a name="16183" href="Stlc.html#16183" class="InductiveConstructor"
      >&#946;if-false</a
      ><a name="16192"
      > </a
      ><a name="16193" class="Symbol"
      >:</a
      ><a name="16194"
      > </a
      ><a name="16195" class="Symbol"
      >&#8704;</a
      ><a name="16196"
      > </a
      ><a name="16197" class="Symbol"
      >{</a
      ><a name="16198" href="Stlc.html#16198" class="Bound"
      >M</a
      ><a name="16199"
      > </a
      ><a name="16200" href="Stlc.html#16200" class="Bound"
      >N</a
      ><a name="16201" class="Symbol"
      >}</a
      ><a name="16202"
      > </a
      ><a name="16203" class="Symbol"
      >&#8594;</a
      ><a name="16204"
      >
    </a
      ><a name="16209" href="Stlc.html#3755" class="InductiveConstructor Operator"
      >if</a
      ><a name="16211"
      > </a
      ><a name="16212" href="Stlc.html#3740" class="InductiveConstructor"
      >false</a
      ><a name="16217"
      > </a
      ><a name="16218" href="Stlc.html#3755" class="InductiveConstructor Operator"
      >then</a
      ><a name="16222"
      > </a
      ><a name="16223" href="Stlc.html#16198" class="Bound"
      >M</a
      ><a name="16224"
      > </a
      ><a name="16225" href="Stlc.html#3755" class="InductiveConstructor Operator"
      >else</a
      ><a name="16229"
      > </a
      ><a name="16230" href="Stlc.html#16200" class="Bound"
      >N</a
      ><a name="16231"
      > </a
      ><a name="16232" href="Stlc.html#15823" class="Datatype Operator"
      >&#10233;</a
      ><a name="16233"
      > </a
      ><a name="16234" href="Stlc.html#16200" class="Bound"
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

<a name="17808" class="Keyword"
      >infix</a
      ><a name="17813"
      > </a
      ><a name="17814" class="Number"
      >10</a
      ><a name="17816"
      > </a
      ><a name="17817" href="Stlc.html#17857" class="Datatype Operator"
      >_&#10233;*_</a
      ><a name="17821"
      > 
</a
      ><a name="17823" class="Keyword"
      >infixr</a
      ><a name="17829"
      > </a
      ><a name="17830" class="Number"
      >2</a
      ><a name="17831"
      > </a
      ><a name="17832" href="Stlc.html#17910" class="InductiveConstructor Operator"
      >_&#10233;&#10216;_&#10217;_</a
      ><a name="17838"
      >
</a
      ><a name="17839" class="Keyword"
      >infix</a
      ><a name="17844"
      >  </a
      ><a name="17846" class="Number"
      >3</a
      ><a name="17847"
      > </a
      ><a name="17848" href="Stlc.html#17890" class="InductiveConstructor Operator"
      >_&#8718;</a
      ><a name="17850"
      >

</a
      ><a name="17852" class="Keyword"
      >data</a
      ><a name="17856"
      > </a
      ><a name="17857" href="Stlc.html#17857" class="Datatype Operator"
      >_&#10233;*_</a
      ><a name="17861"
      > </a
      ><a name="17862" class="Symbol"
      >:</a
      ><a name="17863"
      > </a
      ><a name="17864" href="Stlc.html#3628" class="Datatype"
      >Term</a
      ><a name="17868"
      > </a
      ><a name="17869" class="Symbol"
      >&#8594;</a
      ><a name="17870"
      > </a
      ><a name="17871" href="Stlc.html#3628" class="Datatype"
      >Term</a
      ><a name="17875"
      > </a
      ><a name="17876" class="Symbol"
      >&#8594;</a
      ><a name="17877"
      > </a
      ><a name="17878" class="PrimitiveType"
      >Set</a
      ><a name="17881"
      > </a
      ><a name="17882" class="Keyword"
      >where</a
      ><a name="17887"
      >
  </a
      ><a name="17890" href="Stlc.html#17890" class="InductiveConstructor Operator"
      >_&#8718;</a
      ><a name="17892"
      > </a
      ><a name="17893" class="Symbol"
      >:</a
      ><a name="17894"
      > </a
      ><a name="17895" class="Symbol"
      >&#8704;</a
      ><a name="17896"
      > </a
      ><a name="17897" href="Stlc.html#17897" class="Bound"
      >M</a
      ><a name="17898"
      > </a
      ><a name="17899" class="Symbol"
      >&#8594;</a
      ><a name="17900"
      > </a
      ><a name="17901" href="Stlc.html#17897" class="Bound"
      >M</a
      ><a name="17902"
      > </a
      ><a name="17903" href="Stlc.html#17857" class="Datatype Operator"
      >&#10233;*</a
      ><a name="17905"
      > </a
      ><a name="17906" href="Stlc.html#17897" class="Bound"
      >M</a
      ><a name="17907"
      >
  </a
      ><a name="17910" href="Stlc.html#17910" class="InductiveConstructor Operator"
      >_&#10233;&#10216;_&#10217;_</a
      ><a name="17916"
      > </a
      ><a name="17917" class="Symbol"
      >:</a
      ><a name="17918"
      > </a
      ><a name="17919" class="Symbol"
      >&#8704;</a
      ><a name="17920"
      > </a
      ><a name="17921" href="Stlc.html#17921" class="Bound"
      >L</a
      ><a name="17922"
      > </a
      ><a name="17923" class="Symbol"
      >{</a
      ><a name="17924" href="Stlc.html#17924" class="Bound"
      >M</a
      ><a name="17925"
      > </a
      ><a name="17926" href="Stlc.html#17926" class="Bound"
      >N</a
      ><a name="17927" class="Symbol"
      >}</a
      ><a name="17928"
      > </a
      ><a name="17929" class="Symbol"
      >&#8594;</a
      ><a name="17930"
      > </a
      ><a name="17931" href="Stlc.html#17921" class="Bound"
      >L</a
      ><a name="17932"
      > </a
      ><a name="17933" href="Stlc.html#15823" class="Datatype Operator"
      >&#10233;</a
      ><a name="17934"
      > </a
      ><a name="17935" href="Stlc.html#17924" class="Bound"
      >M</a
      ><a name="17936"
      > </a
      ><a name="17937" class="Symbol"
      >&#8594;</a
      ><a name="17938"
      > </a
      ><a name="17939" href="Stlc.html#17924" class="Bound"
      >M</a
      ><a name="17940"
      > </a
      ><a name="17941" href="Stlc.html#17857" class="Datatype Operator"
      >&#10233;*</a
      ><a name="17943"
      > </a
      ><a name="17944" href="Stlc.html#17926" class="Bound"
      >N</a
      ><a name="17945"
      > </a
      ><a name="17946" class="Symbol"
      >&#8594;</a
      ><a name="17947"
      > </a
      ><a name="17948" href="Stlc.html#17921" class="Bound"
      >L</a
      ><a name="17949"
      > </a
      ><a name="17950" href="Stlc.html#17857" class="Datatype Operator"
      >&#10233;*</a
      ><a name="17952"
      > </a
      ><a name="17953" href="Stlc.html#17926" class="Bound"
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

<a name="18414" href="Stlc.html#18414" class="Function"
      >reduction&#8321;</a
      ><a name="18424"
      > </a
      ><a name="18425" class="Symbol"
      >:</a
      ><a name="18426"
      > </a
      ><a name="18427" href="Stlc.html#5714" class="Function"
      >not</a
      ><a name="18430"
      > </a
      ><a name="18431" href="Stlc.html#3699" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="18432"
      > </a
      ><a name="18433" href="Stlc.html#3726" class="InductiveConstructor"
      >true</a
      ><a name="18437"
      > </a
      ><a name="18438" href="Stlc.html#17857" class="Datatype Operator"
      >&#10233;*</a
      ><a name="18440"
      > </a
      ><a name="18441" href="Stlc.html#3740" class="InductiveConstructor"
      >false</a
      ><a name="18446"
      >
</a
      ><a name="18447" href="Stlc.html#18414" class="Function"
      >reduction&#8321;</a
      ><a name="18457"
      > </a
      ><a name="18458" class="Symbol"
      >=</a
      ><a name="18459"
      >
    </a
      ><a name="18464" href="Stlc.html#5714" class="Function"
      >not</a
      ><a name="18467"
      > </a
      ><a name="18468" href="Stlc.html#3699" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="18469"
      > </a
      ><a name="18470" href="Stlc.html#3726" class="InductiveConstructor"
      >true</a
      ><a name="18474"
      >
  </a
      ><a name="18477" href="Stlc.html#17910" class="InductiveConstructor Operator"
      >&#10233;&#10216;</a
      ><a name="18479"
      > </a
      ><a name="18480" href="Stlc.html#15975" class="InductiveConstructor"
      >&#946;&#955;&#183;</a
      ><a name="18483"
      > </a
      ><a name="18484" href="Stlc.html#9602" class="InductiveConstructor"
      >value-true</a
      ><a name="18494"
      > </a
      ><a name="18495" href="Stlc.html#17910" class="InductiveConstructor Operator"
      >&#10217;</a
      ><a name="18496"
      >
    </a
      ><a name="18501" href="Stlc.html#3755" class="InductiveConstructor Operator"
      >if</a
      ><a name="18503"
      > </a
      ><a name="18504" href="Stlc.html#3726" class="InductiveConstructor"
      >true</a
      ><a name="18508"
      > </a
      ><a name="18509" href="Stlc.html#3755" class="InductiveConstructor Operator"
      >then</a
      ><a name="18513"
      > </a
      ><a name="18514" href="Stlc.html#3740" class="InductiveConstructor"
      >false</a
      ><a name="18519"
      > </a
      ><a name="18520" href="Stlc.html#3755" class="InductiveConstructor Operator"
      >else</a
      ><a name="18524"
      > </a
      ><a name="18525" href="Stlc.html#3726" class="InductiveConstructor"
      >true</a
      ><a name="18529"
      >
  </a
      ><a name="18532" href="Stlc.html#17910" class="InductiveConstructor Operator"
      >&#10233;&#10216;</a
      ><a name="18534"
      > </a
      ><a name="18535" href="Stlc.html#16130" class="InductiveConstructor"
      >&#946;if-true</a
      ><a name="18543"
      > </a
      ><a name="18544" href="Stlc.html#17910" class="InductiveConstructor Operator"
      >&#10217;</a
      ><a name="18545"
      >
    </a
      ><a name="18550" href="Stlc.html#3740" class="InductiveConstructor"
      >false</a
      ><a name="18555"
      >
  </a
      ><a name="18558" href="Stlc.html#17890" class="InductiveConstructor Operator"
      >&#8718;</a
      ><a name="18559"
      >

</a
      ><a name="18561" href="Stlc.html#18561" class="Function"
      >reduction&#8322;</a
      ><a name="18571"
      > </a
      ><a name="18572" class="Symbol"
      >:</a
      ><a name="18573"
      > </a
      ><a name="18574" href="Stlc.html#5718" class="Function"
      >two</a
      ><a name="18577"
      > </a
      ><a name="18578" href="Stlc.html#3699" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="18579"
      > </a
      ><a name="18580" href="Stlc.html#5714" class="Function"
      >not</a
      ><a name="18583"
      > </a
      ><a name="18584" href="Stlc.html#3699" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="18585"
      > </a
      ><a name="18586" href="Stlc.html#3726" class="InductiveConstructor"
      >true</a
      ><a name="18590"
      > </a
      ><a name="18591" href="Stlc.html#17857" class="Datatype Operator"
      >&#10233;*</a
      ><a name="18593"
      > </a
      ><a name="18594" href="Stlc.html#3726" class="InductiveConstructor"
      >true</a
      ><a name="18598"
      >
</a
      ><a name="18599" href="Stlc.html#18561" class="Function"
      >reduction&#8322;</a
      ><a name="18609"
      > </a
      ><a name="18610" class="Symbol"
      >=</a
      ><a name="18611"
      >
    </a
      ><a name="18616" href="Stlc.html#5718" class="Function"
      >two</a
      ><a name="18619"
      > </a
      ><a name="18620" href="Stlc.html#3699" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="18621"
      > </a
      ><a name="18622" href="Stlc.html#5714" class="Function"
      >not</a
      ><a name="18625"
      > </a
      ><a name="18626" href="Stlc.html#3699" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="18627"
      > </a
      ><a name="18628" href="Stlc.html#3726" class="InductiveConstructor"
      >true</a
      ><a name="18632"
      >
  </a
      ><a name="18635" href="Stlc.html#17910" class="InductiveConstructor Operator"
      >&#10233;&#10216;</a
      ><a name="18637"
      > </a
      ><a name="18638" href="Stlc.html#15855" class="InductiveConstructor"
      >&#958;&#183;&#8321;</a
      ><a name="18641"
      > </a
      ><a name="18642" class="Symbol"
      >(</a
      ><a name="18643" href="Stlc.html#15975" class="InductiveConstructor"
      >&#946;&#955;&#183;</a
      ><a name="18646"
      > </a
      ><a name="18647" href="Stlc.html#9553" class="InductiveConstructor"
      >value-&#955;</a
      ><a name="18654" class="Symbol"
      >)</a
      ><a name="18655"
      > </a
      ><a name="18656" href="Stlc.html#17910" class="InductiveConstructor Operator"
      >&#10217;</a
      ><a name="18657"
      >
    </a
      ><a name="18662" class="Symbol"
      >(</a
      ><a name="18663" href="Stlc.html#3663" class="InductiveConstructor Operator"
      >&#955;[</a
      ><a name="18665"
      > </a
      ><a name="18666" href="Stlc.html#5671" class="Function"
      >x</a
      ><a name="18667"
      > </a
      ><a name="18668" href="Stlc.html#3663" class="InductiveConstructor Operator"
      >&#8758;</a
      ><a name="18669"
      > </a
      ><a name="18670" href="Stlc.html#2601" class="InductiveConstructor"
      >&#120121;</a
      ><a name="18671"
      > </a
      ><a name="18672" href="Stlc.html#3663" class="InductiveConstructor Operator"
      >]</a
      ><a name="18673"
      > </a
      ><a name="18674" href="Stlc.html#5714" class="Function"
      >not</a
      ><a name="18677"
      > </a
      ><a name="18678" href="Stlc.html#3699" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="18679"
      > </a
      ><a name="18680" class="Symbol"
      >(</a
      ><a name="18681" href="Stlc.html#5714" class="Function"
      >not</a
      ><a name="18684"
      > </a
      ><a name="18685" href="Stlc.html#3699" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="18686"
      > </a
      ><a name="18687" href="Stlc.html#3647" class="InductiveConstructor"
      >`</a
      ><a name="18688"
      > </a
      ><a name="18689" href="Stlc.html#5671" class="Function"
      >x</a
      ><a name="18690" class="Symbol"
      >))</a
      ><a name="18692"
      > </a
      ><a name="18693" href="Stlc.html#3699" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="18694"
      > </a
      ><a name="18695" href="Stlc.html#3726" class="InductiveConstructor"
      >true</a
      ><a name="18699"
      >
  </a
      ><a name="18702" href="Stlc.html#17910" class="InductiveConstructor Operator"
      >&#10233;&#10216;</a
      ><a name="18704"
      > </a
      ><a name="18705" href="Stlc.html#15975" class="InductiveConstructor"
      >&#946;&#955;&#183;</a
      ><a name="18708"
      > </a
      ><a name="18709" href="Stlc.html#9602" class="InductiveConstructor"
      >value-true</a
      ><a name="18719"
      > </a
      ><a name="18720" href="Stlc.html#17910" class="InductiveConstructor Operator"
      >&#10217;</a
      ><a name="18721"
      >
    </a
      ><a name="18726" href="Stlc.html#5714" class="Function"
      >not</a
      ><a name="18729"
      > </a
      ><a name="18730" href="Stlc.html#3699" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="18731"
      > </a
      ><a name="18732" class="Symbol"
      >(</a
      ><a name="18733" href="Stlc.html#5714" class="Function"
      >not</a
      ><a name="18736"
      > </a
      ><a name="18737" href="Stlc.html#3699" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="18738"
      > </a
      ><a name="18739" href="Stlc.html#3726" class="InductiveConstructor"
      >true</a
      ><a name="18743" class="Symbol"
      >)</a
      ><a name="18744"
      >
  </a
      ><a name="18747" href="Stlc.html#17910" class="InductiveConstructor Operator"
      >&#10233;&#10216;</a
      ><a name="18749"
      > </a
      ><a name="18750" href="Stlc.html#15908" class="InductiveConstructor"
      >&#958;&#183;&#8322;</a
      ><a name="18753"
      > </a
      ><a name="18754" href="Stlc.html#9553" class="InductiveConstructor"
      >value-&#955;</a
      ><a name="18761"
      > </a
      ><a name="18762" class="Symbol"
      >(</a
      ><a name="18763" href="Stlc.html#15975" class="InductiveConstructor"
      >&#946;&#955;&#183;</a
      ><a name="18766"
      > </a
      ><a name="18767" href="Stlc.html#9602" class="InductiveConstructor"
      >value-true</a
      ><a name="18777" class="Symbol"
      >)</a
      ><a name="18778"
      > </a
      ><a name="18779" href="Stlc.html#17910" class="InductiveConstructor Operator"
      >&#10217;</a
      ><a name="18780"
      >
    </a
      ><a name="18785" href="Stlc.html#5714" class="Function"
      >not</a
      ><a name="18788"
      > </a
      ><a name="18789" href="Stlc.html#3699" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="18790"
      > </a
      ><a name="18791" class="Symbol"
      >(</a
      ><a name="18792" href="Stlc.html#3755" class="InductiveConstructor Operator"
      >if</a
      ><a name="18794"
      > </a
      ><a name="18795" href="Stlc.html#3726" class="InductiveConstructor"
      >true</a
      ><a name="18799"
      > </a
      ><a name="18800" href="Stlc.html#3755" class="InductiveConstructor Operator"
      >then</a
      ><a name="18804"
      > </a
      ><a name="18805" href="Stlc.html#3740" class="InductiveConstructor"
      >false</a
      ><a name="18810"
      > </a
      ><a name="18811" href="Stlc.html#3755" class="InductiveConstructor Operator"
      >else</a
      ><a name="18815"
      > </a
      ><a name="18816" href="Stlc.html#3726" class="InductiveConstructor"
      >true</a
      ><a name="18820" class="Symbol"
      >)</a
      ><a name="18821"
      >
  </a
      ><a name="18824" href="Stlc.html#17910" class="InductiveConstructor Operator"
      >&#10233;&#10216;</a
      ><a name="18826"
      > </a
      ><a name="18827" href="Stlc.html#15908" class="InductiveConstructor"
      >&#958;&#183;&#8322;</a
      ><a name="18830"
      > </a
      ><a name="18831" href="Stlc.html#9553" class="InductiveConstructor"
      >value-&#955;</a
      ><a name="18838"
      > </a
      ><a name="18839" href="Stlc.html#16130" class="InductiveConstructor"
      >&#946;if-true</a
      ><a name="18847"
      >  </a
      ><a name="18849" href="Stlc.html#17910" class="InductiveConstructor Operator"
      >&#10217;</a
      ><a name="18850"
      >
    </a
      ><a name="18855" href="Stlc.html#5714" class="Function"
      >not</a
      ><a name="18858"
      > </a
      ><a name="18859" href="Stlc.html#3699" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="18860"
      > </a
      ><a name="18861" href="Stlc.html#3740" class="InductiveConstructor"
      >false</a
      ><a name="18866"
      >
  </a
      ><a name="18869" href="Stlc.html#17910" class="InductiveConstructor Operator"
      >&#10233;&#10216;</a
      ><a name="18871"
      > </a
      ><a name="18872" href="Stlc.html#15975" class="InductiveConstructor"
      >&#946;&#955;&#183;</a
      ><a name="18875"
      > </a
      ><a name="18876" href="Stlc.html#9629" class="InductiveConstructor"
      >value-false</a
      ><a name="18887"
      > </a
      ><a name="18888" href="Stlc.html#17910" class="InductiveConstructor Operator"
      >&#10217;</a
      ><a name="18889"
      >
    </a
      ><a name="18894" href="Stlc.html#3755" class="InductiveConstructor Operator"
      >if</a
      ><a name="18896"
      > </a
      ><a name="18897" href="Stlc.html#3740" class="InductiveConstructor"
      >false</a
      ><a name="18902"
      > </a
      ><a name="18903" href="Stlc.html#3755" class="InductiveConstructor Operator"
      >then</a
      ><a name="18907"
      > </a
      ><a name="18908" href="Stlc.html#3740" class="InductiveConstructor"
      >false</a
      ><a name="18913"
      > </a
      ><a name="18914" href="Stlc.html#3755" class="InductiveConstructor Operator"
      >else</a
      ><a name="18918"
      > </a
      ><a name="18919" href="Stlc.html#3726" class="InductiveConstructor"
      >true</a
      ><a name="18923"
      >
  </a
      ><a name="18926" href="Stlc.html#17910" class="InductiveConstructor Operator"
      >&#10233;&#10216;</a
      ><a name="18928"
      > </a
      ><a name="18929" href="Stlc.html#16183" class="InductiveConstructor"
      >&#946;if-false</a
      ><a name="18938"
      > </a
      ><a name="18939" href="Stlc.html#17910" class="InductiveConstructor Operator"
      >&#10217;</a
      ><a name="18940"
      >
    </a
      ><a name="18945" href="Stlc.html#3726" class="InductiveConstructor"
      >true</a
      ><a name="18949"
      >
  </a
      ><a name="18952" href="Stlc.html#17890" class="InductiveConstructor Operator"
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

<a name="21498" href="Stlc.html#21498" class="Function"
      >Context</a
      ><a name="21505"
      > </a
      ><a name="21506" class="Symbol"
      >:</a
      ><a name="21507"
      > </a
      ><a name="21508" class="PrimitiveType"
      >Set</a
      ><a name="21511"
      >
</a
      ><a name="21512" href="Stlc.html#21498" class="Function"
      >Context</a
      ><a name="21519"
      > </a
      ><a name="21520" class="Symbol"
      >=</a
      ><a name="21521"
      > </a
      ><a name="21522" href="Maps.html#10132" class="Function"
      >PartialMap</a
      ><a name="21532"
      > </a
      ><a name="21533" href="Stlc.html#2555" class="Datatype"
      >Type</a
      ><a name="21537"
      >

</a
      ><a name="21539" class="Keyword"
      >infix</a
      ><a name="21544"
      > </a
      ><a name="21545" class="Number"
      >10</a
      ><a name="21547"
      > </a
      ><a name="21548" href="Stlc.html#21560" class="Datatype Operator"
      >_&#8866;_&#8758;_</a
      ><a name="21553"
      >

</a
      ><a name="21555" class="Keyword"
      >data</a
      ><a name="21559"
      > </a
      ><a name="21560" href="Stlc.html#21560" class="Datatype Operator"
      >_&#8866;_&#8758;_</a
      ><a name="21565"
      > </a
      ><a name="21566" class="Symbol"
      >:</a
      ><a name="21567"
      > </a
      ><a name="21568" href="Stlc.html#21498" class="Function"
      >Context</a
      ><a name="21575"
      > </a
      ><a name="21576" class="Symbol"
      >&#8594;</a
      ><a name="21577"
      > </a
      ><a name="21578" href="Stlc.html#3628" class="Datatype"
      >Term</a
      ><a name="21582"
      > </a
      ><a name="21583" class="Symbol"
      >&#8594;</a
      ><a name="21584"
      > </a
      ><a name="21585" href="Stlc.html#2555" class="Datatype"
      >Type</a
      ><a name="21589"
      > </a
      ><a name="21590" class="Symbol"
      >&#8594;</a
      ><a name="21591"
      > </a
      ><a name="21592" class="PrimitiveType"
      >Set</a
      ><a name="21595"
      > </a
      ><a name="21596" class="Keyword"
      >where</a
      ><a name="21601"
      >
  </a
      ><a name="21604" href="Stlc.html#21604" class="InductiveConstructor"
      >Ax</a
      ><a name="21606"
      > </a
      ><a name="21607" class="Symbol"
      >:</a
      ><a name="21608"
      > </a
      ><a name="21609" class="Symbol"
      >&#8704;</a
      ><a name="21610"
      > </a
      ><a name="21611" class="Symbol"
      >{</a
      ><a name="21612" href="Stlc.html#21612" class="Bound"
      >&#915;</a
      ><a name="21613"
      > </a
      ><a name="21614" href="Stlc.html#21614" class="Bound"
      >x</a
      ><a name="21615"
      > </a
      ><a name="21616" href="Stlc.html#21616" class="Bound"
      >A</a
      ><a name="21617" class="Symbol"
      >}</a
      ><a name="21618"
      > </a
      ><a name="21619" class="Symbol"
      >&#8594;</a
      ><a name="21620"
      >
    </a
      ><a name="21625" href="Stlc.html#21612" class="Bound"
      >&#915;</a
      ><a name="21626"
      > </a
      ><a name="21627" href="Stlc.html#21614" class="Bound"
      >x</a
      ><a name="21628"
      > </a
      ><a name="21629" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="21630"
      > </a
      ><a name="21631" href="https://agda.github.io/agda-stdlib/Data.Maybe.Base.html#373" class="InductiveConstructor"
      >just</a
      ><a name="21635"
      > </a
      ><a name="21636" href="Stlc.html#21616" class="Bound"
      >A</a
      ><a name="21637"
      > </a
      ><a name="21638" class="Symbol"
      >&#8594;</a
      ><a name="21639"
      >
    </a
      ><a name="21644" href="Stlc.html#21612" class="Bound"
      >&#915;</a
      ><a name="21645"
      > </a
      ><a name="21646" href="Stlc.html#21560" class="Datatype Operator"
      >&#8866;</a
      ><a name="21647"
      > </a
      ><a name="21648" href="Stlc.html#3647" class="InductiveConstructor"
      >`</a
      ><a name="21649"
      > </a
      ><a name="21650" href="Stlc.html#21614" class="Bound"
      >x</a
      ><a name="21651"
      > </a
      ><a name="21652" href="Stlc.html#21560" class="Datatype Operator"
      >&#8758;</a
      ><a name="21653"
      > </a
      ><a name="21654" href="Stlc.html#21616" class="Bound"
      >A</a
      ><a name="21655"
      >
  </a
      ><a name="21658" href="Stlc.html#21658" class="InductiveConstructor"
      >&#8658;-I</a
      ><a name="21661"
      > </a
      ><a name="21662" class="Symbol"
      >:</a
      ><a name="21663"
      > </a
      ><a name="21664" class="Symbol"
      >&#8704;</a
      ><a name="21665"
      > </a
      ><a name="21666" class="Symbol"
      >{</a
      ><a name="21667" href="Stlc.html#21667" class="Bound"
      >&#915;</a
      ><a name="21668"
      > </a
      ><a name="21669" href="Stlc.html#21669" class="Bound"
      >x</a
      ><a name="21670"
      > </a
      ><a name="21671" href="Stlc.html#21671" class="Bound"
      >N</a
      ><a name="21672"
      > </a
      ><a name="21673" href="Stlc.html#21673" class="Bound"
      >A</a
      ><a name="21674"
      > </a
      ><a name="21675" href="Stlc.html#21675" class="Bound"
      >B</a
      ><a name="21676" class="Symbol"
      >}</a
      ><a name="21677"
      > </a
      ><a name="21678" class="Symbol"
      >&#8594;</a
      ><a name="21679"
      >
    </a
      ><a name="21684" href="Stlc.html#21667" class="Bound"
      >&#915;</a
      ><a name="21685"
      > </a
      ><a name="21686" href="Maps.html#10368" class="Function Operator"
      >,</a
      ><a name="21687"
      > </a
      ><a name="21688" href="Stlc.html#21669" class="Bound"
      >x</a
      ><a name="21689"
      > </a
      ><a name="21690" href="Maps.html#10368" class="Function Operator"
      >&#8758;</a
      ><a name="21691"
      > </a
      ><a name="21692" href="Stlc.html#21673" class="Bound"
      >A</a
      ><a name="21693"
      > </a
      ><a name="21694" href="Stlc.html#21560" class="Datatype Operator"
      >&#8866;</a
      ><a name="21695"
      > </a
      ><a name="21696" href="Stlc.html#21671" class="Bound"
      >N</a
      ><a name="21697"
      > </a
      ><a name="21698" href="Stlc.html#21560" class="Datatype Operator"
      >&#8758;</a
      ><a name="21699"
      > </a
      ><a name="21700" href="Stlc.html#21675" class="Bound"
      >B</a
      ><a name="21701"
      > </a
      ><a name="21702" class="Symbol"
      >&#8594;</a
      ><a name="21703"
      >
    </a
      ><a name="21708" href="Stlc.html#21667" class="Bound"
      >&#915;</a
      ><a name="21709"
      > </a
      ><a name="21710" href="Stlc.html#21560" class="Datatype Operator"
      >&#8866;</a
      ><a name="21711"
      > </a
      ><a name="21712" href="Stlc.html#3663" class="InductiveConstructor Operator"
      >&#955;[</a
      ><a name="21714"
      > </a
      ><a name="21715" href="Stlc.html#21669" class="Bound"
      >x</a
      ><a name="21716"
      > </a
      ><a name="21717" href="Stlc.html#3663" class="InductiveConstructor Operator"
      >&#8758;</a
      ><a name="21718"
      > </a
      ><a name="21719" href="Stlc.html#21673" class="Bound"
      >A</a
      ><a name="21720"
      > </a
      ><a name="21721" href="Stlc.html#3663" class="InductiveConstructor Operator"
      >]</a
      ><a name="21722"
      > </a
      ><a name="21723" href="Stlc.html#21671" class="Bound"
      >N</a
      ><a name="21724"
      > </a
      ><a name="21725" href="Stlc.html#21560" class="Datatype Operator"
      >&#8758;</a
      ><a name="21726"
      > </a
      ><a name="21727" href="Stlc.html#21673" class="Bound"
      >A</a
      ><a name="21728"
      > </a
      ><a name="21729" href="Stlc.html#2574" class="InductiveConstructor Operator"
      >&#8658;</a
      ><a name="21730"
      > </a
      ><a name="21731" href="Stlc.html#21675" class="Bound"
      >B</a
      ><a name="21732"
      >
  </a
      ><a name="21735" href="Stlc.html#21735" class="InductiveConstructor"
      >&#8658;-E</a
      ><a name="21738"
      > </a
      ><a name="21739" class="Symbol"
      >:</a
      ><a name="21740"
      > </a
      ><a name="21741" class="Symbol"
      >&#8704;</a
      ><a name="21742"
      > </a
      ><a name="21743" class="Symbol"
      >{</a
      ><a name="21744" href="Stlc.html#21744" class="Bound"
      >&#915;</a
      ><a name="21745"
      > </a
      ><a name="21746" href="Stlc.html#21746" class="Bound"
      >L</a
      ><a name="21747"
      > </a
      ><a name="21748" href="Stlc.html#21748" class="Bound"
      >M</a
      ><a name="21749"
      > </a
      ><a name="21750" href="Stlc.html#21750" class="Bound"
      >A</a
      ><a name="21751"
      > </a
      ><a name="21752" href="Stlc.html#21752" class="Bound"
      >B</a
      ><a name="21753" class="Symbol"
      >}</a
      ><a name="21754"
      > </a
      ><a name="21755" class="Symbol"
      >&#8594;</a
      ><a name="21756"
      >
    </a
      ><a name="21761" href="Stlc.html#21744" class="Bound"
      >&#915;</a
      ><a name="21762"
      > </a
      ><a name="21763" href="Stlc.html#21560" class="Datatype Operator"
      >&#8866;</a
      ><a name="21764"
      > </a
      ><a name="21765" href="Stlc.html#21746" class="Bound"
      >L</a
      ><a name="21766"
      > </a
      ><a name="21767" href="Stlc.html#21560" class="Datatype Operator"
      >&#8758;</a
      ><a name="21768"
      > </a
      ><a name="21769" href="Stlc.html#21750" class="Bound"
      >A</a
      ><a name="21770"
      > </a
      ><a name="21771" href="Stlc.html#2574" class="InductiveConstructor Operator"
      >&#8658;</a
      ><a name="21772"
      > </a
      ><a name="21773" href="Stlc.html#21752" class="Bound"
      >B</a
      ><a name="21774"
      > </a
      ><a name="21775" class="Symbol"
      >&#8594;</a
      ><a name="21776"
      >
    </a
      ><a name="21781" href="Stlc.html#21744" class="Bound"
      >&#915;</a
      ><a name="21782"
      > </a
      ><a name="21783" href="Stlc.html#21560" class="Datatype Operator"
      >&#8866;</a
      ><a name="21784"
      > </a
      ><a name="21785" href="Stlc.html#21748" class="Bound"
      >M</a
      ><a name="21786"
      > </a
      ><a name="21787" href="Stlc.html#21560" class="Datatype Operator"
      >&#8758;</a
      ><a name="21788"
      > </a
      ><a name="21789" href="Stlc.html#21750" class="Bound"
      >A</a
      ><a name="21790"
      > </a
      ><a name="21791" class="Symbol"
      >&#8594;</a
      ><a name="21792"
      >
    </a
      ><a name="21797" href="Stlc.html#21744" class="Bound"
      >&#915;</a
      ><a name="21798"
      > </a
      ><a name="21799" href="Stlc.html#21560" class="Datatype Operator"
      >&#8866;</a
      ><a name="21800"
      > </a
      ><a name="21801" href="Stlc.html#21746" class="Bound"
      >L</a
      ><a name="21802"
      > </a
      ><a name="21803" href="Stlc.html#3699" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="21804"
      > </a
      ><a name="21805" href="Stlc.html#21748" class="Bound"
      >M</a
      ><a name="21806"
      > </a
      ><a name="21807" href="Stlc.html#21560" class="Datatype Operator"
      >&#8758;</a
      ><a name="21808"
      > </a
      ><a name="21809" href="Stlc.html#21752" class="Bound"
      >B</a
      ><a name="21810"
      >
  </a
      ><a name="21813" href="Stlc.html#21813" class="InductiveConstructor"
      >&#120121;-I&#8321;</a
      ><a name="21817"
      > </a
      ><a name="21818" class="Symbol"
      >:</a
      ><a name="21819"
      > </a
      ><a name="21820" class="Symbol"
      >&#8704;</a
      ><a name="21821"
      > </a
      ><a name="21822" class="Symbol"
      >{</a
      ><a name="21823" href="Stlc.html#21823" class="Bound"
      >&#915;</a
      ><a name="21824" class="Symbol"
      >}</a
      ><a name="21825"
      > </a
      ><a name="21826" class="Symbol"
      >&#8594;</a
      ><a name="21827"
      >
    </a
      ><a name="21832" href="Stlc.html#21823" class="Bound"
      >&#915;</a
      ><a name="21833"
      > </a
      ><a name="21834" href="Stlc.html#21560" class="Datatype Operator"
      >&#8866;</a
      ><a name="21835"
      > </a
      ><a name="21836" href="Stlc.html#3726" class="InductiveConstructor"
      >true</a
      ><a name="21840"
      > </a
      ><a name="21841" href="Stlc.html#21560" class="Datatype Operator"
      >&#8758;</a
      ><a name="21842"
      > </a
      ><a name="21843" href="Stlc.html#2601" class="InductiveConstructor"
      >&#120121;</a
      ><a name="21844"
      >
  </a
      ><a name="21847" href="Stlc.html#21847" class="InductiveConstructor"
      >&#120121;-I&#8322;</a
      ><a name="21851"
      > </a
      ><a name="21852" class="Symbol"
      >:</a
      ><a name="21853"
      > </a
      ><a name="21854" class="Symbol"
      >&#8704;</a
      ><a name="21855"
      > </a
      ><a name="21856" class="Symbol"
      >{</a
      ><a name="21857" href="Stlc.html#21857" class="Bound"
      >&#915;</a
      ><a name="21858" class="Symbol"
      >}</a
      ><a name="21859"
      > </a
      ><a name="21860" class="Symbol"
      >&#8594;</a
      ><a name="21861"
      >
    </a
      ><a name="21866" href="Stlc.html#21857" class="Bound"
      >&#915;</a
      ><a name="21867"
      > </a
      ><a name="21868" href="Stlc.html#21560" class="Datatype Operator"
      >&#8866;</a
      ><a name="21869"
      > </a
      ><a name="21870" href="Stlc.html#3740" class="InductiveConstructor"
      >false</a
      ><a name="21875"
      > </a
      ><a name="21876" href="Stlc.html#21560" class="Datatype Operator"
      >&#8758;</a
      ><a name="21877"
      > </a
      ><a name="21878" href="Stlc.html#2601" class="InductiveConstructor"
      >&#120121;</a
      ><a name="21879"
      >
  </a
      ><a name="21882" href="Stlc.html#21882" class="InductiveConstructor"
      >&#120121;-E</a
      ><a name="21885"
      > </a
      ><a name="21886" class="Symbol"
      >:</a
      ><a name="21887"
      > </a
      ><a name="21888" class="Symbol"
      >&#8704;</a
      ><a name="21889"
      > </a
      ><a name="21890" class="Symbol"
      >{</a
      ><a name="21891" href="Stlc.html#21891" class="Bound"
      >&#915;</a
      ><a name="21892"
      > </a
      ><a name="21893" href="Stlc.html#21893" class="Bound"
      >L</a
      ><a name="21894"
      > </a
      ><a name="21895" href="Stlc.html#21895" class="Bound"
      >M</a
      ><a name="21896"
      > </a
      ><a name="21897" href="Stlc.html#21897" class="Bound"
      >N</a
      ><a name="21898"
      > </a
      ><a name="21899" href="Stlc.html#21899" class="Bound"
      >A</a
      ><a name="21900" class="Symbol"
      >}</a
      ><a name="21901"
      > </a
      ><a name="21902" class="Symbol"
      >&#8594;</a
      ><a name="21903"
      >
    </a
      ><a name="21908" href="Stlc.html#21891" class="Bound"
      >&#915;</a
      ><a name="21909"
      > </a
      ><a name="21910" href="Stlc.html#21560" class="Datatype Operator"
      >&#8866;</a
      ><a name="21911"
      > </a
      ><a name="21912" href="Stlc.html#21893" class="Bound"
      >L</a
      ><a name="21913"
      > </a
      ><a name="21914" href="Stlc.html#21560" class="Datatype Operator"
      >&#8758;</a
      ><a name="21915"
      > </a
      ><a name="21916" href="Stlc.html#2601" class="InductiveConstructor"
      >&#120121;</a
      ><a name="21917"
      > </a
      ><a name="21918" class="Symbol"
      >&#8594;</a
      ><a name="21919"
      >
    </a
      ><a name="21924" href="Stlc.html#21891" class="Bound"
      >&#915;</a
      ><a name="21925"
      > </a
      ><a name="21926" href="Stlc.html#21560" class="Datatype Operator"
      >&#8866;</a
      ><a name="21927"
      > </a
      ><a name="21928" href="Stlc.html#21895" class="Bound"
      >M</a
      ><a name="21929"
      > </a
      ><a name="21930" href="Stlc.html#21560" class="Datatype Operator"
      >&#8758;</a
      ><a name="21931"
      > </a
      ><a name="21932" href="Stlc.html#21899" class="Bound"
      >A</a
      ><a name="21933"
      > </a
      ><a name="21934" class="Symbol"
      >&#8594;</a
      ><a name="21935"
      >
    </a
      ><a name="21940" href="Stlc.html#21891" class="Bound"
      >&#915;</a
      ><a name="21941"
      > </a
      ><a name="21942" href="Stlc.html#21560" class="Datatype Operator"
      >&#8866;</a
      ><a name="21943"
      > </a
      ><a name="21944" href="Stlc.html#21897" class="Bound"
      >N</a
      ><a name="21945"
      > </a
      ><a name="21946" href="Stlc.html#21560" class="Datatype Operator"
      >&#8758;</a
      ><a name="21947"
      > </a
      ><a name="21948" href="Stlc.html#21899" class="Bound"
      >A</a
      ><a name="21949"
      > </a
      ><a name="21950" class="Symbol"
      >&#8594;</a
      ><a name="21951"
      >
    </a
      ><a name="21956" href="Stlc.html#21891" class="Bound"
      >&#915;</a
      ><a name="21957"
      > </a
      ><a name="21958" href="Stlc.html#21560" class="Datatype Operator"
      >&#8866;</a
      ><a name="21959"
      > </a
      ><a name="21960" href="Stlc.html#3755" class="InductiveConstructor Operator"
      >if</a
      ><a name="21962"
      > </a
      ><a name="21963" href="Stlc.html#21893" class="Bound"
      >L</a
      ><a name="21964"
      > </a
      ><a name="21965" href="Stlc.html#3755" class="InductiveConstructor Operator"
      >then</a
      ><a name="21969"
      > </a
      ><a name="21970" href="Stlc.html#21895" class="Bound"
      >M</a
      ><a name="21971"
      > </a
      ><a name="21972" href="Stlc.html#3755" class="InductiveConstructor Operator"
      >else</a
      ><a name="21976"
      > </a
      ><a name="21977" href="Stlc.html#21897" class="Bound"
      >N</a
      ><a name="21978"
      > </a
      ><a name="21979" href="Stlc.html#21560" class="Datatype Operator"
      >&#8758;</a
      ><a name="21980"
      > </a
      ><a name="21981" href="Stlc.html#21899" class="Bound"
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

<a name="23264" href="Stlc.html#23264" class="Function"
      >typing&#8321;</a
      ><a name="23271"
      > </a
      ><a name="23272" class="Symbol"
      >:</a
      ><a name="23273"
      > </a
      ><a name="23274" href="Maps.html#10265" class="Function"
      >&#8709;</a
      ><a name="23275"
      > </a
      ><a name="23276" href="Stlc.html#21560" class="Datatype Operator"
      >&#8866;</a
      ><a name="23277"
      > </a
      ><a name="23278" href="Stlc.html#5714" class="Function"
      >not</a
      ><a name="23281"
      > </a
      ><a name="23282" href="Stlc.html#21560" class="Datatype Operator"
      >&#8758;</a
      ><a name="23283"
      > </a
      ><a name="23284" href="Stlc.html#2601" class="InductiveConstructor"
      >&#120121;</a
      ><a name="23285"
      > </a
      ><a name="23286" href="Stlc.html#2574" class="InductiveConstructor Operator"
      >&#8658;</a
      ><a name="23287"
      > </a
      ><a name="23288" href="Stlc.html#2601" class="InductiveConstructor"
      >&#120121;</a
      ><a name="23289"
      >
</a
      ><a name="23290" href="Stlc.html#23264" class="Function"
      >typing&#8321;</a
      ><a name="23297"
      > </a
      ><a name="23298" class="Symbol"
      >=</a
      ><a name="23299"
      > </a
      ><a name="23300" href="Stlc.html#21658" class="InductiveConstructor"
      >&#8658;-I</a
      ><a name="23303"
      > </a
      ><a name="23304" class="Symbol"
      >(</a
      ><a name="23305" href="Stlc.html#21882" class="InductiveConstructor"
      >&#120121;-E</a
      ><a name="23308"
      > </a
      ><a name="23309" class="Symbol"
      >(</a
      ><a name="23310" href="Stlc.html#21604" class="InductiveConstructor"
      >Ax</a
      ><a name="23312"
      > </a
      ><a name="23313" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="23317" class="Symbol"
      >)</a
      ><a name="23318"
      > </a
      ><a name="23319" href="Stlc.html#21847" class="InductiveConstructor"
      >&#120121;-I&#8322;</a
      ><a name="23323"
      > </a
      ><a name="23324" href="Stlc.html#21813" class="InductiveConstructor"
      >&#120121;-I&#8321;</a
      ><a name="23328" class="Symbol"
      >)</a
      ><a name="23329"
      >

</a
      ><a name="23331" href="Stlc.html#23331" class="Function"
      >typing&#8322;</a
      ><a name="23338"
      > </a
      ><a name="23339" class="Symbol"
      >:</a
      ><a name="23340"
      > </a
      ><a name="23341" href="Maps.html#10265" class="Function"
      >&#8709;</a
      ><a name="23342"
      > </a
      ><a name="23343" href="Stlc.html#21560" class="Datatype Operator"
      >&#8866;</a
      ><a name="23344"
      > </a
      ><a name="23345" href="Stlc.html#5718" class="Function"
      >two</a
      ><a name="23348"
      > </a
      ><a name="23349" href="Stlc.html#21560" class="Datatype Operator"
      >&#8758;</a
      ><a name="23350"
      > </a
      ><a name="23351" class="Symbol"
      >(</a
      ><a name="23352" href="Stlc.html#2601" class="InductiveConstructor"
      >&#120121;</a
      ><a name="23353"
      > </a
      ><a name="23354" href="Stlc.html#2574" class="InductiveConstructor Operator"
      >&#8658;</a
      ><a name="23355"
      > </a
      ><a name="23356" href="Stlc.html#2601" class="InductiveConstructor"
      >&#120121;</a
      ><a name="23357" class="Symbol"
      >)</a
      ><a name="23358"
      > </a
      ><a name="23359" href="Stlc.html#2574" class="InductiveConstructor Operator"
      >&#8658;</a
      ><a name="23360"
      > </a
      ><a name="23361" href="Stlc.html#2601" class="InductiveConstructor"
      >&#120121;</a
      ><a name="23362"
      > </a
      ><a name="23363" href="Stlc.html#2574" class="InductiveConstructor Operator"
      >&#8658;</a
      ><a name="23364"
      > </a
      ><a name="23365" href="Stlc.html#2601" class="InductiveConstructor"
      >&#120121;</a
      ><a name="23366"
      >
</a
      ><a name="23367" href="Stlc.html#23331" class="Function"
      >typing&#8322;</a
      ><a name="23374"
      > </a
      ><a name="23375" class="Symbol"
      >=</a
      ><a name="23376"
      > </a
      ><a name="23377" href="Stlc.html#21658" class="InductiveConstructor"
      >&#8658;-I</a
      ><a name="23380"
      > </a
      ><a name="23381" class="Symbol"
      >(</a
      ><a name="23382" href="Stlc.html#21658" class="InductiveConstructor"
      >&#8658;-I</a
      ><a name="23385"
      > </a
      ><a name="23386" class="Symbol"
      >(</a
      ><a name="23387" href="Stlc.html#21735" class="InductiveConstructor"
      >&#8658;-E</a
      ><a name="23390"
      > </a
      ><a name="23391" class="Symbol"
      >(</a
      ><a name="23392" href="Stlc.html#21604" class="InductiveConstructor"
      >Ax</a
      ><a name="23394"
      > </a
      ><a name="23395" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="23399" class="Symbol"
      >)</a
      ><a name="23400"
      > </a
      ><a name="23401" class="Symbol"
      >(</a
      ><a name="23402" href="Stlc.html#21735" class="InductiveConstructor"
      >&#8658;-E</a
      ><a name="23405"
      > </a
      ><a name="23406" class="Symbol"
      >(</a
      ><a name="23407" href="Stlc.html#21604" class="InductiveConstructor"
      >Ax</a
      ><a name="23409"
      > </a
      ><a name="23410" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="23414" class="Symbol"
      >)</a
      ><a name="23415"
      > </a
      ><a name="23416" class="Symbol"
      >(</a
      ><a name="23417" href="Stlc.html#21604" class="InductiveConstructor"
      >Ax</a
      ><a name="23419"
      > </a
      ><a name="23420" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="23424" class="Symbol"
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

We can also show that terms are _not_ typeable.
For example, here is a formal proof that it is not possible
to type the term `` λ[ x ∶ 𝔹 ] λ[ y ∶ 𝔹 ] ` x · ` y ``.
In other words, no type `A` is the type of this term.

<pre class="Agda">

<a name="25002" href="Stlc.html#25002" class="Function"
      >contradiction</a
      ><a name="25015"
      > </a
      ><a name="25016" class="Symbol"
      >:</a
      ><a name="25017"
      > </a
      ><a name="25018" class="Symbol"
      >&#8704;</a
      ><a name="25019"
      > </a
      ><a name="25020" class="Symbol"
      >{</a
      ><a name="25021" href="Stlc.html#25021" class="Bound"
      >A</a
      ><a name="25022"
      > </a
      ><a name="25023" href="Stlc.html#25023" class="Bound"
      >B</a
      ><a name="25024" class="Symbol"
      >}</a
      ><a name="25025"
      > </a
      ><a name="25026" class="Symbol"
      >&#8594;</a
      ><a name="25027"
      > </a
      ><a name="25028" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#414" class="Function Operator"
      >&#172;</a
      ><a name="25029"
      > </a
      ><a name="25030" class="Symbol"
      >(</a
      ><a name="25031" href="Stlc.html#2601" class="InductiveConstructor"
      >&#120121;</a
      ><a name="25032"
      > </a
      ><a name="25033" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="25034"
      > </a
      ><a name="25035" href="Stlc.html#25021" class="Bound"
      >A</a
      ><a name="25036"
      > </a
      ><a name="25037" href="Stlc.html#2574" class="InductiveConstructor Operator"
      >&#8658;</a
      ><a name="25038"
      > </a
      ><a name="25039" href="Stlc.html#25023" class="Bound"
      >B</a
      ><a name="25040" class="Symbol"
      >)</a
      ><a name="25041"
      >
</a
      ><a name="25042" href="Stlc.html#25002" class="Function"
      >contradiction</a
      ><a name="25055"
      > </a
      ><a name="25056" class="Symbol"
      >()</a
      ><a name="25058"
      >

</a
      ><a name="25060" href="Stlc.html#25060" class="Function"
      >notyping</a
      ><a name="25068"
      > </a
      ><a name="25069" class="Symbol"
      >:</a
      ><a name="25070"
      > </a
      ><a name="25071" class="Symbol"
      >&#8704;</a
      ><a name="25072"
      > </a
      ><a name="25073" class="Symbol"
      >{</a
      ><a name="25074" href="Stlc.html#25074" class="Bound"
      >A</a
      ><a name="25075" class="Symbol"
      >}</a
      ><a name="25076"
      > </a
      ><a name="25077" class="Symbol"
      >&#8594;</a
      ><a name="25078"
      > </a
      ><a name="25079" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#414" class="Function Operator"
      >&#172;</a
      ><a name="25080"
      > </a
      ><a name="25081" class="Symbol"
      >(</a
      ><a name="25082" href="Maps.html#10265" class="Function"
      >&#8709;</a
      ><a name="25083"
      > </a
      ><a name="25084" href="Stlc.html#21560" class="Datatype Operator"
      >&#8866;</a
      ><a name="25085"
      > </a
      ><a name="25086" href="Stlc.html#3663" class="InductiveConstructor Operator"
      >&#955;[</a
      ><a name="25088"
      > </a
      ><a name="25089" href="Stlc.html#5671" class="Function"
      >x</a
      ><a name="25090"
      > </a
      ><a name="25091" href="Stlc.html#3663" class="InductiveConstructor Operator"
      >&#8758;</a
      ><a name="25092"
      > </a
      ><a name="25093" href="Stlc.html#2601" class="InductiveConstructor"
      >&#120121;</a
      ><a name="25094"
      > </a
      ><a name="25095" href="Stlc.html#3663" class="InductiveConstructor Operator"
      >]</a
      ><a name="25096"
      > </a
      ><a name="25097" href="Stlc.html#3663" class="InductiveConstructor Operator"
      >&#955;[</a
      ><a name="25099"
      > </a
      ><a name="25100" href="Stlc.html#5673" class="Function"
      >y</a
      ><a name="25101"
      > </a
      ><a name="25102" href="Stlc.html#3663" class="InductiveConstructor Operator"
      >&#8758;</a
      ><a name="25103"
      > </a
      ><a name="25104" href="Stlc.html#2601" class="InductiveConstructor"
      >&#120121;</a
      ><a name="25105"
      > </a
      ><a name="25106" href="Stlc.html#3663" class="InductiveConstructor Operator"
      >]</a
      ><a name="25107"
      > </a
      ><a name="25108" href="Stlc.html#3647" class="InductiveConstructor"
      >`</a
      ><a name="25109"
      > </a
      ><a name="25110" href="Stlc.html#5671" class="Function"
      >x</a
      ><a name="25111"
      > </a
      ><a name="25112" href="Stlc.html#3699" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="25113"
      > </a
      ><a name="25114" href="Stlc.html#3647" class="InductiveConstructor"
      >`</a
      ><a name="25115"
      > </a
      ><a name="25116" href="Stlc.html#5673" class="Function"
      >y</a
      ><a name="25117"
      > </a
      ><a name="25118" href="Stlc.html#21560" class="Datatype Operator"
      >&#8758;</a
      ><a name="25119"
      > </a
      ><a name="25120" href="Stlc.html#25074" class="Bound"
      >A</a
      ><a name="25121" class="Symbol"
      >)</a
      ><a name="25122"
      >
</a
      ><a name="25123" href="Stlc.html#25060" class="Function"
      >notyping</a
      ><a name="25131"
      > </a
      ><a name="25132" class="Symbol"
      >(</a
      ><a name="25133" href="Stlc.html#21658" class="InductiveConstructor"
      >&#8658;-I</a
      ><a name="25136"
      > </a
      ><a name="25137" class="Symbol"
      >(</a
      ><a name="25138" href="Stlc.html#21658" class="InductiveConstructor"
      >&#8658;-I</a
      ><a name="25141"
      > </a
      ><a name="25142" class="Symbol"
      >(</a
      ><a name="25143" href="Stlc.html#21735" class="InductiveConstructor"
      >&#8658;-E</a
      ><a name="25146"
      > </a
      ><a name="25147" class="Symbol"
      >(</a
      ><a name="25148" href="Stlc.html#21604" class="InductiveConstructor"
      >Ax</a
      ><a name="25150"
      > </a
      ><a name="25151" href="Stlc.html#25151" class="Bound"
      >&#915;x</a
      ><a name="25153" class="Symbol"
      >)</a
      ><a name="25154"
      > </a
      ><a name="25155" class="Symbol"
      >(</a
      ><a name="25156" href="Stlc.html#21604" class="InductiveConstructor"
      >Ax</a
      ><a name="25158"
      > </a
      ><a name="25159" href="Stlc.html#25159" class="Bound"
      >&#915;y</a
      ><a name="25161" class="Symbol"
      >))))</a
      ><a name="25165"
      > </a
      ><a name="25166" class="Symbol"
      >=</a
      ><a name="25167"
      >  </a
      ><a name="25169" href="Stlc.html#25002" class="Function"
      >contradiction</a
      ><a name="25182"
      > </a
      ><a name="25183" class="Symbol"
      >(</a
      ><a name="25184" href="Maps.html#11919" class="Function"
      >just-injective</a
      ><a name="25198"
      > </a
      ><a name="25199" href="Stlc.html#25151" class="Bound"
      >&#915;x</a
      ><a name="25201" class="Symbol"
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



