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

CONTINUE FROM HERE



Example terms.
<pre class="Agda">

<a name="3839" href="Stlc.html#3839" class="Function"
      >f</a
      ><a name="3840"
      > </a
      ><a name="3841" href="Stlc.html#3841" class="Function"
      >x</a
      ><a name="3842"
      > </a
      ><a name="3843" class="Symbol"
      >:</a
      ><a name="3844"
      > </a
      ><a name="3845" href="Maps.html#2171" class="Datatype"
      >Id</a
      ><a name="3847"
      >
</a
      ><a name="3848" href="Stlc.html#3839" class="Function"
      >f</a
      ><a name="3849"
      >  </a
      ><a name="3851" class="Symbol"
      >=</a
      ><a name="3852"
      >  </a
      ><a name="3854" href="Maps.html#2188" class="InductiveConstructor"
      >id</a
      ><a name="3856"
      > </a
      ><a name="3857" class="Number"
      >0</a
      ><a name="3858"
      >
</a
      ><a name="3859" href="Stlc.html#3841" class="Function"
      >x</a
      ><a name="3860"
      >  </a
      ><a name="3862" class="Symbol"
      >=</a
      ><a name="3863"
      >  </a
      ><a name="3865" href="Maps.html#2188" class="InductiveConstructor"
      >id</a
      ><a name="3867"
      > </a
      ><a name="3868" class="Number"
      >1</a
      ><a name="3869"
      >

</a
      ><a name="3871" href="Stlc.html#3871" class="Function"
      >not</a
      ><a name="3874"
      > </a
      ><a name="3875" href="Stlc.html#3875" class="Function"
      >two</a
      ><a name="3878"
      > </a
      ><a name="3879" class="Symbol"
      >:</a
      ><a name="3880"
      > </a
      ><a name="3881" href="Stlc.html#3608" class="Datatype"
      >Term</a
      ><a name="3885"
      > 
</a
      ><a name="3887" href="Stlc.html#3871" class="Function"
      >not</a
      ><a name="3890"
      > </a
      ><a name="3891" class="Symbol"
      >=</a
      ><a name="3892"
      >  </a
      ><a name="3894" href="Stlc.html#3643" class="InductiveConstructor Operator"
      >&#955;[</a
      ><a name="3896"
      > </a
      ><a name="3897" href="Stlc.html#3841" class="Function"
      >x</a
      ><a name="3898"
      > </a
      ><a name="3899" href="Stlc.html#3643" class="InductiveConstructor Operator"
      >&#8758;</a
      ><a name="3900"
      > </a
      ><a name="3901" href="Stlc.html#2581" class="InductiveConstructor"
      >&#120121;</a
      ><a name="3902"
      > </a
      ><a name="3903" href="Stlc.html#3643" class="InductiveConstructor Operator"
      >]</a
      ><a name="3904"
      > </a
      ><a name="3905" class="Symbol"
      >(</a
      ><a name="3906" href="Stlc.html#3735" class="InductiveConstructor Operator"
      >if</a
      ><a name="3908"
      > </a
      ><a name="3909" href="Stlc.html#3627" class="InductiveConstructor"
      >`</a
      ><a name="3910"
      > </a
      ><a name="3911" href="Stlc.html#3841" class="Function"
      >x</a
      ><a name="3912"
      > </a
      ><a name="3913" href="Stlc.html#3735" class="InductiveConstructor Operator"
      >then</a
      ><a name="3917"
      > </a
      ><a name="3918" href="Stlc.html#3720" class="InductiveConstructor"
      >false</a
      ><a name="3923"
      > </a
      ><a name="3924" href="Stlc.html#3735" class="InductiveConstructor Operator"
      >else</a
      ><a name="3928"
      > </a
      ><a name="3929" href="Stlc.html#3706" class="InductiveConstructor"
      >true</a
      ><a name="3933" class="Symbol"
      >)</a
      ><a name="3934"
      >
</a
      ><a name="3935" href="Stlc.html#3875" class="Function"
      >two</a
      ><a name="3938"
      > </a
      ><a name="3939" class="Symbol"
      >=</a
      ><a name="3940"
      >  </a
      ><a name="3942" href="Stlc.html#3643" class="InductiveConstructor Operator"
      >&#955;[</a
      ><a name="3944"
      > </a
      ><a name="3945" href="Stlc.html#3839" class="Function"
      >f</a
      ><a name="3946"
      > </a
      ><a name="3947" href="Stlc.html#3643" class="InductiveConstructor Operator"
      >&#8758;</a
      ><a name="3948"
      > </a
      ><a name="3949" href="Stlc.html#2581" class="InductiveConstructor"
      >&#120121;</a
      ><a name="3950"
      > </a
      ><a name="3951" href="Stlc.html#2554" class="InductiveConstructor Operator"
      >&#8658;</a
      ><a name="3952"
      > </a
      ><a name="3953" href="Stlc.html#2581" class="InductiveConstructor"
      >&#120121;</a
      ><a name="3954"
      > </a
      ><a name="3955" href="Stlc.html#3643" class="InductiveConstructor Operator"
      >]</a
      ><a name="3956"
      > </a
      ><a name="3957" href="Stlc.html#3643" class="InductiveConstructor Operator"
      >&#955;[</a
      ><a name="3959"
      > </a
      ><a name="3960" href="Stlc.html#3841" class="Function"
      >x</a
      ><a name="3961"
      > </a
      ><a name="3962" href="Stlc.html#3643" class="InductiveConstructor Operator"
      >&#8758;</a
      ><a name="3963"
      > </a
      ><a name="3964" href="Stlc.html#2581" class="InductiveConstructor"
      >&#120121;</a
      ><a name="3965"
      > </a
      ><a name="3966" href="Stlc.html#3643" class="InductiveConstructor Operator"
      >]</a
      ><a name="3967"
      > </a
      ><a name="3968" href="Stlc.html#3627" class="InductiveConstructor"
      >`</a
      ><a name="3969"
      > </a
      ><a name="3970" href="Stlc.html#3839" class="Function"
      >f</a
      ><a name="3971"
      > </a
      ><a name="3972" href="Stlc.html#3679" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="3973"
      > </a
      ><a name="3974" class="Symbol"
      >(</a
      ><a name="3975" href="Stlc.html#3627" class="InductiveConstructor"
      >`</a
      ><a name="3976"
      > </a
      ><a name="3977" href="Stlc.html#3839" class="Function"
      >f</a
      ><a name="3978"
      > </a
      ><a name="3979" href="Stlc.html#3679" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="3980"
      > </a
      ><a name="3981" href="Stlc.html#3627" class="InductiveConstructor"
      >`</a
      ><a name="3982"
      > </a
      ><a name="3983" href="Stlc.html#3841" class="Function"
      >x</a
      ><a name="3984" class="Symbol"
      >)</a
      >

</pre>

## Values

<pre class="Agda">

<a name="4022" class="Keyword"
      >data</a
      ><a name="4026"
      > </a
      ><a name="4027" href="Stlc.html#4027" class="Datatype"
      >Value</a
      ><a name="4032"
      > </a
      ><a name="4033" class="Symbol"
      >:</a
      ><a name="4034"
      > </a
      ><a name="4035" href="Stlc.html#3608" class="Datatype"
      >Term</a
      ><a name="4039"
      > </a
      ><a name="4040" class="Symbol"
      >&#8594;</a
      ><a name="4041"
      > </a
      ><a name="4042" class="PrimitiveType"
      >Set</a
      ><a name="4045"
      > </a
      ><a name="4046" class="Keyword"
      >where</a
      ><a name="4051"
      >
  </a
      ><a name="4054" href="Stlc.html#4054" class="InductiveConstructor"
      >value-&#955;</a
      ><a name="4061"
      >     </a
      ><a name="4066" class="Symbol"
      >:</a
      ><a name="4067"
      > </a
      ><a name="4068" class="Symbol"
      >&#8704;</a
      ><a name="4069"
      > </a
      ><a name="4070" class="Symbol"
      >{</a
      ><a name="4071" href="Stlc.html#4071" class="Bound"
      >x</a
      ><a name="4072"
      > </a
      ><a name="4073" href="Stlc.html#4073" class="Bound"
      >A</a
      ><a name="4074"
      > </a
      ><a name="4075" href="Stlc.html#4075" class="Bound"
      >N</a
      ><a name="4076" class="Symbol"
      >}</a
      ><a name="4077"
      > </a
      ><a name="4078" class="Symbol"
      >&#8594;</a
      ><a name="4079"
      > </a
      ><a name="4080" href="Stlc.html#4027" class="Datatype"
      >Value</a
      ><a name="4085"
      > </a
      ><a name="4086" class="Symbol"
      >(</a
      ><a name="4087" href="Stlc.html#3643" class="InductiveConstructor Operator"
      >&#955;[</a
      ><a name="4089"
      > </a
      ><a name="4090" href="Stlc.html#4071" class="Bound"
      >x</a
      ><a name="4091"
      > </a
      ><a name="4092" href="Stlc.html#3643" class="InductiveConstructor Operator"
      >&#8758;</a
      ><a name="4093"
      > </a
      ><a name="4094" href="Stlc.html#4073" class="Bound"
      >A</a
      ><a name="4095"
      > </a
      ><a name="4096" href="Stlc.html#3643" class="InductiveConstructor Operator"
      >]</a
      ><a name="4097"
      > </a
      ><a name="4098" href="Stlc.html#4075" class="Bound"
      >N</a
      ><a name="4099" class="Symbol"
      >)</a
      ><a name="4100"
      >
  </a
      ><a name="4103" href="Stlc.html#4103" class="InductiveConstructor"
      >value-true</a
      ><a name="4113"
      >  </a
      ><a name="4115" class="Symbol"
      >:</a
      ><a name="4116"
      > </a
      ><a name="4117" href="Stlc.html#4027" class="Datatype"
      >Value</a
      ><a name="4122"
      > </a
      ><a name="4123" href="Stlc.html#3706" class="InductiveConstructor"
      >true</a
      ><a name="4127"
      >
  </a
      ><a name="4130" href="Stlc.html#4130" class="InductiveConstructor"
      >value-false</a
      ><a name="4141"
      > </a
      ><a name="4142" class="Symbol"
      >:</a
      ><a name="4143"
      > </a
      ><a name="4144" href="Stlc.html#4027" class="Datatype"
      >Value</a
      ><a name="4149"
      > </a
      ><a name="4150" href="Stlc.html#3720" class="InductiveConstructor"
      >false</a
      >

</pre>

## Substitution

<pre class="Agda">

<a name="4198" href="Stlc.html#4198" class="Function Operator"
      >_[_:=_]</a
      ><a name="4205"
      > </a
      ><a name="4206" class="Symbol"
      >:</a
      ><a name="4207"
      > </a
      ><a name="4208" href="Stlc.html#3608" class="Datatype"
      >Term</a
      ><a name="4212"
      > </a
      ><a name="4213" class="Symbol"
      >&#8594;</a
      ><a name="4214"
      > </a
      ><a name="4215" href="Maps.html#2171" class="Datatype"
      >Id</a
      ><a name="4217"
      > </a
      ><a name="4218" class="Symbol"
      >&#8594;</a
      ><a name="4219"
      > </a
      ><a name="4220" href="Stlc.html#3608" class="Datatype"
      >Term</a
      ><a name="4224"
      > </a
      ><a name="4225" class="Symbol"
      >&#8594;</a
      ><a name="4226"
      > </a
      ><a name="4227" href="Stlc.html#3608" class="Datatype"
      >Term</a
      ><a name="4231"
      >
</a
      ><a name="4232" class="Symbol"
      >(</a
      ><a name="4233" href="Stlc.html#3627" class="InductiveConstructor"
      >`</a
      ><a name="4234"
      > </a
      ><a name="4235" href="Stlc.html#4235" class="Bound"
      >x&#8242;</a
      ><a name="4237" class="Symbol"
      >)</a
      ><a name="4238"
      > </a
      ><a name="4239" href="Stlc.html#4198" class="Function Operator"
      >[</a
      ><a name="4240"
      > </a
      ><a name="4241" href="Stlc.html#4241" class="Bound"
      >x</a
      ><a name="4242"
      > </a
      ><a name="4243" href="Stlc.html#4198" class="Function Operator"
      >:=</a
      ><a name="4245"
      > </a
      ><a name="4246" href="Stlc.html#4246" class="Bound"
      >V</a
      ><a name="4247"
      > </a
      ><a name="4248" href="Stlc.html#4198" class="Function Operator"
      >]</a
      ><a name="4249"
      > </a
      ><a name="4250" class="Keyword"
      >with</a
      ><a name="4254"
      > </a
      ><a name="4255" href="Stlc.html#4241" class="Bound"
      >x</a
      ><a name="4256"
      > </a
      ><a name="4257" href="Maps.html#2509" class="Function Operator"
      >&#8799;</a
      ><a name="4258"
      > </a
      ><a name="4259" href="Stlc.html#4235" class="Bound"
      >x&#8242;</a
      ><a name="4261"
      >
</a
      ><a name="4262" class="Symbol"
      >...</a
      ><a name="4265"
      > </a
      ><a name="4266" class="Symbol"
      >|</a
      ><a name="4267"
      > </a
      ><a name="4268" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#520" class="InductiveConstructor"
      >yes</a
      ><a name="4271"
      > </a
      ><a name="4272" class="Symbol"
      >_</a
      ><a name="4273"
      > </a
      ><a name="4274" class="Symbol"
      >=</a
      ><a name="4275"
      > </a
      ><a name="4276" href="Stlc.html#4246" class="Bound"
      >V</a
      ><a name="4277"
      >
</a
      ><a name="4278" class="Symbol"
      >...</a
      ><a name="4281"
      > </a
      ><a name="4282" class="Symbol"
      >|</a
      ><a name="4283"
      > </a
      ><a name="4284" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#547" class="InductiveConstructor"
      >no</a
      ><a name="4286"
      >  </a
      ><a name="4288" class="Symbol"
      >_</a
      ><a name="4289"
      > </a
      ><a name="4290" class="Symbol"
      >=</a
      ><a name="4291"
      > </a
      ><a name="4292" href="Stlc.html#3627" class="InductiveConstructor"
      >`</a
      ><a name="4293"
      > </a
      ><a name="4294" href="Stlc.html#4235" class="Bound"
      >x&#8242;</a
      ><a name="4296"
      >
</a
      ><a name="4297" class="Symbol"
      >(</a
      ><a name="4298" href="Stlc.html#3643" class="InductiveConstructor Operator"
      >&#955;[</a
      ><a name="4300"
      > </a
      ><a name="4301" href="Stlc.html#4301" class="Bound"
      >x&#8242;</a
      ><a name="4303"
      > </a
      ><a name="4304" href="Stlc.html#3643" class="InductiveConstructor Operator"
      >&#8758;</a
      ><a name="4305"
      > </a
      ><a name="4306" href="Stlc.html#4306" class="Bound"
      >A&#8242;</a
      ><a name="4308"
      > </a
      ><a name="4309" href="Stlc.html#3643" class="InductiveConstructor Operator"
      >]</a
      ><a name="4310"
      > </a
      ><a name="4311" href="Stlc.html#4311" class="Bound"
      >N&#8242;</a
      ><a name="4313" class="Symbol"
      >)</a
      ><a name="4314"
      > </a
      ><a name="4315" href="Stlc.html#4198" class="Function Operator"
      >[</a
      ><a name="4316"
      > </a
      ><a name="4317" href="Stlc.html#4317" class="Bound"
      >x</a
      ><a name="4318"
      > </a
      ><a name="4319" href="Stlc.html#4198" class="Function Operator"
      >:=</a
      ><a name="4321"
      > </a
      ><a name="4322" href="Stlc.html#4322" class="Bound"
      >V</a
      ><a name="4323"
      > </a
      ><a name="4324" href="Stlc.html#4198" class="Function Operator"
      >]</a
      ><a name="4325"
      > </a
      ><a name="4326" class="Keyword"
      >with</a
      ><a name="4330"
      > </a
      ><a name="4331" href="Stlc.html#4317" class="Bound"
      >x</a
      ><a name="4332"
      > </a
      ><a name="4333" href="Maps.html#2509" class="Function Operator"
      >&#8799;</a
      ><a name="4334"
      > </a
      ><a name="4335" href="Stlc.html#4301" class="Bound"
      >x&#8242;</a
      ><a name="4337"
      >
</a
      ><a name="4338" class="Symbol"
      >...</a
      ><a name="4341"
      > </a
      ><a name="4342" class="Symbol"
      >|</a
      ><a name="4343"
      > </a
      ><a name="4344" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#520" class="InductiveConstructor"
      >yes</a
      ><a name="4347"
      > </a
      ><a name="4348" class="Symbol"
      >_</a
      ><a name="4349"
      > </a
      ><a name="4350" class="Symbol"
      >=</a
      ><a name="4351"
      > </a
      ><a name="4352" href="Stlc.html#3643" class="InductiveConstructor Operator"
      >&#955;[</a
      ><a name="4354"
      > </a
      ><a name="4355" href="Stlc.html#4301" class="Bound"
      >x&#8242;</a
      ><a name="4357"
      > </a
      ><a name="4358" href="Stlc.html#3643" class="InductiveConstructor Operator"
      >&#8758;</a
      ><a name="4359"
      > </a
      ><a name="4360" href="Stlc.html#4306" class="Bound"
      >A&#8242;</a
      ><a name="4362"
      > </a
      ><a name="4363" href="Stlc.html#3643" class="InductiveConstructor Operator"
      >]</a
      ><a name="4364"
      > </a
      ><a name="4365" href="Stlc.html#4311" class="Bound"
      >N&#8242;</a
      ><a name="4367"
      >
</a
      ><a name="4368" class="Symbol"
      >...</a
      ><a name="4371"
      > </a
      ><a name="4372" class="Symbol"
      >|</a
      ><a name="4373"
      > </a
      ><a name="4374" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#547" class="InductiveConstructor"
      >no</a
      ><a name="4376"
      >  </a
      ><a name="4378" class="Symbol"
      >_</a
      ><a name="4379"
      > </a
      ><a name="4380" class="Symbol"
      >=</a
      ><a name="4381"
      > </a
      ><a name="4382" href="Stlc.html#3643" class="InductiveConstructor Operator"
      >&#955;[</a
      ><a name="4384"
      > </a
      ><a name="4385" href="Stlc.html#4301" class="Bound"
      >x&#8242;</a
      ><a name="4387"
      > </a
      ><a name="4388" href="Stlc.html#3643" class="InductiveConstructor Operator"
      >&#8758;</a
      ><a name="4389"
      > </a
      ><a name="4390" href="Stlc.html#4306" class="Bound"
      >A&#8242;</a
      ><a name="4392"
      > </a
      ><a name="4393" href="Stlc.html#3643" class="InductiveConstructor Operator"
      >]</a
      ><a name="4394"
      > </a
      ><a name="4395" class="Symbol"
      >(</a
      ><a name="4396" href="Stlc.html#4311" class="Bound"
      >N&#8242;</a
      ><a name="4398"
      > </a
      ><a name="4399" href="Stlc.html#4198" class="Function Operator"
      >[</a
      ><a name="4400"
      > </a
      ><a name="4401" href="Stlc.html#4317" class="Bound"
      >x</a
      ><a name="4402"
      > </a
      ><a name="4403" href="Stlc.html#4198" class="Function Operator"
      >:=</a
      ><a name="4405"
      > </a
      ><a name="4406" href="Stlc.html#4322" class="Bound"
      >V</a
      ><a name="4407"
      > </a
      ><a name="4408" href="Stlc.html#4198" class="Function Operator"
      >]</a
      ><a name="4409" class="Symbol"
      >)</a
      ><a name="4410"
      >
</a
      ><a name="4411" class="Symbol"
      >(</a
      ><a name="4412" href="Stlc.html#4412" class="Bound"
      >L&#8242;</a
      ><a name="4414"
      > </a
      ><a name="4415" href="Stlc.html#3679" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="4416"
      > </a
      ><a name="4417" href="Stlc.html#4417" class="Bound"
      >M&#8242;</a
      ><a name="4419" class="Symbol"
      >)</a
      ><a name="4420"
      > </a
      ><a name="4421" href="Stlc.html#4198" class="Function Operator"
      >[</a
      ><a name="4422"
      > </a
      ><a name="4423" href="Stlc.html#4423" class="Bound"
      >x</a
      ><a name="4424"
      > </a
      ><a name="4425" href="Stlc.html#4198" class="Function Operator"
      >:=</a
      ><a name="4427"
      > </a
      ><a name="4428" href="Stlc.html#4428" class="Bound"
      >V</a
      ><a name="4429"
      > </a
      ><a name="4430" href="Stlc.html#4198" class="Function Operator"
      >]</a
      ><a name="4431"
      > </a
      ><a name="4432" class="Symbol"
      >=</a
      ><a name="4433"
      >  </a
      ><a name="4435" class="Symbol"
      >(</a
      ><a name="4436" href="Stlc.html#4412" class="Bound"
      >L&#8242;</a
      ><a name="4438"
      > </a
      ><a name="4439" href="Stlc.html#4198" class="Function Operator"
      >[</a
      ><a name="4440"
      > </a
      ><a name="4441" href="Stlc.html#4423" class="Bound"
      >x</a
      ><a name="4442"
      > </a
      ><a name="4443" href="Stlc.html#4198" class="Function Operator"
      >:=</a
      ><a name="4445"
      > </a
      ><a name="4446" href="Stlc.html#4428" class="Bound"
      >V</a
      ><a name="4447"
      > </a
      ><a name="4448" href="Stlc.html#4198" class="Function Operator"
      >]</a
      ><a name="4449" class="Symbol"
      >)</a
      ><a name="4450"
      > </a
      ><a name="4451" href="Stlc.html#3679" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="4452"
      > </a
      ><a name="4453" class="Symbol"
      >(</a
      ><a name="4454" href="Stlc.html#4417" class="Bound"
      >M&#8242;</a
      ><a name="4456"
      > </a
      ><a name="4457" href="Stlc.html#4198" class="Function Operator"
      >[</a
      ><a name="4458"
      > </a
      ><a name="4459" href="Stlc.html#4423" class="Bound"
      >x</a
      ><a name="4460"
      > </a
      ><a name="4461" href="Stlc.html#4198" class="Function Operator"
      >:=</a
      ><a name="4463"
      > </a
      ><a name="4464" href="Stlc.html#4428" class="Bound"
      >V</a
      ><a name="4465"
      > </a
      ><a name="4466" href="Stlc.html#4198" class="Function Operator"
      >]</a
      ><a name="4467" class="Symbol"
      >)</a
      ><a name="4468"
      >
</a
      ><a name="4469" class="Symbol"
      >(</a
      ><a name="4470" href="Stlc.html#3706" class="InductiveConstructor"
      >true</a
      ><a name="4474" class="Symbol"
      >)</a
      ><a name="4475"
      > </a
      ><a name="4476" href="Stlc.html#4198" class="Function Operator"
      >[</a
      ><a name="4477"
      > </a
      ><a name="4478" href="Stlc.html#4478" class="Bound"
      >x</a
      ><a name="4479"
      > </a
      ><a name="4480" href="Stlc.html#4198" class="Function Operator"
      >:=</a
      ><a name="4482"
      > </a
      ><a name="4483" href="Stlc.html#4483" class="Bound"
      >V</a
      ><a name="4484"
      > </a
      ><a name="4485" href="Stlc.html#4198" class="Function Operator"
      >]</a
      ><a name="4486"
      > </a
      ><a name="4487" class="Symbol"
      >=</a
      ><a name="4488"
      > </a
      ><a name="4489" href="Stlc.html#3706" class="InductiveConstructor"
      >true</a
      ><a name="4493"
      >
</a
      ><a name="4494" class="Symbol"
      >(</a
      ><a name="4495" href="Stlc.html#3720" class="InductiveConstructor"
      >false</a
      ><a name="4500" class="Symbol"
      >)</a
      ><a name="4501"
      > </a
      ><a name="4502" href="Stlc.html#4198" class="Function Operator"
      >[</a
      ><a name="4503"
      > </a
      ><a name="4504" href="Stlc.html#4504" class="Bound"
      >x</a
      ><a name="4505"
      > </a
      ><a name="4506" href="Stlc.html#4198" class="Function Operator"
      >:=</a
      ><a name="4508"
      > </a
      ><a name="4509" href="Stlc.html#4509" class="Bound"
      >V</a
      ><a name="4510"
      > </a
      ><a name="4511" href="Stlc.html#4198" class="Function Operator"
      >]</a
      ><a name="4512"
      > </a
      ><a name="4513" class="Symbol"
      >=</a
      ><a name="4514"
      > </a
      ><a name="4515" href="Stlc.html#3720" class="InductiveConstructor"
      >false</a
      ><a name="4520"
      >
</a
      ><a name="4521" class="Symbol"
      >(</a
      ><a name="4522" href="Stlc.html#3735" class="InductiveConstructor Operator"
      >if</a
      ><a name="4524"
      > </a
      ><a name="4525" href="Stlc.html#4525" class="Bound"
      >L&#8242;</a
      ><a name="4527"
      > </a
      ><a name="4528" href="Stlc.html#3735" class="InductiveConstructor Operator"
      >then</a
      ><a name="4532"
      > </a
      ><a name="4533" href="Stlc.html#4533" class="Bound"
      >M&#8242;</a
      ><a name="4535"
      > </a
      ><a name="4536" href="Stlc.html#3735" class="InductiveConstructor Operator"
      >else</a
      ><a name="4540"
      > </a
      ><a name="4541" href="Stlc.html#4541" class="Bound"
      >N&#8242;</a
      ><a name="4543" class="Symbol"
      >)</a
      ><a name="4544"
      > </a
      ><a name="4545" href="Stlc.html#4198" class="Function Operator"
      >[</a
      ><a name="4546"
      > </a
      ><a name="4547" href="Stlc.html#4547" class="Bound"
      >x</a
      ><a name="4548"
      > </a
      ><a name="4549" href="Stlc.html#4198" class="Function Operator"
      >:=</a
      ><a name="4551"
      > </a
      ><a name="4552" href="Stlc.html#4552" class="Bound"
      >V</a
      ><a name="4553"
      > </a
      ><a name="4554" href="Stlc.html#4198" class="Function Operator"
      >]</a
      ><a name="4555"
      > </a
      ><a name="4556" class="Symbol"
      >=</a
      ><a name="4557"
      > </a
      ><a name="4558" href="Stlc.html#3735" class="InductiveConstructor Operator"
      >if</a
      ><a name="4560"
      > </a
      ><a name="4561" class="Symbol"
      >(</a
      ><a name="4562" href="Stlc.html#4525" class="Bound"
      >L&#8242;</a
      ><a name="4564"
      > </a
      ><a name="4565" href="Stlc.html#4198" class="Function Operator"
      >[</a
      ><a name="4566"
      > </a
      ><a name="4567" href="Stlc.html#4547" class="Bound"
      >x</a
      ><a name="4568"
      > </a
      ><a name="4569" href="Stlc.html#4198" class="Function Operator"
      >:=</a
      ><a name="4571"
      > </a
      ><a name="4572" href="Stlc.html#4552" class="Bound"
      >V</a
      ><a name="4573"
      > </a
      ><a name="4574" href="Stlc.html#4198" class="Function Operator"
      >]</a
      ><a name="4575" class="Symbol"
      >)</a
      ><a name="4576"
      > </a
      ><a name="4577" href="Stlc.html#3735" class="InductiveConstructor Operator"
      >then</a
      ><a name="4581"
      > </a
      ><a name="4582" class="Symbol"
      >(</a
      ><a name="4583" href="Stlc.html#4533" class="Bound"
      >M&#8242;</a
      ><a name="4585"
      > </a
      ><a name="4586" href="Stlc.html#4198" class="Function Operator"
      >[</a
      ><a name="4587"
      > </a
      ><a name="4588" href="Stlc.html#4547" class="Bound"
      >x</a
      ><a name="4589"
      > </a
      ><a name="4590" href="Stlc.html#4198" class="Function Operator"
      >:=</a
      ><a name="4592"
      > </a
      ><a name="4593" href="Stlc.html#4552" class="Bound"
      >V</a
      ><a name="4594"
      > </a
      ><a name="4595" href="Stlc.html#4198" class="Function Operator"
      >]</a
      ><a name="4596" class="Symbol"
      >)</a
      ><a name="4597"
      > </a
      ><a name="4598" href="Stlc.html#3735" class="InductiveConstructor Operator"
      >else</a
      ><a name="4602"
      > </a
      ><a name="4603" class="Symbol"
      >(</a
      ><a name="4604" href="Stlc.html#4541" class="Bound"
      >N&#8242;</a
      ><a name="4606"
      > </a
      ><a name="4607" href="Stlc.html#4198" class="Function Operator"
      >[</a
      ><a name="4608"
      > </a
      ><a name="4609" href="Stlc.html#4547" class="Bound"
      >x</a
      ><a name="4610"
      > </a
      ><a name="4611" href="Stlc.html#4198" class="Function Operator"
      >:=</a
      ><a name="4613"
      > </a
      ><a name="4614" href="Stlc.html#4552" class="Bound"
      >V</a
      ><a name="4615"
      > </a
      ><a name="4616" href="Stlc.html#4198" class="Function Operator"
      >]</a
      ><a name="4617" class="Symbol"
      >)</a
      >

</pre>

## Reduction rules

<pre class="Agda">

<a name="4664" class="Keyword"
      >infix</a
      ><a name="4669"
      > </a
      ><a name="4670" class="Number"
      >10</a
      ><a name="4672"
      > </a
      ><a name="4673" href="Stlc.html#4684" class="Datatype Operator"
      >_&#10233;_</a
      ><a name="4676"
      > 

</a
      ><a name="4679" class="Keyword"
      >data</a
      ><a name="4683"
      > </a
      ><a name="4684" href="Stlc.html#4684" class="Datatype Operator"
      >_&#10233;_</a
      ><a name="4687"
      > </a
      ><a name="4688" class="Symbol"
      >:</a
      ><a name="4689"
      > </a
      ><a name="4690" href="Stlc.html#3608" class="Datatype"
      >Term</a
      ><a name="4694"
      > </a
      ><a name="4695" class="Symbol"
      >&#8594;</a
      ><a name="4696"
      > </a
      ><a name="4697" href="Stlc.html#3608" class="Datatype"
      >Term</a
      ><a name="4701"
      > </a
      ><a name="4702" class="Symbol"
      >&#8594;</a
      ><a name="4703"
      > </a
      ><a name="4704" class="PrimitiveType"
      >Set</a
      ><a name="4707"
      > </a
      ><a name="4708" class="Keyword"
      >where</a
      ><a name="4713"
      >
  </a
      ><a name="4716" href="Stlc.html#4716" class="InductiveConstructor"
      >&#946;&#955;&#183;</a
      ><a name="4719"
      > </a
      ><a name="4720" class="Symbol"
      >:</a
      ><a name="4721"
      > </a
      ><a name="4722" class="Symbol"
      >&#8704;</a
      ><a name="4723"
      > </a
      ><a name="4724" class="Symbol"
      >{</a
      ><a name="4725" href="Stlc.html#4725" class="Bound"
      >x</a
      ><a name="4726"
      > </a
      ><a name="4727" href="Stlc.html#4727" class="Bound"
      >A</a
      ><a name="4728"
      > </a
      ><a name="4729" href="Stlc.html#4729" class="Bound"
      >N</a
      ><a name="4730"
      > </a
      ><a name="4731" href="Stlc.html#4731" class="Bound"
      >V</a
      ><a name="4732" class="Symbol"
      >}</a
      ><a name="4733"
      > </a
      ><a name="4734" class="Symbol"
      >&#8594;</a
      ><a name="4735"
      > </a
      ><a name="4736" href="Stlc.html#4027" class="Datatype"
      >Value</a
      ><a name="4741"
      > </a
      ><a name="4742" href="Stlc.html#4731" class="Bound"
      >V</a
      ><a name="4743"
      > </a
      ><a name="4744" class="Symbol"
      >&#8594;</a
      ><a name="4745"
      >
    </a
      ><a name="4750" class="Symbol"
      >(</a
      ><a name="4751" href="Stlc.html#3643" class="InductiveConstructor Operator"
      >&#955;[</a
      ><a name="4753"
      > </a
      ><a name="4754" href="Stlc.html#4725" class="Bound"
      >x</a
      ><a name="4755"
      > </a
      ><a name="4756" href="Stlc.html#3643" class="InductiveConstructor Operator"
      >&#8758;</a
      ><a name="4757"
      > </a
      ><a name="4758" href="Stlc.html#4727" class="Bound"
      >A</a
      ><a name="4759"
      > </a
      ><a name="4760" href="Stlc.html#3643" class="InductiveConstructor Operator"
      >]</a
      ><a name="4761"
      > </a
      ><a name="4762" href="Stlc.html#4729" class="Bound"
      >N</a
      ><a name="4763" class="Symbol"
      >)</a
      ><a name="4764"
      > </a
      ><a name="4765" href="Stlc.html#3679" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="4766"
      > </a
      ><a name="4767" href="Stlc.html#4731" class="Bound"
      >V</a
      ><a name="4768"
      > </a
      ><a name="4769" href="Stlc.html#4684" class="Datatype Operator"
      >&#10233;</a
      ><a name="4770"
      > </a
      ><a name="4771" href="Stlc.html#4729" class="Bound"
      >N</a
      ><a name="4772"
      > </a
      ><a name="4773" href="Stlc.html#4198" class="Function Operator"
      >[</a
      ><a name="4774"
      > </a
      ><a name="4775" href="Stlc.html#4725" class="Bound"
      >x</a
      ><a name="4776"
      > </a
      ><a name="4777" href="Stlc.html#4198" class="Function Operator"
      >:=</a
      ><a name="4779"
      > </a
      ><a name="4780" href="Stlc.html#4731" class="Bound"
      >V</a
      ><a name="4781"
      > </a
      ><a name="4782" href="Stlc.html#4198" class="Function Operator"
      >]</a
      ><a name="4783"
      >
  </a
      ><a name="4786" href="Stlc.html#4786" class="InductiveConstructor"
      >&#958;&#183;&#8321;</a
      ><a name="4789"
      > </a
      ><a name="4790" class="Symbol"
      >:</a
      ><a name="4791"
      > </a
      ><a name="4792" class="Symbol"
      >&#8704;</a
      ><a name="4793"
      > </a
      ><a name="4794" class="Symbol"
      >{</a
      ><a name="4795" href="Stlc.html#4795" class="Bound"
      >L</a
      ><a name="4796"
      > </a
      ><a name="4797" href="Stlc.html#4797" class="Bound"
      >L&#8242;</a
      ><a name="4799"
      > </a
      ><a name="4800" href="Stlc.html#4800" class="Bound"
      >M</a
      ><a name="4801" class="Symbol"
      >}</a
      ><a name="4802"
      > </a
      ><a name="4803" class="Symbol"
      >&#8594;</a
      ><a name="4804"
      >
    </a
      ><a name="4809" href="Stlc.html#4795" class="Bound"
      >L</a
      ><a name="4810"
      > </a
      ><a name="4811" href="Stlc.html#4684" class="Datatype Operator"
      >&#10233;</a
      ><a name="4812"
      > </a
      ><a name="4813" href="Stlc.html#4797" class="Bound"
      >L&#8242;</a
      ><a name="4815"
      > </a
      ><a name="4816" class="Symbol"
      >&#8594;</a
      ><a name="4817"
      >
    </a
      ><a name="4822" href="Stlc.html#4795" class="Bound"
      >L</a
      ><a name="4823"
      > </a
      ><a name="4824" href="Stlc.html#3679" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="4825"
      > </a
      ><a name="4826" href="Stlc.html#4800" class="Bound"
      >M</a
      ><a name="4827"
      > </a
      ><a name="4828" href="Stlc.html#4684" class="Datatype Operator"
      >&#10233;</a
      ><a name="4829"
      > </a
      ><a name="4830" href="Stlc.html#4797" class="Bound"
      >L&#8242;</a
      ><a name="4832"
      > </a
      ><a name="4833" href="Stlc.html#3679" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="4834"
      > </a
      ><a name="4835" href="Stlc.html#4800" class="Bound"
      >M</a
      ><a name="4836"
      >
  </a
      ><a name="4839" href="Stlc.html#4839" class="InductiveConstructor"
      >&#958;&#183;&#8322;</a
      ><a name="4842"
      > </a
      ><a name="4843" class="Symbol"
      >:</a
      ><a name="4844"
      > </a
      ><a name="4845" class="Symbol"
      >&#8704;</a
      ><a name="4846"
      > </a
      ><a name="4847" class="Symbol"
      >{</a
      ><a name="4848" href="Stlc.html#4848" class="Bound"
      >V</a
      ><a name="4849"
      > </a
      ><a name="4850" href="Stlc.html#4850" class="Bound"
      >M</a
      ><a name="4851"
      > </a
      ><a name="4852" href="Stlc.html#4852" class="Bound"
      >M&#8242;</a
      ><a name="4854" class="Symbol"
      >}</a
      ><a name="4855"
      > </a
      ><a name="4856" class="Symbol"
      >&#8594;</a
      ><a name="4857"
      >
    </a
      ><a name="4862" href="Stlc.html#4027" class="Datatype"
      >Value</a
      ><a name="4867"
      > </a
      ><a name="4868" href="Stlc.html#4848" class="Bound"
      >V</a
      ><a name="4869"
      > </a
      ><a name="4870" class="Symbol"
      >&#8594;</a
      ><a name="4871"
      >
    </a
      ><a name="4876" href="Stlc.html#4850" class="Bound"
      >M</a
      ><a name="4877"
      > </a
      ><a name="4878" href="Stlc.html#4684" class="Datatype Operator"
      >&#10233;</a
      ><a name="4879"
      > </a
      ><a name="4880" href="Stlc.html#4852" class="Bound"
      >M&#8242;</a
      ><a name="4882"
      > </a
      ><a name="4883" class="Symbol"
      >&#8594;</a
      ><a name="4884"
      >
    </a
      ><a name="4889" href="Stlc.html#4848" class="Bound"
      >V</a
      ><a name="4890"
      > </a
      ><a name="4891" href="Stlc.html#3679" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="4892"
      > </a
      ><a name="4893" href="Stlc.html#4850" class="Bound"
      >M</a
      ><a name="4894"
      > </a
      ><a name="4895" href="Stlc.html#4684" class="Datatype Operator"
      >&#10233;</a
      ><a name="4896"
      > </a
      ><a name="4897" href="Stlc.html#4848" class="Bound"
      >V</a
      ><a name="4898"
      > </a
      ><a name="4899" href="Stlc.html#3679" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="4900"
      > </a
      ><a name="4901" href="Stlc.html#4852" class="Bound"
      >M&#8242;</a
      ><a name="4903"
      >
  </a
      ><a name="4906" href="Stlc.html#4906" class="InductiveConstructor"
      >&#946;if-true</a
      ><a name="4914"
      > </a
      ><a name="4915" class="Symbol"
      >:</a
      ><a name="4916"
      > </a
      ><a name="4917" class="Symbol"
      >&#8704;</a
      ><a name="4918"
      > </a
      ><a name="4919" class="Symbol"
      >{</a
      ><a name="4920" href="Stlc.html#4920" class="Bound"
      >M</a
      ><a name="4921"
      > </a
      ><a name="4922" href="Stlc.html#4922" class="Bound"
      >N</a
      ><a name="4923" class="Symbol"
      >}</a
      ><a name="4924"
      > </a
      ><a name="4925" class="Symbol"
      >&#8594;</a
      ><a name="4926"
      >
    </a
      ><a name="4931" href="Stlc.html#3735" class="InductiveConstructor Operator"
      >if</a
      ><a name="4933"
      > </a
      ><a name="4934" href="Stlc.html#3706" class="InductiveConstructor"
      >true</a
      ><a name="4938"
      > </a
      ><a name="4939" href="Stlc.html#3735" class="InductiveConstructor Operator"
      >then</a
      ><a name="4943"
      > </a
      ><a name="4944" href="Stlc.html#4920" class="Bound"
      >M</a
      ><a name="4945"
      > </a
      ><a name="4946" href="Stlc.html#3735" class="InductiveConstructor Operator"
      >else</a
      ><a name="4950"
      > </a
      ><a name="4951" href="Stlc.html#4922" class="Bound"
      >N</a
      ><a name="4952"
      > </a
      ><a name="4953" href="Stlc.html#4684" class="Datatype Operator"
      >&#10233;</a
      ><a name="4954"
      > </a
      ><a name="4955" href="Stlc.html#4920" class="Bound"
      >M</a
      ><a name="4956"
      >
  </a
      ><a name="4959" href="Stlc.html#4959" class="InductiveConstructor"
      >&#946;if-false</a
      ><a name="4968"
      > </a
      ><a name="4969" class="Symbol"
      >:</a
      ><a name="4970"
      > </a
      ><a name="4971" class="Symbol"
      >&#8704;</a
      ><a name="4972"
      > </a
      ><a name="4973" class="Symbol"
      >{</a
      ><a name="4974" href="Stlc.html#4974" class="Bound"
      >M</a
      ><a name="4975"
      > </a
      ><a name="4976" href="Stlc.html#4976" class="Bound"
      >N</a
      ><a name="4977" class="Symbol"
      >}</a
      ><a name="4978"
      > </a
      ><a name="4979" class="Symbol"
      >&#8594;</a
      ><a name="4980"
      >
    </a
      ><a name="4985" href="Stlc.html#3735" class="InductiveConstructor Operator"
      >if</a
      ><a name="4987"
      > </a
      ><a name="4988" href="Stlc.html#3720" class="InductiveConstructor"
      >false</a
      ><a name="4993"
      > </a
      ><a name="4994" href="Stlc.html#3735" class="InductiveConstructor Operator"
      >then</a
      ><a name="4998"
      > </a
      ><a name="4999" href="Stlc.html#4974" class="Bound"
      >M</a
      ><a name="5000"
      > </a
      ><a name="5001" href="Stlc.html#3735" class="InductiveConstructor Operator"
      >else</a
      ><a name="5005"
      > </a
      ><a name="5006" href="Stlc.html#4976" class="Bound"
      >N</a
      ><a name="5007"
      > </a
      ><a name="5008" href="Stlc.html#4684" class="Datatype Operator"
      >&#10233;</a
      ><a name="5009"
      > </a
      ><a name="5010" href="Stlc.html#4976" class="Bound"
      >N</a
      ><a name="5011"
      >
  </a
      ><a name="5014" href="Stlc.html#5014" class="InductiveConstructor"
      >&#958;if</a
      ><a name="5017"
      > </a
      ><a name="5018" class="Symbol"
      >:</a
      ><a name="5019"
      > </a
      ><a name="5020" class="Symbol"
      >&#8704;</a
      ><a name="5021"
      > </a
      ><a name="5022" class="Symbol"
      >{</a
      ><a name="5023" href="Stlc.html#5023" class="Bound"
      >L</a
      ><a name="5024"
      > </a
      ><a name="5025" href="Stlc.html#5025" class="Bound"
      >L&#8242;</a
      ><a name="5027"
      > </a
      ><a name="5028" href="Stlc.html#5028" class="Bound"
      >M</a
      ><a name="5029"
      > </a
      ><a name="5030" href="Stlc.html#5030" class="Bound"
      >N</a
      ><a name="5031" class="Symbol"
      >}</a
      ><a name="5032"
      > </a
      ><a name="5033" class="Symbol"
      >&#8594;</a
      ><a name="5034"
      >
    </a
      ><a name="5039" href="Stlc.html#5023" class="Bound"
      >L</a
      ><a name="5040"
      > </a
      ><a name="5041" href="Stlc.html#4684" class="Datatype Operator"
      >&#10233;</a
      ><a name="5042"
      > </a
      ><a name="5043" href="Stlc.html#5025" class="Bound"
      >L&#8242;</a
      ><a name="5045"
      > </a
      ><a name="5046" class="Symbol"
      >&#8594;</a
      ><a name="5047"
      >    
    </a
      ><a name="5056" href="Stlc.html#3735" class="InductiveConstructor Operator"
      >if</a
      ><a name="5058"
      > </a
      ><a name="5059" href="Stlc.html#5023" class="Bound"
      >L</a
      ><a name="5060"
      > </a
      ><a name="5061" href="Stlc.html#3735" class="InductiveConstructor Operator"
      >then</a
      ><a name="5065"
      > </a
      ><a name="5066" href="Stlc.html#5028" class="Bound"
      >M</a
      ><a name="5067"
      > </a
      ><a name="5068" href="Stlc.html#3735" class="InductiveConstructor Operator"
      >else</a
      ><a name="5072"
      > </a
      ><a name="5073" href="Stlc.html#5030" class="Bound"
      >N</a
      ><a name="5074"
      > </a
      ><a name="5075" href="Stlc.html#4684" class="Datatype Operator"
      >&#10233;</a
      ><a name="5076"
      > </a
      ><a name="5077" href="Stlc.html#3735" class="InductiveConstructor Operator"
      >if</a
      ><a name="5079"
      > </a
      ><a name="5080" href="Stlc.html#5025" class="Bound"
      >L&#8242;</a
      ><a name="5082"
      > </a
      ><a name="5083" href="Stlc.html#3735" class="InductiveConstructor Operator"
      >then</a
      ><a name="5087"
      > </a
      ><a name="5088" href="Stlc.html#5028" class="Bound"
      >M</a
      ><a name="5089"
      > </a
      ><a name="5090" href="Stlc.html#3735" class="InductiveConstructor Operator"
      >else</a
      ><a name="5094"
      > </a
      ><a name="5095" href="Stlc.html#5030" class="Bound"
      >N</a
      >

</pre>

## Reflexive and transitive closure


<pre class="Agda">

<a name="5160" class="Keyword"
      >infix</a
      ><a name="5165"
      > </a
      ><a name="5166" class="Number"
      >10</a
      ><a name="5168"
      > </a
      ><a name="5169" href="Stlc.html#5209" class="Datatype Operator"
      >_&#10233;*_</a
      ><a name="5173"
      > 
</a
      ><a name="5175" class="Keyword"
      >infixr</a
      ><a name="5181"
      > </a
      ><a name="5182" class="Number"
      >2</a
      ><a name="5183"
      > </a
      ><a name="5184" href="Stlc.html#5262" class="InductiveConstructor Operator"
      >_&#10233;&#10216;_&#10217;_</a
      ><a name="5190"
      >
</a
      ><a name="5191" class="Keyword"
      >infix</a
      ><a name="5196"
      >  </a
      ><a name="5198" class="Number"
      >3</a
      ><a name="5199"
      > </a
      ><a name="5200" href="Stlc.html#5242" class="InductiveConstructor Operator"
      >_&#8718;</a
      ><a name="5202"
      >

</a
      ><a name="5204" class="Keyword"
      >data</a
      ><a name="5208"
      > </a
      ><a name="5209" href="Stlc.html#5209" class="Datatype Operator"
      >_&#10233;*_</a
      ><a name="5213"
      > </a
      ><a name="5214" class="Symbol"
      >:</a
      ><a name="5215"
      > </a
      ><a name="5216" href="Stlc.html#3608" class="Datatype"
      >Term</a
      ><a name="5220"
      > </a
      ><a name="5221" class="Symbol"
      >&#8594;</a
      ><a name="5222"
      > </a
      ><a name="5223" href="Stlc.html#3608" class="Datatype"
      >Term</a
      ><a name="5227"
      > </a
      ><a name="5228" class="Symbol"
      >&#8594;</a
      ><a name="5229"
      > </a
      ><a name="5230" class="PrimitiveType"
      >Set</a
      ><a name="5233"
      > </a
      ><a name="5234" class="Keyword"
      >where</a
      ><a name="5239"
      >
  </a
      ><a name="5242" href="Stlc.html#5242" class="InductiveConstructor Operator"
      >_&#8718;</a
      ><a name="5244"
      > </a
      ><a name="5245" class="Symbol"
      >:</a
      ><a name="5246"
      > </a
      ><a name="5247" class="Symbol"
      >&#8704;</a
      ><a name="5248"
      > </a
      ><a name="5249" href="Stlc.html#5249" class="Bound"
      >M</a
      ><a name="5250"
      > </a
      ><a name="5251" class="Symbol"
      >&#8594;</a
      ><a name="5252"
      > </a
      ><a name="5253" href="Stlc.html#5249" class="Bound"
      >M</a
      ><a name="5254"
      > </a
      ><a name="5255" href="Stlc.html#5209" class="Datatype Operator"
      >&#10233;*</a
      ><a name="5257"
      > </a
      ><a name="5258" href="Stlc.html#5249" class="Bound"
      >M</a
      ><a name="5259"
      >
  </a
      ><a name="5262" href="Stlc.html#5262" class="InductiveConstructor Operator"
      >_&#10233;&#10216;_&#10217;_</a
      ><a name="5268"
      > </a
      ><a name="5269" class="Symbol"
      >:</a
      ><a name="5270"
      > </a
      ><a name="5271" class="Symbol"
      >&#8704;</a
      ><a name="5272"
      > </a
      ><a name="5273" href="Stlc.html#5273" class="Bound"
      >L</a
      ><a name="5274"
      > </a
      ><a name="5275" class="Symbol"
      >{</a
      ><a name="5276" href="Stlc.html#5276" class="Bound"
      >M</a
      ><a name="5277"
      > </a
      ><a name="5278" href="Stlc.html#5278" class="Bound"
      >N</a
      ><a name="5279" class="Symbol"
      >}</a
      ><a name="5280"
      > </a
      ><a name="5281" class="Symbol"
      >&#8594;</a
      ><a name="5282"
      > </a
      ><a name="5283" href="Stlc.html#5273" class="Bound"
      >L</a
      ><a name="5284"
      > </a
      ><a name="5285" href="Stlc.html#4684" class="Datatype Operator"
      >&#10233;</a
      ><a name="5286"
      > </a
      ><a name="5287" href="Stlc.html#5276" class="Bound"
      >M</a
      ><a name="5288"
      > </a
      ><a name="5289" class="Symbol"
      >&#8594;</a
      ><a name="5290"
      > </a
      ><a name="5291" href="Stlc.html#5276" class="Bound"
      >M</a
      ><a name="5292"
      > </a
      ><a name="5293" href="Stlc.html#5209" class="Datatype Operator"
      >&#10233;*</a
      ><a name="5295"
      > </a
      ><a name="5296" href="Stlc.html#5278" class="Bound"
      >N</a
      ><a name="5297"
      > </a
      ><a name="5298" class="Symbol"
      >&#8594;</a
      ><a name="5299"
      > </a
      ><a name="5300" href="Stlc.html#5273" class="Bound"
      >L</a
      ><a name="5301"
      > </a
      ><a name="5302" href="Stlc.html#5209" class="Datatype Operator"
      >&#10233;*</a
      ><a name="5304"
      > </a
      ><a name="5305" href="Stlc.html#5278" class="Bound"
      >N</a
      ><a name="5306"
      >  

</a
      ><a name="5310" href="Stlc.html#5310" class="Function"
      >reduction&#8321;</a
      ><a name="5320"
      > </a
      ><a name="5321" class="Symbol"
      >:</a
      ><a name="5322"
      > </a
      ><a name="5323" href="Stlc.html#3871" class="Function"
      >not</a
      ><a name="5326"
      > </a
      ><a name="5327" href="Stlc.html#3679" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="5328"
      > </a
      ><a name="5329" href="Stlc.html#3706" class="InductiveConstructor"
      >true</a
      ><a name="5333"
      > </a
      ><a name="5334" href="Stlc.html#5209" class="Datatype Operator"
      >&#10233;*</a
      ><a name="5336"
      > </a
      ><a name="5337" href="Stlc.html#3720" class="InductiveConstructor"
      >false</a
      ><a name="5342"
      >
</a
      ><a name="5343" href="Stlc.html#5310" class="Function"
      >reduction&#8321;</a
      ><a name="5353"
      > </a
      ><a name="5354" class="Symbol"
      >=</a
      ><a name="5355"
      >
    </a
      ><a name="5360" href="Stlc.html#3871" class="Function"
      >not</a
      ><a name="5363"
      > </a
      ><a name="5364" href="Stlc.html#3679" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="5365"
      > </a
      ><a name="5366" href="Stlc.html#3706" class="InductiveConstructor"
      >true</a
      ><a name="5370"
      >
  </a
      ><a name="5373" href="Stlc.html#5262" class="InductiveConstructor Operator"
      >&#10233;&#10216;</a
      ><a name="5375"
      > </a
      ><a name="5376" href="Stlc.html#4716" class="InductiveConstructor"
      >&#946;&#955;&#183;</a
      ><a name="5379"
      > </a
      ><a name="5380" href="Stlc.html#4103" class="InductiveConstructor"
      >value-true</a
      ><a name="5390"
      > </a
      ><a name="5391" href="Stlc.html#5262" class="InductiveConstructor Operator"
      >&#10217;</a
      ><a name="5392"
      >
    </a
      ><a name="5397" href="Stlc.html#3735" class="InductiveConstructor Operator"
      >if</a
      ><a name="5399"
      > </a
      ><a name="5400" href="Stlc.html#3706" class="InductiveConstructor"
      >true</a
      ><a name="5404"
      > </a
      ><a name="5405" href="Stlc.html#3735" class="InductiveConstructor Operator"
      >then</a
      ><a name="5409"
      > </a
      ><a name="5410" href="Stlc.html#3720" class="InductiveConstructor"
      >false</a
      ><a name="5415"
      > </a
      ><a name="5416" href="Stlc.html#3735" class="InductiveConstructor Operator"
      >else</a
      ><a name="5420"
      > </a
      ><a name="5421" href="Stlc.html#3706" class="InductiveConstructor"
      >true</a
      ><a name="5425"
      >
  </a
      ><a name="5428" href="Stlc.html#5262" class="InductiveConstructor Operator"
      >&#10233;&#10216;</a
      ><a name="5430"
      > </a
      ><a name="5431" href="Stlc.html#4906" class="InductiveConstructor"
      >&#946;if-true</a
      ><a name="5439"
      > </a
      ><a name="5440" href="Stlc.html#5262" class="InductiveConstructor Operator"
      >&#10217;</a
      ><a name="5441"
      >
    </a
      ><a name="5446" href="Stlc.html#3720" class="InductiveConstructor"
      >false</a
      ><a name="5451"
      >
  </a
      ><a name="5454" href="Stlc.html#5242" class="InductiveConstructor Operator"
      >&#8718;</a
      ><a name="5455"
      >

</a
      ><a name="5457" href="Stlc.html#5457" class="Function"
      >reduction&#8322;</a
      ><a name="5467"
      > </a
      ><a name="5468" class="Symbol"
      >:</a
      ><a name="5469"
      > </a
      ><a name="5470" href="Stlc.html#3875" class="Function"
      >two</a
      ><a name="5473"
      > </a
      ><a name="5474" href="Stlc.html#3679" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="5475"
      > </a
      ><a name="5476" href="Stlc.html#3871" class="Function"
      >not</a
      ><a name="5479"
      > </a
      ><a name="5480" href="Stlc.html#3679" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="5481"
      > </a
      ><a name="5482" href="Stlc.html#3706" class="InductiveConstructor"
      >true</a
      ><a name="5486"
      > </a
      ><a name="5487" href="Stlc.html#5209" class="Datatype Operator"
      >&#10233;*</a
      ><a name="5489"
      > </a
      ><a name="5490" href="Stlc.html#3706" class="InductiveConstructor"
      >true</a
      ><a name="5494"
      >
</a
      ><a name="5495" href="Stlc.html#5457" class="Function"
      >reduction&#8322;</a
      ><a name="5505"
      > </a
      ><a name="5506" class="Symbol"
      >=</a
      ><a name="5507"
      >
    </a
      ><a name="5512" href="Stlc.html#3875" class="Function"
      >two</a
      ><a name="5515"
      > </a
      ><a name="5516" href="Stlc.html#3679" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="5517"
      > </a
      ><a name="5518" href="Stlc.html#3871" class="Function"
      >not</a
      ><a name="5521"
      > </a
      ><a name="5522" href="Stlc.html#3679" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="5523"
      > </a
      ><a name="5524" href="Stlc.html#3706" class="InductiveConstructor"
      >true</a
      ><a name="5528"
      >
  </a
      ><a name="5531" href="Stlc.html#5262" class="InductiveConstructor Operator"
      >&#10233;&#10216;</a
      ><a name="5533"
      > </a
      ><a name="5534" href="Stlc.html#4786" class="InductiveConstructor"
      >&#958;&#183;&#8321;</a
      ><a name="5537"
      > </a
      ><a name="5538" class="Symbol"
      >(</a
      ><a name="5539" href="Stlc.html#4716" class="InductiveConstructor"
      >&#946;&#955;&#183;</a
      ><a name="5542"
      > </a
      ><a name="5543" href="Stlc.html#4054" class="InductiveConstructor"
      >value-&#955;</a
      ><a name="5550" class="Symbol"
      >)</a
      ><a name="5551"
      > </a
      ><a name="5552" href="Stlc.html#5262" class="InductiveConstructor Operator"
      >&#10217;</a
      ><a name="5553"
      >
    </a
      ><a name="5558" class="Symbol"
      >(</a
      ><a name="5559" href="Stlc.html#3643" class="InductiveConstructor Operator"
      >&#955;[</a
      ><a name="5561"
      > </a
      ><a name="5562" href="Stlc.html#3841" class="Function"
      >x</a
      ><a name="5563"
      > </a
      ><a name="5564" href="Stlc.html#3643" class="InductiveConstructor Operator"
      >&#8758;</a
      ><a name="5565"
      > </a
      ><a name="5566" href="Stlc.html#2581" class="InductiveConstructor"
      >&#120121;</a
      ><a name="5567"
      > </a
      ><a name="5568" href="Stlc.html#3643" class="InductiveConstructor Operator"
      >]</a
      ><a name="5569"
      > </a
      ><a name="5570" href="Stlc.html#3871" class="Function"
      >not</a
      ><a name="5573"
      > </a
      ><a name="5574" href="Stlc.html#3679" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="5575"
      > </a
      ><a name="5576" class="Symbol"
      >(</a
      ><a name="5577" href="Stlc.html#3871" class="Function"
      >not</a
      ><a name="5580"
      > </a
      ><a name="5581" href="Stlc.html#3679" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="5582"
      > </a
      ><a name="5583" href="Stlc.html#3627" class="InductiveConstructor"
      >`</a
      ><a name="5584"
      > </a
      ><a name="5585" href="Stlc.html#3841" class="Function"
      >x</a
      ><a name="5586" class="Symbol"
      >))</a
      ><a name="5588"
      > </a
      ><a name="5589" href="Stlc.html#3679" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="5590"
      > </a
      ><a name="5591" href="Stlc.html#3706" class="InductiveConstructor"
      >true</a
      ><a name="5595"
      >
  </a
      ><a name="5598" href="Stlc.html#5262" class="InductiveConstructor Operator"
      >&#10233;&#10216;</a
      ><a name="5600"
      > </a
      ><a name="5601" href="Stlc.html#4716" class="InductiveConstructor"
      >&#946;&#955;&#183;</a
      ><a name="5604"
      > </a
      ><a name="5605" href="Stlc.html#4103" class="InductiveConstructor"
      >value-true</a
      ><a name="5615"
      > </a
      ><a name="5616" href="Stlc.html#5262" class="InductiveConstructor Operator"
      >&#10217;</a
      ><a name="5617"
      >
    </a
      ><a name="5622" href="Stlc.html#3871" class="Function"
      >not</a
      ><a name="5625"
      > </a
      ><a name="5626" href="Stlc.html#3679" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="5627"
      > </a
      ><a name="5628" class="Symbol"
      >(</a
      ><a name="5629" href="Stlc.html#3871" class="Function"
      >not</a
      ><a name="5632"
      > </a
      ><a name="5633" href="Stlc.html#3679" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="5634"
      > </a
      ><a name="5635" href="Stlc.html#3706" class="InductiveConstructor"
      >true</a
      ><a name="5639" class="Symbol"
      >)</a
      ><a name="5640"
      >
  </a
      ><a name="5643" href="Stlc.html#5262" class="InductiveConstructor Operator"
      >&#10233;&#10216;</a
      ><a name="5645"
      > </a
      ><a name="5646" href="Stlc.html#4839" class="InductiveConstructor"
      >&#958;&#183;&#8322;</a
      ><a name="5649"
      > </a
      ><a name="5650" href="Stlc.html#4054" class="InductiveConstructor"
      >value-&#955;</a
      ><a name="5657"
      > </a
      ><a name="5658" class="Symbol"
      >(</a
      ><a name="5659" href="Stlc.html#4716" class="InductiveConstructor"
      >&#946;&#955;&#183;</a
      ><a name="5662"
      > </a
      ><a name="5663" href="Stlc.html#4103" class="InductiveConstructor"
      >value-true</a
      ><a name="5673" class="Symbol"
      >)</a
      ><a name="5674"
      > </a
      ><a name="5675" href="Stlc.html#5262" class="InductiveConstructor Operator"
      >&#10217;</a
      ><a name="5676"
      >
    </a
      ><a name="5681" href="Stlc.html#3871" class="Function"
      >not</a
      ><a name="5684"
      > </a
      ><a name="5685" href="Stlc.html#3679" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="5686"
      > </a
      ><a name="5687" class="Symbol"
      >(</a
      ><a name="5688" href="Stlc.html#3735" class="InductiveConstructor Operator"
      >if</a
      ><a name="5690"
      > </a
      ><a name="5691" href="Stlc.html#3706" class="InductiveConstructor"
      >true</a
      ><a name="5695"
      > </a
      ><a name="5696" href="Stlc.html#3735" class="InductiveConstructor Operator"
      >then</a
      ><a name="5700"
      > </a
      ><a name="5701" href="Stlc.html#3720" class="InductiveConstructor"
      >false</a
      ><a name="5706"
      > </a
      ><a name="5707" href="Stlc.html#3735" class="InductiveConstructor Operator"
      >else</a
      ><a name="5711"
      > </a
      ><a name="5712" href="Stlc.html#3706" class="InductiveConstructor"
      >true</a
      ><a name="5716" class="Symbol"
      >)</a
      ><a name="5717"
      >
  </a
      ><a name="5720" href="Stlc.html#5262" class="InductiveConstructor Operator"
      >&#10233;&#10216;</a
      ><a name="5722"
      > </a
      ><a name="5723" href="Stlc.html#4839" class="InductiveConstructor"
      >&#958;&#183;&#8322;</a
      ><a name="5726"
      > </a
      ><a name="5727" href="Stlc.html#4054" class="InductiveConstructor"
      >value-&#955;</a
      ><a name="5734"
      > </a
      ><a name="5735" href="Stlc.html#4906" class="InductiveConstructor"
      >&#946;if-true</a
      ><a name="5743"
      >  </a
      ><a name="5745" href="Stlc.html#5262" class="InductiveConstructor Operator"
      >&#10217;</a
      ><a name="5746"
      >
    </a
      ><a name="5751" href="Stlc.html#3871" class="Function"
      >not</a
      ><a name="5754"
      > </a
      ><a name="5755" href="Stlc.html#3679" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="5756"
      > </a
      ><a name="5757" href="Stlc.html#3720" class="InductiveConstructor"
      >false</a
      ><a name="5762"
      >
  </a
      ><a name="5765" href="Stlc.html#5262" class="InductiveConstructor Operator"
      >&#10233;&#10216;</a
      ><a name="5767"
      > </a
      ><a name="5768" href="Stlc.html#4716" class="InductiveConstructor"
      >&#946;&#955;&#183;</a
      ><a name="5771"
      > </a
      ><a name="5772" href="Stlc.html#4130" class="InductiveConstructor"
      >value-false</a
      ><a name="5783"
      > </a
      ><a name="5784" href="Stlc.html#5262" class="InductiveConstructor Operator"
      >&#10217;</a
      ><a name="5785"
      >
    </a
      ><a name="5790" href="Stlc.html#3735" class="InductiveConstructor Operator"
      >if</a
      ><a name="5792"
      > </a
      ><a name="5793" href="Stlc.html#3720" class="InductiveConstructor"
      >false</a
      ><a name="5798"
      > </a
      ><a name="5799" href="Stlc.html#3735" class="InductiveConstructor Operator"
      >then</a
      ><a name="5803"
      > </a
      ><a name="5804" href="Stlc.html#3720" class="InductiveConstructor"
      >false</a
      ><a name="5809"
      > </a
      ><a name="5810" href="Stlc.html#3735" class="InductiveConstructor Operator"
      >else</a
      ><a name="5814"
      > </a
      ><a name="5815" href="Stlc.html#3706" class="InductiveConstructor"
      >true</a
      ><a name="5819"
      >
  </a
      ><a name="5822" href="Stlc.html#5262" class="InductiveConstructor Operator"
      >&#10233;&#10216;</a
      ><a name="5824"
      > </a
      ><a name="5825" href="Stlc.html#4959" class="InductiveConstructor"
      >&#946;if-false</a
      ><a name="5834"
      > </a
      ><a name="5835" href="Stlc.html#5262" class="InductiveConstructor Operator"
      >&#10217;</a
      ><a name="5836"
      >
    </a
      ><a name="5841" href="Stlc.html#3706" class="InductiveConstructor"
      >true</a
      ><a name="5845"
      >
  </a
      ><a name="5848" href="Stlc.html#5242" class="InductiveConstructor Operator"
      >&#8718;</a
      >

</pre>

Much of the above, though not all, can be filled in using C-c C-r and C-c C-s.



## Type rules

<pre class="Agda">

<a name="5972" href="Stlc.html#5972" class="Function"
      >Context</a
      ><a name="5979"
      > </a
      ><a name="5980" class="Symbol"
      >:</a
      ><a name="5981"
      > </a
      ><a name="5982" class="PrimitiveType"
      >Set</a
      ><a name="5985"
      >
</a
      ><a name="5986" href="Stlc.html#5972" class="Function"
      >Context</a
      ><a name="5993"
      > </a
      ><a name="5994" class="Symbol"
      >=</a
      ><a name="5995"
      > </a
      ><a name="5996" href="Maps.html#10132" class="Function"
      >PartialMap</a
      ><a name="6006"
      > </a
      ><a name="6007" href="Stlc.html#2535" class="Datatype"
      >Type</a
      ><a name="6011"
      >

</a
      ><a name="6013" class="Keyword"
      >infix</a
      ><a name="6018"
      > </a
      ><a name="6019" class="Number"
      >10</a
      ><a name="6021"
      > </a
      ><a name="6022" href="Stlc.html#6034" class="Datatype Operator"
      >_&#8866;_&#8758;_</a
      ><a name="6027"
      >

</a
      ><a name="6029" class="Keyword"
      >data</a
      ><a name="6033"
      > </a
      ><a name="6034" href="Stlc.html#6034" class="Datatype Operator"
      >_&#8866;_&#8758;_</a
      ><a name="6039"
      > </a
      ><a name="6040" class="Symbol"
      >:</a
      ><a name="6041"
      > </a
      ><a name="6042" href="Stlc.html#5972" class="Function"
      >Context</a
      ><a name="6049"
      > </a
      ><a name="6050" class="Symbol"
      >&#8594;</a
      ><a name="6051"
      > </a
      ><a name="6052" href="Stlc.html#3608" class="Datatype"
      >Term</a
      ><a name="6056"
      > </a
      ><a name="6057" class="Symbol"
      >&#8594;</a
      ><a name="6058"
      > </a
      ><a name="6059" href="Stlc.html#2535" class="Datatype"
      >Type</a
      ><a name="6063"
      > </a
      ><a name="6064" class="Symbol"
      >&#8594;</a
      ><a name="6065"
      > </a
      ><a name="6066" class="PrimitiveType"
      >Set</a
      ><a name="6069"
      > </a
      ><a name="6070" class="Keyword"
      >where</a
      ><a name="6075"
      >
  </a
      ><a name="6078" href="Stlc.html#6078" class="InductiveConstructor"
      >Ax</a
      ><a name="6080"
      > </a
      ><a name="6081" class="Symbol"
      >:</a
      ><a name="6082"
      > </a
      ><a name="6083" class="Symbol"
      >&#8704;</a
      ><a name="6084"
      > </a
      ><a name="6085" class="Symbol"
      >{</a
      ><a name="6086" href="Stlc.html#6086" class="Bound"
      >&#915;</a
      ><a name="6087"
      > </a
      ><a name="6088" href="Stlc.html#6088" class="Bound"
      >x</a
      ><a name="6089"
      > </a
      ><a name="6090" href="Stlc.html#6090" class="Bound"
      >A</a
      ><a name="6091" class="Symbol"
      >}</a
      ><a name="6092"
      > </a
      ><a name="6093" class="Symbol"
      >&#8594;</a
      ><a name="6094"
      >
    </a
      ><a name="6099" href="Stlc.html#6086" class="Bound"
      >&#915;</a
      ><a name="6100"
      > </a
      ><a name="6101" href="Stlc.html#6088" class="Bound"
      >x</a
      ><a name="6102"
      > </a
      ><a name="6103" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="6104"
      > </a
      ><a name="6105" href="https://agda.github.io/agda-stdlib/Data.Maybe.Base.html#373" class="InductiveConstructor"
      >just</a
      ><a name="6109"
      > </a
      ><a name="6110" href="Stlc.html#6090" class="Bound"
      >A</a
      ><a name="6111"
      > </a
      ><a name="6112" class="Symbol"
      >&#8594;</a
      ><a name="6113"
      >
    </a
      ><a name="6118" href="Stlc.html#6086" class="Bound"
      >&#915;</a
      ><a name="6119"
      > </a
      ><a name="6120" href="Stlc.html#6034" class="Datatype Operator"
      >&#8866;</a
      ><a name="6121"
      > </a
      ><a name="6122" href="Stlc.html#3627" class="InductiveConstructor"
      >`</a
      ><a name="6123"
      > </a
      ><a name="6124" href="Stlc.html#6088" class="Bound"
      >x</a
      ><a name="6125"
      > </a
      ><a name="6126" href="Stlc.html#6034" class="Datatype Operator"
      >&#8758;</a
      ><a name="6127"
      > </a
      ><a name="6128" href="Stlc.html#6090" class="Bound"
      >A</a
      ><a name="6129"
      >
  </a
      ><a name="6132" href="Stlc.html#6132" class="InductiveConstructor"
      >&#8658;-I</a
      ><a name="6135"
      > </a
      ><a name="6136" class="Symbol"
      >:</a
      ><a name="6137"
      > </a
      ><a name="6138" class="Symbol"
      >&#8704;</a
      ><a name="6139"
      > </a
      ><a name="6140" class="Symbol"
      >{</a
      ><a name="6141" href="Stlc.html#6141" class="Bound"
      >&#915;</a
      ><a name="6142"
      > </a
      ><a name="6143" href="Stlc.html#6143" class="Bound"
      >x</a
      ><a name="6144"
      > </a
      ><a name="6145" href="Stlc.html#6145" class="Bound"
      >N</a
      ><a name="6146"
      > </a
      ><a name="6147" href="Stlc.html#6147" class="Bound"
      >A</a
      ><a name="6148"
      > </a
      ><a name="6149" href="Stlc.html#6149" class="Bound"
      >B</a
      ><a name="6150" class="Symbol"
      >}</a
      ><a name="6151"
      > </a
      ><a name="6152" class="Symbol"
      >&#8594;</a
      ><a name="6153"
      >
    </a
      ><a name="6158" href="Stlc.html#6141" class="Bound"
      >&#915;</a
      ><a name="6159"
      > </a
      ><a name="6160" href="Maps.html#10368" class="Function Operator"
      >,</a
      ><a name="6161"
      > </a
      ><a name="6162" href="Stlc.html#6143" class="Bound"
      >x</a
      ><a name="6163"
      > </a
      ><a name="6164" href="Maps.html#10368" class="Function Operator"
      >&#8758;</a
      ><a name="6165"
      > </a
      ><a name="6166" href="Stlc.html#6147" class="Bound"
      >A</a
      ><a name="6167"
      > </a
      ><a name="6168" href="Stlc.html#6034" class="Datatype Operator"
      >&#8866;</a
      ><a name="6169"
      > </a
      ><a name="6170" href="Stlc.html#6145" class="Bound"
      >N</a
      ><a name="6171"
      > </a
      ><a name="6172" href="Stlc.html#6034" class="Datatype Operator"
      >&#8758;</a
      ><a name="6173"
      > </a
      ><a name="6174" href="Stlc.html#6149" class="Bound"
      >B</a
      ><a name="6175"
      > </a
      ><a name="6176" class="Symbol"
      >&#8594;</a
      ><a name="6177"
      >
    </a
      ><a name="6182" href="Stlc.html#6141" class="Bound"
      >&#915;</a
      ><a name="6183"
      > </a
      ><a name="6184" href="Stlc.html#6034" class="Datatype Operator"
      >&#8866;</a
      ><a name="6185"
      > </a
      ><a name="6186" href="Stlc.html#3643" class="InductiveConstructor Operator"
      >&#955;[</a
      ><a name="6188"
      > </a
      ><a name="6189" href="Stlc.html#6143" class="Bound"
      >x</a
      ><a name="6190"
      > </a
      ><a name="6191" href="Stlc.html#3643" class="InductiveConstructor Operator"
      >&#8758;</a
      ><a name="6192"
      > </a
      ><a name="6193" href="Stlc.html#6147" class="Bound"
      >A</a
      ><a name="6194"
      > </a
      ><a name="6195" href="Stlc.html#3643" class="InductiveConstructor Operator"
      >]</a
      ><a name="6196"
      > </a
      ><a name="6197" href="Stlc.html#6145" class="Bound"
      >N</a
      ><a name="6198"
      > </a
      ><a name="6199" href="Stlc.html#6034" class="Datatype Operator"
      >&#8758;</a
      ><a name="6200"
      > </a
      ><a name="6201" href="Stlc.html#6147" class="Bound"
      >A</a
      ><a name="6202"
      > </a
      ><a name="6203" href="Stlc.html#2554" class="InductiveConstructor Operator"
      >&#8658;</a
      ><a name="6204"
      > </a
      ><a name="6205" href="Stlc.html#6149" class="Bound"
      >B</a
      ><a name="6206"
      >
  </a
      ><a name="6209" href="Stlc.html#6209" class="InductiveConstructor"
      >&#8658;-E</a
      ><a name="6212"
      > </a
      ><a name="6213" class="Symbol"
      >:</a
      ><a name="6214"
      > </a
      ><a name="6215" class="Symbol"
      >&#8704;</a
      ><a name="6216"
      > </a
      ><a name="6217" class="Symbol"
      >{</a
      ><a name="6218" href="Stlc.html#6218" class="Bound"
      >&#915;</a
      ><a name="6219"
      > </a
      ><a name="6220" href="Stlc.html#6220" class="Bound"
      >L</a
      ><a name="6221"
      > </a
      ><a name="6222" href="Stlc.html#6222" class="Bound"
      >M</a
      ><a name="6223"
      > </a
      ><a name="6224" href="Stlc.html#6224" class="Bound"
      >A</a
      ><a name="6225"
      > </a
      ><a name="6226" href="Stlc.html#6226" class="Bound"
      >B</a
      ><a name="6227" class="Symbol"
      >}</a
      ><a name="6228"
      > </a
      ><a name="6229" class="Symbol"
      >&#8594;</a
      ><a name="6230"
      >
    </a
      ><a name="6235" href="Stlc.html#6218" class="Bound"
      >&#915;</a
      ><a name="6236"
      > </a
      ><a name="6237" href="Stlc.html#6034" class="Datatype Operator"
      >&#8866;</a
      ><a name="6238"
      > </a
      ><a name="6239" href="Stlc.html#6220" class="Bound"
      >L</a
      ><a name="6240"
      > </a
      ><a name="6241" href="Stlc.html#6034" class="Datatype Operator"
      >&#8758;</a
      ><a name="6242"
      > </a
      ><a name="6243" href="Stlc.html#6224" class="Bound"
      >A</a
      ><a name="6244"
      > </a
      ><a name="6245" href="Stlc.html#2554" class="InductiveConstructor Operator"
      >&#8658;</a
      ><a name="6246"
      > </a
      ><a name="6247" href="Stlc.html#6226" class="Bound"
      >B</a
      ><a name="6248"
      > </a
      ><a name="6249" class="Symbol"
      >&#8594;</a
      ><a name="6250"
      >
    </a
      ><a name="6255" href="Stlc.html#6218" class="Bound"
      >&#915;</a
      ><a name="6256"
      > </a
      ><a name="6257" href="Stlc.html#6034" class="Datatype Operator"
      >&#8866;</a
      ><a name="6258"
      > </a
      ><a name="6259" href="Stlc.html#6222" class="Bound"
      >M</a
      ><a name="6260"
      > </a
      ><a name="6261" href="Stlc.html#6034" class="Datatype Operator"
      >&#8758;</a
      ><a name="6262"
      > </a
      ><a name="6263" href="Stlc.html#6224" class="Bound"
      >A</a
      ><a name="6264"
      > </a
      ><a name="6265" class="Symbol"
      >&#8594;</a
      ><a name="6266"
      >
    </a
      ><a name="6271" href="Stlc.html#6218" class="Bound"
      >&#915;</a
      ><a name="6272"
      > </a
      ><a name="6273" href="Stlc.html#6034" class="Datatype Operator"
      >&#8866;</a
      ><a name="6274"
      > </a
      ><a name="6275" href="Stlc.html#6220" class="Bound"
      >L</a
      ><a name="6276"
      > </a
      ><a name="6277" href="Stlc.html#3679" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="6278"
      > </a
      ><a name="6279" href="Stlc.html#6222" class="Bound"
      >M</a
      ><a name="6280"
      > </a
      ><a name="6281" href="Stlc.html#6034" class="Datatype Operator"
      >&#8758;</a
      ><a name="6282"
      > </a
      ><a name="6283" href="Stlc.html#6226" class="Bound"
      >B</a
      ><a name="6284"
      >
  </a
      ><a name="6287" href="Stlc.html#6287" class="InductiveConstructor"
      >&#120121;-I&#8321;</a
      ><a name="6291"
      > </a
      ><a name="6292" class="Symbol"
      >:</a
      ><a name="6293"
      > </a
      ><a name="6294" class="Symbol"
      >&#8704;</a
      ><a name="6295"
      > </a
      ><a name="6296" class="Symbol"
      >{</a
      ><a name="6297" href="Stlc.html#6297" class="Bound"
      >&#915;</a
      ><a name="6298" class="Symbol"
      >}</a
      ><a name="6299"
      > </a
      ><a name="6300" class="Symbol"
      >&#8594;</a
      ><a name="6301"
      >
    </a
      ><a name="6306" href="Stlc.html#6297" class="Bound"
      >&#915;</a
      ><a name="6307"
      > </a
      ><a name="6308" href="Stlc.html#6034" class="Datatype Operator"
      >&#8866;</a
      ><a name="6309"
      > </a
      ><a name="6310" href="Stlc.html#3706" class="InductiveConstructor"
      >true</a
      ><a name="6314"
      > </a
      ><a name="6315" href="Stlc.html#6034" class="Datatype Operator"
      >&#8758;</a
      ><a name="6316"
      > </a
      ><a name="6317" href="Stlc.html#2581" class="InductiveConstructor"
      >&#120121;</a
      ><a name="6318"
      >
  </a
      ><a name="6321" href="Stlc.html#6321" class="InductiveConstructor"
      >&#120121;-I&#8322;</a
      ><a name="6325"
      > </a
      ><a name="6326" class="Symbol"
      >:</a
      ><a name="6327"
      > </a
      ><a name="6328" class="Symbol"
      >&#8704;</a
      ><a name="6329"
      > </a
      ><a name="6330" class="Symbol"
      >{</a
      ><a name="6331" href="Stlc.html#6331" class="Bound"
      >&#915;</a
      ><a name="6332" class="Symbol"
      >}</a
      ><a name="6333"
      > </a
      ><a name="6334" class="Symbol"
      >&#8594;</a
      ><a name="6335"
      >
    </a
      ><a name="6340" href="Stlc.html#6331" class="Bound"
      >&#915;</a
      ><a name="6341"
      > </a
      ><a name="6342" href="Stlc.html#6034" class="Datatype Operator"
      >&#8866;</a
      ><a name="6343"
      > </a
      ><a name="6344" href="Stlc.html#3720" class="InductiveConstructor"
      >false</a
      ><a name="6349"
      > </a
      ><a name="6350" href="Stlc.html#6034" class="Datatype Operator"
      >&#8758;</a
      ><a name="6351"
      > </a
      ><a name="6352" href="Stlc.html#2581" class="InductiveConstructor"
      >&#120121;</a
      ><a name="6353"
      >
  </a
      ><a name="6356" href="Stlc.html#6356" class="InductiveConstructor"
      >&#120121;-E</a
      ><a name="6359"
      > </a
      ><a name="6360" class="Symbol"
      >:</a
      ><a name="6361"
      > </a
      ><a name="6362" class="Symbol"
      >&#8704;</a
      ><a name="6363"
      > </a
      ><a name="6364" class="Symbol"
      >{</a
      ><a name="6365" href="Stlc.html#6365" class="Bound"
      >&#915;</a
      ><a name="6366"
      > </a
      ><a name="6367" href="Stlc.html#6367" class="Bound"
      >L</a
      ><a name="6368"
      > </a
      ><a name="6369" href="Stlc.html#6369" class="Bound"
      >M</a
      ><a name="6370"
      > </a
      ><a name="6371" href="Stlc.html#6371" class="Bound"
      >N</a
      ><a name="6372"
      > </a
      ><a name="6373" href="Stlc.html#6373" class="Bound"
      >A</a
      ><a name="6374" class="Symbol"
      >}</a
      ><a name="6375"
      > </a
      ><a name="6376" class="Symbol"
      >&#8594;</a
      ><a name="6377"
      >
    </a
      ><a name="6382" href="Stlc.html#6365" class="Bound"
      >&#915;</a
      ><a name="6383"
      > </a
      ><a name="6384" href="Stlc.html#6034" class="Datatype Operator"
      >&#8866;</a
      ><a name="6385"
      > </a
      ><a name="6386" href="Stlc.html#6367" class="Bound"
      >L</a
      ><a name="6387"
      > </a
      ><a name="6388" href="Stlc.html#6034" class="Datatype Operator"
      >&#8758;</a
      ><a name="6389"
      > </a
      ><a name="6390" href="Stlc.html#2581" class="InductiveConstructor"
      >&#120121;</a
      ><a name="6391"
      > </a
      ><a name="6392" class="Symbol"
      >&#8594;</a
      ><a name="6393"
      >
    </a
      ><a name="6398" href="Stlc.html#6365" class="Bound"
      >&#915;</a
      ><a name="6399"
      > </a
      ><a name="6400" href="Stlc.html#6034" class="Datatype Operator"
      >&#8866;</a
      ><a name="6401"
      > </a
      ><a name="6402" href="Stlc.html#6369" class="Bound"
      >M</a
      ><a name="6403"
      > </a
      ><a name="6404" href="Stlc.html#6034" class="Datatype Operator"
      >&#8758;</a
      ><a name="6405"
      > </a
      ><a name="6406" href="Stlc.html#6373" class="Bound"
      >A</a
      ><a name="6407"
      > </a
      ><a name="6408" class="Symbol"
      >&#8594;</a
      ><a name="6409"
      >
    </a
      ><a name="6414" href="Stlc.html#6365" class="Bound"
      >&#915;</a
      ><a name="6415"
      > </a
      ><a name="6416" href="Stlc.html#6034" class="Datatype Operator"
      >&#8866;</a
      ><a name="6417"
      > </a
      ><a name="6418" href="Stlc.html#6371" class="Bound"
      >N</a
      ><a name="6419"
      > </a
      ><a name="6420" href="Stlc.html#6034" class="Datatype Operator"
      >&#8758;</a
      ><a name="6421"
      > </a
      ><a name="6422" href="Stlc.html#6373" class="Bound"
      >A</a
      ><a name="6423"
      > </a
      ><a name="6424" class="Symbol"
      >&#8594;</a
      ><a name="6425"
      >
    </a
      ><a name="6430" href="Stlc.html#6365" class="Bound"
      >&#915;</a
      ><a name="6431"
      > </a
      ><a name="6432" href="Stlc.html#6034" class="Datatype Operator"
      >&#8866;</a
      ><a name="6433"
      > </a
      ><a name="6434" href="Stlc.html#3735" class="InductiveConstructor Operator"
      >if</a
      ><a name="6436"
      > </a
      ><a name="6437" href="Stlc.html#6367" class="Bound"
      >L</a
      ><a name="6438"
      > </a
      ><a name="6439" href="Stlc.html#3735" class="InductiveConstructor Operator"
      >then</a
      ><a name="6443"
      > </a
      ><a name="6444" href="Stlc.html#6369" class="Bound"
      >M</a
      ><a name="6445"
      > </a
      ><a name="6446" href="Stlc.html#3735" class="InductiveConstructor Operator"
      >else</a
      ><a name="6450"
      > </a
      ><a name="6451" href="Stlc.html#6371" class="Bound"
      >N</a
      ><a name="6452"
      > </a
      ><a name="6453" href="Stlc.html#6034" class="Datatype Operator"
      >&#8758;</a
      ><a name="6454"
      > </a
      ><a name="6455" href="Stlc.html#6373" class="Bound"
      >A</a
      >

</pre>

## Example type derivations

<pre class="Agda">

<a name="6515" href="Stlc.html#6515" class="Function"
      >typing&#8321;</a
      ><a name="6522"
      > </a
      ><a name="6523" class="Symbol"
      >:</a
      ><a name="6524"
      > </a
      ><a name="6525" href="Maps.html#10265" class="Function"
      >&#8709;</a
      ><a name="6526"
      > </a
      ><a name="6527" href="Stlc.html#6034" class="Datatype Operator"
      >&#8866;</a
      ><a name="6528"
      > </a
      ><a name="6529" href="Stlc.html#3871" class="Function"
      >not</a
      ><a name="6532"
      > </a
      ><a name="6533" href="Stlc.html#6034" class="Datatype Operator"
      >&#8758;</a
      ><a name="6534"
      > </a
      ><a name="6535" href="Stlc.html#2581" class="InductiveConstructor"
      >&#120121;</a
      ><a name="6536"
      > </a
      ><a name="6537" href="Stlc.html#2554" class="InductiveConstructor Operator"
      >&#8658;</a
      ><a name="6538"
      > </a
      ><a name="6539" href="Stlc.html#2581" class="InductiveConstructor"
      >&#120121;</a
      ><a name="6540"
      >
</a
      ><a name="6541" href="Stlc.html#6515" class="Function"
      >typing&#8321;</a
      ><a name="6548"
      > </a
      ><a name="6549" class="Symbol"
      >=</a
      ><a name="6550"
      > </a
      ><a name="6551" href="Stlc.html#6132" class="InductiveConstructor"
      >&#8658;-I</a
      ><a name="6554"
      > </a
      ><a name="6555" class="Symbol"
      >(</a
      ><a name="6556" href="Stlc.html#6356" class="InductiveConstructor"
      >&#120121;-E</a
      ><a name="6559"
      > </a
      ><a name="6560" class="Symbol"
      >(</a
      ><a name="6561" href="Stlc.html#6078" class="InductiveConstructor"
      >Ax</a
      ><a name="6563"
      > </a
      ><a name="6564" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="6568" class="Symbol"
      >)</a
      ><a name="6569"
      > </a
      ><a name="6570" href="Stlc.html#6321" class="InductiveConstructor"
      >&#120121;-I&#8322;</a
      ><a name="6574"
      > </a
      ><a name="6575" href="Stlc.html#6287" class="InductiveConstructor"
      >&#120121;-I&#8321;</a
      ><a name="6579" class="Symbol"
      >)</a
      ><a name="6580"
      >

</a
      ><a name="6582" href="Stlc.html#6582" class="Function"
      >typing&#8322;</a
      ><a name="6589"
      > </a
      ><a name="6590" class="Symbol"
      >:</a
      ><a name="6591"
      > </a
      ><a name="6592" href="Maps.html#10265" class="Function"
      >&#8709;</a
      ><a name="6593"
      > </a
      ><a name="6594" href="Stlc.html#6034" class="Datatype Operator"
      >&#8866;</a
      ><a name="6595"
      > </a
      ><a name="6596" href="Stlc.html#3875" class="Function"
      >two</a
      ><a name="6599"
      > </a
      ><a name="6600" href="Stlc.html#6034" class="Datatype Operator"
      >&#8758;</a
      ><a name="6601"
      > </a
      ><a name="6602" class="Symbol"
      >(</a
      ><a name="6603" href="Stlc.html#2581" class="InductiveConstructor"
      >&#120121;</a
      ><a name="6604"
      > </a
      ><a name="6605" href="Stlc.html#2554" class="InductiveConstructor Operator"
      >&#8658;</a
      ><a name="6606"
      > </a
      ><a name="6607" href="Stlc.html#2581" class="InductiveConstructor"
      >&#120121;</a
      ><a name="6608" class="Symbol"
      >)</a
      ><a name="6609"
      > </a
      ><a name="6610" href="Stlc.html#2554" class="InductiveConstructor Operator"
      >&#8658;</a
      ><a name="6611"
      > </a
      ><a name="6612" href="Stlc.html#2581" class="InductiveConstructor"
      >&#120121;</a
      ><a name="6613"
      > </a
      ><a name="6614" href="Stlc.html#2554" class="InductiveConstructor Operator"
      >&#8658;</a
      ><a name="6615"
      > </a
      ><a name="6616" href="Stlc.html#2581" class="InductiveConstructor"
      >&#120121;</a
      ><a name="6617"
      >
</a
      ><a name="6618" href="Stlc.html#6582" class="Function"
      >typing&#8322;</a
      ><a name="6625"
      > </a
      ><a name="6626" class="Symbol"
      >=</a
      ><a name="6627"
      > </a
      ><a name="6628" href="Stlc.html#6132" class="InductiveConstructor"
      >&#8658;-I</a
      ><a name="6631"
      > </a
      ><a name="6632" class="Symbol"
      >(</a
      ><a name="6633" href="Stlc.html#6132" class="InductiveConstructor"
      >&#8658;-I</a
      ><a name="6636"
      > </a
      ><a name="6637" class="Symbol"
      >(</a
      ><a name="6638" href="Stlc.html#6209" class="InductiveConstructor"
      >&#8658;-E</a
      ><a name="6641"
      > </a
      ><a name="6642" class="Symbol"
      >(</a
      ><a name="6643" href="Stlc.html#6078" class="InductiveConstructor"
      >Ax</a
      ><a name="6645"
      > </a
      ><a name="6646" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="6650" class="Symbol"
      >)</a
      ><a name="6651"
      > </a
      ><a name="6652" class="Symbol"
      >(</a
      ><a name="6653" href="Stlc.html#6209" class="InductiveConstructor"
      >&#8658;-E</a
      ><a name="6656"
      > </a
      ><a name="6657" class="Symbol"
      >(</a
      ><a name="6658" href="Stlc.html#6078" class="InductiveConstructor"
      >Ax</a
      ><a name="6660"
      > </a
      ><a name="6661" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="6665" class="Symbol"
      >)</a
      ><a name="6666"
      > </a
      ><a name="6667" class="Symbol"
      >(</a
      ><a name="6668" href="Stlc.html#6078" class="InductiveConstructor"
      >Ax</a
      ><a name="6670"
      > </a
      ><a name="6671" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="6675" class="Symbol"
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


