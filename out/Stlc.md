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

    A, B, C ::=
      A ⇒ B   -- functions
      𝔹        -- booleans

And here it is formalised in Agda.

<pre class="Agda">

<a name="2555" class="Keyword"
      >infixr</a
      ><a name="2561"
      > </a
      ><a name="2562" class="Number"
      >20</a
      ><a name="2564"
      > </a
      ><a name="2565" href="Stlc.html#2594" class="InductiveConstructor Operator"
      >_&#8658;_</a
      ><a name="2568"
      >

</a
      ><a name="2570" class="Keyword"
      >data</a
      ><a name="2574"
      > </a
      ><a name="2575" href="Stlc.html#2575" class="Datatype"
      >Type</a
      ><a name="2579"
      > </a
      ><a name="2580" class="Symbol"
      >:</a
      ><a name="2581"
      > </a
      ><a name="2582" class="PrimitiveType"
      >Set</a
      ><a name="2585"
      > </a
      ><a name="2586" class="Keyword"
      >where</a
      ><a name="2591"
      >
  </a
      ><a name="2594" href="Stlc.html#2594" class="InductiveConstructor Operator"
      >_&#8658;_</a
      ><a name="2597"
      > </a
      ><a name="2598" class="Symbol"
      >:</a
      ><a name="2599"
      > </a
      ><a name="2600" href="Stlc.html#2575" class="Datatype"
      >Type</a
      ><a name="2604"
      > </a
      ><a name="2605" class="Symbol"
      >&#8594;</a
      ><a name="2606"
      > </a
      ><a name="2607" href="Stlc.html#2575" class="Datatype"
      >Type</a
      ><a name="2611"
      > </a
      ><a name="2612" class="Symbol"
      >&#8594;</a
      ><a name="2613"
      > </a
      ><a name="2614" href="Stlc.html#2575" class="Datatype"
      >Type</a
      ><a name="2618"
      >
  </a
      ><a name="2621" href="Stlc.html#2621" class="InductiveConstructor"
      >&#120121;</a
      ><a name="2622"
      > </a
      ><a name="2623" class="Symbol"
      >:</a
      ><a name="2624"
      > </a
      ><a name="2625" href="Stlc.html#2575" class="Datatype"
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

    L, M, N ::= ` x | λ[ x ∶ A ] N 




<pre class="Agda">

<a name="3504" class="Keyword"
      >infixl</a
      ><a name="3510"
      > </a
      ><a name="3511" class="Number"
      >20</a
      ><a name="3513"
      > </a
      ><a name="3514" href="Stlc.html#3637" class="InductiveConstructor Operator"
      >_&#183;_</a
      ><a name="3517"
      >
</a
      ><a name="3518" class="Keyword"
      >infix</a
      ><a name="3523"
      >  </a
      ><a name="3525" class="Number"
      >15</a
      ><a name="3527"
      > </a
      ><a name="3528" href="Stlc.html#3601" class="InductiveConstructor Operator"
      >&#955;[_&#8758;_]_</a
      ><a name="3535"
      >
</a
      ><a name="3536" class="Keyword"
      >infix</a
      ><a name="3541"
      >  </a
      ><a name="3543" class="Number"
      >15</a
      ><a name="3545"
      > </a
      ><a name="3546" href="Stlc.html#3693" class="InductiveConstructor Operator"
      >if_then_else_</a
      ><a name="3559"
      >

</a
      ><a name="3561" class="Keyword"
      >data</a
      ><a name="3565"
      > </a
      ><a name="3566" href="Stlc.html#3566" class="Datatype"
      >Term</a
      ><a name="3570"
      > </a
      ><a name="3571" class="Symbol"
      >:</a
      ><a name="3572"
      > </a
      ><a name="3573" class="PrimitiveType"
      >Set</a
      ><a name="3576"
      > </a
      ><a name="3577" class="Keyword"
      >where</a
      ><a name="3582"
      >
  </a
      ><a name="3585" href="Stlc.html#3585" class="InductiveConstructor"
      >`</a
      ><a name="3586"
      > </a
      ><a name="3587" class="Symbol"
      >:</a
      ><a name="3588"
      > </a
      ><a name="3589" href="Maps.html#2171" class="Datatype"
      >Id</a
      ><a name="3591"
      > </a
      ><a name="3592" class="Symbol"
      >&#8594;</a
      ><a name="3593"
      > </a
      ><a name="3594" href="Stlc.html#3566" class="Datatype"
      >Term</a
      ><a name="3598"
      >
  </a
      ><a name="3601" href="Stlc.html#3601" class="InductiveConstructor Operator"
      >&#955;[_&#8758;_]_</a
      ><a name="3608"
      > </a
      ><a name="3609" class="Symbol"
      >:</a
      ><a name="3610"
      > </a
      ><a name="3611" href="Maps.html#2171" class="Datatype"
      >Id</a
      ><a name="3613"
      > </a
      ><a name="3614" class="Symbol"
      >&#8594;</a
      ><a name="3615"
      > </a
      ><a name="3616" href="Stlc.html#2575" class="Datatype"
      >Type</a
      ><a name="3620"
      > </a
      ><a name="3621" class="Symbol"
      >&#8594;</a
      ><a name="3622"
      > </a
      ><a name="3623" href="Stlc.html#3566" class="Datatype"
      >Term</a
      ><a name="3627"
      > </a
      ><a name="3628" class="Symbol"
      >&#8594;</a
      ><a name="3629"
      > </a
      ><a name="3630" href="Stlc.html#3566" class="Datatype"
      >Term</a
      ><a name="3634"
      >
  </a
      ><a name="3637" href="Stlc.html#3637" class="InductiveConstructor Operator"
      >_&#183;_</a
      ><a name="3640"
      > </a
      ><a name="3641" class="Symbol"
      >:</a
      ><a name="3642"
      > </a
      ><a name="3643" href="Stlc.html#3566" class="Datatype"
      >Term</a
      ><a name="3647"
      > </a
      ><a name="3648" class="Symbol"
      >&#8594;</a
      ><a name="3649"
      > </a
      ><a name="3650" href="Stlc.html#3566" class="Datatype"
      >Term</a
      ><a name="3654"
      > </a
      ><a name="3655" class="Symbol"
      >&#8594;</a
      ><a name="3656"
      > </a
      ><a name="3657" href="Stlc.html#3566" class="Datatype"
      >Term</a
      ><a name="3661"
      >
  </a
      ><a name="3664" href="Stlc.html#3664" class="InductiveConstructor"
      >true</a
      ><a name="3668"
      > </a
      ><a name="3669" class="Symbol"
      >:</a
      ><a name="3670"
      > </a
      ><a name="3671" href="Stlc.html#3566" class="Datatype"
      >Term</a
      ><a name="3675"
      >
  </a
      ><a name="3678" href="Stlc.html#3678" class="InductiveConstructor"
      >false</a
      ><a name="3683"
      > </a
      ><a name="3684" class="Symbol"
      >:</a
      ><a name="3685"
      > </a
      ><a name="3686" href="Stlc.html#3566" class="Datatype"
      >Term</a
      ><a name="3690"
      >
  </a
      ><a name="3693" href="Stlc.html#3693" class="InductiveConstructor Operator"
      >if_then_else_</a
      ><a name="3706"
      > </a
      ><a name="3707" class="Symbol"
      >:</a
      ><a name="3708"
      > </a
      ><a name="3709" href="Stlc.html#3566" class="Datatype"
      >Term</a
      ><a name="3713"
      > </a
      ><a name="3714" class="Symbol"
      >&#8594;</a
      ><a name="3715"
      > </a
      ><a name="3716" href="Stlc.html#3566" class="Datatype"
      >Term</a
      ><a name="3720"
      > </a
      ><a name="3721" class="Symbol"
      >&#8594;</a
      ><a name="3722"
      > </a
      ><a name="3723" href="Stlc.html#3566" class="Datatype"
      >Term</a
      ><a name="3727"
      > </a
      ><a name="3728" class="Symbol"
      >&#8594;</a
      ><a name="3729"
      > </a
      ><a name="3730" href="Stlc.html#3566" class="Datatype"
      >Term</a
      >

</pre>

Each type introduces its own constructs, which come in pairs,
one to introduce (or construct) values of the type, and one to eliminate
(or deconstruct) them.

CONTINUE FROM HERE



Example terms.
<pre class="Agda">

<a name="3956" href="Stlc.html#3956" class="Function"
      >f</a
      ><a name="3957"
      > </a
      ><a name="3958" href="Stlc.html#3958" class="Function"
      >x</a
      ><a name="3959"
      > </a
      ><a name="3960" class="Symbol"
      >:</a
      ><a name="3961"
      > </a
      ><a name="3962" href="Maps.html#2171" class="Datatype"
      >Id</a
      ><a name="3964"
      >
</a
      ><a name="3965" href="Stlc.html#3956" class="Function"
      >f</a
      ><a name="3966"
      >  </a
      ><a name="3968" class="Symbol"
      >=</a
      ><a name="3969"
      >  </a
      ><a name="3971" href="Maps.html#2188" class="InductiveConstructor"
      >id</a
      ><a name="3973"
      > </a
      ><a name="3974" class="Number"
      >0</a
      ><a name="3975"
      >
</a
      ><a name="3976" href="Stlc.html#3958" class="Function"
      >x</a
      ><a name="3977"
      >  </a
      ><a name="3979" class="Symbol"
      >=</a
      ><a name="3980"
      >  </a
      ><a name="3982" href="Maps.html#2188" class="InductiveConstructor"
      >id</a
      ><a name="3984"
      > </a
      ><a name="3985" class="Number"
      >1</a
      ><a name="3986"
      >

</a
      ><a name="3988" href="Stlc.html#3988" class="Function"
      >not</a
      ><a name="3991"
      > </a
      ><a name="3992" href="Stlc.html#3992" class="Function"
      >two</a
      ><a name="3995"
      > </a
      ><a name="3996" class="Symbol"
      >:</a
      ><a name="3997"
      > </a
      ><a name="3998" href="Stlc.html#3566" class="Datatype"
      >Term</a
      ><a name="4002"
      > 
</a
      ><a name="4004" href="Stlc.html#3988" class="Function"
      >not</a
      ><a name="4007"
      > </a
      ><a name="4008" class="Symbol"
      >=</a
      ><a name="4009"
      >  </a
      ><a name="4011" href="Stlc.html#3601" class="InductiveConstructor Operator"
      >&#955;[</a
      ><a name="4013"
      > </a
      ><a name="4014" href="Stlc.html#3958" class="Function"
      >x</a
      ><a name="4015"
      > </a
      ><a name="4016" href="Stlc.html#3601" class="InductiveConstructor Operator"
      >&#8758;</a
      ><a name="4017"
      > </a
      ><a name="4018" href="Stlc.html#2621" class="InductiveConstructor"
      >&#120121;</a
      ><a name="4019"
      > </a
      ><a name="4020" href="Stlc.html#3601" class="InductiveConstructor Operator"
      >]</a
      ><a name="4021"
      > </a
      ><a name="4022" class="Symbol"
      >(</a
      ><a name="4023" href="Stlc.html#3693" class="InductiveConstructor Operator"
      >if</a
      ><a name="4025"
      > </a
      ><a name="4026" href="Stlc.html#3585" class="InductiveConstructor"
      >`</a
      ><a name="4027"
      > </a
      ><a name="4028" href="Stlc.html#3958" class="Function"
      >x</a
      ><a name="4029"
      > </a
      ><a name="4030" href="Stlc.html#3693" class="InductiveConstructor Operator"
      >then</a
      ><a name="4034"
      > </a
      ><a name="4035" href="Stlc.html#3678" class="InductiveConstructor"
      >false</a
      ><a name="4040"
      > </a
      ><a name="4041" href="Stlc.html#3693" class="InductiveConstructor Operator"
      >else</a
      ><a name="4045"
      > </a
      ><a name="4046" href="Stlc.html#3664" class="InductiveConstructor"
      >true</a
      ><a name="4050" class="Symbol"
      >)</a
      ><a name="4051"
      >
</a
      ><a name="4052" href="Stlc.html#3992" class="Function"
      >two</a
      ><a name="4055"
      > </a
      ><a name="4056" class="Symbol"
      >=</a
      ><a name="4057"
      >  </a
      ><a name="4059" href="Stlc.html#3601" class="InductiveConstructor Operator"
      >&#955;[</a
      ><a name="4061"
      > </a
      ><a name="4062" href="Stlc.html#3956" class="Function"
      >f</a
      ><a name="4063"
      > </a
      ><a name="4064" href="Stlc.html#3601" class="InductiveConstructor Operator"
      >&#8758;</a
      ><a name="4065"
      > </a
      ><a name="4066" href="Stlc.html#2621" class="InductiveConstructor"
      >&#120121;</a
      ><a name="4067"
      > </a
      ><a name="4068" href="Stlc.html#2594" class="InductiveConstructor Operator"
      >&#8658;</a
      ><a name="4069"
      > </a
      ><a name="4070" href="Stlc.html#2621" class="InductiveConstructor"
      >&#120121;</a
      ><a name="4071"
      > </a
      ><a name="4072" href="Stlc.html#3601" class="InductiveConstructor Operator"
      >]</a
      ><a name="4073"
      > </a
      ><a name="4074" href="Stlc.html#3601" class="InductiveConstructor Operator"
      >&#955;[</a
      ><a name="4076"
      > </a
      ><a name="4077" href="Stlc.html#3958" class="Function"
      >x</a
      ><a name="4078"
      > </a
      ><a name="4079" href="Stlc.html#3601" class="InductiveConstructor Operator"
      >&#8758;</a
      ><a name="4080"
      > </a
      ><a name="4081" href="Stlc.html#2621" class="InductiveConstructor"
      >&#120121;</a
      ><a name="4082"
      > </a
      ><a name="4083" href="Stlc.html#3601" class="InductiveConstructor Operator"
      >]</a
      ><a name="4084"
      > </a
      ><a name="4085" href="Stlc.html#3585" class="InductiveConstructor"
      >`</a
      ><a name="4086"
      > </a
      ><a name="4087" href="Stlc.html#3956" class="Function"
      >f</a
      ><a name="4088"
      > </a
      ><a name="4089" href="Stlc.html#3637" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="4090"
      > </a
      ><a name="4091" class="Symbol"
      >(</a
      ><a name="4092" href="Stlc.html#3585" class="InductiveConstructor"
      >`</a
      ><a name="4093"
      > </a
      ><a name="4094" href="Stlc.html#3956" class="Function"
      >f</a
      ><a name="4095"
      > </a
      ><a name="4096" href="Stlc.html#3637" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="4097"
      > </a
      ><a name="4098" href="Stlc.html#3585" class="InductiveConstructor"
      >`</a
      ><a name="4099"
      > </a
      ><a name="4100" href="Stlc.html#3958" class="Function"
      >x</a
      ><a name="4101" class="Symbol"
      >)</a
      >

</pre>

## Values

<pre class="Agda">

<a name="4139" class="Keyword"
      >data</a
      ><a name="4143"
      > </a
      ><a name="4144" href="Stlc.html#4144" class="Datatype"
      >Value</a
      ><a name="4149"
      > </a
      ><a name="4150" class="Symbol"
      >:</a
      ><a name="4151"
      > </a
      ><a name="4152" href="Stlc.html#3566" class="Datatype"
      >Term</a
      ><a name="4156"
      > </a
      ><a name="4157" class="Symbol"
      >&#8594;</a
      ><a name="4158"
      > </a
      ><a name="4159" class="PrimitiveType"
      >Set</a
      ><a name="4162"
      > </a
      ><a name="4163" class="Keyword"
      >where</a
      ><a name="4168"
      >
  </a
      ><a name="4171" href="Stlc.html#4171" class="InductiveConstructor"
      >value-&#955;</a
      ><a name="4178"
      >     </a
      ><a name="4183" class="Symbol"
      >:</a
      ><a name="4184"
      > </a
      ><a name="4185" class="Symbol"
      >&#8704;</a
      ><a name="4186"
      > </a
      ><a name="4187" class="Symbol"
      >{</a
      ><a name="4188" href="Stlc.html#4188" class="Bound"
      >x</a
      ><a name="4189"
      > </a
      ><a name="4190" href="Stlc.html#4190" class="Bound"
      >A</a
      ><a name="4191"
      > </a
      ><a name="4192" href="Stlc.html#4192" class="Bound"
      >N</a
      ><a name="4193" class="Symbol"
      >}</a
      ><a name="4194"
      > </a
      ><a name="4195" class="Symbol"
      >&#8594;</a
      ><a name="4196"
      > </a
      ><a name="4197" href="Stlc.html#4144" class="Datatype"
      >Value</a
      ><a name="4202"
      > </a
      ><a name="4203" class="Symbol"
      >(</a
      ><a name="4204" href="Stlc.html#3601" class="InductiveConstructor Operator"
      >&#955;[</a
      ><a name="4206"
      > </a
      ><a name="4207" href="Stlc.html#4188" class="Bound"
      >x</a
      ><a name="4208"
      > </a
      ><a name="4209" href="Stlc.html#3601" class="InductiveConstructor Operator"
      >&#8758;</a
      ><a name="4210"
      > </a
      ><a name="4211" href="Stlc.html#4190" class="Bound"
      >A</a
      ><a name="4212"
      > </a
      ><a name="4213" href="Stlc.html#3601" class="InductiveConstructor Operator"
      >]</a
      ><a name="4214"
      > </a
      ><a name="4215" href="Stlc.html#4192" class="Bound"
      >N</a
      ><a name="4216" class="Symbol"
      >)</a
      ><a name="4217"
      >
  </a
      ><a name="4220" href="Stlc.html#4220" class="InductiveConstructor"
      >value-true</a
      ><a name="4230"
      >  </a
      ><a name="4232" class="Symbol"
      >:</a
      ><a name="4233"
      > </a
      ><a name="4234" href="Stlc.html#4144" class="Datatype"
      >Value</a
      ><a name="4239"
      > </a
      ><a name="4240" href="Stlc.html#3664" class="InductiveConstructor"
      >true</a
      ><a name="4244"
      >
  </a
      ><a name="4247" href="Stlc.html#4247" class="InductiveConstructor"
      >value-false</a
      ><a name="4258"
      > </a
      ><a name="4259" class="Symbol"
      >:</a
      ><a name="4260"
      > </a
      ><a name="4261" href="Stlc.html#4144" class="Datatype"
      >Value</a
      ><a name="4266"
      > </a
      ><a name="4267" href="Stlc.html#3678" class="InductiveConstructor"
      >false</a
      >

</pre>

## Substitution

<pre class="Agda">

<a name="4315" href="Stlc.html#4315" class="Function Operator"
      >_[_:=_]</a
      ><a name="4322"
      > </a
      ><a name="4323" class="Symbol"
      >:</a
      ><a name="4324"
      > </a
      ><a name="4325" href="Stlc.html#3566" class="Datatype"
      >Term</a
      ><a name="4329"
      > </a
      ><a name="4330" class="Symbol"
      >&#8594;</a
      ><a name="4331"
      > </a
      ><a name="4332" href="Maps.html#2171" class="Datatype"
      >Id</a
      ><a name="4334"
      > </a
      ><a name="4335" class="Symbol"
      >&#8594;</a
      ><a name="4336"
      > </a
      ><a name="4337" href="Stlc.html#3566" class="Datatype"
      >Term</a
      ><a name="4341"
      > </a
      ><a name="4342" class="Symbol"
      >&#8594;</a
      ><a name="4343"
      > </a
      ><a name="4344" href="Stlc.html#3566" class="Datatype"
      >Term</a
      ><a name="4348"
      >
</a
      ><a name="4349" class="Symbol"
      >(</a
      ><a name="4350" href="Stlc.html#3585" class="InductiveConstructor"
      >`</a
      ><a name="4351"
      > </a
      ><a name="4352" href="Stlc.html#4352" class="Bound"
      >x&#8242;</a
      ><a name="4354" class="Symbol"
      >)</a
      ><a name="4355"
      > </a
      ><a name="4356" href="Stlc.html#4315" class="Function Operator"
      >[</a
      ><a name="4357"
      > </a
      ><a name="4358" href="Stlc.html#4358" class="Bound"
      >x</a
      ><a name="4359"
      > </a
      ><a name="4360" href="Stlc.html#4315" class="Function Operator"
      >:=</a
      ><a name="4362"
      > </a
      ><a name="4363" href="Stlc.html#4363" class="Bound"
      >V</a
      ><a name="4364"
      > </a
      ><a name="4365" href="Stlc.html#4315" class="Function Operator"
      >]</a
      ><a name="4366"
      > </a
      ><a name="4367" class="Keyword"
      >with</a
      ><a name="4371"
      > </a
      ><a name="4372" href="Stlc.html#4358" class="Bound"
      >x</a
      ><a name="4373"
      > </a
      ><a name="4374" href="Maps.html#2509" class="Function Operator"
      >&#8799;</a
      ><a name="4375"
      > </a
      ><a name="4376" href="Stlc.html#4352" class="Bound"
      >x&#8242;</a
      ><a name="4378"
      >
</a
      ><a name="4379" class="Symbol"
      >...</a
      ><a name="4382"
      > </a
      ><a name="4383" class="Symbol"
      >|</a
      ><a name="4384"
      > </a
      ><a name="4385" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#520" class="InductiveConstructor"
      >yes</a
      ><a name="4388"
      > </a
      ><a name="4389" class="Symbol"
      >_</a
      ><a name="4390"
      > </a
      ><a name="4391" class="Symbol"
      >=</a
      ><a name="4392"
      > </a
      ><a name="4393" href="Stlc.html#4363" class="Bound"
      >V</a
      ><a name="4394"
      >
</a
      ><a name="4395" class="Symbol"
      >...</a
      ><a name="4398"
      > </a
      ><a name="4399" class="Symbol"
      >|</a
      ><a name="4400"
      > </a
      ><a name="4401" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#547" class="InductiveConstructor"
      >no</a
      ><a name="4403"
      >  </a
      ><a name="4405" class="Symbol"
      >_</a
      ><a name="4406"
      > </a
      ><a name="4407" class="Symbol"
      >=</a
      ><a name="4408"
      > </a
      ><a name="4409" href="Stlc.html#3585" class="InductiveConstructor"
      >`</a
      ><a name="4410"
      > </a
      ><a name="4411" href="Stlc.html#4352" class="Bound"
      >x&#8242;</a
      ><a name="4413"
      >
</a
      ><a name="4414" class="Symbol"
      >(</a
      ><a name="4415" href="Stlc.html#3601" class="InductiveConstructor Operator"
      >&#955;[</a
      ><a name="4417"
      > </a
      ><a name="4418" href="Stlc.html#4418" class="Bound"
      >x&#8242;</a
      ><a name="4420"
      > </a
      ><a name="4421" href="Stlc.html#3601" class="InductiveConstructor Operator"
      >&#8758;</a
      ><a name="4422"
      > </a
      ><a name="4423" href="Stlc.html#4423" class="Bound"
      >A&#8242;</a
      ><a name="4425"
      > </a
      ><a name="4426" href="Stlc.html#3601" class="InductiveConstructor Operator"
      >]</a
      ><a name="4427"
      > </a
      ><a name="4428" href="Stlc.html#4428" class="Bound"
      >N&#8242;</a
      ><a name="4430" class="Symbol"
      >)</a
      ><a name="4431"
      > </a
      ><a name="4432" href="Stlc.html#4315" class="Function Operator"
      >[</a
      ><a name="4433"
      > </a
      ><a name="4434" href="Stlc.html#4434" class="Bound"
      >x</a
      ><a name="4435"
      > </a
      ><a name="4436" href="Stlc.html#4315" class="Function Operator"
      >:=</a
      ><a name="4438"
      > </a
      ><a name="4439" href="Stlc.html#4439" class="Bound"
      >V</a
      ><a name="4440"
      > </a
      ><a name="4441" href="Stlc.html#4315" class="Function Operator"
      >]</a
      ><a name="4442"
      > </a
      ><a name="4443" class="Keyword"
      >with</a
      ><a name="4447"
      > </a
      ><a name="4448" href="Stlc.html#4434" class="Bound"
      >x</a
      ><a name="4449"
      > </a
      ><a name="4450" href="Maps.html#2509" class="Function Operator"
      >&#8799;</a
      ><a name="4451"
      > </a
      ><a name="4452" href="Stlc.html#4418" class="Bound"
      >x&#8242;</a
      ><a name="4454"
      >
</a
      ><a name="4455" class="Symbol"
      >...</a
      ><a name="4458"
      > </a
      ><a name="4459" class="Symbol"
      >|</a
      ><a name="4460"
      > </a
      ><a name="4461" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#520" class="InductiveConstructor"
      >yes</a
      ><a name="4464"
      > </a
      ><a name="4465" class="Symbol"
      >_</a
      ><a name="4466"
      > </a
      ><a name="4467" class="Symbol"
      >=</a
      ><a name="4468"
      > </a
      ><a name="4469" href="Stlc.html#3601" class="InductiveConstructor Operator"
      >&#955;[</a
      ><a name="4471"
      > </a
      ><a name="4472" href="Stlc.html#4418" class="Bound"
      >x&#8242;</a
      ><a name="4474"
      > </a
      ><a name="4475" href="Stlc.html#3601" class="InductiveConstructor Operator"
      >&#8758;</a
      ><a name="4476"
      > </a
      ><a name="4477" href="Stlc.html#4423" class="Bound"
      >A&#8242;</a
      ><a name="4479"
      > </a
      ><a name="4480" href="Stlc.html#3601" class="InductiveConstructor Operator"
      >]</a
      ><a name="4481"
      > </a
      ><a name="4482" href="Stlc.html#4428" class="Bound"
      >N&#8242;</a
      ><a name="4484"
      >
</a
      ><a name="4485" class="Symbol"
      >...</a
      ><a name="4488"
      > </a
      ><a name="4489" class="Symbol"
      >|</a
      ><a name="4490"
      > </a
      ><a name="4491" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#547" class="InductiveConstructor"
      >no</a
      ><a name="4493"
      >  </a
      ><a name="4495" class="Symbol"
      >_</a
      ><a name="4496"
      > </a
      ><a name="4497" class="Symbol"
      >=</a
      ><a name="4498"
      > </a
      ><a name="4499" href="Stlc.html#3601" class="InductiveConstructor Operator"
      >&#955;[</a
      ><a name="4501"
      > </a
      ><a name="4502" href="Stlc.html#4418" class="Bound"
      >x&#8242;</a
      ><a name="4504"
      > </a
      ><a name="4505" href="Stlc.html#3601" class="InductiveConstructor Operator"
      >&#8758;</a
      ><a name="4506"
      > </a
      ><a name="4507" href="Stlc.html#4423" class="Bound"
      >A&#8242;</a
      ><a name="4509"
      > </a
      ><a name="4510" href="Stlc.html#3601" class="InductiveConstructor Operator"
      >]</a
      ><a name="4511"
      > </a
      ><a name="4512" class="Symbol"
      >(</a
      ><a name="4513" href="Stlc.html#4428" class="Bound"
      >N&#8242;</a
      ><a name="4515"
      > </a
      ><a name="4516" href="Stlc.html#4315" class="Function Operator"
      >[</a
      ><a name="4517"
      > </a
      ><a name="4518" href="Stlc.html#4434" class="Bound"
      >x</a
      ><a name="4519"
      > </a
      ><a name="4520" href="Stlc.html#4315" class="Function Operator"
      >:=</a
      ><a name="4522"
      > </a
      ><a name="4523" href="Stlc.html#4439" class="Bound"
      >V</a
      ><a name="4524"
      > </a
      ><a name="4525" href="Stlc.html#4315" class="Function Operator"
      >]</a
      ><a name="4526" class="Symbol"
      >)</a
      ><a name="4527"
      >
</a
      ><a name="4528" class="Symbol"
      >(</a
      ><a name="4529" href="Stlc.html#4529" class="Bound"
      >L&#8242;</a
      ><a name="4531"
      > </a
      ><a name="4532" href="Stlc.html#3637" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="4533"
      > </a
      ><a name="4534" href="Stlc.html#4534" class="Bound"
      >M&#8242;</a
      ><a name="4536" class="Symbol"
      >)</a
      ><a name="4537"
      > </a
      ><a name="4538" href="Stlc.html#4315" class="Function Operator"
      >[</a
      ><a name="4539"
      > </a
      ><a name="4540" href="Stlc.html#4540" class="Bound"
      >x</a
      ><a name="4541"
      > </a
      ><a name="4542" href="Stlc.html#4315" class="Function Operator"
      >:=</a
      ><a name="4544"
      > </a
      ><a name="4545" href="Stlc.html#4545" class="Bound"
      >V</a
      ><a name="4546"
      > </a
      ><a name="4547" href="Stlc.html#4315" class="Function Operator"
      >]</a
      ><a name="4548"
      > </a
      ><a name="4549" class="Symbol"
      >=</a
      ><a name="4550"
      >  </a
      ><a name="4552" class="Symbol"
      >(</a
      ><a name="4553" href="Stlc.html#4529" class="Bound"
      >L&#8242;</a
      ><a name="4555"
      > </a
      ><a name="4556" href="Stlc.html#4315" class="Function Operator"
      >[</a
      ><a name="4557"
      > </a
      ><a name="4558" href="Stlc.html#4540" class="Bound"
      >x</a
      ><a name="4559"
      > </a
      ><a name="4560" href="Stlc.html#4315" class="Function Operator"
      >:=</a
      ><a name="4562"
      > </a
      ><a name="4563" href="Stlc.html#4545" class="Bound"
      >V</a
      ><a name="4564"
      > </a
      ><a name="4565" href="Stlc.html#4315" class="Function Operator"
      >]</a
      ><a name="4566" class="Symbol"
      >)</a
      ><a name="4567"
      > </a
      ><a name="4568" href="Stlc.html#3637" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="4569"
      > </a
      ><a name="4570" class="Symbol"
      >(</a
      ><a name="4571" href="Stlc.html#4534" class="Bound"
      >M&#8242;</a
      ><a name="4573"
      > </a
      ><a name="4574" href="Stlc.html#4315" class="Function Operator"
      >[</a
      ><a name="4575"
      > </a
      ><a name="4576" href="Stlc.html#4540" class="Bound"
      >x</a
      ><a name="4577"
      > </a
      ><a name="4578" href="Stlc.html#4315" class="Function Operator"
      >:=</a
      ><a name="4580"
      > </a
      ><a name="4581" href="Stlc.html#4545" class="Bound"
      >V</a
      ><a name="4582"
      > </a
      ><a name="4583" href="Stlc.html#4315" class="Function Operator"
      >]</a
      ><a name="4584" class="Symbol"
      >)</a
      ><a name="4585"
      >
</a
      ><a name="4586" class="Symbol"
      >(</a
      ><a name="4587" href="Stlc.html#3664" class="InductiveConstructor"
      >true</a
      ><a name="4591" class="Symbol"
      >)</a
      ><a name="4592"
      > </a
      ><a name="4593" href="Stlc.html#4315" class="Function Operator"
      >[</a
      ><a name="4594"
      > </a
      ><a name="4595" href="Stlc.html#4595" class="Bound"
      >x</a
      ><a name="4596"
      > </a
      ><a name="4597" href="Stlc.html#4315" class="Function Operator"
      >:=</a
      ><a name="4599"
      > </a
      ><a name="4600" href="Stlc.html#4600" class="Bound"
      >V</a
      ><a name="4601"
      > </a
      ><a name="4602" href="Stlc.html#4315" class="Function Operator"
      >]</a
      ><a name="4603"
      > </a
      ><a name="4604" class="Symbol"
      >=</a
      ><a name="4605"
      > </a
      ><a name="4606" href="Stlc.html#3664" class="InductiveConstructor"
      >true</a
      ><a name="4610"
      >
</a
      ><a name="4611" class="Symbol"
      >(</a
      ><a name="4612" href="Stlc.html#3678" class="InductiveConstructor"
      >false</a
      ><a name="4617" class="Symbol"
      >)</a
      ><a name="4618"
      > </a
      ><a name="4619" href="Stlc.html#4315" class="Function Operator"
      >[</a
      ><a name="4620"
      > </a
      ><a name="4621" href="Stlc.html#4621" class="Bound"
      >x</a
      ><a name="4622"
      > </a
      ><a name="4623" href="Stlc.html#4315" class="Function Operator"
      >:=</a
      ><a name="4625"
      > </a
      ><a name="4626" href="Stlc.html#4626" class="Bound"
      >V</a
      ><a name="4627"
      > </a
      ><a name="4628" href="Stlc.html#4315" class="Function Operator"
      >]</a
      ><a name="4629"
      > </a
      ><a name="4630" class="Symbol"
      >=</a
      ><a name="4631"
      > </a
      ><a name="4632" href="Stlc.html#3678" class="InductiveConstructor"
      >false</a
      ><a name="4637"
      >
</a
      ><a name="4638" class="Symbol"
      >(</a
      ><a name="4639" href="Stlc.html#3693" class="InductiveConstructor Operator"
      >if</a
      ><a name="4641"
      > </a
      ><a name="4642" href="Stlc.html#4642" class="Bound"
      >L&#8242;</a
      ><a name="4644"
      > </a
      ><a name="4645" href="Stlc.html#3693" class="InductiveConstructor Operator"
      >then</a
      ><a name="4649"
      > </a
      ><a name="4650" href="Stlc.html#4650" class="Bound"
      >M&#8242;</a
      ><a name="4652"
      > </a
      ><a name="4653" href="Stlc.html#3693" class="InductiveConstructor Operator"
      >else</a
      ><a name="4657"
      > </a
      ><a name="4658" href="Stlc.html#4658" class="Bound"
      >N&#8242;</a
      ><a name="4660" class="Symbol"
      >)</a
      ><a name="4661"
      > </a
      ><a name="4662" href="Stlc.html#4315" class="Function Operator"
      >[</a
      ><a name="4663"
      > </a
      ><a name="4664" href="Stlc.html#4664" class="Bound"
      >x</a
      ><a name="4665"
      > </a
      ><a name="4666" href="Stlc.html#4315" class="Function Operator"
      >:=</a
      ><a name="4668"
      > </a
      ><a name="4669" href="Stlc.html#4669" class="Bound"
      >V</a
      ><a name="4670"
      > </a
      ><a name="4671" href="Stlc.html#4315" class="Function Operator"
      >]</a
      ><a name="4672"
      > </a
      ><a name="4673" class="Symbol"
      >=</a
      ><a name="4674"
      > </a
      ><a name="4675" href="Stlc.html#3693" class="InductiveConstructor Operator"
      >if</a
      ><a name="4677"
      > </a
      ><a name="4678" class="Symbol"
      >(</a
      ><a name="4679" href="Stlc.html#4642" class="Bound"
      >L&#8242;</a
      ><a name="4681"
      > </a
      ><a name="4682" href="Stlc.html#4315" class="Function Operator"
      >[</a
      ><a name="4683"
      > </a
      ><a name="4684" href="Stlc.html#4664" class="Bound"
      >x</a
      ><a name="4685"
      > </a
      ><a name="4686" href="Stlc.html#4315" class="Function Operator"
      >:=</a
      ><a name="4688"
      > </a
      ><a name="4689" href="Stlc.html#4669" class="Bound"
      >V</a
      ><a name="4690"
      > </a
      ><a name="4691" href="Stlc.html#4315" class="Function Operator"
      >]</a
      ><a name="4692" class="Symbol"
      >)</a
      ><a name="4693"
      > </a
      ><a name="4694" href="Stlc.html#3693" class="InductiveConstructor Operator"
      >then</a
      ><a name="4698"
      > </a
      ><a name="4699" class="Symbol"
      >(</a
      ><a name="4700" href="Stlc.html#4650" class="Bound"
      >M&#8242;</a
      ><a name="4702"
      > </a
      ><a name="4703" href="Stlc.html#4315" class="Function Operator"
      >[</a
      ><a name="4704"
      > </a
      ><a name="4705" href="Stlc.html#4664" class="Bound"
      >x</a
      ><a name="4706"
      > </a
      ><a name="4707" href="Stlc.html#4315" class="Function Operator"
      >:=</a
      ><a name="4709"
      > </a
      ><a name="4710" href="Stlc.html#4669" class="Bound"
      >V</a
      ><a name="4711"
      > </a
      ><a name="4712" href="Stlc.html#4315" class="Function Operator"
      >]</a
      ><a name="4713" class="Symbol"
      >)</a
      ><a name="4714"
      > </a
      ><a name="4715" href="Stlc.html#3693" class="InductiveConstructor Operator"
      >else</a
      ><a name="4719"
      > </a
      ><a name="4720" class="Symbol"
      >(</a
      ><a name="4721" href="Stlc.html#4658" class="Bound"
      >N&#8242;</a
      ><a name="4723"
      > </a
      ><a name="4724" href="Stlc.html#4315" class="Function Operator"
      >[</a
      ><a name="4725"
      > </a
      ><a name="4726" href="Stlc.html#4664" class="Bound"
      >x</a
      ><a name="4727"
      > </a
      ><a name="4728" href="Stlc.html#4315" class="Function Operator"
      >:=</a
      ><a name="4730"
      > </a
      ><a name="4731" href="Stlc.html#4669" class="Bound"
      >V</a
      ><a name="4732"
      > </a
      ><a name="4733" href="Stlc.html#4315" class="Function Operator"
      >]</a
      ><a name="4734" class="Symbol"
      >)</a
      >

</pre>

## Reduction rules

<pre class="Agda">

<a name="4781" class="Keyword"
      >infix</a
      ><a name="4786"
      > </a
      ><a name="4787" class="Number"
      >10</a
      ><a name="4789"
      > </a
      ><a name="4790" href="Stlc.html#4801" class="Datatype Operator"
      >_&#10233;_</a
      ><a name="4793"
      > 

</a
      ><a name="4796" class="Keyword"
      >data</a
      ><a name="4800"
      > </a
      ><a name="4801" href="Stlc.html#4801" class="Datatype Operator"
      >_&#10233;_</a
      ><a name="4804"
      > </a
      ><a name="4805" class="Symbol"
      >:</a
      ><a name="4806"
      > </a
      ><a name="4807" href="Stlc.html#3566" class="Datatype"
      >Term</a
      ><a name="4811"
      > </a
      ><a name="4812" class="Symbol"
      >&#8594;</a
      ><a name="4813"
      > </a
      ><a name="4814" href="Stlc.html#3566" class="Datatype"
      >Term</a
      ><a name="4818"
      > </a
      ><a name="4819" class="Symbol"
      >&#8594;</a
      ><a name="4820"
      > </a
      ><a name="4821" class="PrimitiveType"
      >Set</a
      ><a name="4824"
      > </a
      ><a name="4825" class="Keyword"
      >where</a
      ><a name="4830"
      >
  </a
      ><a name="4833" href="Stlc.html#4833" class="InductiveConstructor"
      >&#946;&#955;&#183;</a
      ><a name="4836"
      > </a
      ><a name="4837" class="Symbol"
      >:</a
      ><a name="4838"
      > </a
      ><a name="4839" class="Symbol"
      >&#8704;</a
      ><a name="4840"
      > </a
      ><a name="4841" class="Symbol"
      >{</a
      ><a name="4842" href="Stlc.html#4842" class="Bound"
      >x</a
      ><a name="4843"
      > </a
      ><a name="4844" href="Stlc.html#4844" class="Bound"
      >A</a
      ><a name="4845"
      > </a
      ><a name="4846" href="Stlc.html#4846" class="Bound"
      >N</a
      ><a name="4847"
      > </a
      ><a name="4848" href="Stlc.html#4848" class="Bound"
      >V</a
      ><a name="4849" class="Symbol"
      >}</a
      ><a name="4850"
      > </a
      ><a name="4851" class="Symbol"
      >&#8594;</a
      ><a name="4852"
      > </a
      ><a name="4853" href="Stlc.html#4144" class="Datatype"
      >Value</a
      ><a name="4858"
      > </a
      ><a name="4859" href="Stlc.html#4848" class="Bound"
      >V</a
      ><a name="4860"
      > </a
      ><a name="4861" class="Symbol"
      >&#8594;</a
      ><a name="4862"
      >
    </a
      ><a name="4867" class="Symbol"
      >(</a
      ><a name="4868" href="Stlc.html#3601" class="InductiveConstructor Operator"
      >&#955;[</a
      ><a name="4870"
      > </a
      ><a name="4871" href="Stlc.html#4842" class="Bound"
      >x</a
      ><a name="4872"
      > </a
      ><a name="4873" href="Stlc.html#3601" class="InductiveConstructor Operator"
      >&#8758;</a
      ><a name="4874"
      > </a
      ><a name="4875" href="Stlc.html#4844" class="Bound"
      >A</a
      ><a name="4876"
      > </a
      ><a name="4877" href="Stlc.html#3601" class="InductiveConstructor Operator"
      >]</a
      ><a name="4878"
      > </a
      ><a name="4879" href="Stlc.html#4846" class="Bound"
      >N</a
      ><a name="4880" class="Symbol"
      >)</a
      ><a name="4881"
      > </a
      ><a name="4882" href="Stlc.html#3637" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="4883"
      > </a
      ><a name="4884" href="Stlc.html#4848" class="Bound"
      >V</a
      ><a name="4885"
      > </a
      ><a name="4886" href="Stlc.html#4801" class="Datatype Operator"
      >&#10233;</a
      ><a name="4887"
      > </a
      ><a name="4888" href="Stlc.html#4846" class="Bound"
      >N</a
      ><a name="4889"
      > </a
      ><a name="4890" href="Stlc.html#4315" class="Function Operator"
      >[</a
      ><a name="4891"
      > </a
      ><a name="4892" href="Stlc.html#4842" class="Bound"
      >x</a
      ><a name="4893"
      > </a
      ><a name="4894" href="Stlc.html#4315" class="Function Operator"
      >:=</a
      ><a name="4896"
      > </a
      ><a name="4897" href="Stlc.html#4848" class="Bound"
      >V</a
      ><a name="4898"
      > </a
      ><a name="4899" href="Stlc.html#4315" class="Function Operator"
      >]</a
      ><a name="4900"
      >
  </a
      ><a name="4903" href="Stlc.html#4903" class="InductiveConstructor"
      >&#958;&#183;&#8321;</a
      ><a name="4906"
      > </a
      ><a name="4907" class="Symbol"
      >:</a
      ><a name="4908"
      > </a
      ><a name="4909" class="Symbol"
      >&#8704;</a
      ><a name="4910"
      > </a
      ><a name="4911" class="Symbol"
      >{</a
      ><a name="4912" href="Stlc.html#4912" class="Bound"
      >L</a
      ><a name="4913"
      > </a
      ><a name="4914" href="Stlc.html#4914" class="Bound"
      >L&#8242;</a
      ><a name="4916"
      > </a
      ><a name="4917" href="Stlc.html#4917" class="Bound"
      >M</a
      ><a name="4918" class="Symbol"
      >}</a
      ><a name="4919"
      > </a
      ><a name="4920" class="Symbol"
      >&#8594;</a
      ><a name="4921"
      >
    </a
      ><a name="4926" href="Stlc.html#4912" class="Bound"
      >L</a
      ><a name="4927"
      > </a
      ><a name="4928" href="Stlc.html#4801" class="Datatype Operator"
      >&#10233;</a
      ><a name="4929"
      > </a
      ><a name="4930" href="Stlc.html#4914" class="Bound"
      >L&#8242;</a
      ><a name="4932"
      > </a
      ><a name="4933" class="Symbol"
      >&#8594;</a
      ><a name="4934"
      >
    </a
      ><a name="4939" href="Stlc.html#4912" class="Bound"
      >L</a
      ><a name="4940"
      > </a
      ><a name="4941" href="Stlc.html#3637" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="4942"
      > </a
      ><a name="4943" href="Stlc.html#4917" class="Bound"
      >M</a
      ><a name="4944"
      > </a
      ><a name="4945" href="Stlc.html#4801" class="Datatype Operator"
      >&#10233;</a
      ><a name="4946"
      > </a
      ><a name="4947" href="Stlc.html#4914" class="Bound"
      >L&#8242;</a
      ><a name="4949"
      > </a
      ><a name="4950" href="Stlc.html#3637" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="4951"
      > </a
      ><a name="4952" href="Stlc.html#4917" class="Bound"
      >M</a
      ><a name="4953"
      >
  </a
      ><a name="4956" href="Stlc.html#4956" class="InductiveConstructor"
      >&#958;&#183;&#8322;</a
      ><a name="4959"
      > </a
      ><a name="4960" class="Symbol"
      >:</a
      ><a name="4961"
      > </a
      ><a name="4962" class="Symbol"
      >&#8704;</a
      ><a name="4963"
      > </a
      ><a name="4964" class="Symbol"
      >{</a
      ><a name="4965" href="Stlc.html#4965" class="Bound"
      >V</a
      ><a name="4966"
      > </a
      ><a name="4967" href="Stlc.html#4967" class="Bound"
      >M</a
      ><a name="4968"
      > </a
      ><a name="4969" href="Stlc.html#4969" class="Bound"
      >M&#8242;</a
      ><a name="4971" class="Symbol"
      >}</a
      ><a name="4972"
      > </a
      ><a name="4973" class="Symbol"
      >&#8594;</a
      ><a name="4974"
      >
    </a
      ><a name="4979" href="Stlc.html#4144" class="Datatype"
      >Value</a
      ><a name="4984"
      > </a
      ><a name="4985" href="Stlc.html#4965" class="Bound"
      >V</a
      ><a name="4986"
      > </a
      ><a name="4987" class="Symbol"
      >&#8594;</a
      ><a name="4988"
      >
    </a
      ><a name="4993" href="Stlc.html#4967" class="Bound"
      >M</a
      ><a name="4994"
      > </a
      ><a name="4995" href="Stlc.html#4801" class="Datatype Operator"
      >&#10233;</a
      ><a name="4996"
      > </a
      ><a name="4997" href="Stlc.html#4969" class="Bound"
      >M&#8242;</a
      ><a name="4999"
      > </a
      ><a name="5000" class="Symbol"
      >&#8594;</a
      ><a name="5001"
      >
    </a
      ><a name="5006" href="Stlc.html#4965" class="Bound"
      >V</a
      ><a name="5007"
      > </a
      ><a name="5008" href="Stlc.html#3637" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="5009"
      > </a
      ><a name="5010" href="Stlc.html#4967" class="Bound"
      >M</a
      ><a name="5011"
      > </a
      ><a name="5012" href="Stlc.html#4801" class="Datatype Operator"
      >&#10233;</a
      ><a name="5013"
      > </a
      ><a name="5014" href="Stlc.html#4965" class="Bound"
      >V</a
      ><a name="5015"
      > </a
      ><a name="5016" href="Stlc.html#3637" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="5017"
      > </a
      ><a name="5018" href="Stlc.html#4969" class="Bound"
      >M&#8242;</a
      ><a name="5020"
      >
  </a
      ><a name="5023" href="Stlc.html#5023" class="InductiveConstructor"
      >&#946;if-true</a
      ><a name="5031"
      > </a
      ><a name="5032" class="Symbol"
      >:</a
      ><a name="5033"
      > </a
      ><a name="5034" class="Symbol"
      >&#8704;</a
      ><a name="5035"
      > </a
      ><a name="5036" class="Symbol"
      >{</a
      ><a name="5037" href="Stlc.html#5037" class="Bound"
      >M</a
      ><a name="5038"
      > </a
      ><a name="5039" href="Stlc.html#5039" class="Bound"
      >N</a
      ><a name="5040" class="Symbol"
      >}</a
      ><a name="5041"
      > </a
      ><a name="5042" class="Symbol"
      >&#8594;</a
      ><a name="5043"
      >
    </a
      ><a name="5048" href="Stlc.html#3693" class="InductiveConstructor Operator"
      >if</a
      ><a name="5050"
      > </a
      ><a name="5051" href="Stlc.html#3664" class="InductiveConstructor"
      >true</a
      ><a name="5055"
      > </a
      ><a name="5056" href="Stlc.html#3693" class="InductiveConstructor Operator"
      >then</a
      ><a name="5060"
      > </a
      ><a name="5061" href="Stlc.html#5037" class="Bound"
      >M</a
      ><a name="5062"
      > </a
      ><a name="5063" href="Stlc.html#3693" class="InductiveConstructor Operator"
      >else</a
      ><a name="5067"
      > </a
      ><a name="5068" href="Stlc.html#5039" class="Bound"
      >N</a
      ><a name="5069"
      > </a
      ><a name="5070" href="Stlc.html#4801" class="Datatype Operator"
      >&#10233;</a
      ><a name="5071"
      > </a
      ><a name="5072" href="Stlc.html#5037" class="Bound"
      >M</a
      ><a name="5073"
      >
  </a
      ><a name="5076" href="Stlc.html#5076" class="InductiveConstructor"
      >&#946;if-false</a
      ><a name="5085"
      > </a
      ><a name="5086" class="Symbol"
      >:</a
      ><a name="5087"
      > </a
      ><a name="5088" class="Symbol"
      >&#8704;</a
      ><a name="5089"
      > </a
      ><a name="5090" class="Symbol"
      >{</a
      ><a name="5091" href="Stlc.html#5091" class="Bound"
      >M</a
      ><a name="5092"
      > </a
      ><a name="5093" href="Stlc.html#5093" class="Bound"
      >N</a
      ><a name="5094" class="Symbol"
      >}</a
      ><a name="5095"
      > </a
      ><a name="5096" class="Symbol"
      >&#8594;</a
      ><a name="5097"
      >
    </a
      ><a name="5102" href="Stlc.html#3693" class="InductiveConstructor Operator"
      >if</a
      ><a name="5104"
      > </a
      ><a name="5105" href="Stlc.html#3678" class="InductiveConstructor"
      >false</a
      ><a name="5110"
      > </a
      ><a name="5111" href="Stlc.html#3693" class="InductiveConstructor Operator"
      >then</a
      ><a name="5115"
      > </a
      ><a name="5116" href="Stlc.html#5091" class="Bound"
      >M</a
      ><a name="5117"
      > </a
      ><a name="5118" href="Stlc.html#3693" class="InductiveConstructor Operator"
      >else</a
      ><a name="5122"
      > </a
      ><a name="5123" href="Stlc.html#5093" class="Bound"
      >N</a
      ><a name="5124"
      > </a
      ><a name="5125" href="Stlc.html#4801" class="Datatype Operator"
      >&#10233;</a
      ><a name="5126"
      > </a
      ><a name="5127" href="Stlc.html#5093" class="Bound"
      >N</a
      ><a name="5128"
      >
  </a
      ><a name="5131" href="Stlc.html#5131" class="InductiveConstructor"
      >&#958;if</a
      ><a name="5134"
      > </a
      ><a name="5135" class="Symbol"
      >:</a
      ><a name="5136"
      > </a
      ><a name="5137" class="Symbol"
      >&#8704;</a
      ><a name="5138"
      > </a
      ><a name="5139" class="Symbol"
      >{</a
      ><a name="5140" href="Stlc.html#5140" class="Bound"
      >L</a
      ><a name="5141"
      > </a
      ><a name="5142" href="Stlc.html#5142" class="Bound"
      >L&#8242;</a
      ><a name="5144"
      > </a
      ><a name="5145" href="Stlc.html#5145" class="Bound"
      >M</a
      ><a name="5146"
      > </a
      ><a name="5147" href="Stlc.html#5147" class="Bound"
      >N</a
      ><a name="5148" class="Symbol"
      >}</a
      ><a name="5149"
      > </a
      ><a name="5150" class="Symbol"
      >&#8594;</a
      ><a name="5151"
      >
    </a
      ><a name="5156" href="Stlc.html#5140" class="Bound"
      >L</a
      ><a name="5157"
      > </a
      ><a name="5158" href="Stlc.html#4801" class="Datatype Operator"
      >&#10233;</a
      ><a name="5159"
      > </a
      ><a name="5160" href="Stlc.html#5142" class="Bound"
      >L&#8242;</a
      ><a name="5162"
      > </a
      ><a name="5163" class="Symbol"
      >&#8594;</a
      ><a name="5164"
      >    
    </a
      ><a name="5173" href="Stlc.html#3693" class="InductiveConstructor Operator"
      >if</a
      ><a name="5175"
      > </a
      ><a name="5176" href="Stlc.html#5140" class="Bound"
      >L</a
      ><a name="5177"
      > </a
      ><a name="5178" href="Stlc.html#3693" class="InductiveConstructor Operator"
      >then</a
      ><a name="5182"
      > </a
      ><a name="5183" href="Stlc.html#5145" class="Bound"
      >M</a
      ><a name="5184"
      > </a
      ><a name="5185" href="Stlc.html#3693" class="InductiveConstructor Operator"
      >else</a
      ><a name="5189"
      > </a
      ><a name="5190" href="Stlc.html#5147" class="Bound"
      >N</a
      ><a name="5191"
      > </a
      ><a name="5192" href="Stlc.html#4801" class="Datatype Operator"
      >&#10233;</a
      ><a name="5193"
      > </a
      ><a name="5194" href="Stlc.html#3693" class="InductiveConstructor Operator"
      >if</a
      ><a name="5196"
      > </a
      ><a name="5197" href="Stlc.html#5142" class="Bound"
      >L&#8242;</a
      ><a name="5199"
      > </a
      ><a name="5200" href="Stlc.html#3693" class="InductiveConstructor Operator"
      >then</a
      ><a name="5204"
      > </a
      ><a name="5205" href="Stlc.html#5145" class="Bound"
      >M</a
      ><a name="5206"
      > </a
      ><a name="5207" href="Stlc.html#3693" class="InductiveConstructor Operator"
      >else</a
      ><a name="5211"
      > </a
      ><a name="5212" href="Stlc.html#5147" class="Bound"
      >N</a
      >

</pre>

## Reflexive and transitive closure


<pre class="Agda">

<a name="5277" class="Keyword"
      >infix</a
      ><a name="5282"
      > </a
      ><a name="5283" class="Number"
      >10</a
      ><a name="5285"
      > </a
      ><a name="5286" href="Stlc.html#5326" class="Datatype Operator"
      >_&#10233;*_</a
      ><a name="5290"
      > 
</a
      ><a name="5292" class="Keyword"
      >infixr</a
      ><a name="5298"
      > </a
      ><a name="5299" class="Number"
      >2</a
      ><a name="5300"
      > </a
      ><a name="5301" href="Stlc.html#5379" class="InductiveConstructor Operator"
      >_&#10233;&#10216;_&#10217;_</a
      ><a name="5307"
      >
</a
      ><a name="5308" class="Keyword"
      >infix</a
      ><a name="5313"
      >  </a
      ><a name="5315" class="Number"
      >3</a
      ><a name="5316"
      > </a
      ><a name="5317" href="Stlc.html#5359" class="InductiveConstructor Operator"
      >_&#8718;</a
      ><a name="5319"
      >

</a
      ><a name="5321" class="Keyword"
      >data</a
      ><a name="5325"
      > </a
      ><a name="5326" href="Stlc.html#5326" class="Datatype Operator"
      >_&#10233;*_</a
      ><a name="5330"
      > </a
      ><a name="5331" class="Symbol"
      >:</a
      ><a name="5332"
      > </a
      ><a name="5333" href="Stlc.html#3566" class="Datatype"
      >Term</a
      ><a name="5337"
      > </a
      ><a name="5338" class="Symbol"
      >&#8594;</a
      ><a name="5339"
      > </a
      ><a name="5340" href="Stlc.html#3566" class="Datatype"
      >Term</a
      ><a name="5344"
      > </a
      ><a name="5345" class="Symbol"
      >&#8594;</a
      ><a name="5346"
      > </a
      ><a name="5347" class="PrimitiveType"
      >Set</a
      ><a name="5350"
      > </a
      ><a name="5351" class="Keyword"
      >where</a
      ><a name="5356"
      >
  </a
      ><a name="5359" href="Stlc.html#5359" class="InductiveConstructor Operator"
      >_&#8718;</a
      ><a name="5361"
      > </a
      ><a name="5362" class="Symbol"
      >:</a
      ><a name="5363"
      > </a
      ><a name="5364" class="Symbol"
      >&#8704;</a
      ><a name="5365"
      > </a
      ><a name="5366" href="Stlc.html#5366" class="Bound"
      >M</a
      ><a name="5367"
      > </a
      ><a name="5368" class="Symbol"
      >&#8594;</a
      ><a name="5369"
      > </a
      ><a name="5370" href="Stlc.html#5366" class="Bound"
      >M</a
      ><a name="5371"
      > </a
      ><a name="5372" href="Stlc.html#5326" class="Datatype Operator"
      >&#10233;*</a
      ><a name="5374"
      > </a
      ><a name="5375" href="Stlc.html#5366" class="Bound"
      >M</a
      ><a name="5376"
      >
  </a
      ><a name="5379" href="Stlc.html#5379" class="InductiveConstructor Operator"
      >_&#10233;&#10216;_&#10217;_</a
      ><a name="5385"
      > </a
      ><a name="5386" class="Symbol"
      >:</a
      ><a name="5387"
      > </a
      ><a name="5388" class="Symbol"
      >&#8704;</a
      ><a name="5389"
      > </a
      ><a name="5390" href="Stlc.html#5390" class="Bound"
      >L</a
      ><a name="5391"
      > </a
      ><a name="5392" class="Symbol"
      >{</a
      ><a name="5393" href="Stlc.html#5393" class="Bound"
      >M</a
      ><a name="5394"
      > </a
      ><a name="5395" href="Stlc.html#5395" class="Bound"
      >N</a
      ><a name="5396" class="Symbol"
      >}</a
      ><a name="5397"
      > </a
      ><a name="5398" class="Symbol"
      >&#8594;</a
      ><a name="5399"
      > </a
      ><a name="5400" href="Stlc.html#5390" class="Bound"
      >L</a
      ><a name="5401"
      > </a
      ><a name="5402" href="Stlc.html#4801" class="Datatype Operator"
      >&#10233;</a
      ><a name="5403"
      > </a
      ><a name="5404" href="Stlc.html#5393" class="Bound"
      >M</a
      ><a name="5405"
      > </a
      ><a name="5406" class="Symbol"
      >&#8594;</a
      ><a name="5407"
      > </a
      ><a name="5408" href="Stlc.html#5393" class="Bound"
      >M</a
      ><a name="5409"
      > </a
      ><a name="5410" href="Stlc.html#5326" class="Datatype Operator"
      >&#10233;*</a
      ><a name="5412"
      > </a
      ><a name="5413" href="Stlc.html#5395" class="Bound"
      >N</a
      ><a name="5414"
      > </a
      ><a name="5415" class="Symbol"
      >&#8594;</a
      ><a name="5416"
      > </a
      ><a name="5417" href="Stlc.html#5390" class="Bound"
      >L</a
      ><a name="5418"
      > </a
      ><a name="5419" href="Stlc.html#5326" class="Datatype Operator"
      >&#10233;*</a
      ><a name="5421"
      > </a
      ><a name="5422" href="Stlc.html#5395" class="Bound"
      >N</a
      ><a name="5423"
      >  

</a
      ><a name="5427" href="Stlc.html#5427" class="Function"
      >reduction&#8321;</a
      ><a name="5437"
      > </a
      ><a name="5438" class="Symbol"
      >:</a
      ><a name="5439"
      > </a
      ><a name="5440" href="Stlc.html#3988" class="Function"
      >not</a
      ><a name="5443"
      > </a
      ><a name="5444" href="Stlc.html#3637" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="5445"
      > </a
      ><a name="5446" href="Stlc.html#3664" class="InductiveConstructor"
      >true</a
      ><a name="5450"
      > </a
      ><a name="5451" href="Stlc.html#5326" class="Datatype Operator"
      >&#10233;*</a
      ><a name="5453"
      > </a
      ><a name="5454" href="Stlc.html#3678" class="InductiveConstructor"
      >false</a
      ><a name="5459"
      >
</a
      ><a name="5460" href="Stlc.html#5427" class="Function"
      >reduction&#8321;</a
      ><a name="5470"
      > </a
      ><a name="5471" class="Symbol"
      >=</a
      ><a name="5472"
      >
    </a
      ><a name="5477" href="Stlc.html#3988" class="Function"
      >not</a
      ><a name="5480"
      > </a
      ><a name="5481" href="Stlc.html#3637" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="5482"
      > </a
      ><a name="5483" href="Stlc.html#3664" class="InductiveConstructor"
      >true</a
      ><a name="5487"
      >
  </a
      ><a name="5490" href="Stlc.html#5379" class="InductiveConstructor Operator"
      >&#10233;&#10216;</a
      ><a name="5492"
      > </a
      ><a name="5493" href="Stlc.html#4833" class="InductiveConstructor"
      >&#946;&#955;&#183;</a
      ><a name="5496"
      > </a
      ><a name="5497" href="Stlc.html#4220" class="InductiveConstructor"
      >value-true</a
      ><a name="5507"
      > </a
      ><a name="5508" href="Stlc.html#5379" class="InductiveConstructor Operator"
      >&#10217;</a
      ><a name="5509"
      >
    </a
      ><a name="5514" href="Stlc.html#3693" class="InductiveConstructor Operator"
      >if</a
      ><a name="5516"
      > </a
      ><a name="5517" href="Stlc.html#3664" class="InductiveConstructor"
      >true</a
      ><a name="5521"
      > </a
      ><a name="5522" href="Stlc.html#3693" class="InductiveConstructor Operator"
      >then</a
      ><a name="5526"
      > </a
      ><a name="5527" href="Stlc.html#3678" class="InductiveConstructor"
      >false</a
      ><a name="5532"
      > </a
      ><a name="5533" href="Stlc.html#3693" class="InductiveConstructor Operator"
      >else</a
      ><a name="5537"
      > </a
      ><a name="5538" href="Stlc.html#3664" class="InductiveConstructor"
      >true</a
      ><a name="5542"
      >
  </a
      ><a name="5545" href="Stlc.html#5379" class="InductiveConstructor Operator"
      >&#10233;&#10216;</a
      ><a name="5547"
      > </a
      ><a name="5548" href="Stlc.html#5023" class="InductiveConstructor"
      >&#946;if-true</a
      ><a name="5556"
      > </a
      ><a name="5557" href="Stlc.html#5379" class="InductiveConstructor Operator"
      >&#10217;</a
      ><a name="5558"
      >
    </a
      ><a name="5563" href="Stlc.html#3678" class="InductiveConstructor"
      >false</a
      ><a name="5568"
      >
  </a
      ><a name="5571" href="Stlc.html#5359" class="InductiveConstructor Operator"
      >&#8718;</a
      ><a name="5572"
      >

</a
      ><a name="5574" href="Stlc.html#5574" class="Function"
      >reduction&#8322;</a
      ><a name="5584"
      > </a
      ><a name="5585" class="Symbol"
      >:</a
      ><a name="5586"
      > </a
      ><a name="5587" href="Stlc.html#3992" class="Function"
      >two</a
      ><a name="5590"
      > </a
      ><a name="5591" href="Stlc.html#3637" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="5592"
      > </a
      ><a name="5593" href="Stlc.html#3988" class="Function"
      >not</a
      ><a name="5596"
      > </a
      ><a name="5597" href="Stlc.html#3637" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="5598"
      > </a
      ><a name="5599" href="Stlc.html#3664" class="InductiveConstructor"
      >true</a
      ><a name="5603"
      > </a
      ><a name="5604" href="Stlc.html#5326" class="Datatype Operator"
      >&#10233;*</a
      ><a name="5606"
      > </a
      ><a name="5607" href="Stlc.html#3664" class="InductiveConstructor"
      >true</a
      ><a name="5611"
      >
</a
      ><a name="5612" href="Stlc.html#5574" class="Function"
      >reduction&#8322;</a
      ><a name="5622"
      > </a
      ><a name="5623" class="Symbol"
      >=</a
      ><a name="5624"
      >
    </a
      ><a name="5629" href="Stlc.html#3992" class="Function"
      >two</a
      ><a name="5632"
      > </a
      ><a name="5633" href="Stlc.html#3637" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="5634"
      > </a
      ><a name="5635" href="Stlc.html#3988" class="Function"
      >not</a
      ><a name="5638"
      > </a
      ><a name="5639" href="Stlc.html#3637" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="5640"
      > </a
      ><a name="5641" href="Stlc.html#3664" class="InductiveConstructor"
      >true</a
      ><a name="5645"
      >
  </a
      ><a name="5648" href="Stlc.html#5379" class="InductiveConstructor Operator"
      >&#10233;&#10216;</a
      ><a name="5650"
      > </a
      ><a name="5651" href="Stlc.html#4903" class="InductiveConstructor"
      >&#958;&#183;&#8321;</a
      ><a name="5654"
      > </a
      ><a name="5655" class="Symbol"
      >(</a
      ><a name="5656" href="Stlc.html#4833" class="InductiveConstructor"
      >&#946;&#955;&#183;</a
      ><a name="5659"
      > </a
      ><a name="5660" href="Stlc.html#4171" class="InductiveConstructor"
      >value-&#955;</a
      ><a name="5667" class="Symbol"
      >)</a
      ><a name="5668"
      > </a
      ><a name="5669" href="Stlc.html#5379" class="InductiveConstructor Operator"
      >&#10217;</a
      ><a name="5670"
      >
    </a
      ><a name="5675" class="Symbol"
      >(</a
      ><a name="5676" href="Stlc.html#3601" class="InductiveConstructor Operator"
      >&#955;[</a
      ><a name="5678"
      > </a
      ><a name="5679" href="Stlc.html#3958" class="Function"
      >x</a
      ><a name="5680"
      > </a
      ><a name="5681" href="Stlc.html#3601" class="InductiveConstructor Operator"
      >&#8758;</a
      ><a name="5682"
      > </a
      ><a name="5683" href="Stlc.html#2621" class="InductiveConstructor"
      >&#120121;</a
      ><a name="5684"
      > </a
      ><a name="5685" href="Stlc.html#3601" class="InductiveConstructor Operator"
      >]</a
      ><a name="5686"
      > </a
      ><a name="5687" href="Stlc.html#3988" class="Function"
      >not</a
      ><a name="5690"
      > </a
      ><a name="5691" href="Stlc.html#3637" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="5692"
      > </a
      ><a name="5693" class="Symbol"
      >(</a
      ><a name="5694" href="Stlc.html#3988" class="Function"
      >not</a
      ><a name="5697"
      > </a
      ><a name="5698" href="Stlc.html#3637" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="5699"
      > </a
      ><a name="5700" href="Stlc.html#3585" class="InductiveConstructor"
      >`</a
      ><a name="5701"
      > </a
      ><a name="5702" href="Stlc.html#3958" class="Function"
      >x</a
      ><a name="5703" class="Symbol"
      >))</a
      ><a name="5705"
      > </a
      ><a name="5706" href="Stlc.html#3637" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="5707"
      > </a
      ><a name="5708" href="Stlc.html#3664" class="InductiveConstructor"
      >true</a
      ><a name="5712"
      >
  </a
      ><a name="5715" href="Stlc.html#5379" class="InductiveConstructor Operator"
      >&#10233;&#10216;</a
      ><a name="5717"
      > </a
      ><a name="5718" href="Stlc.html#4833" class="InductiveConstructor"
      >&#946;&#955;&#183;</a
      ><a name="5721"
      > </a
      ><a name="5722" href="Stlc.html#4220" class="InductiveConstructor"
      >value-true</a
      ><a name="5732"
      > </a
      ><a name="5733" href="Stlc.html#5379" class="InductiveConstructor Operator"
      >&#10217;</a
      ><a name="5734"
      >
    </a
      ><a name="5739" href="Stlc.html#3988" class="Function"
      >not</a
      ><a name="5742"
      > </a
      ><a name="5743" href="Stlc.html#3637" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="5744"
      > </a
      ><a name="5745" class="Symbol"
      >(</a
      ><a name="5746" href="Stlc.html#3988" class="Function"
      >not</a
      ><a name="5749"
      > </a
      ><a name="5750" href="Stlc.html#3637" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="5751"
      > </a
      ><a name="5752" href="Stlc.html#3664" class="InductiveConstructor"
      >true</a
      ><a name="5756" class="Symbol"
      >)</a
      ><a name="5757"
      >
  </a
      ><a name="5760" href="Stlc.html#5379" class="InductiveConstructor Operator"
      >&#10233;&#10216;</a
      ><a name="5762"
      > </a
      ><a name="5763" href="Stlc.html#4956" class="InductiveConstructor"
      >&#958;&#183;&#8322;</a
      ><a name="5766"
      > </a
      ><a name="5767" href="Stlc.html#4171" class="InductiveConstructor"
      >value-&#955;</a
      ><a name="5774"
      > </a
      ><a name="5775" class="Symbol"
      >(</a
      ><a name="5776" href="Stlc.html#4833" class="InductiveConstructor"
      >&#946;&#955;&#183;</a
      ><a name="5779"
      > </a
      ><a name="5780" href="Stlc.html#4220" class="InductiveConstructor"
      >value-true</a
      ><a name="5790" class="Symbol"
      >)</a
      ><a name="5791"
      > </a
      ><a name="5792" href="Stlc.html#5379" class="InductiveConstructor Operator"
      >&#10217;</a
      ><a name="5793"
      >
    </a
      ><a name="5798" href="Stlc.html#3988" class="Function"
      >not</a
      ><a name="5801"
      > </a
      ><a name="5802" href="Stlc.html#3637" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="5803"
      > </a
      ><a name="5804" class="Symbol"
      >(</a
      ><a name="5805" href="Stlc.html#3693" class="InductiveConstructor Operator"
      >if</a
      ><a name="5807"
      > </a
      ><a name="5808" href="Stlc.html#3664" class="InductiveConstructor"
      >true</a
      ><a name="5812"
      > </a
      ><a name="5813" href="Stlc.html#3693" class="InductiveConstructor Operator"
      >then</a
      ><a name="5817"
      > </a
      ><a name="5818" href="Stlc.html#3678" class="InductiveConstructor"
      >false</a
      ><a name="5823"
      > </a
      ><a name="5824" href="Stlc.html#3693" class="InductiveConstructor Operator"
      >else</a
      ><a name="5828"
      > </a
      ><a name="5829" href="Stlc.html#3664" class="InductiveConstructor"
      >true</a
      ><a name="5833" class="Symbol"
      >)</a
      ><a name="5834"
      >
  </a
      ><a name="5837" href="Stlc.html#5379" class="InductiveConstructor Operator"
      >&#10233;&#10216;</a
      ><a name="5839"
      > </a
      ><a name="5840" href="Stlc.html#4956" class="InductiveConstructor"
      >&#958;&#183;&#8322;</a
      ><a name="5843"
      > </a
      ><a name="5844" href="Stlc.html#4171" class="InductiveConstructor"
      >value-&#955;</a
      ><a name="5851"
      > </a
      ><a name="5852" href="Stlc.html#5023" class="InductiveConstructor"
      >&#946;if-true</a
      ><a name="5860"
      >  </a
      ><a name="5862" href="Stlc.html#5379" class="InductiveConstructor Operator"
      >&#10217;</a
      ><a name="5863"
      >
    </a
      ><a name="5868" href="Stlc.html#3988" class="Function"
      >not</a
      ><a name="5871"
      > </a
      ><a name="5872" href="Stlc.html#3637" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="5873"
      > </a
      ><a name="5874" href="Stlc.html#3678" class="InductiveConstructor"
      >false</a
      ><a name="5879"
      >
  </a
      ><a name="5882" href="Stlc.html#5379" class="InductiveConstructor Operator"
      >&#10233;&#10216;</a
      ><a name="5884"
      > </a
      ><a name="5885" href="Stlc.html#4833" class="InductiveConstructor"
      >&#946;&#955;&#183;</a
      ><a name="5888"
      > </a
      ><a name="5889" href="Stlc.html#4247" class="InductiveConstructor"
      >value-false</a
      ><a name="5900"
      > </a
      ><a name="5901" href="Stlc.html#5379" class="InductiveConstructor Operator"
      >&#10217;</a
      ><a name="5902"
      >
    </a
      ><a name="5907" href="Stlc.html#3693" class="InductiveConstructor Operator"
      >if</a
      ><a name="5909"
      > </a
      ><a name="5910" href="Stlc.html#3678" class="InductiveConstructor"
      >false</a
      ><a name="5915"
      > </a
      ><a name="5916" href="Stlc.html#3693" class="InductiveConstructor Operator"
      >then</a
      ><a name="5920"
      > </a
      ><a name="5921" href="Stlc.html#3678" class="InductiveConstructor"
      >false</a
      ><a name="5926"
      > </a
      ><a name="5927" href="Stlc.html#3693" class="InductiveConstructor Operator"
      >else</a
      ><a name="5931"
      > </a
      ><a name="5932" href="Stlc.html#3664" class="InductiveConstructor"
      >true</a
      ><a name="5936"
      >
  </a
      ><a name="5939" href="Stlc.html#5379" class="InductiveConstructor Operator"
      >&#10233;&#10216;</a
      ><a name="5941"
      > </a
      ><a name="5942" href="Stlc.html#5076" class="InductiveConstructor"
      >&#946;if-false</a
      ><a name="5951"
      > </a
      ><a name="5952" href="Stlc.html#5379" class="InductiveConstructor Operator"
      >&#10217;</a
      ><a name="5953"
      >
    </a
      ><a name="5958" href="Stlc.html#3664" class="InductiveConstructor"
      >true</a
      ><a name="5962"
      >
  </a
      ><a name="5965" href="Stlc.html#5359" class="InductiveConstructor Operator"
      >&#8718;</a
      >

</pre>

Much of the above, though not all, can be filled in using C-c C-r and C-c C-s.



## Type rules

<pre class="Agda">

<a name="6089" href="Stlc.html#6089" class="Function"
      >Context</a
      ><a name="6096"
      > </a
      ><a name="6097" class="Symbol"
      >:</a
      ><a name="6098"
      > </a
      ><a name="6099" class="PrimitiveType"
      >Set</a
      ><a name="6102"
      >
</a
      ><a name="6103" href="Stlc.html#6089" class="Function"
      >Context</a
      ><a name="6110"
      > </a
      ><a name="6111" class="Symbol"
      >=</a
      ><a name="6112"
      > </a
      ><a name="6113" href="Maps.html#10132" class="Function"
      >PartialMap</a
      ><a name="6123"
      > </a
      ><a name="6124" href="Stlc.html#2575" class="Datatype"
      >Type</a
      ><a name="6128"
      >

</a
      ><a name="6130" class="Keyword"
      >infix</a
      ><a name="6135"
      > </a
      ><a name="6136" class="Number"
      >10</a
      ><a name="6138"
      > </a
      ><a name="6139" href="Stlc.html#6151" class="Datatype Operator"
      >_&#8866;_&#8758;_</a
      ><a name="6144"
      >

</a
      ><a name="6146" class="Keyword"
      >data</a
      ><a name="6150"
      > </a
      ><a name="6151" href="Stlc.html#6151" class="Datatype Operator"
      >_&#8866;_&#8758;_</a
      ><a name="6156"
      > </a
      ><a name="6157" class="Symbol"
      >:</a
      ><a name="6158"
      > </a
      ><a name="6159" href="Stlc.html#6089" class="Function"
      >Context</a
      ><a name="6166"
      > </a
      ><a name="6167" class="Symbol"
      >&#8594;</a
      ><a name="6168"
      > </a
      ><a name="6169" href="Stlc.html#3566" class="Datatype"
      >Term</a
      ><a name="6173"
      > </a
      ><a name="6174" class="Symbol"
      >&#8594;</a
      ><a name="6175"
      > </a
      ><a name="6176" href="Stlc.html#2575" class="Datatype"
      >Type</a
      ><a name="6180"
      > </a
      ><a name="6181" class="Symbol"
      >&#8594;</a
      ><a name="6182"
      > </a
      ><a name="6183" class="PrimitiveType"
      >Set</a
      ><a name="6186"
      > </a
      ><a name="6187" class="Keyword"
      >where</a
      ><a name="6192"
      >
  </a
      ><a name="6195" href="Stlc.html#6195" class="InductiveConstructor"
      >Ax</a
      ><a name="6197"
      > </a
      ><a name="6198" class="Symbol"
      >:</a
      ><a name="6199"
      > </a
      ><a name="6200" class="Symbol"
      >&#8704;</a
      ><a name="6201"
      > </a
      ><a name="6202" class="Symbol"
      >{</a
      ><a name="6203" href="Stlc.html#6203" class="Bound"
      >&#915;</a
      ><a name="6204"
      > </a
      ><a name="6205" href="Stlc.html#6205" class="Bound"
      >x</a
      ><a name="6206"
      > </a
      ><a name="6207" href="Stlc.html#6207" class="Bound"
      >A</a
      ><a name="6208" class="Symbol"
      >}</a
      ><a name="6209"
      > </a
      ><a name="6210" class="Symbol"
      >&#8594;</a
      ><a name="6211"
      >
    </a
      ><a name="6216" href="Stlc.html#6203" class="Bound"
      >&#915;</a
      ><a name="6217"
      > </a
      ><a name="6218" href="Stlc.html#6205" class="Bound"
      >x</a
      ><a name="6219"
      > </a
      ><a name="6220" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="6221"
      > </a
      ><a name="6222" href="https://agda.github.io/agda-stdlib/Data.Maybe.Base.html#373" class="InductiveConstructor"
      >just</a
      ><a name="6226"
      > </a
      ><a name="6227" href="Stlc.html#6207" class="Bound"
      >A</a
      ><a name="6228"
      > </a
      ><a name="6229" class="Symbol"
      >&#8594;</a
      ><a name="6230"
      >
    </a
      ><a name="6235" href="Stlc.html#6203" class="Bound"
      >&#915;</a
      ><a name="6236"
      > </a
      ><a name="6237" href="Stlc.html#6151" class="Datatype Operator"
      >&#8866;</a
      ><a name="6238"
      > </a
      ><a name="6239" href="Stlc.html#3585" class="InductiveConstructor"
      >`</a
      ><a name="6240"
      > </a
      ><a name="6241" href="Stlc.html#6205" class="Bound"
      >x</a
      ><a name="6242"
      > </a
      ><a name="6243" href="Stlc.html#6151" class="Datatype Operator"
      >&#8758;</a
      ><a name="6244"
      > </a
      ><a name="6245" href="Stlc.html#6207" class="Bound"
      >A</a
      ><a name="6246"
      >
  </a
      ><a name="6249" href="Stlc.html#6249" class="InductiveConstructor"
      >&#8658;-I</a
      ><a name="6252"
      > </a
      ><a name="6253" class="Symbol"
      >:</a
      ><a name="6254"
      > </a
      ><a name="6255" class="Symbol"
      >&#8704;</a
      ><a name="6256"
      > </a
      ><a name="6257" class="Symbol"
      >{</a
      ><a name="6258" href="Stlc.html#6258" class="Bound"
      >&#915;</a
      ><a name="6259"
      > </a
      ><a name="6260" href="Stlc.html#6260" class="Bound"
      >x</a
      ><a name="6261"
      > </a
      ><a name="6262" href="Stlc.html#6262" class="Bound"
      >N</a
      ><a name="6263"
      > </a
      ><a name="6264" href="Stlc.html#6264" class="Bound"
      >A</a
      ><a name="6265"
      > </a
      ><a name="6266" href="Stlc.html#6266" class="Bound"
      >B</a
      ><a name="6267" class="Symbol"
      >}</a
      ><a name="6268"
      > </a
      ><a name="6269" class="Symbol"
      >&#8594;</a
      ><a name="6270"
      >
    </a
      ><a name="6275" href="Stlc.html#6258" class="Bound"
      >&#915;</a
      ><a name="6276"
      > </a
      ><a name="6277" href="Maps.html#10368" class="Function Operator"
      >,</a
      ><a name="6278"
      > </a
      ><a name="6279" href="Stlc.html#6260" class="Bound"
      >x</a
      ><a name="6280"
      > </a
      ><a name="6281" href="Maps.html#10368" class="Function Operator"
      >&#8758;</a
      ><a name="6282"
      > </a
      ><a name="6283" href="Stlc.html#6264" class="Bound"
      >A</a
      ><a name="6284"
      > </a
      ><a name="6285" href="Stlc.html#6151" class="Datatype Operator"
      >&#8866;</a
      ><a name="6286"
      > </a
      ><a name="6287" href="Stlc.html#6262" class="Bound"
      >N</a
      ><a name="6288"
      > </a
      ><a name="6289" href="Stlc.html#6151" class="Datatype Operator"
      >&#8758;</a
      ><a name="6290"
      > </a
      ><a name="6291" href="Stlc.html#6266" class="Bound"
      >B</a
      ><a name="6292"
      > </a
      ><a name="6293" class="Symbol"
      >&#8594;</a
      ><a name="6294"
      >
    </a
      ><a name="6299" href="Stlc.html#6258" class="Bound"
      >&#915;</a
      ><a name="6300"
      > </a
      ><a name="6301" href="Stlc.html#6151" class="Datatype Operator"
      >&#8866;</a
      ><a name="6302"
      > </a
      ><a name="6303" href="Stlc.html#3601" class="InductiveConstructor Operator"
      >&#955;[</a
      ><a name="6305"
      > </a
      ><a name="6306" href="Stlc.html#6260" class="Bound"
      >x</a
      ><a name="6307"
      > </a
      ><a name="6308" href="Stlc.html#3601" class="InductiveConstructor Operator"
      >&#8758;</a
      ><a name="6309"
      > </a
      ><a name="6310" href="Stlc.html#6264" class="Bound"
      >A</a
      ><a name="6311"
      > </a
      ><a name="6312" href="Stlc.html#3601" class="InductiveConstructor Operator"
      >]</a
      ><a name="6313"
      > </a
      ><a name="6314" href="Stlc.html#6262" class="Bound"
      >N</a
      ><a name="6315"
      > </a
      ><a name="6316" href="Stlc.html#6151" class="Datatype Operator"
      >&#8758;</a
      ><a name="6317"
      > </a
      ><a name="6318" href="Stlc.html#6264" class="Bound"
      >A</a
      ><a name="6319"
      > </a
      ><a name="6320" href="Stlc.html#2594" class="InductiveConstructor Operator"
      >&#8658;</a
      ><a name="6321"
      > </a
      ><a name="6322" href="Stlc.html#6266" class="Bound"
      >B</a
      ><a name="6323"
      >
  </a
      ><a name="6326" href="Stlc.html#6326" class="InductiveConstructor"
      >&#8658;-E</a
      ><a name="6329"
      > </a
      ><a name="6330" class="Symbol"
      >:</a
      ><a name="6331"
      > </a
      ><a name="6332" class="Symbol"
      >&#8704;</a
      ><a name="6333"
      > </a
      ><a name="6334" class="Symbol"
      >{</a
      ><a name="6335" href="Stlc.html#6335" class="Bound"
      >&#915;</a
      ><a name="6336"
      > </a
      ><a name="6337" href="Stlc.html#6337" class="Bound"
      >L</a
      ><a name="6338"
      > </a
      ><a name="6339" href="Stlc.html#6339" class="Bound"
      >M</a
      ><a name="6340"
      > </a
      ><a name="6341" href="Stlc.html#6341" class="Bound"
      >A</a
      ><a name="6342"
      > </a
      ><a name="6343" href="Stlc.html#6343" class="Bound"
      >B</a
      ><a name="6344" class="Symbol"
      >}</a
      ><a name="6345"
      > </a
      ><a name="6346" class="Symbol"
      >&#8594;</a
      ><a name="6347"
      >
    </a
      ><a name="6352" href="Stlc.html#6335" class="Bound"
      >&#915;</a
      ><a name="6353"
      > </a
      ><a name="6354" href="Stlc.html#6151" class="Datatype Operator"
      >&#8866;</a
      ><a name="6355"
      > </a
      ><a name="6356" href="Stlc.html#6337" class="Bound"
      >L</a
      ><a name="6357"
      > </a
      ><a name="6358" href="Stlc.html#6151" class="Datatype Operator"
      >&#8758;</a
      ><a name="6359"
      > </a
      ><a name="6360" href="Stlc.html#6341" class="Bound"
      >A</a
      ><a name="6361"
      > </a
      ><a name="6362" href="Stlc.html#2594" class="InductiveConstructor Operator"
      >&#8658;</a
      ><a name="6363"
      > </a
      ><a name="6364" href="Stlc.html#6343" class="Bound"
      >B</a
      ><a name="6365"
      > </a
      ><a name="6366" class="Symbol"
      >&#8594;</a
      ><a name="6367"
      >
    </a
      ><a name="6372" href="Stlc.html#6335" class="Bound"
      >&#915;</a
      ><a name="6373"
      > </a
      ><a name="6374" href="Stlc.html#6151" class="Datatype Operator"
      >&#8866;</a
      ><a name="6375"
      > </a
      ><a name="6376" href="Stlc.html#6339" class="Bound"
      >M</a
      ><a name="6377"
      > </a
      ><a name="6378" href="Stlc.html#6151" class="Datatype Operator"
      >&#8758;</a
      ><a name="6379"
      > </a
      ><a name="6380" href="Stlc.html#6341" class="Bound"
      >A</a
      ><a name="6381"
      > </a
      ><a name="6382" class="Symbol"
      >&#8594;</a
      ><a name="6383"
      >
    </a
      ><a name="6388" href="Stlc.html#6335" class="Bound"
      >&#915;</a
      ><a name="6389"
      > </a
      ><a name="6390" href="Stlc.html#6151" class="Datatype Operator"
      >&#8866;</a
      ><a name="6391"
      > </a
      ><a name="6392" href="Stlc.html#6337" class="Bound"
      >L</a
      ><a name="6393"
      > </a
      ><a name="6394" href="Stlc.html#3637" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="6395"
      > </a
      ><a name="6396" href="Stlc.html#6339" class="Bound"
      >M</a
      ><a name="6397"
      > </a
      ><a name="6398" href="Stlc.html#6151" class="Datatype Operator"
      >&#8758;</a
      ><a name="6399"
      > </a
      ><a name="6400" href="Stlc.html#6343" class="Bound"
      >B</a
      ><a name="6401"
      >
  </a
      ><a name="6404" href="Stlc.html#6404" class="InductiveConstructor"
      >&#120121;-I&#8321;</a
      ><a name="6408"
      > </a
      ><a name="6409" class="Symbol"
      >:</a
      ><a name="6410"
      > </a
      ><a name="6411" class="Symbol"
      >&#8704;</a
      ><a name="6412"
      > </a
      ><a name="6413" class="Symbol"
      >{</a
      ><a name="6414" href="Stlc.html#6414" class="Bound"
      >&#915;</a
      ><a name="6415" class="Symbol"
      >}</a
      ><a name="6416"
      > </a
      ><a name="6417" class="Symbol"
      >&#8594;</a
      ><a name="6418"
      >
    </a
      ><a name="6423" href="Stlc.html#6414" class="Bound"
      >&#915;</a
      ><a name="6424"
      > </a
      ><a name="6425" href="Stlc.html#6151" class="Datatype Operator"
      >&#8866;</a
      ><a name="6426"
      > </a
      ><a name="6427" href="Stlc.html#3664" class="InductiveConstructor"
      >true</a
      ><a name="6431"
      > </a
      ><a name="6432" href="Stlc.html#6151" class="Datatype Operator"
      >&#8758;</a
      ><a name="6433"
      > </a
      ><a name="6434" href="Stlc.html#2621" class="InductiveConstructor"
      >&#120121;</a
      ><a name="6435"
      >
  </a
      ><a name="6438" href="Stlc.html#6438" class="InductiveConstructor"
      >&#120121;-I&#8322;</a
      ><a name="6442"
      > </a
      ><a name="6443" class="Symbol"
      >:</a
      ><a name="6444"
      > </a
      ><a name="6445" class="Symbol"
      >&#8704;</a
      ><a name="6446"
      > </a
      ><a name="6447" class="Symbol"
      >{</a
      ><a name="6448" href="Stlc.html#6448" class="Bound"
      >&#915;</a
      ><a name="6449" class="Symbol"
      >}</a
      ><a name="6450"
      > </a
      ><a name="6451" class="Symbol"
      >&#8594;</a
      ><a name="6452"
      >
    </a
      ><a name="6457" href="Stlc.html#6448" class="Bound"
      >&#915;</a
      ><a name="6458"
      > </a
      ><a name="6459" href="Stlc.html#6151" class="Datatype Operator"
      >&#8866;</a
      ><a name="6460"
      > </a
      ><a name="6461" href="Stlc.html#3678" class="InductiveConstructor"
      >false</a
      ><a name="6466"
      > </a
      ><a name="6467" href="Stlc.html#6151" class="Datatype Operator"
      >&#8758;</a
      ><a name="6468"
      > </a
      ><a name="6469" href="Stlc.html#2621" class="InductiveConstructor"
      >&#120121;</a
      ><a name="6470"
      >
  </a
      ><a name="6473" href="Stlc.html#6473" class="InductiveConstructor"
      >&#120121;-E</a
      ><a name="6476"
      > </a
      ><a name="6477" class="Symbol"
      >:</a
      ><a name="6478"
      > </a
      ><a name="6479" class="Symbol"
      >&#8704;</a
      ><a name="6480"
      > </a
      ><a name="6481" class="Symbol"
      >{</a
      ><a name="6482" href="Stlc.html#6482" class="Bound"
      >&#915;</a
      ><a name="6483"
      > </a
      ><a name="6484" href="Stlc.html#6484" class="Bound"
      >L</a
      ><a name="6485"
      > </a
      ><a name="6486" href="Stlc.html#6486" class="Bound"
      >M</a
      ><a name="6487"
      > </a
      ><a name="6488" href="Stlc.html#6488" class="Bound"
      >N</a
      ><a name="6489"
      > </a
      ><a name="6490" href="Stlc.html#6490" class="Bound"
      >A</a
      ><a name="6491" class="Symbol"
      >}</a
      ><a name="6492"
      > </a
      ><a name="6493" class="Symbol"
      >&#8594;</a
      ><a name="6494"
      >
    </a
      ><a name="6499" href="Stlc.html#6482" class="Bound"
      >&#915;</a
      ><a name="6500"
      > </a
      ><a name="6501" href="Stlc.html#6151" class="Datatype Operator"
      >&#8866;</a
      ><a name="6502"
      > </a
      ><a name="6503" href="Stlc.html#6484" class="Bound"
      >L</a
      ><a name="6504"
      > </a
      ><a name="6505" href="Stlc.html#6151" class="Datatype Operator"
      >&#8758;</a
      ><a name="6506"
      > </a
      ><a name="6507" href="Stlc.html#2621" class="InductiveConstructor"
      >&#120121;</a
      ><a name="6508"
      > </a
      ><a name="6509" class="Symbol"
      >&#8594;</a
      ><a name="6510"
      >
    </a
      ><a name="6515" href="Stlc.html#6482" class="Bound"
      >&#915;</a
      ><a name="6516"
      > </a
      ><a name="6517" href="Stlc.html#6151" class="Datatype Operator"
      >&#8866;</a
      ><a name="6518"
      > </a
      ><a name="6519" href="Stlc.html#6486" class="Bound"
      >M</a
      ><a name="6520"
      > </a
      ><a name="6521" href="Stlc.html#6151" class="Datatype Operator"
      >&#8758;</a
      ><a name="6522"
      > </a
      ><a name="6523" href="Stlc.html#6490" class="Bound"
      >A</a
      ><a name="6524"
      > </a
      ><a name="6525" class="Symbol"
      >&#8594;</a
      ><a name="6526"
      >
    </a
      ><a name="6531" href="Stlc.html#6482" class="Bound"
      >&#915;</a
      ><a name="6532"
      > </a
      ><a name="6533" href="Stlc.html#6151" class="Datatype Operator"
      >&#8866;</a
      ><a name="6534"
      > </a
      ><a name="6535" href="Stlc.html#6488" class="Bound"
      >N</a
      ><a name="6536"
      > </a
      ><a name="6537" href="Stlc.html#6151" class="Datatype Operator"
      >&#8758;</a
      ><a name="6538"
      > </a
      ><a name="6539" href="Stlc.html#6490" class="Bound"
      >A</a
      ><a name="6540"
      > </a
      ><a name="6541" class="Symbol"
      >&#8594;</a
      ><a name="6542"
      >
    </a
      ><a name="6547" href="Stlc.html#6482" class="Bound"
      >&#915;</a
      ><a name="6548"
      > </a
      ><a name="6549" href="Stlc.html#6151" class="Datatype Operator"
      >&#8866;</a
      ><a name="6550"
      > </a
      ><a name="6551" href="Stlc.html#3693" class="InductiveConstructor Operator"
      >if</a
      ><a name="6553"
      > </a
      ><a name="6554" href="Stlc.html#6484" class="Bound"
      >L</a
      ><a name="6555"
      > </a
      ><a name="6556" href="Stlc.html#3693" class="InductiveConstructor Operator"
      >then</a
      ><a name="6560"
      > </a
      ><a name="6561" href="Stlc.html#6486" class="Bound"
      >M</a
      ><a name="6562"
      > </a
      ><a name="6563" href="Stlc.html#3693" class="InductiveConstructor Operator"
      >else</a
      ><a name="6567"
      > </a
      ><a name="6568" href="Stlc.html#6488" class="Bound"
      >N</a
      ><a name="6569"
      > </a
      ><a name="6570" href="Stlc.html#6151" class="Datatype Operator"
      >&#8758;</a
      ><a name="6571"
      > </a
      ><a name="6572" href="Stlc.html#6490" class="Bound"
      >A</a
      >

</pre>

## Example type derivations

<pre class="Agda">

<a name="6632" href="Stlc.html#6632" class="Function"
      >typing&#8321;</a
      ><a name="6639"
      > </a
      ><a name="6640" class="Symbol"
      >:</a
      ><a name="6641"
      > </a
      ><a name="6642" href="Maps.html#10265" class="Function"
      >&#8709;</a
      ><a name="6643"
      > </a
      ><a name="6644" href="Stlc.html#6151" class="Datatype Operator"
      >&#8866;</a
      ><a name="6645"
      > </a
      ><a name="6646" href="Stlc.html#3988" class="Function"
      >not</a
      ><a name="6649"
      > </a
      ><a name="6650" href="Stlc.html#6151" class="Datatype Operator"
      >&#8758;</a
      ><a name="6651"
      > </a
      ><a name="6652" href="Stlc.html#2621" class="InductiveConstructor"
      >&#120121;</a
      ><a name="6653"
      > </a
      ><a name="6654" href="Stlc.html#2594" class="InductiveConstructor Operator"
      >&#8658;</a
      ><a name="6655"
      > </a
      ><a name="6656" href="Stlc.html#2621" class="InductiveConstructor"
      >&#120121;</a
      ><a name="6657"
      >
</a
      ><a name="6658" href="Stlc.html#6632" class="Function"
      >typing&#8321;</a
      ><a name="6665"
      > </a
      ><a name="6666" class="Symbol"
      >=</a
      ><a name="6667"
      > </a
      ><a name="6668" href="Stlc.html#6249" class="InductiveConstructor"
      >&#8658;-I</a
      ><a name="6671"
      > </a
      ><a name="6672" class="Symbol"
      >(</a
      ><a name="6673" href="Stlc.html#6473" class="InductiveConstructor"
      >&#120121;-E</a
      ><a name="6676"
      > </a
      ><a name="6677" class="Symbol"
      >(</a
      ><a name="6678" href="Stlc.html#6195" class="InductiveConstructor"
      >Ax</a
      ><a name="6680"
      > </a
      ><a name="6681" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="6685" class="Symbol"
      >)</a
      ><a name="6686"
      > </a
      ><a name="6687" href="Stlc.html#6438" class="InductiveConstructor"
      >&#120121;-I&#8322;</a
      ><a name="6691"
      > </a
      ><a name="6692" href="Stlc.html#6404" class="InductiveConstructor"
      >&#120121;-I&#8321;</a
      ><a name="6696" class="Symbol"
      >)</a
      ><a name="6697"
      >

</a
      ><a name="6699" href="Stlc.html#6699" class="Function"
      >typing&#8322;</a
      ><a name="6706"
      > </a
      ><a name="6707" class="Symbol"
      >:</a
      ><a name="6708"
      > </a
      ><a name="6709" href="Maps.html#10265" class="Function"
      >&#8709;</a
      ><a name="6710"
      > </a
      ><a name="6711" href="Stlc.html#6151" class="Datatype Operator"
      >&#8866;</a
      ><a name="6712"
      > </a
      ><a name="6713" href="Stlc.html#3992" class="Function"
      >two</a
      ><a name="6716"
      > </a
      ><a name="6717" href="Stlc.html#6151" class="Datatype Operator"
      >&#8758;</a
      ><a name="6718"
      > </a
      ><a name="6719" class="Symbol"
      >(</a
      ><a name="6720" href="Stlc.html#2621" class="InductiveConstructor"
      >&#120121;</a
      ><a name="6721"
      > </a
      ><a name="6722" href="Stlc.html#2594" class="InductiveConstructor Operator"
      >&#8658;</a
      ><a name="6723"
      > </a
      ><a name="6724" href="Stlc.html#2621" class="InductiveConstructor"
      >&#120121;</a
      ><a name="6725" class="Symbol"
      >)</a
      ><a name="6726"
      > </a
      ><a name="6727" href="Stlc.html#2594" class="InductiveConstructor Operator"
      >&#8658;</a
      ><a name="6728"
      > </a
      ><a name="6729" href="Stlc.html#2621" class="InductiveConstructor"
      >&#120121;</a
      ><a name="6730"
      > </a
      ><a name="6731" href="Stlc.html#2594" class="InductiveConstructor Operator"
      >&#8658;</a
      ><a name="6732"
      > </a
      ><a name="6733" href="Stlc.html#2621" class="InductiveConstructor"
      >&#120121;</a
      ><a name="6734"
      >
</a
      ><a name="6735" href="Stlc.html#6699" class="Function"
      >typing&#8322;</a
      ><a name="6742"
      > </a
      ><a name="6743" class="Symbol"
      >=</a
      ><a name="6744"
      > </a
      ><a name="6745" href="Stlc.html#6249" class="InductiveConstructor"
      >&#8658;-I</a
      ><a name="6748"
      > </a
      ><a name="6749" class="Symbol"
      >(</a
      ><a name="6750" href="Stlc.html#6249" class="InductiveConstructor"
      >&#8658;-I</a
      ><a name="6753"
      > </a
      ><a name="6754" class="Symbol"
      >(</a
      ><a name="6755" href="Stlc.html#6326" class="InductiveConstructor"
      >&#8658;-E</a
      ><a name="6758"
      > </a
      ><a name="6759" class="Symbol"
      >(</a
      ><a name="6760" href="Stlc.html#6195" class="InductiveConstructor"
      >Ax</a
      ><a name="6762"
      > </a
      ><a name="6763" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="6767" class="Symbol"
      >)</a
      ><a name="6768"
      > </a
      ><a name="6769" class="Symbol"
      >(</a
      ><a name="6770" href="Stlc.html#6326" class="InductiveConstructor"
      >&#8658;-E</a
      ><a name="6773"
      > </a
      ><a name="6774" class="Symbol"
      >(</a
      ><a name="6775" href="Stlc.html#6195" class="InductiveConstructor"
      >Ax</a
      ><a name="6777"
      > </a
      ><a name="6778" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="6782" class="Symbol"
      >)</a
      ><a name="6783"
      > </a
      ><a name="6784" class="Symbol"
      >(</a
      ><a name="6785" href="Stlc.html#6195" class="InductiveConstructor"
      >Ax</a
      ><a name="6787"
      > </a
      ><a name="6788" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="6792" class="Symbol"
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


