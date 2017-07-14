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

    A, B, C ::= A ⇒ B | 𝔹

And here it is formalised in Agda.

<pre class="Agda">

<a name="2511" class="Keyword"
      >infixr</a
      ><a name="2517"
      > </a
      ><a name="2518" class="Number"
      >20</a
      ><a name="2520"
      > </a
      ><a name="2521" href="Stlc.html#2550" class="InductiveConstructor Operator"
      >_&#8658;_</a
      ><a name="2524"
      >

</a
      ><a name="2526" class="Keyword"
      >data</a
      ><a name="2530"
      > </a
      ><a name="2531" href="Stlc.html#2531" class="Datatype"
      >Type</a
      ><a name="2535"
      > </a
      ><a name="2536" class="Symbol"
      >:</a
      ><a name="2537"
      > </a
      ><a name="2538" class="PrimitiveType"
      >Set</a
      ><a name="2541"
      > </a
      ><a name="2542" class="Keyword"
      >where</a
      ><a name="2547"
      >
  </a
      ><a name="2550" href="Stlc.html#2550" class="InductiveConstructor Operator"
      >_&#8658;_</a
      ><a name="2553"
      > </a
      ><a name="2554" class="Symbol"
      >:</a
      ><a name="2555"
      > </a
      ><a name="2556" href="Stlc.html#2531" class="Datatype"
      >Type</a
      ><a name="2560"
      > </a
      ><a name="2561" class="Symbol"
      >&#8594;</a
      ><a name="2562"
      > </a
      ><a name="2563" href="Stlc.html#2531" class="Datatype"
      >Type</a
      ><a name="2567"
      > </a
      ><a name="2568" class="Symbol"
      >&#8594;</a
      ><a name="2569"
      > </a
      ><a name="2570" href="Stlc.html#2531" class="Datatype"
      >Type</a
      ><a name="2574"
      >
  </a
      ><a name="2577" href="Stlc.html#2577" class="InductiveConstructor"
      >&#120121;</a
      ><a name="2578"
      > </a
      ><a name="2579" class="Symbol"
      >:</a
      ><a name="2580"
      > </a
      ><a name="2581" href="Stlc.html#2531" class="Datatype"
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




<pre class="Agda">

<a name="3423" class="Keyword"
      >infixl</a
      ><a name="3429"
      > </a
      ><a name="3430" class="Number"
      >20</a
      ><a name="3432"
      > </a
      ><a name="3433" href="Stlc.html#3556" class="InductiveConstructor Operator"
      >_&#183;_</a
      ><a name="3436"
      >
</a
      ><a name="3437" class="Keyword"
      >infix</a
      ><a name="3442"
      >  </a
      ><a name="3444" class="Number"
      >15</a
      ><a name="3446"
      > </a
      ><a name="3447" href="Stlc.html#3520" class="InductiveConstructor Operator"
      >&#955;[_&#8758;_]_</a
      ><a name="3454"
      >
</a
      ><a name="3455" class="Keyword"
      >infix</a
      ><a name="3460"
      >  </a
      ><a name="3462" class="Number"
      >15</a
      ><a name="3464"
      > </a
      ><a name="3465" href="Stlc.html#3612" class="InductiveConstructor Operator"
      >if_then_else_</a
      ><a name="3478"
      >

</a
      ><a name="3480" class="Keyword"
      >data</a
      ><a name="3484"
      > </a
      ><a name="3485" href="Stlc.html#3485" class="Datatype"
      >Term</a
      ><a name="3489"
      > </a
      ><a name="3490" class="Symbol"
      >:</a
      ><a name="3491"
      > </a
      ><a name="3492" class="PrimitiveType"
      >Set</a
      ><a name="3495"
      > </a
      ><a name="3496" class="Keyword"
      >where</a
      ><a name="3501"
      >
  </a
      ><a name="3504" href="Stlc.html#3504" class="InductiveConstructor"
      >`</a
      ><a name="3505"
      > </a
      ><a name="3506" class="Symbol"
      >:</a
      ><a name="3507"
      > </a
      ><a name="3508" href="Maps.html#2171" class="Datatype"
      >Id</a
      ><a name="3510"
      > </a
      ><a name="3511" class="Symbol"
      >&#8594;</a
      ><a name="3512"
      > </a
      ><a name="3513" href="Stlc.html#3485" class="Datatype"
      >Term</a
      ><a name="3517"
      >
  </a
      ><a name="3520" href="Stlc.html#3520" class="InductiveConstructor Operator"
      >&#955;[_&#8758;_]_</a
      ><a name="3527"
      > </a
      ><a name="3528" class="Symbol"
      >:</a
      ><a name="3529"
      > </a
      ><a name="3530" href="Maps.html#2171" class="Datatype"
      >Id</a
      ><a name="3532"
      > </a
      ><a name="3533" class="Symbol"
      >&#8594;</a
      ><a name="3534"
      > </a
      ><a name="3535" href="Stlc.html#2531" class="Datatype"
      >Type</a
      ><a name="3539"
      > </a
      ><a name="3540" class="Symbol"
      >&#8594;</a
      ><a name="3541"
      > </a
      ><a name="3542" href="Stlc.html#3485" class="Datatype"
      >Term</a
      ><a name="3546"
      > </a
      ><a name="3547" class="Symbol"
      >&#8594;</a
      ><a name="3548"
      > </a
      ><a name="3549" href="Stlc.html#3485" class="Datatype"
      >Term</a
      ><a name="3553"
      >
  </a
      ><a name="3556" href="Stlc.html#3556" class="InductiveConstructor Operator"
      >_&#183;_</a
      ><a name="3559"
      > </a
      ><a name="3560" class="Symbol"
      >:</a
      ><a name="3561"
      > </a
      ><a name="3562" href="Stlc.html#3485" class="Datatype"
      >Term</a
      ><a name="3566"
      > </a
      ><a name="3567" class="Symbol"
      >&#8594;</a
      ><a name="3568"
      > </a
      ><a name="3569" href="Stlc.html#3485" class="Datatype"
      >Term</a
      ><a name="3573"
      > </a
      ><a name="3574" class="Symbol"
      >&#8594;</a
      ><a name="3575"
      > </a
      ><a name="3576" href="Stlc.html#3485" class="Datatype"
      >Term</a
      ><a name="3580"
      >
  </a
      ><a name="3583" href="Stlc.html#3583" class="InductiveConstructor"
      >true</a
      ><a name="3587"
      > </a
      ><a name="3588" class="Symbol"
      >:</a
      ><a name="3589"
      > </a
      ><a name="3590" href="Stlc.html#3485" class="Datatype"
      >Term</a
      ><a name="3594"
      >
  </a
      ><a name="3597" href="Stlc.html#3597" class="InductiveConstructor"
      >false</a
      ><a name="3602"
      > </a
      ><a name="3603" class="Symbol"
      >:</a
      ><a name="3604"
      > </a
      ><a name="3605" href="Stlc.html#3485" class="Datatype"
      >Term</a
      ><a name="3609"
      >
  </a
      ><a name="3612" href="Stlc.html#3612" class="InductiveConstructor Operator"
      >if_then_else_</a
      ><a name="3625"
      > </a
      ><a name="3626" class="Symbol"
      >:</a
      ><a name="3627"
      > </a
      ><a name="3628" href="Stlc.html#3485" class="Datatype"
      >Term</a
      ><a name="3632"
      > </a
      ><a name="3633" class="Symbol"
      >&#8594;</a
      ><a name="3634"
      > </a
      ><a name="3635" href="Stlc.html#3485" class="Datatype"
      >Term</a
      ><a name="3639"
      > </a
      ><a name="3640" class="Symbol"
      >&#8594;</a
      ><a name="3641"
      > </a
      ><a name="3642" href="Stlc.html#3485" class="Datatype"
      >Term</a
      ><a name="3646"
      > </a
      ><a name="3647" class="Symbol"
      >&#8594;</a
      ><a name="3648"
      > </a
      ><a name="3649" href="Stlc.html#3485" class="Datatype"
      >Term</a
      >

</pre>

Each type introduces its own constructs, which come in pairs,
one to introduce (or construct) values of the type, and one to eliminate
(or deconstruct) them.

CONTINUE FROM HERE



Example terms.
<pre class="Agda">

<a name="3875" href="Stlc.html#3875" class="Function"
      >f</a
      ><a name="3876"
      > </a
      ><a name="3877" href="Stlc.html#3877" class="Function"
      >x</a
      ><a name="3878"
      > </a
      ><a name="3879" class="Symbol"
      >:</a
      ><a name="3880"
      > </a
      ><a name="3881" href="Maps.html#2171" class="Datatype"
      >Id</a
      ><a name="3883"
      >
</a
      ><a name="3884" href="Stlc.html#3875" class="Function"
      >f</a
      ><a name="3885"
      >  </a
      ><a name="3887" class="Symbol"
      >=</a
      ><a name="3888"
      >  </a
      ><a name="3890" href="Maps.html#2188" class="InductiveConstructor"
      >id</a
      ><a name="3892"
      > </a
      ><a name="3893" class="Number"
      >0</a
      ><a name="3894"
      >
</a
      ><a name="3895" href="Stlc.html#3877" class="Function"
      >x</a
      ><a name="3896"
      >  </a
      ><a name="3898" class="Symbol"
      >=</a
      ><a name="3899"
      >  </a
      ><a name="3901" href="Maps.html#2188" class="InductiveConstructor"
      >id</a
      ><a name="3903"
      > </a
      ><a name="3904" class="Number"
      >1</a
      ><a name="3905"
      >

</a
      ><a name="3907" href="Stlc.html#3907" class="Function"
      >not</a
      ><a name="3910"
      > </a
      ><a name="3911" href="Stlc.html#3911" class="Function"
      >two</a
      ><a name="3914"
      > </a
      ><a name="3915" class="Symbol"
      >:</a
      ><a name="3916"
      > </a
      ><a name="3917" href="Stlc.html#3485" class="Datatype"
      >Term</a
      ><a name="3921"
      > 
</a
      ><a name="3923" href="Stlc.html#3907" class="Function"
      >not</a
      ><a name="3926"
      > </a
      ><a name="3927" class="Symbol"
      >=</a
      ><a name="3928"
      >  </a
      ><a name="3930" href="Stlc.html#3520" class="InductiveConstructor Operator"
      >&#955;[</a
      ><a name="3932"
      > </a
      ><a name="3933" href="Stlc.html#3877" class="Function"
      >x</a
      ><a name="3934"
      > </a
      ><a name="3935" href="Stlc.html#3520" class="InductiveConstructor Operator"
      >&#8758;</a
      ><a name="3936"
      > </a
      ><a name="3937" href="Stlc.html#2577" class="InductiveConstructor"
      >&#120121;</a
      ><a name="3938"
      > </a
      ><a name="3939" href="Stlc.html#3520" class="InductiveConstructor Operator"
      >]</a
      ><a name="3940"
      > </a
      ><a name="3941" class="Symbol"
      >(</a
      ><a name="3942" href="Stlc.html#3612" class="InductiveConstructor Operator"
      >if</a
      ><a name="3944"
      > </a
      ><a name="3945" href="Stlc.html#3504" class="InductiveConstructor"
      >`</a
      ><a name="3946"
      > </a
      ><a name="3947" href="Stlc.html#3877" class="Function"
      >x</a
      ><a name="3948"
      > </a
      ><a name="3949" href="Stlc.html#3612" class="InductiveConstructor Operator"
      >then</a
      ><a name="3953"
      > </a
      ><a name="3954" href="Stlc.html#3597" class="InductiveConstructor"
      >false</a
      ><a name="3959"
      > </a
      ><a name="3960" href="Stlc.html#3612" class="InductiveConstructor Operator"
      >else</a
      ><a name="3964"
      > </a
      ><a name="3965" href="Stlc.html#3583" class="InductiveConstructor"
      >true</a
      ><a name="3969" class="Symbol"
      >)</a
      ><a name="3970"
      >
</a
      ><a name="3971" href="Stlc.html#3911" class="Function"
      >two</a
      ><a name="3974"
      > </a
      ><a name="3975" class="Symbol"
      >=</a
      ><a name="3976"
      >  </a
      ><a name="3978" href="Stlc.html#3520" class="InductiveConstructor Operator"
      >&#955;[</a
      ><a name="3980"
      > </a
      ><a name="3981" href="Stlc.html#3875" class="Function"
      >f</a
      ><a name="3982"
      > </a
      ><a name="3983" href="Stlc.html#3520" class="InductiveConstructor Operator"
      >&#8758;</a
      ><a name="3984"
      > </a
      ><a name="3985" href="Stlc.html#2577" class="InductiveConstructor"
      >&#120121;</a
      ><a name="3986"
      > </a
      ><a name="3987" href="Stlc.html#2550" class="InductiveConstructor Operator"
      >&#8658;</a
      ><a name="3988"
      > </a
      ><a name="3989" href="Stlc.html#2577" class="InductiveConstructor"
      >&#120121;</a
      ><a name="3990"
      > </a
      ><a name="3991" href="Stlc.html#3520" class="InductiveConstructor Operator"
      >]</a
      ><a name="3992"
      > </a
      ><a name="3993" href="Stlc.html#3520" class="InductiveConstructor Operator"
      >&#955;[</a
      ><a name="3995"
      > </a
      ><a name="3996" href="Stlc.html#3877" class="Function"
      >x</a
      ><a name="3997"
      > </a
      ><a name="3998" href="Stlc.html#3520" class="InductiveConstructor Operator"
      >&#8758;</a
      ><a name="3999"
      > </a
      ><a name="4000" href="Stlc.html#2577" class="InductiveConstructor"
      >&#120121;</a
      ><a name="4001"
      > </a
      ><a name="4002" href="Stlc.html#3520" class="InductiveConstructor Operator"
      >]</a
      ><a name="4003"
      > </a
      ><a name="4004" href="Stlc.html#3504" class="InductiveConstructor"
      >`</a
      ><a name="4005"
      > </a
      ><a name="4006" href="Stlc.html#3875" class="Function"
      >f</a
      ><a name="4007"
      > </a
      ><a name="4008" href="Stlc.html#3556" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="4009"
      > </a
      ><a name="4010" class="Symbol"
      >(</a
      ><a name="4011" href="Stlc.html#3504" class="InductiveConstructor"
      >`</a
      ><a name="4012"
      > </a
      ><a name="4013" href="Stlc.html#3875" class="Function"
      >f</a
      ><a name="4014"
      > </a
      ><a name="4015" href="Stlc.html#3556" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="4016"
      > </a
      ><a name="4017" href="Stlc.html#3504" class="InductiveConstructor"
      >`</a
      ><a name="4018"
      > </a
      ><a name="4019" href="Stlc.html#3877" class="Function"
      >x</a
      ><a name="4020" class="Symbol"
      >)</a
      >

</pre>

## Values

<pre class="Agda">

<a name="4058" class="Keyword"
      >data</a
      ><a name="4062"
      > </a
      ><a name="4063" href="Stlc.html#4063" class="Datatype"
      >Value</a
      ><a name="4068"
      > </a
      ><a name="4069" class="Symbol"
      >:</a
      ><a name="4070"
      > </a
      ><a name="4071" href="Stlc.html#3485" class="Datatype"
      >Term</a
      ><a name="4075"
      > </a
      ><a name="4076" class="Symbol"
      >&#8594;</a
      ><a name="4077"
      > </a
      ><a name="4078" class="PrimitiveType"
      >Set</a
      ><a name="4081"
      > </a
      ><a name="4082" class="Keyword"
      >where</a
      ><a name="4087"
      >
  </a
      ><a name="4090" href="Stlc.html#4090" class="InductiveConstructor"
      >value-&#955;</a
      ><a name="4097"
      >     </a
      ><a name="4102" class="Symbol"
      >:</a
      ><a name="4103"
      > </a
      ><a name="4104" class="Symbol"
      >&#8704;</a
      ><a name="4105"
      > </a
      ><a name="4106" class="Symbol"
      >{</a
      ><a name="4107" href="Stlc.html#4107" class="Bound"
      >x</a
      ><a name="4108"
      > </a
      ><a name="4109" href="Stlc.html#4109" class="Bound"
      >A</a
      ><a name="4110"
      > </a
      ><a name="4111" href="Stlc.html#4111" class="Bound"
      >N</a
      ><a name="4112" class="Symbol"
      >}</a
      ><a name="4113"
      > </a
      ><a name="4114" class="Symbol"
      >&#8594;</a
      ><a name="4115"
      > </a
      ><a name="4116" href="Stlc.html#4063" class="Datatype"
      >Value</a
      ><a name="4121"
      > </a
      ><a name="4122" class="Symbol"
      >(</a
      ><a name="4123" href="Stlc.html#3520" class="InductiveConstructor Operator"
      >&#955;[</a
      ><a name="4125"
      > </a
      ><a name="4126" href="Stlc.html#4107" class="Bound"
      >x</a
      ><a name="4127"
      > </a
      ><a name="4128" href="Stlc.html#3520" class="InductiveConstructor Operator"
      >&#8758;</a
      ><a name="4129"
      > </a
      ><a name="4130" href="Stlc.html#4109" class="Bound"
      >A</a
      ><a name="4131"
      > </a
      ><a name="4132" href="Stlc.html#3520" class="InductiveConstructor Operator"
      >]</a
      ><a name="4133"
      > </a
      ><a name="4134" href="Stlc.html#4111" class="Bound"
      >N</a
      ><a name="4135" class="Symbol"
      >)</a
      ><a name="4136"
      >
  </a
      ><a name="4139" href="Stlc.html#4139" class="InductiveConstructor"
      >value-true</a
      ><a name="4149"
      >  </a
      ><a name="4151" class="Symbol"
      >:</a
      ><a name="4152"
      > </a
      ><a name="4153" href="Stlc.html#4063" class="Datatype"
      >Value</a
      ><a name="4158"
      > </a
      ><a name="4159" href="Stlc.html#3583" class="InductiveConstructor"
      >true</a
      ><a name="4163"
      >
  </a
      ><a name="4166" href="Stlc.html#4166" class="InductiveConstructor"
      >value-false</a
      ><a name="4177"
      > </a
      ><a name="4178" class="Symbol"
      >:</a
      ><a name="4179"
      > </a
      ><a name="4180" href="Stlc.html#4063" class="Datatype"
      >Value</a
      ><a name="4185"
      > </a
      ><a name="4186" href="Stlc.html#3597" class="InductiveConstructor"
      >false</a
      >

</pre>

## Substitution

<pre class="Agda">

<a name="4234" href="Stlc.html#4234" class="Function Operator"
      >_[_:=_]</a
      ><a name="4241"
      > </a
      ><a name="4242" class="Symbol"
      >:</a
      ><a name="4243"
      > </a
      ><a name="4244" href="Stlc.html#3485" class="Datatype"
      >Term</a
      ><a name="4248"
      > </a
      ><a name="4249" class="Symbol"
      >&#8594;</a
      ><a name="4250"
      > </a
      ><a name="4251" href="Maps.html#2171" class="Datatype"
      >Id</a
      ><a name="4253"
      > </a
      ><a name="4254" class="Symbol"
      >&#8594;</a
      ><a name="4255"
      > </a
      ><a name="4256" href="Stlc.html#3485" class="Datatype"
      >Term</a
      ><a name="4260"
      > </a
      ><a name="4261" class="Symbol"
      >&#8594;</a
      ><a name="4262"
      > </a
      ><a name="4263" href="Stlc.html#3485" class="Datatype"
      >Term</a
      ><a name="4267"
      >
</a
      ><a name="4268" class="Symbol"
      >(</a
      ><a name="4269" href="Stlc.html#3504" class="InductiveConstructor"
      >`</a
      ><a name="4270"
      > </a
      ><a name="4271" href="Stlc.html#4271" class="Bound"
      >x&#8242;</a
      ><a name="4273" class="Symbol"
      >)</a
      ><a name="4274"
      > </a
      ><a name="4275" href="Stlc.html#4234" class="Function Operator"
      >[</a
      ><a name="4276"
      > </a
      ><a name="4277" href="Stlc.html#4277" class="Bound"
      >x</a
      ><a name="4278"
      > </a
      ><a name="4279" href="Stlc.html#4234" class="Function Operator"
      >:=</a
      ><a name="4281"
      > </a
      ><a name="4282" href="Stlc.html#4282" class="Bound"
      >V</a
      ><a name="4283"
      > </a
      ><a name="4284" href="Stlc.html#4234" class="Function Operator"
      >]</a
      ><a name="4285"
      > </a
      ><a name="4286" class="Keyword"
      >with</a
      ><a name="4290"
      > </a
      ><a name="4291" href="Stlc.html#4277" class="Bound"
      >x</a
      ><a name="4292"
      > </a
      ><a name="4293" href="Maps.html#2509" class="Function Operator"
      >&#8799;</a
      ><a name="4294"
      > </a
      ><a name="4295" href="Stlc.html#4271" class="Bound"
      >x&#8242;</a
      ><a name="4297"
      >
</a
      ><a name="4298" class="Symbol"
      >...</a
      ><a name="4301"
      > </a
      ><a name="4302" class="Symbol"
      >|</a
      ><a name="4303"
      > </a
      ><a name="4304" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#520" class="InductiveConstructor"
      >yes</a
      ><a name="4307"
      > </a
      ><a name="4308" class="Symbol"
      >_</a
      ><a name="4309"
      > </a
      ><a name="4310" class="Symbol"
      >=</a
      ><a name="4311"
      > </a
      ><a name="4312" href="Stlc.html#4282" class="Bound"
      >V</a
      ><a name="4313"
      >
</a
      ><a name="4314" class="Symbol"
      >...</a
      ><a name="4317"
      > </a
      ><a name="4318" class="Symbol"
      >|</a
      ><a name="4319"
      > </a
      ><a name="4320" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#547" class="InductiveConstructor"
      >no</a
      ><a name="4322"
      >  </a
      ><a name="4324" class="Symbol"
      >_</a
      ><a name="4325"
      > </a
      ><a name="4326" class="Symbol"
      >=</a
      ><a name="4327"
      > </a
      ><a name="4328" href="Stlc.html#3504" class="InductiveConstructor"
      >`</a
      ><a name="4329"
      > </a
      ><a name="4330" href="Stlc.html#4271" class="Bound"
      >x&#8242;</a
      ><a name="4332"
      >
</a
      ><a name="4333" class="Symbol"
      >(</a
      ><a name="4334" href="Stlc.html#3520" class="InductiveConstructor Operator"
      >&#955;[</a
      ><a name="4336"
      > </a
      ><a name="4337" href="Stlc.html#4337" class="Bound"
      >x&#8242;</a
      ><a name="4339"
      > </a
      ><a name="4340" href="Stlc.html#3520" class="InductiveConstructor Operator"
      >&#8758;</a
      ><a name="4341"
      > </a
      ><a name="4342" href="Stlc.html#4342" class="Bound"
      >A&#8242;</a
      ><a name="4344"
      > </a
      ><a name="4345" href="Stlc.html#3520" class="InductiveConstructor Operator"
      >]</a
      ><a name="4346"
      > </a
      ><a name="4347" href="Stlc.html#4347" class="Bound"
      >N&#8242;</a
      ><a name="4349" class="Symbol"
      >)</a
      ><a name="4350"
      > </a
      ><a name="4351" href="Stlc.html#4234" class="Function Operator"
      >[</a
      ><a name="4352"
      > </a
      ><a name="4353" href="Stlc.html#4353" class="Bound"
      >x</a
      ><a name="4354"
      > </a
      ><a name="4355" href="Stlc.html#4234" class="Function Operator"
      >:=</a
      ><a name="4357"
      > </a
      ><a name="4358" href="Stlc.html#4358" class="Bound"
      >V</a
      ><a name="4359"
      > </a
      ><a name="4360" href="Stlc.html#4234" class="Function Operator"
      >]</a
      ><a name="4361"
      > </a
      ><a name="4362" class="Keyword"
      >with</a
      ><a name="4366"
      > </a
      ><a name="4367" href="Stlc.html#4353" class="Bound"
      >x</a
      ><a name="4368"
      > </a
      ><a name="4369" href="Maps.html#2509" class="Function Operator"
      >&#8799;</a
      ><a name="4370"
      > </a
      ><a name="4371" href="Stlc.html#4337" class="Bound"
      >x&#8242;</a
      ><a name="4373"
      >
</a
      ><a name="4374" class="Symbol"
      >...</a
      ><a name="4377"
      > </a
      ><a name="4378" class="Symbol"
      >|</a
      ><a name="4379"
      > </a
      ><a name="4380" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#520" class="InductiveConstructor"
      >yes</a
      ><a name="4383"
      > </a
      ><a name="4384" class="Symbol"
      >_</a
      ><a name="4385"
      > </a
      ><a name="4386" class="Symbol"
      >=</a
      ><a name="4387"
      > </a
      ><a name="4388" href="Stlc.html#3520" class="InductiveConstructor Operator"
      >&#955;[</a
      ><a name="4390"
      > </a
      ><a name="4391" href="Stlc.html#4337" class="Bound"
      >x&#8242;</a
      ><a name="4393"
      > </a
      ><a name="4394" href="Stlc.html#3520" class="InductiveConstructor Operator"
      >&#8758;</a
      ><a name="4395"
      > </a
      ><a name="4396" href="Stlc.html#4342" class="Bound"
      >A&#8242;</a
      ><a name="4398"
      > </a
      ><a name="4399" href="Stlc.html#3520" class="InductiveConstructor Operator"
      >]</a
      ><a name="4400"
      > </a
      ><a name="4401" href="Stlc.html#4347" class="Bound"
      >N&#8242;</a
      ><a name="4403"
      >
</a
      ><a name="4404" class="Symbol"
      >...</a
      ><a name="4407"
      > </a
      ><a name="4408" class="Symbol"
      >|</a
      ><a name="4409"
      > </a
      ><a name="4410" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#547" class="InductiveConstructor"
      >no</a
      ><a name="4412"
      >  </a
      ><a name="4414" class="Symbol"
      >_</a
      ><a name="4415"
      > </a
      ><a name="4416" class="Symbol"
      >=</a
      ><a name="4417"
      > </a
      ><a name="4418" href="Stlc.html#3520" class="InductiveConstructor Operator"
      >&#955;[</a
      ><a name="4420"
      > </a
      ><a name="4421" href="Stlc.html#4337" class="Bound"
      >x&#8242;</a
      ><a name="4423"
      > </a
      ><a name="4424" href="Stlc.html#3520" class="InductiveConstructor Operator"
      >&#8758;</a
      ><a name="4425"
      > </a
      ><a name="4426" href="Stlc.html#4342" class="Bound"
      >A&#8242;</a
      ><a name="4428"
      > </a
      ><a name="4429" href="Stlc.html#3520" class="InductiveConstructor Operator"
      >]</a
      ><a name="4430"
      > </a
      ><a name="4431" class="Symbol"
      >(</a
      ><a name="4432" href="Stlc.html#4347" class="Bound"
      >N&#8242;</a
      ><a name="4434"
      > </a
      ><a name="4435" href="Stlc.html#4234" class="Function Operator"
      >[</a
      ><a name="4436"
      > </a
      ><a name="4437" href="Stlc.html#4353" class="Bound"
      >x</a
      ><a name="4438"
      > </a
      ><a name="4439" href="Stlc.html#4234" class="Function Operator"
      >:=</a
      ><a name="4441"
      > </a
      ><a name="4442" href="Stlc.html#4358" class="Bound"
      >V</a
      ><a name="4443"
      > </a
      ><a name="4444" href="Stlc.html#4234" class="Function Operator"
      >]</a
      ><a name="4445" class="Symbol"
      >)</a
      ><a name="4446"
      >
</a
      ><a name="4447" class="Symbol"
      >(</a
      ><a name="4448" href="Stlc.html#4448" class="Bound"
      >L&#8242;</a
      ><a name="4450"
      > </a
      ><a name="4451" href="Stlc.html#3556" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="4452"
      > </a
      ><a name="4453" href="Stlc.html#4453" class="Bound"
      >M&#8242;</a
      ><a name="4455" class="Symbol"
      >)</a
      ><a name="4456"
      > </a
      ><a name="4457" href="Stlc.html#4234" class="Function Operator"
      >[</a
      ><a name="4458"
      > </a
      ><a name="4459" href="Stlc.html#4459" class="Bound"
      >x</a
      ><a name="4460"
      > </a
      ><a name="4461" href="Stlc.html#4234" class="Function Operator"
      >:=</a
      ><a name="4463"
      > </a
      ><a name="4464" href="Stlc.html#4464" class="Bound"
      >V</a
      ><a name="4465"
      > </a
      ><a name="4466" href="Stlc.html#4234" class="Function Operator"
      >]</a
      ><a name="4467"
      > </a
      ><a name="4468" class="Symbol"
      >=</a
      ><a name="4469"
      >  </a
      ><a name="4471" class="Symbol"
      >(</a
      ><a name="4472" href="Stlc.html#4448" class="Bound"
      >L&#8242;</a
      ><a name="4474"
      > </a
      ><a name="4475" href="Stlc.html#4234" class="Function Operator"
      >[</a
      ><a name="4476"
      > </a
      ><a name="4477" href="Stlc.html#4459" class="Bound"
      >x</a
      ><a name="4478"
      > </a
      ><a name="4479" href="Stlc.html#4234" class="Function Operator"
      >:=</a
      ><a name="4481"
      > </a
      ><a name="4482" href="Stlc.html#4464" class="Bound"
      >V</a
      ><a name="4483"
      > </a
      ><a name="4484" href="Stlc.html#4234" class="Function Operator"
      >]</a
      ><a name="4485" class="Symbol"
      >)</a
      ><a name="4486"
      > </a
      ><a name="4487" href="Stlc.html#3556" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="4488"
      > </a
      ><a name="4489" class="Symbol"
      >(</a
      ><a name="4490" href="Stlc.html#4453" class="Bound"
      >M&#8242;</a
      ><a name="4492"
      > </a
      ><a name="4493" href="Stlc.html#4234" class="Function Operator"
      >[</a
      ><a name="4494"
      > </a
      ><a name="4495" href="Stlc.html#4459" class="Bound"
      >x</a
      ><a name="4496"
      > </a
      ><a name="4497" href="Stlc.html#4234" class="Function Operator"
      >:=</a
      ><a name="4499"
      > </a
      ><a name="4500" href="Stlc.html#4464" class="Bound"
      >V</a
      ><a name="4501"
      > </a
      ><a name="4502" href="Stlc.html#4234" class="Function Operator"
      >]</a
      ><a name="4503" class="Symbol"
      >)</a
      ><a name="4504"
      >
</a
      ><a name="4505" class="Symbol"
      >(</a
      ><a name="4506" href="Stlc.html#3583" class="InductiveConstructor"
      >true</a
      ><a name="4510" class="Symbol"
      >)</a
      ><a name="4511"
      > </a
      ><a name="4512" href="Stlc.html#4234" class="Function Operator"
      >[</a
      ><a name="4513"
      > </a
      ><a name="4514" href="Stlc.html#4514" class="Bound"
      >x</a
      ><a name="4515"
      > </a
      ><a name="4516" href="Stlc.html#4234" class="Function Operator"
      >:=</a
      ><a name="4518"
      > </a
      ><a name="4519" href="Stlc.html#4519" class="Bound"
      >V</a
      ><a name="4520"
      > </a
      ><a name="4521" href="Stlc.html#4234" class="Function Operator"
      >]</a
      ><a name="4522"
      > </a
      ><a name="4523" class="Symbol"
      >=</a
      ><a name="4524"
      > </a
      ><a name="4525" href="Stlc.html#3583" class="InductiveConstructor"
      >true</a
      ><a name="4529"
      >
</a
      ><a name="4530" class="Symbol"
      >(</a
      ><a name="4531" href="Stlc.html#3597" class="InductiveConstructor"
      >false</a
      ><a name="4536" class="Symbol"
      >)</a
      ><a name="4537"
      > </a
      ><a name="4538" href="Stlc.html#4234" class="Function Operator"
      >[</a
      ><a name="4539"
      > </a
      ><a name="4540" href="Stlc.html#4540" class="Bound"
      >x</a
      ><a name="4541"
      > </a
      ><a name="4542" href="Stlc.html#4234" class="Function Operator"
      >:=</a
      ><a name="4544"
      > </a
      ><a name="4545" href="Stlc.html#4545" class="Bound"
      >V</a
      ><a name="4546"
      > </a
      ><a name="4547" href="Stlc.html#4234" class="Function Operator"
      >]</a
      ><a name="4548"
      > </a
      ><a name="4549" class="Symbol"
      >=</a
      ><a name="4550"
      > </a
      ><a name="4551" href="Stlc.html#3597" class="InductiveConstructor"
      >false</a
      ><a name="4556"
      >
</a
      ><a name="4557" class="Symbol"
      >(</a
      ><a name="4558" href="Stlc.html#3612" class="InductiveConstructor Operator"
      >if</a
      ><a name="4560"
      > </a
      ><a name="4561" href="Stlc.html#4561" class="Bound"
      >L&#8242;</a
      ><a name="4563"
      > </a
      ><a name="4564" href="Stlc.html#3612" class="InductiveConstructor Operator"
      >then</a
      ><a name="4568"
      > </a
      ><a name="4569" href="Stlc.html#4569" class="Bound"
      >M&#8242;</a
      ><a name="4571"
      > </a
      ><a name="4572" href="Stlc.html#3612" class="InductiveConstructor Operator"
      >else</a
      ><a name="4576"
      > </a
      ><a name="4577" href="Stlc.html#4577" class="Bound"
      >N&#8242;</a
      ><a name="4579" class="Symbol"
      >)</a
      ><a name="4580"
      > </a
      ><a name="4581" href="Stlc.html#4234" class="Function Operator"
      >[</a
      ><a name="4582"
      > </a
      ><a name="4583" href="Stlc.html#4583" class="Bound"
      >x</a
      ><a name="4584"
      > </a
      ><a name="4585" href="Stlc.html#4234" class="Function Operator"
      >:=</a
      ><a name="4587"
      > </a
      ><a name="4588" href="Stlc.html#4588" class="Bound"
      >V</a
      ><a name="4589"
      > </a
      ><a name="4590" href="Stlc.html#4234" class="Function Operator"
      >]</a
      ><a name="4591"
      > </a
      ><a name="4592" class="Symbol"
      >=</a
      ><a name="4593"
      > </a
      ><a name="4594" href="Stlc.html#3612" class="InductiveConstructor Operator"
      >if</a
      ><a name="4596"
      > </a
      ><a name="4597" class="Symbol"
      >(</a
      ><a name="4598" href="Stlc.html#4561" class="Bound"
      >L&#8242;</a
      ><a name="4600"
      > </a
      ><a name="4601" href="Stlc.html#4234" class="Function Operator"
      >[</a
      ><a name="4602"
      > </a
      ><a name="4603" href="Stlc.html#4583" class="Bound"
      >x</a
      ><a name="4604"
      > </a
      ><a name="4605" href="Stlc.html#4234" class="Function Operator"
      >:=</a
      ><a name="4607"
      > </a
      ><a name="4608" href="Stlc.html#4588" class="Bound"
      >V</a
      ><a name="4609"
      > </a
      ><a name="4610" href="Stlc.html#4234" class="Function Operator"
      >]</a
      ><a name="4611" class="Symbol"
      >)</a
      ><a name="4612"
      > </a
      ><a name="4613" href="Stlc.html#3612" class="InductiveConstructor Operator"
      >then</a
      ><a name="4617"
      > </a
      ><a name="4618" class="Symbol"
      >(</a
      ><a name="4619" href="Stlc.html#4569" class="Bound"
      >M&#8242;</a
      ><a name="4621"
      > </a
      ><a name="4622" href="Stlc.html#4234" class="Function Operator"
      >[</a
      ><a name="4623"
      > </a
      ><a name="4624" href="Stlc.html#4583" class="Bound"
      >x</a
      ><a name="4625"
      > </a
      ><a name="4626" href="Stlc.html#4234" class="Function Operator"
      >:=</a
      ><a name="4628"
      > </a
      ><a name="4629" href="Stlc.html#4588" class="Bound"
      >V</a
      ><a name="4630"
      > </a
      ><a name="4631" href="Stlc.html#4234" class="Function Operator"
      >]</a
      ><a name="4632" class="Symbol"
      >)</a
      ><a name="4633"
      > </a
      ><a name="4634" href="Stlc.html#3612" class="InductiveConstructor Operator"
      >else</a
      ><a name="4638"
      > </a
      ><a name="4639" class="Symbol"
      >(</a
      ><a name="4640" href="Stlc.html#4577" class="Bound"
      >N&#8242;</a
      ><a name="4642"
      > </a
      ><a name="4643" href="Stlc.html#4234" class="Function Operator"
      >[</a
      ><a name="4644"
      > </a
      ><a name="4645" href="Stlc.html#4583" class="Bound"
      >x</a
      ><a name="4646"
      > </a
      ><a name="4647" href="Stlc.html#4234" class="Function Operator"
      >:=</a
      ><a name="4649"
      > </a
      ><a name="4650" href="Stlc.html#4588" class="Bound"
      >V</a
      ><a name="4651"
      > </a
      ><a name="4652" href="Stlc.html#4234" class="Function Operator"
      >]</a
      ><a name="4653" class="Symbol"
      >)</a
      >

</pre>

## Reduction rules

<pre class="Agda">

<a name="4700" class="Keyword"
      >infix</a
      ><a name="4705"
      > </a
      ><a name="4706" class="Number"
      >10</a
      ><a name="4708"
      > </a
      ><a name="4709" href="Stlc.html#4720" class="Datatype Operator"
      >_&#10233;_</a
      ><a name="4712"
      > 

</a
      ><a name="4715" class="Keyword"
      >data</a
      ><a name="4719"
      > </a
      ><a name="4720" href="Stlc.html#4720" class="Datatype Operator"
      >_&#10233;_</a
      ><a name="4723"
      > </a
      ><a name="4724" class="Symbol"
      >:</a
      ><a name="4725"
      > </a
      ><a name="4726" href="Stlc.html#3485" class="Datatype"
      >Term</a
      ><a name="4730"
      > </a
      ><a name="4731" class="Symbol"
      >&#8594;</a
      ><a name="4732"
      > </a
      ><a name="4733" href="Stlc.html#3485" class="Datatype"
      >Term</a
      ><a name="4737"
      > </a
      ><a name="4738" class="Symbol"
      >&#8594;</a
      ><a name="4739"
      > </a
      ><a name="4740" class="PrimitiveType"
      >Set</a
      ><a name="4743"
      > </a
      ><a name="4744" class="Keyword"
      >where</a
      ><a name="4749"
      >
  </a
      ><a name="4752" href="Stlc.html#4752" class="InductiveConstructor"
      >&#946;&#955;&#183;</a
      ><a name="4755"
      > </a
      ><a name="4756" class="Symbol"
      >:</a
      ><a name="4757"
      > </a
      ><a name="4758" class="Symbol"
      >&#8704;</a
      ><a name="4759"
      > </a
      ><a name="4760" class="Symbol"
      >{</a
      ><a name="4761" href="Stlc.html#4761" class="Bound"
      >x</a
      ><a name="4762"
      > </a
      ><a name="4763" href="Stlc.html#4763" class="Bound"
      >A</a
      ><a name="4764"
      > </a
      ><a name="4765" href="Stlc.html#4765" class="Bound"
      >N</a
      ><a name="4766"
      > </a
      ><a name="4767" href="Stlc.html#4767" class="Bound"
      >V</a
      ><a name="4768" class="Symbol"
      >}</a
      ><a name="4769"
      > </a
      ><a name="4770" class="Symbol"
      >&#8594;</a
      ><a name="4771"
      > </a
      ><a name="4772" href="Stlc.html#4063" class="Datatype"
      >Value</a
      ><a name="4777"
      > </a
      ><a name="4778" href="Stlc.html#4767" class="Bound"
      >V</a
      ><a name="4779"
      > </a
      ><a name="4780" class="Symbol"
      >&#8594;</a
      ><a name="4781"
      >
    </a
      ><a name="4786" class="Symbol"
      >(</a
      ><a name="4787" href="Stlc.html#3520" class="InductiveConstructor Operator"
      >&#955;[</a
      ><a name="4789"
      > </a
      ><a name="4790" href="Stlc.html#4761" class="Bound"
      >x</a
      ><a name="4791"
      > </a
      ><a name="4792" href="Stlc.html#3520" class="InductiveConstructor Operator"
      >&#8758;</a
      ><a name="4793"
      > </a
      ><a name="4794" href="Stlc.html#4763" class="Bound"
      >A</a
      ><a name="4795"
      > </a
      ><a name="4796" href="Stlc.html#3520" class="InductiveConstructor Operator"
      >]</a
      ><a name="4797"
      > </a
      ><a name="4798" href="Stlc.html#4765" class="Bound"
      >N</a
      ><a name="4799" class="Symbol"
      >)</a
      ><a name="4800"
      > </a
      ><a name="4801" href="Stlc.html#3556" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="4802"
      > </a
      ><a name="4803" href="Stlc.html#4767" class="Bound"
      >V</a
      ><a name="4804"
      > </a
      ><a name="4805" href="Stlc.html#4720" class="Datatype Operator"
      >&#10233;</a
      ><a name="4806"
      > </a
      ><a name="4807" href="Stlc.html#4765" class="Bound"
      >N</a
      ><a name="4808"
      > </a
      ><a name="4809" href="Stlc.html#4234" class="Function Operator"
      >[</a
      ><a name="4810"
      > </a
      ><a name="4811" href="Stlc.html#4761" class="Bound"
      >x</a
      ><a name="4812"
      > </a
      ><a name="4813" href="Stlc.html#4234" class="Function Operator"
      >:=</a
      ><a name="4815"
      > </a
      ><a name="4816" href="Stlc.html#4767" class="Bound"
      >V</a
      ><a name="4817"
      > </a
      ><a name="4818" href="Stlc.html#4234" class="Function Operator"
      >]</a
      ><a name="4819"
      >
  </a
      ><a name="4822" href="Stlc.html#4822" class="InductiveConstructor"
      >&#958;&#183;&#8321;</a
      ><a name="4825"
      > </a
      ><a name="4826" class="Symbol"
      >:</a
      ><a name="4827"
      > </a
      ><a name="4828" class="Symbol"
      >&#8704;</a
      ><a name="4829"
      > </a
      ><a name="4830" class="Symbol"
      >{</a
      ><a name="4831" href="Stlc.html#4831" class="Bound"
      >L</a
      ><a name="4832"
      > </a
      ><a name="4833" href="Stlc.html#4833" class="Bound"
      >L&#8242;</a
      ><a name="4835"
      > </a
      ><a name="4836" href="Stlc.html#4836" class="Bound"
      >M</a
      ><a name="4837" class="Symbol"
      >}</a
      ><a name="4838"
      > </a
      ><a name="4839" class="Symbol"
      >&#8594;</a
      ><a name="4840"
      >
    </a
      ><a name="4845" href="Stlc.html#4831" class="Bound"
      >L</a
      ><a name="4846"
      > </a
      ><a name="4847" href="Stlc.html#4720" class="Datatype Operator"
      >&#10233;</a
      ><a name="4848"
      > </a
      ><a name="4849" href="Stlc.html#4833" class="Bound"
      >L&#8242;</a
      ><a name="4851"
      > </a
      ><a name="4852" class="Symbol"
      >&#8594;</a
      ><a name="4853"
      >
    </a
      ><a name="4858" href="Stlc.html#4831" class="Bound"
      >L</a
      ><a name="4859"
      > </a
      ><a name="4860" href="Stlc.html#3556" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="4861"
      > </a
      ><a name="4862" href="Stlc.html#4836" class="Bound"
      >M</a
      ><a name="4863"
      > </a
      ><a name="4864" href="Stlc.html#4720" class="Datatype Operator"
      >&#10233;</a
      ><a name="4865"
      > </a
      ><a name="4866" href="Stlc.html#4833" class="Bound"
      >L&#8242;</a
      ><a name="4868"
      > </a
      ><a name="4869" href="Stlc.html#3556" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="4870"
      > </a
      ><a name="4871" href="Stlc.html#4836" class="Bound"
      >M</a
      ><a name="4872"
      >
  </a
      ><a name="4875" href="Stlc.html#4875" class="InductiveConstructor"
      >&#958;&#183;&#8322;</a
      ><a name="4878"
      > </a
      ><a name="4879" class="Symbol"
      >:</a
      ><a name="4880"
      > </a
      ><a name="4881" class="Symbol"
      >&#8704;</a
      ><a name="4882"
      > </a
      ><a name="4883" class="Symbol"
      >{</a
      ><a name="4884" href="Stlc.html#4884" class="Bound"
      >V</a
      ><a name="4885"
      > </a
      ><a name="4886" href="Stlc.html#4886" class="Bound"
      >M</a
      ><a name="4887"
      > </a
      ><a name="4888" href="Stlc.html#4888" class="Bound"
      >M&#8242;</a
      ><a name="4890" class="Symbol"
      >}</a
      ><a name="4891"
      > </a
      ><a name="4892" class="Symbol"
      >&#8594;</a
      ><a name="4893"
      >
    </a
      ><a name="4898" href="Stlc.html#4063" class="Datatype"
      >Value</a
      ><a name="4903"
      > </a
      ><a name="4904" href="Stlc.html#4884" class="Bound"
      >V</a
      ><a name="4905"
      > </a
      ><a name="4906" class="Symbol"
      >&#8594;</a
      ><a name="4907"
      >
    </a
      ><a name="4912" href="Stlc.html#4886" class="Bound"
      >M</a
      ><a name="4913"
      > </a
      ><a name="4914" href="Stlc.html#4720" class="Datatype Operator"
      >&#10233;</a
      ><a name="4915"
      > </a
      ><a name="4916" href="Stlc.html#4888" class="Bound"
      >M&#8242;</a
      ><a name="4918"
      > </a
      ><a name="4919" class="Symbol"
      >&#8594;</a
      ><a name="4920"
      >
    </a
      ><a name="4925" href="Stlc.html#4884" class="Bound"
      >V</a
      ><a name="4926"
      > </a
      ><a name="4927" href="Stlc.html#3556" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="4928"
      > </a
      ><a name="4929" href="Stlc.html#4886" class="Bound"
      >M</a
      ><a name="4930"
      > </a
      ><a name="4931" href="Stlc.html#4720" class="Datatype Operator"
      >&#10233;</a
      ><a name="4932"
      > </a
      ><a name="4933" href="Stlc.html#4884" class="Bound"
      >V</a
      ><a name="4934"
      > </a
      ><a name="4935" href="Stlc.html#3556" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="4936"
      > </a
      ><a name="4937" href="Stlc.html#4888" class="Bound"
      >M&#8242;</a
      ><a name="4939"
      >
  </a
      ><a name="4942" href="Stlc.html#4942" class="InductiveConstructor"
      >&#946;if-true</a
      ><a name="4950"
      > </a
      ><a name="4951" class="Symbol"
      >:</a
      ><a name="4952"
      > </a
      ><a name="4953" class="Symbol"
      >&#8704;</a
      ><a name="4954"
      > </a
      ><a name="4955" class="Symbol"
      >{</a
      ><a name="4956" href="Stlc.html#4956" class="Bound"
      >M</a
      ><a name="4957"
      > </a
      ><a name="4958" href="Stlc.html#4958" class="Bound"
      >N</a
      ><a name="4959" class="Symbol"
      >}</a
      ><a name="4960"
      > </a
      ><a name="4961" class="Symbol"
      >&#8594;</a
      ><a name="4962"
      >
    </a
      ><a name="4967" href="Stlc.html#3612" class="InductiveConstructor Operator"
      >if</a
      ><a name="4969"
      > </a
      ><a name="4970" href="Stlc.html#3583" class="InductiveConstructor"
      >true</a
      ><a name="4974"
      > </a
      ><a name="4975" href="Stlc.html#3612" class="InductiveConstructor Operator"
      >then</a
      ><a name="4979"
      > </a
      ><a name="4980" href="Stlc.html#4956" class="Bound"
      >M</a
      ><a name="4981"
      > </a
      ><a name="4982" href="Stlc.html#3612" class="InductiveConstructor Operator"
      >else</a
      ><a name="4986"
      > </a
      ><a name="4987" href="Stlc.html#4958" class="Bound"
      >N</a
      ><a name="4988"
      > </a
      ><a name="4989" href="Stlc.html#4720" class="Datatype Operator"
      >&#10233;</a
      ><a name="4990"
      > </a
      ><a name="4991" href="Stlc.html#4956" class="Bound"
      >M</a
      ><a name="4992"
      >
  </a
      ><a name="4995" href="Stlc.html#4995" class="InductiveConstructor"
      >&#946;if-false</a
      ><a name="5004"
      > </a
      ><a name="5005" class="Symbol"
      >:</a
      ><a name="5006"
      > </a
      ><a name="5007" class="Symbol"
      >&#8704;</a
      ><a name="5008"
      > </a
      ><a name="5009" class="Symbol"
      >{</a
      ><a name="5010" href="Stlc.html#5010" class="Bound"
      >M</a
      ><a name="5011"
      > </a
      ><a name="5012" href="Stlc.html#5012" class="Bound"
      >N</a
      ><a name="5013" class="Symbol"
      >}</a
      ><a name="5014"
      > </a
      ><a name="5015" class="Symbol"
      >&#8594;</a
      ><a name="5016"
      >
    </a
      ><a name="5021" href="Stlc.html#3612" class="InductiveConstructor Operator"
      >if</a
      ><a name="5023"
      > </a
      ><a name="5024" href="Stlc.html#3597" class="InductiveConstructor"
      >false</a
      ><a name="5029"
      > </a
      ><a name="5030" href="Stlc.html#3612" class="InductiveConstructor Operator"
      >then</a
      ><a name="5034"
      > </a
      ><a name="5035" href="Stlc.html#5010" class="Bound"
      >M</a
      ><a name="5036"
      > </a
      ><a name="5037" href="Stlc.html#3612" class="InductiveConstructor Operator"
      >else</a
      ><a name="5041"
      > </a
      ><a name="5042" href="Stlc.html#5012" class="Bound"
      >N</a
      ><a name="5043"
      > </a
      ><a name="5044" href="Stlc.html#4720" class="Datatype Operator"
      >&#10233;</a
      ><a name="5045"
      > </a
      ><a name="5046" href="Stlc.html#5012" class="Bound"
      >N</a
      ><a name="5047"
      >
  </a
      ><a name="5050" href="Stlc.html#5050" class="InductiveConstructor"
      >&#958;if</a
      ><a name="5053"
      > </a
      ><a name="5054" class="Symbol"
      >:</a
      ><a name="5055"
      > </a
      ><a name="5056" class="Symbol"
      >&#8704;</a
      ><a name="5057"
      > </a
      ><a name="5058" class="Symbol"
      >{</a
      ><a name="5059" href="Stlc.html#5059" class="Bound"
      >L</a
      ><a name="5060"
      > </a
      ><a name="5061" href="Stlc.html#5061" class="Bound"
      >L&#8242;</a
      ><a name="5063"
      > </a
      ><a name="5064" href="Stlc.html#5064" class="Bound"
      >M</a
      ><a name="5065"
      > </a
      ><a name="5066" href="Stlc.html#5066" class="Bound"
      >N</a
      ><a name="5067" class="Symbol"
      >}</a
      ><a name="5068"
      > </a
      ><a name="5069" class="Symbol"
      >&#8594;</a
      ><a name="5070"
      >
    </a
      ><a name="5075" href="Stlc.html#5059" class="Bound"
      >L</a
      ><a name="5076"
      > </a
      ><a name="5077" href="Stlc.html#4720" class="Datatype Operator"
      >&#10233;</a
      ><a name="5078"
      > </a
      ><a name="5079" href="Stlc.html#5061" class="Bound"
      >L&#8242;</a
      ><a name="5081"
      > </a
      ><a name="5082" class="Symbol"
      >&#8594;</a
      ><a name="5083"
      >    
    </a
      ><a name="5092" href="Stlc.html#3612" class="InductiveConstructor Operator"
      >if</a
      ><a name="5094"
      > </a
      ><a name="5095" href="Stlc.html#5059" class="Bound"
      >L</a
      ><a name="5096"
      > </a
      ><a name="5097" href="Stlc.html#3612" class="InductiveConstructor Operator"
      >then</a
      ><a name="5101"
      > </a
      ><a name="5102" href="Stlc.html#5064" class="Bound"
      >M</a
      ><a name="5103"
      > </a
      ><a name="5104" href="Stlc.html#3612" class="InductiveConstructor Operator"
      >else</a
      ><a name="5108"
      > </a
      ><a name="5109" href="Stlc.html#5066" class="Bound"
      >N</a
      ><a name="5110"
      > </a
      ><a name="5111" href="Stlc.html#4720" class="Datatype Operator"
      >&#10233;</a
      ><a name="5112"
      > </a
      ><a name="5113" href="Stlc.html#3612" class="InductiveConstructor Operator"
      >if</a
      ><a name="5115"
      > </a
      ><a name="5116" href="Stlc.html#5061" class="Bound"
      >L&#8242;</a
      ><a name="5118"
      > </a
      ><a name="5119" href="Stlc.html#3612" class="InductiveConstructor Operator"
      >then</a
      ><a name="5123"
      > </a
      ><a name="5124" href="Stlc.html#5064" class="Bound"
      >M</a
      ><a name="5125"
      > </a
      ><a name="5126" href="Stlc.html#3612" class="InductiveConstructor Operator"
      >else</a
      ><a name="5130"
      > </a
      ><a name="5131" href="Stlc.html#5066" class="Bound"
      >N</a
      >

</pre>

## Reflexive and transitive closure


<pre class="Agda">

<a name="5196" class="Keyword"
      >infix</a
      ><a name="5201"
      > </a
      ><a name="5202" class="Number"
      >10</a
      ><a name="5204"
      > </a
      ><a name="5205" href="Stlc.html#5245" class="Datatype Operator"
      >_&#10233;*_</a
      ><a name="5209"
      > 
</a
      ><a name="5211" class="Keyword"
      >infixr</a
      ><a name="5217"
      > </a
      ><a name="5218" class="Number"
      >2</a
      ><a name="5219"
      > </a
      ><a name="5220" href="Stlc.html#5298" class="InductiveConstructor Operator"
      >_&#10233;&#10216;_&#10217;_</a
      ><a name="5226"
      >
</a
      ><a name="5227" class="Keyword"
      >infix</a
      ><a name="5232"
      >  </a
      ><a name="5234" class="Number"
      >3</a
      ><a name="5235"
      > </a
      ><a name="5236" href="Stlc.html#5278" class="InductiveConstructor Operator"
      >_&#8718;</a
      ><a name="5238"
      >

</a
      ><a name="5240" class="Keyword"
      >data</a
      ><a name="5244"
      > </a
      ><a name="5245" href="Stlc.html#5245" class="Datatype Operator"
      >_&#10233;*_</a
      ><a name="5249"
      > </a
      ><a name="5250" class="Symbol"
      >:</a
      ><a name="5251"
      > </a
      ><a name="5252" href="Stlc.html#3485" class="Datatype"
      >Term</a
      ><a name="5256"
      > </a
      ><a name="5257" class="Symbol"
      >&#8594;</a
      ><a name="5258"
      > </a
      ><a name="5259" href="Stlc.html#3485" class="Datatype"
      >Term</a
      ><a name="5263"
      > </a
      ><a name="5264" class="Symbol"
      >&#8594;</a
      ><a name="5265"
      > </a
      ><a name="5266" class="PrimitiveType"
      >Set</a
      ><a name="5269"
      > </a
      ><a name="5270" class="Keyword"
      >where</a
      ><a name="5275"
      >
  </a
      ><a name="5278" href="Stlc.html#5278" class="InductiveConstructor Operator"
      >_&#8718;</a
      ><a name="5280"
      > </a
      ><a name="5281" class="Symbol"
      >:</a
      ><a name="5282"
      > </a
      ><a name="5283" class="Symbol"
      >&#8704;</a
      ><a name="5284"
      > </a
      ><a name="5285" href="Stlc.html#5285" class="Bound"
      >M</a
      ><a name="5286"
      > </a
      ><a name="5287" class="Symbol"
      >&#8594;</a
      ><a name="5288"
      > </a
      ><a name="5289" href="Stlc.html#5285" class="Bound"
      >M</a
      ><a name="5290"
      > </a
      ><a name="5291" href="Stlc.html#5245" class="Datatype Operator"
      >&#10233;*</a
      ><a name="5293"
      > </a
      ><a name="5294" href="Stlc.html#5285" class="Bound"
      >M</a
      ><a name="5295"
      >
  </a
      ><a name="5298" href="Stlc.html#5298" class="InductiveConstructor Operator"
      >_&#10233;&#10216;_&#10217;_</a
      ><a name="5304"
      > </a
      ><a name="5305" class="Symbol"
      >:</a
      ><a name="5306"
      > </a
      ><a name="5307" class="Symbol"
      >&#8704;</a
      ><a name="5308"
      > </a
      ><a name="5309" href="Stlc.html#5309" class="Bound"
      >L</a
      ><a name="5310"
      > </a
      ><a name="5311" class="Symbol"
      >{</a
      ><a name="5312" href="Stlc.html#5312" class="Bound"
      >M</a
      ><a name="5313"
      > </a
      ><a name="5314" href="Stlc.html#5314" class="Bound"
      >N</a
      ><a name="5315" class="Symbol"
      >}</a
      ><a name="5316"
      > </a
      ><a name="5317" class="Symbol"
      >&#8594;</a
      ><a name="5318"
      > </a
      ><a name="5319" href="Stlc.html#5309" class="Bound"
      >L</a
      ><a name="5320"
      > </a
      ><a name="5321" href="Stlc.html#4720" class="Datatype Operator"
      >&#10233;</a
      ><a name="5322"
      > </a
      ><a name="5323" href="Stlc.html#5312" class="Bound"
      >M</a
      ><a name="5324"
      > </a
      ><a name="5325" class="Symbol"
      >&#8594;</a
      ><a name="5326"
      > </a
      ><a name="5327" href="Stlc.html#5312" class="Bound"
      >M</a
      ><a name="5328"
      > </a
      ><a name="5329" href="Stlc.html#5245" class="Datatype Operator"
      >&#10233;*</a
      ><a name="5331"
      > </a
      ><a name="5332" href="Stlc.html#5314" class="Bound"
      >N</a
      ><a name="5333"
      > </a
      ><a name="5334" class="Symbol"
      >&#8594;</a
      ><a name="5335"
      > </a
      ><a name="5336" href="Stlc.html#5309" class="Bound"
      >L</a
      ><a name="5337"
      > </a
      ><a name="5338" href="Stlc.html#5245" class="Datatype Operator"
      >&#10233;*</a
      ><a name="5340"
      > </a
      ><a name="5341" href="Stlc.html#5314" class="Bound"
      >N</a
      ><a name="5342"
      >  

</a
      ><a name="5346" href="Stlc.html#5346" class="Function"
      >reduction&#8321;</a
      ><a name="5356"
      > </a
      ><a name="5357" class="Symbol"
      >:</a
      ><a name="5358"
      > </a
      ><a name="5359" href="Stlc.html#3907" class="Function"
      >not</a
      ><a name="5362"
      > </a
      ><a name="5363" href="Stlc.html#3556" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="5364"
      > </a
      ><a name="5365" href="Stlc.html#3583" class="InductiveConstructor"
      >true</a
      ><a name="5369"
      > </a
      ><a name="5370" href="Stlc.html#5245" class="Datatype Operator"
      >&#10233;*</a
      ><a name="5372"
      > </a
      ><a name="5373" href="Stlc.html#3597" class="InductiveConstructor"
      >false</a
      ><a name="5378"
      >
</a
      ><a name="5379" href="Stlc.html#5346" class="Function"
      >reduction&#8321;</a
      ><a name="5389"
      > </a
      ><a name="5390" class="Symbol"
      >=</a
      ><a name="5391"
      >
    </a
      ><a name="5396" href="Stlc.html#3907" class="Function"
      >not</a
      ><a name="5399"
      > </a
      ><a name="5400" href="Stlc.html#3556" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="5401"
      > </a
      ><a name="5402" href="Stlc.html#3583" class="InductiveConstructor"
      >true</a
      ><a name="5406"
      >
  </a
      ><a name="5409" href="Stlc.html#5298" class="InductiveConstructor Operator"
      >&#10233;&#10216;</a
      ><a name="5411"
      > </a
      ><a name="5412" href="Stlc.html#4752" class="InductiveConstructor"
      >&#946;&#955;&#183;</a
      ><a name="5415"
      > </a
      ><a name="5416" href="Stlc.html#4139" class="InductiveConstructor"
      >value-true</a
      ><a name="5426"
      > </a
      ><a name="5427" href="Stlc.html#5298" class="InductiveConstructor Operator"
      >&#10217;</a
      ><a name="5428"
      >
    </a
      ><a name="5433" href="Stlc.html#3612" class="InductiveConstructor Operator"
      >if</a
      ><a name="5435"
      > </a
      ><a name="5436" href="Stlc.html#3583" class="InductiveConstructor"
      >true</a
      ><a name="5440"
      > </a
      ><a name="5441" href="Stlc.html#3612" class="InductiveConstructor Operator"
      >then</a
      ><a name="5445"
      > </a
      ><a name="5446" href="Stlc.html#3597" class="InductiveConstructor"
      >false</a
      ><a name="5451"
      > </a
      ><a name="5452" href="Stlc.html#3612" class="InductiveConstructor Operator"
      >else</a
      ><a name="5456"
      > </a
      ><a name="5457" href="Stlc.html#3583" class="InductiveConstructor"
      >true</a
      ><a name="5461"
      >
  </a
      ><a name="5464" href="Stlc.html#5298" class="InductiveConstructor Operator"
      >&#10233;&#10216;</a
      ><a name="5466"
      > </a
      ><a name="5467" href="Stlc.html#4942" class="InductiveConstructor"
      >&#946;if-true</a
      ><a name="5475"
      > </a
      ><a name="5476" href="Stlc.html#5298" class="InductiveConstructor Operator"
      >&#10217;</a
      ><a name="5477"
      >
    </a
      ><a name="5482" href="Stlc.html#3597" class="InductiveConstructor"
      >false</a
      ><a name="5487"
      >
  </a
      ><a name="5490" href="Stlc.html#5278" class="InductiveConstructor Operator"
      >&#8718;</a
      ><a name="5491"
      >

</a
      ><a name="5493" href="Stlc.html#5493" class="Function"
      >reduction&#8322;</a
      ><a name="5503"
      > </a
      ><a name="5504" class="Symbol"
      >:</a
      ><a name="5505"
      > </a
      ><a name="5506" href="Stlc.html#3911" class="Function"
      >two</a
      ><a name="5509"
      > </a
      ><a name="5510" href="Stlc.html#3556" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="5511"
      > </a
      ><a name="5512" href="Stlc.html#3907" class="Function"
      >not</a
      ><a name="5515"
      > </a
      ><a name="5516" href="Stlc.html#3556" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="5517"
      > </a
      ><a name="5518" href="Stlc.html#3583" class="InductiveConstructor"
      >true</a
      ><a name="5522"
      > </a
      ><a name="5523" href="Stlc.html#5245" class="Datatype Operator"
      >&#10233;*</a
      ><a name="5525"
      > </a
      ><a name="5526" href="Stlc.html#3583" class="InductiveConstructor"
      >true</a
      ><a name="5530"
      >
</a
      ><a name="5531" href="Stlc.html#5493" class="Function"
      >reduction&#8322;</a
      ><a name="5541"
      > </a
      ><a name="5542" class="Symbol"
      >=</a
      ><a name="5543"
      >
    </a
      ><a name="5548" href="Stlc.html#3911" class="Function"
      >two</a
      ><a name="5551"
      > </a
      ><a name="5552" href="Stlc.html#3556" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="5553"
      > </a
      ><a name="5554" href="Stlc.html#3907" class="Function"
      >not</a
      ><a name="5557"
      > </a
      ><a name="5558" href="Stlc.html#3556" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="5559"
      > </a
      ><a name="5560" href="Stlc.html#3583" class="InductiveConstructor"
      >true</a
      ><a name="5564"
      >
  </a
      ><a name="5567" href="Stlc.html#5298" class="InductiveConstructor Operator"
      >&#10233;&#10216;</a
      ><a name="5569"
      > </a
      ><a name="5570" href="Stlc.html#4822" class="InductiveConstructor"
      >&#958;&#183;&#8321;</a
      ><a name="5573"
      > </a
      ><a name="5574" class="Symbol"
      >(</a
      ><a name="5575" href="Stlc.html#4752" class="InductiveConstructor"
      >&#946;&#955;&#183;</a
      ><a name="5578"
      > </a
      ><a name="5579" href="Stlc.html#4090" class="InductiveConstructor"
      >value-&#955;</a
      ><a name="5586" class="Symbol"
      >)</a
      ><a name="5587"
      > </a
      ><a name="5588" href="Stlc.html#5298" class="InductiveConstructor Operator"
      >&#10217;</a
      ><a name="5589"
      >
    </a
      ><a name="5594" class="Symbol"
      >(</a
      ><a name="5595" href="Stlc.html#3520" class="InductiveConstructor Operator"
      >&#955;[</a
      ><a name="5597"
      > </a
      ><a name="5598" href="Stlc.html#3877" class="Function"
      >x</a
      ><a name="5599"
      > </a
      ><a name="5600" href="Stlc.html#3520" class="InductiveConstructor Operator"
      >&#8758;</a
      ><a name="5601"
      > </a
      ><a name="5602" href="Stlc.html#2577" class="InductiveConstructor"
      >&#120121;</a
      ><a name="5603"
      > </a
      ><a name="5604" href="Stlc.html#3520" class="InductiveConstructor Operator"
      >]</a
      ><a name="5605"
      > </a
      ><a name="5606" href="Stlc.html#3907" class="Function"
      >not</a
      ><a name="5609"
      > </a
      ><a name="5610" href="Stlc.html#3556" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="5611"
      > </a
      ><a name="5612" class="Symbol"
      >(</a
      ><a name="5613" href="Stlc.html#3907" class="Function"
      >not</a
      ><a name="5616"
      > </a
      ><a name="5617" href="Stlc.html#3556" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="5618"
      > </a
      ><a name="5619" href="Stlc.html#3504" class="InductiveConstructor"
      >`</a
      ><a name="5620"
      > </a
      ><a name="5621" href="Stlc.html#3877" class="Function"
      >x</a
      ><a name="5622" class="Symbol"
      >))</a
      ><a name="5624"
      > </a
      ><a name="5625" href="Stlc.html#3556" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="5626"
      > </a
      ><a name="5627" href="Stlc.html#3583" class="InductiveConstructor"
      >true</a
      ><a name="5631"
      >
  </a
      ><a name="5634" href="Stlc.html#5298" class="InductiveConstructor Operator"
      >&#10233;&#10216;</a
      ><a name="5636"
      > </a
      ><a name="5637" href="Stlc.html#4752" class="InductiveConstructor"
      >&#946;&#955;&#183;</a
      ><a name="5640"
      > </a
      ><a name="5641" href="Stlc.html#4139" class="InductiveConstructor"
      >value-true</a
      ><a name="5651"
      > </a
      ><a name="5652" href="Stlc.html#5298" class="InductiveConstructor Operator"
      >&#10217;</a
      ><a name="5653"
      >
    </a
      ><a name="5658" href="Stlc.html#3907" class="Function"
      >not</a
      ><a name="5661"
      > </a
      ><a name="5662" href="Stlc.html#3556" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="5663"
      > </a
      ><a name="5664" class="Symbol"
      >(</a
      ><a name="5665" href="Stlc.html#3907" class="Function"
      >not</a
      ><a name="5668"
      > </a
      ><a name="5669" href="Stlc.html#3556" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="5670"
      > </a
      ><a name="5671" href="Stlc.html#3583" class="InductiveConstructor"
      >true</a
      ><a name="5675" class="Symbol"
      >)</a
      ><a name="5676"
      >
  </a
      ><a name="5679" href="Stlc.html#5298" class="InductiveConstructor Operator"
      >&#10233;&#10216;</a
      ><a name="5681"
      > </a
      ><a name="5682" href="Stlc.html#4875" class="InductiveConstructor"
      >&#958;&#183;&#8322;</a
      ><a name="5685"
      > </a
      ><a name="5686" href="Stlc.html#4090" class="InductiveConstructor"
      >value-&#955;</a
      ><a name="5693"
      > </a
      ><a name="5694" class="Symbol"
      >(</a
      ><a name="5695" href="Stlc.html#4752" class="InductiveConstructor"
      >&#946;&#955;&#183;</a
      ><a name="5698"
      > </a
      ><a name="5699" href="Stlc.html#4139" class="InductiveConstructor"
      >value-true</a
      ><a name="5709" class="Symbol"
      >)</a
      ><a name="5710"
      > </a
      ><a name="5711" href="Stlc.html#5298" class="InductiveConstructor Operator"
      >&#10217;</a
      ><a name="5712"
      >
    </a
      ><a name="5717" href="Stlc.html#3907" class="Function"
      >not</a
      ><a name="5720"
      > </a
      ><a name="5721" href="Stlc.html#3556" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="5722"
      > </a
      ><a name="5723" class="Symbol"
      >(</a
      ><a name="5724" href="Stlc.html#3612" class="InductiveConstructor Operator"
      >if</a
      ><a name="5726"
      > </a
      ><a name="5727" href="Stlc.html#3583" class="InductiveConstructor"
      >true</a
      ><a name="5731"
      > </a
      ><a name="5732" href="Stlc.html#3612" class="InductiveConstructor Operator"
      >then</a
      ><a name="5736"
      > </a
      ><a name="5737" href="Stlc.html#3597" class="InductiveConstructor"
      >false</a
      ><a name="5742"
      > </a
      ><a name="5743" href="Stlc.html#3612" class="InductiveConstructor Operator"
      >else</a
      ><a name="5747"
      > </a
      ><a name="5748" href="Stlc.html#3583" class="InductiveConstructor"
      >true</a
      ><a name="5752" class="Symbol"
      >)</a
      ><a name="5753"
      >
  </a
      ><a name="5756" href="Stlc.html#5298" class="InductiveConstructor Operator"
      >&#10233;&#10216;</a
      ><a name="5758"
      > </a
      ><a name="5759" href="Stlc.html#4875" class="InductiveConstructor"
      >&#958;&#183;&#8322;</a
      ><a name="5762"
      > </a
      ><a name="5763" href="Stlc.html#4090" class="InductiveConstructor"
      >value-&#955;</a
      ><a name="5770"
      > </a
      ><a name="5771" href="Stlc.html#4942" class="InductiveConstructor"
      >&#946;if-true</a
      ><a name="5779"
      >  </a
      ><a name="5781" href="Stlc.html#5298" class="InductiveConstructor Operator"
      >&#10217;</a
      ><a name="5782"
      >
    </a
      ><a name="5787" href="Stlc.html#3907" class="Function"
      >not</a
      ><a name="5790"
      > </a
      ><a name="5791" href="Stlc.html#3556" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="5792"
      > </a
      ><a name="5793" href="Stlc.html#3597" class="InductiveConstructor"
      >false</a
      ><a name="5798"
      >
  </a
      ><a name="5801" href="Stlc.html#5298" class="InductiveConstructor Operator"
      >&#10233;&#10216;</a
      ><a name="5803"
      > </a
      ><a name="5804" href="Stlc.html#4752" class="InductiveConstructor"
      >&#946;&#955;&#183;</a
      ><a name="5807"
      > </a
      ><a name="5808" href="Stlc.html#4166" class="InductiveConstructor"
      >value-false</a
      ><a name="5819"
      > </a
      ><a name="5820" href="Stlc.html#5298" class="InductiveConstructor Operator"
      >&#10217;</a
      ><a name="5821"
      >
    </a
      ><a name="5826" href="Stlc.html#3612" class="InductiveConstructor Operator"
      >if</a
      ><a name="5828"
      > </a
      ><a name="5829" href="Stlc.html#3597" class="InductiveConstructor"
      >false</a
      ><a name="5834"
      > </a
      ><a name="5835" href="Stlc.html#3612" class="InductiveConstructor Operator"
      >then</a
      ><a name="5839"
      > </a
      ><a name="5840" href="Stlc.html#3597" class="InductiveConstructor"
      >false</a
      ><a name="5845"
      > </a
      ><a name="5846" href="Stlc.html#3612" class="InductiveConstructor Operator"
      >else</a
      ><a name="5850"
      > </a
      ><a name="5851" href="Stlc.html#3583" class="InductiveConstructor"
      >true</a
      ><a name="5855"
      >
  </a
      ><a name="5858" href="Stlc.html#5298" class="InductiveConstructor Operator"
      >&#10233;&#10216;</a
      ><a name="5860"
      > </a
      ><a name="5861" href="Stlc.html#4995" class="InductiveConstructor"
      >&#946;if-false</a
      ><a name="5870"
      > </a
      ><a name="5871" href="Stlc.html#5298" class="InductiveConstructor Operator"
      >&#10217;</a
      ><a name="5872"
      >
    </a
      ><a name="5877" href="Stlc.html#3583" class="InductiveConstructor"
      >true</a
      ><a name="5881"
      >
  </a
      ><a name="5884" href="Stlc.html#5278" class="InductiveConstructor Operator"
      >&#8718;</a
      >

</pre>

Much of the above, though not all, can be filled in using C-c C-r and C-c C-s.



## Type rules

<pre class="Agda">

<a name="6008" href="Stlc.html#6008" class="Function"
      >Context</a
      ><a name="6015"
      > </a
      ><a name="6016" class="Symbol"
      >:</a
      ><a name="6017"
      > </a
      ><a name="6018" class="PrimitiveType"
      >Set</a
      ><a name="6021"
      >
</a
      ><a name="6022" href="Stlc.html#6008" class="Function"
      >Context</a
      ><a name="6029"
      > </a
      ><a name="6030" class="Symbol"
      >=</a
      ><a name="6031"
      > </a
      ><a name="6032" href="Maps.html#10132" class="Function"
      >PartialMap</a
      ><a name="6042"
      > </a
      ><a name="6043" href="Stlc.html#2531" class="Datatype"
      >Type</a
      ><a name="6047"
      >

</a
      ><a name="6049" class="Keyword"
      >infix</a
      ><a name="6054"
      > </a
      ><a name="6055" class="Number"
      >10</a
      ><a name="6057"
      > </a
      ><a name="6058" href="Stlc.html#6070" class="Datatype Operator"
      >_&#8866;_&#8758;_</a
      ><a name="6063"
      >

</a
      ><a name="6065" class="Keyword"
      >data</a
      ><a name="6069"
      > </a
      ><a name="6070" href="Stlc.html#6070" class="Datatype Operator"
      >_&#8866;_&#8758;_</a
      ><a name="6075"
      > </a
      ><a name="6076" class="Symbol"
      >:</a
      ><a name="6077"
      > </a
      ><a name="6078" href="Stlc.html#6008" class="Function"
      >Context</a
      ><a name="6085"
      > </a
      ><a name="6086" class="Symbol"
      >&#8594;</a
      ><a name="6087"
      > </a
      ><a name="6088" href="Stlc.html#3485" class="Datatype"
      >Term</a
      ><a name="6092"
      > </a
      ><a name="6093" class="Symbol"
      >&#8594;</a
      ><a name="6094"
      > </a
      ><a name="6095" href="Stlc.html#2531" class="Datatype"
      >Type</a
      ><a name="6099"
      > </a
      ><a name="6100" class="Symbol"
      >&#8594;</a
      ><a name="6101"
      > </a
      ><a name="6102" class="PrimitiveType"
      >Set</a
      ><a name="6105"
      > </a
      ><a name="6106" class="Keyword"
      >where</a
      ><a name="6111"
      >
  </a
      ><a name="6114" href="Stlc.html#6114" class="InductiveConstructor"
      >Ax</a
      ><a name="6116"
      > </a
      ><a name="6117" class="Symbol"
      >:</a
      ><a name="6118"
      > </a
      ><a name="6119" class="Symbol"
      >&#8704;</a
      ><a name="6120"
      > </a
      ><a name="6121" class="Symbol"
      >{</a
      ><a name="6122" href="Stlc.html#6122" class="Bound"
      >&#915;</a
      ><a name="6123"
      > </a
      ><a name="6124" href="Stlc.html#6124" class="Bound"
      >x</a
      ><a name="6125"
      > </a
      ><a name="6126" href="Stlc.html#6126" class="Bound"
      >A</a
      ><a name="6127" class="Symbol"
      >}</a
      ><a name="6128"
      > </a
      ><a name="6129" class="Symbol"
      >&#8594;</a
      ><a name="6130"
      >
    </a
      ><a name="6135" href="Stlc.html#6122" class="Bound"
      >&#915;</a
      ><a name="6136"
      > </a
      ><a name="6137" href="Stlc.html#6124" class="Bound"
      >x</a
      ><a name="6138"
      > </a
      ><a name="6139" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="6140"
      > </a
      ><a name="6141" href="https://agda.github.io/agda-stdlib/Data.Maybe.Base.html#373" class="InductiveConstructor"
      >just</a
      ><a name="6145"
      > </a
      ><a name="6146" href="Stlc.html#6126" class="Bound"
      >A</a
      ><a name="6147"
      > </a
      ><a name="6148" class="Symbol"
      >&#8594;</a
      ><a name="6149"
      >
    </a
      ><a name="6154" href="Stlc.html#6122" class="Bound"
      >&#915;</a
      ><a name="6155"
      > </a
      ><a name="6156" href="Stlc.html#6070" class="Datatype Operator"
      >&#8866;</a
      ><a name="6157"
      > </a
      ><a name="6158" href="Stlc.html#3504" class="InductiveConstructor"
      >`</a
      ><a name="6159"
      > </a
      ><a name="6160" href="Stlc.html#6124" class="Bound"
      >x</a
      ><a name="6161"
      > </a
      ><a name="6162" href="Stlc.html#6070" class="Datatype Operator"
      >&#8758;</a
      ><a name="6163"
      > </a
      ><a name="6164" href="Stlc.html#6126" class="Bound"
      >A</a
      ><a name="6165"
      >
  </a
      ><a name="6168" href="Stlc.html#6168" class="InductiveConstructor"
      >&#8658;-I</a
      ><a name="6171"
      > </a
      ><a name="6172" class="Symbol"
      >:</a
      ><a name="6173"
      > </a
      ><a name="6174" class="Symbol"
      >&#8704;</a
      ><a name="6175"
      > </a
      ><a name="6176" class="Symbol"
      >{</a
      ><a name="6177" href="Stlc.html#6177" class="Bound"
      >&#915;</a
      ><a name="6178"
      > </a
      ><a name="6179" href="Stlc.html#6179" class="Bound"
      >x</a
      ><a name="6180"
      > </a
      ><a name="6181" href="Stlc.html#6181" class="Bound"
      >N</a
      ><a name="6182"
      > </a
      ><a name="6183" href="Stlc.html#6183" class="Bound"
      >A</a
      ><a name="6184"
      > </a
      ><a name="6185" href="Stlc.html#6185" class="Bound"
      >B</a
      ><a name="6186" class="Symbol"
      >}</a
      ><a name="6187"
      > </a
      ><a name="6188" class="Symbol"
      >&#8594;</a
      ><a name="6189"
      >
    </a
      ><a name="6194" href="Stlc.html#6177" class="Bound"
      >&#915;</a
      ><a name="6195"
      > </a
      ><a name="6196" href="Maps.html#10368" class="Function Operator"
      >,</a
      ><a name="6197"
      > </a
      ><a name="6198" href="Stlc.html#6179" class="Bound"
      >x</a
      ><a name="6199"
      > </a
      ><a name="6200" href="Maps.html#10368" class="Function Operator"
      >&#8758;</a
      ><a name="6201"
      > </a
      ><a name="6202" href="Stlc.html#6183" class="Bound"
      >A</a
      ><a name="6203"
      > </a
      ><a name="6204" href="Stlc.html#6070" class="Datatype Operator"
      >&#8866;</a
      ><a name="6205"
      > </a
      ><a name="6206" href="Stlc.html#6181" class="Bound"
      >N</a
      ><a name="6207"
      > </a
      ><a name="6208" href="Stlc.html#6070" class="Datatype Operator"
      >&#8758;</a
      ><a name="6209"
      > </a
      ><a name="6210" href="Stlc.html#6185" class="Bound"
      >B</a
      ><a name="6211"
      > </a
      ><a name="6212" class="Symbol"
      >&#8594;</a
      ><a name="6213"
      >
    </a
      ><a name="6218" href="Stlc.html#6177" class="Bound"
      >&#915;</a
      ><a name="6219"
      > </a
      ><a name="6220" href="Stlc.html#6070" class="Datatype Operator"
      >&#8866;</a
      ><a name="6221"
      > </a
      ><a name="6222" href="Stlc.html#3520" class="InductiveConstructor Operator"
      >&#955;[</a
      ><a name="6224"
      > </a
      ><a name="6225" href="Stlc.html#6179" class="Bound"
      >x</a
      ><a name="6226"
      > </a
      ><a name="6227" href="Stlc.html#3520" class="InductiveConstructor Operator"
      >&#8758;</a
      ><a name="6228"
      > </a
      ><a name="6229" href="Stlc.html#6183" class="Bound"
      >A</a
      ><a name="6230"
      > </a
      ><a name="6231" href="Stlc.html#3520" class="InductiveConstructor Operator"
      >]</a
      ><a name="6232"
      > </a
      ><a name="6233" href="Stlc.html#6181" class="Bound"
      >N</a
      ><a name="6234"
      > </a
      ><a name="6235" href="Stlc.html#6070" class="Datatype Operator"
      >&#8758;</a
      ><a name="6236"
      > </a
      ><a name="6237" href="Stlc.html#6183" class="Bound"
      >A</a
      ><a name="6238"
      > </a
      ><a name="6239" href="Stlc.html#2550" class="InductiveConstructor Operator"
      >&#8658;</a
      ><a name="6240"
      > </a
      ><a name="6241" href="Stlc.html#6185" class="Bound"
      >B</a
      ><a name="6242"
      >
  </a
      ><a name="6245" href="Stlc.html#6245" class="InductiveConstructor"
      >&#8658;-E</a
      ><a name="6248"
      > </a
      ><a name="6249" class="Symbol"
      >:</a
      ><a name="6250"
      > </a
      ><a name="6251" class="Symbol"
      >&#8704;</a
      ><a name="6252"
      > </a
      ><a name="6253" class="Symbol"
      >{</a
      ><a name="6254" href="Stlc.html#6254" class="Bound"
      >&#915;</a
      ><a name="6255"
      > </a
      ><a name="6256" href="Stlc.html#6256" class="Bound"
      >L</a
      ><a name="6257"
      > </a
      ><a name="6258" href="Stlc.html#6258" class="Bound"
      >M</a
      ><a name="6259"
      > </a
      ><a name="6260" href="Stlc.html#6260" class="Bound"
      >A</a
      ><a name="6261"
      > </a
      ><a name="6262" href="Stlc.html#6262" class="Bound"
      >B</a
      ><a name="6263" class="Symbol"
      >}</a
      ><a name="6264"
      > </a
      ><a name="6265" class="Symbol"
      >&#8594;</a
      ><a name="6266"
      >
    </a
      ><a name="6271" href="Stlc.html#6254" class="Bound"
      >&#915;</a
      ><a name="6272"
      > </a
      ><a name="6273" href="Stlc.html#6070" class="Datatype Operator"
      >&#8866;</a
      ><a name="6274"
      > </a
      ><a name="6275" href="Stlc.html#6256" class="Bound"
      >L</a
      ><a name="6276"
      > </a
      ><a name="6277" href="Stlc.html#6070" class="Datatype Operator"
      >&#8758;</a
      ><a name="6278"
      > </a
      ><a name="6279" href="Stlc.html#6260" class="Bound"
      >A</a
      ><a name="6280"
      > </a
      ><a name="6281" href="Stlc.html#2550" class="InductiveConstructor Operator"
      >&#8658;</a
      ><a name="6282"
      > </a
      ><a name="6283" href="Stlc.html#6262" class="Bound"
      >B</a
      ><a name="6284"
      > </a
      ><a name="6285" class="Symbol"
      >&#8594;</a
      ><a name="6286"
      >
    </a
      ><a name="6291" href="Stlc.html#6254" class="Bound"
      >&#915;</a
      ><a name="6292"
      > </a
      ><a name="6293" href="Stlc.html#6070" class="Datatype Operator"
      >&#8866;</a
      ><a name="6294"
      > </a
      ><a name="6295" href="Stlc.html#6258" class="Bound"
      >M</a
      ><a name="6296"
      > </a
      ><a name="6297" href="Stlc.html#6070" class="Datatype Operator"
      >&#8758;</a
      ><a name="6298"
      > </a
      ><a name="6299" href="Stlc.html#6260" class="Bound"
      >A</a
      ><a name="6300"
      > </a
      ><a name="6301" class="Symbol"
      >&#8594;</a
      ><a name="6302"
      >
    </a
      ><a name="6307" href="Stlc.html#6254" class="Bound"
      >&#915;</a
      ><a name="6308"
      > </a
      ><a name="6309" href="Stlc.html#6070" class="Datatype Operator"
      >&#8866;</a
      ><a name="6310"
      > </a
      ><a name="6311" href="Stlc.html#6256" class="Bound"
      >L</a
      ><a name="6312"
      > </a
      ><a name="6313" href="Stlc.html#3556" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="6314"
      > </a
      ><a name="6315" href="Stlc.html#6258" class="Bound"
      >M</a
      ><a name="6316"
      > </a
      ><a name="6317" href="Stlc.html#6070" class="Datatype Operator"
      >&#8758;</a
      ><a name="6318"
      > </a
      ><a name="6319" href="Stlc.html#6262" class="Bound"
      >B</a
      ><a name="6320"
      >
  </a
      ><a name="6323" href="Stlc.html#6323" class="InductiveConstructor"
      >&#120121;-I&#8321;</a
      ><a name="6327"
      > </a
      ><a name="6328" class="Symbol"
      >:</a
      ><a name="6329"
      > </a
      ><a name="6330" class="Symbol"
      >&#8704;</a
      ><a name="6331"
      > </a
      ><a name="6332" class="Symbol"
      >{</a
      ><a name="6333" href="Stlc.html#6333" class="Bound"
      >&#915;</a
      ><a name="6334" class="Symbol"
      >}</a
      ><a name="6335"
      > </a
      ><a name="6336" class="Symbol"
      >&#8594;</a
      ><a name="6337"
      >
    </a
      ><a name="6342" href="Stlc.html#6333" class="Bound"
      >&#915;</a
      ><a name="6343"
      > </a
      ><a name="6344" href="Stlc.html#6070" class="Datatype Operator"
      >&#8866;</a
      ><a name="6345"
      > </a
      ><a name="6346" href="Stlc.html#3583" class="InductiveConstructor"
      >true</a
      ><a name="6350"
      > </a
      ><a name="6351" href="Stlc.html#6070" class="Datatype Operator"
      >&#8758;</a
      ><a name="6352"
      > </a
      ><a name="6353" href="Stlc.html#2577" class="InductiveConstructor"
      >&#120121;</a
      ><a name="6354"
      >
  </a
      ><a name="6357" href="Stlc.html#6357" class="InductiveConstructor"
      >&#120121;-I&#8322;</a
      ><a name="6361"
      > </a
      ><a name="6362" class="Symbol"
      >:</a
      ><a name="6363"
      > </a
      ><a name="6364" class="Symbol"
      >&#8704;</a
      ><a name="6365"
      > </a
      ><a name="6366" class="Symbol"
      >{</a
      ><a name="6367" href="Stlc.html#6367" class="Bound"
      >&#915;</a
      ><a name="6368" class="Symbol"
      >}</a
      ><a name="6369"
      > </a
      ><a name="6370" class="Symbol"
      >&#8594;</a
      ><a name="6371"
      >
    </a
      ><a name="6376" href="Stlc.html#6367" class="Bound"
      >&#915;</a
      ><a name="6377"
      > </a
      ><a name="6378" href="Stlc.html#6070" class="Datatype Operator"
      >&#8866;</a
      ><a name="6379"
      > </a
      ><a name="6380" href="Stlc.html#3597" class="InductiveConstructor"
      >false</a
      ><a name="6385"
      > </a
      ><a name="6386" href="Stlc.html#6070" class="Datatype Operator"
      >&#8758;</a
      ><a name="6387"
      > </a
      ><a name="6388" href="Stlc.html#2577" class="InductiveConstructor"
      >&#120121;</a
      ><a name="6389"
      >
  </a
      ><a name="6392" href="Stlc.html#6392" class="InductiveConstructor"
      >&#120121;-E</a
      ><a name="6395"
      > </a
      ><a name="6396" class="Symbol"
      >:</a
      ><a name="6397"
      > </a
      ><a name="6398" class="Symbol"
      >&#8704;</a
      ><a name="6399"
      > </a
      ><a name="6400" class="Symbol"
      >{</a
      ><a name="6401" href="Stlc.html#6401" class="Bound"
      >&#915;</a
      ><a name="6402"
      > </a
      ><a name="6403" href="Stlc.html#6403" class="Bound"
      >L</a
      ><a name="6404"
      > </a
      ><a name="6405" href="Stlc.html#6405" class="Bound"
      >M</a
      ><a name="6406"
      > </a
      ><a name="6407" href="Stlc.html#6407" class="Bound"
      >N</a
      ><a name="6408"
      > </a
      ><a name="6409" href="Stlc.html#6409" class="Bound"
      >A</a
      ><a name="6410" class="Symbol"
      >}</a
      ><a name="6411"
      > </a
      ><a name="6412" class="Symbol"
      >&#8594;</a
      ><a name="6413"
      >
    </a
      ><a name="6418" href="Stlc.html#6401" class="Bound"
      >&#915;</a
      ><a name="6419"
      > </a
      ><a name="6420" href="Stlc.html#6070" class="Datatype Operator"
      >&#8866;</a
      ><a name="6421"
      > </a
      ><a name="6422" href="Stlc.html#6403" class="Bound"
      >L</a
      ><a name="6423"
      > </a
      ><a name="6424" href="Stlc.html#6070" class="Datatype Operator"
      >&#8758;</a
      ><a name="6425"
      > </a
      ><a name="6426" href="Stlc.html#2577" class="InductiveConstructor"
      >&#120121;</a
      ><a name="6427"
      > </a
      ><a name="6428" class="Symbol"
      >&#8594;</a
      ><a name="6429"
      >
    </a
      ><a name="6434" href="Stlc.html#6401" class="Bound"
      >&#915;</a
      ><a name="6435"
      > </a
      ><a name="6436" href="Stlc.html#6070" class="Datatype Operator"
      >&#8866;</a
      ><a name="6437"
      > </a
      ><a name="6438" href="Stlc.html#6405" class="Bound"
      >M</a
      ><a name="6439"
      > </a
      ><a name="6440" href="Stlc.html#6070" class="Datatype Operator"
      >&#8758;</a
      ><a name="6441"
      > </a
      ><a name="6442" href="Stlc.html#6409" class="Bound"
      >A</a
      ><a name="6443"
      > </a
      ><a name="6444" class="Symbol"
      >&#8594;</a
      ><a name="6445"
      >
    </a
      ><a name="6450" href="Stlc.html#6401" class="Bound"
      >&#915;</a
      ><a name="6451"
      > </a
      ><a name="6452" href="Stlc.html#6070" class="Datatype Operator"
      >&#8866;</a
      ><a name="6453"
      > </a
      ><a name="6454" href="Stlc.html#6407" class="Bound"
      >N</a
      ><a name="6455"
      > </a
      ><a name="6456" href="Stlc.html#6070" class="Datatype Operator"
      >&#8758;</a
      ><a name="6457"
      > </a
      ><a name="6458" href="Stlc.html#6409" class="Bound"
      >A</a
      ><a name="6459"
      > </a
      ><a name="6460" class="Symbol"
      >&#8594;</a
      ><a name="6461"
      >
    </a
      ><a name="6466" href="Stlc.html#6401" class="Bound"
      >&#915;</a
      ><a name="6467"
      > </a
      ><a name="6468" href="Stlc.html#6070" class="Datatype Operator"
      >&#8866;</a
      ><a name="6469"
      > </a
      ><a name="6470" href="Stlc.html#3612" class="InductiveConstructor Operator"
      >if</a
      ><a name="6472"
      > </a
      ><a name="6473" href="Stlc.html#6403" class="Bound"
      >L</a
      ><a name="6474"
      > </a
      ><a name="6475" href="Stlc.html#3612" class="InductiveConstructor Operator"
      >then</a
      ><a name="6479"
      > </a
      ><a name="6480" href="Stlc.html#6405" class="Bound"
      >M</a
      ><a name="6481"
      > </a
      ><a name="6482" href="Stlc.html#3612" class="InductiveConstructor Operator"
      >else</a
      ><a name="6486"
      > </a
      ><a name="6487" href="Stlc.html#6407" class="Bound"
      >N</a
      ><a name="6488"
      > </a
      ><a name="6489" href="Stlc.html#6070" class="Datatype Operator"
      >&#8758;</a
      ><a name="6490"
      > </a
      ><a name="6491" href="Stlc.html#6409" class="Bound"
      >A</a
      >

</pre>

## Example type derivations

<pre class="Agda">

<a name="6551" href="Stlc.html#6551" class="Function"
      >typing&#8321;</a
      ><a name="6558"
      > </a
      ><a name="6559" class="Symbol"
      >:</a
      ><a name="6560"
      > </a
      ><a name="6561" href="Maps.html#10265" class="Function"
      >&#8709;</a
      ><a name="6562"
      > </a
      ><a name="6563" href="Stlc.html#6070" class="Datatype Operator"
      >&#8866;</a
      ><a name="6564"
      > </a
      ><a name="6565" href="Stlc.html#3907" class="Function"
      >not</a
      ><a name="6568"
      > </a
      ><a name="6569" href="Stlc.html#6070" class="Datatype Operator"
      >&#8758;</a
      ><a name="6570"
      > </a
      ><a name="6571" href="Stlc.html#2577" class="InductiveConstructor"
      >&#120121;</a
      ><a name="6572"
      > </a
      ><a name="6573" href="Stlc.html#2550" class="InductiveConstructor Operator"
      >&#8658;</a
      ><a name="6574"
      > </a
      ><a name="6575" href="Stlc.html#2577" class="InductiveConstructor"
      >&#120121;</a
      ><a name="6576"
      >
</a
      ><a name="6577" href="Stlc.html#6551" class="Function"
      >typing&#8321;</a
      ><a name="6584"
      > </a
      ><a name="6585" class="Symbol"
      >=</a
      ><a name="6586"
      > </a
      ><a name="6587" href="Stlc.html#6168" class="InductiveConstructor"
      >&#8658;-I</a
      ><a name="6590"
      > </a
      ><a name="6591" class="Symbol"
      >(</a
      ><a name="6592" href="Stlc.html#6392" class="InductiveConstructor"
      >&#120121;-E</a
      ><a name="6595"
      > </a
      ><a name="6596" class="Symbol"
      >(</a
      ><a name="6597" href="Stlc.html#6114" class="InductiveConstructor"
      >Ax</a
      ><a name="6599"
      > </a
      ><a name="6600" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="6604" class="Symbol"
      >)</a
      ><a name="6605"
      > </a
      ><a name="6606" href="Stlc.html#6357" class="InductiveConstructor"
      >&#120121;-I&#8322;</a
      ><a name="6610"
      > </a
      ><a name="6611" href="Stlc.html#6323" class="InductiveConstructor"
      >&#120121;-I&#8321;</a
      ><a name="6615" class="Symbol"
      >)</a
      ><a name="6616"
      >

</a
      ><a name="6618" href="Stlc.html#6618" class="Function"
      >typing&#8322;</a
      ><a name="6625"
      > </a
      ><a name="6626" class="Symbol"
      >:</a
      ><a name="6627"
      > </a
      ><a name="6628" href="Maps.html#10265" class="Function"
      >&#8709;</a
      ><a name="6629"
      > </a
      ><a name="6630" href="Stlc.html#6070" class="Datatype Operator"
      >&#8866;</a
      ><a name="6631"
      > </a
      ><a name="6632" href="Stlc.html#3911" class="Function"
      >two</a
      ><a name="6635"
      > </a
      ><a name="6636" href="Stlc.html#6070" class="Datatype Operator"
      >&#8758;</a
      ><a name="6637"
      > </a
      ><a name="6638" class="Symbol"
      >(</a
      ><a name="6639" href="Stlc.html#2577" class="InductiveConstructor"
      >&#120121;</a
      ><a name="6640"
      > </a
      ><a name="6641" href="Stlc.html#2550" class="InductiveConstructor Operator"
      >&#8658;</a
      ><a name="6642"
      > </a
      ><a name="6643" href="Stlc.html#2577" class="InductiveConstructor"
      >&#120121;</a
      ><a name="6644" class="Symbol"
      >)</a
      ><a name="6645"
      > </a
      ><a name="6646" href="Stlc.html#2550" class="InductiveConstructor Operator"
      >&#8658;</a
      ><a name="6647"
      > </a
      ><a name="6648" href="Stlc.html#2577" class="InductiveConstructor"
      >&#120121;</a
      ><a name="6649"
      > </a
      ><a name="6650" href="Stlc.html#2550" class="InductiveConstructor Operator"
      >&#8658;</a
      ><a name="6651"
      > </a
      ><a name="6652" href="Stlc.html#2577" class="InductiveConstructor"
      >&#120121;</a
      ><a name="6653"
      >
</a
      ><a name="6654" href="Stlc.html#6618" class="Function"
      >typing&#8322;</a
      ><a name="6661"
      > </a
      ><a name="6662" class="Symbol"
      >=</a
      ><a name="6663"
      > </a
      ><a name="6664" href="Stlc.html#6168" class="InductiveConstructor"
      >&#8658;-I</a
      ><a name="6667"
      > </a
      ><a name="6668" class="Symbol"
      >(</a
      ><a name="6669" href="Stlc.html#6168" class="InductiveConstructor"
      >&#8658;-I</a
      ><a name="6672"
      > </a
      ><a name="6673" class="Symbol"
      >(</a
      ><a name="6674" href="Stlc.html#6245" class="InductiveConstructor"
      >&#8658;-E</a
      ><a name="6677"
      > </a
      ><a name="6678" class="Symbol"
      >(</a
      ><a name="6679" href="Stlc.html#6114" class="InductiveConstructor"
      >Ax</a
      ><a name="6681"
      > </a
      ><a name="6682" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="6686" class="Symbol"
      >)</a
      ><a name="6687"
      > </a
      ><a name="6688" class="Symbol"
      >(</a
      ><a name="6689" href="Stlc.html#6245" class="InductiveConstructor"
      >&#8658;-E</a
      ><a name="6692"
      > </a
      ><a name="6693" class="Symbol"
      >(</a
      ><a name="6694" href="Stlc.html#6114" class="InductiveConstructor"
      >Ax</a
      ><a name="6696"
      > </a
      ><a name="6697" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="6701" class="Symbol"
      >)</a
      ><a name="6702"
      > </a
      ><a name="6703" class="Symbol"
      >(</a
      ><a name="6704" href="Stlc.html#6114" class="InductiveConstructor"
      >Ax</a
      ><a name="6706"
      > </a
      ><a name="6707" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="6711" class="Symbol"
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


