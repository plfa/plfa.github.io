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
  * Variables, `\` x`
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

<a name="3420" class="Keyword"
      >infixl</a
      ><a name="3426"
      > </a
      ><a name="3427" class="Number"
      >20</a
      ><a name="3429"
      > </a
      ><a name="3430" href="Stlc.html#3553" class="InductiveConstructor Operator"
      >_&#183;_</a
      ><a name="3433"
      >
</a
      ><a name="3434" class="Keyword"
      >infix</a
      ><a name="3439"
      >  </a
      ><a name="3441" class="Number"
      >15</a
      ><a name="3443"
      > </a
      ><a name="3444" href="Stlc.html#3517" class="InductiveConstructor Operator"
      >&#955;[_&#8758;_]_</a
      ><a name="3451"
      >
</a
      ><a name="3452" class="Keyword"
      >infix</a
      ><a name="3457"
      >  </a
      ><a name="3459" class="Number"
      >15</a
      ><a name="3461"
      > </a
      ><a name="3462" href="Stlc.html#3609" class="InductiveConstructor Operator"
      >if_then_else_</a
      ><a name="3475"
      >

</a
      ><a name="3477" class="Keyword"
      >data</a
      ><a name="3481"
      > </a
      ><a name="3482" href="Stlc.html#3482" class="Datatype"
      >Term</a
      ><a name="3486"
      > </a
      ><a name="3487" class="Symbol"
      >:</a
      ><a name="3488"
      > </a
      ><a name="3489" class="PrimitiveType"
      >Set</a
      ><a name="3492"
      > </a
      ><a name="3493" class="Keyword"
      >where</a
      ><a name="3498"
      >
  </a
      ><a name="3501" href="Stlc.html#3501" class="InductiveConstructor"
      >`</a
      ><a name="3502"
      > </a
      ><a name="3503" class="Symbol"
      >:</a
      ><a name="3504"
      > </a
      ><a name="3505" href="Maps.html#2171" class="Datatype"
      >Id</a
      ><a name="3507"
      > </a
      ><a name="3508" class="Symbol"
      >&#8594;</a
      ><a name="3509"
      > </a
      ><a name="3510" href="Stlc.html#3482" class="Datatype"
      >Term</a
      ><a name="3514"
      >
  </a
      ><a name="3517" href="Stlc.html#3517" class="InductiveConstructor Operator"
      >&#955;[_&#8758;_]_</a
      ><a name="3524"
      > </a
      ><a name="3525" class="Symbol"
      >:</a
      ><a name="3526"
      > </a
      ><a name="3527" href="Maps.html#2171" class="Datatype"
      >Id</a
      ><a name="3529"
      > </a
      ><a name="3530" class="Symbol"
      >&#8594;</a
      ><a name="3531"
      > </a
      ><a name="3532" href="Stlc.html#2531" class="Datatype"
      >Type</a
      ><a name="3536"
      > </a
      ><a name="3537" class="Symbol"
      >&#8594;</a
      ><a name="3538"
      > </a
      ><a name="3539" href="Stlc.html#3482" class="Datatype"
      >Term</a
      ><a name="3543"
      > </a
      ><a name="3544" class="Symbol"
      >&#8594;</a
      ><a name="3545"
      > </a
      ><a name="3546" href="Stlc.html#3482" class="Datatype"
      >Term</a
      ><a name="3550"
      >
  </a
      ><a name="3553" href="Stlc.html#3553" class="InductiveConstructor Operator"
      >_&#183;_</a
      ><a name="3556"
      > </a
      ><a name="3557" class="Symbol"
      >:</a
      ><a name="3558"
      > </a
      ><a name="3559" href="Stlc.html#3482" class="Datatype"
      >Term</a
      ><a name="3563"
      > </a
      ><a name="3564" class="Symbol"
      >&#8594;</a
      ><a name="3565"
      > </a
      ><a name="3566" href="Stlc.html#3482" class="Datatype"
      >Term</a
      ><a name="3570"
      > </a
      ><a name="3571" class="Symbol"
      >&#8594;</a
      ><a name="3572"
      > </a
      ><a name="3573" href="Stlc.html#3482" class="Datatype"
      >Term</a
      ><a name="3577"
      >
  </a
      ><a name="3580" href="Stlc.html#3580" class="InductiveConstructor"
      >true</a
      ><a name="3584"
      > </a
      ><a name="3585" class="Symbol"
      >:</a
      ><a name="3586"
      > </a
      ><a name="3587" href="Stlc.html#3482" class="Datatype"
      >Term</a
      ><a name="3591"
      >
  </a
      ><a name="3594" href="Stlc.html#3594" class="InductiveConstructor"
      >false</a
      ><a name="3599"
      > </a
      ><a name="3600" class="Symbol"
      >:</a
      ><a name="3601"
      > </a
      ><a name="3602" href="Stlc.html#3482" class="Datatype"
      >Term</a
      ><a name="3606"
      >
  </a
      ><a name="3609" href="Stlc.html#3609" class="InductiveConstructor Operator"
      >if_then_else_</a
      ><a name="3622"
      > </a
      ><a name="3623" class="Symbol"
      >:</a
      ><a name="3624"
      > </a
      ><a name="3625" href="Stlc.html#3482" class="Datatype"
      >Term</a
      ><a name="3629"
      > </a
      ><a name="3630" class="Symbol"
      >&#8594;</a
      ><a name="3631"
      > </a
      ><a name="3632" href="Stlc.html#3482" class="Datatype"
      >Term</a
      ><a name="3636"
      > </a
      ><a name="3637" class="Symbol"
      >&#8594;</a
      ><a name="3638"
      > </a
      ><a name="3639" href="Stlc.html#3482" class="Datatype"
      >Term</a
      ><a name="3643"
      > </a
      ><a name="3644" class="Symbol"
      >&#8594;</a
      ><a name="3645"
      > </a
      ><a name="3646" href="Stlc.html#3482" class="Datatype"
      >Term</a
      >

</pre>

Each type introduces its own constructs, which come in pairs,
one to introduce (or construct) values of the type, and one to eliminate
(or deconstruct) them.

CONTINUE FROM HERE



Example terms.
<pre class="Agda">

<a name="3872" href="Stlc.html#3872" class="Function"
      >f</a
      ><a name="3873"
      > </a
      ><a name="3874" href="Stlc.html#3874" class="Function"
      >x</a
      ><a name="3875"
      > </a
      ><a name="3876" class="Symbol"
      >:</a
      ><a name="3877"
      > </a
      ><a name="3878" href="Maps.html#2171" class="Datatype"
      >Id</a
      ><a name="3880"
      >
</a
      ><a name="3881" href="Stlc.html#3872" class="Function"
      >f</a
      ><a name="3882"
      >  </a
      ><a name="3884" class="Symbol"
      >=</a
      ><a name="3885"
      >  </a
      ><a name="3887" href="Maps.html#2188" class="InductiveConstructor"
      >id</a
      ><a name="3889"
      > </a
      ><a name="3890" class="Number"
      >0</a
      ><a name="3891"
      >
</a
      ><a name="3892" href="Stlc.html#3874" class="Function"
      >x</a
      ><a name="3893"
      >  </a
      ><a name="3895" class="Symbol"
      >=</a
      ><a name="3896"
      >  </a
      ><a name="3898" href="Maps.html#2188" class="InductiveConstructor"
      >id</a
      ><a name="3900"
      > </a
      ><a name="3901" class="Number"
      >1</a
      ><a name="3902"
      >

</a
      ><a name="3904" href="Stlc.html#3904" class="Function"
      >not</a
      ><a name="3907"
      > </a
      ><a name="3908" href="Stlc.html#3908" class="Function"
      >two</a
      ><a name="3911"
      > </a
      ><a name="3912" class="Symbol"
      >:</a
      ><a name="3913"
      > </a
      ><a name="3914" href="Stlc.html#3482" class="Datatype"
      >Term</a
      ><a name="3918"
      > 
</a
      ><a name="3920" href="Stlc.html#3904" class="Function"
      >not</a
      ><a name="3923"
      > </a
      ><a name="3924" class="Symbol"
      >=</a
      ><a name="3925"
      >  </a
      ><a name="3927" href="Stlc.html#3517" class="InductiveConstructor Operator"
      >&#955;[</a
      ><a name="3929"
      > </a
      ><a name="3930" href="Stlc.html#3874" class="Function"
      >x</a
      ><a name="3931"
      > </a
      ><a name="3932" href="Stlc.html#3517" class="InductiveConstructor Operator"
      >&#8758;</a
      ><a name="3933"
      > </a
      ><a name="3934" href="Stlc.html#2577" class="InductiveConstructor"
      >&#120121;</a
      ><a name="3935"
      > </a
      ><a name="3936" href="Stlc.html#3517" class="InductiveConstructor Operator"
      >]</a
      ><a name="3937"
      > </a
      ><a name="3938" class="Symbol"
      >(</a
      ><a name="3939" href="Stlc.html#3609" class="InductiveConstructor Operator"
      >if</a
      ><a name="3941"
      > </a
      ><a name="3942" href="Stlc.html#3501" class="InductiveConstructor"
      >`</a
      ><a name="3943"
      > </a
      ><a name="3944" href="Stlc.html#3874" class="Function"
      >x</a
      ><a name="3945"
      > </a
      ><a name="3946" href="Stlc.html#3609" class="InductiveConstructor Operator"
      >then</a
      ><a name="3950"
      > </a
      ><a name="3951" href="Stlc.html#3594" class="InductiveConstructor"
      >false</a
      ><a name="3956"
      > </a
      ><a name="3957" href="Stlc.html#3609" class="InductiveConstructor Operator"
      >else</a
      ><a name="3961"
      > </a
      ><a name="3962" href="Stlc.html#3580" class="InductiveConstructor"
      >true</a
      ><a name="3966" class="Symbol"
      >)</a
      ><a name="3967"
      >
</a
      ><a name="3968" href="Stlc.html#3908" class="Function"
      >two</a
      ><a name="3971"
      > </a
      ><a name="3972" class="Symbol"
      >=</a
      ><a name="3973"
      >  </a
      ><a name="3975" href="Stlc.html#3517" class="InductiveConstructor Operator"
      >&#955;[</a
      ><a name="3977"
      > </a
      ><a name="3978" href="Stlc.html#3872" class="Function"
      >f</a
      ><a name="3979"
      > </a
      ><a name="3980" href="Stlc.html#3517" class="InductiveConstructor Operator"
      >&#8758;</a
      ><a name="3981"
      > </a
      ><a name="3982" href="Stlc.html#2577" class="InductiveConstructor"
      >&#120121;</a
      ><a name="3983"
      > </a
      ><a name="3984" href="Stlc.html#2550" class="InductiveConstructor Operator"
      >&#8658;</a
      ><a name="3985"
      > </a
      ><a name="3986" href="Stlc.html#2577" class="InductiveConstructor"
      >&#120121;</a
      ><a name="3987"
      > </a
      ><a name="3988" href="Stlc.html#3517" class="InductiveConstructor Operator"
      >]</a
      ><a name="3989"
      > </a
      ><a name="3990" href="Stlc.html#3517" class="InductiveConstructor Operator"
      >&#955;[</a
      ><a name="3992"
      > </a
      ><a name="3993" href="Stlc.html#3874" class="Function"
      >x</a
      ><a name="3994"
      > </a
      ><a name="3995" href="Stlc.html#3517" class="InductiveConstructor Operator"
      >&#8758;</a
      ><a name="3996"
      > </a
      ><a name="3997" href="Stlc.html#2577" class="InductiveConstructor"
      >&#120121;</a
      ><a name="3998"
      > </a
      ><a name="3999" href="Stlc.html#3517" class="InductiveConstructor Operator"
      >]</a
      ><a name="4000"
      > </a
      ><a name="4001" href="Stlc.html#3501" class="InductiveConstructor"
      >`</a
      ><a name="4002"
      > </a
      ><a name="4003" href="Stlc.html#3872" class="Function"
      >f</a
      ><a name="4004"
      > </a
      ><a name="4005" href="Stlc.html#3553" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="4006"
      > </a
      ><a name="4007" class="Symbol"
      >(</a
      ><a name="4008" href="Stlc.html#3501" class="InductiveConstructor"
      >`</a
      ><a name="4009"
      > </a
      ><a name="4010" href="Stlc.html#3872" class="Function"
      >f</a
      ><a name="4011"
      > </a
      ><a name="4012" href="Stlc.html#3553" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="4013"
      > </a
      ><a name="4014" href="Stlc.html#3501" class="InductiveConstructor"
      >`</a
      ><a name="4015"
      > </a
      ><a name="4016" href="Stlc.html#3874" class="Function"
      >x</a
      ><a name="4017" class="Symbol"
      >)</a
      >

</pre>

## Values

<pre class="Agda">

<a name="4055" class="Keyword"
      >data</a
      ><a name="4059"
      > </a
      ><a name="4060" href="Stlc.html#4060" class="Datatype"
      >Value</a
      ><a name="4065"
      > </a
      ><a name="4066" class="Symbol"
      >:</a
      ><a name="4067"
      > </a
      ><a name="4068" href="Stlc.html#3482" class="Datatype"
      >Term</a
      ><a name="4072"
      > </a
      ><a name="4073" class="Symbol"
      >&#8594;</a
      ><a name="4074"
      > </a
      ><a name="4075" class="PrimitiveType"
      >Set</a
      ><a name="4078"
      > </a
      ><a name="4079" class="Keyword"
      >where</a
      ><a name="4084"
      >
  </a
      ><a name="4087" href="Stlc.html#4087" class="InductiveConstructor"
      >value-&#955;</a
      ><a name="4094"
      >     </a
      ><a name="4099" class="Symbol"
      >:</a
      ><a name="4100"
      > </a
      ><a name="4101" class="Symbol"
      >&#8704;</a
      ><a name="4102"
      > </a
      ><a name="4103" class="Symbol"
      >{</a
      ><a name="4104" href="Stlc.html#4104" class="Bound"
      >x</a
      ><a name="4105"
      > </a
      ><a name="4106" href="Stlc.html#4106" class="Bound"
      >A</a
      ><a name="4107"
      > </a
      ><a name="4108" href="Stlc.html#4108" class="Bound"
      >N</a
      ><a name="4109" class="Symbol"
      >}</a
      ><a name="4110"
      > </a
      ><a name="4111" class="Symbol"
      >&#8594;</a
      ><a name="4112"
      > </a
      ><a name="4113" href="Stlc.html#4060" class="Datatype"
      >Value</a
      ><a name="4118"
      > </a
      ><a name="4119" class="Symbol"
      >(</a
      ><a name="4120" href="Stlc.html#3517" class="InductiveConstructor Operator"
      >&#955;[</a
      ><a name="4122"
      > </a
      ><a name="4123" href="Stlc.html#4104" class="Bound"
      >x</a
      ><a name="4124"
      > </a
      ><a name="4125" href="Stlc.html#3517" class="InductiveConstructor Operator"
      >&#8758;</a
      ><a name="4126"
      > </a
      ><a name="4127" href="Stlc.html#4106" class="Bound"
      >A</a
      ><a name="4128"
      > </a
      ><a name="4129" href="Stlc.html#3517" class="InductiveConstructor Operator"
      >]</a
      ><a name="4130"
      > </a
      ><a name="4131" href="Stlc.html#4108" class="Bound"
      >N</a
      ><a name="4132" class="Symbol"
      >)</a
      ><a name="4133"
      >
  </a
      ><a name="4136" href="Stlc.html#4136" class="InductiveConstructor"
      >value-true</a
      ><a name="4146"
      >  </a
      ><a name="4148" class="Symbol"
      >:</a
      ><a name="4149"
      > </a
      ><a name="4150" href="Stlc.html#4060" class="Datatype"
      >Value</a
      ><a name="4155"
      > </a
      ><a name="4156" href="Stlc.html#3580" class="InductiveConstructor"
      >true</a
      ><a name="4160"
      >
  </a
      ><a name="4163" href="Stlc.html#4163" class="InductiveConstructor"
      >value-false</a
      ><a name="4174"
      > </a
      ><a name="4175" class="Symbol"
      >:</a
      ><a name="4176"
      > </a
      ><a name="4177" href="Stlc.html#4060" class="Datatype"
      >Value</a
      ><a name="4182"
      > </a
      ><a name="4183" href="Stlc.html#3594" class="InductiveConstructor"
      >false</a
      >

</pre>

## Substitution

<pre class="Agda">

<a name="4231" href="Stlc.html#4231" class="Function Operator"
      >_[_:=_]</a
      ><a name="4238"
      > </a
      ><a name="4239" class="Symbol"
      >:</a
      ><a name="4240"
      > </a
      ><a name="4241" href="Stlc.html#3482" class="Datatype"
      >Term</a
      ><a name="4245"
      > </a
      ><a name="4246" class="Symbol"
      >&#8594;</a
      ><a name="4247"
      > </a
      ><a name="4248" href="Maps.html#2171" class="Datatype"
      >Id</a
      ><a name="4250"
      > </a
      ><a name="4251" class="Symbol"
      >&#8594;</a
      ><a name="4252"
      > </a
      ><a name="4253" href="Stlc.html#3482" class="Datatype"
      >Term</a
      ><a name="4257"
      > </a
      ><a name="4258" class="Symbol"
      >&#8594;</a
      ><a name="4259"
      > </a
      ><a name="4260" href="Stlc.html#3482" class="Datatype"
      >Term</a
      ><a name="4264"
      >
</a
      ><a name="4265" class="Symbol"
      >(</a
      ><a name="4266" href="Stlc.html#3501" class="InductiveConstructor"
      >`</a
      ><a name="4267"
      > </a
      ><a name="4268" href="Stlc.html#4268" class="Bound"
      >x&#8242;</a
      ><a name="4270" class="Symbol"
      >)</a
      ><a name="4271"
      > </a
      ><a name="4272" href="Stlc.html#4231" class="Function Operator"
      >[</a
      ><a name="4273"
      > </a
      ><a name="4274" href="Stlc.html#4274" class="Bound"
      >x</a
      ><a name="4275"
      > </a
      ><a name="4276" href="Stlc.html#4231" class="Function Operator"
      >:=</a
      ><a name="4278"
      > </a
      ><a name="4279" href="Stlc.html#4279" class="Bound"
      >V</a
      ><a name="4280"
      > </a
      ><a name="4281" href="Stlc.html#4231" class="Function Operator"
      >]</a
      ><a name="4282"
      > </a
      ><a name="4283" class="Keyword"
      >with</a
      ><a name="4287"
      > </a
      ><a name="4288" href="Stlc.html#4274" class="Bound"
      >x</a
      ><a name="4289"
      > </a
      ><a name="4290" href="Maps.html#2509" class="Function Operator"
      >&#8799;</a
      ><a name="4291"
      > </a
      ><a name="4292" href="Stlc.html#4268" class="Bound"
      >x&#8242;</a
      ><a name="4294"
      >
</a
      ><a name="4295" class="Symbol"
      >...</a
      ><a name="4298"
      > </a
      ><a name="4299" class="Symbol"
      >|</a
      ><a name="4300"
      > </a
      ><a name="4301" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#520" class="InductiveConstructor"
      >yes</a
      ><a name="4304"
      > </a
      ><a name="4305" class="Symbol"
      >_</a
      ><a name="4306"
      > </a
      ><a name="4307" class="Symbol"
      >=</a
      ><a name="4308"
      > </a
      ><a name="4309" href="Stlc.html#4279" class="Bound"
      >V</a
      ><a name="4310"
      >
</a
      ><a name="4311" class="Symbol"
      >...</a
      ><a name="4314"
      > </a
      ><a name="4315" class="Symbol"
      >|</a
      ><a name="4316"
      > </a
      ><a name="4317" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#547" class="InductiveConstructor"
      >no</a
      ><a name="4319"
      >  </a
      ><a name="4321" class="Symbol"
      >_</a
      ><a name="4322"
      > </a
      ><a name="4323" class="Symbol"
      >=</a
      ><a name="4324"
      > </a
      ><a name="4325" href="Stlc.html#3501" class="InductiveConstructor"
      >`</a
      ><a name="4326"
      > </a
      ><a name="4327" href="Stlc.html#4268" class="Bound"
      >x&#8242;</a
      ><a name="4329"
      >
</a
      ><a name="4330" class="Symbol"
      >(</a
      ><a name="4331" href="Stlc.html#3517" class="InductiveConstructor Operator"
      >&#955;[</a
      ><a name="4333"
      > </a
      ><a name="4334" href="Stlc.html#4334" class="Bound"
      >x&#8242;</a
      ><a name="4336"
      > </a
      ><a name="4337" href="Stlc.html#3517" class="InductiveConstructor Operator"
      >&#8758;</a
      ><a name="4338"
      > </a
      ><a name="4339" href="Stlc.html#4339" class="Bound"
      >A&#8242;</a
      ><a name="4341"
      > </a
      ><a name="4342" href="Stlc.html#3517" class="InductiveConstructor Operator"
      >]</a
      ><a name="4343"
      > </a
      ><a name="4344" href="Stlc.html#4344" class="Bound"
      >N&#8242;</a
      ><a name="4346" class="Symbol"
      >)</a
      ><a name="4347"
      > </a
      ><a name="4348" href="Stlc.html#4231" class="Function Operator"
      >[</a
      ><a name="4349"
      > </a
      ><a name="4350" href="Stlc.html#4350" class="Bound"
      >x</a
      ><a name="4351"
      > </a
      ><a name="4352" href="Stlc.html#4231" class="Function Operator"
      >:=</a
      ><a name="4354"
      > </a
      ><a name="4355" href="Stlc.html#4355" class="Bound"
      >V</a
      ><a name="4356"
      > </a
      ><a name="4357" href="Stlc.html#4231" class="Function Operator"
      >]</a
      ><a name="4358"
      > </a
      ><a name="4359" class="Keyword"
      >with</a
      ><a name="4363"
      > </a
      ><a name="4364" href="Stlc.html#4350" class="Bound"
      >x</a
      ><a name="4365"
      > </a
      ><a name="4366" href="Maps.html#2509" class="Function Operator"
      >&#8799;</a
      ><a name="4367"
      > </a
      ><a name="4368" href="Stlc.html#4334" class="Bound"
      >x&#8242;</a
      ><a name="4370"
      >
</a
      ><a name="4371" class="Symbol"
      >...</a
      ><a name="4374"
      > </a
      ><a name="4375" class="Symbol"
      >|</a
      ><a name="4376"
      > </a
      ><a name="4377" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#520" class="InductiveConstructor"
      >yes</a
      ><a name="4380"
      > </a
      ><a name="4381" class="Symbol"
      >_</a
      ><a name="4382"
      > </a
      ><a name="4383" class="Symbol"
      >=</a
      ><a name="4384"
      > </a
      ><a name="4385" href="Stlc.html#3517" class="InductiveConstructor Operator"
      >&#955;[</a
      ><a name="4387"
      > </a
      ><a name="4388" href="Stlc.html#4334" class="Bound"
      >x&#8242;</a
      ><a name="4390"
      > </a
      ><a name="4391" href="Stlc.html#3517" class="InductiveConstructor Operator"
      >&#8758;</a
      ><a name="4392"
      > </a
      ><a name="4393" href="Stlc.html#4339" class="Bound"
      >A&#8242;</a
      ><a name="4395"
      > </a
      ><a name="4396" href="Stlc.html#3517" class="InductiveConstructor Operator"
      >]</a
      ><a name="4397"
      > </a
      ><a name="4398" href="Stlc.html#4344" class="Bound"
      >N&#8242;</a
      ><a name="4400"
      >
</a
      ><a name="4401" class="Symbol"
      >...</a
      ><a name="4404"
      > </a
      ><a name="4405" class="Symbol"
      >|</a
      ><a name="4406"
      > </a
      ><a name="4407" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#547" class="InductiveConstructor"
      >no</a
      ><a name="4409"
      >  </a
      ><a name="4411" class="Symbol"
      >_</a
      ><a name="4412"
      > </a
      ><a name="4413" class="Symbol"
      >=</a
      ><a name="4414"
      > </a
      ><a name="4415" href="Stlc.html#3517" class="InductiveConstructor Operator"
      >&#955;[</a
      ><a name="4417"
      > </a
      ><a name="4418" href="Stlc.html#4334" class="Bound"
      >x&#8242;</a
      ><a name="4420"
      > </a
      ><a name="4421" href="Stlc.html#3517" class="InductiveConstructor Operator"
      >&#8758;</a
      ><a name="4422"
      > </a
      ><a name="4423" href="Stlc.html#4339" class="Bound"
      >A&#8242;</a
      ><a name="4425"
      > </a
      ><a name="4426" href="Stlc.html#3517" class="InductiveConstructor Operator"
      >]</a
      ><a name="4427"
      > </a
      ><a name="4428" class="Symbol"
      >(</a
      ><a name="4429" href="Stlc.html#4344" class="Bound"
      >N&#8242;</a
      ><a name="4431"
      > </a
      ><a name="4432" href="Stlc.html#4231" class="Function Operator"
      >[</a
      ><a name="4433"
      > </a
      ><a name="4434" href="Stlc.html#4350" class="Bound"
      >x</a
      ><a name="4435"
      > </a
      ><a name="4436" href="Stlc.html#4231" class="Function Operator"
      >:=</a
      ><a name="4438"
      > </a
      ><a name="4439" href="Stlc.html#4355" class="Bound"
      >V</a
      ><a name="4440"
      > </a
      ><a name="4441" href="Stlc.html#4231" class="Function Operator"
      >]</a
      ><a name="4442" class="Symbol"
      >)</a
      ><a name="4443"
      >
</a
      ><a name="4444" class="Symbol"
      >(</a
      ><a name="4445" href="Stlc.html#4445" class="Bound"
      >L&#8242;</a
      ><a name="4447"
      > </a
      ><a name="4448" href="Stlc.html#3553" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="4449"
      > </a
      ><a name="4450" href="Stlc.html#4450" class="Bound"
      >M&#8242;</a
      ><a name="4452" class="Symbol"
      >)</a
      ><a name="4453"
      > </a
      ><a name="4454" href="Stlc.html#4231" class="Function Operator"
      >[</a
      ><a name="4455"
      > </a
      ><a name="4456" href="Stlc.html#4456" class="Bound"
      >x</a
      ><a name="4457"
      > </a
      ><a name="4458" href="Stlc.html#4231" class="Function Operator"
      >:=</a
      ><a name="4460"
      > </a
      ><a name="4461" href="Stlc.html#4461" class="Bound"
      >V</a
      ><a name="4462"
      > </a
      ><a name="4463" href="Stlc.html#4231" class="Function Operator"
      >]</a
      ><a name="4464"
      > </a
      ><a name="4465" class="Symbol"
      >=</a
      ><a name="4466"
      >  </a
      ><a name="4468" class="Symbol"
      >(</a
      ><a name="4469" href="Stlc.html#4445" class="Bound"
      >L&#8242;</a
      ><a name="4471"
      > </a
      ><a name="4472" href="Stlc.html#4231" class="Function Operator"
      >[</a
      ><a name="4473"
      > </a
      ><a name="4474" href="Stlc.html#4456" class="Bound"
      >x</a
      ><a name="4475"
      > </a
      ><a name="4476" href="Stlc.html#4231" class="Function Operator"
      >:=</a
      ><a name="4478"
      > </a
      ><a name="4479" href="Stlc.html#4461" class="Bound"
      >V</a
      ><a name="4480"
      > </a
      ><a name="4481" href="Stlc.html#4231" class="Function Operator"
      >]</a
      ><a name="4482" class="Symbol"
      >)</a
      ><a name="4483"
      > </a
      ><a name="4484" href="Stlc.html#3553" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="4485"
      > </a
      ><a name="4486" class="Symbol"
      >(</a
      ><a name="4487" href="Stlc.html#4450" class="Bound"
      >M&#8242;</a
      ><a name="4489"
      > </a
      ><a name="4490" href="Stlc.html#4231" class="Function Operator"
      >[</a
      ><a name="4491"
      > </a
      ><a name="4492" href="Stlc.html#4456" class="Bound"
      >x</a
      ><a name="4493"
      > </a
      ><a name="4494" href="Stlc.html#4231" class="Function Operator"
      >:=</a
      ><a name="4496"
      > </a
      ><a name="4497" href="Stlc.html#4461" class="Bound"
      >V</a
      ><a name="4498"
      > </a
      ><a name="4499" href="Stlc.html#4231" class="Function Operator"
      >]</a
      ><a name="4500" class="Symbol"
      >)</a
      ><a name="4501"
      >
</a
      ><a name="4502" class="Symbol"
      >(</a
      ><a name="4503" href="Stlc.html#3580" class="InductiveConstructor"
      >true</a
      ><a name="4507" class="Symbol"
      >)</a
      ><a name="4508"
      > </a
      ><a name="4509" href="Stlc.html#4231" class="Function Operator"
      >[</a
      ><a name="4510"
      > </a
      ><a name="4511" href="Stlc.html#4511" class="Bound"
      >x</a
      ><a name="4512"
      > </a
      ><a name="4513" href="Stlc.html#4231" class="Function Operator"
      >:=</a
      ><a name="4515"
      > </a
      ><a name="4516" href="Stlc.html#4516" class="Bound"
      >V</a
      ><a name="4517"
      > </a
      ><a name="4518" href="Stlc.html#4231" class="Function Operator"
      >]</a
      ><a name="4519"
      > </a
      ><a name="4520" class="Symbol"
      >=</a
      ><a name="4521"
      > </a
      ><a name="4522" href="Stlc.html#3580" class="InductiveConstructor"
      >true</a
      ><a name="4526"
      >
</a
      ><a name="4527" class="Symbol"
      >(</a
      ><a name="4528" href="Stlc.html#3594" class="InductiveConstructor"
      >false</a
      ><a name="4533" class="Symbol"
      >)</a
      ><a name="4534"
      > </a
      ><a name="4535" href="Stlc.html#4231" class="Function Operator"
      >[</a
      ><a name="4536"
      > </a
      ><a name="4537" href="Stlc.html#4537" class="Bound"
      >x</a
      ><a name="4538"
      > </a
      ><a name="4539" href="Stlc.html#4231" class="Function Operator"
      >:=</a
      ><a name="4541"
      > </a
      ><a name="4542" href="Stlc.html#4542" class="Bound"
      >V</a
      ><a name="4543"
      > </a
      ><a name="4544" href="Stlc.html#4231" class="Function Operator"
      >]</a
      ><a name="4545"
      > </a
      ><a name="4546" class="Symbol"
      >=</a
      ><a name="4547"
      > </a
      ><a name="4548" href="Stlc.html#3594" class="InductiveConstructor"
      >false</a
      ><a name="4553"
      >
</a
      ><a name="4554" class="Symbol"
      >(</a
      ><a name="4555" href="Stlc.html#3609" class="InductiveConstructor Operator"
      >if</a
      ><a name="4557"
      > </a
      ><a name="4558" href="Stlc.html#4558" class="Bound"
      >L&#8242;</a
      ><a name="4560"
      > </a
      ><a name="4561" href="Stlc.html#3609" class="InductiveConstructor Operator"
      >then</a
      ><a name="4565"
      > </a
      ><a name="4566" href="Stlc.html#4566" class="Bound"
      >M&#8242;</a
      ><a name="4568"
      > </a
      ><a name="4569" href="Stlc.html#3609" class="InductiveConstructor Operator"
      >else</a
      ><a name="4573"
      > </a
      ><a name="4574" href="Stlc.html#4574" class="Bound"
      >N&#8242;</a
      ><a name="4576" class="Symbol"
      >)</a
      ><a name="4577"
      > </a
      ><a name="4578" href="Stlc.html#4231" class="Function Operator"
      >[</a
      ><a name="4579"
      > </a
      ><a name="4580" href="Stlc.html#4580" class="Bound"
      >x</a
      ><a name="4581"
      > </a
      ><a name="4582" href="Stlc.html#4231" class="Function Operator"
      >:=</a
      ><a name="4584"
      > </a
      ><a name="4585" href="Stlc.html#4585" class="Bound"
      >V</a
      ><a name="4586"
      > </a
      ><a name="4587" href="Stlc.html#4231" class="Function Operator"
      >]</a
      ><a name="4588"
      > </a
      ><a name="4589" class="Symbol"
      >=</a
      ><a name="4590"
      > </a
      ><a name="4591" href="Stlc.html#3609" class="InductiveConstructor Operator"
      >if</a
      ><a name="4593"
      > </a
      ><a name="4594" class="Symbol"
      >(</a
      ><a name="4595" href="Stlc.html#4558" class="Bound"
      >L&#8242;</a
      ><a name="4597"
      > </a
      ><a name="4598" href="Stlc.html#4231" class="Function Operator"
      >[</a
      ><a name="4599"
      > </a
      ><a name="4600" href="Stlc.html#4580" class="Bound"
      >x</a
      ><a name="4601"
      > </a
      ><a name="4602" href="Stlc.html#4231" class="Function Operator"
      >:=</a
      ><a name="4604"
      > </a
      ><a name="4605" href="Stlc.html#4585" class="Bound"
      >V</a
      ><a name="4606"
      > </a
      ><a name="4607" href="Stlc.html#4231" class="Function Operator"
      >]</a
      ><a name="4608" class="Symbol"
      >)</a
      ><a name="4609"
      > </a
      ><a name="4610" href="Stlc.html#3609" class="InductiveConstructor Operator"
      >then</a
      ><a name="4614"
      > </a
      ><a name="4615" class="Symbol"
      >(</a
      ><a name="4616" href="Stlc.html#4566" class="Bound"
      >M&#8242;</a
      ><a name="4618"
      > </a
      ><a name="4619" href="Stlc.html#4231" class="Function Operator"
      >[</a
      ><a name="4620"
      > </a
      ><a name="4621" href="Stlc.html#4580" class="Bound"
      >x</a
      ><a name="4622"
      > </a
      ><a name="4623" href="Stlc.html#4231" class="Function Operator"
      >:=</a
      ><a name="4625"
      > </a
      ><a name="4626" href="Stlc.html#4585" class="Bound"
      >V</a
      ><a name="4627"
      > </a
      ><a name="4628" href="Stlc.html#4231" class="Function Operator"
      >]</a
      ><a name="4629" class="Symbol"
      >)</a
      ><a name="4630"
      > </a
      ><a name="4631" href="Stlc.html#3609" class="InductiveConstructor Operator"
      >else</a
      ><a name="4635"
      > </a
      ><a name="4636" class="Symbol"
      >(</a
      ><a name="4637" href="Stlc.html#4574" class="Bound"
      >N&#8242;</a
      ><a name="4639"
      > </a
      ><a name="4640" href="Stlc.html#4231" class="Function Operator"
      >[</a
      ><a name="4641"
      > </a
      ><a name="4642" href="Stlc.html#4580" class="Bound"
      >x</a
      ><a name="4643"
      > </a
      ><a name="4644" href="Stlc.html#4231" class="Function Operator"
      >:=</a
      ><a name="4646"
      > </a
      ><a name="4647" href="Stlc.html#4585" class="Bound"
      >V</a
      ><a name="4648"
      > </a
      ><a name="4649" href="Stlc.html#4231" class="Function Operator"
      >]</a
      ><a name="4650" class="Symbol"
      >)</a
      >

</pre>

## Reduction rules

<pre class="Agda">

<a name="4697" class="Keyword"
      >infix</a
      ><a name="4702"
      > </a
      ><a name="4703" class="Number"
      >10</a
      ><a name="4705"
      > </a
      ><a name="4706" href="Stlc.html#4717" class="Datatype Operator"
      >_&#10233;_</a
      ><a name="4709"
      > 

</a
      ><a name="4712" class="Keyword"
      >data</a
      ><a name="4716"
      > </a
      ><a name="4717" href="Stlc.html#4717" class="Datatype Operator"
      >_&#10233;_</a
      ><a name="4720"
      > </a
      ><a name="4721" class="Symbol"
      >:</a
      ><a name="4722"
      > </a
      ><a name="4723" href="Stlc.html#3482" class="Datatype"
      >Term</a
      ><a name="4727"
      > </a
      ><a name="4728" class="Symbol"
      >&#8594;</a
      ><a name="4729"
      > </a
      ><a name="4730" href="Stlc.html#3482" class="Datatype"
      >Term</a
      ><a name="4734"
      > </a
      ><a name="4735" class="Symbol"
      >&#8594;</a
      ><a name="4736"
      > </a
      ><a name="4737" class="PrimitiveType"
      >Set</a
      ><a name="4740"
      > </a
      ><a name="4741" class="Keyword"
      >where</a
      ><a name="4746"
      >
  </a
      ><a name="4749" href="Stlc.html#4749" class="InductiveConstructor"
      >&#946;&#955;&#183;</a
      ><a name="4752"
      > </a
      ><a name="4753" class="Symbol"
      >:</a
      ><a name="4754"
      > </a
      ><a name="4755" class="Symbol"
      >&#8704;</a
      ><a name="4756"
      > </a
      ><a name="4757" class="Symbol"
      >{</a
      ><a name="4758" href="Stlc.html#4758" class="Bound"
      >x</a
      ><a name="4759"
      > </a
      ><a name="4760" href="Stlc.html#4760" class="Bound"
      >A</a
      ><a name="4761"
      > </a
      ><a name="4762" href="Stlc.html#4762" class="Bound"
      >N</a
      ><a name="4763"
      > </a
      ><a name="4764" href="Stlc.html#4764" class="Bound"
      >V</a
      ><a name="4765" class="Symbol"
      >}</a
      ><a name="4766"
      > </a
      ><a name="4767" class="Symbol"
      >&#8594;</a
      ><a name="4768"
      > </a
      ><a name="4769" href="Stlc.html#4060" class="Datatype"
      >Value</a
      ><a name="4774"
      > </a
      ><a name="4775" href="Stlc.html#4764" class="Bound"
      >V</a
      ><a name="4776"
      > </a
      ><a name="4777" class="Symbol"
      >&#8594;</a
      ><a name="4778"
      >
    </a
      ><a name="4783" class="Symbol"
      >(</a
      ><a name="4784" href="Stlc.html#3517" class="InductiveConstructor Operator"
      >&#955;[</a
      ><a name="4786"
      > </a
      ><a name="4787" href="Stlc.html#4758" class="Bound"
      >x</a
      ><a name="4788"
      > </a
      ><a name="4789" href="Stlc.html#3517" class="InductiveConstructor Operator"
      >&#8758;</a
      ><a name="4790"
      > </a
      ><a name="4791" href="Stlc.html#4760" class="Bound"
      >A</a
      ><a name="4792"
      > </a
      ><a name="4793" href="Stlc.html#3517" class="InductiveConstructor Operator"
      >]</a
      ><a name="4794"
      > </a
      ><a name="4795" href="Stlc.html#4762" class="Bound"
      >N</a
      ><a name="4796" class="Symbol"
      >)</a
      ><a name="4797"
      > </a
      ><a name="4798" href="Stlc.html#3553" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="4799"
      > </a
      ><a name="4800" href="Stlc.html#4764" class="Bound"
      >V</a
      ><a name="4801"
      > </a
      ><a name="4802" href="Stlc.html#4717" class="Datatype Operator"
      >&#10233;</a
      ><a name="4803"
      > </a
      ><a name="4804" href="Stlc.html#4762" class="Bound"
      >N</a
      ><a name="4805"
      > </a
      ><a name="4806" href="Stlc.html#4231" class="Function Operator"
      >[</a
      ><a name="4807"
      > </a
      ><a name="4808" href="Stlc.html#4758" class="Bound"
      >x</a
      ><a name="4809"
      > </a
      ><a name="4810" href="Stlc.html#4231" class="Function Operator"
      >:=</a
      ><a name="4812"
      > </a
      ><a name="4813" href="Stlc.html#4764" class="Bound"
      >V</a
      ><a name="4814"
      > </a
      ><a name="4815" href="Stlc.html#4231" class="Function Operator"
      >]</a
      ><a name="4816"
      >
  </a
      ><a name="4819" href="Stlc.html#4819" class="InductiveConstructor"
      >&#958;&#183;&#8321;</a
      ><a name="4822"
      > </a
      ><a name="4823" class="Symbol"
      >:</a
      ><a name="4824"
      > </a
      ><a name="4825" class="Symbol"
      >&#8704;</a
      ><a name="4826"
      > </a
      ><a name="4827" class="Symbol"
      >{</a
      ><a name="4828" href="Stlc.html#4828" class="Bound"
      >L</a
      ><a name="4829"
      > </a
      ><a name="4830" href="Stlc.html#4830" class="Bound"
      >L&#8242;</a
      ><a name="4832"
      > </a
      ><a name="4833" href="Stlc.html#4833" class="Bound"
      >M</a
      ><a name="4834" class="Symbol"
      >}</a
      ><a name="4835"
      > </a
      ><a name="4836" class="Symbol"
      >&#8594;</a
      ><a name="4837"
      >
    </a
      ><a name="4842" href="Stlc.html#4828" class="Bound"
      >L</a
      ><a name="4843"
      > </a
      ><a name="4844" href="Stlc.html#4717" class="Datatype Operator"
      >&#10233;</a
      ><a name="4845"
      > </a
      ><a name="4846" href="Stlc.html#4830" class="Bound"
      >L&#8242;</a
      ><a name="4848"
      > </a
      ><a name="4849" class="Symbol"
      >&#8594;</a
      ><a name="4850"
      >
    </a
      ><a name="4855" href="Stlc.html#4828" class="Bound"
      >L</a
      ><a name="4856"
      > </a
      ><a name="4857" href="Stlc.html#3553" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="4858"
      > </a
      ><a name="4859" href="Stlc.html#4833" class="Bound"
      >M</a
      ><a name="4860"
      > </a
      ><a name="4861" href="Stlc.html#4717" class="Datatype Operator"
      >&#10233;</a
      ><a name="4862"
      > </a
      ><a name="4863" href="Stlc.html#4830" class="Bound"
      >L&#8242;</a
      ><a name="4865"
      > </a
      ><a name="4866" href="Stlc.html#3553" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="4867"
      > </a
      ><a name="4868" href="Stlc.html#4833" class="Bound"
      >M</a
      ><a name="4869"
      >
  </a
      ><a name="4872" href="Stlc.html#4872" class="InductiveConstructor"
      >&#958;&#183;&#8322;</a
      ><a name="4875"
      > </a
      ><a name="4876" class="Symbol"
      >:</a
      ><a name="4877"
      > </a
      ><a name="4878" class="Symbol"
      >&#8704;</a
      ><a name="4879"
      > </a
      ><a name="4880" class="Symbol"
      >{</a
      ><a name="4881" href="Stlc.html#4881" class="Bound"
      >V</a
      ><a name="4882"
      > </a
      ><a name="4883" href="Stlc.html#4883" class="Bound"
      >M</a
      ><a name="4884"
      > </a
      ><a name="4885" href="Stlc.html#4885" class="Bound"
      >M&#8242;</a
      ><a name="4887" class="Symbol"
      >}</a
      ><a name="4888"
      > </a
      ><a name="4889" class="Symbol"
      >&#8594;</a
      ><a name="4890"
      >
    </a
      ><a name="4895" href="Stlc.html#4060" class="Datatype"
      >Value</a
      ><a name="4900"
      > </a
      ><a name="4901" href="Stlc.html#4881" class="Bound"
      >V</a
      ><a name="4902"
      > </a
      ><a name="4903" class="Symbol"
      >&#8594;</a
      ><a name="4904"
      >
    </a
      ><a name="4909" href="Stlc.html#4883" class="Bound"
      >M</a
      ><a name="4910"
      > </a
      ><a name="4911" href="Stlc.html#4717" class="Datatype Operator"
      >&#10233;</a
      ><a name="4912"
      > </a
      ><a name="4913" href="Stlc.html#4885" class="Bound"
      >M&#8242;</a
      ><a name="4915"
      > </a
      ><a name="4916" class="Symbol"
      >&#8594;</a
      ><a name="4917"
      >
    </a
      ><a name="4922" href="Stlc.html#4881" class="Bound"
      >V</a
      ><a name="4923"
      > </a
      ><a name="4924" href="Stlc.html#3553" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="4925"
      > </a
      ><a name="4926" href="Stlc.html#4883" class="Bound"
      >M</a
      ><a name="4927"
      > </a
      ><a name="4928" href="Stlc.html#4717" class="Datatype Operator"
      >&#10233;</a
      ><a name="4929"
      > </a
      ><a name="4930" href="Stlc.html#4881" class="Bound"
      >V</a
      ><a name="4931"
      > </a
      ><a name="4932" href="Stlc.html#3553" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="4933"
      > </a
      ><a name="4934" href="Stlc.html#4885" class="Bound"
      >M&#8242;</a
      ><a name="4936"
      >
  </a
      ><a name="4939" href="Stlc.html#4939" class="InductiveConstructor"
      >&#946;if-true</a
      ><a name="4947"
      > </a
      ><a name="4948" class="Symbol"
      >:</a
      ><a name="4949"
      > </a
      ><a name="4950" class="Symbol"
      >&#8704;</a
      ><a name="4951"
      > </a
      ><a name="4952" class="Symbol"
      >{</a
      ><a name="4953" href="Stlc.html#4953" class="Bound"
      >M</a
      ><a name="4954"
      > </a
      ><a name="4955" href="Stlc.html#4955" class="Bound"
      >N</a
      ><a name="4956" class="Symbol"
      >}</a
      ><a name="4957"
      > </a
      ><a name="4958" class="Symbol"
      >&#8594;</a
      ><a name="4959"
      >
    </a
      ><a name="4964" href="Stlc.html#3609" class="InductiveConstructor Operator"
      >if</a
      ><a name="4966"
      > </a
      ><a name="4967" href="Stlc.html#3580" class="InductiveConstructor"
      >true</a
      ><a name="4971"
      > </a
      ><a name="4972" href="Stlc.html#3609" class="InductiveConstructor Operator"
      >then</a
      ><a name="4976"
      > </a
      ><a name="4977" href="Stlc.html#4953" class="Bound"
      >M</a
      ><a name="4978"
      > </a
      ><a name="4979" href="Stlc.html#3609" class="InductiveConstructor Operator"
      >else</a
      ><a name="4983"
      > </a
      ><a name="4984" href="Stlc.html#4955" class="Bound"
      >N</a
      ><a name="4985"
      > </a
      ><a name="4986" href="Stlc.html#4717" class="Datatype Operator"
      >&#10233;</a
      ><a name="4987"
      > </a
      ><a name="4988" href="Stlc.html#4953" class="Bound"
      >M</a
      ><a name="4989"
      >
  </a
      ><a name="4992" href="Stlc.html#4992" class="InductiveConstructor"
      >&#946;if-false</a
      ><a name="5001"
      > </a
      ><a name="5002" class="Symbol"
      >:</a
      ><a name="5003"
      > </a
      ><a name="5004" class="Symbol"
      >&#8704;</a
      ><a name="5005"
      > </a
      ><a name="5006" class="Symbol"
      >{</a
      ><a name="5007" href="Stlc.html#5007" class="Bound"
      >M</a
      ><a name="5008"
      > </a
      ><a name="5009" href="Stlc.html#5009" class="Bound"
      >N</a
      ><a name="5010" class="Symbol"
      >}</a
      ><a name="5011"
      > </a
      ><a name="5012" class="Symbol"
      >&#8594;</a
      ><a name="5013"
      >
    </a
      ><a name="5018" href="Stlc.html#3609" class="InductiveConstructor Operator"
      >if</a
      ><a name="5020"
      > </a
      ><a name="5021" href="Stlc.html#3594" class="InductiveConstructor"
      >false</a
      ><a name="5026"
      > </a
      ><a name="5027" href="Stlc.html#3609" class="InductiveConstructor Operator"
      >then</a
      ><a name="5031"
      > </a
      ><a name="5032" href="Stlc.html#5007" class="Bound"
      >M</a
      ><a name="5033"
      > </a
      ><a name="5034" href="Stlc.html#3609" class="InductiveConstructor Operator"
      >else</a
      ><a name="5038"
      > </a
      ><a name="5039" href="Stlc.html#5009" class="Bound"
      >N</a
      ><a name="5040"
      > </a
      ><a name="5041" href="Stlc.html#4717" class="Datatype Operator"
      >&#10233;</a
      ><a name="5042"
      > </a
      ><a name="5043" href="Stlc.html#5009" class="Bound"
      >N</a
      ><a name="5044"
      >
  </a
      ><a name="5047" href="Stlc.html#5047" class="InductiveConstructor"
      >&#958;if</a
      ><a name="5050"
      > </a
      ><a name="5051" class="Symbol"
      >:</a
      ><a name="5052"
      > </a
      ><a name="5053" class="Symbol"
      >&#8704;</a
      ><a name="5054"
      > </a
      ><a name="5055" class="Symbol"
      >{</a
      ><a name="5056" href="Stlc.html#5056" class="Bound"
      >L</a
      ><a name="5057"
      > </a
      ><a name="5058" href="Stlc.html#5058" class="Bound"
      >L&#8242;</a
      ><a name="5060"
      > </a
      ><a name="5061" href="Stlc.html#5061" class="Bound"
      >M</a
      ><a name="5062"
      > </a
      ><a name="5063" href="Stlc.html#5063" class="Bound"
      >N</a
      ><a name="5064" class="Symbol"
      >}</a
      ><a name="5065"
      > </a
      ><a name="5066" class="Symbol"
      >&#8594;</a
      ><a name="5067"
      >
    </a
      ><a name="5072" href="Stlc.html#5056" class="Bound"
      >L</a
      ><a name="5073"
      > </a
      ><a name="5074" href="Stlc.html#4717" class="Datatype Operator"
      >&#10233;</a
      ><a name="5075"
      > </a
      ><a name="5076" href="Stlc.html#5058" class="Bound"
      >L&#8242;</a
      ><a name="5078"
      > </a
      ><a name="5079" class="Symbol"
      >&#8594;</a
      ><a name="5080"
      >    
    </a
      ><a name="5089" href="Stlc.html#3609" class="InductiveConstructor Operator"
      >if</a
      ><a name="5091"
      > </a
      ><a name="5092" href="Stlc.html#5056" class="Bound"
      >L</a
      ><a name="5093"
      > </a
      ><a name="5094" href="Stlc.html#3609" class="InductiveConstructor Operator"
      >then</a
      ><a name="5098"
      > </a
      ><a name="5099" href="Stlc.html#5061" class="Bound"
      >M</a
      ><a name="5100"
      > </a
      ><a name="5101" href="Stlc.html#3609" class="InductiveConstructor Operator"
      >else</a
      ><a name="5105"
      > </a
      ><a name="5106" href="Stlc.html#5063" class="Bound"
      >N</a
      ><a name="5107"
      > </a
      ><a name="5108" href="Stlc.html#4717" class="Datatype Operator"
      >&#10233;</a
      ><a name="5109"
      > </a
      ><a name="5110" href="Stlc.html#3609" class="InductiveConstructor Operator"
      >if</a
      ><a name="5112"
      > </a
      ><a name="5113" href="Stlc.html#5058" class="Bound"
      >L&#8242;</a
      ><a name="5115"
      > </a
      ><a name="5116" href="Stlc.html#3609" class="InductiveConstructor Operator"
      >then</a
      ><a name="5120"
      > </a
      ><a name="5121" href="Stlc.html#5061" class="Bound"
      >M</a
      ><a name="5122"
      > </a
      ><a name="5123" href="Stlc.html#3609" class="InductiveConstructor Operator"
      >else</a
      ><a name="5127"
      > </a
      ><a name="5128" href="Stlc.html#5063" class="Bound"
      >N</a
      >

</pre>

## Reflexive and transitive closure


<pre class="Agda">

<a name="5193" class="Keyword"
      >infix</a
      ><a name="5198"
      > </a
      ><a name="5199" class="Number"
      >10</a
      ><a name="5201"
      > </a
      ><a name="5202" href="Stlc.html#5242" class="Datatype Operator"
      >_&#10233;*_</a
      ><a name="5206"
      > 
</a
      ><a name="5208" class="Keyword"
      >infixr</a
      ><a name="5214"
      > </a
      ><a name="5215" class="Number"
      >2</a
      ><a name="5216"
      > </a
      ><a name="5217" href="Stlc.html#5295" class="InductiveConstructor Operator"
      >_&#10233;&#10216;_&#10217;_</a
      ><a name="5223"
      >
</a
      ><a name="5224" class="Keyword"
      >infix</a
      ><a name="5229"
      >  </a
      ><a name="5231" class="Number"
      >3</a
      ><a name="5232"
      > </a
      ><a name="5233" href="Stlc.html#5275" class="InductiveConstructor Operator"
      >_&#8718;</a
      ><a name="5235"
      >

</a
      ><a name="5237" class="Keyword"
      >data</a
      ><a name="5241"
      > </a
      ><a name="5242" href="Stlc.html#5242" class="Datatype Operator"
      >_&#10233;*_</a
      ><a name="5246"
      > </a
      ><a name="5247" class="Symbol"
      >:</a
      ><a name="5248"
      > </a
      ><a name="5249" href="Stlc.html#3482" class="Datatype"
      >Term</a
      ><a name="5253"
      > </a
      ><a name="5254" class="Symbol"
      >&#8594;</a
      ><a name="5255"
      > </a
      ><a name="5256" href="Stlc.html#3482" class="Datatype"
      >Term</a
      ><a name="5260"
      > </a
      ><a name="5261" class="Symbol"
      >&#8594;</a
      ><a name="5262"
      > </a
      ><a name="5263" class="PrimitiveType"
      >Set</a
      ><a name="5266"
      > </a
      ><a name="5267" class="Keyword"
      >where</a
      ><a name="5272"
      >
  </a
      ><a name="5275" href="Stlc.html#5275" class="InductiveConstructor Operator"
      >_&#8718;</a
      ><a name="5277"
      > </a
      ><a name="5278" class="Symbol"
      >:</a
      ><a name="5279"
      > </a
      ><a name="5280" class="Symbol"
      >&#8704;</a
      ><a name="5281"
      > </a
      ><a name="5282" href="Stlc.html#5282" class="Bound"
      >M</a
      ><a name="5283"
      > </a
      ><a name="5284" class="Symbol"
      >&#8594;</a
      ><a name="5285"
      > </a
      ><a name="5286" href="Stlc.html#5282" class="Bound"
      >M</a
      ><a name="5287"
      > </a
      ><a name="5288" href="Stlc.html#5242" class="Datatype Operator"
      >&#10233;*</a
      ><a name="5290"
      > </a
      ><a name="5291" href="Stlc.html#5282" class="Bound"
      >M</a
      ><a name="5292"
      >
  </a
      ><a name="5295" href="Stlc.html#5295" class="InductiveConstructor Operator"
      >_&#10233;&#10216;_&#10217;_</a
      ><a name="5301"
      > </a
      ><a name="5302" class="Symbol"
      >:</a
      ><a name="5303"
      > </a
      ><a name="5304" class="Symbol"
      >&#8704;</a
      ><a name="5305"
      > </a
      ><a name="5306" href="Stlc.html#5306" class="Bound"
      >L</a
      ><a name="5307"
      > </a
      ><a name="5308" class="Symbol"
      >{</a
      ><a name="5309" href="Stlc.html#5309" class="Bound"
      >M</a
      ><a name="5310"
      > </a
      ><a name="5311" href="Stlc.html#5311" class="Bound"
      >N</a
      ><a name="5312" class="Symbol"
      >}</a
      ><a name="5313"
      > </a
      ><a name="5314" class="Symbol"
      >&#8594;</a
      ><a name="5315"
      > </a
      ><a name="5316" href="Stlc.html#5306" class="Bound"
      >L</a
      ><a name="5317"
      > </a
      ><a name="5318" href="Stlc.html#4717" class="Datatype Operator"
      >&#10233;</a
      ><a name="5319"
      > </a
      ><a name="5320" href="Stlc.html#5309" class="Bound"
      >M</a
      ><a name="5321"
      > </a
      ><a name="5322" class="Symbol"
      >&#8594;</a
      ><a name="5323"
      > </a
      ><a name="5324" href="Stlc.html#5309" class="Bound"
      >M</a
      ><a name="5325"
      > </a
      ><a name="5326" href="Stlc.html#5242" class="Datatype Operator"
      >&#10233;*</a
      ><a name="5328"
      > </a
      ><a name="5329" href="Stlc.html#5311" class="Bound"
      >N</a
      ><a name="5330"
      > </a
      ><a name="5331" class="Symbol"
      >&#8594;</a
      ><a name="5332"
      > </a
      ><a name="5333" href="Stlc.html#5306" class="Bound"
      >L</a
      ><a name="5334"
      > </a
      ><a name="5335" href="Stlc.html#5242" class="Datatype Operator"
      >&#10233;*</a
      ><a name="5337"
      > </a
      ><a name="5338" href="Stlc.html#5311" class="Bound"
      >N</a
      ><a name="5339"
      >  

</a
      ><a name="5343" href="Stlc.html#5343" class="Function"
      >reduction&#8321;</a
      ><a name="5353"
      > </a
      ><a name="5354" class="Symbol"
      >:</a
      ><a name="5355"
      > </a
      ><a name="5356" href="Stlc.html#3904" class="Function"
      >not</a
      ><a name="5359"
      > </a
      ><a name="5360" href="Stlc.html#3553" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="5361"
      > </a
      ><a name="5362" href="Stlc.html#3580" class="InductiveConstructor"
      >true</a
      ><a name="5366"
      > </a
      ><a name="5367" href="Stlc.html#5242" class="Datatype Operator"
      >&#10233;*</a
      ><a name="5369"
      > </a
      ><a name="5370" href="Stlc.html#3594" class="InductiveConstructor"
      >false</a
      ><a name="5375"
      >
</a
      ><a name="5376" href="Stlc.html#5343" class="Function"
      >reduction&#8321;</a
      ><a name="5386"
      > </a
      ><a name="5387" class="Symbol"
      >=</a
      ><a name="5388"
      >
    </a
      ><a name="5393" href="Stlc.html#3904" class="Function"
      >not</a
      ><a name="5396"
      > </a
      ><a name="5397" href="Stlc.html#3553" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="5398"
      > </a
      ><a name="5399" href="Stlc.html#3580" class="InductiveConstructor"
      >true</a
      ><a name="5403"
      >
  </a
      ><a name="5406" href="Stlc.html#5295" class="InductiveConstructor Operator"
      >&#10233;&#10216;</a
      ><a name="5408"
      > </a
      ><a name="5409" href="Stlc.html#4749" class="InductiveConstructor"
      >&#946;&#955;&#183;</a
      ><a name="5412"
      > </a
      ><a name="5413" href="Stlc.html#4136" class="InductiveConstructor"
      >value-true</a
      ><a name="5423"
      > </a
      ><a name="5424" href="Stlc.html#5295" class="InductiveConstructor Operator"
      >&#10217;</a
      ><a name="5425"
      >
    </a
      ><a name="5430" href="Stlc.html#3609" class="InductiveConstructor Operator"
      >if</a
      ><a name="5432"
      > </a
      ><a name="5433" href="Stlc.html#3580" class="InductiveConstructor"
      >true</a
      ><a name="5437"
      > </a
      ><a name="5438" href="Stlc.html#3609" class="InductiveConstructor Operator"
      >then</a
      ><a name="5442"
      > </a
      ><a name="5443" href="Stlc.html#3594" class="InductiveConstructor"
      >false</a
      ><a name="5448"
      > </a
      ><a name="5449" href="Stlc.html#3609" class="InductiveConstructor Operator"
      >else</a
      ><a name="5453"
      > </a
      ><a name="5454" href="Stlc.html#3580" class="InductiveConstructor"
      >true</a
      ><a name="5458"
      >
  </a
      ><a name="5461" href="Stlc.html#5295" class="InductiveConstructor Operator"
      >&#10233;&#10216;</a
      ><a name="5463"
      > </a
      ><a name="5464" href="Stlc.html#4939" class="InductiveConstructor"
      >&#946;if-true</a
      ><a name="5472"
      > </a
      ><a name="5473" href="Stlc.html#5295" class="InductiveConstructor Operator"
      >&#10217;</a
      ><a name="5474"
      >
    </a
      ><a name="5479" href="Stlc.html#3594" class="InductiveConstructor"
      >false</a
      ><a name="5484"
      >
  </a
      ><a name="5487" href="Stlc.html#5275" class="InductiveConstructor Operator"
      >&#8718;</a
      ><a name="5488"
      >

</a
      ><a name="5490" href="Stlc.html#5490" class="Function"
      >reduction&#8322;</a
      ><a name="5500"
      > </a
      ><a name="5501" class="Symbol"
      >:</a
      ><a name="5502"
      > </a
      ><a name="5503" href="Stlc.html#3908" class="Function"
      >two</a
      ><a name="5506"
      > </a
      ><a name="5507" href="Stlc.html#3553" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="5508"
      > </a
      ><a name="5509" href="Stlc.html#3904" class="Function"
      >not</a
      ><a name="5512"
      > </a
      ><a name="5513" href="Stlc.html#3553" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="5514"
      > </a
      ><a name="5515" href="Stlc.html#3580" class="InductiveConstructor"
      >true</a
      ><a name="5519"
      > </a
      ><a name="5520" href="Stlc.html#5242" class="Datatype Operator"
      >&#10233;*</a
      ><a name="5522"
      > </a
      ><a name="5523" href="Stlc.html#3580" class="InductiveConstructor"
      >true</a
      ><a name="5527"
      >
</a
      ><a name="5528" href="Stlc.html#5490" class="Function"
      >reduction&#8322;</a
      ><a name="5538"
      > </a
      ><a name="5539" class="Symbol"
      >=</a
      ><a name="5540"
      >
    </a
      ><a name="5545" href="Stlc.html#3908" class="Function"
      >two</a
      ><a name="5548"
      > </a
      ><a name="5549" href="Stlc.html#3553" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="5550"
      > </a
      ><a name="5551" href="Stlc.html#3904" class="Function"
      >not</a
      ><a name="5554"
      > </a
      ><a name="5555" href="Stlc.html#3553" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="5556"
      > </a
      ><a name="5557" href="Stlc.html#3580" class="InductiveConstructor"
      >true</a
      ><a name="5561"
      >
  </a
      ><a name="5564" href="Stlc.html#5295" class="InductiveConstructor Operator"
      >&#10233;&#10216;</a
      ><a name="5566"
      > </a
      ><a name="5567" href="Stlc.html#4819" class="InductiveConstructor"
      >&#958;&#183;&#8321;</a
      ><a name="5570"
      > </a
      ><a name="5571" class="Symbol"
      >(</a
      ><a name="5572" href="Stlc.html#4749" class="InductiveConstructor"
      >&#946;&#955;&#183;</a
      ><a name="5575"
      > </a
      ><a name="5576" href="Stlc.html#4087" class="InductiveConstructor"
      >value-&#955;</a
      ><a name="5583" class="Symbol"
      >)</a
      ><a name="5584"
      > </a
      ><a name="5585" href="Stlc.html#5295" class="InductiveConstructor Operator"
      >&#10217;</a
      ><a name="5586"
      >
    </a
      ><a name="5591" class="Symbol"
      >(</a
      ><a name="5592" href="Stlc.html#3517" class="InductiveConstructor Operator"
      >&#955;[</a
      ><a name="5594"
      > </a
      ><a name="5595" href="Stlc.html#3874" class="Function"
      >x</a
      ><a name="5596"
      > </a
      ><a name="5597" href="Stlc.html#3517" class="InductiveConstructor Operator"
      >&#8758;</a
      ><a name="5598"
      > </a
      ><a name="5599" href="Stlc.html#2577" class="InductiveConstructor"
      >&#120121;</a
      ><a name="5600"
      > </a
      ><a name="5601" href="Stlc.html#3517" class="InductiveConstructor Operator"
      >]</a
      ><a name="5602"
      > </a
      ><a name="5603" href="Stlc.html#3904" class="Function"
      >not</a
      ><a name="5606"
      > </a
      ><a name="5607" href="Stlc.html#3553" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="5608"
      > </a
      ><a name="5609" class="Symbol"
      >(</a
      ><a name="5610" href="Stlc.html#3904" class="Function"
      >not</a
      ><a name="5613"
      > </a
      ><a name="5614" href="Stlc.html#3553" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="5615"
      > </a
      ><a name="5616" href="Stlc.html#3501" class="InductiveConstructor"
      >`</a
      ><a name="5617"
      > </a
      ><a name="5618" href="Stlc.html#3874" class="Function"
      >x</a
      ><a name="5619" class="Symbol"
      >))</a
      ><a name="5621"
      > </a
      ><a name="5622" href="Stlc.html#3553" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="5623"
      > </a
      ><a name="5624" href="Stlc.html#3580" class="InductiveConstructor"
      >true</a
      ><a name="5628"
      >
  </a
      ><a name="5631" href="Stlc.html#5295" class="InductiveConstructor Operator"
      >&#10233;&#10216;</a
      ><a name="5633"
      > </a
      ><a name="5634" href="Stlc.html#4749" class="InductiveConstructor"
      >&#946;&#955;&#183;</a
      ><a name="5637"
      > </a
      ><a name="5638" href="Stlc.html#4136" class="InductiveConstructor"
      >value-true</a
      ><a name="5648"
      > </a
      ><a name="5649" href="Stlc.html#5295" class="InductiveConstructor Operator"
      >&#10217;</a
      ><a name="5650"
      >
    </a
      ><a name="5655" href="Stlc.html#3904" class="Function"
      >not</a
      ><a name="5658"
      > </a
      ><a name="5659" href="Stlc.html#3553" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="5660"
      > </a
      ><a name="5661" class="Symbol"
      >(</a
      ><a name="5662" href="Stlc.html#3904" class="Function"
      >not</a
      ><a name="5665"
      > </a
      ><a name="5666" href="Stlc.html#3553" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="5667"
      > </a
      ><a name="5668" href="Stlc.html#3580" class="InductiveConstructor"
      >true</a
      ><a name="5672" class="Symbol"
      >)</a
      ><a name="5673"
      >
  </a
      ><a name="5676" href="Stlc.html#5295" class="InductiveConstructor Operator"
      >&#10233;&#10216;</a
      ><a name="5678"
      > </a
      ><a name="5679" href="Stlc.html#4872" class="InductiveConstructor"
      >&#958;&#183;&#8322;</a
      ><a name="5682"
      > </a
      ><a name="5683" href="Stlc.html#4087" class="InductiveConstructor"
      >value-&#955;</a
      ><a name="5690"
      > </a
      ><a name="5691" class="Symbol"
      >(</a
      ><a name="5692" href="Stlc.html#4749" class="InductiveConstructor"
      >&#946;&#955;&#183;</a
      ><a name="5695"
      > </a
      ><a name="5696" href="Stlc.html#4136" class="InductiveConstructor"
      >value-true</a
      ><a name="5706" class="Symbol"
      >)</a
      ><a name="5707"
      > </a
      ><a name="5708" href="Stlc.html#5295" class="InductiveConstructor Operator"
      >&#10217;</a
      ><a name="5709"
      >
    </a
      ><a name="5714" href="Stlc.html#3904" class="Function"
      >not</a
      ><a name="5717"
      > </a
      ><a name="5718" href="Stlc.html#3553" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="5719"
      > </a
      ><a name="5720" class="Symbol"
      >(</a
      ><a name="5721" href="Stlc.html#3609" class="InductiveConstructor Operator"
      >if</a
      ><a name="5723"
      > </a
      ><a name="5724" href="Stlc.html#3580" class="InductiveConstructor"
      >true</a
      ><a name="5728"
      > </a
      ><a name="5729" href="Stlc.html#3609" class="InductiveConstructor Operator"
      >then</a
      ><a name="5733"
      > </a
      ><a name="5734" href="Stlc.html#3594" class="InductiveConstructor"
      >false</a
      ><a name="5739"
      > </a
      ><a name="5740" href="Stlc.html#3609" class="InductiveConstructor Operator"
      >else</a
      ><a name="5744"
      > </a
      ><a name="5745" href="Stlc.html#3580" class="InductiveConstructor"
      >true</a
      ><a name="5749" class="Symbol"
      >)</a
      ><a name="5750"
      >
  </a
      ><a name="5753" href="Stlc.html#5295" class="InductiveConstructor Operator"
      >&#10233;&#10216;</a
      ><a name="5755"
      > </a
      ><a name="5756" href="Stlc.html#4872" class="InductiveConstructor"
      >&#958;&#183;&#8322;</a
      ><a name="5759"
      > </a
      ><a name="5760" href="Stlc.html#4087" class="InductiveConstructor"
      >value-&#955;</a
      ><a name="5767"
      > </a
      ><a name="5768" href="Stlc.html#4939" class="InductiveConstructor"
      >&#946;if-true</a
      ><a name="5776"
      >  </a
      ><a name="5778" href="Stlc.html#5295" class="InductiveConstructor Operator"
      >&#10217;</a
      ><a name="5779"
      >
    </a
      ><a name="5784" href="Stlc.html#3904" class="Function"
      >not</a
      ><a name="5787"
      > </a
      ><a name="5788" href="Stlc.html#3553" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="5789"
      > </a
      ><a name="5790" href="Stlc.html#3594" class="InductiveConstructor"
      >false</a
      ><a name="5795"
      >
  </a
      ><a name="5798" href="Stlc.html#5295" class="InductiveConstructor Operator"
      >&#10233;&#10216;</a
      ><a name="5800"
      > </a
      ><a name="5801" href="Stlc.html#4749" class="InductiveConstructor"
      >&#946;&#955;&#183;</a
      ><a name="5804"
      > </a
      ><a name="5805" href="Stlc.html#4163" class="InductiveConstructor"
      >value-false</a
      ><a name="5816"
      > </a
      ><a name="5817" href="Stlc.html#5295" class="InductiveConstructor Operator"
      >&#10217;</a
      ><a name="5818"
      >
    </a
      ><a name="5823" href="Stlc.html#3609" class="InductiveConstructor Operator"
      >if</a
      ><a name="5825"
      > </a
      ><a name="5826" href="Stlc.html#3594" class="InductiveConstructor"
      >false</a
      ><a name="5831"
      > </a
      ><a name="5832" href="Stlc.html#3609" class="InductiveConstructor Operator"
      >then</a
      ><a name="5836"
      > </a
      ><a name="5837" href="Stlc.html#3594" class="InductiveConstructor"
      >false</a
      ><a name="5842"
      > </a
      ><a name="5843" href="Stlc.html#3609" class="InductiveConstructor Operator"
      >else</a
      ><a name="5847"
      > </a
      ><a name="5848" href="Stlc.html#3580" class="InductiveConstructor"
      >true</a
      ><a name="5852"
      >
  </a
      ><a name="5855" href="Stlc.html#5295" class="InductiveConstructor Operator"
      >&#10233;&#10216;</a
      ><a name="5857"
      > </a
      ><a name="5858" href="Stlc.html#4992" class="InductiveConstructor"
      >&#946;if-false</a
      ><a name="5867"
      > </a
      ><a name="5868" href="Stlc.html#5295" class="InductiveConstructor Operator"
      >&#10217;</a
      ><a name="5869"
      >
    </a
      ><a name="5874" href="Stlc.html#3580" class="InductiveConstructor"
      >true</a
      ><a name="5878"
      >
  </a
      ><a name="5881" href="Stlc.html#5275" class="InductiveConstructor Operator"
      >&#8718;</a
      >

</pre>

Much of the above, though not all, can be filled in using C-c C-r and C-c C-s.



## Type rules

<pre class="Agda">

<a name="6005" href="Stlc.html#6005" class="Function"
      >Context</a
      ><a name="6012"
      > </a
      ><a name="6013" class="Symbol"
      >:</a
      ><a name="6014"
      > </a
      ><a name="6015" class="PrimitiveType"
      >Set</a
      ><a name="6018"
      >
</a
      ><a name="6019" href="Stlc.html#6005" class="Function"
      >Context</a
      ><a name="6026"
      > </a
      ><a name="6027" class="Symbol"
      >=</a
      ><a name="6028"
      > </a
      ><a name="6029" href="Maps.html#10132" class="Function"
      >PartialMap</a
      ><a name="6039"
      > </a
      ><a name="6040" href="Stlc.html#2531" class="Datatype"
      >Type</a
      ><a name="6044"
      >

</a
      ><a name="6046" class="Keyword"
      >infix</a
      ><a name="6051"
      > </a
      ><a name="6052" class="Number"
      >10</a
      ><a name="6054"
      > </a
      ><a name="6055" href="Stlc.html#6067" class="Datatype Operator"
      >_&#8866;_&#8758;_</a
      ><a name="6060"
      >

</a
      ><a name="6062" class="Keyword"
      >data</a
      ><a name="6066"
      > </a
      ><a name="6067" href="Stlc.html#6067" class="Datatype Operator"
      >_&#8866;_&#8758;_</a
      ><a name="6072"
      > </a
      ><a name="6073" class="Symbol"
      >:</a
      ><a name="6074"
      > </a
      ><a name="6075" href="Stlc.html#6005" class="Function"
      >Context</a
      ><a name="6082"
      > </a
      ><a name="6083" class="Symbol"
      >&#8594;</a
      ><a name="6084"
      > </a
      ><a name="6085" href="Stlc.html#3482" class="Datatype"
      >Term</a
      ><a name="6089"
      > </a
      ><a name="6090" class="Symbol"
      >&#8594;</a
      ><a name="6091"
      > </a
      ><a name="6092" href="Stlc.html#2531" class="Datatype"
      >Type</a
      ><a name="6096"
      > </a
      ><a name="6097" class="Symbol"
      >&#8594;</a
      ><a name="6098"
      > </a
      ><a name="6099" class="PrimitiveType"
      >Set</a
      ><a name="6102"
      > </a
      ><a name="6103" class="Keyword"
      >where</a
      ><a name="6108"
      >
  </a
      ><a name="6111" href="Stlc.html#6111" class="InductiveConstructor"
      >Ax</a
      ><a name="6113"
      > </a
      ><a name="6114" class="Symbol"
      >:</a
      ><a name="6115"
      > </a
      ><a name="6116" class="Symbol"
      >&#8704;</a
      ><a name="6117"
      > </a
      ><a name="6118" class="Symbol"
      >{</a
      ><a name="6119" href="Stlc.html#6119" class="Bound"
      >&#915;</a
      ><a name="6120"
      > </a
      ><a name="6121" href="Stlc.html#6121" class="Bound"
      >x</a
      ><a name="6122"
      > </a
      ><a name="6123" href="Stlc.html#6123" class="Bound"
      >A</a
      ><a name="6124" class="Symbol"
      >}</a
      ><a name="6125"
      > </a
      ><a name="6126" class="Symbol"
      >&#8594;</a
      ><a name="6127"
      >
    </a
      ><a name="6132" href="Stlc.html#6119" class="Bound"
      >&#915;</a
      ><a name="6133"
      > </a
      ><a name="6134" href="Stlc.html#6121" class="Bound"
      >x</a
      ><a name="6135"
      > </a
      ><a name="6136" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="6137"
      > </a
      ><a name="6138" href="https://agda.github.io/agda-stdlib/Data.Maybe.Base.html#373" class="InductiveConstructor"
      >just</a
      ><a name="6142"
      > </a
      ><a name="6143" href="Stlc.html#6123" class="Bound"
      >A</a
      ><a name="6144"
      > </a
      ><a name="6145" class="Symbol"
      >&#8594;</a
      ><a name="6146"
      >
    </a
      ><a name="6151" href="Stlc.html#6119" class="Bound"
      >&#915;</a
      ><a name="6152"
      > </a
      ><a name="6153" href="Stlc.html#6067" class="Datatype Operator"
      >&#8866;</a
      ><a name="6154"
      > </a
      ><a name="6155" href="Stlc.html#3501" class="InductiveConstructor"
      >`</a
      ><a name="6156"
      > </a
      ><a name="6157" href="Stlc.html#6121" class="Bound"
      >x</a
      ><a name="6158"
      > </a
      ><a name="6159" href="Stlc.html#6067" class="Datatype Operator"
      >&#8758;</a
      ><a name="6160"
      > </a
      ><a name="6161" href="Stlc.html#6123" class="Bound"
      >A</a
      ><a name="6162"
      >
  </a
      ><a name="6165" href="Stlc.html#6165" class="InductiveConstructor"
      >&#8658;-I</a
      ><a name="6168"
      > </a
      ><a name="6169" class="Symbol"
      >:</a
      ><a name="6170"
      > </a
      ><a name="6171" class="Symbol"
      >&#8704;</a
      ><a name="6172"
      > </a
      ><a name="6173" class="Symbol"
      >{</a
      ><a name="6174" href="Stlc.html#6174" class="Bound"
      >&#915;</a
      ><a name="6175"
      > </a
      ><a name="6176" href="Stlc.html#6176" class="Bound"
      >x</a
      ><a name="6177"
      > </a
      ><a name="6178" href="Stlc.html#6178" class="Bound"
      >N</a
      ><a name="6179"
      > </a
      ><a name="6180" href="Stlc.html#6180" class="Bound"
      >A</a
      ><a name="6181"
      > </a
      ><a name="6182" href="Stlc.html#6182" class="Bound"
      >B</a
      ><a name="6183" class="Symbol"
      >}</a
      ><a name="6184"
      > </a
      ><a name="6185" class="Symbol"
      >&#8594;</a
      ><a name="6186"
      >
    </a
      ><a name="6191" href="Stlc.html#6174" class="Bound"
      >&#915;</a
      ><a name="6192"
      > </a
      ><a name="6193" href="Maps.html#10368" class="Function Operator"
      >,</a
      ><a name="6194"
      > </a
      ><a name="6195" href="Stlc.html#6176" class="Bound"
      >x</a
      ><a name="6196"
      > </a
      ><a name="6197" href="Maps.html#10368" class="Function Operator"
      >&#8758;</a
      ><a name="6198"
      > </a
      ><a name="6199" href="Stlc.html#6180" class="Bound"
      >A</a
      ><a name="6200"
      > </a
      ><a name="6201" href="Stlc.html#6067" class="Datatype Operator"
      >&#8866;</a
      ><a name="6202"
      > </a
      ><a name="6203" href="Stlc.html#6178" class="Bound"
      >N</a
      ><a name="6204"
      > </a
      ><a name="6205" href="Stlc.html#6067" class="Datatype Operator"
      >&#8758;</a
      ><a name="6206"
      > </a
      ><a name="6207" href="Stlc.html#6182" class="Bound"
      >B</a
      ><a name="6208"
      > </a
      ><a name="6209" class="Symbol"
      >&#8594;</a
      ><a name="6210"
      >
    </a
      ><a name="6215" href="Stlc.html#6174" class="Bound"
      >&#915;</a
      ><a name="6216"
      > </a
      ><a name="6217" href="Stlc.html#6067" class="Datatype Operator"
      >&#8866;</a
      ><a name="6218"
      > </a
      ><a name="6219" href="Stlc.html#3517" class="InductiveConstructor Operator"
      >&#955;[</a
      ><a name="6221"
      > </a
      ><a name="6222" href="Stlc.html#6176" class="Bound"
      >x</a
      ><a name="6223"
      > </a
      ><a name="6224" href="Stlc.html#3517" class="InductiveConstructor Operator"
      >&#8758;</a
      ><a name="6225"
      > </a
      ><a name="6226" href="Stlc.html#6180" class="Bound"
      >A</a
      ><a name="6227"
      > </a
      ><a name="6228" href="Stlc.html#3517" class="InductiveConstructor Operator"
      >]</a
      ><a name="6229"
      > </a
      ><a name="6230" href="Stlc.html#6178" class="Bound"
      >N</a
      ><a name="6231"
      > </a
      ><a name="6232" href="Stlc.html#6067" class="Datatype Operator"
      >&#8758;</a
      ><a name="6233"
      > </a
      ><a name="6234" href="Stlc.html#6180" class="Bound"
      >A</a
      ><a name="6235"
      > </a
      ><a name="6236" href="Stlc.html#2550" class="InductiveConstructor Operator"
      >&#8658;</a
      ><a name="6237"
      > </a
      ><a name="6238" href="Stlc.html#6182" class="Bound"
      >B</a
      ><a name="6239"
      >
  </a
      ><a name="6242" href="Stlc.html#6242" class="InductiveConstructor"
      >&#8658;-E</a
      ><a name="6245"
      > </a
      ><a name="6246" class="Symbol"
      >:</a
      ><a name="6247"
      > </a
      ><a name="6248" class="Symbol"
      >&#8704;</a
      ><a name="6249"
      > </a
      ><a name="6250" class="Symbol"
      >{</a
      ><a name="6251" href="Stlc.html#6251" class="Bound"
      >&#915;</a
      ><a name="6252"
      > </a
      ><a name="6253" href="Stlc.html#6253" class="Bound"
      >L</a
      ><a name="6254"
      > </a
      ><a name="6255" href="Stlc.html#6255" class="Bound"
      >M</a
      ><a name="6256"
      > </a
      ><a name="6257" href="Stlc.html#6257" class="Bound"
      >A</a
      ><a name="6258"
      > </a
      ><a name="6259" href="Stlc.html#6259" class="Bound"
      >B</a
      ><a name="6260" class="Symbol"
      >}</a
      ><a name="6261"
      > </a
      ><a name="6262" class="Symbol"
      >&#8594;</a
      ><a name="6263"
      >
    </a
      ><a name="6268" href="Stlc.html#6251" class="Bound"
      >&#915;</a
      ><a name="6269"
      > </a
      ><a name="6270" href="Stlc.html#6067" class="Datatype Operator"
      >&#8866;</a
      ><a name="6271"
      > </a
      ><a name="6272" href="Stlc.html#6253" class="Bound"
      >L</a
      ><a name="6273"
      > </a
      ><a name="6274" href="Stlc.html#6067" class="Datatype Operator"
      >&#8758;</a
      ><a name="6275"
      > </a
      ><a name="6276" href="Stlc.html#6257" class="Bound"
      >A</a
      ><a name="6277"
      > </a
      ><a name="6278" href="Stlc.html#2550" class="InductiveConstructor Operator"
      >&#8658;</a
      ><a name="6279"
      > </a
      ><a name="6280" href="Stlc.html#6259" class="Bound"
      >B</a
      ><a name="6281"
      > </a
      ><a name="6282" class="Symbol"
      >&#8594;</a
      ><a name="6283"
      >
    </a
      ><a name="6288" href="Stlc.html#6251" class="Bound"
      >&#915;</a
      ><a name="6289"
      > </a
      ><a name="6290" href="Stlc.html#6067" class="Datatype Operator"
      >&#8866;</a
      ><a name="6291"
      > </a
      ><a name="6292" href="Stlc.html#6255" class="Bound"
      >M</a
      ><a name="6293"
      > </a
      ><a name="6294" href="Stlc.html#6067" class="Datatype Operator"
      >&#8758;</a
      ><a name="6295"
      > </a
      ><a name="6296" href="Stlc.html#6257" class="Bound"
      >A</a
      ><a name="6297"
      > </a
      ><a name="6298" class="Symbol"
      >&#8594;</a
      ><a name="6299"
      >
    </a
      ><a name="6304" href="Stlc.html#6251" class="Bound"
      >&#915;</a
      ><a name="6305"
      > </a
      ><a name="6306" href="Stlc.html#6067" class="Datatype Operator"
      >&#8866;</a
      ><a name="6307"
      > </a
      ><a name="6308" href="Stlc.html#6253" class="Bound"
      >L</a
      ><a name="6309"
      > </a
      ><a name="6310" href="Stlc.html#3553" class="InductiveConstructor Operator"
      >&#183;</a
      ><a name="6311"
      > </a
      ><a name="6312" href="Stlc.html#6255" class="Bound"
      >M</a
      ><a name="6313"
      > </a
      ><a name="6314" href="Stlc.html#6067" class="Datatype Operator"
      >&#8758;</a
      ><a name="6315"
      > </a
      ><a name="6316" href="Stlc.html#6259" class="Bound"
      >B</a
      ><a name="6317"
      >
  </a
      ><a name="6320" href="Stlc.html#6320" class="InductiveConstructor"
      >&#120121;-I&#8321;</a
      ><a name="6324"
      > </a
      ><a name="6325" class="Symbol"
      >:</a
      ><a name="6326"
      > </a
      ><a name="6327" class="Symbol"
      >&#8704;</a
      ><a name="6328"
      > </a
      ><a name="6329" class="Symbol"
      >{</a
      ><a name="6330" href="Stlc.html#6330" class="Bound"
      >&#915;</a
      ><a name="6331" class="Symbol"
      >}</a
      ><a name="6332"
      > </a
      ><a name="6333" class="Symbol"
      >&#8594;</a
      ><a name="6334"
      >
    </a
      ><a name="6339" href="Stlc.html#6330" class="Bound"
      >&#915;</a
      ><a name="6340"
      > </a
      ><a name="6341" href="Stlc.html#6067" class="Datatype Operator"
      >&#8866;</a
      ><a name="6342"
      > </a
      ><a name="6343" href="Stlc.html#3580" class="InductiveConstructor"
      >true</a
      ><a name="6347"
      > </a
      ><a name="6348" href="Stlc.html#6067" class="Datatype Operator"
      >&#8758;</a
      ><a name="6349"
      > </a
      ><a name="6350" href="Stlc.html#2577" class="InductiveConstructor"
      >&#120121;</a
      ><a name="6351"
      >
  </a
      ><a name="6354" href="Stlc.html#6354" class="InductiveConstructor"
      >&#120121;-I&#8322;</a
      ><a name="6358"
      > </a
      ><a name="6359" class="Symbol"
      >:</a
      ><a name="6360"
      > </a
      ><a name="6361" class="Symbol"
      >&#8704;</a
      ><a name="6362"
      > </a
      ><a name="6363" class="Symbol"
      >{</a
      ><a name="6364" href="Stlc.html#6364" class="Bound"
      >&#915;</a
      ><a name="6365" class="Symbol"
      >}</a
      ><a name="6366"
      > </a
      ><a name="6367" class="Symbol"
      >&#8594;</a
      ><a name="6368"
      >
    </a
      ><a name="6373" href="Stlc.html#6364" class="Bound"
      >&#915;</a
      ><a name="6374"
      > </a
      ><a name="6375" href="Stlc.html#6067" class="Datatype Operator"
      >&#8866;</a
      ><a name="6376"
      > </a
      ><a name="6377" href="Stlc.html#3594" class="InductiveConstructor"
      >false</a
      ><a name="6382"
      > </a
      ><a name="6383" href="Stlc.html#6067" class="Datatype Operator"
      >&#8758;</a
      ><a name="6384"
      > </a
      ><a name="6385" href="Stlc.html#2577" class="InductiveConstructor"
      >&#120121;</a
      ><a name="6386"
      >
  </a
      ><a name="6389" href="Stlc.html#6389" class="InductiveConstructor"
      >&#120121;-E</a
      ><a name="6392"
      > </a
      ><a name="6393" class="Symbol"
      >:</a
      ><a name="6394"
      > </a
      ><a name="6395" class="Symbol"
      >&#8704;</a
      ><a name="6396"
      > </a
      ><a name="6397" class="Symbol"
      >{</a
      ><a name="6398" href="Stlc.html#6398" class="Bound"
      >&#915;</a
      ><a name="6399"
      > </a
      ><a name="6400" href="Stlc.html#6400" class="Bound"
      >L</a
      ><a name="6401"
      > </a
      ><a name="6402" href="Stlc.html#6402" class="Bound"
      >M</a
      ><a name="6403"
      > </a
      ><a name="6404" href="Stlc.html#6404" class="Bound"
      >N</a
      ><a name="6405"
      > </a
      ><a name="6406" href="Stlc.html#6406" class="Bound"
      >A</a
      ><a name="6407" class="Symbol"
      >}</a
      ><a name="6408"
      > </a
      ><a name="6409" class="Symbol"
      >&#8594;</a
      ><a name="6410"
      >
    </a
      ><a name="6415" href="Stlc.html#6398" class="Bound"
      >&#915;</a
      ><a name="6416"
      > </a
      ><a name="6417" href="Stlc.html#6067" class="Datatype Operator"
      >&#8866;</a
      ><a name="6418"
      > </a
      ><a name="6419" href="Stlc.html#6400" class="Bound"
      >L</a
      ><a name="6420"
      > </a
      ><a name="6421" href="Stlc.html#6067" class="Datatype Operator"
      >&#8758;</a
      ><a name="6422"
      > </a
      ><a name="6423" href="Stlc.html#2577" class="InductiveConstructor"
      >&#120121;</a
      ><a name="6424"
      > </a
      ><a name="6425" class="Symbol"
      >&#8594;</a
      ><a name="6426"
      >
    </a
      ><a name="6431" href="Stlc.html#6398" class="Bound"
      >&#915;</a
      ><a name="6432"
      > </a
      ><a name="6433" href="Stlc.html#6067" class="Datatype Operator"
      >&#8866;</a
      ><a name="6434"
      > </a
      ><a name="6435" href="Stlc.html#6402" class="Bound"
      >M</a
      ><a name="6436"
      > </a
      ><a name="6437" href="Stlc.html#6067" class="Datatype Operator"
      >&#8758;</a
      ><a name="6438"
      > </a
      ><a name="6439" href="Stlc.html#6406" class="Bound"
      >A</a
      ><a name="6440"
      > </a
      ><a name="6441" class="Symbol"
      >&#8594;</a
      ><a name="6442"
      >
    </a
      ><a name="6447" href="Stlc.html#6398" class="Bound"
      >&#915;</a
      ><a name="6448"
      > </a
      ><a name="6449" href="Stlc.html#6067" class="Datatype Operator"
      >&#8866;</a
      ><a name="6450"
      > </a
      ><a name="6451" href="Stlc.html#6404" class="Bound"
      >N</a
      ><a name="6452"
      > </a
      ><a name="6453" href="Stlc.html#6067" class="Datatype Operator"
      >&#8758;</a
      ><a name="6454"
      > </a
      ><a name="6455" href="Stlc.html#6406" class="Bound"
      >A</a
      ><a name="6456"
      > </a
      ><a name="6457" class="Symbol"
      >&#8594;</a
      ><a name="6458"
      >
    </a
      ><a name="6463" href="Stlc.html#6398" class="Bound"
      >&#915;</a
      ><a name="6464"
      > </a
      ><a name="6465" href="Stlc.html#6067" class="Datatype Operator"
      >&#8866;</a
      ><a name="6466"
      > </a
      ><a name="6467" href="Stlc.html#3609" class="InductiveConstructor Operator"
      >if</a
      ><a name="6469"
      > </a
      ><a name="6470" href="Stlc.html#6400" class="Bound"
      >L</a
      ><a name="6471"
      > </a
      ><a name="6472" href="Stlc.html#3609" class="InductiveConstructor Operator"
      >then</a
      ><a name="6476"
      > </a
      ><a name="6477" href="Stlc.html#6402" class="Bound"
      >M</a
      ><a name="6478"
      > </a
      ><a name="6479" href="Stlc.html#3609" class="InductiveConstructor Operator"
      >else</a
      ><a name="6483"
      > </a
      ><a name="6484" href="Stlc.html#6404" class="Bound"
      >N</a
      ><a name="6485"
      > </a
      ><a name="6486" href="Stlc.html#6067" class="Datatype Operator"
      >&#8758;</a
      ><a name="6487"
      > </a
      ><a name="6488" href="Stlc.html#6406" class="Bound"
      >A</a
      >

</pre>

## Example type derivations

<pre class="Agda">

<a name="6548" href="Stlc.html#6548" class="Function"
      >typing&#8321;</a
      ><a name="6555"
      > </a
      ><a name="6556" class="Symbol"
      >:</a
      ><a name="6557"
      > </a
      ><a name="6558" href="Maps.html#10265" class="Function"
      >&#8709;</a
      ><a name="6559"
      > </a
      ><a name="6560" href="Stlc.html#6067" class="Datatype Operator"
      >&#8866;</a
      ><a name="6561"
      > </a
      ><a name="6562" href="Stlc.html#3904" class="Function"
      >not</a
      ><a name="6565"
      > </a
      ><a name="6566" href="Stlc.html#6067" class="Datatype Operator"
      >&#8758;</a
      ><a name="6567"
      > </a
      ><a name="6568" href="Stlc.html#2577" class="InductiveConstructor"
      >&#120121;</a
      ><a name="6569"
      > </a
      ><a name="6570" href="Stlc.html#2550" class="InductiveConstructor Operator"
      >&#8658;</a
      ><a name="6571"
      > </a
      ><a name="6572" href="Stlc.html#2577" class="InductiveConstructor"
      >&#120121;</a
      ><a name="6573"
      >
</a
      ><a name="6574" href="Stlc.html#6548" class="Function"
      >typing&#8321;</a
      ><a name="6581"
      > </a
      ><a name="6582" class="Symbol"
      >=</a
      ><a name="6583"
      > </a
      ><a name="6584" href="Stlc.html#6165" class="InductiveConstructor"
      >&#8658;-I</a
      ><a name="6587"
      > </a
      ><a name="6588" class="Symbol"
      >(</a
      ><a name="6589" href="Stlc.html#6389" class="InductiveConstructor"
      >&#120121;-E</a
      ><a name="6592"
      > </a
      ><a name="6593" class="Symbol"
      >(</a
      ><a name="6594" href="Stlc.html#6111" class="InductiveConstructor"
      >Ax</a
      ><a name="6596"
      > </a
      ><a name="6597" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="6601" class="Symbol"
      >)</a
      ><a name="6602"
      > </a
      ><a name="6603" href="Stlc.html#6354" class="InductiveConstructor"
      >&#120121;-I&#8322;</a
      ><a name="6607"
      > </a
      ><a name="6608" href="Stlc.html#6320" class="InductiveConstructor"
      >&#120121;-I&#8321;</a
      ><a name="6612" class="Symbol"
      >)</a
      ><a name="6613"
      >

</a
      ><a name="6615" href="Stlc.html#6615" class="Function"
      >typing&#8322;</a
      ><a name="6622"
      > </a
      ><a name="6623" class="Symbol"
      >:</a
      ><a name="6624"
      > </a
      ><a name="6625" href="Maps.html#10265" class="Function"
      >&#8709;</a
      ><a name="6626"
      > </a
      ><a name="6627" href="Stlc.html#6067" class="Datatype Operator"
      >&#8866;</a
      ><a name="6628"
      > </a
      ><a name="6629" href="Stlc.html#3908" class="Function"
      >two</a
      ><a name="6632"
      > </a
      ><a name="6633" href="Stlc.html#6067" class="Datatype Operator"
      >&#8758;</a
      ><a name="6634"
      > </a
      ><a name="6635" class="Symbol"
      >(</a
      ><a name="6636" href="Stlc.html#2577" class="InductiveConstructor"
      >&#120121;</a
      ><a name="6637"
      > </a
      ><a name="6638" href="Stlc.html#2550" class="InductiveConstructor Operator"
      >&#8658;</a
      ><a name="6639"
      > </a
      ><a name="6640" href="Stlc.html#2577" class="InductiveConstructor"
      >&#120121;</a
      ><a name="6641" class="Symbol"
      >)</a
      ><a name="6642"
      > </a
      ><a name="6643" href="Stlc.html#2550" class="InductiveConstructor Operator"
      >&#8658;</a
      ><a name="6644"
      > </a
      ><a name="6645" href="Stlc.html#2577" class="InductiveConstructor"
      >&#120121;</a
      ><a name="6646"
      > </a
      ><a name="6647" href="Stlc.html#2550" class="InductiveConstructor Operator"
      >&#8658;</a
      ><a name="6648"
      > </a
      ><a name="6649" href="Stlc.html#2577" class="InductiveConstructor"
      >&#120121;</a
      ><a name="6650"
      >
</a
      ><a name="6651" href="Stlc.html#6615" class="Function"
      >typing&#8322;</a
      ><a name="6658"
      > </a
      ><a name="6659" class="Symbol"
      >=</a
      ><a name="6660"
      > </a
      ><a name="6661" href="Stlc.html#6165" class="InductiveConstructor"
      >&#8658;-I</a
      ><a name="6664"
      > </a
      ><a name="6665" class="Symbol"
      >(</a
      ><a name="6666" href="Stlc.html#6165" class="InductiveConstructor"
      >&#8658;-I</a
      ><a name="6669"
      > </a
      ><a name="6670" class="Symbol"
      >(</a
      ><a name="6671" href="Stlc.html#6242" class="InductiveConstructor"
      >&#8658;-E</a
      ><a name="6674"
      > </a
      ><a name="6675" class="Symbol"
      >(</a
      ><a name="6676" href="Stlc.html#6111" class="InductiveConstructor"
      >Ax</a
      ><a name="6678"
      > </a
      ><a name="6679" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="6683" class="Symbol"
      >)</a
      ><a name="6684"
      > </a
      ><a name="6685" class="Symbol"
      >(</a
      ><a name="6686" href="Stlc.html#6242" class="InductiveConstructor"
      >&#8658;-E</a
      ><a name="6689"
      > </a
      ><a name="6690" class="Symbol"
      >(</a
      ><a name="6691" href="Stlc.html#6111" class="InductiveConstructor"
      >Ax</a
      ><a name="6693"
      > </a
      ><a name="6694" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="6698" class="Symbol"
      >)</a
      ><a name="6699"
      > </a
      ><a name="6700" class="Symbol"
      >(</a
      ><a name="6701" href="Stlc.html#6111" class="InductiveConstructor"
      >Ax</a
      ><a name="6703"
      > </a
      ><a name="6704" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="6708" class="Symbol"
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
that `\` x`, `false`, and `true` are typed using `Ax`, `𝔹-I₂`, and
`𝔹-I₁` respectively. The `Ax` rule in turn takes an argument, to show
that `(∅ , x ∶ 𝔹) x = just 𝔹`, which can in turn be specified with a
hole. After filling in all holes, the term is as above.

The entire process can be automated using Agsy, invoked with C-c C-a.


