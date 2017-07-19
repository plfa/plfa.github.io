---
title     : "Basics: Functional Programming in Agda"
layout    : page
permalink : /Basics
---

<pre class="Agda">

<a name="113" class="Keyword"
      >open</a
      ><a name="117"
      > </a
      ><a name="118" class="Keyword"
      >import</a
      ><a name="124"
      > </a
      ><a name="125" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#1" class="Module"
      >Relation.Binary.PropositionalEquality</a
      ><a name="162"
      > </a
      ><a name="163" class="Keyword"
      >using</a
      ><a name="168"
      > </a
      ><a name="169" class="Symbol"
      >(</a
      ><a name="170" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >_&#8801;_</a
      ><a name="173" class="Symbol"
      >;</a
      ><a name="174"
      > </a
      ><a name="175" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="179" class="Symbol"
      >)</a
      >

</pre>

The functional programming style brings programming closer to
simple, everyday mathematics: If a procedure or method has no side
effects, then (ignoring efficiency) all we need to understand
about it is how it maps inputs to outputs -- that is, we can think
of it as just a concrete method for computing a mathematical
function.  This is one sense of the word "functional" in
"functional programming."  The direct connection between programs
and simple mathematical objects supports both formal correctness
proofs and sound informal reasoning about program behavior.

The other sense in which functional programming is "functional" is
that it emphasizes the use of functions (or methods) as
_first-class_ values -- i.e., values that can be passed as
arguments to other functions, returned as results, included in
data structures, etc.  The recognition that functions can be
treated as data in this way enables a host of useful and powerful
idioms.

Other common features of functional languages include _algebraic
data types_ and _pattern matching_, which make it easy to
construct and manipulate rich data structures, and sophisticated
_polymorphic type systems_ supporting abstraction and code reuse.
Agda shares all of these features.

This chapter introduces the most essential elements of Agda.

## Enumerated Types

One unusual aspect of Agda is that its set of built-in
features is _extremely_ small. For example, instead of providing
the usual palette of atomic data types (booleans, integers,
strings, etc.), Agda offers a powerful mechanism for defining new
data types from scratch, from which all these familiar types arise
as instances.

Naturally, the Agda distribution comes with an extensive standard
library providing definitions of booleans, numbers, and many
common data structures like lists and hash tables.  But there is
nothing magic or primitive about these library definitions.  To
illustrate this, we will explicitly recapitulate all the
definitions we need in this course, rather than just getting them
implicitly from the library.

To see how this definition mechanism works, let's start with a
very simple example.

### Days of the Week

The following declaration tells Agda that we are defining
a new set of data values -- a _type_.

<pre class="Agda">

<a name="2469" class="Keyword"
      >data</a
      ><a name="2473"
      > </a
      ><a name="2474" href="Basics.html#2474" class="Datatype"
      >Day</a
      ><a name="2477"
      > </a
      ><a name="2478" class="Symbol"
      >:</a
      ><a name="2479"
      > </a
      ><a name="2480" class="PrimitiveType"
      >Set</a
      ><a name="2483"
      > </a
      ><a name="2484" class="Keyword"
      >where</a
      ><a name="2489"
      >
  </a
      ><a name="2492" href="Basics.html#2492" class="InductiveConstructor"
      >monday</a
      ><a name="2498"
      >    </a
      ><a name="2502" class="Symbol"
      >:</a
      ><a name="2503"
      > </a
      ><a name="2504" href="Basics.html#2474" class="Datatype"
      >Day</a
      ><a name="2507"
      >
  </a
      ><a name="2510" href="Basics.html#2510" class="InductiveConstructor"
      >tuesday</a
      ><a name="2517"
      >   </a
      ><a name="2520" class="Symbol"
      >:</a
      ><a name="2521"
      > </a
      ><a name="2522" href="Basics.html#2474" class="Datatype"
      >Day</a
      ><a name="2525"
      >
  </a
      ><a name="2528" href="Basics.html#2528" class="InductiveConstructor"
      >wednesday</a
      ><a name="2537"
      > </a
      ><a name="2538" class="Symbol"
      >:</a
      ><a name="2539"
      > </a
      ><a name="2540" href="Basics.html#2474" class="Datatype"
      >Day</a
      ><a name="2543"
      >
  </a
      ><a name="2546" href="Basics.html#2546" class="InductiveConstructor"
      >thursday</a
      ><a name="2554"
      >  </a
      ><a name="2556" class="Symbol"
      >:</a
      ><a name="2557"
      > </a
      ><a name="2558" href="Basics.html#2474" class="Datatype"
      >Day</a
      ><a name="2561"
      >
  </a
      ><a name="2564" href="Basics.html#2564" class="InductiveConstructor"
      >friday</a
      ><a name="2570"
      >    </a
      ><a name="2574" class="Symbol"
      >:</a
      ><a name="2575"
      > </a
      ><a name="2576" href="Basics.html#2474" class="Datatype"
      >Day</a
      ><a name="2579"
      >
  </a
      ><a name="2582" href="Basics.html#2582" class="InductiveConstructor"
      >saturday</a
      ><a name="2590"
      >  </a
      ><a name="2592" class="Symbol"
      >:</a
      ><a name="2593"
      > </a
      ><a name="2594" href="Basics.html#2474" class="Datatype"
      >Day</a
      ><a name="2597"
      >
  </a
      ><a name="2600" href="Basics.html#2600" class="InductiveConstructor"
      >sunday</a
      ><a name="2606"
      >    </a
      ><a name="2610" class="Symbol"
      >:</a
      ><a name="2611"
      > </a
      ><a name="2612" href="Basics.html#2474" class="Datatype"
      >Day</a
      >

</pre>

The type is called `day`, and its members are `monday`,
`tuesday`, etc.  The second and following lines of the definition
can be read "`monday` is a `day`, `tuesday` is a `day`, etc."

Having defined `day`, we can write functions that operate on
days.

<pre class="Agda">

<a name="2894" href="Basics.html#2894" class="Function"
      >nextWeekday</a
      ><a name="2905"
      > </a
      ><a name="2906" class="Symbol"
      >:</a
      ><a name="2907"
      > </a
      ><a name="2908" href="Basics.html#2474" class="Datatype"
      >Day</a
      ><a name="2911"
      > </a
      ><a name="2912" class="Symbol"
      >-&gt;</a
      ><a name="2914"
      > </a
      ><a name="2915" href="Basics.html#2474" class="Datatype"
      >Day</a
      ><a name="2918"
      >
</a
      ><a name="2919" href="Basics.html#2894" class="Function"
      >nextWeekday</a
      ><a name="2930"
      > </a
      ><a name="2931" href="Basics.html#2492" class="InductiveConstructor"
      >monday</a
      ><a name="2937"
      >    </a
      ><a name="2941" class="Symbol"
      >=</a
      ><a name="2942"
      > </a
      ><a name="2943" href="Basics.html#2510" class="InductiveConstructor"
      >tuesday</a
      ><a name="2950"
      >
</a
      ><a name="2951" href="Basics.html#2894" class="Function"
      >nextWeekday</a
      ><a name="2962"
      > </a
      ><a name="2963" href="Basics.html#2510" class="InductiveConstructor"
      >tuesday</a
      ><a name="2970"
      >   </a
      ><a name="2973" class="Symbol"
      >=</a
      ><a name="2974"
      > </a
      ><a name="2975" href="Basics.html#2528" class="InductiveConstructor"
      >wednesday</a
      ><a name="2984"
      >
</a
      ><a name="2985" href="Basics.html#2894" class="Function"
      >nextWeekday</a
      ><a name="2996"
      > </a
      ><a name="2997" href="Basics.html#2528" class="InductiveConstructor"
      >wednesday</a
      ><a name="3006"
      > </a
      ><a name="3007" class="Symbol"
      >=</a
      ><a name="3008"
      > </a
      ><a name="3009" href="Basics.html#2546" class="InductiveConstructor"
      >thursday</a
      ><a name="3017"
      >
</a
      ><a name="3018" href="Basics.html#2894" class="Function"
      >nextWeekday</a
      ><a name="3029"
      > </a
      ><a name="3030" href="Basics.html#2546" class="InductiveConstructor"
      >thursday</a
      ><a name="3038"
      >  </a
      ><a name="3040" class="Symbol"
      >=</a
      ><a name="3041"
      > </a
      ><a name="3042" href="Basics.html#2564" class="InductiveConstructor"
      >friday</a
      ><a name="3048"
      >
</a
      ><a name="3049" href="Basics.html#2894" class="Function"
      >nextWeekday</a
      ><a name="3060"
      > </a
      ><a name="3061" href="Basics.html#2564" class="InductiveConstructor"
      >friday</a
      ><a name="3067"
      >    </a
      ><a name="3071" class="Symbol"
      >=</a
      ><a name="3072"
      > </a
      ><a name="3073" href="Basics.html#2492" class="InductiveConstructor"
      >monday</a
      ><a name="3079"
      >
</a
      ><a name="3080" href="Basics.html#2894" class="Function"
      >nextWeekday</a
      ><a name="3091"
      > </a
      ><a name="3092" href="Basics.html#2582" class="InductiveConstructor"
      >saturday</a
      ><a name="3100"
      >  </a
      ><a name="3102" class="Symbol"
      >=</a
      ><a name="3103"
      > </a
      ><a name="3104" href="Basics.html#2492" class="InductiveConstructor"
      >monday</a
      ><a name="3110"
      >
</a
      ><a name="3111" href="Basics.html#2894" class="Function"
      >nextWeekday</a
      ><a name="3122"
      > </a
      ><a name="3123" href="Basics.html#2600" class="InductiveConstructor"
      >sunday</a
      ><a name="3129"
      >    </a
      ><a name="3133" class="Symbol"
      >=</a
      ><a name="3134"
      > </a
      ><a name="3135" href="Basics.html#2492" class="InductiveConstructor"
      >monday</a
      >

</pre>

One thing to note is that the argument and return types of
this function are explicitly declared.  Like most functional
programming languages, Agda can often figure out these types for
itself when they are not given explicitly -- i.e., it performs
_type inference_ -- but we'll include them to make reading
easier.

Having defined a function, we should check that it works on
some examples. There are actually three different ways to do this
in Agda.

First, we can use the Emacs command `C-c C-n` to evaluate a
compound expression involving `nextWeekday`. For instance, `nextWeekday
friday` should evaluate to `monday`. If you have a computer handy, this
would be an excellent moment to fire up Agda and try this for yourself.
Load this file, `Basics.lagda`, load it using `C-c C-l`, submit the
above example to Agda, and observe the result.

Second, we can record what we _expect_ the result to be in the
form of an Agda type:

<pre class="Agda">

<a name="4097" href="Basics.html#4097" class="Function"
      >test-nextWeekday</a
      ><a name="4113"
      > </a
      ><a name="4114" class="Symbol"
      >:</a
      ><a name="4115"
      > </a
      ><a name="4116" href="Basics.html#2894" class="Function"
      >nextWeekday</a
      ><a name="4127"
      > </a
      ><a name="4128" class="Symbol"
      >(</a
      ><a name="4129" href="Basics.html#2894" class="Function"
      >nextWeekday</a
      ><a name="4140"
      > </a
      ><a name="4141" href="Basics.html#2582" class="InductiveConstructor"
      >saturday</a
      ><a name="4149" class="Symbol"
      >)</a
      ><a name="4150"
      > </a
      ><a name="4151" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="4152"
      > </a
      ><a name="4153" href="Basics.html#2510" class="InductiveConstructor"
      >tuesday</a
      >

</pre>

This declaration does two things: it makes an assertion (that the second
weekday after `saturday` is `tuesday`), and it gives the assertion a name
that can be used to refer to it later.

Having made the assertion, we must also verify it. We do this by giving
a term of the above type:

<pre class="Agda">

<a name="4472" href="Basics.html#4097" class="Function"
      >test-nextWeekday</a
      ><a name="4488"
      > </a
      ><a name="4489" class="Symbol"
      >=</a
      ><a name="4490"
      > </a
      ><a name="4491" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      >

</pre>

There is no essential difference between the definition for
`test-nextWeekday` here and the definition for `nextWeekday` above,
except for the new symbol for equality `≡` and the constructor `refl`.
The details of these are not important for now (we'll come back to them in
a bit), but essentially `refl` can be read as "The assertion we've made
can be proved by observing that both sides of the equality evaluate to the
same thing, after some simplification."

Third, we can ask Agda to _compile_ some program involving our definition,
This facility is very interesting, since it gives us a way to construct
_fully certified_ programs. We'll come back to this topic in later chapters.
