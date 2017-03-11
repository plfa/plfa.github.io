---
title     : "Basics: Functional Programming in Agda"
layout    : page
permalink : /Basics
---

<div class="foldable">
<pre class="Agda">{% raw %}
<a name="136" class="Keyword"
      >open</a
      ><a name="140"
      > </a
      ><a name="141" class="Keyword"
      >import</a
      ><a name="147"
      > </a
      ><a name="148" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#1" class="Module"
      >Relation.Binary.PropositionalEquality</a
      ><a name="185"
      > </a
      ><a name="186" class="Keyword"
      >using</a
      ><a name="191"
      > </a
      ><a name="192" class="Symbol"
      >(</a
      ><a name="193" href="Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >_&#8801;_</a
      ><a name="196" class="Symbol"
      >;</a
      ><a name="197"
      > </a
      ><a name="198" href="Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="202" class="Symbol"
      >)</a
      >
{% endraw %}</pre>
</div>

# Basics: Functional Programming in Agda

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
*first-class* values -- i.e., values that can be passed as
arguments to other functions, returned as results, included in
data structures, etc.  The recognition that functions can be
treated as data in this way enables a host of useful and powerful
idioms.

Other common features of functional languages include *algebraic
data types* and *pattern matching*, which make it easy to
construct and manipulate rich data structures, and sophisticated
*polymorphic type systems* supporting abstraction and code reuse.
Agda shares all of these features.

This chapter introduces the most essential elements of Agda.

## Enumerated Types

One unusual aspect of Agda is that its set of built-in
features is *extremely* small. For example, instead of providing
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
a new set of data values -- a *type*.

<pre class="Agda">{% raw %}
<a name="2541" class="Keyword"
      >data</a
      ><a name="2545"
      > </a
      ><a name="2546" href="Basics.html#2546" class="Datatype"
      >Day</a
      ><a name="2549"
      > </a
      ><a name="2550" class="Symbol"
      >:</a
      ><a name="2551"
      > </a
      ><a name="2552" class="PrimitiveType"
      >Set</a
      ><a name="2555"
      > </a
      ><a name="2556" class="Keyword"
      >where</a
      ><a name="2561"
      >
  </a
      ><a name="2564" href="Basics.html#2564" class="InductiveConstructor"
      >monday</a
      ><a name="2570"
      >    </a
      ><a name="2574" class="Symbol"
      >:</a
      ><a name="2575"
      > </a
      ><a name="2576" href="Basics.html#2546" class="Datatype"
      >Day</a
      ><a name="2579"
      >
  </a
      ><a name="2582" href="Basics.html#2582" class="InductiveConstructor"
      >tuesday</a
      ><a name="2589"
      >   </a
      ><a name="2592" class="Symbol"
      >:</a
      ><a name="2593"
      > </a
      ><a name="2594" href="Basics.html#2546" class="Datatype"
      >Day</a
      ><a name="2597"
      >
  </a
      ><a name="2600" href="Basics.html#2600" class="InductiveConstructor"
      >wednesday</a
      ><a name="2609"
      > </a
      ><a name="2610" class="Symbol"
      >:</a
      ><a name="2611"
      > </a
      ><a name="2612" href="Basics.html#2546" class="Datatype"
      >Day</a
      ><a name="2615"
      >
  </a
      ><a name="2618" href="Basics.html#2618" class="InductiveConstructor"
      >thursday</a
      ><a name="2626"
      >  </a
      ><a name="2628" class="Symbol"
      >:</a
      ><a name="2629"
      > </a
      ><a name="2630" href="Basics.html#2546" class="Datatype"
      >Day</a
      ><a name="2633"
      >
  </a
      ><a name="2636" href="Basics.html#2636" class="InductiveConstructor"
      >friday</a
      ><a name="2642"
      >    </a
      ><a name="2646" class="Symbol"
      >:</a
      ><a name="2647"
      > </a
      ><a name="2648" href="Basics.html#2546" class="Datatype"
      >Day</a
      ><a name="2651"
      >
  </a
      ><a name="2654" href="Basics.html#2654" class="InductiveConstructor"
      >saturday</a
      ><a name="2662"
      >  </a
      ><a name="2664" class="Symbol"
      >:</a
      ><a name="2665"
      > </a
      ><a name="2666" href="Basics.html#2546" class="Datatype"
      >Day</a
      ><a name="2669"
      >
  </a
      ><a name="2672" href="Basics.html#2672" class="InductiveConstructor"
      >sunday</a
      ><a name="2678"
      >    </a
      ><a name="2682" class="Symbol"
      >:</a
      ><a name="2683"
      > </a
      ><a name="2684" href="Basics.html#2546" class="Datatype"
      >Day</a
      >
{% endraw %}</pre>

The type is called `day`, and its members are `monday`,
`tuesday`, etc.  The second and following lines of the definition
can be read "`monday` is a `day`, `tuesday` is a `day`, etc."

Having defined `day`, we can write functions that operate on
days.

<pre class="Agda">{% raw %}
<a name="2966" href="Basics.html#2966" class="Function"
      >nextWeekday</a
      ><a name="2977"
      > </a
      ><a name="2978" class="Symbol"
      >:</a
      ><a name="2979"
      > </a
      ><a name="2980" href="Basics.html#2546" class="Datatype"
      >Day</a
      ><a name="2983"
      > </a
      ><a name="2984" class="Symbol"
      >-&gt;</a
      ><a name="2986"
      > </a
      ><a name="2987" href="Basics.html#2546" class="Datatype"
      >Day</a
      ><a name="2990"
      >
</a
      ><a name="2991" href="Basics.html#2966" class="Function"
      >nextWeekday</a
      ><a name="3002"
      > </a
      ><a name="3003" href="Basics.html#2564" class="InductiveConstructor"
      >monday</a
      ><a name="3009"
      >    </a
      ><a name="3013" class="Symbol"
      >=</a
      ><a name="3014"
      > </a
      ><a name="3015" href="Basics.html#2582" class="InductiveConstructor"
      >tuesday</a
      ><a name="3022"
      >
</a
      ><a name="3023" href="Basics.html#2966" class="Function"
      >nextWeekday</a
      ><a name="3034"
      > </a
      ><a name="3035" href="Basics.html#2582" class="InductiveConstructor"
      >tuesday</a
      ><a name="3042"
      >   </a
      ><a name="3045" class="Symbol"
      >=</a
      ><a name="3046"
      > </a
      ><a name="3047" href="Basics.html#2600" class="InductiveConstructor"
      >wednesday</a
      ><a name="3056"
      >
</a
      ><a name="3057" href="Basics.html#2966" class="Function"
      >nextWeekday</a
      ><a name="3068"
      > </a
      ><a name="3069" href="Basics.html#2600" class="InductiveConstructor"
      >wednesday</a
      ><a name="3078"
      > </a
      ><a name="3079" class="Symbol"
      >=</a
      ><a name="3080"
      > </a
      ><a name="3081" href="Basics.html#2618" class="InductiveConstructor"
      >thursday</a
      ><a name="3089"
      >
</a
      ><a name="3090" href="Basics.html#2966" class="Function"
      >nextWeekday</a
      ><a name="3101"
      > </a
      ><a name="3102" href="Basics.html#2618" class="InductiveConstructor"
      >thursday</a
      ><a name="3110"
      >  </a
      ><a name="3112" class="Symbol"
      >=</a
      ><a name="3113"
      > </a
      ><a name="3114" href="Basics.html#2636" class="InductiveConstructor"
      >friday</a
      ><a name="3120"
      >
</a
      ><a name="3121" href="Basics.html#2966" class="Function"
      >nextWeekday</a
      ><a name="3132"
      > </a
      ><a name="3133" href="Basics.html#2636" class="InductiveConstructor"
      >friday</a
      ><a name="3139"
      >    </a
      ><a name="3143" class="Symbol"
      >=</a
      ><a name="3144"
      > </a
      ><a name="3145" href="Basics.html#2564" class="InductiveConstructor"
      >monday</a
      ><a name="3151"
      >
</a
      ><a name="3152" href="Basics.html#2966" class="Function"
      >nextWeekday</a
      ><a name="3163"
      > </a
      ><a name="3164" href="Basics.html#2654" class="InductiveConstructor"
      >saturday</a
      ><a name="3172"
      >  </a
      ><a name="3174" class="Symbol"
      >=</a
      ><a name="3175"
      > </a
      ><a name="3176" href="Basics.html#2564" class="InductiveConstructor"
      >monday</a
      ><a name="3182"
      >
</a
      ><a name="3183" href="Basics.html#2966" class="Function"
      >nextWeekday</a
      ><a name="3194"
      > </a
      ><a name="3195" href="Basics.html#2672" class="InductiveConstructor"
      >sunday</a
      ><a name="3201"
      >    </a
      ><a name="3205" class="Symbol"
      >=</a
      ><a name="3206"
      > </a
      ><a name="3207" href="Basics.html#2564" class="InductiveConstructor"
      >monday</a
      >
{% endraw %}</pre>

One thing to note is that the argument and return types of
this function are explicitly declared.  Like most functional
programming languages, Agda can often figure out these types for
itself when they are not given explicitly -- i.e., it performs
*type inference* -- but we'll include them to make reading
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

Second, we can record what we *expect* the result to be in the
form of an Agda type:

<pre class="Agda">{% raw %}
<a name="4169" href="Basics.html#4169" class="Function Operator"
      >test_nextWeekday</a
      ><a name="4185"
      > </a
      ><a name="4186" class="Symbol"
      >:</a
      ><a name="4187"
      > </a
      ><a name="4188" href="Basics.html#2966" class="Function"
      >nextWeekday</a
      ><a name="4199"
      > </a
      ><a name="4200" class="Symbol"
      >(</a
      ><a name="4201" href="Basics.html#2966" class="Function"
      >nextWeekday</a
      ><a name="4212"
      > </a
      ><a name="4213" href="Basics.html#2654" class="InductiveConstructor"
      >saturday</a
      ><a name="4221" class="Symbol"
      >)</a
      ><a name="4222"
      > </a
      ><a name="4223" href="Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="4224"
      > </a
      ><a name="4225" href="Basics.html#2582" class="InductiveConstructor"
      >tuesday</a
      >
{% endraw %}</pre>

This declaration does two things: it makes an assertion (that the second
weekday after `saturday` is `tuesday`), and it gives the assertion a name
that can be used to refer to it later.

Having made the assertion, we must also verify it. We do this by giving
a term of the above type:

<pre class="Agda">{% raw %}
<a name="4544" href="Basics.html#4169" class="Function Operator"
      >test_nextWeekday</a
      ><a name="4560"
      > </a
      ><a name="4561" class="Symbol"
      >=</a
      ><a name="4562"
      > </a
      ><a name="4563" href="Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      >
{% endraw %}</pre>

There is no essential difference between the definition for
`test_nextWeekday` here and the definition for `nextWeekday` above,
except for the new symbol for equality `≡` and the constructor `refl`.
The details of these are not important for now (we'll come back to them in
a bit), but essentially `refl` can be read as "The assertion we've made
can be proved by observing that both sides of the equality evaluate to the
same thing, after some simplification."

Third, we can ask Agda to *compile* some program involving our definition,
This facility is very interesting, since it gives us a way to construct
*fully certified* programs. We'll come back to this topic in later chapters.
