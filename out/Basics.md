---
title     : "Basics: Functional Programming in Agda"
layout    : page
permalink : /Basics
---

<div class="hidden">
<pre class="Agda">{% raw %}
<a name="134" class="Keyword"
      >module</a
      ><a name="140"
      > </a
      ><a name="141" href="Basics.html#1" class="Module"
      >Basics</a
      ><a name="147"
      > </a
      ><a name="148" class="Keyword"
      >where</a
      ><a name="153"
      >

  </a
      ><a name="157" class="Keyword"
      >open</a
      ><a name="161"
      > </a
      ><a name="162" class="Keyword"
      >import</a
      ><a name="168"
      > </a
      ><a name="169" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#1" class="Module"
      >Relation.Binary.PropositionalEquality</a
      ><a name="206"
      > </a
      ><a name="207" class="Keyword"
      >using</a
      ><a name="212"
      > </a
      ><a name="213" class="Symbol"
      >(</a
      ><a name="214" href="Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >_&#8801;_</a
      ><a name="217" class="Symbol"
      >;</a
      ><a name="218"
      > </a
      ><a name="219" href="Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="223" class="Symbol"
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
  <a name="2564" class="Keyword"
      >data</a
      ><a name="2568"
      > </a
      ><a name="2569" href="Basics.html#2569" class="Datatype"
      >Day</a
      ><a name="2572"
      > </a
      ><a name="2573" class="Symbol"
      >:</a
      ><a name="2574"
      > </a
      ><a name="2575" class="PrimitiveType"
      >Set</a
      ><a name="2578"
      > </a
      ><a name="2579" class="Keyword"
      >where</a
      ><a name="2584"
      >
    </a
      ><a name="2589" href="Basics.html#2589" class="InductiveConstructor"
      >monday</a
      ><a name="2595"
      >    </a
      ><a name="2599" class="Symbol"
      >:</a
      ><a name="2600"
      > </a
      ><a name="2601" href="Basics.html#2569" class="Datatype"
      >Day</a
      ><a name="2604"
      >
    </a
      ><a name="2609" href="Basics.html#2609" class="InductiveConstructor"
      >tuesday</a
      ><a name="2616"
      >   </a
      ><a name="2619" class="Symbol"
      >:</a
      ><a name="2620"
      > </a
      ><a name="2621" href="Basics.html#2569" class="Datatype"
      >Day</a
      ><a name="2624"
      >
    </a
      ><a name="2629" href="Basics.html#2629" class="InductiveConstructor"
      >wednesday</a
      ><a name="2638"
      > </a
      ><a name="2639" class="Symbol"
      >:</a
      ><a name="2640"
      > </a
      ><a name="2641" href="Basics.html#2569" class="Datatype"
      >Day</a
      ><a name="2644"
      >
    </a
      ><a name="2649" href="Basics.html#2649" class="InductiveConstructor"
      >thursday</a
      ><a name="2657"
      >  </a
      ><a name="2659" class="Symbol"
      >:</a
      ><a name="2660"
      > </a
      ><a name="2661" href="Basics.html#2569" class="Datatype"
      >Day</a
      ><a name="2664"
      >
    </a
      ><a name="2669" href="Basics.html#2669" class="InductiveConstructor"
      >friday</a
      ><a name="2675"
      >    </a
      ><a name="2679" class="Symbol"
      >:</a
      ><a name="2680"
      > </a
      ><a name="2681" href="Basics.html#2569" class="Datatype"
      >Day</a
      ><a name="2684"
      >
    </a
      ><a name="2689" href="Basics.html#2689" class="InductiveConstructor"
      >saturday</a
      ><a name="2697"
      >  </a
      ><a name="2699" class="Symbol"
      >:</a
      ><a name="2700"
      > </a
      ><a name="2701" href="Basics.html#2569" class="Datatype"
      >Day</a
      ><a name="2704"
      >
    </a
      ><a name="2709" href="Basics.html#2709" class="InductiveConstructor"
      >sunday</a
      ><a name="2715"
      >    </a
      ><a name="2719" class="Symbol"
      >:</a
      ><a name="2720"
      > </a
      ><a name="2721" href="Basics.html#2569" class="Datatype"
      >Day</a
      >
{% endraw %}</pre>

The type is called `day`, and its members are `monday`,
`tuesday`, etc.  The second and following lines of the definition
can be read "`monday` is a `day`, `tuesday` is a `day`, etc."

Having defined `day`, we can write functions that operate on
days.

<pre class="Agda">{% raw %}
  <a name="3005" href="Basics.html#3005" class="Function"
      >nextWeekday</a
      ><a name="3016"
      > </a
      ><a name="3017" class="Symbol"
      >:</a
      ><a name="3018"
      > </a
      ><a name="3019" href="Basics.html#2569" class="Datatype"
      >Day</a
      ><a name="3022"
      > </a
      ><a name="3023" class="Symbol"
      >-&gt;</a
      ><a name="3025"
      > </a
      ><a name="3026" href="Basics.html#2569" class="Datatype"
      >Day</a
      ><a name="3029"
      >
  </a
      ><a name="3032" href="Basics.html#3005" class="Function"
      >nextWeekday</a
      ><a name="3043"
      > </a
      ><a name="3044" href="Basics.html#2589" class="InductiveConstructor"
      >monday</a
      ><a name="3050"
      >    </a
      ><a name="3054" class="Symbol"
      >=</a
      ><a name="3055"
      > </a
      ><a name="3056" href="Basics.html#2609" class="InductiveConstructor"
      >tuesday</a
      ><a name="3063"
      >
  </a
      ><a name="3066" href="Basics.html#3005" class="Function"
      >nextWeekday</a
      ><a name="3077"
      > </a
      ><a name="3078" href="Basics.html#2609" class="InductiveConstructor"
      >tuesday</a
      ><a name="3085"
      >   </a
      ><a name="3088" class="Symbol"
      >=</a
      ><a name="3089"
      > </a
      ><a name="3090" href="Basics.html#2629" class="InductiveConstructor"
      >wednesday</a
      ><a name="3099"
      >
  </a
      ><a name="3102" href="Basics.html#3005" class="Function"
      >nextWeekday</a
      ><a name="3113"
      > </a
      ><a name="3114" href="Basics.html#2629" class="InductiveConstructor"
      >wednesday</a
      ><a name="3123"
      > </a
      ><a name="3124" class="Symbol"
      >=</a
      ><a name="3125"
      > </a
      ><a name="3126" href="Basics.html#2649" class="InductiveConstructor"
      >thursday</a
      ><a name="3134"
      >
  </a
      ><a name="3137" href="Basics.html#3005" class="Function"
      >nextWeekday</a
      ><a name="3148"
      > </a
      ><a name="3149" href="Basics.html#2649" class="InductiveConstructor"
      >thursday</a
      ><a name="3157"
      >  </a
      ><a name="3159" class="Symbol"
      >=</a
      ><a name="3160"
      > </a
      ><a name="3161" href="Basics.html#2669" class="InductiveConstructor"
      >friday</a
      ><a name="3167"
      >
  </a
      ><a name="3170" href="Basics.html#3005" class="Function"
      >nextWeekday</a
      ><a name="3181"
      > </a
      ><a name="3182" href="Basics.html#2669" class="InductiveConstructor"
      >friday</a
      ><a name="3188"
      >    </a
      ><a name="3192" class="Symbol"
      >=</a
      ><a name="3193"
      > </a
      ><a name="3194" href="Basics.html#2589" class="InductiveConstructor"
      >monday</a
      ><a name="3200"
      >
  </a
      ><a name="3203" href="Basics.html#3005" class="Function"
      >nextWeekday</a
      ><a name="3214"
      > </a
      ><a name="3215" href="Basics.html#2689" class="InductiveConstructor"
      >saturday</a
      ><a name="3223"
      >  </a
      ><a name="3225" class="Symbol"
      >=</a
      ><a name="3226"
      > </a
      ><a name="3227" href="Basics.html#2589" class="InductiveConstructor"
      >monday</a
      ><a name="3233"
      >
  </a
      ><a name="3236" href="Basics.html#3005" class="Function"
      >nextWeekday</a
      ><a name="3247"
      > </a
      ><a name="3248" href="Basics.html#2709" class="InductiveConstructor"
      >sunday</a
      ><a name="3254"
      >    </a
      ><a name="3258" class="Symbol"
      >=</a
      ><a name="3259"
      > </a
      ><a name="3260" href="Basics.html#2589" class="InductiveConstructor"
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
  <a name="4224" href="Basics.html#4224" class="Function Operator"
      >test_nextWeekday</a
      ><a name="4240"
      > </a
      ><a name="4241" class="Symbol"
      >:</a
      ><a name="4242"
      > </a
      ><a name="4243" href="Basics.html#3005" class="Function"
      >nextWeekday</a
      ><a name="4254"
      > </a
      ><a name="4255" class="Symbol"
      >(</a
      ><a name="4256" href="Basics.html#3005" class="Function"
      >nextWeekday</a
      ><a name="4267"
      > </a
      ><a name="4268" href="Basics.html#2689" class="InductiveConstructor"
      >saturday</a
      ><a name="4276" class="Symbol"
      >)</a
      ><a name="4277"
      > </a
      ><a name="4278" href="Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="4279"
      > </a
      ><a name="4280" href="Basics.html#2609" class="InductiveConstructor"
      >tuesday</a
      >
{% endraw %}</pre>

This declaration does two things: it makes an assertion (that the second
weekday after `saturday` is `tuesday`), and it gives the assertion a name
that can be used to refer to it later.

Having made the assertion, we must also verify it. We do this by giving
a term of the above type:

<pre class="Agda">{% raw %}
  <a name="4601" href="Basics.html#4224" class="Function Operator"
      >test_nextWeekday</a
      ><a name="4617"
      > </a
      ><a name="4618" class="Symbol"
      >=</a
      ><a name="4619"
      > </a
      ><a name="4620" href="Agda.Builtin.Equality.html#140" class="InductiveConstructor"
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
