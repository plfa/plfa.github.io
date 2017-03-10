---
title         : "Basics: Functional Programming in Agda"
layout        : default
hide-implicit : false
extra-script : [agda-extra-script.html]
extra-style  : [agda-extra-style.html]
---

<div class="hidden">
<!--{% raw %}--><pre class="Agda">
<a name="226" class="Keyword"
      >module</a
      ><a name="232"
      > </a
      ><a name="233" href="Basics.html#1" class="Module"
      >Basics</a
      ><a name="239"
      > </a
      ><a name="240" class="Keyword"
      >where</a
      ><a name="245"
      >

  </a
      ><a name="249" class="Keyword"
      >open</a
      ><a name="253"
      > </a
      ><a name="254" class="Keyword"
      >import</a
      ><a name="260"
      > </a
      ><a name="261" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#1" class="Module"
      >Relation.Binary.PropositionalEquality</a
      ><a name="298"
      > </a
      ><a name="299" class="Keyword"
      >using</a
      ><a name="304"
      > </a
      ><a name="305" class="Symbol"
      >(</a
      ><a name="306" href="Agda.Builtin.Equality.html#55" class="Datatype Operator"
      >_&#8801;_</a
      ><a name="309" class="Symbol"
      >;</a
      ><a name="310"
      > </a
      ><a name="311" href="Agda.Builtin.Equality.html#112" class="InductiveConstructor"
      >refl</a
      ><a name="315" class="Symbol"
      >)</a
      >
</pre><!--{% endraw %}-->
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

<!--{% raw %}--><pre class="Agda">
  <a name="2656" class="Keyword"
      >data</a
      ><a name="2660"
      > </a
      ><a name="2661" href="Basics.html#2661" class="Datatype"
      >Day</a
      ><a name="2664"
      > </a
      ><a name="2665" class="Symbol"
      >:</a
      ><a name="2666"
      > </a
      ><a name="2667" class="PrimitiveType"
      >Set</a
      ><a name="2670"
      > </a
      ><a name="2671" class="Keyword"
      >where</a
      ><a name="2676"
      >
    </a
      ><a name="2681" href="Basics.html#2681" class="InductiveConstructor"
      >monday</a
      ><a name="2687"
      >    </a
      ><a name="2691" class="Symbol"
      >:</a
      ><a name="2692"
      > </a
      ><a name="2693" href="Basics.html#2661" class="Datatype"
      >Day</a
      ><a name="2696"
      >
    </a
      ><a name="2701" href="Basics.html#2701" class="InductiveConstructor"
      >tuesday</a
      ><a name="2708"
      >   </a
      ><a name="2711" class="Symbol"
      >:</a
      ><a name="2712"
      > </a
      ><a name="2713" href="Basics.html#2661" class="Datatype"
      >Day</a
      ><a name="2716"
      >
    </a
      ><a name="2721" href="Basics.html#2721" class="InductiveConstructor"
      >wednesday</a
      ><a name="2730"
      > </a
      ><a name="2731" class="Symbol"
      >:</a
      ><a name="2732"
      > </a
      ><a name="2733" href="Basics.html#2661" class="Datatype"
      >Day</a
      ><a name="2736"
      >
    </a
      ><a name="2741" href="Basics.html#2741" class="InductiveConstructor"
      >thursday</a
      ><a name="2749"
      >  </a
      ><a name="2751" class="Symbol"
      >:</a
      ><a name="2752"
      > </a
      ><a name="2753" href="Basics.html#2661" class="Datatype"
      >Day</a
      ><a name="2756"
      >
    </a
      ><a name="2761" href="Basics.html#2761" class="InductiveConstructor"
      >friday</a
      ><a name="2767"
      >    </a
      ><a name="2771" class="Symbol"
      >:</a
      ><a name="2772"
      > </a
      ><a name="2773" href="Basics.html#2661" class="Datatype"
      >Day</a
      ><a name="2776"
      >
    </a
      ><a name="2781" href="Basics.html#2781" class="InductiveConstructor"
      >saturday</a
      ><a name="2789"
      >  </a
      ><a name="2791" class="Symbol"
      >:</a
      ><a name="2792"
      > </a
      ><a name="2793" href="Basics.html#2661" class="Datatype"
      >Day</a
      ><a name="2796"
      >
    </a
      ><a name="2801" href="Basics.html#2801" class="InductiveConstructor"
      >sunday</a
      ><a name="2807"
      >    </a
      ><a name="2811" class="Symbol"
      >:</a
      ><a name="2812"
      > </a
      ><a name="2813" href="Basics.html#2661" class="Datatype"
      >Day</a
      >
</pre><!--{% endraw %}-->

The type is called `day`, and its members are `monday`,
`tuesday`, etc.  The second and following lines of the definition
can be read "`monday` is a `day`, `tuesday` is a `day`, etc."

Having defined `day`, we can write functions that operate on
days.

<!--{% raw %}--><pre class="Agda">
  <a name="3097" href="Basics.html#3097" class="Function"
      >nextWeekday</a
      ><a name="3108"
      > </a
      ><a name="3109" class="Symbol"
      >:</a
      ><a name="3110"
      > </a
      ><a name="3111" href="Basics.html#2661" class="Datatype"
      >Day</a
      ><a name="3114"
      > </a
      ><a name="3115" class="Symbol"
      >-&gt;</a
      ><a name="3117"
      > </a
      ><a name="3118" href="Basics.html#2661" class="Datatype"
      >Day</a
      ><a name="3121"
      >
  </a
      ><a name="3124" href="Basics.html#3097" class="Function"
      >nextWeekday</a
      ><a name="3135"
      > </a
      ><a name="3136" href="Basics.html#2681" class="InductiveConstructor"
      >monday</a
      ><a name="3142"
      >    </a
      ><a name="3146" class="Symbol"
      >=</a
      ><a name="3147"
      > </a
      ><a name="3148" href="Basics.html#2701" class="InductiveConstructor"
      >tuesday</a
      ><a name="3155"
      >
  </a
      ><a name="3158" href="Basics.html#3097" class="Function"
      >nextWeekday</a
      ><a name="3169"
      > </a
      ><a name="3170" href="Basics.html#2701" class="InductiveConstructor"
      >tuesday</a
      ><a name="3177"
      >   </a
      ><a name="3180" class="Symbol"
      >=</a
      ><a name="3181"
      > </a
      ><a name="3182" href="Basics.html#2721" class="InductiveConstructor"
      >wednesday</a
      ><a name="3191"
      >
  </a
      ><a name="3194" href="Basics.html#3097" class="Function"
      >nextWeekday</a
      ><a name="3205"
      > </a
      ><a name="3206" href="Basics.html#2721" class="InductiveConstructor"
      >wednesday</a
      ><a name="3215"
      > </a
      ><a name="3216" class="Symbol"
      >=</a
      ><a name="3217"
      > </a
      ><a name="3218" href="Basics.html#2741" class="InductiveConstructor"
      >thursday</a
      ><a name="3226"
      >
  </a
      ><a name="3229" href="Basics.html#3097" class="Function"
      >nextWeekday</a
      ><a name="3240"
      > </a
      ><a name="3241" href="Basics.html#2741" class="InductiveConstructor"
      >thursday</a
      ><a name="3249"
      >  </a
      ><a name="3251" class="Symbol"
      >=</a
      ><a name="3252"
      > </a
      ><a name="3253" href="Basics.html#2761" class="InductiveConstructor"
      >friday</a
      ><a name="3259"
      >
  </a
      ><a name="3262" href="Basics.html#3097" class="Function"
      >nextWeekday</a
      ><a name="3273"
      > </a
      ><a name="3274" href="Basics.html#2761" class="InductiveConstructor"
      >friday</a
      ><a name="3280"
      >    </a
      ><a name="3284" class="Symbol"
      >=</a
      ><a name="3285"
      > </a
      ><a name="3286" href="Basics.html#2681" class="InductiveConstructor"
      >monday</a
      ><a name="3292"
      >
  </a
      ><a name="3295" href="Basics.html#3097" class="Function"
      >nextWeekday</a
      ><a name="3306"
      > </a
      ><a name="3307" href="Basics.html#2781" class="InductiveConstructor"
      >saturday</a
      ><a name="3315"
      >  </a
      ><a name="3317" class="Symbol"
      >=</a
      ><a name="3318"
      > </a
      ><a name="3319" href="Basics.html#2681" class="InductiveConstructor"
      >monday</a
      ><a name="3325"
      >
  </a
      ><a name="3328" href="Basics.html#3097" class="Function"
      >nextWeekday</a
      ><a name="3339"
      > </a
      ><a name="3340" href="Basics.html#2801" class="InductiveConstructor"
      >sunday</a
      ><a name="3346"
      >    </a
      ><a name="3350" class="Symbol"
      >=</a
      ><a name="3351"
      > </a
      ><a name="3352" href="Basics.html#2681" class="InductiveConstructor"
      >monday</a
      >
</pre><!--{% endraw %}-->

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

<!--{% raw %}--><pre class="Agda">
  <a name="4316" href="Basics.html#4316" class="Function Operator"
      >test_nextWeekday</a
      ><a name="4332"
      > </a
      ><a name="4333" class="Symbol"
      >:</a
      ><a name="4334"
      > </a
      ><a name="4335" href="Basics.html#3097" class="Function"
      >nextWeekday</a
      ><a name="4346"
      > </a
      ><a name="4347" class="Symbol"
      >(</a
      ><a name="4348" href="Basics.html#3097" class="Function"
      >nextWeekday</a
      ><a name="4359"
      > </a
      ><a name="4360" href="Basics.html#2781" class="InductiveConstructor"
      >saturday</a
      ><a name="4368" class="Symbol"
      >)</a
      ><a name="4369"
      > </a
      ><a name="4370" href="Agda.Builtin.Equality.html#55" class="Datatype Operator"
      >&#8801;</a
      ><a name="4371"
      > </a
      ><a name="4372" href="Basics.html#2701" class="InductiveConstructor"
      >tuesday</a
      >
</pre><!--{% endraw %}-->

This declaration does two things: it makes an assertion (that the second
weekday after `saturday` is `tuesday`), and it gives the assertion a name
that can be used to refer to it later.

Having made the assertion, we must also verify it. We do this by giving
a term of the above type:

<!--{% raw %}--><pre class="Agda">
  <a name="4693" href="Basics.html#4316" class="Function Operator"
      >test_nextWeekday</a
      ><a name="4709"
      > </a
      ><a name="4710" class="Symbol"
      >=</a
      ><a name="4711"
      > </a
      ><a name="4712" href="Agda.Builtin.Equality.html#112" class="InductiveConstructor"
      >refl</a
      >
</pre><!--{% endraw %}-->

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
