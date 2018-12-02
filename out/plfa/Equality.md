---
src       : src/plfa/Equality.lagda
title     : "Equality: Equality and equational reasoning"
layout    : page
prev      : /Relations/
permalink : /Equality/
next      : /Isomorphism/
---

<pre class="Agda">{% raw %}<a id="171" class="Keyword">module</a> <a id="178" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}" class="Module">plfa.Equality</a> <a id="192" class="Keyword">where</a>{% endraw %}</pre>

Much of our reasoning has involved equality.  Given two terms `M`
and `N`, both of type `A`, we write `M ≡ N` to assert that `M` and `N`
are interchangeable.  So far we have treated equality as a primitive,
here we show how to define it as an inductive datatype.


## Imports

This chapter has no imports.  Every chapter in this book, and nearly
every module in the Agda standard library, imports equality.
Since we define equality here, any import would create a conflict.


## Equality

We declare equality as follows.
<pre class="Agda">{% raw %}<a id="744" class="Keyword">data</a> <a id="_≡_"></a><a id="749" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#749" class="Datatype Operator">_≡_</a> <a id="753" class="Symbol">{</a><a id="754" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#754" class="Bound">A</a> <a id="756" class="Symbol">:</a> <a id="758" class="PrimitiveType">Set</a><a id="761" class="Symbol">}</a> <a id="763" class="Symbol">(</a><a id="764" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#764" class="Bound">x</a> <a id="766" class="Symbol">:</a> <a id="768" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#754" class="Bound">A</a><a id="769" class="Symbol">)</a> <a id="771" class="Symbol">:</a> <a id="773" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#754" class="Bound">A</a> <a id="775" class="Symbol">→</a> <a id="777" class="PrimitiveType">Set</a> <a id="781" class="Keyword">where</a>
  <a id="_≡_.refl"></a><a id="789" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#789" class="InductiveConstructor">refl</a> <a id="794" class="Symbol">:</a> <a id="796" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#764" class="Bound">x</a> <a id="798" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#749" class="Datatype Operator">≡</a> <a id="800" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#764" class="Bound">x</a>{% endraw %}</pre>
In other words, for any type `A` and for any `x` of type `A`, the
constructor `refl` provides evidence that `x ≡ x`. Hence, every value
is equal to itself, and we have no other way of showing values
equal.  The definition features an asymmetry, in that the
first argument to `_≡_` is given by the parameter `x : A`, while the
second is given by an index in `A → Set`.  This follows our policy
of using parameters wherever possible.  The first argument to `_≡_`
can be a parameter because it doesn't vary, while the second must be
an index, so it can be required to be equal to the first.

We declare the precedence of equality as follows.
<pre class="Agda">{% raw %}<a id="1465" class="Keyword">infix</a> <a id="1471" class="Number">4</a> <a id="1473" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#749" class="Datatype Operator">_≡_</a>{% endraw %}</pre>
We set the precedence of `_≡_` at level 4, the same as `_≤_`,
which means it binds less tightly than any arithmetic operator.
It associates neither to left nor right; writing `x ≡ y ≡ z`
is illegal.


## Equality is an equivalence relation

An equivalence relation is one which is reflexive, symmetric, and transitive.
Reflexivity is built-in to the definition of equality, via the
constructor `refl`.  It is straightforward to show symmetry.
<pre class="Agda">{% raw %}<a id="sym"></a><a id="1944" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#1944" class="Function">sym</a> <a id="1948" class="Symbol">:</a> <a id="1950" class="Symbol">∀</a> <a id="1952" class="Symbol">{</a><a id="1953" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#1953" class="Bound">A</a> <a id="1955" class="Symbol">:</a> <a id="1957" class="PrimitiveType">Set</a><a id="1960" class="Symbol">}</a> <a id="1962" class="Symbol">{</a><a id="1963" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#1963" class="Bound">x</a> <a id="1965" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#1965" class="Bound">y</a> <a id="1967" class="Symbol">:</a> <a id="1969" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#1953" class="Bound">A</a><a id="1970" class="Symbol">}</a>
  <a id="1974" class="Symbol">→</a> <a id="1976" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#1963" class="Bound">x</a> <a id="1978" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#749" class="Datatype Operator">≡</a> <a id="1980" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#1965" class="Bound">y</a>
    <a id="1986" class="Comment">-----</a>
  <a id="1994" class="Symbol">→</a> <a id="1996" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#1965" class="Bound">y</a> <a id="1998" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#749" class="Datatype Operator">≡</a> <a id="2000" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#1963" class="Bound">x</a>
<a id="2002" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#1944" class="Function">sym</a> <a id="2006" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#789" class="InductiveConstructor">refl</a> <a id="2011" class="Symbol">=</a> <a id="2013" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#789" class="InductiveConstructor">refl</a>{% endraw %}</pre>
How does this proof work? The argument to `sym` has type `x ≡ y`, but
on the left-hand side of the equation the argument has been
instantiated to the pattern `refl`, which requires that `x` and `y`
are the same.  Hence, for the right-hand side of the equation we need
a term of type `x ≡ x`, and `refl` will do.

It is instructive to develop `sym` interactively.  To start, we supply
a variable for the argument on the left, and a hole for the body on
the right:

    sym : ∀ {A : Set} {x y : A}
      → x ≡ y
        -----
      → y ≡ x
    sym e = {! !}

If we go into the hole and type `C-c C-,` then Agda reports:

    Goal: .y ≡ .x
    ————————————————————————————————————————————————————————————
    e  : .x ≡ .y
    .y : .A
    .x : .A
    .A : Set

If in the hole we type `C-c C-c e` then Agda will instantiate `e` to
all possible constructors, with one equation for each. There is only
one possible constructor:

    sym : ∀ {A : Set} {x y : A}
      → x ≡ y
        -----
      → y ≡ x
    sym refl = {! !}

If we go into the hole again and type `C-c C-,` then Agda now reports:

     Goal: .x ≡ .x
     ————————————————————————————————————————————————————————————
     .x : .A
     .A : Set

This is the key step---Agda has worked out that `x` and `y` must be
the same to match the pattern `refl`!

Finally, if we go back into the hole and type `C-c C-r` it will
instantiate the hole with the one constructor that yields a value of
the expected type.

    sym : ∀ {A : Set} {x y : A}
      → x ≡ y
        -----
      → y ≡ x
    sym refl = refl

This completes the definition as given above.

Transitivity is equally straightforward.
<pre class="Agda">{% raw %}<a id="trans"></a><a id="3688" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#3688" class="Function">trans</a> <a id="3694" class="Symbol">:</a> <a id="3696" class="Symbol">∀</a> <a id="3698" class="Symbol">{</a><a id="3699" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#3699" class="Bound">A</a> <a id="3701" class="Symbol">:</a> <a id="3703" class="PrimitiveType">Set</a><a id="3706" class="Symbol">}</a> <a id="3708" class="Symbol">{</a><a id="3709" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#3709" class="Bound">x</a> <a id="3711" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#3711" class="Bound">y</a> <a id="3713" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#3713" class="Bound">z</a> <a id="3715" class="Symbol">:</a> <a id="3717" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#3699" class="Bound">A</a><a id="3718" class="Symbol">}</a>
  <a id="3722" class="Symbol">→</a> <a id="3724" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#3709" class="Bound">x</a> <a id="3726" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#749" class="Datatype Operator">≡</a> <a id="3728" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#3711" class="Bound">y</a>
  <a id="3732" class="Symbol">→</a> <a id="3734" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#3711" class="Bound">y</a> <a id="3736" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#749" class="Datatype Operator">≡</a> <a id="3738" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#3713" class="Bound">z</a>
    <a id="3744" class="Comment">-----</a>
  <a id="3752" class="Symbol">→</a> <a id="3754" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#3709" class="Bound">x</a> <a id="3756" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#749" class="Datatype Operator">≡</a> <a id="3758" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#3713" class="Bound">z</a>
<a id="3760" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#3688" class="Function">trans</a> <a id="3766" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#789" class="InductiveConstructor">refl</a> <a id="3771" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#789" class="InductiveConstructor">refl</a>  <a id="3777" class="Symbol">=</a>  <a id="3780" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#789" class="InductiveConstructor">refl</a>{% endraw %}</pre>
Again, a useful exercise is to carry out an interactive development,
checking how Agda's knowledge changes as each of the two arguments is
instantiated.

## Congruence and substitution {#cong}

Equality satisfies _congruence_.  If two terms are equal,
they remain so after the same function is applied to both.
<pre class="Agda">{% raw %}<a id="cong"></a><a id="4120" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4120" class="Function">cong</a> <a id="4125" class="Symbol">:</a> <a id="4127" class="Symbol">∀</a> <a id="4129" class="Symbol">{</a><a id="4130" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4130" class="Bound">A</a> <a id="4132" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4132" class="Bound">B</a> <a id="4134" class="Symbol">:</a> <a id="4136" class="PrimitiveType">Set</a><a id="4139" class="Symbol">}</a> <a id="4141" class="Symbol">(</a><a id="4142" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4142" class="Bound">f</a> <a id="4144" class="Symbol">:</a> <a id="4146" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4130" class="Bound">A</a> <a id="4148" class="Symbol">→</a> <a id="4150" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4132" class="Bound">B</a><a id="4151" class="Symbol">)</a> <a id="4153" class="Symbol">{</a><a id="4154" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4154" class="Bound">x</a> <a id="4156" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4156" class="Bound">y</a> <a id="4158" class="Symbol">:</a> <a id="4160" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4130" class="Bound">A</a><a id="4161" class="Symbol">}</a>
  <a id="4165" class="Symbol">→</a> <a id="4167" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4154" class="Bound">x</a> <a id="4169" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#749" class="Datatype Operator">≡</a> <a id="4171" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4156" class="Bound">y</a>
    <a id="4177" class="Comment">---------</a>
  <a id="4189" class="Symbol">→</a> <a id="4191" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4142" class="Bound">f</a> <a id="4193" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4154" class="Bound">x</a> <a id="4195" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#749" class="Datatype Operator">≡</a> <a id="4197" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4142" class="Bound">f</a> <a id="4199" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4156" class="Bound">y</a>
<a id="4201" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4120" class="Function">cong</a> <a id="4206" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4206" class="Bound">f</a> <a id="4208" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#789" class="InductiveConstructor">refl</a>  <a id="4214" class="Symbol">=</a>  <a id="4217" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#789" class="InductiveConstructor">refl</a>{% endraw %}</pre>

Congruence of functions with two arguments is similar.
<pre class="Agda">{% raw %}<a id="cong₂"></a><a id="4302" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4302" class="Function">cong₂</a> <a id="4308" class="Symbol">:</a> <a id="4310" class="Symbol">∀</a> <a id="4312" class="Symbol">{</a><a id="4313" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4313" class="Bound">A</a> <a id="4315" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4315" class="Bound">B</a> <a id="4317" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4317" class="Bound">C</a> <a id="4319" class="Symbol">:</a> <a id="4321" class="PrimitiveType">Set</a><a id="4324" class="Symbol">}</a> <a id="4326" class="Symbol">(</a><a id="4327" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4327" class="Bound">f</a> <a id="4329" class="Symbol">:</a> <a id="4331" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4313" class="Bound">A</a> <a id="4333" class="Symbol">→</a> <a id="4335" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4315" class="Bound">B</a> <a id="4337" class="Symbol">→</a> <a id="4339" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4317" class="Bound">C</a><a id="4340" class="Symbol">)</a> <a id="4342" class="Symbol">{</a><a id="4343" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4343" class="Bound">u</a> <a id="4345" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4345" class="Bound">x</a> <a id="4347" class="Symbol">:</a> <a id="4349" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4313" class="Bound">A</a><a id="4350" class="Symbol">}</a> <a id="4352" class="Symbol">{</a><a id="4353" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4353" class="Bound">v</a> <a id="4355" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4355" class="Bound">y</a> <a id="4357" class="Symbol">:</a> <a id="4359" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4315" class="Bound">B</a><a id="4360" class="Symbol">}</a>
  <a id="4364" class="Symbol">→</a> <a id="4366" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4343" class="Bound">u</a> <a id="4368" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#749" class="Datatype Operator">≡</a> <a id="4370" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4345" class="Bound">x</a>
  <a id="4374" class="Symbol">→</a> <a id="4376" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4353" class="Bound">v</a> <a id="4378" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#749" class="Datatype Operator">≡</a> <a id="4380" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4355" class="Bound">y</a>
    <a id="4386" class="Comment">-------------</a>
  <a id="4402" class="Symbol">→</a> <a id="4404" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4327" class="Bound">f</a> <a id="4406" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4343" class="Bound">u</a> <a id="4408" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4353" class="Bound">v</a> <a id="4410" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#749" class="Datatype Operator">≡</a> <a id="4412" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4327" class="Bound">f</a> <a id="4414" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4345" class="Bound">x</a> <a id="4416" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4355" class="Bound">y</a>
<a id="4418" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4302" class="Function">cong₂</a> <a id="4424" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4424" class="Bound">f</a> <a id="4426" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#789" class="InductiveConstructor">refl</a> <a id="4431" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#789" class="InductiveConstructor">refl</a>  <a id="4437" class="Symbol">=</a>  <a id="4440" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#789" class="InductiveConstructor">refl</a>{% endraw %}</pre>

Equality is also a congruence in the function position of an application.
If two functions are equal, then applying them to the same term
yields equal terms.
<pre class="Agda">{% raw %}<a id="cong-app"></a><a id="4628" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4628" class="Function">cong-app</a> <a id="4637" class="Symbol">:</a> <a id="4639" class="Symbol">∀</a> <a id="4641" class="Symbol">{</a><a id="4642" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4642" class="Bound">A</a> <a id="4644" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4644" class="Bound">B</a> <a id="4646" class="Symbol">:</a> <a id="4648" class="PrimitiveType">Set</a><a id="4651" class="Symbol">}</a> <a id="4653" class="Symbol">{</a><a id="4654" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4654" class="Bound">f</a> <a id="4656" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4656" class="Bound">g</a> <a id="4658" class="Symbol">:</a> <a id="4660" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4642" class="Bound">A</a> <a id="4662" class="Symbol">→</a> <a id="4664" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4644" class="Bound">B</a><a id="4665" class="Symbol">}</a>
  <a id="4669" class="Symbol">→</a> <a id="4671" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4654" class="Bound">f</a> <a id="4673" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#749" class="Datatype Operator">≡</a> <a id="4675" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4656" class="Bound">g</a>
    <a id="4681" class="Comment">---------------------</a>
  <a id="4705" class="Symbol">→</a> <a id="4707" class="Symbol">∀</a> <a id="4709" class="Symbol">(</a><a id="4710" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4710" class="Bound">x</a> <a id="4712" class="Symbol">:</a> <a id="4714" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4642" class="Bound">A</a><a id="4715" class="Symbol">)</a> <a id="4717" class="Symbol">→</a> <a id="4719" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4654" class="Bound">f</a> <a id="4721" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4710" class="Bound">x</a> <a id="4723" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#749" class="Datatype Operator">≡</a> <a id="4725" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4656" class="Bound">g</a> <a id="4727" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4710" class="Bound">x</a>
<a id="4729" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4628" class="Function">cong-app</a> <a id="4738" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#789" class="InductiveConstructor">refl</a> <a id="4743" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4743" class="Bound">x</a> <a id="4745" class="Symbol">=</a> <a id="4747" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#789" class="InductiveConstructor">refl</a>{% endraw %}</pre>

Equality also satisfies *substitution*.
If two values are equal and a predicate holds of the first then it also holds of the second.
<pre class="Agda">{% raw %}<a id="subst"></a><a id="4910" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4910" class="Function">subst</a> <a id="4916" class="Symbol">:</a> <a id="4918" class="Symbol">∀</a> <a id="4920" class="Symbol">{</a><a id="4921" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4921" class="Bound">A</a> <a id="4923" class="Symbol">:</a> <a id="4925" class="PrimitiveType">Set</a><a id="4928" class="Symbol">}</a> <a id="4930" class="Symbol">{</a><a id="4931" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4931" class="Bound">x</a> <a id="4933" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4933" class="Bound">y</a> <a id="4935" class="Symbol">:</a> <a id="4937" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4921" class="Bound">A</a><a id="4938" class="Symbol">}</a> <a id="4940" class="Symbol">(</a><a id="4941" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4941" class="Bound">P</a> <a id="4943" class="Symbol">:</a> <a id="4945" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4921" class="Bound">A</a> <a id="4947" class="Symbol">→</a> <a id="4949" class="PrimitiveType">Set</a><a id="4952" class="Symbol">)</a>
  <a id="4956" class="Symbol">→</a> <a id="4958" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4931" class="Bound">x</a> <a id="4960" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#749" class="Datatype Operator">≡</a> <a id="4962" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4933" class="Bound">y</a>
    <a id="4968" class="Comment">---------</a>
  <a id="4980" class="Symbol">→</a> <a id="4982" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4941" class="Bound">P</a> <a id="4984" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4931" class="Bound">x</a> <a id="4986" class="Symbol">→</a> <a id="4988" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4941" class="Bound">P</a> <a id="4990" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4933" class="Bound">y</a>
<a id="4992" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4910" class="Function">subst</a> <a id="4998" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4998" class="Bound">P</a> <a id="5000" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#789" class="InductiveConstructor">refl</a> <a id="5005" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5005" class="Bound">px</a> <a id="5008" class="Symbol">=</a> <a id="5010" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5005" class="Bound">px</a>{% endraw %}</pre>


## Chains of equations

Here we show how to support reasoning with chains of equations, as
used throughout the book.  We package the declarations into a module,
named `≡-Reasoning`, to match the format used in Agda's standard
library.
<pre class="Agda">{% raw %}<a id="5274" class="Keyword">module</a> <a id="≡-Reasoning"></a><a id="5281" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5281" class="Module">≡-Reasoning</a> <a id="5293" class="Symbol">{</a><a id="5294" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5294" class="Bound">A</a> <a id="5296" class="Symbol">:</a> <a id="5298" class="PrimitiveType">Set</a><a id="5301" class="Symbol">}</a> <a id="5303" class="Keyword">where</a>

  <a id="5312" class="Keyword">infix</a>  <a id="5319" class="Number">1</a> <a id="5321" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5369" class="Function Operator">begin_</a>
  <a id="5330" class="Keyword">infixr</a> <a id="5337" class="Number">2</a> <a id="5339" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5449" class="Function Operator">_≡⟨⟩_</a> <a id="5345" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5534" class="Function Operator">_≡⟨_⟩_</a>
  <a id="5354" class="Keyword">infix</a>  <a id="5361" class="Number">3</a> <a id="5363" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5649" class="Function Operator">_∎</a>

  <a id="≡-Reasoning.begin_"></a><a id="5369" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5369" class="Function Operator">begin_</a> <a id="5376" class="Symbol">:</a> <a id="5378" class="Symbol">∀</a> <a id="5380" class="Symbol">{</a><a id="5381" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5381" class="Bound">x</a> <a id="5383" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5383" class="Bound">y</a> <a id="5385" class="Symbol">:</a> <a id="5387" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5294" class="Bound">A</a><a id="5388" class="Symbol">}</a>
    <a id="5394" class="Symbol">→</a> <a id="5396" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5381" class="Bound">x</a> <a id="5398" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#749" class="Datatype Operator">≡</a> <a id="5400" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5383" class="Bound">y</a>
      <a id="5408" class="Comment">-----</a>
    <a id="5418" class="Symbol">→</a> <a id="5420" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5381" class="Bound">x</a> <a id="5422" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#749" class="Datatype Operator">≡</a> <a id="5424" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5383" class="Bound">y</a>
  <a id="5428" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5369" class="Function Operator">begin</a> <a id="5434" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5434" class="Bound">x≡y</a>  <a id="5439" class="Symbol">=</a>  <a id="5442" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5434" class="Bound">x≡y</a>

  <a id="≡-Reasoning._≡⟨⟩_"></a><a id="5449" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5449" class="Function Operator">_≡⟨⟩_</a> <a id="5455" class="Symbol">:</a> <a id="5457" class="Symbol">∀</a> <a id="5459" class="Symbol">(</a><a id="5460" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5460" class="Bound">x</a> <a id="5462" class="Symbol">:</a> <a id="5464" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5294" class="Bound">A</a><a id="5465" class="Symbol">)</a> <a id="5467" class="Symbol">{</a><a id="5468" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5468" class="Bound">y</a> <a id="5470" class="Symbol">:</a> <a id="5472" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5294" class="Bound">A</a><a id="5473" class="Symbol">}</a>
    <a id="5479" class="Symbol">→</a> <a id="5481" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5460" class="Bound">x</a> <a id="5483" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#749" class="Datatype Operator">≡</a> <a id="5485" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5468" class="Bound">y</a>
      <a id="5493" class="Comment">-----</a>
    <a id="5503" class="Symbol">→</a> <a id="5505" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5460" class="Bound">x</a> <a id="5507" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#749" class="Datatype Operator">≡</a> <a id="5509" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5468" class="Bound">y</a>
  <a id="5513" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5513" class="Bound">x</a> <a id="5515" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5449" class="Function Operator">≡⟨⟩</a> <a id="5519" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5519" class="Bound">x≡y</a>  <a id="5524" class="Symbol">=</a>  <a id="5527" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5519" class="Bound">x≡y</a>

  <a id="≡-Reasoning._≡⟨_⟩_"></a><a id="5534" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5534" class="Function Operator">_≡⟨_⟩_</a> <a id="5541" class="Symbol">:</a> <a id="5543" class="Symbol">∀</a> <a id="5545" class="Symbol">(</a><a id="5546" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5546" class="Bound">x</a> <a id="5548" class="Symbol">:</a> <a id="5550" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5294" class="Bound">A</a><a id="5551" class="Symbol">)</a> <a id="5553" class="Symbol">{</a><a id="5554" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5554" class="Bound">y</a> <a id="5556" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5556" class="Bound">z</a> <a id="5558" class="Symbol">:</a> <a id="5560" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5294" class="Bound">A</a><a id="5561" class="Symbol">}</a>
    <a id="5567" class="Symbol">→</a> <a id="5569" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5546" class="Bound">x</a> <a id="5571" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#749" class="Datatype Operator">≡</a> <a id="5573" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5554" class="Bound">y</a>
    <a id="5579" class="Symbol">→</a> <a id="5581" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5554" class="Bound">y</a> <a id="5583" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#749" class="Datatype Operator">≡</a> <a id="5585" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5556" class="Bound">z</a>
      <a id="5593" class="Comment">-----</a>
    <a id="5603" class="Symbol">→</a> <a id="5605" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5546" class="Bound">x</a> <a id="5607" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#749" class="Datatype Operator">≡</a> <a id="5609" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5556" class="Bound">z</a>
  <a id="5613" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5613" class="Bound">x</a> <a id="5615" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5534" class="Function Operator">≡⟨</a> <a id="5618" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5618" class="Bound">x≡y</a> <a id="5622" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5534" class="Function Operator">⟩</a> <a id="5624" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5624" class="Bound">y≡z</a>  <a id="5629" class="Symbol">=</a>  <a id="5632" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#3688" class="Function">trans</a> <a id="5638" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5618" class="Bound">x≡y</a> <a id="5642" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5624" class="Bound">y≡z</a>

  <a id="≡-Reasoning._∎"></a><a id="5649" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5649" class="Function Operator">_∎</a> <a id="5652" class="Symbol">:</a> <a id="5654" class="Symbol">∀</a> <a id="5656" class="Symbol">(</a><a id="5657" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5657" class="Bound">x</a> <a id="5659" class="Symbol">:</a> <a id="5661" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5294" class="Bound">A</a><a id="5662" class="Symbol">)</a>
      <a id="5670" class="Comment">-----</a>
    <a id="5680" class="Symbol">→</a> <a id="5682" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5657" class="Bound">x</a> <a id="5684" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#749" class="Datatype Operator">≡</a> <a id="5686" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5657" class="Bound">x</a>
  <a id="5690" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5690" class="Bound">x</a> <a id="5692" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5649" class="Function Operator">∎</a>  <a id="5695" class="Symbol">=</a>  <a id="5698" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#789" class="InductiveConstructor">refl</a>

<a id="5704" class="Keyword">open</a> <a id="5709" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5281" class="Module">≡-Reasoning</a>{% endraw %}</pre>
This is our first use of a nested module. It consists of the keyword
`module` followed by the module name and any parameters, explicit or
implicit, the keyword `where`, and the contents of the module indented.
Modules may contain any sort of declaration, including other nested modules.
Nested modules are similar to the top-level modules that constitute
each chapter of this book, save that the body of a top-level module
need not be indented.  Opening the module makes all of the definitions
available in the current environment.

As an example, let's look at a proof of transitivity
as a chain of equations.
<pre class="Agda">{% raw %}<a id="trans′"></a><a id="6356" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#6356" class="Function">trans′</a> <a id="6363" class="Symbol">:</a> <a id="6365" class="Symbol">∀</a> <a id="6367" class="Symbol">{</a><a id="6368" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#6368" class="Bound">A</a> <a id="6370" class="Symbol">:</a> <a id="6372" class="PrimitiveType">Set</a><a id="6375" class="Symbol">}</a> <a id="6377" class="Symbol">{</a><a id="6378" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#6378" class="Bound">x</a> <a id="6380" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#6380" class="Bound">y</a> <a id="6382" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#6382" class="Bound">z</a> <a id="6384" class="Symbol">:</a> <a id="6386" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#6368" class="Bound">A</a><a id="6387" class="Symbol">}</a>
  <a id="6391" class="Symbol">→</a> <a id="6393" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#6378" class="Bound">x</a> <a id="6395" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#749" class="Datatype Operator">≡</a> <a id="6397" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#6380" class="Bound">y</a>
  <a id="6401" class="Symbol">→</a> <a id="6403" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#6380" class="Bound">y</a> <a id="6405" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#749" class="Datatype Operator">≡</a> <a id="6407" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#6382" class="Bound">z</a>
    <a id="6413" class="Comment">-----</a>
  <a id="6421" class="Symbol">→</a> <a id="6423" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#6378" class="Bound">x</a> <a id="6425" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#749" class="Datatype Operator">≡</a> <a id="6427" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#6382" class="Bound">z</a>
<a id="6429" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#6356" class="Function">trans′</a> <a id="6436" class="Symbol">{</a><a id="6437" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#6437" class="Bound">A</a><a id="6438" class="Symbol">}</a> <a id="6440" class="Symbol">{</a><a id="6441" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#6441" class="Bound">x</a><a id="6442" class="Symbol">}</a> <a id="6444" class="Symbol">{</a><a id="6445" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#6445" class="Bound">y</a><a id="6446" class="Symbol">}</a> <a id="6448" class="Symbol">{</a><a id="6449" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#6449" class="Bound">z</a><a id="6450" class="Symbol">}</a> <a id="6452" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#6452" class="Bound">x≡y</a> <a id="6456" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#6456" class="Bound">y≡z</a> <a id="6460" class="Symbol">=</a>
  <a id="6464" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5369" class="Function Operator">begin</a>
    <a id="6474" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#6441" class="Bound">x</a>
  <a id="6478" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5534" class="Function Operator">≡⟨</a> <a id="6481" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#6452" class="Bound">x≡y</a> <a id="6485" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5534" class="Function Operator">⟩</a>
    <a id="6491" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#6445" class="Bound">y</a>
  <a id="6495" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5534" class="Function Operator">≡⟨</a> <a id="6498" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#6456" class="Bound">y≡z</a> <a id="6502" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5534" class="Function Operator">⟩</a>
    <a id="6508" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#6449" class="Bound">z</a>
  <a id="6512" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5649" class="Function Operator">∎</a>{% endraw %}</pre>
According to the fixity declarations, the body parses as follows:

    begin (x ≡⟨ x≡y ⟩ (y ≡⟨ y≡z ⟩ (z ∎)))

The application of `begin` is purely cosmetic, as it simply returns
its argument.  That argument consists of `_≡⟨_⟩_` applied to `x`,
`x≡y`, and `y ≡⟨ y≡z ⟩ (z ∎)`.  The first argument is a term, `x`,
while the second and third arguments are both proofs of equations, in
particular proofs of `x ≡ y` and `y ≡ z` respectively, which are
combined by `trans` in the body of `_≡⟨_⟩_` to yield a proof of `x ≡
z`.  The proof of `y ≡ z` consists of `_≡⟨_⟩_` applied to `y`, `y≡z`,
and `z ∎`.  The first argument is a term, `y`, while the second and
third arguments are both proofs of equations, in particular proofs of
`y ≡ z` and `z ≡ z` respectively, which are combined by `trans` in the
body of `_≡⟨_⟩_` to yield a proof of `y ≡ z`.  Finally, the proof of
`z ≡ z` consists of `_∎` applied to the term `z`, which yields `refl`.
After simplification, the body is equivalent to the term:

    trans x≡y (trans y≡z refl)

We could replace any use of a chain of equations by a chain of
applications of `trans`; the result would be more compact but harder
to read.  The trick behind `∎` means that a chain of equalities
simplifies to a chain of applications of `trans` than ends in `trans e
refl`, where `e` is a term that proves some equality, even though `e`
alone would do.


## Chains of equations, another example

As a second example of chains of equations, we repeat the proof that addition
is commutative.  We first repeat the definitions of naturals and addition.
We cannot import them because (as noted at the beginning of this chapter)
it would cause a conflict.
<pre class="Agda">{% raw %}<a id="8213" class="Keyword">data</a> <a id="ℕ"></a><a id="8218" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8218" class="Datatype">ℕ</a> <a id="8220" class="Symbol">:</a> <a id="8222" class="PrimitiveType">Set</a> <a id="8226" class="Keyword">where</a>
  <a id="ℕ.zero"></a><a id="8234" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8234" class="InductiveConstructor">zero</a> <a id="8239" class="Symbol">:</a> <a id="8241" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8218" class="Datatype">ℕ</a>
  <a id="ℕ.suc"></a><a id="8245" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8245" class="InductiveConstructor">suc</a>  <a id="8250" class="Symbol">:</a> <a id="8252" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8218" class="Datatype">ℕ</a> <a id="8254" class="Symbol">→</a> <a id="8256" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8218" class="Datatype">ℕ</a>

<a id="_+_"></a><a id="8259" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8259" class="Function Operator">_+_</a> <a id="8263" class="Symbol">:</a> <a id="8265" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8218" class="Datatype">ℕ</a> <a id="8267" class="Symbol">→</a> <a id="8269" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8218" class="Datatype">ℕ</a> <a id="8271" class="Symbol">→</a> <a id="8273" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8218" class="Datatype">ℕ</a>
<a id="8275" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8234" class="InductiveConstructor">zero</a>    <a id="8283" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8259" class="Function Operator">+</a> <a id="8285" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8285" class="Bound">n</a>  <a id="8288" class="Symbol">=</a>  <a id="8291" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8285" class="Bound">n</a>
<a id="8293" class="Symbol">(</a><a id="8294" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8245" class="InductiveConstructor">suc</a> <a id="8298" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8298" class="Bound">m</a><a id="8299" class="Symbol">)</a> <a id="8301" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8259" class="Function Operator">+</a> <a id="8303" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8303" class="Bound">n</a>  <a id="8306" class="Symbol">=</a>  <a id="8309" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8245" class="InductiveConstructor">suc</a> <a id="8313" class="Symbol">(</a><a id="8314" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8298" class="Bound">m</a> <a id="8316" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8259" class="Function Operator">+</a> <a id="8318" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8303" class="Bound">n</a><a id="8319" class="Symbol">)</a>{% endraw %}</pre>

To save space we postulate (rather than prove in full) two lemmas.
<pre class="Agda">{% raw %}<a id="8413" class="Keyword">postulate</a>
  <a id="+-identity"></a><a id="8425" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8425" class="Postulate">+-identity</a> <a id="8436" class="Symbol">:</a> <a id="8438" class="Symbol">∀</a> <a id="8440" class="Symbol">(</a><a id="8441" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8441" class="Bound">m</a> <a id="8443" class="Symbol">:</a> <a id="8445" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8218" class="Datatype">ℕ</a><a id="8446" class="Symbol">)</a> <a id="8448" class="Symbol">→</a> <a id="8450" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8441" class="Bound">m</a> <a id="8452" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8259" class="Function Operator">+</a> <a id="8454" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8234" class="InductiveConstructor">zero</a> <a id="8459" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#749" class="Datatype Operator">≡</a> <a id="8461" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8441" class="Bound">m</a>
  <a id="+-suc"></a><a id="8465" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8465" class="Postulate">+-suc</a> <a id="8471" class="Symbol">:</a> <a id="8473" class="Symbol">∀</a> <a id="8475" class="Symbol">(</a><a id="8476" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8476" class="Bound">m</a> <a id="8478" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8478" class="Bound">n</a> <a id="8480" class="Symbol">:</a> <a id="8482" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8218" class="Datatype">ℕ</a><a id="8483" class="Symbol">)</a> <a id="8485" class="Symbol">→</a> <a id="8487" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8476" class="Bound">m</a> <a id="8489" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8259" class="Function Operator">+</a> <a id="8491" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8245" class="InductiveConstructor">suc</a> <a id="8495" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8478" class="Bound">n</a> <a id="8497" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#749" class="Datatype Operator">≡</a> <a id="8499" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8245" class="InductiveConstructor">suc</a> <a id="8503" class="Symbol">(</a><a id="8504" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8476" class="Bound">m</a> <a id="8506" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8259" class="Function Operator">+</a> <a id="8508" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8478" class="Bound">n</a><a id="8509" class="Symbol">)</a>{% endraw %}</pre>
This is our first use of a _postulate_.  A postulate specifies a
signature for an identifier but no definition.  Here we postulate
something proved earlier to save space.  Postulates must be used with
caution.  If we postulate something false then we could use Agda to
prove anything whatsoever.

We then repeat the proof of commutativity.
<pre class="Agda">{% raw %}<a id="+-comm"></a><a id="8875" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8875" class="Function">+-comm</a> <a id="8882" class="Symbol">:</a> <a id="8884" class="Symbol">∀</a> <a id="8886" class="Symbol">(</a><a id="8887" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8887" class="Bound">m</a> <a id="8889" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8889" class="Bound">n</a> <a id="8891" class="Symbol">:</a> <a id="8893" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8218" class="Datatype">ℕ</a><a id="8894" class="Symbol">)</a> <a id="8896" class="Symbol">→</a> <a id="8898" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8887" class="Bound">m</a> <a id="8900" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8259" class="Function Operator">+</a> <a id="8902" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8889" class="Bound">n</a> <a id="8904" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#749" class="Datatype Operator">≡</a> <a id="8906" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8889" class="Bound">n</a> <a id="8908" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8259" class="Function Operator">+</a> <a id="8910" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8887" class="Bound">m</a>
<a id="8912" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8875" class="Function">+-comm</a> <a id="8919" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8919" class="Bound">m</a> <a id="8921" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8234" class="InductiveConstructor">zero</a> <a id="8926" class="Symbol">=</a>
  <a id="8930" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5369" class="Function Operator">begin</a>
    <a id="8940" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8919" class="Bound">m</a> <a id="8942" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8259" class="Function Operator">+</a> <a id="8944" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8234" class="InductiveConstructor">zero</a>
  <a id="8951" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5534" class="Function Operator">≡⟨</a> <a id="8954" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8425" class="Postulate">+-identity</a> <a id="8965" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8919" class="Bound">m</a> <a id="8967" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5534" class="Function Operator">⟩</a>
    <a id="8973" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8919" class="Bound">m</a>
  <a id="8977" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5449" class="Function Operator">≡⟨⟩</a>
    <a id="8985" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8234" class="InductiveConstructor">zero</a> <a id="8990" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8259" class="Function Operator">+</a> <a id="8992" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8919" class="Bound">m</a>
  <a id="8996" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5649" class="Function Operator">∎</a>
<a id="8998" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8875" class="Function">+-comm</a> <a id="9005" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#9005" class="Bound">m</a> <a id="9007" class="Symbol">(</a><a id="9008" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8245" class="InductiveConstructor">suc</a> <a id="9012" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#9012" class="Bound">n</a><a id="9013" class="Symbol">)</a> <a id="9015" class="Symbol">=</a>
  <a id="9019" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5369" class="Function Operator">begin</a>
    <a id="9029" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#9005" class="Bound">m</a> <a id="9031" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8259" class="Function Operator">+</a> <a id="9033" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8245" class="InductiveConstructor">suc</a> <a id="9037" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#9012" class="Bound">n</a>
  <a id="9041" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5534" class="Function Operator">≡⟨</a> <a id="9044" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8465" class="Postulate">+-suc</a> <a id="9050" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#9005" class="Bound">m</a> <a id="9052" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#9012" class="Bound">n</a> <a id="9054" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5534" class="Function Operator">⟩</a>
    <a id="9060" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8245" class="InductiveConstructor">suc</a> <a id="9064" class="Symbol">(</a><a id="9065" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#9005" class="Bound">m</a> <a id="9067" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8259" class="Function Operator">+</a> <a id="9069" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#9012" class="Bound">n</a><a id="9070" class="Symbol">)</a>
  <a id="9074" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5534" class="Function Operator">≡⟨</a> <a id="9077" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4120" class="Function">cong</a> <a id="9082" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8245" class="InductiveConstructor">suc</a> <a id="9086" class="Symbol">(</a><a id="9087" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8875" class="Function">+-comm</a> <a id="9094" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#9005" class="Bound">m</a> <a id="9096" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#9012" class="Bound">n</a><a id="9097" class="Symbol">)</a> <a id="9099" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5534" class="Function Operator">⟩</a>
    <a id="9105" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8245" class="InductiveConstructor">suc</a> <a id="9109" class="Symbol">(</a><a id="9110" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#9012" class="Bound">n</a> <a id="9112" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8259" class="Function Operator">+</a> <a id="9114" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#9005" class="Bound">m</a><a id="9115" class="Symbol">)</a>
  <a id="9119" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5449" class="Function Operator">≡⟨⟩</a>
    <a id="9127" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8245" class="InductiveConstructor">suc</a> <a id="9131" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#9012" class="Bound">n</a> <a id="9133" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8259" class="Function Operator">+</a> <a id="9135" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#9005" class="Bound">m</a>
  <a id="9139" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5649" class="Function Operator">∎</a>{% endraw %}</pre>
The reasoning here is similar to that in the
preceding section.  We use
`_≡⟨⟩_` when no justification is required.
One can think of `_≡⟨⟩_` as equivalent to `_≡⟨ refl ⟩_`.

Agda always treats a term as equivalent to its
simplified term.  The reason that one can write

      suc (n + m)
    ≡⟨⟩
      suc n + m

is because Agda treats both terms as the same.
This also means that one could instead interchange
the lines and write

      suc n + m
    ≡⟨⟩
      suc (n + m)

and Agda would not object. Agda only checks that the terms separated
by `≡⟨⟩` have the same simplified form; it's up to us to write them in
an order that will make sense to the reader.


#### Exercise `≤-reasoning` (stretch)

The proof of monotonicity from
Chapter [Relations]({{ site.baseurl }}{% link out/plfa/Relations.md%})
can be written in a more readable form by using an anologue of our
notation for `≡-reasoning`.  Define `≤-reasoning` analogously, and use
it to write out an alternative proof that addition is monotonic with
regard to inequality.  Rewrite both `+-monoˡ-≤` and `+-mono-≤`.



## Rewriting

Consider a property of natural numbers, such as being even.
We repeat the earlier definition.
<pre class="Agda">{% raw %}<a id="10314" class="Keyword">data</a> <a id="even"></a><a id="10319" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#10319" class="Datatype">even</a> <a id="10324" class="Symbol">:</a> <a id="10326" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8218" class="Datatype">ℕ</a> <a id="10328" class="Symbol">→</a> <a id="10330" class="PrimitiveType">Set</a>
<a id="10334" class="Keyword">data</a> <a id="odd"></a><a id="10339" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#10339" class="Datatype">odd</a>  <a id="10344" class="Symbol">:</a> <a id="10346" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8218" class="Datatype">ℕ</a> <a id="10348" class="Symbol">→</a> <a id="10350" class="PrimitiveType">Set</a>

<a id="10355" class="Keyword">data</a> <a id="10360" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#10319" class="Datatype">even</a> <a id="10365" class="Keyword">where</a>

  <a id="even.even-zero"></a><a id="10374" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#10374" class="InductiveConstructor">even-zero</a> <a id="10384" class="Symbol">:</a> <a id="10386" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#10319" class="Datatype">even</a> <a id="10391" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8234" class="InductiveConstructor">zero</a>

  <a id="even.even-suc"></a><a id="10399" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#10399" class="InductiveConstructor">even-suc</a> <a id="10408" class="Symbol">:</a> <a id="10410" class="Symbol">∀</a> <a id="10412" class="Symbol">{</a><a id="10413" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#10413" class="Bound">n</a> <a id="10415" class="Symbol">:</a> <a id="10417" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8218" class="Datatype">ℕ</a><a id="10418" class="Symbol">}</a>
    <a id="10424" class="Symbol">→</a> <a id="10426" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#10339" class="Datatype">odd</a> <a id="10430" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#10413" class="Bound">n</a>
      <a id="10438" class="Comment">------------</a>
    <a id="10455" class="Symbol">→</a> <a id="10457" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#10319" class="Datatype">even</a> <a id="10462" class="Symbol">(</a><a id="10463" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8245" class="InductiveConstructor">suc</a> <a id="10467" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#10413" class="Bound">n</a><a id="10468" class="Symbol">)</a>

<a id="10471" class="Keyword">data</a> <a id="10476" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#10339" class="Datatype">odd</a> <a id="10480" class="Keyword">where</a>
  <a id="odd.odd-suc"></a><a id="10488" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#10488" class="InductiveConstructor">odd-suc</a> <a id="10496" class="Symbol">:</a> <a id="10498" class="Symbol">∀</a> <a id="10500" class="Symbol">{</a><a id="10501" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#10501" class="Bound">n</a> <a id="10503" class="Symbol">:</a> <a id="10505" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8218" class="Datatype">ℕ</a><a id="10506" class="Symbol">}</a>
    <a id="10512" class="Symbol">→</a> <a id="10514" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#10319" class="Datatype">even</a> <a id="10519" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#10501" class="Bound">n</a>
      <a id="10527" class="Comment">-----------</a>
    <a id="10543" class="Symbol">→</a> <a id="10545" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#10339" class="Datatype">odd</a> <a id="10549" class="Symbol">(</a><a id="10550" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8245" class="InductiveConstructor">suc</a> <a id="10554" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#10501" class="Bound">n</a><a id="10555" class="Symbol">)</a>{% endraw %}</pre>
In the previous section, we proved addition is commutative.  Given
evidence that `even (m + n)` holds, we ought also to be able to take
that as evidence that `even (n + m)` holds.

Agda includes special notation to support just this kind of reasoning,
the `rewrite` notation we encountered earlier.
To enable this notation, we use pragmas to tell Agda which type
corresponds to equality.
<pre class="Agda">{% raw %}<a id="10969" class="Symbol">{-#</a> <a id="10973" class="Keyword">BUILTIN</a> EQUALITY <a id="10990" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#749" class="Datatype Operator">_≡_</a> <a id="10994" class="Symbol">#-}</a>{% endraw %}</pre>

We can then prove the desired property as follows.
<pre class="Agda">{% raw %}<a id="even-comm"></a><a id="11074" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#11074" class="Function">even-comm</a> <a id="11084" class="Symbol">:</a> <a id="11086" class="Symbol">∀</a> <a id="11088" class="Symbol">(</a><a id="11089" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#11089" class="Bound">m</a> <a id="11091" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#11091" class="Bound">n</a> <a id="11093" class="Symbol">:</a> <a id="11095" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8218" class="Datatype">ℕ</a><a id="11096" class="Symbol">)</a>
  <a id="11100" class="Symbol">→</a> <a id="11102" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#10319" class="Datatype">even</a> <a id="11107" class="Symbol">(</a><a id="11108" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#11089" class="Bound">m</a> <a id="11110" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8259" class="Function Operator">+</a> <a id="11112" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#11091" class="Bound">n</a><a id="11113" class="Symbol">)</a>
    <a id="11119" class="Comment">------------</a>
  <a id="11134" class="Symbol">→</a> <a id="11136" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#10319" class="Datatype">even</a> <a id="11141" class="Symbol">(</a><a id="11142" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#11091" class="Bound">n</a> <a id="11144" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8259" class="Function Operator">+</a> <a id="11146" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#11089" class="Bound">m</a><a id="11147" class="Symbol">)</a>
<a id="11149" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#11074" class="Function">even-comm</a> <a id="11159" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#11159" class="Bound">m</a> <a id="11161" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#11161" class="Bound">n</a> <a id="11163" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#11163" class="Bound">ev</a>  <a id="11167" class="Keyword">rewrite</a> <a id="11175" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8875" class="Function">+-comm</a> <a id="11182" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#11161" class="Bound">n</a> <a id="11184" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#11159" class="Bound">m</a>  <a id="11187" class="Symbol">=</a>  <a id="11190" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#11163" class="Bound">ev</a>{% endraw %}</pre>
Here `ev` ranges over evidence that `even (m + n)` holds, and we show
that it is also provides evidence that `even (n + m)` holds.  In
general, the keyword `rewrite` is followed by evidence of an
equality, and that equality is used to rewrite the type of the
goal and of any variable in scope.

It is instructive to develop `even-comm` interactively.  To start, we
supply variables for the arguments on the left, and a hole for the
body on the right:

    even-comm : ∀ (m n : ℕ)
      → even (m + n)
        ------------
      → even (n + m)
    even-comm m n ev = {! !}

If we go into the hole and type `C-c C-,` then Agda reports:

    Goal: even (n + m)
    ————————————————————————————————————————————————————————————
    ev : even (m + n)
    n  : ℕ
    m  : ℕ

Now we add the rewrite.

    even-comm : ∀ (m n : ℕ)
      → even (m + n)
        ------------
      → even (n + m)
    even-comm m n ev rewrite +-comm n m = {! !}

If we go into the hole again and type `C-c C-,` then Agda now reports:

    Goal: even (m + n)
    ————————————————————————————————————————————————————————————
    ev : even (m + n)
    n  : ℕ
    m  : ℕ

The arguments have been swapped in the goal.  Now it is trivial to see
that `ev` satisfies the goal, and typing `C-c C-a` in the hole causes
it to be filled with `ev`.  The command `C-c C-a` performs an
automated search, including checking whether a variable in scope has
the same type as the goal.


## Multiple rewrites

One may perform multiple rewrites, each separated by a vertical bar.  For instance,
here is a second proof that addition is commutative, relying on rewrites rather
than chains of equalities.
<pre class="Agda">{% raw %}<a id="+-comm′"></a><a id="12869" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#12869" class="Function">+-comm′</a> <a id="12877" class="Symbol">:</a> <a id="12879" class="Symbol">∀</a> <a id="12881" class="Symbol">(</a><a id="12882" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#12882" class="Bound">m</a> <a id="12884" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#12884" class="Bound">n</a> <a id="12886" class="Symbol">:</a> <a id="12888" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8218" class="Datatype">ℕ</a><a id="12889" class="Symbol">)</a> <a id="12891" class="Symbol">→</a> <a id="12893" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#12882" class="Bound">m</a> <a id="12895" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8259" class="Function Operator">+</a> <a id="12897" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#12884" class="Bound">n</a> <a id="12899" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#749" class="Datatype Operator">≡</a> <a id="12901" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#12884" class="Bound">n</a> <a id="12903" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8259" class="Function Operator">+</a> <a id="12905" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#12882" class="Bound">m</a>
<a id="12907" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#12869" class="Function">+-comm′</a> <a id="12915" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8234" class="InductiveConstructor">zero</a>    <a id="12923" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#12923" class="Bound">n</a>  <a id="12926" class="Keyword">rewrite</a> <a id="12934" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8425" class="Postulate">+-identity</a> <a id="12945" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#12923" class="Bound">n</a>            <a id="12958" class="Symbol">=</a>  <a id="12961" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#789" class="InductiveConstructor">refl</a>
<a id="12966" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#12869" class="Function">+-comm′</a> <a id="12974" class="Symbol">(</a><a id="12975" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8245" class="InductiveConstructor">suc</a> <a id="12979" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#12979" class="Bound">m</a><a id="12980" class="Symbol">)</a> <a id="12982" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#12982" class="Bound">n</a>  <a id="12985" class="Keyword">rewrite</a> <a id="12993" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8465" class="Postulate">+-suc</a> <a id="12999" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#12982" class="Bound">n</a> <a id="13001" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#12979" class="Bound">m</a> <a id="13003" class="Symbol">|</a> <a id="13005" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8875" class="Function">+-comm</a> <a id="13012" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#12979" class="Bound">m</a> <a id="13014" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#12982" class="Bound">n</a>  <a id="13017" class="Symbol">=</a>  <a id="13020" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#789" class="InductiveConstructor">refl</a>{% endraw %}</pre>
This is far more compact.  Among other things, whereas the previous
proof required `cong suc (+-comm m n)` as the justification to invoke
the inductive hypothesis, here it is sufficient to rewrite with
`+-comm m n`, as rewriting automatically takes congruence into
account.  Although proofs with rewriting are shorter, proofs as chains
of equalities are easier to follow, and we will stick with the latter
when feasible.


## Rewriting expanded

The `rewrite` notation is in fact shorthand for an appropriate use of `with`
abstraction.
<pre class="Agda">{% raw %}<a id="even-comm′"></a><a id="13585" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#13585" class="Function">even-comm′</a> <a id="13596" class="Symbol">:</a> <a id="13598" class="Symbol">∀</a> <a id="13600" class="Symbol">(</a><a id="13601" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#13601" class="Bound">m</a> <a id="13603" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#13603" class="Bound">n</a> <a id="13605" class="Symbol">:</a> <a id="13607" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8218" class="Datatype">ℕ</a><a id="13608" class="Symbol">)</a>
  <a id="13612" class="Symbol">→</a> <a id="13614" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#10319" class="Datatype">even</a> <a id="13619" class="Symbol">(</a><a id="13620" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#13601" class="Bound">m</a> <a id="13622" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8259" class="Function Operator">+</a> <a id="13624" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#13603" class="Bound">n</a><a id="13625" class="Symbol">)</a>
    <a id="13631" class="Comment">------------</a>
  <a id="13646" class="Symbol">→</a> <a id="13648" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#10319" class="Datatype">even</a> <a id="13653" class="Symbol">(</a><a id="13654" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#13603" class="Bound">n</a> <a id="13656" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8259" class="Function Operator">+</a> <a id="13658" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#13601" class="Bound">m</a><a id="13659" class="Symbol">)</a>
<a id="13661" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#13585" class="Function">even-comm′</a> <a id="13672" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#13672" class="Bound">m</a> <a id="13674" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#13674" class="Bound">n</a> <a id="13676" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#13676" class="Bound">ev</a> <a id="13679" class="Keyword">with</a>   <a id="13686" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#13672" class="Bound">m</a> <a id="13688" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8259" class="Function Operator">+</a> <a id="13690" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#13674" class="Bound">n</a>  <a id="13693" class="Symbol">|</a> <a id="13695" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8875" class="Function">+-comm</a> <a id="13702" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#13672" class="Bound">m</a> <a id="13704" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#13674" class="Bound">n</a>
<a id="13706" class="Symbol">...</a>                  <a id="13727" class="Symbol">|</a> <a id="13729" class="DottedPattern Symbol">.(</a><a id="13731" class="DottedPattern Bound">n</a> <a id="13733" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8259" class="DottedPattern Function Operator">+</a> <a id="13735" class="DottedPattern Bound">m</a><a id="13736" class="DottedPattern Symbol">)</a> <a id="13738" class="Symbol">|</a> <a id="13740" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#789" class="InductiveConstructor">refl</a>       <a id="13751" class="Symbol">=</a> <a id="13753" class="Bound">ev</a>{% endraw %}</pre>
In general, one can follow `with` by any number of expressions,
separated by bars, where each following equation has the same number
of patterns.  We often write expressions and the corresponding
patterns so they line up in columns, as above. Here the first column
asserts that `m + n` and `n + m` are identical, and the second column
justifies that assertion with evidence of the appropriate equality.
Note also the use of the _dot pattern_, `.(n + m)`.  A dot pattern
consists of a dot followed by an expression, and is used when other
information forces the value matched to be equal to the value of the
expression in the dot pattern.  In this case, the identification of
`m + n` and `n + m` is justified by the subsequent matching of
`+-comm m n` against `refl`.  One might think that the first clause is
redundant as the information is inherent in the second clause, but in
fact Agda is rather picky on this point: omitting the first clause or
reversing the order of the clauses will cause Agda to report an error.
(Try it and see!)

In this case, we can avoid rewrite by simply applying the substitution
function defined earlier.
<pre class="Agda">{% raw %}<a id="even-comm″"></a><a id="14916" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#14916" class="Function">even-comm″</a> <a id="14927" class="Symbol">:</a> <a id="14929" class="Symbol">∀</a> <a id="14931" class="Symbol">(</a><a id="14932" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#14932" class="Bound">m</a> <a id="14934" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#14934" class="Bound">n</a> <a id="14936" class="Symbol">:</a> <a id="14938" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8218" class="Datatype">ℕ</a><a id="14939" class="Symbol">)</a>
  <a id="14943" class="Symbol">→</a> <a id="14945" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#10319" class="Datatype">even</a> <a id="14950" class="Symbol">(</a><a id="14951" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#14932" class="Bound">m</a> <a id="14953" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8259" class="Function Operator">+</a> <a id="14955" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#14934" class="Bound">n</a><a id="14956" class="Symbol">)</a>
    <a id="14962" class="Comment">------------</a>
  <a id="14977" class="Symbol">→</a> <a id="14979" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#10319" class="Datatype">even</a> <a id="14984" class="Symbol">(</a><a id="14985" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#14934" class="Bound">n</a> <a id="14987" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8259" class="Function Operator">+</a> <a id="14989" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#14932" class="Bound">m</a><a id="14990" class="Symbol">)</a>
<a id="14992" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#14916" class="Function">even-comm″</a> <a id="15003" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#15003" class="Bound">m</a> <a id="15005" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#15005" class="Bound">n</a>  <a id="15008" class="Symbol">=</a>  <a id="15011" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4910" class="Function">subst</a> <a id="15017" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#10319" class="Datatype">even</a> <a id="15022" class="Symbol">(</a><a id="15023" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8875" class="Function">+-comm</a> <a id="15030" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#15003" class="Bound">m</a> <a id="15032" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#15005" class="Bound">n</a><a id="15033" class="Symbol">)</a>{% endraw %}</pre>
Nonetheless, rewrite is a vital part of the Agda toolkit.  We will use
it sparingly, but it is occasionally essential.


## Leibniz equality

The form of asserting equality that we have used is due to Martin
Löf, and was published in 1975.  An older form is due to Leibniz, and
was published in 1686.  Leibniz asserted the _identity of
indiscernibles_: two objects are equal if and only if they satisfy the
same properties. This principle sometimes goes by the name Leibniz'
Law, and is closely related to Spock's Law, "A difference that makes
no difference is no difference".  Here we define Leibniz equality,
and show that two terms satisfy Leibniz equality if and only if they
satisfy Martin Löf equality.

Leibniz equality is usually formalised to state that `x ≐ y` holds if
every property `P` that holds of `x` also holds of `y`.  Perhaps
surprisingly, this definition is sufficient to also ensure the
converse, that every property `P` that holds of `y` also holds of `x`.

Let `x` and `y` be objects of type `A`. We say that `x ≐ y` holds if
for every predicate `P` over type `A` we have that `P x` implies `P y`.
<pre class="Agda">{% raw %}<a id="_≐_"></a><a id="16180" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#16180" class="Function Operator">_≐_</a> <a id="16184" class="Symbol">:</a> <a id="16186" class="Symbol">∀</a> <a id="16188" class="Symbol">{</a><a id="16189" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#16189" class="Bound">A</a> <a id="16191" class="Symbol">:</a> <a id="16193" class="PrimitiveType">Set</a><a id="16196" class="Symbol">}</a> <a id="16198" class="Symbol">(</a><a id="16199" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#16199" class="Bound">x</a> <a id="16201" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#16201" class="Bound">y</a> <a id="16203" class="Symbol">:</a> <a id="16205" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#16189" class="Bound">A</a><a id="16206" class="Symbol">)</a> <a id="16208" class="Symbol">→</a> <a id="16210" class="PrimitiveType">Set₁</a>
<a id="16215" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#16180" class="Function Operator">_≐_</a> <a id="16219" class="Symbol">{</a><a id="16220" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#16220" class="Bound">A</a><a id="16221" class="Symbol">}</a> <a id="16223" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#16223" class="Bound">x</a> <a id="16225" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#16225" class="Bound">y</a> <a id="16227" class="Symbol">=</a> <a id="16229" class="Symbol">∀</a> <a id="16231" class="Symbol">(</a><a id="16232" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#16232" class="Bound">P</a> <a id="16234" class="Symbol">:</a> <a id="16236" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#16220" class="Bound">A</a> <a id="16238" class="Symbol">→</a> <a id="16240" class="PrimitiveType">Set</a><a id="16243" class="Symbol">)</a> <a id="16245" class="Symbol">→</a> <a id="16247" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#16232" class="Bound">P</a> <a id="16249" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#16223" class="Bound">x</a> <a id="16251" class="Symbol">→</a> <a id="16253" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#16232" class="Bound">P</a> <a id="16255" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#16225" class="Bound">y</a>{% endraw %}</pre>
We cannot write the left-hand side of the equation as `x ≐ y`,
and instead we write `_≐_ {A} x y` to provide access to the implicit
parameter `A` which appears on the right-hand side.

This is our first use of _levels_.  We cannot assign `Set` the type
`Set`, since this would lead to contradictions such as Russell's
Paradox and Girard's Paradox.  Instead, there is a hierarchy of types,
where `Set : Set₁`, `Set₁ : Set₂`, and so on.  In fact, `Set` itself
is just an abbreviation for `Set₀`.  Since the equation defining `_≐_`
mentions `Set` on the right-hand side, the corresponding signature
must use `Set₁`.  We say a bit more about levels below.

Leibniz equality is reflexive and transitive,
where the first follows by a variant of the identity function
and the second by a variant of function composition.
<pre class="Agda">{% raw %}<a id="refl-≐"></a><a id="17095" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#17095" class="Function">refl-≐</a> <a id="17102" class="Symbol">:</a> <a id="17104" class="Symbol">∀</a> <a id="17106" class="Symbol">{</a><a id="17107" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#17107" class="Bound">A</a> <a id="17109" class="Symbol">:</a> <a id="17111" class="PrimitiveType">Set</a><a id="17114" class="Symbol">}</a> <a id="17116" class="Symbol">{</a><a id="17117" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#17117" class="Bound">x</a> <a id="17119" class="Symbol">:</a> <a id="17121" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#17107" class="Bound">A</a><a id="17122" class="Symbol">}</a>
  <a id="17126" class="Symbol">→</a> <a id="17128" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#17117" class="Bound">x</a> <a id="17130" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#16180" class="Function Operator">≐</a> <a id="17132" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#17117" class="Bound">x</a>
<a id="17134" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#17095" class="Function">refl-≐</a> <a id="17141" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#17141" class="Bound">P</a> <a id="17143" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#17143" class="Bound">Px</a>  <a id="17147" class="Symbol">=</a>  <a id="17150" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#17143" class="Bound">Px</a>

<a id="trans-≐"></a><a id="17154" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#17154" class="Function">trans-≐</a> <a id="17162" class="Symbol">:</a> <a id="17164" class="Symbol">∀</a> <a id="17166" class="Symbol">{</a><a id="17167" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#17167" class="Bound">A</a> <a id="17169" class="Symbol">:</a> <a id="17171" class="PrimitiveType">Set</a><a id="17174" class="Symbol">}</a> <a id="17176" class="Symbol">{</a><a id="17177" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#17177" class="Bound">x</a> <a id="17179" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#17179" class="Bound">y</a> <a id="17181" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#17181" class="Bound">z</a> <a id="17183" class="Symbol">:</a> <a id="17185" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#17167" class="Bound">A</a><a id="17186" class="Symbol">}</a>
  <a id="17190" class="Symbol">→</a> <a id="17192" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#17177" class="Bound">x</a> <a id="17194" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#16180" class="Function Operator">≐</a> <a id="17196" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#17179" class="Bound">y</a>
  <a id="17200" class="Symbol">→</a> <a id="17202" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#17179" class="Bound">y</a> <a id="17204" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#16180" class="Function Operator">≐</a> <a id="17206" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#17181" class="Bound">z</a>
    <a id="17212" class="Comment">-----</a>
  <a id="17220" class="Symbol">→</a> <a id="17222" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#17177" class="Bound">x</a> <a id="17224" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#16180" class="Function Operator">≐</a> <a id="17226" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#17181" class="Bound">z</a>
<a id="17228" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#17154" class="Function">trans-≐</a> <a id="17236" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#17236" class="Bound">x≐y</a> <a id="17240" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#17240" class="Bound">y≐z</a> <a id="17244" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#17244" class="Bound">P</a> <a id="17246" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#17246" class="Bound">Px</a>  <a id="17250" class="Symbol">=</a>  <a id="17253" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#17240" class="Bound">y≐z</a> <a id="17257" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#17244" class="Bound">P</a> <a id="17259" class="Symbol">(</a><a id="17260" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#17236" class="Bound">x≐y</a> <a id="17264" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#17244" class="Bound">P</a> <a id="17266" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#17246" class="Bound">Px</a><a id="17268" class="Symbol">)</a>{% endraw %}</pre>

Symmetry is less obvious.  We have to show that if `P x` implies `P y`
for all predicates `P`, then the implication holds the other way round
as well.
<pre class="Agda">{% raw %}<a id="sym-≐"></a><a id="17446" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#17446" class="Function">sym-≐</a> <a id="17452" class="Symbol">:</a> <a id="17454" class="Symbol">∀</a> <a id="17456" class="Symbol">{</a><a id="17457" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#17457" class="Bound">A</a> <a id="17459" class="Symbol">:</a> <a id="17461" class="PrimitiveType">Set</a><a id="17464" class="Symbol">}</a> <a id="17466" class="Symbol">{</a><a id="17467" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#17467" class="Bound">x</a> <a id="17469" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#17469" class="Bound">y</a> <a id="17471" class="Symbol">:</a> <a id="17473" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#17457" class="Bound">A</a><a id="17474" class="Symbol">}</a>
  <a id="17478" class="Symbol">→</a> <a id="17480" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#17467" class="Bound">x</a> <a id="17482" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#16180" class="Function Operator">≐</a> <a id="17484" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#17469" class="Bound">y</a>
    <a id="17490" class="Comment">-----</a>
  <a id="17498" class="Symbol">→</a> <a id="17500" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#17469" class="Bound">y</a> <a id="17502" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#16180" class="Function Operator">≐</a> <a id="17504" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#17467" class="Bound">x</a>
<a id="17506" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#17446" class="Function">sym-≐</a> <a id="17512" class="Symbol">{</a><a id="17513" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#17513" class="Bound">A</a><a id="17514" class="Symbol">}</a> <a id="17516" class="Symbol">{</a><a id="17517" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#17517" class="Bound">x</a><a id="17518" class="Symbol">}</a> <a id="17520" class="Symbol">{</a><a id="17521" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#17521" class="Bound">y</a><a id="17522" class="Symbol">}</a> <a id="17524" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#17524" class="Bound">x≐y</a> <a id="17528" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#17528" class="Bound">P</a>  <a id="17531" class="Symbol">=</a>  <a id="17534" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#17616" class="Function">Qy</a>
  <a id="17539" class="Keyword">where</a>
    <a id="17549" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#17549" class="Function">Q</a> <a id="17551" class="Symbol">:</a> <a id="17553" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#17513" class="Bound">A</a> <a id="17555" class="Symbol">→</a> <a id="17557" class="PrimitiveType">Set</a>
    <a id="17565" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#17549" class="Function">Q</a> <a id="17567" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#17567" class="Bound">z</a> <a id="17569" class="Symbol">=</a> <a id="17571" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#17528" class="Bound">P</a> <a id="17573" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#17567" class="Bound">z</a> <a id="17575" class="Symbol">→</a> <a id="17577" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#17528" class="Bound">P</a> <a id="17579" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#17517" class="Bound">x</a>
    <a id="17585" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#17585" class="Function">Qx</a> <a id="17588" class="Symbol">:</a> <a id="17590" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#17549" class="Function">Q</a> <a id="17592" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#17517" class="Bound">x</a>
    <a id="17598" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#17585" class="Function">Qx</a> <a id="17601" class="Symbol">=</a> <a id="17603" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#17095" class="Function">refl-≐</a> <a id="17610" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#17528" class="Bound">P</a>
    <a id="17616" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#17616" class="Function">Qy</a> <a id="17619" class="Symbol">:</a> <a id="17621" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#17549" class="Function">Q</a> <a id="17623" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#17521" class="Bound">y</a>
    <a id="17629" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#17616" class="Function">Qy</a> <a id="17632" class="Symbol">=</a> <a id="17634" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#17524" class="Bound">x≐y</a> <a id="17638" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#17549" class="Function">Q</a> <a id="17640" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#17585" class="Function">Qx</a>{% endraw %}</pre>
Given `x ≐ y`, a specific `P`, and a proof of `P y`, we have to
construct a proof of `P x`.  To do so, we instantiate the equality
with a predicate `Q` such that `Q z` holds if `P z` implies `P x`.
The property `Q x` is trivial by reflexivity, and hence `Q y` follows
from `x ≐ y`.  But `Q y` is exactly a proof of what we require, that
`P y` implies `P x`.

We now show that Martin Löf equality implies
Leibniz equality, and vice versa.  In the forward direction, if we know
`x ≡ y` we need for any `P` to take evidence of `P x` to evidence of `P y`,
which is easy since equality of `x` and `y` implies that any proof
of `P x` is also a proof of `P y`.
<pre class="Agda">{% raw %}<a id="≡-implies-≐"></a><a id="18321" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#18321" class="Function">≡-implies-≐</a> <a id="18333" class="Symbol">:</a> <a id="18335" class="Symbol">∀</a> <a id="18337" class="Symbol">{</a><a id="18338" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#18338" class="Bound">A</a> <a id="18340" class="Symbol">:</a> <a id="18342" class="PrimitiveType">Set</a><a id="18345" class="Symbol">}</a> <a id="18347" class="Symbol">{</a><a id="18348" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#18348" class="Bound">x</a> <a id="18350" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#18350" class="Bound">y</a> <a id="18352" class="Symbol">:</a> <a id="18354" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#18338" class="Bound">A</a><a id="18355" class="Symbol">}</a>
  <a id="18359" class="Symbol">→</a> <a id="18361" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#18348" class="Bound">x</a> <a id="18363" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#749" class="Datatype Operator">≡</a> <a id="18365" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#18350" class="Bound">y</a>
    <a id="18371" class="Comment">-----</a>
  <a id="18379" class="Symbol">→</a> <a id="18381" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#18348" class="Bound">x</a> <a id="18383" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#16180" class="Function Operator">≐</a> <a id="18385" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#18350" class="Bound">y</a>
<a id="18387" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#18321" class="Function">≡-implies-≐</a> <a id="18399" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#18399" class="Bound">x≡y</a> <a id="18403" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#18403" class="Bound">P</a>  <a id="18406" class="Symbol">=</a>  <a id="18409" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4910" class="Function">subst</a> <a id="18415" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#18403" class="Bound">P</a> <a id="18417" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#18399" class="Bound">x≡y</a>{% endraw %}</pre>
This direction follows from substitution, which we showed earlier.

In the reverse direction, given that for any `P` we can take a proof of `P x`
to a proof of `P y` we need to show `x ≡ y`.
<pre class="Agda">{% raw %}<a id="≐-implies-≡"></a><a id="18636" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#18636" class="Function">≐-implies-≡</a> <a id="18648" class="Symbol">:</a> <a id="18650" class="Symbol">∀</a> <a id="18652" class="Symbol">{</a><a id="18653" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#18653" class="Bound">A</a> <a id="18655" class="Symbol">:</a> <a id="18657" class="PrimitiveType">Set</a><a id="18660" class="Symbol">}</a> <a id="18662" class="Symbol">{</a><a id="18663" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#18663" class="Bound">x</a> <a id="18665" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#18665" class="Bound">y</a> <a id="18667" class="Symbol">:</a> <a id="18669" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#18653" class="Bound">A</a><a id="18670" class="Symbol">}</a>
  <a id="18674" class="Symbol">→</a> <a id="18676" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#18663" class="Bound">x</a> <a id="18678" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#16180" class="Function Operator">≐</a> <a id="18680" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#18665" class="Bound">y</a>
    <a id="18686" class="Comment">-----</a>
  <a id="18694" class="Symbol">→</a> <a id="18696" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#18663" class="Bound">x</a> <a id="18698" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#749" class="Datatype Operator">≡</a> <a id="18700" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#18665" class="Bound">y</a>
<a id="18702" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#18636" class="Function">≐-implies-≡</a> <a id="18714" class="Symbol">{</a><a id="18715" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#18715" class="Bound">A</a><a id="18716" class="Symbol">}</a> <a id="18718" class="Symbol">{</a><a id="18719" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#18719" class="Bound">x</a><a id="18720" class="Symbol">}</a> <a id="18722" class="Symbol">{</a><a id="18723" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#18723" class="Bound">y</a><a id="18724" class="Symbol">}</a> <a id="18726" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#18726" class="Bound">x≐y</a>  <a id="18731" class="Symbol">=</a>  <a id="18734" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#18808" class="Function">Qy</a>
  <a id="18739" class="Keyword">where</a>
    <a id="18749" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#18749" class="Function">Q</a> <a id="18751" class="Symbol">:</a> <a id="18753" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#18715" class="Bound">A</a> <a id="18755" class="Symbol">→</a> <a id="18757" class="PrimitiveType">Set</a>
    <a id="18765" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#18749" class="Function">Q</a> <a id="18767" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#18767" class="Bound">z</a> <a id="18769" class="Symbol">=</a> <a id="18771" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#18719" class="Bound">x</a> <a id="18773" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#749" class="Datatype Operator">≡</a> <a id="18775" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#18767" class="Bound">z</a>
    <a id="18781" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#18781" class="Function">Qx</a> <a id="18784" class="Symbol">:</a> <a id="18786" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#18749" class="Function">Q</a> <a id="18788" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#18719" class="Bound">x</a>
    <a id="18794" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#18781" class="Function">Qx</a> <a id="18797" class="Symbol">=</a> <a id="18799" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#789" class="InductiveConstructor">refl</a>
    <a id="18808" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#18808" class="Function">Qy</a> <a id="18811" class="Symbol">:</a> <a id="18813" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#18749" class="Function">Q</a> <a id="18815" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#18723" class="Bound">y</a>
    <a id="18821" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#18808" class="Function">Qy</a> <a id="18824" class="Symbol">=</a> <a id="18826" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#18726" class="Bound">x≐y</a> <a id="18830" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#18749" class="Function">Q</a> <a id="18832" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#18781" class="Function">Qx</a>{% endraw %}</pre>
The proof is similar to that for symmetry of Leibniz equality. We take
`Q` to be the predicate that holds of `z` if `x ≡ z`. Then `Q x` is
trivial by reflexivity of Martin Löf equality, and hence `Q y`
follows from `x ≐ y`.  But `Q y` is exactly a proof of what we
require, that `x ≡ y`.

(Parts of this section are adapted from *≐≃≡: Leibniz Equality is
Isomorphic to Martin-Löf Identity, Parametrically*, by Andreas Abel,
Jesper Cockx, Dominique Devries, Andreas Nuyts, and Philip Wadler,
draft, 2017.)


## Universe polymorphism {#unipoly}

As we have seen, not every type belongs to `Set`, but instead every
type belongs somewhere in the hierarchy `Set₀`, `Set₁`, `Set₂`, and so on,
where `Set` abbreviates `Set₀`, and `Set₀ : Set₁`, `Set₁ : Set₂`, and so on.
The definition of equality given above is fine if we want to compare two
values of a type that belongs to `Set`, but what if we want to compare
two values of a type that belongs to `Set ℓ` for some arbitrary level `ℓ`?

The answer is _universe polymorphism_, where a definition is made
with respect to an arbitrary level `ℓ`. To make use of levels, we
first import the following.
<pre class="Agda">{% raw %}<a id="20003" class="Keyword">open</a> <a id="20008" class="Keyword">import</a> <a id="20015" href="https://agda.github.io/agda-stdlib/Level.html" class="Module">Level</a> <a id="20021" class="Keyword">using</a> <a id="20027" class="Symbol">(</a><a id="20028" href="https://agda.github.io/agda-stdlib/Agda.Primitive.html#408" class="Postulate">Level</a><a id="20033" class="Symbol">;</a> <a id="20035" href="https://agda.github.io/agda-stdlib/Agda.Primitive.html#657" class="Primitive Operator">_⊔_</a><a id="20038" class="Symbol">)</a> <a id="20040" class="Keyword">renaming</a> <a id="20049" class="Symbol">(</a><a id="20050" href="https://agda.github.io/agda-stdlib/Agda.Primitive.html#611" class="Primitive">zero</a> <a id="20055" class="Symbol">to</a> <a id="20058" href="https://agda.github.io/agda-stdlib/Agda.Primitive.html#611" class="Primitive">lzero</a><a id="20063" class="Symbol">;</a> <a id="20065" href="https://agda.github.io/agda-stdlib/Agda.Primitive.html#627" class="Primitive">suc</a> <a id="20069" class="Symbol">to</a> <a id="20072" href="https://agda.github.io/agda-stdlib/Agda.Primitive.html#627" class="Primitive">lsuc</a><a id="20076" class="Symbol">)</a>{% endraw %}</pre>
We rename constructors `zero` and `suc` to `lzero` and `lsuc` to avoid confusion
between levels and naturals.

Levels are isomorphic to natural numbers, and have similar constructors:

    lzero : Level
    lsuc  : Level → Level

The names `Set₀`, `Set₁`, `Set₂`, and so on, are abbreviations for

    Set lzero
    Set (lsuc lzero)
    Set (lsuc (lsuc lzero))

and so on. There is also an operator

    _⊔_ : Level → Level → Level

that given two levels returns the larger of the two.

Here is the definition of equality, generalised to an arbitrary level.
<pre class="Agda">{% raw %}<a id="20660" class="Keyword">data</a> <a id="_≡′_"></a><a id="20665" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#20665" class="Datatype Operator">_≡′_</a> <a id="20670" class="Symbol">{</a><a id="20671" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#20671" class="Bound">ℓ</a> <a id="20673" class="Symbol">:</a> <a id="20675" href="https://agda.github.io/agda-stdlib/Agda.Primitive.html#408" class="Postulate">Level</a><a id="20680" class="Symbol">}</a> <a id="20682" class="Symbol">{</a><a id="20683" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#20683" class="Bound">A</a> <a id="20685" class="Symbol">:</a> <a id="20687" class="PrimitiveType">Set</a> <a id="20691" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#20671" class="Bound">ℓ</a><a id="20692" class="Symbol">}</a> <a id="20694" class="Symbol">(</a><a id="20695" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#20695" class="Bound">x</a> <a id="20697" class="Symbol">:</a> <a id="20699" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#20683" class="Bound">A</a><a id="20700" class="Symbol">)</a> <a id="20702" class="Symbol">:</a> <a id="20704" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#20683" class="Bound">A</a> <a id="20706" class="Symbol">→</a> <a id="20708" class="PrimitiveType">Set</a> <a id="20712" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#20671" class="Bound">ℓ</a> <a id="20714" class="Keyword">where</a>
  <a id="_≡′_.refl′"></a><a id="20722" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#20722" class="InductiveConstructor">refl′</a> <a id="20728" class="Symbol">:</a> <a id="20730" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#20695" class="Bound">x</a> <a id="20732" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#20665" class="Datatype Operator">≡′</a> <a id="20735" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#20695" class="Bound">x</a>{% endraw %}</pre>
Similarly, here is the generalised definition of symmetry.
<pre class="Agda">{% raw %}<a id="sym′"></a><a id="20820" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#20820" class="Function">sym′</a> <a id="20825" class="Symbol">:</a> <a id="20827" class="Symbol">∀</a> <a id="20829" class="Symbol">{</a><a id="20830" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#20830" class="Bound">ℓ</a> <a id="20832" class="Symbol">:</a> <a id="20834" href="https://agda.github.io/agda-stdlib/Agda.Primitive.html#408" class="Postulate">Level</a><a id="20839" class="Symbol">}</a> <a id="20841" class="Symbol">{</a><a id="20842" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#20842" class="Bound">A</a> <a id="20844" class="Symbol">:</a> <a id="20846" class="PrimitiveType">Set</a> <a id="20850" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#20830" class="Bound">ℓ</a><a id="20851" class="Symbol">}</a> <a id="20853" class="Symbol">{</a><a id="20854" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#20854" class="Bound">x</a> <a id="20856" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#20856" class="Bound">y</a> <a id="20858" class="Symbol">:</a> <a id="20860" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#20842" class="Bound">A</a><a id="20861" class="Symbol">}</a>
  <a id="20865" class="Symbol">→</a> <a id="20867" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#20854" class="Bound">x</a> <a id="20869" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#20665" class="Datatype Operator">≡′</a> <a id="20872" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#20856" class="Bound">y</a>
    <a id="20878" class="Comment">------</a>
  <a id="20887" class="Symbol">→</a> <a id="20889" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#20856" class="Bound">y</a> <a id="20891" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#20665" class="Datatype Operator">≡′</a> <a id="20894" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#20854" class="Bound">x</a>
<a id="20896" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#20820" class="Function">sym′</a> <a id="20901" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#20722" class="InductiveConstructor">refl′</a> <a id="20907" class="Symbol">=</a> <a id="20909" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#20722" class="InductiveConstructor">refl′</a>{% endraw %}</pre>
For simplicity, we avoid universe polymorphism in the definitions given in
the text, but most definitions in the standard library, including those for
equality, are generalised to arbitrary levels as above.

Here is the generalised definition of Leibniz equality.
<pre class="Agda">{% raw %}<a id="_≐′_"></a><a id="21203" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#21203" class="Function Operator">_≐′_</a> <a id="21208" class="Symbol">:</a> <a id="21210" class="Symbol">∀</a> <a id="21212" class="Symbol">{</a><a id="21213" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#21213" class="Bound">ℓ</a> <a id="21215" class="Symbol">:</a> <a id="21217" href="https://agda.github.io/agda-stdlib/Agda.Primitive.html#408" class="Postulate">Level</a><a id="21222" class="Symbol">}</a> <a id="21224" class="Symbol">{</a><a id="21225" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#21225" class="Bound">A</a> <a id="21227" class="Symbol">:</a> <a id="21229" class="PrimitiveType">Set</a> <a id="21233" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#21213" class="Bound">ℓ</a><a id="21234" class="Symbol">}</a> <a id="21236" class="Symbol">(</a><a id="21237" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#21237" class="Bound">x</a> <a id="21239" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#21239" class="Bound">y</a> <a id="21241" class="Symbol">:</a> <a id="21243" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#21225" class="Bound">A</a><a id="21244" class="Symbol">)</a> <a id="21246" class="Symbol">→</a> <a id="21248" class="PrimitiveType">Set</a> <a id="21252" class="Symbol">(</a><a id="21253" href="https://agda.github.io/agda-stdlib/Agda.Primitive.html#627" class="Primitive">lsuc</a> <a id="21258" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#21213" class="Bound">ℓ</a><a id="21259" class="Symbol">)</a>
<a id="21261" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#21203" class="Function Operator">_≐′_</a> <a id="21266" class="Symbol">{</a><a id="21267" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#21267" class="Bound">ℓ</a><a id="21268" class="Symbol">}</a> <a id="21270" class="Symbol">{</a><a id="21271" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#21271" class="Bound">A</a><a id="21272" class="Symbol">}</a> <a id="21274" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#21274" class="Bound">x</a> <a id="21276" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#21276" class="Bound">y</a> <a id="21278" class="Symbol">=</a> <a id="21280" class="Symbol">∀</a> <a id="21282" class="Symbol">(</a><a id="21283" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#21283" class="Bound">P</a> <a id="21285" class="Symbol">:</a> <a id="21287" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#21271" class="Bound">A</a> <a id="21289" class="Symbol">→</a> <a id="21291" class="PrimitiveType">Set</a> <a id="21295" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#21267" class="Bound">ℓ</a><a id="21296" class="Symbol">)</a> <a id="21298" class="Symbol">→</a> <a id="21300" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#21283" class="Bound">P</a> <a id="21302" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#21274" class="Bound">x</a> <a id="21304" class="Symbol">→</a> <a id="21306" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#21283" class="Bound">P</a> <a id="21308" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#21276" class="Bound">y</a>{% endraw %}</pre>
Before the signature used `Set₁` as the type of a term that includes
`Set`, whereas here the signature uses `Set (lsuc ℓ)` as the type of a
term that includes `Set ℓ`.

Further information on levels can be found in the [Agda Wiki][wiki].

[wiki]: http://wiki.portal.chalmers.se/agda/pmwiki.php?n=ReferenceManual.UniversePolymorphism


## Standard library

Definitions similar to those in this chapter can be found in the
standard library.
<pre class="Agda">{% raw %}<a id="21773" class="Comment">-- import Relation.Binary.PropositionalEquality as Eq</a>
<a id="21827" class="Comment">-- open Eq using (_≡_; refl; trans; sym; cong; cong-app; subst)</a>
<a id="21891" class="Comment">-- open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _≡⟨_⟩_; _∎)</a>{% endraw %}</pre>
Here the imports are shown as comments rather than code to avoid
collisions, as mentioned in the introduction.


## Unicode

This chapter uses the following unicode.

    ≡  U+2261  IDENTICAL TO (\==, \equiv)
    ⟨  U+27E8  MATHEMATICAL LEFT ANGLE BRACKET (\<)
    ⟩  U+27E9  MATHEMATICAL RIGHT ANGLE BRACKET (\>)
    ∎  U+220E  END OF PROOF (\qed)
    ≐  U+2250  APPROACHES THE LIMIT (\.=)
    ℓ  U+2113  SCRIPT SMALL L (\ell)
    ⊔  U+2294  SQUARE CUP (\lub)
    ₀  U+2080  SUBSCRIPT ZERO (\_0)
    ₁  U+2081  SUBSCRIPT ONE (\_1)
    ₂  U+2082  SUBSCRIPT TWO (\_2)
