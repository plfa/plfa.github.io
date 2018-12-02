---
src       : src/plfa/Relations.lagda
title     : "Relations: Inductive definition of relations"
layout    : page
prev      : /Induction/
permalink : /Relations/
next      : /Equality/
---

<pre class="Agda">{% raw %}<a id="170" class="Keyword">module</a> <a id="177" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}" class="Module">plfa.Relations</a> <a id="192" class="Keyword">where</a>{% endraw %}</pre>

After having defined operations such as addition and multiplication,
the next step is to define relations, such as _less than or equal_.

## Imports

<pre class="Agda">{% raw %}<a id="373" class="Keyword">import</a> <a id="380" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html" class="Module">Relation.Binary.PropositionalEquality</a> <a id="418" class="Symbol">as</a> <a id="421" class="Module">Eq</a>
<a id="424" class="Keyword">open</a> <a id="429" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html" class="Module">Eq</a> <a id="432" class="Keyword">using</a> <a id="438" class="Symbol">(</a><a id="439" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator">_≡_</a><a id="442" class="Symbol">;</a> <a id="444" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor">refl</a><a id="448" class="Symbol">;</a> <a id="450" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#1056" class="Function">cong</a><a id="454" class="Symbol">;</a> <a id="456" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.Core.html#838" class="Function">sym</a><a id="459" class="Symbol">)</a>
<a id="461" class="Keyword">open</a> <a id="466" class="Keyword">import</a> <a id="473" href="https://agda.github.io/agda-stdlib/Data.Nat.html" class="Module">Data.Nat</a> <a id="482" class="Keyword">using</a> <a id="488" class="Symbol">(</a><a id="489" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a><a id="490" class="Symbol">;</a> <a id="492" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#115" class="InductiveConstructor">zero</a><a id="496" class="Symbol">;</a> <a id="498" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a><a id="501" class="Symbol">;</a> <a id="503" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">_+_</a><a id="506" class="Symbol">;</a> <a id="508" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#433" class="Primitive Operator">_*_</a><a id="511" class="Symbol">;</a> <a id="513" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#320" class="Primitive Operator">_∸_</a><a id="516" class="Symbol">)</a>
<a id="518" class="Keyword">open</a> <a id="523" class="Keyword">import</a> <a id="530" href="https://agda.github.io/agda-stdlib/Data.Nat.Properties.html" class="Module">Data.Nat.Properties</a> <a id="550" class="Keyword">using</a> <a id="556" class="Symbol">(</a><a id="557" href="https://agda.github.io/agda-stdlib/Data.Nat.Properties.html#8011" class="Function">+-comm</a><a id="563" class="Symbol">;</a> <a id="565" href="https://agda.github.io/agda-stdlib/Data.Nat.Properties.html#7575" class="Function">+-suc</a><a id="570" class="Symbol">)</a>
<a id="572" class="Keyword">open</a> <a id="577" class="Keyword">import</a> <a id="584" href="https://agda.github.io/agda-stdlib/Data.List.html" class="Module">Data.List</a> <a id="594" class="Keyword">using</a> <a id="600" class="Symbol">(</a><a id="601" href="https://agda.github.io/agda-stdlib/Agda.Builtin.List.html#80" class="Datatype">List</a><a id="605" class="Symbol">;</a> <a id="607" href="https://agda.github.io/agda-stdlib/Data.List.Base.html#8019" class="InductiveConstructor">[]</a><a id="609" class="Symbol">;</a> <a id="611" href="https://agda.github.io/agda-stdlib/Agda.Builtin.List.html#132" class="InductiveConstructor Operator">_∷_</a><a id="614" class="Symbol">)</a>
<a id="616" class="Keyword">open</a> <a id="621" class="Keyword">import</a> <a id="628" href="https://agda.github.io/agda-stdlib/Function.html" class="Module">Function</a> <a id="637" class="Keyword">using</a> <a id="643" class="Symbol">(</a><a id="644" href="https://agda.github.io/agda-stdlib/Function.html#1068" class="Function">id</a><a id="646" class="Symbol">;</a> <a id="648" href="https://agda.github.io/agda-stdlib/Function.html#769" class="Function Operator">_∘_</a><a id="651" class="Symbol">)</a>
<a id="653" class="Keyword">open</a> <a id="658" class="Keyword">import</a> <a id="665" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html" class="Module">Relation.Nullary</a> <a id="682" class="Keyword">using</a> <a id="688" class="Symbol">(</a><a id="689" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#464" class="Function Operator">¬_</a><a id="691" class="Symbol">)</a>
<a id="693" class="Keyword">open</a> <a id="698" class="Keyword">import</a> <a id="705" href="https://agda.github.io/agda-stdlib/Data.Empty.html" class="Module">Data.Empty</a> <a id="716" class="Keyword">using</a> <a id="722" class="Symbol">(</a><a id="723" href="https://agda.github.io/agda-stdlib/Data.Empty.html#243" class="Datatype">⊥</a><a id="724" class="Symbol">;</a> <a id="726" href="https://agda.github.io/agda-stdlib/Data.Empty.html#360" class="Function">⊥-elim</a><a id="732" class="Symbol">)</a>{% endraw %}</pre>


## Defining relations

The relation _less than or equal_ has an infinite number of
instances.  Here are a few of them:

    0 ≤ 0     0 ≤ 1     0 ≤ 2     0 ≤ 3     ...
              1 ≤ 1     1 ≤ 2     1 ≤ 3     ...
                        2 ≤ 2     2 ≤ 3     ...
                                  3 ≤ 3     ...
                                            ...

And yet, we can write a finite definition that encompasses
all of these instances in just a few lines.  Here is the
definition as a pair of inference rules:

    z≤n --------
        zero ≤ n

        m ≤ n
    s≤s -------------
        suc m ≤ suc n

And here is the definition in Agda:
<pre class="Agda">{% raw %}<a id="1409" class="Keyword">data</a> <a id="_≤_"></a><a id="1414" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1414" class="Datatype Operator">_≤_</a> <a id="1418" class="Symbol">:</a> <a id="1420" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a> <a id="1422" class="Symbol">→</a> <a id="1424" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a> <a id="1426" class="Symbol">→</a> <a id="1428" class="PrimitiveType">Set</a> <a id="1432" class="Keyword">where</a>

  <a id="_≤_.z≤n"></a><a id="1441" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1441" class="InductiveConstructor">z≤n</a> <a id="1445" class="Symbol">:</a> <a id="1447" class="Symbol">∀</a> <a id="1449" class="Symbol">{</a><a id="1450" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1450" class="Bound">n</a> <a id="1452" class="Symbol">:</a> <a id="1454" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a><a id="1455" class="Symbol">}</a>
      <a id="1463" class="Comment">--------</a>
    <a id="1476" class="Symbol">→</a> <a id="1478" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#115" class="InductiveConstructor">zero</a> <a id="1483" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1414" class="Datatype Operator">≤</a> <a id="1485" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1450" class="Bound">n</a>

  <a id="_≤_.s≤s"></a><a id="1490" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1490" class="InductiveConstructor">s≤s</a> <a id="1494" class="Symbol">:</a> <a id="1496" class="Symbol">∀</a> <a id="1498" class="Symbol">{</a><a id="1499" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1499" class="Bound">m</a> <a id="1501" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1501" class="Bound">n</a> <a id="1503" class="Symbol">:</a> <a id="1505" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a><a id="1506" class="Symbol">}</a>
    <a id="1512" class="Symbol">→</a> <a id="1514" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1499" class="Bound">m</a> <a id="1516" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1414" class="Datatype Operator">≤</a> <a id="1518" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1501" class="Bound">n</a>
      <a id="1526" class="Comment">-------------</a>
    <a id="1544" class="Symbol">→</a> <a id="1546" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="1550" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1499" class="Bound">m</a> <a id="1552" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1414" class="Datatype Operator">≤</a> <a id="1554" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="1558" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1501" class="Bound">n</a>{% endraw %}</pre>
Here `z≤n` and `s≤s` (with no spaces) are constructor names, while
`zero ≤ n`, and `m ≤ n` and `suc m ≤ suc n` (with spaces) are types.
This is our first use of an _indexed_ datatype, where the type `m ≤ n`
is indexed by two naturals, `m` and `n`.  In Agda any line beginning
with two or more dashes is a comment, and here we have exploited that
convention to write our Agda code in a form that resembles the
corresponding inference rules, a trick we will use often from now on.

Both definitions above tell us the same two things:

* _Base case_: for all naturals `n`, the proposition `zero ≤ n` holds
* _Inductive case_: for all naturals `m` and `n`, if the proposition
  `m ≤ n` holds, then the proposition `suc m ≤ suc n` holds.

In fact, they each give us a bit more detail:

* _Base case_: for all naturals `n`, the constructor `z≤n`
  produces evidence that `zero ≤ n` holds.
* _Inductive case_: for all naturals `m` and `n`, the constructor
  `s≤s` takes evidence that `m ≤ n` holds into evidence that
  `suc m ≤ suc n` holds.

For example, here in inference rule notation is the proof that
`2 ≤ 4`.

      z≤n -----
          0 ≤ 2
     s≤s -------
          1 ≤ 3
    s≤s ---------
          2 ≤ 4

And here is the corresponding Agda proof.
<pre class="Agda">{% raw %}<a id="2835" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#2835" class="Function">_</a> <a id="2837" class="Symbol">:</a> <a id="2839" class="Number">2</a> <a id="2841" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1414" class="Datatype Operator">≤</a> <a id="2843" class="Number">4</a>
<a id="2845" class="Symbol">_</a> <a id="2847" class="Symbol">=</a> <a id="2849" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1490" class="InductiveConstructor">s≤s</a> <a id="2853" class="Symbol">(</a><a id="2854" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1490" class="InductiveConstructor">s≤s</a> <a id="2858" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1441" class="InductiveConstructor">z≤n</a><a id="2861" class="Symbol">)</a>{% endraw %}</pre>




## Implicit arguments

This is our first use of implicit arguments.  In the definition of
inequality, the two lines defining the constructors use `∀`, very
similar to our use of `∀` in propositions such as:

    +-comm : ∀ (m n : ℕ) → m + n ≡ n + m

However, here the declarations are surrounded by curly braces `{ }`
rather than parentheses `( )`.  This means that the arguments are
_implicit_ and need not be written explicitly; instead, they are
_inferred_ by Agda's typechecker. Thus, we write `+-comm m n` for the
proof that `m + n ≡ n + m`, but `z≤n` for the proof that `zero ≤ n`,
leaving `n` implicit.  Similarly, if `m≤n` is evidence that `m ≤ n`,
we write `s≤s m≤n` for evidence that `suc m ≤ suc n`, leaving both `m`
and `n` implicit.

If we wish, it is possible to provide implicit arguments explicitly by
writing the arguments inside curly braces.  For instance, here is the
Agda proof that `2 ≤ 4` repeated, with the implicit arguments made
explicit.
<pre class="Agda">{% raw %}<a id="3856" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#3856" class="Function">_</a> <a id="3858" class="Symbol">:</a> <a id="3860" class="Number">2</a> <a id="3862" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1414" class="Datatype Operator">≤</a> <a id="3864" class="Number">4</a>
<a id="3866" class="Symbol">_</a> <a id="3868" class="Symbol">=</a> <a id="3870" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1490" class="InductiveConstructor">s≤s</a> <a id="3874" class="Symbol">{</a><a id="3875" class="Number">1</a><a id="3876" class="Symbol">}</a> <a id="3878" class="Symbol">{</a><a id="3879" class="Number">3</a><a id="3880" class="Symbol">}</a> <a id="3882" class="Symbol">(</a><a id="3883" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1490" class="InductiveConstructor">s≤s</a> <a id="3887" class="Symbol">{</a><a id="3888" class="Number">0</a><a id="3889" class="Symbol">}</a> <a id="3891" class="Symbol">{</a><a id="3892" class="Number">2</a><a id="3893" class="Symbol">}</a> <a id="3895" class="Symbol">(</a><a id="3896" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1441" class="InductiveConstructor">z≤n</a> <a id="3900" class="Symbol">{</a><a id="3901" class="Number">2</a><a id="3902" class="Symbol">}))</a>{% endraw %}</pre>
One may also identify implicit arguments by name.
<pre class="Agda">{% raw %}<a id="3980" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#3980" class="Function">_</a> <a id="3982" class="Symbol">:</a> <a id="3984" class="Number">2</a> <a id="3986" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1414" class="Datatype Operator">≤</a> <a id="3988" class="Number">4</a>
<a id="3990" class="Symbol">_</a> <a id="3992" class="Symbol">=</a> <a id="3994" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1490" class="InductiveConstructor">s≤s</a> <a id="3998" class="Symbol">{</a><a id="3999" class="Argument">m</a> <a id="4001" class="Symbol">=</a> <a id="4003" class="Number">1</a><a id="4004" class="Symbol">}</a> <a id="4006" class="Symbol">{</a><a id="4007" class="Argument">n</a> <a id="4009" class="Symbol">=</a> <a id="4011" class="Number">3</a><a id="4012" class="Symbol">}</a> <a id="4014" class="Symbol">(</a><a id="4015" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1490" class="InductiveConstructor">s≤s</a> <a id="4019" class="Symbol">{</a><a id="4020" class="Argument">m</a> <a id="4022" class="Symbol">=</a> <a id="4024" class="Number">0</a><a id="4025" class="Symbol">}</a> <a id="4027" class="Symbol">{</a><a id="4028" class="Argument">n</a> <a id="4030" class="Symbol">=</a> <a id="4032" class="Number">2</a><a id="4033" class="Symbol">}</a> <a id="4035" class="Symbol">(</a><a id="4036" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1441" class="InductiveConstructor">z≤n</a> <a id="4040" class="Symbol">{</a><a id="4041" class="Argument">n</a> <a id="4043" class="Symbol">=</a> <a id="4045" class="Number">2</a><a id="4046" class="Symbol">}))</a>{% endraw %}</pre>
In the latter format, you may only supply some implicit arguments.
<pre class="Agda">{% raw %}<a id="4141" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#4141" class="Function">_</a> <a id="4143" class="Symbol">:</a> <a id="4145" class="Number">2</a> <a id="4147" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1414" class="Datatype Operator">≤</a> <a id="4149" class="Number">4</a>
<a id="4151" class="Symbol">_</a> <a id="4153" class="Symbol">=</a> <a id="4155" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1490" class="InductiveConstructor">s≤s</a> <a id="4159" class="Symbol">{</a><a id="4160" class="Argument">n</a> <a id="4162" class="Symbol">=</a> <a id="4164" class="Number">3</a><a id="4165" class="Symbol">}</a> <a id="4167" class="Symbol">(</a><a id="4168" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1490" class="InductiveConstructor">s≤s</a> <a id="4172" class="Symbol">{</a><a id="4173" class="Argument">n</a> <a id="4175" class="Symbol">=</a> <a id="4177" class="Number">2</a><a id="4178" class="Symbol">}</a> <a id="4180" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1441" class="InductiveConstructor">z≤n</a><a id="4183" class="Symbol">)</a>{% endraw %}</pre>
It is not permitted to swap implicit arguments, even when named.


## Precedence

We declare the precedence for comparison as follows.
<pre class="Agda">{% raw %}<a id="4344" class="Keyword">infix</a> <a id="4350" class="Number">4</a> <a id="4352" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1414" class="Datatype Operator">_≤_</a>{% endraw %}</pre>
We set the precedence of `_≤_` at level 4, so it binds less tightly
that `_+_` at level 6 and hence `1 + 2 ≤ 3` parses as `(1 + 2) ≤ 3`.
We write `infix` to indicate that the operator does not associate to
either the left or right, as it makes no sense to parse `1 ≤ 2 ≤ 3` as
either `(1 ≤ 2) ≤ 3` or `1 ≤ (2 ≤ 3)`.


## Decidability

Given two numbers, it is straightforward to compute whether or not the
first is less than or equal to the second.  We don't give the code for
doing so here, but will return to this point in
Chapter [Decidable]({{ site.baseurl }}{% link out/plfa/Decidable.md%}).


## Properties of ordering relations

Relations pop up all the time, and mathematicians have agreed
on names for some of the most common properties.

* _Reflexive_ For all `n`, the relation `n ≤ n` holds.
* _Transitive_ For all `m`, `n`, and `p`, if `m ≤ n` and
`n ≤ p` hold, then `m ≤ p` holds.
* _Anti-symmetric_ For all `m` and `n`, if both `m ≤ n` and
`n ≤ m` hold, then `m ≡ n` holds.
* _Total_ For all `m` and `n`, either `m ≤ n` or `n ≤ m`
holds.

The relation `_≤_` satisfies all four of these properties.

There are also names for some combinations of these properties.

* _Preorder_ Any relation that is reflexive and transitive.
* _Partial order_ Any preorder that is also anti-symmetric.
* _Total order_ Any partial order that is also total.

If you ever bump into a relation at a party, you now know how
to make small talk, by asking it whether it is reflexive, transitive,
anti-symmetric, and total. Or instead you might ask whether it is a
preorder, partial order, or total order.

Less frivolously, if you ever bump into a relation while reading a
technical paper, this gives you a way to orient yourself, by checking
whether or not it is a preorder, partial order, or total order.  A
careful author will often call out these properties---or their
lack---for instance by saying that a newly introduced relation is a
a partial order but not a total order.


#### Exercise `orderings` {#orderings}

Give an example of a preorder that is not a partial order.

Give an example of a partial order that is not a total order.


## Reflexivity

The first property to prove about comparison is that it is reflexive:
for any natural `n`, the relation `n ≤ n` holds.  We follow the
convention in the standard library and make the argument implicit,
as that will make it easier to invoke reflexivity.
<pre class="Agda">{% raw %}<a id="≤-refl"></a><a id="6748" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#6748" class="Function">≤-refl</a> <a id="6755" class="Symbol">:</a> <a id="6757" class="Symbol">∀</a> <a id="6759" class="Symbol">{</a><a id="6760" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#6760" class="Bound">n</a> <a id="6762" class="Symbol">:</a> <a id="6764" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a><a id="6765" class="Symbol">}</a>
    <a id="6771" class="Comment">-----</a>
  <a id="6779" class="Symbol">→</a> <a id="6781" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#6760" class="Bound">n</a> <a id="6783" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1414" class="Datatype Operator">≤</a> <a id="6785" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#6760" class="Bound">n</a>
<a id="6787" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#6748" class="Function">≤-refl</a> <a id="6794" class="Symbol">{</a><a id="6795" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#115" class="InductiveConstructor">zero</a><a id="6799" class="Symbol">}</a>   <a id="6803" class="Symbol">=</a>  <a id="6806" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1441" class="InductiveConstructor">z≤n</a>
<a id="6810" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#6748" class="Function">≤-refl</a> <a id="6817" class="Symbol">{</a><a id="6818" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="6822" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#6822" class="Bound">n</a><a id="6823" class="Symbol">}</a>  <a id="6826" class="Symbol">=</a>  <a id="6829" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1490" class="InductiveConstructor">s≤s</a> <a id="6833" class="Symbol">(</a><a id="6834" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#6748" class="Function">≤-refl</a> <a id="6841" class="Symbol">{</a><a id="6842" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#6822" class="Bound">n</a><a id="6843" class="Symbol">})</a>{% endraw %}</pre>
The proof is a straightforward induction on the implicit argument `n`.
In the base case, `zero ≤ zero` holds by `z≤n`.  In the inductive
case, the inductive hypothesis `≤-refl {n}` gives us a proof of `n ≤
n`, and applying `s≤s` to that yields a proof of `suc n ≤ suc n`.

It is a good exercise to prove reflexivity interactively in Emacs,
using holes and the `C-c C-c`, `C-c C-,`, and `C-c C-r` commands.


## Transitivity

The second property to prove about comparison is that it is
transitive: for any naturals `m`, `n`, and `p`, if `m ≤ n` and `n ≤ p`
hold, then `m ≤ p` holds.  Again, `m`, `n`, and `p` are implicit.
<pre class="Agda">{% raw %}<a id="≤-trans"></a><a id="7492" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#7492" class="Function">≤-trans</a> <a id="7500" class="Symbol">:</a> <a id="7502" class="Symbol">∀</a> <a id="7504" class="Symbol">{</a><a id="7505" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#7505" class="Bound">m</a> <a id="7507" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#7507" class="Bound">n</a> <a id="7509" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#7509" class="Bound">p</a> <a id="7511" class="Symbol">:</a> <a id="7513" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a><a id="7514" class="Symbol">}</a>
  <a id="7518" class="Symbol">→</a> <a id="7520" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#7505" class="Bound">m</a> <a id="7522" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1414" class="Datatype Operator">≤</a> <a id="7524" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#7507" class="Bound">n</a>
  <a id="7528" class="Symbol">→</a> <a id="7530" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#7507" class="Bound">n</a> <a id="7532" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1414" class="Datatype Operator">≤</a> <a id="7534" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#7509" class="Bound">p</a>
    <a id="7540" class="Comment">-----</a>
  <a id="7548" class="Symbol">→</a> <a id="7550" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#7505" class="Bound">m</a> <a id="7552" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1414" class="Datatype Operator">≤</a> <a id="7554" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#7509" class="Bound">p</a>
<a id="7556" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#7492" class="Function">≤-trans</a> <a id="7564" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1441" class="InductiveConstructor">z≤n</a>       <a id="7574" class="Symbol">_</a>          <a id="7585" class="Symbol">=</a>  <a id="7588" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1441" class="InductiveConstructor">z≤n</a>
<a id="7592" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#7492" class="Function">≤-trans</a> <a id="7600" class="Symbol">(</a><a id="7601" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1490" class="InductiveConstructor">s≤s</a> <a id="7605" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#7605" class="Bound">m≤n</a><a id="7608" class="Symbol">)</a> <a id="7610" class="Symbol">(</a><a id="7611" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1490" class="InductiveConstructor">s≤s</a> <a id="7615" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#7615" class="Bound">n≤p</a><a id="7618" class="Symbol">)</a>  <a id="7621" class="Symbol">=</a>  <a id="7624" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1490" class="InductiveConstructor">s≤s</a> <a id="7628" class="Symbol">(</a><a id="7629" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#7492" class="Function">≤-trans</a> <a id="7637" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#7605" class="Bound">m≤n</a> <a id="7641" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#7615" class="Bound">n≤p</a><a id="7644" class="Symbol">)</a>{% endraw %}</pre>
Here the proof is by induction on the _evidence_ that `m ≤ n`.  In the
base case, the first inequality holds by `z≤n` and must show `zero ≤
p`, which follows immediately by `z≤n`.  In this case, the fact that
`n ≤ p` is irrelevant, and we write `_` as the pattern to indicate
that the corresponding evidence is unused.

In the inductive case, the first inequality holds by `s≤s m≤n`
and the second inequality by `s≤s n≤p`, and so we are given
`suc m ≤ suc n` and `suc n ≤ suc p`, and must show `suc m ≤ suc p`.
The inductive hypothesis `≤-trans m≤n n≤p` establishes
that `m ≤ p`, and our goal follows by applying `s≤s`.

The case `≤-trans (s≤s m≤n) z≤n` cannot arise, since the first
inequality implies the middle value is `suc n` while the second
inequality implies that it is `zero`.  Agda can determine that such a
case cannot arise, and does not require (or permit) it to be listed.

Alternatively, we could make the implicit parameters explicit.
<pre class="Agda">{% raw %}<a id="≤-trans′"></a><a id="8621" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#8621" class="Function">≤-trans′</a> <a id="8630" class="Symbol">:</a> <a id="8632" class="Symbol">∀</a> <a id="8634" class="Symbol">(</a><a id="8635" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#8635" class="Bound">m</a> <a id="8637" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#8637" class="Bound">n</a> <a id="8639" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#8639" class="Bound">p</a> <a id="8641" class="Symbol">:</a> <a id="8643" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a><a id="8644" class="Symbol">)</a>
  <a id="8648" class="Symbol">→</a> <a id="8650" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#8635" class="Bound">m</a> <a id="8652" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1414" class="Datatype Operator">≤</a> <a id="8654" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#8637" class="Bound">n</a>
  <a id="8658" class="Symbol">→</a> <a id="8660" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#8637" class="Bound">n</a> <a id="8662" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1414" class="Datatype Operator">≤</a> <a id="8664" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#8639" class="Bound">p</a>
    <a id="8670" class="Comment">-----</a>
  <a id="8678" class="Symbol">→</a> <a id="8680" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#8635" class="Bound">m</a> <a id="8682" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1414" class="Datatype Operator">≤</a> <a id="8684" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#8639" class="Bound">p</a>
<a id="8686" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#8621" class="Function">≤-trans′</a> <a id="8695" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#115" class="InductiveConstructor">zero</a>    <a id="8703" class="Symbol">_</a>       <a id="8711" class="Symbol">_</a>       <a id="8719" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1441" class="InductiveConstructor">z≤n</a>       <a id="8729" class="Symbol">_</a>          <a id="8740" class="Symbol">=</a>  <a id="8743" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1441" class="InductiveConstructor">z≤n</a>
<a id="8747" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#8621" class="Function">≤-trans′</a> <a id="8756" class="Symbol">(</a><a id="8757" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="8761" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#8761" class="Bound">m</a><a id="8762" class="Symbol">)</a> <a id="8764" class="Symbol">(</a><a id="8765" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="8769" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#8769" class="Bound">n</a><a id="8770" class="Symbol">)</a> <a id="8772" class="Symbol">(</a><a id="8773" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="8777" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#8777" class="Bound">p</a><a id="8778" class="Symbol">)</a> <a id="8780" class="Symbol">(</a><a id="8781" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1490" class="InductiveConstructor">s≤s</a> <a id="8785" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#8785" class="Bound">m≤n</a><a id="8788" class="Symbol">)</a> <a id="8790" class="Symbol">(</a><a id="8791" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1490" class="InductiveConstructor">s≤s</a> <a id="8795" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#8795" class="Bound">n≤p</a><a id="8798" class="Symbol">)</a>  <a id="8801" class="Symbol">=</a>  <a id="8804" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1490" class="InductiveConstructor">s≤s</a> <a id="8808" class="Symbol">(</a><a id="8809" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#8621" class="Function">≤-trans′</a> <a id="8818" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#8761" class="Bound">m</a> <a id="8820" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#8769" class="Bound">n</a> <a id="8822" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#8777" class="Bound">p</a> <a id="8824" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#8785" class="Bound">m≤n</a> <a id="8828" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#8795" class="Bound">n≤p</a><a id="8831" class="Symbol">)</a>{% endraw %}</pre>
One might argue that this is clearer or one might argue that the extra
length obscures the essence of the proof.  We will usually opt for
shorter proofs.

The technique of induction on evidence that a property holds (e.g.,
inducting on evidence that `m ≤ n`)---rather than induction on 
values of which the property holds (e.g., inducting on `m`)---will turn
out to be immensely valuable, and one that we use often.

Again, it is a good exercise to prove transitivity interactively in Emacs,
using holes and the `C-c C-c`, `C-c C-,`, and `C-c C-r` commands.


## Anti-symmetry

The third property to prove about comparison is that it is
antisymmetric: for all naturals `m` and `n`, if both `m ≤ n` and `n ≤
m` hold, then `m ≡ n` holds.
<pre class="Agda">{% raw %}<a id="≤-antisym"></a><a id="9593" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#9593" class="Function">≤-antisym</a> <a id="9603" class="Symbol">:</a> <a id="9605" class="Symbol">∀</a> <a id="9607" class="Symbol">{</a><a id="9608" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#9608" class="Bound">m</a> <a id="9610" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#9610" class="Bound">n</a> <a id="9612" class="Symbol">:</a> <a id="9614" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a><a id="9615" class="Symbol">}</a>
  <a id="9619" class="Symbol">→</a> <a id="9621" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#9608" class="Bound">m</a> <a id="9623" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1414" class="Datatype Operator">≤</a> <a id="9625" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#9610" class="Bound">n</a>
  <a id="9629" class="Symbol">→</a> <a id="9631" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#9610" class="Bound">n</a> <a id="9633" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1414" class="Datatype Operator">≤</a> <a id="9635" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#9608" class="Bound">m</a>
    <a id="9641" class="Comment">-----</a>
  <a id="9649" class="Symbol">→</a> <a id="9651" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#9608" class="Bound">m</a> <a id="9653" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator">≡</a> <a id="9655" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#9610" class="Bound">n</a>
<a id="9657" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#9593" class="Function">≤-antisym</a> <a id="9667" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1441" class="InductiveConstructor">z≤n</a>       <a id="9677" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1441" class="InductiveConstructor">z≤n</a>        <a id="9688" class="Symbol">=</a>  <a id="9691" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor">refl</a>
<a id="9696" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#9593" class="Function">≤-antisym</a> <a id="9706" class="Symbol">(</a><a id="9707" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1490" class="InductiveConstructor">s≤s</a> <a id="9711" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#9711" class="Bound">m≤n</a><a id="9714" class="Symbol">)</a> <a id="9716" class="Symbol">(</a><a id="9717" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1490" class="InductiveConstructor">s≤s</a> <a id="9721" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#9721" class="Bound">n≤m</a><a id="9724" class="Symbol">)</a>  <a id="9727" class="Symbol">=</a>  <a id="9730" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#1056" class="Function">cong</a> <a id="9735" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="9739" class="Symbol">(</a><a id="9740" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#9593" class="Function">≤-antisym</a> <a id="9750" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#9711" class="Bound">m≤n</a> <a id="9754" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#9721" class="Bound">n≤m</a><a id="9757" class="Symbol">)</a>{% endraw %}</pre>
Again, the proof is by induction over the evidence that `m ≤ n`
and `n ≤ m` hold.

In the base case, both inequalities hold by `z≤n`, and so we are given
`zero ≤ zero` and `zero ≤ zero` and must show `zero ≡ zero`, which
follows by reflexivity.  (Reflexivity of equality, that is, not
reflexivity of inequality.)

In the inductive case, the first inequality holds by `s≤s m≤n` and the
second inequality holds by `s≤s n≤m`, and so we are given `suc m ≤ suc n`
and `suc n ≤ suc m` and must show `suc m ≡ suc n`.  The inductive
hypothesis `≤-antisym m≤n n≤m` establishes that `m ≡ n`, and our goal
follows by congruence.

#### Exercise `≤-antisym-cases` {#leq-antisym-cases} 

The above proof omits cases where one argument is `z≤n` and one
argument is `s≤s`.  Why is it ok to omit them?


## Total

The fourth property to prove about comparison is that it is total:
for any naturals `m` and `n` either `m ≤ n` or `n ≤ m`, or both if
`m` and `n` are equal.

We specify what it means for inequality to be total.
<pre class="Agda">{% raw %}<a id="10791" class="Keyword">data</a> <a id="Total"></a><a id="10796" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#10796" class="Datatype">Total</a> <a id="10802" class="Symbol">(</a><a id="10803" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#10803" class="Bound">m</a> <a id="10805" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#10805" class="Bound">n</a> <a id="10807" class="Symbol">:</a> <a id="10809" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a><a id="10810" class="Symbol">)</a> <a id="10812" class="Symbol">:</a> <a id="10814" class="PrimitiveType">Set</a> <a id="10818" class="Keyword">where</a>

  <a id="Total.forward"></a><a id="10827" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#10827" class="InductiveConstructor">forward</a> <a id="10835" class="Symbol">:</a>
      <a id="10843" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#10803" class="Bound">m</a> <a id="10845" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1414" class="Datatype Operator">≤</a> <a id="10847" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#10805" class="Bound">n</a>
      <a id="10855" class="Comment">---------</a>
    <a id="10869" class="Symbol">→</a> <a id="10871" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#10796" class="Datatype">Total</a> <a id="10877" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#10803" class="Bound">m</a> <a id="10879" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#10805" class="Bound">n</a>

  <a id="Total.flipped"></a><a id="10884" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#10884" class="InductiveConstructor">flipped</a> <a id="10892" class="Symbol">:</a>
      <a id="10900" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#10805" class="Bound">n</a> <a id="10902" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1414" class="Datatype Operator">≤</a> <a id="10904" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#10803" class="Bound">m</a>
      <a id="10912" class="Comment">---------</a>
    <a id="10926" class="Symbol">→</a> <a id="10928" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#10796" class="Datatype">Total</a> <a id="10934" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#10803" class="Bound">m</a> <a id="10936" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#10805" class="Bound">n</a>{% endraw %}</pre>
Evidence that `Total m n` holds is either of the form
`forward m≤n` or `flipped n≤m`, where `m≤n` and `n≤m` are
evidence of `m ≤ n` and `n ≤ m` respectively.

(For those familiar with logic, the above definition
could also be written as a disjunction. Disjunctions will
be introduced in Chapter [Connectives]({{ site.baseurl }}{% link out/plfa/Connectives.md%}).)

This is our first use of a datatype with _parameters_,
in this case `m` and `n`.  It is equivalent to the following
indexed datatype.
<pre class="Agda">{% raw %}<a id="11426" class="Keyword">data</a> <a id="Total′"></a><a id="11431" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#11431" class="Datatype">Total′</a> <a id="11438" class="Symbol">:</a> <a id="11440" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a> <a id="11442" class="Symbol">→</a> <a id="11444" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a> <a id="11446" class="Symbol">→</a> <a id="11448" class="PrimitiveType">Set</a> <a id="11452" class="Keyword">where</a>

  <a id="Total′.forward′"></a><a id="11461" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#11461" class="InductiveConstructor">forward′</a> <a id="11470" class="Symbol">:</a> <a id="11472" class="Symbol">∀</a> <a id="11474" class="Symbol">{</a><a id="11475" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#11475" class="Bound">m</a> <a id="11477" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#11477" class="Bound">n</a> <a id="11479" class="Symbol">:</a> <a id="11481" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a><a id="11482" class="Symbol">}</a>
    <a id="11488" class="Symbol">→</a> <a id="11490" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#11475" class="Bound">m</a> <a id="11492" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1414" class="Datatype Operator">≤</a> <a id="11494" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#11477" class="Bound">n</a>
      <a id="11502" class="Comment">----------</a>
    <a id="11517" class="Symbol">→</a> <a id="11519" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#11431" class="Datatype">Total′</a> <a id="11526" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#11475" class="Bound">m</a> <a id="11528" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#11477" class="Bound">n</a>

  <a id="Total′.flipped′"></a><a id="11533" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#11533" class="InductiveConstructor">flipped′</a> <a id="11542" class="Symbol">:</a> <a id="11544" class="Symbol">∀</a> <a id="11546" class="Symbol">{</a><a id="11547" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#11547" class="Bound">m</a> <a id="11549" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#11549" class="Bound">n</a> <a id="11551" class="Symbol">:</a> <a id="11553" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a><a id="11554" class="Symbol">}</a>
    <a id="11560" class="Symbol">→</a> <a id="11562" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#11549" class="Bound">n</a> <a id="11564" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1414" class="Datatype Operator">≤</a> <a id="11566" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#11547" class="Bound">m</a>
      <a id="11574" class="Comment">----------</a>
    <a id="11589" class="Symbol">→</a> <a id="11591" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#11431" class="Datatype">Total′</a> <a id="11598" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#11547" class="Bound">m</a> <a id="11600" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#11549" class="Bound">n</a>{% endraw %}</pre>
Each parameter of the type translates as an implicit parameter of each
constructor.  Unlike an indexed datatype, where the indexes can vary
(as in `zero ≤ n` and `suc m ≤ suc n`), in a parameterised datatype
the parameters must always be the same (as in `Total m n`).
Parameterised declarations are shorter, easier to read, and
occcasionally aid Agda's termination checker, so we will use them in
preference to indexed types when possible.

With that preliminary out of the way, we specify and prove totality.
<pre class="Agda">{% raw %}<a id="≤-total"></a><a id="12136" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#12136" class="Function">≤-total</a> <a id="12144" class="Symbol">:</a> <a id="12146" class="Symbol">∀</a> <a id="12148" class="Symbol">(</a><a id="12149" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#12149" class="Bound">m</a> <a id="12151" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#12151" class="Bound">n</a> <a id="12153" class="Symbol">:</a> <a id="12155" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a><a id="12156" class="Symbol">)</a> <a id="12158" class="Symbol">→</a> <a id="12160" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#10796" class="Datatype">Total</a> <a id="12166" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#12149" class="Bound">m</a> <a id="12168" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#12151" class="Bound">n</a>
<a id="12170" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#12136" class="Function">≤-total</a> <a id="12178" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#115" class="InductiveConstructor">zero</a>    <a id="12186" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#12186" class="Bound">n</a>                         <a id="12212" class="Symbol">=</a>  <a id="12215" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#10827" class="InductiveConstructor">forward</a> <a id="12223" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1441" class="InductiveConstructor">z≤n</a>
<a id="12227" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#12136" class="Function">≤-total</a> <a id="12235" class="Symbol">(</a><a id="12236" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="12240" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#12240" class="Bound">m</a><a id="12241" class="Symbol">)</a> <a id="12243" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#115" class="InductiveConstructor">zero</a>                      <a id="12269" class="Symbol">=</a>  <a id="12272" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#10884" class="InductiveConstructor">flipped</a> <a id="12280" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1441" class="InductiveConstructor">z≤n</a>
<a id="12284" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#12136" class="Function">≤-total</a> <a id="12292" class="Symbol">(</a><a id="12293" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="12297" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#12297" class="Bound">m</a><a id="12298" class="Symbol">)</a> <a id="12300" class="Symbol">(</a><a id="12301" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="12305" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#12305" class="Bound">n</a><a id="12306" class="Symbol">)</a> <a id="12308" class="Keyword">with</a> <a id="12313" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#12136" class="Function">≤-total</a> <a id="12321" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#12297" class="Bound">m</a> <a id="12323" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#12305" class="Bound">n</a>
<a id="12325" class="Symbol">...</a>                        <a id="12352" class="Symbol">|</a> <a id="12354" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#10827" class="InductiveConstructor">forward</a> <a id="12362" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#12362" class="Bound">m≤n</a>  <a id="12367" class="Symbol">=</a>  <a id="12370" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#10827" class="InductiveConstructor">forward</a> <a id="12378" class="Symbol">(</a><a id="12379" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1490" class="InductiveConstructor">s≤s</a> <a id="12383" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#12362" class="Bound">m≤n</a><a id="12386" class="Symbol">)</a>
<a id="12388" class="Symbol">...</a>                        <a id="12415" class="Symbol">|</a> <a id="12417" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#10884" class="InductiveConstructor">flipped</a> <a id="12425" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#12425" class="Bound">n≤m</a>  <a id="12430" class="Symbol">=</a>  <a id="12433" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#10884" class="InductiveConstructor">flipped</a> <a id="12441" class="Symbol">(</a><a id="12442" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1490" class="InductiveConstructor">s≤s</a> <a id="12446" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#12425" class="Bound">n≤m</a><a id="12449" class="Symbol">)</a>{% endraw %}</pre>
In this case the proof is by induction over both the first
and second arguments.  We perform a case analysis:

* _First base case_: If the first argument is `zero` and the
  second argument is `n` then the forward case holds,
  with `z≤n` as evidence that `zero ≤ n`.

* _Second base case_: If the first argument is `suc m` and the
  second argument is `zero` then the flipped case holds, with
  `z≤n` as evidence that `zero ≤ suc m`.

* _Inductive case_: If the first argument is `suc m` and the
  second argument is `suc n`, then the inductive hypothesis
  `≤-total m n` establishes one of the following:

  + The forward case of the inductive hypothesis holds with `m≤n` as
    evidence that `m ≤ n`, from which it follows that the forward case of the
    proposition holds with `s≤s m≤n` as evidence that `suc m ≤ suc n`.

  + The flipped case of the inductive hypothesis holds with `n≤m` as
    evidence that `n ≤ m`, from which it follows that the flipped case of the
    proposition holds with `s≤s n≤m` as evidence that `suc n ≤ suc m`.

This is our first use of the `with` clause in Agda.  The keyword
`with` is followed by an expression and one or more subsequent lines.
Each line begins with an ellipsis (`...`) and a vertical bar (`|`),
followed by a pattern to be matched against the expression
and the right-hand side of the equation.

Every use of `with` is equivalent to defining a helper function.  For
example, the definition above is equivalent to the following.
<pre class="Agda">{% raw %}<a id="≤-total′"></a><a id="13957" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#13957" class="Function">≤-total′</a> <a id="13966" class="Symbol">:</a> <a id="13968" class="Symbol">∀</a> <a id="13970" class="Symbol">(</a><a id="13971" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#13971" class="Bound">m</a> <a id="13973" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#13973" class="Bound">n</a> <a id="13975" class="Symbol">:</a> <a id="13977" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a><a id="13978" class="Symbol">)</a> <a id="13980" class="Symbol">→</a> <a id="13982" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#10796" class="Datatype">Total</a> <a id="13988" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#13971" class="Bound">m</a> <a id="13990" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#13973" class="Bound">n</a>
<a id="13992" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#13957" class="Function">≤-total′</a> <a id="14001" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#115" class="InductiveConstructor">zero</a>    <a id="14009" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#14009" class="Bound">n</a>        <a id="14018" class="Symbol">=</a>  <a id="14021" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#10827" class="InductiveConstructor">forward</a> <a id="14029" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1441" class="InductiveConstructor">z≤n</a>
<a id="14033" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#13957" class="Function">≤-total′</a> <a id="14042" class="Symbol">(</a><a id="14043" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="14047" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#14047" class="Bound">m</a><a id="14048" class="Symbol">)</a> <a id="14050" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#115" class="InductiveConstructor">zero</a>     <a id="14059" class="Symbol">=</a>  <a id="14062" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#10884" class="InductiveConstructor">flipped</a> <a id="14070" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1441" class="InductiveConstructor">z≤n</a>
<a id="14074" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#13957" class="Function">≤-total′</a> <a id="14083" class="Symbol">(</a><a id="14084" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="14088" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#14088" class="Bound">m</a><a id="14089" class="Symbol">)</a> <a id="14091" class="Symbol">(</a><a id="14092" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="14096" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#14096" class="Bound">n</a><a id="14097" class="Symbol">)</a>  <a id="14100" class="Symbol">=</a>  <a id="14103" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#14135" class="Function">helper</a> <a id="14110" class="Symbol">(</a><a id="14111" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#13957" class="Function">≤-total′</a> <a id="14120" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#14088" class="Bound">m</a> <a id="14122" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#14096" class="Bound">n</a><a id="14123" class="Symbol">)</a>
  <a id="14127" class="Keyword">where</a>
  <a id="14135" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#14135" class="Function">helper</a> <a id="14142" class="Symbol">:</a> <a id="14144" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#10796" class="Datatype">Total</a> <a id="14150" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#14088" class="Bound">m</a> <a id="14152" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#14096" class="Bound">n</a> <a id="14154" class="Symbol">→</a> <a id="14156" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#10796" class="Datatype">Total</a> <a id="14162" class="Symbol">(</a><a id="14163" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="14167" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#14088" class="Bound">m</a><a id="14168" class="Symbol">)</a> <a id="14170" class="Symbol">(</a><a id="14171" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="14175" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#14096" class="Bound">n</a><a id="14176" class="Symbol">)</a>
  <a id="14180" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#14135" class="Function">helper</a> <a id="14187" class="Symbol">(</a><a id="14188" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#10827" class="InductiveConstructor">forward</a> <a id="14196" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#14196" class="Bound">m≤n</a><a id="14199" class="Symbol">)</a>  <a id="14202" class="Symbol">=</a>  <a id="14205" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#10827" class="InductiveConstructor">forward</a> <a id="14213" class="Symbol">(</a><a id="14214" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1490" class="InductiveConstructor">s≤s</a> <a id="14218" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#14196" class="Bound">m≤n</a><a id="14221" class="Symbol">)</a>
  <a id="14225" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#14135" class="Function">helper</a> <a id="14232" class="Symbol">(</a><a id="14233" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#10884" class="InductiveConstructor">flipped</a> <a id="14241" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#14241" class="Bound">n≤m</a><a id="14244" class="Symbol">)</a>  <a id="14247" class="Symbol">=</a>  <a id="14250" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#10884" class="InductiveConstructor">flipped</a> <a id="14258" class="Symbol">(</a><a id="14259" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1490" class="InductiveConstructor">s≤s</a> <a id="14263" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#14241" class="Bound">n≤m</a><a id="14266" class="Symbol">)</a>{% endraw %}</pre>
This is also our first use of a `where` clause in Agda.  The keyword `where` is
followed by one or more definitions, which must be indented.  Any variables
bound of the left-hand side of the preceding equation (in this case, `m` and
`n`) are in scope within the nested definition, and any identifiers bound in the
nested definition (in this case, `helper`) are in scope in the right-hand side
of the preceding equation.

If both arguments are equal, then both cases hold and we could return evidence
of either.  In the code above we return the forward case, but there is a
variant that returns the flipped case.
<pre class="Agda">{% raw %}<a id="≤-total″"></a><a id="14904" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#14904" class="Function">≤-total″</a> <a id="14913" class="Symbol">:</a> <a id="14915" class="Symbol">∀</a> <a id="14917" class="Symbol">(</a><a id="14918" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#14918" class="Bound">m</a> <a id="14920" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#14920" class="Bound">n</a> <a id="14922" class="Symbol">:</a> <a id="14924" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a><a id="14925" class="Symbol">)</a> <a id="14927" class="Symbol">→</a> <a id="14929" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#10796" class="Datatype">Total</a> <a id="14935" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#14918" class="Bound">m</a> <a id="14937" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#14920" class="Bound">n</a>
<a id="14939" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#14904" class="Function">≤-total″</a> <a id="14948" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#14948" class="Bound">m</a>       <a id="14956" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#115" class="InductiveConstructor">zero</a>                      <a id="14982" class="Symbol">=</a>  <a id="14985" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#10884" class="InductiveConstructor">flipped</a> <a id="14993" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1441" class="InductiveConstructor">z≤n</a>
<a id="14997" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#14904" class="Function">≤-total″</a> <a id="15006" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#115" class="InductiveConstructor">zero</a>    <a id="15014" class="Symbol">(</a><a id="15015" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="15019" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#15019" class="Bound">n</a><a id="15020" class="Symbol">)</a>                   <a id="15040" class="Symbol">=</a>  <a id="15043" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#10827" class="InductiveConstructor">forward</a> <a id="15051" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1441" class="InductiveConstructor">z≤n</a>
<a id="15055" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#14904" class="Function">≤-total″</a> <a id="15064" class="Symbol">(</a><a id="15065" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="15069" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#15069" class="Bound">m</a><a id="15070" class="Symbol">)</a> <a id="15072" class="Symbol">(</a><a id="15073" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="15077" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#15077" class="Bound">n</a><a id="15078" class="Symbol">)</a> <a id="15080" class="Keyword">with</a> <a id="15085" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#14904" class="Function">≤-total″</a> <a id="15094" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#15069" class="Bound">m</a> <a id="15096" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#15077" class="Bound">n</a>
<a id="15098" class="Symbol">...</a>                        <a id="15125" class="Symbol">|</a> <a id="15127" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#10827" class="InductiveConstructor">forward</a> <a id="15135" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#15135" class="Bound">m≤n</a>   <a id="15141" class="Symbol">=</a>  <a id="15144" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#10827" class="InductiveConstructor">forward</a> <a id="15152" class="Symbol">(</a><a id="15153" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1490" class="InductiveConstructor">s≤s</a> <a id="15157" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#15135" class="Bound">m≤n</a><a id="15160" class="Symbol">)</a>
<a id="15162" class="Symbol">...</a>                        <a id="15189" class="Symbol">|</a> <a id="15191" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#10884" class="InductiveConstructor">flipped</a> <a id="15199" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#15199" class="Bound">n≤m</a>   <a id="15205" class="Symbol">=</a>  <a id="15208" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#10884" class="InductiveConstructor">flipped</a> <a id="15216" class="Symbol">(</a><a id="15217" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1490" class="InductiveConstructor">s≤s</a> <a id="15221" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#15199" class="Bound">n≤m</a><a id="15224" class="Symbol">)</a>{% endraw %}</pre>
It differs from the original code in that it pattern
matches on the second argument before the first argument.


## Monotonicity

If one bumps into both an operator and an ordering at a party, one may ask if
the operator is _monotonic_ with regard to the ordering.  For example, addition
is monotonic with regard to inequality, meaning

    ∀ {m n p q : ℕ} → m ≤ n → p ≤ q → m + p ≤ n + q

The proof is straightforward using the techniques we have learned, and is best
broken into three parts. First, we deal with the special case of showing
addition is monotonic on the right.
<pre class="Agda">{% raw %}<a id="+-monoʳ-≤"></a><a id="15828" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#15828" class="Function">+-monoʳ-≤</a> <a id="15838" class="Symbol">:</a> <a id="15840" class="Symbol">∀</a> <a id="15842" class="Symbol">(</a><a id="15843" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#15843" class="Bound">m</a> <a id="15845" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#15845" class="Bound">p</a> <a id="15847" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#15847" class="Bound">q</a> <a id="15849" class="Symbol">:</a> <a id="15851" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a><a id="15852" class="Symbol">)</a>
  <a id="15856" class="Symbol">→</a> <a id="15858" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#15845" class="Bound">p</a> <a id="15860" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1414" class="Datatype Operator">≤</a> <a id="15862" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#15847" class="Bound">q</a>
    <a id="15868" class="Comment">-------------</a>
  <a id="15884" class="Symbol">→</a> <a id="15886" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#15843" class="Bound">m</a> <a id="15888" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="15890" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#15845" class="Bound">p</a> <a id="15892" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1414" class="Datatype Operator">≤</a> <a id="15894" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#15843" class="Bound">m</a> <a id="15896" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="15898" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#15847" class="Bound">q</a>
<a id="15900" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#15828" class="Function">+-monoʳ-≤</a> <a id="15910" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#115" class="InductiveConstructor">zero</a>    <a id="15918" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#15918" class="Bound">p</a> <a id="15920" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#15920" class="Bound">q</a> <a id="15922" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#15922" class="Bound">p≤q</a>  <a id="15927" class="Symbol">=</a>  <a id="15930" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#15922" class="Bound">p≤q</a>
<a id="15934" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#15828" class="Function">+-monoʳ-≤</a> <a id="15944" class="Symbol">(</a><a id="15945" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="15949" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#15949" class="Bound">m</a><a id="15950" class="Symbol">)</a> <a id="15952" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#15952" class="Bound">p</a> <a id="15954" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#15954" class="Bound">q</a> <a id="15956" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#15956" class="Bound">p≤q</a>  <a id="15961" class="Symbol">=</a>  <a id="15964" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1490" class="InductiveConstructor">s≤s</a> <a id="15968" class="Symbol">(</a><a id="15969" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#15828" class="Function">+-monoʳ-≤</a> <a id="15979" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#15949" class="Bound">m</a> <a id="15981" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#15952" class="Bound">p</a> <a id="15983" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#15954" class="Bound">q</a> <a id="15985" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#15956" class="Bound">p≤q</a><a id="15988" class="Symbol">)</a>{% endraw %}</pre>
The proof is by induction on the first argument.

* _Base case_: The first argument is `zero` in which case
  `zero + p ≤ zero + q` simplifies to `p ≤ q`, the evidence
  for which is given by the argument `p≤q`.

* _Inductive case_: The first argument is `suc m`, in which case
  `suc m + p ≤ suc m + q` simplifies to `suc (m + p) ≤ suc (m + q)`.
  The inductive hypothesis `+-monoʳ-≤ m p q p≤q` establishes that
  `m + p ≤ m + q`, and our goal follows by applying `s≤s`.

Second, we deal with the special case of showing addition is
monotonic on the left. This follows from the previous
result and the commutativity of addition.
<pre class="Agda">{% raw %}<a id="+-monoˡ-≤"></a><a id="16644" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#16644" class="Function">+-monoˡ-≤</a> <a id="16654" class="Symbol">:</a> <a id="16656" class="Symbol">∀</a> <a id="16658" class="Symbol">(</a><a id="16659" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#16659" class="Bound">m</a> <a id="16661" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#16661" class="Bound">n</a> <a id="16663" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#16663" class="Bound">p</a> <a id="16665" class="Symbol">:</a> <a id="16667" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a><a id="16668" class="Symbol">)</a>
  <a id="16672" class="Symbol">→</a> <a id="16674" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#16659" class="Bound">m</a> <a id="16676" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1414" class="Datatype Operator">≤</a> <a id="16678" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#16661" class="Bound">n</a>
    <a id="16684" class="Comment">-------------</a>
  <a id="16700" class="Symbol">→</a> <a id="16702" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#16659" class="Bound">m</a> <a id="16704" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="16706" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#16663" class="Bound">p</a> <a id="16708" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1414" class="Datatype Operator">≤</a> <a id="16710" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#16661" class="Bound">n</a> <a id="16712" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="16714" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#16663" class="Bound">p</a>
<a id="16716" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#16644" class="Function">+-monoˡ-≤</a> <a id="16726" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#16726" class="Bound">m</a> <a id="16728" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#16728" class="Bound">n</a> <a id="16730" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#16730" class="Bound">p</a> <a id="16732" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#16732" class="Bound">m≤n</a>  <a id="16737" class="Keyword">rewrite</a> <a id="16745" href="https://agda.github.io/agda-stdlib/Data.Nat.Properties.html#8011" class="Function">+-comm</a> <a id="16752" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#16726" class="Bound">m</a> <a id="16754" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#16730" class="Bound">p</a> <a id="16756" class="Symbol">|</a> <a id="16758" href="https://agda.github.io/agda-stdlib/Data.Nat.Properties.html#8011" class="Function">+-comm</a> <a id="16765" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#16728" class="Bound">n</a> <a id="16767" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#16730" class="Bound">p</a>  <a id="16770" class="Symbol">=</a> <a id="16772" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#15828" class="Function">+-monoʳ-≤</a> <a id="16782" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#16730" class="Bound">p</a> <a id="16784" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#16726" class="Bound">m</a> <a id="16786" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#16728" class="Bound">n</a> <a id="16788" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#16732" class="Bound">m≤n</a>{% endraw %}</pre>
Rewriting by `+-comm m p` and `+-comm n p` converts `m + p ≤ n + p` into
`p + m ≤ p + n`, which is proved by invoking `+-monoʳ-≤ p m n m≤n`.

Third, we combine the two previous results.
<pre class="Agda">{% raw %}<a id="+-mono-≤"></a><a id="17002" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#17002" class="Function">+-mono-≤</a> <a id="17011" class="Symbol">:</a> <a id="17013" class="Symbol">∀</a> <a id="17015" class="Symbol">(</a><a id="17016" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#17016" class="Bound">m</a> <a id="17018" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#17018" class="Bound">n</a> <a id="17020" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#17020" class="Bound">p</a> <a id="17022" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#17022" class="Bound">q</a> <a id="17024" class="Symbol">:</a> <a id="17026" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a><a id="17027" class="Symbol">)</a>
  <a id="17031" class="Symbol">→</a> <a id="17033" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#17016" class="Bound">m</a> <a id="17035" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1414" class="Datatype Operator">≤</a> <a id="17037" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#17018" class="Bound">n</a>
  <a id="17041" class="Symbol">→</a> <a id="17043" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#17020" class="Bound">p</a> <a id="17045" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1414" class="Datatype Operator">≤</a> <a id="17047" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#17022" class="Bound">q</a>
    <a id="17053" class="Comment">-------------</a>
  <a id="17069" class="Symbol">→</a> <a id="17071" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#17016" class="Bound">m</a> <a id="17073" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="17075" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#17020" class="Bound">p</a> <a id="17077" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1414" class="Datatype Operator">≤</a> <a id="17079" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#17018" class="Bound">n</a> <a id="17081" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="17083" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#17022" class="Bound">q</a>
<a id="17085" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#17002" class="Function">+-mono-≤</a> <a id="17094" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#17094" class="Bound">m</a> <a id="17096" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#17096" class="Bound">n</a> <a id="17098" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#17098" class="Bound">p</a> <a id="17100" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#17100" class="Bound">q</a> <a id="17102" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#17102" class="Bound">m≤n</a> <a id="17106" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#17106" class="Bound">p≤q</a>  <a id="17111" class="Symbol">=</a>  <a id="17114" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#7492" class="Function">≤-trans</a> <a id="17122" class="Symbol">(</a><a id="17123" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#16644" class="Function">+-monoˡ-≤</a> <a id="17133" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#17094" class="Bound">m</a> <a id="17135" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#17096" class="Bound">n</a> <a id="17137" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#17098" class="Bound">p</a> <a id="17139" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#17102" class="Bound">m≤n</a><a id="17142" class="Symbol">)</a> <a id="17144" class="Symbol">(</a><a id="17145" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#15828" class="Function">+-monoʳ-≤</a> <a id="17155" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#17096" class="Bound">n</a> <a id="17157" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#17098" class="Bound">p</a> <a id="17159" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#17100" class="Bound">q</a> <a id="17161" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#17106" class="Bound">p≤q</a><a id="17164" class="Symbol">)</a>{% endraw %}</pre>
Invoking `+-monoˡ-≤ m n p m≤n` proves `m + p ≤ n + p` and invoking
`+-monoʳ-≤ n p q p≤q` proves `n + p ≤ n + q`, and combining these with
transitivity proves `m + p ≤ n + q`, as was to be shown.


#### Exercise `*-mono-≤` (stretch)

Show that multiplication is monotonic with regard to inequality.


## Strict inequality {#strict-inequality}

We can define strict inequality similarly to inequality.
<pre class="Agda">{% raw %}<a id="17590" class="Keyword">infix</a> <a id="17596" class="Number">4</a> <a id="17598" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#17608" class="Datatype Operator">_&lt;_</a>

<a id="17603" class="Keyword">data</a> <a id="_&lt;_"></a><a id="17608" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#17608" class="Datatype Operator">_&lt;_</a> <a id="17612" class="Symbol">:</a> <a id="17614" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a> <a id="17616" class="Symbol">→</a> <a id="17618" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a> <a id="17620" class="Symbol">→</a> <a id="17622" class="PrimitiveType">Set</a> <a id="17626" class="Keyword">where</a>

  <a id="_&lt;_.z&lt;s"></a><a id="17635" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#17635" class="InductiveConstructor">z&lt;s</a> <a id="17639" class="Symbol">:</a> <a id="17641" class="Symbol">∀</a> <a id="17643" class="Symbol">{</a><a id="17644" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#17644" class="Bound">n</a> <a id="17646" class="Symbol">:</a> <a id="17648" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a><a id="17649" class="Symbol">}</a>
      <a id="17657" class="Comment">------------</a>
    <a id="17674" class="Symbol">→</a> <a id="17676" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#115" class="InductiveConstructor">zero</a> <a id="17681" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#17608" class="Datatype Operator">&lt;</a> <a id="17683" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="17687" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#17644" class="Bound">n</a>

  <a id="_&lt;_.s&lt;s"></a><a id="17692" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#17692" class="InductiveConstructor">s&lt;s</a> <a id="17696" class="Symbol">:</a> <a id="17698" class="Symbol">∀</a> <a id="17700" class="Symbol">{</a><a id="17701" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#17701" class="Bound">m</a> <a id="17703" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#17703" class="Bound">n</a> <a id="17705" class="Symbol">:</a> <a id="17707" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a><a id="17708" class="Symbol">}</a>
    <a id="17714" class="Symbol">→</a> <a id="17716" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#17701" class="Bound">m</a> <a id="17718" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#17608" class="Datatype Operator">&lt;</a> <a id="17720" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#17703" class="Bound">n</a>
      <a id="17728" class="Comment">-------------</a>
    <a id="17746" class="Symbol">→</a> <a id="17748" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="17752" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#17701" class="Bound">m</a> <a id="17754" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#17608" class="Datatype Operator">&lt;</a> <a id="17756" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="17760" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#17703" class="Bound">n</a>{% endraw %}</pre>
The key difference is that zero is less than the successor of an
arbitrary number, but is not less than zero.

Clearly, strict inequality is not reflexive. However it is
_irreflexive_ in that `n < n` never holds for any value of `n`.
Like inequality, strict inequality is transitive.
Strict inequality is not total, but satisfies the closely related property of
_trichotomy_: for any `m` and `n`, exactly one of `m < n`, `m ≡ n`, or `m > n`
holds (where we define `m > n` to hold exactly when `n < m`).
It is also monotonic with regards to addition and multiplication.

Most of the above are considered in exercises below.  Irreflexivity
requires negation, as does the fact that the three cases in
trichotomy are mutually exclusive, so those points are deferred to
Chapter [Negation]({{ site.baseurl }}{% link out/plfa/Negation.md%}).

It is straightforward to show that `suc m ≤ n` implies `m < n`,
and conversely.  One can then give an alternative derivation of the
properties of strict inequality, such as transitivity, by directly
exploiting the corresponding properties of inequality.

#### Exercise `<-trans` (recommended) {#less-trans}

Show that strict inequality is transitive.

#### Exercise `trichotomy` {#trichotomy}

Show that strict inequality satisfies a weak version of trichotomy, in
the sense that for any `m` and `n` that one of the following holds:
  * `m < n`,
  * `m ≡ n`, or
  * `m > n`
Define `m > n` to be the same as `n < m`.
You will need a suitable data declaration,
similar to that used for totality.
(We will show that the three cases are exclusive after we introduce
[negation]({{ site.baseurl }}{% link out/plfa/Negation.md%}).)

#### Exercise `+-mono-<` {#plus-mono-less}

Show that addition is monotonic with respect to strict inequality.
As with inequality, some additional definitions may be required.

#### Exercise `≤-iff-<` (recommended) {#leq-iff-less}

Show that `suc m ≤ n` implies `m < n`, and conversely.

#### Exercise `<-trans-revisited` {#less-trans-revisited}

Give an alternative proof that strict inequality is transitive,
using the relating between strict inequality and inequality and
the fact that inequality is transitive.


## Even and odd

As a further example, let's specify even and odd numbers.  Inequality
and strict inequality are _binary relations_, while even and odd are
_unary relations_, sometimes called _predicates_.
<pre class="Agda">{% raw %}<a id="20101" class="Keyword">data</a> <a id="even"></a><a id="20106" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#20106" class="Datatype">even</a> <a id="20111" class="Symbol">:</a> <a id="20113" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a> <a id="20115" class="Symbol">→</a> <a id="20117" class="PrimitiveType">Set</a>
<a id="20121" class="Keyword">data</a> <a id="odd"></a><a id="20126" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#20126" class="Datatype">odd</a>  <a id="20131" class="Symbol">:</a> <a id="20133" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a> <a id="20135" class="Symbol">→</a> <a id="20137" class="PrimitiveType">Set</a>

<a id="20142" class="Keyword">data</a> <a id="20147" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#20106" class="Datatype">even</a> <a id="20152" class="Keyword">where</a>

  <a id="even.zero"></a><a id="20161" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#20161" class="InductiveConstructor">zero</a> <a id="20166" class="Symbol">:</a>
      <a id="20174" class="Comment">---------</a>
      <a id="20190" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#20106" class="Datatype">even</a> <a id="20195" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#115" class="InductiveConstructor">zero</a>

  <a id="even.suc"></a><a id="20203" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#20203" class="InductiveConstructor">suc</a>  <a id="20208" class="Symbol">:</a> <a id="20210" class="Symbol">∀</a> <a id="20212" class="Symbol">{</a><a id="20213" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#20213" class="Bound">n</a> <a id="20215" class="Symbol">:</a> <a id="20217" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a><a id="20218" class="Symbol">}</a>
    <a id="20224" class="Symbol">→</a> <a id="20226" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#20126" class="Datatype">odd</a> <a id="20230" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#20213" class="Bound">n</a>
      <a id="20238" class="Comment">------------</a>
    <a id="20255" class="Symbol">→</a> <a id="20257" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#20106" class="Datatype">even</a> <a id="20262" class="Symbol">(</a><a id="20263" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="20267" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#20213" class="Bound">n</a><a id="20268" class="Symbol">)</a>

<a id="20271" class="Keyword">data</a> <a id="20276" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#20126" class="Datatype">odd</a> <a id="20280" class="Keyword">where</a>

  <a id="odd.suc"></a><a id="20289" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#20289" class="InductiveConstructor">suc</a>   <a id="20295" class="Symbol">:</a> <a id="20297" class="Symbol">∀</a> <a id="20299" class="Symbol">{</a><a id="20300" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#20300" class="Bound">n</a> <a id="20302" class="Symbol">:</a> <a id="20304" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a><a id="20305" class="Symbol">}</a>
    <a id="20311" class="Symbol">→</a> <a id="20313" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#20106" class="Datatype">even</a> <a id="20318" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#20300" class="Bound">n</a>
      <a id="20326" class="Comment">-----------</a>
    <a id="20342" class="Symbol">→</a> <a id="20344" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#20126" class="Datatype">odd</a> <a id="20348" class="Symbol">(</a><a id="20349" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="20353" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#20300" class="Bound">n</a><a id="20354" class="Symbol">)</a>{% endraw %}</pre>
A number is even if it is zero or the successor of an odd number,
and odd if it is the successor of an even number.

This is our first use of a mutually recursive datatype declaration.
Since each identifier must be defined before it is used, we first
declare the indexed types `even` and `odd` (omitting the `where`
keyword and the declarations of the constructors) and then
declare the constructors (omitting the signatures `ℕ → Set`
which were given earlier).

This is also our first use of _overloaded_ constructors,
that is, using the same name for constructors of different types.
Here `suc` means one of three constructors:

    suc : ℕ → ℕ

    suc : ∀ {n : ℕ}
      → odd n
        ------------
      → even (suc n)

    suc : ∀ {n : ℕ}
      → even n
        -----------
      → odd (suc n)

Similarly, `zero` refers to one of two constructors. Due to how it
does type inference, Agda does not allow overloading of defined names,
but does allow overloading of constructors.  It is recommended that
one restrict overloading to related meanings, as we have done here,
but it is not required.

We show that the sum of two even numbers is even.
<pre class="Agda">{% raw %}<a id="e+e≡e"></a><a id="21530" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#21530" class="Function">e+e≡e</a> <a id="21536" class="Symbol">:</a> <a id="21538" class="Symbol">∀</a> <a id="21540" class="Symbol">{</a><a id="21541" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#21541" class="Bound">m</a> <a id="21543" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#21543" class="Bound">n</a> <a id="21545" class="Symbol">:</a> <a id="21547" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a><a id="21548" class="Symbol">}</a>
  <a id="21552" class="Symbol">→</a> <a id="21554" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#20106" class="Datatype">even</a> <a id="21559" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#21541" class="Bound">m</a>
  <a id="21563" class="Symbol">→</a> <a id="21565" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#20106" class="Datatype">even</a> <a id="21570" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#21543" class="Bound">n</a>
    <a id="21576" class="Comment">------------</a>
  <a id="21591" class="Symbol">→</a> <a id="21593" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#20106" class="Datatype">even</a> <a id="21598" class="Symbol">(</a><a id="21599" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#21541" class="Bound">m</a> <a id="21601" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="21603" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#21543" class="Bound">n</a><a id="21604" class="Symbol">)</a>

<a id="o+e≡o"></a><a id="21607" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#21607" class="Function">o+e≡o</a> <a id="21613" class="Symbol">:</a> <a id="21615" class="Symbol">∀</a> <a id="21617" class="Symbol">{</a><a id="21618" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#21618" class="Bound">m</a> <a id="21620" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#21620" class="Bound">n</a> <a id="21622" class="Symbol">:</a> <a id="21624" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a><a id="21625" class="Symbol">}</a>
  <a id="21629" class="Symbol">→</a> <a id="21631" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#20126" class="Datatype">odd</a> <a id="21635" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#21618" class="Bound">m</a>
  <a id="21639" class="Symbol">→</a> <a id="21641" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#20106" class="Datatype">even</a> <a id="21646" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#21620" class="Bound">n</a>
    <a id="21652" class="Comment">-----------</a>
  <a id="21666" class="Symbol">→</a> <a id="21668" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#20126" class="Datatype">odd</a> <a id="21672" class="Symbol">(</a><a id="21673" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#21618" class="Bound">m</a> <a id="21675" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="21677" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#21620" class="Bound">n</a><a id="21678" class="Symbol">)</a>

<a id="21681" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#21530" class="Function">e+e≡e</a> <a id="21687" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#20161" class="InductiveConstructor">zero</a>     <a id="21696" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#21696" class="Bound">en</a>  <a id="21700" class="Symbol">=</a>  <a id="21703" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#21696" class="Bound">en</a>
<a id="21706" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#21530" class="Function">e+e≡e</a> <a id="21712" class="Symbol">(</a><a id="21713" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#20203" class="InductiveConstructor">suc</a> <a id="21717" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#21717" class="Bound">om</a><a id="21719" class="Symbol">)</a> <a id="21721" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#21721" class="Bound">en</a>  <a id="21725" class="Symbol">=</a>  <a id="21728" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#20203" class="InductiveConstructor">suc</a> <a id="21732" class="Symbol">(</a><a id="21733" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#21607" class="Function">o+e≡o</a> <a id="21739" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#21717" class="Bound">om</a> <a id="21742" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#21721" class="Bound">en</a><a id="21744" class="Symbol">)</a>

<a id="21747" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#21607" class="Function">o+e≡o</a> <a id="21753" class="Symbol">(</a><a id="21754" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#20289" class="InductiveConstructor">suc</a> <a id="21758" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#21758" class="Bound">em</a><a id="21760" class="Symbol">)</a> <a id="21762" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#21762" class="Bound">en</a>  <a id="21766" class="Symbol">=</a>  <a id="21769" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#20289" class="InductiveConstructor">suc</a> <a id="21773" class="Symbol">(</a><a id="21774" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#21530" class="Function">e+e≡e</a> <a id="21780" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#21758" class="Bound">em</a> <a id="21783" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#21762" class="Bound">en</a><a id="21785" class="Symbol">)</a>{% endraw %}</pre>
Corresponding to the mutually recursive types, we use two mutually recursive
functions, one to show that the sum of two even numbers is even, and the other
to show that the sum of an odd and an even number is odd.

This is our first use of mutually recursive functions.  Since each identifier
must be defined before it is used, we first give the signatures for both
functions and then the equations that define them.

To show that the sum of two even numbers is even, consider the
evidence that the first number is even. If it is because it is zero,
then the sum is even because the second number is even.  If it is
because it is the successor of an odd number, then the result is even
because it is the successor of the sum of an odd and an even number,
which is odd.

To show that the sum of an odd and even number is odd, consider the
evidence that the first number is odd. If it is because it is the
successor of an even number, then the result is odd because it is the
successor of the sum of two even numbers, which is even.

#### Exercise `o+o≡e` (stretch) {#odd-plus-odd}

Show that the sum of two odd numbers is even.

#### Exercise `Bin-predicates` (stretch) {#Bin-predicates}

Recall that 
Exercise [Bin]({{ site.baseurl }}{% link out/plfa/Naturals.md%}#Bin)
defines a datatype `Bin` of bitstrings representing natural numbers.
Representations are not unique due to leading zeros.
Hence, eleven may be represented by both of the following

    x1 x1 x0 x1 nil
    x1 x1 x0 x1 x0 x0 nil

Define a predicate

    Can : Bin → Set

over all bitstrings that holds if the bitstring is canonical, meaning
it has no leading zeros; the first representation of eleven above is
canonical, and the second is not.  To define it, you will need an
auxiliary predicate

    One : Bin → Set

that holds only if the bistring has a leading one.  A bitstring is
canonical if it has a leading one (representing a positive number) or
if it consists of a single zero (representing zero).

Show that increment preserves canonical bitstrings.

    Can x
    ------------
    Can (inc x)

Show that converting a natural to a bitstring always yields a
canonical bitstring.

    ----------
    Can (to n)

Show that converting a canonical bitstring to a natural
and back is the identity.

    Can x
    ---------------
    to (from x) ≡ x

(Hint: For each of these, you may first need to prove related
properties of `One`.)

## Standard prelude

Definitions similar to those in this chapter can be found in the standard library.
<pre class="Agda">{% raw %}<a id="24288" class="Keyword">import</a> <a id="24295" href="https://agda.github.io/agda-stdlib/Data.Nat.html" class="Module">Data.Nat</a> <a id="24304" class="Keyword">using</a> <a id="24310" class="Symbol">(</a><a id="24311" href="https://agda.github.io/agda-stdlib/Data.Nat.Base.html#742" class="Datatype Operator">_≤_</a><a id="24314" class="Symbol">;</a> <a id="24316" href="https://agda.github.io/agda-stdlib/Data.Nat.Base.html#765" class="InductiveConstructor">z≤n</a><a id="24319" class="Symbol">;</a> <a id="24321" href="https://agda.github.io/agda-stdlib/Data.Nat.Base.html#807" class="InductiveConstructor">s≤s</a><a id="24324" class="Symbol">)</a>
<a id="24326" class="Keyword">import</a> <a id="24333" href="https://agda.github.io/agda-stdlib/Data.Nat.Properties.html" class="Module">Data.Nat.Properties</a> <a id="24353" class="Keyword">using</a> <a id="24359" class="Symbol">(</a><a id="24360" href="https://agda.github.io/agda-stdlib/Data.Nat.Properties.html#1804" class="Function">≤-refl</a><a id="24366" class="Symbol">;</a> <a id="24368" href="https://agda.github.io/agda-stdlib/Data.Nat.Properties.html#1997" class="Function">≤-trans</a><a id="24375" class="Symbol">;</a> <a id="24377" href="https://agda.github.io/agda-stdlib/Data.Nat.Properties.html#1854" class="Function">≤-antisym</a><a id="24386" class="Symbol">;</a> <a id="24388" href="https://agda.github.io/agda-stdlib/Data.Nat.Properties.html#2109" class="Function">≤-total</a><a id="24395" class="Symbol">;</a>
                                  <a id="24431" href="https://agda.github.io/agda-stdlib/Data.Nat.Properties.html#10952" class="Function">+-monoʳ-≤</a><a id="24440" class="Symbol">;</a> <a id="24442" href="https://agda.github.io/agda-stdlib/Data.Nat.Properties.html#10862" class="Function">+-monoˡ-≤</a><a id="24451" class="Symbol">;</a> <a id="24453" href="https://agda.github.io/agda-stdlib/Data.Nat.Properties.html#10706" class="Function">+-mono-≤</a><a id="24461" class="Symbol">)</a>{% endraw %}</pre>
In the standard library, `≤-total` is formalised in terms of
disjunction (which we define in
Chapter [Connectives]({{ site.baseurl }}{% link out/plfa/Connectives.md%})),
and `+-monoʳ-≤`, `+-monoˡ-≤`, `+-mono-≤` are proved differently than here,
and more arguments are implicit.


## Unicode

This chapter uses the following unicode.

    ≤  U+2264  LESS-THAN OR EQUAL TO (\<=, \le)
    ≥  U+2265  GREATER-THAN OR EQUAL TO (\>=, \ge)
    ˡ  U+02E1  MODIFIER LETTER SMALL L (\^l)
    ʳ  U+02B3  MODIFIER LETTER SMALL R (\^r)

The commands `\^l` and `\^r` give access to a variety of superscript
leftward and rightward arrows in addition to superscript letters `l` and `r`.
