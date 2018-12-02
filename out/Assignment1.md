---
src       : tspl/Assignment1.lagda
title     : "Assignment1: TSPL Assignment 1"
layout    : page
permalink : /Assignment1/
---

<pre class="Agda">{% raw %}<a id="111" class="Keyword">module</a> <a id="118" href="{% endraw %}{{ site.baseurl }}{% link out/Assignment1.md %}{% raw %}" class="Module">Assignment1</a> <a id="130" class="Keyword">where</a>{% endraw %}</pre>

## YOUR NAME AND EMAIL GOES HERE

## Introduction

This assignment is due **4pm Thursday 4 October** (Week 3).

You must do _all_ the exercises labelled "(recommended)".

Exercises labelled "(stretch)" are there to provide an extra challenge.
You don't need to do all of these, but should attempt at least a few.

Exercises without a label are optional, and may be done if you want
some extra practice.

Submit your homework using the "submit" command.
Please ensure your files execute correctly under Agda!

## Imports

<pre class="Agda">{% raw %}<a id="682" class="Keyword">import</a> <a id="689" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html" class="Module">Relation.Binary.PropositionalEquality</a> <a id="727" class="Symbol">as</a> <a id="730" class="Module">Eq</a>
<a id="733" class="Keyword">open</a> <a id="738" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html" class="Module">Eq</a> <a id="741" class="Keyword">using</a> <a id="747" class="Symbol">(</a><a id="748" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator">_≡_</a><a id="751" class="Symbol">;</a> <a id="753" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor">refl</a><a id="757" class="Symbol">;</a> <a id="759" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#1056" class="Function">cong</a><a id="763" class="Symbol">;</a> <a id="765" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.Core.html#838" class="Function">sym</a><a id="768" class="Symbol">)</a>
<a id="770" class="Keyword">open</a> <a id="775" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#3840" class="Module">Eq.≡-Reasoning</a> <a id="790" class="Keyword">using</a> <a id="796" class="Symbol">(</a><a id="797" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#3941" class="Function Operator">begin_</a><a id="803" class="Symbol">;</a> <a id="805" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#3999" class="Function Operator">_≡⟨⟩_</a><a id="810" class="Symbol">;</a> <a id="812" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#4058" class="Function Operator">_≡⟨_⟩_</a><a id="818" class="Symbol">;</a> <a id="820" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#4239" class="Function Operator">_∎</a><a id="822" class="Symbol">)</a>
<a id="824" class="Keyword">open</a> <a id="829" class="Keyword">import</a> <a id="836" href="https://agda.github.io/agda-stdlib/Data.Nat.html" class="Module">Data.Nat</a> <a id="845" class="Keyword">using</a> <a id="851" class="Symbol">(</a><a id="852" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a><a id="853" class="Symbol">;</a> <a id="855" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#115" class="InductiveConstructor">zero</a><a id="859" class="Symbol">;</a> <a id="861" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a><a id="864" class="Symbol">;</a> <a id="866" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">_+_</a><a id="869" class="Symbol">;</a> <a id="871" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#433" class="Primitive Operator">_*_</a><a id="874" class="Symbol">;</a> <a id="876" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#320" class="Primitive Operator">_∸_</a><a id="879" class="Symbol">;</a> <a id="881" href="https://agda.github.io/agda-stdlib/Data.Nat.Base.html#742" class="Datatype Operator">_≤_</a><a id="884" class="Symbol">;</a> <a id="886" href="https://agda.github.io/agda-stdlib/Data.Nat.Base.html#765" class="InductiveConstructor">z≤n</a><a id="889" class="Symbol">;</a> <a id="891" href="https://agda.github.io/agda-stdlib/Data.Nat.Base.html#807" class="InductiveConstructor">s≤s</a><a id="894" class="Symbol">)</a>
<a id="896" class="Keyword">open</a> <a id="901" class="Keyword">import</a> <a id="908" href="https://agda.github.io/agda-stdlib/Data.Nat.Properties.html" class="Module">Data.Nat.Properties</a> <a id="928" class="Keyword">using</a> <a id="934" class="Symbol">(</a><a id="935" href="https://agda.github.io/agda-stdlib/Data.Nat.Properties.html#7678" class="Function">+-assoc</a><a id="942" class="Symbol">;</a> <a id="944" href="https://agda.github.io/agda-stdlib/Data.Nat.Properties.html#7834" class="Function">+-identityʳ</a><a id="955" class="Symbol">;</a> <a id="957" href="https://agda.github.io/agda-stdlib/Data.Nat.Properties.html#7575" class="Function">+-suc</a><a id="962" class="Symbol">;</a> <a id="964" href="https://agda.github.io/agda-stdlib/Data.Nat.Properties.html#8011" class="Function">+-comm</a><a id="970" class="Symbol">;</a>
  <a id="974" href="https://agda.github.io/agda-stdlib/Data.Nat.Properties.html#1804" class="Function">≤-refl</a><a id="980" class="Symbol">;</a> <a id="982" href="https://agda.github.io/agda-stdlib/Data.Nat.Properties.html#1997" class="Function">≤-trans</a><a id="989" class="Symbol">;</a> <a id="991" href="https://agda.github.io/agda-stdlib/Data.Nat.Properties.html#1854" class="Function">≤-antisym</a><a id="1000" class="Symbol">;</a> <a id="1002" href="https://agda.github.io/agda-stdlib/Data.Nat.Properties.html#2109" class="Function">≤-total</a><a id="1009" class="Symbol">;</a> <a id="1011" href="https://agda.github.io/agda-stdlib/Data.Nat.Properties.html#10952" class="Function">+-monoʳ-≤</a><a id="1020" class="Symbol">;</a> <a id="1022" href="https://agda.github.io/agda-stdlib/Data.Nat.Properties.html#10862" class="Function">+-monoˡ-≤</a><a id="1031" class="Symbol">;</a> <a id="1033" href="https://agda.github.io/agda-stdlib/Data.Nat.Properties.html#10706" class="Function">+-mono-≤</a><a id="1041" class="Symbol">)</a>
<a id="1043" class="Keyword">open</a> <a id="1048" class="Keyword">import</a> <a id="1055" href="plfa.Relations.html" class="Module">plfa.Relations</a> <a id="1070" class="Keyword">using</a> <a id="1076" class="Symbol">(</a><a id="1077" href="plfa.Relations.html#17608" class="Datatype Operator">_&lt;_</a><a id="1080" class="Symbol">;</a> <a id="1082" href="plfa.Relations.html#17635" class="InductiveConstructor">z&lt;s</a><a id="1085" class="Symbol">;</a> <a id="1087" href="plfa.Relations.html#17692" class="InductiveConstructor">s&lt;s</a><a id="1090" class="Symbol">;</a> <a id="1092" href="plfa.Relations.html#20161" class="InductiveConstructor">zero</a><a id="1096" class="Symbol">;</a> <a id="1098" href="plfa.Relations.html#20203" class="InductiveConstructor">suc</a><a id="1101" class="Symbol">;</a> <a id="1103" href="plfa.Relations.html#20106" class="Datatype">even</a><a id="1107" class="Symbol">;</a> <a id="1109" href="plfa.Relations.html#20126" class="Datatype">odd</a><a id="1112" class="Symbol">)</a>{% endraw %}</pre>

## Naturals

#### Exercise `seven` {#seven}

Write out `7` in longhand.


#### Exercise `+-example` {#plus-example}

Compute `3 + 4`, writing out your reasoning as a chain of equations.


#### Exercise `*-example` {#times-example}

Compute `3 * 4`, writing out your reasoning as a chain of equations.


#### Exercise `_^_` (recommended) {#power}

Define exponentiation, which is given by the following equations.

    n ^ 0        =  1
    n ^ (1 + m)  =  n * (n ^ m)

Check that `3 ^ 4` is `81`.


#### Exercise `∸-examples` (recommended) {#monus-examples}

Compute `5 ∸ 3` and `3 ∸ 5`, writing out your reasoning as a chain of equations.


#### Exercise `Bin` (stretch) {#Bin}

A more efficient representation of natural numbers uses a binary
rather than a unary system.  We represent a number as a bitstring.
<pre class="Agda">{% raw %}<a id="1951" class="Keyword">data</a> <a id="Bin"></a><a id="1956" href="{% endraw %}{{ site.baseurl }}{% link out/Assignment1.md %}{% raw %}#1956" class="Datatype">Bin</a> <a id="1960" class="Symbol">:</a> <a id="1962" class="PrimitiveType">Set</a> <a id="1966" class="Keyword">where</a>
  <a id="Bin.nil"></a><a id="1974" href="{% endraw %}{{ site.baseurl }}{% link out/Assignment1.md %}{% raw %}#1974" class="InductiveConstructor">nil</a> <a id="1978" class="Symbol">:</a> <a id="1980" href="{% endraw %}{{ site.baseurl }}{% link out/Assignment1.md %}{% raw %}#1956" class="Datatype">Bin</a>
  <a id="Bin.x0_"></a><a id="1986" href="{% endraw %}{{ site.baseurl }}{% link out/Assignment1.md %}{% raw %}#1986" class="InductiveConstructor Operator">x0_</a> <a id="1990" class="Symbol">:</a> <a id="1992" href="{% endraw %}{{ site.baseurl }}{% link out/Assignment1.md %}{% raw %}#1956" class="Datatype">Bin</a> <a id="1996" class="Symbol">→</a> <a id="1998" href="{% endraw %}{{ site.baseurl }}{% link out/Assignment1.md %}{% raw %}#1956" class="Datatype">Bin</a>
  <a id="Bin.x1_"></a><a id="2004" href="{% endraw %}{{ site.baseurl }}{% link out/Assignment1.md %}{% raw %}#2004" class="InductiveConstructor Operator">x1_</a> <a id="2008" class="Symbol">:</a> <a id="2010" href="{% endraw %}{{ site.baseurl }}{% link out/Assignment1.md %}{% raw %}#1956" class="Datatype">Bin</a> <a id="2014" class="Symbol">→</a> <a id="2016" href="{% endraw %}{{ site.baseurl }}{% link out/Assignment1.md %}{% raw %}#1956" class="Datatype">Bin</a>{% endraw %}</pre>
For instance, the bitstring

    1011

standing for the number eleven is encoded, right to left, as

    x1 x1 x0 x1 nil

Representations are not unique due to leading zeros.
Hence, eleven is also represented by `001011`, encoded as

    x1 x1 x0 x1 x0 x0 nil

Define a function

    inc : Bin → Bin

that converts a bitstring to the bitstring for the next higher
number.  For example, since `1100` encodes twelve, we should have

    inc (x1 x1 x0 x1 nil) ≡ x0 x0 x1 x1 nil

Confirm that this gives the correct answer for the bitstrings
encoding zero through four.

Using the above, define a pair of functions to convert
between the two representations.

    to   : ℕ → Bin
    from : Bin → ℕ

For the former, choose the bitstring to have no leading zeros if it
represents a positive natural, and represent zero by `x0 nil`.
Confirm that these both give the correct answer for zero through four.

## Induction

#### Exercise `operators` {#operators}

Give another example of a pair of operators that have an identity
and are associative, commutative, and distribute over one another.

Give an example of an operator that has an identity and is
associative but is not commutative.


#### Exercise `finite-+-assoc` (stretch) {#finite-plus-assoc}

Write out what is known about associativity of addition on each of the first four
days using a finite story of creation, as
[earlier][plfa.Naturals#finite-creation]


#### Exercise `+-swap` (recommended) {#plus-swap} 

Show

    m + (n + p) ≡ n + (m + p)

for all naturals `m`, `n`, and `p`. No induction is needed,
just apply the previous results which show addition
is associative and commutative.  You may need to use
the following function from the standard library:

    sym : ∀ {m n : ℕ} → m ≡ n → n ≡ m

<pre class="Agda">{% raw %}<a id="swap"></a><a id="3801" href="{% endraw %}{{ site.baseurl }}{% link out/Assignment1.md %}{% raw %}#3801" class="Function">swap</a> <a id="3806" class="Symbol">:</a> <a id="3808" class="Symbol">∀</a> <a id="3810" class="Symbol">(</a><a id="3811" href="{% endraw %}{{ site.baseurl }}{% link out/Assignment1.md %}{% raw %}#3811" class="Bound">m</a> <a id="3813" href="{% endraw %}{{ site.baseurl }}{% link out/Assignment1.md %}{% raw %}#3813" class="Bound">n</a> <a id="3815" href="{% endraw %}{{ site.baseurl }}{% link out/Assignment1.md %}{% raw %}#3815" class="Bound">p</a> <a id="3817" class="Symbol">:</a> <a id="3819" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a><a id="3820" class="Symbol">)</a> <a id="3822" class="Symbol">→</a> <a id="3824" href="{% endraw %}{{ site.baseurl }}{% link out/Assignment1.md %}{% raw %}#3811" class="Bound">m</a> <a id="3826" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="3828" class="Symbol">(</a><a id="3829" href="{% endraw %}{{ site.baseurl }}{% link out/Assignment1.md %}{% raw %}#3813" class="Bound">n</a> <a id="3831" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="3833" href="{% endraw %}{{ site.baseurl }}{% link out/Assignment1.md %}{% raw %}#3815" class="Bound">p</a><a id="3834" class="Symbol">)</a> <a id="3836" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator">≡</a> <a id="3838" href="{% endraw %}{{ site.baseurl }}{% link out/Assignment1.md %}{% raw %}#3813" class="Bound">n</a> <a id="3840" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="3842" class="Symbol">(</a><a id="3843" href="{% endraw %}{{ site.baseurl }}{% link out/Assignment1.md %}{% raw %}#3811" class="Bound">m</a> <a id="3845" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="3847" href="{% endraw %}{{ site.baseurl }}{% link out/Assignment1.md %}{% raw %}#3815" class="Bound">p</a><a id="3848" class="Symbol">)</a>
<a id="3850" href="{% endraw %}{{ site.baseurl }}{% link out/Assignment1.md %}{% raw %}#3801" class="Function">swap</a> <a id="3855" href="{% endraw %}{{ site.baseurl }}{% link out/Assignment1.md %}{% raw %}#3855" class="Bound">m</a> <a id="3857" href="{% endraw %}{{ site.baseurl }}{% link out/Assignment1.md %}{% raw %}#3857" class="Bound">n</a> <a id="3859" href="{% endraw %}{{ site.baseurl }}{% link out/Assignment1.md %}{% raw %}#3859" class="Bound">p</a> <a id="3861" class="Keyword">rewrite</a> <a id="3869" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.Core.html#838" class="Function">sym</a> <a id="3873" class="Symbol">(</a><a id="3874" href="https://agda.github.io/agda-stdlib/Data.Nat.Properties.html#7678" class="Function">+-assoc</a> <a id="3882" href="{% endraw %}{{ site.baseurl }}{% link out/Assignment1.md %}{% raw %}#3855" class="Bound">m</a> <a id="3884" href="{% endraw %}{{ site.baseurl }}{% link out/Assignment1.md %}{% raw %}#3857" class="Bound">n</a> <a id="3886" href="{% endraw %}{{ site.baseurl }}{% link out/Assignment1.md %}{% raw %}#3859" class="Bound">p</a><a id="3887" class="Symbol">)</a> <a id="3889" class="Symbol">|</a> <a id="3891" href="https://agda.github.io/agda-stdlib/Data.Nat.Properties.html#8011" class="Function">+-comm</a> <a id="3898" href="{% endraw %}{{ site.baseurl }}{% link out/Assignment1.md %}{% raw %}#3855" class="Bound">m</a> <a id="3900" href="{% endraw %}{{ site.baseurl }}{% link out/Assignment1.md %}{% raw %}#3857" class="Bound">n</a> <a id="3902" class="Symbol">|</a> <a id="3904" href="https://agda.github.io/agda-stdlib/Data.Nat.Properties.html#7678" class="Function">+-assoc</a> <a id="3912" href="{% endraw %}{{ site.baseurl }}{% link out/Assignment1.md %}{% raw %}#3857" class="Bound">n</a> <a id="3914" href="{% endraw %}{{ site.baseurl }}{% link out/Assignment1.md %}{% raw %}#3855" class="Bound">m</a> <a id="3916" href="{% endraw %}{{ site.baseurl }}{% link out/Assignment1.md %}{% raw %}#3859" class="Bound">p</a> <a id="3918" class="Symbol">=</a> <a id="3920" class="Symbol">{!!}</a>{% endraw %}</pre>

#### Exercise `*-distrib-+` (recommended) {#times-distrib-plus}

Show multiplication distributes over addition, that is,

    (m + n) * p ≡ m * p + n * p

for all naturals `m`, `n`, and `p`.

#### Exercise `*-assoc` (recommended) {#times-assoc}

Show multiplication is associative, that is,

    (m * n) * p ≡ m * (n * p)

for all naturals `m`, `n`, and `p`.

#### Exercise `*-comm` {#times-comm}

Show multiplication is commutative, that is,

    m * n ≡ n * m

for all naturals `m` and `n`.  As with commutativity of addition,
you will need to formulate and prove suitable lemmas.

#### Exercise `0∸n≡0` {#zero-monus}

Show

    zero ∸ n ≡ zero

for all naturals `n`. Did your proof require induction?

#### Exercise `∸-+-assoc` {#monus-plus-assoc}

Show that monus associates with addition, that is,

    m ∸ n ∸ p ≡ m ∸ (n + p)

for all naturals `m`, `n`, and `p`.

#### Exercise `Bin-laws` (stretch) {#Bin-laws}

Recall that 
Exercise [Bin][plfa.Naturals#Bin]
defines a datatype `Bin` of bitstrings representing natural numbers
and asks you to define functions

    inc   : Bin → Bin
    to    : ℕ → Bin
    from  : Bin → ℕ

Consider the following laws, where `n` ranges over naturals and `x`
over bitstrings.

    from (inc x) ≡ suc (from x)
    to (from n) ≡ n
    from (to x) ≡ x

For each law: if it holds, prove; if not, give a counterexample.


## Relations


#### Exercise `orderings` {#orderings}

Give an example of a preorder that is not a partial order.

Give an example of a partial order that is not a preorder.


#### Exercise `≤-antisym-cases` {#leq-antisym-cases} 

The above proof omits cases where one argument is `z≤n` and one
argument is `s≤s`.  Why is it ok to omit them?


#### Exercise `*-mono-≤` (stretch)

Show that multiplication is monotonic with regard to inequality.


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
[negation][plfa.Negation].)

#### Exercise `+-mono-<` {#plus-mono-less}

Show that addition is monotonic with respect to strict inequality.
As with inequality, some additional definitions may be required.

#### Exercise `≤-iff-<` (recommended) {#leq-iff-less}

Show that `suc m ≤ n` implies `m < n`, and conversely.

#### Exercise `<-trans-revisited` {#less-trans-revisited}

Give an alternative proof that strict inequality is transitive,
using the relating between strict inequality and inequality and
the fact that inequality is transitive.

#### Exercise `o+o≡e` (stretch) {#odd-plus-odd}

Show that the sum of two odd numbers is even.

#### Exercise `Bin-predicates` (stretch) {#Bin-predicates}

Recall that 
Exercise [Bin][plfa.Naturals#Bin]
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

\end{code}
(Hint: For each of these, you may first need to prove related
properties of `One`.)
