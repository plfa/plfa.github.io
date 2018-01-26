---
title     : "Properties: Proof by Induction"
layout    : page
permalink : /Properties
---

Now that we've defined the naturals and operations upon them, our next
step is to learn how to prove properties that they satisfy.  As hinted
by their name, properties of *inductive datatypes* are proved by
*induction*.


## Imports

Each chapter will begin with a list of the imports we require from the
Agda standard library.

<!-- We will, of course, require the naturals; everything in the
previous chapter is also found in the library module `Data.Nat`, so we
import the required definitions from there.  We also require
propositional equality. -->

<pre class="Agda">{% raw %}
<a name="664" class="Keyword"
      >open</a
      ><a name="668"
      > </a
      ><a name="669" class="Keyword"
      >import</a
      ><a name="675"
      > </a
      ><a name="676" class="Module"
      >Naturals</a
      ><a name="684"
      > </a
      ><a name="685" class="Keyword"
      >using</a
      ><a name="690"
      > </a
      ><a name="691" class="Symbol"
      >(</a
      ><a name="692" href="Naturals.html#1064" class="Datatype"
      >&#8469;</a
      ><a name="693" class="Symbol"
      >;</a
      ><a name="694"
      > </a
      ><a name="695" href="Naturals.html#1080" class="InductiveConstructor"
      >zero</a
      ><a name="699" class="Symbol"
      >;</a
      ><a name="700"
      > </a
      ><a name="701" href="Naturals.html#1091" class="InductiveConstructor"
      >suc</a
      ><a name="704" class="Symbol"
      >;</a
      ><a name="705"
      > </a
      ><a name="706" href="Naturals.html#9439" class="Primitive Operator"
      >_+_</a
      ><a name="709" class="Symbol"
      >;</a
      ><a name="710"
      > </a
      ><a name="711" href="Naturals.html#12016" class="Primitive Operator"
      >_*_</a
      ><a name="714" class="Symbol"
      >;</a
      ><a name="715"
      > </a
      ><a name="716" href="Naturals.html#13851" class="Primitive Operator"
      >_&#8760;_</a
      ><a name="719" class="Symbol"
      >)</a
      ><a name="720"
      >
</a
      ><a name="721" class="Keyword"
      >open</a
      ><a name="725"
      > </a
      ><a name="726" class="Keyword"
      >import</a
      ><a name="732"
      > </a
      ><a name="733" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#1" class="Module"
      >Relation.Binary.PropositionalEquality</a
      ><a name="770"
      > </a
      ><a name="771" class="Keyword"
      >using</a
      ><a name="776"
      > </a
      ><a name="777" class="Symbol"
      >(</a
      ><a name="778" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >_&#8801;_</a
      ><a name="781" class="Symbol"
      >;</a
      ><a name="782"
      > </a
      ><a name="783" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="787" class="Symbol"
      >;</a
      ><a name="788"
      > </a
      ><a name="789" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.Core.html#565" class="Function"
      >sym</a
      ><a name="792" class="Symbol"
      >;</a
      ><a name="793"
      > </a
      ><a name="794" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.Core.html#632" class="Function"
      >trans</a
      ><a name="799" class="Symbol"
      >)</a
      >
{% endraw %}</pre>

Each import consists of the keywords `open` and `import`, followed by
the module name, followed by the keyword `using`, followed by the
names of each identifier imported from the module, surrounded by
parentheses and separated by semicolons. Parentheses and semicolons
are among the few characters that cannot appear in names, so we do not
need extra spaces in the import list.


## Associativity

One property of addition is that it is *associative*, that is that the
order of the parentheses does not matter:

    (m + n) + p ≡ m + (n + p)

We write `=` in an Agda definition, whereas we write `≡` for an
equality we are trying to prove.  Here `m`, `n`, and `p` are variables
that range over all natural numbers.

We can test the proposition by choosing specific numbers for the three
variables.

       (3 + 4) + 5
    ≡
       7 + 5
    ≡
       12
    ≡
       3 + 9
    ≡
       3 + (4 + 5)

Here we have displayed the computation in tabular form, one term to a
line.  It is often easiest to read such computations from the top down
until one reaches the simplest term (in this case, `12`), and
then from the bottom up until one reaches the same term.

The test reveals that associativity is perhaps not as obvious as first
it appears.  Why should `7 + 5` be the same as `3 + 9`?  We might want
to gather more evidence, testing the proposition by choosing other
numbers.  But---since there are an infinite number of
naturals---testing can never be complete.  Is there any way we can be
sure that associativity holds for *all* the natural numbers?

The answer is yes! We can prove a property holds for all naturals using
*proof by induction*.


## Proof by induction

Recall the definition of natural numbers consists of a *base case*
which tells us that `zero` is a natural, and an *inductive case*
which tells us that if `m` is a natural then `suc m` is also a natural.

Proofs by induction follow the structure of this definition.  To prove
a property of natural numbers by induction, we need prove two cases.
First is the *base case*, where we show the property holds for `zero`.
Second is the *inductive case*, where we assume the the property holds for
an arbitary natural `m` (we call this the *inductive hypothesis*), and
then show that the property must also hold for `suc m`.

If we write `P m` for a property of `m`, then what we need to
demonstrate are the following two inference rules:

    ------
    P zero

    P m
    ---------
    P (suc m)

Let's unpack these rules.  The first rule is the base case, and
requires we show that property `P` holds for `zero`.  The second rule
is the inductive case, and requires we show that if we assume the
inductive hypothesis, that `P` holds for `m`, then it follows that
`P` also holds for `suc m`.

Why does this work?  Again, it can be explained by a creation story.
To start with, we know no properties.

    -- in the beginning, no properties are known

Now, we apply the two rules to all the properties we know about.  The
base case tells us that `P zero` holds, so we add it to the set of
known properties.  The inductive case tells us that if `P m` holds (on
the day before today) then `P (suc m)` also holds (today).  We didn't
know about any properties before today, so the inductive case doesn't
apply.

    -- on the first day, one property is known
    P zero

Then we repeat the process, so on the next day we know about all the
properties from the day before, plus any properties added by the rules.
The base case tells us that `P zero` holds, but we already
knew that. But now the inductive case tells us that since `P zero`
held yesterday, then `P (suc zero)` holds today.

    -- on the second day, two properties are known
    P zero
    P (suc zero)

And we repeat the process again. Now the inductive case
tells us that since `P zero` and `P (suc zero)` both hold, then
`P (suc zero)` and `P (suc (suc zero))` also hold. We already knew about
the first of these, but the second is new.

    -- on the third day, three properties are known
    P zero
    P (suc zero)
    P (suc (suc zero))

You've probably got the hang of it by now.

    -- on the fourth day, four properties are known
    P zero
    P (suc zero)
    P (suc (suc zero))
    P (suc (suc (suc zero)))

The process continues.  On the *n*th day there will be *n* distinct
properties that hold.  The property of every natural number will appear
on some given day.  In particular, the property `P n` first appears on
day *n+1*. 

## Our first proof: associativity

In order to prove associativity, we take `P m` to be the property

    (m + n) + p ≡ m + (n + p)

Then the appropriate instances of the inference rules, which
we must show to hold, become:

    -------------------------------
    (zero + n) + p ≡ zero + (n + p)

    (m + n) + p ≡ m + (n + p)
    ---------------------------------
    (suc m + n) + p ≡ (suc m + n) + p

In the inference rules, `n` and `p` are any arbitary natural numbers, so when we
are done with the proof we know it holds for any `n` and `p` as well as any `m`.

Recall the definition of addition has two clauses. 

    zero    + n  =  n                -- (i)
    (suc m) + n  =  suc (m + n)      -- (ii)

For the base case, we must show:

    (zero + n) + p ≡ zero + (n + p)

By (i), both sides of the equation simplify to `n + p`, so it holds.
In tabular form we have:

       (zero + n) + p
    ≡    (i)
       n + p
    ≡    (i)
       zero + (n + p)

Again, it is easiest to read from the top down until one reaches the
simplest term (`n + p`), and then from the bottom up
until one reaches the same term.

For the inductive case, we assume

    (m + n) + p ≡ m + (n + p)

and must show

    (suc m + n) + p ≡ (suc m + n) + p

By (ii), the left-hand side simplifies to `suc ((m + n) + p)` and the
right-hand side simplifies to `suc (m + (n + p))`, and the equality of
these follow from what we assumed.  In tabular form:

       (suc m + n) + p
    ≡    (ii)
       suc (m + n) + p
    ≡    (ii)
       suc ((m + n) + p)
    ≡    (induction hypothesis)
       suc (m + (n + p))
    ≡    (ii)
       suc m + (n + p)

Here it is easiest to read from the top down until one reaches the
simplest term (`suc ((m + n) + p)`), and then from the bottom up until
one reaches the simplest term (`suc (m + (n + p))`).  In this case,
the two simplest terms are not the same, but are equated by the
induction hypothesis.

## Encoding the proof in Agda

We encode this proof in Agda as follows.
<pre class="Agda">{% raw %}
<a name="7291" href="Properties.html#7291" class="Function"
      >+-assoc</a
      ><a name="7298"
      > </a
      ><a name="7299" class="Symbol"
      >:</a
      ><a name="7300"
      > </a
      ><a name="7301" class="Symbol"
      >&#8704;</a
      ><a name="7302"
      > </a
      ><a name="7303" class="Symbol"
      >(</a
      ><a name="7304" href="Properties.html#7304" class="Bound"
      >m</a
      ><a name="7305"
      > </a
      ><a name="7306" href="Properties.html#7306" class="Bound"
      >n</a
      ><a name="7307"
      > </a
      ><a name="7308" href="Properties.html#7308" class="Bound"
      >p</a
      ><a name="7309"
      > </a
      ><a name="7310" class="Symbol"
      >:</a
      ><a name="7311"
      > </a
      ><a name="7312" href="Naturals.html#1064" class="Datatype"
      >&#8469;</a
      ><a name="7313" class="Symbol"
      >)</a
      ><a name="7314"
      > </a
      ><a name="7315" class="Symbol"
      >&#8594;</a
      ><a name="7316"
      > </a
      ><a name="7317" class="Symbol"
      >(</a
      ><a name="7318" href="Properties.html#7304" class="Bound"
      >m</a
      ><a name="7319"
      > </a
      ><a name="7320" href="Naturals.html#9439" class="Primitive Operator"
      >+</a
      ><a name="7321"
      > </a
      ><a name="7322" href="Properties.html#7306" class="Bound"
      >n</a
      ><a name="7323" class="Symbol"
      >)</a
      ><a name="7324"
      > </a
      ><a name="7325" href="Naturals.html#9439" class="Primitive Operator"
      >+</a
      ><a name="7326"
      > </a
      ><a name="7327" href="Properties.html#7308" class="Bound"
      >p</a
      ><a name="7328"
      > </a
      ><a name="7329" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="7330"
      > </a
      ><a name="7331" href="Properties.html#7304" class="Bound"
      >m</a
      ><a name="7332"
      > </a
      ><a name="7333" href="Naturals.html#9439" class="Primitive Operator"
      >+</a
      ><a name="7334"
      > </a
      ><a name="7335" class="Symbol"
      >(</a
      ><a name="7336" href="Properties.html#7306" class="Bound"
      >n</a
      ><a name="7337"
      > </a
      ><a name="7338" href="Naturals.html#9439" class="Primitive Operator"
      >+</a
      ><a name="7339"
      > </a
      ><a name="7340" href="Properties.html#7308" class="Bound"
      >p</a
      ><a name="7341" class="Symbol"
      >)</a
      ><a name="7342"
      >
</a
      ><a name="7343" href="Properties.html#7291" class="Function"
      >+-assoc</a
      ><a name="7350"
      > </a
      ><a name="7351" href="Naturals.html#1080" class="InductiveConstructor"
      >zero</a
      ><a name="7355"
      > </a
      ><a name="7356" href="Properties.html#7356" class="Bound"
      >n</a
      ><a name="7357"
      > </a
      ><a name="7358" href="Properties.html#7358" class="Bound"
      >p</a
      ><a name="7359"
      > </a
      ><a name="7360" class="Symbol"
      >=</a
      ><a name="7361"
      > </a
      ><a name="7362" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="7366"
      >
</a
      ><a name="7367" href="Properties.html#7291" class="Function"
      >+-assoc</a
      ><a name="7374"
      > </a
      ><a name="7375" class="Symbol"
      >(</a
      ><a name="7376" href="Naturals.html#1091" class="InductiveConstructor"
      >suc</a
      ><a name="7379"
      > </a
      ><a name="7380" href="Properties.html#7380" class="Bound"
      >m</a
      ><a name="7381" class="Symbol"
      >)</a
      ><a name="7382"
      > </a
      ><a name="7383" href="Properties.html#7383" class="Bound"
      >n</a
      ><a name="7384"
      > </a
      ><a name="7385" href="Properties.html#7385" class="Bound"
      >p</a
      ><a name="7386"
      > </a
      ><a name="7387" class="Keyword"
      >rewrite</a
      ><a name="7394"
      > </a
      ><a name="7395" href="Properties.html#7291" class="Function"
      >+-assoc</a
      ><a name="7402"
      > </a
      ><a name="7403" href="Properties.html#7380" class="Bound"
      >m</a
      ><a name="7404"
      > </a
      ><a name="7405" href="Properties.html#7383" class="Bound"
      >n</a
      ><a name="7406"
      > </a
      ><a name="7407" href="Properties.html#7385" class="Bound"
      >p</a
      ><a name="7408"
      > </a
      ><a name="7409" class="Symbol"
      >=</a
      ><a name="7410"
      > </a
      ><a name="7411" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      >
{% endraw %}</pre>
Here we have named the proof `assoc+`.  In Agda, identifiers can consist of
any sequence of characters not including spaces or the characters `@.(){};_`.

Let's unpack this code.  The first line states that we are
defining the identifier `assoc+` which is a proof of the
proposition

    ∀ (m n p : ℕ) → (m + n) + p ≡ m + (n + p)

The upside down A is pronounced "for all", and the proposition
asserts that for all natural numbers `m`, `n`, and `p` that
the equations `(m + n) + p ≡ m + (n + p)` holds.  Such a proof
is a function that accepts three natural numbers---corresponding to
to `m`, `n`, and `p`---and returns a proof of the equation.

Proof by induction corresponds exactly to a recursive definition.
Here we are induct on the first argument `m`, and leave the other two
arguments `n` and `p` fixed.

The base case corresponds to instantiating `m` by
pattern matching on `zero`, so what we are required to
prove is:

    (zero + n) + p ≡ zero + (n + p)

After simplifying with the definition of addition, this equation
becomes:

    n + p ≡ n + p

The proof that a term is equal to itself is written `refl`.

The inductive case corresponds to instantiating `m` by `suc zero`,
so what we are required to prove is:

    (suc m + n) + p ≡ suc m + (n + p)

After simplifying with the definition of addition, this equation
becomes:

    suc ((m + n) + p) ≡ suc (m + (n + p))

After rewriting with the inductive hypothesis these two terms are
equal, and the proof is again given by `refl`.
Rewriting by a given equation is indicated by the keyword `rewrite`
followed by a proof of that equation.

Here the inductive hypothesis is not assumed, but instead proved by a
recursive invocation of the function we are definining, `assoc+ m n p`.
As with addition, this is well founded because associativity of
larger numbers is proved in terms of associativity of smaller numbers.
In this case, `assoc (suc m) n p` is proved using `assoc m n p`.

The correspondence between proof by induction and definition by
recursion is one of the most appealing aspects of Agda.


## Building proofs interactively

Agda is designed to be used with the Emacs text editor, and the two
in combination provide features that help to create proofs interactively.

Begin by typing

    +-assoc : ∀ (m n p : ℕ) → (m + n) + p ≡ m + (n + p)
    +-assoc m n p = ?

The question mark indicates that you would like Agda to help with
filling in that part of the code.  If you type `^C ^L` (control-C
followed by control-L), the question mark will be replaced.

    +-assoc : ∀ (m n p : ℕ) → (m + n) + p ≡ m + (n + p)
    +-assoc m n p = { }0

The empty braces are called a *hole*, and 0 is a number used for
referring to the hole.  The hole may display highlighted in green.
Emacs will also create a new window at the bottom of the screen
displaying the text

    ?0 : ((m + n) + p) ≡ (m + (n + p))

This indicates that hole 0 is to be filled in with a proof of
the stated judgement.

We wish to prove the proposition by induction on `m`.  More
the cursor into the hole and type `^C ^C`.  You will be given
the prompt:

    pattern variables to case:

Typing `m` will cause a split on that variable, resulting
in an update to the code.

    +-assoc : ∀ (m n p : ℕ) → (m + n) + p ≡ m + (n + p)
    +-assoc zero n p = { }0
    +-assoc (suc m) n p = { }1

There are now two holes, and the window at the bottom tells you what
each is required to prove:

    ?0 : ((zero + n) + p) ≡ (zero + (n + p))
    ?1 : ((suc m + n) + p) ≡ (suc m + (n + p))

Going into hole 0 and typing `^C ^,` will display the text:

    Goal: (n + p) ≡ (n + p)
    ————————————————————————————————————————————————————————————
    p : ℕ
    n : ℕ

This indicates that after simplification the goal for hole 0 is as
stated, and that variables `p` and `n` of the stated types are
available to use in the proof.  The proof of the given goal is
trivial, and going into the goal and typing `^C ^R` will fill it in,
renumbering the remaining hole to 0:

    +-assoc : ∀ (m n p : ℕ) → (m + n) + p ≡ m + (n + p)
    +-assoc zero n p = refl
    +-assoc (suc m) n p = { }0

Going into the new hold 0 and typing `^C ^,` will display the text:

    Goal: suc ((m + n) + p) ≡ suc (m + (n + p))
    ————————————————————————————————————————————————————————————
    p : ℕ
    n : ℕ
    m : ℕ

Again, this gives the simplified goal and the available variables.
In this case, we need to rewrite by the induction
hypothesis, so let's edit the text accordingly:

    +-assoc : ∀ (m n p : ℕ) → (m + n) + p ≡ m + (n + p)
    +-assoc zero n p = refl
    +-assoc (suc m) n p rewrite +-assoc m n p = { }0

Going into the remaining hole and typing `^C ^,` will show the
goal is now trivial:

    Goal: suc (m + (n + p)) ≡ suc (m + (n + p))
    ————————————————————————————————————————————————————————————
    p : ℕ
    n : ℕ
    m : ℕ

The proof of the given goal is trivial, and going into the goal and
typing `^C ^R` will fill it in, completing the proof:

    +-assoc : ∀ (m n p : ℕ) → (m + n) + p ≡ m + (n + p)
    +-assoc zero n p = refl
    +-assoc (suc m) n p rewrite +-assoc m n p = refl


## Creation, one last time

Again, it may be helpful to view the recursive definition as
a creation story.  This time we are concerned with judgements
asserting associativity.

     -- in the beginning, we know nothing about associativity

Now, we apply the rules to all the judgements we know about.  The base
case tells us that `(zero + n) + p ≡ zero + (n + p)` for every natural
`n` and `p`.  The inductive case tells us that if `(m + n) + p ≡ m +
(n + p)` (on the day before today) then `(suc m + n) + p ≡ suc m + (n
+ p)` (today).  We didn't know any judgments about associativity
before today, so that rule doesn't give us any new judgments.

    -- on the first day, we know about associativity of 0
    (0 + 0) + 0 ≡ 0 + (0 + 0)   ...   (0 + 4) + 5 ≡ 0 + (4 + 5)   ...
    
Then we repeat the process, so on the next day we know about all the
judgements from the day before, plus any judgements added by the rules.
The base case tells us nothing new, but now the inductive case adds
more judgements.

    -- on the second day, we know about associativity of 0 and 1
    (0 + 0) + 0 ≡ 0 + (0 + 0)   ...   (0 + 4) + 5 ≡ 0 + (4 + 5)   ...
    (1 + 0) + 0 ≡ 1 + (0 + 0)   ...   (1 + 4) + 5 ≡ 1 + (4 + 5)   ...

And we repeat the process again.

    -- on the third day, we know about associativity of 0, 1, and 2
    (0 + 0) + 0 ≡ 0 + (0 + 0)   ...   (0 + 4) + 5 ≡ 0 + (4 + 5)   ...
    (1 + 0) + 0 ≡ 1 + (0 + 0)   ...   (1 + 4) + 5 ≡ 1 + (4 + 5)   ...
    (2 + 0) + 0 ≡ 2 + (0 + 0)   ...   (2 + 4) + 5 ≡ 2 + (4 + 5)   ...

You've probably got the hang of it by now.

    -- on the fourth day, we know about associativity of 0, 1, 2, and 3
    (0 + 0) + 0 ≡ 0 + (0 + 0)   ...   (0 + 4) + 5 ≡ 0 + (4 + 5)   ...
    (1 + 0) + 0 ≡ 1 + (0 + 0)   ...   (1 + 4) + 5 ≡ 1 + (4 + 5)   ...
    (2 + 0) + 0 ≡ 2 + (0 + 0)   ...   (2 + 4) + 5 ≡ 2 + (4 + 5)   ...

The process continues.  On the *m*th day we will know all the
judgements where the first number is less than *m*.


## Our second proof: commutativity

Another important property of addition is that it is commutative.  To show
this by induction, we take `P m` to be the property

    m + n ≡ n + m

Then the appropriate instances of the inference rules, which
we must show to hold, become:

    -------------------
    zero + n ≡ n + zero

    m + n ≡ n + m
    ---------------------
    suc m + n ≡ n + suc m

In the inference rules, `n` is any arbitary natural number, so when we
are done with the proof we know it holds for any `n` as well as any `m`.

By equation (i) of the definition of addition, the left-hand side of
the conclusion of the base case simplifies to `n`, so the base case
will hold if we can show

    n + zero ≡ n    -- (x)

By equation (ii) of the definition of addition, the left-hand side of
the conclusion of the inductive case simplifies to `suc (m + n)`, so
the inductive case will hold if we can show

    n + suc m ≡ suc (n + m)    -- (xi)

and then apply the inductive hypothesis to rewrite `m + n` to `n + m`.
We use induction two more times, on `n` this time rather than `m`, to
show both (x) and (xi).

Here is the proof written out in full, using tabular form.

Proposition.

    m + n ≡ n + m

Proof. By induction on `m`.

Base case.

       zero + n
    ≡    (i)
       n
    ≡    (x)
       n + zero

Inductive case.

       suc m + n
    ≡    (ii)
       suc (m + n)
    ≡    (inductive hypothesis)
       suc (n + m)
    ≡    (xi)
       n + suc m
       
QED.

As with other tabular prooofs, it is best understood by reading from top
down and bottom up and meeting in the middle.

We now prove each of the two required lemmas, (x) and (xi).

Lemma (x).

    n + zero ≡ n

Proof. By induction on `n`.

Base case.

       zero + zero
    ≡    (i)
       zero

Inductive case.

       suc n + zero
    ≡    (ii)
       suc (n + zero)
    ≡    (inductive hypothesis)
       suc n

QED.

Lemma (xi).

    m + suc n ≡ suc (m + n)

Proof. By induction on `m`.

Base case.

       zero + suc n
    ≡    (i)
       suc n
    ≡    (i)
       suc (zero + n)

Inductive case.

       suc m + suc n
    ≡    (ii)
       suc (m + suc n)
    ≡    (inductive hypothesis)
       suc (suc (m + n))
    ≡    (ii)
       suc (suc m + n)

QED.

## Encoding the proofs in Agda

These proofs can be encoded concisely in Agda.
<pre class="Agda">{% raw %}
<a name="16853" href="Properties.html#16853" class="Function"
      >+-identity</a
      ><a name="16863"
      > </a
      ><a name="16864" class="Symbol"
      >:</a
      ><a name="16865"
      > </a
      ><a name="16866" class="Symbol"
      >&#8704;</a
      ><a name="16867"
      > </a
      ><a name="16868" class="Symbol"
      >(</a
      ><a name="16869" href="Properties.html#16869" class="Bound"
      >n</a
      ><a name="16870"
      > </a
      ><a name="16871" class="Symbol"
      >:</a
      ><a name="16872"
      > </a
      ><a name="16873" href="Naturals.html#1064" class="Datatype"
      >&#8469;</a
      ><a name="16874" class="Symbol"
      >)</a
      ><a name="16875"
      > </a
      ><a name="16876" class="Symbol"
      >&#8594;</a
      ><a name="16877"
      > </a
      ><a name="16878" href="Properties.html#16869" class="Bound"
      >n</a
      ><a name="16879"
      > </a
      ><a name="16880" href="Naturals.html#9439" class="Primitive Operator"
      >+</a
      ><a name="16881"
      > </a
      ><a name="16882" href="Naturals.html#1080" class="InductiveConstructor"
      >zero</a
      ><a name="16886"
      > </a
      ><a name="16887" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="16888"
      > </a
      ><a name="16889" href="Properties.html#16869" class="Bound"
      >n</a
      ><a name="16890"
      >
</a
      ><a name="16891" href="Properties.html#16853" class="Function"
      >+-identity</a
      ><a name="16901"
      > </a
      ><a name="16902" href="Naturals.html#1080" class="InductiveConstructor"
      >zero</a
      ><a name="16906"
      > </a
      ><a name="16907" class="Symbol"
      >=</a
      ><a name="16908"
      > </a
      ><a name="16909" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="16913"
      >
</a
      ><a name="16914" href="Properties.html#16853" class="Function"
      >+-identity</a
      ><a name="16924"
      > </a
      ><a name="16925" class="Symbol"
      >(</a
      ><a name="16926" href="Naturals.html#1091" class="InductiveConstructor"
      >suc</a
      ><a name="16929"
      > </a
      ><a name="16930" href="Properties.html#16930" class="Bound"
      >n</a
      ><a name="16931" class="Symbol"
      >)</a
      ><a name="16932"
      > </a
      ><a name="16933" class="Keyword"
      >rewrite</a
      ><a name="16940"
      > </a
      ><a name="16941" href="Properties.html#16853" class="Function"
      >+-identity</a
      ><a name="16951"
      > </a
      ><a name="16952" href="Properties.html#16930" class="Bound"
      >n</a
      ><a name="16953"
      > </a
      ><a name="16954" class="Symbol"
      >=</a
      ><a name="16955"
      > </a
      ><a name="16956" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="16960"
      >

</a
      ><a name="16962" href="Properties.html#16962" class="Function"
      >+-suc</a
      ><a name="16967"
      > </a
      ><a name="16968" class="Symbol"
      >:</a
      ><a name="16969"
      > </a
      ><a name="16970" class="Symbol"
      >&#8704;</a
      ><a name="16971"
      > </a
      ><a name="16972" class="Symbol"
      >(</a
      ><a name="16973" href="Properties.html#16973" class="Bound"
      >m</a
      ><a name="16974"
      > </a
      ><a name="16975" href="Properties.html#16975" class="Bound"
      >n</a
      ><a name="16976"
      > </a
      ><a name="16977" class="Symbol"
      >:</a
      ><a name="16978"
      > </a
      ><a name="16979" href="Naturals.html#1064" class="Datatype"
      >&#8469;</a
      ><a name="16980" class="Symbol"
      >)</a
      ><a name="16981"
      > </a
      ><a name="16982" class="Symbol"
      >&#8594;</a
      ><a name="16983"
      > </a
      ><a name="16984" href="Properties.html#16973" class="Bound"
      >m</a
      ><a name="16985"
      > </a
      ><a name="16986" href="Naturals.html#9439" class="Primitive Operator"
      >+</a
      ><a name="16987"
      > </a
      ><a name="16988" href="Naturals.html#1091" class="InductiveConstructor"
      >suc</a
      ><a name="16991"
      > </a
      ><a name="16992" href="Properties.html#16975" class="Bound"
      >n</a
      ><a name="16993"
      > </a
      ><a name="16994" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="16995"
      > </a
      ><a name="16996" href="Naturals.html#1091" class="InductiveConstructor"
      >suc</a
      ><a name="16999"
      > </a
      ><a name="17000" class="Symbol"
      >(</a
      ><a name="17001" href="Properties.html#16973" class="Bound"
      >m</a
      ><a name="17002"
      > </a
      ><a name="17003" href="Naturals.html#9439" class="Primitive Operator"
      >+</a
      ><a name="17004"
      > </a
      ><a name="17005" href="Properties.html#16975" class="Bound"
      >n</a
      ><a name="17006" class="Symbol"
      >)</a
      ><a name="17007"
      >
</a
      ><a name="17008" href="Properties.html#16962" class="Function"
      >+-suc</a
      ><a name="17013"
      > </a
      ><a name="17014" href="Naturals.html#1080" class="InductiveConstructor"
      >zero</a
      ><a name="17018"
      > </a
      ><a name="17019" href="Properties.html#17019" class="Bound"
      >n</a
      ><a name="17020"
      > </a
      ><a name="17021" class="Symbol"
      >=</a
      ><a name="17022"
      > </a
      ><a name="17023" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="17027"
      >
</a
      ><a name="17028" href="Properties.html#16962" class="Function"
      >+-suc</a
      ><a name="17033"
      > </a
      ><a name="17034" class="Symbol"
      >(</a
      ><a name="17035" href="Naturals.html#1091" class="InductiveConstructor"
      >suc</a
      ><a name="17038"
      > </a
      ><a name="17039" href="Properties.html#17039" class="Bound"
      >m</a
      ><a name="17040" class="Symbol"
      >)</a
      ><a name="17041"
      > </a
      ><a name="17042" href="Properties.html#17042" class="Bound"
      >n</a
      ><a name="17043"
      > </a
      ><a name="17044" class="Keyword"
      >rewrite</a
      ><a name="17051"
      > </a
      ><a name="17052" href="Properties.html#16962" class="Function"
      >+-suc</a
      ><a name="17057"
      > </a
      ><a name="17058" href="Properties.html#17039" class="Bound"
      >m</a
      ><a name="17059"
      > </a
      ><a name="17060" href="Properties.html#17042" class="Bound"
      >n</a
      ><a name="17061"
      > </a
      ><a name="17062" class="Symbol"
      >=</a
      ><a name="17063"
      > </a
      ><a name="17064" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="17068"
      >

</a
      ><a name="17070" href="Properties.html#17070" class="Function"
      >+-comm</a
      ><a name="17076"
      > </a
      ><a name="17077" class="Symbol"
      >:</a
      ><a name="17078"
      > </a
      ><a name="17079" class="Symbol"
      >&#8704;</a
      ><a name="17080"
      > </a
      ><a name="17081" class="Symbol"
      >(</a
      ><a name="17082" href="Properties.html#17082" class="Bound"
      >m</a
      ><a name="17083"
      > </a
      ><a name="17084" href="Properties.html#17084" class="Bound"
      >n</a
      ><a name="17085"
      > </a
      ><a name="17086" class="Symbol"
      >:</a
      ><a name="17087"
      > </a
      ><a name="17088" href="Naturals.html#1064" class="Datatype"
      >&#8469;</a
      ><a name="17089" class="Symbol"
      >)</a
      ><a name="17090"
      > </a
      ><a name="17091" class="Symbol"
      >&#8594;</a
      ><a name="17092"
      > </a
      ><a name="17093" href="Properties.html#17082" class="Bound"
      >m</a
      ><a name="17094"
      > </a
      ><a name="17095" href="Naturals.html#9439" class="Primitive Operator"
      >+</a
      ><a name="17096"
      > </a
      ><a name="17097" href="Properties.html#17084" class="Bound"
      >n</a
      ><a name="17098"
      > </a
      ><a name="17099" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="17100"
      > </a
      ><a name="17101" href="Properties.html#17084" class="Bound"
      >n</a
      ><a name="17102"
      > </a
      ><a name="17103" href="Naturals.html#9439" class="Primitive Operator"
      >+</a
      ><a name="17104"
      > </a
      ><a name="17105" href="Properties.html#17082" class="Bound"
      >m</a
      ><a name="17106"
      >
</a
      ><a name="17107" href="Properties.html#17070" class="Function"
      >+-comm</a
      ><a name="17113"
      > </a
      ><a name="17114" href="Naturals.html#1080" class="InductiveConstructor"
      >zero</a
      ><a name="17118"
      > </a
      ><a name="17119" href="Properties.html#17119" class="Bound"
      >n</a
      ><a name="17120"
      > </a
      ><a name="17121" class="Keyword"
      >rewrite</a
      ><a name="17128"
      > </a
      ><a name="17129" href="Properties.html#16853" class="Function"
      >+-identity</a
      ><a name="17139"
      > </a
      ><a name="17140" href="Properties.html#17119" class="Bound"
      >n</a
      ><a name="17141"
      > </a
      ><a name="17142" class="Symbol"
      >=</a
      ><a name="17143"
      > </a
      ><a name="17144" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="17148"
      >
</a
      ><a name="17149" href="Properties.html#17070" class="Function"
      >+-comm</a
      ><a name="17155"
      > </a
      ><a name="17156" class="Symbol"
      >(</a
      ><a name="17157" href="Naturals.html#1091" class="InductiveConstructor"
      >suc</a
      ><a name="17160"
      > </a
      ><a name="17161" href="Properties.html#17161" class="Bound"
      >m</a
      ><a name="17162" class="Symbol"
      >)</a
      ><a name="17163"
      > </a
      ><a name="17164" href="Properties.html#17164" class="Bound"
      >n</a
      ><a name="17165"
      > </a
      ><a name="17166" class="Keyword"
      >rewrite</a
      ><a name="17173"
      > </a
      ><a name="17174" href="Properties.html#16962" class="Function"
      >+-suc</a
      ><a name="17179"
      > </a
      ><a name="17180" href="Properties.html#17164" class="Bound"
      >n</a
      ><a name="17181"
      > </a
      ><a name="17182" href="Properties.html#17161" class="Bound"
      >m</a
      ><a name="17183"
      > </a
      ><a name="17184" class="Symbol"
      >|</a
      ><a name="17185"
      > </a
      ><a name="17186" href="Properties.html#17070" class="Function"
      >+-comm</a
      ><a name="17192"
      > </a
      ><a name="17193" href="Properties.html#17161" class="Bound"
      >m</a
      ><a name="17194"
      > </a
      ><a name="17195" href="Properties.html#17164" class="Bound"
      >n</a
      ><a name="17196"
      > </a
      ><a name="17197" class="Symbol"
      >=</a
      ><a name="17198"
      > </a
      ><a name="17199" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      >
{% endraw %}</pre>
Here we have renamed Lemma (x) and (xi) to `+-identity` and `+-suc`,
respectively.  In the final line, rewriting with two equations is
indicated by separating the two proofs of the relevant equations by a
vertical bar; the rewrite on the left is performed before that on the
right.

## Exercises

+ *Swapping terms*. Show

    m + (n + p) ≡ n + (m + p)

  for all naturals `m`, `n`, and `p`. No induction is needed,
  just apply the previous results which show addition
  is associative and commutative.  You may need to use
  one or more of the following functions from the standard library:

     sym : ∀ {m n : ℕ} → m ≡ n → n ≡ m
     trans : ∀ {m n p : ℕ} → m ≡ n → n ≡ p → m ≡ p

  Name your proof `+-swap`.  

+ *Multiplication distributes over addition*. Show

    (m + n) * p ≡ m * p + n * p

  for all naturals `m`, `n`, and `p`. Name your proof `*-distrib-+`.

+ *Multiplication is associative*. Show

    (m * n) * p ≡ m * (n * p)

  for all naturals `m`, `n`, and `p`. Name your proof `*-assoc`.

+ *Multiplication is commutative*. Show

    m * n ≡ n * m

  for all naturals `m` and `n`.  As with commutativity of addition,
  you will need to formulate and prove suitable lemmas.
  Name your proof `*-comm`.

+ *Monus from zero* Show

    zero ∸ n ≡ zero

  for all naturals `n`. Did your proof require induction?
  Name your proof `0∸n≡0`.

+ *Associativity of monus with addition* Show

    m ∸ n ∸ p ≡ m ∸ (n + p)

  for all naturals `m`, `n`, and `p`.
  Name your proof `∸-+-assoc`.

## Unicode

This chapter introduces the following unicode.

    ≡  U+2261  IDENTICAL TO (\==)
    ∀  U+2200  FOR ALL (\forall)
