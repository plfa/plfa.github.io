---
title     : "Naturals: Natural numbers"
layout    : page
permalink : /Naturals
---

The night sky holds more stars than I can count, though less than five
thousand are visible to the naked sky.  The observable universe
contains about seventy sextillion stars.

But the number of stars is finite, while natural numbers are infinite.
Count all the stars, and you will still have as many natural numbers
left over as you started with.


## The naturals are an inductive datatype

Everyone is familiar with the natural numbers:

    0
    1
    2
    3
    ...

and so on. We write `ℕ` for the *type* of natural numbers, and say that
`0`, `1`, `2`, `3`, and so on are *values* of type `ℕ`.  In Agda,
we indicate this by writing

    0 : ℕ
    1 : ℕ
    2 : ℕ
    3 : ℕ
    ...

and so on.

The set of natural numbers is infinite, yet we can write down
its definition in just a few lines.  Here is the definition
as a pair of inference rules:

    --------
    zero : ℕ

    m : ℕ
    ---------
    suc m : ℕ

And here is the definition in Agda:
<pre class="Agda">{% raw %}
<a name="1059" class="Keyword"
      >data</a
      ><a name="1063"
      > </a
      ><a name="1064" href="Naturals.html#1064" class="Datatype"
      >&#8469;</a
      ><a name="1065"
      > </a
      ><a name="1066" class="Symbol"
      >:</a
      ><a name="1067"
      > </a
      ><a name="1068" class="PrimitiveType"
      >Set</a
      ><a name="1071"
      > </a
      ><a name="1072" class="Keyword"
      >where</a
      ><a name="1077"
      >
  </a
      ><a name="1080" href="Naturals.html#1080" class="InductiveConstructor"
      >zero</a
      ><a name="1084"
      > </a
      ><a name="1085" class="Symbol"
      >:</a
      ><a name="1086"
      > </a
      ><a name="1087" href="Naturals.html#1064" class="Datatype"
      >&#8469;</a
      ><a name="1088"
      >
  </a
      ><a name="1091" href="Naturals.html#1091" class="InductiveConstructor"
      >suc</a
      ><a name="1094"
      >  </a
      ><a name="1096" class="Symbol"
      >:</a
      ><a name="1097"
      > </a
      ><a name="1098" href="Naturals.html#1064" class="Datatype"
      >&#8469;</a
      ><a name="1099"
      > </a
      ><a name="1100" class="Symbol"
      >&#8594;</a
      ><a name="1101"
      > </a
      ><a name="1102" href="Naturals.html#1064" class="Datatype"
      >&#8469;</a
      >
{% endraw %}</pre>
Here `ℕ` is the name of the *datatype* we are defining,
and `zero` and `suc` (short for *successor*) are the
*constructors* of the datatype.

Both definitions above tell us the same two things:

+ *Base case*: `zero` is a natural number.
+ *Inductive case*: if `m` is a natural number, then `suc m` is also a
  natural number.

Further, these two rules give the *only* ways of creating natural numbers.
Hence, the possible natural numbers are

    zero
    suc zero
    suc (suc zero)
    suc (suc (suc zero))
    ...

We write `0` as shorthand for `zero`; and `1` is shorthand
for `suc zero`, the successor of zero, that is, the natural that comes
after zero; and `2` is shorthand for `suc (suc zero)`, which is the
same as `suc 1`, the successor of one; and `3` is shorthand for the
successor of two; and so on.

**Exercise 1** Write out `7` in longhand.


## Unpacking the inference rules

Let's unpack the inference rules.  Each inference rule consists of
zero or more *judgments* written above a horizontal line, called the
*hypotheses*, and a single judgment written below, called the
*conclusion*.  The first rule is the base case. It has no hypotheses,
and the conclusion asserts that `zero` is a natural.  The second rule
is the inductive case. It has one hypothesis, which assumes that `m`
is a natural, and the conclusion asserts that `suc n` is a also a
natural.


## Unpacking the Agda definition

Let's unpack the Agda definition. The keyword `data` tells us this is an
inductive definition, that is, that we are defining a new datatype
with constructors.  The phrase

    ℕ : Set

tells us that `ℕ` is the name of the new datatype, and that it is a
`Set`, which is the way in Agda of saying that it is a type.  The
keyword `where` separates the declaration of the datatype from the
declaration of its constructors. Each constructor is declared on a
separate line, which is indented to indicate that it belongs to the
corresponding `data` declaration.  The lines

    zero : ℕ
    suc : ℕ → ℕ

tell us that `zero` is a natural number and that `suc` takes a natural
number as argument and returns a natural number.

You may have notices that `ℕ` and `→` are don't appear on your
keyboard.  They are symbols in *unicode*.  At the end of each chapter
is a list of all the unicode used in the chapter, including
instructions on how to type them in the Emacs text editor using keys
that are on your keyboard.


## The story of creation

Let's look again at the rules that define the natural numbers:

+ *Base case*: `zero` is a natural number.
+ *Inductive case*: if `m` is a natural number, then `suc m` is also a
  natural number.

Wait a minute! The second line defines natural numbers
in terms of natural numbers. How can that posssibly be allowed?
Isn't this as meaningless as claiming "Brexit means Brexit"?

In fact, it is possible to assign our definition a meaning without
resorting to any unpermitted circularities.  Furthermore, we can do so
while only working with *finite* sets and never referring to the
entire *infinite* set of natural numbers.

We will think of it as a creation story.  To start with, we know about
no natural numbers at all.

    -- in the beginning, there are no natural numbers

Now, we apply the rules to all the natural numbers we know about.  The
base case tells us that `zero` is a natural number, so we add it to the set
of known natural numbers.  The inductive case tells us that if `m` is a
natural number (on the day before today) then `suc m` is also a
natural number (today).  We didn't know about any natural numbers
before today, so the inductive case doesn't apply.

    -- on the first day, there is one natural number   
    zero : ℕ

Then we repeat the process, so on the next day we know about all the
numbers from the day before, plus any numbers added by the rules.  The
base case tells us that `zero` is a natural number, but we already knew
that. But now the inductive case tells us that since `zero` was a natural
number yesterday, then `suc zero` is a natural number today.

    -- on the second day, there are two natural numbers
    zero : ℕ
    suc zero : ℕ

And we repeat the process again. Now the inductive case
tells us that since `zero` and `suc zero` are both natural numbers, then
`suc zero` and `suc (suc zero)` are natural numbers. We already knew about
the first of these, but the second is new.

    -- on the third day, there are three natural numbers
    zero : ℕ
    suc zero : ℕ
    suc (suc zero) : ℕ

You've probably got the hang of it by now.

    -- on the fourth day, there are four natural numbers
    zero : ℕ
    suc zero : ℕ
    suc (suc zero) : ℕ
    suc (suc (suc zero)) : ℕ

The process continues.  On the *n*th day there will be *n* distinct
natural numbers. Every natural number will appear on some given day.
In particular, the number *n* first appears on day *n+1*. And we
never actually define the set of numbers in terms of itself. Instead,
we define the set of numbers on day *n+1* in terms of the set of
numbers on day *n*.

A process like this one is called *inductive*. We start with nothing, and
build up a potentially infinite set by applying rules that convert one
finite set into another finite set.

The rule defining zero is called a *base case*, because it introduces
a natural number even when we know no other natural numbers.  The rule
defining successor is called an *inductive case*, because it
introduces more natural numbers once we already know some.  Note the
crucial role of the base case.  If we only had inductive rules, then
we would have no numbers in the beginning, and still no numbers on the
second day, and on the third, and so on.  An inductive definition lacking
a base case is useless, as in the phrase "Brexit means Brexit".


## Philosophy and history

A philosopher might observe that our reference to the first day,
second day, and so on, implicitly involves an understanding of natural
numbers.  In this sense, our definition might indeed be regarded as in
some sense circular.  We need not let this circularity disturb us.
Everyone possesses a good informal understanding of the natural
numbers, which we may take as a foundation for their formal
description.

While the natural numbers have been understood for as long as people
can count, the inductive definition of the natural numbers is relatively
recent.  It can be traced back to Richard Dedekind's paper "*Was sind
und was sollen die Zahlen?*" (What are and what should be the
numbers?), published in 1888, and Giuseppe Peano's book "*Arithmetices
principia, nova methodo exposita*" (The principles of arithmetic
presented by a new method), published the following year.


## A useful pragma

In Agda, any text following `--` or enclosed between `{-`
and `-}` is considered a *comment*.  Comments have no effect on the
code, with the exception of one special kind of comment, called a
*pragma*, which is enclosed between `{-#` and `#-}`.

Including the line
<pre class="Agda">{% raw %}
<a name="8086" class="Symbol"
      >{-#</a
      ><a name="8089"
      > </a
      ><a name="8090" class="Keyword"
      >BUILTIN</a
      ><a name="8097"
      > NATURAL </a
      ><a name="8106" href="Naturals.html#1064" class="Datatype"
      >&#8469;</a
      ><a name="8107"
      > </a
      ><a name="8108" class="Symbol"
      >#-}</a
      >
{% endraw %}</pre>
tells Agda that `ℕ` corresponds to the natural numbers, and hence one
is permitted to type `0` as shorthand for `zero`, `1` as shorthand for
`suc zero`, `2` as shorthand for `suc (suc zero)`, and so on.  The
declaration is not permitted unless the type given has two constructors,
one corresponding to zero and one to successor.

As well as enabling the above shorthand, the pragma also enables a
more efficient internal representation of naturals as the Haskell type
integer.  Representing the natural *n* with `zero` and `suc`
requires space proportional to *n*, whereas representing it as an integer in
Haskell only requires space proportional to the logarithm of *n*.  In
particular, if *n* is less than 2⁶⁴, it will require just one word on
a machine with 64-bit words.


## Operations on naturals are recursive functions

Now that we have the natural numbers, what can we do with them?
For instance, can we define arithmetic operations such as
addition and multiplication?

As a child I spent much time memorising tables of addition and
multiplication.  At first the rules seemed tricky and I would often
make mistakes.  So it came as a shock to me to realise that all of addition
and multiplication can be precisely defined in just a couple of lines.

Here is the definition of addition in Agda:
<pre class="Agda">{% raw %}
<a name="9439" href="Naturals.html#9439" class="Function Operator"
      >_+_</a
      ><a name="9442"
      > </a
      ><a name="9443" class="Symbol"
      >:</a
      ><a name="9444"
      > </a
      ><a name="9445" href="Naturals.html#1064" class="Datatype"
      >&#8469;</a
      ><a name="9446"
      > </a
      ><a name="9447" class="Symbol"
      >&#8594;</a
      ><a name="9448"
      > </a
      ><a name="9449" href="Naturals.html#1064" class="Datatype"
      >&#8469;</a
      ><a name="9450"
      > </a
      ><a name="9451" class="Symbol"
      >&#8594;</a
      ><a name="9452"
      > </a
      ><a name="9453" href="Naturals.html#1064" class="Datatype"
      >&#8469;</a
      ><a name="9454"
      >
</a
      ><a name="9455" href="Naturals.html#1080" class="InductiveConstructor"
      >zero</a
      ><a name="9459"
      >    </a
      ><a name="9463" href="Naturals.html#9439" class="Function Operator"
      >+</a
      ><a name="9464"
      > </a
      ><a name="9465" href="Naturals.html#9465" class="Bound"
      >n</a
      ><a name="9466"
      >  </a
      ><a name="9468" class="Symbol"
      >=</a
      ><a name="9469"
      >  </a
      ><a name="9471" href="Naturals.html#9465" class="Bound"
      >n</a
      ><a name="9472"
      >                </a
      ><a name="9488" class="Comment"
      >-- (i)</a
      ><a name="9494"
      >
</a
      ><a name="9495" class="Symbol"
      >(</a
      ><a name="9496" href="Naturals.html#1091" class="InductiveConstructor"
      >suc</a
      ><a name="9499"
      > </a
      ><a name="9500" href="Naturals.html#9500" class="Bound"
      >m</a
      ><a name="9501" class="Symbol"
      >)</a
      ><a name="9502"
      > </a
      ><a name="9503" href="Naturals.html#9439" class="Function Operator"
      >+</a
      ><a name="9504"
      > </a
      ><a name="9505" href="Naturals.html#9505" class="Bound"
      >n</a
      ><a name="9506"
      >  </a
      ><a name="9508" class="Symbol"
      >=</a
      ><a name="9509"
      >  </a
      ><a name="9511" href="Naturals.html#1091" class="InductiveConstructor"
      >suc</a
      ><a name="9514"
      > </a
      ><a name="9515" class="Symbol"
      >(</a
      ><a name="9516" href="Naturals.html#9500" class="Bound"
      >m</a
      ><a name="9517"
      > </a
      ><a name="9518" href="Naturals.html#9439" class="Function Operator"
      >+</a
      ><a name="9519"
      > </a
      ><a name="9520" href="Naturals.html#9505" class="Bound"
      >n</a
      ><a name="9521" class="Symbol"
      >)</a
      ><a name="9522"
      >      </a
      ><a name="9528" class="Comment"
      >-- (ii)</a
      >
{% endraw %}</pre>

Let's unpack this definition.  Addition is an infix operator.  It is
written with underbars where the arguement go, hence its name is
`_+_`.  It's type, `ℕ → ℕ → ℕ`, indicates that it accepts two naturals
and returns a natural.  There are two ways to construct a natural,
with `zero` or with `suc`, so there are two lines defining addition,
labeled with comments as (i) and (ii).  Line (i) says that
adding zero to a number (`zero + n`) returns that number (`n`). Line
(ii) says that adding the successor of a number to another number
(`(suc m) + n`) returns the successor of adding the two numbers (`suc
(m+n)`).  We say we are using *pattern matching* when we use a
constructor applied to a term as an argument, such as `zero` in (i)
or `(suc m)` in (ii).

If we write `zero` as `0` and `suc m` as `1 + m`, we get two familiar equations.

   0       + n  =  n
   (1 + m) + n  =  1 + (m + n)

The first follows because zero is a left identity for addition,
and the second because addition is associative.  In its most general
form, associativity is written

   (m + n) + p  =  m + (n + p)

meaning that the order of parentheses is irrelevant.  We get the
second equation from this one by taking `m` to be `1`, `n` to be `m`,
and `p` to be `n`.

The definition is *recursive*, in that the last line defines addition
in terms of addition.  As with the inductive definition of the
naturals, the apparent circularity is not a problem.  It works because
addition of larger numbers is defined in terms of addition of smaller
numbers.  Such a definition is called *well founded*.

For example, let's add two and three.

       2 + 3
    =    (is shorthand for)
       (suc (suc zero)) + (suc (suc (suc zero)))
    =    (ii)
       suc ((suc zero) + (suc (suc (suc zero))))
    =    (ii)
       suc (suc (zero + (suc (suc (suc zero)))))
    =    (i)
       suc (suc (suc (suc (suc zero))))
    =    (is longhand for)
       5

We can write this more compactly by only expanding shorthand as needed.

       2 + 3
    =    (ii)
       suc (1 + 3)
    =    (ii)
       suc (suc (0 + 3))
    =    (i)
       suc (suc 3)
    =    
       5

The first use of (ii) matches by taking `m = 1` and `n = 3`,
The second use of (ii) matches by taking `m = 0` and `n = 3`,
and the use of (i) matches by taking `n = 3`.

**Exercise** Compute `3 + 4` by the same technique.


## Multiplication

Once we have defined addition, we can define multiplication
as repeated addition.
<pre class="Agda">{% raw %}
<a name="12016" href="Naturals.html#12016" class="Function Operator"
      >_*_</a
      ><a name="12019"
      > </a
      ><a name="12020" class="Symbol"
      >:</a
      ><a name="12021"
      > </a
      ><a name="12022" href="Naturals.html#1064" class="Datatype"
      >&#8469;</a
      ><a name="12023"
      > </a
      ><a name="12024" class="Symbol"
      >&#8594;</a
      ><a name="12025"
      > </a
      ><a name="12026" href="Naturals.html#1064" class="Datatype"
      >&#8469;</a
      ><a name="12027"
      > </a
      ><a name="12028" class="Symbol"
      >&#8594;</a
      ><a name="12029"
      > </a
      ><a name="12030" href="Naturals.html#1064" class="Datatype"
      >&#8469;</a
      ><a name="12031"
      >
</a
      ><a name="12032" href="Naturals.html#1080" class="InductiveConstructor"
      >zero</a
      ><a name="12036"
      > </a
      ><a name="12037" href="Naturals.html#12016" class="Function Operator"
      >*</a
      ><a name="12038"
      > </a
      ><a name="12039" href="Naturals.html#12039" class="Bound"
      >n</a
      ><a name="12040"
      >     </a
      ><a name="12045" class="Symbol"
      >=</a
      ><a name="12046"
      >  </a
      ><a name="12048" href="Naturals.html#1080" class="InductiveConstructor"
      >zero</a
      ><a name="12052"
      >           </a
      ><a name="12063" class="Comment"
      >-- (iii)</a
      ><a name="12071"
      >
</a
      ><a name="12072" class="Symbol"
      >(</a
      ><a name="12073" href="Naturals.html#1091" class="InductiveConstructor"
      >suc</a
      ><a name="12076"
      > </a
      ><a name="12077" href="Naturals.html#12077" class="Bound"
      >m</a
      ><a name="12078" class="Symbol"
      >)</a
      ><a name="12079"
      > </a
      ><a name="12080" href="Naturals.html#12016" class="Function Operator"
      >*</a
      ><a name="12081"
      > </a
      ><a name="12082" href="Naturals.html#12082" class="Bound"
      >n</a
      ><a name="12083"
      >  </a
      ><a name="12085" class="Symbol"
      >=</a
      ><a name="12086"
      >  </a
      ><a name="12088" href="Naturals.html#12082" class="Bound"
      >n</a
      ><a name="12089"
      > </a
      ><a name="12090" href="Naturals.html#9439" class="Function Operator"
      >+</a
      ><a name="12091"
      > </a
      ><a name="12092" class="Symbol"
      >(</a
      ><a name="12093" href="Naturals.html#12077" class="Bound"
      >m</a
      ><a name="12094"
      > </a
      ><a name="12095" href="Naturals.html#12016" class="Function Operator"
      >*</a
      ><a name="12096"
      > </a
      ><a name="12097" href="Naturals.html#12082" class="Bound"
      >n</a
      ><a name="12098" class="Symbol"
      >)</a
      ><a name="12099"
      >    </a
      ><a name="12103" class="Comment"
      >-- (iv)</a
      >
{% endraw %}</pre>

Again, rewriting gives us two familiar equations.

  0       * n  =  0
  (1 + m) * n  =  n + (m * n)

The first follows because zero times anything is zero,
and the second follow because multiplication distributes
over addition.  In its most general form, distribution of
multiplication over addition is written

  (m + n) * p  =  (m * p) + (n * p)

We get the second equation from this one by taking `m` to be `1`, `n`
to be `m`, and `p` to be `n`, and then using the fact that one is a
left identity for multiplication, so `1 * n = n`.

Again, the definition is well-founded in that multiplication of
larger numbers is defined in terms of multiplication of smaller numbers.
 
For example, let's multiply two and three.

       2 * 3
    =    (iv)
       3 + (1 * 3)
    =    (iv)
       3 + (3 + (0 * 3))
    =    (iii)
       3 + (3 + 0)
    =
       6

The first use of (iv) matches by taking `m = 1` and `n = 3`,
The second use of (iv) matches by taking `m = 0` and `n = 3`,
and the use of (iii) matches by taking `n = 3`.

**Exercise** Compute `3 * 4` by the same technique.


## Exponentiation

Similarly, once we have defined multiplication, we can define
exponentiation as repeated multiplication.
<pre class="Agda">{% raw %}
<a name="13343" href="Naturals.html#13343" class="Function Operator"
      >_^_</a
      ><a name="13346"
      > </a
      ><a name="13347" class="Symbol"
      >:</a
      ><a name="13348"
      > </a
      ><a name="13349" href="Naturals.html#1064" class="Datatype"
      >&#8469;</a
      ><a name="13350"
      > </a
      ><a name="13351" class="Symbol"
      >&#8594;</a
      ><a name="13352"
      > </a
      ><a name="13353" href="Naturals.html#1064" class="Datatype"
      >&#8469;</a
      ><a name="13354"
      > </a
      ><a name="13355" class="Symbol"
      >&#8594;</a
      ><a name="13356"
      > </a
      ><a name="13357" href="Naturals.html#1064" class="Datatype"
      >&#8469;</a
      ><a name="13358"
      >
</a
      ><a name="13359" href="Naturals.html#13359" class="Bound"
      >n</a
      ><a name="13360"
      > </a
      ><a name="13361" href="Naturals.html#13343" class="Function Operator"
      >^</a
      ><a name="13362"
      > </a
      ><a name="13363" href="Naturals.html#1080" class="InductiveConstructor"
      >zero</a
      ><a name="13367"
      >     </a
      ><a name="13372" class="Symbol"
      >=</a
      ><a name="13373"
      >  </a
      ><a name="13375" href="Naturals.html#1091" class="InductiveConstructor"
      >suc</a
      ><a name="13378"
      > </a
      ><a name="13379" href="Naturals.html#1080" class="InductiveConstructor"
      >zero</a
      ><a name="13383"
      >       </a
      ><a name="13390" class="Comment"
      >-- (v)</a
      ><a name="13396"
      >
</a
      ><a name="13397" href="Naturals.html#13397" class="Bound"
      >n</a
      ><a name="13398"
      > </a
      ><a name="13399" href="Naturals.html#13343" class="Function Operator"
      >^</a
      ><a name="13400"
      > </a
      ><a name="13401" class="Symbol"
      >(</a
      ><a name="13402" href="Naturals.html#1091" class="InductiveConstructor"
      >suc</a
      ><a name="13405"
      > </a
      ><a name="13406" href="Naturals.html#13406" class="Bound"
      >m</a
      ><a name="13407" class="Symbol"
      >)</a
      ><a name="13408"
      >  </a
      ><a name="13410" class="Symbol"
      >=</a
      ><a name="13411"
      >  </a
      ><a name="13413" href="Naturals.html#13397" class="Bound"
      >n</a
      ><a name="13414"
      > </a
      ><a name="13415" href="Naturals.html#12016" class="Function Operator"
      >*</a
      ><a name="13416"
      > </a
      ><a name="13417" class="Symbol"
      >(</a
      ><a name="13418" href="Naturals.html#13397" class="Bound"
      >n</a
      ><a name="13419"
      > </a
      ><a name="13420" href="Naturals.html#13343" class="Function Operator"
      >^</a
      ><a name="13421"
      > </a
      ><a name="13422" href="Naturals.html#13406" class="Bound"
      >m</a
      ><a name="13423" class="Symbol"
      >)</a
      ><a name="13424"
      >    </a
      ><a name="13428" class="Comment"
      >-- (vi)</a
      >
{% endraw %}</pre>

**Exercise** Compute `4 ^ 3`.


## Monus

We can also define subtraction.  Since there are no negative
natural numbers, if we subtract a larger number from a smaller
number we will take the result to be zero.  This adaption of
subtraction to naturals is called *monus* (as compared to *minus*).

Monus is our first example of a definition that uses pattern
matching against both arguments.
<pre class="Agda">{% raw %}
<a name="13851" href="Naturals.html#13851" class="Function Operator"
      >_&#8760;_</a
      ><a name="13854"
      > </a
      ><a name="13855" class="Symbol"
      >:</a
      ><a name="13856"
      > </a
      ><a name="13857" href="Naturals.html#1064" class="Datatype"
      >&#8469;</a
      ><a name="13858"
      > </a
      ><a name="13859" class="Symbol"
      >&#8594;</a
      ><a name="13860"
      > </a
      ><a name="13861" href="Naturals.html#1064" class="Datatype"
      >&#8469;</a
      ><a name="13862"
      > </a
      ><a name="13863" class="Symbol"
      >&#8594;</a
      ><a name="13864"
      > </a
      ><a name="13865" href="Naturals.html#1064" class="Datatype"
      >&#8469;</a
      ><a name="13866"
      >
</a
      ><a name="13867" href="Naturals.html#13867" class="Bound"
      >m</a
      ><a name="13868"
      >       </a
      ><a name="13875" href="Naturals.html#13851" class="Function Operator"
      >&#8760;</a
      ><a name="13876"
      > </a
      ><a name="13877" href="Naturals.html#1080" class="InductiveConstructor"
      >zero</a
      ><a name="13881"
      >     </a
      ><a name="13886" class="Symbol"
      >=</a
      ><a name="13887"
      >  </a
      ><a name="13889" href="Naturals.html#13867" class="Bound"
      >m</a
      ><a name="13890"
      >         </a
      ><a name="13899" class="Comment"
      >-- (vii)</a
      ><a name="13907"
      >
</a
      ><a name="13908" href="Naturals.html#1080" class="InductiveConstructor"
      >zero</a
      ><a name="13912"
      >    </a
      ><a name="13916" href="Naturals.html#13851" class="Function Operator"
      >&#8760;</a
      ><a name="13917"
      > </a
      ><a name="13918" class="Symbol"
      >(</a
      ><a name="13919" href="Naturals.html#1091" class="InductiveConstructor"
      >suc</a
      ><a name="13922"
      > </a
      ><a name="13923" href="Naturals.html#13923" class="Bound"
      >n</a
      ><a name="13924" class="Symbol"
      >)</a
      ><a name="13925"
      >  </a
      ><a name="13927" class="Symbol"
      >=</a
      ><a name="13928"
      >  </a
      ><a name="13930" href="Naturals.html#1080" class="InductiveConstructor"
      >zero</a
      ><a name="13934"
      >      </a
      ><a name="13940" class="Comment"
      >-- (viii)</a
      ><a name="13949"
      >
</a
      ><a name="13950" class="Symbol"
      >(</a
      ><a name="13951" href="Naturals.html#1091" class="InductiveConstructor"
      >suc</a
      ><a name="13954"
      > </a
      ><a name="13955" href="Naturals.html#13955" class="Bound"
      >m</a
      ><a name="13956" class="Symbol"
      >)</a
      ><a name="13957"
      > </a
      ><a name="13958" href="Naturals.html#13851" class="Function Operator"
      >&#8760;</a
      ><a name="13959"
      > </a
      ><a name="13960" class="Symbol"
      >(</a
      ><a name="13961" href="Naturals.html#1091" class="InductiveConstructor"
      >suc</a
      ><a name="13964"
      > </a
      ><a name="13965" href="Naturals.html#13965" class="Bound"
      >n</a
      ><a name="13966" class="Symbol"
      >)</a
      ><a name="13967"
      >  </a
      ><a name="13969" class="Symbol"
      >=</a
      ><a name="13970"
      >  </a
      ><a name="13972" href="Naturals.html#13955" class="Bound"
      >m</a
      ><a name="13973"
      > </a
      ><a name="13974" href="Naturals.html#13851" class="Function Operator"
      >&#8760;</a
      ><a name="13975"
      > </a
      ><a name="13976" href="Naturals.html#13965" class="Bound"
      >n</a
      ><a name="13977"
      >     </a
      ><a name="13982" class="Comment"
      >-- (ix)</a
      >
{% endraw %}</pre>
We can do a simple analysis to show that all the cases are covered.

  * The second argument is either `zero` or `suc n` for some `n`.
    + If it is `zero`, then equation (vii) applies.
    + If it is `suc n`, then the first argument is either `zero`
      or `suc m` for some `m`.
      - If it is `zero`, then equation (viii) applies.
      - If it is `suc m`, then equation (ix) applies.

Again, the recursive definition is well-founded because
monus on bigger numbers is defined in terms of monus on
small numbers.

For example, let's subtract two from three.

       3 ∸ 2
    =    (ix)
       2 ∸ 1
    =    (ix)
       1 ∸ 0
    =    (vii)
       1

We did not use equation (viii) at all, but it will be required
if we try to subtract a smaller number from a larger one.

       2 ∸ 3
    =    (ix)
       1 ∸ 2
    =    (ix)
       0 ∸ 1
    =    (viii)
       0

**Exercise** Compute `5 ∸ 3` and `3 ∸ 5` by the same technique.

## The story of creation, revisited

As with the definition of the naturals by induction, in the definition
of addition by recursion we have defined addition in terms of addition.

Again, it is possible to assign our definition a meaning without
resorting to unpermitted circularities.  We do so by reducing our
definition to equivalent inference rules for judgements about equality.

    ------------
    zero + n = n

    m + n = p
    -------------------
    (suc m) + n = suc p

Here we assume we have already defined the infinite set of natural
numbers, specifying the meaning of the judgment `n : ℕ`.  The first
inference rule is the base case, and corresponds to line (i) of the
definition.  It asserts that if `n` is a natural number then adding
zero to it gives `n`.  The second inference rule is the inductive
case, and corresponds to line (ii) of the definition. It asserts that
if adding `m` and `n` gives `p`, then adding `suc m` and `n` gives
`suc p`.

Again we resort to a creation story, where this time we are
concerned with judgements about addition.

    -- in the beginning, we know nothing about addition

Now, we apply the rules to all the judgment we know about.
The base case tells us that `zero + n = n` for every natural `n`,
so we add all those equations.  The inductive case tells us that if
`m + n = p` (on the day before today) then `suc m + n = suc p`
(today).  We didn't know any equations about addition before today,
so that rule doesn't give us any new equations.

    -- on the first day, we know about addition of 0
    0 + 0 = 0     0 + 1 = 1    0 + 2 = 2     ...

Then we repeat the process, so on the next day we know about all the
equations from the day before, plus any equations added by the rules.
The base case tells us nothing new, but now the inductive case adds
more equations.

    -- on the second day, we know about addition of 0 and 1
    0 + 0 = 0     0 + 1 = 1     0 + 2 = 2     0 + 3 = 3     ...
    1 + 0 = 1     1 + 1 = 2     1 + 2 = 3     1 + 3 = 4     ...

And we repeat the process again.  

    -- on the third day, we know about addition of 0, 1, and 2
    0 + 0 = 0     0 + 1 = 1     0 + 2 = 2     0 + 3 = 3     ...
    1 + 0 = 1     1 + 1 = 2     1 + 2 = 3     1 + 3 = 4     ...
    2 + 0 = 2     2 + 1 = 3     2 + 2 = 4     2 + 3 = 5     ...

You've probably got the hang of it by now.

    -- on the fourth day, we know about addition of 0, 1, 2, and 3
    0 + 0 = 0     0 + 1 = 1     0 + 2 = 2     0 + 3 = 3     ...
    1 + 0 = 1     1 + 1 = 2     1 + 2 = 3     1 + 3 = 4     ...
    2 + 0 = 2     2 + 1 = 3     2 + 2 = 4     2 + 3 = 5     ...
    3 + 0 = 3     3 + 1 = 4     3 + 2 = 5     3 + 3 = 6     ...

The process continues.  On the *m*th day we will know all the
equations where the first number is less than *m*.

As we can see, the reasoning that justifies inductive and recursive
definitions is quite similar.  They might be considered two sides of
the same coin.


## Precedence

We often use *precedence* to avoid writing too many parentheses.
Application *binds more tightly than* (or *has precedence over*) any
operator, and so we may write `suc m + n` to mean `(suc m) + n`.
As another example, we say that multiplication binds more tightly than
addition, and so write `n + m * n` to mean `n + (m * n)`.
We also sometimes say that addition is *associates to the left*, and
so write `m + n + p` to mean `(m + n) + p`.

In Agda the precedence and associativity of infix operators
needs to be declared.
<pre class="Agda">{% raw %}
<a name="18435" class="Keyword"
      >infixl</a
      ><a name="18441"
      > </a
      ><a name="18442" class="Number"
      >7</a
      ><a name="18443"
      >  </a
      ><a name="18445" href="Naturals.html#12016" class="Primitive Operator"
      >_*_</a
      ><a name="18448"
      >
</a
      ><a name="18449" class="Keyword"
      >infixl</a
      ><a name="18455"
      > </a
      ><a name="18456" class="Number"
      >6</a
      ><a name="18457"
      >  </a
      ><a name="18459" href="Naturals.html#9439" class="Primitive Operator"
      >_+_</a
      ><a name="18462"
      >  </a
      ><a name="18464" href="Naturals.html#13851" class="Primitive Operator"
      >_&#8760;_</a
      >
{% endraw %}</pre>
This states that operator `_*_` has precedence level 7, and that
operators `_+_` and `_∸_` have precedence level 6.  Multiplication
binds more tightly that addition or subtraction because it has a
higher precedence.  Writing `infixl` indicates that all three
operators associate to the left.  One can also write `infixr` to
indicate that an operator associates to the right, or just `infix` to
indicate that it has no associativity and parentheses are always
required to disambiguate.

## More pragmas

Inluding the lines
<pre class="Agda">{% raw %}
<a name="19014" class="Symbol"
      >{-#</a
      ><a name="19017"
      > </a
      ><a name="19018" class="Keyword"
      >BUILTIN</a
      ><a name="19025"
      > NATPLUS </a
      ><a name="19034" href="Naturals.html#9439" class="Primitive Operator"
      >_+_</a
      ><a name="19037"
      > </a
      ><a name="19038" class="Symbol"
      >#-}</a
      ><a name="19041"
      >
</a
      ><a name="19042" class="Symbol"
      >{-#</a
      ><a name="19045"
      > </a
      ><a name="19046" class="Keyword"
      >BUILTIN</a
      ><a name="19053"
      > NATTIMES </a
      ><a name="19063" href="Naturals.html#12016" class="Primitive Operator"
      >_*_</a
      ><a name="19066"
      > </a
      ><a name="19067" class="Symbol"
      >#-}</a
      ><a name="19070"
      >
</a
      ><a name="19071" class="Symbol"
      >{-#</a
      ><a name="19074"
      > </a
      ><a name="19075" class="Keyword"
      >BUILTIN</a
      ><a name="19082"
      > NATMINUS </a
      ><a name="19092" href="Naturals.html#13851" class="Primitive Operator"
      >_&#8760;_</a
      ><a name="19095"
      > </a
      ><a name="19096" class="Symbol"
      >#-}</a
      >
{% endraw %}</pre>
tells Agda that these three operators correspond to the usual ones,
and enables it to perform these computations using the corresponing
Haskell operators on the integer type.  Representing naturals with
`zero` and `suc` requires time proportional to *m* to add *m* and *n*,
whereas representing naturals as integers in Haskell requires time
proportional to the larger of the logarithms of *m* and *n*.  In
particular, if *m* and *n* are both less than 2⁶⁴, it will require
constant time on a machine with 64-bit words.  Similarly, representing
naturals with `zero` and `suc` requires time proportional to the
product of *m* and *n* to multiply *m* and *n*, whereas representing
naturals as integers in Haskell requires time proportional to the sum
of the logarithms of *m* and *n*.

## Unicode

In each chapter, we will list at the end all unicode characters that
first appear in that chapter.  This chapter introduces the following
unicode.

    ℕ  U+2115  DOUBLE-STRUCK CAPITAL N (\bN)  
    →  U+2192  RIGHTWARDS ARROW (\to, \r)
    ∸  U+2238  DOT MINUS (\.-)

Each line consists of the Unicode character (ℕ), the corresponding
code point (U+2115), the name of the character (DOUBLE-STRUCK CAPITAL N),
and the sequence to type into Emacs to generate the character (\bN).

The command \r is a little different to the others, because it gives
access to a wide variety of Unicode arrows.  After typing \r, one can access
the many available arrows by using the left, right, up, and down
keys on the keyboard to navigate.
