---
title     : "Relations: Inductive Definition of Relations"
layout    : page
permalink : /Relations
---

After having defined operations such as addition and multiplication,
the next step is to define relations, such as *less than or equal*.

## Imports

<pre class="Agda">{% raw %}
<a name="272" class="Keyword"
      >open</a
      ><a name="276"
      > </a
      ><a name="277" class="Keyword"
      >import</a
      ><a name="283"
      > </a
      ><a name="284" class="Module"
      >Naturals</a
      ><a name="292"
      > </a
      ><a name="293" class="Keyword"
      >using</a
      ><a name="298"
      > </a
      ><a name="299" class="Symbol"
      >(</a
      ><a name="300" href="Naturals.html#1064" class="Datatype"
      >&#8469;</a
      ><a name="301" class="Symbol"
      >;</a
      ><a name="302"
      > </a
      ><a name="303" href="Naturals.html#1080" class="InductiveConstructor"
      >zero</a
      ><a name="307" class="Symbol"
      >;</a
      ><a name="308"
      > </a
      ><a name="309" href="Naturals.html#1091" class="InductiveConstructor"
      >suc</a
      ><a name="312" class="Symbol"
      >;</a
      ><a name="313"
      > </a
      ><a name="314" href="Naturals.html#9439" class="Primitive Operator"
      >_+_</a
      ><a name="317" class="Symbol"
      >;</a
      ><a name="318"
      > </a
      ><a name="319" href="Naturals.html#12016" class="Primitive Operator"
      >_*_</a
      ><a name="322" class="Symbol"
      >;</a
      ><a name="323"
      > </a
      ><a name="324" href="Naturals.html#13851" class="Primitive Operator"
      >_&#8760;_</a
      ><a name="327" class="Symbol"
      >)</a
      ><a name="328"
      >
</a
      ><a name="329" class="Keyword"
      >open</a
      ><a name="333"
      > </a
      ><a name="334" class="Keyword"
      >import</a
      ><a name="340"
      > </a
      ><a name="341" class="Module"
      >Properties</a
      ><a name="351"
      > </a
      ><a name="352" class="Keyword"
      >using</a
      ><a name="357"
      > </a
      ><a name="358" class="Symbol"
      >(</a
      ><a name="359" href="Properties.html#17070" class="Function"
      >+-comm</a
      ><a name="365" class="Symbol"
      >)</a
      ><a name="366"
      >
</a
      ><a name="367" class="Keyword"
      >open</a
      ><a name="371"
      > </a
      ><a name="372" class="Keyword"
      >import</a
      ><a name="378"
      > </a
      ><a name="379" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#1" class="Module"
      >Relation.Binary.PropositionalEquality</a
      ><a name="416"
      > </a
      ><a name="417" class="Keyword"
      >using</a
      ><a name="422"
      > </a
      ><a name="423" class="Symbol"
      >(</a
      ><a name="424" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >_&#8801;_</a
      ><a name="427" class="Symbol"
      >;</a
      ><a name="428"
      > </a
      ><a name="429" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="433" class="Symbol"
      >)</a
      >
{% endraw %}</pre>

## Defining relations

The relation *less than or equal* has an infinite number of
instances.  Here are just a few of them:

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
<pre class="Agda">{% raw %}
<a name="1109" class="Keyword"
      >data</a
      ><a name="1113"
      > </a
      ><a name="1114" href="Relations.html#1114" class="Datatype Operator"
      >_&#8804;_</a
      ><a name="1117"
      > </a
      ><a name="1118" class="Symbol"
      >:</a
      ><a name="1119"
      > </a
      ><a name="1120" href="Naturals.html#1064" class="Datatype"
      >&#8469;</a
      ><a name="1121"
      > </a
      ><a name="1122" class="Symbol"
      >&#8594;</a
      ><a name="1123"
      > </a
      ><a name="1124" href="Naturals.html#1064" class="Datatype"
      >&#8469;</a
      ><a name="1125"
      > </a
      ><a name="1126" class="Symbol"
      >&#8594;</a
      ><a name="1127"
      > </a
      ><a name="1128" class="PrimitiveType"
      >Set</a
      ><a name="1131"
      > </a
      ><a name="1132" class="Keyword"
      >where</a
      ><a name="1137"
      >
  </a
      ><a name="1140" href="Relations.html#1140" class="InductiveConstructor"
      >z&#8804;n</a
      ><a name="1143"
      > </a
      ><a name="1144" class="Symbol"
      >:</a
      ><a name="1145"
      > </a
      ><a name="1146" class="Symbol"
      >&#8704;</a
      ><a name="1147"
      > </a
      ><a name="1148" class="Symbol"
      >{</a
      ><a name="1149" href="Relations.html#1149" class="Bound"
      >m</a
      ><a name="1150"
      > </a
      ><a name="1151" class="Symbol"
      >:</a
      ><a name="1152"
      > </a
      ><a name="1153" href="Naturals.html#1064" class="Datatype"
      >&#8469;</a
      ><a name="1154" class="Symbol"
      >}</a
      ><a name="1155"
      > </a
      ><a name="1156" class="Symbol"
      >&#8594;</a
      ><a name="1157"
      > </a
      ><a name="1158" href="Naturals.html#1080" class="InductiveConstructor"
      >zero</a
      ><a name="1162"
      > </a
      ><a name="1163" href="Relations.html#1114" class="Datatype Operator"
      >&#8804;</a
      ><a name="1164"
      > </a
      ><a name="1165" href="Relations.html#1149" class="Bound"
      >m</a
      ><a name="1166"
      >
  </a
      ><a name="1169" href="Relations.html#1169" class="InductiveConstructor"
      >s&#8804;s</a
      ><a name="1172"
      > </a
      ><a name="1173" class="Symbol"
      >:</a
      ><a name="1174"
      > </a
      ><a name="1175" class="Symbol"
      >&#8704;</a
      ><a name="1176"
      > </a
      ><a name="1177" class="Symbol"
      >{</a
      ><a name="1178" href="Relations.html#1178" class="Bound"
      >m</a
      ><a name="1179"
      > </a
      ><a name="1180" href="Relations.html#1180" class="Bound"
      >n</a
      ><a name="1181"
      > </a
      ><a name="1182" class="Symbol"
      >:</a
      ><a name="1183"
      > </a
      ><a name="1184" href="Naturals.html#1064" class="Datatype"
      >&#8469;</a
      ><a name="1185" class="Symbol"
      >}</a
      ><a name="1186"
      > </a
      ><a name="1187" class="Symbol"
      >&#8594;</a
      ><a name="1188"
      > </a
      ><a name="1189" href="Relations.html#1178" class="Bound"
      >m</a
      ><a name="1190"
      > </a
      ><a name="1191" href="Relations.html#1114" class="Datatype Operator"
      >&#8804;</a
      ><a name="1192"
      > </a
      ><a name="1193" href="Relations.html#1180" class="Bound"
      >n</a
      ><a name="1194"
      > </a
      ><a name="1195" class="Symbol"
      >&#8594;</a
      ><a name="1196"
      > </a
      ><a name="1197" href="Naturals.html#1091" class="InductiveConstructor"
      >suc</a
      ><a name="1200"
      > </a
      ><a name="1201" href="Relations.html#1178" class="Bound"
      >m</a
      ><a name="1202"
      > </a
      ><a name="1203" href="Relations.html#1114" class="Datatype Operator"
      >&#8804;</a
      ><a name="1204"
      > </a
      ><a name="1205" href="Naturals.html#1091" class="InductiveConstructor"
      >suc</a
      ><a name="1208"
      > </a
      ><a name="1209" href="Relations.html#1180" class="Bound"
      >n</a
      >
{% endraw %}</pre>
Here `z≤n` and `s≤s` (with no spaces) are constructor names,
while `m ≤ m`, and `m ≤ n` and `suc m ≤ suc n` (with spaces)
are propositions.

Both definitions above tell us the same two things:

+ *Base case*: for all naturals `n`, the proposition `zero ≤ n` holds
+ *Inductive case*: for all naturals `m` and `n`, if the proposition
  `m ≤ n` holds, then the proposition `suc m ≤ suc n` holds.

In fact, they each give us a bit more detail:

+ *Base case*: for all naturals `n`, the constructor `z≤n` 
  produces evidence that `zero ≤ n` holds.
+ *Inductive case*: for all naturals `m` and `n`, the constructor
  `s≤s` takes evidence that `m ≤ n` holds into evidence that
  `suc m ≤ suc n` holds.

Here we have used the word *evidence* as interchangeable with the
word *proof*.  We will tend to say *evidence* when we want to stress
that proofs are just terms in Agda.

For example, here in inference rule notation is the proof that
`2 ≤ 4`.

      z≤n -----
          0 ≤ 2
     s≤s -------
          1 ≤ 3
    s≤s ---------
          2 ≤ 4

And here is the corresponding Agda proof.
<pre class="Agda">{% raw %}
<a name="2320" href="Relations.html#2320" class="Function"
      >ex&#8321;</a
      ><a name="2323"
      > </a
      ><a name="2324" class="Symbol"
      >:</a
      ><a name="2325"
      > </a
      ><a name="2326" class="Number"
      >2</a
      ><a name="2327"
      > </a
      ><a name="2328" href="Relations.html#1114" class="Datatype Operator"
      >&#8804;</a
      ><a name="2329"
      > </a
      ><a name="2330" class="Number"
      >4</a
      ><a name="2331"
      >
</a
      ><a name="2332" href="Relations.html#2320" class="Function"
      >ex&#8321;</a
      ><a name="2335"
      > </a
      ><a name="2336" class="Symbol"
      >=</a
      ><a name="2337"
      > </a
      ><a name="2338" href="Relations.html#1169" class="InductiveConstructor"
      >s&#8804;s</a
      ><a name="2341"
      > </a
      ><a name="2342" class="Symbol"
      >(</a
      ><a name="2343" href="Relations.html#1169" class="InductiveConstructor"
      >s&#8804;s</a
      ><a name="2346"
      > </a
      ><a name="2347" href="Relations.html#1140" class="InductiveConstructor"
      >z&#8804;n</a
      ><a name="2350" class="Symbol"
      >)</a
      >
{% endraw %}</pre>

## Implicit arguments

In the Agda definition, the two lines defining the constructors
use `∀`, very similar to our use of `∀` in propositions such as:

    com+ : ∀ (m n : ℕ) → m + n ≡ n + m

However, here the declarations are surrounded by curly braces `{ }`
rather than parentheses `( )`.  This means that the arguments are
*implicit* and need not be written explicitly.  Thus, we would write,
for instance, `com+ m n` for the proof that `m + n ≡ n + m`, but
here will write `z≤n` for the proof that `m ≤ m`, leaving the `m` implicit,
or if `m≤n` is evidence that `m ≤ n`, we write write `s≤s m≤n` for the
evidence that `suc m ≤ suc n`, leaving both `m` and `n` implicit.

It is possible to provide implicit arguments explicitly if we wish, by
writing the arguments inside curly braces.  For instance, here is the
Agda proof that `2 ≤ 4` repeated, with the implicit arguments made
explicit.
<pre class="Agda">{% raw %}
<a name="3271" href="Relations.html#3271" class="Function"
      >ex&#8322;</a
      ><a name="3274"
      > </a
      ><a name="3275" class="Symbol"
      >:</a
      ><a name="3276"
      > </a
      ><a name="3277" class="Number"
      >2</a
      ><a name="3278"
      > </a
      ><a name="3279" href="Relations.html#1114" class="Datatype Operator"
      >&#8804;</a
      ><a name="3280"
      > </a
      ><a name="3281" class="Number"
      >4</a
      ><a name="3282"
      >
</a
      ><a name="3283" href="Relations.html#3271" class="Function"
      >ex&#8322;</a
      ><a name="3286"
      > </a
      ><a name="3287" class="Symbol"
      >=</a
      ><a name="3288"
      > </a
      ><a name="3289" href="Relations.html#1169" class="InductiveConstructor"
      >s&#8804;s</a
      ><a name="3292"
      > </a
      ><a name="3293" class="Symbol"
      >{</a
      ><a name="3294" class="Number"
      >1</a
      ><a name="3295" class="Symbol"
      >}</a
      ><a name="3296"
      > </a
      ><a name="3297" class="Symbol"
      >{</a
      ><a name="3298" class="Number"
      >3</a
      ><a name="3299" class="Symbol"
      >}</a
      ><a name="3300"
      > </a
      ><a name="3301" class="Symbol"
      >(</a
      ><a name="3302" href="Relations.html#1169" class="InductiveConstructor"
      >s&#8804;s</a
      ><a name="3305"
      > </a
      ><a name="3306" class="Symbol"
      >{</a
      ><a name="3307" class="Number"
      >0</a
      ><a name="3308" class="Symbol"
      >}</a
      ><a name="3309"
      > </a
      ><a name="3310" class="Symbol"
      >{</a
      ><a name="3311" class="Number"
      >2</a
      ><a name="3312" class="Symbol"
      >}</a
      ><a name="3313"
      > </a
      ><a name="3314" class="Symbol"
      >(</a
      ><a name="3315" href="Relations.html#1140" class="InductiveConstructor"
      >z&#8804;n</a
      ><a name="3318"
      > </a
      ><a name="3319" class="Symbol"
      >{</a
      ><a name="3320" class="Number"
      >2</a
      ><a name="3321" class="Symbol"
      >}))</a
      >
{% endraw %}</pre>

## Precedence

We declare the precedence for comparison as follows.
<pre class="Agda">{% raw %}
<a name="3418" class="Keyword"
      >infix</a
      ><a name="3423"
      > </a
      ><a name="3424" class="Number"
      >4</a
      ><a name="3425"
      > </a
      ><a name="3426" href="Relations.html#1114" class="Datatype Operator"
      >_&#8804;_</a
      >
{% endraw %}</pre>
We set the precedence of `_≤_` at level 4, which means it binds less
tightly that `_+_` at level 6 or `_*_` at level 7, meaning that `1 + 2
≤ 3` parses as `(1 + 2) ≤ 3`.  We write `infix` to indicate that the
operator does not associate to either the left or right, as it makes
no sense to give `1 ≤ 2 ≤ 3` either the meaning `(1 ≤ 2) ≤ 3` or `1 ≤
(2 ≤ 3)`.

## Properties of ordering relations

Relations occur all the time, and mathematicians have agreed
on names for some of the most common properties.

+ *Reflexive* For all `n`, the relation `n ≤ n` holds.
+ *Transitive* For all `m`, `n`, and `p`, if `m ≤ n` and
`n ≤ p` hold, then `m ≤ p` holds.
+ *Anti-symmetric* For all `m` and `n`, if both `m ≤ n` and
`n ≤ m` hold, then `m ≡ n` holds.
+ *Total* For all `m` and `n`, either `m ≤ n` or `n ≤ m`
holds.

The relation `_≤_` satisfies all four of these properties.

There are also names for some combinations of these properties.

+ *Preorder* Any relation that is reflexive and transitive.
+ *Partial order* Any preorder that is also anti-symmetric.
+ *Total order* Any partial order that is also total.

If you ever bump into a relation at a party, you now know how
to make small talk, by asking it whether it is reflexive, transitive,
anti-symmetric, and total. Or instead you might ask whether it is a
preorder, partial order, or total order.

Less frivolously, if you ever bump into a relation while reading
a technical paper, this gives you an easy way to orient yourself,
by checking whether or not it is a preorder, partial order, or total order.
A careful author will often make it explicit, for instance by saying
that a given relation is a preoder but not a partial order, or a
partial order but not a total order. (Can you think of examples of
such relations?)


## Reflexivity

The first property to prove about comparison is that it is reflexive:
for any natural `n`, the relation `n ≤ n` holds.
<pre class="Agda">{% raw %}
<a name="5370" href="Relations.html#5370" class="Function"
      >&#8804;-refl</a
      ><a name="5376"
      > </a
      ><a name="5377" class="Symbol"
      >:</a
      ><a name="5378"
      > </a
      ><a name="5379" class="Symbol"
      >&#8704;</a
      ><a name="5380"
      > </a
      ><a name="5381" class="Symbol"
      >(</a
      ><a name="5382" href="Relations.html#5382" class="Bound"
      >n</a
      ><a name="5383"
      > </a
      ><a name="5384" class="Symbol"
      >:</a
      ><a name="5385"
      > </a
      ><a name="5386" href="Naturals.html#1064" class="Datatype"
      >&#8469;</a
      ><a name="5387" class="Symbol"
      >)</a
      ><a name="5388"
      > </a
      ><a name="5389" class="Symbol"
      >&#8594;</a
      ><a name="5390"
      > </a
      ><a name="5391" href="Relations.html#5382" class="Bound"
      >n</a
      ><a name="5392"
      > </a
      ><a name="5393" href="Relations.html#1114" class="Datatype Operator"
      >&#8804;</a
      ><a name="5394"
      > </a
      ><a name="5395" href="Relations.html#5382" class="Bound"
      >n</a
      ><a name="5396"
      >
</a
      ><a name="5397" href="Relations.html#5370" class="Function"
      >&#8804;-refl</a
      ><a name="5403"
      > </a
      ><a name="5404" href="Naturals.html#1080" class="InductiveConstructor"
      >zero</a
      ><a name="5408"
      > </a
      ><a name="5409" class="Symbol"
      >=</a
      ><a name="5410"
      > </a
      ><a name="5411" href="Relations.html#1140" class="InductiveConstructor"
      >z&#8804;n</a
      ><a name="5414"
      >
</a
      ><a name="5415" href="Relations.html#5370" class="Function"
      >&#8804;-refl</a
      ><a name="5421"
      > </a
      ><a name="5422" class="Symbol"
      >(</a
      ><a name="5423" href="Naturals.html#1091" class="InductiveConstructor"
      >suc</a
      ><a name="5426"
      > </a
      ><a name="5427" href="Relations.html#5427" class="Bound"
      >n</a
      ><a name="5428" class="Symbol"
      >)</a
      ><a name="5429"
      > </a
      ><a name="5430" class="Symbol"
      >=</a
      ><a name="5431"
      > </a
      ><a name="5432" href="Relations.html#1169" class="InductiveConstructor"
      >s&#8804;s</a
      ><a name="5435"
      > </a
      ><a name="5436" class="Symbol"
      >(</a
      ><a name="5437" href="Relations.html#5370" class="Function"
      >&#8804;-refl</a
      ><a name="5443"
      > </a
      ><a name="5444" href="Relations.html#5427" class="Bound"
      >n</a
      ><a name="5445" class="Symbol"
      >)</a
      >
{% endraw %}</pre>
The proof is a straightforward induction on `n`.  In the base case,
`zero ≤ zero` holds by `z≤n`.  In the inductive case, the inductive
hypothesis `≤-refl n` gives us a proof of `n ≤ n`, and applying `s≤s`
to that yields a proof of `suc n ≤ suc n`.

It is a good exercise to prove reflexivity interactively in Emacs,
using holes and the `^C ^C`, `^C ^,`, and `^C ^R` commands.


## Transitivity

The second property to prove about comparison is that it is
transitive: for any naturals `m`, `n`, andl `p`, if `m ≤ n` and `n ≤
p` hold, then `m ≤ p` holds.
<pre class="Agda">{% raw %}
<a name="6025" href="Relations.html#6025" class="Function"
      >&#8804;-trans</a
      ><a name="6032"
      > </a
      ><a name="6033" class="Symbol"
      >:</a
      ><a name="6034"
      > </a
      ><a name="6035" class="Symbol"
      >&#8704;</a
      ><a name="6036"
      > </a
      ><a name="6037" class="Symbol"
      >{</a
      ><a name="6038" href="Relations.html#6038" class="Bound"
      >m</a
      ><a name="6039"
      > </a
      ><a name="6040" href="Relations.html#6040" class="Bound"
      >n</a
      ><a name="6041"
      > </a
      ><a name="6042" href="Relations.html#6042" class="Bound"
      >p</a
      ><a name="6043"
      > </a
      ><a name="6044" class="Symbol"
      >:</a
      ><a name="6045"
      > </a
      ><a name="6046" href="Naturals.html#1064" class="Datatype"
      >&#8469;</a
      ><a name="6047" class="Symbol"
      >}</a
      ><a name="6048"
      > </a
      ><a name="6049" class="Symbol"
      >&#8594;</a
      ><a name="6050"
      > </a
      ><a name="6051" href="Relations.html#6038" class="Bound"
      >m</a
      ><a name="6052"
      > </a
      ><a name="6053" href="Relations.html#1114" class="Datatype Operator"
      >&#8804;</a
      ><a name="6054"
      > </a
      ><a name="6055" href="Relations.html#6040" class="Bound"
      >n</a
      ><a name="6056"
      > </a
      ><a name="6057" class="Symbol"
      >&#8594;</a
      ><a name="6058"
      > </a
      ><a name="6059" href="Relations.html#6040" class="Bound"
      >n</a
      ><a name="6060"
      > </a
      ><a name="6061" href="Relations.html#1114" class="Datatype Operator"
      >&#8804;</a
      ><a name="6062"
      > </a
      ><a name="6063" href="Relations.html#6042" class="Bound"
      >p</a
      ><a name="6064"
      > </a
      ><a name="6065" class="Symbol"
      >&#8594;</a
      ><a name="6066"
      > </a
      ><a name="6067" href="Relations.html#6038" class="Bound"
      >m</a
      ><a name="6068"
      > </a
      ><a name="6069" href="Relations.html#1114" class="Datatype Operator"
      >&#8804;</a
      ><a name="6070"
      > </a
      ><a name="6071" href="Relations.html#6042" class="Bound"
      >p</a
      ><a name="6072"
      >
</a
      ><a name="6073" href="Relations.html#6025" class="Function"
      >&#8804;-trans</a
      ><a name="6080"
      > </a
      ><a name="6081" href="Relations.html#1140" class="InductiveConstructor"
      >z&#8804;n</a
      ><a name="6084"
      > </a
      ><a name="6085" class="Symbol"
      >_</a
      ><a name="6086"
      > </a
      ><a name="6087" class="Symbol"
      >=</a
      ><a name="6088"
      > </a
      ><a name="6089" href="Relations.html#1140" class="InductiveConstructor"
      >z&#8804;n</a
      ><a name="6092"
      >
</a
      ><a name="6093" href="Relations.html#6025" class="Function"
      >&#8804;-trans</a
      ><a name="6100"
      > </a
      ><a name="6101" class="Symbol"
      >(</a
      ><a name="6102" href="Relations.html#1169" class="InductiveConstructor"
      >s&#8804;s</a
      ><a name="6105"
      > </a
      ><a name="6106" href="Relations.html#6106" class="Bound"
      >m&#8804;n</a
      ><a name="6109" class="Symbol"
      >)</a
      ><a name="6110"
      > </a
      ><a name="6111" class="Symbol"
      >(</a
      ><a name="6112" href="Relations.html#1169" class="InductiveConstructor"
      >s&#8804;s</a
      ><a name="6115"
      > </a
      ><a name="6116" href="Relations.html#6116" class="Bound"
      >n&#8804;p</a
      ><a name="6119" class="Symbol"
      >)</a
      ><a name="6120"
      > </a
      ><a name="6121" class="Symbol"
      >=</a
      ><a name="6122"
      > </a
      ><a name="6123" href="Relations.html#1169" class="InductiveConstructor"
      >s&#8804;s</a
      ><a name="6126"
      > </a
      ><a name="6127" class="Symbol"
      >(</a
      ><a name="6128" href="Relations.html#6025" class="Function"
      >&#8804;-trans</a
      ><a name="6135"
      > </a
      ><a name="6136" href="Relations.html#6106" class="Bound"
      >m&#8804;n</a
      ><a name="6139"
      > </a
      ><a name="6140" href="Relations.html#6116" class="Bound"
      >n&#8804;p</a
      ><a name="6143" class="Symbol"
      >)</a
      >
{% endraw %}</pre>
Here the proof is most easily thought of as by induction on the
*evidence* that `m ≤ n`, so we have left `m`, `n`, and `p` implicit.

In the base case, `m ≤ n` holds by `z≤n`, so it must be that
`m` is `zero`, in which case `m ≤ p` also holds by `z≤n`. In this
case, the fact that `n ≤ p` is irrelevant, and we write `_` as the
pattern to indicate that the corresponding evidence is unused. We
could instead have written `n≤p` but not used that variable on the
right-hand side of the equation.

In the inductive case, `m ≤ n` holds by `s≤s m≤n`, so it must be that `m`
is `suc m′` and `n` is `suc n′` for some `m′` and `n′`, and `m≤n` is
evidence that `m′ ≤ n′`.  In this case, the only way that `p ≤ n` can
hold is by `s≤s n≤p`, where `p` is `suc p′` for some `p′` and `n≤p` is
evidence that `n′ ≤ p′`.  The inductive hypothesis `≤-trans m≤n n≤p`
provides evidence that `m′ ≤ p′`, and applying `s≤s` to that gives
evidence of the desired conclusion, `suc m′ ≤ suc p′`.

The case `≤-trans (s≤s m≤n) z≤n` cannot arise, since the first piece of
evidence implies `n` must be `suc n′` for some `n′` while the second
implies `n` must be `zero`.  Agda can determine that such a case cannot
arise, and does not require it to be listed.

Alternatively, we could make the implicit parameters explicit.
<pre class="Agda">{% raw %}
<a name="7462" href="Relations.html#7462" class="Function"
      >&#8804;-trans&#8242;</a
      ><a name="7470"
      > </a
      ><a name="7471" class="Symbol"
      >:</a
      ><a name="7472"
      > </a
      ><a name="7473" class="Symbol"
      >&#8704;</a
      ><a name="7474"
      > </a
      ><a name="7475" class="Symbol"
      >(</a
      ><a name="7476" href="Relations.html#7476" class="Bound"
      >m</a
      ><a name="7477"
      > </a
      ><a name="7478" href="Relations.html#7478" class="Bound"
      >n</a
      ><a name="7479"
      > </a
      ><a name="7480" href="Relations.html#7480" class="Bound"
      >p</a
      ><a name="7481"
      > </a
      ><a name="7482" class="Symbol"
      >:</a
      ><a name="7483"
      > </a
      ><a name="7484" href="Naturals.html#1064" class="Datatype"
      >&#8469;</a
      ><a name="7485" class="Symbol"
      >)</a
      ><a name="7486"
      > </a
      ><a name="7487" class="Symbol"
      >&#8594;</a
      ><a name="7488"
      > </a
      ><a name="7489" href="Relations.html#7476" class="Bound"
      >m</a
      ><a name="7490"
      > </a
      ><a name="7491" href="Relations.html#1114" class="Datatype Operator"
      >&#8804;</a
      ><a name="7492"
      > </a
      ><a name="7493" href="Relations.html#7478" class="Bound"
      >n</a
      ><a name="7494"
      > </a
      ><a name="7495" class="Symbol"
      >&#8594;</a
      ><a name="7496"
      > </a
      ><a name="7497" href="Relations.html#7478" class="Bound"
      >n</a
      ><a name="7498"
      > </a
      ><a name="7499" href="Relations.html#1114" class="Datatype Operator"
      >&#8804;</a
      ><a name="7500"
      > </a
      ><a name="7501" href="Relations.html#7480" class="Bound"
      >p</a
      ><a name="7502"
      > </a
      ><a name="7503" class="Symbol"
      >&#8594;</a
      ><a name="7504"
      > </a
      ><a name="7505" href="Relations.html#7476" class="Bound"
      >m</a
      ><a name="7506"
      > </a
      ><a name="7507" href="Relations.html#1114" class="Datatype Operator"
      >&#8804;</a
      ><a name="7508"
      > </a
      ><a name="7509" href="Relations.html#7480" class="Bound"
      >p</a
      ><a name="7510"
      >
</a
      ><a name="7511" href="Relations.html#7462" class="Function"
      >&#8804;-trans&#8242;</a
      ><a name="7519"
      > </a
      ><a name="7520" href="Naturals.html#1080" class="InductiveConstructor"
      >zero</a
      ><a name="7524"
      > </a
      ><a name="7525" href="Relations.html#7525" class="Bound"
      >n</a
      ><a name="7526"
      > </a
      ><a name="7527" href="Relations.html#7527" class="Bound"
      >p</a
      ><a name="7528"
      > </a
      ><a name="7529" href="Relations.html#1140" class="InductiveConstructor"
      >z&#8804;n</a
      ><a name="7532"
      > </a
      ><a name="7533" class="Symbol"
      >_</a
      ><a name="7534"
      > </a
      ><a name="7535" class="Symbol"
      >=</a
      ><a name="7536"
      > </a
      ><a name="7537" href="Relations.html#1140" class="InductiveConstructor"
      >z&#8804;n</a
      ><a name="7540"
      >
</a
      ><a name="7541" href="Relations.html#7462" class="Function"
      >&#8804;-trans&#8242;</a
      ><a name="7549"
      > </a
      ><a name="7550" class="Symbol"
      >(</a
      ><a name="7551" href="Naturals.html#1091" class="InductiveConstructor"
      >suc</a
      ><a name="7554"
      > </a
      ><a name="7555" href="Relations.html#7555" class="Bound"
      >m</a
      ><a name="7556" class="Symbol"
      >)</a
      ><a name="7557"
      > </a
      ><a name="7558" class="Symbol"
      >(</a
      ><a name="7559" href="Naturals.html#1091" class="InductiveConstructor"
      >suc</a
      ><a name="7562"
      > </a
      ><a name="7563" href="Relations.html#7563" class="Bound"
      >n</a
      ><a name="7564" class="Symbol"
      >)</a
      ><a name="7565"
      > </a
      ><a name="7566" class="Symbol"
      >(</a
      ><a name="7567" href="Naturals.html#1091" class="InductiveConstructor"
      >suc</a
      ><a name="7570"
      > </a
      ><a name="7571" href="Relations.html#7571" class="Bound"
      >p</a
      ><a name="7572" class="Symbol"
      >)</a
      ><a name="7573"
      > </a
      ><a name="7574" class="Symbol"
      >(</a
      ><a name="7575" href="Relations.html#1169" class="InductiveConstructor"
      >s&#8804;s</a
      ><a name="7578"
      > </a
      ><a name="7579" href="Relations.html#7579" class="Bound"
      >m&#8804;n</a
      ><a name="7582" class="Symbol"
      >)</a
      ><a name="7583"
      > </a
      ><a name="7584" class="Symbol"
      >(</a
      ><a name="7585" href="Relations.html#1169" class="InductiveConstructor"
      >s&#8804;s</a
      ><a name="7588"
      > </a
      ><a name="7589" href="Relations.html#7589" class="Bound"
      >n&#8804;p</a
      ><a name="7592" class="Symbol"
      >)</a
      ><a name="7593"
      > </a
      ><a name="7594" class="Symbol"
      >=</a
      ><a name="7595"
      > </a
      ><a name="7596" href="Relations.html#1169" class="InductiveConstructor"
      >s&#8804;s</a
      ><a name="7599"
      > </a
      ><a name="7600" class="Symbol"
      >(</a
      ><a name="7601" href="Relations.html#7462" class="Function"
      >&#8804;-trans&#8242;</a
      ><a name="7609"
      > </a
      ><a name="7610" href="Relations.html#7555" class="Bound"
      >m</a
      ><a name="7611"
      > </a
      ><a name="7612" href="Relations.html#7563" class="Bound"
      >n</a
      ><a name="7613"
      > </a
      ><a name="7614" href="Relations.html#7571" class="Bound"
      >p</a
      ><a name="7615"
      > </a
      ><a name="7616" href="Relations.html#7579" class="Bound"
      >m&#8804;n</a
      ><a name="7619"
      > </a
      ><a name="7620" href="Relations.html#7589" class="Bound"
      >n&#8804;p</a
      ><a name="7623" class="Symbol"
      >)</a
      >
{% endraw %}</pre>
One might argue that this is clearer, since it shows us the forms of `m`, `n`,
and `p`, or one might argue that the extra length obscures the essence of the
proof.  We will usually opt for shorter proofs.

The technique of inducting on evidence that a property holds (e.g.,
inducting on evidence that `m ≤ n`)---rather than induction on the
value of which the property holds (e.g., inducting on `m`)---will turn
out to be immensely valuable, and one that we use often.

Again, it is a good exercise to prove transitivity interactively in Emacs,
using holes and the `^C ^C`, `^C ^,`, and `^C ^R` commands.

## Anti-symmetry

The third property to prove about comparison is that it is antisymmetric:
for all naturals `m` and `n`, if both `m ≤ n` and `n ≤ m` hold, then
`m ≡ n` holds.
<pre class="Agda">{% raw %}
<a name="8431" href="Relations.html#8431" class="Function"
      >&#8804;-antisym</a
      ><a name="8440"
      > </a
      ><a name="8441" class="Symbol"
      >:</a
      ><a name="8442"
      > </a
      ><a name="8443" class="Symbol"
      >&#8704;</a
      ><a name="8444"
      > </a
      ><a name="8445" class="Symbol"
      >{</a
      ><a name="8446" href="Relations.html#8446" class="Bound"
      >m</a
      ><a name="8447"
      > </a
      ><a name="8448" href="Relations.html#8448" class="Bound"
      >n</a
      ><a name="8449"
      > </a
      ><a name="8450" class="Symbol"
      >:</a
      ><a name="8451"
      > </a
      ><a name="8452" href="Naturals.html#1064" class="Datatype"
      >&#8469;</a
      ><a name="8453" class="Symbol"
      >}</a
      ><a name="8454"
      > </a
      ><a name="8455" class="Symbol"
      >&#8594;</a
      ><a name="8456"
      > </a
      ><a name="8457" href="Relations.html#8446" class="Bound"
      >m</a
      ><a name="8458"
      > </a
      ><a name="8459" href="Relations.html#1114" class="Datatype Operator"
      >&#8804;</a
      ><a name="8460"
      > </a
      ><a name="8461" href="Relations.html#8448" class="Bound"
      >n</a
      ><a name="8462"
      > </a
      ><a name="8463" class="Symbol"
      >&#8594;</a
      ><a name="8464"
      > </a
      ><a name="8465" href="Relations.html#8448" class="Bound"
      >n</a
      ><a name="8466"
      > </a
      ><a name="8467" href="Relations.html#1114" class="Datatype Operator"
      >&#8804;</a
      ><a name="8468"
      > </a
      ><a name="8469" href="Relations.html#8446" class="Bound"
      >m</a
      ><a name="8470"
      > </a
      ><a name="8471" class="Symbol"
      >&#8594;</a
      ><a name="8472"
      > </a
      ><a name="8473" href="Relations.html#8446" class="Bound"
      >m</a
      ><a name="8474"
      > </a
      ><a name="8475" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="8476"
      > </a
      ><a name="8477" href="Relations.html#8448" class="Bound"
      >n</a
      ><a name="8478"
      >
</a
      ><a name="8479" href="Relations.html#8431" class="Function"
      >&#8804;-antisym</a
      ><a name="8488"
      > </a
      ><a name="8489" href="Relations.html#1140" class="InductiveConstructor"
      >z&#8804;n</a
      ><a name="8492"
      > </a
      ><a name="8493" href="Relations.html#1140" class="InductiveConstructor"
      >z&#8804;n</a
      ><a name="8496"
      > </a
      ><a name="8497" class="Symbol"
      >=</a
      ><a name="8498"
      > </a
      ><a name="8499" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      ><a name="8503"
      >
</a
      ><a name="8504" href="Relations.html#8431" class="Function"
      >&#8804;-antisym</a
      ><a name="8513"
      > </a
      ><a name="8514" class="Symbol"
      >(</a
      ><a name="8515" href="Relations.html#1169" class="InductiveConstructor"
      >s&#8804;s</a
      ><a name="8518"
      > </a
      ><a name="8519" href="Relations.html#8519" class="Bound"
      >m&#8804;n</a
      ><a name="8522" class="Symbol"
      >)</a
      ><a name="8523"
      > </a
      ><a name="8524" class="Symbol"
      >(</a
      ><a name="8525" href="Relations.html#1169" class="InductiveConstructor"
      >s&#8804;s</a
      ><a name="8528"
      > </a
      ><a name="8529" href="Relations.html#8529" class="Bound"
      >n&#8804;m</a
      ><a name="8532" class="Symbol"
      >)</a
      ><a name="8533"
      > </a
      ><a name="8534" class="Keyword"
      >rewrite</a
      ><a name="8541"
      > </a
      ><a name="8542" href="Relations.html#8431" class="Function"
      >&#8804;-antisym</a
      ><a name="8551"
      > </a
      ><a name="8552" href="Relations.html#8519" class="Bound"
      >m&#8804;n</a
      ><a name="8555"
      > </a
      ><a name="8556" href="Relations.html#8529" class="Bound"
      >n&#8804;m</a
      ><a name="8559"
      > </a
      ><a name="8560" class="Symbol"
      >=</a
      ><a name="8561"
      > </a
      ><a name="8562" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor"
      >refl</a
      >
{% endraw %}</pre>
Again, the proof is by induction over the evidence that `m ≤ n`
and `n ≤ m` hold, and so we have left `m` and `n` implicit.

In the base case, both relations hold by `z≤n`,
so it must be the case that `m` and `n` are both `zero`,
in which case `m ≡ n` holds by reflexivity. (The reflexivity
of equivalance, that is, not the reflexivity of comparison.)

In the inductive case, `m ≤ n` holds by `s≤s m≤n` and `n ≤ m` holds by
`s≤s n≤m`, so it must be that `m` is `suc m′` and `n` is `suc n′`, for
some `m′` and `n′`, where `m≤n` is evidence that `m′ ≤ n′` and `n≤m`
is evidence that `n′ ≤ m′`.  The inductive hypothesis `≤-antisym m≤n n≤m`
establishes that `m′ ≡ n′`, and rewriting by this equation establishes
that `m ≡ n` holds by reflexivity.

## Disjunction

In order to state totality, we need a way to formalise disjunction,
the notion that given two propositions either one or the other holds.
In Agda, we do so by declaring a suitable inductive type.
<pre class="Agda">{% raw %}
<a name="9548" class="Keyword"
      >data</a
      ><a name="9552"
      > </a
      ><a name="9553" href="Relations.html#9553" class="Datatype Operator"
      >_&#8846;_</a
      ><a name="9556"
      > </a
      ><a name="9557" class="Symbol"
      >:</a
      ><a name="9558"
      > </a
      ><a name="9559" class="PrimitiveType"
      >Set</a
      ><a name="9562"
      > </a
      ><a name="9563" class="Symbol"
      >&#8594;</a
      ><a name="9564"
      > </a
      ><a name="9565" class="PrimitiveType"
      >Set</a
      ><a name="9568"
      > </a
      ><a name="9569" class="Symbol"
      >&#8594;</a
      ><a name="9570"
      > </a
      ><a name="9571" class="PrimitiveType"
      >Set</a
      ><a name="9574"
      > </a
      ><a name="9575" class="Keyword"
      >where</a
      ><a name="9580"
      >
  </a
      ><a name="9583" href="Relations.html#9583" class="InductiveConstructor"
      >inj&#8321;</a
      ><a name="9587"
      >  </a
      ><a name="9589" class="Symbol"
      >:</a
      ><a name="9590"
      > </a
      ><a name="9591" class="Symbol"
      >&#8704;</a
      ><a name="9592"
      > </a
      ><a name="9593" class="Symbol"
      >{</a
      ><a name="9594" href="Relations.html#9594" class="Bound"
      >A</a
      ><a name="9595"
      > </a
      ><a name="9596" href="Relations.html#9596" class="Bound"
      >B</a
      ><a name="9597"
      > </a
      ><a name="9598" class="Symbol"
      >:</a
      ><a name="9599"
      > </a
      ><a name="9600" class="PrimitiveType"
      >Set</a
      ><a name="9603" class="Symbol"
      >}</a
      ><a name="9604"
      > </a
      ><a name="9605" class="Symbol"
      >&#8594;</a
      ><a name="9606"
      > </a
      ><a name="9607" href="Relations.html#9594" class="Bound"
      >A</a
      ><a name="9608"
      > </a
      ><a name="9609" class="Symbol"
      >&#8594;</a
      ><a name="9610"
      > </a
      ><a name="9611" href="Relations.html#9594" class="Bound"
      >A</a
      ><a name="9612"
      > </a
      ><a name="9613" href="Relations.html#9553" class="Datatype Operator"
      >&#8846;</a
      ><a name="9614"
      > </a
      ><a name="9615" href="Relations.html#9596" class="Bound"
      >B</a
      ><a name="9616"
      >
  </a
      ><a name="9619" href="Relations.html#9619" class="InductiveConstructor"
      >inj&#8322;</a
      ><a name="9623"
      > </a
      ><a name="9624" class="Symbol"
      >:</a
      ><a name="9625"
      > </a
      ><a name="9626" class="Symbol"
      >&#8704;</a
      ><a name="9627"
      > </a
      ><a name="9628" class="Symbol"
      >{</a
      ><a name="9629" href="Relations.html#9629" class="Bound"
      >A</a
      ><a name="9630"
      > </a
      ><a name="9631" href="Relations.html#9631" class="Bound"
      >B</a
      ><a name="9632"
      > </a
      ><a name="9633" class="Symbol"
      >:</a
      ><a name="9634"
      > </a
      ><a name="9635" class="PrimitiveType"
      >Set</a
      ><a name="9638" class="Symbol"
      >}</a
      ><a name="9639"
      > </a
      ><a name="9640" class="Symbol"
      >&#8594;</a
      ><a name="9641"
      > </a
      ><a name="9642" href="Relations.html#9631" class="Bound"
      >B</a
      ><a name="9643"
      > </a
      ><a name="9644" class="Symbol"
      >&#8594;</a
      ><a name="9645"
      > </a
      ><a name="9646" href="Relations.html#9629" class="Bound"
      >A</a
      ><a name="9647"
      > </a
      ><a name="9648" href="Relations.html#9553" class="Datatype Operator"
      >&#8846;</a
      ><a name="9649"
      > </a
      ><a name="9650" href="Relations.html#9631" class="Bound"
      >B</a
      >
{% endraw %}</pre>
This tells us that if `A` and `B` are propositions then `A ⊎ B` is
also a proposition.  Evidence that `A ⊎ B` holds is either of the form
`inj₁ a`, where `a` is evidence that `A` holds, or `inj₂ b`, where
`b` is evidence that `B` holds.

We set the precedence of disjunction so that it binds less tightly
than comparison.
<pre class="Agda">{% raw %}
<a name="9998" class="Keyword"
      >infix</a
      ><a name="10003"
      > </a
      ><a name="10004" class="Number"
      >1</a
      ><a name="10005"
      > </a
      ><a name="10006" href="Relations.html#9553" class="Datatype Operator"
      >_&#8846;_</a
      >
{% endraw %}</pre>
Thus, `m ≤ n ⊎ n ≤ m` parses as `(m ≤ n) ⊎ (n ≤ m)`.

## Total

The fourth property to prove about comparison is that it is total:
for any naturals `m` and `n` either `m ≤ n` or `n ≤ m`, or both if
`m` and `n` are equal.
<pre class="Agda">{% raw %}
<a name="10255" href="Relations.html#10255" class="Function"
      >&#8804;-total</a
      ><a name="10262"
      > </a
      ><a name="10263" class="Symbol"
      >:</a
      ><a name="10264"
      > </a
      ><a name="10265" class="Symbol"
      >&#8704;</a
      ><a name="10266"
      > </a
      ><a name="10267" class="Symbol"
      >(</a
      ><a name="10268" href="Relations.html#10268" class="Bound"
      >m</a
      ><a name="10269"
      > </a
      ><a name="10270" href="Relations.html#10270" class="Bound"
      >n</a
      ><a name="10271"
      > </a
      ><a name="10272" class="Symbol"
      >:</a
      ><a name="10273"
      > </a
      ><a name="10274" href="Naturals.html#1064" class="Datatype"
      >&#8469;</a
      ><a name="10275" class="Symbol"
      >)</a
      ><a name="10276"
      > </a
      ><a name="10277" class="Symbol"
      >&#8594;</a
      ><a name="10278"
      > </a
      ><a name="10279" href="Relations.html#10268" class="Bound"
      >m</a
      ><a name="10280"
      > </a
      ><a name="10281" href="Relations.html#1114" class="Datatype Operator"
      >&#8804;</a
      ><a name="10282"
      > </a
      ><a name="10283" href="Relations.html#10270" class="Bound"
      >n</a
      ><a name="10284"
      > </a
      ><a name="10285" href="Relations.html#9553" class="Datatype Operator"
      >&#8846;</a
      ><a name="10286"
      > </a
      ><a name="10287" href="Relations.html#10270" class="Bound"
      >n</a
      ><a name="10288"
      > </a
      ><a name="10289" href="Relations.html#1114" class="Datatype Operator"
      >&#8804;</a
      ><a name="10290"
      > </a
      ><a name="10291" href="Relations.html#10268" class="Bound"
      >m</a
      ><a name="10292"
      >
</a
      ><a name="10293" href="Relations.html#10255" class="Function"
      >&#8804;-total</a
      ><a name="10300"
      > </a
      ><a name="10301" href="Naturals.html#1080" class="InductiveConstructor"
      >zero</a
      ><a name="10305"
      > </a
      ><a name="10306" href="Relations.html#10306" class="Bound"
      >n</a
      ><a name="10307"
      > </a
      ><a name="10308" class="Symbol"
      >=</a
      ><a name="10309"
      >  </a
      ><a name="10311" href="Relations.html#9583" class="InductiveConstructor"
      >inj&#8321;</a
      ><a name="10315"
      > </a
      ><a name="10316" href="Relations.html#1140" class="InductiveConstructor"
      >z&#8804;n</a
      ><a name="10319"
      >
</a
      ><a name="10320" href="Relations.html#10255" class="Function"
      >&#8804;-total</a
      ><a name="10327"
      > </a
      ><a name="10328" class="Symbol"
      >(</a
      ><a name="10329" href="Naturals.html#1091" class="InductiveConstructor"
      >suc</a
      ><a name="10332"
      > </a
      ><a name="10333" href="Relations.html#10333" class="Bound"
      >m</a
      ><a name="10334" class="Symbol"
      >)</a
      ><a name="10335"
      > </a
      ><a name="10336" href="Naturals.html#1080" class="InductiveConstructor"
      >zero</a
      ><a name="10340"
      > </a
      ><a name="10341" class="Symbol"
      >=</a
      ><a name="10342"
      >  </a
      ><a name="10344" href="Relations.html#9619" class="InductiveConstructor"
      >inj&#8322;</a
      ><a name="10348"
      > </a
      ><a name="10349" href="Relations.html#1140" class="InductiveConstructor"
      >z&#8804;n</a
      ><a name="10352"
      >
</a
      ><a name="10353" href="Relations.html#10255" class="Function"
      >&#8804;-total</a
      ><a name="10360"
      > </a
      ><a name="10361" class="Symbol"
      >(</a
      ><a name="10362" href="Naturals.html#1091" class="InductiveConstructor"
      >suc</a
      ><a name="10365"
      > </a
      ><a name="10366" href="Relations.html#10366" class="Bound"
      >m</a
      ><a name="10367" class="Symbol"
      >)</a
      ><a name="10368"
      > </a
      ><a name="10369" class="Symbol"
      >(</a
      ><a name="10370" href="Naturals.html#1091" class="InductiveConstructor"
      >suc</a
      ><a name="10373"
      > </a
      ><a name="10374" href="Relations.html#10374" class="Bound"
      >n</a
      ><a name="10375" class="Symbol"
      >)</a
      ><a name="10376"
      > </a
      ><a name="10377" class="Keyword"
      >with</a
      ><a name="10381"
      > </a
      ><a name="10382" href="Relations.html#10255" class="Function"
      >&#8804;-total</a
      ><a name="10389"
      > </a
      ><a name="10390" href="Relations.html#10366" class="Bound"
      >m</a
      ><a name="10391"
      > </a
      ><a name="10392" href="Relations.html#10374" class="Bound"
      >n</a
      ><a name="10393"
      >
</a
      ><a name="10394" class="Symbol"
      >...</a
      ><a name="10397"
      > </a
      ><a name="10398" class="Symbol"
      >|</a
      ><a name="10399"
      > </a
      ><a name="10400" href="Relations.html#9583" class="InductiveConstructor"
      >inj&#8321;</a
      ><a name="10404"
      > </a
      ><a name="10405" href="Relations.html#10405" class="Bound"
      >m&#8804;n</a
      ><a name="10408"
      > </a
      ><a name="10409" class="Symbol"
      >=</a
      ><a name="10410"
      > </a
      ><a name="10411" href="Relations.html#9583" class="InductiveConstructor"
      >inj&#8321;</a
      ><a name="10415"
      > </a
      ><a name="10416" class="Symbol"
      >(</a
      ><a name="10417" href="Relations.html#1169" class="InductiveConstructor"
      >s&#8804;s</a
      ><a name="10420"
      > </a
      ><a name="10421" href="Relations.html#10405" class="Bound"
      >m&#8804;n</a
      ><a name="10424" class="Symbol"
      >)</a
      ><a name="10425"
      >
</a
      ><a name="10426" class="Symbol"
      >...</a
      ><a name="10429"
      > </a
      ><a name="10430" class="Symbol"
      >|</a
      ><a name="10431"
      > </a
      ><a name="10432" href="Relations.html#9619" class="InductiveConstructor"
      >inj&#8322;</a
      ><a name="10436"
      > </a
      ><a name="10437" href="Relations.html#10437" class="Bound"
      >n&#8804;m</a
      ><a name="10440"
      > </a
      ><a name="10441" class="Symbol"
      >=</a
      ><a name="10442"
      > </a
      ><a name="10443" href="Relations.html#9619" class="InductiveConstructor"
      >inj&#8322;</a
      ><a name="10447"
      > </a
      ><a name="10448" class="Symbol"
      >(</a
      ><a name="10449" href="Relations.html#1169" class="InductiveConstructor"
      >s&#8804;s</a
      ><a name="10452"
      > </a
      ><a name="10453" href="Relations.html#10437" class="Bound"
      >n&#8804;m</a
      ><a name="10456" class="Symbol"
      >)</a
      >
{% endraw %}</pre>
In this case the proof is by induction over both the first
and second arguments.  We perform a case analysis:

+ *First base case*: If the first argument is `zero` and the
  second argument is `n` then
  the first disjunct holds, with `z≤n` as evidence that `zero ≤ n`.

+ *Second base case*: If the first argument is `suc m` and the
  second argument is `n` then the right disjunct holds, with
  `z≤n` as evidence that `n ≤ m`.

+ *Inductive case*: If the first argument is `suc m` and the
  second argument is `suc n`, then the inductive hypothesis
  `≤-total m n` establishes one of the following:

  - The first disjunct of the inductive hypothesis holds with `m≤n` as
    evidence that `m ≤ n`, in which case the first disjunct of the
    proposition holds with `s≤s m≤n` as evidence that `suc m ≤ suc n`.

  - The second disjunct of the inductive hypothesis holds with `n≤m` as
    evidence that `n ≤ m`, in which case the second disjunct of the
    proposition holds with `s≤s n≤m` as evidence that `suc n ≤ suc m`.

This is our first use of the `with` clause in Agda.  The keyword
`with` is followed by an expression, and one or more subsequent lines.
Each line begins with an ellipsis (`...`) and a vertical bar (`|`),
followed by a pattern to be matched against the expression, an equal
sign, and the right-hand side of the equation.

Every use of `with` is equivalent to defining a helper function.  For
example, the definition above is equivalent to the following.
<pre class="Agda">{% raw %}
<a name="11959" href="Relations.html#11959" class="Function"
      >&#8804;-total&#8242;</a
      ><a name="11967"
      > </a
      ><a name="11968" class="Symbol"
      >:</a
      ><a name="11969"
      > </a
      ><a name="11970" class="Symbol"
      >&#8704;</a
      ><a name="11971"
      > </a
      ><a name="11972" class="Symbol"
      >(</a
      ><a name="11973" href="Relations.html#11973" class="Bound"
      >m</a
      ><a name="11974"
      > </a
      ><a name="11975" href="Relations.html#11975" class="Bound"
      >n</a
      ><a name="11976"
      > </a
      ><a name="11977" class="Symbol"
      >:</a
      ><a name="11978"
      > </a
      ><a name="11979" href="Naturals.html#1064" class="Datatype"
      >&#8469;</a
      ><a name="11980" class="Symbol"
      >)</a
      ><a name="11981"
      > </a
      ><a name="11982" class="Symbol"
      >&#8594;</a
      ><a name="11983"
      > </a
      ><a name="11984" href="Relations.html#11973" class="Bound"
      >m</a
      ><a name="11985"
      > </a
      ><a name="11986" href="Relations.html#1114" class="Datatype Operator"
      >&#8804;</a
      ><a name="11987"
      > </a
      ><a name="11988" href="Relations.html#11975" class="Bound"
      >n</a
      ><a name="11989"
      > </a
      ><a name="11990" href="Relations.html#9553" class="Datatype Operator"
      >&#8846;</a
      ><a name="11991"
      > </a
      ><a name="11992" href="Relations.html#11975" class="Bound"
      >n</a
      ><a name="11993"
      > </a
      ><a name="11994" href="Relations.html#1114" class="Datatype Operator"
      >&#8804;</a
      ><a name="11995"
      > </a
      ><a name="11996" href="Relations.html#11973" class="Bound"
      >m</a
      ><a name="11997"
      >
</a
      ><a name="11998" href="Relations.html#11959" class="Function"
      >&#8804;-total&#8242;</a
      ><a name="12006"
      > </a
      ><a name="12007" href="Naturals.html#1080" class="InductiveConstructor"
      >zero</a
      ><a name="12011"
      > </a
      ><a name="12012" href="Relations.html#12012" class="Bound"
      >n</a
      ><a name="12013"
      > </a
      ><a name="12014" class="Symbol"
      >=</a
      ><a name="12015"
      > </a
      ><a name="12016" href="Relations.html#9583" class="InductiveConstructor"
      >inj&#8321;</a
      ><a name="12020"
      > </a
      ><a name="12021" href="Relations.html#1140" class="InductiveConstructor"
      >z&#8804;n</a
      ><a name="12024"
      >
</a
      ><a name="12025" href="Relations.html#11959" class="Function"
      >&#8804;-total&#8242;</a
      ><a name="12033"
      > </a
      ><a name="12034" class="Symbol"
      >(</a
      ><a name="12035" href="Naturals.html#1091" class="InductiveConstructor"
      >suc</a
      ><a name="12038"
      > </a
      ><a name="12039" href="Relations.html#12039" class="Bound"
      >m</a
      ><a name="12040" class="Symbol"
      >)</a
      ><a name="12041"
      > </a
      ><a name="12042" href="Naturals.html#1080" class="InductiveConstructor"
      >zero</a
      ><a name="12046"
      > </a
      ><a name="12047" class="Symbol"
      >=</a
      ><a name="12048"
      > </a
      ><a name="12049" href="Relations.html#9619" class="InductiveConstructor"
      >inj&#8322;</a
      ><a name="12053"
      > </a
      ><a name="12054" href="Relations.html#1140" class="InductiveConstructor"
      >z&#8804;n</a
      ><a name="12057"
      >
</a
      ><a name="12058" href="Relations.html#11959" class="Function"
      >&#8804;-total&#8242;</a
      ><a name="12066"
      > </a
      ><a name="12067" class="Symbol"
      >(</a
      ><a name="12068" href="Naturals.html#1091" class="InductiveConstructor"
      >suc</a
      ><a name="12071"
      > </a
      ><a name="12072" href="Relations.html#12072" class="Bound"
      >m</a
      ><a name="12073" class="Symbol"
      >)</a
      ><a name="12074"
      > </a
      ><a name="12075" class="Symbol"
      >(</a
      ><a name="12076" href="Naturals.html#1091" class="InductiveConstructor"
      >suc</a
      ><a name="12079"
      > </a
      ><a name="12080" href="Relations.html#12080" class="Bound"
      >n</a
      ><a name="12081" class="Symbol"
      >)</a
      ><a name="12082"
      > </a
      ><a name="12083" class="Symbol"
      >=</a
      ><a name="12084"
      > </a
      ><a name="12085" href="Relations.html#12117" class="Function"
      >helper</a
      ><a name="12091"
      > </a
      ><a name="12092" class="Symbol"
      >(</a
      ><a name="12093" href="Relations.html#11959" class="Function"
      >&#8804;-total&#8242;</a
      ><a name="12101"
      > </a
      ><a name="12102" href="Relations.html#12072" class="Bound"
      >m</a
      ><a name="12103"
      > </a
      ><a name="12104" href="Relations.html#12080" class="Bound"
      >n</a
      ><a name="12105" class="Symbol"
      >)</a
      ><a name="12106"
      >
  </a
      ><a name="12109" class="Keyword"
      >where</a
      ><a name="12114"
      >
  </a
      ><a name="12117" href="Relations.html#12117" class="Function"
      >helper</a
      ><a name="12123"
      > </a
      ><a name="12124" class="Symbol"
      >:</a
      ><a name="12125"
      > </a
      ><a name="12126" href="Relations.html#12072" class="Bound"
      >m</a
      ><a name="12127"
      > </a
      ><a name="12128" href="Relations.html#1114" class="Datatype Operator"
      >&#8804;</a
      ><a name="12129"
      > </a
      ><a name="12130" href="Relations.html#12080" class="Bound"
      >n</a
      ><a name="12131"
      > </a
      ><a name="12132" href="Relations.html#9553" class="Datatype Operator"
      >&#8846;</a
      ><a name="12133"
      > </a
      ><a name="12134" href="Relations.html#12080" class="Bound"
      >n</a
      ><a name="12135"
      > </a
      ><a name="12136" href="Relations.html#1114" class="Datatype Operator"
      >&#8804;</a
      ><a name="12137"
      > </a
      ><a name="12138" href="Relations.html#12072" class="Bound"
      >m</a
      ><a name="12139"
      > </a
      ><a name="12140" class="Symbol"
      >&#8594;</a
      ><a name="12141"
      > </a
      ><a name="12142" href="Naturals.html#1091" class="InductiveConstructor"
      >suc</a
      ><a name="12145"
      > </a
      ><a name="12146" href="Relations.html#12072" class="Bound"
      >m</a
      ><a name="12147"
      > </a
      ><a name="12148" href="Relations.html#1114" class="Datatype Operator"
      >&#8804;</a
      ><a name="12149"
      > </a
      ><a name="12150" href="Naturals.html#1091" class="InductiveConstructor"
      >suc</a
      ><a name="12153"
      > </a
      ><a name="12154" href="Relations.html#12080" class="Bound"
      >n</a
      ><a name="12155"
      > </a
      ><a name="12156" href="Relations.html#9553" class="Datatype Operator"
      >&#8846;</a
      ><a name="12157"
      > </a
      ><a name="12158" href="Naturals.html#1091" class="InductiveConstructor"
      >suc</a
      ><a name="12161"
      > </a
      ><a name="12162" href="Relations.html#12080" class="Bound"
      >n</a
      ><a name="12163"
      > </a
      ><a name="12164" href="Relations.html#1114" class="Datatype Operator"
      >&#8804;</a
      ><a name="12165"
      > </a
      ><a name="12166" href="Naturals.html#1091" class="InductiveConstructor"
      >suc</a
      ><a name="12169"
      > </a
      ><a name="12170" href="Relations.html#12072" class="Bound"
      >m</a
      ><a name="12171"
      >
  </a
      ><a name="12174" href="Relations.html#12117" class="Function"
      >helper</a
      ><a name="12180"
      > </a
      ><a name="12181" class="Symbol"
      >(</a
      ><a name="12182" href="Relations.html#9583" class="InductiveConstructor"
      >inj&#8321;</a
      ><a name="12186"
      > </a
      ><a name="12187" href="Relations.html#12187" class="Bound"
      >m&#8804;n</a
      ><a name="12190" class="Symbol"
      >)</a
      ><a name="12191"
      > </a
      ><a name="12192" class="Symbol"
      >=</a
      ><a name="12193"
      > </a
      ><a name="12194" href="Relations.html#9583" class="InductiveConstructor"
      >inj&#8321;</a
      ><a name="12198"
      > </a
      ><a name="12199" class="Symbol"
      >(</a
      ><a name="12200" href="Relations.html#1169" class="InductiveConstructor"
      >s&#8804;s</a
      ><a name="12203"
      > </a
      ><a name="12204" href="Relations.html#12187" class="Bound"
      >m&#8804;n</a
      ><a name="12207" class="Symbol"
      >)</a
      ><a name="12208"
      >
  </a
      ><a name="12211" href="Relations.html#12117" class="Function"
      >helper</a
      ><a name="12217"
      > </a
      ><a name="12218" class="Symbol"
      >(</a
      ><a name="12219" href="Relations.html#9619" class="InductiveConstructor"
      >inj&#8322;</a
      ><a name="12223"
      > </a
      ><a name="12224" href="Relations.html#12224" class="Bound"
      >n&#8804;m</a
      ><a name="12227" class="Symbol"
      >)</a
      ><a name="12228"
      > </a
      ><a name="12229" class="Symbol"
      >=</a
      ><a name="12230"
      > </a
      ><a name="12231" href="Relations.html#9619" class="InductiveConstructor"
      >inj&#8322;</a
      ><a name="12235"
      > </a
      ><a name="12236" class="Symbol"
      >(</a
      ><a name="12237" href="Relations.html#1169" class="InductiveConstructor"
      >s&#8804;s</a
      ><a name="12240"
      > </a
      ><a name="12241" href="Relations.html#12224" class="Bound"
      >n&#8804;m</a
      ><a name="12244" class="Symbol"
      >)</a
      >
{% endraw %}</pre>
This is also our first use of a `where` clause in Agda.  The keyword
`where` is followed by one or more definitions, which must be
indented.  Any identifiers bound in the nested definition are in scope
in the right-hand side of the preceding equation (in this case,
`helper`), and any variables bound of the left-hand side of the
preceding equation are in scope within the nested definition (in this
case, `m` and `n`).

If both arguments are equal, then both the first and second disjuncts
hold and we could return evidence of either.  In the code above we
always return the first disjunct, but there is a minor variant that
always returns the second disjunct.
<pre class="Agda">{% raw %}
<a name="12932" href="Relations.html#12932" class="Function"
      >&#8804;-total&#8243;</a
      ><a name="12940"
      > </a
      ><a name="12941" class="Symbol"
      >:</a
      ><a name="12942"
      > </a
      ><a name="12943" class="Symbol"
      >&#8704;</a
      ><a name="12944"
      > </a
      ><a name="12945" class="Symbol"
      >(</a
      ><a name="12946" href="Relations.html#12946" class="Bound"
      >m</a
      ><a name="12947"
      > </a
      ><a name="12948" href="Relations.html#12948" class="Bound"
      >n</a
      ><a name="12949"
      > </a
      ><a name="12950" class="Symbol"
      >:</a
      ><a name="12951"
      > </a
      ><a name="12952" href="Naturals.html#1064" class="Datatype"
      >&#8469;</a
      ><a name="12953" class="Symbol"
      >)</a
      ><a name="12954"
      > </a
      ><a name="12955" class="Symbol"
      >&#8594;</a
      ><a name="12956"
      > </a
      ><a name="12957" href="Relations.html#12946" class="Bound"
      >m</a
      ><a name="12958"
      > </a
      ><a name="12959" href="Relations.html#1114" class="Datatype Operator"
      >&#8804;</a
      ><a name="12960"
      > </a
      ><a name="12961" href="Relations.html#12948" class="Bound"
      >n</a
      ><a name="12962"
      > </a
      ><a name="12963" href="Relations.html#9553" class="Datatype Operator"
      >&#8846;</a
      ><a name="12964"
      > </a
      ><a name="12965" href="Relations.html#12948" class="Bound"
      >n</a
      ><a name="12966"
      > </a
      ><a name="12967" href="Relations.html#1114" class="Datatype Operator"
      >&#8804;</a
      ><a name="12968"
      > </a
      ><a name="12969" href="Relations.html#12946" class="Bound"
      >m</a
      ><a name="12970"
      >
</a
      ><a name="12971" href="Relations.html#12932" class="Function"
      >&#8804;-total&#8243;</a
      ><a name="12979"
      > </a
      ><a name="12980" href="Relations.html#12980" class="Bound"
      >m</a
      ><a name="12981"
      > </a
      ><a name="12982" href="Naturals.html#1080" class="InductiveConstructor"
      >zero</a
      ><a name="12986"
      > </a
      ><a name="12987" class="Symbol"
      >=</a
      ><a name="12988"
      >  </a
      ><a name="12990" href="Relations.html#9619" class="InductiveConstructor"
      >inj&#8322;</a
      ><a name="12994"
      > </a
      ><a name="12995" href="Relations.html#1140" class="InductiveConstructor"
      >z&#8804;n</a
      ><a name="12998"
      >
</a
      ><a name="12999" href="Relations.html#12932" class="Function"
      >&#8804;-total&#8243;</a
      ><a name="13007"
      > </a
      ><a name="13008" href="Naturals.html#1080" class="InductiveConstructor"
      >zero</a
      ><a name="13012"
      > </a
      ><a name="13013" class="Symbol"
      >(</a
      ><a name="13014" href="Naturals.html#1091" class="InductiveConstructor"
      >suc</a
      ><a name="13017"
      > </a
      ><a name="13018" href="Relations.html#13018" class="Bound"
      >n</a
      ><a name="13019" class="Symbol"
      >)</a
      ><a name="13020"
      > </a
      ><a name="13021" class="Symbol"
      >=</a
      ><a name="13022"
      >  </a
      ><a name="13024" href="Relations.html#9583" class="InductiveConstructor"
      >inj&#8321;</a
      ><a name="13028"
      > </a
      ><a name="13029" href="Relations.html#1140" class="InductiveConstructor"
      >z&#8804;n</a
      ><a name="13032"
      >
</a
      ><a name="13033" href="Relations.html#12932" class="Function"
      >&#8804;-total&#8243;</a
      ><a name="13041"
      > </a
      ><a name="13042" class="Symbol"
      >(</a
      ><a name="13043" href="Naturals.html#1091" class="InductiveConstructor"
      >suc</a
      ><a name="13046"
      > </a
      ><a name="13047" href="Relations.html#13047" class="Bound"
      >m</a
      ><a name="13048" class="Symbol"
      >)</a
      ><a name="13049"
      > </a
      ><a name="13050" class="Symbol"
      >(</a
      ><a name="13051" href="Naturals.html#1091" class="InductiveConstructor"
      >suc</a
      ><a name="13054"
      > </a
      ><a name="13055" href="Relations.html#13055" class="Bound"
      >n</a
      ><a name="13056" class="Symbol"
      >)</a
      ><a name="13057"
      > </a
      ><a name="13058" class="Keyword"
      >with</a
      ><a name="13062"
      > </a
      ><a name="13063" href="Relations.html#12932" class="Function"
      >&#8804;-total&#8243;</a
      ><a name="13071"
      > </a
      ><a name="13072" href="Relations.html#13047" class="Bound"
      >m</a
      ><a name="13073"
      > </a
      ><a name="13074" href="Relations.html#13055" class="Bound"
      >n</a
      ><a name="13075"
      >
</a
      ><a name="13076" class="Symbol"
      >...</a
      ><a name="13079"
      > </a
      ><a name="13080" class="Symbol"
      >|</a
      ><a name="13081"
      > </a
      ><a name="13082" href="Relations.html#9583" class="InductiveConstructor"
      >inj&#8321;</a
      ><a name="13086"
      > </a
      ><a name="13087" href="Relations.html#13087" class="Bound"
      >m&#8804;n</a
      ><a name="13090"
      > </a
      ><a name="13091" class="Symbol"
      >=</a
      ><a name="13092"
      > </a
      ><a name="13093" href="Relations.html#9583" class="InductiveConstructor"
      >inj&#8321;</a
      ><a name="13097"
      > </a
      ><a name="13098" class="Symbol"
      >(</a
      ><a name="13099" href="Relations.html#1169" class="InductiveConstructor"
      >s&#8804;s</a
      ><a name="13102"
      > </a
      ><a name="13103" href="Relations.html#13087" class="Bound"
      >m&#8804;n</a
      ><a name="13106" class="Symbol"
      >)</a
      ><a name="13107"
      >
</a
      ><a name="13108" class="Symbol"
      >...</a
      ><a name="13111"
      > </a
      ><a name="13112" class="Symbol"
      >|</a
      ><a name="13113"
      > </a
      ><a name="13114" href="Relations.html#9619" class="InductiveConstructor"
      >inj&#8322;</a
      ><a name="13118"
      > </a
      ><a name="13119" href="Relations.html#13119" class="Bound"
      >n&#8804;m</a
      ><a name="13122"
      > </a
      ><a name="13123" class="Symbol"
      >=</a
      ><a name="13124"
      > </a
      ><a name="13125" href="Relations.html#9619" class="InductiveConstructor"
      >inj&#8322;</a
      ><a name="13129"
      > </a
      ><a name="13130" class="Symbol"
      >(</a
      ><a name="13131" href="Relations.html#1169" class="InductiveConstructor"
      >s&#8804;s</a
      ><a name="13134"
      > </a
      ><a name="13135" href="Relations.html#13119" class="Bound"
      >n&#8804;m</a
      ><a name="13138" class="Symbol"
      >)</a
      >
{% endraw %}</pre>


## Monotonicity

If one bumps into both an operator and an order relation at
a party, one may ask if the operator is *monotonic* with regard
to the order relation.  For example, addition is monotonic
with regard to comparison, meaning

  ∀ {m n p q : ℕ} → m ≤ n → p ≤ q → m + p ≤ n + q

Addition (precedence level 6) binds more tightly than comparison
(precedence level 4), so `m + n ≤ p + q` parses as
`(m + n) ≤ (p + q)`.

The proof is straightforward using the techniques we have learned,
and is best broken into three parts. First, we deal with the special
case of showing addition is monotonic on the right.
<pre class="Agda">{% raw %}
<a name="13779" href="Relations.html#13779" class="Function"
      >+-mono&#691;-&#8804;</a
      ><a name="13788"
      > </a
      ><a name="13789" class="Symbol"
      >:</a
      ><a name="13790"
      > </a
      ><a name="13791" class="Symbol"
      >&#8704;</a
      ><a name="13792"
      > </a
      ><a name="13793" class="Symbol"
      >(</a
      ><a name="13794" href="Relations.html#13794" class="Bound"
      >m</a
      ><a name="13795"
      > </a
      ><a name="13796" href="Relations.html#13796" class="Bound"
      >p</a
      ><a name="13797"
      > </a
      ><a name="13798" href="Relations.html#13798" class="Bound"
      >q</a
      ><a name="13799"
      > </a
      ><a name="13800" class="Symbol"
      >:</a
      ><a name="13801"
      > </a
      ><a name="13802" href="Naturals.html#1064" class="Datatype"
      >&#8469;</a
      ><a name="13803" class="Symbol"
      >)</a
      ><a name="13804"
      > </a
      ><a name="13805" class="Symbol"
      >&#8594;</a
      ><a name="13806"
      > </a
      ><a name="13807" href="Relations.html#13796" class="Bound"
      >p</a
      ><a name="13808"
      > </a
      ><a name="13809" href="Relations.html#1114" class="Datatype Operator"
      >&#8804;</a
      ><a name="13810"
      > </a
      ><a name="13811" href="Relations.html#13798" class="Bound"
      >q</a
      ><a name="13812"
      > </a
      ><a name="13813" class="Symbol"
      >&#8594;</a
      ><a name="13814"
      > </a
      ><a name="13815" href="Relations.html#13794" class="Bound"
      >m</a
      ><a name="13816"
      > </a
      ><a name="13817" href="Naturals.html#9439" class="Primitive Operator"
      >+</a
      ><a name="13818"
      > </a
      ><a name="13819" href="Relations.html#13796" class="Bound"
      >p</a
      ><a name="13820"
      > </a
      ><a name="13821" href="Relations.html#1114" class="Datatype Operator"
      >&#8804;</a
      ><a name="13822"
      > </a
      ><a name="13823" href="Relations.html#13794" class="Bound"
      >m</a
      ><a name="13824"
      > </a
      ><a name="13825" href="Naturals.html#9439" class="Primitive Operator"
      >+</a
      ><a name="13826"
      > </a
      ><a name="13827" href="Relations.html#13798" class="Bound"
      >q</a
      ><a name="13828"
      >
</a
      ><a name="13829" href="Relations.html#13779" class="Function"
      >+-mono&#691;-&#8804;</a
      ><a name="13838"
      > </a
      ><a name="13839" href="Naturals.html#1080" class="InductiveConstructor"
      >zero</a
      ><a name="13843"
      > </a
      ><a name="13844" href="Relations.html#13844" class="Bound"
      >p</a
      ><a name="13845"
      > </a
      ><a name="13846" href="Relations.html#13846" class="Bound"
      >q</a
      ><a name="13847"
      > </a
      ><a name="13848" href="Relations.html#13848" class="Bound"
      >p&#8804;q</a
      ><a name="13851"
      > </a
      ><a name="13852" class="Symbol"
      >=</a
      ><a name="13853"
      >  </a
      ><a name="13855" href="Relations.html#13848" class="Bound"
      >p&#8804;q</a
      ><a name="13858"
      >
</a
      ><a name="13859" href="Relations.html#13779" class="Function"
      >+-mono&#691;-&#8804;</a
      ><a name="13868"
      > </a
      ><a name="13869" class="Symbol"
      >(</a
      ><a name="13870" href="Naturals.html#1091" class="InductiveConstructor"
      >suc</a
      ><a name="13873"
      > </a
      ><a name="13874" href="Relations.html#13874" class="Bound"
      >m</a
      ><a name="13875" class="Symbol"
      >)</a
      ><a name="13876"
      > </a
      ><a name="13877" href="Relations.html#13877" class="Bound"
      >p</a
      ><a name="13878"
      > </a
      ><a name="13879" href="Relations.html#13879" class="Bound"
      >q</a
      ><a name="13880"
      > </a
      ><a name="13881" href="Relations.html#13881" class="Bound"
      >p&#8804;q</a
      ><a name="13884"
      > </a
      ><a name="13885" class="Symbol"
      >=</a
      ><a name="13886"
      >  </a
      ><a name="13888" href="Relations.html#1169" class="InductiveConstructor"
      >s&#8804;s</a
      ><a name="13891"
      > </a
      ><a name="13892" class="Symbol"
      >(</a
      ><a name="13893" href="Relations.html#13779" class="Function"
      >+-mono&#691;-&#8804;</a
      ><a name="13902"
      > </a
      ><a name="13903" href="Relations.html#13874" class="Bound"
      >m</a
      ><a name="13904"
      > </a
      ><a name="13905" href="Relations.html#13877" class="Bound"
      >p</a
      ><a name="13906"
      > </a
      ><a name="13907" href="Relations.html#13879" class="Bound"
      >q</a
      ><a name="13908"
      > </a
      ><a name="13909" href="Relations.html#13881" class="Bound"
      >p&#8804;q</a
      ><a name="13912" class="Symbol"
      >)</a
      >
{% endraw %}</pre>
The proof is by induction on the first argument.

+ *Base case*: The first argument is `zero` in which case
  `zero + p ≤ zero + q` simplifies to `p ≤ q`, the evidence
  for which is given by the explicit argument `p≤q`.

+ *Inductive case*: The first argument is `suc m`, in which case
  `suc m + p ≤ suc m + q` simplifies to `suc (m + p) ≤ suc (m + q)`.
  The inductive hypothesis `+-monoʳ-≤ m p q p≤q` establishes that
  `m + p ≤ m + q`, from which the desired conclusion follows
  by an application of `s≤s`.

Second, we deal with the special case of showing addition is
monotonic on the left. This follows from the previous
result and the commutativity of addition.
<pre class="Agda">{% raw %}
<a name="14610" href="Relations.html#14610" class="Function"
      >+-mono&#737;-&#8804;</a
      ><a name="14619"
      > </a
      ><a name="14620" class="Symbol"
      >:</a
      ><a name="14621"
      > </a
      ><a name="14622" class="Symbol"
      >&#8704;</a
      ><a name="14623"
      > </a
      ><a name="14624" class="Symbol"
      >(</a
      ><a name="14625" href="Relations.html#14625" class="Bound"
      >m</a
      ><a name="14626"
      > </a
      ><a name="14627" href="Relations.html#14627" class="Bound"
      >n</a
      ><a name="14628"
      > </a
      ><a name="14629" href="Relations.html#14629" class="Bound"
      >p</a
      ><a name="14630"
      > </a
      ><a name="14631" class="Symbol"
      >:</a
      ><a name="14632"
      > </a
      ><a name="14633" href="Naturals.html#1064" class="Datatype"
      >&#8469;</a
      ><a name="14634" class="Symbol"
      >)</a
      ><a name="14635"
      > </a
      ><a name="14636" class="Symbol"
      >&#8594;</a
      ><a name="14637"
      > </a
      ><a name="14638" href="Relations.html#14625" class="Bound"
      >m</a
      ><a name="14639"
      > </a
      ><a name="14640" href="Relations.html#1114" class="Datatype Operator"
      >&#8804;</a
      ><a name="14641"
      > </a
      ><a name="14642" href="Relations.html#14627" class="Bound"
      >n</a
      ><a name="14643"
      > </a
      ><a name="14644" class="Symbol"
      >&#8594;</a
      ><a name="14645"
      > </a
      ><a name="14646" href="Relations.html#14625" class="Bound"
      >m</a
      ><a name="14647"
      > </a
      ><a name="14648" href="Naturals.html#9439" class="Primitive Operator"
      >+</a
      ><a name="14649"
      > </a
      ><a name="14650" href="Relations.html#14629" class="Bound"
      >p</a
      ><a name="14651"
      > </a
      ><a name="14652" href="Relations.html#1114" class="Datatype Operator"
      >&#8804;</a
      ><a name="14653"
      > </a
      ><a name="14654" href="Relations.html#14627" class="Bound"
      >n</a
      ><a name="14655"
      > </a
      ><a name="14656" href="Naturals.html#9439" class="Primitive Operator"
      >+</a
      ><a name="14657"
      > </a
      ><a name="14658" href="Relations.html#14629" class="Bound"
      >p</a
      ><a name="14659"
      >
</a
      ><a name="14660" href="Relations.html#14610" class="Function"
      >+-mono&#737;-&#8804;</a
      ><a name="14669"
      > </a
      ><a name="14670" href="Relations.html#14670" class="Bound"
      >m</a
      ><a name="14671"
      > </a
      ><a name="14672" href="Relations.html#14672" class="Bound"
      >n</a
      ><a name="14673"
      > </a
      ><a name="14674" href="Relations.html#14674" class="Bound"
      >p</a
      ><a name="14675"
      > </a
      ><a name="14676" href="Relations.html#14676" class="Bound"
      >m&#8804;n</a
      ><a name="14679"
      > </a
      ><a name="14680" class="Keyword"
      >rewrite</a
      ><a name="14687"
      > </a
      ><a name="14688" href="Properties.html#17070" class="Function"
      >+-comm</a
      ><a name="14694"
      > </a
      ><a name="14695" href="Relations.html#14670" class="Bound"
      >m</a
      ><a name="14696"
      > </a
      ><a name="14697" href="Relations.html#14674" class="Bound"
      >p</a
      ><a name="14698"
      > </a
      ><a name="14699" class="Symbol"
      >|</a
      ><a name="14700"
      > </a
      ><a name="14701" href="Properties.html#17070" class="Function"
      >+-comm</a
      ><a name="14707"
      > </a
      ><a name="14708" href="Relations.html#14672" class="Bound"
      >n</a
      ><a name="14709"
      > </a
      ><a name="14710" href="Relations.html#14674" class="Bound"
      >p</a
      ><a name="14711"
      > </a
      ><a name="14712" class="Symbol"
      >=</a
      ><a name="14713"
      > </a
      ><a name="14714" href="Relations.html#13779" class="Function"
      >+-mono&#691;-&#8804;</a
      ><a name="14723"
      > </a
      ><a name="14724" href="Relations.html#14674" class="Bound"
      >p</a
      ><a name="14725"
      > </a
      ><a name="14726" href="Relations.html#14670" class="Bound"
      >m</a
      ><a name="14727"
      > </a
      ><a name="14728" href="Relations.html#14672" class="Bound"
      >n</a
      ><a name="14729"
      > </a
      ><a name="14730" href="Relations.html#14676" class="Bound"
      >m&#8804;n</a
      >
{% endraw %}</pre>
Rewriting by `+-comm m p` and `+-comm n p` converts `m + p ≤ n + p` into
`p + m ≤ p + n`, which is proved by invoking `+-monoʳ-≤ p m n m≤n`.

Third, we combine the two previous results.
<pre class="Agda">{% raw %}
<a name="14944" href="Relations.html#14944" class="Function"
      >mono+&#8804;</a
      ><a name="14950"
      > </a
      ><a name="14951" class="Symbol"
      >:</a
      ><a name="14952"
      > </a
      ><a name="14953" class="Symbol"
      >&#8704;</a
      ><a name="14954"
      > </a
      ><a name="14955" class="Symbol"
      >(</a
      ><a name="14956" href="Relations.html#14956" class="Bound"
      >m</a
      ><a name="14957"
      > </a
      ><a name="14958" href="Relations.html#14958" class="Bound"
      >n</a
      ><a name="14959"
      > </a
      ><a name="14960" href="Relations.html#14960" class="Bound"
      >p</a
      ><a name="14961"
      > </a
      ><a name="14962" href="Relations.html#14962" class="Bound"
      >q</a
      ><a name="14963"
      > </a
      ><a name="14964" class="Symbol"
      >:</a
      ><a name="14965"
      > </a
      ><a name="14966" href="Naturals.html#1064" class="Datatype"
      >&#8469;</a
      ><a name="14967" class="Symbol"
      >)</a
      ><a name="14968"
      > </a
      ><a name="14969" class="Symbol"
      >&#8594;</a
      ><a name="14970"
      > </a
      ><a name="14971" href="Relations.html#14956" class="Bound"
      >m</a
      ><a name="14972"
      > </a
      ><a name="14973" href="Relations.html#1114" class="Datatype Operator"
      >&#8804;</a
      ><a name="14974"
      > </a
      ><a name="14975" href="Relations.html#14958" class="Bound"
      >n</a
      ><a name="14976"
      > </a
      ><a name="14977" class="Symbol"
      >&#8594;</a
      ><a name="14978"
      > </a
      ><a name="14979" href="Relations.html#14960" class="Bound"
      >p</a
      ><a name="14980"
      > </a
      ><a name="14981" href="Relations.html#1114" class="Datatype Operator"
      >&#8804;</a
      ><a name="14982"
      > </a
      ><a name="14983" href="Relations.html#14962" class="Bound"
      >q</a
      ><a name="14984"
      > </a
      ><a name="14985" class="Symbol"
      >&#8594;</a
      ><a name="14986"
      > </a
      ><a name="14987" href="Relations.html#14956" class="Bound"
      >m</a
      ><a name="14988"
      > </a
      ><a name="14989" href="Naturals.html#9439" class="Primitive Operator"
      >+</a
      ><a name="14990"
      > </a
      ><a name="14991" href="Relations.html#14960" class="Bound"
      >p</a
      ><a name="14992"
      > </a
      ><a name="14993" href="Relations.html#1114" class="Datatype Operator"
      >&#8804;</a
      ><a name="14994"
      > </a
      ><a name="14995" href="Relations.html#14958" class="Bound"
      >n</a
      ><a name="14996"
      > </a
      ><a name="14997" href="Naturals.html#9439" class="Primitive Operator"
      >+</a
      ><a name="14998"
      > </a
      ><a name="14999" href="Relations.html#14962" class="Bound"
      >q</a
      ><a name="15000"
      >
</a
      ><a name="15001" href="Relations.html#14944" class="Function"
      >mono+&#8804;</a
      ><a name="15007"
      > </a
      ><a name="15008" href="Relations.html#15008" class="Bound"
      >m</a
      ><a name="15009"
      > </a
      ><a name="15010" href="Relations.html#15010" class="Bound"
      >n</a
      ><a name="15011"
      > </a
      ><a name="15012" href="Relations.html#15012" class="Bound"
      >p</a
      ><a name="15013"
      > </a
      ><a name="15014" href="Relations.html#15014" class="Bound"
      >q</a
      ><a name="15015"
      > </a
      ><a name="15016" href="Relations.html#15016" class="Bound"
      >m&#8804;n</a
      ><a name="15019"
      > </a
      ><a name="15020" href="Relations.html#15020" class="Bound"
      >p&#8804;q</a
      ><a name="15023"
      > </a
      ><a name="15024" class="Symbol"
      >=</a
      ><a name="15025"
      > </a
      ><a name="15026" href="Relations.html#6025" class="Function"
      >&#8804;-trans</a
      ><a name="15033"
      > </a
      ><a name="15034" class="Symbol"
      >(</a
      ><a name="15035" href="Relations.html#14610" class="Function"
      >+-mono&#737;-&#8804;</a
      ><a name="15044"
      > </a
      ><a name="15045" href="Relations.html#15008" class="Bound"
      >m</a
      ><a name="15046"
      > </a
      ><a name="15047" href="Relations.html#15010" class="Bound"
      >n</a
      ><a name="15048"
      > </a
      ><a name="15049" href="Relations.html#15012" class="Bound"
      >p</a
      ><a name="15050"
      > </a
      ><a name="15051" href="Relations.html#15016" class="Bound"
      >m&#8804;n</a
      ><a name="15054" class="Symbol"
      >)</a
      ><a name="15055"
      > </a
      ><a name="15056" class="Symbol"
      >(</a
      ><a name="15057" href="Relations.html#13779" class="Function"
      >+-mono&#691;-&#8804;</a
      ><a name="15066"
      > </a
      ><a name="15067" href="Relations.html#15010" class="Bound"
      >n</a
      ><a name="15068"
      > </a
      ><a name="15069" href="Relations.html#15012" class="Bound"
      >p</a
      ><a name="15070"
      > </a
      ><a name="15071" href="Relations.html#15014" class="Bound"
      >q</a
      ><a name="15072"
      > </a
      ><a name="15073" href="Relations.html#15020" class="Bound"
      >p&#8804;q</a
      ><a name="15076" class="Symbol"
      >)</a
      >
{% endraw %}</pre>
Invoking `+-monoˡ-≤ m n p m≤n` proves `m + p ≤ n + p` and invoking
`+-monoʳ-≤ n p q p≤q` proves `n + p ≤ n + q`, and combining these with
transitivity proves `m + p ≤ n + q`, as was to be shown.


## Exercises

We can define strict comparison similarly to comparison.
<pre class="Agda">{% raw %}
<a name="15370" class="Keyword"
      >data</a
      ><a name="15374"
      > </a
      ><a name="15375" href="Relations.html#15375" class="Datatype Operator"
      >_&lt;_</a
      ><a name="15378"
      > </a
      ><a name="15379" class="Symbol"
      >:</a
      ><a name="15380"
      > </a
      ><a name="15381" href="Naturals.html#1064" class="Datatype"
      >&#8469;</a
      ><a name="15382"
      > </a
      ><a name="15383" class="Symbol"
      >&#8594;</a
      ><a name="15384"
      > </a
      ><a name="15385" href="Naturals.html#1064" class="Datatype"
      >&#8469;</a
      ><a name="15386"
      > </a
      ><a name="15387" class="Symbol"
      >&#8594;</a
      ><a name="15388"
      > </a
      ><a name="15389" class="PrimitiveType"
      >Set</a
      ><a name="15392"
      > </a
      ><a name="15393" class="Keyword"
      >where</a
      ><a name="15398"
      >
  </a
      ><a name="15401" href="Relations.html#15401" class="InductiveConstructor"
      >z&lt;s</a
      ><a name="15404"
      > </a
      ><a name="15405" class="Symbol"
      >:</a
      ><a name="15406"
      > </a
      ><a name="15407" class="Symbol"
      >&#8704;</a
      ><a name="15408"
      > </a
      ><a name="15409" class="Symbol"
      >{</a
      ><a name="15410" href="Relations.html#15410" class="Bound"
      >n</a
      ><a name="15411"
      > </a
      ><a name="15412" class="Symbol"
      >:</a
      ><a name="15413"
      > </a
      ><a name="15414" href="Naturals.html#1064" class="Datatype"
      >&#8469;</a
      ><a name="15415" class="Symbol"
      >}</a
      ><a name="15416"
      > </a
      ><a name="15417" class="Symbol"
      >&#8594;</a
      ><a name="15418"
      > </a
      ><a name="15419" href="Naturals.html#1080" class="InductiveConstructor"
      >zero</a
      ><a name="15423"
      > </a
      ><a name="15424" href="Relations.html#15375" class="Datatype Operator"
      >&lt;</a
      ><a name="15425"
      > </a
      ><a name="15426" href="Naturals.html#1091" class="InductiveConstructor"
      >suc</a
      ><a name="15429"
      > </a
      ><a name="15430" href="Relations.html#15410" class="Bound"
      >n</a
      ><a name="15431"
      >
  </a
      ><a name="15434" href="Relations.html#15434" class="InductiveConstructor"
      >s&lt;s</a
      ><a name="15437"
      > </a
      ><a name="15438" class="Symbol"
      >:</a
      ><a name="15439"
      > </a
      ><a name="15440" class="Symbol"
      >&#8704;</a
      ><a name="15441"
      > </a
      ><a name="15442" class="Symbol"
      >{</a
      ><a name="15443" href="Relations.html#15443" class="Bound"
      >m</a
      ><a name="15444"
      > </a
      ><a name="15445" href="Relations.html#15445" class="Bound"
      >n</a
      ><a name="15446"
      > </a
      ><a name="15447" class="Symbol"
      >:</a
      ><a name="15448"
      > </a
      ><a name="15449" href="Naturals.html#1064" class="Datatype"
      >&#8469;</a
      ><a name="15450" class="Symbol"
      >}</a
      ><a name="15451"
      > </a
      ><a name="15452" class="Symbol"
      >&#8594;</a
      ><a name="15453"
      > </a
      ><a name="15454" href="Relations.html#15443" class="Bound"
      >m</a
      ><a name="15455"
      > </a
      ><a name="15456" href="Relations.html#15375" class="Datatype Operator"
      >&lt;</a
      ><a name="15457"
      > </a
      ><a name="15458" href="Relations.html#15445" class="Bound"
      >n</a
      ><a name="15459"
      > </a
      ><a name="15460" class="Symbol"
      >&#8594;</a
      ><a name="15461"
      > </a
      ><a name="15462" href="Naturals.html#1091" class="InductiveConstructor"
      >suc</a
      ><a name="15465"
      > </a
      ><a name="15466" href="Relations.html#15443" class="Bound"
      >m</a
      ><a name="15467"
      > </a
      ><a name="15468" href="Relations.html#15375" class="Datatype Operator"
      >&lt;</a
      ><a name="15469"
      > </a
      ><a name="15470" href="Naturals.html#1091" class="InductiveConstructor"
      >suc</a
      ><a name="15473"
      > </a
      ><a name="15474" href="Relations.html#15445" class="Bound"
      >n</a
      ><a name="15475"
      >

</a
      ><a name="15477" class="Keyword"
      >infix</a
      ><a name="15482"
      > </a
      ><a name="15483" class="Number"
      >4</a
      ><a name="15484"
      > </a
      ><a name="15485" href="Relations.html#15375" class="Datatype Operator"
      >_&lt;_</a
      >
{% endraw %}</pre>

+ *Irreflexivity* Show that `n < n` never holds
  for any natural `n`. (This requires negation,
  introduced in the chapter on Logic.)
  Name your proof `<-irrefl`.

+ *Transitivity* Show that

  > if `m < n` and `n < p` then `m < p`

  for all naturals `m`, `n`, and `p`. Name your proof `<-trans`.

+ *Trichotomy* Corresponding to anti-symmetry and totality
  of comparison, we have trichotomy for strict comparison.
  Show that for any given any naturals `m` and `n` that
  `Trichotomy m n` holds, using the defintions below.
  Name your proof `trichotomy`.
  
<pre class="Agda">{% raw %}
<a name="16078" href="Relations.html#16078" class="Function Operator"
      >_&gt;_</a
      ><a name="16081"
      > </a
      ><a name="16082" class="Symbol"
      >:</a
      ><a name="16083"
      > </a
      ><a name="16084" href="Naturals.html#1064" class="Datatype"
      >&#8469;</a
      ><a name="16085"
      > </a
      ><a name="16086" class="Symbol"
      >&#8594;</a
      ><a name="16087"
      > </a
      ><a name="16088" href="Naturals.html#1064" class="Datatype"
      >&#8469;</a
      ><a name="16089"
      > </a
      ><a name="16090" class="Symbol"
      >&#8594;</a
      ><a name="16091"
      > </a
      ><a name="16092" class="PrimitiveType"
      >Set</a
      ><a name="16095"
      >
</a
      ><a name="16096" href="Relations.html#16096" class="Bound"
      >n</a
      ><a name="16097"
      > </a
      ><a name="16098" href="Relations.html#16078" class="Function Operator"
      >&gt;</a
      ><a name="16099"
      > </a
      ><a name="16100" href="Relations.html#16100" class="Bound"
      >m</a
      ><a name="16101"
      > </a
      ><a name="16102" class="Symbol"
      >=</a
      ><a name="16103"
      > </a
      ><a name="16104" href="Relations.html#16100" class="Bound"
      >m</a
      ><a name="16105"
      > </a
      ><a name="16106" href="Relations.html#15375" class="Datatype Operator"
      >&lt;</a
      ><a name="16107"
      > </a
      ><a name="16108" href="Relations.html#16096" class="Bound"
      >n</a
      ><a name="16109"
      >

</a
      ><a name="16111" class="Keyword"
      >infix</a
      ><a name="16116"
      > </a
      ><a name="16117" class="Number"
      >4</a
      ><a name="16118"
      > </a
      ><a name="16119" href="Relations.html#16078" class="Function Operator"
      >_&gt;_</a
      ><a name="16122"
      >

</a
      ><a name="16124" class="Keyword"
      >data</a
      ><a name="16128"
      > </a
      ><a name="16129" href="Relations.html#16129" class="Datatype"
      >Trichotomy</a
      ><a name="16139"
      > </a
      ><a name="16140" class="Symbol"
      >:</a
      ><a name="16141"
      > </a
      ><a name="16142" href="Naturals.html#1064" class="Datatype"
      >&#8469;</a
      ><a name="16143"
      > </a
      ><a name="16144" class="Symbol"
      >&#8594;</a
      ><a name="16145"
      > </a
      ><a name="16146" href="Naturals.html#1064" class="Datatype"
      >&#8469;</a
      ><a name="16147"
      > </a
      ><a name="16148" class="Symbol"
      >&#8594;</a
      ><a name="16149"
      > </a
      ><a name="16150" class="PrimitiveType"
      >Set</a
      ><a name="16153"
      > </a
      ><a name="16154" class="Keyword"
      >where</a
      ><a name="16159"
      >
  </a
      ><a name="16162" href="Relations.html#16162" class="InductiveConstructor"
      >less</a
      ><a name="16166"
      > </a
      ><a name="16167" class="Symbol"
      >:</a
      ><a name="16168"
      > </a
      ><a name="16169" class="Symbol"
      >&#8704;</a
      ><a name="16170"
      > </a
      ><a name="16171" class="Symbol"
      >{</a
      ><a name="16172" href="Relations.html#16172" class="Bound"
      >m</a
      ><a name="16173"
      > </a
      ><a name="16174" href="Relations.html#16174" class="Bound"
      >n</a
      ><a name="16175"
      > </a
      ><a name="16176" class="Symbol"
      >:</a
      ><a name="16177"
      > </a
      ><a name="16178" href="Naturals.html#1064" class="Datatype"
      >&#8469;</a
      ><a name="16179" class="Symbol"
      >}</a
      ><a name="16180"
      > </a
      ><a name="16181" class="Symbol"
      >&#8594;</a
      ><a name="16182"
      > </a
      ><a name="16183" href="Relations.html#16172" class="Bound"
      >m</a
      ><a name="16184"
      > </a
      ><a name="16185" href="Relations.html#15375" class="Datatype Operator"
      >&lt;</a
      ><a name="16186"
      > </a
      ><a name="16187" href="Relations.html#16174" class="Bound"
      >n</a
      ><a name="16188"
      > </a
      ><a name="16189" class="Symbol"
      >&#8594;</a
      ><a name="16190"
      > </a
      ><a name="16191" href="Relations.html#16129" class="Datatype"
      >Trichotomy</a
      ><a name="16201"
      > </a
      ><a name="16202" href="Relations.html#16172" class="Bound"
      >m</a
      ><a name="16203"
      > </a
      ><a name="16204" href="Relations.html#16174" class="Bound"
      >n</a
      ><a name="16205"
      >
  </a
      ><a name="16208" href="Relations.html#16208" class="InductiveConstructor"
      >same</a
      ><a name="16212"
      > </a
      ><a name="16213" class="Symbol"
      >:</a
      ><a name="16214"
      > </a
      ><a name="16215" class="Symbol"
      >&#8704;</a
      ><a name="16216"
      > </a
      ><a name="16217" class="Symbol"
      >{</a
      ><a name="16218" href="Relations.html#16218" class="Bound"
      >m</a
      ><a name="16219"
      > </a
      ><a name="16220" href="Relations.html#16220" class="Bound"
      >n</a
      ><a name="16221"
      > </a
      ><a name="16222" class="Symbol"
      >:</a
      ><a name="16223"
      > </a
      ><a name="16224" href="Naturals.html#1064" class="Datatype"
      >&#8469;</a
      ><a name="16225" class="Symbol"
      >}</a
      ><a name="16226"
      > </a
      ><a name="16227" class="Symbol"
      >&#8594;</a
      ><a name="16228"
      > </a
      ><a name="16229" href="Relations.html#16218" class="Bound"
      >m</a
      ><a name="16230"
      > </a
      ><a name="16231" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator"
      >&#8801;</a
      ><a name="16232"
      > </a
      ><a name="16233" href="Relations.html#16220" class="Bound"
      >n</a
      ><a name="16234"
      > </a
      ><a name="16235" class="Symbol"
      >&#8594;</a
      ><a name="16236"
      > </a
      ><a name="16237" href="Relations.html#16129" class="Datatype"
      >Trichotomy</a
      ><a name="16247"
      > </a
      ><a name="16248" href="Relations.html#16218" class="Bound"
      >m</a
      ><a name="16249"
      > </a
      ><a name="16250" href="Relations.html#16220" class="Bound"
      >n</a
      ><a name="16251"
      >
  </a
      ><a name="16254" href="Relations.html#16254" class="InductiveConstructor"
      >more</a
      ><a name="16258"
      > </a
      ><a name="16259" class="Symbol"
      >:</a
      ><a name="16260"
      > </a
      ><a name="16261" class="Symbol"
      >&#8704;</a
      ><a name="16262"
      > </a
      ><a name="16263" class="Symbol"
      >{</a
      ><a name="16264" href="Relations.html#16264" class="Bound"
      >m</a
      ><a name="16265"
      > </a
      ><a name="16266" href="Relations.html#16266" class="Bound"
      >n</a
      ><a name="16267"
      > </a
      ><a name="16268" class="Symbol"
      >:</a
      ><a name="16269"
      > </a
      ><a name="16270" href="Naturals.html#1064" class="Datatype"
      >&#8469;</a
      ><a name="16271" class="Symbol"
      >}</a
      ><a name="16272"
      > </a
      ><a name="16273" class="Symbol"
      >&#8594;</a
      ><a name="16274"
      > </a
      ><a name="16275" href="Relations.html#16264" class="Bound"
      >m</a
      ><a name="16276"
      > </a
      ><a name="16277" href="Relations.html#16078" class="Function Operator"
      >&gt;</a
      ><a name="16278"
      > </a
      ><a name="16279" href="Relations.html#16266" class="Bound"
      >n</a
      ><a name="16280"
      > </a
      ><a name="16281" class="Symbol"
      >&#8594;</a
      ><a name="16282"
      > </a
      ><a name="16283" href="Relations.html#16129" class="Datatype"
      >Trichotomy</a
      ><a name="16293"
      > </a
      ><a name="16294" href="Relations.html#16264" class="Bound"
      >m</a
      ><a name="16295"
      > </a
      ><a name="16296" href="Relations.html#16266" class="Bound"
      >n</a
      >
{% endraw %}</pre>

+ *Monotonicity* Show that

  > if `m < n` and `p < q` then `m + n < p + q`.

  Name your proof `+-mono-<`.

+ *Relate strict comparison to comparison*
  Show that `m < n` if and only if `suc m ≤ n`.
  Name the two parts of your proof
  `<-implies-≤` and `≤-implies-<`

  To confirm your understanding, you should prove transitivity, trichotomy,
  and monotonicity for `<` directly by modifying
  the original proofs for `≤`.  Once you've done so, you may then wish to redo
  the proofs exploiting the last exercise, so each property of `<` becomes
  an easy consequence of the corresponding property for `≤`.

+ *Even and odd* Another example of a useful relation is to define
  even and odd numbers, as done below.  Using these definitions, show
  - the sum of two even numbers is even
  - the sum of an even and an odd number is odd
  - the sum of two odd numbers is even

<pre class="Agda">{% raw %}
<a name="17199" class="Keyword"
      >mutual</a
      ><a name="17205"
      >
  </a
      ><a name="17208" class="Keyword"
      >data</a
      ><a name="17212"
      > </a
      ><a name="17213" href="Relations.html#17213" class="Datatype"
      >even</a
      ><a name="17217"
      > </a
      ><a name="17218" class="Symbol"
      >:</a
      ><a name="17219"
      > </a
      ><a name="17220" href="Naturals.html#1064" class="Datatype"
      >&#8469;</a
      ><a name="17221"
      > </a
      ><a name="17222" class="Symbol"
      >&#8594;</a
      ><a name="17223"
      > </a
      ><a name="17224" class="PrimitiveType"
      >Set</a
      ><a name="17227"
      > </a
      ><a name="17228" class="Keyword"
      >where</a
      ><a name="17233"
      >
    </a
      ><a name="17238" href="Relations.html#17238" class="InductiveConstructor"
      >ev-zero</a
      ><a name="17245"
      > </a
      ><a name="17246" class="Symbol"
      >:</a
      ><a name="17247"
      > </a
      ><a name="17248" href="Relations.html#17213" class="Datatype"
      >even</a
      ><a name="17252"
      > </a
      ><a name="17253" href="Naturals.html#1080" class="InductiveConstructor"
      >zero</a
      ><a name="17257"
      >
    </a
      ><a name="17262" href="Relations.html#17262" class="InductiveConstructor"
      >ev-suc</a
      ><a name="17268"
      > </a
      ><a name="17269" class="Symbol"
      >:</a
      ><a name="17270"
      > </a
      ><a name="17271" class="Symbol"
      >&#8704;</a
      ><a name="17272"
      > </a
      ><a name="17273" class="Symbol"
      >{</a
      ><a name="17274" href="Relations.html#17274" class="Bound"
      >n</a
      ><a name="17275"
      > </a
      ><a name="17276" class="Symbol"
      >:</a
      ><a name="17277"
      > </a
      ><a name="17278" href="Naturals.html#1064" class="Datatype"
      >&#8469;</a
      ><a name="17279" class="Symbol"
      >}</a
      ><a name="17280"
      > </a
      ><a name="17281" class="Symbol"
      >&#8594;</a
      ><a name="17282"
      > </a
      ><a name="17283" href="Relations.html#17311" class="Datatype"
      >odd</a
      ><a name="17286"
      > </a
      ><a name="17287" href="Relations.html#17274" class="Bound"
      >n</a
      ><a name="17288"
      > </a
      ><a name="17289" class="Symbol"
      >&#8594;</a
      ><a name="17290"
      > </a
      ><a name="17291" href="Relations.html#17213" class="Datatype"
      >even</a
      ><a name="17295"
      > </a
      ><a name="17296" class="Symbol"
      >(</a
      ><a name="17297" href="Naturals.html#1091" class="InductiveConstructor"
      >suc</a
      ><a name="17300"
      > </a
      ><a name="17301" href="Relations.html#17274" class="Bound"
      >n</a
      ><a name="17302" class="Symbol"
      >)</a
      ><a name="17303"
      >
  </a
      ><a name="17306" class="Keyword"
      >data</a
      ><a name="17310"
      > </a
      ><a name="17311" href="Relations.html#17311" class="Datatype"
      >odd</a
      ><a name="17314"
      > </a
      ><a name="17315" class="Symbol"
      >:</a
      ><a name="17316"
      > </a
      ><a name="17317" href="Naturals.html#1064" class="Datatype"
      >&#8469;</a
      ><a name="17318"
      > </a
      ><a name="17319" class="Symbol"
      >&#8594;</a
      ><a name="17320"
      > </a
      ><a name="17321" class="PrimitiveType"
      >Set</a
      ><a name="17324"
      > </a
      ><a name="17325" class="Keyword"
      >where</a
      ><a name="17330"
      >
    </a
      ><a name="17335" href="Relations.html#17335" class="InductiveConstructor"
      >od-suc</a
      ><a name="17341"
      > </a
      ><a name="17342" class="Symbol"
      >:</a
      ><a name="17343"
      > </a
      ><a name="17344" class="Symbol"
      >&#8704;</a
      ><a name="17345"
      > </a
      ><a name="17346" class="Symbol"
      >{</a
      ><a name="17347" href="Relations.html#17347" class="Bound"
      >n</a
      ><a name="17348"
      > </a
      ><a name="17349" class="Symbol"
      >:</a
      ><a name="17350"
      > </a
      ><a name="17351" href="Naturals.html#1064" class="Datatype"
      >&#8469;</a
      ><a name="17352" class="Symbol"
      >}</a
      ><a name="17353"
      > </a
      ><a name="17354" class="Symbol"
      >&#8594;</a
      ><a name="17355"
      > </a
      ><a name="17356" href="Relations.html#17213" class="Datatype"
      >even</a
      ><a name="17360"
      > </a
      ><a name="17361" href="Relations.html#17347" class="Bound"
      >n</a
      ><a name="17362"
      > </a
      ><a name="17363" class="Symbol"
      >&#8594;</a
      ><a name="17364"
      > </a
      ><a name="17365" href="Relations.html#17311" class="Datatype"
      >odd</a
      ><a name="17368"
      > </a
      ><a name="17369" class="Symbol"
      >(</a
      ><a name="17370" href="Naturals.html#1091" class="InductiveConstructor"
      >suc</a
      ><a name="17373"
      > </a
      ><a name="17374" href="Relations.html#17347" class="Bound"
      >n</a
      ><a name="17375" class="Symbol"
      >)</a
      >
{% endraw %}</pre>
The keyword `mutual` indicates that the nested definitions
are mutually recursive.

<!-- Newer version of Agda?
Because the two defintions are mutually recursive, the type
`Even` and `Odd` must be declared before they are defined.  The
declaration just repeats the first line of the definition, but without
the keyword `where`. -->


## Unicode

This chapter introduces the following unicode.

    ≤  U+2264  LESS-THAN OR EQUAL TO (\<=, \le)
    ˡ  U+02E1  MODIFIER LETTER SMALL L (\^l)
    ʳ  U+02B3  MODIFIER LETTER SMALL R (\^r)
    ₁  U+2081  SUBSCRIPT ONE (\_1)
    ₂  U+2082  SUBSCRIPT TWO (\_2)
    
