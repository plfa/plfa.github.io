---
src       : src/plfa/Negation.lagda
title     : "Negation: Negation, with intuitionistic and classical logic"
layout    : page
prev      : /Connectives/
permalink : /Negation/
next      : /Quantifiers/
---

<pre class="Agda">{% raw %}<a id="189" class="Keyword">module</a> <a id="196" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}" class="Module">plfa.Negation</a> <a id="210" class="Keyword">where</a>{% endraw %}</pre>

This chapter introduces negation, and discusses intuitionistic
and classical logic.

## Imports

<pre class="Agda">{% raw %}<a id="338" class="Keyword">open</a> <a id="343" class="Keyword">import</a> <a id="350" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html" class="Module">Relation.Binary.PropositionalEquality</a> <a id="388" class="Keyword">using</a> <a id="394" class="Symbol">(</a><a id="395" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator">_≡_</a><a id="398" class="Symbol">;</a> <a id="400" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor">refl</a><a id="404" class="Symbol">)</a>
<a id="406" class="Keyword">open</a> <a id="411" class="Keyword">import</a> <a id="418" href="https://agda.github.io/agda-stdlib/Data.Nat.html" class="Module">Data.Nat</a> <a id="427" class="Keyword">using</a> <a id="433" class="Symbol">(</a><a id="434" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a><a id="435" class="Symbol">;</a> <a id="437" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#115" class="InductiveConstructor">zero</a><a id="441" class="Symbol">;</a> <a id="443" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a><a id="446" class="Symbol">)</a>
<a id="448" class="Keyword">open</a> <a id="453" class="Keyword">import</a> <a id="460" href="https://agda.github.io/agda-stdlib/Data.Empty.html" class="Module">Data.Empty</a> <a id="471" class="Keyword">using</a> <a id="477" class="Symbol">(</a><a id="478" href="https://agda.github.io/agda-stdlib/Data.Empty.html#243" class="Datatype">⊥</a><a id="479" class="Symbol">;</a> <a id="481" href="https://agda.github.io/agda-stdlib/Data.Empty.html#360" class="Function">⊥-elim</a><a id="487" class="Symbol">)</a>
<a id="489" class="Keyword">open</a> <a id="494" class="Keyword">import</a> <a id="501" href="https://agda.github.io/agda-stdlib/Data.Sum.html" class="Module">Data.Sum</a> <a id="510" class="Keyword">using</a> <a id="516" class="Symbol">(</a><a id="517" href="https://agda.github.io/agda-stdlib/Data.Sum.Base.html#419" class="Datatype Operator">_⊎_</a><a id="520" class="Symbol">;</a> <a id="522" href="https://agda.github.io/agda-stdlib/Data.Sum.Base.html#475" class="InductiveConstructor">inj₁</a><a id="526" class="Symbol">;</a> <a id="528" href="https://agda.github.io/agda-stdlib/Data.Sum.Base.html#500" class="InductiveConstructor">inj₂</a><a id="532" class="Symbol">)</a>
<a id="534" class="Keyword">open</a> <a id="539" class="Keyword">import</a> <a id="546" href="https://agda.github.io/agda-stdlib/Data.Product.html" class="Module">Data.Product</a> <a id="559" class="Keyword">using</a> <a id="565" class="Symbol">(</a><a id="566" href="https://agda.github.io/agda-stdlib/Data.Product.html#1353" class="Function Operator">_×_</a><a id="569" class="Symbol">;</a> <a id="571" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Sigma.html#155" class="Field">proj₁</a><a id="576" class="Symbol">;</a> <a id="578" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Sigma.html#167" class="Field">proj₂</a><a id="583" class="Symbol">)</a> <a id="585" class="Keyword">renaming</a> <a id="594" class="Symbol">(</a><a id="595" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Sigma.html#139" class="InductiveConstructor Operator">_,_</a> <a id="599" class="Symbol">to</a> <a id="602" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Sigma.html#139" class="InductiveConstructor Operator">⟨_,_⟩</a><a id="607" class="Symbol">)</a>
<a id="609" class="Keyword">open</a> <a id="614" class="Keyword">import</a> <a id="621" href="https://agda.github.io/agda-stdlib/Function.html" class="Module">Function</a> <a id="630" class="Keyword">using</a> <a id="636" class="Symbol">(</a><a id="637" href="https://agda.github.io/agda-stdlib/Function.html#769" class="Function Operator">_∘_</a><a id="640" class="Symbol">)</a>
<a id="642" class="Keyword">open</a> <a id="647" class="Keyword">import</a> <a id="654" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}" class="Module">plfa.Isomorphism</a> <a id="671" class="Keyword">using</a> <a id="677" class="Symbol">(</a><a id="678" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#4104" class="Record Operator">_≃_</a><a id="681" class="Symbol">;</a> <a id="683" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#6802" class="Function">≃-sym</a><a id="688" class="Symbol">;</a> <a id="690" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#7143" class="Function">≃-trans</a><a id="697" class="Symbol">;</a> <a id="699" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#9013" class="Record Operator">_≲_</a><a id="702" class="Symbol">;</a> <a id="704" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#2748" class="Postulate">extensionality</a><a id="718" class="Symbol">)</a>{% endraw %}</pre>


## Negation

Given a proposition `A`, the negation `¬ A` holds if `A` cannot hold.
We formalise this idea by declaring negation to be the same
as implication of false.
<pre class="Agda">{% raw %}<a id="¬_"></a><a id="914" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#914" class="Function Operator">¬_</a> <a id="917" class="Symbol">:</a> <a id="919" class="PrimitiveType">Set</a> <a id="923" class="Symbol">→</a> <a id="925" class="PrimitiveType">Set</a>
<a id="929" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#914" class="Function Operator">¬</a> <a id="931" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#931" class="Bound">A</a> <a id="933" class="Symbol">=</a> <a id="935" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#931" class="Bound">A</a> <a id="937" class="Symbol">→</a> <a id="939" href="https://agda.github.io/agda-stdlib/Data.Empty.html#243" class="Datatype">⊥</a>{% endraw %}</pre>
This is a form of _proof by contradiction_: if assuming `A` leads
to the conclusion `⊥` (a contradiction), then we must have `¬ A`.

Evidence that `¬ A` holds is of the form

    λ{ x → N }

where `N` is a term of type `⊥` containing as a free variable `x` of type `A`.
In other words, evidence that `¬ A` holds is a function that converts evidence
that `A` holds into evidence that `⊥` holds.

Given evidence that both `¬ A` and `A` hold, we can conclude that `⊥` holds.
In other words, if both `¬ A` and `A` hold, then we have a contradiction.
<pre class="Agda">{% raw %}<a id="¬-elim"></a><a id="1511" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#1511" class="Function">¬-elim</a> <a id="1518" class="Symbol">:</a> <a id="1520" class="Symbol">∀</a> <a id="1522" class="Symbol">{</a><a id="1523" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#1523" class="Bound">A</a> <a id="1525" class="Symbol">:</a> <a id="1527" class="PrimitiveType">Set</a><a id="1530" class="Symbol">}</a>
  <a id="1534" class="Symbol">→</a> <a id="1536" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#914" class="Function Operator">¬</a> <a id="1538" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#1523" class="Bound">A</a>
  <a id="1542" class="Symbol">→</a> <a id="1544" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#1523" class="Bound">A</a>
    <a id="1550" class="Comment">---</a>
  <a id="1556" class="Symbol">→</a> <a id="1558" href="https://agda.github.io/agda-stdlib/Data.Empty.html#243" class="Datatype">⊥</a>
<a id="1560" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#1511" class="Function">¬-elim</a> <a id="1567" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#1567" class="Bound">¬x</a> <a id="1570" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#1570" class="Bound">x</a> <a id="1572" class="Symbol">=</a> <a id="1574" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#1567" class="Bound">¬x</a> <a id="1577" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#1570" class="Bound">x</a>{% endraw %}</pre>
Here we write `¬x` for evidence of `¬ A` and `x` for evidence of `A`.  This
means that `¬x` must be a function of type `A → ⊥`, and hence the application
`¬x x` must be of type `⊥`.  Note that this rule is just a special case of `→-elim`.

We set the precedence of negation so that it binds more tightly
than disjunction and conjunction, but less tightly than anything else.
<pre class="Agda">{% raw %}<a id="1978" class="Keyword">infix</a> <a id="1984" class="Number">3</a> <a id="1986" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#914" class="Function Operator">¬_</a>{% endraw %}</pre>
Thus, `¬ A × ¬ B` parses as `(¬ A) × (¬ B)` and `¬ m ≡ n` as `¬ (m ≡ n)`.

In _classical_ logic, we have that `A` is equivalent to `¬ ¬ A`.
As we discuss below, in Agda we use _intuitionistic_ logic, where
we have only half of this equivalence, namely that `A` implies `¬ ¬ A`.
<pre class="Agda">{% raw %}<a id="¬¬-intro"></a><a id="2291" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#2291" class="Function">¬¬-intro</a> <a id="2300" class="Symbol">:</a> <a id="2302" class="Symbol">∀</a> <a id="2304" class="Symbol">{</a><a id="2305" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#2305" class="Bound">A</a> <a id="2307" class="Symbol">:</a> <a id="2309" class="PrimitiveType">Set</a><a id="2312" class="Symbol">}</a>
  <a id="2316" class="Symbol">→</a> <a id="2318" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#2305" class="Bound">A</a>
    <a id="2324" class="Comment">-----</a>
  <a id="2332" class="Symbol">→</a> <a id="2334" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#914" class="Function Operator">¬</a> <a id="2336" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#914" class="Function Operator">¬</a> <a id="2338" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#2305" class="Bound">A</a>
<a id="2340" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#2291" class="Function">¬¬-intro</a> <a id="2349" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#2349" class="Bound">x</a>  <a id="2352" class="Symbol">=</a>  <a id="2355" class="Symbol">λ{</a><a id="2357" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#2357" class="Bound">¬x</a> <a id="2360" class="Symbol">→</a> <a id="2362" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#2357" class="Bound">¬x</a> <a id="2365" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#2349" class="Bound">x</a><a id="2366" class="Symbol">}</a>{% endraw %}</pre>
Let `x` be evidence of `A`. We show that assuming
`¬ A` leads to a contradiction, and hence `¬ ¬ A` must hold.
Let `¬x` be evidence of `¬ A`.  Then from `A` and `¬ A`
we have a contradiction, evidenced by `¬x x`.  Hence, we have
shown `¬ ¬ A`.

An equivalent way to write the above is as follows.
<pre class="Agda">{% raw %}<a id="¬¬-intro′"></a><a id="2689" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#2689" class="Function">¬¬-intro′</a> <a id="2699" class="Symbol">:</a> <a id="2701" class="Symbol">∀</a> <a id="2703" class="Symbol">{</a><a id="2704" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#2704" class="Bound">A</a> <a id="2706" class="Symbol">:</a> <a id="2708" class="PrimitiveType">Set</a><a id="2711" class="Symbol">}</a>
  <a id="2715" class="Symbol">→</a> <a id="2717" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#2704" class="Bound">A</a>
    <a id="2723" class="Comment">-----</a>
  <a id="2731" class="Symbol">→</a> <a id="2733" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#914" class="Function Operator">¬</a> <a id="2735" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#914" class="Function Operator">¬</a> <a id="2737" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#2704" class="Bound">A</a>
<a id="2739" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#2689" class="Function">¬¬-intro′</a> <a id="2749" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#2749" class="Bound">x</a> <a id="2751" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#2751" class="Bound">¬x</a> <a id="2754" class="Symbol">=</a> <a id="2756" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#2751" class="Bound">¬x</a> <a id="2759" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#2749" class="Bound">x</a>{% endraw %}</pre>
Here we have simply converted the argument of the lambda term
to an additional argument of the function.  We will usually
use this latter style, as it is more compact.

We cannot show that `¬ ¬ A` implies `A`, but we can show that
`¬ ¬ ¬ A` implies `¬ A`.
<pre class="Agda">{% raw %}<a id="¬¬¬-elim"></a><a id="3041" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#3041" class="Function">¬¬¬-elim</a> <a id="3050" class="Symbol">:</a> <a id="3052" class="Symbol">∀</a> <a id="3054" class="Symbol">{</a><a id="3055" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#3055" class="Bound">A</a> <a id="3057" class="Symbol">:</a> <a id="3059" class="PrimitiveType">Set</a><a id="3062" class="Symbol">}</a>
  <a id="3066" class="Symbol">→</a> <a id="3068" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#914" class="Function Operator">¬</a> <a id="3070" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#914" class="Function Operator">¬</a> <a id="3072" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#914" class="Function Operator">¬</a> <a id="3074" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#3055" class="Bound">A</a>
    <a id="3080" class="Comment">-------</a>
  <a id="3090" class="Symbol">→</a> <a id="3092" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#914" class="Function Operator">¬</a> <a id="3094" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#3055" class="Bound">A</a>
<a id="3096" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#3041" class="Function">¬¬¬-elim</a> <a id="3105" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#3105" class="Bound">¬¬¬x</a>  <a id="3111" class="Symbol">=</a>  <a id="3114" class="Symbol">λ</a> <a id="3116" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#3116" class="Bound">x</a> <a id="3118" class="Symbol">→</a> <a id="3120" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#3105" class="Bound">¬¬¬x</a> <a id="3125" class="Symbol">(</a><a id="3126" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#2291" class="Function">¬¬-intro</a> <a id="3135" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#3116" class="Bound">x</a><a id="3136" class="Symbol">)</a>
<a id="3138" class="Comment">-- ¬¬¬-elim ¬¬¬x x = ¬¬¬x (¬¬-intro x)</a>{% endraw %}</pre>
Let `¬¬¬x` be evidence of `¬ ¬ ¬ A`. We will show that assuming
`A` leads to a contradiction, and hence `¬ A` must hold.
Let `x` be evidence of `A`. Then by the previous result, we
can conclude `¬ ¬ A`, evidenced by `¬¬-intro x`.  Then from
`¬ ¬ ¬ A` and `¬ ¬ A` we have a contradiction, evidenced by
`¬¬¬x (¬¬-intro x)`.  Hence we have shown `¬ A`.

Another law of logic is _contraposition_,
stating that if `A` implies `B`, then `¬ B` implies `¬ A`.
<pre class="Agda">{% raw %}<a id="contraposition"></a><a id="3653" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#3653" class="Function">contraposition</a> <a id="3668" class="Symbol">:</a> <a id="3670" class="Symbol">∀</a> <a id="3672" class="Symbol">{</a><a id="3673" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#3673" class="Bound">A</a> <a id="3675" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#3675" class="Bound">B</a> <a id="3677" class="Symbol">:</a> <a id="3679" class="PrimitiveType">Set</a><a id="3682" class="Symbol">}</a>
  <a id="3686" class="Symbol">→</a> <a id="3688" class="Symbol">(</a><a id="3689" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#3673" class="Bound">A</a> <a id="3691" class="Symbol">→</a> <a id="3693" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#3675" class="Bound">B</a><a id="3694" class="Symbol">)</a>
    <a id="3700" class="Comment">-----------</a>
  <a id="3714" class="Symbol">→</a> <a id="3716" class="Symbol">(</a><a id="3717" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#914" class="Function Operator">¬</a> <a id="3719" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#3675" class="Bound">B</a> <a id="3721" class="Symbol">→</a> <a id="3723" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#914" class="Function Operator">¬</a> <a id="3725" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#3673" class="Bound">A</a><a id="3726" class="Symbol">)</a>
<a id="3728" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#3653" class="Function">contraposition</a> <a id="3743" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#3743" class="Bound">f</a> <a id="3745" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#3745" class="Bound">¬y</a> <a id="3748" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#3748" class="Bound">x</a> <a id="3750" class="Symbol">=</a> <a id="3752" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#3745" class="Bound">¬y</a> <a id="3755" class="Symbol">(</a><a id="3756" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#3743" class="Bound">f</a> <a id="3758" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#3748" class="Bound">x</a><a id="3759" class="Symbol">)</a>{% endraw %}</pre>
Let `f` be evidence of `A → B` and let `¬y` be evidence of `¬ B`.  We
will show that assuming `A` leads to a contradiction, and hence `¬ A`
must hold. Let `x` be evidence of `A`.  Then from `A → B` and `A` we
may conclude `B`, evidenced by `f x`, and from `B` and `¬ B` we may
conclude `⊥`, evidenced by `¬y (f x)`.  Hence, we have shown `¬ A`.

Using negation, it is straightforward to define inequality.
<pre class="Agda">{% raw %}<a id="_≢_"></a><a id="4191" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#4191" class="Function Operator">_≢_</a> <a id="4195" class="Symbol">:</a> <a id="4197" class="Symbol">∀</a> <a id="4199" class="Symbol">{</a><a id="4200" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#4200" class="Bound">A</a> <a id="4202" class="Symbol">:</a> <a id="4204" class="PrimitiveType">Set</a><a id="4207" class="Symbol">}</a> <a id="4209" class="Symbol">→</a> <a id="4211" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#4200" class="Bound">A</a> <a id="4213" class="Symbol">→</a> <a id="4215" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#4200" class="Bound">A</a> <a id="4217" class="Symbol">→</a> <a id="4219" class="PrimitiveType">Set</a>
<a id="4223" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#4223" class="Bound">x</a> <a id="4225" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#4191" class="Function Operator">≢</a> <a id="4227" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#4227" class="Bound">y</a>  <a id="4230" class="Symbol">=</a>  <a id="4233" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#914" class="Function Operator">¬</a> <a id="4235" class="Symbol">(</a><a id="4236" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#4223" class="Bound">x</a> <a id="4238" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator">≡</a> <a id="4240" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#4227" class="Bound">y</a><a id="4241" class="Symbol">)</a>{% endraw %}</pre>
It is trivial to show distinct numbers are not equal.
<pre class="Agda">{% raw %}<a id="4321" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#4321" class="Function">_</a> <a id="4323" class="Symbol">:</a> <a id="4325" class="Number">1</a> <a id="4327" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#4191" class="Function Operator">≢</a> <a id="4329" class="Number">2</a>
<a id="4331" class="Symbol">_</a> <a id="4333" class="Symbol">=</a> <a id="4335" class="Symbol">λ()</a>{% endraw %}</pre>
This is our first use of an absurd pattern in a lambda expression.
The type `M ≡ N` is occupied exactly when `M` and `N` simplify to
identical terms. Since `1` and `2` simplify to distinct normal forms,
Agda determines that there is no possible evidence that `1 ≡ 2`.
As a second example, it is also easy to validate
Peano's postulate that zero is not the successor of any number.
<pre class="Agda">{% raw %}<a id="peano"></a><a id="4744" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#4744" class="Function">peano</a> <a id="4750" class="Symbol">:</a> <a id="4752" class="Symbol">∀</a> <a id="4754" class="Symbol">{</a><a id="4755" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#4755" class="Bound">m</a> <a id="4757" class="Symbol">:</a> <a id="4759" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a><a id="4760" class="Symbol">}</a> <a id="4762" class="Symbol">→</a> <a id="4764" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#115" class="InductiveConstructor">zero</a> <a id="4769" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#4191" class="Function Operator">≢</a> <a id="4771" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="4775" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#4755" class="Bound">m</a>
<a id="4777" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#4744" class="Function">peano</a> <a id="4783" class="Symbol">=</a> <a id="4785" class="Symbol">λ()</a>{% endraw %}</pre>
The evidence is essentially the same, as the absurd pattern matches
all possible evidence of type `zero ≡ suc m`.

Given the correspondence of implication to exponentiation and
false to the type with no members, we can view negation as
raising to the zero power.  This indeed corresponds to what
we know for arithmetic, where

    0 ^ n  ≡  1,  if n ≡ 0
           ≡  0,  if n ≢ 0

Indeed, there is exactly one proof of `⊥ → ⊥`.  We can write
this proof two different ways.
<pre class="Agda">{% raw %}<a id="id"></a><a id="5287" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#5287" class="Function">id</a> <a id="5290" class="Symbol">:</a> <a id="5292" href="https://agda.github.io/agda-stdlib/Data.Empty.html#243" class="Datatype">⊥</a> <a id="5294" class="Symbol">→</a> <a id="5296" href="https://agda.github.io/agda-stdlib/Data.Empty.html#243" class="Datatype">⊥</a>
<a id="5298" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#5287" class="Function">id</a> <a id="5301" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#5301" class="Bound">x</a> <a id="5303" class="Symbol">=</a> <a id="5305" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#5301" class="Bound">x</a>

<a id="id′"></a><a id="5308" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#5308" class="Function">id′</a> <a id="5312" class="Symbol">:</a> <a id="5314" href="https://agda.github.io/agda-stdlib/Data.Empty.html#243" class="Datatype">⊥</a> <a id="5316" class="Symbol">→</a> <a id="5318" href="https://agda.github.io/agda-stdlib/Data.Empty.html#243" class="Datatype">⊥</a>
<a id="5320" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#5308" class="Function">id′</a> <a id="5324" class="Symbol">()</a>{% endraw %}</pre>
But, using extensionality, we can prove these equal.
<pre class="Agda">{% raw %}<a id="id≡id′"></a><a id="5404" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#5404" class="Function">id≡id′</a> <a id="5411" class="Symbol">:</a> <a id="5413" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#5287" class="Function">id</a> <a id="5416" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator">≡</a> <a id="5418" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#5308" class="Function">id′</a>
<a id="5422" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#5404" class="Function">id≡id′</a> <a id="5429" class="Symbol">=</a> <a id="5431" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#2748" class="Postulate">extensionality</a> <a id="5446" class="Symbol">(λ())</a>{% endraw %}</pre>
By extensionality, `id ≡ id′` holds if for every
`x` in their domain we have `id x ≡ id′ x`. But there
is no `x` in their domain, so the equality holds trivially.

Indeed, we can show any two proofs of a negation are equal.
<pre class="Agda">{% raw %}<a id="assimilation"></a><a id="5700" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#5700" class="Function">assimilation</a> <a id="5713" class="Symbol">:</a> <a id="5715" class="Symbol">∀</a> <a id="5717" class="Symbol">{</a><a id="5718" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#5718" class="Bound">A</a> <a id="5720" class="Symbol">:</a> <a id="5722" class="PrimitiveType">Set</a><a id="5725" class="Symbol">}</a> <a id="5727" class="Symbol">(</a><a id="5728" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#5728" class="Bound">¬x</a> <a id="5731" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#5731" class="Bound">¬x′</a> <a id="5735" class="Symbol">:</a> <a id="5737" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#914" class="Function Operator">¬</a> <a id="5739" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#5718" class="Bound">A</a><a id="5740" class="Symbol">)</a> <a id="5742" class="Symbol">→</a> <a id="5744" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#5728" class="Bound">¬x</a> <a id="5747" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator">≡</a> <a id="5749" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#5731" class="Bound">¬x′</a>
<a id="5753" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#5700" class="Function">assimilation</a> <a id="5766" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#5766" class="Bound">¬x</a> <a id="5769" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#5769" class="Bound">¬x′</a> <a id="5773" class="Symbol">=</a> <a id="5775" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#2748" class="Postulate">extensionality</a> <a id="5790" class="Symbol">(λ</a> <a id="5793" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#5793" class="Bound">x</a> <a id="5795" class="Symbol">→</a> <a id="5797" href="https://agda.github.io/agda-stdlib/Data.Empty.html#360" class="Function">⊥-elim</a> <a id="5804" class="Symbol">(</a><a id="5805" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#5766" class="Bound">¬x</a> <a id="5808" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#5793" class="Bound">x</a><a id="5809" class="Symbol">))</a>{% endraw %}</pre>
Evidence for `¬ A` implies that any evidence of `A`
immediately leads to a contradiction.  But extensionality
quantifies over all `x` such that `A` holds, hence any
such `x` immediately leads to a contradiction,
again causing the equality to hold trivially.


#### Exercise `<-irreflexive` (recommended)

Using negation, show that
[strict inequality]({{ site.baseurl }}{% link out/plfa/Relations.md%}#strict-inequality)
is irreflexive, that is, `n < n` holds for no `n`.


#### Exercise `trichotomy`

Show that strict inequality satisfies
[trichotomy]({{ site.baseurl }}{% link out/plfa/Relations.md%}#trichotomy),
that is, for any naturals `m` and `n` exactly one of the following holds:

* `m < n`
* `m ≡ n`
* `m > n`

Here "exactly one" means that not only one of the three must hold,
but that when one holds the negation of the other two must also hold.

#### Exercise `⊎-dual-×` (recommended)

Show that conjunction, disjunction, and negation are related by a
version of De Morgan's Law.

    ¬ (A ⊎ B) ≃ (¬ A) × (¬ B)

This result is an easy consequence of something we've proved previously.

Do we also have the following?

    ¬ (A × B) ≃ (¬ A) ⊎ (¬ B)

If so, prove; if not, can you give a relation weaker than
isomorphism that relates the two sides?


## Intuitive and Classical logic

In Gilbert and Sullivan's _The Gondoliers_, Casilda is told that
as an infant she was married to the heir of the King of Batavia, but
that due to a mix-up no one knows which of two individuals, Marco or
Giuseppe, is the heir.  Alarmed, she wails "Then do you mean to say
that I am married to one of two gondoliers, but it is impossible to
say which?"  To which the response is "Without any doubt of any kind
whatever."

Logic comes in many varieties, and one distinction is between
_classical_ and _intuitionistic_. Intuitionists, concerned
by assumptions made by some logicians about the nature of
infinity, insist upon a constructionist notion of truth.  In
particular, they insist that a proof of `A ⊎ B` must show
_which_ of `A` or `B` holds, and hence they would reject the
claim that Casilda is married to Marco or Giuseppe until one of the
two was identified as her husband.  Perhaps Gilbert and Sullivan
anticipated intuitionism, for their story's outcome is that the heir
turns out to be a third individual, Luiz, with whom Casilda is,
conveniently, already in love.

Intuitionists also reject the law of the excluded middle, which
asserts `A ⊎ ¬ A` for every `A`, since the law gives no clue as to
_which_ of `A` or `¬ A` holds. Heyting formalised a variant of
Hilbert's classical logic that captures the intuitionistic notion of
provability. In particular, the law of the excluded middle is provable
in Hilbert's logic, but not in Heyting's.  Further, if the law of the
excluded middle is added as an axiom to Heyting's logic, then it
becomes equivalent to Hilbert's.  Kolmogorov showed the two logics
were closely related: he gave a double-negation translation, such that
a formula is provable in classical logic if and only if its
translation is provable in intuitionistic logic.

Propositions as Types was first formulated for intuitionistic logic.
It is a perfect fit, because in the intuitionist interpretation the
formula `A ⊎ B` is provable exactly when one exhibits either a proof
of `A` or a proof of `B`, so the type corresponding to disjunction is
a disjoint sum.

(Parts of the above are adopted from "Propositions as Types", Philip Wadler,
_Communications of the ACM_, December 2015.)

## Excluded middle is irrefutable

The law of the excluded middle can be formulated as follows.
<pre class="Agda">{% raw %}<a id="9368" class="Keyword">postulate</a>
  <a id="em"></a><a id="9380" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#9380" class="Postulate">em</a> <a id="9383" class="Symbol">:</a> <a id="9385" class="Symbol">∀</a> <a id="9387" class="Symbol">{</a><a id="9388" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#9388" class="Bound">A</a> <a id="9390" class="Symbol">:</a> <a id="9392" class="PrimitiveType">Set</a><a id="9395" class="Symbol">}</a> <a id="9397" class="Symbol">→</a> <a id="9399" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#9388" class="Bound">A</a> <a id="9401" href="https://agda.github.io/agda-stdlib/Data.Sum.Base.html#419" class="Datatype Operator">⊎</a> <a id="9403" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#914" class="Function Operator">¬</a> <a id="9405" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#9388" class="Bound">A</a>{% endraw %}</pre>
As we noted, the law of the excluded middle does not hold in
intuitionistic logic.  However, we can show that it is _irrefutable_,
meaning that the negation of its negation is provable (and hence that
its negation is never provable).
<pre class="Agda">{% raw %}<a id="em-irrefutable"></a><a id="9665" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#9665" class="Function">em-irrefutable</a> <a id="9680" class="Symbol">:</a> <a id="9682" class="Symbol">∀</a> <a id="9684" class="Symbol">{</a><a id="9685" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#9685" class="Bound">A</a> <a id="9687" class="Symbol">:</a> <a id="9689" class="PrimitiveType">Set</a><a id="9692" class="Symbol">}</a> <a id="9694" class="Symbol">→</a> <a id="9696" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#914" class="Function Operator">¬</a> <a id="9698" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#914" class="Function Operator">¬</a> <a id="9700" class="Symbol">(</a><a id="9701" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#9685" class="Bound">A</a> <a id="9703" href="https://agda.github.io/agda-stdlib/Data.Sum.Base.html#419" class="Datatype Operator">⊎</a> <a id="9705" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#914" class="Function Operator">¬</a> <a id="9707" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#9685" class="Bound">A</a><a id="9708" class="Symbol">)</a>
<a id="9710" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#9665" class="Function">em-irrefutable</a> <a id="9725" class="Symbol">=</a> <a id="9727" class="Symbol">λ</a> <a id="9729" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#9729" class="Bound">k</a> <a id="9731" class="Symbol">→</a> <a id="9733" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#9729" class="Bound">k</a> <a id="9735" class="Symbol">(</a><a id="9736" href="https://agda.github.io/agda-stdlib/Data.Sum.Base.html#500" class="InductiveConstructor">inj₂</a> <a id="9741" class="Symbol">(λ</a> <a id="9744" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#9744" class="Bound">x</a> <a id="9746" class="Symbol">→</a> <a id="9748" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#9729" class="Bound">k</a> <a id="9750" class="Symbol">(</a><a id="9751" href="https://agda.github.io/agda-stdlib/Data.Sum.Base.html#475" class="InductiveConstructor">inj₁</a> <a id="9756" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#9744" class="Bound">x</a><a id="9757" class="Symbol">)))</a>{% endraw %}</pre>
The best way to explain this code is to develop it interactively.

    em-irrefutable k = ?

Given evidence `k` that `¬ (A ⊎ ¬ A)`, that is, a function that give a
value of type `A ⊎ ¬ A` returns a value of the empty type, we must fill
in `?` with a term that returns a value of the empty type.  The only way
we can get a value of the empty type is by applying `k` itself, so let's
expand the hole accordingly.

    em-irrefutable k = k ?

We need to fill the new hole with a value of type `A ⊎ ¬ A`. We don't have
a value of type `A` to hand, so let's pick the second disjunct.

    em-irrefutable k = k (inj₂ λ{ x → ? })

The second disjunct accepts evidence of `¬ A`, that is, a function
that given a value of type `A` returns a value of the empty type.  We
bind `x` to the value of type `A`, and now we need to fill in the hole
with a value of the empty type.  Once again, the only way we can get a
value of the empty type is by applying `k` itself, so let's expand the
hole accordingly.

    em-irrefutable k = k (inj₂ λ{ x → k ? })

This time we do have a value of type `A` to hand, namely `x`, so we can
pick the first disjunct.

    em-irrefutable k = k (inj₂ λ{ x → k (inj₁ x) })

There are no holes left! This completes the proof.

The following story illustrates the behaviour of the term we have created.
(With apologies to Peter Selinger, who tells a similar story
about a king, a wizard, and the Philosopher's stone.)

Once upon a time, the devil approached a man and made an offer:
"Either (a) I will give you one billion dollars, or (b) I will grant
you any wish if you pay me one billion dollars.
Of course, I get to choose whether I offer (a) or (b)."

The man was wary.  Did he need to sign over his soul?
No, said the devil, all the man need do is accept the offer.

The man pondered.  If he was offered (b) it was unlikely that he would
ever be able to buy the wish, but what was the harm in having the
opportunity available?

"I accept," said the man at last.  "Do I get (a) or (b)?"

The devil paused.  "I choose (b)."

The man was disappointed but not surprised.  That was that, he thought.
But the offer gnawed at him.  Imagine what he could do with his wish!
Many years passed, and the man began to accumulate money.  To get the
money he sometimes did bad things, and dimly he realised that
this must be what the devil had in mind.
Eventually he had his billion dollars, and the devil appeared again.

"Here is a billion dollars," said the man, handing over a valise
containing the money.  "Grant me my wish!"

The devil took possession of the valise.  Then he said, "Oh, did I say
(b) before?  I'm so sorry.  I meant (a).  It is my great pleasure to
give you one billion dollars."

And the devil handed back to the man the same valise that the man had
just handed to him.

(Parts of the above are adopted from "Call-by-Value is Dual to Call-by-Name",
Philip Wadler, _International Conference on Functional Programming_, 2003.)


#### Exercise `Classical` (stretch)

Consider the following principles.

  * Excluded Middle: `A ⊎ ¬ A`, for all `A`
  * Double Negation Elimination: `¬ ¬ A → A`, for all `A`
  * Peirce's Law: `((A → B) → A) → A`, for all `A` and `B`.
  * Implication as disjunction: `(A → B) → ¬ A ⊎ B`, for all `A` and `B`.
  * De Morgan: `¬ (¬ A × ¬ B) → A ⊎ B`, for all `A` and `B`.

Show that each of these implies all the others.


#### Exercise `Stable` (stretch)

Say that a formula is _stable_ if double negation elimination holds for it.
<pre class="Agda">{% raw %}<a id="Stable"></a><a id="13272" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#13272" class="Function">Stable</a> <a id="13279" class="Symbol">:</a> <a id="13281" class="PrimitiveType">Set</a> <a id="13285" class="Symbol">→</a> <a id="13287" class="PrimitiveType">Set</a>
<a id="13291" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#13272" class="Function">Stable</a> <a id="13298" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#13298" class="Bound">A</a> <a id="13300" class="Symbol">=</a> <a id="13302" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#914" class="Function Operator">¬</a> <a id="13304" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#914" class="Function Operator">¬</a> <a id="13306" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#13298" class="Bound">A</a> <a id="13308" class="Symbol">→</a> <a id="13310" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#13298" class="Bound">A</a>{% endraw %}</pre>
Show that any negated formula is stable, and that the conjunction
of two stable formulas is stable.

## Standard Prelude

Definitions similar to those in this chapter can be found in the standard library.
<pre class="Agda">{% raw %}<a id="13541" class="Keyword">import</a> <a id="13548" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html" class="Module">Relation.Nullary</a> <a id="13565" class="Keyword">using</a> <a id="13571" class="Symbol">(</a><a id="13572" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#464" class="Function Operator">¬_</a><a id="13574" class="Symbol">)</a>
<a id="13576" class="Keyword">import</a> <a id="13583" href="https://agda.github.io/agda-stdlib/Relation.Nullary.Negation.html" class="Module">Relation.Nullary.Negation</a> <a id="13609" class="Keyword">using</a> <a id="13615" class="Symbol">(</a><a id="13616" href="https://agda.github.io/agda-stdlib/Relation.Nullary.Negation.html#688" class="Function">contraposition</a><a id="13630" class="Symbol">)</a>{% endraw %}</pre>

## Unicode

This chapter uses the following unicode.

    ¬  U+00AC  NOT SIGN (\neg)
    ≢  U+2262  NOT IDENTICAL TO (\==n)
