# Connectives.lagda.md

## Unicode

This chapter uses the following unicode:

    ×  U+00D7  MULTIPLICATION SIGN (\x)
    ⊎  U+228E  MULTISET UNION (\u+)
    ⊤  U+22A4  DOWN TACK (\top)
    ⊥  U+22A5  UP TACK (\bot)
    η  U+03B7  GREEK SMALL LETTER ETA (\eta)
    ₁  U+2081  SUBSCRIPT ONE (\_1)
    ₂  U+2082  SUBSCRIPT TWO (\_2)
    ⇔  U+21D4  LEFT RIGHT DOUBLE ARROW (\<=>)



# Decidable.lagda.md

## Unicode

    ∧  U+2227  LOGICAL AND (\and, \wedge)
    ∨  U+2228  LOGICAL OR (\or, \vee)
    ⊃  U+2283  SUPERSET OF (\sup)
    ᵇ  U+1D47  MODIFIER LETTER SMALL B  (\^b)
    ⌊  U+230A  LEFT FLOOR (\clL)
    ⌋  U+230B  RIGHT FLOOR (\clR)



# Equality.lagda.md

## Unicode

This chapter uses the following unicode:

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



# Induction.lagda.md

## Unicode

This chapter uses the following unicode:

    ∀  U+2200  FOR ALL (\forall, \all)
    ʳ  U+02B3  MODIFIER LETTER SMALL R (\^r)
    ′  U+2032  PRIME (\')
    ″  U+2033  DOUBLE PRIME (\')
    ‴  U+2034  TRIPLE PRIME (\')
    ⁗  U+2057  QUADRUPLE PRIME (\')

Similar to `\r`, the command `\^r` gives access to a variety of
superscript rightward arrows, and also a superscript letter `r`.
The command `\'` gives access to a range of primes (`′ ″ ‴ ⁗`).



# Isomorphism.lagda.md

## Unicode

This chapter uses the following unicode:

    ∘  U+2218  RING OPERATOR (\o, \circ, \comp)
    λ  U+03BB  GREEK SMALL LETTER LAMBDA (\lambda, \Gl)
    ≃  U+2243  ASYMPTOTICALLY EQUAL TO (\~-)
    ≲  U+2272  LESS-THAN OR EQUIVALENT TO (\<~)
    ⇔  U+21D4  LEFT RIGHT DOUBLE ARROW (\<=>)



# Lists.lagda.md

## Unicode

This chapter uses the following unicode:

    ∷  U+2237  PROPORTION  (\::)
    ⊗  U+2297  CIRCLED TIMES  (\otimes, \ox)
    ∈  U+2208  ELEMENT OF  (\in)
    ∉  U+2209  NOT AN ELEMENT OF  (\inn, \notin)



# Naturals.lagda.md

## Unicode

This chapter uses the following unicode:

    ℕ  U+2115  DOUBLE-STRUCK CAPITAL N (\bN)
    →  U+2192  RIGHTWARDS ARROW (\to, \r, \->)
    ∸  U+2238  DOT MINUS (\.-)
    ≡  U+2261  IDENTICAL TO (\==)
    ⟨  U+27E8  MATHEMATICAL LEFT ANGLE BRACKET (\<)
    ⟩  U+27E9  MATHEMATICAL RIGHT ANGLE BRACKET (\>)
    ∎  U+220E  END OF PROOF (\qed)

Each line consists of the Unicode character (`ℕ`), the corresponding
code point (`U+2115`), the name of the character (`DOUBLE-STRUCK CAPITAL N`),
and the sequence to type into Emacs to generate the character (`\bN`).

The command `\r` gives access to a wide variety of rightward arrows.
After typing `\r`, one can access the many available arrows by using
the left, right, up, and down keys to navigate.  The command remembers
where you navigated to the last time, and starts with the same
character next time.  The command `\l` works similarly for left arrows.
In place of left, right, up, and down keys, one may also use control
characters:

    C-b  left (backward one character)
    C-f  right (forward one character)
    C-p  up (to the previous line)
    C-n  down (to the next line)

We write `C-b` to stand for control-b, and similarly.  One can also navigate
left and right by typing the digits that appear in the displayed list.

For a full list of supported characters, use `agda-input-show-translations` with:

    M-x agda-input-show-translations

All the characters supported by `agda-mode` are shown. We write M-x to stand for
typing `ESC` followed by `x`.

If you want to know how you input a specific Unicode character in an agda file,
move the cursor onto the character and use `quail-show-key` with:

    M-x quail-show-key

You'll see a key sequence of the character in mini buffer.
If you run `M-x quail-show-key` on say `∸`, you will see `\.-` for the character.



# Negation.lagda.md

## Unicode

This chapter uses the following unicode:

    ¬  U+00AC  NOT SIGN (\neg)
    ≢  U+2262  NOT IDENTICAL TO (\==n)



# Quantifiers.lagda.md

## Unicode

This chapter uses the following unicode:

    Π  U+03A0  GREEK CAPITAL LETTER PI (\Pi)
    Σ  U+03A3  GREEK CAPITAL LETTER SIGMA (\Sigma)
    ∃  U+2203  THERE EXISTS (\ex, \exists)



# Relations.lagda.md

## Unicode

This chapter uses the following unicode:

    ≤  U+2264  LESS-THAN OR EQUAL TO (\<=, \le)
    ≥  U+2265  GREATER-THAN OR EQUAL TO (\>=, \ge)
    ˡ  U+02E1  MODIFIER LETTER SMALL L (\^l)
    ʳ  U+02B3  MODIFIER LETTER SMALL R (\^r)

The commands `\^l` and `\^r` give access to a variety of superscript
leftward and rightward arrows in addition to superscript letters `l` and `r`.



# BigStep.lagda.md

## Unicode

This chapter uses the following unicode:

    ≈  U+2248  ALMOST EQUAL TO (\~~ or \approx)
    ₑ  U+2091  LATIN SUBSCRIPT SMALL LETTER E (\_e)
    ⊢  U+22A2  RIGHT TACK (\|- or \vdash)
    ⇓  U+21DB  DOWNWARDS DOUBLE ARROW (\d= or \Downarrow)



# Bisimulation.lagda.md

## Unicode

This chapter uses the following unicode:

    †  U+2020  DAGGER (\dag)
    ⁻  U+207B  SUPERSCRIPT MINUS (\^-)
    ¹  U+00B9  SUPERSCRIPT ONE (\^1)



# Confluence.lagda.md

## Unicode

This chapter uses the following unicode:

    ⇛  U+21DB  RIGHTWARDS TRIPLE ARROW (\r== or \Rrightarrow)
    ⁺  U+207A  SUPERSCRIPT PLUS SIGN   (\^+)



# DeBruijn.lagda.md

## Unicode

This chapter uses the following unicode:

    σ  U+03C3  GREEK SMALL LETTER SIGMA (\Gs or \sigma)
    ₀  U+2080  SUBSCRIPT ZERO (\_0)
    ₃  U+20B3  SUBSCRIPT THREE (\_3)
    ₄  U+2084  SUBSCRIPT FOUR (\_4)
    ₅  U+2085  SUBSCRIPT FIVE (\_5)
    ₆  U+2086  SUBSCRIPT SIX (\_6)
    ₇  U+2087  SUBSCRIPT SEVEN (\_7)
    ≠  U+2260  NOT EQUAL TO (\=n)



# Inference.lagda.md

## Unicode

This chapter uses the following unicode:

    ↓  U+2193:  DOWNWARDS ARROW (\d)
    ↑  U+2191:  UPWARDS ARROW (\u)
    ∥  U+2225:  PARALLEL TO (\||)



# Lambda.lagda.md

## Unicode

This chapter uses the following unicode:

    ⇒  U+21D2  RIGHTWARDS DOUBLE ARROW (\=>)
    ƛ  U+019B  LATIN SMALL LETTER LAMBDA WITH STROKE (\Gl-)
    ·  U+00B7  MIDDLE DOT (\cdot)
    ≟  U+225F  QUESTIONED EQUAL TO (\?=)
    —  U+2014  EM DASH (\em)
    ↠  U+21A0  RIGHTWARDS TWO HEADED ARROW (\rr-)
    ξ  U+03BE  GREEK SMALL LETTER XI (\Gx or \xi)
    β  U+03B2  GREEK SMALL LETTER BETA (\Gb or \beta)
    Γ  U+0393  GREEK CAPITAL LETTER GAMMA (\GG or \Gamma)
    ≠  U+2260  NOT EQUAL TO (\=n or \ne)
    ∋  U+220B  CONTAINS AS MEMBER (\ni)
    ∅  U+2205  EMPTY SET (\0)
    ⊢  U+22A2  RIGHT TACK (\vdash or \|-)
    ⦂  U+2982  Z NOTATION TYPE COLON (\:)
    😇  U+1F607  SMILING FACE WITH HALO
    😈  U+1F608  SMILING FACE WITH HORNS

We compose reduction `—→` from an em dash `—` and an arrow `→`.
Similarly for reflexive and transitive closure `—↠`.



# More.lagda.md

## Unicode

This chapter uses the following unicode:

    σ  U+03C3  GREEK SMALL LETTER SIGMA (\Gs or \sigma)
    †  U+2020  DAGGER (\dag)
    ‡  U+2021  DOUBLE DAGGER (\ddag)



# Properties.lagda.md

## Unicode

This chapter uses the following unicode:

    ƛ  U+019B  LATIN SMALL LETTER LAMBDA WITH STROKE (\Gl-)
    Δ  U+0394  GREEK CAPITAL LETTER DELTA (\GD or \Delta)
    β  U+03B2  GREEK SMALL LETTER BETA (\Gb or \beta)
    δ  U+03B4  GREEK SMALL LETTER DELTA (\Gd or \delta)
    μ  U+03BC  GREEK SMALL LETTER MU (\Gm or \mu)
    ξ  U+03BE  GREEK SMALL LETTER XI (\Gx or \xi)
    ρ  U+03B4  GREEK SMALL LETTER RHO (\Gr or \rho)
    ᵢ  U+1D62  LATIN SUBSCRIPT SMALL LETTER I (\_i)
    ᶜ  U+1D9C  MODIFIER LETTER SMALL C (\^c)
    –  U+2013  EM DASH (\em)
    ₄  U+2084  SUBSCRIPT FOUR (\_4)
    ↠  U+21A0  RIGHTWARDS TWO HEADED ARROW (\rr-)
    ⇒  U+21D2  RIGHTWARDS DOUBLE ARROW (\=>)
    ∅  U+2205  EMPTY SET (\0)
    ∋  U+220B  CONTAINS AS MEMBER (\ni)
    ≟  U+225F  QUESTIONED EQUAL TO (\?=)
    ⊢  U+22A2  RIGHT TACK (\vdash or \|-)
    ⦂  U+2982  Z NOTATION TYPE COLON (\:)



# Substitution.lagda.md

## Unicode

This chapter uses the following unicode:

    ⟪  U+27EA  MATHEMATICAL LEFT DOUBLE ANGLE BRACKET (\<<)
    ⟫  U+27EA  MATHEMATICAL RIGHT DOUBLE ANGLE BRACKET (\>>)
    ↑  U+2191  UPWARDS ARROW (\u)
    •  U+2022  BULLET (\bub)
    ⨟  U+2A1F  Z NOTATION SCHEMA COMPOSITION (C-x 8 RET Z NOTATION SCHEMA COMPOSITION)
    〔  U+3014  LEFT TORTOISE SHELL BRACKET (\( option 9 on page 2)
    〕  U+3015  RIGHT TORTOISE SHELL BRACKET (\) option 9 on page 2)



# Untyped.lagda.md

## Unicode

This chapter uses the following unicode:

    ★  U+2605  BLACK STAR (\st)

The `\st` command permits navigation among many different stars;
the one we use is number 7.
