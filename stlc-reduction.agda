-- CS 496, HW 7
-- Nicholas Breitling

module stlc-reduction where

open import stlc-syntax
open import stlc-eval-context
open import eq

-- extension lemma: if every type in the environment Γ is also in Δ, then the
-- two environments extended by τnew will also contain the same types
ext : ∀ {Γ Δ}
  → (∀ {τ} → Γ ∋ τ → Δ ∋ τ)
    ----------------------------------------------
  → (∀ {τ τnew} → (Γ , τnew) ∋ τ → (Δ , τnew) ∋ τ)
ext ρ Z = Z
ext ρ (S x) = S (ρ x)

-- renaming: if every type in Γ is also in Δ, then any term that is typeable
-- under Γ has the same type under Δ
rename : ∀ {Γ Δ}
  → (∀ {τ} → Γ ∋ τ → Δ ∋ τ)
    -----------------------
  → (∀ {τ} → Γ ⊢ τ → Δ ⊢ τ)
rename ρ (` x) = ` (ρ x)
rename ρ (λ' τ1 e) = λ' τ1 (rename (ext ρ) e)
rename ρ (ap e1 e2) = (ap (rename ρ e1) (rename ρ e2))
rename ρ z = z
rename ρ (s e) = s (rename ρ e)
rename ρ rec e [ ez ][ es ]
  = rec rename ρ e [ rename ρ ez ][ rename (ext (ext ρ)) es ]

-- extension lemma: given a map from variables in Γ to terms in Δ, we can
-- construct a map from variables in Γ extended to terms in Δ similarly extended
exts : ∀ {Γ Δ}
  → (∀ {τ} → Γ ∋ τ → Δ ⊢ τ)
    ----------------------------------------------
  → (∀ {τ τnew} → (Γ , τnew) ∋ τ → (Δ , τnew) ⊢ τ)
exts σ Z = ` Z
exts σ (S x) = rename S (σ x) -- get the term from Δ and rename it for Δ , τnew

-- substitution into expressions: if variables in one context map onto terms in
-- another, then terms in the first context map to terms in the second
subst : ∀ {Γ Δ}
  → (∀ {τ} → Γ ∋ τ → Δ ⊢ τ)
    -----------------------
  → (∀ {τ} → Γ ⊢ τ → Δ ⊢ τ)
subst σ (` x) = σ x
subst σ (λ' τ1 e) = λ' τ1 (subst (exts σ) e)
subst σ (ap e1 e2) = ap (subst σ e1) (subst σ e2)
subst σ z = z
subst σ (s e) = s (subst σ e)
subst σ rec e [ ez ][ es ]
  = rec subst σ e [ subst σ ez ][ subst (exts (exts σ)) es ]

-- map for single substitution
σ-single : ∀ {Γ τsub} → Γ ⊢ τsub → ∀ {τ} → (Γ , τsub) ∋ τ → Γ ⊢ τ
σ-single esub Z = esub
σ-single esub (S x) = ` x

-- single substitution
_[:=_] : ∀ {Γ τ τsub}
  → (Γ , τsub) ⊢ τ
  → Γ ⊢ τsub
  -------------
  → Γ ⊢ τ
_[:=_] {Γ} {τ} {τsub} e esub = subst {Γ , τsub} {Γ} (σ-single esub) {τ} e
  -- where
  -- if we have a well-typed term in Γ extended with τsub, and we have a term of
  -- type τsub to substitute, then we can get a well-typed term in Γ by
  -- substituting all the de Bruijn indices that are zero
  -- σ : ∀ {τ} → (Γ , τsub) ∋ τ → Γ ⊢ τ
  -- σ Z = esub
  -- σ (S x) = ` x

-- reduction relation
infix 2 _-→_
data _-→_ : ∀ {Γ τ} → (Γ ⊢ τ) → (Γ ⊢ τ) → Set where
  β-v : ∀ {Γ τ τarg τret} {E : [ τret ] Γ ⊢ τ} {e : (Γ , τarg) ⊢ τret} {v : Γ ⊢ τarg}
    → Value v
      -------------------------------------------
    → E [ (ap (λ' τarg e) v) ] -→ E [ e [:= v ] ]

  rec-zero : ∀ {Γ τ τret}
      { E : [ τret ] Γ ⊢ τ }
      { ez : Γ ⊢ τret }
      { es : ((Γ , tnat) , τret) ⊢ τret }
      ------------------------------------
    → E [ rec z [ ez ][ es ] ] -→ E [ ez ]

  -- we need to rename when substituting since we're taking the environment
  -- from ((Γ , tnat) , τret) to (Γ , tnat), but the expression we're
  -- substituting we have types under Γ alone, not (Γ , tnat).
  rec-succ : ∀ {Γ τ τret}
      { E : [ τret ] Γ ⊢ τ }
      { ez : Γ ⊢ τret }
      { es : ((Γ , tnat) , τret) ⊢ τret }
      { v : Γ ⊢ tnat }
    → Value v
      -------------------------------------------------------------------
    → E [ rec (s v) [ ez ][ es ] ] -→ E [ es [:= rename S (rec v [ ez ][ es ]) ]
                                             [:= v ] ]

-- context replacement lemma, this one was surprisingly a huge pain
crl : ∀ {Γ τsub τ} {e : Γ ⊢ τsub} {e' : Γ ⊢ τsub}
  → (E : [ τsub ] Γ ⊢ τ)
  → e -→ e'
    -------------------
  → E [ e ] -→ E [ e' ]
crl {e = e} {e' = e'} E-out (β-v {Γ} {τ} {τarg} {τret} {E-in} {e-body} {v} V)
  rewrite subst-comm E-out E-in (ap (λ' τarg e-body) v)
        | subst-comm E-out E-in (e-body [:= v ])
        = β-v V
crl {e = e} {e' = e'} E-out (rec-zero {Γ} {τ} {τret} {E-in} {ez} {es})
  rewrite subst-comm E-out E-in (rec z [ ez ][ es ])
        | subst-comm E-out E-in (ez)
        = rec-zero
crl {e = e} {e' = e'} E-out (rec-succ {Γ} {τ} {τret} {E-in} {ez} {es} {v} V)
  rewrite subst-comm E-out E-in (rec (s v) [ ez ][ es ])
        | subst-comm E-out E-in (es [:= rename S (rec v [ ez ][ es ]) ] [:= v ])
        = rec-succ V

-- equivalent reduction relation for alternative evaluation context representation
infix 2 _m-→_
data _m-→_ : ∀ {Γ τ} → (Γ ⊢ τ) → (Γ ⊢ τ) → Set where
  β-v : ∀ {Γ τ τarg τret elhs erhs}
      {E : [ τret ] Γ ⊢ τ}
      {e : (Γ , τarg) ⊢ τret}
      {v : Γ ⊢ τarg}
    → Value v
    → elhs matches E [ ap (λ' τarg e) v ]
    → erhs matches E [ e [:= v ] ]
      -------------------------------------------
    → elhs m-→ erhs

  rec-zero : ∀ {Γ τ τret elhs erhs}
      { E : [ τret ] Γ ⊢ τ }
      { ez : Γ ⊢ τret }
      { es : ((Γ , tnat) , τret) ⊢ τret }
    → elhs matches E [ rec z [ ez ][ es ] ]
    → erhs matches E [ ez ]
      ------------------------------------
    → elhs m-→ erhs

  rec-succ : ∀ {Γ τ τret elhs erhs}
      { E : [ τret ] Γ ⊢ τ }
      { ez : Γ ⊢ τret }
      { es : ((Γ , tnat) , τret) ⊢ τret }
      { v : Γ ⊢ tnat }
    → Value v
    → elhs matches E [ rec (s v) [ ez ][ es ] ]
    → erhs matches E [ es [:= rename S (rec v [ ez ][ es ]) ] [:= v ] ]
      -------------------------------------------------------------------
    → elhs m-→ erhs

-- lemma: if e1 -→ e2, then e1 m-→ e2
red-def-equiv : ∀ {Γ τ} {e1 : Γ ⊢ τ} {e2 : Γ ⊢ τ} → e1 -→ e2 → e1 m-→ e2
red-def-equiv (β-v V) = β-v V (ctx-def-equiv refl) (ctx-def-equiv refl)
red-def-equiv rec-zero = rec-zero (ctx-def-equiv refl) (ctx-def-equiv refl)
red-def-equiv (rec-succ V) =  rec-succ V (ctx-def-equiv refl) (ctx-def-equiv refl)
