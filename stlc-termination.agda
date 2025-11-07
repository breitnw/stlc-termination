-- CS 496, HW 7
-- Nicholas Breitling

module _ where

open import eq
open import nat
open import level
open import empty
open import bool
open import product

-- Data ------------------------------------------------------------------------

-- types
data Type : Set where
  tnat : Type
  _⇒_ : Type → Type → Type

-- typing environments
data Env : Set where
  ∅ : Env
  _,_ : Env → Type → Env

-- lookup judgement (de Bruijn indices)
data _∋_ : Env → Type → Set where
  Z : ∀ {Γ τ}
      -----------
    → (Γ , τ) ∋ τ

  S : ∀ {Γ τ1 τ2}
    → Γ ∋ τ1
      -----------
    → (Γ , τ2) ∋ τ1

-- terms and the typing judgement
data _⊢_ : Env → Type → Set where
  ` : ∀ {Γ τ}
    → Γ ∋ τ
      -----
    → Γ ⊢ τ

  λ' : ∀ {Γ τ2}
    → (τ1 : Type)
    → (Γ , τ1) ⊢ τ2
      ----------
    → Γ ⊢ (τ1 ⇒ τ2)

  ap : ∀ {Γ τ1 τ2}
    → Γ ⊢ (τ1 ⇒ τ2)
    → Γ ⊢ τ1
      -----------
    → Γ ⊢ τ2

  z : ∀ {Γ}
      -------
    → Γ ⊢ tnat

  s : ∀ {Γ}
    → Γ ⊢ tnat
      --------
    → Γ ⊢ tnat

  -- x_pre is bound to #1
  -- y_rec is bound to #0
  rec_[_][_] : ∀ {Γ τ}
    → Γ ⊢ tnat
    → Γ ⊢ τ
    → ((Γ , tnat) , τ) ⊢ τ
      --------------------
    → Γ ⊢ τ

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

-- values
data Value : ∀ {Γ τ} → Γ ⊢ τ → Set where
  V-λ' : ∀ {Γ τ1 τ2} {e : (Γ , τ1) ⊢ τ2}
      ------------
    → Value (λ' τ1 e)

  V-z : ∀ {Γ}
      -------------
    → Value (z {Γ})

  V-suc : ∀ {Γ} {v : Γ ⊢ tnat}
    → Value v
      -----------
    → Value (s v)

-- evaluation contexts
-- the type in brackets is the type of the expression substituted into the
-- context. i know this is a strange way of writing things, but I couldn't
-- figure out a better way...
data [_]_⊢_ : Type → Env → Type → Set where
  -- the type of the substituted expression is the type of the hole
  E-◻ : ∀ {Γ τsub}
      --------------
    → [ τsub ] Γ ⊢ τsub

  E-s : ∀ {Γ τsub}
    → [ τsub ] Γ ⊢ tnat
      --------------
    → [ τsub ] Γ ⊢ tnat

  E-apl : ∀ {Γ τsub τ1 τ2}
    → [ τsub ] Γ ⊢ (τ1 ⇒ τ2)
    → Γ ⊢ τ1
      --------------------
    → [ τsub ] Γ ⊢ τ2

  E-apr : ∀ {Γ τsub τ1 τ2} {v : Γ ⊢ (τ1 ⇒ τ2)}
    → Value v
    → [ τsub ] Γ ⊢ τ1
      --------------------
    → [ τsub ] Γ ⊢ τ2

  E-rec_[_][_] : ∀ {Γ τsub τ}
    → [ τsub ] Γ ⊢ tnat
    → Γ ⊢ τ
    → ((Γ , tnat) , τ) ⊢ τ
      --------------------
    → [ τsub ] Γ ⊢ τ

-- substitution into evaluation contexts
_[_] : ∀ {Γ τ τsub} → [ τsub ] Γ ⊢ τ → Γ ⊢ τsub → Γ ⊢ τ
E-◻ [ esub ] = esub
E-s E [ esub ] = s (E [ esub ])
E-apl E e [ esub ] = ap (E [ esub ]) e
E-apr {Γ} {τsub} {τ1} {τ2} {v} _ E [ esub ] = ap v (E [ esub ])
E-rec E [ ez ][ es ] [ esub ] = rec (E [ esub ]) [ ez ][ es ]

-- example
ex : ∀ {Γ} → (E-s E-◻) [ s (z {Γ}) ] ≡ (s (s z))
ex = refl

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

-- PROVING PRESERVATION --------------------------------------------------------

-- Preservation comes for free with the intrinsically typed de Bruijn
-- representation! The -→ relation only accepts a pair of expressions that have
-- the same type in some environment Γ.

-- PROVING PROGRESS ------------------------------------------------------------

-- substitute a context in another context
_[[_]] : ∀ {Γ τ τsub τsubsub}
  → [ τsub ] Γ ⊢ τ
  → [ τsubsub ] Γ ⊢ τsub
  → [ τsubsub ] Γ ⊢ τ
E-◻ [[ Esub ]] = Esub
E-s E [[ Esub ]] = E-s (E [[ Esub ]])
E-apl E e [[ Esub ]] = E-apl (E [[ Esub ]]) e
E-apr V E [[ Esub ]] = E-apr V (E [[ Esub ]])
E-rec E [ ez ][ es ] [[ Esub ]] = E-rec (E [[ Esub ]]) [ ez ][ es ]

-- and then we gotta prove a lemma about it
subst-comm : ∀ {Γ τ τsub τsubsub}
  (E1 : [ τsub ] Γ ⊢ τ )
  (E2 : [ τsubsub ] Γ ⊢ τsub)
  (e : Γ ⊢ τsubsub)
  → E1 [ E2 [ e ] ] ≡ (E1 [[ E2 ]]) [ e ]
subst-comm E-◻ E2 e = refl
subst-comm (E-s E) E2 e
  rewrite subst-comm E E2 e = refl
subst-comm (E-apl E x) E2 e
  rewrite subst-comm E E2 e = refl
subst-comm (E-apr x E) E2 e
  rewrite subst-comm E E2 e = refl
subst-comm E-rec E [ ez ][ es ] E2 e
  rewrite subst-comm E E2 e = refl

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

-- definition of progress: well-typed terms can either take a step or are done
data Progress {τ} (e1 : ∅ ⊢ τ) : Set where
  step : ∀ {e2 : ∅ ⊢ τ}
    → e1 -→ e2
      ----------
    → Progress e1

  done :
      Value e1
      ----------
    → Progress e1

-- progress lemma
progress : ∀ {τ} → (e : ∅ ⊢ τ) → Progress e
progress (` ())
progress (λ' _ _) = done V-λ'
progress (ap e1 e2) with progress e1
...    | step e1-→e1' = step (crl (E-apl _ _) e1-→e1')
...    | done V-λ' with progress e2
...        | step e2-→e2' = step (crl (E-apr V-λ' _) e2-→e2')
...        | done V    = step (β-v {E = E-◻} V)
progress z = done V-z
progress (s e) with progress e
...    | step e-→e' = step (crl (E-s _) e-→e')
...    | done V     = done (V-suc V)
progress rec e [ ez ][ es ] with progress e
...    | step e-→e' = step (crl (E-rec _ [ _ ][ _ ]) e-→e')
...    | done V with e | V
...         | z        | V-z         = step (rec-zero {E = E-◻})
...         | s v      | V-suc Vprev = step (rec-succ {E = E-◻} Vprev)

-- HOMEWORK 6 ==================================================================

-- Alternative (relation) definition of evaluation contexts --------------------

data _matches_[_] : ∀ {Γ τ1 τ2} → Γ ⊢ τ1 → [ τ2 ] Γ ⊢ τ1 → Γ ⊢ τ2 → Set where
  subst-◻ : ∀ {Γ τ} {esub : Γ ⊢ τ} → esub matches E-◻ [ esub ]
  subst-s : ∀ {Γ τ} {e : Γ ⊢ tnat} {E : [ τ ] Γ ⊢ tnat} { esub : Γ ⊢ τ }
    → e matches E [ esub ] → (s e) matches (E-s E) [ esub ]
  subst-apl : ∀ {Γ τ τsub τarg}
    {e : Γ ⊢ (τarg ⇒ τ)} {E : [ τsub ] Γ ⊢ (τarg ⇒ τ)} {esub : Γ ⊢ τsub} {earg : Γ ⊢ τarg}
    → e matches E [ esub ]
    → (ap e earg) matches E-apl E earg [ esub ]
  subst-apr : ∀ {Γ τ τsub τarg}
    {e : Γ ⊢ τarg} {E : [ τsub ] Γ ⊢ τarg} {esub : Γ ⊢ τsub} {v : Γ ⊢ (τarg ⇒ τ)}
    → e matches E [ esub ]
    → (V : Value v)
    → (ap v e) matches E-apr V E [ esub ]
  subst-rec : ∀ {Γ τ τsub}
    {E : [ τsub ] Γ ⊢ tnat} {ez : Γ ⊢ τ} {es : ((Γ , tnat) , τ) ⊢ τ} {e : Γ ⊢ tnat} {esub : Γ ⊢ τsub}
    → e matches E [ esub ]
    → rec e [ ez ][ es ] matches E-rec E [ ez ][ es ] [ esub ]

-- lemma: if we have an instance of the "matches" relation, then e is
-- equivalent to E [ esub ]
ctx-def-equiv : ∀ {Γ τ τsub} {e : Γ ⊢ τ} {E : [ τsub ] Γ ⊢ τ} {esub : Γ ⊢ τsub}
  → e ≡ E [ esub ]
  → e matches E [ esub ]
ctx-def-equiv {E = E-◻} refl = subst-◻
ctx-def-equiv {E = E-s E} refl = subst-s (ctx-def-equiv refl)
ctx-def-equiv {E = E-apl E e} refl = subst-apl (ctx-def-equiv refl)
ctx-def-equiv {E = E-apr e E} refl = subst-apr (ctx-def-equiv refl) e
ctx-def-equiv {E = E-rec E [ e1 ][ e2 ]} refl = subst-rec (ctx-def-equiv refl)

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

-- Normalization ---------------------------------------------------------------

data ⇓ {Γ τ} (e1 : Γ ⊢ τ) : Set where
  ⇓val :
      Value e1
      --------
    → ⇓ e1

  ⇓step : ∀ {e2 : Γ ⊢ τ}
    → e1 -→ e2
    → ⇓ e2
      --------
    → ⇓ e1

{-# NO_POSITIVITY_CHECK #-}
data SN : ∀ {Γ τ} → (e : Γ ⊢ τ) → Set where
  SNnat : {e : ∅ ⊢ tnat}
    → ⇓ e
      ---------
    → SN e

  SNfun : ∀ {τ1 τ2} {e : ∅ ⊢ (τ1 ⇒ τ2)}
    → ⇓ e
    → (∀ {earg : ∅ ⊢ τ1} → SN earg → SN (ap e earg))
      ----------------------------------
    → SN e

-- data Redex : ∀ {Γ τ} → Γ ⊢ τ → Set where
--   R-ap : ∀ {τarg e v}
--     → Value v
--       ------------
--     → Redex (ap (λ' τarg e) v)

  -- V-z : ∀ {Γ}
  --     -------------
  --   → Value (z {Γ})

  -- V-suc : ∀ {Γ} {v : Γ ⊢ tnat}
  --   → Value v
  --     -----------
  --   → Value (s v)

-- subst-unique-esub : ∀ {Γ τ τsub} {e : Γ ⊢ τ} {E1 E2 : [ τsub ] Γ ⊢ τ} {esub1 esub2 : Γ ⊢ τsub}
--   → e matches E1 [ esub1 ]
--   → e matches E2 [ esub2 ]
--     ------------------------
--   → esub1 ≡ esub2
-- subst-unique-esub {e = ` x} subst-◻ subst-◻ = refl
-- subst-unique-esub {e = λ' τ1 e} subst-◻ subst-◻ = refl
-- subst-unique-esub {e = ap e1 e2} subst-◻ subst-◻ = refl
-- subst-unique-esub {e = ap e1 e2} subst-◻ (subst-apl emE2) = {!!}
-- subst-unique-esub {e = ap e1 e2} subst-◻ (subst-apr emE2 V) = {!!}
-- subst-unique-esub {e = ap e1 e2} (subst-apl emE1) emE2 = {!!}
-- subst-unique-esub {e = ap e1 e2} (subst-apr emE1 V) emE2 = {!!}
-- subst-unique-esub {e = z} subst-◻ subst-◻ = refl
-- subst-unique-esub {e = s e} subst-◻ subst-◻ = refl
-- subst-unique-esub {e = s e} (subst-◻) (subst-s emE2) = {!!}
-- subst-unique-esub {e = s e} (subst-s emE1) emE2 = {!!}
-- subst-unique-esub {e = rec e [ e₁ ][ e₂ ]} emE1 emE2 = {!!}

-- lemma: expression can only match one evaluation context
-- subst-unique-E : ∀ {Γ τ τsub1 τsub2} {e : Γ ⊢ τ} {E1 : [ τsub1 ] Γ ⊢ τ} {E2 : [ τsub2 ] Γ ⊢ τ} {esub1 esub2 : Γ ⊢ τsub}
--   → e matches E1 [ esub1 ]
--   → e matches E2 [ esub2 ]
--     ------------------------
--   → E1 ≡ E2
-- subst-unique-E {e = ` x} subst-◻ subst-◻ = refl
-- subst-unique-E {e = λ' τ1 e} subst-◻ subst-◻ = refl
-- subst-unique-E {e = ap e1 e2} subst-◻ subst-◻ = refl
-- subst-unique-E {e = ap e1 e2} subst-◻ (subst-apl emE2) = {!!}
-- subst-unique-E {e = ap e1 e2} subst-◻ (subst-apr emE2 V) = {!!}
-- subst-unique-E {e = ap e1 e2} (subst-apl emE1) emE2 = {!!}
-- subst-unique-E {e = ap e1 e2} (subst-apr emE1 V) emE2 = {!!}
-- subst-unique-E {e = z} subst-◻ subst-◻ = refl
-- subst-unique-E {e = s e} subst-◻ subst-◻ = refl
-- subst-unique-E {e = s e} (subst-◻) (subst-s emE2) = {!!}
-- subst-unique-E {e = s e} (subst-s emE1) emE2 = {!!}
-- subst-unique-E {e = rec e [ e₁ ][ e₂ ]} emE1 emE2 = {!!}

-- helper lemma: only one valid reduction path
m-→≡ : ∀ {Γ τ} {e1 e2 e3 : Γ ⊢ τ} → (e1 m-→ e2) → (e1 m-→ e3) → e2 ≡ e3
m-→≡ (β-v V e1mE1 e2mE1) (β-v V1 e1mE2 e3mE2)
  = {!subst-unique-esub e1mE1 ?!}
m-→≡ (β-v V e1mE e2mE) (rec-zero x x₁) = {!!}
m-→≡ (β-v V e1mE e2mE) (rec-succ x x₁ x₂) = {!!}
m-→≡ (rec-zero x x₁) e1m-→e3 = {!!}
m-→≡ (rec-succ x x₁ x₂) e1m-→e3 = {!!}

-- lemma: only one valid reduction path
-→≡ : ∀ {Γ τ} {e1 e2 e3 : Γ ⊢ τ} → (e1 -→ e2) → (e1 -→ e3) → e2 ≡ e3
-→≡ e1-→e2 e1-→e3 = m-→≡ (red-def-equiv e1-→e2) (red-def-equiv e1-→e3)

-- helper lemma: if we can take a step, we're not a value
Vm-/→ : ∀ {Γ τ} {e1 e2 : Γ ⊢ τ} {ℓ} → (e1 m-→ e2) → Value e1 → ⊥ {ℓ}
Vm-/→ (β-v V e1 e2) = {!!}
Vm-/→ (rec-zero e1 e2) = {!!}
Vm-/→ (rec-succ V e1 e2) = {!!}

-- lemma: if we can take a step, we're not a value
V-/→ : ∀ {Γ τ} {e1 e2 : Γ ⊢ τ} {ℓ} → (e1 -→ e2) → Value e1 → ⊥ {ℓ}
V-/→ e1-→e2 Ve1 = Vm-/→ (red-def-equiv e1-→e2) Ve1

-- it's getting incredibly nasty

-- lemma: SN preserved by conversion (forward)
SN-→ : ∀ {τ} {e1 : ∅ ⊢ τ} {e2 : ∅ ⊢ τ} → (e1 -→ e2) → SN e1 → SN e2
SN-→ e1-→e2 (SNnat ⇓e1) with ⇓e1
... | ⇓val V = ⊥-elim (V-/→ e1-→e2 V)
... | ⇓step e1-→e3 ⇓e3 rewrite -→≡ e1-→e2 e1-→e3 = SNnat ⇓e3
SN-→ e1-→e2 (SNfun ⇓e1 SNearg→SNap-earg) with ⇓e1
... | ⇓val V = ⊥-elim (V-/→ e1-→e2 V)
... | ⇓step e1-→e3 ⇓e3 rewrite -→≡ e1-→e2 e1-→e3
    = SNfun ⇓e3 (λ {earg} SNearg → SN-→ (crl (E-apl E-◻ earg) e1-→e3)
                                        (SNearg→SNap-earg SNearg))

-- lemma: SN preserved by conversion (backward)
SN←- : ∀ {τ} {e1 : ∅ ⊢ τ} {e2 : ∅ ⊢ τ} → (e1 -→ e2) → SN e2 → SN e1
SN←- e1-→e2 (SNnat ⇓e2) = SNnat (⇓step e1-→e2 ⇓e2)
SN←- e1-→e2 (SNfun ⇓e2 SNearg→SNap-earg)
  = SNfun (⇓step e1-→e2 ⇓e2)
          (λ {earg} SNearg → SN←- (crl (E-apl E-◻ earg) e1-→e2)
                                  (SNearg→SNap-earg SNearg))

-- reflexive and transitive closure
infix 2 _-→*_
data _-→*_ {Γ τ} : (Γ ⊢ τ) → (Γ ⊢ τ) → Set where
  _∎ : (e : Γ ⊢ τ)
      -------
    → e -→* e

  step-→ : {e1 e2 e3 : Γ ⊢ τ}
    → e2 -→* e3
    → e1 -→ e2
      ---------
    → e1 -→* e3

-- lemma: SN preserved by repeated conversion (forward)
SN-→* : ∀ {τ} {e1 : ∅ ⊢ τ} {e2 : ∅ ⊢ τ} → (e1 -→* e2) → SN e1 → SN e2
SN-→* (_ ∎) SNe1 = SNe1
SN-→* (step-→ e2-→*e3 e1-→e2) SNe1 = SN-→* e2-→*e3 (SN-→ e1-→e2 SNe1)

-- lemma: SN preserved by repeated conversion (backward)
SN*←- : ∀ {τ} {e1 : ∅ ⊢ τ} {e2 : ∅ ⊢ τ} → (e1 -→* e2) → SN e2 → SN e1
SN*←- (_ ∎) SNe2 = SNe2
SN*←- (step-→ e2-→*e3 e1-→e2) SNe3 = SN←- e1-→e2 (SN*←- e2-→*e3 SNe3)

-- context replacement lemma for the reflexive and transitive closure
crl* : ∀ {Γ τsub τ} {e : Γ ⊢ τsub} {e' : Γ ⊢ τsub}
  → (E : [ τsub ] Γ ⊢ τ)
  → e -→* e'
    -------------------
  → E [ e ] -→* E [ e' ]
crl* E (_ ∎) = (E [ _ ]) ∎
crl* E (step-→ e2-→*e3 e1-→e2) = step-→ (crl* E e2-→*e3) (crl E e1-→e2)

-- γ substitutions
data Subst : Set where
  ∅ : Subst
  _[x:=_] : ∀ {τ} → Subst → ∅ ⊢ τ → Subst

data _⊨_ : Subst → Env → Set where
  nil :
      -----
      ∅ ⊨ ∅

  cons : ∀ {Γ τ γ} {v : ∅ ⊢ τ}
    → (SN v) → γ ⊨ Γ
      --------------
    → (γ [x:= v ]) ⊨ (Γ , τ)

-- map for mass substitution
σ-mass : ∀ {Γ τ} → (γ : Subst) → γ ⊨ Γ → (Γ ∋ τ → ∅ ⊢ τ)
σ-mass (γ [x:= v ]) (cons _ _) Z = v
σ-mass (γ [x:= v ]) (cons _ Γ⊨γ) (S X) = σ-mass γ Γ⊨γ X

-- mass substitution
_[γ:=_]_ : ∀ {Γ τ}
  → Γ ⊢ τ
  → (γ : Subst)
  → γ ⊨ Γ
  -------------
  → ∅ ⊢ τ
_[γ:=_]_ {Γ} {τ} e γ γ⊨Γ = subst (σ-mass γ γ⊨Γ) e

-- lemma: successor normalizes
⇓suc : ∀ {Γ} {e : Γ ⊢ tnat} → ⇓ e → ⇓ (s e)
⇓suc (⇓val V) = ⇓val (V-suc V)
⇓suc (⇓step e1-→e2 ⇓e2) = ⇓step (crl (E-s E-◻) e1-→e2) (⇓suc ⇓e2)

-- lemma: can extract value and reduction sequence from ⇓
⇓∃val : ∀ {Γ τ} {e : Γ ⊢ τ} → ⇓ e → Σ (Γ ⊢ τ) (λ v → Value v × (e -→* v))
⇓∃val {e = e} (⇓val V) = e , V , e ∎
⇓∃val (⇓step e1-→e2 ⇓e2) with ⇓∃val ⇓e2
... | v , V , e2-→*v = v , V , step-→ e2-→*v e1-→e2

-- lemma: SN implies ⇓
SN→⇓ : ∀ {τ} {e : ∅ ⊢ τ} → SN e → ⇓ e
SN→⇓ (SNnat ⇓e) = ⇓e
SN→⇓ (SNfun ⇓e _) = ⇓e

-- thing : ∀ {τ Γ Δ} {e : Γ ⊢ τ}
--     {σ1 : ∀ {τmap} → Γ ∋ τmap → Δ ⊢ τmap}
--     {σ2 : ∀ {τmap} → Γ ∋ τmap → Δ ⊢ τmap}
--   → subst σ1 e ≡ subst σ2 e
--   → (τnew : Type)
--     -------------------------------------
--   → subst (exts σ1) (rename {Δ = Γ , τnew} S e) ≡ subst (exts σ2) (rename {Δ = Γ , τnew} S e)
-- thing = {!!}

-- lemma: mass substitution is the same as single substitution of the first
-- element and then mass substitution of the rest extended by 1
subst≡ : ∀ {Γ τ τsub γ} {v : ∅ ⊢ τsub}
  → (e : (Γ , τsub) ⊢ τ)
  → (γ⊨Γ : γ ⊨ Γ)
  → (SNv : SN v)
    ----------------------------------------------------------------------------
  → e [γ:= γ [x:= v ] ] (cons SNv γ⊨Γ) ≡ (subst (exts (σ-mass γ γ⊨Γ)) e [:= v ])
subst≡ (` Z) γ⊨Γ SNv = refl
subst≡ (` (S X)) (cons SNnext γ⊨Γ) SNv = {!!}
subst≡ {Γ} {τ} {τsub} {γ} {v} (λ' τ1 e) γ⊨Γ SNv = {!!}
  where
  help : (subst (exts (σ-mass (γ [x:= v ]) (cons SNv γ⊨Γ))) e) ≡ (subst (exts (σ-single v)) (subst (exts (exts (σ-mass γ γ⊨Γ))) e))
  help = {!thing !}
subst≡ (ap e1 e2) γ⊨Γ SNv
  rewrite subst≡ e1 γ⊨Γ SNv
        | subst≡ e2 γ⊨Γ SNv = refl
subst≡ z γ⊨Γ SNv = refl
subst≡ (s e) γ⊨Γ SNv rewrite subst≡ e γ⊨Γ SNv = refl
subst≡ rec e [ e1 ][ e2 ] γ⊨Γ SNv
  rewrite subst≡ e γ⊨Γ SNv
        | subst≡ e1 γ⊨Γ SNv
        -- | subst≡ e2 (cons _ (cons _ γ⊨Γ)) SNv
        = {!subst≡ e2 (cons _ (cons _ γ⊨Γ)) ?!}

subst≡2 : ∀ {Γ τ τsub1 τsub2 γ} {v1 : ∅ ⊢ τsub1} {v2 : ∅ ⊢ τsub2}
  → (e : ((Γ , τsub1) , τsub2) ⊢ τ)
  → (γ⊨Γ : γ ⊨ Γ)
  → (SNv1 : SN v1)
  → (SNv2 : SN v2)
    ----------------------------------------------------------------------------
  → e [γ:= (γ [x:= v1 ]) [x:= v2 ] ] (cons SNv2 (cons SNv1 γ⊨Γ)) ≡ (subst (exts (exts (σ-mass γ γ⊨Γ))) e [:= rename S v2 ] [:= v1 ])
subst≡2 = {!!}

-- lemma: if a term is SN without substitution, then it is SN with substitution

-- lemma: every typed term is good
good : ∀ {Γ τ γ}
  → (e : Γ ⊢ τ) → (γ⊨Γ : γ ⊨ Γ)
    ---------------------------
  → SN (e [γ:= γ ] γ⊨Γ)
good (` Z) (cons SNv γ⊨Γ) = SNv
good (` (S X)) (cons SNv γ⊨Γ) = good (` X) γ⊨Γ
good z _ = SNnat (⇓val V-z)
good {γ = γ} (s e) γ⊨Γ with good e γ⊨Γ
... | SNnat ⇓e = SNnat (⇓suc ⇓e)
good (ap e earg) γ⊨Γ with good e γ⊨Γ | good earg γ⊨Γ
... | SNfun ⇓e SNearg→SNap-earg | SNearg = SNearg→SNap-earg SNearg
good {Γ = Γ} {γ = γ} (λ' τ1 e) γ⊨Γ = SNfun (⇓val V-λ') f
  where
  f : {earg : ∅ ⊢ τ1} → SN earg → SN (ap (λ' τ1 e [γ:= γ ] γ⊨Γ) earg)
  f SNearg with ⇓∃val (SN→⇓ SNearg)
  ... | v , V , earg-→*v =
    let
      SNv : SN v
      SNv = SN-→* earg-→*v SNearg
      extγ⊨ : (γ [x:= v ]) ⊨ (Γ , τ1)
      extγ⊨ = cons SNv γ⊨Γ
      SNesubst : SN (e [γ:= γ [x:= v ] ] extγ⊨)
      SNesubst = good e extγ⊨
      SNapv : SN (ap (λ' τ1 e [γ:= γ ] γ⊨Γ) v)
      SNapv = SN←- (β-v {E = E-◻} V) (cong-pred SN (subst≡ e γ⊨Γ SNv) SNesubst)
    in SN*←- (crl* (E-apr (V-λ') E-◻) earg-→*v) SNapv
good {Γ = Γ} {γ = γ} rec e [ ez ][ es ] γ⊨Γ with ⇓∃val (SN→⇓ (good e γ⊨Γ))
... | ve , Ve , e-→*ve = let
    x = rec-v-normalizes {ez = ez} {es = es} γ⊨Γ Ve
    ez-subst = ez [γ:= γ ] γ⊨Γ
    es-subst = subst (exts (exts (σ-mass γ γ⊨Γ))) es
  in SN*←- (crl* (E-rec E-◻ [ ez-subst ][ es-subst ]) e-→*ve) x
  where
  rec-v-normalizes : ∀ {Γ γ τ} {v : ∅ ⊢ tnat} {ez : Γ ⊢ τ} {es : ((Γ , tnat) , τ) ⊢ τ}
    → (γ⊨Γ : γ ⊨ Γ)
    → Value v
    → SN (rec v [ ez [γ:= γ ] γ⊨Γ ][ subst (exts (exts (σ-mass γ γ⊨Γ))) es ])
  rec-v-normalizes {γ = γ} {ez = ez} {es = es} γ⊨Γ V-z = let
      ez-subst = ez [γ:= γ ] γ⊨Γ
      es-subst = subst (exts (exts (σ-mass γ γ⊨Γ))) es
      SNez-subst = good ez γ⊨Γ
    in SN←- (rec-zero {E = E-◻} {ez = ez-subst} {es = es-subst}) SNez-subst
  rec-v-normalizes {Γ} {γ} {_} {s v} {ez} {es} γ⊨Γ (V-suc V) = let
      ez-subst = ez [γ:= γ ] γ⊨Γ
      es-subst = subst (exts (exts (σ-mass γ γ⊨Γ))) es
      SNrec : SN rec v [ ez-subst ][ es-subst ]
      SNrec = rec-v-normalizes {ez = ez} {es = es} γ⊨Γ V
      SNv : SN v
      SNv = SNnat (⇓val V)
      extγ⊨ : ((γ [x:= v ]) [x:= rec v [ ez-subst ][ es-subst ] ]) ⊨ ((Γ , tnat) , _)
      extγ⊨ = cons SNrec (cons SNv γ⊨Γ)
      SNes-mass-subst = good es extγ⊨
      SNes-mixed-subst = cong-pred SN (subst≡2 es γ⊨Γ SNv SNrec) SNes-mass-subst
    in SN←- (rec-succ {E = E-◻} {ez = ez-subst} {es = es-subst} V) SNes-mixed-subst
