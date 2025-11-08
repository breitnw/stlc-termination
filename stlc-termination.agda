-- CS 496, HW 7
-- Nicholas Breitling

module stlc-termination where

open import stlc-syntax
open import stlc-reduction
open import stlc-eval-context
open import eq
open import empty
open import product

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

-- Helper data for dealing with evaluation contexts
data Redex : ∀ {Γ τ} → Γ ⊢ τ → Set where
  R-ap : ∀ {Γ τbody τarg} {e : (Γ , τarg) ⊢ τbody} {v : Γ ⊢ τarg}
    → Value v
      ------------
    → Redex (ap (λ' τarg e) v)

  R-rec-z : ∀ {Γ τret}
      { ez : Γ ⊢ τret }
      { es : ((Γ , tnat) , τret) ⊢ τret }
      ------------------------------------
    → Redex rec z [ ez ][ es ]

  R-rec-succ : ∀ {Γ τret}
      { ez : Γ ⊢ τret }
      { es : ((Γ , tnat) , τret) ⊢ τret }
      { v : Γ ⊢ tnat }
    → Value v
      ------------------------------------
    → Redex rec (s v) [ ez ][ es ]

subst-unique-τsub : ∀ {Γ τ τsub1 τsub2} {e : Γ ⊢ τ} {E1 : [ τsub1 ] Γ ⊢ τ} {E2 : [ τsub2 ] Γ ⊢ τ} {esub1 : Γ ⊢ τsub1} {esub2 : Γ ⊢ τsub2}
  → e matches E1 [ esub1 ]
  → e matches E2 [ esub2 ]
  → Redex esub1
  → Redex esub2
    ------------------------
  → τsub1 ≡ τsub2
subst-unique-τsub = {!!}

subst-unique-esub : ∀ {Γ τ τsub} {e : Γ ⊢ τ} {E1 E2 : [ τsub ] Γ ⊢ τ} {esub1 esub2 : Γ ⊢ τsub}
  → e matches E1 [ esub1 ]
  → e matches E2 [ esub2 ]
  → Redex esub1
  → Redex esub2
    ------------------------
  → esub1 ≡ esub2
subst-unique-esub {e = ` x} subst-◻ subst-◻ Resub1 Resub2 = refl
subst-unique-esub {e = λ' τ1 e} subst-◻ subst-◻ Resub1 Resub2 = refl
subst-unique-esub {e = ap e1 e2} subst-◻ subst-◻ Resub1 Resub2 = refl
subst-unique-esub {e = ap e1 e2} subst-◻ (subst-apl emE2) Resub1 Resub2 = {!Resub2!}
subst-unique-esub {e = ap e1 e2} subst-◻ (subst-apr emE2 V) Resub1 Resub2 = {!!}
subst-unique-esub {e = ap e1 e2} (subst-apl emE1) emE2 Resub1 Resub2 = {!!}
subst-unique-esub {e = ap e1 e2} (subst-apr emE1 V) emE2 Resub1 Resub2 = {!!}
subst-unique-esub {e = z} subst-◻ subst-◻ Resub1 Resub2 = refl
subst-unique-esub {e = s e} subst-◻ subst-◻ Resub1 Resub2 = refl
subst-unique-esub {e = s e} (subst-◻) (subst-s emE2) Resub1 Resub2 = {!!}
subst-unique-esub {e = s e} (subst-s emE1) emE2 Resub1 Resub2 = {!!}
subst-unique-esub {e = rec e [ e₁ ][ e₂ ]} emE1 emE2 Resub1 Resub2 = {!!}

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

-- lemma : redex only decomposes into E-◻ and itself
-- redex-decompose : ∀ {Γ τ τsub} {e1 : Γ ⊢ τ} {E : Γ ⊢ τ} → Redex e1 → e1 matches E [ esub ]

-- helper lemma: only one valid reduction path for redexes
Redex-m-→≡ : ∀ {Γ τ} {e1 e2 e3 : Γ ⊢ τ} → Redex e1 → (e1 m-→ e2) → (e1 m-→ e3) → e2 ≡ e3
Redex-m-→≡ (R-ap x) e1-→e2 e1-→e3 = {!e1-→e2!}
Redex-m-→≡ R-rec-z e1-→e2 e1-→e3 = {!!}
Redex-m-→≡ (R-rec-succ x) e1-→e2 e1-→e3 = {!!}

-- helper lemma: only one valid reduction path
m-→≡ : ∀ {Γ τ} {e1 e2 e3 : Γ ⊢ τ} → (e1 m-→ e2) → (e1 m-→ e3) → e2 ≡ e3
m-→≡ (β-v {τret = τret1} V1 e1mE1 e2mE1) (β-v {τret = τret2} V2 e1mE2 e3mE2)
  rewrite subst-unique-τsub {τsub1 = τret1} {τsub2 = τret2} e1mE1 e1mE2 {!!} {!!} = {!subst-unique-esub e1mE1 e1mE2!}
m-→≡ (β-v V e1mE e2mE) (rec-zero x x₁) = {!!}
m-→≡ (β-v V e1mE e2mE) (rec-succ x x₁ x₂) = {!!}
m-→≡ (rec-zero x x₁) e1m-→e3 = {!!}
m-→≡ (rec-succ x x₁ x₂) e1m-→e3 = {!!}

-- lemma: only one valid reduction path
-→≡ : ∀ {Γ τ} {e1 e2 e3 : Γ ⊢ τ} → (e1 -→ e2) → (e1 -→ e3) → e2 ≡ e3
-→≡ e1-→e2 e1-→e3 = m-→≡ (red-def-equiv e1-→e2) (red-def-equiv e1-→e3)

-- !!!!! TODO uncomment (temporarily removed because it's slow)
-- helper lemma: if we can take a step, we're not a value
Vm-/→ : ∀ {Γ τ} {e1 e2 : Γ ⊢ τ} {ℓ} → (e1 m-→ e2) → Value e1 → ⊥ {ℓ}
Vm-/→ = {!!}
-- Vm-/→ (β-v V (subst-s em) (subst-s e'm)) (V-suc Ve1)
--   = Vm-/→ (β-v V em e'm) Ve1
-- Vm-/→ (rec-zero (subst-s em) (subst-s e'm)) (V-suc Ve1)
--   = Vm-/→ (rec-zero em e'm) Ve1
-- Vm-/→ (rec-succ V (subst-s em) (subst-s e'm)) (V-suc Ve1)
--   = Vm-/→ (rec-succ V em e'm) Ve1

-- lemma: if we can take a step, we're not a value
V-/→ : ∀ {Γ τ} {e1 e2 : Γ ⊢ τ} {ℓ} → (e1 -→ e2) → Value e1 → ⊥ {ℓ}
V-/→ e1-→e2 Ve1 = Vm-/→ (red-def-equiv e1-→e2) Ve1

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
