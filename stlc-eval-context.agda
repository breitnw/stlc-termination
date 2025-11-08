-- CS 496, HW 7
-- Nicholas Breitling

module stlc-eval-context where

open import stlc-syntax
open import eq

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

-- lemma : evaluation context substitution is commutative
subst-comm : ∀ {Γ τ τsub τsubsub}
  (E1 : [ τsub ] Γ ⊢ τ )
  (E2 : [ τsubsub ] Γ ⊢ τsub)
  (e : Γ ⊢ τsubsub)
  → E1 [ (E2 [ e ]) ] ≡ (E1 [[ E2 ]]) [ e ]
subst-comm E-◻ E2 e = refl
subst-comm (E-s E) E2 e
  rewrite subst-comm E E2 e = refl
subst-comm (E-apl E x) E2 e
  rewrite subst-comm E E2 e = refl
subst-comm (E-apr x E) E2 e
  rewrite subst-comm E E2 e = refl
subst-comm E-rec E [ ez ][ es ] E2 e
  rewrite subst-comm E E2 e = refl

-- alternative definition of evaluation contexts (ternary relation)
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
