-- CS 496, HW 7
-- Nicholas Breitling

module stlc-progress where

open import stlc-syntax
open import stlc-reduction
open import stlc-eval-context

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
