-- CS 496, HW 7
-- Nicholas Breitling

module stlc-syntax where

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
