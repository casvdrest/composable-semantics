{-# OPTIONS --safe --without-K #-}

module Fragment.Boolean where

-- Framework code + stdlib imports
open import Prelude

-- Canonical forms
open import Canon.Bool

import Level as L

--
-- A fragment for boolean expressions
--
module _ {Ix : Set → Set} ⦃ ix-rel : ∀ {X} → Rel₂ L.0ℓ (Ix X) ⦄ where

  open Necessary

  data BoolExprShape ⦃ _ : TBoolΣ ≼ σ ⦄ : μ σ → Set where
    boolean : Bool → BoolExprShape bool′
    conj    : BoolExprShape bool′
    ite     : (t : μ σ) → BoolExprShape t  

  BoolExprΣ : ⦃ TBoolΣ ≼ σ ⦄ → ISignature _ (μ σ) (μ σ)
  BoolExprΣ = BoolExprShape ▸ (λ where
    (boolean _)  → []
    conj         → bool′ ∷ bool′ ∷ []
    (ite t)      → bool′ ∷ t ∷ t ∷ [])

  module _ {σ} {V : Values Ix σ} where 
      
    interpBool : ∀ {Σ} → ⦃ _ : liftVal BoolVal ⊑ V ⦄ → IAlgebra BoolExprΣ λ t → (para (out V) t) Σ
    ialg interpBool (boolean b , _)                    = ↑ b
    ialg interpBool (conj  , L.lift (x ∷ y ∷ []))      = ↑ (↓ x ∧ ↓ y)
    ialg interpBool (ite t , L.lift (c ∷ t' ∷ e ∷ [])) = if ↓ c then t' else e  

  open Necessary 

  Boolean : □ (IFragment {Ix}) (liftCanon boolCanon)
  IFragment.iexpr   (□.future Boolean r) = BoolExprΣ
  IFragment.iinterp (□.future Boolean r) = interpBool ⦃ r ⦄
