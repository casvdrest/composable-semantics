{-# OPTIONS --safe --without-K #-}

module Fragment.Arith where

-- Framework code + stdlib imports
open import Prelude

-- Canonical forms
open import Canon.Nat

import Level as L

--
-- A fragment arithmetic expressions
-- 
module _ where 

  open Necessary

  data ArithExprShape ⦃ _ : TNatΣ ≼ σ ⦄ : (μ σ) → Set where
    num : ℕ → ArithExprShape (nat′) 
    add :     ArithExprShape (nat′)

  ArithExprΣ : ⦃ TNatΣ ≼ σ ⦄ → ISignature _ (μ σ) (μ σ)
  ArithExprΣ = ArithExprShape ▸ λ where
    (num n) → []
    (add  ) → nat′ ∷ nat′ ∷ []

  module _ {Ix} where

    module _ {σ} {V : Values Ix σ} where
      
      interpArith : ∀ {Σ} → ⦃ _ : liftVal NatVal ⊑ V ⦄ → IAlgebra ArithExprΣ λ t → para (out V) t Σ
      ialg interpArith (num n , _)                 = ↑ n
      ialg interpArith (add , L.lift (n ∷ m ∷ [])) = ↑ (↓ n + ↓ m)

    open Necessary

    Arith : □ (IFragment {Ix}) (icanon _ (liftVal NatVal))
    IFragment.iexpr   (□.future Arith x) = ArithExprΣ
    IFragment.iinterp (□.future Arith r) = interpArith ⦃ r ⦄
