{-# OPTIONS --safe --without-K #-}

module Fragment.Exception where

-- Framework code + stdlib imports
open import Prelude

-- Effect interfaces 
open import Interface.Except

import Level as L

--
-- A fragment for unchecked exceptions
--
module _ {Ix : Set → Set} ⦃ ix-rel : ∀ {X} → Rel₂ L.0ℓ (Ix X) ⦄ where

  open Itf Ix
  open Necessary

  data ExceptExprShape {σ : Signature L.0ℓ} : (Ctx (μ σ) × μ σ) → Set where 
    error : ∀ {Γ} → (t : μ σ) → ExceptExprShape (Γ , t)
    try   : ∀ {Γ} → (t : μ σ) → ExceptExprShape (Γ , t)

  ExceptExprΣ : Expressions Ix σ
  ExceptExprΣ = ExceptExprShape ▸ λ where
    (error _) → []
    (try {Γ = Γ} t) → (Γ , t) ∷ (Γ , t) ∷ []

  module _ (M : Eff Ix)
           ⦃ mon : Monadic   M ⦄
           ⦃ _   : Exception Ix M ⦄
           where

    module _ {σ} (V : Values Ix σ) where

      open Exception  ⦃...⦄
      
      interpExcept : IAlgebra ExceptExprΣ λ (Γ , t) → ∀[ M (para (out V)) Γ (para (out V) t) ]
      ialg interpExcept (error t , L.lift [])             = throw t
      ialg interpExcept (try t , L.lift (tm₁ ∷ tm₂ ∷ [])) = try-with t tm₁ tm₂

    Except : ∀[ □ (MonadicFragment Ix M) ]
    MonadicFragment.exprᵐ   (□.future Except {c′} r) = ExceptExprΣ {σ = ICanon.ity c′}
    MonadicFragment.interpᵐ (□.future Except {c′} r) = interpExcept (ICanon.ival c′) 
