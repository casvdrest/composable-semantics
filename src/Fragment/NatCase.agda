{-# OPTIONS --safe --without-K #-}

module Fragment.NatCase where

-- Framework code + stdlib imports
open import Prelude

-- Monadic interfaces
open import Interface.Reader

-- Canonical forms
open import Canon.Nat

import Level as L

--
-- A fragment for natcase  
--
module _ {Ix} ⦃ ix-rel : ∀ {X} → Rel₂ _ (Ix X) ⦄ where 

  open Necessary
  open Itf Ix
  
  data NatCaseExprShape ⦃ _ : TNatΣ ≼ σ ⦄ : (Ctx (μ σ) × μ σ) → Set where
    natcase : ∀ {Γ} t → NatCaseExprShape (Γ , t) 

  NatCaseExprΣ : ⦃ TNatΣ ≼ σ ⦄ → ISignature _ (Ctx (μ σ) × μ σ) (Ctx (μ σ) × μ σ)
  NatCaseExprΣ = NatCaseExprShape ▸ λ where
    (natcase {Γ} t) → (Γ , nat′) ∷ (Γ , t) ∷ (nat′ ∷ Γ , t) ∷ []

  module _ (M : Eff Ix) ⦃ mon : Monadic   M ⦄ ⦃ _   : Reader Ix M ⦄  where

    module _ {V : Values Ix σ} where

      open Reader ⦃...⦄
      
      interpNatCase :   ⦃ _ : liftVal NatVal ⊑ V ⦄
                      → IAlgebra NatCaseExprΣ λ (Γ , t) → ∀[ M (para (out V)) Γ (para (out V) t) ]
      ialg interpNatCase (natcase t , L.lift (n~ ∷ z~ ∷ s~ ∷ [])) = do
        n ← n~
        case ↓ n of λ where
          zero    → z~
          (suc n) → local t (λ _ nv → ↑ n ∷ nv) s~
          
    NatCase : □ (MonadicFragment Ix M) (liftCanon natCanon)
    MonadicFragment.exprᵐ   (□.future NatCase _) = NatCaseExprΣ
    MonadicFragment.interpᵐ (□.future NatCase r) = interpNatCase ⦃ r ⦄

