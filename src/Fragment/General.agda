{-# OPTIONS --safe --without-K #-}

module Fragment.General where

-- Framework code + stdlib imports
open import Prelude

-- Effect interfaces 
open import Interface.General
open import Interface.Lambda

-- Canonical forms
open import Canon.Function

import Level as L

--
-- A fragment for General recursion
-- 
module _ where 

  open Necessary
  open Itf Sto

  
  data GeneralExprShape ⦃ _ : TFunctionΣ ≼ σ ⦄ : (Ctx (μ σ) × μ σ) → Set where
    fix : ∀ {Γ} {s t : μ σ} → GeneralExprShape (Γ , fun′ s t)

  GeneralExprΣ : Expressions Sto TFunctionΣ
  GeneralExprΣ = GeneralExprShape ▸ λ where
    (fix {Γ} {s} {t}) → (s ∷ fun′ s t ∷ Γ , t) ∷ []

  module _ (M : Eff Sto)
         ⦃ mon : Monadic M ⦄
         ⦃ _   : General M ⦄ 
         where

    module _ {σ} {V : Values Sto σ} where
      open Wk {A = Sto (μ σ)} _⊆_

      open General ⦃...⦄
      

      interpGeneral :   ⦃ _ : FunctionVal ⊑ V ⦄
                      → ⦃ IsWeakenable V      ⦄
                      → IAlgebra GeneralExprΣ λ (Γ , t) → ∀[ M (para (out V)) Γ (para (out V) t) ]
      ialg interpGeneral (fix , L.lift (tm ∷ [])) = do
        clos ← general ↑ tm
        return (↑ clos)


    Rec : □ (MonadicFragment Sto M) funCanon
    MonadicFragment.exprᵐ   (□.future Rec r) = GeneralExprΣ
    MonadicFragment.interpᵐ (□.future Rec r) = interpGeneral ⦃ r ⦄
