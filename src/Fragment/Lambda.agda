{-# OPTIONS --safe --without-K #-}

module Fragment.Lambda where

-- Framework code + stdlib imports
open import Prelude

-- Effect interfaces 
open import Interface.Reader
open import Interface.Lambda

-- Canonical forms
open import Canon.Function

import Level as L

--
-- A fragment for variables, λ-abstraction, and application
-- 
module _ where 

  open Necessary
  open Itf Sto

  data LambdaExprShape ⦃ _ : TFunctionΣ ≼ σ ⦄ : (Ctx (μ σ) × μ σ) → Set where 
    var : ∀ {Γ t} → t ∈ Γ    → LambdaExprShape (Γ , t)
    abs : ∀ {Γ s t}          → LambdaExprShape (Γ , fun′ s t)
    app : ∀ {Γ} {s t : μ σ}  → LambdaExprShape (Γ , t)
  
  LambdaExprΣ : Expressions Sto TFunctionΣ
  LambdaExprΣ = LambdaExprShape ▸ λ where
    (var x)           → []
    (abs {Γ} {s} {t}) → (s ∷ Γ , t) ∷ []
    (app {Γ} {s} {t}) → (Γ , fun′ s t) ∷ (Γ , s) ∷ []

  module _ (M : Eff Sto)
         ⦃ mon : Monadic     M   ⦄
         ⦃ _   : IsStrong    mon ⦄
         ⦃ _   : Reader Sto  M   ⦄
         ⦃ _   : Lambda      M   ⦄
         where

    module _ {σ} {V : Values Sto σ} where
    
      open Wk {A = Sto (μ σ)} _⊆_

      open Reader   ⦃...⦄
      open Lambda   ⦃...⦄
      open IsStrong ⦃...⦄
      
      interpLambda :  ⦃ IsWeakenable V      ⦄
                      → ⦃ _ : FunctionVal ⊑ V ⦄
                      →  IAlgebra LambdaExprΣ λ (Γ , t) → ∀[ M (fold V) Γ (fold V t) ]
      ialg interpLambda (var x , _) = do
        nv ← ask
        return (lookupᵃ nv x)
      ialg interpLambda (abs , L.lift (tm ∷ [])) = do
        clos ← abstr tm
        return (↑ clos)
      ialg interpLambda (app , L.lift (tm₁ ∷ tm₂ ∷ [])) = do
        v₁ ← tm₁
        (v₂ , v₁) ← tm₂ ^ v₁
        apply (↓ v₁) v₂

    Fun : □ (MonadicFragment _ M) funCanon
    exprᵐ   (□.future Fun r)        = LambdaExprΣ 
    interpᵐ (□.future Fun r) ⦃ wk ⦄ = interpLambda ⦃ wk ⦄ ⦃ r ⦄
