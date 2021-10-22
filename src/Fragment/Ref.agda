{-# OPTIONS --safe --without-K #-}

module Fragment.Ref where

-- Framework code + stdlib imports
open import Prelude

-- Monadic interfaces
open import Interface.MonotoneState

-- Canonical forms
open import Canon.Ref

import Level as L

--
-- A fragment for reference types 
--
module _ where

  open RefCanon
  open Itf Sto

  data RefExprShape ⦃ _ : TRefΣ ≼ σ ⦄ : (Ctx (μ σ) × μ σ) → Set where
    init  : ∀ {Γ t} → RefExprShape (Γ , ref′ t)
    deref  : ∀ {Γ t} → RefExprShape (Γ , t)
    update : ∀ {Γ t} → RefExprShape (Γ , t)

  RefExprΣ : Expressions Sto TRefΣ
  RefExprΣ = RefExprShape ▸ λ where
    (init  {Γ} {t}) → (Γ , t) ∷ [] 
    (deref  {Γ} {t}) → (Γ , ref′ t) ∷ []
    (update {Γ} {t}) → (Γ , ref′ t) ∷ (Γ , t) ∷ []

  module _ (M : Eff Sto)
         ⦃ mon : Monadic M       ⦄
         ⦃ _   : IsStrong mon    ⦄
         ⦃ _   : MonotoneState M ⦄
         where

    module _ {σ} {V : Values Sto σ} where

      open MonotoneState   ⦃...⦄
      open IsStrong        ⦃...⦄

      interpRef :   ⦃ _ : ReferenceVal ⊑ V ⦄
                  → ⦃ IsWeakenable V ⦄
                  → IAlgebra RefExprΣ λ (Γ , t) → ∀[ M (para (out V)) Γ (para (out V) t) ]
      ialg interpRef (init , L.lift (~e ∷ [])) = do
        tm  ← ~e
        loc ← alloc tm
        return (↑ loc)
      ialg interpRef (deref , L.lift (~loc ∷ [])) = do
        loc  ← ~loc
        get (↓ loc)
      ialg interpRef (update {_} {⟨ _ ⟩} , L.lift (~loc ∷ ~v ∷ [])) = do
        v         ← ~v
        (loc , v) ← ~loc          ^ v
        (_   , v) ← put (↓ loc) v ^ v
        return v 

    open Necessary

    Ref : □ (MonadicFragment Sto M) refCanon
    MonadicFragment.exprᵐ   (□.future Ref r) = RefExprΣ
    MonadicFragment.interpᵐ (□.future Ref r) = interpRef ⦃ r ⦄

