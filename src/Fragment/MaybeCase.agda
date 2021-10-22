{-# OPTIONS --safe --without-K #-}

module Fragment.MaybeCase where

-- Framework code + stdlib imports
open import Prelude

-- Monadic interfaces
open import Interface.Reader

-- Canonical forms
open import Canon.Maybe

import Level as L

--
-- A fragment for maybe case
--
module _ {Ix} ⦃ ix-rel : ∀ {X} → Rel₂ L.0ℓ (Ix X) ⦄ where

  open Itf Ix
  open Necessary

  data MaybeCaseExprShape ⦃ _ : TMaybeΣ ≼ σ ⦄ : Ctx (μ σ) × μ σ → Set where
    mcase : ∀ {Γ} {s t : μ σ} → MaybeCaseExprShape (Γ , t)

  MaybeCaseExprΣ : ⦃ TMaybeΣ ≼ σ ⦄ → ISignature _ (Ctx (μ σ) × μ σ) (Ctx (μ σ) × μ σ)
  MaybeCaseExprΣ = MaybeCaseExprShape ▸ λ where
    (mcase {Γ} {s} {t}) → (Γ , maybe′ s) ∷ (Γ , t) ∷ (s ∷ Γ , t) ∷ []


  module _ (M : Eff Ix)
         ⦃ mon : Monadic   M ⦄
         ⦃ _   : Reader Ix M ⦄
         where

    open Reader ⦃...⦄

    module _ {σ} {V : Values Ix σ} where

      interpMaybeCase :    ⦃ _ : liftVal MaybeVal ⊑ V ⦄
                        →  ⦃ IsWeakenable V           ⦄
                        → IAlgebra MaybeCaseExprΣ λ (Γ , t) → ∀[ M (para (out V)) Γ (para (out V) t) ]
      ialg (interpMaybeCase ⦃ w ⦄) (mcase {s = s} {t = t} , L.lift (v~ ∷ n~ ∷ j~ ∷ [])) = do
        v ← v~
        case ↓ v of λ where
          nothing  → n~
          (just  x) → local t (λ σ nv → wk σ {s} x ∷ nv) j~

    MaybeCase : □ (MonadicFragment Ix M) (liftCanon maybeCanon)
    MonadicFragment.exprᵐ   (□.future MaybeCase r) = MaybeCaseExprΣ
    MonadicFragment.interpᵐ (□.future MaybeCase r) = interpMaybeCase ⦃ r ⦄
