{-# OPTIONS --safe --without-K #-}

module Fragment.Maybe where

-- Framework code + stdlib imports
open import Prelude

-- Canonical forms
open import Canon.Maybe

import Level as L

--
-- A fragment for maybe 
-- 
module _ {Ix} ⦃ ix-rel : ∀ {X} → Rel₂ L.0ℓ (Ix X) ⦄  where

  open Necessary
  open Itf Ix

  data MaybeExprShape ⦃ _ : TMaybeΣ ≼ σ ⦄ : μ σ → Set where
    mkjust    : ∀ {t} → MaybeExprShape (maybe′ t)
    mknothing : ∀ {t} → MaybeExprShape (maybe′ t) 
    flatten   : ∀ {t} → MaybeExprShape (maybe′ t)

  MaybeExprΣ : ⦃ TMaybeΣ ≼ σ ⦄ → ISignature _ (μ σ) (μ σ)
  MaybeExprΣ = MaybeExprShape ▸ λ where
    (mkjust {t})  → t ∷ []
    mknothing     → []
    (flatten {t}) → maybe′ (maybe′ t) ∷ []


  module _ {σ} {V : Values Ix σ} where

    interpMaybe : ∀ {Σ}
                  → ⦃ _ : liftVal MaybeVal ⊑ V ⦄
                  → IAlgebra MaybeExprΣ λ t → (para (out V) t) Σ
    ialg interpMaybe (mkjust , L.lift (v ∷ [])) = ↑ (just v)
    ialg interpMaybe (mknothing , _) = ↑ nothing
    ialg interpMaybe (flatten , L.lift (v ∷ [])) =
      case ↓ v of λ where
        nothing  → ↑ nothing
        (just x) → x

  Maybe' : □ (IFragment {Ix}) (liftCanon maybeCanon)
  IFragment.iexpr   (□.future Maybe' _) = MaybeExprΣ
  IFragment.iinterp (□.future Maybe' r) = interpMaybe ⦃ r ⦄
