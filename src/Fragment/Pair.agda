{-# OPTIONS --safe --without-K #-}

module Fragment.Pair where

-- Framework code + stdlib imports
open import Prelude

-- Canonical forms
open import Canon.Pair

import Level as L

-- 
-- A fragment for products 
--
module _ {Ix} ⦃ ix-rel : ∀ {X} → Rel₂ L.0ℓ (Ix X) ⦄ where

  open Necessary
  open Itf Ix
  
  data PairExprShape ⦃ _ : TPairΣ ≼ σ ⦄ : μ σ → Set where
    mkpair : ∀ {s t} → PairExprShape (pair′ s t )
    fst    : ∀ {s t : μ σ} → PairExprShape s
    snd    : ∀ {s t : μ σ} → PairExprShape t 

  PairExprΣ : ⦃ TPairΣ ≼ σ ⦄ → ISignature _ (μ σ) (μ σ)
  PairExprΣ = PairExprShape ▸ λ where
    (mkpair {s} {t}) → s ∷ t ∷ []
    (fst {s} {t})    → pair′ s t ∷ []
    (snd {s} {t})    → pair′ s t ∷ []

  module _ {σ} {V : Values Ix σ} where

    interpPair : ∀ {Σ}
                 → ⦃ _ : liftVal PairVal ⊑ V ⦄
                 → IAlgebra PairExprΣ λ t → (para (out V) t) Σ
    ialg interpPair (mkpair , L.lift (x ∷ y  ∷ [])) = ↑ (x , y)
    ialg interpPair (fst    , L.lift (v ∷ []))      = proj₁ (↓ v)
    ialg interpPair (snd    , L.lift (v ∷ []))      = proj₂ (↓ v) 

  Pair : □ (IFragment {Ix}) (liftCanon pairCanon)
  IFragment.iexpr   (□.future Pair r) = PairExprΣ
  IFragment.iinterp (□.future Pair r) = interpPair ⦃ r ⦄
