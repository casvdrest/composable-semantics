{-# OPTIONS --safe --without-K #-}

module Canon.Pair where

open import Data.Product
open import Data.Vec

open import Core
open import Signature
open import Canon

open import Level as L

module PairCanon where

  data TPairShape : Set where pair : TPairShape
  TPairΣ = TPairShape ▹ λ where pair → 2

  pair′ : ⦃ TPairΣ ≼ σ ⦄ → (s t : μ σ) → μ σ
  pair′ s t = inject (pair , L.lift (s ∷ t ∷ []))

  open Algebra

  PairVal : Algebra TPairΣ Set Set
  alg PairVal (pair , L.lift (Vs ∷ Vt ∷ [])) = Vs × Vt 

  pairCanon : Canon
  Canon.ty  pairCanon = TPairΣ
  Canon.val pairCanon = PairVal

open PairCanon public
