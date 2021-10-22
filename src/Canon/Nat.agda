{-# OPTIONS --safe --without-K #-}

module Canon.Nat where

open import Data.Product
open import Data.Nat
open import Data.Vec

open import Core
open import Signature
open import Canon

open import Level as L


module NatCanon where

  data TNatShape : Set where nat : TNatShape
  TNatΣ = TNatShape ▹ λ where nat → 0

  nat′ : ⦃ TNatΣ ≼ σ ⦄ → μ σ
  nat′ = inject (nat , L.lift [])

  open Algebra

  NatVal : Algebra TNatΣ Set Set
  alg NatVal (nat , L.lift []) = ℕ

  natCanon : Canon
  Canon.ty natCanon = TNatΣ
  Canon.val natCanon = NatVal

open NatCanon public
