{-# OPTIONS --safe --without-K #-}

module Canon.Bool where

open import Data.Product
open import Data.Bool
open import Data.Vec

open import Core
open import Signature
open import Canon

open import Level as L

module BoolCanon where

  data TBoolShape : Set where bool : TBoolShape
  TBoolΣ = TBoolShape ▹ λ where bool → 0

  bool′ : ⦃ TBoolΣ ≼ σ ⦄ → μ σ
  bool′ = inject (bool , L.lift [])

  open Algebra

  BoolVal : Algebra TBoolΣ Set Set
  alg BoolVal (bool , L.lift []) = Bool

  boolCanon : Canon
  Canon.ty  boolCanon = TBoolΣ
  Canon.val boolCanon = BoolVal

open BoolCanon public
