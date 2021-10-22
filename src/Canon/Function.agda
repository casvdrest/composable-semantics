{-# OPTIONS --safe --without-K #-}

module Canon.Function where

open import Data.Product
open import Data.List
open import Data.Vec
open import Data.List.Relation.Unary.All
open import Data.List.Membership.Propositional
open import Data.List.Relation.Binary.Sublist.Propositional

open import Core
open import Signature
open import Canon

open import Level as L

module FunCanon where

  data TFunctionShape : Set where fun : TFunctionShape
  TFunctionΣ = TFunctionShape ▹ λ where fun → 2

  fun′ : ⦃ TFunctionΣ ≼ σ ⦄ → (s t : μ σ) → μ σ
  fun′ s t = inject (fun , L.lift (s ∷ t ∷ []))

  open Algebra

  FunctionVal : Values Sto TFunctionΣ 
  alg (out FunctionVal) (fun , lift ((s , _) ∷ (t , _) ∷ [])) Σ = closure s t ∈ Σ

  funCanon : ICanon Sto
  ICanon.ity  funCanon = TFunctionΣ
  ICanon.ival funCanon = FunctionVal

open FunCanon public
