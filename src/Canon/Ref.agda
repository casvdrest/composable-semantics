{-# OPTIONS --safe --without-K #-}

module Canon.Ref where

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

module RefCanon where

  data TRefShape : Set where ref : TRefShape
  TRefΣ = TRefShape ▹ λ where ref → 1

  ref′ : ⦃ TRefΣ ≼ σ ⦄ → (t : μ σ) → μ σ
  ref′ t = inject (ref , L.lift (t ∷ []))

  open Algebra

  ReferenceVal : Values Sto TRefΣ 
  alg (out ReferenceVal) (ref , lift ((t , _) ∷ [])) Σ = value t ∈ Σ
  
  refCanon : ICanon Sto
  ICanon.ity  refCanon = TRefΣ 
  ICanon.ival refCanon = ReferenceVal 

open RefCanon public
