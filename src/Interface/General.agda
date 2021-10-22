{-# OPTIONS --safe --without-K #-}

open import Box

module Interface.General where

open import Relation.Unary                        using (IUniversal ; _⇒_)
open import Relation.Binary                       using (Rel)
open import Relation.Binary.PropositionalEquality
open import Relation.Binary.Structures

open import Core
open import Signature 
open import Structure.Monad
open import MonadicFragment

open import Canon.Function

open import Data.List
open import Data.List.Membership.Propositional
open import Data.Product
open import Data.Vec

import Level as L


open FunCanon

{- An interface for general recursion -} 
module _ (M : Eff Sto) where

  record General : Set₁ where
    field general : ∀ {Γ V s t}
                    → ⦃ _ : TFunctionΣ ≼ σ ⦄
                    → ∀[ (closure s t ∈_) ⇒ V (fun′ s t) ]
                    → ∀[  M {σ} V (s ∷ fun′ s t ∷ Γ) (V t)
                       ⇒  M     V Γ (closure s t ∈_)
                       ] 
