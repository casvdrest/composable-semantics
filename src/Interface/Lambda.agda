{-# OPTIONS --safe --without-K #-}

module Interface.Lambda where 

open import Relation.Unary                        using (IUniversal ; _⇒_)
open import Relation.Binary                       using (Rel)
open import Relation.Binary.PropositionalEquality
open import Relation.Binary.Structures

open import Core
open import Signature 
open import Structure.Monad
open import Canon
open import Canon.Function
open import MonadicFragment

open import Data.List
open import Data.List.Membership.Propositional
open import Data.Product
open import Data.Vec

import Level as L

{- An interface for function abstractions -} 
module _ (M : Eff Sto) where

  record Lambda : Set₁ where
    field

      -- Construct a closure (function abstraction). Any effects that may occur
      -- under λ-abstraction are postponed until the function is applied
      abstr : ∀ {Γ V s t}  → ∀[  M {σ} V (s ∷ Γ) (V t)
                              ⇒  M     V Γ (closure s t ∈_)
                              ]

      -- Function application 
      apply : ∀ {Γ V s t} → ∀[  (closure s t ∈_)
                             ⇒  V s
                             ⇒  M {σ} V Γ (V t)
                             ]

