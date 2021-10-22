{-# OPTIONS --safe --without-K #-}

module Interface.MonotoneState where

open import Relation.Unary                        using (IUniversal ; _⇒_ ; U)
open import Relation.Binary                       using (Rel)
open import Relation.Binary.PropositionalEquality
open import Relation.Binary.Structures

open import Core
open import Signature
open import Structure.Monad
open import MonadicFragment

open import Data.Product
open import Data.Vec
open import Data.List
open import Data.List.Relation.Unary.All
open import Data.List.Membership.Propositional

import Level as L

module _ (M : Eff Sto) where


  record MonotoneState : Set₁ where
    field
    
      get   : ∀ {Γ V t} → ∀[  (value t ∈_)
                           ⇒  M {σ} V Γ (V t)
                           ]
      
      put   : ∀ {Γ V t} → ∀[  (value t ∈_)
                           ⇒  V t
                           ⇒  M {σ} V Γ U
                           ]

      
      alloc : ∀ {Γ V t} → ∀[  V t
                           ⇒  M {σ} V Γ (value t ∈_)
                           ]

  
