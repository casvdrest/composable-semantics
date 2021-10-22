{-# OPTIONS --safe --without-K #-}

open import Box

module Interface.Except (Ix : Set → Set) ⦃ _ : ∀ {X} → Rel₂ _ (Ix X) ⦄ where 

open import Relation.Unary                        using (IUniversal ; _⇒_)
open import Relation.Binary                       using (Rel)
open import Relation.Binary.PropositionalEquality
open import Relation.Binary.Structures

open import Core
open import Signature
open import Structure.Monad
open import MonadicFragment

open import Data.List
open import Data.List.Relation.Unary.All

open import Function
open import Level

module _ (M : Eff Ix) where
  
  record Exception : Set₁ where

    field
      throw : ∀ {Γ V} → (t : μ σ) → ∀[ M V Γ (V t) ]

      try-with : ∀ {Γ V} → (t : μ σ) → ∀[ M V Γ (V t) ⇒ M V Γ (V t) ⇒ M V Γ (V t) ]
