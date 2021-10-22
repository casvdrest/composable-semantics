{-# OPTIONS --safe --without-K #-}

module Interface.Reader where

open import Relation.Unary                        using (IUniversal ; _⇒_)
import      Relation.Unary.Closure.Base as Clos
open import Relation.Binary                       using (Rel)
open import Relation.Binary.PropositionalEquality
open import Relation.Binary.Structures

open import Core
open import Signature
open import Structure.Monad

open import Data.List
open import Data.List.Relation.Unary.All
open import Data.List.Relation.Binary.Sublist.Propositional

open import Function
open import Level

open import MonadicFragment
open import Canon.Function

open import Box

module _ Ix ⦃ ix-rel : ∀ {X} → Rel₂ _ (Ix X) ⦄ (M : Eff Ix) where
  
  record Reader : Set₁ where

    field 
      --
      -- Returns the current environment 
      -- 
      ask   : ∀ {Γ V} → ∀[ M V Γ (Env (μ σ) V Γ) ]

      -- 
      -- Run a given computation under a transformed environment
      -- 
      local : ∀ {σ} {Γ Γ′ V} t →  
                let open Clos {A = (Ix (μ σ))} (Rel₂.R ix-rel) in

                ∀[  □ (Env _ V Γ ⇒ Env _ V Γ′)
                 ⇒  M {σ} V Γ′ (V t)
                 ⇒  M V Γ  (V t)
                 ]

  
