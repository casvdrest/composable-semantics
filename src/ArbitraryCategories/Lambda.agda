{-# OPTIONS --safe --without-K #-}

open import Data.Fin
open import Data.Product renaming (_×_ to _×p_)
open import Data.Empty
open import Data.Vec

-------------------------------------------------------------------------------
-- agda-categories imports
--
open import Categories.Category.Core
open import Categories.Monad

open import Categories.Category.BinaryProducts
open import Categories.Category.Cartesian
open import Categories.Category.CartesianClosed.Canonical

open import Categories.Category.Construction.Kleisli

open import Categories.Object.Exponential
open import Categories.Object.Terminal
open import Categories.Object.Product

open import Categories.Functor renaming (id to idᶠ)

open import Data.List
open import Data.List.Membership.Propositional
open import Data.List.Relation.Unary.Any
open import Data.List.Relation.Unary.All

import Categories.Morphism.Reasoning as MR

open import Signature
open import Union

open import Level renaming (suc to sucL)

-------------------------------------------------------------------------------
-- local imports
open import ArbitraryCategories.Base

module ArbitraryCategories.Lambda 
  (𝓒 : Category (sucL 0ℓ) 0ℓ 0ℓ)
  
  (cc : CartesianClosed 𝓒)
  where

  open CartesianClosed cc renaming (curry to λg ; ⟨_,_⟩ to ⟪_,_⟫)
  
  open Terminal
  open IsTerminal 

  open Fragments   𝓒 isCartesian
  open Combinators 𝓒 isCartesian

  open Category 𝓒 renaming (_⇒_ to _⟨⇒⟩_ ; _∘_ to _⟨∘⟩_ )
  open Cartesian isCartesian
 

  -------------------------------------------------------------------------------
  -- Canon

  open _≼_ ⦃...⦄

  module FunCanon where

    data FunTyShape : Set where fun : FunTyShape
    FunTySig = FunTyShape ▹ λ where fun → 2

    funCanon = canon FunTySig λ where .alg (fun , lift (s ∷ t ∷ [])) → t ^ s

    funᵀ : ∀ {σ} → ⦃ FunTySig ≼ σ ⦄ → μ σ → μ σ → μ σ
    funᵀ ⦃ x ⦄ s t = ⟨ (inj (fun , Level.lift (s ∷ t ∷ []))) ⟩

  -------------------------------------------------------------------------------
  -- Fragment

  module Lambda where

    open FunCanon

    module _ {c : Canon} ⦃ p : funCanon ⊑ c ⦄ where

      open Canon c

      data LambdaExprShape : Ctx ×p Ty → Set where
        var : ∀ {Γ t} → t ∈ Γ → LambdaExprShape (Γ , t)
        abs : ∀ {Γ s t}       → LambdaExprShape (Γ , funᵀ s t)
        app : ∀ {Γ} {s t : _} → LambdaExprShape (Γ , t)

      LambdaExprSig : ISignature _ (Ctx ×p Ty) (Ctx ×p Ty)
      LambdaExprSig .Shapeᴵ = LambdaExprShape
      LambdaExprSig .Indices (var x) = []
      LambdaExprSig .Indices (abs {Γ} {s} {t}) = (s ∷ Γ , t) ∷ []
      LambdaExprSig .Indices (app {Γ} {s} {t}) = (Γ , funᵀ s t) ∷ (Γ , s) ∷ []

      evalLambda : IAlgebra LambdaExprSig λ (Γ , t) → Env Γ ⟨⇒⟩ Values t 
      evalLambda .ialg (var x , _) = fetch x
      evalLambda .ialg (abs   , lift (ff ∷ [])) with f ← ff 
        = ↑ ⟨∘⟩ λg (f ⟨∘⟩ ⟪ π₂ , π₁ ⟫ ) 
      evalLambda .ialg (app   , lift (ff ∷ fx ∷ [])) with f ← ff | x ← fx
        = eval ⟨∘⟩ ⟪ ↓ ⟨∘⟩ f , x ⟫ 

    LambdaFragment : □ Fragment funCanon
    □.future LambdaFragment = fragment LambdaExprSig evalLambda
