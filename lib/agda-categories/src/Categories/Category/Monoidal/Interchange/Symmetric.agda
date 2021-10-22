{-# OPTIONS --without-K --safe #-}

open import Categories.Category using (Category; module Commutation)
open import Categories.Category.Monoidal.Core using (Monoidal)
open import Categories.Category.Monoidal.Symmetric using (Symmetric)

-- Extra identities that hold only for symmetric monoidal categories.

module Categories.Category.Monoidal.Interchange.Symmetric
  {o ℓ e} {C : Category o ℓ e} {M : Monoidal C} (S : Symmetric M) where

open import Data.Product using (_,_)

import Categories.Category.Construction.Core C as Core
import Categories.Category.Monoidal.Braided.Properties as BraidedProps
open import Categories.Category.Monoidal.Interchange using (HasInterchange)
import Categories.Category.Monoidal.Interchange.Braided as BraidedInterchange
  using (module swapInner; swapInner-braiding)
import Categories.Category.Monoidal.Reasoning M as MonoidalReasoning
import Categories.Category.Monoidal.Utilities M as MonoidalUtilities
open import Categories.Category.Product using (_⁂_; assocˡ)
open import Categories.Functor using (_∘F_)
open import Categories.NaturalTransformation.NaturalIsomorphism
  using (_≃_; niHelper)
open import Categories.Morphism.IsoEquiv C using (to-unique)
open import Categories.Morphism.Reasoning C
  using (elim-center; pushˡ; pullʳ; cancelInner; switch-fromtoˡ)

open Category C using (Obj; _⇒_; _∘_; id; sym-assoc; ∘-resp-≈ʳ; module Equiv)
open Commutation C
open MonoidalReasoning
open MonoidalUtilities using (_⊗ᵢ_)
open Symmetric S renaming (associator to α; braided to B)
open BraidedInterchange B
open Core.Shorthands               -- for idᵢ, _∘ᵢ_, ...
open MonoidalUtilities.Shorthands  -- for λ⇒, ρ⇒, α⇒, ...
open BraidedProps.Shorthands B     -- for σ⇒, ...

private
  variable
    W W₁ W₂ X X₁ X₂ Y Y₁ Y₂ Z Z₁ Z₂ : Obj
    f g h i : X ⇒ Y

private
  i⇒ = swapInner.from
  i⇐ = swapInner.to

swapInner-commutative : [ (X₁ ⊗₀ X₂) ⊗₀ (Y₁ ⊗₀ Y₂) ⇒
                          (X₁ ⊗₀ X₂) ⊗₀ (Y₁ ⊗₀ Y₂) ]⟨
                           i⇒    ⇒⟨ (X₁ ⊗₀ Y₁) ⊗₀ (X₂ ⊗₀ Y₂) ⟩
                           i⇒
                        ≈ id
                        ⟩
swapInner-commutative = begin
    i⇒ ∘ i⇒                                                               ≈⟨ pullʳ (cancelInner α.isoʳ) ⟩
    α⇐ ∘ id ⊗₁ (α⇒ ∘ σ⇒ ⊗₁ id ∘ α⇐) ∘ id ⊗₁ (α⇒ ∘ σ⇒ ⊗₁ id ∘ α⇐) ∘ α⇒  ≈˘⟨ refl⟩∘⟨ pushˡ split₂ˡ ⟩
    α⇐ ∘ id ⊗₁ ((α⇒ ∘ σ⇒ ⊗₁ id ∘ α⇐) ∘ α⇒ ∘ σ⇒ ⊗₁ id ∘ α⇐) ∘ α⇒        ≈⟨ refl⟩∘⟨ refl⟩⊗⟨ (∘-resp-≈ʳ sym-assoc ○ α[σ⊗1]α⁻¹.isoʳ) ⟩∘⟨refl ⟩
    α⇐ ∘ id ⊗₁ id ∘ α⇒                                                    ≈⟨ elim-center ⊗.identity ○ α.isoˡ ⟩
    id                                                                     ∎
  where module α[σ⊗1]α⁻¹ = _≅_ (α ∘ᵢ braided-iso ⊗ᵢ idᵢ ∘ᵢ α ⁻¹) using (isoʳ)

swapInner-iso : (W ⊗₀ X) ⊗₀ (Y ⊗₀ Z) ≅ (W ⊗₀ Y) ⊗₀ (X ⊗₀ Z)
swapInner-iso = record
  { from = i⇒
  ; to   = i⇒
  ; iso  = record
    { isoˡ = swapInner-commutative
    ; isoʳ = swapInner-commutative
    }
  }

swapInner-selfInverse : [ (X₁ ⊗₀ X₂) ⊗₀ (Y₁ ⊗₀ Y₂) ⇒
                          (X₁ ⊗₀ Y₁) ⊗₀ (X₂ ⊗₀ Y₂) ]⟨
                          i⇒
                        ≈ i⇐
                        ⟩
swapInner-selfInverse =
  to-unique (iso swapInner-iso) swapInner.iso Equiv.refl

swapInner-braiding′ : [ (W ⊗₀ X) ⊗₀ (Y ⊗₀ Z) ⇒ (Y ⊗₀ W) ⊗₀ (Z ⊗₀ X) ]⟨
                        i⇒         ⇒⟨ (W ⊗₀ Y) ⊗₀ (X ⊗₀ Z) ⟩
                        σ⇒ ⊗₁ σ⇒
                      ≈ σ⇒         ⇒⟨ (Y ⊗₀ Z) ⊗₀ (W ⊗₀ X) ⟩
                        i⇒
                      ⟩
swapInner-braiding′ = switch-fromtoˡ swapInner-iso swapInner-braiding
