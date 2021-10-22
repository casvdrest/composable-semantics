{-# OPTIONS --without-K --safe #-}

module Categories.Functor.Instance.StrictCore where

-- The 'strict' core functor (from StrictCats to StrictGroupoids).
-- This is the right-adjoint of the forgetful functor from
-- StrictGroupoids to StrictCats
-- (see Categories.Functor.Adjoint.Instance.StrictCore)

open import Level using (Level; _⊔_)
open import Function.Base using (_$_) renaming (id to idf)
open import Relation.Binary.PropositionalEquality using (refl; cong; cong-id)

open import Categories.Category.Core using (Category)
import Categories.Category.Construction.Core as C
open import Categories.Category.Instance.StrictCats
open import Categories.Category.Instance.StrictGroupoids
open import Categories.Functor using (Functor)
open import Categories.Functor.Equivalence using (_≡F_)
open import Categories.Functor.Instance.Core renaming (Core to WeakCore)
open import Categories.Functor.Properties using ([_]-resp-≅)
import Categories.Morphism as Morphism
import Categories.Morphism.Reasoning as MR
import Categories.Morphism.HeterogeneousIdentity as HId
import Categories.Morphism.HeterogeneousIdentity.Properties as HIdProps
open import Categories.Morphism.IsoEquiv using (⌞_⌟)

module _ {o ℓ e : Level} where
  open Functor (WeakCore {o} {ℓ} {e})

  CoreRespFEq : {A B : Category o ℓ e} {F G : Functor A B} → F ≡F G → F₁ F ≡F F₁ G
  CoreRespFEq {A} {B} {F} {G} F≡G = record
    { eq₀ = eq₀
    ; eq₁ = λ {X} {Y} f → ⌞ begin
        (from $ hid BC $ eq₀ Y) ∘ F.F₁ (from f)       ≈⟨ ∘-resp-≈ˡ (hid-identity BC B from Equiv.refl (eq₀ Y)) ⟩
        (hid B $ cong idf $ eq₀ Y) ∘ F.F₁ (from f)    ≡⟨ cong (λ p → hid B p ∘ _) (cong-id (eq₀ Y)) ⟩
        hid B (eq₀ Y) ∘ F.F₁ (from f)                 ≈⟨ eq₁ (from f) ⟩
        G.F₁ (from f) ∘ hid B (eq₀ X)                 ≡˘⟨ cong (λ p → _ ∘ hid B p) (cong-id (eq₀ X)) ⟩
        G.F₁ (from f) ∘ (hid B $ cong idf $ eq₀ X)    ≈˘⟨ ∘-resp-≈ʳ (hid-identity BC B from Equiv.refl (eq₀ X)) ⟩
        G.F₁ (from f) ∘ (from $ hid BC $ eq₀ X)       ∎ ⌟
    }
    where
      BC = C.Core B
      module F = Functor F using (F₁)
      module G = Functor G using (F₁)
      open Category B using (_∘_; ∘-resp-≈ʳ; ∘-resp-≈ˡ; module HomReasoning; module Equiv)
      open HomReasoning
      open HId using (hid)
      open HIdProps using (hid-identity)
      open _≡F_ F≡G using (eq₀; eq₁)
      open Morphism._≅_ using (from)

Core : ∀ {o ℓ e} → Functor (StrictCats o ℓ e) (StrictGroupoids o (ℓ ⊔ e) e)
Core {o} {ℓ} {e} = record
   { F₀ = F₀
   ; F₁ = F₁
   ; identity = λ {A} →
       record { eq₀ = λ _ → refl ; eq₁ = λ _ → ⌞ MR.id-comm-sym A ⌟ }
   ; homomorphism = λ {A B C} →
       record { eq₀ = λ _ → refl ; eq₁ = λ _ → ⌞ MR.id-comm-sym C ⌟ }
   ; F-resp-≈ = λ {A B F G} → CoreRespFEq {A = A} {B} {F} {G}
   }
   where open Functor (WeakCore {o} {ℓ} {e})
