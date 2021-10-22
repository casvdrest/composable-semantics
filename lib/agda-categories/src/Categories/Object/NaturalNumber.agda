{-# OPTIONS --without-K --safe #-}

open import Categories.Category.Core
open import Categories.Object.Terminal hiding (up-to-iso)

module Categories.Object.NaturalNumber {o ℓ e} (𝒞 : Category o ℓ e) (𝒞-Terminal : Terminal 𝒞) where

open import Level

open import Categories.Morphism 𝒞
open import Categories.Morphism.Reasoning 𝒞

open Category 𝒞
open HomReasoning
open Equiv

open Terminal 𝒞-Terminal

private
  variable
    A B C D X Y Z : Obj
    h i j : A ⇒ B

record IsNaturalNumber (N : Obj) : Set (o ⊔ ℓ ⊔ e) where
  field
    z : ⊤ ⇒ N
    s : N ⇒ N
    universal : ∀ {A} → ⊤ ⇒ A → A ⇒ A → N ⇒ A
    z-commute : ∀ {A} {q : ⊤ ⇒ A} {f : A ⇒ A} → q ≈ universal q f ∘ z
    s-commute : ∀ {A} {q : ⊤ ⇒ A} {f : A ⇒ A} → f ∘ universal q f ≈ universal q f ∘ s
    unique    : ∀ {A} {q : ⊤ ⇒ A} {f : A ⇒ A} {u : N ⇒ A} → q ≈ u ∘ z → f ∘ u ≈ u ∘ s → u ≈ universal q f

  η : universal z s ≈ id
  η = ⟺ (unique (⟺ identityˡ) id-comm)

  universal-cong : ∀ {A} → {f f′ : ⊤ ⇒ A} → {g g′ : A ⇒ A} → f ≈ f′ → g ≈ g′ → universal f g ≈ universal f′ g′
  universal-cong f≈f′ g≈g′ = unique (⟺ f≈f′ ○  z-commute) (∘-resp-≈ˡ (⟺ g≈g′) ○ s-commute)

record NaturalNumber : Set (o ⊔ ℓ ⊔ e) where
  field
    N : Obj
    isNaturalNumber : IsNaturalNumber N

  open IsNaturalNumber isNaturalNumber public

open NaturalNumber

module _ (N : NaturalNumber) (N′ : NaturalNumber) where
  private
    module N = NaturalNumber N
    module N′ = NaturalNumber N′

  up-to-iso : N.N ≅ N′.N
  up-to-iso = record
    { from = N.universal N′.z N′.s
    ; to = N′.universal N.z N.s
    ; iso = record
      { isoˡ = universal-∘ N N′
      ; isoʳ = universal-∘ N′ N
      }
    }
    where
      universal-∘ : ∀ (N N′ : NaturalNumber) → universal N′ (z N) (s N) ∘ universal N (z N′) (s N′) ≈ id  
      universal-∘ N N′ = unique N (z-commute N′ ○ pushʳ (z-commute N)) (pullˡ (s-commute N′) ○ assoc ○ ∘-resp-≈ʳ (s-commute N) ○ ⟺ assoc) ○ (η N)
      
