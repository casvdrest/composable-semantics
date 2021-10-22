{-# OPTIONS --safe --without-K --overlapping-instances #-}

-------------------------------------------------------------------------------
-- agda-stlib imports
--
open import Level renaming (suc to sucL)
open import Function using (_$_) renaming (id to idᶠ ; _∘_ to _∘ᶠ_)

open import Data.Empty
open import Data.Nat hiding (_^_)
open import Data.Bool
open import Data.Product
open import Data.Fin hiding (_+_ ; strengthen)
open import Data.List hiding (product)
open import Data.Sum
open import Data.Unit

open import Relation.Unary using (IUniversal ; _⇒_ ; _∩_)

open import Relation.Binary using (Rel)
open import Relation.Binary.Structures
open import Relation.Binary.PropositionalEquality renaming (refl to ≡-refl ; sym to ≡-sym ; trans to ≡-trans)
open import Relation.Binary.PropositionalEquality.Properties renaming (isEquivalence to ≡-isEquivalence)
open ≡-Reasoning

open import Data.List.Relation.Unary.Any
open import Data.List.Relation.Binary.Sublist.Propositional

-------------------------------------------------------------------------------
-- agda-categories imports
--
open import Categories.Category.Core
open import Categories.Category.Cartesian
open import Categories.Category.Instance.Sets
open import Categories.Category.BinaryProducts
open import Categories.Category.CartesianClosed.Canonical
open import Categories.Category.Cartesian.Monoidal

open import Categories.Morphism
open import Categories.Monad
open import Categories.Monad.Strong
open import Categories.Functor

open import Categories.Category.Monoidal.Instance.Sets
open import Categories.Category.Construction.Kleisli

open import Categories.Object.Product.Core
open import Categories.Object.Exponential
open import Categories.Object.Terminal
            
-------------------------------------------------------------------------------
-- Local

open import ArbitraryCategories.Base

module ArbitraryCategories.StoreSets where

-- Defines a (category of (monotone) predicates over store types, 
module Cat (T : Set) where

  Sto = List T

  open IsEquivalence

  -- Really, this defines a presheaf over the thin category induced by -⊇-,
  -- but for convenience we forget about the laws here. 
  record MPred : Set₁ where
    field P        : Sto → Set
          monotone : ∀ {Σ₁ Σ₂} → Σ₁ ⊇ Σ₂ → P Σ₁ → P Σ₂

  open MPred

  --  ... and these are natural transformations, but again we'll ignore the laws
  record _→·_ (Q R : MPred) : Set where 
    field ap : ∀[ Q .P ⇒ R .P ]

  open _→·_ 

  _∘·_ : ∀ {Q R S : MPred} → (β : R →· S) → (α : Q →· R) → Q →· S 
  (β ∘· α) .ap x = β .ap (α .ap x)

  open _→·_

  record _≣_ {Q R : MPred} (α β : Q →· R) : Set where 
    field because : ∀ {Σ} {x : Q .P Σ} → α .ap x ≡ β .ap x

  open _≣_

  SetΣ : Category (sucL 0ℓ) 0ℓ 0ℓ
  SetΣ = record
    { Obj = MPred
    ; _⇒_ = _→·_
    ; _≈_ = _≣_
    ; id  = λ where .ap → idᶠ
    ; _∘_ = _∘·_
    
    ; assoc     = λ where .because → ≡-refl 
    ; sym-assoc = λ where .because → ≡-refl
    ; identityˡ = λ where .because → ≡-refl
    ; identityʳ = λ where .because → ≡-refl
    ; identity² = λ where .because → ≡-refl
    
    ; equiv = record
        { refl  = λ where     .because → ≡-refl
        ; sym   = λ where p   .because → ≡-sym   (p .because)
        ; trans = λ where p q .because → ≡-trans (p .because) (q .because)
        } 
    ; ∘-resp-≈ = ∘-resp-≣
    }
    where
      ∘-resp-≣ : ∀ {P′ Q R} {α γ : Q →·  R} {β δ : P′ →· Q}
                 → α ≣ γ → β ≣ δ → (α ∘· β) ≣ (γ ∘· δ)
      ∘-resp-≣ {α = α} {γ} {β} {δ} α≣γ β≣δ .because 
        = begin α .ap (β .ap _)  ≡⟨ cong (α .ap) (β≣δ .because) ⟩
                α .ap (δ .ap _)  ≡⟨ α≣γ .because                ⟩
                γ .ap (δ .ap _)  ∎

  Σ⊤ : MPred
  Σ⊤ .P             = λ _ → ⊤
  Σ⊤ .monotone _ tt = tt

  Σ⊤-is-terminal : IsTerminal SetΣ Σ⊤
  Σ⊤-is-terminal =
    record { !        = λ where .ap _ → tt
           ; !-unique = λ where f .because → ≡-refl
           }
  
  _∩·_ : (Q R : MPred) → MPred
  (Q ∩· R) .P                    = Q .P ∩ R .P
  (Q ∩· R) .monotone p (Qx , Rx) = Q .monotone p Qx , R .monotone p Rx

  open BinaryProducts

  SetΣ-products : BinaryProducts SetΣ
  SetΣ-products .product {Q} {R} = record
    { A×B      = Q ∩· R
    ; π₁       = π₁·
    ; π₂       = π₂·
    ; ⟨_,_⟩    = λ α β → ⟨ α , β ⟩·
    ; project₁ = λ where .because → ≡-refl
    ; project₂ = λ where .because → ≡-refl
    ; unique   = isUnique 
    }
    where π₁· : (Q ∩· R) →· Q
          π₁· .ap (Qx , _) = Qx

          π₂· : (Q ∩· R) →· R
          π₂· .ap (_ , Rx) = Rx

          ⟨_,_⟩· : ∀ {S} → (S →· Q) → (S →· R) → (S →· (Q ∩· R))
          ⟨ α , β ⟩· .ap x = (α .ap x) , (β .ap x)

          isUnique : ∀ {P′} {α : P′ →· Q} {β : P′ →· R} {γ : P′ →· (Q ∩· R)}
                     → (π₁· ∘· γ) ≣ α → (π₂· ∘· γ) ≣ β → ⟨ α , β ⟩· ≣ γ  
          isUnique {α = α} {β} {γ} π₁∘γ≣α π₂∘γ≣β .because {x = x} =
            begin ⟨ α , β ⟩· .ap x                      ≡⟨⟩
                  α .ap x , β .ap x                     ≡⟨ cong₂ _,_ (≡-sym (π₁∘γ≣α .because)) (≡-sym (π₂∘γ≣β .because)) ⟩
                  π₁· .ap (γ .ap x) , π₂· .ap (γ .ap x) ≡⟨⟩ 
                  γ .ap x                               ∎  

  SetΣ-cartesian : Cartesian SetΣ
  SetΣ-cartesian = record
    { terminal = record
        { ⊤             = Σ⊤
        ; ⊤-is-terminal = Σ⊤-is-terminal
        }
    ; products = SetΣ-products
    }

-- module Defs (T : Set)
--   (M        : Monad (Cat.SetΣ T))
--   (ct       : Cartesian (Kleisli M))
--   (strength : Strength (CartesianMonoidal.monoidal (Cat.SetΣ-cartesian T)) M) where

--   open Signature

--   open Cat T
--   open MPred
--   open _→·_

--   open Monad M renaming (μ to μM)

--   -- Instantiate combinators with the category SetΣ
--   open Fragments   (Kleisli M) ct public 
--   open Combinators (Kleisli M) ct public

--   -------------------------------------------------------------------------------
--   -- Monadic operations 

--   open _≼_ ⦃...⦄
--   open □

--   return : ∀ {Q} → Q →· F.F₀ Q
--   return .ap = η.η _ .ap

--   _>>=_ : ∀ {Q R Σ} → F.F₀ Q .P Σ → (Q →· F.F₀ R) → F.F₀ R .P Σ 
--   x >>= f = μM.η _ .ap (F.F₁ f .ap x)

--   _>>_ : ∀ {Q R Σ} → F.F₀ Q .P Σ → ∀[ F.F₀ R .P ] → F.F₀ R .P Σ
--   x >> y = μM.η _ .ap (F.F₁ (λ where .ap _ → y) .ap x)

--   open Strength strength

--   _^_ : ∀ {Q R Σ} → F.F₀ R .P Σ → Q .P Σ → F.F₀ (Q ∩· R) .P Σ
--   mp ^ q = strengthen.η _ .ap (q , mp)

--   -------------------------------------------------------------------------------
--   -- Canons

--   module RefCanon where

--     data RefTyShape : Set where ref : RefTyShape
--     RefTySig = RefTyShape ▹ λ where ref → ⊤

    
    
  
