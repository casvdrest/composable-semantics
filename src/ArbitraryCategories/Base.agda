{-# OPTIONS --without-K --safe #-}

-------------------------------------------------------------------------------
-- agda-stlib imports
--
open import Level renaming (suc to sucL)
open import Function using (_∘_ ; _$_) renaming (id to idᶠ)

open import Data.Product using (Σ-syntax ; _,_ ; uncurry ; ∃-syntax ; ∃ ; <_,_>) renaming (_×_ to _×_)
open import Data.Nat hiding (_⊔_)
open import Data.Vec renaming (map to vmap)
open import Data.These
open import Data.Maybe renaming (_>>=_ to _>>=ᵐ_)
open import Data.Sum

open import Data.List
open import Data.List.Membership.Propositional
open import Data.List.Relation.Unary.Any
open import Data.List.Relation.Unary.All

open import Relation.Unary hiding (_∈_ ; _⟨⊙⟩_)

open import Relation.Binary.PropositionalEquality
open import Relation.Binary.PropositionalEquality.Properties using () renaming (isEquivalence to ≡-isEquivalence)


open import Relation.Binary.Definitions using (Reflexive ; Transitive)
open import Relation.Binary.Structures using (IsEquivalence ; IsPreorder)

-------------------------------------------------------------------------------
-- agda-categories imports
--
open import Categories.Category.Core
open import Categories.Category.Cartesian
open import Categories.Category.BinaryProducts

open import Categories.Object.Terminal

import Categories.Morphism

open import Signature
open import Union

module ArbitraryCategories.Base  where

--
-- Language fragments
-- 
module Fragments {o m e}
  (𝓒       : Category o m e)
  (Ct       : Cartesian 𝓒)
  where 

  open Category       𝓒          using (Obj) renaming  (_⇒_ to _⟨⇒⟩_ ; _∘_ to _∘ᴾ_)
  open Cartesian      Ct
  open Terminal       terminal
  open BinaryProducts products    renaming (_×_ to _𝓒×_)

  record Canon : Set (sucL (o ⊔ m)) where
    constructor canon
    field Type : Signature m
          Val  : Algebra Type Obj Obj

    Ctx = List (μ Type)
    Ty  = μ Type

    Env : Ctx → Obj
    Env []      = ⊤
    Env (t ∷ Γ) = cata Val t 𝓒× Env Γ

    Values : Ty → Obj
    Values = cata Val

    fetch : ∀ {Γ t} → t ∈ Γ → Env Γ ⟨⇒⟩ cata Val t 
    fetch (here refl) = π₁
    fetch (there x)   = fetch x ∘ᴾ π₂


  -------------------------------------------------------------------------------
  -- Language fragments with canonical forms given by `c`
 
  module _ (c : Canon) where 

    open Canon c

    record Fragment : Set (sucL (o ⊔ m ⊔ e)) where
      constructor fragment
      field Expr : ISignature m (Ctx × Ty) (Ctx × Ty)
            eval : IAlgebra Expr λ (Γ , t) → Env Γ ⟨⇒⟩ Values t

  -------------------------------------------------------------------------------
  -- Fragments are closed under a co-product derived from the co-producs
  -- of the underlying signature/algebra

  open Fragment
  
  _⟨⊙⟩_ : ∀[ Fragment ⇒ Fragment ⇒ Fragment ]
  Expr (φ₁ ⟨⊙⟩ φ₂) = Expr φ₁ :++:   Expr φ₂
  eval (φ₁ ⟨⊙⟩ φ₂) = eval φ₁ :⊕: eval φ₂

  interpreter : ∀ {c} → (φ : Fragment c) → ∀ {Γ t} → μᴵ (Expr φ) (Γ , t) → Canon.Env c Γ ⟨⇒⟩ Canon.Values c t
  interpreter φ x = foldᴵ (eval φ) x

module Combinators {o m e}
  (𝓒       : Category o m e)
  (Ct       : Cartesian 𝓒)
  where
  
  open Fragments           𝓒 Ct
  open Categories.Morphism 𝓒

  open Category 𝓒          renaming (_⇒_ to _⟨⇒⟩_) 

  open Canon

  open _≼_

  -------------------------------------------------------------------------------
  -- Sub-canons.
  --
  -- The sub-canon relation forms a preorder w.r.t. propositional equality
  record _⊑_ (c₁ c₂ : Canon) : Set (sucL (o ⊔ m ⊔ e)) where
    field ⦃ sub-ty  ⦄ : Type c₁ ≼ Type c₂ 
          canonical   : ∀ {T : Set _} {t : ⟦ Type c₁ ⟧ T} {V : T → Obj}
                      → alg (Val c₁) (map-sig V t) ≅ alg (Val c₂) (map-sig V (inj sub-ty t))


  open _⊑_

  ⊑-refl : Reflexive _⊑_ 
  ⊑-refl = record
    { sub-ty    = ≼-refl
    ; canonical = IsEquivalence.refl ≅-isEquivalence
    }

  ⊑-trans : Transitive _⊑_
  ⊑-trans p q = record
    { sub-ty    = ≼-trans (sub-ty p) (sub-ty q)
    ; canonical = λ {_} {_} {V} → IsEquivalence.trans ≅-isEquivalence (canonical p {V = V}) (canonical q {V = V})
    }

  open IsPreorder

  ⊑-isPreorder : IsPreorder _≡_ _⊑_
  ⊑-isPreorder = record
    { isEquivalence = ≡-isEquivalence
    ; reflexive     = λ where refl → ⊑-refl
    ; trans         = ⊑-trans
    }

  variable
    c c₁ c₂ : Canon

  -- A lemma about the definition of `map-cata`, that proves that it behaves like
  -- `map` for Vectors
  map-cata-def : ∀ {V : Algebra σ Obj Obj} {n} (xs : Vec (μ σ) n)
                 → map-cata V xs ≡ Data.Vec.map (cata V) xs
  map-cata-def []      = _≡_.refl
  map-cata-def {V = V} (x ∷ v) = cong (_ ∷_) (map-cata-def {V = V} v)

  ↑ : ∀ ⦃ p : c₁ ⊑ c ⦄ → {t : ⟦ Type c₁ ⟧ (μ (Type c))}
      → alg (Val c₁) (map-sig (cata (Val c)) t) ⟨⇒⟩ cata (Val c) ⟨ inj (sub-ty  p) t ⟩
  ↑ {c₁ = c₁} {c = c} ⦃ p = p ⦄ = subst
    (λ x → alg (Val c₁) _ ⟨⇒⟩ alg (Val c) (_ , lift x))
    (sym $ map-cata-def {V = Val c} _)
    (_≅_.from (canonical p {V = cata (Val c)}))
                      
  ↓ : ∀ ⦃ p : c₁ ⊑ c ⦄ → {t : ⟦ Type c₁ ⟧ (μ (Type c))}
      → cata (Val c) ⟨ inj (sub-ty  p) t ⟩ ⟨⇒⟩ alg (Val c₁) (map-sig (cata (Val c)) t) 
  ↓ {c₁ = c₁} {c = c} ⦃ p = p ⦄ = subst
    (λ x → alg (Val c) (_ , lift x) ⟨⇒⟩ alg (Val c₁) _)
    (sym $ map-cata-def {V = Val c} _)
    (_≅_.to (canonical p)) 

  record □ (P : Canon → Set (sucL (o ⊔ m ⊔ e))) (c : Canon) : Set (sucL (o ⊔ m ⊔ e)) where
    field future : ∀ {c′} → ⦃ c ⊑ c′ ⦄ → P c′

  open □

  extract : ∀ {P} → ∀[ □ P ⇒ P ]
  extract □P = future □P ⦃ ⊑-refl ⦄

  duplicate : ∀ {P} → ∀[ □ P ⇒ □ (□ P) ]
  future (future (duplicate □P) ⦃ p ⦄) ⦃ q ⦄ = future □P ⦃ ⊑-trans p q ⦄

  open Union.Union

  infix 8 _∙_≣_
  record _∙_≣_ (c₁ c₂ c : Canon) : Set (sucL (o ⊔ m ⊔ e)) where
    field union-ty   : ∀ {X : Set m} → Union (⟦ Type c₁ ⟧ X) (⟦ Type c₂ ⟧ X) (⟦ Type c ⟧ X)
          canonical₁ : ∀ {T} {t : ⟦ Type c₁ ⟧ T}{V : T → Obj} → alg (Val c₁) (map-sig V t) ≅ alg (Val c) (map-sig V (inja union-ty t))  
          canonical₂ : ∀ {T} {t : ⟦ Type c₂ ⟧ T}{V : T → Obj} → alg (Val c₂) (map-sig V t) ≅ alg (Val c) (map-sig V (injb union-ty t))  

  open _∙_≣_

  ∙-copy : c ∙ c ≣ c
  union-ty   ∙-copy = union-copy 
  canonical₁ ∙-copy = IsEquivalence.refl ≅-isEquivalence
  canonical₂ ∙-copy = IsEquivalence.refl ≅-isEquivalence

  infixr 10 _◆_
  _◆_ : (c₁ c₂ : Canon) → Canon
  c₁ ◆ c₂ = canon (Type c₁ :+: Type c₂) (Val c₁ ⊕ Val c₂)

  ∙-disjoint : c₁ ∙ c₂ ≣ c₁ ◆ c₂
  inja (union-ty ∙-disjoint) (x , y) = inj₁ x , y
  injb (union-ty ∙-disjoint) (x , y) = inj₂ x , y
  from (union-ty ∙-disjoint) (inj₁ x , y) = this (x , y)
  from (union-ty ∙-disjoint) (inj₂ x , y) = that (x , y)
  a-inv (union-ty ∙-disjoint) {fst , snd} = _≡_.refl
  b-inv (union-ty ∙-disjoint) = _≡_.refl
  from-inv (union-ty ∙-disjoint) {inj₁ x , snd} = _≡_.refl
  from-inv (union-ty ∙-disjoint) {inj₂ y , snd} = _≡_.refl
  canonical₁ ∙-disjoint = IsEquivalence.refl ≅-isEquivalence
  canonical₂ ∙-disjoint = IsEquivalence.refl ≅-isEquivalence

  ∙≣→⊑₁ : c₁ ∙ c₂ ≣ c → c₁ ⊑ c
  ∙≣→⊑₁ u = record
    { sub-ty    = ∙-≼₁ (λ _ → union-ty u)
    ; canonical = canonical₁ u
    }

  ∙≣→⊑₂ : c₁ ∙ c₂ ≣ c → c₂ ⊑ c
  ∙≣→⊑₂ u = record
    { sub-ty    = ∙-≼₂ (λ _ → union-ty u)
    ; canonical = canonical₂ u 
    }

  open Fragment

  monotone : c₁ ⊑ c₂ → □ Fragment c₁ → □ Fragment c₂ 
  monotone p φ = future (duplicate φ) ⦃ p ⦄

  _⟪⊙⟫_ : ∀[ □ Fragment ⇒ □ Fragment ⇒ □ Fragment ]
  future (φ₁ ⟪⊙⟫ φ₂) = future φ₁ ⟨⊙⟩ future φ₂ 

  infixr 5 _⊙⟪_⟫_
  _⊙⟪_⟫_ : □ Fragment c₁ → c₁ ∙ c₂ ≣ c → □ Fragment c₂ → □ Fragment c
  φ₁ ⊙⟪ u ⟫ φ₂ = monotone (∙≣→⊑₁ u) φ₁ ⟪⊙⟫ monotone (∙≣→⊑₂ u) φ₂ 
  
