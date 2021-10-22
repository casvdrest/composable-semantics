{-# OPTIONS --safe --without-K #-}

module Languages.Expr where 

open import Core
open import Canon
open import Box
open import Fragment

open import Fragment.Arith
open import Fragment.Boolean
open import Fragment.Pair
open import Fragment.Maybe

module _ {Ix : Set → Set} ⦃ _ : ∀ {X} → Rel₂ _ (Ix X) ⦄ where

  lang-expr = Arith ⊙⟨ ∙-disjoint ⟩ Boolean ⊙⟨ ∙-disjoint ⟩ Pair ⊙⟨ ∙-disjoint ⟩ Maybe' {Ix}

