{-# OPTIONS --safe --without-K #-}

module Languages.Language3 where

open import Core
open import Canon
open import Box
open import Fragment

-- Fragments
open import Fragment.Pair
open import Fragment.Maybe
open import Fragment.Arith
open import Fragment.Boolean


----------------------------------------------------------------------------------
-- Bools, Nums, maybe and pairs
--
module _ {Ix : Set → Set} ⦃ _ : ∀ {X} → Rel₂ _ (Ix X) ⦄ where

  lang = Arith ⊙⟨ ∙-disjoint ⟩ Boolean  ⊙⟨ ∙-disjoint ⟩ Pair ⊙⟨ ∙-disjoint ⟩ Maybe'  {Ix}
