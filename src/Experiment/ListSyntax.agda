-- Courtesy to Donnacha Oisín Kidney
--
-- https://doisinkidney.com/posts/2019-04-20-ListSyntax.html

open import Data.List hiding ([_])
open import Data.Product
open import Level

module Experiment.ListSyntax where

module _ where
  record ListSyntax {a b} (A : Set a) (B : Set b) : Set (a ⊔ b) where
    field [_] : B → List A

  open ListSyntax ⦃ ... ⦄ public

  instance
    cons : ∀ {a b} {A : Set a} {B : Set b} ⦃ _ : ListSyntax A B ⦄
         →  ListSyntax A (A × B)
    [_] ⦃ cons ⦄ (x , xs) = x ∷ [ xs ]

  instance
    sing : ∀ {a} {A : Set a} → ListSyntax A A
    [_] ⦃ sing ⦄ = _∷ []
