{-# OPTIONS --safe --without-K #-}
module Languages.Language5 where

open import Core
open import Canon
open import MonadicFragment Sto

open import Interface.Reader
open import Interface.Lambda
open import Interface.MonotoneState
open import Interface.Except

open import Fragment.Arith
open import Fragment.Boolean
open import Fragment.Lambda
open import Fragment.Ref
open import Fragment.Exception

open Itf

module _ (M : Eff) ⦃ mon : Monadic M ⦄ ⦃ _   : IsStrong mon ⦄
         ⦃ _   : Reader Sto    M ⦄
         ⦃ _   : Lambda        M ⦄
         ⦃ _   : MonotoneState M ⦄
         ⦃ _   : Exception Sto M ⦄ where

  lang = lift   M Arith   ⊙⟨ ∙-disjoint ⟩ᵐ lift M Boolean ⊙⟨ ∙-disjoint ⟩ᵐ Fun M ⊙⟨ ∙-disjoint ⟩ᵐ
         Ref    M         ⊙⟨ ∙-copy     ⟩ᵐ Except M 
