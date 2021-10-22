{-# OPTIONS --safe --without-K #-}
module Languages.MiniML where

open import Core
open import Canon
open import MonadicFragment Sto

open import Interface.Reader
open import Interface.Lambda
open import Interface.General
open import Interface.MonotoneState
open import Interface.Except

open import Fragment.Lambda
open import Fragment.General
open import Fragment.Exception
open import Fragment.Arith
open import Fragment.Boolean
open import Fragment.NatCase
open import Fragment.Ref

open Itf

module _ (M : Eff)  ⦃ mon : Monadic M ⦄   ⦃ _   : IsStrong mon ⦄
         ⦃ _   : Reader Sto    M ⦄
         ⦃ _   : Lambda        M ⦄
         ⦃ _   : MonotoneState M ⦄
         ⦃ _   : Exception Sto M ⦄
         ⦃ _   : General       M ⦄  where

  miniml = (lift M Arith ⊙⟨ ∙-copy     ⟩ᵐ NatCase M) ⊙⟨ ∙-disjoint ⟩ᵐ lift M Boolean  ⊙⟨ ∙-disjoint ⟩ᵐ
           Ref M         ⊙⟨ ∙-disjoint ⟩ᵐ Fun M      ⊙⟨ ∙-copy     ⟩ᵐ Except M  

