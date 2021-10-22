{-# OPTIONS --safe --without-K #-}

module Languages.STLC+Ref where 

open import Core
open import Canon
open import MonadicFragment Sto

open import Interface.Reader         
open import Interface.Lambda
open import Interface.MonotoneState
open import Interface.Except
open import Interface.General

open import Fragment.Arith      public
open import Fragment.Lambda     public
open import Fragment.Ref        public 

open Itf

module _ (M : Eff)  ⦃ mon : Monadic M ⦄ ⦃ str : IsStrong mon ⦄
         ⦃ _   : Reader   Sto  M ⦄
         ⦃ _   : Lambda        M ⦄
         ⦃ _   : MonotoneState M ⦄ where

  lang = lift M Arith ⊙⟨ ∙-disjoint ⟩ᵐ Fun M ⊙⟨ ∙-disjoint ⟩ᵐ Ref M 
