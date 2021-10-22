{-# OPTIONS --safe --without-K #-}
module Languages.STLC+Rec+Maybe where 

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
open import Fragment.General
open import Fragment.Maybe
open import Fragment.MaybeCase

open Itf

module _ (M : Eff) ⦃ mon : Monadic M ⦄ ⦃ str : IsStrong mon ⦄
         ⦃ _   : Reader   Sto  M ⦄
         ⦃ _   : Lambda        M ⦄
         ⦃ _   : General       M ⦄ where

  lang = ( lift M Maybe' ⊙⟨ ∙-copy ⟩ᵐ MaybeCase M ) ⊙⟨ ∙-disjoint ⟩ᵐ Fun M ⊙⟨ ∙-disjoint ⟩ᵐ Rec M 
