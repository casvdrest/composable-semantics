{-# OPTIONS --safe --without-K #-}
module Languages.Language1 where

open import Core
open import Canon
open import MonadicFragment Sto

open import Interface.Reader         
open import Interface.Lambda
open import Interface.MonotoneState
open import Interface.Except
open import Interface.General

open import Fragment.Lambda     public
open import Fragment.General    public
open import Fragment.Ref        public 
open import Fragment.Arith      public
open import Fragment.NatCase    public
open import Fragment.Exception  public

open Itf

module _ (M : Eff) ⦃ mon : Monadic M ⦄ ⦃ str : IsStrong mon ⦄
         ⦃ _   : Reader   Sto  M ⦄
         ⦃ _   : Lambda        M ⦄
         ⦃ _   : MonotoneState M ⦄
         ⦃ _   : Exception Sto M ⦄
         ⦃ _   : General       M ⦄  where

  lang = ( Fun M ⊙⟨ ∙-copy ⟩ᵐ Rec M  ) ⊙⟨ ∙-disjoint ⟩ᵐ Ref M ⊙⟨ ∙-disjoint ⟩ᵐ lift M Arith ⊙⟨ ∙-copy ⟩ᵐ NatCase M ⊙⟨ ∙-copy ⟩ᵐ Except M
