{-# OPTIONS --safe --without-K #-}
module Languages.Language2 where

open import Core
open import Canon
open import MonadicFragment Sto

open import Interface.Reader
open import Interface.Lambda

open import Fragment.Lambda
open import Fragment.Arith
open import Fragment.NatCase
open import Fragment.Boolean

open Itf

module _ (M : Eff) ⦃ mon : Monadic M ⦄ ⦃ str : IsStrong mon ⦄
         ⦃ _   : Reader Sto M   ⦄
         ⦃ _   : Lambda     M   ⦄ where

  lang' = Fun M ⊙⟨ ∙-disjoint ⟩ᵐ lift M Boolean  ⊙⟨ ∙-disjoint ⟩ᵐ lift M Arith ⊙⟨ ∙-copy ⟩ᵐ NatCase M  
