{-# OPTIONS --safe --without-K #-}
module Languages.Language4 where

open import Core
open import Canon
open import MonadicFragment Sto

open import Interface.Reader

open import Fragment.Arith
open import Fragment.NatCase
open import Fragment.Boolean
open import Fragment.Maybe
open import Fragment.MaybeCase
open import Fragment.Pair

open Itf

module _ (M : Eff) ⦃ mon : Monadic M ⦄ ⦃ str : IsStrong mon ⦄
         ⦃ _   : Reader Sto  M   ⦄ where 

  lang''' = (lift M Arith  ⊙⟨ ∙-copy ⟩ᵐ NatCase M)   ⊙⟨ ∙-disjoint ⟩ᵐ lift M Boolean ⊙⟨ ∙-disjoint ⟩ᵐ
            (lift M Maybe' ⊙⟨ ∙-copy ⟩ᵐ MaybeCase M) ⊙⟨ ∙-disjoint ⟩ᵐ lift M Pair  
