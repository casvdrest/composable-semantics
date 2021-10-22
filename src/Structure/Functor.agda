{-# OPTIONS --safe --without-K #-}

module Structure.Functor where

open import Core
open import Level

open import Relation.Unary using (IUniversal ; _⇒_)

module _ where

  record RawFunctor {I : Set i} (F : (I → Set ℓ) → (I → Set ℓ)) : Set (i ⊔ suc ℓ) where 
    field fmap : ∀[ P ⇒ Q ] → ∀[ F P ⇒ F Q ]  

  
