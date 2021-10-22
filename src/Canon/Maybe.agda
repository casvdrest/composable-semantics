{-# OPTIONS --safe --without-K #-}

module Canon.Maybe where

open import Data.Product
open import Data.Vec
open import Data.Maybe using (Maybe)

open import Core
open import Signature
open import Canon

open import Level as L

module MaybeCanon where

  data TMaybeShape : Set where maybe : TMaybeShape
  TMaybeΣ = TMaybeShape ▹ λ where pair → 1 

  maybe′ : ⦃ TMaybeΣ ≼ σ ⦄ → (t : μ σ) → μ σ
  maybe′ t = inject (maybe , (lift (t ∷ []))) 
  
  open Algebra

  MaybeVal : Algebra TMaybeΣ Set Set
  alg MaybeVal (maybe , lift (Vt ∷ [])) = Maybe Vt
  
  maybeCanon : Canon
  Canon.ty maybeCanon = TMaybeΣ
  Canon.val maybeCanon = MaybeVal

open MaybeCanon public 
