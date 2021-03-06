{-# OPTIONS --safe --without-K #-}

open import Relation.Unary
import Level as L

module Box where 

  {- A notion of types with preorders -}
  module _ where

    record Rel₂ {a} (ℓ : L.Level) (A : Set a) : Set (a L.⊔ L.suc ℓ) where 
      field R     : A → A → Set ℓ
            refl  : ∀ {x}                     → R x x
            trans : ∀ {x y z} → R x y → R y z → R x z

  {- Kripke semantics of Box (necessity) modality. We define □ for all types
     that have an associated preorder (i.e., instance of `Rel₂`), which is used
     to relate the current world to the future world  -} 
  module Necessary {i ℓ} {I : Set i} ⦃ _ : Rel₂ ℓ I ⦄ where 
  
    open Rel₂ ⦃...⦄

    record □ (P : I → Set (i L.⊔ ℓ)) (x : I) : Set (i L.⊔ ℓ) where 
      field future : ∀[ R x ⇒ P ]

    open □


    ----------------------------------------------------------------------------
    --- 
    --- Comonadic operations  
    
    extract : ∀ {P} → ∀[ □ P ⇒ P ]
    extract px = future px refl
  
    duplicate : ∀ {P} → ∀[ □ P ⇒ □ (□ P) ]
    future (future (duplicate px) r₁) r₂ = future px (trans r₁ r₂)


    ----------------------------------------------------------------------------
    ---
    --- Some auxiliary operations for working with □ types

    □-lift : ∀ {P Q} → ∀[ P ⇒ Q ] → ∀[ □ P ⇒ □ Q ]
    future (□-lift f x) r = f (future x r)

    □-distr-⇒ : ∀ {P Q} → ∀[ □ (P ⇒ Q) ⇒ □ P ⇒ □ Q ] 
    future (□-distr-⇒ f x) r = future f r (future x r)

    weaken : ∀ {P x y} → □ P x → R x y → □ P y 
    weaken px = future (duplicate px)
  
