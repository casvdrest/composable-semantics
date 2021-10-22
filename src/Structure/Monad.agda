{-# OPTIONS --safe --without-K #-}

module Structure.Monad where

open import Core
open import Level
open import Function

open import Relation.Unary  using (IUniversal ; _⇒_ ; _∩_)

open import Relation.Binary                       using (Rel)
open import Relation.Binary.PropositionalEquality using (refl ; _≡_)
open import Relation.Binary.Structures            using (IsPreorder)

open import Data.Product using (proj₁ ; _,_)

module _ where

  record RawMonad {I : Set i} (M : (I → Set ℓ) → (I → Set ℓ)) : Set (i ⊔ suc ℓ) where
    field return : ∀[ P ⇒ M P ]
          bind   : ∀[ P ⇒ M Q ] → ∀[ M P ⇒ M Q ]

    _>>=_ : ∀ {i} → M P i → ∀[ P ⇒ M Q ] → M Q i
    x >>= f = bind f x 
  
    _>>_ : ∀ {i} → M P i → ∀[ M Q ] → M Q i
    x >> y = x >>= λ _ → y

    join : ∀[ M (M P) ⇒ M P ]
    join x = bind id x
  
  record RawComonad {I : Set i} (W : (I → Set ℓ) → (I → Set ℓ)) : Set (i ⊔ suc ℓ) where
    field extract : ∀[ W P ⇒ P ]
          extend  : ∀[ W P ⇒ Q ] → ∀[ W P ⇒ W Q ]


    duplicate : ∀[ W P ⇒ W (W P) ]
    duplicate x = extend id x

module Wk {A : Set a} (_~_  : Rel A a) where

  record Weakenable {ℓ} (P : A → Set ℓ) : Set (ℓ ⊔ a) where
    field
      wk : ∀ {x x′} → x ~ x′ → P x → P x′

  record Strength {M : (A → Set a) → A → Set a} (mon : RawMonad M) : Set (suc a) where  
     infix 10 _^_ 
     field _^_ : ∀ {P Q : A → Set a} → ⦃ Weakenable Q ⦄ → ∀[ M P ⇒ Q ⇒ M (P ∩ Q) ]

{- Monad/Comonad instances for diamond/box + monadic strength -} 
module Closure {A : Set a} (_~_  : Rel A a) (pre : IsPreorder _≡_ _~_) where

  open import Relation.Unary.Closure.Base _~_
  open import Structure.Functor

  instance ◇-functor : RawFunctor {ℓ = a} ◇ 
  RawFunctor.fmap ◇-functor f x = ◇.map f x

  open RawFunctor ⦃...⦄

  instance ◇-monad : RawMonad {ℓ = a} ◇
  RawMonad.return ◇-monad   = ◇.pure (IsPreorder.reflexive pre refl)
  RawMonad.bind   ◇-monad f = ◇.join (IsPreorder.trans pre) ∘ (fmap f)

  thing : ∀ {x} → (possible : ◇ P x) → P (proj₁ possible)
  thing (_ , _ , px) = px

  thinning : ∀ {x} → (possible : ◇ P x) → proj₁ possible ~ x 
  thinning (_ , σ , _) = σ

  instance □-functor : RawFunctor {ℓ = a} □
  RawFunctor.fmap □-functor f x = □.map f x

  instance □-comonad : RawComonad {ℓ = a} □
  RawComonad.extract □-comonad   = □.extract (IsPreorder.reflexive pre refl)
  RawComonad.extend  □-comonad f = fmap f ∘ □.duplicate (IsPreorder.trans pre)

  widen : ∀ {P : Pred A} {Σ Σ′} → Σ ~ Σ′ → ◇ P Σ → ◇ P Σ′
  widen σ px = ◇.reindex (IsPreorder.trans pre) σ px 

  mk◇ : ∀ {P : Pred A} {x} → P x → ◇ P x
  mk◇ = ◇.pure (IsPreorder.reflexive pre refl)

-- module _ where

--   open import Signature
--   open import Data.List.Relation.Binary.Sublist.Propositional

--   Monadic : Eff → Set₁
--   Monadic M = ∀ {σ} {V : μ σ → Sto (μ σ) → Set} {Γ} → RawMonad (M V Γ)

--   HasStrength : ∀ {M : Eff} → Monadic M → Set₁
--   HasStrength mon = ∀ {σ} {V : μ σ → Sto (μ σ) → Set} {Γ} → Wk.Strength _⊆_ (mon {σ} {V} {Γ})

  
