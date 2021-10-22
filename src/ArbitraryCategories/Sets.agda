{-# OPTIONS --without-K --overlapping-instances #-}

-------------------------------------------------------------------------------
-- agda-stlib imports
--
open import Level renaming (suc to sucL)
open import Function using (_∘_ ; _$_ ; case_of_) renaming (id to idᶠ)

open import Data.Empty
open import Data.Nat 
open import Data.Bool
open import Data.Product
open import Data.Fin hiding (_+_ ; lift ; inject)
open import Data.List hiding (product)
open import Data.Sum
open import Data.Unit
open import Data.Vec using ([] ; _∷_)

open import Relation.Binary.PropositionalEquality

open import Data.List.Relation.Unary.Any
open import Data.List.Relation.Unary.All

-------------------------------------------------------------------------------
-- agda-categories imports
--
open import Categories.Category.Core
open import Categories.Category.Cartesian
open import Categories.Category.Instance.Sets
open import Categories.Category.BinaryProducts
open import Categories.Category.CartesianClosed.Canonical

open import Categories.Morphism
open import Categories.Monad
open import Categories.Functor

open import Categories.Category.Monoidal.Instance.Sets
open import Categories.Category.Construction.Kleisli

open import Categories.Object.Product.Core
open import Categories.Object.Exponential

open import Signature
open import Union

module ArbitraryCategories.Sets where 

open ISignature

module Defs (M  : Monad (Sets 0ℓ))
            (ct : Cartesian (Kleisli M)) -- does this hold in general?
            where

  open import ArbitraryCategories.Base

  open Monad M renaming (μ to μM)

  -- Instantiate combinators with the category of sets
  open Fragments   (Kleisli M) ct public 
  open Combinators (Kleisli M) ct public


  open Category (Kleisli M) using () renaming (_⇒_ to _⇒ᴹ_)

  open _≼_ ⦃...⦄
  open □

  return : ∀ {A} → A → F.F₀ A  
  return = η.η _

  _>>=_ : ∀ {A B} → F.F₀ A → (A → F.F₀ B) → F.F₀ B
  _>>=_ {A} {B} x f = μM.η _ (F.F₁ f x)

  _>>_ : ∀ {A B} → F.F₀ A → F.F₀ B → F.F₀ B
  _>>_ {A} {B} x f = x >>= λ _ → f

  pattern 1st = Fin.zero
  pattern 2nd = Fin.suc Fin.zero

  -------------------------------------------------------------------------------
  -- Canons 

  module NatCanon where

    data NatTyShape : Set where nat : NatTyShape
    NatTySig = NatTyShape ▹ λ where nat → 0

    NatCanon = canon NatTySig λ where .alg (nat , _) → ℕ

    natᵀ : ∀ {σ} → ⦃ NatTySig ≼ σ ⦄ → μ σ
    natᵀ = ⟨ inj (nat , lift []) ⟩

  module BoolCanon where

    data BoolTyShape : Set where bool : BoolTyShape
    BoolTySig = BoolTyShape ▹ λ where bool → 0

    BoolCanon = canon BoolTySig λ where .alg (bool , _) → Bool

    boolᵀ : ∀ {σ} → ⦃ BoolTySig ≼ σ ⦄ → μ σ
    boolᵀ ⦃ x ⦄ = ⟨ (inj (bool , lift [])) ⟩


  -------------------------------------------------------------------------------
  -- Fragments

  -- Arith
  module Arith where

    open NatCanon 

    module _ {c : Canon} ⦃ p : NatCanon ⊑ c ⦄ where

      open Canon c
  
      data ArithExprShape : Ctx × Ty → Set where
        numv : ∀ {Γ} → ℕ → ArithExprShape (Γ , natᵀ)
        add  : ∀ {Γ}     → ArithExprShape (Γ , natᵀ)

      ArithExprSig : ISignature _ (Ctx × Ty) (Ctx × Ty)
      ArithExprSig .Shapeᴵ  = ArithExprShape
      ArithExprSig .Indices (numv _)  = []
      ArithExprSig .Indices (add {Γ}) = (Γ , natᵀ) ∷ (Γ , natᵀ) ∷ []

      open Monad M

      evalArith : IAlgebra ArithExprSig λ (Γ , t) → Env Γ ⇒ᴹ Values t
      evalArith .ialg (numv n , _  ) nv = ↑ n 
      evalArith .ialg (add    , lift (fn ∷ fm ∷ [])) nv = do
        n ← fn nv >>= ↓
        m ← fm nv >>= ↓ 
        ↑ (n + m)

    ArithFragment : □ Fragment NatCanon
    future ArithFragment = fragment ArithExprSig evalArith

  -- Bool
  module Boolean where

    open BoolCanon

    module _ {c : Canon} ⦃ _ : BoolCanon ⊑ c ⦄ where 

      open Canon c

      data BoolExprShape : Ctx × Ty → Set where
        boolv : ∀ {Γ} → Bool → BoolExprShape (Γ , boolᵀ)
        ite   : ∀ {Γ t} → BoolExprShape (Γ , t)

      BoolExprSig : ISignature _ (Ctx × Ty) (Ctx × Ty)
      BoolExprSig .Shapeᴵ            = BoolExprShape
      BoolExprSig .Indices (boolv _) = []
      BoolExprSig .Indices (ite {Γ} {t}) = (Γ , boolᵀ) ∷ (Γ , t) ∷ (Γ , t) ∷ []

      evalBool : IAlgebra BoolExprSig λ (Γ , t) → Env Γ ⇒ᴹ Values t 
      evalBool .ialg (boolv x , _)                    nv = ↑ x
      evalBool .ialg (ite , lift (fc ∷ ft ∷ fe ∷ [])) nv = do
        c ← fc nv >>= ↓ 
        if c then ft nv else fe nv

    BoolFragment : □ Fragment BoolCanon
    future BoolFragment = fragment BoolExprSig evalBool

  
  -- Leq
  module Leq where

    open BoolCanon
    open NatCanon

    module _ {c : Canon} ⦃ _ : (NatCanon ◆ BoolCanon) ⊑ c ⦄ where

      open Canon c

      data LeqExprShape : Ctx × Ty → Set where
        leq : ∀ {Γ} → LeqExprShape (Γ , inject (inj₂ bool , lift []) )

      LeqExprSig : ISignature _ (Ctx × Ty) (Ctx × Ty)
      LeqExprSig .Shapeᴵ = LeqExprShape
      LeqExprSig .Indices (leq {Γ}) = (Γ , inject (inj₁ nat , lift [])) ∷ (Γ , inject (inj₁ nat , lift [])) ∷ []

      _<=_ : ℕ → ℕ → Bool
      zero  <= m     = true
      suc n <= zero  = false
      suc n <= suc m = n <= m

      evalLeq : IAlgebra LeqExprSig λ (Γ , t) → Env Γ ⇒ᴹ Values t
      evalLeq .ialg (leq , lift (fn ∷ fm ∷ [])) nv = do
        n ← fn nv >>= ↓ 
        m ← fm nv >>= ↓ 
        ↑ (n <= m) 

    LeqFragment : □ Fragment (NatCanon ◆ BoolCanon)
    future LeqFragment = fragment LeqExprSig evalLeq

module Test where

  -- Identity monad on Set
  Id : Monad (Sets 0ℓ)
  Id = record
    { F = id
    ; η = record
            { η           = λ X → idᶠ
            ; commute     = λ _ → refl
            ; sym-commute = λ _ → refl
            }
    ; μ = record
            { η           = λ _ → idᶠ
            ; commute     = λ _ → refl
            ; sym-commute = λ _ → refl
            }
    ; assoc     = refl
    ; sym-assoc = refl
    ; identityˡ = refl
    ; identityʳ = refl
    }

  postulate fun-ext : ∀ {a b}{A : Set a} {B : Set b} → (f g : A → B) → (∀ {x : A} → f x ≡ g x) → f ≡ g

  id-cc : CartesianClosed (Kleisli Id)
  id-cc = record
    { ⊤ = ⊤
    ; _×_ = _×_
    ; ! = λ _ → tt
    ; π₁ = proj₁
    ; π₂ = proj₂
    ; ⟨_,_⟩ = <_,_>
    ; !-unique = λ _ → refl
    ; π₁-comp = refl
    ; π₂-comp = refl
    ; ⟨,⟩-unique = BinaryProducts.unique products  
    ; _^_ = λ B A → A → B
    ; eval = uncurry _$_
    ; curry = curry
    ; eval-comp = refl
    ; curry-resp-≈ = λ eq → fun-ext _ _ eq 
    ; curry-unique = λ eq → fun-ext _ _ eq
    }
    where open Cartesian Product.Sets-is

  open Defs Id (CartesianClosed.isCartesian id-cc)

  open Arith
  open Boolean
  open Leq

  open import ArbitraryCategories.Lambda (Kleisli Id) id-cc
  open Lambda

  open BoolCanon
  open NatCanon

  lang  = extract $ (LeqFragment ⊙⟪ ∙-copy ⟫ ArithFragment ⊙⟪ ∙-disjoint ⟫ BoolFragment)
  lang′ = extract $ LambdaFragment ⊙⟪ ∙-disjoint ⟫ LeqFragment ⊙⟪ ∙-copy ⟫ ArithFragment ⊙⟪ ∙-disjoint ⟫ BoolFragment

  run  = interpreter lang
  run′ = interpreter lang′ 

  module _ where

    open Canon (NatCanon ◆ BoolCanon)
    open Fragment lang 

    -- if (1 ≤ 2) then false else true
    expr₁ : μᴵ Expr ([] , boolᵀ)
    expr₁ = I⟨ ((inj₂ (inj₂ ite))
             , (lift (I⟨ (inj₁ leq , lift (I⟨ inj₂ (inj₁ (numv 1)) , lift [] ⟩
                                   ∷ (I⟨ inj₂ (inj₁ (numv 2)) , lift [] ⟩
                                   ∷ []))) ⟩
                           ∷ (I⟨ (inj₂ (inj₂ (boolv false)) , lift []) ⟩
                           ∷ (I⟨ (inj₂ (inj₂ (boolv false)) , lift []) ⟩ ∷ []))))) ⟩

    test₁ : run expr₁ tt ≡ false
    test₁ = refl

  module _ where 

    open Fragment lang′

    -- (λ x . x + 2) 2
    expr₂ : μᴵ Expr ([] , natᵀ)
    expr₂ = I⟨ ((inj₁ app) , (lift (
      I⟨ (inj₁ abs , lift (I⟨ (inj₂ (inj₂ (inj₁ add)) , lift (
        I⟨ inj₁ (var (here refl)) , lift [] ⟩ ∷ (
        I⟨ inj₂ (inj₂ (inj₁ (numv 2))) , lift [] ⟩ ∷
        []))) ⟩ ∷ [])) ⟩ ∷
      (I⟨ ((inj₂ (inj₂ (inj₁ (numv 2)))) , (lift [])) ⟩ ∷ [])))) ⟩

    test₂ : run′ expr₂ tt ≡ 4
    test₂ = refl
  
