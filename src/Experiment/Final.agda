module Experiment.Final where

open import Data.Product
open import Data.Nat renaming (_+_ to _+ℕ_ ; _*_ to _*ℕ_)
open import Relation.Unary
open import Function
open import Data.Bool renaming (if_then_else_ to if'_then_else_)
open import Data.List hiding (and ; [_])

open import Experiment.ListSyntax

open import Level renaming (suc to sucL)

variable A B C : Set

data _≡_ (x : A) : A → Set where
  refl : x ≡ x
  
module _ where
  
  data Type : Set where
    nat bool : Type
    _↦_ : (s t : Type) → Type

  record Fragment : Set₁ where
    field Semantics  : (Type → Set) → Set
  
  open Fragment

  record Instance (repr : Type → Set) (f : Fragment) : Set where
    field inst : f .Semantics repr

  open Instance 

  Term : List Fragment → Type → (Type → Set) → Set
  Term fs t repr = go repr fs t
    where go : (Type → Set) → List Fragment → Type → Set
          go repr [] t       = repr t
          go repr (f ∷ fs) t = ⦃ f .Semantics repr ⦄ → go repr fs t

  data All {ℓ} {A : Set ℓ} (P : A → Set) : List A → Set (sucL ℓ) where 
    []  : All P []
    _∷_ : ∀ {x xs} → P x → All P xs → All P (x ∷ xs) 

  ⟦_⟧ : ∀ {repr : Type → Set} {fs : List Fragment} → All (Instance repr) fs → ∀ {t} → Term fs t repr → repr t 
  ⟦ []     ⟧ x = x 
  ⟦ i ∷ is ⟧ x = ⟦ is ⟧ (x ⦃ i .inst ⦄)

  record ArithSem (repr : Type → Set) : Set where
    field _+_ : repr nat → repr nat → repr nat 
          _*_ : repr nat → repr nat → repr nat
          `n  : ℕ → repr nat
    
  arithF : Fragment 
  arithF .Semantics = ArithSem

  record BoolSem (repr : Type → Set) : Set where
    field if_then_else_ : ∀ {t} → repr bool → repr t → repr t → repr t
          and           : (x y : repr bool) → repr bool
          `b            : Bool → repr bool   
   
  boolF : Fragment
  boolF .Semantics = BoolSem

  record NatCaseSem (repr : Type → Set) : Set where
    field ncase_of_∣_ : ∀ {t} → repr nat → repr t → (repr nat → repr t) → repr t

  ncaseF  : Fragment
  ncaseF .Semantics = NatCaseSem

  

{- Example terms -}
module _ where

  open BoolSem    ⦃...⦄
  open ArithSem   ⦃...⦄
  open NatCaseSem ⦃...⦄

  term₁ : ∀[ Term [ arithF ] nat ]
  term₁ = (`n 10 * `n 11) + `n 2

  term₂ : ∀[ Term [ boolF ] bool ] 
  term₂ = if `b true then and (`b true) (`b false) else `b true

  term₃ : ∀[ Term [ arithF ] nat ]
  term₃ = let double = λ x → x + x in double (`n 2 * `n 3)

  term₄ : ∀[ Term [ arithF , boolF ] nat ]
  term₄ = (if `b true then (λ n → n + n) (`n 10) else `n 0) + `n 10

  term₅ : ∀[ Term [ arithF , boolF , ncaseF ] bool ]
  term₅ =
    let iszero n = ncase n of `b true ∣ λ _ → `b false
    in  iszero (`n 10)
  

{- Interpretation semantics -} 
module _ where

  open Instance 

  Eval : Type → Set
  Eval nat     = ℕ
  Eval bool    = Bool
  Eval (s ↦ t) = Eval s → Eval t 

  evalBool : Instance Eval boolF
  BoolSem.if_then_else_ (inst evalBool) = λ c t e → if' c then t else e 
  BoolSem.and (inst evalBool)           = λ x y → x ∧ y
  BoolSem.`b (inst evalBool)            = id

  evalArith : Instance Eval arithF
  ArithSem._+_ (Instance.inst evalArith) = λ n m → n +ℕ m 
  ArithSem._*_ (Instance.inst evalArith) = λ n m → n *ℕ m
  ArithSem.`n  (Instance.inst evalArith) = id

  evalNCase : Instance Eval ncaseF
  NatCaseSem.ncase_of_∣_ (inst evalNCase) = λ n z s → case n of λ { zero → z ; (suc n) → s n }

  test₁ : ⟦ evalArith ∷ [] ⟧ term₁ ≡ 112
  test₁ = refl

  test₂ : ⟦ evalBool ∷ [] ⟧ term₂ ≡ false
  test₂ = refl

  test₃ : ⟦ evalArith ∷ [] ⟧ term₃ ≡ 12
  test₃ = refl

  test₄ : ⟦ evalArith ∷ evalBool ∷ [] ⟧ term₄ ≡ 30
  test₄ = refl

  test₅ : ⟦ evalArith ∷ evalBool ∷ evalNCase ∷ [] ⟧ term₅ ≡ false 
  test₅ = refl
