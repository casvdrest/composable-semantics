{-# OPTIONS --safe --without-K --overlapping-instances #-}

module Test.Language1 where

open import Prelude

open import Canon
open import Canon.Function
open import Canon.Ref
open import Canon.Nat

open import Tree.Tree
open import Tree.Handle
open import Tree.Instances

open import Languages.Language1


import Level as L


module _ where

  open ICanon

  open import Data.Sum

  canon~ = icanon {Sto} _ (mk (out FunctionVal ⊕ (out ReferenceVal ⊕ out (liftVal {Ix = Sto} NatVal))))

  instance val-wk : Itf.IsWeakenable Sto (ival canon~)
  Wk.Weakenable.wk (Itf.IsWeakenable.isWk val-wk {⟨ inj₁ fun , L.lift (s ∷ t ∷ []) ⟩}) σ v = extend σ v
  Wk.Weakenable.wk (Itf.IsWeakenable.isWk val-wk {⟨ inj₂ (inj₁ ref) , L.lift (t ∷ []) ⟩}) σ v = extend σ v
  Wk.Weakenable.wk (Itf.IsWeakenable.isWk val-wk {⟨ inj₂ (inj₂ nat) , L.lift [] ⟩}) σ v = v

  lang~ : MonadicFragment Sto TreeEff canon~
  lang~ = closeᵐ Sto (lang _) 

  open MonadicFragment

  Val = para (out (ival canon~))
  Expr = μᴵ (exprᵐ lang~)
  open Wk {A = Sto (μ (ity canon~)) } _⊆_ 
  open Itf.IsWeakenable ⦃...⦄

  interpLang : ∀ {Γ t} → μᴵ (exprᵐ lang~) (Γ , t) → ℕ → ∀[ M Val Γ ((Val t)) ]
  interpLang tm fuel = run _ ⦃ λ {t} →  Itf.IsWeakenable.isWk val-wk {t}  ⦄ fuel (extractInterpᵐ Sto lang~ tm)

  open NatCanon
  open import Data.Maybe

  inspect : ∀[ M Val [] (Val nat′) ] → Err ℕ
  inspect f with f [] []
  ... | timeout = timeout
  ... | error   = error 
  ... | result (_ , _ , n , _) = result n

  variable Γ : Ctx (μ (ity canon~))
           s t : μ (ity canon~)

  num' : ℕ → Expr (Γ , nat′)
  num' n = I⟨ (inj₂ (inj₂ (inj₁ (num n))) , (L.lift [])) ⟩

  add' : Expr (Γ , nat′) → Expr (Γ , nat′) → Expr (Γ , nat′)
  add' n m = I⟨ (inj₂ (inj₂ (inj₁ add)) , L.lift (n ∷ m ∷ [])) ⟩


  open RefCanon

  init' : Expr (Γ , t) → Expr (Γ , ref′ t)
  init' x = I⟨ inj₂ (inj₁ init) , L.lift (x ∷ []) ⟩ 

  deref' : Expr (Γ , ref′ t) → Expr (Γ , t)
  deref' x = I⟨ inj₂ (inj₁ deref) , L.lift (x ∷ []) ⟩

  update' : Expr (Γ , ref′ t) → Expr (Γ , t) → Expr (Γ , t)
  update' x v = I⟨ ((inj₂ (inj₁ update)) , (L.lift (x ∷ v ∷ []))) ⟩


  open FunCanon

  var' : t ∈ Γ → Expr (Γ , t)
  var' x = I⟨ (inj₁ (inj₁ (var x)) , L.lift []) ⟩

  abs' : Expr (s ∷ Γ , t) → Expr (Γ , fun′ s t)
  abs' x = I⟨ (inj₁ (inj₁ abs) , L.lift (x ∷ [])) ⟩

  app' : Expr (Γ , fun′ s t) → Expr (Γ , s) → Expr (Γ , t)
  app' f x  = I⟨ (inj₁ (inj₁ app) , L.lift (f ∷ x ∷ [])) ⟩

  fix' : Expr (s ∷ fun′ s t ∷ Γ , t) → Expr (Γ , fun′ s t)
  fix' f = I⟨ ((inj₁ (inj₂ fix)) , L.lift (f ∷ [])) ⟩

  natcase' : Expr (Γ , nat′) → Expr (Γ , t) → Expr (nat′ ∷ Γ , t) → Expr (Γ , t)
  natcase' n z s = I⟨ (inj₂ (inj₂ (inj₂ (inj₁ (natcase _)))) , L.lift (n ∷ z ∷ s ∷ [])) ⟩

  throw' : Expr (Γ , t)
  throw' = I⟨ (inj₂ (inj₂ (inj₂ (inj₂ (error _)))) , L.lift []) ⟩

  try' : Expr (Γ , t) → Expr (Γ , t) → Expr (Γ , t)
  try' t c = I⟨ (inj₂ (inj₂ (inj₂ (inj₂ (try _)))) , L.lift (t ∷ c ∷ [])) ⟩

module _ where

  open import Relation.Binary.PropositionalEquality hiding (inspect)
  open import Data.List.Relation.Unary.Any
  open import Data.Maybe

  open import Canon.Nat
  open NatCanon


  -- (λ n . n + 10) 10   ===> 20 
  expr₁ : Expr ([] , nat′)
  expr₁ = app' (abs' (add' (var' (here refl)) (num' 10))) (num' 10)

  test₁ : inspect (interpLang expr₁ 10) ≡ result 20
  test₁ = refl

  -- (λ n . *n + 10) (init 10)  ===> 20 (`n` is a reference)
  expr₂ : Expr ([] , nat′)
  expr₂ = app' (abs' (add' (deref' (var' (here refl))) (num' 10))) (init' (num' 10))

  test₂ : inspect (interpLang expr₂ 10) ≡ result 20
  test₂ = refl

  -- (λ n . (λ m . (λ x . (λ _ . deref x) (update x (add n m))) (init 0)) 10) 10  ==> add two numbers, but store the result in a reference 
  expr₃ : Expr ([] , nat′)
  expr₃ =
    app' (abs' (app' (abs' (app' (abs' (app' (abs'
      (deref' (var' (there (here refl)))))
        (update' (var' (here refl)) (add' (var' (there (here refl)))
          (var' (there (there (here refl)))))))) (init' (num' 0)))) (num' 10))) (num' 10)

  test₃ : inspect (interpLang expr₃ 10) ≡ result 20
  test₃ = refl
 
  expr₄ : Expr ([] , nat′)
  expr₄ = app' throw' (num' 10)

  test₄ : inspect (interpLang expr₄ 10) ≡ error
  test₄ = refl


  expr₅ : Expr ([] , nat′)
  expr₅ = try' (num' 10) (num' 11)

  test₅ : inspect (interpLang expr₅ 10) ≡ result 10
  test₅ = refl


  expr₆ : Expr ([] , nat′)
  expr₆ = try' (app' (abs' throw') (num' 10)) (add' (num' 10) (num' 11))

  test₆ : inspect (interpLang expr₆ 10) ≡ result 21
  test₆ = refl


  expr₇ : Expr ([] , nat′)
  expr₇ = app' (abs' (try' (app' (abs' throw') (update' (var' (here refl)) (num' 1))) (app' (abs' (deref' (var' (there (here refl))))) (update' (var' (here refl)) (add' (deref' (var' (here refl))) (num' 1)))))) (init' (num' 0))

  test₇ : inspect (interpLang expr₇ 10) ≡ result 1
  test₇ = refl

  expr₈ : Expr ([] , nat′)
  expr₈ = app' (fix' (natcase' (var' (here refl))
                               (num' 0)
                               (add' (num' 2) (app' (var' (there (there (here refl))) )
                                                    (var' (here refl)))))) (num' 10)

  test₈ : inspect (interpLang expr₈ 30) ≡ result 20
  test₈ = refl

  expr₉ : Expr ([] , nat′)
  expr₉ =
    app'
      (abs' (deref'
        (app'
          (fix'
            (natcase'
              (var' (here refl))
              (var' (there (there (here refl))))
              (app'
                (abs'
                  (app'
                    (abs' (var' (there (here refl))))
                      (update'
                        (var' (here refl))
                        (add' (num' 2)
                          (deref'
                            (app'
                             (var' (there (there (there (here refl)))))
                             (var' (there (here refl)))))))))
                  (var' (there (there (there (here refl))))))))
          (num' 10))))
      (init' (num' 0))

  test₉ : inspect (interpLang expr₉ 60) ≡ result 20
  test₉ = refl

