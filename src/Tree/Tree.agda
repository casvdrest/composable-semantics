{-# OPTIONS --safe --without-K #-}

module Tree.Tree where

open import Core
open import Signature
open import Structure.Monad

open import Data.Nat
open import Data.Vec hiding (_∷ʳ_ ; lookup ; updateAt)
open import Data.Product
open import Data.List.Relation.Binary.Sublist.Propositional
open import Data.List.Relation.Unary.All renaming (map to map-all)

open import Relation.Unary using (IUniversal ; _⇒_ ; _∩_)

open import Function

module _ where

  data Err (A : Set) : Set where
    result  : A → Err A
    timeout : Err A
    error   : Err A

  module _ {σ : Signature _} where 

    open Wk {A = Sto (μ σ)} _⊆_
    open import Relation.Unary.Closure.Base {A = Sto (μ σ)} _⊆_

    record Sig : Set₁ where
      constructor mkSig
      field
        Cmd : Ctx (μ σ) → ℕ → Sto (μ σ) → Set
        loc : (Γ : Ctx (μ σ)) {n : ℕ} {Σ : Sto (μ σ)} (s : Cmd Γ n Σ) → Ctx (μ σ)
        Sub : ∀ {Γ n} {i : Sto (μ σ)} → Cmd Γ n i → Sto (μ σ) → Set
        Res : ∀ {Γ n} {i : Sto (μ σ)} → Cmd Γ n i → Sto (μ σ) → Set 

    module Tree (sig : Sig) where

      open Sig sig


      Vec' : ℕ → (A : Set) → Set
      Vec' n A = Vec A n

      -------------------------------------------
      --- a free monad with sub-continuations ---
      -------------------------------------------

      data Tree (Γ : Ctx (μ σ)) (V : Pred (Sto (μ σ))) : Pred (Sto (μ σ)) where
        var : ∀[ V ⇒ Tree Γ V ]
        op  : ∀ {Σ : Sto (μ σ)}
              → (c : ((Cmd Γ n)) Σ)
              → (Vec' n ∘ Tree (loc Γ c) ((Sub c)) ⇒ (□ (Res c ⇒ Tree Γ V) ⇒ Tree Γ V)) Σ 

      open RawMonad
  
      bind-tree : ∀ {Γ} → ∀[ P ⇒ Tree Γ Q ] → ∀[ Tree Γ P ⇒ Tree Γ Q ]
      bind-tree f (var x) = f x
      bind-tree f (op c subs k) = op c subs λ σ v → bind-tree f (k σ v)

      instance
        tree-monad : ∀ {Γ} → RawMonad (Tree Γ)
        return tree-monad = var
        bind   tree-monad = bind-tree

      open Weakenable ⦃...⦄

      tree-strength : ∀ {P Q Γ} → ⦃ Weakenable Q ⦄ → ∀[ Tree Γ P ⇒ Q ⇒ Tree Γ (P ∩ Q) ]
      tree-strength (var x)       y = var (x , y)
      tree-strength (op c subs k) y = op c subs (λ σ r → tree-strength (k σ r) (wk σ y))
    
      open Strength

      instance tree-strong : ∀ {Γ : Ctx (μ σ)} → Strength (tree-monad {Γ})
      Wk.Strength._^_ tree-strong = tree-strength


      mutual
        fold-tree : {F : Ctx (μ σ) → Pred (Sto (μ σ)) → Pred (Sto (μ σ))}
             → (base : ∀ {Γ V}
                     → ∀[ V ⇒ F Γ V ])
             → (alg  : ∀ {Γ Σ V n}
                       → (c : (Cmd Γ n) Σ)
                       → Vec' n (F (loc Γ c) (Sub c) Σ)
                       → □ ((Res c) ⇒ F Γ V) Σ
                       → F Γ V Σ)
             → ∀ {Γ V} → ∀[ Tree Γ V ⇒ F Γ V ]
        fold-tree base alg (var x) = base x
        fold-tree base alg (op c subs k) = alg c (map-fold-tree base alg subs) λ σ r → fold-tree base alg (k σ r) 

        map-fold-tree : {F : Ctx (μ σ) → Pred (Sto (μ σ)) → Pred (Sto (μ σ))}
                → (base : ∀ {Γ V} → ∀[ V ⇒ F Γ V ])
                → (alg  : ∀ {Γ Σ V n}
                       → (c : (Cmd Γ n) Σ)
                       → Vec' n (F (loc Γ c) ((Sub c)) Σ)
                       → □ ((Res c) ⇒ F Γ V) Σ
                       → F Γ V Σ)
                → ∀ {Γ V n} → ∀[ Vec' n ∘ Tree Γ V ⇒ Vec' n ∘ F Γ V ]  
        map-fold-tree base alg [] = []
        map-fold-tree base alg (x ∷ xs) = fold-tree base alg x ∷ map-fold-tree base alg xs


      liftT : ∀ {Γ Σ n} (c : (Cmd Γ n) Σ) (subs : Vec (Tree (loc Γ c) (Sub c) Σ) n) →
              Tree Γ (Res c) Σ
      liftT s subs = op s subs λ σ → var
