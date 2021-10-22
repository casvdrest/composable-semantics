{-# OPTIONS --safe --without-K #-}

module Tree.Handle where

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
open import Tree.Tree
open import Canon

module _ {σ : Signature _} (V : μ σ → Sto (μ σ) → Set) where

  open import Data.List.Relation.Binary.Sublist.Propositional renaming (lookup to extend)
  open import Relation.Unary.Closure.Base {A = Sto (μ σ)}                    _⊆_
  open        Closure {A = Sto (μ σ)}                                        _⊆_ ⊆-isPreorder

  open import Data.Empty
  open import Data.List hiding (_∷ʳ_)
  open import Data.List.Membership.Propositional

  data LambdaOp (Γ : Ctx (μ σ)) : ℕ → Sto (μ σ) → Set where
    ask-op   :                             ∀[                                      LambdaOp Γ 0 ]
    local-op : ∀ {Γ′}  → (t : μ σ)       → ∀[ □ (Env (μ σ) V Γ ⇒ Env (μ σ) V Γ′) ⇒ LambdaOp Γ 1 ]
    close-op :           (s t : μ σ)     → ∀[                                      LambdaOp Γ 1 ]
    apply-op : ∀ {s t} →                   ∀[ (closure s t ∈_) ⇒ V s             ⇒ LambdaOp Γ 0 ]
    init-op  : {t : μ σ}                 → ∀[ V t                                ⇒ LambdaOp Γ 0 ]
    get-op   : {t : μ σ}                 → ∀[ (value t ∈_)                       ⇒ LambdaOp Γ 0 ]
    put-op   : {t : μ σ}                 → ∀[ (value t ∈_)   ⇒ V t               ⇒ LambdaOp Γ 0 ]
    throw-op : {t : μ σ}                 → ∀[                                      LambdaOp Γ 0 ]
    try-op   : {t : μ σ}                 → ∀[                                      LambdaOp Γ 2 ]
    fix-op   : {s t : μ σ} → (_↦_ : (s t : μ σ ) → μ σ) → ∀[ (closure s t ∈_) ⇒ V (s ↦ t) ]
               → ∀[                                      LambdaOp Γ 1 ]
  
  loc : ∀ (Γ : Ctx (μ σ)) {n : ℕ} {Σ} (s : LambdaOp Γ n Σ) → Ctx (μ σ)
  loc Γ (close-op s t) = s ∷ Γ
  loc Γ (fix-op {s} {t} fn _) = s ∷ fn s t ∷ Γ
  loc Γ (local-op {Γ′} _ _) = Γ′
  loc Γ _              = Γ
  
  Sub : ∀ {Γ Σ n} (s : LambdaOp Γ n Σ) → Pred (Sto (μ σ))
  Sub (close-op s t) = V t
  Sub (local-op t f) = V t
  Sub (try-op {t}  ) = V t
  Sub (fix-op {s} {t} _ _) = V t
  Sub _              _ = ⊥

  open import Data.Unit

  Res : ∀ {Γ Σ n} (s : LambdaOp Γ n Σ) → Pred (Sto (μ σ))
  Res {Γ} ask-op             = Env (μ σ) V Γ
  Res (local-op t f)         = V t 
  Res (close-op s t)         = closure s t ∈_
  Res (apply-op {t = t} _ _) = V t
  Res (init-op {t} _)        = value t ∈_
  Res (get-op {t} _)         = V t
  Res (put-op {t} _ _)       = λ _ → ⊤
  Res (throw-op {t})         = V t
  Res (try-op {t})           = V t
  Res (fix-op {s} {t} _ _)       = closure s t ∈_ 
    

  LambdaSig : Sig
  LambdaSig = mkSig LambdaOp loc Sub Res


  open import Data.List.Membership.Propositional
  open import Relation.Binary.PropositionalEquality
  open import Data.Maybe

  open Wk {A = Sto (μ σ)} _⊆_
    
  module _ ⦃ w : ∀[ Weakenable ∘ V ] ⦄ where

    open Tree LambdaSig

    open Weakenable ⦃...⦄

    widen-cmd : ∀ {Σ Σ′ Γ n} → Σ ⊆ Σ′ → LambdaOp Γ n Σ → LambdaOp Γ n Σ′ 
    widen-cmd σ ask-op = ask-op
    widen-cmd σ (local-op t f) = local-op t λ σ′ nv → f (⊆-trans σ σ′) nv
    widen-cmd σ (close-op s t) = close-op s t
    widen-cmd σ (apply-op v₁ v₂) = apply-op (extend σ v₁) (wk σ v₂)
    widen-cmd σ (init-op x) = init-op (wk σ x)
    widen-cmd σ (get-op x) = get-op (extend σ x)
    widen-cmd σ (put-op loc v) = put-op (extend σ loc) (wk σ v)
    widen-cmd σ (throw-op {t}) = throw-op {t = t}
    widen-cmd σ (try-op {t}) = try-op {t = t}
    widen-cmd σ (fix-op {s} {t} f ↑)     = fix-op {_}{s} {t} f ↑

    widen-res : ∀ {Γ n Σ Σ′ Σ′′} → (c : Sig.Cmd LambdaSig Γ n Σ) → (σ : Σ ⊆ Σ′) → Res (widen-cmd σ c) Σ′′ → Res c Σ′′
    widen-res ask-op σ x = x
    widen-res (local-op t x₁) σ x = x
    widen-res (close-op s t) σ x = x
    widen-res (apply-op x₁ x₂) σ x = x
    widen-res (init-op x₁) σ x = x
    widen-res (get-op x₁) σ x = x
    widen-res (put-op x₁ x₂) σ x = x
    widen-res throw-op σ x = x
    widen-res try-op σ x = x
    widen-res (fix-op _ _) σ x = x

    mutual 
      widenTree : ∀ {Γ Σ Σ′ P} → ⦃ Weakenable P ⦄ →  Σ ⊆ Σ′ → Tree Γ P Σ → Tree Γ P Σ′
      widenTree σ (var v)       = var (wk σ v)
      widenTree σ (op c subs k) = op (widen-cmd σ c) (map-widen c σ subs) λ σ′ x → k (⊆-trans σ σ′) (widen-res c σ x)

      map-widen : ∀ {Γ Σ Σ′ m n} → (c : Sig.Cmd LambdaSig Γ m Σ ) → (σ : Σ ⊆ Σ′) → Vec (Tree (loc Γ c) (Sub c) Σ) n → Vec (Tree (loc Γ (widen-cmd σ c)) (Sub (widen-cmd σ c)) Σ′) n 
      map-widen c σ [] = []
      map-widen c σ (x ∷ xs) = widen-sub c σ x ∷ map-widen c σ xs

      widen-sub : ∀ {Γ Σ Σ′ n} → (c : Sig.Cmd LambdaSig Γ n Σ ) → (σ : Σ ⊆ Σ′) → Tree (loc Γ c) (Sub c) Σ → Tree (loc Γ (widen-cmd σ c)) (Sub (widen-cmd σ c)) Σ′
      widen-sub ask-op σ x = widenTree ⦃ record { wk = λ _ x → x } ⦄ σ x
      widen-sub (local-op t f) σ x = widenTree σ x
      widen-sub (close-op s t) σ x = widenTree σ x
      widen-sub (apply-op x₁ x₂) σ x = widenTree ⦃ record { wk = λ _ x → x } ⦄ σ x
      widen-sub (init-op x₁) σ x = widenTree ⦃ record { wk = λ _ x → x } ⦄ σ x
      widen-sub (get-op x₁) σ x = widenTree ⦃ record { wk = λ _ x → x } ⦄ σ x
      widen-sub (put-op x₁ x₂) σ x = widenTree ⦃ record { wk = λ _ x → x } ⦄ σ x
      widen-sub throw-op σ x = widenTree ⦃ record { wk = λ _ x → x } ⦄ σ x
      widen-sub try-op σ x = widenTree σ x
      widen-sub (fix-op f ↑) σ x = widenTree σ x 

  open import Data.List hiding (_∷ʳ_ ; lookup)
  open import Data.List.Relation.Unary.All renaming (map to map-all ; lookup to lookupᵃ)
  open import Data.List.Relation.Unary.Any using (here ; there)
  import Level as L


  open import Category.Functor

  instance except-functor : RawFunctor Err
  (except-functor RawFunctor.<$> f) (result x) = result (f x)
  (except-functor RawFunctor.<$> f) timeout = timeout
  (except-functor RawFunctor.<$> f) error = error

  open RawMonad ⦃...⦄
  open RawFunctor ⦃...⦄

  fmap = _<$>_

  open Tree LambdaSig

  StoreValue : Cell (μ σ) → Pred (Sto (μ σ))
  StoreValue (value t) Σ = V t Σ
  StoreValue (closure s t) Σ = ∃₂ λ Γ (E : Env (μ σ) V Γ Σ) → Tree (s ∷ Γ) ((V t)) Σ

  Store : Pred (Sto (μ σ))
  Store Σ = All (λ c → (StoreValue c) Σ) Σ
                                         
  -- TODO : `M` is a strong monad ?
  M : Ctx (μ σ) → Pred (Sto (μ σ)) → Pred (Sto (μ σ))
  M Γ P = Env (μ σ) V Γ ⇒ Store ⇒ Err ∘ (λ Σ → ∃ λ Σ′ → Σ ⊆ Σ′ × P Σ′ × Store Σ′)

  module _ ⦃ w : ∀[ Weakenable ∘ V ] ⦄ where

    open Weakenable ⦃...⦄

    wk-storeval : ∀ {Σ Σ′} → Σ ⊆ Σ′ → {c : Cell (μ σ)} → StoreValue c Σ → StoreValue c Σ′
    wk-storeval {Σ₁} {Σ′} σ {value s} v = wk σ v
    wk-storeval {Σ₁} {Σ′} σ {closure s t} (Γ , nv , tm) = Γ , map-all (wk σ) nv , widenTree σ tm

    wk-store : ∀ {Σ Σ′} → Σ ⊆ Σ′ → Store Σ → All (λ c → StoreValue c Σ′) Σ 
    wk-store σ = map-all (λ {x} sv → wk-storeval σ {x} sv)

    run : ∀ {Γ P} → ℕ → ∀[ Tree Γ P ⇒ M Γ P ] 
    run zero t nv st = timeout
    run fuel@(suc n) (Tree.var x) nv μ = result (_ , ⊆-refl , x , μ)

    -- Reader.ask
    run fuel@(suc n) (Tree.op ask-op [] k) nv μ
      = run fuel (k ⊆-refl nv) nv μ

    -- Reader.local 
    run fuel@(suc n) (Tree.op (local-op t f) (tm ∷ []) k) nv μ
      with run n tm (f ⊆-refl nv) μ
    ... | result (st , σ , v , μ′)
      = fmap (λ (_ , σ′ , v′ , μ′′) → _ , ((⊆-trans σ σ′) , v′ , μ′′))
               (run n (k σ v) (map-all (wk σ) nv) μ′)
    ... | timeout = timeout
    ... | error = error

    -- Lambda.close 
    run fuel@(suc n) (Tree.op (close-op s t) (tm ∷ []) k) nv μ
      with run n (k (closure s t ∷ʳ ⊆-refl) (here refl))
                   (map-all (wk (_ ∷ʳ ⊆-refl)) nv) 
                   ((_ , map-all (wk (_ ∷ʳ ⊆-refl)) nv , widenTree (_ ∷ʳ ⊆-refl) tm) ∷ wk-store (_ ∷ʳ ⊆-refl) μ) 
    ... | result (st′ , σ′ , v , μ′) = result (st′ , (⊆-trans (_ ∷ʳ ⊆-refl) σ′ , v , μ′))
    ... | timeout = timeout
    ... | error   = error 

    -- Lambda.apply 
    run fuel@(suc n) (Tree.op (apply-op v₁ v₂) [] k) nv μ
      with lookupᵃ μ v₁
    ... | Γ , nv′ , tm = case (run n tm (v₂ ∷ nv′) μ) of λ where
      timeout → timeout
      error   → error
      (result (st′ , σ′ , v′ , μ′)) →
        fmap (λ (st′′ , σ′′ , v′′ , μ′′) → st′′ , ⊆-trans σ′ σ′′ , v′′ , μ′′)
             (run n (k σ′ v′) (map-all (wk σ′) nv) μ′)

    -- MonotoneState.alloc
    run fuel@(suc n) (Tree.op (init-op v) [] k) nv μ
      with run fuel (k (_ ∷ʳ ⊆-refl) (here refl))
                    (map-all (wk (_ ∷ʳ ⊆-refl)) nv)
                    (wk (_ ∷ʳ ⊆-refl) v ∷ wk-store (_ ∷ʳ ⊆-refl) μ) 
    ... | timeout = timeout
    ... | error   = error 
    ... | result (st′ , σ′ , v′ , μ′) = result (st′ , ⊆-trans (_ ∷ʳ ⊆-refl) σ′ , v′ , μ′)

    -- MonotoneState.get
    run fuel@(suc n) (Tree.op (get-op loc) [] k) nv μ
      = run fuel (k ⊆-refl (lookupᵃ μ loc)) nv μ 
                                               
    -- MonotoneState.put
    run fuel@(suc n) (Tree.op (put-op loc v) [] k) nv μ
      = run fuel (k ⊆-refl tt) nv (updateAt loc (λ _ → v) μ)

    -- Except.throw
    run fuel@(suc n) (Tree.op (throw-op {t}) [] k) nv μ
      = error

    -- Except.try
    run fuel@(suc n) (Tree.op (try-op {t}) (tm₁ ∷ tm₂ ∷ []) k) nv μ
      with run n tm₁ nv μ
    ... | timeout  = timeout
    ... | error    =
      case run n tm₂ nv μ of λ where
        timeout    → timeout
        error      → error
        (result (st′ , σ′ , v′ , μ′)) →
          fmap (λ (st′′ , σ′′ , v′′ , μ′′) → st′′ , ⊆-trans σ′ σ′′ , v′′ , μ′′)
               (run n (k σ′ v′) (map-all (wk σ′) nv) μ′)
    ... | result (st′ , σ′ , v′ , μ′) = fmap (λ (st′′ , σ′′ , v′′ , μ′′) → st′′ , ⊆-trans σ′ σ′′ , v′′ , μ′′)
                                             (run n (k σ′ v′) (map-all (wk σ′) nv) μ′)

    run fuel@(suc n) (Tree.op (fix-op f ↑) (tm ∷ []) k) nv μ
      with run fuel (k (closure _ _ ∷ʳ ⊆-refl) (here refl)) (map-all (wk (_ ∷ʳ ⊆-refl)) nv)
                    ((_ , (↑ (here refl) ∷ map-all (wk (_ ∷ʳ ⊆-refl)) nv , widenTree (_ ∷ʳ ⊆-refl) tm ))
                    ∷ wk-store (_ ∷ʳ ⊆-refl) μ)
    ... | result (st′ , σ′ , v′ , μ′) = result (st′ , ⊆-trans (_ ∷ʳ ⊆-refl) σ′ , v′ , μ′)
    ... | timeout = timeout
    ... | error = error



