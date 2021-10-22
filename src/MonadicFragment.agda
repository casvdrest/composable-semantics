{-# OPTIONS --safe --without-K #-}

open import Box
import Level as L

module MonadicFragment (Ix : Set → Set) ⦃ ix-rel : ∀ {A} → Rel₂ L.0ℓ (Ix A) ⦄ where

open import Data.List
open import Data.List.Relation.Unary.All renaming (map to amap)
open import Data.List.Relation.Binary.Sublist.Propositional

open import Data.Product                 renaming (map to pmap)
open import Data.Maybe                   using (Maybe ; just ; nothing)

open import Relation.Unary               hiding (_⊆_ ; Pred)

open import Core
open import Signature
open import Canon
open import Fragment
open import Structure.Monad

open import Function


module _ where

  --
  -- The sort `Eff` contains monads on `Ix`-indexed sets, parameterized over a set of values and context 
  -- 
  Eff : Set₁
  Eff = ∀ {σ} → (V : μ σ → (Ix (μ σ)) → Set)
              → (Γ : List (μ σ))
              → (Ix (μ σ) → Set) → Ix (μ σ) → Set 

--
-- Bespoke monad/strength record types for the `Eff` type.
-- These are just here to help Agda's inference for implicits. We could
-- (in principle) replace these with the general types for indexed monads, but
-- this results in large amounts of unsolved metas when writing interpreters.
--
module Itf where

  open Canon.ICanon

  record Monadic (M : Eff) : Set₁ where
    field isMonadic : ∀ {σ} {V : μ σ → Ix (μ σ) → Set} {Γ : Ctx (μ σ)} → RawMonad (M V Γ)

    return : ∀ {σ} {V : μ σ → Ix (μ σ) → Set} {Γ : Ctx (μ σ)} {P}
             → ∀[ P ⇒ M V Γ P ]
    return = RawMonad.return isMonadic

    _>>=_ :  ∀ {σ} {V : μ σ → Ix (μ σ) → Set} {Γ : Ctx (μ σ)} {P Q}
             → ∀ {Σ} → M V Γ P Σ → ∀[ P ⇒ M V Γ Q ] → M V Γ Q Σ
    x >>= f = RawMonad.bind isMonadic f x

  open Monadic ⦃...⦄ public

  open Rel₂ ⦃...⦄

  record IsWeakenable (V : Values Ix σ) : Set where 
    field isWk : ∀ {t} → let open Wk R in Weakenable (para (out V) t) 

    wk : ∀ {i i′} → R i i′ → ∀ {t} → para (out V) t i → para (out V) t i′
    wk sub {t} px = Wk.Weakenable.wk (isWk {t}) sub px

  open IsWeakenable ⦃...⦄ public 

  record IsStrong {M : Eff} (mon : Monadic M) : Set₁ where
    field isStr : ∀ {σ} {V : μ σ → Ix (μ σ) → Set} {Γ : Ctx (μ σ)} → let open Wk R in Strength (Monadic.isMonadic mon {σ} {V} {Γ}) 

    _^_ : ∀ {V : Values Ix σ} {Γ P} → ⦃ IsWeakenable V ⦄ → ∀ {t} →  ∀[ M (para (out V)) Γ P ⇒ para (out V) t ⇒ M (para (out V)) Γ (P ∩ (para (out V) t)) ] 
    _^_ ⦃ w ⦄ {t} x y = Wk.Strength._^_ isStr ⦃ IsWeakenable.isWk w {t} ⦄ x y

module _ where

  open Canon.ICanon
  open Rel₂ 

  Expressions : Signature _ → Set₁
  Expressions σ = ∀ {σ′} → ⦃ σ ≼ σ′ ⦄ → ISignature _ (Ctx (μ σ′) × μ σ′) (Ctx (μ σ′) × μ σ′)

  record MonadicFragment (M : Eff) (c : ICanon Ix) : Set₁ where
    field
      exprᵐ   : ISignature _ (Ctx (μ (ity c)) × μ (ity c)) (Ctx (μ (ity c)) × μ (ity c))
      interpᵐ : let open Wk (R (ix-rel {μ (ity c)})) in ⦃ Itf.IsWeakenable (ival c) ⦄ → IAlgebra exprᵐ λ (Γ , t) → ∀[ M (para (out (ival c))) Γ (para (out (ival c)) t) ] 

  open MonadicFragment public

{- Homogeneous and heterogeneous composition operators for monadic fragments 
   
   The implementations are again (virtually) identical, but the operations have 
   slightly different types 
-} 
module _ {M : Eff} where 

  open MonadicFragment
  open Necessary
  open □

  fcompose-homᵐ : ∀[ MonadicFragment M ⇒ MonadicFragment M ⇒ MonadicFragment M ]   
  exprᵐ   (fcompose-homᵐ φ₁ φ₂) = exprᵐ   φ₁ :++: exprᵐ φ₂
  interpᵐ (fcompose-homᵐ φ₁ φ₂) = interpᵐ φ₁ :⊕: interpᵐ φ₂  

  fcomposeᵐ : ∀ {c₁ c₂ c} → c₁ ∙ c₂ ≣ c → □ (MonadicFragment M) c₁ → □ (MonadicFragment M) c₂ → □ (MonadicFragment M) c
  fcomposeᵐ sep φ₁ φ₂ = □-distr-⇒ (□-lift fcompose-homᵐ (future (duplicate φ₁) (∙-⊑₁ sep)))
                                                        (future (duplicate φ₂) (∙-⊑₂ sep))

  infixr 5 fcomposeᵐ
  syntax fcomposeᵐ sep φ₁ φ₂ = φ₁ ⊙⟨ sep ⟩ᵐ φ₂


{- Extract executable interpᵐreters from extensible monadic fragments -} 
module _ {M : Eff} where 

  open Necessary
  open MonadicFragment
  open ICanon
  open □

  closeᵐ : ∀ {c} → ⦃ Itf.IsWeakenable (ival c) ⦄ → □ (MonadicFragment M) c → MonadicFragment M c 
  exprᵐ   (closeᵐ {_} ⦃ w ⦄ x) = exprᵐ (future x ⊑-refl)
  interpᵐ (closeᵐ {_} ⦃ w ⦄ x) = interpᵐ (future x ⊑-refl) ⦃ w ⦄

  open ICanon
  open MonadicFragment

  module _ {c : ICanon Ix} ⦃ _ : Itf.IsWeakenable (ival c) ⦄ where 

    extractInterpᵐ : (φ : MonadicFragment M c) → ∀ {Γ t} → μᴵ (exprᵐ φ) (Γ , t) → ∀[ M (para (out (ival c))) Γ (para (out (ival c)) t) ] 
    extractInterpᵐ φ = foldᴵ (interpᵐ φ)

  open ICanon
  open MonadicFragment


  module _ {c} (φ : □ (MonadicFragment M) c) {Γ} {t : μ (ity c)} where 

    closeFragment : ⦃ _ : Itf.IsWeakenable (ival c) ⦄ → μᴵ (exprᵐ (closeᵐ φ)) (Γ , t) → ∀[ M (para (out (ival c))) Γ (para (out (ival c)) t) ]
    closeFragment = foldᴵ (interpᵐ (closeᵐ φ))

--
-- Fragment lifting
--
module _ where

  open Canon.ICanon

  open IFragment
  open MonadicFragment
  open Itf
  
  module _   (M : Eff) ⦃ mon : Monadic M ⦄ ⦃ _   : IsStrong mon ⦄ where

    open IsStrong ⦃...⦄

    sequence : ∀ {c} {Γ} {xs : List (μ (ity c))}
               → ⦃ IsWeakenable (ival c) ⦄
               → All (λ (Γ , t) → ∀[ M (para (out (ival c))) Γ (para (out (ival c)) t) ]) (Data.List.map (Γ ,_) xs)
               → ∀[ M (para (out (ival c))) Γ ((λ Σ → All (λ t → (para (out (ival c))) t Σ) xs)) ]
    sequence {xs = []}        []         = return []
    sequence {xs = ⟨ _ ⟩ ∷ _} (px ∷ pxs) = do
      v         ← px
      (vs , v′) ← sequence pxs ^ v
      return (v′ ∷ vs)

    open Necessary
    open □

    lift : ∀[ □ IFragment ⇒ □ (MonadicFragment M) ]
    Shapeᴵ  (exprᵐ (future (lift φ) r)) (Γ , t)   = Shapeᴵ (iexpr (future φ r)) t
    Indices (exprᵐ (future (lift φ) r)) {Γ , _} s = Data.List.map (Γ ,_) (Indices (iexpr (future φ r)) s)
    ialg (interpᵐ (future (lift φ) r)) (c , L.lift vxs) = do
      vs ← sequence vxs
      return (ialg (iinterp (future φ r)) (c , L.lift vs))


