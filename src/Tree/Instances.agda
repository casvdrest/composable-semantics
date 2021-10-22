{-# OPTIONS --safe --without-K #-}

module Tree.Instances where 

open import Core
open import Tree.Tree
open import Tree.Handle

open import Interface.Except
open import Interface.Lambda
open import Interface.Reader
open import Interface.General
open import Interface.MonotoneState

open import Data.Vec

open import Function

{- `Tree` instantiates the relevant interfaces -} 
module _ where

  open Tree
  open import MonadicFragment Sto
  open Itf
  
  TreeEff : Eff 
  TreeEff = Tree ∘ LambdaSig

  instance tree-monadic : Monadic TreeEff 
  Monadic.isMonadic tree-monadic = Tree.tree-monad (LambdaSig _)

  open import Interface.Lambda
  open import Interface.Reader
  open import Interface.MonotoneState
  open import Interface.General

  import Data.List.Relation.Binary.Sublist.Propositional as SL
  open import Data.List.Relation.Unary.All renaming (map to map-all)

  instance tree-lambda : Lambda TreeEff
  Lambda.abstr tree-lambda {s = s} {t} tm = op (close-op s t) (tm ∷ []) λ _ → var
  Lambda.apply tree-lambda f x = op (apply-op f x) [] λ _ → var

  instance tree-reader : Reader Sto TreeEff
  Reader.ask tree-reader = op (ask-op) [] λ _ → var 
  Reader.local tree-reader _ f tm = op (local-op _ f) (tm ∷ []) λ _ → var

  instance tree-monotonestate : MonotoneState TreeEff 
  MonotoneState.get tree-monotonestate loc   = op (get-op loc)   [] λ _ → var
  MonotoneState.put tree-monotonestate loc v = op (put-op loc v) [] λ _ → var
  MonotoneState.alloc tree-monotonestate v   = op (init-op v)    [] λ _ → var    

  instance tree-except : Exception Sto TreeEff
  Exception.throw tree-except t = op (throw-op {t = t}) [] λ _ → var
  Exception.try-with tree-except t tm₁ tm₂ = op (try-op) (tm₁ ∷ tm₂ ∷ []) λ _ → var

  open import Canon.Function
  open FunCanon

  instance tree-general : General TreeEff
  General.general tree-general ⦃ isfun ⦄ ↑ tm = op (fix-op (λ s t → fun′ s t) ↑) (tm ∷ []) λ _ → var

  instance tree-isstrong : IsStrong tree-monadic
  IsStrong.isStr tree-isstrong = tree-strong (LambdaSig _)
