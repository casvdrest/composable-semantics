{-# OPTIONS --safe --without-K #-}

open import Data.Fin
open import Data.Product renaming (_Ã_ to _Ãp_)
open import Data.Empty
open import Data.Vec

-------------------------------------------------------------------------------
-- agda-categories imports
--
open import Categories.Category.Core
open import Categories.Monad

open import Categories.Category.BinaryProducts
open import Categories.Category.Cartesian
open import Categories.Category.CartesianClosed.Canonical

open import Categories.Category.Construction.Kleisli

open import Categories.Object.Exponential
open import Categories.Object.Terminal
open import Categories.Object.Product

open import Categories.Functor renaming (id to idá¶ )

open import Data.List
open import Data.List.Membership.Propositional
open import Data.List.Relation.Unary.Any
open import Data.List.Relation.Unary.All

import Categories.Morphism.Reasoning as MR

open import Signature
open import Union

open import Level renaming (suc to sucL)

-------------------------------------------------------------------------------
-- local imports
open import ArbitraryCategories.Base

module ArbitraryCategories.Lambda 
  (ð : Category (sucL 0â) 0â 0â)
  
  (cc : CartesianClosed ð)
  where

  open CartesianClosed cc renaming (curry to Î»g ; â¨_,_â© to âª_,_â«)
  
  open Terminal
  open IsTerminal 

  open Fragments   ð isCartesian
  open Combinators ð isCartesian

  open Category ð renaming (_â_ to _â¨ââ©_ ; _â_ to _â¨ââ©_ )
  open Cartesian isCartesian
 

  -------------------------------------------------------------------------------
  -- Canon

  open _â¼_ â¦...â¦

  module FunCanon where

    data FunTyShape : Set where fun : FunTyShape
    FunTySig = FunTyShape â¹ Î» where fun â 2

    funCanon = canon FunTySig Î» where .alg (fun , lift (s â· t â· [])) â t ^ s

    funáµ : â {Ï} â â¦ FunTySig â¼ Ï â¦ â Î¼ Ï â Î¼ Ï â Î¼ Ï
    funáµ â¦ x â¦ s t = â¨ (inj (fun , Level.lift (s â· t â· []))) â©

  -------------------------------------------------------------------------------
  -- Fragment

  module Lambda where

    open FunCanon

    module _ {c : Canon} â¦ p : funCanon â c â¦ where

      open Canon c

      data LambdaExprShape : Ctx Ãp Ty â Set where
        var : â {Î t} â t â Î â LambdaExprShape (Î , t)
        abs : â {Î s t}       â LambdaExprShape (Î , funáµ s t)
        app : â {Î} {s t : _} â LambdaExprShape (Î , t)

      LambdaExprSig : ISignature _ (Ctx Ãp Ty) (Ctx Ãp Ty)
      LambdaExprSig .Shapeá´µ = LambdaExprShape
      LambdaExprSig .Indices (var x) = []
      LambdaExprSig .Indices (abs {Î} {s} {t}) = (s â· Î , t) â· []
      LambdaExprSig .Indices (app {Î} {s} {t}) = (Î , funáµ s t) â· (Î , s) â· []

      evalLambda : IAlgebra LambdaExprSig Î» (Î , t) â Env Î â¨ââ© Values t 
      evalLambda .ialg (var x , _) = fetch x
      evalLambda .ialg (abs   , lift (ff â· [])) with f â ff 
        = â â¨ââ© Î»g (f â¨ââ© âª Ïâ , Ïâ â« ) 
      evalLambda .ialg (app   , lift (ff â· fx â· [])) with f â ff | x â fx
        = eval â¨ââ© âª â â¨ââ© f , x â« 

    LambdaFragment : â¡ Fragment funCanon
    â¡.future LambdaFragment = fragment LambdaExprSig evalLambda
