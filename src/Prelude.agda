{-# OPTIONS --safe --without-K #-}

module Prelude where

open import Core            public 
open import Box             public 
open import Signature       public 
open import Canon           public
open import Fragment        public
open import MonadicFragment public 
open import Structure.Monad public 


-- Standard library
open import Data.Product                                     public using    ( _×_
                                                                             ; _,_
                                                                             ; proj₁
                                                                             ; proj₂ )
open import Data.Nat                                         public using    ( ℕ
                                                                             ; zero
                                                                             ; suc
                                                                             ; _+_)
open import Data.Bool                                        public using    ( Bool
                                                                             ; true
                                                                             ; false
                                                                             ; _∧_
                                                                             ; if_then_else_)
open import Data.Maybe                                       public using    ( Maybe
                                                                             ; just
                                                                             ; nothing )
open import Data.List                                        public using    ( List
                                                                             ; map
                                                                             ; []
                                                                             ; _∷_ )
open import Data.Vec                                         public using    ( _∷_ ; [] ; Vec)

open import Data.List.Membership.Propositional               public 
open import Data.List.Relation.Binary.Sublist.Propositional  public hiding   (map) renaming (lookup to extend)
open import Data.List.Relation.Unary.All                     public renaming (lookup to lookupᵃ
                                                                             ; map to map-all )

open import Relation.Unary                                   public using    ( IUniversal ; _⇒_) 

open import Function                                         public using    ( _∘_
                                                                             ; case_of_
                                                                             ; id )
