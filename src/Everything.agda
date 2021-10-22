{-# OPTIONS --without-K #-}

module Everything where


--------------------------------------------------------------------------------
--- Framework code

open import Core
open import Prelude

-- Signature defintions & subsignature relations
--
-- Paper section(s):
-- * 2.1, 2.2, 2.3
-- * 3.1, 3.2, 3.3, (some of) 3.4, 3.5
open import Signature


-- An implementation of Kripke semantics for the "box" (Necessity) modality
--
-- Paper section(s):
-- * 4.1, 4.3
open import Box

-- Union type describing (potentially overlapping) unions on `Set`
--
-- Paper section(s):
-- * 4.2
open import Union

-- Canonical forms
--
-- Paper section(s):
-- * 4.1, 4.2
open import Canon

-- (Pure) Fragments and their composition
--
-- Paper section(s):
-- * 4.1, 4.2, 4.3
open import Fragment

-- Monadic fragments and their composition
--
-- Paper section(s):
-- * 5
open import Structure.Functor
open import Structure.Monad
open import MonadicFragment

----------------------------------------------------------------------------------
-- Canonical forms definitions
-- 
open import Canon.Nat
open import Canon.Bool
open import Canon.Pair
open import Canon.Maybe
open import Canon.Ref

----------------------------------------------------------------------------------
-- Monadic interfaces
--

open import Interface.Reader
open import Interface.Lambda
open import Interface.General
open import Interface.MonotoneState
open import Interface.Except

----------------------------------------------------------------------------------
-- A type of command trees that instantiates the relevant monadic interfaces 
--
open import Tree.Tree
open import Tree.Handle
open import Tree.Instances

----------------------------------------------------------------------------------
-- Fragment definitions
-- 
open import Fragment.Lambda
open import Fragment.General
open import Fragment.Exception
open import Fragment.Arith
open import Fragment.Boolean
open import Fragment.NatCase
open import Fragment.Pair
open import Fragment.Maybe
open import Fragment.MaybeCase
open import Fragment.Ref

----------------------------------------------------------------------------------
-- Example languages 
--
open import Languages.Language1
open import Languages.Language2
open import Languages.Language3
open import Languages.Language4
open import Languages.Language5
open import Languages.Language6

open import Languages.Expr
open import Languages.STLC+Ref
open import Languages.STLC+Rec+Maybe
open import Languages.MiniML

----------------------------------------------------------------------------------
-- Tests
--
open import Test.Language1

----------------------------------------------------------------------------------
-- Generalization to arbitrary categories
open import ArbitraryCategories.Base
open import ArbitraryCategories.Lambda
open import ArbitraryCategories.Sets ---> postulates fun-ext to prove some laws
                                     --   about the underlying category, so no
                                     --   --safe :( 
