{-# OPTIONS --without-K --safe #-}

-- Some of the obvious properties of cartesian functors
module Categories.Functor.Cartesian.Properties where

open import Level
open import Data.Product using (Σ ; _,_)

open import Categories.Category.BinaryProducts using (BinaryProducts)
open import Categories.Category.Core using (Category)
open import Categories.Category.Cartesian.Bundle using (CartesianCategory)
open import Categories.Category.Monoidal.Bundle using (MonoidalCategory)
open import Categories.Functor using (Functor; _∘F_) renaming (id to idF)
open import Categories.Functor.Properties
open import Categories.Functor.Cartesian using (CartesianF; IsCartesianF)
open import Categories.Functor.Monoidal
open import Categories.NaturalTransformation using (NaturalTransformation; ntHelper)

import Categories.Morphism as M
import Categories.Morphism.Reasoning as MR
import Categories.Object.Terminal as ⊤
import Categories.Object.Product as P

private
  variable
    o ℓ e o′ ℓ′ e′ o″ ℓ″ e″ : Level

module _ (C : CartesianCategory o ℓ e) where
  open CartesianCategory C using (terminal; U; products)
  open BinaryProducts products using (product)
  open ⊤.Terminal terminal
  open P U

  idF-IsCartesianF : IsCartesianF C C idF
  idF-IsCartesianF = record
    { F-resp-⊤ = ⊤-is-terminal
    ; F-resp-× = Product⇒IsProduct product
    }

  idF-CartesianF : CartesianF C C
  idF-CartesianF = record
    { isCartesian = idF-IsCartesianF
    }

module _ (A : CartesianCategory o ℓ e) (B : CartesianCategory o′ ℓ′ e′) (C : CartesianCategory o″ ℓ″ e″) where
  private
    module A = CartesianCategory A
    module B = CartesianCategory B
    module C = CartesianCategory C
    module AP = BinaryProducts A.products using (π₁; π₂)
    module BP = BinaryProducts B.products using (π₁; π₂; project₁; project₂)
    module CP = BinaryProducts C.products using (⟨_,_⟩; project₁; project₂; unique′)
    open P C.U

  ∘-IsCartesianF : ∀ {F : Functor A.U B.U} {G : Functor B.U C.U} →
                    IsCartesianF B C G → IsCartesianF A B F →
                    IsCartesianF A C (G ∘F F)
  ∘-IsCartesianF {F} {G} CG CF = record
    { F-resp-⊤ = ⊤.Terminal.⊤-is-terminal (⊤.transport-by-iso C.U C.terminal
                                          (M.≅.trans C.U (M.≅.sym C.U CG.⊤-iso) ([ G ]-resp-≅ (M.≅.sym B.U CF.⊤-iso))))
    ; F-resp-× = record
      { ⟨_,_⟩    = λ f g → G.₁ (CF.×-iso.to _ _) C.∘ CG.×-iso.to _ _ C.∘ CP.⟨ f , g ⟩
      ; project₁ = λ {_ f g} → begin
        G.₁ (F.₁ AP.π₁) C.∘ G.₁ (CF.×-iso.to _ _) C.∘ CG.×-iso.to _ _ C.∘ CP.⟨ f , g ⟩ ≈⟨ refl⟩∘⟨ refl⟩∘⟨ ([ CG.F-prod _ _ ]⟨⟩∘ ○ CG.F-prod.⟨⟩-cong₂ _ _ CP.project₁ CP.project₂) ⟩
        G.₁ (F.₁ AP.π₁) C.∘ G.₁ (CF.×-iso.to _ _) C.∘ CG.F-resp-×.⟨ f , g ⟩            ≈⟨ pullˡ ([ G ]-resp-∘ CF.F-resp-×.project₁) ⟩
        G.₁ BP.π₁ C.∘ CG.F-resp-×.⟨ f , g ⟩                                            ≈⟨ CG.F-resp-×.project₁ ⟩
        f ∎
      ; project₂ = λ {_ f g} → begin
        G.₁ (F.₁ AP.π₂) C.∘ G.₁ (CF.×-iso.to _ _) C.∘ CG.×-iso.to _ _ C.∘ CP.⟨ f , g ⟩ ≈⟨ refl⟩∘⟨ refl⟩∘⟨ ([ CG.F-prod _ _ ]⟨⟩∘ ○ CG.F-prod.⟨⟩-cong₂ _ _ CP.project₁ CP.project₂) ⟩
        G.₁ (F.₁ AP.π₂) C.∘ G.₁ (CF.×-iso.to _ _) C.∘ CG.F-resp-×.⟨ f , g ⟩            ≈⟨ pullˡ ([ G ]-resp-∘ CF.F-resp-×.project₂) ⟩
        G.₁ BP.π₂ C.∘ CG.F-resp-×.⟨ f , g ⟩                                            ≈⟨ CG.F-resp-×.project₂ ⟩
        g ∎
      ; unique   = λ {_ h f g} eq₁ eq₂ → begin
        G.₁ (CF.×-iso.to _ _) C.∘ CG.×-iso.to _ _ C.∘ CP.⟨ f , g ⟩
          ≈⟨ refl⟩∘⟨ refl⟩∘⟨ CP.unique′ (CP.project₁ ○ ⟺ eq₁ ○ pushˡ (⟺ ([ G ]-resp-∘ BP.project₁)) ○ pushˡ (⟺ CP.project₁))
                                       (CP.project₂ ○ ⟺ eq₂ ○ pushˡ (⟺ ([ G ]-resp-∘ BP.project₂)) ○ pushˡ (⟺ CP.project₂)) ⟩
        G.₁ (CF.×-iso.to _ _) C.∘ CG.×-iso.to _ _ C.∘ CG.×-iso.from _ _ C.∘ G.₁ (CF.×-iso.from _ _) C.∘ h
          ≈⟨ refl⟩∘⟨ cancelˡ (CG.×-iso.isoˡ _ _) ⟩
        G.₁ (CF.×-iso.to _ _) C.∘ G.₁ (CF.×-iso.from _ _) C.∘ h
          ≈⟨ cancelˡ (M._≅_.isoˡ ([ G ]-resp-≅ (CF.×-iso _ _))) ⟩
        h
          ∎
      }
    }
    where module F  = Functor F
          module G  = Functor G
          module CG = IsCartesianF CG
          module CF = IsCartesianF CF
          open C.HomReasoning
          open MR C.U

∘-CartesianF : {A : CartesianCategory o ℓ e} {B : CartesianCategory o′ ℓ′ e′} {C : CartesianCategory o″ ℓ″ e″} →
               CartesianF B C → CartesianF A B → CartesianF A C
∘-CartesianF G F = record { isCartesian = ∘-IsCartesianF _ _ _ (CartesianF.isCartesian G) (CartesianF.isCartesian F) }

module _ {C : CartesianCategory o ℓ e} {D : CartesianCategory o′ ℓ′ e′} where
  private
    module C  = CartesianCategory C
    module CP = BinaryProducts C.products
    module CM = MonoidalCategory C.monoidalCategory
    module D  = CartesianCategory D
    module DP = BinaryProducts D.products
    module DM = MonoidalCategory D.monoidalCategory using (associator)
    open D.HomReasoning
    open MR D.U
    open M D.U

  isMonoidalFunctor : CartesianF C D → MonoidalFunctor C.monoidalCategory D.monoidalCategory
  isMonoidalFunctor F = record
    { F          = F.F
    ; isMonoidal = record
      { ε             = F.⊤-iso.to
      ; ⊗-homo        = ntHelper record
        { η       = λ { (X , Y) → F.×-iso.to X Y }
        ; commute = λ { {X , Y} {Z , W} (f , g) →
          F.F-prod.unique′ _ _
            (begin
              F.₁ CP.π₁ D.∘ F.×-iso.to Z W D.∘ (F.₁ f DP.⁂ F.₁ g) ≈⟨ pullˡ F.F-resp-×.project₁ ⟩
              DP.π₁ D.∘ (F.₁ f DP.⁂ F.₁ g)                        ≈⟨ DP.project₁ ⟩
              F.₁ f D.∘ DP.π₁                                     ≈˘⟨ pullʳ F.F-resp-×.project₁ ⟩
              (F.₁ f D.∘ F.₁ CP.π₁) D.∘ F.×-iso.to X Y            ≈˘⟨ pullˡ ([ F.F ]-resp-square CP.project₁) ⟩
              F.₁ CP.π₁ D.∘ F.₁ (f CP.⁂ g) D.∘ F.×-iso.to X Y     ∎)
            (begin
              F.₁ CP.π₂ D.∘ F.×-iso.to Z W D.∘ (F.₁ f DP.⁂ F.₁ g) ≈⟨ pullˡ F.F-resp-×.project₂ ⟩
              DP.π₂ D.∘ (F.₁ f DP.⁂ F.₁ g)                        ≈⟨ DP.project₂ ⟩
              F.₁ g D.∘ DP.π₂                                    ≈˘⟨ pullʳ F.F-resp-×.project₂ ⟩
              (F.₁ g D.∘ F.₁ CP.π₂) D.∘ F.×-iso.to X Y           ≈˘⟨ pullˡ ([ F.F ]-resp-square CP.project₂) ⟩
              F.₁ CP.π₂ D.∘ F.₁ (f CP.⁂ g) D.∘ F.×-iso.to X Y     ∎)
          }
        }
      ; associativity = λ {X Y Z} → let open P D.U in begin
        F.₁ CM.associator.from D.∘ F.×-iso.to (X CP.× Y) Z D.∘ (F.×-iso.to X Y DP.⁂ D.id)
          ≈⟨ F.F-resp-⟨⟩′ _ _ ⟩∘⟨ [ DP.product ⇒ DP.product ⇒ F.F-prod _ _ ]repack∘× ⟩
        F.F-resp-×.⟨ F.₁ (CP.π₁ C.∘ CP.π₁) , F.₁ CP.⟨ CP.π₂ C.∘ CP.π₁ , CP.π₂ ⟩ ⟩ D.∘ F.F-resp-×.⟨ F.×-iso.to X Y D.∘ DP.π₁ , D.id D.∘ DP.π₂ ⟩
          ≈⟨ F.F-prod.⟨⟩-cong₂ _ _ F.homomorphism (F.F-resp-⟨⟩′ _ _ ○ F.F-prod.⟨⟩-cong₂ _ _ F.homomorphism D.Equiv.refl) ⟩∘⟨refl ⟩
        F.F-resp-×.⟨ F.₁ CP.π₁ D.∘ F.₁ CP.π₁ , F.F-resp-×.⟨ F.₁ CP.π₂ D.∘ F.₁ CP.π₁ , F.₁ CP.π₂ ⟩ ⟩ D.∘ F.F-resp-×.⟨ F.×-iso.to X Y D.∘ DP.π₁ , D.id D.∘ DP.π₂ ⟩
          ≈⟨ [ F.F-prod _ _ ]⟨⟩∘ ⟩
        F.F-resp-×.⟨ (F.₁ CP.π₁ D.∘ F.₁ CP.π₁) D.∘ _ , F.F-resp-×.⟨ F.₁ CP.π₂ D.∘ F.₁ CP.π₁ , F.₁ CP.π₂ ⟩ D.∘ _ ⟩
          ≈⟨ F.F-prod.⟨⟩-cong₂ _ _ (pullʳ F.F-resp-×.project₁ ○ pullˡ F.F-resp-×.project₁)
                                   [ F.F-prod _ _ ]⟨⟩∘ ⟩
        F.F-resp-×.⟨ DP.π₁ D.∘ DP.π₁ , F.F-resp-×.⟨ (F.₁ CP.π₂ D.∘ F.₁ CP.π₁) D.∘ _ , F.₁ CP.π₂ D.∘ _ ⟩ ⟩
          ≈⟨ F.F-prod.⟨⟩-cong₂ _ _ D.Equiv.refl
            (F.F-prod.⟨⟩-cong₂ _ _ (pullʳ F.F-resp-×.project₁ ○ pullˡ F.F-resp-×.project₂)
                                   (F.F-resp-×.project₂ ○ D.identityˡ)) ⟩
        F.F-resp-×.⟨ DP.π₁ D.∘ DP.π₁ , F.F-resp-×.⟨ DP.π₂ D.∘ DP.π₁ , DP.π₂ ⟩ ⟩
          ≈˘⟨ F.F-prod.⟨⟩-cong₂ _ _ D.identityˡ ([ F.F-prod _ _ ]⟨⟩∘ ○ (F.F-prod.⟨⟩-cong₂ _ _ DP.project₁ DP.project₂)) ⟩
        F.F-resp-×.⟨ D.id D.∘ DP.π₁ D.∘ DP.π₁ , F.×-iso.to Y Z D.∘ DP.⟨ DP.π₂ D.∘ DP.π₁ , DP.π₂ ⟩ ⟩
          ≈˘⟨ [ DP.product ⇒ (F.F-prod _ _) ]×∘⟨⟩ ⟩
        F.F-resp-×.⟨ D.id D.∘ DP.π₁ , F.×-iso.to Y Z D.∘ DP.π₂ ⟩ D.∘ DM.associator.from
          ≈˘⟨ pullˡ [ DP.product ⇒ DP.product ⇒ F.F-prod _ _ ]repack∘× ⟩
        F.×-iso.to X (Y CP.× Z) D.∘ (D.id DP.⁂ F.×-iso.to Y Z) D.∘ DM.associator.from
          ∎
      ; unitaryˡ      = begin
        F.₁ CP.π₂ D.∘ F.F-resp-×.⟨ DP.π₁ , DP.π₂ ⟩ D.∘ (F.F-resp-⊤.! DP.⁂ D.id) ≈⟨ pullˡ F.F-resp-×.project₂ ⟩
        DP.π₂ D.∘ (F.F-resp-⊤.! DP.⁂ D.id)                                     ≈⟨ DP.project₂ ⟩
        D.id D.∘ DP.π₂                                                         ≈⟨ D.identityˡ ⟩
        DP.π₂                                                                  ∎
      ; unitaryʳ      = begin
        F.₁ CP.π₁ D.∘ F.F-resp-×.⟨ DP.π₁ , DP.π₂ ⟩ D.∘ (D.id DP.⁂ F.F-resp-⊤.!) ≈⟨ pullˡ F.F-resp-×.project₁ ⟩
        DP.π₁ D.∘ (D.id DP.⁂ F.F-resp-⊤.!)                                     ≈⟨ DP.project₁ ⟩
        D.id D.∘ DP.π₁                                                         ≈⟨ D.identityˡ ⟩
        DP.π₁                                                                  ∎
      }
    }
    where module F = CartesianF F

  isStrongMonoidalFunctor : CartesianF C D → StrongMonoidalFunctor C.monoidalCategory D.monoidalCategory
  isStrongMonoidalFunctor F = record
    { F                = F.F
    ; isStrongMonoidal = record
      { ε             = ≅.sym F.⊤-iso
      ; ⊗-homo        = record
        { F⇒G = MF.⊗-homo
        ; F⇐G = ntHelper record
          { η       = λ { (X , Y) → F.×-iso.from X Y }
          ; commute = λ { {X , Y} {Z , W} (f , g) →
            begin
              DP.⟨ F.₁ CP.π₁ , F.₁ CP.π₂ ⟩ D.∘ F.₁ (f CP.⁂ g)                    ≈⟨ DP.⟨⟩∘ ⟩
              DP.⟨ F.₁ CP.π₁ D.∘ F.₁ (f CP.⁂ g) , F.₁ CP.π₂ D.∘ F.₁ (f CP.⁂ g) ⟩ ≈⟨ DP.⟨⟩-cong₂ ([ F.F ]-resp-square CP.project₁) ([ F.F ]-resp-square CP.project₂) ⟩
              DP.⟨ F.₁ f D.∘ F.F₁ CP.π₁ , F.₁ g D.∘ F.F₁ CP.π₂ ⟩                 ≈˘⟨ DP.⁂∘⟨⟩ ⟩
              (F.₁ f DP.⁂ F.₁ g) D.∘ DP.⟨ F.F₁ CP.π₁ , F.F₁ CP.π₂ ⟩              ∎ }
          }
        ; iso = λ { (X , Y) → record
          { isoˡ = F.×-iso.isoʳ X Y
          ; isoʳ = F.×-iso.isoˡ X Y
          } }
        }
      ; associativity = MF.associativity
      ; unitaryˡ      = MF.unitaryˡ
      ; unitaryʳ      = MF.unitaryʳ
      }
    }
    where module F  = CartesianF F
          module MF = MonoidalFunctor (isMonoidalFunctor F)
