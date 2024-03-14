open import funct.container
open import Level renaming (suc to lsuc; zero to lzero)
module funct.endo where
open import Categories.Category.Instance.Sets
open import Categories.Functor
open import Categories.Category renaming (Category to Cat)
open import Relation.Binary.PropositionalEquality as Eq
open import Categories.Category.Construction.F-Algebras
open ≡-Reasoning
open import funct.flaws
open import funct.funext
open import Function

F⟦_⟧ : (F : Container) → Endofunctor (Sets lzero)
F⟦ F ⟧ = record
             { F₀ = I⟦ F ⟧
             ; F₁ = fmap
             ; identity = refl
             ; homomorphism = refl
             ; F-resp-≈ = fmap-unique
             }

C⟦_⟧ : (F : Container) → Cat (lsuc 0ℓ) 0ℓ 0ℓ
C⟦ F ⟧ = F-Algebras F⟦ F ⟧
