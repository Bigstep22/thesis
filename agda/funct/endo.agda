open import funct.container
open import Level renaming (suc to lsuc; zero to lzero)
module funct.endo (F : Container) where
open import Categories.Category.Instance.Sets
open import Categories.Functor
open import Relation.Binary.PropositionalEquality as Eq
open ≡-Reasoning
open import funct.flaws
open import funct.funext
open import Function

contendo : Endofunctor (Sets lzero)
contendo = record
             { F₀ = I⟦ F ⟧
             ; F₁ = fmap
             ; identity = refl
             ; homomorphism = refl
             ; F-resp-≈ = fmap-unique
             }
