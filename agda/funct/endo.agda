open import funct.container
open import Level
module funct.endo where
open import Categories.Category.Instance.Sets
open import Categories.Functor
open import Categories.Category renaming (Category to Cat)
open import Relation.Binary.PropositionalEquality as Eq
open import funct.flaws
open import funct.funext

F[_] : (F : Container) → Endofunctor (Sets 0ℓ)
F[ F ] = record
             { F₀ = I⟦ F ⟧
             ; F₁ = fmap
             ; identity = refl
             ; homomorphism = refl
             ; F-resp-≈ = fmap-unique
             }

