open import Level
module funct.endo where
open import Data.Container renaming (refl to C-refl; map to fmap)
open import Categories.Category.Instance.Sets
open import Categories.Functor
open import Categories.Category renaming (Category to Cat)
open import Relation.Binary.PropositionalEquality as Eq
--open import funct.flaws
open import funct.funext

F[_] : (F : Container 0ℓ 0ℓ) → Endofunctor (Sets 0ℓ)
F[ F ] = record
             { F₀ = ⟦ F ⟧
             ; F₁ = fmap
             ; identity = refl
             ; homomorphism = refl
             ; F-resp-≈ = λ p → cong₂ fmap (funext (λ x → p {x})) refl
             }

