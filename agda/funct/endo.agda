module agda.funct.endo where
open import Data.Container using (Container; ⟦_⟧) renaming (map to fmap)
open import Level using (0ℓ)
open import Categories.Category.Instance.Sets using (Sets)
open import Categories.Functor using (Endofunctor)
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning
open import agda.funct.funext using (funext)
open import Function

F[_] : (F : Container 0ℓ 0ℓ) → Endofunctor (Sets 0ℓ)
F[ F ] = record { F₀ = ⟦ F ⟧
                ; F₁ = fmap
                ; identity = refl
                ; homomorphism = refl
                ; F-resp-≈ = λ p → cong₂ fmap (funext (λ x → p {x})) refl
                }


--natcohere : {F G : Container 0ℓ 0ℓ}{A B : Set}{f : {X : Set} → ⟦ F ⟧ X → ⟦ G ⟧ X}{h : A → B} →
--            fmap h ∘ f ≡ f ∘ fmap h
--natcohere = refl
