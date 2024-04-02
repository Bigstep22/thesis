open import Level renaming (zero to lzero; suc to lsuc)
open import Data.Container renaming (refl to C-refl)
module funct.flaws {F : Container 0ℓ 0ℓ} where
open import Function.Base using (id; _∘_)
open import Relation.Binary.PropositionalEquality as Eq
open ≡-Reasoning
open import Data.Product
open import funct.funext
open import Function

fmap : {X Y : Set} → (X → Y) → ⟦ F ⟧ X → ⟦ F ⟧ Y
fmap ca (op , ar) = op , ca ∘ ar

fmap-id : {X : Set} → (fmap (id {_} {X})) ≡ id {_} {⟦ F ⟧ X}
fmap-id = refl
fmap-comp : {X Y Z : Set}{x : ⟦ F ⟧ X}{f : Y → Z}{g : X → Y} →
                      (fmap (f ∘ g)) ≡ (fmap f) ∘ (fmap g)
fmap-comp = refl

fmap-unique : {X Y : Set} {f g : X → Y} → (∀ {x} → f x ≡ g x) → ∀ {x} → fmap f x ≡ fmap g x
fmap-unique p {x} = cong (flip fmap x) (funext (λ x₁ → p {x₁}))
