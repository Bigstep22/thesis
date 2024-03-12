open import funct.container
module funct.flaws {F : Container} where
open import Function.Base using (id; _∘_)
open import Relation.Binary.PropositionalEquality as Eq
open ≡-Reasoning
open import Data.Product

fmap : {X Y : Set} → (X → Y) → I⟦ F ⟧ X → I⟦ F ⟧ Y
fmap ca (op , ar) = op , ca ∘ ar

fmap-id : {X : Set} → (fmap (id {_} {X})) ≡ id {_} {I⟦ F ⟧ X}
fmap-id = refl
fmap-comp : {X Y Z : Set}{x : I⟦ F ⟧ X}{f : Y → Z}{g : X → Y} →
                      (fmap (f ∘ g)) ≡ (fmap f) ∘ (fmap g)
fmap-comp = refl
