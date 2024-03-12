open import funct.container
module funct.free {F : Container } where
open import Function.Base using (id; _∘_)
open import Relation.Binary.PropositionalEquality as Eq
open ≡-Reasoning
open import funct.flaws
open import Level


postulate freetheorem-initial  : {B C : Set}{b : I⟦ F ⟧ B → B}{c : I⟦ F ⟧ C → C}(h : B → C)
                                 (g : {X : Set} → (I⟦ F ⟧ X → X) → X) →
                                 (h ∘ b ≡ (c ∘ (fmap h))) → h (g b) ≡ g c
postulate freetheorem-terminal : {ℓ : Level}
                                 {C D : Set}{Y : Set ℓ}{c : C → I⟦ F ⟧ C}{d : D → I⟦ F ⟧ D}(h : C → D)
                                 (f : {X : Set} → (X → I⟦ F ⟧ X) → X → Y) →
                                 ((fmap h ∘ c) ≡ d ∘ h) → f c ≡ f d ∘ h
                                 -- TODO: Do D and Y need to be the same thing? This may be a cop-out...
