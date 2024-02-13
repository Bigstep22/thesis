open import cat.container
module cat.free {F : Container } where
open import Function.Base using (id; _∘_)
open import Relation.Binary.PropositionalEquality as Eq
open ≡-Reasoning
open import cat.flaws


postulate freetheorem-initial  : {B C : Set}{b : ⟦ F ⟧ B → B}{c : ⟦ F ⟧ C → C}(h : B → C)
                                 (g : {X : Set} → (⟦ F ⟧ X → X) → X) →
                                 (h ∘ b ≡ (c ∘ (fmap h))) → h (g b) ≡ g c
postulate freetheorem-terminal : {C D Y : Set}{c : C → ⟦ F ⟧ C}{d : D → ⟦ F ⟧ D}(h : C → D)
                                 (f : {X : Set} → (X → ⟦ F ⟧ X) → X → Y) →
                                 ((fmap h ∘ c) ≡ d ∘ h) → f c ≡ f d ∘ h
                                 -- TODO: Do D and Y need to be the same thing? This may be a cop-out...
