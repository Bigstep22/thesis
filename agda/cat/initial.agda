open import cat.container
module cat.initial {F : Container}  where
open import Function.Base using (id; _∘_)
open import Relation.Binary.PropositionalEquality as Eq
open ≡-Reasoning
open import cat.flaws
open import cat.funext
open import Data.Product
open import Function.Base

-- An initial algebra
data μ (F : Container) : Set where
  in' : ⟦ F ⟧ (μ F) → μ F
-- Formerly cata - a catamorhpism
⦅_⦆ : {X : Set} → (⟦ F ⟧ X → X) → μ F → X
⦅ a ⦆ (in' (op , ar)) = a (op , ⦅ a ⦆ ∘ ar)
-- Look! The reflection law: https://wiki.haskell.org/Catamorphisms

universal-propₗ : {X : Set}(a : ⟦ F ⟧ X → X)(h : μ F → X) →
                  h ≡ ⦅ a ⦆ → h ∘ in' ≡ a ∘ fmap h
universal-propₗ a h eq = begin
    h ∘ in'
  ≡⟨ cong (_∘ in') eq ⟩
    ⦅ a ⦆ ∘ in'
  ≡⟨⟩
    a ∘ fmap ⦅ a ⦆
  ≡⟨ cong (_∘_ a) (cong fmap (sym eq)) ⟩
    a ∘ fmap h
  ∎

--universal-propᵣ : {X : Set}(a : ⟦ F ⟧ X → X)(h : μ F → X) →
--                            h ∘ in' ≡ a ∘ fmap h → ⦅ a ⦆ ≡ h
--universal-propᵣ a h eq = {!!}

comp-law : {A : Set}(a : ⟦ F ⟧ A → A) → ⦅ a ⦆ ∘ in' ≡ a ∘ fmap ⦅ a ⦆
comp-law a = refl

reflection : (y : μ F) → ⦅ in' ⦆ y ≡ y
reflection (in' (op , ar)) = begin
     ⦅ in' ⦆ (in' (op , ar))
   ≡⟨⟩
     in' (op , ⦅ in' ⦆ ∘ ar)
   ≡⟨ cong (λ x -> in' (op , x)) (funext (reflection ∘ ar)) ⟩
     in' (op , ar)
   ∎

reflection-law : ⦅ in' ⦆ ≡ id
reflection-law = funext reflection


postulate fusion : {A B : Set}(h : A → B)(a : ⟦ F ⟧ A → A)(b : ⟦ F ⟧ B → B) →
                   (h ∘ a ≡ b ∘ fmap h) →  h ∘ ⦅ a ⦆ ≡ ⦅ b ⦆
