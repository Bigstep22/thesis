{-# OPTIONS --no-termination-check #-}
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


universal-propₗ : {A : Set}(h : μ F → A)(a : ⟦ F ⟧ A → A) →
                           h ≡ ⦅ a ⦆ → h ∘ in' ≡ a ∘ fmap h
universal-propₗ h a eq = begin
    h ∘ in'
  ≡⟨ cong (_∘ in') eq ⟩
    ⦅ a ⦆ ∘ in'
  ≡⟨⟩
    a ∘ fmap ⦅ a ⦆
  ≡⟨ cong (_∘_ a) (cong fmap (sym eq)) ⟩
    a ∘ fmap h
  ∎
-- postulate universal-propᵣ : {A : Set}(h : μ F → A)(a : ⟦ F ⟧ A → A) → (h ∘ in' ≡ a ∘ fmap h) → (h ≡ ⦅ a ⦆)
-- Should we use ≡ or ⇔ (or similar) for this?

comp-law : {A : Set}(a : ⟦ F ⟧ A → A) → ⦅ a ⦆ ∘ in' ≡ a ∘ (fmap ⦅ a ⦆)
comp-law a = universal-propₗ ⦅ a ⦆ a refl


-- This will likely need a broader proof if I want to disable termination checking...
reflection-law : ⦅ in' ⦆ ≡ id
reflection : (y : μ F) → ⦅ in' ⦆ y ≡ y
reflection-law = funext reflection
reflection (in' x) = begin
     ⦅ in' ⦆ (in' x)
   ≡⟨⟩
     in' (fmap ⦅ in' ⦆ x)
   ≡⟨ cong in' (cong (flip fmap x) reflection-law) ⟩
     in' (fmap id x)
   ≡⟨ cong in' (cong-app fmap-id x) ⟩
     in' x
   ∎

postulate fusion : {A B : Set}(h : A → B)(a : ⟦ F ⟧ A → A)(b : ⟦ F ⟧ B → B) →
                   (h ∘ a ≡ b ∘ fmap h) →  h ∘ ⦅ a ⦆ ≡ ⦅ b ⦆
