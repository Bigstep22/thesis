{-# OPTIONS --no-termination-check #-}
{-# OPTIONS --guardedness #-}
open import cat.container
module cat.initial {F : Container}  where
open import Function.Base using (id; _∘_)
open import Relation.Binary.PropositionalEquality as Eq
open ≡-Reasoning
open import cat.flaws
open import cat.funext
open import Data.Product
open import Function.Base

--record Container : Set₁ where
--  constructor _▹_
--  field
--    Op : Set
--    Ar : Op → Set
--
--⟦_⟧ : Container → Set → Set
--⟦ op ▹ ar ⟧ A = Σ[ x ∈ op ] (ar x → A)


-- An initial algebra
data μ (F : Container) : Set where
  in' : ⟦ F ⟧ (μ F) → μ F
-- Formerly cata - a catamorhpism
⦅_⦆ : {X : Set} → (⟦ F ⟧ X → X) → μ F → X
⦅ a ⦆ (in' (op , ar)) = a (op , ⦅ a ⦆ ∘ ar)
-- Look! The reflection law: https://wiki.haskell.org/Catamorphisms


postulate universal-propₗ : {A : Set}(h : μ F → A)(a : ⟦ F ⟧ A → A) →
                           h ≡ ⦅ a ⦆ → h ∘ in' ≡ a ∘ fmap h
postulate universal-propᵣ : {A : Set}(h : μ F → A)(a : ⟦ F ⟧ A → A) →
                           (h ∘ in' ≡ a ∘ fmap h) → (h ≡ ⦅ a ⦆)
-- Should we use ≡ or ⇔ (or similar) for this?

comp-law : {A : Set}(a : ⟦ F ⟧ A → A) → ⦅ a ⦆ ∘ in' ≡ a ∘ (fmap ⦅ a ⦆)
comp-law a = universal-propₗ ⦅ a ⦆ a refl


reflection : (y : μ F) → ⦅ in' ⦆ y ≡ y
reflection (in' x) = begin
     ⦅ in' ⦆ (in' x)
   ≡⟨⟩
     in' (fmap ⦅ in' ⦆ x)
   ≡⟨ cong in' (cong (flip fmap x) (funext reflection)) ⟩
     in' (fmap id x)
   ≡⟨ cong in' (cong-app fmap-id x) ⟩
    in' x
   ∎
reflection-law : ⦅ in' ⦆ ≡ id
reflection-law = funext reflection

postulate fusion : {A B : Set}(h : A → B)(a : ⟦ F ⟧ A → A)(b : ⟦ F ⟧ B → B) →
                   (h ∘ a ≡ b ∘ fmap h) →  h ∘ ⦅ a ⦆ ≡ ⦅ b ⦆
