{-# OPTIONS --no-termination-check #-}
{-# OPTIONS --no-positivity-check #-}
{-# OPTIONS --guardedness #-}
open import Effect.Functor
module cat.initial {F : Set → Set }⦃ _ : RawFunctor F ⦄ where
open RawFunctor ⦃ ... ⦄
open import Function.Base using (id; _∘_)
open import Relation.Binary.PropositionalEquality as Eq
open ≡-Reasoning
open import cat.flaws
open import cat.funext

-- An initial algebra
data μ (F : Set → Set) : Set where
  in' : F (μ F) → μ F
-- Formerly cata - a catamorhpism
⦅_⦆ : {X : Set} → (F X → X) → μ F → X
⦅ a ⦆ (in' x) = a (⦅ a ⦆ <$> x)
-- Look! The reflection law: https://wiki.haskell.org/Catamorphisms

postulate universal-propₗ : {A : Set}(h : μ F → A)(a : F A → A) → ((h ≡ ⦅ a ⦆) → (h ∘ in' ≡ a ∘ (_<$>_ h)))
postulate universal-propᵣ : {A : Set}(h : μ F → A)(a : F A → A) → ((h ∘ in' ≡ a ∘ (_<$>_ h)) → (h ≡ ⦅ a ⦆))
-- Should we use ≡ or ⇔ (or similar) for this?

comp-law : {A : Set}(a : F A → A) → ⦅ a ⦆ ∘ in' ≡ a ∘ (_<$>_ ⦅ a ⦆)
comp-law a = universal-propₗ ⦅ a ⦆ a refl

reflection : (y : μ F) → ⦅ in' ⦆ y ≡ y
reflection (in' x) = begin
     ⦅ in' ⦆ (in' x)
   ≡⟨⟩
     in' (⦅ in' ⦆ <$> x)
   ≡⟨ cong in' (cong (_<$> x) (funext reflection)) ⟩
     in' (id <$> x)
   ≡⟨ cong in' (cong-app fmap-id x) ⟩
    in' x
   ∎
reflection-law : ⦅ in' ⦆ ≡ id
reflection-law = funext reflection

postulate fusion : {A B : Set}(h : A → B)(a : F A → A)(b : F B → B) →
                   (h ∘ a ≡ b ∘ _<$>_ h) →  h ∘ ⦅ a ⦆ ≡ ⦅ b ⦆
