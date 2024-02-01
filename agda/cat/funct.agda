{-# OPTIONS --no-termination-check #-}
{-# OPTIONS --no-positivity-check #-}
{-# OPTIONS --guardedness #-}
open import Effect.Functor
module cat.funct {F : Set → Set }⦃ _ : RawFunctor F ⦄ where
open RawFunctor ⦃ ... ⦄
open import Function.Base using (id; _∘_)
open import Relation.Binary.PropositionalEquality as Eq
open ≡-Reasoning

-- An initial algebra
data μ (F : Set → Set) : Set where
  inj : F (μ F) → μ F
-- Formerly cata - a catamorhpism
⦅_⦆ : {X : Set} → (F X → X) → μ F → X
⦅ a ⦆ (inj x) = a (⦅ a ⦆ <$> x)
-- Look! The reflection law: https://wiki.haskell.org/Catamorphisms

--postulate folds-prop : {A : Set}(h : μ F → A)(a : F A → A) → (h ≡ ⦅ a ⦆) → (h ∘ inj ≡ a ∘ (_<$> h))



-- An initial algebra
record ν (F : Set → Set) : Set where
  coinductive
  field
    out : F (ν F)
open ν
-- an anamorphism
⟦_⟧ : {X : Set} → (X → F X) → X → ν F
out (⟦ c ⟧ x) = ⟦ c ⟧ <$> (c x)
