{-# OPTIONS --without-K --safe #-}

open import cat.category

-- Reasoning facilities about morphism equivalences (not necessarily 'squares')

module cat.morphism.reasoning {o ℓ e} (C : Category o ℓ e) where

-- some items are defined in sub-modules
open import cat.morphism.reasoning.core C public
open import cat.morphism.reasoning.iso C public

open Category C
open Definitions C
open HomReasoning

-- create a commutative square from an equivalence
toSquare : ∀ {A B} {f g : A ⇒ B} → f ≈ g → CommutativeSquare f id id g
toSquare {_} {_} {f} {g} f≈g = begin
      id ∘ f   ≈⟨ identityˡ ⟩
      f        ≈⟨ f≈g ⟩
      g        ≈˘⟨ identityʳ ⟩
      g ∘ id   ∎
