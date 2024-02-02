{-# OPTIONS --guardedness #-}
open import Effect.Functor
module church.defs {F : Set → Set}⦃ _ : RawFunctor F ⦄ where
open RawFunctor ⦃ ... ⦄
open import cat.initial



data Church (F : Set → Set) : Set₁ where
  Ch : ({X : Set} → (F X → X) → X) → Church F
toCh : μ F → Church F
toCh x = Ch (λ {X : Set} → λ (a : F X → X) → ⦅ a ⦆ x)
fromCh : Church F → μ F
fromCh (Ch g) = g in'
