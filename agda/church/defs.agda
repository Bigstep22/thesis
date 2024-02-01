{-# OPTIONS --guardedness #-}
open import Effect.Functor
module church.defs {F : Set → Set}⦃ _ : RawFunctor F ⦄ where
open RawFunctor ⦃ ... ⦄
open import cat.funct



data Church (F : Set → Set) : Set₁ where
  Ch : ({X : Set} → (F X → X) → X) → Church F
toCh : μ F → Church F
toCh x = Ch (λ {X : Set} → λ (a : F X → X) → ⦅ a ⦆ x)
fromCh : Church F → μ F
fromCh (Ch g) = g inj
-- See https://stackoverflow.com/a/56423455 as to why funexti(mplicit) is written this way, is this a weakness in the typechecker?

