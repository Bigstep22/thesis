{-# OPTIONS --type-in-type #-}
{-# OPTIONS --no-termination-check #-}
{-# OPTIONS --guardedness #-}
open import Effect.Functor
module cochurch.defs {F : Set → Set}⦃ _ : RawFunctor F ⦄ where
open RawFunctor ⦃ ... ⦄
open import cat.funct
open ν


data CoChurch (F : Set → Set) : Set₁ where
  CoCh : {X : Set} → (X → F X) → X → CoChurch F
toCoCh : ν F → CoChurch F
toCoCh x = CoCh out x
fromCoCh : CoChurch F → ν F
fromCoCh (CoCh h x) = ⟦ h ⟧ x


