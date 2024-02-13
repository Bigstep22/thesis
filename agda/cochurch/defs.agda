{-# OPTIONS --guardedness #-}
open import cat.container
module cochurch.defs {F : Container} where
open import cat.terminal
open ν
open import Data.Product


data CoChurch (F : Container) : Set₁ where
  CoCh : {X : Set} → (X → ⟦ F ⟧ X) → X → CoChurch F
toCoCh : ν {F} F → CoChurch F
toCoCh x = CoCh out x
fromCoCh : CoChurch F → ν {F} F
fromCoCh (CoCh h x) = 【 h 】 x


data CoChurch' (F : Container) : Set₁ where
  cochurch : (∃ λ S → (S → ⟦ F ⟧ S) × S) → CoChurch' F
