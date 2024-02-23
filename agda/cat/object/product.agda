{-# OPTIONS --without-K --safe #-}
open import cat.category

--(Binary) product of objects and morphisms

module cat.object.product {o ℓ e} (C : Category o ℓ e) where

open import cat.object.product.core C public
open import cat.object.product.morphisms C public
