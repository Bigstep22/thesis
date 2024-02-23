{-# OPTIONS --without-K --safe #-}

{-
  Useful notation for Epimorphisms, Mononmorphisms, and isomorphisms
-}
module cat.morphism.notation where

open import Level

open import cat.category.core
open import cat.morphism

private
  variable
    o ℓ e : Level

_[_↣_] : (𝒞 : Category o ℓ e) → (A B : Category.Obj 𝒞) → Set (o ⊔ ℓ ⊔ e)
𝒞 [ A ↣ B ] = _↣_ 𝒞 A B

_[_↠_] : (𝒞 : Category o ℓ e) → (A B : Category.Obj 𝒞) → Set (o ⊔ ℓ ⊔ e)
𝒞 [ A ↠ B ] = _↠_ 𝒞 A B

_[_≅_] : (𝒞 : Category o ℓ e) → (A B : Category.Obj 𝒞) → Set (ℓ ⊔ e)
𝒞 [ A ≅ B ] = _≅_ 𝒞 A B
