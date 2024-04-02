{-# OPTIONS --guardedness #-}
open import funct.container
module term.cofusion {F : Container} where
open import Function.Base
open import Relation.Binary.PropositionalEquality as Eq hiding ([_])
open import funct.flaws
open import funct.funext
open import term.termcoalg {F}
open import funct.endo
open import Categories.Functor.Coalgebra
open import Categories.Category renaming (Category to Cat)
open import Categories.Object.Terminal
open IsTerminal

fusionprop : {C D ν : Set}{ϕ : C → I⟦ F ⟧ C}{ψ : D → I⟦ F ⟧ D}{term : ν → I⟦ F ⟧ ν}
             (i : IsTerminal C[ F ]CoAlg (to-Coalgebra term))(f : F CoAlghom[ ψ , ϕ ]) →
             C[ F ]CoAlg [ i .! ≈ C[ F ]CoAlg [ i .! ∘ f ] ]
fusionprop i f = i .!-unique (C[ F ]CoAlg [ i .! ∘ f ])


fusion : {C D : Set}{c : C → I⟦ F ⟧ C}{d : D → I⟦ F ⟧ D}(h : C → D) →
                   (d ∘ h ≡ fmap h ∘ c) → ⟦ c ⟧ ≡ ⟦ d ⟧ ∘ h
fusion h p = funext λ x → fusionprop terminal-out (record { f = h ; commutes = λ {y} → cong-app p y }) {x}