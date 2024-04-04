open import Data.Container renaming (map to fmap)
open import Level
module init.fusion {F : Container 0ℓ 0ℓ} where
open import Function.Base
open import Relation.Binary.PropositionalEquality as Eq hiding ([_])
open import funct.funext
open import init.initalg
open import funct.endo
open import Categories.Functor.Algebra
open import Categories.Category renaming (Category to Cat)
open import Categories.Object.Initial
open IsInitial

fusionprop : {A B μ : Set}{ϕ : ⟦ F ⟧ A → A}{ψ : ⟦ F ⟧ B → B}{init : ⟦ F ⟧ μ → μ}
             (i : IsInitial C[ F ]Alg (to-Algebra init))(f : F Alghom[ ϕ , ψ ]) →
             C[ F ]Alg [ i .! ≈ C[ F ]Alg [ f ∘ i .! ] ]
fusionprop i f = i .!-unique (C[ F ]Alg [ f ∘ i .! ])


fusion : {A B : Set}{a : ⟦ F ⟧ A → A}{b : ⟦ F ⟧ B → B}(h : A → B) →
         h ∘ a ≡ b ∘ fmap h →  ⦅ b ⦆ ≡ h ∘ ⦅ a ⦆
fusion h p = funext λ x → fusionprop initial-in (record { f = h ; commutes = λ {y} → cong-app p y }) {x}
