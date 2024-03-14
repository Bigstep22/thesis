open import funct.container
module funct.fusion {F : Container} where
open import Function.Base
open import Relation.Binary.PropositionalEquality as Eq hiding ([_])
open ≡-Reasoning
open import funct.flaws
open import funct.funext
open import funct.initalg
open import Categories.Functor.Algebra
open import Categories.Category renaming (Category to Cat)
open import Categories.Category.Construction.F-Algebras
open import funct.endo
open import Categories.Object.Initial (C⟦ F ⟧)

postulate fusion : {A B : Set}(h : A → B)(a : I⟦ F ⟧ A → A)(b : I⟦ F ⟧ B → B) →
                   (h ∘ a ≡ b ∘ fmap h) →  h ∘ ⦅ a ⦆ ≡ ⦅ b ⦆


fusionprop : {A B μ : Set}{ϕ : I⟦ F ⟧ A → A}{ψ : I⟦ F ⟧ B → B}{init : I⟦ F ⟧ μ → μ}
             (i : IsInitial (to-Algebra init)) → (f : C⟦ F ⟧ [ to-Algebra ϕ , to-Algebra ψ ]) →
             IsInitial.! i ≡ C⟦ F ⟧ [ f ∘ IsInitial.! i {to-Algebra ϕ} ]
fusionprop  {ϕ} {ψ} {init} i f = {!!}
