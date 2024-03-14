open import funct.container
module funct.fusion {F : Container} where
open import Function.Base
open import Relation.Binary.PropositionalEquality as Eq hiding ([_])
open ≡-Reasoning
open import funct.flaws
open import funct.funext
open import funct.initalg {F}
open import Categories.Functor.Algebra
open import Categories.Category renaming (Category to Cat)
open import Categories.Category.Construction.F-Algebras
open import funct.endo
open import Categories.Object.Initial (C⟦ F ⟧)


fusionprop : {A B μ : Set}{ϕ : I⟦ F ⟧ A → A}{ψ : I⟦ F ⟧ B → B}{init : I⟦ F ⟧ μ → μ}
             (i : IsInitial (to-Algebra init))(f : F Alg[ ϕ , ψ ]) →
             C⟦ F ⟧ [ IsInitial.! i {to-Algebra ψ} ≈ C⟦ F ⟧ [ f ∘ IsInitial.! i {to-Algebra ϕ} ] ]
fusionprop  {A}{B}{μ}{ϕ}{ψ}{init} i f = IsInitial.!-unique i (C⟦ F ⟧ [ f ∘ IsInitial.! i {to-Algebra ϕ} ])


fusion : {A B : Set}{h : A → B}{a : I⟦ F ⟧ A → A}{b : I⟦ F ⟧ B → B}{x : I⟦ F ⟧ A} →
                   ((h ∘ a) x ≡ (b ∘ fmap h) x) →  ⦅ b ⦆ ≡ h ∘ ⦅ a ⦆
fusion {A}{B} {h} {a} {b} {x} p = fusionprop initial-in (record
                        { f = ?
                        ; commutes = {!!}
                        })
