open import funct.container
module funct.initalg {F : Container} where
open import Data.Product
open import Level
open import Categories.Category renaming (Category to Cat)
open import Categories.Functor.Algebra
open import Relation.Binary.PropositionalEquality as Eq hiding ([_])
open ≡-Reasoning
open import funct.flaws
open import funct.funext
open import Function
open import funct.endo

open import Categories.Category.Construction.F-Algebras
C[_]Alg : (F : Container) → Cat (suc 0ℓ) 0ℓ 0ℓ
C[ F ]Alg = F-Algebras F[ F ]

open import Categories.Object.Initial C[ F ]Alg

_Alg[_,_] : {X Y : Set}(F : Container)(x : I⟦ F ⟧ X → X)(Y : I⟦ F ⟧ Y → Y) → Set
F Alg[ x , y ] = C[ F ]Alg [ to-Algebra x , to-Algebra y ]

data μ (F : Container) : Set where
  in' : I⟦ F ⟧ (μ F) → μ F
⦅_⦆ : {X : Set} → (I⟦ F ⟧ X → X) → μ F → X
⦅ a ⦆ (in' (op , ar)) = a (op , ⦅ a ⦆ ∘ ar)


open F-Algebra-Morphism
open F-Algebra


valid-falghom : {X : Set}(a : I⟦ F ⟧ X → X) → F Alg[ in' , a ]
valid-falghom {X} a = record { f = ⦅ a ⦆ ; commutes = refl }


isunique : {X : Set}{a : I⟦ F ⟧ X → X}(fhom : F Alg[ in' , a ])(x : μ F) →
           ⦅ a ⦆ x ≡ fhom .f x
isunique {_}{a} fhom (in' (op , ar)) = begin
                   ⦅ a ⦆ (in' (op , ar))
                     ≡⟨⟩ -- Dfn of ⦅_⦆
                   a (op , ⦅ a ⦆ ∘ ar)
                     ≡⟨ cong (λ h → a (op , h)) (funext $ isunique fhom ∘ ar) ⟩ -- induction
                   a (op , (fhom .f) ∘ ar)
                     ≡⟨⟩ -- Dfn of composition
                   (a ∘ fmap (fhom .f)) (op , ar)
                     ≡⟨ cong-app (sym $ funext (λ x → fhom .commutes {x})) (op , ar) ⟩
                   (fhom .f ∘ in') (op , ar)
                 ∎


initial-in : IsInitial (to-Algebra in')
initial-in = record
             { ! = λ {A} → valid-falghom (A .α)
             ; !-unique = λ fhom {x} → isunique fhom x
             }

