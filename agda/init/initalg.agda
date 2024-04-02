open import funct.container
module init.initalg where
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

open import Categories.Object.Initial --C[ F ]Alg

_Alghom[_,_] : {X Y : Set}(F : Container)(x : I⟦ F ⟧ X → X)(Y : I⟦ F ⟧ Y → Y) → Set
F Alghom[ x , y ] = C[ F ]Alg [ to-Algebra x , to-Algebra y ]


data μ (F : Container) : Set where -- This F is different to
  in' : I⟦ F ⟧ (μ F) → μ F -- This F (in μ F) ......
⦅_⦆ : {F : Container}{X : Set} → (I⟦ F ⟧ X → X) → μ F → X
⦅ a ⦆ (in' (op , ar)) = a (op , ⦅ a ⦆ ∘ ar)

open F-Algebra-Morphism
open F-Algebra


valid-falghom : {F : Container}{X : Set}(a : I⟦ F ⟧ X → X) → F Alghom[ in' , a ]
valid-falghom {X} a = record { f = ⦅ a ⦆ ; commutes = refl }


isunique : {F : Container}{X : Set}{a : I⟦ F ⟧ X → X}(fhom : F Alghom[ in' , a ])(x : μ F) →
           ⦅ a ⦆ x ≡ fhom .f x
isunique {_}{_}{a} fhom (in' (op , ar)) = begin
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


initial-in : {F : Container} → IsInitial C[ F ]Alg (to-Algebra in')
initial-in = record
             { ! = λ {A} → valid-falghom (A .α)
             ; !-unique = λ fhom {x} → isunique fhom x
             }

