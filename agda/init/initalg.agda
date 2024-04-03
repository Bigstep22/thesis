--open import funct.container
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
open import Data.Container renaming (refl to C-refl; sym to C-sym)
open import Data.W renaming (sup to in')

open import Categories.Category.Construction.F-Algebras
C[_]Alg : (F : Container 0ℓ 0ℓ) → Cat (suc 0ℓ) 0ℓ 0ℓ
C[ F ]Alg = F-Algebras F[ F ]

open import Categories.Object.Initial --C[ F ]Alg

_Alghom[_,_] : {X Y : Set}(F : Container 0ℓ 0ℓ)(x : ⟦ F ⟧ X → X)(Y : ⟦ F ⟧ Y → Y) → Set
F Alghom[ x , y ] = C[ F ]Alg [ to-Algebra x , to-Algebra y ]


⦅_⦆ : {F : Container 0ℓ 0ℓ}{X : Set} → (⟦ F ⟧ X → X) → μ F → X
⦅ a ⦆ (in' (op , ar)) = a (op , ⦅ a ⦆ ∘ ar)

open F-Algebra-Morphism
open F-Algebra


valid-falghom : {F : Container 0ℓ 0ℓ}{X : Set}(a : ⟦ F ⟧ X → X) → F Alghom[ in' , a ]
valid-falghom {X} a = record { f = ⦅ a ⦆ ; commutes = refl }


isunique : {F : Container 0ℓ 0ℓ}{X : Set}{a : ⟦ F ⟧ X → X}(fhom : F Alghom[ in' , a ])(x : μ F) →
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


initial-in : {F : Container 0ℓ 0ℓ} → IsInitial C[ F ]Alg (to-Algebra in')
initial-in = record
             { ! = λ {A} → valid-falghom (A .α)
             ; !-unique = λ fhom {x} → isunique fhom x
             }

