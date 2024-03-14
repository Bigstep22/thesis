open import funct.container
open import Data.Product
open import Level
module funct.initalg {F : Container {0ℓ}} where
open import Categories.Category renaming (Category to Cat)
open import Categories.Category.Instance.Sets
open import Categories.Functor
open import Categories.Functor.Algebra
open import Relation.Binary.PropositionalEquality as Eq hiding ([_])
open ≡-Reasoning
open import funct.flaws
open import funct.funext
open import Function
open import funct.endo
open import Categories.Object.Initial C⟦ F ⟧



data μ (F : Container) : Set where
  in' : I⟦ F ⟧ (μ F) → μ F
⦅_⦆ : {X : Set} → (I⟦ F ⟧ X → X) → μ F → X
⦅ a ⦆ (in' (op , ar)) = a (op , ⦅ a ⦆ ∘ ar)

_Alg⟦_,_⟧ : {X Y : Set}(F : Container)(x : I⟦ F ⟧ X → X)(Y : I⟦ F ⟧ Y → Y) → Set
F Alg⟦ x , y ⟧ = C⟦ F ⟧ [ to-Algebra x , to-Algebra y ]


valid-falghom : {X : Set}(a : I⟦ F ⟧ X → X) → F Alg⟦ in' , a ⟧
valid-falghom {X} a = record { f = ⦅ a ⦆ ; commutes = refl }


isunique : {X : Set}{a : I⟦ F ⟧ X → X}(fhom : F Alg⟦ in' , a ⟧){x : μ F} →
           ⦅ a ⦆ x ≡ F-Algebra-Morphism.f fhom x
isunique {X}{a} fhom {(in' (op , ar))} = begin
                   ⦅ a ⦆ (in' (op , ar))
                     ≡⟨⟩ -- Dfn of ⦅_⦆
                   a (op , ⦅ a ⦆ ∘ ar)
                     ≡⟨ cong (λ h → a (op , h)) (funext (λ x → isunique fhom {(ar x)})) ⟩ -- induction
                   a (op , f ∘ ar)
                     ≡⟨⟩ -- Dfn of composition
                   (a ∘ fmap f) (op , ar)
                     ≡⟨ flip cong-app (op , ar) (sym (funext commutes)) ⟩
                   (f ∘ in') (op , ar)
                 ∎
                 where f = F-Algebra-Morphism.f fhom
                       commutes = λ x → F-Algebra-Morphism.commutes fhom {x}

initial-in : IsInitial (to-Algebra in')
initial-in = record
             { ! = λ {A} → valid-falghom (F-Algebra.α A)
             ; !-unique = isunique
             }





--           in
--  F (μꟳ)  ---->  μꟳ
--     |           |
--     | F ⦅ a ⦆    | ⦅ a ⦆
--     |           |
--    F X   ---->  X
--            a
-- We know, for a given initial (F, in), and any other (F, a), that there exists
-- a unique morphism ⦅ a ⦆ : μꟳ → X and F ⦅ a ⦆ : F (μꟳ) → F X, such that,
-- the above diagram commutes
