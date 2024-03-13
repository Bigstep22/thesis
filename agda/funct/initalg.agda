open import funct.container
open import Data.Product
open import Level
module funct.initalg (F : Container {0ℓ}) where
open import Categories.Category hiding (_[_,_]) renaming (Category to Cat)
open import Categories.Category.Instance.Sets
open import Categories.Functor
open import Categories.Functor.Algebra
open import Relation.Binary.PropositionalEquality as Eq
open ≡-Reasoning
open import funct.flaws
open import funct.funext
open import Function
open import Categories.Category.Construction.F-Algebras
open import funct.endo F


--falg : Cat (suc 0ℓ) 0ℓ 0ℓ
--falg = F-Algebras contEndo
open import Categories.Object.Initial (F-Algebras contEndo)


data μ (F : Container) : Set where
  in' : I⟦ F ⟧ (μ F) → μ F
⦅_⦆ : {X : Set} → (I⟦ F ⟧ X → X) → μ F → X
⦅ a ⦆ (in' (op , ar)) = a (op , ⦅ a ⦆ ∘ ar)

valid-falghom : {X : Cat.Obj (Sets 0ℓ)} → (a : I⟦ F ⟧ X → X) →
                F-Algebra-Morphism {_}{_}{_}{_}{contEndo} (to-Algebra in') (to-Algebra a)
valid-falghom {X} a = record
         { f = ⦅ a ⦆
         ; commutes = refl
         }


isequiv : (A : F-Algebra contEndo) → (f : F-Algebra-Morphism (to-Algebra in') A) (x : μ F) →
          ⦅ F-Algebra.α A ⦆ x ≡ F-Algebra-Morphism.f f x
isequiv A f (in' (op , ar)) = begin
                   ⦅ F-Algebra.α A ⦆ (in' (op , ar))
                     ≡⟨ refl ⟩ -- Dfn of ⦅_⦆
                   F-Algebra.α A (op , ⦅ F-Algebra.α A ⦆ ∘ ar)
                     ≡⟨ cong (λ h → F-Algebra.α A (op , h)) (funext (λ x → isequiv A f (ar x))) ⟩
                   F-Algebra.α A (op , (F-Algebra-Morphism.f f) ∘ ar)
                     ≡⟨⟩ -- Dfn of composition
                   (F-Algebra.α A ∘ fmap (F-Algebra-Morphism.f f)) (op , ar)
                     ≡⟨ flip cong-app (op , ar) (sym (funext (λ x → F-Algebra-Morphism.commutes f {x}))) ⟩
                   ((F-Algebra-Morphism.f f) ∘ in') (op , ar)
                 ∎

initial-in : IsInitial (to-Algebra in')
initial-in = record
             { ! = λ {A} → record
                 { f = ⦅ F-Algebra.α A ⦆
                 ; commutes = refl
                 }
             ; !-unique = λ {A} f {x} → isequiv A f x
             }

-- IsInitial.! (Initial.⊥-is-initial r) {X} (Initial.⊥ r)




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
