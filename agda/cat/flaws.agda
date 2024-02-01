open import Effect.Functor
module cat.flaws {F : Set → Set }⦃ _ : RawFunctor F ⦄ where
open RawFunctor ⦃ ... ⦄
open import Function.Base using (id; _∘_)
open import Relation.Binary.PropositionalEquality as Eq
open ≡-Reasoning

postulate fmap-id : {X : Set} → (_<$>_ (id {_} {X})) ≡ id {_} {F X}
postulate fmap-comp : {X Y Z : Set}{x : F X}{f : Y → Z}{g : X → Y} →
                      (_<$>_ (f ∘ g)) ≡ (_<$>_ f) ∘ (_<$>_ g)
