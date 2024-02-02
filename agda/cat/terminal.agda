{-# OPTIONS --no-termination-check #-}
{-# OPTIONS --no-positivity-check #-}
{-# OPTIONS --guardedness #-}
open import Effect.Functor
module cat.terminal {F : Set → Set }⦃ _ : RawFunctor F ⦄ where
open RawFunctor ⦃ ... ⦄
open import Function.Base using (id; _∘_)
open import Relation.Binary.PropositionalEquality as Eq
open ≡-Reasoning
open import cat.flaws
open import cat.funext



-- An initial algebra
record ν (F : Set → Set) : Set where
  coinductive
  field
    out : F (ν F)
open ν
-- an anamorphism
⟦_⟧ : {X : Set} → (X → F X) → X → ν F
out (⟦ c ⟧ x) = ⟦ c ⟧ <$> (c x)

postulate universal-propₗ : {C : Set}(h : C → ν F)(c : C → F C) → ((h ≡ ⟦ c ⟧) → (out ∘ h ≡ (_<$>_ h) ∘ c))
postulate universal-propᵣ : {C : Set}(h : C → ν F)(c : C → F C) → ((out ∘ h ≡ (_<$>_ h) ∘ c) → (h ≡ ⟦ c ⟧))

comp-law : {C : Set}(c : C → F C) → out ∘ ⟦ c ⟧ ≡ (_<$>_ ⟦ c ⟧) ∘ c
comp-law c = universal-propₗ ⟦ c ⟧ c refl

postulate νExt : {x y : ν F} → (out x ≡ out y) → x ≡ y
-- TODO: Is the above postulate valid? Something something, terminal therefore uniqueness?

reflection-out : (x : ν F) → out (⟦ out ⟧ x) ≡ out x
reflection : (x : ν F) → ⟦ out ⟧ x ≡ x

reflection-out x = begin
    out (⟦ out ⟧ x)
  ≡⟨⟩ -- Am I sure that reflection and reflection-out don't just form trivial proof-loop?
    ⟦ out ⟧ <$> (out x)
  ≡⟨ cong (_<$> (out x)) (funext reflection) ⟩
    id <$> (out x)
  ≡⟨ cong-app fmap-id (out x) ⟩
    out x
  ∎
  {-
  ≡⟨ cong out  (νreflection  x)  ⟩
    out x
  ∎-}
reflection x = begin
     ⟦ out ⟧ x
   ≡⟨ νExt (reflection-out x) ⟩
     x
   ∎

postulate fusion : {C D : Set}(h : C → D)(c : C → F C)(d : D → F D) →
                   (_<$>_ h ∘ c ≡ d ∘ h) →  ⟦ c ⟧ ≡ ⟦ d ⟧ ∘ h
