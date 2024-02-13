{-# OPTIONS --no-termination-check #-}
{-# OPTIONS --guardedness #-}
open import cat.container
module cat.terminal {F : Container } where
open import Function.Base using (id; _∘_)
open import Relation.Binary.PropositionalEquality as Eq
open ≡-Reasoning
open import cat.flaws
open import cat.funext
open import Function.Base



-- An initial algebra
record ν (F : Container) : Set where
  coinductive
  field
    out : ⟦ F ⟧ (ν F)
open ν
-- an anamorphism
【_】 : {X : Set} → (X → ⟦ F ⟧ X) → X → ν F
out (【 c 】 x) = fmap 【 c 】 (c x)
--⦅ a ⦆ (in' (op , ar)) = a (op , ⦅ a ⦆ ∘ ar)
--fmap : {X Y : Set} → (Y → X) → ⟦ F ⟧ Y → ⟦ F ⟧ X
--fmap ca (op , ar) = op , ca ∘ ar

universal-propₗ : {C : Set}(h : C → ν F)(c : C → ⟦ F ⟧ C) →
                 h ≡ 【 c 】 → out ∘ h ≡ fmap h ∘ c
universal-propₗ h c eq = begin
    out ∘ h
  ≡⟨ cong (_∘_ out) eq ⟩
    out ∘ 【 c 】
  ≡⟨⟩
    fmap 【 c 】 ∘ c
  ≡⟨ cong (_∘ c) (cong fmap (sym eq)) ⟩
    fmap h ∘ c
  ∎
--postulate universal-propᵣ : {C : Set}(h : C → ν F)(c : C → ⟦ F ⟧ C) → ((out ∘ h ≡ (fmap h) ∘ c) → (h ≡ 【 c 】))

comp-law : {C : Set}(c : C → ⟦ F ⟧ C) → out ∘ 【 c 】 ≡ (fmap 【 c 】) ∘ c
comp-law c = universal-propₗ 【 c 】 c refl

--{-# ETA ν #-} -- Seems to cause a hang (or major slowdown) in compilation
postulate νExt : {x y : ν F} → (out x ≡ out y) → x ≡ y
--νExt refl = refl

reflection-out : (x : ν F) → out (【 out 】 x) ≡ out x
reflection : (x : ν F) → 【 out 】 x ≡ x

reflection-out x = begin
    out (【 out 】 x)
  ≡⟨⟩ -- Am I sure that reflection and reflection-out don't just form trivial proof-loop?
    fmap 【 out 】 (out x)
  ≡⟨ cong (flip fmap (out x)) (funext reflection) ⟩
    fmap id (out x)
  ≡⟨ cong-app fmap-id (out x) ⟩
    out x
  ∎
reflection x = begin
     【 out 】 x
   ≡⟨ νExt (reflection-out x) ⟩
     x
   ∎

postulate fusion : {C D : Set}(h : C → D)(c : C → ⟦ F ⟧ C)(d : D → ⟦ F ⟧ D) →
                   (fmap h ∘ c ≡ d ∘ h) → 【 c 】 ≡ 【 d 】 ∘ h
