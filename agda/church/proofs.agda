{-# OPTIONS --type-in-type #-}
{-# OPTIONS --guardedness #-}
{-# OPTIONS --no-termination-check #-}
open import Effect.Functor
module church.proofs {F : Set → Set}⦃ _ : RawFunctor F ⦄ where
open RawFunctor ⦃ ... ⦄
open import Relation.Binary.PropositionalEquality as Eq
open ≡-Reasoning
open import Function.Base using (id; _∘_)
open import cat.funct
open import cat.free
open import cat.flaws
open import cat.funext
open import church.defs

-- PAGE 51 - Proof 1
reflection : (y : μ F) → ⦅ inj ⦆ y ≡ y
reflection (inj x) = begin
     ⦅ inj ⦆ (inj x)
   ≡⟨⟩
     inj (⦅ inj ⦆ <$> x)
   ≡⟨ cong inj (cong (_<$> x) (funext reflection)) ⟩
      inj (id <$> x)
   ≡⟨ cong inj (cong-app fmap-id x) ⟩
     (inj x)
   ∎
reflection-law : ⦅ inj ⦆ ≡ id
reflection-law = funext reflection

from-to-id : fromCh ∘ toCh ≡ id
from-to-id = funext (λ (x : μ F) → begin
    fromCh (toCh x)
  ≡⟨⟩ -- Definition of toCh
     fromCh (Ch (λ {X : Set} → λ (a : F X → X) → ⦅ a ⦆ x))
  ≡⟨⟩ -- Definition of fromCh
    (λ a → ⦅ a ⦆ x) inj
  ≡⟨⟩ -- function application
    ⦅ inj ⦆ x
  ≡⟨ reflection x ⟩
    x
  ≡⟨⟩
    id x
  ∎)


-- PAGE 51 - Proof 2
-- freetheorem g h = ? -- to be proved...

fold-invariance : {Y : Set}(g : {X : Set} → (F X → X) → X)(a : F Y → Y) →
                  ⦅ a ⦆ (g inj) ≡ g a
fold-invariance g a = freetheorem-initial ⦅ a ⦆ g refl

to-from-id : { g : {X : Set} → (F X → X) → X } → toCh (fromCh (Ch g)) ≡ Ch g
to-from-id {g} = begin
    toCh (fromCh (Ch g))
  ≡⟨⟩ -- definition of fromCh
    toCh (g inj)
  ≡⟨⟩ -- definition of toCh
    Ch (λ { X : Set} → λ (a : F X → X) → ⦅ a ⦆ (g inj))
  ≡⟨ cong Ch (funexti (λ Y → funext λ a → fold-invariance g a)) ⟩
    Ch g
  ∎




-- PAGE 51 - Proof 3
unCh : {X : Set} (b : F X → X) (c : Church F) → X
unCh b (Ch g) = g b
-- New function constitutes an implementation for the consumer function being replaced
cons-pres : { g : {X : Set} → (F X → X) → X } {X : Set}
            (b : F X → X) (x : μ F) → (unCh b) (toCh x) ≡ ⦅ b ⦆ x
cons-pres {g} b x = begin
    unCh b (toCh x)
  ≡⟨⟩ -- definition of toCh
    unCh b (Ch (λ a → ⦅ a ⦆ x))
  ≡⟨⟩ -- function application
    (λ a → ⦅ a ⦆ x) b
  ≡⟨⟩ -- function application
    ⦅ b ⦆ x
  ∎



-- PAGE 51 - Proof 4
-- New function constitutes an implementation for the produces function being replaced
prod-pres : (f : {Y : Set} → (F Y → Y) → μ F → Y)(s : μ F) →
            fromCh ((λ x → Ch (λ a → f a x)) s) ≡ f inj s
prod-pres f s = begin
    fromCh ((λ (x : μ F) → Ch (λ a → f a x)) s)
  ≡⟨⟩ -- function application
    fromCh (Ch (λ a → f a s))
  ≡⟨⟩ -- definition of fromCh
    (λ {Y : Set} (a : F Y → Y) → f a s) inj
  ≡⟨⟩ -- function application
    f inj s
  ∎



-- PAGE 51 - Proof 5
-- New function constitutes an implementation for the transformation function being replaced
chTrans : ∀ (f : {Y : Set} → Y → Y) → Church F → Church F
chTrans f (Ch g) = Ch (λ a → g (a ∘ f))
trans-pred : ( g : {X : Set} → (F X → X) → X ) → (f : {Y : Set} → Y → Y) →
             fromCh (chTrans f (Ch g)) ≡ ⦅ inj ∘ f ⦆ (fromCh (Ch g))
trans-pred g f = begin
    fromCh (chTrans f (Ch g))
  ≡⟨⟩ -- Function application
    fromCh (Ch (λ a → g ( a ∘ f )))
  ≡⟨⟩ -- Definition of fromCh
    (λ a → g ( a ∘ f )) inj
  ≡⟨⟩ -- Function application
    g (inj ∘ f)
  ≡⟨ sym (fold-invariance g (inj ∘ f)) ⟩
    ⦅ inj ∘ f ⦆ (g inj)
  ≡⟨⟩ -- Definition of fromCh
    ⦅ inj ∘ f ⦆ (fromCh (Ch g))
  ∎
