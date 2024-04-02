open import funct.container
module church.proofs where
open import Relation.Binary.PropositionalEquality as Eq
open ≡-Reasoning
open import Function.Base using (id; _∘_)
open import init.initalg
open import init.initial
open import funct.flaws
open import funct.funext
open import church.defs

-- PAGE 51 - Proof 1
from-to-id : {F : Container} → fromCh ∘ toCh ≡ id
from-to-id {F} = funext (λ (x : μ F) → begin
    fromCh (toCh x)
  ≡⟨⟩ -- Definition of toCh
     fromCh (Ch (λ {X : Set} → λ (a : I⟦ F ⟧ X → X) → ⦅ a ⦆ x))
  ≡⟨⟩ -- Definition of fromCh
    (λ a → ⦅ a ⦆ x) in'
  ≡⟨⟩ -- function application
    ⦅ in' ⦆ x
  ≡⟨ reflection x ⟩
    x
  ∎)

-- PAGE 51 - Proof 2
postulate freetheorem-initial  : {F : Container}{B C : Set}{b : I⟦ F ⟧ B → B}{c : I⟦ F ⟧ C → C}
                                 (h : B → C) (g : {X : Set} → (I⟦ F ⟧ X → X) → X) →
                                 (h ∘ b ≡ (c ∘ (fmap h))) → h (g b) ≡ g c
fold-invariance : {F : Container}{Y : Set}(g : {X : Set} →
                  (I⟦ F ⟧ X → X) → X)(a : I⟦ F ⟧ Y → Y) →
                  ⦅ a ⦆ (g in') ≡ g a
fold-invariance g a = freetheorem-initial ⦅ a ⦆ g refl
to-from-id : {F : Container}{g : {X : Set} → (I⟦ F ⟧ X → X) → X} →
             toCh (fromCh (Ch g)) ≡ Ch g
to-from-id {F}{g} = begin
    toCh (fromCh (Ch g))
  ≡⟨⟩ -- definition of fromCh
    toCh (g in')
  ≡⟨⟩ -- definition of toCh
    Ch (λ { X : Set} → λ (a : I⟦ F ⟧ X → X) → ⦅ a ⦆ (g in'))
  ≡⟨ cong Ch (funexti (λ {Y : Set} → funext λ (a : I⟦ F ⟧ Y → Y) → fold-invariance g a)) ⟩
    Ch g
  ∎
to-from-id' : {F : Container} → toCh ∘ fromCh ≡ id
to-from-id' {F} = funext (λ where
                        (Ch g) → to-from-id {F}{g})

-- PAGE 51 - Proof 3
unCh : {F : Container}{X : Set}(b : I⟦ F ⟧ X → X)(c : Church F) → X
unCh b (Ch g) = g b
-- New function constitutes an implementation for the consumer function being replaced
cons-pres : {F : Container}{X : Set}(b : I⟦ F ⟧ X → X)(x : μ F) →
            (unCh b) (toCh x) ≡ ⦅ b ⦆ x
cons-pres b x = begin
    unCh b (toCh x)
  ≡⟨⟩ -- definition of toCh
    unCh b (Ch (λ a → ⦅ a ⦆ x))
  ≡⟨⟩ -- function application
    (λ a → ⦅ a ⦆ x) b
  ≡⟨⟩ -- function application
    ⦅ b ⦆ x
  ∎

-- PAGE 51 - Proof 4
-- New function constitutes an implementation for the producer function being replaced
prod-pres : {F : Container}{X : Set}(f : {Y : Set} → (I⟦ F ⟧ Y → Y) → X → Y)(s : X) →
            fromCh ((λ x → Ch (λ a → f a x)) s) ≡ f in' s
prod-pres {F}{X} f s = begin
    fromCh ((λ (x : X) → Ch (λ a → f a x)) s)
  ≡⟨⟩ -- function application
    fromCh (Ch (λ a → f a s))
  ≡⟨⟩ -- definition of fromCh
    (λ {Y : Set} (a : I⟦ F ⟧ Y → Y) → f a s) in'
  ≡⟨⟩ -- function application
    f in' s
  ∎

record nat {F G : Container}(f : {X : Set} → I⟦ F ⟧ X → I⟦ G ⟧ X): Set₁ where
  field
    coherence : {A B : Set}(h : A → B) → fmap {G} h ∘ f ≡ f ∘ fmap {F} h
open nat ⦃ ... ⦄
-- PAGE 51 - Proof 5
-- New function constitutes an implementation for the transformation function being replaced
chTrans : {F G : Container}(f : {X : Set} → I⟦ F ⟧ X → I⟦ G ⟧ X) → Church F → Church G
chTrans f (Ch g) = Ch (λ a → g (a ∘ f))
trans-pred : {F G : Container}( g : {X : Set} → (I⟦ F ⟧ X → X) → X ) → (f : {X : Set} → I⟦ F ⟧ X → I⟦ G ⟧ X) →
             fromCh (chTrans f (Ch g)) ≡ ⦅ in' ∘ f ⦆ (fromCh (Ch g))
trans-pred g f = begin
    fromCh (chTrans f (Ch g))
  ≡⟨⟩ -- Function application
    fromCh (Ch (λ a → g ( a ∘ f )))
  ≡⟨⟩ -- Definition of fromCh
    (λ a → g ( a ∘ f )) in'
  ≡⟨⟩ -- Function application
    g (in' ∘ f)
  ≡⟨ sym (fold-invariance g (in' ∘ f)) ⟩
    ⦅ in' ∘ f ⦆ (g in')
  ≡⟨⟩ -- Definition of fromCh
    ⦅ in' ∘ f ⦆ (fromCh (Ch g))
  ∎
