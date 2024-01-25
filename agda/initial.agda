{-# OPTIONS --type-in-type #-}
{-# OPTIONS --no-positivity-check #-}
{-# OPTIONS --no-termination-check #-}
open import Effect.Functor
module initial {F : Set → Set}⦃ _ : RawFunctor F ⦄ where
open import Function.Base using (id; _∘_)
open import Axiom.Extensionality.Propositional using (Extensionality)
open import Agda.Primitive
open import Relation.Binary.Core
import Relation.Binary.PropositionalEquality as Eq
import Agda.Builtin.Equality
open Eq
open Eq.≡-Reasoning
open RawFunctor ⦃ ... ⦄

data μ (F : Set → Set) : Set where
  inj : F (μ F) → μ F

cata : {X : Set} → (F X → X) → μ F → X
cata alg (inj x) = alg ((cata alg) <$> x)

data Church (F : Set → Set) : Set₁ where
  Ch : ({X : Set} → (F X → X) → X) → Church F

toCh : μ F → Church F
toCh x = Ch (λ {X : Set} → λ (a : F X → X) → cata a x)
fromCh : Church F → μ F
fromCh (Ch g) = g inj

unimp : {X : Set} → {Y : X → Set} → (f : {x : X} → Y x) → (x : X) → Y x
unimp f x = f {x}

postulate funext : {X : Set} {Y : X → Set} {f g : (x : X) → Y x} → (∀ x → f x ≡ g x) → f ≡ g
postulate funexti : {X : Set} {Y : X → Set} {f g : {x : X} → Y x} →
                        (∀ Y → f {Y} ≡ g {Y} ) → (λ {x} → f {x}) ≡ g
-- See https://stackoverflow.com/a/56423455 as to why funexti(mplicit) is written this way, is this a weakness in the typechecker?
-- impl-funext {_} {_} {f} {g} k = funext {!!}

postulate freetheorem : { X Y : Set } → { b : F X → X } → { c : F Y → Y } →
                        ( g : { X : Set } → (F X → X) → X ) → ( h : X → Y ) →
                        (h ∘ b ≡ (c ∘ (_<$>_ h))) → h (g b) ≡ g c

fold-invariance : { g : {X : Set} → (F X → X) → X } → ∀ {Y : Set} (a : F Y → Y) → cata a (g inj) ≡ g a
fold-invariance {g} a = freetheorem g (cata a) refl

to-from-id : { g : {X : Set} → (F X → X) → X } → toCh (fromCh (Ch g)) ≡ Ch g
to-from-id {g} = begin
    toCh (fromCh (Ch g))
  ≡⟨⟩ -- definition of fromCh
    toCh (g inj)
  ≡⟨⟩ -- definition of toCh
    Ch (λ { X : Set} → λ (a : F X → X) → cata a (g inj))
  ≡⟨ cong Ch (funexti (λ Y → funext λ a → fold-invariance {g} a)) ⟩
    Ch g
  ∎

postulate fold-refl-axiom : cata inj ≡ id
--fold-refl-axiom = {!!} -- to be proved...
fold-refl : {x : μ F} → cata inj x ≡ x
fold-refl {x} = cong-app fold-refl-axiom x





from-to-id : fromCh ∘ toCh ≡ id
from-to-id = funext {μ F} (λ (x : μ F) → begin
    fromCh (toCh x)
  ≡⟨⟩ -- Definition of toCh
     fromCh (Ch (λ {X : Set} → λ (a : F X → X) → cata a x))
  ≡⟨⟩ -- Definition of fromCh
    (λ a → cata a x) inj
  ≡⟨⟩ -- function application
    cata inj x
  ≡⟨ fold-refl ⟩
    x
  ≡⟨⟩
    id x
  ∎)






--open import Data.Sum
-- x : A ⊎ B
-- x = inj₁ a
--data List a : Set where
--  Cons : a → (List a) → List a
--  Nil : List a
--data ListF a b : Set where
--  ConsF : a → b → ListF a b
--  NilF : ListF a b
--inj' : ListF A (List A) → List A
--inj' NilF = Nil
--inj' (ConsF x xs) = Cons x xs
--fold : (ListF A B → B) → List A → B
--fold a Nil = a NilF
--fold a (Cons x xs) = a (ConsF x (fold a xs))
