{-# OPTIONS --type-in-type #-}

module initial {A B : Set}{F : Set → Set} where
open import Function.Base using (id; _∘_)
import Relation.Binary.PropositionalEquality as Eq
import Agda.Builtin.Equality
open Eq
open Eq.≡-Reasoning

data μ (F : Set → Set) : Set₁ where
postulate inj : F (μ F) → μ F
postulate cata : {A : Set} → (F A → A) → μ F → A

data Church ( F : Set → Set ) : Set₁ where
  Ch : ({A : Set} → (F A → A) → A) → Church F

toCh : {A : Set} → μ F → Church F
toCh x = Ch (λ {A} → λ (a : F A → A) → cata a x)
fromCh : Church F → μ F
fromCh (Ch g) = g inj

postulate fold-refl-axiom : cata inj ≡ id
postulate fold-refl : {x : μ F} → cata inj x ≡ x

fusion-law : {A : Set} → {x : μ F} → (fromCh (toCh {A} x)) ≡ x
fusion-law {A} {x} =
  begin
    fromCh (toCh {A} x)
  ≡⟨ refl ⟩
    fromCh (Ch (λ a → cata a x))
  ≡⟨ refl ⟩
    (λ a → cata a x) inj
  ≡⟨ refl ⟩
    cata inj x
  ≡⟨ fold-refl ⟩
    x
  ∎









con : Set → Set
con t = t

abs : Set → Set
abs t = t









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
