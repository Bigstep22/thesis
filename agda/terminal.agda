{-# OPTIONS --type-in-type #-}
{-# OPTIONS --no-positivity-check #-}
{-# OPTIONS --no-termination-check #-}
open import Effect.Functor
module terminal {F : Set → Set}⦃ _ : RawFunctor F ⦄ where
open import Function.Base using (id; _∘_)
open import Relation.Binary.Core
import Relation.Binary.PropositionalEquality as Eq
open Eq
open Eq.≡-Reasoning
open RawFunctor ⦃ ... ⦄
open import Data.Product

-- An initial algebra
data ν (F : Set → Set) : Set where
postulate out : ν F → F (ν F)

-- an anamorphism
⟦_⟧ : {X : Set} → (X → F X) → X → ν F
⟦_⟧ c = {!!}


data CoChurch (F : Set → Set) : Set₁ where
  CoCh : {X : Set} → (X → F X) → X → CoChurch F

toCoCh : ν F → CoChurch F
toCoCh x = CoCh out x
fromCoCh : CoChurch F → ν F
fromCoCh (CoCh h x) = ⟦ h ⟧ x
postulate funext  : {X : Set} {Y : X → Set} {f g : (x : X) → Y x} →
                    (∀ x → f x ≡ g x) → f ≡ g
postulate funexti : {X : Set} {Y : X → Set} {f g : {x : X} → Y x} →
                    (∀ Y → f {Y} ≡ g {Y} ) → (λ {x} → f {x}) ≡ g
-- See https://stackoverflow.com/a/56423455 as to why funexti(mplicit) is written this way, is this a weakness in the typechecker?


{-
-- PAGE 52 - Proof 1
postulate refl-helper : ∀ {x : F (μ F)} → (⦅ inj ⦆ <$> x) ≡ x
-- refl-helper = {!!} -- Good luck...
-}
postulate reflection : (x : ν F) → ⟦ out ⟧ x ≡ x
{-reflection (inj x) = begin
     ⦅ inj ⦆  (inj x)
   ≡⟨⟩
     inj (⦅ inj ⦆ <$> x)
   ≡⟨ cong inj refl-helper ⟩
     (inj x)
   ∎
reflection-law : ⦅ inj ⦆ ≡ id
reflection-law = funext reflection
--fold-refl {x} = cong-app fold-refl-axiom x
-}

from-to-id : fromCoCh ∘ toCoCh ≡ id
from-to-id = funext {ν F} (λ (x : ν F) → begin
    fromCoCh (toCoCh x)
  ≡⟨⟩ -- Definition of toCh
     fromCoCh (CoCh out x)
  ≡⟨⟩ -- Definition of fromCh
    ⟦ out ⟧ x
  ≡⟨ reflection x ⟩
    x
  ≡⟨⟩
    id x
  ∎)


-- PAGE 52 - Proof 2
postulate CoChEncode : {X : Set} → {c : X → F X} → (CoCh c) ≡ (CoCh out ∘ ⟦ c ⟧)

to-from-id : {X : Set} ( c : (X → F X) ) (x : X) → toCoCh (fromCoCh (CoCh c x)) ≡ CoCh c x
to-from-id c x = begin
    toCoCh (fromCoCh (CoCh c x))
  ≡⟨⟩ -- definition of fromCh
    toCoCh (⟦ c ⟧ x)
  ≡⟨⟩ -- definition of toCh
    CoCh out (⟦ c ⟧ x)
  ≡⟨⟩ -- composition
    (CoCh out ∘ ⟦ c ⟧) x
  ≡⟨ cong-app (sym CoChEncode) x ⟩ -- Paper makes some more assumptions I have yet to find
    CoCh c x
  ∎



-- PAGE 52 - Proof 3
{-
unCh : {X : Set} (b : F X → X) (c : Church F) → X
unCh b (Ch g) = g b
-}
-- New function constitutes an implementation for the produces function being replaced
prod-pres : {X : Set} (c : X → F X) (x : X) →
            fromCoCh ((λ s → CoCh c s) x) ≡ ⟦ c ⟧ x
prod-pres c x = begin
    fromCoCh ((λ s → CoCh c s) x)
  ≡⟨⟩ -- function application
    fromCoCh (CoCh c x)
  ≡⟨⟩ -- definition of toCh
    ⟦ c ⟧ x
  ∎



-- PAGE 52 - Proof 4
-- New function constitutes an implementation for the produces function being replaced
unCoCh : (f : {Y : Set} → (Y → F Y) → Y → ν F) (c : CoChurch F) → ν F
unCoCh f (CoCh c s) = f c s
cons-pres : {X : Set} → (f : {Y : Set} → (Y → F Y) → Y → ν F) → (x : ν F) →
            unCoCh f (toCoCh x) ≡ f out x
cons-pres f x = begin
    unCoCh f (toCoCh x)
  ≡⟨⟩ -- definition of toCoCh
    unCoCh f (CoCh out x)
  ≡⟨⟩ -- function application
    f out x
  ∎



-- PAGE 52 - Proof 5
-- New function constitutes an implementation for the transformation function being replaced

postulate unfold-fusion : {C D : Set} (h : C → D) (c : C → F C) (d : D → F D) →
                          (_<$>_ h ∘ c ≡ d ∘ h) →  ⟦ c ⟧ ≡ ⟦ d ⟧ ∘ h
postulate valid-hom : ∀ {X : Set} (h : X → F X) (f : {Y : Set} → Y → Y) → (_<$>_ ⟦ h ⟧) ∘ f ∘ h ≡ f ∘ out ∘ ⟦ h ⟧

chTrans : ∀ (f : {Y : Set} → Y → Y) → CoChurch F → CoChurch F
chTrans f (CoCh c s) = CoCh (f ∘ c) s
trans-pred :  {X : Set} (h : X → F X) (f : {Y : Set} → Y → Y)  (x : X) →
             fromCoCh (chTrans f (CoCh h x)) ≡ (⟦ f ∘ out ⟧ ∘ ⟦ h ⟧) x
trans-pred h f x = begin
    fromCoCh (chTrans f (CoCh h x))
  ≡⟨⟩ -- Function application
    fromCoCh (CoCh (f ∘ h) x)
  ≡⟨⟩ -- Definition of fromCh
    ⟦ f ∘ h ⟧ x
  ≡⟨  cong-app (unfold-fusion ⟦ h ⟧ (f ∘ h) (f ∘ out) (valid-hom h f)) x ⟩
    (⟦ f ∘ out ⟧ ∘ ⟦ h ⟧) x
  ∎


--open import Data.Sum
-- x : A ⊎ B
-- x = inj₁ a
--data List a : Set where
