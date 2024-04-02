open import funct.container
module church.inst.list where
open import Data.Product hiding (map)
open import Data.Nat
open import Data.Fin hiding (_+_; _>_; _-_)
open import Data.Empty
open import Data.Unit
open import Function.Base
open import Data.Bool
open import Agda.Builtin.Nat
open import church.defs
open import church.proofs

open import funct.funext
open import init.initalg

open import Relation.Binary.PropositionalEquality as Eq
open ≡-Reasoning

data ListOp (A : Set) : Set where
  nil : ListOp A
  cons : A → ListOp A

--open import funct.flaws {ℕ ▹ Fin}
F : (A : Set) → Container
F A = ListOp A ▹ λ where
                 nil → ⊥
                 (cons n) → ⊤

List : (A : Set) → Set
List A = μ (F A)
List' : (A B : Set) → Set
List' A B = I⟦ F A ⟧ B

[] : {A : Set} → μ (F A)
[] = in' (nil , λ())


_::_ : {A : Set} → A → List A → List A
_::_ x xs = in' (cons x , λ tt → xs)
infixr 20 _::_


fold' : {A X : Set}(n : X)(c : A → X → X) → List A → X
fold' {A}{X} n c = ⦅ (λ where
                        (nil , _) → n
                        (cons n , g) → c n (g tt) ) ⦆

m : {A B C : Set}(f : A → B) → List' A C → List' B C
m f (nil , _) = (nil , λ())
m f (cons n , l) = (cons (f n) , l)
map1 : {A B : Set}(f : A → B) → List A → List B
map1 f = ⦅ in' ∘ m f ⦆ --fold' [] (λ x xs → (f x) :: xs)
mapCh : {A B : Set}(f : A → B) → Church (F A) → Church (F B)
mapCh f (Ch g) = Ch (λ a → g (a ∘ m f))
map2 : {A B : Set}(f : A → B) → List A → List B
map2 f = fromCh ∘ mapCh f ∘ toCh
--                                This last bit doesn't quite fit, new base functor needed?
--                                It should be a nonrecursive implementation....

--map : {A B : Set} (f : A → B) → μ (F A) → μ (F B)
--map f = ⦅ m f ⦆
l1 : μ (F ℕ)
l1 = 5 :: 8 :: []
l2 : μ (F ℕ)
l2 = 3 :: 6 :: []
proof : (map1 (_+_ 2) l2) ≡ l1
proof = refl


su : List' ℕ ℕ → ℕ
su (nil , _) = 0
su (cons n , f) = n + f tt

sum1 : μ (F ℕ) → ℕ
sum1 = ⦅ su ⦆
sumCh : Church (F ℕ) → ℕ
sumCh (Ch g) = g su
sum2 = sumCh ∘ toCh

sumworks : sum1 (5 :: 6 :: 7 :: []) ≡ 18
sumworks = refl


applyUpTo : {A : Set} → (ℕ → A) → ℕ → μ (F A)
applyUpTo f zero    = []
applyUpTo f (suc n) = f zero :: applyUpTo (f ∘ suc) n

upTo : ℕ → μ (F ℕ)
upTo = applyUpTo id

b' : {B : Set} → (a : List' ℕ B → B) → ℕ → ℕ → B
b' a x zero = a (nil , λ())
b' a x (suc n) = a (cons x , λ tt → (b' a (suc x)  n))

b : {B : Set} → (a : List' ℕ B → B) → ℕ × ℕ → B
b a (x , y) = b' a x (suc (y - x))

between1 : ℕ × ℕ → List ℕ
between1 xy = b in' xy
betweenCh : ℕ × ℕ → Church (F ℕ)
betweenCh xy = Ch (λ a → b a xy)
between2 : ℕ × ℕ → List ℕ
between2 xy = fromCh (betweenCh xy)


check : 2 :: 3 :: 4 :: 5 :: 6 :: [] ≡ between1 (2 , 6)
check = refl

eq1 : {xy : ℕ × ℕ}{f : ℕ → ℕ} → (sum2 ∘ map2 f) (between2 xy) ≡ (sumCh ∘ mapCh f) (betweenCh xy)
eq1 {xy}{f} = begin
    (sum2 ∘ map2 f) (between2 xy)
  ≡⟨⟩ -- dfn of all of the functions
    (sumCh ∘ toCh ∘ fromCh ∘ mapCh f ∘ toCh ∘ fromCh) (betweenCh xy)
  ≡⟨ cong sumCh (cong-app to-from-id' ((mapCh f ∘ toCh ∘ fromCh) (betweenCh xy))) ⟩
    (sumCh ∘ mapCh f ∘ toCh ∘ fromCh) (betweenCh xy)
  ≡⟨ cong (sumCh ∘ mapCh f) (cong-app to-from-id' (betweenCh xy)) ⟩
    (sumCh ∘ mapCh f) (betweenCh xy)
  ∎

eq2 : {xy : ℕ × ℕ}{f : ℕ → ℕ} → (sumCh ∘ mapCh f) (betweenCh xy) ≡ (sum1 ∘ map1 f) (between1 xy)
eq2 {xy}{f} = begin
    (sumCh ∘ mapCh f) (betweenCh xy)
  ≡⟨⟩
    (sumCh (Ch (λ a → b (a ∘ m f) xy)))
  ≡⟨⟩
    b (su ∘ m f) xy
  ≡⟨⟩
    unCh su (Ch (λ a → b (a ∘ m f) xy))
  ≡⟨ cong (unCh su) (sym $ cong-app to-from-id' (Ch (λ a → b (a ∘ m f) xy))) ⟩
    unCh su (toCh (fromCh (Ch (λ a → b (a ∘ m f) xy))))
  ≡⟨ cons-pres su (fromCh (Ch (λ a → b (a ∘ m f) xy))) ⟩
    ⦅ su ⦆ (fromCh (Ch (λ a → b (a ∘ m f) xy)))
  ≡⟨ cong ⦅ su ⦆ (trans-pred (flip b xy) (m f)) ⟩
    ⦅ su ⦆ (⦅ in' ∘ m f ⦆ (fromCh (Ch (λ a → b a xy))))
  ≡⟨ cong (⦅ su ⦆ ∘ ⦅ in' ∘ m f ⦆) (prod-pres b xy) ⟩
    (⦅ su ⦆ ∘ ⦅ in' ∘ m f ⦆) (b in' xy)
  ≡⟨⟩
    (sum1 ∘ map1 f) (between1 xy)
  ∎

-- Proofs for each of the above functions
eqsum : sum1 ≡ sum2
eqsum = refl
eqmap : {f : ℕ → ℕ} → map1 f ≡ map2 f
eqmap = refl
eqbetween : between1 ≡ between2
eqbetween = refl


-- Generalization of the above proofs for any container
transCh : {F G : Container}(nat : {X : Set} → I⟦ F ⟧ X → I⟦ G ⟧ X) → Church F → Church G
transCh n (Ch g) = Ch (λ a → g (a ∘ n))
eqtrans : {F G : Container}{nat : {X : Set} → I⟦ F ⟧ X → I⟦ G ⟧ X} → fromCh ∘ transCh nat ∘ toCh ≡ ⦅ in' ∘ nat ⦆
eqtrans = refl
eqprod : {F : Container}{X : Set}{g : {Y : Set} → (I⟦ F ⟧ Y → Y) → X → Y} → fromCh ∘ (λ x → Ch (λ a → g a x)) ≡ g in'
eqprod = refl
consCh : {F : Container}{Y : Set} → (c : (I⟦ F ⟧ Y → Y)) → Church F → Y
consCh c (Ch g) = g c
eqcons : {F : Container}{X : Set}{c : (I⟦ F ⟧ X → X)} → consCh c ∘ toCh ≡ ⦅ c ⦆
eqcons = refl


count : (ℕ → Bool) → μ (F ℕ) → ℕ
count p = ⦅ (λ where
               (nil , _) → 0
               (cons true , f) → 1 + f tt
               (cons false , f) → f tt) ⦆ ∘ map1 p



even : ℕ → Bool
even 0 = true
even (suc n) = not (even n)
odd : ℕ → Bool
odd = not ∘ even

countworks : count even (5 :: 6 :: 7 :: 8 :: []) ≡ 2
countworks = refl
