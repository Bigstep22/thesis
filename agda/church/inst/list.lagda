\paragraph{Example: List fusion}
In order to clearly see how the Church encodings allows functions to fuse, a datatype was selected such
the abstracted function, which have so far been used to prove the needed properties, can be instantiated
to demonstrate how the fusion works for functions across a cocrete datatype.
\begin{code}[hide]
open import Data.Product using (_×_)
open import Data.Nat.Base
open import Agda.Builtin.Nat
open import Data.Fin using (Fin; zero)
open import Data.Bool
open import agda.church.defs renaming (cons to consu)
open import agda.church.proofs
open import agda.funct.funext
open import agda.init.initial
\end{code}
In this module is defined: the container, whose interpretation represents the base functor for lists,
some convenience functions to make type annotations more readable, a producer function \tt{between},
a transformation function \tt{map}, a consumer function \tt{sum}, and a proof that non-church and church-encoded
implementations are equal.
\begin{code}
module agda.church.inst.list where
\end{code}
\subparagraph{Datatypes}
The index set for the container, as well as the container whose interpretation represents the base funtor for list.
Note how ListOp is isomorphis to the datatype \tt{1 + A}, I use ListOp instead to make the code more readable:
\begin{code}
data ListOp (A : Set) : Set where
  nil : ListOp A
  cons : A → ListOp A
F : (A : Set) → Container _ _
F A = ListOp A ▷ λ { nil → Fin 0 ; (cons n) → Fin 1 }
\end{code}
Functions representing the run-of-the-mill list datatype and the base functor for list:
\begin{code}
List : (A : Set) → Set
List A = μ (F A)
List' : (A B : Set) → Set
List' A B = ⟦ F A ⟧ B
\end{code}
Helper functions to assist in cleanly writing out instances of lists:
\begin{code}
[] : {A : Set} → μ (F A)
[] = in' (nil , λ())
_::_ : {A : Set} → A → List A → List A
_::_ x xs = in' (cons x , const xs)
infixr 20 _::_
\end{code}
The fold funtion as it would normally be encountered for lists, defined in terms of $\catam{\_}$:
\begin{code}
fold' : {A X : Set}(n : X)(c : A → X → X) → List A → X
fold' {A}{X} n c = ⦅ (λ{(nil , _) → n; (cons n , g) → c n (g zero)}) ⦆
\end{code}
\subparagraph{between}
The recursion principle \tt{b}, which when used, represents the between function.
It uses \tt{b'} to assist termination checking:
\begin{code}
b' : {B : Set} → (a : List' ℕ B → B) → ℕ → ℕ → B
b' a x zero = a (nil , λ())
b' a x (suc n) = a (cons x , const (b' a (suc x)  n))
b : {B : Set} → (a : List' ℕ B → B) → ℕ × ℕ → B
b a (x , y) = b' a x (suc (y - x))
\end{code}
The functions \tt{between1} and \tt{between2}.
The former is defined without a church-encoding, the latter with.
A reflexive proof and sanity check is included to show equality:
\begin{code}
between1 : ℕ × ℕ → List ℕ
between1 xy = b in' xy
between2 : ℕ × ℕ → List ℕ
between2 = prod b
eqbetween : between1 ≡ between2
eqbetween = refl
checkbetween : 2 :: 3 :: 4 :: 5 :: 6 :: [] ≡ between2 (2 , 6)
checkbetween = refl
\end{code}
\subparagraph{map}
The algebra \tt{m}, which when used in an algebra, represents the map function:
\begin{code}
m : {A B C : Set}(f : A → B) → List' A C → List' B C
m f (nil , _) = (nil , λ())
m f (cons n , l) = (cons (f n) , l)
\end{code}
The functions \tt{map1} and \tt{map2}.
The former is defined without a church-encoding, the latter with.
A reflexive proof and sanity check is included to show equality:
\begin{code}
map1 : {A B : Set}(f : A → B) → List A → List B
map1 f = ⦅ in' ∘ m f ⦆
map2 : {A B : Set}(f : A → B) → List A → List B
map2 f = natTrans (m f)
eqmap : {f : ℕ → ℕ} → map1 f ≡ map2 f
eqmap = refl
checkmap : (map1 (_+_ 2) (3 :: 6 :: [])) ≡ 5 :: 8 :: []
checkmap = refl
\end{code}
\subparagraph{sum}
The algebra \tt{s}, which when used in an algebra, represents the sum function:
\begin{code}
s : List' ℕ ℕ → ℕ
s (nil , _) = 0
s (cons n , f) = n + f zero
\end{code}
The functions \tt{sum1} and \tt{sum2}.
The former is defined without a church-encoding, the latter with.
A reflexive proof and sanity check is included to show equality:
\begin{code}
sum1 : List ℕ → ℕ
sum1 = ⦅ s ⦆
sum2 : List ℕ → ℕ
sum2 = consu s
eqsum : sum1 ≡ sum2
eqsum = refl
checksum : sum1 (5 :: 6 :: 7 :: []) ≡ 18
checksum = refl
\end{code}
\subparagraph{equality}
The below proof shows the equality between the non-church-endcoded pipeline and
the church-encoded pipeline:
\begin{code}
eq : {f : ℕ → ℕ} → sum1 ∘ map1 f ∘ between1 ≡ sum2 ∘ map2 f ∘ between2
eq {f} = begin
    ⦅ s ⦆ ∘ ⦅ in' ∘ m f ⦆ ∘ b in'
  ≡⟨ cong (λ g → ⦅ s ⦆ ∘ ⦅ in' ∘ m f ⦆ ∘ g) (prod-pres b) ⟩ -- reflexive
    ⦅ s ⦆ ∘ ⦅ in' ∘ m f ⦆ ∘ fromCh ∘ prodCh b
  ≡⟨ cong (λ f → ⦅ s ⦆ ∘ f ∘ prodCh b) (sym $ trans-pres (m f)) ⟩
    ⦅ s ⦆ ∘ fromCh ∘ natTransCh (m f) ∘ prodCh b
  ≡⟨ cong (λ g → g ∘ fromCh ∘ natTransCh (m f) ∘ prodCh b) (cons-pres s) ⟩ -- reflexive
    consCh s ∘ toCh ∘ fromCh ∘ natTransCh (m f) ∘ prodCh b
  ≡⟨ cong (λ g → consCh s ∘ toCh ∘ fromCh ∘ natTransCh (m f) ∘ g ∘ prodCh b) (sym to-from-id) ⟩
    consCh s ∘ toCh ∘ fromCh ∘ natTransCh (m f) ∘ toCh ∘ fromCh ∘ prodCh b
  ≡⟨⟩
    consu s ∘ natTrans (m f) ∘ prod b
  ∎



-- Bonus functions
count : (ℕ → Bool) → μ (F ℕ) → ℕ
count p = ⦅ (λ where
               (nil , _) → 0
               (cons true , f) → 1 + f zero
               (cons false , f) → f zero) ⦆ ∘ map1 p

even : ℕ → Bool
even 0 = true
even (suc n) = not (even n)
odd : ℕ → Bool
odd = not ∘ even

countworks : count even (5 :: 6 :: 7 :: 8 :: []) ≡ 2
countworks = refl

-- Investigation related to filter, the following lines are tangentially related to list
build : {F : Container _ _}{X : Set} → ({Y : Set} → (⟦ F ⟧ Y → Y) → X → Y) → (x : X) → μ F
build g = fromCh ∘ prodCh g
foldr' : {F : Container _ _}{X : Set} → (⟦ F ⟧ X → X) → μ F → X
foldr' c = consCh c ∘ toCh
filter : {A : Set} → (A → Bool) → List A → List A
filter p = fromCh ∘ prodCh (λ f → consCh (λ where
   (nil , l) → f (nil , l)
   (cons a , l) → if (p a) then f (cons a , l) else l zero)) ∘ toCh
\end{code}
