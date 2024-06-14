\paragraph{Example: List fusion}
In order to clearly see how the Cochurch encodings allows functions to fuse, a datatype was selected such
the abstracted function, which have so far been used to prove the needed properties, can be instantiated
to demonstrate how the fusion works for functions across a cocrete datatype.
\begin{code}[hide]
{-# OPTIONS --guardedness #-}
module agda.cochurch.inst.list where
open import agda.cochurch.defs renaming (cons to consu)
open import agda.cochurch.proofs
open import Data.Fin using (Fin; zero)
open import Data.Unit
open import agda.cochurch.terminal
open import Data.Product using (_×_)
open import Data.Sum hiding (map)
open import Data.Nat
open import Agda.Builtin.Nat
\end{code}
In this section is defined: the container, whose interpretation represents the base functor for lists,
some convenience functions to make type annotations more readable, a producer function \tt{between},
a transformation function \tt{map}, a consumer function \tt{sum}, and a proof that non-cochurch and cochurch-encoded
implementations are equal.
\subparagraph{Datatypes}
The index set for the container, as well as the container whose interpretation represents the base funtor for list.
Note how ListOp is isomorphic to the datatype \tt{$\top$ + const A}, I use ListOp instead to make the code more readable:
\begin{code}
data ListOp (A : Set) : Set where
  nil : ListOp A
  cons : A → ListOp A
F : (A : Set) → Container 0ℓ 0ℓ
F A = ListOp A ▷ λ { nil → Fin 0 ; (cons n) → Fin 1 }
\end{code}
Functions representing the run-of-the-mill (potentially infinite) list datatype and the base functor for list:
\begin{code}
List : (A : Set) → Set
List A = ν (F A)
List' : (A B : Set) → Set
List' A B = ⟦ F A ⟧ B
\end{code}
Helper functions to assist in cleanly writing out instances of lists:
\begin{code}
[] : {A : Set} → List A
head [] = nil
tail [] = λ()
_::_ : {A : Set} → A → List A → List A
head (x :: xs) = cons x
tail (x :: xs) = const xs
infixr 20 _::_
\end{code}
The unfold funtion as it would normally be encountered for lists, defined in terms of $\anam{\_}$:
\begin{code}
mapping : {A X : Set} → (f : X → ⊤ ⊎ (A × X)) → (X → List' A X)
mapping f x with f x
mapping f x | (inj₁ tt) = (nil , λ())
mapping f x | (inj₂ (a , x')) = (cons a , const x')
unfold' : {F : Container 0ℓ 0ℓ}{A X : Set}(f : X → ⊤ ⊎ (A × X)) → X → List A
unfold' {A}{X} f = A⟦ mapping f ⟧
\end{code}
\subparagraph{Between}
The corecursion principle \tt{b}, which when used, represents the between function.
It uses \tt{b'} to assist in termination checking:
\begin{code}
b' : ℕ × ℕ → List' ℕ (ℕ × ℕ)
b' (x , zero)  = (nil , λ())
b' (x , suc n)  = (cons x , const (suc x , n))
b : ℕ × ℕ → List' ℕ (ℕ × ℕ)
b (x , y) = b' (x , (suc (y - x)))
\end{code}
The functions \tt{between1} and \tt{between2}.
The former is defined without a cochurch-encoding, the latter with.
A reflexive proof is included to show equality:
\begin{code}
between1 : ℕ × ℕ → List ℕ
between1 = A⟦ b ⟧
between2 : ℕ × ℕ → List ℕ
between2 = prod b
eqbetween : between1 ≡ between2
eqbetween = refl
\end{code}
\subparagraph{Map}
The natural transformation \tt{m}, which when used in a natrual transformation function, represents the map function:
\begin{code}
m : {A B C : Set}(f : A → B) → List' A C → List' B C
m f (nil , l) = (nil , l)
m f (cons n , l) = (cons (f n) , l)
\end{code}
The functions \tt{map1} and \tt{map2}.
The former is defined without a cochurch-encoding, the latter with.
A reflexive proof is included to show equality:
\begin{code}
map1 : {A B : Set}(f : A → B) → List A → List B
map1 f = A⟦ m f ∘ out ⟧
map2 : {A B : Set}(f : A → B) → List A → List B
map2 f = natTrans (m f)
eqmap : {f : ℕ → ℕ} → map1 f ≡ map2 f
eqmap = refl
\end{code}
\subparagraph{Sum}
The coalgebra \tt{s}, which when used in a consumer function, represents the sum function.
Note that it is currently set to be non-terminating.
\begin{code}
{-# NON_TERMINATING #-}
s : {S : Set} → (S → List' ℕ S) → S → ℕ
s h s' with h s'
s h s' | (nil , f) = 0
s h s' | (cons x , f) = x + s h (f zero)
\end{code}
The functions \tt{sum1} and \tt{sum2}.
The former is defined without a cochurch-encoding, the latter with.
A reflexive proof is included to show equality:
\begin{code}
sum1 : List ℕ → ℕ
sum1 = s out
sum2 : List ℕ → ℕ
sum2 = consu s
eqsum : sum1 ≡ sum2
eqsum = refl
\end{code}
\subparagraph{Equality}
The below proof shows the equality between the non-cochurch-endcoded pipeline and the cochurch-encoded pipeline:
\begin{code}
eq : {f : ℕ → ℕ}(x : ℕ × ℕ) → (sum1 ∘ map1 f ∘ between1) x ≡ (sum2 ∘ map2 f ∘ between2) x
eq {f} x = begin
    (s out ∘ A⟦ m f ∘ out ⟧ ∘ A⟦ b ⟧) x
  ≡⟨ cong (s out ∘ A⟦ m f ∘ out ⟧) (prod-pres b x) ⟩ -- refl
    (s out ∘ A⟦ m f ∘ out ⟧ ∘ fromCoCh ∘ prodCoCh b) x
  ≡⟨ cong (s out) (sym $ trans-pres (m f)
      (λ _ → (λ { (nil , l) → refl ; (cons n , l) → refl })) (prodCoCh b x)) ⟩
    (s out ∘ fromCoCh ∘ natTransCoCh (m f) ∘ prodCoCh b) x
  ≡⟨ (cons-pres s ((fromCoCh ∘ natTransCoCh (m f) ∘ prodCoCh b) x)) ⟩ -- refl
    (consCoCh s ∘ toCoCh ∘ fromCoCh ∘ natTransCoCh (m f) ∘ prodCoCh b) x
  ≡⟨ cong (consCoCh s ∘ toCoCh ∘ fromCoCh ∘ natTransCoCh (m f))
          (sym $ to-from-id (prodCoCh b x)) ⟩
  (consCoCh s ∘ toCoCh ∘ fromCoCh ∘ natTransCoCh (m f) ∘ toCoCh ∘ fromCoCh ∘ prodCoCh b) x
  ≡⟨⟩
    (consu s ∘ natTrans (m f) ∘ prod b) x
  ∎
\end{code}
